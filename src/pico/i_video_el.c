

#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <doom/r_data.h>
#include "doom/f_wipe.h"
#include "pico.h"

#include "config.h"
#include "d_loop.h"
#include "deh_str.h"
#include "doomtype.h"
#include "i_input.h"
#include "i_joystick.h"
#include "i_system.h"
#include "i_timer.h"
#include "i_video.h"
#include "m_argv.h"
#include "m_config.h"
#include "m_misc.h"
#include "tables.h"
#include "v_diskicon.h"
#include "v_video.h"
#include "w_wad.h"
#include "z_zone.h"

#include "pico/multicore.h"
#include "pico/sync.h"
#include "pico/time.h"
#include "hardware/gpio.h"
#include "picodoom.h"
#include "image_decoder.h"
#include "hardware/dma.h"
#include "hardware/irq.h"
#include "hardware/structs/xip_ctrl.h"
#include "dither_maps.h"

#define EL_VS_PIN    16
#define EL_HS_PIN    17
#define EL_VCLK_PIN  18
#define EL_VID_PIN   19

#define EL_DISP_WIDTH   320
#define EL_DISP_HEIGHT  (256 + 1)
#define EL_DISP_STRIDE  (EL_DISP_WIDTH / 8)
#define EL_DISP_WH_HDR  (((EL_DISP_HEIGHT - 1) << 16) | (EL_DISP_WIDTH - 1))


#include "el.pio.h"

#define LOW_PRIO_IRQ 31

volatile uint32_t sw_number = 94;

static int32_t dma_chan = -1; 

static const patch_t *stbar;
volatile uint8_t interp_in_use;
static boolean initialized = false;

semaphore_t render_frame_ready;
semaphore_t display_frame_freed;
semaphore_t core1_launch;

boolean screensaver_mode = false;
boolean screenvisible = true;
isb_int8_t usegamma = 0;
pixel_t *I_VideoBuffer;
uint8_t *text_screen_data;
uint8_t next_video_type;
uint8_t next_frame_index;
uint8_t next_overlay_index;
volatile uint8_t wipe_min;

uint8_t *wipe_yoffsets;
int16_t *wipe_yoffsets_raw;
uint32_t *wipe_linelookup;

uint8_t *next_video_scroll;
uint8_t *video_scroll;

uint8_t __aligned(4) frame_buffer[2][SCREENWIDTH * MAIN_VIEWHEIGHT];

static uint8_t __aligned(4) frame_buffer_1b[EL_DISP_STRIDE * EL_DISP_HEIGHT] = {0};

static uint8_t palette[256];
static uint8_t shared_pal[NUM_SHARED_PALETTES][16];
static int8_t next_pal=-1;

uint8_t display_frame_index;
uint8_t display_overlay_index;
uint8_t display_video_type;

typedef void (*scanline_func)(uint32_t *dest, int scanline);

static void scanline_func_none(uint32_t *dest, int scanline);
static void scanline_func_double(uint32_t *dest, int scanline);
static void scanline_func_single(uint32_t *dest, int scanline);
static void scanline_func_wipe(uint32_t *dest, int scanline);

scanline_func scanline_funcs[] = {
        scanline_func_none,     // VIDEO_TYPE_NONE
        NULL,                   // VIDEO_TYPE_TEXT
        scanline_func_single,   // VIDEO_TYPE_SAVING
        scanline_func_single,   // VIDEO_TYPE_DOUBLE
        scanline_func_single,   // VIDEO_TYPE_SINGLE
        scanline_func_wipe,     // VIDEO_TYPE_WIPE
};


CU_REGISTER_DEBUG_PINS(dbg1, dbg2);
CU_SELECT_DEBUG_PINS(dbg1);
// CU_SELECT_DEBUG_PINS(dbg2)

#define DM_X(px, dm_id) ((px) & (dither_maps[dm_id].size - 1))
#define DM_Y(py, dm_id) ((py) & (dither_maps[dm_id].size - 1))
#define DM_VAL(px, py, dm_id) (dither_maps[dm_id].map[(dither_maps[dm_id].size * DM_Y((py), dm_id) + DM_X((px), dm_id))])

#define BUF1B_BYTE_ID(x, y) (((y) * EL_DISP_STRIDE) + ((x) >> 3))

#define SET_1B_PIXEL(x, y) (frame_buffer_1b[BUF1B_BYTE_ID(x, y)] |= 1 << (x & 7))
#define UNSET_1B_PIXEL(x, y) (frame_buffer_1b[BUF1B_BYTE_ID(x, y)] &= ~(1 << (x & 7)))
#define PUT_1B_PIXEL(x, y, src_val, dm_id) (src_val >= DM_VAL((x), (y), dm_id) ? (SET_1B_PIXEL((x), (y))) : (UNSET_1B_PIXEL((x), (y))))

#define PUT_1B_PIXEL_ST(x, y, src_val, dm_id) (((src_val >= 80 ? MIN(255, (int16_t)src_val + 32) : MAX(0, (int16_t)src_val - 32)) >= DM_VAL((x), (y), dm_id)) ? (SET_1B_PIXEL((x), (y))) : (UNSET_1B_PIXEL((x), (y))))

static void scanline_func_none(uint32_t *dest, int scanline)
{
    // memset(dest, 0, SCREENWIDTH * 2);
}


static void scanline_func_single(uint32_t *dest, int scanline)
{
    uint8_t *src;

    static const uint8_t *dmap = dither_maps[8].map;
    static const uint8_t dsize = dither_maps[8].size;

    if (scanline < MAIN_VIEWHEIGHT)
    {
        src = frame_buffer[display_frame_index] + scanline * SCREENWIDTH;
    }
    else
    {
        src = frame_buffer[display_frame_index^1] + (scanline - 32) * SCREENWIDTH;
    }
#if !DEMO1_ONLY
    if (video_scroll)
    {
        for(int i = SCREENWIDTH - 1; i > 0; i--)
        {
            src[i] = src[i-1];
        }
        src[0] = video_scroll[scanline];
    }
#endif
    uint8_t *dst = &frame_buffer_1b[(scanline + 28) * EL_DISP_STRIDE];

    for (int pid = 0; pid < SCREENWIDTH; pid += 8)
    {
        uint8_t bt = 0;

        for (int i = 0; i < 8; i++)
        {
            uint8_t sp = *(src + pid + i);
            sp = palette[sp];
            // bt |= (sp >= dmap[(scanline & (dsize - 1)) * dsize + ((pid + i) & (dsize - 1))] ? 1 : 0) << i;
            
            PUT_1B_PIXEL(pid + i, scanline + 28, sp, display_frame_index ? 4 : 8);
        }

        // *(dst + (pid >> 3)) = bt;
    }
}


static inline void palette_convert_scanline(uint32_t *dest, const uint8_t *src)
{
    // for (int i = 0; i < SCREENWIDTH; i += 2)
    // {
    //     uint32_t val = palette[*src++];
    //     val |= (palette[*src++]) << 16;
    //     *dest++ = val;
    // }
}


static void scanline_func_double(uint32_t *dest, int scanline)
{
    if (scanline < MAIN_VIEWHEIGHT)
    {
        const uint8_t *src = frame_buffer[display_frame_index] + scanline * SCREENWIDTH;
        palette_convert_scanline(dest, src);
    }
}


static void scanline_func_wipe(uint32_t *dest, int scanline)
{
    static const uint8_t *dmap = dither_maps[8].map;
    static const uint8_t dsize = dither_maps[8].size;

    const uint8_t *src;
    
    if (scanline < MAIN_VIEWHEIGHT)
    {
        src = frame_buffer[display_frame_index];
    }
    else
    {
        src = frame_buffer[display_frame_index ^ 1] - 32 * SCREENWIDTH;
    }

    assert(wipe_yoffsets && wipe_linelookup);
    uint8_t *dst = &frame_buffer_1b[(scanline + 28) * EL_DISP_STRIDE];

    src += scanline * SCREENWIDTH;
    
    for (int i = 0; i < SCREENWIDTH; i++)
    {
        int rel = scanline - wipe_yoffsets[i];
        uint8_t sp;
   
        if (rel < 0)
        {
            sp = palette[src[i]];
            dst[i >> 3] |= (sp >= dmap[(scanline & (dsize - 1)) * dsize + (i & (dsize - 1))] ? 1 : 0) << (i & 7);
        }
        else
        {
            const uint8_t *flip;
            flip = (const uint8_t*)wipe_linelookup[rel];

            // todo better protection here
            if (flip >= &frame_buffer[0][0] && flip < &frame_buffer[0][0] + 2 * SCREENWIDTH * MAIN_VIEWHEIGHT)
            {
                sp = palette[flip[i]];
                dst[i >> 3] |= (sp >= dmap[(scanline & (dsize - 1)) * dsize + (i & (dsize - 1))] ? 1 : 0) << (i & 7);
            }
        }
    }


    // const uint8_t *src;

    // src = frame_buffer[0];

    // src += scanline * SCREENWIDTH;

    // for (int x = 0; x < SCREENWIDTH; x++)
    // {
    //     // uint8_t sp = palette[src[x]];
    //     uint8_t sp = x % 255;
    //     PUT_1B_PIXEL(x, scanline + 28, sp, 8);
    // }

}


static inline uint draw_vpatch(uint16_t *dest, patch_t *patch, vpatchlist_t *vp, uint off, int scanline)
{
    int repeat = vp->entry.repeat;
    dest += vp->entry.x;
    int w = vpatch_width(patch);
    const uint8_t *data0 = vpatch_data(patch);
    const uint8_t *data = data0 + off;

    int dmi = display_frame_index ? 3 : 8;

    if (!vpatch_has_shared_palette(patch))
    {
        const uint8_t *pal = vpatch_palette(patch);
    
        switch (vpatch_type(patch))
        {
        
        case vp4_runs:
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;

            uint16_t pend = px + w;
            uint8_t gap;
            while (0xff != (gap = *data++))
            {
                px += gap;
                int len = *data++;
                for (int i = 1; i < len; i += 2)
                {
                    uint v = *data++;

                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0xf]], dmi);
                    px++;
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v >> 4]], dmi);
                    px++;
                    // *p++ = palette[pal[v & 0xf]];
                    // *p++ = palette[pal[v >> 4]];
                }
                if (len & 1)
                {
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[(*data++) & 0xf]], dmi);
                    px++;
                    // *p++ = palette[pal[(*data++) & 0xf]];
                }
                assert(px <= pend);
                if (px == pend)
                {
                    break;
                }
            }
            break;
        }
        case vp4_alpha: 
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;

            for (int i = 0; i < w / 2; i++)
            {
                uint v = *data++;
                if (v & 0xf)
                {
                    // p[0] = palette[pal[v & 0xf]];
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0xf]], dmi);
                }
                if (v >> 4)
                {
                    // p[1] = palette[pal[v >> 4]];
                    PUT_1B_PIXEL_ST(px + 1, py + 28, palette[pal[v >> 4]], dmi);
                } 
                px += 2;
            }
            if (w & 1)
            {
                uint v = *data++;
                if (v & 0xf)
                {
                    // p[0] = palette[pal[v & 0xf]];
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0xf]], dmi);
                }
            }
            break;
        }
        case vp4_solid:
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;

            for (int i = 0; i < w / 2; i++)
            {
                uint v = *data++;
                // p[0] = palette[pal[v & 0xf]];
                // p[1] = palette[pal[v >> 4]];
                PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0xf]], dmi);
                PUT_1B_PIXEL_ST(px + 1, py + 28, palette[pal[v >> 4]], dmi);
                px += 2;
            }
            if (w & 1)
            {
                uint v = *data++;
                // p[0] = palette[pal[v & 0xf]];
                PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0xf]], dmi);
            }
            break;
        }
        case vp6_runs:
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;
            uint16_t pend = px + w;
            uint8_t gap;
            
            while (0xff != (gap = *data++))
            {
                px += gap;
                int len = *data++;
                for (int i = 3; i < len; i += 4)
                {
                    uint v = *data++;
                    v |= (*data++) << 8;
                    v |= (*data++) << 16;

                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0x3f]], dmi);
                    px++;                    
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[(v >> 6) & 0x3f]], dmi);
                    px++;
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[(v >> 12) & 0x3f]], dmi);
                    px++;
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[(v >> 18) & 0x3f]], dmi);
                    px++;
                    // *p++ = palette[pal[v & 0x3f]];
                    // *p++ = palette[pal[(v >> 6) & 0x3f]];
                    // *p++ = palette[pal[(v >> 12) & 0x3f]];
                    // *p++ = palette[pal[(v >> 18) & 0x3f]];
                }
                len &= 3;
                if (len--)
                {
                    uint v = *data++;
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0x3f]], dmi);
                    px++;
                    // *p++ = palette[pal[v & 0x3f]];
                    if (len--)
                    {
                        v >>= 6;
                        v |= (*data++) << 2;
                        PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0x3f]], dmi);
                        px++;
                        // *p++ = palette[pal[v & 0x3f]];
                        if (len--)
                        {
                            v >>= 6;
                            v |= (*data++) << 4;
                            // *p++ = palette[pal[v & 0x3f]];
                            PUT_1B_PIXEL_ST(px, py + 28, palette[pal[v & 0x3f]], dmi);
                            px++;
                            assert(!len);
                        }
                    }
                }
                assert(px <= pend);
                if (px == pend)
                {
                    break;
                }
            }
            break;
        }
        case vp8_runs:
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;
            uint16_t pend = px + w;
            uint8_t gap;
        
            while (0xff != (gap = *data++))
            {
                px += gap;
                int len = *data++;
                for (int i = 0; i < len; i++)
                {
                    PUT_1B_PIXEL_ST(px, py + 28, palette[pal[*data++]], dmi);
                    px++;
                    // *p++ = palette[pal[*data++]];
                }
                assert(px <= pend);
                
                if (px == pend)
                {
                    break;
                }
            }
            break;
        }
        case vp_border:
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;
            // dest[0] = palette[*data++];
            PUT_1B_PIXEL_ST(px, py + 28, palette[*data++], dmi);
            uint16_t col = palette[*data++];
            for (int i = 1; i < w - 1; i++)
            {
                PUT_1B_PIXEL_ST(px + i, py + 28, col, dmi);
                // dest[i] = col;
            }
            PUT_1B_PIXEL_ST(px + w - 1, py + 28, col, dmi);

            // dest[w-1] = palette[*data++];
            break;
        }
        default:
            assert(false);
            break;
        }
    }
    else
    {
        uint sp = vpatch_shared_palette(patch);
        uint8_t *pal16 = shared_pal[sp];
        assert(sp < NUM_SHARED_PALETTES);
        switch (vpatch_type(patch))
        {
        case vp4_solid: 
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;

            // if (((uintptr_t)dest) & 3)
            // if (px & 3)
            // {
            for (int i = 0; i < w / 2; i++)
            {
                uint v = *data++;
                PUT_1B_PIXEL_ST(px, py + 28, pal16[v & 0xf], dmi);
                PUT_1B_PIXEL_ST(px + 1, py + 28, pal16[v >> 4], dmi);
                // p[0] = pal16[v & 0xf];
                // p[1] = pal16[v >> 4];
                px += 2;
            }
            // }
            // else
            // {
            //     uint32_t *wide = (uint32_t *) dest;
            //     for (int i = 0; i < w / 2; i++)
            //     {
            //         uint v = *data++;
            //         wide[i] = pal16[v & 0xf] | (pal16[v >> 4] << 16);
            //     }
            // }
            if (w & 1)
            {
                uint v = *data++;
                // dest[w-1] = pal16[v & 0xf];
                PUT_1B_PIXEL_ST(px + w - 1, py + 28, pal16[v & 0xf], dmi);
            }
            break;
        }
        case vp4_alpha:
        {
            uint16_t px = vp->entry.x;
            uint16_t py = scanline;

            for (int i = 0; i < w / 2; i++)
            {
                uint v = *data++;
                if (v & 0xf)
                {
                    // p[0] = pal16[v & 0xf];
                    PUT_1B_PIXEL_ST(px, py + 28, pal16[v & 0xf], dmi);
                }

                if (v >> 4)
                {
                    // p[1] = pal16[v >> 4];
                    PUT_1B_PIXEL_ST(px + 1, py + 28, pal16[v >> 4], dmi);
                }
                px += 2;
            }

            if (w & 1)
            {
                uint v = *data++;
                if (v & 0xf)
                {
                    // p[0] = pal16[v & 0xf];
                    PUT_1B_PIXEL_ST(px, py + 28, pal16[v & 0xf], dmi);
                }
            }
            break;
        }

        default:
            assert(false);
        }
    }
    if (repeat)
    {
        uint16_t px = vp->entry.x;
        uint16_t py = scanline;
        // we need them to be solid... which they are, but if not you'll just get some visual funk
        //assert(vpatch_type(patch) == vp4_solid);
        if (vp->entry.patch_handle == VPATCH_M_THERMM)
        {
            w--; // hackity hack
        }
        
        for(int i=0;i<repeat*w;i++)
        {
            // dest[w+i] = dest[i];

            // PUT_1B_PIXEL(px, py + 28, pal16[v & 0xf], 1);
        }
    }

    return data - data0;
}


void new_frame_init_overlays_palette_and_wipe(void)
{
    // re-initialize our overlay drawing
    if (display_video_type >= FIRST_VIDEO_TYPE_WITH_OVERLAYS)
    {
        memset(vpatchlists->vpatch_next, 0, sizeof(vpatchlists->vpatch_next));
        memset(vpatchlists->vpatch_starters, 0, sizeof(vpatchlists->vpatch_starters));
        memset(vpatchlists->vpatch_doff, 0, sizeof(vpatchlists->vpatch_doff));
        vpatchlist_t *overlays = vpatchlists->overlays[display_overlay_index];
        // do it in reverse so our linked lists are in ascending order
        for (int i = overlays->header.size - 1; i > 0; i--)
        {
            assert(overlays[i].entry.y < count_of(vpatchlists->vpatch_starters));
            vpatchlists->vpatch_next[i] = vpatchlists->vpatch_starters[overlays[i].entry.y];
            vpatchlists->vpatch_starters[overlays[i].entry.y] = i;
        }
        if (next_pal != -1)
        {
            static const uint8_t *playpal;
            static bool calculate_palettes;
            if (!playpal)
            {
                lumpindex_t l = W_GetNumForName("PLAYPAL");
                playpal = W_CacheLumpNum(l, PU_STATIC);
                calculate_palettes = W_LumpLength(l) == 768;
            }
            if (!calculate_palettes || !next_pal)
            {
                const uint8_t *doompalette = playpal + next_pal * 768;

                for (int i = 0; i < 256; i++)
                {
                    int r = *doompalette++;
                    int g = *doompalette++;
                    int b = *doompalette++;
                    if (usegamma) {
                        r = gammatable[usegamma-1][r];
                        g = gammatable[usegamma-1][g];
                        b = gammatable[usegamma-1][b];
                    }
                    // palette[i] = (MAX(MAX(r, g), b) + MIN(MIN(r, g), b)) >> 1;
                    int16_t pp = (r + g + b) * 341 >> 10;
                    if (pp >= 80)
                    {
                        pp = MIN(pp + 8, 255);
                    }
                    else
                    {
                        pp = MAX(pp - 8, 0);
                    }

                    // palette[i] = (r + g + b) * 341 >> 10;
                    palette[i] = (uint8_t)pp;

                    if ((r >= 100) && ((g + b) <= 40))
                    {
                        palette[i] = 255;
                    }

                }
            }
            else
            {
                int mul, r0, g0, b0;
                
                if (next_pal < 9)
                {
                    mul = next_pal * 65536 / 9;
                    r0 = 255; g0 = b0 = 0;
                }
                else if (next_pal < 13)
                {
                    mul = (next_pal - 8) * 65536 / 8;
                    r0 = 215; g0 = 186; b0 = 69;
                }
                else
                {
                    mul = 65536 / 8;
                    r0 = b0 = 0; g0 = 256;
                }
                
                const uint8_t *doompalette = playpal;
                
                for (int i = 0; i < 256; i++)
                {
                    int r = *doompalette++;
                    int g = *doompalette++;
                    int b = *doompalette++;
                    r += ((r0 - r) * mul) >> 16;
                    g += ((g0 - g) * mul) >> 16;
                    b += ((b0 - b) * mul) >> 16;
                    // palette[i] = (MAX(MAX(r, g), b) + MIN(MIN(r, g), b)) >> 1;
                    int16_t pp = (r + g + b) * 341 >> 10;
                    if (pp >= 64)
                    {
                        pp = MIN(pp + 32, 255);
                    }
                    else
                    {
                        pp = MAX(pp - 32, 0);
                    }

                    // palette[i] = (r + g + b) * 341 >> 10;
                    palette[i] = (uint8_t)pp;

                    if ((r >= 100) && ((g + b) <= 40))
                    {
                        palette[i] = 255;
                    }
                }
            }

            next_pal = -1;
            assert(vpatch_type(stbar) == vp4_solid); // no transparent, no runs, 4 bpp
            
            for (int i = 0; i < NUM_SHARED_PALETTES; i++)
            {
                patch_t *patch = resolve_vpatch_handle(vpatch_for_shared_palette[i]);
                assert(vpatch_colorcount(patch) <= 16);
                assert(vpatch_has_shared_palette(patch));
                for (int j = 0; j < 16; j++)
                {
                    shared_pal[i][j] = palette[vpatch_palette(patch)[j]];
                }
            }
        }

        if (display_video_type == VIDEO_TYPE_WIPE)
        {
//            printf("WIPEMIN %d\n", wipe_min);
            if (wipe_min <= 200)
            {
                bool regular = display_overlay_index; // just happens to toggle every frame
                int new_wipe_min = 200;
                for (int i = 0; i < SCREENWIDTH; i++)
                {
                    int v;
                    if (wipe_yoffsets_raw[i] < 0)
                    {
                        if (regular)
                        {
                            wipe_yoffsets_raw[i]++;
                        }
                        v = 0;
                    }
                    else
                    {
                        int dy = (wipe_yoffsets_raw[i] < 16) ? (1 + wipe_yoffsets_raw[i] + regular) / 2 : 4;
                        if (wipe_yoffsets_raw[i] + dy > 200)
                        {
                            v = 200;
                        }
                        else
                        {
                            wipe_yoffsets_raw[i] += dy;
                            v = wipe_yoffsets_raw[i];
                        }
                    }
                    wipe_yoffsets[i] = v;
                    if (v < new_wipe_min)
                    {
                        new_wipe_min = v;
                    }
                }

                assert(new_wipe_min >= wipe_min);
                wipe_min = new_wipe_min;
            }
        }
    }
}



void new_frame_stuff(void)
{
    static bool first_frame = true;

    if (sem_available(&render_frame_ready)) {
        sem_acquire_blocking(&render_frame_ready);
        display_video_type = next_video_type;
        display_frame_index = next_frame_index;
        display_overlay_index = next_overlay_index;

        // if (first_frame)
        // {
        //     first_frame = false;
        //     display_frame_index = 0;
        // }

#if !DEMO1_ONLY
        video_scroll = next_video_scroll; // todo does this waste too much space
#endif
        sem_release(&display_frame_freed);
    
    } 
    else
    {
#if !DEMO1_ONLY
        video_scroll = NULL;
#endif
    }
    
    if (display_video_type != VIDEO_TYPE_SAVING)
    {
        // this stuff is large (so in flash) and not needed in save move
        new_frame_init_overlays_palette_and_wipe();
    }
}


void draw_1b_buffer(void)
{
    // struct scanvideo_scanline_buffer *buffer = scanvideo_begin_scanline_generation_linked(display_video_type == VIDEO_TYPE_TEXT ? 2 : 1, false);

    static uint32_t buffer[SCREENWIDTH * 4];
    // static int frame = 0;

    gpio_xor_mask(1 << 14);

    // if (frame == 0)
    // {
    //     next_frame_index ^= 1;
    //     new_frame_stuff();
    //     frame = 1;
    // }

    new_frame_stuff();

    for (int scanline = 0; scanline < SCREENHEIGHT; scanline++)
    {
        // static int8_t last_frame_number = -1;

        // if ((int8_t)frame != last_frame_number)
        // {
        //     last_frame_number = frame;
        //     new_frame_stuff();
        // }

        if (display_video_type != VIDEO_TYPE_TEXT)
        {
            // we don't have text mode -> normal transition yet, but we may for network game, so leaving this here - we would need to put the buffer pointers back
            // assert (buffer->data < text_scanline_buffer_start || buffer->data >= text_scanline_buffer_start + TEXT_SCANLINE_BUFFER_TOTAL_WORDS);
            
            scanline_funcs[display_video_type](buffer, scanline);
            
            if (display_video_type >= FIRST_VIDEO_TYPE_WITH_OVERLAYS)
            {
                assert(scanline < count_of(vpatchlists->vpatch_starters));
                int prev = 0;
                
                for (int vp = vpatchlists->vpatch_starters[scanline]; vp;)
                {
                    int next = vpatchlists->vpatch_next[vp];

                    while (vpatchlists->vpatch_next[prev] && vpatchlists->vpatch_next[prev] < vp)
                    {
                        prev = vpatchlists->vpatch_next[prev];
                    }

                    assert(prev != vp);
                    assert(vpatchlists->vpatch_next[prev] != vp);
                    vpatchlists->vpatch_next[vp] = vpatchlists->vpatch_next[prev];
                    vpatchlists->vpatch_next[prev] = vp;
                    prev = vp;
                    vp = next;
                }

                vpatchlist_t *overlays = vpatchlists->overlays[display_overlay_index];
                prev = 0;
                
                for (int vp = vpatchlists->vpatch_next[prev]; vp; vp = vpatchlists->vpatch_next[prev])
                {
                    patch_t *patch = resolve_vpatch_handle(overlays[vp].entry.patch_handle);
                    int yoff = scanline - overlays[vp].entry.y;
                    
                    if (yoff < vpatch_height(patch))
                    {
                        vpatchlists->vpatch_doff[vp] = draw_vpatch((uint16_t*)(buffer), patch, &overlays[vp],
                                                                   vpatchlists->vpatch_doff[vp], scanline);
                        prev = vp;
                    }
                    else
                    {
                        vpatchlists->vpatch_next[prev] = vpatchlists->vpatch_next[vp];
                    }
                }
            }

            // uint16_t *p = (uint16_t *)buffer->data;
            // p[0] = video_doom_offset_raw_run;
            // p[1] = p[2];
            // p[2] = SCREENWIDTH - 3;
            // buffer->data[SCREENWIDTH / 2 + 1] = video_doom_offset_raw_1p;
            // buffer->data[SCREENWIDTH / 2 + 2] = video_doom_offset_end_of_scanline_skip_ALIGN;
            // buffer->data_used = SCREENWIDTH / 2 + 3;

        }
        else
        {
            // render_text_mode_scanline(buffer, scanline);
        }

        // scanvideo_end_scanline_generation(buffer);

        // buffer = scanvideo_begin_scanline_generation_linked(display_video_type == VIDEO_TYPE_TEXT ? 2 : 1, false);
    }


    pio_sm_put_blocking(pio0, EL_PIO_SM, EL_DISP_WH_HDR);

    // for (size_t j = 0; j < sizeof(frame_buffer_1b) / sizeof(uint32_t); j++)
    // {
    //     uint32_t data = *(((uint32_t*)&frame_buffer_1b) + j);
    //     pio_sm_put_blocking(pio0, EL_PIO_SM, data);
        
    //     while (!pio_sm_is_tx_fifo_empty(pio0, EL_PIO_SM))
    //     {
    //         asm("nop;");
    //     }
    // }


    dma_channel_set_read_addr(dma_chan, frame_buffer_1b, true);

    // sleep_ms(20ul);

    // irq_set_pending(LOW_PRIO_IRQ);
    // sem_release(&display_frame_freed);
    // DEBUG_PINS_XOR(dbg1, 1);
}


static void el_disp_dma_handler(void)
{

    gpio_xor_mask(1 << 15);

    /* Clear the interrupt request. */
    dma_hw->ints1 = 1u << dma_chan;

    irq_set_pending(LOW_PRIO_IRQ);
}


static void el_disp_init(void)
{
    gpio_init(EL_VS_PIN);
    gpio_init(EL_HS_PIN);
    gpio_init(EL_VCLK_PIN);
    gpio_init(EL_VID_PIN);

    el_program_init(pio0);

    dma_chan = dma_claim_unused_channel(true);
    dma_channel_config cfg = dma_channel_get_default_config(dma_chan);
    
    channel_config_set_transfer_data_size(&cfg, DMA_SIZE_32);
    channel_config_set_read_increment(&cfg, true);
    channel_config_set_dreq(&cfg, DREQ_PIO0_TX0);

    dma_channel_configure(
        dma_chan,
        &cfg,
        &pio0_hw->txf[EL_PIO_SM],                   /* Write address */
        NULL,                                       /* Read address */
        EL_DISP_HEIGHT * EL_DISP_STRIDE / sizeof(uint32_t), /* Number of transfers */
        false                                       /* Don't start yet */
    );

    dma_channel_set_irq0_enabled(dma_chan, true);
    irq_set_exclusive_handler(DMA_IRQ_0, el_disp_dma_handler);
    irq_set_enabled(DMA_IRQ_0, true);
}   



static void core1()
{
    el_disp_init();

    irq_set_exclusive_handler(LOW_PRIO_IRQ, draw_1b_buffer);
    irq_set_enabled(LOW_PRIO_IRQ, true);

    sem_release(&core1_launch);
    // sem_release(&display_frame_freed);
    irq_set_pending(LOW_PRIO_IRQ);

    // DEBUG_PINS_SET(dbg1, 1);
    // DEBUG_PINS_SET(dbg2, 1);
    
    // draw_1b_buffer();

    while (true)
    {
        pd_core1_loop();

        // draw_1b_buffer();
     
        // tight_loop_contents();
    }
}


void I_ShutdownGraphics(void)
{

}


void I_StartFrame (void)
{

}


void I_SetWindowTitle(const char *title)
{

}


void I_SetPaletteNum(int doompalette)
{
    next_pal = doompalette;
}


void I_FinishUpdate (void)
{

}


void I_InitGraphics(void)
{

    printf("SW id: %lu\n", sw_number);

    stbar = resolve_vpatch_handle(VPATCH_STBAR);
    sem_init(&render_frame_ready, 0, 2);
    sem_init(&display_frame_freed, 1, 2);
    sem_init(&core1_launch, 0, 1);
    pd_init();
    multicore_launch_core1(core1);
    // wait for core1 launch as it may do malloc and we have no mutex around that
    sem_acquire_blocking(&core1_launch);

    disallow_core1_malloc = true;
    initialized = true;
}


void I_BindVideoVariables(void)
{

}


void I_StartTic (void)
{
    if (!initialized)
    {
        return;
    }

    I_GetEvent();
}


void I_UpdateNoBlit (void)
{

}


int I_GetPaletteIndex(int r, int g, int b)
{
    return 0;
}


void I_Endoom(byte *endoom_data) {

}


void I_GraphicsCheckCommandLine(void)
{

}


void I_CheckIsScreensaver(void)
{

}


void I_DisplayFPSDots(boolean dots_on)
{

}
