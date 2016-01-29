#include "abstract_heap.h"

// Run with -DNPROG=3

/*
        private static final char[] toBase64 = {
            'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
            'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
            'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
            'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '/'
        };

        private int encode0(byte[] src, int off, int end, byte[] dst) {
            char[] base64 = isURL ? toBase64URL : toBase64;
            int sp = off;
            int slen = (end - off) / 3 * 3;
            int sl = off + slen;
            if (linemax > 0 && slen  > linemax / 4 * 3)
                slen = linemax / 4 * 3;
            int dp = 0;
            while (sp < sl) {
                int sl0 = Math.min(sp + slen, sl);
                for (int sp0 = sp, dp0 = dp ; sp0 < sl0; ) {
                    int bits = (src[sp0++] & 0xff) << 16 |
                               (src[sp0++] & 0xff) <<  8 |
                               (src[sp0++] & 0xff);
                    dst[dp0++] = (byte)base64[(bits >>> 18) & 0x3f];
                    dst[dp0++] = (byte)base64[(bits >>> 12) & 0x3f];
                    dst[dp0++] = (byte)base64[(bits >>> 6)  & 0x3f];
                    dst[dp0++] = (byte)base64[bits & 0x3f];
                }
                int dlen = (sl0 - sp) / 3 * 4;
                dp += dlen;
                sp = sl0;
                if (dlen == linemax && sp < end) {
                    for (byte b : newline){
                        dst[dp++] = b;
                    }
                }
            }
            if (sp < end) {               // 1 or 2 leftover bytes
                int b0 = src[sp++] & 0xff;
                dst[dp++] = (byte)base64[b0 >> 2];
                if (sp == end) {
                    dst[dp++] = (byte)base64[(b0 << 4) & 0x3f];
                    if (doPadding) {
                        dst[dp++] = '=';
                        dst[dp++] = '=';
                    }
                } else {
                    int b1 = src[sp++] & 0xff;
                    dst[dp++] = (byte)base64[(b0 << 4) & 0x3f | (b1 >> 4)];
                    dst[dp++] = (byte)base64[(b1 << 2) & 0x3f];
                    if (doPadding) {
                        dst[dp++] = '=';
                    }
                }
            }
            return dp;
        }
    }*/

ptr_t src=1;
ptr_t dst=2;

data_t sp;
data_t slen;
data_t sl;
data_t dp;
data_t sl0;

// Input
const int linemax=-1;
const data_t off=0;
int sp0=off;
int dp0=0;
data_t end;
const _Bool doPadding=bool_true;

const int base64[] = {
            'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
            'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
            'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
            'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
            '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '/'
        };

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
}

void init_heap(abstract_heapt *heap) {
  heap->is_iterator[src] = 0;
  heap->is_iterator[dst] = 0;
}

void pre(abstract_heapt *heap) {
  // Inputs
  end=size(heap, src);
  Assume(empty(heap, dst) && !alias(heap, src, dst));
  // Inputs

  sp = off;
  slen = (end - off) / 3 * 3;
  sl = off + slen;
  if (linemax > 0 && slen  > linemax / 4 * 3)
    slen = linemax / 4 * 3;
  dp = 0;
  
  sl0 = sp + slen < sl ? sp + slen : sl;
}

_Bool cond(abstract_heapt *heap) {
  return sp < sl;
}

void body(abstract_heapt *heap) {
  //for (int sp0 = sp, dp0 = dp ; sp0 < sl0; ) {
  if (sp0 >= sl0) sl0 = sp + slen < sl ? sp + slen : sl;
  sp0 = sp, dp0 = dp ;
  if (sp0 < sl0) {
      int bits = (getP(heap, src, sp0++) & 0xff) << 16 |
                 (getP(heap, src, sp0++) & 0xff) <<  8 |
                 (getP(heap, src, sp0++) & 0xff);
      add(heap, dst, (unsigned char)base64[(bits >> 18) & 0x3f]);
      dp0++;
      add(heap, dst, (unsigned char)base64[(bits >> 12) & 0x3f]);
      dp0++;
      add(heap, dst, (unsigned char)base64[(bits >> 6)  & 0x3f]);
      dp0++;
      add(heap, dst, (unsigned char)base64[bits & 0x3f]);
      dp0++;
  } else {
    int dlen = (sl0 - sp) / 3 * 4;
    dp += dlen;
    sp = sl0;
  }
  // Unreachable. linexmax = -1 and newline = null.
  /*if (dlen == linemax && sp < end) {
      for (byte b : newline){
          dst[dp++] = b;
      }
  }*/
}

_Bool assertion(abstract_heapt *heap) {
  if (sp < end) {               // 1 or 2 leftover bytes
    int b0 = getP(heap, src, sp++) & 0xff;
    add(heap, dst, (unsigned char)base64[b0 >> 2]);
    dp++;
    if (sp == end) {
      add(heap, dst, (unsigned char)base64[(b0 << 4) & 0x3f]);
      dp++;
      if (doPadding) {
        add(heap, dst, '=');
        dp++;
        add(heap, dst, '=');
        dp++;
      }
    } else {
      int b1 = getP(heap, src, sp++) & 0xff;
      add(heap, dst, (unsigned char)base64[(b0 << 4) & 0x3f | (b1 >> 4)]);
      dp++;
      add(heap, dst, (unsigned char)base64[(b1 << 2) & 0x3f]);
      dp++;
      if (doPadding) {
        add(heap, dst, '=');
        dp++;
      }
    }
  }
  // 3:4
  return bool_false;
  //return size(heap, src) > size(heap, dst);
}
_Bool inv_check(abstract_heapt *heap) {
  return !alias(heap, src, dst) && sp <= dp && off == 0 && (slen == (end - off) / 3 * 3) && sl == off + slen;
  //return !alias(heap, src, dst) && sp <= dp && (slen == (end - off) / 3 * 3) && sl == off + slen && size(heap, src) == end && size(heap, dst) == dp;
}

_Bool inv_assume(abstract_heapt *heap) {
  return !alias(heap, src, dst) && sp <= dp && off == 0 && (slen == (end - off) / 3 * 3) && sl == off + slen;
  //return !alias(heap, src, dst) && sp <= dp && (slen == (end - off) / 3 * 3) && sl == off + slen && size(heap, src) == end && size(heap, dst) == dp;
}
