/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021 Synopsys, Inc.                                   **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

/*
 * npu_shared_hl_te.h
 *
 * File defining utility function for verification tasks
 *
 */
#ifndef NPU_HL_SHARED_TE_INCLUDED
#define NPU_HL_SHARED_TE_INCLUDED

#include "npu_hlapi.hpp"

namespace npu {
  class hl_te {
  public:
    // w32 hex print
    inline void w32hexprint(FILE *pfid, int32_t v, unsigned z, unsigned y,
                            unsigned x, unsigned h, unsigned w) {
      const char *pLT = "-----+";
      const char *pT  = "--------+";
      //const char *pL  = "----|";
      if (0==(x|y)) { //Top header
        fprintf(pfid, "%4x |", z);
        for (unsigned i=0; i<w; i++) { fprintf(pfid, " %8x", i); }
        fprintf(pfid, "\n");

        fprintf(pfid, "%s", pLT);
        for (unsigned i=0; i<w; i++) { fprintf(pfid, "%s", pT); }
        fprintf(pfid, "\n");
      }
      if (0==x)   fprintf(pfid, "%4x |", y);
      fprintf(pfid, (x==w-1)?" %08x\n":" %08x", v);
    }

    inline void w16hexprint(FILE *pfid, int32_t v, unsigned z, unsigned y,
                            unsigned x, unsigned h, unsigned w) {
      const char *pLT = "-----+";
      const char *pT  = "-----+";
      //const char *pL  = "----|";
      if (0==(x|y)) { //Top header
        fprintf(pfid, "%4x |", z);
        for (unsigned i=0; i<w; i++) { fprintf(pfid, " %5x", i); }
        fprintf(pfid, "\n");

        fprintf(pfid, "%s", pLT);
        for (unsigned i=0; i<w; i++) { fprintf(pfid, "%s", pT); }
        fprintf(pfid, "\n");
      }
      if (0==x)   fprintf(pfid, "%4x |", y);
      fprintf(pfid, (x==w-1)?"  %04x\n":"  %04x", v&0xffff);
    }

    // dump AM content
    inline void dump_am(const char *pof, int format/*0:chex 1:thex*/, vyixacc_t *a,
                        int d=0, int h=0, int w=0,
                        int xs=0, int ys=0, int zs=0,
                        int xl=VSIZE/*cols*/, int yl=1/*rows*/,
                        int zl=ISIZE/*depth*/) {
      d = (d==0) ? (zs+zl) : d;
      h = (h==0) ? (ys+yl) : h;
      w = (w==0) ? (xs+xl) : w;
      printf("d=%d w=%d h=%d VSIZE=%d ISIZE=%d\n", d, w, h ,VSIZE,ISIZE);
      assert((zs+zl<=d) && (ys+yl<=h) && (xs+xl<=w));
      //FIXME: for AM, the zl is fixed to ISIZE and xl is fixed to VSIZE
      assert((zs<ISIZE) && (zl==ISIZE));
      assert((xs==0) && (xl==VSIZE));

      uint32_t w32 = 0;
      FILE *outf = NULL;
      //assert(NULL != (outf= fopen(pof, "w")));
      outf= fopen(pof, "w");
      for (int zz=zs; zz<zl; zz++) {
        for (int yy=ys; yy<yl; yy++) {
          for (int xx=xs; xx<xl; xx++) {
            w32 = a[yy][xx][zz];
            if (0==format) w32hexprint(outf, w32, zz, yy, xx, h, w);
            else           fprintf(outf, "0x%08x\n", w32&0xffffffff);
          }
        }
        fprintf(outf, "\n");
      }
      fclose(outf);
    }

    // dump VM content
    inline void dump_vm(const char *pof, int format/*0:chex 1:thex*/, ixpix_t *p,
                        int d=0, int h=0, int w=0,
                        int xs=0, int ys=0, int zs=0,
                        int xl=VSIZE/*cols*/, int yl=1/*rows*/, 
                        int zl=ISIZE/*depth*/) {
      d = (d==0) ? (zs+zl) : d;
      h = (h==0) ? (ys+yl) : h;
      w = (w==0) ? (xs+xl) : w;
      printf("d=%d w=%d h=%d VSIZE=%d ISIZE=%d zs=%d zl=%d ys=%d yl=%d xs=%d xl=%d\n", d, w, h,VSIZE,ISIZE,zs,zl,ys,yl,xs,xl);
      assert((zs+zl<=d) && (ys+yl<=h) && (xs+xl<=w));
      assert((zs<ISIZE) && (zl==ISIZE));

      uint16_t w16 = 0;
      FILE *outf = NULL;
      //assert(NULL != (outf= fopen(pof, "w")));
      outf= fopen(pof, "w");
      for (int zz=zs; zz<zl; zz++) {
        for (int yy=ys; yy<yl; yy++) {
          for (int xx=xs; xx<xl; xx++) {
            w16 = p[yy*w+xx][zz];
            if (0==format) w16hexprint(outf, w16, zz, yy, xx, h, w);
            else           fprintf(outf, "0x%04x\n", w16&0xffff);
          }
        }
        fprintf(outf, "\n");
      }
      fclose(outf);
    }

    inline void dump_vm_dma_pix_t(const char *pof, int format/*0:thex 1:chex*/, pix_t *p, int size){

      uint16_t w16 = 0;
      FILE *outf = NULL;
      outf= fopen(pof, "w");
      for (int index=0; index<size; index++) {
            w16 = p[index];
            if (1==format)  fprintf(outf, "0x%04x\n", w16&0x00ff);
      }
      fclose(outf);
    }

    template<typename T, size_t R> void dump_vm_tensor(const char *pof, const tensor_t<T,R>& a) {
      // print to output stream with a given number of elements per line
      FILE *outf = NULL;
      outf= fopen(pof, "w");
      //assert(((a.get_dim(0)%ISIZE) == 0) && "Channel dimension should be mutliple of ISIZE" );
      const_tensor_iterator_t<T,R> it(a);

      fprintf(outf, "// idx of isize:   ");
      for (int i = 0; i < (int)a.get_dim(0); i++) {
        fprintf(outf, "%02d   ", i);
      }
      fprintf(outf, "\n");

      int c = 0;
      do {
        if(c==0) {
          fprintf(outf, "VM");
          for (int i = (int)R-1; i > 0;  i--) {
            fprintf(outf, "[%02d]", it.get_index(i));
          }
          fprintf(outf, "[]:");
        }

        fprintf(outf, " 0x%02x", (uint8_t)it.read());
        c++;
        if(c == (int)a.get_dim(0)){
          fprintf(outf, "\n");
          c=0;
        }
      } while (it.next());

      fclose(outf);
    }

    template<typename T, size_t R> void dump_xm_tensor(const char *pof, const tensor_t<T,R>& a) {
      // print to output stream with a given number of elements per line
      FILE *outf = NULL;
      outf= fopen(pof, "w");
      //assert(((a.get_dim(0)%ISIZE) == 0) && "Channel dimension should be mutliple of ISIZE" );
      const_tensor_iterator_t<T,R> it(a);

      fprintf(outf, "// idx of isize:   ");
      for (int i = 0; i < (int)a.get_dim(0); i++) {
        fprintf(outf, "%02d   ", i);
      }
      fprintf(outf, "\n");

      int c = 0;
      do {
        if(c==0) {
          fprintf(outf, "XM");
          for (int i = (int)R-1; i > 0;  i--) {
            fprintf(outf, "[%02d]", it.get_index(i));
          }
          fprintf(outf, "[]:");
        }

        fprintf(outf, " 0x%02x", (uint8_t)it.read());
        c++;
        if(c == (int)a.get_dim(0)){
          fprintf(outf, "\n");
          c=0;
        }
      } while (it.next());

      fclose(outf);
    }

    template<typename T, size_t R> void dump_tensor(const char *pof, const tensor_t<T,R>& a) {
      // print to output stream with a given number of elements per line
      FILE *outf = NULL;
      outf= fopen(pof, "w");
      //assert(((a.get_dim(0)%ISIZE) == 0) && "Channel dimension should be mutliple of ISIZE" );
      const_tensor_iterator_t<T,R> it(a);

      fprintf(outf, "// idx of isize:   ");
      for (int i = 0; i < (int)a.get_dim(0); i++) {
        fprintf(outf, "%02d   ", i);
      }
      fprintf(outf, "\n");

      int c = 0;
      do {
        if(c==0) {
          shape<R> pos;
          for (int i = (int)R-1; i > 0;  i--) {
            fprintf(outf, "[%02d]", it.get_index(i));
            pos[i]=it.get_index(i);
          }
          fprintf(outf, "[]:");
          //printf("ptr:%p, off:0x%0x\n", a.ptr + a.get_offset(pos), a.get_offset(pos) );
        }

        fprintf(outf, " 0x%02x", (uint8_t)it.read());
        c++;
        if(c == (int)a.get_dim(0)){
          fprintf(outf, "\n");
          c=0;
        }
      } while (it.next());

      fclose(outf);
    }

  };

} //namespace

#endif
