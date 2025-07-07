#ifndef ARCH_NPU_IDMA_REGRESSION_UTILS_COMPRESS_TEST_HPP_
#define ARCH_NPU_IDMA_REGRESSION_UTILS_COMPRESS_TEST_HPP_

#include <npu_idma_hl_top.hpp>

#ifndef XM_CHAN
#define XM_CHAN    10
#endif
#ifndef XM_COL
#define XM_COL     10
#endif
#ifndef XM_ROW
#define XM_ROW     10
#endif

// Size of buffer in VM (chan as multiple of ISIZE).
#ifndef VM_CHAN
#define VM_CHAN     4
#endif
#ifndef VM_COL
#define VM_COL     16
#endif
#ifndef VM_ROW
#define VM_ROW     16
#endif

// Size of subtensor to be copied, compression per subtensor [H=2][W=2][C=16].
#ifndef SUB_CHAN0
#define SUB_CHAN0   16
#endif
#ifndef SUB_COL0
#define SUB_COL0    2
#endif
#ifndef SUB_ROW0
#define SUB_ROW0    2
#endif
#ifndef SUB_CHAN1
#define SUB_CHAN1   3
#endif
#ifndef SUB_COL1
#define SUB_COL1    4
#endif
#ifndef SUB_ROW1
#define SUB_ROW1    5
#endif

// Position in XM of subtensor.
#ifndef XM_ST_CHAN
#define XM_ST_CHAN  3
#endif
#ifndef XM_ST_COL
#define XM_ST_COL   2
#endif
#ifndef XM_ST_ROW
#define XM_ST_ROW   1
#endif

// Position in VM of subtensor, wraps (chan as multiple of ISIZE).
#ifndef VM_ST_CHAN
#define VM_ST_CHAN  0
#endif
#ifndef VM_ST_COL
#define VM_ST_COL   0
#endif
#ifndef VM_ST_ROW
#define VM_ST_ROW   0
#endif


#define DIVIX_RNDUP(x) ((x+ISIZE-1)/ISIZE)

#define S0 DIVIX_RNDUP(SUB_CHAN0)

#define CBLEN (S0 * SUB_COL0 * SUB_ROW0)

#define CONTAINER_SIZE ((CBLEN + 3) / 4 * CPS_GROUP_SIZE)

using namespace npu;
using namespace npu_idma;

// TODO: this array is only used to calculate XM container offsets.
// Should be handled by the tensor API.
std::array<char, CONTAINER_SIZE> cps_data[XM_ROW][XM_COL][XM_CHAN];

// MMIO registers
ctrl_dma_regs<dma_hlapi_t> rgs;

// buffers in XM and VM
buffer_t<pix_t>   xb;
buffer_t<char>    mb;
buffer_t<ixpix_t> vb;

// instantiate memories
hl_dm dm("dm");
hl_xm xm("xm");
hl_vm vm("vm");

void report_vm(ostream& os) {
  tensor_t<ixpix_t, 3> vt(vb, {VM_CHAN, VM_COL, VM_ROW});
  tensor_iterator_t<ixpix_t, 3> vi(vt);
  for (int h = 0; h < VM_ROW; h++) {
    for (int w = 0; w < VM_COL; w++) {
      for (int c = 0; c < VM_CHAN; c++) {
        os << "REPORT vm[" << h << "][" << w << "][" << c << "]: " << vi.read() << endl;
        vi.next();
      }
    }
  }
}

//
// The test
//
class testprog : public arc_program {
 public:
  inline testprog(const char* file)
    : arc_program()
    , irqflag(false) {
    rptos.open(file);
  }

  virtual void irq() {
    rptos << "REPORT interrupt" << endl;
    irqflag = true;
  }

  void exec() {
    init_mem(xm, vm);

    // read the ID register value
    rptos << "REPORT id.typ: " << rgs.id.tp << ", id.maj: " << ((int)rgs.id.maj) << ", id.min: " << ((int)rgs.id.min) << endl;

    // program the DMA descriptor directly in the idma registers
    rgs.hlapi.i.common.ctrl   = (1 << 16);  // interrupt
    rgs.int_enable            = 1;
    rgs.hlapi.o.status        = 0;
    rgs.hlapi.io.cycles       = 0;
    rgs.hlapi.i.common.next   = nullptr;

    // VM descriptor
    tensor_t<ixpix_t, 3> vt(vb, {VM_CHAN, VM_COL, VM_ROW});
    tensor_t<ixpix_t, 3> vts(vt.slice({VM_ST_CHAN, VM_ST_COL, VM_ST_ROW},
                                      {S0 * SUB_CHAN1, SUB_COL0 * SUB_COL1, SUB_ROW0 * SUB_ROW1}));
    tensor_t<ixpix_t, 6> vtss(vts.split(0, SUB_CHAN1).split(2, SUB_COL1).split(4, SUB_ROW1));
    tensor_t<ixpix_t, 6> vtsst(vtss.transpose({0, 2, 4, 1, 3, 5}));
    rgs.hlapi.i.vm_seq.ptr = localptr_t<ixpix_t>(vtsst.get_ptr());
    rgs.hlapi.i.vm_seq.buf = buf_t<ixpix_t>(localptr_t<ixpix_t>(vtsst.get_base()), vtsst.get_size());
    rgs.hlapi.i.vm_seq.stride = 1;
    // VM pointer post-increments
    rgs.hlapi.i.vm_seq.offsets[NUM_FM_LOOPS-1] = vtsst.get_offset_last(0);
    rgs.hlapi.i.vm_seq.offsets[NUM_FM_LOOPS-2] = vtsst.get_offset_last(1);
    rgs.hlapi.i.vm_seq.offsets[NUM_FM_LOOPS-3] = vtsst.get_offset_last(2);
    rgs.hlapi.i.vm_seq.offsets[NUM_FM_LOOPS-4] = vtsst.get_offset_last(3);
    rgs.hlapi.i.vm_seq.offsets[NUM_FM_LOOPS-5] = vtsst.get_offset_last(4);
    rgs.hlapi.i.vm_seq.offsets[NUM_FM_LOOPS-6] = vtsst.get_offset_last(5);
    // VM loop iteration counts inner to outer
    rgs.hlapi.i.vm_seq.iter[NUM_FM_LOOPS-1] = S0;
    rgs.hlapi.i.vm_seq.iter[NUM_FM_LOOPS-2] = SUB_COL0;
    rgs.hlapi.i.vm_seq.iter[NUM_FM_LOOPS-3] = SUB_ROW0;
    rgs.hlapi.i.vm_seq.iter[NUM_FM_LOOPS-4] = SUB_CHAN1;
    rgs.hlapi.i.vm_seq.iter[NUM_FM_LOOPS-5] = SUB_COL1;
    rgs.hlapi.i.vm_seq.iter[NUM_FM_LOOPS-6] = SUB_ROW1;

    // XM descriptor
    rgs.hlapi.i.xm_seq.compress = true;
    rgs.hlapi.i.xm_seq.cblen = CBLEN;
    rgs.hlapi.i.xm_seq.iter[NUM_FM_LOOPS-1] = SUB_CHAN1;
    rgs.hlapi.i.xm_seq.iter[NUM_FM_LOOPS-2] = SUB_COL1;
    rgs.hlapi.i.xm_seq.iter[NUM_FM_LOOPS-3] = SUB_ROW1;
    rgs.hlapi.i.xm_seq.iter[NUM_FM_LOOPS-4] = 1;  // unused
    rgs.hlapi.i.xm_seq.iter[NUM_FM_LOOPS-5] = 1;  // unused
    rgs.hlapi.i.xm_seq.iter[NUM_FM_LOOPS-6] = 1;  // unused

    // XM data
    tensor_t<pix_t, 3> xt(xb, {CONTAINER_SIZE * XM_CHAN, XM_COL, XM_ROW});
    tensor_t<pix_t, 3> xts(xt.slice({CONTAINER_SIZE * XM_ST_CHAN, XM_ST_COL, XM_ST_ROW},
                                    {SUB_CHAN1 * CONTAINER_SIZE, SUB_COL1, SUB_ROW1}));
    rgs.hlapi.i.xm_seq.ptr = xts.get_ptr();
    rgs.hlapi.i.xm_seq.buf = xm_buf_t<pix_t>(xts.get_base(), xts.get_size());
    // FIXME: Using  xts.get_offset_last will not work since this tensor is of the wrong type.
    rgs.hlapi.i.xm_seq.offsets[NUM_FM_LOOPS-1] = ((pix_t*)&cps_data[0][0][1])-((pix_t*)&cps_data[0][0         ][          0]);
    rgs.hlapi.i.xm_seq.offsets[NUM_FM_LOOPS-2] = ((pix_t*)&cps_data[0][1][0])-((pix_t*)&cps_data[0][0         ][SUB_CHAN1-1]);
    rgs.hlapi.i.xm_seq.offsets[NUM_FM_LOOPS-3] = ((pix_t*)&cps_data[1][0][0])-((pix_t*)&cps_data[0][SUB_COL1-1][SUB_CHAN1-1]);
    rgs.hlapi.i.xm_seq.offsets[NUM_FM_LOOPS-4] = 0;
    rgs.hlapi.i.xm_seq.offsets[NUM_FM_LOOPS-5] = 0;
    rgs.hlapi.i.xm_seq.offsets[NUM_FM_LOOPS-6] = 0;

    // XM metadata
    tensor_t<char, 3> mt(mb, {XM_CHAN, XM_COL, XM_ROW});
    tensor_t<char, 3> mts(mt.slice({XM_ST_CHAN, XM_ST_COL, XM_ST_ROW}, {SUB_CHAN1, SUB_COL1, SUB_ROW1}));
    rgs.hlapi.i.xm_seq.p.mptr = mts.get_ptr();
    rgs.hlapi.i.xm_seq.b.mbuf = xm_buf_t<char>(mts.get_base(), xts.get_size());
    // XM pointer post-increments
    rgs.hlapi.i.xm_seq.o.moffsets[NUM_FM_LOOPS-1] = mts.get_offset_last(0);
    rgs.hlapi.i.xm_seq.o.moffsets[NUM_FM_LOOPS-2] = mts.get_offset_last(1);
    rgs.hlapi.i.xm_seq.o.moffsets[NUM_FM_LOOPS-3] = mts.get_offset_last(2);
    rgs.hlapi.i.xm_seq.o.moffsets[NUM_FM_LOOPS-4] = 0;
    rgs.hlapi.i.xm_seq.o.moffsets[NUM_FM_LOOPS-5] = 0;
    rgs.hlapi.i.xm_seq.o.moffsets[NUM_FM_LOOPS-6] = 0;

    rgs.hlapi.i.zero_point    = 0;
    rgs.hlapi.i.planar_stride = 0; // not in planar mode
    rgs.hlapi.i.planar_offset = 0;

    // trigger the HLAPI execution
    rgs.issue = 1;
    // model some delay
    run_cycles(100);
    while (rgs.status != 0) {
      wait_cycles(10);
    }
    // check if interrupt set and clear flag
    assert (rgs.int_status == 1);
    rgs.int_clear = 1;
    while (rgs.int_status != 0) {
      wait_cycles(1);
    }

    report_vm(rptos);
    rptos.close();
    arc_exit();
  }
  void init_mem(hl_xm& xm, hl_vm& vm) {
    // Initialize XM from memory image produced by oDMA test.
    mem_alloc_t xmalloc(0, xm.size());
    xmalloc.alloc(xb, XM_ROW * XM_COL * XM_CHAN * CONTAINER_SIZE);
    std::ifstream xb_img("xb.img", ios::binary);
    for (unsigned i = 0; i < xb.get_size(); i++) {
      pix_t pix;
      xb_img.read((char*)&pix, sizeof(pix_t));
      xb.write(xb.get_base(), i, pix);
    }
    xb_img.close();

    // Initialize metadata from memory image produced by oDMA test.
    xmalloc.alloc(mb, XM_ROW * XM_COL * XM_CHAN);
    std::ifstream mb_img("mb.img", ios::binary);
    for (unsigned i = 0; i < mb.get_size(); i++) {
      char c;
      mb_img.read(&c, sizeof(char));
      mb.write(mb.get_base(), i, c);
    }
    mb_img.close();

    for (unsigned i = 0; i < mb.get_size(); i++) {
      mb.write(mb.get_base(), i, (pix_t)0);
    }

    // initialize VM to 0xFF
    mem_alloc_t vmalloc(reinterpret_cast<uint64_t>(get_slice_vm_base()), vm.size());
    vmalloc.alloc(vb, VM_CHAN * VM_COL * VM_ROW);
    tensor_t<ixpix_t, 3> vt(vb, {VM_CHAN, VM_COL, VM_ROW});
    tensor_iterator_t<ixpix_t, 3> vi(vt);
    ixpix_t v;
    do {
      for (int i = 0; i < ISIZE; i++) {
        v[i] = (pix_t)-1;
      }
      vi.write(v);
    } while (vi.next());
  }
 private:
  bool irqflag;
  std::ofstream rptos;
};

#include "../common/test_sc.hpp"

#endif  // ARCH_NPU_IDMA_REGRESSION_UTILS_COMPRESS_TEST_HPP_
