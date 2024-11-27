// Adapted from https://github.com/mtikekar/advanced_bsv
// https://github.com/B-Lang-org/bsc/blob/708607343d6e0ac31aa509eca1c918aaa4509ffb/testsuite/bsc.bsv_examples/xbar/XBar.bsv
import FIFOF :: *;
import Vector :: *;

interface Deq#(type t);
  method Action deq;
  method t first;
  method Bool notEmpty;
endinterface

interface Enq#(type t);
  method Action enq(t x);
endinterface

typedef struct {
  Vector#(n, Enq#(t)) iport;
  Deq#(t) oport;
} MergeTree#(numeric type n, type t);

typeclass Merger#(numeric type n, type t);
  module mkMergeTree_(MergeTree#(n, t));
endtypeclass

instance Merger#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkMergeTree_(MergeTree#(1, t));
    FIFOF#(t) in <- mkGLFIFOF(False, True); // only enq is guarded
    MergeTree#(1, t) ret;

    ret.iport[0] =
      (interface Enq;
        method enq = in.enq;
      endinterface);
    ret.oport =
      (interface Deq;
        method deq = in.deq;
        method first = in.first;
        method notEmpty = in.notEmpty;
      endinterface);

    return ret;
  endmodule
endinstance

instance Merger#(n, t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Merger#(hn, t), Merger#(hm, t),
  Bits#(t, tSz)
);

  // General case
  module mkMergeTree_(MergeTree#(n, t));
    // two subtrees
    MergeTree#(hn, t) l <- mkMergeTree_;
    MergeTree#(hm, t) r <- mkMergeTree_;
    Reg#(Bool) lPrio <- mkReg (True);
    FIFOF#(t) out <- mkGLFIFOF(False, True); // only enq is guarded
    MergeTree#(n, t) ret;

    (* fire_when_enabled *)
    rule arbitrate_both(l.oport.notEmpty && r.oport.notEmpty);
      let x = lPrio ? l.oport.first : r.oport.first;
      if (lPrio) l.oport.deq; else r.oport.deq;
      out.enq(x);
      lPrio <= !lPrio;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_left(l.oport.notEmpty && !r.oport.notEmpty);
      let x = l.oport.first;
      l.oport.deq;
      out.enq(x);
      lPrio <= False;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_right(!l.oport.notEmpty && r.oport.notEmpty);
      let x = r.oport.first;
      r.oport.deq;
      out.enq(x);
      lPrio <= True;
    endrule

    ret.iport = append(l.iport, r.iport);
    ret.oport =
      (interface Deq;
        method deq = out.deq;
        method first = out.first;
        method notEmpty = out.notEmpty;
      endinterface);

    return ret;
  endmodule
endinstance

// guard oport only at the interface
module mkMergeTree(MergeTree#(n, t)) provisos (Merger#(n, t));
  MergeTree#(n, t) inner <- mkMergeTree_;
  MergeTree#(n, t) ret;

  ret.iport = inner.iport;
  ret.oport =
    (interface Deq;
      method deq if (inner.oport.notEmpty) = inner.oport.deq;
      method first if (inner.oport.notEmpty) = inner.oport.first;
      method notEmpty = inner.oport.notEmpty;
    endinterface);

  return ret;
endmodule

