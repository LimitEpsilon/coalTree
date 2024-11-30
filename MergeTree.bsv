// Adapted from https://github.com/mtikekar/advanced_bsv
// https://github.com/B-Lang-org/bsc/blob/708607343d6e0ac31aa509eca1c918aaa4509ffb/testsuite/bsc.bsv_examples/xbar/XBar.bsv
import FIFOF :: *;
import Vector :: *;
import GetPut :: *;

interface MergeTree#(numeric type n, type t);
  interface Vector#(n, Put#(t)) iport;
  method Action deq;
  method t first;
  method Bool notEmpty;
endinterface

typeclass Merger#(numeric type n, type t);
  module mkMergeTree_(MergeTree#(n, t));
endtypeclass

instance Merger#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkMergeTree_(MergeTree#(1, t));
    FIFOF#(t) in <- mkGLFIFOF(False, True); // only enq is guarded
    Vector#(1, Put#(t)) i;

    i[0] =
      (interface Put;
        method put = in.enq;
      endinterface);

    interface iport = i;
    method deq = in.deq;
    method first = in.first;
    method notEmpty = in.notEmpty;
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
    Reg#(Bool) lPrio <- mkReg (True); // the left tree has priority
    FIFOF#(t) out <- mkGLFIFOF(False, True); // only enq is guarded

    (* fire_when_enabled *)
    rule arbitrate_both(l.notEmpty && r.notEmpty);
      let x = lPrio ? l.first : r.first;
      out.enq(x);
      if (lPrio) l.deq; else r.deq;
      lPrio <= !lPrio;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_left(l.notEmpty && !r.notEmpty);
      let x = l.first;
      out.enq(x);
      l.deq;
      lPrio <= False;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_right(!l.notEmpty && r.notEmpty);
      let x = r.first;
      out.enq(x);
      r.deq;
      lPrio <= True;
    endrule

    interface iport = append(l.iport, r.iport);
    method deq = out.deq;
    method first = out.first;
    method notEmpty = out.notEmpty;
  endmodule
endinstance

// guard oport only at the interface
module mkMergeTree(MergeTree#(n, t)) provisos (Merger#(n, t));
  MergeTree#(n, t) inner <- mkMergeTree_;

  interface iport = inner.iport;
  method deq if (inner.notEmpty) = inner.deq;
  method first if (inner.notEmpty) = inner.first;
  method notEmpty = inner.notEmpty;
endmodule

