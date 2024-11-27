// Adapted from https://github.com/mtikekar/advanced_bsv
// https://github.com/B-Lang-org/bsc/blob/708607343d6e0ac31aa509eca1c918aaa4509ffb/testsuite/bsc.bsv_examples/xbar/XBar.bsv
import FIFOF :: *;
import Vector :: *;

interface MergeTree#(numeric type n, type t);
  method Action enq(Vector#(n, Maybe#(t)) v);
  method Bool notEmpty;
  method Action deq;
  method t first;
endinterface

typeclass Merger#(numeric type n, type t);
  module mkMergeTree_(MergeTree#(n, t));
endtypeclass

instance Merger#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkMergeTree_(MergeTree#(1, t));
    FIFOF#(t) in <- mkGFIFOF(False, True); // only enq is guarded

    method Action enq(v);
      case (v[0]) matches
        tagged Invalid: noAction;
        tagged Valid .req: in.enq(req);
      endcase
    endmethod

    method notEmpty = in.notEmpty;

    method deq = in.deq; // must be called under if (notEmpty)

    method first = in.first;
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
    MergeTree#(hn, t) g1 <- mkMergeTree_;
    MergeTree#(hm, t) g2 <- mkMergeTree_;
    Reg#(Bool) leftHasPrio <- mkReg (True);
    FIFOF#(t) out <- mkFIFOF;

    (* fire_when_enabled *)
    rule arbitrate_both(g1.notEmpty && g2.notEmpty);
      let x = leftHasPrio ? g1.first : g2.first;
      if (leftHasPrio) g1.deq; else g2.deq;
      out.enq(x);
      leftHasPrio <= !leftHasPrio;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_left(g1.notEmpty && !g2.notEmpty);
      let x = g1.first;
      g1.deq;
      out.enq(x);
      leftHasPrio <= False;
    endrule

    (* fire_when_enabled *)
    rule arbitrate_right(!g1.notEmpty && g2.notEmpty);
      let x = g2.first;
      g2.deq;
      out.enq(x);
      leftHasPrio <= True;
    endrule

    method Action enq(v);
      g1.enq(take(v));
      g2.enq(takeTail(v));
    endmethod

    method notEmpty = out.notEmpty;

    method deq = out.deq; // must be called under if (notEmpty)

    method first = out.first;
  endmodule
endinstance

// guard oport only at the interface
module mkMergeTree(MergeTree#(n, t)) provisos (Merger#(n, t));
  MergeTree#(n, t) inner <- mkMergeTree_;
  method enq = inner.enq;
  method notEmpty = inner.notEmpty;
  method deq if (inner.notEmpty) = inner.deq;
  method first if (inner.notEmpty) = inner.first;
endmodule

