// Adapted from https://github.com/mtikekar/advanced_bsv
import FIFOF :: *;
import SpecialFIFOs :: *;
import Vector :: *;
import GetPut :: *;

typedef Tuple2#(Maybe#(t), Bool) Epoch#(type t);

// Serializer, specialized version of CoalTrees
interface SerTree#(numeric type n, type t);
  method Action enq(Vector#(n, Maybe#(t)) v);
  method Bool notEmpty;
  method Action deq;
  method Epoch#(t) first;
endinterface

typeclass Serializer#(numeric type n, type t);
  module mkSerTree(SerTree#(n, t));
endtypeclass

instance Serializer#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkSerTree(SerTree#(1, t));
    FIFOF#(Epoch#(t)) in <- mkBypassFIFOF;
    Reg#(Bool) epoch <- mkReg(False);

    method Action enq(Vector#(1, Maybe#(t)) v);
      in.enq(tuple2(v[0], epoch));
      epoch <= !epoch;
    endmethod

    method notEmpty = in.notEmpty;

    method deq = in.deq;

    method first = in.first;
  endmodule
endinstance

instance Serializer#(n, t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Serializer#(hn, t), Serializer#(hm, t),
  Bits#(t, tSz)
);

  // General case
  module mkSerTree (SerTree#(n, t));
    // two subtrees
    SerTree#(hn, t) l <- mkSerTree;
    SerTree#(hm, t) r <- mkSerTree;
    FIFOF#(Epoch#(t)) out <- mkBypassFIFOF;
    Reg#(Bool) epoch <- mkReg(False);

    let selL = l.first;
    let selR = r.first;
    match {.reqL, .epochL} = selL;
    match {.reqR, .epochR} = selR;

    (* fire_when_enabled *)
    rule get_result_both(l.notEmpty && r.notEmpty);
      if (epochL == epochR) begin
        epoch <= epochL;
        case (tuple2(reqL, reqR)) matches
          {tagged Valid .*, tagged Valid .*}: begin out.enq(selL); l.deq; end
          {tagged Valid .*, .*}: begin out.enq(selL); l.deq; r.deq; end
          default: begin out.enq(selR); l.deq; r.deq; end
        endcase
      end else if (epochL == epoch) begin
        out.enq(selL); l.deq;
      end else begin // epochR == epoch
        out.enq(selR); r.deq;
      end
    endrule

    (* fire_when_enabled *)
    rule get_result_left(l.notEmpty && !r.notEmpty);
      epoch <= epochL;
      out.enq(selL);
      l.deq;
    endrule

    (* fire_when_enabled *)
    rule get_result_right(!l.notEmpty && r.notEmpty);
      epoch <= epochR;
      out.enq(selR);
      r.deq;
    endrule

    method Action enq(Vector#(n, Maybe#(t)) v);
      l.enq(take(v));
      r.enq(takeTail(v));
    endmethod

    method notEmpty = out.notEmpty;

    method deq = out.deq; // must be called under if (notEmpty)

    method first = out.first;
  endmodule
endinstance

interface MergeTree#(numeric type n, type t);
  interface Vector#(n, Put#(t)) iport;
  method Action deq;
  method Maybe#(t) first;
  method Bool notEmpty;
endinterface

module mkMergeTree(MergeTree#(n, t))
  provisos (Serializer#(n, t), Bits#(t, tSz));
  (* hide *) Vector#(n, FIFOF#(t)) iports <- replicateM(mkLFIFOF);
  (* hide *) SerTree#(n, t) inner <- mkSerTree;

  function Bool isNotEmpty(FIFOF#(t) fifo) = fifo.notEmpty;

  (* fire_when_enabled *)
  rule enq_inner(any(isNotEmpty, iports));
    Vector#(n, Maybe#(t)) v = replicate(tagged Invalid);
    for (Integer i = 0; i < valueOf(n); i = i + 1)
      if (iports[i].notEmpty) begin
        v[i] = tagged Valid iports[i].first;
        iports[i].deq;
      end
    inner.enq(v);
  endrule

  interface iport = map(toPut, iports);
  method deq = inner.deq;
  method first if (inner.notEmpty) = tpl_1(inner.first);
  method notEmpty = inner.notEmpty;
endmodule

