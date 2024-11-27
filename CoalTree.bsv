// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector::*;
import FIFOF::*;

// coalesced request
typedef struct {
  Vector#(n, Bool) mask;
  t req;
} CoalReq#(numeric type n, type t) deriving (Bits, Eq, FShow);

typedef
  Tuple2#(Maybe#(CoalReq#(n, t)), Bool)
  EpochReq#(numeric type n, type t);

interface CoalTree#(numeric type n, type t);
  method Action enq(Vector#(n, Maybe#(t)) v);
  method Bool notEmpty;
  method Action deq;
  method EpochReq#(n, t) first;
endinterface

typeclass Coalescer#(numeric type n, type t);
  module mkCoalTree_(CoalTree#(n, t));
endtypeclass

instance Coalescer#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkCoalTree_(CoalTree#(1, t));
    FIFOF#(EpochReq#(1, t)) in <- mkGFIFOF(False, True); // only enq is guarded
    Reg#(Bool) epoch <- mkReg(False);

    method Action enq(v);
      let req = case (v[0]) matches
        tagged Invalid: tagged Invalid;
        tagged Valid .req:
          tagged Valid (CoalReq {mask: replicate(True), req: req});
      endcase;
      in.enq(tuple2(req, epoch));
      epoch <= !epoch;
    endmethod

    method notEmpty = in.notEmpty;

    method deq = in.deq; // must be called under if (notEmpty)

    method first = in.first;
  endmodule
endinstance

instance Coalescer#(n, t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Coalescer#(hn, t), Coalescer#(hm, t),
  Bits#(t, tSz)
);

  // General case
  module mkCoalTree_(CoalTree#(n, t));
    // two subtrees
    CoalTree#(hn, t) l <- mkCoalTree_;
    CoalTree#(hm, t) r <- mkCoalTree_;
    FIFOF#(EpochReq#(n, t)) out <- mkGFIFOF(False, True); // only enq is guarded
    Reg#(Bool) epoch <- mkReg(False);

    match {.reqL, .epochL} = l.first;
    match {.reqR, .epochR} = r.first;

    EpochReq#(n, t) selL = begin
      let req = case (reqL) matches
        tagged Valid .rL:
          tagged Valid (CoalReq {
            mask: append(rL.mask, replicate(False)),
            req: rL.req
          });
        tagged Invalid: tagged Invalid;
      endcase;
      tuple2(req, epochL);
    end; // select left

    EpochReq#(n, t) selR = begin
      let req = case (reqR) matches
        tagged Valid .rR:
          tagged Valid (CoalReq {
            mask: append(replicate(False), rR.mask),
            req: rR.req
          });
        tagged Invalid: tagged Invalid;
      endcase;
      tuple2(req, epochR);
    end; // select right

    EpochReq#(n, t) selB = begin
      let req = case (tuple2(reqL, reqR)) matches
        {tagged Valid .rL, tagged Valid .rR}:
          tagged Valid (CoalReq {
            mask: append(rL.mask, rR.mask),
            req: rL.req
          });
        default: tagged Invalid;
      endcase;
      tuple2(req, epochL);
    end; // select both

    (* fire_when_enabled *)
    rule get_result_both(l.notEmpty && r.notEmpty);
      if (epochL == epochR) begin
        epoch <= epochL;
        case (tuple2(reqL, reqR)) matches
          {tagged Valid .rL, tagged Valid .rR}: begin
            let dir = compare(pack(rL.req), pack(rR.req));
            let sel = case (dir) LT: selL; GT: selR; EQ: selB; endcase;
            out.enq(sel);
            if (dir != GT) l.deq;
            if (dir != LT) r.deq;
          end
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

    method Action enq(v);
      l.enq(take(v));
      r.enq(takeTail(v));
    endmethod

    method notEmpty = out.notEmpty;

    method deq = out.deq; // must be called under if (notEmpty)

    method first = out.first;
  endmodule
endinstance

// guard deq and first only at the interface
module mkCoalTree(CoalTree#(n, t)) provisos (Coalescer#(n, t));
  CoalTree#(n, t) inner <- mkCoalTree_;
  method enq = inner.enq;
  method notEmpty = inner.notEmpty;
  method deq if (inner.notEmpty) = inner.deq;
  method first if (inner.notEmpty) = inner.first;
endmodule

