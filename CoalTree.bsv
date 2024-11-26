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
    CoalTree#(hn, t) g1 <- mkCoalTree_;
    CoalTree#(hm, t) g2 <- mkCoalTree_;
    FIFOF#(EpochReq#(n, t)) out <- mkGFIFOF(False, True); // only enq is guarded
    Reg#(Bool) epoch <- mkReg(False);

    (* fire_when_enabled *)
    rule get_result;
      match {.req1, .epoch1} = g1.first;
      match {.req2, .epoch2} = g2.first;

      EpochReq#(n, t) selL = begin
        let req = case (req1) matches
          tagged Valid .reqL:
            tagged Valid (CoalReq {
              mask: append(reqL.mask, replicate(False)),
              req: reqL.req
            });
          tagged Invalid: tagged Invalid;
        endcase;
        tuple2(req, epoch1);
      end; // select left

      EpochReq#(n, t) selR = begin
        let req = case (req2) matches
          tagged Valid .reqR:
            tagged Valid (CoalReq {
              mask: append(replicate(False), reqR.mask),
              req: reqR.req
            });
          tagged Invalid: tagged Invalid;
        endcase;
        tuple2(req, epoch2);
      end; // select right

      EpochReq#(n, t) selB = begin
        let req = case (tuple2(req1, req2)) matches
          {tagged Valid .reqL, tagged Valid .reqR}:
            tagged Valid (CoalReq {
              mask: append(reqL.mask, reqR.mask),
              req: reqL.req
            });
          default: tagged Invalid;
        endcase;
        tuple2(req, epoch1);
      end; // select both

      case (tuple2(g1.notEmpty, g2.notEmpty)) matches
        {True, True}:
          if (epoch1 == epoch2) begin
            epoch <= epoch1;
            case (tuple2(req1, req2)) matches
              {tagged Valid .reqL, tagged Valid .reqR}: begin
                let dir = compare(pack(reqL.req), pack(reqR.req));
                let sel = case (dir) LT: selL; GT: selR; EQ: selB; endcase;
                out.enq(sel);
                if (dir != GT) g1.deq;
                if (dir != LT) g2.deq;
              end
              {tagged Valid .*, .*}: begin out.enq(selL); g1.deq; g2.deq; end
              default: begin out.enq(selR); g1.deq; g2.deq; end
            endcase
          end else if (epoch1 == epoch) begin
            out.enq(selL); g1.deq;
          end else begin // epoch2 == epoch
            out.enq(selR); g2.deq;
          end
        {True, False}: begin epoch <= epoch1; out.enq(selL); g1.deq; end
        {False, True}: begin epoch <= epoch2; out.enq(selR); g2.deq; end
        {False, False}: noAction;
      endcase
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

// guard deq and first only at the interface
module mkCoalTree(CoalTree#(n, t)) provisos (Coalescer#(n, t));
  CoalTree#(n, t) inner <- mkCoalTree_;
  method enq = inner.enq;
  method notEmpty = inner.notEmpty;
  method deq if (inner.notEmpty) = inner.deq;
  method first if (inner.notEmpty) = inner.first;
endmodule

