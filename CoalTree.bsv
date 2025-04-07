// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector::*;
import FIFOF::*;

// coalesced request
typedef struct {
  Bit#(n) mask;
  t req;
} CoalReq#(numeric type n, type t) deriving (Bits, Eq, FShow);

typedef
  Tuple2#(CoalReq#(n, t), Bool)
  EpochReq#(numeric type n, type t);

interface CoalTree#(numeric type n, type t);
  method ActionValue#(Bool) enq(Vector#(n, Maybe#(t)) v); // returns the epoch
  method Bool notEmpty;
  method Action deq;
  method EpochReq#(n, t) first;
endinterface

typeclass Coalescer#(numeric type n, type t);
  module mkCoalTree_#(function Ordering comp(t x, t y)) (CoalTree#(n, t));
endtypeclass

instance Coalescer#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkCoalTree_#(function Ordering comp(t x, t y)) (CoalTree#(1, t));
    FIFOF#(EpochReq#(1, t)) in <- mkGLFIFOF(False, True); // only enq is guarded
    Reg#(Bool) epoch <- mkReg(False);

    method ActionValue#(Bool) enq(Vector#(1, Maybe#(t)) v);
      let req = CoalReq {mask: pack(isValid(v[0])), req: fromMaybe(?, v[0])};
      let e = epoch;
      in.enq(tuple2(req, e));
      epoch <= !e;
      return e;
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
  module mkCoalTree_#(function Ordering comp(t x, t y)) (CoalTree#(n, t));
    // two subtrees
    CoalTree#(hn, t) l <- mkCoalTree_(comp);
    CoalTree#(hm, t) r <- mkCoalTree_(comp);
    FIFOF#(EpochReq#(n, t)) out <- mkGLFIFOF(False, True); // only enq is guarded
    Reg#(Bool) epoch <- mkReg(True);

    match {.reqL, .epochL} = l.first;
    match {.reqR, .epochR} = r.first;

    EpochReq#(n, t) selL = begin
      let req = CoalReq {
        mask: {0, reqL.mask},
        req: reqL.req
      };
      tuple2(req, epochL);
    end; // select left

    EpochReq#(n, t) selR = begin
      let req = CoalReq {
        mask: {reqR.mask, 0},
        req: reqR.req
      };
      tuple2(req, epochR);
    end; // select right

    EpochReq#(n, t) selB = begin
      let req = CoalReq {
        mask: {reqR.mask, reqL.mask},
        req: reqL.req
      };
      tuple2(req, epochL);
    end; // select both

    Bool empL = reqL.mask == 0;
    Bool empR = reqR.mask == 0;

    (* fire_when_enabled *)
    rule get_result_both(l.notEmpty && r.notEmpty);
      if (epochL == epochR) begin // update epoch
        epoch <= epochL;
        case (tuple2(empL, empR)) matches
          {False, False}: begin
            let dir = comp(reqL.req, reqR.req);
            let sel = case (dir) LT: selL; GT: selR; EQ: selB; endcase;
            out.enq(sel);
            if (dir != GT) l.deq;
            if (dir != LT) r.deq;
          end
          {False, True}: begin out.enq(selL); l.deq; r.deq; end
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
      if (epoch == epochL) begin
        out.enq(selL);
        l.deq;
      end // else, wait until the right subtree catches up
    endrule

    (* fire_when_enabled *)
    rule get_result_right(!l.notEmpty && r.notEmpty);
      if (epoch == epochR) begin
        out.enq(selR);
        r.deq;
      end // else, wait until the left subtree catches up
    endrule

    method ActionValue#(Bool) enq(Vector#(n, Maybe#(t)) v);
      let eL <- l.enq(take(v));
      let eR <- r.enq(takeTail(v));
      return eL;
    endmethod

    method notEmpty = out.notEmpty;

    method deq = out.deq; // must be called under if (notEmpty)

    method first = out.first;
  endmodule
endinstance

// guard deq and first only at the interface
module mkCoalTree#(function Ordering comp (t x, t y)) (CoalTree#(n, t))
  provisos (Coalescer#(n, t));
  (* hide *)
  CoalTree#(n, t) inner <- mkCoalTree_(comp);
  method enq = inner.enq;
  method notEmpty = inner.notEmpty;
  method deq if (inner.notEmpty) = inner.deq;
  method first if (inner.notEmpty) = inner.first;
endmodule

