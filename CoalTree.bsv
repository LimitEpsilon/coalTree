// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector::*;

// coalesced request
typedef struct {
  Bit#(n) mask;
  t req;
} CoalReq#(numeric type n, type t) deriving (Bits, Eq);

instance FShow#(CoalReq#(n, t)) provisos (FShow#(t));
  function Fmt fshow(CoalReq#(n, t) x);
    return $format("{mask: %b, req: ", x.mask) + fshow(x.req) + fshow("}");
  endfunction
endinstance

interface CoalTree#(numeric type n, type t);
  method Action enq(Vector#(n, Maybe#(t)) v); // returns the epoch
  method Bool notEmpty;
  method Bool getEpoch;
  method Action deq;
  method CoalReq#(n, t) first;
endinterface

typeclass Coalescer#(numeric type n, type t);
  module mkCoalTree_#(function Ordering comp(t x, t y)) (CoalTree#(n, t));
endtypeclass

instance Coalescer#(1, t) provisos (Bits#(t, tSz), FShow#(t));
  // Base instance of 1-long vector
  module mkCoalTree_#(function Ordering comp(t x, t y)) (CoalTree#(1, t));
    Reg#(CoalReq#(1, t)) in <- mkReg(CoalReq {mask: 0, req: unpack(0)});
    Reg#(Bool) empty[2] <- mkCReg(2, True);
    Reg#(Bool) epoch <- mkReg(True);

    method Action enq(Vector#(1, Maybe#(t)) v) if (empty[1]);
      in <= CoalReq {mask: pack(isValid(v[0])), req: fromMaybe(?, v[0])};
      empty[1] <= False;
    endmethod

    method notEmpty = !empty[0];

    method getEpoch = epoch;

    method Action deq;
      empty[0] <= True;
      epoch <= !epoch;
    endmethod // must be called under if (notEmpty)

    method first = in;
  endmodule
endinstance

instance Coalescer#(n, t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Coalescer#(hn, t), Coalescer#(hm, t),
  Bits#(t, tSz), FShow#(t)
);

  // General case
  module mkCoalTree_#(function Ordering comp(t x, t y)) (CoalTree#(n, t));
    // two subtrees
    CoalTree#(hn, t) l <- mkCoalTree_(comp);
    CoalTree#(hm, t) r <- mkCoalTree_(comp);
    Reg#(CoalReq#(n, t)) out <- mkReg(CoalReq {mask: 0, req: unpack(0)});
    Reg#(Bool) empty[2] <- mkCReg(2, True);
    Reg#(Bool) epoch <- mkReg(False);

    let epochL = l.getEpoch;
    let epochR = r.getEpoch;
    let reqL = l.first;
    let reqR = r.first;

    CoalReq#(n, t) selL = CoalReq {
      mask: {0, reqL.mask},
      req: reqL.req
    }; // select left

    CoalReq#(n, t) selR = CoalReq {
      mask: {reqR.mask, 0},
      req: reqR.req
    }; // select right

    CoalReq#(n, t) selB = CoalReq {
      mask: {reqR.mask, reqL.mask},
      req: reqL.req
    }; // select both

    let dir = comp(reqL.req, reqR.req);
    let sel = case (dir) LT: selL; GT: selR; EQ: selB; endcase;

    (* fire_when_enabled *)
    rule get_result_both(l.notEmpty && r.notEmpty && empty[1]);
      // $display(fshow("get_result_both, ") + fshow(reqL) + fshow(reqR) + $format("epochL: %b, epochR: %b", epochL, epochR));
      if (epochL == epochR) begin // update epoch
        epoch <= epochL;
        if (reqL.mask != 0 && reqR.mask != 0) begin
          out <= sel;
          if (dir != GT) l.deq;
          if (dir != LT) r.deq;
        end else begin
          out <= selB; l.deq; r.deq;
        end
      end else if (epochL == epoch) begin // reqL cannot be empty
        out <= selL;
        l.deq;
      end else begin // epochR == epoch
        out <= selR;
        r.deq;
      end
      empty[1] <= False;
    endrule

    (* fire_when_enabled *)
    rule get_result_left(l.notEmpty && !r.notEmpty && empty[1] && epoch == epochL);
      // && epoch != epochR);
      // $display(fshow("get_result_left, ") + fshow(reqL) + $format("epochL: %b, epochR: %b", epochL, epochR));
      out <= selL;
      l.deq;
      empty[1] <= False;
      // else, wait until the right subtree catches up
    endrule

    (* fire_when_enabled *)
    rule get_result_right(!l.notEmpty && r.notEmpty && empty[1] && epoch == epochR);
      // && epoch != epochL);
      // $display(fshow("get_result_right, ") + fshow(reqR) + $format("epochL: %b, epochR: %b", epochL, epochR));
      out <= selR;
      r.deq;
      empty[1] <= False;
      // else, wait until the left subtree catches up
    endrule

    method Action enq(Vector#(n, Maybe#(t)) v);
      l.enq(take(v));
      r.enq(takeTail(v));
    endmethod

    method notEmpty = !empty[0];

    // method getEpoch = (empty[0] && epoch != epochL) ? epochR : epoch;
    method getEpoch = epoch;

    method Action deq; empty[0] <= True; endmethod // must be called under if (notEmpty)

    method first = out;
  endmodule
endinstance

// guard deq and first only at the interface
module mkCoalTree#(function Ordering comp (t x, t y)) (CoalTree#(n, t))
  provisos (Coalescer#(n, t));
  (* hide *)
  CoalTree#(n, t) inner <- mkCoalTree_(comp);
  method enq = inner.enq;
  method notEmpty = inner.notEmpty;
  method getEpoch = inner.getEpoch;
  method deq if (inner.notEmpty) = inner.deq;
  method first if (inner.notEmpty) = inner.first;
endmodule

