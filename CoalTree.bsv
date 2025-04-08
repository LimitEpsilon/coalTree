// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector::*;

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
    Reg#(CoalReq#(1, t)) in <- mkReg(CoalReq {mask: 0, req: unpack(0)});
    Reg#(Bool) empty[2] <- mkCReg(2, True);
    Reg#(Bool) epoch <- mkReg(False);

    method ActionValue#(Bool) enq(Vector#(1, Maybe#(t)) v) if (empty[1]);
      let req = CoalReq {mask: pack(isValid(v[0])), req: fromMaybe(?, v[0])};
      let e = !epoch;
      in <= req; empty[1] <= False;
      epoch <= e;
      return e;
    endmethod

    method notEmpty = !empty[0];

    method Action deq; empty[0] <= True; endmethod // must be called under if (notEmpty)

    method first = tuple2(in, epoch);
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
    Reg#(CoalReq#(n, t)) out <- mkReg(CoalReq {mask: 0, req: unpack(0)});
    Reg#(Bool) empty[2] <- mkCReg(2, True);
    Reg#(Bool) epoch <- mkReg(False);

    match {.reqL, .epochL} = l.first;
    match {.reqR, .epochR} = r.first;

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

    Bool empL = reqL.mask == 0;
    Bool empR = reqR.mask == 0;

    (* fire_when_enabled *)
    rule get_result_both(l.notEmpty && r.notEmpty && empty[1]);
      if (epochL == epochR) begin // update epoch
        epoch <= epochL;
        empty[1] <= False;
        case (tuple2(empL, empR)) matches
          {False, False}: begin
            let dir = comp(reqL.req, reqR.req);
            let sel = case (dir) LT: selL; GT: selR; EQ: selB; endcase;
            out <= sel;
            if (dir != GT) l.deq;
            if (dir != LT) r.deq;
          end
          {False, True}: begin out <= selL; l.deq; r.deq; end
          default: begin out <= selR; l.deq; r.deq; end
        endcase
      end else if (epochL == epoch) begin
        if (!empL) begin out <= selL; empty[1] <= False; end
        l.deq;
      end else begin // epochR == epoch
        if (!empR) begin out <= selR; empty[1] <= False; end
        r.deq;
      end
    endrule

    (* fire_when_enabled *)
    rule get_result_left(l.notEmpty && !r.notEmpty && empty[1]);
      if (epoch == epochL && !empL) begin
        out <= selL; empty[1] <= False;
        l.deq;
      end // else, wait until the right subtree catches up
    endrule

    (* fire_when_enabled *)
    rule get_result_right(!l.notEmpty && r.notEmpty && empty[1]);
      if (epoch == epochR && !empR) begin
        out <= selR; empty[1] <= False;
        r.deq;
      end // else, wait until the left subtree catches up
    endrule

    method ActionValue#(Bool) enq(Vector#(n, Maybe#(t)) v);
      let eL <- l.enq(take(v));
      let eR <- r.enq(takeTail(v));
      return eL;
    endmethod

    method notEmpty = !empty[0];

    method Action deq; empty[0] <= True; endmethod // must be called under if (notEmpty)

    method first = tuple2(out, epoch);
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

