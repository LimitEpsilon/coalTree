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
  module mkCoalTree(CoalTree#(n, t));
endtypeclass

instance Coalescer#(1, t) provisos (Bits#(t, tSz));
  // Base instance of 1-long vector
  module mkCoalTree(CoalTree#(1, t));
    FIFOF#(EpochReq#(1, t)) in <- mkFIFOF;
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

    method deq = in.deq;

    method first = in.first;
  endmodule
endinstance

instance Coalescer#(n, t) provisos (
  Div#(n, 2, hn), Add#(hn, hm, n),
  Coalescer#(hn, t), Coalescer#(hm, t),
  Bits#(t, tSz)
);

  // General case
  module mkCoalTree(CoalTree#(n, t));
    // two subtrees
    CoalTree#(hn, t) g1 <- mkCoalTree;
    CoalTree#(hm, t) g2 <- mkCoalTree;
    FIFOF#(EpochReq#(n, t)) out <- mkFIFOF;
    Reg#(Bool) epoch <- mkReg(False);

    (* fire_when_enabled *)
    rule get_result;
      match {.res1, .epoch1} = g1.notEmpty ? g1.first : ?;
      match {.res2, .epoch2} = g2.notEmpty ? g2.first : ?;

      let req1 = fromMaybe(?, res1);
      let req2 = fromMaybe(?, res2);

      let select = compare(pack(req1.req), pack(req2.req));

      let req1Valid = isValid(res1);
      let req2Valid = isValid(res2);

      EpochReq#(n, t) selL = tuple2(
        req1Valid ?
        tagged Valid (CoalReq {
          mask: append(req1.mask, replicate(False)),
          req: req1.req
        }) : tagged Invalid, epoch1); // select left
      EpochReq#(n, t) selR = tuple2(
        req2Valid ?
        tagged Valid (CoalReq {
          mask: append(replicate(False), req2.mask),
          req: req2.req
        }) : tagged Invalid, epoch2); // select right
      EpochReq#(n, t) selB = tuple2(
        tagged Valid (CoalReq {
          mask: append(req1.mask, req2.mask),
          req: req1.req
        }), epoch1); // select both

      case (tuple2(g1.notEmpty, g2.notEmpty)) matches
        {True, True}:
          if (epoch1 == epoch2) begin
            epoch <= epoch1;
            case (tuple2(req1Valid, req2Valid)) matches
              {True, True}:
                case (select)
                  LT: begin out.enq(selL); g1.deq; end
                  GT: begin out.enq(selR); g2.deq; end
                  EQ: begin out.enq(selB); g1.deq; g2.deq; end
                endcase
              {True, False}: begin out.enq(selL); g1.deq; g2.deq; end
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

    method deq = out.deq;

    method first = out.first;
  endmodule
endinstance

