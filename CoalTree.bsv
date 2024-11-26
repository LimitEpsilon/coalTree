// Adapted from https://github.com/mtikekar/advanced_bsv
import Vector::*;

// coalesced request
typedef struct {
  Vector#(n, Bool) mask;
  t req;
} CoalReq#(numeric type n, type t) deriving (Bits, Eq, FShow);

typedef
  Tuple2#(Maybe#(CoalReq#(n, t)), Bool)
  EpochReq#(numeric type n, type t);

interface EpochFifo#(numeric type n, type t);
  method Action enq(EpochReq#(n, t) x);
  method Bool notEmpty;
  method Action deq;
  method EpochReq#(n, t) first;
endinterface

// Pipeline FIFO
module mkEpochFifo(EpochFifo#(n, t)) provisos (Bits#(t, tSz));
  Reg#(EpochReq#(n, t)) data <- mkReg(tuple2(tagged Invalid, True));
  Reg#(Bool) empty[2] <- mkCReg(2, True);
  Reg#(Bool) full[2] <- mkCReg(2, False);

  method Action enq(x) if (!full[1]);
    data <= x;
    empty[1] <= False;
    full[1] <= True;
  endmethod

  method Bool notEmpty = !empty[0];

  method Action deq if (!empty[0]);
    // Tell later stages a dequeue was requested
    full[0] <= False;
    empty[0] <= True;
  endmethod

  method EpochReq#(n, t) first if (!empty[0]);
    return data;
  endmethod
endmodule

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
    EpochFifo#(1, t) in <- mkEpochFifo;
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

    method Bool notEmpty = in.notEmpty;

    method Action deq = in.deq;

    method EpochReq#(1, t) first = in.first;
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
    EpochFifo#(n, t) out <- mkEpochFifo;
    Reg#(Bool) epoch <- mkReg(False);

    (* fire_when_enabled *)
    rule get_result;
      let res1 = g1.notEmpty ? g1.first : ?;
      let res2 = g2.notEmpty ? g2.first : ?;

      let req1 = fromMaybe(?, tpl_1(res1));
      let req2 = fromMaybe(?, tpl_1(res2));

      let select = compare(pack(req1.req), pack(req2.req));

      let req1Valid = isValid(tpl_1(res1));
      let req2Valid = isValid(tpl_1(res2));

      let epoch1 = tpl_2(res1);
      let epoch2 = tpl_2(res2);

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

      if (g1.notEmpty) begin
        if (g2.notEmpty) begin
          if (epoch1 == epoch2) begin
            epoch <= epoch1;
            if (req1Valid) begin
              if (req2Valid) begin // (Val, Val)
                case (select)
                  LT: begin out.enq(selL); g1.deq; end
                  GT: begin out.enq(selR); g2.deq; end
                  EQ: begin out.enq(selB); g1.deq; g2.deq; end
                endcase
              end else begin // (Val, Inval)
                out.enq(selL); g1.deq; g2.deq;
              end
            end else begin // (Inval, ?)
              out.enq(selR); g1.deq; g2.deq;
            end
          end else begin
            if (epoch1 == epoch) begin
              out.enq(selL); g1.deq;
            end else begin // epoch2 == epoch
              out.enq(selR); g2.deq;
            end
          end
        end else begin
          epoch <= epoch1;
          out.enq(selL); g1.deq;
        end
      end else begin
        if (g2.notEmpty) begin
          epoch <= epoch2;
          out.enq(selR); g2.deq;
        end
      end
    endrule

    method Action enq(v);
      g1.enq(take(v));
      g2.enq(takeTail(v));
    endmethod

    method Bool notEmpty = out.notEmpty;

    method Action deq = out.deq;

    method EpochReq#(n, t) first = out.first;
  endmodule
endinstance

