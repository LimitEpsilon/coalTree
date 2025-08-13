import FIFO::*;

typedef 17 MulWidth;
typedef TMul#(2, MulWidth) AddWidth;

interface UnsafeMAdd;
  (* always_ready *)
  method Action enq(UInt#(MulWidth) a, UInt#(MulWidth) b, UInt#(AddWidth) c, Bool sub);
  (* always_ready *)
  method UInt#(TAdd#(1, AddWidth)) first;
endinterface

// fixed latency of two cycles
(* synthesize *)
module mkUnsafeMAdd (UnsafeMAdd);
  Reg#(UInt#(MulWidth)) a_r <- mkReg(0);
  Reg#(UInt#(MulWidth)) b_r <- mkReg(0);
  Reg#(UInt#(AddWidth)) c_r <- mkReg(0);
  Reg#(UInt#(TAdd#(1, AddWidth))) p_r <- mkReg(0);

  method Action enq(UInt#(MulWidth) a, UInt#(MulWidth) b, UInt#(AddWidth) c, Bool sub);
    a_r <= a;
    b_r <= b;
    c_r <= c;
    UInt#(TAdd#(1, AddWidth)) p = extend(unsignedMul(a_r, b_r));
    p_r <= sub ? p - extend(c_r) : p + extend(c_r);
  endmethod

  method first = p_r;
endmodule

typedef struct {
  UInt#(MulWidth) a;
  UInt#(MulWidth) b;
  UInt#(AddWidth) c;
  Bool sub;
} MAddReq deriving (Bits, Eq, FShow);

interface MAdd;
  method Action enq(UInt#(MulWidth) a, UInt#(MulWidth) b, UInt#(AddWidth) c, Bool sub);
  method UInt#(TAdd#(1, AddWidth)) first; // unguarded
  method Action deq;
endinterface

(* synthesize *)
module mkMAdd (MAdd);
  let m <- mkUnsafeMAdd;
  let computed <- mkReg(False);
  let latched <- mkReg(False);
  RWire#(void) deqReq <- mkRWire;
  RWire#(MAddReq) enqReq <- mkRWire;

  (* fire_when_enabled, no_implicit_conditions *)
  rule canonicalize;
    if (enqReq.wget matches tagged Valid .req) begin
      match MAddReq {a: .a, b: .b, c: .c, sub: .sub} = req;
      m.enq(a, b, c, sub);
      computed <= latched;
      latched <= True;
    end else if (isValid(deqReq.wget) || !computed) begin
      m.enq(?, ?, ?, ?);
      computed <= latched;
      latched <= False;
    end
  endrule

  method Action enq(UInt#(MulWidth) a, UInt#(MulWidth) b, UInt#(AddWidth) c, Bool sub) if (isValid(deqReq.wget) || !computed);
    enqReq.wset(MAddReq {a: a, b: b, c: c, sub: sub});
  endmethod

  method UInt#(TAdd#(1, AddWidth)) first = m.first;

  method Action deq if (computed);
    deqReq.wset(?);
  endmethod
endmodule

interface Mul32;
  method Action enq(Bool x_is_signed, Bit#(32) x, Bool y_is_signed, Bit#(32) y);
  method Bit#(64) first;
  method Action deq;
endinterface

module mkMul32 (Mul32);
  let mulUpper <- mkMAdd;
  let mulMiddle <- mkMAdd;
  let mulLower <- mkMAdd;
  FIFO#(Tuple2#(Bit#(32), Bit#(32))) uxy <- mkFIFO;
  FIFO#(Tuple2#(UInt#(MulWidth), UInt#(MulWidth))) middleArgs <- mkFIFO;
  FIFO#(Bit#(32)) upperRes <- mkSizedFIFO(3);
  FIFO#(Bit#(32)) lowerRes <- mkSizedFIFO(3);
  FIFO#(Bool) resNeg <- mkSizedFIFO(6);
  FIFO#(Bit#(64)) res <- mkFIFO;

  (* fire_when_enabled *)
  rule compute_middle;
    match {.ux, .uy} = uxy.first;
    UInt#(MulWidth) uxUpper = extend(unpack(ux[31:16]));
    UInt#(MulWidth) uxLower = extend(unpack(ux[15:0]));
    UInt#(MulWidth) uyUpper = extend(unpack(uy[31:16]));
    UInt#(MulWidth) uyLower = extend(unpack(uy[15:0]));
    middleArgs.enq(tuple2(uxUpper + uxLower, uyUpper + uyLower));
    uxy.deq;
  endrule

  (* fire_when_enabled *)
  rule multiply_middle;
    UInt#(AddWidth) upper = truncate(mulUpper.first);
    UInt#(AddWidth) lower = truncate(mulLower.first);
    match {.ux, .uy} = middleArgs.first;

    upperRes.enq(truncate(pack(upper)));
    mulMiddle.enq(ux, uy, upper + lower, True);
    lowerRes.enq(truncate(pack(lower)));

    mulUpper.deq;
    mulLower.deq;
    middleArgs.deq;
  endrule

  (* fire_when_enabled *)
  rule compute_end;
    let upper = upperRes.first;
    let middle = pack(mulMiddle.first);
    let lower = lowerRes.first;
    let neg = resNeg.first;

    Bit#(33) middle1 = truncate(middle) + extend(lower[31:16]);
    Bit#(32) upper1 = upper + extend(middle1[32:16]);
    Bit#(64) abs = {upper1, middle1[15:0], lower[15:0]};
    res.enq(neg ? -abs : abs);

    upperRes.deq;
    mulMiddle.deq;
    lowerRes.deq;
    resNeg.deq;
  endrule

  method Action enq(Bool x_is_signed, Bit#(32) x, Bool y_is_signed, Bit#(32) y);
    Bool xNeg = x_is_signed && unpack(msb(x));
    Bool yNeg = y_is_signed && unpack(msb(y));
    Bit#(32) ux = xNeg ? -x : x;
    UInt#(MulWidth) uxUpper = extend(unpack(ux[31:16]));
    UInt#(MulWidth) uxLower = extend(unpack(ux[15:0]));
    Bit#(32) uy = yNeg ? -y : y;
    UInt#(MulWidth) uyUpper = extend(unpack(uy[31:16]));
    UInt#(MulWidth) uyLower = extend(unpack(uy[15:0]));

    mulUpper.enq(uxUpper, uyUpper, 0, False);
    uxy.enq(tuple2(ux, uy));
    mulLower.enq(uxLower, uyLower, 0, False);
    resNeg.enq(xNeg != yNeg);
  endmethod

  method first = res.first;
  method Action deq; res.deq; endmethod
endmodule

