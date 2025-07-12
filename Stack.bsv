import Vector::*;

interface Stack#(numeric type n, type t);
  method Bool notFull;
  method Action push(t x);
  method Bool notEmpty;
  method Action pop;
  method t top;
  method Action clear;
endinterface

module mkStack#(Bool guardPush, Bool guardPop) (Stack#(n, t)) provisos (Bits#(t, tSz));
  // n is size of stack
  // t is data type of stack
  Vector#(n, Reg#(t))            data      <- replicateM(mkRegU);
  RWire#(void)                   popReq    <- mkRWire;
  RWire#(void)                   pushReq   <- mkRWire;
  RWire#(void)                   clearReq  <- mkRWire;
  Reg#(Bit#(TLog#(TAdd#(n, 1)))) size      <- mkReg(0);
  Bit#(TLog#(TAdd#(n, 1)))       max_index = fromInteger(valueOf(n));

  let pushSize = size + 1;
  let popSize = size - 1;

  Bool isEmpty = size == 0;
  Bool isFull = !isValid(popReq.wget) && size == max_index;

  (* fire_when_enabled, no_implicit_conditions *)
  rule canonicalize;
    if (isValid(clearReq.wget))
      size <= 0;
    else if (isValid(popReq.wget))
      size <= isValid(pushReq.wget) ? size : popSize;
    else if (isValid(pushReq.wget))
      size <= pushSize;
  endrule

  method Bool notFull = !isFull;

  method Action push(t x) if (!guardPush || !isFull);
    let size_ = isValid(popReq.wget) ? popSize : size;
    data[size_] <= x;
    pushReq.wset(?);
    for (Integer i = 0; i < valueOf(n); i = i + 1) begin
      if (fromInteger(i) < size_) $display("%0d: %x", i, pack(data[i]));
    end
    $display("pushed %x", pack(x));
  endmethod

  method Bool notEmpty = !isEmpty;

  method Action pop if (!guardPop || !isEmpty);
    $display("popped %x", pack(data[popSize]));
    popReq.wset(?);
  endmethod

  method t top if (!guardPop || !isEmpty);
    return data[popSize];
  endmethod

  method Action clear;
    clearReq.wset(?);
  endmethod
endmodule

