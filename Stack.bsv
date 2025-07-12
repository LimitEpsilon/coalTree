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
  // n is size of stack, should be at least 1
  // t is data type of stack
  Vector#(n, Reg#(t))  data      <- replicateM(mkRegU);
  RWire#(void)         popReq    <- mkRWire;
  RWire#(void)         pushReq   <- mkRWire;
  RWire#(void)         clearReq  <- mkRWire;
  Reg#(Bool)           empty     <- mkReg(True);
  Reg#(Bool)           full      <- mkReg(False);
  Reg#(Bit#(TLog#(n))) size      <- mkReg(0); // points to the next empty slot
  Reg#(Bit#(TLog#(n))) popSize   <- mkReg(-1);
  Bit#(TLog#(n))       max_index = fromInteger(valueOf(n)-1);

  (* fire_when_enabled, no_implicit_conditions *)
  rule canonicalize;
    if (isValid(clearReq.wget)) begin
      empty <= True;
      full <= False;
      size <= 0;
      popSize <= -1;
    end else if (isValid(popReq.wget) && !isValid(pushReq.wget)) begin
      empty <= size == 1;
      full <= False;
      size <= popSize;
      popSize <= popSize - 1;
    end else if (!isValid(popReq.wget) && isValid(pushReq.wget)) begin
      empty <= False;
      full <= size == max_index;
      size <= size + 1;
      popSize <= popSize + 1;
    end
  endrule

  method Bool notFull = isValid(popReq.wget) || !full;

  method Action push(t x) if (!guardPush || isValid(popReq.wget) || !full);
    let topP = isValid(popReq.wget) ? popSize : size;
    data[topP] <= x;
    pushReq.wset(?);
    for (Integer i = 0; i < valueOf(n); i = i + 1) begin
      if (fromInteger(i) < topP) $display("%0d: %x", i, pack(data[i]));
    end
    $display("pushed %x", pack(x));
  endmethod

  method Bool notEmpty = !empty;

  method Action pop if (!guardPop || !empty);
    $display("popped %x", pack(data[popSize]));
    popReq.wset(?);
  endmethod

  method t top if (!guardPop || !empty);
    return data[popSize];
  endmethod

  method Action clear;
    clearReq.wset(?);
  endmethod
endmodule

