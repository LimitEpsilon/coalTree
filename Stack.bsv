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
  Reg#(Bit#(TLog#(TAdd#(n, 1)))) size[3]   <- mkCReg(3, 0);
  Bit#(TLog#(TAdd#(n, 1)))       max_index = fromInteger(valueOf(n));

  Bool isEmpty = size[0] == 0;
  Bool isFull = size[1] == max_index;

  method Bool notFull = !isFull;

  method Action push(t x) if (!guardPush || !isFull);
    for (Integer i = 0; i < valueOf(n); i = i + 1) begin
      if (fromInteger(i) < size[1]) $display("%0d: %x", i, pack(data[i]));
    end
    $display("pushed %x", pack(x));
    data[size[1]] <= x;
    size[1] <= size[1] + 1;
  endmethod

  method Bool notEmpty = !isEmpty;

  method Action pop if (!guardPop || !isEmpty);
    size[0] <= size[0] - 1;
  endmethod

  method t top if (!guardPop || !isEmpty);
    return data[size[0]];
  endmethod

  method Action clear;
    size[2] <= 0;
  endmethod
endmodule

