import Vector::*;
import FIFOF::*;
import RegFile::*;
import Randomizable::*;

import Memory::*;
import GetPut::*;
import ClientServer::*;

import CoalTree::*;
import VectorMem::*;

typedef 1 MemHeight; // h
typedef 512 PhysDataSz; // w8 = 8 * 2ʷ
typedef TLog#(TDiv#(PhysDataSz, 8)) MemWidth;
typedef TAdd#(MemHeight, MemWidth) PhysAddrSz;

typedef 4 ThreadNum;
typedef 32 DataSz;

function Bit#(dataW) fv_new_data
  (Bit#(dataW) old_data, Bit#(dataW) new_data, Bit #(bitW) strb)
  provisos (Mul#(8, bitW, dataW));

  function Bit#(8) f (Integer j) = strb [j] == 1'b1 ? 'hFF : 'h00;

  Vector#(bitW, Bit#(8)) v_mask = genWith(f);
  Bit#(dataW) mask = pack(v_mask);

  return ((old_data & (~ mask)) | (new_data & mask));
endfunction

(* synthesize *)
module mkDMemory(MemoryServer#(MemHeight, PhysDataSz));
	RegFile#(Bit#(MemHeight), Bit#(PhysDataSz)) mem <- mkRegFileFullLoad("dmem.vmh");
	FIFOF#(Bit#(PhysDataSz)) responses <- mkLFIFOF;

  interface Put request;
    method Action put(MemoryRequest#(MemHeight, PhysDataSz) req);
      match MemoryRequest {write: .write, byteen: .byteen, address: .address, data: .data} = req;
      let old_data = mem.sub(address);
      let new_data = fv_new_data(old_data, data, write ? byteen : 0);
      mem.upd(address, new_data);

      if (!write) responses.enq(new_data);
    endmethod
  endinterface

  interface Get response;
    method ActionValue#(MemoryResponse#(PhysDataSz)) get;
      let v <- toGet(responses).get;
      return MemoryResponse {data: v};
    endmethod
  endinterface
endmodule

typedef VecMemoryRequest#(n, PhysAddrSz, TDiv#(DataSz, 8)) MemReq#(numeric type n);
typedef VecMemoryResponse#(n, TDiv#(DataSz, 8)) MemResp#(numeric type n);

interface VectorDMemory#(numeric type n);
  interface Put#(MemReq#(n)) request;
  interface Get#(MemResp#(n)) response;
endinterface

(* synthesize *)
module mkVectorDMemory(VectorDMemory#(ThreadNum));
  let m <- mkDMemory;
  VecMemoryServer#(ThreadNum, PhysAddrSz, TDiv#(DataSz, 8)) s <- mkVecMemoryServer(
    interface MemoryServer;
      interface request = m.request;
      interface response = m.response;
    endinterface
  );

  interface request = s.request;
  interface response = s.response;
endmodule

(* synthesize *)
module mkTopMem(Empty);
  let m <- mkVectorDMemory;
  Randomize#(Bit#(ThreadNum)) randomMask <- mkGenericRandomizer;
  Randomize#(Bit#(TDiv#(DataSz, 8))) randomByteen <- mkGenericRandomizer;
  Randomize#(Vector#(ThreadNum, Bit#(MemWidth))) randomOffset <- mkGenericRandomizer;
  Reg#(Vector#(ThreadNum, Bit#(MemWidth))) lastOffset <- mkReg(unpack(0));
  Randomize#(Vector#(ThreadNum, Bit#(DataSz))) randomData <- mkGenericRandomizer;
  Reg#(Bool) written <- mkReg(False);

  Reg#(UInt#(32)) count <- mkReg(1);
  Reg#(UInt#(32)) cycle <- mkReg(0);
  UInt#(32) threshold = 32;

  (* fire_when_enabled *)
  (* execution_order = "put, increment" *)
  (* execution_order = "test, increment" *)
  rule increment;
    if (cycle == 0) begin
      randomMask.cntrl.init;
      randomByteen.cntrl.init;
      randomOffset.cntrl.init;
      randomData.cntrl.init;
    end
    $display("Cycle: %d over --------------------------------------------------", cycle);
    cycle <= cycle + 1;
  endrule

  (* fire_when_enabled *)
  rule put;
    if (written) begin
      MemReq#(ThreadNum) req = VecMemoryRequest {
        write: False,
        addresses: map(zeroExtend, lastOffset),
        datas: unpack(0),
        byteen: pack(replicate(True)),
        mask: pack(replicate(True))
      };

      m.request.put(req);
      written <= False;
    end else begin
      let offsets <- randomOffset.next;
      let datas <- randomData.next;
      let byteen <- randomByteen.next;
      let mask <- randomMask.next;

      MemReq#(ThreadNum) req = VecMemoryRequest {
        write: True,
        addresses: map(zeroExtend, offsets),
        datas: datas,
        byteen: byteen,
        mask: mask
      };

      if (mask != 0) begin
        $display(
          fshow("Write: offsets: ") + fshow(offsets) +
          fshow(", datas: ") + fshow(datas) +
          $format(", byteen: %0b, mask: %0b", byteen, mask)
        );
        m.request.put(req);
        lastOffset <= offsets;
        written <= True;
      end
    end
  endrule

  (* fire_when_enabled *)
  rule test;
    let mRes <- m.response.get;
    $display(fshow("Read: ") + fshow(mRes));
    if (count == threshold) $finish;
    count <= count + 1;
  endrule
endmodule
