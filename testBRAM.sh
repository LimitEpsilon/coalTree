#!/bin/bash
./simTestBRAM >testBRAM.log && cat testBRAM.log | grep "PortA model" >modelA.log && cat testBRAM.log | grep "PortA response" >realA.log && cat testBRAM.log | grep "PortB model" >modelB.log && cat testBRAM.log | grep "PortB response" >realB.log && rm testBRAM.log
