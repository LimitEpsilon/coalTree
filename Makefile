BSC_FLAGS=-verilog -aggressive-conditions -keep-fires -show-schedule

compile:
	mkdir -p buildDir
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) TestCoal.bsv
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) TestMem.bsv
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) TestStack.bsv

test: compile
	bsc -e mkTopCoal -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTestCoal
	bsc -e mkTopMem -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTestMem
	bsc -e mkTopStack -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTestStack

all: test

clean:
	rm -rf buildDir sim*

.PHONY: clean all add compile
.DEFAULT_GOAL := all
