BSC_FLAGS=-sim -aggressive-conditions -keep-fires -show-schedule

compile:
	mkdir -p buildDir
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) TestCoal.bsv
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) TestMerge.bsv
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) TestMem.bsv

test: compile
	bsc -e mkTopCoal -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTestCoal
	bsc -e mkTopMerge -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTestMerge
	bsc -e mkTopMem -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTestMem

all: test

clean:
	rm -rf buildDir sim*

.PHONY: clean all add compile
.DEFAULT_GOAL := all
