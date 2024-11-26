BSC_FLAGS=-sim -aggressive-conditions -keep-fires -show-schedule

compile:
	mkdir -p buildDir
	bsc -u -bdir buildDir -info-dir buildDir -simdir buildDir -vdir buildDir $(BSC_FLAGS) Test.bsv

test: compile
	bsc -e mkTop -bdir buildDir -info-dir buildDir -simdir buildDir $(BSC_FLAGS) -o simTest

all: test

clean:
	rm -rf buildDir sim*

.PHONY: clean all add compile
.DEFAULT_GOAL := all
