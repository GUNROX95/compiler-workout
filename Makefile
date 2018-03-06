SHELL := /bin/bash

.PHONY: all regression

all:
	pushd src && make && popd

install: ;

regression:
	pushd regression && ./test.sh && popd

clean:
	pushd src && make clean && popd
	pushd regression && make clean && popd
	pushd regression && pushd expressions && make clean && popd
	pushd regression && pushd deep-expressions && make clean && popd && popd



