# Local Makefile for artifacts *in* HACS directory.

# HACS configuration.
HACS = $(abspath .)
include Makefile-hx

all:: Cookmain

# HACS Cook utility dependencies.
Cookmain.o: Cookmain.c Cook.h crsx.h
Cookmain: Cookmain.o Cook_sorts.o Cook_rules.o Cook_symbols.o crsx.o crsx_scan.o
#	$(CC) -o Cookmain Cookmain.o Cook_sorts.o Cook_rules.o Cook_symbols.o crsx.o crsx_scan.o -licuuc -licudata -licui18n -licuio
clean::; rm -f Cook_* Cook.*
realclean::; rm -fr Cookmain tmp

# HACS Cook1 utility dependencies.
Cook1main.o: Cook1main.c Cook1.h crsx.h
Cook1main: Cook1main.o Cook1_sorts.o Cook1_rules.o Cook1_symbols.o crsx.o crsx_scan.o
#	$(CC) -o Cookmain Cookmain.o Cook_sorts.o Cook_rules.o Cook_symbols.o crsx.o crsx_scan.o -licuuc -licudata -licui18n -licuio
clean::; rm -f Cook1_* Cook1.*
realclean::; rm -fr Cook1main tmp
