# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF := config/tests.config 
CHECKS ?= specs

# --------------------------------------------------------------------
.PHONY: default check clean_eco

default: check

check:
	easycrypt runtest $(ECCONF) $(CHECKS)

clean_eco:
	find kyber768 -name '*.eco' -exec rm '{}' ';'
