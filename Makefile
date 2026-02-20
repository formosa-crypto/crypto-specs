# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF := config/tests.config 
JOBS   ?= 4
CHECKS ?= all

# --------------------------------------------------------------------
.PHONY: default check clean_eco

default: check

check:
	easycrypt runtest -report report.yaml -jobs $(JOBS) $(ECCONF) $(CHECKS)

clean_eco:
	find . -name '*.eco' -exec rm '{}' ';'
