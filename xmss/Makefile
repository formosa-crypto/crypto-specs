EASYCRYPT = easycrypt
EC_PARAMS = -I ../common

.PHONY: clean typecheck

typecheck:
	 $(EASYCRYPT) $(EC_PARAMS) Notation.ec
	 $(EASYCRYPT) $(EC_PARAMS) Primitives.ec

clean:
	-rm *.eco
