EASYCRYPT = easycrypt
EC_PARAMS = -I ../common -I ../../common -I ../../../common

.PHONY: clean typecheck

typecheck:
	 $(EASYCRYPT) $(EC_PARAMS) GFq.ec
	 $(EASYCRYPT) $(EC_PARAMS) Rq.ec
	 $(EASYCRYPT) $(EC_PARAMS) Symmetric.ec
	 $(EASYCRYPT) $(EC_PARAMS) Sampling.ec
	 $(EASYCRYPT) $(EC_PARAMS) VecMat.ec
	 $(EASYCRYPT) $(EC_PARAMS) Serialization.ec
	 $(EASYCRYPT) $(EC_PARAMS) InnerPKE.ec
	 $(EASYCRYPT) $(EC_PARAMS) Kyber.ec

clean:
	-rm *.eco
