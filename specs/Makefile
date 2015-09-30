COQC=coqc -I ~/VST -R ~/compcert -as compcert
VOFILES=DRBG_generate_function.vo DRBG_instantiate_function.vo DRBG_state_handle.vo HMAC256_DRBG_functional_prog.vo HMAC_DRBG_generate_algorithm.vo HMAC_DRBG_instantiate_algorithm.vo HMAC_DRBG_generate.vo HMAC_DRBG_update.vo DRBG_working_state.vo DRBG_generate_algorithm_result.vo
GLOBFILES=$(VOFILES:.vo=.glob)

all: HMAC256_DRBG_functional_prog.vo

clean:
	rm -f $(VOFILES)
	rm -f $(GLOBFILES)

%.vo : %.v
	$(COQC) $<

DRBG_generate_function.vo: DRBG_generate_function.v DRBG_generate_algorithm_result.vo DRBG_working_state.vo DRBG_state_handle.vo
	$(COQC) DRBG_generate_function.v

DRBG_generate_algorithm_result.vo: DRBG_generate_algorithm_result.v DRBG_working_state.vo
	$(COQC) DRBG_generate_algorithm_result.v

DRBG_state_handle.vo: DRBG_working_state.vo DRBG_state_handle.v
	$(COQC) DRBG_state_handle.v

DRBG_instantiate_function.vo: DRBG_instantiate_function.v DRBG_state_handle.vo DRBG_working_state.vo
	$(COQC) DRBG_instantiate_function.v

HMAC256_DRBG_functional_prog.vo: HMAC256_DRBG_functional_prog.v DRBG_instantiate_function.vo HMAC_DRBG_instantiate_algorithm.vo DRBG_generate_function.vo HMAC_DRBG_generate_algorithm.vo
	$(COQC) HMAC256_DRBG_functional_prog.v

HMAC_DRBG_generate_algorithm.vo: HMAC_DRBG_generate_algorithm.v DRBG_working_state.vo DRBG_state_handle.vo DRBG_generate_algorithm_result.vo
	$(COQC) HMAC_DRBG_generate_algorithm.v

HMAC_DRBG_instantiate_algorithm.vo: HMAC_DRBG_instantiate_algorithm.v HMAC_DRBG_update.vo DRBG_working_state.vo
	$(COQC) HMAC_DRBG_instantiate_algorithm.v
