COQC=coqc -I ~/VST -R ~/compcert -as compcert
VOFILES=DRBG_generate_function.vo DRBG_instantiate_function.vo DRBG_state_handle.vo HMAC256_DRBG_functional_prog.vo HMAC_DRBG_generate_algorithm.vo HMAC_DRBG_instantiate_algorithm.vo HMAC_DRBG_generate.vo HMAC_DRBG_update.vo DRBG_working_state.vo DRBG_generate_algorithm_result.vo HMAC_DRBG_reseed_algorithm.vo DRBG_entropy_result.vo DRBG_reseed_function.vo HMAC256_DRBG_tests_no_reseed.vo HMAC256_DRBG_tests_pr_false.vo HMAC256_DRBG_tests_pr_true.vo hmac_drbg.vo spec_hmac_drbg.vo verif_hmac_drbg_update.vo verif_mocked_md.vo
GLOBFILES=$(VOFILES:.vo=.glob)

all: verifications

clean:
	rm -f $(VOFILES)
	rm -f $(GLOBFILES)

tests: HMAC256_DRBG_tests_pr_false.vo HMAC256_DRBG_tests_pr_true.vo HMAC256_DRBG_tests_no_reseed.vo

verifications: verif_hmac_drbg_update.vo verif_mocked_md.vo

%.vo : %.v
	$(COQC) $<

verif_mocked_md.vo: verif_mocked_md.v hmac_drbg.vo spec_hmac_drbg.vo
	$(COQC) verif_mocked_md.v

verif_hmac_drbg_update.vo: verif_hmac_drbg_update.v spec_hmac_drbg.vo hmac_drbg.vo
	$(COQC) verif_hmac_drbg_update.v

spec_hmac_drbg.vo: spec_hmac_drbg.v hmac_drbg.vo HMAC256_DRBG_functional_prog.vo
	$(COQC) spec_hmac_drbg.v

DRBG_reseed_function.vo: DRBG_reseed_function.v DRBG_state_handle.vo DRBG_working_state.vo DRBG_entropy_result.vo
	$(COQC) DRBG_reseed_function.v

HMAC_DRBG_reseed_algorithm.vo: HMAC_DRBG_reseed_algorithm.v DRBG_working_state.vo HMAC_DRBG_update.vo
	$(COQC) HMAC_DRBG_reseed_algorithm.v

DRBG_generate_function.vo: DRBG_generate_function.v DRBG_generate_algorithm_result.vo DRBG_working_state.vo DRBG_state_handle.vo DRBG_reseed_function.vo
	$(COQC) DRBG_generate_function.v

DRBG_generate_algorithm_result.vo: DRBG_generate_algorithm_result.v DRBG_working_state.vo
	$(COQC) DRBG_generate_algorithm_result.v

DRBG_state_handle.vo: DRBG_working_state.vo DRBG_state_handle.v
	$(COQC) DRBG_state_handle.v

DRBG_instantiate_function.vo: DRBG_instantiate_function.v DRBG_state_handle.vo DRBG_working_state.vo DRBG_entropy_result.vo
	$(COQC) DRBG_instantiate_function.v

HMAC256_DRBG_functional_prog.vo: HMAC256_DRBG_functional_prog.v DRBG_instantiate_function.vo HMAC_DRBG_instantiate_algorithm.vo DRBG_generate_function.vo HMAC_DRBG_generate_algorithm.vo DRBG_reseed_function.vo HMAC_DRBG_reseed_algorithm.vo HMAC_DRBG_update.vo
	$(COQC) HMAC256_DRBG_functional_prog.v

HMAC256_DRBG_tests_no_reseed.vo: HMAC256_DRBG_tests_no_reseed.v HMAC256_DRBG_functional_prog.vo DRBG_entropy_result.vo DRBG_state_handle.vo DRBG_generate_function.vo DRBG_instantiate_function.vo
	$(COQC) HMAC256_DRBG_tests_no_reseed.v

HMAC256_DRBG_tests_pr_false.vo: HMAC256_DRBG_tests_pr_false.v HMAC256_DRBG_functional_prog.vo DRBG_entropy_result.vo DRBG_state_handle.vo DRBG_generate_function.vo DRBG_instantiate_function.vo DRBG_reseed_function.vo
	$(COQC) HMAC256_DRBG_tests_pr_false.v

HMAC256_DRBG_tests_pr_true.vo: HMAC256_DRBG_tests_pr_true.v HMAC256_DRBG_functional_prog.vo DRBG_entropy_result.vo DRBG_state_handle.vo DRBG_generate_function.vo DRBG_instantiate_function.vo DRBG_reseed_function.vo
		$(COQC) HMAC256_DRBG_tests_pr_true.v

HMAC_DRBG_generate_algorithm.vo: HMAC_DRBG_generate_algorithm.v DRBG_working_state.vo DRBG_state_handle.vo DRBG_generate_algorithm_result.vo
	$(COQC) HMAC_DRBG_generate_algorithm.v

HMAC_DRBG_instantiate_algorithm.vo: HMAC_DRBG_instantiate_algorithm.v HMAC_DRBG_update.vo DRBG_working_state.vo
	$(COQC) HMAC_DRBG_instantiate_algorithm.v
