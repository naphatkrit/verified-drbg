SHAPATH=~/VST/sha
LIBROOT=~
COQC=coqc -I $(LIBROOT)/VST -R $(LIBROOT)/compcert -as compcert
VOFILES=DRBG_functions.vo HMAC_DRBG_algorithms.vo HMAC_DRBG_general_lemmas.vo HMAC256_DRBG_functional_prog.vo HMAC256_DRBG_tests_no_reseed.vo HMAC256_DRBG_tests_pr_false.vo HMAC256_DRBG_tests_pr_true.vo hmac_drbg.vo spec_hmac_drbg.vo verif_hmac_drbg_update.vo verif_hmac_drbg_reseed.vo verif_mocked_md.vo hmac_drbg_compspecs.vo entropy.vo
GLOBFILES=$(VOFILES:.vo=.glob)

all: verifications

clean:
	rm -f $(VOFILES)
	rm -f $(GLOBFILES)

shafiles:
	(cd sha && rm -f *.vo && for i in $(SHAPATH)/*.vo; do ln -s $$i; done)

tests: HMAC256_DRBG_tests_pr_false.vo HMAC256_DRBG_tests_pr_true.vo HMAC256_DRBG_tests_no_reseed.vo

verifications: verif_hmac_drbg_update.vo verif_mocked_md.vo verif_hmac_drbg_reseed.vo

%.vo : %.v
	$(COQC) $<

verif_mocked_md.vo: hmac_drbg.vo spec_hmac_drbg.vo

verif_hmac_drbg_update.vo: spec_hmac_drbg.vo hmac_drbg.vo HMAC_DRBG_update.vo

verif_hmac_drbg_reseed.vo: spec_hmac_drbg.vo hmac_drbg.vo

hmac_drbg_compspecs.vo: hmac_drbg.vo

spec_hmac_drbg.vo: hmac_drbg.vo HMAC256_DRBG_functional_prog.vo hmac_drbg_compspecs.vo entropy.vo DRBG_reseed_function.vo DRBG_state_handle.vo

DRBG_functions.vo: entropy.vo

HMAC_DRBG_algorithms.vo: DRBG_functions.vo

HMAC_DRBG_general_lemmas.vo: DRBG_functions.vo HMAC_DRBG_algorithms.vo

HMAC256_DRBG_functional_prog.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo

HMAC256_DRBG_tests_no_reseed.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo entropy.vo

HMAC256_DRBG_tests_pr_false.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo entropy.vo

HMAC256_DRBG_tests_pr_true.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo entropy.vo
