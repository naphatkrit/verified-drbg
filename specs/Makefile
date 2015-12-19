SHAPATH=~/VST/sha
LIBROOT=~
COQC=coqc -I $(LIBROOT)/VST -R $(LIBROOT)/compcert -as compcert

all: verifications

clean:
	rm -f *.vo
	rm -f *.glob

shafiles:
	(cd sha && rm -f *.vo && for i in $(SHAPATH)/*.vo; do ln -s $$i; done)

tests: HMAC256_DRBG_tests_pr_false.vo HMAC256_DRBG_tests_pr_true.vo HMAC256_DRBG_tests_no_reseed.vo

verifications: verif_hmac_drbg_update.vo verif_mocked_md.vo verif_hmac_drbg_reseed.vo

%.vo : %.v
	$(COQC) $<

entropy_lemmas.vo: entropy.vo

verif_mocked_md.vo: hmac_drbg.vo spec_hmac_drbg.vo

verif_hmac_drbg_update.vo: spec_hmac_drbg.vo hmac_drbg.vo HMAC_DRBG_algorithms.vo

verif_hmac_drbg_reseed.vo: spec_hmac_drbg.vo hmac_drbg.vo DRBG_functions.vo HMAC_DRBG_algorithms.vo spec_hmac_drbg_pure_lemmas.vo entropy.vo entropy_lemmas.vo

verif_hmac_drbg_generate.vo: spec_hmac_drbg.vo hmac_drbg.vo DRBG_functions.vo HMAC_DRBG_pure_lemmas.vo HMAC_DRBG_algorithms.vo spec_hmac_drbg_pure_lemmas.vo entropy.vo entropy_lemmas.vo

hmac_drbg_compspecs.vo: hmac_drbg.vo

spec_hmac_drbg.vo: hmac_drbg.vo HMAC256_DRBG_functional_prog.vo hmac_drbg_compspecs.vo entropy.vo DRBG_functions.vo HMAC_DRBG_algorithms.vo

spec_hmac_drbg_pure_lemmas.vo: hmac_drbg.vo HMAC256_DRBG_functional_prog.vo hmac_drbg_compspecs.vo entropy.vo DRBG_functions.vo HMAC_DRBG_algorithms.vo spec_hmac_drbg.vo

DRBG_functions.vo: entropy.vo

HMAC_DRBG_algorithms.vo: DRBG_functions.vo

HMAC_DRBG_pure_lemmas.vo: DRBG_functions.vo HMAC_DRBG_algorithms.vo

HMAC256_DRBG_functional_prog.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo

HMAC256_DRBG_tests_no_reseed.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo entropy.vo

HMAC256_DRBG_tests_pr_false.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo entropy.vo

HMAC256_DRBG_tests_pr_true.vo: HMAC_DRBG_algorithms.vo DRBG_functions.vo entropy.vo
