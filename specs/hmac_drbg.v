Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _K : ident := 83%positive.
Definition _V : ident := 12%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_annot : ident := 187%positive.
Definition ___builtin_annot_intval : ident := 176%positive.
Definition ___builtin_bswap : ident := 193%positive.
Definition ___builtin_bswap16 : ident := 199%positive.
Definition ___builtin_bswap32 : ident := 177%positive.
Definition ___builtin_clz : ident := 212%positive.
Definition ___builtin_ctz : ident := 175%positive.
Definition ___builtin_fabs : ident := 190%positive.
Definition ___builtin_fmadd : ident := 174%positive.
Definition ___builtin_fmax : ident := 201%positive.
Definition ___builtin_fmin : ident := 164%positive.
Definition ___builtin_fmsub : ident := 202%positive.
Definition ___builtin_fnmadd : ident := 183%positive.
Definition ___builtin_fnmsub : ident := 188%positive.
Definition ___builtin_fsqrt : ident := 171%positive.
Definition ___builtin_membar : ident := 179%positive.
Definition ___builtin_memcpy_aligned : ident := 191%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_read16_reversed : ident := 166%positive.
Definition ___builtin_read32_reversed : ident := 172%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_va_arg : ident := 184%positive.
Definition ___builtin_va_copy : ident := 200%positive.
Definition ___builtin_va_end : ident := 203%positive.
Definition ___builtin_va_start : ident := 181%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___compcert_va_composite : ident := 165%positive.
Definition ___compcert_va_float64 : ident := 169%positive.
Definition ___compcert_va_int32 : ident := 196%positive.
Definition ___compcert_va_int64 : ident := 168%positive.
Definition ___i64_dtos : ident := 204%positive.
Definition ___i64_dtou : ident := 205%positive.
Definition ___i64_sar : ident := 185%positive.
Definition ___i64_sdiv : ident := 178%positive.
Definition ___i64_shl : ident := 162%positive.
Definition ___i64_shr : ident := 173%positive.
Definition ___i64_smod : ident := 167%positive.
Definition ___i64_stod : ident := 197%positive.
Definition ___i64_stof : ident := 198%positive.
Definition ___i64_udiv : ident := 186%positive.
Definition ___i64_umod : ident := 182%positive.
Definition ___i64_utod : ident := 209%positive.
Definition ___i64_utof : ident := 207%positive.
Definition ___stringlit_1 : ident := 118%positive.
Definition ___stringlit_2 : ident := 119%positive.
Definition ___stringlit_3 : ident := 120%positive.
Definition ___stringlit_4 : ident := 121%positive.
Definition ___stringlit_5 : ident := 122%positive.
Definition _add_len : ident := 79%positive.
Definition _additional : ident := 78%positive.
Definition _buf : ident := 213%positive.
Definition _ctx : ident := 170%positive.
Definition _custom : ident := 93%positive.
Definition _data : ident := 195%positive.
Definition _data_len : ident := 86%positive.
Definition _entropy_len : ident := 14%positive.
Definition _entropy_nopr : ident := 112%positive.
Definition _entropy_pr : ident := 110%positive.
Definition _f_entropy : ident := 17%positive.
Definition _hmac_ctx : ident := 10%positive.
Definition _hmac_drbg_self_test_entropy : ident := 116%positive.
Definition _interval : ident := 99%positive.
Definition _left : ident := 104%positive.
Definition _len : ident := 89%positive.
Definition _main : ident := 163%positive.
Definition _mbedtls_hmac_drbg_context : ident := 19%positive.
Definition _mbedtls_hmac_drbg_free : ident := 109%positive.
Definition _mbedtls_hmac_drbg_init : ident := 77%positive.
Definition _mbedtls_hmac_drbg_random : ident := 108%positive.
Definition _mbedtls_hmac_drbg_random_with_add : ident := 107%positive.
Definition _mbedtls_hmac_drbg_reseed : ident := 92%positive.
Definition _mbedtls_hmac_drbg_seed : ident := 95%positive.
Definition _mbedtls_hmac_drbg_seed_buf : ident := 88%positive.
Definition _mbedtls_hmac_drbg_self_test : ident := 123%positive.
Definition _mbedtls_hmac_drbg_set_entropy_len : ident := 98%positive.
Definition _mbedtls_hmac_drbg_set_prediction_resistance : ident := 97%positive.
Definition _mbedtls_hmac_drbg_set_reseed_interval : ident := 100%positive.
Definition _mbedtls_hmac_drbg_update : ident := 84%positive.
Definition _mbedtls_md_context_t : ident := 11%positive.
Definition _mbedtls_md_free : ident := 208%positive.
Definition _mbedtls_md_get_size : ident := 206%positive.
Definition _mbedtls_md_hmac_finish : ident := 192%positive.
Definition _mbedtls_md_hmac_reset : ident := 189%positive.
Definition _mbedtls_md_hmac_starts : ident := 194%positive.
Definition _mbedtls_md_hmac_update : ident := 211%positive.
Definition _mbedtls_md_info_from_type : ident := 180%positive.
Definition _mbedtls_md_info_t : ident := 7%positive.
Definition _mbedtls_md_setup : ident := 214%positive.
Definition _mbedtls_zeroize : ident := 75%positive.
Definition _md_ctx : ident := 9%positive.
Definition _md_info : ident := 8%positive.
Definition _md_len : ident := 80%positive.
Definition _md_size : ident := 94%positive.
Definition _memcmp : ident := 70%positive.
Definition _memcpy : ident := 68%positive.
Definition _memset : ident := 69%positive.
Definition _n : ident := 73%positive.
Definition _out : ident := 105%positive.
Definition _out_len : ident := 103%positive.
Definition _output : ident := 210%positive.
Definition _p : ident := 74%positive.
Definition _p_entropy : ident := 18%positive.
Definition _p_rng : ident := 101%positive.
Definition _prediction_resistance : ident := 15%positive.
Definition _printf : ident := 71%positive.
Definition _reseed_counter : ident := 13%positive.
Definition _reseed_interval : ident := 16%positive.
Definition _resistance : ident := 96%positive.
Definition _result_nopr : ident := 113%positive.
Definition _result_pr : ident := 111%positive.
Definition _ret : ident := 87%positive.
Definition _rounds : ident := 81%positive.
Definition _seed : ident := 90%positive.
Definition _seedlen : ident := 91%positive.
Definition _sep : ident := 82%positive.
Definition _test_offset : ident := 114%positive.
Definition _use_len : ident := 106%positive.
Definition _v : ident := 72%positive.
Definition _verbose : ident := 117%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_mbedtls_zeroize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr tvoid)) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tvolatile tuchar))) ::
               (126%positive, (tptr (tvolatile tuchar))) ::
               (125%positive, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Etempvar _v (tptr tvoid)))
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset 125%positive (Etempvar _n tuint))
          (Sset _n
            (Ebinop Osub (Etempvar 125%positive tuint)
              (Econst_int (Int.repr 1) tint) tuint)))
        (Sifthenelse (Etempvar 125%positive tuint) Sskip Sbreak))
      (Ssequence
        (Ssequence
          (Sset 126%positive (Etempvar _p (tptr (tvolatile tuchar))))
          (Sset _p
            (Ebinop Oadd (Etempvar 126%positive (tptr (tvolatile tuchar)))
              (Econst_int (Int.repr 1) tint) (tptr (tvolatile tuchar)))))
        (Sbuiltin None (EF_vstore Mint8unsigned)
          (Tcons (tptr (tvolatile tuchar)) (Tcons (tvolatile tuchar) Tnil))
          ((Eaddrof
             (Ederef (Etempvar 126%positive (tptr (tvolatile tuchar)))
               (tvolatile tuchar)) (tptr (tvolatile tuchar))) ::
           (Econst_int (Int.repr 0) tint) :: nil))))
    Sskip))
|}.

Definition f_mbedtls_hmac_drbg_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _mbedtls_hmac_drbg_context noattr) tuint) :: nil))
|}.

Definition f_mbedtls_hmac_drbg_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_additional, (tptr tuchar)) :: (_add_len, tuint) :: nil);
  fn_vars := ((_sep, (tarray tuchar 1)) :: (_K, (tarray tuchar 32)) :: nil);
  fn_temps := ((_md_len, tuint) :: (_rounds, tuchar) ::
               (129%positive, tint) :: (128%positive, tint) ::
               (127%positive, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some 127%positive)
      (Evar _mbedtls_md_get_size (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _mbedtls_md_info_t noattr))
                                     Tnil) tuchar cc_default))
      ((Efield
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
           (Tstruct _mbedtls_md_context_t noattr)) _md_info
         (tptr (Tstruct _mbedtls_md_info_t noattr))) :: nil))
    (Sset _md_len (Etempvar 127%positive tuchar)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _additional (tptr tuchar))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sset 128%positive
            (Ecast
              (Ebinop One (Etempvar _add_len tuint)
                (Econst_int (Int.repr 0) tint) tint) tbool))
          (Sset 128%positive (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar 128%positive tint)
          (Sset 129%positive (Ecast (Econst_int (Int.repr 2) tint) tint))
          (Sset 129%positive (Ecast (Econst_int (Int.repr 1) tint) tint))))
      (Sset _rounds (Ecast (Etempvar 129%positive tint) tuchar)))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _sep (tarray tuchar 1))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt
                         (Ederef
                           (Ebinop Oadd (Evar _sep (tarray tuchar 1))
                             (Econst_int (Int.repr 0) tint) (tptr tuchar))
                           tuchar) (Etempvar _rounds tuchar) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Scall None
              (Evar _mbedtls_md_hmac_reset (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _mbedtls_md_context_t noattr))
                                               Tnil) tint cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef
                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                     (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                   (Tstruct _mbedtls_md_context_t noattr))
                 (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _mbedtls_md_hmac_update (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                  (Tcons (tptr tuchar)
                                                    (Tcons tuint Tnil))) tint
                                                cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                     (Tstruct _mbedtls_md_context_t noattr))
                   (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                 (Efield
                   (Ederef
                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                     (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
                   (tarray tuchar 32)) :: (Etempvar _md_len tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _mbedtls_md_hmac_update (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                    (Tcons (tptr tuchar)
                                                      (Tcons tuint Tnil)))
                                                  tint cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                         (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                       (Tstruct _mbedtls_md_context_t noattr))
                     (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                   (Evar _sep (tarray tuchar 1)) ::
                   (Econst_int (Int.repr 1) tint) :: nil))
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _rounds tuchar)
                                 (Econst_int (Int.repr 2) tint) tint)
                    (Scall None
                      (Evar _mbedtls_md_hmac_update (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                        (Tcons (tptr tuchar)
                                                          (Tcons tuint Tnil)))
                                                      tint cc_default))
                      ((Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                           _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                         (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                       (Etempvar _additional (tptr tuchar)) ::
                       (Etempvar _add_len tuint) :: nil))
                    Sskip)
                  (Ssequence
                    (Scall None
                      (Evar _mbedtls_md_hmac_finish (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                        (Tcons (tptr tuchar)
                                                          Tnil)) tint
                                                      cc_default))
                      ((Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                           _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                         (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                       (Evar _K (tarray tuchar 32)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _mbedtls_md_hmac_starts (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                          (Tcons
                                                            (tptr tuchar)
                                                            (Tcons tuint
                                                              Tnil))) tint
                                                        cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                               (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                           (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                         (Evar _K (tarray tuchar 32)) ::
                         (Etempvar _md_len tuint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _mbedtls_md_hmac_update (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                            (Tcons
                                                              (tptr tuchar)
                                                              (Tcons tuint
                                                                Tnil))) tint
                                                          cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                 (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _md_ctx
                               (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                           (Efield
                             (Ederef
                               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                               (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _V (tarray tuchar 32)) ::
                           (Etempvar _md_len tuint) :: nil))
                        (Scall None
                          (Evar _mbedtls_md_hmac_finish (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                            (Tcons
                                                              (tptr tuchar)
                                                              Tnil)) tint
                                                          cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                 (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _md_ctx
                               (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                           (Efield
                             (Ederef
                               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                               (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _V (tarray tuchar 32)) :: nil))))))))))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _sep (tarray tuchar 1))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ebinop Oadd
            (Ederef
              (Ebinop Oadd (Evar _sep (tarray tuchar 1))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Econst_int (Int.repr 1) tint) tint))))))
|}.

Definition f_mbedtls_hmac_drbg_seed_buf := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_data, (tptr tuchar)) :: (_data_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) :: (133%positive, tuchar) ::
               (132%positive, tuchar) :: (131%positive, tint) ::
               (130%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some 130%positive)
          (Evar _mbedtls_md_setup (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _mbedtls_md_context_t noattr))
                                      (Tcons
                                        (tptr (Tstruct _mbedtls_md_info_t noattr))
                                        (Tcons tint Tnil))) tint cc_default))
          ((Eaddrof
             (Efield
               (Ederef
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
               (Tstruct _mbedtls_md_context_t noattr))
             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
           (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sset 131%positive (Etempvar 130%positive tint)))
      (Sset _ret (Etempvar 131%positive tint)))
    (Sifthenelse (Ebinop One (Ecast (Etempvar 131%positive tint) tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Etempvar _ret tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some 132%positive)
        (Evar _mbedtls_md_get_size (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _mbedtls_md_info_t noattr))
                                       Tnil) tuchar cc_default))
        ((Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
         nil))
      (Scall None
        (Evar _mbedtls_md_hmac_starts (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _mbedtls_md_context_t noattr))
                                          (Tcons (tptr tuchar)
                                            (Tcons tuint Tnil))) tint
                                        cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
             (Tstruct _mbedtls_md_context_t noattr))
           (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
           (tarray tuchar 32)) :: (Etempvar 132%positive tuchar) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some 133%positive)
          (Evar _mbedtls_md_get_size (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _mbedtls_md_info_t noattr))
                                         Tnil) tuchar cc_default))
          ((Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
           nil))
        (Scall None
          (Evar _memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                          cc_default))
          ((Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
             (tarray tuchar 32)) :: (Econst_int (Int.repr 1) tint) ::
           (Etempvar 133%positive tuchar) :: nil)))
      (Ssequence
        (Scall None
          (Evar _mbedtls_hmac_drbg_update (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                              (Tcons (tptr tuchar)
                                                (Tcons tuint Tnil))) tvoid
                                            cc_default))
          ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
           (Etempvar _data (tptr tuchar)) :: (Etempvar _data_len tuint) ::
           nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_mbedtls_hmac_drbg_reseed := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_additional, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := ((_seed, (tarray tuchar 384)) :: nil);
  fn_temps := ((_seedlen, tuint) :: (136%positive, tint) ::
               (135%positive, tint) :: (134%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _len tuint)
                   (Econst_int (Int.repr 256) tint) tint)
      (Sset 134%positive (Econst_int (Int.repr 1) tint))
      (Sset 134%positive
        (Ecast
          (Ebinop Ogt
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                  (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len
                tuint) (Etempvar _len tuint) tuint)
            (Econst_int (Int.repr 384) tint) tint) tbool)))
    (Sifthenelse (Etempvar 134%positive tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 5) tint) tint)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Evar _seed (tarray tuchar 384)) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 384) tint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some 135%positive)
          (Efield
            (Ederef
              (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
              (Tstruct _mbedtls_hmac_drbg_context noattr)) _f_entropy
            (tptr (Tfunction
                    (Tcons (tptr tvoid)
                      (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint
                    cc_default)))
          ((Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _p_entropy
             (tptr tvoid)) :: (Evar _seed (tarray tuchar 384)) ::
           (Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len
             tuint) :: nil))
        (Sifthenelse (Ebinop One (Etempvar 135%positive tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 9) tint) tint)))
          Sskip))
      (Ssequence
        (Sset _seedlen
          (Efield
            (Ederef
              (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
              (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len
            tuint))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop One (Etempvar _additional (tptr tuchar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sset 136%positive
                (Ecast
                  (Ebinop One (Etempvar _len tuint)
                    (Econst_int (Int.repr 0) tint) tint) tbool))
              (Sset 136%positive (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar 136%positive tint)
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Ebinop Oadd (Evar _seed (tarray tuchar 384))
                     (Etempvar _seedlen tuint) (tptr tuchar)) ::
                   (Etempvar _additional (tptr tuchar)) ::
                   (Etempvar _len tuint) :: nil))
                (Sset _seedlen
                  (Ebinop Oadd (Etempvar _seedlen tuint)
                    (Etempvar _len tuint) tuint)))
              Sskip))
          (Ssequence
            (Scall None
              (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                  (Tcons (tptr tuchar)
                                                    (Tcons tuint Tnil)))
                                                tvoid cc_default))
              ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (Evar _seed (tarray tuchar 384)) ::
               (Etempvar _seedlen tuint) :: nil))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr))
                  _reseed_counter tint) (Econst_int (Int.repr 1) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_mbedtls_hmac_drbg_seed := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_f_entropy,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint
                         cc_default))) :: (_p_entropy, (tptr tvoid)) ::
                (_custom, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) :: (_entropy_len, tuint) :: (_md_size, tuint) ::
               (143%positive, tint) :: (142%positive, tint) ::
               (141%positive, tint) :: (140%positive, tint) ::
               (139%positive, tuchar) :: (138%positive, tint) ::
               (137%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some 137%positive)
          (Evar _mbedtls_md_setup (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _mbedtls_md_context_t noattr))
                                      (Tcons
                                        (tptr (Tstruct _mbedtls_md_info_t noattr))
                                        (Tcons tint Tnil))) tint cc_default))
          ((Eaddrof
             (Efield
               (Ederef
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
               (Tstruct _mbedtls_md_context_t noattr))
             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
           (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sset 138%positive (Etempvar 137%positive tint)))
      (Sset _ret (Etempvar 138%positive tint)))
    (Sifthenelse (Ebinop One (Ecast (Etempvar 138%positive tint) tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Etempvar _ret tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some 139%positive)
        (Evar _mbedtls_md_get_size (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _mbedtls_md_info_t noattr))
                                       Tnil) tuchar cc_default))
        ((Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
         nil))
      (Sset _md_size (Etempvar 139%positive tuchar)))
    (Ssequence
      (Scall None
        (Evar _mbedtls_md_hmac_starts (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _mbedtls_md_context_t noattr))
                                          (Tcons (tptr tuchar)
                                            (Tcons tuint Tnil))) tint
                                        cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
             (Tstruct _mbedtls_md_context_t noattr))
           (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
           (tarray tuchar 32)) :: (Etempvar _md_size tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                          cc_default))
          ((Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
             (tarray tuchar 32)) :: (Econst_int (Int.repr 1) tint) ::
           (Etempvar _md_size tuint) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                (Tstruct _mbedtls_hmac_drbg_context noattr)) _f_entropy
              (tptr (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint
                      cc_default)))
            (Etempvar _f_entropy (tptr (Tfunction
                                         (Tcons (tptr tvoid)
                                           (Tcons (tptr tuchar)
                                             (Tcons tuint Tnil))) tint
                                         cc_default))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                  (Tstruct _mbedtls_hmac_drbg_context noattr)) _p_entropy
                (tptr tvoid)) (Etempvar _p_entropy (tptr tvoid)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr))
                  _reseed_interval tint) (Econst_int (Int.repr 10000) tint))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Ole (Etempvar _md_size tuint)
                                 (Econst_int (Int.repr 20) tint) tint)
                    (Sset 140%positive
                      (Ecast (Econst_int (Int.repr 16) tint) tint))
                    (Sifthenelse (Ebinop Ole (Etempvar _md_size tuint)
                                   (Econst_int (Int.repr 28) tint) tint)
                      (Ssequence
                        (Sset 141%positive
                          (Ecast (Econst_int (Int.repr 24) tint) tint))
                        (Sset 140%positive
                          (Ecast (Etempvar 141%positive tint) tint)))
                      (Ssequence
                        (Sset 141%positive
                          (Ecast (Econst_int (Int.repr 32) tint) tint))
                        (Sset 140%positive
                          (Ecast (Etempvar 141%positive tint) tint)))))
                  (Sset _entropy_len (Etempvar 140%positive tint)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                        (Tstruct _mbedtls_hmac_drbg_context noattr))
                      _entropy_len tuint)
                    (Ebinop Odiv
                      (Ebinop Omul (Etempvar _entropy_len tuint)
                        (Econst_int (Int.repr 3) tint) tuint)
                      (Econst_int (Int.repr 2) tint) tuint))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some 142%positive)
                            (Evar _mbedtls_hmac_drbg_reseed (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tint
                                                              cc_default))
                            ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                             (Etempvar _custom (tptr tuchar)) ::
                             (Etempvar _len tuint) :: nil))
                          (Sset 143%positive (Etempvar 142%positive tint)))
                        (Sset _ret (Etempvar 143%positive tint)))
                      (Sifthenelse (Ebinop One
                                     (Ecast (Etempvar 143%positive tint)
                                       tint) (Econst_int (Int.repr 0) tint)
                                     tint)
                        (Sreturn (Some (Etempvar _ret tint)))
                        Sskip))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                            (Tstruct _mbedtls_hmac_drbg_context noattr))
                          _entropy_len tuint) (Etempvar _entropy_len tuint))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
|}.

Definition f_mbedtls_hmac_drbg_set_prediction_resistance := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_resistance, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _prediction_resistance
    tint) (Etempvar _resistance tint))
|}.

Definition f_mbedtls_hmac_drbg_set_entropy_len := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len tuint)
  (Etempvar _len tuint))
|}.

Definition f_mbedtls_hmac_drbg_set_reseed_interval := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_interval, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_interval tint)
  (Etempvar _interval tint))
|}.

Definition f_mbedtls_hmac_drbg_random_with_add := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p_rng, (tptr tvoid)) :: (_output, (tptr tuchar)) ::
                (_out_len, tuint) :: (_additional, (tptr tuchar)) ::
                (_add_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) ::
               (_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (_md_len, tuint) :: (_left, tuint) :: (_out, (tptr tuchar)) ::
               (_use_len, tuint) :: (149%positive, tuint) ::
               (148%positive, tint) :: (147%positive, tint) ::
               (146%positive, tint) :: (145%positive, tint) ::
               (144%positive, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Ecast (Etempvar _p_rng (tptr tvoid))
      (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some 144%positive)
        (Evar _mbedtls_md_get_size (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _mbedtls_md_info_t noattr))
                                       Tnil) tuchar cc_default))
        ((Efield
           (Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
             (Tstruct _mbedtls_md_context_t noattr)) _md_info
           (tptr (Tstruct _mbedtls_md_info_t noattr))) :: nil))
      (Sset _md_len (Etempvar 144%positive tuchar)))
    (Ssequence
      (Sset _left (Etempvar _out_len tuint))
      (Ssequence
        (Sset _out (Etempvar _output (tptr tuchar)))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _out_len tuint)
                         (Econst_int (Int.repr 1024) tint) tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 3) tint) tint)))
            Sskip)
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _add_len tuint)
                           (Econst_int (Int.repr 256) tint) tint)
              (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 5) tint) tint)))
              Sskip)
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop One
                               (Efield
                                 (Ederef
                                   (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 _f_entropy
                                 (tptr (Tfunction
                                         (Tcons (tptr tvoid)
                                           (Tcons (tptr tuchar)
                                             (Tcons tuint Tnil))) tint
                                         cc_default)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sifthenelse (Ebinop Oeq
                                 (Efield
                                   (Ederef
                                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                     (Tstruct _mbedtls_hmac_drbg_context noattr))
                                   _prediction_resistance tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Sset 147%positive
                      (Ecast (Econst_int (Int.repr 1) tint) tbool))
                    (Ssequence
                      (Sset 147%positive
                        (Ecast
                          (Ebinop Ogt
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                (Tstruct _mbedtls_hmac_drbg_context noattr))
                              _reseed_counter tint)
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                (Tstruct _mbedtls_hmac_drbg_context noattr))
                              _reseed_interval tint) tint) tbool))
                      (Sset 147%positive
                        (Ecast (Etempvar 147%positive tint) tbool))))
                  (Sset 147%positive (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar 147%positive tint)
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some 145%positive)
                            (Evar _mbedtls_hmac_drbg_reseed (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tint
                                                              cc_default))
                            ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                             (Etempvar _additional (tptr tuchar)) ::
                             (Etempvar _add_len tuint) :: nil))
                          (Sset 146%positive (Etempvar 145%positive tint)))
                        (Sset _ret (Etempvar 146%positive tint)))
                      (Sifthenelse (Ebinop One
                                     (Ecast (Etempvar 146%positive tint)
                                       tint) (Econst_int (Int.repr 0) tint)
                                     tint)
                        (Sreturn (Some (Etempvar _ret tint)))
                        Sskip))
                    (Sset _add_len (Econst_int (Int.repr 0) tint)))
                  Sskip))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop One
                                 (Etempvar _additional (tptr tuchar))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Sset 148%positive
                      (Ecast
                        (Ebinop One (Etempvar _add_len tuint)
                          (Econst_int (Int.repr 0) tint) tint) tbool))
                    (Sset 148%positive (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar 148%positive tint)
                    (Scall None
                      (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                          (Tcons
                                                            (tptr tuchar)
                                                            (Tcons tuint
                                                              Tnil))) tvoid
                                                        cc_default))
                      ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                       (Etempvar _additional (tptr tuchar)) ::
                       (Etempvar _add_len tuint) :: nil))
                    Sskip))
                (Ssequence
                  (Swhile
                    (Ebinop One (Etempvar _left tuint)
                      (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Ogt (Etempvar _left tuint)
                                       (Etempvar _md_len tuint) tint)
                          (Sset 149%positive
                            (Ecast (Etempvar _md_len tuint) tuint))
                          (Sset 149%positive
                            (Ecast (Etempvar _left tuint) tuint)))
                        (Sset _use_len (Etempvar 149%positive tuint)))
                      (Ssequence
                        (Scall None
                          (Evar _mbedtls_md_hmac_reset (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                           Tnil) tint
                                                         cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                 (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _md_ctx
                               (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar _mbedtls_md_hmac_update (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                              (Tcons
                                                                (tptr tuchar)
                                                                (Tcons tuint
                                                                  Tnil)))
                                                            tint cc_default))
                            ((Eaddrof
                               (Efield
                                 (Ederef
                                   (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 _md_ctx
                                 (Tstruct _mbedtls_md_context_t noattr))
                               (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                             (Efield
                               (Ederef
                                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                 (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _V (tarray tuchar 32)) ::
                             (Etempvar _md_len tuint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_md_hmac_finish (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  Tnil)) tint
                                                              cc_default))
                              ((Eaddrof
                                 (Efield
                                   (Ederef
                                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                     (Tstruct _mbedtls_hmac_drbg_context noattr))
                                   _md_ctx
                                   (Tstruct _mbedtls_md_context_t noattr))
                                 (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 _V (tarray tuchar 32)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _memcpy (Tfunction
                                                (Tcons (tptr tvoid)
                                                  (Tcons (tptr tvoid)
                                                    (Tcons tuint Tnil)))
                                                (tptr tvoid) cc_default))
                                ((Etempvar _out (tptr tuchar)) ::
                                 (Efield
                                   (Ederef
                                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                     (Tstruct _mbedtls_hmac_drbg_context noattr))
                                   _V (tarray tuchar 32)) ::
                                 (Etempvar _use_len tuint) :: nil))
                              (Ssequence
                                (Sset _out
                                  (Ebinop Oadd (Etempvar _out (tptr tuchar))
                                    (Etempvar _use_len tuint) (tptr tuchar)))
                                (Sset _left
                                  (Ebinop Osub (Etempvar _left tuint)
                                    (Etempvar _use_len tuint) tuint)))))))))
                  (Ssequence
                    (Scall None
                      (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                          (Tcons
                                                            (tptr tuchar)
                                                            (Tcons tuint
                                                              Tnil))) tvoid
                                                        cc_default))
                      ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                       (Etempvar _additional (tptr tuchar)) ::
                       (Etempvar _add_len tuint) :: nil))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                            (Tstruct _mbedtls_hmac_drbg_context noattr))
                          _reseed_counter tint)
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                              (Tstruct _mbedtls_hmac_drbg_context noattr))
                            _reseed_counter tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
|}.

Definition f_mbedtls_hmac_drbg_random := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p_rng, (tptr tvoid)) :: (_output, (tptr tuchar)) ::
                (_out_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) ::
               (_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (150%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Ecast (Etempvar _p_rng (tptr tvoid))
      (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some 150%positive)
        (Evar _mbedtls_hmac_drbg_random_with_add (Tfunction
                                                   (Tcons (tptr tvoid)
                                                     (Tcons (tptr tuchar)
                                                       (Tcons tuint
                                                         (Tcons (tptr tuchar)
                                                           (Tcons tuint Tnil)))))
                                                   tint cc_default))
        ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
         (Etempvar _output (tptr tuchar)) :: (Etempvar _out_len tuint) ::
         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
         (Econst_int (Int.repr 0) tint) :: nil))
      (Sset _ret (Etempvar 150%positive tint)))
    (Sreturn (Some (Etempvar _ret tint)))))
|}.

Definition f_mbedtls_hmac_drbg_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Scall None
      (Evar _mbedtls_md_free (Tfunction
                               (Tcons
                                 (tptr (Tstruct _mbedtls_md_context_t noattr))
                                 Tnil) tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
           (Tstruct _mbedtls_md_context_t noattr))
         (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil))
    (Scall None
      (Evar _mbedtls_zeroize (Tfunction
                               (Tcons (tptr tvoid) (Tcons tuint Tnil)) tvoid
                               cc_default))
      ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
       (Esizeof (Tstruct _mbedtls_hmac_drbg_context noattr) tuint) :: nil))))
|}.

Definition v_entropy_pr := {|
  gvar_info := (tarray tuchar 56);
  gvar_init := (Init_int8 (Int.repr 160) :: Init_int8 (Int.repr 201) ::
                Init_int8 (Int.repr 171) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 241) :: Init_int8 (Int.repr 226) ::
                Init_int8 (Int.repr 229) :: Init_int8 (Int.repr 164) ::
                Init_int8 (Int.repr 222) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 189) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 247) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 156) :: Init_int8 (Int.repr 91) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 239) ::
                Init_int8 (Int.repr 216) :: Init_int8 (Int.repr 202) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 248) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 165) ::
                Init_int8 (Int.repr 132) :: Init_int8 (Int.repr 254) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 171) ::
                Init_int8 (Int.repr 90) :: Init_int8 (Int.repr 238) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 170) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 96) ::
                Init_int8 (Int.repr 153) :: Init_int8 (Int.repr 212) ::
                Init_int8 (Int.repr 94) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 151) :: Init_int8 (Int.repr 220) ::
                Init_int8 (Int.repr 64) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 134) :: Init_int8 (Int.repr 163) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 245) ::
                Init_int8 (Int.repr 89) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 228) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_result_pr := {|
  gvar_info := (tarray tuchar 80);
  gvar_init := (Init_int8 (Int.repr 154) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 162) :: Init_int8 (Int.repr 208) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 213) ::
                Init_int8 (Int.repr 155) :: Init_int8 (Int.repr 254) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 236) ::
                Init_int8 (Int.repr 177) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 155) :: Init_int8 (Int.repr 96) ::
                Init_int8 (Int.repr 129) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 209) :: Init_int8 (Int.repr 150) ::
                Init_int8 (Int.repr 157) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 30) :: Init_int8 (Int.repr 148) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 152) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 147) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 202) :: Init_int8 (Int.repr 184) ::
                Init_int8 (Int.repr 252) :: Init_int8 (Int.repr 204) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 192) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 164) :: Init_int8 (Int.repr 137) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 149) :: Init_int8 (Int.repr 94) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 198) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 127) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 43) ::
                Init_int8 (Int.repr 248) :: Init_int8 (Int.repr 163) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 171) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 92) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 166) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 136) :: Init_int8 (Int.repr 241) ::
                Init_int8 (Int.repr 167) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 238) :: Init_int8 (Int.repr 243) ::
                Init_int8 (Int.repr 225) :: Init_int8 (Int.repr 92) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 155) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 175) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 68) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_entropy_nopr := {|
  gvar_info := (tarray tuchar 40);
  gvar_init := (Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 155) :: Init_int8 (Int.repr 191) ::
                Init_int8 (Int.repr 124) :: Init_int8 (Int.repr 221) ::
                Init_int8 (Int.repr 165) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 149) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 134) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 201) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 131) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 200) ::
                Init_int8 (Int.repr 199) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 91) :: Init_int8 (Int.repr 91) ::
                Init_int8 (Int.repr 150) :: Init_int8 (Int.repr 196) ::
                Init_int8 (Int.repr 142) :: Init_int8 (Int.repr 155) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 227) ::
                Init_int8 (Int.repr 233) :: Init_int8 (Int.repr 157) ::
                Init_int8 (Int.repr 254) :: Init_int8 (Int.repr 223) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_result_nopr := {|
  gvar_info := (tarray tuchar 80);
  gvar_init := (Init_int8 (Int.repr 198) :: Init_int8 (Int.repr 161) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 184) ::
                Init_int8 (Int.repr 212) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 171) :: Init_int8 (Int.repr 127) ::
                Init_int8 (Int.repr 236) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 220) :: Init_int8 (Int.repr 169) ::
                Init_int8 (Int.repr 216) :: Init_int8 (Int.repr 202) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 156) :: Init_int8 (Int.repr 166) ::
                Init_int8 (Int.repr 172) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 198) :: Init_int8 (Int.repr 248) ::
                Init_int8 (Int.repr 162) :: Init_int8 (Int.repr 190) ::
                Init_int8 (Int.repr 34) :: Init_int8 (Int.repr 131) ::
                Init_int8 (Int.repr 74) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 177) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 148) :: Init_int8 (Int.repr 241) ::
                Init_int8 (Int.repr 193) :: Init_int8 (Int.repr 165) ::
                Init_int8 (Int.repr 207) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 34) :: Init_int8 (Int.repr 236) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 224) ::
                Init_int8 (Int.repr 150) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 212) :: Init_int8 (Int.repr 191) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 224) ::
                Init_int8 (Int.repr 135) :: Init_int8 (Int.repr 253) ::
                Init_int8 (Int.repr 181) :: Init_int8 (Int.repr 179) ::
                Init_int8 (Int.repr 233) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 147) ::
                Init_int8 (Int.repr 213) :: Init_int8 (Int.repr 187) ::
                Init_int8 (Int.repr 152) :: Init_int8 (Int.repr 250) ::
                Init_int8 (Int.repr 237) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 232) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 200) :: Init_int8 (Int.repr 164) ::
                Init_int8 (Int.repr 89) :: Init_int8 (Int.repr 183) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_test_offset := {|
  gvar_info := tuint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_hmac_drbg_self_test_entropy := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr tvoid)) :: (_buf, (tptr tuchar)) ::
                (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Etempvar _data (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                      cc_default))
      ((Etempvar _buf (tptr tuchar)) ::
       (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Evar _test_offset tuint)
         (tptr tuchar)) :: (Etempvar _len tuint) :: nil))
    (Ssequence
      (Sassign (Evar _test_offset tuint)
        (Ebinop Oadd (Evar _test_offset tuint) (Etempvar _len tuint) tuint))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_mbedtls_hmac_drbg_self_test := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_verbose, tint) :: nil);
  fn_vars := ((_ctx, (Tstruct _mbedtls_hmac_drbg_context noattr)) ::
              (_buf, (tarray tuchar 80)) :: nil);
  fn_temps := ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               (160%positive, tint) :: (159%positive, tint) ::
               (158%positive, tint) :: (157%positive, tint) ::
               (156%positive, tint) :: (155%positive, tint) ::
               (154%positive, tint) :: (153%positive, tint) ::
               (152%positive, tint) ::
               (151%positive, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some 151%positive)
      (Evar _mbedtls_md_info_from_type (Tfunction (Tcons tint Tnil)
                                         (tptr (Tstruct _mbedtls_md_info_t noattr))
                                         cc_default))
      ((Econst_int (Int.repr 4) tint) :: nil))
    (Sset _md_info
      (Etempvar 151%positive (tptr (Tstruct _mbedtls_md_info_t noattr)))))
  (Ssequence
    (Scall None
      (Evar _mbedtls_hmac_drbg_init (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                        Tnil) tvoid cc_default))
      ((Eaddrof (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
         (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) :: nil))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_1 (tarray tschar 27)) :: nil))
        Sskip)
      (Ssequence
        (Sassign (Evar _test_offset tuint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Scall (Some 152%positive)
              (Evar _mbedtls_hmac_drbg_seed (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                (Tcons
                                                  (tptr (Tstruct _mbedtls_md_info_t noattr))
                                                  (Tcons
                                                    (tptr (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              (Tcons
                                                                (tptr tuchar)
                                                                (Tcons tuint
                                                                  Tnil)))
                                                            tint cc_default))
                                                    (Tcons (tptr tvoid)
                                                      (Tcons (tptr tuchar)
                                                        (Tcons tuint Tnil))))))
                                              tint cc_default))
              ((Eaddrof
                 (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                 (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               (Evar _hmac_drbg_self_test_entropy (Tfunction
                                                    (Tcons (tptr tvoid)
                                                      (Tcons (tptr tuchar)
                                                        (Tcons tuint Tnil)))
                                                    tint cc_default)) ::
               (Ecast (Evar _entropy_pr (tarray tuchar 56)) (tptr tvoid)) ::
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sifthenelse (Ebinop One (Etempvar 152%positive tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_2 (tarray tschar 8)) :: nil))
                  Sskip)
                (Sreturn (Some (Econst_int (Int.repr 1) tint))))
              Sskip))
          (Ssequence
            (Scall None
              (Evar _mbedtls_hmac_drbg_set_prediction_resistance (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                   tvoid
                                                                   cc_default))
              ((Eaddrof
                 (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                 (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (Econst_int (Int.repr 1) tint) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some 153%positive)
                  (Evar _mbedtls_hmac_drbg_random (Tfunction
                                                    (Tcons (tptr tvoid)
                                                      (Tcons (tptr tuchar)
                                                        (Tcons tuint Tnil)))
                                                    tint cc_default))
                  ((Eaddrof
                     (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                     (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                   (Evar _buf (tarray tuchar 80)) ::
                   (Econst_int (Int.repr 80) tint) :: nil))
                (Sifthenelse (Ebinop One (Etempvar 153%positive tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_2 (tarray tschar 8)) :: nil))
                      Sskip)
                    (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                  Sskip))
              (Ssequence
                (Ssequence
                  (Scall (Some 154%positive)
                    (Evar _mbedtls_hmac_drbg_random (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        (Tcons (tptr tuchar)
                                                          (Tcons tuint Tnil)))
                                                      tint cc_default))
                    ((Eaddrof
                       (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                     (Evar _buf (tarray tuchar 80)) ::
                     (Econst_int (Int.repr 80) tint) :: nil))
                  (Sifthenelse (Ebinop One (Etempvar 154%positive tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Scall None
                          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                          tint
                                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                          ((Evar ___stringlit_2 (tarray tschar 8)) :: nil))
                        Sskip)
                      (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Scall (Some 155%positive)
                      (Evar _memcmp (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) tint
                                      cc_default))
                      ((Evar _buf (tarray tuchar 80)) ::
                       (Evar _result_pr (tarray tuchar 80)) ::
                       (Econst_int (Int.repr 80) tint) :: nil))
                    (Sifthenelse (Ebinop One (Etempvar 155%positive tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Scall None
                            (Evar _printf (Tfunction
                                            (Tcons (tptr tschar) Tnil) tint
                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                            ((Evar ___stringlit_2 (tarray tschar 8)) :: nil))
                          Sskip)
                        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                      Sskip))
                  (Ssequence
                    (Scall None
                      (Evar _mbedtls_hmac_drbg_free (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                        Tnil) tvoid
                                                      cc_default))
                      ((Eaddrof
                         (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                         (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar _mbedtls_hmac_drbg_free (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                          Tnil) tvoid
                                                        cc_default))
                        ((Eaddrof
                           (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                           (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                         nil))
                      (Ssequence
                        (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Scall None
                            (Evar _printf (Tfunction
                                            (Tcons (tptr tschar) Tnil) tint
                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                            ((Evar ___stringlit_3 (tarray tschar 8)) :: nil))
                          Sskip)
                        (Ssequence
                          (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Scall None
                              (Evar _printf (Tfunction
                                              (Tcons (tptr tschar) Tnil) tint
                                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                              ((Evar ___stringlit_4 (tarray tschar 28)) ::
                               nil))
                            Sskip)
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_hmac_drbg_init (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                Tnil) tvoid
                                                              cc_default))
                              ((Eaddrof
                                 (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                               nil))
                            (Ssequence
                              (Sassign (Evar _test_offset tuint)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some 156%positive)
                                    (Evar _mbedtls_hmac_drbg_seed (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_md_info_t noattr))
                                                                    (Tcons
                                                                    (tptr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tint
                                                                    cc_default))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))))))
                                                                    tint
                                                                    cc_default))
                                    ((Eaddrof
                                       (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                     (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                                     (Evar _hmac_drbg_self_test_entropy 
                                     (Tfunction
                                       (Tcons (tptr tvoid)
                                         (Tcons (tptr tuchar)
                                           (Tcons tuint Tnil))) tint
                                       cc_default)) ::
                                     (Ecast
                                       (Evar _entropy_nopr (tarray tuchar 40))
                                       (tptr tvoid)) ::
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) ::
                                     (Econst_int (Int.repr 0) tint) :: nil))
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar 156%positive tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _verbose tint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Scall None
                                          (Evar _printf (Tfunction
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil) tint
                                                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                          ((Evar ___stringlit_2 (tarray tschar 8)) ::
                                           nil))
                                        Sskip)
                                      (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                                    Sskip))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some 157%positive)
                                      (Evar _mbedtls_hmac_drbg_reseed 
                                      (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                          (Tcons (tptr tuchar)
                                            (Tcons tuint Tnil))) tint
                                        cc_default))
                                      ((Eaddrof
                                         (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                         (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                       (Ecast (Econst_int (Int.repr 0) tint)
                                         (tptr tvoid)) ::
                                       (Econst_int (Int.repr 0) tint) :: nil))
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar 157%positive tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Ssequence
                                        (Sifthenelse (Ebinop One
                                                       (Etempvar _verbose tint)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Scall None
                                            (Evar _printf (Tfunction
                                                            (Tcons
                                                              (tptr tschar)
                                                              Tnil) tint
                                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                            ((Evar ___stringlit_2 (tarray tschar 8)) ::
                                             nil))
                                          Sskip)
                                        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                                      Sskip))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some 158%positive)
                                        (Evar _mbedtls_hmac_drbg_random 
                                        (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons (tptr tuchar)
                                              (Tcons tuint Tnil))) tint
                                          cc_default))
                                        ((Eaddrof
                                           (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                           (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                         (Evar _buf (tarray tuchar 80)) ::
                                         (Econst_int (Int.repr 80) tint) ::
                                         nil))
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar 158%positive tint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Ssequence
                                          (Sifthenelse (Ebinop One
                                                         (Etempvar _verbose tint)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Scall None
                                              (Evar _printf (Tfunction
                                                              (Tcons
                                                                (tptr tschar)
                                                                Tnil) tint
                                                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                              ((Evar ___stringlit_2 (tarray tschar 8)) ::
                                               nil))
                                            Sskip)
                                          (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                                        Sskip))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some 159%positive)
                                          (Evar _mbedtls_hmac_drbg_random 
                                          (Tfunction
                                            (Tcons (tptr tvoid)
                                              (Tcons (tptr tuchar)
                                                (Tcons tuint Tnil))) tint
                                            cc_default))
                                          ((Eaddrof
                                             (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                             (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                           (Evar _buf (tarray tuchar 80)) ::
                                           (Econst_int (Int.repr 80) tint) ::
                                           nil))
                                        (Sifthenelse (Ebinop One
                                                       (Etempvar 159%positive tint)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Ssequence
                                            (Sifthenelse (Ebinop One
                                                           (Etempvar _verbose tint)
                                                           (Econst_int (Int.repr 0) tint)
                                                           tint)
                                              (Scall None
                                                (Evar _printf (Tfunction
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  Tnil) tint
                                                                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                ((Evar ___stringlit_2 (tarray tschar 8)) ::
                                                 nil))
                                              Sskip)
                                            (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                                          Sskip))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some 160%positive)
                                            (Evar _memcmp (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              (Tcons
                                                                (tptr tvoid)
                                                                (Tcons tuint
                                                                  Tnil)))
                                                            tint cc_default))
                                            ((Evar _buf (tarray tuchar 80)) ::
                                             (Evar _result_nopr (tarray tuchar 80)) ::
                                             (Econst_int (Int.repr 80) tint) ::
                                             nil))
                                          (Sifthenelse (Ebinop One
                                                         (Etempvar 160%positive tint)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _verbose tint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Scall None
                                                  (Evar _printf (Tfunction
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)
                                                                  tint
                                                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                  ((Evar ___stringlit_2 (tarray tschar 8)) ::
                                                   nil))
                                                Sskip)
                                              (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                                            Sskip))
                                        (Ssequence
                                          (Scall None
                                            (Evar _mbedtls_hmac_drbg_free 
                                            (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                Tnil) tvoid cc_default))
                                            ((Eaddrof
                                               (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                               (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _mbedtls_hmac_drbg_free 
                                              (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                  Tnil) tvoid cc_default))
                                              ((Eaddrof
                                                 (Evar _ctx (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                 (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                               nil))
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _verbose tint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Scall None
                                                  (Evar _printf (Tfunction
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)
                                                                  tint
                                                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                  ((Evar ___stringlit_3 (tarray tschar 8)) ::
                                                   nil))
                                                Sskip)
                                              (Ssequence
                                                (Sifthenelse (Ebinop One
                                                               (Etempvar _verbose tint)
                                                               (Econst_int (Int.repr 0) tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _printf (Tfunction
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)
                                                                    tint
                                                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                    ((Evar ___stringlit_5 (tarray tschar 2)) ::
                                                     nil))
                                                  Sskip)
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((161%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some 161%positive)
    (Evar _mbedtls_hmac_drbg_self_test (Tfunction (Tcons tint Tnil) tint
                                         cc_default))
    ((Econst_int (Int.repr 1) tint) :: nil))
  (Sreturn (Some (Etempvar 161%positive tint))))
|}.

Definition composites : list composite_definition :=
(Composite _mbedtls_md_context_t Struct
   ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
    (_md_ctx, (tptr tvoid)) :: (_hmac_ctx, (tptr tvoid)) :: nil)
   noattr ::
 Composite _mbedtls_hmac_drbg_context Struct
   ((_md_ctx, (Tstruct _mbedtls_md_context_t noattr)) ::
    (_V, (tarray tuchar 32)) :: (_reseed_counter, tint) ::
    (_entropy_len, tuint) :: (_prediction_resistance, tint) ::
    (_reseed_interval, tint) ::
    (_f_entropy,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tuint Tnil)))
             tint cc_default))) :: (_p_entropy, (tptr tvoid)) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin ___builtin_membar
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external ___compcert_va_composite
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_external ___i64_dtos
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_external ___i64_dtou
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_external ___i64_stod
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_external ___i64_utod
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_external ___i64_stof
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_external ___i64_utof
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_external ___i64_sdiv
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_external ___i64_udiv
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_external ___i64_smod
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_external ___i64_umod
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_external ___i64_shl
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_external ___i64_shr
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_external ___i64_sar
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin ___builtin_clz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin ___builtin_ctz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (_mbedtls_md_info_from_type,
   Gfun(External (EF_external _mbedtls_md_info_from_type
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) (tptr (Tstruct _mbedtls_md_info_t noattr))
     cc_default)) ::
 (_mbedtls_md_free,
   Gfun(External (EF_external _mbedtls_md_free
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr)) Tnil) tvoid
     cc_default)) ::
 (_mbedtls_md_setup,
   Gfun(External (EF_external _mbedtls_md_setup
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
       (Tcons (tptr (Tstruct _mbedtls_md_info_t noattr)) (Tcons tint Tnil)))
     tint cc_default)) ::
 (_mbedtls_md_get_size,
   Gfun(External (EF_external _mbedtls_md_get_size
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_info_t noattr)) Tnil) tuchar
     cc_default)) ::
 (_mbedtls_md_hmac_starts,
   Gfun(External (EF_external _mbedtls_md_hmac_starts
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
       (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint cc_default)) ::
 (_mbedtls_md_hmac_update,
   Gfun(External (EF_external _mbedtls_md_hmac_update
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
       (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint cc_default)) ::
 (_mbedtls_md_hmac_finish,
   Gfun(External (EF_external _mbedtls_md_hmac_finish
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
       (Tcons (tptr tuchar) Tnil)) tint cc_default)) ::
 (_mbedtls_md_hmac_reset,
   Gfun(External (EF_external _mbedtls_md_hmac_reset
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr)) Tnil) tint
     cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external _memcpy
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external _memset
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_memcmp,
   Gfun(External (EF_external _memcmp
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
     cc_default)) ::
 (_printf,
   Gfun(External (EF_external _printf
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_mbedtls_zeroize, Gfun(Internal f_mbedtls_zeroize)) ::
 (_mbedtls_hmac_drbg_init, Gfun(Internal f_mbedtls_hmac_drbg_init)) ::
 (_mbedtls_hmac_drbg_update, Gfun(Internal f_mbedtls_hmac_drbg_update)) ::
 (_mbedtls_hmac_drbg_seed_buf, Gfun(Internal f_mbedtls_hmac_drbg_seed_buf)) ::
 (_mbedtls_hmac_drbg_reseed, Gfun(Internal f_mbedtls_hmac_drbg_reseed)) ::
 (_mbedtls_hmac_drbg_seed, Gfun(Internal f_mbedtls_hmac_drbg_seed)) ::
 (_mbedtls_hmac_drbg_set_prediction_resistance, Gfun(Internal f_mbedtls_hmac_drbg_set_prediction_resistance)) ::
 (_mbedtls_hmac_drbg_set_entropy_len, Gfun(Internal f_mbedtls_hmac_drbg_set_entropy_len)) ::
 (_mbedtls_hmac_drbg_set_reseed_interval, Gfun(Internal f_mbedtls_hmac_drbg_set_reseed_interval)) ::
 (_mbedtls_hmac_drbg_random_with_add, Gfun(Internal f_mbedtls_hmac_drbg_random_with_add)) ::
 (_mbedtls_hmac_drbg_random, Gfun(Internal f_mbedtls_hmac_drbg_random)) ::
 (_mbedtls_hmac_drbg_free, Gfun(Internal f_mbedtls_hmac_drbg_free)) ::
 (_entropy_pr, Gvar v_entropy_pr) :: (_result_pr, Gvar v_result_pr) ::
 (_entropy_nopr, Gvar v_entropy_nopr) ::
 (_result_nopr, Gvar v_result_nopr) :: (_test_offset, Gvar v_test_offset) ::
 (_hmac_drbg_self_test_entropy, Gfun(Internal f_hmac_drbg_self_test_entropy)) ::
 (_mbedtls_hmac_drbg_self_test, Gfun(Internal f_mbedtls_hmac_drbg_self_test)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _mbedtls_hmac_drbg_self_test :: _mbedtls_hmac_drbg_free ::
 _mbedtls_hmac_drbg_random :: _mbedtls_hmac_drbg_random_with_add ::
 _mbedtls_hmac_drbg_set_reseed_interval ::
 _mbedtls_hmac_drbg_set_entropy_len ::
 _mbedtls_hmac_drbg_set_prediction_resistance :: _mbedtls_hmac_drbg_seed ::
 _mbedtls_hmac_drbg_reseed :: _mbedtls_hmac_drbg_seed_buf ::
 _mbedtls_hmac_drbg_update :: _mbedtls_hmac_drbg_init :: _printf ::
 _memcmp :: _memset :: _memcpy :: _mbedtls_md_hmac_reset ::
 _mbedtls_md_hmac_finish :: _mbedtls_md_hmac_update ::
 _mbedtls_md_hmac_starts :: _mbedtls_md_get_size :: _mbedtls_md_setup ::
 _mbedtls_md_free :: _mbedtls_md_info_from_type ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fsqrt :: ___builtin_ctz :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod ::
 ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod ::
 ___i64_stod :: ___i64_dtou :: ___i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.