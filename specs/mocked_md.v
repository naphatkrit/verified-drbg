Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _d : ident := 85%positive.
Definition _SHA256_Init : ident := 65%positive.
Definition ___i64_sdiv : ident := 40%positive.
Definition _num : ident := 16%positive.
Definition ___i64_stof : ident := 38%positive.
Definition ___i64_sar : ident := 46%positive.
Definition _key : ident := 69%positive.
Definition _free : ident := 62%positive.
Definition ___builtin_fmin : ident := 54%positive.
Definition ___builtin_memcpy_aligned : ident := 22%positive.
Definition _h : ident := 12%positive.
Definition _md_name : ident := 92%positive.
Definition _mbedtls_md_free : ident := 108%positive.
Definition _ilen : ident := 104%positive.
Definition _memcpy : ident := 63%positive.
Definition _hmac_ctx : ident := 10%positive.
Definition ___i64_shl : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition ___compcert_va_int64 : ident := 31%positive.
Definition _HMAC : ident := 88%positive.
Definition _md : ident := 79%positive.
Definition _j : ident := 72%positive.
Definition ___builtin_bswap16 : ident := 49%positive.
Definition _SHA256_Update : ident := 66%positive.
Definition ___builtin_read16_reversed : ident := 59%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _main : ident := 109%positive.
Definition _HMAC_Update : ident := 78%positive.
Definition _md_type : ident := 94%positive.
Definition _ctx : ident := 68%positive.
Definition ___builtin_fnmsub : ident := 58%positive.
Definition ___builtin_va_copy : ident := 28%positive.
Definition _mbedtls_md_hmac_reset : ident := 102%positive.
Definition _mbedtls_md_info_t : ident := 7%positive.
Definition _input : ident := 103%positive.
Definition _mbedtls_md_setup : ident := 99%positive.
Definition ___builtin_fabs : ident := 21%positive.
Definition _i_ctx : ident := 18%positive.
Definition _mbedtls_md_hmac_starts : ident := 101%positive.
Definition _m__1 : ident := 89%positive.
Definition ___i64_shr : ident := 45%positive.
Definition _output : ident := 106%positive.
Definition _buf : ident := 80%positive.
Definition _Nl : ident := 13%positive.
Definition ___builtin_va_arg : ident := 27%positive.
Definition _key_len : ident := 84%positive.
Definition _HMAC_cleanup : ident := 82%positive.
Definition ___compcert_va_composite : ident := 33%positive.
Definition ___builtin_fmsub : ident := 56%positive.
Definition ___builtin_membar : ident := 25%positive.
Definition _data : ident := 15%positive.
Definition ___builtin_read32_reversed : ident := 60%positive.
Definition _keylen : ident := 100%positive.
Definition _hmac_ctx_st : ident := 20%positive.
Definition ___compcert_va_float64 : ident := 32%positive.
Definition _mbedtls_md_info_from_string : ident := 93%positive.
Definition _mbedtls_md_hmac_update : ident := 105%positive.
Definition _len : ident := 70%positive.
Definition ___builtin_annot_intval : ident := 24%positive.
Definition _mbedtls_md_get_size : ident := 96%positive.
Definition _SHA256_Final : ident := 67%positive.
Definition _SHA256state_st : ident := 17%positive.
Definition _md_info : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _reset : ident := 73%positive.
Definition ___builtin_clz : ident := 50%positive.
Definition ___i64_umod : ident := 43%positive.
Definition _pad : ident := 74%positive.
Definition ___builtin_fmax : ident := 53%positive.
Definition ___builtin_bswap : ident := 47%positive.
Definition _mbedtls_md_hmac_finish : ident := 107%positive.
Definition ___builtin_fnmadd : ident := 57%positive.
Definition _mocked_sha256_info : ident := 91%positive.
Definition ___i64_stod : ident := 36%positive.
Definition _Nh : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _sha_ctx : ident := 98%positive.
Definition ___builtin_va_start : ident := 26%positive.
Definition _o_ctx : ident := 19%positive.
Definition ___i64_utof : ident := 39%positive.
Definition _HMAC2 : ident := 90%positive.
Definition _m : ident := 83%positive.
Definition _malloc : ident := 61%positive.
Definition __243 : ident := 11%positive.
Definition _hmac : ident := 97%positive.
Definition ___i64_utod : ident := 37%positive.
Definition _HMAC_Final : ident := 81%positive.
Definition _ctx_key : ident := 76%positive.
Definition _n : ident := 86%positive.
Definition ___i64_smod : ident := 42%positive.
Definition _md_ctx : ident := 9%positive.
Definition _memset : ident := 64%positive.
Definition ___builtin_fsqrt : ident := 52%positive.
Definition ___i64_udiv : ident := 41%positive.
Definition _c : ident := 87%positive.
Definition _HMAC_Init : ident := 77%positive.
Definition _i : ident := 71%positive.
Definition _aux : ident := 75%positive.
Definition ___i64_dtos : ident := 34%positive.
Definition ___builtin_va_end : ident := 29%positive.
Definition _mbedtls_md_info_from_type : ident := 95%positive.
Definition ___builtin_fmadd : ident := 55%positive.
Definition ___i64_dtou : ident := 35%positive.
Definition ___compcert_va_int32 : ident := 30%positive.
Definition ___builtin_annot : ident := 23%positive.
Definition ___builtin_ctz : ident := 51%positive.
Definition ___builtin_bswap32 : ident := 48%positive.

Definition f_HMAC_Init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_key, (tptr tuchar)) :: (_len, tint) :: nil);
  fn_vars := ((_pad, (tarray tuchar 64)) :: (_ctx_key, (tarray tuchar 64)) ::
              nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_reset, tint) ::
               (_aux, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _reset (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _key (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _reset (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _j (Econst_int (Int.repr 64) tint))
          (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _len tint)
                         tint)
            (Ssequence
              (Scall None
                (Evar _SHA256_Init (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _SHA256state_st noattr))
                                       Tnil) tvoid cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                       (Tstruct _hmac_ctx_st noattr)) _md_ctx
                     (Tstruct _SHA256state_st noattr))
                   (tptr (Tstruct _SHA256state_st noattr))) :: nil))
              (Ssequence
                (Scall None
                  (Evar _SHA256_Update (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _SHA256state_st noattr))
                                           (Tcons (tptr tvoid)
                                             (Tcons tuint Tnil))) tvoid
                                         cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                         (Tstruct _hmac_ctx_st noattr)) _md_ctx
                       (Tstruct _SHA256state_st noattr))
                     (tptr (Tstruct _SHA256state_st noattr))) ::
                   (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar _SHA256_Final (Tfunction
                                          (Tcons (tptr tuchar)
                                            (Tcons
                                              (tptr (Tstruct _SHA256state_st noattr))
                                              Tnil)) tvoid cc_default))
                    ((Evar _ctx_key (tarray tuchar 64)) ::
                     (Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _md_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
                  (Scall None
                    (Evar _memset (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Eaddrof
                       (Ederef
                         (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                           (Econst_int (Int.repr 32) tint) (tptr tuchar))
                         tuchar) (tptr tuchar)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))))
            (Ssequence
              (Scall None
                (Evar _memcpy (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Evar _ctx_key (tarray tuchar 64)) ::
                 (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                 nil))
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Eaddrof
                   (Ederef
                     (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Etempvar _len tint) (tptr tuchar)) tuchar)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub (Esizeof (tarray tuchar 64) tuint)
                   (Etempvar _len tint) tuint) :: nil))))))
      Sskip)
    (Ssequence
      (Sifthenelse (Etempvar _reset tint)
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 64) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _aux
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar) tuchar))
                  (Ssequence
                    (Sset _aux
                      (Ecast
                        (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                          (Etempvar _aux tuchar) tint) tuchar))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar)
                      (Etempvar _aux tuchar)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Scall None
              (Evar _SHA256_Init (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _SHA256state_st noattr))
                                     Tnil) tvoid cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef
                     (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                     (Tstruct _hmac_ctx_st noattr)) _i_ctx
                   (Tstruct _SHA256state_st noattr))
                 (tptr (Tstruct _SHA256state_st noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _SHA256_Update (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _SHA256state_st noattr))
                                         (Tcons (tptr tvoid)
                                           (Tcons tuint Tnil))) tvoid
                                       cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                       (Tstruct _hmac_ctx_st noattr)) _i_ctx
                     (Tstruct _SHA256state_st noattr))
                   (tptr (Tstruct _SHA256state_st noattr))) ::
                 (Evar _pad (tarray tuchar 64)) ::
                 (Econst_int (Int.repr 64) tint) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Econst_int (Int.repr 64) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _aux
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar)
                            tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                              (Etempvar _i tint) (tptr tuchar)) tuchar)
                          (Ebinop Oxor (Econst_int (Int.repr 92) tint)
                            (Etempvar _aux tuchar) tint))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall None
                    (Evar _SHA256_Init (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _SHA256state_st noattr))
                                           Tnil) tvoid cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _o_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
                  (Scall None
                    (Evar _SHA256_Update (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _SHA256state_st noattr))
                                             (Tcons (tptr tvoid)
                                               (Tcons tuint Tnil))) tvoid
                                           cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _o_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) ::
                     (Evar _pad (tarray tuchar 64)) ::
                     (Econst_int (Int.repr 64) tint) :: nil)))))))
        Sskip)
      (Scall None
        (Evar _memcpy (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                        (tptr tvoid) cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _md_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _i_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) ::
         (Esizeof (Tstruct _SHA256state_st noattr) tuint) :: nil)))))
|}.

Definition f_HMAC_Update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _SHA256_Update (Tfunction
                         (Tcons (tptr (Tstruct _SHA256state_st noattr))
                           (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                         cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
         (Tstruct _hmac_ctx_st noattr)) _md_ctx
       (Tstruct _SHA256state_st noattr))
     (tptr (Tstruct _SHA256state_st noattr))) ::
   (Etempvar _data (tptr tvoid)) :: (Etempvar _len tuint) :: nil))
|}.

Definition f_HMAC_Final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := ((_buf, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _SHA256_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr (Tstruct _SHA256state_st noattr))
                              Tnil)) tvoid cc_default))
    ((Evar _buf (tarray tuchar 32)) ::
     (Eaddrof
       (Efield
         (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
           (Tstruct _hmac_ctx_st noattr)) _md_ctx
         (Tstruct _SHA256state_st noattr))
       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                      cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
             (Tstruct _hmac_ctx_st noattr)) _md_ctx
           (Tstruct _SHA256state_st noattr))
         (tptr (Tstruct _SHA256state_st noattr))) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
             (Tstruct _hmac_ctx_st noattr)) _o_ctx
           (Tstruct _SHA256state_st noattr))
         (tptr (Tstruct _SHA256state_st noattr))) ::
       (Esizeof (Tstruct _SHA256state_st noattr) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _SHA256_Update (Tfunction
                               (Tcons (tptr (Tstruct _SHA256state_st noattr))
                                 (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                               tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _md_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) ::
         (Evar _buf (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Scall None
        (Evar _SHA256_Final (Tfunction
                              (Tcons (tptr tuchar)
                                (Tcons
                                  (tptr (Tstruct _SHA256state_st noattr))
                                  Tnil)) tvoid cc_default))
        ((Etempvar _md (tptr tuchar)) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _md_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) :: nil)))))
|}.

Definition f_HMAC_cleanup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _hmac_ctx_st noattr) tuint) :: nil))
|}.

Definition v_m := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_HMAC := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_d, (tptr tuchar)) :: (_n, tint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, (Tstruct _hmac_ctx_st noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _md (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _md (Evar _m (tarray tuchar 32)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
         (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                             cc_default))
        ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
           (tptr (Tstruct _hmac_ctx_st noattr))) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
             (tptr (Tstruct _hmac_ctx_st noattr))) ::
           (Etempvar _md (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_cleanup (Tfunction
                                  (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                    Tnil) tvoid cc_default))
            ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
               (tptr (Tstruct _hmac_ctx_st noattr))) :: nil))
          (Sreturn (Some (Etempvar _md (tptr tuchar)))))))))
|}.

Definition v_m__1 := {|
  gvar_info := (tarray tuchar 64);
  gvar_init := (Init_space 64 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_HMAC2 := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_d, (tptr tuchar)) :: (_n, tint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, (Tstruct _hmac_ctx_st noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _md (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _md (Evar _m__1 (tarray tuchar 64)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
         (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                             cc_default))
        ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
           (tptr (Tstruct _hmac_ctx_st noattr))) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
             (tptr (Tstruct _hmac_ctx_st noattr))) ::
           (Etempvar _md (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_Init (Tfunction
                               (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                 (Tcons (tptr tuchar) (Tcons tint Tnil)))
                               tvoid cc_default))
            ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
               (tptr (Tstruct _hmac_ctx_st noattr))) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
             (Etempvar _key_len tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _HMAC_Update (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _hmac_ctx_st noattr))
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                   tvoid cc_default))
              ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _HMAC_Final (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _hmac_ctx_st noattr))
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default))
                ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                   (tptr (Tstruct _hmac_ctx_st noattr))) ::
                 (Ebinop Oadd (Etempvar _md (tptr tuchar))
                   (Econst_int (Int.repr 32) tint) (tptr tuchar)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _HMAC_cleanup (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _hmac_ctx_st noattr))
                                          Tnil) tvoid cc_default))
                  ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                     (tptr (Tstruct _hmac_ctx_st noattr))) :: nil))
                (Sreturn (Some (Etempvar _md (tptr tuchar))))))))))))
|}.

Definition v_mocked_sha256_info := {|
  gvar_info := (Tstruct _mbedtls_md_info_t noattr);
  gvar_init := (Init_space 0 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_mbedtls_md_info_from_string := {|
  fn_return := (tptr (Tstruct _mbedtls_md_info_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_md_name, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _mocked_sha256_info (Tstruct _mbedtls_md_info_t noattr))
                 (tptr (Tstruct _mbedtls_md_info_t noattr)))))
|}.

Definition f_mbedtls_md_info_from_type := {|
  fn_return := (tptr (Tstruct _mbedtls_md_info_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_md_type, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _mocked_sha256_info (Tstruct _mbedtls_md_info_t noattr))
                 (tptr (Tstruct _mbedtls_md_info_t noattr)))))
|}.

Definition f_mbedtls_md_get_size := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 32) tint)))
|}.

Definition f_mbedtls_md_setup := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct __243 noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_hmac, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_sha_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (110%positive, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some 110%positive)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _hmac_ctx_st noattr) tuint) :: nil))
    (Sset _sha_ctx
      (Ecast (Etempvar 110%positive (tptr tvoid))
        (tptr (Tstruct _hmac_ctx_st noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _sha_ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 20864) tint) tint)))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
            (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid))
        (Etempvar _sha_ctx (tptr (Tstruct _hmac_ctx_st noattr))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_mbedtls_md_hmac_starts := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct __243 noattr))) ::
                (_key, (tptr tuchar)) :: (_keylen, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Init (Tfunction
                       (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                         (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                       cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
         (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid)) ::
     (Ecast (Etempvar _key (tptr tuchar)) (tptr tuchar)) ::
     (Etempvar _keylen tuint) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_hmac_reset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct __243 noattr))) :: nil);
  fn_vars := ((_buf, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Final (Tfunction
                        (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
         (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid)) ::
     (Evar _buf (tarray tuchar 32)) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_hmac_update := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct __243 noattr))) ::
                (_input, (tptr tuchar)) :: (_ilen, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Update (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                         cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
         (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid)) ::
     (Etempvar _input (tptr tuchar)) :: (Etempvar _ilen tuint) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_hmac_finish := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct __243 noattr))) ::
                (_output, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Final (Tfunction
                        (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
         (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid)) ::
     (Etempvar _output (tptr tuchar)) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct __243 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_cleanup (Tfunction
                          (Tcons (tptr (Tstruct _hmac_ctx_st noattr)) Tnil)
                          tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
         (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid)) :: nil))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct __243 noattr)))
         (Tstruct __243 noattr)) _hmac_ctx (tptr tvoid)) :: nil)))
|}.

Definition composites : list composite_definition :=
(Composite __243 Struct
   ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
    (_md_ctx, (tptr tvoid)) :: (_hmac_ctx, (tptr tvoid)) :: nil)
   noattr ::
 Composite _SHA256state_st Struct
   ((_h, (tarray tuint 8)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite _hmac_ctx_st Struct
   ((_md_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_i_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_o_ctx, (Tstruct _SHA256state_st noattr)) :: nil)
   noattr :: Composite _mbedtls_md_info_t Struct nil noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
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
 (_SHA256_Init,
   Gfun(External (EF_external _SHA256_Init
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil) tvoid cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external _SHA256_Update
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external _SHA256_Final
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil)) tvoid
     cc_default)) :: (_HMAC_Init, Gfun(Internal f_HMAC_Init)) ::
 (_HMAC_Update, Gfun(Internal f_HMAC_Update)) ::
 (_HMAC_Final, Gfun(Internal f_HMAC_Final)) ::
 (_HMAC_cleanup, Gfun(Internal f_HMAC_cleanup)) :: (_m, Gvar v_m) ::
 (_HMAC, Gfun(Internal f_HMAC)) :: (_m__1, Gvar v_m__1) ::
 (_HMAC2, Gfun(Internal f_HMAC2)) ::
 (_mocked_sha256_info, Gvar v_mocked_sha256_info) ::
 (_mbedtls_md_info_from_string, Gfun(Internal f_mbedtls_md_info_from_string)) ::
 (_mbedtls_md_info_from_type, Gfun(Internal f_mbedtls_md_info_from_type)) ::
 (_mbedtls_md_get_size, Gfun(Internal f_mbedtls_md_get_size)) ::
 (_mbedtls_md_setup, Gfun(Internal f_mbedtls_md_setup)) ::
 (_mbedtls_md_hmac_starts, Gfun(Internal f_mbedtls_md_hmac_starts)) ::
 (_mbedtls_md_hmac_reset, Gfun(Internal f_mbedtls_md_hmac_reset)) ::
 (_mbedtls_md_hmac_update, Gfun(Internal f_mbedtls_md_hmac_update)) ::
 (_mbedtls_md_hmac_finish, Gfun(Internal f_mbedtls_md_hmac_finish)) ::
 (_mbedtls_md_free, Gfun(Internal f_mbedtls_md_free)) :: nil);
prog_public :=
(_mbedtls_md_free :: _mbedtls_md_hmac_finish :: _mbedtls_md_hmac_update ::
 _mbedtls_md_hmac_reset :: _mbedtls_md_hmac_starts :: _mbedtls_md_setup ::
 _mbedtls_md_get_size :: _mbedtls_md_info_from_type ::
 _mbedtls_md_info_from_string :: _HMAC2 :: _HMAC :: _HMAC_cleanup ::
 _HMAC_Final :: _HMAC_Update :: _HMAC_Init :: _SHA256_Final ::
 _SHA256_Update :: _SHA256_Init :: _memset :: _memcpy :: _free :: _malloc ::
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

