(* ========================================================================= *)
(*                                                                           *)
(*                     Formalization of Laplace Transform                    *)
(*                                                                           *)
(*    (c) Copyright, Adnan Rashid* & Osman Hasan**                           *)
(*                   System Analysis and Verification (SAVe) Lab,            *)
(*                   National University of Sciences and Technology          *)
(*                                                                           *)
(*     Contact: *<adnan.rashid@seecs.edu.pk>                                 *)
(*                                                                           *)
(* Last update: September 12, 2024                                           *)
(*                                                                           *)
(* ========================================================================= *)

(*---------------------------------------------------------------------------*)
(*                          Theories to load                                 *)
(*---------------------------------------------------------------------------*)

needs "Multivariate/cauchy.ml";; 

(*---------------------------------------------------------------------------*)
(*          Some useful theorems regarding real and complex numbers          *)
(*---------------------------------------------------------------------------*)

let LINEAR_CX_DROP = prove
 (`linear(Cx o drop)`,
  SIMP_TAC[linear; o_THM; COMPLEX_CMUL; DROP_ADD;CX_ADD; CX_ADD;DROP_CMUL; CX_MUL]);;

let CONTINUOUS_ON_CX_DROP1 = prove
 (`!s. (Cx o drop) continuous_on s`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CX_DROP]);;

let ABS_REAL_CONTINUOUS_ATREAL = prove
 (`!x. abs real_continuous (atreal x)`,
  REWRITE_TAC[real_continuous_atreal] THEN
  GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let ABS_REAL_CONTINUOUS_WITHIN = prove
 (`!s x. abs real_continuous (atreal x within s)`,
  MESON_TAC[ABS_REAL_CONTINUOUS_ATREAL; REAL_CONTINUOUS_ATREAL_WITHINREAL]);;

let VSUM_CX2 = prove
 (`!f:real^1#(real^1->bool)->real s:real^1#(real^1->bool)->bool.
   FINITE s ==> vsum s (\a :real^1#(real^1->bool) . Cx(f a)) = Cx(sum s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC [SUM_CLAUSES; VSUM_CLAUSES; COMPLEX_VEC_0; CX_ADD]);;

let VSUM_LIFT2 = prove
 (`!f:real^1#(real^1->bool)->real s:real^1#(real^1->bool)->bool.
  FINITE s ==> vsum s (\a :real^1#(real^1->bool) . lift (f a)) = lift (sum s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC [SUM_CLAUSES; VSUM_CLAUSES;  LIFT_ADD; LIFT_NUM]);;

let EQ_EXT_PAIR = prove
 (`!(f:real^1#(real^1->bool)->B) (g:real^1#(real^1->bool)->B).
 (!x. f x = g x) ==> f = g`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o ABS `x:real^1#(real^1->bool)` o SPEC 
      `x:real^1#(real^1->bool)`) THEN
  REWRITE_TAC[ETA_AX]);;

let FUN_EQ_THM_PAIR = prove
 (`!(f:real^1#(real^1->bool)->B) (g:real^1#(real^1->bool)->B). 
    f = g <=> (!x. f x = g x)`,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC;
    MATCH_ACCEPT_TAC EQ_EXT_PAIR]);;

let REAL_LE_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(&0 < x - y)` ASSUME_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  STRIP_TAC THEN UNDISCH_TAC `!e. &0 < e ==> x <= y + e` THEN SIMP_TAC [] THEN
  SIMP_TAC [NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC [REAL_ARITH `~((a:real) <= b + c) = c < a - b`] THEN
  ASM_MESON_TAC [REAL_DOWN]);;

let INTERVAL_TRANSLATION_1 = prove
 (`!a:real^1 b c. 
    interval [(\x. x - c) a , (\x. x - c) b] = 
    IMAGE (\x. x - c) (interval [a,b])`,
  SIMP_TAC [] THEN REWRITE_TAC [EXTENSION; IN_INTERVAL; IN_IMAGE] THEN
  REWRITE_TAC [VECTOR_ARITH `x:real^1 = x' - c <=> x + c = x'`] THEN
  REWRITE_TAC [UNWIND_THM1] THEN
  SIMP_TAC [VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REWRITE_TAC
    [REAL_ARITH
       `(a - (c:real) <= x  /\ x  <= b - c <=> a <= x + c /\ x + c <= b)`]);;

let VECTOR_SUB_ADD3 = VECTOR_ARITH `!x y. --x + x + y  = y:real^N`;;

let REAL_SUB_RNEG_1 = prove
 (`!x y. (x:real) - (y:real) = x + (--y)`,
  REAL_ARITH_TAC);;

let REAL_SUB_1 = prove
 (`!x y. --(x:real) - --(y:real) = --x + y`,
  REAL_ARITH_TAC);;

let REAL_LE_11 = prove
 (`!x y z. (x < y) /\ (y = z) ==> (x < z) `,
  REAL_ARITH_TAC);;

let REAL_LE_POW_ADD_2 = prove
 (`!x y. &0 <= (x - y) pow 2`,
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let REAL_LT_ADD2_SYM = prove
 (`!x y z. x < z /\ y < z ==> (x + y) < (&2 * z)`,
  REAL_ARITH_TAC);;

let REAL_LT_LSQRT = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x < y pow 2 ==> sqrt(x) < y`,
  MESON_TAC[SQRT_MONO_LT; REAL_POW_LT; POW_2_SQRT]);;

let REAL_NEG_ABS_EQ = prove
 (`!x . (x < &0) ==>  (abs(x) = --(x) )`,
  REAL_ARITH_TAC);;

let REAL_ABS_LE_POS = prove
 (`!x y . (abs(x) <= y) ==>  ( x <= y)`,
  REAL_ARITH_TAC);;

let abs_if1 = new_definition `
 !x. abs x = if &0 <= x then x else --x `;;

let REAL_LE_POS_ABS = prove
 (`!x y . ((x  <= y ) /\ (&0 <= y) )==> x <= abs(y) `,
  REAL_ARITH_TAC);;

let REAL_LT_IMP_NE1 = prove
 (`!x y. y < x ==> ~(x = y)`,
  REAL_ARITH_TAC);;

let RE_CX_II = prove
 (`!x y .Re (Cx x + ii * Cx y) = x`,
  REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let IM_CX_II = prove
 (`!x y .Im (Cx x + ii * Cx y) = y`,
  REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let CX_CMUL = prove
(`!c x. c % Cx x = Cx (c * x)`,
REWRITE_TAC [COMPLEX_CMUL] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let LIFT_VEC_0 = prove
 (`vec 0 = lift (&0)`,
  SIMP_TAC [CART_EQ; VEC_COMPONENT; DIMINDEX_1; FORALL_1; LIFT_COMPONENT]);;

let LIFT_VEC_1 = prove
 (`vec 1 = lift (&1)`,
  SIMP_TAC [CART_EQ; VEC_COMPONENT; DIMINDEX_1; FORALL_1; LIFT_COMPONENT]);;

let REAL_LE_ADD21 = prove
 (`!x y z. x <= y /\ &0 <= z ==> (x - z) <= (y - z)`, REAL_ARITH_TAC);;

let SUC_1 = prove
 (`!n. 1 <= n ==> SUC (n-1) = n`,
  ARITH_TAC);;

let SUB_ADD_1 = prove
 (`!x n. 1 <= x ==> n - (x - 1) = (n + 1) - x` ,
   ARITH_TAC);;

let IN_INTERVAL_TOTAL = prove
 (`!x:real^1 a b. (x IN interval [a, b]) \/  ~(x IN interval [a, b])`,
  REWRITE_TAC [IN_INTERVAL_1] THEN REAL_ARITH_TAC);;

let INV_REAL_MUL_COMPLEX = prove
 (`~(c = &0) ==> ((d * b = a * Cx (&1) / Cx c) =  (Cx c * d) * b = a)`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let GE_THN_ZERO_SUM = prove
 (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 < c) ==> (&0 < (a + b + c))`,
  REAL_ARITH_TAC);;

let GE_THN_ZERO_SUM_2 = prove
 (`!a b c. (&0 < a) /\ (&0 < b) ==> (&0 < (a + b))`,
  REAL_ARITH_TAC);;

let REAL_ADD_LE_3 = prove
 (`!w x y z. w <= c * z /\ x <= d * v /\ y <= u  ==> w + x + y <= c * z + d * v + u`,
  REAL_ARITH_TAC);;

let ABS_NEG_POS_EQ = prove
 (`!x. &0 < x ==> abs(--x)= x`,  REAL_ARITH_TAC);;

let SUC_GT_ZERO = prove
 (`!n:num. (0 < n) ==> SUC (n - 1)= n`,
  ARITH_TAC);;

let NUM_ZERO_TOTAL = prove
 (`!n:num. (n = 0) \/ (0 < n)`,
  ARITH_TAC);;

let COMPLEX_INV_EQ = prove
 (`~(b = &0) ==> ((a * (Cx (&1) / Cx b) = c ) <=> (a = Cx b * c))`,
  SIMPLE_COMPLEX_ARITH_TAC);;
  
let COMPLEX_INV_EQ_1 = prove
 (`~(x = &0) ==> ((Cx x * y = z )  <=> ( y = z * inv(Cx x)))`,
  SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_POS_NZ = prove
 (`!x. &0 < x ==> ~(x = &0)`,
  REAL_ARITH_TAC);;

let REAL_LT_NEG = prove
 (`!x y. --x < --y <=> y < x`,
  REAL_ARITH_TAC);;

(*---------------------------------------------------------------------------*)
(*                          Some custom tactics                              *)
(*---------------------------------------------------------------------------*)

let asm_conv_tac_complex_field = REPEAT (POP_ASSUM (MP_TAC)) THEN
    CONV_TAC COMPLEX_FIELD THEN REPEAT DISCH_TAC ;;

let asm_conv_tac_real_field = REPEAT (POP_ASSUM (MP_TAC)) THEN
    CONV_TAC REAL_FIELD THEN REPEAT DISCH_TAC ;;

let asm_simple_complex_arith_tac = REPEAT (POP_ASSUM (MP_TAC)) THEN
    SIMPLE_COMPLEX_ARITH_TAC THEN REPEAT DISCH_TAC ;;

let ap_term_thm_tac = AP_TERM_TAC THEN AP_THM_TAC;;

let strip_function_operand = AP_TERM_TAC THEN AP_THM_TAC;;

let strip_operand_function = AP_THM_TAC THEN AP_TERM_TAC;;

let strip_function = AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC;;

let strip_operand = AP_THM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC;;

(*---------------------------------------------------------------------------*)
(*         Some useful theorems regarding limit at positive infinity         *)
(*---------------------------------------------------------------------------*)

let EXP_A_TENDSTO_0_INFINITY = prove
 (`!(a:real) . &0 < a ==>
    ( (\(x:real). exp (--(a * x))) ---> &0) (at_posinfinity)`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `(--inv a * log e) + &1` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(--inv a * log e) + &1 <= x` ASSUME_TAC THENL
   [REWRITE_TAC [GSYM real_ge] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `x > --inv a * log e` ASSUME_TAC THENL
   [REWRITE_TAC [real_gt] THEN asm_conv_tac_real_field; ALL_TAC] THEN
  REWRITE_TAC [REAL_SUB_RZERO] THEN REWRITE_TAC [REAL_ABS_EXP] THEN
  SUBGOAL_THEN `(--inv a * log e < x)` ASSUME_TAC THENL
   [asm_conv_tac_real_field; ALL_TAC] THEN
  SUBGOAL_THEN `(--inv a * log e < (inv a * a) *  x)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv a * a = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV; ASM_SIMP_TAC []] THEN
    asm_conv_tac_real_field;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv a * --log e < inv a * (a * x)` ASSUME_TAC THENL
   [REWRITE_TAC [REAL_FIELD `inv a * --log e = --inv a * log e`] THEN
    ASM_REWRITE_TAC [REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--log e < (a * x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `inv (a:real)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC []] THEN UNDISCH_TAC `&0 < a` THEN
    REWRITE_TAC [REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp (--(a * x)) < exp(--(--log e))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(log (inv e) = --(log e))` ASSUME_TAC THENL
       [MATCH_MP_TAC LOG_INV;
        SUBGOAL_THEN `( --(log e) = log (inv e))` ASSUME_TAC THENL
         [ALL_TAC;
          ONCE_ASM_SIMP_TAC [] THEN SUBGOAL_THEN `&0 < inv e` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV;
            SUBGOAL_THEN `exp (log (inv e))= inv e` ASSUME_TAC THENL
             [MATCH_MP_TAC EXP_LOG; ALL_TAC]]]];
      REWRITE_TAC [REAL_EXP_MONO_LT]];
    SUBGOAL_THEN `exp (-- --log e) = e` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_NEG_NEG] THEN REWRITE_TAC [REAL_EXP_LOG];
      SUBGOAL_THEN `e = exp (-- --log e)` ASSUME_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC REAL_LE_11 THEN EXISTS_TAC `exp (-- --log e)` THEN
        CONJ_TAC]]] THEN
  ASM_SIMP_TAC []);;

let REAL_CONVERGENT_BOUNDED_INCREASING = prove
 (`! (f:real->real) b. (!m n. m <= n ==> f m <= f n)
       /\ (!n. abs(f n) <= b)  ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - l) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `\x. ?n. (f:real->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC [] THEN ANTS_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `abs x <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `!M'. (!x. (?n. (f:real->real) n = x) ==> x <= M') ==> l <= M'` THEN
  DISCH_THEN (MP_TAC o SPEC `((l:real) - e)`) THEN
  ASM_MESON_TAC
    [REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
     REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

let REAL_CONVERGENT_BOUNDED_INCREASING_ALT = prove
 (`! (f:real->real) b. (!m n. m <= n ==> f m <= f n)
    /\ (!n. abs(f n) <= b) ==> ?l. !e. &0 < e ==> ?N. !n. n >= N ==> abs(f n - l) < e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [real_ge] THEN
  MP_TAC (SPEC `\x. ?n. (f:real->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC [] THEN ANTS_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `abs(x) <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `!M'. (!x. (?n. (f:real->real) n = x) ==> x <= M') ==> l <= M'` THEN
  DISCH_THEN (MP_TAC o SPEC `((l:real) - e)`) THEN
  ASM_MESON_TAC
    [REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
     REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

let SEQ_MONO_LE = prove
 (`!(f:real->real) x n k. (&0 <= n) /\ 
      (!n m.(n <= m) ==> ( f n <= f (m) ))
      /\ ( (f ---> k) at_posinfinity ) ==>  f n <= k`,
  REPEAT GEN_TAC THEN REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_EPS THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real)`) THEN ASM_SIMP_TAC [] THEN
  SIMP_TAC [real_ge] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`b:real`; `n:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `n:real`) THEN ASM_SIMP_TAC [] THEN
    ASM_REWRITE_TAC [abs_if1] THEN ASM_REWRITE_TAC [REAL_LE_SUB_LADD] THEN
    ASM_REWRITE_TAC [REAL_ADD_LID] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_SUB_RADD] THEN STRIP_TAC THEN
      ASM_MESON_TAC [REAL_LT_LE; REAL_ADD_SYM];
      ASM_REWRITE_TAC [REAL_NEG_SUB] THEN ASM_REWRITE_TAC [REAL_LT_SUB_RADD] THEN
      STRIP_TAC THEN UNDISCH_TAC `~(k <= (f:real->real) n)` THEN
      ASM_REWRITE_TAC [REAL_NOT_LE] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k:real` THEN
      ASM_MESON_TAC [REAL_LT_LE; REAL_LE_ADDR]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(i:num). f ((b:real) - &i) <= k + (e : real)` ASSUME_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(f:real->real) b` THEN CONJ_TAC THENL
     [UNDISCH_TAC `!n m. n <= m ==> (f:real->real) n <= f  m` THEN
      DISCH_THEN (MP_TAC o SPEC `n:real`) THEN
      DISCH_THEN (MP_TAC o SPEC `b:real`);
      ALL_TAC] THEN
    ASM_SIMP_TAC []] THEN
  INDUCT_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `b:real`) THEN
    SUBGOAL_THEN `b <= (b:real)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN ASM_REWRITE_TAC [abs_if1] THEN
    SIMP_TAC [REAL_SUB_RZERO] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_SUB_RADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&0 <= (f:real->real) b - k)` THEN
    ASM_REWRITE_TAC [REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `abs((f:real->real) b - k) = --(f b - k)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_NEG_ABS_EQ THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ONCE_REWRITE_TAC [REAL_ADD_AC] THEN REWRITE_TAC [GSYM REAL_LE_SUB_RADD] THEN
    MATCH_MP_TAC REAL_ABS_LE_POS THEN ASM_SIMP_TAC [] THEN
    UNDISCH_TAC `--((f:real->real) b - k) < e` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `!n m. n <= m ==> (f:real->real) n <= f  m` THEN
    DISCH_THEN (MP_TAC o SPEC `( (b:real) - &(SUC (i:num)))`) THEN
    DISCH_THEN (MP_TAC o SPEC `(b:real) - &(SUC (i:num)) + &1`) THEN
    SUBGOAL_THEN `b - &(SUC i) <=  b - &(SUC i) + &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `n:real` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC []; REAL_ARITH_TAC];
        REWRITE_TAC [GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `( b - & (SUC i) ) + &1 = ( b - &i)` ASSUME_TAC THENL
       [REWRITE_TAC [GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(f:real->real)(b - &(SUC i) + &1)` THEN CONJ_TAC THEN
        ASM_SIMP_TAC []]]]);;

let REALLIM_ABS_LIM = prove
 (`!f:real->real l . 
 ((\i. f(abs i)) ---> l) at_posinfinity ==> (f ---> l) at_posinfinity`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN ASM_SIMP_TAC []];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN REPEAT STRIP_TAC] THEN
  asm_conv_tac_real_field);;

let REALLIM_ABS_LIM_1 = prove
 (`!f:real->real l. (f ---> l) at_posinfinity  ==>
     ((\i. f (abs i)) ---> l) at_posinfinity`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real`; EXISTS_TAC `&0`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
  asm_conv_tac_real_field);;

let LIM_ABS_LIM = prove
 (`!f:real->complex l. 
 (f --> l) at_posinfinity  ==> ((\i. f(abs i)) --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
    SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_ABS_REFL] THEN asm_conv_tac_real_field;
      ASM_SIMP_TAC []];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
    SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_ABS_REFL]; ASM_SIMP_TAC []] THEN
    asm_conv_tac_real_field]);;

let LIM_ABS_LIM_1 = prove
 (`!f:real->complex l. 
 (f --> l) at_posinfinity  ==> ((\i. f(abs i)) --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`&0`; `b:real`] REAL_LE_TOTAL) THEN STRIP_TAC THENL
   [EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
    SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_ABS_REFL] THEN asm_conv_tac_real_field;
      ASM_SIMP_TAC []];
    EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
    SUBGOAL_THEN `abs x = x:real` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_ABS_REFL]; ASM_SIMP_TAC []] THEN
    asm_conv_tac_real_field]);;

let LIM_POSINFINITY_REV = prove
 (`!f:real->complex l c . 
 ((\i. f(i + c)) --> l) at_posinfinity  ==> (f --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  MESON_TAC [REAL_ARITH `N + k <= n ==> N <= n - k /\ (n - k) + k = n`]);;

let LIM_POSINFINITY_REV_ABS = prove
 (`!f:real->complex l c . ((\i. f(i + abs(c))) --> l) at_posinfinity ==> (f --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  MESON_TAC [REAL_ARITH `N + k <= n ==> N <= n - k /\ (n - k) + k = n`]);;

let LIM_POSINFINITY_OFFSET = prove
 (`!f:real->complex l c. 
 (f --> l) at_posinfinity ==> ((\i. f (i + abs c)) --> l) at_posinfinity`,
  REWRITE_TAC [LIM_AT_POSINFINITY] THEN REWRITE_TAC [real_ge] THEN
  MESON_TAC [REAL_ARITH `N <= n ==> N <= n + abs k`]);;

let  convergent_f = new_definition
    `convergent_f (f:real->real^M)  net = (?l. (f --> l) net) ` ;;

let FUN_LIM = prove
 (`!(f:real->real^M) . convergent_f f net = 
    (f --> (lim net f) ) net`,
  GEN_TAC THEN REWRITE_TAC [convergent_f] THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [lim];
    DISCH_TAC THEN EXISTS_TAC `lim net (f:real->real^M)` THEN
    POP_ASSUM ACCEPT_TAC]);;

let LIM_OFFSET_LIM_EQ = prove
 (`!f:real->real^2 l c . (f --> l) at_posinfinity  ==> 
    lim at_posinfinity f = 
    lim at_posinfinity (\b . f (b + abs c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TENDSTO_LIM THEN
  SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
  SUBGOAL_THEN
    `((\x. (f:real->complex) (x + abs(c)))  --> 
  lim at_posinfinity (\x. f (x + abs(c)))) at_posinfinity`
    ASSUME_TAC THENL
   [SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
    EXISTS_TAC `l:complex` THEN ASM_SIMP_TAC [LIM_POSINFINITY_OFFSET];
    MATCH_MP_TAC LIM_POSINFINITY_REV_ABS THEN EXISTS_TAC `c:real` THEN
    ASM_SIMP_TAC []]);;

let LIM_UNIQUE_POSINFINITY = prove
 (`! f:real->complex l:complex l'.
      ~(trivial_limit at_posinfinity) /\ (f --> l) at_posinfinity 
     /\ (f --> l') at_posinfinity ==> (l = l')`,
  MESON_TAC [LIM_UNIQUE]);;

let ABS_LIM_ZERO_POSINFINTY = prove
 (`((f:real->real) ---> &0) at_posinfinity ==> ((\x. abs (f x)) ---> &0) at_posinfinity`,
  SIMP_TAC [REALLIM_AT_POSINFINITY; REAL_SUB_RZERO; REAL_ABS_ABS]);;

let LIM_ABS_LIM_EQ = prove
 (`!f:real->real^2 l . (f --> l) at_posinfinity  ==> lim at_posinfinity f = 
   lim at_posinfinity (\x . f (abs x))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC TENDSTO_LIM THEN
  SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN
  SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
  EXISTS_TAC `l:complex` THEN ASM_SIMP_TAC []);;

let LIM_UNIQUE_POSINFINITY = prove (`! f:real->complex l:complex l'.
   ~(trivial_limit at_posinfinity) /\ (f --> l) at_posinfinity /\ (f --> l') at_posinfinity ==> (l = l')`,
     MESON_TAC [LIM_UNIQUE]);;

let LIM_ABS_LIM_EQ_1 = prove
 (`!f:real->real^2 l . (f --> l) at_posinfinity  ==> lim at_posinfinity (\x . f(abs x))  = lim at_posinfinity f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TENDSTO_LIM THEN
  SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN
  SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
  EXISTS_TAC `l:complex` THEN ASM_SIMP_TAC []);;

let LIM_COMPLEX_REAL_COMPONENTS = prove
 (`!(f:real->complex) (L1:real) (L2:real). 
    ( ( (\t. Re (f t) ) ---> L1) at_posinfinity )  /\
     ( ( (\t. Im (f t) ) ---> L2) at_posinfinity ) ==>
        (  ( f --> complex(L1, L2) ) at_posinfinity )`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [REALLIM_AT_POSINFINITY; LIM_AT_POSINFINITY] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real) * inv (sqrt (&2))`) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real) * inv (sqrt (&2))`) THEN
  SUBGOAL_THEN `&0 < e * inv (sqrt (&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN `inv(sqrt (&2) ) = sqrt (inv (&2 ))` ASSUME_TAC THENL
   [SIMP_TAC [GSYM SQRT_INV]; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `max (b:real) (b':real)` THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(x:real)`) THEN
  SUBGOAL_THEN `(x:real) >= (b:real)` ASSUME_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `x >= max y z ==>x >= y`]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) >= (b':real)` ASSUME_TAC THENL
   [ASM_MESON_TAC [REAL_ARITH `x >= max y z ==>x >= z`]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [dist] THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX] THEN REWRITE_TAC [RE_SUB] THEN
  ONCE_REWRITE_TAC [RE] THEN REWRITE_TAC [IM_SUB] THEN ONCE_REWRITE_TAC [IM] THEN
  REWRITE_TAC [complex_norm] THEN ONCE_REWRITE_TAC [RE; IM] THEN
  SUBGOAL_THEN
    `abs (Re ((f:real->complex) x) - L1) pow 2 < (e * inv (sqrt (&2))) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC []];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `abs (Im ((f:real->complex) x) - L2) pow 2 < (e * inv (sqrt (&2))) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC []];
    ALL_TAC] THEN
  UNDISCH_TAC
    `abs (Re ((f:real->complex) x) - L1) pow 2 < (e * inv (sqrt (&2))) pow 2` THEN
  REWRITE_TAC [REAL_POW2_ABS] THEN STRIP_TAC THEN
  UNDISCH_TAC
    `abs (Im ((f:real->complex) x) - L2) pow 2 < (e * inv (sqrt (&2))) pow 2` THEN
  REWRITE_TAC [REAL_POW2_ABS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(Re ((f:real->complex) x) - L1) pow 2 + (Im (f x) - L2) pow 2 <
      &2 * (e * inv (sqrt (&2))) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD2_SYM THEN CONJ_TAC THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * (e * inv (sqrt (&2))) pow 2 ) = e pow 2` ASSUME_TAC THENL
   [REWRITE_TAC [REAL_POW_MUL] THEN ONCE_REWRITE_TAC [GSYM REAL_INV_POW] THEN
    SUBGOAL_THEN `(sqrt (&2) pow 2) = &2` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2; ASM_SIMP_TAC []] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC
      `(Re ((f:real->complex) x) - L1) pow 2 + (Im (f x) - L2) pow 2 <
      &2 * (e * inv (sqrt (&2))) pow 2` THEN
    ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REWRITE_TAC [REAL_LE_POW_ADD_2];
      CONJ_TAC THENL
       [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ASM_SIMP_TAC []]]]);;

let INTEGRAL_COMPARISON_TEST = prove
 (`!(f:real->real) (g:real->real) a. 
  (!x. a <= x ==> (&0 <= f x /\ f x <= g x)) /\ (&0 <= a) /\
    (!b. ( g real_integrable_on real_interval [a,b] ) ) /\
      (?k.( ( (\b. (real_integral (real_interval [a,b]) g) ) ---> k) at_posinfinity  ) )  /\
      (!b. ( f real_integrable_on real_interval [a,b] ) ) ==>
        (?k.( ( (\b. (real_integral (real_interval [a,b]) f) ) ---> k) at_posinfinity  ) )`,
  REWRITE_TAC [REALLIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONVERGENT_BOUNDED_INCREASING_ALT THEN
  EXISTS_TAC `k:real` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC (SPECL [`a:real`; `m:real`] REAL_LET_TOTAL) THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
        `real_integral (real_interval [a,x]) (f:real->real) =
      real_integral (real_interval [a,m]) f +
         real_integral (real_interval [m,x]) f`
        ASSUME_TAC THENL
       [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [REAL_LE_ADDR] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [m,x]) f) =
    ( ( real_integral (real_interval [m,x])  (\t. &0) ) <=
     real_integral (real_interval [m,x]) f )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC [REAL_INTEGRABLE_0] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `!b. f real_integrable_on real_interval [a,b]` THEN
        DISCH_THEN (MP_TAC o SPEC `x:real`) THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN EXISTS_TAC `a:real` THEN
        EXISTS_TAC `x:real` THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN asm_conv_tac_real_field;
        REPEAT STRIP_TAC THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m:real` THEN CONJ_TAC THENL
           [ASM_SIMP_TAC []; ALL_TAC] THEN
          SUBGOAL_THEN `(m:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
           [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
          UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
          DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []]];
      SUBGOAL_THEN `real_interval [a,m]= {}` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC [REAL_LE_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [a,x]) f) =
     ( ( real_integral (real_interval [a,x])  (\t. &0) ) <=
        real_integral (real_interval [a,x]) f )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []]];
    ALL_TAC] THEN
  GEN_TAC THEN MP_TAC (SPECL [`a:real`; `x:real`] REAL_LET_TOTAL) THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a:real` THEN
      ASM_SIMP_TAC [];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `abs (real_integral (real_interval [a,x]) f) =
    (real_integral (real_interval [a,x]) f)`
      ASSUME_TAC THENL
     [REWRITE_TAC [REAL_ABS_REFL] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [a,x]) f) =
     ( ( real_integral (real_interval [a,x])  (\t. &0) ) <=
        real_integral (real_interval [a,x]) f )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `real_integral (real_interval [a,x]) (f:real->real) =
    (\t.real_integral (real_interval [a,t]) f ) x`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(\t. real_integral  (real_interval [a,t]) g) x` THEN CONJ_TAC THENL
     [SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= x` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC []];
      ALL_TAC] THEN
    MATCH_MP_TAC SEQ_MONO_LE THEN CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC
        `!e. &0 < e ==> (?b. !x. x >= b
       ==> abs (real_integral (real_interval [a,x]) g - k) < e)` THEN
      ASM_REWRITE_TAC [GSYM REALLIM_AT_POSINFINITY]] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
    MP_TAC (SPECL [`a:real`; `n:real`] REAL_LET_TOTAL) THEN REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
        `real_integral (real_interval [a,m]) (g:real->real) =
     real_integral (real_interval [a,n]) g +
       real_integral (real_interval [n,m]) g`
        ASSUME_TAC THENL
       [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_LE_ADDR] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [n,m]) g) =
  ( ( real_integral (real_interval [n,m])  (\t. &0) ) <=
    real_integral (real_interval [n,m]) g )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `!b. g real_integrable_on real_interval [a,b]` THEN
        DISCH_THEN (MP_TAC o SPEC `m:real`) THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN EXISTS_TAC `a:real` THEN
        EXISTS_TAC `m:real` THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN DISJ2_TAC THEN
        ASM_SIMP_TAC [] THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
        SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `n:real` THEN CONJ_TAC THENL
           [ASM_SIMP_TAC []; ALL_TAC] THEN
          SUBGOAL_THEN `(n:real) <= x'  /\ x' <= m` ASSUME_TAC THENL
           [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
          UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
          DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC [] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `(f:real->real) x'` THEN ASM_SIMP_TAC []]];
      SUBGOAL_THEN `real_interval [a,n]= {}` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC [REAL_LE_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
      SUBGOAL_THEN
        `(&0 <= real_integral (real_interval [a,m]) g) =
   ( ( real_integral (real_interval [a,m])  (\t. &0) ) <=
      real_integral (real_interval [a,m]) g )`
        ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
       [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= m` ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
        UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
        DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC [] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(f:real->real) x'` THEN ASM_SIMP_TAC []]];
    SUBGOAL_THEN `real_interval [a,x]= {}` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
    SIMP_TAC [REAL_ARITH `abs(&0) = &0`] THEN
    MP_TAC (SPECL [`k:real`; `&0`] REAL_LTE_TOTAL) THEN STRIP_TAC THEN
    MATCH_MP_TAC (REAL_ARITH `~(k < &0) ==> (&0 <= k)`) THEN ASM_SIMP_TAC [] THEN
    UNDISCH_TAC
      `!e. &0 < e ==> (?b. !x. x >= b
       ==> abs (real_integral (real_interval [a,x]) g - k) < e)` THEN
    DISCH_THEN (MP_TAC o SPEC `abs( k :real)/ &2`) THEN
    ASM_SIMP_TAC [REAL_ARITH `( (x < &0) ==> (&0 < (abs(x) / &2)) )`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC
      `!x. x >= b ==> abs (real_integral (real_interval [a,x]) g - k) <  abs k / &2` THEN
    DISCH_THEN (MP_TAC o SPEC `b:real`) THEN
    ASM_REWRITE_TAC [REAL_ARITH `x >= x`] THEN REWRITE_TAC [REAL_NOT_LT] THEN
    MP_TAC (SPECL [`b:real`; `a:real`] REAL_LTE_TOTAL) THEN STRIP_TAC THENL
     [SUBGOAL_THEN `real_interval [a,b]= {}` ASSUME_TAC THENL
       [REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN ASM_SIMP_TAC [];
        ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_INTEGRAL_EMPTY] THEN
        SIMP_TAC [REAL_ARITH `abs(&0 - k) = abs(k)`] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `(x:real) - y = x + --y`] THEN
    SUBGOAL_THEN `--k = abs(k)` ASSUME_TAC THENL
     [MATCH_MP_TAC (REAL_ARITH `(k < &0) ==> (--k = abs(k))`) THEN
      ASM_SIMP_TAC [];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `real_integral (real_interval [a,b]) g =  
    abs(real_integral (real_interval [a,b]) g)`
      ASSUME_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN
        `abs (real_integral (real_interval [a,b]) g + abs k) = 
     abs (abs(real_integral (real_interval [a,b]) g) + abs k)`
        ASSUME_TAC THENL
       [ASM_MESON_TAC []; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN
      SIMP_TAC [REAL_ARITH `abs( abs(x) + abs(y)) = abs(x) + abs(y)`] THEN
      SIMP_TAC [REAL_ARITH `(abs(x) / &2) <= ( abs(y) + abs(x))`]] THEN
    MATCH_MP_TAC (REAL_ARITH `(&0 <= x) ==> (x = abs(x))`) THEN
    SUBGOAL_THEN
      `(&0 <= real_integral (real_interval [a,b]) g) =
     ( ( real_integral (real_interval [a,b])  (\t. &0) ) <=
        real_integral (real_interval [a,b]) g )`
      ASSUME_TAC THENL
     [REWRITE_TAC [REAL_INTEGRAL_0]; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_INTEGRABLE_0]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC []; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [] THEN SUBGOAL_THEN `(a:real) <= x'` ASSUME_TAC THENL
     [SUBGOAL_THEN `(a:real) <= x'  /\ x' <= b` ASSUME_TAC THENL
       [ASM_MESON_TAC [IN_REAL_INTERVAL]; ASM_SIMP_TAC []];
      UNDISCH_TAC `!x. a <= x ==> &0 <= f x /\ f x <= g x` THEN
      DISCH_THEN (MP_TAC o SPEC `(x' :real)`) THEN ASM_SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(f:real->real) x'` THEN ASM_SIMP_TAC []]]);;

(*---------------------------------------------------------------------------*)
(*     Some useful theorems regarding to integration and differentiation     *)
(*---------------------------------------------------------------------------*)

let HAS_INTEGRAL_COMPLEX_MUL = prove
 (`!(f:real^1->complex) (k:complex) s (c:complex) .
      (f has_integral k) s ==> ((\x. z * (f(x) )) has_integral (z * k)) s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE [o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC [linear] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [COMPLEX_CMUL]] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let INTEGRAL_COMPLEX_MUL = prove
 (`!f:real^1->complex c s.
     f integrable_on s ==> integral s (\x. c * f(x)) = c * integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_MUL THEN
  ASM_SIMP_TAC [INTEGRABLE_INTEGRAL]);;

let INTEGRABLE_COMPLEX_MUL = prove
 (`!f:real^1->complex c s.
     f integrable_on s ==> (\x. c * f(x)) integrable_on s`,
  REWRITE_TAC [integrable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `c * (y:real^2)` THEN MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_MUL THEN
  ASM_SIMP_TAC []);;

let CX_HAS_REAL_INTERGRAL = prove
 (`! (f:real->real) (s:complex) (t:real)(l:real).
    (f has_real_integral l) (real_interval [(&0),t])
     ==> ((\t:real^1. Cx (f (drop t ) ) ) has_integral Cx l) (interval [lift (&0),lift t])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `(f has_real_integral (l ) ) (real_interval [(&0),t]) <=>
       ((\t. lift (f (drop t))) has_integral lift ( l))
         (interval [lift (&0),lift t])`
    ASSUME_TAC THENL
   [REWRITE_TAC [has_real_integral] THEN REWRITE_TAC [o_DEF] THEN
    REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN REWRITE_TAC [LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [has_integral] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(e:real)`) THEN ASM_SIMP_TAC [] THEN
  STRIP_TAC THEN EXISTS_TAC `(d:real^1->real^1->bool)` THEN ASM_SIMP_TAC [] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `(p:real^1#(real^1->bool)->bool)`) THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM LIFT_CMUL] THEN STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_CMUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  SUBGOAL_THEN
    `( (vsum (p:real^1#(real^1->bool)->bool)
   (\ (a:real^1#(real^1->bool)) . Cx ( (\ (a:real^1#(real^1->bool)). content (SND a) * f (drop (FST a) ))a ) ) ) = 
    (Cx (sum p (\ (a:real^1#(real^1->bool)). content (SND a) * (f:real->real) (drop (FST a)) ) ) ))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_CX2 THEN MATCH_MP_TAC TAGGED_DIVISION_OF_FINITE THEN
    EXISTS_TAC `interval [lift (&0),lift t]` THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\ (x,k). Cx ((\ (x:real^1,k:(real^1->bool)). content k * f (drop x) ) (x , k))) =
    (\(a:real^1#(real^1->bool)). Cx ((\a. content (SND a) * (f:real->real)  (drop (FST a) ) ) a))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [FUN_EQ_THM_PAIR] THEN GEN_TAC THEN
    SUBGOAL_THEN
      `(\(a:real^1#(real^1->bool)). Cx ((\a. content (SND a) *  (f:real->real) (drop (FST a) )) a)) x = 
    ( (\a. Cx ((\a. content (SND a) * f (drop (FST a)) ) a)) (FST x , SND x) )`
      ASSUME_TAC THENL
     [SIMP_TAC [FST; SND; PAIR]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\(x,k). Cx ((\(x,k). content k * (f:real->real) (drop x) ) (x,k))) (x:real^1#(real^1->bool)) = 
   ((\ (x,k). Cx ((\ (x,k). content k * f (drop x) ) (x,k))) (FST x , SND x) )`
      ASSUME_TAC THENL
     [PURE_ONCE_REWRITE_TAC [PAIR] THEN SIMP_TAC [];
      PURE_ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [FST; SND]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `vsum p (\ (x:real^1,k:real^1->bool). Cx (content k * (f:real->real) (drop x) )) =
    vsum p (\ (x,k). Cx ((\ (x,k). content k * f (drop x) ) (x,k)))`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  PURE_ONCE_ASM_REWRITE_TAC [] THEN PURE_ONCE_ASM_REWRITE_TAC [] THEN
  PURE_ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  REWRITE_TAC [COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN
    `( (vsum (p:real^1#(real^1->bool)->bool)
    (\ (a:real^1#(real^1->bool)) . lift ( (\ (a:real^1#(real^1->bool)). content (SND a) * f (drop (FST a) ) )a ) ) ) = 
     (lift (sum p (\ (a:real^1#(real^1->bool)). content (SND a) * (f:real->real) (drop (FST a)) ) ) ))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_LIFT2 THEN MATCH_MP_TAC TAGGED_DIVISION_OF_FINITE THEN
    EXISTS_TAC `interval [lift (&0),lift t]` THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\ (x,k). lift ((\ (x:real^1,k:(real^1->bool)). content k * f (drop x) ) (x , k))) =
     (\(a:real^1#(real^1->bool)). lift ((\a. content (SND a) * (f:real->real)  (drop (FST a))) a))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [FUN_EQ_THM_PAIR] THEN GEN_TAC THEN
    SUBGOAL_THEN
      `(\(a:real^1#(real^1->bool)). lift ((\a. content (SND a) *  (f:real->real) (drop (FST a) )) a)) x = 
    ( (\a. lift ((\a. content (SND a) * f (drop (FST a))) a)) (FST x , SND x) )`
      ASSUME_TAC THENL
     [SIMP_TAC [FST; SND; PAIR]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\(x,k). lift ((\(x,k). content k * (f:real->real) (drop x) ) (x,k))) (x:real^1#(real^1->bool)) = 
   ((\ (x,k). lift ((\ (x,k). content k * f (drop x)) (x,k))) (FST x , SND x) )`
      ASSUME_TAC THENL
     [PURE_ONCE_REWRITE_TAC [PAIR] THEN SIMP_TAC [];
      PURE_ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [FST; SND]];
    SUBGOAL_THEN
      `vsum p (\ (x:real^1,k:real^1->bool). lift (content k * (f:real->real) (drop x) )) =
    vsum p (\ (x,k). lift ((\ (x,k). content k * f (drop x) ) (x,k)))`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    UNDISCH_TAC
      `norm (vsum (p:real^1#(real^1->bool)->bool)
     (\(x:real^1,k:real^1->bool). lift (content k *  (f:real->real) (drop x) )) - lift (l)) < e` THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN PURE_ONCE_ASM_REWRITE_TAC [] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM LIFT_SUB] THEN
    REWRITE_TAC [NORM_LIFT]]);;

let HAS_COMPLEX_INTEGRAL_CMUL = prove
  (`!(f:real^1->complex) k s c:complex.
   (f has_integral k) s  ==> ((\x. c * f(x)) has_integral (c * k)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[linear] THEN REWRITE_TAC[COMPLEX_CMUL] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let COMPLEX_INTEGRAL_CMUL = prove
  (`!f:real^1->complex c s.  f integrable_on s ==> integral s (\x. c * f(x)) = c * integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_COMPLEX_INTEGRAL_CMUL THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let  VECTOR_COMPLEX_DIFF_CHAIN_WITHIN = prove
 (`!(f:real^1->complex) (g:complex->complex) (f':complex) (g':complex) x s .
      (f has_vector_derivative f') (at x within s) /\
       (g has_complex_derivative g') (at (f x) within IMAGE f s)
         ==> ((g o f) has_vector_derivative (f' * g')) (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [has_vector_derivative; has_complex_derivative] THEN
  DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC [o_DEF; COMPLEX_CMUL; COMPLEX_MUL_AC]);;

let HAS_CX_FRECHET_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((Cx o f o drop) has_derivative (\x . f' % Cx (drop x ) ))
        (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC [has_derivative_within; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  REWRITE_TAC [o_THM; LIFT_DROP; LIM_WITHIN; REALLIM_WITHINREAL] THEN
  SUBGOAL_THEN `linear (\x. f' % Cx (drop x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN SIMP_TAC [linear] THEN
    SIMP_TAC [DROP_ADD; CX_ADD] THEN SIMP_TAC [DROP_CMUL; CX_CMUL];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [IMP_CONJ] THEN
  REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [DIST_LIFT] THEN
  REWRITE_TAC [GSYM LIFT_SUB] THEN REWRITE_TAC [LIFT_DROP] THEN
  REWRITE_TAC [NORM_ARITH `dist(x,vec 0) = norm x`] THEN
  REWRITE_TAC [NORM_LIFT] THEN REWRITE_TAC [CX_CMUL] THEN
  REWRITE_TAC [GSYM CX_ADD] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  REWRITE_TAC [CX_CMUL] THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
  SIMP_TAC
    [REAL_FIELD
       `&0 < abs(y - x)
    ==> fy - (fx + f' * (y - x)) = (y - x) * ((fy - fx) / (y - x) - f')`] THEN
  REWRITE_TAC [REAL_ABS_MUL; REAL_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_ABS] THEN
  SIMP_TAC [REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_MUL_LID]);;

let HAS_CX_VECTOR_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((Cx o f o drop) has_vector_derivative (Cx f'))(at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC [has_vector_derivative; HAS_CX_FRECHET_DERIVATIVE_WITHIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM; CX_CMUL; REAL_MUL_SYM]);;

let VECTOR_COMPLEX_DIFF_CHAIN_AT = prove
 (`!(f:real^1->complex) (g:complex->complex) (f':complex) (g':complex) x .
         (f has_vector_derivative f') (at x) /\
         (g has_complex_derivative g') (at (f x))
         ==> ((g o f) has_vector_derivative (f' * g')) (at x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [has_vector_derivative; has_complex_derivative] THEN
  DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN_AT) THEN
  REWRITE_TAC [o_DEF; COMPLEX_CMUL; COMPLEX_MUL_AC]);;

let HAS_CX_FRECHET_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x) <=>
      ((Cx o f o drop) has_derivative (\x . f' % Cx (drop x ) ))(at (lift x))`,
  ONCE_REWRITE_TAC [GSYM WITHINREAL_UNIV; GSYM WITHIN_UNIV] THEN
  REWRITE_TAC [HAS_CX_FRECHET_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC [IMAGE_LIFT_UNIV]);;

let HAS_CX_VECTOR_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x ) <=>
        ((Cx o f o drop) has_vector_derivative (Cx f'))
        (at (lift x))`,
  REWRITE_TAC [has_vector_derivative; HAS_CX_FRECHET_DERIVATIVE_AT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM; CX_CMUL; REAL_MUL_SYM]);;

let HAS_VECTOR_DERIVATIVE_EQUAL = prove
 (`! (f:real^1->complex) (g:real^1->complex) t:real^1. (&0 < (drop t) ) /\ 
   (!t. (&0 < (drop t) ) ==> f t = g t) /\
   (f has_vector_derivative (vector_derivative f (at t))) (at t) ==>
   (g has_vector_derivative (vector_derivative f (at t))) (at t)`,
  REWRITE_TAC [has_vector_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `f:real^1->complex` THEN EXISTS_TAC `drop t / &2` THEN
  ASM_SIMP_TAC [] THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < drop t` THEN
    SIMP_TAC [REAL_ARITH `&0 < a ==> &0 < (a / &2)`];
    ALL_TAC] THEN
  REWRITE_TAC [dist] THEN
  REWRITE_TAC
    [GSYM ABS_DROP; GSYM REAL_BOUNDS_LT; DROP_SUB;
     REAL_ARITH `(--(a / &2) < b - a) <=> a / &2 < b`] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 < drop (x')` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `drop t / &2` THEN
    ASM_SIMP_TAC [] THEN UNDISCH_TAC `&0 < drop t` THEN
    SIMP_TAC [REAL_ARITH `&0 < a ==> &0 < (a / &2)`];
    UNDISCH_TAC `!t. &0 < drop t ==> (f:real^1->complex) t = g t` THEN
    DISCH_THEN (MP_TAC o SPEC `x':real^1`) THEN ASM_SIMP_TAC []]);;

let VECTOR_DERIVATIVE_EQUAL = prove
 (`! (f:real^1->complex) (g:real^1->complex) t:real^1. (&0 < (drop t) ) /\ (!t. (&0 < (drop t) ) ==> f t = g t) /\
   (f has_vector_derivative (vector_derivative f (at t))) (at t) /\
   (g has_vector_derivative (vector_derivative g (at t))) (at t) ==>
   (vector_derivative f (at t) =  vector_derivative g (at t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `f:real^1->complex` THEN EXISTS_TAC `t:real^1` THEN
  ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [HAS_VECTOR_DERIVATIVE_EQUAL]);;

let VECTOR_DERIVATIVE_NEG = prove
 (`!f:real^1->complex x:real^1. f differentiable (at x) 
    ==>( vector_derivative (\x. --f x) (at x) = --vector_derivative f  (at x))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `--x = Cx(&1) * --x`] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `Cx(&1) * --x = --Cx(&1) * x`] THEN
  REWRITE_TAC [GSYM CX_NEG; GSYM COMPLEX_CMUL] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC []);;

let INTEGRAL_DIFF_EQ = prove
 (`!(lst1:(real^1->complex) list)(lst2:(real^1->complex) list)
   (f1:real^1->complex) (n1:num)(x:real^1) (f2:real^1->complex) (n2:num) . 
   (!x. diff_eq_n lst1 f1 n1 x = diff_eq_n lst2 f2 n2 x) ==> 
     integral (interval [lift(&0) , x]) ( \x. diff_eq_n lst1 f1 n1 x) = 
     integral(interval [lift(&0) , x]) (\x. diff_eq_n lst2 f2 n2 x)`,
  ASM_SIMP_TAC []);;

let VECTOR_DERIVATIVE_SUB = prove
 (`!f:real^1->complex g x. f differentiable (at x) /\ g differentiable (at x)
    ==> vector_derivative (\x. f x - g x) (at x) = (vector_derivative f  (at x))  - (vector_derivative g (at x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
  REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC []);;

let VECTOR_DERIVATIVE_ADD = prove
 (`!f:real^1->complex g x. f differentiable (at x) /\ g differentiable (at x)
    ==> vector_derivative (\x. f x + g x) (at x) = (vector_derivative f  (at x))  + (vector_derivative g (at x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC []);;

let VECTOR_DERIVATIVE_CMUL = prove
 (`!f:real^1->complex c x. f differentiable (at x)
    ==> vector_derivative (\x. c % f x) (at x) =  c % (vector_derivative f  (at x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC []);;

let BILINEAR_X_MUL_Y = prove
 (`bilinear (\x y. x * y)`,
  REWRITE_TAC [bilinear] THEN CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC [linear] THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [COMPLEX_CMUL]; ALL_TAC; REWRITE_TAC [COMPLEX_CMUL]] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let INTEGRATION_BY_PARTS_WITHIN = prove
 (`!(f:real^1->complex) (g:real^1->complex) f' g' a:real^1 b:real^1 .  drop a <= drop b /\
    (!x. drop (a) <= drop(x) /\ drop(x) <= drop(b) ==> (f  has_vector_derivative f'(x)) (at x within interval [a,b]) ) /\
      (!x. drop(a) <= drop(x) /\ drop(x) <= drop(b) ==> (g  has_vector_derivative g'(x)) (at x within interval [a,b]) )  ==>
      ( (\x. f'(x) * g(x) + f(x) * g'(x)) has_integral (f(b) * g(b) - f(a) * g(a) )) (interval [a , b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(a:complex) + (b:complex) = b + a`] THEN
  SUBGOAL_THEN
    `((\x. (\x y . x * y) ((f:real^1->complex) x) ((g:real^1->complex) x))has_vector_derivative
   ((\x y . x * y) (f x) ((g':real^1->complex) x) + (\x y . x * y) ((f':real^1->complex) x) (g x))) (at x within interval [a,b])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN THEN
    SUBGOAL_THEN `drop a <= drop x /\ drop x <= drop b` ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_INTERVAL_1];
      ASM_SIMP_TAC [] THEN REWRITE_TAC [BILINEAR_X_MUL_Y]];
    SUBGOAL_THEN
      `(f:real^1->complex) x * (g':real^1->complex) x + f' x * (g:real^1->complex) x =
   (\x y. x * y) (f x) (g' x) + (\x y. x * y) ((f':real^1->complex) x) (g x)`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!a. (f:real^1->complex) a * (g:real^1->complex) a = (\x y. x * y) (f a) (g a)`
      ASSUME_TAC THENL
     [SIMP_TAC []; PURE_ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC []]]);;

let INTEGRAL_BY_PARTS_WITHIN = prove
 (`!(f:real^1->complex) (g:real^1->complex) f' g' a:real^1 b:real^1 .  drop a <= drop b /\
   (!x. drop (a) <= drop(x) /\ drop(x) <= drop(b) ==> (f  has_vector_derivative f'(x)) (at x within interval [a,b]) ) /\
    (!x. drop(a) <= drop(x) /\ drop(x) <= drop(b) ==> (g  has_vector_derivative g'(x)) (at x within interval [a,b]) )  
      /\  (\x. f' x * g x) integrable_on  (interval [a,b]) /\ (\x. f x * g' x) integrable_on  (interval [a,b]) ==>
       (integral (interval [a , b])  (\x. f x * g' x) =
             (f b * g b - f a * g a) - integral (interval [a , b])(\x. f' x * g x))`,
  MP_TAC INTEGRATION_BY_PARTS_WITHIN THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x:complex = y - z) <=> (x + z = y)`] THEN
  SIMP_TAC [GSYM INTEGRAL_ADD] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x + z = y) <=> (x:complex = y - z)`] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN PURE_ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
  FIRST_X_ASSUM
    (MP_TAC o
     SPECL
       [`(f:real^1->complex)`; `(g:real^1->complex)`; `(f':real^1->complex)`;
        `(g':real^1->complex)`; `a:real^1`; `b:real^1`]) THEN
  ASM_SIMP_TAC []);;

let INTEGRATION_BY_PARTS_AT = prove
 (`!(f:real^1->complex) (g:real^1->complex) f' g' a:real^1 b:real^1 .  drop a <= drop b /\ (!x.(f  has_vector_derivative f'(x)) (at x ))  /\
   (!x.(g  has_vector_derivative g'(x)) (at x) )  ==> ((\x. f'(x) * g(x) + f(x) * g'(x)) has_integral (f(b) * g(b) - f(a) * g(a) )) 
     (interval [a , b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(a:complex) + (b:complex) = b + a`] THEN
  SUBGOAL_THEN
    `((\x. (\x y . x * y) ((f:real^1->complex) x) ((g:real^1->complex) x)) has_vector_derivative
    ((\x y . x * y) (f x) ((g':real^1->complex) x) + (\x y . x * y) ((f':real^1->complex) x) (g x))) (at x within interval [a,b])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN THEN
    SUBGOAL_THEN `drop a <= drop x /\ drop x <= drop b` ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_INTERVAL_1]; ALL_TAC] THEN
    SUBGOAL_THEN
      `((f:real^1->complex) has_vector_derivative f' x) (at x within interval [a,b])`
      ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC [];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `((g:real^1->complex) has_vector_derivative g' x) (at x within interval [a,b])`
      ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC [];
      ASM_SIMP_TAC [] THEN REWRITE_TAC [BILINEAR_X_MUL_Y]];
    SUBGOAL_THEN
      `(f:real^1->complex) x * (g':real^1->complex) x + f' x * (g:real^1->complex) x =
   (\x y. x * y) (f x) (g' x) + (\x y. x * y) ((f':real^1->complex) x) (g x)`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!a. (f:real^1->complex) a * (g:real^1->complex) a = (\x y. x * y) (f a) (g a)`
      ASSUME_TAC THENL
     [SIMP_TAC []; PURE_ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC []]]);;

let INTEGRAL_BY_PARTS_AT = prove
 (`!(f:real^1->complex) (g:real^1->complex) f' g' a:real^1 b:real^1 .  drop a <= drop b /\
    (!x.  (f  has_vector_derivative f'(x)) (at x) )  /\ (!x. (g  has_vector_derivative g'(x)) (at x) )  
     /\  (\x. f' x * g x) integrable_on  (interval [a,b]) /\ (\x. f x * g' x) integrable_on  (interval [a,b]) ==>
      (integral (interval [a , b])  (\x. f x * g' x) = (f b * g b - f a * g a) - integral (interval [a , b])(\x. f' x * g x))`,
  MP_TAC INTEGRATION_BY_PARTS_AT THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x:complex = y - z) <=> (x + z = y)`] THEN
  SIMP_TAC [GSYM INTEGRAL_ADD] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x + z = y) <=> (x:complex = y - z)`] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN PURE_ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
  FIRST_X_ASSUM
    (MP_TAC o
     SPECL
       [`(f:real^1->complex)`; `(g:real^1->complex)`; `(f':real^1->complex)`;
        `(g':real^1->complex)`; `a:real^1`; `b:real^1`]) THEN
  ASM_SIMP_TAC []);;

let INTEGRAL_BY_SUBSTITUTION_LINEAR = prove
 (`!(f:real^1->complex)(f':real^1->complex) (a:real^1) (b:real^1) (c:real^1). (drop a <=drop b) /\ (&0 <= drop c) /\
    (!x. (f has_vector_derivative (f' x))(at x within interval [(\x. x - c) a , (\x. x- c) b])) 
      ==> ((integral (interval[(\x. x - c) a,(\x. x - c) b]) f') = (integral (interval [a,b])
        (\x. (drop ((\x:real^1. lift(&1)) x)) %  f' ((\x. x - c) x)    )) )`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
    `((\x.  (drop ( (\x. lift (&1)) x) % (f':real^1->complex) ((\x. x - c) x))  ) has_integral 
   ((\x. (f:real^1->complex) ((\x. x - c) x)) b - (\x. f ((\x. x - c) x)) a)  )(interval [a,b])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC VECTOR_DIFF_CHAIN_WITHIN THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `lift(&1) = lift(&1) - vec 0` ASSUME_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
      REWRITE_TAC [GSYM LIFT_VEC_1] THEN
      SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST; HAS_VECTOR_DERIVATIVE_ID];
      SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM INTERVAL_TRANSLATION_1] THEN
      ASM_SIMP_TAC []];
    SUBGOAL_THEN
      `integral (interval [a,b]) (\x. drop  ((\x. lift (&1)) x) % (f':real^1->complex) ((\x. x - c) x) ) = 
   ((\x. f ((\x. x - c) x)) b - (\x. f ((\x. x - c) x)) a )`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN CONJ_TAC THENL
     [SIMP_TAC [DROP_SUB] THEN MATCH_MP_TAC REAL_LE_ADD21 THEN
      ASM_SIMP_TAC [];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC
        `!x. ((f:real^1->complex) has_vector_derivative f' x)(at x within interval [(\x. x - c) a,(\x. x - c) b])` THEN
      SIMP_TAC []]]);;

let INTEGRAL_BY_SUBSTITUTION_LINEAR_1 = prove
 (`!(f:real^1->complex)(f':real^1->complex)(a:real^1) (b:real^1) (c:real^1). (drop a <=drop b) /\ (&0 <= drop c) /\
    (!x.  x IN interval [(\x. x - c) a , (\x. x- c) b] ==> (f has_vector_derivative (f' x))(at x within interval [(\x. x - c) a , (\x. x- c) b])) 
      ==> ((integral (interval[(\x. x - c) a,(\x. x - c) b]) f') = (integral (interval [a,b]) (\x. (drop ((\x:real^1. lift(&1)) x)) %  f' ((\x. x - c) x)    )) )`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
    `((\x.  (drop ( (\x. lift (&1)) x) % (f':real^1->complex) ((\x. x - c) x))  ) has_integral 
   ((\x. (f:real^1->complex) ((\x. x - c) x)) b - (\x. f ((\x. x - c) x)) a) )(interval [a,b])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC VECTOR_DIFF_CHAIN_WITHIN THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `lift(&1) = lift(&1) - vec 0` ASSUME_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
      REWRITE_TAC [GSYM LIFT_VEC_1] THEN
      SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST; HAS_VECTOR_DERIVATIVE_ID];
      SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM INTERVAL_TRANSLATION_1] THEN
      UNDISCH_TAC
        `!x. x IN interval [(\x. x - c) a,(\x. x - c) b] ==>((f:real^1->complex) has_vector_derivative f' x)
    (at x within interval [(\x. x - c) a,(\x. x - c) b])` THEN
      SIMP_TAC [] THEN DISCH_THEN (MP_TAC o SPEC `x:real^1 - c`) THEN
      REWRITE_TAC [IN_INTERVAL_1; DROP_SUB] THEN
      SUBGOAL_THEN `drop a - drop c <= drop x - drop c` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD21;
        SUBGOAL_THEN `drop x - drop c <= drop b - drop c` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_ADD21; ALL_TAC]] THEN
      ASM_SIMP_TAC []];
    SUBGOAL_THEN
      `integral (interval [a,b]) (\x. drop  ((\x. lift (&1)) x) % (f':real^1->complex) ((\x. x - c) x) ) = 
   ((\x. f ((\x. x - c) x)) b - (\x. f ((\x. x - c) x)) a )`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN CONJ_TAC THENL
     [SIMP_TAC [DROP_SUB] THEN MATCH_MP_TAC REAL_LE_ADD21 THEN
      ASM_SIMP_TAC [];
      UNDISCH_TAC
        `!x. x IN interval [(\x. x - c) a,(\x. x - c) b] ==>((f:real^1->complex) has_vector_derivative f' x)
    (at x within interval [(\x. x - c) a,(\x. x - c) b])` THEN
      SIMP_TAC []]]);;

let INTEGRAL_NORM_BOUND_INTEGRAL_SPEC = prove
 (`!f:real^M->real^N g:real^M->real^1 s. f integrable_on s /\ g integrable_on s /\
     (!x. x IN s ==> norm(f x) <= drop(g x))  ==> norm(integral s f) <= abs(drop(integral s g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(drop (integral s (g:real^M->real^1)))` THEN CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_SIMP_TAC []);;

let VECTOR_DERIVATIVE_SUB = prove
 (`!f:real^1->complex g x. f differentiable (at x) /\ g differentiable (at x)
    ==> vector_derivative (\x. f x - g x) (at x) = (vector_derivative f  (at x))  - (vector_derivative g (at x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
  REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC []);;

let INTEGRAL_NORM_BOUND_INTEGRAL_SPEC = prove
 (`!f:real^M->real^N g:real^M->real^1 s.  f integrable_on s /\ g integrable_on s /\  (!x. x IN s ==> norm(f x) <= drop(g x))
     ==> norm(integral s f) <= abs(drop(integral s g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(drop (integral s (g:real^M->real^1)))` THEN CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_SIMP_TAC []);;

(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    Formalization of Laplace Transform                     *)
(*---------------------------------------------------------------------------*)

let laplace_transform = new_definition
  `laplace_transform (f:real^1->complex) (s:complex) = 
     integral {t | &0 <= drop t}
         (\t. (cexp (-- (s * Cx (drop t))) * (f t) ))`;;
		 
let exp_order_comp = new_definition
 `exp_order_comp (f:real^1->complex) M a = 
     ((&0 < M) /\
     (!t. &0 <= t
    ==> (norm (f (lift t ))  <= (M * exp (drop a * t))) ) )`;;

let laplace_exists = new_definition
   `laplace_exists (f:real^1->complex) s = 
   ((!b. (f piecewise_differentiable_on interval [lift (&0),lift b])) /\
   (?(M:real) a. (Re s > drop a) /\ (exp_order_comp f M a)) )`;;

(*---------------------------------------------------------------------------*)
(*                          Some useful theorems                             *)
(*---------------------------------------------------------------------------*)

let CEXP_S_T_CONTINUOUS_ALT = prove
 (`!(s:complex) (a:real) (b:real).
 (\t. cexp (--(s * Cx (drop t)))) continuous_on interval [lift a, lift b]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  REWRITE_TAC [CONTINUOUS_ON_CX_DROP1]);;

let CEXP_S_T_CONTINUOUS = prove
 (`! (s:complex) (b:real^1).
      (\t. cexp (--(s * Cx (drop t)))) continuous_on interval [lift (&0),b]`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`s:real^2`; `&0`; `(drop b)`] CEXP_S_T_CONTINUOUS_ALT) THEN
  SIMP_TAC [LIFT_DROP]);;

let LAPLACE_EXISTS_INTEGRABLE = prove
 (`!(f:real^1->complex) (s:complex) (b:real).
     laplace_exists f s ==> 
       (\ (t:real^1).( cexp(--(s * Cx (drop t))) * (f t))) integrable_on
        interval [lift (&0),lift b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS] THEN
  ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON]);;

let LAPLACE_EXISTS_INTEGRABLE_ABS = prove
 (`!(f:real^1->complex) s b.
     laplace_exists f s ==> 
      (\t. lift (norm (cexp(--(s * Cx (drop t))) * (f t)) )) integrable_on
       interval [lift (&0),lift b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [LIFT_CMUL] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM o_DEF] THEN
    SUBGOAL_THEN
      `lift o norm o (\t. cexp (--(s * Cx (drop t))))=
    (lift o norm) o (\t. cexp (--(s * Cx (drop t))))`
      ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CEXP_S_T_CONTINUOUS] THEN
    ONCE_REWRITE_TAC [CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC [GSYM o_DEF] THEN
    SUBGOAL_THEN `!(f:real^1->complex). lift o norm o f= (lift o norm) o f`
      ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
    ASM_SIMP_TAC [PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON]]);;

let LAPLACE_EXISTS_INTEGRABLE_ABS_ALT = prove
 (`!(f:real^1->complex) (s:complex)(a:real) (b:real).
    laplace_exists f s  /\ a <= b /\ &0 <= a ==> 
     (\t. lift (norm (cexp (--(s * Cx (drop t))) * (f t)) )) integrable_on
        interval [lift a, lift b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [LIFT_CMUL] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THENL
   [SUBGOAL_THEN
      `lift o norm o (\t. cexp (--(s * Cx (drop t))))=
     (lift o norm) o (\t. cexp (--(s * Cx (drop t))))`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
      ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS_ALT];
        ONCE_REWRITE_TAC [CONTINUOUS_ON_LIFT_NORM]]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN `!(f:real^1->complex). lift o norm o f= (lift o norm) o f`
    ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
    SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_LIFT_NORM]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval [lift (&0),lift (b)]` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [SUBSET_INTERVAL] THEN STRIP_TAC THEN GEN_TAC THEN
  STRIP_TAC THEN SUBGOAL_THEN `i<=1` ASSUME_TAC THENL
   [UNDISCH_TAC `i <= dimindex (:1)` THEN ONCE_REWRITE_TAC [DIMINDEX_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= i /\ i <= 1` ASSUME_TAC THENL
   [CONJ_TAC THEN ONCE_ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `i=1` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= i /\ i <= 1` THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM drop] THEN
  ONCE_REWRITE_TAC [LIFT_DROP] THEN CONJ_TAC THENL
   [ONCE_ASM_SIMP_TAC []; ARITH_TAC]);;

let LAPLACE_EXISTS_INTEGRABLE_ALT = prove
 (`!(f:real^1->complex) (s:complex)(a:real)(b:real).
     laplace_exists f s   /\  (a) <= (b) /\ (&0) <= (a)  ==> 
      (\ (t:real^1).( cexp(--(s * Cx(drop(t)))) * (f t))) integrable_on interval [lift(a),lift(b)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS_ALT]; ALL_TAC] THEN
  REWRITE_TAC [INTEGRABLE_CONTINUOUS] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval [lift (&0),lift(b)]` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [SUBSET_INTERVAL] THEN STRIP_TAC THEN GEN_TAC THEN
  STRIP_TAC THEN SUBGOAL_THEN `i<=1` ASSUME_TAC THENL
   [UNDISCH_TAC `i <= dimindex (:1)` THEN ONCE_REWRITE_TAC [DIMINDEX_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= i /\ i <= 1` ASSUME_TAC THENL
   [CONJ_TAC THEN ONCE_ASM_SIMP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `i=1` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= i /\ i <= 1` THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM drop] THEN
  ONCE_REWRITE_TAC [LIFT_DROP] THEN CONJ_TAC THENL
   [ONCE_ASM_SIMP_TAC []; ARITH_TAC]);;

let CEXP_S_T_CONTINUOUS1 = prove
 (`! (s:complex) (t:real^1) (b:real).
     (\t. cexp (--(s * Cx (drop t)))) continuous_on interval [lift (&0),lift(b)]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(s * Cx(drop(t))))) =
		(\t. cexp ((\t. (--(s * Cx(drop(t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
  REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  REWRITE_TAC [CONTINUOUS_ON_CX_DROP1]);;

let CEXP_S_T_CONTINUOUS_COMPOSE = prove
 (`! (s:complex) (t:real^1) (b:real) (x:real).
    (\t. cexp (--(s * Cx t))) continuous atreal x within real_interval [&0,b]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!t. ( cexp (--(s * Cx((t))))) =
		(\t. cexp ((\t. (--(s * Cx((t))))) t)) t`
    ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
  REWRITE_TAC [REAL_CONTINUOUS_WITHIN_ID] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_WITHINREAL_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_WITHIN_CEXP] THEN
  REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN `(Cx x) = Cx (drop (lift x) )` ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_WITHIN THEN
  REWRITE_TAC [LINEAR_CX_DROP]);;

let PIECEWISE_CONTINUOUS_ON_IMAGE_LIFT = prove
 (`!(f:real^1->complex) b.
   (!a. f piecewise_differentiable_on interval [lift (&0),lift a])
   ==> (\x. (f:real^1->complex) x) continuous_on
    IMAGE lift (real_interval [&0,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC [CONTINUOUS_ON_ID] THEN
  REWRITE_TAC
    [SET_RULE
       `IMAGE (\x. x) (interval [lift (&0),lift b])
    = (interval [lift (&0),lift b])`] THEN
  MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
  ASM_SIMP_TAC []);;

let ABS_RE_REAL_LAPLACE_INTEGRABLE = prove
 (`! f:real^1->complex s:complex  b:real .
    laplace_exists f s ==>(\x. abs (Re (cexp (--(s * Cx x)) * f (lift x)))) real_integrable_on
        real_interval [&0 , b]`,
  REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN
    `abs o Re o (\x. cexp (--(s * Cx x)) * f (lift x)) =
   (abs o Re) o (\x. cexp (--(s * Cx x)) * (f:real^1->complex) (lift x))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    REWRITE_TAC [ABS_REAL_CONTINUOUS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
   f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [&0,b])`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [PIECEWISE_CONTINUOUS_ON_IMAGE_LIFT]; ALL_TAC] THEN
  REWRITE_TAC [CONTINUOUS_WITHIN] THEN
  UNDISCH_TAC
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
   (real_interval [&0,b])` THEN
  REWRITE_TAC [CONTINUOUS_ON] THEN
  DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
  ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN
  ASM_SIMP_TAC []);;
 
let ABS_IM_REAL_LAPLACE_INTEGRABLE = prove
 (`! f:real^1->complex s:complex  b:real .
  laplace_exists f s ==>
  (\x. abs (Im (cexp (--(s * Cx x)) * f (lift x)))) real_integrable_on real_interval [&0 , b]`,
  REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  SUBGOAL_THEN
    `abs o Im o (\x. cexp (--(s * Cx x)) * f (lift x)) =
   (abs o Im) o (\x. cexp (--(s * Cx x)) * (f:real^1->complex) (lift x))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_SIMP_TAC [] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    REWRITE_TAC [ABS_REAL_CONTINUOUS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
    f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
    (real_interval [&0,b])`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [PIECEWISE_CONTINUOUS_ON_IMAGE_LIFT]; ALL_TAC] THEN
  REWRITE_TAC [CONTINUOUS_WITHIN] THEN
  UNDISCH_TAC
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
    (real_interval [&0,b])` THEN
  REWRITE_TAC [CONTINUOUS_ON] THEN
  DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
  ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN
  ASM_SIMP_TAC []);;

let RE_REAL_LAPLACE_INTEGRABLE = prove
 (`! f:real^1->complex s:complex  b:real .
    laplace_exists f s ==> (\x. Re (cexp (--(s * Cx x)) * f (lift x))) real_integrable_on
      real_interval [&0 , b]`,
  REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
    f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
    (real_interval [&0,b])`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [PIECEWISE_CONTINUOUS_ON_IMAGE_LIFT]; ALL_TAC] THEN
  REWRITE_TAC [CONTINUOUS_WITHIN] THEN
  UNDISCH_TAC
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
    (real_interval [&0,b])` THEN
  REWRITE_TAC [CONTINUOUS_ON] THEN
  DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
  ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN
  ASM_SIMP_TAC []);;

let IM_REAL_LAPLACE_INTEGRABLE = prove
 (`! f:real^1->complex s:complex  b:real .
    laplace_exists f s ==>
     (\x. Im (cexp (--(s * Cx x)) * f (lift x))) real_integrable_on real_interval [&0 , b]`,
  REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
  REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE] THEN
  REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
  SUBGOAL_THEN
    `(f:real^1->complex) (lift x) = 
    f (lift (drop (lift x) ) )`
    ASSUME_TAC THENL
   [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
  REWRITE_TAC [LIFT_DROP] THEN
  SUBGOAL_THEN
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
        (real_interval [&0,b])`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [PIECEWISE_CONTINUOUS_ON_IMAGE_LIFT]; ALL_TAC] THEN
  REWRITE_TAC [CONTINUOUS_WITHIN] THEN
  UNDISCH_TAC
    `(\x. (f:real^1->complex) x) continuous_on IMAGE lift
        (real_interval [&0,b])` THEN
  REWRITE_TAC [CONTINUOUS_ON] THEN
  DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
  ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN ONCE_ASM_REWRITE_TAC [LIFT_DROP] THEN
  ASM_SIMP_TAC []);;

let LIM_LAPLACE_EXISTS = prove
 (`!(f:real^1->complex) (s:complex).
    laplace_exists f s ==> 
     (?l.( (\b. integral (interval [lift (&0),lift(b)] )
       (\t. (cexp (--(s * Cx (drop t))) * f t) ) ) -->  l)(at_posinfinity))`,
  let lemma1 = prove
     (`!t.  cexp (--(s * Cx (drop t))) * f t =
   Cx(Re(cexp (--(s * Cx (drop t))) * f t))  + ii *
       Cx(Im( cexp (--(s * Cx (drop t))) * f t))`,
      MESON_TAC [COMPLEX_EXPAND]) in
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_exists; exp_order_comp] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [lemma1] THEN
  SUBGOAL_THEN
    `!t.(integral (interval [lift (&0),lift t]) (\t. Cx (Re (cexp (--(s * Cx (drop t))) * f t)) +
     ii * Cx (Im (cexp (--(s * Cx (drop t))) * f t)))) =
      (integral (interval [lift (&0),lift t])
       (\t. Cx (Re (cexp (--(s * Cx (drop t))) * f t)) )) + 
      (integral (interval [lift (&0),lift t])
       (\t. ii * Cx (Im (cexp (--(s * Cx (drop t))) * f t))))`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_ADD THEN STRIP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THENL
     [REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `Cx o Re o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Re) o (\t. cexp (--(s * Cx (drop t))) * f t)`
        ASSUME_TAC THENL
       [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_RE]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS1];
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC []];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC [ii] THEN REWRITE_TAC [CONTINUOUS_ON_CONST]; ALL_TAC] THEN
      REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `Cx o Im o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Im) o (\t. cexp (--(s * Cx (drop t))) * f t)`
        ASSUME_TAC THENL
       [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_IM]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS1];
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC []]];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `!t. integral (interval [lift (&0),lift t])
   (\t. ii * Cx (Im (cexp (--(s * Cx (drop t))) * f t))) =
     ii * integral (interval [lift (&0),lift t])
     (\t. Cx (Im (cexp (--(s * Cx (drop t))) * f t)))`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN REWRITE_TAC [GSYM o_DEF] THEN
    SUBGOAL_THEN
      `Cx o Im o (\t. cexp (--(s * Cx (drop t))) * f t) =
    (Cx o Im) o (\t. cexp (--(s * Cx (drop t))) * f t)`
      ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC [CONTINUOUS_ON_CX_IM]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [CEXP_S_T_CONTINUOUS1];
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC []];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `! b . integral (interval [lift (&0),lift b])
    (\t. Cx (Re (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))) = 
     Cx( real_integral (real_interval [(&0), b])
      (\x:real. (\t. (Re (cexp (--(s * Cx (drop t))) * f t))) (lift x) )  )`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN
      `!t. (Re (cexp (--(s * Cx (drop t))) * f t)) = 
    (\t. (Re (cexp (--(s * Cx (t))) * f (lift t))) ) (drop t)`
      ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CX_HAS_REAL_INTERGRAL THEN
    SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE]; ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
    SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
      ASSUME_TAC THENL
     [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
    REWRITE_TAC [LIFT_DROP] THEN
    SUBGOAL_THEN
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
      ASSUME_TAC THENL
     [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC
        [SET_RULE
           `IMAGE (\x. x) (interval [lift (&0),lift b]) =
   (interval [lift (&0),lift b])`] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON;
      REWRITE_TAC [CONTINUOUS_WITHIN] THEN
      UNDISCH_TAC
        `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
      REWRITE_TAC [CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
      ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
      ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `! b . integral (interval [lift (&0),lift b])
    (\t. Cx (Im (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))) =
      Cx( real_integral (real_interval [(&0), b])
        (\x:real. (\t. (Im (cexp (--(s * Cx (drop t))) * f t))) (lift x) )  )`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN
      `!t. (Im (cexp (--(s * Cx (drop t))) * f t)) = 
    (\t. (Im (cexp (--(s * Cx (t))) * f (lift t))) ) (drop t)`
      ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    PURE_ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CX_HAS_REAL_INTERGRAL THEN
    SIMP_TAC [LIFT_DROP] THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN]] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE]; ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHINREAL] THEN
    REWRITE_TAC [LIM_WITHINREAL_WITHIN] THEN REWRITE_TAC [o_DEF] THEN
    SUBGOAL_THEN `(f:real^1->complex) (lift x) = f (lift (drop (lift x) ) )`
      ASSUME_TAC THENL
     [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM CONTINUOUS_WITHIN] THEN
    REWRITE_TAC [LIFT_DROP] THEN
    SUBGOAL_THEN
      `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])`
      ASSUME_TAC THENL
     [REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC
        [SET_RULE
           `IMAGE (\x. x) (interval [lift (&0),lift b]) =
   (interval [lift (&0),lift b])`] THEN
      MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON;
      REWRITE_TAC [CONTINUOUS_WITHIN] THEN
      UNDISCH_TAC
        `(\x. (f:real^1->complex) x) continuous_on IMAGE lift (real_interval [&0,b])` THEN
      REWRITE_TAC [CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o SPEC `lift (x:real )`) THEN
      ASM_REWRITE_TAC [IN_IMAGE_LIFT_DROP] THEN
      ONCE_ASM_REWRITE_TAC [LIFT_DROP]] THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
    EXISTS_TAC
      `(\t. norm (cexp (--(s:complex * Cx (drop (lift t))))  *  
     Cx (M:real * exp (drop a * t)) ) )` THEN
    STRIP_TAC THENL
     [REPEAT STRIP_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC
        `!t. &0 <= t ==> norm ( (f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
      DISCH_THEN (MP_TAC o SPEC `x:real`) THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN
      SUBGOAL_THEN
        `norm ((f:real^1->complex) (lift x)) <= 
     norm (Cx (M * exp (drop a * x) ) )`
        ASSUME_TAC THENL
       [SUBGOAL_THEN
          `norm ((f:real^1->complex) (lift x)) <= 
   abs (M * exp (drop a * x) )`
          ASSUME_TAC THENL
         [ALL_TAC; SIMP_TAC [COMPLEX_NORM_CX] THEN ASM_SIMP_TAC []] THEN
        MATCH_MP_TAC REAL_LE_POS_ABS THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN STRIP_TAC THENL
         [ASM_MESON_TAC [GSYM REAL_LT_LE]; SIMP_TAC [REAL_EXP_POS_LE]];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC
          `norm (cexp (--(s * Cx (drop (lift x)))) * (f:real^1->complex) (lift x))` THEN
        SIMP_TAC [COMPLEX_NORM_GE_RE_IM] THEN SIMP_TAC [COMPLEX_NORM_MUL] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [] THEN
        SIMP_TAC [NORM_POS_LE]];
      ALL_TAC] THEN
    SIMP_TAC [REAL_ARITH `&0 <= &0`] THEN STRIP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_INTEGRABLE_ON] THEN REWRITE_TAC [o_DEF] THEN
      SIMP_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SUBGOAL_THEN
        `lift o norm o (\x. cexp (--(s * Cx (drop (lift (drop x))))) *
   Cx (M * exp (drop a * drop x)))= (lift o norm) o (\x. cexp (--(s * Cx (drop (lift (drop x))))) *
    Cx (M * exp (drop a * drop x)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
        SIMP_TAC [];
        ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN SIMP_TAC [LIFT_DROP] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG];
        SIMP_TAC [CX_MUL] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN SIMP_TAC [CX_EXP] THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [CX_MUL]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SIMP_TAC [CONTINUOUS_ON_CX_DROP1];
      ALL_TAC] THEN
    SIMP_TAC [LIFT_DROP] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN MATCH_MP_TAC ABS_RE_REAL_LAPLACE_INTEGRABLE THEN
      REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
      EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC []] THEN
    SIMP_TAC [CX_MUL; COMPLEX_NORM_MUL; CX_EXP] THEN
    SIMP_TAC [COMPLEX_NORM_CX] THEN
    SIMP_TAC [REAL_ARITH `a:real * b * c = b*a*c`] THEN
    SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN SIMP_TAC [GSYM COMPLEX_NORM_MUL] THEN
    SIMP_TAC [GSYM CEXP_ADD; GSYM COMPLEX_ADD_RDISTRIB] THEN
    SIMP_TAC [SIMPLE_COMPLEX_ARITH `--x + y:complex = --(x - y)`] THEN
    SUBGOAL_THEN
      `!b. real_integral (real_interval [&0,b])
     (\t . abs M * norm (cexp (--(s - Cx (drop a)) * Cx t)) ) =
       (abs M) * real_integral (real_interval [&0,b])
        (\t. norm (cexp (--(s - Cx (drop a)) * Cx t)) )`
      ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN
      CONJ_TAC THENL
       [SIMP_TAC [COMPLEX_MUL_LNEG] THEN
        REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE];
        REWRITE_TAC [REAL_CONTINUOUS_NORM_WITHIN]];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [NORM_CEXP] THEN
    SIMP_TAC [RE_MUL_CX; RE_CX] THEN
    SIMP_TAC
      [SIMPLE_COMPLEX_ARITH `--(x - y) = --x + y:complex`; RE_ADD; RE_CX] THEN
    SIMP_TAC [RE_NEG] THEN SIMP_TAC [REAL_ARITH `--x + y:real = --(x - y)`] THEN
    EXISTS_TAC
      `abs M * inv (--(Re s - drop a)) * &0 - abs M * inv (--(Re s - drop a)) * &1` THEN
    MATCH_MP_TAC REALLIM_ABS_LIM THEN SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!b. real_integral (real_interval [&0,abs b])(\t. exp (--(Re s - drop a) * t)) =
    inv(-- (Re s- drop a) ) *  exp (--(Re s - drop a) * abs b) -
     inv(-- (Re s- drop a) ) *  exp (--(Re s - drop a) * &0)`
      ASSUME_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC [] THEN
      REWRITE_TAC [REAL_ARITH `x:real * (y - z) = x * y - x * z`] THEN
      MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
      MATCH_MP_TAC REALLIM_LMUL THENL
       [SIMP_TAC [REAL_ARITH `-- (a:real) * b = --( a * b)`] THEN
        MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
        MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN
        REWRITE_TAC [REAL_ARITH `&0 < x - y <=> y < x:real`] THEN
        ASM_MESON_TAC [real_gt];
        SIMP_TAC [REAL_ARITH `-- (a:real - b) * &0 = &0`] THEN
        REWRITE_TAC [REAL_EXP_0] THEN REWRITE_TAC [REALLIM_CONST]]] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
    ONCE_REWRITE_TAC
      [REAL_ARITH
         `exp (--(Re s - drop a) * x) = &1 * exp (--(Re s - drop a) * x)`] THEN
    ONCE_REWRITE_TAC [REAL_ARITH `a * &1 * b = a * b`] THEN
    SUBGOAL_THEN `&1= inv (--(Re s - drop a)) * --(Re s - drop a)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC [REAL_NEG_SUB] THEN REWRITE_TAC [REAL_SUB_0] THEN
      UNDISCH_TAC `Re s > drop a` THEN
      SUBGOAL_THEN `Re s > drop a <=> drop a < Re s` ASSUME_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_LT_LE]] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!t. exp (--(Re s - drop a) * t) = (\ t. exp (--(Re s - drop a) * t) )  t`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    ONCE_REWRITE_TAC [REAL_ARITH `(a:real * b) * c = a * (b * c)`] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
    SIMP_TAC [REAL_ARITH `(x:real) - (y:real) = x + (--y)`] THEN
    REWRITE_TAC [GSYM REAL_SUB_LNEG] THEN
    SIMP_TAC [REAL_ARITH `--(x:real) - --(y:real) = --x + y`] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB] THEN REWRITE_TAC [REAL_EXP_ADD] THEN
    ONCE_REWRITE_TAC
      [REAL_ARITH `(a:real * b * c + d * b * c) = b * (d * c) + (a * b) * c`] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN CONJ_TAC THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [REAL_MUL_AC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [REAL_MUL_AC] THEN
      SUBGOAL_THEN
        `((\n. --Re s * n) has_real_derivative --Re s)
   (atreal (x) within real_interval [&0 , abs b]) =
    ((\n. --Re s * n) has_real_derivative --Re s * &1)
     (atreal (x) within  real_interval [&0 , abs b])`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [REAL_MUL_RID] THEN SIMP_TAC [];
        ONCE_ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
        SIMP_TAC [HAS_REAL_DERIVATIVE_ID]];
      SIMP_TAC [] THEN
      SUBGOAL_THEN `atreal (x * --Re s) = atreal (--Re s * x )` ASSUME_TAC THENL
       [SIMP_TAC [REAL_MUL_AC]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SIMP_TAC [HAS_REAL_DERIVATIVE_EXP];
      ONCE_REWRITE_TAC [REAL_MUL_AC] THEN
      SUBGOAL_THEN
        `((\n. drop( a ) * n) has_real_derivative drop(a))
   (atreal (x) within real_interval [&0,abs b]) =
     ((\n. drop(a) * n) has_real_derivative drop(a) * &1)
      (atreal (x) within real_interval [&0,abs b])`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [REAL_MUL_RID] THEN SIMP_TAC [];
        ONCE_ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
        SIMP_TAC [HAS_REAL_DERIVATIVE_ID]];
      SIMP_TAC [] THEN
      SUBGOAL_THEN `atreal (x* drop(a)) = atreal (drop(a) *  x )` ASSUME_TAC THENL
       [SIMP_TAC [REAL_MUL_AC]; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SIMP_TAC [HAS_REAL_DERIVATIVE_EXP]];
    SUBGOAL_THEN
      `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
      EXISTS_TAC
        `(\t. norm (cexp (--(s:complex * Cx (drop (lift t))))  *  
     Cx (M:real * exp (drop a * t)) ) )` THEN
      STRIP_TAC THENL
       [REPEAT STRIP_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC
          `!t. &0 <= t ==> norm ( (f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
        DISCH_THEN (MP_TAC o SPEC `x:real`) THEN ASM_SIMP_TAC [] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN
          `norm ((f:real^1->complex) (lift x)) <= 
     norm (Cx (M * exp (drop a * x) ) )`
          ASSUME_TAC THENL
         [SUBGOAL_THEN
            `norm ((f:real^1->complex) (lift x)) <= 
   abs (M * exp (drop a * x) )`
            ASSUME_TAC THENL
           [ALL_TAC; SIMP_TAC [COMPLEX_NORM_CX] THEN ASM_SIMP_TAC []] THEN
          MATCH_MP_TAC REAL_LE_POS_ABS THEN ASM_SIMP_TAC [] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN STRIP_TAC THENL
           [ASM_MESON_TAC [GSYM REAL_LT_LE]; SIMP_TAC [REAL_EXP_POS_LE]];
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC
            `norm (cexp (--(s * Cx (drop (lift x)))) * (f:real^1->complex) (lift x))` THEN
          SIMP_TAC [COMPLEX_NORM_GE_RE_IM] THEN SIMP_TAC [COMPLEX_NORM_MUL] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [] THEN
          SIMP_TAC [NORM_POS_LE]];
        ALL_TAC] THEN
      SIMP_TAC [REAL_ARITH `&0 <= &0`] THEN STRIP_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [REAL_INTEGRABLE_ON] THEN
        REWRITE_TAC [o_DEF] THEN SIMP_TAC [IMAGE_LIFT_REAL_INTERVAL] THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        SUBGOAL_THEN
          `lift o norm o (\x. cexp (--(s * Cx (drop (lift (drop x))))) *
   Cx (M * exp (drop a * drop x)))= (lift o norm) o (\x. cexp (--(s * Cx (drop (lift (drop x))))) *
    Cx (M * exp (drop a * drop x)))`
          ASSUME_TAC THENL
         [ONCE_REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [o_DEF] THEN
          SIMP_TAC [];
          ALL_TAC] THEN
        ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN SIMP_TAC [LIFT_DROP] THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC [GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG];
          SIMP_TAC [CX_MUL] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
          SIMP_TAC [CONTINUOUS_ON_CONST] THEN SIMP_TAC [CX_EXP] THEN
          ONCE_REWRITE_TAC [GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [CX_MUL]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        SIMP_TAC [CONTINUOUS_ON_CX_DROP1];
        ALL_TAC] THEN
      SIMP_TAC [LIFT_DROP] THEN CONJ_TAC THENL
       [ALL_TAC;
        GEN_TAC THEN MATCH_MP_TAC ABS_IM_REAL_LAPLACE_INTEGRABLE THEN
        REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
        EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC []] THEN
      SIMP_TAC [CX_MUL; COMPLEX_NORM_MUL; CX_EXP] THEN
      SIMP_TAC [COMPLEX_NORM_CX] THEN
      SIMP_TAC [REAL_ARITH `a:real * b * c = b*a*c`] THEN
      SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN SIMP_TAC [GSYM COMPLEX_NORM_MUL] THEN
      SIMP_TAC [GSYM CEXP_ADD; GSYM COMPLEX_ADD_RDISTRIB] THEN
      SIMP_TAC [SIMPLE_COMPLEX_ARITH `--x + y:complex = --(x - y)`] THEN
      SUBGOAL_THEN
        `!b. real_integral (real_interval [&0,b])
     (\t . abs M * norm (cexp (--(s - Cx (drop a)) * Cx t)) ) =
       (abs M) * real_integral (real_interval [&0,b])
        (\t. norm (cexp (--(s - Cx (drop a)) * Cx t)) )`
        ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN
        CONJ_TAC THENL
         [SIMP_TAC [COMPLEX_MUL_LNEG] THEN
          REWRITE_TAC [CEXP_S_T_CONTINUOUS_COMPOSE];
          REWRITE_TAC [REAL_CONTINUOUS_NORM_WITHIN]];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN SIMP_TAC [NORM_CEXP] THEN
      SIMP_TAC [RE_MUL_CX; RE_CX] THEN
      SIMP_TAC
        [SIMPLE_COMPLEX_ARITH `--(x - y) = --x + y:complex`; RE_ADD; RE_CX] THEN
      SIMP_TAC [RE_NEG] THEN SIMP_TAC [REAL_ARITH `--x + y:real = --(x - y)`] THEN
      EXISTS_TAC
        `abs M * inv (--(Re s - drop a)) * &0 - abs M * inv (--(Re s - drop a)) * &1` THEN
      MATCH_MP_TAC REALLIM_ABS_LIM THEN SIMP_TAC [] THEN
      SUBGOAL_THEN
        `!b. real_integral (real_interval [&0,abs b])(\t. exp (--(Re s - drop a) * t)) =
    inv(-- (Re s- drop a) ) *  exp (--(Re s - drop a) * abs b) -
     inv(-- (Re s- drop a) ) *  exp (--(Re s - drop a) * &0)`
        ASSUME_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC [] THEN
        REWRITE_TAC [REAL_ARITH `x:real * (y - z) = x * y - x * z`] THEN
        MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
        MATCH_MP_TAC REALLIM_LMUL THENL
         [SIMP_TAC [REAL_ARITH `-- (a:real) * b = --( a * b)`] THEN
          MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
          MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN
          REWRITE_TAC [REAL_ARITH `&0 < x - y <=> y < x:real`] THEN
          ASM_MESON_TAC [real_gt];
          SIMP_TAC [REAL_ARITH `-- (a:real - b) * &0 = &0`] THEN
          REWRITE_TAC [REAL_EXP_0] THEN REWRITE_TAC [REALLIM_CONST]]] THEN
      GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN SIMP_TAC [] THEN
      ONCE_REWRITE_TAC
        [REAL_ARITH
           `exp (--(Re s - drop a) * x) = &1 * exp (--(Re s - drop a) * x)`] THEN
      ONCE_REWRITE_TAC [REAL_ARITH `a * &1 * b = a * b`] THEN
      SUBGOAL_THEN `&1= inv (--(Re s - drop a)) * --(Re s - drop a)`
        ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
        REWRITE_TAC [REAL_NEG_SUB] THEN REWRITE_TAC [REAL_SUB_0] THEN
        UNDISCH_TAC `Re s > drop a` THEN
        SUBGOAL_THEN `Re s > drop a <=> drop a < Re s` ASSUME_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC [] THEN REWRITE_TAC [REAL_LT_LE]] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN
        `!t. exp (--(Re s - drop a) * t) = (\ t. exp (--(Re s - drop a) * t) )  t`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_SIMP_TAC [] THEN
      ONCE_REWRITE_TAC [REAL_ARITH `(a:real * b) * c = a * (b * c)`] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
      SIMP_TAC [REAL_ARITH `(x:real) - (y:real) = x + (--y)`] THEN
      REWRITE_TAC [GSYM REAL_SUB_LNEG] THEN
      SIMP_TAC [REAL_ARITH `--(x:real) - --(y:real) = --x + y`] THEN
      REWRITE_TAC [REAL_ADD_RDISTRIB] THEN REWRITE_TAC [REAL_EXP_ADD] THEN
      ONCE_REWRITE_TAC
        [REAL_ARITH
           `(a:real * b * c + d * b * c) = b * (d * c) + (a * b) * c`] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN CONJ_TAC THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN ONCE_REWRITE_TAC [REAL_MUL_AC] THEN
      MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [REAL_MUL_AC] THEN
        SUBGOAL_THEN
          `((\n. --Re s * n) has_real_derivative --Re s)
   (atreal (x) within real_interval [&0 , abs b]) =
    ((\n. --Re s * n) has_real_derivative --Re s * &1)
     (atreal (x) within  real_interval [&0 , abs b])`
          ASSUME_TAC THENL
         [ONCE_REWRITE_TAC [REAL_MUL_RID] THEN SIMP_TAC [];
          ONCE_ASM_SIMP_TAC [] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
          SIMP_TAC [HAS_REAL_DERIVATIVE_ID]];
        SIMP_TAC [] THEN
        SUBGOAL_THEN `atreal (x * --Re s) = atreal (--Re s * x )` ASSUME_TAC THENL
         [SIMP_TAC [REAL_MUL_AC]; ALL_TAC] THEN
        ONCE_ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        SIMP_TAC [HAS_REAL_DERIVATIVE_EXP];
        ONCE_REWRITE_TAC [REAL_MUL_AC] THEN
        SUBGOAL_THEN
          `((\n. drop( a ) * n) has_real_derivative drop(a))
   (atreal (x) within real_interval [&0,abs b]) =
     ((\n. drop(a) * n) has_real_derivative drop(a) * &1)
      (atreal (x) within real_interval [&0,abs b])`
          ASSUME_TAC THENL
         [ONCE_REWRITE_TAC [REAL_MUL_RID] THEN SIMP_TAC [];
          ONCE_ASM_SIMP_TAC [] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
          SIMP_TAC [HAS_REAL_DERIVATIVE_ID]];
        SIMP_TAC [] THEN
        SUBGOAL_THEN `atreal (x* drop(a)) = atreal (drop(a) *  x )`
          ASSUME_TAC THENL
         [SIMP_TAC [REAL_MUL_AC]; ALL_TAC] THEN
        ONCE_ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        SIMP_TAC [HAS_REAL_DERIVATIVE_EXP]];
      UNDISCH_TAC
        `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity` THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC
        `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity` THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
        `?m. ((\b. real_integral (real_interval [&0,b])
    (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x)))) --->  m)  at_posinfinity`
        ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
        EXISTS_TAC
          `(\x. &2 * abs (Re (cexp (--(s * Cx (drop (lift x)))) *f (lift x))) )` THEN
        CONJ_TAC THENL
         [REPEAT STRIP_TAC THENL
           [SIMP_TAC [REAL_ABS_LE; REAL_SUB_LE];
            SIMP_TAC [REAL_MUL_2] THEN REAL_ARITH_TAC];
          ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
          SIMP_TAC [LIFT_DROP] THEN
          MATCH_MP_TAC ABS_RE_REAL_LAPLACE_INTEGRABLE THEN
          REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
          EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC [];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN
            `!b. real_integral (real_interval [&0,b])
   (\x. &2 *  abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x)))) =
     &2 * real_integral (real_interval [&0,b])(\x.  abs (Re (cexp (--(s * Cx (drop (lift x)))) * 
      f (lift x))))`
            ASSUME_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
            SIMP_TAC [LIFT_DROP] THEN
            MATCH_MP_TAC ABS_RE_REAL_LAPLACE_INTEGRABLE THEN
            REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
            EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN
            ASM_SIMP_TAC [];
            ASM_SIMP_TAC [] THEN
            SUBGOAL_THEN
              `?k. ((\b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) *
     f (lift x))))) ---> k) at_posinfinity`
              ASSUME_TAC THENL
             [EXISTS_TAC `k:real` THEN ASM_SIMP_TAC []; ALL_TAC] THEN
            EXISTS_TAC `&2 * k:real` THEN
            SUBGOAL_THEN
              `!b. &2 *  real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) ) =
    (\b. &2)b * (\ b . real_integral (real_interval [&0,b])
     (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) )) b`
              ASSUME_TAC THENL
             [SIMP_TAC []; ALL_TAC] THEN
            ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
            SIMP_TAC [REALLIM_CONST] THEN ASM_SIMP_TAC []];
          GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
          SIMP_TAC [LIFT_DROP] THENL
           [MATCH_MP_TAC ABS_RE_REAL_LAPLACE_INTEGRABLE;
            MATCH_MP_TAC RE_REAL_LAPLACE_INTEGRABLE] THEN
          REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
          EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC []];
        SUBGOAL_THEN
          `?m. ((\b. real_integral (real_interval [&0,b])
  (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x)))) --->  m) at_posinfinity`
          ASSUME_TAC THENL
         [MATCH_MP_TAC INTEGRAL_COMPARISON_TEST THEN
          EXISTS_TAC
            `(\x. &2 * abs (Im (cexp (--(s * Cx (drop (lift x)))) *f (lift x))) )` THEN
          CONJ_TAC THENL
           [REPEAT STRIP_TAC THENL
             [SIMP_TAC [REAL_ABS_LE; REAL_SUB_LE];
              SIMP_TAC [REAL_MUL_2] THEN REAL_ARITH_TAC];
            ALL_TAC] THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
           [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
            SIMP_TAC [LIFT_DROP] THEN
            MATCH_MP_TAC ABS_IM_REAL_LAPLACE_INTEGRABLE THEN
            REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
            EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN
            ASM_SIMP_TAC [];
            ALL_TAC] THEN
          CONJ_TAC THENL
           [SUBGOAL_THEN
              `!b. real_integral (real_interval [&0,b]) (\x. &2 *  abs (Im (cexp (--(s * Cx (drop (lift x)))) *
    f (lift x)))) = &2 * real_integral (real_interval [&0,b])
      (\x.  abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))))`
              ASSUME_TAC THENL
             [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
              SIMP_TAC [LIFT_DROP] THEN
              MATCH_MP_TAC ABS_IM_REAL_LAPLACE_INTEGRABLE THEN
              REWRITE_TAC [laplace_exists; exp_order_comp] THEN
              ASM_SIMP_TAC [] THEN EXISTS_TAC `M:real` THEN
              EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC [];
              ASM_SIMP_TAC [] THEN
              SUBGOAL_THEN
                `?k. ((\b.  real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) *
      f (lift x))))) ---> k) at_posinfinity`
                ASSUME_TAC THENL
               [EXISTS_TAC `k':real` THEN ASM_SIMP_TAC []; ALL_TAC] THEN
              EXISTS_TAC `&2 * k':real` THEN
              SUBGOAL_THEN
                `!b. &2 *  real_integral (real_interval [&0,b])
   (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) ) =
     (\b. &2)b * (\ b . real_integral (real_interval [&0,b])
      (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) )) b`
                ASSUME_TAC THENL
               [SIMP_TAC []; ALL_TAC] THEN
              ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
              SIMP_TAC [REALLIM_CONST] THEN ASM_SIMP_TAC []];
            GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
            SIMP_TAC [LIFT_DROP] THENL
             [MATCH_MP_TAC ABS_IM_REAL_LAPLACE_INTEGRABLE;
              MATCH_MP_TAC IM_REAL_LAPLACE_INTEGRABLE] THEN
            REWRITE_TAC [laplace_exists; exp_order_comp] THEN ASM_SIMP_TAC [] THEN
            EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN
            ASM_SIMP_TAC []];
          UNDISCH_TAC
            `?m. ((\b. real_integral (real_interval [&0,b])
    (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x)))) --->  m)  at_posinfinity` THEN
          REPEAT STRIP_TAC THEN
          UNDISCH_TAC
            `?m. ((\b. real_integral (real_interval [&0,b])
  (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x)))) --->  m) at_posinfinity` THEN
          REPEAT STRIP_TAC THEN EXISTS_TAC `complex(k-m, k'-m')` THEN
          MATCH_MP_TAC LIM_COMPLEX_REAL_COMPONENTS THEN SIMP_TAC [] THEN
          SIMP_TAC [GSYM COMPLEX_TRAD] THEN SIMP_TAC [RE; IM] THEN
          ASM_SIMP_TAC [] THEN CONJ_TAC THENL
           [SUBGOAL_THEN
              `!x. Re (cexp (--(s * Cx (drop (lift x)))) * (f:real^1->complex) (lift x)) =
    abs( Re(cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
     ( abs(Re(cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
      Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x)) )`
              ASSUME_TAC THENL
             [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
            ONCE_ASM_REWRITE_TAC [] THEN
            SUBGOAL_THEN
              `!b. real_integral (real_interval [&0,b])
   (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
     (abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
       Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))))  =
    real_integral (real_interval [&0,b])
     (\x. abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) ) -
    real_integral (real_interval [&0,b])
     (\x.  abs (Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
       Re (cexp (--(s * Cx (drop (lift x)))) * f (lift x)) )`
              ASSUME_TAC THENL
             [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
               [SIMP_TAC [LIFT_DROP] THEN
                MATCH_MP_TAC ABS_RE_REAL_LAPLACE_INTEGRABLE;
                MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
                SIMP_TAC [LIFT_DROP] THENL
                 [MATCH_MP_TAC ABS_RE_REAL_LAPLACE_INTEGRABLE;
                  MATCH_MP_TAC RE_REAL_LAPLACE_INTEGRABLE]] THEN
              REWRITE_TAC [laplace_exists; exp_order_comp] THEN
              ASM_SIMP_TAC [] THEN EXISTS_TAC `M:real` THEN
              EXISTS_TAC `a:real^1`;
              ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_SUB] THEN
            ASM_SIMP_TAC [];
            SUBGOAL_THEN
              `!x. Im (cexp (--(s * Cx (drop (lift x)))) * (f:real^1->complex) (lift x)) =
   abs( Im(cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
    ( abs(Im(cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
     Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x)) )`
              ASSUME_TAC THENL
             [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
            ONCE_ASM_REWRITE_TAC [] THEN
            SUBGOAL_THEN
              `!b. real_integral (real_interval [&0,b])
    (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
      (abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
      Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))))  =
    real_integral (real_interval [&0,b])
      (\x. abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) ) -
    real_integral (real_interval [&0,b])
      (\x.  abs (Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x))) -
             Im (cexp (--(s * Cx (drop (lift x)))) * f (lift x)) )`
              ASSUME_TAC THENL
             [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
               [SIMP_TAC [LIFT_DROP] THEN
                MATCH_MP_TAC ABS_IM_REAL_LAPLACE_INTEGRABLE;
                MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
                SIMP_TAC [LIFT_DROP] THENL
                 [MATCH_MP_TAC ABS_IM_REAL_LAPLACE_INTEGRABLE;
                  MATCH_MP_TAC IM_REAL_LAPLACE_INTEGRABLE]] THEN
              REWRITE_TAC [laplace_exists; exp_order_comp] THEN
              ASM_SIMP_TAC [] THEN EXISTS_TAC `M:real` THEN
              EXISTS_TAC `a:real^1`;
              ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_SUB] THEN
            ASM_SIMP_TAC []]]]]]);;

let INTEGRABLE_LIM_AT_POSINFINITY = prove
 (`!f. (f integrable_on {t | &0 <= drop t}) <=>
        (!a. f integrable_on interval[vec 0,a]) /\
        ?(l:real^2). ((\a. integral (interval[vec 0,lift a]) f) --> l) at_posinfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC [integrable_on] THEN EQ_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC [GSYM integrable_on] THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
      REWRITE_TAC [INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
      SUBGOAL_THEN
        `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
        (fun th -> REWRITE_TAC [th]) THENL
       [REWRITE_TAC
          [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
           IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        STRIP_TAC THEN X_GEN_TAC `a:real^1` THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [`vec 0:real^1`; `a:real^1`]) THEN
        REWRITE_TAC [DROP_VEC; LIFT_NUM; REAL_ARITH `max x x = x`]];
      EXISTS_TAC `y:complex` THEN POP_ASSUM MP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_ALT] THEN
      REWRITE_TAC [INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
      SUBGOAL_THEN
        `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
        (fun th -> REWRITE_TAC [th]) THENL
       [REWRITE_TAC
          [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
           IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC [LIM_AT_POSINFINITY; dist; real_ge] THEN STRIP_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
      X_GEN_TAC `b:real` THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPECL [`lift(--b)`; `lift b`]) THEN
      REWRITE_TAC [DROP_VEC; LIFT_NUM; LIFT_DROP] THEN
      SUBGOAL_THEN `max (&0) (--b) = &0` SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC [LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC
          [BALL_1; SUBSET_INTERVAL_1; DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP]] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC [GSYM integrable_on] THEN STRIP_TAC THEN
    REWRITE_TAC [integrable_on] THEN EXISTS_TAC `l:complex` THEN
    REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN REWRITE_TAC [HAS_INTEGRAL_ALT] THEN
    REWRITE_TAC [INTEGRAL_RESTRICT_INTER; INTEGRABLE_RESTRICT_INTER] THEN
    SUBGOAL_THEN
      `!a b. {t | &0 <= drop t} INTER interval[a,b] =
          interval[lift(max (&0) (drop a)),b]`
      (fun th -> REWRITE_TAC [th]) THENL
     [REWRITE_TAC
        [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
         IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC [LIM_AT_POSINFINITY; dist; real_ge] THEN STRIP_TAC THEN
    REWRITE_TAC [LIFT_NUM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `b:real^1`) THEN
      MATCH_MP_TAC (REWRITE_RULE [IMP_CONJ_ALT] INTEGRABLE_SUBINTERVAL) THEN
      SIMP_TAC [SUBSET_INTERVAL_1; DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `B:real` (LABEL_TAC "*")) THEN
      EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
      REWRITE_TAC
        [BALL_1; SUBSET_INTERVAL_1; DROP_ADD; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
      STRIP_TAC THENL
       [ALL_TAC;
        SUBGOAL_THEN `max (&0) (drop a) = &0` SUBST1_TAC THENL
         [ALL_TAC;
          REWRITE_TAC [LIFT_NUM] THEN FIRST_X_ASSUM (MP_TAC o SPEC `drop b`) THEN
          REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC]] THEN
      ASM_REAL_ARITH_TAC]]);;

(*---------------------------------------------------------------------------*)
(*                      Properties of Laplace Tranform                       *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*                               Linearity                                   *)
(*---------------------------------------------------------------------------*)

let LAPLACE_COMPLEX_MUL_LINEARITY = prove
 (`!(f:real^1->complex) (s:complex) (a:real^2).
   laplace_exists f s ==> (laplace_transform (\x. a * f x) s = a * laplace_transform f s)`,
  REWRITE_TAC [laplace_transform] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x:complex * y * z = y * x * z`] THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t} (\t. a * (cexp (--(s * Cx (drop t))) * (f:real^1->complex) t)) =
   a * integral {t | &0 <= drop t} (\t.  (cexp (--(s * Cx (drop t))) * f t))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
    REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [GSYM LIFT_NUM] THENL
     [MP_TAC
        (ISPECL [`f:real^1->complex`; `s:real^2`; `drop a`]
           LAPLACE_EXISTS_INTEGRABLE) THEN
      REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC;
      MATCH_MP_TAC LIM_LAPLACE_EXISTS];
    ALL_TAC] THEN
  ASM_SIMP_TAC []);;

let LAPLACE_MUL_LINEARITY = prove
 (`!(f:real^1->complex) (s:complex) (a:real).
   laplace_exists f s ==> 
  (laplace_transform (\x. a % f x) s = a % laplace_transform f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_CMUL] THEN
  ASM_SIMP_TAC [LAPLACE_COMPLEX_MUL_LINEARITY]);;

let LAPLACE_COMPLEX_MUL_ADD_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex) a b.
 laplace_exists f s /\ laplace_exists g s ==>
(laplace_transform (\x. a * f x + b * g x ) s = a * laplace_transform f s + b * laplace_transform g s)`,
  REWRITE_TAC [laplace_transform] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `v:complex * (w * x + y * z) = w * v * x + y * v * z`] THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t}
    (\t. a * cexp (--(s * Cx (drop t))) * f t + b * cexp (--(s * Cx (drop t))) * g t) =
     integral {t | &0 <= drop t}
      (\t. a * cexp (--(s * Cx (drop t))) * f t) + integral {t | &0 <= drop t} (\t. b * cexp (--(s * Cx (drop t))) * g t)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_COMPLEX_MUL THEN
    REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN
    REWRITE_TAC [GSYM LIFT_NUM] THEN REPEAT STRIP_TAC THENL
     [MP_TAC
        (ISPECL [`f:real^1->complex`; `s:real^2`; `drop a`]
           LAPLACE_EXISTS_INTEGRABLE) THEN
      REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC;
      MATCH_MP_TAC LIM_LAPLACE_EXISTS;
      MP_TAC
        (ISPECL [`g:real^1->complex`; `s:real^2`; `drop a`]
           LAPLACE_EXISTS_INTEGRABLE) THEN
      REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC;
      MATCH_MP_TAC LIM_LAPLACE_EXISTS];
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `integral {t | &0 <= drop t}
   (\t. a * (cexp (--(s * Cx (drop t))) * f t)) = a * integral {t | &0 <= drop t}
      (\t.  (cexp (--(s * Cx (drop t))) * f t))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
      REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN
      REWRITE_TAC [GSYM LIFT_NUM] THEN REPEAT STRIP_TAC THENL
       [MP_TAC
          (ISPECL [`f:real^1->complex`; `s:real^2`; `drop a`]
             LAPLACE_EXISTS_INTEGRABLE) THEN
        REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC;
        MATCH_MP_TAC LIM_LAPLACE_EXISTS];
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      SUBGOAL_THEN
        `integral {t | &0 <= drop t}
   (\t. b * (cexp (--(s * Cx (drop t))) * g t)) = b * integral {t | &0 <= drop t}
      (\t.  (cexp (--(s * Cx (drop t))) * g t))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
        REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN
        REWRITE_TAC [GSYM LIFT_NUM] THEN REPEAT STRIP_TAC THENL
         [MP_TAC
            (ISPECL [`g:real^1->complex`; `s:real^2`; `drop a`]
               LAPLACE_EXISTS_INTEGRABLE) THEN
          REWRITE_TAC [LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC;
          MATCH_MP_TAC LIM_LAPLACE_EXISTS];
        ALL_TAC]]] THEN
  ASM_SIMP_TAC []);;

let LAPLACE_MUL_ADD_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex) a b.
 laplace_exists f s /\ laplace_exists g s ==>
(laplace_transform (\x. a % f x + b % g x ) s = 
  a % laplace_transform f s + b % laplace_transform g s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_CMUL] THEN
  MATCH_MP_TAC LAPLACE_COMPLEX_MUL_ADD_LINEARITY THEN ASM_SIMP_TAC []);;

let LAPLACE_ADD_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex).
    laplace_exists f s /\ laplace_exists g s ==>
     (laplace_transform (\x. f x + g x ) s = laplace_transform f s + laplace_transform g s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`(f:real^1->complex)`; `(g:real^1->complex)`; `s:complex`; `Cx (&1)`;
        `Cx (&1)`]
       LAPLACE_COMPLEX_MUL_ADD_LINEARITY) THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [COMPLEX_FIELD `Cx (&1) * x = x`]);;

(*---------------------------------------------------------------------------*)
(*                           Frequency Shifting                              *)
(*---------------------------------------------------------------------------*)

let LAPLACE_SHIFT_IN_S_DOMAIN = prove
 (`! (f:real^1->complex) (s:complex) b.
     laplace_exists f s  ==> (laplace_transform (\t. cexp (b * Cx (drop t)) * f t) s = laplace_transform f (s - b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_exists; laplace_transform] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x:complex * y * z = (x * y) * z`] THEN
  SIMP_TAC [GSYM CEXP_ADD; GSYM COMPLEX_MUL_LNEG; GSYM COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(--s + b) = --(s - b)`]);;

(*---------------------------------------------------------------------------*)
(*                          Some useful theorems                             *)
(*---------------------------------------------------------------------------*)

let LIM_ABS_LIM_EQ_LAPLACE = prove
 (`!(f:real^1->complex). laplace_exists f s ==>
   lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * f t)) =
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--(s * Cx (drop t))) * f t)) (abs b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_ABS_LIM_EQ THEN
  MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN ASM_SIMP_TAC []);;

let LAPLACE_INTEGRAL_EQ_REP = prove
 (`!(f:real^1->complex). laplace_exists f s ==>
    integral {t | &0 <= drop t} 
     (\t. cexp (--(s * Cx (drop t))) * f t) = 
     lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) 
     (\t. cexp (--(s * Cx (drop t))) * f t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  REWRITE_TAC [HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC [LIFT_VEC_0] THEN
    MP_TAC
      (SPECL [`f:real^1->complex`; `s:complex`; `drop a`]
         LAPLACE_EXISTS_INTEGRABLE) THEN
    ASM_SIMP_TAC [LIFT_DROP];
    REWRITE_TAC [GSYM LIFT_NUM] THEN SIMP_TAC [GSYM FUN_LIM] THEN
    REWRITE_TAC [convergent_f] THEN MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN
    ASM_SIMP_TAC []]);;

let INTEGRAL_BY_PARTS_LAPLACE_DIFF_INTEGRAND = prove
 (`!f:real^1->complex f':real^1->complex s.
   laplace_exists f s /\
   laplace_exists f' s /\
  (!x. (f has_vector_derivative f' x) (at x)) ==>
 (!b. integral (interval [lift (&0),lift (abs b)]) 
   (\t. (\t. cexp (--(s * Cx (drop t)))) t * f' t) =
((\ t. cexp (--(s * Cx (drop t)))) (lift (abs b))) * (f (lift (abs b))) - 
 ((\ t . cexp (--(s * Cx (drop t)))  ) (lift (&0) ) ) * (f (lift (&0)) ) 
   - (integral (interval [lift (&0),lift (abs b)]) 
  (\t. (\t. cexp (--(s * Cx (drop t))) * (--s)) t * f t) ))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_BY_PARTS_AT THEN
  SIMP_TAC [LIFT_DROP] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN PURE_ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
    MATCH_MP_TAC VECTOR_COMPLEX_DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(Cx (drop t) * --s) = (--s * Cx (drop t) )`] THEN
      SIMP_TAC [HAS_COMPLEX_DERIVATIVE_CEXP]] THEN
    PURE_ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
    SUBGOAL_THEN
      `((\t. --s * Cx (drop t)) has_vector_derivative --s) (at t) = ((\t. (\x y. x * y) ((\x:real^1. --s:complex) t)
   ((\x. Cx (drop x))  t)) has_vector_derivative (\x y. x * y) ((\x:real^1. --s:complex) t) (Cx (&1)) +
    (\x y. x * y) (Cx (&0)) ((\x. Cx (drop x))  t)) (at t)`
      ASSUME_TAC THENL
     [SIMP_TAC [COMPLEX_MUL_RID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_AT THEN
    SIMP_TAC [GSYM COMPLEX_VEC_0] THEN SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST] THEN
    REWRITE_TAC [BILINEAR_X_MUL_Y] THEN
    SUBGOAL_THEN `(\x. Cx (drop x)) = Cx o (\x . x) o drop` ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN
    ONCE_REWRITE_TAC [GSYM LIFT_DROP] THEN
    ONCE_REWRITE_TAC [GSYM HAS_CX_VECTOR_DERIVATIVE_AT] THEN
    ONCE_REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [HAS_REAL_DERIVATIVE_ID];
    ALL_TAC;
    SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x * y) * z = y:complex * (x * z)`] THEN
    MATCH_MP_TAC INTEGRABLE_COMPLEX_MUL THEN
    MP_TAC
      (SPECL [`f:real^1->complex`; `s:complex`; `abs b`]
         LAPLACE_EXISTS_INTEGRABLE);
    MP_TAC
      (SPECL [`f':real^1->complex`; `s:complex`; `abs b`]
         LAPLACE_EXISTS_INTEGRABLE)] THEN
  ASM_SIMP_TAC []);;

(*---------------------------------------------------------------------------*)
(*                First-order Differentiation in Time Domain                 *)
(*---------------------------------------------------------------------------*)

let LAPLACE_DIFF_THEOREM_AT = prove
 (`!(f:real^1->complex) (f':real^1->complex) (s:complex) (b:real).
      laplace_exists f s /\ laplace_exists f' s  /\
      (!x. (f has_vector_derivative f' x) (at x))  ==>
      (laplace_transform f' s = (s * (laplace_transform f s)) - f (lift (&0)) )`,
  REWRITE_TAC [laplace_transform] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t} (\t. cexp (--(s * Cx (drop t))) * (f':real^1->complex) t) = lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * f' t))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LAPLACE_INTEGRAL_EQ_REP]; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t} (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t) = lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * f t))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LAPLACE_INTEGRAL_EQ_REP]; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * f' t))=
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--(s * Cx (drop t))) * f' t)) (abs b))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LIM_ABS_LIM_EQ_LAPLACE]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `lim at_posinfinity (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * f t))=
   lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift (b)]) (\t. cexp (--(s * Cx (drop t))) * f t)) (abs b))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LIM_ABS_LIM_EQ_LAPLACE]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `!b. integral (interval [lift (&0),lift (abs b)]) (\t. (\t. cexp (--(s * Cx (drop t)))) t * (f':real^1->complex) t) =
    ((\ t . cexp (--(s * Cx (drop t)))  ) (lift (abs b) ) ) * ((f:real^1->complex) (lift (abs b)) ) - ((\ t . cexp (--(s * Cx (drop t)))  ) (lift (&0) ) ) * (f (lift (&0)) ) 
     - (integral (interval [lift (&0),lift (abs b)]) (\t. (\t. cexp (--(s * Cx (drop t))) * (--s)) t * f t) )`
    ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC [INTEGRAL_BY_PARTS_LAPLACE_DIFF_INTEGRAND];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!b. integral (interval [lift (&0),lift (abs b)]) (\t. cexp (--(s * Cx (drop t))) * f' t) =
   integral (interval [lift (&0),lift (abs b)]) (\t. (\t. cexp (--(s * Cx (drop t)))) t * f' t)`
    ASSUME_TAC THENL
   [SIMP_TAC []; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ASM_SIMP_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SIMP_TAC
    [LIFT_DROP; COMPLEX_MUL_RZERO; COMPLEX_NEG_0; CEXP_0; COMPLEX_MUL_LID] THEN
  SUBGOAL_THEN
    `s * lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)])
   (\t. cexp (--(s * Cx (drop t))) * f t)) - f (lift (&0)) = Cx (&0) - ( --s * lim at_posinfinity
    (\b. integral (interval [lift (&0),lift (abs b)])
     (\t. cexp (--(s * Cx (drop t))) * f t)) +  f (lift (&0)))`
    ASSUME_TAC THENL
   [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(x * --y) * (z:complex) = --x * y * z`] THEN
  SUBGOAL_THEN
    `!b. cexp (--(s * Cx (abs b))) * f (lift (abs b)) - f (lift (&0)) -
    integral (interval [lift (&0),lift (abs b)]) (\t. --cexp (--(s * Cx (drop t))) * s * f t)  =
    (\b. cexp (--(s * Cx (abs b))) * f (lift (abs b))) b - (\b.(\b. integral (interval [lift (&0),lift (abs b)])
     (\t. --cexp (--(s * Cx (drop t))) * s * f t) ) b + (\b. f (lift (&0) ) )b) b`
    ASSUME_TAC THENL
   [SIMP_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  MATCH_MP_TAC TENDSTO_LIM THEN SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
  MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
   [SIMP_TAC [GSYM COMPLEX_VEC_0] THEN UNDISCH_TAC `laplace_exists f s` THEN
    REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON THEN
    EXISTS_TAC `(\b. M * exp (--(Re s - drop a) * abs b))` THEN SIMP_TAC [] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
        `!x. norm (cexp (--(s * Cx (abs x))) * (f:real^1->complex) (lift (abs x))) <=
    M * exp (--(Re s - drop a) * abs x)`
        ASSUME_TAC THENL
       [ALL_TAC; PURE_ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [EVENTUALLY_TRUE]] THEN
      GEN_TAC THEN
      SIMP_TAC
        [COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NEG_LMUL; RE_MUL_CX;
         REAL_ARITH `--(a - b:real)*c = --a*c + b*c`; REAL_EXP_ADD] THEN
      ONCE_REWRITE_TAC [RE_NEG; REAL_ARITH `a:real * b * c = b * a * c`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC [REAL_EXP_POS_LE] THEN
      UNDISCH_TAC
        `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
      DISCH_THEN (MP_TAC o SPEC `abs(x:real )`) THEN SIMP_TAC [REAL_ABS_POS];
      SIMP_TAC [LIFT_VEC_0] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      REWRITE_TAC [GSYM TENDSTO_REAL] THEN
      SUBGOAL_THEN `&0 = M * &0` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_MUL THEN
      SIMP_TAC [REALLIM_CONST] THEN MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
      REWRITE_TAC [GSYM REAL_NEG_LMUL] THEN
      MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN
      REWRITE_TAC [REAL_ARITH `&0 < x - y <=> y < x:real`] THEN
      ASM_MESON_TAC [real_gt]];
    MATCH_MP_TAC LIM_ADD THEN SIMP_TAC [LIM_CONST] THEN
    SIMP_TAC [SIMPLE_COMPLEX_ARITH `--x:complex * y * z= --y * x * z`] THEN
    SUBGOAL_THEN
      `!b. integral (interval [lift (&0),lift (b)])(\t. --s * cexp (--(s * Cx (drop t))) * f t) =
    --s * integral (interval [lift (&0),lift (b)]) (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t)`
      ASSUME_TAC THENL
     [GEN_TAC THEN
      SUBGOAL_THEN
        `(\t. --s *cexp (--(s * Cx (drop t))) * (f:real^1->complex) t) =
   (\t.  --s  * (\t. cexp (--(s * Cx (drop t))) * f t) t)`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COMPLEX_INTEGRAL_CMUL THEN
      MATCH_MP_TAC LAPLACE_EXISTS_INTEGRABLE THEN ASM_SIMP_TAC [];
      ONCE_ASM_SIMP_TAC [] THEN MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
      SUBGOAL_THEN
        `lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)])(\t. cexp (--(s * Cx (drop t))) * f t)) =
   lim at_posinfinity (\b. (\x. integral (interval [lift (&0),lift (x)])(\t. cexp (--(s * Cx (drop t))) * f t)) (abs b))`
        ASSUME_TAC THENL
       [SIMP_TAC []; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
        `lim at_posinfinity (\b. (\x. integral (interval [lift (&0),lift x])
     (\t. cexp (--(s * Cx (drop t))) * f t))(abs b)) = lim at_posinfinity (\b. integral (interval [lift (&0),lift (b)])
       (\t. cexp (--(s * Cx (drop t))) * f t))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC LIM_ABS_LIM_EQ;
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN
        SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f]] THEN
      MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN ASM_SIMP_TAC []]]);;

let LAPLACE_DIFF_F_THEOREM_AT = prove
 (`! (f:real^1->complex) (s:complex) (b:real).
  laplace_exists f s /\
 (laplace_exists (\x. vector_derivative f ( at x )) s ) /\ 
 (!x. f differentiable at x) 
     ==>
   (laplace_transform (\x. vector_derivative f (at x)) s = 
   (s * (laplace_transform f s)) - f (lift (&0)) )`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LAPLACE_DIFF_THEOREM_AT THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN
  ASM_SIMP_TAC []);;

let LAPLACE_F_EQ_EQ = prove
 (`!(f:real^1->complex) g s.
   (!x . f x = g x) /\
   laplace_exists f s /\  laplace_exists g s   ==>
     laplace_transform f s = laplace_transform g s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [laplace_transform] THEN AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM] THEN STRIP_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC []);;

(*---------------------------------------------------------------------------*)
(*              Higher-order Differentiation in Time Domain                  *)
(*---------------------------------------------------------------------------*)

let higher_vector_derivative = new_recursive_definition num_RECURSION
   `(higher_vector_derivative 0 (f:real^1->complex) (x:real^1) = f x ) /\
     (!n. higher_vector_derivative (SUC n) (f:real^1->complex) (x:real^1) =
    (vector_derivative (\x. higher_vector_derivative n f x ) (at x)))`;;

let laplace_exists_higher_deriv = new_recursive_definition num_RECURSION
`(laplace_exists_higher_deriv 0 (f:real^1->complex) (s:complex) = 
   (laplace_exists f s)  )   /\
(!n. laplace_exists_higher_deriv (SUC n) (f:real^1->complex) (s:complex) =
    ((laplace_exists (\x:real^1. higher_vector_derivative (SUC n) f x) s) 
    /\ (laplace_exists_higher_deriv n f s) ))`;;

let differentiable_higher_derivative = new_recursive_definition num_RECURSION
`(differentiable_higher_derivative 0 (f:real^1->complex) (x:real^1) = (f differentiable at x)  )  /\
   (!n. differentiable_higher_derivative  (SUC n) (f:real^1->complex) (x:real^1) =
     ((((\x:real^1. higher_vector_derivative (SUC n) f x)) differentiable at x) /\ (differentiable_higher_derivative  n f x) ))`;;

let LAPLACE_N_PLUS_ONETH_ORDER_DERIVATIVE = prove
 (`!f n s. (laplace_exists
      (\x. vector_derivative (\x. higher_vector_derivative n f x) (at x))
      s) /\
  (laplace_exists_higher_deriv n f s) /\
  (!x. (\x. vector_derivative (\x. higher_vector_derivative n f x) (at x)) differentiable
          at x /\
          differentiable_higher_derivative n f x)
   ==>
(laplace_transform (\x. vector_derivative (\x. higher_vector_derivative n (f:real^1->complex) x) (at x)) s = 
     s * laplace_transform (\x. higher_vector_derivative n f x) s   - (\x. higher_vector_derivative n f x) (lift (&0)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LAPLACE_DIFF_F_THEOREM_AT THEN
  ASM_SIMP_TAC [] THEN CONJ_TAC THENL
   [MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `laplace_exists_higher_deriv n f s` THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC [higher_vector_derivative] THEN ASM_SIMP_TAC [] THEN
      SIMP_TAC [laplace_exists_higher_deriv; ETA_AX];
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUC_GT_ZERO;
        UNDISCH_TAC `laplace_exists_higher_deriv n f s` THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [laplace_exists_higher_deriv]] THEN
      ASM_SIMP_TAC []];
    GEN_TAC THEN
    UNDISCH_TAC
      `!x. (\x. vector_derivative (\x. higher_vector_derivative n f x) (at x)) differentiable
     at x /\ differentiable_higher_derivative n f x` THEN
    DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN REPEAT STRIP_TAC THEN
    MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `differentiable_higher_derivative n f x` THEN
      ASM_SIMP_TAC [] THEN
      REWRITE_TAC
        [higher_vector_derivative; differentiable_higher_derivative] THEN
      SIMP_TAC [ETA_AX];
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUC_GT_ZERO;
        UNDISCH_TAC `differentiable_higher_derivative n f x` THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [differentiable_higher_derivative]] THEN
      ASM_SIMP_TAC []]]);;

let LAPLACE_HIGHER_DIFF_F_THEOREM_AT_CORRECT = prove
 (`!(f:real^1->complex) (s:complex) (n:num).
     ((laplace_exists_higher_deriv n f s) /\
     (!x:real^1. differentiable_higher_derivative n f x)) ==>
     (laplace_transform (\x.  higher_vector_derivative n f x ) s =
     ((s pow n) * (laplace_transform f s)) -
      vsum (1..n) (\x. s pow (x - 1)  *
       higher_vector_derivative (n - x) f (lift (&0))) )`,
  REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC [higher_vector_derivative; complex_pow; COMPLEX_MUL_LID] THEN
    SIMP_TAC [VSUM_CLAUSES_NUMSEG] THEN SUBGOAL_THEN `1 = 0 <=> F` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN SIMP_TAC [ETA_AX; VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC
    [higher_vector_derivative; laplace_exists_higher_deriv;
     differentiable_higher_derivative] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
    `laplace_exists_higher_deriv n f s /\ (!x. differentiable_higher_derivative n f x)
    ==> laplace_transform (\x. higher_vector_derivative n f x) s = s pow n * laplace_transform f s -
     vsum (1..n) (\x. s pow (x - 1) * higher_vector_derivative (n - x) f (lift (&0)))` THEN
  ASM_SIMP_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [higher_vector_derivative] THEN
  SUBGOAL_THEN
    `laplace_transform (\x. vector_derivative (\x. higher_vector_derivative n (f:real^1->complex) x) (at x)) s = 
     s * laplace_transform (\x. higher_vector_derivative n f x) s   - (\x. higher_vector_derivative n f x) (lift (&0))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LAPLACE_N_PLUS_ONETH_ORDER_DERIVATIVE]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN ONCE_ASM_REWRITE_TAC [] THEN
  SIMP_TAC [COMPLEX_SUB_LDISTRIB; complex_pow] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH
       `(a*f*b - a*c - d:complex = (a*f)*b - e) <=> a*c + d = e`] THEN
  SIMP_TAC [ADD1] THEN
  SUBGOAL_THEN
    `s * vsum (1..n)(\x. s pow (x - 1) * higher_vector_derivative (n - x) f (lift (&0)))
      = vsum (1..n)(\x. s * s pow (x - 1) * higher_vector_derivative (n - x) f (lift (&0)))`
    ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_COMPLEX_LMUL THEN
    SIMP_TAC [FINITE_NUMSEG];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN
    `vsum (1..n) (\x. s * s pow (x - 1) * higher_vector_derivative (n - x) f (lift (&0))) =
     vsum (1..n)(\x. s pow x * higher_vector_derivative (n - x) f (lift (&0)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN SIMP_TAC [COMPLEX_EQ_MUL_RCANCEL] THEN
    DISJ1_TAC THEN
    SUBGOAL_THEN `s * s pow (x - 1) = s pow (SUC (x - 1))` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN REWRITE_TAC [complex_pow]; ALL_TAC] THEN
    ONCE_REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN `SUC (x - 1) = x` ASSUME_TAC THENL
     [MATCH_MP_TAC SUC_1; ALL_TAC] THEN
    ASM_SIMP_TAC [];
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `vsum (1..n) (\x. s pow x * higher_vector_derivative (n - x) f (lift (&0))) + higher_vector_derivative n f (lift (&0))  = 
     vsum (0..n)  (\x. s pow x * higher_vector_derivative (n - x) f (lift (&0)))`
      ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC [COMPLEX_ADD_AC] THEN
      ONCE_REWRITE_TAC [ARITH_RULE `1 = 0 + 1`] THEN
      SUBGOAL_THEN
        `higher_vector_derivative n f (lift (&0)) =
    (\x. s pow x * higher_vector_derivative (n - x) f (lift (&0))) 0`
        ASSUME_TAC THENL
       [SIMP_TAC [complex_pow; COMPLEX_MUL_LID; SUB];
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC VSUM_CLAUSES_LEFT THEN
        ARITH_TAC];
      ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN
        `vsum (1..n + 1) (\x. s pow (x - 1) * higher_vector_derivative ((n + 1) - x) f (lift (&0))) =
   vsum (0..n )(\x. s pow (x) * higher_vector_derivative (n  - x) f (lift (&0)))`
        ASSUME_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC []] THEN
      MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN EXISTS_TAC `(\x. x - 1)` THEN
      EXISTS_TAC `(\x. x + 1)` THEN CONJ_TAC THEN SIMP_TAC [IN_NUMSEG] THENL
       [ALL_TAC;
        REPEAT STRIP_TAC THENL
         [UNDISCH_TAC `1 <= x`;
          UNDISCH_TAC `x <= n + 1`;
          UNDISCH_TAC `1 <= x`;
          SUBGOAL_THEN `n - (x - 1) = (n + 1) - x` ASSUME_TAC THENL
           [MATCH_MP_TAC SUB_ADD_1; ALL_TAC] THEN
          ASM_SIMP_TAC []]] THEN
      ARITH_TAC]]);;

let LIM_NULL_COMPLEX_BOUND = prove
 (`!f g. eventually (\n. norm (f n) <= norm (g n)) net /\ (g --> Cx(&0)) net
         ==> (f --> Cx(&0)) net`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0; LIM_TRANSFORM_BOUND]);;

(*---------------------------------------------------------------------------*)
(*                       Integration in Time Domain                          *)
(*---------------------------------------------------------------------------*)

let INTEGRAL_BY_PARTS_LAPLACE_INTEG_INTEGRAND = prove
 (`!(f:real^1->complex) b s. &0 < Re s /\ laplace_exists f s /\
    laplace_exists (\x. integral (interval [lift (&0),x]) f) s /\
    (!x. f continuous_on interval [lift (&0),x]) 
    ==>
	 (integral (interval [lift (&0),lift (abs b)])
         (\t. (\t. integral (interval [lift (&0),t]) f) t *
              (\t. cexp (--(s * Cx (drop t)))) t) =
         (\t. integral (interval [lift (&0),t]) f) (lift (abs b)) *
         (\t. --inv s * cexp (--(s * Cx (drop t)))) (lift (abs b)) -
         (\t. integral (interval [lift (&0),t]) f) (lift (&0)) *
         (\t. --inv s * cexp (--(s * Cx (drop t)))) (lift (&0)) -
         integral (interval [lift (&0),lift (abs b)])
         (\x. f x * (\t. --inv s * cexp (--(s * Cx (drop t)))) x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_BY_PARTS_WITHIN THEN CONJ_TAC THENL
   [SIMP_TAC [LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC [GSYM IN_INTERVAL_1] THEN
    MATCH_MP_TAC INTEGRAL_HAS_VECTOR_DERIVATIVE THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `(\t. --(inv s) * cexp (--(s * Cx (drop t)))) =  (\x:real^1. (\x y . x * y) ((\t. --(inv s) ) x)
    ( (\t. cexp (--(s * Cx (drop t))) ) x))`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\t. cexp (--(s * Cx (drop t)))) t = ((\x y . x * y) ((\t. --(inv s) ) t)
    (--s * cexp (--(s * Cx (drop t))))) + ((\x y . x * y) (Cx (&0)) ((\t. cexp (--(s * Cx (drop t))) ) t))`
      ASSUME_TAC THENL
     [SIMP_TAC
        [COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; COMPLEX_MUL_ASSOC;
         COMPLEX_NEG_MUL2] THEN
      SUBGOAL_THEN `inv s * s = Cx(&1)` ASSUME_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [COMPLEX_MUL_LID]] THEN
      MATCH_MP_TAC COMPLEX_MUL_LINV THEN SIMP_TAC [COMPLEX_EQ] THEN
      SIMP_TAC [DE_MORGAN_THM; RE_CX] THEN DISJ1_TAC THEN
      MATCH_MP_TAC REAL_POS_NZ THEN ASM_SIMP_TAC [];
      ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN THEN
    SIMP_TAC [GSYM COMPLEX_VEC_0] THEN SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC [BILINEAR_X_MUL_Y]] THEN
    ONCE_REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC VECTOR_COMPLEX_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
      SIMP_TAC [HAS_COMPLEX_DERIVATIVE_CEXP]] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_LNEG] THEN
    SUBGOAL_THEN
      `((\t. --s * Cx (drop t)) has_vector_derivative --s) (at t within interval [lift (&0),lift (abs b)]) =
    ((\t. (\x y. x * y) ((\x:real^1. --s:complex) t) ((\x. Cx (drop x))  t)) has_vector_derivative
      (\x y. x * y) ((\x:real^1. --s:complex) t) (Cx (&1)) + (\x y. x * y) (Cx (&0)) ((\x. Cx (drop x))  t))
       (at t within interval [lift (&0),lift (abs b)])`
      ASSUME_TAC THENL
     [SIMP_TAC [] THEN
      SIMP_TAC [COMPLEX_MUL_RID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID];
      ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN THEN
    SIMP_TAC [GSYM COMPLEX_VEC_0] THEN SIMP_TAC [HAS_VECTOR_DERIVATIVE_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC [BILINEAR_X_MUL_Y]] THEN
    SUBGOAL_THEN `(\x. Cx (drop x)) =  Cx o (\x . x) o drop` ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN
    ONCE_REWRITE_TAC [LIFT_DROP] THEN ONCE_REWRITE_TAC [GSYM LIFT_DROP] THEN
    ONCE_REWRITE_TAC [GSYM HAS_CX_VECTOR_DERIVATIVE_WITHIN] THEN
    ONCE_REWRITE_TAC [LIFT_DROP] THEN REWRITE_TAC [HAS_REAL_DERIVATIVE_ID];
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN SIMP_TAC [] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN ASM_SIMP_TAC [] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN SIMP_TAC [CONTINUOUS_ON_CEXP] THEN
      SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      SIMP_TAC [CONTINUOUS_ON_CX_DROP1];
      SIMP_TAC [] THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        UNDISCH_TAC
          `laplace_exists (\x. integral (interval [lift (&0),x]) f) s` THEN
        REWRITE_TAC [laplace_exists] THEN ASM_SIMP_TAC [];
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [CONTINUOUS_ON_CEXP] THEN SIMP_TAC [GSYM COMPLEX_MUL_LNEG] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        SIMP_TAC [CONTINUOUS_ON_CONST] THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        SIMP_TAC [CONTINUOUS_ON_CX_DROP1]]]]);;

let LAPLACE_INTEGRAL = prove
 (`! (f:real^1->complex) (s:complex) .
    (&0  < (Re s)) /\ laplace_exists f s /\
    ( laplace_exists (\x. integral (interval [lift(&0) , x]) f) s )
    /\ (!x. f continuous_on  interval [lift (&0), x])
        ==>
    laplace_transform (\x. integral (interval [lift(&0) , x]) f) s =
       ( (Cx (&1) / s) * (laplace_transform f s)  )`,
  REPEAT GEN_TAC THEN REWRITE_TAC [laplace_transform] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t}
 (\t. cexp (--(s * Cx (drop t))) * integral (interval [lift (&0),t]) f) =
 lim at_posinfinity
 (\b. integral (interval [lift (&0),lift b])
      (\t. cexp (--(s * Cx (drop t))) * integral (interval [lift (&0),t]) (f:real^1->complex)))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LAPLACE_INTEGRAL_EQ_REP]; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t} (\t. cexp (--(s * Cx (drop t))) * f t) = lim at_posinfinity
 (\b. integral (interval [lift (&0),lift b])
      (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LAPLACE_INTEGRAL_EQ_REP]; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `lim at_posinfinity  (\b. integral (interval [lift (&0),lift b])
    (\t. cexp (--(s * Cx (drop t))) * integral (interval [lift (&0),t]) (f:real^1->complex))) =  
    lim at_posinfinity (\b.  (\b. integral (interval [lift (&0),lift b])
      (\t. cexp (--(s * Cx (drop t))) * integral (interval [lift (&0),t]) f)) (abs b))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LIM_ABS_LIM_EQ_LAPLACE]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `lim at_posinfinity  (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * (f:real^1->complex) t)) = 
    lim at_posinfinity (\b. (\b. integral (interval [lift (&0),lift b]) (\t. cexp (--(s * Cx (drop t))) * f t))  (abs b))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC [LIM_ABS_LIM_EQ_LAPLACE]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `!b. integral (interval [lift (&0),lift (abs b)]) (\t. (\t.integral (interval [lift (&0),t]) f) t *  (\t.cexp (--(s * Cx (drop t)))) t ) =
   (\t.integral (interval [lift (&0),t]) (f:real^1->complex)) (lift (abs b)) * (\t. --(inv s) *cexp (--(s * Cx (drop t)))) (lift (abs b)) -
     (\t.integral (interval [lift (&0),t]) f) (lift (&0)) * (\t. --(inv s) *cexp (--(s * Cx (drop t)))) (lift (&0)) -
      integral (interval [lift (&0),lift (abs b)]) (\x. f x *  (\t. --(inv s) * cexp (--(s * Cx (drop t)))) x)`
    ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC [INTEGRAL_BY_PARTS_LAPLACE_INTEG_INTEGRAND];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!b. integral (interval [lift (&0),lift (abs b)]) (\t. cexp (--(s * Cx (drop t))) * 
    integral (interval [lift (&0),t]) f) =  integral (interval [lift (&0),lift (abs b)]) 
      (\t. (\t. integral (interval [lift (&0),t]) f) t * (\t. cexp (--(s * Cx (drop t)))) t)`
    ASSUME_TAC THENL
   [SIMP_TAC [COMPLEX_MUL_AC]; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [] THEN
  SIMP_TAC
    [INTEGRAL_REFL; COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_SUB_RZERO] THEN
  SUBGOAL_THEN
    `lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)]) f * --inv s * cexp (--(s * Cx (drop (lift (abs b))))) -
   integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x))))) =
    lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)]) f * --inv s * cexp (--(s * Cx (drop (lift (abs b)))))) - 
     lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x)))))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TENDSTO_LIM THEN SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
    SUBGOAL_THEN
      `!b. integral (interval [lift (&0),lift (abs b)]) f * --inv s * cexp (--(s * Cx (drop (lift (abs b))))) -
    integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x)))) =
     (\b. integral (interval [lift (&0),lift (abs b)]) f *  --inv s * cexp (--(s * Cx (drop (lift (abs b)))))) b - 
       (\b. integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x))))) b`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_REWRITE_TAC [] THEN MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THEN
    SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THENL
     [ALL_TAC;
      SUBGOAL_THEN
        `!b. integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x)))) = --inv s *
    integral (interval [lift (&0),lift (abs b)]) (\x. cexp (--(s * Cx (drop x))) * f x)`
        ASSUME_TAC THENL
       [GEN_TAC THEN
        SUBGOAL_THEN
          `!x. f x * --inv s * cexp (--(s * Cx (drop x))) = --inv s * (\t. cexp (--(s * Cx (drop t))) * f t ) x`
          ASSUME_TAC THENL
         [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COMPLEX_INTEGRAL_CMUL THEN
        MATCH_MP_TAC LAPLACE_EXISTS_INTEGRABLE THEN ONCE_ASM_REWRITE_TAC [];
        ONCE_ASM_REWRITE_TAC [] THEN
        EXISTS_TAC
          `--inv s * lim at_posinfinity (\b. integral (interval [lift (&0),lift (b)])
    (\x. cexp (--(s * Cx (drop x))) * f x))` THEN
        MATCH_MP_TAC LIM_COMPLEX_LMUL THEN MATCH_MP_TAC LIM_ABS_LIM_1 THEN
        SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
        MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN ONCE_ASM_REWRITE_TAC []]] THEN
    EXISTS_TAC `--inv(s) * Cx(&0)` THEN
    SUBGOAL_THEN
      `!b.integral (interval [lift (&0),lift (abs b)]) f * --inv s *
     cexp (--(s * Cx (drop (lift (abs b))))) =  --inv s * (integral (interval [lift (&0),lift (abs b)]) f *
        cexp (--(s * Cx (drop (lift (abs b))))))`
      ASSUME_TAC THENL
     [SIMP_TAC [COMPLEX_MUL_AC]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
    MATCH_MP_TAC LIM_ABS_LIM_1 THEN SIMP_TAC [LIFT_DROP] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_BOUND THEN UNDISCH_TAC `laplace_exists f s` THEN
    REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `?b. (drop b) < Re s /\ (!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp ( (drop b) * t)) /\
      ~( (drop b) = &0)`
      ASSUME_TAC THENL
     [EXISTS_TAC
        `if ~((drop a) = --(Re s)) then lift(((drop a) + (Re s)) / &2) else lift(drop a)` THEN
      SIMP_TAC [LIFT_DROP] THEN CONJ_TAC THENL
       [COND_CASES_TAC THENL
         [SIMP_TAC [LIFT_DROP] THEN
          SUBGOAL_THEN
            `((((drop a) + Re s) / &2) < Re s) = (((drop a) + Re s) < (Re s * &2))`
            ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LT_LDIV_EQ THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          SIMP_TAC
            [REAL_ARITH `((a + b) < (b * &2)) = ((a-b) < &0)`;
             REAL_ARITH `((a - b) < &0) = (a < b)`] THEN
          ASM_MESON_TAC [real_gt];
          ONCE_ASM_REWRITE_TAC [] THEN
          SIMP_TAC [REAL_ARITH `(--x < x) <=> (&0 < x)`] THEN
          ONCE_ASM_REWRITE_TAC []];
        CONJ_TAC THEN COND_CASES_TAC THENL
         [SIMP_TAC [LIFT_DROP] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * exp (drop a * t)` THEN
          UNDISCH_TAC
            `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
          DISCH_THEN (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC [] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC []; ALL_TAC] THEN
          SIMP_TAC [REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC []] THEN
          SIMP_TAC [REAL_ARITH `(a <= (a + b) / &2) = (a <= b)`] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC [real_gt];
          REPEAT STRIP_TAC THEN
          UNDISCH_TAC
            `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
          DISCH_THEN (MP_TAC o SPEC `t:real`);
          SIMP_TAC [LIFT_DROP] THEN
          SIMP_TAC [REAL_ARITH `(((a + b ) / &2) = &0) =  (a = --b)`];
          SIMP_TAC [REAL_NOT_EQ] THEN DISJ1_TAC THEN ASM_SIMP_TAC [] THEN
          ONCE_REWRITE_TAC [REAL_NEG_LT0]] THEN
        ASM_SIMP_TAC []];
      ALL_TAC] THEN
    UNDISCH_TAC
      `?b. (drop b) < Re s /\ (!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp ( (drop b) * t)) /\
      ~( (drop b) = &0)` THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC
      `(\t. Cx(drop (integral (interval [lift (&0),lift (t)])  (\t. lift (M * exp ((drop b) * (drop (t)) ))) )) *
      cexp (--(s * Cx(t))))` THEN
    CONJ_TAC THENL
     [SIMP_TAC [COMPLEX_NORM_MUL; NORM_CEXP] THEN
      SUBGOAL_THEN
        `!n. (norm (integral (interval [lift (&0),lift n]) (f:real^1->complex)) *
   exp (Re (--(s * Cx n))) <=  norm (Cx ( drop ( integral (interval [lift (&0),lift n])
      (\t. lift (M * exp ((drop b) * drop t)))))) * exp (Re (--(s * Cx n)))) =
    (norm (integral (interval [lift (&0),lift n]) f)  <= norm (Cx(drop(integral (interval [lift (&0),lift n])
      (\t. lift (M * exp ((drop b) * drop t)))))) )`
        ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
        SIMP_TAC [REAL_EXP_POS_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN SIMP_TAC [COMPLEX_NORM_CX] THEN
      SUBGOAL_THEN
        `!n.norm (integral (interval [lift (&0),lift n]) (f:real^1->real^2)) <=
     abs (drop (integral (interval [lift (&0),lift n]) (\t. lift (M * exp ((drop b) * drop t)))))`
        ASSUME_TAC THENL
       [ALL_TAC; ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [EVENTUALLY_TRUE]] THEN
      GEN_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_SPEC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
          `(\t. lift (M * exp (drop b * drop t))) = lift o (\t. M * exp(drop b * t)) o drop`
          ASSUME_TAC THENL
         [SIMP_TAC [o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [GSYM REAL_CONTINUOUS_ON] THEN SIMP_TAC [LIFT_DROP] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_EXP] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_ID];
        SIMP_TAC [LIFT_DROP; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
        UNDISCH_TAC
          `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop b * t)` THEN
        DISCH_THEN (MP_TAC o SPEC `drop x`) THEN ASM_SIMP_TAC [LIFT_DROP]];
      REWRITE_TAC [GSYM COMPLEX_VEC_0] THEN ONCE_REWRITE_TAC [LIM_NULL_NORM] THEN
      SIMP_TAC [COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      REWRITE_TAC [LIFT_VEC_0; GSYM TENDSTO_REAL] THEN
      SUBGOAL_THEN
        `!x.(drop  (integral (interval [lift (&0),lift x]) (\t. lift (M * exp (drop b * drop t))))) = 
     real_integral (real_interval [&0,x]) (\t. M * exp(drop b * t))`
        ASSUME_TAC THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN
        SIMP_TAC [INTERVAL_REAL_INTERVAL; LIFT_DROP] THEN
        SUBGOAL_THEN
          `(\t. lift (M * exp (drop b * drop t))) = lift o (\t. M * exp(drop b * t)) o drop`
          ASSUME_TAC THENL
         [SIMP_TAC [o_DEF]; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_EXP] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_ABS_LIM THEN
      SIMP_TAC [] THEN
      SUBGOAL_THEN
        `!i. ((\t. M * exp (drop b * t)) has_real_integral  ((\t. M * inv (drop b) * exp (drop b * t))(abs i) - 
    (\t. M * inv (drop b) * exp (drop b * t)) (&0))) (real_interval [&0,abs i])`
        ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
        SIMP_TAC [] THEN
        SUBGOAL_THEN
          `!t.  M * inv (drop b) * exp (drop b * t) = M * (\t.inv (drop b) * exp (drop b * t)) t`
          ASSUME_TAC THENL
         [SIMP_TAC []; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
        SUBGOAL_THEN
          `exp (drop b * x) = (\x. inv (drop b)) x * ((drop b) *  exp (drop b * x)) +
    (&0) * (\t.exp (drop b * t)) x`
          ASSUME_TAC THENL
         [SIMP_TAC [REAL_MUL_LZERO; REAL_ADD_RID] THEN
          SUBGOAL_THEN `inv (drop b) * drop b = &1` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC [];
            SIMP_TAC [REAL_MUL_ASSOC] THEN ASM_SIMP_TAC [] THEN
            SIMP_TAC [REAL_MUL_LID]];
          SUBGOAL_THEN
            `!t. inv (drop b) * exp (drop b * t) = (\t. inv (drop b) ) t * (\t. exp (drop b * t) ) t`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN
          SIMP_TAC [HAS_REAL_DERIVATIVE_CONST] THEN
          ONCE_REWRITE_TAC [GSYM o_DEF; REAL_MUL_AC] THEN
          MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
           [ALL_TAC;
            MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
            SIMP_TAC [HAS_REAL_DERIVATIVE_EXP]] THEN
          SUBGOAL_THEN
            `drop b = (\t:real. drop b) x * &1 + &0 * (\t:real. t) x`
            ASSUME_TAC THENL
           [SIMP_TAC [REAL_MUL_LZERO; REAL_MUL_RID; REAL_ADD_RID]; ALL_TAC] THEN
          SUBGOAL_THEN `!t. drop b * t = (\t. drop b) t * (\t:real. t) t`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN
          SIMP_TAC [HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID]];
        SUBGOAL_THEN
          `!i. real_integral (real_interval [&0,abs i]) (\t. M * exp (drop b * t)) = 
     (\t. M * inv (drop b) * exp (drop b * t)) (abs i) - (\t. M * inv (drop b) * exp (drop b * t)) (&0)`
          ASSUME_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
          ONCE_ASM_REWRITE_TAC [];
          ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        SIMP_TAC [REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
        ONCE_REWRITE_TAC [GSYM REAL_ABS_EXP] THEN
        ONCE_REWRITE_TAC [GSYM REAL_ABS_MUL] THEN
        ONCE_REWRITE_TAC [REAL_ABS_EXP] THEN
        MATCH_MP_TAC ABS_LIM_ZERO_POSINFINTY THEN
        ONCE_REWRITE_TAC [REAL_SUB_RDISTRIB] THEN
        SUBGOAL_THEN
          `!i. (M * inv (drop b) * exp (drop b * abs i)) * exp (Re (--(s * Cx (abs i)))) - (M * inv (drop b)) *
     exp (Re (--(s * Cx (abs i))))  = (M * inv (drop b)) * ( (exp (drop b * abs i) * exp (Re (--(s * Cx (abs i)))))
       - exp (Re (--(s * Cx (abs i)))))`
          ASSUME_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [REAL_ARITH `&0 =  (M * inv (drop b)) * &0`] THEN
        MATCH_MP_TAC REALLIM_LMUL THEN
        ONCE_REWRITE_TAC [REAL_ARITH `&0 = &0 - &0`] THEN
        MATCH_MP_TAC REALLIM_SUB THEN ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
        SIMP_TAC [RE_NEG; GSYM COMPLEX_CMUL; RE_CMUL] THEN CONJ_TAC THENL
         [SIMP_TAC [GSYM REAL_EXP_ADD; GSYM real_sub] THEN
          SUBGOAL_THEN
            `!i.drop b * abs i - abs i * Re s = --((Re s - drop b) * abs i)`
            ASSUME_TAC THENL
           [REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
          MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN
          SIMP_TAC [real_sub; GSYM REAL_LT_LNEG; REAL_LT_NEG] THEN
          ONCE_ASM_REWRITE_TAC [];
          ONCE_REWRITE_TAC [REAL_MUL_AC] THEN MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
          MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN ONCE_ASM_REWRITE_TAC []]]];
    ONCE_ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `lim at_posinfinity  (\b. integral (interval [lift (&0),lift (abs b)]) f *
    --inv s * cexp (--(s * Cx (drop (lift (abs b)))))) = --inv s * Cx(&0)`
      ASSUME_TAC THENL
     [ALL_TAC;
      ONCE_ASM_REWRITE_TAC [] THEN
      SIMP_TAC [COMPLEX_MUL_RZERO; COMPLEX_SUB_LZERO] THEN
      SUBGOAL_THEN
        `lim at_posinfinity
   (\b. integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x))))) =
     --inv s * lim at_posinfinity (\b. integral (interval [lift (&0),lift (abs b)]) (\x. cexp (--(s * Cx (drop x))) *  f x ))`
        ASSUME_TAC THENL
       [ALL_TAC;
        ONCE_ASM_REWRITE_TAC [] THEN
        SIMP_TAC
          [COMPLEX_NEG_LMUL; COMPLEX_NEG_NEG; complex_div; COMPLEX_MUL_LID]] THEN
      MATCH_MP_TAC TENDSTO_LIM THEN SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
      SUBGOAL_THEN
        `!b. integral (interval [lift (&0),lift (abs b)]) (\x. f x * --inv s * cexp (--(s * Cx (drop x)))) = --inv s *
    integral (interval [lift (&0),lift (abs b)]) (\x. cexp (--(s * Cx (drop x))) * f x)`
        ASSUME_TAC THENL
       [GEN_TAC THEN
        SUBGOAL_THEN
          `!x. f x * --inv s * cexp (--(s * Cx (drop x))) = --inv s * (\t. cexp (--(s * Cx (drop t))) * f t ) x`
          ASSUME_TAC THENL
         [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COMPLEX_INTEGRAL_CMUL THEN
        MATCH_MP_TAC LAPLACE_EXISTS_INTEGRABLE THEN ONCE_ASM_REWRITE_TAC [];
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
        SIMP_TAC [GSYM FUN_LIM] THEN REWRITE_TAC [convergent_f] THEN
        EXISTS_TAC
          `lim at_posinfinity (\b. integral (interval [lift (&0),lift (b)])
     (\x. cexp (--(s * Cx (drop x))) * f x))` THEN
        MATCH_MP_TAC LIM_ABS_LIM_1 THEN SIMP_TAC [GSYM FUN_LIM] THEN
        REWRITE_TAC [convergent_f] THEN MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN
        ONCE_ASM_REWRITE_TAC []]] THEN
    MATCH_MP_TAC TENDSTO_LIM THEN SIMP_TAC [TRIVIAL_LIMIT_AT_POSINFINITY] THEN
    SUBGOAL_THEN
      `!b.integral (interval [lift (&0),lift (abs b)]) f * --inv s *
     cexp (--(s * Cx (drop (lift (abs b))))) =  --inv s * (integral (interval [lift (&0),lift (abs b)]) f *
        cexp (--(s * Cx (drop (lift (abs b))))))`
      ASSUME_TAC THENL
     [SIMP_TAC [COMPLEX_MUL_AC]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LIM_COMPLEX_LMUL THEN
    MATCH_MP_TAC LIM_ABS_LIM_1 THEN SIMP_TAC [LIFT_DROP] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_BOUND THEN UNDISCH_TAC `laplace_exists f s` THEN
    REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `?b. (drop b) < Re s /\ (!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp ( (drop b) * t)) /\
      ~( (drop b) = &0)`
      ASSUME_TAC THENL
     [EXISTS_TAC
        `if ~((drop a) = --(Re s)) then lift(((drop a) + (Re s)) / &2) else lift(drop a)` THEN
      SIMP_TAC [LIFT_DROP] THEN CONJ_TAC THENL
       [COND_CASES_TAC THENL
         [SIMP_TAC [LIFT_DROP] THEN
          SUBGOAL_THEN
            `((((drop a) + Re s) / &2) < Re s) = (((drop a) + Re s) < (Re s * &2))`
            ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LT_LDIV_EQ THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          SIMP_TAC
            [REAL_ARITH `((a + b) < (b * &2)) = ((a-b) < &0)`;
             REAL_ARITH `((a - b) < &0) = (a < b)`] THEN
          ASM_MESON_TAC [real_gt];
          ONCE_ASM_REWRITE_TAC [] THEN
          SIMP_TAC [REAL_ARITH `(--x < x) <=> (&0 < x)`] THEN
          ONCE_ASM_REWRITE_TAC []];
        CONJ_TAC THEN COND_CASES_TAC THENL
         [SIMP_TAC [LIFT_DROP] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * exp (drop a * t)` THEN
          UNDISCH_TAC
            `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
          DISCH_THEN (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC [] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC []; ALL_TAC] THEN
          SIMP_TAC [REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC []] THEN
          SIMP_TAC [REAL_ARITH `(a <= (a + b) / &2) = (a <= b)`] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC [real_gt];
          REPEAT STRIP_TAC THEN
          UNDISCH_TAC
            `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
          DISCH_THEN (MP_TAC o SPEC `t:real`);
          SIMP_TAC [LIFT_DROP] THEN
          SIMP_TAC [REAL_ARITH `(((a + b ) / &2) = &0) =  (a = --b)`];
          SIMP_TAC [REAL_NOT_EQ] THEN DISJ1_TAC THEN ASM_SIMP_TAC [] THEN
          ONCE_REWRITE_TAC [REAL_NEG_LT0]] THEN
        ASM_SIMP_TAC []];
      ALL_TAC] THEN
    UNDISCH_TAC
      `?b. (drop b) < Re s /\ (!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp ( (drop b) * t)) /\
      ~( (drop b) = &0)` THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC
      `(\t. Cx(drop (integral (interval [lift (&0),lift (t)])  (\t. lift (M * exp ((drop b) * (drop (t)) ))) )) *
      cexp (--(s * Cx(t))))` THEN
    CONJ_TAC THENL
     [SIMP_TAC [COMPLEX_NORM_MUL; NORM_CEXP] THEN
      SUBGOAL_THEN
        `!n. (norm (integral (interval [lift (&0),lift n]) (f:real^1->complex)) *
   exp (Re (--(s * Cx n))) <=  norm (Cx ( drop ( integral (interval [lift (&0),lift n])
      (\t. lift (M * exp ((drop b) * drop t)))))) * exp (Re (--(s * Cx n)))) =
    (norm (integral (interval [lift (&0),lift n]) f)  <= norm (Cx(drop(integral (interval [lift (&0),lift n])
      (\t. lift (M * exp ((drop b) * drop t)))))) )`
        ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
        SIMP_TAC [REAL_EXP_POS_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN SIMP_TAC [COMPLEX_NORM_CX] THEN
      SUBGOAL_THEN
        `!n.norm (integral (interval [lift (&0),lift n]) (f:real^1->real^2)) <=
     abs (drop (integral (interval [lift (&0),lift n]) (\t. lift (M * exp ((drop b) * drop t)))))`
        ASSUME_TAC THENL
       [ALL_TAC; ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC [EVENTUALLY_TRUE]] THEN
      GEN_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_SPEC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
          `(\t. lift (M * exp (drop b * drop t))) = lift o (\t. M * exp(drop b * t)) o drop`
          ASSUME_TAC THENL
         [SIMP_TAC [o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC [INTERVAL_REAL_INTERVAL] THEN ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [GSYM REAL_CONTINUOUS_ON] THEN SIMP_TAC [LIFT_DROP] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_EXP] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_ID];
        SIMP_TAC [LIFT_DROP; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
        UNDISCH_TAC
          `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop b * t)` THEN
        DISCH_THEN (MP_TAC o SPEC `drop x`) THEN ASM_SIMP_TAC [LIFT_DROP]];
      REWRITE_TAC [GSYM COMPLEX_VEC_0] THEN ONCE_REWRITE_TAC [LIM_NULL_NORM] THEN
      SIMP_TAC [COMPLEX_NORM_MUL; NORM_CEXP; COMPLEX_NORM_CX] THEN
      ONCE_REWRITE_TAC [GSYM o_DEF] THEN
      REWRITE_TAC [LIFT_VEC_0; GSYM TENDSTO_REAL] THEN
      SUBGOAL_THEN
        `!x.(drop  (integral (interval [lift (&0),lift x]) (\t. lift (M * exp (drop b * drop t))))) = 
     real_integral (real_interval [&0,x]) (\t. M * exp(drop b * t))`
        ASSUME_TAC THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN
        SIMP_TAC [INTERVAL_REAL_INTERVAL; LIFT_DROP] THEN
        SUBGOAL_THEN
          `(\t. lift (M * exp (drop b * drop t))) = lift o (\t. M * exp(drop b * t)) o drop`
          ASSUME_TAC THENL
         [SIMP_TAC [o_DEF]; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_INTEGRAL THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        ONCE_REWRITE_TAC [GSYM o_DEF] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_EXP] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
        SIMP_TAC [REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_ABS_LIM THEN
      SIMP_TAC [] THEN
      SUBGOAL_THEN
        `!i. ((\t. M * exp (drop b * t)) has_real_integral  ((\t. M * inv (drop b) * exp (drop b * t))(abs i) - 
    (\t. M * inv (drop b) * exp (drop b * t)) (&0))) (real_interval [&0,abs i])`
        ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
        SIMP_TAC [] THEN
        SUBGOAL_THEN
          `!t.  M * inv (drop b) * exp (drop b * t) = M * (\t.inv (drop b) * exp (drop b * t)) t`
          ASSUME_TAC THENL
         [SIMP_TAC []; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
        SUBGOAL_THEN
          `exp (drop b * x) = (\x. inv (drop b)) x * ((drop b) *  exp (drop b * x)) +
    (&0) * (\t.exp (drop b * t)) x`
          ASSUME_TAC THENL
         [SIMP_TAC [REAL_MUL_LZERO; REAL_ADD_RID] THEN
          SUBGOAL_THEN `inv (drop b) * drop b = &1` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC [];
            SIMP_TAC [REAL_MUL_ASSOC] THEN ASM_SIMP_TAC [] THEN
            SIMP_TAC [REAL_MUL_LID]];
          SUBGOAL_THEN
            `!t. inv (drop b) * exp (drop b * t) = (\t. inv (drop b) ) t * (\t. exp (drop b * t) ) t`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN
          SIMP_TAC [HAS_REAL_DERIVATIVE_CONST] THEN
          ONCE_REWRITE_TAC [GSYM o_DEF; REAL_MUL_AC] THEN
          MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
           [ALL_TAC;
            MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
            SIMP_TAC [HAS_REAL_DERIVATIVE_EXP]] THEN
          SUBGOAL_THEN
            `drop b = (\t:real. drop b) x * &1 + &0 * (\t:real. t) x`
            ASSUME_TAC THENL
           [SIMP_TAC [REAL_MUL_LZERO; REAL_MUL_RID; REAL_ADD_RID]; ALL_TAC] THEN
          SUBGOAL_THEN `!t. drop b * t = (\t. drop b) t * (\t:real. t) t`
            ASSUME_TAC THENL
           [SIMP_TAC []; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN
          SIMP_TAC [HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID]];
        SUBGOAL_THEN
          `!i. real_integral (real_interval [&0,abs i]) (\t. M * exp (drop b * t)) = 
     (\t. M * inv (drop b) * exp (drop b * t)) (abs i) - (\t. M * inv (drop b) * exp (drop b * t)) (&0)`
          ASSUME_TAC THENL
         [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
          ONCE_ASM_REWRITE_TAC [];
          ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        SIMP_TAC [REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
        ONCE_REWRITE_TAC [GSYM REAL_ABS_EXP] THEN
        ONCE_REWRITE_TAC [GSYM REAL_ABS_MUL] THEN
        ONCE_REWRITE_TAC [REAL_ABS_EXP] THEN
        MATCH_MP_TAC ABS_LIM_ZERO_POSINFINTY THEN
        ONCE_REWRITE_TAC [REAL_SUB_RDISTRIB] THEN
        SUBGOAL_THEN
          `!i. (M * inv (drop b) * exp (drop b * abs i)) * exp (Re (--(s * Cx (abs i)))) - (M * inv (drop b)) *
     exp (Re (--(s * Cx (abs i))))  = (M * inv (drop b)) * ( (exp (drop b * abs i) * exp (Re (--(s * Cx (abs i)))))
       - exp (Re (--(s * Cx (abs i)))))`
          ASSUME_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [REAL_ARITH `&0 =  (M * inv (drop b)) * &0`] THEN
        MATCH_MP_TAC REALLIM_LMUL THEN
        ONCE_REWRITE_TAC [REAL_ARITH `&0 = &0 - &0`] THEN
        MATCH_MP_TAC REALLIM_SUB THEN ONCE_REWRITE_TAC [COMPLEX_MUL_AC] THEN
        SIMP_TAC [RE_NEG; GSYM COMPLEX_CMUL; RE_CMUL] THEN CONJ_TAC THENL
         [SIMP_TAC [GSYM REAL_EXP_ADD; GSYM real_sub] THEN
          SUBGOAL_THEN
            `!i.drop b * abs i - abs i * Re s = --((Re s - drop b) * abs i)`
            ASSUME_TAC THENL
           [REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
          MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN
          SIMP_TAC [real_sub; GSYM REAL_LT_LNEG; REAL_LT_NEG] THEN
          ONCE_ASM_REWRITE_TAC [];
          ONCE_REWRITE_TAC [REAL_MUL_AC] THEN MATCH_MP_TAC REALLIM_ABS_LIM_1 THEN
          MATCH_MP_TAC EXP_A_TENDSTO_0_INFINITY THEN ONCE_ASM_REWRITE_TAC []]]]]);;

(*---------------------------------------------------------------------------*)
(*                          Some useful theorems                             *)
(*---------------------------------------------------------------------------*)

let LAPLACE_SECOND_ORDER_DERIV = prove
 (`!f:real^1->complex s:complex . 
   laplace_exists_higher_deriv 2 f s /\
    (!x. differentiable_higher_derivative 2 f x) ==>   
     laplace_transform (\t. vector_derivative (\x. vector_derivative f (at x)) (at t)) s = 
      s pow 2 * laplace_transform f s - vsum (1..2)(\x. s pow (x - 1) * higher_vector_derivative (2 - x) f (lift (&0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`f:real^1->complex`; `s:complex`; `2`]
       LAPLACE_HIGHER_DIFF_F_THEOREM_AT_CORRECT) THEN
  ASM_SIMP_TAC [] THEN SIMP_TAC [TWO; ONE] THEN
  REWRITE_TAC [higher_vector_derivative] THEN
  REWRITE_TAC [ETA_AX; GSYM ONE; GSYM TWO]);;

(*---------------------------------------------------------------------------*)
(*                               Time Shifting                               *)
(*---------------------------------------------------------------------------*)

let shifted_unit_step = define `shifted_unit_step t0 =  
  (\t. if t IN  {t | drop t0 <= drop t} then Cx (&1) else Cx(&0))`;;

let shifted_fun = define `shifted_fun f t0 =  
  (\t. f (t - t0) * (shifted_unit_step t0) t)`;;

let LAPLACE_TIME_SHIFTING = prove
 (`!(f:real^1->complex) s t0.
    &0 <= drop t0 /\ laplace_exists f s ==> 
      (laplace_transform (shifted_fun f t0) s = 
       (laplace_transform f s) * cexp (--(s * Cx (drop t0))) )`,
  REWRITE_TAC
    [shifted_fun; shifted_unit_step; laplace_exists; laplace_transform] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t}
 (\t. cexp (--(s * Cx (drop t))) *
      f (t - t0) *
      (if t IN {t | drop t0 <= drop t} then Cx (&1) else Cx (&0))) =
      integral {t | drop t0 <= drop t}
 (\t. cexp (--(s * Cx (drop t))) *
      f (t - t0) )`
    ASSUME_TAC THENL
   [SUBGOAL_THEN
      `!t. (cexp (--(s * Cx (drop t))) *
       f (t - t0) *
       (if t IN {t | drop t0 <= drop t} then Cx (&1) else Cx (&0))) =
       (if t IN {t | drop t0 <= drop t} then cexp (--(s * Cx (drop t))) * f (t - t0) else Cx (&0))`
      ASSUME_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC [] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC INTEGRAL_RESTRICT THEN
    REWRITE_TAC [SUBSET] THEN
    REWRITE_TAC
      [EXTENSION; FORALL_LIFT; IN_INTER; IN_INTERVAL_1; LIFT_DROP;
       IN_ELIM_THM] THEN
    asm_conv_tac_real_field;
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `integral {t | drop t0 <= drop t}
      (\t. (\t. cexp (--(s * Cx (drop (t + t0)))) * (f:real^1->complex) t) (--t0 + t)) =  integral (IMAGE (\t. --t0 + t) {t | drop t0 <= drop t}) (\t. cexp (--(s * Cx (drop (t + t0)))) * (f:real^1->complex) t)`
    ASSUME_TAC THENL
   [SIMP_TAC [GSYM INTEGRAL_TRANSLATION]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC [] THEN
  REWRITE_TAC [VECTOR_ARITH `((--t0 + t) + t0) = t:real^1`] THEN
  SUBGOAL_THEN `!t. (--t0 + t) = (t - t0:real^1)` ASSUME_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [] THEN
  DISCH_THEN (K ALL_TAC) THEN
  SUBGOAL_THEN `!t.(t - t0:real^1) = (--t0 + t)` ASSUME_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `IMAGE (\t. --t0 + t)  {t | drop t0 <= drop t} = {t | &0 <= drop t}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC [IN_ELIM_THM; DROP_ADD; LIFT_DROP; REAL_LE_ADDR] THEN
    REPEAT STRIP_TAC THENL
     [EXISTS_TAC `(y:real^1) + t0` THEN VECTOR_ARITH_TAC;
      REWRITE_TAC [DROP_NEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [DROP_ADD; CX_ADD; COMPLEX_ADD_LDISTRIB] THEN
  SUBGOAL_THEN
    `!t. (--(s * Cx (drop t) + s * Cx (drop t0))) = ((--(s * Cx (drop t))) + (--(s * Cx (drop t0))))`
    ASSUME_TAC THENL
   [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC [CEXP_ADD] THEN
  ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
  REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `((f:real^1->complex) t * cexp (--(s * Cx (drop t))) * cexp (--(s * Cx (drop t0)))) = ( cexp (--(s * Cx (drop t0))) * (cexp (--(s * Cx (drop t))) * f t))`] THEN
  MATCH_MP_TAC INTEGRAL_COMPLEX_MUL THEN
  REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM LIFT_NUM] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [SIMP_TAC [CEXP_S_T_CONTINUOUS]; ALL_TAC] THEN
    MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `drop (a':real^1)`) THEN
    REWRITE_TAC [LIFT_DROP];
    REWRITE_TAC [GSYM LIFT_NUM] THEN MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN
    ASM_SIMP_TAC [laplace_exists] THEN EXISTS_TAC `M:real` THEN
    EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC []]);;

(*---------------------------------------------------------------------------*)
(*                          Some useful theorems                             *)
(*---------------------------------------------------------------------------*)

let HAS_INTEGRAL_AFFINITY_ALT = prove
 (`!(f:real^1->complex) i s a. 
    ~(a = &0)  
        ==>
     (((\x. f (a % x)) has_integral i) s <=>
     (f has_integral abs a % i) (IMAGE (\x. a % x) s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN
      `!(f:real^1->real^2) i s m c.
         (f has_integral i) s /\ ~(m = &0)
         ==> ((\x. f (m % x + c)) has_integral
              inv (abs m pow dimindex (:1)) % i)
             (IMAGE (\x. inv m % x + --(inv m % c)) s)`
      ASSUME_TAC THENL
     [REWRITE_TAC [HAS_INTEGRAL_AFFINITY]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    DISCH_THEN (MP_TAC o SPEC `(\x. (f:real^1->real^2) (a % x))`) THEN
    DISCH_THEN (MP_TAC o SPEC `(i:real^2)`) THEN
    DISCH_THEN (MP_TAC o SPEC `s:real^1->bool`) THEN
    DISCH_THEN (MP_TAC o SPEC `inv (a:real)`) THEN
    DISCH_THEN (MP_TAC o SPEC `vec 0:real^1`) THEN ASM_SIMP_TAC [] THEN
    REWRITE_TAC [DIMINDEX_1; REAL_POW_1] THEN REWRITE_TAC [REAL_INV_INV] THEN
    REWRITE_TAC [VECTOR_ARITH `(x + vec 0:real^1) = (x)`] THEN
    REWRITE_TAC [REAL_ABS_INV; REAL_INV_INV] THEN
    REWRITE_TAC [VECTOR_ARITH `(a % vec 0:real^1) = (vec 0)`] THEN
    REWRITE_TAC [VECTOR_ARITH `(x + --(vec 0:real^1)) = (x)`] THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(a * inv a) = &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC [REAL_MUL_RINV]; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [VECTOR_ARITH `(&1 % x:real^1) = x`] THEN
    REWRITE_TAC [ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(a = &0)` THEN SIMPLE_COMPLEX_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN
      `!(f:real^1->real^2) i s m c.
         (f has_integral i) s /\ ~(m = &0)
         ==> ((\x. f (m % x + c)) has_integral
              inv (abs m pow dimindex (:1)) % i)
             (IMAGE (\x. inv m % x + --(inv m % c)) s)`
      ASSUME_TAC THENL
     [REWRITE_TAC [HAS_INTEGRAL_AFFINITY]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN DISCH_THEN (MP_TAC o SPEC `(f:real^1->real^2)`) THEN
    DISCH_THEN (MP_TAC o SPEC `abs a % (i:real^2)`) THEN
    DISCH_THEN (MP_TAC o SPEC `(IMAGE (\x. a % x) (s:real^1->bool))`) THEN
    DISCH_THEN (MP_TAC o SPEC `(a:real)`) THEN
    DISCH_THEN (MP_TAC o SPEC `vec 0:real^1`) THEN ASM_SIMP_TAC [] THEN
    REWRITE_TAC [DIMINDEX_1; REAL_POW_1] THEN
    REWRITE_TAC [VECTOR_ARITH `(a % x + vec 0:real^1) = a % x`] THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(inv (abs a) * abs a) = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN UNDISCH_TAC `~(a = &0)` THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [VECTOR_ARITH `(&1 % i:real^2) = i`] THEN
    REWRITE_TAC [VECTOR_ARITH `(inv a % vec 0:real^1) = (vec 0)`] THEN
    REWRITE_TAC [VECTOR_ARITH `(x + --(vec 0:real^1)) = (x)`] THEN
    SUBGOAL_THEN
      `(IMAGE (\x. inv a % x) (IMAGE (\x. a % x) s)) = (s:real^1->bool)`
      ASSUME_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC []] THEN
    REWRITE_TAC [EXTENSION; IN_UNION; IN_IMAGE; IN_UNIV; IN_ELIM_THM; IN] THEN
    STRIP_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN `inv a % a % x'' = x'':real^1` ASSUME_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC []] THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(inv a * a) = &1` ASSUME_TAC THENL
       [ASM_SIMP_TAC [REAL_MUL_LINV];
        ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN VECTOR_ARITH_TAC];
      STRIP_TAC THEN EXISTS_TAC `a % x:real^1` THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(inv a * a) = &1` ASSUME_TAC THENL
       [ASM_SIMP_TAC [REAL_MUL_LINV]; ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN STRIP_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `x:real^1` THEN ASM_SIMP_TAC []]]);;

let INTEGRABLE_AFFINITY_ALT = prove
 (`!(f:real^1->real^2) s a. 
    ~(a = &0)  
        /\
     (\x. f (a % x)) integrable_on s ==>
     (f integrable_on IMAGE (\x. a % x) s)`,
  REWRITE_TAC [integrable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `abs a % y:real^2` THEN
  ASM_SIMP_TAC [GSYM HAS_INTEGRAL_AFFINITY_ALT]);;

let INTEGRABLE_AFFINITY_ALT_EQ = prove
 (`!(f:real^1->real^2) s a. 
    ~(a = &0)  
        ==>
     ((\x. f (a % x)) integrable_on s <=>
     (f integrable_on IMAGE (\x. a % x) s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_SIMP_TAC [INTEGRABLE_AFFINITY_ALT]; ALL_TAC] THEN
  REWRITE_TAC [integrable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `abs (inv a) % y:real^2` THEN
  MP_TAC
    (ISPECL
       [`(f:real^1->real^2)`; `abs (inv a) % y:real^2`; `(s:real^1->bool)`;
        `a:real`]
       HAS_INTEGRAL_AFFINITY_ALT) THEN
  ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC EQ_IMP THEN strip_operand_function THEN
  REWRITE_TAC [COMPLEX_CMUL] THEN REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `(y = Cx (abs a * abs (inv a)) * y) = (Cx (&1) * y = Cx (abs a * abs (inv a)) * y)`] THEN
  strip_operand_function THEN AP_TERM_TAC THEN
  REWRITE_TAC [GSYM REAL_ABS_MUL] THEN MP_TAC (SPEC `a:real` REAL_MUL_RINV) THEN
  ASM_SIMP_TAC [] THEN REAL_ARITH_TAC);;

let INTEGRAL_AFFINITY_ALT = prove
 (`!f:real^1->real^2 s a. 
       ~(a = &0) /\ ((\x. f (a % x)) integrable_on s)
        ==>
           (integral s (\x. f (a % x)) = 
            integral (IMAGE (\x. a % x) s) (\x. inv (abs a) % f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC [HAS_INTEGRAL_AFFINITY_ALT] THEN
  SUBGOAL_THEN
    `(integral (IMAGE (\x. a % x) s) (\x. inv (abs a) % (f:real^1->real^2) x)) = inv (abs a) % (integral (IMAGE (\x. a % x) s) f)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_CMUL THEN MATCH_MP_TAC INTEGRABLE_AFFINITY_ALT THEN
    ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC [COMPLEX_CMUL] THEN
  SUBGOAL_THEN
    `(Cx (abs a) * Cx (inv (abs a)) * integral (IMAGE (\x. a % x) s) f) = (Cx (&1) * integral (IMAGE (\x. a % x) s) (f:real^1->real^2))`
    SUBST1_TAC THENL
   [REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN strip_operand_function THEN
    REWRITE_TAC [GSYM CX_MUL; CX_INJ] THEN REWRITE_TAC [GSYM REAL_ABS_INV] THEN
    REWRITE_TAC [GSYM REAL_ABS_MUL] THEN MP_TAC (SPEC `a:real` REAL_MUL_RINV) THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN REAL_ARITH_TAC;
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `Cx (&1) * x = x`] THEN
    REWRITE_TAC [GSYM HAS_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC INTEGRABLE_AFFINITY_ALT THEN ASM_SIMP_TAC []]);;

let INTEGRAL_TRANSLATION = prove
 (`!f:real^M->real^N s a.
       integral s (\x. f (a + x)) = integral (IMAGE (\x. a + x) s) f`,
   REWRITE_TAC[integral; GSYM HAS_INTEGRAL_TRANSLATION]);;

let INTEGRAL_CMUL_1 = prove
 (`!f:real^M->real^2 c s.
        f integrable_on s ==> integral s (\t. c % f t) = c % integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

(*---------------------------------------------------------------------------*)
(*                              Time Scaling                                 *)
(*---------------------------------------------------------------------------*)

let LAPLACE_SCALING = prove
 (`! (f:real^1->complex) (s:real^2) c.
     laplace_exists f s  /\ laplace_exists f (s / Cx c) /\ &0 < c  ==> 
      (laplace_transform (\t. f (c % t)) s = 
       (laplace_transform f (s / Cx c)) * (Cx (&1) / Cx c) )`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `laplace_exists f s` THEN
  REWRITE_TAC [laplace_exists; laplace_transform; exp_order_comp] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t} (\t. cexp (--(s * Cx (drop t))) * f (c % t)) = 
integral {t | &0 <= drop t} (\t. (\t. cexp (--((inv c % s) * Cx (drop t))) * (f:real^1->complex) t) (c % t))`
    SUBST1_TAC THENL
   [SIMP_TAC [] THEN strip_function THEN strip_operand_function THEN
    AP_TERM_TAC THEN REWRITE_TAC [DROP_CMUL] THEN
    REWRITE_TAC [CX_MUL; COMPLEX_CMUL] THEN REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
    AP_TERM_TAC THEN strip_operand_function THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `(((a:complex) * b) * c) = ((b * (c * a)))`] THEN
    REWRITE_TAC [CX_INV] THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `(a = a * b * c) = ((a * Cx (&1) = a * b * c))`] THEN
    AP_TERM_TAC THEN REWRITE_TAC [GSYM CX_INV] THEN
    REWRITE_TAC [GSYM CX_MUL; CX_INJ] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    MP_TAC (SPEC `c:real` REAL_MUL_RINV) THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [REAL_NOT_EQ] THEN DISJ2_TAC THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `integral {t | &0 <= drop t}
 (\t. (\t. cexp (--(inv c % s * Cx (drop t))) * f t) (c % t)) = integral (IMAGE (\t. c % t) {t | &0 <= drop t}) (\t. inv (abs c) % (\t. cexp (--(inv c % s * Cx (drop t))) * (f:real^1->complex) t) t)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_AFFINITY_ALT THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_NOT_EQ] THEN DISJ2_TAC THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    MP_TAC
      (ISPECL
         [`(\t. cexp (--(inv c % s * Cx (drop t))) * f t)`;
          `{t | &0 <= drop t}`; `c:real`]
         INTEGRABLE_AFFINITY_ALT_EQ) THEN
    SIMP_TAC [] THEN SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_NOT_EQ] THEN DISJ2_TAC THEN ASM_SIMP_TAC []; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
    SUBGOAL_THEN
      `(IMAGE (\t. c % t) {t | &0 <= drop t}) = {t | &0 <= drop t}`
      ASSUME_TAC THENL
     [REWRITE_TAC
        [EXTENSION; IN_IMAGE; IN_ELIM_THM; UNWIND_THM1; DROP_SUB; LIFT_DROP;
         IN_UNIV] THEN
      GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
       [ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_CMUL] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE];
        ALL_TAC] THEN
      EXISTS_TAC `(&1 / c) % (x:real^1)` THEN REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC [real_div] THEN REWRITE_TAC [REAL_ARITH `&1 * x = x`] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(c * inv c) = &1` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC [REAL_NOT_EQ] THEN
          DISJ2_TAC THEN ASM_SIMP_TAC [];
          ASM_SIMP_TAC [] THEN VECTOR_ARITH_TAC];
        REWRITE_TAC [DROP_CMUL] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_INV THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE]];
      ASM_SIMP_TAC [] THEN REWRITE_TAC [COMPLEX_CMUL] THEN
      REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [LIFT_VEC_0] THENL
       [SUBGOAL_THEN `a' = lift (drop a')` ASSUME_TAC THENL
         [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        REWRITE_TAC [CEXP_S_T_CONTINUOUS1] THEN
        UNDISCH_TAC
          `!b. (f:real^1->complex) piecewise_differentiable_on interval [lift (&0),lift b]` THEN
        REWRITE_TAC [piecewise_differentiable_on] THEN
        DISCH_THEN (MP_TAC o SPEC `drop a'`) THEN SIMP_TAC [];
        MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN
        REWRITE_TAC [laplace_exists; exp_order_comp] THEN STRIP_TAC THENL
         [ASM_SIMP_TAC []; ALL_TAC] THEN
        REWRITE_TAC [RE_MUL_CX] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        UNDISCH_TAC `laplace_exists f (s / Cx c)` THEN
        REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `(a':real^1)` THEN EXISTS_TAC `M':real` THEN
        ASM_SIMP_TAC [] THEN UNDISCH_TAC `Re (s / Cx c) > drop a'` THEN
        REWRITE_TAC [complex_div] THEN REWRITE_TAC [GSYM CX_INV; RE_MUL_CX] THEN
        REAL_ARITH_TAC]];
    SUBGOAL_THEN
      `(IMAGE (\t. c % t) {t | &0 <= drop t}) = {t | &0 <= drop t}`
      ASSUME_TAC THENL
     [REWRITE_TAC
        [EXTENSION; IN_IMAGE; IN_ELIM_THM; UNWIND_THM1; DROP_SUB; LIFT_DROP;
         IN_UNIV] THEN
      GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
       [ASM_SIMP_TAC [] THEN REWRITE_TAC [DROP_CMUL] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE];
        ALL_TAC] THEN
      EXISTS_TAC `(&1 / c) % (x:real^1)` THEN REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC [real_div] THEN REWRITE_TAC [REAL_ARITH `&1 * x = x`] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(c * inv c) = &1` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC [REAL_NOT_EQ] THEN
          DISJ2_TAC THEN ASM_SIMP_TAC [];
          ASM_SIMP_TAC [] THEN VECTOR_ARITH_TAC];
        REWRITE_TAC [DROP_CMUL] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_INV THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE]];
      ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN
        `integral {t | &0 <= drop t} (\t. (inv (abs c)) % (cexp (--(inv c % s * Cx (drop t))) * f t)) = (inv (abs c)) % integral {t | &0 <= drop t} (\t. cexp (--(inv c % s * Cx (drop t))) * (f:real^1->real^2) t)`
        SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC [complex_div] THEN
        REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH
             `((s * inv (Cx c)) * Cx (drop t)) = ((inv (Cx c) * s) * Cx (drop t))`] THEN
        REWRITE_TAC [GSYM CX_INV; GSYM COMPLEX_CMUL] THEN
        REWRITE_TAC [COMPLEX_CMUL] THEN SUBGOAL_THEN `abs c = c` ASSUME_TAC THENL
         [REWRITE_TAC [REAL_ABS_REFL] THEN ASM_SIMP_TAC [REAL_LT_IMP_LE];
          ASM_SIMP_TAC [] THEN
          REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a * Cx (&1) * b) = (b * a)`]]] THEN
      MATCH_MP_TAC INTEGRAL_CMUL THEN REWRITE_TAC [COMPLEX_CMUL] THEN
      REWRITE_TAC [INTEGRABLE_LIM_AT_POSINFINITY] THEN REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [LIFT_VEC_0] THENL
       [SUBGOAL_THEN `a' = lift (drop a')` ASSUME_TAC THENL
         [REWRITE_TAC [LIFT_DROP]; ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        REWRITE_TAC [CEXP_S_T_CONTINUOUS1] THEN
        UNDISCH_TAC
          `!b. (f:real^1->complex) piecewise_differentiable_on interval [lift (&0),lift b]` THEN
        REWRITE_TAC [piecewise_differentiable_on] THEN
        DISCH_THEN (MP_TAC o SPEC `drop a'`) THEN SIMP_TAC [];
        MATCH_MP_TAC LIM_LAPLACE_EXISTS THEN
        REWRITE_TAC [laplace_exists; exp_order_comp] THEN STRIP_TAC THENL
         [ASM_SIMP_TAC []; ALL_TAC] THEN
        REWRITE_TAC [RE_MUL_CX] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        UNDISCH_TAC `laplace_exists f (s / Cx c)` THEN
        REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `(a':real^1)` THEN EXISTS_TAC `M':real` THEN
        ASM_SIMP_TAC [] THEN UNDISCH_TAC `Re (s / Cx c) > drop a'` THEN
        REWRITE_TAC [complex_div] THEN REWRITE_TAC [GSYM CX_INV; RE_MUL_CX] THEN
        REAL_ARITH_TAC]]]);;

(*---------------------------------------------------------------------------*)
(*                       Some useful theorems regarding                      *)
(*                  differentiability and the Laplace existence              *)
(*---------------------------------------------------------------------------*)

let DIFFERENTIABLE_MUL = prove
 (`!(f:real^1->complex) g x:real^1.
        f differentiable at x /\ g differentiable at x
        ==> (\x. f x * g x) differentiable at x`,
  REWRITE_TAC [differentiable] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC
    `(\d. (f:real^1->complex) x * (f'':real^1->complex) d + f' d * g x)` THEN
  SUBGOAL_THEN
    `((\x. (\x y . x * y) ((f:real^1->complex) x) ((g:real^1->complex) x)) has_derivative
   (\d. ((\x y . x * y) (f x) ((f'':real^1->complex) d) + (\x y . x * y) ((f':real^1->complex) d) (g x)))) (at x)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_BILINEAR_AT THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [BILINEAR_X_MUL_Y];
    SUBGOAL_THEN
      `!d. (\d. (f:real^1->complex) x * (f'':real^1->complex) d + f' d * g x)  = (\d. (\x y. x * y) (f x) (f'' d) + (\x y. x * y) (f' d) (g x))`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN
      `!x. (\x. (f:real^1->complex) x * (g:real^1->complex) x) = (\x. (\x y. x * y) (f x) (g x))`
      ASSUME_TAC THENL
     [SIMP_TAC []; PURE_ONCE_ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC []]]);;

let PIECEWISE_DIFFERENTIABLE_COMPLEX_MUL = prove
 (`!f g:real^1->real^2 s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x * g x) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[piecewise_differentiable_on] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPLEX_MUL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t UNION u :real^1->bool` THEN
  ASM_SIMP_TAC[FINITE_UNION; DIFFERENTIABLE_MUL; IN_INTER;
               SET_RULE `s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`]);;

let COMPLEX_DIFFERENTIABLE_CHAIN_AT = prove
 (`!(f:real^1->complex) g x .
    f differentiable (at x) /\
    g complex_differentiable (at(f x))
    ==> (g o f) differentiable (at x)`,
  REWRITE_TAC
    [complex_differentiable; has_complex_derivative; differentiable] THEN
  MESON_TAC [DIFF_CHAIN_AT]);;

let DIFFERENTIABLE_BILINEAR_AT = prove
 (`!(h:real^M->real^N->real^P) (f:real^Q->real^M) (g:real^Q->real^N) 
(f':real^Q->real^M) (g':real^Q->real^N) (x:real^Q).
    f differentiable (at x) /\ g differentiable (at x) /\ bilinear h
    ==> (\x. h (f x) (g x)) differentiable (at x)`,
  REWRITE_TAC [differentiable] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC
    `(\ (d:real^Q). (h:real^M->real^N->real^P)
                            ((f:real^Q->real^M) (x:real^Q))
                            ((f'':real^Q->real^N) (d:real^Q)) +
                            (h:real^M->real^N->real^P)
                            ((f':real^Q->real^M) (d:real^Q))
                            ((g:real^Q->real^N) (x:real^Q)))` THEN
  MATCH_MP_TAC HAS_DERIVATIVE_BILINEAR_AT THEN ASM_SIMP_TAC []);;

let CX_REAL_DIFFERENTIABLE_AT = prove
 (`!f x. f real_differentiable (atreal x) 
    ==> (Cx o f o drop) differentiable (at (lift x))`,
  REWRITE_TAC
    [differentiable; real_differentiable; HAS_CX_FRECHET_DERIVATIVE_AT] THEN
  MESON_TAC []);;

let LAPLACE_EXISTS_CEXP_MUL_F_1 = prove
 (`!(f:real^1->complex) w0 s.
      laplace_exists f s ==>
      laplace_exists (\t. cexp ((ii * Cx w0) * Cx (drop t)) * f t) s`,
  REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_COMPLEX_MUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC []] THEN
    MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
    MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_CHAIN_AT THEN
    SIMP_TAC [COMPLEX_DIFFERENTIABLE_AT_CEXP] THEN
    SUBGOAL_THEN
      `(\t. (ii * Cx w0) * Cx (drop t)) = 
               (\t. (\x y. x * y) ( (\t. (ii * Cx w0)) t)
                          ((\t. Cx(drop t)) t))`
      ASSUME_TAC THENL
     [SIMP_TAC []; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC DIFFERENTIABLE_BILINEAR_AT THEN
    SIMP_TAC [DIFFERENTIABLE_CONST] THEN REWRITE_TAC [BILINEAR_X_MUL_Y] THEN
    SUBGOAL_THEN `(\t. Cx (drop t)) = (Cx o (\t. t ) o drop)` ASSUME_TAC THENL
     [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN `x = lift (drop x)` ASSUME_TAC THENL
     [SIMP_TAC [LIFT_DROP]; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN MATCH_MP_TAC CX_REAL_DIFFERENTIABLE_AT THEN
    SIMP_TAC [REAL_DIFFERENTIABLE_ID];
    POP_ASSUM MP_TAC THEN REWRITE_TAC [exp_order_comp] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [COMPLEX_NORM_MUL] THEN REWRITE_TAC [NORM_CEXP] THEN
    REWRITE_TAC [LIFT_DROP] THEN EXISTS_TAC `M:real` THEN
    EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC
      `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
    DISCH_THEN (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm ((f:real^1->real^2) (lift t))` THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `((ii * a) * b) = (ii * (a * b))`] THEN
    REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [RE_MUL_II] THEN
    REWRITE_TAC [IM_CX] THEN REWRITE_TAC [REAL_ARITH `-- (&0) = &0`] THEN
    REWRITE_TAC [REAL_EXP_0] THEN REAL_ARITH_TAC]);;

let LAPLACE_EXISTS_CEXP_MUL_F_2 = prove
 (`!(f:real^1->complex) w0 s.
      laplace_exists f s ==>
      laplace_exists (\t. cexp ((--ii * Cx w0) * Cx (drop t)) * f t) s`,
  REWRITE_TAC [SIMPLE_COMPLEX_ARITH `--ii * a = ii * --a`] THEN
  REWRITE_TAC [GSYM CX_NEG] THEN ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_1]);;

let LAPLACE_COMPLEX_MUL_SUB_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex) a b.
 laplace_exists f s /\ laplace_exists g s ==>
(laplace_transform (\x. a * f x - b * g x ) s = a * laplace_transform f s - b * laplace_transform g s)`,
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH `(a - (b:complex) * c) = (a + -- b * c)`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [LAPLACE_COMPLEX_MUL_ADD_LINEARITY]);;

let LAPLACE_NEG_LINEARITY = prove
 (`!(f:real^1->complex) (s:complex).
 laplace_exists f s ==>
(laplace_transform (\x. -- (f x)) s = -- laplace_transform f s)`,
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(-- a) = (-- Cx (&1) * a)`] THEN
  ASM_SIMP_TAC [LAPLACE_COMPLEX_MUL_LINEARITY]);;


let PIECEWISE_DIFFERENTIABLE_MUL = prove
 (`!f g:real^1->real^2 s:real^1->bool.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x * g x) piecewise_differentiable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC [piecewise_differentiable_on] THEN
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC [CONTINUOUS_ON_COMPLEX_MUL] THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `u:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t UNION u :real^1->bool` THEN ASM_SIMP_TAC [FINITE_UNION] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC
    [SET_RULE
       `(s:real^1->bool) DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`;
     IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `!x. x IN s DIFF t ==> (g:real^1->real^2) differentiable at x` THEN
  DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `!x. x IN s DIFF u ==> (f:real^1->real^2) differentiable at x` THEN
  DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DIFFERENTIABLE_MUL]);;

let LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY = prove
 (`!(f:real^1->complex) (s:complex) c:real^2. 
  	     laplace_exists f s /\ &0 < norm c
	     ==> laplace_exists (\t. c * f t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
      SIMP_TAC [DIFFERENTIABLE_ON_CONST];
      UNDISCH_TAC `laplace_exists f s` THEN REWRITE_TAC [laplace_exists] THEN
      MESON_TAC []];
    ALL_TAC] THEN
  UNDISCH_TAC `laplace_exists f s` THEN REWRITE_TAC [laplace_exists] THEN
  REWRITE_TAC [exp_order_comp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [COMPLEX_NORM_MUL] THEN EXISTS_TAC `norm (c:real^2) * M` THEN
  EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC [] THEN STRIP_TAC THENL
   [ASM_SIMP_TAC [REAL_LT_MUL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
  UNDISCH_TAC
    `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
  DISCH_THEN (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE]);;

let LAPLACE_EXISTS_NEG_LINEARITY = prove
 (`!(f:real^1->complex) (s:complex). 
  	laplace_exists f s ==> laplace_exists (\t. -- f t) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC
    [COMPLEX_FIELD `(--(f:real^1->complex) t) = (--Cx (&1) * (f t))`] THEN
  MATCH_MP_TAC LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY THEN ASM_SIMP_TAC [] THEN
  REWRITE_TAC [GSYM CX_NEG] THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
  REAL_ARITH_TAC);;

let LAPLACE_SUB_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex).
 laplace_exists f s /\ laplace_exists g s ==>
(laplace_transform (\x. f x - g x) s = laplace_transform f s - laplace_transform g s)`,
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a - (b:complex)) = (a + -- b)`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [GSYM LAPLACE_NEG_LINEARITY] THEN
  MATCH_MP_TAC LAPLACE_ADD_LINEARITY THEN ASM_SIMP_TAC [] THEN
  ASM_SIMP_TAC [LAPLACE_EXISTS_NEG_LINEARITY]);;

let LAPLACE_EXISTS_ADD_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex). 
  	     laplace_exists f s /\  laplace_exists g s
	     ==> laplace_exists (\t. f t + g t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PIECEWISE_DIFFERENTIABLE_ADD THEN CONJ_TAC THENL
     [UNDISCH_TAC `laplace_exists f s`; UNDISCH_TAC `laplace_exists g s`] THEN
    REWRITE_TAC [laplace_exists] THEN MESON_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC [exp_order_comp] THEN UNDISCH_TAC `laplace_exists f s` THEN
  UNDISCH_TAC `laplace_exists g s` THEN
  REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `(M':real) + (M:real)` THEN
  EXISTS_TAC `lift (max (drop (a:real^1)) (drop (a':real^1)))` THEN CONJ_TAC THENL
   [REWRITE_TAC [real_max] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [LIFT_DROP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC [REAL_ARITH `&0 = &0 + &0`] THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `norm ((f:real^1->complex) (lift (t:real))) + norm ((g:real^1->complex) (lift t))` THEN
  REWRITE_TAC [NORM_TRIANGLE; REAL_ADD_RDISTRIB; LIFT_DROP; real_max] THEN
  COND_CASES_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  UNDISCH_TAC
    `!t. &0 <= t ==> norm ((g:real^1->complex) (lift t)) <= M * exp (drop a * t)` THEN
  UNDISCH_TAC
    `!t. &0 <= t ==> norm ((f:real^1->complex) (lift t)) <= M' * exp (drop a' * t)` THEN
  DISCH_THEN (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  DISCH_THEN (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M:real) * exp (drop a * (t:real))` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < exp (drop a * (t:real))` ASSUME_TAC THEN
    REWRITE_TAC [REAL_EXP_POS_LT] THEN
    SUBGOAL_THEN `&0 < exp (drop a' * (t:real))` ASSUME_TAC THEN
    REWRITE_TAC [REAL_EXP_POS_LT] THEN ASM_SIMP_TAC [GSYM LOG_MONO_LE] THEN
    REWRITE_TAC [LOG_EXP] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M':real) * exp (drop a' * (t:real))` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < exp (drop a * (t:real))` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_EXP_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < exp (drop a' * (t:real))` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_EXP_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC [GSYM LOG_MONO_LE] THEN REWRITE_TAC [LOG_EXP] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [GSYM REAL_NOT_LE]]);;

let LAPLACE_EXISTS_MUL_LINEARITY = prove
 (`!(f:real^1->complex) (s:complex) c. 
  	     laplace_exists f s /\ &0 < c
	     ==> laplace_exists (\t. c % f t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_CMUL] THEN
  MATCH_MP_TAC LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY THEN ASM_SIMP_TAC [] THEN
  REWRITE_TAC [COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC);;

let LAPLACE_EXISTS_SUB_LINEARITY = prove
 (`!(f:real^1->complex) g (s:complex).
 laplace_exists f s /\ laplace_exists g s ==>
(laplace_exists (\t. f t - g t) s)`,
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a - (b:complex)) = (a + -- b)`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LAPLACE_EXISTS_ADD_LINEARITY THEN
  ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [LAPLACE_EXISTS_NEG_LINEARITY]);;

(*---------------------------------------------------------------------------*)
(*                         Cosine-based Modulation                           *)
(*---------------------------------------------------------------------------*)

let LAPLACE_COMPLEX_COSINE_MODULATION = prove
 (`!(f:real^1->complex) (s:complex) w0.
      laplace_exists f s ==> 
    (laplace_transform (\t. ccos (Cx (w0) * Cx (drop t)) * f t) s = 
    (laplace_transform f (s - ii * Cx w0) +
     laplace_transform f (s + ii * Cx w0)) / Cx (&2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [ccos; complex_div] THEN
  SIMP_TAC [SIMPLE_COMPLEX_ARITH `(((a:complex) * b) * c) = (b * (a * c))`] THEN
  SUBGOAL_THEN
    `(laplace_transform
 (\t. inv (Cx (&2)) *
      (cexp ((ii * Cx w0) * Cx (drop t)) * (f:real^1->complex) t +
       cexp ((--ii * Cx w0) * Cx (drop t)) * f t))
 s) = (inv (Cx (&2)) * laplace_transform
 (\t. (cexp ((ii * Cx w0) * Cx (drop t)) * f t +
       cexp ((--ii * Cx w0) * Cx (drop t)) * f t))
 s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN
    MATCH_MP_TAC LAPLACE_EXISTS_ADD_LINEARITY THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_1] THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_2];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(ii * a * b) = ((ii * a) * b)`] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(--ii * a * b) = ((--ii * a) * b)`] THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `(inv (Cx (&2)) * (a + b) * c) = (inv (Cx (&2)) * (a * c + b * c))`] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `laplace_transform
 (\t. cexp ((ii * Cx w0) * Cx (drop t)) * (f:real^1->complex) t +
     cexp ((--ii * Cx w0) * Cx (drop t)) * f t) s = laplace_transform (\t. cexp ((ii * Cx w0) * Cx (drop t)) * f t) s + laplace_transform (\t. cexp ((--ii * Cx w0) * Cx (drop t)) * f t) s`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_ADD_LINEARITY THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_1] THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_2];
    ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    ASM_SIMP_TAC [LAPLACE_SHIFT_IN_S_DOMAIN] THEN
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a - -- ii * b) = (a + ii * b)`] THEN
    CONV_TAC COMPLEX_FIELD]);;

(*---------------------------------------------------------------------------*)
(*                          Sine-based Modulation                            *)
(*---------------------------------------------------------------------------*)

let LAPLACE_COMPLEX_SINE_MODULATION = prove
 (`!(f:real^1->complex) (s:complex) w0.
      laplace_exists f s ==> 
    (laplace_transform (\t. csin (Cx (w0) * Cx (drop t)) * f t) s = 
    (laplace_transform f (s - ii * Cx w0) -
     laplace_transform f (s + ii * Cx w0)) / (Cx (&2) * ii))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [csin; complex_div] THEN
  SIMP_TAC
    [SIMPLE_COMPLEX_ARITH `((a:complex * (b * d) * c) = ((a * b) * c) * d)`] THEN
  REWRITE_TAC [COMPLEX_SUB_LDISTRIB; COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH
       `((a * b) * c - (d * b) * c) = (b * (a * c - d * (c:complex)))`] THEN
  SUBGOAL_THEN
    `(laplace_transform
 (\t. inv (Cx (&2) * ii) *
      (cexp ((ii * Cx w0) * Cx (drop t)) * (f:real^1->complex) t -
       cexp ((--ii * Cx w0) * Cx (drop t)) * f t))
 s) = (inv (Cx (&2) * ii) * laplace_transform
 (\t. (cexp ((ii * Cx w0) * Cx (drop t)) * f t -
       cexp ((--ii * Cx w0) * Cx (drop t)) * f t))
 s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN
    MATCH_MP_TAC LAPLACE_EXISTS_SUB_LINEARITY THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_1] THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_2];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN ONCE_ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `laplace_transform
 (\t. cexp ((ii * Cx w0) * Cx (drop t)) * (f:real^1->complex) t -
     cexp ((--ii * Cx w0) * Cx (drop t)) * f t) s = laplace_transform (\t. cexp ((ii * Cx w0) * Cx (drop t)) * f t) s - laplace_transform (\t. cexp ((--ii * Cx w0) * Cx (drop t)) * f t) s`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_SUB_LINEARITY THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_1] THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_CEXP_MUL_F_2];
    ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    ASM_SIMP_TAC [LAPLACE_SHIFT_IN_S_DOMAIN] THEN
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(a - -- ii * b) = (a + ii * b)`] THEN
    CONV_TAC COMPLEX_FIELD]);;

(*---------------------------------------------------------------------------*)
(*       Differentiation in Time Domain with Zero Initial Conditions         *)
(*---------------------------------------------------------------------------*)

let zero_initial_conditions = new_recursive_definition num_RECURSION
  `( zero_initial_conditions 0 (f:real^1->complex)  = ( f (lift (&0) ) = Cx(&0) ) )  /\
    (!n. zero_initial_conditions  (SUC n) (f:real^1->complex) =
       (( higher_vector_derivative (SUC n) f  (lift (&0)) = Cx(&0)  ) /\ (zero_initial_conditions  n f ) ))`;;

let LAPLACE_DIFF_THEOREM_AT_ZERO_INIT = prove
 (`!(f:real^1->complex)(f':real^1->complex) (s:complex) (b:real).
      laplace_exists f s /\ laplace_exists f' s  /\
      (!x. (f has_vector_derivative f' x) (at x)) /\
     (zero_initial_conditions 0 f)  ==>
      (laplace_transform f' s = s * (laplace_transform f s) )`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `laplace_transform f' s =
             s * laplace_transform f s - (f:real^1->complex) (lift (&0))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_DIFF_THEOREM_AT THEN ASM_SIMP_TAC [];
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC [zero_initial_conditions] THEN SIMPLE_COMPLEX_ARITH_TAC]);;

let LAPLACE_DIFF_F_THEOREM_AT_ZERO_INIT = prove
 (`! (f:real^1->complex) (s:complex) (b:real).
     laplace_exists f s /\
    (laplace_exists (\x. vector_derivative f ( at x )) s ) /\ 
    (!x. f differentiable at x) /\
     zero_initial_conditions 0 f
 ==>
    (laplace_transform (\x. vector_derivative f (at x)) s = 
                                 (s * (laplace_transform f s)) )`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LAPLACE_DIFF_THEOREM_AT_ZERO_INIT THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM VECTOR_DERIVATIVE_WORKS] THEN
  ASM_SIMP_TAC []);;

let LAPLACE_HIGHER_DIFF_F_THEOREM_AT_CORRECT_ZERO_INIT = prove
 (`!(f:real^1->complex) (s:complex) n.
     ((laplace_exists_higher_deriv n f s) /\
     (!x:real^1. differentiable_higher_derivative n f x)) /\
     (zero_initial_conditions (n - 1) f)
     ==>
     (laplace_transform (\x.  higher_vector_derivative n f x) s =
     ((s pow n) * (laplace_transform f s)))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC [higher_vector_derivative; complex_pow; COMPLEX_MUL_LID] THEN
    SIMP_TAC [ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC
    [higher_vector_derivative; laplace_exists_higher_deriv;
     differentiable_higher_derivative] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
    `(laplace_exists_higher_deriv n f s /\
       (!x. differentiable_higher_derivative n f x)) /\
      zero_initial_conditions (n - 1) f
      ==> laplace_transform (\x. higher_vector_derivative n f x) s =
          s pow n * laplace_transform f s` THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN `zero_initial_conditions (n - 1) (f:real^1->complex)`
    ASSUME_TAC THENL
   [MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `zero_initial_conditions (SUC n - 1) f` THENL
     [ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM ONE] THEN
      REWRITE_TAC [ARITH_RULE `1 - 1 = 0`] THEN
      REWRITE_TAC [ARITH_RULE `0 - 1 = 0`];
      REWRITE_TAC [ARITH_RULE `SUC n = n + 1`] THEN
      REWRITE_TAC [ARITH_RULE `(n + 1) - 1 = n`] THEN
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [REWRITE_TAC [ADD1] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
        ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [zero_initial_conditions] THEN
        POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC []]];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `laplace_transform (\x. vector_derivative (\x. higher_vector_derivative n (f:real^1->complex) x) (at x)) s = 
     s * laplace_transform (\x. higher_vector_derivative n f x) s`
    ASSUME_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [complex_pow]] THEN
  MATCH_MP_TAC LAPLACE_DIFF_F_THEOREM_AT_ZERO_INIT THEN
  REWRITE_TAC [zero_initial_conditions] THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL
   [MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `laplace_exists_higher_deriv n f s` THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC [higher_vector_derivative] THEN ASM_SIMP_TAC [] THEN
      SIMP_TAC [laplace_exists_higher_deriv; ETA_AX];
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUC_GT_ZERO;
        UNDISCH_TAC `laplace_exists_higher_deriv n f s` THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [laplace_exists_higher_deriv]] THEN
      ASM_SIMP_TAC []];
    CONJ_TAC THENL
     [GEN_TAC THEN
      UNDISCH_TAC
        `!x. (\x. vector_derivative (\x. higher_vector_derivative n f x) (at x)) differentiable
     at x /\ differentiable_higher_derivative n f x` THEN
      DISCH_THEN (MP_TAC o SPEC `x:real^1`) THEN REPEAT STRIP_TAC THEN
      MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
      REPEAT STRIP_TAC THENL
       [UNDISCH_TAC `differentiable_higher_derivative n f x` THEN
        ASM_SIMP_TAC [] THEN
        REWRITE_TAC
          [higher_vector_derivative; differentiable_higher_derivative] THEN
        SIMP_TAC [ETA_AX];
        SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUC_GT_ZERO;
          UNDISCH_TAC `differentiable_higher_derivative n f x` THEN
          ONCE_ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [differentiable_higher_derivative]] THEN
        ASM_SIMP_TAC []];
      MP_TAC NUM_ZERO_TOTAL THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `zero_initial_conditions (SUC n - 1) f` THENL
       [ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM ONE] THEN
        REWRITE_TAC [ARITH_RULE `1 - 1 = 0`] THEN
        REWRITE_TAC [zero_initial_conditions; higher_vector_derivative];
        REWRITE_TAC [ARITH_RULE `SUC n = n + 1`] THEN
        REWRITE_TAC [ARITH_RULE `(n + 1) - 1 = n`] THEN
        SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
         [REWRITE_TAC [ADD1] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
          ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [zero_initial_conditions] THEN
          SIMP_TAC []]]]]);;

(*---------------------------------------------------------------------------*)
(*                          Some useful theorems                             *)
(*---------------------------------------------------------------------------*)

let LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY_GEN = prove
 (`!(f:real^1->complex) (s:complex) c:complex. 
  	     laplace_exists f s 
	     ==> laplace_exists (\t. c * f t) s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(c = Cx (&0))` THENL
   [ALL_TAC;
    ASM_SIMP_TAC [COMPLEX_NORM_NZ; LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY]] THEN
  ASM_SIMP_TAC [] THEN
  REWRITE_TAC [SIMPLE_COMPLEX_ARITH `Cx (&0) * x = Cx (&0)`] THEN
  REWRITE_TAC [laplace_exists] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE THEN
    SIMP_TAC [DIFFERENTIABLE_ON_CONST];
    ALL_TAC] THEN
  UNDISCH_TAC `laplace_exists f s` THEN
  REWRITE_TAC [laplace_exists; exp_order_comp] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `M:real` THEN EXISTS_TAC `a:real^1` THEN ASM_SIMP_TAC [] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM COMPLEX_VEC_0; NORM_0] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC [REAL_LT_IMP_LE]; REWRITE_TAC [REAL_EXP_POS_LE]]);;

let LAPLACE_EXISTS_MUL_LINEARITY_GEN = prove
 (`!(f:real^1->complex) (s:complex) c. 
  	     laplace_exists f s 
	     ==> laplace_exists (\t. c % f t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_CMUL] THEN
  ASM_SIMP_TAC [LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY_GEN]);;

let VSUM_00 = prove
 (`vsum(0..0) f = f(0)`,
  REWRITE_TAC[VSUM_SING_NUMSEG]);;

let VSUM_11 = prove
 (`!t. vsum(0..1) t = t(0) + t(1)`,
  REWRITE_TAC[num_CONV `1`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let VSUM_22 = prove
 (`!t. vsum(0..2) t = t(0) + t(1) + t(2)`,
  REWRITE_TAC[num_CONV `1`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_2 = prove
 (`!t. vsum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `1`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]
  THEN VECTOR_ARITH_TAC);;

(*---------------------------------------------------------------------------*)
(*                      n-order Differential Equation                        *)
(*---------------------------------------------------------------------------*)

 let diff_eq_n_order = new_definition
    `diff_eq_n_order n (lst:complex list) (f:real^1->complex) t = 
  (vsum (0..n) (\k. (EL k lst) * (higher_vector_derivative k f t)))`;; 

let DIFF_EQ_LAPLACE_EXISTS_ALT_SECOND = prove
 (`!n lst f s. laplace_exists_higher_deriv n f s
             ==> laplace_exists (\t. diff_eq_n_order n lst f t) s`,
  INDUCT_TAC THENL
   [SIMP_TAC [diff_eq_n_order; EL; VSUM_00; EL] THEN
    REWRITE_TAC [laplace_exists_higher_deriv] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [higher_vector_derivative] THEN
    ASM_SIMP_TAC [LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY_GEN];
    ASM_SIMP_TAC
      [diff_eq_n_order; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC N`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LAPLACE_EXISTS_ADD_LINEARITY THEN
    REPEAT STRIP_TAC THENL
     [REWRITE_TAC [GSYM diff_eq_n_order] THEN
      FIRST_X_ASSUM
        (MP_TAC o
         SPECL [`lst:complex list`; `f:real^1->complex`; `s:complex`]);
      MATCH_MP_TAC LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY_GEN] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [laplace_exists_higher_deriv] THEN
    SIMP_TAC []]);;

let LAPLACE_OF_DIFF_EQ_SECOND = prove
 (`!(f:real^1->complex) lst s n.
    ((laplace_exists_higher_deriv n f s) /\
     (!x:real^1. differentiable_higher_derivative n f x))
        ==> 
      (laplace_transform (\t. diff_eq_n_order n lst f t) s =
       (laplace_transform f s) * vsum (0..n) (\k. (EL k lst)  * (s pow k) ) - vsum (0..n) (\k. (EL k lst) * ( vsum (1..k) (\i. s pow (i - 1)  * higher_vector_derivative (k - i) f (lift(&0))) ) ) )`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC [VSUM_00; diff_eq_n_order; EL] THEN
    SIMP_TAC [higher_vector_derivative; complex_pow] THEN
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x * Cx (&1) = x`] THEN
    SUBGOAL_THEN `0 < 1` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [VSUM_TRIV_NUMSEG] THEN REWRITE_TAC [COMPLEX_VEC_0] THEN
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x - y * Cx (&0) = x`] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `laplace_transform f s * HD lst = HD lst * laplace_transform f s`] THEN
    MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN
    UNDISCH_TAC `laplace_exists_higher_deriv 0 f s` THEN
    SIMP_TAC [laplace_exists_higher_deriv];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [diff_eq_n_order; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC N`] THEN
  SUBGOAL_THEN `!n. 1 <= SUC n` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC [ONE] THEN REWRITE_TAC [LE_SUC] THEN
    REWRITE_TAC [LE_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `laplace_transform
 (\t. vsum (0..n) (\k. (EL k lst) * higher_vector_derivative k f t) +
      (EL (SUC n) lst) * higher_vector_derivative (SUC n) f t) s = (laplace_transform
 (\t. vsum (0..n) (\k. (EL k lst) * higher_vector_derivative k f t)) s + laplace_transform
 (\t. ((EL (SUC n) lst) * higher_vector_derivative (SUC n) f t)) s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_ADD_LINEARITY THEN
    REWRITE_TAC [GSYM diff_eq_n_order] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_EQ_LAPLACE_EXISTS_ALT_SECOND;
      MATCH_MP_TAC LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY_GEN] THEN
    UNDISCH_TAC `laplace_exists_higher_deriv (SUC n) f s` THEN
    SIMP_TAC [laplace_exists_higher_deriv];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [GSYM diff_eq_n_order] THEN
  UNDISCH_TAC
    `laplace_exists_higher_deriv n f s /\
      (!x. differentiable_higher_derivative n f x)
      ==> laplace_transform (\t. diff_eq_n_order n lst f t) s =
          laplace_transform f s * vsum (0..n) (\k. (EL k lst) * s pow k) -
          vsum (0..n)
          (\k. (EL k lst) *
               vsum (1..k)
               (\i. s pow (i - 1) *
                    higher_vector_derivative (k - i) f (lift (&0))))` THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC [laplace_exists_higher_deriv; differentiable_higher_derivative] THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN
  REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
  REWRITE_TAC [SIMPLE_COMPLEX_ARITH `((x:complex) - y + z) = (x + z - y)`] THEN
  REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(((x:complex) + y) - z) = (x + y - z)`] THEN
  REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH `(((a:complex) + b) = (a + c)) = (b = c)`] THEN
  SUBGOAL_THEN
    `(laplace_transform
 (\t. (EL (SUC n) lst) * higher_vector_derivative (SUC n) f t)
 s)  = ((EL (SUC n) lst) * laplace_transform
 (\t. higher_vector_derivative (SUC n) (f:real^1->complex) t)
 s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN ASM_SIMP_TAC []; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN
    `laplace_transform (\t. higher_vector_derivative (SUC n) f t) s = s pow (SUC n) * laplace_transform (f:real^1->complex) s -
             vsum (1..(SUC n))
             (\t. s pow (t - 1) *
                  higher_vector_derivative ((SUC n) - t) f (lift (&0)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_HIGHER_DIFF_F_THEOREM_AT_CORRECT THEN CONJ_TAC THENL
     [UNDISCH_TAC
        `laplace_exists (\x. higher_vector_derivative (SUC n) f x) s` THEN
      REWRITE_TAC [ETA_AX] THEN ASM_SIMP_TAC [laplace_exists_higher_deriv] THEN
      REWRITE_TAC [ETA_AX];
      REWRITE_TAC [differentiable_higher_derivative] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC
        `!x. (\x. higher_vector_derivative (SUC n) f x) differentiable at x /\
          differentiable_higher_derivative n f x` THEN
      DISCH_THEN (MP_TAC o SPEC `t:real^1`) THEN SIMP_TAC []];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_LDISTRIB] THEN
  SUBGOAL_THEN
    `(s pow (SUC n - 1) * higher_vector_derivative (SUC n - SUC n) f (lift (&0))) = vsum ((SUC n)..(SUC n))
  (\i. s pow (i - 1) * higher_vector_derivative (SUC n - i) f (lift (&0)))`
    ASSUME_TAC THENL
   [REWRITE_TAC [VSUM_SING_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `vsum (1..n)
  (\i. s pow (i - 1) * higher_vector_derivative (SUC n - i) f (lift (&0))) +
  vsum (SUC n..SUC n)
  (\i. s pow (i - 1) * higher_vector_derivative (SUC n - i) f (lift (&0))) = vsum (1..SUC n)
 (\t. s pow (t - 1) * higher_vector_derivative (SUC n - t) (f:real^1->complex) (lift (&0)))`
    ASSUME_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `((a:complex) * (b - c)) = (a * b - a * c)`] THEN
    SIMPLE_COMPLEX_ARITH_TAC] THEN
  SUBGOAL_THEN `n = SUC n -1` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  SUBGOAL_THEN `SUC (SUC n - 1) = SUC n` ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `SUC n = n + 1` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `(n + 1) - 1 = n` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  MATCH_MP_TAC VSUM_ADD_SPLIT THEN SUBGOAL_THEN `n + 1 = SUC n` ASSUME_TAC THENL
   [ARITH_TAC; ASM_REWRITE_TAC []]);;

(*---------------------------------------------------------------------------*)
(*        n-order Differential Equation with Zero Intial Conditions          *)
(*---------------------------------------------------------------------------*)

let LAPLACE_OF_DIFF_EQ_ZERO_INIT_SECOND = prove
 (`!(f:real^1->complex) lst s n.
    ((laplace_exists_higher_deriv n f s) /\
     (!x:real^1. differentiable_higher_derivative n f x)) /\
      (0 < n ==> zero_initial_conditions (n - 1) f)
        ==> 
      (laplace_transform (\t. diff_eq_n_order n lst f t) s =
       (laplace_transform f s) * vsum (0..n) (\k. (EL k lst)  * (s pow k) ) )`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC [VSUM_00; diff_eq_n_order; EL] THEN
    SIMP_TAC [higher_vector_derivative; complex_pow] THEN
    REWRITE_TAC [SIMPLE_COMPLEX_ARITH `x * Cx (&1) = x`] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `laplace_transform f s * HD lst = HD lst * laplace_transform f s`] THEN
    MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN
    UNDISCH_TAC `laplace_exists_higher_deriv 0 f s` THEN
    SIMP_TAC [laplace_exists_higher_deriv];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [diff_eq_n_order; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC N`] THEN
  SUBGOAL_THEN `!n. 1 <= SUC n` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC [ONE] THEN REWRITE_TAC [LE_SUC] THEN
    REWRITE_TAC [LE_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN
  SUBGOAL_THEN
    `laplace_transform
 (\t. vsum (0..n) (\k. (EL k lst) * higher_vector_derivative k f t) +
      (EL (SUC n) lst) * higher_vector_derivative (SUC n) f t) s = (laplace_transform
 (\t. vsum (0..n) (\k. (EL k lst) * higher_vector_derivative k f t)) s + laplace_transform
 (\t. ((EL (SUC n) lst) * higher_vector_derivative (SUC n) f t)) s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LAPLACE_ADD_LINEARITY THEN
    REWRITE_TAC [GSYM diff_eq_n_order] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_EQ_LAPLACE_EXISTS_ALT_SECOND;
      MATCH_MP_TAC LAPLACE_EXISTS_COMPLEX_MUL_LINEARITY_GEN] THEN
    UNDISCH_TAC `laplace_exists_higher_deriv (SUC n) f s` THEN
    SIMP_TAC [laplace_exists_higher_deriv];
    ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN REWRITE_TAC [GSYM diff_eq_n_order] THEN
  UNDISCH_TAC
    `(laplace_exists_higher_deriv n f s /\
       (!x. differentiable_higher_derivative n f x)) /\
      (0 < n ==> zero_initial_conditions (n - 1) f)
      ==> laplace_transform (\t. diff_eq_n_order n lst f t) s =
          laplace_transform f s * vsum (0..n) (\k. EL k lst * s pow k)` THEN
  POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN MP_TAC NUM_ZERO_TOTAL THEN
  DISCH_THEN (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THENL
   [UNDISCH_TAC `laplace_exists_higher_deriv (SUC n) f s` THEN
    UNDISCH_TAC `!x. differentiable_higher_derivative (SUC n) f x` THEN
    UNDISCH_TAC `0 < SUC n ==> zero_initial_conditions (SUC n - 1) f` THEN
    ASM_SIMP_TAC
      [differentiable_higher_derivative; laplace_exists_higher_deriv] THEN
    REWRITE_TAC [GSYM ONE; ARITH_RULE `0 - 1 = 0`; ARITH_RULE `1 -1 = 0`] THEN
    SIMP_TAC [ARITH_RULE `0 < 1`] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [VSUM_00; EL] THEN REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
      `(laplace_transform
 (\t. (EL 1 lst) * higher_vector_derivative 1 f t)
 s)  = ((EL 1 lst) * laplace_transform
 (\t. higher_vector_derivative 1 (f:real^1->complex) t)
 s)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN ASM_SIMP_TAC [];
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `laplace_transform (\t. higher_vector_derivative 1 f t) s = s pow 1 * laplace_transform (f:real^1->complex) s`
      ASSUME_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC [] THEN CONV_TAC COMPLEX_FIELD] THEN
    MATCH_MP_TAC LAPLACE_HIGHER_DIFF_F_THEOREM_AT_CORRECT_ZERO_INIT THEN
    ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [ARITH_RULE `1 -1 = 0`] THEN
    SIMP_TAC [ONE; laplace_exists_higher_deriv] THEN
    ASM_SIMP_TAC
      [ONE; laplace_exists_higher_deriv; differentiable_higher_derivative] THEN
    ASM_SIMP_TAC [GSYM ONE];
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC
      [laplace_exists_higher_deriv; differentiable_higher_derivative] THEN
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN `zero_initial_conditions (n - 1) (f:real^1->complex)`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `0 < SUC n` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `0 < SUC n ==> zero_initial_conditions (SUC n - 1) f` THEN
      ASM_SIMP_TAC [zero_initial_conditions] THEN REWRITE_TAC [ADD1; ADD_SUB] THEN
      SUBGOAL_THEN `n = SUC (n - 1)` ASSUME_TAC THENL
       [REWRITE_TAC [ADD1] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
        ARITH_TAC;
        ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [zero_initial_conditions] THEN
        POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC []];
      ASM_SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
      SUBGOAL_THEN
        `(laplace_transform
 (\t. (EL (SUC n) lst) * higher_vector_derivative (SUC n) f t)
 s)  = ((EL (SUC n) lst) * laplace_transform
 (\t. higher_vector_derivative (SUC n) (f:real^1->complex) t)
 s)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC LAPLACE_COMPLEX_MUL_LINEARITY THEN ASM_SIMP_TAC [];
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
        `laplace_transform (\t. higher_vector_derivative (SUC n) f t) s = s pow (SUC n) * laplace_transform (f:real^1->complex) s`
        ASSUME_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        SIMPLE_COMPLEX_ARITH_TAC] THEN
      MATCH_MP_TAC LAPLACE_HIGHER_DIFF_F_THEOREM_AT_CORRECT_ZERO_INIT THEN
      ASM_SIMP_TAC [] THEN CONJ_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `0 < SUC n ==> zero_initial_conditions (SUC n - 1) f` THEN
        SIMP_TAC [ARITH_RULE `0 < SUC n`]] THEN
      CONJ_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC [differentiable_higher_derivative]] THEN
      UNDISCH_TAC
        `laplace_exists (\x. higher_vector_derivative (SUC n) f x) s` THEN
      REWRITE_TAC [ETA_AX] THEN ASM_SIMP_TAC [laplace_exists_higher_deriv] THEN
      REWRITE_TAC [ETA_AX]]]);;

(*---------------------------------------------------------------------------*)
(*              Transfer Function of a Generic n-order System                *)
(*---------------------------------------------------------------------------*)

let diff_eq_n_order_sys = new_definition
   `diff_eq_n_order_sys (m:num) (n:num) (inlst:complex list) (outlst:complex list) (y:real^1->complex) (x:real^1->complex)  = 
   (!t:real^1. (diff_eq_n_order n outlst y t  = diff_eq_n_order m inlst x t )) `;; 

let TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND = prove
 (`!(y:real^1->complex) x m n inlst outlst s. 
    (!t. differentiable_higher_derivative n y t) /\ 
    (!t. differentiable_higher_derivative m x t) /\ 
    (laplace_exists_higher_deriv n y s)  /\ 
    (laplace_exists_higher_deriv m x s) /\
    (0 < n ==> zero_initial_conditions (n - 1) y) /\
    (0 < m ==> zero_initial_conditions (m - 1) x) /\
       diff_eq_n_order_sys m n inlst outlst y x
         ==> 
 (laplace_transform y s *
      vsum (0..n) (\k. (EL k outlst) * s pow k) = 
   laplace_transform x s *
          vsum (0..m) (\k. (EL k inlst) * s pow k) )`,
  REWRITE_TAC [diff_eq_n_order_sys] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `laplace_transform y s *
             vsum (0..n) (\k. (EL k outlst) * s pow k) =
             laplace_transform (\t. diff_eq_n_order n outlst y t) s`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC [LAPLACE_OF_DIFF_EQ_ZERO_INIT_SECOND];
    SUBGOAL_THEN
      `laplace_transform x s * vsum (0..m) (\k. (EL k inlst) * s pow k) = laplace_transform (\t. diff_eq_n_order m inlst x t) s`
      SUBST1_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC []] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC [LAPLACE_OF_DIFF_EQ_ZERO_INIT_SECOND]]);;


let TRANSFER_FUNCTION_OF_N_ORDER_SYS_SECOND = prove
 (`!(y:real^1->complex) x m n inlst outlst s. 
    (!t. differentiable_higher_derivative n y t) /\ 
    (!t. differentiable_higher_derivative m x t) /\ 
    (laplace_exists_higher_deriv n y s)  /\ 
    (laplace_exists_higher_deriv m x s) /\
    (0 < n ==> zero_initial_conditions (n - 1) y) /\
    (0 < m ==> zero_initial_conditions (m - 1) x) /\
       diff_eq_n_order_sys m n inlst outlst y x /\
   ~(laplace_transform x s = Cx (&0)) /\
   ~(( vsum (0..n) (\t. (EL t outlst)  * (s pow t))) = Cx (&0)) 
         ==> laplace_transform y s / laplace_transform x s = (vsum (0..m) (\t. (EL t inlst)  * (s pow t))) / (vsum (0..n) (\t. (EL t outlst)  * (s pow t)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [COMPLEX_FIELD
       `!a b c d. ~(d = Cx (&0)) /\ ~(b = Cx (&0)) ==> ((a / b = c / d ) = (a * d = b * c))`] THEN
  ASM_SIMP_TAC [TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND]);;

let differentiable_higher_deriv = new_definition
  `differentiable_higher_deriv m n x y t  <=> 
   (differentiable_higher_derivative n y t) /\ 
   (differentiable_higher_derivative m x t)`;;

let laplace_exists_of_higher_deriv = new_definition
  `laplace_exists_of_higher_deriv m n x y s  <=> 
   (laplace_exists_higher_deriv n y s)  /\ 
   (laplace_exists_higher_deriv m x s)`;;

let zero_init_conditions = new_definition
   `zero_init_conditions m n x y   <=> 
    (0 < n ==> zero_initial_conditions (n - 1) y) /\
    (0 < m ==> zero_initial_conditions (m - 1) x)`;;

let TRANSFER_FUNCTION_OF_N_ORDER_SYS_SECOND_FINAL = prove
 (`!(y:real^1->complex) x m n inlst outlst s. 
    (!t. differentiable_higher_deriv m n x y t) /\ 
    (laplace_exists_of_higher_deriv m n x y s) /\
    (zero_init_conditions m n x y) /\
     diff_eq_n_order_sys m n inlst outlst y x /\
   ~(laplace_transform x s = Cx (&0)) /\
   ~(( vsum (0..n) (\t. (EL t outlst)  * (s pow t))) = Cx (&0)) 
         ==> laplace_transform y s / laplace_transform x s = 
            (vsum (0..m) (\t. (EL t inlst)  * (s pow t))) / 
            (vsum (0..n) (\t. (EL t outlst)  * (s pow t)))`,
  REWRITE_TAC
    [differentiable_higher_deriv; laplace_exists_of_higher_deriv;
     zero_init_conditions] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [COMPLEX_FIELD
       `!a b c d. ~(d = Cx (&0)) /\ ~(b = Cx (&0)) ==> ((a / b = c / d ) = (a * d = b * c))`] THEN
  ASM_SIMP_TAC [TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND]);;

(*===========================================================================*)
(*                        DIFF_EQ_2_TRANS_FUN_TAC                            *)
(*         A tactic for the automatic transfer function verification         *)
(*             of the systems upto 20th order and is extendeable             *)
(*===========================================================================*)

let NUM_ARITH_TAC = 
    REWRITE_TAC [num_CONV `1`; num_CONV `2`; num_CONV `3`; 
                 num_CONV `4`; num_CONV `5`; num_CONV `6`; num_CONV `7`;
                 num_CONV `8`; num_CONV `9`; num_CONV `10`];;

(*---------------------------------------------------------------------------*)
(*             Some useful theorems regarding vector summation               *)
(*---------------------------------------------------------------------------*)

let VSUM_00 = prove
 (`vsum(0..0) f = f(0)`,
  REWRITE_TAC[VSUM_SING_NUMSEG]);;

let VSUM_11 = prove
 (`!t. vsum(0..1) t = t(0) + t(1)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let VSUM_22 = prove
 (`!t. vsum(0..2) t = t(0) + t(1) + t(2)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_33 = prove
 (`!t. vsum(0..3) t = t(0) + t(1) + t(2) + t(3)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_44 = prove
 (`!t. vsum(0..4) t = t(0) + t(1) + t(2) + t(3) + t(4)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_55 = prove
 (`!t. vsum(0..5) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_66 = prove
 (`!t. vsum(0..6) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_77 = prove
 (`!t. vsum(0..7) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_88 = prove
 (`!t. vsum(0..8) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_99 = prove
 (`!t. vsum(0..9) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_1010 = prove
 (`!t. vsum(0..10) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10)`,
  NUM_ARITH_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC [VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_1111 = prove
 (`!t. vsum(0..11) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10)) + t(11))`] THEN
REWRITE_TAC [GSYM VSUM_1010] THEN REWRITE_TAC [ARITH_RULE `10 = 11 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1212 = prove
 (`!t. vsum(0..12) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11)) + t(12))`] THEN
REWRITE_TAC [GSYM VSUM_1111] THEN REWRITE_TAC [ARITH_RULE `11 = 12 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1313 = prove
 (`!t. vsum(0..13) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12)) + t(13))`] THEN
REWRITE_TAC [GSYM VSUM_1212] THEN REWRITE_TAC [ARITH_RULE `12 = 13 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1414 = prove
 (`!t. vsum(0..14) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13)) + t(14))`] THEN
REWRITE_TAC [GSYM VSUM_1313] THEN REWRITE_TAC [ARITH_RULE `13 = 14 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1515 = prove
 (`!t. vsum(0..15) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14)) + t(15))`] THEN
REWRITE_TAC [GSYM VSUM_1414] THEN REWRITE_TAC [ARITH_RULE `14 = 15 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1616 = prove
 (`!t. vsum(0..16) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15)) + t(16))`] THEN
REWRITE_TAC [GSYM VSUM_1515] THEN REWRITE_TAC [ARITH_RULE `15 = 16 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1717 = prove
 (`!t. vsum(0..17) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16)) + t(17))`] 
THEN REWRITE_TAC [GSYM VSUM_1616] THEN 
REWRITE_TAC [ARITH_RULE `16 = 17 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1818 = prove
 (`!t. vsum(0..18) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17)) + t(18))`] THEN 
REWRITE_TAC [GSYM VSUM_1717] THEN REWRITE_TAC [ARITH_RULE `17 = 18 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_1919 = prove
 (`!t. vsum(0..19) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18) + t(19)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18) + t(19)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18)) + t(19))`] THEN 
REWRITE_TAC [GSYM VSUM_1818] THEN REWRITE_TAC [ARITH_RULE `18 = 19 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

let VSUM_2020 = prove
 (`!t. vsum(0..20) t = t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18) + t(19) + t(20)`,
REWRITE_TAC [VECTOR_ARITH `(t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18) + t(19) + t(20)) = ((t(0) + t(1) + t(2) + t(3) + t(4) + t(5) + t(6) + t(7) + t(8) + t(9) + t(10) + t(11) + t(12) + t(13) + t(14) + t(15) + t(16) + t(17) + t(18) + t(19)) + t(20))`] THEN 
REWRITE_TAC [GSYM VSUM_1919] THEN REWRITE_TAC [ARITH_RULE `19 = 20 - 1`]
THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_CLAUSES_RIGHT THEN ARITH_TAC);;

(*---------------------------------------------------------------------------*)
(*                            Numbers Equivalence                            *)
(*---------------------------------------------------------------------------*)

let ONE = 
	prove (`1  = SUC 0`, ARITH_TAC);;
let TWO = 
	prove (`2  = SUC 1`, ARITH_TAC);;
let THREE = 
	prove (`3  = SUC 2`, ARITH_TAC);;
let FOUR = 
	prove (`4  = SUC 3`, ARITH_TAC);;
let FIVE = 
	prove (`5  = SUC 4`, ARITH_TAC);;
let SIX = 
	prove (`6  = SUC 5`, ARITH_TAC);;
let SEVEN = 
	prove (`7  = SUC 6`, ARITH_TAC);;
let EIGHT = 
	prove (`8  = SUC 7`, ARITH_TAC);;
let NINE  = 
	prove (`9  = SUC 8`, ARITH_TAC);; 
let TEN = 
	prove (`10  = SUC 9`, ARITH_TAC);;
let ELEVEN = 
	prove (`11  = SUC 10`, ARITH_TAC);;
let TWELVE = 
	prove (`12  = SUC 11`, ARITH_TAC);;
let THIRTEEN = 
	prove (`13  = SUC 12`, ARITH_TAC);;
let FOURTEEN = 
	prove (`14  = SUC 13`, ARITH_TAC);;
let FIFTEEN = 
	prove (`15  = SUC 14`, ARITH_TAC);;
let SIXTEEN = 
	prove (`16  = SUC 15`, ARITH_TAC);;
let SEVENTEEN = 
	prove (`17  = SUC 16`, ARITH_TAC);;
let EIGHTEEN = 
	prove (`18  = SUC 17`, ARITH_TAC);;
let NINETEEN = 
	prove (`19  = SUC 18`, ARITH_TAC);;
let TWENTY = 
	prove (`20  = SUC 19`, ARITH_TAC);;

let NUM_SIMP_TAC = 
SIMP_TAC [ONE; TWO; THREE; FOUR; FIVE; SIX; SEVEN; EIGHT; 
             NINE; TEN; ELEVEN; TWELVE; THIRTEEN; FOURTEEN; FIFTEEN;
             SIXTEEN; SEVENTEEN; EIGHTEEN; NINETEEN; TWENTY];;

(*---------------------------------------------------------------------------*)
(*    Theorems regarding the vector summation and power of complex number    *)
(*---------------------------------------------------------------------------*)

let VSUM_0_LIST_ELEMENT_RMUL_POW = prove
 (`! a b c s. 
   vsum (0..0) (\t. (EL t [a]) * s pow t) = 
   a * (s pow 0)`,
  SIMP_TAC [VSUM_00; EL; HD; ADD1; TL]);;

let VSUM_1_LIST_ELEMENT_RMUL_POW = prove
 (`! a b c s. 
   vsum (0..1) (\t. (EL t [a; b]) * s pow t) = 
   a * (s pow 0) +  b *  (s pow 1)`,
  SIMP_TAC [VSUM_11] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_2_LIST_ELEMENT_RMUL_POW = prove
 (`! a b c s. 
   vsum (0..2) (\t. (EL t [a; b; c]) * s pow t) = 
   a * (s pow 0) +  b *  (s pow 1) + 
                           c *  (s pow 2)`,
  SIMP_TAC [VSUM_22] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_3_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d s. 
   vsum (0..3) (\t. (EL t [a; b; c; d]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3)`,
  SIMP_TAC [VSUM_33] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_4_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e s. 
   vsum (0..4) (\t. (EL t [a; b; c; d; e]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4)`,
  SIMP_TAC [VSUM_44] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_5_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f s. 
   vsum (0..5) (\t. (EL t [a; b; c; d; e; f]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5)`,
  SIMP_TAC [VSUM_55] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_6_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g s. 
   vsum (0..6) (\t. (EL t [a; b; c; d; e; f; g]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6)`,
  SIMP_TAC [VSUM_66] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_7_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h s. 
   vsum (0..7) (\t. (EL t [a; b; c; d; e; f; g; h]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7)`,
  SIMP_TAC [VSUM_77] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_8_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i s. 
   vsum (0..8) (\t. (EL t [a; b; c; d; e; f; g; h; i]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8)`,
  SIMP_TAC [VSUM_88] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_9_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j s. 
   vsum (0..9) (\t. (EL t [a; b; c; d; e; f; g; h; i; j]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9)`,
  SIMP_TAC [VSUM_99] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_10_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k s. 
   vsum (0..10) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10)`,
  SIMP_TAC [VSUM_1010] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_11_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l s. 
   vsum (0..11) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11)`,
  SIMP_TAC [VSUM_1111] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_12_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m s. 
   vsum (0..12) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12)`,
  SIMP_TAC [VSUM_1212] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_13_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n s. 
   vsum (0..13) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13)`,
  SIMP_TAC [VSUM_1313] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_14_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p s. 
   vsum (0..14) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + p * (s pow 14)`,
  SIMP_TAC [VSUM_1414] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;


let VSUM_15_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p q s. 
   vsum (0..15) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p; q]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + 
   p * (s pow 14) + q * (s pow 15)`,
  SIMP_TAC [VSUM_1515] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_16_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p q r s. 
   vsum (0..16) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p; q; r]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + 
   p * (s pow 14) + q * (s pow 15) +
   r * (s pow 16)`,
  SIMP_TAC [VSUM_1616] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_17_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p q r u s. 
   vsum (0..17) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p; q; r; u]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + 
   p * (s pow 14) + q * (s pow 15) +
   r * (s pow 16) + u * (s pow 17)`,
  SIMP_TAC [VSUM_1717] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_18_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p q r u v s. 
   vsum (0..18) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p; q; r; u; v]) * s pow t) = 
   a * (s pow 0) +  b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + 
   p * (s pow 14) + q * (s pow 15) +
   r * (s pow 16) + u * (s pow 17) + v * (s pow 18)`,
  SIMP_TAC [VSUM_1818] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_19_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p q r u v w s. 
   vsum (0..19) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p; q; r; u; v; w]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + 
   p * (s pow 14) + q * (s pow 15) +
   r * (s pow 16) + u * (s pow 17) + 
   v * (s pow 18) + w * (s pow 19)`,
  SIMP_TAC [VSUM_1919] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

let VSUM_20_LIST_ELEMENT_RMUL_POW = prove
 (`!a b c d e f g h i j k l m n p q r u v w x s. 
   vsum (0..20) (\t. (EL t [a; b; c; d; e; f; g; h; i; j; k; l; m; n; p; q; r; u; v; w; x]) * s pow t) = 
   a * (s pow 0) + b * (s pow 1) + 
   c * (s pow 2) + d * (s pow 3) +
   e * (s pow 4) + f * (s pow 5) +
   g * (s pow 6) + h * (s pow 7) +
   i * (s pow 8) + j * (s pow 9) +
   k * (s pow 10) + l * (s pow 11) +
   m * (s pow 12) + n * (s pow 13) + 
   p * (s pow 14) + q * (s pow 15) +
   r * (s pow 16) + u * (s pow 17) + 
   v * (s pow 18) + w * (s pow 19) + x * (s pow 20)`,
  SIMP_TAC [VSUM_2020] THEN NUM_SIMP_TAC THEN SIMP_TAC [EL; HD; TL]);;

(*---------------------------------------------------------------------------*)
(*               Theorems regarding the power of complex number              *)
(*---------------------------------------------------------------------------*)

let COMPLEX_POW_2 = prove
 (`!x. x pow 2 = x * x`,
  REWRITE_TAC [num_CONV `2`] THEN REWRITE_TAC [complex_pow; COMPLEX_POW_1]);;

let COMPLEX_POW_3 = prove
 (`!x. x pow 3 = x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_2] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_4 = prove
 (`!x. x pow 4 = x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_3] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_5 = prove
 (`!x. x pow 5 = x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_4] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_6 = prove
 (`!x. x pow 6 = x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_5] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_7 = prove
 (`!x. x pow 7 = x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_6] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_8 = prove
 (`!x. x pow 8 = x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_7] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_9 = prove
 (`!x. x pow 9 = x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_8] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_10 = prove
 (`!x. x pow 10 = x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_9] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_11 = prove
 (`!x. x pow 11 = x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_10] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_12 = prove
 (`!x. x pow 12 = x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_11] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_13 = prove
 (`!x. x pow 13 = x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_12] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_14 = prove
 (`!x. x pow 14 = x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_13] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_15 = prove
 (`!x. x pow 15 = x * x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_14] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_16 = prove
 (`!x. x pow 16 = x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_15] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_17 = prove
 (`!x. x pow 17 = x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_16] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_18 = prove
 (`!x. x pow 18 = x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_17] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_19 = prove
 (`!x. x pow 19 = x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_18] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

let COMPLEX_POW_20 = prove
 (`!x. x pow 20 = x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x`,
  REWRITE_TAC [GSYM COMPLEX_POW_19] THEN REWRITE_TAC [GSYM complex_pow] THEN ARITH_TAC);;

(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*                           End of the Verification                         *)
(*---------------------------------------------------------------------------*)
