(* ========================================================================= *)
(*                                                                           *)
(*     Formal Verification of Physical Human-Robot                           *)
(*              Interaction using Interactive Theorem Proving                *)
(*                                                                           *)
(*    (c) Copyright, Sa'ed Abed*, Adnan Rashid** and Osman Hasan**           *)
(*       *Computer Engineering Department,                                   *)
(*         College of Engineering and Petroleum, Kuwait University, Kuwait   *)
(*                                                                           *)
(*       **System Analysis and Verification (SAVe) Lab,                      *)
(*        National University of Sciences and Technology (NUST), Pakistan    *)
(*                                                                           *)
(* ========================================================================= *)

(*===========================================================================*)

(*===========================================================================*)

let print_typed_var fmt tm =
      let s,ty = dest_var tm in
      pp_print_string fmt ("("^s^":"^string_of_type ty^")") in
    install_user_printer("print_typed_var",print_typed_var);;


(*----For deleting type-----------*)

delete_user_printer "print_typed_var";;

(*===========================================================================*)

(*===========================================================================*)
(*            Formalization of Physical Human Robot Interaction              *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                Physical Interaction Parameters                            *)
(*---------------------------------------------------------------------------*)

new_type_abbrev ("m",`:real`);;  (*=Virtual Mass=*)
new_type_abbrev ("c",`:real`);;  (*=Virtual Damping=*)
new_type_abbrev ("k",`:real`);;  (*=Virtual Stiffness=*)
new_type_abbrev 
     ("phy_inter_par",`:m # c # k`);;  (*==Physical Interaction Parameters==*)


new_type_abbrev ("force_fun",`:real^1->complex`);;  (*=Type of Force Function=*)


new_type_abbrev ("dist_fun",`:real^1->complex`);;  (*=Distance function=*)

new_type_abbrev ("vel_fun",`:real^1->complex`);;  (*=Velocity function=*)


(* ------------------------------------------------------------------------- *)
(*                 Modeling one-dimensional Admittance Equation              *)
(* ------------------------------------------------------------------------- *)

let lst_x_fun = new_definition `  
    lst_x_fun ((m,c,k):phy_inter_par) = [Cx k; Cx c; Cx m]`;;


let lst_x0_fun = new_definition `  
    lst_x0_fun ((m,c,k):phy_inter_par) = [--Cx k; --Cx c; --Cx m]`;;


 let admit_eq_1d = new_definition
    `admit_eq_1d (fH:force_fun) (x:dist_fun) (x0:dist_fun) ((m,c,k):phy_inter_par) t  = 
          (fH t = diff_eq_n_order 2 (lst_x_fun (m,c,k)) x t +
                  diff_eq_n_order 2 (lst_x0_fun (m,c,k)) x0 t)`;; 


g `!fH x x0 m c k t.
  admit_eq_1d (fH:force_fun) (x:dist_fun) (x0:dist_fun) ((m,c,k):phy_inter_par) t =
  (fH t = Cx m * (vector_derivative (\t. vector_derivative x (at t)) (at t) -
                  vector_derivative (\t. vector_derivative x0 (at t)) (at t)) +
	  Cx c * (vector_derivative x (at t) - vector_derivative x0 (at t)) +
	  Cx k * (x t - x0 t))`;;

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [admit_eq_1d]);;
e (REWRITE_TAC [lst_x_fun; lst_x0_fun]);;
e (REWRITE_TAC [diff_eq_n_order]);;
e (REWRITE_TAC [VSUM_22; EL]);;
e (REWRITE_TAC [HD]);;
e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (SIMP_TAC [ETA_AX]);;
e (SUBGOAL_THEN `higher_vector_derivative 2 (x:real^1->complex) t = 
                       vector_derivative (\t. vector_derivative x (at t)) (at t)` ASSUME_TAC);;
      e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
      e (REWRITE_TAC [higher_vector_derivative]);;
      e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
      e (REWRITE_TAC [higher_vector_derivative]);;
      e (SIMP_TAC [ETA_AX]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `higher_vector_derivative 2 (x0:real^1->complex) t = 
                       vector_derivative (\t. vector_derivative x0 (at t)) (at t)` ASSUME_TAC);;
      e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
      e (REWRITE_TAC [higher_vector_derivative]);;
      e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
      e (REWRITE_TAC [higher_vector_derivative]);;
      e (SIMP_TAC [ETA_AX]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (CONV_TAC COMPLEX_FIELD);;

let ADMIT_EQ_1D_EQUIV_THM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(*      Modeling one-dimensional Admittance Equation under free motion       *)
(* ------------------------------------------------------------------------- *)


(*==Under the conditions when x_0, x_0^dot, x_0^dotdot and k is zero==*)


(*==fm stands for free motion, admit_eq stands for the admittance equation==*)

let lst_x_fm_fun = new_definition `  
    lst_x_fm_fun ((m,c,k):phy_inter_par) = [Cx (&0); Cx c; Cx m]`;;

 let admit_eq_fm_1d = new_definition
    `admit_eq_fm_1d (fH:force_fun) (x:dist_fun) ((m,c,k):phy_inter_par) t  = 
          (fH t = diff_eq_n_order 2 (lst_x_fm_fun (m,c,k)) x t)`;; 


g `!fH x m c k t.
 admit_eq_fm_1d (fH:force_fun) (x:dist_fun) ((m,c,k):phy_inter_par) t =
  (fH t = Cx m * vector_derivative (\t. vector_derivative x (at t)) (at t) + Cx c * vector_derivative x (at t))`;;

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [admit_eq_fm_1d]);;
e (REWRITE_TAC [lst_x_fm_fun]);;
e (REWRITE_TAC [diff_eq_n_order]);;
e (REWRITE_TAC [VSUM_22; EL]);;
e (REWRITE_TAC [HD]);;
e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (SIMP_TAC [ETA_AX]);;
e (SUBGOAL_THEN `higher_vector_derivative 2 (x:real^1->complex) t = 
                       vector_derivative (\t. vector_derivative x (at t)) (at t)` ASSUME_TAC);;
      e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
      e (REWRITE_TAC [higher_vector_derivative]);;
      e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
      e (REWRITE_TAC [higher_vector_derivative]);;
      e (SIMP_TAC [ETA_AX]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (REWRITE_TAC [ARITH_RULE `1 = SUC 0`]);;
e (REWRITE_TAC [EL; higher_vector_derivative; TL; HD]);;
e (CONV_TAC COMPLEX_FIELD);;

let ADMIT_EQ_FM_1D_EQUIV_THM = top_thm ();;


(*==Equivalence relationship between the one-dimensional admittance equations without free motion and with free motion under free motion assumptions==*)


g `!fH x x0 m c k t.
  x0 t = Cx (&0) /\
  vector_derivative x0 (at t) = Cx (&0) /\
  vector_derivative (\t. vector_derivative x0 (at t)) (at t) = Cx (&0) /\
  (k = &0)
     ==> admit_eq_1d (fH:force_fun) (x:dist_fun) (x0:dist_fun) ((m,c,k):phy_inter_par) t =
         admit_eq_fm_1d fH x (m,c,k) t`;;

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [ADMIT_EQ_1D_EQUIV_THM;ADMIT_EQ_FM_1D_EQUIV_THM]);;
e (ASM_SIMP_TAC []);;
e (CONV_TAC COMPLEX_FIELD);;

let ADMIT_EQ_WFM_EQ_FM = top_thm ();;


(*==Now we have to model the desired position in s domain, which is the laplace transform of the admittance equation with free motion==*)


let transfer_function = new_definition 
   `transfer_function s (x:real^1->complex) (y:real^1->complex) 
    = (laplace_transform y s / laplace_transform x s)`;;


(*--This is the definition of the Laplace transform of the admittance equation without free motion and its associated lemma--*)

let lap_tran_admit_eq_1d = new_definition
    `lap_tran_admit_eq_1d (fH:force_fun) (x:dist_fun) ((m,c,k):phy_inter_par) s  = 
          (laplace_transform fH s  = laplace_transform (\t. diff_eq_n_order 2 (lst_x_fun (m,c,k)) x t) s)`;; 



g `!(x:dist_fun) m c k s.
  laplace_exists_higher_deriv 2 x s /\
  (!t. differentiable_higher_derivative 2 x t) /\
  (zero_initial_conditions 1 x)
 ==> laplace_transform (\t. diff_eq_n_order 2 (lst_x_fun ((m,c,k):phy_inter_par)) x t) s =
   ((laplace_transform x s) * vsum (0..2) (\i. (EL i (lst_x_fun (m,c,k)))  * (s pow i) ))`;;

e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC LAPLACE_OF_DIFF_EQ_ZERO_INIT_SECOND);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC THEN REWRITE_TAC [ARITH_RULE `2 - 1 = 1`; ARITH_RULE `0 < 2`]);;

let LAPLACE_OF_RHS_ADMIT_EQ_GEN = top_thm ();;


(*--This is the definition of the Laplace transform of the admittance equation with free space and its associated lemma--*)

let lap_tran_admit_eq_fm_1d = new_definition
    `lap_tran_admit_eq_fm_1d (fH:force_fun) (x:dist_fun) ((m,c,k):phy_inter_par) s  = 
          (laplace_transform fH s  = laplace_transform (\t. diff_eq_n_order 2 (lst_x_fm_fun (m,c,k)) x t) s)`;; 


g `!(x:dist_fun) m c k s.
  laplace_exists_higher_deriv 2 x s /\
  (!t. differentiable_higher_derivative 2 x t) /\
  (zero_initial_conditions 1 x)
 ==> laplace_transform (\t. diff_eq_n_order 2 (lst_x_fm_fun ((m,c,k):phy_inter_par)) x t) s =
   ((laplace_transform x s) * vsum (0..2) (\i. (EL i (lst_x_fm_fun (m,c,k)))  * (s pow i) ))`;;

e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC LAPLACE_OF_DIFF_EQ_ZERO_INIT_SECOND);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC THEN REWRITE_TAC [ARITH_RULE `2 - 1 = 1`; ARITH_RULE `0 < 2`]);;

let LAPLACE_OF_RHS_ADMIT_EQ_GEN = top_thm ();;

(* ------------------------------------------------------------------------- *)

let TF_SUM_SIMP x = 
 REWRITE_TAC [x; VSUM_0_LIST_ELEMENT_RMUL_POW;
                VSUM_1_LIST_ELEMENT_RMUL_POW; VSUM_2_LIST_ELEMENT_RMUL_POW; 
                VSUM_3_LIST_ELEMENT_RMUL_POW; VSUM_4_LIST_ELEMENT_RMUL_POW;
		VSUM_5_LIST_ELEMENT_RMUL_POW; VSUM_6_LIST_ELEMENT_RMUL_POW;
		VSUM_7_LIST_ELEMENT_RMUL_POW; VSUM_8_LIST_ELEMENT_RMUL_POW;
                VSUM_9_LIST_ELEMENT_RMUL_POW; VSUM_10_LIST_ELEMENT_RMUL_POW;
	     VSUM_11_LIST_ELEMENT_RMUL_POW; VSUM_12_LIST_ELEMENT_RMUL_POW;
	     VSUM_13_LIST_ELEMENT_RMUL_POW; VSUM_14_LIST_ELEMENT_RMUL_POW;
	     VSUM_15_LIST_ELEMENT_RMUL_POW; VSUM_16_LIST_ELEMENT_RMUL_POW;
	     VSUM_17_LIST_ELEMENT_RMUL_POW; VSUM_18_LIST_ELEMENT_RMUL_POW;
	     VSUM_19_LIST_ELEMENT_RMUL_POW; VSUM_20_LIST_ELEMENT_RMUL_POW];;

let TF_POW_SIMP x = 
 REWRITE_TAC [x; COMPLEX_POW_1; COMPLEX_POW_2; COMPLEX_POW_3; COMPLEX_POW_4;
	     COMPLEX_POW_5; COMPLEX_POW_6; COMPLEX_POW_7; COMPLEX_POW_8;
	     COMPLEX_POW_9; COMPLEX_POW_10; COMPLEX_POW_11; COMPLEX_POW_12;
	  COMPLEX_POW_13; COMPLEX_POW_14; COMPLEX_POW_15; COMPLEX_POW_16;
	  COMPLEX_POW_17; COMPLEX_POW_18; COMPLEX_POW_19; COMPLEX_POW_20];;

let TF_ARITH_TAC = 
 ASM_REWRITE_TAC 
   [ARITH_RULE `0 - 1 = 0`;
    ARITH_RULE `1 - 1 = 0`; ARITH_RULE `2 - 1 = 1`; ARITH_RULE `3 - 1 = 2`;
    ARITH_RULE `4 - 1 = 3`; ARITH_RULE `5 - 1 = 4`; ARITH_RULE `6 - 1 = 5`;
    ARITH_RULE `7 - 1 = 6`; ARITH_RULE `8 - 1 = 7`; ARITH_RULE `9 - 1 = 8`;
    ARITH_RULE `10 - 1 = 9`; ARITH_RULE `11 - 1 = 10`; ARITH_RULE `12 - 1 = 11`;
    ARITH_RULE `13 - 1 = 12`; ARITH_RULE `14 - 1 = 13`; ARITH_RULE `15 - 1 = 14`;
    ARITH_RULE `16 - 1 = 15`; ARITH_RULE `17 - 1 = 16`; ARITH_RULE `18 - 1 = 17`;
    ARITH_RULE `19 - 1 = 18`; ARITH_RULE `20 - 1 = 19`; ARITH_RULE `21 - 1 = 20`];;

(* ------------------------------------------------------------------------- *)

(**-----transfer function = Xd / FH = 1 / s (ms + c)-----**)

let tf_fm_admit_eq = new_definition 
   `tf_fm_admit_eq (fH:force_fun) (xd:vel_fun) ((m,c,k):phy_inter_par) s
    = ( transfer_function s fH xd = 
    (Cx (&1) / (s * (Cx m * s + Cx c)) ))`;;

let valid_phycl_intractn_parmtrs = new_definition 
   `valid_phycl_intractn_parmtrs ((m,c,k):phy_inter_par)
    = ((&0 < k) /\ (&0 < c) /\ (&0 < m))`;;

let valid_phycl_intractn_parmtrs_fm = new_definition 
   `valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par)
    = ((&0 < c) /\ (&0 < m))`;;

let lst_fH_fm_fun = new_definition `  
     lst_fH_fm_fun = [(Cx (&1))]`;;


 let admit_eq_fm_1d_alt = new_definition
    `admit_eq_fm_1d_alt (fH:force_fun) (x:dist_fun) ((m,c,k):phy_inter_par) t  = 
          (diff_eq_n_order 0 (lst_fH_fm_fun) fH t =
	   diff_eq_n_order 2 (lst_x_fm_fun (m,c,k)) x t)`;; 


g `!k c m (fH:force_fun) (xd:vel_fun) s.
   valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
   (!t. differentiable_higher_derivative 2 xd t) /\  
   (!t. differentiable_higher_derivative 0 fH t) /\
   (laplace_exists_higher_deriv 2 xd s) /\ 
   (laplace_exists_higher_deriv 0 fH s) /\
    zero_initial_conditions 1 xd /\
  ~(laplace_transform fH s = Cx (&0)) /\
  ~((s * (Cx m * s + Cx c)) = Cx (&0)) /\
   (!t. admit_eq_fm_1d_alt fH xd (m,c,k) t)
    ==> 
     tf_fm_admit_eq fH xd (m,c,k) s`;;

e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm; admit_eq_fm_1d_alt; tf_fm_admit_eq; transfer_function]);;
e (REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [COMPLEX_FIELD
       `! a b c d. ~(d = Cx (&0)) /\  ~(b = Cx (&0)) ==> ( (a / b = c / d ) = (a * d = b * c ))`]);;
e (SUBGOAL_THEN
    `s * (Cx m * s + Cx c) = 
      vsum (0..2) (\i. (EL i (lst_x_fm_fun (m,c,k))) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_x_fm_fun);;
      e (SIMP_TAC [CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN
    `Cx (&1) = 
      vsum (0..0) (\i. (EL i lst_fH_fm_fun) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_fH_fm_fun);;
      e (TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND);;
e (TF_ARITH_TAC THEN ASM_SIMP_TAC [diff_eq_n_order_sys] THEN ARITH_TAC);;

let TF_ADMIT_EQ_FM_1D = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(*

Tc: A time constant related to parameters modeling bias and imperfections

V (s) / f_H (s) = (1 / c) / (((m / c) * s + 1) * (Tc * s + 1))

*)

let lst_Vs_fun_olm = new_definition `  
    lst_Vs_fun_olm ((m,c,k):phy_inter_par) Tc =
              [Cx (&1); (Cx m / Cx c) + Cx Tc; (Cx m / Cx c) * Cx Tc]`;;


let lst_fH_fun_olm = new_definition `  
    lst_fH_fun_olm ((m,c,k):phy_inter_par) = [Cx (&1) / Cx c]`;;


 let admit_eq_1d_olm = new_definition
    `admit_eq_1d_olm (fH:force_fun) (Vs:vel_fun) ((m,c,k):phy_inter_par) Tc t  = 
          (diff_eq_n_order 2 (lst_Vs_fun_olm (m,c,k) Tc) Vs t =
                  diff_eq_n_order 0 (lst_fH_fun_olm (m,c,k)) fH t)`;; 

let tf_admit_eq_olm = new_definition 
   `tf_admit_eq_olm (fH:force_fun) (Vs:vel_fun) ((m,c,k):phy_inter_par) Tc s
    = ( transfer_function s fH Vs = 
    ((Cx (&1) / Cx c) / (((Cx m / Cx c) * Cx Tc) * s pow 2 + ((Cx m / Cx c) + Cx Tc) * s + Cx (&1))) )`;;
    

g `!k c m (fH:force_fun) (Vs:vel_fun) Tc s.
   valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
   (!t. differentiable_higher_derivative 2 Vs t) /\  
   (!t. differentiable_higher_derivative 0 fH t) /\
   (laplace_exists_higher_deriv 2 Vs s) /\ 
   (laplace_exists_higher_deriv 0 fH s) /\
    zero_initial_conditions 1 Vs /\
  ~(laplace_transform fH s = Cx (&0)) /\
  ~((((Cx m / Cx c) * Cx Tc) * s pow 2 + ((Cx m / Cx c) + Cx Tc) * s + Cx (&1)) = Cx (&0)) /\
   (!t. admit_eq_1d_olm fH Vs (m,c,k) Tc t)
    ==> 
     tf_admit_eq_olm fH Vs (m,c,k) Tc s`;;

e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm; admit_eq_1d_olm; tf_admit_eq_olm; transfer_function]);;
e (REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [COMPLEX_FIELD
       `! a b c d. ~(d = Cx (&0)) /\  ~(b = Cx (&0)) ==> ( (a / b = c / d ) = (a * d = b * c ))`]);;
e (SUBGOAL_THEN
    `((Cx m / Cx c * Cx Tc) * s pow 2 + (Cx m / Cx c + Cx Tc) * s + Cx (&1)) = 
      vsum (0..2) (\i. (EL i (lst_Vs_fun_olm (m,c,k) Tc)) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_Vs_fun_olm);;
      e (SIMP_TAC [CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN
    `Cx (&1) / Cx c = 
      vsum (0..0) (\i. (EL i (lst_fH_fun_olm (m,c,k))) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_fH_fun_olm);;
      e (TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND);;
e (TF_ARITH_TAC THEN ASM_SIMP_TAC [diff_eq_n_order_sys] THEN ARITH_TAC);;

let TF_ADMIT_EQ_1D_OLM = top_thm ();;


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(*---  The closed-loop model verification  ---*)


let lst_Vs_fun_clm = new_definition `  
    lst_Vs_fun_clm ((m,c,k):phy_inter_par) Tc KH =
              [Cx KH; Cx c; (Cx c * Cx Tc) + Cx m; Cx m * Cx Tc]`;;

let lst_fH_fun_clm = new_definition `  
    lst_fH_fun_clm = [Cx (&0); Cx (&1)]`;;


let admit_eq_1d_clm = new_definition
    `admit_eq_1d_clm (fH:force_fun) (Vs:dist_fun) ((m,c,k):phy_inter_par) Tc KH t = 
          (diff_eq_n_order 3 (lst_Vs_fun_clm (m,c,k) Tc KH) Vs t =
                  diff_eq_n_order 1 lst_fH_fun_clm fH t)`;; 

let tf_admit_eq_clm = new_definition 
   `tf_admit_eq_clm (fH:force_fun) (Vs:vel_fun) ((m,c,k):phy_inter_par) Tc KH s
    = ( transfer_function s fH Vs = 
    (s / ((Cx m * Cx Tc) * s pow 3 + ((Cx c * Cx Tc) + Cx m) * s pow 2 + Cx c * s + Cx KH)) )`;;


g `!k c m (fH:force_fun) (Vs:vel_fun) Tc KH s.
   valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
   (!t. differentiable_higher_derivative 3 Vs t) /\  
   (!t. differentiable_higher_derivative 1 fH t) /\
   (laplace_exists_higher_deriv 3 Vs s) /\ 
   (laplace_exists_higher_deriv 1 fH s) /\
    zero_initial_conditions 2 Vs /\
    zero_initial_conditions 0 fH /\
  ~(laplace_transform fH s = Cx (&0)) /\
  ~(((Cx m * Cx Tc) * s pow 3 + ((Cx c * Cx Tc) + Cx m) * s pow 2 + Cx c * s + Cx KH) = Cx (&0)) /\
   (!t. admit_eq_1d_clm fH Vs (m,c,k) Tc KH t)
    ==> 
     tf_admit_eq_clm fH Vs (m,c,k) Tc KH s`;;

e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm; admit_eq_1d_clm; tf_admit_eq_clm; transfer_function]);;
e (REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [COMPLEX_FIELD
       `! a b c d. ~(d = Cx (&0)) /\  ~(b = Cx (&0)) ==> ( (a / b = c / d ) = (a * d = b * c ))`]);;
e (SUBGOAL_THEN
    `((Cx m * Cx Tc) * s pow 3 + (Cx c * Cx Tc + Cx m) * s pow 2 + Cx c * s + Cx KH) = 
      vsum (0..3) (\i. (EL i (lst_Vs_fun_clm (m,c,k) Tc KH)) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_Vs_fun_clm);;
      e (SIMP_TAC [CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `laplace_transform fH s * s = laplace_transform fH s * vsum (0..1) (\i. EL i lst_fH_fun_clm * s pow i)` ASSUME_TAC);;
      e (AP_TERM_TAC);;
      e (TF_SUM_SIMP lst_fH_fun_clm);;
      e (TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND);;
e (TF_ARITH_TAC THEN ASM_SIMP_TAC [diff_eq_n_order_sys]);;

let TF_ADMIT_EQ_1D_CLM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(*---  The improved open-loop model verification  ---*)


let lst_Vs_fun_iolm = new_definition `  
    lst_Vs_fun_iolm ((m,c,k):phy_inter_par) Kp KB CB CR MR mR Tc =
        [Cx c * (Cx Kp * Cx KB + Cx KB * Cx CR);
	  Cx m * (Cx Kp * Cx KB + Cx KB * Cx CR) + Cx c * (Cx CB * Cx CR + Cx KB * Cx MR + Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CR + Cx mR * Cx KB + Cx KB * Cx CR); 			  
			       Cx m * (Cx CB * Cx CR + Cx KB * Cx MR + Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CR + Cx mR * Cx KB + Cx KB * Cx CR) + Cx c * (Cx Kp * Cx MR + Cx mR * Cx CB + Cx mR * Cx KB * Cx Tc + Cx mR * Cx CR + Cx CB * Cx MR + Cx CB * Cx CR * Cx Tc + Cx KB * Cx MR * Cx Tc); 
			         Cx m * (Cx Kp * Cx MR + Cx mR * Cx CB + Cx mR * Cx KB * Cx Tc + Cx mR * Cx CR + Cx CB * Cx MR + Cx CB * Cx CR * Cx Tc + Cx KB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR + Cx mR * Cx CR * Cx Tc + Cx mR * Cx CB * Cx Tc + Cx CB * Cx MR * Cx Tc); 
			           Cx m * (Cx mR * Cx MR + Cx mR * Cx CR * Cx Tc + Cx mR * Cx CB * Cx Tc + Cx CB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR * Cx Tc); 
						 Cx m * (Cx mR * Cx MR * Cx Tc)]`;;

let lst_fH_fun_iolm = new_definition `  
    lst_fH_fun_iolm KB CB Kp = [Cx Kp * Cx KB; Cx Kp * Cx CB]`;;


let admit_eq_1d_iolm = new_definition
    `admit_eq_1d_iolm (fH:force_fun) (Vs:dist_fun) ((m,c,k):phy_inter_par) Kp KB CB CR MR mR Tc t = 
          (diff_eq_n_order 5 (lst_Vs_fun_iolm (m,c,k) Kp KB CB CR MR mR Tc) Vs t =
                  diff_eq_n_order 1 (lst_fH_fun_iolm KB CB Kp) fH t)`;; 


let tf_admit_eq_iolm = new_definition 
   `tf_admit_eq_iolm (fH:force_fun) (Vs:vel_fun) ((m,c,k):phy_inter_par) Kp KB CB CR MR mR Tc s
    = ( transfer_function s fH Vs = 
    ((Cx Kp * Cx CB * s + Cx Kp * Cx KB) / 
	 ((Cx m * (Cx mR * Cx MR * Cx Tc)) * s pow 5 + (Cx m * (Cx mR * Cx MR + Cx mR * Cx CR * Cx Tc + Cx mR * Cx CB * Cx Tc + Cx CB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR * Cx Tc)) * s pow 4 + 
	       (Cx m * (Cx Kp * Cx MR + Cx mR * Cx CB + Cx mR * Cx KB * Cx Tc + Cx mR * Cx CR + Cx CB * Cx MR + Cx CB * Cx CR * Cx Tc + Cx KB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR + Cx mR * Cx CR * Cx Tc + Cx mR * Cx CB * Cx Tc + Cx CB * Cx MR * Cx Tc)) * s pow 3 + (Cx m * (Cx CB * Cx CR + Cx KB * Cx MR + Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CR + Cx mR * Cx KB + Cx KB * Cx CR) + Cx c * (Cx Kp * Cx MR + Cx mR * Cx CB + Cx mR * Cx KB * Cx Tc + Cx mR * Cx CR + Cx CB * Cx MR + Cx CB * Cx CR * Cx Tc + Cx KB * Cx MR * Cx Tc)) * s pow 2 + 
		                      (Cx m * (Cx Kp * Cx KB + Cx KB * Cx CR) + Cx c * (Cx CB * Cx CR + Cx KB * Cx MR + Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CR + Cx mR * Cx KB + Cx KB * Cx CR)) * s + Cx c * (Cx Kp * Cx KB + Cx KB * Cx CR))) )`;;


(*===============-----------------========================*)


g `!k c m (fH:force_fun) (Vs:vel_fun) Kp KB CB CR MR mR Tc s.
   valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
   (!t. differentiable_higher_derivative 5 Vs t) /\  
   (!t. differentiable_higher_derivative 1 fH t) /\
   (laplace_exists_higher_deriv 5 Vs s) /\ 
   (laplace_exists_higher_deriv 1 fH s) /\
    zero_initial_conditions 4 Vs /\
    zero_initial_conditions 0 fH /\
  ~(laplace_transform fH s = Cx (&0)) /\
  ~(((Cx m * (Cx mR * Cx MR * Cx Tc)) * s pow 5 + 
    (Cx m * (Cx mR * Cx MR + Cx mR * Cx CR * Cx Tc + Cx mR * Cx CB * Cx Tc + Cx CB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR * Cx Tc)) * s pow 4 + 
	       (Cx m * (Cx Kp * Cx MR + Cx mR * Cx CB + Cx mR * Cx KB * Cx Tc + Cx mR * Cx CR + Cx CB * Cx MR + Cx CB * Cx CR * Cx Tc + Cx KB * Cx MR * Cx Tc) + 
		             Cx c * (Cx mR * Cx MR + Cx mR * Cx CR * Cx Tc + Cx mR * Cx CB * Cx Tc + Cx CB * Cx MR * Cx Tc)) * s pow 3 + 
		       (Cx m * (Cx CB * Cx CR + Cx KB * Cx MR + Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CR + Cx mR * Cx KB + Cx KB * Cx CR) + 
			      Cx c * (Cx Kp * Cx MR + Cx mR * Cx CB + Cx mR * Cx KB * Cx Tc + Cx mR * Cx CR + Cx CB * Cx MR + Cx CB * Cx CR * Cx Tc + Cx KB * Cx MR * Cx Tc)) * s pow 2 + 
		                      (Cx m * (Cx Kp * Cx KB + Cx KB * Cx CR) + 
							  Cx c * (Cx CB * Cx CR + Cx KB * Cx MR + Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CR + Cx mR * Cx KB + Cx KB * Cx CR)) * s + 
							  Cx c * (Cx Kp * Cx KB + Cx KB * Cx CR)) = Cx (&0)) /\
   (!t. admit_eq_1d_iolm fH Vs (m,c,k) Kp KB CB CR MR mR Tc t)
    ==> 
     tf_admit_eq_iolm fH Vs (m,c,k) Kp KB CB CR MR mR Tc s`;;


e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm; admit_eq_1d_iolm; tf_admit_eq_iolm; transfer_function]);;
e (REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [COMPLEX_FIELD
       `! a b c d. ~(d = Cx (&0)) /\  ~(b = Cx (&0)) ==> ( (a / b = c / d ) = (a * d = b * c ))`]);;

e (SUBGOAL_THEN
    `((Cx m * (Cx mR * Cx MR * Cx Tc)) * s pow 5 + (Cx m * (Cx mR * Cx MR +
    Cx mR * Cx CR * Cx Tc +
    Cx mR * Cx CB * Cx Tc +
    Cx CB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR * Cx Tc)) * s pow 4 + 
	       (Cx m * (Cx Kp * Cx MR +
    Cx mR * Cx CB +
    Cx mR * Cx KB * Cx Tc +
    Cx mR * Cx CR +
    Cx CB * Cx MR +
    Cx CB * Cx CR * Cx Tc +
    Cx KB * Cx MR * Cx Tc) + Cx c * (Cx mR * Cx MR +
    Cx mR * Cx CR * Cx Tc +
    Cx mR * Cx CB * Cx Tc +
    Cx CB * Cx MR * Cx Tc)) * s pow 3 + (Cx m * (Cx CB * Cx CR +
    Cx KB * Cx MR +
    Cx KB * Cx CR * Cx Tc +
    Cx Kp * Cx CR +
    Cx mR * Cx KB +
    Cx KB * Cx CR) + Cx c * (Cx Kp * Cx MR +
    Cx mR * Cx CB +
    Cx mR * Cx KB * Cx Tc +
    Cx mR * Cx CR +
    Cx CB * Cx MR +
    Cx CB * Cx CR * Cx Tc +
    Cx KB * Cx MR * Cx Tc)) * s pow 2 + 
		                      (Cx m * (Cx Kp * Cx KB + Cx KB * Cx CR) + Cx c * (Cx CB * Cx CR +
    Cx KB * Cx MR +
    Cx KB * Cx CR * Cx Tc +
    Cx Kp * Cx CR +
    Cx mR * Cx KB +
    Cx KB * Cx CR)) * s + Cx c * (Cx Kp * Cx KB + Cx KB * Cx CR)) = 
      vsum (0..5) (\i. (EL i (lst_Vs_fun_iolm (m,c,k) Kp KB CB CR MR mR Tc)) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_Vs_fun_iolm);;
      e (SIMP_TAC [CX_ADD; CX_SUB; CX_MUL; CX_DIV] THEN TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `laplace_transform fH s * (Cx Kp * Cx CB * s + Cx Kp * Cx KB) = laplace_transform fH s * vsum (0..1) (\i. EL i (lst_fH_fun_iolm_final KB CB Kp) * s pow i)` ASSUME_TAC);;
      e (AP_TERM_TAC);;
      e (TF_SUM_SIMP lst_fH_fun_iolm);;
      e (TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND);;
e (TF_ARITH_TAC THEN ASM_SIMP_TAC [diff_eq_n_order_sys]);;

let TF_ADMIT_EQ_1D_IOLM = top_thm ();;


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(*---  The improved closed-loop model verification  ---*)


let lst_Vs_fun_iclm = new_definition `  
    lst_Vs_fun_iclm ((m,c,k):phy_inter_par) Kp KH KB KR CB CR CH MR mR Tc =
              [(Cx Kp * Cx KH * Cx KB);
	          (Cx c * Cx Kp * Cx KB + Cx Kp * Cx KH * Cx CB + 
         Cx Kp * Cx CH * Cx KB + Cx c * Cx KB * Cx CR);
	    (Cx m * Cx KB * Cx CR + Cx c * Cx Kp * Cx CB + Cx m * Cx Kp * Cx KB + 
       Cx c * Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CH * Cx CB + Cx c * Cx mR * Cx KB + 
	   Cx c * Cx CB * Cx CR + Cx c * Cx KB * Cx MR + Cx c * Cx Kp * Cx CR);
	      (Cx c * Cx CB * Cx CR * Cx Tc + Cx m * Cx mR * Cx KB + Cx m * Cx Kp * Cx  CB + 
         Cx m * Cx CB * Cx CR + Cx m * Cx KB * Cx MR + Cx c * Cx CB * Cx MR + Cx c * Cx Kp * Cx MR +
           Cx c * Cx Kp * Cx MR * Cx Tc + Cx c * Cx mR * Cx CB + Cx m * Cx Kp * Cx CR + 
		      Cx m * Cx KB * Cx CR * Cx Tc + Cx c * Cx mR * Cx KB * Cx Tc + Cx CR * Cx mR * Cx c);
	        (Cx c * Cx CB * Cx MR * Cx Tc + Cx c * Cx mR * Cx MR + Cx m * Cx Kp * Cx MR + Cx m * Cx mR * Cx CB + Cx m * Cx mR * Cx CR + 
         Cx m * Cx mR * Cx CR * Cx Tc + Cx m * Cx mR * Cx CB * Cx Tc + Cx m * Cx KB * Cx MR * Cx Tc + 
		   Cx m * Cx CB * Cx CR * Cx Tc + Cx m * Cx CB * Cx MR + Cx m * Cx mR * Cx KR * Cx Tc);
		  (Cx m * Cx CB * Cx MR * Cx Tc + Cx m * Cx mR * Cx CR * Cx Tc + Cx m * Cx mR * Cx CB * Cx Tc + Cx m * Cx mR * Cx MR + Cx c * Cx mR * Cx MR * Cx Tc);
		    (Cx m * Cx mR * Cx MR * Cx Tc)]`;;


let lst_fH_fun_iclm = new_definition `  
    lst_fH_fun_iclm KB CB Kp CH KH =
                        [Cx (&0);
	                     Cx Kp * Cx KB * Cx KH; 
	                         Cx Kp * Cx CB * Cx KH + Cx Kp * Cx CH * Cx KB; 
	                                        Cx Kp * Cx CB * Cx CH]`;;

let admit_eq_1d_iclm = new_definition
    `admit_eq_1d_iclm (fH:force_fun) (Vs:dist_fun) ((m,c,k):phy_inter_par) Kp KH KB KR CB CR CH MR mR Tc  t = 
        (diff_eq_n_order 6 (lst_Vs_fun_iclm (m,c,k) Kp KH KB KR CB CR CH MR mR Tc) Vs t =
                  diff_eq_n_order 3 (lst_fH_fun_iclm KB CB Kp CH KH) fH t)`;; 



let tf_admit_eq_iclm = new_definition 
   `tf_admit_eq_iclm (fH:force_fun) (Vs:vel_fun) ((m,c,k):phy_inter_par) Kp KH KB KR CB CR CH MR mR Tc s
    = ( transfer_function s fH Vs = 
    (((Cx Kp * Cx CB * Cx CH) * s pow 3 + 
				    (Cx Kp * Cx CB * Cx KH + Cx Kp * Cx CH * Cx KB) * s pow 2 + 
		             (Cx Kp * Cx KB * Cx KH) * s ) / 
	 ((Cx m * Cx mR * Cx MR * Cx Tc) * s pow 6 + 
	    (Cx m * Cx CB * Cx MR * Cx Tc + Cx m * Cx mR * Cx CR * Cx Tc + Cx m * Cx mR * Cx CB * Cx Tc + Cx m * Cx mR * Cx MR + Cx c * Cx mR * Cx MR * Cx Tc) * s pow 5 + 
		     (Cx c * Cx CB * Cx MR * Cx Tc + Cx c * Cx mR * Cx MR + Cx m * Cx Kp * Cx MR + Cx m * Cx mR * Cx CB + Cx m * Cx mR * Cx CR + 
         Cx m * Cx mR * Cx CR * Cx Tc + Cx m * Cx mR * Cx CB * Cx Tc + Cx m * Cx KB * Cx MR * Cx Tc + 
		   Cx m * Cx CB * Cx CR * Cx Tc + Cx m * Cx CB * Cx MR + Cx m * Cx mR * Cx KR * Cx Tc) * s pow 4 + 
	            (Cx c * Cx CB * Cx CR * Cx Tc + Cx m * Cx mR * Cx KB + Cx m * Cx Kp * Cx  CB + 
         Cx m * Cx CB * Cx CR + Cx m * Cx KB * Cx MR + Cx c * Cx CB * Cx MR + Cx c * Cx Kp * Cx MR +
           Cx c * Cx Kp * Cx MR * Cx Tc + Cx c * Cx mR * Cx CB + Cx m * Cx Kp * Cx CR + 
		      Cx m * Cx KB * Cx CR * Cx Tc + Cx c * Cx mR * Cx KB * Cx Tc + Cx CR * Cx mR * Cx c) * s pow 3 + 
				   (Cx m * Cx KB * Cx CR + Cx c * Cx Kp * Cx CB + Cx m * Cx Kp * Cx KB + 
       Cx c * Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CH * Cx CB + Cx c * Cx mR * Cx KB + 
	   Cx c * Cx CB * Cx CR + Cx c * Cx KB * Cx MR + Cx c * Cx Kp * Cx CR) * s pow 2 + 
		             (Cx c * Cx Kp * Cx KB + Cx Kp * Cx KH * Cx CB + 
         Cx Kp * Cx CH * Cx KB + Cx c * Cx KB * Cx CR) * s + 
						(Cx Kp * Cx KH * Cx KB))) )`;;


g `!k c m (fH:force_fun) (Vs:vel_fun) Kp KH KB KR CB CR CH MR mR Tc s.
   valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
   (!t. differentiable_higher_derivative 6 Vs t) /\  
   (!t. differentiable_higher_derivative 3 fH t) /\
   (laplace_exists_higher_deriv 6 Vs s) /\ 
   (laplace_exists_higher_deriv 3 fH s) /\
    zero_initial_conditions 5 Vs /\
    zero_initial_conditions 2 fH /\
  ~(laplace_transform fH s = Cx (&0)) /\
  ~(((Cx m * Cx mR * Cx MR * Cx Tc) * s pow 6 + 
	    (Cx m * Cx CB * Cx MR * Cx Tc + Cx m * Cx mR * Cx CR * Cx Tc + Cx m * Cx mR * Cx CB * Cx Tc + Cx m * Cx mR * Cx MR + Cx c * Cx mR * Cx MR * Cx Tc) * s pow 5 + 
		     (Cx c * Cx CB * Cx MR * Cx Tc + Cx c * Cx mR * Cx MR + Cx m * Cx Kp * Cx MR + Cx m * Cx mR * Cx CB + Cx m * Cx mR * Cx CR + 
         Cx m * Cx mR * Cx CR * Cx Tc + Cx m * Cx mR * Cx CB * Cx Tc + Cx m * Cx KB * Cx MR * Cx Tc + 
		   Cx m * Cx CB * Cx CR * Cx Tc + Cx m * Cx CB * Cx MR + Cx m * Cx mR * Cx KR * Cx Tc) * s pow 4 + 
	            (Cx c * Cx CB * Cx CR * Cx Tc + Cx m * Cx mR * Cx KB + Cx m * Cx Kp * Cx  CB + 
         Cx m * Cx CB * Cx CR + Cx m * Cx KB * Cx MR + Cx c * Cx CB * Cx MR + Cx c * Cx Kp * Cx MR +
           Cx c * Cx Kp * Cx MR * Cx Tc + Cx c * Cx mR * Cx CB + Cx m * Cx Kp * Cx CR + 
		      Cx m * Cx KB * Cx CR * Cx Tc + Cx c * Cx mR * Cx KB * Cx Tc + Cx CR * Cx mR * Cx c) * s pow 3 + 
				   (Cx m * Cx KB * Cx CR + Cx c * Cx Kp * Cx CB + Cx m * Cx Kp * Cx KB + 
       Cx c * Cx KB * Cx CR * Cx Tc + Cx Kp * Cx CH * Cx CB + Cx c * Cx mR * Cx KB + 
	   Cx c * Cx CB * Cx CR + Cx c * Cx KB * Cx MR + Cx c * Cx Kp * Cx CR) * s pow 2 + 
		             (Cx c * Cx Kp * Cx KB + Cx Kp * Cx KH * Cx CB + 
         Cx Kp * Cx CH * Cx KB + Cx c * Cx KB * Cx CR) * s + 
						(Cx Kp * Cx KH * Cx KB)) = Cx (&0)) /\
   (!t. admit_eq_1d_iclm fH Vs (m,c,k) Kp KH KB KR CB CR CH MR mR Tc t)
    ==> 
     tf_admit_eq_iclm fH Vs (m,c,k) Kp KH KB KR CB CR CH MR mR Tc s`;;


e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm; admit_eq_1d_iclm; tf_admit_eq_iclm; transfer_function]);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC
    [COMPLEX_FIELD
       `! a b c d. ~(d = Cx (&0)) /\  ~(b = Cx (&0)) ==> ( (a / b = c / d ) = (a * d = b * c ))`]);;


e (SUBGOAL_THEN
    `((Cx m * Cx mR * Cx MR * Cx Tc) * s pow 6 +
          (Cx m * Cx CB * Cx MR * Cx Tc +
           Cx m * Cx mR * Cx CR * Cx Tc +
           Cx m * Cx mR * Cx CB * Cx Tc +
           Cx m * Cx mR * Cx MR +
           Cx c * Cx mR * Cx MR * Cx Tc) *
          s pow 5 +
          (Cx c * Cx CB * Cx MR * Cx Tc +
           Cx c * Cx mR * Cx MR +
           Cx m * Cx Kp * Cx MR +
           Cx m * Cx mR * Cx CB +
           Cx m * Cx mR * Cx CR +
           Cx m * Cx mR * Cx CR * Cx Tc +
           Cx m * Cx mR * Cx CB * Cx Tc +
           Cx m * Cx KB * Cx MR * Cx Tc +
           Cx m * Cx CB * Cx CR * Cx Tc +
           Cx m * Cx CB * Cx MR +
           Cx m * Cx mR * Cx KR * Cx Tc) *
          s pow 4 +
          (Cx c * Cx CB * Cx CR * Cx Tc +
           Cx m * Cx mR * Cx KB +
           Cx m * Cx Kp * Cx CB +
           Cx m * Cx CB * Cx CR +
           Cx m * Cx KB * Cx MR +
           Cx c * Cx CB * Cx MR +
           Cx c * Cx Kp * Cx MR +
           Cx c * Cx Kp * Cx MR * Cx Tc +
           Cx c * Cx mR * Cx CB +
           Cx m * Cx Kp * Cx CR +
           Cx m * Cx KB * Cx CR * Cx Tc +
           Cx c * Cx mR * Cx KB * Cx Tc +
           Cx CR * Cx mR * Cx c) *
          s pow 3 +
          (Cx m * Cx KB * Cx CR +
           Cx c * Cx Kp * Cx CB +
           Cx m * Cx Kp * Cx KB +
           Cx c * Cx KB * Cx CR * Cx Tc +
           Cx Kp * Cx CH * Cx CB +
           Cx c * Cx mR * Cx KB +
           Cx c * Cx CB * Cx CR +
           Cx c * Cx KB * Cx MR +
           Cx c * Cx Kp * Cx CR) *
          s pow 2 +
          (Cx c * Cx Kp * Cx KB +
           Cx Kp * Cx KH * Cx CB +
           Cx Kp * Cx CH * Cx KB +
           Cx c * Cx KB * Cx CR) *
          s +
          Cx Kp * Cx KH * Cx KB) = 
      vsum (0..6) (\i. (EL i (lst_Vs_fun_iclm (m,c,k) Kp KH KB KR CB CR CH MR mR Tc)) * s pow i)`
    ASSUME_TAC);;
      e (TF_SUM_SIMP lst_Vs_fun_iclm);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `laplace_transform fH s * ((Cx Kp * Cx CB * Cx CH) * s pow 3 + 
				    (Cx Kp * Cx CB * Cx KH + Cx Kp * Cx CH * Cx KB) * s pow 2 + 
		             (Cx Kp * Cx KB * Cx KH) * s ) = laplace_transform fH s * vsum (0..3) (\i. EL i (lst_fH_fun_iclm KB CB Kp CH KH) * s pow i)` ASSUME_TAC);;
      e (AP_TERM_TAC);;
      e (TF_SUM_SIMP lst_fH_fun_iclm);;
      e (TF_POW_SIMP complex_pow THEN CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC TRANSFER_FUNCTION_OF_N_ORDER_SYS_ALT_SECOND);;
e (TF_ARITH_TAC THEN ASM_SIMP_TAC [diff_eq_n_order_sys]);;

let TF_ADMIT_EQ_1D_ICLM = top_thm ();;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)


(*========Stability of Physical Human-robot Interaction (pHRI)========*)


let is_stable_phycl_intractn = new_definition 
    `is_stable_phycl_intractn (p:complex -> complex)  = 
          ~ ({x | p x = Cx(&0) /\ Re x < (&0)} = EMPTY)`;; 

let REAL_INV_NZ = prove
 (`!x. ~(x = &0) ==> ~(inv x = &0)`,
  GEN_TAC THEN DISCH_TAC THEN DISCH_THEN (MP_TAC o AP_TERM `(*) (x:real)`) THEN
  ASM_SIMP_TAC [REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `(x * inv x)=(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_SIMP_TAC [];
    PURE_ASM_SIMP_TAC [] THEN CONV_TAC REAL_FIELD]);;


let REAL_INV_POS = prove(
  `!x. &0 < x ==> &0 < inv x`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT_TCL DISJ_CASES_THEN
   MP_TAC (SPECL [`inv x:real`; `&0`] REAL_LT_TOTAL) THENL
   [POP_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_NZ o
              GSYM o MATCH_MP REAL_LT_IMP_NE) THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM REAL_NEG_GT0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL o C CONJ (ASSUME `&0 < x`)) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    POP_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_NEG_GT0] THEN DISCH_THEN(MP_TAC o CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_LT_ANTISYM];
    REWRITE_TAC[]]);;

let REAL_POS_POW2 = prove
 (`!x. &0 <= x pow 2`,
  STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM REAL_POW2_ABS] THEN
  SUBGOAL_THEN `&0 = &0 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC [REAL_POW_ZERO] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `2 = 0` THEN ARITH_TAC; REWRITE_TAC []];
    ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THEN
    ARITH_TAC]);;

let DENOM_LT_0 = prove
 (`! (x:real)(y:real)(z:real).
	((y < &0)) ==> ((x / y < z) = ( y * z < x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [] THEN
  SUBGOAL_THEN `y = --abs y` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(&0 <= y)` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_NOT_LE] THEN ONCE_ASM_REWRITE_TAC [];
      REWRITE_TAC [real_abs] THEN COND_CASES_TAC THENL
       [ASM_MESON_TAC []; SIMPLE_COMPLEX_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(abs y = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN UNDISCH_TAC `y = --abs y` THEN
    SIMP_TAC [EQ_SYM] THEN SIMP_TAC [GSYM REAL_LNEG_UNIQ] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN SIMP_TAC [REAL_LNEG_UNIQ] THEN
    SIMP_TAC [REAL_NEG_EQ] THEN SIMP_TAC [REAL_NEG_NEG] THEN POP_ASSUM MP_TAC;
    SUBGOAL_THEN `&0 < abs y` ASSUME_TAC THENL
     [UNDISCH_TAC `y = --abs y` THEN SIMP_TAC [EQ_SYM] THEN
      SIMP_TAC [GSYM REAL_LNEG_UNIQ] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
      SIMP_TAC [REAL_LNEG_UNIQ] THEN SIMP_TAC [REAL_NEG_EQ] THEN DISCH_TAC THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC;
      ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [real_div] THEN
      ONCE_REWRITE_TAC [REAL_INV_NEG] THEN
      ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL] THEN
      ONCE_REWRITE_TAC [REAL_NEG_RMUL] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      UNDISCH_TAC `&0 < abs y` THEN SIMP_TAC [GSYM REAL_LT_RDIV_EQ] THEN
      DISCH_TAC THEN ONCE_REWRITE_TAC [real_div]]] THEN
  CONV_TAC REAL_FIELD);;

let  COMPLEX_EQ_RDIV_EQ = prove
 (`!x y z. (~(z = Cx(&0)) ) ==> ( (x = y / z )<=> (x * z =  y) )`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `((x * z) = y) = ((x *z) = (y * Cx (&1)))`] THEN
    SUBGOAL_THEN `Cx (&1) = z / z` ASSUME_TAC THENL
     [REWRITE_TAC [complex_div] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      MATCH_MP_TAC COMPLEX_MUL_RINV THEN ASM_REWRITE_TAC [];
      UNDISCH_TAC `Cx (&1) = z / z` THEN SIMP_TAC [] THEN DISCH_TAC THEN
      ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN SIMPLE_COMPLEX_ARITH_TAC];
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `( (x = y / z ) =  (x * Cx (&1) = y / z))`] THEN
    SUBGOAL_THEN `Cx (&1) = z / z` ASSUME_TAC THENL
     [REWRITE_TAC [complex_div] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      MATCH_MP_TAC COMPLEX_MUL_RINV THEN ASM_REWRITE_TAC [];
      UNDISCH_TAC `Cx (&1) = z / z` THEN SIMP_TAC [] THEN DISCH_TAC THEN
      REWRITE_TAC [complex_div] THEN ONCE_REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC]]);;

let COMPLEX_EQ_LDIV_EQ = prove
 (`!x y z. (~(z = Cx(&0)) ) ==> ( (x / z = y )<=> (x = z * y) )`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `((x = z * y) =((x * Cx(&1)) = z * y) )`] THEN
    SUBGOAL_THEN `Cx (&1) = z / z` ASSUME_TAC THENL
     [REWRITE_TAC [complex_div] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      MATCH_MP_TAC COMPLEX_MUL_RINV THEN ASM_REWRITE_TAC [];
      ALL_TAC] THEN
    UNDISCH_TAC `Cx (&1) = z / z` THEN SIMP_TAC [] THEN DISCH_TAC THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    SUBGOAL_THEN `x * (z:complex) * inv z = (x * inv z)* z` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC];
      ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM complex_div] THEN
      ONCE_ASM_REWRITE_TAC []] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    REWRITE_TAC [complex_div] THEN ONCE_ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    SUBGOAL_THEN `(z * (y:complex) * inv z)=( (z * inv z )* y )` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `(z * inv z = Cx (&1))` ASSUME_TAC THENL
     [UNDISCH_TAC `~(z = Cx (&0))` THEN ONCE_REWRITE_TAC [COMPLEX_MUL_RINV];
      ONCE_ASM_REWRITE_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC]]);;

let COMPLEX_CSQRT_EQ_2 = prove
 (`!(x:complex) y. (x = y) ==> (csqrt (x) = csqrt (y))`,
  ASM_MESON_TAC []);;

let COMPLEX_EQ_CSQR_EQ = prove
 (`!(x:complex) y. (x = y) ==> ( ((x)pow 2) = ((y) pow 2) )`,
  ASM_MESON_TAC []);;

let CX_IM_0_PROD = prove
 (`!(x:complex) y.((Im y = &0) /\ (Im x = &0))
   		 ==> (Re (x * y) = Re (x)* Re (y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [complex_mul] THEN REWRITE_TAC [RE] THEN
  UNDISCH_TAC `Im x = &0` THEN SIMP_TAC [] THEN DISCH_TAC THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_POW_3 = prove
 (`!(x:real). ( (x * x * x )=((x) pow 3 ) )`,
  GEN_TAC THEN SUBGOAL_THEN `3 = 2 + 1` ASSUME_TAC 
  THENL [ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `3 = 2 + 1` THEN SIMP_TAC [] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC [REAL_POW_ADD] THEN ONCE_REWRITE_TAC [REAL_POW_2] THEN
  ONCE_REWRITE_TAC [REAL_POW_1] THEN REAL_ARITH_TAC);;

let COMPLEX_POW_3 = prove
 (`!(x:complex). ( (x * x * x )=((x) pow 3 ) )`,
  GEN_TAC THEN SUBGOAL_THEN `3 = 2 + 1` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC [COMPLEX_FIELD `3 = 2 + 1`] THEN UNDISCH_TAC `3 = 2 + 1` THEN
  SIMP_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [COMPLEX_POW_ADD] THEN
  ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN ONCE_REWRITE_TAC [COMPLEX_POW_1] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(*======================================================================*)
(*                          Quadratic Formula                           *)
(*======================================================================*)

let QUADRATIC_FORMULA = prove
 (`!a b c s. ~(Cx (&0) = Cx a) ==> 
( ((Cx a * (s pow 2 )) + (Cx b * (s)) + Cx c = Cx (&0))
 <=>  ( (s = ( ( Cx (--b) + csqrt (((Cx b) pow 2) - (Cx (&4)) * Cx a * Cx c)) / (Cx (&2) * (Cx a)) ) )\/
      (s = ( ( Cx (--b) - csqrt ( ((Cx b) pow 2) - Cx (&4) * Cx a * Cx c)) / (Cx (&2) * Cx a) ) ) ) )`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
      `(s + Cx b * inv (Cx (&2) * Cx a)) pow 2 =
      (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&4) * Cx a pow 2)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_INV] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
      SUBGOAL_THEN `inv (Cx (&2) pow 2) = inv (Cx (&4))` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN SIMPLE_COMPLEX_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `inv (Cx (&2) pow 2) = inv (Cx (&4))` THEN SIMP_TAC [] THEN
      DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      ONCE_REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_EQ_SUB_LADD] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RINV] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex) - b - (c + d) = a - b - c - d)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `( (a:complex) - b - c - a = --b + --c  )`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `( ((a:complex)*b*c)*d*e = (a*d)*(b*e)*c  )`] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
      SUBGOAL_THEN `~(Cx (&4) = Cx (&0))` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~(Cx (&4) = Cx (&0))` THEN SIMP_TAC [COMPLEX_MUL_RINV] THEN
      DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx(&1) * (a:complex) ) = (a)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `( ((a:complex)*b*c)*d = a * d * (b * c)  )`] THEN
      UNDISCH_TAC `~(Cx (&0) = Cx a)` THEN SIMP_TAC [EQ_SYM_EQ] THEN
      SIMP_TAC [COMPLEX_MUL_RINV] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `( (a:complex) * b * c * d = b * d * (a * c))`] THEN
      UNDISCH_TAC `~(Cx a = Cx (&0))` THEN SIMP_TAC [EQ_SYM_EQ] THEN
      SIMP_TAC [COMPLEX_MUL_RINV] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex) * b * (Cx (&1)) = a * b)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex) + b  = --c + --d)=
    		      			    		  (a + b + c + d = Cx (&0)))`] THEN
      SUBGOAL_THEN
        `Cx b * inv (Cx a) * s * inv (Cx (&2)) =
      s * inv (Cx a) * Cx b * inv (Cx (&2))`
        ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC
        `Cx b * inv (Cx a) * s * inv (Cx (&2)) =
      s * inv (Cx a) * Cx b * inv (Cx (&2))` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(((a:complex) + b + c + d = a + c + (b + d)))`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(( a + c + b + b) = a + c + Cx (&2)*b )`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `( (a:complex)*b*c*d = b * (c * d)* a)`] THEN
      SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `( (a:complex)*(b*c*d)*e = a * b * c * (e * d ) )`] THEN
      UNDISCH_TAC `~( Cx (&2) = Cx (&0) )` THEN SIMP_TAC [COMPLEX_MUL_RINV] THEN
      DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex) + b + c ) =(a + b + c) * (Cx (&1)) )`] THEN
      SUBGOAL_THEN `Cx a * inv (Cx a) = Cx (&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `~(Cx a = Cx (&0))` THEN SIMP_TAC [COMPLEX_MUL_RINV];
        ALL_TAC] THEN
      UNDISCH_TAC `Cx a * inv (Cx a) = Cx (&1)` THEN SIMP_TAC [EQ_SYM_EQ] THEN
      DISCH_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex) + b) * c * d) = (((a + b) * c) * d )`] THEN
      ONCE_REWRITE_TAC [GSYM complex_div] THEN
      UNDISCH_TAC `~(Cx a = Cx (&0))` THEN SIMP_TAC [COMPLEX_EQ_LDIV_EQ] THEN
      SIMP_TAC [COMPLEX_MUL_RINV] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex) * b * (Cx (&1)) = a * b)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex) * (Cx (&0)) = (Cx (&0)))`] THEN
      DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex) + b + c) * d) = (a * d + b * d + c * d )`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex) + b + c) * d) = (a * d + b * d + c * d )`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(((a:complex) * b * c)*d) = (a*(d*b)*c)`] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(((a:complex) * b) * c) = ((c*b)*a)`] THEN
      UNDISCH_TAC `~(Cx a = Cx (&0))` THEN SIMP_TAC [COMPLEX_MUL_RINV] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `(((a:complex) *b)*c) = ((b*c)*a)`] THEN
      SIMP_TAC [COMPLEX_MUL_LINV] THEN
      ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx(&1) * (a:complex) ) = (a)`] THEN
      DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex)*b + c + d*e ) = (b*a + e*d+c)`] THEN
      UNDISCH_TAC `Cx a * s pow 2 + Cx b * s + Cx c = Cx (&0)` THEN
      SIMP_TAC [];
      UNDISCH_TAC
        `(s + Cx b * inv (Cx (&2) * Cx a)) pow 2 =
      (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&4) * Cx a pow 2)` THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_SUB_0] THEN
      SUBGOAL_THEN
        `((Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&4) * Cx a pow 2) )
   		 = ((csqrt ((Cx b pow 2 - Cx (&4) * Cx a * Cx c))) * inv (Cx (&2) * Cx a)) pow 2`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN ONCE_REWRITE_TAC [CSQRT] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_INV] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
        ONCE_REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH
             `((Cx (&2) * Cx (&2))) = 
     		       	(Cx (&4))`] THEN
        SIMPLE_COMPLEX_ARITH_TAC;
        ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_DIFFSQ] THEN
      ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
      ONCE_REWRITE_TAC [COMPLEX_ENTIRE] THEN ONCE_REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN ONCE_REWRITE_TAC [CX_NEG] THEN
      DISCH_TAC THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a:complex) - (--c*b + d )) = (a + c*b - d)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(a - ( --c - d) * e) =
    		      			 ((a:complex) + c*e + d*e )`] THEN
      UNDISCH_TAC
        `(s + Cx b * inv (Cx (&2) * Cx a)) -
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) =
      Cx (&0) \/
      (s + Cx b * inv (Cx (&2) * Cx a)) +
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) =
      Cx (&0)` THEN
      SIMP_TAC [] THEN ONCE_ASM_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a + b) + c) = ((a:complex) + b + c)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a + b) - c) = ((a:complex) + b - c)`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH `((a *  b) * c) = c * ((a:complex) *  b )`] THEN
      DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
      SUBGOAL_THEN `Cx a * Cx (&2) = Cx (&2) * Cx a` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `Cx a * Cx (&2) = Cx (&2) * Cx a` THEN SIMP_TAC [] THEN
      DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_ASM_REWRITE_TAC []];
    ONCE_REWRITE_TAC [COMPLEX_ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [COMPLEX_LNEG_UNIQ] THEN
    SUBGOAL_THEN `Cx (&1) = inv (Cx a) * inv (inv (Cx a))` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ONCE_REWRITE_TAC [COMPLEX_INV_INV] THEN
      MATCH_MP_TAC COMPLEX_MUL_LINV THEN ONCE_ASM_REWRITE_TAC [] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `(Cx a * s pow 2 + Cx b * s = --Cx c) =
    		      			    (Cx a * s pow 2 + Cx b * s) * (Cx (&1)) = --Cx c`] THEN
    UNDISCH_TAC `Cx (&1) = inv (Cx a) * inv (inv (Cx a))` THEN SIMP_TAC [] THEN
    DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `(Cx a * s pow 2 + Cx b * s) * inv (Cx a) * inv (inv (Cx a)) =
      ((Cx a * s pow 2 + Cx b * s) * inv (Cx a)) / inv (Cx a)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [complex_div] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
      `(Cx a * s pow 2 + Cx b * s) * inv (Cx a) * inv (inv (Cx a)) =
      ((Cx a * s pow 2 + Cx b * s) * inv (Cx a)) / inv (Cx a)` THEN
    SIMP_TAC [] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN `~(inv (Cx a) = Cx (&0))` ASSUME_TAC THENL
     [SUBGOAL_THEN `(((inv (Cx (a))) = Cx (&0)) = (Cx (a) = Cx(&0)) )`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [COMPLEX_INV_EQ_0];
        ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        ONCE_ASM_REWRITE_TAC []] THEN
      ONCE_ASM_REWRITE_TAC [];
      ALL_TAC] THEN
    UNDISCH_TAC `~(inv (Cx a) = Cx (&0))` THEN SIMP_TAC [COMPLEX_EQ_LDIV_EQ] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `( (Cx a * s pow 2) * inv (Cx a) + (Cx b * s) * inv (Cx a) =
  inv (Cx a) * --Cx c ) = ( ((Cx a * s pow 2) * inv (Cx a) + (Cx b * s) * inv (Cx a)) + Cx (&0) =
  inv (Cx a) * --Cx c)`] THEN
    SUBGOAL_THEN
      `Cx (&0) =
      Cx b pow 2 * inv (Cx (&4) * Cx a pow 2) -
      Cx b pow 2 * inv (Cx (&4) * Cx a pow 2)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
      `Cx (&0) =
      Cx b pow 2 * inv (Cx (&4) * Cx a pow 2) -
      Cx b pow 2 * inv (Cx (&4) * Cx a pow 2)` THEN
    SIMP_TAC [] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `((((a:complex) + b) + c - d) = (a + b + c - d ))`] THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH
         `(((a:complex) + b + c - d) = ((a + b + c) - d ))`] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ONCE_REWRITE_TAC [COMPLEX_EQ_SUB_LADD] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    SUBGOAL_THEN `(Cx a * s pow 2) * inv (Cx a) = s pow 2` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `((Cx a * s pow 2) * inv (Cx a) = s pow 2) = 
     		       	((Cx a * s pow 2) * inv (Cx a) = Cx (&1) * s pow 2)`] THEN
      SUBGOAL_THEN `Cx (&1) = inv (Cx a) * Cx a` ASSUME_TAC THENL
       [UNDISCH_TAC `~(Cx (&0) = Cx a)` THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
        ONCE_REWRITE_TAC [COMPLEX_MUL_LINV];
        UNDISCH_TAC `Cx (&1) = inv (Cx a) * Cx a` THEN SIMP_TAC [] THEN
        DISCH_TAC THEN SIMPLE_COMPLEX_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(Cx a * s pow 2) * inv (Cx a) = s pow 2` THEN SIMP_TAC [] THEN
    DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `s pow 2 +
      (Cx b * s) * inv (Cx a) +
      Cx b pow 2 * inv (Cx (&4) * Cx a pow 2) =
      (s + Cx b * inv (Cx (&2) * Cx a)) pow 2`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `((((a:complex)*b)*d) = 
     		       	(d*a*b))`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex) + b + b + c) = 
     		       	(a + Cx(&2)*b + c))`] THEN
      ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(((a:complex)*b*c*d*e) = 
     		       	((a*d)*e*c*b))`] THEN
      SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~( Cx (&2) = Cx (&0) )` THEN DISCH_TAC THEN
      SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) = Cx (&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `~( Cx (&2) = Cx (&0) )` THEN
        ONCE_REWRITE_TAC [COMPLEX_MUL_RINV];
        ALL_TAC] THEN
      UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) = Cx (&1)` THEN SIMP_TAC [] THEN
      DISCH_TAC THEN ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_INV] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `((Cx (&2) * Cx (&2))) = 
     		       	(Cx (&4))`] THEN
      ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `((Cx (&1) * a * b * c)) = 
     		       	(a*b*c)`] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
      `s pow 2 +
      (Cx b * s) * inv (Cx a) +
      Cx b pow 2 * inv (Cx (&4) * Cx a pow 2) =
      (s + Cx b * inv (Cx (&2) * Cx a)) pow 2` THEN
    SIMP_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [COMPLEX_MUL_RNEG] THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `(--a + b) = 
     		       	(b + --a)`] THEN
    ONCE_REWRITE_TAC [GSYM complex_sub] THEN REPEAT STRIP_TAC THENL
     [UNDISCH_TAC
        `s =
      (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
      (Cx (&2) * Cx a)` THEN
      SIMP_TAC [CX_NEG] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      SUBGOAL_THEN
        `csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) +
      Cx b * inv (Cx (&2) * Cx a) +
      --Cx b * inv (Cx (&2) * Cx a) =
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) +
      Cx b * inv (Cx (&2) * Cx a) - Cx b * inv (Cx (&2) * Cx a)`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [complex_sub] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC
        `csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) +
      Cx b * inv (Cx (&2) * Cx a) +
      --Cx b * inv (Cx (&2) * Cx a) =
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) +
      Cx b * inv (Cx (&2) * Cx a) - Cx b * inv (Cx (&2) * Cx a)` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `(csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) +
  Cx b * inv (Cx (&2) * Cx a) - Cx b * inv (Cx (&2) * Cx a)) = (csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) +
 ( Cx b * inv (Cx (&2) * Cx a) - Cx b * inv (Cx (&2) * Cx a) ))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [complex_sub]; ALL_TAC] THEN
      ONCE_REWRITE_TAC [COMPLEX_SUB_REFL] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RID] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN ONCE_REWRITE_TAC [CSQRT] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_INV] THEN
      ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
      SUBGOAL_THEN
        `((Cx (&4) * Cx a * Cx c) * inv (Cx (&2) pow 2) * inv (Cx a pow 2) =
      (Cx (&4) * inv (Cx (&2) pow 2)) * (Cx a * inv (Cx a pow 2)) * Cx c)`
        ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC
        `((Cx (&4) * Cx a * Cx c) * inv (Cx (&2) pow 2) * inv (Cx a pow 2) =
      (Cx (&4) * inv (Cx (&2) pow 2)) * (Cx a * inv (Cx a pow 2)) * Cx c)` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
      ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
      SUBGOAL_THEN `(inv (Cx (&2)) * inv (Cx (&2)) = inv (Cx (&4)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [GSYM COMPLEX_INV_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(inv (Cx (&2)) * inv (Cx (&2)) = inv (Cx (&4)))` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(Cx (&4) = Cx (&0))` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `Cx (&4) * inv (Cx (&4)) = Cx (&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `~(Cx (&4) = Cx (&0))` THEN
        ONCE_REWRITE_TAC [COMPLEX_MUL_RINV];
        ALL_TAC] THEN
      UNDISCH_TAC `Cx (&4) * inv (Cx (&4)) = Cx (&1)` THEN SIMP_TAC [] THEN
      DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
      SUBGOAL_THEN
        `Cx a * inv (Cx a) * inv (Cx a) = (Cx a * inv (Cx a)) * inv (Cx a)`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
        SIMPLE_COMPLEX_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC
        `Cx a * inv (Cx a) * inv (Cx a) = (Cx a * inv (Cx a)) * inv (Cx a)` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN `Cx a * inv (Cx a) = Cx (&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `~(Cx (&0) = Cx a)` THEN SIMP_TAC [EQ_SYM_EQ] THEN
        DISCH_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
        UNDISCH_TAC `~(Cx a = Cx (&0))` THEN
        ONCE_REWRITE_TAC [COMPLEX_MUL_RINV];
        UNDISCH_TAC `Cx a * inv (Cx a) = Cx (&1)` THEN SIMP_TAC [] THEN
        DISCH_TAC THEN SIMPLE_COMPLEX_ARITH_TAC];
      UNDISCH_TAC
        `s =
      (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
      (Cx (&2) * Cx a)` THEN
      SIMP_TAC [CX_NEG] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
      SUBGOAL_THEN
        `Cx b * inv (Cx (&2) * Cx a) +
      --Cx b * inv (Cx (&2) * Cx a) -
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) =
      Cx (&0) -
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a)`
        ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC
          `Cx b * inv (Cx (&2) * Cx a) +
      --Cx b * inv (Cx (&2) * Cx a) -
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a) =
      Cx (&0) -
      csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c) * inv (Cx (&2) * Cx a)` THEN
        SIMP_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
        ONCE_REWRITE_TAC [complex_sub] THEN
        ONCE_REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
        ONCE_REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH `(Cx(&0) + --a) = 
     		       	(--a)`] THEN
        ONCE_REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH `(--a * Cx(&0)) = 
     		       	(Cx(&0))`] THEN
        ONCE_REWRITE_TAC [COMPLEX_NEG_MUL2] THEN
        ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN ONCE_REWRITE_TAC [CSQRT] THEN
        ONCE_REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_INV] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_MUL] THEN
        ONCE_REWRITE_TAC [COMPLEX_POW_2] THEN
        ONCE_REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH
             `((Cx (&2) * Cx (&2))) = 
     		       	(Cx (&4))`] THEN
        ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
        ONCE_REWRITE_TAC [COMPLEX_INV_MUL] THEN
        ONCE_REWRITE_TAC
          [SIMPLE_COMPLEX_ARITH
             `(((a:complex)*b*c)*d*e*f) = 
     		       	((a*d)*(b*e)*(f*c))`] THEN
        SUBGOAL_THEN `~(Cx (&4) = Cx (&0))` ASSUME_TAC THENL
         [ALL_TAC;
          UNDISCH_TAC `~(Cx (&4) = Cx (&0))` THEN SIMP_TAC [COMPLEX_MUL_RINV] THEN
          DISCH_TAC THEN UNDISCH_TAC `~(Cx (&0) = Cx a)` THEN
          SIMP_TAC [EQ_SYM_EQ] THEN SIMP_TAC [COMPLEX_MUL_RINV] THEN
          ONCE_REWRITE_TAC [GSYM COMPLEX_POW_2] THEN
          ONCE_REWRITE_TAC
            [SIMPLE_COMPLEX_ARITH
               `(Cx (&0) + ((a:complex)*b*c)-
     Cx (&1) * Cx (&1) * d *e  ) = 
     		       	(((a:complex)*b*c)-d *e )`] THEN
          DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM complex_sub]]] THEN
      SIMPLE_COMPLEX_ARITH_TAC]]);;

(*======================================================================*)
(*                        Real Roots (Case 1)                           *)
(*                      x = -b + sqrt (x)/ 2 a                          *)
(*             0 < a  /\ sqrt (b pow 2 - &4 * a * c) < b                *)
(*======================================================================*)

let QUAD_REAL_CASE1 = prove
 (`!(a:real) (b:real) (c:real). 
  ~(Cx(&0) = Cx(a)) /\
  (&0 < (b pow 2 - &4 * a * c)) /\ 
  (sqrt (b pow 2 - &4 * a * c) < b) /\ 
  (&0 < a)  ==> 
  (is_stable_phycl_intractn (\x:complex. Cx a * x pow 2 + Cx b * x + Cx c) )`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN 
  ONCE_REWRITE_TAC [is_stable_phycl_intractn] THEN
  SIMP_TAC [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `!x:complex. ((Cx a * x pow 2 + Cx b * x + Cx c = Cx (&0)) = (x =
              (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) \/
              x =
              (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC QUADRATIC_FORMULA THEN
    ONCE_ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
  EXISTS_TAC
    `(Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
          (Cx (&2) * Cx a)` THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
  REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_INV] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  ONCE_REWRITE_TAC [GSYM CX_POW] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  SUBGOAL_THEN
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))`
    ASSUME_TAC THENL
   [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
    REWRITE_TAC [REAL_LE_LT] THEN UNDISCH_TAC `&0 < b pow 2 - &4 * a * c` THEN
    SIMP_TAC [];
    ALL_TAC] THEN
  UNDISCH_TAC
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))` THEN
  SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_ADD] THEN REWRITE_TAC [RE_CX] THEN
  ONCE_REWRITE_TAC [REAL_RING `--a * c + (b:real) * c = (--a + b) * c`] THEN
  SUBGOAL_THEN `~( Cx (&0) = (Cx (&2) * Cx a))` ASSUME_TAC THENL
   [SUBGOAL_THEN `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a` ASSUME_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC []] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a)`] THEN
      REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
      SUBGOAL_THEN
        `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`
        ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC
          `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))` THEN
        SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM complex_div] THEN
        SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
         [ALL_TAC;
          UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN DISCH_TAC THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN
          SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC THENL
           [ALL_TAC;
            UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)` THEN SIMP_TAC [] THEN
            DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []]]];
      SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC [complex_div] THEN UNDISCH_TAC `(Cx (&0) = Cx a)` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]]] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    SIMP_TAC [GSYM CX_MUL] THEN SIMP_TAC [CX_INJ] THEN
    SUBGOAL_THEN `&0 < &2*a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `((&0)) = ((&0) * inv (&2 * a))`] THEN
    SUBGOAL_THEN
      `(--b + sqrt (b pow 2 - &4 * a * c)) * inv (&2 * a) < &0 * inv (&2 * a)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC
          [REAL_FIELD
             `(--b + sqrt (b pow 2 - &4 * a * c) < &0) = (sqrt (b pow 2 - &4 * a * c) < b)`] THEN
        ASM_SIMP_TAC [];
        MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC []];
      UNDISCH_TAC
        `(--b + sqrt (b pow 2 - &4 * a * c)) * inv (&2 * a) < &0 * inv (&2 * a)` THEN
      SIMP_TAC [] THEN ASM_REWRITE_TAC [NOT_IN_EMPTY]]]);;

(*======================================================================*)
(*                        Real Roots (Case 2)                           *)
(*             a < 0  /\ b < sqrt (b pow 2 - &4 * a * c)                *)
(*======================================================================*)
 
let QUAD_REAL_CASE2  = prove
 (`!(a:real) (b:real) (c:real). 
   ~(Cx(&0) = Cx a) /\  
    (&0 < (b pow 2 - &4 * a * c)) /\ 
    (b < sqrt (b pow 2 - &4 * a * c)) /\ 
    (a < &0)  ==>
    (is_stable_phycl_intractn (\x:complex. Cx a * x pow 2 + Cx b * x + Cx c) )`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN 
  ONCE_REWRITE_TAC [is_stable_phycl_intractn] THEN
  SIMP_TAC [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `!x:complex. ((Cx a * x pow 2 + Cx b * x + Cx c = Cx (&0)) = (x =
              (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) \/
              x =
              (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC QUADRATIC_FORMULA THEN ASM_SIMP_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
  EXISTS_TAC
    `(Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
          (Cx (&2) * Cx a)` THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
  REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_INV] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  ONCE_REWRITE_TAC [GSYM CX_POW] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  SUBGOAL_THEN
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))`
    ASSUME_TAC THENL
   [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
    REWRITE_TAC [REAL_LE_LT] THEN UNDISCH_TAC `&0 < b pow 2 - &4 * a * c` THEN
    SIMP_TAC [];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
  REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [GSYM CX_ADD] THEN
  REWRITE_TAC [RE_CX] THEN
  ONCE_REWRITE_TAC [REAL_RING `--a * c + (b:real) * c = (--a + b) * c`] THEN
  SUBGOAL_THEN `~( Cx (&0) = (Cx (&2) * Cx a))` ASSUME_TAC THENL
   [SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a)) = ( Cx (&0) = Cx (a) ) )`
      ASSUME_TAC THENL
     [ALL_TAC;
      POP_ASSUM MP_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
      POP_ASSUM (K ALL_TAC) THEN ONCE_ASM_REWRITE_TAC [] THEN
      ONCE_ASM_REWRITE_TAC []] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a)`] THEN
      REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
      SUBGOAL_THEN
        `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`
        ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC
          `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))` THEN
        SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM complex_div] THEN
        SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
         [ALL_TAC;
          UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN DISCH_TAC THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN
          SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC THENL
           [ALL_TAC;
            UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)` THEN SIMP_TAC [] THEN
            DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []]]];
      SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC [complex_div] THEN UNDISCH_TAC `(Cx (&0) = Cx a)` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]]] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    SUBGOAL_THEN `&2 * a < &0` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_MUL_SYM] THEN SUBGOAL_THEN `&0 < &2` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < &2` THEN SIMP_TAC [GSYM REAL_LT_RDIV_EQ] THEN
      ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `&0 / &2 = &0`] THEN DISCH_TAC THEN
      ASM_MESON_TAC [];
      UNDISCH_TAC `&2 * a < &0` THEN REWRITE_TAC [GSYM real_div] THEN
      SIMP_TAC [DENOM_LT_0] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a) * &0 = &0`] THEN
      ONCE_REWRITE_TAC [REAL_ARITH `(&0 < --(a:real) + b) = (&0 < b + --a)`] THEN
      REWRITE_TAC [GSYM REAL_LT_SUB_RADD] THEN
      ONCE_REWRITE_TAC [REAL_ARITH `(&0 - --(a:real) =  a)`] THEN
      ONCE_ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NOT_IN_EMPTY]]]);;

(*======================================================================*)
(*                        Real Roots (Case 3)                           *)
(*             0 < b/a  /\ (b pow 2 - &4 * a * c) = 0                   *)
(*======================================================================*)

let QUAD_REAL_CASE3 = prove
 (`!(a:real) (b:real) (c:real). 
 ~(Cx(&0) = Cx(a))  /\ 
  ((b pow 2 - &4 * a * c) = &0) /\
  (&0 < b / a)  ==> 
  (is_stable_phycl_intractn (\x:complex. Cx a * x pow 2 + Cx b * x + Cx c) )`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN 
  ONCE_REWRITE_TAC [is_stable_phycl_intractn] THEN
  SIMP_TAC [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `!x:complex. ((Cx a * x pow 2 + Cx b * x + Cx c = Cx (&0)) = (x =
              (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) \/
              x =
              (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC QUADRATIC_FORMULA THEN
    ONCE_ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
  EXISTS_TAC
    `(Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
          (Cx (&2) * Cx a)` THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
  REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_INV] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  ONCE_REWRITE_TAC [GSYM CX_POW] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  UNDISCH_TAC `b pow 2 - &4 * a * c = &0` THEN SIMP_TAC [] THEN
  SIMP_TAC [CSQRT_0] THEN
  ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx(&0) *(a:complex) = Cx(&0)  )`] THEN
  REWRITE_TAC [RE_CX] THEN
  ONCE_REWRITE_TAC
    [SIMPLE_COMPLEX_ARITH `(--b * (c:real)  + &0 = --b * c  )`] THEN
  SUBGOAL_THEN `--b * inv (&2 * a) < &0` ASSUME_TAC THENL
   [REWRITE_TAC [REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC
      [SIMPLE_COMPLEX_ARITH `(--b * (c:real) * d = (--b * d) * c  )`] THEN
    SUBGOAL_THEN `&0 < inv (&2)` ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < inv (&2)` THEN SIMP_TAC [GSYM REAL_LT_RDIV_EQ] THEN
    DISCH_TAC THEN
    ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&0 / (c:real) = &0  )`] THEN
    REWRITE_TAC [GSYM REAL_NEG_LMUL] THEN REWRITE_TAC [REAL_NEG_LT0] THEN
    ASM_MESON_TAC [real_div];
    REWRITE_TAC [GSYM CX_ADD] THEN REWRITE_TAC [RE_CX] THEN
    ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(--(a:real)*b + &0 = --a*b   )`] THEN
    DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NOT_IN_EMPTY]]);;

(*======================================================================*)
(*                        Real Roots (Case 4)                           *)
(*                    For x = -b - sqrt (x)/ 2 a                        *)
(*             0 < a  /\ sqrt (b pow 2 - &4 * a * c) < --b              *)
(*======================================================================*)

let QUAD_REAL_CASE4  = prove
 (`!(a:real) (b:real) (c:real). 
  ~(Cx(&0) = Cx a) /\
   (&0 < (b pow 2 - &4 * a * c)) /\ 
   (sqrt (b pow 2 - &4 * a * c) < --b ) /\ 
   (a < &0)  ==> 
(is_stable_phycl_intractn (\x:complex. Cx(a)* x pow 2 + Cx(b) * x + Cx(c)) )`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN 
  ONCE_REWRITE_TAC [is_stable_phycl_intractn] THEN
  SIMP_TAC [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `!x:complex. ((Cx a * x pow 2 + Cx b * x + Cx c = Cx (&0)) = (x =
              (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) \/
              x =
              (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC QUADRATIC_FORMULA THEN
    ONCE_ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
  EXISTS_TAC
    `(Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
          (Cx (&2) * Cx a)` THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
  REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_INV] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  ONCE_REWRITE_TAC [GSYM CX_POW] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  SUBGOAL_THEN
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))`
    ASSUME_TAC THENL
   [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
    REWRITE_TAC [REAL_LE_LT] THEN UNDISCH_TAC `&0 < b pow 2 - &4 * a * c` THEN
    SIMP_TAC [];
    ALL_TAC] THEN
  UNDISCH_TAC
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))` THEN
  SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_SUB] THEN REWRITE_TAC [RE_CX] THEN
  ONCE_REWRITE_TAC [REAL_RING `--a * c - (b:real) * c = (--a - b) * c`] THEN
  SUBGOAL_THEN `~( Cx (&0) = (Cx (&2) * Cx a))` ASSUME_TAC THENL
   [SUBGOAL_THEN `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a` ASSUME_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC []] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a)`] THEN
      REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
      SUBGOAL_THEN
        `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`
        ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC
          `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))` THEN
        SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM complex_div] THEN
        SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
         [ALL_TAC;
          UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN DISCH_TAC THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN
          SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC THENL
           [ALL_TAC;
            UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)` THEN SIMP_TAC [] THEN
            DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []]]];
      SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC [complex_div] THEN UNDISCH_TAC `(Cx (&0) = Cx a)` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]]] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    SUBGOAL_THEN `&2 * a < &0` ASSUME_TAC THENL
     [REWRITE_TAC [REAL_MUL_SYM] THEN SUBGOAL_THEN `&0 < &2` ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < &2` THEN SIMP_TAC [GSYM REAL_LT_RDIV_EQ] THEN
      ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `&0 / &2 = &0`] THEN DISCH_TAC THEN
      ASM_MESON_TAC [];
      UNDISCH_TAC `&2 * a < &0` THEN REWRITE_TAC [GSYM real_div] THEN
      ASM_SIMP_TAC [DENOM_LT_0] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a) * &0 = &0`] THEN
      ONCE_REWRITE_TAC [REAL_ARITH `(&0 < --(a:real) - b) = (b < --a )`] THEN
      REWRITE_TAC [GSYM REAL_LT_SUB_RADD] THEN
      ONCE_REWRITE_TAC [REAL_ARITH `(&0 - --(a:real) =  a)`] THEN
      ONCE_ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NOT_IN_EMPTY]]]);;

(*======================================================================*)
(*                        Real Roots (Case 5)                           *)
(*             0 < a  /\ --b < (b pow 2 - &4 * a * c)                   *)
(*======================================================================*)

let QUAD_REAL_CASE5  = prove
 (`!(a:real) (b:real) (c:real). 
  ~(Cx (&0) = Cx a) /\
   ((&0) < (b pow 2 - &4 * a * c)) /\
   (--b < sqrt (b pow 2 - &4 * a * c) ) /\
   (&0 < a)  ==> 
   (is_stable_phycl_intractn (\x:complex. Cx a * x pow 2 + Cx b * x + Cx c) )`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN 
  ONCE_REWRITE_TAC [is_stable_phycl_intractn] THEN
  SIMP_TAC [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `!x:complex. ((Cx a * x pow 2 + Cx b * x + Cx c = Cx (&0)) = (x =
              (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) \/
              x =
              (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC QUADRATIC_FORMULA THEN
    ONCE_ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
  EXISTS_TAC
    `(Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
          (Cx (&2) * Cx a)` THEN
  ASM_REWRITE_TAC [] THEN REWRITE_TAC [complex_div] THEN
  REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_INV] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_MUL] THEN REWRITE_TAC [GSYM CX_MUL] THEN
  ONCE_REWRITE_TAC [GSYM CX_POW] THEN REWRITE_TAC [GSYM CX_SUB] THEN
  SUBGOAL_THEN
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))`
    ASSUME_TAC THENL
   [REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
    REWRITE_TAC [REAL_LE_LT] THEN UNDISCH_TAC `&0 < b pow 2 - &4 * a * c` THEN
    SIMP_TAC [];
    ALL_TAC] THEN
  UNDISCH_TAC
    `csqrt (Cx (b pow 2 - &4 * a * c)) = Cx (sqrt (b pow 2 - &4 * a * c))` THEN
  SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM CX_MUL] THEN
  REWRITE_TAC [GSYM CX_SUB] THEN REWRITE_TAC [RE_CX] THEN
  ONCE_REWRITE_TAC [REAL_RING `--a * c - (b:real) * c = (--a - b) * c`] THEN
  SUBGOAL_THEN `~( Cx (&0) = (Cx (&2) * Cx a))` ASSUME_TAC THENL
   [SUBGOAL_THEN `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a` ASSUME_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a` THEN
      SIMP_TAC [] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC []] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC
        [SIMPLE_COMPLEX_ARITH
           `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a)`] THEN
      REWRITE_TAC [complex_div] THEN
      ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
      SUBGOAL_THEN
        `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`
        ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC
          `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))` THEN
        SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [GSYM complex_div] THEN
        SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
         [ALL_TAC;
          UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN DISCH_TAC THEN
          SIMP_TAC [COMPLEX_EQ_RDIV_EQ] THEN
          SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC THENL
           [ALL_TAC;
            UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)` THEN SIMP_TAC [] THEN
            DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []]]];
      SUBGOAL_THEN `~(Cx (&2) = Cx (&0))` ASSUME_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `~(Cx (&2) = Cx (&0))` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC [complex_div] THEN UNDISCH_TAC `(Cx (&0) = Cx a)` THEN
        SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]]] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    SIMP_TAC [GSYM CX_MUL] THEN SIMP_TAC [CX_INJ] THEN
    SUBGOAL_THEN `&0 < &2*a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `((&0)) = ((&0) * inv (&2 * a))`] THEN
    SUBGOAL_THEN
      `(--b - sqrt (b pow 2 - &4 * a * c)) * inv (&2 * a) < &0 * inv (&2 * a)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [REAL_FIELD `(--(x:real) - y < (&0)) = (--x < y)`];
        MATCH_MP_TAC REAL_INV_POS] THEN
      ASM_REWRITE_TAC [];
      UNDISCH_TAC
        `(--b - sqrt (b pow 2 - &4 * a * c)) * inv (&2 * a) < &0 * inv (&2 * a)` THEN
      SIMP_TAC [] THEN ASM_REWRITE_TAC [NOT_IN_EMPTY]]]);;

(*======================================================================*)
(*                         Imaginary Roots                              *)
(*                  For x = -b +/- sqrt (x)/ 2 a                        *)
(*           0 < b/a  /\ (b pow 2 - &4 * a * c) < 0                     *)
(*======================================================================*)

let QUAD_IMAG_CASE = prove
 (`!(a:real) (b:real) (c:real). 
 ~(Cx (&0) = Cx a)  /\ 
  ((b pow 2 - &4 * a * c) < &0)/\ 
  (&0 < b / a) ==> 
  (is_stable_phycl_intractn (\x:complex. Cx a * x pow 2 + Cx b * x + Cx c) )`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN 
  ONCE_REWRITE_TAC [is_stable_phycl_intractn] THEN
  SIMP_TAC [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `!x:complex. ((Cx a * x pow 2 + Cx b * x + Cx c = Cx (&0)) = (x =
              (Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) \/
              x =
              (Cx (--b) - csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
              (Cx (&2) * Cx a) ) )`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC QUADRATIC_FORMULA THEN
    ONCE_ASM_REWRITE_TAC [] THEN MESON_TAC [];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
  EXISTS_TAC
    `(Cx (--b) + csqrt (Cx b pow 2 - Cx (&4) * Cx a * Cx c)) /
          (Cx (&2) * Cx a)` THEN
  ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [GSYM CX_MUL] THEN
  ONCE_REWRITE_TAC [GSYM CX_MUL] THEN ONCE_REWRITE_TAC [GSYM CX_POW] THEN
  REWRITE_TAC [GSYM CX_SUB] THEN
  SUBGOAL_THEN `((b pow 2 - &4 *( a:real) * c) = --(&4 * a * c -  b pow 2))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [REAL_NEG_SUB] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `--(&4 * a * c - b pow 2) = -- &1 * (&4 * a * c - b pow 2)`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [GSYM REAL_NEG_MINUS1] THEN SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `--(&4 * a * c - b pow 2) = -- &1 * (&4 * a * c - b pow 2)` THEN
  SIMP_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [CX_MUL] THEN
  ONCE_REWRITE_TAC [CX_NEG] THEN ONCE_REWRITE_TAC [GSYM COMPLEX_POW_II_2] THEN
  SUBGOAL_THEN
    `Cx (&4 * a * c - b pow 2)  = (csqrt ( Cx (&4 * a * c - b pow 2) ))pow 2`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC [CSQRT] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [GSYM COMPLEX_POW_MUL] THEN
  SUBGOAL_THEN
    `csqrt ((ii * csqrt (Cx (&4 * a * c - b pow 2))) pow 2) = (ii * csqrt (Cx (&4 * a * c - b pow 2)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC POW_2_CSQRT THEN DISJ2_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
        `(ii * csqrt (Cx (&4 * a * c - b pow 2))) = ( csqrt (Cx (&4 * a * c - b pow 2)) * ii )`
        ASSUME_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
      ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [RE_MUL_II] THEN
      SUBGOAL_THEN
        `csqrt (Cx (&4 * a * c - b pow 2)) =
   		  (Cx (sqrt(&4 * a * c - b pow 2)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
        ONCE_REWRITE_TAC [REAL_LE_LT] THEN DISJ1_TAC THEN
        ONCE_REWRITE_TAC [GSYM REAL_NEG_SUB] THEN
        UNDISCH_TAC `b pow 2 - &4 * a * c < &0` THEN CONV_TAC REAL_FIELD;
        ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [IM_CX] THEN
        SIMPLE_COMPLEX_ARITH_TAC];
      SUBGOAL_THEN
        `csqrt (Cx (&4 * a * c - b pow 2)) =
   		  (Cx (sqrt(&4 * a * c - b pow 2)))`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
        ONCE_REWRITE_TAC [REAL_LE_LT] THEN DISJ1_TAC THEN
        ONCE_REWRITE_TAC [GSYM REAL_NEG_SUB];
        ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_LE_LT] THEN
        DISJ1_TAC THEN ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
        ONCE_REWRITE_TAC [IM_MUL_II] THEN ONCE_REWRITE_TAC [RE_CX] THEN
        MATCH_MP_TAC SQRT_POS_LT] THEN
      UNDISCH_TAC `b pow 2 - &4 * a * c < &0` THEN CONV_TAC REAL_FIELD];
    POP_ASSUM MP_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `csqrt (Cx (&4 * a * c - b pow 2)) =
   		  (Cx (sqrt(&4 * a * c - b pow 2)))`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC CX_SQRT THEN
      ONCE_REWRITE_TAC [REAL_LE_LT] THEN DISJ1_TAC THEN
      ONCE_REWRITE_TAC [GSYM REAL_NEG_SUB] THEN
      UNDISCH_TAC `b pow 2 - &4 * a * c < &0` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [GSYM CX_MUL] THEN ONCE_REWRITE_TAC [GSYM CX_NEG] THEN
    ONCE_REWRITE_TAC [complex_div] THEN
    ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC [GSYM CX_INV] THEN ONCE_REWRITE_TAC [GSYM CX_MUL] THEN
    ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [GSYM CX_MUL] THEN ONCE_REWRITE_TAC [ii] THEN
    ONCE_REWRITE_TAC [CX_DEF] THEN ONCE_REWRITE_TAC [complex_mul] THEN
    ONCE_REWRITE_TAC [RE] THEN ONCE_REWRITE_TAC [IM] THEN
    SUBGOAL_THEN
      `(&0 * sqrt (&4 * a * c - b pow 2) * inv (&2 * a) - &1 * &0) = &0`
      ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `(&0 * &0 + &1 * sqrt (&4 * a * c - b pow 2) * inv (&2 * a) ) 
  		     =  (sqrt (&4 * a * c - b pow 2) * inv (&2 * a))`
      ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    ONCE_ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [complex_add] THEN
    ONCE_REWRITE_TAC [RE] THEN ONCE_REWRITE_TAC [IM] THEN
    ONCE_REWRITE_TAC [RE] THEN
    ONCE_REWRITE_TAC
      [REAL_ARITH
         `(--b * inv (&2 * a) + &0 < &0) = (--b * inv (&2 * a) < &0)`] THEN
    ONCE_REWRITE_TAC [REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC [REAL_ARITH `((a:real) * b * c) = ((a*c)*b)`] THEN
    SUBGOAL_THEN `&0 < &2` ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < &2` THEN ONCE_REWRITE_TAC [GSYM real_div] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [REAL_ARITH `(&0 * &2) = (&0)`] THEN
    ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL] THEN ONCE_REWRITE_TAC [real_div] THEN
    ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC [GSYM real_div] THEN
    SUBGOAL_THEN `(--(b / a) < &0) = (&0 < b / a)` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < b / a` THEN CONV_TAC REAL_FIELD;
      ONCE_ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NOT_IN_EMPTY]]]);;

(*======================================================================*)
(*----Generalized theorem regarding stability of physical human-robot  
                  interaction having polynomial with quadratic roots----*)
(*======================================================================*)

g ` !a b c.  
  ~(Cx (&0) = Cx a) /\
   (((&0 < b / a) /\ (((b pow 2 - &4 * a * c) < &0) \/ (b pow 2 - &4 * a * c = &0))) \/
   ((&0 < b pow 2 - &4 * a * c)  /\
       ((a < &0) /\ ((b < sqrt (b pow 2 - &4 * a * c) \/ (sqrt (b pow 2 - &4 * a * c) < --b)))  \/ 
       ((&0 < a) /\ ((sqrt (b pow 2 - &4 * a * c) < b) \/ (--b < sqrt (b pow 2 - &4 * a * c)))) ) ) )
        ==> is_stable_phycl_intractn (\x. Cx a * x pow 2 + Cx b * x + Cx c)`;;

e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC QUAD_IMAG_CASE );;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC QUAD_REAL_CASE3);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC QUAD_REAL_CASE2);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC QUAD_REAL_CASE4);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC QUAD_REAL_CASE1);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC QUAD_REAL_CASE5);;
e (ASM_SIMP_TAC []);;

let QUAD_STABLE_ALL_CASES_GEN_PHRI = top_thm();;

(*==================================================================*)

g `!a b c.  ~(Cx (&0) = Cx a) /\
          (&0 < b / a /\
          (b pow 2 - &4 * a * c < &0 \/
           b pow 2 - &4 * a * c = &0) \/
          &0 < b pow 2 - &4 * a * c /\
          (&0 < a /\ (sqrt (b pow 2 - &4 * a * c) < b \/
            -- b < sqrt (b pow 2 - &4 * a * c)))) 
         ==> is_stable_phycl_intractn (\s. Cx a * s pow 2 + Cx b * s + Cx c)`;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC QUAD_STABLE_ALL_CASES_GEN_PHRI);;
e (POP_ASSUM MP_TAC THEN STRIP_TAC);;
e (ASM_SIMP_TAC [IM_CX; RE_CX; CX_INJ]);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;

let STABILITY_CONSRAINTS_GEN_PHRI = top_thm ();;


(*============================================================================*)
(*============================================================================*)
(*============================================================================*)


g `!Tc m k c.
       valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
          &0 < Tc  /\
         ~(&0 = ((m / c) * Tc)) /\
         (&0 < ((m / c) + Tc) / ((m / c) * Tc) /\
          (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1) < &0 \/ ((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1) = &0) \/
          &0 < ((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1) /\
          &0 < ((m / c) * Tc) /\
          (sqrt (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1)) < ((m / c) + Tc) \/
           --((m / c) + Tc) < sqrt (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1))))
         ==> is_stable_phycl_intractn (\s. Cx ((m / c) * Tc) * s pow 2 + Cx ((m / c) + Tc) * s + Cx (&1))`;;
	 
e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm]);;
e (SIMP_TAC [STABILITY_CONSRAINTS_GEN_PHRI; CX_INJ]);;

let STABLE_OLM_PHRI = top_thm ();;

(*---------------------------------------------------------------------------*)

g `!Tc m k c.
       valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
          &0 < Tc  /\
         (&0 < ((m / c) + Tc) / ((m / c) * Tc) /\
          (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1) < &0 \/
	   ((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1) = &0) \/
          &0 < ((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1) /\
  (sqrt (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1)) < ((m / c) + Tc) \/
  --((m / c) + Tc) < sqrt (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) * (&1))))
         ==> is_stable_phycl_intractn (\s. Cx ((m / c) * Tc) * s pow 2 + Cx ((m / c) + Tc) * s + Cx (&1))`;;

e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm]);;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (SUBGOAL_THEN `&0 < ((m / c) * Tc)` ASSUME_TAC);;
       e (SUBGOAL_THEN `&0 < (m / c)` ASSUME_TAC);;
              e (MATCH_MP_TAC REAL_LT_DIV);;
	      e (ASM_SIMP_TAC []);;

       e (REWRITE_TAC [REAL_MUL_POS_LT]);;
       e (ASM_SIMP_TAC []);;

e (MATCH_MP_TAC STABILITY_CONSRAINTS_GEN_PHRI);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [CX_INJ] THEN CONV_TAC REAL_FIELD);;

let STABLE_OLM_PHRI_ALT = top_thm ();;

(*===========================================================================*)

g `!Tc m k c.
       valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
          &0 < Tc  /\
         (&0 < ((m / c) + Tc) / ((m / c) * Tc) /\
          (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) < &0 \/
	   ((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) = &0) \/
          &0 < ((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc) /\
  (sqrt (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc)) < ((m / c) + Tc) \/
  --((m / c) + Tc) < sqrt (((m / c) + Tc) pow 2 - &4 * ((m / c) * Tc))))
         ==> is_stable_phycl_intractn (\s. Cx ((m / c) * Tc) * s pow 2 + Cx ((m / c) + Tc) * s + Cx (&1))`;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC STABLE_OLM_PHRI_ALT);;
e (EXISTS_TAC `k:real`);;
e (ASM_SIMP_TAC [REAL_FIELD `&4 * a * &1  = &4 * a`]);;

let STABLE_OLM_PHRI_FINAL = top_thm ();;

(*===========================================================================*)
(*===========================================================================*)

   (*==========================================================*)
   (*******************CUBIC POLYNOMIAL*************************)
   (************************************************************)
   (*==========================================================*)

(*-*-*-*-*-*-*-*-*-*-*-CUBIC FACTORIZATION-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-* *-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
 

g `!a b c d b1 c1 d1 r (s:complex). 
   Cx(b) = Cx(b1) + Cx(a * r) /\
   Cx(c) = Cx(c1) + Cx(b1 * r)  /\
   Cx(d) = Cx(c1 * r)  
   ==> ((Cx(a) * s pow 3 + Cx(b) * s pow 2 + Cx(c) * s  + Cx(d) = Cx(&0)) <=>
        ((s + Cx(r)) *  ((Cx(a) * (s pow 2 )) + (Cx (b1) * (s)) + Cx (c1) )  = Cx(&0)))`;;


e (REPEAT STRIP_TAC THEN ASM_SIMP_TAC []);;
e (SIMP_TAC [COMPLEX_FIELD `((a:complex) + b ) *
 (d + e + f)  = 
  	    		      (a*d + a * e + a * f +  b * d + b * e + b * f )   
			       `]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_3; COMPLEX_POW_2]);;
e (ONCE_REWRITE_TAC [COMPLEX_RING `( 
s * Cx a * s * s +
 s * Cx b1 * s +
 s * Cx c1 +
 Cx r * Cx a * s * s +
 Cx r * Cx b1 * s +
 Cx r * Cx c1
   )  = 

 ( Cx a * s * s * s +
   Cx b1 * s * s + Cx r * Cx a * s * s +
   Cx c1 * s + Cx r * Cx b1 * s +
   Cx r * Cx c1
 )   
			       `]);;
e (SIMP_TAC [COMPLEX_RING `((Cx b1 * s * s +
 Cx r * Cx a * s * s) = ((Cx b1  +
 Cx r * Cx a ) * s * s) )  /\ 
 ( (Cx c1 * s +
 Cx r * Cx b1 * s) = ((Cx c1  +
 Cx r * Cx b1) * s) )`]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

let CUBIC_FACT = top_thm ();;

(*-*-*-*-*-*-*-*-*-*-*-CUBIC ROOTS-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-* *-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
 

g `!a b c d b1 c1 d1 r s.
         ~(Cx (&0) = Cx (a)) /\ 
	 Cx b = Cx b1 + Cx (a * r) /\
         Cx c = Cx c1 + Cx (b1 * r) /\
         Cx d = Cx (c1 * r)
         ==> ( ( (Cx a * s pow 3 + Cx b * s pow 2 + Cx c * s + Cx d = Cx (&0))) 
         = ( (s = --Cx(r))  \/ (s =
 (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
 (Cx (&2) * Cx a) ) \/ (s =
 (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
 (Cx (&2) * Cx a) )) )  `;;

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `(Cx a * s pow 3 + Cx b * s pow 2 + Cx c * s + Cx d = Cx (&0) <=>
              (s + Cx r) * (Cx a * s pow 2 + Cx b1 * s + Cx c1) = Cx (&0))` ASSUME_TAC );;
e (MATCH_MP_TAC CUBIC_FACT);;
e (ASM_SIMP_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC [COMPLEX_RING `((s + Cx r) * (Cx a * s pow 2 + Cx b1 * s + Cx c1) = Cx (&0)) = ( (s + Cx r) = Cx (&0)  \/
 ((Cx a * s pow 2 + Cx b1 * s + Cx c1) =
 Cx (&0) )) `]);;
e (ASM_SIMP_TAC []);;
e (ONCE_REWRITE_TAC [COMPLEX_RING `(s + Cx r = Cx (&0)) = (s = --Cx r)`]);;



e (SUBGOAL_THEN `( Cx a * s pow 2 + Cx b1 * s + Cx c1 = Cx (&0)) = (s =
 (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
 (Cx (&2) * Cx a) \/
 s =
 (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
 (Cx (&2) * Cx a))` ASSUME_TAC);;
e (MATCH_MP_TAC QUADRATIC_FORMULA);;
e (ASM_SIMP_TAC []);;
e (ASM_REWRITE_TAC []);;


let CUBIC_ROOTS = top_thm();;


(*-*-*-*-*-*-*-*-*-*-*-CUBIC STABILITY-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-* *-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
 

g `!a b c d b1 c1 d1 r x.
         ~(Cx (&0) = Cx a) /\
         Cx b = Cx b1 + Cx (a * r) /\
         Cx c = Cx c1 + Cx (b1 * r) /\
         Cx d = Cx (c1 * r) /\
(
 (  &0 < (r:real)
 )
\/
 ((&0 < b1 / a /\
          (b1 pow 2 - &4 * a * c1 < &0 \/ b1 pow 2 - &4 * a * c1 = &0) \/
          &0 < b1 pow 2 - &4 * a * c1 /\
          (a < &0 /\
           (b1 < sqrt (b1 pow 2 - &4 * a * c1) \/
            sqrt (b1 pow 2 - &4 * a * c1) < --b1) \/
           &0 < a /\
           (sqrt (b1 pow 2 - &4 * a * c1) < b1 \/
            --b1 < sqrt (b1 pow 2 - &4 * a * c1))))
 
)
  
) ==> is_stable_phycl_intractn (\x. Cx a * x pow 3 + Cx b * x pow 2 + Cx c * x + Cx d) `;;


e (REPEAT STRIP_TAC);;

e (ASM_SIMP_TAC [is_stable_phycl_intractn]);;
e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (--Cx(r))`);;

e (ASM_REWRITE_TAC []);;
    e (ONCE_REWRITE_TAC [GSYM CX_NEG]);;
    e (ONCE_REWRITE_TAC [RE_CX]);;
e (ONCE_REWRITE_TAC [REAL_FIELD `(--r < &0) = (&0 < r)`]);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC [NOT_IN_EMPTY]);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Imaginary Case*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) < 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (ASM_SIMP_TAC [is_stable_phycl_intractn]);;
e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          ((Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
        (Cx (&2) * Cx a) )`);;

e (ASM_REWRITE_TAC []);;
  e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;


 e (SUBGOAL_THEN `((b1 pow 2 - &4 *( a:real) * c1) = --(&4 * a * c1 -  b1 pow 2)) ` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [REAL_NEG_SUB]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC ``);;
e (ONCE_ASM_REWRITE_TAC []);;
 e (SUBGOAL_THEN `(--(&4 * a * c1 - b1 pow 2)) = -- &1 * (&4 * a * c1 - b1 pow 2)` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_MINUS1]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `--(&4 * a * c1 - b1 pow 2) = -- &1 * (&4 * a * c1 - b1 pow 2)`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (ONCE_REWRITE_TAC [CX_NEG]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_II_2]);;

 e (SUBGOAL_THEN ` Cx (&4 * a * c1 - b1 pow 2)  = (csqrt ( Cx (&4 * a * c1 - b1 pow 2) ))pow 2` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [CSQRT]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;



e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [GSYM  COMPLEX_POW_MUL]);;


 e (SUBGOAL_THEN `csqrt ((ii * csqrt (Cx (&4 * a * c1 - b1 pow 2))) pow 2) = (ii * csqrt (Cx (&4 * a * c1 - b1 pow 2)))` ASSUME_TAC);;
e (MATCH_MP_TAC POW_2_CSQRT);;
e (DISJ2_TAC);;

e (CONJ_TAC);;

 e (SUBGOAL_THEN `(ii * csqrt (Cx (&4 * a * c1 - b1 pow 2))) = ( csqrt (Cx (&4 * a * c1 - b1 pow 2)) * ii )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_MUL_II]);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a * c1 - b1 pow 2)) = Cx (sqrt (&4 * a * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [IM_CX]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a * c1 - b1 pow 2)) = Cx (sqrt (&4 * a * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a * c1 - b1 pow 2)) = Cx (sqrt (&4 * a * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [IM]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (UNDISCH_TAC `Cx (&4 * a * c1 - b1 pow 2) = csqrt (Cx (&4 * a * c1 - b1 pow 2)) pow 2`);;

e (SIMP_TAC [CX_SQRT]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a * c1 - b1 pow 2)) = Cx (sqrt (&4 * a * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISCH_TAC);;
e (DISJ1_TAC);;
e (MATCH_MP_TAC SQRT_POS_LT);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt ((ii * csqrt (Cx (&4 * a * c1 - b1 pow 2))) pow 2) =
      ii * csqrt (Cx (&4 * a * c1 - b1 pow 2))`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a * c1 - b1 pow 2)) =
   		  (Cx (sqrt(&4 * a * c1 - b1 pow 2))) ` ASSUME_TAC);;


e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (&4 * a * c1 - b1 pow 2)) = Cx (sqrt (&4 * a * c1 - b1 pow 2))`);;

e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_NEG]);;

e (ONCE_REWRITE_TAC [complex_div]);;
e (ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB]);;
e (ONCE_REWRITE_TAC [GSYM CX_INV]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;



e (ONCE_REWRITE_TAC [ii]);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [complex_mul]);;

e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;

 e (SUBGOAL_THEN `(&0 * sqrt (&4 * a * c1 - b1 pow 2) * inv (&2 * a) - &1 * &0) = &0` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (SUBGOAL_THEN `(&0 * &0 + &1 * sqrt (&4 * a * c1 - b1 pow 2) * inv (&2 * a) ) 
  		     =  (sqrt (&4 * a * c1 - b1 pow 2) * inv (&2 * a))` ASSUME_TAC);;

e (REAL_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [complex_add]);;
e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;
e (ONCE_REWRITE_TAC [RE]);;

e (ONCE_REWRITE_TAC[REAL_ARITH `(--b1 * inv (&2 * a) + &0 < &0) = (--b1 * inv (&2 * a) < &0)`] );;

e (ONCE_REWRITE_TAC [REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC[REAL_ARITH `((a:real) * b * c) = ((a*c)*b)`] );;

 e (SUBGOAL_THEN `&0 < &2` ASSUME_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `&0 < &2`);;

e (ONCE_REWRITE_TAC [GSYM real_div]);;

e (SIMP_TAC [REAL_LT_LDIV_EQ]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC[REAL_ARITH `(&0 * &2) = (&0)`] );;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_REWRITE_TAC [GSYM real_div]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC []);;
e (ASM_MESON_TAC [NOT_IN_EMPTY]);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) = 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
 
     e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
          (Cx (&2) * Cx a)`);;

e (ASM_REWRITE_TAC []);;

e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;

e (UNDISCH_TAC `b1 pow 2 - &4 * a * c1 = &0`);;
e (SIMP_TAC []);;

e (SIMP_TAC [CSQRT_0]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (Cx(&0) *(a:complex) = Cx(&0)  )`]);;

e (REWRITE_TAC[RE_CX]);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real)  + &0 = --b * c  )`]);;


 e (SUBGOAL_THEN `--b1 * inv (&2 * a) < &0` ASSUME_TAC);;


e (REWRITE_TAC[REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real) * d = (--b * d) * c  )`]);;

 e (SUBGOAL_THEN `&0 < inv (&2 )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;


e (UNDISCH_TAC `&0 < inv (&2)`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;

e (DISCH_TAC);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (&0 / (c:real) = &0  )`]);;
e (REWRITE_TAC[GSYM REAL_NEG_LMUL]);;

e (REWRITE_TAC[REAL_NEG_LT0]);;
e (ASM_MESON_TAC [real_div]);;
e (REWRITE_TAC[GSYM CX_ADD]);;

e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--(a:real)*b + &0 = --a*b   )`]);;
e (DISCH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 2-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) = 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
          (Cx (&2) * Cx a)`);;


e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a)) = ( Cx (&0) = Cx (a) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a = ( Cx (&2) * Cx (a)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

 e (SUBGOAL_THEN `(&2 * a) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) + b) = (&0 < b + --a) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 4-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ (b pow 2 - &4 * a * c) < --b **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;
e (DISCH_TAC);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;

e (EXISTS_TAC `
          (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
          (Cx (&2) * Cx a)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a)) = ( Cx (&0) = Cx (a) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a = ( Cx (&2) * Cx (a)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (ASM_SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) - b) = (b < --a ) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 1-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ --b < (b pow 2 - &4 * a * c) **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
          (Cx (&2) * Cx a)`);;


e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a)) = ( Cx (&0) = Cx (a) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a = ( Cx (&2) * Cx (a)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a)) 
     		       `]);;


e (SUBGOAL_THEN `(--b1 + sqrt (b1 pow 2 - &4 * a * c1)) * inv (&2 * a) < &0 * inv (&2 * a) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
e (ONCE_REWRITE_TAC [REAL_ARITH `(--(b:real) + c < &0) = (c < b) `]);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b1 + sqrt (b1 pow 2 - &4 * a * c1)) * inv (&2 * a) < &0 * inv (&2 * a)`);;
e (SIMP_TAC []);;


    (*--------- e (REWRITE_TAC [REAL_LT_ADD_SUB]);;-------------*)
   (*---------  e (REWRITE_TAC [REAL_SUB_LZERO]);;-------------*)
    (*--------- e (REWRITE_TAC [REAL_LT_NEG]);;-------------*)
(*---------e (ONCE_REWRITE_TAC[REAL_RING ` ((&0 - (b:real))) = ( - b)`] );;-------------*)
(*---------e (ASM_REWRITE_TAC []);;-------------*)
(*---------e (DISCH_TAC);;-------------*)
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 5-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ --b < (b pow 2 - &4 * a * c) **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!(x:complex). ( (Cx a * x pow 3 +
       (Cx b) * x pow 2 +
       (Cx c) * x +
       Cx (d) =
       Cx (&0)) <=>
             ( (x = --Cx r) \/
              (x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) )  \/
              ( x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
              (Cx (&2) * Cx a) ) ) ) ` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC CUBIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a * Cx c1)) /
          (Cx (&2) * Cx a)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a * c1)) = Cx (sqrt (b1 pow 2 - &4 * a * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a)) = ( Cx (&0) = Cx (a) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a = ( Cx (&2) * Cx (a)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a = (Cx (&2) * Cx a) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a <=> Cx (&0) = Cx a`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a)) 
     		       `]);;


e (SUBGOAL_THEN `(--b1 - sqrt (b1 pow 2 - &4 * a * c1)) * inv (&2 * a) < &0 * inv (&2 * a) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
r(1);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b1 - sqrt (b1 pow 2 - &4 * a * c1)) * inv (&2 * a) < &0 * inv (&2 * a)`);;
e (SIMP_TAC []);;
e (ONCE_REWRITE_TAC[REAL_RING ` ((( --(b:real) - c)) < ( &0)) = (c < --b)`] );;
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
e (ONCE_REWRITE_TAC [REAL_FIELD `(--(x:real) - y < (&0)) = (--x < y)`]);;
e (ASM_REWRITE_TAC []);;

let CUBIC_ALL_STABLE_CASES = top_thm();;

(*===========================================================================*)
(*===========================================================================*)

g `!b0 b1 b2 b3 b11 b21 r.
         ~(Cx (&0) = Cx b3) /\
         Cx b2 = Cx b21 + Cx (b3 * r) /\
         Cx b1 = Cx b11 + Cx (b21 * r) /\
         Cx b0 = Cx (b11 * r) /\
         (&0 < r \/
          &0 < b21 / b3 /\
          (b21 pow 2 - &4 * b3 * b11 < &0 \/ b21 pow 2 - &4 * b3 * b11 = &0) \/
          &0 < b21 pow 2 - &4 * b3 * b11 /\
          (b3 < &0 /\
           (b21 < sqrt (b21 pow 2 - &4 * b3 * b11) \/
            sqrt (b21 pow 2 - &4 * b3 * b11) < --b21) \/
           &0 < b3 /\
           (sqrt (b21 pow 2 - &4 * b3 * b11) < b21 \/
            --b21 < sqrt (b21 pow 2 - &4 * b3 * b11))))
         ==> is_stable_phycl_intractn
             (\x. Cx b3 * x pow 3 + Cx b2 * x pow 2 + Cx b1 * x + Cx b0)`;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC CUBIC_ALL_STABLE_CASES);;
e (EXISTS_TAC `b21:real`);;
e (EXISTS_TAC `b11:real`);;
e (EXISTS_TAC `r:real`);;
e (ASM_SIMP_TAC []);;

let CUBIC_ALL_STABLE_CASES_ALT = top_thm();;

(*===========================================================================*)

g `!b0 b1 b2 b3 b11 b21 r.
         (&0 < b3) /\
         Cx b2 = Cx b21 + Cx (b3 * r) /\
         Cx b1 = Cx b11 + Cx (b21 * r) /\
         Cx b0 = Cx (b11 * r) /\
         (&0 < r \/
          &0 < b21 / b3 /\
          (b21 pow 2 - &4 * b3 * b11 < &0 \/ b21 pow 2 - &4 * b3 * b11 = &0) \/
          &0 < b21 pow 2 - &4 * b3 * b11 /\
          (&0 < b3 /\
           (sqrt (b21 pow 2 - &4 * b3 * b11) < b21 \/
            --b21 < sqrt (b21 pow 2 - &4 * b3 * b11))))
         ==> is_stable_phycl_intractn
             (\x. Cx b3 * x pow 3 + Cx b2 * x pow 2 + Cx b1 * x + Cx b0)`;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC CUBIC_ALL_STABLE_CASES_ALT);;
e (EXISTS_TAC `b11:real`);;
e (EXISTS_TAC `b21:real`);;
e (EXISTS_TAC `r:real`);;
e (ASM_SIMP_TAC [CX_INJ]);;
e (SUBGOAL_THEN `~(&0 = b3)` ASSUME_TAC);;
      e (POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

e (ASM_SIMP_TAC [GSYM CX_INJ]);;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM MP_TAC);;
e (STRIP_TAC);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;

let CUBIC_ALL_STABLE_CASES_FINAL = top_thm();;

(*===========================================================================*)
(*===========================================================================*)

g `!b0 b1 b2 b3 b11 b21 r.
         (&0 < (m * Tc)) /\
         Cx (c * Tc + m) = Cx b21 + Cx ((m * Tc) * r) /\
         Cx c = Cx b11 + Cx (b21 * r) /\
         Cx KH = Cx (b11 * r) /\
         (&0 < r \/
          &0 < b21 / (m * Tc) /\
          (b21 pow 2 - &4 * (m * Tc) * b11 < &0 \/ b21 pow 2 - &4 * (m * Tc) * b11 = &0) \/
          &0 < b21 pow 2 - &4 * (m * Tc) * b11 /\
          (&0 < (m * Tc) /\
           (sqrt (b21 pow 2 - &4 * (m * Tc) * b11) < b21 \/
            --b21 < sqrt (b21 pow 2 - &4 * (m * Tc) * b11))))
         ==> is_stable_phycl_intractn
             (\x. Cx (m * Tc) * x pow 3 + Cx (c * Tc + m) * x pow 2 + Cx c * x + Cx KH)`;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC CUBIC_ALL_STABLE_CASES_FINAL);;
e (EXISTS_TAC `b11:real`);;
e (EXISTS_TAC `b21:real`);;
e (EXISTS_TAC `r:real`);;
e (ASM_SIMP_TAC []);;


let CUBIC_STABLE_CLM_PHRI = top_thm();;

(*===========================================================================*)

g `!b0 b1 b2 b3 b11 b21 r m c k Tc KH.
       valid_phycl_intractn_parmtrs_fm ((m,c,k):phy_inter_par) /\
         (&0 < Tc) /\
         Cx (c * Tc + m) = Cx b21 + Cx ((m * Tc) * r) /\
         Cx c = Cx b11 + Cx (b21 * r) /\
         Cx KH = Cx (b11 * r) /\
         (&0 < r \/
          &0 < b21 / (m * Tc) /\
          (b21 pow 2 - &4 * (m * Tc) * b11 < &0 \/ b21 pow 2 - &4 * (m * Tc) * b11 = &0) \/
          &0 < b21 pow 2 - &4 * (m * Tc) * b11 /\
          (&0 < (m * Tc) /\
           (sqrt (b21 pow 2 - &4 * (m * Tc) * b11) < b21 \/
            --b21 < sqrt (b21 pow 2 - &4 * (m * Tc) * b11))))
         ==> is_stable_phycl_intractn
             (\x. Cx (m * Tc) * x pow 3 + Cx (c * Tc + m) * x pow 2 + Cx c * x + Cx KH)`;;

e (REWRITE_TAC [valid_phycl_intractn_parmtrs_fm]);;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC CUBIC_STABLE_CLM_PHRI);;
e (EXISTS_TAC `b11:real`);;
e (EXISTS_TAC `b21:real`);;
e (EXISTS_TAC `r:real`);;
e (ASM_SIMP_TAC [REAL_MUL_POS_LT]);;


let STABLE_CLM_PHRI_FINAL = top_thm();;


(*===========================================================================*)
(*===========================================================================*)


   (*==========================================================*)
   (*******************QUARTIC POLYNOMIAL***********************)
   (************************************************************)
   (*==========================================================*)


g `!a1 b1 c1 a2 b2 c2 (s:complex). (Cx(a:real) = Cx(a1 * a2))  /\
   	       Cx(b) = Cx(a1 * b2) + Cx(a2 * b1) /\
    	       	     Cx(c) = Cx(a1 * c2) + Cx(b1 * b2) +Cx( a2 * c1) /\
    	 	     	    Cx(d) = Cx(b1 * c2) + Cx(b2 * c1) /\
			    	  Cx(e) = Cx(c1 * c2) 
   ==> ((Cx(a) * s pow 4 + Cx(b) * s pow 3 + Cx(c) * s pow 2 + Cx(d) * s + Cx(e) = Cx(&0)) <=>
        (((Cx(a1) * (s pow 2 )) + (Cx (b1) * (s)) + Cx (c1) ) * ((Cx(a2) * (s pow 2 )) + (Cx (b2) * (s)) + Cx (c2)) = Cx(&0)))`;;

e (REPEAT STRIP_TAC THEN ASM_SIMP_TAC []);;
e (SIMP_TAC [COMPLEX_FIELD `((a:complex) + b + c) *
 (d + e + f)  = 
  	    		      (a*d + a * e + a * f + b * d + b * e + b * f + c * d + c * e + c * f)   
			       `]);;
e (ONCE_REWRITE_TAC [COMPLEX_RING `( (Cx a1 * s pow 2) * Cx a2 * s pow 2 +
 (Cx a1 * s pow 2) * Cx b2 * s +
 (Cx a1 * s pow 2) * Cx c2 +
 (Cx b1 * s) * Cx a2 * s pow 2 +
 (Cx b1 * s) * Cx b2 * s +
 (Cx b1 * s) * Cx c2 +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s +
 Cx c1 * Cx c2 )  = 
  	    		      (Cx a1 * Cx a2 * s pow 2  * s pow 2 +
 Cx a1  * Cx b2 * s pow 2 * s +
 Cx a1  * Cx c2 * s pow 2 +
 Cx b1  * Cx a2 * s * s pow 2 +
 Cx b1 * Cx b2 * s * s +
 Cx b1  * Cx c2 * s +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s +
 Cx c1 * Cx c2
 )   
			       `]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_ADD]);;
e (ONCE_REWRITE_TAC [COMPLEX_RING `(Cx a1 * Cx a2 * s pow (2 + 2) +
 Cx a1 * Cx b2 * s pow 2 * s +
 Cx a1 * Cx c2 * s pow 2 +
 Cx b1 * Cx a2 * s * s pow 2 +
 Cx b1 * Cx b2 * s * s +
 Cx b1 * Cx c2 * s +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s +
 Cx c1 * Cx c2) = (Cx a1 * Cx a2 * s pow (2 + 2) +
 Cx a1 * Cx b2 * s pow 2 * s pow 1 +
 Cx a1 * Cx c2 * s pow 2 +
 Cx b1 * Cx a2 * s pow 1 * s pow 2 +
 Cx b1 * Cx b2 * s pow 1 * s pow 1 +
 Cx b1 * Cx c2 * s pow 1 +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s pow 1+
 Cx c1 * Cx c2)` ]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_ADD]);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (SIMP_TAC [ARITH]);;
e (SIMP_TAC [COMPLEX_RING `(Cx a1 * Cx a2 * s pow 4 +
 Cx a1 * Cx b2 * s pow 3 +
 Cx a1 * Cx c2 * s pow 2 +
 Cx b1 * Cx a2 * s pow 3 +
 Cx b1 * Cx b2 * s pow 2 +
 Cx b1 * Cx c2 * s pow 1 +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s pow 1 +
 Cx c1 * Cx c2  ) = (Cx a1 * Cx a2 * s pow 4 +
 (Cx a1 * Cx b2 + Cx b1 * Cx a2) * s pow 3 +
  (Cx a1 * Cx c2 + Cx b1 * Cx b2 + Cx c1 * Cx a2) * s pow 2 +
   (Cx b1 * Cx c2 + Cx c1 * Cx b2 ) * s + 
     Cx c1 * Cx c2)` ]);;


e (ONCE_REWRITE_TAC [COMPLEX_POW_1]);;

e (CONV_TAC COMPLEX_FIELD);;

let QUARTIC_FACT = top_thm();;


(*===============================================================================*)


g `!a1 a2 b1 b2 c1 c2 s.
         ~(Cx (&0) = Cx (a)) /\ ~(Cx (&0) = Cx (a1)) /\ ~(Cx (&0) = Cx (a2)) /\Cx a = Cx (a1 * a2) /\
         Cx b = Cx (a1 * b2) + Cx (a2 * b1) /\
         Cx c = Cx (a1 * c2) + Cx (b1 * b2) + Cx (a2 * c1) /\
         Cx d = Cx (b1 * c2) + Cx (b2 * c1) /\
         Cx e = Cx (c1 * c2)
         ==> (Cx a * s pow 4 +
              Cx b * s pow 3 +
              Cx c * s pow 2 +
              Cx d * s +
              Cx e =
              Cx (&0)) = (( (s = ( ( Cx (--b1) + csqrt ( ((Cx (b1)) pow 2) - (Cx (&4))*(Cx (a1))*(Cx (c1))  )  )/ ((Cx (&2))* (Cx (a1))) ) )\/
      (s = ( ( Cx (--b1) - csqrt ( ((Cx (b1)) pow 2) - (Cx (&4))*(Cx (a1))*(Cx (c1))  )  )/ ((Cx (&2))* (Cx (a1))) ) ) \/ 
(s = ( ( Cx (--b2) + csqrt ( ((Cx (b2)) pow 2) - (Cx (&4))*(Cx (a2))*(Cx (c2))  )  )/ ((Cx (&2))* (Cx (a2))) ) )\/
      (s = ( ( Cx (--b2) - csqrt ( ((Cx (b2)) pow 2) - (Cx (&4))*(Cx (a2))*(Cx (c2))  )  )/ ((Cx (&2))* (Cx (a2))) ) )) ) `;;


e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `(Cx a * s pow 4 + Cx b * s pow 3 + Cx c * s pow 2 + Cx d * s + Cx e = Cx (&0)) = ((Cx a1 * s pow 2 + Cx b1 * s + Cx c1) *
              (Cx a2 * s pow 2 + Cx b2 * s + Cx c2) =
              Cx (&0))` ASSUME_TAC );;
e (MATCH_MP_TAC QUARTIC_FACT);;
e (ASM_SIMP_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC [COMPLEX_RING `((Cx a1 * s pow 2 + Cx b1 * s + Cx c1) *
 (Cx a2 * s pow 2 + Cx b2 * s + Cx c2) =
 Cx (&0)) = ((Cx a1 * s pow 2 + Cx b1 * s + Cx c1) = Cx(&0) \/
 ((Cx a2 * s pow 2 + Cx b2 * s + Cx c2) =
 Cx (&0) )) `]);;
e (ASM_SIMP_TAC []);;




e (SUBGOAL_THEN `((Cx a1 * s pow 2 + Cx b1 * s + Cx c1)  =
 Cx (&0)) = (s =
 (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
 (Cx (&2) * Cx a1) \/
 s =
 (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
 (Cx (&2) * Cx a1))` ASSUME_TAC);;
e (MATCH_MP_TAC QUADRATIC_FORMULA);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;

e (SUBGOAL_THEN `((Cx a2 * s pow 2 + Cx b2 * s + Cx c2)  =
 Cx (&0)) = (s =
 (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
 (Cx (&2) * Cx a2) \/
 s =
 (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
 (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (MATCH_MP_TAC QUADRATIC_FORMULA);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;
e (MESON_TAC []);;

let QUARITC_ROOTS = top_thm();;

(*=================================================================*)
(*-*-*-*-*-*-*-*-*-*-*-QUARTIC STABILITY-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-* *-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


g `!a1 a2 b1 b2 c1 c2 (x:complex).
         ~(Cx (&0) = Cx a) /\
         ~(Cx (&0) = Cx a1) /\
         ~(Cx (&0) = Cx a2) /\
         Cx a = Cx (a1 * a2) /\
         Cx b = Cx (a1 * b2) + Cx (a2 * b1) /\
         Cx c = Cx (a1 * c2) + Cx (b1 * b2) + Cx (a2 * c1) /\
         Cx d = Cx (b1 * c2) + Cx (b2 * c1) /\
         Cx e = Cx (c1 * c2) /\
(
(
((&0 < b1 / a1 /\
          (b1 pow 2 - &4 * a1 * c1 < &0 \/ b1 pow 2 - &4 * a1 * c1 = &0) \/
          &0 < b1 pow 2 - &4 * a1 * c1 /\
          (a1 < &0 /\
           (b1 < sqrt (b1 pow 2 - &4 * a1 * c1) \/
            sqrt (b1 pow 2 - &4 * a1 * c1) < --b1) \/
           &0 < a1 /\
           (sqrt (b1 pow 2 - &4 * a1 * c1) < b1 \/
            --b1 < sqrt (b1 pow 2 - &4 * a1 * c1))))
 
)  
) \/

((&0 < b2 / a2 /\
          (b2 pow 2 - &4 * a2 * c2 < &0 \/ b2 pow 2 - &4 * a2 * c2 = &0) \/
          &0 < b2 pow 2 - &4 * a2 * c2 /\
          (a2 < &0 /\
           (b2 < sqrt (b2 pow 2 - &4 * a2 * c2) \/
            sqrt (b2 pow 2 - &4 * a2 * c2) < --b2) \/
           &0 < a2 /\
           (sqrt (b2 pow 2 - &4 * a2 * c2) < b2 \/
            --b2 < sqrt (b2 pow 2 - &4 * a2 * c2))))
  )
  
) ==> is_stable_phycl_intractn (\x. Cx a * x pow 4 + Cx b * x pow 3 + Cx c * x pow 2 + Cx d * x + Cx e) `;;

e (REPEAT STRIP_TAC);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Imaginary Case*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) < 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (SIMP_TAC [is_stable_phycl_intractn]);;
e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;


e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;


 e (SUBGOAL_THEN `((b1 pow 2 - &4 *( a1:real) * c1) = --(&4 * a1 * c1 -  b1 pow 2)) ` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [REAL_NEG_SUB]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC ``);;
e (ONCE_ASM_REWRITE_TAC []);;
 e (SUBGOAL_THEN `(--(&4 * a1 * c1 - b1 pow 2)) = -- &1 * (&4 * a1 * c1 - b1 pow 2)` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_MINUS1]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `--(&4 * a1 * c1 - b1 pow 2) = -- &1 * (&4 * a1 * c1 - b1 pow 2)`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (ONCE_REWRITE_TAC [CX_NEG]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_II_2]);;

 e (SUBGOAL_THEN ` Cx (&4 * a1 * c1 - b1 pow 2)  = (csqrt ( Cx (&4 * a1 * c1 - b1 pow 2) ))pow 2` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [CSQRT]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;



e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [GSYM  COMPLEX_POW_MUL]);;


 e (SUBGOAL_THEN `csqrt ((ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))) pow 2) = (ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2)))` ASSUME_TAC);;
e (MATCH_MP_TAC POW_2_CSQRT);;
e (DISJ2_TAC);;

e (CONJ_TAC);;

 e (SUBGOAL_THEN `(ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))) = ( csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) * ii )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_MUL_II]);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [IM_CX]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [IM]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (UNDISCH_TAC `Cx (&4 * a1 * c1 - b1 pow 2) = csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) pow 2`);;

e (SIMP_TAC [CX_SQRT]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISCH_TAC);;
e (DISJ1_TAC);;
e (MATCH_MP_TAC SQRT_POS_LT);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt ((ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))) pow 2) =
      ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) =
   		  (Cx (sqrt(&4 * a1 * c1 - b1 pow 2))) ` ASSUME_TAC);;


e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2))`);;

e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_NEG]);;

e (ONCE_REWRITE_TAC [complex_div]);;
e (ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB]);;
e (ONCE_REWRITE_TAC [GSYM CX_INV]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;



e (ONCE_REWRITE_TAC [ii]);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [complex_mul]);;

e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;

 e (SUBGOAL_THEN `(&0 * sqrt (&4 * a1 * c1 - b1 pow 2) * inv (&2 * a1) - &1 * &0) = &0` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (SUBGOAL_THEN `(&0 * &0 + &1 * sqrt (&4 * a1 * c1 - b1 pow 2) * inv (&2 * a1) ) 
  		     =  (sqrt (&4 * a1 * c1 - b1 pow 2) * inv (&2 * a1))` ASSUME_TAC);;

e (REAL_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [complex_add]);;
e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;
e (ONCE_REWRITE_TAC [RE]);;

e (ONCE_REWRITE_TAC[REAL_ARITH `(--b1 * inv (&2 * a1) + &0 < &0) = (--b1 * inv (&2 * a1) < &0)`] );;

e (ONCE_REWRITE_TAC [REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC[REAL_ARITH `((a:real) * b * c) = ((a*c)*b)`] );;

 e (SUBGOAL_THEN `&0 < &2` ASSUME_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `&0 < &2`);;

e (ONCE_REWRITE_TAC [GSYM real_div]);;

e (SIMP_TAC [REAL_LT_LDIV_EQ]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC[REAL_ARITH `(&0 * &2) = (&0)`] );;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_REWRITE_TAC [GSYM real_div]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC []);;
e (ASM_MESON_TAC [NOT_IN_EMPTY]);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) = 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

 e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;

e (UNDISCH_TAC `b1 pow 2 - &4 * a1 * c1 = &0`);;
e (SIMP_TAC []);;

e (SIMP_TAC [CSQRT_0]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (Cx(&0) *(a:complex) = Cx(&0)  )`]);;

e (REWRITE_TAC[RE_CX]);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real)  + &0 = --b * c  )`]);;


 e (SUBGOAL_THEN `--b1 * inv (&2 * a1) < &0` ASSUME_TAC);;


e (REWRITE_TAC[REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real) * d = (--b * d) * c  )`]);;

 e (SUBGOAL_THEN `&0 < inv (&2 )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;


e (UNDISCH_TAC `&0 < inv (&2)`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;

e (DISCH_TAC);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (&0 / (c:real) = &0  )`]);;
e (REWRITE_TAC[GSYM REAL_NEG_LMUL]);;

e (REWRITE_TAC[REAL_NEG_LT0]);;
e (ASM_MESON_TAC [real_div]);;
e (REWRITE_TAC[GSYM CX_ADD]);;

e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--(a:real)*b + &0 = --a*b   )`]);;
e (DISCH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) = 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;



e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a1) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a1 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a1) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) + b) = (&0 < b + --a) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 4-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ sqrt (b pow 2 - &4 * a * c) < --b **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a1) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a1 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (ASM_SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a1) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) - b) = (b < --a ) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 1-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ sqrt (b pow 2 - &4 * a * c) < b-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a1 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a1)) 
     		       `]);;


e (SUBGOAL_THEN `(--b1 + sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
e (ONCE_REWRITE_TAC [REAL_ARITH `(--(b:real) + c < &0) = (c < b) `]);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b1 + sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1)`);;
e (SIMP_TAC []);;


    (*--------- e (REWRITE_TAC [REAL_LT_ADD_SUB]);;-------------*)
   (*---------  e (REWRITE_TAC [REAL_SUB_LZERO]);;-------------*)
    (*--------- e (REWRITE_TAC [REAL_LT_NEG]);;-------------*)
(*---------e (ONCE_REWRITE_TAC[REAL_RING ` ((&0 - (b:real))) = ( - b)`] );;-------------*)
(*---------e (ASM_REWRITE_TAC []);;-------------*)
(*---------e (DISCH_TAC);;-------------*)
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 5-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ --b < (b pow 2 - &4 * a * c) **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a1 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a1)) 
     		       `]);;


e (SUBGOAL_THEN `(--b1 - sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
r(1);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b1 - sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1)`);;
e (SIMP_TAC []);;
e (ONCE_REWRITE_TAC[REAL_RING ` ((( --(b:real) - c)) < ( &0)) = (c < --b)`] );;
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
e (ONCE_REWRITE_TAC [REAL_FIELD `(--(x:real) - y < (&0)) = (--x < y)`]);;
e (ASM_REWRITE_TAC []);;
(**************second quadratic*******************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-Imaginary Case*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) < 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
e (ASM_SIMP_TAC [is_stable_phycl_intractn]);;
e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;


e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;


 e (SUBGOAL_THEN `((b2 pow 2 - &4 *( a2:real) * c2) = --(&4 * a2 * c2 -  b2 pow 2)) ` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [REAL_NEG_SUB]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC ``);;
e (ONCE_ASM_REWRITE_TAC []);;
 e (SUBGOAL_THEN `(--(&4 * a2 * c2 - b2 pow 2)) = -- &1 * (&4 * a2 * c2 - b2 pow 2)` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_MINUS1]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `--(&4 * a2 * c2 - b2 pow 2) = -- &1 * (&4 * a2 * c2 - b2 pow 2)`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (ONCE_REWRITE_TAC [CX_NEG]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_II_2]);;

 e (SUBGOAL_THEN ` Cx (&4 * a2 * c2 - b2 pow 2)  = (csqrt ( Cx (&4 * a2 * c2 - b2 pow 2) ))pow 2` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [CSQRT]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;



e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [GSYM  COMPLEX_POW_MUL]);;


 e (SUBGOAL_THEN `csqrt ((ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))) pow 2) = (ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2)))` ASSUME_TAC);;
e (MATCH_MP_TAC POW_2_CSQRT);;
e (DISJ2_TAC);;

e (CONJ_TAC);;

 e (SUBGOAL_THEN `(ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))) = ( csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) * ii )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_MUL_II]);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [IM_CX]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [IM]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (UNDISCH_TAC `Cx (&4 * a2 * c2 - b2 pow 2) = csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) pow 2`);;

e (SIMP_TAC [CX_SQRT]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISCH_TAC);;
e (DISJ1_TAC);;
e (MATCH_MP_TAC SQRT_POS_LT);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt ((ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))) pow 2) =
      ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) =
   		  (Cx (sqrt(&4 * a2 * c2 - b2 pow 2))) ` ASSUME_TAC);;


e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2))`);;

e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_NEG]);;

e (ONCE_REWRITE_TAC [complex_div]);;
e (ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB]);;
e (ONCE_REWRITE_TAC [GSYM CX_INV]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;



e (ONCE_REWRITE_TAC [ii]);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [complex_mul]);;

e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;

 e (SUBGOAL_THEN `(&0 * sqrt (&4 * a2 * c2 - b2 pow 2) * inv (&2 * a2) - &1 * &0) = &0` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (SUBGOAL_THEN `(&0 * &0 + &1 * sqrt (&4 * a2 * c2 - b2 pow 2) * inv (&2 * a2) ) 
  		     =  (sqrt (&4 * a2 * c2 - b2 pow 2) * inv (&2 * a2))` ASSUME_TAC);;

e (REAL_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [complex_add]);;
e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;
e (ONCE_REWRITE_TAC [RE]);;

e (ONCE_REWRITE_TAC[REAL_ARITH `(--b2 * inv (&2 * a2) + &0 < &0) = (--b2 * inv (&2 * a2) < &0)`] );;

e (ONCE_REWRITE_TAC [REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC[REAL_ARITH `((a:real) * b * c) = ((a*c)*b)`] );;

 e (SUBGOAL_THEN `&0 < &2` ASSUME_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `&0 < &2`);;

e (ONCE_REWRITE_TAC [GSYM real_div]);;

e (SIMP_TAC [REAL_LT_LDIV_EQ]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC[REAL_ARITH `(&0 * &2) = (&0)`] );;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_REWRITE_TAC [GSYM real_div]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC []);;
e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(*****************************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-real case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-* b pow 2 - &4 * a * c = &0 /\ &0 < b / a**-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;

e (UNDISCH_TAC `b2 pow 2 - &4 * a2 * c2 = &0`);;
e (SIMP_TAC []);;

e (SIMP_TAC [CSQRT_0]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (Cx(&0) *(a:complex) = Cx(&0)  )`]);;

e (REWRITE_TAC[RE_CX]);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real)  + &0 = --b * c  )`]);;


 e (SUBGOAL_THEN `--b2 * inv (&2 * a2) < &0` ASSUME_TAC);;


e (REWRITE_TAC[REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real) * d = (--b * d) * c  )`]);;

 e (SUBGOAL_THEN `&0 < inv (&2 )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;


e (UNDISCH_TAC `&0 < inv (&2)`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;

e (DISCH_TAC);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (&0 / (c:real) = &0  )`]);;
e (REWRITE_TAC[GSYM REAL_NEG_LMUL]);;

e (REWRITE_TAC[REAL_NEG_LT0]);;
e (ASM_MESON_TAC [real_div]);;
e (REWRITE_TAC[GSYM CX_ADD]);;

e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--(a:real)*b + &0 = --a*b   )`]);;
e (DISCH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(**********************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-real case 2-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-a < &0 b < sqrt (b pow 2 - &4 * a * c) /\**-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
 e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;



e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a2) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a2 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a2) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) + b) = (&0 < b + --a) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
r(1);;
(***********************************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-real case 1-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-0 < a  sqrt (b pow 2 - &4 * a * c) < b**-*-*-*-*-*-*-*-**-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a2 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a2)) 
     		       `]);;


e (SUBGOAL_THEN `(--b2 + sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
e (ONCE_REWRITE_TAC [REAL_ARITH `(--(b:real) + c < &0) = (c < b) `]);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b2 + sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2)`);;
e (SIMP_TAC []);;


    (*--------- e (REWRITE_TAC [REAL_LT_ADD_SUB]);;-------------*)
   (*---------  e (REWRITE_TAC [REAL_SUB_LZERO]);;-------------*)
    (*--------- e (REWRITE_TAC [REAL_LT_NEG]);;-------------*)
(*---------e (ONCE_REWRITE_TAC[REAL_RING ` ((&0 - (b:real))) = ( - b)`] );;-------------*)
(*---------e (ASM_REWRITE_TAC []);;-------------*)
(*---------e (DISCH_TAC);;-------------*)
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
(********************real case 5*****************************)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a2 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a2)) 
     		       `]);;


e (SUBGOAL_THEN `(--b2 - sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
r(1);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b2 - sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2)`);;
e (SIMP_TAC []);;
e (ONCE_REWRITE_TAC[REAL_RING ` ((( --(b:real) - c)) < ( &0)) = (c < --b)`] );;
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
e (ONCE_REWRITE_TAC [REAL_FIELD `(--(x:real) - y < (&0)) = (--x < y)`]);;
e (ASM_REWRITE_TAC []);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 4-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ sqrt (b pow 2 - &4 * a * c) < --b **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e =
              Cx (&0) <=>
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUARITC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a2) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a2 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (ASM_SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a2) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) - b) = (b < --a ) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
e (ASM_SIMP_TAC [REAL_FIELD `(--b2 - sqrt (b2 pow 2 - &4 * a2 * c2) < &0) = (--b2 < sqrt (b2 pow 2 - &4 * a2 * c2))`]);;

let QUARTIC_STABLE = top_thm();;


(*===========================================================================*)
(*===========================================================================*)


g `!a0 a1 a2 a21 a22 a3 a31 a32 a4 a41 a42 (s:complex).
         ~(Cx (&0) = Cx a4) /\
         ~(Cx (&0) = Cx a41) /\
         ~(Cx (&0) = Cx a42) /\
         Cx a4 = Cx (a41 * a42) /\
         Cx a3 = Cx (a41 * a32) + Cx (a42 * a31) /\
         Cx a2 = Cx (a41 * a22) + Cx (a31 * a32) + Cx (a42 * a21) /\
         Cx a1 = Cx (a31 * a22) + Cx (a32 * a21) /\
         Cx a0 = Cx (a21 * a22) /\
(
(
((&0 < a31 / a41 /\
          (a31 pow 2 - &4 * a41 * a21 < &0 \/ a31 pow 2 - &4 * a41 * a21 = &0) \/
          &0 < a31 pow 2 - &4 * a41 * a21 /\
          (a41 < &0 /\
           (a31 < sqrt (a31 pow 2 - &4 * a41 * a21) \/
            sqrt (a31 pow 2 - &4 * a41 * a21) < --a31) \/
           &0 < a41 /\
           (sqrt (a31 pow 2 - &4 * a41 * a21) < a31 \/
            --a31 < sqrt (a31 pow 2 - &4 * a41 * a21))))
 
)  
) \/

((&0 < a32 / a42 /\
          (a32 pow 2 - &4 * a42 * a22 < &0 \/ a32 pow 2 - &4 * a42 * a22 = &0) \/
          &0 < a32 pow 2 - &4 * a42 * a22 /\
          (a42 < &0 /\
           (a32 < sqrt (a32 pow 2 - &4 * a42 * a22) \/
            sqrt (a32 pow 2 - &4 * a42 * a22) < --a32) \/
           &0 < a42 /\
           (sqrt (a32 pow 2 - &4 * a42 * a22) < a32 \/
            --a32 < sqrt (a32 pow 2 - &4 * a42 * a22))))
  )
  
) ==> is_stable_phycl_intractn (\s. Cx a4 * s pow 4 + Cx a3 * s pow 3 + Cx a2 * s pow 2 + Cx a1 * s + Cx a0) `;;

e (MESON_TAC [QUARTIC_STABLE]);;

let QUARTIC_STABLE_IOLM = top_thm ();;


(*===========================================================================*)

(*===============================QUINTIC ROOT================================*)


g `!a b c d e m cp a1 b1 c1 a2 b2 c2 (s:complex). 
          (Cx a = Cx(a1 * a2))  /\
   	   Cx b = Cx(a1 * b2) + Cx(a2 * b1) /\
    	   Cx c = Cx(a1 * c2) + Cx(b1 * b2) + Cx( a2 * c1) /\
    	   Cx d = Cx(b1 * c2) + Cx(b2 * c1) /\
	   Cx e = Cx(c1 * c2) 
   ==> (((Cx m * s + Cx cp) * (Cx a * s pow 4 + Cx b * s pow 3 + Cx c * s pow 2 + Cx d * s + Cx e) = Cx (&0)) <=>
        ((Cx m * s + Cx cp) * ((Cx (a1) * (s pow 2 )) + (Cx (b1) * (s)) + Cx (c1) ) * ((Cx(a2) * (s pow 2 )) + (Cx (b2) * (s)) + Cx (c2)) = Cx(&0)))`;;


e (REPEAT STRIP_TAC THEN ASM_SIMP_TAC []);;
e (SIMP_TAC [COMPLEX_FIELD `((a:complex) + b + c) *
 (d + e + f)  = 
  	    		      (a*d + a * e + a * f + b * d + b * e + b * f + c * d + c * e + c * f)   
			       `]);;
e (ONCE_REWRITE_TAC [COMPLEX_RING `( (Cx a1 * s pow 2) * Cx a2 * s pow 2 +
 (Cx a1 * s pow 2) * Cx b2 * s +
 (Cx a1 * s pow 2) * Cx c2 +
 (Cx b1 * s) * Cx a2 * s pow 2 +
 (Cx b1 * s) * Cx b2 * s +
 (Cx b1 * s) * Cx c2 +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s +
 Cx c1 * Cx c2 )  = 
  	    		      (Cx a1 * Cx a2 * s pow 2  * s pow 2 +
 Cx a1  * Cx b2 * s pow 2 * s +
 Cx a1  * Cx c2 * s pow 2 +
 Cx b1  * Cx a2 * s * s pow 2 +
 Cx b1 * Cx b2 * s * s +
 Cx b1  * Cx c2 * s +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s +
 Cx c1 * Cx c2
 )   
			       `]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_ADD]);;
e (ONCE_REWRITE_TAC [COMPLEX_RING `(Cx a1 * Cx a2 * s pow (2 + 2) +
 Cx a1 * Cx b2 * s pow 2 * s +
 Cx a1 * Cx c2 * s pow 2 +
 Cx b1 * Cx a2 * s * s pow 2 +
 Cx b1 * Cx b2 * s * s +
 Cx b1 * Cx c2 * s +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s +
 Cx c1 * Cx c2) = (Cx a1 * Cx a2 * s pow (2 + 2) +
 Cx a1 * Cx b2 * s pow 2 * s pow 1 +
 Cx a1 * Cx c2 * s pow 2 +
 Cx b1 * Cx a2 * s pow 1 * s pow 2 +
 Cx b1 * Cx b2 * s pow 1 * s pow 1 +
 Cx b1 * Cx c2 * s pow 1 +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s pow 1+
 Cx c1 * Cx c2)` ]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_ADD]);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (SIMP_TAC [ARITH]);;
e (SIMP_TAC [COMPLEX_RING `(Cx a1 * Cx a2 * s pow 4 +
 Cx a1 * Cx b2 * s pow 3 +
 Cx a1 * Cx c2 * s pow 2 +
 Cx b1 * Cx a2 * s pow 3 +
 Cx b1 * Cx b2 * s pow 2 +
 Cx b1 * Cx c2 * s pow 1 +
 Cx c1 * Cx a2 * s pow 2 +
 Cx c1 * Cx b2 * s pow 1 +
 Cx c1 * Cx c2  ) = (Cx a1 * Cx a2 * s pow 4 +
 (Cx a1 * Cx b2 + Cx b1 * Cx a2) * s pow 3 +
  (Cx a1 * Cx c2 + Cx b1 * Cx b2 + Cx c1 * Cx a2) * s pow 2 +
   (Cx b1 * Cx c2 + Cx c1 * Cx b2 ) * s + 
     Cx c1 * Cx c2)` ]);;


e (ONCE_REWRITE_TAC [COMPLEX_POW_1]);;

e (CONV_TAC COMPLEX_FIELD);;

let QUINTIC_FACT = top_thm ();;


(*===========================================================================*)
(*===========================================================================*)
(*===========================================================================*)


g `!a1 a2 b1 b2 c1 c2 m a b c d e cp s. ~(Cx (&0) = Cx (m)) /\
         ~(Cx (&0) = Cx (a)) /\ ~(Cx (&0) = Cx (a1)) /\ ~(Cx (&0) = Cx (a2)) /\Cx a = Cx (a1 * a2) /\
         Cx b = Cx (a1 * b2) + Cx (a2 * b1) /\
         Cx c = Cx (a1 * c2) + Cx (b1 * b2) + Cx (a2 * c1) /\
         Cx d = Cx (b1 * c2) + Cx (b2 * c1) /\
         Cx e = Cx (c1 * c2)
         ==> ((Cx m * s + Cx cp) * (Cx a * s pow 4 +
              Cx b * s pow 3 +
              Cx c * s pow 2 +
              Cx d * s +
              Cx e) =
              Cx (&0)) = ((s = -- Cx cp / Cx m) \/ ( (s = ( ( Cx (--b1) + csqrt ( ((Cx (b1)) pow 2) - (Cx (&4))*(Cx (a1))*(Cx (c1))  )  )/ ((Cx (&2))* (Cx (a1))) ) )\/
      (s = ( ( Cx (--b1) - csqrt ( ((Cx (b1)) pow 2) - (Cx (&4))*(Cx (a1))*(Cx (c1))  )  )/ ((Cx (&2))* (Cx (a1))) ) ) \/ 
(s = ( ( Cx (--b2) + csqrt ( ((Cx (b2)) pow 2) - (Cx (&4))*(Cx (a2))*(Cx (c2))  )  )/ ((Cx (&2))* (Cx (a2))) ) )\/
      (s = ( ( Cx (--b2) - csqrt ( ((Cx (b2)) pow 2) - (Cx (&4))*(Cx (a2))*(Cx (c2))  )  )/ ((Cx (&2))* (Cx (a2))) ) )) ) `;;


e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `((Cx m * s + Cx cp) * (Cx a * s pow 4 + Cx b * s pow 3 + Cx c * s pow 2 + Cx d * s + Cx e) = Cx (&0)) = ((Cx m * s + Cx cp) * (Cx a1 * s pow 2 + Cx b1 * s + Cx c1) *
              (Cx a2 * s pow 2 + Cx b2 * s + Cx c2) =
              Cx (&0))` ASSUME_TAC );;
e (MATCH_MP_TAC QUINTIC_FACT);;
e (ASM_SIMP_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC [COMPLEX_RING `((Cx m * s + Cx cp) *
 (Cx a1 * s pow 2 + Cx b1 * s + Cx c1) *
 (Cx a2 * s pow 2 + Cx b2 * s + Cx c2) =
 Cx (&0)) = ((Cx m * s + Cx cp) = Cx (&0) \/
         (Cx a1 * s pow 2 + Cx b1 * s + Cx c1) = Cx (&0) \/
	   (Cx a2 * s pow 2 + Cx b2 * s + Cx c2) = Cx (&0)) `]);;
e (ASM_SIMP_TAC []);;

e (SUBGOAL_THEN `((Cx m * s + Cx cp) = Cx (&0)) = (s = --(Cx cp) / Cx m)` ASSUME_TAC);;

e (UNDISCH_TAC `~(Cx (&0) = Cx m)`);;
e (CONV_TAC COMPLEX_FIELD);;
e (ASM_SIMP_TAC []);;



e (SUBGOAL_THEN `((Cx a1 * s pow 2 + Cx b1 * s + Cx c1)  =
 Cx (&0)) = (s =
 (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
 (Cx (&2) * Cx a1) \/
 s =
 (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
 (Cx (&2) * Cx a1))` ASSUME_TAC);;
e (MATCH_MP_TAC QUADRATIC_FORMULA);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;

e (SUBGOAL_THEN `((Cx a2 * s pow 2 + Cx b2 * s + Cx c2)  =
 Cx (&0)) = (s =
 (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
 (Cx (&2) * Cx a2) \/
 s =
 (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
 (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (MATCH_MP_TAC QUADRATIC_FORMULA);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;


e (MESON_TAC []);;

let QUINTIC_ROOTS = top_thm();;


(*===========================================================================*)
(*===========================================================================*)


(*=================================================================*)
(*-*-*-*-*-*-*-*-*-*-*-QUINTIC STABILITY-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-* *-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


g `!a b c d e m cp a1 a2 b1 b2 c1 c2 (x:complex).
         ~(Cx (&0) = Cx m) /\
         ~(Cx (&0) = Cx a) /\
         ~(Cx (&0) = Cx a1) /\
         ~(Cx (&0) = Cx a2) /\
         Cx a = Cx (a1 * a2) /\
         Cx b = Cx (a1 * b2) + Cx (a2 * b1) /\
         Cx c = Cx (a1 * c2) + Cx (b1 * b2) + Cx (a2 * c1) /\
         Cx d = Cx (b1 * c2) + Cx (b2 * c1) /\
         Cx e = Cx (c1 * c2) /\
(
(
((&0 < b1 / a1 /\
          (b1 pow 2 - &4 * a1 * c1 < &0 \/ b1 pow 2 - &4 * a1 * c1 = &0) \/
          &0 < b1 pow 2 - &4 * a1 * c1 /\
          (a1 < &0 /\
           (b1 < sqrt (b1 pow 2 - &4 * a1 * c1) \/
            sqrt (b1 pow 2 - &4 * a1 * c1) < --b1) \/
           &0 < a1 /\
           (sqrt (b1 pow 2 - &4 * a1 * c1) < b1 \/
            --b1 < sqrt (b1 pow 2 - &4 * a1 * c1))))
 
)  
) \/

((&0 < b2 / a2 /\
          (b2 pow 2 - &4 * a2 * c2 < &0 \/ b2 pow 2 - &4 * a2 * c2 = &0) \/
          &0 < b2 pow 2 - &4 * a2 * c2 /\
          (a2 < &0 /\
           (b2 < sqrt (b2 pow 2 - &4 * a2 * c2) \/
            sqrt (b2 pow 2 - &4 * a2 * c2) < --b2) \/
           &0 < a2 /\
           (sqrt (b2 pow 2 - &4 * a2 * c2) < b2 \/
            --b2 < sqrt (b2 pow 2 - &4 * a2 * c2))))
  )
  
) ==> is_stable_phycl_intractn (\x. (Cx m * x + Cx cp) * (Cx a * x pow 4 + Cx b * x pow 3 + Cx c * x pow 2 + Cx d * x + Cx e)) `;;

e (REPEAT STRIP_TAC);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Imaginary Case*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) < 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (SIMP_TAC [is_stable_phycl_intractn]);;
e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
	      x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;


e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;


 e (SUBGOAL_THEN `((b1 pow 2 - &4 *( a1:real) * c1) = --(&4 * a1 * c1 -  b1 pow 2)) ` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [REAL_NEG_SUB]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC ``);;
e (ONCE_ASM_REWRITE_TAC []);;
 e (SUBGOAL_THEN `(--(&4 * a1 * c1 - b1 pow 2)) = -- &1 * (&4 * a1 * c1 - b1 pow 2)` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_MINUS1]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `--(&4 * a1 * c1 - b1 pow 2) = -- &1 * (&4 * a1 * c1 - b1 pow 2)`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (ONCE_REWRITE_TAC [CX_NEG]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_II_2]);;

 e (SUBGOAL_THEN ` Cx (&4 * a1 * c1 - b1 pow 2)  = (csqrt ( Cx (&4 * a1 * c1 - b1 pow 2) ))pow 2` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [CSQRT]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;



e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [GSYM  COMPLEX_POW_MUL]);;


 e (SUBGOAL_THEN `csqrt ((ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))) pow 2) = (ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2)))` ASSUME_TAC);;
e (MATCH_MP_TAC POW_2_CSQRT);;
e (DISJ2_TAC);;

e (CONJ_TAC);;

 e (SUBGOAL_THEN `(ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))) = ( csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) * ii )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_MUL_II]);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [IM_CX]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [IM]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (UNDISCH_TAC `Cx (&4 * a1 * c1 - b1 pow 2) = csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) pow 2`);;

e (SIMP_TAC [CX_SQRT]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISCH_TAC);;
e (DISJ1_TAC);;
e (MATCH_MP_TAC SQRT_POS_LT);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt ((ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))) pow 2) =
      ii * csqrt (Cx (&4 * a1 * c1 - b1 pow 2))`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) =
   		  (Cx (sqrt(&4 * a1 * c1 - b1 pow 2))) ` ASSUME_TAC);;


e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (&4 * a1 * c1 - b1 pow 2)) = Cx (sqrt (&4 * a1 * c1 - b1 pow 2))`);;

e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_NEG]);;

e (ONCE_REWRITE_TAC [complex_div]);;
e (ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB]);;
e (ONCE_REWRITE_TAC [GSYM CX_INV]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;



e (ONCE_REWRITE_TAC [ii]);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [complex_mul]);;

e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;

 e (SUBGOAL_THEN `(&0 * sqrt (&4 * a1 * c1 - b1 pow 2) * inv (&2 * a1) - &1 * &0) = &0` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (SUBGOAL_THEN `(&0 * &0 + &1 * sqrt (&4 * a1 * c1 - b1 pow 2) * inv (&2 * a1) ) 
  		     =  (sqrt (&4 * a1 * c1 - b1 pow 2) * inv (&2 * a1))` ASSUME_TAC);;

e (REAL_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [complex_add]);;
e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;
e (ONCE_REWRITE_TAC [RE]);;

e (ONCE_REWRITE_TAC[REAL_ARITH `(--b1 * inv (&2 * a1) + &0 < &0) = (--b1 * inv (&2 * a1) < &0)`] );;

e (ONCE_REWRITE_TAC [REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC[REAL_ARITH `((a:real) * b * c) = ((a*c)*b)`] );;

 e (SUBGOAL_THEN `&0 < &2` ASSUME_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `&0 < &2`);;

e (ONCE_REWRITE_TAC [GSYM real_div]);;

e (SIMP_TAC [REAL_LT_LDIV_EQ]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC[REAL_ARITH `(&0 * &2) = (&0)`] );;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_REWRITE_TAC [GSYM real_div]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC []);;
e (ASM_MESON_TAC [NOT_IN_EMPTY]);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) = 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

 e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;

e (UNDISCH_TAC `b1 pow 2 - &4 * a1 * c1 = &0`);;
e (SIMP_TAC []);;

e (SIMP_TAC [CSQRT_0]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (Cx(&0) *(a:complex) = Cx(&0)  )`]);;

e (REWRITE_TAC[RE_CX]);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real)  + &0 = --b * c  )`]);;


 e (SUBGOAL_THEN `--b1 * inv (&2 * a1) < &0` ASSUME_TAC);;


e (REWRITE_TAC[REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real) * d = (--b * d) * c  )`]);;

 e (SUBGOAL_THEN `&0 < inv (&2 )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;


e (UNDISCH_TAC `&0 < inv (&2)`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;

e (DISCH_TAC);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (&0 / (c:real) = &0  )`]);;
e (REWRITE_TAC[GSYM REAL_NEG_LMUL]);;

e (REWRITE_TAC[REAL_NEG_LT0]);;
e (ASM_MESON_TAC [real_div]);;
e (REWRITE_TAC[GSYM CX_ADD]);;

e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--(a:real)*b + &0 = --a*b   )`]);;
e (DISCH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) = 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;



e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a1) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a1 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a1) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) + b) = (&0 < b + --a) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 4-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ sqrt (b pow 2 - &4 * a * c) < --b **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a1) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a1 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (ASM_SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a1) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) - b) = (b < --a ) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;

(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 1-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ sqrt (b pow 2 - &4 * a * c) < b-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a1 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a1)) 
     		       `]);;


e (SUBGOAL_THEN `(--b1 + sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
e (ONCE_REWRITE_TAC [REAL_ARITH `(--(b:real) + c < &0) = (c < b) `]);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b1 + sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1)`);;
e (SIMP_TAC []);;


    (*--------- e (REWRITE_TAC [REAL_LT_ADD_SUB]);;-------------*)
   (*---------  e (REWRITE_TAC [REAL_SUB_LZERO]);;-------------*)
    (*--------- e (REWRITE_TAC [REAL_LT_NEG]);;-------------*)
(*---------e (ONCE_REWRITE_TAC[REAL_RING ` ((&0 - (b:real))) = ( - b)`] );;-------------*)
(*---------e (ASM_REWRITE_TAC []);;-------------*)
(*---------e (DISCH_TAC);;-------------*)
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 5-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ --b < (b pow 2 - &4 * a * c) **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
          (Cx (&2) * Cx a1)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b1 pow 2 - &4 * a1 * c1`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b1 pow 2 - &4 * a1 * c1)) = Cx (sqrt (b1 pow 2 - &4 * a1 * c1))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a1)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a1)) = ( Cx (&0) = Cx (a1) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a1 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a1) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a1 = ( Cx (&2) * Cx (a1)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a1 = (Cx (&2) * Cx a1) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a1)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a1 <=> Cx (&0) = Cx a1`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a1 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a1)) 
     		       `]);;


e (SUBGOAL_THEN `(--b1 - sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
r(1);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b1 - sqrt (b1 pow 2 - &4 * a1 * c1)) * inv (&2 * a1) < &0 * inv (&2 * a1)`);;
e (SIMP_TAC []);;
e (ONCE_REWRITE_TAC[REAL_RING ` ((( --(b:real) - c)) < ( &0)) = (c < --b)`] );;
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
e (ONCE_REWRITE_TAC [REAL_FIELD `(--(x:real) - y < (&0)) = (--x < y)`]);;
e (ASM_REWRITE_TAC []);;
(**************second quadratic*******************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-Imaginary Case*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < b/a  /\ (b pow 2 - &4 * a * c) < 0 **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
e (ASM_SIMP_TAC [is_stable_phycl_intractn]);;
e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;


e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
    e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;


 e (SUBGOAL_THEN `((b2 pow 2 - &4 *( a2:real) * c2) = --(&4 * a2 * c2 -  b2 pow 2)) ` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [REAL_NEG_SUB]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC ``);;
e (ONCE_ASM_REWRITE_TAC []);;
 e (SUBGOAL_THEN `(--(&4 * a2 * c2 - b2 pow 2)) = -- &1 * (&4 * a2 * c2 - b2 pow 2)` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_MINUS1]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `--(&4 * a2 * c2 - b2 pow 2) = -- &1 * (&4 * a2 * c2 - b2 pow 2)`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [CX_MUL]);;
e (ONCE_REWRITE_TAC [CX_NEG]);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_POW_II_2]);;

 e (SUBGOAL_THEN ` Cx (&4 * a2 * c2 - b2 pow 2)  = (csqrt ( Cx (&4 * a2 * c2 - b2 pow 2) ))pow 2` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [CSQRT]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;



e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [GSYM  COMPLEX_POW_MUL]);;


 e (SUBGOAL_THEN `csqrt ((ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))) pow 2) = (ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2)))` ASSUME_TAC);;
e (MATCH_MP_TAC POW_2_CSQRT);;
e (DISJ2_TAC);;

e (CONJ_TAC);;

 e (SUBGOAL_THEN `(ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))) = ( csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) * ii )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_MUL_II]);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [IM_CX]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [IM]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (ONCE_REWRITE_TAC [IM_MUL_II]);;
e (UNDISCH_TAC `Cx (&4 * a2 * c2 - b2 pow 2) = csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) pow 2`);;

e (SIMP_TAC [CX_SQRT]);;
e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2) )` ASSUME_TAC);;
e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [RE_CX]);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISCH_TAC);;
e (DISJ1_TAC);;
e (MATCH_MP_TAC SQRT_POS_LT);;

e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;

e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt ((ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))) pow 2) =
      ii * csqrt (Cx (&4 * a2 * c2 - b2 pow 2))`);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
 e (SUBGOAL_THEN `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) =
   		  (Cx (sqrt(&4 * a2 * c2 - b2 pow 2))) ` ASSUME_TAC);;


e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (ONCE_REWRITE_TAC [REAL_LE_LT]);;
e (DISJ1_TAC);;
e (ONCE_REWRITE_TAC [GSYM  REAL_NEG_SUB]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (&4 * a2 * c2 - b2 pow 2)) = Cx (sqrt (&4 * a2 * c2 - b2 pow 2))`);;

e (SIMP_TAC []);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_NEG]);;

e (ONCE_REWRITE_TAC [complex_div]);;
e (ONCE_REWRITE_TAC [COMPLEX_ADD_RDISTRIB]);;
e (ONCE_REWRITE_TAC [GSYM CX_INV]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;

e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;
e (ONCE_REWRITE_TAC [GSYM CX_MUL]);;



e (ONCE_REWRITE_TAC [ii]);;
e (ONCE_REWRITE_TAC [CX_DEF]);;
e (ONCE_REWRITE_TAC [complex_mul]);;

e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;

 e (SUBGOAL_THEN `(&0 * sqrt (&4 * a2 * c2 - b2 pow 2) * inv (&2 * a2) - &1 * &0) = &0` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (SUBGOAL_THEN `(&0 * &0 + &1 * sqrt (&4 * a2 * c2 - b2 pow 2) * inv (&2 * a2) ) 
  		     =  (sqrt (&4 * a2 * c2 - b2 pow 2) * inv (&2 * a2))` ASSUME_TAC);;

e (REAL_ARITH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC [complex_add]);;
e (ONCE_REWRITE_TAC [RE]);;
e (ONCE_REWRITE_TAC [IM]);;
e (ONCE_REWRITE_TAC [RE]);;

e (ONCE_REWRITE_TAC[REAL_ARITH `(--b2 * inv (&2 * a2) + &0 < &0) = (--b2 * inv (&2 * a2) < &0)`] );;

e (ONCE_REWRITE_TAC [REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC[REAL_ARITH `((a:real) * b * c) = ((a*c)*b)`] );;

 e (SUBGOAL_THEN `&0 < &2` ASSUME_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (UNDISCH_TAC `&0 < &2`);;

e (ONCE_REWRITE_TAC [GSYM real_div]);;

e (SIMP_TAC [REAL_LT_LDIV_EQ]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC[REAL_ARITH `(&0 * &2) = (&0)`] );;
e (ONCE_REWRITE_TAC [GSYM REAL_NEG_LMUL]);;
e (ONCE_REWRITE_TAC[REAL_RING `&0 = --(&0)`] );;

e (ONCE_REWRITE_TAC [REAL_LT_NEG]);;
e (ONCE_REWRITE_TAC [GSYM real_div]);;
e (ONCE_ASM_REWRITE_TAC []);;
e (ONCE_REWRITE_TAC []);;
e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(*****************************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-real case 3-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-* b pow 2 - &4 * a * c = &0 /\ &0 < b / a**-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)

e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;

e (UNDISCH_TAC `b2 pow 2 - &4 * a2 * c2 = &0`);;
e (SIMP_TAC []);;

e (SIMP_TAC [CSQRT_0]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (Cx(&0) *(a:complex) = Cx(&0)  )`]);;

e (REWRITE_TAC[RE_CX]);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real)  + &0 = --b * c  )`]);;


 e (SUBGOAL_THEN `--b2 * inv (&2 * a2) < &0` ASSUME_TAC);;


e (REWRITE_TAC[REAL_INV_MUL]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--b * (c:real) * d = (--b * d) * c  )`]);;

 e (SUBGOAL_THEN `&0 < inv (&2 )` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;


e (UNDISCH_TAC `&0 < inv (&2)`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;

e (DISCH_TAC);;

e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (&0 / (c:real) = &0  )`]);;
e (REWRITE_TAC[GSYM REAL_NEG_LMUL]);;

e (REWRITE_TAC[REAL_NEG_LT0]);;
e (ASM_MESON_TAC [real_div]);;
e (REWRITE_TAC[GSYM CX_ADD]);;

e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` (--(a:real)*b + &0 = --a*b   )`]);;
e (DISCH_TAC);;

e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
(**********************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-real case 2-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-a < &0 b < sqrt (b pow 2 - &4 * a * c) /\**-*-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
 e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ((Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;



e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a2) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a2 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a2) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) + b) = (&0 < b + --a) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
r(1);;
(***********************************************)

(*-*-*-*-*-*-*-*-*-*-*-*-*-real case 1-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-0 < a  sqrt (b pow 2 - &4 * a * c) < b**-*-*-*-*-*-*-*-**-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_ADD]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c + (b:real) * c = (--a + b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a2 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a2)) 
     		       `]);;


e (SUBGOAL_THEN `(--b2 + sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
e (ONCE_REWRITE_TAC [REAL_ARITH `(--(b:real) + c < &0) = (c < b) `]);;
e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b2 + sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2)`);;
e (SIMP_TAC []);;


    (*--------- e (REWRITE_TAC [REAL_LT_ADD_SUB]);;-------------*)
   (*---------  e (REWRITE_TAC [REAL_SUB_LZERO]);;-------------*)
    (*--------- e (REWRITE_TAC [REAL_LT_NEG]);;-------------*)
(*---------e (ONCE_REWRITE_TAC[REAL_RING ` ((&0 - (b:real))) = ( - b)`] );;-------------*)
(*---------e (ASM_REWRITE_TAC []);;-------------*)
(*---------e (DISCH_TAC);;-------------*)
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
(********************real case 5*****************************)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(up)--------------*)


e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)
e (SIMP_TAC [GSYM CX_MUL]);;
e (SIMP_TAC [CX_INJ]);;
 e (SUBGOAL_THEN `&0 < &2*a2 ` ASSUME_TAC);;
e (MATCH_MP_TAC REAL_LT_MUL);;
e (ASM_REWRITE_TAC []);;
e (SIMPLE_COMPLEX_ARITH_TAC);;


e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `	((&0)) = ((&0) * inv (&2 * a2)) 
     		       `]);;


e (SUBGOAL_THEN `(--b2 - sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2) ` ASSUME_TAC);;	
e (MATCH_MP_TAC REAL_LT_RMUL);;	   
e (CONJ_TAC);;  
r(1);;
e (MATCH_MP_TAC REAL_INV_POS);;	   
e (ASM_REWRITE_TAC []);;
e (UNDISCH_TAC `(--b2 - sqrt (b2 pow 2 - &4 * a2 * c2)) * inv (&2 * a2) < &0 * inv (&2 * a2)`);;
e (SIMP_TAC []);;
e (ONCE_REWRITE_TAC[REAL_RING ` ((( --(b:real) - c)) < ( &0)) = (c < --b)`] );;
e (ASM_REWRITE_TAC [NOT_IN_EMPTY]);;
e (ONCE_REWRITE_TAC [REAL_FIELD `(--(x:real) - y < (&0)) = (--x < y)`]);;
e (ASM_REWRITE_TAC []);;


(*-*-*-*-*-*-*-*-*-*-*-*-*-Real Case 4-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)
(*-*-*-*-*0 < a  /\ sqrt (b pow 2 - &4 * a * c) < --b **-**-*-*-*-*-*-*-*)
(*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*)


e (ONCE_REWRITE_TAC [is_stable_phycl_intractn]);;
    e (SIMP_TAC [EXTENSION]);;
    e (REWRITE_TAC[IN_ELIM_THM]);;
e (SUBGOAL_THEN `!x. ( (Cx m * x + Cx cp) * (Cx a * x pow 4 +
              Cx b * x pow 3 +
              Cx c * x pow 2 +
              Cx d * x +
              Cx e) =
              Cx (&0) <=>
              x = --Cx cp / Cx m \/
              x =
              (Cx (--b1) + csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b1) - csqrt (Cx b1 pow 2 - Cx (&4) * Cx a1 * Cx c1)) /
              (Cx (&2) * Cx a1) \/
              x =
              (Cx (--b2) + csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2) \/
              x =
              (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
              (Cx (&2) * Cx a2))` ASSUME_TAC);;
e (STRIP_TAC);;
e (MATCH_MP_TAC QUINTIC_ROOTS);;
e (ASM_SIMP_TAC []);;
e (POP_ASSUM MP_TAC);;
e (ASM_SIMP_TAC []);;

e (ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (DISCH_TAC);;

e (EXISTS_TAC `
          (Cx (--b2) - csqrt (Cx b2 pow 2 - Cx (&4) * Cx a2 * Cx c2)) /
          (Cx (&2) * Cx a2)`);;

e (ASM_REWRITE_TAC []);;

    e (REWRITE_TAC[complex_div]);;

    e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
    e (REWRITE_TAC[GSYM CX_INV]);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_MUL]);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_REWRITE_TAC [GSYM CX_POW]);;
e (REWRITE_TAC[GSYM CX_SUB]);;
(*-------------csqrt--(down)--------------*)
 e (SUBGOAL_THEN `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))` ASSUME_TAC);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (MATCH_MP_TAC CX_SQRT);;
e (REWRITE_TAC [REAL_LE_LT]);;
e (UNDISCH_TAC `&0 < b2 pow 2 - &4 * a2 * c2`);;

e (SIMP_TAC []);;
e (UNDISCH_TAC `csqrt (Cx (b2 pow 2 - &4 * a2 * c2)) = Cx (sqrt (b2 pow 2 - &4 * a2 * c2))`);;

e (SIMP_TAC []);;

(*-------------csqrt--(down)--------------*)

e (DISCH_TAC);;
e (REWRITE_TAC[GSYM CX_MUL]);;

e (REWRITE_TAC[GSYM CX_SUB]);;
e (REWRITE_TAC[RE_CX]);;
e (ONCE_REWRITE_TAC[REAL_RING `--a * c - (b:real) * c = (--a - b) * c `] );;


(*--------2*a <> 0 (Down)--------*)

e (SUBGOAL_THEN ` ~( Cx (&0) = (Cx (&2) * Cx a2)) ` ASSUME_TAC);;
 
	 e (SUBGOAL_THEN `( ( Cx (&0) = (Cx (&2) * Cx a2)) = ( Cx (&0) = Cx (a2) ) ) ` ASSUME_TAC);;

	   e (EQ_TAC);;
   	   e (DISCH_TAC);;
   	     e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(Cx (&0) = Cx a2 )=(Cx (&0) = (Cx (&2) /Cx (&2))  * Cx a2) `]);;
	   e (REWRITE_TAC [complex_div]);;
	   e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;		
	     e (SUBGOAL_THEN `Cx (&2) * inv (Cx (&2)) * Cx a2 = ( Cx (&2) * Cx (a2)) * inv (Cx (&2))` ASSUME_TAC);;
	       e (SIMPLE_COMPLEX_ARITH_TAC);;
	       e (UNDISCH_TAC `Cx (&2) * inv (Cx (&2)) * Cx a2 = (Cx (&2) * Cx a2) * inv (Cx (&2))`);;
	       e (SIMP_TAC []);;	       
	       e (DISCH_TAC);;
	       e (REWRITE_TAC [GSYM complex_div]);;
	       	 e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;	       
		     e (DISCH_TAC);;
		      e (SIMP_TAC [COMPLEX_EQ_RDIV_EQ]);;
	      e (SUBGOAL_THEN `Cx (&0) * Cx (&2) = Cx (&0)` ASSUME_TAC);;
	      	e (SIMPLE_COMPLEX_ARITH_TAC);;
        	e (UNDISCH_TAC `Cx (&0) * Cx (&2) = Cx (&0)`);;
	       	e (SIMP_TAC []);;	       
	       	e (DISCH_TAC);;
	   e (ONCE_ASM_REWRITE_TAC []);;
           e (SIMPLE_COMPLEX_ARITH_TAC);;
	   e (DISCH_TAC);;
	   
	   e (SUBGOAL_THEN `~( Cx (&2) = Cx (&0) )` ASSUME_TAC);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		     e (UNDISCH_TAC `~(Cx (&2) = Cx (&0))`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (DISCH_TAC);;
		     e (REWRITE_TAC [complex_div]);;
		      e (UNDISCH_TAC `(Cx (&0) = Cx a2)`);;
	       	     e (SIMP_TAC [GSYM COMPLEX_EQ_LDIV_EQ]);;
		     e (SIMPLE_COMPLEX_ARITH_TAC);;
		      e (UNDISCH_TAC `Cx (&0) = Cx (&2) * Cx a2 <=> Cx (&0) = Cx a2`);;
		       e (SIMP_TAC []);;
		     
		     e (DISCH_TAC);;
		     
		     e (POP_ASSUM (K ALL_TAC));;
		     
		     e (ONCE_ASM_REWRITE_TAC []);;
		      e (ONCE_ASM_REWRITE_TAC []);;
(*---------2*a <> 0 (Up)-------------*)

	   



 e (SUBGOAL_THEN `(&2 * a2) < &0 ` ASSUME_TAC);;
e (REWRITE_TAC[REAL_MUL_SYM]);;
 e (SUBGOAL_THEN ` &0 < &2` ASSUME_TAC);;

e (SIMPLE_COMPLEX_ARITH_TAC);;

e (UNDISCH_TAC `&0 < &2`);;
e (SIMP_TAC [GSYM REAL_LT_RDIV_EQ]);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH ` &0 / &2 = &0`]);;

e (DISCH_TAC);;


e (ASM_MESON_TAC []);;

e (UNDISCH_TAC `&2 * a2 < &0`);;
e (REWRITE_TAC[GSYM real_div]);;

e (ASM_SIMP_TAC [DENOM_LT_0]);;
e (DISCH_TAC);;
e (ONCE_REWRITE_TAC [SIMPLE_COMPLEX_ARITH `(&2 * a2) * &0 = &0	  
     		       `]);;

e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 < --(a:real) - b) = (b < --a ) `]);;

e (REWRITE_TAC[GSYM REAL_LT_SUB_RADD]);;
e (ONCE_REWRITE_TAC [REAL_ARITH ` (&0 - --(a:real) =  a)`]);;


e (ONCE_ASM_REWRITE_TAC []);;

e (ASM_MESON_TAC [NOT_IN_EMPTY]);;
e (ASM_SIMP_TAC [REAL_FIELD `(--b2 - sqrt (b2 pow 2 - &4 * a2 * c2) < &0) = (--b2 < sqrt (b2 pow 2 - &4 * a2 * c2))`]);;

let QUINTIC_STABLE = top_thm();;


(*===========================================================================*)


g `!a0 a1 a2 a3 a4 m c a41 a42 a31 a32 a21 a22.
         ~(Cx (&0) = Cx m) /\
         ~(Cx (&0) = Cx a) /\
         ~(Cx (&0) = Cx a41) /\
         ~(Cx (&0) = Cx a42) /\
         Cx a4 = Cx (a41 * a42) /\
         Cx a3 = Cx (a41 * a32) + Cx (a42 * a31) /\
         Cx a2 = Cx (a41 * a22) + Cx (a31 * a32) + Cx (a42 * a21) /\
         Cx a1 = Cx (a31 * a22) + Cx (a32 * a21) /\
         Cx a0 = Cx (a21 * a22) /\
(
(
((&0 < a31 / a41 /\
          (a31 pow 2 - &4 * a41 * a21 < &0 \/ a31 pow 2 - &4 * a41 * a21 = &0) \/
          &0 < a31 pow 2 - &4 * a41 * a21 /\
          (a41 < &0 /\
           (a31 < sqrt (a31 pow 2 - &4 * a41 * a21) \/
            sqrt (a31 pow 2 - &4 * a41 * a21) < --a31) \/
           &0 < a41 /\
           (sqrt (a31 pow 2 - &4 * a41 * a21) < a31 \/
            --a31 < sqrt (a31 pow 2 - &4 * a41 * a21))))
 
)  
) \/

((&0 < a32 / a42 /\
          (a32 pow 2 - &4 * a42 * a22 < &0 \/ a32 pow 2 - &4 * a42 * a22 = &0) \/
          &0 < a32 pow 2 - &4 * a42 * a22 /\
          (a42 < &0 /\
           (a32 < sqrt (a32 pow 2 - &4 * a42 * a22) \/
            sqrt (a32 pow 2 - &4 * a42 * a22) < --a32) \/
           &0 < a42 /\
           (sqrt (a32 pow 2 - &4 * a42 * a22) < a32 \/
            --a32 < sqrt (a32 pow 2 - &4 * a42 * a22))))
  )
  
) ==> is_stable_phycl_intractn (\s. (Cx m * s + Cx c) * (Cx a4 * s pow 4 + Cx a3 * s pow 3 + Cx a2 * s pow 2 + Cx a1 * s + Cx a0)) `;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC QUINTIC_STABLE);;
e (EXISTS_TAC `a41:real`);;
e (EXISTS_TAC `a42:real`);;
e (EXISTS_TAC `a31:real`);;
e (EXISTS_TAC `a32:real`);;
e (EXISTS_TAC `a21:real`);;
e (EXISTS_TAC `a22:real`);;
e (ASM_SIMP_TAC []);;
e (REWRITE_TAC [CX_INJ]);;
e (SUBGOAL_THEN `~(&0 = a41)` ASSUME_TAC);;
      e (ASM_SIMP_TAC [GSYM CX_INJ]);;

e (SUBGOAL_THEN `~(&0 = a42)` ASSUME_TAC);;
      e (ASM_SIMP_TAC [GSYM CX_INJ]);;

e (POP_ASSUM MP_TAC);;
e (POP_ASSUM MP_TAC);;
e (CONV_TAC REAL_FIELD);;

let STABLE_IOLM = top_thm();;

(*===========================================================================*)
(*===========================================================================*)


g `!m c mR MR CR CB KB Kp Tc a41 a42 a31 a32 a21 a22.
         ~(Cx (&0) = Cx m) /\
         ~(Cx (&0) = Cx a) /\
         ~(Cx (&0) = Cx a41) /\
         ~(Cx (&0) = Cx a42) /\
         Cx (mR * MR * Tc) = Cx (a41 * a42) /\
         Cx (mR * MR + mR * CR * Tc + mR * CB * Tc + CB * MR * Tc) = Cx (a41 * a32) + Cx (a42 * a31) /\
         Cx (Kp * MR + mR * CB + mR * KB * Tc + mR * CR + CB * MR + CB * CR * Tc + KB * MR * Tc) = Cx (a41 * a22) + Cx (a31 * a32) + Cx (a42 * a21) /\
         Cx (CB * CR + KB * MR + KB * CR * Tc + Kp * CR + mR * KB + KB * CR) = Cx (a31 * a22) + Cx (a32 * a21) /\
         Cx (Kp * KB + KB * CR) = Cx (a21 * a22) /\
(
(
((&0 < a31 / a41 /\
          (a31 pow 2 - &4 * a41 * a21 < &0 \/ a31 pow 2 - &4 * a41 * a21 = &0) \/
          &0 < a31 pow 2 - &4 * a41 * a21 /\
          (a41 < &0 /\
           (a31 < sqrt (a31 pow 2 - &4 * a41 * a21) \/
            sqrt (a31 pow 2 - &4 * a41 * a21) < --a31) \/
           &0 < a41 /\
           (sqrt (a31 pow 2 - &4 * a41 * a21) < a31 \/
            --a31 < sqrt (a31 pow 2 - &4 * a41 * a21))))
 
)  
) \/

((&0 < a32 / a42 /\
          (a32 pow 2 - &4 * a42 * a22 < &0 \/ a32 pow 2 - &4 * a42 * a22 = &0) \/
          &0 < a32 pow 2 - &4 * a42 * a22 /\
          (a42 < &0 /\
           (a32 < sqrt (a32 pow 2 - &4 * a42 * a22) \/
            sqrt (a32 pow 2 - &4 * a42 * a22) < --a32) \/
           &0 < a42 /\
           (sqrt (a32 pow 2 - &4 * a42 * a22) < a32 \/
            --a32 < sqrt (a32 pow 2 - &4 * a42 * a22))))
  )
  
) ==> is_stable_phycl_intractn (\s. (Cx m * s + Cx c) * (Cx (mR * MR * Tc) * s pow 4 + Cx (mR * MR + mR * CR * Tc + mR * CB * Tc + CB * MR * Tc) * s pow 3 + Cx (Kp * MR + mR * CB + mR * KB * Tc + mR * CR + CB * MR + CB * CR * Tc + KB * MR * Tc) * s pow 2 + Cx (CB * CR + KB * MR + KB * CR * Tc + Kp * CR + mR * KB + KB * CR) * s + Cx (Kp * KB + KB * CR))) `;;

e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (MATCH_MP_TAC STABLE_IOLM);;
e (EXISTS_TAC `a41:real`);;
e (EXISTS_TAC `a42:real`);;
e (EXISTS_TAC `a31:real`);;
e (EXISTS_TAC `a32:real`);;
e (EXISTS_TAC `a21:real`);;
e (EXISTS_TAC `a22:real`);;

e (ASM_SIMP_TAC []);;

let STABLE_IOLM_ALT = top_thm();;

(*===========================================================================*)
(*                          End of the Verification                          *)
(*===========================================================================*)
