(**********************************************************************)
(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*           Delayed Substitution Lambda Calculus                     *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      DLB_reduction.v                               *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import General.
Require Import DLB_Terms.
Require Import DLB_Tactics.


(* Parallel lift reduction *)

Definition termred := lambda -> lambda -> Prop. 

Inductive dlb_red1: termred := 
  | un_dlb_red : dlb_red1 Unit Unit
  | pair_dlb_red : forall M M' ,
      dlb_red1 M M' ->
      forall N N', dlb_red1 N N' -> dlb_red1 (Pair M N) (Pair M' N')
  | ref_dlb_red : forall i M M', dlb_red1 M M' -> dlb_red1 (Ref i M) (Ref i M')
  | raise_dlb_red : forall n j M M' ,  dlb_red1 M M' -> dlb_red1 (Raise M n j) (Raise M' n j)
  | abs_dlb_red :
      forall j M M', dlb_red1 M M' -> dlb_red1 (Abs j M) (Abs j M') 
  | app_dlb_red :
      forall M M' ,
      dlb_red1 M M' ->
      forall N N', dlb_red1 N N' -> dlb_red1 (App M N) (App M' N')
  | ref_app_red : forall i M M' N N', dlb_red1 M M' -> dlb_red1 N N' ->
                                  dlb_red1 (App (Ref i M) N) (Ref i (Pair M' N'))
  | raise_un_dlb_red: forall n j, dlb_red1 (Raise Unit n j) Unit 
  | raise_pair_dlb_red: forall n j M M' N N', dlb_red1 M M' -> dlb_red1 N N' ->
                                                dlb_red1 (Raise (Pair M N) n j) 
                                                           (Pair (Raise M' n j) (Raise N' n j))
  | raise_lt_dlb_red : forall n j i M M', dlb_red1 M M' -> i<j -> 
                                       dlb_red1 (Raise (Ref i M) n j) (Ref i (Raise M' n j))
  | raise_gte_dlb_red : forall n j i M M', dlb_red1 M M' -> i>= j -> 
                                       dlb_red1 (Raise (Ref i M) n j) (Ref (i+n) (Raise M' n j))
  | raise_abs_dlb_red : forall M M', 
                     dlb_red1 M M' ->
                     forall i n j, dlb_red1 (Raise (Abs i M) n j) 
                                              (Abs i (Raise M' (S(i+n)) j))
  | beta_lt_red : forall j i N, i < j -> 
                                   dlb_red1 (App (Abs j (Ref i Unit)) N) (Ref i Unit)
  | beta_gt_red : forall j i N, i > j -> 
                                   dlb_red1 (App (Abs j (Ref i Unit)) N) (Ref (pred i) Unit)
  | beta_eq_red : forall j N N', dlb_red1 N N' -> 
                                   dlb_red1 (App (Abs j (Ref j Unit)) N) (Raise N' 0 j)
  | beta_pair_red : forall j i M M' N N' P P', dlb_red1 M M' -> dlb_red1 N N' -> dlb_red1 P P' ->
                                    dlb_red1 (App (Abs j (Ref i (Pair P M))) N) 
                                               (App (App (Abs j (Ref i P')) N') (App (Abs j M') N'))
  | beta_abs_red : forall j k M M' N N',
                     dlb_red1 M M' -> dlb_red1 N N' -> 
                     dlb_red1 (App (Abs j (Abs k M)) N) 
                               (Abs k (App (Abs (S(k+j)) M') N'))
.

Hint Constructors dlb_red1. 

Definition dlb_red := multi_step dlb_red1. 


Lemma refl_dlb_red1: reflective dlb_red1. 
Proof. red. induction M; split_all. Qed. 

Hint Resolve refl_dlb_red1. 

Lemma preserves_unit_dlb_red: 
forall red M N, multi_step red M N -> red = dlb_red1 -> M = Unit -> N = Unit. 
Proof. intros red M N r; induction r; split_all; subst. inversion H; subst. auto. Qed. 

Lemma preserves_pair_dlb_red: 
forall M M' N N', dlb_red M M' -> dlb_red N N' -> dlb_red (Pair M N) (Pair M' N').
Proof. 
intros. apply transitive_red with (Pair M' N). 
eapply2 preserves_pairl_multi_step. red; split_all. 
eapply2 preserves_pairr_multi_step. red; split_all. 
Qed. 

Lemma preserves_ref_dlb_red: 
forall red M M', multi_step red M M' -> red = dlb_red1 -> 
forall i, dlb_red (Ref i M) (Ref i M').
Proof.
intros red M M' r; induction r; split_all; subst. eapply2 zero_red. 
eapply succ_red. eapply ref_dlb_red.  eexact H. eapply2 IHr. 
Qed. 

Lemma preserves_raise_dlb_red: 
forall red M M', multi_step red M M' -> red = dlb_red1 -> 
forall n j, dlb_red (Raise M n j) (Raise M' n j).
Proof.
intros red M M' r; induction r; split_all; subst. eapply2 zero_red. 
eapply succ_red. eapply raise_dlb_red.  eexact H. eapply2 IHr. 
Qed. 

Lemma preserves_appl_dlb_red: 
forall red M M' N, multi_step red M M' -> red = dlb_red1 -> dlb_red (App M N) (App M' N).
Proof. 
intros red M M' N r; induction r; split_all; subst. eapply2 zero_red. 
apply succ_red with (App N0 N).  auto. eapply2 IHr. 
Qed. 

Lemma preserves_appr_dlb_red: 
forall red M N N', multi_step red N N' -> red = dlb_red1 -> dlb_red (App M N) (App M N').
Proof. 
intros red M N N' r; induction r; split_all; subst. eapply2 zero_red. 
apply succ_red with (App M N).  auto. eapply2 IHr. 
Qed. 

Lemma preserves_app_dlb_red: 
forall M M' N N', dlb_red M M' -> dlb_red N N' -> dlb_red (App M N) (App M' N').
Proof. 
intros. apply transitive_red with (App M' N). 
eapply2 preserves_appl_dlb_red. 
eapply2 preserves_appr_dlb_red. 
Qed. 

Lemma preserves_abs_dlb_red: 
forall red M M' j, multi_step red M M' -> red = dlb_red1 -> dlb_red (Abs j M) (Abs j M').
Proof. 
intros red M M' N r; induction r; split_all; subst. eapply2 zero_red. 
apply succ_red with (Abs N N0).  auto. eapply2 IHr. 
Qed. 

Lemma preserves_unit2_dlb_red: 
forall red P1 P2, multi_step red P1 P2 -> red = dlb_red1 -> 
P1 = Unit -> P2 = Unit. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
inversion H; subst. eapply2 IHr. 
Qed. 

Lemma preserves_pair2_dlb_red: 
forall red P1 P2, multi_step red P1 P2 -> red = dlb_red1 -> 
forall M1 N1, P1 = Pair M1 N1 -> 
exists M2 N2, P2 = Pair M2 N2 /\ dlb_red M1 M2 /\ dlb_red N1 N2. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
exist M1; exist N1; eapply2 zero_red. 
inversion H; subst. 
assert(exists M2 N2 : lambda,
          P = Pair M2 N2 /\ dlb_red M' M2 /\ dlb_red N' N2). eapply2 IHr. 
split_all; subst. exist x; exist x0; eapply2 succ_red. 
Qed. 

Lemma preserves_ref2_dlb_red: 
forall red P1 P2, multi_step red P1 P2 -> red = dlb_red1 -> 
forall i s1, P1 = Ref i s1 -> 
exists s2, P2 = Ref i s2 /\ dlb_red s1 s2. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
exist s1; eapply2 zero_red. 
inversion H; subst. 
assert( exists s2 : lambda, P = Ref i s2 /\ dlb_red M' s2).  eapply2 IHr. 
split_all; subst. exist x; eapply2 succ_red. 
Qed. 

Lemma preserves_abs2_dlb_red: 
forall red P1 P2, multi_step red P1 P2 -> red = dlb_red1 -> 
forall j t1, P1 = Abs j t1 -> 
exists t2, P2 = Abs j t2 /\ dlb_red t1 t2. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
exist t1; eapply2 zero_red. 
inversion H; subst. 
assert( exists t2 : lambda, P = Abs j t2 /\ dlb_red M' t2).  eapply2 IHr. 
split_all; subst. exist x; eapply2 succ_red. 
Qed. 


Lemma diamond_dlb_red1 : diamond dlb_red1 dlb_red1. 
Proof. 
red. induction M; split_all. 
(* 6 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
(* 5 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
elim(IHM1 M' M'0); split_all. 
elim(IHM2 N' N'0); split_all.  exist (Pair x x0). 
(* 4 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
elim(IHM M' M'0); split_all. eauto. 
(* 3 *) 
inversion H; subst. 
(* 8 *) 
   inversion H0; subst; eauto; try discriminate. 
(* 13 *)
elim(IHM M'0 M'); split_all; eauto. 
(* 12 *) 
inversion H5; subst; eauto. 
(* 11 *) 
inversion H5; subst; eauto. 
elim(IHM (Pair M'0 N') (Pair M'1 N'0)); split_all. 
inversion H2; inversion H4; subst. inversion H16; subst.
exist (Pair (Raise M' n n0) (Raise N'1 n n0)). 
(* 10 *) 
inversion H5; subst; eauto. 
elim(IHM(Ref i M'0) (Ref i M'1)); split_all; eauto.
inversion H2; inversion H3; subst. inversion H12; subst.
exist (Ref i (Raise M' n n0)). 
(* 9 *) 
inversion H5; subst; eauto. 
elim(IHM(Ref i M'0) (Ref i M'1)); split_all; eauto.
inversion H2; inversion H3; subst. inversion H12; subst.
exist (Ref (i+n) (Raise M' n n0)). 
(* 8 *) 
inversion H5; subst; eauto. 
elim(IHM (Abs i M'0) (Abs i M'1)); split_all. 
inversion H2; inversion H3; subst. inversion H11; subst.
exist (Abs i (Raise M' (S (i + n)) n0)).
(* 7 *) 
inversion H0; subst; eauto. 
inversion H5; subst; eauto. 
(* 6 *) 
inversion H0; subst. inversion H7; subst.  
elim(IHM (Pair M' N') (Pair M'1 N'0)); split_all. inversion H2; inversion H4; subst. 
inversion H16; subst. 
exist(Pair (Raise M'0 n n0) (Raise N'1 n n0)). 
elim(IHM (Pair M' N') (Pair M'0 N'0)); split_all. inversion H2; inversion H3; subst. 
inversion H15; subst. 
exist(Pair (Raise M'1 n n0) (Raise N'1 n n0)). 
(* 5 *) 
inversion H0; subst. inversion H7; subst.  
elim(IHM (Ref i M') (Ref i M'1)); split_all. inversion H2; inversion H3; subst. 
inversion H12; subst. 
exist(Ref i (Raise M'0 n n0)). 
elim(IHM (Ref i M') (Ref i M'0)); split_all. inversion H2; inversion H3; subst. 
inversion H12; subst. 
exist(Ref i (Raise M'1 n n0)). 
noway. 
(* 4 *) 
inversion H0; subst. inversion H7; subst.  
elim(IHM (Ref i M') (Ref i M'1)); split_all. inversion H2; inversion H3; subst. 
inversion H12; subst. 
exist(Ref (i+n) (Raise M'0 n n0)). 
elim(IHM (Ref i M') (Ref i M'0)); split_all. inversion H2; inversion H3; subst. 
inversion H12; subst. 
exist(Ref (i+n) (Raise M'1 n n0)). 
noway. 
elim(IHM (Ref i M') (Ref i M'0)); split_all. inversion H2; inversion H3; subst. 
inversion H12; subst. 
exist(Ref (i+n) (Raise M'1 n n0)). 
(* 3 *) 
inversion H0; subst. inversion H6; subst.  
elim(IHM (Abs i M') (Abs i M'1)); split_all. inversion H2; inversion H3; subst. 
inversion H11; subst. 
exist(Abs i (Raise M'0 (S (i + n)) n0)).
elim(IHM (Abs i M') (Abs i M'0)); split_all. inversion H2; inversion H3; subst. 
inversion H10; subst. 
exist(Abs i (Raise M'1 (S (i + n)) n0)).
(* 2 *) 
inversion H; inversion H0; subst. 
elim(IHM M' M'0); split_all. exist (Abs n x). 
(* 1 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
(* 25 *)
elim(IHM1 M'0 M'); elim(IHM2 N' N'0); split_all; eauto. 
(* 24 *) 
inversion H3; subst. elim(IHM1 (Ref i M'0) (Ref i M'1)); elim(IHM2 N' N'0); split_all; eauto. 
inversion H4; inversion H7; subst. invsub. exist (Ref i (Pair M' x)). 
(* 23 *) 
inversion H3; subst. inversion H6; subst. inversion H7; subst. eauto. 
(* 22 *) 
inversion H3; subst. inversion H6; subst. inversion H7; subst. eauto. 
(* 21 *) 
inversion H3; subst. inversion H6; subst. inversion H7; subst.
elim(IHM2 N' N'0); split_all. eauto. 
(* 20 *) 
inversion H3; subst. inversion H6; subst. inversion H7; subst.
elim(IHM1 (Abs j (Ref i (Pair P' M'0))) (Abs j (Ref i (Pair M'1 N'1)))); elim(IHM2 N' N'0);split_all. 
inversion H10; inversion H13; subst. invsub. 
inversion H17; inversion H21; subst. invsub. 
inversion H18; inversion H23; subst. invsub. 
exist(App (App (Abs j (Ref i M')) x) (App (Abs j  N'2) x)). 
(* 19 *) 
inversion H3; subst. inversion H6; subst. 
elim(IHM1 (Abs j (Abs k M'0)) (Abs j (Abs k M'))); elim(IHM2 N' N'0); split_all. 
inversion H4; inversion H9; subst. invsub. 
inversion H14; inversion H18; subst. invsub. 
exist (Abs k (App (Abs (S (k+j)) M'2) x)).
(* 18 *) 
inversion H8; subst. elim(IHM1 (Ref i M') (Ref i M'1)); elim(IHM2 N' N'0); split_all. 
inversion H4; inversion H7; subst; invsub. exist(Ref i (Pair M'0 x)). 
(* 17 *) 
invsub. elim(IHM1 (Ref i M') (Ref i M'0)); elim(IHM2 N' N'0); split_all. 
inversion H4; inversion H6; subst; invsub. exist(Ref i (Pair M'1 x)). 
(* 16 *) 
inversion H7; subst. inversion H5; subst. inversion H6; subst. eauto. 
(* 15 *) 
invsub. eauto. 
(* 14 *) 
invsub. noway. 
(* 13 *) 
invsub. noway. 
(* 12 *) 
inversion H7; subst. inversion H5; subst. inversion H6; subst.  eauto. 
(* 11 *) 
invsub. noway. 
(* 10 *) 
invsub. eauto. 
(* 9 *) 
invsub. noway. 
(* 8 *) 
inversion H7; subst. inversion H5; subst. inversion H6; subst. 
elim(IHM2 N' N'0); split_all; eauto. 
(* 7 *) 
invsub. noway. 
(* 6 *) 
invsub. noway. 
(* 5 *)
inversion H5; subst. elim(IHM2 N' N'0); split_all. eauto. 
(* 4 *) 
inversion H9; subst. inversion H7; subst. inversion H8; subst. 
elim(IHM1 (Abs j (Ref i (Pair P' M'))) (Abs j (Ref i (Pair M'1 N'1))));
elim(IHM2 N' N'0); split_all.
inversion H10; inversion H13; subst. invsub. 
inversion H17; inversion H21; subst. invsub. 
inversion H18; inversion H23; subst. invsub. 
exist(App (App (Abs j (Ref i M'0)) x) (App (Abs j N'2) x)). 
(* 3 *) 
invsub. 
elim(IHM1 (Abs j (Ref i (Pair P' M'))) (Abs j (Ref i (Pair P'0 M'0))));
elim(IHM2 N' N'0); split_all.
inversion H5; inversion H7; subst. invsub. 
inversion H14; inversion H18; subst. invsub. 
inversion H15; inversion H20; subst. invsub. 
exist(App (App (Abs j (Ref i M'1)) x) (App (Abs j N'1) x)). 
(* 2 *) 
inversion H8; subst. inversion H6; subst. 
elim(IHM1 (Abs j (Abs k M')) (Abs j (Abs k M'0))); elim(IHM2 N' N'0); split_all. 
inversion H4; inversion H9; subst. invsub. 
inversion H14; inversion H18; subst. invsub. 
exist (Abs k (App (Abs (S(k+j)) M'2) x)). 
(* 1 *) 
invsub. 
elim(IHM1 (Abs j (Abs k M')) (Abs j (Abs k M'0))); elim(IHM2 N' N'0); split_all. 
inversion H4; inversion H6; subst. invsub. 
inversion H12; inversion H16; subst. invsub. 
exist (Abs k (App (Abs (S(k+j)) M'2) x)).
Qed. 


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem tuple_parallel_confluence: confluence lambda dlb_red. 
Proof. red. eapply2 diamond0_tiling. eapply2 diamond_iff_diamond0. eapply2 diamond_dlb_red1. Qed.

(* sequential reduction *)



Inductive seq_red1 : lambda -> lambda -> Prop := 
  | pairl_seq_red :  forall M M' N, seq_red1 M M' -> seq_red1 (Pair M N) (Pair M' N)
  | pairr_seq_red :  forall M N N', seq_red1 N N' -> seq_red1 (Pair M N) (Pair M N')
  | ref_seq_red : forall i M M' ,  seq_red1 M M' -> seq_red1 (Ref i M) (Ref i M')
  | raise_seq_red : forall n j M M', seq_red1 M M' -> seq_red1 (Raise M n j) (Raise M' n j)
  | abs_seq_red :  forall i M M', seq_red1 M M' -> seq_red1 (Abs i M) (Abs i M') 
  | appl_seq_red :  forall M M' N, seq_red1 M M' -> seq_red1 (App M N) (App M' N)
  | appr_seq_red :  forall M N N', seq_red1 N N' -> seq_red1 (App M N) (App M N')
  | ref_pair_seq_red : forall i M N, seq_red1 (App (Ref i M) N) (Ref i (Pair M N))
  | raise_un_seq_red: forall n j, seq_red1 (Raise Unit n j) Unit 
  | raise_pair_seq_red: forall n j M N,
                          seq_red1 (Raise (Pair M N) n j) 
                                     (Pair (Raise M n j) (Raise N n j))
  | raise_lt_seq_red : forall n j i M,  i<j -> 
                                       seq_red1 (Raise (Ref i M) n j) (Ref i (Raise M n j))
  | raise_gte_seq_red : forall n j i M, i>= j -> 
                                        seq_red1 (Raise (Ref i M) n j) (Ref (i+n) (Raise M n j))
  | raise_abs_seq_red : 
                     forall i M n j, seq_red1 (Raise (Abs i M) n j) 
                                              (Abs i (Raise M (S(i+n)) j))
  | beta_lt_seq_red : forall j i N, i < j -> 
                                   seq_red1 (App (Abs j (Ref i Unit)) N) (Ref i Unit)
  | beta_gt_seq_red : forall j i N, i > j -> 
                                   seq_red1 (App (Abs j (Ref i Unit)) N) (Ref (pred i) Unit)
  | beta_eq_seq_red : forall j N,
                                   seq_red1 (App (Abs j (Ref j Unit)) N) (Raise N 0 j)
  | beta_pair_seq_red : forall j i M N P,
                                    seq_red1 (App (Abs j (Ref i (Pair P M))) N) 
                                               (App (App (Abs j (Ref i P)) N) (App (Abs j M) N))
  | beta_abs_seq_red : forall j k M N,
                     seq_red1 (App (Abs j (Abs k M)) N) 
                               (Abs k (App (Abs (S(k+j)) M) N))
.


Definition seq_red := multi_step seq_red1. 

Hint Constructors seq_red1 .


Lemma reflective_seq_red: reflective seq_red. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_seq_red.


Lemma preserves_pairl_seq_red: preserves_pairl seq_red. 
Proof. eapply2 preserves_pairl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_pairl_seq_red.

Lemma preserves_pairr_seq_red: preserves_pairr seq_red. 
Proof. eapply2 preserves_pairr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_pairr_seq_red.


Lemma preserves_pair_seq_red: preserves_pair seq_red. 
Proof. 
red; split_all. 
apply transitive_red with (Pair M' N); split_all. 
eapply2 preserves_pairl_seq_red. 
eapply2 preserves_pairr_seq_red. 
Qed. 
Hint Resolve preserves_pair_seq_red.



Lemma preserves_apl_seq_red: preserves_apl seq_red. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_seq_red.

Lemma preserves_apr_seq_red: preserves_apr seq_red. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_seq_red.

Lemma preserves_app_seq_red: preserves_app seq_red. 
Proof. 
red; split_all. 
apply transitive_red with (App M' N); split_all. 
eapply2 preserves_apl_seq_red. 
eapply2 preserves_apr_seq_red. 
Qed. 
Hint Resolve preserves_app_seq_red.


Lemma preserves_abs_seq_red: preserves_abs seq_red. 
Proof. eapply2 preserves_abs_multi_step. red; split_all.  Qed. 

Hint Resolve preserves_app_seq_red preserves_abs_seq_red.


Lemma preserves_raise_seq_red: preserves_raise seq_red. 
Proof. eapply2 preserves_raise_multi_step. red; split_all.  Qed. 

Hint Resolve preserves_raise_seq_red.

Lemma preserves_ref_seq_red: preserves_ref seq_red. 
Proof. eapply2 preserves_ref_multi_step. red; split_all.  Qed. 

Hint Resolve preserves_ref_seq_red.


Lemma seq_red1_to_dlb_red1 : implies_red seq_red1 dlb_red1. 
Proof.  red. intros M N B; induction B; split_all; try (red; one_step; fail). Qed. 


Lemma seq_red_to_dlb_red: implies_red seq_red dlb_red. 
Proof.
  eapply2 implies_red_multi_step. red; split_all; one_step; eapply2 seq_red1_to_dlb_red1.
Qed. 



Lemma to_seq_red_multi_step: forall red, implies_red red seq_red -> implies_red (multi_step red) seq_red. 
Proof. 
red.  intros red B M N R; induction R; split_all.
red; split_all. 
assert(seq_red M N) by eapply2 B. 
apply transitive_red with N; auto. 
eapply2 IHR. 
Qed. 

Hint Resolve preserves_app_seq_red preserves_abs_seq_red. 


Lemma dlb_red1_to_seq_red: implies_red dlb_red1 seq_red .
Proof. 
  red.  intros M N OR; induction OR; split_all; eapply2 succ_red;
        try eapply2 preserves_ref_seq_red;
        try eapply2 preserves_pair_seq_red;
        try eapply2 preserves_abs_seq_red; 
        try eapply2 preserves_app_seq_red; 
        try eapply2 preserves_aps_seq_red; 
        try eapply2 preserves_raise_seq_red. 
Qed.

Hint Resolve dlb_red1_to_seq_red.

Lemma dlb_red_to_seq_red: implies_red dlb_red seq_red. 
Proof. eapply2 to_seq_red_multi_step. Qed.


Lemma diamond_seq_red: diamond seq_red seq_red. 
Proof. 
red; split_all. 
assert(dlb_red M N) by eapply2 seq_red_to_dlb_red.  
assert(dlb_red M P) by eapply2 seq_red_to_dlb_red.  
elim(tuple_parallel_confluence M N H1 P); split_all. 
exist x; eapply2 dlb_red_to_seq_red. 
Qed. 


Theorem tuple_confluence: confluence lambda seq_red. 
Proof. red. split_all. eapply2 diamond_seq_red. Qed.

