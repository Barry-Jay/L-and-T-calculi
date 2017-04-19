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
(*             Delayed Substitution Lambda Calculus                   *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                    DLB_Tactics.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import General.
Require Import DLB_Terms. 

Definition termred := lambda -> lambda -> Prop.

Definition preserve (R : termred) (P : lambda -> Prop) :=
  forall x : lambda, P x -> forall y : lambda, R x y -> P y.


Inductive multi_step : termred -> termred :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: lambda-> lambda -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.

Hint Constructors multi_step.

Definition reflective red := forall (M: lambda), red M M.

Lemma refl_multi_step : forall (red: termred), reflective (multi_step red).
Proof. red; split_all. Qed.


Ltac reflect := match goal with 
| |- reflective (multi_step _) => eapply2 refl_multi_step
| |- multi_step _ _ _ => try (eapply2 refl_multi_step)
| _ => split_all
end.


Ltac one_step := 
match goal with 
| |- multi_step _ _ ?N => apply succ_red with N; auto; try reflect
end.

Definition transitive red := forall (M N P: lambda), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; split_all. 
apply succ_red with N; auto. 
Qed. 

Definition preserves_pairl (red : termred) := 
forall M M' N, red M M' -> red (Pair M N) (Pair M' N).

Definition preserves_pairr (red : termred) := 
forall M N N', red N N' -> red (Pair M N) (Pair M N').

Lemma preserves_pairl_multi_step : forall (red: termred), preserves_pairl red -> preserves_pairl (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (Pair N0 N); auto. Qed. 

Lemma preserves_pairr_multi_step : forall (red: termred), preserves_pairr red -> preserves_pairr (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (Pair M N); auto. Qed. 


Definition preserves_pair (red : termred) := 
forall M M' N N', red M M' -> red N N' -> red (Pair M N) (Pair M' N').


Definition preserves_apl (red : termred) := 
forall M M' N, red M M' -> red (App M N) (App M' N).

Definition preserves_apr (red : termred) := 
forall M N N', red N N' -> red (App M N) (App M N').

Lemma preserves_apl_multi_step : forall (red: termred), preserves_apl red -> preserves_apl (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App N0 N); auto. Qed. 

Lemma preserves_apr_multi_step : forall (red: termred), preserves_apr red -> preserves_apr (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App M N); auto. Qed. 


Definition preserves_app (red : termred) := 
forall M M' N N', red M M' -> red N N' -> red (App M N) (App M' N').


Definition preserves_abs (red : termred) := 
forall j M N, red M N -> red (Abs j M) (Abs j N).


Lemma preserves_abs_multi_step : forall red, preserves_abs red -> preserves_abs (multi_step red). 
Proof.
red; induction 2; split_all.
apply succ_red with (Abs j N); auto.
Qed.


Definition preserves_ref (red : termred) := 
forall M N, red M N ->  forall i, red (Ref i M) (Ref i N).

Lemma preserves_ref_multi_step : forall red, preserves_ref red -> preserves_ref (multi_step red). 
Proof.
red; induction 2; split_all.
apply succ_red with (Ref i N); auto.
Qed.


Definition preserves_raise (red : termred) := 
forall M N, red M N ->  forall n j, red (Raise M n j) (Raise N n j).

Lemma preserves_raise_multi_step : forall red, preserves_raise red -> preserves_raise (multi_step red). 
Proof.
red; induction 2; split_all.
apply succ_red with (Raise N n j); auto.
Qed.

Lemma preserves_app_multi_step : forall (red: termred), reflective red -> preserves_app red -> preserves_app (multi_step red). 
Proof.
red. induction 3; split_all. generalize H0; induction 1. 
reflect. 
apply succ_red with (App M N); auto.
assert( transitive (multi_step red)) by eapply2 transitive_red.  
apply X0 with (App N0 N); auto. 
one_step. 
Qed.

Hint Resolve preserves_abs_multi_step  preserves_app_multi_step . 



Definition preserves_abs1 (red: termred) := 
forall M N, red M N -> forall j M0, M = Abs j M0 -> 
  exists N0, red M0 N0 /\ Abs j N0 = N.

Lemma preserves_abs1_multi_step : forall red, preserves_abs1 red -> preserves_abs1 (multi_step red).
Proof. 
unfold preserves_abs1.  induction 2; split_all. 
exist M0. 
assert(exists N0 : lambda, red M0 N0 /\ Abs j N0 = N) by eapply2 H; split_all.
assert(exists N0 : lambda, multi_step red x N0 /\ Abs j N0 = P) by eapply2 IHmulti_step; split_all.
exist x0. 
apply succ_red with x; auto.
Qed.

Hint Resolve preserves_abs1_multi_step . 

Ltac inv1 prop := 
match goal with 
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| H: prop (App  _ _) |- _ => inversion H; clear H; inv1 prop
| H: prop (Abs _ _) |- _ => inversion H; clear H; inv1 prop
| _ => split_all
 end.


Definition implies_red (red1 red2: termred) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with N; auto. 
Qed. 


Ltac inv red := 
match goal with 
| H: multi_step red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Abs _ _) _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: red (Abs _ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Abs _ _) |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: red _ (Abs _ _) |- _ => inversion H; clear H; inv red
| _ => subst; split_all 
 end.


Definition diamond0 (red1 red2 : termred) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond0_flip: forall red1 red2, diamond0 red1 red2 -> diamond0 red2 red1. 
Proof. unfold diamond0; split_all. elim (H M P H1 N H0); split_all. exist x. Qed.

Lemma diamond0_strip : 
forall red1 red2, diamond0 red1 red2 -> diamond0 red1 (multi_step red2). 
Proof. intros. 
eapply2 diamond0_flip. 
red; induction 1; split_all.
exist P.
elim (H M P0 H2 N); split_all. 
elim(IHmulti_step H x); split_all. 
exist x0.
apply succ_red with x; auto. 
Qed. 


Definition diamond0_star (red1 red2: termred) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond0_star_strip: forall red1 red2, diamond0_star red1 red2 -> diamond0 (multi_step red2) red1 .
Proof. 
red. induction 2; split_all. 
exist P.
elim(H M P0 H2 N H0); split_all. 
elim(IHmulti_step H x); split_all. 
exist x0.
apply transitive_red with x; auto. 
Qed. 

Lemma diamond0_tiling : 
forall red1 red2, diamond0 red1 red2 -> diamond0 (multi_step red1) (multi_step red2).
Proof. 
red.  induction 2; split_all.
exist P.
elim(diamond0_strip red red2 H M N H0 P0); split_all.
elim(IHmulti_step H x H4); split_all.
exist x0.
apply succ_red with x; auto.
Qed. 

Hint Resolve diamond0_tiling. 



Definition diamond (red1 red2 : termred) := 
forall M N P, red1 M N -> red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_iff_diamond0 : forall red1 red2, diamond red1 red2 <-> diamond0 red1 red2. 
Proof.  intros; red; split_all; red; split_all; eapply2 H. Qed.

Lemma diamond_tiling : forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof.
  intros. eapply2 diamond_iff_diamond0. eapply2 diamond0_tiling. eapply2 diamond_iff_diamond0.
Qed. 

