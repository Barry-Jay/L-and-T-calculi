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
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      DLB_Normal.v                                  *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import General.
Require Import DLB_Terms.
Require Import DLB_Tactics.
Require Import DLB_reduction.


Inductive sort := 
  Tuple 
| Index 
| Term 
| Funty : sort -> sort -> sort
.

Inductive well_formed : sort -> lambda -> Prop := 
| wf_un: well_formed Tuple Unit 
| wf_pair:forall P M, well_formed Tuple P -> well_formed Term M -> well_formed Tuple (Pair P M)
| wf_ref: forall i M, well_formed Tuple M -> well_formed Term (Ref i M) 
| wf_raise_tuple: forall M n j, well_formed Tuple M -> well_formed Tuple (Raise M n j)
| wf_raise_term: forall M n j, well_formed Term M -> well_formed Term (Raise M n j)
| wf_abs : forall j M, well_formed Term M -> well_formed Term (Abs j M)
| wf_app: forall M N, well_formed Term M -> well_formed Term N -> well_formed Term (App M N)
.

Hint Constructors well_formed. 

Lemma unique_sort: 
forall t s1 s2, well_formed s1 t -> well_formed s2 t -> s1 = s2.
Proof. induction t; split_all; inversion H; inversion H0; subst; auto. Qed. 


Lemma dlb_red1_preserves_well_formed: 
forall M N, dlb_red1 M N -> forall s, well_formed s M -> well_formed s N. 
Proof.
intros M N r; induction r; split_all; try (inversion H; subst; auto; fail). 
(* 9 *) 
inversion H; subst; auto. eapply2 wf_ref. eapply2 wf_pair. inversion H3; auto. 
(* 8 *) 
inversion H; subst. inversion H2; subst. eapply2 wf_pair. inversion H2. 
(* 7 *) 
inversion H0; subst; inversion H3; subst. eapply2 wf_ref. 
(* 6 *) 
inversion H0; subst; inversion H3; subst. eapply2 wf_ref. 
(* 5 *) 
inversion H; subst; inversion H2; subst. eapply2 wf_abs. 
(* 4 *) 
inversion H0; subst. inversion H4; subst. auto. 
(* 3 *) 
inversion H0; subst. inversion H4; subst. auto. 
(* 2 *) 
inversion H; subst. inversion H3; subst.  inversion H2; subst.  inversion H5; subst.
eapply2 wf_app. eapply2 wf_app. 
(* 1 *) 
inversion H; subst. inversion H3; subst.  inversion H2; subst.  
eapply2 wf_abs. 
Qed. 

Lemma dlb_red_preserves_well_formed: 
forall red M N, multi_step red M N -> red = dlb_red1 -> 
forall s, well_formed s M -> well_formed s N. 
Proof.
intros red M N r; induction r; split_all; subst. eapply2 IHr. 
eapply2 dlb_red1_preserves_well_formed. 
Qed. 


Fixpoint rank (M: lambda) := 
match M with 
| Unit => 1 
| Pair M1 M2 => S((rank M1) + (rank M2))
| Ref _ P => S (rank P)
| Raise M1 _ _ =>  S(rank M1)
| Abs _ M1 => S(rank M1)
| App M1 M2 => S((rank M1) + (rank M2))
end.

Lemma rank_positive: forall M, rank M > 0. 
Proof. 
induction M; split_all; try omega. 
Qed. 



Ltac rank_tac := match goal with 
| |- forall M, ?P  => 
cut (forall p M, p >= rank M -> P ); [ intros H M;  eapply2 H | 
intro p; induction p; intro M;  [ assert(rank M >0) by eapply2 rank_positive; noway |]
]
end .



(* normal terms *) 

Inductive normal : sort -> lambda -> Prop :=
| nf_un: normal Tuple Unit
| nf_pair: forall s u,  normal Tuple s -> normal Term u -> normal Tuple (Pair s u)
| nf_ref: forall i s, normal Tuple s -> normal Term (Ref i s)
| nf_abs : forall j M, normal Term M -> normal Term (Abs j M)
.

Hint Constructors normal. 

Lemma normal_is_decidable : forall M s, normal s M \/ ~(normal s M).
Proof.
induction M; intro s; case s; auto;
try (right; intro n1;  inversion n1; fail). 
(* 3 *) 
elim(IHM1 Tuple); elim(IHM2 Term); split_all. 
right; intro n; inversion n; assert False by eapply2 H; noway. 
(* 4 *) 
right; intro n; inversion n; assert False by eapply2 H0; noway. 
(* 3 *) 
right; intro n; inversion n; assert False by eapply2 H0; noway. 
(* 2 *) 
elim(IHM Tuple); split_all. right; intro n1; inversion n1; assert False by eapply2 H; noway. 
(* 1 *) 
elim(IHM Term); split_all. right; intro n1; inversion n1; assert False by eapply2 H; noway. 
Qed. 



Lemma normal_implies_well_formed: forall M s, normal s M -> well_formed s M. 
Proof. intros M; induction M; split_all; inversion H; auto; subst.  Qed. 

Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma normal_is_irreducible: 
forall s M, normal s M -> irreducible M seq_red1. 
Proof. 
intros s M nor; induction nor; split_all; intro; intro r; inversion r; subst; split_all.  
(* 4 *) 
eapply2 IHnor1.
(* 3 *)
eapply2 IHnor2.
(* 2 *) 
eapply2 IHnor.
(* 1 *) 
eapply2 IHnor.
Qed. 

(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Lemma beta_normal:
  forall j M N, normal Term M -> well_formed Term (App (Abs j M) N) ->
                   exists P, seq_red1 (App (Abs j M) N) P. 
Proof.
  induction M; split_all; inversion H; subst; eauto.
  assert(n<j \/ n> j \/ n=j) by omega. inversion H1; subst; eauto. 
inversion H3; subst; eauto. inversion H2; subst; eauto; inversion H3; subst; eauto.
Qed. 


Lemma raise_normal:
  forall M, normal Term M -> forall n j, exists N, seq_red1 (Raise M n j) N. 
Proof. 
induction M; split_all; eauto; inversion H; subst. 
cut(n < j \/ n >= j).  intro c; inversion c; eauto. omega. 
Qed. 

Theorem tuple_progress : 
forall (M : lambda) s, well_formed s M -> (normal s M) \/ (exists N, seq_red1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.  
(* 6 *) 
inversion H; subst; eauto. 
(* 5 *) 
inversion H; subst; eauto. 
assert((normal Tuple M1) \/ (exists N : lambda, seq_red1 M1 N)). 
eapply2 IHM1. 
inversion H0; split_all. 
assert((normal Term M2) \/ (exists N : lambda, seq_red1 M2 N)). 
eapply2 IHM2. 
inversion H2; split_all; subst; eauto. 
right; exist (Pair x M2). 
(* 4 *) 
inversion H; subst. 
assert(normal Tuple M \/ (exists N : lambda, seq_red1 M N)) by  eapply2 IHM. 
inversion H0; split_all. right; eauto. 
(* 3 *) 
right. inversion H; subst. 
elim(IHM Tuple); split_all. 
inversion H0; subst; eauto.  eauto. 
elim(IHM Term); split_all. 
inversion H0; subst; eauto.  
cut(i < n0 \/ i >= n0).  intro c; inversion c; eauto. omega. 
eauto. 
(* 2 *) 
 inversion H; subst. 
elim(IHM Term); split_all. 
right; eauto. 
(* 1 *) 
right. 
inversion H; subst; eauto. 
elim(IHM1 Term); split_all. 
inversion H0; subst; eauto. 
inversion H0; subst. eapply2 beta_normal.
eauto. 
Qed. 

Lemma irreducible_is_normal: 
forall s M, well_formed s M -> irreducible M seq_red1 -> normal s M. 
Proof. split_all. elim(tuple_progress M s); split_all. assert False by eapply2 H0; noway. Qed. 

Theorem irreducible_iff_normal: forall s M, well_formed s M -> (irreducible M seq_red1 <-> normal s M). 
Proof. split_all. eapply2 irreducible_is_normal. eapply2 normal_is_irreducible. Qed. 


Definition stable M := forall N, dlb_red M N -> N = M. 

Theorem normal_implies_stable: forall s M, normal s M -> stable M. 
Proof. 
unfold stable; split_all.
assert(seq_red M N) by eapply2 dlb_red_to_seq_red.  
inversion H1; subst. auto. 
assert(irreducible M seq_red1). eapply2 irreducible_iff_normal. 
eapply2 normal_implies_well_formed. 
assert False by eapply2 H4. noway. 
Qed. 
