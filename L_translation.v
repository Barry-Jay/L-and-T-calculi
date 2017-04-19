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
(*                        L-Calculus                                  *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                         L_translation.v                            *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import Test.
Require Import General.
Require Import DLB_Terms.
Require Import DLB_Tactics.
Require Import DLB_reduction.
Require Import DLB_Normal.
Require Import L_Combinators.
Require Import L_combinator_tactics.
Require Import L_opred.


Fixpoint nat_comb i :=
  match i with
    | 0 => Op Zero
    | S i => Ap (Op Next) (nat_comb i)
  end.

  Lemma discriminate_lt: forall i n s t u, i<n ->
       opred (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (nat_comb i)) (nat_comb n)) s) t) u) s. 
  Proof.
    induction i; split_all. gen_case H n; split_all. noway. red; one_step. 
    gen_case H n; split_all. noway. eapply succ_red. eapply2 disc_nn_red. eapply2 IHi. omega.
  Qed.
  
  Lemma discriminate_gt: forall i n s t u, i>n ->
       opred (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (nat_comb i)) (nat_comb n)) s) t) u) t. 
  Proof.
    induction i; split_all. noway.  gen_case H n; split_all. red; one_step. 
    eapply succ_red. eapply2 disc_nn_red. eapply2 IHi. omega.
  Qed.
  
  Lemma discriminate_eq: forall i s t u, 
       opred (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (nat_comb i)) (nat_comb i)) s) t) u) u. 
  Proof.
    induction i; split_all. red; one_step. eapply succ_red. eapply2 disc_nn_red. eapply2 IHi. 
  Qed.
  
  Lemma pred_nat_comb: forall i,  opred (Ap (Op Pred) (nat_comb i)) (nat_comb (pred i)).
  Proof. induction i; split_all; red; one_step. Qed. 

  Lemma plus_nat_comb:
    forall i j, opred (Ap (Ap (Op Plus) (nat_comb i)) (nat_comb j)) (nat_comb (i+j)). 
  Proof.
    induction i; split_all.  red; one_step.
    eapply succ_red. eapply2 plus_next_red.
    replace (Ap (Op Next) (nat_comb j)) with (nat_comb (S j)) by auto. 
    replace (Ap (Op Next) (nat_comb (i+j))) with (nat_comb (S(i + j))) by auto. 
    replace (S(i+j)) with (i+ S j) by omega. eapply2 IHi. 
  Qed.
  

Fixpoint translation (M:lambda) :=
  match M with
    | Unit  => Op Un
    | Pair N P => Ap (Ap (Op Pr) (translation N)) (translation P) 
    | Ref i N => Ap (Ap (Op Var) (nat_comb i)) (translation N)
    | Raise N n k  => Ap (Ap (Ap (Op Rase) (translation N)) (nat_comb n)) (nat_comb k) 
    | Abs j N => Ap (Ap (Op Lam) (nat_comb j))(translation N)
    | App N P => Ap (translation N) (translation P)
  end.




Lemma translation_preserves_seq_red1:
  forall M N, seq_red1 M N -> opred (translation M) (translation N).
Proof.
  intros M N r; induction r; split_all; try (red; one_step;fail); 
  try (inversion H; subst; eapply2 preserves_app_opred; fail). 
  (* 7 *) 
  eapply succ_red. eapply2 raise_var_red.
  eapply2 preserves_app_opred. eapply2 preserves_app_opred. 
  eapply2 discriminate_lt.
  (* 6 *)
  eapply succ_red. eapply2 raise_var_red.
  eapply2 preserves_app_opred. eapply2 preserves_app_opred. 
  assert(i>j \/ i=j) by omega. inversion H0.
  eapply transitive_red. eapply2 discriminate_gt.  eapply2 plus_nat_comb. 
  subst. 
  eapply transitive_red. eapply2 discriminate_eq.
  eapply2 plus_nat_comb. 
  (* 5 *)
  eapply succ_red. eapply2 raise_abs_red. 
  eapply2 preserves_app_opred. eapply2 preserves_app_opred. eapply2 preserves_app_opred. 
   eapply2 preserves_app_opred. eapply2 plus_nat_comb. 
  (* 4 *)
  eapply succ_red. eapply2 lam_var_un_red.
  eapply transitive_red. eapply2 discriminate_lt. 
  eapply2 preserves_app_opred.
  (* 3 *)
  eapply succ_red. eapply2 lam_var_un_red.
  eapply transitive_red. eapply2 discriminate_gt. 
  eapply2 preserves_app_opred.  eapply2 preserves_app_opred. eapply2 pred_nat_comb. 
  (* 2 *)
  eapply succ_red. eapply2 lam_var_un_red.
  eapply transitive_red. eapply2 discriminate_eq. 
  eapply2 preserves_app_opred.
  (* 1 *)
  eapply succ_red. eapply2 lam_lam_red.
  eapply2 preserves_app_opred.  eapply2 preserves_app_opred.  eapply2 preserves_app_opred.
  eapply2 preserves_app_opred. eapply2 preserves_app_opred. eapply2 plus_nat_comb. 
Qed.




Theorem  translation_preserves_seq_red:
  forall M N, seq_red M N -> opred (translation M) (translation N).
Proof.
cut(forall red M N, DLB_Tactics.multi_step red M N -> red = seq_red1 -> 
opred (translation M) (translation N)).
split_all. eapply2 H. 
intros red M N r; induction r; split_all; subst. 
eapply transitive_red. eapply2 translation_preserves_seq_red1. 
eapply2 IHr. 
Qed.





Inductive well_formed_combinator : combinator -> sort -> Prop :=
| wf_un: well_formed_combinator (Op Un) Tuple 
| wf_pr: well_formed_combinator (Op Pr) (Funty Tuple (Funty Term Tuple))
| wf_zero: well_formed_combinator (Op Zero) Index 
| wf_next: well_formed_combinator (Op Next) (Funty Index Index)
| wf_pred: well_formed_combinator (Op Pred) (Funty Index Index)
| wf_plus: well_formed_combinator (Op Plus) (Funty Index (Funty Index Index))
| wf_discriminate: well_formed_combinator (Op Discriminate) 
                     (Funty Index (Funty Index (Funty Term (Funty Term (Funty Term Term)))))
| wf_var: well_formed_combinator (Op Var) (Funty Index (Funty Tuple Term))
| wf_rase_tuple: well_formed_combinator (Op Rase)(Funty Tuple (Funty Index (Funty Index Tuple)))
| wf_rase_term: well_formed_combinator (Op Rase) (Funty Term (Funty Index (Funty Index Term)))
| wf_lam: well_formed_combinator (Op Lam) (Funty Index  (Funty Term Term))
| wf_ap: forall (ty1 ty2:sort) (t u:combinator), well_formed_combinator t (Funty ty1 ty2) -> 
                                                 well_formed_combinator u ty1 -> 
                                                 well_formed_combinator (Ap t u) ty2
| wf_ap2: forall (t u:combinator), well_formed_combinator t Term ->
                                                 well_formed_combinator u Term -> 
                                                 well_formed_combinator (Ap t u) Term
.

Hint Constructors well_formed_combinator.

Lemma nat_comb_is_well_formed: forall i, well_formed_combinator (nat_comb i) Index. 
Proof. induction i; split_all. eapply2 wf_ap. Qed. 

Lemma well_formed_combinator_limit:
  forall t ty0 ty1 ty2 ty3 ty4 ty5 ty6,
    well_formed_combinator t
      (Funty ty0 (Funty ty1 (Funty ty2 (Funty ty3 (Funty ty4 (Funty ty5 ty6)))))) ->
    False.
Proof.  induction t; split_all; inversion H; subst; auto. eapply2 IHt1. Qed. 
  
Lemma seq_red1_preserves_well_formed:
  forall M N, seq_red1 M N -> forall st,  well_formed st M -> well_formed st N. 
Proof. 
split_all. eapply2 (dlb_red1_preserves_well_formed M). eapply2 seq_red1_to_dlb_red1.
Qed. 



Lemma translation_preserves_well_formed: 
forall M st, well_formed st M -> well_formed_combinator (translation M) st. 
Proof. 
induction M; split_all.
(* 6 *) 
inversion H; subst; auto. 
(* 5 *) 
inversion H; subst; auto. eapply wf_ap. eapply wf_ap.  eauto. eapply2 IHM1. eapply2 IHM2. 
(* 4 *) 
inversion H; subst; auto. eapply wf_ap. eapply wf_ap.  2:eapply2 nat_comb_is_well_formed. 
eauto. eapply2 IHM. 
(* 3 *) 
inversion H; subst; auto. 
(* 4 *) 
eapply wf_ap.  eapply wf_ap. 2:eapply2 nat_comb_is_well_formed.
 2:eapply2 nat_comb_is_well_formed. eapply wf_ap. eapply2 wf_rase_tuple. eapply2 IHM. 
(* 3 *) 
eapply wf_ap.  eapply wf_ap. 2:eapply2 nat_comb_is_well_formed.
 2:eapply2 nat_comb_is_well_formed. eapply wf_ap. eapply2 wf_rase_term. eapply2 IHM. 
(* 2 *) 
inversion H; subst; auto. eapply wf_ap. eapply wf_ap. 2:eapply2 nat_comb_is_well_formed.
eauto. eapply2 IHM. 
(* 1 *) 
inversion H; subst; auto. 
Qed. 

(* not completed 
Fixpoint translation_to_lambda (M:combinator) :=
  match M with
    | Op Un => Unit 
    | Ap (Ap (Op Pr) M1) M2 => Pair (translation_to_lambda M1) (translation_to_lambda M2)
    | Op Zero => Ref 0 Unit  (* a hack *) 
    | Ap (Op Next) M1 => 
      match translation_to_lambda M1 with 
          | Ref i _ => Ref (S i) Unit 
          | t => t 
      end
    | Ap (Op Pred) M1 =>
      match translation_to_lambda M1 with 
          | Ref i _ => Ref (pred i) Unit 
          | t => t 
      end
    | Ap (Ap (Op Plus) M1) M2 => 
       match translation_to_lambda M1 with 
          | Ref i1 _ => match translation_to_lambda M2 with 
                          | Ref i2 _ => Ref (i1+i2) Unit 
                          | t => t 
                        end
           | t => t 
      end
    | Ap (Ap (Ap (Ap (Ap (Op Discriminate) M1) M2) M3) M4) M5 => 
      match translation_to_lambda M1 with 
          | Ref i1 _ => match translation_to_lambda M2 with 
                          | Ref i2 _ => 
                            match compare i1 i2 with 
                              (* i1<i2 *) | inleft (left _) => translation_to_lambda M3
                            (* i1 = i2 *) | inleft _ => translation_to_lambda M5
                                (* k>i *) | _ =>  translation_to_lambda M4
                            end 
                          | t => t 
                        end
          | _ => Ref 0 Unit 
      end
    | Ap (Ap (Op Var) i) M1 => match translation_to_lambda i with 
                                 | Ref i1 _ => Ref i1 (translation_to_lambda M1)
                                 | t => t 
                               end
    | Ap (Ap (Ap (Op Rase) M1) j) k => 
       match translation_to_lambda j with 
         | Ref j1 _ => match translation_to_lambda k with 
                         | Ref k1 _ => Raise (translation_to_lambda M1) j1 k1 
                         | t => t 
                       end
         | t => t 
       end
    | Ap (Ap (Op Lam) j) M1 => 
      match translation_to_lambda j with 
         | Ref j1 _ => Abs j1 (translation_to_lambda M1) 
         | t => t 
      end
    | Ap M1 M2 => App (translation_to_lambda M1) (translation_to_lambda M2)
    | t => Unit 
  end
.


Lemma translation_to_lambda_preserves_well_formed: 
forall M st, well_formed_combinator M st -> (st = Tuple -> well_formed st (translation_to_lambda M)) /\ (st = Term -> well_formed st (translation_to_lambda M)).  
Proof. 
intros M st wf; induction wf; intros; try (split_all; fail). 
(* 2 *) 
inversion wf1; subst; try (split_all; fail).   
inversion H; subst; try (split_all; fail). 
(* 5 *) 
split; intro; try discriminate; subst. simpl.  eapply2 wf_pair. eapply2 IHwf2. 
(* 3 *) 
inversion wf1. 
_all. 
(* 12 *) 


Qed. 

*) 