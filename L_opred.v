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
(*                       L-Calculus                                   *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                          L_opred.v                                 *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import General.
Require Import L_Combinators.
Require Import L_combinator_tactics.


(* combinator-reduction  *) 


Inductive opred1 : combred :=
  | op_opred : forall o, opred1 (Op o) (Op o)
  | app_opred :
      forall M M' ,
      opred1 M M' ->
      forall N N' : combinator, opred1 N N' -> opred1 (Ap M N) (Ap M' N')
  | plus_zero_red : forall j j', opred1 j j' -> opred1 (Ap (Ap (Op Plus) (Op Zero)) j) j'  
  | plus_next_red: forall i i' j j', opred1 i i' -> opred1 j j' -> 
                                     opred1 (Ap (Ap (Op Plus) (Ap (Op Next) i)) j)
                                            (Ap (Ap (Op Plus) i') (Ap (Op Next) j'))
  | pred_zero_red: opred1 (Ap (Op Pred) (Op Zero)) (Op Zero)
  | pred_next_red: forall i i', opred1 i i' -> opred1 (Ap (Op Pred) (Ap (Op Next) i)) i' 
  | disc_zz_red: forall s t u u', opred1 u u' -> 
     opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (Op Zero)) (Op Zero)) s) t) u) u' 
  | disc_zn_red: forall j s s' t u, opred1 s s' -> 
   opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (Op Zero)) (Ap (Op Next) j)) s) t) u) s'
  | disc_nz_red: forall i s t t' u, opred1 t t' -> 
   opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (Ap (Op Next) i)) (Op Zero)) s) t) u) t'
  | disc_nn_red: forall i i' j j' s s' t t' u u', opred1 i i' -> opred1 j j' -> opred1 s s' -> 
                                            opred1 t t' -> opred1 u u' -> 
   opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate)(Ap (Op Next) i)) (Ap (Op Next) j)) s) t) u) 
          (Ap (Ap (Ap (Ap (Ap (Op Discriminate) i') j') s') t') u') 
  | var_red : forall i i' s s' u u', opred1 i i' -> opred1 s s' -> opred1 u u' -> 
            opred1(Ap (Ap (Ap (Op Var) i) s) u) 
                  (Ap (Ap (Op Var) i') (Ap (Ap (Op Pr) s') u'))
  | raise_un_red: forall j k, opred1 (Ap (Ap (Ap (Op Rase) (Op Un)) j) k) (Op Un)
  | raise_pair_red:  forall j j' k k' s s' t t', opred1 j j' -> 
                                  opred1 k k' -> opred1 s s' -> opred1 t t' -> 
                                  opred1 (Ap (Ap (Ap (Op Rase)(Ap (Ap (Op Pr) s) t)) j) k)
                                         (Ap (Ap (Op Pr) (Ap (Ap (Ap (Op Rase) s') j') k'))
                                             (Ap (Ap (Ap (Op Rase) t') j') k'))
  | raise_var_red : forall i i' j j' k k' s s' ,  opred1 i i' -> opred1 j j' -> 
                                  opred1 k k' -> opred1 s s' -> 
         opred1 (Ap (Ap (Ap (Op Rase) (Ap (Ap (Op Var) i) s)) j) k)
                (Ap (Ap (Op Var) (Ap (Ap (Ap (Ap (Ap (Op Discriminate) i') k') i') 
                                         (Ap (Ap (Op Plus) i') j'))
                                     (Ap (Ap (Op Plus) i') j')))
                    (Ap (Ap (Ap (Op Rase) s') j') k'))
  | raise_abs_red : forall i i' t t' j j' k k', opred1 i i' -> opred1 t t' -> 
                                                opred1 j j' -> opred1 k k' -> 
                     opred1 (Ap (Ap (Ap (Op Rase) (Ap (Ap (Op Lam) i) t)) j) k)
                            (Ap (Ap (Op Lam) i') 
                                (Ap (Ap (Ap (Op Rase) t') (Ap (Op Next) (Ap (Ap (Op Plus) i') j'))) k'))
  | lam_var_un_red : forall j j' i i' u u', opred1 j j' -> opred1 i i' -> opred1 u u' -> 
                        opred1 (Ap(Ap(Ap(Op Lam) j) (Ap (Ap (Op Var) i) (Op Un))) u)
                               (Ap (Ap (Ap (Ap (Ap (Op Discriminate) i') j') 
                                           (Ap (Ap (Op Var) i') (Op Un)))
                                       (Ap (Ap (Op Var) (Ap (Op Pred) i')) (Op Un)))
                                   (Ap (Ap (Ap (Op Rase) u') (Op Zero)) j'))
  | lam_var_pr_red : forall j j' i i' s s' t t' u u', opred1 j j' -> opred1 i i' -> 
                                      opred1 s s' -> opred1 t t' -> opred1 u u' -> 
               opred1 (Ap(Ap(Ap(Op Lam) j) (Ap (Ap (Op Var) i) (Ap (Ap (Op Pr) s) t))) u) 
                      (Ap(Ap(Ap(Ap(Op Lam) j') (Ap (Ap (Op Var) i') s')) u')
                           (Ap(Ap(Ap(Op Lam) j') t') u'))
  | lam_lam_red : forall j j' i i' t t' u u' , opred1 j j' -> opred1 i i' -> 
                         opred1 t t' -> opred1 u u' -> 
                        opred1 (Ap (Ap (Ap (Op Lam) j) (Ap (Ap (Op Lam) i) t)) u) 
                               (Ap (Ap (Op Lam) i') (Ap (Ap (Ap (Op Lam) 
                                                                (Ap (Op Next) (Ap (Ap (Op Plus) i') j')))
                                                            t') u'))
.


         
Hint Constructors opred1. 



Definition opred := multi_step opred1. 

Lemma reflective_opred1 : reflective opred1.
Proof. red; induction M; split_all. Qed. 
Hint Resolve reflective_opred1. 

Lemma reflective_opred : reflective opred.
Proof. unfold opred; eapply2 refl_multi_step. Qed. 
Hint Resolve reflective_opred. 



Lemma preserves_app_opred : preserves_app opred.
Proof. eapply2 preserves_app_multi_step. red; split_all. Qed.
Hint Resolve  preserves_app_opred. 


(* Diamond Lemmas *) 


Lemma diamond0_opred1_opred1 : diamond0 opred1 opred1. 
Proof.  
red;intros M N OR; induction OR; split_all; eauto; inv opred1; eauto. 
(* 40 *) 
elim(IHOR1 M'0); elim(IHOR2 N'0); split_all. eauto.
(* 39 *) 
inv opred1. elim(IHOR2 P); split_all; eauto. 
(* 38 *) 
inv opred1. elim(IHOR1 (Ap (Op Plus) (Ap (Op Next) i'))); elim(IHOR2 j'); split_all. 
inv opred1. invsub. exist(Ap (Ap (Op Plus) N'2)(Ap (Op Next) x)) . 
(* 37 *) 
inv opred1. eauto. 
(* 36 *) 
inv opred1. elim(IHOR2 (Ap (Op Next) P)); split_all; inv opred1; invsub; eauto. 
(* 35 *) 
inv opred1. elim(IHOR2 P); split_all; eauto. 
(* 34 *) 
inv opred1. elim(IHOR1 (Ap (Ap (Ap (Ap (Op Discriminate) (Op Zero)) (Ap (Op Next) N'3)) P)
               N'0)); split_all.
inv opred1.   invsub. eauto. 
(* 33 *) 
inv opred1. elim(IHOR1 (Ap (Ap (Ap (Ap (Op Discriminate) (Ap (Op Next) N'4)) (Op Zero)) N'1)
               P)); split_all.
inv opred1.   invsub. eauto. auto 10. 
(* 32 *) 
inv opred1. elim(IHOR1 (Ap (Ap (Ap (Ap (Op Discriminate) (Ap (Op Next) i')) (Ap (Op Next) j')) s')
               t')); split_all.
elim(IHOR2 u'); split_all. 
inv opred1.   invsub. exist (Ap (Ap (Ap (Ap (Ap (Op Discriminate) N'9) N'7) N'4) N'2) x0).
auto 10. auto 10. 
(* 31 *) 
inv opred1. elim(IHOR2 u');elim(IHOR1(Ap (Ap (Op Var) i') s')); split_all. 
inv opred1; invsub; eauto. 
exist(Ap (Ap (Op Var) N'3) (Ap (Ap (Op Pr) N'2)  x0)).
(* 30 *) 
inv opred1. eauto. 
(* 29 *) 
inv opred1. 
elim(IHOR2 k');elim(IHOR1(Ap (Ap (Op Rase) (Ap (Ap (Op Pr) s') t')) j')); split_all. 
inv opred1; invsub; eauto. 
exist (Ap (Ap (Op Pr) (Ap (Ap (Ap (Op Rase) N'6) N'1) x0))
          (Ap (Ap (Ap (Op Rase) N'5) N'1) x0)). 
auto 10. 
(* 28 *) 
inv opred1. 
elim(IHOR2 k');elim(IHOR1(Ap (Ap (Op Rase) (Ap (Ap (Op Var) i') s')) j')); split_all. 
inv opred1; invsub; eauto. 
exist (Ap
          (Ap (Op Var)
             (Ap
                (Ap (Ap (Ap (Ap (Op Discriminate) N'6) x0) N'6)
                    (Ap (Ap (Op Plus) N'6) N'1)) 
                (Ap (Ap (Op Plus) N'6) N'1)))
       (Ap (Ap (Ap (Op Rase) N'5) N'1) x0)).
auto 10. 
(* 27 *) 
inv opred1. 
elim(IHOR2 k');
elim(IHOR1(Ap (Ap (Op Rase) (Ap (Ap (Op Lam) i') t')) j')); split_all. 
inv opred1; invsub; eauto. 
exist (Ap (Ap (Op Lam) N'6) (Ap (Ap (Ap (Op Rase) N'5) (Ap (Op Next) (Ap (Ap (Op Plus) N'6) N'1))) x0)) .
auto 10. 
(* 26 *) 
inv opred1. 
elim(IHOR2 u');
elim(IHOR1(Ap (Ap (Op Lam) j') (Ap (Ap (Op Var) i') (Op Un)))); split_all. 
inv opred1; invsub; eauto. 
exist (Ap
          (Ap
             (Ap (Ap (Ap (Op Discriminate) N'4) N'5)
                (Ap (Ap (Op Var) N'4) (Op Un)))
             (Ap (Ap (Op Var) (Ap (Op Pred) N'4)) (Op Un)))
          (Ap (Ap (Ap (Op Rase) x0) (Op Zero)) N'5)).
auto 10. 
(* 25 *) 
inv opred1. 
elim(IHOR2 u');
elim(IHOR1(Ap (Ap (Op Lam) j') (Ap (Ap (Op Var) i') (Ap (Ap (Op Pr) s') t')))); split_all. 
inv opred1; invsub; eauto. 
exist (Ap (Ap (Ap (Ap (Op Lam) N'9) (Ap (Ap (Op Var) N'8) N'7)) x0)
          (Ap (Ap (Ap (Op Lam) N'9) N'6) x0)).
auto 10. 
(* 24 *) 
inv opred1. 
elim(IHOR2 u');
elim(IHOR1(Ap (Ap (Op Lam) j') (Ap (Ap (Op Lam) i') t'))); split_all. 
inv opred1; invsub; eauto. 
exist (Ap (Ap (Op Lam) N'5)
          (Ap (Ap (Ap (Op Lam) (Ap (Op Next) (Ap (Ap (Op Plus) N'5) N'6))) N'4) x0)).
auto 10. 
(* 23 *) 
elim(IHOR N'); split_all.  eauto. 
(* 22 *) 
elim(IHOR1 N'1); elim(IHOR2 N'); split_all. exist (Ap (Ap (Op Plus) x0) (Ap (Op Next) x)).   
(* 21 *) 
elim(IHOR1 i'0); elim(IHOR2 j'0); split_all. exist (Ap (Ap (Op Plus) x0) (Ap (Op Next) x)).   
(* 20 *) 
elim(IHOR N'0); split_all.  eauto. 
(* 19 *) 
elim(IHOR N'); split_all.  eauto. 
(* 18 *) 
elim(IHOR N'1); split_all; eauto. 
(* 17 *) 
elim(IHOR N'0); split_all; eauto. 
(* 16 *) 
elim(IHOR1 N'5); elim(IHOR2 N'3); elim(IHOR3 N'1); elim(IHOR4 N'0); elim(IHOR5 N'); split_all.
exist(Ap (Ap (Ap (Ap (Ap (Op Discriminate) x3) x2) x1) x0) x).
auto 10. 
(* 15 *) 
elim(IHOR1 i'0); elim(IHOR2 j'0); elim(IHOR3 s'0); elim(IHOR4 t'0); elim(IHOR5 u'0); split_all.
exist(Ap (Ap (Ap (Ap (Ap (Op Discriminate) x3) x2) x1) x0) x).
auto 10. auto 10. 
(* 14 *) 
elim(IHOR1 N'1); elim(IHOR2 N'0); elim(IHOR3 N'); split_all. 
exist(Ap (Ap (Op Var) x1) (Ap (Ap (Op Pr) x0) x)). 
(* 13 *) 
elim(IHOR1 i'0); elim(IHOR2 s'0); elim(IHOR3 u'0); split_all. 
exist(Ap (Ap (Op Var) x1) (Ap (Ap (Op Pr) x0) x)). 
(* 12 *) 
elim(IHOR1 N'0); elim(IHOR2 N'); elim(IHOR3 N'3); elim(IHOR4 N'2); split_all. 
exist (Ap (Ap (Op Pr) (Ap (Ap (Ap (Op Rase) x0) x2) x1))
          (Ap (Ap (Ap (Op Rase) x) x2) x1)). 
auto 10. 
(* 11 *) 
elim(IHOR1 j'0); elim(IHOR2 k'0); elim(IHOR3 s'0); elim(IHOR4 t'0); split_all. 
exist (Ap (Ap (Op Pr) (Ap (Ap (Ap (Op Rase) x0) x2) x1))
          (Ap (Ap (Ap (Op Rase) x) x2) x1)); 
auto 10. 
(* 10 *) 
elim(IHOR1 N'3); elim(IHOR2 N'0); elim(IHOR3 N'); elim(IHOR4 N'2); split_all. 
exist  (Ap
          (Ap (Op Var)
             (Ap
                (Ap (Ap (Ap (Ap (Op Discriminate) x2) x0) x2)
                   (Ap (Ap (Op Plus) x2) x1)) (Ap (Ap (Op Plus) x2) x1)))
          (Ap (Ap (Ap (Op Rase) x) x1) x0)).
auto 10. 
(* 9 *) 
elim(IHOR1 i'0); elim(IHOR2 j'0); elim(IHOR3 k'0); elim(IHOR4 s'0); split_all. 
exist  (Ap
          (Ap (Op Var)
             (Ap
                (Ap (Ap (Ap (Ap (Op Discriminate) x2) x0) x2)
                   (Ap (Ap (Op Plus) x2) x1)) (Ap (Ap (Op Plus) x2) x1)))
          (Ap (Ap (Ap (Op Rase) x) x1) x0));
auto 10. 
(* 8 *) 
elim(IHOR1 N'3); elim(IHOR2 N'2); elim(IHOR3 N'0); elim(IHOR4 N'); split_all. 
exist(Ap (Ap (Op Lam) x2)
          (Ap (Ap (Ap (Op Rase) x1) (Ap (Op Next) (Ap (Ap (Op Plus) x2) x0))) x)).
auto 10.
(* 7 *) 
elim(IHOR1 i'0); elim(IHOR2 t'0); elim(IHOR3 j'0); elim(IHOR4 k'0); split_all.
exist(Ap (Ap (Op Lam) x2)
          (Ap (Ap (Ap (Op Rase) x1) (Ap (Op Next) (Ap (Ap (Op Plus) x2) x0))) x)).
auto 10. auto 10.
(* 6 *) 
elim(IHOR1 N'3); elim(IHOR2 N'2); elim(IHOR3 N'); split_all.
exist(Ap
          (Ap
             (Ap (Ap (Ap (Op Discriminate) x0) x1)
                (Ap (Ap (Op Var) x0) (Op Un)))
             (Ap (Ap (Op Var) (Ap (Op Pred) x0)) (Op Un)))
          (Ap (Ap (Ap (Op Rase) x) (Op Zero)) x1)). 
auto 10. 
(* 5 *) 
elim(IHOR1 j'0); elim(IHOR2 i'0); elim(IHOR3 u'0); split_all.
exist(Ap
          (Ap
             (Ap (Ap (Ap (Op Discriminate) x0) x1)
                (Ap (Ap (Op Var) x0) (Op Un)))
             (Ap (Ap (Op Var) (Ap (Op Pred) x0)) (Op Un)))
          (Ap (Ap (Ap (Op Rase) x) (Op Zero)) x1)). 
auto 10. auto 10. 
(* 4 *) 
elim(IHOR1 N'5); elim(IHOR2 N'4); elim(IHOR3 N'3); elim(IHOR4 N'2); elim(IHOR5 N'); split_all.
exist(Ap (Ap (Ap (Ap (Op Lam) x3) (Ap (Ap (Op Var) x2) x1)) x)
          (Ap (Ap (Ap (Op Lam) x3) x0) x)).
auto 10. 
(* 3 *) 
elim(IHOR1 j'0); elim(IHOR2 i'0); elim(IHOR3 s'0); elim(IHOR4 t'0); elim(IHOR5 u'0); split_all.
exist(Ap (Ap (Ap (Ap (Op Lam) x3) (Ap (Ap (Op Var) x2) x1)) x)
          (Ap (Ap (Ap (Op Lam) x3) x0) x)).
auto 10. auto 10. 
(* 2 *) 
elim(IHOR1 N'3); elim(IHOR2 N'2); elim(IHOR3 N'1); elim(IHOR4 N'); split_all.
exist(Ap (Ap (Op Lam) x1)
          (Ap (Ap (Ap (Op Lam) (Ap (Op Next) (Ap (Ap (Op Plus) x1) x2))) x0) x)).
auto 10.
(* 7 *) 
elim(IHOR1 j'0); elim(IHOR2 i'0); elim(IHOR3 t'0); elim(IHOR4 u'0); split_all.
exist(Ap (Ap (Op Lam) x1)
          (Ap (Ap (Ap (Op Lam) (Ap (Op Next) (Ap (Ap (Op Plus) x1) x2))) x0) x)).
auto 10. auto 10.
Qed.

Hint Resolve diamond0_opred1_opred1.

Lemma diamond0_opred1_opred : diamond0 opred1 opred.
Proof. eapply2 diamond0_strip. Qed. 

Lemma diamond0_opred : diamond0 opred opred.
Proof.  eapply2 diamond0_tiling. Qed. 
Hint Resolve diamond0_opred.


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem combinator_confluence: confluence combinator opred. 
Proof. red. eapply2 diamond0_tiling.  Qed. 


(* combinator-sequential-reduction *) 

Inductive seq_opred1 : combinator -> combinator -> Prop := 
  | appl_seq_opred :  forall M M' N, seq_opred1 M M' -> 
                                      seq_opred1 (Ap M N) (Ap M' N)  
  | appr_seq_opred :  forall M N N', seq_opred1 N N' -> 
                                      seq_opred1 (Ap M N) (Ap M N')  
  | plus_zero_seqred : forall j, seq_opred1 (Ap (Ap (Op Plus) (Op Zero)) j) j  
  | plus_next_seqred: forall i j, 
                                     seq_opred1 (Ap (Ap (Op Plus) (Ap (Op Next) i)) j)
                                            (Ap (Ap (Op Plus) i) (Ap (Op Next) j))
  | pred_zero_seqred: seq_opred1 (Ap (Op Pred) (Op Zero)) (Op Zero)
  | pred_next_seqred: forall i, seq_opred1 (Ap (Op Pred) (Ap (Op Next) i)) i 
  | disc_zz_seqred: forall s t u , 
     seq_opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (Op Zero)) (Op Zero)) s) t) u) u 
  | disc_zn_seqred: forall j s t u, 
   seq_opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (Op Zero)) (Ap (Op Next) j)) s) t) u) s
  | disc_nz_seqred: forall i s t u, 
   seq_opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate) (Ap (Op Next) i)) (Op Zero)) s) t) u) t
  | disc_nn_seqred: forall i j s t u, 
   seq_opred1 (Ap (Ap (Ap (Ap (Ap (Op Discriminate)(Ap (Op Next) i)) (Ap (Op Next) j)) s) t) u) 
          (Ap (Ap (Ap (Ap (Ap (Op Discriminate) i) j) s) t) u) 
  | var_seqred : forall i s u, 
            seq_opred1(Ap (Ap (Ap (Op Var) i) s) u) 
                  (Ap (Ap (Op Var) i) (Ap (Ap (Op Pr) s) u))
  | raise_un_seqred: forall j k, seq_opred1 (Ap (Ap (Ap (Op Rase) (Op Un)) j) k) (Op Un)
  | raise_pair_seqred:  forall j k s t, 
                                  seq_opred1 (Ap (Ap (Ap (Op Rase)(Ap (Ap (Op Pr) s) t)) j) k)
                                         (Ap (Ap (Op Pr) (Ap (Ap (Ap (Op Rase) s) j) k))
                                             (Ap (Ap (Ap (Op Rase) t) j) k))
  | raise_var_seqred : forall i j k s , 
         seq_opred1 (Ap (Ap (Ap (Op Rase) (Ap (Ap (Op Var) i) s)) j) k)
                (Ap (Ap (Op Var) (Ap (Ap (Ap (Ap (Ap (Op Discriminate) i) k) i) 
                                         (Ap (Ap (Op Plus) i) j))
                                     (Ap (Ap (Op Plus) i) j)))
                    (Ap (Ap (Ap (Op Rase) s) j) k))
  | raise_abs_seqred : forall i t j k,
                     seq_opred1 (Ap (Ap (Ap (Op Rase) (Ap (Ap (Op Lam) i) t)) j) k)
                            (Ap (Ap (Op Lam) i) 
                                (Ap (Ap (Ap (Op Rase) t) (Ap (Op Next) (Ap (Ap (Op Plus) i) j))) k))
  | lam_var_un_seqred : forall j i u, 
                        seq_opred1 (Ap(Ap(Ap(Op Lam) j) (Ap (Ap (Op Var) i) (Op Un))) u)
                               (Ap (Ap (Ap (Ap (Ap (Op Discriminate) i) j) 
                                           (Ap (Ap (Op Var) i) (Op Un)))
                                       (Ap (Ap (Op Var) (Ap (Op Pred) i)) (Op Un)))
                                   (Ap (Ap (Ap (Op Rase) u) (Op Zero)) j))
  | lam_var_pr_seqred : forall j i s t u,
               seq_opred1 (Ap(Ap(Ap(Op Lam) j) (Ap (Ap (Op Var) i) (Ap (Ap (Op Pr) s) t))) u) 
                      (Ap(Ap(Ap(Ap(Op Lam) j) (Ap (Ap (Op Var) i) s)) u)
                           (Ap(Ap(Ap(Op Lam) j) t) u))
  | lam_lam_seqred : forall j i t u,
                        seq_opred1 (Ap (Ap (Ap (Op Lam) j) (Ap (Ap (Op Lam) i) t)) u) 
                               (Ap (Ap (Op Lam) i) (Ap (Ap (Ap (Op Lam) 
                                                               (Ap (Op Next) (Ap (Ap (Op Plus) i) j)))
                                                            t) u))
.


Definition seq_opred := multi_step seq_opred1. 

Hint Constructors seq_opred1 .


Lemma reflective_seq_opred: reflective seq_opred. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_seq_opred.


Definition preserves_apl (red : combred) := 
forall M M' N, red M M' -> red (Ap M N) (Ap M' N).

Definition preserves_apr (red : combred) := 
forall M N N', red N N' -> red (Ap M N) (Ap M N').

Lemma preserves_apl_multi_step : forall (red: combred), preserves_apl red -> preserves_apl (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (Ap N0 N); auto. Qed. 

Lemma preserves_apr_multi_step : forall (red: combred), preserves_apr red -> preserves_apr (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (Ap M N); auto. Qed. 


Lemma preserves_apl_seq_opred: preserves_apl seq_opred. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_seq_opred.

Lemma preserves_apr_seq_opred: preserves_apr seq_opred. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_seq_opred.

Lemma preserves_app_seq_opred: preserves_app seq_opred. 
Proof. 
red; split_all. 
apply transitive_red with (Ap M' N); split_all. 
eapply2 preserves_apl_seq_opred. 
eapply2 preserves_apr_seq_opred. 
Qed. 
Hint Resolve preserves_app_seq_opred.


Lemma seq_opred1_to_opred1 : implies_red seq_opred1 opred1. 
Proof. red. intros M N B; induction B; split_all.  Qed. 


Lemma seq_opred_to_opred: implies_red seq_opred opred. 
Proof. 
eapply2 implies_red_multi_step. 
red; split_all; one_step; eapply2 seq_opred1_to_opred1. 
Qed. 

Lemma to_seq_opred_multi_step: forall red, implies_red red seq_opred -> implies_red (multi_step red) seq_opred. 
Proof. 
red.  intros red B M N R; induction R; split_all.
red; split_all. 
assert(seq_opred M N) by eapply2 B. 
apply transitive_red with N; auto. 
eapply2 IHR. 
Qed. 


Lemma opred1_to_seq_opred: implies_red opred1 seq_opred .
Proof. 
red.  intros M N OR; induction OR; split_all; eapply succ_red; 
auto; repeat eapply2 preserves_app_seq_opred. auto. 
Qed. 

Hint Resolve opred1_to_seq_opred.

Lemma opred_to_seq_opred: implies_red opred seq_opred. 
Proof. eapply2 to_seq_opred_multi_step. Qed.


Lemma diamond_seq_opred: diamond seq_opred seq_opred. 
Proof. 
red; split_all. 
assert(opred M N) by eapply2 seq_opred_to_opred.  
assert(opred M P) by eapply2 seq_opred_to_opred.  
elim(diamond0_opred M N H1 P); split_all. 
exist x; eapply2 opred_to_seq_opred. 
Qed. 
Hint Resolve diamond_seq_opred. 

Theorem abstraction_combinator_confluence: confluence combinator seq_opred. 
Proof. red. split_all. eapply2 diamond_seq_opred.  Qed. 

