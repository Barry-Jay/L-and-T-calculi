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
(*                        L_Combinators.v                             *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import General.



(* combinators to represent lambda-calculus with tuples *)

Inductive operator : Set := 
Un | Pr | Zero | Next | Pred | Plus | Discriminate | Var | Rase | Lam.  

Inductive combinator:  Set :=
| Op : operator -> combinator
| Ap : combinator -> combinator -> combinator .

Lemma decidable_combinator_equality : forall (M N: combinator), M = N \/ M<> N. 
Proof. 
  induction M; induction N; intros; try (left; congruence); try(right; congruence).
  (* 2 *)
  assert(o = o0 \/ o <> o0).  case o; case o0; try (right; discriminate); try (left;auto). 
  inversion H. subst; left; auto. right; intro; invsub.  
  (* 1 *) 
   elim(IHM1 N1); elim(IHM2 N2); auto; (right; congruence; fail) || left; congruence. 
Qed. 

