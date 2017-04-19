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
(*               Delayed Substitution Lambda Calculus                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                        Tuple_Terms.v                               *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import General.



(* lambda terms using de Bruijn's indices *)

Inductive lambda:  Set :=
| Unit  : lambda
| Pair: lambda -> lambda -> lambda
| Ref : nat -> lambda -> lambda 
| Raise: lambda -> nat -> nat -> lambda 
| Abs : nat -> lambda -> lambda  
| App : lambda -> lambda -> lambda .



Lemma decidable_term_equality : forall (M N: lambda), M = N \/ M<> N. 
Proof. 
  induction M; induction N; intros; try (left; congruence); try(right; congruence).
  (* 5 *) 
  elim(IHM1 N1); elim(IHM2 N2); auto; (right; congruence; fail) || left; congruence. 
  (* 4 *)
  elim(decidable_nats n0 n); auto. elim(IHM N); split_all. left; congruence. right; congruence. 
  right; congruence. 
  (* 3 *)
  elim(decidable_nats n1 n); auto. elim(decidable_nats n0 n2); auto. 
  elim(IHM N); split_all. left; congruence. right; congruence. 
  right; congruence.  right; congruence.
  (* 2 *)
  elim(IHM N); split_all.  elim(decidable_nats n0 n); auto. left; congruence. 
  right; congruence.  right; congruence.
  (* 1 *)
   elim(IHM1 N1); elim(IHM2 N2); auto; (right; congruence; fail) || left; congruence. 
Qed. 


