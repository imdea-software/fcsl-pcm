(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

(******************************************************************************)
(* This file is Prelude -- often used notation definitions and lemmas that    *)
(* are not included in the other libraries.                                   *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun Eqdep.
From mathcomp Require Import ssrnat seq choice fintype eqtype.
From pcm Require Import options axioms.

(***********)
(* Prelude *)
(***********)

(* often used notation definitions and lemmas that are *)
(* not included in the other libraries *)

(* export inj_pair without exporting the whole Eqdep library *)
Definition inj_pair2 := @inj_pair2.
Arguments inj_pair2 [U P p x y] _.
Prenex Implicits inj_pair2.

(* Because of a bug in inversion and injection tactics *)
(* we occasionally have to destruct pair by hand, else we *)
(* lose the second equation. *)
Lemma inj_pair A B (a1 a2 : A) (b1 b2 : B) :
         (a1, b1) = (a2, b2) -> (a1 = a2) * (b1 = b2).
Proof. by case. Qed.
Arguments inj_pair [A B a1 a2 b1 b2].
Prenex Implicits inj_pair.

(* eta laws for pairs and units *)
Notation prod_eta := surjective_pairing.

(* eta law often used with injection *)
Lemma prod_inj A B (x y : A * B) : x = y <-> (x.1, x.2) = (y.1, y.2).
Proof. by case: x y=>x1 x2 []. Qed.

Lemma idfunE (U : Type) (x : U) : idfun x = x.
Proof. by []. Qed.

(* idfun is a left and right unit for composition *)
Lemma idfun0E (U V : Type) (f : U -> V):
        (idfun \o f = f) * (f \o idfun = f).
Proof. by []. Qed.

(* Triples *)
Section TripleLemmas.
Variables (A B C : Type).
Implicit Types (a : A) (b : B) (c : C).

Lemma t1P a1 a2 b1 b2 c1 c2 : (a1, b1, c1) = (a2, b2, c2) -> a1 = a2.
Proof. by case. Qed.

Lemma t2P a1 a2 b1 b2 c1 c2 : (a1, b1, c1) = (a2, b2, c2) -> b1 = b2.
Proof. by case. Qed.

Lemma t3P a1 a2 b1 b2 c1 c2 : (a1, b1, c1) = (a2, b2, c2) -> c1 = c2.
Proof. by case. Qed.

Lemma t12P a1 a2 b1 b2 c1 c2 : (a1, b1, c1) = (a2, b2, c2) -> (a1 = a2) * (b1 = b2).
Proof. by case. Qed.

Lemma t13P a1 a2 b1 b2 c1 c2 : (a1, b1, c1) = (a2, b2, c2) -> (a1 = a2) * (c1 = c2).
Proof. by case. Qed.

Lemma t23P a1 a2 b1 b2 c1 c2 : (a1, b1, c1) = (a2, b2, c2) -> (b1 = b2) * (c1 = c2).
Proof. by case. Qed.

End TripleLemmas.
Prenex Implicits t1P t2P t3P t12P t13P t23P.

(***************************)
(* operations on functions *)
(***************************)

Lemma eta A (B : A -> Type) (f : forall x, B x) : f = [eta f].
Proof. by []. Qed.

Lemma ext A (B : A -> Type) (f1 f2 : forall x, B x) :
        f1 = f2 -> forall x, f1 x = f2 x.
Proof. by move=>->. Qed.

Lemma compA A B C D (h : A -> B) (g : B -> C) (f : C -> D) :
        (f \o g) \o h = f \o (g \o h).
Proof. by []. Qed.

Definition fprod A1 A2 B1 B2 (f1 : A1 -> B1) (f2 : A2 -> B2) :=
  fun (x : A1 * A2) => (f1 x.1, f2 x.2).

Notation "f1 \* f2" := (fprod f1 f2) (at level 42, left associativity) : fun_scope.

(* product morphism, a.k.a. fork or fanout or fsplice *)
Definition pmorphism A B1 B2 (f1 : A -> B1) (f2 : A -> B2) :=
  fun x : A => (f1 x, f2 x).
Arguments pmorphism {A B1 B2} f1 f2 x /.
Notation "f1 \** f2 " := (pmorphism f1 f2)
  (at level 50, left associativity, format "f1  \** '/ '  f2") : fun_scope.

(* product with functions *)
Lemma prod_feta (A B : Type) : @idfun (A * B) = fst \** snd.
Proof. by apply: fext=>x; rewrite /pmorphism -prod_eta. Qed.

Reserved Notation "[ ** f1 & f2 ]" (at level 0).
Reserved Notation "[ ** f1 , f2 & f3 ]" (at level 0, format
  "'[hv' [ ** '['  f1 , '/'  f2 ']' '/ '  &  f3 ] ']'").
Reserved Notation "[ ** f1 , f2 , f3 & f4 ]" (at level 0, format
  "'[hv' [ ** '['  f1 , '/'  f2 , '/'  f3 ']' '/ '  &  f4 ] ']'").
Reserved Notation "[ ** f1 , f2 , f3 , f4 & f5 ]"  (at level 0, format
  "'[hv' [ ** '['  f1 , '/'  f2 , '/'  f3 , '/'  f4 ']' '/ '  &  f5 ] ']'").

Notation "[ ** f1 & f2 ]" := (f1 \** f2) (only parsing) : fun_scope.
Notation "[ ** f1 , f2 & f3 ]" := ((f1 \** f2) \** f3) : fun_scope.
Notation "[ ** f1 , f2 , f3 & f4 ]" := (((f1 \** f2) \** f3) \** f4) : fun_scope.
Notation "[ ** f1 , f2 , f3 , f4 & f5 ]" := ((((f1 \** f2) \** f3) \** f4) \** f5) : fun_scope.

(* composing relation and function *)

Definition relfuncomp A B (D : rel A) (f : B -> A) : rel B :=
  fun x y => D (f x) (f y).

Notation "D \\o f" := (@relfuncomp _ _ D f) (at level 42, left associativity).

(************************)
(* extension to ssrbool *)
(************************)

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 ']' '/ '  &  P7 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 ']' '/ '  &  P7 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 ']' '/ '  &  P8 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 ']' '/ '  &  P9 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/' P9 ']' '/ '  &  P10 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/' P9 , '/' P10 ']' '/ '  &  P11 ] ']'").

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 & P12 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/' P9 , '/' P10 , '/' P11 ']' '/ '  &  P12 ] ']'").


Reserved Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  |  P5 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  |  P6 ] ']'").

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.
Inductive and7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Inductive and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Prop) : Prop :=
  And8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Inductive and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Inductive and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop) : Prop :=
  And10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.
Inductive and11 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 : Prop) : Prop :=
  And11 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11.
Inductive and12 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 : Prop) : Prop :=
  And12 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12.

Inductive or5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  Or51 of P1 | Or52 of P2 | Or53 of P3 | Or54 of P4 | Or55 of P5.
Inductive or6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  Or61 of P1 | Or62 of P2 | Or63 of P3 | Or64 of P4 | Or65 of P5 | Or66 of P6.
Inductive or7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  Or71 of P1 | Or72 of P2 | Or73 of P3 | Or74 of P4 | Or75 of P5 | Or76 of P6 | Or77 of P7.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" :=
  (and11 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 & P12 ]" :=
  (and12 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12) : type_scope.

Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" := (or5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" := (or6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 , P6 | P7 ]" := (or7 P1 P2 P3 P4 P5 P6 P7) : type_scope.

(** Add the ability to rewrite with [<->] for the custom logical connectives *)

From Coq Require Import Classes.Morphisms Program.Basics Program.Tactics.
From Coq Require Import Relations.

Local Obligation Tactic := try solve [simpl_relation | firstorder auto].

Definition iter_arrow_type (n : nat) (A : Type) := iter n (fun T => A -> T).

Fixpoint iter_respectful {S T} (A : relation S) (Z : relation T) (n : nat)
  : relation (iter_arrow_type n S T) :=
  if n is n'.+1 then respectful A (@iter_respectful _ _ A Z n')
  else Z.
Arguments iter_respectful {S T} A Z n.

(** Logical conjunction *)
#[export] Program Instance and3_impl_morphism : Proper (iter_respectful impl impl 3) and3 | 1.
#[export] Program Instance and3_iff_morphism : Proper (iter_respectful iff iff 3) and3 | 1.

#[export] Program Instance and4_impl_morphism : Proper (iter_respectful impl impl 4) and4 | 1.
#[export] Program Instance and4_iff_morphism : Proper (iter_respectful iff iff 4) and4 | 1.

#[export] Program Instance and5_impl_morphism : Proper (iter_respectful impl impl 5) and5 | 1.
#[export] Program Instance and5_iff_morphism : Proper (iter_respectful iff iff 5) and5 | 1.

#[export] Program Instance and6_impl_morphism : Proper (iter_respectful impl impl 6) and6 | 1.
#[export] Program Instance and6_iff_morphism : Proper (iter_respectful iff iff 6) and6 | 1.

#[export] Program Instance and7_impl_morphism : Proper (iter_respectful impl impl 7) and7 | 1.
#[export] Program Instance and7_iff_morphism : Proper (iter_respectful iff iff 7) and7 | 1.

#[export] Program Instance and8_impl_morphism : Proper (iter_respectful impl impl 8) and8 | 1.
#[export] Program Instance and8_iff_morphism : Proper (iter_respectful iff iff 8) and8 | 1.

#[export] Program Instance and9_impl_morphism : Proper (iter_respectful impl impl 9) and9 | 1.
#[export] Program Instance and9_iff_morphism : Proper (iter_respectful iff iff 9) and9 | 1.

#[export] Program Instance and10_impl_morphism : Proper (iter_respectful impl impl 10) and10 | 1.
#[export] Program Instance and10_iff_morphism : Proper (iter_respectful iff iff 10) and10 | 1.

#[export] Program Instance and11_impl_morphism : Proper (iter_respectful impl impl 11) and11 | 1.
#[export] Program Instance and11_iff_morphism : Proper (iter_respectful iff iff 11) and11 | 1.

#[export] Program Instance and12_impl_morphism : Proper (iter_respectful impl impl 12) and12 | 1.
#[export] Program Instance and12_iff_morphism : Proper (iter_respectful iff iff 12) and12 | 1.

(** Logical disjunction *)
#[export] Program Instance or3_impl_morphism : Proper (iter_respectful impl impl 3) or3 | 1.
#[export] Program Instance or3_iff_morphism : Proper (iter_respectful iff iff 3) or3 | 1.

#[export] Program Instance or4_impl_morphism : Proper (iter_respectful impl impl 4) or4 | 1.
#[export] Program Instance or4_iff_morphism : Proper (iter_respectful iff iff 4) or4 | 1.

#[export] Program Instance or5_impl_morphism : Proper (iter_respectful impl impl 5) or5 | 1.
#[export] Program Instance or5_iff_morphism : Proper (iter_respectful iff iff 5) or5 | 1.

#[export] Program Instance or6_impl_morphism : Proper (iter_respectful impl impl 6) or6 | 1.
#[export] Program Instance or6_iff_morphism : Proper (iter_respectful iff iff 6) or6 | 1.

#[export] Program Instance or7_impl_morphism : Proper (iter_respectful impl impl 7) or7 | 1.
#[export] Program Instance or7_iff_morphism : Proper (iter_respectful iff iff 7) or7 | 1.


Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and7P : reflect [/\ b1, b2, b3, b4, b5, b6 & b7] [&& b1, b2, b3, b4, b5, b6 & b7].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and8P : reflect [/\ b1, b2, b3, b4, b5, b6, b7 & b8] [&& b1, b2, b3, b4, b5, b6, b7 & b8].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and9P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8 & b9] [&& b1, b2, b3, b4, b5, b6, b7, b8 & b9].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and10P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10] [&& b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and11P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and12P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
by constructor.
Qed.

Lemma or5P : reflect [\/ b1, b2, b3, b4 | b5] [|| b1, b2, b3, b4 | b5].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
by constructor; case.
Qed.

Lemma or6P : reflect [\/ b1, b2, b3, b4, b5 | b6] [|| b1, b2, b3, b4, b5 | b6].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
by constructor; case.
Qed.

Lemma or7P : reflect [\/ b1, b2, b3, b4, b5, b6 | b7] [|| b1, b2, b3, b4, b5, b6 | b7].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
case b7; first by constructor; constructor 7.
by constructor; case.
Qed.

End ReflectConnectives.

Arguments and6P {b1 b2 b3 b4 b5 b6}.
Arguments and7P {b1 b2 b3 b4 b5 b6 b7}.
Arguments and8P {b1 b2 b3 b4 b5 b6 b7 b8}.
Arguments and9P {b1 b2 b3 b4 b5 b6 b7 b8 b9}.
Arguments and10P {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10}.
Arguments and11P {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11}.
Arguments and12P {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12}.

Arguments or5P {b1 b2 b3 b4 b5}.
Arguments or6P {b1 b2 b3 b4 b5 b6}.
Arguments or7P {b1 b2 b3 b4 b5 b6 b7}.
Prenex Implicits and6P and7P or5P or6P or7P.

Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof. by case: a; case: b; constructor=>//; case. Qed.

Arguments andX {a b}.

Lemma iffPb (b1 b2 : bool) : reflect (b1 <-> b2) (b1 == b2).
Proof.
case: eqP=>[->|N]; constructor=>//.
case: b1 b2 N; case=>//= _.
- by case=>/(_ erefl).
by case=>_ /(_ erefl).
Qed.

Lemma iffE (b1 b2 : bool) : b1 = b2 <-> (b1 <-> b2).
Proof. by split=>[->|] //; move/iffPb/eqP. Qed.

(**************)
(* empty type *)
(**************)

Lemma false_eqP : Equality.axiom (fun _ _ : False => true).
Proof. by case. Qed.

Definition false_EqMixin := EqMixin false_eqP.
Canonical false_EqType := Eval hnf in EqType False false_EqMixin.

(*************)
(* sum types *)
(*************)

Section InvertingSumTags.
Variables A B : Type.

Definition lft : A + B -> option A :=
  fun x => if x is inl x' then Some x' else None.
Definition rgt : A + B -> option B :=
  fun x => if x is inr x' then Some x' else None.

Lemma lft_inl_ocanc : ocancel lft inl. Proof. by case. Qed.
Lemma rgt_inr_ocanc : ocancel rgt inr. Proof. by case. Qed.
Lemma inl_lft_pcanc : pcancel inl lft. Proof. by []. Qed.
Lemma inr_rgt_pcanc : pcancel inr rgt. Proof. by []. Qed.

End InvertingSumTags.

Prenex Implicits lft rgt.

#[export]
Hint Extern 0 (ocancel _ _) =>
 (apply: lft_inl_ocanc || apply: rgt_inr_ocanc) : core.

(********)
(* nats *)
(********)

Lemma gt0 m n : m < n -> 0 < n.
Proof. by case: n. Qed.

Lemma neq0 m n : m < n -> n != 0.
Proof. by move/gt0; rewrite lt0n. Qed.

Lemma neqSn n : n.+1 != n.
Proof. by elim: n. Qed.

Lemma neqnS n : n != n.+1.
Proof. by elim: n. Qed.

(*************************************)
(* A copy of booleans with mnemonics *)
(* LL and RR for working with sides  *)
(*************************************)

Inductive Side := LL | RR.
Definition Side_eq x y :=
  match x, y with LL, LL => true | RR, RR => true | _, _ => false end.
Lemma Side_eqP : Equality.axiom Side_eq.
Proof. by case; case; constructor. Qed.
Definition Side_EqMix := EqMixin Side_eqP.
Canonical Side_EqType := Eval hnf in EqType Side Side_EqMix.
Definition nat2Side x := if odd x then LL else RR.
Definition Side2nat x := if x is RR then 0 else 1.
Lemma ssrcanc : ssrfun.cancel Side2nat nat2Side. Proof. by case. Qed.
Definition Side_choiceMixin := CanChoiceMixin ssrcanc.
Canonical Side_choiceType := Eval hnf in ChoiceType Side Side_choiceMixin.
Definition Side_countMixin := CanCountMixin ssrcanc.
Canonical Side_countType := Eval hnf in CountType Side Side_countMixin.
Lemma Side_enumP : Finite.axiom [:: LL; RR]. Proof. by case. Qed.
Definition Side_finMixin := Eval hnf in FinMixin Side_enumP.
Canonical Side_finType := Eval hnf in FinType Side Side_finMixin.

Section FindLast.

Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

(* helper function for finding the last occurrence in a single pass *)
(* calculates index and size *)
Definition find_last_aux oi0 p s : option nat * nat :=
  foldl (fun '(o,i) x => (if p x then Some i else o, i.+1)) oi0 s.

Lemma find_last_auxE oi0 p s :
        find_last_aux oi0 p s =
        let k := seq.find p (rev s) in
        (if k == size s then oi0.1
           else Some (oi0.2 + (size s - k).-1), oi0.2 + size s).
Proof.
rewrite /find_last_aux; elim: s oi0=>/= [|x s IH] [o0 i0] /=; first by rewrite addn0.
rewrite IH /= rev_cons -cats1 find_cat /= has_find.
move: (find_size p (rev s)); rewrite size_rev; case: ltngtP=>// H _.
- case: eqP=>[E|_]; first by rewrite E ltnNge leqnSn in H.
  apply: injective_projections=>/=; [congr Some | rewrite addSnnS]=>//.
  by rewrite !predn_sub /= -predn_sub addSnnS prednK // subn_gt0.
case: ifP=>_; rewrite addSnnS; last by rewrite addn1 eqxx.
by rewrite addn0 eqn_leq leqnSn /= ltnn subSnn addn0.
Qed.

Definition find_last p s : nat :=
  let '(o, i) := find_last_aux (None, 0) p s in odflt i o.

(* finding last is finding first in reversed list and flipping indices *)
Corollary find_lastE p s :
            find_last p s =
            if has p s then (size s - seq.find p (rev s)).-1
                       else size s.
Proof.
rewrite /find_last find_last_auxE /= !add0n -has_rev; case/boolP: (has p (rev s)).
- by rewrite has_find size_rev; case: ltngtP.
by move/hasNfind=>->; rewrite size_rev eqxx.
Qed.

Lemma find_last_size p s : find_last p s <= size s.
Proof.
rewrite find_lastE; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_find_last p s : has p s = (find_last p s < size s).
Proof.
symmetry; rewrite find_lastE; case: ifP=>H /=; last by rewrite ltnn.
by rewrite -subnS /= ltn_subrL /=; case: s H.
Qed.

Lemma hasNfind_last p s : ~~ has p s -> find_last p s = size s.
Proof. by rewrite has_find_last; case: ltngtP (find_last_size p s). Qed.

Lemma find_last0 p x : find_last p [::] = 0.
Proof. by []. Qed.

Lemma find_last1 p x : find_last p [::x] = ~~ p x.
Proof. by rewrite find_lastE /= orbF; case: ifP=>// ->. Qed.

Lemma find_last_cat p s1 s2 :
        find_last p (s1 ++ s2) =
        if has p s1 && ~~ has p s2
          then find_last p s1
          else size s1 + find_last p s2.
Proof.
rewrite !find_lastE has_cat rev_cat find_cat has_rev size_cat size_rev.
case/boolP: (has p s2)=>H2; last first.
- rewrite orbF; case/boolP: (has p s1)=>//= H1.
  by rewrite addnC subnDl.
have H2' : find p (rev s2) < size s2.
- by rewrite -size_rev -has_find has_rev.
rewrite /= orbT andbF -addnBA; last by apply: ltnW.
rewrite -!subn1 -subnDA -addnBA; last by rewrite subn_gt0.
by rewrite subnDA.
Qed.

Lemma find_last_cons p x s :
        find_last p (x::s) =
        if p x && ~~ has p s then 0 else (find_last p s).+1.
Proof.
rewrite -cat1s find_last_cat /= !add1n orbF find_last1.
by case: ifP=>// /andP [->].
Qed.

Lemma find_last_rcons p x s :
        find_last p (rcons s x) =
        if p x then size s
          else if has p s then find_last p s
                          else (size s).+1.
Proof.
rewrite -cats1 find_last_cat /= orbF find_last1.
case: (p x)=>/=; first by rewrite andbF addn0.
by rewrite andbT addn1.
Qed.

Lemma nth_find_last x0 p s : has p s -> p (nth x0 s (find_last p s)).
Proof.
rewrite find_lastE=>/[dup] E ->; rewrite -has_rev in E.
rewrite -subnS -nth_rev; last by rewrite -size_rev -has_find.
by apply: nth_find.
Qed.

Lemma has_drop p s i : has p s -> has p (drop i s) = (i <= find_last p s).
Proof.
rewrite find_lastE=>/[dup] E ->; rewrite -has_rev in E.
have Hh: 0 < size s - find p (rev s).
- by rewrite -size_rev subn_gt0 -has_find.
rewrite -size_rev; move/(has_take (size s - i)): (E).
rewrite take_rev -subnS size_rev.
case/boolP: (i < size s)=>[Hi|].
- rewrite subnA //; last by apply: ltnW.
  rewrite subnn add0n has_rev=>->.
  rewrite ltn_subRL addnC -ltn_subRL subnS.
  by case: (size s - find p (rev s)) Hh.
rewrite -ltnNge ltnS => Hi _.
rewrite drop_oversize //=; symmetry; apply/negbTE.
rewrite -ltnNge subnS prednK //.
by apply/leq_trans/Hi; exact: leq_subr.
Qed.

Lemma find_geq p s i : has p (drop i s) -> i <= find_last p s.
Proof.
case/boolP: (has p s)=>Hp; first by rewrite (has_drop _ Hp).
suff: ~~ has p (drop i s) by move/negbTE=>->.
move: Hp; apply: contra; rewrite -{2}(cat_take_drop i s) has_cat=>->.
by rewrite orbT.
Qed.

Variant split_find_last_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindLastNth x s1 s2 of p x & ~~ has p s2 :
    split_find_last_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_find_last_nth x0 p s (i := find_last p s) :
        has p s ->
        split_find_last_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
move=> p_s; rewrite -[X in split_find_last_nth_spec _ X](cat_take_drop i s).
rewrite (drop_nth x0 _); last by rewrite -has_find_last.
rewrite -cat_rcons; constructor; first by apply: nth_find_last.
by rewrite has_drop // ltnn.
Qed.

Variant split_find_last_spec p : seq T -> seq T -> seq T -> Type :=
  FindLastSplit x s1 s2 of p x & ~~ has p s2 :
    split_find_last_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_find_last p s (i := find_last p s) :
        has p s ->
        split_find_last_spec p s (take i s) (drop i.+1 s).
Proof.
by case: s => // x ? in i * =>?; case: split_find_last_nth=>//; constructor.
Qed.

End FindLast.

Section FindLastEq.

Variables (T : eqType).
Implicit Type p : seq T.

Definition index_last (x : T) : seq T -> nat := find_last (pred1 x).

Lemma index_last_size x s : index_last x s <= size s.
Proof. by rewrite /index_last; apply: find_last_size. Qed.

Lemma index_last_mem x s : (index_last x s < size s) = (x \in s).
Proof. by rewrite /index_last -has_find_last has_pred1. Qed.

Lemma memNindex_last x s : x \notin s -> index_last x s = size s.
Proof. by rewrite -has_pred1=>/hasNfind_last. Qed.

Lemma index_last0 x : index_last x [::] = 0.
Proof. by []. Qed.

Lemma index_last1 x y : index_last x [::y] = (x != y).
Proof. by rewrite /index_last find_last1 /= eq_sym. Qed.

Lemma index_last_cat x s1 s2 :
        index_last x (s1 ++ s2) =
        if (x \in s1) && (x \notin s2)
          then index_last x s1
          else size s1 + index_last x s2.
Proof. by rewrite /index_last find_last_cat !has_pred1. Qed.

Lemma index_last_cons x y s :
        index_last x (y::s) =
        if (x == y) && (x \notin s) then 0 else (index_last x s).+1.
Proof. by rewrite /index_last find_last_cons has_pred1 eq_sym. Qed.

Lemma index_last_rcons x y s :
        index_last x (rcons s y) =
        if x == y then size s
          else if x \in s then index_last x s
                          else (size s).+1.
Proof. by rewrite /index_last find_last_rcons has_pred1 eq_sym. Qed.

Lemma index_geq x s i : x \in drop i s -> i <= index_last x s.
Proof. by rewrite -has_pred1; apply: find_geq. Qed.

Lemma index_last_count x s : count_mem x s <= 1 -> index_last x s = index x s.
Proof.
move=>H; case/boolP: (x \in s)=>Hx; last first.
- by rewrite (memNindex_last Hx) (memNindex Hx).
elim: s x H Hx=>//= h t IH x; rewrite eq_sym index_last_cons inE.
case: eqP=>/=?; last by rewrite add0n=> H1 H2; rewrite IH.
by rewrite -{2}(addn0 1%N) leq_add2l leqn0 =>/eqP /count_memPn ->.
Qed.

Corollary index_last_uniq x s : uniq s -> index_last x s = index x s.
Proof.
move=>H; apply: index_last_count.
by rewrite count_uniq_mem //; apply: leq_b1.
Qed.

Variant splitLast x : seq T -> seq T -> seq T -> Type :=
  SplitLast p1 p2 of x \notin p2 : splitLast x (rcons p1 x ++ p2) p1 p2.

Lemma splitLastP s x (i := index_last x s) :
        x \in s ->
        splitLast x s (take i s) (drop i.+1 s).
Proof.
case: s => // y s in i * => H.
case: split_find_last_nth=>//; first by rewrite has_pred1.
move=>_ s1 s2 /= /eqP->; rewrite has_pred1 => H2.
by constructor.
Qed.

End FindLastEq.

(* sequence prefixes *)

(* Two helper concepts for searching in sequences:                       *)
(*                                                                       *)
(* - onth: like nth, but returns None when the element is not found      *)
(* - prefix: a prefix relation on sequences, used for growing            *)
(*   interpretation contexts                                             *)

Section SeqPrefix.
Variable A : Type.

Fixpoint onth (s : seq A) n : option A :=
  if s is x::sx then if n is nx.+1 then onth sx nx else Some x else None.

Definition prefix s1 s2 : Prop :=
  forall n x, onth s1 n = some x -> onth s2 n = some x.

(* Lemmas *)

Variant onth_spec s n : bool -> Type :=
| onth_none   : onth s n = None   -> onth_spec s n false
| onth_some v : onth s n = Some v -> onth_spec s n true.

Lemma onth_sizeP s n : onth_spec s n (n < size s).
Proof.
elim: s n=>/= [|a s IH] n; first by rewrite ltn0; constructor.
case: n=>[|n] /=; first by apply: (@onth_some _ _ a).
rewrite ltnS; case: (IH n)=>[|v] H.
- by constructor.
by apply: (@onth_some _ _ v).
Qed.

Lemma size_onth s n : n < size s -> exists x, onth s n = Some x.
Proof.
by case: onth_sizeP=>// v H _; exists v.
Qed.

Lemma onth_size s n x : onth s n = Some x -> n < size s.
Proof.
by case: onth_sizeP=>//->.
Qed.

Lemma size_onthPn s n : reflect (onth s n = None) (size s <= n).
Proof.
by rewrite leqNgt; apply: (iffP idP); case: onth_sizeP=>//= v ->.
Qed.

Lemma nth_onth x0 n s : nth x0 s n = odflt x0 (onth s n).
Proof.
elim: s n=>/= [|a s IH] n /=; first by apply: nth_nil.
by case: n.
Qed.

Lemma prefix_refl s : prefix s s.
Proof. by move=>n x <-. Qed.

Lemma prefix_trans s2 s1 s3 : prefix s1 s2 -> prefix s2 s3 -> prefix s1 s3.
Proof. by move=>H1 H2 n x E; apply: H2; apply: H1. Qed.

Lemma prefix_cons x s1 s2 : prefix (x :: s1) (x :: s2) <-> prefix s1 s2.
Proof. by split=>E n; [apply: (E n.+1) | case: n]. Qed.

Lemma prefix_cons' x y s1 s2 :
        prefix (x :: s1) (y :: s2) -> x = y /\ prefix s1 s2.
Proof. by move=>H; case: (H 0 x (erefl _)) (H)=>-> /prefix_cons. Qed.

Lemma prefix_rcons x s : prefix s (rcons s x).
Proof. by elim: s=>//= y ys IH; apply/prefix_cons; apply: IH. Qed.

Lemma prefix_cat s1 s2 : prefix s1 (s1 ++ s2).
Proof.
elim: s2 s1=>[|x xs IH] s1; first by rewrite cats0.
rewrite -cat_rcons; apply: prefix_trans (IH _).
by apply: prefix_rcons.
Qed.

Lemma prefix_size s1 s2 : prefix s1 s2 -> size s1 <= size s2.
Proof.
elim: s1 s2=>[//|a s1 IH] [|b s2] H; first by move: (H 0 a (erefl _)).
by rewrite ltnS; apply: (IH _ (proj2 (prefix_cons' H))).
Qed.

Lemma prefix_onth s t x : x < size s -> prefix s t -> onth s x = onth t x.
Proof.
elim:s t x =>[//|a s IH] [|b t] x H1 H2; first by move: (H2 0 a (erefl _)).
by case/prefix_cons': H2=><- H2; case: x H1=>[|n] //= H1; apply: IH.
Qed.

Lemma prefixE s1 s2 : prefix s1 s2 <-> exists s3, s2 = s1 ++ s3.
Proof.
split; last by case=>s3 ->; apply: prefix_cat.
elim: s1 s2=>[|x xs IH] s2; first by exists s2.
case: s2=>[/(_ 0 x erefl)//|y ys /prefix_cons' [?]].
by subst y=>/IH [s3 ->]; exists s3.
Qed.

End SeqPrefix.

#[export]
Hint Resolve prefix_refl : core.

Lemma onth_mem (A : eqType) (s : seq A) n x : onth s n = Some x -> x \in s.
Proof.
by elim: s n=>//= a s IH [[->]|n /IH]; rewrite inE ?eq_refl // orbC => ->.
Qed.

Lemma prefixP (A : eqType) (s1 s2 : seq A) :
        reflect (prefix s1 s2) (seq.prefix s1 s2).
Proof.
apply/(equivP (seq.prefixP (s1:=s1) (s2:=s2))).
by apply: iff_sym; exact: prefixE.
Qed.

(******************************)
(* Some commuting conversions *)
(******************************)

Lemma fun_op A B C (b : option A) (vS : A -> B) (vN : B)  (f : B -> C) :
        f (if b is Some v then vS v else vN) =
        if b is Some v then f (vS v) else f vN.
Proof. by case: b=>//. Qed.

Lemma op_if A B (b : bool) (vS vN : option A)  (vS1 : A -> B) (vN1 : B) :
        (if (if b then vS else vN) is Some v then vS1 v else vN1) =
        if b then if vS is Some v then vS1 v else vN1
        else if vN is Some v then vS1 v else vN1.
Proof. by case: b. Qed.


(*************************************************************)
(* quick ways to extract projections and transitivity proofs *)
(* out of iterated inequalities                              *)
(*************************************************************)

Lemma ltn13 a b c : a < b < c -> a < c.
Proof. by case/andP; apply: ltn_trans. Qed.

Lemma ltn12 a b c : a < b < c -> a < b.
Proof. by case/andP. Qed.

Lemma ltn23 a b c : a < b < c -> b < c.
Proof. by case/andP. Qed.

Lemma leq13 a b c : a <= b <= c -> a <= c.
Proof. by case/andP; apply: leq_trans. Qed.

Lemma leq12 a b c : a <= b <= c -> a <= b.
Proof. by case/andP. Qed.

Lemma leq23 a b c : a <= b <= c -> b <= c.
Proof. by case/andP. Qed.

Lemma lqt13 a b c : a <= b < c -> a < c.
Proof. by case/andP; apply: leq_ltn_trans. Qed.

Lemma lqt12 a b c : a <= b < c -> a <= b.
Proof. by case/andP. Qed.

Lemma lqt23 a b c : a <= b < c -> b < c.
Proof. by case/andP. Qed.

(*******************)
(* Finite products *)
(*******************)

(* It's easy to define finite (aka. tagged) products as functions *)
(* but this requires assuming function extensionality. *)
(* Here, we define finite products somewhat more cheaply *)
(* without extensionality, though with proof irrelevance. *)

Fixpoint FinProd' A (T : A -> Type) (xs : seq A) : Type :=
  if xs is x :: xs' then prod (T x) (FinProd' T xs') else unit.

Fixpoint finprod' A (T : A -> Type) (xs : seq A)
                  (fs : forall x, T x) : FinProd' T xs :=
  if xs is x :: xs' then (fs x, finprod' xs' fs) else tt.

Section FinProdEqType.
Variables (A : eqType) (T : A -> Type).

Lemma mem_nil (a : A) : a \in [::] -> T a.
Proof. by []. Qed.

Lemma mem_cdr (a x : A) (xs : seq A) : a \in x :: xs -> a <> x -> a \in xs.
Proof. by rewrite inE; case/orP=>// /eqP ->. Qed.

Fixpoint sel' (a : A) (xs : seq A) :=
  if xs is x :: xs' as xs return a \in xs -> FinProd' T xs -> T a then
    fun pf '(f, fs) =>
      match decP (a =P x) with
        left eqf => cast T eqf f
      | right neqf => sel' a xs' (mem_cdr pf neqf) fs
      end
  else fun pf _ => mem_nil pf.

Lemma finprod_beta' (f : forall x, T x) a xs :
        forall pf : a \in xs, sel' pf (finprod' xs f) = f a.
Proof.
by elim: xs=>[|x xs IH] //= pf; case: decP=>// {}pf; subst x; rewrite eqc.
Qed.

Lemma finprod_ext' (xs : seq A) (fs1 fs2 : FinProd' T xs) :
        uniq xs ->
        fs1 = fs2 <-> forall a (pf : a \in xs), sel' pf fs1 = sel' pf fs2.
Proof.
move=>U; split=>[->|] //.
elim: xs U fs1 fs2=>[_ [][]//|x xs IH /= /andP [Ux U][f1 fs1][f2 fs2] H].
case: decP (H x)=>// eqf; rewrite !eqc => ->; last by rewrite inE eq_refl.
rewrite (IH U fs1 fs2) // => a pf.
have N : a <> x by move=>E; rewrite -E pf in Ux.
have xpf : a \in x :: xs by rewrite inE pf orbT.
case: decP (H a xpf)=>// qf; move: {qf} (mem_cdr _ _)=>qf.
by rewrite (pf_irr pf qf).
Qed.

End FinProdEqType.

(* Now we instaniate the helper defs with a finite type *)

Section FinProd.
Variables (A : finType) (T : A -> Type).

Definition FinProd := FinProd' T (enum A).
Definition finprod (f : forall x, T x) : FinProd := finprod' (enum A) f.
Definition sel (a : A) (fs : FinProd) := sel' (mem_enum A a) fs.

(* beta equality *)
Lemma sel_fin f a : sel a (finprod f) = f a.
Proof. by rewrite /sel finprod_beta'. Qed.

(* extensionality *)
Lemma fin_ext (fs1 fs2 : FinProd) :
        (forall a, sel a fs1 = sel a fs2) -> fs1 = fs2.
Proof.
move=>H; rewrite (finprod_ext' _ _ (enum_uniq _))=>a pf.
by move: (H a); rewrite /sel (pf_irr (mem_enum _ _) pf).
Qed.

(* eta equality *)
Lemma fin_eta (fs : FinProd) : fs = finprod (sel^~ fs).
Proof. by apply: fin_ext=>a; rewrite sel_fin. Qed.

End FinProd.

(* Splicing a value into a given tag *)

Section Splice.
Variables (A : finType) (T : A -> Type).

Definition splice (fs : FinProd T) (a : A) (ta : T a) :=
  finprod (fun t =>
    if decP (t =P a) is left pf then cast T pf ta else sel t fs).

Lemma sel_spliceE fs a ta : sel a (splice fs ta) = ta.
Proof. by rewrite sel_fin; case: decP=>// pf; rewrite eqc. Qed.

Lemma sel_spliceN fs a b (tb : T b) :
        a <> b -> sel a (splice fs tb) = sel a fs.
Proof. by move=>N; rewrite sel_fin; case: decP. Qed.

Lemma splice_eta fs a : splice fs (sel a fs) = fs.
Proof.
apply: fin_ext=>x; rewrite sel_fin.
by case: decP=>// ?; subst x; rewrite eqc.
Qed.

End Splice.

Arguments splice [A T] fs a ta.

(* Special notation for boolean predicates over K*V *)

Notation "[ 'pts' k v | E ]" :=
 (fun kv => let '(k, v) := kv in E%B)
 (at level 0, k name, v name, format "[ 'pts'  k  v  |  E ]").
Notation "[ 'pts' k ( v : V ) | E ]" :=
 (fun kv : _*V =>let '(k, v) := kv in E%B)
 (at level 0, k name, v name, only parsing).
Notation "[ 'pts' ( k : K ) v | E ]" :=
 (fun kv : K*_ => let '(k, v) := kv in E%B)
 (at level 0, k name, v name, only parsing).
Notation "[ 'pts' ( k : K ) ( v : V ) | E ]" :=
 (fun kv : K*V => let '(k, v) := kv in E%B)
 (at level 0, k name, v name, only parsing).
