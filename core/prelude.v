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
From mathcomp Require Import ssrnat seq eqtype choice fintype.
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

Lemma trans_eq A (x y z : A) : x = y -> x = z -> y = z.
Proof. by move/esym; apply: eq_trans. Qed.

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

(*************)
(* sequences *)
(*************)

(* TODO upstream to mathcomp *)
Section Fold.

Lemma map_foldr {T1 T2} (f : T1 -> T2) xs :
  map f xs = foldr (fun x ys => f x :: ys) [::] xs.
Proof. by []. Qed.

Lemma fusion_foldr {T R Q} (g : R -> Q) f0 f1 z0 z1 (xs : seq T) :
  (forall x y, g (f0 x y) = f1 x (g y)) -> g z0 = z1 ->
  g (foldr f0 z0 xs) = foldr f1 z1 xs.
Proof. by move=>Hf Hz; elim: xs=>//= x xs <-. Qed.

Lemma fusion_foldl {T R Q} (g : R -> Q) f0 f1 z0 z1 (xs : seq T) :
  (forall x y, g (f0 x y) = f1 (g x) y) -> g z0 = z1 ->
  g (foldl f0 z0 xs) = foldl f1 z1 xs.
Proof.
move=>Hf Hz; elim: xs z0 z1 Hz =>//= x xs IH z0 z1 Hz.
by apply: IH; rewrite Hf Hz.
Qed.

Lemma foldl_foldr {T R} (f : R -> T -> R) z xs :
  foldl f z xs = foldr (fun b g x => g (f x b)) id xs z.
Proof. by elim: xs z=>/=. Qed.

Lemma foldr_foldl {T R} (f : T -> R -> R) z xs :
  foldr f z xs = foldl (fun g b x => g (f b x)) id xs z.
Proof.
elim/last_ind: xs z=>//= xs x IH z.
by rewrite foldl_rcons -IH foldr_rcons.
Qed.

End Fold.

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

Lemma onth_sizeN s : onth s (size s) = None.
Proof. by apply/size_onthPn. Qed.

Lemma nth_onth x0 n s : nth x0 s n = odflt x0 (onth s n).
Proof.
elim: s n=>/= [|a s IH] n /=; first by apply: nth_nil.
by case: n.
Qed.

Lemma onth_nth x0 n s : n < size s -> onth s n = Some (nth x0 s n).
Proof.
elim: s n=>//= a s IH n.
by rewrite ltnS; case: n.
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

Lemma onth_mem (A : eqType) (s : seq A) n x :
        onth s n = Some x ->
        x \in s.
Proof.
by elim: s n=>//= a s IH [[->]|n /IH]; rewrite inE ?eq_refl // orbC =>->.
Qed.

Lemma onth_index (A : eqType) (s : seq A) x :
        onth s (index x s) = if x \in s then Some x else None.
Proof.
by elim: s=>//=h s IH; rewrite inE eq_sym; case: eqP=>//= ->.
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
