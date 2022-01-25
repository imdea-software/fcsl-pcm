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
From mathcomp Require Import ssrnat seq choice fintype eqtype path.
From fcsl Require Import axioms.
From fcsl Require Import options.

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
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 '/' ,  P9 ']' '/ '  &  P10 ] ']'").


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
Program Instance and3_impl_morphism : Proper (iter_respectful impl impl 3) and3 | 1.
Program Instance and3_iff_morphism : Proper (iter_respectful iff iff 3) and3 | 1.

Program Instance and4_impl_morphism : Proper (iter_respectful impl impl 4) and4 | 1.
Program Instance and4_iff_morphism : Proper (iter_respectful iff iff 4) and4 | 1.

Program Instance and5_impl_morphism : Proper (iter_respectful impl impl 5) and5 | 1.
Program Instance and5_iff_morphism : Proper (iter_respectful iff iff 5) and5 | 1.

Program Instance and6_impl_morphism : Proper (iter_respectful impl impl 6) and6 | 1.
Program Instance and6_iff_morphism : Proper (iter_respectful iff iff 6) and6 | 1.

Program Instance and7_impl_morphism : Proper (iter_respectful impl impl 7) and7 | 1.
Program Instance and7_iff_morphism : Proper (iter_respectful iff iff 7) and7 | 1.

Program Instance and8_impl_morphism : Proper (iter_respectful impl impl 8) and8 | 1.
Program Instance and8_iff_morphism : Proper (iter_respectful iff iff 8) and8 | 1.

Program Instance and9_impl_morphism : Proper (iter_respectful impl impl 9) and9 | 1.
Program Instance and9_iff_morphism : Proper (iter_respectful iff iff 9) and9 | 1.

Program Instance and10_impl_morphism : Proper (iter_respectful impl impl 10) and10 | 1.
Program Instance and10_iff_morphism : Proper (iter_respectful iff iff 10) and10 | 1.

(** Logical disjunction *)
Program Instance or3_impl_morphism : Proper (iter_respectful impl impl 3) or3 | 1.
Program Instance or3_iff_morphism : Proper (iter_respectful iff iff 3) or3 | 1.

Program Instance or4_impl_morphism : Proper (iter_respectful impl impl 4) or4 | 1.
Program Instance or4_iff_morphism : Proper (iter_respectful iff iff 4) or4 | 1.

Program Instance or5_impl_morphism : Proper (iter_respectful impl impl 5) or5 | 1.
Program Instance or5_iff_morphism : Proper (iter_respectful iff iff 5) or5 | 1.

Program Instance or6_impl_morphism : Proper (iter_respectful impl impl 6) or6 | 1.
Program Instance or6_iff_morphism : Proper (iter_respectful iff iff 6) or6 | 1.

Program Instance or7_impl_morphism : Proper (iter_respectful impl impl 7) or7 | 1.
Program Instance or7_iff_morphism : Proper (iter_respectful iff iff 7) or7 | 1.


Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; constructor; try by case.
Qed.

Lemma and7P : reflect [/\ b1, b2, b3, b4, b5, b6 & b7] [&& b1, b2, b3, b4, b5, b6 & b7].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; case: b7; constructor; try by case.
Qed.

Lemma and8P : reflect [/\ b1, b2, b3, b4, b5, b6, b7 & b8] [&& b1, b2, b3, b4, b5, b6, b7 & b8].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; case: b7; case: b8; constructor; try by case.
Qed.

Lemma and9P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8 & b9] [&& b1, b2, b3, b4, b5, b6, b7, b8 & b9].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; case: b7; case: b8; case: b9; constructor; try by case.
Qed.

Lemma and10P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10] [&& b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6;
   case: b7; case: b8; case: b9; case: b10; constructor; try by case.
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

Arguments or5P {b1 b2 b3 b4 b5}.
Arguments or6P {b1 b2 b3 b4 b5 b6}.
Arguments or7P {b1 b2 b3 b4 b5 b6 b7}.
Prenex Implicits and6P and7P or5P or6P or7P.

Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof. by case: a; case: b; constructor=>//; case. Qed.

Arguments andX {a b}.

(********************)
(* extension to seq *)
(********************)

Lemma all_mem (A : eqType) (s1 s2 : seq A) :
        reflect {subset s2 <= s1} (all [mem s1] s2).
Proof. by case: allP=>H; constructor; [move=>x /H | move=>X; apply: H=>x /X]. Qed.

Lemma all_predC_sym (A : eqType) (s1 s2 : seq A) :
        all [predC s1] s2 = all [predC s2] s1.
Proof. by rewrite all_predC has_sym -all_predC. Qed.

Lemma nilp_hasPn A (s : seq A) : nilp s = ~~ has predT s.
Proof. by case: s. Qed.

Lemma index_rcons (A : eqType) (a x : A) xs :
        index a (rcons xs x) =
        if a \in xs then index a xs else
          if a == x then size xs else (size xs).+1.
Proof.
rewrite eq_sym; elim: xs=>[|y xs IH] //=.
rewrite inE eq_sym; case: eqP=>//= _.
by rewrite IH; case: ifP=>// _; case: eqP.
Qed.

Lemma index_memN (A : eqType) (x : A) xs :
        x \notin xs -> index x xs = size xs.
Proof.
rewrite -index_mem -ltnNge ltnS.
by case: ltngtP (index_size x xs).
Qed.

Lemma size0nilP (A : eqType) (xs : seq A) :
        reflect (xs = [::]) (size xs == 0).
Proof.
case: eqP=>X; constructor; first by move/size0nil: X.
by move=>N; rewrite N in X.
Qed.

Lemma has_nilP (A : eqType) (xs : seq A) :
        reflect (has predT xs) (xs != [::]).
Proof. by case: xs=>[|x xs]; constructor. Qed.

Lemma map_nilP A (B : eqType) (f : A -> B) (s : seq A) :
        reflect (exists k, k \in map f s) (map f s != [::]).
Proof.
case: has_nilP=>X; constructor.
- by case/hasP: X=>x; exists x.
by case=>k K; elim: X; apply/hasP; exists k.
Qed.

Lemma filter_nilP (A : eqType) (p : pred A) (s : seq A) :
        reflect (forall x, p x -> x \in s -> false)
                ([seq x <- s | p x] == [::]).
Proof.
case: eqP=>E; constructor.
- move=>x H1 H2; suff : x \in [seq x <- s | p x] by rewrite E.
  by rewrite mem_filter H1 H2.
move=>H; apply: E; apply: size0nil; apply/eqP; rewrite size_filter.
by rewrite eqn0Ngt -has_count; apply/hasPn=>x /H; case: (p x)=>//; apply.
Qed.

Lemma filter_mem_sym (A : eqType) (s1 s2 : seq A) :
        filter (mem s1) s2 =i filter (mem s2) s1.
Proof. by move=>x; rewrite !mem_filter andbC. Qed.

Lemma filter_swap A (s : seq A) p1 p2 :
        filter p1 (filter p2 s) = filter p2 (filter p1 s).
Proof. by rewrite -!filter_predI; apply eq_filter=>z /=; rewrite andbC. Qed.

Lemma filter_predIC A (s : seq A) p1 p2 :
         filter (predI p1 p2) s = filter (predI p2 p1) s.
Proof. by rewrite filter_predI filter_swap -filter_predI. Qed.

Lemma filter_predC1 (A : eqType) (x : A) (s : seq A) :
        x \notin s -> filter (predC1 x) s = s.
Proof.
by move=>H; apply/all_filterP/allP=>y /=; case: eqP=>// ->; apply/contraL.
Qed.

Lemma index_inj (A : eqType) (s : seq A) (x y : A) :
        x \in s -> index x s = index y s -> x = y.
Proof.
elim: s=>[|k s IH] //=; rewrite inE eq_sym.
by case: eqP=>[->{k} _|_ /= S]; case: eqP=>// _ []; apply: IH S.
Qed.


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

(*****************************************)
(* Some basic subset properties on lists *)
(*****************************************)

Lemma subset_nilR (A : eqType) (xs : seq A) :
        {subset xs <= [::]} -> xs = [::].
Proof. by case: xs=>// x xs /(_ x); rewrite inE eq_refl=>/(_ erefl). Qed.

Lemma subset_nil (A : eqType) (xs ys : seq A) :
        {subset xs <= ys} -> ys = [::] -> xs = [::].
Proof. by move=>X E; move: E X=>->; apply: subset_nilR. Qed.

(*****************)
(* filter + last *)
(*****************)

Section LastFilter.
Variables (A : eqType).

(* if s has an element, last returns one of them *)
Lemma last_in x k (s : seq A) : x \in s -> last k s \in s.
Proof.
elim: s k=>[|k s IH] k' //=; rewrite !inE.
case/orP=>[/eqP <-|/IH ->]; first by apply: mem_last.
by rewrite orbT.
Qed.

Arguments last_in x [k s].

Lemma last_notin x k (s : seq A) : x \in s -> k \notin s -> last k s != k.
Proof. by move/(last_in _ (k:=k))=>H /negbTE; case: eqP H=>// ->->. Qed.

(* last either returns a default, or one of s's elements *)
Lemma last_change k (s : seq A) : last k s != k -> last k s \in s.
Proof. by move: (mem_last k s); rewrite inE; case: eqP. Qed.

Lemma last_changeE1 k (s : seq A) :
        last k s != k -> forall x, last x s = last k s.
Proof. by elim: s k=>[|k s IH] y //=; rewrite eq_refl. Qed.

Lemma last_changeE2 k (s : seq A) :
        last k s != k -> forall x, x \notin s -> last x s != x.
Proof. by move/last_change/last_notin. Qed.

(* common formats of last_change *)
Lemma last_nochange k (s : seq A) : last k s = k -> (k \in s) || (s == [::]).
Proof.
case: s k=>[|k s] //= k'; rewrite inE; case: eqP=>[->|N L] //.
by move: (@last_change k s); rewrite L=>-> //; case: eqP N.
Qed.

Lemma last_nochange_nil k (s : seq A) : last k s = k -> k \notin s -> s = [::].
Proof. by move/last_nochange; case/orP=>[/negbF ->|/eqP]. Qed.

(* last has bigger index than anything in x *)
Lemma index_last_mono x k (s : seq A) :
         uniq (k :: s) -> x \in s -> index x s <= index (last k s) s.
Proof.
elim: s k=>[|k s IH] //= k'; rewrite !inE negb_or (eq_sym x).
case: eqP=>//= _; case: eqP=>//= _ /and3P [_ H2 H3 H].
case: eqP=>[/esym E|_]; last by apply: IH=>//=; rewrite H2 H3.
by rewrite (last_nochange_nil E H2) in H.
Qed.

(* if it has bigger index, and is in the list, then it's last *)
Lemma max_index_last (s : seq A) (x y : A) :
         uniq s -> x \in s ->
         (forall z, z \in s -> index z s <= index x s) -> last y s = x.
Proof.
elim: s y=>[|k s IH] y //= /andP [Nk U]; rewrite inE (eq_sym k).
case: (x =P k) Nk=>[<-{k} Nk _|_ Nk /= S] /= D; last first.
- apply: IH=>// z Z; move: (D z); rewrite inE Z orbT=>/(_ (erefl _)).
  by case: ifP Z Nk=>// /eqP ->->.
suff : size s == 0 by move/eqP/size0nil=>->.
rewrite eqn0Ngt -has_predT; apply/hasPn=>z Z.
move: (D z); rewrite inE Z orbT=>/(_ (erefl _)).
by case: ifP Z Nk=>// /eqP ->->.
Qed.

(* last_filter either returns default or a p-element of ks *)
Lemma last_filter_change k p (ks : seq A) :
        last k (filter p ks) != k ->
        p (last k (filter p ks)) && (last k (filter p ks) \in ks).
Proof. by move/last_change; rewrite mem_filter. Qed.

Lemma index_filter_mono (p : pred A) (ks : seq A) x y :
        p x -> index x ks <= index y ks ->
        index x (filter p ks) <= index y (filter p ks).
Proof.
move=>Px; elim: ks=>[|k ks IH] //=; case P : (p k)=>/=;
by case: ifP Px; case: ifP=>// _ /eqP <-; rewrite P.
Qed.

Lemma filter_sub (p1 p2 : pred A) (s : seq A) :
        subpred p1 p2 -> {subset filter p1 s <= filter p2 s}.
Proof.
move=>S; rewrite (_ : filter p1 s = filter p1 (filter p2 s)).
- by apply: mem_subseq; apply: filter_subseq.
rewrite -filter_predI; apply: eq_in_filter=>x X /=.
by case E : (p1 x)=>//=; rewrite (S _ E).
Qed.

Lemma last_filter_neq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> x \notin s ->
        last x (filter p1 s) != x -> last x (filter p2 s) != x.
Proof.
move=>S N /last_filter_change /andP [H1 H2].
apply: (@last_notin (last x [seq x <-s | p1 x])).
- by rewrite mem_filter H2 andbT; apply: S.
by rewrite mem_filter negb_and N orbT.
Qed.

Lemma last_filter_eq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> x \notin s ->
        last x (filter p2 s) = x -> last x (filter p1 s) = x.
Proof.
move=>S N /eqP E; apply/eqP.
by apply: contraTT E; apply: last_filter_neq.
Qed.

Lemma index_last_sub (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> uniq (x :: s) ->
        index (last x (filter p1 s)) (x :: s) <=
        index (last x (filter p2 s)) (x :: s).
Proof.
move=>S; elim: s x=>[|k s IH] //= x; rewrite !inE negb_or -andbA.
rewrite -(eq_sym k) -!(eq_sym (last _ _)); case/and4P=>N Sx Sk U.
have [Ux Uk] : uniq (x :: s) /\ uniq (k :: s) by rewrite /= Sx Sk U.
case P1 : (p1 k)=>/=.
- rewrite (S _ P1) /=; case: (last k _ =P k).
  - move/last_nochange; rewrite mem_filter (negbTE Sk) andbF /=.
    move/eqP=>-> /=; rewrite (negbTE N).
    case: (last k _ =P k); first by move=>->; rewrite (negbTE N).
    by case/eqP/last_filter_change/andP; case: eqP Sx=>// <- /negbTE ->.
  move/eqP=>N1; move: (last_filter_neq S Sk N1)=>N2.
  move: (IH _ Uk); rewrite /= !(eq_sym k).
  rewrite (negbTE N1) (negbTE N2) -(last_changeE1 N1 x) -(last_changeE1 N2 x).
  rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sx,orbT) //.
  by rewrite (negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sx,orbT).
case P2 : (p2 k)=>/=.
- case: (last x _ =P x)=>// /eqP N1; move: (last_filter_neq S Sx N1)=>N2.
  move: (IH _ Ux); rewrite /= !(eq_sym x) (negbTE N1) (negbTE N2).
  rewrite -(last_changeE1 N1 k) {1 3}(last_changeE1 N2 k).
  rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sk,orbT) //.
  by rewrite !(negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sk,Sx,orbT).
case: (last x _ =P x)=>// /eqP N1; move: (last_filter_neq S Sx N1)=>N2.
move: (IH _ Ux); rewrite /= !(eq_sym x) (negbTE N1) (negbTE N2).
rewrite -(last_changeE1 N1 k) -(last_changeE1 N2 k).
rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sk,orbT) //.
by rewrite !(negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sk,orbT).
Qed.

Lemma last_filter_last_helper (p : pred A) x (s : seq A) y :
        uniq (x :: s) -> p y -> y \in s ->
        index y s <= index (last x (filter p s)) s.
Proof.
elim: s x=>[|k s IH] x //=; rewrite !inE !negb_or !(eq_sym _ k).
case/andP=>/andP [H1 H2] /andP [H3 H4] Px.
case: eqP=> [->|_] //= Ks; case P: (p k)=>/=.
- case: eqP=>E; last by apply: IH=>//=; rewrite H3 H4.
  move: (@last_in y k (filter p s)); rewrite -E !mem_filter.
  by rewrite Px Ks P (negbTE H3); move/(_ (erefl _)).
case: eqP=>E; last by apply: IH=>//=; rewrite H2 H4.
by move: H1; rewrite E; move/last_filter_change; rewrite -E P.
Qed.

Lemma last_filter_last (p : pred A) x (s : seq A) y :
        uniq (x :: s) -> p y -> y \in s ->
        index y (x :: s) <= index (last x (filter p s)) (x :: s).
Proof.
move=>/= /andP [Sx U] H Sy /=; case: (x =P y)=>//= _.
have Hy : y \in [seq x <- s | p x] by rewrite mem_filter H Sy.
rewrite eq_sym; case: (last x _ =P x); last first.
- by move=>_; apply: last_filter_last_helper=>//=; rewrite Sx U.
move/last_nochange; rewrite mem_filter (negbTE Sx) andbF /=.
by move/eqP=>E; rewrite E in Hy.
Qed.

End LastFilter.

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
