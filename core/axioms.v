(*
Copyright 2013 IMDEA Software Institute
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
(* This file contains axioms that are used in some parts of the library.      *)
(* The selected set of axioms is known to be consistent with Coq's logic.     *)
(* These axioms are:                                                          *)
(*   - propositional extensionality (pext);                                   *)
(*   - functional extensionality (fext).                                      *)
(* This file also defines the dynamic type as an alias for sigT and           *)
(* Jonh Major equality via equality cast.                                     *)
(******************************************************************************)

From Corelib Require Import ssreflect ssrfun.
From Stdlib Require Import Eqdep ClassicalFacts.
From mathcomp Require Import eqtype.
From pcm Require Import options.

(*****************************)
(* Axioms and extensionality *)
(*****************************)

(* We're additionally using the eq_rect_eq axiom (equivalent to UIP) from
   Coq.Logic.Eqdep for its two consequences: inj_pair2 and StreicherK *)

(* extensionality is needed for domains *)
Axiom pext : forall p1 p2 : Prop, (p1 <-> p2) -> p1 = p2.
Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Lemma pf_irr (P : Prop) (p1 p2 : P) : p1 = p2.
Proof. by apply/ext_prop_dep_proof_irrel_cic/@pext. Qed.

Lemma inj_sval A P : injective (@sval A P).
Proof.
move=>[x Hx][y Hy] /= H; move: Hx Hy; rewrite H=>*.
congr exist; apply: pf_irr.
Qed.

Lemma svalE A (P : A -> Prop) x H : sval (exist P x H) = x.
Proof. by []. Qed.

Lemma compf1 A B (f : A -> B) : f = f \o id.
Proof. by apply: fext. Qed.

Lemma comp1f A B (f : A -> B) : f = id \o f.
Proof. by apply: fext. Qed.

(********)
(* Cast *)
(********)

(* depends on StreicherK axiom *)

Section Cast.
Variable (T : Type) (interp : T -> Type).

Definition cast A B (pf : A = B) (v : interp A) : interp B :=
  ecast _ _ pf v.

Lemma eqc A (pf : A = A) (v : interp A) : cast pf v = v.
Proof. by move: pf; apply: Streicher_K. Qed.

Lemma castE A B (pf1 pf2 : A = B) (v1 v2 : interp A) :
        v1 = v2 <-> cast pf1 v1 = cast pf2 v2.
Proof. by subst B; rewrite !eqc. Qed.

End Cast.

Arguments cast {T} interp [A][B] pf v.

(* special notation for the common case when interp = id *)
Abbreviation icast pf v := (@cast _ id _ _ pf v).

(* in case of eqTypes StreicherK not needed *)
Section EqTypeCast.
Variable (T : eqType) (interp : T -> Type).
Lemma eqd a (pf : a = a) (v : interp a) : cast interp pf v = v.
Proof. by rewrite eq_axiomK. Qed.
End EqTypeCast.

(* type dynamic is sigT *)

Section Dynamic.
Variables (A : Type) (P : A -> Type).

(** eta expand definitions to prevent universe inconsistencies when using
    the injectivity of constructors of datatypes depending on [[dynamic]] *)

Definition dynamic := sigT [eta P].
Definition dyn := existT P.
Definition dyn_tp := @projT1 _ P.
Definition dyn_val := @projT2 _ P.
Definition dyn_eta := @sigT_eta _ P.
Definition inj_dynT := @eq_sigT_fst _ P.
Definition inj_dyn := @inj_pair2 _ P.
End Dynamic.

Prenex Implicits dyn_tp dyn_val inj_dynT inj_dyn.
Arguments dyn {T} interp {A} _ : rename.
Abbreviation idyn v := (@dyn _ id _ v).

(* Tagging *)

Abbreviation Tag := (@existT _ _).
Definition inj_tagT := @eq_sigT_fst.
Definition inj_tagK := @inj_pair2.
Prenex Implicits inj_tagT inj_tagK.

(* Because of a bug in inversion and injection tactics *)
(* we occasionally have to destruct pairs by hand, else we *)
(* lose the second equation. *)
Lemma inj_pair A B (a1 a2 : A) (b1 b2 : B) :
         (a1, b1) = (a2, b2) -> 
         (a1 = a2) * (b1 = b2).
Proof. by case. Qed.

Arguments inj_pair {A B a1 a2 b1 b2}.

Definition inj_some := @Some_inj.
Prenex Implicits inj_some.

