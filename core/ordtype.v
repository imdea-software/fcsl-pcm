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
(* This file defines ordType - the structure for types with a decidable       *)
(* (strict) order relation.                                                   *)
(* ordType is a subclass of mathcomp's eqType                                 *)
(* This file also defines some important instances of ordType                 *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype.
From pcm Require Import options.

Module Ordered.

Section RawMixin.

Structure mixin_of (T : eqType) :=
  Mixin {ordering : rel T;
         _ : irreflexive ordering;
         _ : transitive ordering;
         _ : forall x y, x != y -> ordering x y || ordering y x}.

End RawMixin.

(* the class takes a naked type T and returns all the *)
(* related mixins; the inherited ones and the added ones *)
Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T;
   mixin : mixin_of (EqType T base)}.

Local Coercion base : class_of >-> Equality.class_of.

(* The polymorphism annotations here and below are needed for storing *)
(* ordType instances in finMaps which have an ordType constraint of *)
(* their own. An example of this is KVMap from HTT. *)
Polymorphic Cumulative Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Polymorphic Universe ou.
Polymorphic Variables (T : Type@{ou}) (cT : type@{ou}).
Polymorphic Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Polymorphic Definition clone c of phant_id class c := @Pack T c.

(* produce an ordered type out of the inherited mixins *)
(* equalize m0 and m by means of a phantom; will be exploited *)
(* further down in the definition of OrdType *)
Polymorphic Definition pack b (m0 : mixin_of (EqType T b)) :=
  fun m & phant_id m0 m => Pack (@Class T b m).

Polymorphic Definition eqType := Eval hnf in EqType cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Notation ordType := Ordered.type.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T _ m _ id).
Definition ord T : rel (sort T) := (ordering (mixin (class T))).
Notation "[ 'ordType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.
End Exports.
End Ordered.
Export Ordered.Exports.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

Section Lemmas.
Variable T : ordType.
Implicit Types x y : T.

Lemma irr : irreflexive (@ord T).
Proof. by case: T=>s [b [m]]. Qed.

Lemma trans : transitive (@ord T).
Proof. by case: T=>s [b [m]]. Qed.

Lemma semiconnex x y : x != y -> ord x y || ord y x.
Proof. by case: T x y=>s [b [m]]. Qed.

Lemma ord_total x y : [|| ord x y, x == y | ord y x].
Proof.
case E: (x == y)=>/=; first by rewrite orbT.
by apply: semiconnex; rewrite negbT.
Qed.

Lemma nsym x y : ord x y -> ~ ord y x.
Proof. by move=>E1 E2; move: (trans E1 E2); rewrite irr. Qed.

Lemma orefl x : oleq x x.
Proof. by rewrite /oleq eq_refl orbT. Qed.

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=; case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1; case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1.
Qed.

Lemma oantisym : antisymmetric (@oleq T).
Proof.
move=>x y; rewrite /oleq (eq_sym x).
case: eqP=>// _; rewrite !orbF=>/andP [H1 H2].
by move: (trans H1 H2); rewrite irr.
Qed.

Lemma subrel_ord : subrel (@ord T) oleq.
Proof. exact: subrelUl. Qed.

Lemma sorted_oleq s : sorted (@ord T) s -> sorted (@oleq T) s.
Proof. by case: s=>//= x s; apply/sub_path/subrel_ord. Qed.

Lemma path_filter (r : rel T) (tr : transitive r) s (p : pred T) x :
        path r x s -> path r x (filter p s).
Proof. exact: (subseq_path tr (filter_subseq p s)). Qed.

Lemma ord_sorted_eq (s1 s2 : seq T) :
        sorted ord s1 -> sorted ord s2 -> s1 =i s2 -> s1 = s2.
Proof. by exact/irr_sorted_eq/irr/trans. Qed.

Lemma oleq_ord_trans (n m p : T) :
        oleq m n -> ord n p -> ord m p.
Proof. by case/orP; [apply: trans | move/eqP=>->]. Qed.

Lemma ord_oleq_trans (n m p : T) :
        ord m n -> oleq n p -> ord m p.
Proof. by move=>H /orP [|/eqP <- //]; apply: trans. Qed.

End Lemmas.

#[export]
Hint Resolve orefl irr trans otrans oantisym oleq_ord_trans : core.

Section Totality.
Variable K : ordType.

Variant total_spec (x y : K) : bool -> bool -> bool -> Type :=
| total_spec_lt of ord x y : total_spec x y true false false
| total_spec_eq of x == y : total_spec x y false true false
| total_spec_gt of ord y x : total_spec x y false false true.

Lemma ordP x y : total_spec x y (ord x y) (x == y) (ord y x).
Proof.
case H1: (x == y).
- by rewrite (eqP H1) irr; apply: total_spec_eq.
case H2: (ord x y); case H3: (ord y x).
- by case: (nsym H2 H3).
- by apply: total_spec_lt H2.
- by apply: total_spec_gt H3.
by move: (ord_total x y); rewrite H1 H2 H3.
Qed.
End Totality.

Lemma eq_oleq (K : ordType) (x y : K) : (x == y) = oleq x y && oleq y x.
Proof. by rewrite /oleq (eq_sym x); case: ordP. Qed.

(* Monotone (i.e. strictly increasing) functions for Ord Types *)
Section Mono.
Variables (A B :ordType).

Definition strictly_increasing f x y := @ord A x y -> @ord B (f x) (f y).

Structure mono : Type := Mono
           {fun_of: A -> B; _: forall x y, strictly_increasing fun_of x y}.

End Mono.
Arguments strictly_increasing {A B} f x y.
Arguments Mono {A B _} _.

Section Weakening.
Variable T : ordType.
Implicit Types x y : T.

Lemma ordW x y: ord x y -> oleq x y.
Proof. by rewrite /oleq =>->//. Qed.

Lemma oleqNord x y: oleq x y = ~~ (ord y x).
Proof. by rewrite /oleq; case:(ordP x y)=>//. Qed.

Lemma oleq_eqVord x y : oleq x y = (x == y) || ord x y.
Proof. by rewrite /oleq orbC. Qed.

Variant oleq_spec x y : bool -> bool -> Type :=
| oleq_spec_le of oleq x y : oleq_spec x y true false
| oleq_spec_gt of ord y x : oleq_spec x y false true.

Lemma oleqP x y : oleq_spec x y (oleq x y) (ord y x).
Proof.
case:(ordP x y).
- by move=>/ordW O; rewrite O; apply: oleq_spec_le.
- by move=>/eqP E; rewrite E orefl; apply: oleq_spec_le; apply: orefl.
by move=>O; rewrite oleqNord O //=; apply: oleq_spec_gt.
Qed.

Lemma oleq_total x y: oleq x y || oleq y x.
Proof. by case:oleqP=>// /ordW ->//. Qed.

End Weakening.

(* A trivial total ordering for Unit *)
Section unitOrd.
Let ordtt (x y : unit) := false.

Lemma irr_tt : irreflexive ordtt.
Proof. by []. Qed.

Lemma trans_tt : transitive ordtt.
Proof. by []. Qed.

Lemma semiconn_tt x y : x != y -> ordtt x y || ordtt y x.
Proof. by []. Qed.

Let unit_ordMixin := OrdMixin irr_tt trans_tt semiconn_tt.
Canonical Structure unit_ordType := Eval hnf in OrdType unit unit_ordMixin.
End unitOrd.

Section NatOrd.
Lemma irr_ltn_nat : irreflexive ltn. Proof. by move=>x; rewrite /= ltnn. Qed.
Lemma trans_ltn_nat : transitive ltn. Proof. by apply: ltn_trans. Qed.
Lemma semiconn_ltn_nat x y : x != y -> (x < y) || (y < x).
Proof. by case: ltngtP. Qed.

Definition nat_ordMixin := OrdMixin irr_ltn_nat trans_ltn_nat semiconn_ltn_nat.
Canonical Structure nat_ordType := Eval hnf in OrdType nat nat_ordMixin.
End NatOrd.

Section ProdOrd.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) :=
  fun x y => if x.1 == y.1 then ord x.2 y.2 else ord x.1 y.1.

Lemma irr_lex : irreflexive lex.
Proof. by move=>x; rewrite /lex eq_refl irr. Qed.

Lemma trans_lex : transitive lex.
Proof.
move=>[x1 x2][y1 y2][z1 z2]; rewrite /lex /=.
case: ifP=>H1; first by rewrite (eqP H1); case: eqP=>// _; apply: trans.
case: ifP=>H2; first by rewrite (eqP H2) in H1 *; rewrite H1.
case: ifP=>H3; last by apply: trans.
by rewrite (eqP H3)=>R1; move/(nsym R1).
Qed.

Lemma semiconn_lex : forall x y, x != y -> lex x y || lex y x.
Proof.
move=>[x1 x2][y1 y2]; rewrite /lex /=.
by case: ifP=>H1 H2; rewrite eq_sym H1 semiconnex //; move: H2; rewrite -pair_eqE /= H1 //.
Qed.

Definition prod_ordMixin := OrdMixin irr_lex trans_lex semiconn_lex.
Canonical Structure prod_ordType := Eval hnf in OrdType (K * T) prod_ordMixin.
End ProdOrd.

Section FinTypeOrd.
Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T).

Lemma irr_ordf : irreflexive ordf.
Proof. by move=>x; rewrite /ordf ltnn. Qed.

Lemma trans_ordf : transitive ordf.
Proof. by move=>x y z; rewrite /ordf; apply: ltn_trans. Qed.

Lemma semiconn_ordf x y : x != y -> ordf x y || ordf y x.
Proof.
rewrite /ordf; case: ltngtP=>//= H.
have [H1 H2]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x H1) -(nth_index x H2) H eq_refl.
Qed.

Definition fin_ordMixin := OrdMixin irr_ordf trans_ordf semiconn_ordf.
End FinTypeOrd.

(* notation to let us write I_n instead of (ordinal_finType n) *)
Notation "[ 'fin_ordMixin' 'of' T ]" :=
  (fin_ordMixin _ : Ordered.mixin_of [eqType of T]) (at level 0).

Definition ordinal_ordMixin n := [fin_ordMixin of 'I_n].
Canonical Structure ordinal_ordType n := Eval hnf in OrdType 'I_n (ordinal_ordMixin n).

Section SeqOrd.
Variable (T : ordType).

Fixpoint ords x : pred (seq T) :=
  fun y => match x , y with
                 | [::] , [::] => false
                 | [::] ,  t :: ts => true
                 | x :: xs , y :: ys => if x == y then ords xs ys
                                        else ord x y
                 | _ :: _ , [::] => false
             end.

Lemma irr_ords : irreflexive ords.
Proof. by elim=>//= a l ->; rewrite irr; case:eqP=> //=. Qed.

Lemma trans_ords : transitive ords.
Proof.
elim=>[|y ys IHy][|x xs][|z zs]//=.
case:eqP=>//[->|H0];case:eqP=>//H; first by move/IHy; apply.
- by case:eqP=>//; rewrite -H; first (by move/H0).
case:eqP=>//[->|H1] H2; first by move/(nsym H2).
by move/(trans H2).
Qed.

Lemma semiconn_ords : forall x y, x != y -> ords x y || ords y x.
Proof.
elim=>[|x xs IH][|y ys]//=.
case:ifP => H1 H2; rewrite eq_sym H1.
- by apply: IH; move: H2; rewrite -eqseqE /= H1 andTb.
by rewrite semiconnex // H1.
Qed.

Definition seq_ordMixin := OrdMixin irr_ords trans_ords semiconn_ords.
Canonical Structure seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.
End SeqOrd.

#[deprecated(since="fcsl-pcm 1.4.0", note="Use ord_sorted_eq instead.")]
Notation eq_sorted_ord := ord_sorted_eq (only parsing).
