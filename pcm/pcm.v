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
(* This file defines pcm -- a type equipped with partial commutative          *)
(* monoid structure, several subclasses of PCMs, and important                *)
(* concrete instances.                                                        *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype bigop seq.
From fcsl Require Import prelude seqperm pred options.

Declare Scope pcm_scope.
Delimit Scope pcm_scope with pcm.
Open Scope pcm_scope.

(*******************************)
(* Partial Commutative Monoids *)
(*******************************)

Module PCM.

Record mixin_of (T : Type) := Mixin {
    valid_op : T -> bool;
    join_op : T -> T -> T;
    unit_op : T;
    _ : commutative join_op;
    _ : associative join_op;
    _ : left_id unit_op join_op;
    (* monotonicity of valid *)
    _ : forall x y, valid_op (join_op x y) -> valid_op x;
    (* unit is valid *)
    _ : valid_op unit_op}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack c := @Pack T c.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

Definition valid := valid_op class.
Definition join := join_op class.
Definition Unit := unit_op class.

End ClassDef.

Arguments Unit {cT}.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation pcm := type.
Notation PCMMixin := Mixin.
Notation PCM T m := (@pack T m).

Notation "[ 'pcmMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'pcmMixin'  'of'  T ]") : pcm_scope.
Notation "[ 'pcm' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'pcm'  'of'  T  'for'  C ]") : pcm_scope.
Notation "[ 'pcm' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'pcm'  'of'  T ]") : pcm_scope.

Notation "x \+ y" := (join x y)
  (at level 43, left associativity) : pcm_scope.
Notation valid := valid.
Notation Unit := Unit.

Arguments Unit {cT}.
Arguments valid {cT} !_ / : simpl nomatch.
Prenex Implicits join Unit.

(* Restating the laws, with the notation. *)
(* Plus some additional derived lemmas.   *)

Section Laws.
Variable U V : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof.
by rewrite /join; case: U x y=>tp [v j z Cj *]; apply: Cj.
Qed.

Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
Proof.
by rewrite /join; case: U x y z=>tp [v j z Cj Aj *]; apply: Aj.
Qed.

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
Proof. by rewrite -joinA (joinC y) joinA. Qed.

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof. by rewrite joinA (joinC x) -joinA. Qed.

Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof.
by rewrite /valid/join; case: U x y=>tp [v j z Cj Aj Uj /= Mj inv f ?]; apply: Mj.
Qed.

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof. by rewrite joinC; apply: validL. Qed.

(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma validE2 (x y : U) : valid (x \+ y) -> (valid x * valid y) * (valid (x \+ y) * valid (y \+ x)).
Proof. by move=>X; rewrite (validL X) (validR X) X joinC X. Qed.

Lemma unitL (x : U) : Unit \+ x = x.
Proof.
by rewrite /Unit/join; case: U x=>tp [v j z Cj Aj Uj *]; apply: Uj.
Qed.

Lemma unitR (x : U) : x \+ Unit = x.
Proof. by rewrite joinC unitL. Qed.

Lemma valid_unit : valid (@Unit U).
Proof.
by rewrite /valid/Unit; case: U=>tp [v j z Cj Aj Uj Vm Vu *].
Qed.

(* some helper lemmas for easier extraction of validity claims *)
Lemma validAR (x y z : U) : valid (x \+ y \+ z) -> valid (y \+ z).
Proof. by rewrite -joinA; apply: validR. Qed.

Lemma validAL (x y z : U) : valid (x \+ (y \+ z)) -> valid (x \+ y).
Proof. by rewrite joinA; apply: validL. Qed.

Lemma validLA (x y z : U) : valid (x \+ y \+ z) -> valid (x \+ (y \+ z)).
Proof. by rewrite joinA. Qed.

Lemma validRA (x y z : U) : valid (x \+ (y \+ z)) -> valid (x \+ y \+ z).
Proof. by rewrite joinA. Qed.

(* poor man's automation for a very frequent story of 3 summands *)
(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma validLE3 (x y z : U) : valid (x \+ y \+ z) ->
        (((valid x * valid y) * (valid z * valid (x \+ y))) *
        ((valid (x \+ z) * valid (y \+ x)) * (valid (y \+ z) * valid (z \+ x)))) *
        (((valid (z \+ y) * valid (x \+ (y \+ z))) *
          (valid (x \+ y \+ z) * valid (x \+ (z \+ y)))) *
         ((valid (x \+ z \+ y) * valid (y \+ (x \+ z))) *
          (valid (y \+ x \+ z) * valid (y \+ (z \+ x))))) *
        (((valid (y \+ z \+ x) * valid (z \+ (x \+ y))) *
          (valid (z \+ x \+ y) * valid (z \+ (y \+ x)))) *
         valid (z \+ y \+ x)).
Proof.
move=> V3; rewrite !(validE2 V3) joinA V3.
rewrite joinAC in V3; rewrite !(validE2 V3).
rewrite [x \+ z]joinC in V3; rewrite !(validE2 V3).
rewrite joinAC in V3; rewrite !(validE2 V3).
rewrite [z \+ y]joinC in V3; rewrite !(validE2 V3).
by rewrite joinAC in V3; rewrite !(validE2 V3).
Qed.

Lemma validRE3 (x y z : U) : valid (x \+ (y \+ z)) ->
        (((valid x * valid y) * (valid z * valid (x \+ y))) *
         ((valid (x \+ z) * valid (y \+ x)) * (valid (y \+ z) * valid (z \+ x)))) *
        (((valid (z \+ y) * valid (x \+ (y \+ z))) *
          (valid (x \+ y \+ z) * valid (x \+ (z \+ y)))) *
         ((valid (x \+ z \+ y) * valid (y \+ (x \+ z))) *
          (valid (y \+ x \+ z) * valid (y \+ (z \+ x))))) *
        (((valid (y \+ z \+ x) * valid (z \+ (x \+ y))) *
          (valid (z \+ x \+ y) * valid (z \+ (y \+ x)))) *
         valid (z \+ y \+ x)).
Proof. by rewrite {1}joinA; apply: validLE3. Qed.

End Laws.

Hint Resolve valid_unit : core.

Section UnfoldingRules.
Variable U : pcm.

Lemma pcm_joinE (x y : U) : x \+ y = join_op (class U) x y.
Proof. by rewrite /join. Qed.

Lemma pcm_validE (x : U) : valid x = valid_op (class U) x.
Proof. by rewrite /valid. Qed.

Lemma pcm_unitE : Unit = unit_op (class U).
Proof. by rewrite /Unit. Qed.

Definition pcmE := (pcm_joinE, pcm_validE, pcm_unitE).

(* also a simple rearrangment equation *)
Definition pull (x y : U) := (joinC y x, joinCA y x).

End UnfoldingRules.

End Exports.

End PCM.

Export PCM.Exports.

(*********************)
(* Cancellative PCMs *)
(*********************)

(* definition of precision for an arbitrary PCM U *)

Definition precise (U : pcm) (P : U -> Prop) :=
  forall s1 s2 t1 t2,
    valid (s1 \+ t1) -> P s1 -> P s2 ->
    s1 \+ t1 = s2 \+ t2 -> s1 = s2.

Module CancellativePCM.

Variant mixin_of (U : pcm) := Mixin of
  forall x1 x2 x : U, valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2.

Section ClassDef.

Record class_of (U : Type) := Class {
  base : PCM.mixin_of U;
  mixin : mixin_of (PCM.Pack base)}.

Local Coercion base : class_of >-> PCM.mixin_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce a cancellative type out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack b0 (m0 : mixin_of (PCM.Pack b0)) :=
  fun m & phant_id m0 m => Pack (@Class T b0 m).

Definition pcm := PCM.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PCM.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pcm : type >-> PCM.type.
Canonical Structure pcm.

Notation cpcm := type.
Notation CPCMMixin := Mixin.
Notation CPCM T m := (@pack T _ _ m id).

Notation "[ 'cpcm' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'cpcm'  'of'  T  'for' cT ]") : pcm_scope.
Notation "[ 'cpcm' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'cpcm'  'of'  T ]") : pcm_scope.

Section Lemmas.
Variable U : cpcm.

Lemma joinKx (x1 x2 x : U) : valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2.
Proof. by case: U x1 x2 x=>V [b][K] T; apply: K. Qed.

Lemma joinxK (x x1 x2 : U) : valid (x \+ x1) -> x \+ x1 = x \+ x2 -> x1 = x2.
Proof. by rewrite !(joinC x); apply: joinKx. Qed.

Lemma cancPL (P : U -> Prop) s1 s2 t1 t2 :
        precise P -> valid (s1 \+ t1) -> P s1 -> P s2 ->
        s1 \+ t1 = s2 \+ t2 -> (s1 = s2) * (t1 = t2).
Proof.
move=>H V H1 H2 E; move: (H _ _ _ _ V H1 H2 E)=>X.
by rewrite -X in E *; rewrite (joinxK V E).
Qed.

Lemma cancPR (P : U -> Prop) s1 s2 t1 t2 :
        precise P -> valid (s1 \+ t1) -> P t1 -> P t2 ->
        s1 \+ t1 = s2 \+ t2 -> (s1 = s2) * (t1 = t2).
Proof.
move=>H V H1 H2 E. rewrite (joinC s1) (joinC s2) in E V.
by rewrite !(cancPL H V H1 H2 E).
Qed.

End Lemmas.
End Exports.

End CancellativePCM.

Export CancellativePCM.Exports.

(***************)
(* Topped PCMs *)
(***************)

(* PCM with an explicit undef value *)
(* we will want these constants to be decidable *)
(* so we also add unitb, to test if an element is unit *)
(* for undefb, that should be valid, so we don't add anything special *)
(* OTOH, unit should not be decomposable *)

Module TPCM.

Record mixin_of (U : pcm) := Mixin {
  undef_op : U;
  unitb_op : U -> bool;
  _ : forall x, reflect (x = Unit) (unitb_op x);
  _ : ~~ valid undef_op;
  _ : forall x, undef_op \+ x = undef_op}.

Section ClassDef.

Record class_of (U : Type) := Class {
  base : PCM.mixin_of U;
  mixin : mixin_of (PCM.Pack base)}.

Local Coercion base : class_of >-> PCM.mixin_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce a topped pcm out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack b0 (m0 : mixin_of (PCM.Pack b0)) :=
  fun m & phant_id m0 m => Pack (@Class T b0 m).

Definition pcm := PCM.Pack class.
Definition unitb := unitb_op (mixin class).
Definition undef : pcm := undef_op (mixin class).

End ClassDef.

Module Exports.
Coercion base : class_of >-> PCM.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pcm : type >-> PCM.type.
Canonical Structure pcm.
Notation tpcm := type.
Notation TPCMMixin := Mixin.
Notation TPCM T m := (@pack T _ _ m id).

Notation "[ 'tpcm' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'tpcm'  'of'  T  'for' cT ]") : pcm_scope.
Notation "[ 'tpcm' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'tpcm'  'of'  T ]") : pcm_scope.

Notation undef := undef.
Notation unitb := unitb.
Arguments undef {cT}.
Prenex Implicits undef.

Section Lemmas.
Variable U : tpcm.

Lemma unitbP (x : U) : reflect (x = Unit) (unitb x).
Proof. by case: U x=>V [b][u]. Qed.

Lemma unitbE (f : U) : f = Unit <-> unitb f.
Proof. by case: unitbP. Qed.

Lemma unitb0 : unitb (Unit : U).
Proof. by case: unitbP. Qed.

Lemma valid_undefN : ~~ valid (@undef U).
Proof. by case: U=>V [b][u]. Qed.

Lemma valid_undef : valid (@undef U) = false.
Proof. by rewrite (negbTE valid_undefN). Qed.

Lemma undef_join (x : U) : undef \+ x = undef.
Proof. by case: U x=>V [b][u]. Qed.

Lemma join_undef (x : U) : x \+ undef = undef.
Proof. by rewrite joinC undef_join. Qed.

Lemma undef0 : (undef : U) <> (Unit : U).
Proof. by move=>E; move: (@valid_unit U); rewrite -E valid_undef. Qed.

Lemma unitb_undef : unitb (undef : U) = false.
Proof. by case: unitbP =>// /undef0. Qed.

Definition tpcmE := (undef_join, join_undef, valid_undef, unitb0, unitb_undef).

End Lemmas.
End Exports.

End TPCM.

Export TPCM.Exports.

(********************************)
(* PCMs with decidable equality *)
(********************************)

Module EQPCM.
Section ClassDef.

Record mixin_of (U : eqType) := Mixin {
  base : PCM.mixin_of U}.

Record class_of (U : Type) := Class {
  eqbase : Equality.mixin_of U;
  mixin : mixin_of (EqType U eqbase)}.

Local Coercion eqbase: class_of >-> Equality.mixin_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce an eqpcm out of the mixin *)
(* equalize m0 and m by means of a phantom *)
Definition pack (eb0 : Equality.mixin_of T) (m0 : mixin_of (EqType T eb0)) :=
  fun m & phant_id m0 m => Pack (@Class T eb0 m).

Definition pcm := PCM.Pack (base (mixin class)).
Definition eqtype := Eval hnf in EqType cT class.

End ClassDef.

Module Exports.
Coercion eqbase : class_of >-> Equality.mixin_of.
Coercion sort : type >-> Sortclass.
Coercion pcm : type >-> PCM.type.
Coercion eqtype : type >-> eqType.
Canonical Structure pcm.
Canonical Structure eqtype.
Notation eqpcm := type.
Notation EQPCM T m := (@pack T _ _ (Mixin m) id).

Notation "[ 'eqpcm' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'eqpcm'  'of'  T  'for' cT ]") : pcm_scope.
Notation "[ 'eqpcm' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'eqpcm'  'of'  T ]") : pcm_scope.

End Exports.

End EQPCM.

Export EQPCM.Exports.


(***************************************)
(* Support for big operators over PCMs *)
(***************************************)

Canonical pcm_monoid (U : pcm) := Monoid.Law (@joinA U) (@unitL U) (@unitR U).
Canonical pcm_comoid (U : pcm) := Monoid.ComLaw (@joinC U).

Section BigPartialMorph.
Variables (R1 : Type) (R2 : pcm) (K : R1 -> R2 -> Type) (f : R2 -> R1).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Hypotheses (f_op : forall x y : R2, valid (x \+ y) -> f (x \+ y) = op1 (f x) (f y))
           (f_id : f Unit = id1).

Lemma big_pmorph I r (P : pred I) F :
        valid (\big[PCM.join/Unit]_(i <- r | P i) F i) ->
        f (\big[PCM.join/Unit]_(i <- r | P i) F i) =
          \big[op1/id1]_(i <- r | P i) f (F i).
Proof.
rewrite unlock; elim: r=>[|x r IH] //=; case: ifP=>// H V.
by rewrite f_op // IH //; apply: validR V.
Qed.

End BigPartialMorph.


(*********************)
(* PCM constructions *)
(*********************)


(* nats with addition are a pcm *)
Definition natPCMMix :=
  PCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).
Canonical natPCM := Eval hnf in PCM nat natPCMMix.
Canonical natEQPCM := Eval hnf in EQPCM nat natPCMMix.

(* also with multiplication, but we don't make that one canonical *)
Definition multPCMMix :=
  PCMMixin mulnC mulnA mul1n (fun x y => @id true) (erefl _).
Definition multPCM := Eval hnf in PCM nat multPCMMix.
Definition multEQPCM := Eval hnf in EQPCM nat multPCMMix.

(* with max too *)
Definition maxPCMMix :=
  PCMMixin maxnC maxnA max0n (fun x y => @id true) (erefl _).
Definition maxPCM := Eval hnf in PCM nat maxPCMMix.
Definition maxEQPCM := Eval hnf in EQPCM nat maxPCMMix.

(* bools with disjunction are a pcm *)
Definition bool_orPCMMix :=
  PCMMixin orbC orbA orFb (fun x y => @id true) (erefl _).
Definition bool_orPCM := Eval hnf in PCM bool bool_orPCMMix.
Definition bool_orEQPCM := Eval hnf in EQPCM bool bool_orPCMMix.

(* positive natural numbers under max are a pcm *)
Section PosNatMax.

Definition posNat := sig (fun x => x > 0).

Lemma max_pos (x y : posNat) : maxn (val x) (val y) > 0.
Proof. by case: x y=>x pfx [y pfy]; rewrite leq_max pfx pfy. Qed.

Definition pos_valid (x : posNat) := true.
Definition pos_join x y : posNat :=
  Sub (maxn (val x) (val y)) (max_pos x y).
Definition pos_unit : posNat := Sub 1 (leqnn 1).

Lemma pos_joinC x y : pos_join x y = pos_join y x.
Proof. by apply/eqP; rewrite /pos_join -val_eqE /= maxnC. Qed.

Lemma pos_joinA x y z : pos_join x (pos_join y z) = pos_join (pos_join x y) z.
Proof. by apply/eqP; rewrite /pos_join -val_eqE /= maxnA. Qed.

Lemma pos_validL x y : pos_valid (pos_join x y) -> pos_valid x.
Proof. by []. Qed.

Lemma pos_unitL x : pos_join pos_unit x = x.
Proof.
apply/eqP; rewrite /pos_join -val_eqE.
by apply/eqP/maxn_idPr; case: x.
Qed.

Lemma pos_validU : pos_valid pos_unit. Proof. by []. Qed.

Definition posnatmaxPCMMix :=
   PCMMixin pos_joinC pos_joinA pos_unitL
           pos_validL pos_validU.
Canonical posnatmaxPCM := Eval hnf in PCM posNat posnatmaxPCMMix.

End PosNatMax.

(* cartesian product of pcms is a pcm *)

Module ProdPCM.
Section ProdPCM.
Variables (U V : pcm).
Local Notation tp := (U * V)%type.

Definition pvalid := [fun x : tp => valid x.1 && valid x.2].
Definition pjoin := [fun x1 x2 : tp => (x1.1 \+ x2.1, x1.2 \+ x2.2)].
Definition punit : tp := (Unit, Unit).

Lemma joinC x y : pjoin x y = pjoin y x.
Proof. by rewrite /= (joinC x.1) (joinC x.2). Qed.

Lemma joinA x y z : pjoin x (pjoin y z) = pjoin (pjoin x y) z.
Proof. by rewrite /= !joinA. Qed.

Lemma validL x y : pvalid (pjoin x y) -> pvalid x.
Proof. by case/andP => /= /validL-> /validL->. Qed.

Lemma unitL x : pjoin punit x = x.
Proof. by rewrite /= !unitL -prod_eta. Qed.

Lemma validU : pvalid punit.
Proof. by rewrite /= !valid_unit. Qed.

End ProdPCM.
End ProdPCM.

Definition prodPCMMixin U V :=
  PCMMixin (@ProdPCM.joinC U V) (@ProdPCM.joinA U V)
           (@ProdPCM.unitL U V) (@ProdPCM.validL U V)
           (@ProdPCM.validU U V).
Canonical prodPCM U V := Eval hnf in PCM (_ * _) (@prodPCMMixin U V).
Canonical prodEQPCM (U V : eqpcm) :=
  Eval hnf in EQPCM (_ * _) (prodPCMMixin U V).

(* product simplification *)

Section Simplification.
Variable U V : pcm.

Lemma pcmPJ (x1 y1 : U) (x2 y2 : V) :
        (x1, x2) \+ (y1, y2) = (x1 \+ y1, x2 \+ y2).
Proof. by rewrite pcmE. Qed.

Lemma pcmFJ (x y : U * V) : (x \+ y).1 = x.1 \+ y.1.
Proof. by rewrite pcmE. Qed.

Lemma pcmSJ (x y : U * V) : (x \+ y).2 = x.2 \+ y.2.
Proof. by rewrite pcmE. Qed.

Lemma pcmPV (x : prodPCM U V) : valid x = valid x.1 && valid x.2.
Proof. by []. Qed.

Lemma pcmPU : Unit = (Unit, Unit) :> prodPCM U V.
Proof. by rewrite pcmE. Qed.

Definition pcmPE := (pcmPJ, pcmFJ, pcmSJ, pcmPV, pcmPU).

End Simplification.

(* product of TPCMs is a TPCM *)

Section ProdTPCM.
Variables (U V : tpcm).

Lemma prod_unitb (x : prodPCM U V) :
        reflect (x = Unit) (unitb x.1 && unitb x.2).
Proof.
case: x=>x1 x2; case: andP=>/= H; constructor.
- by case: H=>/unitbP -> /unitbP ->; rewrite pcmPE.
by rewrite pcmPE; case=>X1 X2; elim: H; rewrite X1 X2 !tpcmE.
Qed.

Lemma prod_valid_undef : ~~ valid (@undef U, @undef V).
Proof. by rewrite /= !valid_undef. Qed.

Lemma prod_undef_join x : (@undef U, @undef V) \+ x = (@undef U, @undef V).
Proof. by rewrite [x]prod_eta /= pcmPJ !undef_join. Qed.

Definition prodTPCMMix := TPCMMixin prod_unitb prod_valid_undef prod_undef_join.
Canonical prodTPCM := Eval hnf in TPCM (U * V) prodTPCMMix.

End ProdTPCM.

(* unit is a PCM, but not a TPCM, as there is no undefined element. *)
(* We have to lift for that *)

Module UnitPCM.
Section UnitPCM.

Definition uvalid (x : unit) := true.
Definition ujoin (x y : unit) := tt.
Definition uunit := tt.

Lemma ujoinC x y : ujoin x y = ujoin y x.
Proof. by []. Qed.

Lemma ujoinA x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by []. Qed.

Lemma uvalidL x y : uvalid (ujoin x y) -> uvalid x.
Proof. by []. Qed.

Lemma uunitL x : ujoin uunit x = x.
Proof. by case: x. Qed.

Lemma uvalidU : uvalid uunit.
Proof. by []. Qed.

End UnitPCM.
End UnitPCM.

Definition unitPCMMixin :=
  PCMMixin UnitPCM.ujoinC UnitPCM.ujoinA
           UnitPCM.uunitL UnitPCM.uvalidL UnitPCM.uvalidU.
Canonical unitPCM := Eval hnf in PCM unit unitPCMMixin.
Canonical unitEQPCM := Eval hnf in EQPCM unit unitPCMMixin.


(* bools with conjunction are a pcm *)
Definition boolPCMMixin := PCMMixin andbC andbA andTb
                           (fun x y => @id true) (erefl _).
Canonical boolConjPCM := Eval hnf in PCM bool boolPCMMixin.
Canonical boolConjEQPCM := Eval hnf in EQPCM bool boolPCMMixin.

(*************************)
(* PCM-induced pre-order *)
(*************************)

Definition pcm_preord (U : pcm) (x y : U) := exists z, y = x \+ z.

Notation "[ 'pcm' x '<=' y ]" := (@pcm_preord _ x y)
  (at level 0, x, y at level 69,
   format "[ '[hv' 'pcm'  x '/   '  <=  y ']' ]") : type_scope.

Section PleqLemmas.
Variable U : pcm.
Implicit Types x y z : U.

Lemma pleq_unit x : [pcm Unit <= x].
Proof. by exists x; rewrite unitL. Qed.

(* preorder lemmas *)

(* We don't have antisymmetry in general, though for common PCMs *)
(* e.g., union maps, we do have it; but it is proved separately for them *)

Lemma pleq_refl {x} : [pcm x <= x].
Proof. by exists Unit; rewrite unitR. Qed.

Lemma pleq_trans x y z : [pcm x <= y] -> [pcm y <= z] -> [pcm x <= z].
Proof. by case=>a -> [b ->]; exists (a \+ b); rewrite joinA. Qed.

(* monotonicity lemmas *)

Lemma pleq_join2r x x1 x2 : [pcm x1 <= x2] -> [pcm x1 \+ x <= x2 \+ x].
Proof. by case=>a ->; exists a; rewrite joinAC. Qed.

Lemma pleq_join2l x x1 x2 : [pcm x1 <= x2] -> [pcm x \+ x1 <= x \+ x2].
Proof. by rewrite !(joinC x); apply: pleq_join2r. Qed.

Lemma pleq_joinr x1 x2 : [pcm x1 <= x1 \+ x2].
Proof. by exists x2. Qed.

Lemma pleq_joinl x1 x2 : [pcm x2 <= x1 \+ x2].
Proof. by rewrite joinC; apply: pleq_joinr. Qed.

(* validity lemmas *)

Lemma pleqV (x1 x2 : U) : [pcm x1 <= x2] -> valid x2 -> valid x1.
Proof. by case=>x -> /validL. Qed.

Lemma pleq_validL (x x1 x2 : U) :
        [pcm x1 <= x2] -> valid (x \+ x2) -> valid (x \+ x1).
Proof. by case=>a -> V; rewrite (validRE3 V). Qed.

Lemma pleq_validR (x x1 x2 : U) :
        [pcm x1 <= x2] -> valid (x2 \+ x) -> valid (x1 \+ x).
Proof. by rewrite -!(joinC x); apply: pleq_validL. Qed.

(* the next two lemmas only hold for cancellative PCMs *)

Lemma pleq_joinxK (V : cpcm) (x x1 x2 : V) :
        valid (x2 \+ x) -> [pcm x1 \+ x <= x2 \+ x] -> [pcm x1 <= x2].
Proof. by move=>W [a]; rewrite joinAC=>/(joinKx W) ->; exists a. Qed.

Lemma pleq_joinKx (V : cpcm) (x x1 x2 : V) :
        valid (x \+ x2) -> [pcm x \+ x1 <= x \+ x2] -> [pcm x1 <= x2].
Proof. by rewrite !(joinC x); apply: pleq_joinxK. Qed.

End PleqLemmas.

Hint Resolve pleq_unit pleq_refl pleq_joinr pleq_joinl : core.
Prenex Implicits pleq_refl.

(*******************)
(* Local functions *)
(*******************)

Definition local (U : pcm) (f : U -> U -> option U) :=
  forall p x y r, valid (x \+ (p \+ y)) -> f x (p \+ y) = Some r ->
                  valid (r \+ p \+ y) /\ f (x \+ p) y = Some (r \+ p).

Lemma localV U f x y r :
        @local U f -> valid (x \+ y) -> f x y = Some r -> valid (r \+ y).
Proof. by move=>H V E; move: (H Unit x y r); rewrite unitL !unitR; case. Qed.

Lemma idL (U : pcm) : @local U (fun x y => Some x).
Proof. by move=>p x y _ V [<-]; rewrite -joinA. Qed.

(******************)
(* Tuples of PCMs *)
(******************)

(* Often times we need to iterate PCM-product construction, *)
(* but then, due to the Coq policy of reducing destructors *)
(* the iterated projections are not simplified. Thus, it *)
(* makes (some) sense to have primitive product iterations *)
(* for the few common numbers *)

(* Also, products are the construction we use by default *)
(* when pairing resources. It makes sense to use different pairing *)
(* constructions for composing resources vs. when we need a tuple *)
(* PCM in one resource. That way, the lemmas and rewrite rules *)
(* that are used to change the views from a larger resource to a smaller one *)
(* can be prevented from descending and unfolding too much. *)
(* Truth be told, the control of this unfolding should really be done *)
(* by using Opaque and Transparent, if they only worked properly in Coq *)

Inductive Prod3 (U1 U2 U3 : Type) := mk3 {pcm31 : U1; pcm32 : U2; pcm33 : U3}.

Prenex Implicits pcm31 pcm32 pcm33.

Section UPCM3.
Variables U1 U2 U3 : pcm.
Notation tp := (Prod3 U1 U2 U3).

Let uvalid (x : tp) := [&& valid (pcm31 x), valid (pcm32 x) & valid (pcm33 x)].
Let ujoin (x y : tp) := mk3 (pcm31 x \+ pcm31 y) (pcm32 x \+ pcm32 y) (pcm33 x \+ pcm33 y).
Let uunit : tp := mk3 Unit Unit Unit.

Lemma ujoinC x y : ujoin x y = ujoin y x.
Proof. by congr mk3; rewrite joinC. Qed.

Lemma ujoinA x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by congr mk3; rewrite joinA. Qed.

Lemma uvalidL x y : uvalid (ujoin x y) -> uvalid x.
Proof. by rewrite /uvalid; case/and3P; do ![move/validL=>->]. Qed.

Lemma uunitL x : ujoin uunit x = x.
Proof. by case: x=>*; rewrite /uunit /ujoin /= !unitL. Qed.

Lemma uvalidU : uvalid uunit.
Proof. by rewrite /uvalid !valid_unit. Qed.

Definition prod3PCMMixin := PCMMixin ujoinC ujoinA uunitL uvalidL uvalidU.
Canonical prod3_PCM := Eval hnf in PCM (Prod3 U1 U2 U3) prod3PCMMixin.
End UPCM3.

Section UTPCM3.
Variables U1 U2 U3 : tpcm.
Notation tp := (Prod3 U1 U2 U3).

Let uunitb (x : tp) := [&& unitb (pcm31 x), unitb (pcm32 x) & unitb (pcm33 x)].
Let uundef : tp := mk3 undef undef undef.

Lemma uunitbP x : reflect (x = Unit) (uunitb x).
Proof.
rewrite /uunitb !pcmE; case: x=>x1 x2 x3 /=.
do 3![case: unitbP=>[->|H]; last by constructor; case].
by constructor.
Qed.

Lemma uvalid_undef : ~~ valid uundef.
Proof. by rewrite pcmE /valid /= !valid_undef. Qed.

Lemma uundef_join x : uundef \+ x = uundef.
Proof. by rewrite pcmE /= !undef_join. Qed.

Definition prod3TPCMMix := TPCMMixin uunitbP uvalid_undef uundef_join.
Canonical prod3_TPCM := Eval hnf in TPCM (Prod3 U1 U2 U3) prod3TPCMMix.
End UTPCM3.

(* And for 4 *)

Inductive Prod4 (U1 U2 U3 U4 : Type) := mk4 {pcm41 : U1; pcm42 : U2; pcm43 : U3; pcm44 : U4}.

Prenex Implicits pcm41 pcm42 pcm43 pcm44.

Section UPCM4.
Variables U1 U2 U3 U4 : pcm.
Notation tp := (Prod4 U1 U2 U3 U4).

Let uvalid (x : tp) := [&& valid (pcm41 x), valid (pcm42 x),
                           valid (pcm43 x) & valid (pcm44 x)].
Let ujoin (x y : tp) := mk4 (pcm41 x \+ pcm41 y) (pcm42 x \+ pcm42 y)
                            (pcm43 x \+ pcm43 y) (pcm44 x \+ pcm44 y).
Let uunit : tp := mk4 Unit Unit Unit Unit.

Lemma ujoinC4 x y : ujoin x y = ujoin y x.
Proof. by congr mk4; rewrite joinC. Qed.

Lemma ujoinA4 x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by congr mk4; rewrite joinA. Qed.

Lemma uvalidL4 x y : uvalid (ujoin x y) -> uvalid x.
Proof. by rewrite /uvalid; case/and4P; do ![move/validL=>->]. Qed.

Lemma uunitL4 x : ujoin uunit x = x.
Proof. by case: x=>*; rewrite /uunit /ujoin /= !unitL. Qed.

Lemma uvalidU4 : uvalid uunit.
Proof. by rewrite /uvalid !valid_unit. Qed.

Definition prod4PCMMixin := PCMMixin ujoinC4 ujoinA4 uunitL4 uvalidL4 uvalidU4.
Canonical prod4_PCM := Eval hnf in PCM (Prod4 U1 U2 U3 U4) prod4PCMMixin.
End UPCM4.

Section UTPCM4.
Variables U1 U2 U3 U4 : tpcm.
Notation tp := (Prod4 U1 U2 U3 U4).

Let uunitb (x : tp) := [&& unitb (pcm41 x), unitb (pcm42 x),
                           unitb (pcm43 x) & unitb (pcm44 x)].
Let uundef : tp := mk4 undef undef undef undef.

Lemma uunitbP4 x : reflect (x = Unit) (uunitb x).
Proof.
rewrite /uunitb !pcmE; case: x=>x1 x2 x3 x4 /=.
do 4![case: unitbP=>[->|H] /=; last by constructor; case].
by constructor.
Qed.

Lemma uvalid_undef4 : ~~ valid uundef.
Proof. by rewrite pcmE /valid /= !valid_undef. Qed.

Lemma uundef_join4 x : uundef \+ x = uundef.
Proof. by rewrite pcmE /= !undef_join. Qed.

Definition prod4TPCMMix := TPCMMixin uunitbP4 uvalid_undef4 uundef_join4.
Canonical prod4_TPCM := Eval hnf in TPCM (Prod4 U1 U2 U3 U4) prod4TPCMMix.
End UTPCM4.

(* And for 5 *)

Inductive Prod5 (U1 U2 U3 U4 U5 : Type) :=
  mk5 {pcm51 : U1; pcm52 : U2; pcm53 : U3; pcm54 : U4; pcm55 : U5}.

Prenex Implicits pcm51 pcm52 pcm53 pcm54 pcm55.

Section UPCM5.
Variables U1 U2 U3 U4 U5 : pcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).

Let uvalid (x : tp) := [&& valid (pcm51 x), valid (pcm52 x),
                           valid (pcm53 x), valid (pcm54 x) & valid (pcm55 x)].
Let ujoin (x y : tp) := mk5 (pcm51 x \+ pcm51 y) (pcm52 x \+ pcm52 y)
                            (pcm53 x \+ pcm53 y) (pcm54 x \+ pcm54 y)
                            (pcm55 x \+ pcm55 y).
Let uunit : tp := mk5 Unit Unit Unit Unit Unit.

Lemma ujoinC5 x y : ujoin x y = ujoin y x.
Proof. by congr mk5; rewrite joinC. Qed.

Lemma ujoinA5 x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by congr mk5; rewrite joinA. Qed.

Lemma uvalidL5 x y : uvalid (ujoin x y) -> uvalid x.
Proof. by rewrite /uvalid; case/and5P; do ![move/validL=>->]. Qed.

Lemma uunitL5 x : ujoin uunit x = x.
Proof. by case: x=>*; rewrite /uunit /ujoin /= !unitL. Qed.

Lemma uvalidU5 : uvalid uunit.
Proof. by rewrite /uvalid !valid_unit. Qed.

Definition prod5PCMMixin := PCMMixin ujoinC5 ujoinA5 uunitL5 uvalidL5 uvalidU5.
Canonical prod5_PCM := Eval hnf in PCM (Prod5 U1 U2 U3 U4 U5) prod5PCMMixin.
End UPCM5.

Section UTPCM5.
Variables U1 U2 U3 U4 U5 : tpcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).

Let uunitb (x : tp) := [&& unitb (pcm51 x), unitb (pcm52 x),
                           unitb (pcm53 x), unitb (pcm54 x) & unitb (pcm55 x)].
Let uundef : tp := mk5 undef undef undef undef undef.

Lemma uunitbP5 x : reflect (x = Unit) (uunitb x).
Proof.
rewrite /uunitb !pcmE; case: x=>x1 x2 x3 x4 x5 /=.
do ![case: unitbP=>[->|H] /=; last by constructor; case].
by constructor.
Qed.

Lemma uvalid_undef5 : ~~ valid uundef.
Proof. by rewrite pcmE /valid /= !valid_undef. Qed.

Lemma uundef_join5 x : uundef \+ x = uundef.
Proof. by rewrite pcmE /= !undef_join. Qed.

Definition prod5TPCMMix := TPCMMixin uunitbP5 uvalid_undef5 uundef_join5.
Canonical prod5_TPCM := Eval hnf in TPCM (Prod5 U1 U2 U3 U4 U5) prod5TPCMMix.
End UTPCM5.

(* And for 6 *)

Inductive Prod6 (U1 U2 U3 U4 U5 U6 : Type) :=
  mk6 {pcm61 : U1; pcm62 : U2; pcm63 : U3;
       pcm64 : U4; pcm65 : U5; pcm66 : U6}.

Prenex Implicits pcm61 pcm62 pcm63 pcm64 pcm65 pcm66.

Section UPCM6.
Variables U1 U2 U3 U4 U5 U6 : pcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).

Let uvalid (x : tp) := [&& valid (pcm61 x), valid (pcm62 x), valid (pcm63 x),
                           valid (pcm64 x), valid (pcm65 x) & valid (pcm66 x)].
Let ujoin (x y : tp) := mk6 (pcm61 x \+ pcm61 y) (pcm62 x \+ pcm62 y)
                            (pcm63 x \+ pcm63 y) (pcm64 x \+ pcm64 y)
                            (pcm65 x \+ pcm65 y) (pcm66 x \+ pcm66 y).
Let uunit : tp := mk6 Unit Unit Unit Unit Unit Unit.

Lemma ujoinC6 x y : ujoin x y = ujoin y x.
Proof. by congr mk6; rewrite joinC. Qed.

Lemma ujoinA6 x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by congr mk6; rewrite joinA. Qed.

Lemma uvalidL6 x y : uvalid (ujoin x y) -> uvalid x.
Proof. by rewrite /uvalid; case/and6P; do ![move/validL=>->]. Qed.

Lemma uunitL6 x : ujoin uunit x = x.
Proof. by case: x=>*; rewrite /uunit /ujoin /= !unitL. Qed.

Lemma uvalidU6 : uvalid uunit.
Proof. by rewrite /uvalid !valid_unit. Qed.

Definition prod6PCMMixin := PCMMixin ujoinC6 ujoinA6 uunitL6 uvalidL6 uvalidU6.
Canonical prod6_PCM := Eval hnf in PCM (Prod6 U1 U2 U3 U4 U5 U6) prod6PCMMixin.
End UPCM6.

Section UTPCM6.
Variables U1 U2 U3 U4 U5 U6 : tpcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).

Let uunitb (x : tp) := [&& unitb (pcm61 x), unitb (pcm62 x), unitb (pcm63 x),
                           unitb (pcm64 x), unitb (pcm65 x) & unitb (pcm66 x)].
Let uundef : tp := mk6 undef undef undef undef undef undef.

Lemma uunitbP6 x : reflect (x = Unit) (uunitb x).
Proof.
rewrite /uunitb !pcmE; case: x=>x1 x2 x3 x4 x5 x6 /=.
do ![case: unitbP=>[->|H] /=; last by constructor; case].
by constructor.
Qed.

Lemma uvalid_undef6 : ~~ valid uundef.
Proof. by rewrite pcmE /valid /= !valid_undef. Qed.

Lemma uundef_join6 x : uundef \+ x = uundef.
Proof. by rewrite pcmE /= !undef_join. Qed.

Definition prod6TPCMMix := TPCMMixin uunitbP6 uvalid_undef6 uundef_join6.
Canonical prod6_TPCM := Eval hnf in TPCM (Prod6 U1 U2 U3 U4 U5 U6) prod6TPCMMix.
End UTPCM6.

(* And for 7 *)

Inductive Prod7 (U1 U2 U3 U4 U5 U6 U7 : Type) :=
  mk7 {pcm71 : U1; pcm72 : U2; pcm73 : U3;
       pcm74 : U4; pcm75 : U5; pcm76 : U6; pcm77 : U7}.

Prenex Implicits pcm71 pcm72 pcm73 pcm74 pcm75 pcm76 pcm77.

Section UPCM7.
Variables U1 U2 U3 U4 U5 U6 U7 : pcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).

Let uvalid (x : tp) := [&& valid (pcm71 x), valid (pcm72 x),
                           valid (pcm73 x), valid (pcm74 x),
                           valid (pcm75 x), valid (pcm76 x) &
                           valid (pcm77 x)].
Let ujoin (x y : tp) := mk7 (pcm71 x \+ pcm71 y) (pcm72 x \+ pcm72 y)
                            (pcm73 x \+ pcm73 y) (pcm74 x \+ pcm74 y)
                            (pcm75 x \+ pcm75 y) (pcm76 x \+ pcm76 y)
                            (pcm77 x \+ pcm77 y).
Let uunit : tp := mk7 Unit Unit Unit Unit Unit Unit Unit.

Lemma ujoinC7 x y : ujoin x y = ujoin y x.
Proof. by congr mk7; rewrite joinC. Qed.

Lemma ujoinA7 x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by congr mk7; rewrite joinA. Qed.

Lemma uvalidL7 x y : uvalid (ujoin x y) -> uvalid x.
Proof. by rewrite /uvalid; case/and7P; do ![move/validL=>->]. Qed.

Lemma uunitL7 x : ujoin uunit x = x.
Proof. by case: x=>*; rewrite /uunit /ujoin /= !unitL. Qed.

Lemma uvalidU7 : uvalid uunit.
Proof. by rewrite /uvalid !valid_unit. Qed.

Definition prod7PCMMixin := PCMMixin ujoinC7 ujoinA7 uunitL7 uvalidL7 uvalidU7.
Canonical prod7_PCM := Eval hnf in PCM (Prod7 U1 U2 U3 U4 U5 U6 U7) prod7PCMMixin.
End UPCM7.

Section UTPCM7.
Variables U1 U2 U3 U4 U5 U6 U7 : tpcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).

Let uunitb (x : tp) := [&& unitb (pcm71 x), unitb (pcm72 x), unitb (pcm73 x),
                           unitb (pcm74 x), unitb (pcm75 x), unitb (pcm76 x) &
                           unitb (pcm77 x)].
Let uundef : tp := mk7 undef undef undef undef undef undef undef.

Lemma uunitbP7 x : reflect (x = Unit) (uunitb x).
Proof.
rewrite /uunitb !pcmE; case: x=>x1 x2 x3 x4 x5 x6 x7 /=.
do ![case: unitbP=>[->|H] /=; last by constructor; case].
by constructor.
Qed.

Lemma uvalid_undef7 : ~~ valid uundef.
Proof. by rewrite pcmE /valid /= !valid_undef. Qed.

Lemma uundef_join7 x : uundef \+ x = uundef.
Proof. by rewrite pcmE /= !undef_join. Qed.

Definition prod7TPCMMix := TPCMMixin uunitbP7 uvalid_undef7 uundef_join7.
Canonical prod7_TPCM := Eval hnf in TPCM (Prod7 U1 U2 U3 U4 U5 U6 U7) prod7TPCMMix.
End UTPCM7.


(********************)
(* PCMs and folding *)
(********************)

(* folding functions that are morphisms in the first argument *)

Section PCMfold.
Variables (A : Type) (R : pcm) (a : R -> A -> R).
Hypothesis H : (forall x y k, a (x \+ y) k = a x k \+ y).

(* first a helper lemma *)
Lemma foldl_helper (s1 s2 : seq A) (z0 : R) x :
        foldl a z0 (s1 ++ x :: s2) = foldl a z0 (x :: s1 ++ s2).
Proof.
elim: s1 s2 z0=>[|k ks IH] s2' z0 //=.
rewrite IH /=; congr foldl.
rewrite -[a z0 k]unitL H -[z0]unitL !H.
by rewrite -{2}[a Unit x]unitL H joinCA joinA.
Qed.

Lemma foldl_perm (s1 s2 : seq A) (z0 : R) :
        perm s1 s2 -> foldl a z0 s1 = foldl a z0 s2.
Proof.
move=>P; elim: s1 s2 z0 P=>[|k ks IH] s2 z0 P; first by move/pperm_nil: P=>->.
have K: k \In s2 by apply: pperm_in P _; rewrite InE; left.
case: {K} (In_split K) P=>x [y] ->{s2} /= /pperm_cons_cat_cons P.
by rewrite foldl_helper //=; apply: IH.
Qed.

Lemma foldl_init (s : seq A) (x y : R) :
        foldl a (x \+ y) s = foldl a x s \+ y.
Proof. by elim: s x y=>[|k s IH] x y //=; rewrite H IH. Qed.

End PCMfold.
