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

From HB Require Import structures.
From Stdlib Require Import ssreflect ssrbool ssrfun Setoid.
From mathcomp Require Import ssrnat eqtype seq bigop choice.
From mathcomp Require Import fintype finset finfun.
From pcm Require Import options axioms prelude seqperm pred seqext.

Declare Scope pcm_scope.
Delimit Scope pcm_scope with pcm.
Open Scope pcm_scope.

(*******************************)
(* Partial Commutative Monoids *)
(*******************************)

Definition pcm_axiom T (valid : T -> bool) (join : T -> T -> T) 
                       (unit : T) (unitb : T -> bool) := 
  Prod6 (commutative join)
        (associative join)
        (left_id unit join)
        (* monotonicity of valid *)
        (forall x y, valid (join x y) -> valid x)
        (* unit is valid *)
        (valid unit)
        (* (as a matter of principle, we make points decidable) *)
        (forall x, reflect (x = unit) (unitb x)).

HB.mixin Record isPCM T := {
  valid : T -> bool;
  join : T -> T -> T;
  Unit : T;
  unitb : T -> bool;
  pcm_subproof : pcm_axiom valid join Unit unitb}.

#[short(type="pcm")]
HB.structure Definition PCM := {T of isPCM T}.

(* Infix "\+" := join (at level 43, left associativity) : pcm_scope. *)
Infix "\+" := join (at level 50, left associativity) : pcm_scope.

Arguments Unit {s}.
Arguments valid {s} : simpl never.
Prenex Implicits join Unit.

Lemma joinC {U} : commutative (@join U). Proof. by case: (@pcm_subproof U). Qed.
Lemma joinA {U} : associative (@join U). Proof. by case: (@pcm_subproof U). Qed.
Lemma unitL {U} : left_id Unit (@join U). Proof. by case: (@pcm_subproof U). Qed.
Lemma valid_unit {U} : valid (@Unit U). Proof. by case: (@pcm_subproof U). Qed.
Lemma validL {U : pcm} {x y : U} : valid (x \+ y) -> valid x.
Proof. by case: (@pcm_subproof U) x y. Qed.
Lemma unitbP {U : pcm} {x : U} : reflect (x = Unit) (unitb x).
Proof. by case: (@pcm_subproof U). Qed.

Section DerivedLemmas.
Variables U V : pcm.

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
Proof. by rewrite -joinA (joinC y) joinA. Qed.

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof. by rewrite joinA (joinC x) -joinA. Qed.

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof. by rewrite joinC; apply: validL. Qed.

(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma validE2 (x y : U) : valid (x \+ y) -> 
        (valid x * valid y) * (valid (x \+ y) * valid (y \+ x)).
Proof. by move=>X; rewrite (validL X) (validR X) X joinC X. Qed.

Lemma unitR (x : U) : x \+ Unit = x.
Proof. by rewrite joinC unitL. Qed.

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

End DerivedLemmas.

Arguments unitL {U}.
Arguments unitR {U}.

#[export]
Hint Resolve valid_unit : core.

Section UnfoldingRules.
Variable U : pcm.

Lemma pcm_joinE (x y : U) : x \+ y = isPCM.join (PCM.class U) x y.
Proof. by []. Qed.

Lemma pcm_validE (x : U) : valid x = isPCM.valid (PCM.class U) x.
Proof. by []. Qed.

Lemma pcm_unitE : Unit = isPCM.Unit (PCM.class U).
Proof. by []. Qed.

Lemma unitb0 : unitb (Unit : U).
Proof. by case: unitbP. Qed.

Definition pcmE := (pcm_joinE, pcm_validE, pcm_unitE, unitb0).

(* also a simple rearrangment equation *)
Definition pull (x y : U) := (joinC y x, joinCA y x).

End UnfoldingRules.


(*********************)
(* Cancellative PCMs *)
(*********************)

(* predicate precision for arbitrary PCM U *)

Definition precise (U : pcm) (P : U -> Prop) :=
  forall s1 s2 t1 t2,
    valid (s1 \+ t1) -> P s1 -> P s2 ->
    s1 \+ t1 = s2 \+ t2 -> s1 = s2.

Definition cpcm_axiom (U : pcm) := 
  forall x1 x2 x : U, 
     valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2.

HB.mixin Record isCPCM U of PCM U := {
  cpcm_subproof : cpcm_axiom U}. 

#[short(type="cpcm")]
HB.structure Definition CPCM := {U of PCM U & isCPCM U}.

Lemma joinKx (U : cpcm) {x1 x2 x : U} :
        valid (x1 \+ x) -> x1 \+ x = x2 \+ x -> x1 = x2.
Proof. by apply: cpcm_subproof. Qed.


Section CPCMLemmas.
Variable U : cpcm.

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
move=>H V H1 H2 E; rewrite (joinC s1) (joinC s2) in E V.
by rewrite !(cancPL H V H1 H2 E).
Qed.

End CPCMLemmas.

(****************)
(* Conical PCMs *)
(****************)

(* commutative monoid is conical if *)
(* x+y=0 implies that x=y=0, for any elements x,y *)
(* https://en.wikipedia.org/wiki/Refinement_monoid *)

Definition pcmc_axiom (U : pcm) :=
  forall x1 x2 : U, unitb (x1 \+ x2) -> unitb x1 && unitb x2.

HB.mixin Record isPCMC U of PCM U := {
  pcmc_subproof : pcmc_axiom U}. 

#[short(type="pcmc")]
HB.structure Definition PCMC := {U of PCM U & isPCMC U}.

Section Repack.
Context {U : pcmc}.
Implicit Type x : U.

Lemma join00 {x1 x2} : unitb (x1 \+ x2) -> unitb x1 && unitb x2.
Proof. by move/pcmc_subproof. Qed.

Lemma join0L {x1 x2} : unitb (x1 \+ x2) -> unitb x1.
Proof. by case/join00/andP. Qed.

Lemma join0R {x1 x2} : unitb (x1 \+ x2) -> unitb x2.
Proof. by case/join00/andP. Qed.

Lemma join0E {x1 x2 : U} : unitb (x1 \+ x2) = unitb x1 && unitb x2.
Proof.
apply/idP/idP; first by apply/join00.
by case/andP=>/unitbP -> /unitbP ->; apply/unitbP; rewrite unitL.
Qed.

Lemma join0I {x1 x2} : x1 \+ x2 = Unit -> x1 = Unit /\ x2 = Unit.
Proof. by case/unitbP/join00/andP; split; apply/unitbP. Qed.
End Repack.

(***************)
(* Topped PCMs *)
(***************)

(* PCM with an explicit undef value *)
(* we and undef elemeent and function undefb *)
(* to test decidably if an element is undef *)


Definition tpcm_axiom (U : pcm) (undef : U) 
                      (undefb : U -> bool) := 
  Prod3 (forall x : U, reflect (x = undef) (undefb x))
        (~~ valid undef) 
        (forall x : U, undef \+ x = undef).

HB.mixin Record isTPCM U of PCM U := {
  undef : U;
  undefb : U -> bool;
  tpcm_subproof : tpcm_axiom undef undefb}.

#[short(type="tpcm")]
HB.structure Definition TPCM := {U of PCM U & isTPCM U}.

Lemma undefbP (U : tpcm) {x : U} : reflect (x = undef) (undefb x).
Proof. by case: (@tpcm_subproof U). Qed.

Lemma valid_undefN {U} : ~~ valid (@undef U).
Proof. by case: (@tpcm_subproof U). Qed.

Lemma undef_join (U : tpcm) (x : U) : undef \+ x = undef.
Proof. by case: (@tpcm_subproof U). Qed.

Section TPCMLemmas.
Variable U : tpcm.

Lemma undefbE (f : U) : f = undef <-> undefb f.
Proof. by case: undefbP. Qed.

Lemma undefb_undef : undefb (undef : U).
Proof. by case: undefbP. Qed.

Lemma valid_undef : valid (undef : U) = false.
Proof. by rewrite (negbTE valid_undefN). Qed.

Lemma join_undef (x : U) : x \+ undef = undef.
Proof. by rewrite joinC undef_join. Qed.

Lemma undef0 : (undef : U) <> (Unit : U).
Proof. by move=>E; move: (@valid_unit U); rewrite -E valid_undef. Qed.

Lemma unitb_undef : unitb (undef : U) = false.
Proof. by case: unitbP =>// /undef0. Qed.

Lemma undefD (x : U) : decidable (x = undef). 
Proof.
case D: (undefb x).
- by left; move/undefbP: D.
by right; move/undefbP: D.
Qed.

End TPCMLemmas.

Definition tpcmE := (undef_join, join_undef, valid_undef, 
                     unitb_undef, undefb_undef).


(***************)
(* Normal TPCM *)
(***************)

(* TPCM whose only invalid element is undef *)

Definition normal_tpcm_axiom (U : tpcm) := forall x : U, valid x \/ x = undef. 

HB.mixin Record isNormal_TPCM U of TPCM U := {
  normal_tpcm_subproof : normal_tpcm_axiom U}.

#[short(type="normal_tpcm")]
HB.structure Definition Normal_TPCM := {U of TPCM U & isNormal_TPCM U}.

(* branching on valid x or x = undef *)
Variant normal_spec {U : normal_tpcm} (x : U) : 
          bool -> bool -> bool -> Type := 
| normal_undef of x = undef : normal_spec x false true false
| normal_valid of valid x : normal_spec x true false (unitb x).

Lemma normalP {U : normal_tpcm} (x : U) : 
        normal_spec x (valid x) (undefb x) (unitb x).
Proof.
case: undefbP=>[->|N].
- by rewrite valid_undef unitb_undef; apply: normal_undef.
have V : (valid x) by case: (normal_tpcm_subproof x) N.
by rewrite V; apply: normal_valid.
Qed.

Lemma undefNV {U : normal_tpcm} (x : U) : undefb x = ~~ valid x. 
Proof. by case: normalP. Qed.

Lemma undefVN {U : normal_tpcm} (x : U) : valid x = ~~ undefb x.
Proof. by case: normalP. Qed.

(* branching on valid x or x = undef or x = unit *)
Variant normal0_spec {U : normal_tpcm} (x : U) : 
          bool -> bool -> bool -> Type := 
| normal0_undef of x = undef : normal0_spec x false true false
| normal0_unit of x = Unit : normal0_spec x true false true
| normal0_valid of valid x & x <> Unit : normal0_spec x true false false.

Lemma normalP0 {U : normal_tpcm} (x : U) : 
        normal0_spec x (valid x) (undefb x) (unitb x).
Proof.
case: (normalP x)=>[->|V]; first by apply: normal0_undef.
case E: (unitb x); move/unitbP: E;
by [apply: normal0_unit|apply: normal0_valid].
Qed.


(***************************************)
(* PCMs with combination of properties *)
(***************************************)

(* pcm with decidable equality *)
#[short(type="eqpcm")]
HB.structure Definition EQPCM := {U of Equality U & PCM U}. 

(* cancellative pcm with decidable equality *)
#[short(type="eqcpcm")]
HB.structure Definition EQCPCM := {U of CPCM U & EQPCM U}.

(* tpcm with decidable equality *)
#[short(type="eqtpcm")]
HB.structure Definition EQTPCM := {U of TPCM U & EQPCM U}.

(* normal tpcm with decidable equality *)
#[short(type="normal_eqtpcm")]
HB.structure Definition Normal_EQTPCM := {U of Normal_TPCM U & EQPCM U}. 

(* cancellative tpcm *)
#[short(type="ctpcm")]
HB.structure Definition CTPCM := {U of CPCM U & TPCM U}.

(* cancellative tpcm with decidable equality *)
#[short(type="eqctpcm")]
HB.structure Definition EQCTPCM := {U of Equality U & CTPCM U}. 

(* normal cancellative tpcm *)
#[short(type="normal_ctpcm")]
HB.structure Definition Normal_CTPCM := {U of Normal_TPCM U & CPCM U}.

(* normal cancellative tpcm with decidable equality *)
#[short(type="normal_eqctpcm")]
HB.structure Definition Normal_EQCTPCM := {U of Normal_TPCM U & EQCPCM U}.

(* adding conical variants *)

(* conical pcm with decidable equality *)
#[short(type="eqpcmc")]
HB.structure Definition EQPCMC := {U of Equality U & PCMC U}. 

(* conical cancellative pcm *)
#[short(type="cpcmc")]
HB.structure Definition CPCMC := {U of CPCM U & PCMC U}.

(* conical tpcm *)
#[short(type="tpcmc")]
HB.structure Definition TPCMC := {U of TPCM U & PCMC U}.

(* conical normal tpcm *)
#[short(type="normal_tpcmc")]
HB.structure Definition Normal_TPCMC := {U of Normal_TPCM U & PCMC U}.

(* conical with two extra properties *)

(* conical cancellative pcm with decidable equality *)
#[short(type="eqcpcmc")]
HB.structure Definition EQCPCMC := {U of CPCM U & EQPCMC U}.

(* conical tpcm with decidable equality *)
#[short(type="eqtpcmc")]
HB.structure Definition EQTPCMC := {U of TPCMC U & EQPCM U}.

(* conical cancellative tpcm *)
#[short(type="ctpcmc")]
HB.structure Definition CTPCMC := {U of TPCMC U & CTPCM U}. 

(* conical with three extra properties *)

(* conical normal tpcm with decidable equality *)
#[short(type="normal_eqtpcmc")]
HB.structure Definition Normal_EQTPCMC := {U of Normal_TPCMC U & EQPCM U}.

(* conical normal cancellative tpcm *)
#[short(type="normal_ctpcmc")]
HB.structure Definition Normal_CTPCMC := {U of Normal_TPCMC U & CTPCM U}. 

(* conical cancellative tpcm with decidable equality *)
#[short(type="eqctpcmc")]
HB.structure Definition EQCTPCMC := {U of EQTPCMC U & CTPCM U}. 

(* conical with four extra properties *)

(* conical normal cancellative tpcm with decidable equality *)
#[short(type="normal_eqctpcmc")]
HB.structure Definition Normal_EQCTPCMC := {U of Normal_CTPCM U & EQPCMC U}. 


(***************************************)
(* Support for big operators over PCMs *)
(***************************************)

(* U has the laws of commutative monoids from bigop *)
HB.instance Definition _ (U : pcm) := 
  Monoid.isComLaw.Build U Unit join joinA joinC unitL.

Section BigPartialMorph.
Variables (R1 : Type) (R2 : pcm) (K : R1 -> R2 -> Type) (f : R2 -> R1).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Hypotheses (f_op : forall x y : R2, valid (x \+ y) -> f (x \+ y) = op1 (f x) (f y))
           (f_id : f Unit = id1).

Lemma big_pmorph I r (P : pred I) F :
        valid (\big[join/Unit]_(i <- r | P i) F i) ->
        f (\big[join/Unit]_(i <- r | P i) F i) =
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

(* we use isPCM to build a PCM over a type *)
(* if the type has other characteristics, e.g. equality *)
(* the appropriate structure is built automatically *)
(* e.g., the following builds both the PCM and the EQPCM *)
(* eqpcm instance is automatically inferred *)
Lemma nat_is_pcm : pcm_axiom xpredT addn 0 (eq_op^~ 0).
Proof. by split=>//; [apply:addnC|apply:addnA|apply:(@eqP _^~_)]. Qed.
HB.instance Definition natPCM : isPCM nat := isPCM.Build nat nat_is_pcm. 
(* Check (PCM.clone nat _). *)

Lemma nat_is_conical : pcmc_axiom nat.
Proof.
move=>x y /unitbP/eqP; rewrite addn_eq0.
by case/andP=>/eqP -> /eqP ->. 
Qed.
HB.instance Definition _ := isPCMC.Build nat nat_is_conical.

(* nats are pcm with multiplication too *)
(* but the instance isn't declared canonical as natPCM already is *)
Lemma nat_is_mulpcm : pcm_axiom xpredT mult 1 (eq_op^~ 1).
Proof. by split=>//; [apply:mulnC|apply:mulnA|apply:mul1n|apply:(@eqP _^~_)]. Qed.
HB.instance Definition nat_mulPCM : isPCM nat := isPCM.Build nat nat_is_mulpcm.

(* nats with max too *)
Lemma nat_is_maxpcm : pcm_axiom xpredT maxn 0 (eq_op^~ 0).
Proof. by split=>//; [apply:maxnC|apply:maxnA|apply:max0n|apply:(@eqP _^~_)]. Qed.
HB.instance Definition nat_maxPCM : isPCM nat := isPCM.Build nat nat_is_maxpcm. 

(* bools with disjunction *)
(* eqpcm automatically inferred *)
Lemma bool_is_disjpcm : pcm_axiom xpredT orb false (eq_op^~ false).
Proof. by split=>//; [apply:orbC|apply:orbA|apply:(@eqP _^~_)]. Qed.
HB.instance Definition bool_disjPCM : isPCM bool := 
  isPCM.Build bool bool_is_disjpcm.
(* Check (EQPCM.clone bool _). *)

Lemma bool_is_conical : pcmc_axiom bool.
Proof. by case; case. Qed.
HB.instance Definition _ := isPCMC.Build bool bool_is_conical.

(* bools with conjunction *)
(* but the instance isn't declared canonical as boolPCM alread is *)
Lemma bool_is_pcm : pcm_axiom xpredT andb true (eq_op^~ true).
Proof. by split=>//; [apply:andbC|apply:andbA|apply:(@eqP _^~_)]. Qed.
HB.instance Definition boolPCM : isPCM bool := isPCM.Build bool bool_is_pcm.

(* positive nats under max *)
Section PosNatMax.
Definition posNat := sig (fun x => x > 0).

Definition pos_valid := [fun x : posNat => true].
Definition pos_unit : posNat := Sub 1 (leqnn 1).
Definition pos_unitb := [fun x : posNat => val x == 1].
Lemma max_pos (x y : posNat) : maxn (val x) (val y) > 0.
Proof. by case: x y=>x pfx [y pfy]; rewrite leq_max pfx pfy. Qed.
Definition pos_join := [fun x y : posNat =>
  Sub (maxn (val x) (val y)) (max_pos x y) : posNat].

Lemma posnat_is_pcm : pcm_axiom pos_valid pos_join pos_unit pos_unitb.
Proof.
split=>[x y|x y z|x|||x] //.
- by apply/eqP; rewrite -val_eqE /= maxnC. 
- by apply/eqP; rewrite -val_eqE /= maxnA. 
- by apply/eqP; rewrite -val_eqE; apply/eqP/maxn_idPr; case: x.
by apply/eqP.
Qed.

HB.instance Definition _ : isPCM posNat := isPCM.Build posNat posnat_is_pcm.
(* inherit equality type from sig and nat *)
HB.instance Definition _ := Equality.copy posNat _.
End PosNatMax.

Arguments pos_unit /.

(* unit is a PCM, but not a TPCM, as there is no undefined element. *)
(* we'll have to lift with option types for that *)
Section UnitPCM.
Definition unit_valid := [fun x : unit => true].
Definition unit_join := [fun x y : unit => tt].
Definition unit_unit := tt.
Definition unit_unitb := [fun x : unit => true].

Lemma unit_is_pcm : pcm_axiom unit_valid unit_join unit_unit unit_unitb.
Proof. by split=>//; case=>//; apply/eqP. Qed.

HB.instance Definition _ : isPCM unit := isPCM.Build unit unit_is_pcm.
End UnitPCM.

Arguments unit_unit /.

(***********************)
(* Option PCM and TPCM *)
(***********************)

Section OptionTPCM.
Variables U : pcm.

Definition ovalid := [fun x : option U =>
  if x is Some a then valid a else false].
Definition ojoin := [fun x y : option U =>
  if x is Some a then
    if y is Some b then Some (a \+ b) else None
    else None]. 
Definition ounit : option U := Some Unit.
Definition ounitb := [fun x : option U =>
  if x is Some v then unitb v else false].
Definition oundef : option U := None.
Definition oundefb := [fun x : option U =>
  if x is Some a then false else true].

Lemma option_is_pcm : pcm_axiom ovalid ojoin ounit ounitb.
Proof.
split=>[x y|x y z|x|x y||x].
- by case: x; case: y=>//=b a; rewrite joinC. 
- by case: x; case: y; case: z=>//=c b a; rewrite joinA. 
- by case: x=>//=a; rewrite unitL. 
- by case x=>//=a; case: y=>//=b /validL. 
- by rewrite /= valid_unit. 
case: x=>[a|] /=; last by constructor.
by case: unitbP=>[->|H]; constructor=>//; case.
Qed.

HB.instance Definition _ : isPCM (option U) := 
  isPCM.Build (option U) option_is_pcm.

Lemma option_is_tpcm : tpcm_axiom oundef oundefb.
Proof. by split=>//; case=>[a|]; constructor. Qed.

HB.instance Definition _ : isTPCM (option U) := 
  isTPCM.Build (option U) option_is_tpcm.
End OptionTPCM.

Arguments ounit /. 
Arguments oundef /.

(* option preserves equality *)
HB.instance Definition _ (U : eqpcm) := PCM.copy (option U) _.
(* Check (EQPCM.clone (option nat) _). *)

(* option preserves cancellativity *)
Lemma option_is_cpcm (U : cpcm) : cpcm_axiom (option U).
Proof. by case=>[x|][y|][z|] // V [] /(joinKx V)=>->. Qed.
HB.instance Definition _ (U : cpcm) :=   
  isCPCM.Build (option U) (@option_is_cpcm U).

(* option is normal if U is all valid *)
Lemma option_is_normal (U : pcm) : 
        @valid U =1 xpredT -> normal_tpcm_axiom (option U).
Proof. by move=>E [x|]; [left; rewrite /valid /= E|right]. Qed.

(* option preserves conicity *)
Lemma option_is_conical (U : pcmc) : pcmc_axiom (option U).
Proof. by case=>[x|][y|] //= /unitbP [/unitbP/join00]. Qed.
HB.instance Definition _ (U : pcmc) := 
  isPCMC.Build (option U) (@option_is_conical U).  

(* case analysis infrastructure *)
CoInductive option_pcm_spec (A : pcm) (x y : option A) : 
  option A -> Type := 
| some_case x' y' of x = some x' & y = some y' :
    option_pcm_spec x y (some (x' \+ y'))
| none_case of ~~ valid (x \+ y) : 
    option_pcm_spec x y None.

Lemma optionP (A : pcm) (x y : option A) : option_pcm_spec x y (x \+ y).
Proof.
case: x=>[x|]; case: y=>[y|]=>/=; first by [apply: some_case];
by apply: none_case.
Qed.

(*****************************)
(* Cartesian product of PCMs *)
(*****************************)

Section ProdPCM.
Variables U V : pcm.
Local Notation tp := (U * V)%type.

Definition valid2 := [fun x : tp => valid x.1 && valid x.2].
Definition join2 := [fun x1 x2 : tp => (x1.1 \+ x2.1, x1.2 \+ x2.2)].
Definition unit2 : tp := (Unit, Unit).
Definition unitb2 := [fun x : U * V => unitb x.1 && unitb x.2]. 

Lemma prod_is_pcm : pcm_axiom valid2 join2 unit2 unitb2.
Proof.
split=>[x y|x y z|x|x y||x].
- by rewrite /= (joinC x.1) (joinC x.2). 
- by rewrite /= !joinA. 
- by rewrite /= !unitL -prod_eta. 
- by rewrite /valid2 /=; case/andP=>/validL -> /validL ->.
- by rewrite /valid2 /= !valid_unit. 
case: x=>x1 x2 /=; case: andP=>H; constructor.
- by case: H=>/unitbP -> /unitbP ->.
by case=>X1 X2; elim: H; rewrite X1 X2 !pcmE.
Qed.

HB.instance Definition _ : isPCM (U * V)%type := 
  isPCM.Build (U * V)%type prod_is_pcm. 
End ProdPCM.

(* explicitly extend to eqpcms *)
HB.instance Definition _ (U V : eqpcm) := PCM.copy (U * V)%type _.

Arguments unit2 /.

Lemma prod_is_conical (U V : pcmc) : pcmc_axiom (U * V)%type.
Proof.
case=>x1 x2 [y1 y2] /unitbP [].
case/unitbP/join00/andP=>X1 Y1 /unitbP/join00/andP [X2 Y2]. 
by rewrite /unitb /= X1 X2 Y1 Y2.
Qed.

HB.instance Definition _ (U V : pcmc) := 
  isPCMC.Build (U * V)%type (@prod_is_conical U V).

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

Lemma pcmPV (x : U * V) : valid x = valid x.1 && valid x.2.
Proof. by []. Qed.

Lemma pcmPU : Unit = (Unit, Unit) :> U * V.
Proof. by rewrite pcmE. Qed.

Definition pcmPE := (pcmPJ, pcmFJ, pcmSJ, pcmPV, pcmPU).

End Simplification.

(* We often iterate PCM-products so  *)
(* we provide primitives for small numbers *)

Section Prod3PCM.
Variables U1 U2 U3 : pcm.
Notation tp := (Prod3 U1 U2 U3).
Definition valid3 := [fun x : tp =>
  [&& valid (proj31 x), 
      valid (proj32 x) & 
      valid (proj33 x)]].
Definition join3 := [fun x y : tp =>
  mk3 (proj31 x \+ proj31 y) 
      (proj32 x \+ proj32 y) 
      (proj33 x \+ proj33 y)].
Definition unit3 : tp := mk3 Unit Unit Unit.
Definition unitb3 := [fun x : tp => 
  [&& unitb (proj31 x), 
      unitb (proj32 x) &
      unitb (proj33 x)]].

Lemma prod3_is_pcm : pcm_axiom valid3 join3 unit3 unitb3.
Proof.
split=>[x y|x y z||x y||x] /=.
- by congr mk3; rewrite joinC. 
- by congr mk3; rewrite joinA. 
- by case=>*; rewrite /= !unitL. 
- by case/and3P; do ![move/validL=>->]. 
- by rewrite !valid_unit. 
case: x=>x1 x2 x3 /=.
do ![case: unitbP=>[->|H]; last by constructor; case];
by constructor.
Qed.

HB.instance Definition _ : isPCM (Prod3 U1 U2 U3) := 
  isPCM.Build (Prod3 U1 U2 U3) prod3_is_pcm.
End Prod3PCM.

HB.instance Definition _ (U1 U2 U3 : eqpcm) := 
  PCM.copy (Prod3 U1 U2 U3) _.

Arguments unit3 /.

Lemma prod3_is_conical (U1 U2 U3 : pcmc) : pcmc_axiom (Prod3 U1 U2 U3).
Proof.
case=>x1 x2 x3 [y1 y2 y3] /unitbP [].
case/unitbP/join00/andP=>X1 Y1 /unitbP/join00/andP [X2 Y2]
/unitbP/join00/andP [X3 Y3]. 
by rewrite /unitb /= X1 X2 X3 Y1 Y2 Y3.
Qed.

HB.instance Definition _ (U1 U2 U3 : pcmc) := 
  isPCMC.Build (Prod3 U1 U2 U3) (@prod3_is_conical U1 U2 U3).

Section Prod4PCM.
Variables U1 U2 U3 U4 : pcm.
Notation tp := (Prod4 U1 U2 U3 U4).
Definition valid4 := [fun x : tp =>
  [&& valid (proj41 x), 
      valid (proj42 x),
      valid (proj43 x) & 
      valid (proj44 x)]].
Definition join4 := [fun x y : tp =>
  mk4 (proj41 x \+ proj41 y) 
      (proj42 x \+ proj42 y)
      (proj43 x \+ proj43 y) 
      (proj44 x \+ proj44 y)].
Definition unit4 : tp := mk4 Unit Unit Unit Unit.
Definition unitb4 := [fun x : tp => 
  [&& unitb (proj41 x), 
      unitb (proj42 x),
      unitb (proj43 x) &
      unitb (proj44 x)]].

Lemma prod4_is_pcm : pcm_axiom valid4 join4 unit4 unitb4.
Proof.
split=>[x y|x y z||x y||x] /=.
- by congr mk4; rewrite joinC. 
- by congr mk4; rewrite joinA. 
- by case=>*; rewrite /= !unitL. 
- by case/and4P; do ![move/validL=>->]. 
- by rewrite !valid_unit. 
case: x=>x1 x2 x3 x4 /=.
do ![case: unitbP=>[->|H]; last by constructor; case];
by constructor.
Qed.

HB.instance Definition _ : isPCM (Prod4 U1 U2 U3 U4) := 
  isPCM.Build (Prod4 U1 U2 U3 U4) prod4_is_pcm.
End Prod4PCM.

HB.instance Definition _ (U1 U2 U3 U4 : eqpcm) := 
  PCM.copy (Prod4 U1 U2 U3 U4) _.

Arguments unit4 /.

Lemma prod4_is_conical (U1 U2 U3 U4 : pcmc) : pcmc_axiom (Prod4 U1 U2 U3 U4).
Proof.
case=>x1 x2 x3 x4 [y1 y2 y3 y4] /unitbP [].
case/unitbP/join00/andP=>X1 Y1 /unitbP/join00/andP [X2 Y2]
/unitbP/join00/andP [X3 Y3] /unitbP/join00/andP [X4 Y4]. 
by rewrite /unitb /= X1 X2 X3 X4 Y1 Y2 Y3 Y4.
Qed.

HB.instance Definition _ (U1 U2 U3 U4 : pcmc) := 
  isPCMC.Build (Prod4 U1 U2 U3 U4) (@prod4_is_conical U1 U2 U3 U4).

Section Prod5PCM.
Variables U1 U2 U3 U4 U5 : pcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).

Definition valid5 := [fun x : tp =>
  [&& valid (proj51 x), 
      valid (proj52 x),
      valid (proj53 x), 
      valid (proj54 x) & 
      valid (proj55 x)]].
Definition join5 := [fun x y : tp =>
  mk5 (proj51 x \+ proj51 y) 
      (proj52 x \+ proj52 y)
      (proj53 x \+ proj53 y) 
      (proj54 x \+ proj54 y)
      (proj55 x \+ proj55 y)].
Definition unit5 : tp := mk5 Unit Unit Unit Unit Unit.
Definition unitb5 := [fun x : tp =>
  [&& unitb (proj51 x), 
      unitb (proj52 x),
      unitb (proj53 x),
      unitb (proj54 x) &
      unitb (proj55 x)]].

Lemma prod5_is_pcm : pcm_axiom valid5 join5 unit5 unitb5.
Proof.
split=>[x y|x y z||x y||x] /=.
- by congr mk5; rewrite joinC. 
- by congr mk5; rewrite joinA. 
- by case=>*; rewrite /= !unitL. 
- by case/and5P; do ![move/validL=>->]. 
- by rewrite !valid_unit. 
case: x=>x1 x2 x3 x4 x5 /=.
do ![case: unitbP=>[->|H]; last by constructor; case];
by constructor.
Qed.

HB.instance Definition _ : isPCM (Prod5 U1 U2 U3 U4 U5) := 
  isPCM.Build (Prod5 U1 U2 U3 U4 U5) prod5_is_pcm.
End Prod5PCM.

HB.instance Definition _ (U1 U2 U3 U4 U5 : eqpcm) := 
  PCM.copy (Prod5 U1 U2 U3 U4 U5) _.

Arguments unit5 /.

Lemma prod5_is_conical (U1 U2 U3 U4 U5 : pcmc) : 
        pcmc_axiom (Prod5 U1 U2 U3 U4 U5).
Proof.
case=>x1 x2 x3 x4 x5 [y1 y2 y3 y4 y5] /unitbP [].
case/unitbP/join00/andP=>X1 Y1 /unitbP/join00/andP [X2 Y2]
/unitbP/join00/andP [X3 Y3 ]/unitbP/join00/andP [X4 Y4]
/unitbP/join00/andP [X5 Y5].
by rewrite /unitb /= X1 X2 X3 X4 X5 Y1 Y2 Y3 Y4 Y5.
Qed.

HB.instance Definition _ (U1 U2 U3 U4 U5 : pcmc) := 
  isPCMC.Build (Prod5 U1 U2 U3 U4 U5) (@prod5_is_conical U1 U2 U3 U4 U5).

Section Prod6PCM.
Variables U1 U2 U3 U4 U5 U6 : pcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).

Definition valid6 := [fun x : tp =>
  [&& valid (proj61 x), 
      valid (proj62 x), 
      valid (proj63 x),
      valid (proj64 x), 
      valid (proj65 x) & 
      valid (proj66 x)]].
Definition join6 := [fun x y : tp =>
  mk6 (proj61 x \+ proj61 y) 
      (proj62 x \+ proj62 y)
      (proj63 x \+ proj63 y) 
      (proj64 x \+ proj64 y)
      (proj65 x \+ proj65 y) 
      (proj66 x \+ proj66 y)].
Definition unit6 : tp := mk6 Unit Unit Unit Unit Unit Unit.
Definition unitb6 := [fun x : tp =>
  [&& unitb (proj61 x), 
      unitb (proj62 x),
      unitb (proj63 x),
      unitb (proj64 x),
      unitb (proj65 x) &
      unitb (proj66 x)]].

Lemma prod6_is_pcm : pcm_axiom valid6 join6 unit6 unitb6.
Proof.
split=>[x y|x y z||x y||x] /=.
- by congr mk6; rewrite joinC. 
- by congr mk6; rewrite joinA. 
- by case=>*; rewrite /= !unitL. 
- by case/and6P; do ![move/validL=>->]. 
- by rewrite !valid_unit. 
case: x=>x1 x2 x3 x4 x5 x6 /=.
do ![case: unitbP=>[->|H]; last by constructor; case];
by constructor.
Qed.

HB.instance Definition _ : isPCM (Prod6 U1 U2 U3 U4 U5 U6) := 
  isPCM.Build (Prod6 U1 U2 U3 U4 U5 U6) prod6_is_pcm.
End Prod6PCM.

HB.instance Definition _ (U1 U2 U3 U4 U5 U6 : eqpcm) := 
  PCM.copy (Prod6 U1 U2 U3 U4 U5 U6) _.

Arguments unit6 /.

Lemma prod6_is_conical (U1 U2 U3 U4 U5 U6 : pcmc) : 
        pcmc_axiom (Prod6 U1 U2 U3 U4 U5 U6).
Proof.
case=>x1 x2 x3 x4 x5 x6 [y1 y2 y3 y4 y5 y6] /unitbP [].
case/unitbP/join00/andP=>X1 Y1 /unitbP/join00/andP [X2 Y2]
/unitbP/join00/andP [X3 Y3 ]/unitbP/join00/andP [X4 Y4]
/unitbP/join00/andP [X5 Y5] /unitbP/join00/andP [X6 Y6].
by rewrite /unitb /= X1 X2 X3 X4 X5 X6 Y1 Y2 Y3 Y4 Y5 Y6.
Qed.

HB.instance Definition _ (U1 U2 U3 U4 U5 U6 : pcmc) := 
  isPCMC.Build (Prod6 U1 U2 U3 U4 U5 U6) (@prod6_is_conical U1 U2 U3 U4 U5 U6).

Section Prod7PCM.
Variables U1 U2 U3 U4 U5 U6 U7 : pcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).

Definition valid7 := [fun x : tp =>
  [&& valid (proj71 x), 
      valid (proj72 x), 
      valid (proj73 x),
      valid (proj74 x), 
      valid (proj75 x), 
      valid (proj76 x) &
      valid (proj77 x)]].
Definition join7 := [fun x y : tp =>
  mk7 (proj71 x \+ proj71 y) 
      (proj72 x \+ proj72 y)
      (proj73 x \+ proj73 y) 
      (proj74 x \+ proj74 y)
      (proj75 x \+ proj75 y) 
      (proj76 x \+ proj76 y)
      (proj77 x \+ proj77 y)].
Definition unit7 : tp := mk7 Unit Unit Unit Unit Unit Unit Unit.
Definition unitb7 := [fun x : tp =>
  [&& unitb (proj71 x), 
      unitb (proj72 x),
      unitb (proj73 x),
      unitb (proj74 x),
      unitb (proj75 x),
      unitb (proj76 x) &
      unitb (proj77 x)]].

Lemma prod7_is_pcm : pcm_axiom valid7 join7 unit7 unitb7.
Proof.
split=>[x y|x y z||x y||x] /=.
- by congr mk7; rewrite joinC. 
- by congr mk7; rewrite joinA. 
- by case=>*; rewrite /= !unitL. 
- by case/and7P; do ![move/validL=>->]. 
- by rewrite !valid_unit. 
case: x=>x1 x2 x3 x4 x5 x6 x7 /=.
do ![case: unitbP=>[->|H]; last by constructor; case];
by constructor.
Qed.

HB.instance Definition _ : isPCM (Prod7 U1 U2 U3 U4 U5 U6 U7) := 
  isPCM.Build (Prod7 U1 U2 U3 U4 U5 U6 U7) prod7_is_pcm.
End Prod7PCM.

HB.instance Definition _ (U1 U2 U3 U4 U5 U6 U7 : eqpcm) := 
  PCM.copy (Prod7 U1 U2 U3 U4 U5 U6 U7) _.

Arguments unit7 /.

Lemma prod7_is_conical (U1 U2 U3 U4 U5 U6 U7 : pcmc) : 
        pcmc_axiom (Prod7 U1 U2 U3 U4 U5 U6 U7).
Proof.
case=>x1 x2 x3 x4 x5 x6 x7 [y1 y2 y3 y4 y5 y6 y7] /unitbP [].
case/unitbP/join00/andP=>X1 Y1 /unitbP/join00/andP [X2 Y2]
/unitbP/join00/andP [X3 Y3 ]/unitbP/join00/andP [X4 Y4]
/unitbP/join00/andP [X5 Y5] /unitbP/join00/andP [X6 Y6]
/unitbP/join00/andP [X7 Y7].
by rewrite /unitb /= X1 X2 X3 X4 X5 X6 X7 Y1 Y2 Y3 Y4 Y5 Y6 Y7.
Qed.

HB.instance Definition _ (U1 U2 U3 U4 U5 U6 U7 : pcmc) := 
  isPCMC.Build (Prod7 U1 U2 U3 U4 U5 U6 U7) 
               (@prod7_is_conical U1 U2 U3 U4 U5 U6 U7).

(* Finite products of PCMs as functions *)
Section FunPCM.
Variables (T : finType) (Us : T -> pcm).
Notation tp := (forall t, Us t).

Definition fun_valid := [fun f : tp => [forall t, valid (f t)]].
Definition fun_join := [fun f1 f2 : tp => fun t => f1 t \+ f2 t].
Definition fun_unit : tp := fun t => Unit.
Definition fun_unitb := [fun f : tp => [forall t, unitb (f t)]].

Lemma fun_is_pcm : pcm_axiom fun_valid fun_join fun_unit fun_unitb.
Proof.
split=>[f g|f g h|f|f g||f] /=.
- by apply: fext=>t; rewrite joinC.
- by apply: fext=>t; rewrite joinA.
- by apply: fext=>t; rewrite unitL.
- by move/forallP=>V; apply/forallP=>t; apply: validL (V t).
- by apply/forallP=>t; apply: valid_unit.
case: forallP=>H; constructor.
- by apply: fext=>t; apply/unitbP; apply: H.
by move=>H1; elim: H=>t; apply/unitbP; rewrite H1. 
Qed.

HB.instance Definition _ : isPCM (forall t, Us t) := 
  isPCM.Build (forall t, Us t) fun_is_pcm.
End FunPCM.

Arguments fun_unit /.

(* we won't use fun types for any examples *)
(* so we don't need equality or conicity structure on them *)

(* Finite products of PCMs as finfuns *)
(* We will work with this second structure, though *)
(* the one above is needed to state that sel and finfun are morphisms *)
(* (between FunPCM and FinPCM) *)
(* dffun used for inheritance (see finfun.v) *)
Section FinPCM.
Variables (T : finType) (Us : T -> pcm).
Notation tp := {dffun forall t, Us t}.

Definition fin_valid := [fun f : tp => [forall t, valid (sel t f)]].
Definition fin_join := [fun f g : tp => [ffun t => sel t f \+ sel t g]].
Definition fin_unit : tp := [ffun => Unit]. 
Definition fin_unitb := [fun f : tp => [forall t, unitb (sel t f)]].

Lemma ffinprod_is_pcm : pcm_axiom fin_valid fin_join fin_unit fin_unitb.
Proof.
split=>[x y|x y z|x|x y||x] /=. 
- by apply/ffunP=>t; rewrite !ffunE joinC.  
- by apply/ffunP=>t; rewrite /sel !ffunE joinA.
- by apply/ffunP=>t; rewrite /sel !ffunE unitL.
- move/forallP=>H; apply/forallP=>t; move: (H t).
  by rewrite /sel !ffunE=>/validL.
- by apply/forallP=>t; rewrite /sel ffunE valid_unit. 
case H: [forall t, _]; constructor.
- move/forallP: H=>H; apply/ffinP=>t.
  by rewrite sel_fin; move/unitbP: (H t).
move=>E; move/negP: H; apply; apply/forallP=>t.
by rewrite E sel_fin unitb0.
Qed.

HB.instance Definition _ :=
  isPCM.Build {dffun forall t, Us t} ffinprod_is_pcm.
End FinPCM.

HB.instance Definition _ (T : finType) (Us : T -> eqpcm) := 
  PCM.copy {dffun forall t, Us t} _. 

Arguments fin_unit /.

Lemma dffun_is_conical (T : finType) (Us : T -> pcmc) : 
        pcmc_axiom {dffun forall t, Us t}.
Proof.
by move=>x y /forallP H; apply/andP; split; apply/forallP=>t;
move: (H t); rewrite /sel !ffunE; [move/join0L|move/join0R].
Qed.

HB.instance Definition _ (T : finType) (Us : T -> pcmc) := 
  isPCMC.Build {dffun forall t, Us t} (@dffun_is_conical T Us).

(* product of TPCMs is a TPCM *)

(* With TPCMs we could remove the pairs where *)
(* one element is valid and the other is not. *)
(* We will do that later with normalization procedure. *)
(* That will give us a new construction for normalized products *)
(* but we first need to introduce PCM morphisms *)
(* Here, we give non-normalized ones. *)
Section ProdTPCM.
Variables U V : tpcm.
Definition undef2 := (@undef U, @undef V).
Definition undefb2 := [fun x : U * V => undefb x.1 && undefb x.2].

Lemma prod_is_tpcm : tpcm_axiom undef2 undefb2.
Proof.
split=>/=.
- case=>x1 x2; case: andP=>/= H; constructor.
  - by case: H=>/undefbP -> /undefbP ->. 
  by case=>X1 X2; elim: H; rewrite X1 X2 !tpcmE.
- by rewrite /valid /= !valid_undef. 
by case=>x1 x2; rewrite pcmPJ !undef_join.
Qed.

HB.instance Definition _ := isTPCM.Build (U * V)%type prod_is_tpcm.
End ProdTPCM.

Arguments undef2 /.

(* iterated TPCMs *)

Section Prod3TPCM.
Variables U1 U2 U3 : tpcm.
Notation tp := (Prod3 U1 U2 U3).
Definition undef3 : tp := mk3 undef undef undef.
Definition undefb3 := [fun x : tp =>
  [&& undefb (proj31 x), 
      undefb (proj32 x) & 
      undefb (proj33 x)]].

Lemma prod3_is_tpcm : tpcm_axiom undef3 undefb3.
Proof.
split=>[x||x].
- case: x=>x1 x2 x3 /=.
  do ![case: undefbP=>[->|H]; last by constructor; case].
  by constructor.
- by rewrite /valid /= !valid_undef. 
by rewrite pcmE /= !undef_join. 
Qed.

HB.instance Definition _ : isTPCM (Prod3 U1 U2 U3) := 
  isTPCM.Build (Prod3 U1 U2 U3) prod3_is_tpcm.
End Prod3TPCM.

Arguments undef3 /.

Section Prod4TPCM.
Variables U1 U2 U3 U4 : tpcm.
Notation tp := (Prod4 U1 U2 U3 U4).
Definition undef4 : tp := mk4 undef undef undef undef.
Definition undefb4 := [fun x : tp =>
  [&& undefb (proj41 x), 
      undefb (proj42 x),
      undefb (proj43 x) &
      undefb (proj44 x)]].

Lemma prod4_is_tpcm : tpcm_axiom undef4 undefb4.
Proof.
split=>[x||x] /=.
- case: x=>x1 x2 x3 x4 /=.
    do ![case: undefbP=>[->|H]; last by constructor; case].
  by constructor.
- by rewrite /valid /= !valid_undef. 
by rewrite pcmE /= !undef_join. 
Qed.

HB.instance Definition _ : isTPCM (Prod4 U1 U2 U3 U4) := 
  isTPCM.Build (Prod4 U1 U2 U3 U4) prod4_is_tpcm.
End Prod4TPCM.

Arguments undef4 /.

Section Prod5TPCM.
Variables U1 U2 U3 U4 U5 : tpcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).
Definition undef5 : tp := mk5 undef undef undef undef undef.
Definition undefb5 := [fun x : tp =>
  [&& undefb (proj51 x), 
      undefb (proj52 x),
      undefb (proj53 x),
      undefb (proj54 x) &
      undefb (proj55 x)]].

Lemma prod5_is_tpcm : tpcm_axiom undef5 undefb5.
Proof.
split=>[x||x] /=.
- case: x=>x1 x2 x3 x4 x5 /=.
  do ![case: undefbP=>[->|H]; last by constructor; case].
  by constructor.
- by rewrite /valid /= !valid_undef. 
by rewrite pcmE /= !undef_join. 
Qed.

HB.instance Definition _ : isTPCM (Prod5 U1 U2 U3 U4 U5) := 
  isTPCM.Build (Prod5 U1 U2 U3 U4 U5) prod5_is_tpcm.
End Prod5TPCM.

Arguments undef5 /.


Section Prod6TPCM.
Variables U1 U2 U3 U4 U5 U6 : tpcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).
Definition undef6 : tp := mk6 undef undef undef undef undef undef.
Definition undefb6 := [fun x : tp =>
  [&& undefb (proj61 x), 
      undefb (proj62 x),
      undefb (proj63 x),
      undefb (proj64 x),
      undefb (proj65 x) &
      undefb (proj66 x)]].

Lemma prod6_is_tpcm : tpcm_axiom undef6 undefb6.
Proof.
split=>[x||x] /=. 
- case: x=>x1 x2 x3 x4 x5 x6 /=.
  do ![case: undefbP=>[->|H]; last by constructor; case].
  by constructor.
- by rewrite /valid /= !valid_undef. 
by rewrite pcmE /= !undef_join. 
Qed.

HB.instance Definition _ : isTPCM (Prod6 U1 U2 U3 U4 U5 U6) := 
  isTPCM.Build (Prod6 U1 U2 U3 U4 U5 U6) prod6_is_tpcm.
End Prod6TPCM.

Arguments undef6 /.

Section Prod7TPCM.
Variables U1 U2 U3 U4 U5 U6 U7 : tpcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).
Definition undef7 : tp := mk7 undef undef undef undef undef undef undef.
Definition undefb7 := [fun x : tp =>
  [&& undefb (proj71 x), 
      undefb (proj72 x),
      undefb (proj73 x),
      undefb (proj74 x),
      undefb (proj75 x),
      undefb (proj76 x) &
      undefb (proj77 x)]].

Lemma prod7_is_tpcm : tpcm_axiom undef7 undefb7.
Proof.
split=>[x||x].
- case: x=>x1 x2 x3 x4 x5 x6 x7 /=.
  do ![case: undefbP=>[->|H]; last by constructor; case].
  by constructor.
- by rewrite /valid /= !valid_undef. 
by rewrite pcmE /= !undef_join. 
Qed.

HB.instance Definition _ : isTPCM (Prod7 U1 U2 U3 U4 U5 U6 U7) := 
  isTPCM.Build (Prod7 U1 U2 U3 U4 U5 U6 U7) prod7_is_tpcm.
End Prod7TPCM.

Arguments undef7 /.

(* TPCM proofs use function extensionality *)
(* it's TPCM only if T inhabited finite type *)
(* (otherwise valid undef) *)

Definition fun_undef T (Us : T -> tpcm) : forall t, Us t 
  := fun t => undef. 
Arguments fun_undef {T Us} /.

Definition fun_undefb (T : finType) (Us : T -> tpcm) := 
  fun f : forall t, Us t => [forall t, undefb (f t)].
Arguments fun_undefb {T Us} f /.

Section FunTPCM.
Variables (T : ifinType) (Us : T -> tpcm).
Notation tp := (forall t, Us t).

Lemma fun_is_tpcm : tpcm_axiom fun_undef (fun_undefb (Us:=Us)).
Proof. 
split=>[f||f] /=.
- case: forallP=>H; constructor.
  - by apply: fext=>t; apply/undefbP; apply: H.
  by move=>H1; elim: H=>t; apply/undefbP; rewrite H1. 
- by apply/negP=>/forallP/(_ inhab); rewrite valid_undef.
by apply: fext=>t; rewrite /join /= undef_join.
Qed.

HB.instance Definition _ : isTPCM (forall t, Us t) := 
  isTPCM.Build (forall t, Us t) fun_is_tpcm.

End FunTPCM.


(* TPCM only if T inhabited finite type *)
(* (otherwise valid undef) *)
Definition fin_undef (T : finType) (Us : T -> tpcm) 
  : {dffun forall t, Us t} := [ffun t => undef].
Arguments fin_undef {T Us} /.

Definition fin_undefb (T : finType) (Us : T -> tpcm) 
    (x : {dffun forall t, Us t}) := 
  [forall t, undefb (sel t x)].
Arguments fin_undefb {T Us} x /.

Section FinTPCM.
Variables (T : ifinType) (Us : T -> tpcm).
Notation tp := {dffun forall t, Us t}.

Lemma finprod_is_tpcm : tpcm_axiom fin_undef (fin_undefb (Us:=Us)).
Proof.
split=>[x||x] /=.
- case H : [forall t, _]; constructor.
  - move/forallP: H=>H; apply/ffinP=>t.
    by rewrite sel_fin; move/undefbP: (H t).
  move=>E; move/negP: H; apply; apply/forallP=>t.
  by rewrite E sel_fin undefb_undef.
- apply/negP=>/forallP/(_ inhab).
  by rewrite sel_fin valid_undef.
by apply/ffinP=>t; rewrite !sel_fin undef_join. 
Qed.

HB.instance Definition _ : isTPCM tp := 
  isTPCM.Build tp finprod_is_tpcm.
End FinTPCM.

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

Lemma pleq_joinr {x1 x2} : [pcm x1 <= x1 \+ x2].
Proof. by exists x2. Qed.

Lemma pleq_joinl {x1 x2} : [pcm x2 <= x1 \+ x2].
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

#[export]
Hint Resolve pleq_unit pleq_refl pleq_joinr pleq_joinl : core.
Prenex Implicits pleq_refl pleq_joinl pleq_joinr.

(* shorter names *)
Notation pcmR := pleq_refl.
Notation pcmS := pleq_joinr.
Notation pcmO := pleq_joinl.

Lemma pleq_undef (U : tpcm) (x : U) : [pcm x <= undef].
Proof. by exists undef; rewrite join_undef. Qed.

#[export] 
Hint Resolve pleq_undef : core.

(********************)
(* PCMs and folding *)
(********************)

(* folding functions that are morphisms in the first argument *)

Section PCMfoldLeft.
Variables (A : Type) (R : pcm) (a : R -> A -> R).
Hypothesis H : (forall x y k, a (x \+ y) k = a x k \+ y).

(* first a helper lemma *)
Lemma foldl_helper (s1 s2 : seq A) (z0 : R) x :
        foldl a z0 (s1 ++ x :: s2) = foldl a z0 (x :: s1 ++ s2).
Proof.
rewrite foldl_cat /= foldl_cat; congr foldl.
elim: {s2} s1 z0=>[|k ks IH] z0 //=; rewrite IH; congr foldl.
rewrite -[a z0 k]unitL H -[z0]unitL !H.
by rewrite -{2}[a Unit x]unitL H joinCA joinA. 
Qed.

Lemma foldl_perm (s1 s2 : seq A) (z0 : R) :
        perm s1 s2 -> 
        foldl a z0 s1 = foldl a z0 s2.
Proof.
move=>P; elim: s1 s2 z0 P=>[|k ks IH] s2 z0 P; first by move/pperm_nil: P=>->.
have K: k \In s2 by apply: pperm_in P _; rewrite InE; left.
case: {K} (In_split K) P=>x [y] ->{s2} /= /pperm_cons_cat_cons P.
by rewrite foldl_helper //=; apply: IH.
Qed.

Lemma foldl_init (s : seq A) (x y : R) :
        foldl a (x \+ y) s = foldl a x s \+ y.
Proof. by elim: s x y=>[|k s IH] x y //=; rewrite H IH. Qed.

End PCMfoldLeft.

Section PCMfoldRight. 
Variables (A : Type) (R : pcm) (a : A -> R -> R).
Hypothesis H : (forall k x y, a k (x \+ y) = a k x \+ y).

Lemma foldr_helper (s1 s2 : seq A) (z0 : R) x :
        foldr a z0 (s1 ++ x :: s2) = foldr a z0 (s1 ++ rcons s2 x).
Proof.
rewrite -!foldl_rev rev_cat rev_cons cat_rcons.
rewrite foldl_helper; last by move=>*; rewrite H. 
by rewrite -[x :: _ ++ _]revK rev_cons rev_cat !revK rcons_cat.
Qed.

Lemma foldr_perm (s1 s2 : seq A) (z0 : R) :
        perm s1 s2 -> 
        foldr a z0 s1 = foldr a z0 s2.
Proof.
move=>P; rewrite -!foldl_rev; apply: foldl_perm.
- by move=>*; rewrite H.
apply/(pperm_trans _ (pperm_rev _))/pperm_sym.
by apply/(pperm_trans _ (pperm_rev _))/pperm_sym.
Qed.

Lemma foldr_init (s : seq A) (x y : R) :
        foldr a (x \+ y) s = foldr a x s \+ y.
Proof. by rewrite -!foldl_rev foldl_init. Qed.

End PCMfoldRight.

(* fold-join lemmas *)

Lemma foldl_join A (U : pcm) h (s : seq A) (a : A -> U):
        foldl (fun h t => a t \+ h) h s =
        foldl (fun h t => a t \+ h) Unit s \+ h.
Proof.
set g := fun x => x \+ h.
apply/esym/(fusion_foldl (g:=g)); last by rewrite /g unitL.
by move=>x y; rewrite joinA.
Qed.

Lemma foldr_join A (U : pcm) h (s : seq A) (a : A -> U):
        foldr (fun t h => h \+ a t) h s =
        h \+ foldr (fun t h => h \+ a t) Unit s.
Proof.
apply/esym/fusion_foldr; last by rewrite unitR.
by move=>x y; rewrite joinA.
Qed.

Section BigOps.
Variables (U : pcm).
Variables (I : Type) (f : I -> U).

Lemma big_validV (xs : seq I) i :
        valid (\big[join/Unit]_(i <- xs) f i) ->
        i \In xs -> valid (f i).
Proof.
elim: xs=>[|x xs IH] in i * => //.
rewrite big_cons InE=>V [->|]; first by apply: (validL V).
by apply: IH; rewrite (validR V).
Qed.

Lemma big_validVL (xs : seq I) z i :
        valid (f z \+ \big[join/Unit]_(i <- xs) f i) ->
        i \In xs -> i <> z -> valid (f z \+ f i).
Proof.
elim: xs=>[|x xs IH] in i * => //.
rewrite big_cons InE =>V [->_ |].
- by move: V; rewrite joinA; apply: validL.
by apply: IH; move: V; rewrite joinCA; apply: validR.
Qed.

Lemma big_validV2 (xs : seq I) :
        valid (\big[join/Unit]_(i <- xs) f i) ->
        forall i j, i \In xs -> j \In xs -> i <> j -> valid (f i \+ f j).
Proof.
elim: xs=>[|x xs IH] //=; rewrite big_cons.
move=>V i j; rewrite !InE; case=>[->|Xi][->|Xj] N //; last first.
- by apply: IH=>//; apply: (validR V).
- by rewrite joinC; apply: (big_validVL V).
by apply: (big_validVL V)=>// /esym.
Qed.

End BigOps.

(***********************************)
(* separating conjunction aka star *)
(***********************************)

Definition star {U : pcm} (p1 p2 : Pred U) : Pred U :=
  [Pred h | exists h1 h2, [ /\ h = h1 \+ h2, h1 \In p1 & h2 \In p2] ].
Definition emp {U : pcm} : Pred U := eq^~ Unit.
Definition top {U : pcm} : Pred U := PredT.

Notation "p1 '#' p2" := (star p1 p2)
  (at level 57, right associativity) : rel_scope.

Add Parametric Morphism U : (@star U) with signature
 @Eq_Pred _ _ ==> @Eq_Pred _ _ ==> @Eq_Pred _ _ as star_morph.
Proof.
move=>x y E x1 y1 E1 m /=; split; case=>h1 [h2][-> H1 H2];
by exists h1, h2; split=>//; [apply/E|apply/E1].
Qed.

(* monoid laws for star hold under <~>, not = *)
(* thus, require fun/prop extensionality to make hold under = *)
(* working with <~> entails use of setoids *)
(* and prevents use of monoids from bigops *)
(* the latter isn't a big deal, however, as most lemmas *)
(* in bigops are about decidable/finite sets *)
(* and won't work with Prop anyway *)

Section StarMonoid.
Context {U : pcm}.
Implicit Type x y z : Pred U.

Lemma starA x y z : x # y # z <~> (x # y) # z.
Proof.
move=>m /=; split; case=>h1 [h2][H1 H2].
- case=>h3 [h4][H3 H4 H5]; subst h2.
  eexists (h1 \+ h3), h4; rewrite -joinA; split=>//.
  by exists h1, h3. 
case: H2=>h3 [h4][? H2 H3 H4]; subst h1.
exists h3, (h4 \+ h2); rewrite joinA; split=>//.
by exists h4, h2.
Qed.

Lemma starC x y : x # y <~> y # x.
Proof.
move=>m; split.
- by case=>h1 [h2][H H1 H2]; exists h2, h1; rewrite joinC. 
by case=>h1 [h2][H H1 H2]; exists h2, h1; rewrite joinC.
Qed.

Lemma starL x : emp # x <~> x.
Proof.
move=>m; split=>[|H]; first by case=>h1 [h2][->->]; rewrite unitL. 
by exists Unit, m; rewrite unitL. 
Qed.

Lemma starR x : x # emp <~> x.
Proof. by rewrite starC starL. Qed.

Lemma starAC x y z : x # y # z <~> x # z # y.
Proof. by rewrite (starC y). Qed.

Lemma starCA x y z : x # (y # z) <~> y # (x # z).
Proof. by rewrite starA (starC x) -starA. Qed.

(*
HB.instance Definition _ := 
  Monoid.isComLaw.Build (Pred U) emp star starA starC starL.
*)

End StarMonoid.


(* star iterated over sequence *)

Section IterStarSeq.
Context {U : pcm} {A : Type}.

Notation seq_join hs := (\big[join/Unit]_(i <- hs) i).

(* definition is locked to prevent automation from going inside *)
Definition sepit_seq (s : seq A) (f : A -> Pred U) : Pred U :=
  locked
  [Pred h | exists hs : seq U,
              [/\ size hs = size s, h = seq_join hs &
                  All (fun '(a, h) => h \In f a) (zip s hs)]].

Lemma sepit_seq_unlock s f :
        sepit_seq s f =   
        [Pred h | exists hs : seq U,
              [/\ size hs = size s, h = seq_join hs &
                  All (fun '(a, h) => h \In f a) (zip s hs)]].
Proof. by rewrite /sepit_seq -lock. Qed.

Lemma sepit_seq0 f : sepit_seq [::] f <~> emp.
Proof.
rewrite sepit_seq_unlock=>h; split.
- by case=>/= hs [/size0nil -> -> _]; rewrite !big_nil.
by move=>->; exists [::]; rewrite !big_nil.
Qed.

Lemma sepitseq_cons x s f : 
        sepit_seq (x::s) f <~> f x # sepit_seq s f.
Proof.
rewrite !sepit_seq_unlock=>h; split.
- case=>/=; case=>[|h0 hs]; case=>//= /eqP; rewrite eqSS =>/eqP Hs.
  rewrite big_cons =>->[H0 H1].
  by exists h0, (seq_join hs); do!split=>//; exists hs.
case=>h1[_][{h}-> H1][hs][E -> H].
by exists (h1 :: hs); rewrite /= E !big_cons.
Qed.

(* alternative def *)
(* appears simpler, but no much gain from \big ops *)
(* as star/emp are only monoids under <~>, not = *)
Lemma sepit_seqE s f :
         sepit_seq s f <~> \big[star/emp]_(i <- s) f i.
Proof. 
elim: s=>[|x s IH]; first by rewrite sepit_seq0 big_nil. 
by rewrite sepitseq_cons big_cons IH.
Qed.

Lemma sepitseq_cat s1 s2 f : 
        sepit_seq (s1 ++ s2) f <~>
        sepit_seq s1 f # sepit_seq s2 f.
Proof.
rewrite sepit_seq_unlock.
elim: s1 s2=>[|x s1 IH] s2 h /=; split.
- case=>hs [E {h}-> H2].
  exists Unit, (seq_join hs); rewrite unitL.
  split=>//; first by rewrite sepit_seq0.
  by rewrite sepit_seq_unlock; exists hs.
- case=>h1[h2][{h}->]; rewrite sepit_seq0=>->. 
  by rewrite sepit_seq_unlock unitL.
- case=>/=; case=>[|h0 hs]; case=>//= /eqP; rewrite eqSS=>/eqP E.
  rewrite !big_cons /= =>->[H0 HS].
  case: (IH s2 (seq_join hs)).1; first by exists hs.
  move=>h1[h2][HJ H1 H2].
  exists (h0 \+ h1), h2; rewrite HJ joinA; split=>//.
  by rewrite sepitseq_cons; exists h0, h1.
case=>h1 [h2][{h} ->]; rewrite sepit_seq_unlock.
case; case=>[|h0 hs1]; case=>//= /eqP; rewrite eqSS=>/eqP E1.
rewrite !big_cons /= =>{h1}->[H0 H1].
rewrite sepit_seq_unlock; case=>hs2[E2 {h2}-> H2].
exists (h0 :: hs1 ++ hs2); rewrite big_cons big_cat joinA; split=>//=.
- by rewrite !size_cat E1 E2.
rewrite zip_cat //=; split=>//.
by apply/All_cat.
Qed.

Lemma sepitseq_perm s1 s2 (f : A -> Pred U) :
        perm s1 s2 -> 
        sepit_seq s1 f <~> sepit_seq s2 f.
Proof.
elim: s1 s2 =>[|x s1 IH] s2 /=; first by move/pperm_nil=>->.
move=>H; have Hx: x \In s2 by apply/(pperm_in H)/In_cons; left.
case: (In_split Hx)=>s21[s22] E; rewrite {s2 Hx}E in H *.
move/pperm_cons_cat_cons: H=>/IH {}IH.
rewrite sepitseq_cons sepitseq_cat=>h; rewrite !toPredE; split.
- case=>h1 [h2][->{h} H1]; rewrite IH sepitseq_cat 2!sepit_seq_unlock.
  case=>_ [_][->{h2}][hs3][E3 -> H3][hs4][E4 -> H4]; rewrite joinCA.
  exists (seq_join hs3), (h1 \+ seq_join hs4); split=>//; first by exists hs3.
  rewrite sepitseq_cons sepit_seq_unlock; exists h1, (seq_join hs4).
  by split=>//; exists hs4.
rewrite sepitseq_cons sepit_seq_unlock. 
case=>_ [h2][{h}-> [hs1][Hs1 -> H1]].
rewrite sepit_seq_unlock.
case=>h3 [_][->{h2} H3 [hs2][Hs2 -> H2]]; rewrite joinCA.
exists h3, (seq_join hs1 \+ seq_join hs2); split=>//.
rewrite IH sepit_seq_unlock; exists (hs1 ++ hs2); split.
- by rewrite !size_cat Hs1 Hs2.
- by rewrite big_cat.
by rewrite zip_cat //; apply/All_cat.
Qed.

Lemma sepit_seqF s (f1 f2 : A -> Pred U) :
        (forall x, x \In s -> f1 x <~> f2 x) -> 
        sepit_seq s f1 <~> sepit_seq s f2.
Proof.
elim: s=>[|x s IH] H h; rewrite !toPredE.
- by rewrite !sepit_seq0.
have /IH {IH}H': forall x : A, x \In s -> f1 x =p f2 x.
  by move=>? H0; apply: H; apply/In_cons; right.
have Hx : x \In x :: s by apply/In_cons; left.
by rewrite !sepitseq_cons; split; case=>h1[h2][{h}-> H1 H2]; exists h1, h2;
split=>//; [rewrite -H | rewrite -H' | rewrite H | rewrite H'].
Qed.

Lemma big_sepitseq (s : seq A) (f : A -> U) m : 
        m = \big[join/Unit]_(i <- s) f i <->
        m \In sepit_seq s (fun i h => h = f i).
Proof.
rewrite sepit_seqE; elim: s m=>[|x xs IH] /= m; first by rewrite !big_nil.
rewrite !big_cons; split=>[E|]; last first.
- by case=>h1 [h2][Em H1 H2]; rewrite Em H1; congr (_ \+ _); rewrite IH.
by rewrite InE; exists (f x), (\big[join/Unit]_(j <- xs) f j); rewrite -IH. 
Qed.

Lemma eq_sepitseqF s (f1 f2 : A -> Pred U) :
        (forall x, x \In s -> f1 x <~> f2 x) -> 
        sepit_seq s f1 <~> sepit_seq s f2.
Proof. by move=>H; apply: sepit_seqF=>x Hx; apply: H. Qed.

Lemma sepitseq_emp (s : seq A) (f : A -> Pred U) : 
        (forall x, x \In s -> f x <~> emp (U:=U)) -> 
        sepit_seq s f <~> emp.
Proof.
move=>H; rewrite sepit_seqE.
elim: s H=>[|a xs IH] H; first by rewrite big_nil.
rewrite big_cons H ?InE; last by left.
by rewrite starL IH // => x X; apply: H; rewrite InE; right.
Qed.

End IterStarSeq.

(* iterated star on eqType *)

Section IterStarEq.
Context {U : pcm} {A : eqType}.

Lemma sepit_seqP x s (f : A -> Pred U) :
        uniq s ->
        sepit_seq s f <~>
        if x \in s then f x # sepit_seq (filter (predC1 x) s) f
        else sepit_seq s f.
Proof.
(* can't use big library for this proof, because all *)
(* necessary lemmas require AC wrt =; thus, direct proof below *)
case E: (x \in s)=>//.
elim: s E=>[|y s IH] //= /[swap]; case/andP=>Hy Hu.
- rewrite sepitseq_cons inE; case/orP.
  by move/eqP=>->; rewrite eq_refl filter_predC1.
move=>Hx h0.
have ->: (y != x) by apply/eqP=>Hxy; rewrite Hxy Hx in Hy.
by split; case=>ha[h1][{h0}-> Ha]; [rewrite (IH Hx Hu) | rewrite sepitseq_cons];
case=>hb[h][{h1}-> Hb H]; rewrite joinCA; exists hb, (ha \+ h); split=>//;
[rewrite sepitseq_cons | rewrite (IH Hx Hu)]; exists ha, h.
Qed.

Lemma perm_sepitseq s1 s2 (f : A -> Pred U) :
        perm_eq s1 s2 -> 
        sepit_seq s1 f <~> sepit_seq s2 f.
Proof. by move/perm_eq_perm; exact: sepitseq_perm. Qed.

End IterStarEq.

(* iterated star on finsets *)

Section FinIterStar.
Context {U : pcm} {I : finType}.

Definition sepit (s : {set I}) (Ps : I -> Pred U) := 
  sepit_seq (enum s) Ps.

Lemma sepitE (s : {set I}) f :
        sepit s f <~> \big[star/emp]_(i in s) f i.
Proof. by rewrite -big_filter /sepit sepit_seqE. Qed.

Lemma sepit0 f : sepit set0 f <~> emp.
Proof. by rewrite sepitE big_pred0 // => x; rewrite in_set0. Qed.

Lemma sepitF (s : {set I}) f1 f2 :
        (forall x, x \in s -> f1 x <~> f2 x) -> 
        sepit s f1 <~> sepit s f2.
Proof. 
move=>H; apply: eq_sepitseqF=>x /mem_seqP.
by rewrite mem_enum; apply: H. 
Qed.

Lemma eq_sepit (s1 s2 : {set I}) f : 
        s1 =i s2 -> 
        sepit s1 f <~> sepit s2 f.
Proof. by move/eq_enum=>H; apply: perm_sepitseq; rewrite H. Qed.

Lemma sepitS x (s : {set I}) f :
        sepit s f <~> if x \in s then f x # sepit (s :\ x) f
                      else sepit s f.
Proof.
rewrite /sepit {1}(sepit_seqP x f (enum_uniq s)) mem_enum.
case: (x \in s)=>//; rewrite !sepit_seqE !big_filter big_filter_cond.  
rewrite (eq_bigl (mem (s :\ x))) //.
by move=>z; rewrite !inE andbC.
Qed.

Lemma sepitT1 x f : sepit setT f <~> f x # sepit (setT :\ x) f.
Proof. by rewrite (sepitS x) in_setT. Qed.

Lemma big_sepit (s : {set I}) (f : I -> U) m : 
        m = \big[join/Unit]_(i in s) (f i) <->
        m \In sepit s (fun i h => h = f i).
Proof. by rewrite /sepit /= -big_sepitseq -big_enum. Qed.

Lemma big_sepitT (f : I -> U) m : 
        m = \big[join/Unit]_i (f i) <->
        m \In sepit setT (fun i h => h = f i).
Proof. 
rewrite -big_sepit; apply: iff_sym.
by rewrite -big_enum /= enum_T big_enum.
Qed.

End FinIterStar.
