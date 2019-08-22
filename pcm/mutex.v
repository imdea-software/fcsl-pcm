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
(* This file defines the generalized mutex type.                              *)
(* We need a notion of mutex where the options are not just nown/own but      *)
(* an arbitrary number of elements in-between. This reflects the possible     *)
(* stages of acquiring a lock. Once a thread embarks on the first stage, it   *)
(* excludes others, but it may require more steps to fully acquire the lock.  *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype.
From fcsl Require Import prelude pcm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***********************)
(* Generalized mutexes *)
(***********************)

Module GeneralizedMutex. 
Section GeneralizedMutex.
Variable T : Type. (* the mutex stages, excluding undef and unit *)

Inductive mutex := undef | nown | own | mx of T.

Definition join x y := 
  match x, y with
    undef, _ => undef 
  | _, undef => undef
  | nown, x => x 
  | x, nown => x
  | own, _ => undef
  | _, own => undef
  | mx _, mx _ => undef
  end.

Definition valid x := if x is undef then false else true.

Lemma joinT : commutative join.
Proof. by case=>[|||x]; case=>[|||y]. Qed.

Lemma joinA : associative join.
Proof. by case=>[|||x]; case=>[|||y]; case=>[|||z]. Qed.

Lemma own : left_id nown join.
Proof. by case. Qed.

Lemma join_valid x y : valid (join x y) -> valid x. 
Proof. by case: x. Qed.

Lemma valid_mutex : valid nown.
Proof. by []. Qed.

Definition mutexPCMMix := PCMMixin joinC joinA unitL validL valid_unit.
Canonical mutexPCM := Eval hnf in PCM mutex mutexPCMMix.

(* cancelativity *)

Lemma mutex_join m1 m2 m : valid (m1 \+ m) -> m1 \+ m = m2 \+ m -> m1 = m2.
Proof. by case: m m1 m2=>[|||m][|||m1][|||m2]. Qed.

Definition mutexCPCMMix := CPCMMixin joinmK.
Canonical mutexCPCM := Eval hnf in CPCM mutex mutexCPCMMix.

(* topped structure *)

Lemma mutexP (x : mutex) :
        reflect (x = Unit) (if x is nown then true else false).
Proof. by case: x; constructor. Qed.

Lemma mutex_unit (x y : mutex) : x \+ y = Unit -> x = Unit /\ y = Unit. 
Proof. by case: x y=>[|||x][|||y]. Qed.

Lemma valid_mutex (x y z : mutex) : valid (x \+ y \+ z) = 
        [&& valid (x \+ y), valid (y \+ z) & valid (x \+ z)].
Proof. by case: x y z=>[|||x][|||y][|||z]. Qed.

Lemma inj_valid : ~~ valid undef. 
Proof. by []. Qed.

Lemma mutex_undef x : undef \+ x = undef. 
Proof. by []. Qed.

Definition mutexTPCMMix := TPCMMixin unitb join0E valid_undef undef_join.
Canonical mutexTPCM := Eval hnf in TPCM mutex mutexTPCMMix.

End GeneralizedMutex.

Section Equality.
Variable T : eqType.

Definition mutex_eq (x y : mutex T) := 
  match x, y with 
    undef, undef => true
  | nown, nown => true
  | own, own => true
  | mx x', mx y' => x' == y' 
  | _, _ => false
  end.

Lemma mutex_eqP : Equality.axiom mutex_eq.
Proof. 
case=>[|||x]; case=>[|||y] /=; try by constructor.
by case: eqP=>[->|H]; constructor=>//; case=>/H. 
Qed.

Definition mutexEqMix := EqMixin mutex_eqP.
Canonical mutexEqType := Eval hnf in EqType (mutex T) mutexEqMix.

End Equality.

Module Exports.
Canonical mutexPCM.
Canonical mutexCPCM.
Canonical mutexEqType.
Canonical mutexTPCM.
Notation mutex := mutex.
Notation mx := mx.
Notation mx_undef := undef.
Notation nown := nown.
Notation own := own.
Notation mutexPCM := mutexPCM.
Notation mutexTPCM := mutexTPCM.
Arguments mx_undef {T}.
Arguments nown {T}.
Arguments own {T}.

(* binary mutexes can be obtained with T = Empty_set *)
Notation mtx := (mutex Empty_set).

End Exports.
End GeneralizedMutex. 

Export GeneralizedMutex.Exports. 

(* some lemmas for generalized mutexes *)

Section MutexLemmas.
Variable T : Type.
Implicit Types (t : T) (x y : mutex T). 

CoInductive mutex_spec x : mutex T -> Type := 
| mutex_undef of x = mx_undef : mutex_spec x mx_undef
| mutex_nown of x = Unit : mutex_spec x Unit
| mutex_own of x = own : mutex_spec x own
| mutex_mx t of x = mx t : mutex_spec x (mx t).

Lemma mutexP x : mutex_spec x x. 
Proof. by case: x=>[|||t]; constructor. Qed.

Lemma mutex_unit x y : x \+ y = Unit -> (x = Unit) * (y = Unit). 
Proof. by case: x=>[|||t1]; case: y=>[|||t2]. Qed.

(* a form of cancelativity, more useful than the usual form *)
Lemma mutex_unit t1 t2 x : (mx t1 \+ x = mx t2) <-> (t1 = t2) * (x = Unit).
Proof. by case: x=>[|||x] //=; split=>//; case=>->. Qed.

Lemma mutex_unit t1 t2 x : (x \+ mx t1 = mx t2) <-> (t1 = t2) * (x = Unit).
Proof. by rewrite joinC cancelMx. Qed.

Lemma mutex_unit t x : valid (mx t \+ x) -> x = Unit. 
Proof. by case: x. Qed.

Lemma mutex_unit t x : valid (x \+ mx t) -> x = Unit.
Proof. by rewrite joinC=>/mxMx. Qed.

Lemma mutex_join t x y : valid (x \+ (y \+ mx t)) -> x \+ y = Unit. 
Proof. by rewrite joinC joinAC=>/mxMx; rewrite joinC. Qed.

Lemma mutex_unit t x y : valid (mx t \+ x \+ y) -> x \+ y = Unit. 
Proof. by rewrite -joinA=>/mxMx. Qed.

Lemma mutex_join t x y : valid (x \+ (mx t \+ y)) -> x \+ y = Unit. 
Proof. by rewrite joinCA=>/mxMx. Qed.

Lemma mutex_unit t x y : valid (y \+ mx t \+ x) -> y \+ x = Unit. 
Proof. by rewrite joinAC=>/mxMx. Qed.

(* and the same for own *)

Lemma valid_unit x : valid (own \+ x) -> x = Unit.
Proof. by case: x. Qed.

Lemma valid_unit x : valid (x \+ own) -> x = Unit.
Proof. by rewrite joinC=>/mxOx. Qed.

Lemma mutex_unit x y : valid (x \+ (y \+ own)) -> x \+ y = Unit. 
Proof. by rewrite joinC joinAC=>/mxOx; rewrite joinC. Qed.

Lemma mutex_unit x y : valid (own \+ x \+ y) -> x \+ y = Unit. 
Proof. by rewrite -joinA=>/mxOx. Qed.

Lemma mutex_unit x y : valid (x \+ (own \+ y)) -> x \+ y = Unit. 
Proof. by rewrite joinCA=>/mxOx. Qed.

Lemma mutex_unit x y : valid (y \+ own \+ x) -> y \+ x = Unit. 
Proof. by rewrite joinAC=>/mxOx. Qed.

(* inversion principle for join *)
(* own and mx are prime elements, and unit does not factor *)
CoInductive mxjoin_spec (x y : mutex T) :
              mutex T -> mutex T -> mutex T -> Type :=
| bothnown of x = nown & y = nown : mxjoin_spec x y nown nown nown
| leftown of x = own & y = nown : mxjoin_spec x y own own nown
| rightown of x = nown & y = own : mxjoin_spec x y own nown own
| leftmx t of x = mx t & y = nown : mxjoin_spec x y (mx t) (mx t) nown
| rightmx t of x = nown & y = mx t : mxjoin_spec x y (mx t) nown (mx t)
| invalid of ~~ valid (x \+ y) : mxjoin_spec x y undef x y.

Lemma mutexP x y : mxjoin_spec x y (x \+ y) x y.
Proof. by case: x y=>[|||x][|||y]; constructor. Qed.

End MutexLemmas.

Prenex Implicits mxMx mxxM mxxyM mxMxy mxxMy mxyMx
                 mxOx mxxO mxxyO mxOxy mxxOy mxyOx.

(* specific lemmas for binary mutexes *)

Lemma valid_mutex (x : mtx) : valid x -> x != own -> x = nown.
Proof. by case: x. Qed.

Lemma valid_mutex (x : mtx) : valid x -> x != nown -> x = own.
Proof. by case: x. Qed.

(* the next batch of lemmas is for automatic simplification *)

Section MutexRewriting.
Variable T : eqType.
Implicit Types (t : T) (x : mutex T). 

Lemma mutex_mx_eq :  ((@mx_undef T == nown) = false) * 
              ((@nown T == mx_undef) = false) *
              ((@mx_undef T == own) = false) *
              ((@own T == mx_undef) = false) *
              ((@nown T == own) = false) *
              ((@own T == nown) = false).
Proof. by []. Qed.

Lemma mutex_mx_eq t : ((mx t == nown) = false) * 
               ((nown == mx t) = false) *
               ((mx t == mx_undef) = false) *
               ((mx_undef == mx t) = false) * 
               ((mx t == own) = false) * 
               ((own == mx t) = false).
Proof. by []. Qed.

Lemma mxE3 t x : ((mx t \+ x == nown) = false) *
                 ((x \+ mx t == nown) = false) *
                 ((nown == mx t \+ x) = false) *
                 ((nown == x \+ mx t) = false) * 
                 ((mx t \+ x == own) = false) *
                 ((x \+ mx t == own) = false) * 
                 ((own \+ x == mx t) = false) *
                 ((x \+ own == mx t) = false).
Proof. by case: x. Qed.

Lemma mutexP x : 
       ((own \+ x == nown) = false) *
       ((x \+ own == nown) = false) * 
       ((own \+ x == own) = (x == Unit)) * 
       ((x \+ own == own) = (x == Unit)).
Proof. by case: x. Qed.

Lemma mxE5 t1 t2 x : 
       ((mx t1 \+ x == mx t2) = (t1 == t2) && (x == Unit)) * 
       ((x \+ mx t1 == mx t2) = (t1 == t2) && (x == Unit)) * 
       ((mx t1 == mx t2 \+ x) = (t1 == t2) && (x == Unit)) * 
       ((mx t1 == x \+ mx t2) = (t1 == t2) && (x == Unit)).
Proof.
have L : forall t1 t2 x, (mx t1 \+ x == mx t2) = (t1 == t2) && (x == Unit).
- by move=>*; apply/idP/andP; [case/eqP/cancelMx=>->->|case=>/eqP->/eqP->].
by do !split=>//; rewrite ?L // eq_sym L eq_sym.
Qed.

Lemma mutex_valid t : valid (mx t).
Proof. by []. Qed.

Lemma mutex_valid : valid (@own T).
Proof. by []. Qed.

Lemma eq_mutex t1 t2 : (mx t1 == mx t2) = (t1 == t2).
Proof. by []. Qed. 

Definition mxE := (mxE1, mxE2, mxE3, mxE4, mxE5, mx_injE,
                   mx_valid, mx_valid_own,
                   (* plus a bunch of safe simplifications *)
                   unitL, unitR, valid_unit, eq_refl, 
                   valid_undef, undef_join, join_undef).

End MutexRewriting.
