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
From Coq Require Setoid.
From mathcomp Require Import ssrnat eqtype seq.
From pcm Require Import options prelude pred.
From pcm Require Import pcm morphism natmap.

(***********************)
(* Generalized mutexes *)
(***********************)

Module GeneralizedMutex.
Section GeneralizedMutex.
Variable T : Type. (* the mutex stages, excluding undef and unit *)

Inductive mutex := undef | nown | mx of T.

Definition join' x y :=
  match x, y with
    undef, _ => undef
  | _, undef => undef
  | nown, x => x
  | x, nown => x
  | mx _, mx _ => undef
  end.

Definition valid' x := if x is undef then false else true.

Lemma joinC : commutative join'.
Proof. by case=>[||x]; case=>[||y]. Qed.

Lemma joinA : associative join'.
Proof. by case=>[||x]; case=>[||y]; case=>[||z]. Qed.

Lemma unitL : left_id nown join'.
Proof. by case. Qed.

Lemma validL x y : valid' (join' x y) -> valid' x.
Proof. by case: x. Qed.

Lemma valid_unit : valid' nown.
Proof. by []. Qed.

Definition mutexPCMMix := PCMMixin joinC joinA unitL validL valid_unit.
Canonical mutexPCM := Eval hnf in PCM mutex mutexPCMMix.

(* cancelativity *)

Lemma joinmK (m1 m2 m : mutexPCM) : valid (m1 \+ m) -> m1 \+ m = m2 \+ m -> m1 = m2.
Proof. by case: m m1 m2=>[||m][||m1][||m2]; rewrite !pcmE. Qed.

Definition mutexCPCMMix := CPCMMixin joinmK.
Canonical mutexCPCM := Eval hnf in CPCM mutex mutexCPCMMix.

(* topped structure *)

Lemma unitb (x : mutex) : reflect (x = Unit) (if x is nown then true else false).
Proof. by case: x=>[||x]; constructor; rewrite !pcmE. Qed.

Lemma join0E (x y : mutex) : x \+ y = Unit -> x = Unit /\ y = Unit.
Proof. by case: x y=>[||x][||y]. Qed.

Lemma valid3 (x y z : mutex) : valid (x \+ y \+ z) =
        [&& valid (x \+ y), valid (y \+ z) & valid (x \+ z)].
Proof. by case: x y z=>[||x][||y][||z]. Qed.

Lemma valid_undef : ~~ valid undef.
Proof. by []. Qed.

Lemma undef_join x : undef \+ x = undef.
Proof. by []. Qed.

Definition mutexTPCMMix := TPCMMixin unitb valid_undef undef_join.
Canonical mutexTPCM := Eval hnf in TPCM mutex mutexTPCMMix.

End GeneralizedMutex.

Section Equality.
Variable T : eqType.

Definition mutex_eq (x y : mutex T) :=
  match x, y with
    undef, undef => true
  | nown, nown => true
  | mx x', mx y' => x' == y'
  | _, _ => false
  end.

Lemma mutex_eqP : Equality.axiom mutex_eq.
Proof.
case=>[||x]; case=>[||y] /=; try by constructor.
by case: eqP=>[->|H]; constructor=>//; case=>/H.
Qed.

Definition mutexEqMix := EqMixin mutex_eqP.
Canonical mutexEqType := Eval hnf in EqType (mutex T) mutexEqMix.
Canonical mutexEQPCM := Eval hnf in EQPCM (mutex T) (mutexPCMMix T).

End Equality.

Module Exports.
Canonical mutexPCM.
Canonical mutexCPCM.
Canonical mutexEqType.
Canonical mutexTPCM.
Canonical mutexEQPCM.
Notation mutex := mutex.
Notation mx_undef := undef.
Notation nown := nown.
Notation mx := mx.
Notation mutexPCM := mutexPCM.
Notation mutexTPCM := mutexTPCM.
Arguments mx_undef {T}.
Arguments nown {T}.
Arguments mx [T].

(* mutexes with distingusihed own element *)
Notation mtx T := (mutex (option T)).
Notation mtx2 := (mtx False).
Notation mtx3 := (mtx unit).
Notation own := (mx None).
Notation auth x := (mx (Some x)).
Notation auth1 := (mx (Some tt)).
End Exports.
End GeneralizedMutex.

Export GeneralizedMutex.Exports.

(* some lemmas for generalized mutexes *)

Section MutexLemmas.
Variable T : Type.
Implicit Types (t : T) (x y : mutex T).

Variant mutex_spec x : mutex T -> Type :=
| mutex_undef of x = mx_undef : mutex_spec x mx_undef
| mutex_nown of x = Unit : mutex_spec x Unit
| mutex_mx t of x = mx t : mutex_spec x (mx t).

Lemma mxP x : mutex_spec x x.
Proof. by case: x=>[||t]; constructor. Qed.

Lemma mxE0 x y : x \+ y = Unit -> (x = Unit) * (y = Unit).
Proof. exact: GeneralizedMutex.join0E. Qed.

(* a form of cancelativity, more useful than the usual form *)
Lemma cancelMx t1 t2 x : (mx t1 \+ x = mx t2) <-> (t1 = t2) * (x = Unit).
Proof. by case: x=>[||x] //=; split=>//; case=>->. Qed.

Lemma cancelxM t1 t2 x : (x \+ mx t1 = mx t2) <-> (t1 = t2) * (x = Unit).
Proof. by rewrite joinC cancelMx. Qed.

Lemma mxMx t x : valid (mx t \+ x) -> x = Unit.
Proof. by case: x. Qed.

Lemma mxxM t x : valid (x \+ mx t) -> x = Unit.
Proof. by rewrite joinC=>/mxMx. Qed.

Lemma mxxyM t x y : valid (x \+ (y \+ mx t)) -> x \+ y = Unit.
Proof. by rewrite joinA=>/mxxM. Qed.

Lemma mxMxy t x y : valid (mx t \+ x \+ y) -> x \+ y = Unit.
Proof. by rewrite -joinA=>/mxMx. Qed.

Lemma mxxMy t x y : valid (x \+ (mx t \+ y)) -> x \+ y = Unit.
Proof. by rewrite joinCA=>/mxMx. Qed.

Lemma mxyMx t x y : valid (y \+ mx t \+ x) -> y \+ x = Unit.
Proof. by rewrite joinAC=>/mxMx. Qed.

(* inversion principle for join *)
(* own and mx are prime elements, and unit does not factor *)
Variant mxjoin_spec (x y : mutex T) : mutex T -> mutex T -> mutex T -> Type :=
| bothnown of x = nown & y = nown : mxjoin_spec x y nown nown nown
| leftmx t of x = mx t & y = nown : mxjoin_spec x y (mx t) (mx t) nown
| rightmx t of x = nown & y = mx t : mxjoin_spec x y (mx t) nown (mx t)
| invalid of ~~ valid (x \+ y) : mxjoin_spec x y undef x y.

Lemma mxPJ x y : mxjoin_spec x y (x \+ y) x y.
Proof. by case: x y=>[||x][||y]; constructor. Qed.

End MutexLemmas.

Prenex Implicits mxMx mxxM mxxyM mxMxy mxxMy mxyMx.

Section OwnMutex.
Variables T : Type.
Implicit Types x y : mtx T.

Lemma mxOx x : valid (own \+ x) -> x = Unit.
Proof. by apply: mxMx. Qed.

Lemma mxxO x : valid (x \+ own) -> x = Unit.
Proof. by apply: mxxM. Qed.

Lemma mxxyO x y : valid (x \+ (y \+ own)) -> x \+ y = Unit.
Proof. by apply: mxxyM. Qed.

Lemma mxOxy x y : valid (own \+ x \+ y) -> x \+ y = Unit.
Proof. by apply: mxMxy. Qed.

Lemma mxxOy x y : valid (x \+ (own \+ y)) -> x \+ y = Unit.
Proof. by apply: mxxMy. Qed.

Lemma mxyOx x y : valid (y \+ own \+ x) -> y \+ x = Unit.
Proof. by apply: mxyMx. Qed.
End OwnMutex.

Prenex Implicits  mxOx mxxO mxxyO mxOxy mxxOy mxyOx.

(* specific lemmas for binary mutexes *)

Lemma mxON (x : mtx2) : valid x -> x != own -> x = nown.
Proof. by case: x=>//; case. Qed.

Lemma mxNN (x : mtx2) : valid x -> x != nown -> x = own.
Proof. by case: x=>//; case=>//; case. Qed.

(* the next batch of lemmas is for automatic simplification *)

Section MutexRewriting.
Variable T : eqType.
Implicit Types (t : T) (x : mutex T).

Lemma mxE1 :  (((@mx_undef T == nown) = false) *
               ((@nown T == mx_undef) = false)).
Proof. by []. Qed.

Lemma mxE2 t : (((mx t == nown) = false) *
                ((nown == mx t) = false)) *
               (((mx t == mx_undef) = false) *
                ((mx_undef == mx t) = false)).
Proof. by []. Qed.

Lemma mxE3 t x : ((((mx t \+ x == nown) = false) *
                   ((x \+ mx t == nown) = false)) *
                  (((nown == mx t \+ x) = false) *
                   ((nown == x \+ mx t) = false))).
Proof. by case: x. Qed.

Lemma mxE5 t1 t2 x :
       (((mx t1 \+ x == mx t2) = (t1 == t2) && (x == Unit)) *
        ((x \+ mx t1 == mx t2) = (t1 == t2) && (x == Unit))) *
       (((mx t1 == mx t2 \+ x) = (t1 == t2) && (x == Unit)) *
        ((mx t1 == x \+ mx t2) = (t1 == t2) && (x == Unit))).
Proof.
have L : forall t1 t2 x, (mx t1 \+ x == mx t2) = (t1 == t2) && (x == Unit).
- by move=>*; apply/eqP/andP=>[/cancelMx[]->->|[]/eqP->/eqP->].
by do !split=>//; rewrite ?L // eq_sym L eq_sym.
Qed.

Lemma mx_valid t : valid (mx t).
Proof. by []. Qed.

Lemma mx_injE t1 t2 : (mx t1 == mx t2) = (t1 == t2).
Proof. by []. Qed.

Definition mxE := ((((mxE1, mxE2), (mxE3)), ((mxE5, mx_injE),
                   (mx_valid))),
                   (* plus a bunch of safe simplifications *)
                   (((unitL, unitR), (valid_unit, eq_refl)),
                   ((valid_undef, undef_join), join_undef))).

End MutexRewriting.

(* function mapping all mx's to own *)
Definition mxown T (x : mutex T) : mtx2 :=
  match x with
    mx_undef => mx_undef
  | nown => nown
  | _ => own
  end.

(* this is a morphism under full domain *)
Lemma mxown_morph_ax T : morph_axiom (@sepT _) (@mxown T).
Proof. by split=>[|x y] //; case: x=>//; case: y. Qed.

Canonical mxown_pmorph T := Morphism' (@mxown T) (mxown_morph_ax T).

(* the key inversion property is the following *)
(* we could use simple case analysis in practice *)
(* but this appears often, so we might just as well have a lemma for it *)
Lemma mxownP T (x : mutex T) : mxown x = nown -> x = nown.
Proof. by case: x. Qed.

Definition mxundef T (x : mtx T) : mtx2 :=
  match x with
  | nown => nown
  | mx None => own
  | _ => undef
  end.

Definition sep_mxundef T (x y : mtx T) :=
  if x \+ y is (nown | mx None) then true else false.

Lemma mxundef_seprel_ax T : seprel_axiom (@sep_mxundef T).
Proof. by split=>//; case=>[||x] // [||y] // [||[]] //=; case: y. Qed.

Canonical mxundef_seprel T :=
  Eval hnf in seprel (@sep_mxundef T) (mxundef_seprel_ax T).

Lemma mxundef_ax T : morph_axiom (@sep_mxundef T) (@mxundef T).
Proof. by split=>//; case=>[||x] // [||[]] //; case: x. Qed.

Canonical mxundef_pmorph T := Morphism' (@mxundef T) (mxundef_ax T).

Prenex Implicits mxown mxundef.

(* inversion principle for mxundef *)
Variant mxundef_spec T (x : mtx T) : mtx2 -> mtx T -> Type :=
| mxundef_nown of x = nown : mxundef_spec x nown nown
| mxundef_own of x = own : mxundef_spec x own own
| mxundef_undef of x = undef : mxundef_spec x undef undef
| mxundef_mx t of x = auth t : mxundef_spec x undef (auth t).

Lemma mxundefP T (x : mtx T) : mxundef_spec x (mxundef x) x.
Proof. by case: x=>[||[t|]]; constructor. Qed.

(* nats into mtx *)
(* notice this is not a morphism *)
Definition nxown n : mtx2 := if n is 0 then nown else own.

Variant nxown_spec n : mtx2 -> Type :=
| nxZ of n = 0 : nxown_spec n nown
| nxS m of n = m.+1 : nxown_spec n own.

Lemma nxP n : nxown_spec n (nxown n).
Proof. by case: n=>[|n]; [apply: nxZ | apply: (@nxS _ n)]. Qed.

Variant nxownjoin_spec n1 n2 : mtx2 -> Type :=
| nxjZ of n1 = 0 & n2 = 0 : nxownjoin_spec n1 n2 nown
| nxjS m of n1 + n2 = m.+1 : nxownjoin_spec n1 n2 own.

Lemma nxPJ n1 n2 : nxownjoin_spec n1 n2 (nxown (n1 \+ n2)).
Proof.
case: n1 n2=>[|n1][|n2] /=.
- by constructor.
- by apply: (@nxjS _ _ n2).
- by apply: (@nxjS _ _ n1); rewrite addn0 //.
apply: (@nxjS _ _ (n1 + n2).+1).
by rewrite addSn addnS.
Qed.

(**********************************)
(* Morphisms on locking histories *)
(**********************************)

(* Morphism on locking histories that provides mutual exclusion: *)
(* when one thread has locked, the other can't proceed. *)
(* Because the morphism just looks into the last history entry *)
(* we call it *omega*, or omg for short. *)


Section OmegaMorph.
Let U := nat_mapPCM (bool * bool).

Definition omg_s := fun x y : U =>
  [&& last_val false x ==> (last_key y < last_key x) &
      last_val false y ==> (last_key x < last_key y)].

Lemma omg_sep_ax : seprel_axiom omg_s.
Proof.
rewrite /omg_s; split=>[|x y|x y|x y z] /=; first by rewrite lastval0.
- by rewrite andbC.
- move=>V /andP [H _]; rewrite lastkey0 lastval0.
  by case: (x in x ==> _) H=>// /(leq_trans _) ->.
move=>V /andP [X Y] /andP [].
rewrite !lastkeyUn !lastvalUn !(validLE3 V).
rewrite {1 2}maxnC {1 2}/maxn gtn_max leq_max /=.
case: (ltngtP (last_key x) (last_key y)) X Y=>H X Y Kx Kz;
 rewrite ?H ?X ?(negbTE Y) fun_if if_arg ?implybT ?Kx Kz if_same //= ?andbT.
by case: (x in x ==> _) Kz=>// /(ltn_trans H) ->.
Qed.

Canonical omg_seprel := Eval hnf in seprel omg_s omg_sep_ax.

Definition omg (x : U) : mtx2 := if last_val false x then own else nown.

Lemma omg_morph_ax : morph_axiom omg_seprel omg.
Proof.
rewrite /omg; split=>[|x y V /andP [X Y]]; first by rewrite lastval0.
rewrite lastvalUn V; case: ltngtP X Y=>H X Y;
by rewrite ?(negbTE X) ?(negbTE Y) //; case: ifP.
Qed.

Canonical omg_morph := Morphism' omg omg_morph_ax.

(* transfer lemmas *)

Lemma omgPos (V : pcm) (v : V) (ht : V -> natmap (bool * bool)) :
        last_val false (ht v) = (omg (ht v) == own).
Proof. by rewrite /omg /=; case: ifP. Qed.

Lemma omgPosMorph (V : pcm) (v1 v2 : V) (D : sep_rel V) (ht : @morphism V U D):
        valid (v1 \+ v2) -> 'preim ht omg_s v1 v2 ->
        last_val false (ht v1 \+ ht v2) = (omg (ht v1) \+ omg (ht v2) == own).
Proof.
move=>W /andP [G] /andP []; rewrite /omg /= in G *.
rewrite lastvalUn (pfVf ht W G); case: ltngtP=>H H1 H2;
by rewrite ?(negbTE H1) ?(negbTE H2) //; case: ifP.
Qed.

Lemma omgNeg (V : pcm) (v : V) (ht : V -> natmap (bool * bool)) :
       ~~ last_val false (ht v) = (omg (ht v) == nown).
Proof. by rewrite /omg /=; case: ifP. Qed.

Lemma omgNegMorph (V : pcm) (v1 v2 : V) (D : sep_rel V) (ht : @morphism V U D) :
         valid (v1 \+ v2) ->'preim ht omg_s v1 v2 ->
         ~~ last_val false (ht v1 \+ ht v2) = (omg (ht v1) \+ omg (ht v2) == nown).
Proof.
move=>W /andP [G] /andP []; rewrite /= /omg in G *.
rewrite lastvalUn (pfVf ht W G); case: ltngtP=>H H1 H2;
by rewrite ?(negbTE H1) ?(negbTE H2) //; case: ifP.
Qed.

Lemma omgidPos (v : U) :
        last_val false v = (omg v == own).
Proof. by rewrite (omgPos _ id). Qed.

Lemma omgidPosMorph (v1 v2 : U) :
        valid (v1 \+ v2) -> omg_s v1 v2 ->
        last_val false (v1 \+ v2) = (omg v1 \+ omg v2 == own).
Proof. by move=> W S; rewrite (@omgPosMorph _ _ _ _ (id_morph _)). Qed.

Lemma omgidNeg (v : U) :
        ~~ last_val false v = (omg v == nown).
Proof. by rewrite (omgNeg _ id). Qed.

Lemma omgidNegMorph (v1 v2 : U) :
        valid (v1 \+ v2) -> omg_s v1 v2 ->
         ~~last_val false (v1 \+ v2) = (omg v1 \+ omg v2 == nown).
Proof. by move=>W S; rewrite (@omgNegMorph _ _ _ _ (id_morph _)). Qed.

Definition omgP := ((omgidNegMorph, omgidPosMorph, omgPosMorph, omgNegMorph), (omgidPos, omgidNeg, omgPos, omgNeg)).

Canonical omg_seprel.
Canonical omg_morph.

Lemma omg_fresh_val (V : pcm) (v1 v2 : V) (D : sep_rel V) (ht : @morphism V U D) :
      valid (v1 \+ v2) ->
      D v1 v2 ->
      (omg (fresh (ht v1 \+ ht v2) \-> (false, true) \+ ht v1) = own) *
      (omg (fresh (ht v1 \+ ht v2) \-> (true, false) \+ ht v1) = nown) *
      (omg (fresh (ht v1 \+ ht v2) \-> (false, true) \+ ht v2) = own) *
      (omg (fresh (ht v1 \+ ht v2) \-> (true, false) \+ ht v2) = nown).
Proof.
move=>A O; have Vh : valid (ht v1 \+ ht v2).
- by move/pfV2: O; move/(_ _ ht A).
by rewrite /omg !lastval_freshUn.
Qed.

Lemma omg_fresh_sep (V : pcm) (v1 v2 : V) (D : sep_rel V) (ht : @morphism V U D) op :
        valid (v1 \+ v2) ->
        D v1 v2 ->
        (omg (ht v2) = nown ->
          omg_s (fresh (ht v1 \+ ht v2) \-> op \+ ht v1) (ht v2)) *
        (omg (ht v1) = nown ->
          omg_s (ht v1) (fresh (ht v1 \+ ht v2) \-> op \+ ht v2)).
Proof.
move=>A O; have Vh : valid (ht v1 \+ ht v2).
- by move/pfV2: O; move/(_ _ ht A).
rewrite /omg_s lastval_freshUn // lastkey_freshUn //.
split=>N; first by rewrite omgP N /fresh lastkeyUn Vh ltnS leq_maxr implybT.
by rewrite omgP N lastkey_freshUn //= ltnS lastkeyUn Vh leq_maxl implybT.
Qed.

Definition omg_fresh := (omg_fresh_val, omg_fresh_sep).

Lemma omg_eta (h : natmap (bool * bool)):
        valid h -> omg h = own ->
        exists h' v, [/\ h' = free h (last_key h),
          h = last_key h \-> (v, true) \+ h',
          last_key h != 0,
          last_key h \in dom h,
          last_key h \notin dom h' &
          last_key h' < last_key h].
Proof.
rewrite /omg; case: ifP=>// N V _; set k := last_key h.
have D : k \in dom h.
- rewrite /last_val /atval /oapp in N.
  by case: dom_find N=>[->//|].
have K : k != 0 by apply: dom_cond D.
case: (um_eta D); case=>v1 v2 [Ef Eh].
set h' := free h k in Eh *; set q := k \-> (v1, true).
have Nd : k \notin dom h'.
- rewrite Eh in V; case: validUn V=>// _ _ X _; apply: X.
  by rewrite domPt inE /= K eq_refl.
exists h', v1; split=>//.
- by rewrite /last_val /atval Ef /= in N; rewrite -N.
have: last_key h' <= k.
- by rewrite /k Eh; apply: lastkeyUnf; rewrite -Eh.
rewrite leq_eqVlt; case/orP=>// /eqP E.
rewrite -E in Nd; apply: contraR Nd=>/= _.
by apply: (dom_lastkeyE (a:=0)); rewrite E; case: (k) K.
Qed.

(* specialize to alternating histories *)
Lemma omg_eta_all (h : natmap (bool * bool)) :
        valid h -> omg h = own -> um_all (fun k v => v.2 = ~~ v.1) h ->
        exists h', [/\ h' = free h (last_key h),
          h = last_key h \-> (false, true) \+ h',
          last_key h != 0,
          last_key h \in dom h,
          last_key h \notin dom h' &
          last_key h' < last_key h].
Proof.
move=>V H A; case: (omg_eta V H)=>h' [v][H1 H2 H3 H4 H5 H6].
exists h'; split=>//; rewrite H2 in V A; case: (umallPtUnE V A)=>/=.
by case: v {A} V H2.
Qed.

Lemma omg_lastkey x y :
        (omg x = own -> valid (x \+ y) -> omg_s x y ->
           last_key (x \+ y) = last_key x) *
        (omg y = own -> valid (x \+ y) -> omg_s x y ->
           last_key (x \+ y) = last_key y).
Proof.
rewrite /omg_s /omg; split=>L V S; case: ifP L=>L // _;
rewrite L /= in S; rewrite lastkeyUn V; case/andP: S=>S1 S2.
 by rewrite maxnC /maxn S1.
by rewrite /maxn S2.
Qed.

End OmegaMorph.
