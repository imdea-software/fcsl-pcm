(*
Copyright 2015 IMDEA Software Institute
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
(* This file contains an implementation of maps over non-zero natural         *)
(* numbers, pcm instance for natmap, gapless natmaps, natmaps with binary     *)
(* range, several sorts of continuous natmaps.                                *)
(* Histories are a special case of natmaps.                                   *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import options prelude pred finmap rtc seqint.
From fcsl Require Export pcm morphism unionmap.

(************************)
(************************)
(* Maps over non-0 nats *)
(************************)
(************************)

Notation nat_pred := (fun x : nat_ordType => x != 0).

Module Type NMSig.

Parameter tp : Type -> Type.

Section Params.
Variable A : Type.
Notation tp := (tp A).

Parameter nm_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : nat -> A -> tp -> tp.
Parameter dom : tp -> seq nat.
Parameter dom_eq : tp -> tp -> bool.
Parameter assocs : tp -> seq (nat * A).
Parameter free : tp -> nat -> tp.
Parameter find : nat -> tp -> option A.
Parameter union : tp -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : nat -> A -> tp.

Parameter from : tp -> @UM.base nat_ordType nat_pred A.
Parameter to : @UM.base nat_ordType nat_pred A -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : nm_undef = to (@UM.Undef nat_ordType nat_pred A).
Axiom defE : forall f, defined f = UM.valid (from f).
Axiom emptyE : empty = to (@UM.empty nat_ordType nat_pred A).
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)).
Axiom domE : forall f, dom f = UM.dom (from f).
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Axiom assocsE : forall f, assocs f = UM.assocs (from f).
Axiom freeE : forall f k, free f k = to (UM.free (from f) k).
Axiom findE : forall k f, find k f = UM.find k (from f).
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom empbE : forall f, empb f = UM.empb (from f).
Axiom undefbE : forall f, undefb f = UM.undefb (from f).
Axiom ptsE : forall k v, pts k v = to (@UM.pts nat_ordType nat_pred A k v).

End Params.
End NMSig.

Module NMDef : NMSig.
Section NMDef.
Variable A : Type.

Definition tp : Type := @UM.base nat_ordType nat_pred A.

Definition nm_undef := @UM.Undef nat_ordType nat_pred A.
Definition defined f := @UM.valid nat_ordType nat_pred A f.
Definition empty := @UM.empty nat_ordType nat_pred A.
Definition upd k v f := @UM.upd nat_ordType nat_pred A k v f.
Definition dom f := @UM.dom nat_ordType nat_pred A f.
Definition dom_eq f1 f2 := @UM.dom_eq nat_ordType nat_pred A f1 f2.
Definition assocs f := @UM.assocs nat_ordType nat_pred A f.
Definition free f k := @UM.free nat_ordType nat_pred A f k.
Definition find k f := @UM.find nat_ordType nat_pred A k f.
Definition union f1 f2 := @UM.union nat_ordType nat_pred A f1 f2.
Definition empb f := @UM.empb nat_ordType nat_pred A f.
Definition undefb f := @UM.undefb nat_ordType nat_pred A f.
Definition pts k v := @UM.pts nat_ordType nat_pred A k v.

Definition from (f : tp) : @UM.base nat_ordType nat_pred A := f.
Definition to (b : @UM.base nat_ordType nat_pred A) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : nm_undef = to (@UM.Undef nat_ordType nat_pred A). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty nat_ordType nat_pred A). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by []. Qed.
Lemma assocsE f : assocs f = UM.assocs (from f). Proof. by []. Qed.
Lemma freeE f k : free f k = to (UM.free (from f) k). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma undefbE f : undefb f = UM.undefb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts nat_ordType nat_pred A k v).
Proof. by []. Qed.

End NMDef.
End NMDef.

Notation natmap := NMDef.tp.

Definition natmapMixin A :=
  UMCMixin (@NMDef.ftE A) (@NMDef.tfE A) (@NMDef.defE A)
           (@NMDef.undefE A) (@NMDef.emptyE A) (@NMDef.updE A)
           (@NMDef.domE A) (@NMDef.dom_eqE A) (@NMDef.assocsE A)
           (@NMDef.freeE A) (@NMDef.findE A) (@NMDef.unionE A)
           (@NMDef.empbE A) (@NMDef.undefbE A) (@NMDef.ptsE A).

Canonical nat_mapUMC A :=
  Eval hnf in UMC (natmap A) (@natmapMixin A).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition nat_mapPCMMix A := union_map_classPCMMix (nat_mapUMC A).
Canonical nat_mapPCM A := Eval hnf in PCM (natmap A) (@nat_mapPCMMix A).

Definition nat_mapCPCMMix A := union_map_classCPCMMix (nat_mapUMC A).
Canonical nat_mapCPCM A := Eval hnf in CPCM (natmap A) (@nat_mapCPCMMix A).

Definition nat_mapTPCMMix A := union_map_classTPCMMix (nat_mapUMC A).
Canonical nat_mapTPCM A := Eval hnf in TPCM (natmap A) (@nat_mapTPCMMix A).

Definition nat_map_eqMix (A : eqType) :=
  @union_map_class_eqMix nat_ordType nat_pred A _ (@natmapMixin A).
Canonical nat_map_eqType (A : eqType) :=
  Eval hnf in EqType (natmap A) (@nat_map_eqMix A).

(* installing the Pred structure for writing x \In h *)
Canonical Structure natmap_PredType A : PredType (nat * A) :=
  Mem_UmMap_PredType (nat_mapUMC A).
Coercion Pred_of_natmap A (f : natmap A) : Pred_Class := [eta Mem_UmMap f].

Definition nm_pts A (k : nat) (v : A) :=
  @UMC.pts nat_ordType nat_pred A (@nat_mapUMC A) k v.

(* baking nat_pred into the notation *)
Notation "x \-> v" := (@nm_pts _ x v) (at level 30).

Definition nm_foldr V C a c d f := @um_foldr nat_ordType nat_pred V C (@nat_mapUMC V) a c d f.

Lemma uniq_dom0 A (h : natmap A) : uniq (0 :: dom h).
Proof. by rewrite /= uniq_dom cond_dom. Qed.

#[export]
Hint Resolve uniq_dom0 : core.

Lemma nm_dom0 A (h : natmap A) : (h = undef \/ h = Unit) <-> (dom h = [::]).
Proof.
split=>[|E]; first by case=>->; rewrite ?dom_undef ?dom0.
case V : (valid h); last by move/invalidE: (negbT V)=>->; left.
by rewrite (dom0E V) ?E //; right.
Qed.

Definition stamp := nat.

Lemma In_dom0 A (h : natmap A) k e : (k, e) \In h -> k \in 0::dom h.
Proof. by move=>H; rewrite inE (In_dom H) orbT. Qed.

(***************************************)
(***************************************)
(* Constructions of last_key and fresh *)
(***************************************)
(***************************************)

Definition last_key {A} (h : natmap A) := last 0 (dom h).
Definition fresh {A} (h : natmap A) := (last_key h).+1.

Prenex Implicits last_key fresh.

Section FreshLastKey.

Lemma lastkey_undef A : last_key (undef : natmap A) = 0.
Proof. by rewrite /last_key /undef /= !umEX. Qed.

Lemma lastkey0 A : last_key (Unit : natmap A) = 0.
Proof. by rewrite /last_key /Unit /= !umEX. Qed.

Lemma lastkey_dom A (h : natmap A) :
        valid h -> last_key h \notin dom h -> h = Unit.
Proof.
rewrite /valid /= /last_key /Unit /= !umEX /= -{4}[h]UMC.tfE.
case: (UMC.from h)=>//=; case=>s H /= H1 _ /seq_last_in.
rewrite /UM.empty UMC.eqE UM.umapE /supp fmapE /= {H H1}.
by elim: s.
Qed.

Lemma dom_lastkey0P A (h : natmap A) : last_key h = 0 <-> dom h = [::].
Proof.
rewrite -nm_dom0; split; last first.
- by case=>E; subst h; rewrite ?lastkey_undef ?lastkey0.
move=>E; case V : (valid h); last by left; move/invalidE: (negbT V).
right; apply: lastkey_dom=>//; rewrite E.
by apply: contraT; rewrite negbK; apply: dom_cond.
Qed.

Lemma dom_lastkey0PN A (h : natmap A) : last_key h != 0 <-> dom h != [::].
Proof. by split; move/eqP=>H; apply/eqP=>X; elim: H; apply/dom_lastkey0P. Qed.

Lemma dom_lastkey0D A (h : natmap A) k : k \in dom h -> last_key h != 0.
Proof. by move=>D; apply/negP=>/eqP/dom_lastkey0P H; rewrite H in D. Qed.

Lemma dom_lastkey0DX A (h : natmap A) :
        last_key h != 0 <-> exists k, k \in dom h.
Proof.
rewrite dom_lastkey0PN; split.
- by case/has_nilP/hasP=>x; exists x.
by case=>k D; apply/eqP=>N; rewrite N in D.
Qed.

Lemma dom_lastkey A (h : natmap A) :
        valid h -> ~~ unitb h -> last_key h \in dom h.
Proof. by move=>X; apply: contraR; move/(lastkey_dom X)=>->; apply/unitbP. Qed.

Lemma lastkeyxx A (h : natmap A) :
        valid h -> last_key h = 0 -> h = Unit.
Proof.
by move=>V H; apply: lastkey_dom V _; apply/negP=>/dom_cond; rewrite H.
Qed.

Lemma dom_lastkeyE A (h : natmap A) a : a < last_key h -> last_key h \in dom h.
Proof.
move=>H; case V : (valid h); last first.
- by move/invalidE: (negbT V) H=>->; rewrite lastkey_undef.
by apply: dom_lastkey V (contraL _ H)=>/unitbE ->; rewrite lastkey0.
Qed.

Lemma dom_lastkeyN A (h : natmap A) : last_key h != 0 <-> last_key h \in dom h.
Proof.
split; last by move/dom_cond.
by rewrite -lt0n=>H; apply: dom_lastkeyE H.
Qed.

Lemma lastkey_max A (h : natmap A) x : x \in dom h -> x <= last_key h.
Proof.
rewrite /last_key /= !umEX; case: (UMC.from h)=>//; case=>s H _ /=.
rewrite /supp /ord /= (leq_eqVlt x) orbC.
by apply: sorted_last_key_maxR (sorted_oleq H)=>//; apply: otrans.
Qed.

Lemma max_lastkey A (h : natmap A) x :
        x \in dom h -> {in dom h, forall y, y <= x} -> last_key h = x.
Proof.
rewrite /last_key !umEX; case: (UMC.from h)=>//; case=>s H _ /=.
move=>H1 /= H2; apply: sorted_max_key_last (sorted_oleq H) H1 _=>//.
- by apply: otrans.
- by apply: oantisym.
by move=>z /(H2 z); rewrite leq_eqVlt orbC.
Qed.

Lemma lastkey_leq A (h : natmap A) x :
        {in dom h, forall y, y <= x} <-> last_key h <= x.
Proof.
split; last by move=>D y Y; apply: leq_trans D; apply: lastkey_max Y.
case V : (valid h); last first.
- by move/negbT/invalidE: V=>->; rewrite lastkey_undef.
case E: (unitb h); first by move/unitbP: E=>->; rewrite lastkey0.
by apply; rewrite dom_lastkey // E.
Qed.

Lemma lastkey_ltn A a (h : natmap A) x :
        a < last_key h -> {in dom h, forall y, y < x} <-> last_key h < x.
Proof.
move/dom_lastkeyE=>D; split; first by apply.
by move=>Y y X; apply: leq_ltn_trans Y; apply: lastkey_max.
Qed.

Lemma lastkeyPt A (x : nat) (v : A) : x != 0 -> last_key (x \-> v) = x.
Proof. by rewrite /last_key domPtK /= => ->. Qed.

Lemma hist_path A (h : natmap A) : path oleq 0 (dom h).
Proof.
rewrite !umEX; case: (UMC.from h)=>//= {}h _; case: h; case=>//= x s H.
rewrite {1}/oleq /ord /= orbC -leq_eqVlt /=.
by apply: sub_path H=>z y; rewrite /oleq=>->.
Qed.

Lemma lastkey_mono A B (h1 : natmap A) (h2 : natmap B) :
        {subset dom h1 <= dom h2} -> last_key h1 <= last_key h2.
Proof.
rewrite leq_eqVlt orbC; apply: (seq_last_monoR _ (@otrans nat_ordType))=>//;
by apply: hist_path.
Qed.

Lemma lastkeyfUn A (h1 h2 : natmap A) :
        valid (h1 \+ h2) -> last_key h1 <= last_key (h1 \+ h2).
Proof. by move=>X; apply: lastkey_mono=>x; rewrite domUn inE X => ->. Qed.

Lemma lastkeyUnf A (h1 h2 : natmap A) :
        valid (h1 \+ h2) -> last_key h2 <= last_key (h1 \+ h2).
Proof. by rewrite joinC; apply: lastkeyfUn. Qed.

(* a convenient rephrasing of above lemmas *)

Lemma lastkeyUn_mono A (h1 h2 : natmap A) t :
        valid (h1 \+ h2) -> last_key (h1 \+ h2) < t -> last_key h1 < t.
Proof.
move=>V; apply/leq_trans/lastkey_mono.
by move=>x D; rewrite domUn inE V D.
Qed.

Lemma lastkeyUn0T A1 A2 (h1 : natmap A1) (h2 : natmap A2) :
        valid h1 -> valid h2 ->
        (forall x, x \in dom h1 -> x \in dom h2 -> false) ->
        last_key h1 = last_key h2 -> (h1 = Unit) * (h2 = Unit).
Proof.
move=>V1 V2 D E.
case E1: (unitb h1).
- move/unitbE: E1 E V2=>->; rewrite lastkey0.
  by case/esym/dom_lastkey0P/nm_dom0=>-> //; rewrite valid_undef.
case E2: (unitb h2).
- move/unitbE: E2 E V1=>->; rewrite lastkey0.
  by case/dom_lastkey0P/nm_dom0=>-> //; rewrite valid_undef.
move: (D _ (dom_lastkey V1 (negbT E1))).
by rewrite E (dom_lastkey V2 (negbT E2))=>/(_ erefl).
Qed.

Lemma lastkeyUn0 A (h1 h2 : natmap A) :
        valid (h1 \+ h2) ->
        last_key h1 = last_key h2 -> (h1 = Unit) * (h2 = Unit).
Proof.
move=>V E.
case: validUn V=>// V1 V2 D _; apply: lastkeyUn0T V1 V2 _ E.
by move=>x /D /negbTE ->.
Qed.

Lemma lastkey_subdom A1 A2 (h1 : natmap A1) (h2 : natmap A2) :
        {subset dom h1 <= dom h2} ->
        last_key h2 \in dom h1 -> last_key h1 = last_key h2.
Proof.
by move=>S D; apply/eqP; rewrite eqn_leq (lastkey_max D) (lastkey_mono S).
Qed.

Variable A : Type.
Implicit Type h : natmap A.

Lemma lastkeyUn h1 h2 :
        last_key (h1 \+ h2) =
        if valid (h1 \+ h2) then maxn (last_key h1) (last_key h2) else 0.
Proof.
have H (k1 k2 : natmap A) : valid (k1 \+ k2) ->
  last_key k1 < last_key k2 -> last_key (k1 \+ k2) = last_key k2.
- move=>V H; apply: max_lastkey=>[|x].
  - by rewrite domUn inE V (dom_lastkeyE H) orbT.
  rewrite domUn inE V; case/orP; move/lastkey_max=>// T;
  by apply: leq_trans T (ltnW H).
case V : (valid _); last first.
- by move/invalidE: (negbT V)=>->; rewrite lastkey_undef.
rewrite /maxn; case: (ltngtP (last_key h2) (last_key h1)).
- by rewrite joinC in V *; apply: H.
- by apply: H.
by move/esym/(lastkeyUn0 V)=>E; rewrite !E unitL.
Qed.

Lemma lastkeyPtUn_max h t u :
        last_key (t \-> u \+ h) =
        if valid (t \-> u \+ h) then maxn t (last_key h) else 0.
Proof.
by rewrite lastkeyUn; case: ifP=>// /validPtUn_cond /= D; rewrite lastkeyPt.
Qed.

Lemma lastkeyPtUn h t1 v :
        valid h ->
        fresh h <= t1 ->
        last_key (t1 \-> v \+ h) = t1.
Proof.
move=>V N; rewrite lastkeyPtUn_max validPtUn /= V.
case: eqP N=>[->|] //= _ N.
case: ifP=>D; first by rewrite /maxn; case: ltngtP N.
by move/(elimF idP): D; elim; apply/negP=>/lastkey_max; case: ltngtP N.
Qed.

Lemma lastkeyPtUn_valid h t u :
        valid h -> last_key h < t -> valid (t \-> u \+ h).
Proof.
move=>V L; rewrite validPtUn; apply/and3P; split=>//=.
- by rewrite /= -lt0n; apply: leq_ltn_trans L.
by apply: contraL L; move/lastkey_max; case: leqP.
Qed.

(* monotonicity just gives us <= *)
(* when we remove the last key, we get a strict < *)
Lemma lastkeyF h :
        last_key h \in dom h ->
        last_key (free h (last_key h)) < last_key h.
Proof.
move=>D; case: (um_eta D)=>v [Ef] Eh.
have N : last_key h \notin dom (free h (last_key h)).
- by rewrite domF inE eq_refl.
have: last_key (free h (last_key h)) <= last_key h.
- by apply: lastkey_mono=>x; rewrite domF inE; case: ifP.
rewrite leq_eqVlt; case/orP=>// /eqP E; rewrite -{1}E in N.
have Dn : last_key h > 0 by move/dom_cond: D; case: (last_key h).
by rewrite -E in Dn; rewrite (dom_lastkeyE Dn) in N.
Qed.

Lemma lastkeyPtUnE u2 u1 h t :
        last_key (t \-> u1 \+ h) = last_key (t \-> u2 \+ h).
Proof. by rewrite !lastkeyPtUn_max !validPtUn. Qed.

Lemma lastkeyUnPtE u2 u1 h t :
        last_key (h \+ t \-> u1) = last_key (h \+ t \-> u2).
Proof. by rewrite !(joinC h); apply: lastkeyPtUnE. Qed.

Lemma lastkeyU u h t :
        t \in dom h -> last_key (upd t u h) = last_key h.
Proof. by case/um_eta=>v [_ E]; rewrite E updPtUn (lastkeyPtUnE v). Qed.

Lemma lastkeyUmax h u t :
        last_key (upd t u h) =
        if t \in dom h then last_key h else
        if valid (upd t u h) then maxn t (last_key h) else 0.
Proof.
case: ifP; first by apply: lastkeyU.
move=>H; rewrite validU /=; case: eqP =>[->|/eqP Nt /=].
- by rewrite upd_condN // lastkey_undef.
case: ifP=>V; last first.
- by move/invalidE: (negbT V)=>->; rewrite upd_undef lastkey_undef.
have W : valid (upd t u h) by rewrite validU /= V Nt.
have E : upd t u h = t \-> u \+ h.
- apply: find_eta=>//; first by rewrite validPtUn /= V H Nt.
- by move=>k; rewrite findU /= Nt V findPtUn2 // validPtUn /= Nt V H.
by rewrite E lastkeyUn -E W lastkeyPt.
Qed.

(* freshness *)

Lemma fresh0N h x : fresh h <= x -> x != 0.
Proof. by case: eqP=>// ->. Qed.

Lemma dom_ordfresh h x : x \in dom h -> x < fresh h.
Proof. by move/lastkey_max. Qed.

Lemma dom_freshN h x : x \in dom h -> x != fresh h.
Proof. by move/dom_ordfresh; case: ltngtP. Qed.

Lemma dom_ordfreshT h x t : fresh h <= t -> x \in dom h -> x != t.
Proof. by move=>H1 /dom_ordfresh H2; case: ltngtP (leq_trans H2 H1). Qed.

Lemma dom_freshn h n : fresh h + n \notin dom h.
Proof. by apply: contra (@dom_ordfresh _ _) _; rewrite -leqNgt leq_addr. Qed.

Lemma ordfresh_dom0 h t : fresh h <= t -> t \notin 0::dom h.
Proof.
rewrite leqNgt; apply: contra; rewrite inE.
by case/orP=>[/eqP -> //|]; apply: dom_ordfresh.
Qed.

Lemma ordfresh_dom h t : fresh h <= t -> t \notin dom h.
Proof. by rewrite leqNgt; apply: contra; apply: dom_ordfresh. Qed.

Lemma dom_ordfresh0 h x t : fresh h <= t -> x \in 0::dom h -> x < t.
Proof.
by rewrite inE=>D /orP [/eqP ->|/dom_ordfresh H]; apply: leq_ltn_trans D.
Qed.

Lemma dom_freshN0 h x t : fresh h <= t -> x \in 0::dom h -> x != t.
Proof. by move=>D /(dom_ordfresh0 D); case: ltngtP. Qed.

Lemma omfresh_dom B h t (f : omap_fun (nat_mapUMC A) (nat_mapUMC B)) :
         fresh h <= t -> t \notin dom (f h).
Proof. by move=>F; apply/negP=>/omf_subdom/dom_ordfresh; case: ltngtP F. Qed.

Lemma dom_omfresh B h t (f : omap_fun (nat_mapUMC A) (nat_mapUMC B)) :
        t \in dom (f h) -> t < fresh h.
Proof. by move/omf_subdom/dom_ordfresh. Qed.

Lemma dom_omfreshT B h x t (f : omap_fun (nat_mapUMC A) (nat_mapUMC B)) :
        fresh h <= t -> x \in dom (f h) -> x != t.
Proof. by move=>H1 /dom_omfresh H2; case: ltngtP (leq_trans H2 H1). Qed.

Lemma omf_subdom0 B h (f : omap_fun (nat_mapUMC A) (nat_mapUMC B)) :
        {subset 0::dom (f h) <= 0::dom h}.
Proof.
move=>x; rewrite !inE; case/orP=>[->//|].
by move/omf_subdom=>->; rewrite orbT.
Qed.

Lemma find_fresh h x : fresh h <= x -> find x h = None.
Proof. by move=>H; rewrite In_findNE // ordfresh_dom. Qed.

Lemma dom_freshUn h1 h2 : valid h1 -> [pcm h2 <= h1] -> fresh h1 \notin dom h2.
Proof.
move=>V [x E]; rewrite {h1}E in V *; apply: contra (@dom_ordfresh _ _) _.
by rewrite joinC in V *; rewrite -leqNgt; apply: lastkeyUnf.
Qed.

Lemma valid_fresh h v t : fresh h <= t -> valid (t \-> v \+ h) = valid h.
Proof. by move=>N; rewrite validPtUn /= (fresh0N N) (ordfresh_dom N) andbT. Qed.

Lemma dom_freshUnN h1 h2 x :
        valid h1 -> [pcm h2 <= h1] -> x \in dom h2 -> x != fresh h1.
Proof. by move=>V H; apply: contraL=>/eqP ->; apply: dom_freshUn. Qed.

Lemma fresh_dom h : fresh h \notin dom h.
Proof. by move: (dom_freshn h 0); rewrite addn0.  Qed.

Lemma valid_freshX h1 h2 v :
        valid h1 -> last_key h2 <= last_key h1 ->
        valid (fresh h1 \-> v \+ h2) = valid h2.
Proof.
move=>V N; rewrite validPtUn /=; case W : (valid h2)=>//=.
apply/negP=>/dom_ordfresh; rewrite ltnS /fresh.
by case: ltngtP N.
Qed.

Lemma dom_fresh t1 e h :
        valid h -> fresh h <= t1 ->
        dom (t1 \-> e \+ h) = rcons (dom h) t1.
Proof.
move=>W N; rewrite joinC domUnPtK //.
- by rewrite joinC valid_fresh.
by apply/allP=>x /dom_ordfresh D; apply: leq_ltn_trans N.
Qed.

Lemma freshPtUn h t1 v :
        valid h ->
        fresh h <= t1 ->
        fresh (t1 \-> v \+ h) = t1.+1.
Proof. by move=>V N; rewrite /fresh lastkeyPtUn. Qed.

Lemma lastkey_freshX h1 h2 v :
        valid h1 -> valid h2 ->
        last_key h2 <= last_key h1 ->
        last_key (fresh h1 \-> v \+ h2) = fresh h1.
Proof.
move=>V1 V2 N; apply: max_lastkey=>[|y] /=.
- rewrite domUn inE valid_freshX //= V2 /= domPt inE /= eq_refl. by [].
rewrite dom_fresh // mem_rcons inE.
case/orP=>[/eqP ->//|/dom_ordfresh].
by rewrite ltnS=>H; apply: leq_trans H (ltnW _).
Qed.

Lemma valid_freshUn h1 h2 v :
        valid h1 -> [pcm h2 <= h1] -> valid (fresh h1 \-> v \+ h2) = valid h2.
Proof.
move=>V [x E]; rewrite {h1}E in V *.
by rewrite validPtUn dom_freshUn // andbT.
Qed.

Lemma lastkey_freshUn h1 h2 v :
        valid h1 -> [pcm h2 <= h1] ->
        last_key (fresh h1 \-> v \+ h2) = fresh h1.
Proof.
move=>V [x E]; rewrite {h1}E in V *; apply: max_lastkey=>[|y] /=;
  rewrite domUn inE valid_freshUn // (validE2 V) /= domPt inE ?eq_refl //.
rewrite andbC eq_sym leq_eqVlt; case: eqP=>//= _ D.
by apply: lastkey_max; rewrite domUn inE V D.
Qed.

Lemma lastkey_fresh h v : valid h -> last_key (fresh h \-> v \+ h) = fresh h.
Proof.
move=>Vf; apply: max_lastkey=>[|x] /=.
- by rewrite domUn inE valid_fresh // Vf domPt inE eq_refl.
rewrite domUn inE /= valid_fresh // Vf /= domPt inE /= eq_sym.
by rewrite leq_eqVlt; case: eqP=>//= _; apply: dom_ordfresh.
Qed.

Lemma dom_freshUnK h1 h2 v :
        valid h1 -> [pcm h2 <= h1] ->
        dom (fresh h1 \-> v \+ h2) = rcons (dom h2) (fresh h1).
Proof.
move=>V [x E]; subst h1; rewrite joinC domUnPtK //.
- by rewrite joinC valid_freshUn // (validL V).
apply/allP=>k /= D; apply: dom_ordfresh.
by rewrite domUn inE V D.
Qed.

Lemma freshfUn h1 h2 :
        valid (h1 \+ h2) -> fresh h1 <= fresh (h1 \+ h2).
Proof. by apply: lastkeyfUn. Qed.

Lemma freshUnf h1 h2 :
        valid (h1 \+ h2) -> fresh h2 <= fresh (h1 \+ h2).
Proof. by apply: lastkeyUnf. Qed.

Lemma freshfUnT U D (f : @morphism U (nat_mapPCM A) D) fr :
        forall x y : U, valid (x \+ y) ->
          D x y ->
          fresh (f (x \+ y)) <= fr -> fresh (f x) <= fr.
Proof.
move=>x y V H; apply: leq_trans.
by rewrite pfjoin // freshfUn // pfV2.
Qed.

Lemma freshfUn_phantT U D fr (f : @morphism U (nat_mapPCM A) D) of phantom (_ -> _) f :
        forall x y : U, valid (x \+ y) ->
          D x y ->
          fresh (f (x \+ y)) <= fr -> fresh (f x) <= fr.
Proof. by apply: freshfUnT. Qed.


(* pcm induced ordering *)

Lemma umpleq_lastkey h1 h2 :
        valid h2 -> [pcm h1 <= h2] -> last_key h1 <= last_key h2.
Proof.
by move=>V H; case: H V=>z->V; apply: lastkey_mono=>k D; rewrite domUn inE V D.
Qed.

(* backward induction on valid natmaps *)

Lemma valid_indb (P : natmap A -> Prop) :
        P Unit ->
        (forall u, P (1 \-> u)) ->
        (forall t u h, P h -> last_key h < t ->
                       valid (h \+ t \-> u) -> P (t \-> u \+ h)) ->
        forall h, valid h -> P h.
Proof.
move=>H1 H2 H3; elim/um_indb=>//=.
- by rewrite -[valid _]negbK; move/negP/invalidE.
move=>k v f H V K _.
case E: (unitb f); last first.
- apply: H3=>//; first by apply: H (validL V).
  apply: K; apply: contraR (negbT E).
  by rewrite -unitbE; apply: lastkey_dom (validL V).
move/unitbE: {K H} E V=>->; rewrite unitL unitR => V.
move: (H3 k v Unit H1); rewrite unitL unitR lastkey0 lt0n.
by apply=>//; rewrite validPt /= in V.
Qed.

(* forward induction on valid natmaps *)

Lemma valid_indf (P : natmap A -> Prop) :
        P Unit ->
        (forall t u h, P h ->
           (forall x, x \in dom h -> t < x) ->
           valid (t \-> u \+ h) -> P (t \-> u \+ h)) ->
        forall h, valid h -> P h.
Proof.
move=>H1 H2; elim/um_indf=>//=.
- by rewrite -[valid _]negbK; move/negP/invalidE.
move=>k v f H V K _.
apply: H2=>//; first by apply: H (validR V).
move=>x; move/(order_path_min (@ordtype.trans _)): K.
by case: allP=>// X _; apply: X.
Qed.

End FreshLastKey.

Notation freshT f := (@freshfUn_phantT _ _ _ _ _ (Phantom (_ -> _) f)).

Lemma fresh_mono A B (h1 : natmap A) (h2 : natmap B) :
        {subset dom h1 <= dom h2} -> fresh h1 <= fresh h2.
Proof. by apply: lastkey_mono. Qed.

Lemma range_freshUnK (A : ordType) (h : natmap A) k (v : A) :
        valid h -> last_key h < k ->
        range (k \-> v \+ h) = rcons (range h) v.
Proof.
move=>V K; rewrite joinC rangeUnPtK //; last first.
- by apply/allP=>x /lastkey_max/leq_ltn_trans; apply.
rewrite validUnPt V /=; case: k K=>//= k K.
by apply: contraL K=>/lastkey_max; rewrite ltnS; case: ltngtP.
Qed.

Lemma dom_fresh_sub A1 A2 (h1 : natmap A1) (h2 : natmap A2) :
        valid h1 -> {subset dom h2 <= dom h1} -> fresh h1 \notin dom h2.
Proof.
move=>V S; apply: contra; first by move/S; apply: dom_ordfresh.
by rewrite ltnn.
Qed.

Lemma valid_fresh_sub A1 A2 (h1 : natmap A1) (h2 : natmap A2) v :
        valid h1 -> {subset dom h2 <= dom h1} ->
        valid (fresh h1 \-> v \+ h2) = valid h2.
Proof. by move=>V S; rewrite validPtUn dom_fresh_sub // andbT. Qed.

(* lemmas with omap *)

Lemma lastkey_omap V1 V2 (f : nat * V1 -> option V2) (h : natmap V1) :
        last_key (omap f h) <= last_key h.
Proof. by apply: lastkey_mono; apply: dom_omap_sub. Qed.

Lemma lastkey_omap_some V1 V2 (f : nat * V1 -> option V2) (h : natmap V1) :
        (forall x, x \In h -> oapp predT false (f x)) ->
        last_key (omap f h) = last_key h.
Proof. by rewrite /last_key=>/dom_omap_some ->. Qed.

Lemma omap_fresh V V' (h : natmap V) (a : nat * V -> option V') k v :
        fresh h <= k ->
        omap a (pts k v \+ h) =
        (if a (k, v) is Some v' then
         pts k v' \+ omap a h else omap a h) :> natmap V'.
Proof.
case W : (valid h).
- by move=>H; rewrite omapPtUn valid_fresh // W.
move/negbT/invalidE: W=>->.
by case: (a _)=>[w|]; rewrite join_undef omap_undef // join_undef.
Qed.

(* renaming for freshness *)

Lemma fresh_omap V1 V2 (f : nat * V1 -> option V2) (h : natmap V1) :
        fresh (omap f h) <= fresh h.
Proof. by apply: lastkey_omap. Qed.

Lemma fresh_omap_some V1 V2 (f : nat * V1 -> option V2) (h : natmap V1) :
        (forall x, x \In h -> oapp predT false (f x)) ->
        fresh (omap f h) = fresh h.
Proof. by move=>H; rewrite /fresh lastkey_omap_some. Qed.

(* lemmas with In *)

Lemma In_lastkey V k v (h : natmap V) :  (k, v) \In h -> k <= last_key h.
Proof. by move/In_dom/lastkey_max. Qed.

Lemma In_fresh V (h : natmap V) x e t k :
         fresh h <= t ->
         (k, x) \In h -> (k, x) \In t \-> e \+ h.
Proof.
by move=>N H; apply/InR=>//; rewrite valid_fresh // (In_valid H).
Qed.

Lemma In_fresh_inv V (h : natmap V) x e t k :
        k < fresh h -> fresh h <= t ->
        (k, x) \In t \-> e \+ h -> (k, x) \In h.
Proof.
move=>N F H; have W : valid (t \-> e \+ h).
- by rewrite valid_fresh // (validR (In_valid H)).
by case/(InPtUnE _ W): H F=>// [[<- _]]; case: ltngtP N.
Qed.

(* lemmas with umfilt *)

(* a form of totality on the stamp ordering *)
Lemma umfiltT V (k1 k2 : stamp) (f : natmap V) :
        k1 \in dom f ->
        k2 \in dom f ->
        k1 \notin dom (um_filterk (ltn^~ k2) f) ->
        k2 \notin dom (um_filterk (ltn^~ k1) f) ->
        k1 = k2.
Proof.
case/In_domX=>v1 D1 /In_domX [v2 D2] S1 S2.
case: (ltngtP k1 k2)=>// N.
- by move/(In_umfiltk (ltn^~ k2))/(_ N)/In_dom: D1; rewrite (negbTE S1).
by move/(In_umfiltk (ltn^~ k1))/(_ N)/In_dom: D2; rewrite (negbTE S2).
Qed.

(* a somewhat different form of the previous lemma *)
Lemma umfiltT0 V (k1 k2 : stamp) (f : natmap V) :
        k1 \in dom f ->
        k2 \in dom f ->
        um_filterk (ltn^~ k1) f = Unit ->
        um_filterk (ltn^~ k2) f = Unit ->
        k1 = k2.
Proof.
by move=>D1 D2 U1 U2; apply: umfiltT D1 D2 _ _; rewrite ?U1 ?U2 dom0.
Qed.

(* umfilt and last/fresh *)
Lemma lastkey_umfilt V (p : pred (nat * V)) (h : natmap V) :
        last_key (um_filter p h) <= last_key h.
Proof. by apply: lastkey_mono; apply: dom_umfilt_subset. Qed.

Lemma fresh_umfilt V (p : pred (nat * V)) (h : natmap V) :
        fresh (um_filter p h) <= fresh h.
Proof. by apply: lastkey_umfilt. Qed.

Lemma umfilt_fresh V (p : pred (nat * V)) (h : natmap V) k v :
        fresh h <= k ->
        um_filter p (pts k v \+ h) =
        if p (k, v) then pts k v \+ um_filter p h else um_filter p h.
Proof.
case W : (valid h).
- by move=>H; rewrite umfiltPtUn valid_fresh // W.
move/negbT/invalidE: W=>->.
by case: ifP; rewrite join_undef umfilt_undef // join_undef.
Qed.

Lemma fresh_lt V (h : natmap V) x :
        fresh h <= x ->
        um_filterk [ pred k | k < x ] h = h.
Proof.
move=>F; rewrite -[RHS]umfilt_predT.
apply/eq_in_umfilt; case=>y v /In_dom/lastkey_max /= K.
by rewrite (leq_ltn_trans K F).
Qed.

(* OmapFun lemmas regarding natmaps *)

Section OmapFunNatmap.
Variables (V V' : Type).
Variable f : omap_fun (nat_mapUMC V) (nat_mapUMC V').

Lemma omf0 h : 0 \in dom (f h) = false.
Proof. by apply/negP=>/dom_cond. Qed.

Lemma omf_path h : path ltn 0 (dom (f h)).
Proof.
rewrite path_min_sorted; first by apply: omf_sorted.
by apply/allP=>z /dom_cond /=; case: z.
Qed.

Lemma omf_fresh t e h :
        fresh h <= t ->
        f (t \-> e \+ h) =
        if map_fun f (t, e) is Some v then t \-> v \+ f h else f h.
Proof. by case: f=>s [m H] /= N; rewrite !H omap_fresh. Qed.

Lemma fresh_omf h : fresh (f h) <= fresh h.
Proof. by case: f=>s [m H] /=; rewrite H fresh_omap. Qed.

(* commonly used lemma in automation *)
Lemma fresh_omfT t h : fresh h <= t -> fresh (f h) <= t.
Proof. by apply: leq_trans (fresh_omf _). Qed.

Lemma omf_freshT t h : t < fresh (f h) -> t < fresh h.
Proof. by apply: contraTT; rewrite -!ltnNge; apply: fresh_omfT. Qed.

Lemma fresh_omfUn h1 h2 :
        valid (h1 \+ h2) -> fresh (f h1 \+ f h2) <= fresh (h1 \+ h2).
Proof. by move=>W; rewrite -omfUn // fresh_omf. Qed.

Lemma fresh_omfUnT t h1 h2 :
        valid (h1 \+ h2) ->
        fresh (h1 \+ h2) <= t ->
        fresh (f h1 \+ f h2) <= t.
Proof. by move=>W /fresh_omfT; rewrite omfUn. Qed.

Lemma omf_subfresh t e h :
        fresh h <= t ->
        {subset dom (f h) <= dom (f (t \-> e \+ h))}.
Proof.
move=>N x H; rewrite omf_fresh //; case: (map_fun _ _)=>[a|//].
by rewrite domPtUn inE H orbT valid_fresh ?(dom_valid H, fresh_omfT).
Qed.

Lemma lastkey_omf h : last_key (f h) <= last_key h.
Proof. by case: f=>s [m H] /=; rewrite H lastkey_omap. Qed.

Lemma omf_fresh_lt x h :
        fresh h <= x -> um_filterk [ pred k | k < x ] (f h) = f h.
Proof. by move=>H; apply/fresh_lt/leq_trans/H/fresh_omf. Qed.

Lemma lastkey_omfE h : last_key h \in dom (f h) -> last_key (f h) = last_key h.
Proof. by apply: lastkey_subdom omf_subdom. Qed.

(* some phantomization *)

Lemma pfresh_omf_phantT (x : phantom (_ -> _) f) t h :
         fresh h <= t -> fresh (f h) <= t.
Proof. by apply: fresh_omfT. Qed.

End OmapFunNatmap.

(* in many proofs, rewriting by the following 3 lemmas discharges the sideconditions *)
(* so we give it a name *)
Definition freshX := (fresh_omfT, valid_omf, ordfresh_dom).
Notation pfresh_omfT f := (@pfresh_omf_phantT _ _ _ (Phantom (_ -> _) f)).

(*******************************)
(* Monotonicity for natmap nat *)
(*******************************)

Lemma nm_monoPtUn t t' (h : natmap nat) :
        last_key h < t ->
        (forall k v, (k, v) \In h -> v < t') ->
        um_mono (t \-> t' \+ h) = um_mono h.
Proof.
move=>H1 H2; case W: (valid h); last first.
- by move/invalidE: (negbT W)=>->; rewrite join_undef.
by apply: ummonoPtUn (lastkeyPtUn_valid _ W H1) _=>k v X; split;
[move/In_dom/lastkey_max/leq_ltn_trans: X; apply|apply: H2 X].
Qed.

(* Membership lemmas under pcm morphisms *)
Section Membership.
Variables (U : pcm) (V : Type) (S : rel U).
Variables (f : morphism (nat_mapPCM V) S).

Lemma pfL e (x y : U) :
        valid (x \+ y) -> S x y -> e \In f x -> e \In f (x \+ y).
Proof. by move=>W H1 H2; rewrite pfjoin //=; apply: InL=>//; rewrite pfV2. Qed.

Lemma pfR e (x y : U) :
        valid (x \+ y) -> S x y -> e \In f y -> e \In f (x \+ y).
Proof. by move=>W H1 H2; rewrite pfjoin //=; apply: InR=>//; rewrite pfV2. Qed.

Lemma pfUn e (x y : U) :
        valid (x \+ y) -> S x y -> e \In f (x \+ y) -> e \In f x \/ e \In f y.
Proof. by move=>W H1; rewrite pfjoin //; case/InUn; eauto. Qed.

End Membership.

(***********************************************)
(***********************************************)
(* Executing up to (and including/excluding) t *)
(***********************************************)
(***********************************************)

Definition oexec_le V R (a : R -> V -> R) ks t (h : natmap V) z0 :=
  oevalv a {sqint t ks] h z0.
Definition oexec_lt V R (a : R -> V -> R) ks t (h : natmap V) z0 :=
  oevalv a {sqint t ks| h z0.

(* Main transfer lemmas *)

Lemma oexleE V R a t v (h : natmap V) ks (z0 : R) :
        uniq ks ->
        t \in ks -> (t, v) \In h ->
        oexec_le a ks t h z0 = a (oexec_lt a ks t h z0) v.
Proof.
move=>U K H; rewrite /oexec_le/oexec_lt (squxR U K) oev_cat /=.
by move/In_find: H=>->.
Qed.

Arguments oexleE [V R a t v h ks z0].

Lemma oexleNE V R a t (h : natmap V) ks (z0 : R) :
        uniq ks ->
        (t \notin ks) || (t \notin dom h) ->
        oexec_le a ks t h z0 = oexec_lt a ks t h z0.
Proof.
rewrite /oexec_le/oexec_lt; move=>U /orP [] K.
- by rewrite (sq_uoxx (t1:=t) (t2:=t)) // sqkk_xx //= (negbTE K) cats0.
rewrite [LHS]oevFK [RHS]oevFK; congr oeval; rewrite -!filter_predI.
apply: eq_in_filter=>/= x X; case D: (x \in dom h)=>//=.
by rewrite ole_eqVlt; [case: eqP D K=>// ->-> | by left].
Qed.

Arguments oexleNE [V R a t h ks z0].

(**********************************************************)
(* Interaction of oexec_lt and oexec_le with constructors *)
(**********************************************************)

Lemma oexlt_notin V R a ks t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_lt a ks t h z0 = oevalv a ks h z0.
Proof. by move=>K; rewrite /oexec_lt squo_notinE. Qed.

Arguments oexlt_notin [V R a ks t h z0].

Lemma oexle_notin V R a ks t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_le a ks t h z0 = oevalv a ks h z0.
Proof. by move=>K; rewrite /oexec_le squx_notinE. Qed.

Arguments oexle_notin [V R a ks t h z0].

Lemma oexlt_cat V R a ks1 ks2 t (h : natmap V) (z0 : R) :
        t \notin ks1 -> ~~ has (mem ks1) ks2 ->
        oexec_lt a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_lt a ks1 t h z0
        else oexec_lt a ks2 t h (oexec_lt a ks1 t h z0).
Proof.
move=>T U; rewrite /oexec_lt squo_catE //.
by case: ifP=>//; rewrite oev_cat (squo_notinE (ks:=ks1)).
Qed.

Arguments oexlt_cat [V R a ks1 ks2 t h z0].

Lemma oexle_cat V R a ks1 ks2 t (h : natmap V) (z0 : R) :
        t \notin ks1 -> ~~ has (mem ks1) ks2 ->
        oexec_le a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_le a ks1 t h z0
        else oexec_le a ks2 t h (oexec_le a ks1 t h z0).
Proof.
move=>T U; rewrite /oexec_le squx_catE // (negbTE T).
by rewrite oev_cat (squx_notinE (ks:=ks1)).
Qed.

Arguments oexle_cat [V R a ks1 ks2 t h z0].

Lemma oexlt_cons V R a ks k t v (h : natmap V) (z0 : R) :
        k \notin ks ->
        (k, v) \In h -> t != k ->
        oexec_lt a (k :: ks) t h z0 = oexec_lt a ks t h (a z0 v).
Proof.
move=>U H Ntk; rewrite /oexec_lt squo_consE // (negbTE Ntk) /=.
by move/In_find: H=>->.
Qed.

Arguments oexlt_cons [V R a ks k t v h z0].

Lemma oexle_cons V R a ks k t v (h : natmap V) (z0 : R) :
        k \notin ks ->
        (k, v) \In h ->
        oexec_le a (k :: ks) t h z0 =
        if t == k then a z0 v else oexec_le a ks t h (a z0 v).
Proof.
move=>U H; rewrite /oexec_le squx_consE //=.
by case: eqP=>/=; move/In_find: H=>->.
Qed.

Arguments oexle_cons [V R a ks k t v h z0].

(* for oexlt, we need to cover the case when k == t *)
Lemma oexlt_cons_same V R a ks k (h : natmap V) (z0 : R) :
        oexec_lt a (k :: ks) k h z0 = z0.
Proof. by rewrite /oexec_lt squo_consL. Qed.

Arguments oexlt_cons_same {V R a ks k h z0}.

Lemma oexlt_cons_notin V R a ks k t (h : natmap V) (z0 : R) :
        k \notin dom h -> t != k ->
        oexec_lt a (k :: ks) t h z0 = oexec_lt a ks t h z0.
Proof.
move=>H Ntk; rewrite /oexec_lt /sq_olt /= oltL Ntk /=.
case: dom_find (H)=>// -> _.
rewrite [in LHS]oevFK [in RHS]oevFK; congr oeval.
rewrite -!filter_predI; apply: eq_in_filter=>x X /=.
case Dx: (x \in dom h)=>//=; rewrite olt_cons Ntk /=.
by case: eqP Dx H=>// ->->.
Qed.

Arguments oexlt_cons_notin [V R a ks k t h z0].

(* for oexle, we have two "notin" lemmas *)
Lemma oexle_cons_same_notin V R a ks k (h : natmap V) (z0 : R) :
        k \notin dom h -> oexec_le a (k :: ks) k h z0 = z0.
Proof.
move=>H.
rewrite /oexec_le [in LHS]oevFK squx_consLX /= (negbTE H).
set j := filter _ _; rewrite (_ : j = [::]) //.
apply/eqP/filter_nilP=>x; rewrite mem_filter /=.
by case: eqP H=>// -> /negbTE ->.
Qed.

Arguments oexle_cons_same_notin [V R a ks k h z0].

Lemma oexle_cons_notin V R a ks k t (h : natmap V) (z0 : R) :
        k \notin dom h -> t != k ->
        oexec_le a (k :: ks) t h z0 = oexec_le a ks t h z0.
Proof.
move=>H Ntk; rewrite /oexec_le [in LHS]oevFK [in RHS]oevFK.
rewrite -!filter_predI /= (negbTE H) /=.
congr oeval; apply: eq_in_filter=>x X /=.
by rewrite ole_cons Ntk /=; case: eqP H=>// -> /negbTE ->.
Qed.

Arguments oexle_cons_notin [V R a ks k t h z0].

Lemma oexlt_rcons V R a ks k t (h : natmap V) (z0 : R) :
        k \notin ks -> t \in ks ->
        oexec_lt a (rcons ks k) t h z0 = oexec_lt a ks t h z0.
Proof. by move=>U T; rewrite /oexec_lt squo_rconsE // T. Qed.

Arguments oexlt_rcons [V R a ks k t h z0].

Lemma oexle_rcons V R a ks k t (h : natmap V) (z0 : R) :
        k \notin ks -> t \in ks ->
        oexec_le a (rcons ks k) t h z0 = oexec_le a ks t h z0.
Proof. by move=>U T; rewrite /oexec_le squx_rconsE // T. Qed.

Arguments oexle_rcons [V R a ks k t h z0].

Lemma oexlt_rcons_notin V R a ks k t v (h : natmap V) (z0 : R) :
        k \notin ks ->
        (k, v) \In h -> t \notin ks -> t != k ->
        oexec_lt a (rcons ks k) t h z0 =
        a (oexec_lt a ks t h z0) v.
Proof.
move=>U H T Ntk; rewrite /oexec_lt squo_rconsE // (negbTE T) (negbTE Ntk).
by rewrite oev_rconsE squo_notinE //; move/In_find: H=>->.
Qed.

Arguments oexlt_rcons_notin [V R a ks k t v h z0].

Lemma oexle_rcons_notin V R a ks k t (h : natmap V) (z0 : R) :
        k \notin ks -> t \notin ks ->
        oexec_le a (rcons ks k) t h z0 = oevalv a (rcons ks k) h z0.
Proof. by move=>U T; rewrite /oexec_le squx_rconsE // (negbTE T). Qed.

Arguments oexle_rcons_notin [V R a ks k t h z0].

(* in case of oexlt we must cover the case when t == k *)
Lemma oexlt_rcons_same V R a ks k (h : natmap V) (z0 : R) :
        k \notin ks ->
        oexec_lt a (rcons ks k) k h z0 = oevalv a ks h z0.
Proof. by move=>U; rewrite /oexec_lt squo_rcons_sameE. Qed.

Arguments oexlt_rcons_same [V R a ks k h z0].

(* in case of oexle, case t == k can be optimized *)
Lemma oexle_rcons_same V R a ks k (h : natmap V) (z0 : R) :
        k \notin ks ->
        oexec_le a (rcons ks k) k h z0 = oevalv a (rcons ks k) h z0.
Proof. by move=>U; rewrite oexle_rcons_notin. Qed.

Arguments oexle_rcons_same [V R a ks k h z0].

(* in case of oexle, when we know the value at k *)
(* we can further expand the right-hand side *)
Lemma oexle_rcons_notin_in V R a ks k t v (h : natmap V) (z0 : R) :
        k \notin ks -> uniq ks ->
        (k, v) \In h -> t \notin ks ->
        oexec_le a (rcons ks k) t h z0 = a (oexec_le a ks t h z0) v.
Proof.
move=>K U H T; rewrite oexle_rcons_notin // oev_rconsE.
by move/In_find: (H)=>->; rewrite oexleNE ?T //= /oexec_lt squo_notinE.
Qed.

Arguments oexle_rcons_notin_in [V R a ks k t v h z0].

(* oexlt/oexle filter lemmas *)

Lemma oexlt_umfilt V R a ks p t (h : natmap V) (z0 : R) :
        oexec_lt a ks t (um_filterk p h) z0 =
        oevalv a (filter p {sqint t ks|) h z0.
Proof. by rewrite /oexec_lt oev_filter. Qed.

Arguments oexlt_umfilt {V R a ks p t h z0}.

Lemma oexle_umfilt V R a ks p t (h : natmap V) (z0 : R) :
        oexec_le a ks t (um_filterk p h) z0 =
        oevalv a (filter p {sqint t ks]) h z0.
Proof. by rewrite /oexec_le oev_filter. Qed.

Arguments oexle_umfilt {V R a ks p t h z0}.

(* two somewhat simpler rewrites under a condition *)
Lemma oexlt_umfiltN V R a ks p t (h : natmap V) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_lt a ks t (um_filterk p h) z0 =
        oexec_lt a (filter p ks) t h z0.
Proof.
move=>H; rewrite /oexec_lt !oev_filter !oev_umfilt.
apply: eq_in_oevK; rewrite -!filter_predI; apply: eq_in_filter.
move=>k Ks /=; rewrite !find_umfilt.
case D : (k \in dom h)=>//=; case/In_domX: D=>v /In_find ->.
case Pk : (p k); case: ifP=>//= H1; first by rewrite (olt_filterR _ H1) ?H.
by apply: contraFF H1=>H1; rewrite (olt_filterL _ H1) // Pk !orbT.
Qed.

Arguments oexlt_umfiltN [V R a ks p t h z0].

Lemma oexle_umfiltN V R a ks p t (h : natmap V) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_le a ks t (um_filterk p h) z0 =
        oexec_le a (filter p ks) t h z0.
Proof.
move=>H; rewrite /oexec_le !oev_filter !oev_umfilt.
apply: eq_in_oevK; rewrite -!filter_predI; apply: eq_in_filter.
move=>k Ks /=; rewrite find_umfilt find_umfilt.
case D : (k \in dom h)=>//=; case/In_domX: D=>v /In_find ->.
case Pk : (p k); case: ifP=>//= H1; first by rewrite (ole_filterR _ H1) ?H.
by apply: contraFF H1=>H1; rewrite (ole_filterL _ H1) // Pk !orbT.
Qed.

Arguments oexle_umfiltN [V R a ks p t h z0].

(* restating the last two lemmas for the other direction *)
Lemma oexlt_filter V R a ks p t (h : natmap V) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_lt a (filter p ks) t h z0 =
        oexec_lt a ks t (um_filterk p h) z0.
Proof. by move=>H; rewrite (oexlt_umfiltN H). Qed.

Lemma oexle_filter V R a ks p t (h : natmap V) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_le a (filter p ks) t h z0 =
        oexec_le a ks t (um_filterk p h) z0.
Proof. by move=>H; rewrite (oexle_umfiltN H). Qed.

(* interaction with the map *)

Lemma oexlt_filter_dom V R a ks t (h : natmap V) (z0 : R) :
        (t \notin ks) || (t \in dom h) ->
        oexec_lt a ks t h z0 =
        oexec_lt a (filter (mem (dom h)) ks) t h z0.
Proof. by move=>H; rewrite oexlt_filter // umfiltk_dom'. Qed.

Lemma oexle_filter_dom V R a ks t (h : natmap V) (z0 : R) :
        (t \notin ks) || (t \in dom h) ->
        oexec_le a ks t h z0 =
        oexec_le a (filter (mem (dom h)) ks) t h z0.
Proof. by move=>H; rewrite oexle_filter // umfiltk_dom'. Qed.

(* interaction of oexlt, oexle and last *)

Lemma oexlt_oexle_last V R a k ks t (h : natmap V) (z0 : R) :
        uniq (k::ks) -> t != k ->
        oexec_lt a (k::ks) t h z0 =
        oexec_le a (k::ks) (last k {sqint t ks|) h z0.
Proof.
move=>U Ntk; rewrite /oexec_lt/oexec_le [LHS]oevFK [RHS]oevFK -!filter_predI.
by congr oeval; apply: eq_in_filter=>x X /=; rewrite olt_ole_last.
Qed.

Lemma oev_oexle_last V R a k ks (h : natmap V) (z0 : R) :
        uniq (k::ks) ->
        oevalv a (k::ks) h z0 =
        oexec_le a (k::ks) (last k ks) h z0.
Proof.
move=>U; move: (U)=>/= /andP [U1 U2].
rewrite /oexec_le squx_consE //.
case: eqP=>[/last_nochange|/eqP/last_change H].
- by rewrite (negbTE U1); move/eqP=>->.
rewrite /sq_ole /=; congr oeval.
rewrite -[LHS]filter_predT; apply/esym/eq_in_filter.
by move=>x X; apply: ole_last.
Qed.

(*******************************************************)
(* oexlt/oexle on endpoints of intervals of invariance *)
(*******************************************************)

(* these can be called "induction" lemmas over the interval *)

Definition oex_inv V R (P : R -> Prop) a ks (h : natmap V) (z0 : R) :=
  forall k v, (k, v) \In h ->
    let z := oexec_lt a ks k h z0 in P z -> P (a z v).

(* The naming schema in these lemmas is based on backward reasoning *)
(* E.g., the suffix ox means we're proving an lt_fact (o) from le_fact (x) *)

(* two-sided intervals *)

Lemma oex_ox V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <[ks] t2 ->
        {in |sqint t1 t2 ks|, oex_inv P a ks h z0} ->
        P (oexec_le a ks t1 h z0) -> P (oexec_lt a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_lt (sq_uxoo U T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in |sqint t1 t2 ks| by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter -andbA=>/and3P [T1K _ Ks].
rewrite (sq_oxoo (x:=k)) // sqoxR // -catA /= in Eh.
suff -> : ks1 = |sqint t1 k ks| by rewrite -sq_uxoo //; apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr andbF.
Qed.

(* one can try to derive the next lemma from the previous *)
(* but we need to reason about successor of t1 in ks *)
(* which we don't have yet. Hence, we prove the lemma directly *)
(* using the same approach as in the previous lemma. *)

Lemma oex_oo V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in [sqint t1 t2 ks|, oex_inv P a ks h z0} ->
        P (oexec_lt a ks t1 h z0) -> P (oexec_lt a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_lt (sq_uoxo U T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in [sqint t1 t2 ks| by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter -andbA=>/and3P [T1K _ Ks].
rewrite (sq_xxoo (x:=k)) // sqxxR // -catA /= in Eh.
suff -> : ks1 = [sqint t1 k ks| by rewrite -sq_uoxo //; apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr andbF.
Qed.

Lemma oex_xo V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in [sqint t1 t2 ks], oex_inv P a ks h z0} ->
        P (oexec_lt a ks t1 h z0) -> P (oexec_le a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_le (sq_uoxx U T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in [sqint t1 t2 ks] by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter -andbA=>/and3P [T1K _ Ks].
rewrite (sq_xxox (x:=k)) // sqxxR // -catA /= in Eh.
suff -> : ks1 = [sqint t1 k ks| by rewrite -sq_uoxo //; apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr andbF.
Qed.

Lemma oex_xx V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in |sqint t1 t2 ks], oex_inv P a ks h z0} ->
        P (oexec_le a ks t1 h z0) -> P (oexec_le a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_le (sq_uxox U T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in |sqint t1 t2 ks] by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter -andbA=>/and3P [T1K _ Ks].
rewrite (sq_oxox (x:=k)) // sqoxR // -catA /= in Eh.
suff -> : ks1 = |sqint t1 k ks| by rewrite -sq_uxoo //; apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr andbF.
Qed.

Arguments oex_ox [V R] P [a ks h t1 t2 z0].
Arguments oex_oo [V R] P [a ks h t1 t2 z0].
Arguments oex_xo [V R] P [a ks h t1 t2 z0].
Arguments oex_xx [V R] P [a ks h t1 t2 z0].

(* one-sided intervals *)

Lemma oex_ux V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in |sqint t ks}, oex_inv P a ks h z0} ->
        P (oexec_le a ks t h z0) -> P (oevalv a ks h z0).
Proof.
move=>U IH P0; rewrite (sq_uxou t U) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in |sqint t ks} by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter=>/andP [TK Ks].
rewrite (sq_oxou (t2:=k)) ?(oltW TK) // sqoxR // -catA /= in Eh.
suff -> : ks1 = |sqint t k ks| by rewrite -sq_uxoo //; apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr andbF.
Qed.

Lemma oex_uo V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in [sqint t ks}, oex_inv P a ks h z0} ->
        P (oexec_lt a ks t h z0) -> P (oevalv a ks h z0).
Proof.
move=>U IH P0; rewrite (sq_uoxu t U) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in [sqint t ks} by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter=>/andP [TK Ks].
rewrite (sq_xxou (t2:=k)) // sqxxR // -catA /= in Eh.
suff -> : ks1 = [sqint t k ks| by rewrite -sq_uoxo //; apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr andbF.
Qed.

Lemma oex_xu V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in {sqint t ks], oex_inv P a ks h z0} ->
        P z0 -> P (oexec_le a ks t h z0).
Proof.
move=>U IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in {sqint t ks] by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter=>/andP [TK Ks].
rewrite (sq_uxox (t1:=k)) // squxR // -catA /= in Eh.
suff -> : ks1 = {sqint k ks| by apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr.
Qed.

Lemma oex_ou V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in {sqint t ks|, oex_inv P a ks h z0} ->
        P z0 -> P (oexec_lt a ks t h z0).
Proof.
move=>U IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh filter_uniq //; case/andP: U.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in {sqint t ks| by rewrite Eh mem_cat inE eq_refl orbT.
move: (K); rewrite mem_filter=>/andP [TK Ks].
rewrite (sq_uxoo (t1:=k)) // squxR // -catA /= in Eh.
suff -> : ks1 = {sqint k ks| by apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr.
Qed.

Arguments oex_ux [V R] P [a ks h t z0].
Arguments oex_uo [V R] P [a ks h t z0].
Arguments oex_xu [V R] P [a ks h t z0].
Arguments oex_ou [V R] P [a ks h t z0].

(* whole list *)

Lemma oex_uu V R (P : R -> Prop) a ks (h : natmap V) (z0 : R) :
        uniq ks ->
        {in ks, oex_inv P a ks h z0} ->
        P z0 -> P (oevalv a ks h z0).
Proof.
move=>U IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have Us : uniq (ks1 ++ k :: ks2) by rewrite -Eh.
have Nk : k \notin ks1 by apply: contraL Us=>E; rewrite cat_uniq /= E andbF.
have K : k \in ks by rewrite Eh mem_cat inE eq_refl orbT.
rewrite (sq_uxou k U) squxR // -catA /= in Eh.
suff -> : ks1 = {sqint k ks| by apply: IH.
by rewrite (cat_cancel _ _ Eh) // mem_filter olt_irr.
Qed.

Arguments oex_uu [V R] P [a ks h z0].

(**********************************************)
(* functional versions of the interval lemmas *)
(**********************************************)

Definition oexF_inv V R X (f : R -> X) a ks (h : natmap V) (z0 : R) :=
  forall k v, (k, v) \In h ->
    let z := oexec_lt a ks k h z0 in f (a z v) = f z.

(* two-sided intervals *)

Lemma oexF_ox V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <[ks] t2 ->
        {in |sqint t1 t2 ks|, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t2 h z0) = f (oexec_le a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_le a ks t1 h z0).
by apply: (oex_ox P) T _ _=>// x S v K E ; rewrite /P -E; apply: H.
Qed.

Lemma oexF_oo V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in [sqint t1 t2 ks|, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t2 h z0) = f (oexec_lt a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_lt a ks t1 h z0).
by apply: (oex_oo P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xo V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in [sqint t1 t2 ks], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t2 h z0) = f (oexec_lt a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_lt a ks t1 h z0).
by apply: (oex_xo P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xx V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in |sqint t1 t2 ks], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t2 h z0) = f (oexec_le a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_le a ks t1 h z0).
by apply: (oex_xx P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Arguments oexF_ox [V R X] f [a ks h t1 t2 z0].
Arguments oexF_oo [V R X] f [a ks h t1 t2 z0].
Arguments oexF_xo [V R X] f [a ks h t1 t2 z0].
Arguments oexF_xx [V R X] f [a ks h t1 t2 z0].

(* one-sided intervals *)

Lemma oexF_ux V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in |sqint t ks}, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f (oexec_le a ks t h z0).
Proof.
move=>U H; pose P := fun x => f x = f (oexec_le a ks t h z0).
by apply: (oex_ux P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_uo V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in [sqint t ks}, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f (oexec_lt a ks t h z0).
Proof.
move=>U H; pose P := fun x => f x = f (oexec_lt a ks t h z0).
by apply: (oex_uo P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xu V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in {sqint t ks], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t h z0) = f z0.
Proof.
move=>U H; pose P := fun x => f x = f z0.
by apply: (oex_xu P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_ou V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in {sqint t ks|, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t h z0) = f z0.
Proof.
move=>U H; pose P := fun x => f x = f z0.
by apply: (oex_ou P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Arguments oexF_ux [V R X] f [a ks h t z0].
Arguments oexF_uo [V R X] f [a ks h t z0].
Arguments oexF_xu [V R X] f [a ks h t z0].
Arguments oexF_ou [V R X] f [a ks h t z0].

(* whole list *)

Lemma oexF_uu V R X (f : R -> X) a ks (h : natmap V) (z0 : R) :
        uniq ks ->
        {in ks, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f z0.
Proof.
move=>U H; pose P := fun x => f x = f z0.
by apply: (oex_uu P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Arguments oexF_uu [V R X] f [a ks h z0].

(* we can now combine the split lemmas with *)
(* cons properties of oeval, to obtain a point-split *)
(* when the middle point is in the map *)

Lemma oev2_split V R a t1 v (h : natmap V) ks (z0 : R) :
        uniq ks -> t1 \in ks -> (t1, v) \In h ->
        oevalv a ks h z0 =
        oevalv a |sqint t1 ks} h (a (oexec_lt a ks t1 h z0) v).
Proof.
move=>U D H; rewrite {1}(sq_uoxu t1 U) oev_cat.
by rewrite sqxuL //=; move/In_find: H=>->.
Qed.

Arguments oev2_split [V R a t1 v h ks z0] _ _ _.

Lemma oex2_split V R a t1 t2 v (h : natmap V) ks (z0 : R) :
        uniq ks -> t1 <[ks] t2 -> t1 \in ks -> (t1, v) \In h ->
        oexec_lt a ks t2 h z0 =
        oevalv a |sqint t1 t2 ks| h (a (oexec_lt a ks t1 h z0) v).
Proof.
move=>U T D H; rewrite /oexec_lt.
rewrite (sq_uoxo U (oltW T)) oev_cat sqxoL //=.
by move/In_find: H=>->.
Qed.

Arguments oex2_split [V R a t1 t2 v h ks z0] _ _ _ _.

(* we frequently iterate oex2_split, so the following saves verbiage *)
Lemma oex3_split V R a t1 t2 t3 v1 v2 (h : natmap V) ks (z0 : R) :
        uniq ks ->
        t1 <[ks] t2 -> t1 \in ks -> (t1, v1) \In h ->
        t2 <[ks] t3 -> t2 \in ks -> (t2, v2) \In h ->
        oexec_lt a ks t3 h z0 =
        oevalv a |sqint t2 t3 ks| h
                 (a (oevalv a |sqint t1 t2 ks| h
                    (a (oexec_lt a ks t1 h z0) v1))
                 v2).
Proof.
move=>U T1 D1 H1 T2 D2 H2.
by rewrite (oex2_split U T2 D2 H2) (oex2_split U T1 D1 H1).
Qed.

Arguments oex3_split [V R a t1 t2 t3 v1 v2 h ks z0] _ _ _ _ _ _ _.

(******************************************)
(* Interaction of consec with oexlt/oexle *)
(******************************************)

Lemma oexlt_consec V R a ks t1 t2 (h : natmap V) (z0 : R) :
        uniq ks ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 = oexec_le a ks t1 h z0.
Proof.
move=>U C; apply: (oexF_ox id)=>//; first by apply: consec_olt.
by move=>x; rewrite consec_oo.
Qed.

Arguments oexlt_consec [V R a ks t1 t2 h z0].

(* the following is direct *)
Lemma oexlt_split V R a x1 t1 t2 x2 (h : natmap V) (z0 : R) :
        uniq (x1++t1::t2::x2) ->
        oexec_lt a (x1++t1::t2::x2) t2 h z0 =
        oexec_le a (x1++t1::t2::x2) t1 h z0.
Proof.
move=>U; apply: oexlt_consec=>//; apply/consecP_split=>//.
- by rewrite mem_cat !inE eq_refl !orbT.
by eauto.
Qed.

Lemma oexlt_consec_in V R a t1 t2 v (h : natmap V) ks (z0 : R) :
        uniq ks ->
        (t1, v) \In h ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 = a (oexec_lt a ks t1 h z0) v.
Proof.
move=>U H C; move/olt_memE: (consec_olt C)=>T.
by rewrite (oexlt_consec U C) (oexleE U T H).
Qed.

Lemma oexlt_consec_fst V R a t (h : natmap V) k ks (z0 : R) :
        uniq (k::ks) -> k \notin dom h -> t \in k::ks ->
        consec (k::ks) k t ->
        oexec_lt a (k::ks) t h z0 = z0.
Proof.
move=>U K T C; case/(consecP_split _ U T): C=>xs1 [xs2] X.
case: xs1 X U {T}=>[|x xs1]; last first.
- by case=>->-> /=; rewrite mem_cat inE eq_refl !orbT.
case=>->{ks}; rewrite /= inE negb_or -andbA; case/and4P=>U1 U2 U3 U4.
rewrite oexlt_cons_notin ?inE 1?negb_or ?(eq_sym t) ?U1 ?U2 //.
by rewrite oexlt_cons_same.
Qed.

Lemma oexlt_consec_find V R a t1 t2 (h : natmap V) ks (z0 : R) :
        uniq ks ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 =
        if find t1 h is Some e then a (oexec_lt a ks t1 h z0) e
        else oexec_lt a ks t1 h z0.
Proof.
move=>U C; rewrite (oexlt_consec U C).
case E : (find t1 h)=>[e|]; first by move/In_find: E=>/(oexleE U (consec_mem C)) ->.
by rewrite oexleNE // orbC; move/In_findN: E=>->.
Qed.

Arguments oexlt_consec_find [V R a t1 t2 h ks z0].


(*******************)
(*******************)
(* Gapless natmaps *)
(*******************)
(*******************)

Section Gapless.
Variable A : Type.
Implicit Type h : natmap A.

Definition gapless h := forall k, 0 < k <= last_key h -> k \in dom h.

Definition gaplessb h := all (fun t => t \in dom h) (iota 1 (last_key h)).

Lemma gaplessP h : reflect (gapless h) (gaplessb h).
Proof.
case V: (gaplessb h);constructor; last first.
- move=>H;apply/(elimF idP V)/allP=>?.
  by rewrite mem_iota add1n ltnS=>?; apply/H.
by move/allP:V=>H t;move: (H t);rewrite mem_iota add1n ltnS.
Qed.

Lemma gp_undef : gapless undef.
Proof. by move=>k; rewrite lastkey_undef; case: k. Qed.

Lemma gp0 : gapless Unit.
Proof. by move=>k; rewrite lastkey0; case: k. Qed.

Lemma gp_fresh h u : gapless (fresh h \-> u \+ h) <-> gapless h.
Proof.
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undef.
split=>H k; move: (V); rewrite -(valid_fresh u (leqnn _))=>V'; last first.
- rewrite lastkey_fresh // domPtUn inE V' /= (leq_eqVlt k) eq_sym.
  by move: (H k); rewrite -(ltnS k); case: (ltngtP k (last_key h).+1).
rewrite -(ltnS k) -/(fresh h); case/andP=>Z N.
move: (H k); rewrite lastkey_fresh // domPtUn inE V' Z /= leq_eqVlt eq_sym.
by case: ltngtP N=>//= _ _; apply.
Qed.

Lemma gpPtUn h k u :
        valid (k \-> u \+ h) ->
        gapless (k \-> u \+ h) -> last_key h < k -> k = fresh h.
Proof.
move=>V C N; apply/eqP/contraT=>X.
have Y : fresh h < k by rewrite leq_eqVlt eq_sym (negbTE X) in N.
suff Z : last_key (k \-> u \+ h) = k.
- move: (C (fresh h)); rewrite Z (leq_eqVlt _ k) Y orbT andbT; move/(_ (erefl _)).
  rewrite domPtUn inE (negbTE X) /=; case/andP=>_ /dom_ordfresh.
  by rewrite ltnn.
apply: max_lastkey (find_some (findPtUn V)) _ => x.
rewrite domUn inE; case/andP=>_ /orP [].
- by rewrite domPt inE; case/andP=>_ /eqP ->.
by move/lastkey_max/leq_ltn_trans/(_ N)/ltnW.
Qed.

Lemma gaplessPtUnE u2 u1 h k :
        gapless (k \-> u1 \+ h) <-> gapless (k \-> u2 \+ h).
Proof.
rewrite /gapless (lastkeyPtUnE u2); split=>H t /H;
by rewrite !domPtUn !inE !validPtUn.
Qed.

Lemma gapless_pleq h1 h2 :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] ->
        exists h, h2 = h1 \+ h /\ forall k, k \in dom h -> last_key h1 < k.
Proof.
move=>G V H; case: H V=>h ->{h2} V; exists h; split=>// k D.
apply: contraR (dom_inNR V D)=>H; apply: G; move/dom_cond: D=>/= D.
by rewrite lt0n D leqNgt.
Qed.

End Gapless.

Arguments gp_fresh [A][h] u.

(*****************************)
(*****************************)
(* Natmaps with binary range *)
(*****************************)
(*****************************)

Section AtVal.
Variable A : Type.
Implicit Type h : natmap (A * A).

Definition atval v t h := oapp snd v (find t h).

Lemma atvalUn v t h1 h2 :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        (forall k : nat, k \in dom h2 -> last_key h1 < k) ->
        atval v t (h1 \+ h2) = atval v t h1.
Proof.
move=>V K H; rewrite /atval findUnR //.
by case: ifP=>// /H; rewrite ltnNge K.
Qed.

Lemma umpleq_atval v t h1 h2 :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        atval v t h2 = atval v t h1.
Proof.
move=>G V H K; case/(gapless_pleq G V): {V} H (V)=>h [->{h2} H] V.
by apply: atvalUn.
Qed.

Definition last_val v h := atval v (last_key h) h.

Lemma lastval0 v : last_val v Unit = v.
Proof. by rewrite /last_val /atval lastkey0 find0E. Qed.

Lemma lastvalPt v p x : p != 0 -> last_val v (p \-> x) = x.2.
Proof.
by move=>V; rewrite /last_val /atval lastkeyPt // findPt /= V.
Qed.

Lemma lastval_fresh v x h :
        valid h -> last_val v (fresh h \-> x \+ h) = x.2.
Proof.
by move=>V; rewrite /last_val /atval lastkey_fresh // findPtUn // valid_fresh.
Qed.

Lemma lastvalUn v h1 h2 :
        last_val v (h1 \+ h2) =
        if valid (h1 \+ h2) then
          if last_key h1 < last_key h2 then last_val v h2 else last_val v h1
        else v.
Proof.
rewrite /last_val /atval lastkeyUn maxnC /maxn.
case: ifP; last by move/negbT/invalidE=>->; rewrite find_undef.
case: (ltngtP (last_key h1) (last_key h2)) => N V.
- by rewrite findUnR // (dom_lastkeyE N).
- by rewrite findUnL // (dom_lastkeyE N).
by rewrite !(lastkeyUn0 V N) unitL lastkey0 find0E.
Qed.

Lemma lastval_freshUn v x h1 h2 :
        valid h1 -> [pcm h2 <= h1] ->
        last_val v (fresh h1 \-> x \+ h2) = x.2.
Proof.
move=>V H; rewrite /last_val /atval.
rewrite lastkey_freshUn // findPtUn // valid_freshUn //.
by case: H V=>h -> /validL.
Qed.

Lemma lastval_indom v h :
        last_val v h <> v -> last_key h \in dom h.
Proof. by rewrite /last_val /atval; case: dom_find=>// ->. Qed.

End AtVal.
