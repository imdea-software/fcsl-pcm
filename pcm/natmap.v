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
From fcsl Require Import prelude pcm pred finmap mutex morphism.
From fcsl Require Export unionmap automap rtc.
From fcsl Require Import options.

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
Variable A : Type.
Implicit Type h : natmap A.

Lemma lastkey_undef : last_key (undef : natmap A) = 0.
Proof. by rewrite /last_key /undef /= !umEX. Qed.

Lemma lastkey0 : last_key (Unit : natmap A) = 0.
Proof. by rewrite /last_key /Unit /= !umEX. Qed.

Lemma lastkey_dom h : valid h -> last_key h \notin dom h -> h = Unit.
Proof.
rewrite /valid /= /last_key /Unit /= !umEX /= -{4}[h]UMC.tfE.
case: (UMC.from h)=>//=; case=>s H /= H1 _ /seq_last_in.
rewrite /UM.empty UMC.eqE UM.umapE /supp fmapE /= {H H1}.
by elim: s.
Qed.

Lemma dom_lastkey0P h : last_key h = 0 <-> dom h = [::].
Proof.
rewrite -nm_dom0; split; last first.
- by case=>E; subst h; rewrite ?lastkey_undef ?lastkey0.
move=>E; case V : (valid h); last by left; move/invalidE: (negbT V).
right; apply: lastkey_dom=>//; rewrite E.
by apply: contraT; rewrite negbK; apply: dom_cond.
Qed.

Lemma dom_lastkey h :  valid h -> ~~ unitb h -> last_key h \in dom h.
Proof. by move=>X; apply: contraR; move/(lastkey_dom X)=>->; apply/unitbP. Qed.

Lemma lastkeyxx h : valid h -> last_key h = 0 -> h = Unit.
Proof.
by move=>V H; apply: lastkey_dom V _; apply/negP=>/dom_cond; rewrite H.
Qed.

Lemma dom_lastkeyE h a : a < last_key h -> last_key h \in dom h.
Proof.
move=>H; case V : (valid h); last first.
- by move/invalidE: (negbT V) H=>->; rewrite lastkey_undef.
by apply: dom_lastkey V (contraL _ H)=>/unitbE ->; rewrite lastkey0.
Qed.

Lemma lastkey_max h x : x \in dom h -> x <= last_key h.
Proof.
rewrite /last_key /= !umEX; case: (UMC.from h)=>//; case=>s H _ /=.
rewrite /supp /ord /= (leq_eqVlt x) orbC.
by apply: sorted_last_key_maxR (sorted_oleq H)=>//; apply: otrans.
Qed.

Lemma max_lastkey h x :
        x \in dom h -> {in dom h, forall y, y <= x} -> last_key h = x.
Proof.
rewrite /last_key !umEX; case: (UMC.from h)=>//; case=>s H _ /=.
move=>H1 /= H2; apply: sorted_max_key_last (sorted_oleq H) H1 _=>//.
- by apply: otrans.
- by apply: oantisym.
by move=>z /(H2 z); rewrite leq_eqVlt orbC.
Qed.

Lemma lastkey_leq h x :
        {in dom h, forall y, y <= x} <-> last_key h <= x.
Proof.
split; last by move=>D y Y; apply: leq_trans D; apply: lastkey_max Y.
case V : (valid h); last first.
- by move/negbT/invalidE: V=>->; rewrite lastkey_undef.
case E: (unitb h); first by move/unitbP: E=>->; rewrite lastkey0.
by apply; rewrite dom_lastkey // E.
Qed.

Lemma lastkey_ltn a h x :
        a < last_key h -> {in dom h, forall y, y < x} <-> last_key h < x.
Proof.
move/dom_lastkeyE=>D; split; first by apply.
by move=>Y y X; apply: leq_ltn_trans Y; apply: lastkey_max.
Qed.

Lemma lastkeyPt (x : nat) (v : A) : x != 0 -> last_key (x \-> v) = x.
Proof. by rewrite /last_key domPtK /= => ->. Qed.

Lemma hist_path B (h : natmap B) : path oleq 0 (dom h).
Proof.
rewrite !umEX; case: (UMC.from h)=>//= {}h _; case: h; case=>//= x s H.
rewrite {1}/oleq /ord /= orbC -leq_eqVlt /=.
by apply: sub_path H=>z y; rewrite /oleq=>->.
Qed.

Lemma lastkey_mono B (h1 : natmap A) (h2 : natmap B) :
        {subset dom h1 <= dom h2} -> last_key h1 <= last_key h2.
Proof.
rewrite leq_eqVlt orbC; apply: (seq_last_monoR _ (@otrans nat_ordType))=>//;
by apply: hist_path.
Qed.

Lemma lastkeyfUn h1 h2 :
        valid (h1 \+ h2) -> last_key h1 <= last_key (h1 \+ h2).
Proof. by move=>X; apply: lastkey_mono=>x; rewrite domUn inE X => ->. Qed.

Lemma lastkeyUnf h1 h2 :
        valid (h1 \+ h2) -> last_key h2 <= last_key (h1 \+ h2).
Proof. by rewrite joinC; apply: lastkeyfUn. Qed.

(* a convenient rephrasing of above lemmas *)

Lemma lastkeyUn_mono h1 h2 t :
        valid (h1 \+ h2) -> last_key (h1 \+ h2) < t -> last_key h1 < t.
Proof.
move=>V; apply/leq_trans/lastkey_mono.
by move=>x D; rewrite domUn inE V D.
Qed.

Lemma lastkeyUn0 h1 h2 :
        valid (h1 \+ h2) ->
        last_key h1 = last_key h2 -> (h1 = Unit) * (h2 = Unit).
Proof.
move=>V E.
case E1: (unitb h1).
- move/unitbE: E1 E V=>->; rewrite unitL lastkey0.
  by case/esym/dom_lastkey0P/nm_dom0=>-> //; rewrite valid_undef.
case E2: (unitb h2).
- move/unitbE: E2 E V=>->; rewrite unitR lastkey0.
  by case/dom_lastkey0P/nm_dom0=>-> //; rewrite valid_undef.
case: validUn (V)=>// _ _ /(_ _ (dom_lastkey (validL V) (negbT E1))).
by rewrite E (dom_lastkey (validR V) (negbT E2)).
Qed.

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

Lemma lastkeyPtUn h t u :
        last_key (t \-> u \+ h) =
        if valid (t \-> u \+ h) then maxn t (last_key h) else 0.
Proof.
by rewrite lastkeyUn; case: ifP=>// /validPtUn_cond /= D; rewrite lastkeyPt.
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
Proof. by rewrite !lastkeyPtUn !validPtUn. Qed.

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

Lemma dom_freshUn h1 h2 : valid h1 -> [pcm h2 <= h1] -> fresh h1 \notin dom h2.
Proof.
move=>V [x E]; rewrite {h1}E in V *; apply: contra (@dom_ordfresh _ _) _.
by rewrite joinC in V *; rewrite -leqNgt; apply: lastkeyUnf.
Qed.

Lemma valid_ge_fresh h v t :
        fresh h <= t -> valid (t \-> v \+ h) = valid h.
Proof. by move=>N; rewrite validPtUn /= (fresh0N N) (ordfresh_dom N) andbT. Qed.

Lemma dom_freshUnN h1 h2 x :
        valid h1 -> [pcm h2 <= h1] -> x \in dom h2 -> x != fresh h1.
Proof. by move=>V H; apply: contraL=>/eqP ->; apply: dom_freshUn. Qed.

Lemma dom_fresh h : fresh h \notin dom h.
Proof. by move: (dom_freshn h 0); rewrite addn0.  Qed.

Lemma valid_freshUn h1 h2 v :
        valid h1 -> [pcm h2 <= h1] -> valid (fresh h1 \-> v \+ h2) = valid h2.
Proof.
move=>V [x E]; rewrite {h1}E in V *.
by rewrite validPtUn dom_freshUn // andbT.
Qed.

Lemma valid_fresh h v : valid (fresh h \-> v \+ h) = valid h.
Proof. by rewrite validPtUn dom_fresh andbT. Qed.

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
- by rewrite domUn inE valid_fresh Vf domPt inE eq_refl.
rewrite domUn inE /= valid_fresh Vf /= domPt inE /= eq_sym.
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
split=>H k; move: (V); rewrite -(valid_fresh _ u)=>V'; last first.
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

(* in case A = bool *)
Lemma lastval_indomb h :
        last_val false h -> last_key h \in dom h.
Proof. by move=>H; apply: (lastval_indom (v:=false)); rewrite H. Qed.

(* Continuous maps with binary range *)

Section Continuous.
Variable A : Type.
Implicit Type h : natmap (A * A).

Definition continuous v h :=
  forall k x, find k.+1 h = Some x -> oapp snd v (find k h) = x.1.

Lemma cn_undef v : continuous v undef.
Proof. by move=>x w; rewrite find_undef. Qed.

Lemma cn0 v : continuous v Unit.
Proof. by move=>x w; rewrite find0E. Qed.

Lemma cn_fresh v h x :
        valid h ->
        continuous v (fresh h \-> x \+ h) <->
        continuous v h /\ last_val v h = x.1.
Proof.
rewrite -(valid_fresh _ x)=>V; split; last first.
- case=>C H k y; rewrite !findPtUn2 // eqSS; case: ltngtP=>N.
  - by rewrite ltn_eqF; [apply: C | apply: (ltn_trans N _)].
  - by move/find_some /dom_ordfresh /(ltn_trans N); rewrite ltnn.
  by case=><-; rewrite N ltn_eqF.
move=>C; split; last first.
- move: (C (last_key h) x).
  by rewrite !findPtUn2 // eq_refl ltn_eqF //; apply.
move=>k w; case: (ltnP k (last_key h))=>N; last first.
- by move/find_some /dom_ordfresh /(leq_ltn_trans N); rewrite ltnn.
by move: (C k w); rewrite !findPtUn2 // eqSS !ltn_eqF // (ltn_trans N _).
Qed.

Lemma cn_sub v h x y k :
        valid (k.+1 \-> (x, y) \+ h) -> continuous v (k.+1 \-> (x, y) \+ h) ->
        oapp snd v (find k h) = x.
Proof.
by move=>V /(_ k (x, y)); rewrite !findPtUn2 // eq_refl ltn_eqF //; apply.
Qed.

End Continuous.

Arguments cn_fresh [A][v][h][x] _.

(* Complete natmaps with binary range *)

Section Complete.
Variable A : Type.
Implicit Type h : natmap (A * A).

Definition complete v0 h vn :=
  [/\ valid h, gapless h, continuous v0 h & last_val v0 h = vn].

Lemma cm_valid v0 h vn : complete v0 h vn -> valid h.
Proof. by case. Qed.

Lemma cm0 v : complete v Unit v.
Proof. by split=>//; [apply: gp0 | apply: cn0 | rewrite lastval0]. Qed.

Lemma cm_fresh v0 vn h x :
        complete v0 (fresh h \-> x \+ h) vn <-> vn = x.2 /\ complete v0 h x.1.
Proof.
split.
- by case=>/validR V /gp_fresh G /(cn_fresh V) []; rewrite lastval_fresh.
case=>-> [V] /(gp_fresh x) G C E; split=>//;
by [rewrite valid_fresh | apply/(cn_fresh V) | rewrite lastval_fresh].
Qed.

Lemma cmPtUn v0 vn h k x :
        complete v0 (k \-> x \+ h) vn -> last_key h < k -> k = fresh h.
Proof. by case=>V /(gpPtUn V). Qed.

Lemma cmPt v0 vn k x : complete v0 (k \-> x) vn -> k = 1 /\ x = (v0, vn).
Proof.
case; rewrite validPt; case: k=>//= k _ /(_ 1).
rewrite lastkeyPt //= domPt inE /= => /(_ (erefl _))/eqP ->.
move/(_ 0 x); rewrite findPt findPt2 /= => -> //.
by rewrite /last_val lastkeyPt // /atval findPt /= => <-; case: x.
Qed.

Lemma cmCons v0 vn k x h :
        complete v0 (k \-> x \+ h) vn -> last_key h < k ->
         [/\ k = fresh h, vn = x.2 & complete v0 h x.1].
Proof. by move=>C H; move: {C} (cmPtUn C H) (C)=>-> /cm_fresh []. Qed.

End Complete.

Prenex Implicits cm_valid cmPt.


(************************)
(************************)
(************************)
(* Surgery on histories *)
(* using leq filtering  *)
(************************)
(************************)
(************************)

Notation le t := [pts k _ | k <= t].
Notation lt t := [pts k _ | k < t].

Lemma pts_sub V t1 t2 : t1 <= t2 -> subpred (T:=nat*V) (le t1) (le t2).
Proof. by move=>T [k v] /leq_trans; apply. Qed.

Lemma pts_sub_lt V t1 t2 : t1 < t2 -> subpred (T:=nat*V) (le t1) (lt t2).
Proof. by move=>T [k v] /leq_ltn_trans; apply. Qed.

Lemma ptsD V t1 t2 :
        t1 <= t2 -> predD (le t2) (le t1) =1 [pts k (v : V) | t1 < k <= t2].
Proof. by move=>T [k v] /=; rewrite -ltnNge. Qed.

Lemma ptsD_lt V t1 t2 :
        t1 < t2 -> predD (lt t2) (le t1) =1 [pts k (v : V) | t1 < k < t2].
Proof. by move=>T [k v] /=; rewrite -ltnNge. Qed.

Lemma lastkey_umfilt_leq A (h : natmap A) t : last_key (um_filter (le t) h) <= t.
Proof.
case V : (valid h); last first.
- by move/negbT/invalidE: V=>->; rewrite umfilt_undef lastkey_undef.
have V' : valid (um_filter (le t) h) by rewrite valid_umfilt.
case E : (unitb (um_filter (le t) h)).
- by move/unitbP: E=>->; rewrite lastkey0.
by case/dom_umfilt: (dom_lastkey V' (negbT E))=>v [].
Qed.

Lemma lastkey_umfilt_dom A (h : natmap A) t :
        last_key (um_filter (le t) h) <= last_key h.
Proof. by apply: lastkey_mono; apply: dom_umfilt_subset. Qed.

Lemma umfilt_le_last A (h : natmap A) t :
        last_key h <= t -> um_filter (le t) h = h.
Proof.
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite umfilt_undef.
move=>N; rewrite -{2}[h]umfilt_predT; apply/eq_in_umfilt.
by case=>k v /In_dom/lastkey_max/leq_trans; apply.
Qed.

Lemma umfilt_last A (h : natmap A) : um_filter (le (last_key h)) h = h.
Proof. by apply: umfilt_le_last. Qed.

Lemma umfilt_le_fresh A (h : natmap A) : um_filter (le (fresh h)) h = h.
Proof. by apply: umfilt_le_last; apply: ltnW. Qed.

Lemma umfilt_le0 A (h : natmap A) t :
        valid h -> {in dom h, forall k, t < k} -> um_filter (le t) h = Unit.
Proof.
move=>V D; rewrite -(umfilt_pred0 V).
apply/eq_in_umfilt; case=>k v [/= _][z E]; subst h.
rewrite leqNgt; apply: contraTF (D k _)=>//.
by rewrite domPtUn inE V eq_refl.
Qed.

Lemma umfilt_le_split A (h : natmap A) t1 t2 :
        t1 <= t2 ->
        um_filter (le t2) h =
        um_filter (le t1) h \+ um_filter [pts x _ | t1 < x <= t2] h.
Proof.
move=>T; rewrite -umfilt_dpredU; last first.
- by case=>x y N /=; rewrite negb_and -leqNgt N.
apply/eq_in_umfilt; case=>k v _ => /=.
by case: (leqP k t1)=>//= /leq_trans; apply.
Qed.

Lemma umfilt_lt_split A (h : natmap A) t1 t2 k :
        t1 <= k <= t2 ->
        um_filter [pts x _ | t1 < x <= t2] h =
        um_filter [pts x _ | t1 < x <= k] h \+
        um_filter [pts x _ | k < x <= t2] h.
Proof.
move=>/andP [T1 T2]; rewrite -umfilt_dpredU; last first.
- by case=>x y /andP [N1 N2]; rewrite /= negb_and -leqNgt N2.
apply/eq_in_umfilt; case=>k1 v1 _ /=.
case: (leqP k1 k)=>//=; last by move/(leq_ltn_trans T1)=>->.
by move/leq_trans=>-> //; rewrite orbF.
Qed.

Lemma umfilt_pt_split A (h : natmap A) k v :
        (k, v) \In h -> um_filter [pts x _ | k.-1 < x <= k] h = k \-> v.
Proof.
move=>H; have W : valid h by case: H.
have N: 0 < k by move/In_dom/dom_cond: H; case: k.
have subX : forall m n, 0 < n -> (m < n) = (m <= n.-1) by move=>? [].
rewrite (In_eta H) umfiltPtUn -(In_eta H) subX // W !leqnn /=.
rewrite umfilt_mem0L ?unitR ?validF //.
move=>k1 v1 /InF [_ /=]; rewrite andbC; case: (ltngtP k k1) =>//=.
by rewrite subX //; case: (ltngtP k1 k.-1).
Qed.

Lemma umfilt_leUn A (h1 h2 : natmap A) t :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        {in dom h2, forall k, k > last_key h1} ->
        um_filter (le t) (h1 \+ h2) = um_filter (le t) h1.
Proof.
move=>V K D; rewrite umfiltUn // (umfilt_le0 (validR V)) ?unitR //.
by move=>k /D /(leq_ltn_trans K).
Qed.

Lemma umfilt_le_gapless A (h1 h2 : natmap A) t :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        um_filter (le t) h2 = um_filter (le t) h1.
Proof.
move=>G V H K; case: (gapless_pleq G V H)=>h [? D].
by subst h2; rewrite umfilt_leUn.
Qed.

Lemma dom_umfilt_le_eq A (h : natmap A) t1 t2 :
        t1 \in 0::dom h -> t2 \in 0::dom h ->
        um_filter (le t1) h = um_filter (le t2) h ->
        t1 = t2.
Proof.
rewrite !inE; case/orP=>[/eqP ->|/In_domX [v1 T1]].
- case/orP=>[/eqP ->|/In_domX [v2 T2]] //.
  move/eq_in_umfilt=>/(_ (t2, v2) T2).
  by rewrite leqnn leqn0 eq_sym=>/eqP.
case/orP=>[/eqP ->|/In_domX [v2 T2] L].
- move/eq_in_umfilt=>/(_ (t1, v1) T1).
  by rewrite leqnn leqn0=>/esym/eqP.
move/eq_in_umfilt: (L)=>/(_ (t1, v1) T1).
move/eq_in_umfilt: (L)=>/(_ (t2, v2) T2).
by rewrite !leqnn; case: ltngtP.
Qed.

Lemma eval_leUn A R a (h1 h2 : [pcm of natmap A]) t (z0 : R) :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        {in dom h2, forall k, k > last_key h1} ->
        eval a (le t) (h1 \+ h2) z0 = eval a (le t) h1 z0.
Proof. by move=>V K D; apply: eq_filt_eval; apply: umfilt_leUn. Qed.

Lemma eval_le_gapless A R a (h1 h2 : [pcm of natmap A]) t (z0 : R) :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        eval a (le t) h2 z0 = eval a (le t) h1 z0.
Proof. by move=>G V H K; apply: eq_filt_eval; apply: umfilt_le_gapless. Qed.

Lemma eval_le0 A R a (h : natmap A) (z0 : R) : eval a (le 0) h z0 = z0.
Proof.
case W : (valid h); last first.
- by move/negbT/invalidE: W=>->; rewrite eval_undef.
rewrite eval_umfilt umfilt_mem0L ?eval0 //.
by move=>k v /In_dom/dom_cond; rewrite /=; case: ltngtP.
Qed.

Lemma eval_le_split A R a (h : natmap A) t1 t2 (z0 : R) :
        t1 <= t2 ->
        eval a (le t2) h z0 =
        eval a [pts k v | t1 < k <= t2] h (eval a (le t1) h z0).
Proof.
move=>T; case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite !eval_undef.
rewrite eval_umfilt (umfilt_predD h (pts_sub T)) evalUn; last first.
- move=>x y /dom_umfilt [vx][X _] /dom_umfilt [wy][/= /andP][].
  by rewrite /= -ltnNge; move/(leq_ltn_trans X).
- by rewrite -(umfilt_predD h (pts_sub T)) valid_umfilt.
by rewrite -!eval_umfilt; apply: eq_in_eval=>kv _; apply: (ptsD T).
Qed.

Lemma eval_lt_split A R a (h : natmap A) t1 t2 (z0 : R) :
        t1 < t2 ->
        eval a (lt t2) h z0 =
        eval a [pts k v | t1 < k < t2] h (eval a (le t1) h z0).
Proof.
move=>T; case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite !eval_undef.
rewrite eval_umfilt (umfilt_predD h (pts_sub_lt T)) evalUn; last first.
- move=>x y /dom_umfilt [vx][X _] /dom_umfilt [wy][/= /andP][].
  by rewrite /= -ltnNge; move/(leq_ltn_trans X).
- by rewrite -(umfilt_predD h (pts_sub_lt T)) valid_umfilt.
by rewrite -!eval_umfilt; apply: eq_in_eval=>kv _; apply: (ptsD_lt T).
Qed.

Lemma eval_le_lt_split A R a (h : natmap A) t (z0 : R) :
        eval a (le t) h z0 =
        eval a [pts k v | k == t] h (eval a (lt t) h z0).
Proof.
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite !eval_undef.
have D : subpred (T:=nat*A) (lt t) (le t) by case=>k v /ltnW.
rewrite eval_umfilt (umfilt_predD h D) evalUn; last first.
- move=>x y /dom_umfilt [vx][X _] /dom_umfilt [wy][/= /andP][].
  by rewrite /= -ltnNge; move/(leq_ltn_trans X).
- by rewrite -(umfilt_predD h D) valid_umfilt.
rewrite -!eval_umfilt; apply: eq_in_eval; case=>k v _ /=.
by case: ltngtP.
Qed.

Lemma eval_eq A R a (h : natmap A) t v (z0 : R) :
        (t, v) \In h -> eval a [pts k _ | k == t] h z0 = a z0 t v.
Proof.
move=>H; rewrite eval_umfilt; have N : t != 0 by move/In_dom/dom_cond: H.
suff -> : um_filter [pts k _ | k == t] h = t \-> v by rewrite evalPt /= N.
apply/umem_eq=>[||[k w]]; first by rewrite valid_umfilt; case: H.
- by rewrite validPt.
rewrite In_umfilt. split; last by move/InPt =>[[->->]].
by move=>[/eqP -> H1]; rewrite (In_fun H H1); apply: In_condPt.
Qed.

Lemma eval_le_last A R a (h : natmap A) t (z0 : R) :
        last_key h <= t -> eval a (le t) h z0 = eval a xpredT h z0.
Proof.
by move=>H; apply: eq_in_eval; case=>k v /In_dom/lastkey_max/leq_trans; apply.
Qed.

Lemma eval_fresh_le A R a (h : natmap A) t v (z0 : R) :
        eval a (le t) (fresh h \-> v \+ h) z0 =
        if t <= last_key h then eval a (le t) h z0 else
          if valid h then a (eval a predT h z0) (fresh h) v else z0.
Proof.
case V: (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undef !eval_undef; case: ifP.
case: ifP=>H.
- by rewrite eval_umfilt umfiltPtUn valid_fresh V ltnNge H -eval_umfilt.
rewrite joinC evalUnPt; last first.
- by apply/allP=>x; apply: lastkey_max.
- by rewrite joinC valid_fresh.
rewrite ltnNge H; congr a; apply: eq_in_eval.
case=>k w /In_dom/lastkey_max /=.
by case: ltngtP H=>// /ltnW H _ /leq_trans; apply.
Qed.

Lemma eval_fresh_lt A R a (h : natmap A) t v (z0 : R) :
        eval a (lt t) (fresh h \-> v \+ h) z0 =
        if t <= fresh h then eval a (lt t) h z0 else
          if valid h then a (eval a predT h z0) (fresh h) v else z0.
Proof.
case V: (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undef !eval_undef; case: ifP.
case: ifPn=>H.
- by rewrite eval_umfilt umfiltPtUn valid_fresh V ltnNge H -eval_umfilt.
rewrite joinC evalUnPt; last first.
- by apply/allP=>x; apply: lastkey_max.
- by rewrite joinC valid_fresh.
rewrite ltnNge H; congr a; apply: eq_in_eval.
case=>k w /In_dom/lastkey_max /=; rewrite /fresh -ltnNge in H.
by case: ltngtP H=>// /ltnW H _ /leq_ltn_trans; apply.
Qed.

Lemma eval_le_fresh A R a (h : natmap A) t v (z0 : R) :
        t <= last_key h ->
        eval a (le t) (fresh h \-> v \+ h) z0 = eval a (le t) h z0.
Proof. by move=>H; rewrite eval_fresh_le H. Qed.

Lemma eval_lt_fresh A R a (h : natmap A) t v (z0 : R) :
        t <= fresh h ->
        eval a (lt t) (fresh h \-> v \+ h) z0 = eval a (lt t) h z0.
Proof. by move=>H; rewrite eval_fresh_lt H. Qed.

Lemma eval_le_ind A R a (P : R -> Prop) (h : natmap A) t1 t2 (z0 : R) :
         t1 <= t2 ->
         P (eval a (le t1) h z0) ->
         (forall k v z0, (k, v) \In h -> t1 < k <= t2 -> P z0 -> P (a z0 k v)) ->
         P (eval a (le t2) h z0).
Proof.
by move=>T P0 H; rewrite (eval_le_split a h z0 T); apply: eval_ind.
Qed.

Lemma eval_lt_ind A R a (P : R -> Prop) (h : natmap A) t1 t2 (z0 : R) :
         t1 < t2 ->
         P (eval a (le t1) h z0) ->
         (forall k v z0, (k, v) \In h -> t1 < k < t2 -> P z0 -> P (a z0 k v)) ->
         P (eval a (lt t2) h z0).
Proof.
by move=>T P0 H; rewrite (eval_lt_split a h z0 T); apply: eval_ind.
Qed.

(* common case: functional version of the above le_lemma *)
Lemma eval_leF A R X a (f : R -> X) (h : natmap A) t1 t2 (z0 : R) :
         t1 <= t2 ->
         (forall k v z0, (k, v) \In h -> t1 < k <= t2 -> f (a z0 k v) = f z0) ->
         f (eval a (le t1) h z0) = f (eval a (le t2) h z0).
Proof.
move=>T H.
apply: (eval_le_ind (P := fun x => f (eval a (le t1) h z0) = f x)) T _ _=>//.
by move=>k v z1 H1 /H ->.
Qed.

(* common case: functional version of the above lt_lemma *)
Lemma eval_ltF A R X a (f : R -> X) (h : natmap A) t1 t2 (z0 : R) :
         t1 < t2 ->
         (forall k v z0, (k, v) \In h -> t1 < k < t2 -> f (a z0 k v) = f z0) ->
         f (eval a (le t1) h z0) = f (eval a (lt t2) h z0).
Proof.
move=>T H.
apply: (eval_lt_ind (P := fun x => f (eval a (le t1) h z0) = f x)) T _ _=>//.
by move=>k v z1 H1 /H ->.
Qed.

Lemma umcnt_le_split A p (h : natmap A) t1 t2 :
        t1 <= t2 ->
        um_count (predI p (le t2)) h =
        um_count (predI p (le t1)) h +
        um_count (predI p [pts k v | t1 < k <= t2]) h.
Proof.
move=>T; rewrite -!umcnt_umfilt !(umcnt_umfiltC p).
by rewrite (umcnt_predD _ (pts_sub T)) (eq_in_umcnt2 _ (ptsD T)).
Qed.

Lemma umcnt_le0 A p (h : natmap A) t :
        valid h -> {in dom h, forall k, t < k} ->
        um_count (predI p (le t)) h = 0.
Proof. by rewrite -umcnt_umfilt=>V /(umfilt_le0 V) ->; rewrite umcnt0. Qed.

Lemma umcnt_leUn A p (h1 h2 : natmap A) t :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        {in dom h2, forall k, k > last_key h1} ->
        um_count (predI p (le t)) (h1 \+ h2) =
        um_count (predI p (le t)) h1.
Proof. by move=>V K D; rewrite -!umcnt_umfilt umfilt_leUn. Qed.

Lemma umcnt_le_gapless A p (h1 h2 : natmap A) t :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        um_count (predI p (le t)) h2 = um_count (predI p (le t)) h1.
Proof. by move=>G V K D; rewrite -!umcnt_umfilt (umfilt_le_gapless G). Qed.

Lemma umcnt_le_last A p (h : natmap A) t :
        last_key h <= t -> um_count (predI p (le t)) h = um_count p h.
Proof. by move=>K; rewrite -!umcnt_umfilt umfilt_le_last. Qed.

Lemma umcnt_fresh_le A p (h : natmap A) t v :
        um_count (predI p (le t)) (fresh h \-> v \+ h) =
        if t <= last_key h then um_count (predI p (le t)) h else
        if p (fresh h, v) && valid h then 1 + um_count p h else um_count p h.
Proof.
case V: (valid h); last first.
- move/invalidE: (negbT V)=>->; rewrite join_undef !umcnt_undef.
  by rewrite lastkey_undef andbF; case: ifP.
case: ifP=>H.
- by rewrite -!umcnt_umfilt umfiltPtUn valid_fresh V ltnNge H.
rewrite umcntPtUn ?valid_fresh //= ltnNge H /=.
by rewrite umcnt_le_last; [case: ifP | case: ltngtP H].
Qed.

Lemma umcnt_le_fresh A p (h : natmap A) t v :
        t <= last_key h ->
        um_count (predI p (le t)) (fresh h \-> v \+ h) =
        um_count (predI p (le t)) h.
Proof. by move=>H; rewrite umcnt_fresh_le H. Qed.

Definition fresh_le := (umcnt_fresh_le, eval_fresh_le).
Definition le_last := (umcnt_le_last, eval_le_last).
Definition le_fresh := (umcnt_le_fresh, eval_le_fresh).
Definition lt_fresh := (eval_lt_fresh).

Lemma umcnt_mono A p (h : natmap A) t1 t2 :
        t1 <= t2 ->
        um_count (predI p (le t1)) h <= um_count (predI p (le t2)) h.
Proof. by move=>T; rewrite (umcnt_le_split _ _ T); apply: leq_addr. Qed.

Lemma umcnt_leE A p (h : natmap A) t1 t2 :
        um_count (predI p (le t1)) h = um_count (predI p (le t2)) h ->
        um_count (predI p [pts k v | t1 < k <= t2]) h = 0.
Proof.
case T: (t1 <= t2); last first.
- rewrite -{4}(umcnt_pred0 h) =>_; apply: eq_in_umcnt2=>[[k v]] /=.
  by apply: contraFF T=>/and3P [_ /ltnW]; apply: leq_trans.
move/eqP; rewrite (umcnt_le_split _ _ T).
by rewrite -{1}[um_count (predI p (le t1)) h]addn0 eqn_add2l=>/eqP.
Qed.

Lemma umcnt_umfilt_eq A p (h : natmap A) t1 t2 :
        um_count (predI p (le t1)) h = um_count (predI p (le t2)) h ->
        um_filter (predI p (le t1)) h = um_filter (predI p (le t2)) h.
Proof.
suff {t1 t2} L t1 t2 : t1 <= t2 ->
  um_count (predI p (le t1)) h = um_count (predI p (le t2)) h ->
  um_filter (predI p (le t1)) h = um_filter (predI p (le t2)) h.
- by move=>E; case: (leqP t1 t2)=>[|/ltnW] N; [|apply/esym]; apply: L N _.
case V : (valid h); last first.
- by move/negbT/invalidE: V=>->; rewrite !umfilt_undef.
move=>N /umcnt_leE /(umcnt_umfilt0 V).
rewrite !umfilt_predI !(umfiltC p) (umfilt_le_split _ N)=>->.
by rewrite unitR.
Qed.

(* count and eval leE lemmas put together *)
Lemma evcnt_le_ind A R a (P : R -> Prop) p (h : natmap A) t1 t2 (z0 : R) :
        t1 <= t2 ->
        P (eval a (le t1) h z0) ->
        (forall k v z0, (k, v) \In h -> t1 < k <= t2 ->
                        ~~ p (k, v) -> P z0 -> P (a z0 k v)) ->
        um_count (predI p (le t1)) h = um_count (predI p (le t2)) h ->
        P (eval a (le t2) h z0).
Proof.
move=>T P0 H /umcnt_leE/umcnt_mem0=>K; apply: eval_le_ind (T) (P0) _.
move=>k v z1 H' K'; apply: (H k v z1 H' K').
by move: (K k v H'); rewrite negb_and; case/orP=>//; rewrite K'.
Qed.

(* common case is when P is an equality of functions *)
Lemma evcnt_leF A R X a (f : R -> X) p (h : natmap A) t1 t2 (z0 : R) :
        t1 <= t2 ->
        (forall k v z0, (k, v) \In h -> t1 < k <= t2 ->
                        ~~ p (k, v) -> f (a z0 k v) = f z0) ->
        um_count (predI p (le t1)) h = um_count (predI p (le t2)) h ->
        f (eval a (le t1) h z0) = f (eval a (le t2) h z0).
Proof.
move=>T H.
apply: (evcnt_le_ind (P := fun x => f (eval a (le t1) h z0) = f x)) T _ _=>//.
by move=>k v z1 H' K' /H ->.
Qed.

(* The following is a lemma that generalizes evcnt_leF *)
(* from counting to functions that are monotone, in a suitable sense *)
(* that will be defined below *)

(* The lemma says that if evaluating a growing function preserves *)
(* the result, then all the evaluating steps preserve the result *)

(*********************************)
(* Some notational abbreviations *)
(*********************************)

(* exec is evaluating a history up to a timestamp *)
(* run is evaluating a history up to the end *)

(* In exec and run, the timestamp shouldn't influence *)
(* the val of the operation. So we need a coercion to *)
(* account for the timestamp, which is then ignored *)
Notation exec a t h z0 := (evalv a (le t) h z0).
Notation run a h z0 := (evalv a xpredT h z0).

Section Exec.
Variables (V R : Type) (aop : V -> R -> R).

Lemma exec0 a (h : natmap V) (z0 : R) : exec a 0 h z0 = z0.
Proof.
have /(eq_in_eval _) -> : forall kv, kv \In h -> le 0 kv = pred0 kv.
- by case=>k v /In_cond; case: k.
by rewrite eval_pred0.
Qed.

End Exec.

Section Growing.
Variables (V R : Type) (X : ordType) (a : R -> V -> R) (f : R -> X).
Implicit Types p : pred (nat*V).

Definition growing (h : natmap V) :=
  forall k v z0, (k, v) \In h -> oleq (f z0) (f (a z0 v)).

Lemma growL h1 h2 : valid (h1 \+ h2) -> growing (h1 \+ h2) -> growing h1.
Proof. by move=>W G k v z0 H; apply: (G k); apply/InL. Qed.

Lemma growR h1 h2 : valid (h1 \+ h2) -> growing (h1 \+ h2) -> growing h2.
Proof. by rewrite joinC; apply: growL. Qed.

Lemma helper0 p h z0 : growing h -> oleq (f z0) (f (evalv a p h z0)).
Proof.
elim/um_indf: h z0=>[||k v h IH W /(order_path_min (@trans _)) T] z0 G;
rewrite ?eval_undef ?eval0 // evalPtUn //.
have K: (k, v) \In pts k v \+ h by apply/InPtUnE=>//; left.
have Gh: growing h.
- by move=>k1 v1 z1 X1; apply: (G k1); apply/InPtUnE=>//; right.
case: ifP=>// P; last by apply: IH.
by apply: otrans (IH _ Gh); apply: (G k).
Qed.

Lemma helper1 p h z0 k v :
        growing (k \-> v \+ h) ->
        valid (k \-> v \+ h) ->
        all (ord k) (dom h) ->
        p (k, v) ->
        f (evalv a p (k \-> v \+ h) z0) = f z0 ->
        f (a z0 v) = f z0.
Proof.
move=>G W D P; move: (growR W G)=>Gh.
have K: (k, v) \In k \-> v \+ h by apply/InPtUnE=>//; left.
rewrite evalPtUn // P => E; apply/eqP; case: ordP=>//.
- by move/(G k v z0): K; rewrite /oleq eq_sym; case: ordP.
by move: (helper0 p (a z0 v) Gh); rewrite -E /oleq eq_sym; case: ordP.
Qed.

Lemma helper2 p h1 h2 z0 k v :
        growing (h1 \+ (k \-> v \+ h2)) ->
        valid (h1 \+ (k \-> v \+ h2)) ->
        {in dom h1, forall x, x < k} ->
        all (ord k) (dom h2) ->
        p (k, v) ->
        f (evalv a p (h1 \+ (k \-> v \+ h2)) z0) = f z0 ->
        f (a (evalv a p h1 z0) v) = f (evalv a p h1 z0).
Proof.
move=>G W D1 D2 P E1; rewrite evalUn ?(validX W) // in E1; last first.
- move=>x y /D1 X1; rewrite domPtUn inE ?(validX W).
  by case/orP=>[/eqP <-|/(allP D2)] //; apply: ltn_trans.
suff E2 : f (evalv a p h1 z0) = f z0.
- by apply: helper1 (growR W G) (validR W) D2 P _; rewrite E1 E2.
apply/eqP; case: ordP=>//.
- by move: (helper0 p z0 (growL W G)); rewrite /oleq eq_sym; case: ordP.
move: (helper0 p (evalv a p h1 z0) (growR W G)).
by rewrite -E1 /oleq eq_sym; case: ordP.
Qed.

(* "introducing" growth *)
Lemma growI h t1 t2 z0 :
        growing h -> t1 <= t2 ->
        oleq (f (exec a t1 h z0)) (f (exec a t2 h z0)).
Proof.
move=>G N; case W: (valid h); last first.
- by move/negbT/invalidE: W=>->; rewrite !eval_undef.
rewrite eval_umfilt [in X in oleq _ X]eval_umfilt (umfilt_le_split h N).
rewrite evalUn; first by apply: helper0=>x y z /In_umfilt [_ /G].
- by rewrite -(umfilt_le_split h N) valid_umfilt.
by move=>??/dom_umfilt[?][/leq_ltn_trans Y _]/dom_umfilt[?][/andP[/Y]].
Qed.

(* "eliminating" growth *)
Lemma growE h t1 t2 z0 k v :
        growing h -> (k, v) \In h -> t1 < k <= t2 ->
        f (exec a t2 h z0) = f (exec a t1 h z0) ->
        f (a (exec a k.-1 h z0) v) = f (exec a k.-1 h z0).
Proof.
move=>G H /andP [N1 N2] E; have W : valid h by case: H.
pose h0 : natmap V := um_filter (le t1) h.
pose h1 : natmap V := um_filter [pts x _ | t1 < x <= k.-1] h.
pose h2 : natmap V := um_filter [pts x _ | k < x <= t2] h.
have subX : forall k m n, k < n -> (m < n) = (m <= n.-1) by move=>?? [].
have K1 : k.-1 <= k by rewrite ltnW // (subX t1).
have K2 : t1 <= k.-1 by rewrite -(subX t1).
have K3 : k.-1 <= k <= t2 by rewrite K1 N2.
have K4 : t1 <= k.-1 <= t2 by rewrite K2 (leq_trans K1 N2).
have Eh: um_filter (le t2) h = h0 \+ (h1 \+ (k \-> v \+ h2)).
- rewrite (umfilt_le_split h N2) (umfilt_le_split h K1).
  by rewrite (umfilt_le_split h K2) (umfilt_pt_split H) -!joinA.
have W1 : valid (h0 \+ (h1 \+ (k \-> v \+ h2))) by rewrite -Eh valid_umfilt.
rewrite eval_umfilt (umfilt_le_split h K2) evalUn ?(validX W1) //; last first.
- by move=>??/dom_umfilt[?][/leq_ltn_trans Y] _ /dom_umfilt[?][] /andP [/Y].
rewrite -(eval_umfilt (le t1)); apply: helper2 (validR W1) _ _ _ _ =>//.
- by apply: growR W1 _; rewrite -Eh=>k1 v1 z1 /In_umfilt [] _ /G.
- by move=>x /dom_umfilt; rewrite (subX t1 x) //; case=>v0 [] /andP [].
- by apply/allP=>x /dom_umfilt; case=>v0 [] /andP [].
rewrite eval_umfilt Eh evalUn ?(validX W1) -?eval_umfilt // in E.
move=>x y /dom_umfilt; case=>v1 [/leq_ltn_trans Y _].
rewrite -(umfilt_pt_split H) -(umfilt_lt_split h K3).
by rewrite -(umfilt_lt_split h K4) =>/dom_umfilt; case=>v0 [/andP][/Y].
Qed.

End Growing.

(* The common case of growI and growE is when X = nat. *)

Section GrowingNat.
Variables (V R : Type) (X : ordType) (a : R -> V -> R) (f : R -> nat).
Implicit Types p : pred (nat*V).

Lemma growIn h t1 t2 z0 :
        growing a f h -> t1 <= t2 ->
        f (exec a t1 h z0) <= f (exec a t2 h z0).
Proof.
by move=>G N; move: (growI z0 G N); rewrite leq_eqVlt /oleq/ord orbC.
Qed.

Lemma growEn h t1 t2 z0 k v :
        growing a f h -> (k, v) \In h -> t1 < k <= t2 ->
        f (exec a t2 h z0) = f (exec a t1 h z0) ->
        f (a (exec a k.-1 h z0) v) = f (exec a k.-1 h z0).
Proof. by apply: growE. Qed.

End GrowingNat.


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
  case: dom_find N=>[->//|]. move=>v. simpl.
  by [].
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


(************************************)
(* Specializing to ordering on nats *)
(* (the distinction is that we need *)
(* a special number, 0, to be added *)
(* to the list)                     *)
(************************************)

(* rename index to prevent accidental simplification *)
Definition nat_index := nosimpl (@index nat_eqType).

Definition seq_le (ks : seq nat) (t1 t2 : nat) :=
  index t1 (0::ks) <= index t2 (0::ks).

Definition seq_lt (ks : seq nat) (t1 t2 : nat) :=
  index t1 (0::ks) < index t2 (0::ks).

Notation "t1 '<=[' ks ] t2" := (seq_le ks t1 t2)
  (at level 10, format "t1  '<=[' ks ]  t2").

Notation "t1 '<[' ks ] t2" := (seq_lt ks t1 t2)
  (at level 10, format "t1  '<[' ks ]  t2").

Lemma sle_refl ks t : t <=[ks] t.
Proof. by rewrite /seq_le. Qed.

Hint Resolve sle_refl : core.

Definition olast_key {A} ks (h : natmap A) :=
  last 0 (filter (fun x => x \in dom h) ks).
Prenex Implicits olast_key.

Section OLastKey.
Variable A : Type.
Implicit Type h : natmap A.

Lemma olastkey_undef ks : olast_key ks (undef : natmap A) = 0.
Proof. by elim: ks=>[|k ks] //=; rewrite /olast_key dom_undef. Qed.

Lemma olastkey0 ks : olast_key ks (Unit : natmap A) = 0.
Proof. by elim: ks=>[|k ks] //=; rewrite /olast_key dom0. Qed.

Lemma mem_olastkey ks h : olast_key ks h \in 0 :: ks.
Proof.
move: (mem_last 0 [seq x <- ks | x \in dom h]).
by rewrite !inE mem_filter; case: eqP=>//= _ /andP [].
Qed.

Hint Resolve mem_olastkey : core.

(* some interdependence between olastkey components *)

Lemma olastkey0P ks h :
        reflect (forall k, k \in dom h -> k \in ks -> false)
                (olast_key ks h == 0).
Proof.
rewrite /olast_key; case: eqP=>H; constructor; last first.
- by move=>K; case/eqP/last_filter_change/andP: H=>H /(K _ H).
move=>k H1 H2; move: (@last_in _ k 0 [seq x <- ks | x \in dom h]).
by rewrite !mem_filter H1 H=>/(_ H2) /andP [] /dom_cond.
Qed.

Lemma olastkey0_dom ks h :
        (olast_key ks h == 0) = (olast_key ks h \notin dom h).
Proof.
apply/idP/idP=>[/eqP ->|H]; first by case E: (0 \in _)=>//; move/dom_cond: E.
by apply: contraR H=>/last_filter_change /andP [].
Qed.

Lemma olastkeyN_dom ks h :
        (olast_key ks h != 0) = (olast_key ks h \in dom h).
Proof. by rewrite olastkey0_dom negbK. Qed.

Lemma olastkey0_mem ks h :
        0 \notin ks -> (olast_key ks h == 0) = (olast_key ks h \notin ks).
Proof.
move=>N; apply/idP/idP=>[/eqP ->|H] //.
by apply: contraR H=>/last_filter_change /andP [].
Qed.

Lemma olastkeyN_mem ks h :
        0 \notin ks -> (olast_key ks h != 0) = (olast_key ks h \in ks).
Proof. by move/olastkey0_mem=>->; rewrite negbK. Qed.

Lemma olastkey0_index ks h  :
        (olast_key ks h == 0) = (index (olast_key ks h) (0 :: ks) == 0).
Proof. by rewrite /= (eq_sym 0); case: eqP. Qed.

Lemma olastkey_in k ks h :
        k \in dom h -> k \in ks ->
        (olast_key ks h \in dom h) && (olast_key ks h \in ks).
Proof.
move=>D K; move: (@last_in _ k 0 [seq x <- ks | x \in dom h]).
by rewrite !mem_filter D K; apply.
Qed.

Lemma olastkey_indom k ks h :
         k \in dom h -> k \in ks ->
         olast_key ks h \in dom h.
Proof. by move=>H /(olastkey_in H) /andP []. Qed.

Lemma olastkey_inmem k ks h :
         k \in dom h -> k \in ks ->
         olast_key ks h \in ks.
Proof. by move=>H /(olastkey_in H) /andP []. Qed.

Lemma olastkey_max ks h x :
        uniq (0 :: ks) -> x \in dom h -> x \in ks -> x <=[ks] (olast_key ks h).
Proof.  by apply: last_filter_last. Qed.

Lemma max_olastkey ks h x :
        uniq (0 :: ks) ->
        x \in dom h -> x \in ks ->
        (forall y, y \in dom h -> y \in ks -> y <=[ks] x) ->
        olast_key ks h = x.
Proof.
move=>/= /andP [N U] Dx Kx H; apply: max_index_last.
- by rewrite filter_uniq.
- by rewrite mem_filter Dx Kx.
move=>z; rewrite mem_filter=>/andP [Dz Kz].
move: {H}(H z Dz Kz); rewrite /seq_le /nat_index /= !(eq_sym 0).
move: (dom_cond Dx) (dom_cond Dz)=>/= /negbTE -> /negbTE ->.
by apply: index_filter_mono.
Qed.

Lemma olastkeyPt ks (x : nat) (v : A) :
        uniq ks -> x != 0 -> x \in ks -> olast_key ks (x \-> v) = x.
Proof.
rewrite /olast_key domPtK /= =>U -> Kx.
have : [seq x0 <- ks | x0 \in [:: x]] = [seq x0 <- ks | (pred1 x) x0].
- by apply: eq_in_filter=>/= y; rewrite inE.
by move=>->; rewrite (filter_pred1_uniq U Kx).
Qed.

Lemma olastkey_mono B ks (h1 : natmap A) (h2 : natmap B) :
        {subset dom h1 <= dom h2} -> uniq (0 :: ks) ->
        (olast_key ks h1) <=[ks] (olast_key ks h2).
Proof. by apply: index_last_sub. Qed.

Lemma olastkeyfUn ks h1 h2 :
        valid (h1 \+ h2) -> uniq (0 :: ks) ->
        (olast_key ks h1) <=[ks] (olast_key ks (h1 \+ h2)).
Proof. by move=>X U; apply: olastkey_mono=>// x; rewrite domUn inE X => ->. Qed.

Lemma olastkeyUnf ks h1 h2 :
        valid (h1 \+ h2) -> uniq (0 :: ks) ->
        (olast_key ks h2) <=[ks] (olast_key ks (h1 \+ h2)).
Proof. by rewrite joinC; apply: olastkeyfUn. Qed.

(* a convenient rephrasing of above lemmas *)

Lemma olastkeyUn0 ks h1 h2 :
        valid (h1 \+ h2) -> uniq (0 :: ks) ->
        olast_key ks h1 = olast_key ks h2 ->
        ([seq x <- ks | x \in dom h1] = [::]) *
        ([seq x <- ks | x \in dom h2] = [::]).
Proof.
move=>V U E.
case E1: ([seq x <- ks | x \in dom h1] == [::]).
- rewrite /olast_key (eqP E1) /= in E *.
  by move/esym/eqP/olastkey0P/filter_nilp/eqP: E=>->.
case E2 : ([seq x <- ks | x \in dom h2] == [::]).
- rewrite /olast_key (eqP E2) /= in E *.
  by move/eqP/olastkey0P/filter_nilp/eqP: E=>->.
case/filter_nilp: E1=>x Dx /(olastkey_indom Dx).
rewrite E; case: validUn (V)=>// _ _ X _ /X.
by rewrite -olastkey0_dom=>/olastkey0P/filter_nilp; rewrite E2.
Qed.

Definition omaxn ks m n := if m <[ks] n then n else m.

Lemma olastkeyUn ks h1 h2 :
        uniq (0::ks) ->
        olast_key ks (h1 \+ h2) =
        if valid (h1 \+ h2) then
           omaxn ks (olast_key ks h1) (olast_key ks h2)
        else 0.
Proof.
move=>U; have N : 0 \notin ks by case/andP: U.
have H (k1 k2 : natmap A) : valid (k1 \+ k2) ->
  (olast_key ks k1) <[ks] (olast_key ks k2) ->
  olast_key ks (k1 \+ k2) = olast_key ks k2.
- move=>V H; apply: max_olastkey=>//.
  - rewrite domUn inE V -(olastkeyN_dom ks k2).
    by rewrite olastkey0_index -lt0n (gt0 H) orbT.
  - by rewrite -(olastkeyN_mem k2) // olastkey0_index -lt0n (gt0 H).
  move=>y; rewrite domUn inE V; case/orP=>D /(olastkey_max U D) // T.
  by apply: leq_trans T (ltnW H).
case V : (valid _); last first.
- by move/invalidE: (negbT V)=>->; rewrite olastkey_undef.
rewrite /omaxn /seq_lt; case: ltngtP.
- by apply: H.
- by rewrite joinC in V *; apply: H V.
move/(index_inj (mem_olastkey _ _)).
case/(olastkeyUn0 V U)=>/eqP E1 /eqP E2.
rewrite /olast_key (eqP E1).
rewrite (_ : [seq x <- ks | _] = [::]) //.
apply/eqP/filter_nilp=>x; rewrite domUn inE V.
by case/orP; apply: filter_nilp.
Qed.

(* monotonicity just gives us <= *)
(* when we remove the olast key, we get a strict < *)
Lemma olastkeyF ks h :
        uniq (0 :: ks) ->
        olast_key ks h \in dom h ->
        (olast_key ks (free h (olast_key ks h))) <[ks] (olast_key ks h).
Proof.
move=>U D.
have N : olast_key ks h \notin dom (free h (olast_key ks h)).
- by rewrite domF inE eq_refl.
have : index (olast_key ks (free h (olast_key ks h))) (0 :: ks) <=
       index (olast_key ks h) (0 :: ks).
- by apply: olastkey_mono=>// x; rewrite domF inE; case: ifP.
rewrite leq_eqVlt; case/orP=>// /eqP /(index_inj (mem_olastkey _ _)) /eqP E.
rewrite -{1}(eqP E) -olastkey0_dom in N.
by rewrite (eqP N) eq_sym olastkey0_dom D in E.
Qed.

Lemma olastkeyPtUnE ks u2 u1 h t :
        olast_key ks (t \-> u1 \+ h) = olast_key ks (t \-> u2 \+ h).
Proof.
have V2 : valid (t \-> u2 \+ h) = valid (t \-> u1 \+ h) by rewrite !validPtUn.
case V1: (valid (t \-> u1 \+ h)); rewrite V1 in V2; last first.
- by move/invalidE: (negbT V1) (negbT V2) => -> /invalidE ->.
by congr last; apply/eq_in_filter=>x K; rewrite !domPtUn !inE V1 V2.
Qed.

Lemma olastkeyUnPtE ks u2 u1 h t :
        olast_key ks (h \+ t \-> u1) = olast_key ks (h \+ t \-> u2).
Proof. by rewrite !(joinC h); apply: olastkeyPtUnE. Qed.

Lemma olastkeyU ks u h t :
        t \in dom h -> olast_key ks (upd t u h) = olast_key ks h.
Proof. by case/um_eta=>v [_ E]; rewrite E updPtUn (olastkeyPtUnE ks v). Qed.

(* pcm induced ordering *)

Lemma umpleq_olastkey ks h1 h2 :
        uniq (0 :: ks) ->
        valid h2 -> [pcm h1 <= h2] ->
        (olast_key ks h1) <=[ks] (olast_key ks h2).
Proof.
move=>U V H; case: H V=>z -> V.
by apply: olastkey_mono=>// k D; rewrite domUn inE V D.
Qed.

End OLastKey.

(* lemmas with omap *)

Lemma olastkey_omap (V1 V2 : ordType) (f : nat * V1 -> option V2) (h : natmap V1) ks :
        uniq (0 :: ks) ->
        (olast_key ks (omap f h)) <=[ks] (olast_key ks h).
Proof. by move=>U; apply: olastkey_mono=>//; apply: dom_omap_sub. Qed.


(*************************)
(* Surgery on histories  *)
(* using oleq filtering  *)
(*************************)

Notation ole ks t := [pts k _ | k <=[ks] t].
Notation olt ks t := [pts k _ | k <[ks] t].

Lemma pts_osub V ks t1 t2 :
        t1 <=[ks] t2 -> subpred (T:=nat*V) (ole ks t1) (ole ks t2).
Proof. by move=>T [k v] /leq_trans; apply. Qed.

Lemma optsD V ks t1 t2 :
        t1 <=[ks] t2 ->
        predD (ole ks t2) (ole ks t1) =1
        [pts k (v : V) | t1 <[ks] k && k <=[ks] t2].
Proof. by move=>T [k v] /=; rewrite -ltnNge. Qed.

Lemma olastkey_umfilt_leq A ks (h : natmap A) t :
        uniq (0 :: ks) ->
        (olast_key ks (um_filter (ole ks t) h)) <=[ks] t.
Proof.
move=>U; case: (olast_key ks (um_filter (ole ks t) h) =P 0)=>[->|/eqP] //.
by rewrite {1}olastkeyN_dom=>/dom_umfilt [v][].
Qed.

Lemma olastkey_umfilt_dom A ks (h : natmap A) t :
        uniq (0::ks) ->
        (olast_key ks (um_filter (ole ks t) h)) <=[ks] (olast_key ks h).
Proof. by apply: olastkey_mono; apply: dom_umfilt_subset. Qed.

(* In the next lemma, we need a new condition *)
(* that the ordering ks is total on dom h. *)
(* In practice, we will always have this, as the ordering *)
(* will in fact be a permutation of dom h. *)

Lemma umfilt_ole_olast A ks (h : natmap A) t :
        uniq (0::ks) ->
        {subset dom h <= ks} ->
        (olast_key ks h) <=[ks] t ->
        um_filter (ole ks t) h = h.
Proof.
move=>U S; case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite umfilt_undef.
move=>N; rewrite -{2}[h]umfilt_predT; apply/eq_in_umfilt.
by case=>k v /In_dom H; apply: leq_trans N; apply: olastkey_max (S _ H).
Qed.

Lemma umfilt_olast A ks (h : natmap A) :
        uniq (0::ks) -> {subset dom h <= ks} ->
        um_filter (ole ks (olast_key ks h)) h = h.
Proof. by move=>U S; apply: umfilt_ole_olast. Qed.

Lemma umfilt_ole_fresh A ks (h : natmap A) fresh :
         uniq (0::ks) ->
         {subset dom h <= ks} ->
         fresh \notin (0::ks) ->
         um_filter (ole ks fresh) h = h.
Proof.
move=>U S F; apply: umfilt_ole_olast=>//.
move: (index_size fresh (0::ks)).
rewrite /seq_le /nat_index leq_eqVlt index_mem (negbTE F) orbF.
by move/eqP=>->; apply: index_size.
Qed.

Lemma umfilt_ole0 A ks (h : natmap A) t :
        valid h -> {in dom h, forall k, t <[ks] k} ->
        um_filter (ole ks t) h = Unit.
Proof.
move=>V D; rewrite -(umfilt_pred0 V).
apply/eq_in_umfilt; case=>k v [_][z E]; subst h.
rewrite /seq_le /nat_index leqNgt; apply: contraTF (D k _)=>//=.
by rewrite domPtUn inE V eq_refl.
Qed.

Lemma umfilt_ole_split A ks (h : natmap A) t1 t2 :
        t1 <=[ks] t2 ->
        um_filter (ole ks t2) h =
        um_filter (ole ks t1) h \+
        um_filter [pts x _ | t1 <[ks] x && x <=[ks] t2] h.
Proof.
move=>T; rewrite -umfilt_dpredU; last first.
- by case=>x y N /=; rewrite negb_and -leqNgt -/(seq_le ks _ _) N.
apply/eq_in_umfilt; case=>k v _ /=; rewrite /seq_le /seq_lt.
case: (leqP (index k (0::ks)) (index t1 (0::ks)))=>//=.
by move/leq_trans; apply.
Qed.

Lemma umfilt_olt_split A ks (h : natmap A) t1 t2 k :
        t1 <=[ks] k && k <=[ks] t2 ->
        um_filter [pts x _ | t1 <[ks] x && x <=[ks] t2] h =
        um_filter [pts x _ | t1 <[ks] x && x <=[ks] k] h \+
        um_filter [pts x _ | k <[ks] x && x <=[ks] t2] h.
Proof.
move=>/andP [T1 T2]; rewrite -umfilt_dpredU; last first.
- by case=>x y /andP [N1 N2]; rewrite /= negb_and -leqNgt -/(seq_le _ _ _) N2.
apply/eq_in_umfilt; case=>k1 v1 _ /=; rewrite /seq_le /seq_lt.
case: (leqP (index k1 (0::ks)) (index k (0::ks)))=>//=; last first.
- by move/(leq_ltn_trans T1)=>->.
by move/leq_trans=>-> //; rewrite orbF.
Qed.

Lemma umfilt_opt_split A ks (h : natmap A) k v :
        (k, v) \In h -> k \in ks ->
        um_filter [pts x _ | k <=[ks] x && x <=[ks] k] h = k \-> v.
Proof.
move=>H K; have W : valid h by case: H.
have N: 0 < index k (0::ks) by move/In_dom/dom_cond: H; case: k K. clear N.
rewrite (In_eta H) umfiltPtUn -(In_eta H) W sle_refl /=.
rewrite umfilt_mem0L ?unitR ?validF //.
move=>k1 v1 /InF [_ /=]; rewrite andbC -eqn_leq /nat_index.
case: (index k1 _ =P index k _)=>// /esym /index_inj ->;
by rewrite 1?eq_refl // inE K orbT.
Qed.

Lemma oev_umfilt_le A R ks a (h : natmap A) t (z0 : R) :
        oeval a ks (um_filter (ole ks t) h) z0 =
        oeval a [seq x <- ks | x <=[ks] t] h z0.
Proof.
rewrite oev_filter; apply: eq_in_oevF=>k v K.
by rewrite !In_umfilt.
Qed.

Lemma umfilt_oleUn A ks (h1 h2 : natmap A) t :
        valid (h1 \+ h2) -> t <=[ks] (olast_key ks h1) ->
        {in dom h2, forall k, olast_key ks h1 <[ks] k} ->
        um_filter (ole ks t) (h1 \+ h2) = um_filter (ole ks t) h1.
Proof.
move=>V K D; rewrite umfiltUn // (umfilt_ole0 (validR V)) ?unitR //.
by move=>k /D /(leq_ltn_trans K).
Qed.

(* properties of the ordering *)

Lemma ole0min x ks : 0 <=[ks] x.
Proof. by []. Qed.

Lemma olt0min x ks : 0 <[ks] x = (x != 0).
Proof. by rewrite /seq_lt /nat_index /= (eq_sym 0); case: eqP.  Qed.

Lemma ole0 x ks : x <=[ks] 0 = (x == 0).
Proof. by rewrite /seq_le /nat_index /= (eq_sym 0); case: eqP. Qed.

Lemma olt0 x ks : x <[ks] 0 = false.
Proof. by rewrite /seq_lt /nat_index /= (eq_sym 0); case: eqP. Qed.

Lemma ole_dom x1 x2 ks :
        x1 <=[ks] x2 -> x1 != 0 -> x2 \in ks -> (x1 \in ks).
Proof.
rewrite /seq_le /nat_index /= !(eq_sym 0) -!index_mem.
case: eqP; case: eqP=>//= _ _ N _.
by apply: leq_ltn_trans; rewrite -ltnS.
Qed.

Lemma oleL k t ks : k <=[k :: ks] t = (k == 0) || (t != 0).
Proof. by rewrite /seq_le /nat_index /= eq_refl !(eq_sym 0); do !case: eqP. Qed.

Lemma oleR k t ks : k <=[t :: ks] t = (k == 0) || (k == t).
Proof.
rewrite /seq_le /nat_index /= eq_refl !(eq_sym 0) -!(eq_sym t).
by do ![case: eqP=>//]; move=>->->.
Qed.

Lemma oltL k t ks : k <[k :: ks] t = (k != t) && (t != 0).
Proof. by rewrite /seq_lt ltnNge -/(seq_le _ _ _) oleR negb_or andbC eq_sym. Qed.

Lemma oltR k t ks : k <[t :: ks] t = (k == 0) && (t != 0).
Proof. by rewrite /seq_lt ltnNge -/(seq_le _ _ _) oleL negb_or negbK andbC. Qed.

Lemma ole_consL x t k ks : x != k -> x <=[k::ks] t -> x <=[ks] t.
Proof.
rewrite /seq_le /nat_index /= => Kx; do ![case: eqP=>//]=>*;
by subst x; rewrite eq_refl in Kx.
Qed.

Lemma ole_consR x t k ks : k != t -> x <=[ks] t -> x <=[k::ks] t.
Proof.
rewrite /seq_le /nat_index /= => Kx; do ![case: eqP=>//]=>*.
by subst k; rewrite eq_refl in Kx.
Qed.

Lemma index_rcons (A : eqType) (a x : A) xs :
        index a (rcons xs x) =
        if a \in xs then index a xs else
          if a == x then size xs else (size xs).+1.
Proof.
rewrite eq_sym; elim: xs=>[|y xs IH] //=.
rewrite inE eq_sym; case: eqP=>//= _.
by rewrite IH; case: ifP=>//; case: eqP.
Qed.

Lemma index_memN (A : eqType) (x : A) xs :
        x \notin xs -> index x xs = size xs.
Proof.
rewrite -index_mem -ltnNge ltnS.
by case: ltngtP (index_size x xs).
Qed.

Lemma ole_rcons x1 x2 k ks :
        x1 \in ks -> k \notin ks ->
        x1 <=[rcons ks k] x2 = x1 <=[ks] x2.
Proof.
rewrite /seq_le /nat_index /= !(eq_sym 0).
case: eqP; case: eqP=>// N2 N1; rewrite !ltnS !index_rcons.
case: ifP; case: ifP=>// /negbT/index_memN ->; rewrite index_size.
case: ifP; first by rewrite index_size.
by move/leq_trans: (index_size x1 ks)=>->.
Qed.

Lemma ole_rcons2 x1 x2 k ks :
        x1 <=[ks] x2 -> x2 != k -> x1 <=[rcons ks k] x2.
Proof.
rewrite /seq_le /nat_index /= !(eq_sym 0).
case: (x1 =P 0)=>// N1; case: (x2 =P 0)=>// N2.
rewrite !ltnS !index_rcons.
case X1: (x1 \in ks); last first.
- move/negbT/index_memN: X1=>->.
  case X2: (x2 \in ks); first by rewrite -index_mem in X2; case: ltnP X2.
  by move/negbT/index_memN: X2=>->; case: eqP; case: eqP.
case X2: (x2 \in ks)=>//.
by move/negbT/index_memN: X2=>->; case: eqP=>// _ /leq_trans ->.
Qed.

Lemma olt_rcons x t ks :
        x \in ks -> t \notin ks -> t != 0 -> x <[rcons ks t] t.
Proof.
rewrite /seq_lt /nat_index /= !(eq_sym 0).
case: (x =P 0)=>[->|_ E1 E2 N]; first by case: eqP.
by rewrite !index_rcons eq_refl E1 (negbTE E2) (negbTE N) ltnS index_mem.
Qed.

Lemma ole_take ks t :
        uniq (0::ks) ->
        [seq x <- ks | x <=[ks] t] = take (index t (0::ks)) ks.
Proof.
elim: ks=>//= k ks; rewrite inE negb_or -!(eq_sym k) -!(eq_sym t) -andbA.
move=>IH /and4P [H1 H2 H3 H4]; rewrite oleL (negbTE H1) /=.
case: (t =P 0) IH=>[->|/eqP T] /= IH.
  rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx /=.
  by rewrite ole0; case: eqP Kx H2=>// ->->.
congr cons; case: eqP=>[->|/eqP N].
- rewrite take0 -(filter_pred0 ks).
  apply: eq_in_filter=>x Kx /=; rewrite oleR.
  by case: eqP Kx H2 H3=>[->->|] //; case: eqP=>// ->  _ ->.
rewrite -IH ?H2 ?H4 //; apply: eq_in_filter=>x Kx; apply/idP/idP.
- by apply: ole_consL; case: eqP Kx H3=>//->->.
by apply: ole_consR; rewrite eq_sym.
Qed.

Lemma olt_take ks t :
        uniq (0::ks) ->
        [seq x <- ks | x <[ks] t] = take (index t (0::ks)).-1 ks.
Proof.
elim: ks=>//= k ks; rewrite inE negb_or -!(eq_sym t) -!(eq_sym k) -andbA.
move=>IH /and4P [H1 H2 H3 H4]; rewrite oltL andbC.
case: (t =P 0) IH=>[->|/eqP T] /= IH.
- rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx /=.
  by rewrite olt0.
case: (k =P t)=>[<-|N] /=.
- rewrite -(filter_pred0 ks); apply/eq_in_filter=>x Kx /=.
  by rewrite oltR H1; case: eqP Kx H2=>// ->->.
congr cons; rewrite -IH ?H2 ?H4 //; apply: eq_in_filter=>x Kx.
rewrite /seq_lt !ltnNge; congr negb; apply/idP/idP.
- by apply: ole_consL; case: eqP N=>// ->.
by apply: ole_consR; case: eqP Kx H3=>// ->->.
Qed.

Lemma ole_drop ks t :
        uniq (0::ks) ->
        [seq x <- ks | t <=[ks] x] = drop (index t (0::ks)).-1 ks.
Proof.
elim: ks=>//= k ks; rewrite inE negb_or -!(eq_sym k) -!(eq_sym t) -andbA.
move=>IH /and4P [H1 H2 H3 H4]; rewrite oleR.
case: (t =P 0) IH=>[->|/eqP T] /= IH; first by rewrite IH ?H2 ?H4 // drop0.
case: eqP=>E.
- congr cons; rewrite /seq_le -{4}(filter_predT ks).
  apply: eq_in_filter=>x Kx.
  by rewrite E -/(seq_le _ _ _) oleL orbC; case: eqP Kx H2=>// ->->.
rewrite -IH ?H2 ?H4 //; apply: eq_in_filter=>x Kx.
apply/idP/idP.
- by apply: ole_consL; case: eqP E.
by apply: ole_consR; case: eqP Kx H3=>// ->->.
Qed.

Lemma olt_drop ks t :
        uniq (0::ks) ->
        [seq x <- ks | t <[ks] x] = drop (index t (0::ks)) ks.
Proof.
elim: ks=>//= k ks; rewrite inE negb_or -!(eq_sym k) -!(eq_sym t) -andbA.
move=>IH /and4P [H1 H2 H3 H4]; rewrite oltR H1 andbT.
case: (t =P 0) IH=>[->|/eqP T] /= IH.
- congr cons; rewrite drop0 in IH; rewrite /seq_lt -{4}IH ?H2 ?H4 //.
  by apply: eq_in_filter=>x Kx; rewrite !ltnNge -/(seq_le _ _ _) ole0 olt0min.
case: (t =P k)=>[->|/eqP N] /=.
- rewrite drop0 /seq_lt -{4}(filter_predT ks).
  apply: eq_in_filter=>x Kx; rewrite -/(seq_lt _ _ _) oltL.
  case: (k =P x) Kx H1 H2 H3=>[->->|] //=.
  by case: (x =P 0)=>// -> _ ->.
rewrite -IH ?H2 ?H4 //; apply: eq_in_filter=>x Kx.
rewrite /seq_lt !ltnNge; congr negb; apply/idP/idP.
- by apply: ole_consL; case: eqP Kx H3=>// ->->.
by apply: ole_consR; rewrite eq_sym.
Qed.

Lemma olt_consL x t k ks : x != k -> x <[k::ks] t -> x <[ks] t.
Proof.
rewrite /seq_lt /nat_index /= => Kx; do ![case: eqP=>//]=>*.
by subst x; rewrite eq_refl in Kx.
Qed.

Lemma olt_consR x t k ks : k != t -> x <[ks] t -> x <[k::ks] t.
Proof.
rewrite /seq_lt /nat_index /= => Kx; do ![case: eqP=>//]=>*;
by subst k; rewrite eq_refl in Kx.
Qed.

Lemma olt_irr x ks : x <[ks] x = false.
Proof. by rewrite /seq_lt ltnn. Qed.

Lemma index_filter_le (A : eqType) (p : pred A) (ks : seq A) (t1 t2 : A) :
         t1 \in ks -> p t1 -> t2 \in ks -> p t2 ->
         (index t1 (filter p ks) <= index t2 (filter p ks)) =
         (index t1 ks <= index t2 ks).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //; rewrite !inE /=.
case: ifP=>Pk //=; rewrite !(eq_sym k);
case: eqP Pk=>[->|N1]; case: eqP=>[->|N2] //= Pk Kt1 Pt1 Kt2 Pt2.
- by rewrite !ltnS IH //.
- by rewrite leqnn.
- by rewrite Pk in Pt1.
- by rewrite Pk in Pt2.
by rewrite ltnS IH.
Qed.

Lemma index_filter_lt (A : eqType) (p : pred A) (ks : seq A) (t1 t2 : A) :
         t1 \in ks -> p t1 -> t2 \in ks -> p t2 ->
         (index t1 (filter p ks) < index t2 (filter p ks)) =
         (index t1 ks < index t2 ks).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //; rewrite !inE /=.
case: ifP=>Pk //=; rewrite !(eq_sym k);
case: eqP Pk=>[->|N1]; case: eqP=>[->|N2] //= Pk Kt1 Pt1 Kt2 Pt2.
- by rewrite !ltnS IH.
- by rewrite ltnn.
- by rewrite Pk in Pt1.
- by rewrite Pk in Pt2.
by rewrite ltnS IH.
Qed.

Lemma olt_filter (p : pred nat) (ks : seq nat) (t1 t2 : nat) :
        t1 \in filter p ks ->
        t2 \in filter p ks ->
        t1 <[filter p ks] t2 = t1 <[ks] t2.
Proof.
rewrite !mem_filter; case/andP=>Pt1 Kt1 /andP [Pt2 Kt2].
rewrite /seq_lt /nat_index /=; case: eqP=>_; case: eqP=>_ //.
by rewrite !ltnS index_filter_lt.
Qed.

Lemma ole_filter (p : pred nat) (ks : seq nat) (t1 t2 : nat) :
        t1 \in filter p ks -> t2 \in filter p ks ->
        t1 <=[filter p ks] t2 = t1 <=[ks] t2.
Proof.
rewrite !mem_filter; case/andP=>Pt1 Kt1 /andP [Pt2 Kt2].
rewrite /seq_le /nat_index /=; case: eqP=>_; case: eqP=>_ //.
by rewrite !ltnS index_filter_le.
Qed.

Lemma olt_mem x y ks : x <[ks] y -> x \in 0::ks.
Proof.
rewrite /seq_lt /nat_index /= inE (eq_sym 0); case: eqP=>//= _; case: eqP=>// _.
by rewrite ltnS -index_mem; move/leq_trans; apply; apply: index_size.
Qed.

Lemma olt_catL xs1 xs2 t1 t2 : t1 <[xs1] t2 -> t1 <[xs1++xs2] t2.
Proof.
rewrite /seq_lt /= !index_cat /=.
case: ifP; case: ifP=>// _ _; rewrite !ltnS=>N.
case: ifP=>[|/negbT]; case: ifP=>[|/negbT] //.
- by move=>_ T1; apply: ltn_addr; rewrite index_mem.
- by rewrite -index_mem; move/(ltn_trans N); rewrite index_mem=>->.
rewrite -!index_mem -!leqNgt leq_eqVlt ltnNge index_size orbF.
by move=>/eqP ->; case: ltngtP N.
Qed.

Lemma olt_catR xs1 xs2 t1 t2 :
        uniq (xs1 ++ xs2) -> t2 \in xs2 ->
        t1 <[xs2] t2 -> t1 <[xs1++xs2] t2.
Proof.
move=>U T2; rewrite /seq_lt /= !index_cat /=.
case: ifP; case: ifP=>// _ _; rewrite !ltnS=>N.
rewrite cat_uniq in U; case/and3P: U=>U1 U2 U3.
case: ifP=>[|/negbT]; case: ifP=>[|/negbT] //.
- have : t1 \in xs2.
  - by rewrite -index_mem; apply: leq_trans N _; rewrite index_size.
  by move/hasPn: U2=>U2 /U2 /= /negbTE ->.
- have : t1 \in xs2.
  - by rewrite -index_mem; apply: leq_trans N _; rewrite index_size.
  by move/hasPn: U2=>U2 /U2 /= /negbTE ->.
- by move/hasPn: U2; move/(_ _ T2)=>/= /negbTE ->.
by rewrite ltn_add2l.
Qed.

(* various lemmas for splittings of the interval *)
(* categorized wrt. the boundaries of the interval are *)
(* closed/open on left/right *)
(* the 4 versions are: *)
(* ole_le_split: [0, t2] = [0, t1] + (t1, t2] *)
(* ole_lt_split: [0, t2] = [0, t1) + [t1, t2] *)
(* olt_le_split: [0, t2) = [0, t1] + (t1, t2) *)
(* olt_lt_split: [0, t2) = [0, t1) + [t1, t2) *)

Lemma ole_le_split ks t1 t2 :
        uniq (0::ks) -> t1 <=[ks] t2 ->
        [seq x <- ks | x <=[ks] t2] =
          [seq x <- ks | x <=[ks] t1] ++
          [seq x <- ks | t1 <[ks] x & x <=[ks] t2].
Proof.
move=>U T.
have E1 : {in ks, forall x, x <=[ks] t1 =
                            x <=[ks] t2 && x <=[ks] t1}.
- move=>x Kx; case E: (x <=[ks] t1)=>//=;
  by rewrite ?andbF // /seq_le (leq_trans E T).
have E2 : {in ks, forall x, t1 <[ks] x && x <=[ks] t2 =
                            x <=[ks] t2 && t1<[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite [in RHS]ole_take // olt_drop // cat_take_drop.
Qed.

Lemma ole_lt_split ks t1 t2 :
        uniq (0::ks) -> t1 <=[ks] t2 ->
        [seq x <- ks | x <=[ks] t2] =
          [seq x <- ks | x <[ks] t1] ++
          [seq x <- ks | t1 <=[ks] x & x <=[ks] t2].
Proof.
move=>U T.
have E1 : {in ks, forall x, x <[ks] t1 =
                            x <=[ks] t2 && x <[ks] t1}.
- move=>x Kx; case E: (x <[ks] t1)=>//=;
  by rewrite ?andbF // /seq_le leq_eqVlt (leq_trans E T) orbT.
have E2 : {in ks, forall x, t1 <=[ks] x && x <=[ks] t2 =
                            x <=[ks] t2 && t1<=[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite [in RHS]olt_take // ole_drop // cat_take_drop.
Qed.

Lemma olt_le_split ks t1 t2 :
        uniq (0::ks) -> t1 <[ks] t2 ->
        [seq x <- ks | x <[ks] t2] =
          [seq x <- ks | x <=[ks] t1] ++
          [seq x <- ks | t1 <[ks] x & x <[ks] t2].
Proof.
move=>U T.
have E1 : {in ks, forall x, x <=[ks] t1 =
                            x <[ks] t2 && x <=[ks] t1}.
- move=>x Kx; case E: (x <=[ks] t1)=>//=;
  by rewrite ?andbF // /seq_lt (leq_ltn_trans E T).
have E2 : {in ks, forall x, t1 <[ks] x && x <[ks] t2 =
                            x <[ks] t2 && t1<[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite ole_take // [in RHS]olt_drop // cat_take_drop.
Qed.

Lemma olt_lt_split ks t1 t2 :
        uniq (0::ks) -> t1 <=[ks] t2 ->
        [seq x <- ks | x <[ks] t2] =
          [seq x <- ks | x <[ks] t1] ++
          [seq x <- ks | t1 <=[ks] x & x <[ks] t2].
Proof.
move=>U T.
have E1 : {in ks, forall x, x <[ks] t1 =
                            x <[ks] t2 && x <[ks] t1}.
- move=>x Kx; case E: (x <[ks] t1)=>//=;
  by rewrite ?andbF // /seq_lt (leq_trans E T).
have E2 : {in ks, forall x, t1 <=[ks] x && x <[ks] t2 =
                            x <[ks] t2 && t1<=[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite [in RHS]olt_take // ole_drop // cat_take_drop.
Qed.

(* lemmas about singletons *)
Lemma ole_leS ks k :
        uniq ks ->
        [seq x <- ks | k <=[ks] x & x <=[ks] k] =
        if k \in ks then [:: k] else [::].
Proof.
move=>U; case: ifP=>K.
- rewrite -(filter_pred1_uniq U K); apply: eq_in_filter=>x Kx.
  rewrite -eqn_leq; apply/eqP/eqP=>[|->] //.
  by move/esym/index_inj=>-> //; rewrite inE Kx orbT.
rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx.
rewrite -eqn_leq; case: eqP=>// /esym/index_inj E.
by rewrite -E ?Kx // in K; rewrite inE Kx orbT.
Qed.

Lemma ole_ltS ks k : [seq x <- ks | k <=[ks] x & x <[ks] k] = [::].
Proof.
rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx.
by rewrite /seq_le /seq_lt; case: ltngtP.
Qed.

Lemma oev_ole_last A R a ks (h : natmap A) t (z0 : R) :
        uniq (0::ks) ->
        olast_key ks h <=[ks] t ->
        oeval a [seq x <- ks | x <=[ks] t] h z0 =
        oeval a ks h z0.
Proof.
move=>U H; apply: eq_in_oevK; rewrite -filter_predI.
apply: eq_in_filter=>x Kx /=; case D: (x \in dom h)=>//=.
by apply: leq_trans (olastkey_max U D Kx) H.
Qed.

Lemma oev_fresh_ole A R a ks (h : natmap A) t fresh v (z0 : R) :
        uniq (0::ks) -> valid (fresh \-> v \+ h) ->
        t <[ks] fresh ->
        oeval a [seq x <- ks | x <=[ks] t] (fresh \-> v \+ h) z0 =
        oeval a [seq x <- ks | x <=[ks] t] h z0.
Proof.
move=>U V T; rewrite !oev_filter umfiltPtUn V /=.
by rewrite /seq_le leqNgt -/(seq_lt _ _ _) T.
Qed.

Lemma oev_ole_ind A R a (P : R -> Prop) ks (h : natmap A) t1 t2 (z0 : R) :
         uniq (0::ks) -> t1 <=[ks] t2 ->
         P (oeval a [seq x <- ks | x <=[ks] t1] h z0) ->
         (forall k v z0, (k, v) \In h -> k \in ks ->
            t1 <[ks] k -> k <=[ks] t2 -> P z0 -> P (a z0 k v)) ->
         P (oeval a [seq x <- ks | x <=[ks] t2] h z0).
Proof.
move=>U T P0 H; rewrite (ole_le_split U T) oev_cat.
apply: oev_ind=>// k v z Kh; rewrite mem_filter -andbA.
by case/and3P=>*; apply: H.
Qed.

(* common case: functional version of the above lemma *)
Lemma oev_oleF A R X a (f : R -> X) ks (h : natmap A) t1 t2 (z0 : R) :
         uniq (0::ks) -> t1 <=[ks] t2 ->
         (forall k v z0, (k, v) \In h -> k \in ks ->
            t1 <[ks] k -> k <=[ks] t2 -> f (a z0 k v) = f z0) ->
         f (oeval a [seq x <- ks | x <=[ks] t1] h z0) =
         f (oeval a [seq x <- ks | x <=[ks] t2] h z0).
Proof.
move=>U T H.
apply: (oev_ole_ind (P := fun x => f (oeval a [seq x <- ks | x <=[ks] t1] h z0) = f x)) T _ _=>//.
by move=>k v z1 D K T1 T2; rewrite H.
Qed.

(* notation for executing up to (and including/excluding) t *)

Notation oexec_le a ks t h z0 :=
  (oevalv a (filter (fun x => x <=[ks] t) ks) h z0).
Notation oexec_lt a ks t h z0 :=
  (oevalv a (filter (fun x => x <[ks] t) ks) h z0).

(* some lemmas for the new notation *)

Section OExec.
Variables (V R : Type) (aop : V -> R -> R).

Lemma oex_le0 a ks (h : natmap V) (z0 : R) : oexec_le a ks 0 h z0 = z0.
Proof.
case W : (valid h); last first.
- by move/negbT/invalidE: W=>->; rewrite oev_undef.
have /eq_in_umfilt E : forall kv, kv \In h -> kv.1 <=[ks] 0 = pred0 kv.
- by move=>kv /In_dom/dom_cond; rewrite ole0=>/= /negbTE ->.
by rewrite oev_filter E umfilt_pred0 // oev0.
Qed.

Lemma oex_leT a ks t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_le a ks t h z0 = if t == 0 then z0 else oevalv a ks h z0.
Proof.
move=>K.
case: eqP=>[->|/eqP T]; first by rewrite oex_le0.
suff : [seq x <- ks | x <=[ks] t] = ks by move=>->.
rewrite -[in RHS](filter_predT ks); apply/eq_in_filter=>x D.
rewrite /seq_le /nat_index /= !(eq_sym 0) (negbTE T); case: eqP=>// _.
by rewrite -!index_mem -ltnNge in K D; rewrite (ltn_trans D K).
Qed.

Lemma oex_leT_last a ks k (h : natmap V) (z0 : R) :
        uniq (0::rcons ks k) ->
        oexec_le a (rcons ks k) k h z0 = oevalv a (rcons ks k) h z0.
Proof.
move=>/= /andP [U1 U2].
have Nk : k \notin ks.
- by rewrite rcons_uniq in U2; case/andP: U2.
suff -> : [seq x <- rcons ks k | x <=[rcons ks k] k] = rcons ks k=>//.
rewrite -[in RHS](filter_predT (rcons ks k)); apply/eq_in_filter=>x D.
rewrite /seq_le /nat_index /= !(eq_sym 0); case: eqP=>// _.
case: eqP U1=>[->|_ U1]; first by rewrite /= mem_rcons inE eq_refl.
rewrite (index_rcons k k ks) eq_refl (negbTE Nk).
by rewrite -index_mem size_rcons in D.
Qed.

Lemma oex_le_cat a ks1 ks2 t (h : natmap V) (z0 : R) :
        uniq (0 :: ks1++ks2) ->
        oexec_le a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_le a ks1 t h z0
        else oexec_le a ks2 t h (oexec_le a ks1 t h z0).
Proof.
case: (t =P 0)=>[->|/eqP T]; first by rewrite !oex_le0; case: ifP.
rewrite /= mem_cat negb_or -andbA=>/and3P [N1 N2].
rewrite cat_uniq=>/and3P [U1 /hasPn /= U U2].
have E1 : [seq x <- ks1++ks2 | x <=[ks1++ks2] t] =
          [seq x <- ks1 | x <=[ks1++ks2] t] ++
          [seq x <- ks2 | x <=[ks1++ks2] t].
- elim: ks1 N1 {U1 U}=>[|k ks1 IH] //=.
  rewrite inE negb_or (eq_sym 0)=>/andP [K N1].
  by rewrite !oleL (negbTE K) T /= filter_cat.
have E2 : [seq x <- ks1 | x <=[ks1++ks2] t] =
          [seq x <- ks1 | x <=[ks1] t].
- apply/eq_in_filter=>x K; rewrite /seq_le /nat_index /= !(eq_sym 0) (negbTE T).
  case: eqP=>// _; rewrite !index_cat K; case: ifPn=>// T'.
  rewrite -!index_mem -ltnNge in K T'.
  by rewrite !(ltn_trans K _) // ltnS leq_addr.
have E3 : [seq x <- ks2 | x <=[ks1++ks2] t] =
  if t \in ks1 then [::] else [seq x <- ks2 | x <=[ks2] t].
- case: ifPn=>T'; last first.
  - apply/eq_in_filter=>k K; rewrite /seq_le /nat_index /= !(eq_sym 0) (negbTE T).
    case: eqP K=>[->|_ K]; first by rewrite (negbTE N2).
    by rewrite !index_cat (negbTE T') (negbTE (U _ K)) !ltnS leq_add2l.
  rewrite -(filter_pred0 ks2); apply: eq_in_filter=>k K.
  rewrite /seq_le /nat_index /= !(eq_sym 0) (negbTE T).
  case: eqP K=>[->|_ K]; first by rewrite (negbTE N2).
  apply/negbTE; rewrite !index_cat T' (negbTE (U _ K)) -ltnNge ltnS.
  by rewrite -!index_mem in K T'; rewrite (leq_trans T' _) // leq_addr.
by rewrite E1 E2 oev_cat E3; case: ifP.
Qed.

Lemma oex_le_cons a ks k t v (h : natmap V) (z0 : R) :
        uniq (0::k::ks) ->
        (k, v) \In h ->
        oexec_le a (k :: ks) t h z0 =
        if t == 0 then z0 else
          if t == k then a z0 v else oexec_le a ks t h (a z0 v).
Proof.
move=>U H; case: (t =P 0)=>[->|/eqP T]; first by rewrite oex_le0.
rewrite (_ : k::ks = [::k] ++ ks) in U *; last by rewrite cat1s.
by rewrite oex_le_cat //= inE oleL T orbT /=; move/In_find: H=>->.
Qed.

Lemma oex_rcons_in a ks k t (h : natmap V) (z0 : R) :
        uniq (0::rcons ks k) -> t \in ks ->
        oexec_le a (rcons ks k) t h z0 = oexec_le a ks t h z0.
Proof.
move=>U T; have N : t != 0.
- case: eqP T=>// ->; rewrite /= mem_rcons inE negb_or -andbA in U.
  by case/and3P: U=>_ /negbTE ->.
rewrite (_ : rcons ks k = ks ++ [:: k]) in U *; last by rewrite cats1.
by rewrite oex_le_cat //= oleL T.
Qed.

Lemma oex_le_rcons_notin a ks k t v (h : natmap V) (z0 : R) :
        uniq (0::rcons ks k) -> (k, v) \In h -> t \notin ks ->
        oexec_le a (rcons ks k) t h z0 =
        if t == 0 then z0 else a (oexec_le a ks t h z0) v.
Proof.
move=>U H K; case: (t =P 0)=>[->|/eqP T]; first by rewrite oex_le0.
rewrite (_ : rcons ks k = ks ++ [:: k]) in U *; last by rewrite cats1.
by rewrite oex_le_cat //= oleL (negbTE K) T orbT /=; move/In_find: H=>->.
Qed.

Lemma oex_le_consecutive a x1 t1 t2 x2 v (h : natmap V) (z0 : R) :
        uniq (0::x1 ++ [:: t1, t2 & x2]) ->
        (t2, v) \In h ->
        oexec_le a (x1 ++ [:: t1, t2 & x2]) t2 h z0 =
        a (oexec_le a (x1 ++ [:: t1, t2 & x2]) t1 h z0) v.
Proof.
move=>U H; have X : x1 ++ [:: t1, t2 & x2] = rcons x1 t1 ++ [:: t2 & x2].
- by rewrite -cats1 -catA.
rewrite {}X /= in U *.
move: (U); rewrite !mem_cat cat_uniq /= !inE !negb_or -!andbA => U'.
case/and8P: U'=>U1 U2 U3 U4 U5 /hasPn /= U6 U7 U8.
rewrite !oex_le_cat // (negbTE U5) mem_rcons inE eq_refl.
rewrite (oex_le_cons _ _ _ _ H)=>/=; last by rewrite !inE negb_or U2 U3 U7 U8.
rewrite (eq_sym t2) (negbTE U2) eq_refl.
by rewrite oex_leT // (eq_sym t2) (negbTE U2) oex_leT_last //= U1 U4.
Qed.

(* Now for oexec_lt, i.e., oexec with lt *)

Lemma oex_lt0 a ks (h : natmap V) (z0 : R) : oexec_lt a ks 0 h z0 = z0.
Proof.
case W : (valid h); last first.
- by move/negbT/invalidE: W=>->; rewrite oev_undef.
have /eq_in_umfilt E : forall kv, kv \In h -> kv.1 <[ks] 0 = pred0 kv.
- by move=>kv /In_dom/dom_cond; rewrite olt0.
by rewrite oev_filter E umfilt_pred0 // oev0.
Qed.

Lemma oex_ltT a ks t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_lt a ks t h z0 = if t == 0 then z0 else oevalv a ks h z0.
Proof.
move=>K.
case: eqP=>[->|/eqP T]; first by rewrite oex_lt0.
suff : [seq x <- ks | x <[ks] t] = ks by move=>->.
rewrite -[in RHS](filter_predT ks); apply/eq_in_filter=>x D.
rewrite /seq_lt /nat_index /= !(eq_sym 0) (negbTE T); case: eqP=>// _.
by rewrite -!index_mem -ltnNge ltnS in K D; rewrite ltnS (leq_trans D K).
Qed.

Lemma oex_ltT_last a ks k (h : natmap V) (z0 : R) :
        uniq (0::rcons ks k) ->
        oexec_lt a (rcons ks k) k h z0 = oevalv a ks h z0.
Proof.
move=>/= /andP [U1 U2].
have Nk : k \notin ks.
- by rewrite rcons_uniq in U2; case/andP: U2.
rewrite mem_rcons inE negb_or (eq_sym 0) in U1; case/andP: U1=>U U1.
suff -> : [seq x <- rcons ks k | x <[rcons ks k] k] = ks =>//.
rewrite /seq_lt filter_rcons ltnn -[in RHS](filter_predT ks); apply/eq_in_filter=>x D.
rewrite /nat_index /= !(eq_sym 0) (negbTE U) ltnS.
case: eqP D U1=>[->->//|_ D U1].
by rewrite (index_rcons k k ks) eq_refl (negbTE Nk) index_rcons D index_mem.
Qed.

Lemma oex_lt_cat a ks1 ks2 t (h : natmap V) (z0 : R) :
        uniq (0 :: ks1++ks2) ->
        oexec_lt a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_lt a ks1 t h z0
        else oexec_lt a ks2 t h (oexec_lt a ks1 t h z0).
Proof.
case: (t =P 0)=>[->|/eqP T]; first by rewrite !oex_lt0; case: ifP.
rewrite /= mem_cat negb_or -andbA=>/and3P [N1 N2].
rewrite cat_uniq=>/and3P [U1 /hasPn /= U U2].
have E1 : [seq x <- ks1++ks2 | x <[ks1++ks2] t] =
          [seq x <- ks1 | x <[ks1++ks2] t] ++
          [seq x <- ks2 | x <[ks1++ks2] t].
- elim: ks1 N1 {U1 U}=>[|k ks1 IH] //=.
  rewrite inE negb_or (eq_sym 0)=>/andP [K N1].
  by rewrite !oltL T andbT; case: eqP=>//=; rewrite filter_cat.
have E2 : [seq x <- ks1 | x <[ks1++ks2] t] =
          [seq x <- ks1 | x <[ks1] t].
- apply/eq_in_filter=>x K; rewrite /seq_lt /nat_index /= !(eq_sym 0) (negbTE T).
  case: eqP=>// _; rewrite !index_cat K; case: ifPn=>// T'.
  rewrite -!index_mem -ltnNge in K T'.
  by rewrite !ltnS !(leq_trans K _) // leq_addr.
have E3 : [seq x <- ks2 | x <[ks1++ks2] t] =
  if t \in ks1 then [::] else [seq x <- ks2 | x <[ks2] t].
- case: ifPn=>T'; last first.
  - apply/eq_in_filter=>k K; rewrite /seq_lt /nat_index /= !(eq_sym 0) (negbTE T).
    case: eqP K=>[->|_ K]; first by rewrite (negbTE N2).
    by rewrite !index_cat (negbTE T') (negbTE (U _ K)) !ltnS ltn_add2l.
  rewrite -(filter_pred0 ks2); apply: eq_in_filter=>k K.
  rewrite /seq_lt /nat_index /= !(eq_sym 0) (negbTE T).
  case: eqP K=>[->|_ K]; first by rewrite (negbTE N2).
  apply/negbTE; rewrite !index_cat T' (negbTE (U _ K)) -ltnNge !ltnS ltnW //.
  by rewrite -!index_mem in K T'; rewrite (leq_trans T' _) // leq_addr.
by rewrite E1 E2 oev_cat E3; case: ifP.
Qed.

Lemma oex_lt_cons_same a ks k (h : natmap V) (z0 : R) :
        uniq (0::k::ks) ->
        oexec_lt a (k :: ks) k h z0 = z0.
Proof.
move=>U; rewrite (_ : k::ks = [::k] ++ ks) in U *; last by rewrite cat1s.
by rewrite oex_lt_cat //= inE oltL eq_refl.
Qed.

Lemma oex_lt_cons a ks k t v (h : natmap V) (z0 : R) :
        uniq (0::k::ks) ->
        (k, v) \In h ->
        oexec_lt a (k :: ks) t h z0 =
        if t == 0 then z0 else
          if t == k then z0 else oexec_lt a ks t h (a z0 v).
Proof.
move=>U H; case: (t =P 0)=>[->|/eqP T]; first by rewrite oex_lt0.
rewrite (_ : k::ks = [::k] ++ ks) in U *; last by rewrite cat1s.
rewrite oex_lt_cat //= inE oltL T andbT (eq_sym t); case: eqP=>//=.
by move/In_find: H=>->.
Qed.

Lemma oex_lt_rcons_in a ks k t (h : natmap V) (z0 : R) :
        uniq (0::rcons ks k) -> t \in ks ->
        oexec_lt a (rcons ks k) t h z0 = oexec_lt a ks t h z0.
Proof.
move=>U T; have N : t != 0.
- case: eqP T=>// ->; rewrite /= mem_rcons inE negb_or -andbA in U.
  by case/and3P: U=>_ /negbTE ->.
rewrite (_ : rcons ks k = ks ++ [:: k]) in U *; last by rewrite cats1.
by rewrite oex_lt_cat //= oltL T.
Qed.

Lemma oex_lt_rcons_notin a ks k t v (h : natmap V) (z0 : R) :
        uniq (0::rcons ks k) -> (k, v) \In h -> t \notin ks ->
        oexec_lt a (rcons ks k) t h z0 =
        if t == 0 then z0 else
          if t == k then oexec_lt a ks t h z0 else a (oexec_lt a ks t h z0) v.
Proof.
move=>U H K; case: (t =P 0)=>[->|/eqP T]; first by rewrite oex_lt0.
rewrite (_ : rcons ks k = ks ++ [:: k]) in U *; last by rewrite cats1.
rewrite oex_lt_cat //= oltL (negbTE K) T andbT (eq_sym k); case: eqP=>//=.
by move/In_find: H=>->.
Qed.

Lemma oex_lt_consecutive a x1 t1 t2 x2 (h : natmap V) (z0 : R) :
        uniq (0::x1 ++ [:: t1, t2 & x2]) ->
        oexec_lt a (x1 ++ [:: t1, t2 & x2]) t2 h z0 =
        oexec_le a (x1 ++ [:: t1, t2 & x2]) t1 h z0.
Proof.
move=>U; have X : x1 ++ [:: t1, t2 & x2] = rcons x1 t1 ++ [:: t2 & x2].
- by rewrite -cats1 -catA.
rewrite {}X /= in U *.
move: (U); rewrite !mem_cat cat_uniq /= !inE !negb_or -!andbA => U'.
case/and8P: U'=>U1 U2 U3 U4 U5 /hasPn /= U6 U7 U8.
rewrite oex_lt_cat // oex_le_cat // (negbTE U5) mem_rcons inE eq_refl.
rewrite (_ : t2 :: x2 = [:: t2] ++ x2) // oex_lt_cat; last first.
- by rewrite /= inE negb_or U2 U3 U7 U8.
rewrite inE eq_refl //= oltL eq_refl /= oex_ltT //.
by rewrite (eq_sym t2) (negbTE U2) oex_leT_last //= U1 U4.
Qed.

Lemma oex_le_lt_split a x1 x2 (h : natmap V) t v (z0 : R) :
        uniq (0::x1 ++ [:: t & x2]) ->
        (t, v) \In h ->
        oexec_le a (x1 ++ [:: t & x2]) t h z0 =
        a (oexec_lt a (x1 ++ [::t & x2]) t h z0) v.
Proof.
move=>U /In_find E; have X : x1 ++ [:: t & x2] = rcons x1 t ++ x2.
- by rewrite -cats1 -catA.
rewrite {}X /= in U *.
move: (U); rewrite !mem_cat cat_uniq /= negb_or -!andbA.
case/and5P=>U1 U2 U3 /hasPn /= U4 U5.
have U' : uniq (0 :: rcons x1 t) by rewrite /= U1 U3.
rewrite oex_le_cat // oex_lt_cat // mem_rcons inE eq_refl /=.
by rewrite oex_leT_last // oex_ltT_last // oev_rconsE E.
Qed.

End OExec.

(* induction principle for the new notation *)

Definition consecutive ks t1 t2 :=
  [&& t1 <[ks] t2, t2 \in ks &
      ~~ has (fun z => t1 <[ks] z && z <[ks] t2) ks].

Lemma consec_mem1 ks t1 t2 : consecutive ks t1 t2 -> t1 \in 0::ks.
Proof.
case/and3P=>H1 H2 _; rewrite inE.
move: H1; rewrite /seq_lt /nat_index /= !(eq_sym 0).
case: eqP=>// _; case: eqP=>//= _; rewrite ltnS.
by rewrite -index_mem=>/leq_trans; apply; apply: index_size.
Qed.

Lemma consec_mem2 ks t1 t2 : consecutive ks t1 t2 -> t2 \in ks.
Proof. by case/and3P. Qed.

Lemma cons_ind (ks : seq nat) (P : nat -> Prop) :
        uniq (0 :: ks) ->
        P 0 ->
        (forall t1 t2, consecutive ks t1 t2 -> P t1 -> P t2) ->
        forall t, t \in 0::ks -> P t.
Proof.
move=>/= /andP [U0 Uk] Bx IHx t; rewrite inE; case/orP=>[/eqP ->//|].
elim: ks U0 Uk IHx=>[|k ks IH] //=.
rewrite !inE !(eq_sym 0) negb_or=>/andP [Nk K0] /andP [Kk Uk] IHx.
have Nzk z : z \in ks -> z != 0 by case: eqP K0=>// -> /negbTE ->.
have Kzk z : z \in ks -> z != k by case: eqP Kk=>// -> /negbTE ->.
have C0k : consecutive (k::ks) 0 k.
- rewrite /consecutive olt0min Nk inE eq_refl /=.
  rewrite negb_or oltL eq_refl andbF /=.
  by apply/hasPn=>z /Nzk X; rewrite oltR (negbTE X) andbF.
case/orP=>[/eqP ->|]; first by apply: IHx C0k Bx.
apply: IH=>// t1 t2 /and3P [C1 C2 /hasPn /= C3].
have N1 : t1 != k.
- by case: eqP C1=>// -> /olt_mem; rewrite inE (negbTE Nk) (negbTE Kk).
have N2 : t2 != k by case: eqP C2 Kk=>// ->->.
have D1 : t1 <[k :: ks] t2 by apply: olt_consR C1; rewrite eq_sym.
have Nt2 : t2 != 0 by case: eqP C1=>// ->; rewrite olt0.
case: (t1 =P 0)=>[E _|/eqP N].
- suff Ckt2 : consecutive (k::ks) k t2 by apply: (IHx) Ckt2 (IHx _ _ C0k Bx).
  rewrite /consecutive /= !oltL eq_sym N2 Nt2 inE C2 orbT eq_refl /=.
  apply/hasPn=>z Kz; apply: contra (C3 z Kz).
  by rewrite E olt0min (Nzk _ Kz); case/andP=>_ /(olt_consL (Kzk _ Kz)) ->.
suff Ct1t2 : consecutive (k::ks) t1 t2 by apply: IHx.
rewrite /consecutive D1 inE C2 orbT /= negb_or oltR !negb_and N /=.
apply/hasPn=>z Kz; apply: contra (C3 z Kz)=>/andP [X1 X2].
by rewrite (olt_consL N1 X1) (olt_consL (Kzk _ Kz) X2).
Qed.

Lemma cons_splitP (ks : seq nat) t1 t2 :
        uniq (0 :: ks) ->
        reflect (exists x1 x2, 0 :: ks = x1 ++ [:: t1, t2 & x2])
                (consecutive ks t1 t2).
Proof.
move=>U; move: (U)=>/= /andP [K0 Ku].
case X : (consecutive ks t1 t2); constructor.
- case/and3P: X=>H1 H2 /hasPn H3.
  rewrite -[0::ks](cat_take_drop (index t2 (0::ks)).+1).
  rewrite /= -(olt_drop t2 U) -(ole_take t2 U).
  rewrite (ole_lt_split (t1:=t2)) // ole_leS // H2 -catA /=.
  rewrite (olt_le_split U H1).
  rewrite (_ : [seq x <- ks | t1 <[ks] x & x <[ks] t2] = [::]); last first.
  - rewrite (eq_in_filter (a2:=pred0)) ?filter_pred0 //.
    by move=>z /H3 /negbTE ->.
  rewrite -catA /=; move: (olt_mem H1); rewrite inE.
  case/orP=>[/eqP ->|Kt1]; last first.
  - rewrite (ole_lt_split (t1:=t1)) // ole_leS // Kt1 -catA /= -cat1s catA.
    by eexists _, _.
  exists [::], [seq x <- ks | t2 <[ks] x].
  rewrite (eq_in_filter (a2:=pred0)) ?filter_pred0 //.
  by move=>z; rewrite ole0; case: eqP K0=>// -> /negbTE ->.
move=>H; move/negP: X; apply; case: H; case=>[|x xs][ys] /= E.
- case: E U K0 Ku=><- -> U.
  rewrite inE negb_or (eq_sym 0)=>/andP [Nt2 Nys] /= /andP [Nty2 Uy].
  rewrite /consecutive /= !oltR (negbTE Nt2) inE !eq_refl /=.
  by apply/hasPn=>z _; rewrite olt0min oltR; case: z.
case: E U K0 Ku=>_ -> U K0 Ku; apply/and3P; split.
- apply: olt_catR=>//; first by rewrite !inE eq_refl orbT.
  rewrite cat_uniq in Ku; rewrite oltL; case/and3P: Ku=>_ _.
  case: eqP=>[->|_ _]; first by rewrite /= inE eq_refl.
  by case: eqP K0=>// ->; rewrite mem_cat !inE eq_refl !orbT.
- by rewrite mem_cat !inE eq_refl !orbT.
apply/hasPn=>z Kz; rewrite mem_cat !inE !negb_or in K0.
case/and4P: K0=>X1 X2 X3 X4; rewrite cat_uniq /= 2!negb_or in Ku.
case/and5P: Ku=>Y1 /and3P [Y2 Y3 Y4].
rewrite inE negb_or=>/andP [Y5 Y6] Y7 Y8.
rewrite /seq_lt /= (negbTE X2) (negbTE X3).
rewrite !index_cat (negbTE Y2) (negbTE Y3) /= (negbTE Y5).
rewrite !eq_refl /= addn0 addn1 ltnS.
case: ifP Kz=>[/eqP <-|Nz].
- by rewrite mem_cat (negbTE X1) /= !inE (negbTE X2) (negbTE X3) (negbTE X4).
rewrite !ltnS; case: ifP=>_; first by case: ltngtP.
case: ifP=>_; first by rewrite addn0 ltnn.
case: ifP=>[|_] _; first by rewrite addn1 ltnn andbF.
by rewrite negb_and; apply/orP; right; rewrite -ltnNge addnS ltnS leq_addr.
Qed.

Lemma oex_le_lt V R a t v (h : natmap V) ks (z0 : R) :
        uniq (0::ks) -> t \in ks -> (t, v) \In h ->
        oexec_le a ks t h z0 = a (oexec_lt a ks t h z0) v.
Proof. by move=>U K H; case/splitPr: K U=>x1 x2 U; apply: oex_le_lt_split. Qed.

Lemma oex_lt_le_consec V R a t1 t2 (h : natmap V) ks (z0 : R) :
        uniq (0::ks) ->
        consecutive ks t1 t2 ->
        oexec_lt a ks t2 h z0 = oexec_le a ks t1 h z0.
Proof.
move=>U C; case/(cons_splitP _ _ U): C=>x1 [x2] E; rewrite E in U.
case: x1 E U=>[|x x1][??]; last by subst x ks; apply: oex_lt_consecutive.
subst t1 ks; rewrite /= inE negb_or=>/and3P [] /andP [H1 H2] H3 H4.
rewrite /= oltL oleL eq_refl (eq_sym t2) (negbTE H1) /=.
congr oeval; apply: eq_in_filter=>z.
by rewrite oltR ole0 (eq_sym t2) H1 andbT.
Qed.

Lemma oex_lt_consec V R a t1 t2 v (h : natmap V) ks (z0 : R) :
        uniq (0::ks) ->
        (t1, v) \In h ->
        consecutive ks t1 t2 ->
        oexec_lt a ks t2 h z0 = a (oexec_lt a ks t1 h z0) v.
Proof.
move=>U H C; case/(cons_splitP _ _ U): C=>x1 [x2] E; rewrite E in U.
case: x1 E U=>[|x x1] /=; first by case=>?; subst t1; move/In_dom/dom_cond: H.
by case=>? E U; subst x; rewrite E -oex_le_lt_split //; apply: oex_lt_consecutive.
Qed.

Lemma oex_lt_consec0 V R a t (h : natmap V) ks (z0 : R) :
        uniq (0::ks) ->
        consecutive ks 0 t ->
        oexec_lt a ks t h z0 = z0.
Proof.
move=>U C; case/(cons_splitP _ _ U): C=>x1 [x2]; case: x1=>[|x xs] /=.
- by case=>?; subst ks; rewrite oex_lt_cons_same.
by case=>??; subst x ks; move: U; rewrite /= mem_cat inE eq_refl !orbT.
Qed.

(* A restatement of the induction principle into a form *)
(* that's more usable in the common cases *)

Lemma consec0_ind (ks : seq nat) (P : nat -> Prop) :
        uniq (0 :: ks) ->
        P 0 ->
        (forall t, consecutive ks 0 t -> P 0 -> P t) ->
        (forall t1 t2, t1 \in ks -> consecutive ks t1 t2 -> P t1 -> P t2) ->
        forall t, t \in 0::ks -> P t.
Proof.
move=>U H0 H1 Ht; apply: cons_ind=>// t1 t2 C.
move: {C} (consec_mem1 C) (C); rewrite inE; case/orP.
- by move/eqP=>->; apply: H1.
by apply: Ht.
Qed.

Lemma consec_ind (ks : seq nat) (P : nat -> Prop) :
        uniq (0 :: ks) ->
        (forall t, consecutive ks 0 t -> P t) ->
        (forall t1 t2, t1 \in ks -> consecutive ks t1 t2 -> P t1 -> P t2) ->
        forall t, t \in ks -> P t.
Proof.
move=>U H1 Ht t D.
have D0 : t \in 0::ks by rewrite inE D orbT.
move: t D0 D; apply: consec0_ind=>//.
- by move: U=>/= /andP [/negbTE ->].
- by move=>t /H1.
by move=>t1 t2 Kt1 C H _; apply: Ht C (H Kt1).
Qed.

Lemma oleq_eqVlt ks t1 t2 :
        t1 \in ks \/ t2 \in ks ->
        t1 <=[ks] t2 = (t1 == t2) || (t1 <[ks] t2).
Proof.
move=>H; rewrite /seq_lt /seq_le leq_eqVlt /=.
case: ifP; case: ifP.
- by move/eqP=><- /eqP <-.
- by move=>N /eqP <-; rewrite N.
- by move/eqP=><- N; rewrite /= !ltn0 orbF -(eq_sym 0) N.
move=>N1 N2; rewrite !ltnS eqSS.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

Lemma olt_sorted ks t1 t2 :
        sorted ltn ks -> t2 \in ks -> t1 <[ks] t2 -> t1 < t2.
Proof.
move=>S Kt2; rewrite /seq_lt /=.
case: ifP; case: ifP=>//; first by move=>H2 /eqP <-; case: t2 H2 Kt2.
by move=>_ _; rewrite ltnS; apply: sorted_index_ord ltnn ltn_trans S Kt2.
Qed.

Lemma ole_sorted ks t1 t2 :
        sorted ltn ks -> t2 \in ks -> t1 <=[ks] t2 -> t1 <= t2.
Proof.
move=>S K; rewrite oleq_eqVlt; last by right.
by case/orP=>[/eqP -> //|/(olt_sorted S K)/ltnW].
Qed.

Lemma oltnNge ks t1 t2 : t1 <[ks] t2 = ~~ t2 <=[ks] t1.
Proof.
rewrite /seq_lt /seq_le /= !(eq_sym 0).
by case: ifP; case: ifP=>// N2 N1; rewrite !ltnS ltnNge.
Qed.

Lemma oleqNgt ks t1 t2 : t1 <=[ks] t2 = ~~ t2 <[ks] t1.
Proof. by rewrite oltnNge negbK. Qed.

Lemma consec_sorted ks t1 t2 :
        sorted ltn ks -> consecutive ks t1 t2 ->
        forall z, z \in 0::ks -> (z <= t1) = (z < t2).
Proof.
move=>S /and3P [T1 T2 /hasPn T3]; move: (olt_mem T1)=>D1.
move/(olt_sorted S T2): T1=>T1.
move=>z; rewrite inE; case/orP.
- by move/eqP=>->; rewrite leq0n; case: t2 {T2 T3} T1.
move=>Dz; move: (T3 z Dz); rewrite !negb_and -!oleqNgt.
case/orP=>D; last first.
- move: (ole_sorted S Dz D)=>Z2.
  by rewrite leqNgt (leq_trans T1 Z2) ltnNge Z2.
rewrite inE in D1; case/orP: D1 D=>[/eqP ->|D1 D].
- rewrite ole0=>/eqP ->; rewrite leqnn.
  by rewrite (leq_ltn_trans _ T1).
move: (ole_sorted S D1 D)=>Z1.
by rewrite Z1 (leq_ltn_trans Z1 T1).
Qed.

(* we frequently need to talk about consecutivity of stamps *)
(* wrt. some additional property *)

Definition consecutivep ks p t1 t2 :=
  [&& t1 <[ks] t2, t2 \in ks &
      ~~ has (fun z => [&& t1 <[ks] z, z <[ks] t2 & p z]) ks].

Lemma consp_ind (ks : seq nat) (p : pred nat) (P : nat -> Prop) :
        uniq (0 :: ks) ->
        P 0 ->
        (forall t1 t2, t1 <[ks] t2 ->
            t2 \in filter p ks ->
            ~~ has (fun z => t1 <[ks] z && z <[ks] t2) (filter p ks) ->
            P t1 -> P t2) ->
        forall t : nat, t \in 0::filter p ks -> P t.
Proof.
move=>/= /andP [U1 U2] H IH; apply: cons_ind=>//=.
- by rewrite mem_filter negb_and filter_uniq // U1 orbT.
move=>t1 t2 /and3P [X H2 /hasPn H3]; move: (olt_mem X); rewrite inE=>H1.
apply: IH=>//.
- case/orP: H1=>[/eqP ->|]; last by move/olt_filter=><-.
  by rewrite olt0min; case: eqP X=>// ->; rewrite olt0.
apply/hasPn=>z Kz; apply: contra (H3 _ Kz).
by case/orP: H1=>[/eqP ->|H1]; rewrite ?olt0min !olt_filter.
Qed.


(* the generalization of the growing argument *)

Section OGrowing.
Variables (V R : Type) (X : ordType) (a : R -> V -> R) (f : R -> X).

Lemma ohelper0 ks h z0 :
        growing a f h -> oleq (f z0) (f (oevalv a ks h z0)).
Proof.
move=>G; elim: ks z0=>[|k ks IH] z0 //=; apply: otrans (IH _).
by case E: (find k h)=>[b|] //; move/In_find: E; apply: G.
Qed.

Lemma ohelper1 h k ks z0 v :
        growing a f h -> (k, v) \In h ->
        f (oevalv a (k::ks) h z0) = f z0 ->
        f (a z0 v) = f z0.
Proof.
move=>G H /=; move/In_find: (H)=>-> E; apply/eqP; case: ordP=>//.
- by move: (G k v z0 H); rewrite /oleq eq_sym; case: ordP.
by move: (ohelper0 ks (a z0 v) G); rewrite E /oleq eq_sym; case: ordP.
Qed.

Lemma ohelper2 h ks1 k ks2 z0 v :
        growing a f h -> (k, v) \In h ->
        f (oevalv a (ks1++k::ks2) h z0) = f z0 ->
        f (a (oevalv a ks1 h z0) v) = f (oevalv a ks1 h z0).
Proof.
move=>G H E1; move/In_find: (H)=>F.
suff E2 : f (oevalv a ks1 h z0) = f z0.
- by rewrite oev_cat -E2 in E1; apply: ohelper1 G H E1.
apply/eqP; case: ordP=>//.
- by move: (ohelper0 ks1 z0 G); rewrite /oleq eq_sym; case: ordP.
suff: oleq (f (oevalv a ks1 h z0)) (f z0).
- by rewrite /oleq eq_sym; case: ordP.
by rewrite -E1 oev_cat; apply: ohelper0.
Qed.

(* "introducing" growth *)
Lemma ogrowI ks h t1 t2 z0 :
        growing a f h -> uniq (0::ks) -> t1 <=[ks] t2 ->
        oleq (f (oexec_le a ks t1 h z0)) (f (oexec_le a ks t2 h z0)).
Proof. by move=>G U N; rewrite (ole_le_split U N) oev_cat; apply: ohelper0. Qed.

(* "eliminating" growth *)
Lemma ogrowE ks h t1 t2 z0 k v :
        growing a f h ->
        uniq (0::ks) ->
        (k, v) \In h -> k \in ks ->
        t1 <[ks] k -> k <=[ks] t2 ->
        f (oexec_le a ks t2 h z0) = f (oexec_le a ks t1 h z0) ->
          f (a (oevalv a [seq x <- ks | x <[ks] k] h z0) v) =
          f (oevalv a [seq x <- ks | x <[ks] k] h z0).
Proof.
move=>G U H K N1 N2 E; have Uk : uniq ks by case/andP: U.
set k0 := [seq x <- ks | x <=[ks] t1] in E.
set k1 := [seq x <- ks | t1 <[ks] x & x <[ks] k].
set k2 := [seq x <- ks | k <[ks] x & x <=[ks] t2].
have E1 : [seq x <- ks | x <[ks] k] = k0 ++ k1 by rewrite (olt_le_split U N1).
have E2 : [seq x <- ks | x <=[ks] t2] = (k0 ++ k1) ++ k :: k2.
- rewrite (ole_le_split U N2) -E1 -cat_rcons -cats1.
  by rewrite (ole_lt_split U (leqnn _)) ole_leS // K.
by rewrite E1 oev_cat; rewrite E2 -catA oev_cat in E; apply: ohelper2 G H E.
Qed.

End OGrowing.

(**********************)
(* umall2 and natmaps *)
(**********************)

Section Umall2.
Variables (A : Type) (P : A -> A -> Prop).

Lemma umall2_lastkey (h1 h2 : natmap A) :
        um_all2 P h1 h2 -> last_key h1 = last_key h2.
Proof. by move/umall2_dom=>E; rewrite /last_key E. Qed.

Lemma umall2_umfilt_lastkey (h1 h2 : natmap A) :
        um_all2 P h1 (um_filter (le (last_key h1)) h2) <->
        forall k, k <= last_key h1 -> optionR P (find k h1) (find k h2).
Proof.
pose f t (kv : nat*A) := oleq kv.1 t.
have E (h : natmap A) : forall kv : nat * A, kv \In h ->
     le (last_key h1) kv = f (last_key h1) kv.
- by case=>k v _; rewrite /f/oleq/ord /=; case: ltngtP.
rewrite -{1}[h1]umfilt_last.
move/eq_in_umfilt: (E h2)=>->.
move/eq_in_umfilt: (E h1)=>->.
rewrite umall2_umfilt_oleq; split=>H k N; apply: H;
by move: N; rewrite /oleq/ord /=; case: ltngtP.
Qed.

End Umall2.

(* Transitive closure of relations between stamps *)
(* in a natmap. This is somewhat streamlined compared *)
(* to plan transitive closure rtc. *)
(* First, we don't want reflexive closure. *)
(* Second, we want a different closure condition *)
(* Because this is really about histories, we name the *)
(* lemmas using a prefix "h", rather than "nm" for natmaps *)

Section HistoryTransitiveClosure.
Variables (A : Type) (h : natmap A) (R : rel nat).
Hypothesis HRclosed : forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h).

Definition hrtc x y := rtc (0::dom h) R x y.
Definition htc x y := tc (0::dom h) R x y.

Definition acyclic (R : rel nat) := forall x y n, iter' R n.+1 x y -> x != y.

Lemma hclosed x y : R x y -> (x \in 0::dom h) = (y \in 0::dom h).
Proof. by case/HRclosed/andP=>->->. Qed.

Lemma hrtc_pathP x y :
        reflect (x \in 0::dom h /\ exists2 p, path R x p & y = last x p)
                (hrtc x y).
Proof. by apply/(rtc_pathP hclosed). Qed.

Lemma hrtcP x y : reflect (x \in 0::dom h /\ iter R x y) (hrtc x y).
Proof. by apply/(rtcP hclosed). Qed.

Lemma hrtc_pathP_last x y :
        reflect (y \in 0::dom h /\ exists2 p, path R x p & y = last x p)
                (hrtc x y).
Proof. by apply/(rtc_pathP_last hclosed). Qed.

Lemma hrtcP_last x y : reflect (y \in 0::dom h /\ iter R x y) (hrtc x y).
Proof. by apply/(rtcP_last hclosed). Qed.

Lemma htcP_closed x y : htc x y -> (x \in 0::dom h) && (y \in 0::dom h).
Proof.
rewrite /htc/tc=>/andP [->] /hasP [z Mz /andP [Rxz]].
case/(rtcP_last hclosed)=>My; case; case=>[<-|n /iterS [w][_]];
by [case/HRclosed/andP: Rxz | case/HRclosed/andP].
Qed.

Lemma htcP x y : reflect (exists n, iter' R n.+1 x y) (htc x y).
Proof.
rewrite /htc; case: (tcP hclosed)=>H; constructor; first by case: H.
case=>n /= [z][Rxz J]; apply: H; split; last by exists n, z.
by case/HRclosed/andP: Rxz.
Qed.

Lemma hrtc_acyc_asym : acyclic R -> antisymmetric hrtc.
Proof.
move=>H x y /andP [/hrtcP [_ [n1 H1]] /hrtcP [_ [n2 H2]]].
case: n1 H1=>[|n1 H1] //; move: (H x x (n1+n2)).
by rewrite -addSn=>/(_ (iter'_add H1 H2)); rewrite eq_refl.
Qed.

Lemma hrtc_asym_acyc : irreflexive R -> antisymmetric hrtc -> acyclic R.
Proof.
move=>I S x s n /= [y][H1 H2]; case: eqP=>// N; subst s.
case/andP: (HRclosed H1)=>Y1 Y2; move: (S x y) (H1).
have -> : hrtc x y by apply/hrtcP; split=>//; exists 1, y.
have -> : hrtc y x by apply/hrtcP; split=>//; exists n.
by move=>-> //; rewrite I.
Qed.

Lemma htc_acyc : acyclic R <-> irreflexive htc.
Proof.
split=>[H x|H x y n]; first by case: htcP=>//; case=>n /H; rewrite eq_refl.
case: eqP=>// <-{y} J; have: exists n, iter' R n.+1 x x by exists n.
by move/htcP; rewrite H.
Qed.

Lemma htc_trans : transitive htc.
Proof. by apply: tc_trans=>x y /HRclosed /andP [->]; rewrite inE orbC=>->. Qed.

Lemma htc_antisym : acyclic R -> antisymmetric htc.
Proof. by move/htc_acyc=>H x y /andP [X /(htc_trans X)]; rewrite H. Qed.

Lemma htc1 x y : R x y -> htc x y.
Proof. by move=>Rxy; apply/htcP; exists 0, y. Qed.

End HistoryTransitiveClosure.

Lemma htc_idemp A (h : natmap A)  (R : rel nat) :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        htc h (htc h R) =2 htc h R.
Proof. by move=>Rcond x y; rewrite /htc tc_idemp. Qed.

Lemma htc_sub A (h : natmap A) (R1 R2 : rel nat) x y :
        (forall x y, R2 x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x y, R1 x y -> R2 x y) ->
        htc h R1 x y -> htc h R2 x y.
Proof. by move=>Rcond Rsub; apply: tc_sub. Qed.

Lemma htc_ind2 A (h : natmap A) (R1 : rel nat) (R2 : nat -> nat -> Prop) x y :
        (forall x y, R1 x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x y, R1 x y -> R2 x y) ->
        Transitive R2 ->
        htc h R1 x y -> R2 x y.
Proof.
move=>H S T /(htcP H) [n].
elim: n x y=>[|n IH] x y /= [s][X]; first by move=><-; apply: S.
by move/IH; apply: T (S _ _ X).
Qed.

Lemma htc_last A (h : natmap A) (R : rel nat) (P : Pred nat) :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x y, R x y -> P y) ->
        (forall x y, htc h R x y -> P y).
Proof.
move=>H L x y /htcP [] // n; elim: n x y=>[|n IH] x y /= [s][X];
by [move=><-; apply: L X |move/IH].
Qed.

Lemma hrtc_last A (h : natmap A) (R : rel nat) (P : Pred nat) :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x y, R x y -> P y) ->
        (forall x y, hrtc h R x y -> P y \/ x = y).
Proof.
move=>H L x y /hrtcP [] // _ [n]; elim: n x y=>[|n IH] x y /=; first by right.
by case=>s [/L X] /IH; case=>[|<-]; left.
Qed.

(* minimality of m is preserved by htc and hrtc *)

Lemma htc_min A (h : natmap A) (R : rel nat) m :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x, R x m -> x = m) ->
        (forall x, htc h R x m -> x = m).
Proof.
move=>H M x /htcP [] // n; elim: n x=>[|n IH] x /=.
- by case=>s [X E]; move: E X=>-> /M.
by case=>s [X] /IH E; move: E X=>-> /M.
Qed.

Lemma hrtc_min A (h : natmap A) (R : rel nat) m :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x, R x m -> x = m) ->
        (forall x, hrtc h R x m -> x = m).
Proof.
move=>H M x /hrtcP [] // D [n]; elim: n x D=>[|n IH] x D //= [s][X] /IH.
by case/andP: (H _ _ X)=>_ S /(_ S) E; move: E X=>->; apply: M.
Qed.

(* when an element is not in range *)

Lemma htcR A (h : natmap A) (R : rel nat) m :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x, ~ R x m) ->
        (forall x, ~ htc h R x m).
Proof.
move=>H M x /htcP [] // n; elim: n x=>[|n IH] /= x [s][X];
by [move=>E; move: E X=>-> /M | move/IH].
Qed.

Lemma hrtcR A (h : natmap A) (R : rel nat) m :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        (forall x, ~ R x m) ->
        (forall x, hrtc h R x m -> x = m).
Proof.
move=>H M x /hrtcP [] // _ [n]; elim: n x=>[|n IH] x //=.
by case=>s [X] /IH E; move: E X=>-> /M.
Qed.

(* there's really not much reason to bother with reflexive closure *)
(* as it's defined simply in terms of transitive closure *)
Lemma hrtcE A (h : natmap A) (R : rel nat) x y :
        (forall x y, R x y -> (x \in 0::dom h) && (y \in 0::dom h)) ->
        hrtc h R x y = htc h R x y || (x == y) && (x \in 0::dom h).
Proof.
move=>H; apply/(hrtcP H)/idP; last first.
- case/orP; last by case/andP=>/eqP -> Y.
  by case/(htcP H)=>n /= [s][X Y]; split; [case/H/andP: X|exists n.+1, s].
case=>-> [n]; rewrite andbT; elim: n x y=>[|n IH] x y /=.
- by move=>->; rewrite eq_refl orbT.
by case=>s [/(htc1 H) X] /IH /orP [/(htc_trans X) ->|/eqP <-] //; rewrite X.
Qed.
