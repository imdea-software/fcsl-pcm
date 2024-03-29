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
From mathcomp Require Import ssrnat eqtype seq path interval.
From pcm Require Import options prelude pred finmap rtc seqext useqord uslice uconsec.
From pcm Require Export pcm morphism unionmap.

From mathcomp Require order.
Import order.Order.NatOrder.

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
- by rewrite domF inE eqxx.
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
- by rewrite domUn inE valid_freshX //= V2 /= domPt inE /= eqxx.
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
  rewrite domUn inE valid_freshUn // (validE2 V) /= domPt inE ?eqxx //.
rewrite andbC eq_sym leq_eqVlt; case: eqP=>//= _ D.
by apply: lastkey_max; rewrite domUn inE V D.
Qed.

Lemma lastkey_fresh h v : valid h -> last_key (fresh h \-> v \+ h) = fresh h.
Proof.
move=>Vf; apply: max_lastkey=>[|x] /=.
- by rewrite domUn inE valid_fresh // Vf domPt inE eqxx.
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


Section LastVal.
Variable A : Type.
Implicit Type h : natmap A.

Definition last_val h := find (last_key h) h.

Lemma lastval0 : last_val Unit = None.
Proof. by rewrite /last_val lastkey0 find0E. Qed.

Lemma lastval_undef : last_val um_undef = None.
Proof. by rewrite /last_val lastkey_undef find_undef. Qed.

Variant lastval_specx h : option A -> Type :=
| lastval_somex r kv of last_val h = Some r & kv \In h :
    lastval_specx h (Some r)
| lastval_nonex of valid h & h = Unit : lastval_specx h None
| lastval_undefx of h = um_undef : lastval_specx h None.

Lemma lastvalPX h : lastval_specx h (last_val h).
Proof.
case E : (last_val h)=>[a|].
- move/find_some: (E); case: dom_find=>// v /In_find H _ _.
  by apply: lastval_somex E H.
move/find_none: E=>E.
case V : (valid h).
- by move/(lastkey_dom V)/(lastval_nonex V): E.
by move/negbT/invalidE: V=>->; apply: lastval_undefx.
Qed.

Variant lastval_spec h : option A -> Type :=
| lastval_some r kv of last_val h = Some r & kv \In h :
    lastval_spec h (Some r)
| lastval_none of last_val h = None & (forall kv, kv \Notin h) :
    lastval_spec h None.

Lemma lastvalP h : lastval_spec h (last_val h).
Proof.
case: lastvalPX=>[r kv|_ ->|->].
- by apply: lastval_some.
- by apply: lastval_none=>[|kv /In0//]; rewrite lastval0.
by apply: lastval_none=>[|kv /In_undef//]; rewrite lastval_undef.
Qed.

Lemma lastvalS h : reflect (exists kv, kv \In h) (isSome (last_val h)).
Proof.
case: lastvalP=>[r kv E H|E H]; constructor.
- by exists kv.
by case=>kv /H.
Qed.

Lemma lastval_mem kv h : kv \In h -> exists r, last_val h = Some r.
Proof. by case: lastvalP=>[r|_ H /H//]; exists r. Qed.

Lemma lastval_mem_none kv h : last_val h = None -> kv \Notin h.
Proof. by case: lastvalP. Qed.

End LastVal.

(***********************************************)
(***********************************************)
(* Executing up to (and including/excluding) t *)
(***********************************************)
(***********************************************)

Definition oexec_le V R (a : R -> V -> R) ks t (h : natmap V) z0 :=
  oevalv a (&=ks `]-oo, t]) h z0.
Definition oexec_lt V R (a : R -> V -> R) ks t (h : natmap V) z0 :=
  oevalv a (&=ks `]-oo, t[) h z0.

(* Main transfer lemmas *)

Lemma oexleE V R a t v (h : natmap V) ks (z0 : R) :
        t \in ks -> (t, v) \In h ->
        oexec_le a ks t h z0 = a (oexec_lt a ks t h z0) v.
Proof.
by move=>K H; rewrite /oexec_le/oexec_lt eqsl_uxR K (oev_rconsP _ _ _ H).
Qed.

Arguments oexleE [V R a t v h ks z0].

Lemma oexleNE V R a t (h : natmap V) ks (z0 : R) :
        (t \notin ks) || (t \notin dom h) ->
        oexec_le a ks t h z0 = oexec_lt a ks t h z0.
Proof.
rewrite /oexec_le/oexec_lt; case K: (t \in ks)=>/= H; last first.
- rewrite (eqsl_uoxx (t1:=t) (t2:=t)); last by exact: sle_refl.
  by rewrite eqsl_kk1 /= K cats0.
rewrite [LHS]oevFK [RHS]oevFK; congr oeval.
by rewrite eqsl_uxR K filter_rcons (negbTE H).
Qed.

Arguments oexleNE [V R a t h ks z0].

(**********************************************************)
(* Interaction of oexec_lt and oexec_le with constructors *)
(**********************************************************)

Lemma oexlt_notin V R a ks t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_lt a ks t h z0 = oevalv a ks h z0.
Proof. by move=>K; rewrite /oexec_lt eqsl_uL_notinE. Qed.

Arguments oexlt_notin [V R a ks t h z0].

Lemma oexle_notin V R a ks t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_le a ks t h z0 = oevalv a ks h z0.
Proof. by move=>K; rewrite /oexec_le eqsl_uL_notinE. Qed.

Arguments oexle_notin [V R a ks t h z0].

Lemma oexlt_cat V R a ks1 ks2 t (h : natmap V) (z0 : R) :
        t \notin ks1 ->
        oexec_lt a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_lt a ks1 t h z0
        else oexec_lt a ks2 t h (oexec_lt a ks1 t h z0).
Proof.
move=>T; rewrite /oexec_lt eqsl_uL_catE (negbTE T).
by rewrite oev_cat (eqsl_uL_notinE (s:=ks1)).
Qed.

Arguments oexlt_cat [V R a ks1 ks2 t h z0].

Lemma oexle_cat V R a ks1 ks2 t (h : natmap V) (z0 : R) :
        t \notin ks1 ->
        oexec_le a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_le a ks1 t h z0
        else oexec_le a ks2 t h (oexec_le a ks1 t h z0).
Proof.
move=>T; rewrite /oexec_le eqsl_uL_catE (negbTE T).
by rewrite oev_cat (eqsl_uL_notinE (s:=ks1)).
Qed.

Arguments oexle_cat [V R a ks1 ks2 t h z0].

Lemma oexlt_cons V R a ks k t v (h : natmap V) (z0 : R) :
        (k, v) \In h -> t != k ->
        oexec_lt a (k :: ks) t h z0 = oexec_lt a ks t h (a z0 v).
Proof.
move=>H Ntk; rewrite /oexec_lt eqsl_uL_consE (negbTE Ntk) /=.
by move/In_find: H=>->.
Qed.

Arguments oexlt_cons [V R a ks k t v h z0].

Lemma oexle_cons V R a ks k t v (h : natmap V) (z0 : R) :
        (k, v) \In h ->
        oexec_le a (k :: ks) t h z0 =
        if t == k then a z0 v else oexec_le a ks t h (a z0 v).
Proof.
move=>H; rewrite /oexec_le eqsl_uL_consE.
by case: eqP=>/=; move/In_find: H=>->.
Qed.

Arguments oexle_cons [V R a ks k t v h z0].

(* for oexlt, we need to cover the case when k == t *)
Lemma oexlt_cons_same V R a ks k (h : natmap V) (z0 : R) :
        oexec_lt a (k :: ks) k h z0 = z0.
Proof. by rewrite /oexec_lt eqsl_uL_consL. Qed.

Arguments oexlt_cons_same {V R a ks k h z0}.

Lemma oexlt_cons_notin V R a ks k t (h : natmap V) (z0 : R) :
        k \notin dom h -> t != k ->
        oexec_lt a (k :: ks) t h z0 = oexec_lt a ks t h z0.
Proof.
move=>H Ntk; rewrite /oexec_lt eqsl_uL_consE (negbTE Ntk) /=.
by case: dom_find H=>//= -> _.
Qed.

Arguments oexlt_cons_notin [V R a ks k t h z0].

(* for oexle, we have two "notin" lemmas *)
Lemma oexle_cons_same_notin V R a ks k (h : natmap V) (z0 : R) :
        k \notin dom h -> oexec_le a (k :: ks) k h z0 = z0.
Proof.
move=>H.
by rewrite /oexec_le [in LHS]oevFK eqsl_uL_consL /= (negbTE H).
Qed.

Arguments oexle_cons_same_notin [V R a ks k h z0].

Lemma oexle_cons_notin V R a ks k t (h : natmap V) (z0 : R) :
        k \notin dom h -> t != k ->
        oexec_le a (k :: ks) t h z0 = oexec_le a ks t h z0.
Proof.
move=>H Ntk; rewrite /oexec_le [in LHS]oevFK [in RHS]oevFK.
by rewrite eqsl_uL_consE (negbTE Ntk) /= (negbTE H).
Qed.

Arguments oexle_cons_notin [V R a ks k t h z0].

Lemma oexlt_rcons V R a ks k t (h : natmap V) (z0 : R) :
        t \in ks ->
        oexec_lt a (rcons ks k) t h z0 = oexec_lt a ks t h z0.
Proof. by move=>T; rewrite /oexec_lt eqsl_uL_rconsE T. Qed.

Arguments oexlt_rcons [V R a ks k t h z0].

Lemma oexle_rcons V R a ks k t (h : natmap V) (z0 : R) :
        t \in ks ->
        oexec_le a (rcons ks k) t h z0 = oexec_le a ks t h z0.
Proof. by move=>T; rewrite /oexec_le eqsl_uL_rconsE T. Qed.

Arguments oexle_rcons [V R a ks k t h z0].

Lemma oexlt_rcons_notin V R a ks k t v (h : natmap V) (z0 : R) :
        (k, v) \In h -> t \notin ks -> t != k ->
        oexec_lt a (rcons ks k) t h z0 =
        a (oexec_lt a ks t h z0) v.
Proof.
move=>H T Ntk; rewrite /oexec_lt eqsl_uL_rconsE /= (negbTE T) Ntk.
by rewrite oev_rconsE eqsl_uL_notinE //; move/In_find: H=>->.
Qed.

Arguments oexlt_rcons_notin [V R a ks k t v h z0].

Lemma oexle_rcons_notin V R a ks k t (h : natmap V) (z0 : R) :
        t \notin ks ->
        oexec_le a (rcons ks k) t h z0 = oevalv a (rcons ks k) h z0.
Proof. by move=>T; rewrite /oexec_le eqsl_uL_rconsE (negbTE T). Qed.

Arguments oexle_rcons_notin [V R a ks k t h z0].

(* in case of oexlt we must cover the case when t == k *)
Lemma oexlt_rcons_same V R a ks k (h : natmap V) (z0 : R) :
        k \notin ks ->
        oexec_lt a (rcons ks k) k h z0 = oevalv a ks h z0.
Proof. by move=>U; rewrite /oexec_lt eqsl_uL_rconsE eqxx /= (negbTE U). Qed.

Arguments oexlt_rcons_same [V R a ks k h z0].

(* in case of oexle, case t == k can be optimized *)
(* TODO doesn't simplify anything *)
Lemma oexle_rcons_same V R a ks k (h : natmap V) (z0 : R) :
        k \notin ks ->
        oexec_le a (rcons ks k) k h z0 = oevalv a (rcons ks k) h z0.
Proof. exact: oexle_rcons_notin. Qed.

Arguments oexle_rcons_same [V R a ks k h z0].

(* in case of oexle, when we know the value at k *)
(* we can further expand the right-hand side *)
Lemma oexle_rcons_notin_in V R a ks k t v (h : natmap V) (z0 : R) :
        (k, v) \In h -> t \notin ks ->
        oexec_le a (rcons ks k) t h z0 = a (oexec_le a ks t h z0) v.
Proof.
move=>H T; rewrite oexle_rcons_notin // oev_rconsE.
by move/In_find: (H)=>->; rewrite oexleNE ?T // /oexec_lt eqsl_uL_notinE.
Qed.

Arguments oexle_rcons_notin_in [V R a ks k t v h z0].

(* oexlt/oexle filter lemmas *)

Lemma oexlt_umfilt V R a ks p t (h : natmap V) (z0 : R) :
        oexec_lt a ks t (um_filterk p h) z0 =
        oevalv a (filter p (&=ks `]-oo, t[)) h z0.
Proof. by rewrite /oexec_lt oev_filter. Qed.

Arguments oexlt_umfilt {V R a ks p t h z0}.

Lemma oexle_umfilt V R a ks p t (h : natmap V) (z0 : R) :
        oexec_le a ks t (um_filterk p h) z0 =
        oevalv a (filter p (&=ks `]-oo, t])) h z0.
Proof. by rewrite /oexec_le oev_filter. Qed.

Arguments oexle_umfilt {V R a ks p t h z0}.

(* two somewhat simpler rewrites under a condition *)
Lemma oexlt_umfiltN V R a ks p t (h : natmap V) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_lt a ks t (um_filterk p h) z0 =
        oexec_lt a (filter p ks) t h z0.
Proof.
move=>H; rewrite /oexec_lt oev_umfilt eqsl_filterL //=.
apply: eq_in_oevK; rewrite -!filter_predI; apply: eq_in_filter=>k Ks /=.
by case D : (k \in dom h)=>//=; case/In_domX: D=>v /In_find ->.
Qed.

Arguments oexlt_umfiltN [V R a ks p t h z0].

Lemma oexle_umfiltN V R a ks p t (h : natmap V) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_le a ks t (um_filterk p h) z0 =
        oexec_le a (filter p ks) t h z0.
Proof.
move=>H; rewrite /oexec_le oev_umfilt eqsl_filterL //=.
apply: eq_in_oevK; rewrite -!filter_predI; apply: eq_in_filter=>k Ks /=.
by case D : (k \in dom h)=>//=; case/In_domX: D=>v /In_find ->.
Qed.

Arguments oexle_umfiltN [V R a ks p t h z0].

(* restating the last two lemmas for the other direction *)
(* TODO why not just state them like this initially? *)
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
        oexec_le a (k::ks) (last k (&=ks `]-oo, t[)) h z0.
Proof.
move=>U Ntk; rewrite /oexec_lt/oexec_le [LHS]oevFK [RHS]oevFK.
by rewrite eqsl_uox_last.
Qed.

Lemma oev_oexle_last V R a k ks (h : natmap V) (z0 : R) :
        uniq (k::ks) ->
        oevalv a (k::ks) h z0 =
        oexec_le a (k::ks) (last k ks) h z0.
Proof.
case/andP=>U1 U2; rewrite /oexec_le eqsl_uL_consE.
case: eqP=>/= [/last_nochange|/eqP/last_change H].
- by rewrite (negbTE U1)=>/eqP->.
by congr oeval; apply/eqsl_lastR_uniq.
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
        {in &=ks `]t1, t2[, oex_inv P a ks h z0} ->
        P (oexec_le a ks t1 h z0) -> P (oexec_lt a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_lt (eqsl_uxoo T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `]t1, t2[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]t1, t2[): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_oo: (K)=>// [_ T1K T2K].
suff {IH U K}-> : ks1 = &=ks `]t1, k[ by rewrite -eqsl_uxoo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=;
  last by apply/andP; rewrite !lteBSide /= leEnat; split=>//=; apply: ltnW.
rewrite eqsl_xoL T2K /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

(* one can try to derive the next lemma from the previous *)
(* but we need to reason about successor of t1 in ks *)
(* which we don't have yet. Hence, we prove the lemma directly *)
(* using the same approach as in the previous lemma. *)

Lemma oex_oo V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2[, oex_inv P a ks h z0} ->
        P (oexec_lt a ks t1 h z0) -> P (oexec_lt a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_lt (eqsl_uoxo T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `[t1, t2[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `[t1, t2[): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_xo: (K)=>// [_ T1K T2K].
suff {IH U K}-> : ks1 = &=ks `[t1, k[ by rewrite -eqsl_uoxo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=;
  last by apply/andP; rewrite !lteBSide /= !leEnat; split=>//=; apply: ltnW.
rewrite (eqsl_xoL k) T2K /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_xo V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2], oex_inv P a ks h z0} ->
        P (oexec_lt a ks t1 h z0) -> P (oexec_le a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_le (eqsl_uoxx T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `[t1, t2] by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `[t1, t2]): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_xx: (K)=>// [Ks T1K T2K].
suff {IH U K}-> : ks1 = &=ks `[t1, k[ by rewrite -eqsl_uoxo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last by apply/andP.
rewrite eqsl_xxL T2K Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_xx V R (P : R -> Prop) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `]t1, t2], oex_inv P a ks h z0} ->
        P (oexec_le a ks t1 h z0) -> P (oexec_le a ks t2 h z0).
Proof.
move=>U T IH P0; rewrite /oexec_le (eqsl_uxox T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `]t1, t2] by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]t1, t2]): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_ox: (K)=>// [Ks T1K T2K].
suff {IH U K}-> : ks1 = &=ks `]t1, k[ by rewrite -eqsl_uxoo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last by apply/andP.
rewrite eqsl_xxL T2K Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Arguments oex_ox [V R] P [a ks h t1 t2 z0].
Arguments oex_oo [V R] P [a ks h t1 t2 z0].
Arguments oex_xo [V R] P [a ks h t1 t2 z0].
Arguments oex_xx [V R] P [a ks h t1 t2 z0].

(* one-sided intervals *)

Lemma oex_ux V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `]t,+oo[, oex_inv P a ks h z0} ->
        P (oexec_le a ks t h z0) -> P (oevalv a ks h z0).
Proof.
move=>U IH P0; rewrite (eqsl_uxou ks t) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `]t, +oo[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]t, +oo[): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_ou: (K)=>// [Ks TK].
suff {IH U K}-> : ks1 = &=ks `]t, k[ by rewrite -eqsl_uxoo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last by apply/andP.
rewrite eqsl_xuL Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_uo V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `[t,+oo[, oex_inv P a ks h z0} ->
        P (oexec_lt a ks t h z0) -> P (oevalv a ks h z0).
Proof.
move=>U IH P0; rewrite (eqsl_uoxu ks t) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `[t, +oo[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `[t, +oo[): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_xu: (K)=>// [Ks TK].
suff {IH U K}-> : ks1 = &=ks `[t, k[ by rewrite -eqsl_uoxo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last by apply/andP.
rewrite eqsl_xuL Ks => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_xu V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t], oex_inv P a ks h z0} ->
        P z0 -> P (oexec_le a ks t h z0).
Proof.
move=>U IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have K : k \in &=ks `]-oo, t] by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]-oo, t]): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_ux: (K)=>// [Ks TK].
suff {IH U K}-> : ks1 = &=ks `]-oo, k[ by apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) //=.
rewrite eqsl_xxL TK Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_ou V R (P : R -> Prop) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t[, oex_inv P a ks h z0} ->
        P z0 -> P (oexec_lt a ks t h z0).
Proof.
move=>U IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have K : k \in &=ks `]-oo, t[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]-oo, t[): U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_uo: (K)=>// [Ks TK].
suff {IH U K}-> : ks1 = &=ks `]-oo, k[ by apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=;
  last by rewrite lteBSide /= leEnat; apply: ltnW.
rewrite eqsl_xoL TK => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
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
have K : k \in ks by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move: U.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
suff -> : ks1 = &=ks `]-oo, k[ by apply: IH.
move: Eh; rewrite {1}(eqsl_uxou ks k) eqsl_uxR K -cats1 -catA /= => Eh.
by rewrite (cat_cancel _ _ Eh) //=; apply: eqsliceRO_notin.
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
        {in &=ks `]t1, t2[, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t2 h z0) = f (oexec_le a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_le a ks t1 h z0).
by apply: (oex_ox P) T _ _=>// x S v K E ; rewrite /P -E; apply: H.
Qed.

Lemma oexF_oo V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2[, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t2 h z0) = f (oexec_lt a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_lt a ks t1 h z0).
by apply: (oex_oo P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xo V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t2 h z0) = f (oexec_lt a ks t1 h z0).
Proof.
move=>U T H; pose P := fun x => f x = f (oexec_lt a ks t1 h z0).
by apply: (oex_xo P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xx V R X (f : R -> X) a ks (h : natmap V) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `]t1, t2], oexF_inv f a ks h z0} ->
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
        {in &=ks `]t, +oo[, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f (oexec_le a ks t h z0).
Proof.
move=>U H; pose P := fun x => f x = f (oexec_le a ks t h z0).
by apply: (oex_ux P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_uo V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `[t, +oo[, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f (oexec_lt a ks t h z0).
Proof.
move=>U H; pose P := fun x => f x = f (oexec_lt a ks t h z0).
by apply: (oex_uo P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xu V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t h z0) = f z0.
Proof.
move=>U H; pose P := fun x => f x = f z0.
by apply: (oex_xu P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_ou V R X (f : R -> X) a ks (h : natmap V) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t[, oexF_inv f a ks h z0} ->
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
        t1 \in ks -> (t1, v) \In h ->
        oevalv a ks h z0 =
        oevalv a (&=ks `]t1, +oo[) h (a (oexec_lt a ks t1 h z0) v).
Proof.
move=>D H; rewrite {1}(eqsl_uoxu ks t1) oev_cat.
by rewrite eqsl_xuL D /=; move/In_find: H=>->.
Qed.

Arguments oev2_split [V R a t1 v h ks z0] _ _.

Lemma oex2_split V R a t1 t2 v (h : natmap V) ks (z0 : R) :
        t1 <[ks] t2 -> (t1, v) \In h ->
        oexec_lt a ks t2 h z0 =
        oevalv a (&=ks `]t1, t2[) h (a (oexec_lt a ks t1 h z0) v).
Proof.
move=>T H; rewrite /oexec_lt.
rewrite (eqsl_uoxo (sltW T)) oev_cat eqsl_xoL T /=.
by move/In_find: H=>->.
Qed.

Arguments oex2_split [V R a t1 t2 v h ks z0] _ _.

(* we frequently iterate oex2_split, so the following saves verbiage *)
Lemma oex3_split V R a t1 t2 t3 v1 v2 (h : natmap V) ks (z0 : R) :
        t1 <[ks] t2 -> (t1, v1) \In h ->
        t2 <[ks] t3 -> (t2, v2) \In h ->
        oexec_lt a ks t3 h z0 =
        oevalv a (&=ks `]t2, t3[) h
                 (a (oevalv a (&=ks `]t1, t2[) h
                    (a (oexec_lt a ks t1 h z0) v1))
                 v2).
Proof.
move=>T1 H1 T2 H2.
by rewrite (oex2_split T2 H2) (oex2_split T1 H1).
Qed.

Arguments oex3_split [V R a t1 t2 t3 v1 v2 h ks z0] _ _ _ _.

(******************************************)
(* Interaction of consec with oexlt/oexle *)
(******************************************)

Lemma oexlt_consec V R a ks t1 t2 (h : natmap V) (z0 : R) :
        uniq ks ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 = oexec_le a ks t1 h z0.
Proof.
move=>U C; apply: (oexF_ox id)=>//; first by apply: consec_slt.
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
- by rewrite mem_cat !inE eqxx !orbT.
by exists x1, x2.
Qed.

Lemma oexlt_consec_in V R a t1 t2 v (h : natmap V) ks (z0 : R) :
        uniq ks ->
        (t1, v) \In h ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 = a (oexec_lt a ks t1 h z0) v.
Proof.
move=>U H C; move/slt_memE: (consec_slt C)=>T.
by rewrite (oexlt_consec U C) (oexleE T H).
Qed.

Lemma oexlt_consec_fst V R a t (h : natmap V) k ks (z0 : R) :
        uniq (k::ks) -> k \notin dom h -> t \in k::ks ->
        consec (k::ks) k t ->
        oexec_lt a (k::ks) t h z0 = z0.
Proof.
move=>U K T C; case/(consecP_split _ U T): C=>xs1 [xs2] X.
case: xs1 X U {T}=>[|x xs1]; last first.
- by case=>->-> /=; rewrite mem_cat inE eqxx !orbT.
case=>->{ks}; rewrite /= inE negb_or -andbA; case/and4P=>U1 U2 U3 U4.
rewrite oexlt_cons_notin ?inE 1?negb_or ?(eq_sym t) ?U1 ?U2 //.
by rewrite oexlt_cons_same.
Qed.

Lemma oexlt_consec_find V R a t1 t2 (h : natmap V) ks (z0 : R) :
        uniq ks ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 =
        if find t1 h is Some e
          then a (oexec_lt a ks t1 h z0) e
          else oexec_lt a ks t1 h z0.
Proof.
move=>U C; rewrite (oexlt_consec U C).
case E : (find t1 h)=>[e|]; first by move/In_find: E=>/(oexleE (consec_mem C)) ->.
by rewrite oexleNE // orbC; move/In_findN: E=>->.
Qed.

Arguments oexlt_consec_find [V R a t1 t2 h ks z0].



(* The lemmas past this point are currently used for some examples, *)
(* but will be deprecated and removed in future releases *)

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

Definition last_atval v h := atval v (last_key h) h.

Lemma lastatval0 v : last_atval v Unit = v.
Proof. by rewrite /last_atval /atval lastkey0 find0E. Qed.

Lemma lastatvalPt v p x : p != 0 -> last_atval v (p \-> x) = x.2.
Proof.
by move=>V; rewrite /last_atval /atval lastkeyPt // findPt /= V.
Qed.

Lemma lastatval_fresh v x h :
        valid h -> last_atval v (fresh h \-> x \+ h) = x.2.
Proof.
by move=>V; rewrite /last_atval /atval lastkey_fresh // findPtUn // valid_fresh.
Qed.

Lemma lastatvalUn v h1 h2 :
        last_atval v (h1 \+ h2) =
        if valid (h1 \+ h2) then
          if last_key h1 < last_key h2 then last_atval v h2 else last_atval v h1
        else v.
Proof.
rewrite /last_atval /atval lastkeyUn maxnC /maxn.
case: ifP; last by move/negbT/invalidE=>->; rewrite find_undef.
case: (ltngtP (last_key h1) (last_key h2)) => N V.
- by rewrite findUnR // (dom_lastkeyE N).
- by rewrite findUnL // (dom_lastkeyE N).
by rewrite !(lastkeyUn0 V N) unitL lastkey0 find0E.
Qed.

Lemma lastatval_freshUn v x h1 h2 :
        valid h1 -> [pcm h2 <= h1] ->
        last_atval v (fresh h1 \-> x \+ h2) = x.2.
Proof.
move=>V H; rewrite /last_atval /atval.
rewrite lastkey_freshUn // findPtUn // valid_freshUn //.
by case: H V=>h -> /validL.
Qed.

Lemma lastatval_indom v h :
        last_atval v h <> v -> last_key h \in dom h.
Proof. by rewrite /last_atval /atval; case: dom_find=>// ->. Qed.

End AtVal.

(* in case A = bool *)
Lemma lastatval_indomb h :
        last_atval false h -> last_key h \in dom h.
Proof. by move=>H; apply: (lastatval_indom (v:=false)); rewrite H. Qed.

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
        continuous v h /\ last_atval v h = x.1.
Proof.
rewrite -(valid_fresh x (leqnn _))=>V; split; last first.
- case=>C H k y; rewrite !findPtUn2 // eqSS; case: ltngtP=>N.
  - by rewrite ltn_eqF; [apply: C | apply: (ltn_trans N _)].
  - by move/find_some /dom_ordfresh /(ltn_trans N); rewrite ltnn.
  by case=><-; rewrite N ltn_eqF.
move=>C; split; last first.
- move: (C (last_key h) x).
  by rewrite !findPtUn2 // eqxx ltn_eqF //; apply.
move=>k w; case: (ltnP k (last_key h))=>N; last first.
- by move/find_some /dom_ordfresh /(leq_ltn_trans N); rewrite ltnn.
by move: (C k w); rewrite !findPtUn2 // eqSS !ltn_eqF // (ltn_trans N _).
Qed.

Lemma cn_sub v h x y k :
        valid (k.+1 \-> (x, y) \+ h) -> continuous v (k.+1 \-> (x, y) \+ h) ->
        oapp snd v (find k h) = x.
Proof.
by move=>V /(_ k (x, y)); rewrite !findPtUn2 // eqxx ltn_eqF //; apply.
Qed.

End Continuous.

Arguments cn_fresh [A][v][h][x] _.

(* Complete natmaps with binary range *)

Section Complete.
Variable A : Type.
Implicit Type h : natmap (A * A).

Definition complete v0 h vn :=
  [/\ valid h, gapless h, continuous v0 h & last_atval v0 h = vn].

Lemma cm_valid v0 h vn : complete v0 h vn -> valid h.
Proof. by case. Qed.

Lemma cm0 v : complete v Unit v.
Proof. by split=>//; [apply: gp0 | apply: cn0 | rewrite lastatval0]. Qed.

Lemma cm_fresh v0 vn h x :
        complete v0 (fresh h \-> x \+ h) vn <-> vn = x.2 /\ complete v0 h x.1.
Proof.
split.
- by case=>/validR V /gp_fresh G /(cn_fresh V) []; rewrite lastatval_fresh.
case=>-> [V] /(gp_fresh x) G C E; split=>//;
by [rewrite valid_fresh | apply/(cn_fresh V) | rewrite lastatval_fresh].
Qed.

Lemma cmPtUn v0 vn h k x :
        complete v0 (k \-> x \+ h) vn -> last_key h < k -> k = fresh h.
Proof. by case=>V /(gpPtUn V). Qed.

Lemma cmPt v0 vn k x : complete v0 (k \-> x) vn -> k = 1 /\ x = (v0, vn).
Proof.
case; rewrite validPt; case: k=>//= k _ /(_ 1).
rewrite lastkeyPt //= domPt inE /= => /(_ (erefl _))/eqP ->.
move/(_ 0 x); rewrite findPt findPt2 /= => -> //.
by rewrite /last_atval lastkeyPt // /atval findPt /= => <-; case: x.
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

Lemma lastkey_umfilt_leq A (h : natmap A) t : last_key (um_filterk (leq^~ t) h) <= t.
Proof.
case V : (valid h); last first.
- by move/negbT/invalidE: V=>->; rewrite umfilt_undef lastkey_undef.
have V' : valid (um_filterk (leq^~ t) h) by rewrite valid_umfilt.
case E : (unitb (um_filterk (leq^~ t) h)).
- by move/unitbP: E=>->; rewrite lastkey0.
by case/dom_umfilt: (dom_lastkey V' (negbT E))=>v [].
Qed.

Lemma lastkey_umfilt_dom A (h : natmap A) t :
        last_key (um_filterk (leq^~ t) h) <= last_key h.
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
by rewrite domPtUn inE V eqxx.
Qed.

Lemma umfilt_le_split A (h : natmap A) t1 t2 :
        t1 <= t2 ->
        um_filter (le t2) h =
        um_filter (le t1) h \+ um_filter [pts k _ | t1 < k <= t2] h.
Proof.
move=>T; rewrite -umfilt_dpredU; last first.
- by case=>x y /= N; rewrite negb_and -leqNgt N.
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
rewrite (In_eta H) umfiltPtUn -(In_eta H) /= subX // W !leqnn /=.
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
  move/eq_in_umfilt=>/(_ (t2, v2) T2) /=.
  by rewrite leqnn leqn0 eq_sym=>/eqP.
case/orP=>[/eqP ->|/In_domX [v2 T2] L].
- move/eq_in_umfilt=>/(_ (t1, v1) T1) /=.
  by rewrite leqnn leqn0=>/esym/eqP.
move/eq_in_umfilt: (L)=>/(_ (t1, v1) T1).
move/eq_in_umfilt: (L)=>/(_ (t2, v2) T2) /=.
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
        eval a [pts k _ | t1 < k <= t2] h (eval a (le t1) h z0).
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
rewrite In_umfilt; split; last by move/InPt =>[[->->]].
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
- by rewrite eval_umfilt umfiltPtUn valid_fresh // V ltnNge H -eval_umfilt.
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
- by rewrite eval_umfilt umfiltPtUn valid_fresh // V ltnNge H -eval_umfilt.
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
- by rewrite -!umcnt_umfilt umfiltPtUn valid_fresh // V ltnNge H.
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
Variables (V R : Type).

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
move=>G W D1 D2 P E1; rewrite evalUn ?W // in E1; last first.
- move=>x y /D1 X1; rewrite domPtUn inE (validR W).
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
rewrite eval_umfilt (umfilt_le_split h K2) evalUn ?(validAL W1) //; last first.
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
