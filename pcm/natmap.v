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
From fcsl Require Import options prelude pred finmap rtc.
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
        omap a (k \-> v \+ h) =
        (if a (k, v) is Some v' then
         k \-> v' \+ omap a h else omap a h) :> natmap V'.
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
        k < fresh h <= t ->
        (k, x) \In t \-> e \+ h -> (k, x) \In h.
Proof.
move=>/andP [N F] H; have W : valid (t \-> e \+ h).
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
        um_filter p (k \-> v \+ h) =
        if p (k, v) then k \-> v \+ um_filter p h else um_filter p h.
Proof.
case W : (valid h).
- by move=>H; rewrite umfiltPtUn valid_fresh // W.
move/negbT/invalidE: W=>->.
by case: ifP; rewrite join_undef umfilt_undef // join_undef.
Qed.

Lemma fresh_lt V (h : natmap V) x :
        fresh h <= x ->
        um_filterk (ltn^~ x) h = h.
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

End OmapFunNatmap.

(* in many proofs, rewriting by the following 3 lemmas discharges the sideconditions *)
(* so we git it a name *)
Definition freshX := (fresh_omfT, valid_omf, ordfresh_dom).

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


(***********************************)
(***********************************)
(* Sequence-induced ordering       *)
(* definition and basic properties *)
(***********************************)
(***********************************)

(* x <[ks] y if x appears to the left of y in the sequence ks *)

(* It turns out it's useful to have 0 <[ks] x, for every x. *)
(* Basically, we use these orderings for reasoning about *)
(* timestamps in histories, and we always keep the null timestamp *)
(* to stand for the initialization step *)
(* That said, the null timestamp is never in any history as *)
(* the initialization step is implicit *)

Definition seq_le (ks : seq nat) (t1 t2 : nat) :=
  index t1 ks <= index t2 ks.

Definition seq_lt (ks : seq nat) (t1 t2 : nat) :=
  index t1 ks < index t2 ks.

Notation "t1 '<=[' ks ] t2" := (seq_le ks t1 t2)
  (at level 10, format "t1  '<=[' ks ]  t2").

Notation "t1 '<[' ks ] t2" := (seq_lt ks t1 t2)
  (at level 10, format "t1  '<[' ks ]  t2").

Lemma sle_refl ks t : t <=[ks] t.
Proof. by rewrite /seq_le. Qed.

#[export]
Hint Resolve sle_refl : core.


(* transfer properties of sequence ordering *)

Lemma ole_eqVlt ks t1 t2 :
        t1 \in ks \/ t2 \in ks ->
        t1 <=[ks] t2 = (t1 == t2) || (t1 <[ks] t2).
Proof.
move=>H; rewrite /seq_lt /seq_le leq_eqVlt /=.
case: (t1 =P t2)=>[->|N]; first by rewrite eq_refl.
case: eqP=>//; case: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

Lemma olt_neqAle ks t1 t2 :
        t1 \in ks \/ t2 \in ks ->
        t1 <[ks] t2 = (t1 != t2) && (t1 <=[ks] t2).
Proof.
move=>H.
rewrite /seq_lt /seq_le ltn_neqAle.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

Lemma oltNge ks t1 t2 : t1 <[ks] t2 = ~~ t2 <=[ks] t1.
Proof. by rewrite /seq_lt /seq_le ltnNge. Qed.

Lemma oleNgt ks t1 t2 : t1 <=[ks] t2 = ~~ t2 <[ks] t1.
Proof. by rewrite oltNge negbK. Qed.

(* order properties of the sequence orderings *)

Lemma olt_irr x ks : x <[ks] x = false.
Proof. by rewrite /seq_lt ltnn. Qed.

Lemma olt_neq x y ks : x <[ks] y -> x != y.
Proof. by case: eqP=>// ->; rewrite olt_irr. Qed.

Lemma olt_antisym ks : antisymmetric (seq_lt ks).
Proof. by move=>x y; rewrite /seq_lt; case: ltngtP. Qed.

Lemma olt_trans ks : transitive (seq_lt ks).
Proof. by move=>x y z; apply: ltn_trans. Qed.

Lemma olt_total ks : {in ks &, total (fun x y => (x == y) || seq_lt ks x y)}.
Proof.
rewrite /seq_lt=>x y K1 _.
case: ltngtP=>//; rewrite ?orbT ?orbF //.
by move/index_inj=>-> //; rewrite eq_refl.
Qed.

Lemma ole_refl ks : reflexive (seq_le ks).
Proof. by move=>x; rewrite /seq_le leqnn. Qed.

Lemma ole_antisym ks : {in ks &, antisymmetric (seq_le ks)}.
Proof. by rewrite /seq_le=>x y K _; case: ltngtP=>// /index_inj ->. Qed.

Lemma ole_trans ks : transitive (seq_le ks).
Proof. by move=>x y z; apply: leq_trans. Qed.

Lemma ole_total ks : total (seq_le ks).
Proof. by rewrite /seq_le=>x y; case: ltngtP. Qed.

Lemma ole_olt_trans ks t1 t2 t3 :
        t1 <=[ks] t2 -> t2 <[ks] t3 -> t1 <[ks] t3.
Proof. by apply: leq_ltn_trans. Qed.

Lemma olt_ole_trans ks t1 t2 t3 :
        t1 <[ks] t2 -> t2 <=[ks] t3 -> t1 <[ks] t3.
Proof. by apply: leq_trans. Qed.

Lemma oltW ks t1 t2 : t1 <[ks] t2 -> t1 <=[ks] t2.
Proof. by apply: ltnW. Qed.

Lemma olt_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <[ks1] t = k <[ks2] t.
Proof. by move=>S U T K; apply/idP/idP=>/(index_subseq S U T K). Qed.

Lemma ole_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <=[ks1] t = k <=[ks2] t.
Proof. by move=>S U T K; rewrite !oleNgt (olt_subseq S U K T). Qed.

(* membership properties of the sequence orderings *)

Lemma olt_memI x y ks : x \in ks -> y \notin ks -> x <[ks] y.
Proof. by move=>X /index_memN E; rewrite /seq_lt E index_mem. Qed.

Lemma ole_memI x y ks : y \notin ks -> x <=[ks] y.
Proof. by move/index_memN=>E; rewrite /seq_le E index_size. Qed.

Lemma olt_memE x y ks : x <[ks] y -> x \in ks.
Proof. by rewrite -index_mem=>/leq_trans; apply; rewrite index_size. Qed.

Lemma ole_memE x y ks : x <=[ks] y -> y \in ks -> x \in ks.
Proof. by move=>H; rewrite -!index_mem; apply: leq_ltn_trans H. Qed.

(* sequence orderings and constructors *)

Lemma olt_nil x y : x <[Nil nat] y = false. Proof. by []. Qed.
Lemma ole_nil x y : x <=[Nil nat] y. Proof. by []. Qed.

(* cons *)

Lemma olt_cons x y k ks :
        x <[k :: ks] y = (y != k) && ((x == k) || (x <[ks] y)).
Proof. by rewrite /seq_lt /= !(eq_sym k); case: eqP; case: eqP. Qed.

Lemma ole_cons x y k ks :
        x <=[k :: ks] y = (x == k) || (y != k) && x <=[ks] y.
Proof. by rewrite oleNgt olt_cons negb_and negbK negb_or -oleNgt. Qed.

Lemma oltL x y ks : x <[x :: ks] y = (y != x).
Proof. by rewrite olt_cons eq_refl andbT. Qed.

Lemma oleL x y ks : x <=[x :: ks] y.
Proof. by rewrite ole_cons eq_refl. Qed.

Lemma oltR x y ks : x <[y :: ks] y = false.
Proof. by rewrite oltNge oleL. Qed.

Lemma oleR x y ks : x <=[y :: ks] y = (y == x).
Proof. by rewrite oleNgt oltL negbK. Qed.

(* sequence orderings and last *)

Lemma ole_last x k ks :
        uniq (k :: ks) -> x \in ks -> x <=[ks] (last k ks).
Proof. by apply: index_last_mono. Qed.

Lemma ole_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks -> x <=[k::ks] (last k ks).
Proof.
move=>U; move: (U)=>/= /andP [U1 U2].
rewrite inE ole_cons; case: eqP=>//= /eqP Nxk K.
by rewrite (last_notin K) //= ole_last.
Qed.

Lemma olt_last x k ks :
        uniq (k :: ks) -> x \in ks -> last k ks != x -> x <[ks] (last k ks).
Proof.
move=>U X N; move: (ole_last U X); rewrite ole_eqVlt; last by left.
by rewrite eq_sym (negbTE N).
Qed.

Lemma olt_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks ->
        last k ks != x -> x <[k::ks] (last k ks).
Proof.
move=>U X N; rewrite olt_neqAle; last by right; apply: mem_last.
by rewrite eq_sym N ole_last_cons.
Qed.

(* sequence orderings and rcons *)

Lemma olt_rcons x y k ks :
        x <[rcons ks k] y = if y \in ks then x <[ks] y
                            else (x \in ks) || (k != y) && (k == x).
Proof.
rewrite /seq_lt !index_rcons.
case X: (x \in ks); case Y: (y \in ks)=>//=.
- by case: eqP; [rewrite index_mem | rewrite ltnS index_size].
- move/negbT/index_memN: X=>X; rewrite [LHS]ltnNge [RHS]ltnNge.
  rewrite X index_size /=.
  case: eqP=>//; first by rewrite index_size.
  by rewrite ltnW // ltnS index_size.
rewrite !(eq_sym k).
case: eqP; case: eqP=>//=.
- by rewrite ltnn.
- by rewrite ltnS leqnn.
- by rewrite ltnNge ltnW.
by rewrite ltnn.
Qed.

Lemma ole_rcons x y k ks :
        x <=[rcons ks k] y = if x \in ks then x <=[ks] y
                             else (y \notin ks) && ((k == x) || (k != y)).
Proof.
by rewrite !oleNgt olt_rcons; case: ifP=>//; rewrite negb_or negb_and negbK.
Qed.

(* some shortcuts for olt/ole_rcons *)

Lemma olt_rconsI x y k ks : x <[ks] y -> x <[rcons ks k] y.
Proof. by move=>H; rewrite olt_rcons H (olt_memE H) if_same. Qed.

Lemma ole_rconsI x y k ks : k != y -> x <=[ks] y -> x <=[rcons ks k] y.
Proof.
move=>N H; rewrite ole_rcons H N orbT andbT.
case: ifP=>// K; apply: contraFT K.
by rewrite negbK; apply: ole_memE H.
Qed.

Lemma olt_rcons_in x y k ks :
        x \in ks -> x <[rcons ks k] y = x <[ks] y.
Proof.
move=>H; rewrite olt_rcons H /=; case: ifP=>// K.
by apply/esym; apply: olt_memI=>//; rewrite K.
Qed.

Lemma ole_rcons_in x y k ks :
        x \in ks -> x <=[rcons ks k] y = x <=[ks] y.
Proof. by move=>X; rewrite ole_rcons X. Qed.

Lemma olt_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <[rcons ks k1] y = x <[rcons ks k2] y.
Proof. by rewrite !olt_rcons=>/orP [] ->. Qed.

Lemma ole_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <=[rcons ks k1] y = x <=[rcons ks k2] y.
Proof. by rewrite !ole_rcons=>/orP [] ->. Qed.

Lemma olt_rconsR ks x k : x <[rcons ks k] k -> x \in ks.
Proof. by rewrite olt_rcons eq_refl orbF; case: ifP=>[_ /olt_memE|]. Qed.

Lemma ole_rconsR ks x k : x <=[rcons ks k] k -> x \in rcons ks k.
Proof.
rewrite ole_rcons eq_refl orbF mem_rcons inE.
case X: (x \in ks); first by rewrite orbT.
by rewrite orbF eq_sym; case/andP.
Qed.

(* sequence orderings and concatenation *)
Lemma ole_cat ks1 ks2 x y :
        x <=[ks1++ks2] y = if x \in ks1 then x <=[ks1] y
                           else (y \notin ks1) && x <=[ks2] y.
Proof.
rewrite /seq_le !index_cat.
case X: (x \in ks1); case Y: (y \in ks1)=>//=.
- move/negbT/index_memN: Y=>Y.
  by rewrite Y index_size ltnW // ltn_addr // index_mem.
- rewrite -index_mem in Y.
  apply/negP=>H; move/(leq_ltn_trans H): Y.
  by rewrite ltnNge leq_addr.
by rewrite leq_add2l.
Qed.

Lemma olt_cat ks1 ks2 x y :
        x <[ks1++ks2] y = if y \in ks1 then x <[ks1] y
                          else (x \in ks1) || x <[ks2] y.
Proof. by rewrite !oltNge ole_cat; case: ifP=>//; rewrite negb_and negbK. Qed.

(* shortcuts *)

Lemma olt_catL ks1 ks2 x y : x <[ks1] y -> x <[ks1++ks2] y.
Proof. by move=>H; rewrite olt_cat H (olt_memE H) if_same. Qed.

Lemma olt_splitR x y ks1 ks2 : y != x -> y \notin ks1 -> x <[ks1++x::ks2] y.
Proof.
by move=>N Y; rewrite olt_cat olt_cons eq_refl andbT (negbTE Y) N orbT.
Qed.

Lemma ole_splitR x y ks1 ks2 : y \notin ks1 -> x <=[ks1++x::ks2] y.
Proof.
move=>Y; rewrite ole_eqVlt; last first.
- by left; rewrite mem_cat inE eq_refl orbT.
by case: eqP=>[|/eqP N] //=; rewrite (olt_splitR _ _ Y) // eq_sym.
Qed.

(* the other direction of olt_splitR, further strenghtened *)
(* with an additional fact that x \notin ks1 *)
(* by picking a split with the first occurrence of x *)
(* in fact, we can have both directions here, so we prove a reflect lemma *)
(* but it should really only be used in the direction x <[ks] y -> .. *)
(* because in the other direction olt_splitR is already stronger. *)
Lemma olt_splitL (ks : seq nat) x y :
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2, x != y,
                                     x \notin ks1 & y \notin ks1])
                (x <[ks] y).
Proof.
case H : (x <[ks] y); constructor; last first.
- case=>ks1 [ks2][E N _ Y]; move/negP: H; apply.
  by rewrite E; apply: olt_splitR Y; rewrite eq_sym.
have : x \in ks by rewrite -index_mem (leq_trans H _) // index_size.
case/in_split=>ks1 [ks2][E X]; exists ks1, ks2.
rewrite /seq_lt {ks}E !index_cat /= eq_refl in H *.
case: eqP H=>[->|/eqP N] /=; first by rewrite ltnn.
rewrite (negbTE X) addn0; case: ifP=>// _.
by rewrite ltnNge index_size.
Qed.

(* ditto for ole_split *)
Lemma ole_splitL (ks : seq nat) x y :
        x \in ks ->
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2,
                                     x \notin ks1 & y \notin ks1])
                (x <=[ks] y).
Proof.
move=>X; case H : (x <=[ks] y); constructor; last first.
- case=>ks1 [ks2][E _ N]; move/negP: H; apply.
  by rewrite E; apply: ole_splitR.
case/in_split: X=>ks1 [ks2][E X]; exists ks1, ks2; split=>//.
rewrite /seq_le {ks}E !index_cat /= eq_refl (negbTE X) addn0 in H.
by case: ifP H=>//; rewrite -index_mem; case: ltngtP.
Qed.

(* sequence orderings and filter *)

Lemma olt_filterL (p : pred nat) (ks : seq nat) (x y : nat) :
         (x \notin ks) || p x ->
         x <[ks] y -> x <[filter p ks] y.
Proof. by apply: index_filter_ltL. Qed.

Lemma ole_filterL (p : pred nat) (ks : seq nat) (x y : nat) :
        (x \notin ks) || p x ->
        x <=[ks] y -> x <=[filter p ks] y.
Proof. by apply: index_filter_leL. Qed.

Lemma olt_filterR (p : pred nat) (ks : seq nat) (x y : nat) :
        (y \notin ks) || p y ->
        x <[filter p ks] y -> x <[ks] y.
Proof. by apply: index_filter_ltR. Qed.

Lemma ole_filterR (p : pred nat) (ks : seq nat) (x y : nat) :
        (y \notin ks) || p y ->
        x <=[filter p ks] y -> x <=[ks] y.
Proof. by apply: index_filter_leR. Qed.

Lemma olt_filter (p : pred nat) (ks : seq nat) (x y : nat) :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <[filter p ks] y = x <[ks] y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: olt_filterR | apply: olt_filterL].
Qed.

Lemma ole_filter (p : pred nat) (ks : seq nat) (x y : nat) :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <=[filter p ks] y = x <=[ks] y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: ole_filterR | apply: ole_filterL].
Qed.

(* sequence orderings and sortedness *)

(* every list is sorted by its olt relation, assuming uniqeness *)
Lemma sorted_olt ks : uniq ks -> sorted (seq_lt ks) ks.
Proof.
case: ks=>//= k ks; elim: ks k=>[|k1 ks IH] k2 //=.
rewrite inE negb_or -andbA=>/and4P [N1 N2 N3 N4].
rewrite oltL eq_sym N1 /=.
have : path (seq_lt [:: k1 & ks]) k1 ks by apply: IH; rewrite N3 N4.
apply: (@sub_in_path _ (mem (k1::ks))); last by apply/allP.
move=>x y /=; rewrite !inE !olt_cons.
case/orP=>[/eqP ->{x}|X].
- rewrite (eq_sym k1 k2) (negbTE N1) /= eq_refl andbT.
  case/orP=>[/eqP ->|Y ->]; first by rewrite eq_refl.
  by case: eqP Y N2=>// ->->.
case/orP=>[/eqP ->|Y]; first by rewrite eq_refl.
case: eqP Y N3=>[->|/eqP N Y N3] //=.
case: eqP X N3=>[->->|/eqP M X K1] //= H.
by rewrite H orbT andbT; case: eqP Y N2=>// ->->.
Qed.

Lemma sorted_ole ks : uniq ks -> sorted (seq_le ks) ks.
Proof.
move=>U; apply: sub_sorted (sorted_olt U).
by move=>x y; rewrite /seq_lt/seq_le; case: ltngtP.
Qed.

(* olt/ole and sortedness under nats *)

Lemma olt_sorted ks x y :
        sorted ltn ks -> y \in ks -> x <[ks] y -> x < y.
Proof. by apply: sorted_index_ord ltn_trans. Qed.

Lemma ole_sorted ks x y :
        sorted ltn ks -> y \in ks -> x <=[ks] y -> x <= y.
Proof.
move=>S K; rewrite ole_eqVlt; last by right.
by case/orP=>[/eqP ->//|/(olt_sorted S K)/ltnW].
Qed.

Lemma olt_sortedE ks x y :
        sorted ltn ks ->
        x \in ks -> y \in ks ->
        x <[ks] y = (x < y).
Proof.
move=>S X Y; apply/idP/idP; first by apply: olt_sorted S Y.
by apply: (sorted_ord_index (leT:=ltn)) ltn_trans S X; apply: irr.
Qed.

Lemma ole_sortedE ks x y :
        sorted ltn ks ->
        x \in ks -> y \in ks ->
        x <=[ks] y = (x <= y).
Proof. by move=>S X Y; rewrite leqNgt oleNgt (olt_sortedE S Y X). Qed.

(* olt/ole under general sorted relations *)
Lemma olt_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <[ks] y -> ltT x y.
Proof. by apply: sorted_index_ord. Qed.

Lemma ole_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <=[ks] y -> (x == y) || ltT x y.
Proof.
move=>T S Y; rewrite ole_eqVlt; last by right.
by case/orP=>[->//|/(olt_sorted_lt T S Y) ->]; rewrite orbT.
Qed.

(* we can get the other direction as well *)
(* if we add antisymmetry, totality *)
(* and the condition that x \in ks *)
Lemma olt_sorted_ltE ltT ks x y :
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        {in ks &, total ltT} ->
        x \in ks -> y \in ks ->
        x <[ks] y = (x != y) && ltT x y.
Proof.
move=>As T S Tot X Y; apply/idP/idP.
- by case: eqP=>[->|/eqP N] /=; [rewrite olt_irr | apply: olt_sorted_lt].
by case/andP=>H K; apply: sorted_ord_index_leq K H.
Qed.

(* if we add antisymmetry and totality and t1 \in ks *)
Lemma ole_sorted_ltE ltT ks x y :
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        {in ks &, total ltT} ->
        x \in ks -> y \in ks ->
        x <=[ks] y = (x == y) || ltT x y.
Proof.
move=>As T Tot S X Y; rewrite ole_eqVlt; last by right.
by rewrite (olt_sorted_ltE As T Tot S X Y); case: eqP.
Qed.


(***********************************)
(***********************************)
(* Intervals of sequence orderings *)
(***********************************)
(***********************************)

(* helper take/drop properties *)

(* we need the uniqueness condition here because otherwise *)
(* the filter picks up all the occurrences of each element whose *)
(* first appearance is before the first appearance of t *)
Lemma olt_take ks t :
        uniq ks ->
        [seq x <- ks | x <[ks] t] = take (index t ks) ks.
Proof.
elim: ks=>[|k ks IH] //= /andP [K U].
rewrite oltL eq_sym; case: eqP K=>[-> K|/eqP H K] /=.
- rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx /=.
  by rewrite oltR.
congr cons; rewrite -IH //; apply: eq_in_filter=>x Kx.
by rewrite olt_cons eq_sym H /=; case: eqP Kx K=>//= ->->.
Qed.

Lemma ole_take ks t :
        uniq ks ->
        [seq x <- ks | x <=[ks] t] = take (index t ks).+1 ks.
Proof.
elim: ks=>[|k ks IH] //= /andP [K U].
rewrite oleL; congr cons; case: eqP K=>[-> K|/eqP H K].
- rewrite take0 -(filter_pred0 ks); apply: eq_in_filter=>x Kx /=.
  by rewrite oleR; by case: eqP Kx K=>// ->->.
rewrite -IH //; apply: eq_in_filter=>x Kx.
by rewrite ole_cons (eq_sym t k) H /=; case: eqP Kx K=>//= ->->.
Qed.

(* we also need uniqueness here because otherwise *)
(* the filter won't pick up those elements that appear after t *)
(* in the list, but whose first occurrence is before t *)
Lemma olt_drop ks t :
        uniq ks ->
        [seq x <- ks | t <[ks] x] = drop (index t ks).+1 ks.
Proof.
elim: ks=>[|k ks IH] //= /andP [K U].
rewrite oltR; case: eqP K=>[-> K|/eqP H K] /=.
- rewrite drop0 -{3}(filter_predT ks); apply: eq_in_filter=>x Kx.
  by rewrite oltL; case: eqP Kx K=>// ->->.
rewrite -IH //; apply: eq_in_filter=>x Kx.
by rewrite olt_cons (eq_sym t k) (negbTE H) /=; case: eqP Kx K=>// ->->.
Qed.

Lemma ole_drop ks t :
        uniq ks ->
        [seq x <- ks | t <=[ks] x] = drop (index t ks) ks.
Proof.
elim: ks=>[|k ks IH] //= /andP [K U].
rewrite oleR (eq_sym k t); case: eqP K=>[-> K|/eqP H K] /=.
- congr cons; rewrite -{3}(filter_predT ks).
  by apply: eq_in_filter=>x Kx; rewrite oleL.
rewrite -IH //; apply: eq_in_filter=>x Kx.
by rewrite ole_cons (negbTE H) /=; case: eqP Kx K=>// ->->.
Qed.

(* Abbreviations for the various filtered intervals *)

Definition sq_ole t ks := [seq x <- ks | x <=[ks] t].
Definition sq_olt t ks := [seq x <- ks | x  <[ks] t].
Definition ole_sq t ks := [seq x <- ks | t <=[ks] x].
Definition olt_sq t ks := [seq x <- ks | t  <[ks] x].

Notation "{ 'sqint' t ks ]" := (sq_ole t ks)
 (at level 1, t at next level, ks at next level,
  format "{ 'sqint'  t  ks ]") : fun_scope.
Notation "{ 'sqint' t ks |" := (sq_olt t ks)
 (at level 1, t at next level, ks at next level,
  format "{ 'sqint'  t  ks |") : fun_scope.
Notation "[ 'sqint' t ks }" := (ole_sq t ks)
 (at level 1, t at next level, ks at next level,
  format "[ 'sqint'  t  ks }") : fun_scope.
Notation "| 'sqint' t ks }" := (olt_sq t ks)
 (at level 1, t at next level, ks at next level,
  format "| 'sqint'  t  ks }") : fun_scope.

Definition sq_olele t1 t2 ks := [seq x <- ks | t1 <=[ks] x && x <=[ks] t2].
Definition sq_olelt t1 t2 ks := [seq x <- ks | t1 <=[ks] x && x  <[ks] t2].
Definition sq_oltle t1 t2 ks := [seq x <- ks | t1  <[ks] x && x <=[ks] t2].
Definition sq_oltlt t1 t2 ks := [seq x <- ks | t1  <[ks] x && x  <[ks] t2].

Notation "[ 'sqint' t1 t2 ks ]" := (sq_olele t1 t2 ks)
 (at level 1, t1 at next level, t2 at next level, ks at next level,
  format "[ 'sqint'  t1  t2  ks ]") : fun_scope.
Notation "[ 'sqint' t1 t2 ks |" := (sq_olelt t1 t2 ks)
 (at level 1, t1 at next level, t2 at next level, ks at next level,
  format "[ 'sqint'  t1  t2  ks |") : fun_scope.
Notation "| 'sqint' t1 t2 ks ]" := (sq_oltle t1 t2 ks)
 (at level 1, t1 at next level, t2 at next level, ks at next level,
  format "| 'sqint'  t1  t2  ks ]") : fun_scope.
Notation "| 'sqint' t1 t2 ks |" := (sq_oltlt t1 t2 ks)
 (at level 1, t1 at next level, t2 at next level, ks at next level,
  format "| 'sqint'  t1  t2  ks |") : fun_scope.

(* some basic transfer lemmas *)

(* the lemma name is derived out of brackes on the left interval *)
(* X = closed bracket, O = open bracket, i.e. | *)

Lemma sqoo_filterL t1 t2 xs :
        |sqint t1 t2 xs| = filter (fun x => t1 <[xs] x) {sqint t2 xs|.
Proof. by rewrite -filter_predI. Qed.

Lemma sqoo_filterR t1 t2 xs :
        |sqint t1 t2 xs| = filter (fun x => x <[xs] t2) |sqint t1 xs}.
Proof. by rewrite -filter_swap -filter_predI. Qed.

Lemma sqxo_filterL t1 t2 xs :
        [sqint t1 t2 xs| = filter (fun x => t1 <=[xs] x) {sqint t2 xs|.
Proof. by rewrite -filter_predI. Qed.

Lemma sqxo_filterR t1 t2 xs :
        [sqint t1 t2 xs| = filter (fun x => x <[xs] t2) [sqint t1 xs}.
Proof. by rewrite -filter_swap -filter_predI. Qed.

Lemma sqox_filterL t1 t2 xs :
        |sqint t1 t2 xs] = filter (fun x => t1 <[xs] x) {sqint t2 xs].
Proof. by rewrite -filter_predI. Qed.

Lemma sqox_filterR t1 t2 xs :
        |sqint t1 t2 xs] = filter (fun x => x <=[xs] t2) |sqint t1 xs}.
Proof. by rewrite -filter_swap -filter_predI. Qed.

Lemma sqxx_filterL t1 t2 xs :
        [sqint t1 t2 xs] = filter (fun x => t1 <=[xs] x) {sqint t2 xs].
Proof. by rewrite -filter_predI. Qed.

Lemma sqxx_filterR t1 t2 xs :
        [sqint t1 t2 xs] = filter (fun x => x <=[xs] t2) [sqint t1 xs}.
Proof. by rewrite -filter_swap -filter_predI. Qed.

(* We can also nest the interval constructions; not sure *)
(* how useful these lemmas are, but let's have them. Each of them *)
(* requires a precondition ordering t1 and t2 in xs *)

(* the name is derived out of the brackes on the right side of equations *)
(* U = brace, X = closed bracket, O = open bracket, i.e. | *)

Lemma sq_ouou t1 t2 xs :
        t1 <[xs] t2 ->
        |sqint t1 t2 xs| = |sqint t1 ({sqint t2 xs|)}.
Proof.
move=>T12; rewrite /olt_sq -filter_predI; apply: eq_in_filter=>k K /=.
case Tk2 : (k <[xs] t2)=>//=; last by rewrite !andbF.
by rewrite andbT (olt_filter (p:=fun x => x <[xs] t2)) ?T12 ?Tk2 ?orbT ?andbT.
Qed.

Lemma sq_uouo t1 t2 xs :
        t1 <[xs] t2 ->
        |sqint t1 t2 xs| = {sqint t2 |sqint t1 xs}|.
Proof.
move=>T12; rewrite /sq_olt -filter_predI; apply: eq_in_filter=>k K /=.
case T1k : (t1 <[xs] k)=>//=; last by rewrite andbF.
by rewrite andbT (olt_filter (p:=fun x => t1 <[xs] x)) ?T1k ?T12 ?orbT.
Qed.

Lemma sq_xuou t1 t2 xs :
        t1 <[xs] t2 ->
        [sqint t1 t2 xs| = [sqint t1 ({sqint t2 xs|)}.
Proof.
move=>T12; rewrite /ole_sq -filter_predI; apply: eq_in_filter=>k K /=.
case Tk2 : (k <[xs] t2)=>//=; last by rewrite !andbF.
by rewrite andbT (ole_filter (p:=fun x => x <[xs] t2)) ?T12 ?Tk2 ?orbT ?andbT.
Qed.

Lemma sq_uxuo t1 t2 xs :
        t1 <=[xs] t2 ->
        [sqint t1 t2 xs| = {sqint t2 [sqint t1 xs}|.
Proof.
move=>T12; rewrite /sq_olt -filter_predI; apply: eq_in_filter=>k K /=.
case T1k : (t1 <=[xs] k)=>//=; last by rewrite andbF.
by rewrite andbT (olt_filter (p:=fun x => t1 <=[xs] x)) ?T1k ?T12 ?orbT.
Qed.

Lemma sq_ouxu t1 t2 xs :
        t1 <=[xs] t2 ->
        |sqint t1 t2 xs] = |sqint t1 ({sqint t2 xs])}.
Proof.
move=>T12; rewrite /olt_sq -filter_predI; apply: eq_in_filter=>k K /=.
case Tk2 : (k <=[xs] t2)=>//=; last by rewrite !andbF.
by rewrite andbT (olt_filter (p:=fun x => x <=[xs] t2)) ?T12 ?Tk2 ?orbT ?andbT.
Qed.

Lemma sq_uoux t1 t2 xs :
        t1 <[xs] t2 ->
        |sqint t1 t2 xs] = {sqint t2 |sqint t1 xs}].
Proof.
move=>T12; rewrite /sq_ole -filter_predI; apply: eq_in_filter=>k K /=.
case T1k : (t1 <[xs] k)=>//=; last by rewrite andbF.
by rewrite andbT (ole_filter (p:=fun x => t1 <[xs] x)) ?T1k ?T12 ?orbT.
Qed.

Lemma sq_xuxu t1 t2 xs :
        t1 <=[xs] t2 ->
        [sqint t1 t2 xs] = [sqint t1 ({sqint t2 xs])}.
Proof.
move=>T12; rewrite /ole_sq -filter_predI; apply: eq_in_filter=>k K /=.
case Tk2 : (k <=[xs] t2)=>//=; last by rewrite !andbF.
by rewrite andbT (ole_filter (p:=fun x => x <=[xs] t2)) ?T12 ?Tk2 ?orbT ?andbT.
Qed.

Lemma sq_uxux t1 t2 xs :
        t1 <=[xs] t2 ->
        [sqint t1 t2 xs] = {sqint t2 [sqint t1 xs}].
Proof.
move=>T12; rewrite /sq_ole -filter_predI; apply: eq_in_filter=>k K /=.
case T1k : (t1 <=[xs] k)=>//=; last by rewrite andbF.
by rewrite andbT (ole_filter (p:=fun x => t1 <=[xs] x)) ?T1k ?T12 ?orbT.
Qed.

(* splitting the whole list *)

Lemma sq_uxou ks t : uniq ks -> ks = {sqint t ks] ++ |sqint t ks}.
Proof.
by move=>U; rewrite /sq_ole /olt_sq ole_take // olt_drop // cat_take_drop.
Qed.

Lemma sq_uoxu ks t : uniq ks -> ks = {sqint t ks| ++ [sqint t ks}.
Proof.
move=>U.
by rewrite /sq_olt /ole_sq olt_take // ole_drop // cat_take_drop.
Qed.

(*
Lemma sq_uoou ks t :
        uniq (0::ks) -> t \in ks ->
        ks = {sqint t ks| ++ t :: |sqint t ks}.
Proof.
move=>U K.
have Nt : t != 0 by case: eqP U K=>[->|/eqP] //= /andP [/negbTE ->].
case/splitP: K U=>p1 p2 /= U.
have Np1 : t \notin p1.
- by case/andP: U=>_; rewrite cat_uniq rcons_uniq=>/and3P [] /andP [].
rewrite /sq_olt /olt_sq olt_take // olt_drop //= eq_sym (negbTE Nt) /=.
rewrite index_cat mem_rcons index_rcons inE eq_refl (negbTE Np1) /=.
rewrite take_cat drop_cat size_rcons ltnn ltnS leqnn subnn drop0.
by rewrite -cats1 /= take_cat ltnn subnn take0 cats0 -catA.
Qed.
*)

(* splitting one-sided intervals *)

(* the name is derived out of the brackes on the right side of equations *)
(* u = brace, x = closed bracket, o = open bracket, i.e. | *)
(* the 8 versions are: *)
(* sq_uxox: {0, t2] = {0, t1] + (t1, t2] *)
(* sq_uoxx: {0, t2] = {0, t1) + [t1, t2] *)
(* sq_uxoo: {0, t2) = {0, t1] + (t1, t2) *)
(* sq_uoxo: {0, t2) = {0, t1) + [t1, t2) *)
(* etc. *)

Lemma sq_uxox ks t1 t2 :
        uniq ks ->
        t1 <=[ks] t2 ->
        {sqint t2 ks] = {sqint t1 ks] ++ |sqint t1 t2 ks].
Proof.
move=>U T.
have E1 : {in ks, forall x, x <=[ks] t1 =
                            x <=[ks] t2 && x <=[ks] t1}.
- move=>x Kx; case E: (x <=[ks] t1)=>//=;
  by rewrite ?andbF // /seq_le (leq_trans E T).
have E2 : {in ks, forall x, t1 <[ks] x && x <=[ks] t2 =
                            x <=[ks] t2 && t1<[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite /sq_ole /sq_oltle.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite [in RHS]ole_take // olt_drop // cat_take_drop.
Qed.

Lemma sq_uoxx ks t1 t2 :
        uniq ks ->
        t1 <=[ks] t2 ->
        {sqint t2 ks] = {sqint t1 ks| ++ [sqint t1 t2 ks].
Proof.
move=>U T.
have E1 : {in ks, forall x, x <[ks] t1 =
                            x <=[ks] t2 && x <[ks] t1}.
- move=>x Kx; case E: (x <[ks] t1)=>//=;
  by rewrite ?andbF // /seq_le leq_eqVlt (leq_trans E T) orbT.
have E2 : {in ks, forall x, t1 <=[ks] x && x <=[ks] t2 =
                            x <=[ks] t2 && t1<=[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite /sq_ole /sq_olt /sq_olele.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite [in RHS]olt_take // ole_drop // cat_take_drop.
Qed.

(* the following split is special among the splits *)
(* because it requires t1 <[ks] t2 *)
(* i.e., it doesn't hold if t1 == t2 *)
(* The reason is that the left interval is open *)
(* but the first interal on the right is closed *)
Lemma sq_uxoo ks t1 t2 :
        uniq ks ->
        t1 <[ks] t2 ->
        {sqint t2 ks| = {sqint t1 ks] ++ |sqint t1 t2 ks|.
Proof.
move=>U T.
have E1 : {in ks, forall x, x <=[ks] t1 =
                            x <[ks] t2 && x <=[ks] t1}.
- move=>x Kx; case E: (x <=[ks] t1)=>//=;
  by rewrite ?andbF // /seq_lt (leq_ltn_trans E T).
have E2 : {in ks, forall x, t1 <[ks] x && x <[ks] t2 =
                            x <[ks] t2 && t1<[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite /sq_olt /sq_ole /sq_oltlt.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite ole_take // [in RHS]olt_drop // cat_take_drop.
Qed.

Lemma sq_uoxo ks t1 t2 :
        uniq ks ->
        t1 <=[ks] t2 ->
        {sqint t2 ks| = {sqint t1 ks| ++ [sqint t1 t2 ks|.
Proof.
move=>U T.
have E1 : {in ks, forall x, x <[ks] t1 =
                            x <[ks] t2 && x <[ks] t1}.
- move=>x Kx; case E: (x <[ks] t1)=>//=;
  by rewrite ?andbF // /seq_lt (leq_trans E T).
have E2 : {in ks, forall x, t1 <=[ks] x && x <[ks] t2 =
                            x <[ks] t2 && t1<=[ks] x}.
- by move=>x Kx; rewrite andbC.
rewrite /sq_olt /sq_olelt.
rewrite (eq_in_filter E1) (eq_in_filter E2) !filter_predI -filter_cat.
by rewrite [in RHS]olt_take // ole_drop // cat_take_drop.
Qed.

(***)

Lemma sq_xxou ks t1 t2 :
        uniq ks ->
        t1 <=[ks] t2 ->
        [sqint t1 ks} = [sqint t1 t2 ks] ++ |sqint t2 ks}.
Proof.
move=>U T; rewrite sqxx_filterR.
rewrite (_ : |sqint t2 ks} = filter (fun x => t2 <[ks] x) [sqint t1 ks}); last first.
- rewrite -filter_predI; apply: eq_in_filter=>x X /=.
  by case E : (t2 <[ks] x)=>//=; rewrite (oltW (ole_olt_trans T E)).
rewrite [in X in X ++ _]filter_swap [in X in _ ++ X]filter_swap -filter_cat.
by congr filter; apply: sq_uxou.
Qed.

Lemma sq_xoxu ks t1 t2 :
        uniq ks ->
        t1 <=[ks] t2 ->
        [sqint t1 ks} = [sqint t1 t2 ks| ++ [sqint t2 ks}.
Proof.
move=>U T; rewrite sqxo_filterR.
rewrite (_ : [sqint t2 ks} = filter (fun x => t2 <=[ks] x) [sqint t1 ks}); last first.
- rewrite -filter_predI; apply: eq_in_filter=>x X /=.
  by case E : (t2 <=[ks] x)=>//=; rewrite (ole_trans T E).
rewrite [in X in X ++ _]filter_swap [in X in _ ++ X]filter_swap -filter_cat.
by congr filter; apply: sq_uoxu.
Qed.

Lemma sq_oxou ks t1 t2 :
        uniq ks ->
        t1 <=[ks] t2 ->
        |sqint t1 ks} = |sqint t1 t2 ks] ++ |sqint t2 ks}.
Proof.
move=>U T; rewrite sqox_filterR.
rewrite (_ : |sqint t2 ks} = filter (fun x => t2 <[ks] x) |sqint t1 ks}); last first.
- rewrite -filter_predI; apply: eq_in_filter=>x X /=.
  by case E : (t2 <[ks] x)=>//=; rewrite (ole_olt_trans T E).
rewrite [in X in X ++ _]filter_swap [in X in _ ++ X]filter_swap -filter_cat.
by congr filter; apply: sq_uxou.
Qed.

Lemma sq_ooxu ks t1 t2 :
        uniq ks ->
        t1 <[ks] t2 ->
        |sqint t1 ks} = |sqint t1 t2 ks| ++ [sqint t2 ks}.
Proof.
move=>U T; rewrite sqoo_filterR.
rewrite (_ : [sqint t2 ks} = filter (fun x => t2 <=[ks] x) |sqint t1 ks}); last first.
- rewrite -filter_predI; apply: eq_in_filter=>x X /=.
  by case E : (t2 <=[ks] x)=>//=; rewrite (olt_ole_trans T E).
rewrite [in X in X ++ _]filter_swap [in X in _ ++ X]filter_swap -filter_cat.
by congr filter; apply: sq_uoxu.
Qed.

(* splitting two-sided intervals *)

Lemma sq_xoxx t1 t2 x ks :
        uniq ks ->
        x \in [sqint t1 t2 ks] ->
        [sqint t1 t2 ks] = [sqint t1 x ks| ++ [sqint x t2 ks].
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqxx_filterL (sq_uoxx U H2) filter_cat -sqxo_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(ole_trans H1).
Qed.

Lemma sq_xxox t1 t2 x ks :
        uniq ks ->
        x \in [sqint t1 t2 ks] ->
        [sqint t1 t2 ks] = [sqint t1 x ks] ++ |sqint x t2 ks].
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqxx_filterL (sq_uxox U H2) filter_cat -sqxx_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(ole_olt_trans H1)/oltW.
Qed.

Lemma sq_xxoo t1 t2 x ks :
        uniq ks ->
        x \in [sqint t1 t2 ks| ->
        [sqint t1 t2 ks| = [sqint t1 x ks] ++ |sqint x t2 ks|.
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqxo_filterL (sq_uxoo U H2) filter_cat -sqxx_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(ole_olt_trans H1)/oltW.
Qed.

Lemma sq_xoxo t1 t2 x ks :
        uniq ks ->
        x \in [sqint t1 t2 ks| ->
        [sqint t1 t2 ks| = [sqint t1 x ks| ++ [sqint x t2 ks|.
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqxo_filterL (sq_uoxo U (oltW H2)) filter_cat -sqxo_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(ole_trans H1).
Qed.

Lemma sq_oxox t1 t2 x ks :
        uniq ks ->
        x \in |sqint t1 t2 ks] ->
        |sqint t1 t2 ks] = |sqint t1 x ks] ++ |sqint x t2 ks].
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqox_filterL (sq_uxox U H2) filter_cat -sqox_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(olt_trans H1).
Qed.

Lemma sq_ooxx t1 t2 x ks :
        uniq ks ->
        x \in |sqint t1 t2 ks] ->
        |sqint t1 t2 ks] = |sqint t1 x ks| ++ [sqint x t2 ks].
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqox_filterL (sq_uoxx U H2) filter_cat -sqoo_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(olt_ole_trans H1).
Qed.

Lemma sq_oxoo t1 t2 x ks :
        uniq ks ->
        x \in |sqint t1 t2 ks| ->
        |sqint t1 t2 ks| = |sqint t1 x ks] ++ |sqint x t2 ks|.
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqoo_filterL (sq_uxoo U H2) filter_cat -sqox_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(olt_trans H1).
Qed.

Lemma sq_ooxo t1 t2 x ks :
        uniq ks ->
        x \in |sqint t1 t2 ks] ->
        |sqint t1 t2 ks| = |sqint t1 x ks| ++ [sqint x t2 ks|.
Proof.
move=>U; rewrite mem_filter=>/andP [] /andP [H1 H2] _.
rewrite sqoo_filterL (sq_uoxo U H2) filter_cat -sqoo_filterL.
congr (_ ++ _); rewrite -[RHS]filter_predT; apply: eq_in_filter.
by move=>k; rewrite mem_filter -andbA=>/and3P [] /(olt_ole_trans H1).
Qed.

(* singleton intervals *)

Lemma sqkk_xx ks k :
        uniq ks ->
        [sqint k k ks] = if k \in ks then [:: k] else [::].
Proof.
move=>U; case: ifP=>K.
- rewrite -(filter_pred1_uniq U K); apply: eq_in_filter=>x Kx.
  rewrite -eqn_leq; apply/eqP/eqP=>[|->] //.
  by move/esym/index_inj=>-> //; rewrite inE Kx orbT.
rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx.
rewrite -eqn_leq; case: eqP=>// /esym/index_inj E.
by rewrite -E ?Kx // in K; rewrite inE Kx orbT.
Qed.

Lemma sqkk_xo ks k : [sqint k k ks| = [::].
Proof.
rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx.
by rewrite /seq_le /seq_lt; case: ltngtP.
Qed.

Lemma sqkk_ox ks k : |sqint k k ks] = [::].
Proof.
rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx.
by rewrite /seq_le /seq_lt; case: ltngtP.
Qed.

Lemma sqkk_oo ks k : |sqint k k ks| = [::].
Proof.
rewrite -(filter_pred0 ks); apply: eq_in_filter=>x Kx.
by rewrite /seq_lt; case: ltngtP.
Qed.

(* endpoint split of single-bounded interval *)

Lemma squxR t ks :
        uniq ks -> t \in ks ->
        {sqint t ks] = {sqint t ks| ++ [:: t].
Proof. by move=>U D; rewrite (sq_uoxx (t1:=t)) // sqkk_xx // D. Qed.

Lemma sqxuL t ks :
        uniq ks -> t \in ks ->
        [sqint t ks} = [:: t] ++ |sqint t ks}.
Proof. by move=>U D; rewrite (sq_xxou (t2:=t)) // sqkk_xx // D. Qed.

(* endpoint split of double-bounded intervals *)

Lemma sqxxL t1 t2 ks :
        uniq ks ->
        t1 <=[ks] t2 -> t1 \in ks ->
        [sqint t1 t2 ks] = t1 :: |sqint t1 t2 ks].
Proof.
move=>U T D.
rewrite (sq_xxox (x:=t1)) ?sqkk_xx ?D //.
by rewrite mem_filter ole_refl T D.
Qed.

Lemma sqxxR t1 t2 ks :
        uniq ks ->
        t1 <=[ks] t2 -> t2 \in ks ->
        [sqint t1 t2 ks] = [sqint t1 t2 ks| ++ [:: t2].
Proof.
move=>U T D.
rewrite (sq_xoxx (x:=t2)) ?sqkk_xx ?D //.
by rewrite mem_filter ole_refl T D.
Qed.

Lemma sqxoL t1 t2 ks :
        uniq ks ->
        t1 <[ks] t2 -> t1 \in ks ->
        [sqint t1 t2 ks| = t1 :: |sqint t1 t2 ks|.
Proof.
move=>U T D.
rewrite (sq_xxoo (x:=t1)) ?sqkk_xx ?D //.
by rewrite mem_filter ole_refl T D.
Qed.

Lemma sqoxR t1 t2 ks :
        uniq ks ->
        t1 <[ks] t2 -> t2 \in ks ->
        |sqint t1 t2 ks] = |sqint t1 t2 ks| ++ [:: t2].
Proof.
move=>U T D.
rewrite (sq_ooxx (x:=t2)) ?sqkk_xx ?D //.
by rewrite mem_filter ole_refl T D.
Qed.

(* some simplifying equalities on intervals *)

(*
Lemma squx0 t ks :
        {sqint t ks] = if 0 \notin ks then [::] else filter (pred1 0) ks.
Proof.
rewrite if_neg; case: ifP=>K.
- by apply: eq_in_filter=>x /=; rewrite ole0.
rewrite -(filter_pred0 ks); apply: eq_in_filter.
by  move=>x; rewrite ole0; case: eqP K=>// ->->.
Qed.

Lemma squo0 ks : {sqint 0 ks| = [::].
Proof. by rewrite -(filter_pred0 ks); apply: eq_in_filter=>x; rewrite olt0. Qed.
*)

Lemma squx_notinE t ks : t \notin ks -> {sqint t ks] = ks.
Proof.
move=>T; rewrite -[RHS]filter_predT; apply: eq_in_filter=>x /= _.
by apply: ole_memI T.
Qed.

Lemma squo_notinE t ks : t \notin ks -> {sqint t ks| = ks.
Proof.
move=>T; rewrite -[RHS]filter_predT; apply: eq_in_filter=>x /= K.
by  apply: olt_memI K T.
Qed.

Lemma squx_consLX t ks :
        {sqint t (t :: ks)] = t :: filter (pred1 t) ks.
Proof.
rewrite (_ : t :: filter (pred1 t) ks = filter (pred1 t) (t :: ks)) /=.
- by apply: eq_in_filter=>x; rewrite oleR eq_sym.
by rewrite eq_refl.
Qed.

Lemma squx_consL t ks :
        t \notin ks -> {sqint t (t :: ks)] = [:: t].
Proof. by move=>H; rewrite squx_consLX (filter_pred1 H). Qed.

Lemma squo_consL t ks : {sqint t (t :: ks)| = [::].
Proof.
rewrite -(filter_pred0 (t::ks)); apply: eq_in_filter=>x.
by rewrite oltR.
Qed.

Lemma sqxu_notinE t ks : t \notin ks -> [sqint t ks} = [::].
Proof.
move=>T; rewrite -(filter_pred0 ks); apply: eq_in_filter=>x /= X.
by apply/negP=>/ole_memE/(_ X); rewrite (negbTE T).
Qed.

Lemma sqou_notinE t ks : t \notin ks -> |sqint t ks} = [::].
Proof.
move=>T; rewrite -(filter_pred0 ks); apply: eq_in_filter=>x /= _.
by apply/negP=>/olt_memE; rewrite (negbTE T).
Qed.

Lemma sqxu_consL t ks : [sqint t (t :: ks)} = t::ks.
Proof.
rewrite -[RHS]filter_predT; apply: eq_in_filter=>x _.
by rewrite oleL.
Qed.

Lemma sqou_consLX t ks :
        |sqint t (t :: ks)} = filter (predC (pred1 t)) ks.
Proof.
rewrite /olt_sq /= oltL eq_refl /=; apply: eq_in_filter=>x.
by rewrite oltL.
Qed.

Lemma sqou_consL t ks : t \notin ks -> |sqint t (t :: ks)} = ks.
Proof.
move=>T; rewrite sqou_consLX -[RHS]filter_predT.
by apply: eq_in_filter=>x /=; case: eqP T=>// -> /negbTE ->.
Qed.


(* intervals of one-element list *)

Lemma squx_singleton t k : {sqint t [:: k]] = [:: k].
Proof. by rewrite /sq_ole /= oleL. Qed.

Lemma squo_singleton t k :
        {sqint t [:: k]| = if t != k then [:: k] else [::].
Proof. by rewrite /sq_olt /= oltL. Qed.

(* intervals and constructors *)

Lemma squx_rcons_sameE ks k :
        k \notin ks -> {sqint k (rcons ks k)] = rcons ks k.
Proof.
move=>D; rewrite /sq_ole filter_rcons ole_refl.
congr rcons.
rewrite -[RHS]filter_predT; apply: eq_in_filter=>x /= K.
by rewrite ole_rcons // K (ole_memI _ D).
Qed.

Lemma squo_rcons_sameE ks k :
        k \notin ks -> {sqint k (rcons ks k)| = ks.
Proof.
move=>D; rewrite /sq_olt filter_rcons olt_irr.
rewrite -[RHS]filter_predT; apply: eq_in_filter=>x /= K.
by rewrite olt_rcons // K (negbTE D).
Qed.

Lemma squo_catE ks1 ks2 t :
        ~~ has (mem ks1) ks2 ->
        {sqint t ks1 ++ ks2| =
        if t \in ks1 then {sqint t ks1| else ks1 ++ {sqint t ks2|.
Proof.
move/hasPn=>U; rewrite /sq_olt filter_cat.
rewrite (_ : [seq x <- ks1 | x <[ks1++ks2] t] = {sqint t ks1|); last first.
- apply: eq_in_filter=>x X; rewrite olt_cat X /=; case: ifP=>// Y.
  by apply/esym; apply: olt_memI=>//; rewrite Y.
rewrite (_ : [seq x <- ks2 | x <[ks1++ks2] t] =
  if t \in ks1 then [::] else [seq x <- ks2 | x <[ks2] t]).
- by case: ifP; [rewrite cats0 | move/negbT/squo_notinE=>->].
case: ifP=>T; last first.
- apply: eq_in_filter=>x /= K2.
  by rewrite olt_cat T; move/U: K2=>/negbTE /= ->.
rewrite -(filter_pred0 ks2); apply: eq_in_filter=>x Kx.
rewrite olt_cat T /=; apply/negP=>/olt_memE=>Kx'.
by move/(_ _ Kx): U=>/=; rewrite Kx'.
Qed.

Lemma squx_catE ks1 ks2 t :
        ~~ has (mem ks1) ks2 ->
        {sqint t ks1 ++ ks2] =
        if t \in ks1 then {sqint t ks1] else ks1 ++ {sqint t ks2].
Proof.
move/hasPn=>U; rewrite /sq_ole filter_cat.
rewrite (_ : [seq x <- ks1 | x <=[ks1++ks2] t] = {sqint t ks1]); last first.
- by apply: eq_in_filter=>x X; rewrite ole_cat X.
rewrite (_ : [seq x <- ks2 | x <=[ks1++ks2] t] =
  if t \in ks1 then [::] else [seq x <- ks2 | x <=[ks2] t]).
- by case: ifP; [rewrite cats0 | move/negbT/squx_notinE=>->].
case: ifP=>T; last first.
- apply: eq_in_filter=>x /= K2.
  by rewrite ole_cat T /=; move/U: K2=>/negbTE /= ->.
rewrite -(filter_pred0 ks2); apply: eq_in_filter=>x Kx.
by rewrite ole_cat T; move/U: Kx=>/= /negbTE ->.
Qed.

Lemma sqou_catE ks1 ks2 t :
        ~~ has (mem ks1) ks2 ->
        |sqint t ks1 ++ ks2} =
        if t \in ks1 then |sqint t ks1} ++ ks2 else |sqint t ks2}.
Proof.
move/hasPn=>U; rewrite /olt_sq filter_cat.
rewrite (_ : [seq x <- ks1 | t <[ks1++ks2] x] = |sqint t ks1}); last first.
- by apply: eq_in_filter=>x X; rewrite olt_cat X.
rewrite (_ : [seq x <- ks2 | t <[ks1++ks2] x] =
  if t \in ks1 then ks2 else |sqint t ks2}).
- by case: ifP=>// /negbT/sqou_notinE=>->; rewrite cat0s.
case: ifP=>T; last first.
- apply: eq_in_filter=>x /= K2.
  by rewrite olt_cat T /=; move/U: K2=>/negbTE /= ->.
rewrite -[RHS]filter_predT; apply: eq_in_filter=>x Kx.
by rewrite olt_cat T /=; move/U: Kx=>/negbTE /= ->.
Qed.

Lemma sqxu_catE ks1 ks2 t :
        ~~ has (mem ks1) ks2 ->
        [sqint t ks1 ++ ks2} =
        if t \in ks1 then [sqint t ks1} ++ ks2 else [sqint t ks2}.
Proof.
move/hasPn=>U; rewrite /ole_sq filter_cat.
rewrite (_ : [seq x <- ks1 | t <=[ks1++ks2] x] = [sqint t ks1}); last first.
- apply: eq_in_filter=>x X; rewrite ole_cat X /=; case: ifP=>// /negbT T.
  by apply/esym/negP=>/ole_memE/(_ X); rewrite (negbTE T).
rewrite (_ : [seq x <- ks2 | t <=[ks1++ks2] x] =
  if t \in ks1 then ks2 else [sqint t ks2}).
- by case: ifP=>// /negbT/sqxu_notinE=>->; rewrite cat0s.
case: ifP=>T; last first.
- apply: eq_in_filter=>x /= K2.
  by rewrite ole_cat T /=; move/U: K2=>/negbTE /= ->.
rewrite -[RHS]filter_predT; apply: eq_in_filter=>x Kx.
by rewrite ole_cat T /=; apply: ole_memI; apply: U Kx.
Qed.

Lemma squx_consE k ks t :
        k \notin ks ->
        {sqint t (k::ks)] =
        if t == k then [:: k] else k :: {sqint t ks].
Proof.
rewrite -(cat1s k)=>U; rewrite squx_catE //= ?inE.
- by rewrite eq_sym; case: eqP=>// ->; rewrite squx_consL.
by apply/hasPn=>x /=; rewrite inE; case: eqP U=>// -> /negbTE ->.
Qed.

Lemma squo_cons_same k ks : {sqint k (k::ks)| = [::].
Proof.
rewrite /sq_olt /= oltL eq_refl -[RHS](filter_pred0 ks).
by apply: eq_in_filter=>x X /=; rewrite oltR.
Qed.

Lemma squo_cons_head k ks t :
        t != k -> {sqint t (k::ks)| = k :: behead {sqint t (k::ks)|.
Proof. by rewrite /sq_olt /= oltL => ->. Qed.

(* the tails may differ in a few extra k's on the left side *)
(* this lemma doesn't quite say that -- it says that the non-k *)
(* positions are the same -- but it's ok *)
Lemma squo_cons_filter k ks t :
        t != k ->
        filter (predC1 k) {sqint t (k::ks)| = filter (predC1 k) {sqint t ks|.
Proof.
move=>N; rewrite /sq_olt /= oltL N /= eq_refl /=.
rewrite -[LHS]filter_predI -[RHS]filter_predI.
apply: eq_in_filter=>x X /=.
by rewrite olt_cons N /=; case: eqP.
Qed.

(* without k \notin ks, we can get =i *)
Lemma squo_cons_mem k ks t :
        {sqint t (k::ks)| =i
        if t == k then [::] else k :: {sqint t ks|.
Proof.
case: eqP=>[->|/eqP N] x; first by rewrite squo_cons_same.
rewrite squo_cons_head // !inE.
case: eqP=>//= /eqP Nx.
have : (x \in filter (predC1 k) {sqint t (k::ks)|) =
       (x \in filter (predC1 k) {sqint t ks|).
- by rewrite (squo_cons_filter ks N).
rewrite !mem_filter /= Nx /= inE (negbTE Nx) /=.
by rewrite /sq_olt /= oltL N /= mem_filter.
Qed.

(* with k \notin ks, we get equality *)
Lemma squo_consE k ks t :
        k \notin ks ->
        {sqint t (k::ks)| =
        if t == k then [::] else k :: {sqint t ks|.
Proof.
rewrite -(cat1s k)=>U; rewrite squo_catE // ?inE.
- by case: eqP=>// ->; rewrite squo_consL.
by apply/hasPn=>x /=; rewrite inE; case: eqP U=>// -> /negbTE ->.
Qed.

Lemma squx_rconsE k ks t :
        k \notin ks ->
        {sqint t (rcons ks k)] =
        if t \in ks then {sqint t ks] else rcons ks k.
Proof.
rewrite -cats1=>U; rewrite squx_catE //=; last first.
- by rewrite (negbTE U).
by rewrite squx_singleton.
Qed.

Lemma squo_rconsE k ks t :
        k \notin ks ->
        {sqint t (rcons ks k)| =
        if t \in ks then {sqint t ks| else
          if t == k then ks else rcons ks k.
Proof.
rewrite -(cats1 ks)=>U; rewrite squo_catE //= ?squo_singleton.
- by case: eqP U=>//= -> /negbTE ->; rewrite cats0.
by rewrite (negbTE U).
Qed.

(* surgery on intervals (very incomplete right now) *)

Lemma squo_cons x xs : x \notin xs -> {sqint x x::xs| = [::].
Proof. by move=>H; rewrite squo_consE // eq_refl. Qed.

Lemma squo_split t xs1 xs2 :
        t \notin xs1 -> t \notin xs2 -> ~~ has (mem xs1) xs2 ->
        {sqint t (xs1++t::xs2)| = xs1.
Proof.
move=>T1 T2 /hasPn X; rewrite squo_catE.
- by rewrite (negbTE T1) squo_cons // cats0.
apply/hasPn=>x; rewrite inE; case: eqP=>[->|_] //=.
by apply: X.
Qed.

Lemma sqou_split t xs1 xs2 :
        t \notin xs1 -> t \notin xs2 -> ~~ has (mem xs1) xs2 ->
        |sqint t (xs1++t::xs2)} = xs2.
Proof.
move=>T1 T2 /hasPn X; rewrite sqou_catE.
- by rewrite (negbTE T1) sqou_consL.
by apply/hasPn=>x; rewrite inE; case: eqP=>[->|_] //=; apply: X.
Qed.

(* the uniqueness condition can be relaxed here *)
(* but selecting just the right conditions is a burden *)
(* as there are too many of them *)
Lemma sqoo_split t1 t2 xs1 xs2 xs :
        uniq (xs1++t1::xs++t2::xs2) ->
        |sqint t1 t2 xs1++t1::xs++t2::xs2| = xs.
Proof.
move=>U; move: (U); rewrite /= !cat_uniq /= !mem_cat !inE /= !negb_or -!andbA.
rewrite !cat_uniq /= has_cat /= !negb_or /= -!andbA.
case/and10P=>U1 U2 U3 U4 U5 U6 U7 U8 U9 /and4P [U10 U11 U12 U13].
rewrite sq_ouou ?olt_splitR //; last by rewrite eq_sym.
rewrite (_ : xs1++t1::xs++t2::xs2 = (xs1++t1::xs)++t2::xs2);
last by rewrite -catA.
rewrite squo_split ?sqou_split //.
- by rewrite mem_cat inE !negb_or U4 eq_sym U7 U10.
apply/hasPn=>x X /=; rewrite mem_cat inE !negb_or.
move/hasPn: U5=>-> //=; move/hasPn: U11=>-> //=.
by case: eqP X U8=>// ->->.
Qed.

Lemma sqoo_split_consec t1 t2 xs1 xs2 :
        uniq (xs1++t1::t2::xs2) ->
        |sqint t1 t2 xs1++t1::t2::xs2| = [::].
Proof.
move=>U; rewrite (_ : t2::xs2 = [::]++t2::xs2) // in U *.
by rewrite sqoo_split.
Qed.

(* the common case when xs1 = nil *)
Lemma sqoo_nil_split t1 t2 xs2 xs :
        uniq (t1::xs++t2::xs2) ->
        |sqint t1 t2 t1::xs++t2::xs2| = xs.
Proof.
set j := t1::_; move=>U.
by rewrite -(cat0s j) sqoo_split.
Qed.

Lemma sqoo_nil_split_consec t1 t2 xs2 :
        uniq (t1::t2::xs2) ->
        |sqint t1 t2 t1::t2::xs2| = [::].
Proof.
set j := t1::_; move=>U.
by rewrite -(cat0s j) sqoo_split_consec.
Qed.

(* intervals and filter *)

Lemma squo_filter p t xs :
        (t \notin xs) || p t ->
        {sqint t (filter p xs)| = filter p {sqint t xs|.
Proof.
move=>H; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite olt_filter // D orbT.
Qed.

Lemma squx_filter p t xs :
        (t \notin xs) || p t ->
        {sqint t (filter p xs)] = filter p {sqint t xs].
Proof.
move=>H; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite ole_filter // D orbT.
Qed.

Lemma sqou_filter p t xs :
        (t \notin xs) || p t ->
        |sqint t (filter p xs)} = filter p |sqint t xs}.
Proof.
move=>H; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite olt_filter // D orbT.
Qed.

Lemma sqxu_filter p t xs :
        (t \notin xs) || p t ->
        [sqint t (filter p xs)} = filter p [sqint t xs}.
Proof.
move=>H; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite ole_filter // D orbT.
Qed.

Lemma sqoo_filter p t1 t2 xs :
        (t1 \notin xs) || p t1 -> (t2 \notin xs) || p t2 ->
        |sqint t1 t2 (filter p xs)| = filter p |sqint t1 t2 xs|.
Proof.
move=>H1 H2; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite !olt_filter ?(D,orbT).
Qed.

Lemma sqox_filter p t1 t2 xs :
        (t1 \notin xs) || p t1 -> (t2 \notin xs) || p t2 ->
        |sqint t1 t2 (filter p xs)] = filter p |sqint t1 t2 xs].
Proof.
move=>H1 H2; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite olt_filter ?ole_filter ?(D,orbT).
Qed.

Lemma sqxo_filter p t1 t2 xs :
        (t1 \notin xs) || p t1 -> (t2 \notin xs) || p t2 ->
        [sqint t1 t2 (filter p xs)| = filter p [sqint t1 t2 xs|.
Proof.
move=>H1 H2; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite olt_filter ?ole_filter ?(D,orbT).
Qed.

Lemma sqxx_filter p t1 t2 xs :
        (t1 \notin xs) || p t1 -> (t2 \notin xs) || p t2 ->
        [sqint t1 t2 (filter p xs)] = filter p [sqint t1 t2 xs].
Proof.
move=>H1 H2; rewrite [LHS]filter_swap -!filter_predI.
apply: eq_in_filter=>x X /=; case D : (p x)=>//=.
by rewrite !ole_filter ?(D,orbT).
Qed.

(* sequence ordering, intervals, and last *)

Lemma olt_ole_last k ks x t :
        uniq (k::ks) -> t != k ->
        x <[k::ks] t = x <=[k::ks] (last k {sqint t ks|).
Proof.
elim: ks k=>/= [|y ks IH] k //=.
- rewrite olt_cons olt_nil ole_cons ole_nil andbT eq_refl orbF.
  by move=>_ ->.
rewrite inE negb_or -andbA; case/and4P=>Nky K Y U Nkt.
rewrite olt_cons ole_cons Nkt /=; case: (x =P k)=>//= /eqP Nkx.
rewrite squo_consE //.
case: (t =P y)=>[E|/eqP Nty].
- by subst y; rewrite oltR //= eq_refl.
suff -> /= : last y {sqint t ks| != k by rewrite IH // Y.
case: eqP=>// E; move: (mem_last y {sqint t ks|).
by rewrite inE E (negbTE Nky) mem_filter (negbTE K) andbF.
Qed.

(* a slight variation to add the cons to last *)
Lemma olt_ole_last' k ks x t :
        uniq (k::ks) -> t != k ->
        x <[k::ks] t = x <=[k::ks] (last k {sqint t (k::ks)|).
Proof.
move=>U K; rewrite olt_ole_last // squo_consE; last by case/andP: U.
by rewrite (negbTE K).
Qed.

Lemma squox_last k ks t :
        uniq (k::ks) -> t != k ->
        {sqint (last k {sqint t ks|) (k :: ks)] = {sqint t (k::ks)|.
Proof.
by move=>U K; apply: eq_in_filter=>x _; rewrite -olt_ole_last.
Qed.

(****************************)
(* some bureaucratic lemmas *)
(****************************)

(* membership *)

Lemma mem_oo t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <[ks] k & k <[ks] t2])
                (k \in |sqint t1 t2 ks|).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_xo t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <=[ks] k & k <[ks] t2])
                (k \in [sqint t1 t2 ks|).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_ox t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <[ks] k & k <=[ks] t2])
                (k \in |sqint t1 t2 ks]).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_xx t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <=[ks] k & k <=[ks] t2])
                (k \in [sqint t1 t2 ks]).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_uo t ks k :
        reflect ([/\ k \in ks & k <[ks] t])(k \in {sqint t ks|).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

Lemma mem_ux t ks k :
        reflect ([/\ k \in ks & k <=[ks] t])(k \in {sqint t ks]).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

Lemma mem_ou t ks k :
        reflect ([/\ k \in ks & t <[ks] k])(k \in |sqint t ks}).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

Lemma mem_xu t ks k :
        reflect ([/\ k \in ks & t <=[ks] k])(k \in [sqint t ks}).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

(* has predT lemmas *)

Lemma has_oo t1 t2 ks :
        has predT |sqint t1 t2 ks| = has (fun z => t1 <[ks] z && z <[ks] t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_oo=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_ox t1 t2 ks :
        has predT |sqint t1 t2 ks] = has (fun z => t1 <[ks] z && z <=[ks] t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_ox=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_xo t1 t2 ks :
        has predT [sqint t1 t2 ks| = has (fun z => t1 <=[ks] z && z <[ks] t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_xo=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_xx t1 t2 ks :
        has predT [sqint t1 t2 ks] = has (fun z => t1 <=[ks] z && z <=[ks] t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_xx=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_ou t ks :
        has predT |sqint t ks} = has (fun z => t <[ks] z) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_ou=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_xu t ks :
        has predT [sqint t ks} = has (fun z => t <=[ks] z) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_xu=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_uo t ks :
        has predT {sqint t ks| = has (fun z => z <[ks] t) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_uo=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_ux t ks :
        has predT {sqint t ks] = has (fun z => z <=[ks] t) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_ux=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

(* negation of has on the left side *)

Lemma hasNL_oo ks t1 t2 (p : pred nat) :
       t1 <[ks] t2 -> ~~ has p |sqint t1 t2 ks| ->
       {in ks, forall z, p z -> z <[ks] t2 = z <=[ks] t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oleNgt.
case/orP=>H1; first by rewrite H1 (ole_olt_trans H1 T).
by rewrite oltNge H1 oleNgt (olt_ole_trans T H1).
Qed.

Lemma hasNL_ox ks t1 t2 (p : pred nat) :
       t1 <=[ks] t2 -> ~~ has p |sqint t1 t2 ks] ->
       {in ks, forall z, p z -> z <=[ks] t2 = z <=[ks] t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oleNgt.
case/orP=>H1; first by rewrite H1 (ole_trans H1 T).
rewrite (negbTE H1); apply/esym/negP=>X.
by rewrite (ole_trans X T) in H1.
Qed.

Lemma hasNL_xo ks t1 t2 (p : pred nat) :
       t1 <=[ks] t2 -> ~~ has p [sqint t1 t2 ks| ->
       {in ks, forall z, p z -> z <[ks] t2 = z <[ks] t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oleNgt.
rewrite -oltNge; case/orP=>H1; first by rewrite H1 (olt_ole_trans H1 T).
by rewrite oltNge H1 oltNge (ole_trans T H1).
Qed.

Lemma hasNL_xx ks t1 t2 (p : pred nat) :
       t1 <=[ks] t2 -> ~~ has p [sqint t1 t2 ks] ->
       {in ks, forall z, p z -> z <=[ks] t2 = z <[ks] t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oltNge.
case/orP=>H1; first by rewrite H1 (oltW (olt_ole_trans H1 T)).
by rewrite oleNgt H1 oltNge (oltW (ole_olt_trans T H1)).
Qed.

Lemma hasNL_ou ks t (p : pred nat) :
       ~~ has p |sqint t ks} -> {in ks, forall z, p z -> z <=[ks] t}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oleNgt.
Qed.

Lemma hasNL_xu ks t (p : pred nat) :
       ~~ has p [sqint t ks} -> {in ks, forall z, p z -> z <[ks] t}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oltNge.
Qed.

Lemma hasNL_uo ks t (p : pred nat) :
       ~~ has p {sqint t ks| -> {in ks, forall z, p z -> t <=[ks] z}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oleNgt.
Qed.

Lemma hasNL_ux ks t (p : pred nat) :
       ~~ has p {sqint t ks] -> {in ks, forall z, p z -> t <[ks] z}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oltNge.
Qed.

(* negation of has on the right side *)

Lemma hasNR_oo ks t1 t2 (p : pred nat) :
       {in ks, forall z, p z -> z <[ks] t2 = z <=[ks] t1} ->
       ~~ has p |sqint t1 t2 ks|.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (olt_ole_trans H1 H2); rewrite olt_irr.
Qed.

Lemma hasNR_ox ks t1 t2 (p : pred nat) :
       {in ks, forall z, p z -> z <=[ks] t2 = z <=[ks] t1} ->
       ~~ has p |sqint t1 t2 ks].
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (ole_olt_trans H2 H1); rewrite olt_irr.
Qed.

Lemma hasNR_xo ks t1 t2 (p : pred nat) :
       {in ks, forall z, p z -> z <[ks] t2 = z <[ks] t1} ->
       ~~ has p [sqint t1 t2 ks|.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (ole_olt_trans H1 H2); rewrite olt_irr.
Qed.

Lemma hasNR_xx ks t1 t2 (p : pred nat) :
       {in ks, forall z, p z -> z <=[ks] t2 = z <[ks] t1} ->
       ~~ has p [sqint t1 t2 ks].
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (ole_olt_trans H1 H2); rewrite olt_irr.
Qed.

Lemma hasNR_ou ks t (p : pred nat) :
       {in ks, forall z, p z -> z <=[ks] t} -> ~~ has p |sqint t ks}.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (ole_olt_trans (T z H2 P) H1); rewrite olt_irr.
Qed.

Lemma hasNR_xu ks t (p : pred nat) :
       {in ks, forall z, p z -> z <[ks] t} -> ~~ has p [sqint t ks}.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (olt_ole_trans (T z H2 P) H1); rewrite olt_irr.
Qed.

Lemma hasNR_uo ks t (p : pred nat) :
       {in ks, forall z, p z -> t <=[ks] z} -> ~~ has p {sqint t ks|.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (ole_olt_trans (T z H2 P) H1); rewrite olt_irr.
Qed.

Lemma hasNR_ux ks t (p : pred nat) :
       {in ks, forall z, p z -> t <[ks] z} -> ~~ has p {sqint t ks].
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (olt_ole_trans (T z H2 P) H1); rewrite olt_irr.
Qed.


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


(**************************************)
(**************************************)
(* Consecutive elements in a sequence *)
(**************************************)
(**************************************)


(* The interval lemmas let us equate evaluations of interval endpoints *)
(* But, when a property we want to prove involves other components *)
(* we need to properly induct over ks. *)
(* We thus first define what it means for elements in ks to be consecutive, *)
(* so that the properties can be used in the proofs of the inductive cases. *)

(* t2 is consecutive to t1 in ks if it appears after t1 and there are *)
(* no other elements in ks between t1 and t2 *)
Definition consec ks t1 t2 :=
  [&& t1 <[ks] t2 & ~~ has predT |sqint t1 t2 ks|].

(* several alternative formulations *)
Lemma consecP ks t1 t2 :
        reflect ([/\ t1 <[ks] t2 & |sqint t1 t2 ks| = [::]])
                (consec ks t1 t2).
Proof.
case C : (consec ks t1 t2); constructor.
- by case/andP: C=>T; rewrite -nilp_hasPn=>/nilP S.
case=>T S; move/(elimF idP): C; apply.
by rewrite /consec T /= -nilp_hasPn; apply/nilP.
Qed.

Lemma consecP_in (ks : seq nat) t1 t2 :
        reflect ([/\ t1 \in ks & {in ks, forall z, z <[ks] t2 = z <=[ks] t1}])
                (consec ks t1 t2).
Proof.
case C: (consec ks t1 t2); constructor.
- case/andP: C=>T E; split; first by apply: olt_memE T.
  by move=>z Z; apply: hasNL_oo T E _ Z _.
case=>T H; apply: (elimF idP) C _.
by rewrite /consec H // ole_refl hasNR_oo // => z /H.
Qed.

(* frequent projections *)

Lemma consec_olt ks t1 t2 : consec ks t1 t2 -> t1 <[ks] t2.
Proof. by case/andP. Qed.

Lemma consec_mem ks t1 t2 : consec ks t1 t2 -> t1 \in ks.
Proof. by case/andP=>/olt_memE. Qed.

Lemma consec_oo ks t1 t2 : consec ks t1 t2 -> |sqint t1 t2 ks| = [::].
Proof. by case/consecP. Qed.

Lemma consec_in ks t1 t2 :
        consec ks t1 t2 -> {in ks, forall z, z <[ks] t2 = z <=[ks] t1}.
Proof. by case/consecP_in. Qed.

(* main splitting properties of consec *)

(* if t2 \in ks then ks splits *)
Lemma consecP_split ks t1 t2 :
        uniq ks -> t2 \in ks ->
        reflect (exists xs1 xs2, ks = xs1++t1::t2::xs2)
                (consec ks t1 t2).
Proof.
move=>U T2.
case C : (consec ks t1 t2); constructor.
- case/andP: C=>N H; case/olt_splitL: N=>xs1 [xs2][E] N T1 T2'.
  rewrite {ks}E mem_cat /= inE (negbTE T2') eq_sym (negbTE N)  /= in U T2 H *.
  case/in_split: T2=>ks3 [ks4][E T2'']; rewrite {xs2}E in U H *.
  by rewrite sqoo_split // -nilp_hasPn in H; move/nilP: H=>->; exists xs1, ks4.
case=>xs1 [xs2] E; rewrite {ks}E in U T2 C; move/(elimF idP): C; apply.
move: (U); rewrite cat_uniq /= inE !negb_or -!andbA (eq_sym t1 t2).
case/and8P=>U1 U2 U3 U4 U5 U6 U7 U8.
by rewrite /consec olt_splitR // sqoo_split_consec.
Qed.

(* if t2 \notin ks, then t1 is last *)
Lemma consec_last ks t1 t2 :
        uniq ks -> t2 \notin ks ->
        consec ks t1 t2 -> t1 = last t2 ks.
Proof.
move=>U T /andP []; case: (lastP ks) U T=>[|xs x] //=.
rewrite rcons_uniq olt_rcons mem_rcons inE negb_or last_rcons !(eq_sym x).
case/andP=>H1 H2 /andP [H5 H6] H3 H4.
rewrite (negbTE H6) H5 /= in H3; case/orP: H3=>[H3 |/eqP //].
suff : x \in |sqint t1 t2 (rcons xs x)| by move/hasPn: H4=>X /X.
rewrite mem_filter !olt_rcons (negbTE H1) H3 eq_refl (negbTE H6) !(eq_sym x) H5 /=.
by rewrite mem_rcons inE eq_refl.
Qed.

(* restatement of consec_last as a  split *)
Lemma consecP_last ks t1 t2 :
        uniq ks -> t2 \notin ks ->
        reflect (exists xs, ks = rcons xs t1)
                (consec ks t1 t2).
Proof.
move=>U T2.
case C : (consec ks t1 t2); constructor.
- move: (lastI t2 ks); rewrite -(consec_last U T2 C).
  case: (lastP ks)=>[[E]|xs x]; first by rewrite E (consec_mem C) in T2.
  by rewrite belast_rcons; case=>/rcons_inj [->]; eauto.
case=>xs E; rewrite E /consec rcons_uniq mem_rcons inE negb_or eq_sym in C U T2.
case/andP: U T2 C=>T1 U /andP [N T2].
rewrite olt_rcons (negbTE T2) (negbTE T1) N eq_refl /=.
case/negbFE/hasP=>x.
rewrite mem_filter !olt_rcons mem_rcons inE (eq_sym x) eq_refl /=.
rewrite (negbTE T1) (negbTE T2) N /= andbT orbC -andbA andbb orbC andbC.
case: ifP=>/= X; last by rewrite andbN.
by move/olt_memE; rewrite (negbTE T1).
Qed.

(* consecutiveness and sortedness under nat *)

Lemma consec_sorted ks t1 t2 :
        sorted ltn ks -> t2 \in ks -> consec ks t1 t2 ->
        {in ks, forall z, (z < t2) = (z <= t1)}.
Proof.
move=>S T2 /consecP_in [T1 H] z Z.
rewrite -(olt_sortedE S Z T2) -(ole_sortedE S Z T1).
by apply: H Z.
Qed.

(* consecutiveness and sortedness under general relation *)

Lemma consec_sorted_lt ltT ks t1 t2 :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        {in ks &, total (fun x y => (x == y) || ltT x y)} ->
        t2 \in ks ->
        consec ks t1 t2 ->
        {in ks, forall z, ltT z t2 = (z == t1) || ltT z t1}.
Proof.
move=>I Asym T S Tot T2 C; move: (consec_mem C)=>T1.
have {}Asym : antisymmetric (fun x y => (x == y) || ltT x y).
- move=>x y; rewrite (eq_sym y); case: eqP=>//= _.
  by apply: (Asym x y).
have {}T : transitive (fun x y => (x == y) || ltT x y).
- move=>x y z; case: eqP=>[->|/eqP _] //=.
  case: eqP=>[->->|/eqP _ /=]; first by rewrite orbT.
  by case: eqP=>//= _; apply: T.
have {}S : sorted (fun x y => (x == y) || ltT x y) ks.
- by apply: sub_sorted S=>x y ->; rewrite orbT.
move=>z Z; move/consec_in/(_ z Z): C.
rewrite (olt_sorted_ltE Asym T S Tot) //.
rewrite (ole_sorted_ltE Asym T S Tot) //.
by rewrite !orbA orbb; case: eqP=>//= ->; rewrite I.
Qed.

Lemma consec_sorted_le (leT : rel nat) ks t1 t2 :
        {in ks, reflexive leT} ->
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        {in ks &, total leT} ->
        t2 \in ks ->
        consec ks t1 t2 ->
        {in ks, forall z, leT z t1 = (z != t2) && leT z t2}.
Proof.
move=>R Asym T S Tot T2 C; move: (consec_mem C)=>T1.
move=>z Z; move/consec_in/(_ z Z): C.
rewrite (olt_sorted_ltE Asym T S Tot) //.
rewrite (ole_sorted_ltE Asym T S Tot) //.
by move=>->; case: eqP=>// ->; rewrite R.
Qed.

(* alternative formulation where we sort ks in consec *)
(* this form is required in some proofs for linearizability *)
Lemma consec_sort_lt ltT ks t1 t2 :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        {in ks &, total (fun x y => (x == y) || ltT x y)} ->
        uniq ks ->
        t2 \in ks ->
        consec (sort (fun x y => (x == y) || ltT x y) ks) t1 t2 ->
        {in ks, forall z, ltT z t2 = (z == t1) || ltT z t1}.
Proof.
set ks' := sort _ _=>I asym T Tot U T2 C z Z.
apply: (@consec_sorted_lt ltT ks')=>//.
- by apply: sort_sorted_in_lt.
- by move=>x y; rewrite !mem_sort; apply: Tot.
- by rewrite mem_sort.
by rewrite mem_sort.
Qed.

Lemma consec_sort_le (leT : rel nat) ks t1 t2 :
        {in ks, reflexive leT} ->
        antisymmetric leT ->
        transitive leT ->
        {in ks &, total leT} ->
        t2 \in ks ->
        consec (sort leT ks) t1 t2 ->
        {in ks, forall z, leT z t1 = (z != t2) && leT z t2}.
Proof.
set ks' := sort _ _=>R Asym T Tot T2 C z Z.
apply: (@consec_sorted_le leT ks')=>//.
- by move=>x; rewrite mem_sort; apply: R.
- by apply: sort_sorted_in Tot _ _.
- by move=>x y; rewrite !mem_sort; apply: Tot.
- by rewrite mem_sort.
by rewrite mem_sort.
Qed.

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

(*******************************)
(* consec and cons constructor *)
(*******************************)

Lemma consec_hdswap k1 k2 ks x :
        k1 \notin ks -> x != k2 ->
        consec (k1::ks) k1 x -> consec (k2::ks) k2 x.
Proof.
move=>K1 N2 C.
have N1 : x != k1 by move/consec_olt: C; rewrite oltL.
move: C; rewrite /consec !oltL N1 N2 /=.
apply: contra=>/hasP [z Z] _; apply/hasP; exists z=>//.
rewrite !mem_filter !oltL !inE !olt_cons  N1 N2  /= !(eq_sym z) in Z *.
case: eqP Z=>[<-|_]; first by case: eqP.
by case: eqP=>//= <-; rewrite (negbTE K1) andbF.
Qed.

Lemma consec_cons k ks x y :
        x != k -> y != k -> consec ks x y -> consec (k::ks) x y.
Proof.
move=>Nx Ny; rewrite /consec olt_cons Ny (negbTE Nx) /=.
case/andP=>->; apply: contra; case/hasP=>z Z _; apply/hasP; exists z=>//.
rewrite !mem_filter inE !olt_cons (negbTE Nx) Ny !(eq_sym z) in Z *.
by case: eqP Z.
Qed.

Lemma consec_hd2 k1 k2 ks : k1 != k2 -> consec [:: k1, k2 & ks] k1 k2.
Proof.
move=>N; rewrite /consec !oltL eq_sym N /=.
apply/hasPn=>z; rewrite mem_filter !oltL !olt_cons (eq_sym k2 k1) N /= eq_refl.
by case: eqP.
Qed.

Lemma consec_behead k ks x y :
        k \notin ks -> x != k -> y != k ->
        consec (k::ks) x y -> consec ks x y.
Proof.
move=>K Nx Ny; rewrite /consec olt_cons Ny (negbTE Nx) /=.
case/andP=>->; apply: contra; case/hasP=>z Z _; apply/hasP; exists z=>//.
rewrite !mem_filter !olt_cons !inE !(eq_sym z) (negbTE Nx) Ny /= -!andbA in Z * .
by case: eqP K Z=>// -> /negbTE ->; rewrite !andbF.
Qed.

(***************************************)
(* Consecutiveness induction principle *)
(***************************************)

Lemma consec_ind_raw k (ks : seq nat) (P : nat -> Prop) :
        k \notin ks -> uniq ks ->
        P k ->
        (forall t1 t2, t2 \in ks -> consec (k::ks) t1 t2 -> P t1 -> P t2) ->
        forall t, t \in k::ks -> P t.
Proof.
elim: ks=>[|x ks IH] //= K U H0 Hstep t; first by rewrite inE=>/eqP ->.
rewrite inE negb_or in K U; case/andP: K U=>K1 K2 /andP [U1 U2].
rewrite !inE; case/or3P; first by move/eqP=>->.
- move/eqP=>->{t}; apply: Hstep H0; first by rewrite inE eq_refl.
  rewrite /consec oltL eq_sym K1 (sqoo_split_consec (xs1:=[::])) //=.
  by rewrite inE negb_or K1 K2 U1 U2.
have U : uniq (k::x::ks) by rewrite /= inE negb_or K1 K2 U1 U2.
move=>T; apply: IH=>[|||t1 t2 T2 C|] //; last by rewrite inE T orbT.
(* useful sides *)
have Nx2 : t2 != x by case: eqP T2 U1=>// ->->.
have Nk2 : t2 != k by case: eqP T2 K2=>// ->->.
(* main proof *)
case: (t1 =P k) C=>[->{t1} C _|/eqP Nt1k C].
- (* in this case, we need two induction steps *)
  suff [Ckx Cxt2] : consec [:: k, x & ks] k x /\ consec [:: k, x & ks] x t2.
  - have : P x by apply: Hstep Ckx H0; rewrite inE eq_refl.
    by apply: Hstep Cxt2; rewrite inE T2 orbT.
  split; first by apply: consec_hd2.
  apply: consec_cons=>//; try by rewrite (eq_sym _ k).
  by apply: consec_hdswap C.
(* another useful side which holds only if k != t1 *)
have Nx1 : t1 != x.
- case: eqP U1=>// <-; move: (consec_mem C).
  by rewrite inE (negbTE Nt1k) /= =>->.
(* then the proof is straightforward *)
apply: Hstep; first by rewrite inE T2 orbT.
by do 2![apply: consec_cons=>//]; apply: consec_behead C.
Qed.

(* somewhat modified variant of consec_ind_raw *)
(* that I hope is more usable in practice *)
Lemma consec_ind k (ks : seq nat) (P : nat -> Prop) :
        uniq (k :: ks) ->
        P k ->
        (forall t1 t2, t2 \in ks -> consec (k::ks) t1 t2 -> P t1 -> P t2) ->
        forall t, t \in ks -> P t.
Proof.
move=>/= /andP [U1 U2] P0 IH t D; apply: consec_ind_raw IH _ _=>//.
by rewrite inE D orbT.
Qed.

(* special variants when we induct over an interval *)
(* that is open/closed/unbounded on the right *)

Lemma consec_indo (ks : seq nat) k1 k2 (P : nat -> Prop) :
        uniq ks -> k1 <[ks] k2 ->
        P k1 ->
        (forall t1 t2,
           t2 \in |sqint k1 k2 ks| ->
           consec [sqint k1 k2 ks| t1 t2 -> P t1 -> P t2) ->
        forall t, t \in |sqint k1 k2 ks| -> P t.
Proof.
move=>U N H0 IH t; apply: (consec_ind (k:=k1))=>//=.
- by rewrite filter_uniq // andbT mem_filter olt_irr.
move=>t1 t2 H C; apply: IH=>//; rewrite sqxoL //.
by apply: olt_memE N.
Qed.

Lemma consec_indx (ks : seq nat) k1 k2 (P : nat -> Prop) :
        uniq ks -> k1 <=[ks] k2 -> k1 \in ks ->
        P k1 ->
        (forall t1 t2,
           t2 \in |sqint k1 k2 ks] ->
           consec [sqint k1 k2 ks] t1 t2 -> P t1 -> P t2) ->
        forall t, t \in |sqint k1 k2 ks] -> P t.
Proof.
move=>U N K H0 IH t; apply: (consec_ind (k:=k1))=>//=.
- by rewrite filter_uniq // andbT mem_filter olt_irr.
by move=>t1 t2 H C; apply: IH=>//; rewrite sqxxL.
Qed.

Lemma consec_indu (ks : seq nat) k (P : nat -> Prop) :
        uniq ks -> k \in ks ->
        P k ->
        (forall t1 t2,
           t2 \in |sqint k ks} ->
           consec [sqint k ks} t1 t2 -> P t1 -> P t2) ->
        forall t, t \in |sqint k ks} -> P t.
Proof.
move=>U K H0 IH t; apply: (consec_ind (k:=k))=>//=.
- by rewrite filter_uniq // andbT mem_filter olt_irr.
by move=>t1 t2 H C; apply: IH=>//; rewrite sqxuL.
Qed.

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
