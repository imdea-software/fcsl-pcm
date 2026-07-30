(*
Copyright 2022 IMDEA Software Institute
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

From Stdlib Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude pred ordtype seqext.
Local Open Scope order_scope.
Import Order.Theory.

(* We assume the sequences are unique and use the first index, however most *)
(* lemmas don't require this condition explicitly. The ones that do are     *)
(* grouped in a separate section.                                           *)

(***********************************)
(***********************************)
(* Sequence-induced ordering       *)
(* definition and basic properties *)
(***********************************)
(***********************************)

(* x <[ks] y if first x appears to the left of last y in the sequence ks *)

(* It turns out it's useful to have 0 <[ks] x, for every x. *)
(* Basically, we use these orderings for reasoning about *)
(* timestamps in histories, and we always keep the null timestamp *)
(* to stand for the initialization step *)
(* That said, the null timestamp is never in any history as *)
(* the initialization step is implicit *)

Module Type SeqOrdTp.
Parameter seq_le : forall (A : eqType) (ks : seq A), A -> A -> bool.
Parameter seq_lt : forall (A : eqType) (ks : seq A), A -> A -> bool.
Notation "t1 '<=[' ks ] t2" := (seq_le ks t1 t2)
  (at level 10, format "t1  '<=[' ks ]  t2").
Notation "t1 '<[' ks ] t2" := (seq_lt ks t1 t2)
  (at level 10, format "t1  '<[' ks ]  t2").
Parameter seqle_unlock : forall (A : eqType) ks (t1 t2 : A),
  t1 <=[ks] t2 = (index t1 ks <= index t2 ks)%N.
Parameter seqlt_unlock : forall (A : eqType) ks (t1 t2 : A),
  t1 <[ks] t2 = (index t1 ks < index t2 ks)%N.
End SeqOrdTp.

Module SeqOrd : SeqOrdTp.
Section SeqOrd.
Variables (A : eqType) (ks : seq A) (t1 t2 : A).
Definition seq_le := (index t1 ks <= index t2 ks)%N.
Definition seq_lt := (index t1 ks < index t2 ks)%N.
Definition seqle_unlock := erefl seq_le.
Definition seqlt_unlock := erefl seq_lt.
End SeqOrd.
End SeqOrd.
Export SeqOrd.

(* alternative rewrites that drop %N *)
Lemma seqle_unlockE (A : eqType) ks (t1 t2 : A) : 
        t1 <=[ks] t2 = (index t1 ks <= index t2 ks).
Proof. exact: seqle_unlock. Qed.

Lemma seqlt_unlockE (A : eqType) ks (t1 t2 : A) : 
        t1 <[ks] t2 = (index t1 ks < index t2 ks).
Proof. exact: seqlt_unlock. Qed.

Section SeqLeBase.
Variable (A : eqType).
Implicit Type (ks : seq A).

(* relating to mathcomp's mem2 *)
Lemma sle_mem2 ks t1 t2 : 
        uniq ks ->
        mem2 ks t1 t2 = (t1 <=[ks] t2) && (t2 \in ks).
Proof.
move=>U; apply/idP/idP. 
- move=>H; rewrite (mem2r H) andbT; case/splitP2r: H U=>p1 p2. 
  rewrite inE cat_uniq /= negb_or -!andbA => H /and5P [U1 U2 /hasPn U3 U4 U5].
  rewrite seqle_unlock !index_cat (negbTE U2) /= eqxx eq_sym.
  case: (t2 =P t1) H=>[-> _|_ H]; first by rewrite (negbTE U2).
  by rewrite (negbTE (U3 _ H)) addn0 leq_addr. 
case/andP=>H1 H2; case/splitPr: H2 U H1=>p1 p2.
rewrite cat_uniq /= negb_or -!andbA; case/and5P=>U1 U2 /hasPn U3 U4 U5.
rewrite seqle_unlock /mem2 /= !index_cat (negbTE U2) /= eqxx.
case: ifPn=>T1; first by rewrite drop_cat index_mem T1 mem_cat inE eqxx orbT.
case: ifPn=>N; first by rewrite drop_cat addn0 ltnn subnn /= inE eqxx.
by rewrite addn0 leqNgt -addSnnS ltn_addr.
Qed.

(****************** transitivity ****************)

Lemma sle_trans ks : transitive (seq_le ks).
Proof. by move=>y x z; rewrite !seqle_unlock; apply: leq_trans. Qed.

Lemma slt_trans ks : transitive (seq_lt ks).
Proof. by move=>y x z; rewrite !seqlt_unlock; apply: ltn_trans. Qed.

Lemma sle_slt_trans ks t1 t2 t3 :
        t1 <=[ks] t2 -> t2 <[ks] t3 -> t1 <[ks] t3.
Proof. by rewrite !seqlt_unlock !seqle_unlock; apply: leq_ltn_trans. Qed.

Lemma slt_sle_trans ks t1 t2 t3 :
        t1 <[ks] t2 -> t2 <=[ks] t3 -> t1 <[ks] t3.
Proof. by rewrite !seqlt_unlock !seqle_unlock; apply: leq_trans. Qed.


(****************** reflexivity ****************)

Lemma sle_refl ks : reflexive (seq_le ks).
Proof. by move=>x; rewrite seqle_unlock. Qed.

(****************** irreflexivity ***************)

Lemma slt_irr x ks : x <[ks] x = false.
Proof. by rewrite seqlt_unlock; apply: ltnn. Qed.

(* non-equational variant *)
Lemma sltnn x ks : ~ x <[ks] x.
Proof. by rewrite slt_irr. Qed.

(****************** antisymmetry ****************)

Lemma sle_antisym ks : {in ks, antisymmetric (seq_le ks)}.
Proof.
move=>x Hx y; rewrite !seqle_unlock.
by rewrite -eqn_leq =>/eqP /inj_index; apply.
Qed.

(****************** asymmetry ***************)

Lemma slt_asym x y ks : x <[ks] y -> ~~ y <[ks] x.
Proof. by rewrite !seqlt_unlock; case: ltngtP. Qed.

(***************** totality ********************)

Lemma sle_total ks x y : x <=[ks] y || y <=[ks] x.
Proof. by rewrite !seqle_unlock; case: ltngtP. Qed.

Lemma slt_total ks x y : 
        x \in ks -> 
        [|| x == y, x <[ks] y | y <[ks] x].
Proof.
rewrite !seqlt_unlock=>H; case: ltngtP; rewrite ?orbT ?orbF //.
by move/inj_index=>->.
Qed.

(* transfer properties of sequence ordering *)

(****************** sle_eqVlt ***************)

Lemma sle_eqVlt ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <=[ks] t2 = (t1 == t2) || (t1 <[ks] t2).
Proof.
move=>H; rewrite seqlt_unlock seqle_unlock leq_eqVlt /=.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(inj_index H)/N.
by move/esym/(inj_index H)/esym/N.
Qed.

(****************** slt_neqAle ***************)

Lemma slt_neqAle ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <[ks] t2 = (t1 != t2) && (t1 <=[ks] t2).
Proof.
move=>H.
rewrite seqlt_unlock seqle_unlock ltn_neqAle.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(inj_index H)/N.
by move/esym/(inj_index H)/esym/N.
Qed.

(****************** sltNge ***************)

Lemma sltNge ks t1 t2 : t1 <[ks] t2 = ~~ t2 <=[ks] t1.
Proof. by rewrite seqlt_unlock seqle_unlock ltnNge. Qed.

(****************** sleNgt ***************)

Lemma sleNgt ks t1 t2 : t1 <=[ks] t2 = ~~ t2 <[ks] t1.
Proof. by rewrite sltNge negbK. Qed.

(* order properties of the sequence orderings *)

(****************** slt_neq ***************)

Corollary slt_neq x y ks : x <[ks] y -> x != y.
Proof. by apply/contraL=>/eqP->; rewrite slt_irr. Qed.

End SeqLeBase.

#[export] Hint Resolve sle_refl : core.

Section SeqLeProp.
Variable (A : eqType).
Implicit Type (ks : seq A).

Lemma sltW ks t1 t2 : t1 <[ks] t2 -> t1 <=[ks] t2.
Proof. by rewrite seqlt_unlock seqle_unlock; apply: ltnW. Qed.

(* membership properties of the sequence orderings *)

Lemma slt_memI x y ks : x \in ks -> y \notin ks -> x <[ks] y.
Proof. by move=>X /index_memN E; rewrite seqlt_unlock E index_mem. Qed.

Lemma sle_memI x y ks : y \notin ks -> x <=[ks] y.
Proof. by move/index_memN=>E; rewrite seqle_unlock E index_size. Qed.

Lemma slt_memE x y ks : x <[ks] y -> x \in ks.
Proof. 
rewrite seqlt_unlock -index_mem=>/leq_trans.
by apply; rewrite index_size. 
Qed.

Lemma sle_memE x y ks : x <=[ks] y -> y \in ks -> x \in ks.
Proof. by rewrite seqle_unlock -!index_mem; apply: leq_ltn_trans. Qed.

(* sequence orderings and constructors *)

Lemma slt_nil x y : x <[Nil A] y = false. 
Proof. by rewrite seqlt_unlock. Qed.
Lemma sle_nil x y : x <=[Nil A] y. 
Proof. by rewrite seqle_unlock. Qed.

(* cons *)

Lemma slt_cons x y k ks :
        x <[k :: ks] y = (y != k) && ((x == k) || (x <[ks] y)).
Proof. by rewrite !seqlt_unlock /= !(eq_sym k); case: eqP; case: eqP. Qed.

Lemma sle_cons x y k ks :
        x <=[k :: ks] y = (x == k) || (y != k) && x <=[ks] y.
Proof. by rewrite sleNgt slt_cons negb_and negbK negb_or -sleNgt. Qed.

Lemma sltL x y ks : x <[x :: ks] y = (y != x).
Proof. by rewrite slt_cons eq_refl andbT. Qed.

Lemma sleL x y ks : x <=[x :: ks] y.
Proof. by rewrite sle_cons eq_refl. Qed.

Lemma sltR x y ks : x <[y :: ks] y = false.
Proof. by rewrite sltNge sleL. Qed.

Lemma sleR x y ks : x <=[y :: ks] y = (y == x).
Proof. by rewrite sleNgt sltL negbK. Qed.

(* sequence ordering and head *)

Lemma sle_head x ks y : (head x ks) <=[ks] y.
Proof. 
case: ks=>[|k ks] /=; first by rewrite sle_nil.
by rewrite sleL. 
Qed.

(* sequence orderings and rcons *)

Lemma slt_rcons x y k ks :
        x <[rcons ks k] y = if y \in ks then x <[ks] y
                            else (x \in ks) || (k != y) && (k == x).
Proof.
rewrite !seqlt_unlock !index_rcons.
case X: (x \in ks); case Y: (y \in ks)=>//=.
- by case: eqP; [rewrite index_mem | rewrite ltnS index_size].
- move/negbT/index_memN: X=>X; rewrite [LHS]ltnNge [RHS]ltnNge.
  rewrite X index_size /=.
  case: eqP=>//; first by rewrite index_size.
  by rewrite ltnW // ltnS index_size.
rewrite !(eq_sym k).
case: eqP=>_; case: eqP=>_ /=.
- by rewrite ltnn.
- by rewrite ltnS leqnn.
- by rewrite ltnNge leqnSn.
by rewrite ltnn.
Qed.

Lemma sle_rcons x y k ks :
        x <=[rcons ks k] y = if x \in ks then x <=[ks] y
                             else (y \notin ks) && ((k == x) || (k != y)).
Proof.
by rewrite !sleNgt slt_rcons; case: ifP=>//; rewrite negb_or negb_and negbK.
Qed.

(* some shortcuts for slt/sle_rcons *)

Lemma slt_rconsI x y k ks : x <[ks] y -> x <[rcons ks k] y.
Proof. by move=>H; rewrite slt_rcons H (slt_memE H) if_same. Qed.

Lemma sle_rconsI x y k ks : k != y -> x <=[ks] y -> x <=[rcons ks k] y.
Proof.
move=>N H; rewrite sle_rcons H N orbT andbT.
case: ifP=>// K; apply: contraFT K.
by rewrite negbK; apply: sle_memE H.
Qed.

Lemma slt_rcons_in x y k ks :
        x \in ks -> x <[rcons ks k] y = x <[ks] y.
Proof.
move=>H; rewrite slt_rcons H /=; case: ifP=>// K.
by apply/esym; apply: slt_memI=>//; rewrite K.
Qed.

Lemma sle_rcons_in x y k ks :
        x \in ks -> x <=[rcons ks k] y = x <=[ks] y.
Proof. by move=>X; rewrite sle_rcons X. Qed.

Lemma slt_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <[rcons ks k1] y = x <[rcons ks k2] y.
Proof. by rewrite !slt_rcons=>/orP [] ->. Qed.

Lemma sle_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <=[rcons ks k1] y = x <=[rcons ks k2] y.
Proof. by rewrite !sle_rcons=>/orP [] ->. Qed.

Lemma slt_rconsR ks x k : x <[rcons ks k] k -> x \in ks.
Proof. by rewrite slt_rcons eq_refl orbF; case: ifP=>[_ /slt_memE|]. Qed.

Lemma sle_rconsR ks x k : x <=[rcons ks k] k -> x \in rcons ks k.
Proof.
rewrite sle_rcons eq_refl orbF mem_rcons inE.
case X: (x \in ks); first by rewrite orbT.
by rewrite orbF eq_sym; case/andP.
Qed.

(* sequence orderings and concatenation *)
Lemma sle_cat ks1 ks2 x y :
        x <=[ks1++ks2] y = if x \in ks1 then x <=[ks1] y
                           else (y \notin ks1) && x <=[ks2] y.
Proof.
rewrite !seqle_unlock !index_cat.
case X: (x \in ks1); case Y: (y \in ks1)=>//=.
- move/negbT/index_memN: Y=>Y.
  by rewrite Y index_size ltnW // ltn_addr // index_mem.
- rewrite -index_mem in Y.
  apply/negP=>H; move/(leq_ltn_trans H): Y.
  by rewrite ltnNge leq_addr.
by rewrite leq_add2l.
Qed.

Lemma slt_cat ks1 ks2 x y :
        x <[ks1++ks2] y = if y \in ks1 then x <[ks1] y
                          else (x \in ks1) || x <[ks2] y.
Proof. by rewrite !sltNge sle_cat; case: ifP=>//; rewrite negb_and negbK. Qed.

(* shortcuts *)

Lemma slt_catL ks1 ks2 x y : x <[ks1] y -> x <[ks1++ks2] y.
Proof. by move=>H; rewrite slt_cat H (slt_memE H) if_same. Qed.

Lemma slt_splitR x y ks1 ks2 : y != x -> y \notin ks1 -> x <[ks1++x::ks2] y.
Proof.
by move=>N Y; rewrite slt_cat slt_cons eq_refl andbT (negbTE Y) N orbT.
Qed.

Lemma sle_splitR x y ks1 ks2 : y \notin ks1 -> x <=[ks1++x::ks2] y.
Proof.
move=>Y; rewrite sle_eqVlt.
- by apply/orP; left; rewrite mem_cat inE eq_refl orbT.
by case: eqP=>[|/eqP N] //=; rewrite (slt_splitR _ _ Y) // eq_sym.
Qed.

(* the other direction of slt_splitR, further strenghtened *)
(* with an additional fact that x \notin ks1 *)
(* by picking a split with the first occurrence of x *)
(* in fact, we can have both directions here, so we prove a reflect lemma *)
(* but it should really only be used in the direction x <[ks] y -> .. *)
(* because in the other direction slt_splitR is already stronger. *)
Lemma slt_splitL ks x y :
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2, x != y,
                                     x \notin ks1 & y \notin ks1])
                (x <[ks] y).
Proof.
case H : (x <[ks] y); constructor; last first.
- apply/contraFnot: H; case=>ks1 [ks2][-> N _].
  by apply: slt_splitR; rewrite eq_sym.
rewrite seqlt_unlock in H.
have : x \in ks by rewrite -index_mem (leq_trans H _) // index_size.
case/in_split=>ks1 [ks2][E X]; exists ks1, ks2.
rewrite /seq_lt {ks}E !index_cat /= eq_refl in H *.
case: eqP H=>[->|/eqP N] /=; first by rewrite ltnn.
rewrite (negbTE X) addn0; case: ifP=>//= _.
by rewrite ltnNge index_size.
Qed.

(* ditto for ole_split *)
Lemma sle_splitL ks x y :
        x \in ks ->
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2,
                                     x \notin ks1 & y \notin ks1])
                (x <=[ks] y).
Proof.
move=>X; case H : (x <=[ks] y); constructor; last first.
- apply/contraFnot: H; case=>ks1 [ks2][-> _ N].
  by apply: sle_splitR.
case/in_split: X=>ks1 [ks2][E X]; exists ks1, ks2; split=>//.
rewrite seqle_unlock {ks}E !index_cat /= eq_refl (negbTE X) addn0 in H.
by case: ifP H=>//; rewrite -index_mem; case: ltngtP.
Qed.

(* sequence orderings and filter *)

Lemma slt_filterL (p : pred A) ks x y :
         (x \notin ks) || p x ->
         x <[ks] y -> x <[filter p ks] y.
Proof. by rewrite !seqlt_unlock; apply: index_filter_ltL. Qed.

Lemma sle_filterL (p : pred A) ks x y :
        (x \notin ks) || p x ->
        x <=[ks] y -> x <=[filter p ks] y.
Proof. by rewrite !seqle_unlock; apply: index_filter_leL. Qed.

Lemma slt_filterR (p : pred A) ks x y :
        (y \notin ks) || p y ->
        x <[filter p ks] y -> x <[ks] y.
Proof. by rewrite !seqlt_unlock; apply: index_filter_ltR. Qed.

Lemma sle_filterR (p : pred A) ks x y :
        (y \notin ks) || p y ->
        x <=[filter p ks] y -> x <=[ks] y.
Proof. by rewrite !seqle_unlock; apply: index_filter_leR. Qed.

Lemma slt_filter (p : pred A) ks x y :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <[filter p ks] y = x <[ks] y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: slt_filterR | apply: slt_filterL].
Qed.

Lemma sle_filter (p : pred A) ks x y :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <=[filter p ks] y = x <=[ks] y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: sle_filterR | apply: sle_filterL].
Qed.

(* sequence orderings and sortedness *)

(* slt/sle under general sorted relations *)
Lemma slt_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <[ks] y -> ltT x y.
Proof. by rewrite seqlt_unlock; apply: sorted_index_ord. Qed.

Lemma sle_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <=[ks] y -> (x == y) || ltT x y.
Proof.
move=>T S Y; rewrite sle_eqVlt; first by rewrite Y orbT.
by case/orP=>[->//|/(slt_sorted_lt T S Y) ->]; rewrite orbT.
Qed.

(* we can get the other direction as well *)
(* if we add antisymmetry *)
(* and the condition that x \in ks *)
Lemma slt_sorted_leE leT ks x y :
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        x \in ks -> y \in ks ->
        x <[ks] y = (x != y) && leT x y.
Proof.
move=>As T S X Y; apply/idP/idP.
- case: eqP=>[->|/eqP N] /=; 
  by [apply: contraLR; rewrite slt_irr|apply: slt_sorted_lt].
by rewrite seqlt_unlock; case/andP=>H K; apply: sorted_ord_index_leq K H.
Qed.

(* if we add antisymmetry and t1 \in ks *)
Lemma sle_sorted_leE leT ks x y :
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        x \in ks -> y \in ks ->
        x <=[ks] y = (x == y) || leT x y.
Proof.
move=>As T S X Y; rewrite sle_eqVlt; first by rewrite X.
by rewrite (slt_sorted_leE As T S X Y); case: eqP.
Qed.

End SeqLeProp.

#[export] Hint Resolve slt_nil sle_nil : core.


Section SeqLeUniq.
Variable (A : eqType).
Implicit Type (ks : seq A).

Lemma slt_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <[ks1] t = k <[ks2] t.
Proof. 
rewrite !seqlt_unlock=>S U T K.
by apply/idP/idP=>/(index_subseq S U T K). 
Qed.

Lemma sle_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <=[ks1] t = k <=[ks2] t.
Proof. by move=>S U T K; rewrite !sleNgt (slt_subseq S U K T). Qed.

(* sequence orderings and last *)

Lemma sle_last x k ks :
        uniq ks -> x \in ks -> x <=[ks] (last k ks).
Proof. by rewrite seqle_unlock; apply: index_last_mono. Qed.

Lemma sle_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks -> x <=[k::ks] (last k ks).
Proof.
move=>/= /andP [U1 U2].
rewrite inE sle_cons; case: eqP=>//= /eqP Nxk K.
by rewrite (last_notin K) //=; apply: sle_last.
Qed.

Lemma slt_last x k ks :
        uniq ks -> x \in ks -> last k ks != x -> x <[ks] (last k ks).
Proof.
move=>U X N; move: (sle_last k U X); rewrite sle_eqVlt; first by rewrite X.
by rewrite eq_sym (negbTE N).
Qed.

Lemma slt_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks ->
        last k ks != x -> x <[k::ks] (last k ks).
Proof.
move=>U X N; rewrite slt_neqAle; first by rewrite X.
by rewrite eq_sym N sle_last_cons.
Qed.

(* switching sorted between seq_lt and seq_le *)
Lemma sorted_slt_sle xs ks : 
        uniq ks ->
        {subset xs <= ks} ->
        sorted (seq_lt ks) xs = uniq xs && sorted (seq_le ks) xs.
Proof.
elim: xs=>[|x xs IH] //= Uq S.
rewrite (path_sortedE (@slt_trans A _)) (path_sortedE (@sle_trans A _)).
rewrite IH //; first by move=>z Z; rewrite S // inE Z orbT. 
rewrite -andbA; apply/and3P/and4P.
- case=>/allP H ->->; split=>//.
  - by apply/negP=>/H; rewrite slt_irr. 
  by apply/allP=>z /H/sltW. 
case=>H1 -> /allP H2 ->; split=>//.
apply/allP=>z /[dup] Z /H2 X.
have Oz : z \in ks by rewrite S // inE Z orbT. 
rewrite slt_neqAle ?Oz ?orbT //=.
by case: eqP Z H1=>// ->->.
Qed.

(* every list is sorted by its slt relation, assuming uniqueness *)

Lemma sorted_slt_subseq xs ks : 
        uniq ks ->
        {subset xs <= ks} ->
        sorted (seq_lt ks) xs = subseq xs ks.
Proof.
move: {-2}ks xs (subseq_refl ks); elim: ks=>[|k ks IH] ys xs //=.
- by move/eqP=>->; case: xs=>[|x xs] //= _ /(_ x (mem_head _ _)).
case: ys=>[|y ys] Sq /=; first by case: xs=>[|x xs] //= _ /(_ x (mem_head _ _)).
have {}Sq : subseq ys ks by case: eqP Sq=>// _ /cons_subseq.
case: xs=>[|x xs] //= /andP [Ny Uq] S; rewrite (path_sortedE (@slt_trans A _)).
apply/andP/idP.
- case=>/allP H Sq2.
  have Nyxs : y \notin xs by apply/negP=>/H; rewrite slt_cons eqxx.
  have S1 : (x == y) || (x \in ys) by apply/S/mem_head.
  have {}S : {subset xs <= ys}.
  - move=>z /[dup] Z; move: (S z (subset_consR x Z)) Nyxs. 
    by case/orP=>// /eqP -> /negbTE ->.
  have Nz : {in xs, forall z, z != y}.
  - by move=>z /S; case: eqP=>// ->; rewrite (negbTE Ny).
  rewrite -IH //; first by case: eqP S1=>//= _ S1 z; rewrite inE=>/orP [/eqP ->|/S].
  suff : sorted (seq_lt ys) xs.
  - case: eqP=>[|/eqP Nxy] //=; rewrite path_min_sorted //.
    by apply/allP=>z /H; rewrite slt_cons (negbTE Nxy); case: (z =P y). 
  rewrite (eq_in_sorted (e':=seq_lt (y::ys)) (P:=[mem xs])) //.  
  by move=>z z'; rewrite !inE=>Z Z'; rewrite slt_cons (negbTE (Nz _ Z)) /= (Nz _ Z').
move=>Sq2.
have S1 : (x == y) || (x \in ys) by apply/S/mem_head.
have {}S : {subset xs <= ys}.
- case: eqP S1 Sq2 S=>[->|/eqP N] /= S1 Sq2 S.
  - by apply/mem_subseq.
  by move=>z Z; apply/(mem_subseq Sq2); rewrite inE Z orbT.
have Nz : {in xs, forall z, z != y}.
- by move=>z /S; case: eqP=>// ->; rewrite (negbTE Ny).
split.
- apply/allP=>z Z; rewrite slt_cons (Nz _ Z) /=.
  case: eqP S1 Sq2=>[|/eqP N] //= S1 Sq2.
  case/split_subseq: {S Sq S1 Ny} Sq2 Uq=>a1 [a2][->{ys}] /mem_subseq S Uq.
  rewrite slt_cat slt_cons eqxx andbT; move: Uq; rewrite cat_uniq /= negb_or -andbA.
  case/and4P=>_ /negbTE -> /hasPn/(_ z (S _ Z)) /negbTE ->.
  by case: eqP=>// <-; rewrite (S _ Z).
rewrite -IH // in Sq2.
- by case: eqP S1=>//= _ S1 z; rewrite inE=>/orP [/eqP ->|/S].
have {}Sq2 : sorted (seq_lt ys) xs.
- by case: eqP Sq2=>//= _ /path_sorted.
rewrite (eq_in_sorted (e':=seq_lt ys) (P:=[mem xs])) //.  
by move=>z z'; rewrite !inE=>Z Z'; rewrite slt_cons (negbTE (Nz _ Z)) (Nz _ Z').
Qed.

Lemma sorted_slt ks : uniq ks -> sorted (seq_lt ks) ks.
Proof. by move=>U; rewrite sorted_slt_subseq. Qed.

Lemma sorted_sle_subseq xs ks : 
        uniq ks -> 
        {subset xs <= ks} ->
        subseq xs ks = uniq xs && sorted (seq_le ks) xs.
Proof. by move=>U S; rewrite -sorted_slt_sle ?sorted_slt_subseq. Qed.

Lemma sorted_sle ks : uniq ks -> sorted (seq_le ks) ks.
Proof.
move=>U; apply: sub_sorted (sorted_slt U).
by move=>x y /sltW.
Qed.

Lemma slt_sorted (ord : rel A) ks x y :
        transitive ord ->
        sorted ord ks -> y \in ks -> x <[ks] y -> ord x y.
Proof. by move=>T; apply/slt_sorted_lt/T. Qed.

Lemma slt_sortedI (ord : rel A) ks : 
        uniq ks ->
        (forall x y, y \in ks -> x <[ks] y -> ord x y) ->
        sorted ord ks.
Proof. 
elim: ks=>[|k ks IH] //= /andP [Nk U] H.
rewrite path_min_sorted.
- apply/allP=>x X; apply: H; first by rewrite inE X orbT.
  by rewrite slt_cons eqxx andbT; case: eqP X Nk=>// ->->.
apply: IH=>// x y Y N; apply: H; first by rewrite inE Y orbT.
by rewrite slt_cons N orbT andbT; case: eqP Y Nk=>// ->->.
Qed.

Lemma slt_sortedE (ord : rel A) ks x y :
        irreflexive ord ->
        transitive ord ->
        sorted ord ks ->
        x \in ks -> y \in ks ->
        x <[ks] y = ord x y.
Proof.
move=>I T S X Y; apply/idP/idP; first by apply: slt_sorted S Y.
by rewrite seqlt_unlock; apply: (sorted_ord_index I T S X).
Qed.

Lemma subseq_eq (s1 s2 xs : seq A) : 
        uniq xs ->
        subseq s1 xs ->
        subseq s2 xs ->
        s1 =i s2 ->
        s1 = s2.
Proof.
move=>Uq S1 S2 E; apply: (sorted_eq (leT:=seq_lt xs)).
- by apply: slt_trans.
- by move=>x y /andP [] H /(slt_trans H); rewrite slt_irr. 
- by rewrite sorted_slt_subseq //; apply/mem_subseq.
- by rewrite sorted_slt_subseq //; apply/mem_subseq.
by apply/uniq_perm/E; apply/subseq_uniq/Uq.
Qed.

End SeqLeUniq.

(* ole and sortedness under ordering on A *)

Section SeqLeOrd.
Variable (A : ordType).
Implicit Type (ks : seq A).

Lemma sle_sorted ks x y :
        sorted ord ks -> y \in ks -> x <=[ks] y -> oleq x y.
Proof. by rewrite oleq_eqVord; apply/sle_sorted_lt/trans. Qed.

Lemma sle_sortedI ks : 
        uniq ks ->
        (forall x y, y \in ks -> x <=[ks] y -> oleq x y) ->
        sorted ord ks.
Proof.
move=>Uq H; apply: slt_sortedI=>// x y Dy N.
move: (H x y Dy (sltW N)); rewrite oleq_eqVord.
by case: eqP N=>// ->; rewrite slt_irr.
Qed.

Lemma sle_sortedE ks x y :
        sorted ord ks ->
        x \in ks -> y \in ks ->
        x <=[ks] y = oleq x y.
Proof. 
move=>S X Y; rewrite oleqNord sleNgt.
by rewrite (slt_sortedE (@irr _) (@trans _) S Y X). 
Qed.

End SeqLeOrd.

(* split_findlast in terms of <[s] *)

Lemma slt_findlast {A : eqType} (p : pred A) (s : seq A) :
        uniq s ->
        has p s -> 
        exists x, [/\ x \in s, p x &
          forall z, z \in s -> x <[s] z -> ~~ p z].
Proof.
move=>Us H.
case: {-1}s {-3}_ {-6}_ / {H} (split_findlast H) (erefl s).
move=>x s1 s2 Px /hasPn /= S2 E; exists x.
rewrite mem_cat mem_rcons inE eqxx /=; split=>//.
move=>z; rewrite mem_cat mem_rcons inE -orbA.
case/or3P=>[/eqP ->|Z|/S2//]; first by rewrite slt_irr.
rewrite slt_cat mem_rcons inE Z orbT slt_rcons Z=>/slt_memE.
rewrite E cat_uniq rcons_uniq -andbA in Us.
by case/and4P: Us=>/negbTE ->.
Qed.

Lemma slt_filterlast {A : eqType} (p q : pred A) (s : seq A) :
        uniq s ->
        has p (filter q s) -> 
        exists x, [/\ x \in s, p x, q x &
          forall z, z \in s -> x <[s] z -> q z -> ~~ p z].
Proof.
move=>Us; rewrite has_filterI.
case/(slt_findlast Us)=>x [X] /andP [H1 H2] Y.
exists x; split=>//= z Z /(Y z Z). 
by rewrite negb_and; case/orP=>// /negbTE ->.
Qed.

Lemma has_first {A : eqType} (xs : seq A) f : 
        has f xs ->
        exists x, [/\ x \in xs, f x & 
          forall x', x' <[xs] x -> ~~ f x'].
Proof.
case/has_first_split=>x [p1][p2][-> H1 H2]; exists x.
split=>[|//|y]; first by rewrite mem_cat mem_rcons inE eqxx.
by rewrite slt_cat mem_rcons inE eqxx /= =>/slt_rconsR/(hasPn H2).
Qed.

(* prefixes is ordered monotonically *)
Lemma prefixes_mono {A : eqType} (s : seq A) xs ys :  
        xs \in prefixes s ->
        ys <=[prefixes s] xs = prefix ys xs.
Proof.
elim: s xs ys=>[|x s IH] /= xs ys; rewrite inE.
- by move/eqP=>->; rewrite sle_cons eqxx orbF; case: ys.
case/orP=>[/eqP ->|/mapP [x0 X0 ->]].
- by rewrite sle_cons eqxx orbF; case: ys {IH}.
rewrite sle_cons /=; case: ys=>[|y ys] //=.
have I : injective (cons x) by move=>x1 x2 [].
apply/idP/idP; last first.
- case/andP=>/eqP ->{y} P. 
  by rewrite seqle_unlock !index_map // -seqle_unlock IH.
rewrite seqle_unlock index_map //; move=>H.
have : y :: ys \in [seq x :: i | i <- prefixes s].
- rewrite -!index_mem in X0 *; rewrite size_map. 
  by apply: leq_ltn_trans H X0.
case/mapP=>x1 X2 [??]; subst y x1; rewrite eqxx /= -IH //.
by rewrite seqle_unlock (leq_trans _ H) // index_map.
Qed.

(* sequence orderings and map/pmap *)

Section SeqLeLtMap.
Context {A B : ordType}.
Implicit Type ks : seq A.

(* map *)

Lemma slt_map (f : A -> B) ks x' y : 
        x' <[map f ks] (f y) ->
        exists2 x, f x = x' & x <[ks] y.
Proof. 
case Dy : (y \in ks); last first.
- move=>N; case/mapPP: (slt_memE N)=>x -> /mem_seqP Dx.
  by exists x=>//; rewrite slt_memI // Dy. 
elim: ks Dy=>[|k ks IH] //=; rewrite inE !slt_cons.
case: (y =P k)=>[<-{k}|/eqP Ny]; first by rewrite eqxx.
move=>Dy /andP [Nf] /orP [/eqP ->|].
- by exists k=>//; rewrite slt_cons Ny eqxx.
by case/(IH Dy)=>x <- N; exists x=>//; rewrite slt_cons Ny N orbT.
Qed.

Lemma slt_map_inj (f : A -> B) ks x y : 
        {in ks, forall x, f x = f y -> x = y} ->
        x <[ks] y ->
        (f x) <[map f ks] (f y).
Proof.
case Dy : (y \in ks); last first.
- move=>H1 H2; apply: slt_memI; apply/mapP.
  - by exists x=>//; apply: (slt_memE H2).
  by case=>z Z /esym N; move/(H1 _ Z): N (Z) Dy=>->->.
elim: ks Dy=>[|k ks IH] //=; rewrite inE !slt_cons. 
case: (y =P k)=>[<-{k}|/eqP N] //= Dy H X; rewrite (_ : f y != f k) /=.
- by apply: contra N=>/eqP/esym/H -> //; rewrite inE eqxx.
case/orP: X N H=>[/eqP ->|Nxy] N H; first by rewrite eqxx.
by rewrite IH ?orbT // => z Z /H -> //; rewrite inE Z orbT.
Qed.

Lemma sle_map (f : A -> B) ks x' y : 
        x' \in map f ks ->
        x' <=[map f ks] (f y) ->
        exists2 x, f x = x' & x <=[ks] y.
Proof.
move=>Dx; rewrite sle_eqVlt ?Dx //; case/orP=>[/eqP ->|].
- by exists y=>//; rewrite sle_refl.
by case/slt_map=>x <- /sltW; exists x.
Qed.

Lemma sle_map_inj (f : A -> B) ks x y : 
        {in ks, forall x, f x = f y -> x = y} ->
        x <=[ks] y ->
        (f x) <=[map f ks] (f y).
Proof.
move=>H; case Dy : (y \in ks); last first.
- move=>N; apply/sle_memI/mapP; case=>z Z E.
  by move/esym/(H _ Z): E (Z) Dy=>->->.
rewrite sle_eqVlt ?Dy ?orbT //.
case/orP=>[/eqP ->|]; first by rewrite sle_refl. 
by move/(slt_map_inj H)/sltW. 
Qed.

(* pmap *)

Lemma slt_pmap (f : A -> option B) ks x' y' y : 
        f y = Some y' ->
        x' <[pmap f ks] y' ->
        exists2 x, f x = Some x' & x <[ks] y.
Proof.
rewrite seqlt_unlock=>H /(index_pmap H) [x]. 
by exists x=>//; rewrite seqlt_unlock.
Qed.

Lemma slt_pmap_inj (f : A -> option B) ks x y x' y' : 
        {in ks, forall x, f x = Some y' -> x = y} ->
        x <[ks] y ->
        f x = Some x' ->
        f y = Some y' ->
        x' <[pmap f ks] y'.
Proof. by rewrite !seqlt_unlock; apply: index_pmap_inj. Qed.

Lemma sle_pmap (f : A -> option B) ks x' y' y : 
        x' \in pmap f ks ->
        f y = Some y' ->
        x' <=[pmap f ks] y' ->
        exists2 x, f x = Some x' & x <=[ks] y.
Proof.
move=>Dx' Y; rewrite sle_eqVlt ?Dx' //.
case/orP=>[/eqP ->|]; first by exists y=>//; rewrite sle_refl.
by case/(slt_pmap Y)=>x <- /sltW; exists x.
Qed.

Lemma sle_pmap_inj (f : A -> option B) ks x y x' y' : 
        {in ks, forall x, f x = Some y' -> x = y} ->
        x <=[ks] y ->
        f x = Some x' ->
        f y = Some y' ->
        x' <=[pmap f ks] y'.
Proof.
move=>H; case Dy: (y \in ks); last first.
- move=>N X Y; apply/sle_memI/pmapPP; case=>z E /mem_seqP Z. 
  by move/(H _ Z): E (Z) Dy=>->->.
rewrite sle_eqVlt ?Dy ?orbT //.
case/orP=>[/eqP ->-> [->]|]; first by rewrite sle_refl. 
by move=>N X /(slt_pmap_inj H N X)/sltW.
Qed.

End SeqLeLtMap.

