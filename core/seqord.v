From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype slice seqext.

Open Scope order_scope.
Import Order.Theory.

(***********************************)
(***********************************)
(* Sequence-induced ordering       *)
(* definition and basic properties *)
(***********************************)
(***********************************)

(* x <[ks[ y if first x appears to the left of last y in the sequence ks *)

(* It turns out it's useful to have 0 <[ks[ x, for every x. *)
(* Basically, we use these orderings for reasoning about *)
(* timestamps in histories, and we always keep the null timestamp *)
(* to stand for the initialization step *)
(* That said, the null timestamp is never in any history as *)
(* the initialization step is implicit *)

Definition seq_le {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (index t1 ks <= index t2 ks)%N.

Definition seq_lt {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (index t1 ks < index t2 ks)%N.

Notation "t1 '<=[' ks [ t2" := (seq_le ks t1 t2)
  (at level 10, format "t1  '<=[' ks [  t2").

Notation "t1 '<[' ks [ t2" := (seq_lt ks t1 t2)
  (at level 10, format "t1  '<[' ks [  t2").

(*
Definition seq_le_fl {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (index t1 ks <= indexlast t2 ks)%N.

Definition seq_lt_fl {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (index t1 ks < indexlast t2 ks)%N.

Notation "t1 '<=FL[' ks ] t2" := (seq_le_fl ks t1 t2)
  (at level 10, format "t1  '<=FL[' ks ]  t2").

Notation "t1 '<FL[' ks ] t2" := (seq_lt_fl ks t1 t2)
  (at level 10, format "t1  '<FL[' ks ]  t2").

Definition seq_le_lf {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (indexlast t1 ks <= index t2 ks)%N.

Definition seq_lt_lf {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (indexlast t1 ks < index t2 ks)%N.

Notation "t1 '<=LF[' ks ] t2" := (seq_le_lf ks t1 t2)
  (at level 10, format "t1  '<=LF[' ks ]  t2").

Notation "t1 '<LF[' ks ] t2" := (seq_lt_lf ks t1 t2)
  (at level 10, format "t1  '<LF[' ks ]  t2").
*)

Definition seq_le_l {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (indexlast t1 ks <= indexlast t2 ks)%N.

Definition seq_lt_l {A : eqType} (ks : seq A) (t1 t2 : A) :=
  (indexlast t1 ks < indexlast t2 ks)%N.

Notation "t1 '<=]' ks ] t2" := (seq_le_l ks t1 t2)
  (at level 10, format "t1  '<=]' ks ]  t2").

Notation "t1 '<]' ks ] t2" := (seq_lt_l ks t1 t2)
  (at level 10, format "t1  '<]' ks ]  t2").

(*
#[export]
Hint Resolve sle_refl : core.
*)

Section SeqLeEq.
Variable (A : eqType).
Implicit Type (ks : seq A).

(****************** transitivity ****************)

Lemma sle_trans ks : transitive (seq_le ks).
Proof. by move=>y x z; apply: leq_trans. Qed.

(*
(* degenerate transitivity for LE-FL! *)
Lemma sle_trans_fl y x z ks :
  (count_mem y ks <= 1)%N ->
  x <=FL[ks] y -> y <=FL[ks] z -> x <=FL[ks] z.
Proof.
rewrite /seq_le_fl; move=>/indexlast_count Hy Hxy Hyz.
apply/(leq_trans Hxy)/leq_trans/Hyz.
by rewrite Hy.
Qed.

Lemma sle_trans_lf ks : transitive (seq_le_lf ks).
Proof.
rewrite /seq_le_lf=>y x z Hxy Hyz.
apply/leq_trans/Hyz/(leq_trans Hxy).
by exact: index_leq_last.
Qed.
*)
Lemma sle_l_trans ks : transitive (seq_le_l ks).
Proof. by move=>y x z; apply: leq_trans. Qed.

Lemma slt_trans ks : transitive (seq_lt ks).
Proof. by move=>y x z; apply: ltn_trans. Qed.

Lemma sle_slt_trans ks t1 t2 t3 :
        t1 <=[ks[ t2 -> t2 <[ks[ t3 -> t1 <[ks[ t3.
Proof. by apply: leq_ltn_trans. Qed.

Lemma slt_sle_trans ks t1 t2 t3 :
        t1 <[ks[ t2 -> t2 <=[ks[ t3 -> t1 <[ks[ t3.
Proof. by apply: leq_trans. Qed.


(*
(* degenerate transitivity for LT-FL! *)
Lemma slt_trans_fl y x z ks :
  (count_mem y ks <= 1)%N ->
  x <FL[ks] y -> y <FL[ks] z -> x <FL[ks] z.
Proof.
rewrite /seq_lt_fl; move=>Hy Hxy Hyz.
apply/(ltn_trans Hxy)/leq_ltn_trans/Hyz.
by move/indexlast_count: Hy=>->.
Qed.

Lemma slt_trans_lf ks : transitive (seq_lt_lf ks).
Proof.
rewrite /seq_lt_lf.
move=>y x z Hxy Hyz.
apply/(ltn_trans Hxy)/leq_ltn_trans/Hyz.
by exact: index_leq_last.
Qed.
*)
Lemma slt_l_trans ks : transitive (seq_lt_l ks).
Proof. by move=>y x z; apply: ltn_trans. Qed.

Lemma sle_slt_l_trans ks t1 t2 t3 :
        t1 <=]ks] t2 -> t2 <]ks] t3 -> t1 <]ks] t3.
Proof. by apply: leq_ltn_trans. Qed.

Lemma slt_sle_l_trans ks t1 t2 t3 :
        t1 <]ks] t2 -> t2 <=]ks] t3 -> t1 <]ks] t3.
Proof. by apply: leq_trans. Qed.


(****************** reflexivity ****************)

Lemma sle_refl ks : reflexive (seq_le ks).
Proof. by rewrite /seq_le. Qed.

(*
Lemma sle_refl_fl ks : reflexive (seq_le_fl ks).
Proof. by rewrite /seq_le_fl=>x; apply: index_leq_last. Qed.

(* degenerate reflexivity for LE-LF! *)
Lemma sle_refl_lf ks t : (count_mem t ks <= 1)%N -> t <=LF[ks] t.
Proof. by move/indexlast_count=>H; rewrite /seq_le_lf H. Qed.
*)
Lemma sle_l_refl ks t : t <=]ks] t.
Proof. by rewrite /seq_le_l. Qed.
(*
(* degenerate reflexivity for LT-FL! *)
Lemma slt_refl_fl ks t : (1 < count_mem t ks)%N -> t <FL[ks] t.
Proof. by move/index_lt_last=>H; rewrite /seq_lt_fl. Qed.
*)
(****************** irreflexivity ***************)

Lemma slt_irr x ks : ~~ x <[ks[ x.
Proof. by rewrite /seq_lt ltnn. Qed.

(*
(* degenerate irreflexivity for LT-FL! *)
Lemma slt_irr_fl ks t : (count_mem t ks <= 1)%N -> ~~ t <FL[ks] t.
Proof. by move/indexlast_count=>H; rewrite /seq_lt_fl H ltnn. Qed.

Lemma slt_irr_lf x ks : ~~ x <LF[ks] x.
Proof. by rewrite /seq_lt_lf ltnNge index_leq_last. Qed.
*)
Lemma slt_l_irr x ks : ~~ x <]ks] x.
Proof. by rewrite /seq_lt_l ltnn. Qed.
(*
(* degenerate irreflexivity for LE-LF! *)
Lemma sle_irr_lf ks t : (1 < count_mem t ks)%N -> ~~ t <=LF[ks] t.
Proof. by move/index_lt_last=>H; rewrite /seq_le_lf -ltnNge. Qed.
*)
(****************** antisymmetry ****************)

Lemma sle_antisym ks : {in ks, antisymmetric (seq_le ks)}.
Proof.
rewrite /seq_le=>x Hx y.
by rewrite -eqn_leq =>/eqP /index_inj; apply.
Qed.

(*
(* degenerate antisymmetry for LE-FL! *)
Lemma sle_antisym_fl ks x y :
  (count_mem x ks == 1)%N -> (count_mem y ks <= 1)%N ->
  x <=FL[ks] y -> y <=FL[ks] x -> x = y.
Proof.
rewrite /seq_le_fl => H /indexlast_count<-.
have <-: index x ks = indexlast x ks.
- by apply/indexlast_count; rewrite (eqP H).
move=>Hx Hy.
have Hi: (x \in ks) by rewrite -has_pred1 has_count (eqP H).
by apply/(index_inj Hi)/eqP; rewrite eqn_leq Hx.
Qed.

Lemma sle_antisym_lf ks : {in ks, antisymmetric (seq_le_lf ks)}.
Proof.
rewrite /seq_le_lf=>x Hx y.
case/andP=>Hxy Hyx.
have /eqP Ex: index x ks == indexlast x ks.
- rewrite eqn_leq index_leq_last /=.
  by apply/leq_trans/Hyx/leq_trans/index_leq_last.
rewrite -{}Ex in Hxy.
have /eqP Ey: index y ks == indexlast y ks.
- rewrite eqn_leq index_leq_last /=.
  by apply/leq_trans/Hxy.
rewrite -{}Ey in Hyx.
suff: index x ks == index y ks by move/eqP/index_inj; apply.
by rewrite eqn_leq Hxy.
Qed.
*)
Lemma sle_l_antisym ks : {in ks, antisymmetric (seq_le_l ks)}.
Proof.
rewrite /seq_le_l=>x Hx y.
by rewrite -eqn_leq =>/eqP /indexlast_inj; apply.
Qed.

(****************** asymmetry ***************)

Lemma slt_asym x y ks : x <[ks[ y -> ~~ y <[ks[ x.
Proof. by rewrite /seq_lt; case: ltngtP. Qed.

(*
(* degenerate asymmetry for LT-FL! *)
Lemma slt_asym_fl ks x y :
  (count_mem x ks <= 1)%N -> (count_mem y ks <= 1)%N ->
  x <FL[ks] y -> ~~ y <FL[ks] x.
Proof.
rewrite /seq_lt_fl -leqNgt => /indexlast_count->/indexlast_count->.
by apply: ltnW.
Qed.

Lemma slt_asym_lf x y ks : x <LF[ks] y -> ~~ y <LF[ks] x.
Proof.
rewrite /seq_lt_lf -leqNgt => H.
apply: leq_trans; first by exact: index_leq_last.
apply: leq_trans; last by exact: index_leq_last.
by apply: ltnW.
Qed.
*)
Lemma slt_l_asym x y ks : x <]ks] y -> ~~ y <]ks] x.
Proof. by rewrite /seq_lt_l; case: ltngtP. Qed.
(*
(* degenerate asymmetry for LE-FL? *)
*)
(***************** totality ********************)

Lemma sle_total ks x y : x <=[ks[ y || y <=[ks[ x.
Proof. by rewrite /seq_le; case: ltngtP. Qed.

(*

Lemma sle_total_fl ks x y : x <=FL[ks] y || y <=FL[ks] x.
Proof.
rewrite /seq_le_fl; case/orP: (leq_total (index x ks) (index y ks))=>H.
- by apply/orP; left; apply/(leq_trans H)/index_leq_last.
by apply/orP; right; apply/(leq_trans H)/index_leq_last.
Qed.

(* no/degenerate totality for LE-LF *)
*)
Lemma sle_l_total ks x y : x <=]ks] y || y <=]ks] x.
Proof. by rewrite /seq_le_l; case: ltngtP. Qed.

Lemma slt_total ks x y : x \in ks -> [|| x == y, x <[ks[ y | y <[ks[ x].
Proof.
rewrite /seq_lt=>H; case: ltngtP; rewrite ?orbT ?orbF //.
by move/index_inj=>->.
Qed.

(*
Lemma slt_total_fl ks x y : x \in ks -> [|| x == y, x <FL[ks] y | y <FL[ks] x].
Proof.
rewrite /seq_lt_fl=>H; case: (ltngtP (index x ks) (index y ks)).
- move=>Hx; suff: (index x ks < indexlast y ks)%N by move=>-> /=; rewrite orbT.
  by apply: (leq_trans Hx); exact: index_leq_last.
- move=>Hy; suff: (index y ks < indexlast x ks)%N by move=>-> /=; rewrite !orbT.
  by apply: (leq_trans Hy); exact: index_leq_last.
by move/index_inj=>->//; rewrite eq_refl.
Qed.

(* no/degenerate totality for LT-LF *)
*)
Lemma slt_l_total ks x y : x \in ks -> [|| x == y, x <]ks] y | y <]ks] x].
Proof.
rewrite /seq_lt_l=>H; case: ltngtP; rewrite ?orbT ?orbF //.
by move/indexlast_inj=>->.
Qed.

(* transfer properties of sequence ordering *)

(****************** sle_eqVlt ***************)

Lemma sle_eqVlt ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <=[ks[ t2 = (t1 == t2) || (t1 <[ks[ t2).
Proof.
move=>H; rewrite /seq_lt /seq_le leq_eqVlt /=.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

(*
Lemma sle_eqVlt_fl ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <=FL[ks] t2 = (t1 == t2) || (t1 <FL[ks] t2).
Proof.
move=>H; rewrite /seq_lt_fl /seq_le_fl.
case: (eqVneq t1 t2)=>[->|N] /=; first by apply: index_leq_last.
rewrite leq_eqVlt; case: eqP=>//= /(index_last_inj H).
by apply: contra_eq.
Qed.

(* only one direction! *)
Lemma sle_eqVlt_lf ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <=LF[ks] t2 -> (t1 == t2) || (t1 <LF[ks] t2).
Proof.
rewrite orbC=>H; rewrite /seq_lt_lf /seq_le_lf.
case: (eqVneq t1 t2)=>[->|N] //=.
rewrite leq_eqVlt; case: eqP=>//= + _; move/esym/(index_last_inj H).
by apply: contra_eq=>_; rewrite eq_sym.
Qed.
*)
Lemma sle_l_eqVlt ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <=]ks] t2 = (t1 == t2) || (t1 <]ks] t2).
Proof.
move=>H; rewrite /seq_lt_l /seq_le_l leq_eqVlt.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(indexlast_inj H)/N.
by move/esym/(indexlast_inj H)/esym/N.
Qed.

(****************** olt_neqAle ***************)

Lemma slt_neqAle ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <[ks[ t2 = (t1 != t2) && (t1 <=[ks[ t2).
Proof.
move=>H.
rewrite /seq_lt /seq_le ltn_neqAle.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

(*
(* only one direction! *)
Lemma slt_neqAle_fl ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 != t2 -> t1 <=FL[ks] t2 -> t1 <FL[ks] t2.
Proof.
move=>H N.
rewrite /seq_lt_fl /seq_le_fl leq_eqVlt; case/orP=>// /eqP.
by move/(index_last_inj H); apply: contra_eq.
Qed.

Lemma slt_neqAle_lf ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <LF[ks] t2 = (t1 != t2) && (t1 <=LF[ks] t2).
Proof.
rewrite orbC=>H.
rewrite /seq_lt_lf /seq_le_lf.
case: (eqVneq t1 t2)=>[->|N] /=; first by rewrite ltnNge index_leq_last.
rewrite ltn_neqAle; case: eqP=>//= /esym/(index_last_inj H).
by apply: contra_eq=>_; rewrite eq_sym.
Qed.
*)
Lemma slt_l_neqAle ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <]ks] t2 = (t1 != t2) && (t1 <=]ks] t2).
Proof.
move=>H.
rewrite /seq_lt_l /seq_le_l ltn_neqAle.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(indexlast_inj H)/N.
by move/esym/(indexlast_inj H)/esym/N.
Qed.

(****************** sltNge ***************)

Lemma sltNge ks t1 t2 : t1 <[ks[ t2 = ~~ t2 <=[ks[ t1.
Proof. by rewrite /seq_lt /seq_le ltnNge. Qed.

(*
(* only one direction! *)
Lemma sltNge_fl ks t1 t2 : ~~ t2 <=FL[ks] t1 -> t1 <FL[ks] t2.
Proof.
rewrite /seq_lt_fl /seq_le_fl -ltnNge => H.
apply: leq_ltn_trans; first by exact: index_leq_last.
apply: (leq_trans H).
by exact: index_leq_last.
Qed.

(* only one (reverse) direction! *)
Lemma sltNge_lf ks t1 t2 : t1 <LF[ks] t2 -> ~~ t2 <=LF[ks] t1.
Proof.
rewrite /seq_lt_lf /seq_le_lf -ltnNge => H.
apply: leq_ltn_trans; first by exact: index_leq_last.
apply: (leq_trans H).
by exact: index_leq_last.
Qed.
*)
Lemma sltNge_l ks t1 t2 : t1 <]ks] t2 = ~~ t2 <=]ks] t1.
Proof. by rewrite /seq_lt_l /seq_le_l ltnNge. Qed.

(****************** oleNgt ***************)

Lemma sleNgt ks t1 t2 : t1 <=[ks[ t2 = ~~ t2 <[ks[ t1.
Proof. by rewrite sltNge negbK. Qed.

(*
(* only one direction! *)
Lemma sleNgt_fl ks t1 t2 : ~~ t2 <FL[ks] t1 -> t1 <=FL[ks] t2.
Proof. by apply/contraR/sltNge_fl. Qed.

(* only one direction! *)
Lemma sleNgt_lf ks t1 t2 : t1 <=LF[ks] t2 -> ~~ t2 <LF[ks] t1.
Proof. by apply/contraL/sltNge_lf. Qed.
*)
Lemma sleNgt_l ks t1 t2 : t1 <=]ks] t2 = ~~ t2 <]ks] t1.
Proof. by rewrite sltNge_l negbK. Qed.

(* order properties of the sequence orderings *)

(****************** slt_neq ***************)

Corollary slt_neq x y ks : x <[ks[ y -> x != y.
Proof. by apply/contraL=>/eqP->; apply: slt_irr. Qed.


(*
(* no slt_neq_fl *)

Corollary slt_neq_lf x y ks : x <LF[ks] y -> x != y.
Proof. by apply/contraL=>/eqP->; apply: slt_irr_lf. Qed.
*)
Corollary slt_l_neq x y ks : x <]ks] y -> x != y.
Proof. by apply/contraL=>/eqP->; apply: slt_l_irr. Qed.



Lemma sltW ks t1 t2 : t1 <[ks[ t2 -> t1 <=[ks[ t2.
Proof. by apply: ltnW. Qed.

Lemma sltW_l ks t1 t2 : t1 <]ks] t2 -> t1 <=]ks] t2.
Proof. by apply: ltnW. Qed.

Lemma slt_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <[ks1[ t = k <[ks2[ t.
Proof. by move=>S U T K; apply/idP/idP=>/(index_subseq S U T K). Qed.

Lemma sle_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <=[ks1[ t = k <=[ks2[ t.
Proof. by move=>S U T K; rewrite !sleNgt (slt_subseq S U K T). Qed.

Lemma slt_l_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <]ks1] t = k <]ks2] t.
Proof. by move=>S U T K; apply/idP/idP=>/(indexlast_subseq S U T K). Qed.

Lemma sle_l_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <=]ks1] t = k <=]ks2] t.
Proof. by move=>S U T K; rewrite !sleNgt_l (slt_l_subseq S U K T). Qed.

(* membership properties of the sequence orderings *)

Lemma slt_memI x y ks : x \in ks -> y \notin ks -> x <[ks[ y.
Proof. by move=>X /index_memN E; rewrite /seq_lt E index_mem. Qed.

Lemma sle_memI x y ks : y \notin ks -> x <=[ks[ y.
Proof. by move/index_memN=>E; rewrite /seq_le E index_size. Qed.

Lemma slt_memE x y ks : x <[ks[ y -> x \in ks.
Proof. by rewrite -index_mem=>/leq_trans; apply; rewrite index_size. Qed.

Lemma sle_memE x y ks : x <=[ks[ y -> y \in ks -> x \in ks.
Proof. by move=>H; rewrite -!index_mem; apply: leq_ltn_trans H. Qed.

Lemma slt_l_memI x y ks : x \in ks -> y \notin ks -> x <]ks] y.
Proof. by move=>X /indexlast_memN E; rewrite /seq_lt_l E indexlast_mem. Qed.

Lemma sle_l_memI x y ks : y \notin ks -> x <=]ks] y.
Proof. by move/indexlast_memN=>E; rewrite /seq_le_l E indexlast_size. Qed.

Lemma slt_l_memE x y ks : x <]ks] y -> x \in ks.
Proof. by rewrite -indexlast_mem=>/leq_trans; apply; rewrite indexlast_size. Qed.

Lemma sle_l_memE x y ks : x <=]ks] y -> y \in ks -> x \in ks.
Proof. by move=>H; rewrite -!indexlast_mem; apply: leq_ltn_trans H. Qed.

(* sequence orderings and constructors *)

Lemma slt_nil x y : x <[Nil A[ y = false. Proof. by []. Qed.
Lemma sle_nil x y : x <=[Nil A[ y. Proof. by []. Qed.

(* cons *)

Lemma slt_cons x y k ks :
        x <[k :: ks[ y = (y != k) && ((x == k) || (x <[ks[ y)).
Proof. by rewrite /seq_lt /= !(eq_sym k); case: eqP; case: eqP. Qed.

Lemma sle_cons x y k ks :
        x <=[k :: ks[ y = (x == k) || (y != k) && x <=[ks[ y.
Proof. by rewrite sleNgt slt_cons negb_and negbK negb_or -sleNgt. Qed.

Lemma slt_l_cons x y k ks :
        x <]k :: ks] y = ((y == k) ==> (y \in ks)) &&
                           if x \in ks then x <]ks] y else x == k.
Proof.
rewrite /seq_lt_l /= !indexlast_cons !(eq_sym k).
case/boolP: (y \in ks)=>Y; case/boolP: (x \in ks)=>X /=;
rewrite ?andbF ?andbT ?implybF ?implybT ?(memNindexlast X) ?(memNindexlast Y) /=.
- by rewrite ltnS.
- by case: eqP=>//= _; rewrite ltnS ltnNge indexlast_size.
- by case: eqP.
by case: eqP; case: eqP=>//= _ _; rewrite ltnS ltnn.
Qed.

Lemma sle_l_cons x y k ks :
        x <=]k :: ks] y = (x <=]ks] y && ((y == k) ==> (y \in ks))) ||
                           (x \notin ks) && (x==k).
Proof.
rewrite /seq_le_l /= !indexlast_cons !(eq_sym k).
case/boolP: (y \in ks)=>Y; case/boolP: (x \in ks) => X /=;
rewrite ?implybF ?implybT ?andbF ?andbT ?orbF ?(memNindexlast X) ?(memNindexlast Y) ?ltnS //.
- case: eqP=>/= _; first by rewrite orbT.
  by rewrite orbF ltnS.
- case: eqP=>/= _; first by rewrite andbF.
  by rewrite andbT ltnS.
by rewrite leqnn /=; case: eqP=>_; case: eqP=>_ //=; rewrite ltnS leqnn.
Qed.

Lemma sltL x y ks : x <[x :: ks[ y = (y != x).
Proof. by rewrite slt_cons eq_refl andbT. Qed.

Lemma sleL x y ks : x <=[x :: ks[ y.
Proof. by rewrite sle_cons eq_refl. Qed.

Lemma sltR x y ks : ~~ x <[y :: ks[ y.
Proof. by rewrite sltNge sleL. Qed.

Lemma sleR x y ks : x <=[y :: ks[ y = (y == x).
Proof. by rewrite sleNgt sltL negbK. Qed.

(* sequence orderings and last *)

Lemma sle_last x k ks :
        uniq ks -> x \in ks -> x <=[ks[ (last k ks).
Proof. by apply: index_last_mono. Qed.

Lemma sle_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks -> x <=[k::ks[ (last k ks).
Proof.
move=>/= /andP [U1 U2].
rewrite inE sle_cons; case: eqP=>//= /eqP Nxk K.
by rewrite (last_notin K) //=; apply: sle_last.
Qed.

Lemma slt_last x k ks :
        uniq ks -> x \in ks -> last k ks != x -> x <[ks[ (last k ks).
Proof.
move=>U X N; move: (sle_last k U X); rewrite sle_eqVlt; last by rewrite X.
by rewrite eq_sym (negbTE N).
Qed.

Lemma slt_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks ->
        last k ks != x -> x <[k::ks[ (last k ks).
Proof.
move=>U X N; rewrite slt_neqAle; last by rewrite X.
by rewrite eq_sym N sle_last_cons.
Qed.

(* sequence ordering and head *)

Lemma sle_head x ks y : (head x ks) <=[ks[ y.
Proof. by case: ks=>[|k ks] //=; rewrite sleL. Qed.


(* sequence orderings and rcons *)

Lemma slt_rcons x y k ks :
        x <[rcons ks k[ y = if y \in ks then x <[ks[ y
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
case: eqP=>_; case: eqP=>_ /=.
- by rewrite ltnn.
- by rewrite ltnS leqnn.
- by rewrite ltnNge leqnSn.
by rewrite ltnn.
Qed.

Lemma sle_rcons x y k ks :
        x <=[rcons ks k[ y = if x \in ks then x <=[ks[ y
                             else (y \notin ks) && ((k == x) || (k != y)).
Proof.
by rewrite !sleNgt slt_rcons; case: ifP=>//; rewrite negb_or negb_and negbK.
Qed.

(* some shortcuts for slt/sle_rcons *)

Lemma slt_rconsI x y k ks : x <[ks[ y -> x <[rcons ks k[ y.
Proof. by move=>H; rewrite slt_rcons H (slt_memE H) if_same. Qed.

Lemma sle_rconsI x y k ks : k != y -> x <=[ks[ y -> x <=[rcons ks k[ y.
Proof.
move=>N H; rewrite sle_rcons H N orbT andbT.
case: ifP=>// K; apply: contraFT K.
by rewrite negbK; apply: sle_memE H.
Qed.

Lemma slt_rcons_in x y k ks :
        x \in ks -> x <[rcons ks k[ y = x <[ks[ y.
Proof.
move=>H; rewrite slt_rcons H /=; case: ifP=>// K.
by apply/esym; apply: slt_memI=>//; rewrite K.
Qed.

Lemma sle_rcons_in x y k ks :
        x \in ks -> x <=[rcons ks k[ y = x <=[ks[ y.
Proof. by move=>X; rewrite sle_rcons X. Qed.

Lemma slt_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <[rcons ks k1[ y = x <[rcons ks k2[ y.
Proof. by rewrite !slt_rcons=>/orP [] ->. Qed.

Lemma sle_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <=[rcons ks k1[ y = x <=[rcons ks k2[ y.
Proof. by rewrite !sle_rcons=>/orP [] ->. Qed.

Lemma slt_rconsR ks x k : x <[rcons ks k[ k -> x \in ks.
Proof. by rewrite slt_rcons eq_refl orbF; case: ifP=>[_ /slt_memE|]. Qed.

Lemma sle_rconsR ks x k : x <=[rcons ks k[ k -> x \in rcons ks k.
Proof.
rewrite sle_rcons eq_refl orbF mem_rcons inE.
case X: (x \in ks); first by rewrite orbT.
by rewrite orbF eq_sym; case/andP.
Qed.

(* sequence orderings and concatenation *)
Lemma sle_cat ks1 ks2 x y :
        x <=[ks1++ks2[ y = if x \in ks1 then x <=[ks1[ y
                           else (y \notin ks1) && x <=[ks2[ y.
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

Lemma slt_cat ks1 ks2 x y :
        x <[ks1++ks2[ y = if y \in ks1 then x <[ks1[ y
                          else (x \in ks1) || x <[ks2[ y.
Proof. by rewrite !sltNge sle_cat; case: ifP=>//; rewrite negb_and negbK. Qed.

(* shortcuts *)

Lemma slt_catL ks1 ks2 x y : x <[ks1[ y -> x <[ks1++ks2[ y.
Proof. by move=>H; rewrite slt_cat H (slt_memE H) if_same. Qed.

Lemma slt_splitR x y ks1 ks2 : y != x -> y \notin ks1 -> x <[ks1++x::ks2[ y.
Proof.
by move=>N Y; rewrite slt_cat slt_cons eq_refl andbT (negbTE Y) N orbT.
Qed.

Lemma sle_splitR x y ks1 ks2 : y \notin ks1 -> x <=[ks1++x::ks2[ y.
Proof.
move=>Y; rewrite sle_eqVlt; last first.
- by apply/orP; left; rewrite mem_cat inE eq_refl orbT.
by case: eqP=>[|/eqP N] //=; rewrite (slt_splitR _ _ Y) // eq_sym.
Qed.

(* the other direction of slt_splitR, further strenghtened *)
(* with an additional fact that x \notin ks1 *)
(* by picking a split with the first occurrence of x *)
(* in fact, we can have both directions here, so we prove a reflect lemma *)
(* but it should really only be used in the direction x <[ks[ y -> .. *)
(* because in the other direction slt_splitR is already stronger. *)
Lemma slt_splitL ks x y :
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2, x != y,
                                     x \notin ks1 & y \notin ks1])
                (x <[ks[ y).
Proof.
case H : (x <[ks[ y); constructor; last first.
- apply/contraFnot: H; case=>ks1 [ks2][-> N _].
  by apply: slt_splitR; rewrite eq_sym.
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
                (x <=[ks[ y).
Proof.
move=>X; case H : (x <=[ks[ y); constructor; last first.
- apply/contraFnot: H; case=>ks1 [ks2][-> _ N].
  by apply: sle_splitR.
case/in_split: X=>ks1 [ks2][E X]; exists ks1, ks2; split=>//.
rewrite /seq_le {ks}E !index_cat /= eq_refl (negbTE X) addn0 in H.
by case: ifP H=>//; rewrite -index_mem; case: ltngtP.
Qed.

(* sequence orderings and filter *)

Lemma slt_filterL (p : pred A) ks x y :
         (x \notin ks) || p x ->
         x <[ks[ y -> x <[filter p ks[ y.
Proof. by apply: index_filter_ltL. Qed.

Lemma sle_filterL (p : pred A) ks x y :
        (x \notin ks) || p x ->
        x <=[ks[ y -> x <=[filter p ks[ y.
Proof. by apply: index_filter_leL. Qed.

Lemma slt_filterR (p : pred A) ks x y :
        (y \notin ks) || p y ->
        x <[filter p ks[ y -> x <[ks[ y.
Proof. by apply: index_filter_ltR. Qed.

Lemma sle_filterR (p : pred A) ks x y :
        (y \notin ks) || p y ->
        x <=[filter p ks[ y -> x <=[ks[ y.
Proof. by apply: index_filter_leR. Qed.

Lemma slt_filter (p : pred A) ks x y :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <[filter p ks[ y = x <[ks[ y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: slt_filterR | apply: slt_filterL].
Qed.

Lemma sle_filter (p : pred A) ks x y :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <=[filter p ks[ y = x <=[ks[ y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: sle_filterR | apply: sle_filterL].
Qed.

(* sequence orderings and sortedness *)

(* every list is sorted by its slt relation, assuming uniqueness *)
Lemma sorted_slt ks : uniq ks -> sorted (seq_lt ks) ks.
Proof.
case: ks=>//= k ks; elim: ks k=>[|k1 ks IH] k2 //=.
rewrite inE negb_or -andbA=>/and4P [N1 N2 N3 N4].
rewrite sltL eq_sym N1 /=.
have : path (seq_lt [:: k1 & ks]) k1 ks by apply: IH; rewrite N3 N4.
apply: (@sub_in_path _ (mem (k1::ks))); last by apply/allP.
move=>x y /=; rewrite !inE !slt_cons.
case/orP=>[/eqP ->{x}|X].
- rewrite (eq_sym k1 k2) (negbTE N1) /= eq_refl andbT.
  case/orP=>[/eqP ->|Y ->]; first by rewrite eq_refl.
  by case: eqP Y N2=>// ->->.
case/orP=>[/eqP ->|Y]; first by rewrite eq_refl.
case: eqP Y N3=>[->|/eqP N Y N3] //=.
case: eqP X N3=>[->->|/eqP M X K1] //= H.
by rewrite H orbT andbT; case: eqP Y N2=>// ->->.
Qed.

Lemma sorted_sle ks : uniq ks -> sorted (seq_le ks) ks.
Proof.
move=>U; apply: sub_sorted (sorted_slt U).
by move=>x y; rewrite /seq_lt/seq_le; case: ltngtP.
Qed.

(* olt/ole under general sorted relations *)
Lemma slt_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <[ks[ y -> ltT x y.
Proof. by apply: sorted_index_ord. Qed.

Lemma sle_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <=[ks[ y -> (x == y) || ltT x y.
Proof.
move=>T S Y; rewrite sle_eqVlt; last by rewrite Y orbT.
by case/orP=>[->//|/(slt_sorted_lt T S Y) ->]; rewrite orbT.
Qed.

Lemma slt_sorted_ltE ltT ks x y :
        irreflexive ltT ->
        transitive ltT ->
        sorted ltT ks ->
        x \in ks -> y \in ks ->
        x <[ks[ y = ltT x y.
Proof.
move=>Is T S X Y; apply/idP/idP.
- by apply: slt_sorted_lt.
by apply: sorted_ord_index.
Qed.

(* we can get the other direction as well *)
(* if we add antisymmetry *)
(* and the condition that x \in ks *)
Lemma slt_sorted_leE leT ks x y :
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        x \in ks -> y \in ks ->
        x <[ks[ y = (x != y) && leT x y.
Proof.
move=>As T S X Y; apply/idP/idP.
- by case: eqP=>[->|/eqP N] /=; [apply: contraLR; rewrite slt_irr | apply: slt_sorted_lt].
by case/andP=>H K; apply: sorted_ord_index_leq K H.
Qed.

(* if we add antisymmetry and t1 \in ks *)
Lemma sle_sorted_leE leT ks x y :
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        x \in ks -> y \in ks ->
        x <=[ks[ y = (x == y) || leT x y.
Proof.
move=>As T S X Y; rewrite sle_eqVlt; last by rewrite X.
by rewrite (slt_sorted_leE As T S X Y); case: eqP.
Qed.

End SeqLeEq.

Section SeqLeOrd.
Variable (A : ordType).
Implicit Type (ks : seq A).

(* olt/ole and sortedness under ordering on A *)

Lemma slt_sorted ks x y :
        sorted ord ks -> y \in ks -> x <[ks[ y -> ord x y.
Proof. by apply/slt_sorted_lt/trans. Qed.

Lemma sle_sorted ks x y :
        sorted ord ks -> y \in ks -> x <=[ks[ y -> oleq x y.
Proof. by rewrite oleq_eqVord; apply/sle_sorted_lt/trans. Qed.

Lemma slt_sortedE ks x y :
        sorted ord ks ->
        x \in ks -> y \in ks ->
        x <[ks[ y = ord x y.
Proof.
move=>S X Y; apply/idP/idP; first by apply: slt_sorted S Y.
by apply: (sorted_ord_index (@irr _) (@trans _)) S X.
Qed.

Lemma sle_sortedE ks x y :
        sorted ord ks ->
        x \in ks -> y \in ks ->
        x <=[ks[ y = oleq x y.
Proof. by move=>S X Y; rewrite oleqNord sleNgt (slt_sortedE S Y X). Qed.

End SeqLeOrd.

(* interaction with slicing *)

Section SliceSeqLe.
Variable (A : eqType).
Implicit Type (s : seq A).

(* TODO generalize? *)
Lemma uniq_ux_filter s i :
  uniq s ->
  &=s `]-oo, i] = [seq x <- s | x <=[s[ i].
Proof.
move=>U; rewrite /eq_slice /= subn0 -indexlast_uniq // /slice /= drop0 addn1.
elim: s U=>//=h s IH.
case/andP=>Nh U; rewrite sle_cons eqxx /=.
congr (cons _); case: (eqVneq i h)=>[E|N].
- rewrite -{h}E in Nh *; rewrite take0 -(filter_pred0 s).
  apply: eq_in_filter=>z Hz /=; rewrite sle_cons eqxx /= orbF.
  by apply/esym/negbTE; apply: contraNneq Nh=><-.
rewrite IH //; apply: eq_in_filter=>z Hz; rewrite sle_cons N /=.
suff: (z != h) by move/negbTE=>->.
by apply: contraNneq Nh=><-.
Qed.

Lemma uniq_uo_filter s i :
  uniq s ->
  &=s `]-oo, i[ = [seq x <- s | x <[s[ i].
Proof.
move=>U; rewrite /eq_slice /= subn0 /slice /= drop0 addn0.
elim: s U=>//=h s IH.
case/andP=>Nh U; rewrite slt_cons eqxx /= andbT.
case: (eqVneq i h)=>[E|N] /=.
- rewrite -{h}E in Nh *; rewrite -(filter_pred0 s).
  by apply: eq_in_filter=>z Hz /=; rewrite slt_cons eqxx.
congr (cons _); rewrite IH //; apply: eq_in_filter=>z Hz.
rewrite slt_cons N /=.
suff: (z != h) by move/negbTE=>->.
by apply: contraNneq Nh=><-.
Qed.

(* sequence ordering, intervals, and last *)

Lemma olt_ole_last k s x t :
        uniq (k::s) -> t != k ->
        x <[k::s[ t = x <=[k::s[ (last k (&=s `]-oo, t[)).
Proof.
elim: s k=>/= [|y s IH] k //=.
- rewrite slt_cons slt_nil sle_cons sle_nil andbT eqxx orbF.
  by move=>_ ->.
rewrite inE negb_or -andbA; case/and4P=>Nky K Y U Nkt.
rewrite slt_cons sle_cons Nkt /=; case: (eqVneq x k)=>//= Nkx.
rewrite eqsl_uo_consE.
case: (eqVneq t y)=>/= [E|Nty].
- by rewrite eqxx /=; subst y; apply/negbTE/sltR.
suff -> /= : last y (&=s `]-oo, t[) != k by rewrite IH //= Y.
apply: contraTneq (mem_last y (&=s `]-oo, t[))=> E.
rewrite inE E negb_or Nky /=; apply: contra K.
by exact: slice_subset_full.
Qed.

(* a slight variation to add the cons to last *)
Corollary olt_ole_last' k s x t :
            uniq (k::s) -> t != k ->
            x <[k::s[ t = x <=[k::s[ (last k (&=(k::s) `]-oo, t[)).
Proof. by move=>U K; rewrite olt_ole_last // eqsl_uo_consE K. Qed.

Corollary eqsl_uox_last k s t :
            uniq (k::s) -> t != k ->
            &=(k :: s) `]-oo, last k (&=s `]-oo, t[) ] = &=(k :: s) `]-oo,t[.
Proof.
move=>U K.
rewrite (uniq_ux_filter _ U) (uniq_uo_filter _ U).
by apply: eq_in_filter=>x _; rewrite -olt_ole_last.
Qed.


(****************************)
(* some bureaucratic lemmas *)
(****************************)

(* membership *)

Lemma eqslice_mem (i : interval A) ks (k : A) :
        k \in &=ks i =
        has (fun j => j \in ix_itv ks i) (indexall k ks).
Proof.
by rewrite /eq_slice /= shl_itv0 slice_memE.
Qed.

Lemma mem_oo t1 t2 ks (k : A) :
        k \in &=ks `]t1, t2[ =
        has (fun i => indexlast t1 ks < i < index t2 ks) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /=.
Qed.

Lemma mem_xo t1 t2 ks (k : A) :
        k \in &=ks `[t1, t2[ =
        has (fun i => index t1 ks <= i < index t2 ks) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /=.
Qed.

Lemma mem_ox t1 t2 ks (k : A) :
        k \in &=ks `]t1, t2] =
        has (fun i => indexlast t1 ks < i <= indexlast t2 ks) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /=.
Qed.

Lemma mem_xx t1 t2 ks (k : A) :
        k \in &=ks `[t1, t2] =
        has (fun i => index t1 ks <= i <= indexlast t2 ks) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /=.
Qed.

Lemma mem_uo t2 ks (k : A) :
        k \in &=ks `]-oo, t2[ =
        has (fun i => i < index t2 ks) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /=.
Qed.

Lemma mem_ux t2 ks (k : A) :
        k \in &=ks `]-oo, t2] =
        has (fun i => i <= indexlast t2 ks) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /=.
Qed.

Lemma mem_ou t1 ks (k : A) :
        k \in &=ks `]t1, +oo[ =
        has (fun i => indexlast t1 ks < i) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /= andbT.
Qed.

Lemma mem_xu t1 ks (k : A) :
        k \in &=ks `[t1, +oo[ =
        has (fun i => index t1 ks <= i) (indexall k ks).
Proof.
rewrite /eq_slice /= !subn0 slice_memE.
by apply: eq_has=>z; rewrite in_itv /= andbT.
Qed.

(* has predT lemmas *)

Lemma has_oo t1 t2 (ks : seq A) :
        has predT (&=ks `]t1,t2[) = has (fun k => has (fun z => indexlast t1 ks < z < index t2 ks) (indexall k ks)) ks.
Proof.
apply/hasP/hasP=>[[x + _]|[x Hx Hi]] /=.
- move/[dup]/slice_subset_full=>Hi; rewrite mem_oo /= => Hx.
  by exists x.
by exists x=>//; rewrite mem_oo.
Qed.s

[[x]|[x X Y]].
- by case/mem_oo=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_ox t1 t2 ks :
        has predT |sqint t1 t2 ks] = has (fun z => t1 <[ks[ z && z <=[ks[ t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_ox=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_xo t1 t2 ks :
        has predT [sqint t1 t2 ks| = has (fun z => t1 <=[ks[ z && z <[ks[ t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_xo=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_xx t1 t2 ks :
        has predT [sqint t1 t2 ks] = has (fun z => t1 <=[ks[ z && z <=[ks[ t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_xx=>H1 H2 H3 _; exists x=>//; rewrite H2 H3.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_ou t ks :
        has predT |sqint t ks} = has (fun z => t <[ks[ z) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_ou=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_xu t ks :
        has predT [sqint t ks} = has (fun z => t <=[ks[ z) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_xu=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_uo t ks :
        has predT {sqint t ks| = has (fun z => z <[ks[ t) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_uo=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.

Lemma has_ux t ks :
        has predT {sqint t ks] = has (fun z => z <=[ks[ t) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
- by case/mem_ux=>H1 H2 _; exists x=>//; rewrite H2.
by exists x=>//; rewrite mem_filter X Y.
Qed.
*)
(* negation of has on the left side *)

Lemma hasNL_oo ks t1 t2 (p : pred A) :
       (* added *) count_mem t1 ks <= 1%N ->
       t1 <[ks[ t2 -> ~~ has p (&=ks `]t1, t2[) ->
       {in ks, forall z, p z -> z <[ks[ t2 = z <=[ks[ t1}.
Proof.
move=>_ T /hasPn H z K P.
apply: contraTeq P=>N; apply: H; apply: contra_neqT N.
rewrite /eq_slice /= !subn0 slice_memE.
rewrite -all_predC.

rewrite slt_le
rewrite K /= negb_and addn1 addn0 leEnat. rewrite -indexlast_uniq. // -!sleNgt.
case/orP=>H1; first by rewrite H1 (sle_slt_trans H1 T).
by rewrite sltNge H1 sleNgt (slt_sle_trans T H1).
Qed.

(*
Lemma hasNL_ox ks t1 t2 (p : pred A) :
       t1 <=[ks[ t2 -> ~~ has p |sqint t1 t2 ks] ->
       {in ks, forall z, p z -> z <=[ks[ t2 = z <=[ks[ t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oleNgt.
case/orP=>H1; first by rewrite H1 (ole_trans H1 T).
rewrite (negbTE H1); apply/esym/negP=>X.
by rewrite (ole_trans X T) in H1.
Qed.

Lemma hasNL_xo ks t1 t2 (p : pred A) :
       t1 <=[ks[ t2 -> ~~ has p [sqint t1 t2 ks| ->
       {in ks, forall z, p z -> z <[ks[ t2 = z <[ks[ t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oleNgt.
rewrite -oltNge; case/orP=>H1; first by rewrite H1 (olt_ole_trans H1 T).
by rewrite oltNge H1 oltNge (ole_trans T H1).
Qed.

Lemma hasNL_xx ks t1 t2 (p : pred A) :
       t1 <=[ks[ t2 -> ~~ has p [sqint t1 t2 ks] ->
       {in ks, forall z, p z -> z <=[ks[ t2 = z <[ks[ t1}.
Proof.
move=>T /hasPn H z K P.
move: (H z); rewrite mem_filter K andbT P.
move/contraL/(_ erefl); rewrite negb_and -!oltNge.
case/orP=>H1; first by rewrite H1 (oltW (olt_ole_trans H1 T)).
by rewrite oleNgt H1 oltNge (oltW (ole_olt_trans T H1)).
Qed.

Lemma hasNL_ou ks t (p : pred A) :
       ~~ has p |sqint t ks} -> {in ks, forall z, p z -> z <=[ks[ t}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oleNgt.
Qed.

Lemma hasNL_xu ks t (p : pred A) :
       ~~ has p [sqint t ks} -> {in ks, forall z, p z -> z <[ks[ t}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oltNge.
Qed.

Lemma hasNL_uo ks t (p : pred A) :
       ~~ has p {sqint t ks| -> {in ks, forall z, p z -> t <=[ks[ z}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oleNgt.
Qed.

Lemma hasNL_ux ks t (p : pred A) :
       ~~ has p {sqint t ks] -> {in ks, forall z, p z -> t <[ks[ z}.
Proof.
move/hasPn=>H z K P.
move: (H z); rewrite mem_filter K andbT P.
by move/contraL/(_ erefl); rewrite oltNge.
Qed.
*)
(* negation of has on the right side *)

Lemma hasNR_oo ks t1 t2 (p : pred A) :
       (* added *) uniq ks ->
       {in ks, forall z, p z -> z <[ks[ t2 = z <=[ks[ t1} ->
       ~~ has p (&=ks `]t1, t2[).
Proof.
move=>U T; apply/hasPn=>z; rewrite slice_memE /=; last first.
- by rewrite count_uniq_mem //; apply: leq_b1.
rewrite !subn0 addn0 addn1 leEnat -indexlast_uniq //.
case/and3P=>H1 H2 H3; apply: contraL H2=>P; rewrite -sleNgt.
by rewrite -(T _ H1 P).
Qed.

(*
Lemma hasNR_ox ks t1 t2 (p : pred A) :
       {in ks, forall z, p z -> z <=[ks[ t2 = z <=[ks[ t1} ->
       ~~ has p |sqint t1 t2 ks].
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (ole_olt_trans H2 H1); rewrite olt_irr.
Qed.

Lemma hasNR_xo ks t1 t2 (p : pred A) :
       {in ks, forall z, p z -> z <[ks[ t2 = z <[ks[ t1} ->
       ~~ has p [sqint t1 t2 ks|.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (ole_olt_trans H1 H2); rewrite olt_irr.
Qed.

Lemma hasNR_xx ks t1 t2 (p : pred A) :
       {in ks, forall z, p z -> z <=[ks[ t2 = z <[ks[ t1} ->
       ~~ has p [sqint t1 t2 ks].
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter -andbA.
case/and3P=>H1 H2 H3; apply/negP=>P; rewrite (T z H3 P) in H2.
by move: (ole_olt_trans H1 H2); rewrite olt_irr.
Qed.

Lemma hasNR_ou ks t (p : pred A) :
       {in ks, forall z, p z -> z <=[ks[ t} -> ~~ has p |sqint t ks}.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (ole_olt_trans (T z H2 P) H1); rewrite olt_irr.
Qed.

Lemma hasNR_xu ks t (p : pred A) :
       {in ks, forall z, p z -> z <[ks[ t} -> ~~ has p [sqint t ks}.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (olt_ole_trans (T z H2 P) H1); rewrite olt_irr.
Qed.

Lemma hasNR_uo ks t (p : pred A) :
       {in ks, forall z, p z -> t <=[ks[ z} -> ~~ has p {sqint t ks|.
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (ole_olt_trans (T z H2 P) H1); rewrite olt_irr.
Qed.

Lemma hasNR_ux ks t (p : pred A) :
       {in ks, forall z, p z -> t <[ks[ z} -> ~~ has p {sqint t ks].
Proof.
move=>T; apply/hasPn=>z; rewrite mem_filter.
case/andP=>H1 H2; apply/negP=>P.
by move: (olt_ole_trans (T z H2 P) H1); rewrite olt_irr.
Qed.
*)

End LemmasSeqLe.


(**************************************)
(**************************************)
(* Consecutive elements in a sequence *)
(**************************************)
(**************************************)

Section ConsecEq.
Variable (A : eqType).
Implicit Type (ks : seq A).

(* The interval lemmas let us equate evaluations of interval endpoints *)
(* But, when a property we want to prove involves other components *)
(* we need to properly induct over ks. *)
(* We thus first define what it means for elements in ks to be consecutive, *)
(* so that the properties can be used in the proofs of the inductive cases. *)

(* t2 is consecutive to t1 in ks if it appears after t1 and there are *)
(* no other elements in ks between t1 and t2 *)

(* TODO count_mem t1 ks == 1 ? *)
Definition consec ks t1 t2 :=
  [&& t1 <[ks[ t2 & nilp (&=ks `]t1, t2[)].

(* several alternative formulations *)
Lemma consecP ks t1 t2 :
        reflect ([/\ t1 <[ks[ t2 & &=ks `]t1, t2[ = [::]])
                (consec ks t1 t2).
Proof.
case C : (consec ks t1 t2); constructor.
- by case/andP: C=>T /nilP S.
case=>T S; move/(elimF idP): C; apply.
by rewrite /consec T /=; apply/nilP.
Qed.

Lemma consecP_inlt (ks : seq A) t1 t2 :
        (* added *) uniq ks ->
        reflect ([/\ t1 \in ks & {in ks, forall z, z <[ks[ t2 = z <=[ks[ t1}])
                (consec ks t1 t2).
Proof.
move=>_; case C: (consec ks t1 t2); constructor.
- case/andP: C=>T E; split; first by apply: slt_memE T.
  move=>z Z; rewrite nilp_hasPn in E. apply: hasNL_oo T E _ Z _.
case=>T H; apply: (elimF idP) C _.
by rewrite /consec H // sle_refl /= nilp_hasPn; apply: hasNR_oo=> // z /H.
Qed.

Lemma consecP_ingt (ks : seq A) t1 t2 :
        (* added *) uniq ks ->
        reflect ([/\ t1 \in ks & {in ks, forall z, t2 <=[ks[ z = t1 <[ks[ z}])
                (consec ks t1 t2).
Proof.
move=>U; case: consecP_inlt=>//.
- case=>T1 H; constructor.
  by split=>// z /H E; rewrite sleNgt E -sltNge.
move=>H1; constructor; case=>T1 H; elim: H1.
by split=>// z /H E; rewrite sleNgt -E -sltNge.
Qed.


(* frequent projections *)

Lemma consec_olt ks t1 t2 : consec ks t1 t2 -> t1 <[ks[ t2.
Proof. by case/andP. Qed.

Lemma consec_oltW ks t1 t2 : consec ks t1 t2 -> t1 <=[ks[ t2.
Proof. by move/consec_olt/sltW. Qed.

Lemma consec_mem ks t1 t2 : consec ks t1 t2 -> t1 \in ks.
Proof. by case/andP=>/slt_memE. Qed.

Lemma consec_oo ks t1 t2 : consec ks t1 t2 -> &=ks `]t1, t2[ = [::].
Proof. by case/consecP. Qed.

Lemma consec_in ks t1 t2 :
        (* added *) uniq ks ->
        consec ks t1 t2 -> {in ks, forall z, z <[ks[ t2 = z <=[ks[ t1}.
Proof. by move=>U; case/(consecP_inlt _ _ U). Qed.

(* and some streamlining *)

Lemma consec_prev (ks : seq A) x y z :
        (* added *) uniq ks ->
        consec ks x y -> z <[ks[ y -> z <=[ks[ x.
Proof. by move=>U; case/(consecP_inlt _ _ U)=>X E N; rewrite -E // (slt_memE N). Qed.

Lemma consec_prevN ks x y z :
        (* added *) uniq ks ->
        z != x -> consec ks x y -> z <[ks[ y -> z <[ks[ x.
Proof.
move=>U N C /(consec_prev U C).
by rewrite sle_eqVlt; [rewrite (negbTE N) | rewrite (consec_mem C) orbT].
Qed.

Lemma consec_next (ks : seq A) x y z :
        (* added *) uniq ks ->
        consec ks x y -> x <[ks[ z -> y <=[ks[ z.
Proof.
case/consecP_ingt=>X E N; case Dz : (z \in ks); first by rewrite E.
by apply: ole_memI; rewrite Dz.
Qed.

Lemma consec_nextN ks x y z :
        y \in ks \/ z \in ks ->
        y != z -> consec ks x y -> x <[ks[ z -> y <[ks[ z.
Proof.
move=>D N C /(consec_next C).
by rewrite (sle_eqVlt D) (negbTE N).
Qed.

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
        uniq ks ->
        consec ks t1 t2 ->
        t2 \notin ks <-> exists ks', ks = rcons ks' t1.
Proof.
move=>U /andP [T /hasPn H]; case: (lastP ks) H U T=>[|xs x] //= H.
rewrite rcons_uniq olt_rcons mem_rcons inE negb_or !(eq_sym x).
case/andP=>Nx Ux; case: ifP=>X; rewrite ?andbF ?andbT.
- move=>Nt; split=>//; case=>ks' /rcons_inj [??]; subst ks' x.
  by rewrite (slt_memE Nt) in Nx.
move: (H x); rewrite mem_filter !olt_rcons mem_rcons inE (negbTE Nx)
!eq_refl X !orbF !andbT /= (eq_sym x)=>N T.
split.
- move=>Nt2x; rewrite Nt2x !andbT /= in N T.
  by case/orP: T N=>[T /(_ T)//|/eqP ->]; exists xs.
case=>ks' /rcons_inj [??]; subst ks' x.
by rewrite (negbTE Nx) eq_refl andbT in T.
Qed.


(* restatement using last *)
Lemma consec_lastE ks t1 t2 t3 :
        uniq ks ->
        consec ks t1 t2 ->
        t2 \notin ks <-> t1 = last t3 ks.
Proof.
move=>U C; rewrite (consec_last U C).
split=>[[ks' ->]|E]; first by rewrite last_rcons.
case: (lastP ks) E C=>[-> /andP [] //|s x].
by rewrite last_rcons => ->; exists s.
Qed.

(* not quite the same lemmas as consec_last, but a useful split *)
Lemma consecP_last ks t1 t2 :
        uniq ks -> t2 \notin ks ->
        reflect (exists xs, ks = rcons xs t1)
                (consec ks t1 t2).
Proof.
move=>U T2; case C : (consec ks t1 t2); constructor.
- by move/consec_last: T2; apply.
case=>xs E; rewrite E /consec rcons_uniq mem_rcons inE negb_or eq_sym in C U T2.
case/andP: U T2 C=>T1 U /andP [N T2].
rewrite olt_rcons (negbTE T2) (negbTE T1) N eq_refl /=.
case/negbFE/hasP=>x.
rewrite mem_filter !olt_rcons mem_rcons inE (eq_sym x) eq_refl /=.
rewrite (negbTE T1) (negbTE T2) N /= andbT orbC -andbA andbb orbC andbC.
case: ifP=>/= X; last by rewrite andbN.
by move/slt_memE; rewrite (negbTE T1).
Qed.

Lemma consecP_lastE y ks t1 t2 :
        uniq ks -> t2 \notin ks ->
        consec ks t1 t2 = (t1 \in ks) && (t1 == last y ks).
Proof.
move=>U T2; case: consecP_last=>//.
- by case=>xs ->; rewrite mem_rcons last_rcons inE eq_refl.
move=>H; apply/esym/negP=>/andP [H1 H2]; elim: H.
by apply/(rcons_lastXP _ y); rewrite H1 H2.
Qed.

Lemma consecP_nilp_filter ks (p : pred _) t1 t2 :
        consec (filter p ks) t1 t2 <->
        if p t2 then [/\ t1 <[ks[ t2, p t1 & nilp (filter p |sqint t1 t2 ks|)]
        else [/\ t1 \in ks, p t1 & nilp (filter p |sqint t1 ks})].
Proof.
case: ifP=>P2; split.
- case/consecP=>Cx /nilP Nx.
  move: (slt_memE Cx); rewrite mem_filter=>/andP [P1 K1].
  rewrite olt_filter ?(P1,P2,orbT) // in Cx.
  split=>//; rewrite !nilp_hasPn in Nx *; apply: contra Nx.
  case/hasP=>x; rewrite !mem_filter -!andbA=>/and4P [Px N1 N2 Kx] _.
  apply/hasP; exists x=>//; rewrite !mem_filter !olt_filter ?(P1,P2,Px,orbT) //.
  by rewrite N1 N2 Kx.
- case=>N P1 Nx; apply/consecP; split.
  - by rewrite olt_filter ?(P1,P2,orbT).
  apply/nilP; rewrite !nilp_hasPn in Nx *; apply: contra Nx.
  case/hasP=>x; rewrite !mem_filter -!andbA=>/and4P [X1 X2 Px Kx] _.
  rewrite !olt_filter ?(P1,P2,Px,orbT) // in X1 X2.
  by apply/hasP; exists x=>//; rewrite !mem_filter Px Kx /= X1 X2.
- case/consecP=>Cx /nilP Nx.
  move: (slt_memE Cx); rewrite mem_filter=>/andP [P1 K1].
  split=>//; rewrite !nilp_hasPn in Nx *; apply: contra Nx.
  case/hasP=>x; rewrite !mem_filter=>/and3P [Px Nx Kx] _.
  apply/hasP; exists x=>//; rewrite !mem_filter -!andbA.
  apply/and4P; split=>//; first by rewrite olt_filter ?(P1,Px,orbT).
  apply: olt_memI; first by rewrite mem_filter Px Kx.
  by rewrite mem_filter P2.
case=>K1 P1 Nx; apply/consecP; split.
- apply: olt_memI; first by rewrite mem_filter P1 K1.
  by rewrite mem_filter P2.
apply/nilP; rewrite !nilp_hasPn in Nx *; apply: contra Nx.
case/hasP=>x; rewrite !mem_filter -!andbA; case/and4P=>N1 N2 Px Kx _.
apply/hasP; exists x=>//; rewrite !mem_filter Px Kx andbT /=.
by rewrite olt_filter ?(P1,Px,orbT) in N1.
Qed.

Lemma consecP_filter ks (p : pred _) t1 t2 :
        consec (filter p ks) t1 t2 <->
        if p t2 then
          [/\ t1 <[ks[ t2, p t1 & {in |sqint t1 t2 ks|, forall z, ~~ p z}]
        else [/\ t1 \in ks, p t1 & {in |sqint t1 ks}, forall z, ~~ p z}].
Proof.
split=>[|H].
- by move/consecP_nilp_filter; case: ifP=>P [?? /nilp_filter].
by apply/consecP_nilp_filter; case: ifP H=>P [?? /nilp_filter].
Qed.

Lemma olt_consec_prev ks t1 t2 :
        uniq ks ->
        t1 <[ks[ t2 <-> exists t, t1 <=[ks[ t /\ consec ks t t2.
Proof.
move=>U; split=>[H|]; last first.
- by case=>t [H1] /consecP [H2 _]; apply: (ole_olt_trans H1 H2).
case/olt_splitL: H U=>ks1 [ks2][-> Nt1t2 N1 N2] /=.
rewrite cat_uniq /= negb_or /= -!andbA.
case/and5P=>Uks1 Nt1ks1 /hasPn Hks2 Nt1ks2 Uks2.
case X : (t2 \in ks2); last first.
- have L : last t1 ks2 \notin ks1.
  - move: (mem_last t1 ks2); rewrite inE.
    by case/orP=>[/eqP ->//|H]; apply: Hks2.
  exists (last t1 ks2); split.
  - by rewrite ole_cat (negbTE N1) oleL andbT.
  apply/andP; split.
  - rewrite olt_cat (negbTE N2) (negbTE L) /= olt_cons (eq_sym t2) Nt1t2 /=.
    move: (mem_last t1 ks2); rewrite inE=>/orP [->//|H].
    by rewrite olt_memI ?X ?orbT.
  apply/hasPn=>x; rewrite mem_filter -!andbA; case/and3P.
  rewrite olt_cat; case Xks1 : (x \in ks1).
  - by move/slt_memE; rewrite (negbTE L).
  rewrite (negbTE L) /= olt_cons; case/andP=>Nxt1 O.
  rewrite olt_cat (negbTE N2) Xks1 /= olt_cons (eq_sym t2) Nt1t2 /=.
  rewrite (negbTE Nxt1) /= => Xp1.
  case/orP: O Xp1=>[/eqP/last_nochange|/[swap] Xp1].
  - by rewrite (negbTE Nt1ks2)=>/eqP ->.
  move: (@ole_last _ x t1 ks2)=>/(_ Uks2 (slt_memE Xp1)) Z.
  by move/(ole_olt_trans Z); rewrite olt_irr.
case/splitP: {ks2} X Hks2 Nt1ks2 Uks2=>p1 p2 H2.
rewrite mem_cat cat_uniq /= negb_or rcons_uniq mem_rcons inE.
rewrite (negbTE Nt1t2) /= -!andbA.
case/andP=>Nt1p1 Nt1p2 /and4P [Nt2p1 Up1 /hasPn Hp2 Up2].
have L : last t1 p1 \notin ks1.
- move: (mem_last t1 p1); rewrite inE.
  case/orP=>[/eqP ->//|H]; apply: H2.
  by rewrite mem_cat mem_rcons inE H orbT.
exists (last t1 p1); split.
- by rewrite ole_cat (negbTE Nt1ks1) oleL andbT.
apply/andP; split.
- rewrite olt_cat (negbTE N2) (negbTE L) /= olt_cons (eq_sym t2) Nt1t2 /=.
  rewrite olt_cat mem_rcons inE eq_refl /= olt_rcons (negbTE Nt2p1) eq_refl /=.
  by move: (mem_last t1 p1); rewrite inE=>/orP [->|->] //=; rewrite orbT.
apply/hasPn=>x; rewrite mem_filter -!andbA; case/and3P.
rewrite olt_cat; case Xks1 : (x \in ks1).
- by move/slt_memE; rewrite (negbTE L).
rewrite (negbTE L) /= olt_cons; case/andP=>Nxt1 O.
rewrite olt_cat (negbTE N2) Xks1 /= olt_cons (eq_sym t2) Nt1t2 /=.
rewrite (negbTE Nxt1) /= olt_cat mem_rcons inE eq_refl /=.
rewrite olt_rcons (negbTE Nt2p1) eq_refl /= orbF => Xp1.
case/orP: O Xp1=>[/eqP/last_nochange|/[swap] Xp1].
- by rewrite (negbTE Nt1p1)=>/eqP ->.
rewrite olt_cat mem_rcons inE Xp1 orbT olt_rcons Xp1.
move: (@ole_last _ x t1 p1)=>/(_ Up1 Xp1) Z.
by move/(ole_olt_trans Z); rewrite olt_irr.
Qed.

Lemma olt_consec_next ks t1 t2 :
        uniq ks ->
        t1 <[ks[ t2 <-> exists t, consec ks t1 t /\ t <=[ks[ t2.
Proof.
move=>U; split=>[H|]; last first.
- by case=>t [/consecP [X _] /(olt_ole_trans X)].
case/olt_splitL: H U=>ks1 [ks2][-> Nt1t2 N1 N2] /=.
rewrite cat_uniq /= negb_or -!andbA.
case/and5P=>Uks1 _ /hasPn Nks2 Nt1ks2 Uks2.
have H : head t2 ks2 \notin ks1.
- move: (mem_head t2 ks2); rewrite inE.
  by case/orP=>[/eqP ->//|]; apply: Nks2.
exists (head t2 ks2); split; last first.
- rewrite ole_cat (negbTE H) N2 /= ole_cons (eq_sym t2) Nt1t2 /=.
  by rewrite ole_head orbT.
apply/andP; split.
- rewrite olt_cat (negbTE H) (negbTE N1) /= oltL.
  case: eqP Nt1ks2 (mem_head t2 ks2)=>// -> X.
  by rewrite inE (negbTE Nt1t2) (negbTE X).
apply/hasPn=>x; rewrite mem_filter -andbA; case/and3P.
rewrite olt_cat; case Xks1 : (x \in ks1).
- by move/slt_memE; rewrite (negbTE N1).
rewrite (negbTE N1) oltL /= => Nxt1.
rewrite olt_cat (negbTE H) Xks1 /= olt_cons (negbTE Nxt1) /=.
by case/andP=>X /(ole_olt_trans (@ole_head _ t2 ks2 x)); rewrite olt_irr.
Qed.


(* previous element is uniquely determined *)
Lemma consec_prev_inj ks t t1 t2 :
         consec ks t1 t ->
         consec ks t2 t ->
         t1 = t2.
Proof.
case/andP=>T1 /hasPn H1 /andP [T2 /hasPn H2].
move: (@olt_total _ ks t1 t2 (slt_memE T1)).
case: eqP=>//= _ /orP [] N.
- by move: (H1 t2); rewrite mem_filter inE N T2=>/(_ (slt_memE T2)).
by move: (H2 t1); rewrite mem_filter inE N T1=>/(_ (slt_memE T1)).
Qed.

(* next of a non-last element is uniquely determined *)
Lemma consec_next_inj_nonlast ks t t1 t2 t3 :
         uniq ks ->
         t != last t3 ks ->
         consec ks t t1 ->
         consec ks t t2 -> t1 = t2.
Proof.
move=>U N C1 C2.
have K1 : t1 \in ks by apply: contraR N=>/(consec_lastE t3 U C1) ->.
have K2 : t2 \in ks by apply: contraR N=>/(consec_lastE t3 U C2) ->.
case/andP: C1 C2=>T1 /hasPn H1 /andP [T2 /hasPn H2].
move: (@olt_total _ ks t1 t2 K1); case: eqP=>//= _.
case/orP=>X; first by move: (H2 t1); rewrite mem_filter T1 X=>/(_ K1).
by move: (H1 t2); rewrite mem_filter T2 X=>/(_ K2).
Qed.

(* a restatement in a more useful form *)
Lemma consec_next_inj ks t t1 t2 :
         uniq ks ->
         t1 \in ks ->
         consec ks t t1 ->
         consec ks t t2 -> t1 = t2.
Proof.
move=>U T C1 C2; suff N : t != last t1 ks.
- by apply: consec_next_inj_nonlast U N C1 C2.
by apply: contraL T=>/eqP /(consec_lastE t1 U C1).
Qed.

(* consecutiveness and sortedness under general relation *)

Lemma consec_sorted_lt ltT ks t1 t2 :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        t2 \in ks ->
        consec ks t1 t2 ->
        {in ks, forall z, ltT z t2 = (z == t1) || ltT z t1}.
Proof.
move=>I Asym T S T2 C; move: (consec_mem C)=>T1.
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
rewrite (olt_sorted_leE Asym T S) //.
rewrite (ole_sorted_leE Asym T S) //.
by rewrite !orbA orbb; case: eqP=>//= ->; rewrite I.
Qed.

Lemma consec_sorted_le (leT : rel A) ks t1 t2 :
        {in ks, reflexive leT} ->
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        t2 \in ks ->
        consec ks t1 t2 ->
        {in ks, forall z, leT z t1 = (z != t2) && leT z t2}.
Proof.
move=>R Asym T S T2 C; move: (consec_mem C)=>T1.
move=>z Z; move/consec_in/(_ z Z): C.
rewrite (olt_sorted_leE Asym T S) //.
rewrite (ole_sorted_leE Asym T S) //.
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
- by apply: sort_sorted_in_lt=>//.
- by rewrite mem_sort.
by rewrite mem_sort.
Qed.

Lemma consec_sort_le leT ks t1 t2 :
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
- by rewrite mem_sort.
by rewrite mem_sort.
Qed.

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

Lemma consec_hd2 k1 k2 ks : k1 != k2 -> consec [:: k1, k2 & ks] k1 k2.
Proof.
move=>N; rewrite /consec !oltL eq_sym N /=.
apply/hasPn=>z; rewrite mem_filter !oltL !olt_cons (eq_sym k2 k1) N /= eq_refl.
by case: eqP.
Qed.

(* a useful lemma that collects the case analysis *)
(* for consec (k::ks) *)
Lemma consec_consEP' k k1 k2 ks :
        k \notin ks ->
        consec (k::ks) k1 k2 <->
        if k1 == k then
          if k2 \in ks then ks = k2 :: behead ks
          else k2 != k /\ ks = [::]
        else k2 != k /\ consec ks k1 k2.
Proof.
move=>U; split; last first.
- case: (k1 =P k)=>[->{k1}|/eqP Nk1k [Nk2]]; last first.
  - case/consecP=>H1 /nilP H2; apply/consecP.
    rewrite olt_cons (negbTE Nk1k) /= H1 andbT; split=>//.
    apply/nilP; rewrite !nilp_hasPn in H2 *.
    apply: contra H2=>/hasP [x H2 _]; apply/hasP; exists x=>//.
    move: H2; rewrite !mem_filter !olt_cons inE.
    by rewrite (negbTE Nk1k) Nk2 /=; case: (x =P k).
  case K2 : (k2 \in ks).
  - move=>E; rewrite {}E in U K2 *.
    rewrite inE negb_or in U; case/andP: U=>U1 U2.
    by apply: consec_hd2.
  case=>Nk2k E; rewrite {ks}E in U K2 *.
  apply/consecP; rewrite oltL; split=>//.
  apply/nilP; rewrite nilp_hasPn.
  apply/hasPn=>x; rewrite mem_filter oltL /=.
  rewrite olt_cons inE olt_nil orbF Nk2k /=.
  by case: (x =P k).
case: (k1 =P k)=>[->|/eqP Nk1k]; last first.
- move/consecP; rewrite olt_cons (negbTE Nk1k) /=.
  case=>/andP [Nk2k H1 /nilP H2]; split=>//; apply/consecP; split=>//.
  apply/nilP; rewrite !nilp_hasPn in H2 *; apply: contra H2=>/hasP [x] H _.
  apply/hasP; exists x=>//; rewrite !mem_filter in H *.
  rewrite olt_cons !inE olt_cons (negbTE Nk1k) (negbTE Nk2k) /=.
  by case: (x =P k) H=>//= ->{x}; rewrite (negbTE U) andbF.
case K2: (k2 \in ks)=>/consecP []; rewrite oltL => Nk2k /nilP; last first.
- move=>H; split=>//; apply/nilP; rewrite !nilp_hasPn in H *.
  apply: contra H=>/hasP [x X _]; apply/hasP; exists x=>//.
  rewrite mem_filter oltL olt_cons inE X Nk2k /= orbT andbT.
  case: (x =P k) X U=>[->->//|/eqP Nxk X U /=].
  by apply: olt_memI=>//; rewrite K2.
case: ks U K2=>//= x ks; rewrite !inE negb_or nilp_hasPn.
case/andP=>Nkx U K2 H; congr (_ :: _).
case: (k2 =P x) K2=>[->//|/eqP Nk2x /= K2].
move/negP: H; elim; apply/hasP; exists x=>//.
rewrite mem_filter !oltL !olt_cons eq_refl andbT inE inE eq_refl orbT andbT.
by rewrite Nk2x Nk2k /= eq_sym Nkx orbT.
Qed.

Lemma consec_consEP k k1 k2 ks :
        k \notin ks ->
        consec (k::ks) k1 k2 <->
        if k1 == k then
          if k2 \in ks then k2 = head k ks
          else k2 != k /\ ks = [::]
        else k2 != k /\ consec ks k1 k2.
Proof.
move/consec_consEP'=>->.
case: ifP=>// E1; case: ifP=>//.
by case: ks=>//= x ks E2; split=>[[]|->].
Qed.

(* let's make them boolean *)
Lemma consec_consE' k k1 k2 ks :
        k \notin ks ->
        consec (k::ks) k1 k2 =
        if k1 == k then
          if k2 \in ks then ks == k2 :: behead ks
          else (k2 != k) && (ks == [::])
        else (k2 != k) && consec ks k1 k2.
Proof.
move=>K; rewrite iffE consec_consEP' //.
case: ifP=>H1; last by case: andP.
case: ifP=>H2; first by case: eqP.
by split; [case=>->->|case/andP=>-> /eqP].
Qed.

Lemma consec_consE k k1 k2 ks :
        k \notin ks ->
        consec (k::ks) k1 k2 =
        if k1 == k then
          if k2 \in ks then k2 == head k ks
          else (k2 != k) && (ks == [::])
        else (k2 != k) && consec ks k1 k2.
Proof.
move=>K; rewrite iffE consec_consEP //.
case: ifP=>H1; last by case: andP.
case: ifP=>H2; first by case: eqP.
by split; [case=>->->|case/andP=>-> /eqP].
Qed.

(* for rcons, we need a uniqueness condition *)
Lemma consec_rconsEP' k k1 k2 ks :
        uniq ks -> k \notin ks ->
        consec (rcons ks k) k1 k2 <->
        if k1 != k then
          if k2 \notin ks then k2 = k /\ exists ks', ks = rcons ks' k1
          else consec ks k1 k2
        else k2 \notin rcons ks k.
Proof.
move=>U K; split; last first.
- case: eqP=>[-> /= K2|/eqP N /=].
  - by apply/consecP_last=>//; [rewrite rcons_uniq K U | exists ks].
  case: ifP=>K2; last first.
  - move/negbT: K2; rewrite negbK=>K2 /consecP_inlt [K1 E].
    apply/consecP_inlt; split; first by rewrite mem_rcons inE K1 orbT.
    move=>z; rewrite mem_rcons inE; case/orP=>[/eqP ->{z}|Z].
    - rewrite olt_rcons K2 ole_rcons (negbTE K) eq_refl andbT K1 /=.
      by apply/negP=>/slt_memE; rewrite (negbTE K).
    by rewrite olt_rcons K2 ole_rcons Z; apply: E.
  case=>->{k2 K2} [ks' E]; rewrite {ks}E in U K *.
  apply/consecP_inlt; split.
  - by rewrite mem_rcons inE mem_rcons inE eq_refl orbT.
  rewrite rcons_uniq in U; case/andP: U=>N1 U.
  rewrite mem_rcons inE  negb_or eq_sym N /= in K.
  move=>z; rewrite mem_rcons inE mem_rcons inE => Z.
  rewrite olt_rcons mem_rcons inE eq_sym (negbTE N) (negbTE K) /=.
  rewrite eq_refl orbF !ole_rcons N1 /= eq_refl orbF !mem_rcons !inE eq_refl /=.
  case: eqP Z=>[->{z} /= _|/eqP Nz /=].
  - by rewrite eq_sym (negbTE N) /=; case: ifP=>// K'; rewrite K' ole_memI.
  rewrite (eq_sym z); case: eqP=>[/= ->|/=]; first by rewrite ole_refl if_same.
  by move=>_ Z; rewrite Z ole_memI.
case/consecP_inlt=>K1 E.
move: K1; rewrite mem_rcons inE=>K1.
case/orP: K1 E=>[/eqP ->{k1}|K1] E.
- rewrite eq_refl /=.
  move: (E k); rewrite mem_rcons inE eq_refl=>/(_ erefl).
  rewrite ole_refl; apply: contraL; rewrite mem_rcons inE.
  case/orP=>[/eqP ->|K2]; first by rewrite olt_irr.
  rewrite olt_rcons K2; apply/negP.
  by move/(olt_trans (olt_memI K2 K))/oltxx.
case: eqP K1 K=>[->->//|/eqP N K1 K /=]; case: ifP=>K2; last first.
- move/negbT: K2; rewrite negbK=>K2; apply/consecP_inlt; split=>//.
  move=>z Z; move: (E z); rewrite mem_rcons inE Z orbT=>/(_ erefl).
  by rewrite olt_rcons K2 ole_rcons Z.
move: (E k); rewrite mem_rcons inE eq_refl=>/(_ erefl).
rewrite olt_rcons (negbTE K2) (negbTE K) /= eq_refl andbT.
rewrite ole_rcons (negbTE K) K1 /=; case: eqP=>// -> _; split=>//.
suff -> : k1 = last k1 ks.
- move: ks {E N U K K2} k1 K1; apply: last_ind=>[//|ks x IH] k1.
  rewrite mem_rcons inE; case/orP=>[/eqP ->|].
  - by rewrite last_rcons; exists ks.
  by case/IH=>ks' E; rewrite last_rcons; exists ks.
apply/eqP; case: eqP=>// /eqP; rewrite eq_sym=>M.
move: (last_change M)=>L.
move: (E (last k1 ks)); rewrite mem_rcons inE L orbT=>/(_ erefl).
rewrite olt_rcons ole_rcons (negbTE K2) L /=.
move/esym; rewrite (sle_eqVlt (or_intror K1)) (negbTE M) /=.
by move/(ole_olt_trans (ole_last k1 U K1))/oltxx.
Qed.

Lemma consec_rconsEP k k1 k2 ks :
        uniq ks -> k \notin ks ->
        consec (rcons ks k) k1 k2 <->
        if k1 != k then
          if k2 \notin ks then k2 = k /\ k1 = last k ks
          else consec ks k1 k2
        else k2 \notin rcons ks k.
Proof.
move=>U K; rewrite consec_rconsEP' //.
case: eqP=>//= /eqP N1; case: ifP=>// N2.
split; case=>->; first by case=>ks' ->; rewrite last_rcons.
move/esym=>E; split=>//; rewrite -E.
have : last k ks != k by rewrite E.
move/last_change=>{N1 N2}E.
move: ks k U K E; apply: last_ind=>// xs x IH k U K E.
by rewrite last_rcons; exists xs.
Qed.

(* boolean version *)
Lemma consec_rconsE' y k k1 k2 ks :
        uniq ks -> k \notin ks ->
        consec (rcons ks k) k1 k2 =
        if k1 != k then
          if k2 \notin ks then [&& k2 == k, k1 == last y ks & k1 \in ks]
          else consec ks k1 k2
        else k2 \notin rcons ks k.
Proof.
move=>U K; rewrite iffE consec_rconsEP' //.
case: ifP=>_ //; case: ifP=>_ //; split.
- by case=>X1 /(rcons_lastXP _ y); rewrite X1 eq_refl.
case/and3P=>/eqP X1 X2 X3; split=>//.
by apply/(rcons_lastXP _ y); rewrite X2 X3.
Qed.

(* This one is the same, except it drops k1 \in ks condition *)
(* and replaces y by k. The simplifications may be desirable *)
(* depending on the direction of rewriting *)
Lemma consec_rconsE k k1 k2 ks :
        uniq ks -> k \notin ks ->
        consec (rcons ks k) k1 k2 =
        if k1 != k then
          if k2 \notin ks then (k2 == k) && (k1 == last k ks)
          else consec ks k1 k2
        else k2 \notin rcons ks k.
Proof.
move=>U K; rewrite iffE consec_rconsEP //.
case: ifP=>H1 //; case: ifP=>H2 //.
by split; [case=>->->; rewrite !eq_refl|case/andP=>/eqP -> /eqP ->].
Qed.

Lemma consec_behead k ks x y :
        k \notin ks -> x != k ->
        consec (k::ks) x y -> y != k /\ consec ks x y.
Proof. by move=>K Nx /(consec_consEP _ _ K); rewrite (negbTE Nx). Qed.

(* the following isn't a consecuence of consec_consE *)
(* as it's independent of k \notin ks *)
Lemma consec_cons k ks x y :
        x != k -> y != k -> consec ks x y -> consec (k::ks) x y.
Proof.
move=>Nx Ny; rewrite /consec olt_cons Ny (negbTE Nx) /=.
case/andP=>->; apply: contra; case/hasP=>z Z _; apply/hasP; exists z=>//.
rewrite !mem_filter inE !olt_cons (negbTE Nx) Ny !(eq_sym z) in Z *.
by case: eqP Z.
Qed.

(* Pairs of consecutive elements are totally ordered. *)
(* That is: either the two pairs are the same pair, *)
(* or one of the second projections is ordered before the *)
(* first projection of the other pair. *)
Lemma consec2_total ks x1 x2 y1 y2 :
        uniq ks ->
        y1 \in ks \/ y2 \in ks ->
        consec ks x1 y1 -> consec ks x2 y2 ->
        [|| (x1 == x2) && (y1 == y2), y2 <=[ks[ x1 | y1 <=[ks[ x2].
Proof.
move=>U.
suff L a1 a2 b1 b2 : b1 \in ks ->
  consec ks a1 b1 -> consec ks a2 b2 ->
  [|| (a1 == a2) && (b1 == b2), b2 <=[ks[ a1 | b1 <=[ks[ a2].
- case=>Y Cx1 Cx2; first by apply: L.
  case/or3P: (L _ _ _ _ Y Cx2 Cx1)=>[|->|->]; try by rewrite !orbT.
  by case/andP=>/eqP/esym -> /eqP/esym ->; rewrite !eq_refl.
move=>Y1 Cx1 Cx2; move: (consec_mem Cx1) (consec_mem Cx2)=>X1 X2.
case/or3P: (olt_total a2 X1) Cx2 X2=>[/eqP <-{a2}|H|H] Cx2 X2.
- by rewrite (consec_next_inj U Y1 Cx1 Cx2) !eq_refl.
- by rewrite (consec_next Cx1 H) !orbT.
by rewrite (consec_next Cx2 H) !orbT.
Qed.

(***************************************)
(* Consecutiveness induction principle *)
(***************************************)

Lemma consec_ind_raw k ks (P : A -> Prop) :
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
by do 2![apply: consec_cons=>//]; case/(consec_behead K2 Nt1k): C.
Qed.

(* somewhat modified variant of consec_ind_raw *)
(* where we supply the starting k by hand *)
Lemma consec_ind k ks (P : A -> Prop) :
        uniq (k :: ks) ->
        P k ->
        (forall t1 t2, t2 \in ks -> consec (k::ks) t1 t2 -> P t1 -> P t2) ->
        forall t, t \in ks -> P t.
Proof.
move=>/= /andP [U1 U2] P0 IH t D; apply: consec_ind_raw IH _ _=>//.
by rewrite inE D orbT.
Qed.

(* a version that deconstructs ks to find the starting point *)
(* and gives us useful (though derivable) membership predicates t1 \in ks *)
Lemma consec_indX (ks : seq A) (P : A -> Prop) :
        uniq ks ->
        (forall t1, t1 \in ks -> ks = t1 :: behead ks -> P t1) ->
        (forall t1 t2, t1 \in ks -> t2 \in ks -> consec ks t1 t2 ->
           P t1 -> P t2) ->
        forall t, t \in ks -> P t.
Proof.
case: ks=>//= k ks /andP [K U] H1 H2; apply: consec_ind_raw=>//.
- by apply: (H1 k)=>//; rewrite inE eq_refl.
move=>t1 t2 N Cx; apply: H2=>//.
- by rewrite (consec_mem Cx).
by rewrite inE N orbT.
Qed.

(* special variants when we induct over an interval *)
(* that is open/closed/unbounded on the right *)
Lemma consec_indo ks k1 k2 (P : A -> Prop) :
        uniq ks -> k1 <[ks[ k2 ->
        P k1 ->
        (forall t1 t2,
           t2 \in |sqint k1 k2 ks| ->
           consec [sqint k1 k2 ks| t1 t2 -> P t1 -> P t2) ->
        forall t, t \in |sqint k1 k2 ks| -> P t.
Proof.
move=>U N H0 IH t; apply: (consec_ind (k:=k1))=>//=.
- by rewrite filter_uniq // andbT mem_filter olt_irr.
move=>t1 t2 H C; apply: IH=>//; rewrite sqxoL //.
by apply: slt_memE N.
Qed.

Lemma consec_indx ks k1 k2 (P : A -> Prop) :
        uniq ks -> k1 <=[ks[ k2 -> k1 \in ks ->
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

Lemma consec_indu ks k (P : A -> Prop) :
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

End ConsecEq.

Section ConsecOrd.
Variable (A : ordType).
Implicit Type (ks : seq A).

(* consecutiveness and sortedness under A *)

Lemma consec_sorted ks t1 t2 :
        sorted ord ks -> t2 \in ks -> consec ks t1 t2 ->
        {in ks, forall z, ord z t2 = oleq z t1}.
Proof.
move=>S T2 /consecP_inlt [T1 H] z Z.
rewrite -(olt_sortedE S Z T2) -(ole_sortedE S Z T1).
by apply: H Z.
Qed.

End ConsecOrd.

Section ConsecNat.

(* an element is either first, or has a predecessor *)
Lemma consec_prevX (ks : seq nat) x :
        uniq ks ->
        x \in ks ->
        ks = x :: behead ks \/ exists y, consec ks y x.
Proof.
case: (not_memX ks)=>k N U X.
have {}U : uniq (k :: ks) by rewrite /= N U.
have : k <[k::ks] x by rewrite oltL; case: eqP X N=>// ->->.
case/(olt_consec_prev _ _ U)=>t [_]; rewrite consec_consEP' //.
by case: eqP X=>[_ ->|_ _ []]; [left|right; exists t].
Qed.

(* an element is either last, or has a successor *)
Lemma consec_nextX (ks : seq nat) x :
        uniq ks ->
        x \in ks ->
        (exists ks', ks = rcons ks' x) \/ exists y, consec ks x y.
Proof.
case: (not_memX ks)=>k N U X.
have Ur : uniq (rcons ks k) by rewrite rcons_uniq N U.
have : x <[rcons ks k] k by rewrite olt_rcons (negbTE N) eq_refl orbF.
case/(olt_consec_next _ _ Ur)=>t [].
rewrite consec_rconsEP' //.
case: eqP X N=>[->->//|/eqP Nkx X N /=].
case T: (t \in ks)=>/=; first by right; exists t.
by case=>-> {t T} [ks' -> _]; left; exists ks'.
Qed.

End ConsecNat.
