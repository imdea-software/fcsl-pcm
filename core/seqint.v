From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import options prelude ordtype.

(* there always exists a nat not in a given list *)
Lemma not_memX (ks : seq nat) : exists k, k \notin ks.
Proof.
have L a xs : foldl addn a xs = a + foldl addn 0 xs.
- elim: xs a=>[|z xs IH] //= a; first by rewrite addn0.
  by rewrite add0n // [in LHS]IH [in RHS]IH addnA.
set k := foldl addn 1 ks.
suff K a : a \in ks -> a < k by exists k; apply/negP=>/K; rewrite ltnn.
rewrite {}/k; elim: ks=>[|k ks IH] //=; rewrite inE.
case/orP=>[/eqP ->|/IH]; first by rewrite L add1n addSn ltnS leq_addr.
rewrite L=>N; rewrite L; apply: leq_trans N _.
by rewrite addnAC leq_addr.
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

Lemma neq_olt x y ks : x <[ks] y -> y != x.
Proof. by move/olt_neq; case: ltngtP. Qed.

Lemma oltxx x ks : ~ x <[ks] x.
Proof. by rewrite olt_irr. Qed.

Lemma olt_antisym ks : antisymmetric (seq_lt ks).
Proof. by move=>x y; rewrite /seq_lt; case: ltngtP. Qed.

(* antisymmetry is too weak for olt *)
Lemma olt_asym ks x y : x <[ks] y -> y <=[ks] x -> false.
Proof. by rewrite /seq_lt/seq_le; case: ltngtP. Qed.

Lemma olt_trans ks : transitive (seq_lt ks).
Proof. by move=>x y z; apply: ltn_trans. Qed.

Lemma olt_total' ks : {in ks &, total (fun x y => (x == y) || seq_lt ks x y)}.
Proof.
rewrite /seq_lt=>x y K1 _.
case: ltngtP=>//; rewrite ?orbT ?orbF //.
by move/index_inj=>-> //; rewrite eq_refl.
Qed.

(* a stronger variant *)
Lemma olt_total ks x y : x \in ks -> [|| x == y, x <[ks] y | y <[ks] x].
Proof.
rewrite /seq_lt=>X; case: ltngtP; rewrite ?orbT ?orbF //.
by move/index_inj=>-> //.
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
        uniq ks -> x \in ks -> x <=[ks] (last k ks).
Proof. by apply: index_last_mono. Qed.

Lemma ole_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks -> x <=[k::ks] (last k ks).
Proof.
move=>U; move: (U)=>/= /andP [U1 U2].
rewrite inE ole_cons; case: eqP=>//= /eqP Nxk K.
by rewrite (last_notin K) //= ole_last.
Qed.

Lemma olt_last x k ks :
        uniq ks -> x \in ks -> last k ks != x -> x <[ks] (last k ks).
Proof.
move=>U X N; move: (ole_last k U X); rewrite ole_eqVlt; last by left.
by rewrite eq_sym (negbTE N).
Qed.

Lemma olt_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks ->
        last k ks != x -> x <[k::ks] (last k ks).
Proof.
move=>U X N; rewrite olt_neqAle; last by right; apply: mem_last.
by rewrite eq_sym N ole_last_cons.
Qed.

(* sequence ordering and head *)

Lemma ole_head x ks y : (head x ks) <=[ks] y.
Proof. by case: ks=>[|k ks] //=; rewrite oleL. Qed.


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

(* DEVCOMMENT: this lemma exists in a less general form as `sub_path_in` in 1.11, *)
(* it was generalized in 1.12 and renamed in 1.13. *)
(* TODO remove when dropping 1.12 *)
Local Lemma sub_in_path (T : eqType) (P : {pred T}) (e e' : rel T)
                        (ee' : {in P &, subrel e e'}) : forall x s,
                        all P (x :: s) -> path e x s -> path e' x s.
Proof.
by move=>x s; elim: s x=>//= y s ihs x /and3P [? ? ?] /andP [/ee' -> //]; apply/ihs/andP.
Qed.

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
(* if we add antisymmetry *)
(* and the condition that x \in ks *)
Lemma olt_sorted_ltE ltT ks x y :
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        x \in ks -> y \in ks ->
        x <[ks] y = (x != y) && ltT x y.
Proof.
move=>As T S X Y; apply/idP/idP.
- by case: eqP=>[->|/eqP N] /=; [rewrite olt_irr | apply: olt_sorted_lt].
by case/andP=>H K; apply: sorted_ord_index_leq K H.
Qed.

(* if we add antisymmetry and t1 \in ks *)
Lemma ole_sorted_ltE ltT ks x y :
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        x \in ks -> y \in ks ->
        x <=[ks] y = (x == y) || ltT x y.
Proof.
move=>As T S X Y; rewrite ole_eqVlt; last by right.
by rewrite (olt_sorted_ltE As T S X Y); case: eqP.
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

Lemma consecP_inlt (ks : seq nat) t1 t2 :
        reflect ([/\ t1 \in ks & {in ks, forall z, z <[ks] t2 = z <=[ks] t1}])
                (consec ks t1 t2).
Proof.
case C: (consec ks t1 t2); constructor.
- case/andP: C=>T E; split; first by apply: olt_memE T.
  by move=>z Z; apply: hasNL_oo T E _ Z _.
case=>T H; apply: (elimF idP) C _.
by rewrite /consec H // ole_refl hasNR_oo // => z /H.
Qed.

Lemma consecP_ingt (ks : seq nat) t1 t2 :
        reflect ([/\ t1 \in ks & {in ks, forall z, t2 <=[ks] z = t1 <[ks] z}])
                (consec ks t1 t2).
Proof.
case: consecP_inlt.
- case=>T1 H; constructor.
  by split=>// z /H E; rewrite oleNgt E -oltNge.
move=>H1; constructor; case=>T1 H; elim: H1.
by split=>// z /H E; rewrite oleNgt -E -oltNge.
Qed.


(* frequent projections *)

Lemma consec_olt ks t1 t2 : consec ks t1 t2 -> t1 <[ks] t2.
Proof. by case/andP. Qed.

Lemma consec_oltW ks t1 t2 : consec ks t1 t2 -> t1 <=[ks] t2.
Proof. by move/consec_olt/oltW. Qed.

Lemma consec_mem ks t1 t2 : consec ks t1 t2 -> t1 \in ks.
Proof. by case/andP=>/olt_memE. Qed.

Lemma consec_oo ks t1 t2 : consec ks t1 t2 -> |sqint t1 t2 ks| = [::].
Proof. by case/consecP. Qed.

Lemma consec_in ks t1 t2 :
        consec ks t1 t2 -> {in ks, forall z, z <[ks] t2 = z <=[ks] t1}.
Proof. by case/consecP_inlt. Qed.

(* and some streamlining *)

Lemma consec_prev (ks : seq nat) x y z :
        consec ks x y -> z <[ks] y -> z <=[ks] x.
Proof. by case/consecP_inlt=>X E N; rewrite -E // (olt_memE N). Qed.

Lemma consec_prevN ks x y z :
        z != x -> consec ks x y -> z <[ks] y -> z <[ks] x.
Proof.
move=>N C /(consec_prev C).
by rewrite (ole_eqVlt (or_intror (consec_mem C))) (negbTE N).
Qed.

Lemma consec_next (ks : seq nat) x y z :
        consec ks x y -> x <[ks] z -> y <=[ks] z.
Proof.
case/consecP_ingt=>X E N; case Dz : (z \in ks); first by rewrite E.
by apply: ole_memI; rewrite Dz.
Qed.

Lemma consec_nextN ks x y z :
        y \in ks \/ z \in ks ->
        y != z -> consec ks x y -> x <[ks] z -> y <[ks] z.
Proof.
move=>D N C /(consec_next C).
by rewrite (ole_eqVlt D) (negbTE N).
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
  by rewrite (olt_memE Nt) in Nx.
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
by move/olt_memE; rewrite (negbTE T1).
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
        if p t2 then [/\ t1 <[ks] t2, p t1 & nilp (filter p |sqint t1 t2 ks|)]
        else [/\ t1 \in ks, p t1 & nilp (filter p |sqint t1 ks})].
Proof.
case: ifP=>P2; split.
- case/consecP=>Cx /nilP Nx.
  move: (olt_memE Cx); rewrite mem_filter=>/andP [P1 K1].
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
  move: (olt_memE Cx); rewrite mem_filter=>/andP [P1 K1].
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
          [/\ t1 <[ks] t2, p t1 & {in |sqint t1 t2 ks|, forall z, ~~ p z}]
        else [/\ t1 \in ks, p t1 & {in |sqint t1 ks}, forall z, ~~ p z}].
Proof.
split=>[|H].
- by move/consecP_nilp_filter; case: ifP=>P [?? /nilp_filter].
by apply/consecP_nilp_filter; case: ifP H=>P [?? /nilp_filter].
Qed.

Lemma olt_consec_prev ks t1 t2 :
        uniq ks ->
        t1 <[ks] t2 <-> exists t, t1 <=[ks] t /\ consec ks t t2.
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
  - by move/olt_memE; rewrite (negbTE L).
  rewrite (negbTE L) /= olt_cons; case/andP=>Nxt1 O.
  rewrite olt_cat (negbTE N2) Xks1 /= olt_cons (eq_sym t2) Nt1t2 /=.
  rewrite (negbTE Nxt1) /= => Xp1.
  case/orP: O Xp1=>[/eqP/last_nochange|/[swap] Xp1].
  - by rewrite (negbTE Nt1ks2)=>/eqP ->.
  move: (@ole_last x t1 ks2)=>/(_ Uks2 (olt_memE Xp1)) Z.
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
- by move/olt_memE; rewrite (negbTE L).
rewrite (negbTE L) /= olt_cons; case/andP=>Nxt1 O.
rewrite olt_cat (negbTE N2) Xks1 /= olt_cons (eq_sym t2) Nt1t2 /=.
rewrite (negbTE Nxt1) /= olt_cat mem_rcons inE eq_refl /=.
rewrite olt_rcons (negbTE Nt2p1) eq_refl /= orbF => Xp1.
case/orP: O Xp1=>[/eqP/last_nochange|/[swap] Xp1].
- by rewrite (negbTE Nt1p1)=>/eqP ->.
rewrite olt_cat mem_rcons inE Xp1 orbT olt_rcons Xp1.
move: (@ole_last x t1 p1)=>/(_ Up1 Xp1) Z.
by move/(ole_olt_trans Z); rewrite olt_irr.
Qed.

Lemma olt_consec_next ks t1 t2 :
        uniq ks ->
        t1 <[ks] t2 <-> exists t, consec ks t1 t /\ t <=[ks] t2.
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
- by move/olt_memE; rewrite (negbTE N1).
rewrite (negbTE N1) oltL /= => Nxt1.
rewrite olt_cat (negbTE H) Xks1 /= olt_cons (negbTE Nxt1) /=.
by case/andP=>X /(ole_olt_trans (@ole_head t2 ks2 x)); rewrite olt_irr.
Qed.


(* previous element is uniquely determined *)
Lemma consec_prev_inj ks t t1 t2 :
         consec ks t1 t ->
         consec ks t2 t ->
         t1 = t2.
Proof.
case/andP=>T1 /hasPn H1 /andP [T2 /hasPn H2].
move: (@olt_total ks t1 t2 (olt_memE T1)).
case: eqP=>//= _ /orP [] N.
- by move: (H1 t2); rewrite mem_filter inE N T2=>/(_ (olt_memE T2)).
by move: (H2 t1); rewrite mem_filter inE N T1=>/(_ (olt_memE T1)).
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
move: (@olt_total ks t1 t2 K1); case: eqP=>//= _.
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

(* consecutiveness and sortedness under nat *)

Lemma consec_sorted ks t1 t2 :
        sorted ltn ks -> t2 \in ks -> consec ks t1 t2 ->
        {in ks, forall z, (z < t2) = (z <= t1)}.
Proof.
move=>S T2 /consecP_inlt [T1 H] z Z.
rewrite -(olt_sortedE S Z T2) -(ole_sortedE S Z T1).
by apply: H Z.
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
rewrite (olt_sorted_ltE Asym T S) //.
rewrite (ole_sorted_ltE Asym T S) //.
by rewrite !orbA orbb; case: eqP=>//= ->; rewrite I.
Qed.

Lemma consec_sorted_le (leT : rel nat) ks t1 t2 :
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
rewrite (olt_sorted_ltE Asym T S) //.
rewrite (ole_sorted_ltE Asym T S) //.
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
Lemma consec_consEP' k k1 k2 (ks : seq nat) :
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

Lemma consec_consEP k k1 k2 (ks : seq nat) :
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
Lemma consec_consE' k k1 k2 (ks : seq nat) :
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

Lemma consec_consE k k1 k2 (ks : seq nat) :
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
Lemma consec_rconsEP' k k1 k2 (ks : seq nat) :
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
      by apply/negP=>/olt_memE; rewrite (negbTE K).
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
move/esym; rewrite (ole_eqVlt (or_intror K1)) (negbTE M) /=.
by move/(ole_olt_trans (ole_last k1 U K1))/oltxx.
Qed.

Lemma consec_rconsEP k k1 k2 (ks : seq nat) :
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
Lemma consec_rconsE' y k k1 k2 (ks : seq nat) :
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
Lemma consec_rconsE k k1 k2 (ks : seq nat) :
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

(* an element is either first, or has a predecessor *)
Lemma consec_prevX ks x :
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
Lemma consec_nextX ks x :
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

(* Pairs of consecutive elements are totally ordered. *)
(* That is: either the two pairs are the same pair, *)
(* or one of the second projections is ordered before the *)
(* first projection of the other pair. *)
Lemma consec2_total ks x1 x2 y1 y2 :
        uniq ks ->
        y1 \in ks \/ y2 \in ks ->
        consec ks x1 y1 -> consec ks x2 y2 ->
        [|| (x1 == x2) && (y1 == y2), y2 <=[ks] x1 | y1 <=[ks] x2].
Proof.
move=>U.
suff L a1 a2 b1 b2 : b1 \in ks ->
  consec ks a1 b1 -> consec ks a2 b2 ->
  [|| (a1 == a2) && (b1 == b2), b2 <=[ks] a1 | b1 <=[ks] a2].
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
by do 2![apply: consec_cons=>//]; case/(consec_behead K2 Nt1k): C.
Qed.

(* somewhat modified variant of consec_ind_raw *)
(* where we supply the starting k by hand *)
Lemma consec_ind k (ks : seq nat) (P : nat -> Prop) :
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
Lemma consec_indX (ks : seq nat) (P : nat -> Prop) :
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
