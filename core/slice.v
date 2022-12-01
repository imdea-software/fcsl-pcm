From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype seqext.

Open Scope order_scope.
Import Order.Theory.

(* TODO move to prelude *)
Lemma if_triv b : (if b then true else false) = b.
Proof. by case: b. Qed.

Lemma drop_take_id {A} x (s : seq A) : drop x (take x s) = [::].
Proof. by rewrite -{2}(add0n x) -take_drop take0. Qed.

Lemma drop_take_mask {A} (s : seq A) x y :
        drop x (take y s) = mask (nseq x false ++ nseq (y-x) true) s.
Proof.
case: (ltnP x (size s))=>Hx; last first.
- rewrite drop_oversize; last by rewrite size_take_min geq_min Hx orbT.
  rewrite -{1}(subnKC Hx) nseqD -catA -{3}(cats0 s) mask_cat; last by rewrite size_nseq.
  by rewrite mask0 mask_false.
have Hx': size (nseq x false) = size (take x s).
- by rewrite size_nseq size_take_min; symmetry; apply/minn_idPl/ltnW.
rewrite -{2}(cat_take_drop x s) mask_cat // mask_false /= -takeEmask take_drop.
case: (leqP x y)=>[Hxy|/ltnW Hxy]; first by rewrite subnK.
move: (Hxy); rewrite -subn_eq0=>/eqP->; rewrite add0n drop_take_id.
by rewrite drop_oversize // size_take_min geq_min Hxy.
Qed.

(* weaker form of in_mask *)
Lemma in_mask_count {A : eqType} x m (s : seq A) :
  (count_mem x s <= 1)%N -> x \in mask m s = (x \in s) && nth false m (index x s).
Proof.
elim: s m => [|y s IHs] m /=; first by rewrite mask0 in_nil.
case: m=>/=[|b m]; first by rewrite in_nil nth_nil andbF.
case: b; rewrite !inE eq_sym; case: eqP=>//= _.
- by rewrite add0n; apply: IHs.
- rewrite -{2}(addn0 1%N) leq_add2l leqn0 => /eqP Hc.
  rewrite IHs; last by rewrite Hc.
  by move/count_memPn/negbTE: Hc=>->.
by rewrite add0n; apply: IHs.
Qed.

Lemma mem_take_index {A : eqType} x (s : seq A) :
        x \notin take (index x s) s.
Proof.
elim: s=>//=h s; case: eqP=>//= /eqP H IH.
by rewrite inE negb_or eq_sym H.
Qed.

Lemma mem_drop_index_last {A : eqType} x (s : seq A) :
        x \notin drop (index_last x s).+1 s.
Proof.
elim: s=>//=h s; rewrite index_last_cons.
case: eqP=>//= _ H.
by case: ifP=>//=; rewrite drop0.
Qed.

Lemma prefix_drop_sub {A : eqType} (s1 s2 : seq A) :
        seq.prefix s1 s2 ->
        forall n, {subset (drop n s1) <= drop n s2}.
Proof.
case/seq.prefixP=>s0 {s2}-> n x H.
rewrite drop_cat; case: ltnP=>Hn.
- by rewrite mem_cat H.
by move: H; rewrite drop_oversize.
Qed.

(* convert bound to nat *)
(* maps -oo -> 0, +oo -> m *)
Definition bnd (i : itv_bound nat) (m : nat) : nat :=
  match i with
  | BSide  b n => n + ~~ b
  | BInfty b   => if b then 0 else m
  end.

(* slicing is applying an interval to a seq *)
Definition slice {A : Type} (s : seq A) (i : interval nat) :=
  let sz := size s in
  let: Interval l u := i in
  drop (bnd l sz) (take (bnd u sz) s).

Arguments slice {A} s i : simpl never.

Notation "&: s i" := (slice s i)
 (at level 1, i at next level, s at next level,
  format "'&:' s  i") : fun_scope.

(* subtract n from bound, convert values past zero to -oo *)
Definition shl_bnd (i : itv_bound nat) (n : nat) :=
  match i with
  | BSide  b m => if (m < n)%N then -oo else BSide b (m - n)
  | BInfty b => BInfty _ b
  end.

Lemma shl_bnd0 i : shl_bnd i 0 = i.
Proof. by case: i=>[[] i|[]] //=; rewrite subn0. Qed.

Lemma shl_bnd_add i n m : shl_bnd (shl_bnd i n) m = shl_bnd i (n+m).
Proof.
case: i=>[[] i|[]] //=.
- case: ltnP=>Hin /=; first by rewrite ltn_addr.
  by rewrite ltn_subLR // subnDA.
case: ltnP=>Hin /=; first by rewrite ltn_addr.
by rewrite ltn_subLR // subnDA.
Qed.

Definition shl_itv (i : interval nat) (n : nat) :=
  let: Interval l u := i in
  Interval (shl_bnd l n) (shl_bnd u n).

Lemma shl_itv0 i : shl_itv i 0 = i.
Proof. by case: i=>i j /=; rewrite !shl_bnd0. Qed.

Lemma shl_itv_add i n m : shl_itv (shl_itv i n) m = shl_itv i (n+m).
Proof. by case: i=>i j /=; rewrite !shl_bnd_add. Qed.

Lemma mem_shl n m i :
  (n \in shl_itv i m) = (m + n \in i).
Proof.
rewrite !in_itv; case: i=>i j /=.
case: i=>[[] i|[]]; case: j=>[[] j|[]] /=;
rewrite ?leEnat ?ltEnat ?addn0 ?addn1 ?andbF ?andbT //=.
- case: (ltnP i m)=>/= Hi; case: (ltnP j m)=>/= Hj.
  - symmetry; apply/negbTE; rewrite negb_and -leqNgt -ltnNge.
    by apply/orP; right; apply/ltnW/ltn_addr.
  - have ->/=: (i <= m + n)%N by apply/ltnW/ltn_addr.
    by rewrite ltEnat /= ltn_subRL.
  - rewrite andbF; symmetry; apply/negbTE; rewrite negb_and -leqNgt -ltnNge.
    by apply/orP; right; apply/ltnW/ltn_addr.
  - by rewrite leEnat ltEnat /= ltn_subRL leq_subLR.
- case: (ltnP i m)=>/= Hi; case: (ltnP j m)=>/= Hj.
  - symmetry; apply/negbTE; rewrite negb_and -!ltnNge.
    by apply/orP; right; apply/ltn_addr.
  - have ->/=: (i <= m + n)%N by apply/ltnW/ltn_addr.
    by rewrite leEnat /= leq_subRL.
  - rewrite andbF; symmetry; apply/negbTE; rewrite negb_and -!ltnNge.
    by apply/orP; right; apply/ltn_addr.
  - by rewrite leEnat leq_subRL // leq_subLR.
- case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/ltnW/ltn_addr.
  by rewrite leEnat leq_subLR.
- case: (ltnP i m)=>/= Hi; case: (ltnP j m)=>/= Hj.
  - symmetry; apply/negbTE; rewrite negb_and -leqNgt -ltnNge.
    by apply/orP; right; apply/ltnW/ltn_addr.
  - have ->/=: (i < m + n)%N by apply/ltn_addr.
    by rewrite ltEnat /= ltn_subRL.
  - rewrite andbF; symmetry; apply/negbTE; rewrite negb_and -leqNgt -ltnNge.
    by apply/orP; right; apply/ltnW/ltn_addr.
  - by rewrite ltEnat /= ltn_subRL ltn_subLR.
- case: (ltnP i m)=>/= Hi; case: (ltnP j m)=>/= Hj.
  - symmetry; apply/negbTE; rewrite negb_and -!ltnNge.
    by apply/orP; right; apply/ltn_addr.
  - have ->/=: (i < m + n)%N by apply/ltn_addr.
    by rewrite leEnat /= leq_subRL.
  - rewrite andbF; symmetry; apply/negbTE; rewrite negb_and -!ltnNge.
    by apply/orP; right; apply/ltn_addr.
  - by rewrite leEnat ltEnat /= leq_subRL // ltn_subLR.
- case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/ltn_addr.
  by rewrite ltEnat /= ltn_subLR.
- case: (ltnP j m)=>/= Hi.
  - symmetry; apply/negbTE; rewrite -leqNgt.
    by apply/ltnW/ltn_addr.
  by rewrite ltEnat /= ltn_subRL.
case: (ltnP j m)=>/= Hi.
- symmetry; apply/negbTE; rewrite -ltnNge.
  by apply/ltn_addr.
by rewrite leEnat leq_subRL.
Qed.

(* Compute (&[::1%nat;2;3;4;5;6;7] `[1%nat,4[). *)

Section Lemmas.
Variable (A : Type).
Implicit Type (s : seq A).

(* "test" lemmas *)
Lemma slice_ouou s a b :
        &:s `]a,b[ = &:(&:s `]-oo,b[) `]a,+oo[.
Proof. by rewrite /slice /= !addn0 drop0 take_size. Qed.

Lemma slice_uouo s a b :
        &:s `]a,b+a] = &:(&:s `]a,+oo[) `]-oo,b[.
Proof.
by rewrite /slice /= !addn1 !addn0 drop0 take_size take_drop addnS.
Qed.

(* ... *)

(* some simplifying equalities on slices *)

Lemma slice_uu s : &:s `]-oo, +oo[ = s.
Proof. by rewrite /slice /= drop0 take_size. Qed.

Lemma itv_underL s (i j : itv_bound nat) :
  bnd i (size s) = 0 ->
  &:s (Interval i j) = &:s (Interval -oo j).
Proof. by move=>Hi; rewrite /slice /= Hi drop0. Qed.

Lemma itv_underR s (i j : itv_bound nat) :
  bnd j (size s) = 0 ->
  &:s (Interval i j) = [::].
Proof. by move=>Hj; rewrite /slice /= Hj take0. Qed.

Lemma itv_overL s (i j : itv_bound nat) :
  size s <= bnd i (size s) ->
  &:s (Interval i j) = [::].
Proof.
move=>Hi /=; rewrite /slice /=; apply: drop_oversize.
rewrite size_take; case: ifP=>// H.
by apply/ltnW/(leq_trans H).
Qed.

Lemma itv_overR s (i j : itv_bound nat) :
  size s <= bnd j (size s) ->
  &:s (Interval i j) = &:s (Interval i +oo).
Proof. by move=>Hj; rewrite /slice /= take_size take_oversize. Qed.

Lemma itv_minfR s (i : itv_bound nat) :
  &:s (Interval i -oo) = [::].
Proof. by rewrite /slice /= take0. Qed.

Lemma itv_pinfL s (j : itv_bound nat) :
  &:s (Interval +oo j) = [::].
Proof.
rewrite /slice /=; apply: drop_oversize.
by rewrite size_take_min; apply: geq_minr.
Qed.

Lemma itv_swapped s (i j : itv_bound nat) :
  bnd j (size s) <= bnd i (size s) ->
  &:s (Interval i j) = [::].
Proof.
move=>H; rewrite /slice; apply: drop_oversize.
rewrite size_take_min; apply/leq_trans/H.
by exact: geq_minl.
Qed.

(* splitting slice *)

Lemma slice_split s b x (i : interval nat) :
  x \in i ->
  &:s i = &:s (Interval i.1 (BSide b x)) ++ &:s (Interval (BSide b x) i.2).
Proof.
case/boolP: (size s <= bnd (BSide b x) (size s)).
- move=>H; rewrite (itv_overL _ H) cats0 (itv_overR _ H).
  case: i=>i j /= Hx; apply: itv_overR; rewrite /= in H.
  move: Hx; rewrite in_itv; case/andP=>_.
  case: j=>[[] j|[]] //= Hx; apply: (leq_trans H); case: {H}b; rewrite ?addn0 ?addn1 //;
  by apply/ltnW.
rewrite -ltNge ltEnat /= =>/ltnW/minn_idPl Hx.
rewrite in_itv; case: i=>[[[] i|[]]]; case=>[[] j|[]];
case/andP=>//=; rewrite /slice /= ?leEnat ?ltEnat ?drop0
  ?take_size ?addn0 ?addn1 /= => Hi Hj.
- (* [i, j[ *)
  have Hbj : (x + ~~ b <= j)%N.
  - case: {Hx}b=>/=; last by rewrite addn1.
    by rewrite addn0; apply/ltnW.
  rewrite -{1}(subnKC Hbj) takeD drop_cat size_take_min Hx take_drop subnK //.
  case: {Hbj Hx}b=>/=; last by rewrite addn1 ltnS Hi.
  rewrite addn0 ltn_neqAle Hi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- (* [i, j] *)
  have Hbj : (x + ~~ b <= j.+1)%N.
  - case: {Hx}b=>/=; last by rewrite addn1.
    by rewrite addn0; apply/ltnW.
  rewrite -{1}(subnKC Hbj) takeD drop_cat size_take_min Hx take_drop subnK //.
  case: {Hbj Hx}b=>/=; last by rewrite addn1 ltnS Hi.
  rewrite addn0 ltn_neqAle Hi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- (* [i, +oo[ *)
  rewrite -{1}(cat_take_drop (x + ~~b) s) drop_cat size_take_min Hx.
  case: {Hx}b=>/=; last by rewrite addn1 ltnS Hi.
  rewrite addn0 ltn_neqAle Hi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- (* ]i, j[ *)
  have Hbj : (x + ~~ b <= j)%N.
  - case: {Hx}b=>/=; last by rewrite addn1.
    by rewrite addn0; apply/ltnW.
  rewrite -{1}(subnKC Hbj) takeD drop_cat size_take_min Hx take_drop subnK //.
  case: {Hbj Hx}b=>/=; last by rewrite addn1 ltnS Hi.
  rewrite addn0 ltn_neqAle Hi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- (* ]i, j] *)
  have Hbj : (x + ~~ b <= j.+1)%N.
  - case: {Hx}b=>/=; last by rewrite addn1.
    by rewrite addn0; apply/ltnW.
  rewrite -{1}(subnKC Hbj) takeD drop_cat size_take_min Hx take_drop subnK //.
  case: {Hbj Hx}b=>/=; last by rewrite addn1 ltnS Hi.
  rewrite addn0 ltn_neqAle Hi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- (* ]i, +oo[ *)
  rewrite -{1}(cat_take_drop (x + ~~b) s) drop_cat size_take_min Hx.
  case: {Hx}b=>/=; last by rewrite addn1 ltnS Hi.
  rewrite addn0 ltn_neqAle Hi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- (* ]-oo, j[ *)
  have Hbj : (x + ~~ b <= j)%N.
  - case: {Hx}b=>/=; last by rewrite addn1.
    by rewrite addn0; apply/ltnW.
  by rewrite -{1}(subnKC Hbj) takeD take_drop subnK.
- (* ]-oo, j] *)
  have Hbj : (x + ~~ b <= j.+1)%N.
  - case: {Hx}b=>/=; last by rewrite addn1.
    by rewrite addn0; apply/ltnW.
  by rewrite -{1}(subnKC Hbj) takeD take_drop subnK.
(* ]-oo, +oo[ *)
by rewrite cat_take_drop.
Qed.

(* "test" lemmas *)
Corollary slice_uxou s i : s = &:s `]-oo, i] ++ &:s `]i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uoxu s i : s = &:s `]-oo, i[ ++ &:s `[i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uxox s a b :
            a <= b ->
            &:s `]-oo, b] = &:s `]-oo, a] ++ &:s `]a, b].
Proof. by move=>Hab; rewrite (slice_split _ false (x:=a)). Qed.

(* ... *)

(* singleton slice *)

Lemma slice_kk s k l r :
        &:s (Interval (BSide l k) (BSide r k)) =
        if l && ~~ r then oapp (cons^~ [::]) [::] (onth s k) else [::].
Proof.
rewrite /slice /=; case: (onth_sizeP s k)=>[|v] H; rewrite H /=.
- move/size_onthPn: H=>H; rewrite if_same.
  apply: drop_oversize; rewrite size_take ltnNge.
  have ->/= : (size s <= k + ~~ r)%N by apply/leq_trans/leq_addr.
  by apply/leq_trans/leq_addr.
move: (onth_size H)=>Hk; case: l; case: r=>/=;
rewrite ?addn0 ?addn1.
- by apply: drop_oversize; rewrite size_take Hk.
- rewrite -addn1 addnC -take_drop.
  rewrite (take_nth v); last by rewrite size_drop subn_gt0.
  by rewrite take0 /= nth_drop addn0 nth_onth H.
- by apply: drop_oversize; rewrite size_take Hk.
apply: drop_oversize; rewrite size_take; case: ifP=>// /negbT.
by rewrite -leqNgt.
Qed.

(* "test" lemmas *)
Corollary slice_kkxx s k :
            &:s `[k, k] = oapp (cons^~ [::]) [::] (onth s k).
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkxo s k : &:s `[k,k[ = [::].
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkox s k : &:s `]k,k] = [::].
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkoo s k : &:s `]k,k[ = [::].
Proof. by rewrite slice_kk. Qed.

(* endpoint split *)

Lemma slice_xR a x s :
        a <= BLeft x ->
        &:s (Interval a (BRight x)) =
        oapp (rcons (&:s (Interval a (BLeft x))))
                    (&:s (Interval a +oo))
             (onth s x).
Proof.
move=>Hax; rewrite (slice_split _ true (x:=x)) /=; last first.
- rewrite in_itv /= lexx andbT.
  by case: a Hax=>/=[ax av|ax]; case: ax.
rewrite slice_kk /=; case: (onth_sizeP s x)=>[|v] H;
  rewrite H /=; last by rewrite cats1.
rewrite cats0 itv_overR //= addn0.
by apply/size_onthPn.
Qed.

Lemma slice_xL b x s :
        BRight x <= b ->
        &:s (Interval (BLeft x) b) =
        oapp (cons^~ (&:s (Interval (BRight x) b)))
                     [::]
             (onth s x).
Proof.
move=>Hxb; rewrite (slice_split _ false (x:=x)) /=; last first.
- rewrite in_itv /= lexx /=.
  by case: b Hxb=>/=[bx bv|bx]; case: bx.
rewrite slice_kk /=; case: (onth_sizeP s x)=>[|v] H; rewrite H //=.
rewrite itv_overL //= addn1; apply: ltW.
by apply/size_onthPn.
Qed.

(* slice of empty list *)

Lemma slice0 i :
        &:([::] : seq A) i = [::].
Proof.
by rewrite /slice /=; case: i=>[[[] av|[]]]; case=>[[] bv|[]].
Qed.

(* slice of one-element list *)

Lemma slice1 (k : A) i :
        &:[::k] i = if 0 \in i then [::k] else [::].
Proof.
rewrite /slice in_itv /=.
case: i=>[[[] i|[]][[] j|[]]] //=;
rewrite ?drop0 ?addn0 ?addn1 ?andbF ?andbT //=.
- case: j=>[|j]/=; first by rewrite ltxx andbF.
  by rewrite andbT; case: i.
- by case: i.
- by case: i.
- by apply: drop_oversize; rewrite size_take /=; case: ifP=>//; case: j.
- by case: j.
by case: j.
Qed.

(* slice and constructors *)

Lemma slice_cat s1 s2 i :
        &:(s1++s2) i = &:s1 i ++ &:s2 (shl_itv i (size s1)).
Proof.
rewrite /slice; case: i=>[[[] i|[]][[] j|[]]] /=;
rewrite ?addn0 ?addn1 ?take0 ?drop0 ?take_size ?drop_size
  ?size_cat ?leEnat ?ltEnat //=.
- (* [i, j[ *)
  rewrite take_cat; case: ltnP=>Hj /=; first by rewrite take0 /= cats0.
  rewrite addn0 (take_oversize (n:=j)) // drop_cat.
  case: ltnP=>Hi /=; first by rewrite drop0.
  by rewrite addn0 (drop_oversize (n:=i)).
- (* [i, j] *)
  rewrite take_cat; case: ltngtP=>Hj /=.
  - by rewrite take0 /= cats0.
  - rewrite (take_oversize (n:=j.+1)); last by apply: ltnW.
    rewrite drop_cat; case: ltnP=>Hi /=; first by rewrite drop0 addn1 subSn.
    by rewrite addn0 addn1 subSn // (drop_oversize (n:=i)).
  by rewrite Hj subnn take_size take0 /= !cats0.
- (* [i, +oo[ *)
  rewrite drop_cat; case: ltnP=>Hi; first by rewrite drop0.
  by rewrite (drop_oversize (n:=i)) //= addn0.
- (* ]i, j[ *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite take0 /= cats0.
  rewrite (take_oversize (n:=j)) // drop_cat.
  case: ltngtP=>Hi /=; rewrite addn0.
  - by rewrite drop0.
  - rewrite addn1 subSn // (drop_oversize (n:=i.+1)) //.
    by apply: ltnW.
  by rewrite Hi subnn drop0 drop_size.
- (* ]i, j] *)
  rewrite take_cat; case: ltngtP=>Hj /=.
  - by rewrite take0 /= cats0.
  - rewrite (take_oversize (n:=j.+1)); last by apply: ltnW.
    rewrite drop_cat; case: ltngtP=>Hi /=.
    - by rewrite drop0 addn1 subSn.
    - rewrite !addn1 !subSn // (drop_oversize (n:=i.+1)) //.
      by apply: ltnW.
    by rewrite Hi subnn drop_size !drop0 /= addn1 subSn.
  by rewrite Hj subnn take_size take0 /= !cats0.
- (* ]i, +oo[ *)
  rewrite drop_cat; case: ltngtP=>Hi /=.
  - by rewrite drop0.
  - rewrite addn1 subSn // (drop_oversize (n:=i.+1)) //.
    by apply: ltnW.
  by rewrite Hi subnn drop_size /= drop0.
- (* ]-oo, j[ *)
  rewrite take_cat; case: ltnP=>Hj /=; first by rewrite take0 /= cats0.
  by rewrite addn0 (take_oversize (n:=j)).
- (* ]-oo, j] *)
  rewrite take_cat; case: ltngtP=>Hj /=.
  - by rewrite take0 cats0.
  - rewrite addn1 subSn // (take_oversize (n:=j.+1)) //.
    by apply: ltnW.
  by rewrite Hj subnn take_size take0.
- (* ]+oo, j[ *)
  by rewrite !drop_oversize // size_take_min ?size_cat; apply: geq_minr.
(* ]+oo, j] *)
by rewrite !drop_oversize // size_take_min ?size_cat; apply: geq_minr.
Qed.

Lemma slice_cat_piecewise s1 s2 i :
        &:(s1++s2) i = if size s1 \in i
                        then &:s1 (Interval i.1 +oo) ++ &:s2 (Interval -oo (shl_bnd i.2 (size s1)))
                        else if bnd i.2 (size s1 + size s2) <= size s1
                               then &:s1 i
                               else &:s2 (shl_itv i (size s1)).
Proof.
rewrite slice_cat; case: i=>i j /=; case: ifP.
- rewrite in_itv; case/andP=>Hi Hj.
  rewrite (itv_overR _ (j:=j)); last first.
  - case: j Hj=>[[] j|[]] //=.
    - by rewrite addn0; move/ltnW.
    by rewrite addn1 leEnat; move/(ltnW (n:=j.+1)).
  rewrite (itv_underL (i:=shl_bnd i _)) //.
  case: i Hi=>[[] i|[]] //=; last by rewrite ltEnat /=; move=>->.
  rewrite leEnat leq_eqVlt; case/orP=>[/eqP->|->] //=.
  by rewrite ltnn /= subnn.
rewrite in_itv=>/negbT; rewrite negb_and=>H.
case: ifP=>Hj.
- rewrite (itv_underR (s:=s2)); first by rewrite cats0.
  case: {H}j Hj=>[[] j|[]] //=.
  - rewrite addn0 leEnat leq_eqVlt; case/orP=>[/eqP->|->] //=.
    by rewrite ltnn /= subnn.
  - by rewrite addn1 leEnat =>->.
  by rewrite leEnat -{2}(addn0 (size s1)) leq_add2l leqn0 => /eqP.
case/orP: H; last first.
- case: j Hj=>[[] j|[]] //=.
  - by rewrite addn0 -leNgt=>->.
  by rewrite leEnat addn1 -ltnNge =>->.
case: i=>[[] i|[]] //=; last by rewrite !itv_pinfL.
- rewrite leEnat -ltnNge => Hi.
  rewrite (ltnNge i) (ltnW Hi) /= itv_overL //= addn0 leEnat.
  by apply: ltnW.
rewrite ltEnat /= -leqNgt => Hi.
rewrite ltnNge Hi /= itv_overL //= addn1 leEnat.
by apply: ltnW.
Qed.

Lemma slice_cons x s i :
        &:(x::s) i = if 0 \in i then x::&:s (shl_itv i 1) else &:s (shl_itv i 1).
Proof. by rewrite -cat1s slice_cat /= slice1; case: ifP. Qed.

Lemma slice_rcons x s i :
        &:(rcons s x) i = if size s \in i then rcons (&:s i) x else &:s i.
Proof.
rewrite -cats1 slice_cat slice1 mem_shl addn0.
by case: ifP=>_; [rewrite cats1 | rewrite cats0].
Qed.

(* mask *)

Lemma slice_mask s i :
        &:s i = let x := bnd i.1 (size s) in
               let y := bnd i.2 (size s) in
               mask (nseq x false ++
                     nseq (y-x) true) s.
Proof. by rewrite /slice /=; case: i=>i j /=; rewrite drop_take_mask. Qed.

End Lemmas.

Variant abs_itv A := AbsItv of interval A & seq A & nat.

Definition ix_bnd {A : eqType} (s : seq A) (i : itv_bound A) : itv_bound nat :=
  match i with
  | BSide  b x => BSide  b (if b then index x s else index_last x s)
  | BInfty b   => BInfty _ b
  end.

Definition ix_itv {A : eqType} (s : seq A) (i : interval A) : interval nat :=
  let: Interval l u := i in
  Interval (ix_bnd s l) (ix_bnd s u).

(*
Definition has_bnd {A : eqType} (x : A) (i : itv_bound A) : bool :=
  match i with
  | BSide  _ y => x == y
  | BInfty _   => true
  end.

Definition has_itv {A : eqType} (x : A) (i : interval A) : bool :=
  let: Interval l u := i in
  has_bnd x l || has_bnd x u.
*)

(*
Definition mem_ix {A : eqType} x (s : seq A) (i : interval A) :=
  let: Interval l u := i in
  match l with
  | BSide b lb => if b then index lb s <= index x s
                       else index_last lb s < index x s
  | BInfty b => b
  end &&
  match u with
  | BSide b ub => if ~~ b then index x s <= index_last ub s
                          else index x s < index ub s
  | BInfty b => ~~ b
  end.

Definition mem_ix_last {A : eqType} x (s : seq A) (i : interval A) :=
  let: Interval l u := i in
  match l with
  | BSide b lb => if b then index lb s <= index_last x s
                       else index_last lb s < index_last x s
  | BInfty b => b
  end &&
  match u with
  | BSide b ub => if ~~ b then index_last x s <= index_last ub s
                          else index_last x s < index ub s
  | BInfty b => ~~ b
  end.
*)
(*
Definition shl_ix_bnd {A : eqType} (s : seq A) (i : itv_bound A) n : itv_bound A :=
  match i with
  | BLeft  x => if index x s <= n then -oo else BLeft x
  | BRight x => if index_last x s < n then -oo else BRight x
  | BInfty b   => BInfty _ b
  end.

Definition shl_ix_itv {A : eqType} (s : seq A) (i : interval A) (n : nat) :=
  let: Interval l u := i in
  Interval (shl_ix_bnd s l n) (shl_ix_bnd s u n).
*)
(*
Definition eq_slice_shl {A : eqType} (s q : seq A) n (i : interval A) :=
  slice s (shl_itv (ix_itv q i) n).

Notation "&[ q ]{ n } s i" := (eq_slice_shl s q n i)
 (at level 1, i at next level, s at next level,
  format "&[ q ]{ n } s  i") : fun_scope.
*)
  (*
Notation "&={ n } s i" := (eq_slice_shl s s n i)
 (at level 1, i at next level, s at next level,
  format "&={ n } s  i") : fun_scope.
*)
(*
Definition eq_slice {A : eqType} (s q : seq A) (i : interval A) :=
  slice s (ix_itv q i).

Notation "&[ q ] s i" := (eq_slice s q i)
 (at level 1, i at next level, s at next level,
  format "&[ q ] s  i") : fun_scope.

Notation "&= s i" := (eq_slice s s i)
 (at level 1, i at next level, s at next level,
  format "&= s  i") : fun_scope.
*)
(*
Definition support_abs_itv A (i : abs_itv A) (s : seq A) : abs_itv A :=
  let: AbsItv i _ n := i in
  AbsItv i s n.
*)
Definition shl_abs_itv A (i : abs_itv A) (m : nat) : abs_itv A :=
  let: AbsItv i q n := i in
  AbsItv i q (n + m).

Definition interp {A : eqType} (i : abs_itv A) : interval nat :=
  let: AbsItv i q n := i in
  shl_itv (ix_itv q i) n.

Definition eq_slice {A : eqType} (s : seq A) (i : abs_itv A) :=
  slice s (interp i).
(*
Definition mem_ix {A : eqType} x (s : seq A) (i : abs_itv A) :=
  index x s \in interp i.

Definition mem_ix_last {A : eqType} x (s : seq A) (i : abs_itv A) :=
  index_last x s \in interp i.
*)
(*
Notation "&[ q ] s i" := (eq_slice s q i)
 (at level 1, i at next level, s at next level,
  format "&[ q ] s  i") : fun_scope.
*)

Notation "&% s i" := (eq_slice s i)
 (at level 1, i at next level, s at next level,
  format "&% s  i") : fun_scope.

Notation "&= s i" := (eq_slice s (AbsItv i s 0))
 (at level 1, i at next level, s at next level,
  format "&= s  i") : fun_scope.

Section LemmasEq.
Variable (A : eqType).
Implicit Type (s : seq A).

Lemma interp_shl (i : abs_itv A) n : shl_itv (interp i) n = interp (shl_abs_itv i n).
Proof. by case: i=>/= i s m; rewrite shl_itv_add. Qed.

(*
Lemma eqslice_shl0 q s i : &[q] s i = &[q]{0} s i.
Proof.
by rewrite /eq_slice_shl /eq_slice shl_itv0.
Qed.

(* make these definitions instead? *)
Lemma mem_ix_itv x s i : mem_ix x s i = (index x s \in ix_itv s i).
Proof.
rewrite in_itv.
by case: i=>[[[] i|[]][[] j|[]]].
Qed.

Lemma mem_ix_last_itv x s i : mem_ix_last x s i = (index_last x s \in ix_itv s i).
Proof.
rewrite in_itv.
by case: i=>[[[] i|[]][[] j|[]]].
Qed.
*)
(*
Lemma shl_ix_bnd1 x s i : shl_bnd (ix_bnd (x::s) i) 1 = ix_bnd s (shl_ix_bnd (x::s) i 1%N).
Proof.
case: i=>[[] i| []] //=; rewrite leEnat.
- rewrite addn0; case: eqP=>//= _.
  by rewrite ltnS leqn0 subn1 /=; case: eqP.
rewrite addn1 ltnS index_last_cons.
case/boolP: ((i == x) && (i \notin s))=>//= _.
by rewrite subn1.
Qed.
*)
(*
Lemma shl_ix_bnd_n s1 s2 i : shl_bnd (ix_bnd (s1 ++ s2) i) (size s1) = ix_bnd (s1 ++ s2) (shl_ix_bnd (s1 ++ s2) i (size s1)).
Proof.
case: i=>[[] i| []] //=; rewrite leEnat.
- rewrite addn0 index_cat; case/boolP: (i \in s1)=>Hi.
  - by rewrite index_size.
  rewrite -{2 6}(addn0 (size s1)) leq_add2l leqn0; case: eqP=>//=.
  rewrite index_cat (negbTE Hi).
case: ifP=>//=. case: eqP=>//= _.
  by rewrite ltnS leqn0 subn1 /=; case: eqP.
rewrite addn1 ltnS index_last_cons.
case/boolP: ((i == x) && (i \notin s))=>//= _.
by rewrite subn1.
Qed.

Lemma shl_ix_itv_n s1 s2 i : shl_itv (ix_itv (s1 ++ s2) i) (size s1) = ix_itv (s1 ++ s2) (shl_ix_itv (s1 ++ s2) i (size s1)).
Proof.
case: i=>[[] i| []] //=; rewrite leEnat.
- rewrite addn0 index_cat; case/boolP: (i \in s1)=>Hi.
  - by rewrite index_size.
  rewrite -{2 6}(addn0 (size s1)) leq_add2l leqn0; case: eqP=>//=.
  rewrite index_cat (negbTE Hi).
case: ifP=>//=. case: eqP=>//= _.
  by rewrite ltnS leqn0 subn1 /=; case: eqP.
rewrite addn1 ltnS index_last_cons.
case/boolP: ((i == x) && (i \notin s))=>//= _.
by rewrite subn1.
Qed.

Lemma shl_ix_itv1 x s i : shl_itv (ix_itv (x::s) i) 1 = ix_itv s (shl_ix_itv (x::s) i 1%N).
Proof.
by case: i=>i j /=; rewrite !shl_ix_bnd1.
Qed.
*)
(*
Lemma shl_ix_bnd s1 s2 i : shl_bnd (ix_bnd (s1 ++ s2) i) (size s1) = ix_bnd s2 i.
Proof.
case: i=>[[] i| []] //=.
- rewrite addn0 index_cat.
  case/boolP: (i \in s1)=>/= Hi.
  - rewrite leEnat index_size.

Lemma shl_ix_itv s1 s2 i : shl_itv (ix_itv (s1 ++ s2) i) (size s1) = ix_itv s2 i.
Proof.
case: i=>i j /=.
*)

(* membership *)

Lemma slice_mem (x : A) s i :
        (count_mem x s <= 1)%N ->
        (x \in &:s i) = (x \in s) && (bnd i.1 (size s) <= index x s < bnd i.2 (size s)).
Proof.
move=>H; rewrite slice_mask; case: i=>i j /=.
rewrite (in_mask_count _ H); case Hx: (x \in s)=>//=.
rewrite ltEnat leEnat /= nth_cat size_nseq; case: ltngtP=>Hi /=.
- by rewrite nth_nseq Hi.
- rewrite nth_nseq if_triv; case: (ltnP (index _ _))=>Hj.
  - by apply: ltn_sub2r=>//; apply/ltn_trans/Hj.
  - by apply/negbTE; rewrite -leqNgt; apply/leq_sub2r.
rewrite -Hi subnn nth0; case: ltnP.
- by rewrite -subn_gt0; set q := bnd j (size s) - index x s; case: q.
by rewrite -subn_eq0=>/eqP->.
Qed.

Lemma eqsl_underL s (i j : itv_bound A) :
  bnd (ix_bnd s i) (size s) = 0 ->
  &=s (Interval i j) = &=s (Interval -oo j).
Proof. by move=>H; apply: itv_underL; rewrite shl_bnd0. Qed.

Lemma eqsl_underR s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) = 0 ->
  &=s (Interval i j) = [::].
Proof. by move=>H; apply: itv_underR; rewrite shl_bnd0. Qed.

Lemma eqsl_overL s (i j : itv_bound A) :
  size s <= bnd (ix_bnd s i) (size s) ->
  &=s (Interval i j) = [::].
Proof. by move=>H; apply: itv_overL; rewrite shl_bnd0. Qed.

Lemma eqsl_overR s (i j : itv_bound A) :
  size s <= bnd (ix_bnd s j) (size s) ->
  &=s (Interval i j) = &=s (Interval i +oo).
Proof. by move=>Hj; apply: itv_overR; rewrite shl_bnd0. Qed.

Corollary eqsl_notinL y b t s :
  t \notin s ->
  &=s (Interval (BSide b t) y) = [::].
Proof.
move=>T; apply: eqsl_overL=>/=.
rewrite (memNindex T) (memNindex_last T) if_same.
by apply: leq_addr.
Qed.

Corollary eqsl_notinR x b t s :
  t \notin s ->
  &=s (Interval x (BSide b t)) = &=s (Interval x +oo).
Proof.
move=>T; apply: eqsl_overR=>/=.
rewrite (memNindex T) (memNindex_last T) if_same.
by apply: leq_addr.
Qed.

Lemma eqsl_minfR s (i : itv_bound A) :
  &=s (Interval i -oo) = [::].
Proof. by rewrite /eq_slice /=; apply: itv_minfR. Qed.

Lemma eqsl_pinfL s (j : itv_bound A) :
  &=s (Interval +oo j) = [::].
Proof. by rewrite /eq_slice /=; apply: itv_pinfL. Qed.

Lemma eqsliceRO_notin s x a :
        x \notin &=s (Interval a (BLeft x)).
Proof.
rewrite /eq_slice /slice /= addn0 shl_bnd0 subn0.
apply/negP=>/mem_drop; apply/negP.
by apply: mem_take_index.
Qed.

Lemma eqsliceLO_notin s x b :
        x \notin &=s (Interval (BRight x) b).
Proof.
rewrite /eq_slice /slice /= addn1 shl_bnd0 subn0.
by move: (mem_drop_index_last x s); apply/contra/prefix_drop_sub/prefix_take.
Qed.

Lemma eqsl_kk s l r k :
        (count_mem k s <= 1)%N ->
        &=s (Interval (BSide l k) (BSide r k)) =
        if [&& l, ~~ r & k \in s] then [:: k] else [::].
Proof.
move=>H; rewrite /eq_slice /= !subn0 index_last_count // !if_same slice_kk.
case: ifP; last by rewrite andbA =>->.
case/andP=>->->/=; case: ifP.
- by move/onth_index=>->.
by move/negbT/memNindex=>->; rewrite onth_sizeN.
Qed.

(* test lemmas *)

Lemma eqsl_uxR t s :
        &=s `]-oo, t] = &=s `]-oo, t[ ++ &=s `[t, t].
Proof.
rewrite /eq_slice /= !subn0 (@slice_split _ _ true (index t s)) //.
rewrite in_itv /=; apply: index_leq_last.
Qed.

Lemma eqsl_xuL t s :
        &=s `[t, +oo[ = &=s `[t, t] ++ &=s `]t, +oo[.
Proof.
rewrite /eq_slice /= !subn0 (@slice_split _ _ false (index_last t s)) //.
by rewrite in_itv /= andbT; apply: index_leq_last.
Qed.

(* TODO tweak index/last? *)

Lemma eqsl_xxL t1 t2 s :
        index t1 s <= index_last t2 s ->
        count_mem t1 s = 1%N ->
        &=s `[t1, t2] = t1 :: &=s `]t1, t2].
Proof.
move=>I H.
have H1: index_last t1 s = index t1 s.
- by rewrite index_last_count // H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ false (index_last t1 s)) H1 /=.
- by rewrite slice_kk /= onth_index // -has_pred1 has_count H.
by rewrite in_itv /= lexx.
Qed.

Lemma eqsl_xxR t1 t2 s :
        index t1 s <= index t2 s ->
        count_mem t2 s = 1%N ->
        &=s `[t1, t2] = rcons (&=s `[t1, t2[) t2.
Proof.
move=>I H.
have H2: index_last t2 s = index t2 s.
- by rewrite index_last_count // H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ true (index_last t2 s)) H2 /=.
- rewrite slice_kk /= onth_index /=; first by rewrite cats1.
  by rewrite -has_pred1 has_count H.
by rewrite in_itv /= lexx andbT.
Qed.

Lemma eqsl_xoL t1 t2 s :
        index t1 s < index t2 s ->
        count_mem t1 s = 1%N ->
        &=s `[t1, t2[  = t1 :: &=s `]t1, t2[.
Proof.
move=>I H.
have H1: index_last t1 s = index t1 s.
- by rewrite index_last_count // H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ false (index_last t1 s)) H1 /=.
- by rewrite slice_kk /= onth_index // -has_pred1 has_count H.
by rewrite in_itv /= lexx.
Qed.

Lemma eqsl_oxR t1 t2 s :
        index_last t1 s < index t2 s ->
        count_mem t2 s = 1%N ->
        &=s `]t1, t2] = rcons (&=s `]t1, t2[) t2.
Proof.
move=>I H.
have H2: index_last t2 s = index t2 s.
- by rewrite index_last_count // H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ true (index_last t2 s)) H2 /=.
- rewrite slice_kk /= onth_index /=; first by rewrite cats1.
  by rewrite -has_pred1 has_count H.
by rewrite in_itv /= lexx andbT.
Qed.

(* eqslice of one-element list *)

Lemma ixslice1 (k : A) i :
        &%[::k] i = if 0 \in interp i then [::k] else [::].
Proof. by rewrite /eq_slice; case: i=>i q b /=; rewrite slice1. Qed.

Corollary eqslice1uR (k : A) b t :
            &=[::k] (Interval -oo (BSide b t)) = if ~~ b || (t!=k) then [::k] else [::].
Proof.
rewrite ixslice1 /= index_last_cons index_last0 /= andbT eq_sym.
by case: b=>//=; case: eqP.
Qed.

Corollary eqslice1uL (k : A) b t :
            &=[::k] (Interval (BSide b t) +oo) = if b && (t==k) then [::k] else [::].
Proof.
rewrite ixslice1 /= index_last_cons index_last0 /= !andbT eq_sym.
by case: b=>//=; case: eqP.
Qed.

(* ... *)

Lemma ixslice_cat s1 s2 i :
        &%(s1 ++ s2) i =
             &% s1 i ++ &%s2 (shl_abs_itv i (size s1)).
Proof.
rewrite /eq_slice; case:i => i q n /=.
by rewrite slice_cat shl_itv_add.
Qed.
(*
Lemma eqslice_cat_shl s n s1 s2 i :
        &[s]{n} (s1 ++ s2) i =
             &[s]{n} s1 i ++ &[s]{n + size s1} s2 i.
Proof. by rewrite /eq_slice_shl slice_cat shl_itv_add. Qed.

Lemma eqslice_cat s1 s2 i :
        &=(s1 ++ s2) i =
             &[s1 ++ s2] s1 i ++ &[s1 ++ s2]{size s1} s2 i.
Proof. by rewrite eqslice_shl0 eqslice_cat_shl add0n -eqslice_shl0. Qed.
*)
(* cons lemmas *)
(* TODO unify *)

Lemma ixslice_cons x s i :
        &%(x::s) i = if 0 \in interp i
                       then x::&%s (shl_abs_itv i 1)
                       else    &%s (shl_abs_itv i 1).
Proof. by rewrite /eq_slice /= slice_cons /= interp_shl. Qed.

(* cons/infty normalization *)

Lemma ix_ur_cons k b t s :
        &%s (AbsItv (Interval -oo (BSide b t)) (k::s) 1) =
        if (t != k) || (~~ b && (t \in s)) then &=s (Interval -oo (BSide b t)) else [::].
Proof.
rewrite /eq_slice /= subn0 index_last_cons eq_sym.
case: eqP=>/= ?; last by rewrite -fun_if /= subn1.
case/boolP: (t \in s)=> H /=; last first.
- by rewrite andbF if_same /= itv_minfR.
by rewrite andbT; case: b=>/=; [rewrite itv_minfR | rewrite subn1].
Qed.

Lemma ix_ul_cons k b t s :
        &%s (AbsItv (Interval (BSide b t) +oo) (k::s) 1) =
        if (t != k) || (~~ b && (t \in s)) then &=s (Interval (BSide b t) +oo) else s.
Proof.
rewrite /eq_slice /= subn0 index_last_cons eq_sym.
case: eqP=>/= ?; last by rewrite -fun_if /= subn1.
case/boolP: (t \in s)=> H /=; last first.
- by rewrite andbF if_same /= slice_uu.
by rewrite andbT; case: b=>/=; [rewrite slice_uu | rewrite subn1].
Qed.

Corollary ix_ux_consE k t s :
            &=(k::s) `]-oo,t] =
            k :: if (t != k) || (t \in s) then &=s `]-oo,t] else [::].
Proof. by rewrite ixslice_cons /= add0n ix_ur_cons. Qed.

Corollary ix_uo_consE k t s :
            &=(k::s) `]-oo,t[ =
            if t != k then k :: &=s `]-oo,t[ else [::].
Proof. by rewrite ixslice_cons /= ix_ur_cons eq_sym; case: eqP. Qed.

Corollary ix_xu_consE k t s :
            &=(k::s) `[t,+oo[ =
            if t != k then &=s `[t,+oo[ else k::s.
Proof. by rewrite ixslice_cons /= subn0 /= ix_ul_cons eq_sym; case: eqP. Qed.

Corollary ix_ou_consE k t s :
            &=(k::s) `]t,+oo[ =
            if (t != k) || (t \in s) then &=s `]t,+oo[ else s.
Proof. by rewrite ixslice_cons /= ix_ul_cons. Qed.

Corollary ix_ux_consLX t s :
            &=(t::s) `]-oo,t] = t :: if t \in s then &=s `]-oo,t] else [::].
Proof. by rewrite ix_ux_consE eqxx. Qed.

Corollary ix_uo_consL t s :
            &=(t::s) `]-oo,t[ = [::].
Proof. by rewrite ix_uo_consE eqxx. Qed.

Corollary ix_xu_consL t s :
            &=(t::s) `[t,+oo[ = t::s.
Proof. by rewrite ix_xu_consE eqxx. Qed.

Corollary ix_ou_consLX t s :
            &=(t::s) `]t,+oo[ = if t \in s then &=s `]t,+oo[ else s.
Proof. by rewrite ix_ou_consE eqxx. Qed.

(* rcons lemmas *)
(* TODO unify *)

Lemma ixslice_rcons x s i :
        &%(rcons s x) i =
        if size s \in interp i then rcons (&%s i) x
                               else        &%s i.
Proof. by rewrite /eq_slice slice_rcons. Qed.

(* rcons/infty normalization *)

Lemma ix_ur_rcons k b t s :
        &%s (AbsItv (Interval -oo (BSide b t)) (rcons s k) 0) =
        if (t \in s) && (~~ b ==> (t != k)) then &=s (Interval -oo (BSide b t)) else s.
Proof.
rewrite /eq_slice /= !subn0 index_rcons index_last_rcons.
case/boolP: (t \in s)=> H/=; last first.
- rewrite if_same itv_overR /=; first by apply: slice_uu.
  by rewrite leEnat -addn1; case: eqP=>/= _; rewrite -?addnA; apply: leq_addr.
case: eqP=>/= _; last by rewrite implybT.
rewrite implybF negbK /=; case: b=>//=.
rewrite itv_overR /=; first by apply: slice_uu.
by rewrite addn1.
Qed.

Lemma ix_ul_rcons k b t s :
        &%s (AbsItv (Interval (BSide b t) +oo) (rcons s k) 0) =
        if (t \in s) && (~~ b ==> (t != k)) then &=s (Interval (BSide b t) +oo) else [::].
Proof.
rewrite /eq_slice /= !subn0 index_rcons index_last_rcons.
case/boolP: (t \in s)=> H/=; last first.
- rewrite if_same itv_overL //= leEnat -addn1.
  by case: eqP=>/= _; rewrite -?addnA; apply: leq_addr.
case: eqP=>/= _; last by rewrite implybT.
rewrite implybF negbK /=; case: b=>//=.
by rewrite itv_overL //= addn1.
Qed.

Lemma ix_ux_rconsE k t s :
        &= (rcons s k) `]-oo,t] =
        if (t != k) && (t \in s) then &=s `]-oo,t] else rcons s k.
Proof.
rewrite ixslice_rcons /= subn0 !index_last_rcons
  ix_ur_rcons in_itv /= leEnat.
case: eqP=>/= _; first by rewrite andbF leqnn.
rewrite andbT; case/boolP: (t \in s)=> H/=; last by rewrite leqnSn.
by rewrite leqNgt index_last_mem H.
Qed.

Lemma ix_uo_rconsE k t s :
        &= (rcons s k) `]-oo,t[ =
        if (t == k) || (t \in s) then &=s `]-oo,t[ else rcons s k.
Proof.
rewrite ixslice_rcons /= subn0 index_rcons
  ix_ur_rcons in_itv /= ltEnat /=.
case/boolP: (t \in s)=> H/=; first by rewrite ltnNge index_size /= orbT.
case: eqP=>/= _; last by rewrite ltnS leqnn.
rewrite ltnn eqsl_overR /=; first by rewrite /eq_slice slice_uu.
by rewrite addn0 (memNindex H).
Qed.

Lemma ix_xu_rconsE k t s :
        &= (rcons s k) `[t,+oo[ =
        if (t == k) || (t \in s) then rcons (&= s `[t,+oo[) k else [::].
Proof.
rewrite ixslice_rcons /= subn0 index_rcons
  ix_ul_rcons in_itv /= andbT leEnat.
case/boolP: (t \in s)=> H/=; first by rewrite orbT index_size.
rewrite orbF; case: eqP=>/= _; last by rewrite ltnn.
by rewrite leqnn eqsl_overL //= addn0 leEnat (memNindex H).
Qed.

Lemma ix_ou_rconsE k t s :
        &= (rcons s k) `]t,+oo[ =
        if (t != k) && (t \in s) then rcons (&= s `]t,+oo[) k else [::].
Proof.
rewrite ixslice_rcons /= subn0 index_last_rcons
  ix_ul_rcons in_itv /= andbT ltEnat /=.
case: eqP=>/= _; first by rewrite andbF ltnn.
rewrite andbT; case/boolP: (t \in s)=> H/=; last by rewrite ltnNge leqnSn.
by rewrite index_last_mem H.
Qed.

(* intervals and filter *)

(* TODO unify *)
Lemma eqsl_filterL (p : pred A) b (y : A) s :
        (y \notin s) || p y ->
        &= (filter p s) (Interval -oo (BSide b y)) = filter p (&= s (Interval -oo (BSide b y))).
Proof.
case/orP=>Ht.
- rewrite !eqsl_notinR //=; first by rewrite /eq_slice !slice_uu.
  by rewrite mem_filter negb_and Ht orbT.
rewrite /eq_slice /slice /= !drop0 !subn0.
case: b=>/=.
- rewrite !addn0; elim: s=>//=h s IH.
  case/boolP: (h == y)=>[{h}/eqP->|H] /=.
  - by rewrite Ht /= eqxx.
  case: ifP=>//= Hp.
  by rewrite (negbTE H) /= IH.
rewrite !addn1; elim: s=>//=h s IH; rewrite index_last_cons.
case/boolP: (y == h)=>[{h}/eqP<-|H] /=.
- rewrite Ht /= index_last_cons eqxx /= mem_filter Ht /=.
  case: ifP; first by rewrite !take0.
  by rewrite IH.
case: ifP=>//= Hp.
by rewrite index_last_cons (negbTE H) /= IH.
Qed.

Lemma eqsl_filterR (p : pred A) b (x : A) s :
        (x \notin s) || p x ->
        &= (filter p s) (Interval (BSide b x) +oo) = filter p (&= s (Interval (BSide b x) +oo)).
Proof.
case/orP=>Ht.
- by rewrite !eqsl_notinL //= mem_filter negb_and Ht orbT.
rewrite /eq_slice /slice /= !take_size !subn0.
case: b=>/=.
- rewrite !addn0; elim: s=>//=h s IH.
  case/boolP: (h == x)=>[{h}/eqP->|H] /=.
  - by rewrite Ht /= eqxx.
  case: ifP=>//= Hp.
  by rewrite (negbTE H) /= IH.
rewrite !addn1; elim: s=>//=h s IH; rewrite index_last_cons.
case/boolP: (x == h)=>[{h}/eqP<-|H] /=.
- rewrite Ht /= index_last_cons eqxx /= mem_filter Ht /=.
  case: ifP; first by rewrite !drop0.
  by rewrite IH.
case: ifP=>//= Hp.
by rewrite index_last_cons (negbTE H) /= IH.
Qed.

End LemmasEq.