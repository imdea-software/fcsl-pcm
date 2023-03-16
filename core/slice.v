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

Lemma mem_drop_indexlast {A : eqType} x (s : seq A) :
        x \notin drop (indexlast x s).+1 s.
Proof.
elim: s=>//=h s; rewrite indexlast_cons.
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

Lemma shl_bnd0 i : shl_bnd i 0%N = i.
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

Lemma shl_itv0 i : shl_itv i 0%N = i.
Proof. by case: i=>i j /=; rewrite !shl_bnd0. Qed.

Lemma shl_itv_add i n m : shl_itv (shl_itv i n) m = shl_itv i (n+m).
Proof. by case: i=>i j /=; rewrite !shl_bnd_add. Qed.

Lemma mem_shl n m i :
  (n \in shl_itv i m) = (m + n \in i).
Proof.
rewrite !in_itv; case: i=>i j /=.
case: i=>[l i|[]]; case: j=>[r j|[]] //=;
rewrite ?andbF ?andbT //.
- case: (ltnP j m)=>/= Hj.
  - rewrite andbF; symmetry; apply/negbTE; rewrite negb_and lteifNE negbK -lteifNE.
    by apply/orP; right; apply/lteifS/ltn_addr.
  have ->: (n < j - m ?<= if ~~ r) = (m + n < j ?<= if ~~ r).
  - case: r=>/=; first by rewrite ltEnat /= ltn_subRL.
    by rewrite leEnat leq_subRL.
  case: (m + n < j ?<= if ~~ r); rewrite ?andbF // !andbT.
  case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/lteifS/ltn_addr.
  case: l=>/=; last by rewrite ltEnat /= ltn_subLR.
  by rewrite leEnat leq_subLR.
- case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/lteifS/ltn_addr.
  case: l=>/=; last by rewrite ltEnat /= ltn_subLR.
  by rewrite leEnat leq_subLR.
case: (ltnP j m)=>/= Hj.
- symmetry; apply/negbTE; rewrite lteifNE negbK.
  by apply/lteifS/ltn_addr.
case: r=>/=; first by rewrite ltEnat /= ltn_subRL.
by rewrite leEnat leq_subRL.
Qed.

(* generalize to orderType? *)
Lemma mem_itv_inf (n : nat) : n \in `]-oo,+oo[.
Proof. by rewrite in_itv. Qed.

(* Compute (&[::1%nat;2;3;4;5;6;7] `[1%nat,4[). *)

Section Lemmas.
Variable (A : Type).
Implicit Type (s : seq A).

Lemma slice_decompose s l r x y :
        &:s (Interval (BSide l x) (BSide r y)) =
        &:(&:s (Interval -oo (BSide r y))) (Interval (BSide l x) +oo).
Proof. by rewrite /slice /= drop0 take_size. Qed.

(* "test" lemmas *)
Lemma slice_ouou s a b :
        &:s `]a,b[ = &:(&:s `]-oo,b[) `]a,+oo[.
Proof. by rewrite slice_decompose. Qed.

(* TODO generalize? *)
Lemma slice_uouo s a b :
        &:s `]a,b+a] = &:(&:s `]a,+oo[) `]-oo,b[.
Proof.
by rewrite /slice /= !addn1 !addn0 drop0 take_size take_drop addnS.
Qed.

(* ... *)

(* some simplifying equalities on slices *)

Lemma slice_0L s y : &:s (Interval -oo y) = &:s (Interval (BLeft 0%N) y).
Proof. by rewrite /slice /= addn0. Qed.

Lemma slice_FR s x : &:s (Interval x +oo) = &:s (Interval x (BLeft (size s))).
Proof. by rewrite /slice /= addn0. Qed.

Lemma slice_uu s : &:s `]-oo, +oo[ = s.
Proof. by rewrite /slice /= drop0 take_size. Qed.

Lemma itv_underL s (i j : itv_bound nat) :
        bnd i (size s) = 0%N ->
        &:s (Interval i j) = &:s (Interval -oo j).
Proof. by move=>Hi; rewrite /slice /= Hi drop0. Qed.

Lemma itv_underR s (i j : itv_bound nat) :
        bnd j (size s) = 0%N ->
        &:s (Interval i j) = [::].
Proof. by move=>Hj; rewrite /slice /= Hj take0. Qed.

Corollary itv_under0R s (i : itv_bound nat) :
            &:s (Interval i (BLeft 0%N)) = [::].
Proof. by apply: itv_underR. Qed.

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

(* TODO unify these two? *)
Lemma itv_swapped_bnd s (i j : itv_bound nat) :
        j <= i ->
        &:s (Interval i j) = [::].
Proof.
move=>H; rewrite /slice; apply: drop_oversize.
move: H; case: i=>[ib ix|[]]; case: j=>[jb jx|[]] //=;
rewrite ?bnd_simp ?take_size ?take0 ?drop_size //= size_take_min.
- rewrite leBSide; case: ib=>/=; case: jb=>/=; rewrite ?addn0 ?addn1=>Hji.
  - apply/leq_trans/Hji; exact: geq_minl.
  - apply/leq_trans/Hji; exact: geq_minl.
  - apply: leq_trans; first by exact: geq_minl.
    by apply: ltnW.
  by apply: leq_trans; first by exact: geq_minl.
by move=>_; exact: geq_minr.
Qed.

Lemma itv_swapped s (i j : itv_bound nat) :
        bnd j (size s) <= bnd i (size s) ->
        &:s (Interval i j) = [::].
Proof.
move=>H; rewrite /slice; apply: drop_oversize.
rewrite size_take_min; apply/leq_trans/H.
by exact: geq_minl.
Qed.

Corollary slice_usize s : s = &:s `]-oo, size s[.
Proof. by rewrite itv_overR /=; [rewrite slice_uu | rewrite addn0]. Qed.

(* slice size *)

Lemma slice_size s (i : interval nat) :
  size (&:s i) = minn (bnd i.2 (size s)) (size s) - bnd i.1 (size s).
Proof.
rewrite /slice; case: i=>[[l i|[]][r j|[]]] //=; rewrite ?take0 ?drop0 ?take_size ?drop_size ?minnn ?min0n ?subn0 //=.
- by rewrite size_drop size_take_min.
- by rewrite size_drop.
- by rewrite size_take_min.
- by rewrite size_drop size_take_min.
by rewrite subnn.
Qed.

(* splitting slice *)

Lemma slice_split_bnd s (i : interval nat) x :
  i.1 <= x <= i.2 ->
  &:s i = &:s (Interval i.1 x) ++ &:s (Interval x i.2).
Proof.
case: i=>i1 i2 /=.
case: x=>[b x|[]]; rewrite ?bnd_simp /=; first last.
- by move/eqP=>->; rewrite itv_pinfL cats0.
- by rewrite andbT =>/eqP->; rewrite itv_minfR.
case/boolP: (size s <= bnd (BSide b x) (size s)).
- move=>H Hx; rewrite (itv_overL _ H) cats0 (itv_overR _ H).
  apply: itv_overR; rewrite /= in H.
  case/andP: Hx=>_.
  case: i2=>[[] i2|[]] //= Hx; apply: (leq_trans H); case: {H}b Hx; rewrite bnd_simp ?addn0 ?addn1 //.
  by move=>Hx; apply/ltnW.
rewrite -ltNge ltEnat /= =>/ltnW/minn_idPl Hx.
case: i1=>[l i|[]]; case: i2=>[r j|[]] //=;
rewrite ?bnd_simp ?andbF ?andbT // ?lteBSide /slice /= ?drop0 ?take_size.
- case/andP=>Hi Hj.
  have Hxj : (x + ~~ b <= j + ~~r)%N.
  - case: r Hj=>/=; rewrite ?leEnat ?ltEnat; case: {Hx Hi}b=>/=;
    rewrite ?addn0 ?addn1 // => Hj;
    by apply: ltnW.
  have Hxi : (i + ~~ l <= x + ~~ b)%N.
  - case: l Hi=>/=; rewrite ?implybT ?implybF /= ?addn0 ?addn1 /= => Hi.
    - by apply/(leq_trans Hi)/leq_addr.
    by case: {Hx Hj Hxj}b Hi=>/=; rewrite ?leEnat ?ltEnat /= ?addn0 ?addn1.
  rewrite -{1}(subnKC Hxj) takeD drop_cat size_take_min Hx take_drop subnK //.
  rewrite ltn_neqAle Hxi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- move=>Hi; rewrite -{1}(cat_take_drop (x + ~~ b) s) drop_cat size_take_min Hx.
  have Hxi : (i + ~~ l <= x + ~~ b)%N.
  - case: l Hi=>/=; rewrite ?implybT ?implybF /= ?addn0 ?addn1 /= => Hi.
    - by apply/(leq_trans Hi)/leq_addr.
    by case: {Hx}b Hi=>/=; rewrite ?leEnat ?ltEnat /= ?addn0 ?addn1.
  rewrite ltn_neqAle Hxi andbT; case: eqP=>//= ->.
  by rewrite subnn drop0 drop_take_id.
- move=>Hj.
  have Hbj : (x + ~~ b <= j + ~~ r)%N.
  - case: r Hj=>/=; rewrite ?leEnat ?ltEnat; case: {Hx}b=>/=;
    rewrite ?addn0 ?addn1 // => Hx;
    by apply: ltnW.
  by rewrite -{1}(subnKC Hbj) takeD take_drop subnK.
by move=>_; rewrite cat_take_drop.
Qed.

Corollary slice_split s b x (i : interval nat) :
  x \in i ->
  &:s i = &:s (Interval i.1 (BSide b x)) ++ &:s (Interval (BSide b x) i.2).
Proof.
move=>Hx; apply: slice_split_bnd.
case: i Hx=>[[l i|[]][r j|[]]] //=;
rewrite in_itv /= ?andbT ?andbF // ?leBSide; case: b=>/=;
rewrite ?implybF ?implybT //=.
- by case/andP=>->/= /lteifW.
- by case/andP=>/lteifW->.
- by move/lteifW.
by move/lteifW.
Qed.

(* slice extrusion *)

Lemma slice_extrude s (i : interval nat) :
        i.1 < i.2 ->
        s = &:s (Interval -oo i.1) ++ &:s i ++ &:s (Interval i.2 +oo).
Proof.
case: i=>[[[] i|[]][[] j|[]]] //=; rewrite bnd_simp=>H;
  rewrite ?itv_minfR ?itv_pinfL /= ?cats0.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)) //=
    (slice_split _ true (x:=j) (i:=`[i, +oo[)) //= in_itv /= andbT; apply/ltnW.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)) //=
    (slice_split _ false (x:=j) (i:=`[i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)).
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)) //=
    (slice_split _ true (x:=j) (i:=`]i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)) //=
    (slice_split _ false (x:=j) (i:=`]i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)).
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=j)).
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=j)).
by rewrite slice_uu.
Qed.

(* "test" lemmas *)
Corollary slice_uxou s i : s = &:s `]-oo, i] ++ &:s `]i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uoxu s i : s = &:s `]-oo, i[ ++ &:s `[i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uxxo s a b :
            a <= b ->
            &:s `]-oo, b] = &:s `]-oo, a] ++ &:s `]a, b].
Proof. by move=>Hab; rewrite (slice_split _ false (x:=a)). Qed.

Corollary slice_uxox s a b :
            a <= b ->
            &:s `]-oo, b] = &:s `]-oo, a[ ++ &:s `[a, b].
Proof. by move=>Hab; rewrite (slice_split _ true (x:=a)). Qed.

Corollary slice_uoox (s : seq A) a b :
            a < b ->
            &:s `]-oo, b[ = &:s `]-oo, a[ ++ &:s `[a, b[.
Proof. by move=>Hab; rewrite (slice_split _ true (x:=a)). Qed.

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

(* endpoint +1 *)

Lemma slice_oSL x a s :
        &:s (Interval (BRight x) a) = &:s (Interval (BLeft x.+1) a).
Proof.
case/boolP: (x.+1 \in Interval (BRight x) a)=>[H|].
- rewrite (slice_split _ true (x:=x.+1)) //=.
  suff ->: &:s `]x, x.+1[ = [::] by rewrite cat0s.
  by rewrite /slice /= addn0 addn1 drop_take_id.
rewrite in_itv /= negb_and ltEnat /= ltnS leqnn /=.
case: a=>[[] a|[]] //=.
- by rewrite -leNgt leEnat => H; rewrite !itv_swapped //= !addn0 ?addn1 leEnat.
- by rewrite -ltNge ltEnat /= => H; rewrite !itv_swapped //= !addn1 ?addn0 leEnat ltnS.
by move=>_; rewrite !itv_minfR.
Qed.

Lemma slice_oSR a x s :
        &:s (Interval a (BLeft x.+1)) = &:s (Interval a (BRight x)).
Proof.
case/boolP: (x \in Interval a (BLeft x.+1))=>[H|].
- rewrite (slice_split _ false (x:=x)) //=.
  suff ->: &:s `]x, x.+1[ = [::] by rewrite cats0.
  by rewrite /slice /= addn0 addn1 drop_take_id.
rewrite in_itv /= negb_and ltEnat /= ltnS leqnn /= orbF.
case: a=>[[] a|[]] //=.
- by rewrite -ltNge ltEnat /= => H; rewrite !itv_swapped //= !addn0 ?addn1 leEnat.
- by rewrite -leNgt leEnat => H; rewrite !itv_swapped //= !addn1 ?addn0 leEnat ltnS.
by move=>_; rewrite !itv_pinfL.
Qed.

(* endpoint -1 *)

Corollary slice_oPR a x s :
        0 < x ->
        &:s (Interval a (BRight x.-1)) = &:s (Interval a (BLeft x)).
Proof. by move=>Hx; rewrite -{2}(prednK Hx) slice_oSR. Qed.

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
        &:[::k] i = if 0%N \in i then [::k] else [::].
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
rewrite /slice; case: i=>[[l i|[]][r j|[]]] /=;
rewrite ?take0 ?drop0 ?take_size ?drop_size // ?size_cat.
- rewrite take_cat; case: ltnP=>Hj.
  - have ->/=: (j < size s1)%N by apply/leq_ltn_trans/Hj/leq_addr.
    by rewrite take0 /= cats0.
  rewrite (take_oversize (s:=s1)) //.
  move: Hj; rewrite leq_eqVlt; case/orP=>[/eqP Ej|Hj].
  - rewrite -Ej subnn take0 cats0 /=.
    case: r Ej=>/=.
    - by rewrite addn0=>->; rewrite ltnn subnn /= take0 /= cats0.
    by rewrite addn1=>->; rewrite !ltnS leqnn /= take0 /= cats0.
  rewrite (ltnNge j); have H1: (size s1 <= j)%N.
  - by case: r Hj=>/=; rewrite ?addn1 // addn0 => /ltnW.
  rewrite H1 drop_cat; case: ltnP=>Hi /=.
  - have ->/=: (i < size s1)%N by apply/leq_ltn_trans/Hi/leq_addr.
    by rewrite drop0 addnBAC.
  rewrite (drop_oversize (s:=s1)) //=.
  move: Hi; rewrite leq_eqVlt; case/orP=>[/eqP Ei|Hi].
  - rewrite -Ei subnn drop0 /=.
    case: l Ei=>/=.
    - by rewrite addn0=><-; rewrite ltnn subnn /= drop0 addnBAC.
    by rewrite addn1=><-; rewrite leqnn /= drop0 addnBAC.
  rewrite (ltnNge i); have H2: (size s1 <= i)%N.
  - by case: l Hi=>/=; rewrite ?addn1 // addn0 => /ltnW.
  by rewrite H2 /= !addnBAC.
- rewrite drop_cat; case: ltnP=>Hi /=.
  - have ->/=: (i < size s1)%N by apply/leq_ltn_trans/Hi/leq_addr.
    by rewrite drop0.
  rewrite (drop_oversize (s:=s1)) //=.
  move: Hi; rewrite leq_eqVlt; case/orP=>[/eqP Ei|Hi].
  - rewrite -Ei subnn drop0 /=.
    case: l Ei=>/=.
    - by rewrite addn0=><-; rewrite ltnn subnn /= drop0.
    by rewrite addn1=><-; rewrite leqnn /= drop0.
  rewrite (ltnNge i); have H2: (size s1 <= i)%N.
  - by case: l Hi=>/=; rewrite ?addn1 // addn0 => /ltnW.
  by rewrite H2 /= addnBAC.
- rewrite take_cat; case: ltnP=>Hj.
  - have ->/=: (j < size s1)%N by apply/leq_ltn_trans/Hj/leq_addr.
    by rewrite take0 /= cats0.
  rewrite (take_oversize (s:=s1)) //.
  move: Hj; rewrite leq_eqVlt; case/orP=>[/eqP Ej|Hj].
  - rewrite -Ej subnn take0 cats0 /=.
    case: r Ej=>/=.
    - by rewrite addn0=>->; rewrite ltnn subnn /= take0 /= cats0.
    by rewrite addn1=>->; rewrite !ltnS leqnn /= take0 /= cats0.
  rewrite (ltnNge j); have H1: (size s1 <= j)%N.
  - by case: r Hj=>/=; rewrite ?addn1 // addn0 => /ltnW.
  by rewrite H1 /= addnBAC.
by rewrite !drop_oversize //= size_take_min ?size_cat; apply: geq_minr.
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
        &:(x::s) i = if 0%N \in i then x::&:s (shl_itv i 1) else &:s (shl_itv i 1).
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

(* count *)

Lemma slice_count p s i :
        count p (&:s i) =
        count (fun j => j \in i) (findall p s).
Proof.
elim: s i=>/= [|x s IH] i.
- by rewrite slice0.
rewrite findall_cons slice_cons.
case/boolP: (p x)=>/= Hpx; case/boolP: (0 \in i)=>I0 /=.
- rewrite Hpx !add1n; congr S.
  rewrite IH count_map; apply: eq_count=>z /=.
  by rewrite mem_shl add1n.
- rewrite IH /= count_map; apply: eq_count=>z /=.
  by rewrite mem_shl add1n.
- rewrite (negbTE Hpx) /= IH /= count_map; apply: eq_count=>z /=.
  by rewrite mem_shl add1n.
rewrite IH /= count_map; apply: eq_count=>z /=.
by rewrite mem_shl add1n.
Qed.

(* has *)

Corollary slice_has p s i :
            has p (&:s i) =
            has (fun j => j \in i) (findall p s).
Proof. by rewrite !has_count slice_count. Qed.

End Lemmas.

(* map *)

Lemma slice_map {A B} (f : A -> B) i s :
  [seq f x | x <- &:s i] = &: [seq f x | x <- s] i.
Proof. by rewrite !slice_mask /= map_mask /= size_map. Qed.

Variant abs_itv A := AbsItv of interval A & seq A & nat.

Definition pred_bnd {A : Type} (p : pred A) (i : itv_bound A) : bool :=
  if i is BSide _ x then p x else true.

Definition pred_itv {A : Type} (p : pred A) (i : interval A) : bool :=
  let: Interval l u := i in
  (pred_bnd p l) && (pred_bnd p u).

Definition ix_bnd {A : eqType} (s : seq A) (i : itv_bound A) : itv_bound nat :=
  match i with
  | BSide  b x => BSide  b (if b then index x s else indexlast x s)
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
                       else indexlast lb s < index x s
  | BInfty b => b
  end &&
  match u with
  | BSide b ub => if ~~ b then index x s <= indexlast ub s
                          else index x s < index ub s
  | BInfty b => ~~ b
  end.

Definition mem_ix_last {A : eqType} x (s : seq A) (i : interval A) :=
  let: Interval l u := i in
  match l with
  | BSide b lb => if b then index lb s <= indexlast x s
                       else indexlast lb s < indexlast x s
  | BInfty b => b
  end &&
  match u with
  | BSide b ub => if ~~ b then indexlast x s <= indexlast ub s
                          else indexlast x s < index ub s
  | BInfty b => ~~ b
  end.
*)
(*
Definition shl_ix_bnd {A : eqType} (s : seq A) (i : itv_bound A) n : itv_bound A :=
  match i with
  | BLeft  x => if index x s <= n then -oo else BLeft x
  | BRight x => if indexlast x s < n then -oo else BRight x
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
  indexlast x s \in interp i.
*)
(*
Notation "&[ q ] s i" := (eq_slice s q i)
 (at level 1, i at next level, s at next level,
  format "&[ q ] s  i") : fun_scope.
*)

Notation "&% s i" := (eq_slice s i)
 (at level 1, i at next level, s at next level,
  format "&% s  i") : fun_scope.

Notation "&= s i" := (eq_slice s (AbsItv i s 0%N))
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

Lemma mem_ix_last_itv x s i : mem_ix_last x s i = (indexlast x s \in ix_itv s i).
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
rewrite addn1 ltnS indexlast_cons.
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
rewrite addn1 ltnS indexlast_cons.
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
rewrite addn1 ltnS indexlast_cons.
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

Corollary slice_memE (x : A) s i :
            x \in &:s i =
            has (fun j => j \in i) (indexall x s).
Proof. by rewrite /indexall -has_pred1; apply: slice_has. Qed.

(*
Lemma slice_memE (x : A) s i :
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
*)
(* slice subset *)

Lemma slice_subset s i1 i2 :
  i1 <= i2 ->
  {subset (&:s i1) <= &:s i2}.
Proof.
case: i1=>i1 j1; case: i2=>i2 j2.
rewrite subitvE; case/andP=>Hi Hj.
move=>x Hx.
have Hij : i1 <= j1.
- apply: contraLR Hx; rewrite -ltNge=>/ltW Hji.
  by rewrite itv_swapped_bnd.
rewrite (@slice_split_bnd _ _ _ i1) /=; last first.
- by rewrite Hi /=; apply/le_trans/Hj.
rewrite mem_cat; apply/orP; right.
rewrite (@slice_split_bnd _ _ _ j1) /=; last first.
- by rewrite Hj andbT.
by rewrite mem_cat Hx.
Qed.

Corollary slice_subset_full s i :
            {subset &:s i <= s}.
Proof.
by rewrite -{2}(slice_uu s); apply/slice_subset/itv_lex1.
Qed.

Lemma ixsl_uu s q n :
  &%s (AbsItv `]-oo,+oo[ q n) = s.
Proof. by apply: slice_uu. Qed.

Lemma ixsl_underL s (i j : itv_bound A) q n :
  bnd (shl_bnd (ix_bnd q i) n) (size s) = 0%N ->
  &%s (AbsItv (Interval i j) q n) = &%s (AbsItv (Interval -oo j) q n).
Proof. by move=>H; apply: itv_underL. Qed.

Lemma ixsl_overL s (i j : itv_bound A) q n :
  size s <= bnd (shl_bnd (ix_bnd q i) n) (size s) ->
  &%s (AbsItv (Interval i j) q n) = [::].
Proof. by move=>H; apply: itv_overL. Qed.

Lemma ixsl_underR s (i j : itv_bound A) q n :
  bnd (shl_bnd (ix_bnd q j) n) (size s) = 0%N ->
  &%s (AbsItv (Interval i j) q n) = [::].
Proof. by move=>H; apply: itv_underR. Qed.

Lemma ixsl_overR s (i j : itv_bound A) q n :
  size s <= bnd (shl_bnd (ix_bnd q j) n) (size s) ->
  &%s (AbsItv (Interval i j) q n) = &%s (AbsItv (Interval i +oo) q n).
Proof. by move=>Hj; apply: itv_overR. Qed.

Lemma eqsl_underL s (i j : itv_bound A) :
  bnd (ix_bnd s i) (size s) = 0%N ->
  &=s (Interval i j) = &=s (Interval -oo j).
Proof. by move=>H; apply: itv_underL; rewrite shl_bnd0. Qed.

Lemma eqsl_underR s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) = 0%N ->
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

Lemma eqsl_swapped s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) <= bnd (ix_bnd s i) (size s) ->
  &=s (Interval i j) = [::].
Proof.
move=>H; rewrite /eq_slice /= !shl_bnd0.
by apply: itv_swapped.
Qed.

Corollary eqsl_notinL y b t s :
  t \notin s ->
  &=s (Interval (BSide b t) y) = [::].
Proof.
move=>T; apply: eqsl_overL=>/=.
rewrite (memNindex T) (memNindexlast T) if_same.
by apply: leq_addr.
Qed.

Corollary eqsl_notinR x b t s :
  t \notin s ->
  &=s (Interval x (BSide b t)) = &=s (Interval x +oo).
Proof.
move=>T; apply: eqsl_overR=>/=.
rewrite (memNindex T) (memNindexlast T) if_same.
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
by move: (mem_drop_indexlast x s); apply/contra/prefix_drop_sub/prefix_take.
Qed.

(* TODO unify? *)
Lemma eqsl_kk_out s l r k :
        ~~ l || r ->
        &=s (Interval (BSide l k) (BSide r k)) = [::].
Proof.
move=>H; apply: eqsl_swapped=>/=.
case/orP: H.
- move/negbTE=>-> /=; case: r=>//=; rewrite addn1 addn0; apply: ltnW.
  by rewrite ltnS; apply: index_leq_last.
move=>-> /=; rewrite addn0; case: l=>/=; first by rewrite addn0.
by rewrite addn1; apply: ltnW; rewrite ltnS; apply: index_leq_last.
Qed.

Lemma eqsl_kk1 s l r k :
        (count_mem k s <= 1)%N ->
        &=s (Interval (BSide l k) (BSide r k)) =
        if [&& l, ~~ r & k \in s] then [:: k] else [::].
Proof.
move/indexlast_count=>H; rewrite /eq_slice /= !subn0 -H // !if_same slice_kk.
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
rewrite /eq_slice /= !subn0 (@slice_split _ _ false (indexlast t s)) //.
by rewrite in_itv /= andbT; apply: index_leq_last.
Qed.

(* TODO tweak index/last? *)

Lemma eqsl_xxL t1 t2 s :
        index t1 s <= indexlast t2 s ->
        count_mem t1 s = 1%N ->
        &=s `[t1, t2] = t1 :: &=s `]t1, t2].
Proof.
move=>I H.
have H1: indexlast t1 s = index t1 s.
- by symmetry; apply/indexlast_count; rewrite H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ false (indexlast t1 s)) H1 /=.
- by rewrite slice_kk /= onth_index // -has_pred1 has_count H.
by rewrite in_itv /= lexx.
Qed.

Lemma eqsl_xxR t1 t2 s :
        index t1 s <= index t2 s ->
        count_mem t2 s = 1%N ->
        &=s `[t1, t2] = rcons (&=s `[t1, t2[) t2.
Proof.
move=>I H.
have H2: indexlast t2 s = index t2 s.
- by symmetry; apply/indexlast_count; rewrite H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ true (indexlast t2 s)) H2 /=.
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
have H1: indexlast t1 s = index t1 s.
- by symmetry; apply/indexlast_count; rewrite H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ false (indexlast t1 s)) H1 /=.
- by rewrite slice_kk /= onth_index // -has_pred1 has_count H.
by rewrite in_itv /= lexx.
Qed.

Lemma eqsl_oxR t1 t2 s :
        indexlast t1 s < index t2 s ->
        count_mem t2 s = 1%N ->
        &=s `]t1, t2] = rcons (&=s `]t1, t2[) t2.
Proof.
move=>I H.
have H2: indexlast t2 s = index t2 s.
- by symmetry; apply/indexlast_count; rewrite H.
rewrite /eq_slice /= !subn0 (@slice_split _ _ true (indexlast t2 s)) H2 /=.
- rewrite slice_kk /= onth_index /=; first by rewrite cats1.
  by rewrite -has_pred1 has_count H.
by rewrite in_itv /= lexx andbT.
Qed.

(* eqslice of one-element list *)

Lemma ixslice1 (k : A) i :
        &%[::k] i = if 0%N \in interp i then [::k] else [::].
Proof. by rewrite /eq_slice; case: i=>i q b /=; rewrite slice1. Qed.

Corollary eqslice1uR (k : A) b t :
            &=[::k] (Interval -oo (BSide b t)) =
            if ~~ b || (t!=k) then [::k] else [::].
Proof.
rewrite ixslice1 /= indexlast_cons indexlast0 /= andbT eq_sym.
by case: b=>//=; case: eqP.
Qed.

Corollary eqslice1uL (k : A) b t :
            &=[::k] (Interval (BSide b t) +oo) =
            if b && (t==k) then [::k] else [::].
Proof.
rewrite ixslice1 /= indexlast_cons indexlast0 /= !andbT eq_sym.
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
        &%(x::s) i = if 0%N \in interp i
                       then x::&%s (shl_abs_itv i 1)
                       else    &%s (shl_abs_itv i 1).
Proof. by rewrite /eq_slice /= slice_cons /= interp_shl. Qed.

(* cons/infty normalization *)

Lemma ixsl_ur_cons k b t s :
        &%s (AbsItv (Interval -oo (BSide b t)) (k::s) 1) =
        if (t != k) || (~~ b && (t \in s)) then &=s (Interval -oo (BSide b t)) else [::].
Proof.
rewrite /eq_slice /= subn0 indexlast_cons eq_sym.
case: eqP=>/= ?; last by rewrite -fun_if /= subn1.
case/boolP: (t \in s)=> H /=; last first.
- by rewrite andbF if_same /= itv_minfR.
by rewrite andbT; case: b=>/=; [rewrite itv_minfR | rewrite subn1].
Qed.

Lemma ixsl_ul_cons k b t s :
        &%s (AbsItv (Interval (BSide b t) +oo) (k::s) 1) =
        if (t != k) || (~~ b && (t \in s)) then &=s (Interval (BSide b t) +oo) else s.
Proof.
rewrite /eq_slice /= subn0 indexlast_cons eq_sym.
case: eqP=>/= ?; last by rewrite -fun_if /= subn1.
case/boolP: (t \in s)=> H /=; last first.
- by rewrite andbF if_same /= slice_uu.
by rewrite andbT; case: b=>/=; [rewrite slice_uu | rewrite subn1].
Qed.

(* test lemmas *)

Corollary eqsl_ux_consE k t s :
            &=(k::s) `]-oo,t] =
            k :: if (t != k) || (t \in s) then &=s `]-oo,t] else [::].
Proof. by rewrite ixslice_cons /= add0n ixsl_ur_cons. Qed.

Corollary eqsl_uo_consE k t s :
            &=(k::s) `]-oo,t[ =
            if t != k then k :: &=s `]-oo,t[ else [::].
Proof. by rewrite ixslice_cons /= ixsl_ur_cons eq_sym; case: eqP. Qed.

Corollary eqsl_xu_consE k t s :
            &=(k::s) `[t,+oo[ =
            if t != k then &=s `[t,+oo[ else k::s.
Proof. by rewrite ixslice_cons /= subn0 /= ixsl_ul_cons eq_sym; case: eqP. Qed.

Corollary eqsl_ou_consE k t s :
            &=(k::s) `]t,+oo[ =
            if (t != k) || (t \in s) then &=s `]t,+oo[ else s.
Proof. by rewrite ixslice_cons /= ixsl_ul_cons. Qed.

Corollary eqsl_ux_consLX t s :
            &=(t::s) `]-oo,t] = t :: if t \in s then &=s `]-oo,t] else [::].
Proof. by rewrite eqsl_ux_consE eqxx. Qed.

Corollary eqsl_uo_consL t s :
            &=(t::s) `]-oo,t[ = [::].
Proof. by rewrite eqsl_uo_consE eqxx. Qed.

Corollary eqsl_xu_consL t s :
            &=(t::s) `[t,+oo[ = t::s.
Proof. by rewrite eqsl_xu_consE eqxx. Qed.

Corollary eqsl_ou_consLX t s :
            &=(t::s) `]t,+oo[ = if t \in s then &=s `]t,+oo[ else s.
Proof. by rewrite eqsl_ou_consE eqxx. Qed.

(* rcons lemmas *)
(* TODO unify *)

Lemma ixslice_rcons x s i :
        &%(rcons s x) i =
        if size s \in interp i then rcons (&%s i) x
                               else        &%s i.
Proof. by rewrite /eq_slice slice_rcons. Qed.

(* rcons/infty normalization *)

Lemma ixsl_ur_rcons k b t s :
        &%s (AbsItv (Interval -oo (BSide b t)) (rcons s k) 0%N) =
        if (t \in s) && (~~ b ==> (t != k)) then &=s (Interval -oo (BSide b t)) else s.
Proof.
rewrite /eq_slice /= !subn0 index_rcons indexlast_rcons eq_sym.
case/boolP: (t \in s)=> H/=; last first.
- rewrite if_same itv_overR /=; first by apply: slice_uu.
  by rewrite leEnat -addn1; case: eqP=>/= _; rewrite -?addnA; apply: leq_addr.
case: eqP=>/= _; last by rewrite implybT.
rewrite implybF negbK /=; case: b=>//=.
rewrite itv_overR /=; first by apply: slice_uu.
by rewrite addn1.
Qed.

Lemma ixsl_ul_rcons k b t s :
        &%s (AbsItv (Interval (BSide b t) +oo) (rcons s k) 0%N) =
        if (t \in s) && (~~ b ==> (t != k)) then &=s (Interval (BSide b t) +oo) else [::].
Proof.
rewrite /eq_slice /= !subn0 index_rcons indexlast_rcons eq_sym.
case/boolP: (t \in s)=> H/=; last first.
- rewrite if_same itv_overL //= leEnat -addn1.
  by case: eqP=>/= _; rewrite -?addnA; apply: leq_addr.
case: eqP=>/= _; last by rewrite implybT.
rewrite implybF negbK /=; case: b=>//=.
by rewrite itv_overL //= addn1.
Qed.

Lemma eqsl_ux_rconsE k t s :
        &= (rcons s k) `]-oo,t] =
        if (t != k) && (t \in s) then &=s `]-oo,t] else rcons s k.
Proof.
rewrite ixslice_rcons /= subn0 !indexlast_rcons
  ixsl_ur_rcons in_itv /= leEnat eq_sym.
case: eqP=>/= _; first by rewrite andbF leqnn.
rewrite andbT; case/boolP: (t \in s)=> H/=; last by rewrite leqnSn.
by rewrite leqNgt indexlast_mem H.
Qed.

Lemma eqsl_uo_rconsE k t s :
        &= (rcons s k) `]-oo,t[ =
        if (t == k) || (t \in s) then &=s `]-oo,t[ else rcons s k.
Proof.
rewrite ixslice_rcons /= subn0 index_rcons
  ixsl_ur_rcons in_itv /= ltEnat /=.
case/boolP: (t \in s)=> H/=; first by rewrite ltnNge index_size /= orbT.
case: eqP=>/= _; last by rewrite ltnS leqnn.
rewrite ltnn eqsl_overR /=; first by rewrite /eq_slice slice_uu.
by rewrite addn0 (memNindex H).
Qed.

Lemma eqsl_xu_rconsE k t s :
        &= (rcons s k) `[t,+oo[ =
        if (t == k) || (t \in s) then rcons (&= s `[t,+oo[) k else [::].
Proof.
rewrite ixslice_rcons /= subn0 index_rcons
  ixsl_ul_rcons in_itv /= andbT leEnat.
case/boolP: (t \in s)=> H/=; first by rewrite orbT index_size.
rewrite orbF; case: eqP=>/= _; last by rewrite ltnn.
by rewrite leqnn eqsl_overL //= addn0 leEnat (memNindex H).
Qed.

Lemma eqsl_ou_rconsE k t s :
        &= (rcons s k) `]t,+oo[ =
        if (t != k) && (t \in s) then rcons (&= s `]t,+oo[) k else [::].
Proof.
rewrite ixslice_rcons /= subn0 indexlast_rcons eq_sym
  ixsl_ul_rcons in_itv /= andbT ltEnat /=.
case: eqP=>/= _; first by rewrite andbF ltnn.
rewrite andbT; case/boolP: (t \in s)=> H/=; last by rewrite ltnNge leqnSn.
by rewrite indexlast_mem H.
Qed.

(* test surgery lemmas *)

Lemma eqsl_uo_split t (s1 s2 : seq A) :
        t \notin s1 ->
        &=(s1++t::s2) `]-oo, t[ = s1.
Proof.
move=>X1.
rewrite ixslice_cat /= add0n ixslice_cons /= addn1 index_cat /= eqxx addn0 (negbTE X1) ltnn subnn /=.
rewrite ixsl_overR /=; last by rewrite subn0 addn0 index_cat (negbTE X1) /= eqxx addn0.
rewrite ixsl_uu ixsl_underR /=; last by rewrite index_cat (negbTE X1) /= eqxx addn0 ltnS leqnn.
by rewrite cats0.
Qed.

Lemma eqsl_ou_split t (s1 s2 : seq A) :
        t \notin s2 ->
        &=(s1++t::s2) `]t, +oo[ = s2.
Proof.
move=>X2.
rewrite ixslice_cat /= add0n ixslice_cons /= addn1 indexlast_cat /= inE eqxx /= andbF
  indexlast_cons eqxx /= X2 addn0 ltnn subnn /=.
rewrite ixsl_overL /=; last first.
- by rewrite subn0 addn1 indexlast_cat inE eqxx /= andbF indexlast_cons eqxx X2 addn0.
rewrite ixsl_underL /=; last first.
- by rewrite indexlast_cat inE eqxx /= andbF indexlast_cons eqxx X2 /= addn0 ltnS leqnn.
by rewrite ixsl_uu.
Qed.

Lemma eqsl_oo_split t1 t2 (s1 s2 s : seq A) :
        t1 != t2 ->
        t1 \notin s2 -> t1 \notin s ->
        t2 \notin s1 -> t2 \notin s ->
        &=(s1++t1::s++t2::s2) `]t1, t2[ = s.
Proof.
move=>N X12 X1 X21 X2.
rewrite ixslice_cat ixslice_cons /=.
rewrite indexlast_cat inE eqxx /= andbF indexlast_cons eqxx /=
  mem_cat inE (negbTE X1) (negbTE N) (negbTE X12) /= addn0 add0n addn1 ltnn subnn /=.
rewrite ixsl_overL /=; last first.
- by rewrite subn0 addn1 indexlast_cat inE eqxx /= andbF indexlast_cons eqxx /=
       mem_cat inE (negbTE X1) (negbTE N) (negbTE X12) /= addn0.
rewrite ixslice_cat /= ixsl_underL /=; last first.
- by rewrite indexlast_cat inE eqxx /= andbF indexlast_cons eqxx /=
       mem_cat inE (negbTE X1) (negbTE N) (negbTE X12) /= addn0 ltnS leqnn.
rewrite ixsl_overR /=; last first.
- by rewrite index_cat (negbTE X21) /= (negbTE N) index_cat (negbTE X2) /= eqxx
       addn0 ltnNge addnS ltnS leq_addr /= addn0 -addSn addnC addnK.
rewrite ixsl_uu ixsl_underR /=; last first.
- by rewrite index_cat (negbTE X21) /= (negbTE N) index_cat (negbTE X2) /= eqxx
       addn0 addSn addnS ltnn subnn.
by rewrite cats0.
Qed.

Corollary eqsl_oo_nil_split t1 t2 (s s2 : seq A) :
            t1 != t2 ->
            t1 \notin s2 -> t1 \notin s ->
            t2 \notin s ->
            &=(t1::s++t2::s2) `]t1, t2[ = s.
Proof.
move=>N X12 X1 X2.
by rewrite -(cat0s (_ :: _ ++ _)); apply: eqsl_oo_split.
Qed.

Lemma eqsl_oo_split_consec t1 t2 (s1 s2 : seq A) :
        &=(s1++t1::t2::s2) `]t1, t2[ = [::].
Proof.
case/boolP: (t1 == t2)=>H.
- by rewrite (eqP H); apply: eqsl_kk_out.
case/boolP: (t1 \in s2)=>H12.
- apply: eqsl_swapped=>/=.
  rewrite addn0 addn1 index_cat /= eqxx (negbTE H) indexlast_cat inE eqxx /=
    andbF !indexlast_cons eqxx /= inE (negbTE H) /= H12 /=.
  rewrite -addnS; case: ifP=>_.
  - by apply/leq_trans/leq_addr/index_size.
  by rewrite leEnat leq_add2l.
case/boolP: (t2 \in s1)=>H21.
- apply: eqsl_swapped=>/=.
  rewrite addn0 addn1 index_cat H21 indexlast_cat inE eqxx /=
    andbF !indexlast_cons eqxx /= inE (negbTE H) /= H12 /= addn0.
  by apply/ltnW; rewrite ltnS; apply: index_size.
rewrite (_ : t2::s2 = [::]++t2::s2) //.
by apply: eqsl_oo_split.
Qed.

Corollary eqsl_oo_nil_split_consec t1 t2 s :
            &=(t1::t2::s) `]t1, t2[ = [::].
Proof. by rewrite -(cat0s (_ :: _ :: _)); apply: eqsl_oo_split_consec. Qed.

(* intervals and filter *)

(* TODO unify / better theory *)
Lemma eqsl_filterL (p : pred A) b (y : A) s :
        (y \notin s) || p y ->
        &= (filter p s) (Interval -oo (BSide b y)) = filter p (&= s (Interval -oo (BSide b y))).
Proof.
case/orP=>Hy.
- rewrite !eqsl_notinR //=; first by rewrite /eq_slice !slice_uu.
  by rewrite mem_filter negb_and Hy orbT.
rewrite /eq_slice /= !subn0 /slice !drop0 /=.
elim: s=>//=h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH indexlast_cons.
  case/boolP: (h == y)=>[/eqP Ey|_] /=; first by rewrite Ey Hy in Hp.
  by rewrite -fun_if addSn /= (negbTE Hp).
rewrite !indexlast_cons mem_filter {}Hy /=.
case: b IH=>/=.
- by rewrite !addn0 => IH; case: ifP=>_ //=; rewrite Hp IH.
by rewrite !addn1 /= Hp => IH; case: ifP=>_; [rewrite !take0 | rewrite IH].
Qed.

Lemma eqsl_filterR (p : pred A) b (x : A) s :
        (x \notin s) || p x ->
        &= (filter p s) (Interval (BSide b x) +oo) = filter p (&= s (Interval (BSide b x) +oo)).
Proof.
case/orP=>Hx.
- by rewrite !eqsl_notinL //= mem_filter negb_and Hx orbT.
rewrite /eq_slice /= !subn0 /slice /= !take_size.
elim: s=>//=h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH indexlast_cons.
  case/boolP: (h == x)=>[/eqP Ex|_] /=; first by rewrite Ex Hx in Hp.
  by rewrite -fun_if addSn.
rewrite !indexlast_cons mem_filter {}Hx /=.
case: b IH=>/=.
- by rewrite !addn0 => IH; case: ifP=>_ //=; rewrite Hp.
by rewrite !addn1 /= => IH; case: ifP=>_ //=; rewrite !drop0.
Qed.

Lemma eqsl_filter (p : pred A) i s :
        pred_itv (fun x => (x \notin s) || p x) i ->
        &= (filter p s) i = filter p (&= s i).
Proof.
case: i=>[[l i|[]][r j|[]]] /=;
rewrite ?eqsl_pinfL ?eqsl_minfR ?ixsl_uu ?andbT //=.
- case/andP; case/orP=>Hi.
  - by rewrite !eqsl_notinL //= mem_filter negb_and Hi orbT.
  case/orP=>Hj.
  - rewrite !eqsl_notinR //; last by rewrite mem_filter negb_and Hj orbT.
    by apply: eqsl_filterR; rewrite Hi orbT.
  rewrite /eq_slice /= !subn0 /slice /=.
  elim: s=>//= h s IH.
  case/boolP: (p h)=>/= Hp; last first.
  - rewrite {}IH !indexlast_cons.
    case/boolP: (h == i)=>[/eqP Ei|_] /=; first by rewrite Ei Hi in Hp.
    case/boolP: (h == j)=>[/eqP Ej|_] /=; first by rewrite Ej Hj in Hp.
    by rewrite -!fun_if !addSn.
  rewrite !indexlast_cons !mem_filter Hi Hj /=.
  case: r IH; case: l=>/=; rewrite ?addn0 ?addn1 /= => IH.
  - case: ifP=>_; case: ifP=>_ //=; rewrite Hp.
    move: (@eqsl_filterL p true j s); rewrite Hj orbT=>/(_ erefl).
    by rewrite /eq_slice /slice /= !addn0 !subn0 !drop0=>->.
  - case: ifP=>_; case: ifP=>_ //=; rewrite !drop0.
    move: (@eqsl_filterL p true j s); rewrite Hj orbT=>/(_ erefl).
    by rewrite /eq_slice /slice /= !addn0 !subn0 !drop0=>->.
  - case: ifP=>_; case: ifP=>_ //=; rewrite ?Hp ?take0 //=.
    move: (@eqsl_filterL p false j s); rewrite Hj orbT=>/(_ erefl).
    by rewrite /eq_slice /slice /= !subn0 !addn1 !drop0=>->.
  case: ifP=>_; case: ifP=>_ //=; rewrite ?drop0 ?take0 //=.
  move: (@eqsl_filterL p false j s); rewrite Hj orbT=>/(_ erefl).
  by rewrite /eq_slice /slice /= !subn0 !addn1 !drop0=>->.
- by move=>H; rewrite eqsl_filterR.
by move=>H; rewrite eqsl_filterL.
Qed.

End LemmasEq.

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

Section LemmasSeqLe.
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

(*
(****************************)
(* some bureaucratic lemmas *)
(****************************)

(* membership *)

Lemma mem_oo t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <[ks[ k & k <[ks[ t2])
                (k \in |sqint t1 t2 ks|).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_xo t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <=[ks[ k & k <[ks[ t2])
                (k \in [sqint t1 t2 ks|).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_ox t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <[ks[ k & k <=[ks[ t2])
                (k \in |sqint t1 t2 ks]).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_xx t1 t2 ks k :
        reflect ([/\ k \in ks, t1 <=[ks[ k & k <=[ks[ t2])
                (k \in [sqint t1 t2 ks]).
Proof. by rewrite mem_filter andbC; apply: and3P. Qed.

Lemma mem_uo t ks k :
        reflect ([/\ k \in ks & k <[ks[ t])(k \in {sqint t ks|).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

Lemma mem_ux t ks k :
        reflect ([/\ k \in ks & k <=[ks[ t])(k \in {sqint t ks]).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

Lemma mem_ou t ks k :
        reflect ([/\ k \in ks & t <[ks[ k])(k \in |sqint t ks}).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

Lemma mem_xu t ks k :
        reflect ([/\ k \in ks & t <=[ks[ k])(k \in [sqint t ks}).
Proof. by rewrite mem_filter andbC; apply: andP. Qed.

(* has predT lemmas *)

Lemma has_oo t1 t2 ks :
        has predT |sqint t1 t2 ks| = has (fun z => t1 <[ks[ z && z <[ks[ t2) ks.
Proof.
apply/hasP/hasP=>[[x]|[x X Y]].
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
