From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype seqext.

Open Scope order_scope.
Import Order.Theory.

Definition bnd (i : itv_bound nat) (m : nat) : nat :=
  match i with
  | BSide  b n => n + ~~ b
  | BInfty b   => if b then 0 else m
  end.

Definition slice {A : Type} (s : seq A) (i : interval nat) :=
  let sz := size s in
  let: Interval l u := i in
  drop (bnd l sz) (take (bnd u sz) s).

Arguments slice {A} s i : simpl never.

Definition shl_bnd (i : itv_bound nat) (n : nat) :=
  match i with
  | BSide  b m => BSide b (m - n)
  | BInfty b => BInfty _ b
  end.

Definition shl_itv (i : interval nat) (n : nat) :=
  let: Interval l u := i in
  Interval (shl_bnd l n) (shl_bnd u n).

Notation "& s i" := (slice s i)
 (at level 1, i at next level, s at next level,
  format "'&' s  i") : fun_scope.

Compute (&[::1%nat;2;3;4;5;6;7] `[1%nat,4[).

Section Lemmas.
Variable (A : Type).
Implicit Type (s : seq A).

Lemma slice_uu s : &s `]-oo, +oo[ = s.
Proof. by rewrite /slice /= drop0 take_size. Qed.

Lemma slice_ouou s a b :
        &s `]a,b[ = &(&s `]-oo,b[) `]a,+oo[.
Proof.
rewrite /slice /= !addn0 drop0 take_take size_take;
case: ifP=>// /negbT; rewrite -leqNgt // => H.
by rewrite take_size take_oversize.
Qed.

(* ... *)

Lemma itv_underL s (i j : itv_bound nat) :
  bnd i (size s) = 0 ->
  &s (Interval i j) = &s (Interval -oo j).
Proof. by move=>Hi; rewrite /slice /= Hi drop0. Qed.

Lemma itv_underR s (i j : itv_bound nat) :
  bnd j (size s) = 0 ->
  &s (Interval i j) = [::].
Proof. by move=>Hj; rewrite /slice /= Hj take0. Qed.

Lemma itv_overL s (i j : itv_bound nat) :
  size s <= bnd i (size s) ->
  &s (Interval i j) = [::].
Proof.
move=>Hi /=; rewrite /slice /=; apply: drop_oversize.
rewrite size_take; case: ifP=>// H.
by apply/ltnW/(leq_trans H).
Qed.

Lemma itv_overR s (i j : itv_bound nat) :
  size s <= bnd j (size s) ->
  &s (Interval i j) = &s (Interval i +oo).
Proof.
by move=>Hj; rewrite /slice /= take_size take_oversize.
Qed.

(* TODO refactor *)
Lemma slice_split s b x (i : interval nat) :
  x \in i ->
  &s i = &s (Interval i.1 (BSide b x)) ++ &s (Interval (BSide b x) i.2).
Proof.
case/boolP: (size s <= bnd (BSide b x) (size s)).
- move=>H; rewrite (itv_overL _ H) (itv_overR _ H) cats0.
  rewrite in_itv; case: i=>[[[] i|[]]]; case=>[[] j|[]] //;
  case/andP=>_ //= Hb; rewrite /slice /= ?drop0 take_size take_oversize //;
  by apply: (leq_trans H)=>{H}; case: b=>/=; rewrite ?addn0 ?addn1 //; apply/ltnW.
rewrite -ltNge ltEnat /= =>Hx.
rewrite in_itv; case: i=>[[[] i|[]]]; case=>[[] j|[]] //;
case/andP=>//=; rewrite /slice /= ?leEnat ?ltEnat /= => Ha Hb;
case: b Hx=>/=; rewrite ?drop0 ?take_size ?addn0 ?addn1=>Hx.
- have Hb' := ltnW Hb.
  rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(subnKC Hb) takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- have Hn' : (x <= j.+1)%N by apply: (leq_trans Hb).
  rewrite -{1}(subnKC Hn') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- have Hb' : (x.+1 <= j.+1)%N by [].
  by rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- rewrite -{1}(cat_take_drop x s) drop_cat size_take Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(cat_take_drop x.+1 s) drop_cat size_take Hx ltnS Ha.
- have Hb' := ltnW Hb.
  rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(subnKC Hb) takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- have Hb' : (x <= j.+1)%N by apply: (leq_trans Hb).
  rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- have Hb' : (x.+1 <= j.+1)%N by [].
  by rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- rewrite -{1}(cat_take_drop x s) drop_cat size_take Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(cat_take_drop x.+1 s) drop_cat size_take Hx ltnS Ha.
- have Hb' := ltnW Hb.
  by rewrite -{1}(subnKC Hb') takeD take_drop subnK.
- by rewrite -{1}(subnKC Hb) takeD take_drop subnK.
- have Hb' : (x <= j.+1)%N by apply: (leq_trans Hb).
  by rewrite -{1}(subnKC Hb') takeD take_drop subnK.
- have Hb' : (x.+1 <= j.+1)%N by [].
  by rewrite -{1}(subnKC Hb') takeD take_drop subnK.
- by rewrite cat_take_drop.
by rewrite cat_take_drop.
Qed.

Corollary slice_uxou s i : s = &s `]-oo, i] ++ &s `]i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uoxu s i : s = &s `]-oo, i[ ++ &s `[i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uxox s a b :
            a <= b ->
            &s `]-oo, b] = &s `]-oo, a] ++ &s `]a, b].
Proof. by move=>Hab; rewrite (slice_split _ false (x:=a)). Qed.

(* ... *)

(* singleton intervals *)

Lemma slice_kk s k l r :
        &s (Interval (BSide l k) (BSide r k)) =
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

Corollary slice_kkxx s k :
            &s `[k, k] = oapp (cons^~ [::]) [::] (onth s k).
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkxo s k : &s `[k,k[ = [::].
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkox s k :&s `]k,k] = [::].
Proof. by rewrite slice_kk. Qed.

Corollary slice_kkoo s k : &s `]k,k[ = [::].
Proof. by rewrite slice_kk. Qed.

(* endpoint split *)

Lemma slice_xR a x s :
        a <= BLeft x ->
        &s (Interval a (BRight x)) =
        oapp (rcons (&s (Interval a (BLeft x))))
                    (&s (Interval a +oo))
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
        &s (Interval (BLeft x) b) =
        oapp (cons^~ (&s (Interval (BRight x) b)))
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

Lemma slice0 i :
        &([::] : seq A) i = [::].
Proof.
by rewrite /slice /=; case: i=>[[[] av|[]]]; case=>[[] bv|[]].
Qed.

(* interval of one-element list *)

Lemma slice1 (k : A) i :
        &[::k] i = if 0 \in i then [::k] else [::].
Proof.
rewrite /slice in_itv /=.
case: i=>[[[] av|[]]]; case=>[[] bv|[]] //=;
rewrite ?drop0 ?addn0 ?addn1 ?andbF ?andbT //=.
- case: bv=>[|bv]/=; first by rewrite ltxx andbF.
  by rewrite andbT; case: av.
- by case: av.
- by case: av.
- by apply: drop_oversize; rewrite size_take /=; case: ifP=>//; case: bv.
- by case: bv.
by case: bv.
Qed.

(* intervals and constructors *)

Lemma slice_cat s1 s2 i :
        &(s1++s2) i = if size s1 \in i
                        then &s1 (Interval i.1 +oo) ++ &s2 (Interval -oo (shl_bnd i.2 (size s1)))
                        else if bnd i.2 (size s1 + size s2) <= size s1
                               then &s1 i
                               else &s2 (shl_itv i (size s1)).
Proof.
rewrite /slice !in_itv /=.
case: i=>[[[] i|[]]]; case=>[[] j|[]] //=;
rewrite ?addn0 ?addn1 ?drop0 ?take0 ?take_size ?drop_size
  ?size_cat ?andbF ?andbT ?leEnat ?ltEnat /= ?if_same //.
- (* [i, j[ *)
  case: ifP.
  - case/andP=>Hi Hj; rewrite take_cat ltnNge (ltnW Hj) /=
      drop_cat ltn_neqAle Hi andbT; case: eqP=>//= ->.
    by rewrite subnn drop0 drop_size.
  move/negbT; rewrite negb_and -ltnNge -leqNgt take_cat; case/orP=>H.
  - case: ltnP; first by move/ltnW->.
    rewrite leq_eqVlt; case/orP.
    - by move/eqP=><-; rewrite subnn take0 cats0 take_size /= leqnn.
    by move=>Hj; rewrite leqNgt Hj /= drop_cat ltnNge (ltnW H).
  rewrite H ltn_neqAle H andbT; case: eqP=>//= ->.
  by rewrite subnn take0 take_size cats0.
- (* [i, j] *)
  case: ifP.
  - case/andP=>Hi Hj; rewrite take_cat subSn // ltnNge (ltnW (n:=j.+1) Hj) /=
      drop_cat ltn_neqAle Hi andbT; case: eqP=>//= ->.
    by rewrite subnn drop0 drop_size.
  move/negbT; rewrite negb_and -!ltnNge take_cat; case/orP=>H.
  - case: ltnP; first by move/ltnW->.
    rewrite leq_eqVlt ltnS ltnNge; case/orP.
    - by move/eqP=>E; rewrite E subnn ltnn /= take0 cats0 -E take_size.
    by move=>Hj; rewrite Hj /= drop_cat ltnNge (ltnW H) /= subSn.
  rewrite H ltn_neqAle H andbT; case: eqP=>//= ->.
  by rewrite subnn take0 take_size cats0.
- (* [i, +oo[ *)
  rewrite drop_cat; case: ltnP=>Hi; first by rewrite (ltnW Hi).
  case: ltngtP Hi=>//= Hi _.
  - rewrite -{3}(addn0 (size s1)) leq_add2l leqn0; case: eqP=>//.
    by move/eqP/nilP=>->/=; rewrite drop_oversize //; apply: ltnW.
  by rewrite -Hi subnn drop0 drop_size.
- (* ]i, j[ *)
  case: ifP.
  - case/andP=>Hi Hj; rewrite take_cat ltnNge (ltnW Hj) /=
      drop_cat ltn_neqAle Hi andbT; case: eqP=>//= ->.
    by rewrite subnn drop0 drop_size.
  move/negbT; rewrite negb_and -ltnNge -leqNgt take_cat; case/orP=>H.
  - case: ltnP; first by move/ltnW->.
    rewrite leq_eqVlt; case/orP.
    - by move/eqP=><-; rewrite subnn take0 cats0 take_size /= leqnn.
    by move=>Hj; rewrite leqNgt Hj /= drop_cat ltnNge (ltnW H) /= subSn.
  rewrite H ltn_neqAle H andbT; case: eqP=>//= ->.
  by rewrite subnn take0 take_size cats0.
- (* ]i, j] *)
  case: ifP.
  - case/andP=>Hi Hj; rewrite take_cat subSn // ltnNge (ltnW (n:=j.+1) Hj) /=
      drop_cat ltn_neqAle Hi andbT; case: eqP=>//= ->.
    by rewrite subnn drop0 drop_size.
  move/negbT; rewrite negb_and -!ltnNge take_cat; case/orP=>H.
  - case: ltnP; first by move/ltnW->.
    rewrite leq_eqVlt ltnS ltnNge; case/orP.
    - by move/eqP=>E; rewrite E subnn ltnn /= take0 cats0 -E take_size.
    by move=>Hj; rewrite Hj /= drop_cat ltnNge (ltnW H) /= !subSn.
  rewrite H ltn_neqAle H andbT; case: eqP=>//= ->.
  by rewrite subnn take0 take_size cats0.
- (* ]i, +oo[ *)
  rewrite drop_cat; case: ltnP=>Hi; first by rewrite (ltnW Hi).
  rewrite ltnNge; case: ltngtP Hi=>//= + _.
  - rewrite ltnS=>Hi; rewrite Hi /= -{3}(addn0 (size s1)) leq_add2l leqn0; case: eqP.
    - by move/eqP/nilP=>->/=; rewrite drop_oversize //; apply: ltnW.
    by move=>_; rewrite subSn.
  by move=>Hi; rewrite Hi subnn drop0 ltnn /= -Hi drop_size.
- (* ]-oo, j[ *)
  rewrite take_cat; case: ltngtP=>//= ->.
  by rewrite subnn take0 take_size cats0.
- (* ]-oo, j] *)
  rewrite -ltnS take_cat; case: ltngtP=>// Hj.
  - by rewrite subSn.
  by rewrite Hj subnn take0 take_size cats0.
- (* ]+oo, j[ *)
  rewrite !drop_oversize ?if_same // size_take; case: ltnP=>//=;
  rewrite ?size_cat; try by move/ltnW.
  by rewrite leqnn.
(* ]+oo, j] *)
rewrite !drop_oversize ?if_same // size_take; case: ltnP=>//=;
rewrite ?size_cat; try by move/ltnW.
by rewrite leqnn.
Qed.

Lemma slice_cat' s1 s2 i :
        &(s1++s2) i = if size s1 \in i
                        then &s1 i ++ &s2 (shl_itv i (size s1))
                        else if bnd i.2 (size s1 + size s2) <= size s1
                               then &s1 i
                               else &s2 (shl_itv i (size s1)).
Proof.
rewrite slice_cat; case: ifP=>//; case: i=>i j /=.
rewrite in_itv; case/andP=>Hi Hj.
rewrite (itv_overR _ (j:=j)); last first.
- case: j Hj=>[[] j|[]] //=.
  - by rewrite addn0; move/ltnW.
  by rewrite addn1 leEnat; move/(ltnW (n:=j.+1)).
rewrite (itv_underL (i:=shl_bnd i _)) //.
case: i Hi=>[[] i|[]] /=.
- by rewrite addn0 leEnat -subn_eq0 => /eqP.
rewrite addn1.
Admitted.

End Lemmas.