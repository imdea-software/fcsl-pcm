From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype seqext.

Open Scope order_scope.
Import Order.Theory.

(* TODO move to prelude *)
Lemma drop_take_id {A} x (s : seq A) : drop x (take x s) = [::].
Proof. by rewrite -{2}(add0n x) -take_drop take0. Qed.

(* convert bound to nat *)
(* maps -oo -> 0, +oo -> m *)
Definition bnd (i : itv_bound nat) (m : nat) : nat :=
  match i with
  | BSide  b n => n + ~~ b
  | BInfty b   => if b then 0 else m
  end.

(* apply interval to seq *)
Definition slice {A : Type} (s : seq A) (i : interval nat) :=
  let sz := size s in
  let: Interval l u := i in
  drop (bnd l sz) (take (bnd u sz) s).

Arguments slice {A} s i : simpl never.

Notation "& s i" := (slice s i)
 (at level 1, i at next level, s at next level,
  format "'&' s  i") : fun_scope.

(* subtract n from bound, convert values past zero to -oo *)
Definition shl_bnd (i : itv_bound nat) (n : nat) :=
  match i with
  | BSide  b m => if m + ~~ b <= n then -oo else BSide b (m - n)
  | BInfty b => BInfty _ b
  end.

Definition shl_itv (i : interval nat) (n : nat) :=
  let: Interval l u := i in
  Interval (shl_bnd l n) (shl_bnd u n).

Lemma mem_shl n m i :
  (n \in shl_itv i m) = (n + m \in i).
Proof.
rewrite !in_itv; case: i=>i j /=.
case: i=>[[] i|[]]; case: j=>[[] j|[]] /=;
rewrite ?leEnat ?ltEnat ?addn0 ?addn1 ?andbF ?andbT //=.
- by case: (leqP i m)=>/= Hi;
  [ have ->/=: (i <= n + m)%N by apply/(leq_trans Hi)/leq_addl
  | rewrite leEnat leq_subLR addnC; case: (leqP i (n + m))=>//= _];
  (case: (leqP j m)=>/= Hj;
  [ symmetry; apply/negbTE; rewrite -ltnNge ltnS;
      by apply/(leq_trans Hj)/leq_addl |
    by rewrite ltEnat /= ltn_subRL addnC]).
- by case: (leqP i m)=>/= Hi;
  [ have ->/=: (i <= n + m)%N by apply/(leq_trans Hi)/leq_addl
  | rewrite leEnat leq_subLR addnC; case: (leqP i (n + m))=>//= _];
  (case: (ltnP j m)=>/= Hj;
  [ symmetry; apply/negbTE; rewrite -ltnNge;
      by apply/(leq_trans Hj)/leq_addl |
    by rewrite leEnat /= leq_subRL // addnC]).
- case: (leqP i m)=>/= Hi.
  - by symmetry; apply/(leq_trans Hi)/leq_addl.
  by rewrite leEnat leq_subLR addnC.
- by case: (ltnP i m)=>/= Hi;
  [ have ->/=: (i < n + m)%N by apply/(leq_trans Hi)/leq_addl
  | rewrite ltEnat /= ltn_subLR // addnC; case: (ltnP i (n + m))=>//= _];
  (case: (leqP j m)=>/= Hj;
   [ symmetry; apply/negbTE; rewrite -ltnNge ltnS;
     by apply/(leq_trans Hj)/leq_addl |
    by rewrite ltEnat /= ltn_subRL addnC]).
- by case: (ltnP i m)=>/= Hi;
  [ have ->/=: (i < n + m)%N by apply/(leq_trans Hi)/leq_addl
  | rewrite ltEnat /= ltn_subLR // addnC; case: (ltnP i (n + m))=>//= _];
  (case: (ltnP j m)=>/= Hj;
  [ symmetry; apply/negbTE; rewrite -ltnNge;
      by apply/(leq_trans Hj)/leq_addl |
    by rewrite leEnat /= leq_subRL // addnC]).
- case: (ltnP i m)=>/= Hi.
  - by symmetry; apply/(leq_trans Hi)/leq_addl.
  by rewrite ltEnat /= ltn_subLR // addnC.
- case: (leqP j m)=>/= Hj.
  - symmetry; apply/negbTE; rewrite -ltnNge ltnS.
    by apply/(leq_trans Hj)/leq_addl.
  by rewrite ltEnat /= ltn_subRL // addnC.
case: (ltnP j m)=>/= Hj.
- symmetry; apply/negbTE; rewrite -ltnNge.
  by apply/(leq_trans Hj)/leq_addl.
by rewrite leEnat /= leq_subRL // addnC.
Qed.

(* Compute (&[::1%nat;2;3;4;5;6;7] `[1%nat,4[). *)

Section Lemmas.
Variable (A : Type).
Implicit Type (s : seq A).

(* "test" lemmas *)
Lemma slice_ouou s a b :
        &s `]a,b[ = &(&s `]-oo,b[) `]a,+oo[.
Proof. by rewrite /slice /= !addn0 drop0 take_size. Qed.

Lemma slice_uouo s a b :
        &s `]a,b+a] = &(&s `]a,+oo[) `]-oo,b[.
Proof.
by rewrite /slice /= !addn1 !addn0 drop0 take_size take_drop addnS.
Qed.

(* ... *)

(* some simplifying equalities on slices *)

Lemma slice_uu s : &s `]-oo, +oo[ = s.
Proof. by rewrite /slice /= drop0 take_size. Qed.

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

Lemma itv_minfR s (i : itv_bound nat) :
  &s (Interval i -oo) = [::].
Proof. by rewrite /slice /= take0. Qed.

Lemma itv_pinfL s (j : itv_bound nat) :
  &s (Interval +oo j) = [::].
Proof.
rewrite /slice /=; apply: drop_oversize.
by rewrite size_take_min; apply: geq_minr.
Qed.

Lemma itv_swapped s (i j : itv_bound nat) :
  bnd j (size s) <= bnd i (size s) ->
  &s (Interval i j) = [::].
Proof.
move=>H; rewrite /slice; apply: drop_oversize.
rewrite size_take_min; apply/leq_trans/H.
by exact: geq_minl.
Qed.

(* splitting slice *)

Lemma slice_split s b x (i : interval nat) :
  x \in i ->
  &s i = &s (Interval i.1 (BSide b x)) ++ &s (Interval (BSide b x) i.2).
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
Corollary slice_uxou s i : s = &s `]-oo, i] ++ &s `]i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uoxu s i : s = &s `]-oo, i[ ++ &s `[i, +oo[.
Proof. by rewrite -(slice_split _ _ (i:=`]-oo, +oo[)) // slice_uu. Qed.

Corollary slice_uxox s a b :
            a <= b ->
            &s `]-oo, b] = &s `]-oo, a] ++ &s `]a, b].
Proof. by move=>Hab; rewrite (slice_split _ false (x:=a)). Qed.

(* ... *)

(* singleton slice *)

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

(* "test" lemmas *)
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

(* slice of empty list *)

Lemma slice0 i :
        &([::] : seq A) i = [::].
Proof.
by rewrite /slice /=; case: i=>[[[] av|[]]]; case=>[[] bv|[]].
Qed.

(* slice of one-element list *)

Lemma slice1 (k : A) i :
        &[::k] i = if 0 \in i then [::k] else [::].
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
        &(s1++s2) i = &s1 i ++ &s2 (shl_itv i (size s1)).
Proof.
rewrite /slice; case: i=>[[[] i|[]][[] j|[]]] /=;
rewrite ?addn0 ?addn1 ?take0 ?drop0 ?take_size ?drop_size
  ?size_cat ?leEnat ?ltEnat //.
- (* [i, j[ *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite (ltnW Hj) /= take0 /= cats0.
  rewrite (leqNgt j) ltn_neqAle Hj andbT negbK (take_oversize (n:=j)) // drop_cat.
  case: eqP=>[->|_].
  - rewrite subnn /= take0 /=; case: ltnP=>// Hji.
    by rewrite cats0 drop_oversize //; apply/leq_trans/Hji.
  case: ltnP=>Hi; first by rewrite (ltnW Hi) /= addn0 drop0.
  rewrite (drop_oversize (n:=i)) //= addn0 (leqNgt i) ltn_neqAle Hi andbT negbK.
  case: eqP=>[->|_] /=; last by rewrite addn0.
  by rewrite subnn drop0.
- (* [i, j] *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite (ltnW Hj) /= take0 /= cats0.
  rewrite (ltnNge j) (take_oversize (n:=j.+1)) // drop_cat.
  move: Hj; rewrite leq_eqVlt ltnS; case/orP=>[/eqP E|Hj].
  - rewrite E subnn ltnn take0 /= ltnS; case: leqP=>// Hji.
    by rewrite cats0 drop_oversize // E.
  rewrite Hj /= addn1 subSn //; case: ltnP=>Hi; first by rewrite (ltnW Hi) /= drop0.
  rewrite (drop_oversize (n:=i)) //= (leqNgt i) ltn_neqAle Hi andbT negbK.
  case: eqP=>[->|_] /=; last by rewrite addn0.
  by rewrite subnn drop0.
- (* [i, +oo[ *)
  rewrite drop_cat; case: ltnP=>Hi; first by rewrite (ltnW Hi) /= drop0.
  rewrite (drop_oversize (n:=i)) //= (leqNgt i) ltn_neqAle Hi andbT negbK.
  case: eqP=>[->|_] /=; last by rewrite addn0.
  by rewrite subnn drop0.
- (* ]i, j[ *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite (ltnW Hj) /= take0 /= cats0.
  rewrite (leqNgt j) (ltn_neqAle _ j) Hj andbT negbK (take_oversize (n:=j)) // drop_cat.
  case: eqP=>[->|_].
  - rewrite subnn /= take0 /=; case: ltnP=>// Hji.
    by rewrite cats0 drop_oversize //; apply/leq_trans/Hji.
  case: ltnP=>Hi; first by rewrite (ltnW Hi) /= addn0 drop0.
  rewrite (drop_oversize (n:=i.+1)) //= addn0.
  move: Hi; rewrite leq_eqVlt ltnS; case/orP=>[/eqP ->|Hi].
  - by rewrite subnn ltnS leqnn /= drop0.
  by rewrite ltnNge Hi /= addn1 subSn.
- (* ]i, j] *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite (ltnW Hj) /= take0 /= cats0.
  rewrite (ltnNge j) (take_oversize (n:=j.+1)) // drop_cat.
  move: Hj; rewrite leq_eqVlt ltnS; case/orP=>[/eqP E|Hj].
  - rewrite E subnn ltnn take0 /= ltnS; case: leqP=>// Hji.
    by rewrite cats0 drop_oversize // E.
  rewrite Hj /= addn1 subSn //; case: ltnP=>Hi; first by rewrite (ltnW Hi) /= drop0.
  rewrite (drop_oversize (n:=i.+1)) //=.
  move: Hi; rewrite leq_eqVlt ltnS; case/orP=>[/eqP ->|Hi].
  - by rewrite subnn ltnS leqnn /= drop0.
  by rewrite ltnNge Hi /= addn1 subSn.
- (* ]i, +oo[ *)
  rewrite drop_cat; case: ltnP=>Hi; first by rewrite (ltnW Hi) /= drop0.
  rewrite (drop_oversize (n:=i.+1)) //=.
  move: Hi; rewrite leq_eqVlt ltnS; case/orP=>[/eqP ->|Hi].
  - by rewrite subnn ltnS leqnn /= drop0.
  by rewrite ltnNge Hi /= addn1 subSn.
- (* ]-oo, j[ *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite (ltnW Hj) /= take0 /= cats0.
  rewrite (leqNgt j) (ltn_neqAle _ j) Hj andbT negbK (take_oversize (n:=j)) //.
  case: eqP=>/= [->|_]; last by rewrite addn0.
  by rewrite subnn take0.
- (* ]-oo, j] *)
  rewrite take_cat; case: ltnP=>Hj; first by rewrite (ltnW Hj) /= take0 /= cats0.
  rewrite (ltnNge j) (take_oversize (n:=j.+1)) //.
  move: Hj; rewrite leq_eqVlt ltnS; case/orP=>[/eqP ->|Hj].
  - by rewrite subnn ltnn take0.
  by rewrite Hj /= addn1 subSn.
- (* ]+oo, j[ *)
  rewrite !drop_oversize ?if_same // size_take; case: ltnP=>//=;
  rewrite ?size_cat; try by move/ltnW.
  by rewrite leqnn.
(* ]+oo, j] *)
rewrite !drop_oversize ?if_same // size_take; case: ltnP=>//=;
rewrite ?size_cat; try by move/ltnW.
by rewrite leqnn.
Qed.

Lemma slice_cat_piecewise s1 s2 i :
        &(s1++s2) i = if size s1 \in i
                        then &s1 (Interval i.1 +oo) ++ &s2 (Interval -oo (shl_bnd i.2 (size s1)))
                        else if bnd i.2 (size s1 + size s2) <= size s1
                               then &s1 i
                               else &s2 (shl_itv i (size s1)).
Proof.
rewrite slice_cat; case: i=>i j /=; case: ifP.
- rewrite in_itv; case/andP=>Hi Hj.
  rewrite (itv_overR _ (j:=j)); last first.
  - case: j Hj=>[[] j|[]] //=.
    - by rewrite addn0; move/ltnW.
    by rewrite addn1 leEnat; move/(ltnW (n:=j.+1)).
  rewrite (itv_underL (i:=shl_bnd i _)) //.
  case: i Hi=>[[] i|[]] //=.
  - by rewrite addn0 => ->.
  by rewrite addn1 leEnat ltEnat /= =>->.
rewrite in_itv=>/negbT; rewrite negb_and=>H.
case: ifP=>Hj.
- rewrite (itv_underR (s:=s2)); first by rewrite cats0.
  case: {H}j Hj=>[[] j|[]] //=.
  - by rewrite addn0=>->.
  - by rewrite addn1=>->.
  by rewrite leEnat -{2}(addn0 (size s1)) leq_add2l leqn0 => /eqP.
case/orP: H; last first.
- case: j Hj=>[[] j|[]] //=.
  - by rewrite addn0 -leNgt=>->.
  by rewrite leEnat addn1 -ltnNge =>->.
case: i=>[[] i|[]] //=; last by rewrite !itv_pinfL.
- rewrite leEnat addn0 -ltnNge => Hi.
  rewrite (leqNgt i) Hi /= itv_overL //= addn0 leEnat.
  by apply: ltnW.
rewrite ltEnat leEnat /= addn1 -leqNgt => Hi.
rewrite ltnNge Hi /= itv_overL //= addn1 leEnat.
by apply: ltnW.
Qed.

Lemma slice_cons x s i :
        &(x::s) i = if 0 \in i then x::&s (shl_itv i 1) else &s (shl_itv i 1).
Proof. by rewrite -cat1s slice_cat /= slice1; case: ifP. Qed.

Lemma slice_rcons x s i :
        &(rcons s x) i = if size s \in i then rcons (&s i) x else &s i.
Proof.
rewrite -cats1 slice_cat /= slice1 mem_shl add0n.
by case: ifP=>_; [rewrite cats1 | rewrite cats0].
Qed.

End Lemmas.