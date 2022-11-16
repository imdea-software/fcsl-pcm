From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype seqext.

Definition shift_bnd (i : itv_bound nat) (n : nat) :=
  match i with
  | BLeft  m => BLeft (m + n)
  | BRight m => BRight (m + n)
  | BInfty b => BInfty _ b
  end.

Definition shift_itv (i : interval nat) (n : nat) :=
  let: Interval l u := i in
  Interval (shift_bnd l n) (shift_bnd u n).

Definition seq_itv {A : Type} (i : interval nat) (s : seq A) :=
  let: Interval l u := i in
  match l, u with
  | BLeft a,     BRight b     => drop a    (take b.+1 s) (* olele *)
  | BLeft a,     BLeft b      => drop a    (take b    s) (* olelt *)
  | BLeft a,     BInfty false => drop a               s  (* oleu  *)
  | BRight a,    BRight b     => drop a.+1 (take b.+1 s) (* oltle *)
  | BRight a,    BLeft b      => drop a.+1 (take b    s) (* oltlt *)
  | BRight a,    BInfty false => drop a.+1            s  (* oltu  *)
  | BInfty true, BRight b     =>            take b.+1 s  (* oule *)
  | BInfty true, BLeft b      =>            take b    s  (* oult *)
  | BInfty true, BInfty false =>                      s  (* ouu *)
  | _          , _            =>                      [::]
  end.

Arguments seq_itv {A} i s : simpl never.

Open Scope order_scope.
Import Order.Theory.

Notation "& s i" := (seq_itv i s)
 (at level 1, i at next level, s at next level,
  format "'&' s  i") : fun_scope.

About BLeft.

Compute (&[::1%nat;2;3;4;5;6;7] `]6,8]).

Section Lemmas.
Variable (A : Type).
Implicit Type (s : seq A).

Lemma sq_ouou s a b :
        &s `]a,b[ = &(&s `]-oo,b[) `]a,+oo[.
Proof. by []. Qed.

(* ... *)

Lemma int_overR s (b : bool) (x : nat) (i : itv_bound nat) :
  size s <= x + ~~ b ->
  &s (Interval i (BSide b x)) = &s (Interval i +oo).
Proof.
by case: b; rewrite /seq_itv /= ?addn0 ?addn1 => Hs; rewrite take_oversize.
Qed.

Lemma int_overL s (b : bool) (x : nat) (j : itv_bound nat) :
  size s <= x + ~~ b ->
  &s (Interval (BSide b x) j) = [::].
Proof.
case: b; rewrite /seq_itv /= ?addn0 ?addn1 => Hs;
case: j=>[[] j|[]] //=; apply: drop_oversize=>//;
rewrite size_take; case: ifP=>// Hj.
- by apply/ltnW/leq_trans/Hs.
- by apply/leq_trans/Hs/leq_ltn_trans/Hj.
- by apply/ltnW/leq_trans/Hs.
by apply/leq_trans/Hs/leq_ltn_trans/Hj.
Qed.

(* TODO refactor *)
Lemma int_cut s b x (i : interval nat) :
  x \in i ->
  &s i = &s (Interval i.1 (BSide b x)) ++ &s (Interval (BSide b x) i.2).
Proof.
case/boolP: (size s <= x + ~~ b).
- move=>H; rewrite (int_overL _ H) (int_overR _ H) cats0.
  rewrite in_itv; case: i=>[[[] av|[]]]; case=>[[] bv|[]] //;
  case/andP=>_ //= Hb; rewrite /seq_itv take_oversize //; apply: (leq_trans H)=>{H};
  by case: b=>/=; rewrite ?addn0 ?addn1 //; apply: ltnW.
rewrite -ltNge ltEnat /= =>Hx.
rewrite in_itv; case: i=>[[[] av|[]]]; case=>[[] bv|[]] //;
case/andP=>//=; rewrite /seq_itv ?leEnat ?ltEnat /= => Ha Hb;
case: b Hx=>/=; rewrite /seq_itv ?addn0 ?addn1=>Hx.
- have Hb' := ltnW Hb.
  rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(subnKC Hb) takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- have Hn' : (x <= bv.+1)%N by apply: (leq_trans Hb).
  rewrite -{1}(subnKC Hn') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- have Hb' : (x.+1 <= bv.+1)%N by [].
  by rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- rewrite -{1}(cat_take_drop x s) drop_cat size_take Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(cat_take_drop x.+1 s) drop_cat size_take Hx ltnS Ha.
- have Hb' := ltnW Hb.
  rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(subnKC Hb) takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- have Hb' : (x <= bv.+1)%N by apply: (leq_trans Hb).
  rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- have Hb' : (x.+1 <= bv.+1)%N by [].
  by rewrite -{1}(subnKC Hb') takeD drop_cat size_take take_drop subnK // Hx ltnS Ha.
- rewrite -{1}(cat_take_drop x s) drop_cat size_take Hx ltn_neqAle Ha andbT.
  by case: eqP=>//=->; rewrite subnn drop0 [in RHS](drop_oversize (n:=x)) // size_take Hx.
- by rewrite -{1}(cat_take_drop x.+1 s) drop_cat size_take Hx ltnS Ha.
- have Hb' := ltnW Hb.
  by rewrite -{1}(subnKC Hb') takeD take_drop subnK.
- by rewrite -{1}(subnKC Hb) takeD take_drop subnK.
- have Hb' : (x <= bv.+1)%N by apply: (leq_trans Hb).
  by rewrite -{1}(subnKC Hb') takeD take_drop subnK.
- have Hb' : (x.+1 <= bv.+1)%N by [].
  by rewrite -{1}(subnKC Hb') takeD take_drop subnK.
- by rewrite cat_take_drop.
by rewrite cat_take_drop.
Qed.

Corollary sq_uxou s i : s = &s `]-oo, i] ++ &s `]i, +oo[.
Proof. by rewrite -(int_cut _ _ (i:=`]-oo, +oo[)). Qed.

Corollary sq_uoxu s i : s = &s `]-oo, i[ ++ &s `[i, +oo[.
Proof. by rewrite -(int_cut _ _ (i:=`]-oo, +oo[)). Qed.

Corollary sq_uxox s a b :
        a <= b ->
        &s `]-oo, b] = &s `]-oo, a] ++ &s `]a, b].
Proof. by move=>Hab; rewrite (int_cut _ false (x:=a)). Qed.

(* ... *)

(* singleton intervals *)

Lemma sqkk s k l r :
        &s (Interval (BSide l k) (BSide r k)) =
        if l && ~~ r then oapp (cons^~ [::]) [::] (onth s k) else [::].
Proof.
rewrite /seq_itv; case: (onth_sizeP s k)=>[|v] H; rewrite H /=.
- move/size_onthPn: H=>H.
  have H' : size s <= k.+1 by apply: ltnW.
  by rewrite !take_oversize // !drop_oversize // !if_same.
move: (onth_size H)=>Hk; case: l; case: r=>/=.
- by rewrite drop_oversize // size_take Hk.
- rewrite -addn1 addnC -take_drop.
  rewrite (take_nth v); last by rewrite size_drop subn_gt0.
  by rewrite take0 /= nth_drop addn0 nth_onth H.
- by rewrite drop_oversize // size_take Hk.
rewrite drop_oversize // size_take; case: ifP=>// /negbT.
by rewrite -leqNgt.
Qed.

Corollary sqkk_xx s k :
            &s `[k, k] = oapp (cons^~ [::]) [::] (onth s k).
Proof. by rewrite sqkk. Qed.

Corollary sqkk_xo s k : &s `[k,k[ = [::].
Proof. by rewrite sqkk. Qed.

Corollary sqkk_ox s k :&s `]k,k] = [::].
Proof. by rewrite sqkk. Qed.

Corollary sqkk_oo s k : &s `]k,k[ = [::].
Proof. by rewrite sqkk. Qed.

(* endpoint split *)

Lemma sqxR a x s :
        a <= BLeft x ->
        &s (Interval a (BRight x)) =
        oapp (rcons (&s (Interval a (BLeft x))))
                    (&s (Interval a +oo))
             (onth s x).
Proof.
move=>Hax; rewrite (int_cut _ true (x:=x)) /=; last first.
- rewrite in_itv /= lexx andbT.
  by case: a Hax=>/=[ax av|ax]; case: ax.
rewrite sqkk /=; case: (onth_sizeP s x)=>[|v] H;
  rewrite H /=; last by rewrite cats1.
rewrite cats0 int_overR //= addn0.
by apply/size_onthPn.
Qed.

Lemma sqxL b x s :
        BRight x <= b ->
        &s (Interval (BLeft x) b) =
        oapp (cons^~ (&s (Interval (BRight x) b)))
                     [::]
             (onth s x).
Proof.
move=>Hxb; rewrite (int_cut _ false (x:=x)) /=; last first.
- rewrite in_itv /= lexx /=.
  by case: b Hxb=>/=[bx bv|bx]; case: bx.
rewrite sqkk /=; case: (onth_sizeP s x)=>[|v] H; rewrite H //=.
rewrite int_overL //= addn1; apply: ltW.
by apply/size_onthPn.
Qed.

Lemma sq_nil i :
        &([::] : seq A) i = [::].
Proof.
by rewrite /seq_itv /=; case: i=>[[[] av|[]]]; case=>[[] bv|[]].
Qed.

(* interval of one-element list *)

Lemma sq_singleton (k : A) i :
        &[::k] i = if 0 \in i then [::k] else [::].
Proof.
rewrite /seq_itv in_itv /=.
case: i=>[[[] av|[]]]; case=>[[] bv|[]] //=;
rewrite ?andbF ?andbT //.
- case: bv=>[|bv]/=; first by rewrite ltxx andbF.
  by rewrite andbT; case: av.
- by case: av.
- by case: av.
- by rewrite drop_oversize // size_take /=; case: ifP=>//; case: bv.
by case: bv.
Qed.

(* intervals and constructors *)

Lemma sq_cat s1 s2 i :
        &(s1++s2) i = if size s1 \in i then &s1 i ++ &s2 i
                         else if size s2 \in i then &s2 i else &s1 i.
Proof.
rewrite /seq_itv !in_itv /=.
case: i=>[[[] av|[]]]; case=>[[] bv|[]] //=;
rewrite ?andbF ?andbT ?leEnat ?ltEnat //=.
- rewrite take_cat; case: ltngtP=>Hb1.
  - rewrite andbF; case: ifP=>//.
    case/andP=>Ha Hb2.
Admitted.

End Lemmas.