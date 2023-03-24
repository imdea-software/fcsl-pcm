From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype seqext slice useqord.

Open Scope order_scope.
Import Order.Theory.

(* slicing by element index *)
(* we assume the sequences are unique and take the first index *)
(* however most lemmas don't require this explicitly *)

Definition ix_bnd {A : eqType} (s : seq A) (i : itv_bound A) : itv_bound nat :=
  match i with
  | BSide  b x => BSide  b (index x s)
  | BInfty b   => BInfty _ b
  end.

Definition ix_itv {A : eqType} (s : seq A) (i : interval A) : interval nat :=
  let: Interval l u := i in
  Interval (ix_bnd s l) (ix_bnd s u).

Definition eq_slice {A : eqType} (s : seq A) (i : interval A) :=
  slice s (ix_itv s i).

Notation "&= s i" := (eq_slice s i)
 (at level 1, i at next level, s at next level,
  format "&= s  i") : fun_scope.

Section Lemmas.
Variable (A : eqType).
Implicit Type (s : seq A).

Lemma eqsl_uu s :
  &=s `]-oo,+oo[ = s.
Proof. by apply: slice_uu. Qed.

Lemma eqsl_underL s (i j : itv_bound A) :
  bnd (ix_bnd s i) (size s) = 0%N ->
  &=s (Interval i j) = &=s (Interval -oo j).
Proof. by move=>H; apply: itv_underL. Qed.

Lemma eqsl_underR s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) = 0%N ->
  &=s (Interval i j) = [::].
Proof. by move=>H; apply: itv_underR. Qed.

Lemma eqsl_overL s (i j : itv_bound A) :
  size s <= bnd (ix_bnd s i) (size s) ->
  &=s (Interval i j) = [::].
Proof. by move=>H; apply: itv_overL. Qed.

Lemma eqsl_overR s (i j : itv_bound A) :
  size s <= bnd (ix_bnd s j) (size s) ->
  &=s (Interval i j) = &=s (Interval i +oo).
Proof. by move=>Hj; apply: itv_overR. Qed.

Lemma eqsl_swapped s (i j : itv_bound A) :
  bnd (ix_bnd s j) (size s) <= bnd (ix_bnd s i) (size s) ->
  &=s (Interval i j) = [::].
Proof.
by move=>H; rewrite /eq_slice /=; apply: itv_swapped.
Qed.

Corollary eqsl_notinL y b t s :
  t \notin s ->
  &=s (Interval (BSide b t) y) = [::].
Proof.
move=>T; apply: eqsl_overL=>/=.
by rewrite (memNindex T); apply: leq_addr.
Qed.

Corollary eqsl_notinR x b t s :
  t \notin s ->
  &=s (Interval x (BSide b t)) = &=s (Interval x +oo).
Proof.
move=>T; apply: eqsl_overR=>/=.
by rewrite (memNindex T); apply: leq_addr.
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
rewrite /eq_slice /slice /= addn0.
apply/negP=>/mem_drop; apply/negP.
by apply: mem_take_index.
Qed.

Lemma eqsliceLO_notin (s : seq A) x b :
        uniq s ->
        x \notin &=s (Interval (BRight x) b).
Proof.
rewrite /eq_slice /slice /= addn1 => U.
move: (mem_drop_indexlast x s); rewrite indexlast_uniq //.
by apply/contra/prefix_drop_sub/prefix_take.
Qed.

(*
Lemma eqsl_kk_out s l r k :
        ~~ l || r ->
        &=s (Interval (BSide l k) (BSide r k)) = [::].
Proof.
move=>H; apply: eqsl_swapped=>/=.
case/orP: H.
- by move/negbTE=>-> /=; case: r=>//=; rewrite addn1 addn0.
move=>-> /=; rewrite addn0; case: l=>/=; first by rewrite addn0.
by rewrite addn1.
Qed.
*)

Lemma eqsl_kk1 (s : seq A) l r k :
        &=s (Interval (BSide l k) (BSide r k)) =
        if [&& l, ~~ r & k \in s] then [:: k] else [::].
Proof.
rewrite /eq_slice /= slice_kk onth_index.
apply/esym; case: ifP; first by case/and3P=>->->->.
move/negbT; rewrite !negb_and negbK.
case/or3P=>[/negbTE->|->|/negbTE->] //=.
- by rewrite andbF.
by rewrite if_same.
Qed.

(* endpoint split of single-bounded interval *)

Lemma eqsl_uxR t s :
        &=s `]-oo, t] = if t \in s
                          then rcons (&=s `]-oo, t[) t
                          else &=s `]-oo, t[.
Proof.
rewrite /eq_slice /= (@slice_split _ _ _ true (index t s)) /=; last first.
- by rewrite in_itv /=.
rewrite slice_kk /= onth_index; case: ifP=>/= H.
- by rewrite cats1.
by rewrite cats0.
Qed.

Lemma eqsl_xuL t s :
        &=s `[t, +oo[ = if t \in s
                          then t :: &=s `]t, +oo[
                          else &=s `]t, +oo[.
Proof.
rewrite /eq_slice /= (@slice_split _ _ _ false (index t s)) //=; last first.
- by rewrite in_itv /= andbT.
by rewrite slice_kk /= onth_index; case: ifP.
Qed.

Lemma eqsl_xxL t1 t2 s :
        &=s `[t1, t2] = if (t1 <=[s] t2) && (t1 \in s)
                          then t1 :: &=s `]t1, t2]
                          else [::].
Proof.
rewrite /eq_slice /seq_le /=.
case: leqP=>I /=; last by rewrite itv_swapped_bnd.
rewrite (@slice_split _ _ _ false (index t1 s)) /=; last first.
- by rewrite in_itv /= lexx.
rewrite slice_kk /= onth_index; case: ifP=>//= /negbT N1.
by rewrite (memNindex N1) itv_overL //= addn1.
Qed.

Lemma eqsl_xxR t1 t2 s :
        &=s `[t1, t2] = if t1 <=[s] t2 then
                           if t2 \in s
                             then rcons (&=s `[t1, t2[) t2
                             else &=s `[t1, +oo[
                           else [::].
Proof.
rewrite /eq_slice /seq_le /=.
case: leqP=>I /=; last by rewrite itv_swapped_bnd //.
rewrite (@slice_split _ _ _ true (index t2 s)) /=; last first.
- by rewrite in_itv /= lexx andbT.
rewrite slice_kk /= onth_index /=; case: ifP=>/=; first by rewrite cats1.
rewrite cats0 => /negbT/memNindex->.
by apply: itv_overR=>/=; rewrite addn0.
Qed.

Lemma eqsl_xoL t1 t2 s :
        &=s `[t1, t2[ = if t1 <[s] t2
                          then t1 :: &=s `]t1, t2[
                          else [::].
Proof.
rewrite /eq_slice /seq_lt /=.
case: ltnP=>I; last by rewrite itv_swapped_bnd.
rewrite (@slice_split _ _ _ false (index t1 s)) /=; last first.
- by rewrite in_itv /= lexx.
rewrite slice_kk /= onth_index; case: ifP=>//= /negbT/memNindex E.
by move: I; rewrite E ltnNge index_size.
Qed.

Lemma eqsl_oxR t1 t2 s :
        &=s `]t1, t2] = if t1 <[s] t2 then
                          if t2 \in s
                            then rcons (&=s `]t1, t2[) t2
                            else &=s `]t1, +oo[
                          else [::].
Proof.
rewrite /eq_slice /seq_lt /=.
case: ltnP=>I; last by rewrite itv_swapped_bnd.
rewrite (@slice_split _ _ _ true (index t2 s)) /=; last first.
- by rewrite in_itv /= lexx andbT.
rewrite slice_kk /= onth_index /=; case: ifP=>/=; first by rewrite cats1.
rewrite cats0 =>/negbT/memNindex->.
by apply: itv_overR=>/=; rewrite addn0.
Qed.

(* some simplifying equalities on intervals *)

Lemma eqsl_uL_notinE s b t :
        t \notin s ->
        &=s `(Interval -oo (BSide b t)) = s.
Proof.
move=>N; rewrite /eq_slice /= itv_overR /=; first by exact: slice_uu.
by rewrite (memNindex N); exact: leq_addr.
Qed.

Lemma eqsl_uR_notinE s b t :
        t \notin s ->
        &=s `(Interval (BSide b t) +oo) = [::].
Proof.
move=>N; rewrite /eq_slice /= itv_overL //=.
by rewrite (memNindex N); exact: leq_addr.
Qed.

(* eqslive of nil *)
Lemma eqslice0 i :
        &=([::] : seq A) i = [::].
Proof. by rewrite /eq_slice slice0. Qed.

(* concat *)
(* TODO unify *)

Lemma eqsl_uL_catE s1 s2 b t :
        &= (s1 ++ s2) (Interval -oo (BSide b t)) =
        if t \in s1 then &= s1 (Interval -oo (BSide b t))
                    else s1 ++ &= s2 (Interval -oo (BSide b t)).
Proof.
rewrite /eq_slice slice_cat /= index_cat; case: ifP=>H1.
- by rewrite index_mem H1 itv_minfR cats0.
rewrite ltnNge leq_addr /= addnC addnK itv_overR /=; first by rewrite slice_uu.
by rewrite -addnA addnCA; exact: leq_addr.
Qed.

Lemma eqsl_uR_catE s1 s2 b t :
        &= (s1 ++ s2) (Interval (BSide b t) +oo) =
        if t \in s1 then &= s1 (Interval (BSide b t) +oo) ++ s2
                    else &= s2 (Interval (BSide b t) +oo).
Proof.
rewrite /eq_slice slice_cat /= index_cat; case: ifP=>H1.
- by rewrite index_mem H1 slice_uu.
rewrite ltnNge leq_addr /= addnC addnK itv_overL //=.
by rewrite -addnA addnCA; exact: leq_addr.
Qed.

Lemma eqsl_catE s1 s2 b1 t1 b2 t2 :
        &= (s1 ++ s2) (Interval (BSide b1 t1) (BSide b2 t2)) =
        if t1 \in s1
          then if t2 \in s1
                 then &= s1 (Interval (BSide b1 t1) (BSide b2 t2))
                 else &= s1 (Interval (BSide b1 t1) +oo) ++ &= s2 (Interval -oo (BSide b2 t2))
          else if t2 \in s1
                 then [::]
                 else &= s2 (Interval (BSide b1 t1) (BSide b2 t2)).
Proof.
rewrite /eq_slice slice_cat /= !index_cat.
case/boolP: (t1 \in s1)=>H1; case/boolP: (t2 \in s1)=>H2.
- by rewrite !index_mem H1 H2 itv_minfR cats0.
- rewrite index_mem H1 ltnNge leq_addr /= itv_overR /=; last by rewrite -addnA; exact: leq_addr.
  by congr (_ ++ _); rewrite addnC addnK.
- by rewrite ltnNge leq_addr /= index_mem H2 itv_minfR cats0 itv_overL //= -addnA; exact: leq_addr.
rewrite !ltnNge !leq_addr /= itv_overL /=; last by rewrite -addnA; exact: leq_addr.
by do 2!rewrite addnC addnK.
Qed.

(* cons lemmas *)
(* TODO unify *)

Lemma eqsl_uL_consE s b k t :
         &=(k :: s) (Interval -oo (BSide b t)) =
         if t == k then
           if b
             then [::]
             else [::k]
           else k :: &=s (Interval -oo (BSide b t)).
Proof.
rewrite -cat1s eqsl_uL_catE /= inE; case: eqVneq=>// {t}->.
by rewrite /eq_slice /= eqxx; case: b.
Qed.

Corollary eqsl_uL_consL s b t :
            &=(t :: s) (Interval -oo (BSide b t)) =
            if b then [::] else [::t].
Proof. by rewrite eqsl_uL_consE eqxx. Qed.

Lemma eqsl1_uL (k : A) b t :
        &=[::k] (Interval -oo (BSide b t)) =
        if ~~ b || (t!=k) then [::k] else [::].
Proof.
rewrite eqsl_uL_consE; case: eqVneq=>_.
- by rewrite orbF; case: b.
by rewrite orbT eqslice0.
Qed.

Lemma eqsl_uR_consE s b k t :
         &=(k :: s) (Interval (BSide b t) +oo) =
         if t == k then
           if b
             then k::s
             else s
           else &=s (Interval (BSide b t) +oo).
Proof.
rewrite -cat1s eqsl_uR_catE /= inE; case: eqVneq=>// {t}->.
by rewrite /eq_slice /= eqxx; case: b.
Qed.

Corollary eqsl_uR_consL s b t :
            &=(t :: s) (Interval (BSide b t) +oo) = if b then t::s else s.
Proof. by rewrite eqsl_uR_consE eqxx. Qed.

Lemma eqsl1_uR (k : A) b t :
        &=[::k] (Interval (BSide b t) +oo) =
        if b && (t==k) then [::k] else [::].
Proof.
rewrite eqsl_uR_consE; case: eqVneq=>_; first by rewrite andbT.
by rewrite eqslice0 andbF.
Qed.

Lemma eqsl_consE s k b1 t1 b2 t2 :
         &=(k :: s) (Interval (BSide b1 t1) (BSide b2 t2)) =
         if t1 == k then
           if t2 == k
             then if b1 && ~~ b2 then [::k] else [::]
             else if b1 then k :: &=s (Interval -oo (BSide b2 t2))
                        else &=s (Interval -oo (BSide b2 t2))
           else if t2 == k
                  then [::]
                  else &=s (Interval (BSide b1 t1) (BSide b2 t2)).
Proof.
rewrite -cat1s eqsl_catE /= !inE.
case: eqVneq=>[{t1}->|N1]; case: eqVneq=>[E2|N2] //=.
- by rewrite /eq_slice /= E2 eqxx; case: b1; case: b2.
by rewrite /eq_slice /= eqxx; case: b1.
Qed.

(* rcons lemmas *)

Lemma eqsl_uL_rconsE s b k t :
         &=(rcons s k) (Interval -oo (BSide b t)) =
         if t \in s
           then &=s (Interval -oo (BSide b t))
           else if ~~ b || (t!=k) then rcons s k else s.
Proof.
rewrite -cats1 eqsl_uL_catE /=; case: ifP=>//= _.
by rewrite eqsl1_uL; case: ifP=>_ //; rewrite cats0.
Qed.

Lemma eqsl_uR_rconsE s b k t :
         &=(rcons s k) (Interval (BSide b t) +oo) =
         if t \in s
           then rcons (&=s (Interval (BSide b t) +oo)) k
           else if b && (t == k) then [:: k] else [::].
Proof.
rewrite -cats1 eqsl_uR_catE /=; case: ifP=>//= _.
- by rewrite cats1.
by rewrite eqsl1_uR.
Qed.

Lemma eqsl_rconsE s k b1 t1 b2 t2 :
         &=(rcons s k) (Interval (BSide b1 t1) (BSide b2 t2)) =
         if t1 \in s then
           if t2 \in s
             then &=s (Interval (BSide b1 t1) (BSide b2 t2))
             else if b2 && (k==t2)
                    then &=s (Interval (BSide b1 t1) +oo)
                    else rcons (&=s (Interval (BSide b1 t1) +oo)) k
           else if t2 \in s
                  then [::]
                  else if [&& b1, k==t1 & (k==t2) ==> ~~b2]
                         then [::k] else [::].
Proof.
rewrite -cats1 eqsl_catE.
case/boolP: (t1 \in s)=>H1; case/boolP: (t2 \in s)=>H2 //.
- rewrite /eq_slice /=; case: eqVneq; case B2: b2=>/= _; try by rewrite cats1.
  by rewrite cats0.
by rewrite /eq_slice /=; case: eqVneq=>_; case: eqVneq=>_; case: b1; case: b2.
Qed.

(* test surgery lemmas *)

Lemma eqsl_uo_split t (s1 s2 : seq A) :
        t \notin s1 ->
        &=(s1++t::s2) `]-oo, t[ = s1.
Proof.
by move=>X1; rewrite eqsl_uL_catE (negbTE X1) eqsl_uL_consE eqxx cats0.
Qed.

Lemma eqsl_ou_split t (s1 s2 : seq A) :
        t \notin s1 ->
        &=(s1++t::s2) `]t, +oo[ = s2.
Proof.
by move=>X1; rewrite eqsl_uR_catE (negbTE X1) eqsl_uR_consE eqxx.
Qed.

Lemma eqsl_oo_split t1 t2 (s1 s2 s : seq A) :
        t1 != t2 ->
        t1 \notin s1 ->
        t2 \notin s1 ->
        t2 \notin s ->
        &=(s1++t1::s++t2::s2) `]t1, t2[ = s.
Proof.
move=>N X1 X21 X2.
rewrite eqsl_catE -cat_cons eqsl_uL_catE eqsl_catE /=
  eqsl_consE !eqsl_uL_consE eqsl_uR_consE /= !inE !eqxx /= !cats0.
by rewrite (negbTE X1) (negbTE X21) eq_sym (negbTE N) /= (negbTE X2).
Qed.

Corollary eqsl_oo_nil_split t1 t2 (s s2 : seq A) :
            t1 != t2 ->
            t2 \notin s ->
            &=(t1::s++t2::s2) `]t1, t2[ = s.
Proof.
move=>N X2.
by rewrite -(cat0s (_ :: _ ++ _)); apply: eqsl_oo_split.
Qed.

Corollary eqsl_oo_split_consec t1 t2 (s1 s2 : seq A) :
            t1 != t2 ->
            t1 \notin s1 -> t2 \notin s1 ->
            &=(s1++t1::t2::s2) `]t1, t2[ = [::].
Proof.
move=>N X1 X2.
by rewrite -(cat1s t1); apply: (@eqsl_oo_split _ _ _ _ [::]).
Qed.

Corollary eqsl_oo_nil_split_consec t1 t2 s :
            t1 != t2 ->
            &=(t1::t2::s) `]t1, t2[ = [::].
Proof.
move=>N.
by rewrite -(cat0s (_ :: _ :: _)); apply: eqsl_oo_split_consec.
Qed.

(* intervals and filter *)

(* TODO unify / better theory *)
Lemma eqsl_filterL (p : pred A) b (y : A) s :
        (y \notin s) || p y ->
        &= (filter p s) (Interval -oo (BSide b y)) = filter p (&= s (Interval -oo (BSide b y))).
Proof.
case/orP=>Hy.
- rewrite !eqsl_notinR //=; first by rewrite !eqsl_uu.
  by apply: contra Hy; rewrite mem_filter; case/andP.
elim: s=>//= h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH eqsl_uL_consE; case: eqVneq=>[E|_] /=.
  - by rewrite -E Hy in Hp.
  by rewrite (negbTE Hp).
rewrite !eqsl_uL_consE; case: eqVneq=>_ /=.
- by case: {IH}b=>//=; rewrite Hp.
by rewrite Hp IH.
Qed.

Lemma eqsl_filterR (p : pred A) b (x : A) s :
        (x \notin s) || p x ->
        &= (filter p s) (Interval (BSide b x) +oo) = filter p (&= s (Interval (BSide b x) +oo)).
Proof.
case/orP=>Hx.
- by rewrite !eqsl_notinL //= mem_filter negb_and Hx orbT.
elim: s=>//=h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH eqsl_uR_consE; case: eqVneq=>[E|_] //=.
  by rewrite -E Hx in Hp.
rewrite !eqsl_uR_consE; case: eqVneq=>//= _.
by case: {IH}b=>//=; rewrite Hp.
Qed.

Lemma eqsl_filter (p : pred A) b1 t1 b2 t2 s :
        (t1 \notin s) || (p t1 && ((t2 \notin s) || p t2)) ->
        &= (filter p s) (Interval (BSide b1 t1) (BSide b2 t2)) =
        filter p (&= s (Interval (BSide b1 t1) (BSide b2 t2))).
Proof.
case/orP=>[N1|/andP [H1]].
- by rewrite !eqsl_notinL //= mem_filter negb_and N1 orbT.
case/orP=>H2.
- rewrite !eqsl_notinR //=.
  - by rewrite eqsl_filterR // H1 orbT.
  by rewrite mem_filter negb_and H2 orbT.
elim: s=>//= h s IH.
case/boolP: (p h)=>/= Hp; last first.
- rewrite {}IH eqsl_consE; case: eqVneq=>[E1|_].
  - by rewrite -E1 H1 in Hp.
  case: eqVneq=>[E2|_] //.
  by rewrite -E2 H2 in Hp.
rewrite !eqsl_consE; case: eqVneq=>/=_; case: eqVneq=>//=_.
- by case: ifP=>//= _; rewrite Hp.
rewrite eqsl_filterL; last by rewrite H2 orbT.
by case: ifP=>//= _; rewrite Hp.
Qed.

Lemma eqslice_uniq s i :
        uniq s -> uniq (&=s i).
Proof.
rewrite /eq_slice; apply: slice_uniq.
Qed.

End Lemmas.

(* interaction with slicing *)

Section SliceSeqLe.
Variable (A : eqType).
Implicit Type (s : seq A).

(* TODO generalize / refactor to useq? *)
Lemma uniq_ux_filter s i :
        uniq s ->
        &=s `]-oo, i] = [seq x <- s | x <=[s] i].
Proof.
move=>U; rewrite /eq_slice /= /slice /= drop0 addn1.
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
        &=s `]-oo, i[ = [seq x <- s | x <[s] i].
Proof.
move=>U; rewrite /eq_slice /= /slice /= drop0 addn0.
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
        x <[k::s] t = x <=[k::s] (last k (&=s `]-oo, t[)).
Proof.
elim: s k=>/= [|y s IH] k //=.
- rewrite slt_cons slt_nil sle_cons sle_nil andbT eqxx orbF.
  by move=>_ ->.
rewrite inE negb_or -andbA; case/and4P=>Nky K Y U Nkt.
rewrite slt_cons sle_cons Nkt /=; case: (eqVneq x k)=>//= Nkx.
rewrite eqsl_uL_consE; case: (eqVneq t y)=>/= [E|Nty].
- by rewrite eqxx /= E; apply/negbTE/sltR.
suff -> /= : last y (&=s `]-oo, t[) != k by rewrite IH //= Y.
apply: contraTneq (mem_last y (&=s `]-oo, t[))=> E.
rewrite inE E negb_or Nky /=; apply: contra K.
by exact: slice_subset_full.
Qed.

(* a slight variation to add the cons to last *)
Corollary olt_ole_last' k s x t :
            uniq (k::s) -> t != k ->
            x <[k::s] t = x <=[k::s] (last k (&=(k::s) `]-oo, t[)).
Proof. by move=>U K; rewrite olt_ole_last // eqsl_uL_consE (negbTE K). Qed.

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

Lemma eqslice_mem (i : interval A) (ks : seq A) (k : A) :
        uniq ks ->
        k \in &=ks i =
        (k \in ks) && (index k ks \in ix_itv ks i).
Proof.
rewrite /eq_slice /= slice_memE => U.
rewrite indexall_uniq //.
by case: (k \in ks)=>//=; rewrite orbF.
Qed.

(* corollaries *)
Lemma mem_oo t1 t2 (ks : seq A) (k : A) :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <[ks] k & k <[ks] t2])
                (k \in &=ks `]t1, t2[).
Proof. by move=>U; rewrite eqslice_mem // in_itv; apply: and3P. Qed.

Lemma mem_xo t1 t2 (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <=[ks] k & k <[ks] t2])
                (k \in &=ks `[t1, t2[).
Proof. by move=>U; rewrite eqslice_mem // in_itv; apply: and3P. Qed.

Lemma mem_ox t1 t2 (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <[ks] k & k <=[ks] t2])
                (k \in &=ks `]t1, t2]).
Proof. by move=>U; rewrite eqslice_mem // in_itv; apply: and3P. Qed.

Lemma mem_xx t1 t2 (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks, t1 <=[ks] k & k <=[ks] t2])
                (k \in &=ks `[t1, t2]).
Proof. by move=>U; rewrite eqslice_mem // in_itv; apply: and3P. Qed.

Lemma mem_uo t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & k <[ks] t])(k \in &=ks `]-oo, t[).
Proof. by move=>U; rewrite eqslice_mem // in_itv; apply: andP. Qed.

Lemma mem_ux t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & k <=[ks] t])(k \in &=ks `]-oo, t]).
Proof. by move=>U; rewrite eqslice_mem // in_itv; apply: andP. Qed.

Lemma mem_ou t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & t <[ks] k])(k \in &=ks `]t, +oo[).
Proof. by move=>U; rewrite eqslice_mem // in_itv /= andbT; apply: andP. Qed.

Lemma mem_xu t (ks : seq A) k :
        uniq ks ->
        reflect ([/\ k \in ks & t <=[ks] k])(k \in &=ks `[t, +oo[).
Proof. by move=>U; rewrite eqslice_mem // in_itv /= andbT; apply: andP. Qed.

(* has predT lemmas *)

Lemma has_predT_uslice (ks : seq A) i :
        uniq ks ->
        has predT (&=ks i) = has (fun z => index z ks \in ix_itv ks i) ks.
Proof.
move=>U; apply/hasP/hasP; case=>x.
- by rewrite eqslice_mem // =>/andP [Hx Hi] _; exists x.
by move=>Hx Hi; exists x=>//; rewrite eqslice_mem // Hx.
Qed.

(* corollaries *)
Lemma has_oo t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]t1, t2[) = has (fun z => t1 <[ks] z && z <[ks] t2) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv. Qed.

Lemma has_ox t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]t1, t2]) = has (fun z => t1 <[ks] z && z <=[ks] t2) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv. Qed.

Lemma has_xo t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `[t1, t2[) = has (fun z => t1 <=[ks] z && z <[ks] t2) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv. Qed.

Lemma has_xx t1 t2 (ks : seq A) :
        uniq ks ->
        has predT (&=ks `[t1, t2]) = has (fun z => t1 <=[ks] z && z <=[ks] t2) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv. Qed.

Lemma has_ou t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]t, +oo[) = has (fun z => t <[ks] z) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv /= andbT. Qed.

Lemma has_xu t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `[t, +oo[) = has (fun z => t <=[ks] z) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv /= andbT. Qed.

Lemma has_uo t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]-oo, t[) = has (fun z => z <[ks] t) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv. Qed.

Lemma has_ux t (ks : seq A) :
        uniq ks ->
        has predT (&=ks `]-oo, t]) = has (fun z => z <=[ks] t) ks.
Proof. by move/has_predT_uslice=>->; apply: eq_has=>z; rewrite in_itv. Qed.

(* negation of has on the left side *)

Lemma hasNL_oo (ks : seq A) t1 t2 (p : pred A) :
        uniq ks -> t1 <[ks] t2 ->
        ~~ has p (&=ks `]t1, t2[) ->
        {in ks, forall z, p z -> z <[ks] t2 = z <=[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -!sleNgt; case/orP=>Hz.
- by rewrite Hz; apply: (sle_slt_trans Hz).
rewrite sltNge Hz sleNgt; congr negb; apply/esym.
by apply: (slt_sle_trans T).
Qed.

Lemma hasNL_ox (ks : seq A) t1 t2 (p : pred A) :
        uniq ks -> t1 <=[ks] t2 ->
        ~~ has p (&=ks `]t1, t2]) ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <=[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -sleNgt -sltNge; case/orP=>Hz.
- by rewrite Hz; apply: (sle_trans Hz).
rewrite !sleNgt Hz; congr negb; apply/esym.
by apply: (sle_slt_trans T).
Qed.

Lemma hasNL_xo (ks : seq A) t1 t2 (p : pred A) :
       uniq ks -> t1 <=[ks] t2 ->
       ~~ has p (&=ks `[t1, t2[) ->
       {in ks, forall z, p z -> z <[ks] t2 = z <[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -sltNge -sleNgt; case/orP=>Hz.
- by rewrite Hz; apply: (slt_sle_trans Hz).
rewrite !sltNge Hz; congr negb; apply/esym.
by apply: (sle_trans T).
Qed.

Lemma hasNL_xx (ks : seq A) t1 t2 (p : pred A) :
        uniq ks -> t1 <=[ks] t2 ->
        ~~ has p (&=ks `[t1, t2]) ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <[ks] t1}.
Proof.
move=>U T /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= =>/contraL/(_ P).
rewrite negb_and -!sltNge; case/orP=>Hz.
- by rewrite Hz; apply/sltW/(slt_sle_trans Hz).
rewrite sltNge sleNgt Hz; congr negb; apply/esym.
by apply/sltW/(sle_slt_trans T).
Qed.

Lemma hasNL_ou (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `]t, +oo[) -> {in ks, forall z, p z -> z <=[ks] t}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= andbT =>/contraL/(_ P).
by rewrite -sleNgt.
Qed.

Lemma hasNL_xu (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `[t, +oo[) -> {in ks, forall z, p z -> z <[ks] t}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= andbT =>/contraL/(_ P).
by rewrite -sltNge.
Qed.

Lemma hasNL_uo (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `]-oo, t[) -> {in ks, forall z, p z -> t <=[ks] z}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= =>/contraL/(_ P).
by rewrite -sleNgt.
Qed.

Lemma hasNL_ux (ks : seq A) t (p : pred A) :
        uniq ks ->
        ~~ has p (&=ks `]-oo, t]) -> {in ks, forall z, p z -> t <[ks] z}.
Proof.
move=>U /hasPn H z K P.
move: (H z); rewrite eqslice_mem // in_itv K /= =>/contraL/(_ P).
by rewrite -sltNge.
Qed.

(* negation of has on the right side *)

Lemma hasNR_oo (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <[ks] t2 = z <=[ks] t1} ->
        ~~ has p (&=ks `]t1, t2[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /=.
case/and3P=>H1 H2 H3; apply: contraL H2=>P; rewrite -sleNgt.
by rewrite -(T _ H1 P).
Qed.

Lemma hasNR_ox (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <=[ks] t1} ->
        ~~ has p (&=ks `]t1, t2]).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /=.
case/and3P=>H1 H2 H3; apply: contraL H2=>P; rewrite -sleNgt.
by rewrite -(T _ H1 P).
Qed.

Lemma hasNR_xo (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <[ks] t2 = z <[ks] t1} ->
        ~~ has p (&=ks `[t1, t2[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /=.
case/and3P=>H1 H2 H3; apply: contraL H2=>P; rewrite -sltNge.
by rewrite -(T _ H1 P).
Qed.

Lemma hasNR_xx (ks : seq A) t1 t2 (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <=[ks] t2 = z <[ks] t1} ->
        ~~ has p (&=ks `[t1, t2]).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /=.
case/and3P=>H1 H2 H3; apply: contraL H2=>P; rewrite -sltNge.
by rewrite -(T _ H1 P).
Qed.

Lemma hasNR_ou (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <=[ks] t} ->
        ~~ has p (&=ks `]t, +oo[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /= andbT.
case/andP=>H1 H2; apply: contraL H2=>P; rewrite -sleNgt.
by apply: T.
Qed.

Lemma hasNR_xu (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> z <[ks] t} ->
        ~~ has p (&=ks `[t, +oo[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /= andbT.
case/andP=>H1 H2; apply: contraL H2=>P; rewrite -sltNge.
by apply: T.
Qed.

Lemma hasNR_uo (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> t <=[ks] z} ->
        ~~ has p (&=ks `]-oo, t[).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /=.
case/andP=>H1 H2; apply: contraL H2=>P; rewrite -sleNgt.
by apply: T.
Qed.

Lemma hasNR_ux (ks : seq A) t (p : pred A) :
        uniq ks ->
        {in ks, forall z, p z -> t <[ks] z} ->
        ~~ has p (&=ks `]-oo, t]).
Proof.
move=>U T; apply/hasPn=>z; rewrite eqslice_mem // in_itv /=.
case/andP=>H1 H2; apply: contraL H2=>P; rewrite -sltNge.
by apply: T.
Qed.

End SliceSeqLe.


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

(* TODO: `uniq ks` should probably be added here *)
Definition consec ks t1 t2 :=
  [&& t1 <[ks] t2 & nilp (&=ks `]t1, t2[)].

(* several alternative formulations *)
Lemma consecP ks t1 t2 :
        reflect (t1 <[ks] t2 /\ ~~ has predT (&=ks `]t1, t2[))
                (consec ks t1 t2).
Proof.
apply: (iffP andP); case=>-> H; split=>//.
- by rewrite -nilp_hasPn.
by rewrite nilp_hasPn.
Qed.

Lemma consecP_inlt (ks : seq A) t1 t2 :
        uniq ks ->
        reflect ([/\ t1 \in ks & {in ks, forall z, z <[ks] t2 = z <=[ks] t1}])
                (consec ks t1 t2).
Proof.
move=>U; apply: (iffP (consecP ks t1 t2)); case=>H1 H2; split.
- by apply: slt_memE H1.
- by move=>z Z; apply: (hasNL_oo U H1 H2 Z).
- by rewrite H2 // sle_refl.
by apply: (hasNR_oo U)=>z /H2.
Qed.

Lemma consecP_ingt (ks : seq A) t1 t2 :
        uniq ks ->
        reflect ([/\ t1 \in ks & {in ks, forall z, t2 <=[ks] z = t1 <[ks] z}])
                (consec ks t1 t2).
Proof.
move=>U; apply (iffP (consecP_inlt t1 t2 U)); case=>H1 H2;
  split=>// z /H2 E.
- by rewrite sleNgt E sltNge.
by rewrite sltNge E sleNgt.
Qed.

(* frequent projections *)

Lemma consec_slt ks t1 t2 : consec ks t1 t2 -> t1 <[ks] t2.
Proof. by case/andP. Qed.

Lemma consec_sltW ks t1 t2 : consec ks t1 t2 -> t1 <=[ks] t2.
Proof. by move/consec_slt/sltW. Qed.

Lemma consec_mem ks t1 t2 : consec ks t1 t2 -> t1 \in ks.
Proof. by case/andP=>/slt_memE. Qed.

Lemma consec_oo ks t1 t2 : consec ks t1 t2 -> &=ks `]t1, t2[ = [::].
Proof. by case/consecP=>_; rewrite -nilp_hasPn=>/nilP. Qed.

Lemma consec_in (ks : seq A) t1 t2 :
        uniq ks ->
        consec ks t1 t2 -> {in ks, forall z, z <[ks] t2 = z <=[ks] t1}.
Proof. by move=>U; case/(consecP_inlt _ _ U). Qed.

(* and some streamlining *)

Lemma consec_prev (ks : seq A) x y z :
        uniq ks ->
        consec ks x y -> z <[ks] y -> z <=[ks] x.
Proof. by move=>U; case/(consecP_inlt _ _ U)=>X E N; rewrite -E // (slt_memE N). Qed.

Lemma consec_prevN (ks : seq A) x y z :
        uniq ks ->
        z != x -> consec ks x y -> z <[ks] y -> z <[ks] x.
Proof.
move=>U N C /(consec_prev U C).
by rewrite sle_eqVlt; [rewrite (negbTE N) | rewrite (consec_mem C) orbT].
Qed.

Lemma consec_next (ks : seq A) x y z :
        uniq ks ->
        consec ks x y -> x <[ks] z -> y <=[ks] z.
Proof.
move=>U; case/(consecP_ingt _ _ U)=>X E N; case Dz : (z \in ks); first by rewrite E.
by apply: sle_memI; rewrite Dz.
Qed.

Lemma consec_nextN (ks : seq A) x y z :
        uniq ks ->
        y \in ks \/ z \in ks ->
        y != z -> consec ks x y -> x <[ks] z -> y <[ks] z.
Proof.
move=>U /orP D N C /(consec_next U C).
by rewrite (sle_eqVlt D) (negbTE N).
Qed.

(* main splitting properties of consec *)

(* if t2 \in ks then ks splits *)
Lemma consecP_split (ks : seq A) t1 t2 :
        uniq ks ->
        t2 \in ks ->
        reflect (exists xs1 xs2, ks = xs1++t1::t2::xs2)
                (consec ks t1 t2).
Proof.
move=>U T2; apply: (iffP idP).
- case/andP=>+ H; case/slt_splitL=>xs1 [xs2][E] N T1 T2'.
  rewrite {ks}E mem_cat /= inE (negbTE T2') eq_sym (negbTE N)  /= in U T2 H *.
  case/in_split: T2=>ks3 [ks4][E T2'']; rewrite {xs2}E in U H *.
  by rewrite eqsl_oo_split // in H; move/nilP: H=>->; exists xs1, ks4.
case=>xs1 [xs2] E; move: U; rewrite {ks}E in T2 *.
rewrite cat_uniq /= inE !negb_or -!andbA (eq_sym t1 t2).
case/and8P=>U1 U2 U3 U4 U5 U6 U7 U8.
by rewrite /consec slt_splitR // eqsl_oo_split_consec=>//; rewrite eq_sym.
Qed.

(* if t2 \notin ks, then t1 is last *)
Lemma consec_last (ks : seq A) t1 t2 :
        uniq ks ->
        consec ks t1 t2 ->
        t2 \notin ks <-> exists ks', ks = rcons ks' t1.
Proof.
move=>U /andP [T]; rewrite nilp_hasPn => /hasPn H.
case: (lastP ks) U H T=>[|xs x] //= {ks} + H.
rewrite rcons_uniq slt_rcons mem_rcons inE negb_or !(eq_sym x).
case/andP=>Nx Ux; case: ifP=>X; rewrite ?andbF ?andbT.
- move=>Nt; split=>//; case=>ks' /rcons_inj [??]; subst ks' x.
  by rewrite (slt_memE Nt) in Nx.
move/contra: (H x)=>/(_ erefl).
rewrite eqslice_mem /=; last by rewrite rcons_uniq Nx.
rewrite mem_rcons inE eqxx /= in_itv /= negb_and ltEnat /=
  -!sleNgt !sle_rcons (negbTE Nx) X /= eqxx /= orbF andbT (eq_sym x).
case/orP=>[/negbTE->|/eqP->] /=.
- by case/andP=>H1 /eqP->; split=>// _; exists xs.
rewrite eqxx /= orbF => H1; split=>//; case=>ks' /rcons_inj [_ Ex].
by rewrite Ex H1 in Nx.
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
move=>U T2; apply: (iffP idP).
- by move/consec_last: T2; apply.
case=>xs E; rewrite E /consec rcons_uniq mem_rcons inE negb_or eq_sym in U T2 *.
case/andP: U T2=>T1 U /andP [N T2].
rewrite slt_rcons (negbTE T2) (negbTE T1) N eq_refl /= nilp_hasPn.
rewrite -all_predC; apply/allP=>x /=; apply: contraTeq=>_.
rewrite eqslice_mem; last by rewrite rcons_uniq T1.
rewrite mem_rcons inE in_itv /= ltEnat /= !negb_and negb_or -!sleNgt !sle_rcons
  (eq_sym x) eqxx orbF T1 (negbTE T2) (negbTE N) /= andbC orbCA orbb.
case: ifP=>/= _; last by rewrite orbN.
by rewrite orbF sleNgt; apply: contra T1; exact: slt_memE.
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
        uniq ks ->
        consec (filter p ks) t1 t2 <->
        if p t2 then [/\ t1 <[ks] t2, p t1 & nilp (filter p (&=ks `]t1, t2[))]
                else [/\ t1 \in ks,   p t1 & nilp (filter p (&=ks `]t1, +oo[))].
Proof.
move=>U; case: ifP=>P2; split.
- case/consecP=>Cx Nx.
  move: (slt_memE Cx); rewrite mem_filter=>/andP [P1 K1].
  rewrite slt_filter ?(P1,P2,orbT) // in Cx.
  split=>//; rewrite nilp_hasPn; apply: contra Nx.
  case/hasP=>x; rewrite mem_filter; case/andP=>Px.
  move/(mem_oo _ _ _ U); case=>N1 N2 Kx _; apply/hasP; exists x=>//.
  apply/mem_oo; first by apply: filter_uniq.
  by rewrite mem_filter !slt_filter ?(P1,P2,Px,orbT).
- case=>N P1 Nx; apply/consecP; split.
  - by rewrite slt_filter ?(P1,P2,orbT).
  rewrite nilp_hasPn in Nx; apply: contra Nx.
  case/hasP=>x /(mem_oo _ _ _ (filter_uniq _ U)); rewrite mem_filter.
  case=>/andP [Px Kx] X1 X2 _.
  rewrite !slt_filter ?(P1,P2,Px,orbT) // in X1 X2.
  by apply/hasP; exists x=>//; rewrite mem_filter Px /=; apply/mem_oo.
- case/consecP=>Cx Nx.
  move: (slt_memE Cx); rewrite mem_filter=>/andP [P1 K1].
  split=>//; rewrite nilp_hasPn; apply: contra Nx.
  case/hasP=>x; rewrite mem_filter=>/andP [Px] /(mem_ou _ _ U) [Nx Kx] _.
  apply/hasP; exists x=>//; apply/mem_oo; first by apply: filter_uniq.
  rewrite mem_filter Px Nx; split=>//.
  - by rewrite slt_filter ?(P1,Px,orbT).
  by apply: slt_memI; rewrite mem_filter ?Px // P2.
case=>K1 P1 Nx; apply/consecP; split.
- apply: slt_memI; first by rewrite mem_filter P1 K1.
  by rewrite mem_filter P2.
rewrite nilp_hasPn in Nx; apply: contra Nx.
case/hasP=>x /(mem_oo _ _ _ (filter_uniq _ U)); rewrite mem_filter.
case=>/andP [Px Kx N1 N2] _.
apply/hasP; exists x=>//; rewrite mem_filter Px /=.
apply/mem_ou=>//; split=>//.
by rewrite slt_filter ?(P1,Px,orbT) in N1.
Qed.

Lemma consecP_filter ks (p : pred _) t1 t2 :
        uniq ks ->
        consec (filter p ks) t1 t2 <->
        if p t2
          then [/\ t1 <[ks] t2, p t1 & {in &=ks `]t1, t2[ , forall z, ~~ p z}]
          else [/\ t1 \in ks  , p t1 & {in &=ks `]t1, +oo[, forall z, ~~ p z}].
Proof.
move=>U; split=>[|H].
- by move/(consecP_nilp_filter _ _ _ U); case: ifP=>P [?? /nilp_filter].
by apply/consecP_nilp_filter; case: ifP H=>P [?? /nilp_filter].
Qed.

Lemma olt_consec_prev ks t1 t2 :
        uniq ks ->
        t1 <[ks] t2 <-> exists t, t1 <=[ks] t /\ consec ks t t2.
Proof.
move=>U; split=>[H|]; last first.
- by case=>t [H1] /consecP [H2 _]; apply: (sle_slt_trans H1 H2).
case/slt_splitL: H U=>ks1 [ks2][-> Nt1t2 N1 N2] /=.
rewrite cat_uniq /= negb_or /= -!andbA.
case/and5P=>Uks1 Nt1ks1 /hasPn Hks2 Nt1ks2 Uks2.
case X : (t2 \in ks2); last first.
- have L : last t1 ks2 \notin ks1.
  - move: (mem_last t1 ks2); rewrite inE.
    by case/orP=>[/eqP ->//|H]; apply: Hks2.
  exists (last t1 ks2); split.
  - by rewrite sle_cat (negbTE N1) sleL andbT.
  apply/andP; split.
  - rewrite slt_cat (negbTE N2) (negbTE L) /= slt_cons (eq_sym t2) Nt1t2 /=.
    move: (mem_last t1 ks2); rewrite inE=>/orP [->//|H].
    by rewrite slt_memI ?X ?orbT.
  rewrite nilp_hasPn; apply: contra L; case/hasP=>x + _; case/mem_oo.
  - rewrite cat_uniq /= negb_or Uks1 Uks2 Nt1ks1 Nt1ks2 /= andbT.
    by apply/hasPn.
  move=>_; rewrite !slt_cat (negbTE N2) !slt_cons (eq_sym t2) Nt1t2 /=.
  case Xks1 : (x \in ks1)=>/=; first by move/slt_memE.
  case/orP=>// /andP [Nxt1]; rewrite (negbTE Nxt1) /=.
  case/orP=>[/eqP/last_nochange|/[swap] Xp1].
  - by rewrite (negbTE Nt1ks2)=>/eqP ->.
  move: (@sle_last _ x t1 ks2)=>/(_ Uks2 (slt_memE Xp1)) Z.
  by move/(sle_slt_trans Z); apply: contraLR=>_; rewrite slt_irr.
case/splitP: {ks2} X Hks2 Nt1ks2 Uks2=>p1 p2 H2.
rewrite mem_cat cat_uniq /= negb_or rcons_uniq mem_rcons inE.
rewrite (negbTE Nt1t2) /= -!andbA.
case/andP=>Nt1p1 Nt1p2 /and4P [Nt2p1 Up1 /hasPn Hp2 Up2].
have L : last t1 p1 \notin ks1.
- move: (mem_last t1 p1); rewrite inE.
  case/orP=>[/eqP ->//|H]; apply: H2.
  by rewrite mem_cat mem_rcons inE H orbT.
exists (last t1 p1); split.
- by rewrite sle_cat (negbTE Nt1ks1) sleL andbT.
apply/andP; split.
- rewrite slt_cat (negbTE N2) (negbTE L) /= slt_cons (eq_sym t2) Nt1t2 /=.
  rewrite slt_cat mem_rcons inE eq_refl /= slt_rcons (negbTE Nt2p1) eq_refl /=.
  by move: (mem_last t1 p1); rewrite inE=>/orP [->|->] //=; rewrite orbT.
rewrite nilp_hasPn; apply: contra L; case/hasP=>x.
case/mem_oo.
- rewrite cat_uniq /= cat_uniq mem_cat !negb_or mem_rcons rcons_uniq
    negb_or Uks1 N1 Nt1t2 Nt1p1 Nt1p2 Nt2p1 Up1 Up2 /= andbT.
  by apply/andP; split; apply/hasPn.
move=>_; rewrite !slt_cat !slt_cons !slt_cat !mem_rcons !inE (negbTE N2)
  (eq_sym t2) Nt1t2 /= eqxx /=.
case Xks1 : (x \in ks1)=>/=; first by move/slt_memE.
case/orP=>// /andP [Nxt1]; rewrite (negbTE Nxt1) /=.
case/orP=>[/eqP/last_nochange|/[swap]].
- rewrite (negbTE Nt1p1)=>/eqP ->/=.
  by rewrite slt_cons eqxx.
rewrite slt_rcons (negbTE Nt2p1) eqxx /= orbF => Xp1.
rewrite Xp1 orbT slt_rcons Xp1 sltNge.
by move: (@sle_last _ x t1 p1)=>/(_ Up1 Xp1) ->.
Qed.

Lemma olt_consec_next ks t1 t2 :
        uniq ks ->
        t1 <[ks] t2 <-> exists t, consec ks t1 t /\ t <=[ks] t2.
Proof.
move=>U; split=>[H|]; last first.
- by case=>t [/consecP [X _] /(slt_sle_trans X)].
case/slt_splitL: H U=>ks1 [ks2][-> Nt1t2 N1 N2] /=.
rewrite cat_uniq /= negb_or -!andbA.
case/and5P=>Uks1 _ /hasPn Nks2 Nt1ks2 Uks2.
have H : head t2 ks2 \notin ks1.
- move: (mem_head t2 ks2); rewrite inE.
  by case/orP=>[/eqP ->//|]; apply: Nks2.
exists (head t2 ks2); split; last first.
- rewrite sle_cat (negbTE H) N2 /= sle_cons (eq_sym t2) Nt1t2 /=.
  by rewrite sle_head orbT.
apply/andP; split.
- rewrite slt_cat (negbTE H) (negbTE N1) /= sltL.
  case: eqP Nt1ks2 (mem_head t2 ks2)=>// -> X.
  by rewrite inE (negbTE Nt1t2) (negbTE X).
rewrite nilp_hasPn; apply: contra H.
case/hasP=>x; case/mem_oo.
- rewrite cat_uniq /= negb_or Uks1 N1 Nt1ks2 Uks2 /= andbT.
  by apply/hasPn.
move=>_; rewrite !slt_cat /= !slt_cons eqxx /= andbT (negbTE N1) /=.
case Xks1 : (x \in ks1)=>/=.
- by move/slt_memE=>E; rewrite E in N1.
move=>Nxt1; rewrite (negbTE Nxt1) /=; case: ifP=>// _.
case/andP=>_ /(sle_slt_trans (@sle_head _ t2 ks2 x))=>+ _.
by apply: contraLR=>_; rewrite slt_irr.
Qed.

(* previous element is uniquely determined *)
Lemma consec_prev_inj ks t t1 t2 :
         uniq ks ->
         consec ks t1 t ->
         consec ks t2 t ->
         t1 = t2.
Proof.
move=>U /andP [T1 +] /andP [T2]; rewrite !nilp_hasPn => /hasPn H1 /hasPn H2.
move: (@slt_total _ ks t1 t2 (slt_memE T1)).
case/or3P=>[/eqP->|L1|L2] //.
- move: (H1 t2)=>/contraL/(_ erefl); apply: contraNeq=>_.
  by apply/mem_oo=>//; split=>//; apply: slt_memE T2.
move: (H2 t1)=>/contraL/(_ erefl); apply: contraNeq=>_.
by apply/mem_oo=>//; split=>//; apply: slt_memE T1.
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
case/andP: C1 C2=>T1 + /andP [T2].
rewrite !nilp_hasPn => /hasPn H1 /hasPn H2.
move: (@slt_total _ ks t1 t2 K1); case/or3P=>[/eqP->|L1|L2] //.
- move: (H2 t1)=>/contraL/(_ erefl); apply: contraNeq=>_.
  by apply/mem_oo.
move: (H1 t2)=>/contraL/(_ erefl); apply: contraNeq=>_.
by apply/mem_oo.
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
        uniq ks ->
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT ks ->
        t2 \in ks ->
        consec ks t1 t2 ->
        {in ks, forall z, ltT z t2 = (z == t1) || ltT z t1}.
Proof.
move=>U I Asym T S T2 C; move: (consec_mem C)=>T1.
have {}Asym : antisymmetric (fun x y => (x == y) || ltT x y).
- move=>x y; rewrite (eq_sym y); case: eqP=>//= _.
  by apply: (Asym x y).
have {}T : transitive (fun x y => (x == y) || ltT x y).
- move=>x y z; case: eqP=>[->|/eqP _] //=.
  case: eqP=>[->->|/eqP _ /=]; first by rewrite orbT.
  by case: eqP=>//= _; apply: T.
have {}S : sorted (fun x y => (x == y) || ltT x y) ks.
- by apply: sub_sorted S=>x y ->; rewrite orbT.
move=>z Z; move/(consec_in U)/(_ z Z): C.
rewrite (slt_sorted_leE Asym T S) //.
rewrite (sle_sorted_leE Asym T S) //.
by rewrite !orbA orbb; case: eqP=>//= ->; rewrite I.
Qed.

Lemma consec_sorted_le (leT : rel A) ks t1 t2 :
        uniq ks ->
        {in ks, reflexive leT} ->
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        t2 \in ks ->
        consec ks t1 t2 ->
        {in ks, forall z, leT z t1 = (z != t2) && leT z t2}.
Proof.
move=>U R Asym T S T2 C; move: (consec_mem C)=>T1.
move=>z Z; move/(consec_in U)/(_ z Z): C.
rewrite (slt_sorted_leE Asym T S) //.
rewrite (sle_sorted_leE Asym T S) //.
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
- by rewrite sort_uniq.
- by apply: sort_sorted_in_lt.
- by rewrite mem_sort.
by rewrite mem_sort.
Qed.

Lemma consec_sort_le leT ks t1 t2 :
        uniq ks ->
        {in ks, reflexive leT} ->
        antisymmetric leT ->
        transitive leT ->
        {in ks &, total leT} ->
        t2 \in ks ->
        consec (sort leT ks) t1 t2 ->
        {in ks, forall z, leT z t1 = (z != t2) && leT z t2}.
Proof.
set ks' := sort _ _=>U R Asym T Tot T2 C z Z.
apply: (@consec_sorted_le leT ks')=>//.
- by rewrite sort_uniq.
- by move=>x; rewrite mem_sort; apply: R.
- by apply: sort_sorted_in Tot _ _.
- by rewrite mem_sort.
by rewrite mem_sort.
Qed.

(*******************************)
(* consec and cons constructor *)
(*******************************)

Lemma consec_hdswap k1 k2 ks x :
        uniq ks ->
        k1 \notin ks -> k2 \notin ks ->
        x != k2 ->
        consec (k1::ks) k1 x -> consec (k2::ks) k2 x.
Proof.
move=>U K1 K2 N2 C.
have N1 : x != k1 by move/consec_slt: C; rewrite sltL.
move: C; rewrite /consec !sltL N1 N2 /= !nilp_hasPn.
apply: contra=>/hasP [z Z] _; apply/hasP; exists z=>//.
case/mem_oo: Z; first by rewrite /= K2.
rewrite inE sltL slt_cons=>Z1 Nz /andP [_ Z2].
rewrite (negbTE Nz) /= in Z1 Z2.
apply/mem_oo; first by rewrite /= K1.
rewrite inE sltL slt_cons Z1 N1 Z2 /= orbT; split=>//.
by apply: contra K1 => /eqP <-.
Qed.

Lemma consec_hd2 k1 k2 ks :
  uniq ks ->
  k1 \notin ks -> k2 \notin ks ->
  k1 != k2 -> consec [:: k1, k2 & ks] k1 k2.
Proof.
move=>U K1 K2 N; rewrite /consec !sltL eq_sym N /= nilp_hasPn.
apply/hasPn=>z; apply: contraL=>/= _.
rewrite eqslice_mem; last first.
- by rewrite /= inE negb_or N K1 K2.
rewrite negb_and; apply/orP; right.
by rewrite in_itv /= (negbTE N) !eqxx /= negb_and ltEnat /= -!leqNgt leqn0 lt0n orbN.
Qed.

(* a useful lemma that collects the case analysis *)
(* for consec (k::ks) *)
Lemma consec_consEP' k k1 k2 ks :
        uniq ks ->
        k \notin ks ->
        consec (k::ks) k1 k2 <->
        if k1 == k then
          if k2 \in ks then ks = k2 :: behead ks
          else k2 != k /\ ks = [::]
        else k2 != k /\ consec ks k1 k2.
Proof.
move=>U N; split; last first.
- case: (k1 =P k)=>[->{k1}|/eqP Nk1k [Nk2]]; last first.
  - case/consecP=>H1; move=> H2; apply/consecP.
    rewrite slt_cons (negbTE Nk1k) /= H1 andbT; split=>//.
    apply: contra H2=>/hasP [x H2 _]; apply/hasP; exists x=>//.
    move: H2; case/mem_oo; first by rewrite /= N.
    rewrite !slt_cons inE (negbTE Nk1k) Nk2 /=; case: eqVneq=>//= _ Hx Hx1 Hx2.
    by apply/mem_oo.
  case K2 : (k2 \in ks).
  - move=>E; rewrite {K2}E /= in N U *.
    rewrite inE negb_or in N.
    case/andP: U=>U1 U2; case/andP: N=>N1 N2.
    by apply: consec_hd2.
  case=>Nk2k E; rewrite {ks N U K2}E.
  apply/consecP; rewrite sltL; split=>//.
  apply/hasPn=>x; apply: contraL=>_; apply: contra Nk2k.
  by case/mem_oo=>//; rewrite inE sltL => /eqP->; rewrite eqxx.
case: (k1 =P k)=>[->|/eqP Nk1k]; last first.
- move/consecP; rewrite slt_cons (negbTE Nk1k) /=.
  case=>/andP [Nk2k H1 H2]; split=>//; apply/consecP; split=>//.
  apply: contra H2=>/hasP [x] H _.
  apply/hasP; exists x=>//.
  case/mem_oo: H=>// Hx Hx1 Hx2.
  apply/mem_oo=>/=; first by rewrite N.
  rewrite inE !slt_cons (negbTE Nk1k) (negbTE Nk2k) /=.
  by case: eqVneq=>[E|_] //=; rewrite -E Hx in N.
case K2: (k2 \in ks)=>/consecP []; rewrite sltL => Nk2k; last first.
- move=>H; split=>//; apply/nilP; rewrite nilp_hasPn.
  apply: contra H=>/hasP [x X _]; apply/hasP; exists x=>//.
  apply/mem_oo; first by rewrite /= N.
  rewrite inE sltL slt_cons X Nk2k /= orbT.
  case: (x =P k)=>//= [E|_]; first by rewrite -E X in N.
  by split=>//; apply: slt_memI=>//; rewrite K2.
case: ks U N K2=>//= x ks; rewrite !inE negb_or.
case/andP=>Nkxs U /andP [Nkx Nks] K2 H; congr (_ :: _).
case/orP: K2=>[/eqP->|K2] //.
apply: contraNeq H=>?; apply/hasP; exists x=>//.
apply/mem_oo; first by rewrite /= inE negb_or Nkx Nks Nkxs.
rewrite sltL slt_cons sltL !inE eqxx /= orbT Nk2k /= (eq_sym x) (negbTE Nkx) /=.
by split=>//; rewrite eq_sym.
Qed.

Lemma consec_consEP k k1 k2 ks :
        uniq ks ->
        k \notin ks ->
        consec (k::ks) k1 k2 <->
        if k1 == k then
          if k2 \in ks then k2 = head k ks
          else k2 != k /\ ks = [::]
        else k2 != k /\ consec ks k1 k2.
Proof.
move=>U /(consec_consEP' _ _ U)=>->.
case: ifP=>// E1; case: ifP=>//.
by case: {U}ks=>//= x ks E2; split=>[[]|->].
Qed.

(* let's make them boolean *)
Lemma consec_consE' k k1 k2 ks :
        uniq ks ->
        k \notin ks ->
        consec (k::ks) k1 k2 =
        if k1 == k then
          if k2 \in ks then ks == k2 :: behead ks
          else (k2 != k) && (ks == [::])
        else (k2 != k) && consec ks k1 k2.
Proof.
move=>U K; rewrite iffE consec_consEP' //.
case: ifP=>H1; last by case: andP.
case: ifP=>H2; first by case: eqP.
by split; [case=>->->|case/andP=>-> /eqP].
Qed.

Lemma consec_consE k k1 k2 ks :
        uniq ks ->
        k \notin ks ->
        consec (k::ks) k1 k2 =
        if k1 == k then
          if k2 \in ks then k2 == head k ks
          else (k2 != k) && (ks == [::])
        else (k2 != k) && consec ks k1 k2.
Proof.
move=>U K; rewrite iffE consec_consEP //.
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
  - move/negbT: K2; rewrite negbK=>K2 /(consecP_inlt _ _ U) [K1 E].
    apply/consecP_inlt; first by rewrite rcons_uniq K.
    split; first by rewrite mem_rcons inE K1 orbT.
    move=>z; rewrite mem_rcons inE; case/orP=>[/eqP ->{z}|Z].
    - rewrite slt_rcons K2 sle_rcons (negbTE K) eq_refl andbT K1 /=.
      by apply/negP=>/slt_memE; rewrite (negbTE K).
    by rewrite slt_rcons K2 sle_rcons Z; apply: E.
  case=>->{k2 K2} [ks' E]; rewrite {ks}E in U K *.
  apply/consecP_inlt; first by rewrite rcons_uniq K.
  split.
  - by rewrite mem_rcons inE mem_rcons inE eq_refl orbT.
  rewrite rcons_uniq in U; case/andP: U=>N1 U.
  rewrite mem_rcons inE negb_or eq_sym N /= in K.
  move=>z; rewrite mem_rcons inE mem_rcons inE => Z.
  rewrite slt_rcons mem_rcons inE eq_sym (negbTE N) (negbTE K) /=.
  rewrite eq_refl orbF !sle_rcons N1 /= eq_refl orbF !mem_rcons !inE eq_refl /=.
  case: eqP Z=>[->{z} /= _|/eqP Nz /=].
  - by rewrite eq_sym (negbTE N) /=; case: ifP=>// K'; rewrite K' sle_memI.
  rewrite (eq_sym z); case: eqP=>[/= ->|/=]; first by rewrite sle_refl if_same.
  by move=>_ Z; rewrite Z sle_memI.
case/consecP_inlt; first by rewrite rcons_uniq K.
move=>+ E; rewrite mem_rcons inE=>K1.
case/orP: K1 E=>[/eqP ->{k1}|K1] E.
- rewrite eq_refl /=.
  move: (E k); rewrite mem_rcons inE eq_refl=>/(_ erefl).
  rewrite sle_refl; apply: contraL; rewrite mem_rcons inE.
  case/orP=>[/eqP ->|K2]; first by rewrite slt_irr.
  rewrite slt_rcons K2; apply/negP.
  by move/(slt_trans (slt_memI K2 K)); apply/negP; exact: slt_irr.
case: eqP K1 K=>[->->//|/eqP N K1 K /=]; case: ifP=>K2; last first.
- move/negbT: K2; rewrite negbK=>K2; apply/consecP_inlt=>//.
  split=>// z Z; move: (E z); rewrite mem_rcons inE Z orbT=>/(_ erefl).
  by rewrite slt_rcons K2 sle_rcons Z.
move: (E k); rewrite mem_rcons inE eq_refl=>/(_ erefl).
rewrite slt_rcons (negbTE K2) (negbTE K) /= eq_refl andbT.
rewrite sle_rcons (negbTE K) K1 /=; case: eqP=>// -> _; split=>//.
suff -> : k1 = last k1 ks.
- move: ks {E N U K K2} k1 K1; apply: last_ind=>[//|ks x IH] k1.
  rewrite mem_rcons inE; case/orP=>[/eqP ->|].
  - by rewrite last_rcons; exists ks.
  by case/IH=>ks' E; rewrite last_rcons; exists ks.
apply/eqP/contraT; rewrite eq_sym=>M; exfalso.
move: (last_change M)=>L.
move: (E (last k1 ks)); rewrite mem_rcons inE L orbT=>/(_ erefl).
rewrite slt_rcons sle_rcons (negbTE K2) L /=.
move/esym; rewrite sle_eqVlt; last by rewrite L.
rewrite (negbTE M) /=.
by move/(sle_slt_trans (sle_last k1 U K1)); apply/negP; exact: slt_irr.
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
        uniq ks ->
        k \notin ks -> x != k ->
        consec (k::ks) x y -> y != k /\ consec ks x y.
Proof. by move=>U K Nx /(consec_consEP _ _ U K); rewrite (negbTE Nx). Qed.

(* the following isn't a consequence of consec_consE *)
(* as it's independent of k \notin ks *)
(* TODO not anymore *)
Lemma consec_cons k ks x y :
        uniq ks -> k \notin ks ->
        x != k -> y != k -> consec ks x y -> consec (k::ks) x y.
Proof.
move=>U N Nx Ny; rewrite /consec slt_cons Ny (negbTE Nx) /=.
case/andP=>->/=; rewrite !nilp_hasPn; apply: contra.
case/hasP=>z Z _; apply/hasP; exists z=>//.
case/mem_oo: Z; first by rewrite /= N.
rewrite inE !slt_cons (negbTE Nx) Ny !(eq_sym z) /=.
case: eqVneq=>//= _ Hz Hxz Hzy.
by apply/mem_oo.
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
case/or3P: (slt_total a2 X1) Cx2 X2=>[/eqP <-{a2}|H|H] Cx2 X2.
- by rewrite (consec_next_inj U Y1 Cx1 Cx2) !eq_refl.
- by rewrite (consec_next U Cx1 H) !orbT.
by rewrite (consec_next U Cx2 H) !orbT.
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
  by rewrite /consec sltL eq_sym K1 (eqsl_oo_split_consec (s1:=[::])).
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
  apply: consec_cons=>//=.
  - by rewrite U1.
  - by rewrite inE negb_or K1.
  - by rewrite eq_sym.
  by apply: consec_hdswap C.
(* another useful side which holds only if k != t1 *)
have Nx1 : t1 != x.
- case: eqP U1=>// <-; move: (consec_mem C).
  by rewrite inE (negbTE Nt1k) /= =>->.
(* then the proof is straightforward *)
apply: Hstep; first by rewrite inE T2 orbT.
apply: consec_cons=>//=.
- by rewrite U1.
- by rewrite inE negb_or K1.
by apply: consec_cons=>//; case/consec_behead: C.
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
        uniq ks -> k1 <[ks] k2 ->
        P k1 ->
        (forall t1 t2,
           t2 \in &=ks `]k1, k2[ ->
           consec (&=ks `[k1, k2[) t1 t2 -> P t1 -> P t2) ->
        forall t, t \in &=ks `]k1,k2[ -> P t.
Proof.
move=>U N H0 IH t; apply: (consec_ind (k:=k1))=>//=.
- by rewrite eqslice_uniq // andbT eqslice_mem // negb_and in_itv /= ltxx /= orbT.
by move=>t1 t2 H C; apply: IH=>//; rewrite eqsl_xoL N.
Qed.

Lemma consec_indx ks k1 k2 (P : A -> Prop) :
        uniq ks -> k1 <=[ks] k2 -> k1 \in ks ->
        P k1 ->
        (forall t1 t2,
           t2 \in &=ks `]k1, k2] ->
           consec (&=ks `[k1, k2]) t1 t2 -> P t1 -> P t2) ->
        forall t, t \in &=ks `]k1, k2] -> P t.
Proof.
move=>U N K H0 IH t; apply: (consec_ind (k:=k1))=>//=.
 - by rewrite eqslice_uniq // andbT eqslice_mem //= negb_and in_itv /= ltxx /= orbT.
by move=>t1 t2 H C; apply: IH=>//; rewrite eqsl_xxL N /= K.
Qed.

Lemma consec_indu ks k (P : A -> Prop) :
        uniq ks -> k \in ks ->
        P k ->
        (forall t1 t2,
           t2 \in &=ks `]k, +oo[ ->
           consec (&=ks `[k, +oo[) t1 t2 -> P t1 -> P t2) ->
        forall t, t \in &=ks `]k, +oo[ -> P t.
Proof.
move=>U K H0 IH t; apply: (consec_ind (k:=k))=>//=.
- by rewrite eqslice_uniq // andbT eqslice_mem //= negb_and in_itv /= ltxx /= orbT.
by move=>t1 t2 H C; apply: IH=>//; rewrite eqsl_xuL K.
Qed.

End ConsecEq.

Section ConsecOrd.
Variable (A : ordType).
Implicit Type (ks : seq A).

(* consecutiveness and sortedness under A *)

Lemma consec_sorted ks t1 t2 :
        uniq ks ->
        sorted ord ks -> t2 \in ks -> consec ks t1 t2 ->
        {in ks, forall z, ord z t2 = oleq z t1}.
Proof.
move=>U S T2 /(consecP_inlt _ _ U) [T1 H] z Z.
rewrite -(slt_sortedE S Z T2) -(sle_sortedE S Z T1).
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
have U' : uniq (k :: ks) by rewrite /= N U.
have : k <[k::ks] x by rewrite sltL; case: eqP X N=>// ->->.
case/(olt_consec_prev _ _ U')=>t [_]; rewrite consec_consEP' //.
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
have : x <[rcons ks k] k by rewrite slt_rcons (negbTE N) eq_refl orbF.
case/(olt_consec_next _ _ Ur)=>t [].
rewrite consec_rconsEP' //.
case: eqP X N=>[->->//|/eqP Nkx X N /=].
case T: (t \in ks)=>/=; first by right; exists t.
by case=>-> {t T} [ks' -> _]; left; exists ks'.
Qed.

End ConsecNat.
