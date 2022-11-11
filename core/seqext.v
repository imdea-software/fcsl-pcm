From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq path eqtype choice.
From pcm Require Import options.

(*********************)
(* Extensions to seq *)
(*********************)

(* With A : Type, we have the In_split lemma. *)
(* With A : eqType, the lemma can be strenghtened to *)
(* not only return the split of xs, but the split of xs *)
(* that uses the first occurrence of x is xs *)
Lemma in_split (A : eqType) (xs : seq A) x :
        x \in xs -> exists xs1 xs2, xs = xs1 ++ x :: xs2 /\ x \notin xs1.
Proof.
rewrite -has_pred1; case/split_find=>_ s1 s2 /eqP ->.
by rewrite has_pred1=>H; exists s1, s2; rewrite -cats1 -catA.
Qed.

Lemma subset_nilR (A : eqType) (xs : seq A) :
        {subset xs <= [::]} -> xs = [::].
Proof. by case: xs=>// x xs /(_ x); rewrite inE eq_refl=>/(_ erefl). Qed.

Lemma subset_nil (A : eqType) (xs ys : seq A) :
        {subset xs <= ys} -> ys = [::] -> xs = [::].
Proof. by move=>X E; move: E X=>->; apply: subset_nilR. Qed.

Lemma all_mem (A : eqType) (s1 s2 : seq A) :
        reflect {subset s2 <= s1} (all [mem s1] s2).
Proof. by case: allP=>H; constructor; [move=>x /H | move=>X; apply: H=>x /X]. Qed.

Lemma all_predC_sym (A : eqType) (s1 s2 : seq A) :
        all [predC s1] s2 = all [predC s2] s1.
Proof. by rewrite all_predC has_sym -all_predC. Qed.

Lemma nilp_hasPn A (s : seq A) : nilp s = ~~ has predT s.
Proof. by case: s. Qed.

Lemma nilp_filter (A : eqType) (p : pred A) s :
        reflect {in s, forall z, ~~ p z} (nilp (filter p s)).
Proof.
case E : (nilp _); constructor.
- move: E; rewrite nilp_hasPn=>/hasPn H x Kx; apply/negP=>Px.
  by move: (H x); rewrite mem_filter Px=>/(_ Kx).
move=>X; move/negP: E; elim.
rewrite nilp_hasPn; apply/negP=>/hasP [x].
rewrite mem_filter=>/andP [Px Kx] _.
by move: (X x Kx); rewrite Px.
Qed.

Lemma index_rcons (A : eqType) (a x : A) xs :
        index a (rcons xs x) =
        if a \in xs then index a xs else
          if a == x then size xs else (size xs).+1.
Proof.
rewrite eq_sym; elim: xs=>[|y xs IH] //=.
rewrite inE eq_sym; case: eqP=>//= _.
by rewrite IH; case: ifP=>// _; case: eqP.
Qed.

Lemma index_memN (A : eqType) (x : A) xs :
        x \notin xs <-> index x xs = size xs.
Proof.
split; first by exact: memNindex.
by move=>E; rewrite -index_mem E ltnn.
Qed.

Corollary index_sizeE (A : eqType) (s : seq A) x :
            reflect (index x s = size s) (x \notin s).
Proof. by apply/(equivP idP)/index_memN. Qed.

Lemma size0nilP (A : eqType) (xs : seq A) :
        reflect (xs = [::]) (size xs == 0).
Proof.
case: eqP=>X; constructor; first by move/size0nil: X.
by move=>N; rewrite N in X.
Qed.

Lemma has_nilP (A : eqType) (xs : seq A) :
        reflect (has predT xs) (xs != [::]).
Proof. by case: xs=>[|x xs]; constructor. Qed.

Lemma map_nilP A (B : eqType) (f : A -> B) (s : seq A) :
        reflect (exists k, k \in map f s) (map f s != [::]).
Proof.
case: has_nilP=>X; constructor.
- by case/hasP: X=>x; exists x.
by case=>k K; elim: X; apply/hasP; exists k.
Qed.

Lemma filter_nilP (A : eqType) (p : pred A) (s : seq A) :
        reflect (forall x, p x -> x \in s -> false)
                ([seq x <- s | p x] == [::]).
Proof.
case: eqP=>E; constructor.
- move=>x H1 H2; suff : x \in [seq x <- s | p x] by rewrite E.
  by rewrite mem_filter H1 H2.
move=>H; apply: E; apply: size0nil; apply/eqP; rewrite size_filter.
by rewrite eqn0Ngt -has_count; apply/hasPn=>x /H; case: (p x)=>//; apply.
Qed.

Lemma filter_pred1 (A : eqType) (x : A) (s : seq A) :
        x \notin s -> filter (pred1 x) s = [::].
Proof.
move=>H; apply/eqP; apply/filter_nilP=>z /eqP ->.
by rewrite (negbTE H).
Qed.

Lemma filter_predC1 (A : eqType) (x : A) (s : seq A) :
        x \notin s -> filter (predC1 x) s = s.
Proof.
by move=>H; apply/all_filterP/allP=>y /=; case: eqP=>// ->; apply/contraL.
Qed.

Lemma filter_mem_sym (A : eqType) (s1 s2 : seq A) :
        filter (mem s1) s2 =i filter (mem s2) s1.
Proof. by move=>x; rewrite !mem_filter andbC. Qed.

Lemma filter_swap A (s : seq A) p1 p2 :
        filter p1 (filter p2 s) = filter p2 (filter p1 s).
Proof. by rewrite -!filter_predI; apply eq_filter=>z /=; rewrite andbC. Qed.

Lemma filter_predIC A (s : seq A) p1 p2 :
         filter (predI p1 p2) s = filter (predI p2 p1) s.
Proof. by rewrite filter_predI filter_swap -filter_predI. Qed.

Lemma index_inj (A : eqType) (s : seq A) (x y : A) :
        x \in s -> index x s = index y s -> x = y.
Proof.
elim: s=>[|k s IH] //=; rewrite inE eq_sym.
by case: eqP=>[->{k} _|_ /= S]; case: eqP=>// _ []; apply: IH S.
Qed.

Lemma cat_cancel (A : eqType) (xs1 xs2 ys1 ys2 : seq A) (k : A) :
        k \notin xs1 -> k \notin xs2 ->
        xs1 ++ k :: ys1 = xs2 ++ k :: ys2 ->
        (xs1 = xs2) * (ys1 = ys2).
Proof.
move=>Nk1 Nk2 E.
have Es : size xs1 = size xs2.
- have : index k (xs1++k::ys1) = index k (xs2++k::ys2) by rewrite E.
  by rewrite !index_cat /= (negbTE Nk1) (negbTE Nk2) eq_refl !addn0.
have Ex : xs1 = take (size xs1) (xs1 ++ k :: ys1).
- by rewrite take_cat ltnn subnn /= cats0.
rewrite E Es take_cat ltnn subnn /= cats0 in Ex.
rewrite {xs1 Nk1 Es}Ex in E *.
have : ys1 = drop (size (xs2++[::k])) (xs2++k::ys1).
- by rewrite drop_cat size_cat /= addn1 ltnNge ltnW //= subSn // subnn /= drop0.
by rewrite E drop_cat size_cat /= addn1 ltnNge ltnW //= subSn // subnn /= drop0.
Qed.

(* if the list is not empty, the default value in head doesn't matter *)
Lemma head_dflt (A : eqType) (x1 x2 x : A) (s : seq A) :
        x \in s -> head x1 s = head x2 s.
Proof. by case: s. Qed.

Lemma mem_head (A : eqType) (x : A) (s : seq A) : head x s \in x :: s.
Proof. by case: s=>[|y ys]; rewrite !inE //= eq_refl orbT. Qed.

(* a common pattern of using mem_head that avoids forward reasoning *)
Lemma mem_headI (A : eqType) (x : A) (s : seq A) a :
        a = head x s -> a \in x :: s.
Proof. by move=>->; apply: mem_head. Qed.

Lemma head_nilp (A : eqType) (x : A) (s : seq A) :
        x \notin s -> head x s = x -> nilp s.
Proof.
elim: s=>[|y ys IH] //= H1 H2.
by rewrite H2 inE eq_refl /= in H1.
Qed.

Lemma head_notin (A : eqType) (x y : A) (s : seq A) :
        y \in s -> x \notin s -> head x s != x.
Proof.
move=>Y X; apply/negP=>/eqP; move/(head_nilp X)/nilP=>E.
by rewrite E in Y.
Qed.

(* Interaction of filter/last/index *)

Section FilterLastIndex.
Variables (A : eqType).

(* if s has an element, last returns one of them *)
Lemma last_in x k (s : seq A) : x \in s -> last k s \in s.
Proof.
elim: s k=>[|k s IH] k' //=; rewrite !inE.
case/orP=>[/eqP <-|/IH ->]; first by apply: mem_last.
by rewrite orbT.
Qed.

Arguments last_in x [k s].

Lemma last_notin x k (s : seq A) : x \in s -> k \notin s -> last k s != k.
Proof. by move/(last_in _ (k:=k))=>H /negbTE; case: eqP H=>// ->->. Qed.

(* last either returns a default, or one of s's elements *)
Lemma last_change k (s : seq A) : last k s != k -> last k s \in s.
Proof. by move: (mem_last k s); rewrite inE; case: eqP. Qed.

Lemma last_changeE1 k (s : seq A) :
        last k s != k -> forall x, last x s = last k s.
Proof. by elim: s k=>[|k s IH] y //=; rewrite eq_refl. Qed.

Lemma last_changeE2 k (s : seq A) :
        last k s != k -> forall x, x \notin s -> last x s != x.
Proof. by move/last_change/last_notin. Qed.

(* common formats of last_change *)
Lemma last_nochange k (s : seq A) : last k s = k -> (k \in s) || (s == [::]).
Proof.
case: s k=>[|k s] //= k'; rewrite inE; case: eqP=>[->|N L] //.
by move: (@last_change k s); rewrite L=>-> //; case: eqP N.
Qed.

Lemma last_nochange_nil k (s : seq A) : last k s = k -> k \notin s -> s = [::].
Proof. by move/last_nochange; case/orP=>[/negbF ->|/eqP]. Qed.

(* last and rcons *)

Lemma rcons_lastX x y (s : seq A) :
        x \in s -> exists s', s = rcons s' (last y s).
Proof.
elim/last_ind: s=>[|ks k IH] //=.
by rewrite last_rcons; exists ks.
Qed.

Lemma rcons_lastP x (s : seq A) :
        reflect (exists s', s = rcons s' (last x s)) (last x s \in s).
Proof.
case X : (last x s \in s); constructor; first by apply: rcons_lastX X.
case=>s' E; move/negP: X; elim.
by rewrite E last_rcons mem_rcons inE eq_refl.
Qed.

Lemma rcons_lastXP x y (s : seq A) :
        reflect (exists s', s = rcons s' x) ((x == last y s) && (x \in s)).
Proof.
case: eqP=>[->|N]; first by apply: rcons_lastP.
by constructor; case=>s' E; elim: N; rewrite E last_rcons.
Qed.

(* last has bigger index than anything in x *)
Lemma index_last_mono x k (s : seq A) :
         uniq s -> x \in s -> index x s <= index (last k s) s.
Proof.
elim: s k=>[|k s IH] //= k'; rewrite inE !(eq_sym k).
case/andP=>K U; case: (x =P k)=>//= /eqP N X.
case: (last k s =P k)=>[/last_nochange|/eqP L].
- by case: eqP X=>[->//|]; rewrite (negbTE K).
by apply: leq_trans (IH k U X) _.
Qed.

(* if it has bigger index, and is in the list, then it's last *)
Lemma max_index_last (s : seq A) (x y : A) :
         uniq s -> x \in s ->
         (forall z, z \in s -> index z s <= index x s) -> last y s = x.
Proof.
elim: s y=>[|k s IH] y //= /andP [Nk U]; rewrite inE (eq_sym k).
case: (x =P k) Nk=>[<-{k} Nk _|_ Nk /= S] /= D; last first.
- apply: IH=>// z Z; move: (D z); rewrite inE Z orbT=>/(_ (erefl _)).
  by case: ifP Z Nk=>// /eqP ->->.
suff : nilp s by move/nilP=>->.
rewrite /nilp eqn0Ngt -has_predT; apply/hasPn=>z Z.
move: (D z); rewrite inE Z orbT=>/(_ (erefl _)).
by case: ifP Z Nk=>// /eqP ->->.
Qed.

(* last_filter either returns default or a p-element of ks *)
Lemma last_filter_change k p (ks : seq A) :
        last k (filter p ks) != k ->
        p (last k (filter p ks)) && (last k (filter p ks) \in ks).
Proof. by move/last_change; rewrite mem_filter. Qed.

Lemma index_filter_mono (p : pred A) (ks : seq A) x y :
        p x -> index x ks <= index y ks ->
        index x (filter p ks) <= index y (filter p ks).
Proof.
move=>Px; elim: ks=>[|k ks IH] //=; case P : (p k)=>/=;
by case: ifP Px; case: ifP=>// _ /eqP <-; rewrite P.
Qed.

Lemma filter_sub (p1 p2 : pred A) (s : seq A) :
        subpred p1 p2 -> {subset filter p1 s <= filter p2 s}.
Proof.
move=>S; rewrite (_ : filter p1 s = filter p1 (filter p2 s)).
- by apply: mem_subseq; apply: filter_subseq.
rewrite -filter_predI; apply: eq_in_filter=>x X /=.
by case E : (p1 x)=>//=; rewrite (S _ E).
Qed.

Lemma last_filter_neq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> x \notin s ->
        last x (filter p1 s) != x -> last x (filter p2 s) != x.
Proof.
move=>S N /last_filter_change /andP [H1 H2].
apply: (@last_notin (last x [seq x <-s | p1 x])).
- by rewrite mem_filter H2 andbT; apply: S.
by rewrite mem_filter negb_and N orbT.
Qed.

Lemma last_filter_eq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> x \notin s ->
        last x (filter p2 s) = x -> last x (filter p1 s) = x.
Proof.
move=>S N /eqP E; apply/eqP.
by apply: contraTT E; apply: last_filter_neq.
Qed.

Lemma index_last_sub (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> uniq (x :: s) ->
        index (last x (filter p1 s)) (x :: s) <=
        index (last x (filter p2 s)) (x :: s).
Proof.
move=>S; elim: s x=>[|k s IH] //= x; rewrite !inE negb_or -andbA.
rewrite -(eq_sym k) -!(eq_sym (last _ _)); case/and4P=>N Sx Sk U.
have [Ux Uk] : uniq (x :: s) /\ uniq (k :: s) by rewrite /= Sx Sk U.
case P1 : (p1 k)=>/=.
- rewrite (S _ P1) /=; case: (last k _ =P k).
  - move/last_nochange; rewrite mem_filter (negbTE Sk) andbF /=.
    move/eqP=>-> /=; rewrite (negbTE N).
    case: (last k _ =P k); first by move=>->; rewrite (negbTE N).
    by case/eqP/last_filter_change/andP; case: eqP Sx=>// <- /negbTE ->.
  move/eqP=>N1; move: (last_filter_neq S Sk N1)=>N2.
  move: (IH _ Uk); rewrite /= !(eq_sym k).
  rewrite (negbTE N1) (negbTE N2) -(last_changeE1 N1 x) -(last_changeE1 N2 x).
  rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sx,orbT) //.
  by rewrite (negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sx,orbT).
case P2 : (p2 k)=>/=.
- case: (last x _ =P x)=>// /eqP N1; move: (last_filter_neq S Sx N1)=>N2.
  move: (IH _ Ux); rewrite /= !(eq_sym x) (negbTE N1) (negbTE N2).
  rewrite -(last_changeE1 N1 k) {1 3}(last_changeE1 N2 k).
  rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sk,orbT) //.
  by rewrite !(negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sk,Sx,orbT).
case: (last x _ =P x)=>// /eqP N1; move: (last_filter_neq S Sx N1)=>N2.
move: (IH _ Ux); rewrite /= !(eq_sym x) (negbTE N1) (negbTE N2).
rewrite -(last_changeE1 N1 k) -(last_changeE1 N2 k).
rewrite (negbTE (last_changeE2 N1 _)) ?(mem_filter,negb_and,Sk,orbT) //.
by rewrite !(negbTE (last_changeE2 N2 _)) ?(mem_filter,negb_and,Sk,orbT).
Qed.

Lemma last_filter_last_helper (p : pred A) x (s : seq A) y :
        uniq (x :: s) -> p y -> y \in s ->
        index y s <= index (last x (filter p s)) s.
Proof.
elim: s x=>[|k s IH] x //=; rewrite !inE !negb_or !(eq_sym _ k).
case/andP=>/andP [H1 H2] /andP [H3 H4] Px.
case: eqP=> [->|_] //= Ks; case P: (p k)=>/=.
- case: eqP=>E; last by apply: IH=>//=; rewrite H3 H4.
  move: (@last_in y k (filter p s)); rewrite -E !mem_filter.
  by rewrite Px Ks P (negbTE H3); move/(_ (erefl _)).
case: eqP=>E; last by apply: IH=>//=; rewrite H2 H4.
by move: H1; rewrite E; move/last_filter_change; rewrite -E P.
Qed.

Lemma last_filter_last (p : pred A) x (s : seq A) y :
        uniq (x :: s) -> p y -> y \in s ->
        index y (x :: s) <= index (last x (filter p s)) (x :: s).
Proof.
move=>/= /andP [Sx U] H Sy /=; case: (x =P y)=>//= _.
have Hy : y \in [seq x <- s | p x] by rewrite mem_filter H Sy.
rewrite eq_sym; case: (last x _ =P x); last first.
- by move=>_; apply: last_filter_last_helper=>//=; rewrite Sx U.
move/last_nochange; rewrite mem_filter (negbTE Sx) andbF /=.
by move/eqP=>E; rewrite E in Hy.
Qed.

Lemma index_filter_ltL (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 ->
         (index t1 ks < index t2 ks) ->
         (index t1 (filter p ks) < index t2 (filter p ks)).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or (eq_sym t1).
case: eqP=>[->{k} /= Pt1|/eqP Nkt1 /= H].
- by rewrite Pt1 /= eq_refl; case: eqP.
case: eqP=>// /eqP Nkt2; case: ifP=>H1 /=.
- by rewrite (negbTE Nkt1) (negbTE Nkt2) !ltnS; apply: IH H.
by rewrite ltnS; apply: IH H.
Qed.

Lemma index_filter_leL (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 ->
         (index t1 ks <= index t2 ks) ->
         (index t1 (filter p ks) <= index t2 (filter p ks)).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or (eq_sym t1).
case: eqP=>[->{k} /= Pt1|/eqP Nkt1 /= H].
- by rewrite Pt1 /= eq_refl; case: eqP.
case: eqP=>// /eqP Nkt2; case: ifP=>H1 /=.
- by rewrite (negbTE Nkt1) (negbTE Nkt2) !ltnS; apply: IH H.
by rewrite ltnS; apply: IH H.
Qed.

Lemma index_filter_ltR (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) < index t2 (filter p ks)) ->
         (index t1 ks < index t2 ks).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or /=.
rewrite (eq_sym t2).
case: eqP=>[->{k} /= Pt2|/eqP Nkt2 /=].
- by rewrite Pt2 /= eq_refl; case: eqP.
case: eqP=>[->{t1}//|/eqP Nt1k].
case: ifP=>H1 H2 /=.
- by rewrite (negbTE Nt1k) (negbTE Nkt2) !ltnS; apply: IH H2.
by rewrite ltnS; apply: IH H2.
Qed.

Lemma index_filter_leR (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) <= index t2 (filter p ks)) ->
         (index t1 ks <= index t2 ks).
Proof.
elim: ks t1 t2=>[|k ks IH] t1 t2 //=; rewrite inE negb_or /=.
rewrite (eq_sym t2).
case: eqP=>[->{k} /= Pt2|/eqP Nkt2 /=].
- by rewrite Pt2 /= eq_refl; case: eqP.
case: eqP=>[->{t1}//|/eqP Nt1k].
case: ifP=>H1 H2 /=.
- by rewrite (negbTE Nt1k) (negbTE Nkt2) !ltnS; apply: IH H2.
by rewrite ltnS; apply: IH H2.
Qed.

(* we can put the left and right lemmas together *)
Lemma index_filter_lt (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 -> (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) < index t2 (filter p ks)) =
         (index t1 ks < index t2 ks).
Proof.
move=>H1 H2; apply/idP/idP.
- by apply: index_filter_ltR.
by apply: index_filter_ltL.
Qed.

Lemma index_filter_le (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 -> (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) <= index t2 (filter p ks)) =
         (index t1 ks <= index t2 ks).
Proof.
move=>H1 H2; apply/idP/idP.
- by apply: index_filter_leR.
by apply: index_filter_leL.
Qed.

(* index and masking *)

Lemma index_mask (s : seq A) m a b  :
         uniq s ->
         a \in mask m s -> b \in mask m s ->
         index a (mask m s) < index b (mask m s) <->
         index a s < index b s.
Proof.
elim: m s=>[|x m IH][|k s] //= /andP [K U]; case: x=>[|Ma Mb] /=.
- rewrite !inE; case/orP=>[/eqP <-|Ma].
  - by case/orP=>[/eqP ->|]; rewrite eq_refl //; case: eqP.
  case/orP=>[/eqP ->|Mb]; first by rewrite eq_refl.
  by case: eqP; case: eqP=>//; rewrite ltnS IH.
case: eqP Ma K=>[-> /mem_mask -> //|Ka].
case: eqP Mb=>[-> /mem_mask -> //|Kb Mb Ma].
by rewrite ltnS IH.
Qed.

Lemma index_subseq (s1 s2 : seq A) a b :
         subseq s1 s2 -> uniq s2 -> a \in s1 -> b \in s1 ->
         index a s1 < index b s1 <-> index a s2 < index b s2.
Proof. by case/subseqP=>m _ ->; apply: index_mask. Qed.

End FilterLastIndex.

(* index and mapping *)

Section IndexPmap.
Variables (A B : eqType).

Lemma index_pmap_inj (s : seq A) (f : A -> option B) a1 a2 b1 b2 :
        injective f -> f a1 = Some b1 -> f a2 = Some b2 ->
        index b1 (pmap f s) < index b2 (pmap f s) <-> index a1 s < index a2 s.
Proof.
move=>Inj E1 E2; elim: s=>[|k s IH] //=; rewrite /oapp.
case: eqP=>[->{k}|].
- rewrite E1 /= eq_refl.
  case: (a1 =P a2) E1 E2=>[-> -> [/eqP ->] //|].
  by case: (b1 =P b2)=>[-> Na <- /Inj /esym/Na|].
case: eqP=>[->{k} Na|N2 N1]; first by rewrite E2 /= eq_refl !ltn0.
case E : (f k)=>[b|] //=.
case: eqP E1 E=>[-><- /Inj/N1 //|_ _].
by case: eqP E2=>[-><- /Inj/N2 //|_ _ _]; rewrite IH.
Qed.

Lemma index_pmap_inj_mem (s : seq A) (f : A -> option B) a1 a2 b1 b2 :
        {in s &, injective f} ->
        a1 \in s -> a2 \in s ->
        f a1 = Some b1 -> f a2 = Some b2 ->
        index b1 (pmap f s) < index b2 (pmap f s) <-> index a1 s < index a2 s.
Proof.
move=>Inj A1 A2 E1 E2.
elim: s Inj A1 A2=>[|k s IH] //= Inj; rewrite /oapp !inE !(eq_sym k).
case: eqP Inj=>[<-{k} /= Inj _|].
- rewrite E1 /= !eq_refl eq_sym.
  case: eqP E1 E2=>[->-> [->]|]; first by rewrite eq_refl.
  case: eqP=>[-> Na <- E /= A2|//].
  by move/Inj: E Na=>-> //; rewrite inE ?(eq_refl,A2,orbT).
case eqP=>[<-{k} Na Inj /= A1 _|]; first by rewrite E2 /= eq_refl !ltn0.
move=>N2 N1 Inj /= A1 A2.
have Inj1 : {in s &, injective f}.
- by move=>x y X Y; apply: Inj; rewrite inE ?X ?Y ?orbT.
case E : (f k)=>[b|] /=; last by rewrite IH.
case: eqP E1 E=>[-> <- E|_ _].
- by move/Inj: E N1=>-> //; rewrite inE ?(eq_refl,A1,orbT).
case: eqP E2=>[-><- E|_ _ _]; last by rewrite IH.
by move/Inj: E N2=>-> //; rewrite inE ?(eq_refl,A2,orbT).
Qed.

(* we can relax the previous lemma a bit *)
(* the relaxation will be more commonly used than the previous lemma *)
(* because the option type gives us the implication that the second *)
(* element is in the map *)
Lemma index_pmap_inj_in (s : seq A) (f : A -> option B) a1 a2 b1 b2 :
        {in s & predT, injective f} ->
        f a1 = Some b1 -> f a2 = Some b2 ->
        index b1 (pmap f s) < index b2 (pmap f s) <-> index a1 s < index a2 s.
Proof.
move=>Inj E1 E2.
case A1 : (a1 \in s); last first.
- move/negbT/index_sizeE: (A1)=>->.
  suff /index_sizeE -> : b1 \notin pmap f s by rewrite !ltnNge !index_size.
  rewrite mem_pmap; apply/mapP; case=>x X /esym; rewrite -E1=>E.
  by move/(Inj _ _ X): E A1=><- //; rewrite X.
case A2 : (a2 \in s).
- by apply: index_pmap_inj_mem=>// x y X _; apply: Inj.
move/negbT/index_sizeE: (A2)=>->.
suff /index_sizeE -> : b2 \notin pmap f s.
- by rewrite !index_mem /= A1 mem_pmap; split=>// _; apply/mapP; exists a1.
rewrite mem_pmap; apply/mapP; case=>x X /esym; rewrite -E2=>E.
by move/(Inj _ _ X): E A2=><- //; rewrite X.
Qed.

End IndexPmap.

Section SeqRel.
Variable (A : eqType).
Implicit Type (ltT leT : rel A).

(* ordering with path, seq and last *)

Lemma eq_last (s : seq A) x y :
        x \in s -> last y s = last x s.
Proof. by elim: s x y=>[|w s IH]. Qed.

Lemma seq_last_in (s : seq A) x :
        last x s \notin s -> s = [::].
Proof.
case: (lastP s)=>{s} // s y; case: negP=>//; elim; rewrite last_rcons.
by elim: s=>[|y' s IH]; rewrite /= inE // IH orbT.
Qed.

Lemma path_last (s : seq A) leT x :
        ssrbool.transitive leT -> path leT x s ->
        (x == last x s) || leT x (last x s).
Proof.
move=>T /(order_path_min T) /allP; case: s=>[|a s] H /=.
- by rewrite eq_refl.
by rewrite (H (last a s)) ?orbT // mem_last.
Qed.

Lemma path_lastR (s : seq A) leT x :
        reflexive leT -> transitive leT ->
        path leT x s -> leT x (last x s).
Proof. by move=>R T P; case: eqP (path_last T P)=>// <- _; apply: R. Qed.

(* in a sorted list, the last element is maximal *)
(* and the maximal element is last *)

Lemma sorted_last_key_max (s : seq A) leT x y :
        transitive leT -> sorted leT s -> x \in s ->
        (x == last y s) || leT x (last y s).
Proof.
move=>T; elim: s x y=>[|z s IH] //= x y H; rewrite inE.
case: eqP=>[->|] /= _; first by apply: path_last.
by apply: IH (path_sorted H).
Qed.

Lemma sorted_last_key_maxR (s : seq A) leT x y :
        reflexive leT -> transitive leT ->
        sorted leT s -> x \in s -> leT x (last y s).
Proof.
move=>R T S X; case/orP: (sorted_last_key_max y T S X)=>// /eqP <-.
by apply: R.
Qed.

Lemma sorted_max_key_last (s : seq A) leT x y :
        transitive leT -> antisymmetric leT ->
        sorted leT s -> x \in s ->
        (forall z, z \in s -> leT z x) -> last y s = x.
Proof.
move=>T S; elim: s x y => [|w s IH] //= x y; rewrite inE /=.
case: eqP=>[<- /= H1 _ H2 | _ H /= H1 H2]; last first.
- apply: IH (path_sorted H) H1 _ => z H3; apply: H2.
  by rewrite inE /= H3 orbT.
case/orP: (path_last T H1)=>[/eqP //|] X.
by apply: S; rewrite X H2 ?mem_last.
Qed.

Lemma max_key_last_notin (s : seq A) (leT : rel A) x y :
        leT y x -> (forall z, z \in s -> leT z x) -> leT (last y s) x.
Proof.
elim: s x y=>[|w s IH] //= x y H1 H2; apply: IH.
- by apply: (H2 w); rewrite inE eq_refl.
by move=>z D; apply: H2; rewrite inE D orbT.
Qed.

Lemma seq_last_mono (s1 s2 : seq A) leT x :
        transitive leT -> path leT x s1 -> path leT x s2 ->
        {subset s1 <= s2} ->
        (last x s1 == last x s2) || leT (last x s1) (last x s2).
Proof.
move=>T; case: s1=>/= [_ H1 _|a s]; first by apply: path_last H1.
case/andP=>H1 H2 H3 H; apply: sorted_last_key_max (path_sorted H3) _=>//.
apply: {x s2 H1 H3} H; rewrite inE orbC -implyNb.
by case E: (_ \notin _) (@seq_last_in s a)=>//= ->.
Qed.

Lemma seq_last_monoR (s1 s2 : seq A) leT x :
        reflexive leT -> transitive leT ->
        path leT x s1 -> path leT x s2 ->
        {subset s1 <= s2} ->
        leT (last x s1) (last x s2).
Proof. by move=>R T P1 P2 S; case: eqP (seq_last_mono T P1 P2 S)=>[->|]. Qed.

Lemma ord_path (s : seq A) leT (x y : A) :
        transitive leT ->
        leT x y -> path leT y s -> path leT x s.
Proof.
move=>T; elim: s x y=>[|k s IH] x y //= H1 /andP [H2 ->].
by rewrite (T _ _ _ H1 H2).
Qed.

Lemma path_mem (s : seq A) leT x y :
        transitive leT ->
        path leT x s -> y \in s -> leT x y.
Proof.
move=>T; elim: s x=>[|z s IH] x //= /andP [O P].
rewrite inE; case/orP=>[/eqP -> //|].
by apply: IH; apply: ord_path O P.
Qed.

Lemma path_mem_irr (s : seq A) ltT x :
        irreflexive ltT -> transitive ltT ->
        path ltT x s -> x \notin s.
Proof.
move=>I T P; apply: contraFT (I x).
by rewrite negbK; apply: path_mem T P.
Qed.

Lemma sorted_rcons (s : seq A) leT (y : A) :
        sorted leT s -> (forall x, x \in s -> leT x y) ->
        sorted leT (rcons s y).
Proof.
elim: s=>[|a s IH] //= P H; rewrite rcons_path P /=.
by apply: H (mem_last _ _).
Qed.

Lemma sorted_subset_subseq (s1 s2 : seq A) ltT :
        irreflexive ltT -> transitive ltT ->
        sorted ltT s1 -> sorted ltT s2 ->
        {subset s1 <= s2} -> subseq s1 s2.
Proof.
move=>R T S1 S2 H.
suff -> : s1 = filter (fun x => x \in s1) s2 by apply: filter_subseq.
apply: irr_sorted_eq S1 _ _=>//; first by rewrite sorted_filter.
by move=>k; rewrite mem_filter; case S : (_ \in _)=>//; rewrite (H _ S).
Qed.

Lemma sorted_ord_index (s : seq A) ltT x y :
        irreflexive ltT -> transitive ltT ->
        sorted ltT s -> x \in s -> ltT x y -> index x s < index y s.
Proof.
move=>I T S P H; elim: s S P=>[|z s IH] //= P; rewrite !inE !(eq_sym z).
case: eqP H P=>[<-{z} H P _|_ H P /= X]; first by case: eqP H=>[<-|] //; rewrite I.
case: eqP H P=>[<-{z} H|_ H]; last first.
- by move/path_sorted=>S; rewrite ltnS; apply: IH.
by move/(path_mem T)/(_ X)=>/(T _ _ _ H); rewrite I.
Qed.

Lemma path_ord_index_leq (s : seq A) leT x y :
        transitive leT -> antisymmetric leT ->
        leT x y -> path leT y s -> x \in s -> x = y.
Proof.
move=>T; elim: s x y=>[|a l IH] //= x y As Lxy.
case/andP=>Lya Pal; rewrite inE.
case: eqP Lya Pal As=>[<-{a} Lyx _ As _|Nxa Lya Pal /= As' X].
- by apply: As=>//; rewrite Lxy Lyx.
by move/Nxa: (IH x a As' (T _ _ _ Lxy Lya) Pal X).
Qed.

Lemma sorted_ord_index_leq (s : seq A) leT x y :
        transitive leT -> antisymmetric leT ->
        sorted leT s ->
        x \in s -> leT x y -> x != y -> index x s < index y s.
Proof.
move=>T As S P H N; elim: s S As P=>[|z s IH] //= P As; rewrite inE !(eq_sym z).
case: eqP H P As=>[<-{z} H P As _|Nxz H P As /= X]; first by rewrite eq_sym (negbTE N).
case: eqP Nxz P=>[<-{z} Nxy P|Nyz Nxz P].
- by move/Nxy: (path_ord_index_leq T As H P X).
by apply: IH X=>//; apply: path_sorted P.
Qed.

Lemma sorted_index_ord (s : seq A) leT x y :
        transitive leT -> sorted leT s -> y \in s ->
        index x s < index y s -> leT x y.
Proof.
move=>T; elim: s=>[|z s IH] //= P; rewrite inE !(eq_sym z).
case: eqP=>//= /eqP N; case: eqP P=>[-> P /(path_mem T P)|_ P] //.
by rewrite ltnS; apply: IH; apply: path_sorted P.
Qed.

(* sorted, uniq, filter *)

Lemma lt_sorted_uniq_le (s : seq A) ltT :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT s = uniq s && (sorted (fun k t => (k == t) || ltT k t) s).
Proof.
move=>I As T; case: s=>// n s; elim: s n=>//= m s IHs n.
rewrite inE negb_or IHs -!andbA /=.
case: (n =P m)=>[->|/eqP Nm /=]; first by rewrite I.
case lTnm : (ltT n m)=>/=; last by rewrite !andbF.
case Ns: (n \in s)=>//=; do !bool_congr.
have T' : transitive (fun k t => (k == t) || ltT k t).
- move=>x y z /orP [/eqP -> //|H].
  case/orP=>[/eqP <-|]; first by rewrite H orbT.
  by move/(T _ _ _ H)=>->; rewrite orbT.
apply/negP=>/(order_path_min T')/allP/(_ n Ns).
rewrite eq_sym (negbTE Nm) /= =>lTmn.
by rewrite (As m n) ?eq_refl // lTnm lTmn in Nm.
Qed.

Lemma sort_sorted_in_lt (s : seq A) ltT :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        uniq s ->
        {in s &, total (fun k t => (k == t) || ltT k t)} ->
        sorted ltT (sort (fun k t => (k == t) || ltT k t) s).
Proof.
move=>I S T U Tot; rewrite lt_sorted_uniq_le //.
by rewrite sort_uniq U (sort_sorted_in Tot _).
Qed.

(* filtering and consecutive elements in an order *)
Lemma filterCN (ltT : rel A) f t1 t2 :
       t1 \notin f ->
       {in f, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       filter (ltT^~ t2) f = filter (ltT^~ t1) f.
Proof.
move=>N C; apply: eq_in_filter=>x T; rewrite C ?inE ?orbT //.
by case: eqP N T=>// -> /negbTE ->.
Qed.

Lemma filterCE (ltT : rel A) f t1 t2 :
        irreflexive ltT ->
        transitive ltT ->
        sorted ltT f ->
        {in f, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
        t1 \in f ->
        filter (ltT^~ t2) f = filter (ltT^~ t1) f ++ [:: t1].
Proof.
move=>I T S Z F; have U : uniq f by apply: sorted_uniq T I _ S.
rewrite -(filter_pred1_uniq U F); apply: irr_sorted_eq (T) I _ _ _ _ _.
- by apply: sorted_filter T _ _ S.
- rewrite -[filter (ltT^~ t1) _]revK -[filter (pred1 t1) _]revK -rev_cat.
  rewrite rev_sorted -filter_rev filter_pred1_uniq ?(mem_rev,rev_uniq) //.
  rewrite /= path_min_sorted ?(rev_sorted, sorted_filter T _ S) //.
  by apply/allP=>x; rewrite mem_rev mem_filter=>/andP [].
move=>x; rewrite mem_cat !mem_filter /=.
case X: (x \in f); last by rewrite !andbF.
by rewrite Z // orbC !andbT.
Qed.

(* frequently we have nested filtering and sorting *)
(* for which the following forms of the lemmas is more effective *)

Lemma filter2CN (ltT : rel A) p f t1 t2 :
       t1 \notin p ->
       {in p, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       filter (ltT^~ t2) (filter p f) = filter (ltT^~ t1) (filter p f).
Proof.
move=>N C; apply: filterCN; first by rewrite mem_filter negb_and N.
by move=>z; rewrite mem_filter=>/andP [D _]; apply: C.
Qed.

Lemma filter2CE (ltT : rel A) (p : pred A) f t1 t2 :
       irreflexive ltT ->
       antisymmetric ltT ->
       transitive ltT ->
       {in f &, total (fun k t => (k == t) || ltT k t)} ->
       {in p, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       uniq f ->
       p t1 -> t1 \in f ->
       filter (ltT^~ t2)
         (filter p (sort (fun k t => (k == t) || ltT k t) f)) =
       filter (ltT^~ t1)
         (filter p (sort (fun k t => (k == t) || ltT k t) f)) ++ [:: t1].
Proof.
move=>I Asym T Tot Z U P F; apply: filterCE (I) (T) _ _ _.
- by rewrite (sorted_filter T _ _) //; apply: sort_sorted_in_lt.
- by move=>z; rewrite mem_filter=>/andP [Pz _]; apply: Z.
by rewrite mem_filter mem_sort P F.
Qed.

(* nth *)

Lemma nth_cons (a x : A) (s : seq A) (n : nat) :
        nth a (x :: s) n = if n == 0 then x else nth a s n.-1.
Proof. by case: n. Qed.

Lemma nth_base (s : seq A) k1 k2 i :
        i < size s -> nth k1 s i = nth k2 s i.
Proof.
elim: s i=>[|x xs IH] //= i K; rewrite !nth_cons.
by case: eqP=>//; case: i K=>// i; rewrite ltnS=>/IH ->.
Qed.

Lemma nth_path_head (s : seq A) leT x0 k i :
        transitive leT ->
        i <= size s -> path leT k s ->
        (k == nth x0 (k::s) i) || leT k (nth x0 (k::s) i).
Proof.
move=>T; case: (posnP i)=>[->|N S P]; first by rewrite eq_refl.
apply/orP; right; elim: i N S P=>[|i] //; case: s=>//= x xs IH _.
rewrite ltnS=>N /andP [H1 H2]; case: i IH N=>//= i /(_ (erefl _)) IH N.
rewrite !ltnS in IH; move: (IH (ltnW N)); rewrite H1 H2=>/(_ (erefl _)).
by move/T; apply; apply/pathP.
Qed.

Lemma nth_path_last (s : seq A) leT x0 k i :
        transitive leT ->
        i < size s -> path leT k s ->
        (nth x0 s i == last k s) || leT (nth x0 s i) (last k s).
Proof.
move=>T S P.
suff : forall z, z \in s -> (z == last k s) || leT z (last k s).
- by apply; rewrite mem_nth.
move=>z; apply: sorted_last_key_max=>//.
by apply: path_sorted P.
Qed.

Lemma nth_consS (s : seq A) x0 k i : nth x0 s i = nth x0 (k::s) i.+1.
Proof. by []. Qed.

Lemma nth_leT (s : seq A) leT x0 k i :
        i < size s -> path leT k s ->
        leT (nth x0 (k::s) i) (nth x0 s i).
Proof.
elim: i k s=>[|i IH] k s; first by case: s=>[|x xs] //= _ /andP [].
by case: s IH=>[|x xs] //= IH N /andP [P1 P2]; apply: IH.
Qed.

Lemma nth_ltn_mono (s : seq A) leT x0 k i j :
        transitive leT ->
        i <= size s -> j <= size s ->
        path leT k s ->
        i < j -> leT (nth x0 (k::s) i) (nth x0 (k::s) j).
Proof.
move=>T S1 S2 P; elim: j S2=>[|j IH] //= S2.
move: (nth_leT x0 S2 P)=>L.
rewrite ltnS leq_eqVlt=>/orP; case=>[/eqP -> //|].
by move/(IH (ltnW S2))/T; apply.
Qed.

Lemma nth_mono_ltn (s : seq A) ltT x0 k i j :
         irreflexive ltT ->
         transitive ltT ->
         i <= size s -> j <= size s ->
         path ltT k s ->
         ltT (nth x0 (k::s) i) (nth x0 (k::s) j) -> i < j.
Proof.
move=>I T S1 S2 P; case: ltngtP=>//; last by move=>->; rewrite I.
by move/(nth_ltn_mono x0 T S2 S1 P)/T=>X /X; rewrite I.
Qed.

Lemma nth_between (s : seq A) ltT x0 k z i :
        irreflexive ltT ->
        transitive ltT ->
        path ltT k s ->
        ltT (nth x0 (k::s) i) z -> ltT z (nth x0 s i) -> z \notin s.
Proof.
move=>I T P H1 H2; apply/negP=>Z; move: H1 H2.
case: (leqP i (size s))=>N; last first.
- rewrite !nth_default ?(ltnW N) //= => H.
  by move/(T _ _ _ H); rewrite I.
have S : index z s < size s by rewrite index_mem.
rewrite -(nth_index x0 Z) !(nth_consS s x0 k).
move/(nth_mono_ltn I T N S P)=>K1.
move/(nth_mono_ltn I T S (leq_trans K1 S) P); rewrite ltnS.
by case: ltngtP K1.
Qed.

(* how to prove that something's sorted via index? *)

Lemma index_sorted (s : seq A) (leT : rel A) :
        uniq s ->
        (forall a b, a \in s -> b \in s -> index a s < index b s -> leT a b) ->
        sorted leT s.
Proof.
elim: s=>[|x xs IH] //= U H; have P : all (leT x) xs.
- apply/allP=>z Z; apply: H; rewrite ?(inE,eq_refl,Z,orbT) //.
  by case: ifP U=>// /eqP ->; rewrite Z.
rewrite (path_min_sorted P); apply: IH=>[|a b Xa Xb N]; first by case/andP: U.
apply: H; rewrite ?(inE,Xa,Xb,orbT) //.
by case: eqP U=>[->|]; case: eqP=>[->|]; rewrite ?(Xa,Xb).
Qed.

End SeqRel.

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
