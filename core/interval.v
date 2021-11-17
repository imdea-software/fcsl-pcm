From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
From fcsl Require Import options prelude ordtype.

(* A somewhat systematic development of sorted list surgery *)
(* based on intervals *)

Definition ccinterval k t := [fun x => k <= x <= t].
Definition oointerval k t := [fun x => k < x < t].
Definition cointerval k t := [fun x => k <= x < t].
Definition ocinterval k t := [fun x => k < x <= t].
Notation "[ 'int' k , t ]" := (ccinterval k t)
 (at level 0, format "[ 'int'  k ,  t ]") : fun_scope.
Notation "| 'int' k , t ]" := (ocinterval k t)
 (at level 0, format "| 'int'  k ,  t ]") : fun_scope.
Notation "[ 'int' k , t |" := (cointerval k t)
 (at level 0, format "[ 'int' k , t |") : fun_scope.
Notation "| 'int' k , t |" := (oointerval k t)
 (at level 0, format "| 'int'  k ,  t |") : fun_scope.


(* various union lemmas for finite intervals *)

Lemma intUabBc a b c : a < b <= c -> predU |int a, b| [int b, c| =1 |int a, c|.
Proof.
case/andP=>H1 H2 z /=; case: (leqP b z)=>X /=.
- by rewrite (leq_trans H1 X).
by rewrite orbF (leq_trans X H2).
Qed.

Lemma intUaBbc a b c : a <= b < c -> predU |int a, b] |int b, c| =1 |int a, c|.
Proof.
case/andP=>H1 H2 z /=; case: (ltnP b z)=>X /=.
- by rewrite (leq_ltn_trans H1 X).
by rewrite orbF (leq_ltn_trans X H2).
Qed.

Lemma intUAbBc a b c : a <= b <= c -> predU [int a, b| [int b, c| =1 [int a, c|.
Proof.
case/andP=>H1 H2 z /=; case: (leqP b z)=>X /=.
- by rewrite (leq_trans H1 X).
by rewrite orbF (leq_trans X H2).
Qed.

Lemma intUABbc a b c : a <= b < c -> predU [int a, b] |int b, c| =1 [int a, c|.
Proof.
case/andP=>H1 H2 z /=; case: (ltnP b z)=>X /=.
- by rewrite (ltnW (leq_ltn_trans H1 X)).
by rewrite orbF (leq_ltn_trans X H2).
Qed.

Lemma intUabBC a b c : a < b <= c -> predU |int a, b| [int b, c] =1 |int a, c].
Proof.
case/andP=>H1 H2 z /=; case: (leqP b z)=>X /=.
- by rewrite (leq_trans H1 X).
by rewrite orbF (ltnW (leq_trans X H2)).
Qed.

Lemma intUaBbC a b c : a <= b <= c -> predU |int a, b] |int b, c] =1 |int a, c].
Proof.
case/andP=>H1 H2 z /=; case: (ltnP b z)=>X /=.
- by rewrite (leq_ltn_trans H1 X).
by rewrite orbF (leq_trans X H2).
Qed.

Lemma intUAbBC a b c : a <= b <= c -> predU [int a, b| [int b, c] =1 [int a, c].
Proof.
case/andP=>H1 H2 z /=; case: (leqP b z)=>X /=.
- by rewrite (leq_trans H1 X).
by rewrite orbF (ltnW (leq_trans X H2)).
Qed.

Lemma intUABbC a b c : a <= b <= c -> predU [int a, b] |int b, c] =1 [int a, c].
Proof.
case/andP=>H1 H2 z /=; case: (ltnP b z)=>X /=.
- by rewrite (ltnW (leq_ltn_trans H1 X)).
by rewrite orbF (leq_trans X H2).
Qed.

(* infinite intervals *)

Lemma intUabB a b : a < b -> predU |int a, b| (leq b) =1 ltn a.
Proof.
move=>H z /=; case: (leqP b z)=>X //=.
- by rewrite (leq_trans H X).
by rewrite orbF andbT.
Qed.

Lemma intUaBb a b : a <= b -> predU |int a, b] (ltn b) =1 ltn a.
Proof.
move=>H z /=; case: (ltnP b z)=>X //=.
- by rewrite (leq_ltn_trans H X).
by rewrite orbF andbT.
Qed.

Lemma intUAbB a b : a <= b -> predU [int a, b| (leq b) =1 leq a.
Proof.
move=>H z /=; case: (leqP b z)=>X //=.
- by rewrite (leq_trans H X).
by rewrite orbF andbT.
Qed.

Lemma intUABb a b : a <= b -> predU [int a, b] (ltn b) =1 leq a.
Proof.
move=>H z /=; case: (ltnP b z)=>X //=.
- by rewrite (ltnW (leq_ltn_trans H X)).
by rewrite orbF andbT.
Qed.

(* empty and singleton intervals *)

Lemma intaa a : |int a, a| =1 pred0.
Proof. by move=>z /=; case: ltngtP. Qed.

Lemma intaA a : |int a, a] =1 pred0.
Proof. by move=>z /=; case: ltngtP. Qed.

Lemma intAa a : [int a, a| =1 pred0.
Proof. by move=>z /=; case: ltngtP. Qed.

Lemma intAA a : [int a, a] =1 pred1 a.
Proof. by move=>z /=; rewrite -eqn_leq. Qed.

(* filtering wrt. union of intervals *)

(* first a definition when extension of p is smaller than extension of q *)
Definition ltn_apart (p q : pred nat) :=
  forall x y, p x -> q y -> x < y.

Lemma filter_sort_predU (s : seq nat) (p q : pred nat) :
        ltn_apart p q -> sorted ltn s ->
        filter (predU p q) s = filter p s ++ filter q s.
Proof.
move=>H; elim: s=>[|x s IH] //= P.
case Ep: (p x); case Eq: (q x)=>/=; last 1 first.
- by rewrite IH ?(path_sorted P).
- by move: (H x x Ep Eq); rewrite ltnn.
- by rewrite IH ?(path_sorted P).
rewrite IH ?(path_sorted P) //.
suff /eq_in_filter -> : {in s, p =1 pred0} by rewrite filter_pred0.
move=>z /(path_mem ltn_trans P).
by case Ez: (p z)=>//; case: ltngtP (H z x Ez Eq).
Qed.

Lemma intPabBc a b c : ltn_apart |int a, b| [int b, c|.
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_trans H1 H2. Qed.

Lemma intPaBbc a b c : ltn_apart |int a, b] |int b, c|.
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_ltn_trans H1 H2. Qed.

Lemma intPAbBc a b c : ltn_apart [int a, b| [int b, c|.
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_trans H1 H2. Qed.

Lemma intPABbc a b c : ltn_apart [int a, b] |int b, c|.
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_ltn_trans H1 H2. Qed.

Lemma intPabBC a b c : ltn_apart |int a, b| [int b, c].
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_trans H1 H2. Qed.

Lemma intPaBbC a b c : ltn_apart |int a, b] |int b, c].
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_ltn_trans H1 H2. Qed.

Lemma intPAbBC a b c : ltn_apart [int a, b| [int b, c].
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_trans H1 H2. Qed.

Lemma intPABbC a b c : ltn_apart [int a, b] |int b, c].
Proof. by move=>x y /andP [_ H1 /andP [H2 _]]; apply: leq_ltn_trans H1 H2. Qed.

#[export]
Hint Resolve intPabBc intPaBbc intPAbBc intPABbc
             intPabBC intPaBbC intPAbBC intPABbC : core.

(* a nat interval is a convex subset of nats *)
Definition convex (p : pred nat) :=
  forall a b x, a < x < b -> p a -> p b -> p x.

Lemma convab a b : convex |int a, b|.
Proof.
move=>c d x /andP [H1 H2] /andP [H3 _] /andP [_ H4] /=.
by rewrite (ltn_trans H3 H1) (ltn_trans H2 H4).
Qed.

Lemma convaB a b : convex |int a, b].
Proof.
move=>c d x /andP [H1 H2] /andP [H3 _] /andP [_ H4] /=.
by rewrite (ltn_trans H3 H1) (ltnW (leq_trans H2 H4)).
Qed.

Lemma convAb a b : convex [int a, b|.
Proof.
move=>c d x /andP [H1 H2] /andP [H3 _] /andP [_ H4] /=.
by rewrite (ltnW (leq_ltn_trans H3 H1)) (ltn_trans H2 H4).
Qed.

Lemma convAB a b : convex [int a, b].
Proof.
move=>c d x /andP [H1 H2] /andP [H3 _] /andP [_ H4] /=.
by rewrite (ltnW (leq_ltn_trans H3 H1)) (ltnW (leq_trans H2 H4)).
Qed.

Lemma conv_leq a : convex (leq a).
Proof.
by move=>c d x /andP [H1 _] H2; rewrite (ltnW (leq_ltn_trans H2 H1)).
Qed.

Lemma conv_ltn a : convex (ltn a).
Proof. by move=>c d x /andP /= [H1 _] H2; rewrite (ltn_trans H2 H1). Qed.

#[export]
Hint Resolve convab convaB convAb convAB conv_leq conv_ltn : core.

(* intersection of intervals is an interval *)

Lemma conv_predI (p1 p2 : pred nat) :
        convex p1 -> convex p2 -> convex (predI p1 p2).
Proof.
move=>H1 H2 a b x X /andP [A1 A2] /andP [B1 B2] /=.
by rewrite (H1 _ _ _ X A1 B1) (H2 _ _ _ X A2 B2).
Qed.

Lemma int_splitxX (p : pred nat) x :
        p =1 predU (predI p [int 0, x|) (predI p (leq x)).
Proof. by move=>z /=; case: ltngtP; rewrite ?(andbT,andbF,orbF). Qed.

Lemma int_splitXx (p : pred nat) x :
        p =1 predU (predI p [int 0, x]) (predI p (ltn x)).
Proof. by move=>z /=; case: ltngtP; rewrite ?(andbT,andbF,orbF). Qed.

Lemma int_splitax a x b :
        x <= b -> |int a, x| =1 predI |int a, b| [int 0, x|.
Proof.
move=>H z /=; rewrite andbAC [RHS]andbC; case: (ltnP z b)=>//=.
by move/(leq_trans H); rewrite andbC ltnNge=>->.
Qed.

Lemma int_splitxb a x b :
        a <= x -> |int x, b| =1 predI |int a, b| (ltn x).
Proof.
move=>H z /=; rewrite [RHS]andbC; case: (ltnP x z)=>//=.
by move/(leq_ltn_trans H)=>->.
Qed.

(* a sorted list has no element bigger than its max/last element *)
Lemma has_max_ltn (s : seq nat) :
        sorted ltn s -> ~~ has (ltn (last 0 s)) s.
Proof.
move=>S; apply/hasPn=>z Z; rewrite -leqNgt leq_eqVlt.
by apply: sorted_last_key_max ltn_trans S Z.
Qed.

(* the same expressed with leq *)
Lemma has_max_leq (s : seq nat) :
        sorted ltn s -> {in s, leq (last 0 s) =1 pred1 (last 0 s)}.
Proof.
move=>S z /=; case:ltngtP=>// Z /(sorted_last_key_max 0 ltn_trans S).
by case: ltngtP Z.
Qed.

(* a sorted list has no element smaller than its min/first element *)
Lemma has_min (s : seq nat) :
        sorted ltn s -> ~~ has [int 0, head 0 s| s.
Proof.
move=>S; apply/hasPn=>z Z /=; rewrite -leqNgt.
case: s S Z=>[|x s] //= P; rewrite inE; case/orP=>[/eqP ->|] //.
by move/(path_mem ltn_trans P)/ltnW.
Qed.

Lemma sorted_max_filter (s : seq nat) p :
        sorted ltn s -> has p s ->
        exists x, [/\ filter p s = filter (predI p [int 0, x|) s ++ [:: x],
                      p x & ~~ has (predI p (ltn x)) s].
Proof.
move=>S; rewrite -{1}[s]filter_predT has_filter filter_swap -has_filter.
case/hasP=>_ /(last_in 0) Hn _; set x := last 0 (filter p s) in Hn.
move: (Hn); rewrite mem_filter=>/andP [P Hx]; exists x.
rewrite (eq_filter (int_splitxX p x)) filter_sort_predU //; last first.
- by move=>a b /= /andP [_ H] /andP [_ /(leq_trans H)].
split=>//; last first.
- rewrite has_filter filter_predI filter_swap -has_filter has_max_ltn //.
  by rewrite (sorted_filter ltn_trans _ S).
congr (_ ++ _); rewrite filter_predIC filter_predI.
rewrite (eq_in_filter (has_max_leq (sorted_filter ltn_trans _ S))).
by rewrite filter_pred1_uniq // filter_uniq // (sorted_uniq ltn_trans ltnn S).
Qed.

(* special case of the above lemma when p is an open interval *)
Lemma sorted_max_count (s : seq nat) a b :
        sorted ltn s -> count |int a, b| s > 0 ->
        exists x, [/\ count |int a, x| s = (count |int a, b| s).-1,
                      x \in s, a < x < b & ~~ has |int x, b| s].
Proof.
move=>S; rewrite -has_count=>/(sorted_max_filter S) [x][/= H1 H2 H3].
exists x; split=>//; last 1 first.
- by apply: contra H3; apply: sub_has=>z; case/andP: H2=>/ltnW/int_splitxb ->.
- rewrite -!size_filter H1 size_cat addnS addn0 !size_filter.
  by apply: eq_count; apply: int_splitax (ltnW _); case/andP: H2.
have : x \in filter |int a, b| s by rewrite H1 mem_cat orbC inE eq_refl.
by rewrite mem_filter=>/andP [].
Qed.
