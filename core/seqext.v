(*
Copyright 2013 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From Stdlib Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype path choice fintype bigop perm.
From pcm Require Import options prelude pred seqperm.

(*********************)
(* Extensions to seq *)
(*********************)

(* TODO upstream to mathcomp *)

Lemma inj_cons {A} {a1 a2} {s1 s2 : seq A} : 
         cons a1 s1 = cons a2 s2 -> 
         a1 = a2 /\ s1 = s2.
Proof. by case. Qed.

Lemma inj_consE {A : eqType} {x1 x2} {xs1 xs2 : seq A} :
        (x1 :: xs1 == x2 :: xs2) = (x1 == x2) && (xs1 == xs2).
Proof. by []. Qed.

Lemma revE {A} {s1 s2 : seq A} : 
        rev s1 = s2 <-> s1 = rev s2.
Proof. by split=>[<-|->]; rewrite revK. Qed.

Lemma rev_eqseq {A : eqType} {s1 s2 : seq A} : 
        (rev s1 == s2) = (s1 == rev s2).
Proof. by apply/idP/idP=>/eqP/revE/eqP. Qed.

Lemma inj_rev {A} : injective (@rev A).
Proof. by move=>s1 s2 /revE; rewrite revK. Qed.

Lemma head_rcons {A} (s : seq A) (x y : A) : 
        head x (rcons s y) = head y s.
Proof. by rewrite headI. Qed.

Lemma rcons_nseq {A} n (x : A) :
        rcons (nseq n x) x = nseq n.+1 x.
Proof. by elim: n=>//=n ->. Qed.

Lemma behead_rcons {A} (xs : seq A) x :
        0 < size xs ->
        behead (rcons xs x) = rcons (behead xs) x.
Proof. by case: xs. Qed.

Lemma nilp_hasPn {A} (s : seq A) : nilp s = ~~ has predT s.
Proof. by case: s. Qed.

Lemma filter_predIC {A} (s : seq A) p1 p2 :
         filter (predI p1 p2) s = filter (predI p2 p1) s.
Proof. by apply: eq_filter => z /=; rewrite andbC. Qed.

Lemma filter_swap {A} (s : seq A) p1 p2 :
        filter p1 (filter p2 s) = filter p2 (filter p1 s).
Proof. by rewrite -!filter_predI filter_predIC. Qed.

Lemma map_nilp {A B} (f : A -> B) (s : seq A) : 
        nilp (map f s) = nilp s.
Proof. by rewrite /nilp; case: s. Qed.

Lemma filter_nilp {A} (p : pred A) (s : seq A) : 
        nilp (filter p s) = ~~ has p s.
Proof. by rewrite /nilp size_filter -leqn0 leqNgt has_count. Qed.

Lemma head_map {P Q} (f : P -> Q) z (s : seq P) :
        f (head z s) = head (f z) (map f s).
Proof. by case: s. Qed.

Lemma zip_map2 {P Q R S} (f : P -> R) (g : Q -> S) (s1 : seq P) (s2 : seq Q) :
        zip (map f s1) (map g s2) =
        map (fun '(x1,x2) => (f x1,g x2)) (zip s1 s2).
Proof.
elim: s1 s2=>/= [|x1 s1 IH] [|x2 s2] //=.
by congr cons.
Qed.

Lemma zip_mapl {P Q R} (f : P -> R) (s1 : seq P) (s2 : seq Q) :
        zip (map f s1) s2 =
        map (fun '(x1,x2) => (f x1,x2)) (zip s1 s2).
Proof. by rewrite -{1}(map_id s2) zip_map2. Qed.

Lemma zip_mapr {P Q S} (g : Q -> S) (s1 : seq P) (s2 : seq Q) :
        zip s1 (map g s2) =
        map (fun '(x1,x2) => (x1,g x2)) (zip s1 s2).
Proof. by rewrite -{1}(map_id s1) zip_map2. Qed.

Lemma drop_take_id {A} x (s : seq A) : drop x (take x s) = [::].
Proof. by rewrite -{2}(add0n x) -take_drop take0. Qed.

Lemma drop_take_mask {A} (s : seq A) x y :
        drop x (take y s) = mask (nseq x false ++ nseq (y-x) true) s.
Proof.
case: (ltnP x (size s))=>Hx; last first.
- rewrite drop_oversize; first by rewrite size_take_min geq_min Hx orbT.
  rewrite -{1}(subnKC Hx) nseqD -catA -{3}(cats0 s) mask_cat; first by rewrite size_nseq.
  by rewrite mask0 mask_false.
have Hx': size (nseq x false) = size (take x s).
- by rewrite size_nseq size_take_min; symmetry; apply/minn_idPl/ltnW.
rewrite -{2}(cat_take_drop x s) mask_cat // mask_false /= -takeEmask take_drop.
case: (leqP x y)=>[Hxy|/ltnW Hxy]; first by rewrite subnK.
move: (Hxy); rewrite -subn_eq0=>/eqP->; rewrite add0n drop_take_id.
by rewrite drop_oversize // size_take_min geq_min Hxy.
Qed.

Lemma catl_cancel {A} {x1 y1 x2 y2 : seq A} : 
        size x1 = size y1 ->
        x1 ++ x2 = y1 ++ y2 -> 
        x1 = y1 /\ x2 = y2.
Proof. 
move=>S /[dup] /(f_equal (take (size x1))).
rewrite {2}S !take_size_cat // => ->.
by move/(f_equal (drop (size y1))); rewrite !drop_size_cat.
Qed.

Lemma catr_cancel {A} {x1 y1 x2 y2 : seq A} : 
        size x2 = size y2 ->
        x1 ++ x2 = y1 ++ y2 -> 
        x1 = y1 /\ x2 = y2.
Proof. 
move=>S /(f_equal rev); rewrite !rev_cat. 
case/catl_cancel=>[|/inj_rev -> /inj_rev//].
by rewrite !size_rev.
Qed.

Lemma hasN_count {A} {f : {pred A}} {xs} : 
        reflect (count f xs = 0) (~~ has f xs).
Proof. by rewrite has_count -leqNgt leqn0; apply: eqP. Qed.

Lemma hasN_filter {A} {f : {pred A}} {xs} : 
        reflect (filter f xs = [::]) (~~ has f xs).
Proof. by rewrite -filter_nilp; apply: (iffP nilP). Qed.

Lemma count_filter0 {A} {f : {pred A}} {xs} : 
        count f xs = 0 <-> filter f xs = [::].
Proof. by rewrite -size_filter; split=>[/size0nil|->]. Qed.

Lemma count_pmap0 {A B} {f : A -> option B} {xs} :
        count f xs = 0 <-> pmap f xs = [::].
Proof. by elim: xs=>[|x xs IH] //=; rewrite /oapp; case: (f x). Qed.

Lemma hasN_pmap {A B} {f : A -> option B} {xs} : 
        reflect (pmap f xs = [::]) (~~ has f xs).
Proof. by apply: (iffP hasN_count)=>/count_pmap0. Qed.

Lemma count_rcons A (f : {pred A}) x (xs : seq A) : 
        count f (rcons xs x) = (count f xs + f x)%N.
Proof. by rewrite -count_rev rev_rcons /= addnC count_rev. Qed.

Lemma has_first_split A (f : {pred A}) (xs : seq A) : 
        has f xs -> 
        exists x p1 p2, 
        [/\ xs = rcons p1 x ++ p2, f x & ~~ has f p1].
Proof.
elim: xs=>[|x xs IH] //=.
case F : (f x); first by exists x, [::], xs. 
case/IH=>x0 [p1][p2][-> H H1].
by exists x0, (x :: p1), p2; rewrite /= F H1.
Qed.

Lemma has_last_split A (f : {pred A}) (xs : seq A) : 
        has f xs ->
        exists x p1 p2, 
        [/\ xs = rcons p1 x ++ p2, f x & ~~ has f p2].
Proof.
rewrite -has_rev=>/has_first_split [x][p1][p2][/revE E H1 H2].
exists x, (rev p2), (rev p1). 
by rewrite E rev_cat rev_rcons cat_rcons has_rev.
Qed.

Lemma count1_split A (f : {pred A}) (xs : seq A) : 
        count f xs = 1 -> 
        exists x p1 p2, 
        [/\ xs = rcons p1 x ++ p2, f x, ~~ has f p1 & ~~ has f p2].
Proof.
move=>C; have H : has f xs by rewrite has_count C.
case/has_first_split: H C=>x [p1][p2][->{xs} H1 H2].
rewrite count_cat count_rcons H1 (hasN_count H2) add0n add1n.
by case=>/hasN_count; exists x, p1, p2.
Qed.

Lemma count_splitE A (f : {pred A}) (x1 x2 : A) p1 p2 q1 q2 : 
        ~~ has f p1 ->
        ~~ has f q1 ->
        f x1 -> 
        f x2 ->
        p1 ++ x1 :: q1 = 
        p2 ++ x2 :: q2 ->
        [/\ p1 = p2, x1 = x2 & q1 = q2].
Proof.
elim: p1 x1 q1 p2 x2 q2=>[|a1 p1 IH] x1 q1 p2 x2 q2 Hp Hq F1 F2 /= E.
- case: p2 E Hq=>[|a2 p2] /=; first by case.
  by case=>->->; rewrite has_cat /= F2 orbT.
case: p2 E Hp=>[|a2 p2] /=; first by case=>->; rewrite F2.
case=><-{a2} E; rewrite negb_or=>/andP [_ Hp].
by case/(IH _ _ _ _ _ Hp Hq F1 F2): E=>->.
Qed.

Lemma pmap_rcons {A B} {f : A -> option B} {xs x} :
        pmap f (rcons xs x) = 
        if f x is Some y then rcons (pmap f xs) y else pmap f xs.
Proof.
by elim: xs x=>[|y ys IH] x //=; rewrite /oapp IH; case: (f x); case: (f y).
Qed.

Lemma pmap_rev {A B} {f : A -> option B} {xs} :
        pmap f (rev xs) = rev (pmap f xs).
Proof.
elim: xs=>[|x xs IH] //=; rewrite /oapp rev_cons pmap_rcons IH. 
by case: (f x)=>[a|//]; rewrite rev_cons.
Qed.

Lemma sorted_cat {A} (ord : rel A) (xs1 xs2 : seq A) : 
        transitive ord ->
        sorted ord (xs1 ++ xs2) ->
        forall k, k \In xs1 -> all (ord k) xs2.
Proof.
move=>Tr S k K; case/In_split: K S=>s1 [s2 ->].
rewrite -catA sorted_cat_cons /=; case/andP=>_ /(order_path_min Tr).
by rewrite all_cat; case/andP.
Qed.

Lemma iotaDr m1 m2 n : iota (m1 + m2) n = map (addn^~ m1) (iota m2 n).
Proof. by rewrite iotaDl; apply: eq_map=>x; rewrite addnC. Qed.

Section LemmasEq.
Context {A : eqType}.
Implicit Type xs : seq A.

Lemma eqnil xs : xs =i [::] -> xs = [::].
Proof. by case: xs=>// x xs /(_ x); rewrite inE eqxx. Qed.

Lemma revA xs1 xs2 : rev xs1 == xs2 -> all [mem xs1] xs2.
Proof.
elim: xs2 xs1=>[|x2 xs2 IH] //=.
case/lastP=>[|xs1 x1] //=.
rewrite rev_rcons=>/eqP [->{x1}] /eqP /IH /allP X. 
rewrite mem_rcons inE eqxx /=. 
by apply/allP=>z /X /= Z; rewrite mem_rcons inE Z orbT.
Qed.

(* With A : Type, we have the In_split lemma. *)
(* With A : eqType, the lemma can be strenghtened to *)
(* not only return the split of xs, but the split of xs *)
(* that uses the first occurrence of x is xs *)
Lemma in_split xs x :
        x \in xs -> 
        exists xs1 xs2, 
          xs = xs1 ++ x :: xs2 /\ x \notin xs1.
Proof.
rewrite -has_pred1; case/split_find=>_ s1 s2 /eqP ->.
by rewrite has_pred1=>H; exists s1, s2; rewrite -cats1 -catA.
Qed.

(* a weaker form of in_split *)
Lemma mem_split (x : A) s :
        x \in s -> 
        exists s1 s2, s = s1 ++ [:: x] ++ s2.
Proof. by case/in_split=>s1 [s2][H _]; exists s1, s2. Qed.

Lemma mem_split_uniq (x : A) s :
       x \in s -> uniq s ->
       exists s1 s2, [/\ s = s1 ++ [:: x] ++ s2,
                         uniq (s1 ++ s2) &
                         x \notin s1 ++ s2].
Proof.
move=>/[swap] Hu /mem_split [s1 [s2 H]].
exists s1, s2; move: Hu.
by rewrite H uniq_catCA cons_uniq; case/andP.
Qed.

Lemma perm_cons2 (x y : A) s : 
        perm_eq [:: x, y & s] [:: y, x & s].
Proof.
by rewrite (_ : [::x,y & s] = [::x] ++ [::y] ++ s) //
  (_ : [::y,x & s] = [::y] ++ [::x] ++ s) // perm_catCA.
Qed.

Lemma perm1P {s : seq A} (x : A) :
        reflect (s = [:: x]) (perm_eq s [:: x]).
Proof. by apply: (iffP idP)=>[/perm_eq_perm/pperm1|->]. Qed.

Lemma undup_eq1 (x : A) xs :
        xs =i [:: x] <-> undup xs = [:: x].
Proof.
split=>[/perm_undup/perm1P ->//|].
by move/perm1P/perm_mem=>H z; rewrite -mem_undup H.
Qed.

Lemma permeq_filterC p (s : seq A) : 
        perm_eq s (filter p s ++ filter (predC p) s).
Proof. by rewrite perm_sym; apply/permEl/perm_filterC. Qed.

Lemma filter_subseq_in (s1 s2 : seq A) : 
        uniq s2 ->
        subseq s1 s2 ->
        filter [in s1] s2 = s1.
Proof.
elim: s2 s1=>[|x s2 IH] s1 /= U; first by move/eqP=>->.
case: s1=>[_|y s1] /=; first by rewrite filter_pred0. 
case/andP: U=>N U; case: ifPn=>[/eqP ->{y}|Nyx S].
- rewrite inE eqxx /= => /(IH _ U) {2}<-. 
  congr cons; apply: eq_in_filter=>z Z; rewrite inE.
  by case: eqP Z N=>//= ->->.
have Nx : x \notin s1.
- by apply: contra N=>N; rewrite (mem_subseq S) // inE N orbT.
by rewrite inE eq_sym (negbTE Nyx) (negbTE Nx) (IH _ U S).
Qed.

Lemma perm_subseq (r1 r2 r s : seq A) : 
        uniq r ->
        perm_eq r (r1 ++ r2) ->
        subseq s r ->
        exists s1 s2, 
          [/\ perm_eq s (s1 ++ s2), 
              subseq s1 r1 & 
              subseq s2 r2].
Proof.
move=>U P S; set s1 := filter (mem s) r1; set s2 := filter (mem s) r2.
exists s1, s2; split; try by apply: filter_subseq.
by rewrite -filter_cat -{1}(filter_subseq_in _ S) // perm_filter.
Qed.

Lemma rcons_subseq (s : seq A) (x : A) : 
        subseq [:: x] (rcons s x).
Proof.
elim: s=>[|a s IH] // /=; case: (x =P a)=>[->|//].
by apply: sub0seq.
Qed.

Lemma split_subseq x (s1 s2 : seq A) : 
        subseq (x :: s1) s2 <-> 
        exists a1 a2, [/\ s2 = a1 ++ x :: a2 & subseq s1 a2].
Proof.
split; last first.
- case=>a1 [a2][->{s2} S].
  by rewrite -[x :: s1]cat0s cat_subseq ?sub0seq //= eqxx.
elim: s2 s1 x=>[|y s2 IH] s1 x //=.
case: ifPn=>[/eqP <-{y}|_]; first by exists [::], s2.
by case/IH=>a1 [a2][E1 E2]; exists (y :: a1), a2; rewrite /= -E1. 
Qed.

Lemma undup_uniq_eq1 (x : A) xs :
        uniq xs ->
        xs =i [:: x] <-> xs = [:: x].
Proof. by rewrite undup_eq1=>/undup_id ->. Qed.

Lemma all_notin (p : pred A) xs y :
        all p xs -> 
        ~~ p y -> 
        y \notin xs.
Proof. by move/allP=>Ha; apply/contra/Ha. Qed.

Lemma in_consE P x xs : 
        {in x :: xs, forall z, P z} <->
        P x /\ {in xs, forall z, P z}.
Proof. 
split=>[H|[H1 H2]]; last by move=>z /orP [/eqP ->|/H2].
split=>[|z Z]; first by apply: H; rewrite inE eqxx.
by apply: H; rewrite inE Z orbT.
Qed.

Lemma subset_all a (s1 s2 : seq A) : 
        {subset s1 <= s2} -> 
        all a s2 -> 
        all a s1.
Proof. by move=>Hs /allP Ha1; apply/allP=>s /Hs /Ha1. Qed.

Lemma subset_nilR xs :
        {subset xs <= [::]} -> 
        xs = [::].
Proof. by case: xs=>// x xs /(_ x); rewrite inE eqxx=>/(_ erefl). Qed.

Lemma subset_nil xs ys :
        {subset xs <= ys} -> 
        ys = [::] -> 
        xs = [::].
Proof. by move=>X E; move: E X=>->; apply: subset_nilR. Qed.

Lemma subset_consL x (s1 s2 : seq A) :
        {subset x :: s1 <= s2} <->
        x \in s2 /\ {subset s1 <= s2}.
Proof.
split=>[S|[X S]].
- by split=>[|z Z]; apply: S; rewrite inE ?eqxx ?Z ?orbT.
by move=>z; rewrite inE; case/orP=>[/eqP ->|/S//].
Qed.

Lemma subset_consLI x (s1 s2 : seq A) : 
        x \in s2 ->
        {subset s1 <= s2} ->
        {subset x :: s1 <= s2}.
Proof. by move=>H1 H2; rewrite subset_consL. Qed.

Lemma subset_consR x (s : seq A) : 
        {subset s <= x :: s}.
Proof. by move=>z E; rewrite inE E orbT. Qed.

Lemma subset_consLR x (s1 s2 : seq A) : 
        {subset s1 <= s2} ->
        {subset x :: s1 <= x :: s2}.
Proof.
move=>X z; rewrite !inE; case/orP=>[|/X] -> //.
by rewrite orbT.
Qed.

Lemma subset_catL (s1 s2 : seq A) :
        {subset s1 <= s1 ++ s2}.
Proof. by move=>x S; rewrite mem_cat S. Qed.

Lemma subset_catR (s1 s2 : seq A) :
        {subset s2 <= s1 ++ s2}.
Proof. by move=>x S; rewrite mem_cat S orbT. Qed.

Lemma all_mem xs ys : 
        reflect {subset ys <= xs} (all [mem xs] ys).
Proof. 
by case: allP=>H; constructor; [move=>x /H | move=>X; apply: H=>x /X]. 
Qed.

Lemma all_predC_sym xs ys :
        all [predC xs] ys = all [predC ys] xs.
Proof. by rewrite all_predC has_sym -all_predC. Qed.

Lemma nilp_filter (p : pred A) s :
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

Lemma index_rcons a x xs :
        index a (rcons xs x) =
        if a \in xs then index a xs else
          if a == x then size xs else (size xs).+1.
Proof.
rewrite eq_sym; elim: xs=>[|y xs IH] //=.
rewrite inE eq_sym; case: eqP=>//= _.
by rewrite IH; case: ifP=>// _; case: eqP.
Qed.

Lemma index_memN x xs :
        x \notin xs <-> index x xs = size xs.
Proof.
split; first by exact: memNindex.
by move=>E; rewrite -index_mem E ltnn.
Qed.

Lemma index_sizeE x xs :
        reflect (index x xs = size xs) (x \notin xs).
Proof. by apply/(equivP idP)/index_memN. Qed.

Lemma size0nilP xs :
        reflect (xs = [::]) (size xs == 0).
Proof.
case: eqP=>X; constructor; first by move/size0nil: X.
by move=>N; rewrite N in X.
Qed.

Lemma size1cons (xs : seq A) :
        size xs = 1 ->
        exists x, xs = [:: x].
Proof. by case: xs=>[//|x xs][/size0nil ->]; exists x. Qed.

Lemma has_nilP xs :
        reflect (has predT xs) (xs != [::]).
Proof. by case: xs=>[|x xs]; constructor. Qed.

Lemma map_nilP {B : eqType} (f : B -> A) s :
        reflect (exists k, k \in map f s) (map f s != [::]).
Proof.
case: has_nilP=>X; constructor.
- by case/hasP: X=>x; exists x.
by case=>k K; elim: X; apply/hasP; exists k.
Qed.

Lemma all_filterPC T (a : pred T) (s : seq T) : 
         reflect (filter a s = [::]) (all (predC a) s).
Proof.
case: all_filterP=>H; constructor.
- rewrite -H -filter_predI -(filter_pred0 s).
  by apply: eq_filter=>z; rewrite inE andbN.
move=>E; apply: H; elim: s E=>[|x s IH] //=.
by case: ifP=>//= E /IH ->. 
Qed.

Lemma filter_nilP (p : pred A) xs :
        reflect (forall x, p x -> x \in xs -> false)
                ([seq x <- xs | p x] == [::]).
Proof.
case: eqP=>E; constructor.
- move=>x H1 H2; suff : x \in [seq x <- xs | p x] by rewrite E.
  by rewrite mem_filter H1 H2.
move=>H; apply: E; apply: size0nil; apply/eqP; rewrite size_filter.
by rewrite eqn0Ngt -has_count; apply/hasPn=>x /H; case: (p x)=>//; apply.
Qed.

Lemma filter_pred1 x xs :
        x \notin xs -> 
        filter (pred1 x) xs = [::].
Proof.
move=>H; apply/eqP; apply/filter_nilP=>z /eqP ->.
by rewrite (negbTE H).
Qed.

Lemma filter_predC1 x xs :
        x \notin xs -> 
        filter (predC1 x) xs = xs.
Proof.
by move=>H; apply/all_filterP/allP=>y /=; case: eqP=>// ->; apply/contraL.
Qed.

Lemma filter_mem_sym (s1 s2 : seq A) :
        filter (mem s1) s2 =i filter (mem s2) s1.
Proof. by move=>x; rewrite !mem_filter andbC. Qed.

Lemma has_filterI (p q : pred A) (s : seq A) : 
        has p (filter q s) = has (predI p q) s.
Proof. by rewrite has_filter -filter_predI -has_filter. Qed.

Lemma filter_sub p (s : seq A) : 
        {subset s <= p} ->
        filter p s = s.
Proof. by move=>S; rewrite -[RHS]filter_predT; apply: eq_in_filter. Qed.

Lemma filter_in (s : seq A) : 
        filter [in s] s = s.
Proof. by apply: filter_sub. Qed.

Lemma inj_index xs x y :
        x \in xs -> 
        index x xs = index y xs -> 
        x = y.
Proof.
elim: xs=>[|k xs IH] //=; rewrite inE eq_sym.
case: eqP=>[->{k} _|_ /= S]; case: eqP=>// _ []; apply: IH S.
Qed.

Lemma cat_cancel (xs1 xs2 ys1 ys2 : seq A) (k : A) :
        k \notin xs1 -> k \notin xs2 ->
        xs1 ++ k :: ys1 = xs2 ++ k :: ys2 ->
        (xs1 = xs2) * (ys1 = ys2).
Proof.
move=>Nk1 Nk2 E.
have Es : size xs1 = size xs2.
- have : index k (xs1++k::ys1) = index k (xs2++k::ys2) by rewrite E.
  by rewrite !index_cat /= (negbTE Nk1) (negbTE Nk2) eqxx !addn0.
have Ex : xs1 = take (size xs1) (xs1 ++ k :: ys1).
- by rewrite take_cat ltnn subnn /= cats0.
rewrite E Es take_cat ltnn subnn /= cats0 in Ex.
rewrite {xs1 Nk1 Es}Ex in E *.
have : ys1 = drop (size (xs2++[::k])) (xs2++k::ys1).
- by rewrite drop_cat size_cat /= addn1 ltnNge ltnW //= subSn // subnn /= drop0.
by rewrite E drop_cat size_cat /= addn1 ltnNge ltnW //= subSn // subnn /= drop0.
Qed.

(* if the list is not empty, the default value in head doesn't matter *)
Lemma head_dflt (x1 x2 x : A) xs :
        x \in xs -> 
        head x1 xs = head x2 xs.
Proof. by case: xs. Qed.

Lemma head_mem (x : A) xs : head x xs \in x :: xs.
Proof. by case: xs=>[|y ys]; rewrite !inE //= eqxx orbT. Qed.

(* a common pattern of using mem_head that avoids forewriteard reasoning *)
Lemma mem_headI (x : A) xs a :
        a = head x xs -> 
        a \in x :: xs.
Proof. by move=>->; apply: head_mem. Qed.

Lemma head_nilp (x : A) xs :
        x \notin xs -> 
        head x xs = x -> 
        nilp xs.
Proof.
elim: xs=>[|y ys IH] //= H1 H2.
by rewrite H2 inE eqxx /= in H1.
Qed.

Lemma head_notin (x y : A) xs :
        y \in xs -> 
        x \notin xs -> 
        head x xs != x.
Proof.
move=>Y X; apply/negP=>/eqP; move/(head_nilp X)/nilP=>E.
by rewrite E in Y.
Qed.

(* weaker form of in_mask *)
(* TODO upstream to mathcomp *)
Lemma in_mask_count x m xs :
        count_mem x xs <= 1 ->
        (x \in mask m xs) = (x \in xs) && nth false m (index x xs).
Proof.
elim: xs m => [|y xs IHs] m /=; first by rewrite mask0 in_nil.
case: m=>/=[|b m]; first by rewrite in_nil nth_nil andbF.
case: b; rewrite !inE eq_sym; case: eqP=>//= _.
- by rewrite add0n; apply: IHs.
- rewrite -{2}(addn0 1%N) leq_add2l leqn0 => /eqP Hc.
  rewrite IHs; first by rewrite Hc.
  by move/count_memPn/negbTE: Hc=>->.
by rewrite add0n; apply: IHs.
Qed.

Lemma mem_take_index x xs :
        x \notin take (index x xs) xs.
Proof.
elim: xs=>//=h xs; case: eqP=>//= /eqP H IH.
by rewrite inE negb_or eq_sym H.
Qed.

Lemma prefix_drop_sub (s1 s2 : seq A) :
        prefix s1 s2 ->
        forall n, {subset (drop n s1) <= drop n s2}.
Proof.
case/seq.prefixP=>s0 {s2}-> n x H.
rewrite drop_cat; case: ltnP=>Hn.
- by rewrite mem_cat H.
by move: H; rewrite drop_oversize.
Qed.

Lemma rcons_prefix (s1 s2 : seq A) x : 
        prefix s1 (rcons s2 x) ->
        prefix s1 s2 \/ s1 = rcons s2 x.
Proof.
elim: s1 s2 x=>[|y s1 IH] s2 x; first by left; rewrite prefix0s. 
case: s2=>[|y' s2] /= /andP [/eqP ->].
- by case: s1 {IH}=>//; right. 
by rewrite eqxx=>/IH [|/= ->]; [left|right].
Qed.

Lemma prefix_sub (s1 s2 : seq A) :
        prefix s1 s2 -> 
        {subset s1 <= s2}.
Proof. by case/prefixP=>s2' ->; apply: subset_catL. Qed.

Lemma prefix_subT (s1 s2 s3 : seq A) : 
        prefix s1 s2 ->
        {subset s2 <= s3} ->
        {subset s1 <= s3}.
Proof. by move/prefix_sub=>H1 H2 x /H1/H2. Qed.

Lemma prefix_cat (xs ys1 ys2 : seq A) : 
        prefix xs (ys1 ++ ys2) = 
        if size xs < size ys1 then prefix xs ys1 
        else (ys1 == take (size ys1) xs) && 
             prefix (drop (size ys1) xs) ys2.
Proof.
rewrite !prefixE take_cat size_drop; case: ltnP=>// N.
by rewrite -{2}(cat_take_drop (size ys1) xs) eqseq_cat // size_takel.
Qed.

Lemma prefix_catl (xs ys1 ys2 : seq A) : 
        prefix xs (ys1 ++ ys2) = 
        if size xs <= size ys1 then prefix xs ys1 
        else (ys1 == take (size ys1) xs) && 
             prefix (drop (size ys1) xs) ys2.
Proof.
rewrite prefix_cat prefixE; case: ltngtP=>// E. 
by rewrite -E {3}E !take_size drop_size prefix0s andbT.
Qed.

Lemma prefix_catP (xs ys1 ys2 : seq A) : 
        reflect (prefix xs ys1 \/ 
                 exists2 xs2, xs = ys1 ++ xs2 & prefix xs2 ys2)
                (prefix xs (ys1 ++ ys2)).
Proof.
rewrite prefix_catl; case: leqP=>N.
- case D: (prefix xs ys1); constructor; first by left.
  case=>//; case=>xs2 E; move: E N D=>->.
  rewrite size_cat -leq_subRL // subnn leqn0. 
  by move/eqP/size0nil=>->; rewrite cats0 prefix_refl.
case: andP=>[[/eqP H1 H2]|H]; constructor.
- right; exists (drop (size ys1) xs)=>//.
  by rewrite {1}H1 cat_take_drop. 
case=>[/size_prefix|[xs2 E P]]; first by case: ltngtP N.
by apply: H; rewrite E take_size_cat // drop_size_cat.
Qed.

Lemma suffix_cat (xs ys1 ys2 : seq A) : 
        suffix xs (ys1 ++ ys2) = 
        if (size xs < size ys2)%N then suffix xs ys2 
        else (ys2 == drop (size xs - size ys2) xs) && 
             suffix (take (size xs - size ys2) xs) ys1.
Proof.
rewrite /suffix rev_cat prefix_cat !size_rev; case: ltnP=>// N.
by rewrite rev_eqseq !rev_take size_rev revK subKn.
Qed.

Lemma suffix_catl (xs ys1 ys2 : seq A) : 
        suffix xs (ys1 ++ ys2) = 
        if (size xs <= size ys2)%N then suffix xs ys2 
        else (ys2 == drop (size xs - size ys2) xs) && 
             suffix (take (size xs - size ys2) xs) ys1.
Proof.
rewrite suffix_cat; case: ltngtP=>// E; rewrite [RHS]suffixE {}E.
by rewrite subnn !drop0 take0 suffix0s andbT.
Qed.

Lemma suffix_catP (xs ys1 ys2 : seq A) : 
        reflect (suffix xs ys2 \/ 
                 exists2 xs1, xs = xs1 ++ ys2 & suffix xs1 ys1)
                (suffix xs (ys1 ++ ys2)).
Proof.
rewrite /suffix rev_cat; apply: (iffP (prefix_catP _ _ _)).
- case=>[|[xs2] /revE ->]; first by left.
  by right; exists (rev xs2); rewrite ?rev_cat 1?revK.
case=>[|[xs1 ->]]; first by left.
by right; exists (rev xs1)=>//; rewrite rev_cat.
Qed.

Lemma suffix_sub (s1 s2 : seq A) : 
        suffix s1 s2 -> 
        {subset s1 <= s2}.
Proof. by move/prefix_sub=>S x; rewrite -mem_rev=>/S; rewrite mem_rev. Qed.

End LemmasEq.




(* lemmas about prev and next should generally by proved using *)
(* prev_nth and next_nth, but sometimes we can also prove them *)
(* directly by setting up the right induction *)

Lemma prevE (T : eqType) (s : seq T) (p x : T) : 
        prev_at p x x s = prev (x :: s) p.
Proof. by []. Qed.

Lemma nextE (T : eqType) (s : seq T) (p x : T) : 
        next_at p x x s = next (x :: s) p.
Proof. by []. Qed.

(* prev starts counting occurrences of p from the second position; *)
(* the first position is counted as last; that's the meaning *)
(* of considering the sequence argument as a cycle *)
Lemma prev_cons (T : eqType) (s : seq T) x y p :
        prev (x :: y :: s) p = 
        if p == y then x else 
          if p \in s then prev (y :: s) p else 
            if p == x then last y s else p.
Proof.
rewrite !prev_nth !inE orbC /= (eq_sym y); case: (p =P y)=>//= /eqP Npy.
have [S|/index_sizeE ->/=] := boolP (p \in s).
- by apply: set_nth_default; rewrite ltnW // ltnS index_mem. 
by case: (p =P x)=>// <-{x}; rewrite -last_nth.
Qed.

Lemma next_rcons (T : eqType) (s : seq T) a b c :
        next (rcons (rcons s a) b) c =
        if c \in s then next (rcons s a) c else 
          if c == a then b else 
            if c == b then head a s else c.
Proof. 
case: s=>[|y s] //=; rewrite inE. 
by elim: s y {2 3 5}y=>[|x s IH] y y' /=; case: (c =P y').
Qed.

Lemma prevat_rcons (T : eqType) (s : seq T) a b c :
        (* prev (a :: rcons s b) c *)
        prev_at c a a (rcons s b) =
        if c \in s then prev (a :: s) c
        else if c == b then last a s
             else if c == a then b else c.
Proof.  
rewrite /prev /=; elim: s a {2 4 5}a=>[|x s IH] a a'//=.
by rewrite inE; case: (c =P x).
Qed.

Lemma nextat_rcons (T : eqType) (s : seq T) a b c : 
        (* next (rcons (a :: s) b) c = *)
        next_at c a a (rcons s b) =   
        if c == a then head b s 
        else if c \in s then next (rcons s b) c
             else if c == b then a else c.
Proof. 
rewrite nextE !next_nth inE /= eq_sym.
case: (a =P c)=>[->|/eqP N] /=; first by rewrite nth0 head_rcons. 
rewrite mem_rcons inE orbC index_rcons.
case C: (c \in s)=>//=; last first.
- by case: (c =P b)=>// <-; rewrite nth_default // size_rcons.
case: s C=>//= x s; rewrite inE eq_sym.
case: (x =P c)=>[-> _|/eqP Nc /= C]; first by rewrite !nth0 !head_rcons. 
by apply: set_nth_default; rewrite size_rcons ltnS index_mem C.
Qed.

(* decidable sequence disjointness *)

Definition disjoint {A : eqType} (s1 s2 : seq A) := 
  all (fun x => x \notin s1) s2.

Arguments disjoint {A} : simpl never.

Lemma disjointC {A : eqType} (s1 s2 : seq A) :
        disjoint s1 s2 = disjoint s2 s1.
Proof. 
apply/idP/idP=>/allP S; apply/allP=>x X; 
by apply/negP=>/S; rewrite X.
Qed.

Lemma disjointPR {A : eqType} (s1 s2 : seq A) :
        reflect {in s2, forall x, x \notin s1}
                (disjoint s1 s2).
Proof. by apply/(iffP allP). Qed.

Lemma disjointPL {A : eqType} (s1 s2 : seq A) :
        reflect {in s1, forall x, x \notin s2}
                (disjoint s1 s2).
Proof. by rewrite disjointC; apply/disjointPR. Qed.

Lemma disjoint_catR {A : eqType} (s s1 s2 : seq A) : 
        disjoint s (s1 ++ s2) = 
        disjoint s s1 && disjoint s s2.
Proof. by rewrite /disjoint all_cat. Qed.

Lemma disjoint_catL {A : eqType} (s s1 s2 : seq A) : 
        disjoint (s1 ++ s2) s = 
        disjoint s1 s && disjoint s2 s.
Proof. by rewrite -!(disjointC s) disjoint_catR. Qed.

Lemma disjoint1L {A : eqType} x (s : seq A) :
        disjoint [:: x] s = (x \notin s).
Proof.
apply/idP/idP.
- by apply: contraL=>X; apply/allPn; exists x=>//; rewrite negbK inE.
by apply: contraR=>/allPn [y H]; rewrite inE negbK =>/eqP <-.
Qed.

Lemma disjoint1R {A : eqType} x (s : seq A) :
        disjoint s [:: x] = (x \notin s).
Proof. by rewrite disjointC disjoint1L. Qed.

Lemma disjoint_consL {A : eqType} x (s1 s2 : seq A) :
        disjoint (x :: s1) s2 = 
        (x \notin s2) && disjoint s1 s2.
Proof. by rewrite -cat1s disjoint_catL disjoint1L. Qed.

Lemma disjoint_consR {A : eqType} x (s1 s2 : seq A) :
        disjoint s1 (x :: s2) = 
        (x \notin s1) && disjoint s1 s2.
Proof. by rewrite -cat1s disjoint_catR disjoint1R. Qed.

Lemma disjoint_consLI {A : eqType} x (s1 s2 : seq A) :
        x \notin s2 ->
        disjoint s1 s2 ->
        disjoint (x :: s1) s2.
Proof. by rewrite disjoint_consL=>->->. Qed.

Lemma disjoint_consRI {A : eqType} x (s1 s2 : seq A) :
        x \notin s1 ->
        disjoint s1 s2 ->
        disjoint s1 (x :: s2).
Proof. by rewrite disjoint_consR=>->->. Qed.

Lemma disjoint_consLE {A : eqType} x (s1 s2 : seq A) :
        disjoint (x :: s1) s2 ->
        (x \notin s2) * (disjoint s1 s2).
Proof. by rewrite disjoint_consL=>/andX. Qed.

Lemma disjoint_consRE {A : eqType} x (s1 s2 : seq A) :
        disjoint s1 (x :: s2) ->
        (x \notin s1) * (disjoint s1 s2).
Proof. by rewrite disjoint_consR=>/andX. Qed.

Lemma disjoint_subL {A : eqType} (s s1 s2 : seq A) : 
        {subset s2 <= s1} ->
        disjoint s s1 ->
        disjoint s s2.
Proof. by move=>X /allP H; apply/allP=>z /X /H. Qed.

Lemma disjoint_subR {A : eqType} (s s1 s2 : seq A) : 
        {subset s2 <= s1} ->
        disjoint s1 s ->
        disjoint s2 s.
Proof. 
move=>X; rewrite disjointC=>/(disjoint_subL X).
by rewrite disjointC.
Qed.

Lemma disjoint_eqL {A : eqType} {s s1 s2 : seq A} :
        s1 =i s2 ->
        disjoint s1 s = disjoint s2 s.
Proof. by move=>X; apply/idP/idP; apply: disjoint_subR=>z; rewrite X. Qed.

Lemma disjoint_eqR {A : eqType} {s s1 s2 : seq A} :
        s1 =i s2 ->
        disjoint s s1 = disjoint s s2.
Proof. by move=>X; apply/idP/idP; apply: disjoint_subL=>z; rewrite X. Qed.

Lemma disjointN {A : eqType} (s1 s2 : seq A) : 
        ~~ disjoint s1 s2 ->
        exists2 x, x \in s1 & x \in s2.
Proof. by case/allPn=>x; rewrite negbK; exists x. Qed.

(* useful renaming *)
Lemma filter_disjC {A : eqType} {p xs : seq A} :
        reflect (filter [predC p] xs = xs)
                (disjoint p xs).
Proof. exact: all_filterP. Qed.

Lemma disjoint0 {A : eqType} (xs : seq A) :
        disjoint xs xs ->
        xs = [::].
Proof. by case: xs=>//= x xs; rewrite disjoint_consL inE eqxx. Qed.

Lemma disjointR {A : eqType} {xs1 xs2 : seq A} :
        reflect {in xs2, forall x, x \notin xs1}
                (disjoint xs1 xs2).
Proof. by apply: (iffP allP). Qed.

Lemma disjointL {A : eqType} {xs1 xs2 : seq A} :
        reflect {in xs1, forall x, x \notin xs2}
                (disjoint xs1 xs2).
Proof. by rewrite disjointC; apply: disjointR. Qed.

Lemma disj_subL {A : eqType} {xs1 xs2 : seq A} :
        reflect {subset xs1 <= [predC xs2]}
                (disjoint xs1 xs2).
Proof. exact: (iffP disjointL). Qed.

Lemma disj_subR {A : eqType} {xs1 xs2 : seq A} :
        reflect {subset xs2 <= [predC xs1]}
                (disjoint xs1 xs2).
Proof. exact: (iffP disjointR). Qed.

Lemma disj_filt_subL {A : eqType} {p : {pred A}} {xs1 xs2 : seq A} :
        reflect {subset xs1 <= predC [predI p & xs2]}
                (disjoint xs1 (filter p xs2)).
Proof. by apply: (iffP disj_subL)=>S x /S; rewrite !inE mem_filter. Qed.

Lemma disj_filt_subR {A : eqType} {p : {pred A}} {xs1 xs2 : seq A} :
        reflect {subset [predI p & xs2] <= [predC xs1]}
                (disjoint xs1 (filter p xs2)).
Proof.
apply: (iffP disj_filt_subL)=>/subsetC S x X; apply: S;
by rewrite !inE /= negbK.
Qed.

Lemma prefix_disjT {A : eqType} (s1 s2 s3 : seq A) : 
        prefix s1 s2 ->
        disjoint s2 s3 ->
        disjoint s1 s3.
Proof. by move/prefix_sub/disjoint_subR; apply. Qed.

Lemma cycle_head_uniq {A : eqType} (r : rel A) x (xs : seq A) :
        x \in xs ->
        cycle r xs ->
        exists ys, cycle r (x :: ys) /\ uniq (x :: ys).
Proof.
case/splitPr=>p1 p2; rewrite cycle_catC /= rcons_path; case/andP.
by case/shortenP=>p' P U _ R; exists p'; rewrite rcons_path P R.
Qed.

Lemma subseq_permD {A : eqType} (r1 r2 r : seq A) :
        subseq r1 r ->
        subseq r2 r ->
        disjoint r1 r2 ->
        exists2 r', perm_eq r' (r1 ++ r2) & subseq r' r. 
Proof.
elim: r r1 r2=>[|x r IH] r1 r2.
- by move/eqP=>-> /eqP ->; exists [::].
case: r1=>[|a1 r1]; case: r2=>[|a2 r2] //=; first by exists [::].
- case: ifPn=>[/eqP ->{a2}|N] _ S. 
  - by exists (x :: r2)=>//; rewrite eqxx.
  by exists (a2 :: r2)=>//; rewrite (negbTE N).
- rewrite cats0; case: ifPn=>[/eqP ->{a1}|N] S _.
  - by exists (x :: r1)=>//; rewrite eqxx.
  by exists (a1 :: r1)=>//; rewrite (negbTE N).
case: ifPn=>[/eqP ->{a1}|N1] S1.
- rewrite disjoint_consL inE (eq_sym x). 
  case: (a2 =P x)=>//= _ S2 /andP [_] /(IH _ _ S1 S2) [r' P R].
  by exists (x :: r'); [rewrite perm_cons|rewrite eqxx].
case: ifPn=>[/eqP ->{a2}|N2] S2.
- rewrite disjoint_consR inE (eq_sym x) (negbTE N1) /=. 
  case/andP=>_ /(IH _ _ S1 S2) [r'] P R.
  exists (x :: r'); last by rewrite eqxx. 
  rewrite -cat_cons -(cat1s x r') -(cat1s x r2).
  apply/perm_trans/permPl/perm_catCA. 
  by rewrite perm_cat2l.
case/(IH _ _ S1 S2)=>r' P R.
exists r'; first by rewrite -cat1s catA cat1s.
by case: r' P R=>[//|a r'] P; case: (a =P x)=>// -> /cons_subseq.
Qed.

Lemma map_subseq_inj {A B : eqType} (f : A -> B) (s1 s2 : seq A) :
        injective f ->
        subseq (map f s1) (map f s2) = subseq s1 s2.
Proof.
elim: s2 s1=>[|x s2 IH][|y s1] //= I.
case: (y =P x)=>[->|N]; first by rewrite eqxx IH.
by case: eqP; [move/I/N|rewrite -IH].
Qed.

Lemma map_image_subseq {A B : eqType} (f : A -> B) s1 s2 : 
        subseq s1 (map f s2) -> 
        exists2 s, s1 = map f s & subseq s s2. 
Proof.
elim: s2 s1=>[|x s2 IH][|y s1] //=; try by exists [::].
case: ifPn=>[/eqP ->{y}|N] /IH [s -> S].
- by exists (x :: s)=>//; rewrite eqxx.
exists s=>//; case: s S=>[//|z s] S.
by case: eqP S=>// -> /cons_subseq.
Qed.

Lemma pmap_subseq {A B : eqType} (f : A -> option B) (s1 s2 : seq A) :
        subseq s1 s2 ->
        subseq (pmap f s1) (pmap f s2).
Proof.
move=>S; suff : subseq (map Some (pmap f s1)) (map Some (pmap f s2)).
- by rewrite map_subseq_inj //; move=>x y [].
rewrite !pmapS_filter; apply: map_subseq; rewrite subseq_filter.
apply/andP; split; first by apply/allP=>z; rewrite mem_filter=>/andP [].
by apply: subseq_trans S; apply/filter_subseq.
Qed.

(* finding last occurrence of element in a sequence *)

Section FindLast.
Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

(* helper function for finding the last occurrence in a single pass *)
(* calculates index and size *)
Definition findlast_aux oi0 p s : option nat * nat :=
  foldl (fun '(o,i) x => (if p x then Some i else o, i.+1)) oi0 s.

Lemma findlast_auxE oi0 p s :
        findlast_aux oi0 p s =
        let k := seq.find p (rev s) in
        (if k == size s then oi0.1
           else Some (oi0.2 + (size s - k).-1), oi0.2 + size s).
Proof.
rewrite /findlast_aux; elim: s oi0=>/= [|x s IH] [o0 i0] /=.
- by rewrite addn0.
rewrite IH /= rev_cons -cats1 find_cat /= has_find.
move: (find_size p (rev s)); rewrite size_rev; case: ltngtP=>// H _.
- case: eqP=>[E|_]; first by rewrite E ltnNge leqnSn in H.
  apply: injective_projections=>/=; [congr Some|rewrite addSnnS=>//]. 
  by rewrite !predn_sub /= -predn_sub addSnnS prednK // subn_gt0.  
case: ifP=>_; rewrite addSnnS; last by rewrite addn1 eqxx.
by rewrite addn0 eqn_leq leqnSn /= ltnn subSnn addn0.
Qed.

Definition findlast p s : nat :=
  let '(o, i) := findlast_aux (None, 0) p s in odflt i o.

(* finding last is finding first in reversed list and flipping indices *)
Lemma findlastE p s :
        findlast p s =
        if has p s then (size s - seq.find p (rev s)).-1 else size s.
Proof.
rewrite /findlast findlast_auxE /= !add0n -has_rev; case/boolP: (has p (rev s)).
- by rewrite has_find size_rev; case: ltngtP.
by move/hasNfind=>->; rewrite size_rev eqxx.
Qed.

Lemma findlast_size p s : 
        findlast p s <= size s.
Proof.
rewrite findlastE; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_findlast p s : 
        has p s = (findlast p s < size s).
Proof.
symmetry; rewrite findlastE; case: ifP=>H /=; last by rewrite ltnn.
by rewrite -subnS /= ltn_subrL /=; case: s H.
Qed.

Lemma hasNfindlast p s : 
        ~~ has p s -> 
        findlast p s = size s.
Proof. by rewrite has_findlast; case: ltngtP (findlast_size p s). Qed.

Lemma findlast0 p x : findlast p [::] = 0.
Proof. by []. Qed.

Lemma findlast1 p x : findlast p [::x] = ~~ p x.
Proof. by rewrite findlastE /= orbF; case: ifP=>// ->. Qed.

Lemma findlast_cat p s1 s2 :
        findlast p (s1 ++ s2) =
        if has p s1 && ~~ has p s2
          then findlast p s1
          else size s1 + findlast p s2.
Proof.
rewrite !findlastE has_cat rev_cat find_cat has_rev size_cat size_rev.
case/boolP: (has p s2)=>H2; last first.
- rewrite orbF; case/boolP: (has p s1)=>//= H1.
  by rewrite addnC subnDl.
have H2' : find p (rev s2) < size s2.
- by rewrite -size_rev -has_find has_rev.
rewrite /= orbT andbF -addnBA; first by apply: ltnW.
rewrite -!subn1 -subnDA -addnBA; first by rewrite subn_gt0.
by rewrite subnDA.
Qed.

Lemma findlast_cons p x s :
        findlast p (x::s) =
        if p x && ~~ has p s then 0 else (findlast p s).+1.
Proof.
rewrite -cat1s findlast_cat /= !add1n orbF findlast1.
by case: ifP=>// /andP [->].
Qed.

Lemma findlast_rcons p x s :
        findlast p (rcons s x) =
        if p x then size s
          else if has p s then findlast p s
                          else (size s).+1.
Proof.
rewrite -cats1 findlast_cat /= orbF findlast1.
case: (p x)=>/=; first by rewrite andbF addn0.
by rewrite andbT addn1.
Qed.

Lemma nth_findlast x0 p s : 
        has p s -> 
        p (nth x0 s (findlast p s)).
Proof.
rewrite findlastE=>/[dup] E ->; rewrite -has_rev in E.
rewrite -subnS -nth_rev; first by rewrite -size_rev -has_find.
by apply: nth_find.
Qed.

Lemma has_drop p s i : 
        has p s -> 
        has p (drop i s) = (i <= findlast p s).
Proof.
rewrite findlastE=>/[dup] E ->; rewrite -has_rev in E.
have Hh: 0 < size s - find p (rev s).
- by rewrite -size_rev subn_gt0 -has_find.
rewrite -size_rev; move/(has_take (size s - i)): (E).
rewrite take_rev -subnS size_rev.
case/boolP: (i < size s)=>[Hi|].
- rewrite subnA //; first by apply: ltnW.
  rewrite subnn add0n has_rev=>->.
  rewrite ltn_subRL addnC -ltn_subRL subnS.
  by case: (size s - find p (rev s)) Hh.
rewrite -ltnNge ltnS => Hi _.
rewrite drop_oversize //=; symmetry; apply/negbTE.
rewrite -ltnNge subnS prednK //.
by apply/leq_trans/Hi; exact: leq_subr.
Qed.

Lemma find_geq p s i : 
        has p (drop i s) -> i <= findlast p s.
Proof.
case/boolP: (has p s)=>Hp; first by rewrite (has_drop _ Hp).
suff: ~~ has p (drop i s) by move/negbTE=>->.
move: Hp; apply: contra; rewrite -{2}(cat_take_drop i s) has_cat=>->.
by rewrite orbT.
Qed.

Lemma find_leq_last p s : 
        find p s <= findlast p s.
Proof.
rewrite findlastE.
case/boolP: (has p s)=>[|_]; last by apply: find_size.
elim: s=>//= h s IH.
rewrite rev_cons -cats1 find_cat has_rev size_rev /=.
case/orP; first by move=>->.
move=>/[dup] H ->; case: ifP=>_ //.
rewrite subSn /=.
- by rewrite -size_rev; apply: find_size.
apply: (leq_ltn_trans (IH H)); rewrite ltn_predL subn_gt0.
by rewrite -size_rev -has_find has_rev.
Qed.

Variant split_findlast_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindLastNth x s1 s2 of p x & ~~ has p s2 :
    split_findlast_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_findlast_nth x0 p s (i := findlast p s) :
        has p s ->
        split_findlast_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
move=> p_s; rewrite -[X in split_findlast_nth_spec _ X](cat_take_drop i s).
rewrite (drop_nth x0 _); first by rewrite -has_findlast.
rewrite -cat_rcons; constructor; first by apply: nth_findlast.
by rewrite has_drop // ltnn.
Qed.

Variant split_findlast_spec p : seq T -> seq T -> seq T -> Type :=
  FindLastSplit x s1 s2 of p x & ~~ has p s2 :
    split_findlast_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_findlast p s (i := findlast p s) :
        has p s ->
        split_findlast_spec p s (take i s) (drop i.+1 s).
Proof.
by case: s => // x ? in i * =>?; case: split_findlast_nth=>//; constructor.
Qed.

End FindLast.


Section FindLastEq.
Variables T : eqType.
Implicit Type s : seq T.

Definition indexlast (x : T) : seq T -> nat := findlast (pred1 x).

Lemma indexlast_size x s : indexlast x s <= size s.
Proof. by rewrite /indexlast; apply: findlast_size. Qed.

Lemma indexlast_mem x s : (indexlast x s < size s) = (x \in s).
Proof. by rewrite /indexlast -has_findlast has_pred1. Qed.

Lemma memNindexlast x s : x \notin s -> indexlast x s = size s.
Proof. by rewrite -has_pred1=>/hasNfindlast. Qed.

Lemma indexlast0 x : indexlast x [::] = 0.
Proof. by []. Qed.

Lemma indexlast1 x y : indexlast x [::y] = (x != y).
Proof. by rewrite /indexlast findlast1 /= eq_sym. Qed.

Lemma indexlast_cat x s1 s2 :
        indexlast x (s1 ++ s2) =
        if (x \in s1) && (x \notin s2)
          then indexlast x s1
          else size s1 + indexlast x s2.
Proof. by rewrite /indexlast findlast_cat !has_pred1. Qed.

Lemma indexlast_cons x y s :
        indexlast x (y::s) =
        if (y == x) && (x \notin s) then 0 else (indexlast x s).+1.
Proof. by rewrite /indexlast findlast_cons has_pred1. Qed.

Lemma indexlast_rcons x y s :
        indexlast x (rcons s y) =
        if y == x then size s
          else if x \in s then indexlast x s
                          else (size s).+1.
Proof. by rewrite /indexlast findlast_rcons has_pred1. Qed.

Lemma index_geq x s i : 
        x \in drop i s -> 
        i <= indexlast x s.
Proof. by rewrite -has_pred1; apply: find_geq. Qed.

Lemma index_leq_last x s : index x s <= indexlast x s.
Proof. by apply: find_leq_last. Qed.

Lemma indexlast_count x s : 
        count_mem x s <= 1 <-> index x s = indexlast x s.
Proof.
elim: s=>//= h t IH; rewrite indexlast_cons.
case: eqP=>/= ?; last first.
- by rewrite add0n IH; split=>[->|[]].
rewrite add1n ltnS leqn0; split.
- by move/eqP/count_memPn=>->.
by case: ifP=>//= /count_memPn->.
Qed.

Lemma index_lt_last x s : 
        1 < count_mem x s -> 
        index x s < indexlast x s.
Proof.
move=>H; move: (index_leq_last x s); rewrite leq_eqVlt.
by case: eqP=>//= /indexlast_count; case: leqP H.
Qed.

Lemma indexlast_uniq x s : 
        uniq s -> 
        index x s = indexlast x s.
Proof.
move=>H; apply/indexlast_count.
by rewrite count_uniq_mem //; apply: leq_b1.
Qed.

Lemma indexlast_memN x xs :
        x \notin xs <-> indexlast x xs = size xs.
Proof.
split; first by exact: memNindexlast.
by move=>E; rewrite -indexlast_mem E ltnn.
Qed.

Lemma index_last_inj x y s :
        (x \in s) || (y \in s) -> 
        index x s = indexlast y s -> x = y.
Proof.
elim: s=>[|k s IH] //=; rewrite !inE indexlast_cons !(eq_sym k).
case: eqP=>[{k}<- _|_ /= S]; first by case: eqP=>//=.
move: S; case/boolP: (y \in s)=>/=.
- by rewrite andbF=>H _ []; apply: IH; rewrite H orbT.
move=>Ny; rewrite orbF andbT.
by case: eqP=>//; rewrite orbF=>_ H []; apply: IH; rewrite H.
Qed.

Lemma indexlast_inj x y s :
        x \in s -> 
        indexlast x s = indexlast y s -> 
        x = y.
Proof.
elim: s=>[|k s IH] //=; rewrite inE eq_sym !indexlast_cons.
case: eqP=>[->{k} _|_ /= S] /=.
- case: eqP=>//= _.
  by case: ifP=>// /negbT; rewrite negbK=>H; case; apply: IH.
by case: ifP=>// _ []; apply: IH.
Qed.

Lemma mem_drop_indexlast x s :
        x \notin drop (indexlast x s).+1 s.
Proof.
elim: s=>//=h s; rewrite indexlast_cons.
case: eqP=>//= _ H.
by case: ifP=>//=; rewrite drop0.
Qed.

Variant splitLast x : seq T -> seq T -> seq T -> Type :=
  SplitLast p1 p2 of x \notin p2 : splitLast x (rcons p1 x ++ p2) p1 p2.

Lemma splitLastP s x (i := indexlast x s) :
        x \in s ->
        splitLast x s (take i s) (drop i.+1 s).
Proof.
case: s => // y s in i * => H.
case: split_findlast_nth=>//; first by rewrite has_pred1.
move=>_ s1 s2 /= /eqP->; rewrite has_pred1 => H2.
by constructor.
Qed.

End FindLastEq.

(* finding all occurrences *)

Section FindAll.
Variables T : Type.
Implicit Types (x : T) (p : pred T) (s : seq T).

(* helper function for finding all occurrences in a single pass with difference lists *)
Definition findall_aux oi0 p s : (seq nat -> seq nat) * nat :=
  foldl (fun '(s,i) x => (if p x then s \o cons i else s, i.+1)) oi0 s.

Lemma findall_auxE oi0 p s :
      (forall s1 s2 : seq nat, oi0.1 (s1 ++ s2) = oi0.1 s1 ++ s2) ->
      let: (rs, ix) := findall_aux oi0 p s in
        (forall s' : seq nat,
           rs s' = oi0.1 (unzip1 (filter (p \o snd) 
                                         (zip (iota oi0.2 (size s)) s))) ++ s')
        /\ ix = oi0.2 + size s.
Proof.
move; rewrite /findall_aux; elim: s oi0=>[|x s IH] [o0 i0] /= H0.
- split; last by rewrite addn0.
  by move=>s'; rewrite -{1}(cat0s s') H0.
case/boolP: (p x)=>/= Hpx.
- move: (IH (o0 \o cons i0, i0.+1))=>/=.
  rewrite addSn addnS; apply=>s1 s2.
  by rewrite -cat_cons H0.
by move: (IH (o0, i0.+1))=>/=; rewrite addSn addnS; apply.
Qed.

Definition findall p s : seq nat := (findall_aux (id, 0) p s).1 [::].

Lemma findallE p s :
        findall p s = unzip1 (filter (p \o snd) (zip (iota 0 (size s)) s)).
Proof.
rewrite /findall.
move: (@findall_auxE (id, 0) p s)=>/= /(_ (fun s1 s2 : seq nat => erefl)).
case E: (findall_aux (id, 0) p s)=>[rs ix] /=; case=>/(_ [::]) -> _.
by rewrite cats0.
Qed.

Lemma findall_cat p s1 s2 :
        findall p (s1 ++ s2) =
        findall p s1 ++ map (fun n => size s1 + n) (findall p s2).
Proof.
rewrite !findallE size_cat iotaD add0n zip_cat; first by rewrite size_iota.
rewrite filter_cat {1}/unzip1 map_cat; congr (_ ++ _).
set n := size s1.
rewrite -{1}(addn0 n) iotaDl zip_mapl filter_map -!map_comp.
rewrite (eq_filter (a2:=(p \o snd))); first by case.
by apply: eq_map; case.
Qed.

Lemma findall_cons p x s :
        findall p (x::s) =
        if p x then 0 :: map S (findall p s) else map S (findall p s).
Proof. by rewrite -cat1s findall_cat /= findallE /=; case: (p x). Qed.

Lemma findall_rcons p x s :
        findall p (rcons s x) =
        if p x then rcons (findall p s) (size s) else findall p s.
Proof.
rewrite -cats1 findall_cat /= !findallE /=; case: (p x)=>/=.
- by rewrite addn0 cats1.
by rewrite cats0.
Qed.

Lemma findall_size p s :
        size (findall p s) = count p s.
Proof.
by elim: s=>//=x s IH; rewrite findall_cons; case: (p x)=>/=;
rewrite size_map IH.
Qed.

Lemma findall_nilp p s :
        nilp (findall p s) = ~~ has p s.
Proof. by rewrite /nilp findall_size has_count -leqNgt leqn0. Qed.

Lemma findall_head p s :
        find p s = head (size s) (findall p s).
Proof.
elim: s=>//=x s IH; rewrite findall_cons; case: (p x)=>//=.
by rewrite -head_map IH.
Qed.

Lemma findall_last p s :
        findlast p s = last (size s) (findall p s).
Proof.
elim/last_ind: s=>//=s x IH; rewrite findall_rcons findlast_rcons size_rcons.
case: (p x)=>/=; first by rewrite last_rcons.
by rewrite IH -(negbK (has _ _)) -findall_nilp; case: (findall p s).
Qed.

Lemma findall_count1 p s :
        count p s <= 1 ->
        findall p s = if has p s then [::find p s] else [::].
Proof.
rewrite -(findall_size p s); case E: (findall p s)=>[|h t] /=.
- by move/nilP: E; rewrite findall_nilp=>/negbTE ->.
have ->: has p s by rewrite -(negbK (has p s)) -findall_nilp E.
rewrite ltnS leqn0 => /eqP/size0nil Et; move: E; rewrite {t}Et.
by rewrite findall_head=>->.
Qed.

End FindAll.

Section FindAllEq.
Variables T : eqType.
Implicit Type s : seq T.

Definition indexall (x : T) : seq T -> seq nat := findall (pred1 x).

Lemma indexall_size x s :
        size (indexall x s) = count_mem x s.
Proof. by rewrite /indexall findall_size. Qed.

Lemma indexall_mem x s : nilp (indexall x s) = (x \notin s).
Proof. by rewrite /indexall findall_nilp has_pred1. Qed.

Lemma indexall_head x s :
        index x s = head (size s) (indexall x s).
Proof. by rewrite /index /indexall findall_head. Qed.

Lemma indexall_last x s :
        indexlast x s = last (size s) (indexall x s).
Proof. by rewrite /indexlast /indexall findall_last. Qed.

Lemma indexall_count1 x s :
        count_mem x s <= 1 ->
        indexall x s = if x \in s then [:: index x s] else [::].
Proof. by rewrite /indexall /index -has_pred1; apply: findall_count1. Qed.

Corollary indexall_uniq x s :
            uniq s ->
            indexall x s = if x \in s then [:: index x s] else [::].
Proof. by move=>U; apply: indexall_count1; rewrite (count_uniq_mem _ U) leq_b1. Qed.

End FindAllEq.

(* Interaction of filter/last/index *)

Section FilterLastIndex.
Variables A : eqType.

(* if s has an element, last returns one of them *)
Lemma last_in x k (s : seq A) : 
        x \in s -> 
        last k s \in s.
Proof.
elim: s k=>[|k s IH] k' //=; rewrite !inE.
case/orP=>[/eqP <-|/IH ->]; first by apply: mem_last.
by rewrite orbT.
Qed.

Arguments last_in x [k s].

Lemma last_mem x (s : seq A) a : 
        a = last x s ->
        (a == x) || (a \in s).
Proof. by move=>->; apply: mem_last. Qed.

Lemma last_notin x k (s : seq A) : 
        x \in s -> 
        k \notin s -> 
        last k s != k.
Proof. by move/(last_in _ (k:=k))=>H /negbTE; case: eqP H=>// ->->. Qed.

Lemma last_notin_nilp k (s : seq A) : 
        ~~ nilp s -> 
        k \notin s -> 
        last k s != k.
Proof.
move=>N; apply: (last_notin (x := head k s)).
by case: s N=>//= x s _; rewrite inE eqxx.
Qed.

(* last either returns a default, or one of s's elements *)
Lemma last_change k (s : seq A) : 
        last k s != k -> 
        last k s \in s.
Proof. by move: (mem_last k s); rewrite inE; case: eqP. Qed.

Lemma last_changeE1 k (s : seq A) :
        last k s != k -> 
        forall x, last x s = last k s.
Proof. by elim: s k=>[|k s IH] y //=; rewrite eqxx. Qed.

Lemma last_changeE2 k (s : seq A) :
        last k s != k -> 
        forall x, x \notin s -> last x s != x.
Proof. by move/last_change/last_notin. Qed.

(* common formats of last_change *)
Lemma last_nochange k (s : seq A) : 
        last k s = k -> 
        (k \in s) || (s == [::]).
Proof.
case: s k=>[|k s] //= k'; rewrite inE; case: eqP=>[->|N L] //.
by move: (@last_change k s); rewrite L=>-> //; case: eqP N.
Qed.

Lemma last_nochange_nil k (s : seq A) : 
        last k s = k -> 
        k \notin s -> s = [::].
Proof. by move/last_nochange; case/orP=>[/negbF ->|/eqP]. Qed.

(* last and rcons *)

Lemma rcons_lastX x y (s : seq A) :
        x \in s -> 
        exists s', s = rcons s' (last y s).
Proof.
elim/last_ind: s=>[|ks k IH] //=.
by rewrite last_rcons; exists ks.
Qed.

Lemma rcons_lastP x (s : seq A) :
        reflect (exists s', s = rcons s' (last x s)) 
                (last x s \in s).
Proof.
case X : (last x s \in s); constructor; first by apply: rcons_lastX X.
case=>s' E; move/negP: X; elim.
by rewrite E last_rcons mem_rcons inE eqxx.
Qed.

Lemma rcons_lastXP x y (s : seq A) :
        reflect (exists s', s = rcons s' x) 
                ((x == last y s) && (x \in s)).
Proof.
case: eqP=>[->|N]; first by apply: rcons_lastP.
by constructor; case=>s' E; elim: N; rewrite E last_rcons.
Qed.

Lemma rcons_lastN (s : seq A) a p :
        p != a ->
        p = last a s -> 
        exists ss, s = rcons ss p.
Proof. by move/[swap]=>-> N; apply/rcons_lastX/last_change/N. Qed.

Lemma index_last_size_uniq z (s : seq A) :
        uniq s ->
        index (last z s) s = (size s).-1.
Proof.
elim: s z=>//= x s IH z.
case/andP=>Nx U; rewrite eq_sym; case: eqVneq=>H.
- by rewrite (last_nochange_nil H Nx).
rewrite {}IH //; apply: prednK.
by case: {Nx U}s H=>//=; rewrite eqxx.
Qed.

(* last has bigger index than anything in x *)
Lemma index_last_mono x k (s : seq A) :
         uniq s -> 
         x \in s -> 
         index x s <= index (last k s) s.
Proof.
elim: s k=>[|k s IH] //= k'; rewrite inE !(eq_sym k).
case/andP=>K U; case: (x =P k)=>//= /eqP N X.
case: (last k s =P k)=>[/last_nochange|/eqP L].
- by case: eqP X=>[->//|]; rewrite (negbTE K).
by apply: leq_trans (IH k U X) _.
Qed.

(* if it has bigger index, and is in the list, then it's last *)
Lemma max_index_last (s : seq A) (x y : A) :
         uniq s -> 
         x \in s ->
         (forall z, z \in s -> index z s <= index x s) -> 
         last y s = x.
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
        p x -> 
        index x ks <= index y ks ->
        index x (filter p ks) <= index y (filter p ks).
Proof.
move=>Px; elim: ks=>[|k ks IH] //=; case P : (p k)=>/=;
by case: ifP Px; case: ifP=>// _ /eqP <-; rewrite P.
Qed.

Lemma filter_subset (p1 p2 : pred A) (s : seq A) :
        subpred p1 p2 -> 
        {subset filter p1 s <= filter p2 s}.
Proof.
move=>S; rewrite (_ : filter p1 s = filter p1 (filter p2 s));
  last by apply: mem_subseq; apply: filter_subseq.
rewrite -filter_predI; apply: eq_in_filter=>x X /=.
by case E : (p1 x)=>//=; rewrite (S _ E).
Qed.

Lemma last_filter_neq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> 
        x \notin s ->
        last x (filter p1 s) != x -> 
        last x (filter p2 s) != x.
Proof.
move=>S N /last_filter_change /andP [H1 H2].
apply: (@last_notin (last x [seq x <-s | p1 x])).
- by rewrite mem_filter H2 andbT; apply: S.
by rewrite mem_filter negb_and N orbT.
Qed.

Lemma last_filter_eq (p1 p2 : pred A) x (s : seq A) :
        subpred p1 p2 -> 
        x \notin s ->
        last x (filter p2 s) = x -> 
        last x (filter p1 s) = x.
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
        uniq (x :: s) -> 
        p y -> 
        y \in s ->
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
        uniq (x :: s) -> 
        p y -> 
        y \in s ->
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
- by rewrite Pt1 /= eqxx; case: eqP.
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
- by rewrite Pt1 /= eqxx; case: eqP.
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
- by rewrite Pt2 /= eqxx; case: eqP.
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
- by rewrite Pt2 /= eqxx; case: eqP.
case: eqP=>[->{t1}//|/eqP Nt1k].
case: ifP=>H1 H2 /=.
- by rewrite (negbTE Nt1k) (negbTE Nkt2) !ltnS; apply: IH H2.
by rewrite ltnS; apply: IH H2.
Qed.

(* we can put the left and right lemmas together *)
Lemma index_filter_lt (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 -> 
         (t2 \notin ks) || p t2 ->
         (index t1 (filter p ks) < index t2 (filter p ks)) =
         (index t1 ks < index t2 ks).
Proof.
move=>H1 H2; apply/idP/idP.
- by apply: index_filter_ltR.
by apply: index_filter_ltL.
Qed.

Lemma index_filter_le (p : pred A) (ks : seq A) (t1 t2 : A) :
         (t1 \notin ks) || p t1 -> 
         (t2 \notin ks) || p t2 ->
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
         a \in mask m s -> 
         b \in mask m s ->
         index a (mask m s) < index b (mask m s) <->
         index a s < index b s.
Proof.
elim: m s=>[|x m IH][|k s] //= /andP [K U]; case: x=>[|Ma Mb] /=.
- rewrite !inE; case/orP=>[/eqP <-|Ma].
  - by case/orP=>[/eqP ->|]; rewrite eqxx //; case: eqP.
  case/orP=>[/eqP ->|Mb]; first by rewrite eqxx.
  by case: eqP; case: eqP=>//; rewrite ltnS IH.
case: eqP Ma K=>[-> /mem_mask -> //|Ka].
case: eqP Mb=>[-> /mem_mask -> //|Kb Mb Ma].
by rewrite ltnS IH.
Qed.

Lemma indexlast_mask (s : seq A) m a b  :
         uniq s ->
         a \in mask m s -> 
         b \in mask m s ->
         indexlast a (mask m s) < indexlast b (mask m s) <->
         indexlast a s < indexlast b s.
Proof.
elim: m s=>[|x m IH][|k s] //= /andP [K U]; case: x=>[|Ma Mb] /=;
rewrite !indexlast_cons.
- rewrite !inE; case/orP=>[/eqP Ea|Ma].
  - rewrite -{k}Ea in K *.
    have Km: (a \notin mask m s) by apply: contra K; apply: mem_mask.
    case/orP=>[/eqP ->|]; rewrite eqxx /=; first by rewrite K ltnn.
    case: eqP=>[->|Nab] H /=; first by rewrite !ltnn.
    by rewrite K Km.
  case/orP=>[/eqP Eb|Mb].
  - rewrite -{k}Eb in K *.
    have ->: (b \notin mask m s) by apply: contra K; apply: mem_mask.
    by rewrite eqxx /= K.
  rewrite Ma Mb (mem_mask Ma) (mem_mask Mb) /= !andbF.
  by apply: IH.
case: eqP Ma K=>[-> /mem_mask -> //|Ka] /=.
case: eqP Mb=>[-> /mem_mask -> //|Kb Mb Ma _] /=.
by rewrite ltnS IH.
Qed.

Lemma index_subseq (s1 s2 : seq A) a b :
        subseq s1 s2 -> 
        uniq s2 -> 
        a \in s1 -> 
        b \in s1 ->
        index a s1 < index b s1 <-> index a s2 < index b s2.
Proof. by case/subseqP=>m _ ->; apply: index_mask. Qed.

Lemma indexlast_subseq (s1 s2 : seq A) a b :
        subseq s1 s2 -> 
        uniq s2 -> 
        a \in s1 -> 
        b \in s1 ->
        indexlast a s1 < indexlast b s1 <-> indexlast a s2 < indexlast b s2.
Proof. by case/subseqP=>m _ ->; apply: indexlast_mask. Qed.

End FilterLastIndex.

(* index and mapping *)

Section IndexPmap.
Variables A B : eqType.

Lemma index_pmap (f : A -> option B) s x' y' y :
        f y = Some y' ->
        index x' (pmap f s) < index y' (pmap f s) ->
        exists2 x, f x = Some x' & index x s < index y s.
Proof.
move=>Y N; case Dy : (y \in s); last first.
- have : x' \in pmap f s by rewrite -index_mem (leq_trans N) // index_size.
  case/pmapPP=>x H1 /mem_seqP D1; exists x=>//.
  by move/negbT/index_memN: Dy=>->; rewrite index_mem.
elim: s Dy Y N=>[|k ks IH] //=; rewrite inE /oapp eq_sym =>Dy Y.
case: (k =P y) Dy=>[->{k} _|Nk /= H].
- by rewrite Y /= eqxx; case: ifP.
case D: (f k)=>[k'|] /=; last first.
- by case/(IH H Y)=>x X N; exists x=>//; case: ifP.
case: ifPn D=>[/eqP ->|Nk1]; first by exists k=>//; rewrite eqxx.
case: ifPn=>// Nk2 D /(IH H Y) [x] X N; exists x=>//.
by case: ifP.
Qed.

Lemma index_pmap_inj (f : A -> option B) s x y x' y' : 
        {in s, forall x, f x = Some y' -> x = y} ->
        index x s < index y s ->
        f x = Some x' ->
        f y = Some y' ->
        index x' (pmap f s) < index y' (pmap f s).
Proof. 
move=>H N X Y; case Dy : (y \in s); last first.
- have Ny : y' \notin pmap f s.
  - apply/pmapPP; case=>z E /mem_seqP Z.
    by move/(H _ Z): E (Z) Dy=>->->.
  rewrite (memNindex Ny) index_mem.
  apply/pmapPP; exists x=>//; apply/mem_seqP.
  by rewrite -index_mem (leq_trans N) // index_size.
elim: s Dy H N=>[|k s IH] //=; rewrite inE /oapp eq_sym.
case: (k =P y)=>[->{k}|] //=.
case: (k =P x)=>[->{k} Nxy Dy H _|/eqP Nkx Nky Dy H].
- by rewrite X /= eqxx; case: ifP X Nxy=>// /eqP -> /H -> //; rewrite inE eqxx.
have H' : {in s, forall x, f x = Some y' -> x = y}.
- by move=>z Dz /H -> //; rewrite inE Dz orbT.
move/(IH Dy H'); case Dk: (f k)=>[k'|] //=.
case: ifPn Dk=>[/eqP ->{k'} Dk|].
- by case: ifPn=>// /eqP ->; rewrite ltnn.
case: ifPn=>// /eqP ->{k'} N K.
by move/H: K Nky=>-> //; rewrite inE eqxx.
Qed.

End IndexPmap.

Section Allrel.
Variables S T : Type.

Lemma allrel_rconsl (r : T -> S -> bool) x xs ys :
        allrel r (rcons xs x) ys = allrel r xs ys && all (r x) ys.
Proof. by rewrite -cats1 allrel_catl allrel1l. Qed.

Lemma allrel_rconsr (r : T -> S -> bool) y xs ys :
        allrel r xs (rcons ys y) = allrel r xs ys && all (r^~ y) xs.
Proof. by rewrite -cats1 allrel_catr allrel1r. Qed.

End Allrel.


Section AllrelEq.
Variables S T : eqType.

Lemma allrel_in_l (r : T -> S -> bool) (xs xs' : seq T) (ys : seq S) :
        xs =i xs' ->
        allrel r xs ys = allrel r xs' ys.
Proof.
by move=>H; rewrite !allrel_allpairsE; apply/eq_all_r/mem_allpairs_dep.
Qed.

Lemma allrel_in_r (r : T -> S -> bool) (xs : seq T) (ys ys' : seq S) :
        ys =i ys' ->
        allrel r xs ys = allrel r xs ys'.
Proof.
by move=>H; rewrite !allrel_allpairsE; apply/eq_all_r/mem_allpairs_dep.
Qed.

Lemma allrel_sub_l (r : T -> S -> bool) (xs xs' : seq T) (ys : seq S) :
        {subset xs' <= xs} ->
        allrel r xs ys -> allrel r xs' ys.
Proof.
move=>H Ha; apply/allrelP=>x y Hx Hy.
by move/allrelP: Ha; apply=>//; apply: H.
Qed.

Lemma allrel_sub_r (r : T -> S -> bool) (xs : seq T) (ys ys' : seq S) :
        {subset ys' <= ys} ->
        allrel r xs ys -> allrel r xs ys'.
Proof.
move=>H Ha; apply/allrelP=>x y Hx Hy.
by move/allrelP: Ha; apply=>//; apply: H.
Qed.

Lemma allrel_trans (xs ys : seq S) z r :
        transitive r ->
        all (r^~ z) xs -> all (r z) ys -> allrel r xs ys.
Proof.
move=>Ht /allP Ha /allP Hp; apply/allrelP=>x y + Hy.
by move/Ha/Ht; apply; apply: Hp.
Qed.

End AllrelEq.


(* if there exists no path, there's the earliest path element *)
(* that doesn't satisfy the relation *)
(* de-Morgan dual of pathP with a bit of generalization *)
Lemma pathPn {T} {e : rel T} {x : T} {xs : seq T} (x0 : T) :
        reflect (exists i,
                [/\ i < size xs,
                    ~~ e (nth x0 (x :: xs) i) (nth x0 xs i) &
                    forall j, j < i -> e (nth x0 (x :: xs) j) (nth x0 xs j)])
                (~~ path e x xs).
Proof.
elim: xs x=>[|y ys IH] x /=; first by constructor; case=>i []; case: i.
rewrite negb_and; have [Ne|E] /= := boolP (e x y); last first.
- by constructor; exists 0.
apply: (iffP (IH y)).
- by case=>i [H1 H2 H3]; exists i.+1; rewrite ltnS; split=>//; case.
case; case=>[|i][] /=; first by rewrite Ne.
by rewrite ltnS=>H1 H2 H3; exists i; split=>// j; rewrite -ltnS; apply: H3.
Qed.

(* ordering with path, seq and last *)

Lemma eq_last (A : eqType) (s : seq A) x y :
        x \in s -> 
        last y s = last x s.
Proof. by elim: s x y=>[|w s IH]. Qed.

Lemma seq_last_in (A : eqType) (s : seq A) x :
        last x s \notin s -> 
        s = [::].
Proof.
case: (lastP s)=>{s} // s y; case: negP=>//; elim; rewrite last_rcons.
by elim: s=>[|y' s IH]; rewrite /= inE // IH orbT.
Qed.

Lemma path_last (A : eqType) (s : seq A) leT x :
        transitive leT -> 
        path leT x s ->
        (x == last x s) || leT x (last x s).
Proof.
move=>T /(order_path_min T) /allP; case: s=>[|a s] H /=.
- by rewrite eqxx.
by rewrite (H (last a s)) ?orbT // mem_last.
Qed.

Lemma path_lastR (A : eqType) (s : seq A) leT x :
        reflexive leT -> 
        transitive leT ->
        path leT x s -> 
        leT x (last x s).
Proof. by move=>R T P; case: eqP (path_last T P)=>// <- _; apply: R. Qed.

Lemma path_prev (A : eqType) (leT : rel A) s a x :
        x \in s -> 
        path leT a s -> 
        exists y, y \in belast a s /\ leT y x.
Proof.
case/splitPr=>p1 p2; rewrite cat_path /= =>/and3P [].
by exists (last a p1); rewrite belast_cat /= mem_cat inE eqxx orbT. 
Qed.

Lemma path_next (A : eqType) (leT : rel A) s a x b :
        x \in a :: s -> 
        path leT a (rcons s b) -> 
        exists y, y \in rcons s b /\ leT x y.
Proof.
case/splitPl=>p1 p2 Ex; rewrite rcons_cat cat_path rcons_path Ex.
case/and3P=>H1 H2 H3; case: p2 H2 H3=>[|y p2] /= H2 H3.
- by exists b; rewrite mem_cat inE eqxx orbT.
case/andP: H2=>H2 _; exists y; split=>//.
by rewrite mem_cat inE eqxx orbT.
Qed.

Lemma path_uniq (A : eqType) (leT : rel A) a s :
        (forall x y, leT x y -> y != a) ->
        (forall a b x, leT a x -> leT b x -> a = b) ->
        path leT a s -> 
        uniq (a :: s).
Proof.
move=>Na Fp; elim/last_ind: s=>[|s x IH] //=.
rewrite rcons_path mem_rcons=>/andP [Px Cx].
move: {IH}(IH Px) (IH Px); rewrite {1}lastI /=.
rewrite !rcons_uniq inE negb_or=>/andP [N _]/andP [->->].
rewrite eq_sym (Na _ _ Cx) !andbT /=; apply/negP. 
move/path_prev=>/(_ _ _ Px) [/= y][/[swap]] /(Fp _ _ _ Cx) <-. 
by rewrite (negbTE N).
Qed.

(* in a sorted list, the last element is maximal *)
(* and the maximal element is last *)

Lemma sorted_last_key_max (A : eqType) (s : seq A) leT x y :
        transitive leT -> 
        sorted leT s -> 
        x \in s ->
        (x == last y s) || leT x (last y s).
Proof.
move=>T; elim: s x y=>[|z s IH] //= x y H; rewrite inE.
case: eqP=>[->|] /= _; first by apply: path_last.
by apply: IH (path_sorted H).
Qed.

Lemma sorted_last_key_maxR (A : eqType) (s : seq A) leT x y :
        reflexive leT -> 
        transitive leT ->
        sorted leT s -> 
        x \in s -> 
        leT x (last y s).
Proof.
move=>R T S X; case/orP: (sorted_last_key_max y T S X)=>// /eqP <-.
by apply: R.
Qed.

Lemma sorted_max_key_last (A : eqType) (s : seq A) leT x y :
        transitive leT -> 
        antisymmetric leT ->
        sorted leT s -> 
        x \in s ->
        (forall z, z \in s -> leT z x) -> 
        last y s = x.
Proof.
move=>T S; elim: s x y => [|w s IH] //= x y; rewrite inE /=.
case: eqP=>[<- /= H1 _ H2 | _ H /= H1 H2]; last first.
- apply: IH (path_sorted H) H1 _ => z H3; apply: H2.
  by rewrite inE /= H3 orbT.
case/orP: (path_last T H1)=>[/eqP //|] X.
by apply: S; rewrite X H2 ?mem_last.
Qed.

Lemma max_key_last_notin (A : eqType) (s : seq A) (leT : rel A) x y :
        leT y x -> 
        (forall z, z \in s -> leT z x) -> 
        leT (last y s) x.
Proof.
elim: s x y=>[|w s IH] //= x y H1 H2; apply: IH.
- by apply: (H2 w); rewrite inE eqxx.
by move=>z D; apply: H2; rewrite inE D orbT.
Qed.

Lemma seq_last_mono (A : eqType) (s1 s2 : seq A) leT x :
        transitive leT -> 
        path leT x s1 -> 
        path leT x s2 ->
        {subset s1 <= s2} ->
        (last x s1 == last x s2) || leT (last x s1) (last x s2).
Proof.
move=>T; case: s1=>/= [_ H1 _|a s]; first by apply: path_last H1.
case/andP=>H1 H2 H3 H; apply: sorted_last_key_max (path_sorted H3) _=>//.
apply: {x s2 H1 H3} H; rewrite inE orbC -implyNb.
by case E: (_ \notin _) (@seq_last_in A s a)=>//= ->.
Qed.

Lemma seq_last_monoR (A : eqType) (s1 s2 : seq A) leT x :
        reflexive leT -> 
        transitive leT ->
        path leT x s1 -> 
        path leT x s2 ->
        {subset s1 <= s2} ->
        leT (last x s1) (last x s2).
Proof. by move=>R T P1 P2 S; case: eqP (seq_last_mono T P1 P2 S)=>[->|]. Qed.

Lemma ord_path A (s : seq A) leT (x y : A) :
        transitive leT ->
        leT x y -> 
        path leT y s -> 
        path leT x s.
Proof.
move=>T; elim: s x y=>[|k s IH] x y //= H1 /andP [H2 ->].
by rewrite (T _ _ _ H1 H2).
Qed.

Lemma path_mem (A : eqType) (s : seq A) leT x y :
        transitive leT ->
        path leT x s -> 
        y \in s -> 
        leT x y.
Proof.
move=>T; elim: s x=>[|z s IH] x //= /andP [O P].
rewrite inE; case/orP=>[/eqP -> //|].
by apply: IH; apply: ord_path O P.
Qed.

Lemma path_mem_irr (A : eqType) (s : seq A) ltT x :
        irreflexive ltT -> 
        transitive ltT ->
        path ltT x s -> 
        x \notin s.
Proof.
move=>I T P; apply: contraFT (I x).
by rewrite negbK; apply: path_mem T P.
Qed.

Lemma sorted_rcons (A : eqType) (s : seq A) leT (y : A) :
        sorted leT s -> 
        (forall x, x \in s -> leT x y) ->
        sorted leT (rcons s y).
Proof.
elim: s=>[|a s IH] //= P H; rewrite rcons_path P /=.
by apply: H (mem_last _ _).
Qed.

Lemma sorted_rconsE A (leT : rel A) xs x :
        transitive leT ->
        sorted leT (rcons xs x) = 
          all (leT^~ x) xs && sorted leT xs.
Proof.
move/rev_trans=>Ht; rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /=.
by rewrite path_sortedE // all_rev rev_sorted.
Qed.

Lemma sorted1 A (r : rel A) xs : 
        size xs == 1 -> 
        sorted r xs.
Proof. by case: xs=>// x; case. Qed.

Lemma sorted_subset_subseq_irr (A : eqType) (s1 s2 : seq A) ltT :
        irreflexive ltT -> 
        transitive ltT ->
        sorted ltT s1 -> 
        sorted ltT s2 ->
        {subset s1 <= s2} -> 
        subseq s1 s2.
Proof.
move=>R T S1 S2 H.
suff -> : s1 = filter (fun x => x \in s1) s2 by apply: filter_subseq.
apply: irr_sorted_eq S1 _ _=>//; first by rewrite sorted_filter.
by move=>k; rewrite mem_filter; case S : (_ \in _)=>//; rewrite (H _ S).
Qed.

Lemma sorted_subset_subseq_asym (A : eqType) (s1 s2 : seq A) leT :
        uniq s1 ->
        uniq s2 ->
        transitive leT ->
        antisymmetric leT -> 
        sorted leT s1 -> 
        sorted leT s2 ->
        {subset s1 <= s2} -> 
        subseq s1 s2.
Proof.
move=>U1 U2 T An S1 S2 H. 
suff -> : s1 = filter (fun x => x \in s1) s2 by apply: filter_subseq.
apply: (sorted_eq (leT:=leT))=>//; first by rewrite sorted_filter.
rewrite {1}(_ : s1 = undup s1); first by rewrite undup_id.
rewrite (_ : [seq x <- s2 | x \in s1] = 
  undup [seq x <- s2 | x \in s1]); first by rewrite undup_id ?filter_uniq.
apply: perm_undup=>z; rewrite mem_filter.
by case D : (z \in s1)=>//=; rewrite H.
Qed.

Lemma sorted_ord_index (A : eqType) (s : seq A) ltT x y :
        irreflexive ltT -> 
        transitive ltT ->
        sorted ltT s -> 
        x \in s -> 
        ltT x y -> 
        index x s < index y s.
Proof.
move=>I T S P H; elim: s S P=>[|z s IH] //= P; rewrite !inE !(eq_sym z).
case: eqP H P=>[<-{z} H P _|_ H P /= X]; first by case: eqP H=>[<-|] //; rewrite I.
case: eqP H P=>[<-{z} H|_ H]; last first.
- by move/path_sorted=>S; rewrite ltnS; apply: IH.
by move/(path_mem T)/(_ X)=>/(T _ _ _ H); rewrite I.
Qed.

Lemma path_ord_index_leq (A : eqType) (s : seq A) leT x y :
        transitive leT -> 
        antisymmetric leT ->
        leT x y -> 
        path leT y s -> 
        x \in s -> 
        x = y.
Proof.
move=>T; elim: s x y=>[|a l IH] //= x y As Lxy.
case/andP=>Lya Pal; rewrite inE.
case: eqP Lya Pal As=>[<-{a} Lyx _ As _|Nxa Lya Pal /= As' X].
- by apply: As=>//; rewrite Lxy Lyx.
by move/Nxa: (IH x a As' (T _ _ _ Lxy Lya) Pal X).
Qed.

Lemma sorted_ord_index_leq (A : eqType) (s : seq A) leT x y :
        transitive leT -> 
        antisymmetric leT ->
        sorted leT s ->
        x \in s -> 
        leT x y -> 
        x != y -> 
        index x s < index y s.
Proof.
move=>T As S P H N; elim: s S As P=>[|z s IH] //= P As; rewrite inE !(eq_sym z).
case: eqP H P As=>[<-{z} H P As _|Nxz H P As /= X]; first by rewrite eq_sym (negbTE N).
case: eqP Nxz P=>[<-{z} Nxy P|Nyz Nxz P].
- by move/Nxy: (path_ord_index_leq T As H P X).
by apply: IH X=>//; apply: path_sorted P.
Qed.

Lemma sorted_index_ord (A : eqType) (s : seq A) leT x y :
        transitive leT -> 
        sorted leT s -> 
        y \in s ->
        index x s < index y s -> 
        leT x y.
Proof.
move=>T; elim: s=>[|z s IH] //= P; rewrite inE !(eq_sym z).
case: eqP=>//= /eqP N; case: eqP P=>[-> P /(path_mem T P)|_ P] //.
by rewrite ltnS; apply: IH; apply: path_sorted P.
Qed.

(* sorted, uniq, filter *)

Lemma lt_sorted_uniq_le (A : eqType) (s : seq A) ltT :
        irreflexive ltT ->
        antisymmetric ltT ->
        transitive ltT ->
        sorted ltT s = uniq s && 
        (sorted (fun k t => (k == t) || ltT k t) s).
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
by rewrite (As m n) ?eqxx // lTnm lTmn in Nm.
Qed.

Lemma sort_sorted_in_lt (A : eqType) (s : seq A) ltT :
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
Lemma filterCN (A : eqType) (ltT : rel A) f t1 t2 :
       t1 \notin f ->
       {in f, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       filter (ltT^~ t2) f = filter (ltT^~ t1) f.
Proof.
move=>N C; apply: eq_in_filter=>x T; rewrite C ?inE ?orbT //.
by case: eqP N T=>// -> /negbTE ->.
Qed.

Lemma filterCE (A : eqType) (ltT : rel A) f t1 t2 :
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

Lemma filter2CN (A : eqType) (ltT : rel A) p f t1 t2 :
       t1 \notin p ->
       {in p, forall z, ltT z t2 = (z == t1) || ltT z t1} ->
       filter (ltT^~ t2) (filter p f) = filter (ltT^~ t1) (filter p f).
Proof.
move=>N C; apply: filterCN; first by rewrite mem_filter negb_and N.
by move=>z; rewrite mem_filter=>/andP [D _]; apply: C.
Qed.

Lemma filter2CE (A : eqType) (ltT : rel A) (p : pred A) f t1 t2 :
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

Lemma nth_cons A (a x : A) (s : seq A) (n : nat) :
        nth a (x :: s) n = if n == 0 then x else nth a s n.-1.
Proof. by case: n. Qed.

Lemma nth_base A (s : seq A) k1 k2 i :
        i < size s -> 
        nth k1 s i = nth k2 s i.
Proof.
elim: s i=>[|x xs IH] //= i K; rewrite !nth_cons.
by case: eqP=>//; case: i K=>// i; rewrite ltnS=>/IH ->.
Qed.

Lemma nth_path_head (A : eqType) (s : seq A) leT x0 k i :
        transitive leT ->
        i <= size s -> 
        path leT k s ->
        (k == nth x0 (k::s) i) || leT k (nth x0 (k::s) i).
Proof.
move=>T; case: (posnP i)=>[->|N S P]; first by rewrite eqxx.
apply/orP; right; elim: i N S P=>[|i] //; case: s=>//= x xs IH _.
rewrite ltnS=>N /andP [H1 H2]; case: i IH N=>//= i /(_ (erefl _)) IH N.
rewrite !ltnS in IH; move: (IH (ltnW N)); rewrite H1 H2=>/(_ (erefl _)).
by move/T; apply; apply/pathP.
Qed.

Lemma nth_path_last (A : eqType) (s : seq A) leT x0 k i :
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

Lemma nth_consS A (s : seq A) x0 k i : nth x0 s i = nth x0 (k::s) i.+1.
Proof. by []. Qed.

Lemma nth_leT A (s : seq A) leT x0 k i :
        i < size s -> 
        path leT k s ->
        leT (nth x0 (k::s) i) (nth x0 s i).
Proof.
elim: i k s=>[|i IH] k s; first by case: s=>[|x xs] //= _ /andP [].
by case: s IH=>[|x xs] //= IH N /andP [P1 P2]; apply: IH.
Qed.

Lemma nth_ltn_mono A (s : seq A) leT x0 k i j :
        transitive leT ->
        i <= size s -> 
        j <= size s ->
        path leT k s ->
        i < j -> 
        leT (nth x0 (k::s) i) (nth x0 (k::s) j).
Proof.
move=>T S1 S2 P; elim: j S2=>[|j IH] //= S2.
move: (nth_leT x0 S2 P)=>L.
rewrite ltnS leq_eqVlt=>/orP; case=>[/eqP -> //|].
by move/(IH (ltnW S2))/T; apply.
Qed.

Lemma nth_mono_ltn A (s : seq A) ltT x0 k i j :
         irreflexive ltT ->
         transitive ltT ->
         i <= size s -> 
         j <= size s ->
         path ltT k s ->
         ltT (nth x0 (k::s) i) (nth x0 (k::s) j) -> 
         i < j.
Proof.
move=>I T S1 S2 P; case: ltngtP=>//; last by move=>->; rewrite I.
by move/(nth_ltn_mono x0 T S2 S1 P)/T=>X /X; rewrite I.
Qed.

Lemma nth_between (A : eqType) (s : seq A) ltT x0 k z i :
        irreflexive ltT ->
        transitive ltT ->
        path ltT k s ->
        ltT (nth x0 (k::s) i) z -> 
        ltT z (nth x0 s i) -> 
        z \notin s.
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

Lemma index_sorted (A : eqType) (s : seq A) (leT : rel A) :
        uniq s ->
        (forall a b, a \in s -> b \in s -> 
           index a s < index b s -> leT a b) ->
        sorted leT s.
Proof.
elim: s=>[|x xs IH] //= U H; have P : all (leT x) xs.
- apply/allP=>z Z; apply: H; rewrite ?(inE,eqxx,Z,orbT) //.
  by case: ifP U=>// /eqP ->; rewrite Z.
rewrite (path_min_sorted P); apply: IH=>[|a b Xa Xb N]; first by case/andP: U.
apply: H; rewrite ?(inE,Xa,Xb,orbT) //.
by case: eqP U=>[->|]; case: eqP=>[->|]; rewrite ?(Xa,Xb).
Qed.

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

(* merge, merge_sort_push, sort *)

Lemma merge_eq T (lT1 lT2 : rel T) xs ys : 
        (forall x y, x \In xs ++ ys -> 
                     y \In xs ++ ys -> 
                     lT1 x y = lT2 x y) ->
        merge lT1 xs ys = merge lT2 xs ys.
Proof.
elim: xs ys=>[|x xs IH1] ys H //=.
elim: ys IH1 H=>[|y ys IH2] IH1 H //=; rewrite H //.
- by apply/In_cat; left; left.
- by apply/In_cat; right; left.
case: ifP=>_.
- by rewrite IH1 //; move=>x0 y0 X0 Y0; apply: H=>//=; right.
congr (_ :: _); apply: IH2; first by move=>z H2; apply: IH1 H2.
move=>x0 y0 X0 Y0.
have P : perm (y :: (x :: xs) ++ ys) ((x :: xs) ++ y :: ys).
- by apply/pperm_cons_cat_consL/pperm_refl.
by apply: H; apply: (pperm_in P); right.
Qed.

Lemma merge_sort_push_eq T (lT1 lT2 : rel T) xs yss : 
        (forall x y, x \In xs ++ flatten yss ->
                     y \In xs ++ flatten yss ->
                     lT1 x y = lT2 x y) ->
        merge_sort_push lT1 xs yss = merge_sort_push lT2 xs yss.
Proof.
elim: yss xs=>[|ys yss IH] //= xs H.
case: ys H=>[|y ys] H //; congr (_ :: _).
rewrite (_ : merge lT1 (y :: ys) xs = merge lT2 (y :: ys) xs).
- apply: merge_eq=>x0 y0 X0 Y0.
  have P : perm (flatten yss ++ (y :: ys) ++ xs)
                (xs ++ (y :: ys) ++ flatten yss).
  - by rewrite catA; apply/pperm_trans/pperm_catC/pperm_cat2r/pperm_catC.
  by apply: H; apply: (pperm_in P); apply/In_cat; right.
apply: IH=>x0 y0 X0 Y0.
have P : perm (merge lT2 (y :: ys) xs ++ flatten yss) 
              (xs ++ (y :: ys) ++ flatten yss).
- rewrite catA; apply/pperm_cat2r. 
  by apply/pperm_trans/pperm_catC/pperm_merge.
by apply: H; apply: (pperm_in P).
Qed.

Lemma sort_eq T (lT1 lT2 : rel T) (xs : seq T) :
        (forall x y, x \In xs -> y \In xs -> 
                     lT1 x y = lT2 x y) ->
        sort lT1 xs = sort lT2 xs.
Proof.
move=>H; rewrite !sortE. 
have {H} : forall x y, x \In xs ++ flatten [::] -> 
  y \In xs ++ flatten [::] -> lT1 x y = lT2 x y.
- by move=>x y; rewrite cats0; apply: H.
elim: xs [::]=>[|x xs IH] yss H //=. 
- elim: yss [::] H =>[|ys yss IH] //= xs H; rewrite IH.
  - move=>x0 y0 X0 Y0.
    suff P : perm (merge lT1 ys xs ++ flatten yss) (xs ++ ys ++ flatten yss).
    - by apply: H; apply: (pperm_in P).
    by rewrite catA; apply/pperm_cat2r/pperm_trans/pperm_catC/pperm_merge.
  congr merge_sort_pop; apply: merge_eq=>x0 y0 X0 Y0.  
  have P : perm (ys ++ xs ++ flatten yss) (xs ++ ys ++ flatten yss).
  - by rewrite !catA; apply/pperm_cat2r/pperm_catC.
  by apply: H; apply: (pperm_in P); rewrite catA; apply/In_cat; left.
have H' : forall x0 y0, x0 \In [:: x] ++ flatten yss ->
  y0 \In [:: x] ++ flatten yss -> lT1 x0 y0 = lT2 x0 y0.
- move=>x0 y0 X0 Y0. 
  have P : perm (xs ++ [:: x] ++ flatten yss) ((x :: xs) ++ flatten yss).
  - by apply/pperm_cons_catAC.
  by apply: H; apply: (pperm_in P); apply/In_cat; right.
rewrite (merge_sort_push_eq H'); apply: IH=>x0 y0 X0 Y0.
have P : perm (xs ++ flatten (merge_sort_push lT2 [:: x] yss))
              ((x :: xs) ++ flatten yss).
- rewrite -(cat1s x xs) -catA. 
  apply/pperm_trans/pperm_catCA/pperm_cat2l.
  by apply/pperm_merge_sort_push.
by apply: H; apply: (pperm_in P).
Qed.

Section BigCat.
Context {A B : Type}.
Implicit Types (xs : seq A) (f : A -> seq B).

Lemma flatten_map_big xs f :
        flatten (map f xs) = \big[cat/[::]]_(x <- xs) f x.
Proof.
elim: xs=>/= [|x xs IH]; first by rewrite big_nil.
by rewrite big_cons IH.
Qed.

Lemma size_big_cat xs f :
        size (\big[cat/[::]]_(x <- xs) f x) =
        \sum_(x <- xs) (size (f x)).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite !big_nil.
by rewrite !big_cons size_cat IH.
Qed.

Lemma has_big_cat (p : pred B) xs f :
        has p (\big[cat/[::]]_(x <- xs) f x) =
        has (fun x => has p (f x)) xs.
Proof.
elim: xs=>[|x xs IH]; first by rewrite big_nil.
by rewrite big_cons has_cat /= IH.
Qed.

End BigCat.

Lemma big_cat_mem_has A (B : eqType) xs (f : A -> seq B) b :
        (b \in \big[cat/[::]]_(x <- xs) f x) =
        has (fun x => b \in f x) xs.
Proof.
rewrite -has_pred1 has_big_cat; apply: eq_has=>x.
by rewrite has_pred1.
Qed.

(* big_cat_mem for A : Type *)
Lemma big_cat_memT A (B : eqType) x xs (f : A -> seq B) :
        reflect (exists2 i, i \In xs & x \in f i)
                (x \in \big[cat/[::]]_(i <- xs) f i).
Proof. by rewrite big_cat_mem_has; apply/hasPIn. Qed.

(* big_cat_mem for A : eqType *)
Lemma big_cat_memE (A B : eqType) x xs (f : A -> seq B) :
        reflect (exists2 i, i \in xs & x \in f i)
                (x \in \big[cat/[::]]_(i <- xs) f i).
Proof. by rewrite big_cat_mem_has; apply: hasP. Qed.

(* big_cat_mem for A : finType *)
Lemma big_cat_mem (A : finType) (B : eqType) (f : A -> seq B) x :
        reflect (exists i, x \in f i)
                (x \in \big[cat/[::]]_i f i).
Proof. 
case: big_cat_memE=>H; constructor.
- by case: H=>i H1 H2; exists i.
by case=>i X; elim: H; exists i.
Qed.

(* uniqueness for A : Type *)
Lemma uniq_big_catT A (B : eqType) xs (f : A -> seq B) :
        Uniq xs ->
        (forall x, x \In xs -> uniq (f x)) ->
        (forall x1 x2, x1 \In xs -> x2 \In xs -> 
          has (mem (f x1)) (f x2) -> x1 = x2) ->
        uniq (\big[cat/[::]]_(x <- xs) f x).
Proof.
elim: xs=>[|x xs IH] /=.
- by rewrite big_nil /=; constructor.
case=>Nx U H1 H2; rewrite big_cons cat_uniq.
apply/and3P; split.
- by apply: H1; left.
- rewrite has_big_cat -all_predC; apply/allPIn=>x3 H3 /=.
  by apply: contra_notN Nx=>H; rewrite (H2 _ _ _ _ H) //; [left | right].
apply: IH=>//.
- by move=>z Hz; apply: H1; right.
by move=>z1 z2 Hz1 Hz2 N; apply: H2=>//; right.
Qed.

Lemma big_cat_uniq_pairewriteise A (B : eqType) xs (f : A -> seq B) x1 x2 :
        uniq (\big[cat/[::]]_(x <- xs) f x) ->
        x1 \In xs -> 
        x2 \In xs -> 
        has (mem (f x1)) (f x2) ->
        x1 = x2.
Proof.
elim: xs=>[|x xs IH] //.
rewrite big_cons cat_uniq; case/and3P=>U N Us.
case/In_cons=>[->|H1]; case/In_cons=>[->|H2] //; last by apply: IH.
- case/hasP=>/= b Hb1 Hb2.
  exfalso; move/negP: N; apply; apply/hasP.
  by exists b=>//; apply/big_cat_memT; exists x2.
case/hasP=>/= b Hb1 Hb2.
exfalso; move/negP: N; apply.
apply/hasP; exists b=>//; apply/big_cat_memT.
by exists x1.
Qed.

(* uniqueness for A : eqType *)
Lemma uniq_big_catE (A B : eqType) (f : A -> seq B) (xs : seq A) :
        reflect
        [/\ forall i, i \in xs -> uniq (f i),
            forall i k, i \in xs -> k \in f i -> count_mem i xs = 1 &
            forall i j k, i \in xs -> j \in xs ->
              k \in f i -> k \in f j -> i = j]
        (uniq (\big[cat/[::]]_(i <- xs) f i)).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite big_nil; constructor.
rewrite big_cons cat_uniq.
case H1 : (uniq (f x))=>/=; last first.
- by constructor; case=>/(_ x); rewrite inE eqxx H1=>/(_ erefl).
case: hasPn=>/= V; last first.
- constructor; case=>H2 H3 H4; elim: V=>z /big_cat_memE [i X Zi].
  apply/negP=>Zx; move/(H3 i z): (Zi); rewrite inE X orbT=>/(_ erefl).
  move: (H4 x i z); rewrite !inE eqxx X orbT=>/(_ erefl erefl Zx Zi)=>E.
  by rewrite -{i Zi}E eqxx add1n in X *; case=>/count_memPn; rewrite X.
case: IH=>H; constructor; last first.
- case=>H2 H3 H4; apply: H; split; last 1 first.
  - by move=>i j k Xi Xj; apply: H4; rewrite inE ?Xi ?Xj orbT.
  - by move=>i X; apply: H2; rewrite inE X orbT.
  move=>i k X D; move/(H3 i k): (D); rewrite inE X orbT=>/(_ erefl).
  case: (x =P i) X D=>[<-{i}|N] X D; last by rewrite add0n.
  by rewrite add1n=>[[]] /count_memPn; rewrite X.
case: H=>H2 H3 H4; split; first by move=>i; rewrite inE=>/orP [/eqP ->|/H2].
- move=>i k; rewrite inE eq_sym; case: (x =P i)=>[<- _|N /= Xi] K; last first.
  - by rewrite add0n; apply: H3 Xi K.
  rewrite add1n; congr S; apply/count_memPn; apply: contraL (K)=>X.
  by apply/V/big_cat_memE; exists x.
move=>i j k; rewrite !inE=>/orP [/eqP ->{i}|Xi] /orP [/eqP ->{j}|Xj] Ki Kj //.
- by suff : k \notin f x; [rewrite Ki | apply/V/big_cat_memE; exists j].
- by suff : k \notin f x; [rewrite Kj | apply/V/big_cat_memE; exists i].
by apply: H4 Kj.
Qed.

(* alternative formulation *)
Lemma uniq_big_catEX (A B : eqType) (f : A -> seq B) (xs : seq A) :
        uniq xs ->
        reflect
        [/\ forall i, i \in xs -> uniq (f i) &
            forall i j k, i \in xs -> j \in xs ->
              k \in f i -> k \in f j -> i = j]
        (uniq (\big[cat/[::]]_(i <- xs) f i)).
Proof.
move=>U; case: uniq_big_catE=>H; constructor; first by case: H.
by case=>H1 H2; elim: H; split=>// i k I K; rewrite count_uniq_mem // I.
Qed.

(* uniqueness for A : finType *)
Lemma uniq_big_cat (A : finType) (B : eqType) (f : A -> seq B) :
        reflect ([/\ forall t, uniq (f t) &
                     forall t1 t2 k, k \in f t1 -> k \in f t2 -> t1 = t2])
                (uniq (\big[cat/[::]]_tag f tag)).
Proof.
case: uniq_big_catEX=>[|[R1 R2]|R].
- by rewrite /index_enum -enumT enum_uniq.
- by constructor; split=>[t|t1 t2 k K1 K2]; [apply: R1|apply: R2 K1 K2].
constructor; case=>R1 R2; elim: R; split=>[t ?|t1 t2 k ??];
by [apply: R1 | apply: R2].
Qed.

Lemma uniq_big_cat_uniqT A (B : eqType) xs (f : A -> seq B) y :
        uniq (\big[cat/[::]]_(x <- xs) f x) ->
        y \In xs -> 
        uniq (f y).
Proof.
elim: xs=>[|x xs IH] in y * => //.
rewrite big_cons InE cat_uniq.
case/and3P=>U _ Us; case=>[->|Hy] //.
by apply: IH.
Qed.

Prenex Implicits uniq_big_cat_uniqT.

Lemma uniq_big_cat_uniq (A : finType) (f : A -> seq nat) t : 
        uniq (\big[cat/[::]]_t f t) -> 
        uniq (f t).
Proof. by move/uniq_big_cat_uniqT; apply; apply/mem_seqP. Qed.

Lemma uniq_big_cat_uniq0 (A : finType) (f : A -> seq nat) t : 
        uniq (0 :: \big[cat/[::]]_t f t) -> uniq (0 :: f t).
Proof.
case/andP=>U1 /uniq_big_cat_uniq /= U2.
rewrite U2 andbT (contra _ U1) // => U3.
by apply/big_cat_mem; exists t.
Qed.

Lemma uniq_big_cat_disj (A : finType) (B : eqType) (f : A -> seq B) t1 t2 x : 
        uniq (\big[cat/[::]]_t f t) ->
        x \in f t1 -> 
        x \in f t2 -> 
        t1 = t2.
Proof. by case/uniq_big_cat=>_; apply. Qed.

(****************************)
(* enumerating all prefixes *)
(****************************)

(* useful when quantifying over partial sums *)

Fixpoint prefixes {A} (s : seq A) := 
  if s is x :: xs then [::] :: map (cons x) (prefixes xs) else [:: [::]].

Lemma prefixes0 {A : eqType} (s : seq A) : [::] \in prefixes s.
Proof. by elim: s. Qed.

Lemma prefixesT {A : eqType} (s : seq A) : s \in prefixes s.
Proof. 
elim: s=>[|x s IH] //=; rewrite inE mem_map //=.
by move=>?? [].
Qed.

Lemma prefixesE {A : eqType} (s : seq A) xs : 
        (xs \in prefixes s) = prefix xs s.
Proof.
elim: s xs=>[|x s /= IH][|y xs] //=; rewrite inE /=.
case: (y =P x)=>[->|N]; last by apply/mapP; case=>z Z [] /N.
by rewrite mem_map ?IH //; move=>?? [].
Qed.

Lemma uniq_prefixes {A : eqType} (s : seq A) : uniq (prefixes s).
Proof.
elim: s=>[|x s IH] //=.
have I : injective (cons x) by move=>?? [].
rewrite map_inj_uniq // IH andbT.
by apply/mapP; case=>?.
Qed.

Lemma map_f_prefix {A B : eqType} (f : A -> B) (s1 s2 : seq A) : 
        prefix s1 s2 ->
        prefix (map f s1) (map f s2).
Proof.
elim: s2 s1=>[|x s2 /= IH][|y s1] //=.
by case: (y =P x)=>[->|] //= /IH ->; rewrite eqxx.
Qed.

Lemma mem_map_prefix {A B : eqType} (f : A -> B) (s1 s2 : seq A) :
        injective f -> 
        prefix (map f s1) (map f s2) = prefix s1 s2.
Proof.
elim: s2 s1=>[|x s2 /= IH][|y s1] //= I.
by case: (y =P x)=>[->|N]; [rewrite eqxx IH|case: eqP=>// /I /N].
Qed.

Lemma map_image_prefix {A B : eqType} (f : A -> B) s1 s2 : 
        prefix s1 (map f s2) ->
        exists2 s, s1 = map f s & prefix s s2.
Proof.
elim: s2 s1=>[|x s2 /= IH][|y s1] //=; try by exists [::].
case/andP=>/eqP ->{y} /IH [s ->{s1} H].
by exists (x :: s)=>//=; rewrite eqxx.
Qed.

(* lifting map_f_prefix, mem_map_prefix and map_image_prefix to prefixes *)

Lemma map_f_prefixes {A B : eqType} (f : A -> B) (s : seq A) xs : 
        xs \in prefixes s ->
        map f xs \in prefixes (map f s).
Proof. by rewrite !prefixesE; apply: map_f_prefix. Qed.

Lemma mem_map_prefixes {A B : eqType} (f : A -> B) (s : seq A) xs : 
        injective f ->
        (map f xs \in prefixes (map f s)) = (xs \in prefixes s).
Proof. by rewrite !prefixesE; apply: mem_map_prefix. Qed.

(* prefixes (map f s) <= image (map f) (prefixes s) *)
Lemma map_image_prefixes {A B : eqType} (f : A -> B) (s : seq A) xs : 
        xs \in prefixes (map f s) ->
        exists2 ys, xs = map f ys & ys \in prefixes s.
Proof.
rewrite prefixesE=>/map_image_prefix [z -> H]. 
by exists z=>//; rewrite prefixesE.
Qed.

(********************************)
(* enumerating all subsequences *) 
(********************************)

(* subsequence of s is included in s *)
(* in the given order, but not necessarily *)
(* contiguously *)

(* enumerating all subsequences of s *)

Fixpoint subseqs {A} (s : seq A) : seq (seq A) :=
  if s is y :: s' then 
    let: ss := subseqs s' in ss ++ map (cons y) ss
  else [:: [::]].

Lemma subseqs0 {A : eqType} (s : seq A) : [::] \in subseqs s.
Proof. by elim: s=>[|a s IH] //=; rewrite mem_cat IH. Qed.

Lemma subseqsE {A : eqType} (s : seq A) xs : 
        (xs \in subseqs s) = subseq xs s.
Proof.
elim: s xs=>[|a s IH] xs /=; first by rewrite inE.
rewrite mem_cat; case: xs=>[|y xs] /=; first by rewrite subseqs0.
case: (y =P a)=>[->{y}|N]; last first.
- rewrite IH; case: (subseq _)=>//=.
  by apply/negP=>/mapP [z _ [/N]].
rewrite mem_map ?IH 1?orbC; first by move=>?? [].
by apply/orP/idP; [case=>// /cons_subseq|left].
Qed.

(* useful renaming *)
Lemma subseq_f_prefix {A B : eqType} (f : A -> B) (s1 s2 : seq A) : 
        subseq s1 s2 ->
        subseq (map f s1) (map f s2).
Proof. exact: map_subseq. Qed.

(* lifting subseq_f_prefix, mem_map_subseq, map_image_subseq to subseqs *)

Lemma map_subseqs {A B : eqType} (f : A -> B) (s : seq A) xs : 
        xs \in subseqs s ->
        map f xs \in subseqs (map f s).
Proof. by rewrite !subseqsE; apply: map_subseq. Qed.

Lemma mem_map_subseqs {A B : eqType} (f : A -> B) (s : seq A) xs : 
        injective f ->
        (map f xs \in subseqs (map f s)) = (xs \in subseqs s).
Proof. by rewrite !subseqsE; apply: map_subseq_inj. Qed.

Lemma map_image_subseqs {A B : eqType} (f : A -> B) (s : seq A) xs : 
        xs \in subseqs (map f s) ->
        exists2 ys, xs = map f ys & ys \in subseqs s.
Proof.
rewrite subseqsE=>/map_image_subseq [ys ->]. 
by rewrite -subseqsE; exists ys.
Qed.

(*****************************************)
(* self-simplifying definition of suffix *)
(*****************************************)

(* TODO: upstream to mathcomp *)

Fixpoint suffx {T : eqType} (s1 s2 : seq T) {struct s2} : bool := 
  if s2 is x :: s2' then (s1 == x :: s2') || suffx s1 s2'
  else s1 == [::].

Lemma suffxE {T : eqType} (s1 s2 : seq T) : suffx s1 s2 = suffix s1 s2.
Proof.
rewrite/suffix; elim: s2 s1=>[|x2 s2 IH] s1 /=.
- by case: (lastP s1)=>[|{}s1 x1] //=; rewrite rev_rcons; case: s1.
rewrite rev_cons; apply/idP/idP; last first.
- case/rcons_prefix; first by rewrite orbC IH=>->.
  by move/revE=>->; rewrite rev_rcons revK eqxx. 
case/orP=>[/eqP ->|]; first by rewrite rev_cons; apply: prefix_refl.
by rewrite IH=>H; apply: prefix_trans (prefix_rcons _ _).
Qed.

(********************)
(* inversion lemmas *)
(********************)

(* various list morphisms in interaction with *)
(* list constructors and basic primitives *)

Lemma filter_cons_inv {A} {f : {pred A}} {xs y ys}  : 
        filter f xs = y :: ys ->
        exists xs1 xs2, 
           [/\ xs = xs1 ++ y :: xs2, 
               f y, 
               filter f xs2 = ys & 
               ~~ has f xs1].
Proof. 
elim: xs y ys=>[|x' xs IH] //= y ys; case: ifP=>N.
- by case=><-{y} <-; exists [::], xs. 
case/IH=>xs1 [xs2][-> H1 H2 H3]. 
by exists (x' :: xs1), xs2; rewrite /= N H3. 
Qed.

Lemma filter_cat_inv {A} {f : {pred A}} {xs ys1 ys2}  : 
        filter f xs = ys1 ++ ys2 ->
        exists xs1 xs2, 
          [/\ xs = xs1 ++ xs2, 
              filter f xs1 = ys1 & 
              filter f xs2 = ys2].
Proof.
elim: ys1 xs ys2=>[|y ys1 IH] xs ys2 /=.
- by move=><-; exists [::], xs. 
case/filter_cons_inv=>xs1 [xs2][->{xs} H1 /[swap] H2].
case/IH=>xs3 [xs4][->{xs2} H3 H4].
exists (xs1 ++ [:: y] ++ xs3), xs4. 
by rewrite -catA filter_cat /= H1 (hasN_filter H2) H3 H4.
Qed.

Lemma filter_rcons_inv {A} {f : {pred A}} {xs ys y}  : 
        filter f xs = rcons ys y ->
        exists xs1 xs2, 
          [/\ xs = xs1 ++ y :: xs2, 
              filter f xs1 = ys, 
              f y &
              ~~ has f xs2].
Proof.
move/(f_equal rev); rewrite -filter_rev rev_rcons.
case/filter_cons_inv=>xs1 [xs2][H1 H2 H3 H4].
rewrite -(revK xs) H1 rev_cat rev_cons -cats1 -catA /=.
exists (rev xs2), (rev xs1).
by rewrite has_rev filter_rev H3 revK.
Qed.

Lemma map_cons_inv {A B} {f : A -> B} {xs y ys}  : 
        map f xs = y :: ys ->
        exists x xs', 
          [/\ xs = x :: xs', 
              f x = y & 
              map f xs' = ys].
Proof. by elim: xs y ys=>[|x' xs' IH] // _ ys [<-]; exists x', xs'. Qed.

Lemma map_cat_inv {A B} {f : A -> B} {xs ys1 ys2} : 
        map f xs = ys1 ++ ys2 ->
        exists xs1 xs2, 
          [/\ xs = xs1 ++ xs2, 
              map f xs1 = ys1 & 
              map f xs2 = ys2].
Proof.
elim: ys1 xs ys2=>[|y1 ys1 IH] xs ys2 /=; first by exists [::], xs.
case/map_cons_inv=>x [xs'][-> H1] /IH [xs1][xs2][-> H2 H3].
by exists (x :: xs1), xs2; rewrite /= H1 H2 H3. 
Qed.

Lemma map_rcons_inv {A B} {f : A -> B} {xs ys y} : 
        map f xs = rcons ys y ->
        exists xs1 x, 
          [/\ xs = rcons xs1 x, 
              map f xs1 = ys & 
              f x = y].
Proof.
move/(f_equal rev); rewrite -map_rev rev_rcons=>/map_cons_inv [x][xs1]. 
by case=>/revE -> <- /revE <-; exists (rev xs1), x; rewrite rev_cons map_rev.  
Qed.

Lemma pmap_cons_inv {A B} {f : A -> option B} {xs y ys} :
        pmap f xs = y :: ys ->
        exists xs1 x xs2, 
          [/\ xs = xs1 ++ x :: xs2, 
              f x = Some y,
              pmap f xs2 = ys & 
              ~~ has f xs1].
Proof.
elim: xs y ys=>[|x xs IH] y ys //=; rewrite /oapp.
case D : (f x)=>[a|]; first by case=><-{y}; exists [::], x, xs. 
case/IH=>xs1 [x1][xs2][-> C H1 H2].
by exists (x :: xs1), x1, xs2; rewrite /= D C. 
Qed.

Lemma pmap_cat_inv {A B} {f : A -> option B} {xs ys1 ys2} : 
        pmap f xs = ys1 ++ ys2 ->
        exists xs1 xs2, 
          [/\ xs = xs1 ++ xs2, 
              pmap f xs1 = ys1 & 
              pmap f xs2 = ys2].
Proof.
elim: ys1 xs=>[|y1 ys1 IH] /= xs; first by exists [::], xs. 
case/pmap_cons_inv=>xs1 [x][xx][->{xs} H1 /[swap] H2]
/IH [xs3][xs4][-> H3 H4]; exists (xs1 ++ x :: xs3), xs4. 
by rewrite -catA pmap_cat /= /oapp H1 (hasN_pmap H2) H3.
Qed.

Lemma pmap_rcons_inv {A B} {f : A -> option B} {xs y ys} : 
        pmap f xs = rcons ys y ->
        exists xs1 x xs2, 
          [/\ xs = rcons xs1 x ++ xs2, 
              pmap f xs1 = ys, 
              f x = Some y & 
              ~~ has f xs2].
Proof.
move/(f_equal rev); rewrite -pmap_rev rev_rcons=>/pmap_cons_inv [xs1][x][xs2]. 
case=>/revE -> H1 /esym/revE ->; exists (rev xs2), x, (rev xs1).
by rewrite rev_cat -rev_cons pmap_rev has_rev.
Qed.

(*********************************)
(* interleaving of two sequences *)
(*********************************)

Fixpoint interleave A (s s1 s2 : seq A) := 
  match s with 
    nil => s1 = nil /\ s2 = nil
  | x :: s' =>
      (exists s1', s1 = x :: s1' /\ interleave s' s1' s2) \/
      (exists s2', s2 = x :: s2' /\ interleave s' s1 s2')
  end.

Lemma Prefix_interleave A (s s1 s2 : seq A) s' : 
        interleave s s1 s2 ->
        Prefix s' s ->
        exists s1' s2', 
          [/\ interleave s' s1' s2', 
              Prefix s1' s1 & Prefix s2' s2].
Proof.
elim: s s' s1 s2=>[|x s IH] /= s' s1 s2.
- by case=>->-> /Prefixs0 ->; exists [::], [::]. 
case=>[[+][->{s1}]|[+][->{s2}]]; 
[move=>s1|move=>s2]; move=>M /Prefix_consE.
case=>[->|[+][->{s'}]]; first by exists [::], [::]. 
- move=>s' /(IH _ _ _ M) [s1'][s2'][{}M H1 H2].
  exists (x :: s1'), s2'; split=>//=.
  - by left; exists s1'.
  by apply/Prefix_cons.
case=>[->|[+][->{s'}]]; first by exists [::], [::]. 
move=>s' /(IH _ _ _ M) [s1'][s2'][{}M H1 H2].
exists s1', (x :: s2'); split=>//=.
- by right; exists s2'.
by apply/Prefix_cons.
Qed.

Lemma interleave0 A (s1 s2 : seq A) : 
        interleave s1 s2 [::] <-> s1 = s2.
Proof.
elim: s1 s2=>[|x s1 IH] s2 /=; first by split=>//; case.
split=>[|<-]; first by case=>[[s1'][->] /IH ->|[s2'][]].
by left; exists s1; split=>//; apply/IH.
Qed.

Lemma interleave0E A (s1 s2 : seq A) : 
        interleave [::] s1 s2 -> 
        s1 = [::] /\ s2 = [::].
Proof. by []. Qed.

Lemma interleaveC A (s s1 s2 : seq A) : 
        interleave s s1 s2 -> 
        interleave s s2 s1.
Proof.
elim: s s1 s2=>[|x s IH] //= s1 s2; first by case.
by case; case=>a [->] /IH; [right|left]; exists a.
Qed.

Lemma interleaveA A (x y s1 s2 s3 : seq A) : 
        interleave x s1 s2 -> 
        interleave y x s3 -> 
        exists2 z, interleave y s1 z & 
                   interleave z s2 s3.
Proof.
elim: y x s1 s2 s3=>[|a y IH] x s1 s2 s3 /=.
- by move/[swap]; case=>->-> /= [->->]; exists [::].
move/[swap]; case=>[[s1'][->]|[s2'][->]] /= My.
- case; case=>b [->] /IH-/(_ _ My) [z] {}My Mz.
  - by exists z=>//; left; exists b. 
  by eexists (a :: z); [right; exists z|left; exists b].
move/IH=>/(_ _ My) [z] {}My Mz.
by exists (a :: z); right; [exists z|exists s2']. 
Qed.

Lemma interleave_mask A (s s1 s2 : seq A) : 
        interleave s s1 s2 <->
        exists m, 
          [/\ s1 = mask m s, 
              s2 = mask (map negb m) s &
              size s = size m].
Proof.
elim: s s1 s2=>[|x s IH] s1 s2 /=.
- by split=>[[->->]|[m][->->]]; [exists [::]|rewrite !mask0].
split.
- case; case=>_ [->] /IH [m][->->->]; 
  by [exists (true :: m)|exists (false :: m)].
case; case=>[|a m][->-> // [S]]; case: a; 
[left; exists (mask m s)|right; exists (mask (map negb m) s)];
by split=>//; apply/IH; exists m. 
Qed.

(* arbitrary finite interleaving *)

Fixpoint interleave_seq A s (xs : seq (seq A)) := 
  if xs is x :: xs then 
    exists2 s', interleave s x s' & interleave_seq s' xs
  else s = [::].

Lemma interleaves0 A (s : seq A) :
        interleave_seq s [::] -> s = [::].
Proof. by elim: s. Qed.

Lemma interleave0s A (s : seq (seq A)) :
        interleave_seq [::] s <-> 
        (forall x, x \In s -> x = [::]).
Proof. 
elim: s=>[|a s IH] //=; split.
- by case=>s' [->->] /IH H x; rewrite InE; case=>// /H. 
move=>H; exists [::].
- by split=>//; apply: H; left.
by apply/IH=>x X; apply: H; right.
Qed.

Lemma interleave_seq_cons_cat A s x (s1 s2 : seq (seq A)) : 
        interleave_seq s (x :: s1 ++ s2) ->
        interleave_seq s (s1 ++ x :: s2).
Proof.
elim: s1 s x s2=>[|a s1 IH] s x s2 //= [z1] S [z2] Z1 I.
case/interleaveC/(interleaveA Z1): S=>z3 I1 I2.
by exists z3=>//; apply: IH; exists z2=>//; apply/interleaveC.
Qed.

Lemma interleave_seq_permI A (s : seq A) (xs1 xs2 : seq (seq A)) :
        perm xs1 xs2 ->
        interleave_seq s xs1 ->
        interleave_seq s xs2.
Proof.
elim: xs1 s xs2=>[|x xs1 IH] s xs2 S /=.
- by move/interleaves0=>->; move/pperm_nil: S=>->.
case=>s' H; case: (pperm_consE S)=>s1 [s2][E] X; subst xs2.
by move/(IH s' _ X)=>Y; apply/interleave_seq_cons_cat; exists s'.
Qed.

Lemma interleave_seq_perm A (s : seq A) (xs1 xs2 : seq (seq A)) :
        perm xs1 xs2 ->
        interleave_seq s xs1 <->
        interleave_seq s xs2.
Proof. 
by move=>S; split; apply/interleave_seq_permI=>//; apply/pperm_sym. 
Qed.
