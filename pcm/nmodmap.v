(*
Copyright 2025 IMDEA Software Institute
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
From mathcomp Require Import ssrnat eqtype seq interval ssralg bigop.
From pcm Require Import options pred seqext pcm natmap.
Import ssralg.GRing.
Local Open Scope ring_scope.

(**********************************************************)
(* Theory of oevalv/oexec_le/oexec_lt where the           *)
(* sequenced operations form a (total) commutative monoid *)
(* (e.g., numbers).                                       *)
(* Here we take them to form nmodType (number module)     *)
(* to enable importing the ring library and scope         *)
(**********************************************************)

(* search for index i in history h *)
(* and if not found, return some default value *)
(* we give excplicit name to that operation *)
Definition ofind {K : ordType} {C : pred K} V (U : union_map K C V) 
  (x : V) i (h : U) : V := odflt x (find i h).

Abbreviation fnd0 := (ofind 0%R).

(* oeval and sum in number modules *)

Section OevalNModType.
Context {V : nmodType} {U : natmap V}.
Implicit Type h : U.
Local Open Scope ring_scope.

Lemma sum_dom_range h : 
        \sum_(i <- dom h) (fnd0 i h) = \sum_(i <- range h) i.
Proof.
rewrite assocs_dom !big_map.
apply: eq_bigR=>-[i v] /mem_seqP/In_assocs/In_findE E _ /=.
by rewrite /fnd0 E.
Qed.

(* oevalv *)

Lemma oevr_umfiltk s p h v : 
        oevalv +%R s (um_filterk p h) v = 
        \sum_(i <- s | p i) (fnd0 i h) + v.
Proof.
elim: s v=>[|x s IH] //= v; first by rewrite big_nil add0r.
rewrite find_umfiltk big_cons; case: ifP=>// D. 
rewrite IH /ofind [RHS]addrC [LHS]addrC addrA.
by case: (find x h)=>//=; rewrite addr0.
Qed.

Lemma oevr s h v : 
        oevalv +%R s h v = \sum_(i <- s) fnd0 i h + v.
Proof.
by rewrite -big_filter -oevr_umfiltk umfilt_predT filter_predT.
Qed.

Lemma oevr0 s h : oevalv +%R s h 0 = \sum_(i <- s) fnd0 i h.
Proof. by rewrite oevr addr0. Qed.

Lemma oevr_cat s1 s2 h : 
        oevalv +%R (s1 ++ s2) h 0 = 
        oevalv +%R s1 h 0 + oevalv +%R s2 h 0.
Proof. by rewrite !oevr0 big_cat. Qed.

Lemma oevr_cons x s h : 
        oevalv +%R (x :: s) h 0 = 
        fnd0 x h + oevalv +%R s h 0.
Proof. 
rewrite -cat1s oevr_cat /= /fnd0.
by case: (find x h)=>//= a; rewrite add0r.
Qed.

Lemma oevr_rcons x s h : 
        oevalv +%R (rcons s x) h 0 = 
        oevalv +%R s h 0 + fnd0 x h.
Proof. 
rewrite oev_rconsE /fnd0.
by case: (find x h)=>//=; rewrite addr0.
Qed.

(* oevalv is pcm morphism *)
Lemma oevr_join s h1 h2 : 
        valid (h1 \+ h2)%pcm ->
        oevalv +%R s ((h1 \+ h2)%pcm) 0 = 
        oevalv +%R s h1 0 + oevalv +%R s h2 0. 
Proof.
move=>W; elim: s=>[|x s IH]; first by rewrite /= addr0.
rewrite !oevr !big_cons -addrA -!oevr {}IH !oevr /ofind !addr0.
case: validUn (W)=>//= V1 V2 L _; rewrite findUnL //.
case: dom_find (L x)=>[|v] /=.
- by rewrite add0r addrCA. 
move=>_ _ /(_ erefl) /In_findN -> /=.
by rewrite add0r addrA.
Qed.

Lemma perm_oevr s1 s2 h v : 
        perm_eq s1 s2 ->
        oevalv +%R s1 h v = oevalv +%R s2 h v.
Proof. by move=>P; rewrite !oevr (perm_big _ P). Qed.

Lemma oevr_join2 s h1 h2 : 
        valid (h1 \+ h2)%pcm ->
        perm_eq s (dom h1 ++ dom h2) ->
        oevalv +%R s ((h1 \+ h2)%pcm) 0 =
        oevalv +%R (dom h1) h1 0 + oevalv +%R (dom h2) h2 0.
Proof.
move=>W S; rewrite (perm_oevr _ _ S) oevr_cat !oevr_join //.
by rewrite (oevFKD _ _ (disjointD W)) (oevFKD _ _ (disjointDC W)) add0r addr0.
Qed.

Lemma oexler_umfiltk s p t h v : 
        uniq s ->
        oexec_le +%R s t (um_filterk p h) v = 
        \sum_(i <- s | i <=[s] t && p i) fnd0 i h + v.
Proof. 
move=>X; rewrite /oexec_le (uniq_ux_filter _ X).
by rewrite oevr_umfiltk big_filter_cond.
Qed.

(* oexec_le *)

Lemma oexler s t h v : 
        uniq s ->
        oexec_le +%R s t h v = 
        \sum_(i <- s | i <=[s] t) fnd0 i h + v.
Proof. by move=>X; rewrite /oexec_le (uniq_ux_filter _ X) oevr big_filter. Qed.

Lemma oexler0 s t h : 
        uniq s ->
        oexec_le +%R s t h 0 = 
        \sum_(i <- s | i <=[s] t) fnd0 i h.
Proof. by move=>Us; rewrite oexler // addr0. Qed.

Lemma oexler_cat s1 s2 t h : 
        oexec_le +%R (s1 ++ s2) t h 0 = 
        if t \in s1 then oexec_le +%R s1 t h 0 else 
        oexec_le +%R s1 t h 0 + oexec_le +%R s2 t h 0.
Proof. 
rewrite oexle_cat; case: ifP=>// _.
by rewrite /oexec_le oevr addrC -[\sum_(i <- _) _]addr0 -oevr.
Qed.

Lemma oexler_join s t h1 h2 : 
        valid (h1 \+ h2)%pcm ->
        oexec_le +%R s t ((h1 \+ h2)%pcm) 0 = 
        oexec_le +%R s t h1 0 + oexec_le +%R s t h2 0. 
Proof. exact: oevr_join. Qed.

Lemma oexltr_umfiltk s p t h v : 
        uniq s ->
        oexec_lt +%R s t (um_filterk p h) v = 
        \sum_(i <- s | i <[s] t && p i) fnd0 i h + v.
Proof. 
move=>X; rewrite /oexec_lt (uniq_uo_filter _ X).
by rewrite oevr_umfiltk big_filter_cond.
Qed.

(* oexec_lt *)

Lemma oexltr s t h v : 
        uniq s ->
        oexec_lt +%R s t h v = 
        \sum_(i <- s | i <[s] t) fnd0 i h + v.
Proof. by move=>X; rewrite /oexec_lt (uniq_uo_filter _ X) oevr big_filter. Qed.

Lemma oexltr0 s t h : 
        uniq s ->
        oexec_lt +%R s t h 0 = 
        \sum_(i <- s | i <[s] t) fnd0 i h.
Proof. by move=>X; rewrite oexltr // addr0. Qed.

Lemma oexltr_cat s1 s2 t h : 
        oexec_lt +%R (s1 ++ s2) t h 0 = 
        if t \in s1 then oexec_lt +%R s1 t h 0 else 
        oexec_lt +%R s1 t h 0 + oexec_lt +%R s2 t h 0.
Proof. 
rewrite oexlt_cat; case: ifP=>// _.
by rewrite /oexec_lt oevr addrC -[\sum_(i <- _) _]addr0 -oevr.
Qed.

Lemma oexltr_join s t h1 h2 : 
        valid (h1 \+ h2)%pcm ->
        oexec_lt +%R s t ((h1 \+ h2)%pcm) 0 = 
        oexec_lt +%R s t h1 0 + oexec_lt +%R s t h2 0. 
Proof. exact: oevr_join. Qed.

(* oexler and subsequences has *)
(* two mutually exclusive lemmas, both asuming t1 \in s1 *)

(* if everything not in s1 is bigger than t1 *)
Lemma perm_oexle1 s1 s2 s t1 h : 
        uniq s ->
        subseq s1 s ->
        subseq s2 s ->
        perm_eq s (s1 ++ s2) ->
        (* t1 needn't be last in s1 *)
        t1 \in s1 ->
        (* everything in s2 must be after t1 *)
        ~~ has (fun x => x <[s] t1) s2 ->
        oexec_le +%R s t1 h 0 = oexec_le +%R s1 t1 h 0.
Proof.
move=>Us S1 S2 P T1 H; have Us1 : uniq s1 by apply: subseq_uniq Us.
rewrite !oexler0 // (perm_big _ P) big_cat /= addrC big_hasC ?add0r; last first.
- by rewrite big_mkcond [RHS]big_mkcond; apply: eq_bigR=>i /(sle_subseq S1) ->.
have N : {in s2, forall x, x \notin s1}.
- by move: Us (perm_uniq P)=>-> /esym; rewrite cat_uniq=>/and3P [_ /hasPn].
move/hasPn: H=>H; apply/hasPn=>z X; rewrite sle_eqVlt.
- by rewrite (perm_mem P) mem_cat X orbT.
by rewrite negb_or; case: eqP X T1=>[->{z}/N/negbTE ->|_ /H].
Qed.

(* if there exists x not in s1 that's smaller than t1 *)
Lemma perm_oexle2 s1 s2 s t1 h : 
        uniq s ->
        subseq s1 s ->
        subseq s2 s ->
        perm_eq s (s1 ++ s2) ->
        t1 \in s1 ->
        has (fun x => x <[s] t1) s2 ->
        exists t2,
          [/\ t2 \in s2, t2 <[s] t1, 
              {in s2, forall z, t2 <[s2] z -> ~~ z <[s] t1} &
              oexec_le +%R s t1 h 0 = oexec_le +%R s1 t1 h 0 + 
                                      oexec_le +%R s2 t2 h 0].
Proof.
move=>Us S1 S2 P T1 X; have : uniq (s1 ++ s2) by rewrite -(perm_uniq P).
rewrite cat_uniq=>/and3P [U1 /hasPn N U2].
case/(slt_findlast U2): X=>t2 [T2 T X]; exists t2; split=>//.
rewrite !oexler0 // (perm_big _ P) big_cat /=; congr (_ + _).
- by rewrite big_mkcond [RHS]big_mkcond; apply: eq_bigR=>i /(sle_subseq S1) ->.
rewrite big_mkcond [RHS]big_mkcond; apply: eq_bigR=>i I _. 
rewrite sle_eqVlt ?(perm_mem P) ?mem_cat ?I ?orbT //.
case: eqP T1 (N _ I)=>[->->|_ _ _] //=. 
rewrite (_ : i <[s] t1 = i <=[s2] t2) //.
apply/idP/idP=>[Z|]; first by rewrite sleNgt (contraL (X _ I)).
by rewrite (sle_subseq S2 Us) //; move/sle_slt_trans; apply.
Qed.

Lemma perm_oexleL s1 s2 s t1 h : 
        uniq s ->
        subseq s1 s ->
        subseq s2 s ->
        perm_eq s (s1 ++ s2) ->
        t1 \in s1 ->
        exists2 s2', prefix s2' s2 &
          oexec_le +%R s t1 h 0 = oexec_le +%R s1 t1 h 0 + 
                                  oevalv +%R s2' h 0.
Proof.
move=>Us S1 S2 P T1.
have [X|X] := boolP (has (fun x => x <[s] t1) s2); last first.
- exists [::]; first by apply: prefix0s.
  by rewrite (perm_oexle1 _ Us S1 S2 P T1 X) addr0.
case/(perm_oexle2 h Us S1 S2 P T1): X=>t2 [T2 _ _] ->.
by exists &=s2 `]-oo, t2]=>//; apply: prefix_eqsl.
Qed.

Lemma perm_oexleR s1 s2 s t2 h : 
        uniq s ->
        subseq s1 s ->
        subseq s2 s ->
        perm_eq s (s1 ++ s2) ->
        t2 \in s2 ->
        exists2 s1', prefix s1' s1 &
          oexec_le +%R s t2 h 0 = oevalv +%R s1' h 0 + 
                                  oexec_le +%R s2 t2 h 0.
Proof.
move=>Us S1 S2 P T1.
have {}P : perm_eq s (s2 ++ s1) by apply/perm_trans/permPl/perm_catC/P.
case: (perm_oexleL h Us S2 S1 P T1)=>s1' P1 ->; exists s1'=>//.
by rewrite addrC.
Qed.

End OevalNModType.

(* sum of two sequences in terms of set difference *)

Lemma sumrD {I : eqType} {U : nmodType} (F : I -> U) (s1 s2 : seq I) :
        uniq s1 ->
        uniq s2 ->
        \sum_(i <- s1) F i + \sum_(i <- s2 | i \notin s1) F i = 
        \sum_(i <- s2) F i + \sum_(i <- s1 | i \notin s2) F i.
Proof.
move=>U1 U2.
rewrite [in LHS](bigID_idem (addr0 _) _ [in s2]) /=.
rewrite [in RHS](bigID_idem (addr0 _) _ [in s1]) /=.
rewrite addrAC -!addrA; congr (_ + _).
rewrite -[LHS]big_filter -[RHS]big_filter.
by apply/perm_big/uniq_perm/filter_mem_sym; rewrite filter_uniq.
Qed.

(*********************************************)
(* quantification over partial and full sums *) 
(*********************************************)

(* partial sums range over all prefixes *)
Definition all_presums {V : nmodType} (P : V -> bool) (s : seq V) : bool :=
  all (fun pfx => P (\sum_(i <- pfx) i)%R) (prefixes s).

(* full sum takes the full prefix *)
Definition end_sum {V : nmodType} (P : V -> bool) (s : seq V) : bool := 
  P (\sum_(i <- s) i)%R.

Lemma end_presum {V : nmodType} (P : V -> bool) (s : seq V) : 
       all_presums P s ->
       end_sum P s.
Proof. by move/allP=>/= /(_ _ (prefixesT _)). Qed.

Lemma consistently_oexle {V : nmodType}  (P : V -> bool) (h : history V) s :
        uniq s ->
        reflect [/\ P 0%R & forall t, t \in s -> P (oexec_le +%R s t h 0%R)]
                (all_presums P [seq fnd0 i h | i <- s]).
Proof.
move=>Us; apply/(iffP allP)=>[/= H|[/= H1 H2]].
- split=>[|t Dt]; first by move: (H [::] (prefixes0 _)); rewrite big_nil. 
  set F0 := fun i => fnd0 i h.
  have /H : map F0 &=s `]-oo, t] \in prefixes (map F0 s).
  - by rewrite map_f_prefixes // prefixesE prefix_eqsl.
  by rewrite big_map -[(\sum_(_ <- _) _)%R]addr0 -oevr.  
move=>_ /map_image_prefixes [/= pfx ->].
rewrite prefixesE=>/(eqsl_prefix Us) [->|[t /H2 /[swap] ->]].
- by rewrite big_nil.
by rewrite /oexec_le oevr // addr0 big_map.
Qed.

