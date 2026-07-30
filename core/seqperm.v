(*
Copyright 2017 IMDEA Software Institute
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
From mathcomp Require Import ssrnat seq path eqtype.
From pcm Require Import options pred autouniq.

(****************************************************)
(* A theory of permutations over non-equality types *)
(****************************************************)

Section Permutations.
Variable A : Type.

Inductive perm : seq A -> seq A -> Prop :=
| permutation_nil : perm [::] [::]
| permutation_skip x s1 s2 of perm s1 s2 : perm (x :: s1) (x :: s2)
| permutation_swap x y s1 s2 of perm s1 s2 : perm [:: x, y & s1] [:: y, x & s2]
| permutation_trans t s1 s2 of perm s1 t & perm t s2 : perm s1 s2.

Lemma pperm_refl (s : seq A) : perm s s.
Proof. by elim: s=>*; [apply: permutation_nil | apply: permutation_skip]. Qed.

Hint Resolve pperm_refl : core.

Lemma pperm_nil (s : seq A) : 
        perm [::] s <-> s = [::].
Proof.
split; last by move=>->; apply: permutation_nil.
move E: {1}[::]=>l H; move: H {E}(esym E).
by elim=>//??? _ IH1 _ IH2 /IH1/IH2.
Qed.

Lemma pperm_sym s1 s2 : 
        perm s1 s2 <-> perm s2 s1.
Proof.
suff {s1 s2} L : forall s1 s2, perm s1 s2 -> perm s2 s1 by split; apply: L.
apply: perm_ind=>[|||??? _ H1 _ H2] *;
by [apply: permutation_nil | apply: permutation_skip |
    apply: permutation_swap | apply: permutation_trans H2 H1].
Qed.

Lemma pperm_trans s2 s1 s3 : 
        perm s1 s2 -> 
        perm s2 s3 -> 
        perm s1 s3.
Proof. by apply: permutation_trans. Qed.

Lemma pperm_in s1 s2 x : 
        perm s1 s2 -> 
        x \In s1 -> 
        x \In s2.
Proof. elim=>//??? =>[|?|_ I1 _ I2 /I1/I2]; rewrite ?InE; tauto. Qed.

Lemma pperm_catC s1 s2 : perm (s1 ++ s2) (s2 ++ s1).
Proof.
elim: s1 s2=>[|x s1 IH1] s2 /=; first by rewrite cats0.
apply: (@pperm_trans (x::s2++s1)); first by apply: permutation_skip.
elim: s2=>[|y s2 IH2] //=.
apply: (@pperm_trans (y::x::s2++s1)); first by apply: permutation_swap.
by apply: permutation_skip.
Qed.

Hint Resolve pperm_catC : core.

Lemma pperm_cat2lL s s1 s2 : 
        perm s1 s2 -> 
        perm (s ++ s1) (s ++ s2).
Proof. by elim: s=>[//|e s IH /IH]; apply: permutation_skip. Qed.

Lemma pperm_cat2rL s s1 s2 : 
        perm s1 s2 -> 
        perm (s1 ++ s) (s2 ++ s).
Proof.
move=>?.
apply: (@pperm_trans (s ++ s1)); first by apply: pperm_catC.
apply: (@pperm_trans (s ++ s2)); last by apply: pperm_catC.
by apply: pperm_cat2lL.
Qed.

Lemma pperm_catL s1 t1 s2 t2 :
        perm s1 s2 -> 
        perm t1 t2 -> 
        perm (s1 ++ t1) (s2 ++ t2).
Proof. by move/(pperm_cat2rL t1)=>H1/(pperm_cat2lL s2); apply: pperm_trans. Qed.

Lemma pperm_cat_consL s1 t1 s2 t2 x :
        perm s1 s2 -> 
        perm t1 t2 -> 
        perm (s1 ++ x :: t1) (s2 ++ x :: t2).
Proof. by move=>*; apply: pperm_catL=>//; apply: permutation_skip. Qed.

Lemma pperm_cons_catCA s1 s2 x : 
        perm (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
rewrite -cat1s -(cat1s _ s2) !catA.
by apply/pperm_cat2rL/pperm_catC.
Qed.

Lemma pperm_cons_catAC s1 s2 x : 
        perm (s1 ++ x :: s2) (x :: s1 ++ s2).
Proof. by apply/pperm_sym/pperm_cons_catCA. Qed.

Hint Resolve pperm_cons_catCA pperm_cons_catAC : core.

Lemma pperm_cons_cat_consL s1 s2 s x :
        perm s (s1 ++ s2) -> 
        perm (x :: s) (s1 ++ x :: s2).
Proof.
move=>?.
apply: (@pperm_trans (x :: (s1 ++ s2))); first by apply: permutation_skip.
by apply: pperm_cons_catCA.
Qed.

Lemma pperm_size l1 l2 : 
        perm l1 l2 -> 
        size l1 = size l2.
Proof. by elim=>//=???? =>[|?|]->. Qed.

Lemma pperm_cat_consR s1 s2 t1 t2 x :
        perm (s1 ++ x :: t1) (s2 ++ x :: t2) -> 
        perm (s1 ++ t1) (s2 ++ t2).
Proof.
move: s1 t1 s2 t2 x.
suff H:
  forall r1 r2, perm r1 r2 -> forall x s1 t1 s2 t2,
    r1 = s1 ++ x :: t1 -> r2 = s2 ++ x :: t2 -> perm (s1 ++ t1) (s2 ++ t2).
- by move=>s1 t1 s2 t2 x /H; apply.
apply: perm_ind; last 1 first.
- move=>s2 s1 s3 H1 IH1 H2 IH2 x r1 t1 r2 t2 E1 E2.
  case: (@In_split _ x s2).
  - by apply: pperm_in H1 _; rewrite E1 In_cat; right; left.
  move=>s4 [s5] E; apply: (@pperm_trans (s4++s5)); first by apply: IH1 E1 E.
  by apply: IH2 E E2.
- by move=>x [].
- move=>x t1 t2 H IH y [|b s1] s2 [|c p1] p2 /= [E1 E2] [E3 E4]; subst x;
    rewrite ?E1 ?E2 ?E3 ?E4 in H * =>//.
  - by subst y; apply: pperm_trans H _.
  - by apply: pperm_trans H.
  by apply: permutation_skip=>//; apply: IH E2 E4.
move=>x y p1 p2 H IH z [|b s1] t1 [|c s2] t2 /= [E1 E2] [E3 E4]; subst x y;
  rewrite -?E2 -?E4 in H IH * =>//.
- by apply: permutation_skip.
- case: s2 E4=>/=[|a s2][<-]=>[|E4]; apply: permutation_skip=>//.
  by subst p2; apply: pperm_trans H _; apply pperm_cons_catAC.
- case: s1 E2=>/=[|a s1][<-]=>[|E2]; apply: permutation_skip=>//.
  by subst p1; apply: pperm_trans H; apply pperm_cons_catCA.
case: s1 E2=>/=[|a s1][->]=>E2; case: s2 E4=>/=[|d s2][->]=>E4;
  rewrite ?E2 ?E4 in H IH *.
- by apply: permutation_skip.
- apply: (@pperm_trans [:: d, z & s2 ++ t2]); last by apply: permutation_swap.
  by apply: permutation_skip=>//; apply/(pperm_trans H _ )/pperm_cons_catAC.
- apply: (@pperm_trans [:: a, z & s1 ++ t1]); first by apply: permutation_swap.
  by apply: permutation_skip=>//; apply/pperm_trans/H/pperm_cons_catCA.
by apply: permutation_swap; apply: IH.
Qed.

Lemma pperm_cons x s1 s2 : 
        perm (x :: s1) (x :: s2) <-> perm s1 s2.
Proof.
by split; [apply/(@pperm_cat_consR [::] [::]) | apply: permutation_skip].
Qed.

Lemma pperm_cat2l s s1 s2: 
        perm (s ++ s1) (s ++ s2) <-> perm s1 s2.
Proof. by split; [elim: s=>// ??? /pperm_cons | apply: pperm_cat2lL]. Qed.

Lemma pperm_cat2r s s1 s2 : 
        perm (s1 ++ s) (s2 ++ s) <-> perm s1 s2.
Proof.
split; last by apply: pperm_cat2rL.
by elim: s=>[|??? /pperm_cat_consR]; rewrite ?cats0.
Qed.

Lemma pperm_catAC s1 s2 s3 : 
        perm ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof. by move=>*; rewrite -!catA pperm_cat2l. Qed.

Lemma pperm_catCA s1 s2 s3 : 
        perm (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof. by move=>*; rewrite !catA pperm_cat2r. Qed.

Lemma pperm_cons_cat_cons x s1 s2 s :
        perm (x :: s) (s1 ++ x :: s2) <-> 
        perm s (s1 ++ s2).
Proof.
by split; [apply: (@pperm_cat_consR [::]) | apply: pperm_cons_cat_consL].
Qed.

Lemma pperm_consE x s s' : 
        perm (x :: s') s ->
        exists s1 s2, 
          s = s1 ++ x :: s2 /\  
          perm s' (s1 ++ s2).
Proof.
move=>S; have : x \In s by apply/(pperm_in S); left.
case/In_split=>s1 [s2] E; move: E S=>->.
by move/pperm_cons_cat_cons; exists s1, s2. 
Qed.

Lemma pperm_cat_cons x s1 s2 t1 t2 :
        perm (s1 ++ x :: t1) (s2 ++ x :: t2) <-> 
        perm (s1 ++ t1) (s2 ++ t2).
Proof.
split=>[|H]; first by apply: pperm_cat_consR.
apply: (@pperm_trans (x::s1++t1))=>//; apply: (@pperm_trans (x::s2++t2))=>//.
by apply/pperm_cons.
Qed.

Lemma pperm_cat_consE x t1 t2 s :
        perm (t1 ++ x :: t2) s <-> 
        exists s1 s2, 
          s = s1 ++ x :: s2 /\ 
          perm (t1 ++ t2) (s1 ++ s2).
Proof.
split=>[|[s1][s2][->]] T; last by apply/pperm_cat_cons.
by apply/pperm_consE/pperm_trans/T/pperm_cons_cat_cons.
Qed.

Lemma pperm_rcons s1 s2 x : 
       perm s1 s2 <->
       perm (rcons s1 x) (rcons s2 x).
Proof.
rewrite -!cats1; split=>[|H]; first by apply: pperm_cat2rL.
by rewrite -[s1]cats0 -[s2]cats0 -(pperm_cat_cons x).
Qed.

Lemma pperm_rev s : perm s (rev s).
Proof.
elim: s=>[|x xs IH] //=.
rewrite rev_cons -cats1.
apply: (@pperm_trans ([:: x] ++ rev xs)); last by apply: pperm_catC.
by rewrite pperm_cons. 
Qed.

Lemma pperm1 {s : seq A} (x : A) :
        perm s [:: x] <-> s = [:: x].
Proof.
split=>[/pperm_sym H|->//].
have X : x \In s by apply: pperm_in H _; rewrite InE.
case/In_split: X H=>s1 [s2] ->{s} /pperm_cons_cat_cons/pperm_nil.
by case: s1=>//; case: s2.
Qed.

Lemma pperm_rcons_cons s x : 
        perm (rcons s x) (x :: s).
Proof.
rewrite -(revK (x :: _)) rev_cons; apply/pperm_trans/pperm_rev. 
by rewrite -(pperm_rcons _ _ x); apply/pperm_rev.
Qed.

End Permutations.

#[export] Hint Resolve pperm_refl pperm_catC pperm_cons_catCA
   pperm_cons_catAC pperm_catAC pperm_catCA : core.

(* perm and map *)
Lemma pperm_map A B (f : A -> B) (s1 s2 : seq A) :
        perm s1 s2 -> 
        perm (map f s1) (map f s2).
Proof.
elim=>[//|||??? _ IH1 _ IH2]*;
by [apply/pperm_cons|apply/permutation_swap|apply/(pperm_trans IH1 IH2)].
Qed.

Lemma pperm_pmap A B (f : A -> option B) (s1 s2 : seq A) :
        perm s1 s2 -> 
        perm (pmap f s1) (pmap f s2).
Proof.
elim=>[//|a x1 x2 H IH|a b x1 x2 H IH|a x1 x2 H1 IH1 H2 IH2] /=; 
last 1 first.
- by apply/pperm_trans/IH2/IH1.
- by case: (f a)=>[a'|] //=; apply/pperm_cons.
case: (f a)=>[a'|]; case: (f b)=>[b'|] //=; try by [apply/pperm_cons].
by apply/permutation_swap.
Qed.

(* perm and uniq *)

Lemma pperm_Uniq A (s1 s2 : seq A) : 
        perm s1 s2 ->
        Uniq s1 <-> Uniq s2.
Proof.
suff {s1 s2} H : forall (s1 s2 : seq A), perm s1 s2 -> Uniq s1 -> Uniq s2.
- by move=>P; split;apply/H=>//; apply/pperm_sym/P.
move=>s1 s2; elim=>[//|a x1 x2 H IH|a b x1 x2 H IH|a x1 x2 _ IH1 _ IH2] /=;
last 1 first.
- by move/IH1/IH2.
- case=>X1 X2; split; last by apply/IH.
  by move=>Z; apply/X1/pperm_in/Z/pperm_sym.
case=>X1 [X2 X3]; split.
- move=>Z; apply/X1; rewrite !InE in Z *.
  case: Z; first by left.
  by move/pperm_sym: H=>H; move/(pperm_in H)/X2.
split; last by apply/IH.
by move/pperm_sym: H=>H; move/(pperm_in H)=>Z; apply/X1; right.
Qed.

Lemma pperm_uniq (A : eqType) (s1 s2 : seq A) : 
        perm s1 s2 ->
        uniq s1 = uniq s2.
Proof. by move/pperm_Uniq=>H; apply/UniqP/UniqP; rewrite H. Qed.

(* mapping to ssreflect decidable perm *)
Lemma perm_eq_perm {A : eqType} (s1 s2 : seq A) :
        reflect (perm s1 s2) (perm_eq s1 s2).
Proof.
apply: (iffP idP); last first.
- elim=>[|||??? _ H1 _ H2]*.
  - by apply perm_refl.
  - by rewrite perm_cons.
  - by rewrite -![[:: _, _ & _]]/([::_] ++ [::_] ++ _) perm_catCA;
       rewrite !perm_cat2l.
  by apply: perm_trans H1 H2.
elim: s2 s1 =>[s1 /perm_size/size0nil->// | x s2 IH s1 H].
move: (perm_mem H x); rewrite mem_head=>H'; move: H' H.
move/splitPr=>[p1 p2]; rewrite -cat1s perm_catCA perm_cons=>/IH.
by rewrite -[_::s2]cat0s pperm_cat_cons.
Qed.

Lemma pperm_merge T (leT : rel T) s1 s2 : 
        perm (merge leT s1 s2) (s1 ++ s2).
Proof.
elim: s1 s2=>[|x s1 IH] /=; first by elim.
elim=>[|y s2 IH2] /=; first by rewrite cats0.
case: ifP=>H.
- by apply/pperm_cons/pperm_trans/pperm_refl/IH.
rewrite -!cat_cons in IH2 *.
apply/pperm_trans/pperm_cons_catCA/pperm_cons.
by apply/pperm_trans/IH2; case: {IH2} s2.
Qed.

Lemma pperm_merge_sort_push T (leT : rel T) xs yss : 
        perm (flatten (merge_sort_push leT xs yss)) 
             (xs ++ flatten yss).
Proof.
elim: yss xs=>[|[|y ys] yss IH] xs //=.
apply: pperm_trans (IH _) _; rewrite -cat_cons catA.
by apply/pperm_cat2r/pperm_trans/pperm_cons_cat_cons
/pperm_catC/pperm_merge.
Qed.

Lemma pperm_sort T (leT : rel T) xs : 
        perm (sort leT xs) xs.
Proof.
rewrite sortE; rewrite {2}(_ : xs = flatten [::] ++ xs) //.
elim: xs [::]=>[|x xs IH] ss /=.
- elim: ss [::]=>//= s ss IH t.
  apply: pperm_trans (IH (merge leT s t)) _.
  apply/pperm_trans/pperm_catAC/pperm_trans/pperm_catC. 
  by apply/pperm_cat2l/pperm_merge.
apply: pperm_trans {IH}(IH _) _; rewrite -(cat1s x xs).
elim: {x} ss [:: x]=>[|x ss IH] ys /=; first by rewrite cats0.
move/(_ (merge leT x ys)): IH; case: x=>[|x s] IH /=.
- by rewrite catA pperm_cat2r; apply/pperm_catC.
apply: pperm_trans IH _.
rewrite -cat_cons !catA; apply/pperm_cat2r.
rewrite -cat_cons -catA; apply/pperm_trans/pperm_catCA.
by apply/pperm_cat2l/pperm_trans/pperm_refl/pperm_merge.
Qed.

(************************************)
(* Membership lemmas for sortedness *)
(************************************)

Lemma In_merge T (leT : rel T) s1 s2 x : 
        x \In merge leT s1 s2 <-> x \In s1 ++ s2.
Proof.
split; first by apply/pperm_in/pperm_merge.
by apply/pperm_in/pperm_sym/pperm_merge.
Qed.

Lemma In_merge_sort_push T (leT : rel T) xs ys x : 
        x \In flatten (merge_sort_push leT xs ys) <-> 
        x \In xs ++ flatten ys.
Proof.
split.
- by apply/pperm_in/pperm_merge_sort_push.
by apply/pperm_in/pperm_sym/pperm_merge_sort_push.
Qed.

Lemma In_sort T (leT : rel T) xs x : 
        x \In sort leT xs <-> x \In xs.
Proof.
split; first by apply/pperm_in/pperm_sort.
by apply/pperm_in/pperm_sym/pperm_sort.
Qed.

(* decidable variants *)

Lemma mem_merge (T : eqType) (leT : rel T) s1 s2 x : 
       (x \in merge leT s1 s2) = (x \in s1 ++ s2).
Proof.
apply/idP/idP; first by move/mem_seqP/In_merge/mem_seqP.
by move/mem_seqP/(In_merge leT)/mem_seqP.
Qed.

Lemma mem_merge_sort_push (T : eqType) (leT : rel T) xs ys : 
        flatten (merge_sort_push leT xs ys) =i
        xs ++ flatten ys.
Proof.
move=>x.
by apply/idP/idP=>/mem_seqP/(In_merge_sort_push leT)/mem_seqP.
Qed.

(* mem_sort already exists *)

(*************************************************)
(* Interaction of sorting with reflexive closure *)
(* of the sorting relation                       *)
(*************************************************)

(* if sequence has no repetitions, sorting relation *)
(* can be irreflexive because sorting wouldn't *)
(* compare equal elements *)


Lemma merge_lt_le (T : eqType) (ltT : rel T) s1 s2 :
        uniq (s1 ++ s2) ->
        merge (fun x y => (x == y) || ltT x y) s1 s2 = 
        merge ltT s1 s2.
Proof.
elim: s1 s2=>[|x1 s1 IH] s2 /=; first by elim: s2.
elim: s2=>[|x2 s2 IH2] /andP [N Uq] //; rewrite [LHS]/=. 
case: (x1 =P x2) N Uq=>[<-|_] N Uq; rewrite [LHS]/=.
- by rewrite mem_cat inE eqxx orbT in N.
rewrite IH //=; case: ifP=>// _; congr cons; apply: IH2.
rewrite (uniqX' Uq) andbT (contra _ N) //.
by rewrite !mem_cat inE; case/orP => ->; rewrite ?orbT.
Qed.

Lemma merge_sort_push_lt_le (T : eqType) (ltT : rel T) xs yss :
        uniq (xs ++ flatten yss) ->
        merge_sort_push (fun x y => (x == y) || ltT x y) xs yss = 
        merge_sort_push ltT xs yss.
Proof.
elim: yss xs=>[|[|y ys] yss IH] //= xs Uq; congr cons.
rewrite merge_lt_le // ?(uniqX' Uq) //; apply: IH.
rewrite cat_uniq; set x := ~~ has _ _.
rewrite (_ : x = ~~ has [in y :: ys ++ xs] (flatten yss)).
- by apply/hasPn/hasPn=>H z /H; rewrite mem_merge. 
by rewrite merge_uniq -cat_uniq !(uniqX' Uq).
Qed.

Lemma merge_sort_push_uniq (T : eqType) (ltT : rel T) xs ys :
        uniq (flatten (merge_sort_push ltT xs ys)) = 
        uniq (xs ++ flatten ys).
Proof. by apply/perm_uniq/perm_eq_perm/pperm_merge_sort_push. Qed.

Lemma sort_lt_le (T : eqType) (ltT : rel T) xs :
        uniq xs ->
        sort (fun x y => (x == y) || ltT x y) xs = 
        sort ltT xs.
Proof.
rewrite !sortE {1}(_ : xs = flatten [::] ++ xs) //.
elim: xs [::]=>[|x xs IH] ss /=.
- elim: ss [::]=>[|s ss IH] xs //= Uq.
  rewrite IH; last by rewrite merge_lt_le // (uniqX' Uq).
  rewrite merge_lt_le ?(uniqX' Uq) // cat_uniq merge_uniq.
  set x := ~~ has _ _; rewrite (_ : x = ~~ has [in flatten ss] (s ++ xs)).
  - by apply/hasPn/hasPn=>H z; [rewrite -(mem_merge ltT)|rewrite mem_merge]; move=>/H.
  by rewrite -cat_uniq (uniqX' Uq).
elim: ss x=>[|s ss IH2] x //= Uq; first by apply: IH.
set X1 := (X in sort_rec1 _ X); set X2 := (X in _ = sort_rec1 _ X xs).
rewrite (_ : X1 = X2).
- rewrite {}/X1{}/X2; case: s Uq=>// y s Uq; congr cons.
  rewrite merge_lt_le ?merge_sort_push_lt_le ?(uniqX' Uq) //.
  rewrite cat_uniq merge_uniq; set X := ~~ has _ _.
  rewrite (_ : X = ~~ has [in y :: s ++ [:: x]] (flatten ss)).
  - by apply/hasPn/hasPn=>H z /H; rewrite mem_merge.
  by rewrite -cat_uniq (uniqX' Uq).
rewrite IH // {X1}/X2; case: s Uq=>[|a s] Uq /=; first by rewrite !(uniqX' Uq). 
set j := if _ then _ else _; rewrite cat_uniq merge_sort_push_uniq.
set X := ~~ has _ _; rewrite (_ : X = ~~ has [in j ++ flatten ss] xs).
- by apply/hasPn/hasPn=>H z /H; rewrite mem_merge_sort_push.
rewrite -{X}cat_uniq /j /=; case: ifP=>_; last by rewrite (uniqX' Uq).
rewrite /= !mem_cat mem_merge -!mem_cat 2!cat_uniq merge_uniq.
set X := ~~ has _ _; rewrite (_ : X = ~~ has [in s ++ [:: x]] (flatten ss)).
- by apply/hasPn/hasPn=>H z /H; rewrite mem_merge.
rewrite -{X}cat_uniq; set X := ~~ has _ _.
rewrite (_ : X = ~~ has [in (s ++ [:: x]) ++ flatten ss] xs).
- by apply/hasPn/hasPn=>H z /H; rewrite !mem_cat mem_merge -!mem_cat.
by rewrite -{X}cat_uniq !(uniqX' Uq).
Qed.








