(*
Copyright 2010 IMDEA Software Institute
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

(******************************************************************************)
(* This file defines ordType - the structure for types with a decidable       *)
(* (strict) order relation.                                                   *)
(* ordType is a subclass of mathcomp's eqType                                 *)
(* This file also defines some important instances of ordType                 *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype.
From fcsl Require Import options.

Module Ordered.

Section RawMixin.

Structure mixin_of (T : eqType) :=
  Mixin {ordering : rel T;
         _ : irreflexive ordering;
         _ : transitive ordering;
         _ : forall x y, x != y -> ordering x y || ordering y x}.

End RawMixin.

(* the class takes a naked type T and returns all the *)
(* related mixins; the inherited ones and the added ones *)
Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T;
   mixin : mixin_of (EqType T base)}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

(* produce an ordered type out of the inherited mixins *)
(* equalize m0 and m by means of a phantom; will be exploited *)
(* further down in the definition of OrdType *)
Definition pack b (m0 : mixin_of (EqType T b)) :=
  fun m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := Eval hnf in EqType cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Notation ordType := Ordered.type.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T _ m _ id).
Definition ord T : rel (sort T) := (ordering (mixin (class T))).
Notation "[ 'ordType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.
End Exports.
End Ordered.
Export Ordered.Exports.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

(* Remove when dropping the compatibility with MathComp 1.11.0: *)
Local Lemma irr_sorted_eq (T : eqType) (leT : rel T) :
  transitive leT -> irreflexive leT ->
  forall s1 s2 : seq T, sorted leT s1 -> sorted leT s2 -> s1 =i s2 -> s1 = s2.
Proof. by [exact: irr_sorted_eq | exact: eq_sorted_irr]. Qed.

Section Lemmas.
Variable T : ordType.
Implicit Types x y : T.

Lemma irr : irreflexive (@ord T).
Proof. by case: T=>s [b [m]]. Qed.

Lemma trans : transitive (@ord T).
Proof. by case: T=>s [b [m]]. Qed.

Lemma semiconnex x y : x != y -> ord x y || ord y x.
Proof. by case: T x y=>s [b [m]]. Qed.

Lemma ord_total x y : [|| ord x y, x == y | ord y x].
Proof.
case E: (x == y)=>/=; first by rewrite orbT.
by apply: semiconnex; rewrite negbT.
Qed.

Lemma nsym x y : ord x y -> ord y x -> False.
Proof. by move=>E1 E2; move: (trans E1 E2); rewrite irr. Qed.

Lemma orefl x : oleq x x.
Proof. by rewrite /oleq eq_refl orbT. Qed.

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=; case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1; case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1.
Qed.

Lemma oantisym : antisymmetric (@oleq T).
Proof.
move=>x y; rewrite /oleq (eq_sym x).
case: eqP=>// _; rewrite !orbF=>/andP [H1 H2].
by move: (trans H1 H2); rewrite irr.
Qed.

Lemma subrel_ord : subrel (@ord T) oleq.
Proof. exact: subrelUl. Qed.

Lemma sorted_oleq s : sorted (@ord T) s -> sorted (@oleq T) s.
Proof. by case: s=>//= x s; apply/sub_path/subrel_ord. Qed.

Lemma path_filter (r : rel T) (tr : transitive r) s (p : pred T) x :
        path r x s -> path r x (filter p s).
Proof. exact: (subseq_order_path tr (filter_subseq p s)). Qed.

Lemma ord_sorted_eq (s1 s2 : seq T) :
        sorted ord s1 -> sorted ord s2 -> s1 =i s2 -> s1 = s2.
Proof. exact/irr_sorted_eq/irr/trans. Qed.

End Lemmas.

Hint Resolve orefl irr trans otrans oantisym : core.

Section Totality.
Variable K : ordType.

Variant total_spec (x y : K) : bool -> bool -> bool -> Type :=
| total_spec_lt of ord x y : total_spec x y true false false
| total_spec_eq of x == y : total_spec x y false true false
| total_spec_gt of ord y x : total_spec x y false false true.

Lemma ordP x y : total_spec x y (ord x y) (x == y) (ord y x).
Proof.
case H1: (x == y).
- by rewrite (eqP H1) irr; apply: total_spec_eq.
case H2: (ord x y); case H3: (ord y x).
- by case: (nsym H2 H3).
- by apply: total_spec_lt H2.
- by apply: total_spec_gt H3.
by move: (ord_total x y); rewrite H1 H2 H3.
Qed.
End Totality.

Lemma eq_oleq (K : ordType) (x y : K) : (x == y) = oleq x y && oleq y x.
Proof. by rewrite /oleq (eq_sym x); case: ordP. Qed.

(* Monotone (i.e. strictly increasing) functions for Ord Types *)
Section Mono.
Variables (A B :ordType).

Definition strictly_increasing f x y := @ord A x y -> @ord B (f x) (f y).

Structure mono : Type := Mono
           {fun_of: A -> B; _: forall x y, strictly_increasing fun_of x y}.

End Mono.
Arguments strictly_increasing {A B} f x y.
Arguments Mono {A B _} _.

Section Weakening.
Variable T : ordType.
Implicit Types x y : T.

Lemma ordW x y: ord x y -> oleq x y.
Proof. by rewrite /oleq =>->//. Qed.

Lemma oleqNord x y: oleq x y = ~~ (ord y x).
Proof. by rewrite/oleq; case:(ordP x y)=>//. Qed.

Variant oleq_spec x y : bool -> bool -> Type :=
| oleq_spec_le of oleq x y : oleq_spec x y true false
| oleq_spec_gt of ord y x : oleq_spec x y false true.

Lemma oleqP x y : oleq_spec x y (oleq x y) (ord y x).
Proof.
case:(ordP x y).
- by move=>/ordW O; rewrite O; apply: oleq_spec_le.
- by move=>/eqP E; rewrite E orefl; apply: oleq_spec_le; apply: orefl.
by move=>O; rewrite oleqNord O //=; apply: oleq_spec_gt.
Qed.

Lemma oleq_total x y: oleq x y || oleq y x.
Proof. by case:oleqP=>// /ordW ->//. Qed.

End Weakening.

Section NatOrd.
Lemma irr_ltn_nat : irreflexive ltn. Proof. by move=>x; rewrite /= ltnn. Qed.
Lemma trans_ltn_nat : transitive ltn. Proof. by apply: ltn_trans. Qed.
Lemma semiconn_ltn_nat x y : x != y -> (x < y) || (y < x).
Proof. by case: ltngtP. Qed.

Definition nat_ordMixin := OrdMixin irr_ltn_nat trans_ltn_nat semiconn_ltn_nat.
Canonical Structure nat_ordType := Eval hnf in OrdType nat nat_ordMixin.
End NatOrd.

Section ProdOrd.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) :=
  fun x y => if x.1 == y.1 then ord x.2 y.2 else ord x.1 y.1.

Lemma irr_lex : irreflexive lex.
Proof. by move=>x; rewrite /lex eq_refl irr. Qed.

Lemma trans_lex : transitive lex.
Proof.
move=>[x1 x2][y1 y2][z1 z2]; rewrite /lex /=.
case: ifP=>H1; first by rewrite (eqP H1); case: eqP=>// _; apply: trans.
case: ifP=>H2; first by rewrite (eqP H2) in H1 *; rewrite H1.
case: ifP=>H3; last by apply: trans.
by rewrite (eqP H3)=>R1; move/(nsym R1).
Qed.

Lemma semiconn_lex : forall x y, x != y -> lex x y || lex y x.
Proof.
move=>[x1 x2][y1 y2]; rewrite /lex /=.
by case: ifP=>H1 H2; rewrite eq_sym H1 semiconnex //; move: H2; rewrite -pair_eqE /= H1 //.
Qed.

Definition prod_ordMixin := OrdMixin irr_lex trans_lex semiconn_lex.
Canonical Structure prod_ordType := Eval hnf in OrdType (K * T) prod_ordMixin.
End ProdOrd.

Section FinTypeOrd.
Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T).

Lemma irr_ordf : irreflexive ordf.
Proof. by move=>x; rewrite /ordf ltnn. Qed.

Lemma trans_ordf : transitive ordf.
Proof. by move=>x y z; rewrite /ordf; apply: ltn_trans. Qed.

Lemma semiconn_ordf x y : x != y -> ordf x y || ordf y x.
Proof.
rewrite /ordf; case: ltngtP=>//= H.
have [H1 H2]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x H1) -(nth_index x H2) H eq_refl.
Qed.

Definition fin_ordMixin := OrdMixin irr_ordf trans_ordf semiconn_ordf.
End FinTypeOrd.

(* notation to let us write I_n instead of (ordinal_finType n) *)
Notation "[ 'fin_ordMixin' 'of' T ]" :=
  (fin_ordMixin _ : Ordered.mixin_of [eqType of T]) (at level 0).

Definition ordinal_ordMixin n := [fin_ordMixin of 'I_n].
Canonical Structure ordinal_ordType n := Eval hnf in OrdType 'I_n (ordinal_ordMixin n).

Section SeqOrd.
Variable (T : ordType).

Fixpoint ords x  : pred (seq T) :=
  fun y => match x , y with
                 | [::] , [::] => false
                 | [::] ,  t :: ts => true
                 | x :: xs , y :: ys => if x == y then ords xs ys
                                        else ord x y
                 | _ :: _ , [::] => false
             end.

Lemma irr_ords : irreflexive ords.
Proof. by elim=>//= a l ->; rewrite irr; case:eqP=> //=. Qed.

Lemma trans_ords : transitive ords.
Proof.
elim=>[|y ys IHy][|x xs][|z zs]//=.
case:eqP=>//[->|H0];case:eqP=>//H; first by move/IHy; apply.
- by case:eqP=>//; rewrite -H; first (by move/H0).
case:eqP=>//[->|H1] H2; first by move/(nsym H2).
by move/(trans H2).
Qed.

Lemma semiconn_ords : forall x y, x != y -> ords x y || ords y x.
Proof.
elim=>[|x xs IH][|y ys]//=.
case:ifP => H1 H2; rewrite eq_sym H1.
- by apply: IH; move: H2; rewrite -eqseqE /= H1 andTb.
by rewrite semiconnex // H1.
Qed.

Definition seq_ordMixin := OrdMixin irr_ords trans_ords semiconn_ords.
Canonical Structure seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.
End SeqOrd.

(* A trivial total ordering for Unit *)
Section unitOrd.
Let ordtt (x y : unit) := false.

Lemma irr_tt : irreflexive ordtt.
Proof. by []. Qed.

Lemma trans_tt : transitive ordtt.
Proof. by []. Qed.

Lemma semiconn_tt x y : x != y -> ordtt x y || ordtt y x.
Proof. by []. Qed.

Let unit_ordMixin := OrdMixin irr_tt trans_tt semiconn_tt.
Canonical Structure unit_ordType := Eval hnf in OrdType unit unit_ordMixin.
End unitOrd.


(* ordering with path, seq and last *)

Lemma eq_last (A : eqType) (s : seq A) x y :
        x \in s -> last y s = last x s.
Proof. by elim: s x y=>[|w s IH]. Qed.

Lemma seq_last_in (A : eqType) (s : seq A) x :
        last x s \notin s -> s = [::].
Proof.
case: (lastP s)=>{s} // s y; case: negP=>//; elim; rewrite last_rcons.
by elim: s=>[|y' s IH]; rewrite /= inE // IH orbT.
Qed.

Lemma path_last (A : eqType) (s : seq A) leT x :
        transitive leT -> path leT x s ->
        (x == last x s) || leT x (last x s).
Proof.
move=>T /(order_path_min T) /allP; case: s=>[|a s] H /=.
- by rewrite eq_refl.
by rewrite (H (last a s)) ?orbT // mem_last.
Qed.

Lemma path_lastR (A : eqType) (s : seq A) leT x :
        reflexive leT -> transitive leT ->
        path leT x s -> leT x (last x s).
Proof. by move=>R T P; case: eqP (path_last T P)=>// <- _; apply: R. Qed.

(* in a sorted list, the last element is maximal *)
(* and the maximal element is last *)

Lemma sorted_last_key_max (A : eqType) (s : seq A) leT x y :
        transitive leT -> sorted leT s -> x \in s ->
        (x == last y s) || leT x (last y s).
Proof.
move=>T; elim: s x y=>[|z s IH] //= x y H; rewrite inE.
case: eqP=>[->|] /= _; first by apply: path_last.
by apply: IH (path_sorted H).
Qed.

Lemma sorted_last_key_maxR (A : eqType) (s : seq A) leT x y :
        reflexive leT -> transitive leT ->
        sorted leT s -> x \in s -> leT x (last y s).
Proof.
move=>R T S X; case/orP: (sorted_last_key_max y T S X)=>// /eqP <-.
by apply: R.
Qed.

Lemma sorted_max_key_last (A : eqType) (s : seq A) leT x y :
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

Lemma max_key_last_notin (A : eqType) (s : seq A) (leT : rel A) x y :
        leT y x -> (forall z, z \in s -> leT z x) -> leT (last y s) x.
Proof.
elim: s x y=>[|w s IH] //= x y H1 H2; apply: IH.
- by apply: (H2 w); rewrite inE eq_refl.
by move=>z D; apply: H2; rewrite inE D orbT.
Qed.

Lemma seq_last_mono (A : eqType) (s1 s2 : seq A) leT x :
        transitive leT -> path leT x s1 -> path leT x s2 ->
        {subset s1 <= s2} ->
        (last x s1 == last x s2) || leT (last x s1) (last x s2).
Proof.
move=>T; case: s1=>/= [_ H1 _|a s]; first by apply: path_last H1.
case/andP=>H1 H2 H3 H; apply: sorted_last_key_max (path_sorted H3) _=>//.
apply: {x s2 H1 H3} H; rewrite inE orbC -implyNb.
by case E: (_ \notin _) (@seq_last_in _ s a)=>//= ->.
Qed.

Lemma seq_last_monoR (A : eqType) (s1 s2 : seq A) leT x :
        reflexive leT -> transitive leT ->
        path leT x s1 -> path leT x s2 ->
        {subset s1 <= s2} ->
        leT (last x s1) (last x s2).
Proof. by move=>R T P1 P2 S; case: eqP (seq_last_mono T P1 P2 S)=>[->|]. Qed.

Lemma ord_path (A : eqType) (s : seq A) leT (x y : A) :
        transitive leT ->
        leT x y -> path leT y s -> path leT x s.
Proof.
move=>T; elim: s x y=>[|k s IH] x y //= H1 /andP [H2 ->].
by rewrite (T _ _ _ H1 H2).
Qed.

Lemma path_mem (A : eqType) (s : seq A) leT x y :
        transitive leT ->
        path leT x s -> y \in s -> leT x y.
Proof.
move=>T; elim: s x=>[|z s IH] x //= /andP [O P].
rewrite inE; case/orP=>[/eqP -> //|].
by apply: IH; apply: ord_path O P.
Qed.

Lemma sorted_rcons (A : eqType) (s : seq A) leT (y : A) :
        sorted leT s -> (forall x, x \in s -> leT x y) ->
        sorted leT (rcons s y).
Proof.
elim: s=>[|a s IH] //= P H; rewrite rcons_path P /=.
by apply: H (mem_last _ _).
Qed.

Lemma sorted_subset_subseq (A : eqType) (s1 s2 : seq A) leT :
        irreflexive leT -> transitive leT ->
        sorted leT s1 -> sorted leT s2 ->
        {subset s1 <= s2} -> subseq s1 s2.
Proof.
move=>R T S1 S2 H.
suff -> : s1 = filter (fun x => x \in s1) s2 by apply: filter_subseq.
apply: irr_sorted_eq S1 _ _=>//; first by rewrite sorted_filter.
by move=>k; rewrite mem_filter; case S : (_ \in _)=>//; rewrite (H _ S).
Qed.

Lemma sorted_ord_index (A : eqType) (s : seq A) leT x y :
        irreflexive leT -> transitive leT ->
        sorted leT s -> x \in s -> leT x y -> index x s < index y s.
Proof.
move=>I T S P H; elim: s S P=>[|z s IH] //= P; rewrite !inE !(eq_sym z).
case: eqP H P=>[<-{z} H P _|_ H P /= X]; first by case: eqP H=>[<-|] //; rewrite I.
case: eqP H P=>[<-{z} H|_ H]; last first.
- by move/path_sorted=>S; rewrite ltnS; apply: IH.
by move/(path_mem T)/(_ X)=>/(T _ _ _ H); rewrite I.
Qed.

Lemma sorted_index_ord (A : eqType) (s : seq A) leT x y :
        irreflexive leT -> transitive leT ->
        sorted leT s -> y \in s -> index x s < index y s -> leT x y.
Proof.
move=>I T; elim: s=>[|z s IH] //= P; rewrite !inE !(eq_sym z).
case: eqP=>//= /eqP N; case: eqP P=>[-> P /(path_mem T P)|_ P] //.
by rewrite ltnS; apply: IH; apply: path_sorted P.
Qed.

Lemma nth_cons A (a x : A) (s : seq A) (n : nat) :
        nth a (x :: s) n = if n == 0 then x else nth a s n.-1.
Proof. by case: n. Qed.

Lemma nth_base A (s : seq A) k1 k2 i :
        i < size s -> nth k1 s i = nth k2 s i.
Proof.
elim: s i=>[|x xs IH] //= i K; rewrite !nth_cons.
by case: eqP=>//; case: i K=>// i; rewrite ltnS=>/IH ->.
Qed.

Lemma nth_path_head (A : eqType) (s : seq A) leT x0 k i :
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
        i < size s -> path leT k s ->
        leT (nth x0 (k::s) i) (nth x0 s i).
Proof.
elim: i k s=>[|i IH] k s; first by case: s=>[|x xs] //= _ /andP [].
by case: s IH=>[|x xs] //= IH N /andP [P1 P2]; apply: IH.
Qed.

Lemma nth_ltn_mono A (s : seq A) leT x0 k i j :
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

Lemma nth_mono_ltn A (s : seq A) leT x0 k i j :
         irreflexive leT ->
         transitive leT ->
         i <= size s -> j <= size s ->
         path leT k s ->
         leT (nth x0 (k::s) i) (nth x0 (k::s) j) -> i < j.
Proof.
move=>I T S1 S2 P; case: ltngtP=>//; last by move=>->; rewrite I.
by move/(nth_ltn_mono x0 T S2 S1 P)/T=>X /X; rewrite I.
Qed.

Lemma nth_between (A : eqType) (s : seq A) leT x0 k z i :
        irreflexive leT ->
        transitive leT ->
        path leT k s ->
        leT (nth x0 (k::s) i) z -> leT z (nth x0 s i) -> z \notin s.
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

#[deprecated(since="fcsl-pcm 1.4.0", note="Use ord_sorted_eq instead.")]
Notation eq_sorted_ord := ord_sorted_eq (only parsing).
