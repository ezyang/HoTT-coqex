Require Import HoTT.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* Exercise 2.1 *)

Lemma translr {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction p. induction q. reflexivity.
Defined.

Lemma transl {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction p. apply q.
Defined.

Lemma transr {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction q. apply p.
Defined.

Lemma eq_lr_l {A : Type} {x y z : A} (p : x = y) (q : y = z) : translr p q = transl p q.
  induction p. induction q. reflexivity.
Defined.

Lemma eq_l_r {A : Type} {x y z : A} (p : x = y) (q : y = z) : transl p q = transr p q.
  induction p. induction q. reflexivity.
Defined.

(* Cleverly need to swap these arguments >:-) Otherwise, running sym on
the correctly oriented version would also work.  *)
Lemma eq_lr_r {A : Type} {x y z : A} (p : x = y) (q : y = z) : translr p q = transr p q.
  induction q. induction p. reflexivity.
Defined.


(* in all the proofs, we need to do induction on both equalities, because
we need to compute to refl = refl. *)

(* Exercise 2.2 *)
Lemma eq_triangle {A : Type} {x y z : A} (p : x = y) (q : y = z) : eq_lr_l p q @ eq_l_r p q = eq_lr_r p q.
  induction p. induction q. reflexivity.
Qed.

(* Exercise 2.3 *)
(* It's not obvious that there /is/ another proof, but there is, which
works off of a variant of the Yoneda lemma. An alternative way of looking
at it is we are strengthening the inductive hypothesis. *)
Lemma transy {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  generalize q; clear q.
  generalize z; clear z.
  induction p. trivial.
Defined.

Print transy.
(*
transy = 
fun (A : Type) (x y z : A) (p : x = y) (q : y = z) =>
paths_rect x (fun (y0 : A) (_ : x = y0) => forall z0 : A, y0 = z0 -> x = z0)
  (fun z0 : A => idmap) y p z q
     : forall (A : Type) (x y z : A), x = y -> y = z -> x = z
*)
Print transl.
(*
transl = 
fun (A : Type) (x y z : A) (p : x = y) (q : y = z) =>
paths_rect x (fun (y0 : A) (_ : x = y0) => y0 = z -> x = z) idmap y p q
     : forall (A : Type) (x y z : A), x = y -> y = z -> x = z
*)

Lemma eq_y_l {A : Type} {x y z : A} (p : x = y) (q : y = z) : transy p q = transl p q.
  induction p. reflexivity.
Qed.

(* Exercise 2.4 *)

(*
0-path is a point
1-path is a path (the boundary is the two endpoints)
2-path is a homotopy of paths (the boundary is the two endpaths)
*)

(* The key insight is that the 'type' of a n-dimensional path contains
a sigma in it.  You rarely see sigma when we talk about the 'type' of paths
because we will usually have some endpoints in the context.  If you remove
the context, you need to somehow provide the context.  Who provides the
context?  If it's considered part of the path itself, the context needs to
be baked in with the path; since it's part of the type it is in a sigma. *)

(*
A 0-path in A is a point in A.
A 1-path is (x, y, p) with x y : A,     p : x = y
A 2-path is (p, q, r) with p q : x = y, r : p = q
*)

Fixpoint npath (A : Type) (n : nat) :=
  match n with
      | 0 => A
      | S n' => { x : npath A n' & { y : npath A n' & x = y } }
  end.
Eval compute in (npath nat 2).

(* This is equivalent to what you need, but it's worth convincing yourself that
this is in fact that the equalities all work out.
 {x : nat & x' : nat & y : nat & y' : nat & p : x = y & q : x' = y' & ex : x = x' & ey : y = y' & p = transport2 ex ey q } *)

(* Exercise 2.5 *)
Definition eq2_3_6 {A B x y} (f : A -> B) (p : x = y) : f x = f y -> transport (fun _ => B) p (f x) = f y :=
  fun q => transport_const _ _ @ q.
Definition eq2_3_7 {A B x y} (f : A -> B) (p : x = y) : transport (fun _ => B) p (f x) = f y -> f x = f y :=
  fun q => (transport_const _ _)^ @ q. (* careful with associativity precedence *)

(* I don't know what an "inverse equivalence" is, but it seems like these ought to form an equivalence *)

Definition ex2_5_beta {A B x y} (f : A -> B) (p : x = y) (fp : f x = f y) : eq2_3_7 f p (eq2_3_6 f p fp) = idmap fp.
  unfold eq2_3_6, eq2_3_7.
  path_induction; reflexivity.
Defined.

Definition ex2_5_alpha {A B x y} (f : A -> B) (p : x = y) (fp : transport (fun _ => B) p (f x) = f y) : eq2_3_6 f p (eq2_3_7 f p fp) = idmap fp.
  unfold eq2_3_6, eq2_3_7.
  path_induction; reflexivity.
Defined.

(* Because this chapter does not contain a discussion of the "adjointification" of equivalences
(and all of the proofs simply assume a black box way to get there), we don't worry about it either.) *)
Lemma ex2_5 {A B x y} (f : A -> B) (p : x = y) : IsEquiv (eq2_3_6 f p).
  apply (isequiv_adjointify _ (eq2_3_7 f p) (ex2_5_alpha f p) (ex2_5_beta f p)).
Qed.

(* In some cases, however, the adjointification condition is pretty easy to do. *)
Lemma ex2_5' {A B x y} (f : A -> B) (p : x = y) : IsEquiv (eq2_3_6 f p).
  refine (BuildIsEquiv _ _ _ (eq2_3_7 f p) (ex2_5_alpha f p) (ex2_5_beta f p) _).
  intros; unfold ex2_5_alpha, ex2_5_beta, eq2_3_6, eq2_3_7; path_induction; reflexivity.
Defined.

(* Exercise 2.6 *)

Definition invconcat {A} {x y z : A} (p : x = y) : x = z -> y = z.
  path_induction; reflexivity.
Defined.

Definition concat_alpha {A} {x y z : A} (p : x = y) (q : x = z) : @concat A x y z p (@invconcat A x y z p q) = idmap q.
  path_induction; reflexivity.
Defined.

Definition concat_beta {A} {x y z : A} (p : x = y) (q : y = z) : @invconcat A x y z p (@concat A x y z p q) = idmap q.
  path_induction; reflexivity.
Defined.

Lemma ex2_6 {A} {x y z : A} (p : x = y) : IsEquiv (@concat A x y z p).
  apply (isequiv_adjointify _ (@invconcat A x y z p) (concat_alpha p) (concat_beta p)).
Defined.

Lemma ex2_6' {A} {x y z : A} (p : x = y) : IsEquiv (@concat A x y z p).
  refine (BuildIsEquiv _ _ _ (@invconcat A x y z p) (concat_alpha p) (concat_beta p) _).
  intros; unfold invconcat, concat_alpha, concat_beta, concat; path_induction; reflexivity.
Defined.

(* Exercise 2.7 *)

(* pair^= is path_prod.  It's important to give the second path_prod the
arguments to help Coq figure out the definitional equality.
This lemmma is called ap_functor_prod in the standard library, and f is
defined as functor_prod *)
(* NB: defining f using fst/snd and not a match is fairly essential to
   convincing Coq that things are definitionally equal in the way necessa *)
Theorem theorem2_6_5 {A B A' B'} (g : A -> A') (h : B -> B') (x y : A * B) (p : fst x = fst y) (q : snd x = snd y) :
  let f z := (g (fst z), h (snd z)) in
    ap f (path_prod x y p q) = path_prod (f x) (f y) (ap g p) (ap h q).
  intros. destruct x; destruct y; simpl in *. path_induction; reflexivity.
Qed.
Print ap_functor_prod.

(* The key to writing down the generalized version of this theorem relies
on the three useful lemmas 2.3.{9-11}.  They're available in the HoTT library
but it is instructive to state and prove them here. *)

Lemma lemma2_3_9 {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  transport _ q (transport _ p u) = transport _ (p @ q) u.
  path_induction; reflexivity.
Defined.
Print transport_pp. (* Actually, you don't need this one. Yet. *)

Lemma lemma2_3_10 {A B : Type} (f : A -> B) (P : B -> Type) {x y : A} (p : x = y) (u : P (f x)) :
  transport (P o f) p u = transport P (ap f p) u.
  path_induction; reflexivity.
Defined.
Print transport_compose.

Lemma lemma2_3_11 {A : Type} (P Q : A -> Type) (f : forall x : A, P x -> Q x) {x y : A} (p : x = y) (u : P x) :
  transport Q p (f x u) = f y (transport P p u).
  path_induction; reflexivity.
Defined.
Print ap_transport. (* It's not entirely clear why it's called 'ap' transport, since no ap is involved. *)

(* A useful trick which jgross showed me: if you are not sure how a theorem should
be stated, replace it with a : Type, and fill it out using tactic mode.  This is actually
one of those cases where Agda would be superior to Coq for doing these types of proofs,
since holes are natively supported in goals, whereas we have to do some acrobatics. *)

Theorem ex2_7' {A A'} {P : A -> Type} {P' : A' -> Type} (g : A -> A') (h : forall a, P a -> P' (g a)) (x y : sigT P) (p : x.1 = y.1) (q : transport _ p x.2 = y.2) : Type.
  refine (let f z := (g z.1 ; h z.1 z.2) in
    ap f (path_sigma P x y p q) = path_sigma P' (f x) (f y) (ap g p) _).
  subst f; simpl.
  transitivity (transport (P' o g) p (h x .1 x .2)).
  symmetry. apply (lemma2_3_10 g P' _ _).
  transitivity (h y .1 (transport P p x .2)). 
  apply (lemma2_3_11 P (P' o g) _ _ _).
  apply ap.
  exact q.
Defined.

(* Unfortunately, Coq has expanded some of the lemmas into matches on identity,
so we will have to reverse engineer the true theorem in one go. *)
Print ex2_7'.

Theorem ex2_7 {A A'} {P : A -> Type} {P' : A' -> Type} (g : A -> A') (h : forall a, P a -> P' (g a)) (x y : sigT P) (p : x.1 = y.1) (q : transport _ p x.2 = y.2) :
  let f z := (g z.1 ; h z.1 z.2) in
    ap f (path_sigma P x y p q) =
       path_sigma P' (f x) (f y) (ap g p) (concat (inverse (lemma2_3_10 g P' _ _))
                                                  (concat (lemma2_3_11 P (P' o g) _ _ _) (ap _ q))).
  intros; subst f. destruct x; destruct y; simpl in *; unfold lemma2_3_10, lemma2_3_11.
  path_induction; reflexivity.
Qed.

(* This is stated and proved in the library proper in slightly different form *)
Print ap_functor_sigma.

(* Exercise 2.8 *)

(* Reader is also encouraged to check out commentary here, by Bob Harper:
https://www.dropbox.com/sh/jwtpx1rzal7um28/sOgTLhW1Zu/cancellation.pdf  *)

(* coproducts aka sums *)
Require Import Sum.

(* We first reproduce the left-code and the right-code which is presented in
Section 2.12 of the HoTT book, as well as the appropriate equivalences. *)

Definition lcode {A B} (a0 : A) (x : A + B) :=
  match x return Type with inl a => a0 = a | inr b => Empty end.
Definition lencode {A B} {a0 : A} {x : A + B} (p : inl a0 = x) : lcode a0 x :=
  transport (lcode a0) p 1.
Definition ldecode {A B} {a0 : A} {x : A + B} (c : lcode a0 x) : inl a0 = x.
  destruct x. exact (ap inl c). destruct c.
Defined.
(* Done with tactics to automatically push the lambda abstraction inside the
case on x and avoid writing all of the annotations for dependent match. *)
Print ldecode.
Lemma thm2_12_15_alpha {A B} {a0 : A} {x : A + B} (c : lcode a0 x) : (lencode (ldecode c)) = c.
  destruct x; destruct c; reflexivity.
Qed.
Lemma thm2_12_15_beta {A B} {a0 : A} {x : A + B} (p : inl a0 = x) : (ldecode (lencode p)) = p.
  path_induction; reflexivity.
Qed.
Theorem thm2_12_15 {A B} (a0 : A) (x : A + B) : IsEquiv (@lencode A B a0 x).
  apply (isequiv_adjointify _ ldecode thm2_12_15_alpha thm2_12_15_beta ).
Qed.

Definition rcode {A B} (b0 : B) (x : A + B) := match x return Type with inl a => Empty | inr b => b0 = b end.
Definition rencode {A B} {b0 : B} {x : A + B} (p : inr b0 = x) : rcode b0 x := transport (rcode b0) p 1.
Definition rdecode {A B} {b0 : B} {x : A + B} (c : rcode b0 x) : inr b0 = x.
  destruct x. destruct c. f_ap.
Defined.
Lemma thm2_12_15'_alpha {A B} {b0 : B} {x : A + B} (c : rcode b0 x) : (rencode (rdecode c)) = c.
  destruct x; destruct c. reflexivity.
Qed.
Lemma thm2_12_15'_beta {A B} {b0 : B} {x : A + B} (p : inr b0 = x) : (rdecode (rencode p)) = p.
  path_induction. reflexivity.
Qed.
Theorem thm2_12_15' {A B} (b0 : B) (x : A + B) : IsEquiv (@rencode A B b0 x).
  apply (isequiv_adjointify _ rdecode thm2_12_15'_alpha thm2_12_15'_beta ).
Qed.

(* To a new reader, it probably will not be obvious what the codes are for.
The hardest part of this question is knowing how to /state/ the functoriality
property at all.

Referring back to the question statement, we've been asked to state and
prove a corresponding theorem to the functoriality of ap on products.
We can go ahead and attempt to translate the theorem into the language
of coproducts, but the first question one has to answer here is, what corresponds
pair^= here?  We have been instructed that pair^= is the "introduction rule"
for equality on products; we are looking for a similar introduction rule for
equality on sums.  But where it was simply enough to provide two equalities
in the case of product (a negative type former), which equality we provide
for a sum type depends on the tags of the values. (a positive type variable)
So what this "equality" is, is in fact the *code* for equality over coproducts.

While we may not have a good idea what the type of this introduction rule
is, we might know what it is named.  Fortunately, the standard library
already provides us the introduction rule for coproducts; and we can see what
the *code* is (the lhs of the arrow): *)

Check path_sum.

(* In the HoTT library, the matches for the codes for coproducts are all explicitly
written out.  However, it will simplify our work if we wrap them up in a definition,
which we will call 'code'. I take advantage of the previous left-code and right-code
definitions, but there's not any specific reason why they have to be used.  When
Harper gives a presentation of this material, he simply states that these are
defined by double case-match. *)

Definition code {A B} (x0 : A + B) (x : A + B) :=
  match x0 with
      inl a0 => lcode a0 x
    | inr b0 => rcode b0 x
  end.

(* For completeness, though, here is the expanded version: *)
Definition code' {A B} (x0 : A + B) (x : A + B) :=
  match x0 with
      inl a0 => match x with
                    inl a => a0 = a
                  | inr b => Empty
                end
    | inr b0 => match x with
                    inl a => Empty
                  | inr b => b0 = b
                end
  end.
(* Sanity check that these are definitionally equal: *)
Lemma code_code' {A B} (x0 : A + B) (x : A + B) : code x0 x = code' x0 x. reflexivity. Qed.

Definition encode {A B} {x0 x : A + B} (p : x0 = x) : code x0 x.
  destruct x0; [ exact (lencode p) | exact (rencode p) ].
Defined.
Definition decode {A B} {x0 x : A + B} (c : code x0 x) : x0 = x.
  destruct x0; [ exact (ldecode c) | exact (rdecode c) ].
Defined.
Lemma encode_eq_alpha {A B} {x0 : A + B} {x : A + B} (c : code x0 x) : encode (decode c) = c.
  destruct x0. apply thm2_12_15_alpha. apply thm2_12_15'_alpha.
Defined.
Lemma encode_eq_beta {A B} {x0 : A + B} {x : A + B} (p : x0 = x) : decode (encode p) = p.
  path_induction; destruct x0; reflexivity.
Qed.
Theorem encode_eq {A B} (x0 : A + B) (x : A + B) : IsEquiv (@encode A B x0 x).
  apply (isequiv_adjointify _ decode encode_eq_alpha encode_eq_beta ).
Qed.

(* The statement of functoriality ap, then, says what the action of ap
is on elements of the /code/. (In the case of products, that was just the pair of equalities.) *)

Theorem ex2_8 {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B) (pq : code x y) :
  let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in
  ap f (path_sum x y pq) = path_sum (f x) (f y)
     ((match x return code x y -> code (f x) (f y) with
          inl a0 => match y return lcode a0 y -> lcode (g a0) (f y) with
                        inl a => ap g
                      | inr b => fun p => p
                    end
        | inr b0 => match y return rcode b0 y -> rcode (h b0) (f y) with
                        inl a => fun p => p
                      | inr b => ap h
                    end
      end) pq).
  destruct x; destruct y; unfold code, lcode, rcode in *;
  try solve [destruct pq]; path_induction; reflexivity.
Qed.

(* Harper describes a rather interesting alternate method for proving functoriality, which
I tried developing here, but gave up midway.
Definition apf_inv {A B} (f : A -> B) {eq : IsEquiv f} {a a' : A} : f a = f a' -> a = a' :=
  fun q => ((eissect f a) ^ @ ap (f ^-1)%equiv q @ (eissect f a'))%path.
Definition apf_alpha {A B} {f : A -> B} {eq : IsEquiv f} {a a' : A} (p : a = a') : apf_inv f (ap f p) = p.
  path_induction. unfold apf_inv; simpl.
  refine (concat (ap (fun p => (p @ eissect f a)%path) (concat_p1 _)) _).
  apply concat_Vp.
Defined.
Definition apf_beta {A B} {f : A -> B} {eq : IsEquiv f} {a a' : A} (q : f a = f a') : ap f (apf_inv f q) = q.
  (* Notice path_induction doesn't do anything *)
  (* Discover the correct path *)
  unfold apf_inv.
  refine ((concat_p1 _) ^ @ _)%path.
  assert (p : a = a').
    refine ((eissect f a) ^ @ _)%path.
    refine ((ap (f ^-1)%equiv q) @ _)%path.
    exact ((eissect f a')).
  unfold apf_inv.
  path_induction.
  

Theorem apf_eq {A B} {f : A -> B} {eq : IsEquiv f} {x y : A}: IsEquiv (@ap _ _ f x y).
  *)
(* Exercise 2.9 *)

Definition sum_universal_iso {A B X : Type} (f : A + B -> X) : (A -> X) * (B -> X) := (fun a => f (inl a), fun b => f (inr b)).
Definition sum_universal_osi {A B X : Type} (hg : (A -> X) * (B -> X)) : A + B -> X := let (g, h) := hg in fun x => match x with inl a => g a | inr b => h b end.
Definition sum_universal_alpha {A B X : Type} `{Funext} (f : A + B -> X) : sum_universal_osi (sum_universal_iso f) = f.
  unfold sum_universal_iso, sum_universal_osi. apply H; intro x. destruct x; reflexivity.
Defined.
Definition sum_universal_beta {A B X : Type} (hg : (A -> X) * (B -> X)) : sum_universal_iso (sum_universal_osi hg) = hg.
  unfold sum_universal_iso, sum_universal_osi. destruct hg; reflexivity.
Defined.

Definition sum_universal {A B X : Type} `{Funext} : (A -> X) * (B -> X) <~> (A + B -> X).
  apply (equiv_adjointify sum_universal_osi sum_universal_iso sum_universal_alpha sum_universal_beta).
Defined.

(* Presence of function extensionality makes doing the adjointified version annoying. *)

(* Exercise 2.10 *)

Definition sigma_assoc_iso {A} {B : A -> Type} (C : sigT (fun x : A => B x) -> Type) (p : sigT (fun x : A => sigT (fun y : B x => C (x; y)))) : (sigT (fun (p : sigT (fun x : A => B x)) => C p)) := ((p.1; p.2.1); p.2.2).

Definition sigma_assoc_osi {A} {B : A -> Type} (C : sigT (fun x : A => B x) -> Type) (p : sigT (fun (p : sigT (fun x : A => B x)) => C p)) : (sigT (fun x : A => sigT (fun y : B x => C (x; y)))).
  destruct p. destruct x. refine (x; _). refine (b; _). exact c.
Defined.
(* Looking at the dependent pattern match is instructive, and shows the classic
trick for refining the type of c. But I'm a lazy bastard, and the match is about
what I want. *)
Print sigma_assoc_osi.

Ltac simplHyp :=
  match goal with
      | [ H : _ * _ |- _ ] => destruct H
      | [ H : sigT _ |- _ ] => destruct H
  end.

Ltac crush := simpl in *; repeat simplHyp; try trivial; try solve [f_ap].

Definition sigma_assoc {A} {B : A -> Type} (C : sigT (fun x : A => B x) -> Type) :
  sigT (fun x : A => sigT (fun y : B x => C (x; y))) <~> sigT (fun (p : sigT (fun x : A => B x)) => C p).
  refine (equiv_adjointify (@sigma_assoc_iso A B C) (@sigma_assoc_osi A B C) _ _);
  intro; unfold sigma_assoc_osi, sigma_assoc_iso; crush.
Qed.
 
(* Exercise 2.11 *)

(* To show that something is the corner of a pullback square, we just need to
show the desired equivalence. *)

Require Import ObjectClassifier.
Print pullback.

Definition pullback1 {A B C} (f : A -> C) (g : B -> C) (p : pullback f g) : A := p.1.
Definition pullback2 {A B C} (f : A -> C) (g : B -> C) (p : pullback f g) : B := p.2.1.

(* Stating the definitions of pullf and pullf_inv using apD10 is *critical*;
 we will be doing reasoning with the fact that apD10 is an equivalence, and
 if some of the parts of the definition are unfolded it will greatly obscure
 what is going on. *)
Definition pullf {A B C} X `{Funext} (f : A -> C) (g : B -> C) (h : X -> pullback f g) : pullback (@compose X _ _ f) (@compose X _ _ g).
  refine (pullback1 f g o h; _).
  refine (pullback2 f g o h; _).
  apply path_forall; intro.
  exact (h x).2.2.
Defined.
Definition pullf_inv {A B C} X (f : A -> C) (g : B -> C) (z : pullback (@compose X _ _ f) (@compose X _ _ g)) (x : X) : pullback f g.
  refine (z.1 x; (z.2.1 x; _)).
  exact (apD10 z.2.2 x).
Defined.

Theorem ex2_11 `{Funext} {A B C X} {f : A -> C} {g : B -> C} : IsEquiv (pullf X f g).
  refine (isequiv_adjointify _ (pullf_inv X f g) _ _).

  unfold Sect, pullf_inv, pullf, path_forall; simpl. destruct 0 as [f' [g' p]]; simpl. f_ap. f_ap.
  apply ((ap apD10)^-1)%equiv.
  apply (eisretr apD10).

  unfold Sect, pullf_inv, pullf, path_forall; intro h; simpl.
  apply path_forall; intro x.
  repeat (apply path_sigma_uncurried; exists idpath; simpl).
  change (h x).2.2 with ((fun x' => (h x').2.2) x); f_ap. (* because higher-order unification is undecidable *)
  apply eisretr.
Qed.

(* Exercise 2.12 *)

(* In the previous exercise we specialized (since h = .1 and k = .2.1), but for this exercise P is
generic so it will be good to properly define pullback squares and the induced map in full
generality. *)

(* P.S. I tried an alternate formulation where squares were defined specifically as pullbacks.
But this is a little annoying when you have two squares joined together, because you have
to explicitly state that two edges of the square are equal. So I decided to go back to the
more straightforward version. *)

(* It's important to specify the input type of compose, since the inferencer gets
confused otherwise. *)

(* P -> A
   ↓    ↓
   B -> C *)
Definition induced_map `{Funext} {P A B C} (f : A -> C) (g : B -> C) (h : P -> A) (k : P -> B) (p : f o h = g o k) X (i : X -> P) : pullback (@compose X _ _ f) (@compose X _ _ g).
  refine (h o i; (k o i; _)).
  change (f o h o i = g o k o i).
  refine (apD10 _ i).
  exact (ap compose p).
Defined.

(* BTW, why couldn't pullf be defined in the same, graceful manner?  Well,
the trouble is while the p here is explicitly provided, in the pullback case
we got it out of the fact that pullbacks come with equality proofs.  We could
have factored this out, so that the call-site of pullf was responsible
for the extraction, but doing it the other way seemed more natural. It's a
sleight of hand that reduces the arguments you need to pass around. (In
a sense, we embedded the proof that it is a commutative square). *)

Definition pullback_square `{Funext} {P A B C}
                           (f : A -> C) (g : B -> C) (h : P -> A) (k : P -> B)
                           (p : f o h = g o k) := 
  forall X, IsEquiv (induced_map f g h k p X).

(* The squares reproduced for your convenience:
  A -> C -> E
  ↓ p  ↓ q  ↓
  B -> D -> F 
    \--r--/  *)

(* XXX I don't actually know if this is called whiskering *)
Definition whisker
          {A B C D E F} 
          {ac : A -> C}
          {ab : A -> B}
          {cd : C -> D}
          {bd : B -> D}
          {ce : C -> E}
          {ef : E -> F}
          {df : D -> F}
          (p : cd o ac = bd o ab)
          (q : ef o ce = df o cd)
  : ef o ce o ac = df o bd o ab.
transitivity (df o cd o ac); [f_ap|].
change (df o (cd o ac) = df o (bd o ab)); f_ap.
Defined.

(* the hard one *)
Definition induced_map_inv1
          `{Funext}
          {A B C D E F X}
          (ac : A -> C)
          (ab : A -> B)
          (cd : C -> D)
          (bd : B -> D)
          (ce : C -> E)
          (ef : E -> F)
          (df : D -> F)
          (p : cd o ac = bd o ab)
          (q : ef o ce = df o cd)
          (P : pullback_square ef df ce cd q)
          (S : pullback_square cd bd ac ab p)
          (z : pullback (@compose X _ _ ef) (@compose X _ _ (df o bd)))
          : X -> A.
let r := constr:((z.1; (bd o z.2.1; z.2.2)) : pullback (@compose X _ _ ef) (@compose X _ _ df)) in pose r as z'.
let r := constr:(@equiv_inv _ _ _ (P X) z') in pose r as xc.
let r := constr:(induced_map ef df ce cd q X xc) in pose r as z''.
let r := constr:(@eisretr _ _ _ (P X) _ : z'' = z') in pose r as alpha. (* crucial! *)
apply (S X).
refine (xc ; (z.2.1 ; _)).
  etransitivity; [| apply (alpha..2..1)]. (* ho ho, use the retraction! *)
  destruct (alpha ..1). (* get rid of pesky transport *) reflexivity.
Defined.
Print induced_map_inv1.
Definition induced_map_inv2
          `{Funext}
          {A B C D E F X}
          (ac : A -> C)
          (ab : A -> B)
          (cd : C -> D)
          (bd : B -> D)
          (ce : C -> E)
          (ef : E -> F)
          (df : D -> F)
          (p : cd o ac = bd o ab)
          (q : ef o ce = df o cd)
          (P : pullback_square ef df ce cd q)
          (S : pullback_square ef (df o bd) (ce o ac) ab (whisker p q))
          (z : pullback (@compose X _ _ cd) (@compose X _ _ bd))
          : X -> A.
apply (S X).
refine (ce o z.1 ; (z.2.1 ; _)).
destruct z as [xc [xb r]]; simpl.
transitivity (df o cd o xc). change (ef o ce o xc = df o cd o xc); f_ap.
change (df o (cd o xc) = df o (bd o xb)); f_ap.
Defined.

Theorem ex2_12
          `{Funext}
          {A B C D E F}
          (ac : A -> C)
          (ab : A -> B)
          (cd : C -> D)
          (bd : B -> D)
          (ce : C -> E)
          (ef : E -> F)
          (df : D -> F)
          (p : cd o ac = bd o ab)
          (q : ef o ce = df o cd)
          (P : pullback_square ef df ce cd q)
  : (pullback_square cd bd ac ab p <-> pullback_square ef (df o bd) (ce o ac) ab (whisker p q)).
constructor; intro S; intro X.

refine (isequiv_adjointify _ (induced_map_inv1 ac ab cd bd ce ef df p q P S) _ _).
intro z.  destruct z as [x [y r]].
(* The proof here now acts a little differently than the other equivalence
proofs we have encountered.  The first instinct (especially given the other
equivalence proofs in this chapter) is to destruct the input as much as possible,
and then show that things simplify to the original.  However, this strategy
will not work here,   *)
admit.
intro z. unfold induced_map; simpl. unfold induced_map_inv1; simpl.
admit.

refine (isequiv_adjointify _ (induced_map_inv2 ac ab cd bd ce ef df p q P S) _ _).
intro z. unfold induced_map_inv2.
Abort.

(* Exercise 2.13 *)

(* Intuitively, the two inhabitants of Bool ~ Bool are id and neg. *)

Definition equiv_bool_id : Equiv Bool Bool.

Definition ex2_13_f (H : Equiv Bool Bool) : Bool.
  destruct H.
Abort.

Definition ex2_13_g : Bool -> Equiv Bool Bool.
  intro b; destruct b.
Abort.

Lemma ex2_13 : Equiv (Equiv Bool Bool) Bool.
Abort.