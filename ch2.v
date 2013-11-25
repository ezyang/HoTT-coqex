
Require Import HoTT.

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
Lemma eq_triangle {A : Type} {x y z : A} (p : x = y) (q : y = z) : (eq_lr_l p q @ eq_l_r p q)%path = eq_lr_r p q.
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
  fun q => (transport_const _ _ @ q)%path.
Definition eq2_3_7 {A B x y} (f : A -> B) (p : x = y) : transport (fun _ => B) p (f x) = f y -> f x = f y :=
  fun q => ((transport_const _ _) ^ @ q)%path. (* careful with associativity precedence *)

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

(* coproducts aka sums *)
Require Import Sum.

(* We first reproduce the left-code and the right-code which is presented in
Section 2.12 of the HoTT book, as well as the appropriate equivalences. *)

Definition lcode {A B} (a0 : A) (x : A + B) :=
  match x return Type with inl a => a0 = a | inr b => Empty end.
Definition lencode {A B} {a0 : A} {x : A + B} (p : inl a0 = x) : lcode a0 x :=
  transport (lcode a0) p idpath.
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
Definition rencode {A B} {b0 : B} {x : A + B} (p : inr b0 = x) : rcode b0 x := transport (rcode b0) p idpath.
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

(* The hardest part of this question is knowing how to /state/ the functoriality
property at all.

The first question one has to answer here is, what is the "equivalent"
of pair^= here?  We have been instructed that pair^= is the "introduction rule"
for equality on products; we are looking for a similar introduction rule for
equality on sums.  But where it was simply enough to provide two equalities
in the case of product (a negative type former), which equality we provide
for a sum type depends on the tags of the values. (a positive type variable)
So what this "equality" is, is in fact the *code* for equality over coproducts.

Fortunately, the standard library already provides us the introduction rule
for coproducts; and we can see what the *code* is (the lhs of the arrow): *)

Check path_sum.

(* In the HoTT library, the matches for the codes for coproducts are all explicitly
written out.  However, it will simplify our work if we wrap them up in a definition,
which we will call 'code'. I take advantage of the previous left-code and right-code
definitions, but there's not any specific reason why they have to be used. *)

Definition code {A B} (x0 : A + B) (x : A + B) :=
  match x0 return Type with inl a0 => lcode a0 x | inr b0 => rcode b0 x end.
Check @path_sum.
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

(* This code gave hoqtop a lot of headaches. I've submitted two bugs
to this effect:
https://github.com/HoTT/coq/issues/54
https://github.com/HoTT/coq/issues/55
 *)

Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => Empty
                 end)
: z = z'.
  destruct z, z', pq; exact idpath.
Defined.

(* Why are A B etc in Set and not Type?  Some sort of universe polymorphism bug... *)
Theorem ex2_8_raw {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B)
              (* Fortunately, this unifies properly *)
              (pq : match (x, y) with (inl x', inl y') => x' = y' | (inr x', inr y') => x' = y' | _ => Empty end) :
  let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in
  ap f (path_sum x y pq) = path_sum (f x) (f y)
     (* Coq appears to require *ALL* of the annotations *)
     ((match x as x return match (x, y) return Type with
              (inl x', inl y') => x' = y'
            | (inr x', inr y') => x' = y'
            | _ => Empty
          end -> match (f x, f y) return Type with
               | (inl x', inl y') => x' = y'
               | (inr x', inr y') => x' = y'
               | _ => Empty end with
           | inl x' => match y as y return match y return Type with
                                               inl y' => x' = y'
                                             | _ => Empty
                                           end -> match f y return Type with
                                                    | inl y' => g x' = y'
                                                    | _ => Empty end with
                         | inl y' => ap g
                         | inr y' => idmap
                       end
           | inr x' => match y as y return match y return Type with
                                               inr y' => x' = y'
                                             | _ => Empty
                                           end -> match f y return Type with
                                                    | inr y' => h x' = y'
                                                    | _ => Empty end with
                         | inl y' => idmap
                         | inr y' => ap h
                       end
       end) pq).
     (* TRULY! Dependent pattern matching is terrifying! And this is the "good" version...
     ((match (x, y) as (x, y) return
          match (x, y) with
              (inl x', inl y') => x' = y'
            | (inr x', inr y') => x' = y'
            | _ => Empty
          end
          -> match (f x, f y) with
               | (inl x', inl y') => x' = y'
               | (inr x', inr y') => x' = y'
               | _ => Empty end
       with
           (inl x', inl y') => fun p => ap g p
         | (inr x', inr y') => fun q => ap h q
         | _ => fun b => b
       end) pq). *)
  destruct x; destruct y;
  try solve [destruct pq]; path_induction; reflexivity.
Qed.



(* applying the jgross trick to figure out the type... *)
Lemma ex2_8_code_sub (A B A' B' : Type) (g : A -> A') (h : B -> B') (x y : A + B) (pq : code x y) : Type.
  refine (let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in _).
  refine (ap f (path_sum x y pq) = path_sum (f x) (f y) _).
  refine ((match x return code x y -> code (f x) (f y) with inl a0 => fun p =>  _ | inr b0 => fun p => _ end) pq).
  refine (lencode (ap f (ldecode p))).
  refine (rencode (ap f (rdecode p))).
Defined.

Theorem ex2_8_code {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B) (pq : code x y) :
  let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in
  ap f (path_sum x y pq) = path_sum (f x) (f y)
     ((match x return code x y -> code (f x) (f y) with
          inl a0 => fun p => lencode (ap f (ldecode p))
        | inr b0 => fun p => rencode (ap f (rdecode p))
      end) pq).
  destruct x; destruct y; unfold code, lcode, rcode in *;
  try solve [destruct pq]; path_induction; reflexivity.
Qed.

Theorem ex2_8_code' {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B) (pq : code x y) :
  let f z := match z with inl z' => inl (g z') | inr z' => inr (h z') end in
  ap f (path_sum x y pq) = path_sum (f x) (f y) (encode (ap f (decode pq))).
  destruct x; destruct y; unfold code, lcode, rcode, encode, decode in *;
  try solve [destruct pq]; path_induction; reflexivity.
Qed.

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

(* "Application to Paths" from Harper notes https://www.dropbox.com/sh/jwtpx1rzal7um28/sOgTLhW1Zu/cancellation.pdf *)



(* Exercise 2.9 *)

Definition sum_universal_iso {A B X : Type} (f : A + B -> X) : (A -> X) * (B -> X) := (fun a => f (inl a), fun b => f (inr b)).
Definition sum_universal_osi {A B X : Type} (hg : (A -> X) * (B -> X)) : A + B -> X := let (g, h) := hg in fun x => match x with inl a => g a | inr b => h b end.
Definition sum_universal_alpha {A B X : Type} `{Funext} (f : A + B -> X) : sum_universal_osi (sum_universal_iso f) = f.
  unfold sum_universal_iso, sum_universal_osi. apply H; intro x. destruct x; reflexivity.
Defined.
Definition sum_universal_beta {A B X : Type} (hg : (A -> X) * (B -> X)) : sum_universal_iso (sum_universal_osi hg) = hg.
  unfold sum_universal_iso, sum_universal_osi. destruct hg; reflexivity.
Defined.

Definition sum_universal {A B X : Type} `{Funext} : Equiv ((A -> X) * (B -> X)) (A + B -> X).
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
  Equiv (sigT (fun x : A => sigT (fun y : B x => C (x; y)))) (sigT (fun (p : sigT (fun x : A => B x)) => C p)).
  refine (equiv_adjointify (@sigma_assoc_iso A B C) (@sigma_assoc_osi A B C) _ _);
  intro; unfold sigma_assoc_osi, sigma_assoc_iso; crush.
Qed.
 
(* Exercise 2.11 *)



(* Exercise 2.12 *)

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
  