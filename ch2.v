
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

(* An important question one has to answer here is, what is the equivalent
of pair^= here? In the previous cases, we considered products, so we just
always provided two equalities for each member of the pair; but here,
we have a single equality which is *different* depending on what is inhabiting
the pair. So our equality needs to be dependent now! *)

Check path_sum.

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
Theorem ex2_8 {A B A' B' : Type} (g : A -> A') (h : B -> B') (x y : A + B)
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

(* The presentation of sums in the book uses 'codes' to describe
the match statements that occur in the theorem statements.  While the
HoTT Coq library proper does not use codes for sums (only for the
circle), it is instructive to redo the exercise with that formalism. *)

Definition lcode {A B} {a0 : A} (x : A + B) := match x with inl a => a0 = a | inr b => Empty end.
Definition lencode {A B} {a0 : A} (x : A + B) (p : inl a0 = x) : lcode x := transport lcode p idpath.
Definition ldecode {A B} {a0 : A} (x : A + B) (c : @lcode A B a0 x) : inl a0 = x.
  destruct x. f_ap. destruct c.
Defined.

Definition rcode {A B} {b0 : B} (x : A + B) := match x with inl a => Empty | inr b => b0 = b end.
Definition rencode {A B} {b0 : B} (x : A + B) (p : inr b0 = x) : rcode x := transport rcode p idpath.
Definition rdecode {A B} {b0 : B} (x : A + B) (c : @rcode A B b0 x) : inr b0 = x.
  destruct x. destruct c. f_ap.
Defined.

(* XXX TODO *)

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
  