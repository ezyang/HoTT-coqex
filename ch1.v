Require Import HoTT.

(* By default, the HoTT library does not dump a bunch of notations in your
   scope.  However, these notations are tremendously useful, so most users
   of the HoTT library will want to open these two scopes, which introduce
   notations for paths and for equivalences.  The Cliff's notes version of
   these notations:

Notation "1" := idpath : path_scope.
Notation "p @ q" := (concat p q) (at level 20) : path_scope.
Notation "p ^" := (inverse p) (at level 3) : path_scope.
Notation "p # x" := (transport _ p x) (right associativity, at level 65) : path_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

NB: ^ and ^-1 bind quite tightly, so it's not uncommon to see terms like 'f^-1 a'
or '(f a)^-1'.
*)
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* There are also a number of other notations which /are/ enabled by default. The
most important ones are these:

Notation idmap := (fun x => x).
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.
Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.
Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.

NB: When writing code using the projT* notations, the space is usually omitted,
as in 'x.1' or 'p..2'. Coq will format it with a space, however.
 *)

(* The first chapter includes some exercises that might be seen in a traditional
   introduction to Coq.  There are many ways to go about solving these problems,
   but I've opted to approximate theorem-proving in the Chlipala style, as seen
   in CPDT, which emphasizes proof automation. *)
Ltac rewriter := 
  autorewrite with core;
  repeat (match goal with
            | [ H : ?P |- _ ] => rewrite H
          end).
Ltac simplHyp :=
  match goal with
      | [ H : _ * _ |- _ ] => destruct H (* half-assed, can be generalized for any inversion *)
  end.
Ltac crush := simpl in *; repeat simplHyp; try trivial; try solve [f_ap].

(* If you want to use concat, you will usually need to use eauto, since the
path concat passes through is UNSPECIFIED. *)
Hint Resolve ap11 ap01.
Hint Constructors prod.

(* Exercise 1.1 *)
Definition mycompose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
Theorem mycompose_assoc : forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
       mycompose h (mycompose g f) = mycompose (mycompose h g) f.
  reflexivity.
Qed.
(* Or you can do it after applying evaluation rules yourself. *)
Theorem mycompose_assoc' : forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
       mycompose h (mycompose g f) = mycompose (mycompose h g) f.
   intros. cbv delta beta. reflexivity.
Qed.
(* Remark: the fact that this is trivially true in a proof assistant
   is actually somewhat remarkable: it means that if you are able to
   formulate an operation as a function application, you get associativity
   for free.  It's worth contrasting this with the usual definition of
   addition on natural numbers, where associativity only holds *propositionally*. *)
Definition mycompose_library {A B C} := @compose A B C.

(* Exercise 1.2 *)
Section Book_1_2_prod.
  Variable A B : Type.
  Check @fst.
  Check @snd.
  Definition my_prod_rec (C : Type) (g : A -> B -> C) (p : A * B) : C :=
    g (fst p) (snd p).
  Goal fst = my_prod_rec A (fun a => fun b => a). reflexivity. Qed.
  Goal snd = my_prod_rec B (fun a => fun b => b). reflexivity. Qed.
End Book_1_2_prod.

Section Book_1_2_sig.
  Variable A : Type.
  Variable B : A -> Type.
  Check @projT1.
  Check @projT2.
  Definition my_sig_rec (C : Type) (g : forall (x : A), B x -> C) (p : exists (x : A), B x) : C :=
    g (projT1 p) (projT2 p).
  Goal @projT1 A B = my_sig_rec A (fun a => fun b => a). reflexivity. Qed.
  (* recall it's not possible to implement projT2 with the recursor! *)
End Book_1_2_sig.

(* Exercise 1.3 *)

Section Book_1_3_prod.
  Variable A B : Type.
  Definition prod_uppt : forall (x : A * B), ((fst x, snd x) = x) :=
    fun p => match p with (a,b) => 1 end.
  Definition prod_ind_uppt (C : A * B -> Type) (g : forall (x : A) (y : B), C (x, y)) (x : A * B) : C x :=
    transport C (prod_uppt x) (g (fst x) (snd x)).
  Definition Book_1_3_prod := prod_ind_uppt.
  Theorem Book_1_3_prod_refl : forall C g a b, prod_ind_uppt C g (a, b) = g a b. reflexivity. Qed.
End Book_1_3_prod.

Section Book_1_3_sig.
  Variable A : Type.
  Variable B : A -> Type.
  Definition sig_uppt : forall (x : exists (a : A), B a), ((projT1 x; projT2 x) = x) :=
    fun p => match p with (a;b) => 1 end.
  Definition sig_ind_uppt (C : (exists (a : A), B a) -> Type) (g : forall (a : A) (b : B a), C (a; b)) (x : exists (a : A), B a) : C x :=
    transport C (sig_uppt x) (g (projT1 x) (projT2 x)).
  Definition Book_1_3_sig := sig_ind_uppt.
  Theorem Book_1_3_sig_refl : forall C g a b, sig_ind_uppt C g (a; b) = g a b. reflexivity. Qed.
End Book_1_3_sig.

(* Exercise 1.4 *)
Fixpoint iter (C : Type) (c0 : C) (cs : C -> C) (n : nat) : C :=
  match n with
    | 0 => c0
    | S n' => cs (iter C c0 cs n')
  end.

Definition mynat_rec' (C : Type) : C -> (nat -> C -> C) -> nat -> nat * C := fun c0 cs n =>
  iter (nat * C) (0, c0) (fun p => (S (fst p), cs (fst p) (snd p))) n.
Definition mynat_rec (C : Type) : C -> (nat -> C -> C) -> nat -> C :=
  fun c0 cs n => snd (mynat_rec' C c0 cs n).

Hint Unfold mynat_rec' mynat_rec.

(* The trick to this proof is, of course, a strengthened induction hypothesis *)
Lemma mynat_rec_eq : forall {C c0 cs n}, mynat_rec' C c0 cs n = (n, nat_rect (fun _ => C) c0 cs n).
  (* Using uncurried path_prod keeps our induction hypothesis strong *)
  intros; apply path_prod_uncurried; induction n; crush; auto.
Qed.
Hint Resolve mynat_rec_eq.
Hint Rewrite @mynat_rec_eq : core.

(* Here is a traditional Coq proof using rewrite *)
Goal forall C c0 cs n, mynat_rec C c0 cs n = nat_rect (fun _ => C) c0 cs n.
  intros; unfold mynat_rec.
  rewriter; crush.
Qed.

(* Here is a proof which utilizes path concatenation *)
Goal forall C c0 cs n, mynat_rec C c0 cs n = nat_rect (fun _ => C) c0 cs n.
  intros; unfold mynat_rec.
  transitivity (snd (n, nat_rect (fun _ : nat => C) c0 cs n)); [ f_ap | reflexivity ].
Qed.

Eval compute in mynat_rec (list nat) nil (@cons nat) 2.
Eval compute in nat_rect (fun _ => list nat) nil (@cons nat) 2.

(* Exercise 1.5 *)
Definition mycoprod (A B : Type) := exists (x : Bool), Bool_rect (fun _ => Type) A B x.

Section ex_1_5.
  Variable A B : Type.
  Definition inl := existT (Bool_rect (fun _ => Type) A B) true.
  Definition inr := existT (Bool_rect (fun _ => Type) A B) false.
  (* So many ways to write this function! And all of them with different representations... *)
  Definition f1 (C : Type) (l : A -> C) (r : B -> C) (x : Bool) : Bool_rect (fun _ => Type) A B x -> C :=
    match x return Bool_rect (fun _ => Type) A B x -> C (* annotation not necessary *) with
        | true => l
        | false => r
    end.
  Definition f1' (C : Type) (l : A -> C) (r : B -> C) (x : Bool) : Bool_rect (fun _ => Type) A B x -> C :=
    if x return Bool_rect (fun _ => Type) A B x -> C then l else r.
  Definition f2 (C : Type) (l : A -> C) (r : B -> C) (x : Bool) : Bool_rect (fun _ => Type) A B x -> C :=
    Bool_rect (fun x => Bool_rect (fun _ => Type) A B x -> C) l r x.
  Definition f3 (C : Type) (l : A -> C) (r : B -> C) (x : Bool) (b : Bool_rect (fun _ => Type) A B x) : C.
    destruct x; [ exact (l b) | exact (r b) ].
  Defined.
  Definition f4 (C : Type) (l : A -> C) (r : B -> C) (x : Bool) : Bool_rect (fun _ => Type) A B x -> C.
    destruct x; [ exact l | exact r ].
  Defined.
  Definition f5 (C : Type) (l : A -> C) (r : B -> C) (x : Bool) : Bool_rect (fun _ => Type) A B x -> C.
    apply (Bool_rect (fun x => Bool_rect (fun _ => Type) A B x -> C)); [ exact l | exact r ].
  Defined.
  Eval hnf in f1'.
  Definition mycoprod_rec (C : Type) (l : A -> C) (r : B -> C) (x : mycoprod A B) : C := sigT_rect (fun _ => C) (f2 C l r) x.
  Definition mycoprod_ind (C : mycoprod A B -> Type)
                          (l : forall (a : A), C (inl a))
                          (r : forall (b : B), C (inr b))
                          (x : mycoprod A B) : C x :=
    sigT_rect C (Bool_rect (fun y => forall (b : Bool_rect (fun _ => Type) A B y), C (y; b)) l r) x.

  Goal forall C l r x, mycoprod_ind C l r (inl x) = l x. reflexivity. Qed.
  Goal forall C l r x, mycoprod_ind C l r (inr x) = r x. reflexivity. Qed.
End ex_1_5.

(* Exercise 1.6 *)

Definition myprod (A B : Type) := forall (x : Bool), Bool_rect (fun _ => Type) A B x.
Section ex_1_6.
  Context `{Funext}.
  Variable A B : Type.
  Definition mypr1 (p : myprod A B) := p true.
  Definition mypr2 (p : myprod A B) := p false.
  Definition mymkprod (a : A) (b : B) : myprod A B := Bool_rect (Bool_rect (fun _ => Type) A B) a b.
  Definition myprod_uppt (x : myprod A B) : (mymkprod (mypr1 x) (mypr2 x) = x).
    apply path_forall. (* function extensionality! *)
    unfold pointwise_paths; apply Bool_rect; reflexivity.
  Defined.

  Definition myprod_ind (C : myprod A B -> Type)
                        (g : forall (x : A) (y : B), C (mymkprod x y)) (x : myprod A B) : C x :=
    myprod_uppt x # g (mypr1 x) (mypr2 x).

  Lemma myprod_uppt_canonical : forall a b, myprod_uppt (mymkprod a b) = 1.
    intros; unfold myprod_uppt.
    transitivity (path_forall (mymkprod (mypr1 (mymkprod a b)) (mypr2 (mymkprod a b))) _ (fun _ => 1)).
      f_ap; crush; by_extensionality x; destruct x; crush.
      apply path_forall_1. (* for some reason auto doesn't pick this up, maybe because of the axiom *)
  Qed.
  
  Hint Resolve transport_1 myprod_uppt_canonical.
  (* same as exercise 1.3! *)
  Goal forall C g a b, myprod_ind C g (mymkprod a b) = g a b.
    intros; unfold myprod_ind.
    transitivity (transport C 1 (g (mypr1 (mymkprod a b)) (mypr2 (mymkprod a b)))); try f_ap; crush; auto.
  Qed.
End ex_1_6.

(* Exercise 1.7 *)

Definition ind {A : Type} : forall (C : forall (x y : A), x = y -> Type), (forall (x : A), C x x 1) -> forall (x y : A) (p : x = y), C x y p.
  path_induction; crush. (* the easy direction *)
Qed.

(* these are the textbook definitions that uses universes: notice they have exactly the same structure! *)

Definition ind'1 {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a 1) (x : A) (p : a = x) : C x p.
  pose (D := fun x y p => forall (C : forall (z : A) (p : x = z), Type), C x 1 -> C y p).
  assert (d : forall x : A, D x x 1) by exact (fun x C (c : C x 1) => c). (* cannot pose this, for some reason *)
  apply (ind D d); auto.
Qed.
Definition ind'2 {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a 1) (x : A) (p : a = x) : C x p :=
  ind (fun x y p => forall (C : forall (z : A), x = z -> Type), C x 1 -> C y p)
      (fun x C d => d)
      a x p C c.

Set Printing Universes.
Print ind'1.
Print ind'2.
Unset Printing Universes.

Check @transport.
Check @contr_basedpaths.
Print Contr.

Definition ind' {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a 1) (x : A) (p : a = x) : C x p.
   refine (ind (fun _ _ _ => C x p) (fun _ => _) a x p).
   (* Contributed by jgross: use 'change' in order to convert the expressions into
      something we can do a normal transport over.  Fortunately, there is an
      obvious choice. *)
   change ((fun xp => C xp.1 xp.2) (a; 1)) in c.
   change ((fun xp => C xp.1 xp.2) (x; p)).
   Check (@contr _ (contr_basedpaths a) (x; p)).
   apply (transport _ (@contr _ (contr_basedpaths a) (x; p))); crush.
Qed.
Set Printing Universes.
Print ind'.
Unset Printing Universes.

Check (fun (A : Type) (x a : A) (p : a = x) => contr (x; p)).
Definition ind'' {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a 1) (x : A) (p : a = x) : C x p :=
  ind (fun _ _ _ => C x p)
      (fun _ => transport (fun z : exists x, a = x => C z.1 z.2)
                          (contr (x; p)) c)
      a x p.

(* Exercise 1.8 *)
Check nat_rect.
(* You can write these to ways, and it's traditional to recurse on the first argument *)
Definition add (a b : nat) := nat_rect (fun _ => nat) b (fun _ n => S n) a.
Definition mult (a b : nat) := nat_rect (fun _ => nat) 0 (fun _ n => add n b) a.
Definition exp (a b : nat) := nat_rect (fun _ => nat) 1%nat (fun _ n => mult n b) a.
Eval compute in mult 3 4.
Eval compute in exp 2 4.

(* You need congruence of naturals to do some of these proofs, I think. *)

Lemma nat_plus_assoc : forall a b c, add (add a b) c = add a (add b c).
  intros; induction a; crush.
Qed.
Lemma nat_plus_r_zero : forall a, add a 0 = a. induction a; crush. Qed.
Lemma nat_plus_l_zero : forall a, add 0 a = a. reflexivity. Qed.
Hint Immediate nat_plus_r_zero nat_plus_l_zero.
Hint Rewrite nat_plus_r_zero nat_plus_l_zero.
Lemma nat_plus_r_succ : forall a b, add a (S b) = S (add a b). intros; induction a; crush. Qed.
Hint Resolve nat_plus_r_succ.
Lemma nat_plus_commutative : forall a b, add a b = add b a.
  induction a; induction b; crush; f_ap; auto. transitivity (S (add a b)); auto.
Qed. (* oh the lack of congruence! *)

Lemma nat_mult_l_succ : forall a b, mult (S a) b = add b (mult a b).
  intros; induction a; crush. apply inverse; auto. apply nat_plus_commutative.
Qed.
Lemma nat_mult_distr : forall a b c, mult (add a b) c = add (mult a c) (mult b c).
  intros; induction a; crush. destruct b; rewriter; crush.
  (* WHERE IS MY CONGRUENCE!!! *)
  transitivity (add c (add (mult a c) (add (mult b c) c))). apply nat_plus_commutative.
  transitivity (add (add c (mult a c)) (add (mult b c) c)). rewrite <- nat_plus_assoc; trivial.
  change ((fun p => add p (add (mult b c) c)) (add c (mult a c)) = (fun p => add p (add (mult b c) c)) (add (mult a c) c)).
  f_ap. apply nat_plus_commutative.
Qed.
Hint Resolve nat_mult_distr.  
Hint Resolve nat_mult_l_succ.
Lemma nat_mult_assoc : forall a b c, mult (mult a b) c = mult a (mult b c).
  intros; induction a; crush. rewrite <- IHa. auto.
Qed.
Lemma nat_mult_l_one : forall a, mult 1 a = a. reflexivity. Qed.
Lemma nat_mult_r_one : forall a, mult a 1 = a. induction a; crush. rewrite IHa; crush. rewrite nat_plus_commutative; crush.

(* XXX blah blah proof. I gave up because doing these without congruence is annoying *)

(* Exercise 1.9 *)

(* Exercise 1.10 *)

(* Exercise 1.11 *)

Goal forall A : Type, ~~~A -> ~A. auto. Qed.
(* OK, not so interesting? *)
Goal forall A : Type, ~~~A -> ~A.
  unfold not.
  intros A H X.
  apply H.
  intro G.
  apply G.
  apply X.
Qed.

(* Exercise 1.12 *)

Definition ex1_12_i (A B : Type) : A -> (B -> A) := fun (a : A) => fun (_ : B) => a.
Definition ex1_12_ii (A : Type) : A -> ~~A := fun (a : A) => fun (na : A -> Empty) => na a.
Definition ex1_12_iii (A B : Type) : ~A \/ ~B -> ~(A /\ B) := fun (d : ~A \/ ~B) => fun (p : A /\ B) => match d with| Datatypes.inl na => na (fst p) | Datatypes.inr nb => nb (snd p) end.

(* Exercise 1.13 *)

Goal forall P, ~~(P \/ ~P). unfold not; auto. Qed.

(* Exercise 1.14 *)

Definition f : forall (A : Type) (x : A) (p : x = x), p = 1.
  intros. path_induction.
  try (exact 1).
Abort.

(* The problem is both endpoints are fixed. There are nontrivial homotopies now! *)

(* Exercise 1.15 *)

Theorem ioi' {A : Type} (C : A -> Type) (x y : A) (p : x = y) : C x -> C y.
  path_induction; auto.
Qed.

(* OK, this is cheating a little because the problem asked for a proof from plain 'path induction'.
Notice that the normal path induction proof is pretty similar to the based path induction proof. *)

Definition ioi {A : Type} (C : A -> Type) (x y : A) (p : x = y) : C x -> C y :=
  fun c => ind (fun _ _ _ => C y) (fun _ => p # c) x y p.
