Require Import HoTT.

(* Use sparingly! *)
Ltac rewriter := 
  autorewrite with core;
  repeat (match goal with
            | [ H : ?P |- _ ] => rewrite H
          end).
Ltac simplHyp :=
  match goal with
      | [ H : _ * _ |- _ ] => destruct H (* half-assed, can be generalized for any inversion *)
  end.
(* do f_ap first, since simpl may undo the opportunity *)
Ltac crush := try f_ap; simpl in *; repeat simplHyp; try trivial.

Definition refl {A : Type} (x : A) : x = x := 1%path.

(* If you want to use concat, you will usually need to use eauto, since the
path concat passes through is UNSPECIFIED. *)
Hint Resolve ap11 ap01.
Hint Constructors prod.

(* Exercise 1.1 *)
Definition mycompose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
Goal forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
       mycompose h (mycompose g f) = mycompose (mycompose h g) f.
  reflexivity.
Qed.

(* Alternately: intros; cbv delta beta; reflexivity *)

(* Exercise 1.2 *)
Section ex_1_2_prod.
  Variable A B : Type.
  Check @fst.
  Check @snd.
  Definition my_prod_rec (C : Type) (g : A -> B -> C) (p : A * B) : C :=
    g (fst p) (snd p).
  Goal fst = my_prod_rec A (fun a => fun b => a). reflexivity. Qed.
  Goal snd = my_prod_rec B (fun a => fun b => b). reflexivity. Qed.
End ex_1_2_prod.

Section ex_1_2_sig.
  Variable A : Type.
  Variable B : A -> Type.
  Check @projT1.
  Check @projT2.
  Definition my_sig_rec (C : Type) (g : forall (x : A), B x -> C) (p : exists (x : A), B x) : C :=
    g (projT1 p) (projT2 p).
  Goal @projT1 A B = my_sig_rec A (fun a => fun b => a). reflexivity. Qed.
  (* recall it's not possible to implement projT2 with the recursor! *)
End ex_1_2_sig.

(* Exercise 1.3 *)

Section ex_1_3_prod.
  Variable A B : Type.
  Definition uppt : forall (x : A * B), ((fst x, snd x) = x) :=
    fun p => match p with (a,b) => refl (a,b) end.
  Definition my_prod_ind (C : A * B -> Type) (g : forall (x : A) (y : B), C (x, y)) (x : A * B) : C x :=
    transport C (uppt x) (g (fst x) (snd x)).
  Goal forall C g a b, my_prod_ind C g (a, b) = g a b. reflexivity. Qed.
End ex_1_3_prod.

Section ex_1_3_sig.
  Variable A : Type.
  Variable B : A -> Type.
  Definition sig_uppt : forall (x : exists (a : A), B a), ((projT1 x; projT2 x) = x) :=
    fun p => match p with (a;b) => refl (a;b) end.
  Definition mysig_ind (C : (exists (a : A), B a) -> Type) (g : forall (a : A) (b : B a), C (a; b)) (x : exists (a : A), B a) : C x :=
    transport C (sig_uppt x) (g (projT1 x) (projT2 x)).
  Goal forall C g a b, mysig_ind C g (a; b) = g a b. reflexivity. Qed.
End ex_1_3_sig.

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
    transport C (myprod_uppt x) (g (mypr1 x) (mypr2 x)).

  Lemma myprod_uppt_canonical : forall a b, myprod_uppt (mymkprod a b) = 1%path.
    intros; unfold myprod_uppt.
    transitivity (path_forall (mymkprod (mypr1 (mymkprod a b)) (mypr2 (mymkprod a b))) _ (fun _ => 1%path)).
      crush; by_extensionality x; destruct x; crush.
      apply path_forall_1. (* for some reason auto doesn't pick this up, maybe because of the axiom *)
  Qed.
  
  Hint Resolve transport_1 myprod_uppt_canonical.
  (* same as exercise 1.3! *)
  Goal forall C g a b, myprod_ind C g (mymkprod a b) = g a b.
    intros; unfold myprod_ind.
    transitivity (transport C 1%path (g (mypr1 (mymkprod a b)) (mypr2 (mymkprod a b)))); crush; auto.
  Qed.
End ex_1_6.

(* Exercise 1.7 *)

Definition ind {A : Type} : forall (C : forall (x y : A), x = y -> Type), (forall (x : A), C x x 1%path) -> forall (x y : A) (p : x = y), C x y p.
  path_induction; crush. (* the easy direction *)
Qed.

(* these are the textbook definitions that uses universes: notice they have exactly the same structure! *)

Definition ind'1 {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a (refl a)) (x : A) (p : a = x) : C x p.
  pose (D := fun x y p => forall (C : forall (z : A) (p : x = z), Type), C x 1%path -> C y p).
  assert (d : forall x : A, D x x 1%path) by exact (fun x C (c : C x 1%path) => c). (* cannot pose this, for some reason *)
  apply (ind D d); auto.
Qed.
Definition ind'2 {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a (refl a)) (x : A) (p : a = x) : C x p :=
  ind (fun x y p => forall (C : forall (z : A), x = z -> Type), C x 1%path -> C y p)
      (fun x C d => d)
      a x p C c.

Set Printing Universes.
Print ind'1.
Print ind'2.
Unset Printing Universes.

Check @transport.
Check @contr_basedpaths.
Print Contr.

Definition ind' {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a (refl a)) (x : A) (p : a = x) : C x p.
   refine (ind (fun _ _ _ => C x p) (fun _ => _) a x p).
   (* Contributed by jgross: use 'change' in order to convert the expressions into
      something we can do a normal transport over.  Fortunately, there is an
      obvious choice. *)
   change ((fun xp => C xp.1 xp.2) (a; 1%path)) in c.
   change ((fun xp => C xp.1 xp.2) (x; p)).
   Check (@contr _ (contr_basedpaths a) (x; p)).
   apply (transport _ (@contr _ (contr_basedpaths a) (x; p))); crush.
Qed.
Set Printing Universes.
Print ind'.
Unset Printing Universes.

Check (fun (A : Type) (x a : A) (p : a = x) => contr (x; p)).
Definition ind'' {A : Type} (a : A) (C : forall (x : A), a = x -> Type) (c : C a (refl a)) (x : A) (p : a = x) : C x p :=
  ind (fun _ _ _ => C x p)
      (fun _ => transport (fun z : exists x, a = x => C z.1 z.2)
                          (contr (x; p)) c)
      a x p.

(* Exercise 1.8 *)
Check nat_rect.
(*
nat_rect
     : forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)
Definition add (a b : nat) := nat_rect (fun _ => nat) a (fun _ n => S n) b.
Definition mult (a b : nat) := nat_rect (fun _ => nat) 0 (fun _ n => add n a) b.
Definition exp (a b : nat) := nat_rect (fun _ => nat) 1 (fun _ n => mult n a) b.
Eval compute in mult 3 4.
Eval compute in exp 2 4.

(* XXX blah blah proof *)

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

(* Exercise 1.14 *)

(* Exercise 1.15 *)

Theorem ioi' {A : Type} (C : A -> Type) (x y : A) (p : x = y) : C x -> C y.
  path_induction; auto.
Qed.

(* OK, this is cheating a little because the problem asked for a proof from plain 'path induction'.
Notice that the normal path induction proof is pretty similar to the based path induction proof. *)

Definition ioi {A : Type} (C : A -> Type) (x y : A) (p : x = y) : C x -> C y :=
  fun c => ind (fun _ _ _ => C y) (fun _ => transport C p c) x y p.
