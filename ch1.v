Require Import HoTT.

(* Use sparingly! *)
Ltac rewriter := repeat (match goal with
                             | [ H : ?P |- _ ] => rewrite H
                         end).
Ltac simplHyp :=
  match goal with
      | [ H : _ * _ |- _ ] => destruct H (* half-assed, can be generalized for any inversion *)
  end.
Ltac crush := simpl in *; repeat simplHyp; try trivial.

Definition refl {A : Type} (x : A) : x = x := 1%path.

(* If you want to use concat, you will usually need to use eauto, since the
path concat passes through is UNSPECIFIED. *)
Hint Resolve ap11 ap01 concat.
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

(* Here is a traditional Coq proof using rewrite *)
Goal forall C c0 cs n, mynat_rec C c0 cs n = nat_rect (fun _ => C) c0 cs n.
  intros. unfold mynat_rec. rewrite mynat_rec_eq. crush.
Qed.

(* Here is a proof which utilizes explicit path concatenation *)
Goal forall C c0 cs n, mynat_rec C c0 cs n = nat_rect (fun _ => C) c0 cs n.
  intros.
  assert (H : snd (n, nat_rect (fun _ : nat => C) c0 cs n) = nat_rect (fun _ : nat => C) c0 cs n)
         by reflexivity.
  apply (concat (ap snd mynat_rec_eq) H).
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
    unfold pointwise_paths. (* destruct x0; reflexivity. *)
    apply Bool_rect; reflexivity.
  Defined.
  
  Definition myprod_ind (C : myprod A B -> Type)
                        (g : forall (x : A) (y : B), C (mymkprod x y)) (x : myprod A B) : C x :=
    transport C (myprod_uppt x) (g (mypr1 x) (mypr2 x)).
  (* same as exercise 1.3! *)
  Goal forall C g a b, myprod_ind C g (mymkprod a b) = g a b.
    intros.
    unfold myprod_ind.
    (* Prove the transport is trivial for canonical elements *)
    assert (myprod_uppt (mymkprod a b) = 1%path) as X.
      unfold myprod_uppt, mymkprod, mypr1, mypr2, Bool_rect.
      (* needs to be written with implicit arguments, or Coq infers the wrong ones. *)
      assert ((fun b0 : Bool =>
         if b0 as b1
          return
            (@paths (if b1 then A else B)
               (if b1 as b2 return (if b2 then A else B) then a else b)
               (if b1 as b2 return (if b2 then A else B) then a else b))
         then @idpath A a
         else @idpath B b) = fun _ => 1%path) as Y.
        (* why doesn't the by_extensionality tactic work here? *)
        apply H. unfold pointwise_paths. destruct x; reflexivity.
      (* I hear HoTTheorists don't like rewrite *)
      rewrite Y.
      apply path_forall_1.
    rewrite X.
    apply transport_1.
  Qed.
End ex_1_6.
