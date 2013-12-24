Require Import HoTT.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* Exercise 3.1 *)

Theorem ex3_1 : forall A B, Equiv A B -> IsHSet A -> IsHSet B.
  intros A B eq h.
  destruct eq as [f i].

  (* There is a very important fact to remember about ap and equivalences! You
     will have a hard time solving this question without remembering it. *)
  SearchAbout ap IsEquiv.
  (* NB: pose proof says "Here is a proof term, stick it in the context."
     It's often convenient, because you don't have to say what the type of the term is. *)
  pose proof (@isequiv_ap B A f^-1 isequiv_inverse) as ap_equiv.

  (* Annoyingly enough, this seems to be the idiomatic way to construct
     an IsHSet. Just cargo-cult it. *)
  intros x y; apply hprop_allpath; intros p q.

  (* Intuitively, the proof uses the equivalence to ferry an appropriate equality
g     from the known set to the unknown set.  Of course, the details are a little touchy. *)

  assert (forall p' q' : f^-1 x = f^-1 y, (ap f^-1)^-1 p' = (ap f^-1)^-1 q') as H.
    intros; repeat f_ap; apply h.

  assert ((ap f^-1)^-1 (ap f^-1 p) = p) as r. apply eissect.
  assert ((ap f^-1)^-1 (ap f^-1 q) = q) as s. apply eissect.
  refine (r^ @ H _ _ @ s).
Qed.

(* A generalized version of this statement is proved in the library. *)
Theorem ex3_1_library : forall A B, Equiv A B -> IsHSet A -> IsHSet B.
  intros A B e h. apply (trunc_equiv (equiv_fun _ _ e)).
Qed.

(* Here is a different proof that utilizes univalence.  Because it requires
   an axiom, it might be considered an inferior proof, but it is quite simple! *)
Theorem ex3_1_ua `{Univalence} : forall A B, Equiv A B -> IsHSet A -> IsHSet B.
  intros A B eq h.
  assert (A = B) as p. apply equiv_path_universe; trivial.
  apply (transport IsHSet p); trivial.
Qed.

(* Exercise 3.2 *)

Theorem ex3_2 : forall A B, IsHSet A -> IsHSet B -> IsHSet (A + B).
  intros A B g h.
  (* Intuitively, this proof is all about the codes. Analyzing the path space
     over A + B otherwise is difficult.  In Chapter 2, we re-did the codes;
     here, we'll use a code provided by the standard library. *)
  SearchAbout sum paths.

  intros x y; apply hprop_allpath; intros p q.

  assert ((path_sum x y)^-1 p = (path_sum x y)^-1 q) as H.
    pose proof ((path_sum x y)^-1 p). (* just a little trick to make contradiction work *)
    destruct x; destruct y; try apply g; try apply h; try contradiction.

  (* XXX I think there should be some lemma which makes this work *)
  assert (path_sum x y ((path_sum x y)^-1 p) = p) as s by apply eisretr.
  assert (path_sum x y ((path_sum x y)^-1 q) = q) as r by apply eisretr.
  exact (s^ @ ap (path_sum x y) H @ r).
Qed.

(* The HoTT library has rather sophisticated type-class machinery for
   generating proofs of set-likeness, and this can be used to automatically
   dispatch the appropriate already existing lemma. *)
Theorem ex3_2_library : forall A B, IsHSet A -> IsHSet B -> IsHSet (A + B).
  typeclasses eauto.
Qed.

(* Exercise 3.3 *)
Theorem ex3_3 : forall A B, IsHSet A -> (forall x : A, IsHSet (B x)) -> IsHSet (sigT B).
  intros A B h g.
  intros x y; apply hprop_allpath; intros p q.
  try assert (eta_path_sigma p = eta_path_sigma q).
Abort.

(* Exercise 3.4 *)
Lemma ex3_4_right `{Funext} : forall A, IsHProp A -> Contr (A -> A).
  intros A h. refine (BuildContr _ (fun x => x) _).
  intro f. apply path_forall. intro x. apply h. (* NB: tc resolution seems to defeat auto *)
Qed.

Lemma ex3_4_left : forall A, Contr (A -> A) -> IsHProp A.
  intros A [center h]. apply hprop_allpath; intros x y.
  SearchAbout pointwise_paths.
  pose proof (ap10 (h (fun _ => x)) x) ^ as p.
  pose proof (ap10 (h (fun _ => y)) x) as q.
  transitivity (center x); auto.
Qed.

Hint Resolve ex3_4_left ex3_4_right.
Theorem ex3_4 `{Funext} : forall A, IsHProp A <-> Contr (A -> A).
  constructor; auto.
Qed.

(* Exercise 3.5 *)

Definition ex3_5_f A (h : IsHProp A) := fun x => BuildContr _ x (fun y => allpath_hprop x y).
Definition ex3_5_inverse A (g : A -> Contr A) := hprop_allpath A (fun x y => let H := g x in path_contr x y).
Definition ex3_5_inverse' A (g : A -> Contr A) := fun x y => let H := g x in contr_paths_contr x y.

Theorem ex3_5 `{Funext} : forall A, Equiv (IsHProp A) (A -> Contr A).
Abort.

Theorem ex3_5_library `{Funext} : forall A, Equiv (IsHProp A) (A -> Contr A).
  intros; apply equiv_hprop_inhabited_contr.
Qed.

(* Exercise 3.6 *)

Theorem ex3_6 `{Funext} : forall A, IsHProp A -> IsHProp (A + ~A).
  intros A h.
  apply hprop_allpath; intros x y.
  destruct x; destruct y; try contradiction; f_ap.
    apply h.
    apply path_forall; intro. contradiction. (* honestly, this should be a lemma *)
Qed.
(* NB: you can't do it without extensionality! *)

(* Exercise 3.7 *)

Theorem ex3_7 : forall A B, IsHProp A -> IsHProp B -> ~ (A * B) -> IsHProp (A + B).
  intros A B h g e.
  apply hprop_allpath; intros x y.
  destruct x; destruct y; try contradiction (e (a,b)); f_ap.
    apply h. apply g.
Qed.
 