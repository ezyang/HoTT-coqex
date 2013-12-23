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
     from the known set to the unknown set.  Of course, the details are a little touchy. *)

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
Abort.

(* The HoTT library has rather sophisticated type-class machinery for
   generating proofs of set-likeness, and this can be used to automatically
   dispatch the appropriate already existing lemma. *)
Theorem ex3_2_library : forall A B, IsHSet A -> IsHSet B -> IsHSet (A + B).
  typeclasses eauto.
Qed.