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

Goal forall A B, IsHSet A -> IsHSet B -> IsHSet (A * B).
  intros A B h g.
  intros x y; apply hprop_allpath; intros p q.
  assert (ap fst p = ap fst q) by apply h.
  assert (ap snd p = ap snd q) by apply g.
  assert ((ap fst p, ap snd p) = (ap fst q, ap snd q)) by f_ap.
  (* apply (path_prod_uncurried^-1 X1).
  pose proof (eta_path_prod X X0).
  Check @eta_path_prod. *)
Abort.

(* Exercise 3.3 *)
Theorem ex3_3 : forall A B, IsHSet A -> (forall x : A, IsHSet (B x)) -> IsHSet (sigT B).
  intros A B h g.
  intros x y; apply hprop_allpath; intros p q.
  assert (p..1 = q..1) as s by apply h.
Abort.

Theorem ex3_3_library : forall A B, IsHSet A -> (forall x : A, IsHSet (B x)) -> IsHSet (sigT B).
  typeclasses eauto.
Qed.

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

(* Exercise 3.8 *)

Require Import Truncations.
Check Truncation.
Notation Squash A := (Truncation minus_one A).

Definition qinv {A B} (f : A -> B) := {g : B -> A & ((f o g = idmap) * (g o f = idmap))}.

(* Exercise 3.9 *)

(* oops, HoTT library doesn't seem to have LEM, see https://github.com/HoTT/HoTT/issues/299 *)
Class LEM :=
  { lem :> forall (A : Type), IsHProp A -> A + ~A }.

(* computation rules *)
Lemma lem_unit `{LEM} : lem Unit _ = inl tt.
  destruct (lem Unit _). destruct u. auto.
  contradiction (n tt).
Qed.
Lemma lem_empty `{LEM} `{Funext} : lem Empty _ = inr idmap.
  destruct (lem Empty _). contradiction. f_ap. apply ap10^-1. intro x. contradiction.
Qed.

Definition ex3_9_f `{LEM} : sigT IsHProp -> Bool.
  intro x.
  destruct (lem x.1 x.2).
  exact true.
  exact false.
Defined.  

Definition ex3_9_inverse : Bool -> sigT IsHProp.
  intro b.
  destruct b.
  exists Unit; typeclasses eauto.
  exists Empty; typeclasses eauto.
Defined.

Theorem ex3_9 `{LEM} `{Univalence} : sigT IsHProp <~> Bool.
  apply (equiv_adjointify ex3_9_f ex3_9_inverse); unfold Sect, ex3_9_f, ex3_9_inverse.
    destruct x; simpl.
      (* meh, too difficult to do the rewrite *)
      destruct (lem Unit _); auto. contradiction (n tt).
      destruct (lem Empty _); auto. contradiction.
    destruct x as [A h]; simpl. destruct (lem A h).
      pose proof (contr_inhabited_hprop A a).
      pose proof equiv_contr_unit as g'.
      pose proof ((path_universe g') ^) as g.
      try apply (path_sigma IsHProp (Unit; trunc_succ) (A; h) g).
      (* universe inconsistency *)
Abort.

(* Exercise 3.10 *)

(* Exercise 3.11 *)

Definition thm3_2_2_e : Bool <~> Bool.
  apply (equiv_adjointify negb negb); unfold Sect; destruct x; trivial.
Defined.

Theorem thm3_2_2 `{Univalence} `{Funext} : ~ (forall A, ~~A -> A).
  intro f.
  (* NB: happly is called apD10 *)
  (* to work around universe inconsistency, you cannot path_universe in a Definition *)
  pose proof (fun u => apD10 (apD f (path_universe thm3_2_2_e)) u) as h.
  (* NB: lemma 2.9.4 is transport_arrow *)
  pose proof (fun u => @transport_arrow _ (fun A => ~~A) (fun A => A) _ _ (path_universe thm3_2_2_e) (f Bool) u) as g.
  assert (forall (u v : ~~Bool), u = v) as eq.
    intros; apply path_forall; intro x; contradiction (u x).
  assert (forall (u : ~~Bool), transport (fun A => ~~A) (path_universe thm3_2_2_e)^ u = u) as i.
    intros; apply eq.
  pose proof (fun u => (h u)^ @ g u @ ap (fun z => transport idmap (path_universe thm3_2_2_e) (f Bool z)) (i u)) as j.
  (* NB: 2.10 discussion is transport_path_universe *)
  pose proof (fun u => j u @ transport_path_universe thm3_2_2_e (f Bool u)) as k.
  assert (forall x : Bool, ~(thm3_2_2_e x = x)) as X.
    destruct x; unfold thm3_2_2_e; simpl. apply false_ne_true. apply true_ne_false.
  apply (X (f Bool (fun k => k true)) (k (fun k => k true))^).
Qed.

Corollary thm3_2_7 `{Univalence} `{Funext} : ~ (forall A, A + ~A).
  intro g.
  refine (thm3_2_2 (fun A => _)).
  intro u.
  destruct (g A). trivial. contradiction (u n).
Qed.

Theorem ex3_11 `{Univalence} `{Funext} `{LEM} : ~ (forall A, Squash A -> A).
  intro f.
  refine (thm3_2_2 (fun A => _)).
  intro u.
Abort. (* I seem to want LEM and ex3_14 here, but we can only validly assume LEM on As that are HProp. *)

(* Exercise 3.12 *)

Theorem ex3_12 `{LEM} : forall A, Squash (Squash A -> A).
  intro.
  apply truncation_incl. (* This can't be right. *)
Abort.

(* Exercise 3.13 *)

Theorem ex3_13 : (forall A, A + ~A) -> (forall X Y, IsHSet X -> (forall (x : X), IsHSet (Y x)) -> (forall x, Squash (Y x)) -> Squash (forall x, Y x)).
  intros lemi X Y xset yset h.
  destruct (lemi X).
  refine (Truncation_rect_nondep (fun syx => truncation_incl (fun x' => _)) (h x)).
Abort.