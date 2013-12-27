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

  (* Annoyingly enough, this seems to be the idiomatic way to construct
     an IsHSet. Just cargo-cult it. *)
  intros x y; apply hprop_allpath; intros p q.

  (* Intuitively, the proof uses the equivalence to ferry an appropriate equality
     from the known set to the unknown set.  Of course, the details are a little touchy. *)

  assert (ap f^-1 p = ap f^-1 q) as H by (apply h).
  exact ((ap (ap f^-1))^-1 H).
Qed.

(* A generalized version of this statement is proved in the library. *)
Theorem ex3_1_library : forall A B, Equiv A B -> IsHSet A -> IsHSet B.
  intros A B e h.
  exact (trunc_equiv (equiv_fun _ _ e)).
Qed.

(* Here is a different proof that utilizes univalence.  Because it requires
   an axiom, it might be considered an inferior proof, but it is quite simple! *)
Theorem ex3_1_ua `{Univalence} : forall A B, Equiv A B -> IsHSet A -> IsHSet B.
  intros A B eq h.
  exact (transport IsHSet (equiv_path_universe _ _ eq) h).
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

  exact ((ap (path_sum x y)^-1)^-1 H).
Qed.

(* The HoTT library has rather sophisticated type-class machinery for
   generating proofs of set-likeness, and this can be used to automatically
   dispatch the appropriate already existing lemma. *)
Theorem ex3_2_library : forall A B, IsHSet A -> IsHSet B -> IsHSet (A + B).
  typeclasses eauto.
Qed.

(* Exercise 3.3 *)

(* Warmup: *)
Example thm3_1_5 : forall A B, IsHSet A -> IsHSet B -> IsHSet (A * B).
  intros A B h g.
  intros x y; apply hprop_allpath; intros p q.
  assert (path_prod _ _ (ap fst p) (ap snd p) = p) as a by apply eta_path_prod.
  assert (path_prod _ _ (ap fst q) (ap snd q) = q) as b by apply eta_path_prod.
  assert (path_prod _ _ (ap fst p) (ap snd p) = path_prod _ _ (ap fst q) (ap snd q)) as c.
    f_ap. apply h. apply g.
  exact (a^ @ c @ b).
Qed.

Theorem ex3_3 : forall A B, IsHSet A -> (forall x : A, IsHSet (B x)) -> IsHSet (sigT B).
  intros A B h g.
  intros x y; apply hprop_allpath; intros p q.
  assert (path_sigma_uncurried _ _ _ (p..1; p..2) = p) as a by apply eta_path_sigma_uncurried.
  assert (path_sigma_uncurried _ _ _ (q..1; q..2) = q) as b by apply eta_path_sigma_uncurried.
  assert (p..1 = q..1) as sa by apply h.
  assert (path_sigma_uncurried _ _ _ (p..1; p..2) = path_sigma_uncurried _ _ _ (q..1; q..2)) as c.
    f_ap. (* f_ap seems to not know to do path_sigma_uncurried *)
    apply path_sigma_uncurried. exists sa. apply g. (* NB: we don't have to worry about transport! Try simpl *)
  exact (a^ @ c @ b).
Qed.

(* XXX Despite its simplicity, I think this exercise is quite hard (much like exercise 2.7),
because the added dependence makes many plausible approaches not work.  Here are some
approaches that no longer work:

 * 'p..2 = q..2' does not typecheck (the direct approach). More generally, things
   which you would like to have the same type don't, and inserting transports yourself
   don't seem to help things (similarly, consider eta_path_sigma)
 * You cannot 'destruct' the term 'sa : p..1 = q..2' on account of dependence (the "oh
   let's try path induction willy-nilly)
 * Using the curried path_sigma function means you cannot apply f_ap to take
   advantage of the structure of the path space revealed by path_sigma (the "surely
   the shorter name is better crowd")

The key insight of this problem is that the path space of a sigma type... is a sigma
type itself, which is witnessed by the equivalence path_sigma_uncurried (note the
uncurried: the sigma does NOT show up when things are curried; it's an implicit phenomenon
due to dependence in that case). So if we need to analyze a complicated path like
p = q, we turn it into a path of sigma types, and then use standard techniques (path_sigma
/again/) to finally crack it.

I suspect the lessons learned here also may provide some clues for how to improve f_ap
further, in the face of dependence and multiple arguments (model them as sigmas!)

*)

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
  intro A.
  apply (equiv_adjointify (ex3_5_f A) (ex3_5_inverse A)); unfold Sect, ex3_5_f, ex3_5_inverse.
  intro f. apply path_forall. intro x. assert (IsHProp (Contr_internal A)) as X by typeclasses eauto. apply X.
  intro h. assert (IsHProp (IsHProp A)) as X by typeclasses eauto. apply X.
Qed.

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

(* This is a copy-paste of Theorem 3.2.2, but with ~~ replaced with Squash and relevant proof terms adjusted *)
Theorem ex3_11 `{Univalence} `{Funext} : ~ (forall A, Squash A -> A).
  intro f.
  pose proof (fun u => apD10 (apD f (path_universe thm3_2_2_e)) u) as h.
  pose proof (fun u => @transport_arrow _ (fun A => Squash A) (fun A => A) _ _ (path_universe thm3_2_2_e) (f Bool) u) as g.
  assert (forall (u v : Squash Bool), u = v) as eq.
    intros. pose proof (istrunc_truncation minus_one Bool) as X. apply X.
  assert (forall (u : Squash Bool), transport (fun A => Squash A) (path_universe thm3_2_2_e)^ u = u) as i.
    intros; apply eq.
  pose proof (fun u => (h u)^ @ g u @ ap (fun z => transport idmap (path_universe thm3_2_2_e) (f Bool z)) (i u)) as j.
  pose proof (fun u => j u @ transport_path_universe thm3_2_2_e (f Bool u)) as k.
  assert (forall x : Bool, ~(thm3_2_2_e x = x)) as X.
    destruct x; unfold thm3_2_2_e; simpl. apply false_ne_true. apply true_ne_false.
  apply (X (f Bool (truncation_incl true)) (k (truncation_incl true))^).
Qed.

(* The result of this exercise is a generalization of Theorem 3.2.2, in
the following sense: *)
Theorem thm3_2_2' `{Univalence} `{Funext} : ~ (forall A, ~~A -> A).
  intro f.
  refine (ex3_11 (fun A => _)). intro sa. apply f.
  refine (Truncation_rect_nondep (fun a p => p a) sa).
Qed.
(* NB: typeclasses automatically resolved the proof that ~~A is an HProp *)
(* We will consider how to go the other direction in a later exercise. *)

(* jgross suggests an alternate proof uses HITs (observing that the circle
   is connected (squash) but not contractible (not squashed)). The basic idea
   is the same: here, we use univalence to construct a nontrivial path space,
   in the alternate proof, the circle provides the nontrivial path space. *)

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