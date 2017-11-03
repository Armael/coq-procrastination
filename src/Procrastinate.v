(******************************************************************************)
(* begin procrastination [group g] [assuming a b...]                          *)
(* procrastinate [g]                                                          *)
(* end procrastination                                                        *)
(* already procrastinated [g]                                                 *)
(* with procrastination [group g] do cont                                     *)
(******************************************************************************)

Module Marker.

Definition end_procrastination (P : Type) := P.

Definition group (P : Prop) := P.

Ltac find_group :=
  match goal with
  | H : group _ |- _ => constr:(H)
  end.

End Marker.

Module MkHelperLemmas.

(* General helpers *)

Local Ltac transparent_assert name type :=
  unshelve refine (let name := _ : type in _).

Inductive Boxer :=
| boxer : forall A : Type, A -> Boxer.
Arguments boxer : clear implicits.

Local Ltac mk_forall varty goalty n cont :=
  lazymatch n with
  | O => cont (@nil Boxer)
  | S ?n' =>
    let X := fresh "x" in
    refine (forall (X : varty), _ : goalty);
    mk_forall varty goalty n' ltac:(fun x => cont (cons (boxer varty X) x))
  end.

Local Ltac mk_forall_tys vartys goalty cont :=
  lazymatch vartys with
  | nil => cont (@nil Boxer)
  | cons (boxer _ ?ty) ?tys =>
    let X := fresh "x" in
    refine (forall (X : ty), _ : goalty);
    mk_forall_tys tys goalty ltac:(fun x => cont (cons (boxer ty X) x))
  end.

Local Ltac mk_arrow vars goalty :=
  lazymatch vars with
  | nil => idtac
  | cons (boxer _ ?v) ?vs =>
    refine (v -> _ : goalty);
    mk_arrow vs goalty
  end.

Local Ltac mk_app f vars goalty :=
  lazymatch vars with
  | nil => exact f
  | cons (boxer _ ?v) ?vs =>
    refine (_ v : goalty);
    let x := fresh "x" in intro x;
    mk_app (f x) vs goalty
  end.

Local Ltac mk_sigT_sig n goalty cont :=
  lazymatch n with
  | 0 => cont (@nil Boxer)
  | 1 =>
    let X := fresh "x" in
    refine (sig (fun X => _) : goalty);
    cont (cons (@boxer _ X) (@nil Boxer))
  | S ?n' =>
    let X := fresh "x" in
    refine (sigT (fun X => _) : goalty);
    mk_sigT_sig n' goalty ltac:(fun x => cont (cons (@boxer _ X) x))
  end.

Local Ltac mk_exists n goalty cont :=
  lazymatch n with
  | O => cont (@nil Boxer)
  | S ?n' =>
    let X := fresh "x" in
    refine (exists X, _ : goalty);
    mk_exists n' goalty ltac:(fun x => cont (cons (@boxer _ X) x))
  end.

Local Ltac introsType :=
  repeat (
      match goal with
      | |- forall (_ : Type), _ =>
        intro
      end
    ).

(** [begin procrastination] helpers *)

Local Ltac prove_begin_procrastination_helper :=
  introsType;
  intros facts P H1 H;
  unfold Marker.end_procrastination in *;
  repeat (let x := fresh "x" in destruct H as (x & H));
  eauto.

Goal forall (g : Prop) (P : Type),
    (Marker.group g -> P) ->
    Marker.end_procrastination g ->
    P.
Proof. prove_begin_procrastination_helper. Qed.

Goal forall A (g : A -> Prop) (P : Prop),
    (forall a, Marker.group (g a) -> P) ->
    Marker.end_procrastination (exists a, g a) ->
    P.
Proof. prove_begin_procrastination_helper. Qed.

Goal forall A B (g : A -> B -> Prop) (P : Prop),
    (forall a b, Marker.group (g a b) -> P) ->
    Marker.end_procrastination (exists a b, g a b) ->
    P.
Proof. prove_begin_procrastination_helper. Qed.

Goal forall A B (g : A -> B -> Prop) (P : Type),
    (forall a b, Marker.group (g a b) -> P) ->
    Marker.end_procrastination {a : A & { b | g a b } } ->
    P.
Proof. prove_begin_procrastination_helper. Qed.

(* Generates a definition G := ... . G then corresponds to a goal that can be
   proved using [prove_begin_procrastination_helper], and is of the form:

  forall
    (A B .. Z : Type)
    (facts : A -> B -> .. -> Z -> Prop)
    (P: Prop),
  (forall a b .. z, Marker.group (facts a b .. z) -> P) ->
  end_procrastination (exists a b .. z, facts a b .. z) ->
  P.

  The type of P is actually taken as a parameter Pty (in practice, Prop or
  Type), and the last hypothesis is produced by the argument tactic [mk_exists].

  When P is of type Prop, the last hypothesis is as shown, and uses exists.
  When P is of type Type, the last hypothesis is instead of the form
    sigT (fun a => sigT (fun b => ... sig (fun z => facts_closed a b .. z)))
*)
Local Ltac mk_begin_procrastination_helper_aux n G Pty mk_exists :=
  transparent_assert G Type;
  [ mk_forall Type Type n ltac:(fun L =>
      let g_ty := fresh "g_ty" in
      transparent_assert g_ty Type;
      [ mk_arrow L Type; exact Prop | simpl in g_ty];

      let g := fresh "g" in
      refine (forall (g : g_ty), _ : Type);
      subst g_ty;

      let P := fresh "P" in
      refine (forall (P : Pty), _ : Type);

      let H1 := fresh "H1" in transparent_assert H1 Type;
      [ mk_forall_tys L Type ltac:(fun l =>
          let g_args := fresh in transparent_assert g_args Prop;
          [ mk_app g l Prop | simpl in g_args];
          refine (Marker.group g_args -> P : Type)
        )
      | simpl in H1];

      let H2 := fresh "H2" in transparent_assert H2 Type;
      [ refine (Marker.end_procrastination _ : Type);
        mk_exists n ltac:(fun l => mk_app g l Prop)
      | simpl in H2];

      exact (H1 -> H2 -> P)
    )
  | simpl in G].

Local Ltac mk_begin_procrastination_helper_Type n G :=
  mk_begin_procrastination_helper_aux n G Type
    ltac:(fun n cont => mk_sigT_sig n Type cont).

Local Ltac mk_begin_procrastination_helper_Prop n G :=
  mk_begin_procrastination_helper_aux n G Prop
    ltac:(fun n cont => mk_exists n Prop cont).

Ltac mk_begin_procrastination_helper n :=
  let H := fresh in
  match goal with |- ?G =>
    match type of G with
    | Prop => mk_begin_procrastination_helper_Prop n H
    | _ => mk_begin_procrastination_helper_Type n H
    end;
    cut H; subst H; [| prove_begin_procrastination_helper]
  end.

Goal True. mk_begin_procrastination_helper 0. intro H; eapply H; clear H.
Abort.

Goal True. mk_begin_procrastination_helper 3. intro H; eapply H; clear H.
Abort.

Goal nat. mk_begin_procrastination_helper 3. intro H; eapply H; clear H.
Abort.

(** [end procrastination] helpers *)

Local Ltac prove_end_procrastination_helper :=
  introsType;
  let P1 := fresh in
  let P2 := fresh in
  let H1 := fresh in
  let H2 := fresh in
  intros P1 P2 H1 H2;
  unfold Marker.end_procrastination in *;
  repeat (let x := fresh "x" in destruct H2 as (x & H2); exists x);
  apply H1; auto.

Goal forall A (P1 P2 : A -> Prop),
  (forall a, P1 a -> P2 a) ->
  (exists a, P1 a) ->
  Marker.end_procrastination (exists a, P2 a).
Proof. prove_end_procrastination_helper. Qed.

Goal forall A B (P1 P2 : A -> B -> Prop),
  (forall a b, P1 a b -> P2 a b) ->
  (exists a b, P1 a b) ->
  Marker.end_procrastination (exists a b, P2 a b).
Proof. prove_end_procrastination_helper. Qed.

Goal forall A (P1 P2 : A -> Prop),
  (forall a, P1 a -> P2 a) ->
  { a | P1 a } ->
  Marker.end_procrastination { a | P2 a }.
Proof. prove_end_procrastination_helper. Qed.

Local Ltac mk_end_procrastination_helper_aux n G mk_exists :=
  transparent_assert G Type;
  [ mk_forall Type Type n ltac:(fun L =>
      let P_ty := fresh "P_ty" in
      transparent_assert P_ty Type;
      [ mk_arrow L Type; exact Prop | simpl in P_ty ];

      let P1 := fresh "P1" in
      let P2 := fresh "P2" in
      refine (forall (P1 P2 : P_ty), _ : Type);
      subst P_ty;

      let H1 := fresh "H1" in transparent_assert H1 Type;
      [ mk_forall_tys L Type ltac:(fun l =>
          refine (_ -> _ : Type);
          [ mk_app P1 l Type | mk_app P2 l Type ]
        )
      | simpl in H1 ];

      refine (H1 -> _ -> Marker.end_procrastination _ : Type);
      [ mk_exists n ltac:(fun l => mk_app P1 l Prop)
      | mk_exists n ltac:(fun l => mk_app P2 l Prop) ]
   )
  | simpl in G].

Local Ltac mk_end_procrastination_helper_Type n G :=
  mk_end_procrastination_helper_aux n G
    ltac:(fun n cont => mk_sigT_sig n Type cont).

Local Ltac mk_end_procrastination_helper_Prop n G :=
  mk_end_procrastination_helper_aux n G
    ltac:(fun n cont => mk_exists n Prop cont).

Ltac mk_end_procrastination_helper n :=
  let H := fresh in
  match goal with |- Marker.end_procrastination ?G =>
    match type of G with
    | Prop => mk_end_procrastination_helper_Prop n H
    | _ => mk_end_procrastination_helper_Type n H
    end;
    cut H; subst H; [| prove_end_procrastination_helper ]
  end.

Goal Marker.end_procrastination nat. mk_end_procrastination_helper 3.
Abort.

Goal Marker.end_procrastination True. mk_end_procrastination_helper 3.
Abort.

End MkHelperLemmas.

(******************************************************************************)

(** [begin procrastination] *)

Ltac begin_procrastination_core g n intros_tac :=
  MkHelperLemmas.mk_begin_procrastination_helper n;
  let H := fresh in
  intro H; eapply H; clear H;
  [ intros_tac tt; intro g | ].

Tactic Notation "begin" "procrastination" :=
  let g := fresh "g" in
  begin_procrastination_core g 0 ltac:(fun tt => idtac).

Tactic Notation "begin" "procrastination"
       "group" ident(g) :=
  begin_procrastination_core g 0 ltac:(fun tt => idtac).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) :=
  let g := fresh "g" in
  begin_procrastination_core g 1 ltac:(fun tt => intros a).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) :=
  begin_procrastination_core g 1 ltac:(fun tt => intros a).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) :=
  let g := fresh "g" in
  begin_procrastination_core g 2 ltac:(fun tt => intros a b).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) :=
  begin_procrastination_core g 2 ltac:(fun tt => intros a b).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) ident(c) :=
  let g := fresh "g" in
  begin_procrastination_core g 3 ltac:(fun tt => intros a b c).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) :=
  begin_procrastination_core g 3 ltac:(fun tt => intros a b c).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  let g := fresh "g" in
  begin_procrastination_core g 4 ltac:(fun tt => intros a b c d).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  begin_procrastination_core g 4 ltac:(fun tt => intros a b c d).

Goal True.
  begin procrastination group foo assuming a b.
Abort.

(** [procrastinate] *)

Local Ltac procrastinate_aux tm ty :=
  let ty' := (eval simpl in ty) in
  lazymatch ty' with
  | and ?x ?y => procrastinate_aux (@proj2 x y tm) y
  | _ => eapply (proj1 tm)
  end.

Ltac procrastinate_core group :=
  let ty := type of group in
  let ty' := (eval unfold Marker.group in ty) in
  procrastinate_aux group ty'.

Tactic Notation "procrastinate" :=
  let g := Marker.find_group in
  procrastinate_core g.

Tactic Notation "procrastinate" ident(g) :=
  procrastinate_core g.

Goal True.
  begin procrastination group foo.
  begin procrastination group bar.
  assert (1 = 1) by procrastinate. (* goes in group [bar] *)
  assert (2 = 2) by (procrastinate foo).
Abort.

(** [with procrastination] *)

Local Ltac with_procrastination_aux tm ty tac :=
  lazymatch ty with
  | and ?x ?y =>
    tac (@proj1 x y tm);
    tryif is_evar y then idtac
    else with_procrastination_aux (@proj2 x y tm) y tac
  end.

Ltac with_procrastination_core g tac :=
  let ty := type of g in
  let ty' := (eval unfold Marker.group in ty) in
  with_procrastination_aux g ty' tac.

Tactic Notation "with" "procrastination"
       "do" tactic(tac) :=
  let g := Marker.find_group in
  with_procrastination_core g tac.

Tactic Notation "with" "procrastination"
       "group" ident(g)
       "do" tactic(tac) :=
  with_procrastination_core g tac.

Goal True.
  begin procrastination group foo.
  assert (1 + 1 = 2) by procrastinate.
  assert (L: forall n, n + 0 = n) by procrastinate.
  clear L.
  assert (3 + 0 = 3).
  { with procrastination group foo do (fun H => try apply H). }
Abort.

(** [already procrastinated] *)

Ltac already_procrastinated_core g :=
  solve [ with procrastination group g do (fun H => try apply H) ].

Tactic Notation "already" "procrastinated" :=
  let g := Marker.find_group in
  already_procrastinated_core g.

Tactic Notation "already" "procrastinated" ident(g) :=
  already_procrastinated_core g.

(** [end procrastination] *)

Local Ltac introv_rec :=
  lazymatch goal with
  | |- (?P -> ?Q) => idtac
  | |- (forall _, _) => intro; introv_rec
  | |- _ => idtac
  end.

(* (A /\ B /\ C /\ D) -> (A /\ B /\ C) *)
Local Ltac ands_remove_last ty :=
  lazymatch ty with
  | and ?x ?y =>
    lazymatch y with
    | and _ _ =>
      let y' := ands_remove_last y in
      constr:(and x y')
    | _ => constr:(x)
    end
  end.

Local Ltac cleanup_conj_goal_aux tm ty :=
  lazymatch ty with
  | and ?x ?y =>
    split; [apply (@proj1 x y tm) | cleanup_conj_goal_aux (@proj2 x y tm) y]
  | ?x => split; [apply tm | exact I]
  end.

Local Ltac cleanup_conj_goal_core :=
  let H_P_clean := fresh "H_P_clean" in
  intro H_P_clean;
  match goal with
  | |- ?P_to_clean =>
    let P_clean := ands_remove_last P_to_clean in
    cleanup_conj_goal_aux H_P_clean P_clean
  end.

Local Ltac count_exists t k :=
  let t := eval hnf in t in
  lazymatch t with
  | @ex ?A ?P => count_exists_aux t k A P
  | @sig ?A ?P => count_exists_aux t k A P
  | @sigT ?A ?P => count_exists_aux t k A P
  | _ => k O
  end

with count_exists_aux t k A P :=
  let x := fresh in
  evar (x : A);
  count_exists (P x) ltac:(fun res => k (S res));
  clear x.

Goal exists a b c, a + b = c.
  match goal with |- ?g => count_exists g ltac:(fun res => pose res) end.
Abort.

Ltac end_procrastination_core :=
  match goal with
  |- Marker.end_procrastination ?g =>
    count_exists g ltac:(fun n =>
      MkHelperLemmas.mk_end_procrastination_helper n;
      let H := fresh in
      intro H; eapply H; clear H;
      [ introv_rec; cleanup_conj_goal_core | hnf ]
    )
  end.

Tactic Notation "end" "procrastination" :=
  end_procrastination_core.

Goal True.
  begin procrastination group g.

  assert (H1 : 1 + 1 = 2) by (procrastinate g).
  assert (H2 : 1 + 2 = 3) by (procrastinate g).
  assert (H3 : 1 + 3 = 4) by (procrastinate g).

  tauto.
  end procrastination.

  repeat split; reflexivity.
Qed.

Goal True.
  begin procrastination assuming a b c.
  assert (a + b = c) by procrastinate. simpl in g.
  exact I.

  end procrastination.
Abort.

(******************************************************************************)

(** Notations for markers *)

Notation "'end'  'procrastination'" :=
  (Marker.end_procrastination _) (at level 0).

Notation "'Group'  P" :=
  (Marker.group P) (at level 0).
