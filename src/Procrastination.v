(******************************************************************************)
(* Summary of the tactics exported by this file:                              *)
(*                                                                            *)
(* begin procrastination [group g] [assuming a b...]                          *)
(* procrastinate [group g]                                                    *)
(* procrastinate [intropat] : H [group g]                                     *)
(* end procrastination                                                        *)
(* already procrastinated [group g]                                           *)
(* already procrastinated [intropat] : H [group g]                            *)
(* with procrastinated [group g] [do cont]                                    *)
(*                                                                            *)
(* + variants replacing "procrastinate" with "defer", "procrastination" with  *)
(*   "deferring" and "procrastinated" with "deferred".                        *)
(******************************************************************************)

(* The comments below describe the various tricks used for implementing the
   library. For a higher-level description of what it does, and how to use it,
   one should rather refer to the manual in `manual/manual.pdf`, and the
   `examples/` directory. For a reference of the tactics, see
   `TacticsReference.md`.
*)

(* We define a couple "marker" definitions. These are equivalent to the
   identity, but are useful to mark subterms to be used with tactics or
   notation. *)
Module Marker.

(* This marker is used in combination with a notation (see the end of the file),
   in order to hide the exact expression of a subgoal, and to indicate that
   faced with this subgoal, the user always has to call the
   [end procrastination] tactic. *)
Definition end_procrastination (P : Type) := P.
Definition end_deferring (P : Type) := P.

(* This is used for pretty-printing purposes, in order to rewrite a "end
   procrastination" marker into a "end deferring" marker (which is
   pretty-printed differently) if the user is using the "defer" aliases... *)
Lemma end_procrastination_eq_end_deferring : forall P,
  end_procrastination P = end_deferring P.
Proof. reflexivity. Qed.

(* This marker is used to keep track of "group" assumptions in the context
   (introduced by [begin procrastination]). This is useful so that tactics can
   omit specifying a group: in that case, the first group of the context is
   used. *)
Definition group (P : Prop) := P.

Ltac find_group :=
  match goal with
  | H : group _ |- _ => constr:(H)
  end.

End Marker.


(* A very simple implementation of [begin procrastination] could be as follows:

   ```
   Lemma L0 : forall Goal group,
     (group -> Goal) ->
     group ->
     Goal.

   Ltac begin_procrastination := eapply L0.
   ```

   By using [eapply L0], [group] is introduced as an evar. Then, in the first
   subgoal [group -> Goal], [procrastinate] can be used to discharge
   propositions to procrastinate, by raffining the [group] evar (which is of
   type [Prop]). Then, in the second subgoal, one has to prove the propositions
   collected in [group].


   Similarly, [begin procrastination assuming a] could be implemented as:

   ```
   Lemma L1 : forall A Goal (group : A -> Prop),
     (forall a, group a -> Goal) ->
     (exists a, group a) ->
     Goal.

   Ltac begin_procrastination_assuming_1 := eapply L1
   ```

   This allows us to procrastinate propositions that depend on some parameter
   [a] of type [A]. However we would like to have this for an arbitrary number
   of parameters. This is the purpose of the tactics in the module below.


   More precisely, the tactics below take an arity as parameter, and build the
   statement of a lemma (similar to L0 or L1) for that arity. To achieve that
   using Ltac, we do not try to construct the term corresponding to the lemma's
   statement directly (this is not supported by Ltac). Instead, what we can do
   is produce a subgoal (of type [Prop]) corresponding to the statement of the
   lemma, and construct the statement using successive applications of the
   [refine] tactic.

   The same set of tricks is used to implement [end procrastination], which
   requires generating a "clean-up" lemma, whose statement depends on the number
   of "exists" introduced by [begin procrastination].

   We start by defining some utility tactics, that help building bits of the
   statements when following this methodology.
*)
Module MkHelperLemmas.

(* General helpers *)

(* [transparent_assert name type] produces a new subgoal of type [type], whose
   *proof term* will appear as a definition in the context of the main subgoal.

   Here, [type] will be [Prop] or [Type], and the first subgoal will be proved
   using multiple [refine], thus constructing the desired lemma statement.
*)
Ltac transparent_assert name type :=
  unshelve refine (let name := _ : type in _).

(* This is generally useful in tactics to have lists of things (e.g.
   assumptions) of heterogeneous types, by "boxing" them using [boxer]. *)
Inductive Boxer :=
| boxer : forall A : Type, A -> Boxer.
Arguments boxer : clear implicits.

(* It is useful for user-friendliness to carry around the user-provided names
   (given with ...assuming a b c). However, Ltac does not have proper
   data-structures that could be used to carry around a list of identifiers.

  We use the following trick as a workaround: given identifiers a, b, c, one can
  craft the following coq term: (fun a b c : unit => tt). Amusingly, this will
  be pretty-printed by coq as (fun _ _ _ => tt), but the information about the
  user names is still kept around. Then, one can match on this coq term to
  recover the names:

  match constr:(fun a b c : unit => tt) with
  | (fun x => _) =>
    idtac x
  end

  will print 'a', for example. Then one can apply a
  "list-of-identifiers-as-a-coq-term" to tt to get its tail, while the base case
  is having tt.
*)

(* Computes the number of identifiers, ie the "length of the list" *)
Ltac ids_nb ids :=
  lazymatch ids with
  | tt => constr:(O)
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let n := ids_nb ids' in
    constr:(S n)
  end.

Ltac iter_idents ids tac :=
  lazymatch ids with
  | tt => idtac
  | (fun x => _) =>
    tac x;
    iter_idents ltac:(eval cbv beta in (ids tt)) tac
  end.

(* For debugging purposes *)
Ltac print_ids ids :=
  lazymatch ids with
  | tt => idtac
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    idtac x;
    print_ids ids'
  end.


(* [mk_forall varty goalty n cont], called on a goal of type [goalty] (e.g.
   [Type] or [Prop]), refines its proof term to be [forall x_1 ... x_n, _],
   where all [x_i] have type [varty].

   The continuation [cont] is then called, with as argument the list of variable
   names introduced, i.e. the list of (boxed) [x_i].
*)
Ltac mk_forall varty goalty n cont :=
  lazymatch n with
  | O => cont (@nil Boxer)
  | S ?n' =>
    let X := fresh in
    refine (forall (X : varty), _ : goalty);
    mk_forall varty goalty n' ltac:(fun x => cont (cons (boxer varty X) x))
  end.

(* [mk_forall_tys vartys goalty cont] is similar to [mk_forall], but the
   variables introduced can now have different types, as specified by the list
   [vartys].
*)
Ltac mk_forall_tys vartys goalty cont :=
  lazymatch vartys with
  | nil => cont (@nil Boxer)
  | cons (boxer _ ?ty) ?tys =>
    let X := fresh in
    refine (forall (X : ty), _ : goalty);
    mk_forall_tys tys goalty ltac:(fun x => cont (cons (boxer ty X) x))
  end.

(* [mk_arrow vars goalty] refines the proof term to be [x_1 -> .. -> x_n -> _],
   where [vars] is [[x_1; ..; x_n]]. *)
Ltac mk_arrow vars goalty :=
  lazymatch vars with
  | nil => idtac
  | cons (boxer _ ?v) ?vs =>
    refine (v -> _ : goalty);
    mk_arrow vs goalty
  end.

(* [mk_app f vars goalty] refines the proof term to be [f x_1 .. x_2], where
   [vars] is [[x_1; ..; x_n]]. *)
Ltac mk_app f vars goalty :=
  lazymatch vars with
  | nil => exact f
  | cons (boxer _ ?v) ?vs =>
    refine (_ v : goalty);
    let x := fresh "x" in intro x;
    mk_app (f x) vs goalty
  end.

(* [mk_sigT_sig ids goalty cont] refines the proof term to be [sigT (fun x_1 => ..
   sigT (fun x_n-1 => sig (fun x_n => _)))], then calls [cont] with the list of
   variables introduced [[x_1; .. x_n]]. *)
Ltac mk_sigT_sig ids goalty cont :=
  lazymatch ids with
  | tt => cont (@nil Boxer)
  | (fun x => tt) =>
    let X := fresh x in
    refine (sig (fun X => _) : goalty);
    cont (cons (@boxer _ X) (@nil Boxer))
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let X := fresh x in
    refine (sigT (fun X => _) : goalty);
    mk_sigT_sig ids' goalty ltac:(fun x => cont (cons (@boxer _ X) x))
  end.

(* Similarly, [mk_exists ids goalty cont] refines the proof term to be [exists x_1
   .. x_n, _], and calls [cont] with the list [[x_1; ..; x_n]]. *)
Ltac mk_exists ids goalty cont :=
  lazymatch ids with
  | tt => cont (@nil Boxer)
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let X := fresh x in
    refine (exists X, _ : goalty);
    mk_exists ids' goalty ltac:(fun x => cont (cons (@boxer _ X) x))
  end.

Ltac introsType :=
  repeat (
      match goal with
      | |- forall (_ : Type), _ =>
        intro
      end
    ).

(* [begin procrastination] helpers *)

(* This tactic is able to prove the statements of helper lemmas for [begin
   procrastination], for any arity. *)
Ltac prove_begin_procrastination_helper :=
  introsType;
  let H := fresh in
  intros ? ? ? H;
  unfold Marker.end_procrastination in *;
  repeat (let x := fresh "x" in destruct H as (x & H));
  eauto.

(* Tests for the tactic above. *)
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

(* Tactic that generates lemma statements as [begin procrastination] helpers.

   Generates a definition G := ... . G then corresponds to a statement that can
   be proved using [prove_begin_procrastination_helper], and is of the form:

   ```
   forall
     (A B .. Z : Type)
     (facts : A -> B -> .. -> Z -> Prop)
     (P: Prop),
   (forall a b .. z, Marker.group (facts a b .. z) -> P) ->
   end_procrastination (exists a b .. z, facts a b .. z) ->
   P.
   ```

   The type of P is actually taken as a parameter Pty (in practice, Prop or
   Type), and the last hypothesis is produced by the argument tactic
   [mk_exists].

   When P is of type Prop, the last hypothesis is as shown, and uses exists.
   When P is of type Type, the last hypothesis is instead of the form
     sigT (fun a => sigT (fun b => ... sig (fun z => facts_closed a b .. z)))
*)
Ltac mk_begin_procrastination_helper_aux n G Pty mk_exists :=
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

Ltac mk_begin_procrastination_helper_Type ids G :=
  let n := ids_nb ids in
  mk_begin_procrastination_helper_aux n G Type
    ltac:(fun n cont => mk_sigT_sig ids Type cont).

Ltac mk_begin_procrastination_helper_Prop ids G :=
  let n := ids_nb ids in
  mk_begin_procrastination_helper_aux n G Prop
    ltac:(fun n cont => mk_exists ids Prop cont).

(* When the goal is of type [Type], generate a statement using constructive
   exists. When it is of type [Prop], use regular exists. *)
Ltac mk_begin_procrastination_helper ids :=
  let H := fresh in
  match goal with |- ?G =>
    match type of G with
    | Prop => mk_begin_procrastination_helper_Prop ids H
    | _ => mk_begin_procrastination_helper_Type ids H
    end;
    cut H; subst H; [| prove_begin_procrastination_helper]
  end.

(* Tests *)
Goal True.
  mk_begin_procrastination_helper tt.
  intro H; eapply H; clear H.
Abort.

Goal True.
  mk_begin_procrastination_helper (fun a b c : unit => tt).
  intro H; eapply H; clear H.
Abort.

Goal nat.
  mk_begin_procrastination_helper (fun a b c : unit => tt).
  intro H; eapply H; clear H.
Abort.

(* [end procrastination] helpers.

   [end procrastination] is called on the second subgoal produced by [begin
   procrastination], of the form [exists a .. z, group a .. z], where [group a
   .. z] has been instantiated by [procrastinate] into something of the form [P1
   /\ P2 /\ ... /\ Pn /\ ?P], where P1 .. Pn are the propositions that have been
   procrastinated, and [?P] is the "accumulator" evar.

   The role of [end procrastination] is to close the goal, instantiating [?P]
   with [True], and removing it from the goal.

   This is done by first applying a lemma of the form:

   ```
   forall A .. Z (G1 G2 : A -> .. -> Z -> Prop),
   (forall a .. z, G1 a .. z -> G2 a .. z) ->
   (exists a .. z, G1 a .. z) ->
   exists a .. z, G2 a .. z
   ```

   After applying this lemma, [G2] is unified with the current goal (to clean),
   and [G1] is introduced as an evar. An auxiliary tactic
   ([cleanup_conj_goal_core], defined below) is called on the first subgoal, and
   will discharge it, instantiating [G1] with the cleaned-up goal (i.e [P1 /\ P2
   /\ ... /\ Pn]).

   The helpers below help generating and proving this lemma, for any number of
   variables [a] .. [z].
*)

(* Tactic that proves the lemma above for any arity. *)
Ltac prove_end_procrastination_helper :=
  introsType;
  let P1 := fresh in
  let P2 := fresh in
  let H1 := fresh in
  let H2 := fresh in
  intros P1 P2 H1 H2;
  unfold Marker.end_procrastination in *;
  repeat (let x := fresh "x" in destruct H2 as (x & H2); exists x);
  apply H1; auto.

(* Tests. *)
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

(* Generates a definition G := ... . G then corresponds to a statement that can
   be proved using [prove_begin_procrastination_helper], and is of the form
   detailed above.

   [mk_exists] is used to refine the nested "exists", allowing the tactic to
   produce statements using either exists in [Prop] ([exists]) or [Type]
   ([sig]/[sigT]).
 *)
Ltac mk_end_procrastination_helper_aux n G mk_exists :=
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

Ltac mk_end_procrastination_helper_Type ids G :=
  let n := ids_nb ids in
  mk_end_procrastination_helper_aux n G
    ltac:(fun n cont => mk_sigT_sig ids Type cont).

Ltac mk_end_procrastination_helper_Prop ids G :=
  let n := ids_nb ids in
  mk_end_procrastination_helper_aux n G
    ltac:(fun n cont => mk_exists ids Prop cont).

(* Dispatch [mk_exists] depending on the type of the goal *)
Ltac mk_end_procrastination_helper ids :=
  let H := fresh in
  match goal with |- Marker.end_procrastination ?G =>
    match type of G with
    | Prop => mk_end_procrastination_helper_Prop ids H
    | _ => mk_end_procrastination_helper_Type ids H
    end;
    cut H; subst H; [| prove_end_procrastination_helper ]
  end.

Goal Marker.end_procrastination nat.
  mk_end_procrastination_helper (fun x y z : unit => tt).
  intros.
Abort.

Goal Marker.end_procrastination True.
  mk_end_procrastination_helper (fun x y z : unit => tt).
Abort.

End MkHelperLemmas.

(******************************************************************************)

(* [begin procrastination [group g] [assuming a b...]]

   If [group g] is not specified, a fresh named is used.
*)

Ltac specialize_helper_types H ids :=
  MkHelperLemmas.iter_idents ids ltac:(fun _ =>
    let e := fresh in
    evar (e : Type);
    specialize (H e);
    subst e
  ).

Ltac mkrefine_group ids :=
  lazymatch ids with
  | tt => uconstr:(_)
  | (fun x => _) =>
    let ids' := eval cbv beta in (ids tt) in
    let ret := mkrefine_group ids' in
    uconstr:(fun x => ret)
  end.

Ltac specialize_helper_group H ids :=
  let group_uconstr := mkrefine_group ids in
  let g := fresh in
  refine (let g := group_uconstr in _);
  specialize (H g);
  subst g.

Ltac begin_procrastination_core g ids :=
  MkHelperLemmas.mk_begin_procrastination_helper ids;
  let H := fresh in
  intro H;
  specialize_helper_types H ids;
  specialize_helper_group H ids;
  eapply H; clear H;
  [ MkHelperLemmas.iter_idents ids ltac:(fun x => intro x); intro g |].

(* Unfortunately, despite the fact that our core tactic
   [begin_procrastination_core] works for any arity, we have no choice but
   manually exporting it for a given set of arities, as Ltac doesn't expose any
   way of manipulating lists of identifiers.

   See e.g. https://github.com/coq/coq/pull/6081
*)

Tactic Notation "begin" "procrastination" :=
  let g := fresh "g" in
  begin_procrastination_core g tt.

Tactic Notation "begin" "procrastination"
       "group" ident(g) :=
  begin_procrastination_core g tt.

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a : unit => tt).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) :=
  begin_procrastination_core g (fun a : unit => tt).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b : unit => tt).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) :=
  begin_procrastination_core g (fun a b : unit => tt).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) ident(c) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b c : unit => tt).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) :=
  begin_procrastination_core g (fun a b c : unit => tt).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b c d : unit => tt).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  begin_procrastination_core g (fun a b c d : unit => tt).

Tactic Notation "begin" "procrastination"
       "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b c d e : unit => tt).

Tactic Notation "begin" "procrastination"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  begin_procrastination_core g (fun a b c d e : unit => tt).

(** "Defer" variants *)

Tactic Notation "begin" "deferring" :=
  let g := fresh "g" in
  begin_procrastination_core g ltac:(fun tt => idtac);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "group" ident(g) :=
  begin_procrastination_core g ltac:(fun tt => idtac);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "assuming" ident(a) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "group" ident(g)
       "assuming" ident(a) :=
  begin_procrastination_core g (fun a : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "assuming" ident(a) ident(b) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "group" ident(g)
       "assuming" ident(a) ident(b) :=
  begin_procrastination_core g (fun a b : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "assuming" ident(a) ident(b) ident(c) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b c : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) :=
  begin_procrastination_core g (fun a b c : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b c d : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) ident(d) :=
  begin_procrastination_core g (fun a b c d : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  let g := fresh "g" in
  begin_procrastination_core g (fun a b c d e : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

Tactic Notation "begin" "deferring"
       "group" ident(g)
       "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  begin_procrastination_core g (fun a b c d e : unit => tt);
  [| rewrite Marker.end_procrastination_eq_end_deferring ].

(* Test *)
Goal True.
  begin procrastination group foo assuming a b.
Abort.

Goal nat.
  begin procrastination group foo assuming a b.
Abort.

Goal True.
  begin deferring group foo assuming a b.
Abort.

(* [procrastinate [group g]]

   If the name of the group [g] is not specified, the group that has been
   introduced last is used.

   Also defines the [procrastinate [X]: H [group g]] helper tactic, which
   asserts [H] (with optional name [X]) and procrastinates its proof in group
   [g].
*)

(* After unfolding markers, a group is a variable [g] in the context, of type of
   the form [P1 /\ ... /\ Pk /\ ?P], where [P1 ... Pk] are the propositions that
   have been previously procrastinated.

   What [procrastinate] does is instantiating [?P] with [G /\ ?P'], where [G] is
   the current goal, and [?P'] a newly introduced evar. The group now entails
   the current goal, which [procrastinate] proves -- effectively delaying its
   proof.
*)
Ltac procrastinate_aux tm ty :=
  let ty' := (eval simpl in ty) in
  lazymatch ty' with
  | and ?x ?y => procrastinate_aux (@proj2 x y tm) y
  | _ => eapply (proj1 tm)
  end.

Ltac procrastinate_core group :=
  let ty := type of group in
  let ty' := (eval unfold Marker.group in ty) in
  procrastinate_aux group ty'.

Tactic Notation "procrastinate" "group" ident(g) :=
  procrastinate_core g.

Tactic Notation "procrastinate" :=
  let g := Marker.find_group in
  procrastinate group g.

Tactic Notation "procrastinate" simple_intropattern(i) ":" uconstr(H) "group" ident(g) :=
  assert H as i by procrastinate_core g.

Tactic Notation "procrastinate" ":" uconstr(H) "group" ident(g) :=
  assert H by procrastinate_core g.

Tactic Notation "procrastinate" simple_intropattern(i) ":" uconstr(H) :=
  let g := Marker.find_group in
  procrastinate i : H group g.

Tactic Notation "procrastinate" ":" uconstr(H) :=
  let g := Marker.find_group in
  procrastinate: H group g.

(** "Defer" variants *)

Tactic Notation "defer" "group" ident(g) :=
  procrastinate_core g.

Tactic Notation "defer" :=
  let g := Marker.find_group in
  procrastinate group g.

Tactic Notation "defer" simple_intropattern(i) ":" uconstr(H) "group" ident(g) :=
  assert H as i by procrastinate_core g.

Tactic Notation "defer" ":" uconstr(H) "group" ident(g) :=
  assert H by procrastinate_core g.

Tactic Notation "defer" simple_intropattern(i) ":" uconstr(H) :=
  let g := Marker.find_group in
  procrastinate i : H group g.

Tactic Notation "defer" ":" uconstr(H) :=
  let g := Marker.find_group in
  procrastinate: H group g.

(* Test *)
Goal True.
  begin procrastination group foo.
  begin procrastination group bar.
  assert (1 = 1) by procrastinate. (* goes in group [bar] *)
  procrastinate: (2 = 2). (* same result *)
  procrastinate E: (3 = 3). (* same result, allows naming the hypothesis *)
  assert (4 = 4) by (procrastinate group foo). (* goes in group [foo] *)
  procrastinate [E1 E2]: (5 = 5 /\ 6 = 6) group foo. (* same result *)
Abort.

(* [with procrastinated [group g] [do tac]]

   If [group g] is omitted, the group that has been introduced last is used.

   If [do tac] is omitted, adds to the context all propositions that have been
   procrastinated so far.

   When [do tac] is provided, with [tac] a valid tactic, calls [tac] on each
   proposition stored in group [g].
*)

Ltac with_procrastinated_aux tm ty tac :=
  lazymatch ty with
  | and ?x ?y =>
    tac (@proj1 x y tm);
    tryif is_evar y then idtac
    else with_procrastinated_aux (@proj2 x y tm) y tac
  end.

Ltac with_procrastinated_core g tac :=
  let ty := type of g in
  let ty' := (eval unfold Marker.group in ty) in
  with_procrastinated_aux g ty' tac.

Tactic Notation "with" "procrastinated"
       "do" tactic(tac) :=
  let g := Marker.find_group in
  with_procrastinated_core g tac.

Tactic Notation "with" "procrastinated"
       "group" ident(g)
       "do" tactic(tac) :=
  with_procrastinated_core g tac.

Tactic Notation "with" "procrastinated" :=
  let g := Marker.find_group in
  with_procrastinated_core g ltac:(fun t => pose proof t).

Tactic Notation "with" "procrastinated"
       "group" ident(g) :=
  let g := Marker.find_group in
  with_procrastinated_core g ltac:(fun t => pose proof t).

(** "Defer" variants *)

Tactic Notation "with" "deferred"
       "do" tactic(tac) :=
  let g := Marker.find_group in
  with_procrastinated_core g tac.

Tactic Notation "with" "deferred"
       "group" ident(g)
       "do" tactic(tac) :=
  with_procrastinated_core g tac.

Tactic Notation "with" "deferred" :=
  let g := Marker.find_group in
  with_procrastinated_core g ltac:(fun t => pose proof t).

Tactic Notation "with" "deferred"
       "group" ident(g) :=
  let g := Marker.find_group in
  with_procrastinated_core g ltac:(fun t => pose proof t).

(* Test *)
Goal True.
  begin procrastination group foo.
  assert (1 + 1 = 2) by procrastinate.
  assert (L: forall n, n + 0 = n) by procrastinate.
  clear L.
  assert (3 + 0 = 3).
  { with procrastinated group foo do (fun H => try apply H). }
Abort.

(* [already procrastinated [group g]]

   If [g] is omitted, picks the group that has been introduced last.

   Tries to apply one of the propositions collected in [g] to the goal.


   Also defines the [already procrastinated [X]: H [group g]] helper tactic,
   which asserts [H] (with optional name [X]) and proves it using [already
   procrastinated].
*)

Ltac already_procrastinated_core g :=
  progress (with procrastinated group g do (fun H => try (apply H))).

Tactic Notation "already" "procrastinated" "group" ident(g) :=
  already_procrastinated_core g.

Tactic Notation "already" "procrastinated" :=
  let g := Marker.find_group in
  already procrastinated group g.

Tactic Notation "already" "procrastinated" simple_intropattern(i) ":" uconstr(H) "group" ident(g) :=
  assert H as i by already procrastinated group g.

Tactic Notation "already" "procrastinated" ":" uconstr(H) "group" ident(g) :=
  assert H by already procrastinated group g.

Tactic Notation "already" "procrastinated" simple_intropattern(i) ":" uconstr(H) :=
  let g := Marker.find_group in
  already procrastinated i : H group g.

Tactic Notation "already" "procrastinated" ":" uconstr(H) :=
  let g := Marker.find_group in
  already procrastinated : H group g.

(** "Defer" variants *)

Tactic Notation "already" "deferred" "group" ident(g) :=
  already_procrastinated_core g.

Tactic Notation "already" "deferred" :=
  let g := Marker.find_group in
  already procrastinated group g.

Tactic Notation "already" "deferred" simple_intropattern(i) ":" uconstr(H) "group" ident(g) :=
  assert H as i by already procrastinated group g.

Tactic Notation "already" "deferred" ":" uconstr(H) "group" ident(g) :=
  assert H by already procrastinated group g.

Tactic Notation "already" "deferred" simple_intropattern(i) ":" uconstr(H) :=
  let g := Marker.find_group in
  already procrastinated i : H group g.

Tactic Notation "already" "deferred" ":" uconstr(H) :=
  let g := Marker.find_group in
  already procrastinated : H group g.


(* [end procrastination] *)

Ltac introv_rec :=
  lazymatch goal with
  | |- (?P -> ?Q) => idtac
  | |- (forall _, _) => intro; introv_rec
  | |- _ => idtac
  end.

(* (A /\ B /\ C /\ D) -> (A /\ B /\ C) *)
Ltac ands_remove_last ty :=
  lazymatch ty with
  | and ?x ?y =>
    lazymatch y with
    | and _ _ =>
      let y' := ands_remove_last y in
      constr:(and x y')
    | _ => constr:(x)
    end
  end.

Ltac cleanup_conj_goal_aux tm ty :=
  lazymatch ty with
  | and ?x ?y =>
    split; [apply (@proj1 x y tm) | cleanup_conj_goal_aux (@proj2 x y tm) y]
  | ?x => split; [apply tm | exact I]
  end.

(* Expose this tactic as it may be useful for procrastination-like setups *)
Ltac cleanup_conj_goal_core :=
  let H_P_clean := fresh "H_P_clean" in
  intro H_P_clean;
  match goal with
  | |- ?P_to_clean =>
    let P_clean := ands_remove_last P_to_clean in
    cleanup_conj_goal_aux H_P_clean P_clean
  end.

(* A tactic to collect the names of the "exists" in from of the goal. This is
   using the neat trick provided in the comment section of
   http://gallium.inria.fr/blog/how-to-quantify-quantifiers-an-ltac-puzzle/ (!)
   which is apparently inspired by Adam Chlipala's book. *)

Ltac collect_exists_ids_loop G ids :=
  lazymatch G with
  | (fun g => exists x, @?body g x) =>
    let G' := constr:(fun (z : _ * _) => body (fst z) (snd z)) in
    let G' := eval cbn beta in G' in
    let ids' := collect_exists_ids_loop G' ids in
    constr:(fun (x : unit) => ids')
  | _ => constr:(ids)
  end.

Ltac collect_exists_ids g :=
  collect_exists_ids_loop (fun (_:unit) => g) tt.

(* Test for [collect_exists_ids] *)
Goal Marker.end_procrastination (exists a b c, a + b = c).
  match goal with |- Marker.end_procrastination ?g =>
    let ids := collect_exists_ids g in
    (* MkHelperLemmas.print_ids ids *) (* prints: a b c *)
    idtac
  end.
Abort.

Ltac end_procrastination_core :=
  match goal with
  |- Marker.end_procrastination ?g =>
    let ids := collect_exists_ids g in
    MkHelperLemmas.mk_end_procrastination_helper ids;
    let H := fresh in
    intro H; eapply H; clear H;
    [ introv_rec; cleanup_conj_goal_core | hnf ]
  end.

Tactic Notation "end" "procrastination" :=
  end_procrastination_core.

Tactic Notation "end" "deferring" :=
  rewrite <-Marker.end_procrastination_eq_end_deferring;
  end_procrastination_core.

(* Tests *)
Goal True.
  begin procrastination group g.

  assert (H1 : 1 + 1 = 2) by (procrastinate group g).
  assert (H2 : 1 + 2 = 3) by (procrastinate group g).
  procrastinate H3: (1 + 3 = 4) group g.

  tauto.
  end procrastination.

  repeat split; reflexivity.
Qed.

Goal True.
  begin procrastination assuming a b c.
  assert (a + b = c). procrastinate. simpl in g.
  exact I.

  end procrastination.
Abort.

(******************************************************************************)

(* Notation for markers *)

(* We print this marker as [end procrastination], to informally indicate to the
   user that such a goal should always be treated by calling the [end
   procrastination] tactic. *)
Notation "'end'  'procrastination'" :=
  (Marker.end_procrastination _) (at level 0).

Notation "'end'  'deferring'" :=
  (Marker.end_deferring _) (at level 0).

Notation "'Group'  P" :=
  (Marker.group P) (at level 0).
