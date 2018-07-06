# Tactics Reference

- `begin defer [assuming a b...] [in g]`

  Start a "defer" block. If `group g` is provided, give name `g` to
  the hypothesis of type `Group` introduced. If `assuming a b...` (where `a`,
  `b`, ... are one or several user-provided names) is provided, also introduce
  in the context abstract variables of the same names.

- `defer [in g]`

  Discharge the current sub-goal, deferring it for later. If `in g` is
  provided, store it in the hypothesis `g` which must be of type `Group ...`. If
  `in g` is not provided, the tactic picks the hypothesis of type `Group ...`
  which has been introduced last (if there are several).

  The sub-goal being differed has to make sense in the context of the `Group` it
  is stored in (which is the context of the `begin defer` that introduced the
  `Group`). Otherwise Coq will raise an error involving the context of the evar
  in the `Group`.

- `defer [H]: E [in g]`

  Introduces a new assumption `E`, named after `H`, and defer its proof in `g`.
  This is equivalent to `assert E as H by (defer in g)`.

  If `H` is not provided, adds `E` in front of the goal instead of adding it to
  the context -- i.e. on a goal `G`, `defer: E` produces a goal `E -> G`.

- `end defer`

  To be called on a `end defer` goal. It does some cleanup and gives back the
  variables and side-goals that have been procrastinated.

- `deferred [in g]`

  Tries to prove the goal using an already deferred proposition. If it fails,
  adds all already deferred propositions to the context.

- `deferred [H]: E [in g]`

  Adds an assumption `E` to the context, named after `H`, and tries to prove it
  using an already deferred proposition. If this fails, gives back a subgoal `X1
  -> .. -> Xn -> E`, where `X1`...`Xn` are the already deferred propositions.

  If `H` is not provided, adds `E` in front of the goal instead of adding it to
  the context.

- `exploit deferred tac [in g]`

  Calls the tactic [tac] on each proposition stored in group [g]. [tac] is
  allowed to fail, but the whole tactic fails if no progress has been made.
