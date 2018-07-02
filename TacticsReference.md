# Tactics Reference

- `begin procrastination [group g] [assuming a b...]`

  Start a "procrastination" block. If `group g` is provided, give name `g` to
  the hypothesis of type `Group` introduced. If `assuming a b...` (where `a`,
  `b`, ... are one or several user-provided names) is provided, also introduce
  in the context abstract variables of the same names.

- `procrastinate [group g]`

  Discharge the current sub-goal, deferring it for later. If `group g` is
  provided, store it in the hypothesis `g` which must be of type `Group ...`. If
  `group g` is not provided, the tactic picks the hypothesis of type `Group ...`
  which has been introduced last (if there are several).

  The sub-goal being differed has to make sense in the context of the `Group` it
  is stored in (which is the context of the `begin procrastination` that
  introduced the `Group`). Otherwise Coq will raise an error involving the
  context of the evar in the `Group`.

- `procrastinate [intropat] : H [group g]`

  `procrastinate name: H group g` is a shorthand for `assert (name: H) by
  (procrastination group g)`.

  In other words, it adds an hypothesis of type `H` to the context, and defers
  it proof. `group g` is optional, with the same behavior as `procrastinate`.

- `end procrastination`

  To be called on a `end procrastination` goal. It does some cleanup and gives
  back the variables and side-goals that have been procrastinated.

- `already procrastinated [group g]`

  `already procrastinated group g` proves a sub-goal if it has already been
  procrastinated before in the group `g`.

  `group g` is optional, with the same behavior as in `procrastinate`.

- `already procrastinated [intropat] : H [group g]`

  `already procrastinated name : H group g` adds only one hypothesis from `g :
  Group ...` to the context, of type `H`, and names it `name`. This is a more
  explicit version of `already procrastinated`. E.g. with `g : Group (P /\ Q /\
  ?G)`, `already procrastinated H: Q group g` introduces an hypothesis `H` of
  type `Q`.

  `group g` is optional, with the same behavior as in `procrastinate`.

- `with procrastinated [group g] [do tac]`

  + `with procrastinated` adds all hypothesis corresponding to the already
    procrastinated facts stored in `g`. E.g. if `g` has type `Group (P /\ Q /\
    ?G)`, `already procrastinated group g` adds an hypothesis of type `P` and an
    hypothesis of type `Q`.

    This is useful since tactics (e.g. `omega`) are not necessarily able to peek
    into the `Group _` hypothesis (and it is not always desirable anyway).

  + `with procrastinated do tac` allows iterating on already procrastinated
    facts. `tac` must be a tactic lambda taking an hypothesis name as input. It
    will be called on each term that has already been procrastinated in group
    `g`.

  `group g` is optional, with the same behavior as in `procrastinate`.

## "defer" variants of the tactics

Variants of the tactics are also provided that use "defer" in place of
"procrastinate", "defer" being easier to type.

- `begin deferring` is an alias for `begin procrastination`
- `defer` is an alias for `procrastinate`
- `end deferring` is an alias for `end procrastination`
- `already deferred` is an alias for `already procrastinated`
- `with deferred` is an alias for `with procrastinated`
