Require Import Procrastination.Procrastination.

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
  assert (a + b = c) by procrastinate. simpl in g.
  exact I.

  end procrastination.
  exists 0, 0, 0. reflexivity.
Qed.
