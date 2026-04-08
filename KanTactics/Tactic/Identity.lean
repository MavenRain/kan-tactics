import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Identity

Tactics derived from identity Kan extensions.

## Primitive: kan_exact (Lan_Id F)

Given a proof term e : A, the functor F maps the goal A to e.
Along the identity embedding K = Id, the Kan extension is trivial:

    (Lan_Id F)(A) = F(A) = e

The comma category (Id | A) has a single object (A, id), and
F provides the proof directly.  No subgoals are produced.

## Derived: kan_rfl (Lan_delta Id)

Consider the diagonal functor delta : Type -> Type x Type mapping A |-> (A, A).
The identity functor Id : Type -> Type maps A |-> A.

The left Kan extension (Lan_delta Id)(A, B) computes:

    colim_{C, (C -> A, C -> B)} C

When A is definitionally equal to B, this colimit has a terminal object
(A, id, id), yielding the proof Eq.refl A.

Derived as: `first | kan_exact rfl | kan_exact True.intro`.
The first branch handles equality goals; the fallback handles goals
definitionally equal to True.
-/


open Lean Elab Tactic

set_option autoImplicit false

/-- Exact: close a goal with a specific proof term.  (Primitive) -/
elab "kan_exact " e:term : tactic => kanExtend (.identityExact e)

/-- Reflexivity: close a = a via the identity Kan extension.
    Derived from `kan_exact`: tries `rfl`, then `True.intro`. -/
elab "kan_rfl" : tactic => do
  try evalTactic (<- `(tactic| kan_exact rfl))
  catch _ => evalTactic (<- `(tactic| kan_exact True.intro))
