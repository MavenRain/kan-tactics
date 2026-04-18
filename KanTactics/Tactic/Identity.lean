import KanTactics.Tactic.Core
import KanTactics.Tactic.Precomposition

/-!
# KanTactics.Tactic.Identity

Tactics derived from identity Kan extensions.

## Derived: kan_exact (degenerate precomposition)

Given a proof term e : A, closing a goal of type A with e is the
degenerate case of partial precomposition where the term has no
holes and therefore produces no subgoals.  The identity Kan
extension (Lan_Id F)(A) = F(A) = e factors through
`precompositionRefine` without loss: both elaborate the term at
the goal type and assign it, with `kan_refine` additionally
collecting any unassigned metavariables (zero, in the exact case).

Implemented as: `kan_refine e`.

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

/-- Exact: close a goal with a specific proof term.
    Derived from `kan_refine`: the hole-free case of partial
    precomposition. -/
elab "kan_exact " e:term : tactic => do
  evalTactic (<- `(tactic| kan_refine $e))

/-- Reflexivity: close a = a via the identity Kan extension.
    Derived from `kan_exact`: tries `rfl`, then `True.intro`. -/
elab "kan_rfl" : tactic => do
  try evalTactic (<- `(tactic| kan_exact rfl))
  catch _ => evalTactic (<- `(tactic| kan_exact True.intro))
