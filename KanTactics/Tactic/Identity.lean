/-!
# KanTactics.Tactic.Identity

Tactics derived from the identity Kan extension: `kan_rfl` and `kan_exact`.

## rfl as Lan_delta Id

Consider the diagonal functor delta : Type -> Type x Type mapping A |-> (A, A).
The identity functor Id : Type -> Type maps A |-> A.

The left Kan extension (Lan_delta Id)(A, B) computes:

    colim_{C, (C -> A, C -> B)} C

When A is definitionally equal to B, this colimit has a terminal object
(A, id, id), yielding the proof Eq.refl A.  When A is not definitionally
equal to B, the comma category (delta | (A, B)) is empty and the
extension fails.

This is exactly the behavior of `rfl`: it closes an equality goal
a = b when a and b are definitionally equal, and fails otherwise.

## exact as Lan_Id F

Given a proof term e : A, the functor F maps the goal A to e.
Along the identity embedding K = Id, the Kan extension is trivial:

    (Lan_Id F)(A) = F(A) = e

The comma category (Id | A) has a single object (A, id), and
F provides the proof directly.  No subgoals are produced.
-/

import KanTactics.Tactic.Core

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Reflexivity as the left Kan extension of Id along the diagonal.

    The comma category (delta | (A, B)) is nonempty iff A and B are
    definitionally equal, in which case the unique terminal object
    yields Eq.refl A as the colimit.

    Primary path: use the built-in refl check.
    Fallback: close goals that are definitionally True. -/
def rflKan : KanComputation where
  name := "identity (rfl)"
  kind := .identity
  execute := fun mvarId => do
    -- Primary: identity extension via reflexivity
    (do mvarId.refl; pure []) <|> do
    -- Fallback: close definitionally-True goals
    let newGoal <- mvarId.change (mkConst ``True)
    newGoal.assign (mkConst ``True.intro)
    pure []

/-- Exact term as the trivial (identity) Kan extension.

    The comma category (Id | goal) has exactly one object,
    and the diagram functor F provides the proof directly. -/
def exactKan (stx : Syntax) : KanComputation where
  name := "identity (exact)"
  kind := .identity
  execute := fun mvarId => do
    let target <- mvarId.getType
    let e <- Lean.Elab.Term.elabTerm stx (some target)
    mvarId.assign e
    pure []

/-- Reflexivity: close a = a via the identity Kan extension. -/
elab "kan_rfl" : tactic => kanExtend rflKan

/-- Exact: close a goal with a specific proof term. -/
elab "kan_exact " e:term : tactic => kanExtend (exactKan e)
