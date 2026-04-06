/-!
# KanTactics.Tactic.Transport

Tactics derived from transport Kan extensions: `kan_rw` and `kan_calc_trans`.

## rw as transport along an equality path

Given h : a = b, rewriting with h transports the goal along the
equality path from a to b (or b to a for <-h).

The functor K maps goals containing b to goals containing a,
via the substitution P[a/x] -> P[b/x] induced by h.

The Kan extension (Lan_K Id)(Gamma |- P[a]) computes:
- Comma category: one object, the substituted goal P[b]
- Subgoal: Gamma |- P[b]
- Assembly: Eq.mpr (congr proof) (proof of P[b])

Multiple rewrites compose as iterated transport Kan extensions:

    rw [h1, h2, h3] = Lan_K3 o Lan_K2 o Lan_K1

Since Kan extensions compose, the chain is itself a Kan extension.

## calc as composed transports

A calc block chains transitivities:

    calc a = b := p1
         _ = c := p2
         _ = d := p3

Each step is a transport Kan extension.  The full block is their
sequential composition, which is again a Kan extension (the composite
of Kan extensions along a chain of equalities in the groupoid).

We provide `kan_calc_trans` which performs a single transitivity step
(splitting a = c into a = b and b = c).  Full calc blocks decompose
into iterated applications of this extension.
-/

import KanTactics.Tactic.Core

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Single rewrite step: transport the goal along one equality.

    Categorically, this computes one Kan extension along the
    substitution functor induced by the equality. -/
private def rewriteStep (mvarId : MVarId) (stx : Syntax) (symm : Bool)
    : TacticM MVarId := do
  let heq <- Lean.Elab.Term.elabTerm stx none
  let target <- instantiateMVars (<- mvarId.getType)
  let result <- mvarId.rewrite target heq symm
  mvarId.replaceTargetEq result.eNew result.eqProof

/-- Rewrite as iterated transport Kan extensions.

    Each rule h (or <-h for reverse) triggers a transport along
    the equality h.  The transports compose sequentially.  After
    all rewrites, the identity extension (rfl) is attempted at the
    boundary to close trivially-reflexive goals. -/
def rwKan (rules : Array (Syntax × Bool)) : KanComputation where
  name := "transport (rw)"
  kind := .transport
  execute := fun mvarId => do
    let mut goal := mvarId
    for (stx, symm) in rules do
      goal <- rewriteStep goal stx symm
    -- Attempt to close with rfl (identity extension at the boundary)
    (do goal.refl; pure []) <|> pure [goal]

/-- Transitivity step for calc blocks.

    Splits an equality goal a = c into two subgoals a = b and b = c,
    for a given intermediate value b.  This is the Kan extension along
    the composition morphism in the equality groupoid:

    The comma category has one object (the pair of sub-equalities),
    and the colimit assembly is Eq.trans. -/
def calcTransKan (midpoint : Syntax) : KanComputation where
  name := "transport (calc/trans)"
  kind := .transport
  execute := fun mvarId => do
    let target <- instantiateMVars (<- mvarId.getType)
    target.eq?.elimM
      -- Not an equality: let refl produce a clear error
      (do mvarId.refl; pure [])
      fun (ty, lhs, rhs) => do
        let mid <- Lean.Elab.Term.elabTerm midpoint (some ty)
        let goalLeft <- mkFreshExprMVar (<- mkEq lhs mid)
        let goalRight <- mkFreshExprMVar (<- mkEq mid rhs)
        let proof <- mkEqTrans goalLeft goalRight
        mvarId.assign proof
        pure [goalLeft.mvarId!, goalRight.mvarId!]

-- Syntax for rewrite rules: each optionally preceded by <- for reverse

declare_syntax_cat kanRwRule
syntax "<-" term : kanRwRule
syntax term : kanRwRule

/-- Rewrite with a list of equalities via iterated transport. -/
syntax "kan_rw" "[" kanRwRule,* "]" : tactic

elab_rules : tactic
  | `(tactic| kan_rw [$rules,*]) => do
    let parsed <- rules.getElems.mapM fun rule => do
      match rule with
      | `(kanRwRule| <- $t) => pure (t, true)
      | `(kanRwRule| $t:term) => pure (t, false)
      | _ => Lean.Elab.throwUnsupportedSyntax
    kanExtend (rwKan parsed)

/-- Transitivity: split a = c into a = b and b = c. -/
elab "kan_calc_trans " mid:term : tactic => kanExtend (calcTransKan mid)
