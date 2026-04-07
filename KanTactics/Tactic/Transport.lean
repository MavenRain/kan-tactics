import KanTactics.Tactic.Core

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


open Lean Meta Elab Tactic

set_option autoImplicit false

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
      | `(kanRwRule| <- $t) => pure ((t : Syntax), true)
      | `(kanRwRule| $t:term) => pure ((t : Syntax), false)
      | _ => Lean.Elab.throwUnsupportedSyntax
    kanExtend (.transport parsed)

/-- Transitivity: split a = c into a = b and b = c. -/
elab "kan_calc_trans " mid:term : tactic => kanExtend (.transportTrans mid)
