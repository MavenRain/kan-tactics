import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Decompose

Tactics derived from colimit decomposition Kan extensions:
`kan_cases` and `kan_rcases`.

## cases as coproduct elimination

An inductive type T ~= A1 + A2 + ... + An is a coproduct.
To prove P given h : T, we must prove P for each component:

    P given h matches c1(args1)
    P given h matches c2(args2)
    ...
    P given h matches cn(argsn)

The functor K maps each Ai to T via the constructor injection ci.
To map *out* of the coproduct, we need a map from each component.
The Kan extension at goal P decomposes the comma category:

    (K | h : T) has one object per constructor ci

Each object contributes a subgoal: prove P with the constructor's
arguments in context.  The assembly uses the type's recursor to
combine the per-constructor proofs.

## rcases as iterated decomposition

rcases recursively applies cases, decomposing nested inductive
types in one step.  This is the composition of multiple Kan extensions,
one per level of nesting.  Since Kan extensions compose, the recursive
decomposition is itself a single Kan extension.

NOTE: Full rcases pattern syntax (as in Mathlib) requires a custom
parser.  This implementation provides basic recursive decomposition.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Cases as coproduct decomposition.

    Decomposes a hypothesis h of inductive type into one subgoal
    per constructor.  Each subgoal introduces the constructor's
    arguments into the context.

    Comma category (K | h) has n objects for n constructors.
    The Kan extension produces n subgoals, one per constructor.
    Assembly: the type's recursor applied to all branch proofs. -/
def casesKan (stx : Syntax) : KanComputation where
  name := "coproduct decomposition (cases)"
  kind := .colimitDecomposition
  execute := fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    (exprAsFVarId e).elim
      -- Not a free variable: let cases fail with its own diagnostic
      (do let result <- mvarId.cases e.fvarId!
          pure (result.map (fun s => s.mvarId)).toList)
      fun fvarId => do
        let result <- mvarId.cases fvarId
        pure (result.map (fun s => s.mvarId)).toList

/-- Recursive cases as iterated coproduct decomposition.

    Applies case analysis to the given hypothesis.  In its basic form,
    this is equivalent to `kan_cases`.  A full implementation would
    support nested patterns for deep decomposition.

    Categorically: the composition of Kan extensions along a chain
    of coproduct decompositions, one per nesting level. -/
def rcasesKan (stx : Syntax) : KanComputation where
  name := "iterated coproduct decomposition (rcases)"
  kind := .colimitDecomposition
  execute := fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    (exprAsFVarId e).elim
      (do let result <- mvarId.cases e.fvarId!
          pure (result.map (fun s => s.mvarId)).toList)
      fun fvarId => do
        let result <- mvarId.cases fvarId
        pure (result.map (fun s => s.mvarId)).toList

/-- Case analysis: decompose a hypothesis into one subgoal per constructor. -/
elab "kan_cases " e:term : tactic => kanExtend (casesKan e)

/-- Recursive case analysis (basic form; equivalent to kan_cases). -/
elab "kan_rcases " e:term : tactic => kanExtend (rcasesKan e)
