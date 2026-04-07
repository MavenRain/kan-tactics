import Lean

/-!
# KanTactics.Tactic.Core

The core Kan extension tactic framework.

## The Categorical View of Tactics

In the category **Proof** of proof states:
- Objects are sequents (context |- goal)
- Morphisms are proof terms witnessing entailment

A tactic T corresponds to a left Kan extension.  Given:

- K : C -> Proof, an embedding of "structured" proof states
- F : C -> Proof, mapping structured states to proofs or simpler goals

The left Kan extension (Lan_K F)(goal) computes:

1. The comma category (K | goal): all ways to factor the goal through K
2. For each factorization, F gives a subgoal or direct proof
3. The colimit assembles the pieces via the universal property

## This Module

Defines `name` and `execute` (the specification of each Kan extension
kind) and `kanExtend` (the universal entry point).  Every tactic
in this library invokes `kanExtend` with a specific `KanExtensionKind`,
demonstrating that the tactic is an instance of a Kan extension.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-! ## Combinators -/

/-- Extract FVarId from an expression, returning none if not a free variable.
    Uses if/else on the boolean predicate rather than pattern matching. -/
def exprAsFVarId (e : Expr) : Option FVarId :=
  if e.isFVar then some e.fvarId! else none

/-- Extract the InductiveVal from a ConstantInfo, if it is an inductive type. -/
def inductiveVal? (info : ConstantInfo) : Option InductiveVal :=
  match info with
  | .inductInfo val => some val
  | .axiomInfo _    => none
  | .defnInfo _     => none
  | .thmInfo _      => none
  | .opaqueInfo _   => none
  | .quotInfo _     => none
  | .ctorInfo _     => none
  | .recInfo _      => none

/-! ## Kan Extension Framework -/

/-- Classification of Kan extensions by their categorical origin.

    Each variant identifies the categorical construction that
    gives rise to a family of tactics. -/
inductive KanExtensionKind where
  /-- Extension of id along the diagonal.  Closes the goal directly
      when source and target are definitionally equal.
      Tactics: rfl, exact. -/
  | identity
  /-- Backward extension along a morphism f : A -> B.  Reduces a
      goal of type B to a goal of type A (the domain of f).
      Tactics: apply, refine. -/
  | precomposition
  /-- Unit of an adjunction (e.g., currying via the exponential).
      Introduces binders into the context.
      Tactics: intro, intros. -/
  | adjunctionUnit
  /-- Transport along an equality path.  Rewrites the goal by
      substituting along a proof of a = b.
      Tactics: rw, calc. -/
  | transport
  /-- Automated search in the transport category.  Finds a
      simplification path using a database of equational lemmas.
      Tactics: simp, dsimp, simp only. -/
  | normalize
  /-- Injection into a coproduct/sigma.  Selects a constructor
      and reduces to its argument types.
      Tactics: constructor, use, exists. -/
  | colimitInjection
  /-- Decomposition at a coproduct.  Splits a hypothesis into
      cases, one per constructor of the inductive type.
      Tactics: cases, rcases. -/
  | colimitDecomposition
  /-- Extension along an initial algebra structure map.
      Structural induction on an inductive type.
      Tactics: induction. -/
  | initialAlgebra
  deriving Repr, BEq

/-- Human-readable name for each Kan extension kind. -/
def name (kind : KanExtensionKind) : String :=
  match kind with
  | .identity => "identity"
  | .precomposition => "precomposition"
  | .adjunctionUnit => "adjunction unit"
  | .transport => "transport"
  | .normalize => "normalize"
  | .colimitInjection => "colimit injection"
  | .colimitDecomposition => "colimit decomposition"
  | .initialAlgebra => "initial algebra"

/-- Execute the Kan extension computation for a given kind on a goal.

    The implementation:
    (1) inspects the goal (computing the comma category K | goal),
    (2) assigns a proof term to the goal (the colimit cocone), and
    (3) returns any new subgoals (the components of the colimit).

    Must assign `mvarId` and must NOT call `setGoals` or
    `replaceMainGoal` (the caller handles goal management). -/
def execute (kind : KanExtensionKind) : MVarId -> TacticM (List MVarId) :=
  match kind with
  | .identity => sorry
  | .precomposition => sorry
  | .adjunctionUnit => sorry
  | .transport => sorry
  | .normalize => sorry
  | .colimitInjection => sorry
  | .colimitDecomposition => sorry
  | .initialAlgebra => sorry

/-- Execute a Kan extension tactic.

    This is **the** universal entry point.  Every tactic in this library
    invokes this with a specific `KanExtensionKind`.  The function:

    1. Retrieves the current main goal
    2. Delegates to `execute kind` which computes the comma category,
       applies F, and assembles via the colimit
    3. Replaces the main goal with any new subgoals

    By routing every tactic through this single function, we
    demonstrate that each tactic is an instance of a Kan extension.

    Categorically: compute (Lan_K F)(goal) via the colimit formula. -/
def kanExtend (kind : KanExtensionKind) : TacticM Unit := do
  let mvarId <- getMainGoal
  mvarId.withContext do
    let newGoals <- execute kind mvarId
    replaceMainGoal newGoals
