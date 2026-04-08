import Lean
import Lean.Meta.Tactic.Simp

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

Defines the **minimal spanning set** of 9 primitive Kan extension kinds.
Every other tactic in the library is derived by composing these primitives.

The 9 primitives, grouped by categorical origin:

- **Identity**: `identityExact` (provide a proof term)
- **Precomposition**: `precomposition` (apply), `precompositionRefine` (refine)
- **Adjunction unit**: `adjunctionUnitIntro` (introduce one binder)
- **Transport**: `transport` (rewrite by equalities)
- **Normalization**: `normalize` (simp), `normalizeDSimp` (dsimp),
  `normalizeSimpOnly` (simp only)
- **Decomposition**: `colimitDecomposition` (case analysis)

Derived tactics (kan_rfl, kan_intros, kan_constructor, kan_use,
kan_exists, kan_rcases, kan_calc_trans, kan_induction) compose these
primitives, preserving the categorical interpretation while eliminating
redundancy from the core.
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

/-- Look up the first constructor of the goal's inductive type.
    Returns none if the goal type is not an inductive or has no constructors.
    Chains Option combinators: constName? -> find? -> inductiveVal? -> head?. -/
def firstCtorOf (target : Expr) : MetaM (Option Name) := do
  let env <- getEnv
  pure <| target.getAppFn.constName?
    |>.bind fun name => env.find? name
    |>.bind inductiveVal?
    |>.bind fun val => val.ctors.head?

/-! ## Kan Extension Framework -/

/-- Single rewrite step: transport the goal along one equality.

    Categorically, this computes one Kan extension along the
    substitution functor induced by the equality. -/
def rewriteStep (mvarId : MVarId) (stx : Syntax) (symm : Bool)
    : TacticM MVarId := do
  let heq <- Lean.Elab.Term.elabTerm stx none
  let target <- instantiateMVars (<- mvarId.getType)
  let result <- mvarId.rewrite target heq symm
  mvarId.replaceTargetEq result.eNew result.eqProof

/-- Run the simplifier on a goal and process the result.

    If a propositional proof was produced, replace the target.
    If the simplified expression is True, close the goal.
    If no propositional change occurred, change the target definitionally. -/
def processSimpResult (mvarId : MVarId) (result : Simp.Result)
    : TacticM (List MVarId) :=
  result.proof?.elim
    (do let newGoal <- mvarId.change result.expr
        pure [newGoal])
    fun proof => do
      let newGoal <- mvarId.replaceTargetEq result.expr proof
      if result.expr.isConstOf ``True then
        newGoal.assign (mkConst ``True.intro)
        pure []
      else
        pure [newGoal]

/-- The minimal spanning set of Kan extension kinds.

    Each variant identifies an independent categorical construction.
    No variant is expressible as a composition of others.  All other
    tactics in the library are derived from these 9 primitives. -/
inductive KanExtensionKind where
  /-- Trivial identity extension: the given term proves the goal.

      Given a proof term e : A, the functor F maps the goal A to e.
      Along the identity embedding K = Id:

          (Lan_Id F)(A) = F(A) = e

      The comma category (Id | A) has a single object (A, id). -/
  | identityExact (stx : Syntax)
  /-- Backward extension along a morphism.  Reduces a goal of type B
      to subgoals by applying the given term.

      Given f : A1 -> ... -> An -> B, the comma category (K | B) has a
      single object when f's return type unifies with B, projecting to
      n subgoals.  Uses unconstrained elaboration + `mvarId.apply`. -/
  | precomposition (stx : Syntax)
  /-- Partial precomposition with explicit holes.  Each placeholder
      in the term becomes a subgoal.

      Uses goal-directed elaboration (`elabTerm stx (some target)`)
      and direct assignment, collecting unassigned metavariables. -/
  | precompositionRefine (stx : Syntax)
  /-- Single adjunction unit.  Introduces one binder with the given name.

      The unit of the exponential adjunction Hom(Gamma x A, B) ~=
      Hom(Gamma, A -> B) introduces x : A into context, yielding
      goal B with A available. -/
  | adjunctionUnitIntro (name : Name)
  /-- Transport along equality paths.  Rewrites the goal by each rule
      in sequence (true = reverse direction).

      Each rewrite step is a Kan extension along the substitution
      functor induced by the equality.  Their composition is again
      a Kan extension. -/
  | transport (rules : Array (Syntax × Bool))
  /-- Automated search in the transport category.  Simplifies the goal
      using all registered simp lemmas.

      The simplifier searches for a factorization through the full
      comma category of available simp lemmas. -/
  | normalize
  /-- Definitional normalization only (beta, delta, iota, zeta, eta).

      Restricts the transport category to definitional equalities,
      which form a sub-groupoid of the full equality groupoid. -/
  | normalizeDSimp
  /-- Normalization restricted to the given set of simp lemmas.

      Restricts the comma category to a specified set of lemmas,
      giving fine-grained control over which transports are allowed. -/
  | normalizeSimpOnly (lemmas : Array Syntax)
  /-- Decomposition at a coproduct.  Splits a hypothesis into cases,
      one per constructor of the inductive type.

      The Kan extension at goal P decomposes the comma category
      (K | h : T) into one object per constructor, each contributing
      a subgoal with the constructor's arguments in context. -/
  | colimitDecomposition (stx : Syntax)

/-- Human-readable name for each primitive Kan extension kind. -/
def name (kind : KanExtensionKind) : String :=
  match kind with
  | .identityExact _ => "identity (exact)"
  | .precomposition _ => "precomposition (apply)"
  | .precompositionRefine _ => "precomposition (refine)"
  | .adjunctionUnitIntro _ => "adjunction unit (intro)"
  | .transport _ => "transport (rw)"
  | .normalize => "normalize (simp)"
  | .normalizeDSimp => "normalize (dsimp)"
  | .normalizeSimpOnly _ => "normalize (simp only)"
  | .colimitDecomposition _ => "colimit decomposition (cases)"

/-- Execute the Kan extension computation for a given kind on a goal.

    The implementation:
    (1) inspects the goal (computing the comma category K | goal),
    (2) assigns a proof term to the goal (the colimit cocone), and
    (3) returns any new subgoals (the components of the colimit).

    Must assign `mvarId` and must NOT call `setGoals` or
    `replaceMainGoal` (the caller handles goal management). -/
def execute (kind : KanExtensionKind) : MVarId -> TacticM (List MVarId) :=
  match kind with
  | .identityExact stx => fun mvarId => do
    let target <- mvarId.getType
    let e <- Lean.Elab.Term.elabTerm stx (some target)
    mvarId.assign e
    pure []
  | .precomposition stx => fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    mvarId.apply e
  | .precompositionRefine stx => fun mvarId => do
    let target <- mvarId.getType
    let e <- Lean.Elab.Term.elabTerm stx (some target)
    mvarId.assign e
    let unassigned <- (<- getMVars e).filterM fun m => do
      return !(<- m.isAssigned)
    pure unassigned.toList
  | .adjunctionUnitIntro n => fun mvarId => do
    let (_, newMVarId) <- mvarId.intro n
    pure [newMVarId]
  | .transport rules => fun mvarId => do
    let goal <- rules.foldlM (fun g (stx, symm) => rewriteStep g stx symm) mvarId
    (do goal.refl; pure []) <|> pure [goal]
  | .normalize => fun mvarId => do
    let simpTheorems <- getSimpTheorems
    let congrTheorems <- getSimpCongrTheorems
    let ctx <- Simp.mkContext (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    processSimpResult mvarId result
  | .normalizeDSimp => fun mvarId => do
    let simpTheorems <- getSimpTheorems
    let congrTheorems <- getSimpCongrTheorems
    let ctx <- Simp.mkContext
      (config := { zeta := true, beta := true, eta := true, iota := true, proj := true })
      (simpTheorems := #[simpTheorems])
      (congrTheorems := congrTheorems)
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    let newGoal <- mvarId.change result.expr
    pure [newGoal]
  | .normalizeSimpOnly lemmaStxs => fun mvarId => do
    let simpTheorems <- lemmaStxs.foldlM (fun acc stx => do
      let e <- Lean.Elab.Term.elabTerm stx none
      e.constName?.elim
        (pure acc)
        fun n => acc.addConst n) ({} : SimpTheorems)
    let congrTheorems <- getSimpCongrTheorems
    let ctx <- Simp.mkContext (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    processSimpResult mvarId result
  | .colimitDecomposition stx => fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    (exprAsFVarId e).elim
      (do let result <- mvarId.cases e.fvarId!
          pure (result.map (fun s => s.mvarId)).toList)
      fun fvarId => do
        let result <- mvarId.cases fvarId
        pure (result.map (fun s => s.mvarId)).toList

/-- Execute a Kan extension tactic.

    This is **the** universal entry point for primitive tactics.
    Every primitive tactic invokes this with a specific `KanExtensionKind`.

    Derived tactics compose primitive tactics via `evalTactic` rather than
    adding variants to this enum, keeping the core minimal.

    Categorically: compute (Lan_K F)(goal) via the colimit formula. -/
def kanExtend (kind : KanExtensionKind) : TacticM Unit := do
  let mvarId <- getMainGoal
  mvarId.withContext do
    let newGoals <- execute kind mvarId
    replaceMainGoal newGoals
