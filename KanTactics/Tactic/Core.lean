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
private def rewriteStep (mvarId : MVarId) (stx : Syntax) (symm : Bool)
    : TacticM MVarId := do
  let heq <- Lean.Elab.Term.elabTerm stx none
  let target <- instantiateMVars (<- mvarId.getType)
  let result <- mvarId.rewrite target heq symm
  mvarId.replaceTargetEq result.eNew result.eqProof

/-- Run the simplifier on a goal and process the result.

    If a propositional proof was produced, replace the target.
    If the simplified expression is True, close the goal.
    If no propositional change occurred, change the target definitionally. -/
private def processSimpResult (mvarId : MVarId) (result : Simp.Result)
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

/-- Classification of Kan extensions by their categorical origin.

    Each variant identifies the categorical construction that
    gives rise to a family of tactics, carrying any arguments
    needed by the extension. -/
inductive KanExtensionKind where
  /-- Extension of id along the diagonal.  Closes the goal directly
      when source and target are definitionally equal. -/
  | identity
  /-- Trivial identity extension: the given term proves the goal. -/
  | identityExact (stx : Syntax)
  /-- Backward extension along a morphism.  Reduces a goal of type B
      to subgoals by applying the given term. -/
  | precomposition (stx : Syntax)
  /-- Partial precomposition with explicit holes.  Each placeholder
      in the term becomes a subgoal. -/
  | precompositionRefine (stx : Syntax)
  /-- Unit of the exponential adjunction.  Introduces all leading
      binders into the context. -/
  | adjunctionUnit
  /-- Single adjunction unit.  Introduces one binder with the given name. -/
  | adjunctionUnitIntro (name : Name)
  /-- Iterated adjunction units with explicit names. -/
  | adjunctionUnitIntros (names : Array Name)
  /-- Transport along equality paths.  Rewrites the goal by each rule
      in sequence (true = reverse direction). -/
  | transport (rules : Array (Syntax × Bool))
  /-- Transport via transitivity.  Splits a = c into a = b and b = c
      at the given midpoint. -/
  | transportTrans (midpoint : Syntax)
  /-- Automated search in the transport category.  Simplifies the goal
      using all registered simp lemmas. -/
  | normalize
  /-- Definitional normalization only (beta, delta, iota, zeta, eta). -/
  | normalizeDSimp
  /-- Normalization restricted to the given set of simp lemmas. -/
  | normalizeSimpOnly (lemmas : Array Syntax)
  /-- Injection into a coproduct/sigma.  Selects the first constructor
      and reduces to its argument types. -/
  | colimitInjection
  /-- Coproduct injection with a given witness for the first argument. -/
  | colimitInjectionUse (stx : Syntax)
  /-- Decomposition at a coproduct.  Splits a hypothesis into cases,
      one per constructor of the inductive type. -/
  | colimitDecomposition (stx : Syntax)
  /-- Extension along an initial algebra structure map.
      Structural induction on an inductive type. -/
  | initialAlgebra (stx : Syntax)

/-- Human-readable name for each Kan extension kind. -/
def name (kind : KanExtensionKind) : String :=
  match kind with
  | .identity => "identity (rfl)"
  | .identityExact _ => "identity (exact)"
  | .precomposition _ => "precomposition (apply)"
  | .precompositionRefine _ => "precomposition (refine)"
  | .adjunctionUnit => "adjunction unit (intros *)"
  | .adjunctionUnitIntro _ => "adjunction unit (intro)"
  | .adjunctionUnitIntros _ => "adjunction unit (intros)"
  | .transport _ => "transport (rw)"
  | .transportTrans _ => "transport (calc/trans)"
  | .normalize => "normalize (simp)"
  | .normalizeDSimp => "normalize (dsimp)"
  | .normalizeSimpOnly _ => "normalize (simp only)"
  | .colimitInjection => "colimit injection (constructor)"
  | .colimitInjectionUse _ => "colimit injection (use)"
  | .colimitDecomposition _ => "colimit decomposition (cases)"
  | .initialAlgebra _ => "initial algebra (induction)"

/-- Execute the Kan extension computation for a given kind on a goal.

    The implementation:
    (1) inspects the goal (computing the comma category K | goal),
    (2) assigns a proof term to the goal (the colimit cocone), and
    (3) returns any new subgoals (the components of the colimit).

    Must assign `mvarId` and must NOT call `setGoals` or
    `replaceMainGoal` (the caller handles goal management). -/
def execute (kind : KanExtensionKind) : MVarId -> TacticM (List MVarId) :=
  match kind with
  | .identity => fun mvarId =>
    (do mvarId.refl; pure []) <|> do
      let newGoal <- mvarId.change (mkConst ``True)
      newGoal.assign (mkConst ``True.intro)
      pure []
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
  | .adjunctionUnit => fun mvarId => do
    let (_, newMVarId) <- mvarId.intros
    pure [newMVarId]
  | .adjunctionUnitIntro n => fun mvarId => do
    let (_, newMVarId) <- mvarId.intro n
    pure [newMVarId]
  | .adjunctionUnitIntros names => fun mvarId => do
    let (_, newMVarId) <- mvarId.introN names.size names.toList
    pure [newMVarId]
  | .transport rules => fun mvarId => do
    let mut goal := mvarId
    for (stx, symm) in rules do
      goal <- rewriteStep goal stx symm
    (do goal.refl; pure []) <|> pure [goal]
  | .transportTrans midpoint => fun mvarId => do
    let target <- instantiateMVars (<- mvarId.getType)
    target.eq?.elim
      (do mvarId.refl; pure [])
      fun (ty, lhs, rhs) => do
        let mid <- Lean.Elab.Term.elabTerm midpoint (some ty)
        let goalLeft <- mkFreshExprMVar (<- mkEq lhs mid)
        let goalRight <- mkFreshExprMVar (<- mkEq mid rhs)
        let proof <- mkEqTrans goalLeft goalRight
        mvarId.assign proof
        pure [goalLeft.mvarId!, goalRight.mvarId!]
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
    let mut simpTheorems : SimpTheorems := {}
    for stx in lemmaStxs do
      let e <- Lean.Elab.Term.elabTerm stx none
      simpTheorems <- e.constName?.elim
        (pure simpTheorems)
        fun n => simpTheorems.addConst n
    let congrTheorems <- getSimpCongrTheorems
    let ctx <- Simp.mkContext (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    processSimpResult mvarId result
  | .colimitInjection => fun mvarId => do
    let target <- instantiateMVars (<- mvarId.getType)
    (<- firstCtorOf target).elim
      (do let ctor <- mkConstWithFreshMVarLevels `True
          mvarId.apply ctor)
      fun ctorName => do
        let ctor <- mkConstWithFreshMVarLevels ctorName
        mvarId.apply ctor
  | .colimitInjectionUse stx => fun mvarId => do
    let target <- instantiateMVars (<- mvarId.getType)
    let goals <- (<- firstCtorOf target).elim
      (do let ctor <- mkConstWithFreshMVarLevels `True
          mvarId.apply ctor)
      fun ctorName => do
        let ctor <- mkConstWithFreshMVarLevels ctorName
        mvarId.apply ctor
    goals.head?.elim (pure []) fun witnessGoal => do
      let witness <- Lean.Elab.Term.elabTerm stx (some (<- witnessGoal.getType))
      witnessGoal.assign witness
      pure goals.tail
  | .colimitDecomposition stx => fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    (exprAsFVarId e).elim
      (do let result <- mvarId.cases e.fvarId!
          pure (result.map (fun s => s.mvarId)).toList)
      fun fvarId => do
        let result <- mvarId.cases fvarId
        pure (result.map (fun s => s.mvarId)).toList
  | .initialAlgebra stx => fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    (exprAsFVarId e).elim
      (do let recConst <- mkConstWithFreshMVarLevels `Nat.rec
          mvarId.apply recConst)
      fun fvarId => do
        let localDecl <- fvarId.getDecl
        let type <- instantiateMVars localDecl.type
        let typeName := type.getAppFn.constName?.getD Name.anonymous
        let recName := typeName ++ `rec
        let recConst <- mkConstWithFreshMVarLevels recName
        mvarId.apply recConst

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
