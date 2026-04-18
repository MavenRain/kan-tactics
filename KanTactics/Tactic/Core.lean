import Lean
import Lean.Meta.Tactic.Simp  -- SimpTheorems data access only; Simp.main is not called

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

Defines the **minimal spanning set** of 8 primitive Kan extension kinds.
Every other tactic in the library is derived by composing these primitives,
optionally combined with goal- or hypothesis-inspection helpers
(e.g., `firstCtorOf` used by `kan_constructor`) that do not themselves
invoke Kan extensions.

The 8 primitives, grouped by categorical origin:

- **Precomposition**: `precomposition` (apply), `precompositionRefine` (refine)
- **Adjunction unit**: `adjunctionUnitIntro` (introduce one binder)
- **Transport**: `transport` (rewrite by equalities)
- **Normalization**: `normalize` (simp), `normalizeDSimp` (dsimp),
  `normalizeSimpOnly` (simp only)
- **Decomposition**: `colimitDecomposition` (case analysis)

Derived tactics (kan_exact, kan_rfl, kan_intros, kan_constructor, kan_use,
kan_exists, kan_rcases, kan_calc_trans, kan_induction) compose these
primitives.  `kan_exact` is derived from `precompositionRefine`: a goal
closed by a term with no holes is the degenerate case of partial
precomposition where no subgoals remain.
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
    substitution functor induced by the equality.

    Implementation: `kabstract` finds the left-hand side in the goal
    (using `isDefEq` for subterm matching), `mkCongrArg` constructs
    the equality proof, and `replaceTargetEq` updates the goal. -/
def rewriteStep (mvarId : MVarId) (stx : Syntax) (symm : Bool)
    : TacticM MVarId := do
  let heq <- Lean.Elab.Term.elabTerm stx none
  let heqType <- inferType heq
  let some (α, lhs, rhs) := heqType.eq?
    | throwError "rewriteStep: expected an equality proof"
  let (lhs, rhs, proof) <- do
    if symm then
      let symmProof <- mkEqSymm heq
      pure (rhs, lhs, symmProof)
    else
      pure (lhs, rhs, heq)
  let target <- instantiateMVars (<- mvarId.getType)
  let abstracted <- kabstract target lhs
  unless abstracted.hasLooseBVars do
    throwError "rewriteStep: left-hand side not found in goal"
  let newTarget := abstracted.instantiate1 rhs
  let motive := mkLambda `x BinderInfo.default α abstracted
  let eqProof <- mkCongrArg motive proof
  mvarId.replaceTargetEq newTarget eqProof

/-- Try to rewrite a target expression using a single lemma proof.

    Opens universal quantifiers with `forallMetaTelescopeReducing`,
    finds the left-hand side in the target via `kabstract` (which uses
    `isDefEq` internally for subterm matching), and constructs the
    equality proof via `mkCongrArg`. -/
private def tryLemmaRewrite (target : Expr) (lemmaExpr : Expr)
    : MetaM (Option (Expr × Expr)) := do
  let saved <- saveState
  try
    let lemmaType <- inferType lemmaExpr
    let (mvars, _, body) <- forallMetaTelescopeReducing lemmaType
    match body.eq? with
    | some (α, lhs, rhs) =>
      let abstracted <- kabstract target lhs
      if abstracted.hasLooseBVars then
        let rhs <- instantiateMVars rhs
        let newTarget := abstracted.instantiate1 rhs
        let fullLemma <- instantiateMVars (mkAppN lemmaExpr mvars)
        let motive := mkLambda `x BinderInfo.default α abstracted
        let eqProof <- mkCongrArg motive fullLemma
        pure (some (newTarget, eqProof))
      else
        saved.restore
        pure none
    | none =>
      saved.restore
      pure none
  catch _ =>
    saved.restore
    pure none

/-- Iteratively rewrite a target expression using the given lemmas
    until no more rewrites apply.  Chains equality proofs via
    `mkEqTrans`.  Returns `(target, proof?, truncated)` where
    `truncated = true` means the step limit was reached before
    rewriting stabilized; the caller is responsible for surfacing
    this to the user (e.g., via `logWarning`) so that "rewriting
    converged" and "step limit truncated" are distinguishable. -/
private partial def rewriteByLemmaLoop (target : Expr) (lemmas : Array Expr)
    (proof? : Option Expr) (fuel : Nat) : MetaM (Expr × Option Expr × Bool) := do
  if fuel == 0 then return (target, proof?, true)
  for lemma in lemmas do
    match (<- tryLemmaRewrite target lemma) with
    | some (newTarget, stepProof) =>
      let combined <- match proof? with
        | some p => pure (some (<- mkEqTrans p stepProof))
        | none => pure (some stepProof)
      return (<- rewriteByLemmaLoop newTarget lemmas combined (fuel - 1))
    | none => continue
  return (target, proof?, false)

/-- Apply the result of normalization to a goal.

    If an equality proof is available, uses `replaceTargetEq`.
    If only a definitional change occurred, uses `change`.
    Closes the goal with `True.intro` if the result is `True`. -/
private def applyNormalizeResult (mvarId : MVarId) (newTarget : Expr)
    (eqProof? : Option Expr) : TacticM (List MVarId) :=
  match eqProof? with
  | some eqProof => do
    let newGoal <- mvarId.replaceTargetEq newTarget eqProof
    if newTarget.isConstOf ``True then
      newGoal.assign (mkConst ``True.intro)
      pure []
    else
      pure [newGoal]
  | none => do
    let newGoal <- mvarId.change newTarget
    if newTarget.isConstOf ``True then
      newGoal.assign (mkConst ``True.intro)
      pure []
    else
      pure [newGoal]

/-- Introduce all leading forall binders on a goal metavar,
    extending its local context with each binder argument.
    Returns the final metavar after all introductions. -/
private partial def introAllForalls (mvarId : MVarId) : MetaM MVarId := do
  let mvarDecl <- mvarId.getDecl
  let target <- whnf mvarDecl.type
  if target.isForall then
    let fId <- mkFreshFVarId
    let lctx := mvarDecl.lctx.mkLocalDecl fId target.bindingName!
      target.bindingDomain! target.bindingInfo!
    let bodyType := target.bindingBody!.instantiate1 (mkFVar fId)
    let newGoal <- mkFreshExprMVarAt lctx mvarDecl.localInstances bodyType
    mvarId.assign (mkLambda target.bindingName! target.bindingInfo!
      target.bindingDomain! newGoal)
    introAllForalls newGoal.mvarId!
  else
    pure mvarId

/-- The minimal spanning set of Kan extension kinds.

    Each variant identifies an independent categorical construction.
    No variant is expressible as a composition of others.  All other
    tactics in the library are derived from these 8 primitives,
    optionally composed with helpers that inspect goals or
    hypotheses (e.g., `firstCtorOf`). -/
inductive KanExtensionKind where
  /-- Backward extension along a morphism.  Reduces a goal of type B
      to subgoals by applying the given term.

      Given f : A1 -> ... -> An -> B, the comma category (K | B) has a
      single object when f's return type unifies with B, projecting to
      n subgoals.  Uses `forallMetaTelescopeReducing` + `isDefEq`. -/
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
  | .precomposition stx => fun mvarId => do
    -- Backward extension: `forallMetaTelescopeReducing` creates
    -- metavars for all arguments, `isDefEq` checks the return type
    -- matches the goal, and `assign` closes the goal.
    let e <- Lean.Elab.Term.elabTerm stx none
    let eType <- inferType e
    let (mvars, _, body) <- forallMetaTelescopeReducing eType
    let target <- instantiateMVars (<- mvarId.getType)
    unless (<- isDefEq body target) do
      throwError "precomposition: result type does not unify with goal"
    mvarId.assign (mkAppN e mvars)
    let unassigned <- mvars.filterM fun m =>
      return !(<- m.mvarId!.isAssigned)
    pure (unassigned.map (·.mvarId!)).toList
  | .precompositionRefine stx => fun mvarId => do
    let target <- mvarId.getType
    let e <- Lean.Elab.Term.elabTerm stx (some target)
    mvarId.assign e
    let unassigned <- (<- getMVars e).filterM fun m => do
      return !(<- m.isAssigned)
    pure unassigned.toList
  | .adjunctionUnitIntro n => fun mvarId => do
    -- Adjunction unit: manually extend the local context,
    -- create a new metavar in the extended context, and assign
    -- the original goal with a lambda abstraction.
    let mvarDecl <- mvarId.getDecl
    let target <- instantiateMVars mvarDecl.type
    let target <- whnf target
    unless target.isForall do
      throwError "adjunctionUnitIntro: target is not a forall"
    let fvarId <- mkFreshFVarId
    let lctx := mvarDecl.lctx.mkLocalDecl fvarId n
      target.bindingDomain! target.bindingInfo!
    let bodyType := target.bindingBody!.instantiate1 (mkFVar fvarId)
    let newGoal <- mkFreshExprMVarAt lctx mvarDecl.localInstances
      bodyType
    mvarId.assign (mkLambda n target.bindingInfo!
      target.bindingDomain! newGoal)
    pure [newGoal.mvarId!]
  | .transport rules => fun mvarId => do
    let goal <- rules.foldlM
      (fun g (stx, symm) => rewriteStep g stx symm) mvarId
    -- Try closing with Eq.refl if the goal is a = a
    let target <- instantiateMVars (<- goal.getType)
    match target.eq? with
    | some (_, lhs, rhs) =>
      if (<- isDefEq lhs rhs) then
        goal.assign (<- mkEqRefl lhs)
        pure []
      else
        pure [goal]
    | none => pure [goal]
  | .normalize => fun mvarId => do
    -- Phase 1: definitional reduction via Meta.reduce
    let target <- instantiateMVars (<- mvarId.getType)
    let reduced <- Meta.reduce target
      (explicitOnly := false) (skipTypes := false) (skipProofs := false)
    -- Phase 2: equational rewriting with registered simp lemmas.
    -- We read SimpTheorems for lemma data; the rewriting itself
    -- uses kabstract + mkCongrArg, not Simp.main.
    let simpTheorems <- getSimpTheorems
    let candidates <- simpTheorems.post.getMatch reduced
    let lemmas <- candidates.filterMapM fun thm => do
      try pure (some (<- thm.getValue))
      catch _ => pure none
    let (final, proof?, truncated) <- rewriteByLemmaLoop reduced lemmas none 64
    if truncated then
      logWarning "kan_simp: reached rewrite step limit; returning partial result (lemmas may be diverging)"
    applyNormalizeResult mvarId final proof?
  | .normalizeDSimp => fun mvarId => do
    -- Definitional normalization: Meta.reduce performs beta, delta,
    -- iota, zeta, and projection reduction directly on the expression.
    let target <- instantiateMVars (<- mvarId.getType)
    let reduced <- Meta.reduce target
      (explicitOnly := false) (skipTypes := false) (skipProofs := false)
    let newGoal <- mvarId.change reduced
    pure [newGoal]
  | .normalizeSimpOnly lemmaStxs => fun mvarId => do
    -- Elaborate each lemma syntax to a proof expression,
    -- then rewrite using the custom rewrite loop.
    let lemmas <- lemmaStxs.mapM fun stx =>
      Lean.Elab.Term.elabTerm stx none
    let target <- instantiateMVars (<- mvarId.getType)
    let reduced <- Meta.reduce target
      (explicitOnly := false) (skipTypes := false) (skipProofs := false)
    let (final, proof?, truncated) <- rewriteByLemmaLoop reduced lemmas none 64
    if truncated then
      logWarning "kan_simp_only: reached rewrite step limit; returning partial result (lemmas may be diverging)"
    applyNormalizeResult mvarId final proof?
  | .colimitDecomposition stx => fun mvarId => do
    -- Manual recursor construction: look up the casesOn constant,
    -- build the motive by abstracting the discriminant (and, for
    -- indexed inductives, each index) from the goal, assign
    -- parameters/motive/indices/discriminant, and intro constructor
    -- arguments in each branch.
    --
    -- For an inductive with k indices, casesOn's motive has type
    --   (i₁ : I₁) → ... → (iₖ : Iₖ) → IndType params i₁ ... iₖ → Sort u
    -- so the motive is wrapped with one lambda per index.  The motive
    -- body does not generalize indices that appear in the goal; for
    -- dependent elimination where the goal varies with the index, the
    -- resulting branch goals remain well-typed but will not be
    -- automatically simplified.
    let e <- Lean.Elab.Term.elabTerm stx none
    unless e.isFVar do
      throwError "colimitDecomposition: expected a free variable"
    let fvarId := e.fvarId!
    mvarId.withContext do
      let target <- instantiateMVars (<- mvarId.getType)
      let hypType <- inferType (mkFVar fvarId)
      let hypType <- whnf hypType
      let env <- getEnv
      let .const indName indLevels := hypType.getAppFn
        | throwError "colimitDecomposition: hypothesis is not an inductive type"
      let some indInfo := env.find? indName
        | throwError "colimitDecomposition: {indName} not found"
      let some indVal := inductiveVal? indInfo
        | throwError "colimitDecomposition: {indName} is not an inductive type"
      let typeArgs := hypType.getAppArgs
      -- Extract index terms and their types for motive construction.
      -- A well-typed inductive application has `numParams + numIndices`
      -- arguments, so the index positions are always present.
      let indexTerms : Array Expr := (Array.range indVal.numIndices).map fun i =>
        typeArgs[indVal.numParams + i]!
      let indexTypes <- indexTerms.mapM inferType
      -- Build motive body: abstract the discriminant at bvar 0
      let targetAbs <- kabstract target (mkFVar fvarId) 0
      -- Abstract indices from the inner hypothesis type so that
      -- bvar 0 = last index, bvar (k-1) = first index.  This makes
      -- the inner binder type `IndType params i₁ ... iₖ` reference
      -- the outer index binders via de Bruijn indices.
      let mut innerHypT := hypType
      for i in [0:indVal.numIndices] do
        let indexPos := indVal.numIndices - 1 - i
        innerHypT <- kabstract innerHypT indexTerms[indexPos]! i
      -- Wrap: innermost lambda binds the discriminant, outer lambdas
      -- bind each index with the first index as the outermost binder.
      let mut motive := mkLambda `x BinderInfo.default innerHypT targetAbs
      for i in [0:indVal.numIndices] do
        let indexPos := indVal.numIndices - 1 - i
        motive := mkLambda `i BinderInfo.default indexTypes[indexPos]! motive
      -- Construct the casesOn recursor constant with proper levels:
      -- motive sort level first, then the inductive's own levels.
      let casesOnName := indName ++ `casesOn
      let motiveLevel <- getLevel target
      let casesOn := mkConst casesOnName (motiveLevel :: indLevels)
      let casesOnType <- inferType casesOn
      let (mvars, _, _) <- forallMetaTelescopeReducing casesOnType
      -- Assign type parameters from the hypothesis
      for i in [0:indVal.numParams] do
        let some mvar := mvars[i]?
          | break
        let some arg := typeArgs[i]?
          | break
        mvar.mvarId!.assign arg
      -- Assign the motive
      let motiveIdx := indVal.numParams
      let some motiveMVar := mvars[motiveIdx]?
        | throwError "colimitDecomposition: motive metavar not found"
      motiveMVar.mvarId!.assign motive
      -- Assign index arguments (if any)
      for i in [0:indVal.numIndices] do
        let mvarIdx := indVal.numParams + 1 + i
        let argIdx := indVal.numParams + i
        let some mvar := mvars[mvarIdx]?
          | break
        let some arg := typeArgs[argIdx]?
          | break
        mvar.mvarId!.assign arg
      -- Assign the discriminant
      let discIdx := indVal.numParams + 1 + indVal.numIndices
      let some discMVar := mvars[discIdx]?
        | throwError "colimitDecomposition: discriminant metavar not found"
      discMVar.mvarId!.assign (mkFVar fvarId)
      -- Close the goal with the full casesOn application
      mvarId.assign (mkAppN casesOn mvars)
      -- Intro constructor arguments in each branch to place
      -- fields in the local context (matching cases behavior)
      let branchStart := discIdx + 1
      let mut subgoals : Array MVarId := #[]
      for i in [branchStart:mvars.size] do
        let finalId <- introAllForalls mvars[i]!.mvarId!
        subgoals := subgoals.push finalId
      pure subgoals.toList

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
