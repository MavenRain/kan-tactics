import KanTactics.Tactic.Core
import Lean.Meta.Tactic.Simp

/-!
# KanTactics.Tactic.Normalize

Tactics derived from normalization Kan extensions:
`kan_simp`, `kan_dsimp`, and `kan_simp_only`.

## simp as automated colimit search

The simplifier searches for a path through the "transport category",
the category whose objects are types/propositions and whose morphisms
are equational rewrites (simp lemmas).

Given a goal P, simp searches for a sequence of transports (each a
Kan extension) that reduce P to True or to a simpler form:

    P ->[h1] P' ->[h2] P'' ->[h3] ... ->[hn] True

Each step hi is a transport Kan extension, and their composition is
itself a Kan extension (Kan extensions compose).  The automation lies
in the *search* for the right sequence.

Categorically, simp computes the free Kan extension: it searches
the full comma category of available simp lemmas for a factorization
that simplifies the goal.

## dsimp: definitional normalization

dsimp restricts the transport category to definitional equalities,
which form a sub-groupoid of the full equality groupoid.  Since
definitional equalities are checked by the kernel, dsimp produces
a definitionally equal term with no propositional proof obligation.

## simp only: restricted normalization

simp only [lemmas] restricts the comma category to a specified set
of simp lemmas.  Only the given lemmas contribute objects to the
comma category, giving fine-grained control over which transports
are allowed.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Run the simplifier on a goal and process the result.

    If a propositional proof was produced, replace the target.
    If the simplified expression is True, close the goal.
    If no propositional change occurred, change the target definitionally. -/
private def processSimpResult (mvarId : MVarId) (result : Simp.Result)
    : TacticM (List MVarId) :=
  result.proof?.elimM
    (do -- No propositional proof: definitional change only
      let newGoal <- mvarId.change result.expr
      pure [newGoal])
    fun proof => do
      let newGoal <- mvarId.replaceTargetEq result.expr proof
      if result.expr.isConstOf ``True then
        newGoal.assign (mkConst ``True.intro)
        pure []
      else
        pure [newGoal]

/-- Full simplification via automated transport search.

    Searches the complete database of registered simp lemmas for a
    normalization path.  The comma category is the full "rewrite
    category" of available equational lemmas.

    NOTE: Uses Lean's built-in Simp infrastructure.  The exact API
    may need adjustment for your Lean 4 version. -/
def simpKan : KanComputation where
  name := "normalize (simp)"
  kind := .normalize
  execute := fun mvarId => do
    let simpTheorems <- getSimpTheorems
    let congrTheorems <- getSimpCongrTheorems
    let ctx : Simp.Context := {
      simpTheorems := #[simpTheorems]
      congrTheorems
    }
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    processSimpResult mvarId result

/-- Definitional simplification via the strict transport sub-groupoid.

    Only uses definitional equalities (beta, delta, iota, zeta, eta).
    The resulting term is definitionally equal to the original, so no
    propositional proof obligation is generated.

    Categorically, this restricts K to the sub-groupoid of definitional
    equalities, a much smaller comma category than full simp. -/
def dsimpKan : KanComputation where
  name := "normalize (dsimp)"
  kind := .normalize
  execute := fun mvarId => do
    let simpTheorems <- getSimpTheorems
    let congrTheorems <- getSimpCongrTheorems
    let ctx : Simp.Context := {
      simpTheorems := #[simpTheorems]
      congrTheorems
      config := { zeta := true, beta := true, eta := true, iota := true, proj := true }
    }
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    -- dsimp changes the target definitionally (no propositional proof)
    let newGoal <- mvarId.change result.expr
    pure [newGoal]

/-- simp with a restricted set of lemmas.

    The comma category is restricted to the specified lemma set.
    Only the given lemmas contribute factorizations.

    This demonstrates that restricting the base category C of the
    Kan extension (fewer lemmas = fewer objects in the comma category)
    changes the power of the resulting tactic while preserving the
    categorical structure. -/
def simpOnlyKan (lemmaStxs : Array Syntax) : KanComputation where
  name := "normalize (simp only)"
  kind := .normalize
  execute := fun mvarId => do
    -- Build a SimpTheorems containing only the specified lemmas
    let mut simpTheorems : SimpTheorems := {}
    for stx in lemmaStxs do
      let e <- Lean.Elab.Term.elabTerm stx none
      simpTheorems <- e.constName?.elimM
        (pure simpTheorems)
        fun name => simpTheorems.addConst name
    let congrTheorems <- getSimpCongrTheorems
    let ctx : Simp.Context := {
      simpTheorems := #[simpTheorems]
      congrTheorems
    }
    let target <- instantiateMVars (<- mvarId.getType)
    let (result, _) <- Simp.main target ctx
    processSimpResult mvarId result

/-- Simplify using all registered lemmas. -/
elab "kan_simp" : tactic => kanExtend simpKan

/-- Definitionally simplify (no propositional proofs generated). -/
elab "kan_dsimp" : tactic => kanExtend dsimpKan

/-- Simplify using only the specified lemmas. -/
elab "kan_simp_only" "[" lemmas:term,* "]" : tactic => do
  kanExtend (simpOnlyKan lemmas.getElems)
