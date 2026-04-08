import KanTactics.Tactic.Core
import KanTactics.Tactic.Precomposition

/-!
# KanTactics.Tactic.InitialAlgebra

Induction as a Kan extension along the initial algebra structure map.

## The Initial Algebra Perspective

An inductive type T is the initial F-algebra for its signature
endofunctor F.  For example:

- Nat is the initial algebra of F(X) = 1 + X,
  with structure map [zero, succ] : 1 + Nat -> Nat.

- List A is the initial algebra of F(X) = 1 + A x X,
  with structure map [nil, cons] : 1 + A x List A -> List A.

The recursor T.rec is the unique algebra morphism from the initial
algebra to any other F-algebra.  This is precisely the universal
property of the Kan extension.

## Derived: kan_induction (via kan_apply on the recursor)

The functor K embeds "algebra components" into T:

    K : F(T) -> T   (the algebra structure map)

For Nat, K maps:
- inl(star) |-> zero
- inr(n)   |-> succ(n)

The diagram functor F maps each component to its proof obligation:

    F(inl(star)) = P(zero)           (base case)
    F(inr(n))    = P(n) -> P(succ n) (inductive step, with IH)

The Kan extension (Lan_K F)(n : T) at a goal P(n) computes:

    (Lan_K F)(n) = colim_{component, K(component) -> n} F(component)

For Nat, this gives:
- Base: component = inl(star), K(inl(star)) = zero.
  Subgoal: P(zero).
- Step: component = inr(m), K(inr(m)) = succ(m).
  Subgoal: P(m) -> P(succ(m)) (with induction hypothesis).

The colimit assembly is exactly the recursor:

    Nat.rec (base_proof) (step_proof) n : P(n)

Derived by looking up the recursor name from the hypothesis type
and delegating to `kan_apply`.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Structural induction via the initial algebra Kan extension.
    Derived from `kan_apply`: looks up the recursor for the
    hypothesis type, then delegates. -/
elab "kan_induction " e:term : tactic => do
  let mvarId <- getMainGoal
  mvarId.withContext do
    let expr <- Lean.Elab.Term.elabTerm e none
    let recName <- (exprAsFVarId expr).elim
      (pure `Nat.rec)
      fun fvarId => do
        let localDecl <- fvarId.getDecl
        let type <- instantiateMVars localDecl.type
        let typeName := type.getAppFn.constName?.getD Name.anonymous
        pure (typeName ++ `rec)
    let stx := mkIdent recName
    evalTactic (<- `(tactic| kan_apply $stx))
