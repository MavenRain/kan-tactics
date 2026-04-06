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

## Induction as Kan Extension

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
-/

import KanTactics.Tactic.Core

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Induction as Kan extension along the initial algebra structure map.

    Decomposes a goal P(n) into base cases and inductive steps
    according to the constructors of the inductive type of n.

    Each constructor contributes one object to the comma category:
    - Non-recursive constructors yield base-case subgoals
    - Recursive constructors yield step subgoals with IH

    The assembly applies the recursor (the unique initial algebra
    morphism) to combine all branch proofs. -/
def inductionKan (stx : Syntax) : KanComputation where
  name := "initial algebra (induction)"
  kind := .initialAlgebra
  execute := fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    (exprAsFVarId e).elimM
      -- Not a free variable: the recursor application will fail
      -- with a clear diagnostic from the kernel
      (do let recConst <- mkConstWithFreshMVarLevels `Nat.rec
          mvarId.apply recConst)
      fun fvarId => do
        -- Determine the inductive type and its recursor
        let localDecl <- fvarId.getDecl
        let type <- instantiateMVars localDecl.type
        let typeName := type.getAppFn.constName?.getD Name.anonymous
        let recName := typeName ++ `rec
        -- The recursor IS the unique initial algebra morphism.
        -- Applying it computes the Kan extension at this goal.
        let recConst <- mkConstWithFreshMVarLevels recName
        mvarId.apply recConst

/-- Structural induction via the initial algebra Kan extension. -/
elab "kan_induction " e:term : tactic => kanExtend (inductionKan e)
