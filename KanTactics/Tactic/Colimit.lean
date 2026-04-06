import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Colimit

Tactics derived from colimit injection Kan extensions:
`kan_constructor`, `kan_use`, and `kan_exists`.

## constructor as coproduct injection

An inductive type T with constructors c1, ..., cn is a coproduct
(sum type) of the constructor argument types:

    T ~= A1 + A2 + ... + An

where Ai is the (dependent) product of arguments for constructor ci.

The functor K : coprod Ai -> T is the fold of the constructor
injections.  The Kan extension Lan_K Id at a goal of type T
selects a constructor ci and produces subgoals for its arguments.

The comma category (K | T) has one object per constructor.
`constructor` picks the first one.

## use/exists as existential injection

For (Exists x, P(x)), the single constructor is Exists.intro.
Providing a witness a selects the specific injection

    iota_a : P(a) -> Exists x, P(x)

and produces the subgoal P(a).

Categorically, `use a` is the Kan extension that restricts the
comma category to the single injection at a, then extends.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Look up the first constructor of the goal's inductive type.
    Returns none if the goal type is not an inductive or has no constructors.
    Chains Option combinators: constName? -> find? -> inductiveVal? -> head?. -/
private def firstCtorOf (target : Expr) : MetaM (Option Name) := do
  let env <- getEnv
  pure <| target.getAppFn.constName?
    |>.bind fun name => env.find? name
    |>.bind inductiveVal?
    |>.bind fun val => val.ctors.head?

/-- Apply the first constructor of the goal's inductive type.
    The comma category (K | goal) has one object per constructor;
    we select the first. -/
private def applyFirstConstructor (mvarId : MVarId) : TacticM (List MVarId) := do
  let target <- instantiateMVars (<- mvarId.getType)
  (← firstCtorOf target).elim
    -- No constructor found: let apply fail with a clear message
    (do let ctor <- mkConstWithFreshMVarLevels `True
        mvarId.apply ctor)
    fun ctorName => do
      let ctor <- mkConstWithFreshMVarLevels ctorName
      mvarId.apply ctor

/-- Constructor as coproduct injection.

    For an inductive goal type, finds the first applicable constructor
    and creates subgoals for its arguments.

    Comma category (K | goal) has one object per constructor;
    we select the first. -/
def constructorKan : KanComputation where
  name := "colimit injection (constructor)"
  kind := .colimitInjection
  execute := applyFirstConstructor

/-- Use as existential injection with a given witness.

    For a goal (Exists x, P(x)) with witness a:
    1. Inject via the constructor (Exists.intro)
    2. Fill the witness argument with a
    3. Return P(a) as the remaining subgoal

    Comma category: restricted to the single injection at a.
    Assembly: Exists.intro a (proof of P(a)). -/
def useKan (stx : Syntax) : KanComputation where
  name := "colimit injection (use)"
  kind := .colimitInjection
  execute := fun mvarId => do
    -- Inject into the coproduct, then fill the witness component
    let goals <- applyFirstConstructor mvarId
    goals.head?.elim (pure []) fun witnessGoal => do
      let witness <- Lean.Elab.Term.elabTerm stx (some (<- witnessGoal.getType))
      witnessGoal.assign witness
      pure goals.tail

/-- Exists as existential injection (synonym for use). -/
def existsKan (stx : Syntax) : KanComputation :=
  { useKan stx with name := "colimit injection (exists)" }

/-- Apply the first constructor of the goal's inductive type. -/
elab "kan_constructor" : tactic => kanExtend constructorKan

/-- Provide a witness for an existential or constructor argument. -/
elab "kan_use " e:term : tactic => kanExtend (useKan e)

/-- Provide a witness for an existential (synonym for kan_use). -/
elab "kan_exists " e:term : tactic => kanExtend (existsKan e)
