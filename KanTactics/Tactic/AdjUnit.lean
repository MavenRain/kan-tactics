import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.AdjUnit

Tactics derived from adjunction units: `kan_intro` and `kan_intros`.

## Primitive: kan_intro (unit of the exponential adjunction)

The exponential adjunction in the category of types:

    Hom(Gamma x A, B) ~= Hom(Gamma, A -> B)

Its unit eta : Gamma -> (A -> Gamma x A) is the "pairing" map.
At the level of proof states, this adjunction says:

    To prove (A -> B), it suffices to prove B with A in context.

The functor K embeds extended-context goals (Gamma, x:A |- B) into
function goals (Gamma |- A -> B).  The unit of the adjunction is
the "intro" step.

The Kan extension (Lan_K Id)(Gamma |- forall x:A, B(x)) yields:
- Comma category: one object, the context extension with x:A
- Subgoal: Gamma, x:A |- B(x)
- Assembly: fun (x : A) => proof_of_Bx

## Derived: kan_intros (iterated adjunction units)

Multiple introductions compose as iterated currying:

    A -> B -> C  ~=  (A x B) -> C

Each intro step is a separate Kan extension, and their composition
is again a Kan extension (Kan extensions compose along identity).

With explicit names, `kan_intros x y z` expands to
`kan_intro x; kan_intro y; kan_intro z`.

With no arguments, `kan_intros` inspects the goal for all leading
forall-binders and introduces each by name.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Introduce one binder via the exponential adjunction unit.  (Primitive) -/
elab "kan_intro " x:ident : tactic => kanExtend (.adjunctionUnitIntro x.getId)

/-- Introduce all leading forall-binders by repeated `kan_intro`. -/
private partial def introAll : TacticM Unit := do
  let mvarId <- getMainGoal
  let target <- instantiateMVars (<- mvarId.getType)
  if target.isForall then
    let stx := mkIdent target.bindingName!
    evalTactic (<- `(tactic| kan_intro $stx:ident))
    introAll
  else
    pure ()

/-- Introduce multiple binders via iterated adjunction units.
    With no arguments, introduces all leading binders.
    Derived from `kan_intro`. -/
elab "kan_intros" xs:(ppSpace ident)* : tactic => do
  if xs.isEmpty then
    introAll
  else
    xs.forM fun x => do evalTactic (<- `(tactic| kan_intro $x:ident))
