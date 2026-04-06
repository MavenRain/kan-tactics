import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.AdjUnit

Tactics derived from adjunction units: `kan_intro` and `kan_intros`.

## intro as the unit of the exponential adjunction

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

## intros as iterated adjunction units

Multiple introductions compose as iterated currying:

    A -> B -> C  ~=  (A x B) -> C

Each intro step is a separate Kan extension, and their composition
is again a Kan extension (Kan extensions compose along identity).
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Intro as the unit of the exponential adjunction.

    For a goal (forall (x : A), B(x)):
    1. Comma category: the single context extension (Gamma, x:A)
    2. Subgoal: B(x) in the extended context
    3. Assembly: fun (x : A) => proof -/
def introKan (name : Name) : KanComputation where
  name := "adjunction unit (intro)"
  kind := .adjunctionUnit
  execute := fun mvarId => do
    let (_, newMVarId) <- mvarId.intro name
    pure [newMVarId]

/-- Intros with explicit names: iterated exponential adjunction units.

    Each name triggers one application of the adjunction unit.
    The composition of n units corresponds to n-fold currying:
    A1 -> A2 -> ... -> An -> B  ~=  (A1 x ... x An) -> B -/
def introsKan (names : Array Name) : KanComputation where
  name := "adjunction unit (intros)"
  kind := .adjunctionUnit
  execute := fun mvarId => do
    let (_, newMVarId) <- mvarId.introN names.size names.toList
    pure [newMVarId]

/-- Intros with no names: apply the adjunction unit maximally.

    Introduces all leading binders, currying the goal as far
    as the type structure allows. -/
def introsAllKan : KanComputation where
  name := "adjunction unit (intros *)"
  kind := .adjunctionUnit
  execute := fun mvarId => do
    let (_, newMVarId) <- mvarId.intros
    pure [newMVarId]

/-- Introduce one binder via the exponential adjunction unit. -/
elab "kan_intro " x:ident : tactic => kanExtend (introKan x.getId)

/-- Introduce multiple binders via iterated adjunction units.
    With no arguments, introduces all leading binders. -/
elab "kan_intros" xs:(ppSpace ident)* : tactic => do
  if xs.isEmpty then
    kanExtend introsAllKan
  else
    kanExtend (introsKan (xs.map Syntax.getId))
