# kan-tactics

A Lean 4 library demonstrating Mac Lane's dictum that
**all concepts are Kan extensions**, by implementing every standard
proof tactic as a specific instance of a single `kanExtend` entry point.

No Mathlib dependency.  The category theory (Category, Functor,
NatTrans, left/right Kan extensions) is developed from scratch.

## Motivation

In the category **Proof** of proof states:

- Objects are sequents (context |- goal).
- Morphisms are proof terms witnessing entailment.

A tactic T corresponds to a left Kan extension.  Given an embedding
K : C -> Proof of "structured" goals and a diagram F : C -> Proof,
executing T on a goal means computing

```
(Lan_K F)(goal) = colim_{(c, f : K(c) -> goal)} F(c)
```

The colimit runs over the comma category (K | goal).  Each object
in this comma category contributes a subgoal (via F), and the
colimit assembly combines them into a proof of the original goal.

## Architecture

```
KanTactics/
  Category/
    Basic.lean           Category typeclass, notation
    Functor.lean         Functor, identity, composition
    NatTrans.lean        NatTrans, identity, vertical composition
    KanExtension.lean    LeftKanExtension, RightKanExtension

  Tactic/
    Core.lean            KanComputation, kanExtend (the universal entry point)
    Identity.lean        kan_rfl, kan_exact
    Precomposition.lean  kan_apply, kan_refine
    AdjUnit.lean         kan_intro, kan_intros
    Transport.lean       kan_rw, kan_calc_trans
    Normalize.lean       kan_simp, kan_dsimp, kan_simp_only
    Colimit.lean         kan_constructor, kan_use, kan_exists
    Decompose.lean       kan_cases, kan_rcases
    InitialAlgebra.lean  kan_induction
```

Every tactic file constructs a `KanComputation` and passes it to
`kanExtend`.  The `KanComputation` structure records:

- **name**: human-readable identifier.
- **kind**: which categorical construction (`KanExtensionKind`).
- **execute**: the function that computes the comma category,
  assigns a proof to the goal, and returns new subgoals.

## Tactic reference

| Tactic | Kan extension kind | Categorical interpretation |
|---|---|---|
| `kan_rfl` | Identity | Lan of Id along the diagonal; colimit is Eq.refl when sides are def-eq |
| `kan_exact e` | Identity | Trivial extension (Lan_Id F); the term e is the proof directly |
| `kan_apply e` | Precomposition | Backward extension along a morphism; reduces goal to domain of e |
| `kan_refine e` | Precomposition | Partial precomposition; each placeholder is an undetermined colimit component |
| `kan_intro x` | Adjunction unit | Unit of the exponential adjunction; currying A -> B into (x:A |- B) |
| `kan_intros` | Adjunction unit | Iterated currying (composed adjunction units) |
| `kan_rw [h1, <-h2]` | Transport | Transport along equality paths; each rewrite is a substitution Kan extension |
| `kan_calc_trans b` | Transport | Transitivity via Eq.trans; splits a = c into a = b and b = c |
| `kan_simp` | Normalize | Automated search in the transport category of simp lemmas |
| `kan_dsimp` | Normalize | Restricted to the sub-groupoid of definitional equalities |
| `kan_simp_only [h]` | Normalize | Transport category restricted to the given lemma set |
| `kan_constructor` | Colimit injection | Select the first constructor (coproduct injection) |
| `kan_use e` | Colimit injection | Existential witness; restricts comma category to injection at e |
| `kan_exists e` | Colimit injection | Synonym for `kan_use` |
| `kan_cases h` | Colimit decomposition | Coproduct elimination; one subgoal per constructor |
| `kan_rcases h` | Colimit decomposition | Iterated coproduct elimination (basic recursive cases) |
| `kan_induction n` | Initial algebra | Extension along the initial algebra structure map; recursor is the unique morphism |

## Building

```sh
# Build the library
lake build

# Generate documentation (requires doc-gen4; fetched automatically in dev mode)
lake -Kenv=dev update
lake -Kenv=dev build KanTactics:docs

# Docs are written to .lake/build/doc/
open .lake/build/doc/index.html
```

Adjust the version in `lean-toolchain` if it does not match your
installed toolchain.

## Usage

```lean
import KanTactics

example : 1 + 1 = 2 := by kan_rfl

example (h : a = b) (hb : b = c) : a = c := by
  kan_rw [h]
  kan_exact hb

example : Nat -> Nat -> Nat := by
  kan_intros x y
  kan_exact x + y

example : ∃ n : Nat, n = 0 := by
  kan_exists 0
  kan_rfl
```

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
