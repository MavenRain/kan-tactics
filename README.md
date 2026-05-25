# kan-tactics

A Lean 4 library demonstrating Mac Lane's dictum that
**all concepts are Kan extensions**, by implementing every standard
proof tactic as a specific instance of a single `kanExtend` entry point.

The categorical foundation (Category, Functor, NatTrans, left/right
Kan extensions) is provided by [comp-cat-theory], a sibling library
that develops category theory from scratch without Mathlib and proves
that every standard categorical construction (Adjunction, Limit,
Colimit, End, Coend, Monoidal, SymmetricMonoidal, Optic, ...) collapses
to a Kan extension.

[comp-cat-theory]: https://github.com/MavenRain/comp-cat-theory

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
  Tactic/
    Core.lean            KanExtensionKind, kanExtend (the universal entry point)
    Identity.lean        kan_rfl, kan_exact
    Precomposition.lean  kan_apply, kan_refine
    AdjUnit.lean         kan_intro, kan_intros
    Transport.lean       kan_rw, kan_calc_trans
    Normalize.lean       kan_simp, kan_dsimp, kan_simp_only
    Colimit.lean         kan_constructor, kan_use, kan_exists
    Decompose.lean       kan_cases, kan_rcases
    InitialAlgebra.lean  kan_induction

  Examples/
    LanAlongIdentity.lean   Worked proof that Lan_id F ≅ F
```

The categorical foundation lives in [comp-cat-theory]:

```
CompCatTheory/
  Foundation/    Category, Opposite, Product, Terminal, TwistedArrow
  Primitive/     KanExtension  (THE primitive)
  Collapse/      Adjunction, Limit, Colimit, End, Coend, Exponential,
                 Monoidal, SymmetricMonoidal, Optic, MonadAlgebra,
                 FreeAlgebra, Factorization, SubobjectClassifier
```

Each `Collapse/*.lean` file proves the corresponding construction is
a Kan extension; `kan-tactics` reuses this foundation rather than
maintaining a parallel copy.

The tactic implementations in `KanTactics/Tactic/*.lean` are pure
Lean meta-programming on `Expr` (using `kabstract`, `mkCongrArg`,
`Meta.reduce`, `forallMetaTelescopeReducing`).  They do not reference
the Category typeclass directly; the typeclass is the conceptual
foundation that justifies why each tactic is a Kan extension, not a
runtime input to the tactic.

## The 8 primitive Kan extension kinds

`KanExtensionKind` (in `Tactic/Core.lean`) is the minimal spanning set:

| Variant | Tactic surface | Categorical origin |
|---|---|---|
| `precomposition` | `kan_apply` | Backward extension along a morphism |
| `precompositionRefine` | `kan_refine`, `kan_exact` | Partial precomposition with holes |
| `adjunctionUnitIntro` | `kan_intro`, `kan_intros` | Unit of the exponential adjunction |
| `transport` | `kan_rw`, `kan_calc_trans` | Substitution Kan extension |
| `normalize` | `kan_simp` | Full transport category of simp lemmas |
| `normalizeDSimp` | `kan_dsimp` | Sub-groupoid of definitional equalities |
| `normalizeSimpOnly` | `kan_simp_only` | Restricted transport lemma set |
| `colimitDecomposition` | `kan_cases`, `kan_rcases` | Coproduct elimination |

Every tactic invokes `kanExtend` with a `KanExtensionKind` value;
derived tactics (`kan_exact`, `kan_rfl`, `kan_intros`, `kan_use`,
`kan_exists`, `kan_constructor`, `kan_calc_trans`, `kan_induction`)
compose primitives via `evalTactic` rather than adding new variants.

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
# Fetch comp-cat-theory and build
lake update
lake build

# Generate documentation (requires doc-gen4; fetched automatically in dev mode)
lake -Kenv=dev update
lake -Kenv=dev build KanTactics:docs

# Docs are written to .lake/build/doc/
open .lake/build/doc/index.html
```

The Lean toolchain is pinned to `leanprover/lean4:v4.30.0-rc1`;
comp-cat-theory uses the same toolchain so the dependency resolves
cleanly.

## Usage

### Standard Lean goals

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

### Categorical goals via comp-cat-theory

```lean
import KanTactics
import CompCatTheory.Foundation.Category

open CompCatTheory Category

example {C : Type u} [Category.{u, v} C] (X : C) : 𝟙 X = 𝟙 X := by
  kan_rfl

example {C : Type u} [Category.{u, v} C] {A B : C} (f : Hom A B) :
    𝟙 A ≫ f = f := by
  kan_exact id_comp f
```

See `KanTactics/Examples/` for additional worked examples, including
`lan_along_identity` (the trivial Kan extension that motivates the
whole approach).

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
