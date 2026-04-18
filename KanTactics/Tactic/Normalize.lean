import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Normalize

Tactics derived from normalization Kan extensions:
`kan_simp`, `kan_dsimp`, and `kan_simp_only`.

All three are primitive.  They use different lemma sets and different
result-processing paths; none can simulate another.

## kan_simp as automated colimit search (Primitive)

The simplifier searches for a path through the "transport category",
the category whose objects are types/propositions and whose morphisms
are equational rewrites (simp lemmas).

Given a goal P, `kan_simp` searches for a sequence of transports
(each a Kan extension) that reduce P to True or to a simpler form:

    P ->[h1] P' ->[h2] P'' ->[h3] ... ->[hn] True

Each step hi is a transport Kan extension, and their composition is
itself a Kan extension (Kan extensions compose).  The automation lies
in the *search* for the right sequence.

Categorically, `kan_simp` computes the free Kan extension: it
searches the comma category of available simp lemmas for a
factorization that simplifies the goal.

### Scope

`kan_simp` reads the environment's `@[simp]` lemmas but rewrites
via `kabstract + mkCongrArg` rather than Lean's `Simp.main`.  It
does **not** handle: conditional simp lemmas (side conditions),
congruence rewriting under binders, `Iff` lemmas, or user-supplied
simp-set configuration.  A 64-step rewrite limit applies; when
reached, a warning is logged and the partial result is returned.
This covers unconditional equality lemmas applied at the top of
the goal; goals needing deeper or conditional simplification are
outside the scope.

## kan_dsimp: definitional normalization (Primitive)

`kan_dsimp` restricts the transport category to definitional
equalities, which form a sub-groupoid of the full equality
groupoid.  Since definitional equalities are checked by the
kernel, `kan_dsimp` produces a definitionally equal term with no
propositional proof obligation.

### Scope

Implemented as `Meta.reduce` with all reduction flags enabled
(beta, delta, iota, zeta, projection).  Does not consult
user-tagged `@[simp]` definitional lemmas or custom simp sets.

## kan_simp_only: restricted normalization (Primitive)

`kan_simp_only [lemmas]` restricts the comma category to a
specified set of simp lemmas.  Only the given lemmas contribute
objects to the comma category, giving fine-grained control over
which transports are allowed.

### Scope

Shares `kan_simp`'s scope restrictions (no conditional lemmas, no
congruence under binders, no `Iff`).  The 64-step limit also
applies; a warning is logged when reached.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Simplify using all registered lemmas.  (Primitive) -/
elab "kan_simp" : tactic => kanExtend .normalize

/-- Definitionally simplify (no propositional proofs generated).  (Primitive) -/
elab "kan_dsimp" : tactic => kanExtend .normalizeDSimp

/-- Simplify using only the specified lemmas.  (Primitive) -/
elab "kan_simp_only" "[" lemmas:term,* "]" : tactic =>
  kanExtend (.normalizeSimpOnly lemmas.getElems)
