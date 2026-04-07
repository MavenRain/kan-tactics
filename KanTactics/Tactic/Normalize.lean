import KanTactics.Tactic.Core

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

/-- Simplify using all registered lemmas. -/
elab "kan_simp" : tactic => kanExtend .normalize

/-- Definitionally simplify (no propositional proofs generated). -/
elab "kan_dsimp" : tactic => kanExtend .normalizeDSimp

/-- Simplify using only the specified lemmas. -/
elab "kan_simp_only" "[" lemmas:term,* "]" : tactic =>
  kanExtend (.normalizeSimpOnly lemmas.getElems)
