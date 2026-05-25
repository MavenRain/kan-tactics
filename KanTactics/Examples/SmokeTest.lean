import KanTactics.Tactic.Identity
import KanTactics.Tactic.Precomposition
import KanTactics.Tactic.Transport
import KanTactics.Tactic.Normalize
import KanTactics.Tactic.AdjUnit
import CompCatTheory.Foundation.Category
import CompCatTheory.Foundation.Product

/-!
# KanTactics.Examples.SmokeTest

End-to-end smoke test confirming that `kan-tactics` tactics work on
goals about `CompCatTheory.Category` morphisms.  Since the tactic
implementations operate at the meta-programming level on `Expr` (and
never reference the Category typeclass directly), they are agnostic
to which Category foundation a downstream project uses.

This file verifies that property concretely after the refactor that
removed `kan-tactics`'s duplicate Category layer in favour of
depending on `comp-cat-theory`.
-/

set_option autoImplicit false

universe u v u₂ v₂

open CompCatTheory
open Category

namespace KanTactics.Examples.SmokeTest

section CategoryGoals

variable {C : Type u} [Category.{u, v} C]

/-- `kan_rfl` closes reflexivity on a CompCatTheory identity morphism. -/
example (X : C) : 𝟙 X = 𝟙 X := by kan_rfl

/-- `kan_exact` discharges a goal directly with a categorical lemma. -/
example {A B : C} (f : Hom A B) : 𝟙 A ≫ f = f := by
  kan_exact id_comp f

/-- `kan_exact` discharges a goal directly using the dual `comp_id`. -/
example {A B : C} (f : Hom A B) : f ≫ 𝟙 B = f := by
  kan_exact comp_id f

/-- `kan_apply` closes by backward-chaining a known lemma. -/
example {A B : C} (f : Hom A B) : 𝟙 A ≫ f = f := by
  kan_apply id_comp

/-- `kan_rw` rewrites a CompCatTheory morphism equality.  The transport
    primitive auto-closes residual reflexivity goals. -/
example {A B : C} (f g : Hom A B) (h : f = g) : f ≫ 𝟙 B = g ≫ 𝟙 B := by
  kan_rw [h]

/-- `kan_intros` introduces categorical hypotheses, then `kan_exact` closes. -/
example {A B : C} : ∀ (f : Hom A B), 𝟙 A ≫ f = f := by
  kan_intros f
  kan_exact id_comp f

end CategoryGoals

section ProductCategoryGoals

variable {C : Type u} {D : Type u₂}
  [Category.{u, v} C] [Category.{u₂, v₂} D]

/-- Product composition `.fst` reduces definitionally; `kan_rfl` closes. -/
example {X Y Z : C × D}
    (f : @Hom (C × D) _ X Y) (g : @Hom (C × D) _ Y Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := by kan_rfl

/-- Same for `.snd`. -/
example {X Y Z : C × D}
    (f : @Hom (C × D) _ X Y) (g : @Hom (C × D) _ Y Z) :
    (f ≫ g).2 = f.2 ≫ g.2 := by kan_rfl

/-- `kan_simp` simplifies using CompCatTheory's `@[simp]` lemmas. -/
example {X Y Z : C × D}
    (f : @Hom (C × D) _ X Y) (g : @Hom (C × D) _ Y Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := by kan_simp

end ProductCategoryGoals

end KanTactics.Examples.SmokeTest
