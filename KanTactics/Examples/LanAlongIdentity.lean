import CompCatTheory.Foundation.Category
import CompCatTheory.Primitive.KanExtension

/-!
# KanTactics.Examples.LanAlongIdentity

A worked example demonstrating that for every functor `F : C ⥤ D`, the
left Kan extension of `F` along the identity functor on `C` exists and
equals `F`.  The unit is the identity natural transformation, the
universal arrow is identity, and the factorization and uniqueness
conditions both reduce to the left identity law of composition.

This is the simplest illustration of Mac Lane's dictum that "all
concepts are Kan extensions": the identity functor is itself the
trivial Kan extension of itself along itself.

The example uses the `CompCatTheory` foundation directly, since
`KanTactics` now depends on `comp-cat-theory` for its categorical
primitives (Category, Functor, NatTrans, LeftKanExtension).
-/

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

open CompCatTheory
open Category Functor NatTrans

namespace KanTactics.Examples

/-- The left Kan extension of `F : C ⥤ D` along the identity functor on
    `C` exists and is given by `F` itself with the identity unit. -/
theorem lan_along_identity
    {C : Type u₁} {D : Type u₂}
    [Category.{u₁, v₁} C] [Category.{u₂, v₂} D]
    (F : C ⥤ D) :
    ∃ (_ : LeftKanExtension (idFunctor C) F), True := by
  exact ⟨{
    functor := F
    unit := idNat F
    desc := fun α => α
    fac := fun α X => by
      show 𝟙 (F.obj X) ≫ α.app X = α.app X
      exact id_comp (α.app X)
    uniq := fun α β h Y => by
      have hY := h Y
      show β.app Y = α.app Y
      have : 𝟙 (F.obj Y) ≫ β.app Y = α.app Y := hY
      exact (id_comp (β.app Y)).symm.trans this
  }, trivial⟩

end KanTactics.Examples
