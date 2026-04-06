import KanTactics.Category.Basic

/-!
# KanTactics.Category.Functor

Functors between categories.

In the Kan extension framework, functors play two roles:
- K : C -> D is the "embedding" along which we extend
- F : C -> E is the "diagram" we wish to extend to all of D

A functor preserves the categorical structure: it maps objects to
objects and morphisms to morphisms, respecting identity and composition.
-/


set_option autoImplicit false

universe u1 v1 u2 v2 u3 v3

open Category

/-- A functor from category C to category D. -/
structure Functor (C : Type u1) (D : Type u2)
    [Category.{u1, v1} C] [Category.{u2, v2} D] where
  /-- The object mapping. -/
  obj : C -> D
  /-- The morphism mapping. -/
  map : {X Y : C} -> Hom X Y -> Hom (obj X) (obj Y)
  /-- Functors preserve identity. -/
  map_id : {X : C} -> map (idn : Hom X X) = idn
  /-- Functors preserve composition. -/
  map_comp : {X Y Z : C} -> (f : Hom X Y) -> (g : Hom Y Z) ->
    map (f >> g) = map f >> map g

namespace Functor

variable {C : Type u1} {D : Type u2} {E : Type u3}
variable [Category.{u1, v1} C] [Category.{u2, v2} D] [Category.{u3, v3} E]

/-- The identity functor on a category. -/
def identity : Functor C C where
  obj := fun X => X
  map := fun f => f
  map_id := rfl
  map_comp := fun _ _ => rfl

/-- Composition of functors F : C -> D and G : D -> E. -/
def comp (F : Functor C D) (G : Functor D E) : Functor C E where
  obj := fun X => G.obj (F.obj X)
  map := fun f => G.map (F.map f)
  map_id := by rw [F.map_id, G.map_id]
  map_comp := fun f g => by rw [F.map_comp, G.map_comp]

scoped infixr:80 " ooo " => Functor.comp

end Functor
