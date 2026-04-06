import KanTactics.Category.Functor

/-!
# KanTactics.Category.NatTrans

Natural transformations between functors.

A natural transformation eta : F ==> G assigns to each object X
a morphism eta_X : F(X) -> G(X), satisfying the naturality square:

    F(f) >> eta_Y = eta_X >> G(f)

for every morphism f : X -> Y.

In the Kan extension framework, natural transformations appear as:
- The unit eta : F ==> (Lan_K F) o K
- The universal morphism sigma : Lan_K F ==> G
- The factorization condition relating them
-/


set_option autoImplicit false

universe u1 v1 u2 v2

open Category

/-- A natural transformation from functor F to functor G. -/
structure NatTrans {C : Type u1} {D : Type u2}
    [Category.{u1, v1} C] [Category.{u2, v2} D]
    (F G : Functor C D) where
  /-- The component at each object. -/
  app : (X : C) -> Hom (F.obj X) (G.obj X)
  /-- Naturality: F(f) >> eta_Y = eta_X >> G(f). -/
  naturality : {X Y : C} -> (f : Hom X Y) ->
    F.map f >> app Y = app X >> G.map f

namespace NatTrans

variable {C : Type u1} {D : Type u2}
variable [Category.{u1, v1} C] [Category.{u2, v2} D]

/-- The identity natural transformation on a functor F. -/
def identity (F : Functor C D) : NatTrans F F where
  app := fun _ => idn
  naturality := fun f => by rw [id_comp, comp_id]

/-- Vertical composition of natural transformations.
    Given eta : F ==> G and mu : G ==> H, produces eta o mu : F ==> H. -/
def vcomp {F G H : Functor C D}
    (eta : NatTrans F G) (mu : NatTrans G H) : NatTrans F H where
  app := fun X => eta.app X >> mu.app X
  naturality := fun {X Y} f => by
    -- F(f) >> (eta_Y >> mu_Y) = (eta_X >> mu_X) >> H(f)
    rw [<- assoc, eta.naturality, assoc, mu.naturality, <- assoc]

end NatTrans
