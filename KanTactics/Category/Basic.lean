/-!
# KanTactics.Category.Basic

Minimal category theory developed from scratch (no Mathlib dependency).

A category C consists of:
- A collection of objects Obj(C)
- For each pair (A, B), a type Hom(A, B) of morphisms
- Identity morphisms and composition
- Satisfying left/right unitality and associativity

These definitions provide the formal mathematical foundation
for characterizing proof tactics as Kan extensions.
-/

set_option autoImplicit false

universe u v

/-- A category with objects in `Type u` and morphisms in `Type v`. -/
class Category (Obj : Type u) where
  /-- The type of morphisms from `A` to `B`. -/
  Hom : Obj -> Obj -> Type v
  /-- Identity morphism. -/
  id : {A : Obj} -> Hom A A
  /-- Composition of morphisms (diagrammatic order: f then g). -/
  comp : {A B C : Obj} -> Hom A B -> Hom B C -> Hom A C
  /-- Left unitality: id >> f = f. -/
  id_comp : {A B : Obj} -> (f : Hom A B) -> comp id f = f
  /-- Right unitality: f >> id = f. -/
  comp_id : {A B : Obj} -> (f : Hom A B) -> comp f id = f
  /-- Associativity: (f >> g) >> h = f >> (g >> h). -/
  assoc : {A B C D : Obj} -> (f : Hom A B) -> (g : Hom B C) -> (h : Hom C D) ->
    comp (comp f g) h = comp f (comp g h)

namespace Category

scoped infixr:80 " >> " => Category.comp
scoped notation "idn" => Category.id

end Category
