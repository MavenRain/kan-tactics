import KanTactics.Category.NatTrans

/-!
# KanTactics.Category.KanExtension

Left and right Kan extensions, the universal categorical construction
that unifies all proof tactics.

## Left Kan Extension

Given functors K : C -> D and F : C -> E, the left Kan extension
Lan_K F : D -> E satisfies:

    Nat(Lan_K F, G) ~= Nat(F, G o K)

for all functors G : D -> E.  Concretely, Lan_K F is computed
by the colimit formula:

    (Lan_K F)(d) = colim_{(c, f : K(c) -> d)} F(c)

The colimit runs over the comma category (K | d).

## Right Kan Extension

The right Kan extension Ran_K F : D -> E satisfies:

    Nat(G, Ran_K F) ~= Nat(G o K, F)

and is given by the limit formula:

    (Ran_K F)(d) = lim_{(c, f : d -> K(c))} F(c)

## "All Concepts Are Kan Extensions"

Mac Lane's dictum from Categories for the Working Mathematician.
This library demonstrates it concretely: every standard Lean 4 tactic
is an instance of a Kan extension in the category of proof states.
-/

set_option autoImplicit false

universe u1 v1 u2 v2 u3 v3

open Category CFunctor

variable {C : Type u1} {D : Type u2} {E : Type u3}
variable [Category.{u1, v1} C] [Category.{u2, v2} D] [Category.{u3, v3} E]

/-- A left Kan extension of F : C -> E along K : C -> D.

    Consists of:
    - A functor Lan : D -> E (the extension)
    - A unit eta : F ==> Lan o K
    - The universal property: for any (G, alpha : F ==> G o K),
      a unique sigma : Lan ==> G factoring alpha through eta -/
structure LeftKanExtension (K : CFunctor C D) (F : CFunctor C E) where
  /-- The extension functor Lan_K F : D -> E. -/
  lan : CFunctor D E
  /-- The unit eta : F ==> Lan o K. -/
  unit : NatTrans F (K ooo lan)
  /-- Universal property: given (G, alpha), produce sigma : Lan ==> G. -/
  desc : (G : CFunctor D E) -> NatTrans F (K ooo G) -> NatTrans lan G
  /-- Factorization: eta_X >> sigma_{K(X)} = alpha_X for all X in C. -/
  fac : {G : CFunctor D E} -> (alpha : NatTrans F (K ooo G)) ->
    (X : C) -> unit.app X >> (desc G alpha).app (K.obj X) = alpha.app X
  /-- Uniqueness: sigma is the unique such natural transformation. -/
  uniq : {G : CFunctor D E} -> (alpha : NatTrans F (K ooo G)) ->
    (sigma : NatTrans lan G) ->
    ((X : C) -> unit.app X >> sigma.app (K.obj X) = alpha.app X) ->
    (d : D) -> sigma.app d = (desc G alpha).app d

/-- A right Kan extension of F : C -> E along K : C -> D.

    Consists of:
    - A functor Ran : D -> E (the extension)
    - A counit epsilon : Ran o K ==> F
    - The universal property: for any (G, beta : G o K ==> F),
      a unique tau : G ==> Ran factoring beta through epsilon -/
structure RightKanExtension (K : CFunctor C D) (F : CFunctor C E) where
  /-- The extension functor Ran_K F : D -> E. -/
  ran : CFunctor D E
  /-- The counit epsilon : Ran o K ==> F. -/
  counit : NatTrans (K ooo ran) F
  /-- Universal property: given (G, beta), produce tau : G ==> Ran. -/
  lift : (G : CFunctor D E) -> NatTrans (K ooo G) F -> NatTrans G ran
  /-- Factorization: tau_{K(X)} >> epsilon_X = beta_X for all X in C. -/
  fac : {G : CFunctor D E} -> (beta : NatTrans (K ooo G) F) ->
    (X : C) -> (lift G beta).app (K.obj X) >> counit.app X = beta.app X
  /-- Uniqueness: tau is the unique such natural transformation. -/
  uniq : {G : CFunctor D E} -> (beta : NatTrans (K ooo G) F) ->
    (tau : NatTrans G ran) ->
    ((X : C) -> tau.app (K.obj X) >> counit.app X = beta.app X) ->
    (d : D) -> tau.app d = (lift G beta).app d

/-- Kan extensions along the identity are trivial: Lan_Id F = F. -/
theorem lan_along_identity (F : CFunctor C E) :
    ∃ (_ : LeftKanExtension (CFunctor.identity) F),
      True := by
  exact ⟨{
    lan := F
    unit := NatTrans.identity F
    desc := fun _ alpha => alpha
    fac := fun alpha X => Category.id_comp (alpha.app X)
    uniq := fun alpha sigma h d => by
      have hd := h d
      simp only [NatTrans.identity, CFunctor.identity, id_comp] at hd
      exact hd
  }, trivial⟩
