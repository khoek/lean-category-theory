-- -- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import category_theory.universal.complete

-- open category_theory
-- open category_theory.initial
-- open category_theory.universal

-- namespace category_theory.universal.lemmas.cones_in_functor_categories

-- universes j u₁ u₂

-- variable {J : Type u₁}
-- variable [small_category J]
-- variable {C : Type u₁}
-- variable [small_category C]
-- variable {D : Type (u₁+1)}
-- variable [large_category D]

-- @[back] lemma uniqueness_of_morphisms_to_terminal_object_cone_point 
--   {Z : D}
--   {G : J ↝ D}
--   {L : LimitCone G}
--   (cone_maps : Π j : J, Z ⟶ (G j)) 
--   (commutativity : Π j k : J, Π f : j ⟶ k, (cone_maps j) ≫ (G.map f) = cone_maps k)
--   (f g : Z ⟶ L.obj.cone_point)
--   (commutativity_f : Π j : J, f ≫ (L.obj.cone_maps j) = cone_maps j)
--   (commutativity_g : Π j : J, g ≫ (L.obj.cone_maps j) = cone_maps j)
--    : f = g :=
-- begin
--   let cone : Cone G := { cone_point := Z, cone_maps := cone_maps },
--   let cone_morphism_f : ConeMorphism cone L.obj := { cone_morphism := f },
--   let cone_morphism_g : ConeMorphism cone L.obj := { cone_morphism := g },
--   exact congr_arg ConeMorphism.cone_morphism (L.uniqueness cone cone_morphism_f cone_morphism_g), 
-- end

-- -- TODO find a better home
-- lemma bifunctor_naturality  
-- (F : J ↝ (C ↝ D))
-- (X Y : C)
-- (f : X ⟶ Y)
-- (j k : J)
-- (g : j ⟶ k)
--   : ((F j).map f) ≫ ((F.map g) Y)
--   = ((F.map g) X) ≫ ((F k).map f) := by obviously

-- @[simp] lemma cone_in_functor_category 
-- (F : J ↝ (C ↝ D))
-- (X Y : C)
-- (f : X ⟶ Y)
-- (j k : J)
-- (g : j ⟶ k)
-- (cone : Cone F)
-- : ((cone.cone_maps j) X) ≫ ((F j).map f) ≫ 
--       ((F.map g) Y) =
--     ((cone.cone_maps k) X) ≫ ((F k).map f) :=
-- by obviously

-- @[simp] lemma cone_in_functor_category_naturality
-- (F : J ↝ (C ↝ D))
-- (X Y : C)
-- (f : X ⟶ Y)
-- (j : J)
-- (cone : universal.Cone F)
--   : ((cone.cone_point).map f) ≫ ((cone.cone_maps j) Y) =
--     ((cone.cone_maps j) X) ≫ ((F j).map f) := by obviously

-- @[simp] lemma cone_commutativity_in_FunctorCategory
-- (F : J ↝ (C ↝ D))
-- (X : C)
-- (j k : J)
-- (f : j ⟶ k) 
-- (Y : Cone F)
--  : ((Y.cone_maps j) X) ≫ ((F.map f) X) = (Y.cone_maps k) X := 
-- by obviously

-- @[simp] lemma cone_commutativity_in_FunctorCategory_assoc
-- (F : J ↝ (C ↝ D))
-- (X : C)
-- (j k : J)
-- (f : j ⟶ k) 
-- (Y : Cone F)
-- (Z : D)
-- (z : ((F k) X) ⟶ Z)
--  : ((Y.cone_maps j) X) ≫ ((F.map f) X) ≫ z = (Y.cone_maps k) X ≫ z := by obviously

-- @[simp] lemma cone_morphism_commutativity_in_FunctorCategory
-- (F : J ↝ (C ↝ D))
-- (X : C)
-- (j : J)
-- (Y Z : Cone F)
-- (φ : ConeMorphism Y Z)
--  : ((φ.cone_morphism) X) ≫ ((Z.cone_maps j) X) = (Y.cone_maps j) X := 
-- by obviously


-- end category_theory.universal.lemmas.cones_in_functor_categories