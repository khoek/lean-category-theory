-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import category_theory.universal.complete
-- import category_theory.walking
-- import tidy.its

-- open category_theory
-- open category_theory.initial
-- open category_theory.walking

-- namespace category_theory.universal

-- universes u₁ u₂ u₃ u₄

-- section
-- variable {J : Type u₁}
-- variable [small_category J]
-- variable {C : Type (u₁+1)}
-- variable [large_category C]
-- variables {F : J ⥤ C} {L : LimitCone F} {Z : C} 

-- private def Cone_from_map_to_limit (f : Z ⟶ L.obj.cone_point) : Cone F := {
--   cone_point    := Z,
--   cone_maps     := λ j, f ≫ (L.obj.cone_maps j)
-- }
-- private def ConeMorphism_from_map_to_limit (f : Z ⟶ L.obj.cone_point) : ConeMorphism (Cone_from_map_to_limit f) L.obj := {
--   cone_morphism := f
-- }
-- end

-- variable {C : Type (u₁+1)}
-- variable [large_category C]

-- -- PROJECT this construction is unpleasant
-- section
-- open tactic
-- meta def induction_WalkingParallelPair : tactic unit :=
-- do l ← local_context,
--    at_least_one (l.reverse.map (λ h, do t ← infer_type h, t ← whnf t, match t with | `(WalkingParallelPair) := induction h >> skip | `(Two) := induction h >> skip | _ := failed end)),
--    skip
-- end

-- local attribute [tidy] induction_WalkingParallelPair

-- instance Equalizers_from_Limits [Complete C] : has_Equalizers.{u₁+1 u₁} C := {
--   equalizer := λ X Y f g, let lim := limitCone (ParallelPair_functor f g) in {
--     equalizer     := lim.obj.cone_point,
--     inclusion     := lim.obj.cone_maps WalkingParallelPair._1,
--     witness       := let commutativity := @Cone.commutativity_lemma _ _ _ _ _ lim.obj WalkingParallelPair._1 WalkingParallelPair._2 in 
--                      begin 
--                        erw commutativity Two._0,
--                        erw commutativity Two._1,
--                      end,
--     map           := by obviously,
--     factorisation := by obviously,
--     uniqueness    := begin
--                        tidy,
--                        let Z_cone : Cone (ParallelPair_functor f g) := 
--                        { cone_point := Z,
--                          cone_maps := λ j : WalkingParallelPair, a ≫ (lim.obj.cone_maps j), },
--                        have p := lim.uniqueness Z_cone ⟨ a, _ ⟩ ⟨ b, _ ⟩,
--                        have q := congr_arg ConeMorphism.cone_morphism p,
--                        exact q,
--                        tidy,
--                        have c := lim.obj.commutativity,
--                        dsimp at c,
--                        rw ← @c WalkingParallelPair._1 WalkingParallelPair._2 Two._1,
--                        repeat {rw ← category.assoc},
--                        rw witness,
--                      end
--  }                       
-- }

-- instance Products_from_Limits [Complete C] : has_Products C := {
--     product := λ {I : Type u₁} (F : I → C), 
--                  let lim_F := limitCone (functor.fromFunction F) in
--                   {
--                     product       := lim_F.obj.cone_point,
--                     projection    := λ i, lim_F.obj.cone_maps i,
--                     uniqueness    := λ Z f g _, begin
--                                                   have p := lim_F.uniqueness, 
--                                                   have q := p _ (ConeMorphism_from_map_to_limit f) {cone_morphism := g}, 
--                                                   tidy,
--                                                 end,
--                     map           := λ Z i, (lim_F.«from» { cone_point := Z, cone_maps := i }).cone_morphism
--                  }
-- }

-- end category_theory.universal