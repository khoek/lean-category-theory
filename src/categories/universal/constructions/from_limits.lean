-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete
import categories.walking
import tidy.its

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.initial
open categories.walking
open categories.util.finite

namespace categories.universal

universes u₁ u₂ u₃ u₄

section
variable {J : Type (u₁+1)}
variable [category J]
variable {C : Type (u₂+1)}
variable [category C]
variables {F : Functor J C} {L : LimitCone F} {Z : C} 

private definition Cone_from_map_to_limit (f : Z ⟶ L.terminal_object.cone_point) : Cone F := {
  cone_point    := Z,
  cone_maps     := λ j, f ≫ (L.terminal_object.cone_maps j)
}
private definition ConeMorphism_from_map_to_limit (f : Z ⟶ L.terminal_object.cone_point) : ConeMorphism (Cone_from_map_to_limit f) L.terminal_object := {
  cone_morphism := f
}
end

variable {C : Type (u₁+2)}
variable [category C]

-- PROJECT this construction is unpleasant
open tactic
meta def induction_WalkingParallelPair : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(WalkingParallelPair) := induction h >> skip | _ := failed end))
local attribute [tidy] induction_WalkingParallelPair
local attribute [reducible] ParallelPair_functor._match_2
instance Equalizers_from_Limits [Complete C] : has_Equalizers C := {
  equalizer := λ X Y f g, let lim := limitCone (ParallelPair_functor f g) in {
    equalizer     := lim.terminal_object.cone_point,
    inclusion     := lim.terminal_object.cone_maps WalkingParallelPair._1,
    witness       := let commutativity := @Cone.commutativity_lemma _ _ _ _ _ lim.terminal_object WalkingParallelPair._1 WalkingParallelPair._2 in 
                     begin
                       dsimp,
                       erw commutativity Two._0,
                       erw commutativity Two._1,
                     end,
    map           := begin
                       -- PROJECT this is really ugly! Those inductions should work better...
                       tidy,
                       exact k ≫ f,
                       tidy,
                       cases f_1,
                       cases f_1,
                       tidy,
                     end,
    factorisation := ♯,
    uniqueness    := begin
                       tidy,
                       let Z_cone : Cone (ParallelPair_functor f g) := {
                         cone_point := Z,
                         cone_maps := λ j : WalkingParallelPair, a ≫ (lim.terminal_object.cone_maps j),
                      },
                       have p := lim.uniqueness_of_morphisms_to_terminal_object Z_cone ⟨ a, _ ⟩ ⟨ b, _ ⟩,
                       exact congr_arg ConeMorphism.cone_morphism p,
                       -- finally, take care of those placeholders
                       tidy,
                       have c := lim.terminal_object.commutativity,
                       dsimp at c,
                       rw ← @c WalkingParallelPair._1 WalkingParallelPair._2 Two._1,
                       repeat {rw ← category.associativity},
                       rw witness, 
                     end
 }                       
}

instance Products_from_Limits [Complete C] : has_Products C := {
    product := λ {I : Type (u₁+1)} (F : I → C), 
                 let lim_F := limitCone (Functor.fromFunction F) in
                  {
                    product       := lim_F.terminal_object.cone_point,
                    projection    := λ i, lim_F.terminal_object.cone_maps i,
                    uniqueness    := λ Z f g, begin
                                                intros, 
                                                have p := lim_F.uniqueness_of_morphisms_to_terminal_object, 
                                                have q := p _ (ConeMorphism_from_map_to_limit f)
                                                  {cone_morphism := g, commutativity := begin tidy, simp *, end}, -- (`simp *` isn't good in tidy; it's really slow)
                                                tidy,
                                              end,
                    map           := λ Z i, (lim_F.morphism_to_terminal_object_from {
                                              cone_point := Z, 
                                              cone_maps := i
                                           }).cone_morphism
                 }
}

end categories.universal