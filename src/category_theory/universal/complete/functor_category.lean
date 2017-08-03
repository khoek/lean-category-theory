-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..complete

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories
open categories.initial

namespace categories.universal

@[reducible] private definition evaluate_Functor_to_FunctorCategory { J C D : Category } ( F : Functor J (FunctorCategory C D )) ( c : C.Obj ) : Functor J D := {
  onObjects     := λ j, (F.onObjects j).onObjects c,
  onMorphisms   := λ _ _ f, (F.onMorphisms f).components c,
  identities    := ♯,
  functoriality := ♯ 
}

@[reducible] private definition evaluate_Functor_to_FunctorCategory_on_Morphism { J C D : Category } ( F : Functor J (FunctorCategory C D )) { c c' : C.Obj } ( f : C.Hom c c' )
  : NaturalTransformation (evaluate_Functor_to_FunctorCategory F c) (evaluate_Functor_to_FunctorCategory F c') := {
    components := λ j, (F.onObjects j).onMorphisms f,
    naturality := ♯ 
  }

private definition LimitObject_in_FunctorCategory { J C D : Category } [ cmp : Complete D ] ( F : Functor J (FunctorCategory C D) ) : Cone F := {      
  cone_point    := {
    onObjects     := λ c, Limit.onObjects (evaluate_Functor_to_FunctorCategory F c),
    onMorphisms   := λ _ _ f, Limit.onMorphisms (evaluate_Functor_to_FunctorCategory_on_Morphism F f),
    identities    := ♯,
    functoriality := ♯
  },
  cone_maps     := λ j, {
    components := λ c, (limitCone (evaluate_Functor_to_FunctorCategory F c)).terminal_object.cone_maps j,
    naturality := ♯ 
  },
  commutativity := ♯ 
}

set_option pp.implicit true
private definition morphism_to_LimitObject_in_FunctorCategory { J C D : Category } [ cmp : Complete D ] { F : Functor J (FunctorCategory C D) } ( Y : Cone F ) : ConeMorphism Y (LimitObject_in_FunctorCategory F) := {
      cone_morphism := {
        components := begin
                          -- PROJECT This chain of tactics (produced by tidy) claims to finish, but leaves meta-variables
                          intros, 
                          fapply morphism_to_terminal_object_cone_point,
                          intros, 
                          dsimp',
                          tactic.any_goals (tactic.intros >>= λ x, tactic.skip),
                          tactic.any_goals dsimp',
                          exact (Y.cone_maps j).components X,
                          -- simp [id_locked_eq],
                          apply initial.is_terminal.uniqueness_of_morphisms_to_terminal_object,
                          tactic.result >>= tactic.trace
                       end,
        naturality := sorry
      },
      commutativity := sorry
    }

end categories.universal