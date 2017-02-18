-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..monoidal_categories.monoidal_category
import .semigroups.semigroups

namespace tqft.categories.examples.types

open tqft.categories

@[reducible] definition { u } CategoryOfTypes : Category := 
{
    Obj := Type u,
    Hom := λ a b, a → b,

    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

open tqft.categories.monoidal_category

definition MonoidalCategoryOfTypes : MonoidalCategory :=
{
  CategoryOfTypes with
  tensor := {
    onObjects     := λ p, prod p.1 p.2,
    onMorphisms   := λ _ _ p, λ q, (p.1 q.1, p.2 q.2),
    identities    := ♮,
    functoriality := ♮
  },
  tensor_unit := punit,
  associator_transformation := {
    components := sorry,
    naturality := sorry
  },
  associator_is_isomorphism := {
    inverse := {
      components := sorry,
      naturality := sorry
    },
    witness_1 := sorry,
    witness_2 := sorry
  },
  pentagon := sorry
}

end tqft.categories.examples.types