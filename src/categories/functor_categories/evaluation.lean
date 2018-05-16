-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.natural_transformation
import categories.products

open categories
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ u₂

variable (C : Type (u₁+1))
variable [small_category C]
variable (D : Type (u₂+1))
variable [category D]

definition Evaluation : ((C ↝ₛ D) × C) ↝ₛ D := {
  onObjects     := λ p, p.1 +> p.2,
  onMorphisms   := λ x y f, (x.1 &> f.2) ≫ (f.1.components y.2)
}

end categories.functor_categories