-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.tactics.obviously

namespace category_theory

universes u v

variables {C : Type u} {X Y Z : C} [𝒞 : category.{u v} C]
include 𝒞

@[forward] def cancel_left (f g : X ⟶ Y) (h : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g :=
begin
     convert h (𝟙 Y), tidy
end
@[forward] def cancel_right (f g : Y ⟶ Z) (h : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g :=
begin
    convert h (𝟙 Y), tidy
end
@[forward] def cancel_left' (f g : X ⟶ Y) (w : (λ {Z : C} (h : Y ⟶ Z), f ≫ h) = (λ {Z : C} (h : Y ⟶ Z), g ≫ h)) : f = g :=
begin
     convert (congr_fun (congr_fun w Y) (𝟙 Y)), tidy
end
@[forward] def cancel_right' (f g : Y ⟶ Z) (w : (λ {X : C} (h : X ⟶ Y), h ≫ f) = (λ {X : C} (h : X ⟶ Y), h ≫ g)) : f = g :=
begin
     convert (congr_fun (congr_fun w Y) (𝟙 Y)), tidy
end
@[forward] def identity_if_it_quacks_left (f : X ⟶ X) (h : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X :=
begin
    convert h (𝟙 X), tidy
end
@[forward] def identity_if_it_quacks_right (f : X ⟶ X) (h : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X :=
begin
    convert h (𝟙 X), tidy
end

end category_theory