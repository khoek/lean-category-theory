-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section product
variables {β : Type v} {f : β → C} 

structure is_product (t : fan f) :=
(lift : ∀ (s : fan f), s.X ⟶ t.X)
(fac'  : ∀ (s : fan f), ∀ b, (lift s) ≫ t.π b = s.π b . obviously) 
(uniq' : ∀ (s : fan f) (m : s.X ⟶ t.X) (w : ∀ b, m ≫ t.π b = s.π b), m = lift s . obviously)

restate_axiom is_product.fac'
attribute [simp,search] is_product.fac
restate_axiom is_product.uniq'
attribute [search,back'] is_product.uniq

@[extensionality] lemma is_product.ext {t : fan f} (P Q : is_product t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

instance is_product_subsingleton {t : fan f}  : subsingleton (is_product t) := by obviously

lemma is_product.uniq'' {t : fan f} (h : is_product t) {X' : C} (m : X' ⟶ t.X) : m = h.lift { X := X', π := λ b, m ≫ t.π b } :=
h.uniq { X := X', π := λ b, m ≫ t.π b } m (by obviously)

-- TODO provide alternative constructor using uniq'' instead of uniq'.

lemma is_product.univ {t : fan f} (h : is_product t) (s : fan f) (φ : s.X ⟶ t.X) : (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = h.lift s) :=
by obviously

def is_product.of_lift_univ {t : fan f}
  (lift : Π (s : fan f), s.X ⟶ t.X)
  (univ : Π (s : fan f) (φ : s.X ⟶ t.X), (∀ b, φ ≫ t.π b = s.π b) ↔ (φ = lift s)) : is_product t :=
{ lift := lift,
  fac'  := λ s b, ((univ s (lift s)).mpr (eq.refl (lift s))) b,
  uniq' := begin obviously, apply univ_s_m.mp, obviously, end }

end product


section coproduct
variables {β : Type v} {f : β → C} 

structure is_coproduct (t : cofan f) :=
(desc : ∀ (s : cofan f), t.X ⟶ s.X)
(fac'  : ∀ (s : cofan f), ∀ b, t.ι b ≫ (desc s) = s.ι b . obviously) 
(uniq' : ∀ (s : cofan f) (m : t.X ⟶ s.X) (w : ∀ b, t.ι b ≫ m = s.ι b), m = desc s . obviously)

restate_axiom is_coproduct.fac'
attribute [simp,search] is_coproduct.fac
restate_axiom is_coproduct.uniq'
attribute [search, back'] is_coproduct.uniq

@[extensionality] lemma is_coproduct.ext {t : cofan f} (P Q : is_coproduct t) : P = Q :=
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously end

instance is_coproduct_subsingleton {t : cofan f}  : subsingleton (is_coproduct t) := by obviously

lemma is_coproduct.uniq'' {t : cofan f} (h : is_coproduct t) {X' : C} (m : t.X ⟶ X') : m = h.desc { X := X', ι := λ b, t.ι b ≫ m } :=
h.uniq { X := X', ι := λ b, t.ι b ≫ m } m (by obviously)

-- TODO provide alternative constructor using uniq'' instead of uniq'.

lemma is_coproduct.univ {t : cofan f} (h : is_coproduct t) (s : cofan f) (φ : t.X ⟶ s.X) : (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = h.desc s) :=
by obviously

def is_coproduct.of_desc_univ {t :cofan f}
  (desc : Π (s : cofan f), t.X ⟶ s.X)
  (univ : Π (s : cofan f) (φ : t.X ⟶ s.X), (∀ b, t.ι b ≫ φ = s.ι b) ↔ (φ = desc s)) : is_coproduct t :=
{ desc := desc,
  fac'  := λ s b, ((univ s (desc s)).mpr (eq.refl (desc s))) b,
  uniq' := begin obviously, apply univ_s_m.mp, obviously, end }

end coproduct

variable (C)

class has_products :=
(prod : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (prod f) . obviously)

class has_coproducts :=
(coprod : Π {β : Type v} (f : β → C), cofan.{u v} f)
(is_coproduct : Π {β : Type v} (f : β → C), is_coproduct (coprod f) . obviously)

variable {C}

section
variables [has_products.{u v} C] {β : Type v} 

def pi.fan (f : β → C) := has_products.prod.{u v} f
def pi (f : β → C) : C := (pi.fan f).X
def pi.π (f : β → C) (b : β) : pi f ⟶ f b := (pi.fan f).π b
def pi.universal_property (f : β → C) : is_product (pi.fan f) := has_products.is_product.{u v} C f

@[simp] def pi.fan_π (f : β → C) (b : β) : (pi.fan f).π b = @pi.π C _ _ _ f b := rfl

def pi.lift {f : β → C} {P : C} (p : Π b, P ⟶ f b) : P ⟶ pi f :=
(pi.universal_property f).lift ⟨ ⟨ P ⟩, p ⟩

-- @[simp] lemma pi.universal_property_lift (f : β → C) {P : C} (p : Π b, P ⟶ f b) : 
--   (pi.universal_property f).lift ⟨ ⟨ P ⟩, p ⟩ = pi.lift p := rfl

@[simp,search] def pi.lift_π {f : β → C} {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.lift p ≫ pi.π f b = p b :=
by erw is_product.fac

def pi.map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) : (pi f) ⟶ (pi g) :=
pi.lift (λ b, pi.π f b ≫ k b) 

@[simp] def pi.map_π {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) (b : β) : pi.map k ≫ pi.π g b = pi.π f b ≫ k b :=
by erw is_product.fac

def pi.pre {α} (f : α → C) (h : β → α) : pi f ⟶ pi (f ∘ h) :=
pi.lift (λ g, pi.π f (h g))

@[simp] def pi.pre_π {α} (f : α → C) (h : β → α) (b : β) : pi.pre f h ≫ pi.π (f ∘ h) b = pi.π f (h b) := 
by erw is_product.fac

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_products.{u v} D]
include 𝒟 

def pi.post (f : β → C) (G : C ⥤ D) : G (pi f) ⟶ (pi (G.obj ∘ f)) :=
@is_product.lift _ _ _ _ (pi.fan (G.obj ∘ f)) (pi.universal_property _) { X := _, π := λ b, G.map (pi.π f b) }

@[simp] def pi.post_π (f : β → C) (G : C ⥤ D) (b : β) : pi.post f G ≫ pi.π _ b = G.map (pi.π f b) := 
by erw is_product.fac
end

@[extensionality] lemma pi.hom_ext (f : β → C) {X : C} (g h : X ⟶ pi f) (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
begin
  rw is_product.uniq (pi.universal_property f) { X := X, π := λ b, g ≫ pi.π f b } g,
  rw is_product.uniq (pi.universal_property f) { X := X, π := λ b, g ≫ pi.π f b } h,
  obviously,
end

@[simp] def pi.lift_map 
  {f : β → C} {g : β → C} {P : C} (p : Π b, P ⟶ f b) (k : Π b, f b ⟶ g b) :
  pi.lift p ≫ pi.map k = pi.lift (λ b, p b ≫ k b) :=
by obviously

@[simp] def pi.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C} 
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  pi.map k1 ≫ pi.map k2 = pi.map (λ b, k1 b ≫ k2 b) := 
by obviously.

@[simp] def pi.lift_pre {α : Type v} {f : β → C} {P : C} (p : Π b, P ⟶ f b) (h : α → β) :
  pi.lift p ≫ pi.pre _ h = pi.lift (λ a, p (h a)) :=
by obviously

-- TODO lemmas describing interactions:
-- map_pre, pre_pre, lift_post, map_post, pre_post, post_post

end

section
variables [has_coproducts.{u v} C] {β : Type v} 

def Sigma.cofan (f : β → C) := has_coproducts.coprod.{u v} f
def Sigma (f : β → C) : C := (Sigma.cofan f).X
def Sigma.ι (f : β → C) (b : β) : f b ⟶ Sigma f := (Sigma.cofan f).ι b
def Sigma.universal_property (f : β → C) : is_coproduct (Sigma.cofan f) := has_coproducts.is_coproduct.{u v} C f

@[simp] def Sigma.cofan_ι (f : β → C) (b : β) : (Sigma.cofan f).ι b = @Sigma.ι C _ _ _ f b := rfl

def Sigma.desc {f : β → C} {P : C} (p : Π b, f b ⟶ P) : Sigma f ⟶ P :=
(Sigma.universal_property f).desc ⟨ ⟨ P ⟩, p ⟩

@[simp,search] def Sigma.lift_ι {f : β → C} {P : C} (p : Π b, f b ⟶ P) (b : β) : Sigma.ι f b ≫ Sigma.desc p = p b :=
by erw is_coproduct.fac

def Sigma.map {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) : (Sigma f) ⟶ (Sigma g) :=
Sigma.desc (λ b, k b ≫ Sigma.ι g b) 

@[simp] def Sigma.map_ι {f : β → C} {g : β → C} (k : Π b, f b ⟶ g b) (b : β) : Sigma.ι f b ≫ Sigma.map k = k b ≫ Sigma.ι g b :=
by erw is_coproduct.fac

def Sigma.pre {α} (f : α → C) (h : β → α) : Sigma (f ∘ h) ⟶ Sigma f :=
Sigma.desc (λ g, Sigma.ι f (h g))

@[simp] def Sigma.pre_ι {α} (f : α → C) (h : β → α) (b : β) : Sigma.ι (f ∘ h) b ≫ Sigma.pre f h = Sigma.ι f (h b) := 
by erw is_coproduct.fac

section
variables {D : Type u} [𝒟 : category.{u v} D] [has_coproducts.{u v} D]
include 𝒟 

def Sigma.post (f : β → C) (G : C ⥤ D) : (Sigma (G.obj ∘ f)) ⟶ G (Sigma f) :=
@is_coproduct.desc _ _ _ _ (Sigma.cofan (G.obj ∘ f)) (Sigma.universal_property _) { X := _, ι := λ b, G.map (Sigma.ι f b) }

@[simp] def Sigma.post_π (f : β → C) (G : C ⥤ D) (b : β) : Sigma.ι _ b ≫ Sigma.post f G = G.map (Sigma.ι f b) := 
by erw is_coproduct.fac
end

@[extensionality] lemma Sigma.hom_ext (f : β → C) {X : C} (g h : Sigma f ⟶ X) (w : ∀ b, Sigma.ι f b ≫ g = Sigma.ι f b ≫ h) : g = h :=
begin
  rw is_coproduct.uniq (Sigma.universal_property f) { X := X, ι := λ b, Sigma.ι f b ≫ g } g,
  rw is_coproduct.uniq (Sigma.universal_property f) { X := X, ι := λ b, Sigma.ι f b ≫ g } h,
  obviously
end

@[simp] def Sigma.desc_map 
  {f : β → C} {g : β → C} {P : C} (k : Π b, f b ⟶ g b) (p : Π b, g b ⟶ P) :
  Sigma.map k ≫ Sigma.desc p = Sigma.desc (λ b, k b ≫ p b) :=
by obviously

@[simp] def Sigma.map_map {f1 : β → C} {f2 : β → C} {f3 : β → C} 
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  Sigma.map k1 ≫ Sigma.map k2 = Sigma.map (λ b, k1 b ≫ k2 b) := 
by obviously.

@[simp] def Sigma.desc_pre {α : Type v} {f : β → C} {P : C} (p : Π b, f b ⟶ P) (h : α → β) :
  Sigma.pre _ h ≫ Sigma.desc p = Sigma.desc (λ a, p (h a)) :=
by obviously


-- TODO lemmas describing interactions:
-- desc_pre, map_pre, pre_pre, desc_post, map_post, pre_post, post_post

end

end category_theory.limits
