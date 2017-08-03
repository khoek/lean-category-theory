-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

namespace categories

structure {u v} Category :=
  ( Obj : Type u )
  ( Hom : Obj → Obj → Type v )
  ( identity : Π X : Obj, Hom X X )
  ( compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z )

  ( left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity X) f = f )
  ( right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity Y) = f )
  ( associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) )

attribute [simp] Category.left_identity
attribute [simp] Category.right_identity
attribute [simp,ematch] Category.associativity
attribute [applicable] Category.identity

@[tidy] meta def rewrite_associativity_backwards : tactic string := 
(`[repeat_at_least_once { rewrite ← Category.associativity }])   
  >> `[simp]
  >> tactic.done
  >> pure "repeat_at_least_once {rewrite ← Category.associativity}, simp" 

end categories
