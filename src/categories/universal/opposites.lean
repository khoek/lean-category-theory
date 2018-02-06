-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..opposites
import ..equivalence
import .cones
import .universal
import .complete

open categories
open categories.functor
open categories.initial
open categories.opposites
open categories.universal
open categories.equivalence

namespace categories.universal.opposites

def InitialObject_in_Opposite {C : Category} (i : InitialObject (Opposite C)) : TerminalObject C := {
  terminal_object := i.initial_object,
  morphism_to_terminal_object_from := i.morphism_from_initial_object_to,
  uniqueness_of_morphisms_to_terminal_object := i.uniqueness_of_morphisms_from_initial_object
}

def TerminalObject_in_Opposite {C : Category} (t : TerminalObject (Opposite C)) : InitialObject C := {
  initial_object := t.terminal_object,
  morphism_from_initial_object_to := t.morphism_to_terminal_object_from,
  uniqueness_of_morphisms_from_initial_object := t.uniqueness_of_morphisms_to_terminal_object
}

def Equalizer_in_Opposite       {C : Category} {X Y : C.Obj} {f g : C.Hom X Y} (e : @Equalizer (Opposite C) Y X f g)   : Coequalizer f g := sorry
def Coequalizer_in_Opposite     {C : Category} {X Y : C.Obj} {f g : C.Hom X Y} (e : @Coequalizer (Opposite C) Y X f g) : Equalizer f g := sorry
def BinaryProduct_in_Opposite   {C : Category} {X Y : C.Obj}                   (p : @BinaryProduct (Opposite C) X Y)   : BinaryCoproduct X Y := sorry
def BinaryCoproduct_in_Opposite {C : Category} {X Y : C.Obj}                   (p : @BinaryCoproduct (Opposite C) X Y) : BinaryProduct X Y := sorry
def Product_in_Opposite         {C : Category} {I: Type} {F : I → C.Obj}       (p : @Product (Opposite C) _ F)         : Coproduct F := sorry
def Coproduct_in_Opposite       {C : Category} {I: Type} {F : I → C.Obj}       (p : @Coproduct (Opposite C) _ F)       : Product F := sorry

def Cones_in_Opposite   {J C : Category} (F : Functor J C) : Equivalence (Cones (OppositeFunctor F)) (Cocones F) := sorry
def Cocones_in_Opposite {J C : Category} (F : Functor J C) : Equivalence (Cocones (OppositeFunctor F)) (Cones F) := sorry

instance Cocomplete_of_Opposite_Complete {C : Category} [Complete (Opposite C)]   : Cocomplete C := sorry
instance Complete_of_Opposite_Cocomplete {C : Category} [Cocomplete (Opposite C)] : Complete C := sorry
instance Opposite_Complete_of_Cocomplete {C : Category} [Cocomplete C]            : Complete (Opposite C) := sorry
instance Opposite_Cocomplete_of_Complete {C : Category} [Complete C]              : Cocomplete (Opposite C) := sorry

end categories.universal.opposites