-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .applicable .force .at_least_one .repeat_at_least_once .smt .tidy

import .auto_cast

open tactic

attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b has_coe_to_fun.coe
attribute [simp] id_locked_eq
attribute [ematch] subtype.property

open tactic
open lean.parser
open interactive






meta def trace_goal_type : tactic unit :=
do g ← target,
   trace g,
   infer_type g >>= trace,
   skip




set_option formatter.hide_full_terms false

@[simp] lemma {u v} pair_1 {α : Type u} {β : Type v} { a : α } { b : β } : (a, b).1 = a := ♮
@[simp] lemma {u v} pair_2 {α : Type u} {β : Type v} { a : α } { b : β } : (a, b).2 = b := ♮
@[simp,ematch] lemma {u v} pair_equality {α : Type u} {β : Type v} { X : α × β } : (X.1, X.2) = X := ♯
