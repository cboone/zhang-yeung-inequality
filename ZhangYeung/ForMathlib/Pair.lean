/-
Copyright (c) 2024 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Util.Notation3
public import Mathlib.Tactic.Basic

/-!
# Pair notation for random variables

Provides the `⟨X, Y⟩` notation for the function `ω ↦ (X ω, Y ω)`, used pervasively in the entropy
API.

Forked from `PFR.ForMathlib.Pair` in [teorth/pfr](https://github.com/teorth/pfr) at rev `80daaf1`
with no change in content.
-/

public section

/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y

@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := rfl
