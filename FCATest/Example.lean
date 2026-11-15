/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA

/-!
# A small worked example

A fragment of the classical "living beings and water" context of Ganter and Wille, used to
exercise the executable definitions of `FCA.Finite.Basic`.
-/

@[expose] public section

namespace FCATest

/-- The objects of the example context. -/
inductive Being
  | leech | bream | frog | dog | reed | bean
  deriving DecidableEq, Repr

open Being in
instance : Fintype Being :=
  ⟨{leech, bream, frog, dog, reed, bean}, fun g => by cases g <;> decide⟩

/-- The attributes of the example context. -/
inductive Property
  | needsWater | livesInWater | livesOnLand | canMove | hasLimbs
  deriving DecidableEq, Repr

open Property in
instance : Fintype Property :=
  ⟨{needsWater, livesInWater, livesOnLand, canMove, hasLimbs}, fun m => by cases m <;> decide⟩

open Being Property

/-- The incidence relation of the example context, as a Boolean table. -/
def hasProperty : Being → Property → Bool
  | _, needsWater => true
  | leech, livesInWater | bream, livesInWater | frog, livesInWater | reed, livesInWater => true
  | frog, livesOnLand | dog, livesOnLand | reed, livesOnLand | bean, livesOnLand => true
  | leech, canMove | bream, canMove | frog, canMove | dog, canMove => true
  | bream, hasLimbs | frog, hasLimbs | dog, hasLimbs => true
  | _, _ => false

/-- The incidence relation of the example context. -/
abbrev incidence (g : Being) (m : Property) : Prop := hasProperty g m = true

example : FCA.upperPolarFinset incidence {frog, dog} =
    {needsWater, livesOnLand, canMove, hasLimbs} := by
  decide

example : FCA.intentClosureFinset incidence {hasLimbs} = {needsWater, canMove, hasLimbs} := by
  decide

example : (FCA.concepts incidence).card = 10 := by
  decide

end FCATest
