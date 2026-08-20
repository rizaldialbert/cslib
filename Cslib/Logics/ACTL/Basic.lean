import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Foundations.Logic.Operators
import Cslib.Foundations.Logic.InferenceSystem

namespace Cslib.Logic.ACTL

/-- primitive logical operators -/
inductive Formula (Label : Type u) : Type u where
  /-- Truth. -/
  | true
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Formula Label)
  /-- Negation. -/
  | not (φ : Formula Label)
  /-- exists -/
  | exist (φ : Formula Label)
  /-- until -/
  | till (φ₁ φ₂ : Formula Label)
  /-- next -/
  | next (φ : Formula Label)
  /-- next witha action label -/
  | next_act (φ : Formula Label)

instance : Top (Formula Label) := ⟨.true⟩
instance : HasAnd (Formula Label) := ⟨.and⟩
instance : HasNot (Formula Label) := ⟨.not⟩

/-- Other logical connectives / operators derived from primitive operators -/

def Formula.false : Formula Label := ¬⊤

instance : Bot (Formula Label) := ⟨.false⟩

def Formula.or (φ₁ φ₂ : Formula Label) : Formula Label := ¬(¬φ₁ ∧ ¬φ₂)

instance : HasOr (Formula Label) := ⟨.or⟩

def Formula.imp (φ₁ φ₂ : Formula Label) : Formula Label := (¬φ₁ ∨ ¬φ₂)

instance : HasImp (Formula Label) := ⟨.imp⟩

def Formula.forall (φ : Formula Label) : Formula Label :=
  ¬ (.exist (.not φ))

def Formula.finally : Formula Label → Formula Label :=
  (.till .true · )

instance : HasDiamond (Formula Label) := ⟨.finally⟩

-- def Formula.globally (φ : Formula Label) : Formula Label :=
