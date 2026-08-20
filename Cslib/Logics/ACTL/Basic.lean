import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Foundations.Semantics.LTS.OmegaExecution
import Cslib.Foundations.Logic.Operators
import Cslib.Foundations.Logic.InferenceSystem

namespace Cslib.Logic.ACTL

open Cslib.LTS
open ωSequence

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
  | next_act (a : Label) (φ : Formula Label)

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


/-- TODO -/
def Satisfies {lts : LTS State Label}
  {ss : ωSequence State} {μs : ωSequence Label}
  (ρ : OmegaExecution lts ss μs) : Formula Label -> Prop
  | .true => True
  | .and φ φ' => Satisfies ρ φ ∧ Satisfies ρ φ'
  | .not φ => ¬(Satisfies ρ φ)
  | .exist φ => ∃ ss' μs', ∃ θ : OmegaExecution lts ss' μs', ss' 0 = ss 0 ∧ Satisfies θ φ
  | .till φ φ' => ∃ i : ℕ, Satisfies (ρ.drop i) φ' ∧ (∀ j < i, Satisfies (ρ.drop j) φ)
  | .next φ => Satisfies (ρ.drop 1) φ
  | .next_act a φ => μs 0 = a ∧ Satisfies (ρ.drop 1) φ

def Valid (lts : LTS State Label) (φ : Formula Label) : Prop :=
  ∀ ss μs , ∀ρ : OmegaExecution lts ss μs , Satisfies ρ φ

lemma bisimulation_preserves_actl_star
  {lts₁ lts₂ : LTS State Label}
  {φ : Formula Label}
  (h0 : IsBisimulation lts₁ lts₂ R) : Valid lts₁ φ ↔ Valid lts₂ φ := by sorry


end Cslib.Logic.ACTL
