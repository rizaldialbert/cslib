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

@[match_pattern]
def Formula.false : Formula Label := ¬⊤

@[match_pattern]
def Formula.or (φ₁ φ₂ : Formula Label) : Formula Label := ¬(¬φ₁ ∧ ¬φ₂)

instance : Bot (Formula Label) := ⟨.false⟩
instance : HasOr (Formula Label) := ⟨.or⟩

@[match_pattern]
def Formula.forall (φ : Formula Label) : Formula Label := ¬(.exist (¬φ))

@[match_pattern]
def Formula.finally (φ : Formula Label) : Formula Label := (.till .true φ)

@[match_pattern]
def Formula.globally (φ : Formula Label) : Formula Label := ¬.finally (¬φ)

@[match_pattern]
def Formula.imp (φ₁ φ₂ : Formula Label) : Formula Label := (¬φ₁ ∨ φ₂)

instance : HasImp (Formula Label) := ⟨.imp⟩
instance : HasDiamond (Formula Label) := ⟨.finally⟩
instance : HasBox (Formula Label) := ⟨.globally⟩

-- TODO Symmetrize equalities
@[grind =]
lemma Formula.top_def : (⊤ : Formula Label) = .true := rfl

@[grind =]
lemma Formula.and_def {φ₁ φ₂ : Formula Label} : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

@[grind =]
lemma Formula.not_def {φ : Formula Label} : φ.not = (¬φ) := rfl

@[grind =]
lemma Formula.bot_def : (⊥ : Formula Label) = .false := rfl

@[grind =]
lemma Formula.or_def {φ₁ φ₂ : Formula Label} : φ₁.or φ₂ = (φ₁ ∨ φ₂) := rfl

@[grind =]
lemma Formula.imp_def {φ₁ φ₂ : Formula Label} : φ₁.imp φ₂  = (¬φ₁ ∨ φ₂) := rfl

@[grind =]
lemma Formula.diamond_def {φ : Formula Label} : Formula.finally φ = (◇φ) := rfl

@[grind =]
lemma Formula.box_def {φ : Formula Label} : Formula.globally φ = (□φ) := rfl

/-- TODO -/
@[grind =]
def Satisfies {lts : LTS State Label}
  {ss : ωSequence State} {μs : ωSequence Label}
  (ρ : OmegaExecution lts ss μs) : Formula Label -> Prop
  | .true => True
  | .and φ φ' => Satisfies ρ φ ∧ Satisfies ρ φ'
  | .not φ => ¬(Satisfies ρ φ)
  | .exist φ => ∃ ss' μs', ∃θ : OmegaExecution lts ss' μs', ss' 0 = ss 0 ∧ Satisfies θ φ
  | .till φ φ' => ∃ i : ℕ, Satisfies (ρ.drop i) φ' ∧ (∀ j < i, Satisfies (ρ.drop j) φ)
  | .next φ => Satisfies (ρ.drop 1) φ
  | .next_act a φ => μs 0 = a ∧ Satisfies (ρ.drop 1) φ

section Satisfies

variable {State Label}
  {ss : ωSequence State} {μs : ωSequence Label}
  {lts : LTS State Label}
  {ρ : OmegaExecution lts ss μs}

theorem Satisfies.true :
  Satisfies ρ Formula.true := trivial

theorem Satisfies.drop_all :
  ∀(θ : OmegaExecution lts ss μs), Satisfies θ Formula.true := by
  tauto

@[grind =]
theorem Satisfies.and_iff :
  Satisfies ρ φ₁ ∧ Satisfies ρ φ₂ ↔ Satisfies ρ (φ₁ ∧ φ₂) := by rfl

@[grind =]
theorem Satisfies.not_iff : ¬ (Satisfies ρ φ) ↔ Satisfies ρ (¬ φ) := by rfl

@[grind =]
theorem Satisfies.or_iff {φ₁ φ₂ : Formula Label} :
    Satisfies ρ (φ₁ ∨ φ₂) ↔ (Satisfies ρ φ₁ ∨ Satisfies ρ φ₂) := or_iff_not_and_not.symm

@[grind =]
theorem Satisfies.till_iff {φ₁ φ₂ : Formula Label} :
    Satisfies ρ (φ₁.till φ₂)
      ↔ ∃ i : ℕ, Satisfies (ρ.drop i) φ₂ ∧ (∀ j < i, Satisfies (ρ.drop j) φ₁) := by rfl

theorem Satisfies.exist_iff {φ : Formula Label} :
    Satisfies ρ (φ.exist)
      ↔ ∃ ss' μs', ∃θ : OmegaExecution lts ss' μs', ss' 0 = ss 0 ∧ Satisfies θ φ := by rfl

theorem Satisfies.exist_if {φ : Formula Label} (θ : OmegaExecution lts ss' μs') (h : ss' 0 = ss 0) :
  Satisfies θ φ →  Satisfies ρ (φ.exist) := by
  rw [Satisfies]
  intro h_sat
  use ss', μs', θ

@[grind =]
theorem Satisfies.next_iff {φ : Formula Label} {a : Label} :
    Satisfies ρ (φ.next_act a) ↔ (μs 0 = a ∧ Satisfies (ρ.drop 1) φ) := by rfl

@[grind =]
theorem Satisfies.next_act_iff {φ : Formula Label} {a : Label} :
    Satisfies ρ (φ.next_act a) ↔ (μs 0 = a ∧ Satisfies (ρ.drop 1) φ) := by rfl

@[grind =]
theorem Satisfies.imp_iff {φ₁ φ₂: Formula Label} :
  Satisfies ρ (φ₁.imp φ₂) ↔ (Satisfies ρ φ₁ → Satisfies ρ φ₂) := by
  grind

theorem Satisfies.forall_iff :
  Satisfies ρ (.forall φ) ↔ (∀ ss' μs', ∀θ : OmegaExecution lts ss' μs', ss' 0 = ss 0 → Satisfies θ φ) := by
  rw [Formula.forall, ← Satisfies.not_iff, not_iff_comm, Satisfies.exist_iff]
  push Not
  tauto

theorem Satisfies.diamond_iff :
  Satisfies ρ (◇φ) ↔ ∃ i : ℕ, Satisfies (ρ.drop i) φ := by
  simp [← Formula.diamond_def, Formula.finally, Satisfies.till_iff, Satisfies.drop_all]

theorem Satisfies.box_iff :
  Satisfies ρ (□φ) ↔ ∀ i : ℕ, Satisfies (ρ.drop i) φ := by
  simp [← Formula.box_def, Formula.globally,
Formula.finally, ← Satisfies.not_iff, Satisfies.till_iff, Satisfies.drop_all, ← Satisfies.not_iff]

end Satisfies

@[grind =]
def Valid (lts : LTS State Label) (φ : Formula Label) : Prop :=
  ∀ ss μs , ∀ρ : OmegaExecution lts ss μs , Satisfies ρ φ

@[grind =]
lemma Valid.iff :
  Valid lts φ ↔ ∀ ss μs , ∀ρ : OmegaExecution lts ss μs , Satisfies ρ φ := by rfl

lemma bisimulation_preserves_actl_star
  {lts₁ lts₂ : LTS State Label}
  {φ : Formula Label}
  (h0 : IsBisimulation lts₁ lts₂ R) : Valid lts₁ φ ↔ Valid lts₂ φ := by
  induction φ
  · grind only [= Valid.iff, Satisfies]
  · grind only [= Valid.iff, Satisfies]
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

end Cslib.Logic.ACTL
