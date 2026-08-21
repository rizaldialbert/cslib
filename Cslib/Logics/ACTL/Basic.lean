import Mathlib

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

structure Run (lts : LTS State Label) where
  ss : ωSequence State
  μs : ωSequence Label
  exec : OmegaExecution lts ss μs

/-- Dropping steps from the execution. -/
def Run.drop {lts : LTS State Label} (i : ℕ) (ρ : Run lts) : Run lts where
  ss := ωSequence.drop i ρ.ss
  μs := ωSequence.drop i ρ.μs
  exec := by
    intro n
    simp only [get_drop]
    rw [← add_assoc i n 1]
    exact ρ.exec (i + n)

/-- TODO -/
@[grind =]
def Satisfies {lts : LTS State Label} (ρ : Run lts) : Formula Label -> Prop
  | .true => True
  | .and φ φ' => Satisfies ρ φ ∧ Satisfies ρ φ'
  | .not φ => ¬(Satisfies ρ φ)
  | .exist φ => ∃θ : Run lts, θ.ss 0 = ρ.ss 0 ∧ Satisfies θ φ
  | .till φ φ' => ∃ i : ℕ, Satisfies (ρ.drop i) φ' ∧ (∀ j < i, Satisfies (ρ.drop j) φ)
  | .next φ => Satisfies (ρ.drop 1) φ
  | .next_act a φ => ρ.μs 0 = a ∧ Satisfies (ρ.drop 1) φ

section Satisfies

variable {State Label}
  {lts : LTS State Label}
  {ρ : Run lts}

theorem Satisfies.true :
  Satisfies ρ Formula.true := trivial

theorem Satisfies.drop_all :
  ∀(θ : Run lts), Satisfies θ Formula.true := by
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
    Satisfies ρ (φ.exist) ↔ ∃θ : Run lts, θ.ss 0 = ρ.ss 0 ∧ Satisfies θ φ := by rfl

theorem Satisfies.exist_if {φ : Formula Label} (θ : Run lts) (h : θ.ss 0 = ρ.ss 0) :
  Satisfies θ φ → Satisfies ρ (φ.exist) := by
  rw [Satisfies]
  intro h_sat
  use θ

@[grind =]
theorem Satisfies.next_iff {φ : Formula Label} {a : Label} :
    Satisfies ρ (φ.next) ↔ (Satisfies (ρ.drop 1) φ) := by rfl

@[grind =]
theorem Satisfies.next_act_iff {φ : Formula Label} {a : Label} :
    Satisfies ρ (φ.next_act a) ↔ (ρ.μs 0 = a ∧ Satisfies (ρ.drop 1) φ) := by rfl

@[grind =]
theorem Satisfies.imp_iff {φ₁ φ₂ : Formula Label} :
  Satisfies ρ (φ₁.imp φ₂) ↔ (Satisfies ρ φ₁ → Satisfies ρ φ₂) := by grind

theorem Satisfies.forall_iff :
  Satisfies ρ (.forall φ) ↔ (∀θ : Run lts, θ.ss 0 = ρ.ss 0 → Satisfies θ φ) := by
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

structure Judgement State Label where
  /-- Constructs a judgement. -/
  mk ::
  /-- LTS. -/
  lts : LTS State Label
  /-- The run satisfying the proposition `φ`. -/
  run : Run lts
  /-- The proposition satisfied by the state `s`. -/
  φ : Formula Label

@[grind =]
def Valid (lts : LTS State Label) (φ : Formula Label) : Prop := ∀ρ : Run lts, Satisfies ρ φ

@[grind =]
lemma Valid.iff : Valid lts φ ↔ ∀ρ : Run lts, Satisfies ρ φ := by rfl

lemma bismilarity_preserves_actl_star
  {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
  {s : State₁} {t : State₂}
  {φ : Formula Label}
  (h : s ~[lts₁,lts₂] t) -- Bisimilarity lts₁ lts₂ s₁ s₂
  : ∀ (ρ : Run lts₁) (θ : Run lts₂), ((ρ.ss 0 = s) ∧ (θ.ss 0 = t)) → (Satisfies ρ φ ↔ Satisfies θ φ)
    := sorry

end Cslib.Logic.ACTL
