import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Foundations.Semantics.LTS.OmegaExecution
import Cslib.Foundations.Logic.Operators
import Cslib.Foundations.Logic.InferenceSystem

namespace Cslib.Logic.ACTL

open Cslib.LTS
open ωSequence

mutual
/-- primitive logical operators -/
  inductive StateFormula (Label : Type u) : Type u where
  /-- Truth. -/
  | true
  /-- Conjunction. -/
  | and (Φ₁ Φ₂ : StateFormula Label)
  /-- Negation. -/
  | not (Φ  : StateFormula Label)
  /-- exists -/
  | exist (φ : PathFormula Label)

  inductive PathFormula (Label : Type u) : Type u
  | st (Φ : StateFormula Label)
  /-- until -/
  | till (Φ₁ Φ₂ : PathFormula Label)
  /-- next -/
  | next (Φ : PathFormula Label)
  /-- next with action label -/
  | next_act (a : Label) (Φ : PathFormula Label)
  /-- path and -/
  | and (Φ₁ Φ₂ : PathFormula Label)
  /-- path not -/
  | not (Φ : PathFormula Label)
end

instance : Top (StateFormula Label) := ⟨.true⟩
instance : HasAnd (StateFormula Label) := ⟨.and⟩
instance : HasNot (StateFormula Label) := ⟨.not⟩

instance : HasAnd (PathFormula Label) := ⟨.and⟩
instance : HasNot (PathFormula Label) := ⟨.not⟩

/-- Other logical connectives / operators derived from primitive operators -/

@[match_pattern]
def StateFormula.false : StateFormula Label := ¬⊤

@[match_pattern]
def StateFormula.or (Φ₁ Φ₂ : StateFormula Label) : StateFormula Label := ¬(¬Φ₁ ∧ ¬Φ₂)

def PathFormula.or (φ₁ φ₂ : PathFormula Label) : PathFormula Label := ¬ (¬φ₁ ∧ ¬φ₂)

instance : Bot (StateFormula Label) := ⟨.false⟩
instance : HasOr (StateFormula Label) := ⟨.or⟩
instance : HasOr (PathFormula Label) := ⟨.or⟩

@[match_pattern]
def StateFormula.forall (φ : PathFormula Label) : StateFormula Label := ¬(.exist (¬φ))

def PathFormula.true : PathFormula Label := .st .true

@[match_pattern]
def PathFormula.finally (φ : PathFormula Label) : PathFormula Label := (.till .true φ)

@[match_pattern]
def PathFormula.globally (φ : PathFormula Label) : PathFormula Label := ¬.finally (¬φ)

@[match_pattern]
def StateFormula.imp (Φ₁ Φ₂ : StateFormula Label) : StateFormula Label := (¬Φ₁ ∨ Φ₂)

def PathFormula.imp (φ₁ φ₂ : PathFormula Label) : PathFormula Label := (¬ φ₁ ∨ φ₂)

instance : HasImp (StateFormula Label) := ⟨.imp⟩
instance : HasImp (PathFormula Label) := ⟨.imp⟩
instance : HasDiamond (PathFormula Label) := ⟨.finally⟩
instance : HasBox (PathFormula Label) := ⟨.globally⟩

-- TODO Symmetrize equalities
@[grind =]
lemma StateFormula.top_def : (⊤ : StateFormula Label) = .true := rfl

@[grind =]
lemma StateFormula.and_def {Φ₁ Φ₂ : StateFormula Label} : Φ₁.and Φ₂ = (Φ₁ ∧ Φ₂) := rfl

lemma PathFormula.and_def {φ₁ φ₂ : PathFormula Label} : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl

@[grind =]
lemma StateFormula.not_def {Φ : StateFormula Label} : Φ.not = (¬Φ) := rfl

lemma PathFormula.not_def {φ : PathFormula Label} : φ.not = (¬φ) := rfl

@[grind =]
lemma StateFormula.bot_def : (⊥ : StateFormula Label) = .false := rfl

@[grind =]
lemma StateFormula.or_def {φ₁ φ₂ : StateFormula Label} : φ₁.or φ₂ = (φ₁ ∨ φ₂) := rfl

@[grind =]
lemma StateFormula.imp_def {Φ₁ Φ₂ : StateFormula Label} : Φ₁.imp Φ₂  = (¬Φ₁ ∨ Φ₂) := rfl

lemma PathFormula.imp_def {φ₁ φ₂ : StateFormula Label} : φ₁.imp φ₂  = (¬φ₁ ∨ φ₂) := rfl

@[grind =]
lemma PathFormula.diamond_def {φ : PathFormula Label} : PathFormula.finally φ = (◇φ) := rfl

@[grind =]
lemma PathFormula.box_def {φ : PathFormula Label} : PathFormula.globally φ = (□φ) := rfl

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

mutual
  def SatisfiesState (lts : LTS State Label) (s : State) : StateFormula Label -> Prop
  | .true => True
  | .and Φ Φ' => SatisfiesState lts s Φ ∧ SatisfiesState lts s Φ'
  | .not Φ => ¬(SatisfiesState lts s Φ)
  | .exist φ => ∃θ : Run lts, θ.ss 0 = s ∧ SatisfiesPath θ φ

  def SatisfiesPath {lts : LTS State Label} (θ : Run lts) : PathFormula Label -> Prop
  | .st Φ => SatisfiesState lts (θ.ss 0) Φ
  | .till φ₁ φ₂ =>
      ∃j : ℕ  , 0 ≤ j
              ∧ SatisfiesPath (θ.drop j) φ₂
              ∧ (∀k, 0 ≤ k ∧ k < j → SatisfiesPath (θ.drop k) φ₁)
  | .next φ => SatisfiesPath (θ.drop 1) φ
  | .next_act a φ => (θ.μs 0 = a) ∧ SatisfiesPath (θ.drop 1) φ
  | .and φ₁ φ₂ => SatisfiesPath θ φ₁ ∧ SatisfiesPath θ φ₂
  | .not φ => ¬ SatisfiesPath θ φ
end

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
