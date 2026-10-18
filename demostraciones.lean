example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.2, h.1⟩

example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1

example (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp
  exact hqr (hpq hp)

example (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  have hp := h.1
  cases h.2 with
  | inl hq => exact Or.inl ⟨hp, hq⟩
  | inr hr => exact Or.inr ⟨hp, hr⟩

example (P : Prop) : P → ¬¬P := by
  intro hp hnotp
  exact hnotp hp

example (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp
