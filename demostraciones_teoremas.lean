/-!
Teoremas importantes del cálculo proposicional en Lean 4.
Cada declaración theorem contiene una proposición y una prueba verificada por Lean.
-/

-- 1. Identidad: una proposición implica a sí misma.
theorem identidad (P : Prop) : P → P := by
  intro hP
  exact hP

-- 2. Modus ponens: de P y P → Q se concluye Q.
theorem modus_ponens (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  exact hPQ hP

-- 3. Silogismo hipotético: las implicaciones se pueden encadenar.
theorem silogismo_hipotetico (P Q R : Prop)
    (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  exact hQR (hPQ hP)

-- 4. Introducción de la conjunción: si P y Q se cumplen, se cumple P ∧ Q.
theorem introducir_conjuncion (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact ⟨hP, hQ⟩

-- 5. Conmutatividad de la conjunción.
theorem conjuncion_conmutativa (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

-- 6. Asociatividad de la conjunción.
theorem conjuncion_asociativa (P Q R : Prop) : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

-- 7. Conmutatividad de la disyunción, demostrada por casos.
theorem disyuncion_conmutativa (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hP => exact Or.inr hP
    | inr hQ => exact Or.inl hQ
  · intro h
    cases h with
    | inl hQ => exact Or.inr hQ
    | inr hP => exact Or.inl hP

-- 8. Distributividad de la conjunción sobre la disyunción.
theorem conjuncion_distribuye_sobre_disyuncion (P Q R : Prop) :
    P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    cases h.2 with
    | inl hQ => exact Or.inl ⟨h.1, hQ⟩
    | inr hR => exact Or.inr ⟨h.1, hR⟩
  · intro h
    cases h with
    | inl hPQ => exact ⟨hPQ.1, Or.inl hPQ.2⟩
    | inr hPR => exact ⟨hPR.1, Or.inr hPR.2⟩

-- 9. Ley de De Morgan para la negación de una disyunción.
theorem de_morgan_disyuncion (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      exact h (Or.inl hP)
    · intro hQ
      exact h (Or.inr hQ)
  · intro h hPQ
    cases hPQ with
    | inl hP => exact h.1 hP
    | inr hQ => exact h.2 hQ

-- 10. Doble negación: el regreso a P usa razonamiento clásico.
theorem doble_negacion_ley (P : Prop) : P ↔ ¬¬P := by
  constructor
  · intro hP hNoP
    exact hNoP hP
  · intro hNNP
    by_cases hP : P
    · exact hP
    · exact False.elim (hNNP hP)

-- 11. Principio del tercero excluido, clásico.
theorem tercero_excluido (P : Prop) : P ∨ ¬ P := by
  by_cases hP : P
  · exact Or.inl hP
  · exact Or.inr hP
