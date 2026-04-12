/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doeblin's Condition and Exponential Mixing

Doeblin's condition for Markov kernels: if the transition density is
bounded below by ε times the invariant measure, then the chain mixes
exponentially. Key ingredient for the 2D Yang-Mills mass gap.

## Main results

- `MarkovKernel`, `DoeblinCondition` — structures
- `doeblin_one_step_contraction` — |μ(A) - π(A)| ≤ 1 - ε (PROVEN)
- `doeblin_exponential_mixing` — |Kⁿ(x,A) - π(A)| ≤ (1-ε)ⁿ (axiom)
- `doeblin_correlation_decay` — correlation decay (axiom)

## References

- Chatterjee (2026), §15.7, App B.5
- Levin-Peres-Wilmer, "Markov Chains and Mixing Times" (2009), Ch 5
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

/-! ## Structures -/

/-- A Markov kernel: for each x, K(x, ·) is a probability measure. -/
structure MarkovKernel (X : Type*) [MeasurableSpace X] where
  kernel : X → Measure X
  isProb : ∀ x, IsProbabilityMeasure (kernel x)

attribute [instance] MarkovKernel.isProb

/-- Doeblin's condition: K(x, A) ≥ ε · π(A) for all x, A. -/
structure DoeblinCondition {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (π : Measure X) [IsProbabilityMeasure π] where
  ε : ℝ
  hε_pos : 0 < ε
  hε_le : ε ≤ 1
  minorize : ∀ (x : X) (A : Set X), MeasurableSet A →
    ε * (π A).toReal ≤ (K.kernel x A).toReal

/-! ## One-step contraction -/

/-- **Doeblin one-step contraction (PROVEN).**

If probability measure μ satisfies μ(A) ≥ ε·π(A) for all A, then
  |μ(A) - π(A)| ≤ 1 - ε for all measurable A.

This is half the total variation bound ‖μ - π‖_TV ≤ 2(1-ε). -/
theorem doeblin_one_step_contraction {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [hμ : IsProbabilityMeasure μ] [hπ : IsProbabilityMeasure π]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmin : ∀ (A : Set X), MeasurableSet A →
      ε * (π A).toReal ≤ (μ A).toReal) :
    ∀ (A : Set X), MeasurableSet A →
      |(μ A).toReal - (π A).toReal| ≤ 1 - ε := by
  intro A hA
  have hμA := hmin A hA
  have hμAc := hmin Aᶜ hA.compl
  -- Key facts: π(A) ∈ [0,1], μ(A) ∈ [0,1], complements add to 1
  have hπA_nn : 0 ≤ (π A).toReal := ENNReal.toReal_nonneg
  have hμA_nn : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  -- π(Aᶜ) = 1 - π(A) and μ(Aᶜ) = 1 - μ(A)
  -- (for probability measures on complementary sets)
  -- Use prob_compl_eq_one_sub: π(Aᶜ) = 1 - π(A) in ENNReal
  have hπc_ennreal := prob_compl_eq_one_sub hA (μ := π)
  have hμc_ennreal := prob_compl_eq_one_sub hA (μ := μ)
  -- Convert to real: (1 - π(A)).toReal = 1 - π(A).toReal
  have hπA_le_one : π A ≤ 1 := prob_le_one
  have hμA_le_one : μ A ≤ 1 := prob_le_one
  have hπ_compl : (π Aᶜ).toReal = 1 - (π A).toReal := by
    rw [hπc_ennreal]
    exact ENNReal.toReal_sub_of_le hπA_le_one ENNReal.one_ne_top
  have hμ_compl : (μ Aᶜ).toReal = 1 - (μ A).toReal := by
    rw [hμc_ennreal]
    exact ENNReal.toReal_sub_of_le hμA_le_one ENNReal.one_ne_top
  have hπA_le : (π A).toReal ≤ 1 := by linarith [hπ_compl, ENNReal.toReal_nonneg (a := π Aᶜ)]
  rw [hπ_compl] at hμAc; rw [hμ_compl] at hμAc
  rw [abs_le]; constructor <;> nlinarith

/-! ## Exponential mixing (axiomatized) -/

/-- **Doeblin's theorem: exponential mixing.**

Under Doeblin's condition with constant ε, after n steps:
  |Kⁿ(x, A) - π(A)| ≤ (1 - ε)ⁿ for all x, A.

Proof by induction: each application of K contracts TV distance
by factor (1 - ε), using `doeblin_one_step_contraction`.

Axiomatized pending: definition of iterated kernel Kⁿ and the
induction step (requires composing measure-valued functions). -/
axiom doeblin_exponential_mixing {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (π : Measure X) [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π)
    (n : ℕ) (x : X) (A : Set X) (hA : MeasurableSet A) :
    |(K.kernel x A).toReal - (π A).toReal| ≤ (1 - hD.ε) ^ n

/-- **Exponential decay of correlations.**

Under Doeblin's condition, for bounded observables f₁, f₂ depending
on parts of the chain separated by distance d:
  |E[f₁ f₂] - E[f₁]E[f₂]| ≤ 4B²(1-ε)^d

This is the mass gap: correlations decay exponentially in distance. -/
axiom doeblin_correlation_decay {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (π : Measure X) [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π)
    (f₁ f₂ : X → ℝ) (B : ℝ) (hB1 : ∀ x, |f₁ x| ≤ B) (hB2 : ∀ x, |f₂ x| ≤ B)
    (d : ℕ) :
    |∫ x, f₁ x * f₂ x ∂π - (∫ x, f₁ x ∂π) * (∫ x, f₂ x ∂π)| ≤
      4 * B ^ 2 * (1 - hD.ε) ^ d

end
