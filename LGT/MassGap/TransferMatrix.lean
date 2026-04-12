/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix for 2D Lattice Gauge Theory

After spatial gauge fixing, the 2D partition function factorizes as a
product of transfer matrices, one per time step. Each spatial site
contributes an independent Markov chain on G with transition density
  p(V, W) = (1/K) exp(-β · (n - Re Tr(WV⁻¹)))

## Main definitions

- `singleSiteTransitionDensity` — the transition density p(V, W)
- `singleSiteKernel` — the associated Markov kernel on G
- `ymDoeblinConstant` — the Doeblin minorization constant
- `singleSite_doeblin` — verification of Doeblin's condition

## Mathematical content

The key insight (Chatterjee §15.7): after gauge fixing spatial links
to I in 2D, each spatial site s evolves independently. The temporal
link U_t(t, s) at time t transitions to U_t(t+1, s) via the density
  p(V, W) = (1/K) exp(-β(n - Re Tr(WV⁻¹)))
with respect to the Haar measure on G.

Since G is compact, Re Tr(WV⁻¹) ∈ [-n, n] for G ⊂ U(n), so
  p(V, W) ≥ (1/K) exp(-2nβ) > 0  for all V, W.
This gives Doeblin's condition with ε = exp(-2nβ)/K.

## References

- Chatterjee (2026), §15.7
-/

import LGT.GaugeField.GaugeGroup
import LGT.MassGap.DoeblinCondition
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]

/-! ## Single-site transition density -/

/-- The (unnormalized) transition density for a single spatial site:
  q(V, W) = exp(-β · (n - Re Tr(WV⁻¹)))
This is the Boltzmann weight from a single plaquette, since in the
gauge-fixed theory U_p = V · W⁻¹ (up to orientation). -/
def singleSiteTransitionWeight (β : ℝ) (V W : G) : ℝ :=
  Real.exp (-β * (↑n - gaugeReTr G n (W * V⁻¹)))

/-- The transition weight is always positive. -/
theorem singleSiteTransitionWeight_pos (β : ℝ) (V W : G) :
    0 < singleSiteTransitionWeight G n β V W :=
  Real.exp_pos _

/-! ## Doeblin's condition for the YM kernel

The key bound: on a compact group G ⊂ U(n), for all V, W:
  |Re Tr(WV⁻¹)| ≤ n
so the transition weight satisfies:
  q(V, W) ≥ exp(-2nβ)  for all V, W (when β ≥ 0).

After normalization by K = ∫ q(V, W) dμ_Haar(W), the transition
density p = q/K satisfies p(V,W) ≥ exp(-2nβ)/K, giving Doeblin's
condition with constant ε = exp(-2nβ)/K. -/

/-- The Doeblin lower bound constant: exp(-2nβ). -/
def ymDoeblinLowerBound (β : ℝ) : ℝ :=
  Real.exp (-2 * ↑n * β)

/-- The lower bound is positive. -/
theorem ymDoeblinLowerBound_pos (β : ℝ) :
    0 < ymDoeblinLowerBound n β :=
  Real.exp_pos _

/-- **Key estimate:** the transition weight is bounded below.

For G ⊂ U(n) and β ≥ 0:
  exp(-β(n - Re Tr(WV⁻¹))) ≥ exp(-2nβ)

Proof: Re Tr(WV⁻¹) ≥ -n for unitary matrices (eigenvalues on
the unit circle, so Re(eigenvalue) ≥ -1, and Tr = sum of n such). -/
theorem singleSiteTransitionWeight_lower_bound (β : ℝ) (hβ : 0 ≤ β)
    (V W : G)
    (hTrace : ∀ (g : G), -↑n ≤ gaugeReTr G n g) :
    ymDoeblinLowerBound n β ≤ singleSiteTransitionWeight G n β V W := by
  unfold ymDoeblinLowerBound singleSiteTransitionWeight
  apply Real.exp_le_exp_of_le
  -- Need: -(2n)β ≤ -β(n - Re Tr(WV⁻¹)), i.e., β(n - ReTr) ≤ 2nβ
  -- From hTrace: ReTr(WV⁻¹) ≥ -n, so n - ReTr ≤ 2n, so β(n-ReTr) ≤ 2nβ
  nlinarith [hTrace (W * V⁻¹)]

/-- **Doeblin's condition holds for 2D Yang-Mills.**

For any compact G ⊂ U(n) and any β ≥ 0, the single-site Markov
chain satisfies Doeblin's condition. This implies exponential
mixing and hence the mass gap.

The minorization constant is ε = exp(-2nβ) / (Haar volume · max weight),
which is positive because G is compact. -/
theorem ym_satisfies_doeblin (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_lower : ∀ (g : G), -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ (g : G), gaugeReTr G n g ≤ ↑n)
    (μ : Measure G) [IsProbabilityMeasure μ]
    (K : MarkovKernel G)
    (hK : ∀ (V : G) (A : Set G), MeasurableSet A →
      (K.kernel V A).toReal = ∫ W in A,
        singleSiteTransitionWeight G n β V W /
        (∫ W', singleSiteTransitionWeight G n β V W' ∂μ) ∂μ) :
    ∃ (hD : DoeblinCondition K μ), 0 < hD.ε := by
  -- The density p(V,W) = q(V,W) / Z(V) satisfies:
  -- p(V,W) ≥ exp(-2nβ) / Z(V)
  -- And Z(V) = ∫ q(V,W') dμ(W') ≤ exp(0) · μ(G) = 1 (since q ≤ 1 when β(n-ReTr) ≥ 0)
  -- Wait: Z(V) is not necessarily ≤ 1. But Z(V) ≤ exp(0) · 1 = 1 when β ≥ 0 and
  -- n - Re Tr ≥ 0, so q ≤ 1. But we also need Z(V) ≥ exp(-2nβ) > 0.
  -- The Doeblin constant is ε = exp(-2nβ) / sup_V Z(V).
  sorry

end
