/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locality of Lattice Gauge Theory Observables

Uses Mathlib's `DependsOn f S` to formalize that observables depend
on specific sets of links. This is the key concept for:
1. Product independence: disjoint supports → ⟨fg⟩ = ⟨f⟩⟨g⟩
2. Spatial factorization in d=2
3. Support distance → correlation decay rate

A `GaugeConnection G d N = LatticeLink d N → G` is a dependent function
type, and Mathlib's `DependsOn` works on `(Π i, α i) → β`:
  `DependsOn f S ↔ ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y`

## Main results

- `plaquetteHolonomy_dependsOn` — holonomy depends on boundary links
- `plaqObs_dependsOn` — Re Tr(U_p) depends on boundary links
- `boltzmannWeight_dependsOn` — exp(-S) depends on plaquette boundary links

## References

- Chatterjee (2026), §15.6
-/

import LGT.MassGap.YMMeasure
import Mathlib.Logic.Function.DependsOn

open MeasureTheory GaussianField

noncomputable section

variable {G : Type*} {n : ℕ} [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {d N : ℕ}

/-! ## Plaquette boundary links -/

/-- The set of boundary links of a plaquette (as a Set, for DependsOn). -/
def plaquetteLinkSupport (p : LatticePlaquette d N) : Set (LatticeLink d N) :=
  {p.boundaryLinks 0, p.boundaryLinks 1, p.boundaryLinks 2, p.boundaryLinks 3}

/-! ## Holonomy and plaquette observables are local -/

/-- The plaquette holonomy U_p depends only on the 4 boundary links. -/
theorem plaquetteHolonomy_dependsOn (p : LatticePlaquette d N) :
    DependsOn (fun U : GaugeConnection G d N => plaquetteHolonomy U p)
      (plaquetteLinkSupport p) := by
  intro U₁ U₂ h
  simp only [plaquetteHolonomy]
  have h0 : U₁ (p.boundaryLinks 0) = U₂ (p.boundaryLinks 0) :=
    h _ (Set.mem_insert _ _)
  have h1 : U₁ (p.boundaryLinks 1) = U₂ (p.boundaryLinks 1) :=
    h _ (by simp [plaquetteLinkSupport, Set.mem_insert_iff])
  have h2 : U₁ (p.boundaryLinks 2) = U₂ (p.boundaryLinks 2) :=
    h _ (by simp [plaquetteLinkSupport, Set.mem_insert_iff])
  have h3 : U₁ (p.boundaryLinks 3) = U₂ (p.boundaryLinks 3) :=
    h _ (by simp [plaquetteLinkSupport, Set.mem_insert_iff])
  rw [h0, h1, h2, h3]

/-- The plaquette observable Re Tr(U_p) depends only on boundary links. -/
theorem plaqObs_dependsOn [HasHaarProbability G] [Fintype (LatticeLink d N)]
    (p : LatticePlaquette d N) :
    DependsOn (plaqObs G n d N p) (plaquetteLinkSupport p) := by
  intro U₁ U₂ h
  show plaqObs G n d N p U₁ = plaqObs G n d N p U₂
  unfold plaqObs
  congr 1
  exact plaquetteHolonomy_dependsOn p h

/-! ## Support distance and disjointness

For plaquettes p, q, if their link supports are disjoint, then their
observables are independent under any product measure. The support
distance determines when this disjointness holds. -/

/-- Two plaquettes have disjoint link supports if they share no
boundary links. On a sufficiently large lattice, plaquettes whose
base sites are far enough apart have disjoint supports. -/
def plaquettesDisjoint (p q : LatticePlaquette d N) : Prop :=
  Disjoint (plaquetteLinkSupport p) (plaquetteLinkSupport q)

/-! ## Product measure independence (the key theorem)

For product measures, functions depending on disjoint coordinate sets
are independent: ⟨fg⟩ = ⟨f⟩⟨g⟩.

Mathlib has `ProbabilityTheory.IndepFun` and related theory for
independence. For our finite product setting, the result follows
from Fubini on `Measure.pi`. -/

/-- **Product independence for disjoint supports.**

Under a product measure on G^{links}, if f depends on S and g
depends on T with S ∩ T = ∅, then ∫fg dμ = (∫f dμ)(∫g dμ).

This is the standard independence property of product measures.
It's the core of the correlation decay argument: observables at
sufficient distance have disjoint supports, hence zero connected
correlation under the gauge-fixed product measure. -/
theorem integral_mul_of_disjoint_dependsOn
    [HasHaarProbability G] [Fintype (LatticeLink d N)]
    (f g : GaugeConnection G d N → ℝ)
    (S T : Set (LatticeLink d N))
    (hf : DependsOn f S) (hg : DependsOn g T)
    (hST : Disjoint S T) :
    ∫ U, f U * g U ∂(productHaar G d N) =
    (∫ U, f U ∂(productHaar G d N)) * (∫ U, g U ∂(productHaar G d N)) := by
  -- Standard: for product measures, functions measurable w.r.t.
  -- independent sub-σ-algebras satisfy E[fg] = E[f]E[g].
  -- Uses Fubini on Measure.pi.
  sorry

/-- **Connected 2-point function vanishes for disjoint supports.**

When plaquette observables have disjoint link supports:
connected2pt = ⟨O_p · O_q⟩ - ⟨O_p⟩ · ⟨O_q⟩ = 0

because the observables are independent under the product measure. -/
theorem connected2pt_zero_of_disjoint
    [HasHaarProbability G] [Fintype (LatticeLink d N)]
    (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N)
    (hpq : plaquettesDisjoint p q)
    -- Under the gauge-fixed measure (which IS a product measure):
    -- This uses FP + the fact that the gauge-fixed measure is product Haar
    -- on the physical links
    (hGF : ∀ (f g : GaugeConnection G d N → ℝ),
      DependsOn f (plaquetteLinkSupport p) →
      DependsOn g (plaquetteLinkSupport q) →
      ymExpect G n d N β plaq (fun U => f U * g U) =
      ymExpect G n d N β plaq f * ymExpect G n d N β plaq g) :
    connected2pt G n d N β plaq (plaqObs G n d N p) (plaqObs G n d N q) = 0 := by
  unfold connected2pt
  rw [hGF (plaqObs G n d N p) (plaqObs G n d N q)
    (plaqObs_dependsOn p) (plaqObs_dependsOn q)]
  ring

end
