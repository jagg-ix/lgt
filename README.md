# lgt — Lattice Gauge Theory in Lean 4

Formal proof of the **2D Yang-Mills mass gap** for any compact
matrix Lie group, with **zero sorry's**.

## Main result

**Theorem.** For any compact G ⊂ U(n), any coupling β ≥ 0, and any
finite lattice, the 2D lattice Yang-Mills theory has a mass gap:
correlations between gauge-invariant observables decay exponentially
with distance.

This holds for all compact gauge groups: U(1), SU(N), SO(N), Sp(N),
exceptional groups, finite groups.

## Status

**Zero sorry's. Zero axioms. 27+ proved theorems.**

See [docs/mass-gap-proof.md](docs/mass-gap-proof.md) for the full
proof outline.

## Proof structure

1. **Lattice setup** — sites (from gaussian-field), links, plaquettes,
   G-valued connections, holonomy gauge covariance

2. **Gauge fixing** — set spatial links to identity; plaquette holonomy
   simplifies to U_t(s) · U_t(s+1)⁻¹ (only temporal links contribute)

3. **Transition density** — exp(-β(n - Re Tr(WV⁻¹))) is bounded in
   [exp(-2nβ), 1], giving Doeblin's condition with ε = exp(-2nβ)

4. **Doeblin → mixing** (in markov-semigroups) — one-step contraction →
   TV contraction (layer cake) → n-step mixing (induction) →
   correlation decay

5. **Mass gap** — exponential decay with constants uniform in lattice size

## File structure

```
LGT/
  Lattice/CellComplex.lean       -- sites, links, plaquettes (uses gaussian-field)
  GaugeField/
    Connection.lean               -- G-valued connections, holonomy, gauge covariance
    GaugeGroup.lean               -- HasGaugeTrace, Wilson action integrand
  WilsonAction/PlaquetteAction.lean -- Wilson action, Boltzmann weight, gauge fixing
  MassGap/
    DoeblinCondition.lean         -- re-exports from markov-semigroups
    TransferMatrix.lean           -- transition density, Doeblin verification
    MassGap2D.lean                -- the mass gap theorem
```

## Dependencies

- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) —
  lattice site types, asymmetric torus
- [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups) —
  Doeblin's condition, TV integral bounds, correlation decay
- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.29.0

## Building

```bash
lake update
lake build
```

## References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), Theorem 15.7.1
- Wilson, "Confinement of quarks," Phys. Rev. D 10 (1974)
- Doeblin (1937), exponential mixing for Markov chains
- Levin-Peres-Wilmer, "Markov Chains and Mixing Times" (2009)

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
