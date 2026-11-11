# periodic-navier-stokes-smooth-uniqueness

Lean 4 / Mathlib proof, kernel-checked, of the **uniqueness of classical (C^∞) ℤ³-periodic
solutions of the incompressible Navier–Stokes equations** with the same initial velocity, by the
energy method and Grönwall's inequality. Uses only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); no `sorry`, no `native_decide`, no axiom declarations.

This is a classical theorem (energy uniqueness: Serrin 1963; Temam 1995; Constantin–Foias 1988;
Robinson–Rodrigo–Sadowski 2016). The contribution is the complete formalization. It does **not**
address existence or global regularity.

## Main theorem (`NSTorusUniqueness/Uniqueness.lean`)

```lean
theorem NSTorus.IsPeriodicSmoothSolutionOn.eq_of_same_data {ν T : ℝ} {u₀ : VelocityField}
    {u v : TimeDependentVelocity} {p q : TimeDependentPressure} (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, u t = v t
```

plus `pressureGradient_eq_of_same_data` (∇p = ∇q) and `pressure_sub_const_of_same_data`
(p(t) − q(t) is constant in space). `IsPeriodicSmoothSolutionOn` is a verbatim copy of the class
in `BenFrohman/frohmanian-tether-sdiff` (`FrohmanianTether/ClayStatements.lean`); see
`bridge/SdiffBridge.lean` for the `rfl` check against the compiled sdiff definitions.

## Milestones

* **M1, periodic calculus on the unit cell** (`CellIntegral.lean`, `FieldIdentities.lean`,
  `Energy.lean`, `Main.lean`): ∫ ∂ₖφ = 0; ∫⟨w,(a·∇)w⟩ = 0 for div a = 0; ∫⟨w,∇π⟩ = 0 for
  div w = 0; ∫⟨w,Δw⟩ = −∫Σₖ|∂ₖw|² ≤ 0; d/dt ∫|w|² = ∫2⟨w,∂ₜw⟩; and the energy inequality
  ∫2⟨w,∂ₜw⟩ ≤ 2C∫|w|² for ‖∇v‖ ≤ C. Stated both for the iterated integral `cellIntegral` and for
  Mathlib's Lebesgue integral `∫ x in unitCube, _` (`cellIntegral_eq_setIntegral_unitCube`).
* **M2, uniqueness** (`Uniqueness.lean`): Grönwall via Mathlib
  `le_gronwallBound_of_liminf_deriv_right_le`.

## Verify (one command)

```
git clone https://github.com/BenFrohman/periodic-navier-stokes-smooth-uniqueness
cd periodic-navier-stokes-smooth-uniqueness
bash scripts/verify.sh
```

`scripts/verify.sh` fetches the prebuilt Mathlib cache, runs `lake build`, scans the sources for
`sorry`/`admit`/`native_decide`/`axiom`, and runs `AxiomAudit.lean` (a `#print axioms` for the 22
headline theorems plus a strict audit of every declaration in the `NSTorus` namespace). It needs
`elan` on the `PATH`; CI (`.github/workflows/verify.yml`) runs the same script.

Pins:

* Lean toolchain: `leanprover/lean4:v4.30.0-rc1` (`lean-toolchain`)
* Mathlib: `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (`lake-manifest.json`, input rev `v4.30.0-rc1`)

These are the same pins as `BenFrohman/frohmanian-tether-sdiff`.

Axiom output (end of `scripts/verify.sh`, from a clean build):

```
Build completed successfully (8274 jobs).
OK: no sorry/admit/native_decide/axiom declarations
'NSTorus.IsPeriodicSmoothSolutionOn.eq_of_same_data' depends on axioms: [propext, Classical.choice, Quot.sound]
...
AUDIT PASS: 168 NSTorus declarations; only propext, Classical.choice, Quot.sound
AXIOM AUDIT PASS: 22 theorems, only propext, Classical.choice, Quot.sound
VERIFY OK
```

## Bridge to frohmanian-tether-sdiff

`bridge/SdiffBridge.lean` is not part of the default build, because this project depends on
Mathlib alone. It checks by `rfl`, against the compiled sdiff definitions, that `convective`,
`laplacian`, `div`, `pressureGradient`, `latticeVec`, `unitCube`, `IsZ3Periodic` and
`IsPeriodicSmoothSolutionOn` are the sdiff definitions. It also proves
`sdiff_periodic_smooth_solution_unique` for the sdiff predicate.

## Provenance

`IteratedIntegral.lean`, `Clamp.lean` and parts of `CellIntegral.lean`, `FieldIdentities.lean`
and `Energy.lean` are ported from the author's `BenFrohman/weighted-enstrophy-identities`
(`1df4652`) and `BenFrohman/periodic-ns-classical-continuation`, which proved the same energy
estimate for the `fefferman-clay-navier-stokes` solution class on a closed interval `[0, T]`.
This project retargets the argument to the `frohmanian-tether-sdiff` class (half-open `[0, T)`,
one-sided `derivWithin … (Ici 0)`), depends on Mathlib alone, and adds the Lebesgue-integral
statements and pressure uniqueness.

© 2026 Benjamin Stanley Frohman. Apache 2.0.
