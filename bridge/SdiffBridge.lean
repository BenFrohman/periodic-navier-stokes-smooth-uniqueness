/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness
import FrohmanianTether.ClayStatements

/-!
# Bridge to `frohmanian-tether-sdiff` (not part of the default build)

Checks by `rfl` that the mirrored definitions in `NSTorusUniqueness/Defs.lean` are the
definitions of `frohmanian-tether-sdiff`, and transports the uniqueness theorem to the sdiff
predicate `FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn`.

Run (with both projects built, sharing one Mathlib build):
`LEAN_PATH=<this>/.lake/build/lib/lean:<sdiff>/.lake/build/lib/lean:<mathlib & deps> lean bridge/SdiffBridge.lean`
-/

open FrohmanianTether.ClayStatements

theorem NSTorus.convective_eq_sdiff : NSTorus.convective = NavierStokes3D.convective := rfl
theorem NSTorus.laplacian_eq_sdiff : NSTorus.laplacian = NavierStokes3D.laplacian := rfl
theorem NSTorus.div_eq_sdiff : NSTorus.div = NavierStokes3D.div := rfl
theorem NSTorus.pressureGradient_eq_sdiff :
    NSTorus.pressureGradient = NavierStokes3D.pressureGradient := rfl
theorem NSTorus.latticeVec_eq_sdiff : NSTorus.latticeVec = latticeVec := rfl
theorem NSTorus.unitCube_eq_sdiff : NSTorus.unitCube = unitCube := rfl
theorem NSTorus.isZ3Periodic_eq_sdiff {α : Type*} :
    @NSTorus.IsZ3Periodic α = @IsZ3Periodic α := rfl
theorem NSTorus.isPeriodicSmoothSolutionOn_eq_sdiff :
    NSTorus.IsPeriodicSmoothSolutionOn = IsPeriodicSmoothSolutionOn := rfl

/-- **Uniqueness, stated for the `frohmanian-tether-sdiff` predicate.** -/
theorem sdiff_periodic_smooth_solution_unique {ν T : ℝ} {u₀ : NavierStokes3D.VelocityField}
    {u v : NavierStokes3D.TimeDependentVelocity} {p q : NavierStokes3D.TimeDependentPressure}
    (hν : 0 ≤ ν) (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p)
    (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, u t = v t :=
  NSTorus.IsPeriodicSmoothSolutionOn.eq_of_same_data hν hu hv

#print axioms NSTorus.isPeriodicSmoothSolutionOn_eq_sdiff
#print axioms sdiff_periodic_smooth_solution_unique
