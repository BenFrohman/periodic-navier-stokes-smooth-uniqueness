/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Definitions (mirrored from `frohmanian-tether-sdiff`)

Every definition in this file is a verbatim copy (same body, same argument order) of the
definition of the same name in `BenFrohman/frohmanian-tether-sdiff` at commit `2abb3d6`:

* `T3`, `VelocityField`, `TimeDependentVelocity`, `TimeDependentPressure`, `PressureField`,
  `convective`, `laplacian`, `div`, `pressureGradient` — `FrohmanianTether/NS_Equations.lean`
  (namespace `NavierStokes3D`);
* `latticeVec`, `IsZ3Periodic`, `IsPeriodicSmoothSolutionOn` —
  `FrohmanianTether/ClayStatements.lean` (namespace `FrohmanianTether.ClayStatements`).

They live in the namespace `NSTorus` so that this project builds against Mathlib alone. The
bridge to `frohmanian-tether-sdiff` is to replace this file by an import of those modules;
every definition then agrees by `rfl`.
-/

open scoped ContDiff

namespace NSTorus

/-- Model 3-space `ℝ³`. -/
abbrev T3 : Type := EuclideanSpace ℝ (Fin 3)

abbrev VelocityField := T3 → EuclideanSpace ℝ (Fin 3)
abbrev PressureField := T3 → ℝ
abbrev TimeDependentVelocity := ℝ → VelocityField
abbrev TimeDependentPressure := ℝ → PressureField

noncomputable section

/-- Convective derivative `(u · ∇) v`, as the Fréchet derivative of `v` in the direction `u`. -/
def convective (u v : VelocityField) : VelocityField :=
  fun x => (fderiv ℝ v x) (u x)

/-- Laplacian as the trace of the Hessian. -/
def laplacian (f : VelocityField) : VelocityField :=
  fun x => ∑ i : Fin 3,
    (fderiv ℝ (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1)) x)
      (EuclideanSpace.single i 1)

/-- Divergence: `∑ᵢ ∂ᵢ uᵢ`. -/
def div (u : VelocityField) (x : T3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1)

/-- Pressure gradient, via Mathlib's `gradient`. -/
def pressureGradient (p : PressureField) : VelocityField :=
  fun x => gradient p x

/-- The lattice vector `∑ⱼ kⱼ eⱼ` for `k ∈ ℤ³`. -/
def latticeVec (k : Fin 3 → ℤ) : T3 :=
  ∑ j : Fin 3, ((k j : ℤ) : ℝ) • EuclideanSpace.single j (1 : ℝ)

end

/-- `f` is `ℤ³`-periodic, i.e. descends to `ℝ³/ℤ³`. -/
def IsZ3Periodic {α : Type*} (f : T3 → α) : Prop :=
  ∀ (k : Fin 3 → ℤ) (x : T3), f (x + latticeVec k) = f x

/-- `ℤ³`-periodicity is the unit-shift condition (verbatim proof from `frohmanian-tether-sdiff`). -/
theorem isZ3Periodic_iff_unit_shifts {α : Type*} (f : T3 → α) :
    IsZ3Periodic f ↔ ∀ (j : Fin 3) (x : T3), f (x + EuclideanSpace.single j 1) = f x := by
  constructor
  · intro h j x
    have := h (Pi.single j 1) x
    have hv : latticeVec (Pi.single j 1) = EuclideanSpace.single j (1 : ℝ) := by
      unfold latticeVec
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rwa [hv] at this
  · intro h k x
    have hper : ∀ j : Fin 3, Function.Periodic f (EuclideanSpace.single j (1 : ℝ)) :=
      fun j y => h j y
    have hz : ∀ (j : Fin 3) (n : ℤ) (y : T3),
        f (y + ((n : ℤ) : ℝ) • EuclideanSpace.single j (1 : ℝ)) = f y := by
      intro j n y
      have := (hper j).zsmul n y
      rwa [← Int.cast_smul_eq_zsmul ℝ] at this
    unfold latticeVec
    rw [Fin.sum_univ_three, ← add_assoc, ← add_assoc, hz, hz, hz]

/-- Unit cell `[0,1]³` (verbatim copy of `FrohmanianTether.ClayStatements.unitCube`). -/
def unitCube : Set T3 := {x | ∀ i : Fin 3, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Local smooth periodic solution on `[0, T)` (classical class: jointly C^∞, one-sided `∂ₜ`).
Verbatim copy of `FrohmanianTether.ClayStatements.IsPeriodicSmoothSolutionOn`. -/
def IsPeriodicSmoothSolutionOn (ν T : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Set.Ici 0) t + convective (u t) (u t) x +
        pressureGradient (p t) x = ν • laplacian (u t) x ∧ div (u t) x = 0) ∧
  u 0 = u₀ ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, IsZ3Periodic (u t) ∧ IsZ3Periodic (p t)

end NSTorus
