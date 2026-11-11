/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness.Uniqueness
import NSTorusUniqueness.CellLebesgue

/-!
# Headline statements, with Mathlib's Lebesgue integral over the unit cube

Milestone M1 (periodic calculus on the unit cell) and the energy inequality, restated with
`∫ x in unitCube, _` (Mathlib Bochner integral, Lebesgue measure on `EuclideanSpace ℝ (Fin 3)`),
using `cellIntegral_eq_setIntegral_unitCube`. Milestone M2 (uniqueness) is in
`NSTorusUniqueness/Uniqueness.lean`.
-/

open Set MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff

namespace NSTorus

local notation "e" k => EuclideanSpace.single k (1 : ℝ)

/-- **M1(a).** `∫_{[0,1]³} ∂ₖ φ = 0` for `ℤ³`-periodic `φ ∈ C¹`. -/
theorem setIntegral_unitCube_fderiv_eq_zero {φ : T3 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hper : IsZ3Periodic φ) (k : Fin 3) :
    ∫ x in unitCube, fderiv ℝ φ x (e k) = 0 := by
  rw [← cellIntegral_eq_setIntegral_unitCube
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)]
  exact cellIntegral_fderiv_eq_zero hφ hper k

/-- **M1(b).** `∫_{[0,1]³} ⟨w, (a·∇)w⟩ = 0` for `ℤ³`-periodic `C¹` fields with `div a = 0`. -/
theorem setIntegral_unitCube_inner_convective_eq_zero {a w : VelocityField}
    (ha : ContDiff ℝ 1 a) (hw : ContDiff ℝ 1 w) (hdiv : ∀ x, div a x = 0)
    (pa : IsZ3Periodic a) (pw : IsZ3Periodic w) :
    ∫ x in unitCube, ⟪w x, convective a w x⟫ = 0 := by
  rw [← cellIntegral_eq_setIntegral_unitCube (g := fun x => ⟪w x, convective a w x⟫)
    (hw.continuous.inner ((hw.continuous_fderiv one_ne_zero).clm_apply ha.continuous))]
  exact cellIntegral_inner_convective_eq_zero ha hw hdiv pa pw

/-- **M1(c).** `∫_{[0,1]³} ⟨w, ∇π⟩ = 0` for `ℤ³`-periodic `C¹` `w, π` with `div w = 0`. -/
theorem setIntegral_unitCube_inner_pressureGradient_eq_zero {w : VelocityField} {π : T3 → ℝ}
    (hw : ContDiff ℝ 1 w) (hπ : ContDiff ℝ 1 π) (hdiv : ∀ x, div w x = 0)
    (pw : IsZ3Periodic w) (pπ : IsZ3Periodic π) :
    ∫ x in unitCube, ⟪w x, pressureGradient π x⟫ = 0 := by
  rw [← cellIntegral_eq_setIntegral_unitCube (hw.continuous.inner
    (continuous_pressureGradient hπ))]
  exact cellIntegral_inner_pressureGradient_eq_zero hw hπ hdiv pw pπ

/-- **M1(d).** `∫_{[0,1]³} ⟨w, Δw⟩ = −∫_{[0,1]³} Σₖ |∂ₖw|² ≤ 0` for `ℤ³`-periodic `C²` `w`. -/
theorem setIntegral_unitCube_inner_laplacian {w : VelocityField} (hw : ContDiff ℝ 2 w)
    (pw : IsZ3Periodic w) :
    ∫ x in unitCube, ⟪w x, laplacian w x⟫ =
      -∫ x in unitCube, ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2 := by
  have dk : ∀ k : Fin 3, Continuous (fun y => fderiv ℝ w y (e k)) := fun k =>
    ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
  rw [← cellIntegral_eq_setIntegral_unitCube (hw.continuous.inner (continuous_laplacian hw)),
    ← cellIntegral_eq_setIntegral_unitCube
      (continuous_finset_sum _ fun k _ => ((dk k).norm).pow 2)]
  exact cellIntegral_inner_laplacian hw pw

theorem setIntegral_unitCube_inner_laplacian_nonpos {w : VelocityField} (hw : ContDiff ℝ 2 w)
    (pw : IsZ3Periodic w) : ∫ x in unitCube, ⟪w x, laplacian w x⟫ ≤ 0 := by
  rw [← cellIntegral_eq_setIntegral_unitCube (hw.continuous.inner (continuous_laplacian hw))]
  exact cellIntegral_inner_laplacian_nonpos hw pw

section energy

variable {ν T : ℝ} {u v : TimeDependentVelocity} {p q : TimeDependentPressure}

lemma continuous_Gf_slice (cu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
    (cv : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => v q.1 q.2) (S T)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    Continuous fun x => Gf u v (t, x) :=
  (continuousOn_Gf cu cv).comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨ht, trivial⟩

lemma continuous_Gd_slice (hT : 0 < T) (cu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
    (cv : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => v q.1 q.2) (S T)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    Continuous fun x => Gd T u v (t, x) :=
  (continuousOn_Gd hT cu cv).comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨ht, trivial⟩

/-- **M1(e). Differentiating `∫_{[0,1]³} |w|²` under the integral sign.** For `u, v` jointly
`C^∞` on `[0, T] × ℝ³`, `T > 0`, and `t ∈ [0, T]`:
`d/dt ∫_{[0,1]³} |u − v|² = ∫_{[0,1]³} 2⟨u − v, ∂ₜu − ∂ₜv⟩` (within `[0, T]`). -/
theorem hasDerivWithinAt_setIntegral_unitCube_energy (hT : 0 < T)
    (cu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
    (cv : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => v q.1 q.2) (S T)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    HasDerivWithinAt (fun s => ∫ x in unitCube, ‖u s x - v s x‖ ^ 2)
      (∫ x in unitCube, 2 * ⟪u t x - v t x, D T u (t, x) (1, 0) - D T v (t, x) (1, 0)⟫)
      (Icc (0 : ℝ) T) t := by
  have h := hasDerivWithinAt_cellEnergy hT cu cv ht
  have hGf : ∀ s ∈ Icc (0:ℝ) T, (cellIntegral fun x => ‖u s x - v s x‖ ^ 2) =
      ∫ x in unitCube, ‖u s x - v s x‖ ^ 2 := fun s hs => by
    refine cellIntegral_eq_setIntegral_unitCube ?_
    have := continuous_Gf_slice cu cv hs
    simpa [Gf, real_inner_self_eq_norm_sq] using this
  rw [cellIntegral_eq_setIntegral_unitCube (g := fun x =>
    2 * ⟪u t x - v t x, D T u (t, x) (1, 0) - D T v (t, x) (1, 0)⟫)
    (continuous_Gd_slice hT cu cv ht)] at h
  exact h.congr (fun s hs => (hGf s hs).symm) (hGf t ht).symm

/-- **Energy inequality.** For `ν ≥ 0`, two classical periodic solutions on `[0, T] × ℝ³`, and
`‖∇v(t, ·)‖ ≤ C`, with `w = u − v`:
`∫_{[0,1]³} 2⟨w, ∂ₜw⟩ ≤ 2C ∫_{[0,1]³} |w|²`. -/
theorem setIntegral_unitCube_energy_deriv_le (hν : 0 ≤ ν) (hT : 0 < T)
    (hu : IsPeriodicSmoothSolutionIcc ν T u p) (hv : IsPeriodicSmoothSolutionIcc ν T v q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ (v t) x‖ ≤ C) :
    ∫ x in unitCube, 2 * ⟪u t x - v t x, D T u (t, x) (1, 0) - D T v (t, x) (1, 0)⟫ ≤
      2 * C * ∫ x in unitCube, ‖u t x - v t x‖ ^ 2 := by
  have h := cellEnergy_deriv_le hν hu hv ht hC
  rw [cellIntegral_eq_setIntegral_unitCube (continuous_Gd_slice hT hu.1 hv.1 ht),
    cellIntegral_eq_setIntegral_unitCube (continuous_Gf_slice hu.1 hv.1 ht)] at h
  simpa [Gd, Gf, real_inner_self_eq_norm_sq] using h

end energy

end NSTorus
