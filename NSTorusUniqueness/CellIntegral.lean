/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness.Defs
import NSTorusUniqueness.IteratedIntegral

/-!
# Integrals over the unit cell of fields on `ℝ³`; the periodic divergence theorem

`cellIntegral g = ∫₀¹∫₀¹∫₀¹ g(a,b,c) dc db da`, and the periodic divergence theorem
`∫_{[0,1]³} ∂ₖ φ = 0` for a `C¹`, `ℤ³`-periodic `φ` (`cellIntegral_fderiv_eq_zero`).

Provenance: adapted from the author's `BenFrohman/periodic-ns-classical-continuation`
(`TorusIntegral.lean`, `TorusField.lean`), retargeted to the `frohmanian-tether-sdiff`
definitions (`latticeVec`, `IsZ3Periodic` with the lattice vector first).
-/

open MeasureTheory Set NSTorus.Cell

namespace NSTorus

/-! ### Order facts for `torusIntegral` -/

lemma integral01_mono {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, φ x ≤ ψ x) : ∫ x in (0:ℝ)..1, φ x ≤ ∫ x in (0:ℝ)..1, ψ x :=
  intervalIntegral.integral_mono_on zero_le_one (hφ.intervalIntegrable 0 1)
    (hψ.intervalIntegrable 0 1) h

lemma integral01_eq_zero {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x)
    (hle : ∫ x in (0:ℝ)..1, φ x ≤ 0) : ∀ x ∈ Icc (0 : ℝ) 1, φ x = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨c, hc, hcne⟩ := hne
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => (0 : ℝ)) (g := φ) zero_lt_one continuousOn_const hφ.continuousOn
    (fun x hx => h0 x (Ioc_subset_Icc_self hx)) ⟨c, hc, lt_of_le_of_ne (h0 c hc) (Ne.symm hcne)⟩
  simp at hlt
  linarith

theorem torusIntegral_mono_on {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ)
    (h : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1,
      f (t, a, b, c) ≤ g (t, a, b, c)) :
    torusIntegral f t ≤ torusIntegral g t := by
  have c3f := cont_i3 hf; have c3g := cont_i3 hg
  have c2f := cont_i2 hf; have c2g := cont_i2 hg
  refine integral01_mono (by fun_prop) (by fun_prop) fun a ha => ?_
  refine integral01_mono (by fun_prop) (by fun_prop) fun b hb => ?_
  exact integral01_mono (by fun_prop) (by fun_prop) fun c hc => h a ha b hb c hc

theorem eq_zero_of_torusIntegral_nonpos {f : E → ℝ} (hf : Continuous f) (t : ℝ)
    (h0 : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ f (t, a, b, c))
    (hle : torusIntegral f t ≤ 0) :
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, f (t, a, b, c) = 0 := by
  have c3f := cont_i3 hf
  have c2f := cont_i2 hf
  have n3 : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, 0 ≤ i3 f (t, a, b) := fun a ha b hb => by
    have := integral01_mono (φ := fun _ => (0 : ℝ)) continuous_const (by fun_prop)
      (fun c hc => h0 a ha b hb c hc)
    simpa [i3] using this
  have n2 : ∀ a ∈ Icc (0 : ℝ) 1, 0 ≤ i2 f (t, a) := fun a ha => by
    have := integral01_mono (φ := fun _ => (0 : ℝ)) continuous_const (by fun_prop)
      (fun b hb => n3 a ha b hb)
    simpa [i2] using this
  have z2 := integral01_eq_zero (φ := fun a => i2 f (t, a)) (by fun_prop) n2 hle
  intro a ha b hb c hc
  have z3 := integral01_eq_zero (φ := fun b => i3 f (t, a, b)) (by fun_prop) (n3 a ha)
    (le_of_eq (z2 a ha)) b hb
  exact integral01_eq_zero (φ := fun c => f (t, a, b, c)) (by fun_prop) (h0 a ha b hb)
    (le_of_eq z3) c hc

/-! ### The unit cell of `T3` -/

/-- The point `(a, b, c)` of `T3`. -/
noncomputable def toT3 (a b c : ℝ) : T3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![a, b, c]

@[simp] lemma toT3_apply (a b c : ℝ) (i : Fin 3) : toT3 a b c i = ![a, b, c] i := rfl

lemma continuous_toT3 : Continuous fun q : E => toT3 q.2.1 q.2.2.1 q.2.2.2 := by
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

lemma continuous_toT3' : Continuous fun r : ℝ × ℝ × ℝ => toT3 r.1 r.2.1 r.2.2 :=
  continuous_toT3.comp ((continuous_const.prodMk continuous_id :
    Continuous fun r : ℝ × ℝ × ℝ => ((0 : ℝ), r)))

/-- Lift of a field on `T3` to the coordinates `(t, a, b, c)` used by `torusIntegral`. -/
noncomputable def lift {α : Type*} (g : T3 → α) : E → α :=
  fun q => g (toT3 q.2.1 q.2.2.1 q.2.2.2)

lemma continuous_lift {α : Type*} [TopologicalSpace α] {g : T3 → α} (hg : Continuous g) :
    Continuous (lift g) := hg.comp continuous_toT3

/-- `∫_{[0,1]³} g`, as the iterated integral `∫₀¹∫₀¹∫₀¹ g(a,b,c) dc db da`. -/
noncomputable def cellIntegral (g : T3 → ℝ) : ℝ := torusIntegral (lift g) 0

lemma toT3_shift0 (a b c x : ℝ) :
    toT3 x b c = toT3 a b c + (x - a) • EuclideanSpace.single 0 1 := by
  ext i; fin_cases i <;> simp
lemma toT3_shift1 (a b c x : ℝ) :
    toT3 a x c = toT3 a b c + (x - b) • EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp
lemma toT3_shift2 (a b c x : ℝ) :
    toT3 a b x = toT3 a b c + (x - c) • EuclideanSpace.single 2 1 := by
  ext i; fin_cases i <;> simp

lemma hasDerivAt_line {φ : T3 → ℝ} (hφ : Differentiable ℝ φ) (p : T3) (k : Fin 3) (a₀ x : ℝ) :
    HasDerivAt (fun y : ℝ => φ (p + (y - a₀) • EuclideanSpace.single k (1 : ℝ)))
      (fderiv ℝ φ (p + (x - a₀) • EuclideanSpace.single k (1 : ℝ))
        (EuclideanSpace.single k 1)) x := by
  have hl : HasDerivAt (fun y : ℝ => p + (y - a₀) • EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k 1) x := by
    simpa using (((hasDerivAt_id x).sub_const a₀).smul_const
      (EuclideanSpace.single k (1 : ℝ))).const_add p
  exact (hφ _).hasFDerivAt.comp_hasDerivAt x hl

/-- **M1(a). Periodic divergence theorem on the unit cell:** `∫_{[0,1]³} ∂ₖ φ = 0` for
`φ ∈ C¹(ℝ³)` that is `ℤ³`-periodic. -/
theorem cellIntegral_fderiv_eq_zero {φ : T3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hper : IsZ3Periodic φ)
    (k : Fin 3) : cellIntegral (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) = 0 := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hc : Continuous fun x => fderiv ℝ φ x (EuclideanSpace.single k 1) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hu := (isZ3Periodic_iff_unit_shifts φ).1 hper
  unfold cellIntegral
  fin_cases k
  · refine torusIntegral_deriv_a (f := lift φ) (continuous_lift hd.continuous)
      (continuous_lift hc) (fun t a b c => ?_) (fun t a b c => ?_) 0
    · have := hasDerivAt_line hd (toT3 a b c) 0 a a
      simp only [sub_self, zero_smul, add_zero] at this
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [lift, ← toT3_shift0]
    · have := hu 0 (toT3 a b c)
      simp only [lift]
      rw [← this]; congr 1; ext i; fin_cases i <;> simp
  · refine torusIntegral_deriv_b (f := lift φ) (continuous_lift hd.continuous)
      (continuous_lift hc) (fun t a b c => ?_) (fun t a b c => ?_) 0
    · have := hasDerivAt_line hd (toT3 a b c) 1 b b
      simp only [sub_self, zero_smul, add_zero] at this
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [lift, ← toT3_shift1]
    · have := hu 1 (toT3 a b c)
      simp only [lift]
      rw [← this]; congr 1; ext i; fin_cases i <;> simp
  · refine torusIntegral_deriv_c (f := lift φ)
      (continuous_lift hc) (fun t a b c => ?_) (fun t a b c => ?_) 0
    · have := hasDerivAt_line hd (toT3 a b c) 2 c c
      simp only [sub_self, zero_smul, add_zero] at this
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [lift, ← toT3_shift2]
    · have := hu 2 (toT3 a b c)
      simp only [lift]
      rw [← this]; congr 1; ext i; fin_cases i <;> simp

/-! ### Linearity and order on the cell -/

lemma integral01_add {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ∫ x in (0:ℝ)..1, (φ x + ψ x) = (∫ x in (0:ℝ)..1, φ x) + ∫ x in (0:ℝ)..1, ψ x :=
  intervalIntegral.integral_add (hφ.intervalIntegrable 0 1) (hψ.intervalIntegrable 0 1)

theorem torusIntegral_add' {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    torusIntegral (fun q => f q + g q) t = torusIntegral f t + torusIntegral g t := by
  have c3f := cont_i3 hf; have c3g := cont_i3 hg
  have c2f := cont_i2 hf; have c2g := cont_i2 hg
  have h3 : ∀ q, i3 (fun q => f q + g q) q = i3 f q + i3 g q := fun q =>
    integral01_add (by fun_prop) (by fun_prop)
  have h2 : ∀ q, i2 (fun q => f q + g q) q = i2 f q + i2 g q := fun q => by
    simp only [Cell.i2, h3]; exact integral01_add (by fun_prop) (by fun_prop)
  simp only [Cell.torusIntegral, h2]; exact integral01_add (by fun_prop) (by fun_prop)

theorem torusIntegral_const_mul (r : ℝ) (f : E → ℝ) (t : ℝ) :
    torusIntegral (fun q => r * f q) t = r * torusIntegral f t := by
  simp [Cell.torusIntegral, Cell.i2, Cell.i3, intervalIntegral.integral_const_mul]

lemma cellIntegral_add {g h : T3 → ℝ} (hg : Continuous g) (hh : Continuous h) :
    cellIntegral (fun x => g x + h x) = cellIntegral g + cellIntegral h :=
  torusIntegral_add' (continuous_lift hg) (continuous_lift hh) 0

lemma cellIntegral_sub {g h : T3 → ℝ} (hg : Continuous g) (hh : Continuous h) :
    cellIntegral (fun x => g x - h x) = cellIntegral g - cellIntegral h := by
  have := cellIntegral_add hg (hh.neg)
  have h2 : cellIntegral (fun x => -h x) = -cellIntegral h := by
    have := torusIntegral_const_mul (-1) (lift h) 0
    simpa [cellIntegral, lift] using this
  simp only [← sub_eq_add_neg] at this
  rw [this, h2, sub_eq_add_neg]

lemma cellIntegral_const_mul (r : ℝ) (g : T3 → ℝ) :
    cellIntegral (fun x => r * g x) = r * cellIntegral g :=
  torusIntegral_const_mul r (lift g) 0

lemma cellIntegral_sum {g : Fin 3 → T3 → ℝ} (hg : ∀ k, Continuous (g k)) :
    cellIntegral (fun x => ∑ k, g k x) = ∑ k, cellIntegral (g k) := by
  simp only [Fin.sum_univ_three]
  rw [cellIntegral_add (by fun_prop) (hg 2), cellIntegral_add (hg 0) (hg 1)]

lemma cellIntegral_zero : cellIntegral (fun _ => (0 : ℝ)) = 0 := by
  have := cellIntegral_const_mul 0 (fun _ => (0 : ℝ)); simpa using this

lemma cellIntegral_mono_on {g h : T3 → ℝ} (hg : Continuous g) (hh : Continuous h)
    (H : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1,
      g (toT3 a b c) ≤ h (toT3 a b c)) : cellIntegral g ≤ cellIntegral h :=
  torusIntegral_mono_on (continuous_lift hg) (continuous_lift hh) 0 H

/-- Integral of a periodic divergence vanishes. -/
theorem cellIntegral_sum_fderiv_eq_zero {φ : Fin 3 → T3 → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k))
    (hper : ∀ k, IsZ3Periodic (φ k)) :
    cellIntegral (fun x => ∑ k, fderiv ℝ (φ k) x (EuclideanSpace.single k 1)) = 0 := by
  rw [cellIntegral_sum fun k => ((hφ k).continuous_fderiv one_ne_zero).clm_apply continuous_const]
  simp [cellIntegral_fderiv_eq_zero (hφ _) (hper _)]

/-- Every point of `ℝ³` is a point of the closed unit cell plus a lattice vector. -/
lemma exists_cell (x : T3) : ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1, ∃ c ∈ Icc (0 : ℝ) 1,
    ∃ k : Fin 3 → ℤ, x = toT3 a b c + latticeVec k := by
  have hf : ∀ r : ℝ, Int.fract r ∈ Icc (0 : ℝ) 1 := fun r =>
    ⟨Int.fract_nonneg r, (Int.fract_lt_one r).le⟩
  refine ⟨_, hf (x 0), _, hf (x 1), _, hf (x 2), fun i => ⌊x i⌋, ?_⟩
  ext i; fin_cases i <;> simp [latticeVec, Fin.sum_univ_three, Int.fract_add_floor]

/-- A continuous `ℤ³`-periodic `g ≥ 0` with `∫_{[0,1]³} g ≤ 0` vanishes identically. -/
theorem eq_zero_of_cellIntegral_nonpos {g : T3 → ℝ} (hg : Continuous g) (hper : IsZ3Periodic g)
    (h0 : ∀ x, 0 ≤ g x) (hle : cellIntegral g ≤ 0) : ∀ x, g x = 0 := by
  have hz := eq_zero_of_torusIntegral_nonpos (continuous_lift hg) 0
    (fun a _ b _ c _ => h0 _) hle
  intro x
  obtain ⟨a, ha, b, hb, c, hc, k, rfl⟩ := exists_cell x
  rw [hper k]
  exact hz a ha b hb c hc

lemma isZ3Periodic_fderiv {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] {g : T3 → α}
    (hg : IsZ3Periodic g) : IsZ3Periodic (fderiv ℝ g) := by
  intro k x
  rw [← fderiv_comp_add_right]
  congr 1; funext y; exact hg k y

end NSTorus
