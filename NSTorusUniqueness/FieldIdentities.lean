/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness.CellIntegral

/-!
# Pointwise divergence-form identities and their cell integrals (Milestone M1)

Pointwise product rules:

* `2⟨w, (a·∇)w⟩ = Σₖ ∂ₖ(|w|² aₖ) − |w|² div a`;
* `⟨w, Δw⟩ = Σₖ ∂ₖ⟨w, ∂ₖw⟩ − Σₖ |∂ₖw|²`;
* `⟨w, ∇π⟩ = Σₖ ∂ₖ(π wₖ) − π div w`.

Integrated over the unit cell for `ℤ³`-periodic fields (M1):

* `cellIntegral_inner_convective_eq_zero`: `∫ ⟨w, (a·∇)w⟩ = 0` if `div a = 0`;
* `cellIntegral_inner_pressureGradient_eq_zero`: `∫ ⟨w, ∇π⟩ = 0` if `div w = 0`;
* `cellIntegral_inner_laplacian`: `∫ ⟨w, Δw⟩ = −∫ Σₖ |∂ₖw|² ≤ 0`.

Provenance of the pointwise part: the author's `periodic-ns-classical-continuation`
(`FieldIdentities.lean`), retargeted to the `frohmanian-tether-sdiff` definitions.
-/

open InnerProductSpace
open scoped RealInnerProductSpace

namespace NSTorus


local notation "e" k => EuclideanSpace.single k (1 : ℝ)

lemma expand (v : T3) : v = ∑ k : Fin 3, v k • (e k) := by
  ext i; fin_cases i <;> simp [Fin.sum_univ_three]

lemma clm_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : T3 →L[ℝ] F) (v : T3) :
    L v = ∑ k : Fin 3, v k • L (e k) := by
  conv_lhs => rw [expand v]
  simp [map_sum, map_smul]

lemma differentiable_comp {a : VelocityField} (ha : Differentiable ℝ a) (i : Fin 3) :
    Differentiable ℝ fun y => a y i :=
  (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).differentiable.comp ha

lemma contDiff_comp {a : VelocityField} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a) (i : Fin 3) :
    ContDiff ℝ n fun y => a y i :=
  (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp ha

lemma fderiv_comp_apply {a : VelocityField} (ha : Differentiable ℝ a) (i : Fin 3) (x h : T3) :
    fderiv ℝ (fun y => a y i) x h = fderiv ℝ a x h i := by
  have := ((EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt.comp x (ha x).hasFDerivAt).fderiv
  rw [show (fun y => a y i) = (EuclideanSpace.proj i : T3 →L[ℝ] ℝ) ∘ a from rfl, this]
  rfl

/-- `Σₖ ∂ₖ(g aₖ) = ∇g · a + g div a`. -/
theorem sum_fderiv_mul {g : T3 → ℝ} {a : VelocityField} (hg : Differentiable ℝ g)
    (ha : Differentiable ℝ a) (x : T3) :
    ∑ k : Fin 3, fderiv ℝ (fun y => g y * a y k) x (e k) =
      fderiv ℝ g x (a x) + g x * div a x := by
  have h : ∀ k : Fin 3, fderiv ℝ (fun y => g y * a y k) x (e k) =
      a x k * fderiv ℝ g x (e k) + g x * fderiv ℝ (fun y => a y k) x (e k) := fun k => by
    rw [fderiv_fun_mul (hg x) (differentiable_comp ha k x)]
    simp; ring
  simp only [h, Finset.sum_add_distrib, div, Finset.mul_sum, clm_expand (fderiv ℝ g x) (a x),
    smul_eq_mul]

lemma fderiv_sub_apply {a b : VelocityField} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x h : T3) : fderiv ℝ (a - b) x h = fderiv ℝ a x h - fderiv ℝ b x h := by
  rw [fderiv_sub (ha x) (hb x)]; rfl

lemma div_sub {a b : VelocityField} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (x : T3) :
    div (a - b) x = div a x - div b x := by
  simp only [div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [fderiv_comp_apply ha, fderiv_comp_apply hb,
    fderiv_comp_apply (ha.sub hb), fderiv_sub_apply ha hb, PiLp.sub_apply]

lemma laplacian_sub {a b : VelocityField} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (x : T3) :
    laplacian (a - b) x = laplacian a x - laplacian b x := by
  have da := ha.differentiable (by norm_num)
  have db := hb.differentiable (by norm_num)
  have dd : ∀ (c : VelocityField), ContDiff ℝ 2 c → ∀ k : Fin 3,
      Differentiable ℝ fun y => fderiv ℝ c y (e k) := fun c hc k =>
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  simp only [laplacian, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun y => fderiv ℝ (a - b) y (e k)) =
      (fun y => fderiv ℝ a y (e k)) - fun y => fderiv ℝ b y (e k) := by
    funext y; exact fderiv_sub_apply da db y _
  rw [this, fderiv_sub_apply (dd a ha k) (dd b hb k)]

/-- Convective difference: `(a·∇)a − (b·∇)b = ((a−b)·... )`, i.e.
`Da(a) − Db(b) = D(a−b)(a) + Db(a−b)`. -/
lemma convective_sub {a b : VelocityField} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x : T3) : convective a a x - convective b b x =
      fderiv ℝ (a - b) x (a x) + fderiv ℝ b x ((a - b) x) := by
  simp only [convective, fderiv_sub_apply ha hb, Pi.sub_apply, map_sub]; abel

/-- `2⟨w, Dw(a)⟩ = Σₖ ∂ₖ(|w|² aₖ) − |w|² div a`. -/
theorem two_inner_convective {w a : VelocityField} (hw : Differentiable ℝ w)
    (ha : Differentiable ℝ a) (x : T3) :
    2 * ⟪w x, fderiv ℝ w x (a x)⟫ =
      ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, w y⟫ * a y k) x (e k) - ⟪w x, w x⟫ * div a x := by
  have hg : Differentiable ℝ fun y => ⟪w y, w y⟫ := fun y => (hw y).inner ℝ (hw y)
  rw [sum_fderiv_mul hg ha, fderiv_inner_apply ℝ (hw x) (hw x), real_inner_comm (fderiv ℝ w x (a x))]
  ring

/-- `⟨w, Δw⟩ = Σₖ ∂ₖ⟨w, ∂ₖw⟩ − Σₖ |∂ₖw|²`. -/
theorem inner_laplacian {w : VelocityField} (hw : ContDiff ℝ 2 w) (x : T3) :
    ⟪w x, laplacian w x⟫ =
      ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, fderiv ℝ w y (e k)⟫) x (e k) -
        ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2 := by
  have d := hw.differentiable (by norm_num)
  have dd : ∀ k : Fin 3, Differentiable ℝ fun y => fderiv ℝ w y (e k) := fun k =>
    ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  simp only [laplacian, inner_sum, fderiv_inner_apply ℝ (d x) (dd _ x), Finset.sum_add_distrib,
    real_inner_self_eq_norm_sq]
  ring

/-- `⟨w, ∇π⟩ = Σₖ ∂ₖ(π wₖ) − π div w`. -/
theorem inner_gradient {w : VelocityField} {π : T3 → ℝ} (hw : Differentiable ℝ w)
    (hπ : Differentiable ℝ π) (x : T3) :
    ⟪w x, pressureGradient π x⟫ = ∑ k : Fin 3, fderiv ℝ (fun y => π y * w y k) x (e k) - π x * div w x := by
  rw [sum_fderiv_mul hπ hw, real_inner_comm, pressureGradient, gradient, toDual_symm_apply]
  ring


/-! ### Cell integrals (M1) -/

lemma continuous_divsum {φ : Fin 3 → T3 → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k)) :
    Continuous fun x => ∑ k : Fin 3, fderiv ℝ (φ k) x (e k) :=
  continuous_finset_sum _ fun k _ =>
    ((hφ k).continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma contDiff_coord {f : VelocityField} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (k : Fin 3) :
    ContDiff ℝ n (fun y => f y k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hf

lemma isZ3Periodic_coord {f : VelocityField} (hf : IsZ3Periodic f) (k : Fin 3) :
    IsZ3Periodic (fun y => f y k) := fun j x => by simp only [hf j x]

/-- **M1(b).** For `ℤ³`-periodic `C¹` fields `a, w` with `div a = 0`:
`∫_{[0,1]³} ⟨w, (a·∇)w⟩ = 0`. -/
theorem cellIntegral_inner_convective_eq_zero {a w : VelocityField} (ha : ContDiff ℝ 1 a)
    (hw : ContDiff ℝ 1 w) (hdiv : ∀ x, div a x = 0) (pa : IsZ3Periodic a)
    (pw : IsZ3Periodic w) : cellIntegral (fun x => ⟪w x, convective a w x⟫) = 0 := by
  have da := ha.differentiable one_ne_zero
  have dw := hw.differentiable one_ne_zero
  have h1 : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => ⟪w y, w y⟫ * a y k) := fun k =>
    (hw.inner ℝ hw).mul (contDiff_coord ha k)
  have z : cellIntegral (fun x => ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, w y⟫ * a y k) x (e k)) = 0 :=
    cellIntegral_sum_fderiv_eq_zero h1 fun k j x => by simp [pw j x, pa j x]
  have hpt : ∀ x, ⟪w x, convective a w x⟫ =
      (1 / 2 : ℝ) * ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, w y⟫ * a y k) x (e k) := fun x => by
    have := two_inner_convective dw da x
    rw [hdiv x, mul_zero, sub_zero] at this
    simp only [convective]; linarith
  simp only [hpt]
  rw [cellIntegral_const_mul, z, mul_zero]

/-- **M1(c).** For `ℤ³`-periodic `C¹` `w` with `div w = 0` and `ℤ³`-periodic `C¹` `π`:
`∫_{[0,1]³} ⟨w, ∇π⟩ = 0`. -/
theorem cellIntegral_inner_pressureGradient_eq_zero {w : VelocityField} {π : T3 → ℝ}
    (hw : ContDiff ℝ 1 w) (hπ : ContDiff ℝ 1 π) (hdiv : ∀ x, div w x = 0)
    (pw : IsZ3Periodic w) (pπ : IsZ3Periodic π) :
    cellIntegral (fun x => ⟪w x, pressureGradient π x⟫) = 0 := by
  have dw := hw.differentiable one_ne_zero
  have dπ := hπ.differentiable one_ne_zero
  have h1 : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => π y * w y k) := fun k =>
    hπ.mul (contDiff_coord hw k)
  have z := cellIntegral_sum_fderiv_eq_zero h1 fun k j x => by simp [pπ j x, pw j x]
  have hpt : ∀ x, ⟪w x, pressureGradient π x⟫ =
      ∑ k : Fin 3, fderiv ℝ (fun y => π y * w y k) x (e k) := fun x => by
    rw [inner_gradient dw dπ x, hdiv x, mul_zero, sub_zero]
  simp only [hpt]
  exact z

/-- **M1(d).** For `ℤ³`-periodic `C²` `w`:
`∫_{[0,1]³} ⟨w, Δw⟩ = −∫_{[0,1]³} Σₖ |∂ₖw|²`. -/
theorem cellIntegral_inner_laplacian {w : VelocityField} (hw : ContDiff ℝ 2 w)
    (pw : IsZ3Periodic w) :
    cellIntegral (fun x => ⟪w x, laplacian w x⟫) =
      -cellIntegral (fun x => ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2) := by
  have w1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have dk : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => fderiv ℝ w y (e k)) := fun k =>
    (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h2 : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => ⟪w y, fderiv ℝ w y (e k)⟫) := fun k =>
    w1.inner ℝ (dk k)
  have z := cellIntegral_sum_fderiv_eq_zero h2 fun k j x => by
    rw [pw j x, isZ3Periodic_fderiv pw j x]
  have cN : Continuous fun x => ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2 :=
    continuous_finset_sum _ fun k _ => ((dk k).continuous.norm).pow 2
  simp only [inner_laplacian hw]
  rw [cellIntegral_sub (continuous_divsum h2) cN, z, zero_sub]

/-- **M1(d′).** `∫_{[0,1]³} ⟨w, Δw⟩ ≤ 0` for `ℤ³`-periodic `C²` `w`. -/
theorem cellIntegral_inner_laplacian_nonpos {w : VelocityField} (hw : ContDiff ℝ 2 w)
    (pw : IsZ3Periodic w) : cellIntegral (fun x => ⟪w x, laplacian w x⟫) ≤ 0 := by
  rw [cellIntegral_inner_laplacian hw pw, neg_nonpos]
  have dk : ∀ k : Fin 3, Continuous (fun y => fderiv ℝ w y (e k)) := fun k =>
    ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
  have cN : Continuous fun x => ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2 :=
    continuous_finset_sum _ fun k _ => ((dk k).norm).pow 2
  have := cellIntegral_mono_on continuous_const cN
    (fun a _ b _ c _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
  simpa [cellIntegral_zero] using this

end NSTorus
