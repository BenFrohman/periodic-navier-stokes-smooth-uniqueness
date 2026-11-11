/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness.FieldIdentities
import NSTorusUniqueness.Clamp

/-!
# The difference energy on a closed time interval (Milestone M1, energy part)

For two classical `ℤ³`-periodic solutions `u, v` on `[0, T] × ℝ³` (class
`IsPeriodicSmoothSolutionIcc`), with `w = u − v`,

* `E(t) = ∫_{[0,1]³} |w(t)|²` is differentiable on `[0, T]` with
  `E'(t) = ∫_{[0,1]³} 2⟨w, ∂ₜw⟩` (`hasDerivWithinAt_cellEnergy`), by differentiation under the
  integral sign after extending the integrand past `[0, T]` by tangent lines (`Clamp.lean`);
* `E'(t) ≤ 2C E(t)` when `ν ≥ 0` and `‖∇v(t,·)‖ ≤ C` (`cellEnergy_deriv_le`), because the
  transport, pressure and viscous terms integrate to `0`, `0` and `≤ 0` (M1).
-/

open Set Filter Topology InnerProductSpace NSTorus.Cell NSTorus.Clamp
open scoped RealInnerProductSpace ContDiff

namespace NSTorus

local notation "e" k => EuclideanSpace.single k (1 : ℝ)

section regularity

variable {T : ℝ} {u : TimeDependentVelocity}

/-- The space-time set `[0, T] × ℝ³`. -/
abbrev S (T : ℝ) : Set (ℝ × T3) := Icc (0 : ℝ) T ×ˢ univ

lemma uniqueDiffOn_S (hT : 0 < T) : UniqueDiffOn ℝ (S T) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

/-- Joint space-time derivative on `[0, T] × ℝ³`. -/
noncomputable def D (T : ℝ) (u : TimeDependentVelocity) (q : ℝ × T3) : ℝ × T3 →L[ℝ] T3 :=
  fderivWithin ℝ (fun q : ℝ × T3 => u q.1 q.2) (S T) q

variable (hu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
include hu

lemma continuousOn_D (hT : 0 < T) : ContinuousOn (D T u) (S T) :=
  hu.continuousOn_fderivWithin (uniqueDiffOn_S hT) (by simp)

lemma hasFDerivWithinAt_D {q : ℝ × T3} (hq : q ∈ S T) :
    HasFDerivWithinAt (fun q : ℝ × T3 => u q.1 q.2) (D T u q) (S T) q :=
  ((hu.differentiableOn (by simp)) q hq).hasFDerivWithinAt

lemma contDiff_slice {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (u t) :=
  hu.comp_contDiff (f := fun x : T3 => (t, x)) (contDiff_const.prodMk contDiff_id)
    (fun _ => ⟨ht, trivial⟩)

lemma fderiv_slice {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : T3) :
    fderiv ℝ (u t) x = (D T u (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3) := by
  have h1 : HasFDerivAt (fun y : T3 => (t, y)) (ContinuousLinearMap.inr ℝ ℝ T3) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have := (hasFDerivWithinAt_D hu ⟨ht, trivial⟩).comp x h1.hasFDerivWithinAt
    (s := univ) (fun _ _ => ⟨ht, trivial⟩)
  exact (this.hasFDerivAt Filter.univ_mem).fderiv

lemma hasDerivWithinAt_time {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : T3) :
    HasDerivWithinAt (fun s => u s x) (D T u (t, x) (1, 0)) (Icc (0 : ℝ) T) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : T3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have := (hasFDerivWithinAt_D hu ⟨ht, trivial⟩).comp_hasDerivWithinAt t h1.hasDerivWithinAt
    (fun _ hs => ⟨hs, trivial⟩)
  simpa using this

lemma continuousOn_U : ContinuousOn (fun q : ℝ × T3 => u q.1 q.2) (S T) := hu.continuousOn

end regularity

/-- Classical `ℤ³`-periodic solution on the closed slab `[0, T] × ℝ³`, with the time derivative
written as the `(1, 0)`-component of the joint derivative `D T u`. Auxiliary class: every
`IsPeriodicSmoothSolutionOn ν T₁ u₀ u p` restricts to it on `[0, T]` for `0 < T < T₁`
(`IsPeriodicSmoothSolutionOn.toIcc`). -/
def IsPeriodicSmoothSolutionIcc (ν T : ℝ) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (S T) ∧
  (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3,
    D T u (t, x) (1, 0) + convective (u t) (u t) x + pressureGradient (p t) x =
      ν • laplacian (u t) x ∧ div (u t) x = 0) ∧
  ∀ t ∈ Icc (0 : ℝ) T, IsZ3Periodic (u t) ∧ IsZ3Periodic (p t)

/-- `Ico 0 T` is a neighbourhood of `t ∈ [0, T)` within `[0, ∞)`. -/
lemma Ico_mem_nhdsWithin_Ici' {t T : ℝ} (ht : t < T) : Ico (0 : ℝ) T ∈ 𝓝[Ici 0] t := by
  rw [← Ici_inter_Iio]
  exact inter_mem_nhdsWithin _ (Iio_mem_nhds ht)

/-- The one-sided derivative `derivWithin · (Ici 0)` used by `IsPeriodicSmoothSolutionOn` is the
time component of the joint derivative on `[0, T'] × ℝ³`, for `T' < T`. -/
lemma derivWithin_Ici_eq_D {ν T T' : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hT' : 0 < T')
    (hTT : T' < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T') (x : T3) :
    derivWithin (fun s => u s x) (Ici 0) t = D T' u (t, x) (1, 0) := by
  have sub : S T' ⊆ Ico (0 : ℝ) T ×ˢ univ := fun q hq =>
    ⟨⟨hq.1.1, hq.1.2.trans_lt hTT⟩, trivial⟩
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht.1, ht.2.trans_lt hTT⟩
  have hg : ContDiffOn ℝ ∞ (fun s => u s x) (Ico (0 : ℝ) T) :=
    hu.1.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => ⟨hs, trivial⟩)
  have hd : DifferentiableWithinAt ℝ (fun s => u s x) (Ici 0) t :=
    ((hg.differentiableOn (by simp)) t ht').mono_of_mem_nhdsWithin
      (Ico_mem_nhdsWithin_Ici' ht'.2)
  have h1 := (hd.hasDerivWithinAt.mono (Icc_subset_Ici_self : Icc (0 : ℝ) T' ⊆ Ici 0))
  have h2 := hasDerivWithinAt_time (hu.1.mono sub) ht x
  exact ((uniqueDiffOn_Icc hT') t ht).eq_deriv _ h1 h2

/-- **Restriction.** A solution on `[0, T)` is a solution on `[0, T']` for `0 < T' < T`. -/
theorem IsPeriodicSmoothSolutionOn.toIcc {ν T T' : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hT' : 0 < T') (hTT : T' < T) :
    IsPeriodicSmoothSolutionIcc ν T' u p := by
  have sub : S T' ⊆ Ico (0 : ℝ) T ×ˢ univ := fun q hq =>
    ⟨⟨hq.1.1, hq.1.2.trans_lt hTT⟩, trivial⟩
  refine ⟨hu.1.mono sub, hu.2.1.mono sub, fun t ht x => ?_, fun t ht =>
    hu.2.2.2.2 t ⟨ht.1, ht.2.trans_lt hTT⟩⟩
  rw [← derivWithin_Ici_eq_D hu hT' hTT ht x]
  exact hu.2.2.1 t ⟨ht.1, ht.2.trans_lt hTT⟩ x

lemma torusIntegral_congr {f g : E → ℝ} {t t' : ℝ}
    (h : ∀ a b c, f (t, a, b, c) = g (t', a, b, c)) : torusIntegral f t = torusIntegral g t' := by
  simp only [Cell.torusIntegral, Cell.i2, Cell.i3, h]

section energy

variable {T : ℝ} {u v : TimeDependentVelocity}

/-- `|w|²` with `w = u − v`. -/
noncomputable def Gf (u v : TimeDependentVelocity) (q : ℝ × T3) : ℝ :=
  ⟪u q.1 q.2 - v q.1 q.2, u q.1 q.2 - v q.1 q.2⟫

/-- `2⟨w, ∂ₜw⟩`. -/
noncomputable def Gd (T : ℝ) (u v : TimeDependentVelocity) (q : ℝ × T3) : ℝ :=
  2 * ⟪u q.1 q.2 - v q.1 q.2, D T u q (1, 0) - D T v q (1, 0)⟫

/-- The difference energy, through the tangent-line extension in time. -/
noncomputable def energy (T : ℝ) (u v : TimeDependentVelocity) (t : ℝ) : ℝ :=
  torusIntegral (fun q => tangentExt T (fun s => Gf u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2))
    (fun s => Gd T u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2)) q.1) t

/-- Its derivative. -/
noncomputable def energy' (T : ℝ) (u v : TimeDependentVelocity) (t : ℝ) : ℝ :=
  torusIntegral (fun q => Gd T u v (cl T q.1, toT3 q.2.1 q.2.2.1 q.2.2.2)) t

variable (hT : 0 < T) (hu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
  (hv : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => v q.1 q.2) (S T))
include hT hu hv

omit hT in
lemma continuousOn_Gf : ContinuousOn (Gf u v) (S T) := by
  have := (continuousOn_U hu).sub (continuousOn_U hv)
  exact this.inner this

lemma continuousOn_Gd : ContinuousOn (Gd T u v) (S T) := by
  have h1 := (continuousOn_U hu).sub (continuousOn_U hv)
  have c : ContinuousOn (fun _ : ℝ × T3 => ((1 : ℝ), (0 : T3))) (S T) := continuousOn_const
  have h2 := ((continuousOn_D hu hT).clm_apply c).sub ((continuousOn_D hv hT).clm_apply c)
  exact continuousOn_const.mul (h1.inner h2)

omit hu hv in
lemma continuous_clamped {G : ℝ × T3 → ℝ} (hG : ContinuousOn G (S T)) :
    Continuous fun q : E => G (cl T q.1, toT3 q.2.1 q.2.2.1 q.2.2.2) :=
  hG.comp_continuous (((continuous_cl T).comp continuous_fst).prodMk continuous_toT3)
    fun _ => ⟨cl_mem hT.le _, trivial⟩

omit hT in
lemma hasDerivWithinAt_Gf {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : T3) :
    HasDerivWithinAt (fun r => Gf u v (r, x)) (Gd T u v (s, x)) (Icc (0 : ℝ) T) s := by
  have hw := (hasDerivWithinAt_time hu hs x).sub (hasDerivWithinAt_time hv hs x)
  have := hw.inner ℝ hw
  unfold Gf Gd
  convert this using 1
  simp only [Pi.sub_apply]; rw [real_inner_comm (u s x - v s x)]; ring

theorem hasDerivAt_energy (t : ℝ) : HasDerivAt (energy T u v) (energy' T u v t) t := by
  have h1 := continuous_clamped hT (continuousOn_Gf hu hv)
  have h2 := continuous_clamped hT (continuousOn_Gd hT hu hv)
  have hf : Continuous fun q : E =>
      tangentExt T (fun s => Gf u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2))
        (fun s => Gd T u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2)) q.1 := by
    unfold tangentExt
    exact h1.add ((continuous_fst.sub ((continuous_cl T).comp continuous_fst)).mul h2)
  have hd : ∀ t a b c, HasDerivAt
      (fun s => tangentExt T (fun s => Gf u v (s, toT3 a b c))
        (fun s => Gd T u v (s, toT3 a b c)) s)
      (Gd T u v (cl T t, toT3 a b c)) t := fun t a b c =>
    hasDerivAt_ext hT (fun s hs => hasDerivWithinAt_Gf hu hv hs _) t
  unfold energy energy'
  exact hasDerivAt_torusIntegral hf h2 hd t

omit hT hu hv in
lemma energy_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    energy T u v t = cellIntegral fun x => Gf u v (t, x) :=
  torusIntegral_congr fun a b c => by simp [tangentExt, cl_of_mem ht, lift]

omit hT hu hv in
lemma energy'_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    energy' T u v t = cellIntegral fun x => Gd T u v (t, x) :=
  torusIntegral_congr fun a b c => by simp [cl_of_mem ht, lift]

/-- **M1(e). Differentiation of the cell energy.** For `u, v` jointly `C^∞` on `[0, T] × ℝ³`,
`E(t) = ∫_{[0,1]³} |u(t) − v(t)|²` has derivative `∫_{[0,1]³} 2⟨u − v, ∂ₜu − ∂ₜv⟩` within
`[0, T]` at every `t ∈ [0, T]`. -/
theorem hasDerivWithinAt_cellEnergy {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => cellIntegral fun x => ‖u s x - v s x‖ ^ 2)
      (cellIntegral fun x => 2 * ⟪u t x - v t x, D T u (t, x) (1, 0) - D T v (t, x) (1, 0)⟫)
      (Icc (0 : ℝ) T) t := by
  have := (hasDerivAt_energy hT hu hv t).hasDerivWithinAt (s := Icc (0 : ℝ) T)
  rw [energy'_eq ht] at this
  refine this.congr (fun s hs => ?_) ?_
  · rw [energy_eq hs]; simp [Gf]
  · rw [energy_eq ht]; simp [Gf]

end energy

/-! ### The energy inequality -/

lemma continuous_laplacian {w : VelocityField} (hw : ContDiff ℝ 2 w) : Continuous (laplacian w) := by
  unfold laplacian
  refine continuous_finset_sum _ fun k _ => ?_
  have : ContDiff ℝ 1 (fun y => fderiv ℝ w y (e k)) :=
    (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (this.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma continuous_pressureGradient {π : T3 → ℝ} (hπ : ContDiff ℝ 1 π) :
    Continuous (pressureGradient π) :=
  (InnerProductSpace.toDual ℝ T3).symm.continuous.comp (hπ.continuous_fderiv one_ne_zero)

lemma cellIntegral_comb (α : ℝ) {f₁ f₂ f₃ f₄ f₅ : T3 → ℝ} (c₁ : Continuous f₁)
    (c₂ : Continuous f₂) (c₃ : Continuous f₃) (c₄ : Continuous f₄) (c₅ : Continuous f₅) :
    cellIntegral (fun x => α * f₁ x - 2 * f₂ x + 2 * f₃ x - 2 * f₄ x - 2 * f₅ x) =
      α * cellIntegral f₁ - 2 * cellIntegral f₂ + 2 * cellIntegral f₃ - 2 * cellIntegral f₄ -
        2 * cellIntegral f₅ := by
  rw [cellIntegral_sub (by fun_prop) (by fun_prop), cellIntegral_sub (by fun_prop) (by fun_prop),
    cellIntegral_add (by fun_prop) (by fun_prop), cellIntegral_sub (by fun_prop) (by fun_prop),
    cellIntegral_const_mul, cellIntegral_const_mul, cellIntegral_const_mul,
    cellIntegral_const_mul, cellIntegral_const_mul]

section ineq

variable {ν T : ℝ} {u v : TimeDependentVelocity} {p q : TimeDependentPressure}

lemma contDiff_slice_p (hp : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (S T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (p t) :=
  hp.comp_contDiff (f := fun x : T3 => (t, x)) (contDiff_const.prodMk contDiff_id)
    (fun _ => ⟨ht, trivial⟩)

/-- **The energy inequality** `E'(t) ≤ 2C E(t)`, for `ν ≥ 0` and `‖∇v(t, ·)‖ ≤ C`, where
`E'(t) = ∫_{[0,1]³} 2⟨w, ∂ₜw⟩` and `E(t) = ∫_{[0,1]³} |w|²`, `w = u − v`. -/
theorem cellEnergy_deriv_le (hν : 0 ≤ ν) (hu : IsPeriodicSmoothSolutionIcc ν T u p)
    (hv : IsPeriodicSmoothSolutionIcc ν T v q) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ (v t) x‖ ≤ C) :
    cellIntegral (fun x => Gd T u v (t, x)) ≤ 2 * C * cellIntegral (fun x => Gf u v (t, x)) := by
  obtain ⟨cu, cp, pdeu, peru⟩ := hu
  obtain ⟨cv, cq, pdev, perv⟩ := hv
  set a := u t with ha_def
  set b := v t with hb_def
  set w : VelocityField := a - b with hw_def
  have sa := contDiff_slice cu ht; have sb := contDiff_slice cv ht
  have sw : ContDiff ℝ ∞ w := sa.sub sb
  have da := sa.differentiable (by simp); have db := sb.differentiable (by simp)
  have dw := sw.differentiable (by simp)
  have sp := contDiff_slice_p cp ht; have sq := contDiff_slice_p cq ht
  have pa : IsZ3Periodic a := (peru t ht).1
  have pb : IsZ3Periodic b := (perv t ht).1
  have pw : IsZ3Periodic w := fun k x => by simp [hw_def, pa k x, pb k x]
  have hdiva : ∀ x, div a x = 0 := fun x => (pdeu t ht x).2
  have hdivw : ∀ x, div w x = 0 := fun x => by
    rw [hw_def, div_sub da db, hdiva x, (pdev t ht x).2, sub_zero]
  -- pointwise expansion of `Gd`
  have hpt : ∀ x, Gd T u v (t, x) =
      2 * ν * ⟪w x, laplacian w x⟫ - 2 * ⟪w x, pressureGradient (p t) x⟫ +
        2 * ⟪w x, pressureGradient (q t) x⟫ - 2 * ⟪w x, convective a w x⟫ -
        2 * ⟪w x, fderiv ℝ b x (w x)⟫ := fun x => by
    have pu : D T u (t, x) (1, 0) =
        ν • laplacian a x - pressureGradient (p t) x - convective a a x := by
      rw [← (pdeu t ht x).1]; abel
    have pv : D T v (t, x) (1, 0) =
        ν • laplacian b x - pressureGradient (q t) x - convective b b x := by
      rw [← (pdev t ht x).1]; abel
    have hl := laplacian_sub (sa.of_le ENat.LEInfty.out)
      (sb.of_le ENat.LEInfty.out) x
    have hc := convective_sub da db x
    unfold Gd
    simp only
    rw [pu, pv]
    have : ν • laplacian a x - pressureGradient (p t) x - convective a a x -
        (ν • laplacian b x - pressureGradient (q t) x - convective b b x) =
        ν • laplacian w x - pressureGradient (p t) x + pressureGradient (q t) x -
          (fderiv ℝ w x (a x) + fderiv ℝ b x (w x)) := by
      rw [hw_def, hl, ← hc, smul_sub]; abel
    rw [this]
    simp only [inner_sub_right, inner_add_right, inner_smul_right, convective, hw_def,
      Pi.sub_apply]
    ring
  -- continuity of the five terms
  have w1 : ContDiff ℝ 1 w := sw.of_le ENat.LEInfty.out
  have w2 : ContDiff ℝ 2 w := sw.of_le ENat.LEInfty.out
  have cw := w1.continuous
  have c1 : Continuous fun x => ⟪w x, laplacian w x⟫ := cw.inner (continuous_laplacian w2)
  have c2 : Continuous fun x => ⟪w x, pressureGradient (p t) x⟫ :=
    cw.inner (continuous_pressureGradient (sp.of_le ENat.LEInfty.out))
  have c3 : Continuous fun x => ⟪w x, pressureGradient (q t) x⟫ :=
    cw.inner (continuous_pressureGradient (sq.of_le ENat.LEInfty.out))
  have c4 : Continuous fun x => ⟪w x, convective a w x⟫ :=
    cw.inner ((w1.continuous_fderiv one_ne_zero).clm_apply sa.continuous)
  have c5 : Continuous fun x => ⟪w x, fderiv ℝ b x (w x)⟫ :=
    cw.inner (((sb.of_le ENat.LEInfty.out : ContDiff ℝ 1 b).continuous_fderiv
      one_ne_zero).clm_apply cw)
  have cG : Continuous fun x => ⟪w x, w x⟫ := cw.inner cw
  -- the cell integrals (M1)
  have I1 : cellIntegral (fun x => ⟪w x, laplacian w x⟫) ≤ 0 :=
    cellIntegral_inner_laplacian_nonpos w2 pw
  have I2 : cellIntegral (fun x => ⟪w x, pressureGradient (p t) x⟫) = 0 :=
    cellIntegral_inner_pressureGradient_eq_zero w1 (sp.of_le ENat.LEInfty.out)
      hdivw pw (peru t ht).2
  have I3 : cellIntegral (fun x => ⟪w x, pressureGradient (q t) x⟫) = 0 :=
    cellIntegral_inner_pressureGradient_eq_zero w1 (sq.of_le ENat.LEInfty.out)
      hdivw pw (perv t ht).2
  have I4 : cellIntegral (fun x => ⟪w x, convective a w x⟫) = 0 :=
    cellIntegral_inner_convective_eq_zero (sa.of_le ENat.LEInfty.out) w1 hdiva pa pw
  have I5 : -cellIntegral (fun x => ⟪w x, fderiv ℝ b x (w x)⟫) ≤
      C * cellIntegral (fun x => ⟪w x, w x⟫) := by
    have hpt5 : ∀ x, -⟪w x, fderiv ℝ b x (w x)⟫ ≤ C * ⟪w x, w x⟫ := fun x => by
      rw [real_inner_self_eq_norm_sq]
      have h1 := abs_real_inner_le_norm (w x) (fderiv ℝ b x (w x))
      have h2 := (fderiv ℝ b x).le_opNorm (w x)
      have h3 : ‖w x‖ * ‖fderiv ℝ b x (w x)‖ ≤ ‖w x‖ * (C * ‖w x‖) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right (hC x)
          (norm_nonneg _))) (norm_nonneg _)
      nlinarith [neg_abs_le ⟪w x, fderiv ℝ b x (w x)⟫]
    have := cellIntegral_mono_on (g := fun x => -⟪w x, fderiv ℝ b x (w x)⟫)
      (h := fun x => C * ⟪w x, w x⟫) c5.neg (continuous_const.mul cG)
      (fun a _ b _ c _ => hpt5 _)
    rw [cellIntegral_const_mul] at this
    have hneg : cellIntegral (fun x => -⟪w x, fderiv ℝ b x (w x)⟫) =
        -cellIntegral (fun x => ⟪w x, fderiv ℝ b x (w x)⟫) := by
      have := cellIntegral_const_mul (-1) (fun x => ⟪w x, fderiv ℝ b x (w x)⟫)
      simpa using this
    linarith
  have hGf : (fun x => Gf u v (t, x)) = fun x => ⟪w x, w x⟫ := rfl
  rw [hGf]
  simp only [hpt]
  rw [cellIntegral_comb (2 * ν) c1 c2 c3 c4 c5, I2, I3, I4]
  nlinarith [mul_nonneg hν (neg_nonneg.2 I1)]

end ineq

end NSTorus
