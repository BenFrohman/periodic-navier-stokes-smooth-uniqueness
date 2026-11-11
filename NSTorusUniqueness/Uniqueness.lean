/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness.Energy
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniqueness of classical periodic Navier–Stokes solutions (Milestone M2)

**Theorem** (`IsPeriodicSmoothSolutionOn.eq_of_same_data`). Let `ν ≥ 0`. If `(u, p)` and
`(v, q)` are classical `ℤ³`-periodic solutions of the incompressible Navier–Stokes equations on
`[0, T) × ℝ³` in the sense of `IsPeriodicSmoothSolutionOn ν T u₀` (the class used in
`frohmanian-tether-sdiff`), with the same initial velocity `u₀`, then `u t = v t` for every
`t ∈ [0, T)`; moreover `∇p(t) = ∇q(t)`, so `p(t) − q(t)` is constant in space.

Proof: the classical energy method. For `T' < T` put `w = u − v` and
`E(t) = ∫_{[0,1]³} |w(t)|²`. Then `E(0) = 0` and `E' ≤ 2C E` on `[0, T']` with
`C = sup_{[0,T']×ℝ³} ‖∇v‖ < ∞` (`cellEnergy_deriv_le`), so Grönwall's inequality (Mathlib
`le_gronwallBound_of_liminf_deriv_right_le`) gives `E ≡ 0`, and continuity plus periodicity give
`w ≡ 0`.

Classical references: J. Serrin, *The initial value problem for the Navier–Stokes equations*
(1963); R. Temam, *Navier–Stokes Equations and Nonlinear Functional Analysis*, 2nd ed., SIAM
(1995); P. Constantin and C. Foias, *Navier–Stokes Equations*, Univ. Chicago Press (1988);
J. C. Robinson, J. L. Rodrigo and W. Sadowski, *The Three-Dimensional Navier–Stokes Equations*,
Cambridge Univ. Press (2016).
-/

open Set Filter Topology InnerProductSpace NSTorus.Cell NSTorus.Clamp
open scoped RealInnerProductSpace ContDiff

namespace NSTorus

/-- **Grönwall step.** A continuous `E` on `[0, T]` with right derivative `E' ≤ L E` on `[0, T)`
and `E 0 ≤ 0` satisfies `E ≤ 0` on `[0, T]` (Mathlib `le_gronwallBound_of_liminf_deriv_right_le`
with `δ = ε = 0`). -/
theorem le_zero_of_deriv_le_mul {E E' : ℝ → ℝ} {L T : ℝ}
    (hc : ContinuousOn E (Icc 0 T))
    (hd : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hb : ∀ t ∈ Ico (0 : ℝ) T, E' t ≤ L * E t) (h0 : E 0 ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) T, E t ≤ 0 := by
  intro t ht
  have := le_gronwallBound_of_liminf_deriv_right_le (ε := 0) (K := L) hc
    (fun x hx _r hr => (hd x hx).liminf_right_slope_le hr) h0
    (fun x hx => by simpa using hb x hx) t ht
  simpa [gronwallBound_ε0_δ0] using this

/-- A uniform bound for `‖∇v‖` on `[0, T] × ℝ³` (compactness of `[0, T] × [0,1]³` plus
periodicity). -/
theorem exists_bound_fderiv {T : ℝ} {v : TimeDependentVelocity} (hT : 0 < T)
    (cv : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => v q.1 q.2) (S T))
    (perv : ∀ t ∈ Icc (0 : ℝ) T, IsZ3Periodic (v t)) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖fderiv ℝ (v t) x‖ ≤ C := by
  set K : Set (ℝ × T3) := Icc (0 : ℝ) T ×ˢ ((fun r : ℝ × ℝ × ℝ => toT3 r.1 r.2.1 r.2.2) ''
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image continuous_toT3')
  have hKS : K ⊆ S T := fun z hz => ⟨hz.1, trivial⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_D cv hT).mono hKS)
  refine ⟨C, fun t ht x => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, k, rfl⟩ := exists_cell x
  rw [isZ3Periodic_fderiv (perv t ht) k, fderiv_slice cv ht]
  refine ((D T v _).opNorm_comp_le _).trans ?_
  have h1 := hC (t, toT3 a b c) ⟨ht, ⟨(a, b, c), ⟨ha, hb, hc⟩, rfl⟩⟩
  have h2 : ‖ContinuousLinearMap.inr ℝ ℝ T3‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ T3
  nlinarith [norm_nonneg (D T v (t, toT3 a b c))]

/-- **Uniqueness on a closed slab.** Two classical periodic solutions on `[0, T] × ℝ³` (`ν ≥ 0`)
with the same initial velocity have the same velocity on `[0, T]`. -/
theorem IsPeriodicSmoothSolutionIcc.eq_of_eq_zero {ν T : ℝ} {u v : TimeDependentVelocity}
    {p q : TimeDependentPressure} (hν : 0 ≤ ν) (hT : 0 < T)
    (hu : IsPeriodicSmoothSolutionIcc ν T u p) (hv : IsPeriodicSmoothSolutionIcc ν T v q)
    (h0 : u 0 = v 0) : ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  have cu := hu.1; have cv := hv.1
  obtain ⟨C, hC⟩ := exists_bound_fderiv hT cv fun t ht => (hv.2.2.2 t ht).1
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hE := le_zero_of_deriv_le_mul (E := energy T u v) (E' := energy' T u v) (L := 2 * C)
    (continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_energy hT cu cv t).continuousAt).continuousOn
    (fun t _ => (hasDerivAt_energy hT cu cv t).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
      rw [energy'_eq ht', energy_eq ht']
      exact cellEnergy_deriv_le hν hu hv ht' (hC t ht'))
    (by rw [energy_eq h0mem]; simp [Gf, h0, cellIntegral_zero])
  intro t ht
  have hle := hE t ht
  rw [energy_eq ht] at hle
  have cG : Continuous fun x => Gf u v (t, x) :=
    (continuousOn_Gf cu cv).comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨ht, trivial⟩
  have pw : IsZ3Periodic fun x => Gf u v (t, x) := fun k x => by
    simp only [Gf, (hu.2.2.2 t ht).1 k x, (hv.2.2.2 t ht).1 k x]
  have hz := eq_zero_of_cellIntegral_nonpos cG pw (fun x => real_inner_self_nonneg) hle
  funext x
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (hz x))

/-- **Uniqueness of classical periodic Navier–Stokes solutions (velocity).** For `ν ≥ 0`, two
solutions of class `IsPeriodicSmoothSolutionOn ν T u₀` with the same initial velocity `u₀`
coincide on `[0, T)`. -/
theorem IsPeriodicSmoothSolutionOn.eq_of_same_data {ν T : ℝ} {u₀ : VelocityField}
    {u v : TimeDependentVelocity} {p q : TimeDependentPressure} (hν : 0 ≤ ν)
    (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p) (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Ico (0 : ℝ) T, u t = v t := by
  intro t ht
  have hT : 0 < T := ht.1.trans_lt ht.2
  set T' := (t + T) / 2
  have hT' : 0 < T' := by simp only [T']; linarith [ht.1]
  have hTT : T' < T := by simp only [T']; linarith [ht.2]
  have htT : t ≤ T' := by simp only [T']; linarith [ht.2]
  exact (hu.toIcc hT' hTT).eq_of_eq_zero hν hT' (hv.toIcc hT' hTT)
    (hu.2.2.2.1.trans hv.2.2.2.1.symm) t ⟨ht.1, htT⟩

/-- **Uniqueness of the pressure gradient.** Under the same hypotheses,
`∇p(t, x) = ∇q(t, x)` for all `t ∈ [0, T)` and `x`. -/
theorem IsPeriodicSmoothSolutionOn.pressureGradient_eq_of_same_data {ν T : ℝ}
    {u₀ : VelocityField} {u v : TimeDependentVelocity} {p q : TimeDependentPressure}
    (hν : 0 ≤ ν) (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p)
    (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x, pressureGradient (p t) x = pressureGradient (q t) x := by
  intro t ht x
  have huv := hu.eq_of_same_data hν hv
  have hd : derivWithin (fun s => u s x) (Ici 0) t = derivWithin (fun s => v s x) (Ici 0) t :=
    Filter.EventuallyEq.derivWithin_eq
      (mem_of_superset (Ico_mem_nhdsWithin_Ici' ht.2) fun s hs => by simp [huv s hs])
      (by simp [huv t ht])
  have e1 := (hu.2.2.1 t ht x).1
  have e2 := (hv.2.2.1 t ht x).1
  rw [hd, huv t ht] at e1
  exact add_left_cancel (e1.trans e2.symm)

/-- **Uniqueness of the pressure up to a function of time.** Under the same hypotheses, for each
`t ∈ [0, T)` the difference `p(t) − q(t)` is constant on `ℝ³`. -/
theorem IsPeriodicSmoothSolutionOn.pressure_sub_const_of_same_data {ν T : ℝ}
    {u₀ : VelocityField} {u v : TimeDependentVelocity} {p q : TimeDependentPressure}
    (hν : 0 ≤ ν) (hu : IsPeriodicSmoothSolutionOn ν T u₀ u p)
    (hv : IsPeriodicSmoothSolutionOn ν T u₀ v q) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x y, p t x - q t x = p t y - q t y := by
  intro t ht
  have slice : ∀ {r : TimeDependentPressure},
      ContDiffOn ℝ ∞ (fun z : ℝ × T3 => r z.1 z.2) (Ico (0 : ℝ) T ×ˢ univ) →
        Differentiable ℝ (r t) := fun hr =>
    (hr.comp_contDiff (f := fun x : T3 => (t, x)) (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨ht, trivial⟩)).differentiable (by simp)
  have dp := slice hu.2.1; have dq := slice hv.2.1
  have hg := hu.pressureGradient_eq_of_same_data hν hv t ht
  have hf : ∀ x, fderiv ℝ (fun y => p t y - q t y) x = 0 := fun x => by
    have h1 : fderiv ℝ (p t) x = fderiv ℝ (q t) x :=
      (InnerProductSpace.toDual ℝ T3).symm.injective (hg x)
    rw [fderiv_fun_sub (dp x) (dq x), h1, sub_self]
  exact fun x y => is_const_of_fderiv_eq_zero (dp.sub dq) hf x y

end NSTorus
