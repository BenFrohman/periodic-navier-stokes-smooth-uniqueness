/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Iterated integrals over the unit cell and differentiation under the integral sign

Points are `(t, a, b, c) : ℝ × ℝ × ℝ × ℝ`, and
`torusIntegral f t = ∫₀¹∫₀¹∫₀¹ f(t,a,b,c) dc db da`.

Proved here: differentiation under the integral sign for jointly continuous integrands with
jointly continuous time derivative (`hasDerivAt_torusIntegral`, via Mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), and the periodic
fundamental theorem of calculus in each coordinate (`torusIntegral_deriv_a/b/c`).

Provenance: ported unchanged from the author's `BenFrohman/weighted-enstrophy-identities`
(`WeightedEnstrophy/TorusCalculus.lean`, commit `1df4652`), namespace renamed.
-/

open MeasureTheory Set Filter Topology

namespace NSTorus.Cell


/-- Differentiation under the integral sign on `[0,1]` for a jointly continuous integrand
with jointly continuous parameter derivative. -/
theorem hasDerivAt_integral01 (F F' : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ s x, HasDerivAt (fun s => F s x) (F' s x) s) (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ x in (0:ℝ)..1, F s x) (∫ x in (0:ℝ)..1, F' s₀ x) s₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod (isCompact_Icc (a := (0:ℝ)) (b := 1))
    ).exists_bound_of_continuousOn hF'.continuousOn
  have cF : ∀ s, Continuous (F s) := fun s => hF.comp (continuous_const.prodMk continuous_id)
  have cF' : ∀ s, Continuous (F' s) := fun s => hF'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => C) (Metric.closedBall_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (cF s).aestronglyMeasurable)
    ((cF s₀).intervalIntegrable 0 1) (cF' s₀).aestronglyMeasurable ?_
    intervalIntegrable_const (Eventually.of_forall fun x _ s _ => hd s x)).2
  refine Eventually.of_forall fun x hx s hs => hC (s, x) ⟨hs, ?_⟩
  rw [uIoc_of_le zero_le_one] at hx
  exact Ioc_subset_Icc_self hx

/-- Periodic fundamental theorem: `∫₀¹ g' = 0` when `g(1) = g(0)`. -/
theorem integral01_deriv_periodic (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') (hp : g 1 = g 0) : ∫ x in (0:ℝ)..1, g' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
    (hg'.intervalIntegrable 0 1), hp, sub_self]

abbrev E := ℝ × ℝ × ℝ × ℝ

/-- Innermost integral `∫₀¹ f(t,a,b,c) dc`. -/
noncomputable def i3 (f : E → ℝ) (q : ℝ × ℝ × ℝ) : ℝ := ∫ c in (0:ℝ)..1, f (q.1, q.2.1, q.2.2, c)
/-- `∫₀¹∫₀¹ f(t,a,b,c) dc db`. -/
noncomputable def i2 (f : E → ℝ) (q : ℝ × ℝ) : ℝ := ∫ b in (0:ℝ)..1, i3 f (q.1, q.2, b)
/-- `∫_{T³} f(t,·) = ∫₀¹∫₀¹∫₀¹ f(t,a,b,c) dc db da`. -/
noncomputable def torusIntegral (f : E → ℝ) (t : ℝ) : ℝ := ∫ a in (0:ℝ)..1, i2 f (t, a)

lemma cont_i3 {f : E → ℝ} (hf : Continuous f) : Continuous (i3 f) := by
  unfold i3
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : ℝ × ℝ × ℝ) (c : ℝ) => f (q.1, q.2.1, q.2.2, c)) (by fun_prop) 0 1

lemma cont_i2 {f : E → ℝ} (hf : Continuous f) : Continuous (i2 f) := by
  unfold i2
  have := cont_i3 hf
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : ℝ × ℝ) (b : ℝ) => i3 f (q.1, q.2, b)) (by fun_prop) 0 1

lemma cont_torusIntegral {f : E → ℝ} (hf : Continuous f) : Continuous (torusIntegral f) := by
  unfold torusIntegral
  have := cont_i2 hf
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (t : ℝ) (a : ℝ) => i2 f (t, a)) (by fun_prop) 0 1

lemma i3_add {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (q) :
    i3 (f + g) q = i3 f q + i3 g q := by
  unfold i3; simp only [Pi.add_apply]
  exact intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)

lemma i2_add {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (q) :
    i2 (f + g) q = i2 f q + i2 g q := by
  unfold i2; simp only [i3_add hf hg]
  have := cont_i3 hf; have := cont_i3 hg
  exact intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)

lemma torusIntegral_add {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (t) :
    torusIntegral (f + g) t = torusIntegral f t + torusIntegral g t := by
  unfold torusIntegral; simp only [i2_add hf hg]
  have := cont_i2 hf; have := cont_i2 hg
  exact intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)

lemma torusIntegral_smul (r : ℝ) (f : E → ℝ) (t) :
    torusIntegral (r • f) t = r * torusIntegral f t := by
  simp [torusIntegral, i2, i3, intervalIntegral.integral_const_mul]

/-- **Differentiation under the integral sign on `T³`**:
`d/dt ∫_{T³} f(t,x) dx = ∫_{T³} ∂ₜf(t,x) dx` for `f`, `∂ₜf` jointly continuous. -/
theorem hasDerivAt_torusIntegral {f f' : E → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t a b c, HasDerivAt (fun s => f (s, a, b, c)) (f' (t, a, b, c)) t) (t : ℝ) :
    HasDerivAt (torusIntegral f) (torusIntegral f' t) t := by
  have c3 := cont_i3 hf; have c3' := cont_i3 hf'
  have c2 := cont_i2 hf; have c2' := cont_i2 hf'
  have h3 : ∀ a b t, HasDerivAt (fun s => i3 f (s, a, b)) (i3 f' (t, a, b)) t := fun a b t =>
    hasDerivAt_integral01 (fun s c => f (s, a, b, c)) (fun s c => f' (s, a, b, c))
      (by fun_prop) (by fun_prop) (fun s c => hd s a b c) t
  have h2 : ∀ a t, HasDerivAt (fun s => i2 f (s, a)) (i2 f' (t, a)) t := fun a t =>
    hasDerivAt_integral01 (fun s b => i3 f (s, a, b)) (fun s b => i3 f' (s, a, b))
      (by fun_prop) (by fun_prop) (fun s b => h3 a b s) t
  exact hasDerivAt_integral01 (fun s a => i2 f (s, a)) (fun s a => i2 f' (s, a))
      (by fun_prop) (by fun_prop) (fun s a => h2 a s) t

/-- **Torus divergence lemma, direction `c`**: `∫_{T³} ∂_c f = 0` for `f` 1-periodic in `c`. -/
theorem torusIntegral_deriv_c {f f' : E → ℝ} (hf' : Continuous f')
    (hd : ∀ t a b c, HasDerivAt (fun x => f (t, a, b, x)) (f' (t, a, b, c)) c)
    (hp : ∀ t a b c, f (t, a, b, c + 1) = f (t, a, b, c)) (t : ℝ) : torusIntegral f' t = 0 := by
  have h3 : ∀ q, i3 f' q = 0 := fun q => integral01_deriv_periodic _ _
    (fun c => hd q.1 q.2.1 q.2.2 c) (by fun_prop) (by simpa using hp q.1 q.2.1 q.2.2 0)
  simp [torusIntegral, i2, h3]

/-- **Torus divergence lemma, direction `b`**. -/
theorem torusIntegral_deriv_b {f f' : E → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t a b c, HasDerivAt (fun x => f (t, a, x, c)) (f' (t, a, b, c)) b)
    (hp : ∀ t a b c, f (t, a, b + 1, c) = f (t, a, b, c)) (t : ℝ) : torusIntegral f' t = 0 := by
  have c3 := cont_i3 hf; have c3' := cont_i3 hf'
  have h2 : ∀ q, i2 f' q = 0 := fun q => integral01_deriv_periodic
    (fun b => i3 f (q.1, q.2, b)) (fun b => i3 f' (q.1, q.2, b))
    (fun b => hasDerivAt_integral01 (fun x c => f (q.1, q.2, x, c))
      (fun x c => f' (q.1, q.2, x, c)) (by fun_prop) (by fun_prop)
      (fun x c => hd q.1 q.2 x c) b) (by fun_prop)
    (by simp only [i3]; congr 1; ext c; simpa using hp q.1 q.2 0 c)
  simp [torusIntegral, h2]

/-- **Torus divergence lemma, direction `a`**. -/
theorem torusIntegral_deriv_a {f f' : E → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t a b c, HasDerivAt (fun x => f (t, x, b, c)) (f' (t, a, b, c)) a)
    (hp : ∀ t a b c, f (t, a + 1, b, c) = f (t, a, b, c)) (t : ℝ) : torusIntegral f' t = 0 := by
  have c3 := cont_i3 hf; have c3' := cont_i3 hf'
  have c2' := cont_i2 hf'
  have h3 : ∀ b a, HasDerivAt (fun x => i3 f (t, x, b)) (i3 f' (t, a, b)) a := fun b a =>
    hasDerivAt_integral01 (fun x c => f (t, x, b, c)) (fun x c => f' (t, x, b, c))
      (by fun_prop) (by fun_prop) (fun x c => hd t x b c) a
  have h2 : ∀ a, HasDerivAt (fun x => i2 f (t, x)) (i2 f' (t, a)) a := fun a =>
    hasDerivAt_integral01 (fun x b => i3 f (t, x, b)) (fun x b => i3 f' (t, x, b))
      (by fun_prop) (by fun_prop) (fun x b => h3 b x) a
  exact integral01_deriv_periodic (fun x => i2 f (t, x)) (fun x => i2 f' (t, x)) h2
    (by fun_prop) (by simp only [i2, i3]; congr 1; ext b; congr 1; ext c
                      simpa using hp t 0 b c)

end NSTorus.Cell
