/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import NSTorusUniqueness.CellIntegral

/-!
# The iterated cell integral is the Lebesgue integral over the unit cube

`cellIntegral_eq_setIntegral_unitCube`: for continuous `g : ℝ³ → ℝ`,
`cellIntegral g = ∫ x in unitCube, g x` (Mathlib Bochner integral against Lebesgue measure
`volume` on `EuclideanSpace ℝ (Fin 3)`), via Mathlib's measure-preserving equivalences
`EuclideanSpace ℝ (Fin 3) ≃ᵐ (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ × ℝ` and Fubini
(`MeasureTheory.setIntegral_prod`).
-/

open MeasureTheory Set NSTorus.Cell

namespace NSTorus

/-- Coordinates `ℝ³ ≃ᵐ ℝ × ℝ × ℝ`, `x ↦ (x 0, x 1, x 2)`. -/
noncomputable def coordEquiv : T3 ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow))

lemma coordEquiv_apply (x : T3) : coordEquiv x = (x 0, x 1, x 2) := rfl

lemma measurePreserving_coordEquiv : MeasurePreserving coordEquiv volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)))

lemma toT3_coord (x : T3) : toT3 (x 0) (x 1) (x 2) = x := by
  ext i; fin_cases i <;> rfl

lemma integral01_eq_setIntegral (φ : ℝ → ℝ) :
    ∫ x in (0:ℝ)..1, φ x = ∫ x in Icc (0:ℝ) 1, φ x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- **Bridge to Mathlib's Lebesgue integral.** For continuous `g`,
`cellIntegral g = ∫ x in unitCube, g x`. -/
theorem cellIntegral_eq_setIntegral_unitCube {g : T3 → ℝ} (hg : Continuous g) :
    cellIntegral g = ∫ x in unitCube, g x := by
  set h : ℝ × ℝ × ℝ → ℝ := fun r => g (toT3 r.1 r.2.1 r.2.2)
  have hh : Continuous h := hg.comp continuous_toT3'
  have hpre : coordEquiv ⁻¹' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) = unitCube := by
    ext x
    simp only [mem_preimage, coordEquiv_apply, mem_prod, unitCube, mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1, h2⟩ i; fin_cases i <;> assumption
    · intro hx; exact ⟨hx 0, hx 1, hx 2⟩
  have step1 := measurePreserving_coordEquiv.setIntegral_preimage_emb
    coordEquiv.measurableEmbedding h (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)
  rw [hpre] at step1
  have hcomp : ∀ x, h (coordEquiv x) = g x := fun x => by
    simp only [h, coordEquiv_apply, toT3_coord]
  simp only [hcomp] at step1
  rw [step1]
  have K3 : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod _ (hh.continuousOn.integrableOn_compact K3)]
  unfold cellIntegral Cell.torusIntegral Cell.i2 Cell.i3
  rw [integral01_eq_setIntegral]
  refine setIntegral_congr_fun measurableSet_Icc fun a _ => ?_
  have K2 : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hha : Continuous fun r : ℝ × ℝ => h (a, r) := hh.comp (Continuous.prodMk_right a)
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod _ (hha.continuousOn.integrableOn_compact K2)]
  dsimp only
  rw [integral01_eq_setIntegral]
  refine setIntegral_congr_fun measurableSet_Icc fun b _ => ?_
  dsimp only
  rw [integral01_eq_setIntegral]
  rfl

end NSTorus
