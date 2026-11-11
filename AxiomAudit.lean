import NSTorusUniqueness

/-! Axiom audit: every headline theorem must depend only on `propext`, `Classical.choice`,
`Quot.sound`. -/

open NSTorus

#print axioms IsPeriodicSmoothSolutionOn.eq_of_same_data
#print axioms IsPeriodicSmoothSolutionOn.pressureGradient_eq_of_same_data
#print axioms IsPeriodicSmoothSolutionOn.pressure_sub_const_of_same_data
#print axioms IsPeriodicSmoothSolutionIcc.eq_of_eq_zero
#print axioms IsPeriodicSmoothSolutionOn.toIcc
#print axioms le_zero_of_deriv_le_mul
#print axioms exists_bound_fderiv
#print axioms cellEnergy_deriv_le
#print axioms hasDerivWithinAt_cellEnergy
#print axioms cellIntegral_fderiv_eq_zero
#print axioms cellIntegral_inner_convective_eq_zero
#print axioms cellIntegral_inner_pressureGradient_eq_zero
#print axioms cellIntegral_inner_laplacian
#print axioms cellIntegral_inner_laplacian_nonpos
#print axioms cellIntegral_eq_setIntegral_unitCube
#print axioms setIntegral_unitCube_fderiv_eq_zero
#print axioms setIntegral_unitCube_inner_convective_eq_zero
#print axioms setIntegral_unitCube_inner_pressureGradient_eq_zero
#print axioms setIntegral_unitCube_inner_laplacian
#print axioms setIntegral_unitCube_inner_laplacian_nonpos
#print axioms hasDerivWithinAt_setIntegral_unitCube_energy
#print axioms setIntegral_unitCube_energy_deriv_le

/-! Strict audit over every declaration in the `NSTorus` namespace. -/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.map₁.fold (init := #[]) fun acc c _ =>
    if (`NSTorus).isPrefixOf c then acc.push c else acc
  let mut bad : Array (Name × Name) := #[]
  for c in names do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        bad := bad.push (c, a)
  if bad.isEmpty then
    logInfo m!"AUDIT PASS: {names.size} NSTorus declarations; only propext, Classical.choice, Quot.sound"
  else
    logError m!"AUDIT FAIL: {bad}"
