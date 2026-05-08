import NSBarrier.NSModewiseMajorizationTheorems
import Mathlib.Tactic

open NSTorusShellActual

namespace NSShellwiseSumBoundTheorems

open NSFiniteFourierActual
open NSShellBlockCoeffActual
open NSShellBlockUpperActual
open NSShellBlockModewiseActual
open NSLocalPairingXiActual
open NSLocalPairingCoeffBoundActual
open NSLocalPairingModewiseActual
open NSShellEnergyTermActual
open NSFiniteSourceTrajectory

-- ============================================================
-- Shellwise sum bound theorems
--
-- These are the modewise -> shellwise bridges:
-- summing modewise majorizations over the active mode set
-- to obtain shellwise bounds.
-- ============================================================

/-- [Alg] Shell coefficient square block is bounded by the shell block upper. -/
theorem shellCoeffSq_block_le_shellBlockUpper_of_shellsum
    {K_max : ℕ}
    (ns : ActualShellBlockUpperModeData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellCoeffSq ns.modes ns.coeffAbs ns.shellOf n k
          ≤
        shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf n k :=
  hshellCoeffSq_le_shellBlockUpper_of_modeWeights ns

/-- [Alg] Shell block upper is bounded by weighted shell energy. -/
theorem shellBlockUpper_le_shellEnergy_of_shellsum
    {K_max : ℕ}
    (ns : ActualModewiseShellBlockData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellBlockUpperOfModeWeights ns.modes ns.modeWeightSq ns.shellOf n k
          ≤
        ((k.val : ℝ)^2) * ns.Eshell n k :=
  hshellBlockUpper_le_shellEnergy_of_modewise ns

/-- [Alg] Shell energy sum is bounded by weighted shell energy
    (from modewise shell energy terms). -/
theorem shellEnergySum_le_weighted_shellEnergy_of_shellsum
    {K_max : ℕ}
    (ns : ActualModewiseShellEnergyData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k ∈ lowShells (K_max := K_max) ns.supportData.Ncut →
        shellBlockEnergySum ns.modes
          (shellEnergyTermOfModeEnergy ns.shellFactor ns.modeEnergyCoeff)
          ns.shellOf n k
          ≤
        ((k.val : ℝ)^2) * ns.Eshell n k :=
  hshellEnergySum_le_shellEnergy_of_modeEnergy ns

/-- [Alg] Local pairing coefficient is bounded by the l1 local strain amplitude. -/
theorem localPairingCoeff_le_l1LocalStrainAmp_of_shellsum
    {K_max : ℕ}
    (ns : ActualLocalPairingTermData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < ns.supportData.Ncut →
      1 ≤ k.val →
        localPairingCoeffOfTerms ns.modes ns.pairTerm n k
          ≤
        l1LocalStrainAmp ns.modes ns.coeffAbs n :=
  hlocalPairingCoeff_le_l1_of_pairTerms ns

#check @shellCoeffSq_block_le_shellBlockUpper_of_shellsum
#check @shellBlockUpper_le_shellEnergy_of_shellsum
#check @shellEnergySum_le_weighted_shellEnergy_of_shellsum
#check @localPairingCoeff_le_l1LocalStrainAmp_of_shellsum

end NSShellwiseSumBoundTheorems
