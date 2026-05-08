import NSBarrier.NSShellBlockModewiseActual
import NSBarrier.NSLocalPairingModewiseActual
import NSBarrier.NSShellEnergyTermActual
import Mathlib.Tactic

open NSTorusShellActual

namespace NSModewiseMajorizationTheorems

open NSFiniteFourierActual
open NSShellBlockCoeffActual
open NSShellBlockUpperActual
open NSShellBlockModewiseActual
open NSLocalPairingXiActual
open NSLocalPairingCoeffBoundActual
open NSLocalPairingModewiseActual
open NSShellEnergyTermActual

-- ============================================================
-- Modewise majorization theorems
--
-- These make explicit the pointwise modewise comparisons that
-- were previously implicit in structure fields.
-- ============================================================

/-- [Alg] Coefficient square is majorized by the mode weight square. -/
theorem coeffSq_le_modeWeightSq_of_modewise
    {K_max : ℕ}
    (ns : ActualModewiseShellBlockData K_max) :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ ns.modes → (ns.coeffAbs n κ)^2 ≤ ns.modeWeightSq n κ :=
  ns.hcoeffSq_le_modeWeightSq

/-- [Alg] Mode weight square is majorized by the shell energy term. -/
theorem modeWeightSq_le_shellEnergyTerm_of_modewise
    {K_max : ℕ}
    (ns : ActualModewiseShellBlockData K_max) :
    ∀ n : ℕ, ∀ κ : Mode,
      κ ∈ ns.modes → ns.modeWeightSq n κ ≤ ns.shellEnergyTerm n κ :=
  ns.hmodeWeightSq_le_shellEnergyTerm

/-- [Alg] Local production coefficient is majorized by the coefficient magnitude. -/
theorem localProdCoeff_le_coeffAbs_of_modewise
    {K_max : ℕ}
    (ns : ActualLocalPairingTermData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      κ ∈ ns.modes → ns.pairTerm n k κ ≤ ns.coeffAbs n κ :=
  ns.hpairTerm_le_coeffAbs

/-- [Alg] Local production term is majorized by pairTerm times Xi. -/
theorem localProdTerm_le_pairTermXi_of_modewise
    {K_max : ℕ}
    (ns : ActualModewiseLocalPairingData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max, ∀ κ : Mode,
      k.val < ns.supportData.Ncut →
      1 ≤ k.val →
      κ ∈ ns.modes →
        ns.localProdTerm n k κ ≤ ns.pairTerm n k κ * ns.Xi n k :=
  ns.hlocalProd_le_pairTermXi

#check @coeffSq_le_modeWeightSq_of_modewise
#check @modeWeightSq_le_shellEnergyTerm_of_modewise
#check @localProdCoeff_le_coeffAbs_of_modewise
#check @localProdTerm_le_pairTermXi_of_modewise

end NSModewiseMajorizationTheorems
