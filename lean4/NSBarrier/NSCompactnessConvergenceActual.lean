import NSBarrier.NSLimitClosureStability
import NSBarrier.NSGalerkinCoeffODEProductRuleProof
import Mathlib.Tactic

open Filter
open NSTorusShellActual

namespace NSCompactnessConvergenceActual

open NSGalerkinCoeffODEProductRuleProof
open NSGalerkinShellStepIdentity
open NSFiniteSourceTrajectory
open NSLimitClosureStability

-- ============================================================
-- SECTION 1: ACTUAL COMPACTNESS DATA ON THE CONCRETE STATE
-- ============================================================

structure CompactnessConvergenceStateData (K_max m : ℕ) where
  N0 : ℕ
  subseq : ℕ → ℕ
  modes : Finset Mode
  shellOf : Mode → Fin K_max
  coordOf : Mode → Fin m
  weight : Mode → ℝ
  damp : Mode → ℝ
  stateFam : ℕ → ℝ → Fin m → ℝ
  stateLim : ℝ → Fin m → ℝ
  time : ℕ → ℝ
  hstate_tendsto :
    ∀ n : ℕ, ∀ i : Fin m,
      Tendsto
        (fun j : ℕ => stateFam (subseq j) (time n) i)
        atTop
        (nhds (stateLim (time n) i))

#check @CompactnessConvergenceStateData

noncomputable def coeffOfStateFam
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m) :
    ℕ → ℝ → Mode → ℝ :=
  fun J t κ => d.stateFam J t (d.coordOf κ)

noncomputable def coeffOfStateLim
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m) :
    ℝ → Mode → ℝ :=
  fun t κ => d.stateLim t (d.coordOf κ)

#check @coeffOfStateFam
#check @coeffOfStateLim

-- ============================================================
-- SECTION 2: COEFFICIENT CONVERGENCE
-- ============================================================

theorem coeff_tendsto_of_state_tendsto
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m) :
    ∀ n : ℕ, ∀ κ : Mode,
      Tendsto
        (fun j => coeffOfStateFam d (d.subseq j)
          (d.time n) κ)
        atTop
        (nhds (coeffOfStateLim d (d.time n) κ)) := by
  intro n κ
  simp only [coeffOfStateFam, coeffOfStateLim]
  exact d.hstate_tendsto n (d.coordOf κ)

#check @coeff_tendsto_of_state_tendsto

-- ============================================================
-- SECTION 3: SHELLWISE QUADRATIC CONVERGENCE
-- ============================================================

theorem Xi_shell_tendsto_of_coeff_tendsto
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Tendsto
        (fun j => XiContOfCoeffs d.modes d.shellOf d.weight
          (coeffOfStateFam d (d.subseq j))
          (d.time n) k)
        atTop
        (nhds (XiContOfCoeffs d.modes d.shellOf d.weight
          (coeffOfStateLim d)
          (d.time n) k)) := by
  intro n k
  unfold XiContOfCoeffs
  apply tendsto_finset_sum
  intro κ _hκ
  have hcoeff := coeff_tendsto_of_state_tendsto d n κ
  exact (hcoeff.pow 2).const_mul (d.weight κ)

#check @Xi_shell_tendsto_of_coeff_tendsto

-- ============================================================
-- SECTION 4: TOTAL ENSTROPHY CONVERGENCE
-- ============================================================

theorem hElim_tendsto_of_state_compactness
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m) :
    ∀ n : ℕ,
      Tendsto
        (fun j => ∑ k : Fin K_max,
          XiContOfCoeffs d.modes d.shellOf d.weight
            (coeffOfStateFam d (d.subseq j))
            (d.time n) k)
        atTop
        (nhds (∑ k : Fin K_max,
          XiContOfCoeffs d.modes d.shellOf d.weight
            (coeffOfStateLim d)
            (d.time n) k)) := by
  intro n
  apply tendsto_finset_sum
  intro k _hk
  exact Xi_shell_tendsto_of_coeff_tendsto d n k

#check @hElim_tendsto_of_state_compactness

-- ============================================================
-- SECTION 5: DISSIPATION CONVERGENCE
-- ============================================================

theorem DContShell_tendsto_of_coeff_tendsto
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Tendsto
        (fun j => DContOfCoeffs d.modes d.shellOf d.weight
          (coeffOfStateFam d (d.subseq j))
          d.damp (d.time n) k)
        atTop
        (nhds (DContOfCoeffs d.modes d.shellOf d.weight
          (coeffOfStateLim d)
          d.damp (d.time n) k)) := by
  intro n k
  unfold DContOfCoeffs
  apply tendsto_finset_sum
  intro κ _hκ
  have hcoeff := coeff_tendsto_of_state_tendsto d n κ
  exact (hcoeff.pow 2).const_mul (2 * d.weight κ * d.damp κ)

theorem hDlim_tendsto_of_state_compactness
    {K_max m : ℕ}
    (d : CompactnessConvergenceStateData K_max m)
    (Ncut : ℕ) :
    ∀ n : ℕ,
      Tendsto
        (fun j => ∑ k ∈ lowShells (K_max := K_max) Ncut,
          DContOfCoeffs d.modes d.shellOf d.weight
            (coeffOfStateFam d (d.subseq j))
            d.damp (d.time n) k)
        atTop
        (nhds (∑ k ∈ lowShells (K_max := K_max) Ncut,
          DContOfCoeffs d.modes d.shellOf d.weight
            (coeffOfStateLim d)
            d.damp (d.time n) k)) := by
  intro n
  apply tendsto_finset_sum
  intro k _hk
  exact DContShell_tendsto_of_coeff_tendsto d n k

#check @DContShell_tendsto_of_coeff_tendsto
#check @hDlim_tendsto_of_state_compactness

end NSCompactnessConvergenceActual
