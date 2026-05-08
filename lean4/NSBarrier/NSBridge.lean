import NSBarrier.Basic
import NSBarrier.NSFourier
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# NSBridge
Bridge layer connecting the abstract shell-budget barrier theorems
with the Fourier-side analytic interface.
-/

open NSFourier

namespace NSBridge

/-- Lift Fourier shell energy into the barrier-side `ShellEnergy` type. -/
def liftedShellEnergy {K_max : ℕ}
    (fs : FourierState K_max) : ShellEnergy K_max :=
  fun _ k => fs.shellEnergy k

/-- Lift the induced Fourier strain amplitude into the barrier-side
    `StrainAmplitude` type. -/
def liftedStrainAmplitude {K_max : ℕ}
    (fs : FourierState K_max) (C_shell : ℝ) : StrainAmplitude K_max :=
  fun _ => inducedAmplitude fs C_shell

/-- Bridge shell-energy nonnegativity from `NSFourier` to the barrier layer. -/
theorem bridge_shellEnergy_nonneg {K_max : ℕ}
    (fs : FourierState K_max)
    (hE : ShellEnergyNonneg fs) :
    ShellEnergyNonneg (liftedShellEnergy fs) := by
  intro sb k
  exact hE k

/-- Bridge physical production closure from `NSFourier` to the barrier layer. -/
theorem bridge_physical_production_closure {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (C_shell : ℝ)
    (hS : 0 ≤ fs.strainSup)
    (hprod : ProductionFromStrainSup sb.P fs)
    (hXiE : ShellVorticityEnergyBound fs C_shell) :
    PhysicalProductionClosure sb (liftedStrainAmplitude fs C_shell) (liftedShellEnergy fs) := by
  intro k
  exact physical_production_closure_inst sb.P fs C_shell hS hprod hXiE k

/-- Bridge physical dissipation closure from `NSFourier` to the barrier layer. -/
theorem bridge_physical_dissipation_closure {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (ν : ℝ)
    (hD : DissipationFromEnergy sb.D ν fs) :
    PhysicalDissipationClosure sb ν (liftedShellEnergy fs) := by
  intro k
  exact hD k

/-- Main bridge theorem:
    Fourier-side physical estimates imply the barrier-side no-advance theorem. -/
theorem no_advance_from_fourier_inst {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_shell : ℝ)
    (hAbarrier :
      inducedAmplitude fs₂ C_shell ≤ ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hS : 0 ≤ fs₂.strainSup)
    (hE : ShellEnergyNonneg fs₂)
    (hprod : ProductionFromStrainSup sb₂.P fs₂)
    (hXiE : ShellVorticityEnergyBound fs₂ C_shell)
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_physical
    sb₁ sb₂ ν
    (liftedStrainAmplitude fs₂ C_shell)
    (liftedShellEnergy fs₂)
  · simpa [liftedStrainAmplitude] using hAbarrier
  · exact bridge_shellEnergy_nonneg fs₂ hE
  · exact bridge_physical_production_closure sb₂ fs₂ C_shell hS hprod hXiE
  · exact bridge_physical_dissipation_closure sb₂ fs₂ ν hD

#check @liftedShellEnergy
#check @liftedStrainAmplitude
#check @bridge_shellEnergy_nonneg
#check @bridge_physical_production_closure
#check @bridge_physical_dissipation_closure
#check @no_advance_from_fourier_inst

-- ============================================================
-- SECTION 12: TIME-INDEXED FOURIER TRAJECTORIES
-- ============================================================

/-- A discrete-time trajectory of Fourier-side states. -/
def FourierTrajectory (K_max : ℕ) := ℕ → FourierState K_max

/-- Eventually, no corridor step can occur from Fourier-side physical hypotheses. -/
theorem eventually_no_corridorStep_from_fourier_inst {K_max : ℕ}
    (btraj : BudgetTrajectory K_max)
    (ftraj : FourierTrajectory K_max)
    (ν C_shell : ℝ)
    (hS : ∀ n : ℕ, 0 ≤ (ftraj n).strainSup)
    (hE : ∀ n : ℕ, NSFourier.ShellEnergyNonneg (ftraj n))
    (hAbarrier :
      ∃ Na : ℕ, ∀ n : ℕ, Na ≤ n →
        inducedAmplitude (ftraj (n + 1)) C_shell ≤
          ν * (jumpFront (btraj (n + 1)) : ℝ)^2)
    (hprod :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n →
        ProductionFromStrainSup (btraj (n + 1)).P (ftraj (n + 1)))
    (hXiE :
      ∃ Nx : ℕ, ∀ n : ℕ, Nx ≤ n →
        ShellVorticityEnergyBound (ftraj (n + 1)) C_shell)
    (hD :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        DissipationFromEnergy (btraj (n + 1)).D ν (ftraj (n + 1))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ corridorStep (btraj n) (btraj (n + 1)) := by
  rcases hAbarrier with ⟨Na, hA⟩
  rcases hprod with ⟨Np, hP⟩
  rcases hXiE with ⟨Nx, hX⟩
  rcases hD with ⟨Nd, hD'⟩
  refine ⟨max Na (max Np (max Nx Nd)), ?_⟩
  intro n hn
  have hNa : Na ≤ n := by
    exact le_trans (le_max_left Na (max Np (max Nx Nd))) hn
  have hmid1 : max Np (max Nx Nd) ≤ n := by
    exact le_trans (le_max_right Na (max Np (max Nx Nd))) hn
  have hNp : Np ≤ n := by
    exact le_trans (le_max_left Np (max Nx Nd)) hmid1
  have hmid2 : max Nx Nd ≤ n := by
    exact le_trans (le_max_right Np (max Nx Nd)) hmid1
  have hNx : Nx ≤ n := by
    exact le_trans (le_max_left Nx Nd) hmid2
  have hNd : Nd ≤ n := by
    exact le_trans (le_max_right Nx Nd) hmid2
  exact no_advance_from_fourier_inst
    (btraj n) (btraj (n + 1)) (ftraj (n + 1)) ν C_shell
    (hA n hNa)
    (hS (n + 1))
    (hE (n + 1))
    (hP n hNp)
    (hX n hNx)
    (hD' n hNd)

/-- After the Fourier-side barrier regime begins, the jump front is eventually nonincreasing. -/
theorem jumpFront_eventually_nonincreasing_from_fourier_inst {K_max : ℕ}
    (btraj : BudgetTrajectory K_max)
    (ftraj : FourierTrajectory K_max)
    (ν C_shell : ℝ)
    (hS : ∀ n : ℕ, 0 ≤ (ftraj n).strainSup)
    (hE : ∀ n : ℕ, NSFourier.ShellEnergyNonneg (ftraj n))
    (hAbarrier :
      ∃ Na : ℕ, ∀ n : ℕ, Na ≤ n →
        inducedAmplitude (ftraj (n + 1)) C_shell ≤
          ν * (jumpFront (btraj (n + 1)) : ℝ)^2)
    (hprod :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n →
        ProductionFromStrainSup (btraj (n + 1)).P (ftraj (n + 1)))
    (hXiE :
      ∃ Nx : ℕ, ∀ n : ℕ, Nx ≤ n →
        ShellVorticityEnergyBound (ftraj (n + 1)) C_shell)
    (hD :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        DissipationFromEnergy (btraj (n + 1)).D ν (ftraj (n + 1))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      jumpFront (btraj (n + 1)) ≤ jumpFront (btraj n) := by
  rcases eventually_no_corridorStep_from_fourier_inst
      btraj ftraj ν C_shell hS hE hAbarrier hprod hXiE hD with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hnc : ¬ corridorStep (btraj n) (btraj (n + 1)) := hN n hn
  exact Nat.not_lt.mp hnc

/-- Under the Fourier-side barrier regime, the jump front eventually stabilizes
    to a constant value. -/
theorem jumpFront_eventually_constant_from_fourier_inst {K_max : ℕ}
    (btraj : BudgetTrajectory K_max)
    (ftraj : FourierTrajectory K_max)
    (ν C_shell : ℝ)
    (hS : ∀ n : ℕ, 0 ≤ (ftraj n).strainSup)
    (hE : ∀ n : ℕ, NSFourier.ShellEnergyNonneg (ftraj n))
    (hAbarrier :
      ∃ Na : ℕ, ∀ n : ℕ, Na ≤ n →
        inducedAmplitude (ftraj (n + 1)) C_shell ≤
          ν * (jumpFront (btraj (n + 1)) : ℝ)^2)
    (hprod :
      ∃ Np : ℕ, ∀ n : ℕ, Np ≤ n →
        ProductionFromStrainSup (btraj (n + 1)).P (ftraj (n + 1)))
    (hXiE :
      ∃ Nx : ℕ, ∀ n : ℕ, Nx ≤ n →
        ShellVorticityEnergyBound (ftraj (n + 1)) C_shell)
    (hD :
      ∃ Nd : ℕ, ∀ n : ℕ, Nd ≤ n →
        DissipationFromEnergy (btraj (n + 1)).D ν (ftraj (n + 1))) :
    ∃ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → jumpFront (btraj n) = m := by
  rcases jumpFront_eventually_nonincreasing_from_fourier_inst
      btraj ftraj ν C_shell hS hE hAbarrier hprod hXiE hD with
    ⟨N0, hmono⟩
  let f : ℕ → ℕ := fun n => jumpFront (btraj (N0 + n))
  have hfmono : ∀ n, f (n + 1) ≤ f n := by
    intro n
    have hN0 : N0 ≤ N0 + n := by omega
    simpa [f, Nat.add_assoc] using hmono (N0 + n) hN0
  rcases nat_seq_eventually_constant_of_nonincreasing f hfmono with
    ⟨m, N1, hconst⟩
  refine ⟨m, N0 + N1, ?_⟩
  intro n hn
  have hN0 : N0 ≤ n := by omega
  rcases Nat.exists_eq_add_of_le hN0 with ⟨t, rfl⟩
  have ht : N1 ≤ t := by omega
  simpa [f] using hconst t ht

#check @FourierTrajectory
#check @eventually_no_corridorStep_from_fourier_inst
#check @jumpFront_eventually_nonincreasing_from_fourier_inst
#check @jumpFront_eventually_constant_from_fourier_inst

-- ============================================================
-- SECTION 13: STAGED PHYSICAL PRODUCTION CLOSURE
-- ============================================================

/-- Auxiliary gradient-type amplitude, intended to model ‖∇v‖∞
    or a comparable shellwise stretching amplitude. -/
def GradientAmplitude (K_max : ℕ) := FourierState K_max → ℝ

/-- Localized shellwise production bound:
    P_k ≤ G(fs) · Ξ_k. This is the post-localized form of the projected
    stretching estimate, after shell-locality has been imposed. -/
def LocalizedProductionFromGradient {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max) : Prop :=
  ∀ k : Fin K_max, sb.P k ≤ G fs * fs.shellVorticitySq k

/-- Control of the gradient-type amplitude by strain-sup:
    G(fs) ≤ C_str · strainSup(fs). -/
def GradientControlledByStrain {K_max : ℕ}
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str : ℝ) : Prop :=
  G fs ≤ C_str * fs.strainSup

/-- Staged physical-production theorem:
    from localized production plus gradient-to-strain control,
    obtain the shellwise strain-sup production bound needed by the barrier layer. -/
theorem physical_production_from_strain_sup_step {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str : ℝ)
    (hXi : NSFourier.ShellVorticitySqNonneg fs)
    (hloc : LocalizedProductionFromGradient sb fs G)
    (hgc : GradientControlledByStrain fs G C_str) :
    ProductionFromStrainSup sb.P
      { fs with strainSup := C_str * fs.strainSup } := by
  intro k
  have hPk : sb.P k ≤ G fs * fs.shellVorticitySq k := hloc k
  have hXik : 0 ≤ fs.shellVorticitySq k := hXi k
  have hcoef : G fs ≤ C_str * fs.strainSup := hgc
  have hmul :
      G fs * fs.shellVorticitySq k ≤
      (C_str * fs.strainSup) * fs.shellVorticitySq k := by
    exact mul_le_mul_of_nonneg_right hcoef hXik
  exact le_trans hPk (by simpa using hmul)

/-- Full shellwise production closure from the staged physical assumptions:
    P_k ≤ (C_str · C_shell · strainSup(fs)) · k² · E_k. -/
theorem physical_production_closure_from_locality {K_max : ℕ}
    (sb : ShellBudget K_max)
    (fs : FourierState K_max)
    (G : GradientAmplitude K_max)
    (C_str C_shell : ℝ)
    (hXi : NSFourier.ShellVorticitySqNonneg fs)
    (hS : 0 ≤ fs.strainSup)
    (hCstr : 0 ≤ C_str)
    (hloc : LocalizedProductionFromGradient sb fs G)
    (hgc : GradientControlledByStrain fs G C_str)
    (hXiE : ShellVorticityEnergyBound fs C_shell) :
    PhysicalProductionClosure sb
      (liftedStrainAmplitude fs (C_str * C_shell))
      (liftedShellEnergy fs) := by
  intro k
  have hprod :
      ProductionFromStrainSup sb.P { fs with strainSup := C_str * fs.strainSup } :=
    physical_production_from_strain_sup_step sb fs G C_str hXi hloc hgc
  have hclosure :
      ∀ k : Fin K_max,
        sb.P k ≤
          inducedAmplitude ({ fs with strainSup := C_str * fs.strainSup }) C_shell
            * (k.val : ℝ) ^ 2
            * ({ fs with strainSup := C_str * fs.strainSup }).shellEnergy k :=
    NSFourier.physical_production_closure_inst
      sb.P
      { fs with strainSup := C_str * fs.strainSup }
      C_shell
      (by nlinarith [hS, hCstr])
      hprod
      (by
        intro j
        simpa using hXiE j)
  have hk := hclosure k
  simpa [liftedStrainAmplitude, liftedShellEnergy, NSFourier.inducedAmplitude,
    mul_assoc, mul_left_comm, mul_comm]
    using hk

/-- Main staged bridge theorem:
    localized projected production + shell vorticity-energy control +
    dissipation from shell energy imply no front advance. -/
theorem no_advance_physical_from_locality_inst {K_max : ℕ}
    (sb₁ sb₂ : ShellBudget K_max)
    (fs₂ : FourierState K_max)
    (ν C_str C_shell : ℝ)
    (G : GradientAmplitude K_max)
    (hAbarrier :
      inducedAmplitude fs₂ (C_str * C_shell) ≤
        ν * (jumpFront sb₂ : ℝ) ^ 2)
    (hXi : NSFourier.ShellVorticitySqNonneg fs₂)
    (hS : 0 ≤ fs₂.strainSup)
    (hCstr : 0 ≤ C_str)
    (hE : NSFourier.ShellEnergyNonneg fs₂)
    (hloc : LocalizedProductionFromGradient sb₂ fs₂ G)
    (hgc : GradientControlledByStrain fs₂ G C_str)
    (hXiE : ShellVorticityEnergyBound fs₂ C_shell)
    (hD : DissipationFromEnergy sb₂.D ν fs₂) :
    ¬ corridorStep sb₁ sb₂ := by
  apply no_advance_physical
    sb₁ sb₂ ν
    (liftedStrainAmplitude fs₂ (C_str * C_shell))
    (liftedShellEnergy fs₂)
  · simpa [liftedStrainAmplitude] using hAbarrier
  · exact bridge_shellEnergy_nonneg fs₂ hE
  · exact
      physical_production_closure_from_locality
        sb₂ fs₂ G C_str C_shell hXi hS hCstr hloc hgc hXiE
  · exact bridge_physical_dissipation_closure sb₂ fs₂ ν hD

#check @GradientAmplitude
#check @LocalizedProductionFromGradient
#check @GradientControlledByStrain
#check @physical_production_from_strain_sup_step
#check @physical_production_closure_from_locality
#check @no_advance_physical_from_locality_inst


end NSBridge
