import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformBridge
import NSBarrier.NSUniformA2Bridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSBridge
open NSUniform
open NSUniformBridge
open NSUniformA2Bridge

namespace NSUniformA1Bridge

-- ============================================================
-- SECTION 1: UNIFORM A1 HYPOTHESES
-- ============================================================

/-- A family of gradient amplitudes indexed by truncation level. -/
def GradientAmplitudeFamily := ∀ K_max : ℕ, GradientAmplitude K_max

/-- Uniform nonnegativity of shellwise vorticity size. -/
def UniformShellVorticitySqNonneg
    (ftraj : FourierTrajectoryFamily) : Prop :=
  ∀ K_max n, ShellVorticitySqNonneg (ftraj K_max n)

/-- Eventually, shellwise production is controlled by a gradient-type amplitude,
    uniformly in `K_max`. -/
def UniformLocalizedProductionFromGradient
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    LocalizedProductionFromGradient
      ((btraj K_max) (n + 1))
      (ftraj K_max (n + 1))
      (Gfam K_max)

/-- Eventually, the gradient-type amplitude is controlled by strain-sup,
    uniformly in `K_max`. -/
def UniformGradientControlledByStrain
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (C_str : ℝ) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    GradientControlledByStrain
      (ftraj K_max (n + 1))
      (Gfam K_max)
      C_str

#check @GradientAmplitudeFamily
#check @UniformShellVorticitySqNonneg
#check @UniformLocalizedProductionFromGradient
#check @UniformGradientControlledByStrain

-- ============================================================
-- SECTION 2: SCALED STRAIN TRAJECTORY
-- ============================================================

/-- Scale the strain amplitude of a Fourier trajectory by a constant `C_str`. -/
def scaledStrainTrajectory
    (ftraj : FourierTrajectoryFamily)
    (C_str : ℝ) : FourierTrajectoryFamily :=
  fun K_max n => { ftraj K_max n with strainSup := C_str * (ftraj K_max n).strainSup }

/-- Uniform strain-sup nonnegativity is preserved under nonnegative scaling. -/
theorem uniform_strainSupNonneg_scaled
    (ftraj : FourierTrajectoryFamily)
    (C_str : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj) :
    UniformStrainSupNonneg (scaledStrainTrajectory ftraj C_str) := by
  intro K_max n
  dsimp [scaledStrainTrajectory]
  have hSn : 0 ≤ (ftraj K_max n).strainSup := hS K_max n
  nlinarith

/-- Uniform shell energy nonnegativity is unchanged by strain scaling. -/
theorem uniform_shellEnergyNonneg_scaled
    (ftraj : FourierTrajectoryFamily)
    (C_str : ℝ)
    (hE : UniformShellEnergyNonneg ftraj) :
    UniformShellEnergyNonneg (scaledStrainTrajectory ftraj C_str) := by
  intro K_max n
  dsimp [scaledStrainTrajectory]
  exact hE K_max n

/-- Uniform shellwise vorticity nonnegativity is unchanged by strain scaling. -/
theorem uniform_shellVorticitySqNonneg_scaled
    (ftraj : FourierTrajectoryFamily)
    (C_str : ℝ)
    (hXi : UniformShellVorticitySqNonneg ftraj) :
    UniformShellVorticitySqNonneg (scaledStrainTrajectory ftraj C_str) := by
  intro K_max n
  dsimp [scaledStrainTrajectory]
  exact hXi K_max n

/-- Uniform zero-shell vorticity is unchanged by strain scaling. -/
theorem uniform_zeroShellVorticity_scaled
    (ftraj : FourierTrajectoryFamily)
    (C_str : ℝ)
    (h0 : UniformZeroShellVorticity ftraj) :
    UniformZeroShellVorticity (scaledStrainTrajectory ftraj C_str) := by
  rcases h0 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn
  dsimp [scaledStrainTrajectory]
  exact hN K_max n hn

/-- Uniform vorticity-by-radius control is unchanged by strain scaling. -/
theorem uniform_vorticityControlledByRadiusSq_scaled
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (C_str : ℝ)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj) :
    UniformVorticityControlledByRadiusSq (scaledStrainTrajectory ftraj C_str) rtraj := by
  rcases hXiR with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn
  dsimp [scaledStrainTrajectory]
  exact hN K_max n hn

/-- Uniform dissipation-from-energy is unchanged by strain scaling. -/
theorem uniform_dissipationFromEnergy_scaled
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (C_str ν : ℝ)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    UniformDissipationFromEnergy btraj (scaledStrainTrajectory ftraj C_str) ν := by
  rcases hD with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn
  dsimp [scaledStrainTrajectory]
  exact hN K_max n hn

/-- A barrier threshold for the original trajectory with combined constant
    `C_str * C_shell` induces a barrier threshold for the scaled trajectory
    with shell constant `C_shell`. -/
theorem uniform_barrierThreshold_scaled_of_combined
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell)) :
    UniformBarrierThreshold btraj (scaledStrainTrajectory ftraj C_str) ν C_shell := by
  rcases hA with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn
  have h := hN K_max n hn
  simpa [scaledStrainTrajectory, NSFourier.inducedAmplitude,
    mul_assoc, mul_left_comm, mul_comm] using h

#check @scaledStrainTrajectory
#check @uniform_strainSupNonneg_scaled
#check @uniform_shellEnergyNonneg_scaled
#check @uniform_shellVorticitySqNonneg_scaled
#check @uniform_zeroShellVorticity_scaled
#check @uniform_vorticityControlledByRadiusSq_scaled
#check @uniform_dissipationFromEnergy_scaled
#check @uniform_barrierThreshold_scaled_of_combined

-- ============================================================
-- SECTION 3: UNIFORM A1 -> UNIFORM ProductionFromStrainSup
-- ============================================================

/-- Uniform A1 hypotheses imply the uniform shellwise
    `ProductionFromStrainSup` hypothesis, after scaling the strain trajectory. -/
theorem uniform_productionFromStrainSup_from_locality
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (C_str : ℝ)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str) :
    UniformProductionFromStrainSup btraj (scaledStrainTrajectory ftraj C_str) := by
  rcases hloc with ⟨Nl, hloc'⟩
  rcases hgc with ⟨Ng, hgc'⟩
  refine ⟨max Nl Ng, ?_⟩
  intro K_max n hn
  have hNl : Nl ≤ n := by
    exact le_trans (le_max_left Nl Ng) hn
  have hNg : Ng ≤ n := by
    exact le_trans (le_max_right Nl Ng) hn
  simpa [scaledStrainTrajectory] using
    (physical_production_from_strain_sup_step
      ((btraj K_max) (n + 1))
      (ftraj K_max (n + 1))
      (Gfam K_max)
      C_str
      (hXi K_max (n + 1))
      (hloc' K_max n hNl)
      (hgc' K_max n hNg))

#check @uniform_productionFromStrainSup_from_locality

-- ============================================================
-- SECTION 4: A1 + A2 -> NSUniformBridge
-- ============================================================

/-- Combined A1+A2 route to eventual impossibility of corridor advance,
    using a scaled strain trajectory. -/
theorem uniform_eventually_no_corridorStep_from_locality_A1A2_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∃ N : ℕ, ∀ K_max n, N ≤ n →
      ¬ corridorStep ((btraj K_max) n) ((btraj K_max) (n + 1)) := by
  apply NSUniformBridge.uniform_eventually_no_corridorStep_from_fourier_inst
    btraj
    (scaledStrainTrajectory ftraj C_str)
    ν
    C_shell
  · exact uniform_strainSupNonneg_scaled ftraj C_str hCstr hS
  · exact uniform_shellEnergyNonneg_scaled ftraj C_str hE
  · exact uniform_barrierThreshold_scaled_of_combined btraj ftraj ν C_str C_shell hA
  · exact uniform_productionFromStrainSup_from_locality btraj ftraj Gfam C_str hXi hloc hgc
  · exact
      uniform_shellVorticityEnergyBound_from_radius
        (scaledStrainTrajectory ftraj C_str)
        rtraj
        C_shell
        (uniform_zeroShellVorticity_scaled ftraj C_str h0)
        (uniform_shellEnergyNonneg_scaled ftraj C_str hE)
        (uniform_vorticityControlledByRadiusSq_scaled ftraj rtraj C_str hXiR)
        hR
  · exact uniform_dissipationFromEnergy_scaled btraj ftraj C_str ν hD

/-- Combined A1+A2 route to eventual front nonincrease. -/
theorem uniform_eventually_nonincreasing_front_from_locality_A1A2_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    UniformEventuallyNonincreasingFront btraj := by
  apply NSUniformBridge.uniform_eventually_nonincreasing_front_from_fourier_inst
    btraj
    (scaledStrainTrajectory ftraj C_str)
    ν
    C_shell
  · exact uniform_strainSupNonneg_scaled ftraj C_str hCstr hS
  · exact uniform_shellEnergyNonneg_scaled ftraj C_str hE
  · exact uniform_barrierThreshold_scaled_of_combined btraj ftraj ν C_str C_shell hA
  · exact uniform_productionFromStrainSup_from_locality btraj ftraj Gfam C_str hXi hloc hgc
  · exact
      uniform_shellVorticityEnergyBound_from_radius
        (scaledStrainTrajectory ftraj C_str)
        rtraj
        C_shell
        (uniform_zeroShellVorticity_scaled ftraj C_str h0)
        (uniform_shellEnergyNonneg_scaled ftraj C_str hE)
        (uniform_vorticityControlledByRadiusSq_scaled ftraj rtraj C_str hXiR)
        hR
  · exact uniform_dissipationFromEnergy_scaled btraj ftraj C_str ν hD

/-- Combined A1+A2 route to pointwise eventual constancy for each truncation. -/
theorem pointwise_eventually_constant_from_locality_A1A2_inst
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (Gfam : GradientAmplitudeFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_str C_shell : ℝ)
    (hCstr : 0 ≤ C_str)
    (hS : UniformStrainSupNonneg ftraj)
    (hXi : UniformShellVorticitySqNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (C_str * C_shell))
    (hloc : UniformLocalizedProductionFromGradient btraj ftraj Gfam)
    (hgc : UniformGradientControlledByStrain ftraj Gfam C_str)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ m N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) = m := by
  apply NSUniformBridge.pointwise_eventually_constant_from_uniform_fourier_inst
    btraj
    (scaledStrainTrajectory ftraj C_str)
    ν
    C_shell
  · exact uniform_strainSupNonneg_scaled ftraj C_str hCstr hS
  · exact uniform_shellEnergyNonneg_scaled ftraj C_str hE
  · exact uniform_barrierThreshold_scaled_of_combined btraj ftraj ν C_str C_shell hA
  · exact uniform_productionFromStrainSup_from_locality btraj ftraj Gfam C_str hXi hloc hgc
  · exact
      uniform_shellVorticityEnergyBound_from_radius
        (scaledStrainTrajectory ftraj C_str)
        rtraj
        C_shell
        (uniform_zeroShellVorticity_scaled ftraj C_str h0)
        (uniform_shellEnergyNonneg_scaled ftraj C_str hE)
        (uniform_vorticityControlledByRadiusSq_scaled ftraj rtraj C_str hXiR)
        hR
  · exact uniform_dissipationFromEnergy_scaled btraj ftraj C_str ν hD

#check @uniform_eventually_no_corridorStep_from_locality_A1A2_inst
#check @uniform_eventually_nonincreasing_front_from_locality_A1A2_inst
#check @pointwise_eventually_constant_from_locality_A1A2_inst

end NSUniformA1Bridge
