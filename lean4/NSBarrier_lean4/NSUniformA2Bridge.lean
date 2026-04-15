import NSBarrier.Basic
import NSBarrier.NSFourier
import NSBarrier.NSBridge
import NSBarrier.NSUniform
import NSBarrier.NSUniformBridge
import NSBarrier.NSAnalyticA2
import NSBarrier.NSAnalyticA2Bridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open NSFourier
open NSUniform
open NSUniformBridge
open NSAnalyticA2
open NSAnalyticA2Bridge

namespace NSUniformA2Bridge

-- ============================================================
-- SECTION 1: UNIFORM A2 HYPOTHESES
-- ============================================================

/-- A family of shell radius-squared profiles indexed by truncation level and time. -/
def RadiusSqTrajectoryFamily := ∀ K_max : ℕ, ℕ → RadiusSqProfile K_max

/-- Eventually, the zero shell carries no vorticity, uniformly in `K_max`. -/
def UniformZeroShellVorticity
    (ftraj : FourierTrajectoryFamily) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    ZeroShellVorticity (ftraj K_max (n + 1))

/-- Eventually, shellwise vorticity is controlled by a shell radius-squared profile,
    uniformly in `K_max`. -/
def UniformVorticityControlledByRadiusSq
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    VorticityControlledByRadiusSq
      (ftraj K_max (n + 1))
      (rtraj K_max (n + 1))

/-- Eventually, the shell radius-squared profile is controlled by the shell index,
    uniformly in `K_max`. -/
def UniformRadiusSqControlledByIndex
    (rtraj : RadiusSqTrajectoryFamily)
    (C_shell : ℝ) : Prop :=
  ∃ N : ℕ, ∀ K_max n, N ≤ n →
    RadiusSqControlledByIndex
      (rtraj K_max (n + 1))
      C_shell

#check @UniformZeroShellVorticity
#check @UniformVorticityControlledByRadiusSq
#check @UniformRadiusSqControlledByIndex

-- ============================================================
-- SECTION 2: GENERIC A2 -> UNIFORM SHELL-VORTICITY-ENERGY BOUND
-- ============================================================

/-- Uniform A2 radius/profile hypotheses imply the uniform shellwise
    vorticity-energy bound required by `NSUniformBridge`. -/
theorem uniform_shellVorticityEnergyBound_from_radius
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (C_shell : ℝ)
    (h0 : UniformZeroShellVorticity ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell) :
    UniformShellVorticityEnergyBound ftraj C_shell := by
  rcases h0 with ⟨N0, h0'⟩
  rcases hXiR with ⟨Nx, hXiR'⟩
  rcases hR with ⟨Nr, hR'⟩
  refine ⟨max N0 (max Nx Nr), ?_⟩
  intro K_max n hn
  have hN0 : N0 ≤ n := by
    exact le_trans (le_max_left N0 (max Nx Nr)) hn
  have hmid : max Nx Nr ≤ n := by
    exact le_trans (le_max_right N0 (max Nx Nr)) hn
  have hNx : Nx ≤ n := by
    exact le_trans (le_max_left Nx Nr) hmid
  have hNr : Nr ≤ n := by
    exact le_trans (le_max_right Nx Nr) hmid
  exact
    bridge_shellVorticityEnergyBound_from_radius
      (ftraj K_max (n + 1))
      (rtraj K_max (n + 1))
      C_shell
      (h0' K_max n hN0)
      (hE K_max (n + 1))
      (hXiR' K_max n hNx)
      (hR' K_max n hNr)

#check @uniform_shellVorticityEnergyBound_from_radius

-- ============================================================
-- SECTION 3: UNIT-SHELL SPECIALIZATION
-- ============================================================

/-- Time-independent unit-shell radius profile, viewed as a trajectory family. -/
noncomputable def unitShellRadiusSqTrajectory : RadiusSqTrajectoryFamily :=
  fun K_max _ => unitShellRadiusSq K_max

/-- The unit-shell radius profile satisfies the index control uniformly,
    with the explicit constant 9/4. -/
theorem uniform_unitShellRadiusSq_control :
    UniformRadiusSqControlledByIndex
      unitShellRadiusSqTrajectory
      (9 / 4 : ℝ) := by
  refine ⟨0, ?_⟩
  intro K_max n _hn
  simpa [unitShellRadiusSqTrajectory] using
    (unitShellRadiusSq_control (K_max := K_max))

/-- Uniform unit-shell A2 hypotheses imply the uniform shellwise
    vorticity-energy bound with constant 9/4. -/
theorem uniform_shellVorticityEnergyBound_unit_shell
    (ftraj : FourierTrajectoryFamily)
    (h0 : UniformZeroShellVorticity ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory) :
    UniformShellVorticityEnergyBound ftraj (9 / 4 : ℝ) := by
  exact
    uniform_shellVorticityEnergyBound_from_radius
      ftraj
      unitShellRadiusSqTrajectory
      (9 / 4 : ℝ)
      h0
      hE
      hXiR
      uniform_unitShellRadiusSq_control

/-- Monotone unit-shell specialization:
    any larger shell constant also works uniformly. -/
theorem uniform_shellVorticityEnergyBound_unit_shell_of_le
    (ftraj : FourierTrajectoryFamily)
    (C_shell : ℝ)
    (hC : (9 / 4 : ℝ) ≤ C_shell)
    (h0 : UniformZeroShellVorticity ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory) :
    UniformShellVorticityEnergyBound ftraj C_shell := by
  rcases uniform_shellVorticityEnergyBound_unit_shell ftraj h0 hE hXiR with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro K_max n hn k
  have h94 :
      (ftraj K_max (n + 1)).shellVorticitySq k ≤
        (9 / 4 : ℝ) * (k.val : ℝ) ^ 2 * (ftraj K_max (n + 1)).shellEnergy k :=
    hN K_max n hn k
  have hEk : 0 ≤ (ftraj K_max (n + 1)).shellEnergy k :=
    hE K_max (n + 1) k
  have hfac_nonneg : 0 ≤ (k.val : ℝ) ^ 2 * (ftraj K_max (n + 1)).shellEnergy k := by
    have hk2_nonneg : 0 ≤ (k.val : ℝ) ^ 2 := by positivity
    nlinarith
  have hmono :
      (9 / 4 : ℝ) * ((k.val : ℝ) ^ 2 * (ftraj K_max (n + 1)).shellEnergy k) ≤
        C_shell * ((k.val : ℝ) ^ 2 * (ftraj K_max (n + 1)).shellEnergy k) := by
    exact mul_le_mul_of_nonneg_right hC hfac_nonneg
  have hmono' :
      (9 / 4 : ℝ) * (k.val : ℝ) ^ 2 * (ftraj K_max (n + 1)).shellEnergy k ≤
        C_shell * (k.val : ℝ) ^ 2 * (ftraj K_max (n + 1)).shellEnergy k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmono
  linarith

#check @unitShellRadiusSqTrajectory
#check @uniform_unitShellRadiusSq_control
#check @uniform_shellVorticityEnergyBound_unit_shell
#check @uniform_shellVorticityEnergyBound_unit_shell_of_le

-- ============================================================
-- SECTION 4: DIRECT REPLACEMENTS FOR NSUniformBridge
-- ============================================================

/-- Replace the uniform `ShellVorticityEnergyBound` hypothesis in
    `uniform_eventually_no_corridorStep_from_fourier_inst`
    by uniform A2 radius/profile hypotheses. -/
theorem uniform_eventually_no_corridorStep_from_fourier_inst_of_radius
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∃ N : ℕ, ∀ K_max n, N ≤ n →
      ¬ corridorStep ((btraj K_max) n) ((btraj K_max) (n + 1)) := by
  apply NSUniformBridge.uniform_eventually_no_corridorStep_from_fourier_inst
    btraj ftraj ν C_shell hS hE hA hP
  · exact uniform_shellVorticityEnergyBound_from_radius ftraj rtraj C_shell h0 hE hXiR hR
  · exact hD

/-- Replace the uniform `ShellVorticityEnergyBound` hypothesis in
    `uniform_eventually_nonincreasing_front_from_fourier_inst`
    by uniform A2 radius/profile hypotheses. -/
theorem uniform_eventually_nonincreasing_front_from_fourier_inst_of_radius
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    UniformEventuallyNonincreasingFront btraj := by
  apply NSUniformBridge.uniform_eventually_nonincreasing_front_from_fourier_inst
    btraj ftraj ν C_shell hS hE hA hP
  · exact uniform_shellVorticityEnergyBound_from_radius ftraj rtraj C_shell h0 hE hXiR hR
  · exact hD

/-- Replace the uniform `ShellVorticityEnergyBound` hypothesis in
    `pointwise_eventually_constant_from_uniform_fourier_inst`
    by uniform A2 radius/profile hypotheses. -/
theorem pointwise_eventually_constant_from_uniform_fourier_inst_of_radius
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ m N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) = m := by
  apply NSUniformBridge.pointwise_eventually_constant_from_uniform_fourier_inst
    btraj ftraj ν C_shell hS hE hA hP
  · exact uniform_shellVorticityEnergyBound_from_radius ftraj rtraj C_shell h0 hE hXiR hR
  · exact hD

/-- Replace the uniform `ShellVorticityEnergyBound` hypothesis in
    `pointwise_eventually_bounded_from_uniform_fourier_inst`
    by uniform A2 radius/profile hypotheses. -/
theorem pointwise_eventually_bounded_from_uniform_fourier_inst_of_radius
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (rtraj : RadiusSqTrajectoryFamily)
    (ν C_shell : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν C_shell)
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj rtraj)
    (hR : UniformRadiusSqControlledByIndex rtraj C_shell)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ M N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  apply NSUniformBridge.pointwise_eventually_bounded_from_uniform_fourier_inst
    btraj ftraj ν C_shell hS hE hA hP
  · exact uniform_shellVorticityEnergyBound_from_radius ftraj rtraj C_shell h0 hE hXiR hR
  · exact hD

#check @uniform_eventually_no_corridorStep_from_fourier_inst_of_radius
#check @uniform_eventually_nonincreasing_front_from_fourier_inst_of_radius
#check @pointwise_eventually_constant_from_uniform_fourier_inst_of_radius
#check @pointwise_eventually_bounded_from_uniform_fourier_inst_of_radius

-- ============================================================
-- SECTION 5: UNIT-SHELL REPLACEMENTS
-- ============================================================

/-- Unit-shell version of
    `uniform_eventually_no_corridorStep_from_fourier_inst_of_radius`. -/
theorem uniform_eventually_no_corridorStep_from_fourier_inst_of_unit_shell
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (9 / 4 : ℝ))
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∃ N : ℕ, ∀ K_max n, N ≤ n →
      ¬ corridorStep ((btraj K_max) n) ((btraj K_max) (n + 1)) := by
  exact
    uniform_eventually_no_corridorStep_from_fourier_inst_of_radius
      btraj ftraj unitShellRadiusSqTrajectory ν (9 / 4 : ℝ)
      hS hE hA hP h0 hXiR uniform_unitShellRadiusSq_control hD

/-- Unit-shell version of
    `uniform_eventually_nonincreasing_front_from_fourier_inst_of_radius`. -/
theorem uniform_eventually_nonincreasing_front_from_fourier_inst_of_unit_shell
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (9 / 4 : ℝ))
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    UniformEventuallyNonincreasingFront btraj := by
  exact
    uniform_eventually_nonincreasing_front_from_fourier_inst_of_radius
      btraj ftraj unitShellRadiusSqTrajectory ν (9 / 4 : ℝ)
      hS hE hA hP h0 hXiR uniform_unitShellRadiusSq_control hD

/-- Unit-shell version of
    `pointwise_eventually_constant_from_uniform_fourier_inst_of_radius`. -/
theorem pointwise_eventually_constant_from_uniform_fourier_inst_of_unit_shell
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (9 / 4 : ℝ))
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ m N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) = m := by
  exact
    pointwise_eventually_constant_from_uniform_fourier_inst_of_radius
      btraj ftraj unitShellRadiusSqTrajectory ν (9 / 4 : ℝ)
      hS hE hA hP h0 hXiR uniform_unitShellRadiusSq_control hD

/-- Unit-shell version of
    `pointwise_eventually_bounded_from_uniform_fourier_inst_of_radius`. -/
theorem pointwise_eventually_bounded_from_uniform_fourier_inst_of_unit_shell
    (btraj : BudgetTrajectoryFamily)
    (ftraj : FourierTrajectoryFamily)
    (ν : ℝ)
    (hS : UniformStrainSupNonneg ftraj)
    (hE : UniformShellEnergyNonneg ftraj)
    (hA : UniformBarrierThreshold btraj ftraj ν (9 / 4 : ℝ))
    (hP : UniformProductionFromStrainSup btraj ftraj)
    (h0 : UniformZeroShellVorticity ftraj)
    (hXiR : UniformVorticityControlledByRadiusSq ftraj unitShellRadiusSqTrajectory)
    (hD : UniformDissipationFromEnergy btraj ftraj ν) :
    ∀ K_max, ∃ M N : ℕ, ∀ n, N ≤ n → jumpFront ((btraj K_max) n) ≤ M := by
  exact
    pointwise_eventually_bounded_from_uniform_fourier_inst_of_radius
      btraj ftraj unitShellRadiusSqTrajectory ν (9 / 4 : ℝ)
      hS hE hA hP h0 hXiR uniform_unitShellRadiusSq_control hD

#check @uniform_eventually_no_corridorStep_from_fourier_inst_of_unit_shell
#check @uniform_eventually_nonincreasing_front_from_fourier_inst_of_unit_shell
#check @pointwise_eventually_constant_from_uniform_fourier_inst_of_unit_shell
#check @pointwise_eventually_bounded_from_uniform_fourier_inst_of_unit_shell

end NSUniformA2Bridge
