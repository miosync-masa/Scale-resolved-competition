import NSBarrier.NSGalerkinCoeffODEActual
import Mathlib.Tactic

namespace NSGalerkinCoeffIntegratedProof

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSIntegratedHinc
open NSGalerkinHinc
open NSGalerkinEnstrophyIdentity
open NSGalerkinShellStepIdentity
open NSGalerkinODEActual
open NSGalerkinCoeffODEActual

/-
  Goal of this file:
  reduce the last continuous-time Galerkin input

    Xi(t_{n+1},k) - Xi(t_n,k) = Δt * (Pavg - Davg)

  to an even more primitive pair of statements:

    Xi(t_{n+1},k) - Xi(t_n,k) = Pint - Dint
    Pint = Δt * Pavg,   Dint = Δt * Davg

  where Pint and Dint are the genuinely integrated shellwise production
  and dissipation over a time slab.
-/

-- ============================================================
-- SECTION 1: PRIMITIVE INTEGRATED SHELL DATA
-- ============================================================

/-- Primitive integrated Galerkin shell data.

`Pint` and `Dint` are the integrated shellwise production / dissipation
over one time slab; `Pavg` and `Davg` are the corresponding step-averaged
quantities, related by multiplication by `Δt`.

The key exact identity is then
  Xi(t_{n+1},k) - Xi(t_n,k) = Pint(n,k) - Dint(n,k).
-/
structure GalerkinCoeffIntegratedProofData (K_max : ℕ) where
  Δt : ℝ
  hΔt : 0 ≤ Δt

  XiCont : ℝ → Fin K_max → ℝ

  Pint : ℕ → Fin K_max → ℝ
  Dint : ℕ → Fin K_max → ℝ

  Pavg : ℕ → Fin K_max → ℝ
  Davg : ℕ → Fin K_max → ℝ
  hDavg_nonneg : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Davg n k

  time : ℕ → ℝ
  htime_zero : time 0 = 0
  htime_succ : ∀ n : ℕ, time (n + 1) = time n + Δt

  /-- Exact integrated shellwise identity. -/
  hXi_interval_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      XiCont (time (n + 1)) k - XiCont (time n) k
        =
      Pint n k - Dint n k

  /-- Integrated production equals `Δt` times the step average. -/
  hPint_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Pint n k = Δt * Pavg n k

  /-- Integrated dissipation equals `Δt` times the step average. -/
  hDint_eq :
    ∀ n : ℕ, ∀ k : Fin K_max,
      Dint n k = Δt * Davg n k

#check @GalerkinCoeffIntegratedProofData

-- ============================================================
-- SECTION 2: THE KEY ALGEBRAIC REDUCTION
-- ============================================================

/-- From the primitive integrated identity plus the average relations,
one gets the exact shellwise step identity in the form required by
`NSGalerkinCoeffODEActual`. -/
theorem hXi_integrated_of_interval_data
    {K_max : ℕ}
    (gid : GalerkinCoeffIntegratedProofData K_max) :
    ∀ n : ℕ, ∀ k : Fin K_max,
      gid.XiCont (gid.time (n + 1)) k - gid.XiCont (gid.time n) k
        =
      gid.Δt * (gid.Pavg n k - gid.Davg n k) := by
  intro n k
  calc
    gid.XiCont (gid.time (n + 1)) k - gid.XiCont (gid.time n) k
      =
    gid.Pint n k - gid.Dint n k := gid.hXi_interval_eq n k
    _ =
    gid.Δt * gid.Pavg n k - gid.Δt * gid.Davg n k := by
      rw [gid.hPint_eq n k, gid.hDint_eq n k]
    _ =
    gid.Δt * (gid.Pavg n k - gid.Davg n k) := by ring

#check @hXi_integrated_of_interval_data

-- ============================================================
-- SECTION 3: BRIDGE TO NSGalerkinCoeffODEActual
-- ============================================================

/-- The primitive integrated proof data induce the previous
`GalerkinCoeffODEContData`. -/
noncomputable def toGalerkinCoeffODEContData
    {K_max : ℕ}
    (gid : GalerkinCoeffIntegratedProofData K_max) :
    GalerkinCoeffODEContData K_max where
  Δt := gid.Δt
  hΔt := gid.hΔt
  XiCont := gid.XiCont
  PCont := fun _t k => gid.Pavg 0 k
  DCont := fun _t k => gid.Davg 0 k
  Pavg := gid.Pavg
  Davg := gid.Davg
  hDavg_nonneg := gid.hDavg_nonneg
  time := gid.time
  htime_zero := gid.htime_zero
  htime_succ := gid.htime_succ
  hXi_integrated := hXi_integrated_of_interval_data gid

#check @toGalerkinCoeffODEContData

/-
  Note:
  `PCont` and `DCont` are placeholders here because the downstream file
  `NSGalerkinCoeffODEActual` only uses `Pavg`, `Davg`, `XiCont`, and
  `hXi_integrated`.  When the actual interval-integral realization is supplied,
  these can be replaced by the genuine continuous-time shellwise production
  and dissipation fields.
-/

-- ============================================================
-- SECTION 4: FINAL CONSEQUENCES
-- ============================================================

/-- Therefore the primitive integrated Galerkin shell identity already yields the
conditional discrete Grönwall theorem with a fixed cutoff. -/
theorem eventual_discrete_gronwall_of_integrated_proof_cutoff
    {K_max : ℕ}
    (gid : GalerkinCoeffIntegratedProofData K_max)
    (M C : ℝ) (Ncut : ℕ)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).P k
              ≤
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).P k
              ≤
            M * (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy (XiDiscrete (toGalerkinCoeffODEContData gid)) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy (XiDiscrete (toGalerkinCoeffODEContData gid)) (N0 + m)
          ≤
        (1 + M * C) ^ m
          * shellTotalEnstrophy (XiDiscrete (toGalerkinCoeffODEContData gid)) N0 := by
  exact
    eventual_discrete_gronwall_of_continuous_coeffODE_cutoff
      (toGalerkinCoeffODEContData gid)
      M C Ncut
      hM hMC
      htail hratio hDiss_gal

/-- Barrier-specialized version. -/
theorem eventual_discrete_gronwall_of_integrated_proof_barrier_fixed_cutoff
    {K_max : ℕ}
    (gid : GalerkinCoeffIntegratedProofData K_max)
    (Φ ν M C : ℝ) (Ncut : ℕ)
    (hν : 0 < ν)
    (hM : 0 ≤ M)
    (hMC : 0 ≤ M * C)
    (hbar :
      ∃ Nb : ℕ,
        ∀ n : ℕ, Nb ≤ n →
          ∀ k : Fin K_max,
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).D k
              <
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).P k →
            Φ ≤ k4Cost ν k.val → False)
    (htail :
      ∃ Nt : ℕ,
        ∀ n : ℕ, Nt ≤ n →
          ∀ k : Fin K_max,
            Ncut ≤ k.val →
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).P k
              ≤
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).D k)
    (hratio :
      ∃ Nr : ℕ,
        ∀ n : ℕ, Nr ≤ n →
          ∀ k : Fin K_max,
            k.val < Ncut →
            (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).P k
              ≤
            M * (instBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n).D k)
    (hDiss_gal :
      ∃ Nd : ℕ,
        ∀ n : ℕ, Nd ≤ n →
          shellDissipationSource
            (intBudgetTrajectory (toGalerkinODEStepData (toGalerkinCoeffODEContData gid)) n)
            (lowShells (K_max := K_max) Ncut)
              ≤
          C * shellTotalEnstrophy (XiDiscrete (toGalerkinCoeffODEContData gid)) n) :
    ∃ N0 : ℕ,
      ∀ m : ℕ,
        shellTotalEnstrophy (XiDiscrete (toGalerkinCoeffODEContData gid)) (N0 + m)
          ≤
        (1 + M * C) ^ m
          * shellTotalEnstrophy (XiDiscrete (toGalerkinCoeffODEContData gid)) N0 := by
  exact
    eventual_discrete_gronwall_of_continuous_coeffODE_barrier_fixed_cutoff
      (toGalerkinCoeffODEContData gid)
      Φ ν M C Ncut
      hν hM hMC
      hbar htail hratio hDiss_gal

#check @eventual_discrete_gronwall_of_integrated_proof_cutoff
#check @eventual_discrete_gronwall_of_integrated_proof_barrier_fixed_cutoff

end NSGalerkinCoeffIntegratedProof
