import NSBarrier.NSLowShellLocalClosureActual
import Mathlib.Tactic

namespace NSLocalPartActual

open NSFiniteSource
open NSFiniteSourceClosure
open NSFiniteSourceTrajectory
open NSFiniteSourceConditionalGronwall
open NSFiniteBandClosure
open NSFiniteBandEnergy
open NSLowShellTriadLocality
open NSTriadGeometryOffset
open NSUnitWidthTriadGeometry
open NSUnitWidthEuclideanRadius
open NSLowShellLocalClosureActual

/-- True Navier–Stokes local-part data, reduced to the final analytic input
`hloc` for the actual unit-width Fourier shell geometry.

At this stage, all geometric / shell-support bookkeeping is already solved.
What remains is only the actual local closure:
  P_loc(k) ≤ F(E_<N) D_k
for low output shells. -/
structure ActualLocalPartData (K_max : ℕ) where
  traj : BudgetTrajectory K_max
  E : EnstrophyTrajectory
  Eshell : ShellEnergyTrajectory K_max
  supportData : ActualUnitWidthSupportExclusionData K_max

  F : ℝ → ℝ
  C : ℝ

  hC : 0 ≤ C
  hFmono : Monotone F
  hFnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x

  /-- Nonnegativity of the shell energies. -/
  hEn : ∀ n : ℕ, ∀ k : Fin K_max, 0 ≤ Eshell n k

  /-- One-step enstrophy increment is controlled by the total shell net source. -/
  hinc :
    ∀ n : ℕ, E (n + 1) - E n ≤ shellNetSource (traj n) Finset.univ

  /-- High shells are eventually dissipative. -/
  htail :
    ∃ Nt : ℕ,
      ∀ n : ℕ, Nt ≤ n →
        ∀ k : Fin K_max, supportData.Ncut ≤ k.val → (traj n).P k ≤ (traj n).D k

  /-- Actual production split into local and tail parts. -/
  hdecomp :
    ∀ n : ℕ, ∀ k : Fin K_max,
      (traj n).P k =
        supportData.split.P_loc n k + supportData.split.P_tail n k

  /-- The last analytic input:
      the true Navier–Stokes local part is controlled by the low-shell energy. -/
  hloc :
    ∀ n : ℕ, ∀ k : Fin K_max,
      k.val < supportData.Ncut →
        supportData.split.P_loc n k
          ≤ F (lowShellEnergy Eshell supportData.Ncut n) * (traj n).D k

  /-- Low-shell dissipation is eventually controlled by `C * E(n)`. -/
  hDiss :
    ∃ Nd : ℕ,
      ∀ n : ℕ, Nd ≤ n →
        shellDissipationSource (traj n)
          (lowShells (K_max := K_max) supportData.Ncut) ≤ C * E n

  /-- Total shell energy is eventually bounded. -/
  hEtot :
    ∃ Ns : ℕ, ∃ B : ℝ,
      ∀ n : ℕ, Ns ≤ n → totalShellEnergy Eshell n ≤ B

#check @ActualLocalPartData

/-- Therefore the true Navier–Stokes local-part closure already yields
the conditional discrete Grönwall bound. -/
theorem eventual_discrete_gronwall_of_true_local_part
    {K_max : ℕ}
    (ns : ActualLocalPartData K_max) :
    ∃ N0 : ℕ, ∃ B : ℝ,
      0 ≤ ns.F B ∧
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + ns.F B * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_actual_unitWidth_geometry
      ns.traj ns.E ns.Eshell ns.supportData ns.F ns.C
      ns.hC ns.hFmono ns.hFnonneg ns.hEn
      ns.hinc ns.htail ns.hdecomp ns.hloc ns.hDiss ns.hEtot

#check @eventual_discrete_gronwall_of_true_local_part

/-- Uniform-ratio corollary:
    if the closure function `F` is uniformly bounded by a constant `M`
    on the relevant energy range, then one gets a fixed-ratio exponential bound. -/
theorem eventual_discrete_gronwall_of_uniform_true_local_part
    {K_max : ℕ}
    (ns : ActualLocalPartData K_max)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hFM : ∀ x : ℝ, 0 ≤ x → ns.F x ≤ M) :
    ∃ N0 : ℕ,
      ∀ m : ℕ, ns.E (N0 + m) ≤ (1 + M * ns.C) ^ m * ns.E N0 := by
  exact
    eventual_discrete_gronwall_of_uniform_actual_unitWidth_geometry
      ns.traj ns.E ns.Eshell ns.supportData ns.F M ns.C
      hM ns.hC hFM ns.hEn
      ns.hinc ns.htail ns.hdecomp ns.hloc ns.hDiss ns.hEtot

#check @eventual_discrete_gronwall_of_uniform_true_local_part

end NSLocalPartActual
