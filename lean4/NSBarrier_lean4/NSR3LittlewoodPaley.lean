import NSBarrier.NSR3ShellActual
import NSBarrier.NSTorusShell
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory
open NSTorusShell

namespace NSR3LittlewoodPaley

open NSR3ShellActual

-- As in the torus branch, we use the real inner-product structure on a complex
-- `L²` space when feeding projector families into the abstract barrier chain.
noncomputable instance : InnerProductSpace ℝ L2R3 :=
  InnerProductSpace.rclikeToReal ℂ L2R3

/-- The canonical dyadic shell indexed by `k < K_max`. -/
def shellRegion {K_max : ℕ} (k : Fin K_max) : Set Frequency :=
  dyadicAnnulus k.val

/-- The canonical low-frequency cutoff `|ξ| ≤ 2^Ncut`. -/
def lowFrequencyCutoff (Ncut : ℕ) : Set Frequency :=
  lowBall ((2 : ℝ) ^ Ncut)

/-- The canonical high-frequency tail `2^Ncut ≤ |ξ|`. -/
def highFrequencyTail (Ncut : ℕ) : Set Frequency :=
  {ξ : Frequency | (2 : ℝ) ^ Ncut ≤ ‖ξ‖}

/-- The low/high decomposition attached to the Euclidean cutoff. -/
theorem mem_lowFrequencyCutoff_iff
    {Ncut : ℕ} {ξ : Frequency} :
    ξ ∈ lowFrequencyCutoff Ncut ↔ ‖ξ‖ ≤ (2 : ℝ) ^ Ncut := by
  rfl

/-- Unfolded membership in the Euclidean high-frequency tail. -/
theorem mem_highFrequencyTail_iff
    {Ncut : ℕ} {ξ : Frequency} :
    ξ ∈ highFrequencyTail Ncut ↔ (2 : ℝ) ^ Ncut ≤ ‖ξ‖ := by
  rfl

/-- Each canonical shell lies below the next dyadic cutoff. -/
theorem shellRegion_subset_lowFrequencyCutoff_succ
    {K_max : ℕ} (k : Fin K_max) :
    shellRegion k ⊆ lowFrequencyCutoff (k.val + 1) := by
  simpa [shellRegion, lowFrequencyCutoff] using
    dyadicAnnulus_subset_lowBall_succ k.val

/-- Dyadic shells sit inside the corresponding high-frequency tail. -/
theorem shellRegion_subset_highFrequencyTail
    {K_max : ℕ} (k : Fin K_max) :
    shellRegion k ⊆ highFrequencyTail k.val := by
  intro ξ hξ
  exact (mem_dyadicAnnulus_iff.mp hξ).1

/-- Continuous-frequency Littlewood-Paley data on `L²(R³)`:
an abstract projector family together with the canonical dyadic shell geometry
that will later be tied to Fourier multipliers. -/
structure R3LittlewoodPaleyData (K_max : ℕ) where
  projData : ShellProjectorData L2R3 K_max
  shellSet : Fin K_max → Set Frequency
  shellSet_eq : ∀ k : Fin K_max, shellSet k = shellRegion k
  lowCutoff : ℕ → Set Frequency
  lowCutoff_eq : ∀ Ncut : ℕ, lowCutoff Ncut = lowFrequencyCutoff Ncut

/-- Equip any abstract `L²(R³)` projector family with the canonical Euclidean
dyadic shell geometry. -/
def withCanonicalCutoffs
    {K_max : ℕ}
    (projData : ShellProjectorData L2R3 K_max) :
    R3LittlewoodPaleyData K_max where
  projData := projData
  shellSet := shellRegion
  shellSet_eq := fun _ => rfl
  lowCutoff := lowFrequencyCutoff
  lowCutoff_eq := fun _ => rfl

/-- C2 theorem: once an abstract projector family on `L²(R³)` is fixed, the
Euclidean branch carries a canonical Littlewood-Paley shell/cutoff geometry
given by dyadic annuli and dyadic low-frequency balls. -/
theorem R3_shell_projectors_and_cutoffs
    {K_max : ℕ}
    (projData : ShellProjectorData L2R3 K_max) :
    ∃ lp : R3LittlewoodPaleyData K_max,
      lp.projData = projData ∧
      (∀ k : Fin K_max, lp.shellSet k = dyadicAnnulus k.val) ∧
      (∀ Ncut : ℕ, lp.lowCutoff Ncut = lowBall ((2 : ℝ) ^ Ncut)) := by
  refine ⟨withCanonicalCutoffs projData, rfl, ?_, ?_⟩
  · intro k
    rfl
  · intro Ncut
    rfl

end NSR3LittlewoodPaley
