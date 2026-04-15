import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open scoped ENNReal
open scoped BigOperators

namespace NSTorusShellActual

/-- The 3-torus `(ℝ / ℤ)^3`. -/
abbrev T3 := UnitAddTorus (Fin 3)

/-- Fourier modes on `T³`. -/
abbrev Mode := Fin 3 → ℤ

/-- Scalar complex `L²(T³)`. -/
noncomputable abbrev L2T3 :=
  MeasureTheory.Lp ℂ (2 : ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure T3)

/-- The actual Fourier `L²` basis vector at mode `κ`. -/
noncomputable abbrev basisVec (κ : Mode) : L2T3 :=
  ContinuousMap.toLp (E := ℂ) 2 MeasureTheory.volume ℂ (UnitAddTorus.mFourier κ)

/-- The image of a finite mode set under `basisVec`. -/
noncomputable def shellBasisSet (M : Finset Mode) : Set L2T3 :=
  basisVec '' (↑M : Set Mode)

/-- The shell subspace spanned by the basis vectors in `M`. -/
noncomputable def shellSubspace (M : Finset Mode) : Submodule ℂ L2T3 :=
  Submodule.span ℂ (shellBasisSet M)

/-- The actual shell projector onto the shell subspace. -/
noncomputable def shellProj (M : Finset Mode)
    [(shellSubspace M).HasOrthogonalProjection] :
    L2T3 →L[ℂ] L2T3 :=
  (shellSubspace M).starProjection

/-- Contraction of the actual shell projector. -/
theorem shellProj_apply_norm_le (M : Finset Mode)
    [(shellSubspace M).HasOrthogonalProjection]
    (f : L2T3) :
    ‖shellProj M f‖ ≤ ‖f‖ := by
  simpa [shellProj] using (shellSubspace M).norm_starProjection_apply_le f

/-- A family of finite mode sets, one for each shell index below `K_max`. -/
def ModeFamily (K_max : ℕ) := Fin K_max → Finset Mode

/-- The corresponding family of actual shell projectors. -/
noncomputable def shellProjFamily {K_max : ℕ} (modes : ModeFamily K_max)
    [∀ k : Fin K_max, (shellSubspace (modes k)).HasOrthogonalProjection] :
    Fin K_max → (L2T3 →L[ℂ] L2T3) :=
  fun k => shellProj (modes k)

/-- Each actual shell projector in the family is contractive. -/
theorem shellProjFamily_contraction {K_max : ℕ} (modes : ModeFamily K_max)
    [∀ k : Fin K_max, (shellSubspace (modes k)).HasOrthogonalProjection]
    (k : Fin K_max) (f : L2T3) :
    ‖shellProjFamily modes k f‖ ≤ ‖f‖ := by
  exact shellProj_apply_norm_le (modes k) f

#check @basisVec
#check @shellBasisSet
#check @shellSubspace
#check @shellProj
#check @shellProj_apply_norm_le
#check @shellProjFamily
#check @shellProjFamily_contraction

end NSTorusShellActual
