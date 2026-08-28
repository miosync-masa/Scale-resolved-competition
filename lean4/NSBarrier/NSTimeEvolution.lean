/-
  NSTimeEvolution.lean  —  凍結用ステートメントファイル (Statement-first, proofs deferred)

  ## 目的
  「ブローアップするか否か」を非空虚な命題として書けるようにする。

  ## 設計規則（既存階層との決定的な差）
  1. 非線形項は `structure` のフィールドではなく `def` である。
     旧: `nonlin : ℝ → Mode → ℝ`  ← 任意の関数が入る ⇒ NS を固定していない
     新: `nsRHS ν M a κ`          ← NS の右辺そのもの ⇒ 差し替え不能
  2. 「解」は時刻の関数 `a : ℝ → Mode → Vec` であり、
     定義済みベクトル場に対する `HasDerivAt` で拘束される。
  3. 「ブローアップしない」は最大存在時刻 `Tstar = ⊤` で表す。
     `∀ t, ∃ B, E t ≤ B` の形は使わない（下記 SECTION 5 参照：恒真）。
  4. 証明は `sorry`。ステートメントが凍結されるまで証明は書かない。
     詰まっても **ステートメントを弱めない**。

  ## ビルド
  このファイルは意図的に `NSBarrier.lean` から import していない（CI を汚さないため）。
  単体で:  lake env lean NSBarrier/NSTimeEvolution.lean
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

open scoped ENNReal

namespace NSTimeEvolution

-- ============================================================
-- SECTION 1: フーリエ係数空間（超関数論を一切使わない）
-- ============================================================

/-- `T³ = (ℝ/ℤ)³` 上のフーリエモード。 -/
abbrev Mode := Fin 3 → ℤ

/-- 各モードの複素ベクトル振幅 `ℂ³`。 -/
abbrev Vec := Fin 3 → ℂ

/-- モード `κ` の複素ベクトルとしての実現。 -/
def modeC (κ : Mode) : Vec := fun i => (κ i : ℂ)

/-- 双線形（共役なし）内積。 -/
def dot (v w : Vec) : ℂ := ∑ i, v i * w i

/-- Hermite 内積 `⟪v, w⟫ = Σ conj(vᵢ) wᵢ`。 -/
def herm (v w : Vec) : ℂ := ∑ i, (starRingEnd ℂ) (v i) * w i

/-- `‖κ‖²`（整数格子上の二乗長）。 -/
def sqLen (κ : Mode) : ℝ := ∑ i, ((κ i : ℝ)) ^ 2

/-- モードごとの Leray 射影 `P_κ v = v - (κ·v)κ/‖κ‖²`。
`κ = 0` では恒等。R³ の Leray 射影と違い、これは 3×3 行列で完全に書ける。 -/
noncomputable def leray (κ : Mode) (v : Vec) : Vec :=
  if κ = 0 then v
  else fun i => v i - (dot (modeC κ) v / (sqLen κ : ℂ)) * (κ i : ℂ)

/-- 非圧縮条件（モードごと）。 -/
def DivFree (a : Mode → Vec) : Prop := ∀ κ, dot (modeC κ) (a κ) = 0

/-- 実数値速度場に対応する実在条件 `û₍₋κ₎ = conj û_κ`。 -/
def RealField (a : Mode → Vec) : Prop :=
  ∀ κ i, a (-κ) i = (starRingEnd ℂ) (a κ i)

/-- 有限モード集合 `M` 外で消えている（Galerkin 切断）。 -/
def SupportedOn (M : Finset Mode) (a : Mode → Vec) : Prop := ∀ κ ∉ M, a κ = 0

-- ============================================================
-- SECTION 2: Navier–Stokes の右辺（★これが def であることが要点）
-- ============================================================

/-- 移流項 `(u·∇)u` のフーリエ係数（`2πi` の因子は外に出してある）:
`Σ_{p+q=κ} (û_p · q) û_q`。`a` が `M` 上に台を持つ前提で `q = κ - p` と解いてある。 -/
noncomputable def convol (M : Finset Mode) (a : Mode → Vec) (κ : Mode) : Vec :=
  fun i => ∑ p ∈ M, dot (a p) (modeC (κ - p)) * a (κ - p) i

/-- 線形（粘性）項 `-ν(2π‖κ‖)² û_κ`。 -/
noncomputable def linearPart (ν : ℝ) (a : Mode → Vec) (κ : Mode) : Vec :=
  fun i => -((4 * Real.pi ^ 2 * ν * sqLen κ : ℝ) : ℂ) * a κ i

/-- 非線形項 `-2πi P_κ[ Σ_{p+q=κ} (û_p·q) û_q ]`。 -/
noncomputable def nonlinearPart (M : Finset Mode) (a : Mode → Vec) (κ : Mode) : Vec :=
  fun i => -(2 * (Real.pi : ℂ) * Complex.I) * leray κ (convol M a κ) i

/-- **Galerkin 切断された 3D Navier–Stokes のベクトル場**。
`M` は有限なので、これは `ℂ^(3|M|)` 上の多項式写像（2次）である。 -/
noncomputable def nsRHS (ν : ℝ) (M : Finset Mode) (a : Mode → Vec) (κ : Mode) : Vec :=
  fun i => linearPart ν a κ i + nonlinearPart M a κ i

-- ============================================================
-- SECTION 3: 解の定義（時間発展）
-- ============================================================

/-- 区間 `[0, T)` 上の Galerkin 解。

各フィールドは `a` を **定義済みの** `nsRHS` に対して拘束する。
`nsRHS` は差し替えられないので、この述語は空虚に充足できない。 -/
structure IsGalerkinSolutionOn (ν : ℝ) (M : Finset Mode) (T : ℝ)
    (a : ℝ → Mode → Vec) : Prop where
  support : ∀ t, SupportedOn M (a t)
  divFree : ∀ t, DivFree (a t)
  realField : ∀ t, RealField (a t)
  contOn : ContinuousOn a (Set.Icc 0 T)
  evolves : ∀ t ∈ Set.Ioo 0 T, ∀ κ : Mode, ∀ i : Fin 3,
      HasDerivAt (fun s => a s κ i) (nsRHS ν M (a t) κ i) t

/-- 初期値 `a₀` から `[0, T)` 上に解が存在する。 -/
def SolvesOn (ν : ℝ) (M : Finset Mode) (a₀ : Mode → Vec) (T : ℝ) : Prop :=
  ∃ a : ℝ → Mode → Vec, a 0 = a₀ ∧ IsGalerkinSolutionOn ν M T a

-- ============================================================
-- SECTION 4: 最大存在時刻とブローアップ（★ここが本題）
-- ============================================================

/-- **最大存在時刻** `T* = sup { T : [0,T) 上に解が存在 }`。

これが定義できて初めて「有限時間ブローアップ」が命題になる。
旧階層にはこの量が存在しなかった。 -/
noncomputable def Tstar (ν : ℝ) (M : Finset Mode) (a₀ : Mode → Vec) : ℝ≥0∞ :=
  ⨆ (T : ℝ) (_ : SolvesOn ν M a₀ T), ENNReal.ofReal T

/-- **有限時間ブローアップ**。 -/
def BlowsUp (ν : ℝ) (M : Finset Mode) (a₀ : Mode → Vec) : Prop :=
  Tstar ν M a₀ < ⊤

/-- **大域正則性**。`¬ BlowsUp` と同値であるべき（SECTION 6 の目標定理）。 -/
def GloballyRegular (ν : ℝ) (M : Finset Mode) (a₀ : Mode → Vec) : Prop :=
  Tstar ν M a₀ = ⊤

/-- エネルギー `E = Σ_κ ‖û_κ‖²`。 -/
noncomputable def energy (M : Finset Mode) (a : Mode → Vec) : ℝ :=
  ∑ κ ∈ M, ∑ i, Complex.normSq (a κ i)

/-- エンストロフィ `Ω = Σ_κ (2π‖κ‖)² ‖û_κ‖²`。 -/
noncomputable def enstrophy (M : Finset Mode) (a : Mode → Vec) : ℝ :=
  ∑ κ ∈ M, (4 * Real.pi ^ 2 * sqLen κ) * ∑ i, Complex.normSq (a κ i)

/-- **一様有界性**（`B` が `t` に依存しない）。これが「爆発しない」の正しい形。 -/
def UniformlyBoundedOn (E : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ B : ℝ, ∀ t ∈ Set.Ico 0 T, E t ≤ B

-- ============================================================
-- SECTION 5: 負のコントロール（★ sorry なし。ここは必ず通る）
-- ============================================================

/-- **旧 `no_finite_time_blowup` の結論は、仮説を全部消しても証明できる。**

`NSBarrier/NSNoBlowupMaster.lean:89` の結論と字句的に同一。
Gronwall 仮説・`M`・`C`・`E0` は一切使っていない。 -/
theorem discrete_pointwise_bound_is_vacuous (E : ℕ → ℝ) :
    ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ E n ≤ B :=
  fun n => ⟨max 0 (E n), le_max_left _ _, le_max_right _ _⟩

/-- 連続時間版も同様に恒真。 -/
theorem pointwise_bound_is_vacuous (E : ℝ → ℝ) :
    ∀ t : ℝ, ∃ B : ℝ, 0 ≤ B ∧ E t ≤ B :=
  fun t => ⟨max 0 (E t), le_max_left _ _, le_max_right _ _⟩

/-- 対照群: **明らかに非有界な列** でも旧形式は成立してしまう。 -/
example : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ((n : ℝ)) ≤ B :=
  discrete_pointwise_bound_is_vacuous (fun n => (n : ℝ))

/-- 一方、正しい形（`∃B ∀n`）は同じ列を正しく棄却する。 -/
example : ¬ ∃ B : ℝ, ∀ n : ℕ, ((n : ℝ)) ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact absurd (hB n) (not_le.mpr hn)

/-- 量化子の順序が本質。`∀∃` から `∃∀` は出ない。 -/
theorem pointwise_not_implies_uniform :
    ¬ ∀ E : ℕ → ℝ, (∀ n, ∃ B : ℝ, 0 ≤ B ∧ E n ≤ B) → ∃ B : ℝ, ∀ n, E n ≤ B := by
  intro h
  obtain ⟨B, hB⟩ := h (fun n => (n : ℝ)) (discrete_pointwise_bound_is_vacuous _)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact absurd (hB n) (not_le.mpr hn)

-- ============================================================
-- SECTION 6: 目標定理（凍結対象。証明はまだ書かない）
-- ============================================================

/-- **目標 1（本丸）**: Galerkin 非線形項はエネルギーを生成しない。
`⟪a, -2πi P B(a,a)⟫` の実部が消える。有限和の代数的恒等式であり、
非圧縮性・実在条件・`p+q=κ` の対称性のみから従う。 -/
theorem nonlinear_energy_neutral
    (M : Finset Mode) (a : Mode → Vec)
    (hsupp : SupportedOn M a) (hdiv : DivFree a) (hreal : RealField a) :
    (∑ κ ∈ M, herm (a κ) (nonlinearPart M a κ)).re = 0 := by
  sorry

/-- **目標 2**: エネルギー恒等式 `dE/dt = -2ν Ω`。目標 1 から従う。 -/
theorem energy_hasDerivAt
    (ν : ℝ) (M : Finset Mode) (T : ℝ) (a : ℝ → Mode → Vec)
    (h : IsGalerkinSolutionOn ν M T a) (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun s => energy M (a s)) (-2 * ν * enstrophy M (a t)) t := by
  sorry

/-- **目標 3**: 事前評価。エネルギーは初期値で一様に押さえられる。 -/
theorem energy_uniformly_bounded
    (ν : ℝ) (hν : 0 ≤ ν) (M : Finset Mode) (T : ℝ) (a : ℝ → Mode → Vec)
    (h : IsGalerkinSolutionOn ν M T a) :
    UniformlyBoundedOn (fun t => energy M (a t)) T := by
  sorry

/-- **目標 4**: Galerkin 切断は大域可解（`T* = ⊤`）。
局所存在（Picard–Lindelöf：`nsRHS` は有限次元上の 2 次多項式ゆえ局所 Lipschitz）
＋ 目標 3 の事前評価による継続。 -/
theorem galerkin_globally_regular
    (ν : ℝ) (hν : 0 < ν) (M : Finset Mode) (a₀ : Mode → Vec)
    (hsupp : SupportedOn M a₀) (hdiv : DivFree a₀) (hreal : RealField a₀) :
    GloballyRegular ν M a₀ := by
  sorry

/-- **目標 5**: 上と同値な形での「有限時間ブローアップは起きない」。
目標 4 の直接の言い換えだが、`BlowsUp` を明示的に否定する形を残しておく。 -/
theorem galerkin_no_finite_time_blowup
    (ν : ℝ) (hν : 0 < ν) (M : Finset Mode) (a₀ : Mode → Vec)
    (hsupp : SupportedOn M a₀) (hdiv : DivFree a₀) (hreal : RealField a₀) :
    ¬ BlowsUp ν M a₀ := by
  sorry

-- ============================================================
-- SECTION 7: この先（Galerkin を越える部分。まだ書かない）
-- ============================================================

/-
  上の目標 1–5 は Mathlib の欠落ゼロで到達できる（有限次元 ODE のみ）。
  ミレニアム問題本体に必要なのは、ここから先:

  (a) `K_max → ∞` の一様評価: 目標 3 の `B` が `M` に依存しないこと。
      ← これが真のフロンティア。旧階層の `hF_Kmax_independent : True` の中身。
  (b) Hˢ(T³) を重み付き ℓ²（Σ (1+‖κ‖²)ˢ‖û_κ‖² < ∞）として定義。
  (c) 熱半群を対角乗数 e^{-4π²ν‖κ‖²t} として定義し、Duhamel の不動点で局所解。
  (d) `Tstar` を PDE 版に持ち上げ、BKM 型の継続条件を証明。

  (a) を書く前に (a) のステートメントだけ先に凍結すること。
-/

end NSTimeEvolution
