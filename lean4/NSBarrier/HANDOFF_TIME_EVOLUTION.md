# 引き継ぎ: 時間発展層 (NSTimeEvolution.lean)

対象ブランチ: `claude/navier-stokes-time-evolution-xm2p1s`
PR: https://github.com/miosync-masa/Scale-resolved-competition/pull/1

---

## 0. 最初に読むこと

このドキュメントは、**既存の 25,888 行・1,007 statement の Lean 証明が
「4分岐すべて通ってしまった」原因の診断と、その修復作業の引き継ぎ**である。

作業を始める前に SECTION 3「鉄の規則」を必ず読むこと。
そこを踏み外すと、このリポジトリが陥ったのと同じ失敗を再生産する。

---

## 1. 背景: 何が問題だったか

既存階層は T³/R³ × (大域正則性/反例) の 4 分岐すべてが `sorry` 0・`axiom` 0 で
通っている。**これは成果ではなく症状である。**

### 証拠1: 「ブローアップしない」の結論が恒真式

`NSBarrier/NSNoBlowupMaster.lean:89`

```lean
theorem no_finite_time_blowup (E : ℕ → ℝ) (M C E0 : ℝ) ... :
    ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ E n ≤ B
```

量化子が `∀n ∃B` の順なので `B := max 0 (E n)` で**任意の実数列に対して真**。
発散列でも通る。Gronwall 仮説は本質的に不要。

この事実は `NSTimeEvolution.lean` 内で
`discrete_pointwise_bound_is_vacuous` として**証明済み**（`sorry` なし、CI 検証済み）。
仮説を一つも使わずに同じ結論が出ることが機械的に確認できる。

必要なのは `∃B ∀t ∈ [0, T*)` の順序、かつ `t` は連続時間の
**最大存在区間**上でなければならない。

### 証拠2: 非線形項が structure の自由フィールド

`NSBarrier/NSGalerkinExistenceActual.lean`

```lean
structure ActualFiniteDimensionalGalerkinStateData (K_max m : ℕ) where
  ...
  nonlin : ℝ → Mode → ℝ    -- ← フィールド。任意の関数が入る
```

時間微分 `hstate_hasDeriv` 自体は存在するが、右辺の非線形項が
Navier–Stokes の `P(u·∇u)` として**定義されていない**。
したがってこれは「ある ODE 系」であって「NS の Galerkin 切断」ではない。

### 証拠3: 場が時間の関数でない

`NSBarrier/NSNavierStokesProjectedCore.lean`

```lean
vorticityLp : L2VecT3    -- ℝ → L2VecT3 ではない。スナップショット
```

リポジトリ全体で `curl` / `Laplacian` / `divergence` は一度も定義されていない。

### 証拠4: 全体が閉項を持たない条件文の塔

構造体を返す `def` を全走査した結果:

| | |
|---|---|
| `structure` 定義 | 118 |
| 引数に別の構造体を要求する構成 | ほぼ全部 |
| **閉じた項**（構造体を引数に取らない） | 実質 **2** |

つまり全体が `Data → Data → Data → ...` の変換グラフで、
**根に実物の Navier–Stokes が刺さっていない**。
`exists_torus_breakdown_counterexample` が
「反例データを渡されたら反例を返す」形なのもこれで説明がつく。
A/B（正則性）と C/D（反例）が両立するのは矛盾ではなく、
両方とも前件未充足の条件文だからである。

### 証拠5: フロンティア条件が `True`

`NSBarrier/NSMillenniumFrontier.lean:56`

```lean
hF_Kmax_independent : True
```

コメントで正直に書かれているが、真の未解決部分そのものが `True` になっている。

### 根本原因

目的関数が「ミレニアム問題を解く」ではなく「**Lean を通す**」だった。
そうすると最適解は必然的に「通る形に言明を弱めること」になり、
しかも `lake build` は緑のままなので罰則が働かない。
型検査器が保証するのは「証明 ↔ 言明」の一致だけで、
**「言明 ↔ 意図」は一切見ていない**。

---

## 2. 現状: 何ができているか

`NSBarrier/NSTimeEvolution.lean`（240行）を新規追加。**コンパイル確認済み**。

### 設計上の決定的な差

| | 既存階層 | NSTimeEvolution |
|---|---|---|
| 非線形項 | `nonlin : ℝ → Mode → ℝ`（フィールド、差し替え自由） | `nsRHS`（**def**。NS の右辺そのもの） |
| 場 | `vorticityLp : L2VecT3`（スナップショット） | `a : ℝ → Mode → Vec`（時刻の関数） |
| 「爆発しない」 | ステップごとの各点有界性 | `Tstar = ⊤`（最大存在時刻） |

構造体は使っているが、フィールドはすべて
「`a` を**定義済みの** `nsRHS` に対して縛る」ものであり、
中身を差し替えて空虚に充足する余地がない。

### 定式化: T³ のフーリエ係数空間

**超関数論・Sobolev 空間理論・L²(R³) のフーリエ変換を一切使わない。**
T³ 上では以下がすべて初等的に書ける:

| 対象 | 実装 |
|---|---|
| Leray 射影 | `leray κ v = v - (κ·v)κ/‖κ‖²`（モードごとに 3×3 行列） |
| 移流項 | `convol M a κ = Σ_{p∈M} (û_p · (κ-p)) û_{κ-p}` |
| 粘性項 | `linearPart ν a κ = -4π²ν‖κ‖² û_κ` |
| 熱半群（将来） | 対角乗数 `e^{-4π²ν‖κ‖²t}` |
| Hˢ(T³)（将来） | 重み付き ℓ²: `Σ (1+‖κ‖²)ˢ‖û_κ‖² < ∞` |

有限モード集合 `M` 上では `nsRHS` は `ℂ^(3|M|)` 上の **2次多項式写像**。
局所 Lipschitz なので Mathlib の `IsPicardLindelof` がそのまま使える。

### 通っているもの（`sorry` なし）

- 全定義: `modeC` `dot` `herm` `sqLen` `leray` `convol`
  `linearPart` `nonlinearPart` `nsRHS`
- 全述語: `DivFree` `RealField` `SupportedOn`
  `IsGalerkinSolutionOn` `SolvesOn` `Tstar` `BlowsUp`
  `GloballyRegular` `energy` `enstrophy` `UniformlyBoundedOn`
- 負のコントロール:
  `discrete_pointwise_bound_is_vacuous`
  `pointwise_bound_is_vacuous`
  `pointwise_not_implies_uniform`
  および 2 つの `example`

### `sorry` が残っているもの（= これから証明する対象）

1. `nonlinear_energy_neutral` — **本丸**
2. `energy_hasDerivAt` — `dE/dt = -2νΩ`
3. `energy_uniformly_bounded` — 事前評価
4. `galerkin_globally_regular` — `Tstar = ⊤`
5. `galerkin_no_finite_time_blowup` — `¬ BlowsUp`

### CI

`NSTimeEvolution.lean` は `NSBarrier.lean` から import して**いない**。
`lakefile.toml` の `lean_lib NSBarrier` は globs がデフォルト（`Glob.one NSBarrier`）
なので、`lake build` は `NSBarrier.lean` とその推移的 import しかビルドしない。
したがって `sorry` 5 個を含んでいても既存の 0-sorry CI は緑のまま。
**実測で確認済み**（PR #1 の最初のコミットで CI 通過）。

単体コンパイル:
```bash
cd lean4
lake env lean NSBarrier/NSTimeEvolution.lean
```
期待される出力は `declaration uses 'sorry'` の警告 5 行のみ。

---

## 3. 鉄の規則（★最重要）

### R1. ステートメントを先に凍結し、証明のために弱めない

証明が詰まったとき、**ステートメントを触ってはいけない**。
詰まったこと自体が情報である。
弱める必要が本当にあると判断した場合は、必ず人間に確認を取り、
**なぜ弱めるのかを記録してから**変更する。黙って直さない。

### R2. 仮説を追加するときは必ず申告する

「証明のために仮説を1個足す」は R1 の違反である（結論が弱くなる）。
物理的・数学的に正当な仮説であっても、**追加した事実を明示的に報告する**。
SECTION 6 の「未決定事項」がその例。

### R3. すべての「〜が起きない」定理に負のコントロールを付ける

「X は起きない」と主張する定理を書いたら、
**X が明らかに起きる例を代入して、その言明が破れることを確認する** `example` を
同じファイルに置く。DNS で保存量チェックを走らせるのと同じ。
これがあれば今回の失敗は 5 秒で検出できた。

### R4. 仮説削除テスト

証明を書き終えたら、仮説を一つずつ消してコンパイルしてみる。
消しても通るなら、その仮説は使われていない ＝ 言明が想定より弱い。

### R5. 閉項ゲート

新しい `structure` を導入したら、
「それを引数に構造体を取らずに構成する `def` が存在するか」を必ず問う。
存在しないまま定理を積むと、既存階層と同じ「前件未充足の塔」になる。

### R6. `True` を仮説フィールドに置かない

`hFoo : True` は「まだ書けていない」の婉曲表現であり、
コンパイルは通るが内容はゼロ。書けないなら `sorry` を使うか、
その仮説を明示的に structure から外して定理の外に出す。

---

## 4. ビルドと検証

```bash
# ブランチ
git checkout claude/navier-stokes-time-evolution-xm2p1s

# 単体コンパイル（これがメインループ）
cd lean4
lake env lean NSBarrier/NSTimeEvolution.lean

# 既存階層を壊していないことの確認
lake build

# 特定の定理が何に依存しているか
#   ファイル末尾に一時的に追加して確認する:
#   #print axioms NSTimeEvolution.nonlinear_energy_neutral
```

`lake exe cache get` は Mathlib を再取得する場合のみ。通常は不要。

---

## 5. タスク（優先順）

### T0. 係数規約のレビュー（コード書く前）

`nsRHS` の係数が周期 1・波数 `κ ∈ ℤ³` の規約で正しいか確認する。

前提としている規約:
- `u(x) = Σ_κ û_κ e^{2πi κ·x}`
- `∂_j → 2πi κ_j`
- 粘性項: `-ν(2π|κ|)² û_κ = -4π²ν‖κ‖² û_κ` → `linearPart`
- 移流項: `[(u·∇)u]^_κ = 2πi Σ_{p+q=κ} (û_p·q) û_q`
  → `nonlinearPart` で `-2πi P_κ (convol)`

**ここが間違っていると本丸を証明しても意味がない。**
物理側の目で先に検算すること。

### T1. `nonlinear_energy_neutral` の証明（本丸）

SECTION 6 に証明スケッチあり。有限和の代数的恒等式で、解析は一切不要。

### T2. `energy_hasDerivAt`

T1 ＋ `HasDerivAt` の積の法則。
`energy` は `Complex.normSq` の有限和なので微分は素直。

### T3. `energy_uniformly_bounded`

T2 ＋ `enstrophy ≥ 0` から `E` は単調非増加、よって `B := E 0`。

### T4 / T5. 大域存在

Mathlib の `IsPicardLindelof` で局所解 → T3 の事前評価で継続 → `Tstar = ⊤`。
`nsRHS` は有限次元上の 2 次多項式なので局所 Lipschitz は
`ContDiff` 経由で出せるはず。

### T6（この先。まだ手を付けない）

- `K_max` 一様性: T3 の `B` が `M` に依存しないこと。**これが真のフロンティア**。
  既存階層の `hF_Kmax_independent : True` の中身がこれ。
- Hˢ(T³) を重み付き ℓ² として定義
- 熱半群を対角乗数として定義し、Duhamel の不動点で PDE 局所解
- `Tstar` を PDE 版に持ち上げ、BKM 型継続条件

T6 に進む前に、**T6 のステートメントだけ先に凍結すること**（R1）。

---

## 6. `nonlinear_energy_neutral` 証明スケッチ

目標:
```lean
(∑ κ ∈ M, herm (a κ) (nonlinearPart M a κ)).re = 0
```

### 数学的な筋

記号: `⟪v,w⟫ = Σ_i conj(v_i) w_i`（Hermite）、`v·w = Σ_i v_i w_i`（双線形）。
`N_κ = Σ_{p+q=κ} (û_p·q) û_q`（= `convol`）。

**Step 1. Leray 射影を落とす。**
`P_κ` は Hermite かつ冪等、`û_κ` は div-free なので `P_κ û_κ = û_κ`。よって
```
⟪û_κ, P_κ N_κ⟫ = ⟪P_κ û_κ, N_κ⟫ = ⟪û_κ, N_κ⟫
```
以降 `P` は消えて、`S := Σ_κ ⟪û_κ, N_κ⟫` を扱えばよい。

**Step 2. 実在条件で共役を消す。**
`conj(û_κ) = û_{-κ}` より
```
S = Σ_{p,q} (û_p·q) (û_{-(p+q)} · û_q)
```
（右辺の `·` はすべて共役なしの双線形内積）

**Step 3. 三つ組に書き換える。**
`r := -(p+q)` とおくと `p+q+r = 0` で
```
S = Σ_{p+q+r=0} (û_p·q)(û_r·û_q)
```

**Step 4. `q ↔ r` で対称化する。**
和は `p+q+r=0` について対称なので、`q` と `r` を入れ替えても同じ値:
```
S = Σ_{p+q+r=0} (û_p·r)(û_q·û_r)
```
二つを足すと
```
2S = Σ_{p+q+r=0} (û_q·û_r) (û_p·(q+r)) = Σ (û_q·û_r) (û_p·(-p))
```

**Step 5. 非圧縮性で潰す。**
`û_p · p = 0`（div-free）より `2S = 0`、よって `S = 0`。

したがって非線形項の寄与は `Re(-2πi · 0) = 0`。
**実部だけでなく `S` 自体が 0 になる**（結論より強い）。

### Lean 実装上の注意

- Step 4 の入れ替えには `Finset.sum_nbij'` / `Finset.sum_comm` / `Finset.sum_bij` あたりを使う。
  写像 `(p,q) ↦ (p, -(p+q))` が対応する finset 上の対合になることを示す。
- 台の扱い: `κ - p` が `M` の外に出る場合があるが `SupportedOn M a` より
  `a (κ-p) = 0` なので項が消える。和を `M` の外に広げても値が変わらないことを
  先に補題化しておくと Step 3–4 が楽になる。
- `Complex.normSq` と `herm` の関係 (`herm v v = ‖v‖²` の実数化) も補題にしておくと T2 で効く。

---

## 7. 未決定事項（★人間の判断が必要）

### D1. `M` の対称性を仮説に追加すべきか

**発見**: SECTION 6 の Step 4（`q ↔ r` の入れ替え）が成立するには、
`M` が原点対称（`κ ∈ M ↔ -κ ∈ M`）である必要がある。
`p, q ∈ M` かつ `κ = p+q ∈ M` のとき `r = -κ ∈ M` が要るため。

さらに: `SupportedOn M a` と `RealField a` を同時に課すと、
`M` が非対称な場合 `κ ∈ M \ (-M)` に対して `a κ = 0` が強制される。
つまり現状の仮説は矛盾はしないが、**非対称部分を暗黙に殺している**。
これは空虚化の入口になりうる。

**提案**: `IsGalerkinSolutionOn` に以下を追加する。
```lean
symmetric : ∀ κ : Mode, κ ∈ M ↔ -κ ∈ M
```
実数値速度場の Galerkin 切断は物理的に必ず対称なので、
これは制限ではなく**規約の明示化**である。

ただしこれは仮説の追加なので R2 に従い、**勝手に入れずに承認を取ること**。
承認されたら、なぜ必要かを doc comment に書いた上で追加する。

### D2. `Tstar = 0` の扱い

現状の定義では「解が全く存在しない」場合も `Tstar = 0 < ⊤` となり
`BlowsUp = True` に潰れる。局所可解性が別途保証される文脈では問題ないが、
「即座に破綻」と「有限時間で爆発」を区別したいなら定義を分けるべき。

判断待ち。局所存在（T4 の一部）を先に証明すれば自動的に解消する可能性もある。

---

## 8. やってはいけないこと

- ❌ 証明を通すためにステートメントを弱める（R1）
- ❌ 仮説を黙って追加する（R2、D1 が該当）
- ❌ `hFoo : True` のような中身のない仮説フィールドを置く（R6）
- ❌ `NSTimeEvolution.lean` を `NSBarrier.lean` に import する
  （0-sorry CI が壊れる。証明が全部埋まるまで分離したまま）
- ❌ 既存 159 ファイルを「修正」しにいく
  （まず新層を完成させる。既存層の名称修正はその後の別作業）
- ❌ 「ミレニアム問題を解いた」と書く
  現状で射程内なのは **Galerkin 切断の大域可解性**まで。
  それ自体は無条件の本物の定理だが、ミレニアム問題本体ではない。
  T6 の `K_max` 一様性が未解決である限り、そこは越えていない。

---

## 9. 一言

既存の 25,888 行は捨てなくてよい。
`NSTorusShellActual` のフーリエ基底・直交射影・縮小性の証明、
有限帯域 Bernstein は本物であり、そのまま土台に使える。
壊れていたのは上に載っていた言明の方である。

条件付き 25,888 行より、無条件 2,000 行の方が数学的には重い。
