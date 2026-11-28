import OMAReductions.R_Erdos1135_erdos_1135_R2_H2_R1
import Mathlib

/-!
# Bounds for linear forms in log 2 and log 3

Adapted from LABO-COLLATZ, directed by Eric Merle, with formalisation written
with Claude (Anthropic). Source tag v1.5, distributed under CC BY 4.0.

https://github.com/ericmerle3789/one-obstruction-three-faces-lean/tree/v1.5/logs23
https://github.com/ericmerle3789/one-obstruction-three-faces-lean/tree/v1.5/steiner1978
https://creativecommons.org/licenses/by/4.0/

This file collects the declarations used for the positive power gap in the
Collatz cycle argument. It omits unrelated declarations, adapts the
sign-variation proof to the pinned version of Mathlib, and uses the name
`Finset.prod_le_prod` for the nonnegative product inequality in this version.
-/

-- Source module: Steiner/Steiner_Enonces

namespace Steiner

/-- The linear form `Λ = (k + l) log 2 − k log 3` (natural logarithms). -/
noncomputable def Lam (k l : ℕ) : ℝ := ((k + l : ℕ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3

end Steiner

-- Source module: Steiner/Fini

namespace Steiner

/-- An approximation of `⌊k log₂ 3⌋ + 1` (40 digits of `log₂ 3`), re-checked by `posOK`. -/
def Lk (k : ℕ) : ℕ := k * 1584962500721156181453738943947816508759 / 10 ^ 39 + 1

/-- Positive side: `2^(Lk−1) ≤ 3^k < 2^Lk` and `(2^Lk − 3^k)(2^k − 1) > 3^k − 2^k`. -/
def posOK (k : ℕ) : Bool :=
  decide (2 ^ Lk k / 2 ≤ 3 ^ k) && decide (3 ^ k < 2 ^ Lk k) &&
    decide (3 ^ k - 2 ^ k < (2 ^ Lk k - 3 ^ k) * (2 ^ k - 1))

/-- Negative side: `2^(Lk−1) < 3^k` and `(3^k − 2^(Lk−1))(2^k + 1) > 3^k − 2^k`. -/
def negOK (k : ℕ) : Bool :=
  decide (2 ^ Lk k / 2 < 3 ^ k) && decide (3 ^ k - 2 ^ k < (3 ^ k - 2 ^ Lk k / 2) * (2 ^ k + 1))

/-- The test for one `k`; the negative side is skipped at `k = 2` (the solution `(2, 1, −1)`). -/
def chk (k : ℕ) : Bool := posOK k && (k == 2 || negOK k)

/-- `chk k` for `2 ≤ k ≤ N`. -/
def allChk : ℕ → Bool
  | 0 => true
  | 1 => true
  | n + 2 => chk (n + 2) && allChk (n + 1)

theorem allChk_spec : ∀ N, allChk N = true → ∀ k, 2 ≤ k → k ≤ N → chk k = true := by
  intro N
  induction N with
  | zero => intro _ k h1 h2; omega
  | succ N ih =>
    intro hN k h1 h2
    match N, hN, ih with
    | 0, _, _ => omega
    | N + 1, hN, ih =>
      simp only [allChk, Bool.and_eq_true] at hN
      rcases Nat.lt_or_ge k (N + 2) with h | h
      · exact ih hN.2 k h1 (by omega)
      · obtain rfl : k = N + 2 := by omega
        exact hN.1

/-- **The finite check**, by the kernel. -/
theorem allChk_20000 : allChk 20000 = true := by decide +kernel

theorem chk_of_le {k : ℕ} (h1 : 2 ≤ k) (h2 : k ≤ 20000) : chk k = true :=
  allChk_spec 20000 allChk_20000 k h1 h2

theorem pow_half {M : ℕ} (h : 1 ≤ M) : 2 ^ M / 2 = 2 ^ (M - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  simp [pow_succ]

/-- `posOK` excludes every `L` with `3^k < 2^L` and `(2^L − 3^k)(2^k − 1) ≤ 3^k − 2^k`. -/
theorem pos_exclude {k L : ℕ} (hk : 1 ≤ k) (hok : posOK k = true) (h1 : 3 ^ k < 2 ^ L)
    (h2 : (2 ^ L - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k) : False := by
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hA, hB⟩, hC⟩ := hok
  set M := Lk k with hM
  have hM1 : 1 ≤ M := by simp [hM, Lk]
  have hhalf : 2 ^ M / 2 = 2 ^ (M - 1) := pow_half hM1
  rw [hhalf] at hA
  have hs : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- `M ≤ L`
  have hML : M ≤ L := by
    by_contra hlt
    have : 2 ^ L ≤ 2 ^ (M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le hML with heq | hlt
  · subst heq; omega
  · -- `2^L ≥ 2·2^M > 2·3^k`
    have : 2 ^ (M + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hlt
    rw [pow_succ] at this
    have h3 : 3 ^ k - 2 ^ k < 2 ^ L - 3 ^ k := by omega
    have h4 : 2 ^ L - 3 ^ k ≤ (2 ^ L - 3 ^ k) * (2 ^ k - 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega

end Steiner

-- Source module: Steiner/Analyse

namespace Steiner

theorem Lam_eq (k l : ℕ) : Lam k l = Real.log ((2 : ℝ) ^ (k + l) / 3 ^ k) := by
  unfold Lam
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- If `3^k < 2^L`: `0 < Λ ≤ (2^L − 3^k)/3^k`. -/
theorem Lam_pos_le {k l : ℕ} (h : (3 : ℝ) ^ k < 2 ^ (k + l)) :
    0 < Lam k l ∧ Lam k l ≤ ((2 : ℝ) ^ (k + l) - 3 ^ k) / 3 ^ k := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  rw [Lam_eq]
  refine ⟨Real.log_pos ((one_lt_div h3).mpr h), ?_⟩
  calc Real.log ((2 : ℝ) ^ (k + l) / 3 ^ k) ≤ (2 : ℝ) ^ (k + l) / 3 ^ k - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = ((2 : ℝ) ^ (k + l) - 3 ^ k) / 3 ^ k := by field_simp

end Steiner

-- Source module: Logs23/Logs23_Enonces

namespace Logs23

open Steiner

/-- Numerator of the convergent of `log₂ 3` with 100-digit denominator `qBr`. -/
def pBr : ℕ :=
  7075648572877059919177282639679936234273371429152254350020918875159741651922223841987201299719166766

/-- The first denominator of a convergent of `log₂ 3` with 100 digits. -/
def qBr : ℕ :=
  4464237210443557913445974161134855053365712428483203741240064204646931348649280801574011068200682601

/-- Numerator of the next convergent. -/
def pBr' : ℕ :=
  100503145492375000798721301105204469272055612770110310199489733016535938908007507750788779148681720787

/-- Denominator of the next convergent (101 digits). -/
def qBr' : ℕ :=
  63410424818660492580825542274682247263205981867410584037516082787822549765875074521441459392200135171

/-- No `L log 2 − k log 3` with `0 < k < qBr'` is closer to `0` than `pBr log 2 − qBr log 3`. -/
def bridge_gap : Prop :=
  ∀ (k : ℕ) (L : ℤ), 0 < k → k < qBr' →
    |(pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3| ≤ |(L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3|

/-- The size of the gap. -/
def bridge_value : Prop :=
  (1 : ℝ) / 10 ^ 101 ≤ |(pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3|

/-- The lower bound for `Λ`, for `20000 < k < qBr'`. -/
def lam_lower_bridge : Prop :=
  ∀ k l : ℕ, 20000 < k → k < qBr' → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|

/-- **Final target**: the lower bound for `Λ`, for every `k > 20000`. -/
def lam_lower : Prop :=
  ∀ k l : ℕ, 20000 < k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|

end Logs23

-- Source module: Logs23/TwoLog_Enonces

/-!
# Logs23 · FROZEN STATEMENTS of step 2b (a lower bound for linear forms in `log 2` and `log 3`)

Written before the proofs (committed alone), after the statements of step 2a (`Logs23/Logs23_Enonces.lean`).

`two_log_lower` is an explicit lower bound of polylogarithmic type for `|b₁ log 2 − b₂ log 3|`, for `b₂ ≥ 2^334`.
Much stronger explicit bounds are known (M. Laurent, Acta Arith. 66 (1994); M. Laurent, M. Mignotte,
Y. Nesterenko, J. Number Theory 55 (1995); N. Gouillon, J. Théor. Nombres Bordeaux 18 (2006)); the constant
`10^12` and the exponent `5` are chosen so that the proof can be crude. The planned proof (an interpolation
determinant whose zero lemma is replaced by total positivity) is described in the lab's register, not here.

`lam_lower_large` is the case `k ≥ 2^334` of `Logs23.lam_lower`; together with `Logs23.lam_lower_bridge`
(`20000 < k < qBr'`, and `2^334 < qBr'`) it gives `Logs23.lam_lower`, hence, by `Logs23.reduction`, Steiner's
theorem without hypothesis.

| Lean | content |
|---|---|
| `two_log_lower` | `b₂ ≥ 2^334` ⇒ `exp(−10^12 ν^5) ≤ \|b₁ log 2 − b₂ log 3\|`, `ν = ⌊log₂ b₂⌋ + 1` (`Nat.log 2 b₂ + 1`), every `b₁ ≥ 0` |
| `lam_lower_large` | `k ≥ 2^334` ⇒ `1/(2^k − 1) ≤ \|Λ\|`, `Λ = (k + l) log 2 − k log 3`, every `l ≥ 0` |
-/

namespace Logs23

open Steiner

/-- An explicit lower bound for `|b₁ log 2 − b₂ log 3|` when `b₂ ≥ 2^334`, with `ν = Nat.log 2 b₂ + 1`. -/
def two_log_lower : Prop :=
  ∀ b₁ b₂ : ℕ, 2 ^ 334 ≤ b₂ →
    Real.exp (-(10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5)) ≤
      |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3|

/-- The lower bound for `Λ` needed by Steiner's theorem, for `k ≥ 2^334`. -/
def lam_lower_large : Prop :=
  ∀ k l : ℕ, 2 ^ 334 ≤ k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|

end Logs23

-- Source module: Logs23/Encadrements

/-!
# Logs23 · proofs (1): certified enclosures of `log 2` and `log 3`

`log 2 = 2 artanh(1/3)` and `log (3/2) = 2 artanh(1/5)`, with the partial sums
`∑_{i<n} x^(2i+1)/(2i+1)` and the remainder bounds of Mathlib (`Real.sum_range_le_log_div`,
`Real.log_div_le_sum_range_add`). The partial sums are rational numbers computed by `atanhSum`; the comparisons
between such rationals are checked by the kernel (`decide +kernel`). Widths: below `10^(−211)`.
-/

namespace Logs23

/-- `∑_{i<n} x^(2i+1)/(2i+1)` in `ℚ`, by recursion on `n`. -/
def atanhSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhSum x n + x ^ (2 * n + 1) / (2 * n + 1)

theorem atanhSum_cast (x : ℚ) (n : ℕ) :
    ((atanhSum x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  induction n with
  | zero => simp [atanhSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [atanhSum]
    push_cast
    ring

/-- The enclosure of `(1/2) log ((1 + x)/(1 − x))` given by `n` terms, for `0 ≤ x < 1`. -/
theorem half_log_bounds {x : ℚ} (h₀ : 0 ≤ x) (h₁ : x < 1) (n : ℕ) :
    ((atanhSum x n : ℚ) : ℝ) ≤ 1 / 2 * Real.log ((1 + x) / (1 - x)) ∧
      1 / 2 * Real.log ((1 + x) / (1 - x)) ≤
        ((atanhSum x n + x ^ (2 * n + 1) / (1 - x ^ 2) : ℚ) : ℝ) := by
  have h₀' : (0 : ℝ) ≤ x := by exact_mod_cast h₀
  have h₁' : (x : ℝ) < 1 := by exact_mod_cast h₁
  refine ⟨?_, ?_⟩
  · rw [atanhSum_cast]
    exact Real.sum_range_le_log_div h₀' h₁' n
  · push_cast
    rw [atanhSum_cast]
    exact Real.log_div_le_sum_range_add h₀' h₁' n

/-- Lower end for `log 2`. -/
def L2lo : ℚ := 2 * atanhSum (1 / 3) 221
/-- Upper end for `log 2`. -/
def L2hi : ℚ := 2 * (atanhSum (1 / 3) 221 + (1 / 3) ^ (2 * 221 + 1) / (1 - (1 / 3) ^ 2))
/-- Lower end for `log (3/2)`. -/
def L32lo : ℚ := 2 * atanhSum (1 / 5) 155
/-- Upper end for `log (3/2)`. -/
def L32hi : ℚ := 2 * (atanhSum (1 / 5) 155 + (1 / 5) ^ (2 * 155 + 1) / (1 - (1 / 5) ^ 2))

theorem log_two_bounds : (L2lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (L2hi : ℝ) := by
  obtain ⟨h1, h2⟩ := half_log_bounds (x := 1 / 3) (by norm_num) (by norm_num) 221
  have e : (1 + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) = 2 := by norm_num
  rw [e] at h1 h2
  unfold L2lo L2hi
  push_cast at h1 h2 ⊢
  constructor <;> linarith

theorem log_three_halves_bounds : (L32lo : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ (L32hi : ℝ) := by
  obtain ⟨h1, h2⟩ := half_log_bounds (x := 1 / 5) (by norm_num) (by norm_num) 155
  have e : (1 + ((1 / 5 : ℚ) : ℝ)) / (1 - ((1 / 5 : ℚ) : ℝ)) = 3 / 2 := by norm_num
  rw [e] at h1 h2
  unfold L32lo L32hi
  push_cast at h1 h2 ⊢
  constructor <;> linarith

theorem log_three_eq : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log_three_bounds :
    ((L2lo + L32lo : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((L2hi + L32hi : ℚ) : ℝ) := by
  obtain ⟨a, b⟩ := log_two_bounds
  obtain ⟨c, d⟩ := log_three_halves_bounds
  rw [log_three_eq]
  push_cast
  constructor <;> linarith

/-- The widths, checked by the kernel. -/
theorem widths : L2hi - L2lo < 1 / 10 ^ 211 ∧ L32hi - L32lo < 1 / 10 ^ 211 := by
  decide +kernel

end Logs23

-- Source module: Logs23/Pont

/-!
# Logs23 · proofs (2): the bridge

Write `(L, k) = a (pBr, qBr) + b (pBr', qBr')` in the basis of the two convergents, which is unimodular
(`pBr' qBr − pBr qBr' = 1`). Then `L log 2 − k log 3 = a e₁ + b e₂` with `e₁ = pBr log 2 − qBr log 3 < 0` and
`e₂ = pBr' log 2 − qBr' log 3 > 0`. For `0 < k < qBr'`, `a ≠ 0` and `a b ≤ 0`, so `b e₂` is zero or has the sign of
`a e₁`, and `|L log 2 − k log 3| ≥ |a e₁| ≥ |e₁|`. The two signs and `|e₁| ≥ 10^(−101)` come from the enclosures of
`Logs23/Encadrements.lean`, compared by the kernel.
-/

namespace Logs23

open Steiner

/-- If `e₁ < 0 < e₂`, `a ≠ 0` and `a b ≤ 0`, then `|e₁| ≤ |a e₁ + b e₂|`. -/
theorem abs_le_of_signs {e₁ e₂ : ℝ} (h₁ : e₁ < 0) (h₂ : 0 < e₂) {a b : ℤ} (ha : a ≠ 0) (hab : a * b ≤ 0) :
    |e₁| ≤ |(a : ℝ) * e₁ + (b : ℝ) * e₂| := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hb : 0 ≤ b := by
      by_contra hb
      rw [not_le] at hb
      nlinarith
    have ha' : (a : ℝ) ≤ -1 := by exact_mod_cast (by omega : a ≤ -1)
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    rw [abs_of_neg h₁, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hb : b ≤ 0 := by
      by_contra hb
      rw [not_le] at hb
      nlinarith
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
    have hb' : (b : ℝ) ≤ 0 := by exact_mod_cast hb
    rw [abs_of_neg h₁, abs_of_nonpos (by nlinarith)]
    nlinarith

/-- The gap lemma for vectors of natural numbers `(p, q)`, `(p', q')` with `p' q − p q' = 1` whose linear forms
`p log 2 − q log 3 < 0 < p' log 2 − q' log 3` have opposite signs (`q ≥ 0` is used). -/
theorem gap_of_unimodular {p q p' q' : ℕ} (hu : (p' : ℤ) * q - p * q' = 1)
    (h₁ : (p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3 < 0)
    (h₂ : 0 < (p' : ℝ) * Real.log 2 - (q' : ℝ) * Real.log 3)
    (k : ℕ) (L : ℤ) (hk : 0 < k) (hk' : k < q') :
    |(p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3| ≤ |(L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3| := by
  set a : ℤ := p' * k - L * q' with ha
  set b : ℤ := q * L - p * k with hb
  have hk_eq : (k : ℤ) = a * q + b * q' := by
    rw [ha, hb]
    linear_combination (-(k : ℤ)) * hu
  have hq' : (0 : ℤ) < q' := by exact_mod_cast (by omega : 0 < q')
  have hq : (0 : ℤ) ≤ q := by positivity
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  have hk1 : (k : ℤ) < q' := by exact_mod_cast hk'
  -- `a ≠ 0`
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hk_eq
    rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
    · nlinarith
    · rw [hb0, zero_mul] at hk_eq; omega
    · nlinarith
  -- `a b ≤ 0`
  have hab : a * b ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    rcases lt_or_gt_of_ne ha0 with han | hap
    · have hbn : b < 0 := by
        by_contra hb0; rw [not_lt] at hb0; nlinarith
      nlinarith
    · have hbp : 0 < b := by
        by_contra hb0; rw [not_lt] at hb0; nlinarith
      nlinarith
  have hcast : ((p' : ℝ) * q - p * q') = 1 := by exact_mod_cast hu
  have hid : (L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 =
      (a : ℝ) * ((p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3) +
        (b : ℝ) * ((p' : ℝ) * Real.log 2 - (q' : ℝ) * Real.log 3) := by
    rw [ha, hb]
    push_cast
    linear_combination (-((L : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3)) * hcast
  rw [hid]
  exact abs_le_of_signs h₁ h₂ ha0 hab

/-! ## The two convergents -/

theorem unimod_br : (pBr' : ℤ) * qBr - pBr * qBr' = 1 := by decide +kernel

/-- Rational form of `e₁_le`: the upper bound `pBr·L2hi − qBr·(L2lo + L32lo)` for `pBr log 2 − qBr log 3`
is `≤ −10^(−101)` (rational comparison by the kernel). -/
theorem e₁_rat : (pBr : ℚ) * L2hi - qBr * (L2lo + L32lo) ≤ -(1 / 10 ^ 101) := by decide +kernel

/-- Rational form of `e₂_pos`: the lower bound `pBr'·L2lo − qBr'·(L2hi + L32hi)` for `pBr' log 2 − qBr' log 3`
is `> 0` (rational comparison by the kernel). -/
theorem e₂_rat : 0 < (pBr' : ℚ) * L2lo - qBr' * (L2hi + L32hi) := by decide +kernel

theorem e₁_le : (pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3 ≤ -(1 / 10 ^ 101) := by
  obtain ⟨-, h2⟩ := log_two_bounds
  obtain ⟨h3, -⟩ := log_three_bounds
  have hr : ((pBr : ℚ) * L2hi - qBr * (L2lo + L32lo) : ℝ) ≤ ((-(1 / 10 ^ 101) : ℚ) : ℝ) := by
    exact_mod_cast e₁_rat
  push_cast at hr h3
  have hp : (0 : ℝ) ≤ pBr := by positivity
  have hq : (0 : ℝ) ≤ qBr := by positivity
  nlinarith

theorem e₂_pos : 0 < (pBr' : ℝ) * Real.log 2 - (qBr' : ℝ) * Real.log 3 := by
  obtain ⟨h1, -⟩ := log_two_bounds
  obtain ⟨-, h4⟩ := log_three_bounds
  have hr : ((0 : ℚ) : ℝ) < ((pBr' : ℚ) * L2lo - qBr' * (L2hi + L32hi) : ℝ) := by
    exact_mod_cast e₂_rat
  push_cast at hr h4
  have hp : (0 : ℝ) ≤ pBr' := by positivity
  have hq : (0 : ℝ) ≤ qBr' := by positivity
  nlinarith

theorem bridge_value_thm : bridge_value := by
  have h := e₁_le
  rw [bridge_value, abs_of_neg (by linarith)]
  linarith

theorem bridge_gap_thm : bridge_gap := by
  intro k L hk hk'
  have h₁ : (pBr : ℝ) * Real.log 2 - (qBr : ℝ) * Real.log 3 < 0 := by
    have := e₁_le
    have : (0 : ℝ) < 1 / 10 ^ 101 := by positivity
    linarith
  exact gap_of_unimodular unimod_br h₁ e₂_pos k L hk hk'

/-! ## The lower bound for `Λ` up to `qBr'` -/

theorem two_pow_big {k : ℕ} (hk : 20000 < k) : (10 : ℝ) ^ 101 ≤ (2 : ℝ) ^ k - 1 := by
  have h : (10 : ℕ) ^ 101 + 1 ≤ 2 ^ 400 := by decide +kernel
  have h' : (2 : ℕ) ^ 400 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (10 : ℝ) ^ 101 + 1 ≤ (2 : ℝ) ^ k := by exact_mod_cast h.trans h'
  linarith

theorem lam_lower_bridge_thm : lam_lower_bridge := by
  intro k l hk hk'
  have hgap := bridge_gap_thm k ((k + l : ℕ) : ℤ) (by omega) hk'
  have hval := bridge_value_thm
  have hLam : |(((k + l : ℕ) : ℤ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3| = |Lam k l| := by
    unfold Lam; push_cast; ring_nf
  rw [hLam] at hgap
  have hb := two_pow_big hk
  have h10 : (0 : ℝ) < 10 ^ 101 := by positivity
  calc 1 / ((2 : ℝ) ^ k - 1) ≤ 1 / 10 ^ 101 := one_div_le_one_div_of_le h10 hb
    _ ≤ |Lam k l| := hval.trans hgap

end Logs23

-- Source module: Logs23/CauchyBinet

/-!
# Logs23 · the Cauchy–Binet formula

`det (A * B) = ∑_Q det (A with the columns in Q) · det (B with the rows in Q)`, for `A : N × n`, `B : n × N`,
`Q` ranging over the `N`-element subsets of `Fin n`, listed in increasing order by `Finset.orderEmbOfFin`.
-/

namespace Logs23

open Matrix Finset Equiv

variable {R : Type*} [CommRing R]

/-- The `N`-element subsets of `Fin n`. -/
abbrev Subsets (N n : ℕ) := {Q : Finset (Fin n) // Q.card = N}

/-- The increasing enumeration of `Q`. -/
abbrev enum {N n : ℕ} (Q : Subsets N n) : Fin N → Fin n := fun i => Q.1.orderEmbOfFin Q.2 i

/-- `det (A * B)` as a sum over all maps `Fin N → Fin n`. -/
theorem det_mul_eq_sum_fun {N n : ℕ} (A : Matrix (Fin N) (Fin n) R) (B : Matrix (Fin n) (Fin N) R) :
    (A * B).det = ∑ f : Fin N → Fin n, (A.submatrix id f).det * ∏ j, B (f j) j := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

theorem det_submatrix_eq_zero_of_not_injective {N n : ℕ} (A : Matrix (Fin N) (Fin n) R)
    {f : Fin N → Fin n} (hf : ¬ Function.Injective f) : (A.submatrix id f).det = 0 := by
  rw [Function.Injective] at hf
  push Not at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

theorem enum_injective {N n : ℕ} (Q : Subsets N n) : Function.Injective (enum Q) :=
  (Q.1.orderEmbOfFin Q.2).injective

theorem range_enum {N n : ℕ} (Q : Subsets N n) : Set.range (enum Q) = Q.1 :=
  Finset.range_orderEmbOfFin Q.1 Q.2

/-- **Cauchy–Binet.** -/
theorem det_mul_eq_sum_subsets {N n : ℕ} (A : Matrix (Fin N) (Fin n) R) (B : Matrix (Fin n) (Fin N) R) :
    (A * B).det = ∑ Q : Subsets N n, (A.submatrix id (enum Q)).det * (B.submatrix (enum Q) id).det := by
  set F : (Fin N → Fin n) → R := fun f => (A.submatrix id f).det * ∏ j, B (f j) j with hF
  -- the right side as a sum over pairs `(Q, σ)`
  have hR : ∀ Q : Subsets N n, (A.submatrix id (enum Q)).det * (B.submatrix (enum Q) id).det =
      ∑ σ : Perm (Fin N), F (enum Q ∘ σ) := by
    intro Q
    rw [det_apply' (B.submatrix (enum Q) id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : A.submatrix id (enum Q ∘ σ) = (A.submatrix id (enum Q)).submatrix id σ := by
      ext i j; simp
    simp only [hF, h1, det_permute', submatrix_apply, id, Function.comp]
    ring
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun Q _ => hR Q), ← Finset.sum_product']
  -- only injective maps contribute
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun f _ hf => by
    by_contra hinj
    exact hf (by simp [det_submatrix_eq_zero_of_not_injective A hinj]))]
  symm
  refine Finset.sum_bij (fun p _ => enum p.1 ∘ p.2) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (enum_injective p.1).comp p.2.injective
  · intro p _ q _ hpq
    have hQ : p.1 = q.1 := by
      apply Subtype.ext
      have := congrArg Set.range hpq
      simp only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] at this
      rw [range_enum, range_enum] at this
      exact_mod_cast this
    obtain ⟨Qp, σp⟩ := p
    obtain ⟨Qq, σq⟩ := q
    simp only at hQ
    subst hQ
    simp only [Prod.mk.injEq, true_and]
    ext i
    exact congrArg Fin.val (enum_injective Qp (congrFun hpq i))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hcard : (Finset.univ.image f).card = N := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    set Q : Subsets N n := ⟨Finset.univ.image f, hcard⟩ with hQ
    have hmem : ∀ j, f j ∈ Q.1 := fun j => Finset.mem_image_of_mem f (Finset.mem_univ j)
    let τ : Fin N → Fin N := fun j => (Q.1.orderIsoOfFin Q.2).symm ⟨f j, hmem j⟩
    have hτ : ∀ j, enum Q (τ j) = f j := by
      intro j
      simp only [enum, τ]
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    have hτinj : Function.Injective τ := by
      intro a b hab
      apply hf
      rw [← hτ a, ← hτ b, hab]
    let σ : Perm (Fin N) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
    refine ⟨(Q, σ), Finset.mem_univ _, ?_⟩
    funext j
    exact hτ j
  · intro p _
    rfl

end Logs23

-- Source module: Logs23/GenVandermonde

/-!
# Logs23 · generalized Vandermonde determinants

For `0 < y_1 < … < y_N` and natural numbers `m_1 < … < m_N`, `det [y_j ^ m_k] > 0`.
Non-vanishing comes from Descartes' rule of signs (`Polynomial.roots_countP_pos_le_signVariations`): a nonzero
polynomial with at most `N` nonzero coefficients has at most `N − 1` positive roots. The sign is then constant on the
convex set of increasing positive tuples, and positive at `y_j = 2^(j+1)` (a Vandermonde determinant).
-/

namespace Logs23

open Matrix Finset Polynomial

/-- The number of sign variations of a list is at most its number of nonzero entries minus one. -/
theorem coeffList_signVariations_le_length_filter (P : ℝ[X]) :
    P.signVariations ≤ (P.coeffList.filter (· ≠ 0)).length - 1 := by
  unfold Polynomial.signVariations
  apply Nat.sub_le_sub_right
  refine ((List.destutter_sublist _ _).length_le).trans (le_of_eq ?_)
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp [sign_eq_zero_iff]

/-- A polynomial whose nonzero coefficients sit in `s` has at most `s.card − 1` sign variations. -/
theorem signVariations_le_of_support_subset (P : ℝ[X]) {s : Finset ℕ} (hs : P.support ⊆ s) :
    P.signVariations ≤ s.card - 1 := by
  refine (coeffList_signVariations_le_length_filter _).trans (Nat.sub_le_sub_right ?_ 1)
  unfold Polynomial.coeffList
  rw [List.filter_map, List.length_map]
  set F := (List.range P.degree.succ).reverse.filter ((· ≠ 0) ∘ P.coeff) with hF
  have hnd : F.Nodup := by
    rw [hF]
    exact (List.nodup_reverse.mpr List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro i hi
  rw [List.mem_toFinset, hF, List.mem_filter] at hi
  apply hs
  rw [Polynomial.mem_support_iff]
  simpa using hi.2

/-- Generalized Vandermonde determinants with distinct positive nodes and distinct exponents do not vanish. -/
theorem det_genVandermonde_ne_zero {N : ℕ} {y : Fin N → ℝ} (hy : Function.Injective y) (hpos : ∀ j, 0 < y j)
    {m : Fin N → ℕ} (hm : Function.Injective m) : (Matrix.of fun k j => y j ^ m k).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hcM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  set P : ℝ[X] := ∑ k, C (c k) * X ^ (m k) with hP
  have hcoeff : ∀ k, P.coeff (m k) = c k := by
    intro k
    rw [hP, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      have : m k ≠ m b := fun h => hb (hm h).symm
      simp [this]
    · simp
  have hsupp : P.support ⊆ Finset.univ.image m := by
    intro i hi
    rw [Polynomial.mem_support_iff, hP, Polynomial.finsetSum_coeff] at hi
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    rw [Polynomial.coeff_C_mul_X_pow] at hk
    by_cases hik : i = m k
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hik.symm⟩
    · simp [hik] at hk
  have hPne : P ≠ 0 := by
    intro hP0
    apply hc
    funext k
    rw [← hcoeff k, hP0, Polynomial.coeff_zero, Pi.zero_apply]
  have heval : ∀ j, P.IsRoot (y j) := by
    intro j
    have h := congrFun hcM j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    rw [Polynomial.IsRoot, hP, Polynomial.eval_finsetSum]
    simpa using h
  -- `N` distinct positive roots
  have hle : (Finset.univ.val.map y) ≤ P.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hy Finset.univ.nodup)]
    intro x hx
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hPne).mpr (heval j)
  have hcount : N ≤ P.roots.countP (0 < ·) := by
    calc N = (Finset.univ.val.map y).countP (0 < ·) := by
          rw [Multiset.countP_eq_card.mpr (fun x hx => by
            obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
            exact hpos j)]
          simp
      _ ≤ P.roots.countP (0 < ·) := Multiset.countP_le_of_le _ hle
  have hsv := signVariations_le_of_support_subset P hsupp
  have hcard : (Finset.univ.image m).card ≤ N := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := m)
  have hdesc := Polynomial.roots_countP_pos_le_signVariations P
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact absurd (_root_.funext fun k => Fin.elim0 k) hc
    · exact h
  omega

/-- The value at the reference nodes `y_j = 2^(j+1)`. -/
theorem det_genVandermonde_ref_pos {N : ℕ} {m : Fin N → ℕ} (hm : StrictMono m) :
    0 < (Matrix.of fun k (j : Fin N) => ((2 : ℝ) ^ (j.1 + 1)) ^ m k).det := by
  set u : Fin N → ℝ := fun k => (2 : ℝ) ^ m k with hu
  have hmat : (Matrix.of fun k (j : Fin N) => ((2 : ℝ) ^ (j.1 + 1)) ^ m k) =
      Matrix.of fun k j => u k * Matrix.vandermonde u k j := by
    ext k j
    simp only [Matrix.of_apply, Matrix.vandermonde_apply, hu, ← pow_mul]
    ring_nf
  rw [hmat, Matrix.det_mul_column, Matrix.det_vandermonde]
  have hus : StrictMono u := fun a b hab => pow_lt_pow_right₀ (by norm_num) (hm hab)
  apply mul_pos
  · exact Finset.prod_pos fun k _ => by positivity
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have : i < j := Finset.mem_Ioi.mp hj
    linarith [hus this]

/-- **Generalized Vandermonde determinants are positive** for increasing positive nodes and increasing exponents. -/
theorem det_genVandermonde_pos {N : ℕ} {y : Fin N → ℝ} (hy : StrictMono y) (hpos : ∀ j, 0 < y j)
    {m : Fin N → ℕ} (hm : StrictMono m) : 0 < (Matrix.of fun k j => y j ^ m k).det := by
  set y₀ : Fin N → ℝ := fun j => (2 : ℝ) ^ (j.1 + 1) with hy₀
  have hy₀s : StrictMono y₀ := fun a b hab => pow_lt_pow_right₀ (by norm_num) (by simpa using hab)
  set z : ℝ → Fin N → ℝ := fun t j => (1 - t) * y₀ j + t * y j with hz
  set g : ℝ → ℝ := fun t => (Matrix.of fun k j => z t j ^ m k).det with hg
  have hzs : ∀ t ∈ Set.Icc (0 : ℝ) 1, StrictMono (z t) ∧ ∀ j, 0 < z t j := by
    intro t ht
    obtain ⟨h0, h1⟩ := ht
    refine ⟨fun a b hab => ?_, fun j => ?_⟩
    · have ha := hy₀s hab
      have hb := hy hab
      simp only [hz]
      rcases eq_or_lt_of_le h0 with rfl | h0'
      · simpa using ha
      · nlinarith
    · have : 0 < y₀ j := by positivity
      simp only [hz]
      rcases eq_or_lt_of_le h1 with rfl | h1'
      · simpa using hpos j
      · nlinarith [hpos j]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := fun t ht =>
    det_genVandermonde_ne_zero (hzs t ht).1.injective (hzs t ht).2 hm.injective
  have hcont : Continuous g := by
    apply Continuous.matrix_det
    refine continuous_pi fun k => continuous_pi fun j => ?_
    simp only [hz, Matrix.of_apply]
    fun_prop
  have hg0 : 0 < g 0 := by
    simpa [hg, hz] using det_genVandermonde_ref_pos hm
  have hg1 : g 1 = (Matrix.of fun k j => y j ^ m k).det := by simp [hg, hz]
  rw [← hg1]
  by_contra hneg
  rw [not_lt] at hneg
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont.continuousOn ⟨hneg, hg0.le⟩
  exact hne t ht hgt

end Logs23

-- Source module: Logs23/ExpKernel

/-!
# Logs23 · the exponential kernel `det [exp (μ_i ζ_j)]`

For distinct positive `μ_i`, distinct positive `ζ_j` and `x ≥ 0`, the Cauchy–Binet expansion of `det [exp (μ_i x ζ_j)]`
(truncated exponential series, then `n → ∞`) has all its terms of the same sign (generalized Vandermonde
determinants). Hence
* `|det [exp (μ_i ζ_j)]| ≥ (∏_{m<N} 1/m!) |V(μ)| |V(ζ)|` (one term);
* `|det [exp (μ_i ζ_j)]| ≤ x^(−∑_{k<N} k) |det [exp (μ_i x ζ_j)]|` for `x ≥ 1` (termwise).
-/

namespace Logs23

open Matrix Finset Filter Topology Equiv
open scoped Nat

noncomputable section

/-- The Vandermonde product `∏_{i<j} (v_j − v_i)`. -/
def vprod {N : ℕ} (v : Fin N → ℝ) : ℝ := ∏ i : Fin N, ∏ j ∈ Ioi i, (v j - v i)

/-- `0 + 1 + ⋯ + (N − 1)`. -/
def tri (N : ℕ) : ℕ := ∑ k : Fin N, (k : ℕ)

/-- The sum of the elements of `Q`. -/
def esum {N n : ℕ} (Q : Subsets N n) : ℕ := ∑ k, (enum Q k : ℕ)

theorem val_le_of_strictMono {N n : ℕ} {f : Fin N → Fin n} (hf : StrictMono f) (k : Fin N) :
    (k : ℕ) ≤ f k := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨k, by omega⟩ < f ⟨k + 1, hk⟩ := hf (Fin.mk_lt_mk.mpr (by omega))
    have : ((f ⟨k, by omega⟩ : Fin n) : ℕ) < f ⟨k + 1, hk⟩ := h2
    simp only at h1 ⊢
    omega

theorem tri_le_esum {N n : ℕ} (Q : Subsets N n) : tri N ≤ esum Q :=
  Finset.sum_le_sum fun k _ => val_le_of_strictMono (Q.1.orderEmbOfFin Q.2).strictMono k

/-- Sign of a generalized Vandermonde determinant with distinct positive nodes: that of the permutation sorting
the nodes, for every increasing family of exponents. -/
theorem sign_mul_det_genVandermonde_pos {N : ℕ} {y : Fin N → ℝ} (hy : Function.Injective y)
    (hpos : ∀ j, 0 < y j) {e : Fin N → ℕ} (he : StrictMono e) :
    0 < ((Perm.sign (Tuple.sort y) : ℤ) : ℝ) * (Matrix.of fun k j => y j ^ e k).det := by
  set σ := Tuple.sort y
  have hmono : StrictMono (y ∘ σ) :=
    (Tuple.monotone_sort y).strictMono_of_injective (hy.comp σ.injective)
  have h := det_genVandermonde_pos hmono (fun j => hpos (σ j)) he
  have hsub : (Matrix.of fun k j => (y ∘ σ) j ^ e k) = (Matrix.of fun k j => y j ^ e k).submatrix id σ := by
    ext k j; simp
  rw [hsub, det_permute'] at h
  simpa using h

/-- The truncated matrices. -/
def Atr {N : ℕ} (μ : Fin N → ℝ) (n : ℕ) : Matrix (Fin N) (Fin n) ℝ := Matrix.of fun i m => μ i ^ (m : ℕ) / (m : ℕ)!

def Btr {N : ℕ} (ζ : Fin N → ℝ) (x : ℝ) (n : ℕ) : Matrix (Fin n) (Fin N) ℝ :=
  Matrix.of fun m j => (x * ζ j) ^ (m : ℕ)

/-- The kernel matrix. -/
def Ek {N : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => Real.exp (μ i * (x * ζ j))

theorem tendsto_Atr_mul_Btr {N : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) :
    Tendsto (fun n => Atr μ n * Btr ζ x n) atTop (𝓝 (Ek μ ζ x)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hs : HasSum (fun m : ℕ => (μ i * (x * ζ j)) ^ m / (m)!) (Real.exp (μ i * (x * ζ j))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have h := hs.tendsto_sum_nat
  refine h.congr fun n => ?_
  simp only [Matrix.mul_apply, Atr, Btr, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun m => μ i ^ m / (m)! * (x * ζ j) ^ m) n]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow]; ring

theorem tendsto_det {N : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) :
    Tendsto (fun n => (Atr μ n * Btr ζ x n).det) atTop (𝓝 (Ek μ ζ x).det) :=
  ((continuous_id.matrix_det).tendsto _).comp (tendsto_Atr_mul_Btr μ ζ x)

/-- The terms of the Cauchy–Binet expansion. -/
def term {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (Q : Subsets N n) : ℝ :=
  ((Atr μ n).submatrix id (enum Q)).det * ((Btr ζ x n).submatrix (enum Q) id).det

theorem term_eq {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (Q : Subsets N n) :
    term μ ζ x Q = (∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q *
      ((Matrix.of fun k i => μ i ^ (enum Q k : ℕ)).det * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)).det) := by
  have hA : (Atr μ n).submatrix id (enum Q) =
      Matrix.of fun i k => (1 / ((enum Q k : ℕ)! : ℝ)) * (Matrix.of fun k i => μ i ^ (enum Q k : ℕ))ᵀ i k := by
    ext i k; simp [Atr, div_eq_inv_mul]
  have hB : (Btr ζ x n).submatrix (enum Q) id =
      Matrix.of fun k j => x ^ (enum Q k : ℕ) * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)) k j := by
    ext k j; simp [Btr, mul_pow]
  rw [term, hA, hB, det_mul_row, det_mul_column, det_transpose, esum, Finset.prod_pow_eq_pow_sum]
  ring

/-- All terms have the sign `ε := sign(sort μ) · sign(sort ζ)`. -/
theorem eps_mul_term_nonneg {N n : ℕ} {μ ζ : Fin N → ℝ} (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i)
    (hζ : Function.Injective ζ) (hζp : ∀ j, 0 < ζ j) {x : ℝ} (hx : 0 ≤ x) (Q : Subsets N n) :
    0 ≤ ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) * term μ ζ x Q := by
  have he : StrictMono (fun k => (enum Q k : ℕ)) := fun a b hab =>
    (Q.1.orderEmbOfFin Q.2).strictMono hab
  have h1 := sign_mul_det_genVandermonde_pos hμ hμp he
  have h2 := sign_mul_det_genVandermonde_pos hζ hζp he
  have h3 : 0 ≤ (∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q :=
    mul_nonneg (Finset.prod_nonneg fun k _ => by positivity) (pow_nonneg hx _)
  rw [term_eq]
  have : ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) *
      ((∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q *
        ((Matrix.of fun k i => μ i ^ (enum Q k : ℕ)).det * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)).det)) =
      ((∏ k, (1 / ((enum Q k : ℕ)! : ℝ))) * x ^ esum Q) *
        ((((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * (Matrix.of fun k i => μ i ^ (enum Q k : ℕ)).det) *
          (((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) * (Matrix.of fun k j => ζ j ^ (enum Q k : ℕ)).det)) := by ring
  rw [this]
  exact mul_nonneg h3 (mul_pos h1 h2).le

theorem term_scale {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (Q : Subsets N n) :
    term μ ζ x Q = x ^ esum Q * term μ ζ 1 Q := by
  rw [term_eq, term_eq, one_pow]; ring

/-- The leading subset `{0, …, N − 1}` of `Fin n`, `N ≤ n`. -/
def Q₀ {N n : ℕ} (h : N ≤ n) : Subsets N n :=
  ⟨Finset.univ.map (Fin.castLEEmb h), by simp⟩

theorem enum_Q₀ {N n : ℕ} (h : N ≤ n) (k : Fin N) : enum (Q₀ h) k = Fin.castLE h k := by
  have := Finset.orderEmbOfFin_unique (Q₀ h).2 (f := Fin.castLE h)
    (fun k => by simp [Q₀]) (Fin.strictMono_castLE h)
  exact (congrFun this k).symm

theorem vprod_eq_det {N : ℕ} (v : Fin N → ℝ) : (Matrix.of fun (k : Fin N) j => v j ^ (k : ℕ)).det = vprod v := by
  rw [vprod, ← Matrix.det_vandermonde, ← det_transpose]
  rfl

theorem term_Q₀ {N n : ℕ} (h : N ≤ n) (μ ζ : Fin N → ℝ) :
    term μ ζ 1 (Q₀ h) = (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * (vprod μ * vprod ζ) := by
  rw [term_eq]
  simp only [enum_Q₀, Fin.val_castLE, one_pow, mul_one]
  rw [vprod_eq_det ζ, ← vprod_eq_det μ]

/-- `ε · det(truncated product) = Σ ε · term` (nonnegative terms when `ε` is the sign of `eps_mul_term_nonneg`). -/
theorem eps_det_trunc {N n : ℕ} (μ ζ : Fin N → ℝ) (x : ℝ) (ε : ℝ) :
    ε * (Atr μ n * Btr ζ x n).det = ∑ Q : Subsets N n, ε * term μ ζ x Q := by
  rw [det_mul_eq_sum_subsets, Finset.mul_sum]; rfl

variable {N : ℕ} {μ ζ : Fin N → ℝ}

theorem eps_det_Ek_ge (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i) (hζ : Function.Injective ζ)
    (hζp : ∀ j, 0 < ζ j) :
    (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * |vprod μ * vprod ζ| ≤
      ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) * (Ek μ ζ 1).det := by
  set ε := ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) with hε
  have hεabs : |ε| = 1 := by
    rw [hε, abs_mul]
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort μ)) with h | h <;>
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort ζ)) with h' | h' <;> simp [h, h']
  have hlim := (tendsto_det μ ζ 1).const_mul ε
  refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
  rw [eps_det_trunc]
  have hQ₀ := Finset.single_le_sum (f := fun Q => ε * term μ ζ 1 Q)
    (fun Q _ => eps_mul_term_nonneg hμ hμp hζ hζp zero_le_one Q) (Finset.mem_univ (Q₀ hn))
  refine le_trans (le_of_eq ?_) hQ₀
  have hpos : 0 ≤ ε * term μ ζ 1 (Q₀ hn) := eps_mul_term_nonneg hμ hμp hζ hζp zero_le_one _
  set c : ℝ := ∏ k : Fin N, (1 / ((k : ℕ)! : ℝ)) with hc
  have hc0 : 0 ≤ c := Finset.prod_nonneg fun k _ => by positivity
  have ht : term μ ζ 1 (Q₀ hn) = c * (vprod μ * vprod ζ) := term_Q₀ hn μ ζ
  calc c * |vprod μ * vprod ζ| = |ε| * (|c| * |vprod μ * vprod ζ|) := by
        rw [hεabs, abs_of_nonneg hc0, one_mul]
    _ = |ε * term μ ζ 1 (Q₀ hn)| := by rw [ht, abs_mul ε (c * _), abs_mul c]
    _ = ε * term μ ζ 1 (Q₀ hn) := abs_of_nonneg hpos

/-- **The lower bound.** -/
theorem abs_det_Ek_ge (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i) (hζ : Function.Injective ζ)
    (hζp : ∀ j, 0 < ζ j) :
    (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * |vprod μ * vprod ζ| ≤ |(Ek μ ζ 1).det| := by
  refine (eps_det_Ek_ge hμ hμp hζ hζp).trans ?_
  refine (le_abs_self _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign (Tuple.sort μ)) with h | h <;>
  rcases Int.units_eq_one_or (Perm.sign (Tuple.sort ζ)) with h' | h' <;> simp [h, h']

/-- **The Schwarz-type upper bound.** -/
theorem abs_det_Ek_le (hμ : Function.Injective μ) (hμp : ∀ i, 0 < μ i) (hζ : Function.Injective ζ)
    (hζp : ∀ j, 0 < ζ j) {x : ℝ} (hx : 1 ≤ x) :
    |(Ek μ ζ 1).det| ≤ (x ^ tri N)⁻¹ * |(Ek μ ζ x).det| := by
  set ε := ((Perm.sign (Tuple.sort μ) : ℤ) : ℝ) * ((Perm.sign (Tuple.sort ζ) : ℤ) : ℝ) with hε
  have hεabs : |ε| = 1 := by
    rw [hε, abs_mul]
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort μ)) with h | h <;>
    rcases Int.units_eq_one_or (Perm.sign (Tuple.sort ζ)) with h' | h' <;> simp [h, h']
  have hx0 : 0 < x := by linarith
  -- termwise comparison, then limit
  have hfin : ∀ n, ε * (Atr μ n * Btr ζ 1 n).det ≤ (x ^ tri N)⁻¹ * (ε * (Atr μ n * Btr ζ x n).det) := by
    intro n
    rw [eps_det_trunc, eps_det_trunc, Finset.mul_sum]
    refine Finset.sum_le_sum fun Q _ => ?_
    have hnn := eps_mul_term_nonneg hμ hμp hζ hζp zero_le_one Q
    rw [term_scale μ ζ x Q]
    have hpow : x ^ tri N ≤ x ^ esum Q := pow_le_pow_right₀ hx (tri_le_esum Q)
    have hpos : 0 < x ^ tri N := by positivity
    calc ε * term μ ζ 1 Q = (x ^ tri N)⁻¹ * (x ^ tri N * (ε * term μ ζ 1 Q)) := by
          field_simp
      _ ≤ (x ^ tri N)⁻¹ * (x ^ esum Q * (ε * term μ ζ 1 Q)) := by
          gcongr
      _ = (x ^ tri N)⁻¹ * (ε * (x ^ esum Q * term μ ζ 1 Q)) := by ring
  have hlim1 := (tendsto_det μ ζ 1).const_mul ε
  have hlimx := ((tendsto_det μ ζ x).const_mul ε).const_mul (x ^ tri N)⁻¹
  have hle := le_of_tendsto_of_tendsto' hlim1 hlimx hfin
  have hnn : 0 ≤ ε * (Ek μ ζ 1).det :=
    le_trans (mul_nonneg (Finset.prod_nonneg fun k _ => by positivity) (abs_nonneg _))
      (eps_det_Ek_ge hμ hμp hζ hζp)
  calc |(Ek μ ζ 1).det| = ε * (Ek μ ζ 1).det := by
        rw [← abs_of_nonneg hnn, abs_mul, hεabs, one_mul]
    _ ≤ (x ^ tri N)⁻¹ * (ε * (Ek μ ζ x).det) := hle
    _ ≤ (x ^ tri N)⁻¹ * |(Ek μ ζ x).det| := by
        gcongr
        calc ε * (Ek μ ζ x).det ≤ |ε * (Ek μ ζ x).det| := le_abs_self _
          _ = |(Ek μ ζ x).det| := by rw [abs_mul, hεabs, one_mul]

end

end Logs23

-- Source module: Logs23/Confluence

/-!
# Logs23 · from the exponential kernel to the confluent determinant `D(x) = det [(xζ_j)^κ e^{λ_l x ζ_j}]`

Rows `i : Fin (L * (K + 1))` correspond to pairs `(l, κ) ∈ Fin L × Fin (K + 1)` by `finProdFinEquiv`
(`i = κ + (K + 1) l`, lexicographic order, `l` major); `λ_l = (l + 1) log 2`; `μ_h i = λ_l + κ h`.
* `det [e^{μ_h i x ζ_j}] = h^σ · det [e^{λ_l x ζ_j} w_j^κ]`, `w_j = (e^{h x ζ_j} − 1)/h`, `σ = Σ_i κ`
  (a lower triangular change of rows);
* as `h → 0+`, the right-hand determinant tends to `D(x)`;
* `vprod μ_h ≥ h^σ ((log 2)/2)^(tri N)` for small `h`;
hence, from `Logs23/ExpKernel.lean`, for distinct positive `ζ_j`: `|D(1)| ≥ (∏ 1/m!) ((log 2)/2)^(tri N) |V(ζ)|`, and
`|D(1)| ≤ x^(−tri N) |D(x)|` for `x ≥ 1`.
-/

namespace Logs23

open Matrix Finset Filter Topology

open scoped Nat

noncomputable section

variable {L K : ℕ}

/-- The pair `(l, κ)` of a row. -/
abbrev pr (i : Fin (L * (K + 1))) : Fin L × Fin (K + 1) := finProdFinEquiv.symm i

theorem val_eq_pr (i : Fin (L * (K + 1))) : (i : ℕ) = ((pr i).2 : ℕ) + (K + 1) * ((pr i).1 : ℕ) := by
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply i]
  rfl

/-- `λ_l = (l + 1) log 2`. -/
def lam (l : Fin L) : ℝ := ((l : ℕ) + 1 : ℝ) * Real.log 2

/-- `μ_h i = λ_l + κ h`. -/
def muh (h : ℝ) (i : Fin (L * (K + 1))) : ℝ := lam (pr i).1 + ((pr i).2 : ℕ) * h

/-- `σ = Σ_i κ`. -/
def sig (L K : ℕ) : ℕ := ∑ i : Fin (L * (K + 1)), ((pr i).2 : ℕ)

/-- The confluent determinant `D(x) = det [(x ζ_j)^κ e^{λ_l x ζ_j}]`. -/
def Dc (ζ : Fin (L * (K + 1)) → ℝ) (x : ℝ) : ℝ :=
  (Matrix.of fun i j => (x * ζ j) ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * (x * ζ j))).det

/-- `w_h(z) = (e^{h z} − 1)/h`. -/
def wh (h z : ℝ) : ℝ := (Real.exp (h * z) - 1) / h

/-- The determinant after the triangular change of rows. -/
def Wd (ζ : Fin (L * (K + 1)) → ℝ) (h x : ℝ) : ℝ :=
  (Matrix.of fun i j => Real.exp (lam (pr i).1 * (x * ζ j)) * wh h (x * ζ j) ^ ((pr i).2 : ℕ)).det

/-! ## Order of the rows -/

/-- For `i < j`: either the block of `i` is earlier, or it is the same block with a smaller `κ`. -/
theorem lt_cases {i j : Fin (L * (K + 1))} (hij : i < j) :
    (pr i).1 < (pr j).1 ∨ ((pr i).1 = (pr j).1 ∧ (pr i).2 < (pr j).2) := by
  have hi := val_eq_pr i
  have hj := val_eq_pr j
  have hlt : (i : ℕ) < j := hij
  have hki := (pr i).2.2
  have hkj := (pr j).2.2
  rcases lt_trichotomy ((pr i).1 : ℕ) ((pr j).1 : ℕ) with h | h | h
  · exact Or.inl (Fin.lt_def.mpr h)
  · right
    refine ⟨Fin.ext h, Fin.lt_def.mpr ?_⟩
    rw [h] at hi
    omega
  · exfalso
    have : (K + 1) * ((pr j).1 : ℕ) + (K + 1) ≤ (K + 1) * ((pr i).1 : ℕ) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

/-! ## The triangular factorization -/

/-- The change of rows: `U[(l,κ),(l',ι)] = [l = l'] [ι ≤ κ] C(κ, ι) h^ι`. -/
def Um (h : ℝ) : Matrix (Fin (L * (K + 1))) (Fin (L * (K + 1))) ℝ := fun i i' =>
  if (pr i').1 = (pr i).1 ∧ (pr i').2 ≤ (pr i).2 then
    (((pr i).2 : ℕ).choose ((pr i').2 : ℕ) : ℝ) * h ^ ((pr i').2 : ℕ) else 0

theorem Um_lowerTriangular (h : ℝ) : (Um (L := L) (K := K) h).IsLowerTriangular := by
  intro i i' hii'
  have h' : i < i' := hii'
  simp only [Um]
  rw [if_neg]
  rintro ⟨hl, hk⟩
  rcases lt_cases h' with h1 | ⟨_, h2⟩
  · exact (lt_irrefl _) (hl ▸ h1)
  · exact (not_lt.mpr hk) h2

theorem det_Um (h : ℝ) : (Um (L := L) (K := K) h).det = h ^ sig L K := by
  rw [Matrix.det_of_isLowerTriangular _ (Um_lowerTriangular h), sig, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Um]

/-- The row sum giving the exponential back. -/
theorem sum_row (h z : ℝ) (hh : h ≠ 0) (i : Fin (L * (K + 1))) :
    ∑ i', Um h i i' * (Real.exp (lam (pr i').1 * z) * wh h z ^ ((pr i').2 : ℕ)) =
      Real.exp (muh h i * z) := by
  set q := (pr i).2 with hq
  set E := Real.exp (lam (pr i).1 * z) with hE
  -- pass to pairs; only the block of `i` contributes
  have h1 : ∑ i', Um h i i' * (Real.exp (lam (pr i').1 * z) * wh h z ^ ((pr i').2 : ℕ)) =
      ∑ ι : Fin (K + 1), (if ι ≤ q then ((q : ℕ).choose (ι : ℕ) : ℝ) * h ^ (ι : ℕ) else 0) *
        (E * wh h z ^ (ι : ℕ)) := by
    rw [← (finProdFinEquiv).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (pr i).1]
    · refine Finset.sum_congr rfl fun ι _ => ?_
      simp only [Um, pr, Equiv.symm_apply_apply, true_and, hq, hE]
    · intro l _ hl
      refine Finset.sum_eq_zero fun ι _ => ?_
      simp only [Um, pr, Equiv.symm_apply_apply]
      rw [if_neg (fun h' => hl h'.1), zero_mul]
    · simp
  have hqK : (q : ℕ) < K + 1 := q.2
  have h2 : ∑ ι : Fin (K + 1), (if ι ≤ q then ((q : ℕ).choose (ι : ℕ) : ℝ) * h ^ (ι : ℕ) else 0) *
        (E * wh h z ^ (ι : ℕ)) =
      ∑ m ∈ Finset.range (K + 1), (if m ≤ (q : ℕ) then ((q : ℕ).choose m : ℝ) * h ^ m else 0) *
        (E * wh h z ^ m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (if m ≤ (q : ℕ) then ((q : ℕ).choose m : ℝ) * h ^ m else 0) *
        (E * wh h z ^ m)) (K + 1)]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [Fin.le_def]
  have h3 : ∑ m ∈ Finset.range (K + 1), (if m ≤ (q : ℕ) then ((q : ℕ).choose m : ℝ) * h ^ m else 0) *
        (E * wh h z ^ m) =
      E * ∑ m ∈ Finset.range ((q : ℕ) + 1), (h * wh h z) ^ m * 1 ^ ((q : ℕ) - m) * ((q : ℕ).choose m : ℝ) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show (q : ℕ) + 1 ≤ K + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico ((q : ℕ) + 1) (K + 1)) (fun m hm => by
      rw [Finset.mem_Ico] at hm; rw [if_neg (by omega), zero_mul]), add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [if_pos (by omega), one_pow, mul_one, mul_pow]
    ring
  rw [h1, h2, h3, ← add_pow]
  have hw : h * wh h z + 1 = Real.exp (h * z) := by
    simp only [wh]; field_simp; ring
  rw [hw, ← Real.exp_nat_mul, hE, ← Real.exp_add, muh]
  congr 1
  rw [hq]
  ring

theorem conf_factor (ζ : Fin (L * (K + 1)) → ℝ) {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    (Ek (muh h) ζ x).det = h ^ sig L K * Wd ζ h x := by
  have hmat : Ek (muh h) ζ x = Um h * Matrix.of fun i j =>
      Real.exp (lam (pr i).1 * (x * ζ j)) * wh h (x * ζ j) ^ ((pr i).2 : ℕ) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Ek]
    exact (sum_row h (x * ζ j) hh i).symm
  rw [hmat, Matrix.det_mul, det_Um, Wd]

/-! ## The limit `h → 0` -/

theorem tendsto_wh (z : ℝ) : Tendsto (fun h => wh h z) (𝓝[≠] 0) (𝓝 z) := by
  have hd : HasDerivAt (fun t => Real.exp (t * z)) z 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const z).exp
    simpa using this
  have := hd.tendsto_slope_zero
  refine this.congr' (Eventually.of_forall fun t => ?_)
  simp [wh, smul_eq_mul, div_eq_inv_mul]

theorem tendsto_Wd (ζ : Fin (L * (K + 1)) → ℝ) (x : ℝ) :
    Tendsto (fun h => Wd ζ h x) (𝓝[≠] 0) (𝓝 (Dc ζ x)) := by
  have hmat : Tendsto (fun h => (Matrix.of fun i j =>
      Real.exp (lam (pr i).1 * (x * ζ j)) * wh h (x * ζ j) ^ ((pr i).2 : ℕ) :
        Matrix (Fin (L * (K + 1))) (Fin (L * (K + 1))) ℝ)) (𝓝[≠] 0)
      (𝓝 (Matrix.of fun i j => (x * ζ j) ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * (x * ζ j)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    simp only [Matrix.of_apply]
    rw [mul_comm ((x * ζ j) ^ _)]
    exact tendsto_const_nhds.mul ((tendsto_wh (x * ζ j)).pow _)
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-! ## The nodes `μ_h` -/

theorem muh_sub_of_lt {h : ℝ} (hh : 0 ≤ h) {i j : Fin (L * (K + 1))} (hij : i < j) :
    ((pr i).1 = (pr j).1 → h ≤ muh h j - muh h i) ∧
      ((pr i).1 ≠ (pr j).1 → Real.log 2 - K * h ≤ muh h j - muh h i) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkj : ((pr j).2 : ℕ) ≤ K := Nat.lt_succ_iff.mp (pr j).2.2
  have hki : ((pr i).2 : ℕ) ≤ K := Nat.lt_succ_iff.mp (pr i).2.2
  rcases lt_cases hij with h1 | ⟨h1, h2⟩
  · refine ⟨fun h' => absurd h' (ne_of_lt h1), fun _ => ?_⟩
    have hl : ((pr i).1 : ℕ) + 1 ≤ (pr j).1 := h1
    have hlr : ((pr i).1 : ℝ) + 1 ≤ (pr j).1 := by exact_mod_cast hl
    have hkr : (((pr j).2 : ℕ) : ℝ) ≥ 0 := by positivity
    have hkir : (((pr i).2 : ℕ) : ℝ) ≤ K := by exact_mod_cast hki
    simp only [muh, lam]
    nlinarith
  · refine ⟨fun _ => ?_, fun h' => absurd h1 h'⟩
    have hk : ((pr i).2 : ℕ) + 1 ≤ (pr j).2 := h2
    have hkr : (((pr i).2 : ℕ) : ℝ) + 1 ≤ ((pr j).2 : ℕ) := by exact_mod_cast hk
    simp only [muh, lam, h1]
    nlinarith

theorem muh_strictMono {h : ℝ} (hh : 0 < h) (hK : K * h < Real.log 2) :
    StrictMono (muh (L := L) (K := K) h) := by
  intro i j hij
  obtain ⟨h1, h2⟩ := muh_sub_of_lt hh.le hij
  by_cases hb : (pr i).1 = (pr j).1
  · linarith [h1 hb]
  · linarith [h2 hb]

theorem muh_pos {h : ℝ} (hh : 0 ≤ h) (i : Fin (L * (K + 1))) : 0 < muh (L := L) (K := K) h i := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [muh, lam]
  positivity

/-- `#{i < j in the block of j} ≤ κ_j`. -/
theorem card_same_le (j : Fin (L * (K + 1))) :
    ((Finset.Iio j).filter (fun i => (pr i).1 = (pr j).1)).card ≤ ((pr j).2 : ℕ) := by
  have : ((Finset.Iio j).filter (fun i => (pr i).1 = (pr j).1)).card ≤
      (Finset.Iio (pr j).2).card := by
    refine Finset.card_le_card_of_injOn (fun i => (pr i).2) (fun i hi => ?_) (fun a ha b hb hab => ?_)
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Iio] at hi
      rcases lt_cases hi.1 with h1 | ⟨_, h2⟩
      · exact absurd hi.2 (ne_of_lt h1)
      · simpa using h2
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Iio] at ha hb
      have hpa : pr a = pr b := Prod.ext (ha.2.trans hb.2.symm) hab
      exact finProdFinEquiv.symm.injective hpa
  simpa using this

theorem prod_Iio_eq_prod_Ioi {N : ℕ} (f : Fin N → Fin N → ℝ) :
    ∏ i : Fin N, ∏ j ∈ Ioi i, f i j = ∏ j : Fin N, ∏ i ∈ Iio j, f i j := by
  rw [show (∏ i : Fin N, ∏ j ∈ Ioi i, f i j) = ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 from
    Finset.prod_congr rfl fun i _ => by rw [← Finset.prod_filter]; congr 1; ext j; simp]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_filter]; congr 1; ext i; simp

/-- `vprod μ_h ≥ h^σ ((log 2)/2)^(tri N)` for `0 < h ≤ 1` and `K h ≤ (log 2)/2`. -/
theorem vprod_muh_ge {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (hK : K * h ≤ Real.log 2 / 2) :
    h ^ sig L K * (Real.log 2 / 2) ^ tri (L * (K + 1)) ≤ vprod (muh (L := L) (K := K) h) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set c := Real.log 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by linarith
  rw [vprod, prod_Iio_eq_prod_Ioi, sig, tri, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
  -- one column `j`
  set A := (Finset.Iio j).filter (fun i => (pr i).1 = (pr j).1) with hA
  set B := (Finset.Iio j).filter (fun i => ¬ (pr i).1 = (pr j).1) with hB
  have hfac : ∀ i ∈ Finset.Iio j,
      (if (pr i).1 = (pr j).1 then h else c) ≤ muh h j - muh h i := by
    intro i hi
    obtain ⟨hs, hx⟩ := muh_sub_of_lt hh.le (Finset.mem_Iio.mp hi)
    by_cases hb : (pr i).1 = (pr j).1
    · rw [if_pos hb]; exact hs hb
    · rw [if_neg hb]; have := hx hb; linarith
  have hprod : h ^ A.card * c ^ B.card ≤ ∏ i ∈ Finset.Iio j, (muh h j - muh h i) := by
    calc h ^ A.card * c ^ B.card = ∏ i ∈ Finset.Iio j, (if (pr i).1 = (pr j).1 then h else c) := by
          rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      _ ≤ ∏ i ∈ Finset.Iio j, (muh h j - muh h i) :=
          Finset.prod_le_prod (fun i _ => by split_ifs <;> positivity) hfac
  have hAc : A.card ≤ ((pr j).2 : ℕ) := card_same_le j
  have hBc : B.card ≤ (j : ℕ) := by
    calc B.card ≤ (Finset.Iio j).card := Finset.card_filter_le _ _
      _ = j := Fin.card_Iio j
  calc h ^ ((pr j).2 : ℕ) * c ^ (j : ℕ) ≤ h ^ A.card * c ^ B.card := by
        apply mul_le_mul (pow_le_pow_of_le_one hh.le h1 hAc) (pow_le_pow_of_le_one hc0.le hc1 hBc)
          (by positivity) (by positivity)
    _ ≤ _ := hprod

/-! ## The two bounds for `D` -/

theorem eventually_small : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h ≤ 1 ∧ (K : ℝ) * h ≤ Real.log 2 / 2 := by
  have hlog : 0 < Real.log 2 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have h1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have h2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min 1 ((Real.log 2 / 2) / (K + 1)) :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity))
  filter_upwards [h1, h2] with h ha hb
  refine ⟨ha, le_of_lt (lt_of_lt_of_le hb (min_le_left _ _)), ?_⟩
  have hb' : h < (Real.log 2 / 2) / (K + 1) := lt_of_lt_of_le hb (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hb'
  nlinarith

theorem tendsto_Wd_right (ζ : Fin (L * (K + 1)) → ℝ) (x : ℝ) :
    Tendsto (fun h => Wd ζ h x) (𝓝[>] 0) (𝓝 (Dc ζ x)) :=
  (tendsto_Wd ζ x).mono_left (nhdsGT_le_nhdsNE 0)

variable {ζ : Fin (L * (K + 1)) → ℝ}

/-- **Lower bound for `D(1)`.** -/
theorem abs_Dc_ge (hζ : Function.Injective ζ) (hζp : ∀ j, 0 < ζ j) :
    (∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri (L * (K + 1)) * |vprod ζ| ≤
      |Dc ζ 1| := by
  refine ge_of_tendsto (tendsto_Wd_right ζ 1).abs ?_
  filter_upwards [eventually_small (K := K)] with h ⟨hh, h1, hK⟩
  have hlog : Real.log 2 / 2 ≤ Real.log 2 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hmono := muh_strictMono (L := L) (K := K) hh (by nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)])
  have hE := abs_det_Ek_ge hmono.injective (muh_pos hh.le) hζ hζp
  rw [conf_factor ζ hh.ne' 1, abs_mul (h ^ sig L K), abs_of_pos (by positivity : (0:ℝ) < h ^ sig L K)] at hE
  have hV := vprod_muh_ge (L := L) (K := K) hh h1 hK
  have hσ : (0 : ℝ) < h ^ sig L K := by positivity
  have hVpos : 0 ≤ vprod (muh (L := L) (K := K) h) := le_trans (by positivity) hV
  have hfac : (0 : ℝ) ≤ ∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ)) := Finset.prod_nonneg fun k _ => by positivity
  rw [abs_mul (vprod (muh h)), abs_of_nonneg hVpos] at hE
  -- divide by `h^σ`
  have key : h ^ sig L K * ((∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) *
      (Real.log 2 / 2) ^ tri (L * (K + 1)) * |vprod ζ|) ≤ h ^ sig L K * |Wd ζ h 1| := by
    calc h ^ sig L K * ((∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) *
          (Real.log 2 / 2) ^ tri (L * (K + 1)) * |vprod ζ|)
        = (∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) *
          (h ^ sig L K * (Real.log 2 / 2) ^ tri (L * (K + 1))) * |vprod ζ| := by ring
      _ ≤ (∏ k : Fin (L * (K + 1)), (1 / ((k : ℕ)! : ℝ))) * vprod (muh h) * |vprod ζ| := by gcongr
      _ ≤ h ^ sig L K * |Wd ζ h 1| := by rw [mul_assoc]; exact hE
  exact le_of_mul_le_mul_left key hσ

/-- **Schwarz-type upper bound for `D(1)`.** -/
theorem abs_Dc_le (hζ : Function.Injective ζ) (hζp : ∀ j, 0 < ζ j) {x : ℝ} (hx : 1 ≤ x) :
    |Dc ζ 1| ≤ (x ^ tri (L * (K + 1)))⁻¹ * |Dc ζ x| := by
  refine le_of_tendsto_of_tendsto (tendsto_Wd_right ζ 1).abs
    (((tendsto_Wd_right ζ x).abs).const_mul _) ?_
  filter_upwards [eventually_small (K := K)] with h ⟨hh, h1, hK⟩
  have hmono := muh_strictMono (L := L) (K := K) hh (by nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)])
  have hE := abs_det_Ek_le hmono.injective (muh_pos hh.le) hζ hζp hx
  rw [conf_factor ζ hh.ne' 1, conf_factor ζ hh.ne' x, abs_mul (h ^ sig L K), abs_mul (h ^ sig L K),
    abs_of_pos (by positivity : (0:ℝ) < h ^ sig L K)] at hE
  have hσ : (0 : ℝ) < h ^ sig L K := by positivity
  have : h ^ sig L K * |Wd ζ h 1| ≤ h ^ sig L K * ((x ^ tri (L * (K + 1)))⁻¹ * |Wd ζ h x|) := by
    calc h ^ sig L K * |Wd ζ h 1| ≤ (x ^ tri (L * (K + 1)))⁻¹ * (h ^ sig L K * |Wd ζ h x|) := hE
      _ = h ^ sig L K * ((x ^ tri (L * (K + 1)))⁻¹ * |Wd ζ h x|) := by ring
  exact le_of_mul_le_mul_left this hσ

end

end Logs23

-- Source module: Logs23/Interpolation

/-!
# Logs23 · the integer interpolation determinant and bounds for determinants

Columns `j` carry natural numbers `r_j ≥ 1`, `s_j < S`; for natural numbers `b₁ ≥ 0`, `b₂ ≥ 1` put `θ = b₁/b₂`,
`ζ_j = r_j + s_j θ`, `Λ = b₁ log 2 − b₂ log 3`, `δ = −Λ/b₂`. The integer matrix
`M[(l,κ), j] = (r_j b₂ + s_j b₁)^κ (2^{r_j} 3^{s_j})^{l+1}` satisfies `det M = b₂^σ G(δ)`,
`G(t) = det [ζ_j^κ e^{λ_l ζ_j} e^{(l+1) s_j t}]` (`λ_l = (l+1) log 2`). With the bounds of `Logs23/Confluence.lean`
and a perturbation bound, a condition `(P)` on the parameters gives an explicit lower bound for `|Λ|`
(`prop_main`, in `Logs23/Proposition.lean`).
-/

namespace Logs23

open Matrix Finset

open scoped Nat

noncomputable section

/-! ## Bounds for determinants -/

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {M D : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) (hd : ∀ i ∈ s, |a i - b i| ≤ D) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * M ^ (s.card - 1) * D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, |a i| ≤ M := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ M := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, |a i - b i| ≤ D := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hD : 0 ≤ D := le_trans (abs_nonneg _) (hd x (Finset.mem_insert_self x s))
    have hpb : |∏ i ∈ s, b i| ≤ M ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s, |b i| ≤ ∏ _i ∈ s, M := Finset.prod_le_prod (fun i _ => abs_nonneg _) hb'
        _ = M ^ s.card := Finset.prod_const _
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    have key : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    rw [key]
    have h1 := ha x (Finset.mem_insert_self x s)
    have h2 := hd x (Finset.mem_insert_self x s)
    have ih' := ih ha' hb' hd'
    calc |a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i|
        ≤ |a x| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a x - b x| * |∏ i ∈ s, b i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ M * (s.card * M ^ (s.card - 1) * D) + D * M ^ s.card := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * M ^ (s.card + 1 - 1) * D := by
          rcases Nat.eq_zero_or_pos s.card with h0 | h0
          · rw [h0]; simp
          · have : M * M ^ (s.card - 1) = M ^ s.card := by
              rw [← pow_succ']; congr 1; omega
            rw [Nat.add_sub_cancel]
            push_cast
            have e : M * (↑s.card * M ^ (s.card - 1) * D) + D * M ^ s.card =
                (↑s.card + 1) * M ^ s.card * D := by rw [← this]; ring
            rw [e]

/-- `|det A − det B| ≤ N · N! · M^(N−1) · D` when all entries are bounded by `M` and differ by at most `D`. -/
theorem abs_det_sub_det_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) {M D : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) (hB : ∀ i j, |B i j| ≤ M) (hd : ∀ i j, |A i j - B i j| ≤ D) :
    |A.det - B.det| ≤ N * N ! * M ^ (N - 1) * D := by
  rw [det_apply', det_apply', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin N), |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A (σ i) i -
      (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i| ≤ N * M ^ (N - 1) * D := by
    intro σ
    rw [← mul_sub, abs_mul]
    have hs : |((↑↑(Equiv.Perm.sign σ) : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hs, one_mul]
    have := abs_prod_sub_prod_le (Finset.univ : Finset (Fin N)) (fun i => A (σ i) i) (fun i => B (σ i) i) hM
      (fun i _ => hA _ _) (fun i _ => hB _ _) (fun i _ => hd _ _)
    simpa using this
  calc ∑ σ : Equiv.Perm (Fin N), |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A (σ i) i -
        (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i|
      ≤ ∑ _σ : Equiv.Perm (Fin N), (N * M ^ (N - 1) * D : ℝ) := Finset.sum_le_sum fun σ _ => hterm σ
    _ = N * N ! * M ^ (N - 1) * D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `|det A| ≤ N! · M^N` when all entries are bounded by `M`. -/
theorem abs_det_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) {M : ℝ} (hA : ∀ i j, |A i j| ≤ M) :
    |A.det| ≤ N ! * M ^ N := by
  have := Matrix.det_le (abv := AbsoluteValue.abs) hA
  simpa [nsmul_eq_mul] using this

/-! ## The integer matrix -/

variable {L K : ℕ}

/-- The real model `G(t)`. -/
def Gt (rr ss : Fin (L * (K + 1)) → ℕ) (θ t : ℝ) : ℝ :=
  (Matrix.of fun i j => ((rr j : ℝ) + ss j * θ) ^ ((pr i).2 : ℕ) *
    Real.exp (lam (pr i).1 * ((rr j : ℝ) + ss j * θ)) * Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * t)).det

/-- The integer matrix. -/
def Mint (rr ss : Fin (L * (K + 1)) → ℕ) (b₁ b₂ : ℕ) : Matrix (Fin (L * (K + 1))) (Fin (L * (K + 1))) ℤ :=
  Matrix.of fun i j => ((rr j * b₂ + ss j * b₁ : ℕ) : ℤ) ^ ((pr i).2 : ℕ) * (2 ^ rr j * 3 ^ ss j : ℤ) ^ (((pr i).1 : ℕ) + 1)

theorem det_Mint (rr ss : Fin (L * (K + 1)) → ℕ) (b₁ b₂ : ℕ) (hb₂ : 0 < b₂) :
    ((Mint rr ss b₁ b₂).det : ℝ) = (b₂ : ℝ) ^ sig L K *
      Gt rr ss ((b₁ : ℝ) / b₂) (-((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂) := by
  have hb : (b₂ : ℝ) ≠ 0 := by exact_mod_cast hb₂.ne'
  have hmd := RingHom.map_det (Int.castRingHom ℝ) (Mint rr ss b₁ b₂)
  simp only [eq_intCast] at hmd
  rw [hmd]
  have hmat : (Int.castRingHom ℝ).mapMatrix (Mint rr ss b₁ b₂) = Matrix.of fun i j =>
      (b₂ : ℝ) ^ ((pr i).2 : ℕ) * (Matrix.of fun i j => ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂)) ^ ((pr i).2 : ℕ) *
        Real.exp (lam (pr i).1 * ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂))) *
        Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j *
          (-((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂))) i j := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Mint, Matrix.of_apply, eq_intCast, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    push_cast
    -- `(r b₂ + s b₁)^κ = b₂^κ ζ^κ` and `(2^r 3^s)^(l+1) = e^{λ_l ζ} e^{(l+1) s δ}`
    have hz : ((rr j : ℝ) * b₂ + ss j * b₁) = b₂ * ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂)) := by
      field_simp
    have he : ((2 : ℝ) ^ rr j * 3 ^ ss j) ^ (((pr i).1 : ℕ) + 1) =
        Real.exp (lam (pr i).1 * ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂))) *
        Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * (-((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂)) := by
      rw [← Real.exp_add, ← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ rr j * 3 ^ ss j) ^ (((pr i).1 : ℕ) + 1))]
      congr 1
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, lam]
      field_simp
      push_cast
      ring
    rw [hz, mul_pow, he]
    ring
  rw [hmat, det_mul_column, Finset.prod_pow_eq_pow_sum, sig, Gt]

theorem Gt_zero (rr ss : Fin (L * (K + 1)) → ℕ) (θ : ℝ) :
    Gt rr ss θ 0 = Dc (fun j => (rr j : ℝ) + ss j * θ) 1 := by
  simp [Gt, Dc]

/-! ## The perturbation bound -/

/-- Entry bound `X(x) = (x ζ_max)^K e^{λ_max x ζ_max}`. -/
def Xb (K : ℕ) (lmax zmax x : ℝ) : ℝ := (x * zmax) ^ K * Real.exp (lmax * x * zmax)

theorem entry_le {κ : ℕ} (hκ : κ ≤ K) {lam0 lmax z zmax x : ℝ} (hx : 1 ≤ x) (hz1 : 1 ≤ z) (hz : z ≤ zmax)
    (hl0 : 0 ≤ lam0) (hl : lam0 ≤ lmax) :
    |(x * z) ^ κ * Real.exp (lam0 * (x * z))| ≤ Xb K lmax zmax x := by
  have hxz : 1 ≤ x * z := one_le_mul_of_one_le_of_one_le hx hz1
  rw [abs_of_nonneg (by positivity), Xb]
  apply mul_le_mul
  · calc (x * z) ^ κ ≤ (x * z) ^ K := pow_le_pow_right₀ hxz hκ
      _ ≤ (x * zmax) ^ K := pow_le_pow_left₀ (by linarith) (by nlinarith) K
  · apply Real.exp_le_exp.mpr
    have : x * z ≤ x * zmax := by nlinarith
    calc lam0 * (x * z) ≤ lmax * (x * z) := by nlinarith
      _ ≤ lmax * (x * zmax) := by nlinarith [le_trans hl0 hl]
      _ = lmax * x * zmax := by ring
  · positivity
  · exact pow_nonneg (by nlinarith) K

end

end Logs23

-- Source module: Logs23/Proposition

/-!
# Logs23 · the main inequality (step 2b; outline in `README.md`)

For points `ζ_j = r_j + s_j b₁/b₂` with `r_j ≥ 1`, `s_j < S` and the integers `r_j b₂ + s_j b₁` distinct, bounds
`ζ_j ≤ ζ_max`, `λ_l ≤ λ_max`, `L S |Λ|/b₂ ≤ 1`, and `x ≥ 1`: if the parameters satisfy the condition `(P)`, then
`|Λ| ≥ b₂ T' / (N · N! · (3 X(1))^N · L S)`, `T' = (∏_{k<N} 1/k!) ((log 2)/2)^(tri N) |V(ζ)|`.
The case `det M = 0` is not excluded: it is harmless because `|G(0)| ≥ T' > 0`.
-/

namespace Logs23

open Matrix Finset

open scoped Nat

noncomputable section

variable {L K : ℕ}

/-- The leading lower bound `T'`. -/
def Tlow (N : ℕ) (ζ : Fin N → ℝ) : ℝ :=
  (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri N * |vprod ζ|

theorem prop_main (rr ss : Fin (L * (K + 1)) → ℕ) (b₁ b₂ S : ℕ) (hb₂ : 0 < b₂)
    (hr : ∀ j, 1 ≤ rr j) (hs : ∀ j, ss j < S)
    (hinj : Function.Injective fun j => rr j * b₂ + ss j * b₁)
    {zmax lmax : ℝ} (hz : ∀ j, (rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂) ≤ zmax)
    (hlmax : ∀ l : Fin L, lam l ≤ lmax)
    (hδ : (L : ℝ) * S * |((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂| ≤ 1)
    {x : ℝ} (hx : 1 ≤ x)
    (hP : ((L * (K + 1) : ℕ) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1)) / x ^ tri (L * (K + 1)) ≤
      1 / (2 * (b₂ : ℝ) ^ sig L K)) :
    (b₂ : ℝ) * Tlow (L * (K + 1)) (fun j => (rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂)) /
        ((L * (K + 1) : ℕ) * ((L * (K + 1) : ℕ) ! : ℝ) * (3 * Xb K lmax zmax 1) ^ (L * (K + 1)) * (L * S)) ≤
      |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| := by
  set θ : ℝ := (b₁ : ℝ) / b₂ with hθ
  set ζ : Fin (L * (K + 1)) → ℝ := fun j => (rr j : ℝ) + ss j * θ with hζ
  set Λ : ℝ := (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 with hΛ
  set δ : ℝ := -Λ / b₂ with hδdef
  have hb : (0 : ℝ) < b₂ := by exact_mod_cast hb₂
  have hθ0 : 0 ≤ θ := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the points
  have hζ1 : ∀ j, 1 ≤ ζ j := fun j => by
    have : (1 : ℝ) ≤ rr j := by exact_mod_cast hr j
    simp only [hζ]; nlinarith [(Nat.cast_nonneg (ss j) : (0 : ℝ) ≤ ss j)]
  have hζp : ∀ j, 0 < ζ j := fun j => lt_of_lt_of_le one_pos (hζ1 j)
  have hζinj : Function.Injective ζ := by
    intro i j hij
    apply hinj
    have : ((rr i * b₂ + ss i * b₁ : ℕ) : ℝ) = ((rr j * b₂ + ss j * b₁ : ℕ) : ℝ) := by
      push_cast
      have h2 : (rr i : ℝ) * b₂ + ss i * b₁ = b₂ * ζ i := by simp only [hζ, hθ]; field_simp
      have h3 : (rr j : ℝ) * b₂ + ss j * b₁ = b₂ * ζ j := by simp only [hζ, hθ]; field_simp
      rw [h2, h3, hij]
    exact_mod_cast this
  have hlam0 : ∀ l : Fin L, 0 ≤ lam l := fun l => by simp only [lam]; positivity
  -- `|G(0)| ≤ 1/(2 b₂^σ)`
  have hG0 : Gt rr ss θ 0 = Dc ζ 1 := Gt_zero rr ss θ
  have hDx : |Dc ζ x| ≤ ((L * (K + 1)) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1)) := by
    apply abs_det_le
    intro i j
    simp only [Matrix.of_apply]
    exact entry_le (Nat.lt_succ_iff.mp (pr i).2.2) hx (hζ1 j) (hz j) (hlam0 _) (hlmax _)
  have hup : |Gt rr ss θ 0| ≤ 1 / (2 * (b₂ : ℝ) ^ sig L K) := by
    rw [hG0]
    calc |Dc ζ 1| ≤ (x ^ tri (L * (K + 1)))⁻¹ * |Dc ζ x| := abs_Dc_le hζinj hζp hx
      _ ≤ (x ^ tri (L * (K + 1)))⁻¹ * (((L * (K + 1)) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1))) := by gcongr
      _ = ((L * (K + 1)) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1)) / x ^ tri (L * (K + 1)) := by ring
      _ ≤ _ := hP
  -- `|G(δ) − G(0)| ≥ |G(0)|`
  have hdet := det_Mint rr ss b₁ b₂ hb₂
  have hsep : |Gt rr ss θ 0| ≤ |Gt rr ss θ δ - Gt rr ss θ 0| := by
    by_cases hM : (Mint rr ss b₁ b₂).det = 0
    · have : Gt rr ss θ δ = 0 := by
        have h' : (b₂ : ℝ) ^ sig L K * Gt rr ss θ δ = 0 := by
          rw [← hdet]; simp [hM]
        rcases mul_eq_zero.mp h' with h | h
        · exact absurd h (by positivity)
        · exact h
      rw [this, zero_sub, abs_neg]
    · have h1 : (1 : ℝ) ≤ |((Mint rr ss b₁ b₂).det : ℝ)| := by exact_mod_cast Int.one_le_abs hM
      rw [hdet, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b₂ : ℝ) ^ sig L K)] at h1
      have hσ : (0 : ℝ) < (b₂ : ℝ) ^ sig L K := by positivity
      have hGd : 1 / (b₂ : ℝ) ^ sig L K ≤ |Gt rr ss θ δ| := by
        rw [div_le_iff₀ hσ]; linarith
      have : |Gt rr ss θ δ| - |Gt rr ss θ 0| ≤ |Gt rr ss θ δ - Gt rr ss θ 0| := abs_sub_abs_le_abs_sub _ _
      have h2 : 1 / (2 * (b₂ : ℝ) ^ sig L K) = (1 / (b₂ : ℝ) ^ sig L K) / 2 := by ring
      rw [h2] at hup
      linarith
  -- `|G(0)| ≥ T'`
  have hlow : Tlow (L * (K + 1)) ζ ≤ |Gt rr ss θ 0| := by
    rw [hG0, Tlow]; exact abs_Dc_ge hζinj hζp
  -- the perturbation bound
  rcases Nat.eq_zero_or_pos (L * (K + 1)) with hN0 | hNpos
  · -- no rows: the left side is `0`
    have : (((L * (K + 1)) : ℕ) : ℝ) = 0 := by exact_mod_cast hN0
    rw [this, zero_mul, zero_mul, zero_mul, div_zero]
    exact abs_nonneg _
  set X1 := Xb K lmax zmax 1 with hX1
  have j0 : Fin (L * (K + 1)) := ⟨0, hNpos⟩
  have hzmax : 1 ≤ zmax := le_trans (hζ1 j0) (hz j0)
  have hX1p : 0 < X1 := by
    simp only [hX1, Xb]; exact mul_pos (pow_pos (by linarith) K) (Real.exp_pos _)
  have hentry : ∀ i j : Fin (L * (K + 1)), |ζ j ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * ζ j)| ≤ X1 := by
    intro i j
    have := entry_le (Nat.lt_succ_iff.mp (pr i).2.2) le_rfl (hζ1 j) (hz j) (hlam0 (pr i).1) (hlmax (pr i).1)
    simpa using this
  have hcoef : ∀ i j : Fin (L * (K + 1)), |((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ)| ≤ (L : ℝ) * S * |δ| := by
    intro i j
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((pr i).1 : ℕ) + 1),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ss j)]
    have h1 : (((pr i).1 : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast (pr i).1.2
    have h2 : (ss j : ℝ) ≤ S := by exact_mod_cast (hs j).le
    have := abs_nonneg δ
    calc (((pr i).1 : ℕ) + 1 : ℝ) * ss j * |δ| ≤ L * ss j * |δ| := by gcongr
      _ ≤ L * S * |δ| := by gcongr
  have hδ' : (L : ℝ) * S * |δ| ≤ 1 := by
    rw [hδdef, neg_div, abs_neg]; exact hδ
  have hpert : |Gt rr ss θ δ - Gt rr ss θ 0| ≤
      ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1 * ((L : ℝ) * S * |δ|)) := by
    unfold Gt
    apply abs_det_sub_det_le
    · positivity
    · intro i j
      simp only [Matrix.of_apply]
      rw [abs_mul]
      have he : |Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ)| ≤ 3 := by
        rw [abs_of_pos (Real.exp_pos _)]
        calc Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ) ≤ Real.exp 1 :=
              Real.exp_le_exp.mpr (le_trans (le_abs_self _) ((hcoef i j).trans hδ'))
          _ ≤ 3 := Real.exp_one_lt_three.le
      calc |ζ j ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * ζ j)| *
            |Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ)| ≤ X1 * 3 :=
            mul_le_mul (hentry i j) he (abs_nonneg _) hX1p.le
        _ = 3 * X1 := by ring
    · intro i j
      simp only [Matrix.of_apply, mul_zero, Real.exp_zero, mul_one]
      linarith [hentry i j]
    · intro i j
      simp only [Matrix.of_apply, mul_zero, Real.exp_zero, mul_one]
      rw [← mul_sub_one, abs_mul]
      have hu := Real.abs_exp_sub_one_le ((hcoef i j).trans hδ')
      calc |ζ j ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * ζ j)| *
            |Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ) - 1|
          ≤ X1 * (2 * |(((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ|) :=
            mul_le_mul (hentry i j) hu (abs_nonneg _) hX1p.le
        _ ≤ X1 * (2 * ((L : ℝ) * S * |δ|)) := by gcongr; exact hcoef i j
        _ = 2 * X1 * ((L : ℝ) * S * |δ|) := by ring
  have hpow : (3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1) ≤ (3 * X1) ^ (L * (K + 1)) := by
    have : (3 * X1) ^ (L * (K + 1)) = (3 * X1) ^ ((L * (K + 1)) - 1) * (3 * X1) := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    gcongr
    linarith
  have hchain : Tlow (L * (K + 1)) ζ ≤ ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) * (|Λ| / b₂) := by
    have h1 := hlow.trans (hsep.trans hpert)
    have hδabs : |δ| = |Λ| / b₂ := by rw [hδdef, neg_div, abs_neg, abs_div, abs_of_pos hb]
    rw [hδabs] at h1
    calc Tlow (L * (K + 1)) ζ ≤ ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1 * ((L : ℝ) * S * (|Λ| / b₂))) := h1
      _ = ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * ((3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1)) * ((L : ℝ) * S * (|Λ| / b₂)) := by ring
      _ ≤ ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S * (|Λ| / b₂)) := by
          gcongr
      _ = ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) * (|Λ| / b₂) := by ring
  -- conclusion
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, zero_mul] at hNpos; exact absurd hNpos (lt_irrefl 0)
    · exact h
  have hSpos : 0 < S := lt_of_le_of_lt (Nat.zero_le _) (hs j0)
  have hden : 0 < ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) := by
    have : (0 : ℝ) < (L * (K + 1)) := by exact_mod_cast hNpos
    have : (0 : ℝ) < L := by exact_mod_cast hLpos
    have : (0 : ℝ) < S := by exact_mod_cast hSpos
    positivity
  rw [div_le_iff₀ hden]
  have := mul_le_mul_of_nonneg_left hchain hb.le
  calc (b₂ : ℝ) * Tlow (L * (K + 1)) ζ ≤ b₂ * (((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) * (|Λ| / b₂)) := this
    _ = |Λ| * (((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S)) := by field_simp

end

end Logs23

-- Source module: Logs23/Constantes

/-!
# Logs23 · the constants of step 2b, for every `ν ≥ 335`

Parameters: `L = ν`, `K + 1 = 2^15 ν`, `N = L (K + 1)`, `S = 2^7 ν`, `ζ_max = 2^9 ν`, `λ_max = ν log 2`, `x = 16`.
* `cond_P`: the condition `(P)` of `prop_main` holds for every `0 < b₂ < 2^ν`;
* `final_ge`: `b₂ T' / (N N! (3 X(1))^N L S) ≥ exp(−10^12 ν^5)` whenever `0 < b₂ < 2^ν` and
  `T' ≥ (∏ 1/k!) ((log 2)/2)^(tri N) b₂^(−N²)`.
The proofs take logarithms and use `log ν ≤ ν/50 + 3`, `0.6931 < log 2 < 0.6932`, `n! ≤ n^n`, `σ ≤ N K`,
`tri N = N (N − 1)/2`, then polynomial inequalities in `ν`.
-/

namespace Logs23

open Finset Real

open scoped Nat

noncomputable section

/-! ## Elementary bounds -/

theorem log_le_div50 {v : ℝ} (hv : 0 < v) : Real.log v ≤ v / 50 + 3 := by
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < v / 50)
  have h2 : Real.log v = Real.log 50 + Real.log (v / 50) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have h3 : Real.log 50 < 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (50 : ℝ) < 2.7182818283 ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  linarith

theorem log_factorial_le (n : ℕ) : Real.log (n ! : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have h1 : ((n ! : ℕ) : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow n
  calc Real.log (n ! : ℝ) ≤ Real.log ((n ^ n : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    _ = n * Real.log n := by push_cast; rw [Real.log_pow]

theorem tri_eq (N : ℕ) : (tri N : ℝ) = N * (N - 1) / 2 := by
  have h : (∑ i ∈ Finset.range N, i) * 2 = N * (N - 1) := Finset.sum_range_id_mul_two N
  have h' : tri N = ∑ i ∈ Finset.range N, i := by
    rw [tri, Fin.sum_univ_eq_sum_range (fun i => i) N]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp [tri]
  have hc : ((tri N * 2 : ℕ) : ℝ) = ((N * (N - 1) : ℕ) : ℝ) := by rw [h', h]
  push_cast [Nat.cast_sub (show 1 ≤ N from h0)] at hc
  linarith

theorem tri_le (N : ℕ) : (tri N : ℝ) ≤ (N : ℝ) ^ 2 := by
  rw [tri_eq]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem sig_le (L K : ℕ) : (sig L K : ℝ) ≤ (L * (K + 1) : ℕ) * K := by
  have : sig L K ≤ (L * (K + 1)) * K := by
    calc sig L K = ∑ i : Fin (L * (K + 1)), ((pr i).2 : ℕ) := rfl
      _ ≤ ∑ _i : Fin (L * (K + 1)), K := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (pr i).2.2
      _ = (L * (K + 1)) * K := by simp
  exact_mod_cast this

/-! ## The parameters -/

/-- `K = 2^15 ν − 1`. -/
def Kp (ν : ℕ) : ℕ := 2 ^ 15 * ν - 1

theorem Kp_succ {ν : ℕ} (hν : 1 ≤ ν) : Kp ν + 1 = 2 ^ 15 * ν := by
  unfold Kp; have : 1 ≤ 2 ^ 15 * ν := by omega
  omega

theorem N_eq {ν : ℕ} (hν : 1 ≤ ν) : ((ν * (Kp ν + 1) : ℕ) : ℝ) = 2 ^ 15 * (ν : ℝ) ^ 2 := by
  rw [Kp_succ hν]; push_cast; ring

theorem K_le {ν : ℕ} : (Kp ν : ℝ) ≤ 2 ^ 15 * ν := by
  have : Kp ν ≤ 2 ^ 15 * ν := Nat.sub_le _ _
  exact_mod_cast this

/-! ## The condition (P) -/

/-- The polynomial inequality behind `(P)`. -/
theorem poly_P {v ℓ t : ℝ} (hv : 335 ≤ v) (hℓ : ℓ ≤ v / 50 + 3) (_hℓ0 : 0 ≤ ℓ) (ht0 : 0.6931 < t)
    (ht1 : t < 0.6932) :
    2 ^ 15 * v ^ 2 * (15 * t + 2 * ℓ) + 2 ^ 15 * v ^ 2 * (2 ^ 15 * v * (13 * t + ℓ) + 2 ^ 13 * v ^ 2 * t)
      - 2 ^ 15 * v ^ 2 * (2 ^ 15 * v ^ 2 - 1) / 2 * (4 * t) + t
      + 2 ^ 15 * v ^ 2 * (2 ^ 15 * v) * (v * t) ≤ 0 := by
  have hv0 : 0 < v := by linarith
  have h3 : v ^ 3 * 335 ≤ v ^ 4 := by nlinarith [pow_pos hv0 3]
  nlinarith [pow_pos hv0 2, pow_pos hv0 3, pow_pos hv0 4, mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 3).le,
    mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 2).le]

theorem cond_P {ν : ℕ} (hν : 335 ≤ ν) {b₂ : ℕ} (hb : 0 < b₂) (hb₂ : (b₂ : ℝ) < 2 ^ ν) :
    (((ν * (Kp ν + 1)) ! : ℕ) : ℝ) * Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16 ^ (ν * (Kp ν + 1)) /
        16 ^ tri (ν * (Kp ν + 1)) ≤ 1 / (2 * (b₂ : ℝ) ^ sig ν (Kp ν)) := by
  set N := ν * (Kp ν + 1) with hN
  have hν1 : 1 ≤ ν := by omega
  have hv : (335 : ℝ) ≤ ν := by exact_mod_cast hν
  have hv0 : (0 : ℝ) < ν := by linarith
  have hNr : (N : ℝ) = 2 ^ 15 * (ν : ℝ) ^ 2 := N_eq hν1
  have hN0 : (0 : ℝ) < N := by rw [hNr]; positivity
  have ht0 := Real.log_two_gt_d9
  have ht1 := Real.log_two_lt_d9
  have hb0 : (0 : ℝ) < b₂ := by exact_mod_cast hb
  -- both sides are positive; compare logarithms
  have hX : 0 < Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16 := by unfold Xb; positivity
  have hL : 0 < ((N ! : ℕ) : ℝ) * Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16 ^ N / 16 ^ tri N := by
    have := Nat.factorial_pos N; positivity
  have hR : 0 < 1 / (2 * (b₂ : ℝ) ^ sig ν (Kp ν)) := by positivity
  rw [← Real.log_le_log_iff hL hR]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by have := Nat.factorial_pos N; positivity)
    (by positivity), Real.log_pow, Real.log_pow, Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hXlog : Real.log (Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 16) =
      Kp ν * (13 * Real.log 2 + Real.log ν) + 2 ^ 13 * (ν : ℝ) ^ 2 * Real.log 2 := by
    unfold Xb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp,
      show (16 : ℝ) * (2 ^ 9 * ν) = 2 ^ 13 * ν by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  rw [hXlog]
  have hfact := log_factorial_le N
  have hlogN : Real.log N = 15 * Real.log 2 + 2 * Real.log ν := by
    rw [hNr, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have hlogb : Real.log b₂ ≤ ν * Real.log 2 := by
    have := Real.log_lt_log hb0 hb₂
    rw [Real.log_pow] at this; linarith
  have hlogb0 : 0 ≤ Real.log b₂ := Real.log_nonneg (by exact_mod_cast hb)
  have hsig := sig_le ν (Kp ν)
  have hK := K_le (ν := ν)
  have hK0 : (0 : ℝ) ≤ Kp ν := Nat.cast_nonneg _
  have hℓ := log_le_div50 hv0
  have hℓ0 : 0 ≤ Real.log ν := Real.log_nonneg (by linarith)
  have htri := tri_eq N
  rw [hlog16, htri]
  have hP := poly_P hv hℓ hℓ0 (by linarith : (0.6931 : ℝ) < Real.log 2) (by linarith : Real.log 2 < 0.6932)
  rw [hlogN] at hfact
  rw [hNr] at hfact hsig htri ⊢
  -- assemble
  have e1 : (sig ν (Kp ν) : ℝ) * Real.log b₂ ≤ 2 ^ 15 * (ν : ℝ) ^ 2 * (2 ^ 15 * ν) * (ν * Real.log 2) := by
    have hs0 : (0 : ℝ) ≤ sig ν (Kp ν) := Nat.cast_nonneg _
    calc (sig ν (Kp ν) : ℝ) * Real.log b₂ ≤ (2 ^ 15 * (ν : ℝ) ^ 2 * Kp ν) * (ν * Real.log 2) :=
          mul_le_mul hsig hlogb hlogb0 (by positivity)
      _ ≤ 2 ^ 15 * (ν : ℝ) ^ 2 * (2 ^ 15 * ν) * (ν * Real.log 2) := by gcongr
  have e2 : 2 ^ 15 * (ν : ℝ) ^ 2 * (Kp ν * (13 * Real.log 2 + Real.log ν) + 2 ^ 13 * (ν : ℝ) ^ 2 * Real.log 2) ≤
      2 ^ 15 * (ν : ℝ) ^ 2 * (2 ^ 15 * ν * (13 * Real.log 2 + Real.log ν) + 2 ^ 13 * (ν : ℝ) ^ 2 * Real.log 2) := by
    have : (0 : ℝ) ≤ 13 * Real.log 2 + Real.log ν := by linarith
    gcongr
  nlinarith

/-! ## The final bound -/

/-- The polynomial inequality behind the final bound (`N = 2^15 v²`, `log N = 15 t + 2 ℓ`, `t = log 2`,
`u = log 3`, `ℓ = log ν`). -/
theorem poly_final {v ℓ t : ℝ} (hv : 335 ≤ v) (hℓ : ℓ ≤ v / 50 + 3) (_hℓ0 : 0 ≤ ℓ) (ht0 : 0.6931 < t)
    (ht1 : t < 0.6932) (u : ℝ) (_hu0 : 0 ≤ u) (hu : u ≤ 2) :
    (15 * t + 2 * ℓ) + 2 ^ 15 * v ^ 2 * (15 * t + 2 * ℓ)
      + 2 ^ 15 * v ^ 2 * (u + (2 ^ 15 * v * (9 * t + ℓ) + v * t * (2 ^ 9 * v))) + (7 * t + 2 * ℓ)
      + 2 ^ 15 * v ^ 2 * (2 ^ 15 * v ^ 2 * (15 * t + 2 * ℓ)) + (2 ^ 15 * v ^ 2) ^ 2 * u
      + (2 ^ 15 * v ^ 2) ^ 2 * (v * t) ≤ 10 ^ 12 * v ^ 5 := by
  have hv0 : 0 < v := by linarith
  nlinarith [pow_pos hv0 2, pow_pos hv0 3, pow_pos hv0 4, pow_pos hv0 5,
    mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 4).le, mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 2).le,
    mul_le_mul_of_nonneg_left hℓ (pow_pos hv0 3).le]

theorem log_three_le : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  calc (3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
    _ ≤ Real.exp 1 ^ 2 := by gcongr
    _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num

/-- **The final bound.** -/
theorem final_ge {ν : ℕ} (hν : 335 ≤ ν) {b₂ : ℕ} (hb : 0 < b₂) (hb₂ : (b₂ : ℝ) < 2 ^ ν) {T : ℝ}
    (hT : (∏ k : Fin (ν * (Kp ν + 1)), (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri (ν * (Kp ν + 1)) *
      (1 / (b₂ : ℝ)) ^ ((ν * (Kp ν + 1)) ^ 2) ≤ T) :
    Real.exp (-(10 ^ 12 * (ν : ℝ) ^ 5)) ≤
      (b₂ : ℝ) * T / (((ν * (Kp ν + 1) : ℕ) : ℝ) * (((ν * (Kp ν + 1)) ! : ℕ) : ℝ) *
        (3 * Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 1) ^ (ν * (Kp ν + 1)) * ((ν : ℝ) * (2 ^ 7 * ν : ℕ))) := by
  set N := ν * (Kp ν + 1) with hN
  have hν1 : 1 ≤ ν := by omega
  have hv : (335 : ℝ) ≤ ν := by exact_mod_cast hν
  have hv0 : (0 : ℝ) < ν := by linarith
  have hNr : (N : ℝ) = 2 ^ 15 * (ν : ℝ) ^ 2 := N_eq hν1
  have hN0 : (0 : ℝ) < N := by rw [hNr]; positivity
  have ht0 := Real.log_two_gt_d9
  have ht1 := Real.log_two_lt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  have hb0 : (0 : ℝ) < b₂ := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b₂ := by exact_mod_cast hb
  set X1 := Xb (Kp ν) (ν * Real.log 2) (2 ^ 9 * ν) 1 with hX1
  have hX1p : 0 < X1 := by unfold Xb at hX1; rw [hX1]; positivity
  set c := Real.log 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  set T0 := (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * c ^ tri N * (1 / (b₂ : ℝ)) ^ (N ^ 2) with hT0
  have hT0p : 0 < T0 := by
    have : 0 < ∏ k : Fin N, (1 / ((k : ℕ)! : ℝ)) := Finset.prod_pos fun k _ => by positivity
    positivity
  set den := (N : ℝ) * ((N ! : ℕ) : ℝ) * (3 * X1) ^ N * ((ν : ℝ) * (2 ^ 7 * ν : ℕ)) with hden
  have hdenp : 0 < den := by have := Nat.factorial_pos N; positivity
  -- `log den − log T0 ≤ 10^12 ν^5`
  have hℓ := log_le_div50 hv0
  have hℓ0 : 0 ≤ Real.log ν := Real.log_nonneg (by linarith)
  have hlogN : Real.log N = 15 * Real.log 2 + 2 * Real.log ν := by
    rw [hNr, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have hfactN := log_factorial_le N
  have hlogT0 : -((N : ℝ) * ((N : ℝ) * Real.log N)) - (N : ℝ) ^ 2 * Real.log 3 - (N : ℝ) ^ 2 * (ν * Real.log 2) ≤
      Real.log T0 := by
    rw [hT0, Real.log_mul (by positivity) (by positivity), Real.log_mul (by
      exact (Finset.prod_pos fun k _ => by positivity).ne') (by positivity),
      Real.log_prod (fun k _ => by positivity), Real.log_pow, Real.log_pow, one_div, Real.log_inv]
    have h1 : -((N : ℝ) * ((N : ℝ) * Real.log N)) ≤ ∑ k : Fin N, Real.log (1 / ((k : ℕ)! : ℝ)) := by
      have : ∀ k : Fin N, -((N : ℝ) * Real.log N) ≤ Real.log (1 / ((k : ℕ)! : ℝ)) := by
        intro k
        rw [one_div, Real.log_inv, neg_le_neg_iff]
        have hk : ((k : ℕ)! : ℝ) ≤ (N ! : ℝ) := by exact_mod_cast Nat.factorial_le k.2.le
        exact (Real.log_le_log (by positivity) hk).trans hfactN
      calc -((N : ℝ) * ((N : ℝ) * Real.log N)) = ∑ _k : Fin N, -((N : ℝ) * Real.log N) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ => this k
    have h2 : -((N : ℝ) ^ 2 * Real.log 3) ≤ (tri N : ℝ) * Real.log c := by
      have hc3 : (1 : ℝ) / 3 ≤ c := by rw [hc]; linarith
      have hlc : -Real.log 3 ≤ Real.log c := by
        have := Real.log_le_log (by norm_num) hc3
        rwa [one_div, Real.log_inv] at this
      have hlc0 : Real.log c ≤ 0 := Real.log_nonpos hc0.le (by rw [hc]; linarith)
      have htri := tri_le N
      have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have ht0' : (0 : ℝ) ≤ tri N := Nat.cast_nonneg _
      nlinarith
    have h3 : -((N : ℝ) ^ 2 * (ν * Real.log 2)) ≤ ((N ^ 2 : ℕ) : ℝ) * -Real.log b₂ := by
      have := Real.log_lt_log hb0 hb₂
      rw [Real.log_pow] at this
      push_cast
      have : 0 ≤ (N : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  have hlogden : Real.log den ≤ Real.log N + (N : ℝ) * Real.log N + (N : ℝ) * (Real.log 3 +
      (2 ^ 15 * ν * (9 * Real.log 2 + Real.log ν) + ν * Real.log 2 * (2 ^ 9 * ν))) + (7 * Real.log 2 + 2 * Real.log ν) := by
    rw [hden, Real.log_mul (by positivity) (by positivity), Real.log_mul (by have := Nat.factorial_pos N; positivity)
      (by positivity), Real.log_mul (by positivity) (by have := Nat.factorial_pos N; positivity), Real.log_pow,
      Real.log_mul (by norm_num) hX1p.ne']
    have hXl : Real.log X1 ≤ 2 ^ 15 * ν * (9 * Real.log 2 + Real.log ν) + ν * Real.log 2 * (2 ^ 9 * ν) := by
      rw [hX1, Xb, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp,
        show (1 : ℝ) * (2 ^ 9 * ν) = 2 ^ 9 * ν by ring, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hK := K_le (ν := ν)
      have : (0 : ℝ) ≤ 9 * Real.log 2 + Real.log ν := by linarith
      push_cast
      have h' : (Kp ν : ℝ) * (9 * Real.log 2 + Real.log ν) ≤ 2 ^ 15 * ν * (9 * Real.log 2 + Real.log ν) := by gcongr
      linarith
    have hLS : Real.log ((ν : ℝ) * (2 ^ 7 * ν : ℕ)) = 7 * Real.log 2 + 2 * Real.log ν := by
      push_cast
      rw [show (ν : ℝ) * (128 * ν) = 2 ^ 7 * (ν : ℝ) ^ 2 by ring, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]; push_cast; ring
    rw [hLS]
    have hNX := mul_le_mul_of_nonneg_left hXl hN0.le
    linarith
  have hpoly := poly_final hv hℓ hℓ0 (by linarith : (0.6931 : ℝ) < Real.log 2)
    (by linarith : Real.log 2 < 0.6932) (Real.log 3) (Real.log_nonneg (by norm_num)) log_three_le
  have hkey : Real.log den - Real.log T0 ≤ 10 ^ 12 * (ν : ℝ) ^ 5 := by
    rw [hlogN] at hlogT0 hlogden
    rw [hNr] at hlogT0 hlogden
    linarith
  -- conclude
  have hq : Real.exp (-(10 ^ 12 * (ν : ℝ) ^ 5)) ≤ T0 / den := by
    rw [← Real.exp_log (by positivity : 0 < T0 / den), Real.log_div hT0p.ne' hdenp.ne']
    exact Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-(10 ^ 12 * (ν : ℝ) ^ 5)) ≤ T0 / den := hq
    _ ≤ T / den := by gcongr
    _ ≤ (b₂ : ℝ) * T / den := by
        have hT : 0 ≤ T := le_trans hT0p.le hT
        rw [mul_div_assoc]
        exact le_mul_of_one_le_left (by positivity) hb1

end

end Logs23

-- Source module: Logs23/TwoLog

namespace Logs23

open Finset Real Steiner

open scoped Nat

noncomputable section

/-! ## The grid of points -/

theorem NRS {ν : ℕ} (hν : 1 ≤ ν) : ν * (Kp ν + 1) = 2 ^ 8 * ν * (2 ^ 7 * ν) := by
  rw [Kp_succ hν]; ring

/-- Columns ↔ grid. -/
def cE {ν : ℕ} (hν : 1 ≤ ν) : Fin (ν * (Kp ν + 1)) ≃ Fin (2 ^ 8 * ν) × Fin (2 ^ 7 * ν) :=
  (finCongr (NRS hν)).trans finProdFinEquiv.symm

def rrG {ν : ℕ} (hν : 1 ≤ ν) (j : Fin (ν * (Kp ν + 1))) : ℕ := ((cE hν j).1 : ℕ) + 1
def ssG {ν : ℕ} (hν : 1 ≤ ν) (j : Fin (ν * (Kp ν + 1))) : ℕ := ((cE hν j).2 : ℕ)

theorem grid_injective {ν : ℕ} (hν : 1 ≤ ν) {b₁ b₂ : ℕ} (hcop : Nat.Coprime b₁ b₂) (hS : 2 ^ 7 * ν ≤ b₂) :
    Function.Injective fun j => rrG hν j * b₂ + ssG hν j * b₁ := by
  intro i j hij
  simp only at hij
  have hz : ((rrG hν i : ℤ) - rrG hν j) * b₂ = ((ssG hν j : ℤ) - ssG hν i) * b₁ := by
    have : ((rrG hν i * b₂ + ssG hν i * b₁ : ℕ) : ℤ) = ((rrG hν j * b₂ + ssG hν j * b₁ : ℕ) : ℤ) := by
      rw [hij]
    push_cast at this; linarith
  have hcop' : IsCoprime (b₂ : ℤ) b₁ := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hdvd : (b₂ : ℤ) ∣ ((ssG hν j : ℤ) - ssG hν i) := hcop'.dvd_of_dvd_mul_right ⟨(rrG hν i : ℤ) - rrG hν j, by rw [← hz]; ring⟩
  have hsj : ssG hν j < 2 ^ 7 * ν := (cE hν j).2.2
  have hsi : ssG hν i < 2 ^ 7 * ν := (cE hν i).2.2
  have hs : ssG hν j = ssG hν i := by
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
    omega
  have hr : rrG hν i = rrG hν j := by
    rw [hs, sub_self, zero_mul] at hz
    have hb : (b₂ : ℤ) ≠ 0 := by
      have : 0 < b₂ := lt_of_lt_of_le (by positivity) hS
      exact_mod_cast this.ne'
    have := mul_eq_zero.mp hz
    rcases this with h | h
    · omega
    · exact absurd h hb
  apply (cE hν).injective
  simp only [rrG, ssG] at hs hr
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext hs.symm)

/-- `|V(ζ)| ≥ b^(−N²)` when `1 ≤ b` and `|ζ_j − ζ_i| ≥ 1/b` for `i ≠ j`. -/
theorem abs_vprod_ge {N : ℕ} (ζ : Fin N → ℝ) {b : ℝ} (hb : 1 ≤ b) (hsep : ∀ i j, i ≠ j → 1 / b ≤ |ζ j - ζ i|) :
    (1 / b) ^ (N ^ 2) ≤ |vprod ζ| := by
  have hb0 : 0 < 1 / b := by positivity
  have hb1 : 1 / b ≤ 1 := by rw [div_le_one (by linarith)]; exact hb
  rw [vprod, Finset.abs_prod]
  calc (1 / b) ^ (N ^ 2) = ∏ _i : Fin N, (1 / b) ^ N := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, sq]
    _ ≤ ∏ i : Fin N, |∏ j ∈ Ioi i, (ζ j - ζ i)| := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        rw [Finset.abs_prod]
        calc (1 / b) ^ N ≤ (1 / b) ^ (Ioi i).card := by
              apply pow_le_pow_of_le_one hb0.le hb1
              calc (Ioi i).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
                _ = N := by simp
          _ = ∏ _j ∈ Ioi i, 1 / b := (Finset.prod_const _).symm
          _ ≤ ∏ j ∈ Ioi i, |ζ j - ζ i| :=
              Finset.prod_le_prod (fun j _ => hb0.le) fun j hj => hsep i j (ne_of_lt (Finset.mem_Ioi.mp hj))

/-! ## The coprime case -/

theorem b1_lt {b₁ b₂ : ℕ} (hb : 4 ≤ b₂) (hΛ : |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| < 1) :
    b₁ < 2 * b₂ := by
  by_contra h
  rw [not_lt] at h
  have h' : (2 * b₂ : ℝ) ≤ b₁ := by exact_mod_cast h
  have hl : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
    have h43 : (1 : ℝ) - 1 / (4 / 3) ≤ Real.log (4 / 3) := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
      simpa [one_div] using this
    have : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb' : (4 : ℝ) ≤ b₂ := by exact_mod_cast hb
  have : 1 ≤ (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 := by nlinarith
  have := le_abs_self ((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3)
  linarith

theorem two_pow_ge_sq {n : ℕ} (hn : 20 ≤ n) : 2 ^ 7 * n ^ 2 ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    have h2 : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]; ring
    rw [h2]
    calc 2 ^ 7 * (n + 1) ^ 2 ≤ 2 ^ 7 * (2 * n ^ 2) := Nat.mul_le_mul_left _ h1
      _ = 2 * (2 ^ 7 * n ^ 2) := by ring
      _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left _ ih

theorem coprime_case {b₁ b₂ : ℕ} (hb₂ : 2 ^ 334 ≤ b₂) (hcop : Nat.Coprime b₁ b₂) :
    Real.exp (-(10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5)) ≤
      |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| := by
  set Λ := (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 with hΛ
  set ν := Nat.log 2 b₂ + 1 with hνdef
  by_cases hbig : 1 ≤ |Λ|
  · refine le_trans (le_of_lt ?_) hbig
    have : (0 : ℝ) < ((ν : ℕ) : ℝ) := by positivity
    have := pow_pos this 5
    calc Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  rw [not_le] at hbig
  have hb0 : 0 < b₂ := lt_of_lt_of_le (by positivity) hb₂
  have hν : 335 ≤ ν := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hb₂; omega
  have hν1 : 1 ≤ ν := by omega
  have hlt : (b₂ : ℝ) < 2 ^ ν := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b₂
    exact_mod_cast this
  have hge : 2 ^ (ν - 1) ≤ b₂ := by
    have := Nat.pow_log_le_self 2 hb0.ne'
    rwa [show ν - 1 = Nat.log 2 b₂ by omega]
  have hpow : 2 ^ 7 * ν ^ 2 ≤ b₂ := (two_pow_ge_sq (by omega)).trans hge
  have hS : 2 ^ 7 * ν ≤ b₂ := le_trans (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero ν)) hpow
  have hb4 : 4 ≤ b₂ := le_trans (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 ≤ 334 by norm_num)) hb₂
  have hb1 : b₁ < 2 * b₂ := b1_lt hb4 hbig
  have hbr : (0 : ℝ) < b₂ := by exact_mod_cast hb0
  have hθ : (b₁ : ℝ) / b₂ < 2 := by
    rw [div_lt_iff₀ hbr]; exact_mod_cast hb1
  have hθ0 : (0 : ℝ) ≤ (b₁ : ℝ) / b₂ := by positivity
  -- the main inequality
  have hmain := prop_main (L := ν) (K := Kp ν) (rrG hν1) (ssG hν1) b₁ b₂ (2 ^ 7 * ν) hb0
    (fun j => by simp [rrG]) (fun j => (cE hν1 j).2.2) (grid_injective hν1 hcop hS)
    (zmax := 2 ^ 9 * ν) (lmax := ν * Real.log 2)
    (fun j => by
      have hr : ((rrG hν1 j : ℕ) : ℝ) ≤ 2 ^ 8 * ν := by
        have : rrG hν1 j ≤ 2 ^ 8 * ν := (cE hν1 j).1.2
        exact_mod_cast this
      have hs : ((ssG hν1 j : ℕ) : ℝ) ≤ 2 ^ 7 * ν := by
        have : ssG hν1 j ≤ 2 ^ 7 * ν := (cE hν1 j).2.2.le
        exact_mod_cast this
      have hs0 : (0 : ℝ) ≤ ssG hν1 j := Nat.cast_nonneg _
      have hm := mul_le_mul hs hθ.le hθ0 (by positivity)
      have : (2 : ℝ) ^ 9 * ν = 2 ^ 8 * ν + 2 ^ 7 * ν * 2 := by ring
      linarith)
    (fun l => by
      have : ((l : ℕ) : ℝ) + 1 ≤ ν := by exact_mod_cast l.2
      simp only [lam]
      exact mul_le_mul_of_nonneg_right this (Real.log_pos (by norm_num)).le)
    (by
      rw [abs_div, abs_of_pos hbr]
      have h7 : ((ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ)) ≤ b₂ := by
        have : ν * (2 ^ 7 * ν) ≤ b₂ := by
          calc ν * (2 ^ 7 * ν) = 2 ^ 7 * ν ^ 2 := by ring
            _ ≤ b₂ := hpow
        exact_mod_cast this
      rw [← mul_div_assoc, div_le_one hbr]
      have h0 : (0 : ℝ) ≤ (ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ) := by positivity
      calc (ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ) * |Λ| ≤ (ν : ℝ) * ((2 ^ 7 * ν : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hbig.le h0
        _ ≤ b₂ := by linarith)
    (by norm_num : (1 : ℝ) ≤ 16) (cond_P hν hb0 hlt)
  -- the separation of the points
  have hsep : ∀ i j : Fin (ν * (Kp ν + 1)), i ≠ j →
      1 / (b₂ : ℝ) ≤ |((rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂)) -
        ((rrG hν1 i : ℝ) + ssG hν1 i * ((b₁ : ℝ) / b₂))| := by
    intro i j hij
    have hne : ((rrG hν1 j * b₂ + ssG hν1 j * b₁ : ℕ) : ℤ) - ((rrG hν1 i * b₂ + ssG hν1 i * b₁ : ℕ) : ℤ) ≠ 0 := by
      intro h
      apply hij
      apply grid_injective hν1 hcop hS
      simp only
      exact_mod_cast (sub_eq_zero.mp h).symm
    have h1 := Int.one_le_abs hne
    have h1r : (1 : ℝ) ≤ |(((rrG hν1 j * b₂ + ssG hν1 j * b₁ : ℕ) : ℤ) -
        ((rrG hν1 i * b₂ + ssG hν1 i * b₁ : ℕ) : ℤ) : ℝ)| := by exact_mod_cast h1
    have heq : ((rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂)) - ((rrG hν1 i : ℝ) + ssG hν1 i * ((b₁ : ℝ) / b₂)) =
        (((rrG hν1 j * b₂ + ssG hν1 j * b₁ : ℕ) : ℤ) - ((rrG hν1 i * b₂ + ssG hν1 i * b₁ : ℕ) : ℤ) : ℝ) / b₂ := by
      push_cast; field_simp
    rw [heq, abs_div, abs_of_pos hbr]
    exact div_le_div_of_nonneg_right h1r hbr.le
  have hV := abs_vprod_ge (fun j => (rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂))
    (by exact_mod_cast hb0 : (1 : ℝ) ≤ b₂) hsep
  have hfin := final_ge hν hb0 hlt (T := Tlow (ν * (Kp ν + 1))
    (fun j => (rrG hν1 j : ℝ) + ssG hν1 j * ((b₁ : ℝ) / b₂))) (by
      rw [Tlow]
      have : 0 ≤ (∏ k : Fin (ν * (Kp ν + 1)), (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri (ν * (Kp ν + 1)) := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        exact mul_nonneg (Finset.prod_nonneg fun k _ => by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hV this)
  exact hfin.trans hmain

/-! ## `two_log_lower` -/

theorem two_log_lower_thm : two_log_lower := by
  intro b₁ b₂ hb₂
  have hb0 : 0 < b₂ := lt_of_lt_of_le (by positivity) hb₂
  have hg0 : 0 < Nat.gcd b₁ b₂ := Nat.gcd_pos_of_pos_right _ hb0
  obtain ⟨c₁, hc₁⟩ := Nat.gcd_dvd_left b₁ b₂
  obtain ⟨c₂, hc₂⟩ := Nat.gcd_dvd_right b₁ b₂
  have hcop : Nat.Coprime c₁ c₂ := by
    have := Nat.coprime_div_gcd_div_gcd (m := b₁) (n := b₂) hg0
    rwa [Nat.div_eq_of_eq_mul_right hg0 hc₁, Nat.div_eq_of_eq_mul_right hg0 hc₂] at this
  generalize Nat.gcd b₁ b₂ = g at hc₁ hc₂ hg0
  have hc₂0 : 0 < c₂ := by
    rcases Nat.eq_zero_or_pos c₂ with h | h
    · rw [h, mul_zero] at hc₂; omega
    · exact h
  -- `Λ = g Λ'`
  have hΛ : (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 = g * ((c₁ : ℝ) * Real.log 2 - (c₂ : ℝ) * Real.log 3) := by
    rw [hc₁, hc₂]; push_cast; ring
  have hgr : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have hge : |(c₁ : ℝ) * Real.log 2 - (c₂ : ℝ) * Real.log 3| ≤ |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| := by
    rw [hΛ, abs_mul, abs_of_pos (show (0 : ℝ) < g by linarith)]
    exact le_mul_of_one_le_left (abs_nonneg _) hgr
  refine le_trans ?_ hge
  have hν0 : (0 : ℝ) < ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) := by positivity
  by_cases hsmall : c₂ < qBr'
  · -- the bridge
    have h1 := bridge_gap_thm c₂ (c₁ : ℤ) hc₂0 hsmall
    have h2 := bridge_value_thm
    push_cast at h1
    refine le_trans ?_ (h2.trans h1)
    -- `exp(−10^12 ν^5) ≤ 10^(−101)`
    have h101 : (101 : ℝ) * Real.log 10 ≤ 10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5 := by
      have hl10 : Real.log 10 ≤ 10 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10); linarith
      have : (1 : ℝ) ≤ ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have := one_le_pow₀ this (n := 5)
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10)]
    calc Real.exp (-(10 ^ 12 * ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5)) ≤ Real.exp (-(101 * Real.log 10)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 10 ^ 101 := by
          rw [show -(101 * Real.log 10) = -Real.log (10 ^ 101) by rw [Real.log_pow]; push_cast; ring,
            Real.exp_neg, Real.exp_log (by positivity), one_div]
  · -- the coprime case
    rw [not_lt] at hsmall
    have hq : 2 ^ 334 ≤ qBr' := by unfold qBr'; decide +kernel
    have hc : 2 ^ 334 ≤ c₂ := hq.trans hsmall
    refine le_trans ?_ (coprime_case hc hcop)
    apply Real.exp_le_exp.mpr
    have hmono : Nat.log 2 c₂ ≤ Nat.log 2 b₂ := Nat.log_mono_right (by rw [hc₂]; exact Nat.le_mul_of_pos_left _ hg0)
    have : ((Nat.log 2 c₂ + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hmono
    have : ((Nat.log 2 c₂ + 1 : ℕ) : ℝ) ^ 5 ≤ ((Nat.log 2 b₂ + 1 : ℕ) : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by positivity) this 5
    linarith

/-! ## `lam_lower_large`, `lam_lower`, and Steiner's theorem without hypothesis -/

theorem pow5_le_two_pow {n : ℕ} (hn : 335 ≤ n) : 10 ^ 12 * n ^ 5 ≤ 2 ^ (n - 3) := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have h1 : (n + 1) ^ 5 ≤ 2 * n ^ 5 := by
      have hn' : (335 : ℝ) ≤ n := by exact_mod_cast hn
      have h0 : (0 : ℝ) ≤ n := by linarith
      have a5 : 335 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 4); nlinarith [this]
      have a4 : 335 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 3); nlinarith [this]
      have a3 : 335 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 2); nlinarith [this]
      have a2 : 335 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have e : ((n : ℝ) + 1) ^ 5 = (n : ℝ) ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 10 * n ^ 2 + 5 * n + 1 := by ring
      have hr : ((n : ℝ) + 1) ^ 5 ≤ 2 * (n : ℝ) ^ 5 := by rw [e]; linarith
      exact_mod_cast hr
    have h2 : 2 ^ (n + 1 - 3) = 2 * 2 ^ (n - 3) := by
      rw [show n + 1 - 3 = (n - 3) + 1 by omega, pow_succ]; ring
    rw [h2]
    calc 10 ^ 12 * (n + 1) ^ 5 ≤ 10 ^ 12 * (2 * n ^ 5) := Nat.mul_le_mul_left _ h1
      _ = 2 * (10 ^ 12 * n ^ 5) := by ring
      _ ≤ 2 * 2 ^ (n - 3) := Nat.mul_le_mul_left _ ih

theorem lam_lower_large_thm : lam_lower_large := by
  intro k l hk
  have h := two_log_lower_thm (k + l) k hk
  set ν := Nat.log 2 k + 1 with hν
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hν335 : 335 ≤ ν := by have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hk; omega
  have hge : 2 ^ (ν - 1) ≤ k := by
    have := Nat.pow_log_le_self 2 hk0.ne'
    rwa [show ν - 1 = Nat.log 2 k by omega]
  have hLam : |((k + l : ℕ) : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3| = |Lam k l| := by rfl
  rw [hLam] at h
  refine le_trans ?_ h
  -- `1/(2^k − 1) ≤ exp(−10^12 ν^5)`, i.e. `exp(10^12 ν^5) ≤ 2^k − 1`
  have hpow := pow5_le_two_pow hν335
  have hpowr : (10 : ℝ) ^ 12 * (ν : ℝ) ^ 5 ≤ 2 ^ (ν - 3) := by exact_mod_cast hpow
  have hkr : (2 : ℝ) ^ (ν - 1) ≤ k := by exact_mod_cast hge
  have h2k : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k - 1 := by
    have : (1 : ℝ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num)
    have h' : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    linarith
  have hexp : Real.exp (10 ^ 12 * (ν : ℝ) ^ 5) ≤ 2 ^ (k - 1) := by
    -- `10^12 ν^5 ≤ 2^(ν−3) ≤ (k − 1) log 2`
    have hlog2 := Real.log_two_gt_d9
    have h3 : (2 : ℝ) ^ (ν - 3) ≤ ((k - 1 : ℕ) : ℝ) * Real.log 2 := by
      have h4 : (2 : ℝ) ^ (ν - 1) = 4 * 2 ^ (ν - 3) := by
        rw [show ν - 1 = (ν - 3) + 2 by omega, pow_add]; ring
      have h5 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have h6 : (1 : ℝ) ≤ 2 ^ (ν - 3) := one_le_pow₀ (by norm_num)
      rw [h5]
      set X := (2 : ℝ) ^ (ν - 3) with hX
      have hk4 : 4 * X - 1 ≤ (k : ℝ) - 1 := by linarith
      have hl0 : (0 : ℝ) ≤ Real.log 2 := by linarith
      have hm := mul_le_mul_of_nonneg_right hk4 hl0
      have hm2 : (4 * X - 1) * 0.6931 ≤ (4 * X - 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    calc Real.exp (10 ^ 12 * (ν : ℝ) ^ 5) ≤ Real.exp (((k - 1 : ℕ) : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr (hpowr.trans h3)
      _ = 2 ^ (k - 1) := by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; norm_cast
  have hpos : (0 : ℝ) < 2 ^ k - 1 := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (hexp.trans h2k)

theorem lam_lower_thm : lam_lower := by
  intro k l hk
  by_cases hsmall : k < qBr'
  · exact lam_lower_bridge_thm k l hk hsmall
  · rw [not_lt] at hsmall
    have hq : 2 ^ 334 ≤ qBr' := by unfold qBr'; decide +kernel
    exact lam_lower_large_thm k l (hq.trans hsmall)

end

end Logs23

namespace Erdos1135.CycleSearch

private def gapCheck : ℕ → Bool
  | 0 => true
  | j + 1 => (decide (j + 1 < 94) || decide
      (2 ^ Steiner.Lk (j + 1) ≤ (2 ^ Steiner.Lk (j + 1) - 3 ^ (j + 1)) * 2 ^ ((j + 1) / 13))) && gapCheck j

private theorem gapCheck_spec (N : ℕ) (hc : gapCheck N = true) {s : ℕ}
    (hs : 94 ≤ s) (hN : s ≤ N) : 2 ^ Steiner.Lk s ≤ (2 ^ Steiner.Lk s - 3 ^ s) * 2 ^ (s / 13) := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [gapCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases Nat.eq_or_lt_of_le hN with rfl | h
    · exact hc.1.resolve_left (by omega)
    · exact ih hc.2 (by omega)

private theorem finite_gap_checked : gapCheck 4400 = true := by decide +kernel

private theorem finite_relative_gap {s k : ℕ} (hs : 94 ≤ s) (hN : s ≤ 4400) (hc : 3 ^ s < 2 ^ k) :
    2 ^ k ≤ (2 ^ k - 3 ^ s) * 2 ^ (s / 13) := by
  have hok := Steiner.chk_of_le (by omega : 2 ≤ s) (by omega : s ≤ 20000)
  simp only [Steiner.chk, Steiner.posOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hhalf, hB⟩, _⟩, _⟩ := hok
  let L := Steiner.Lk s
  have hL : 1 ≤ L := by simp [L, Steiner.Lk]
  change 2 ^ L / 2 ≤ 3 ^ s at hhalf
  rw [Steiner.pow_half hL] at hhalf
  have hLk : L ≤ k := by
    by_contra! hx
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : k ≤ L - 1)
    omega
  rcases Nat.eq_or_lt_of_le hLk with rfl | h
  · exact gapCheck_spec 4400 finite_gap_checked hs hN
  · have hdouble := Nat.pow_le_pow_right (by decide : 0 < 2) (show L + 1 ≤ k by omega)
    rw [pow_succ] at hdouble
    change 3 ^ s < 2 ^ L at hB
    have hu : 2 ≤ (2 : ℕ) ^ (s / 13) := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : s / 13 ≠ 0)
    have hm := Nat.mul_le_mul_left (2 ^ k - 3 ^ s) hu
    omega

private theorem log_parameter {v : ℕ} (hv : 335 ≤ v) : 128 * (10 ^ 12 * v ^ 5) ≤ 2 ^ (v - 1) := by
  induction v, hv using Nat.le_induction with
  | base => decide +kernel
  | succ v hv ih =>
    have h0 := Nat.pow_le_pow_left (show 8 * (v + 1) ≤ 9 * v by omega) 5
    rw [mul_pow, mul_pow] at h0
    have h1 : (v + 1) ^ 5 ≤ 2 * v ^ 5 := by norm_num at h0; omega
    have h2 := Nat.mul_le_mul_left (128 * 10 ^ 12) h1
    have he : (2 : ℕ) ^ (v + 1 - 1) = 2 ^ (v - 1) * 2 := by
      rw [show v + 1 - 1 = (v - 1) + 1 by omega, pow_succ]
    rw [he]
    nlinarith only [h2, ih]

private theorem log_relative_gap {s : ℕ} (hs : 4400 < s) (e : ℕ) :
    1 / ((2 : ℝ) ^ (s / 13 - 1)) ≤ |Steiner.Lam s e| := by
  let a := s / 13 - 1
  change 1 / ((2 : ℝ) ^ a) ≤ _
  by_cases hb : s < Logs23.qBr'
  · have H := Logs23.bridge_gap_thm s ((s + e : ℕ) : ℤ) (by omega) hb
    have hLam : |(((s + e : ℕ) : ℤ) : ℝ) * Real.log 2 - (s : ℝ) * Real.log 3| = |Steiner.Lam s e| := by
      unfold Steiner.Lam; push_cast; ring_nf
    rw [hLam] at H
    have hA : (10 : ℕ) ^ 101 ≤ 2 ^ a := calc
      _ ≤ 2 ^ 336 := by decide +kernel
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp only [a]; omega)
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hA)).trans (Logs23.bridge_value_thm.trans H)
  · have hq : 2 ^ 334 ≤ Logs23.qBr' := by unfold Logs23.qBr'; decide +kernel
    have hs' : 2 ^ 334 ≤ s := by omega
    let v := Nat.log 2 s + 1
    have hv : 335 ≤ v := by
      have := Nat.le_log_of_pow_le (by decide : 1 < 2) hs'
      dsimp only [v]; omega
    have hl : 2 ^ (v - 1) ≤ s := by simpa [v] using Nat.pow_log_le_self 2 (by omega : s ≠ 0)
    have ha : 2 * (10 ^ 12 * v ^ 5) ≤ a := by
      have h := (log_parameter hv).trans hl
      dsimp only [a]; omega
    have har : 2 * ((10 : ℝ) ^ 12 * (v : ℝ) ^ 5) ≤ a := by exact_mod_cast ha
    have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hA : (10 : ℝ) ^ 12 * (v : ℝ) ^ 5 ≤ (a : ℝ) * Real.log 2 := by
      have h := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ a)
      linarith
    calc
      1 / ((2 : ℝ) ^ a) = Real.exp (-((a : ℝ) * Real.log 2)) := by
        rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log (by norm_num), one_div]
        norm_cast
      _ ≤ Real.exp (-((10 : ℝ) ^ 12 * (v : ℝ) ^ 5)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := Logs23.two_log_lower_thm (s + e) s hs'

/-- Throughout the entire range of the cycle reduction, the relative power
gap is at least one part in `2^(s/13)`. -/
theorem cycle_relative_gap {s k : ℕ} (hs : 94 ≤ s) (hc : 3 ^ s < 2 ^ k) :
    2 ^ k ≤ (2 ^ k - 3 ^ s) * 2 ^ (s / 13) := by
  by_cases hf : s ≤ 4400
  · exact finite_relative_gap hs hf hc
  have hb := Nat.pow_le_pow_left (by decide : 2 ≤ 3) s
  have hsk := le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hb.trans_lt hc))
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hsk
  have hr : (3 : ℝ) ^ s < 2 ^ (s + e) := by exact_mod_cast hc
  obtain ⟨hp, hu⟩ := Steiner.Lam_pos_le hr
  have hlo := log_relative_gap (by omega : 4400 < s) e
  rw [abs_of_pos hp] at hlo
  have hh := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (s / 13 - 1)) (by positivity : (0 : ℝ) < 3 ^ s)).mp (hlo.trans hu)
  simp only [one_mul] at hh
  have hpow : 2 ^ (s / 13 - 1) + 1 ≤ (2 : ℝ) ^ (s / 13) := by
    conv_rhs => rw [show s / 13 = (s / 13 - 1) + 1 by omega, pow_succ]
    linarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := s / 13 - 1)]
  have H := mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hr.le)
  have hfinal : (2 : ℝ) ^ (s + e) ≤ (2 ^ (s + e) - 3 ^ s) * 2 ^ (s / 13) := by nlinarith only [hh, H]
  apply Nat.cast_le (α := ℝ) |>.mp
  push_cast [Nat.cast_sub hc.le]
  exact hfinal


theorem cycle_search_gap {s k : ℕ} (hs : 94 ≤ s) (hc : 3 ^ s < 2 ^ k) :
    2 ^ k ≤ (2 ^ k - 3 ^ s) *
      min (2 ^ (s / 13)) (if s < 10 ^ 100 then 10 ^ 101 + 1
        else 2 ^ (2 * 10 ^ 12 * (Nat.log 2 s + 1) ^ 5) + 1) := by
  have hrel := cycle_relative_gap hs hc
  rw [mul_min]
  apply le_min hrel
  have hsmall : (10 : ℕ) ^ 100 ≤ Logs23.qBr' := by unfold Logs23.qBr'; decide +kernel
  let a := 2 * 10 ^ 12 * (Nat.log 2 s + 1) ^ 5
  have hbase := Nat.pow_le_pow_left (by decide : 2 ≤ 3) s
  have hsk := le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hbase.trans_lt hc))
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hsk
  have hr : (3 : ℝ) ^ s < 2 ^ (s + e) := by exact_mod_cast hc
  obtain ⟨hp, hu⟩ := Steiner.Lam_pos_le hr
  have bridge (hb : s < Logs23.qBr') : 1 / ((10 : ℝ) ^ 101) ≤ |Steiner.Lam s e| := by
    have H := Logs23.bridge_gap_thm s ((s + e : ℕ) : ℤ) (by omega) hb
    have he : |(((s + e : ℕ) : ℤ) : ℝ) * Real.log 2 - (s : ℝ) * Real.log 3| = |Steiner.Lam s e| := by
      unfold Steiner.Lam; push_cast; ring_nf
    rw [← he]
    exact Logs23.bridge_value_thm.trans H
  have finish (M : ℕ) (hM : 0 < M) (hL : 1 / (M : ℝ) ≤ |Steiner.Lam s e|) :
      2 ^ (s + e) ≤ (2 ^ (s + e) - 3 ^ s) * (M + 1) := by
    rw [abs_of_pos hp] at hL
    have hh := (div_le_div_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)
      (by positivity : (0 : ℝ) < 3 ^ s)).mp (hL.trans hu)
    have hreal : (2 : ℝ) ^ (s + e) ≤ (2 ^ (s + e) - 3 ^ s) * ((M : ℝ) + 1) := by nlinarith only [hh]
    apply Nat.cast_le (α := ℝ) |>.mp
    push_cast [Nat.cast_sub hc.le]
    exact hreal
  by_cases hB : s < 10 ^ 100
  · rw [if_pos hB]
    apply finish _ (by positivity)
    exact_mod_cast bridge (hB.trans_le hsmall)
  · rw [if_neg hB]
    change 2 ^ (s + e) ≤ (2 ^ (s + e) - 3 ^ s) * (2 ^ a + 1)
    apply finish _ (by positivity)
    rw [Nat.cast_pow, Nat.cast_ofNat]
    by_cases hb : s < Logs23.qBr'
    · have hla : 336 ≤ a := by
        dsimp only [a]
        have hr := Nat.one_le_pow 5 (Nat.log 2 s + 1) (by omega)
        omega
      have H : (10 : ℕ) ^ 101 ≤ 2 ^ a :=
        (show (10 : ℕ) ^ 101 ≤ 2 ^ 336 by decide +kernel).trans (Nat.pow_le_pow_right (by decide) hla)
      exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast H)).trans (bridge hb)
    · have hq : 2 ^ 334 ≤ Logs23.qBr' := by unfold Logs23.qBr'; decide +kernel
      have hs' : 2 ^ 334 ≤ s := by omega
      have har : (a : ℝ) = 2 * (10 ^ 12 * ((Nat.log 2 s + 1 : ℕ) : ℝ) ^ 5) := by
        dsimp only [a]; push_cast; ring
      have hA : (10 : ℝ) ^ 12 * ((Nat.log 2 s + 1 : ℕ) : ℝ) ^ 5 ≤ (a : ℝ) * Real.log 2 := by
        have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have h := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ a)
        linarith only [h, har]
      calc
        1 / ((2 : ℝ) ^ a) = Real.exp (-((a : ℝ) * Real.log 2)) := by
          rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log (by norm_num), one_div]
          norm_cast
        _ ≤ _ := (Real.exp_le_exp.mpr (neg_le_neg hA)).trans (Logs23.two_log_lower_thm (s + e) s hs')


end Erdos1135.CycleSearch

theorem OMA.solution : OMA.R_Erdos1135_erdos_1135_R2_H2_R1.H1 := by
  intro k s hs hc
  exact Erdos1135.CycleSearch.cycle_search_gap hs hc
