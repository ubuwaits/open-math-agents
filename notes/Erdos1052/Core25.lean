import PrimeDouble625

/-! The odd-exponent interval and arithmetic obstructions for repeated core 25. -/

namespace Erdos1052.Core25

open Erdos1052.Core625

def excluded : Finset ℕ := {3,5,7,13}

private def cuts : CutTable :=
  [(1,5,27),(19,19,31),(31,589,73),(37,1147,127),(61,2257,147),
   (73,4453,295),(127,565531,1055),(487,4514977,1651),(127,286639,311),
   (73,2263,134),(127,287401,273),(127,145669,168),(61,1159,105)]

/-- Each cutoff uses the path estimate for all larger primes. -/
private def check : ℕ → ℚ → ℕ → ℕ → Bool
  | 0, A, _, _ => decide (0 ≤ A ∧ 2 ≤ A)
  | fuel+1, A, x, D =>
    if 2 ≤ A then decide (0 ≤ A) else
      let y := cutoff cuts x D
      decide (1 ≤ y ∧ y < 4094 ∧ D ≠ 0 ∧ 0 ≤ A ∧ A * tail y D < 199/100) &&
      (List.range' (x+1) (y-x)).all (fun q =>
        let d := stripTwos 12 (1+q)
        if d ∣ D ∧ q ∉ excluded ∧ possiblePrime q = true then
          check fuel (A * gain q) q (D / d * q) else true)

private theorem check_sound {fuel x D : ℕ} {A : ℚ} (hc : check fuel A x D = true) :
    Gap excluded (199/100) 2 A x D := by
  induction fuel generalizing A x D with
  | zero =>
    have h : 0 ≤ A ∧ 2 ≤ A := of_decide_eq_true hc
    exact gap_high h.1 h.2
  | succ fuel ih =>
    rw [check] at hc
    split_ifs at hc with h
    · exact gap_high (of_decide_eq_true hc) h
    · obtain ⟨hdata,hchildren⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨hy,hbound,hD,ha,hcut⟩ := of_decide_eq_true hdata
      apply gap_split hy hD ha hcut
      intro q hq
      obtain ⟨hxy,hban,hprime,hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hx,hyq⟩ := Finset.mem_Icc.mp hxy
      have hmem : q ∈ List.range' (x+1) (cutoff cuts x D-x) := by
        rw [List.mem_range'_1]; omega
      have hchild := List.all_eq_true.mp hchildren q hmem
      have hstrip : stripTwos 12 (1+q) = demand q :=
        stripTwos_eq (by omega) (by norm_num; omega)
      simp only [hstrip, hd, hban, prime_possible hprime] at hchild
      exact ih hchild

set_option maxRecDepth 131072 in
set_option maxHeartbeats 4000000 in
theorem seed_fifteen_gap : Gap excluded (199/100) 2 (128/75) 1 5 := by
  apply check_sound (fuel := 12)
  decide +kernel

theorem short_witness {q : ℕ} (h : q < 200)
    (h8 : q%8 = 3) (h3 : q%3 = 1) (h5 : q%5 = 4) : q = 19 ∨ q = 139 := by omega

theorem orders_of_witnesses : orderOf (2 : ZMod 19) = 18 ∧ orderOf (2 : ZMod 139) = 138 := by
  constructor
  · have h : ∀ p ∈ (18:ℕ).primeFactors, (2 : ZMod 19) ^ (18/p) ≠ 1 := by decide +kernel
    exact orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide +kernel)
      (fun p hp hd => h p (Nat.mem_primeFactors.mpr ⟨hp, hd, by decide⟩))
  · have h : ∀ p ∈ (138:ℕ).primeFactors, (2 : ZMod 139) ^ (138/p) ≠ 1 := by decide +kernel
    exact orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide +kernel)
      (fun p hp hd => h p (Nat.mem_primeFactors.mpr ⟨hp, hd, by decide⟩))

theorem large_witness_gap : (199/100:ℚ)*(1+1/200)*(1+1/2^20) < 2 := by norm_num

theorem free_group_gap : (16/15:ℚ)*(64/63)*(2048/2047) < 6/5 := by norm_num

theorem fermat_group_window {B y : ℚ} (hb : 4/3 ≤ B) (hu : B < 25/16)
    (hy : 0 < y) (hy' : y ≤ 1/16) : 5/4 < (1+y)*B ∧ (1+y)*B < 2 := by
  constructor
  · nlinarith [mul_pos hy (by linarith : 0 < B)]
  · calc (1+y)*B < (1+y)*(25/16) := mul_lt_mul_of_pos_left hu (by linarith)
         _ < 2 := by linarith

end Erdos1052.Core25
