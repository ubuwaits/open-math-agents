import Mathlib

/-! Congruence obstructions and loss inequalities for Mersenne residual factors. -/

namespace Erdos1052.MersenneMass

private theorem stable_sixteenth_powers {M : Type*} [Monoid M] (g r : M)
    (ha : g^16 = r) (hb : r^16 = r) (n : ℕ) : g^(16^(n+1)) = r := by
  induction n with
  | zero => simpa using ha
  | succ n ih => rw [pow_succ 16 (n+1), pow_mul, ih, hb]

/-- The four residues at heights h that are positive powers of sixteen. -/
theorem obstruction_residues (n : ℕ) :
    (2 : ZMod 11)^(16^(n+1)) = 9 ∧ (2 : ZMod 13)^(16^(n+1)) = 3 ∧
    (2 : ZMod 7)^(16^(n+1)) = 2 ∧ (2 : ZMod 5)^(16^(n+1)) = 1 := by
  exact ⟨stable_sixteenth_powers _ _ (by decide) (by decide) _,
    stable_sixteenth_powers _ _ (by decide) (by decide) _,
    stable_sixteenth_powers _ _ (by decide) (by decide) _,
    stable_sixteenth_powers _ _ (by decide) (by decide) _⟩

theorem excluded_successors :
    (4*9-3 : ZMod 11) = 0 ∧ (16*3-9 : ZMod 13) = 0 ∧
    (64*1-9 : ZMod 5) = 0 ∧ (128*2-25 : ZMod 7) = 0 ∧
    (2*3-1 : ZMod 5) = 0 ∧ (32*3-1 : ZMod 5) = 0 := by decide

/-- One vertex followed by a suffix of loss at most c/(q+1). -/
theorem prepend {r K c : ℚ} (hr : 0 < r) (hK : 0 < K) :
    1 - r/(r+1)*(1-c/(K*r)) = (1+c/K)/(r+1) := by
  field_simp
  ring

theorem path_constants :
    (1+2/32 : ℚ) = 17/16 ∧ (1+(1+2/128)/2 : ℚ) = 193/128 ∧
    (17/32+193/1024+1/48 : ℚ) = 2275/3072 ∧
    (1/3+1/16 : ℚ) = 19/48 := by norm_num

theorem separated_losses {y : ℚ} (hy : 0 < y) (h : y ≤ 1/65536) :
    2275/3072*y < (1-1/4)*y-3*y^2 ∧
    19/48*y < (1-1/2)*y-3*y^2 := by
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right h hy.le]

/-- Terms using at least two repeated factors consume less than 1/100 per root. -/
theorem higher_degree {s T : ℚ} (hs : 0 ≤ s) (hT : 0 ≤ T)
    (ht : T ≤ 1/65536) (hst : s ≤ T*(65536/65535)) :
    (4/3)*s^2/(1-s) ≤ T/100 := by
  have hsmall : s ≤ 1/65535 := by linarith
  rw [div_le_iff₀ (by linarith : 0 < 1-s)]
  have hsq := mul_le_mul_of_nonneg_right hsmall hs
  have hmix := mul_le_mul_of_nonneg_left hsmall hT
  nlinarith

theorem singleton_charges {x : ℚ} (hx : 0 ≤ x) (ht : x ≤ 1/65536) :
    (4/3)*x/(1-x)+x/100 ≤ 3/2*x ∧
    x/(12*(1-x))+x/100 ≤ x/8 := by
  have hsq := mul_le_mul_of_nonneg_right ht hx
  constructor
  · rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith : 0 < 1-x)]
    nlinarith
  · rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith : 0 < 12*(1-x))]
    nlinarith

/-- The symmetric tolerances y/9 rule out all residual factorizations. -/
theorem ninth_gap {y : ℚ} (hy : 0<y) (h : y≤1/65536) :
    2275/3072*y+(4/3)*(y/9)/(1-y/9)<(8/9)*y-3*y^2 := by
  have hden : 65535/65536 ≤ 1-y/9 := by linarith
  have hmag : (4/3)*(y/9)/(1-y/9) ≤ (4/27)*(65536/65535)*y := by
    apply (div_le_iff₀ (by linarith : 0<1-y/9)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hy.le]
  nlinarith [mul_le_mul_of_nonneg_right h hy.le]

/-- Positive remaining mass after the two small bases forces at least 4096 copies. -/
theorem remaining_count (s : Finset ℕ) (e : ℕ → ℕ) (hk : ∀ k∈s, 31≤k)
    (hm : (1:ℚ)/2^19 ≤ ∑ k∈s, (e k : ℚ)/2^k) : 4096 ≤ ∑ k∈s, e k := by
  have hsum : (∑ k∈s, (e k : ℚ)/2^k) ≤ (∑ k∈s, (e k : ℚ))/2^31 := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun k hh => div_le_div_of_nonneg_left (by positivity)
      (by positivity) (pow_le_pow_right₀ (by norm_num) (hk k hh))
  have hcount : (4096:ℚ) ≤ ∑ k∈s, (e k : ℚ) := by
    have bound := hm.trans hsum
    norm_num at bound
    linarith
  exact_mod_cast hcount

/-- The resulting terminal divisor forces a very large binary exponent. -/
theorem remaining_size (s : Finset ℕ) (e : ℕ → ℕ) (hk : ∀ k∈s, 31≤k)
    (hm : (1:ℚ)/2^19 ≤ ∑ k∈s, (e k : ℚ)/2^k) :
    2^122880 ≤ ∏ k∈s, ((2:ℕ)^k-1)^e k := by
  have hcount := remaining_count s e hk hm
  calc
    2^122880 ≤ (2:ℕ)^(30*(∑ k∈s, e k)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = ∏ k∈s, (2^30)^e k := by rw [Finset.prod_pow_eq_pow_sum, pow_mul]
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro k hh
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (hk k hh)
      exact Nat.pow_le_pow_left (by omega) _

end Erdos1052.MersenneMass
