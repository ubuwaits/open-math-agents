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

/-- The complement is small enough that every one of its simple primes exceeds 16383. -/
theorem complement_upper {C ρ U y : ℚ} (hC : 0<C) (hρ : 1<ρ)
    (hU : 1-1/16384≤U) (hy : 0<y) (eqn : C*ρ*U*(1+y)=1) :
    C < 16384/16383 := by
  have hUpos : 0<U := by linarith
  have hless : C*U < C*ρ*U := by nlinarith [mul_pos (mul_pos hC hUpos) (sub_pos.mpr hρ)]
  have hρpos : 0<ρ := by linarith
  have hypos : 0<C*ρ*U*y := mul_pos (mul_pos (mul_pos hC hρpos) hUpos) hy
  nlinarith [mul_le_mul_of_nonneg_left hU hC.le]

/-- The loss needed in the complement comes from the full unitary identity. -/
theorem complement_lower {C ρ U y : ℚ} (hC : 0<C)
    (hcap : ρ≤1/(1-1/(2:ℚ)^24)) (hU : 0<U) (hUcap : U≤1/(1+1/16384))
    (hy : 0<y) (hycap : y≤1/(2:ℚ)^64) (eqn : C*ρ*U*(1+y)=1) :
    1-(1+1/(2:ℚ)^64)/((1+1/16384)*(1-1/(2:ℚ)^24)) ≤ 1-1/C := by
  have hrec : 1/C=ρ*U*(1+y) := by
    apply (div_eq_iff hC.ne').mpr
    linear_combination -eqn
  rw [hrec]
  have hu := mul_le_mul hcap hUcap hU.le (by norm_num)
  have hplus : 1+y≤1+1/(2:ℚ)^64 := by linarith
  have hb := mul_le_mul hu hplus (by linarith) (by norm_num)
  norm_num at hb ⊢
  linarith

/-- The three discarded singleton starts and the exact numerical margin. -/
theorem complement_charges :
    (7:ℕ) ∣ 8*8191-1 ∧ (11:ℕ) ∣ 2*131071-1 ∧ (13:ℕ) ∣ 8*131071-1 ∧
    (9/(2:ℚ)^18)*(4/3) + 8/(3*2^31)
       + (4/3)/2^24/(1-1/4096) + 1/(12*8191) + 1/(12*131071)
       + 4/(3*524287) + 32/(9*2^31)
       < 1-(1+1/(2:ℚ)^64)/((1+1/16384)*(1-1/(2:ℚ)^24)) ∧
    1/(2*65537:ℚ) + 1/137089 + 1/274177 + 1/(2*67280421310721)
       + 1/(2:ℚ)^16 < 9/(2:ℚ)^18 := by norm_num

/-- A Mersenne start with two available copies has at most two distinct singleton jumps. -/
theorem cubefree_start_costs {x : ℚ} (hx : 0 ≤ x) (hm : x ≤ 1/65536) :
    (5/4)*x/(1-x)+x/100 ≤ (13/10)*x ∧
    x/(16*(1-x))+x/100 ≤ (3/40)*x := by
  have hsq := mul_le_mul_of_nonneg_right hm hx
  constructor
  · rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith : 0 < 1-x)]
    nlinarith
  · rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith : 0 < 16*(1-x))]
    nlinarith

/-- A bound for the necessary group loss, allowing any finite collection of bases. -/
theorem cubefree_required_loss {y S U z : ℚ} (hy : 0 < y) (hs : y ≤ 1/65536)
    (hm : S ≤ (37/48)*y) (hu : 1-S ≤ U) (hU : U ≤ 1)
    (hz : 0 ≤ z) (hz' : z ≤ y^2) :
    1+z < (1+y)*U ∧ y-S-3*y^2 ≤ 1-(1+z)/((1+y)*U) := by
  let w := (1+y)*U-1
  have hyS : y*S ≤ y^2 := by
    nlinarith [mul_le_mul_of_nonneg_left (show S ≤ y by linarith) hy.le]
  have hlow : y-S-y^2 ≤ w := by
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ 1+y by linarith)]
  have hhigh : w ≤ y := by
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_left hU (show 0 ≤ 1+y by linarith)]
  have hzw : z < w := by nlinarith [mul_le_mul_of_nonneg_right hs hy.le]
  have hw : 0 ≤ w := by linarith
  have he : (1+y)*U = 1+w := by dsimp [w]; ring
  rw [he]
  constructor
  · linarith
  · have hw2 : w^2 ≤ y^2 := by nlinarith [mul_self_le_mul_self hw hhigh]
    calc
      y-S-3*y^2 ≤ w-w^2-z := by linarith
      _ ≤ 1-(1+z)/(1+w) := by
        rw [le_sub_comm, div_le_iff₀ (by linarith : 0 < 1+w)]
        nlinarith [mul_nonneg (sq_nonneg w) hw, mul_nonneg hz hw]

/-- The upper and lower coefficients in the five small-mass cases are disjoint. -/
theorem cubefree_loss_gaps {y : ℚ} (hy : 0 < y) (hs : y ≤ 1/65536) :
    (2275/3072)*y < (1-1/12)*y-3*y^2 ∧
    y/3 < (1-1/3)*y-3*y^2 ∧
    (17/32+1/48+13/80)*y < (1-13/48)*y-3*y^2 ∧
    (1/3+3/80)*y < (1-25/48)*y-3*y^2 ∧
    (1/48+3/80+13/80)*y < (1-37/48)*y-3*y^2 := by
  have hy2 := mul_le_mul_of_nonneg_right hs hy.le
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

/-- Count disjoint layers requiring one full charge at some prime.
For the Mersenne bound a charge has size three at a Mersenne prime and one elsewhere. -/
theorem count_charged_layers {ι α : Type*} (layers : Finset ι) (primes : Finset α)
    (used : ι → α → ℕ) (stock cost : α → ℕ)
    (positive : ∀ p ∈ primes, 0 < cost p)
    (budget : ∀ p ∈ primes, ∑ i ∈ layers, used i p ≤ stock p)
    (charge : ∀ i ∈ layers, ∃ p ∈ primes, cost p ≤ used i p) :
    layers.card ≤ ∑ p ∈ primes, stock p / cost p := by
  calc
    layers.card = ∑ _i ∈ layers, 1 := by simp
    _ ≤ ∑ i ∈ layers, ∑ p ∈ primes, used i p / cost p := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨p,hp,h⟩ := charge i hi
      have hone : 1 ≤ used i p / cost p := by
        apply (Nat.le_div_iff_mul_le (positive p hp)).mpr
        simpa using h
      exact hone.trans (Finset.single_le_sum (f := fun q => used i q / cost q)
        (fun _ _ => Nat.zero_le _) hp)
    _ = ∑ p ∈ primes, ∑ i ∈ layers, used i p / cost p := Finset.sum_comm
    _ ≤ ∑ p ∈ primes, stock p / cost p := by
      apply Finset.sum_le_sum
      intro p hp
      apply (Nat.le_div_iff_mul_le (positive p hp)).mpr
      rw [Finset.sum_mul]
      exact (Finset.sum_le_sum fun i _ => Nat.div_mul_le_self (used i p) (cost p)).trans
        (budget p hp)

/-- A Fermat contribution beginning at scale 2^(-4h) preserves the near-one gaps. -/
theorem mixed_tail_gaps {y l s : ℚ} (hy : 0 < y) (hs : y ≤ 1/65536)
    (hl : l+1/120 ≤ 1-s) :
    (1+y)*(1+5*y^4) < 1+y+y^2/2 ∧ l*y+4*y^4 < (1-s)*y-3*y^2 := by
  have hsq := mul_self_le_mul_self hy.le (show y ≤ 1/8 by linarith)
  have hfour := mul_le_mul_of_nonneg_right hsq (sq_nonneg y)
  have htwo := mul_le_mul_of_nonneg_left (show 1+y ≤ 2 by linarith)
    (show 0 ≤ 5*y^4 by positivity)
  constructor
  · nlinarith [sq_pos_of_pos hy]
  · nlinarith [mul_le_mul_of_nonneg_right hl hy.le,
      mul_le_mul_of_nonneg_right hs hy.le]

/-- A negative contribution at least eight times the first positive scale forces scale two. -/
theorem mixed_first_negative {x : ℚ} (hx : 0 < x) : (1+x)*(1-8*x) < 1-4*x := by
  nlinarith [sq_nonneg x]

end Erdos1052.MersenneMass
