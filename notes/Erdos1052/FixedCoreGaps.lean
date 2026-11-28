import PrimeDouble625

/-! Tail and perturbation estimates for fixed repeated cores. -/

namespace Erdos1052.FixedCoreGaps

open Erdos1052.Core625 Erdos1052.CoreBounds

/-- The contribution of Mersenne starts above the cutoff tends to one. -/
theorem shifted_roots_tail (S : Finset ℕ) {x s : ℕ} (hs : 13 ≤ s)
    (hx : 2^s ≤ x+2) (hS : ∀ q ∈ S, x < q) :
    (∏ q ∈ S, if demand q = 1 then pathBound q else 1) ≤ mersenneBound s := by
  let R := S.filter (fun q => demand q = 1)
  let t := fun q : ℕ => (1+q).factorization 2
  have hr (q : ℕ) (hq : q ∈ R) : q ∈ S ∧ demand q = 1 := Finset.mem_filter.mp hq
  have hpow (q : ℕ) (hq : q ∈ R) : 2 ^ t q = 1+q := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
    change 2 ^ t q * demand q = 1+q at h
    simpa only [(hr q hq).2, mul_one] using h
  have hinj : Set.InjOn t R := by
    intro q hq p hp he
    have h1 := hpow q hq
    rw [show t q = t p from he, hpow p hp] at h1
    omega
  rw [← Finset.prod_filter]
  change (∏ q ∈ R, pathBound q) ≤ _
  calc
    _ = ∏ j ∈ R.image t, mersenneFactor j := by
      rw [Finset.prod_image hinj]
      apply Finset.prod_congr rfl
      intro q hq
      have hv : (2:ℚ)^t q = 1+q := by exact_mod_cast hpow q hq
      unfold pathBound mersenneFactor
      rw [hv]
      congr 1 <;> ring
    _ ≤ _ := by
      apply large_mersenne_product (R.image t) hs
      intro j hj
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
      have hq' := hS q (hr q hq).1
      have hle : (2:ℕ)^s ≤ 2^(t q) := by rw [hpow q hq]; omega
      exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hle

/-- A product bound for ordinary primes with finite unused supplies. -/
theorem shifted_tail (S : Finset ℕ) {x s D : ℕ} (hs : 13 ≤ s)
    (hx : 2^s ≤ x+2) (hx' : 1 ≤ x) (hD : D ≠ 0) (hp : primeSupport S)
    (hr : ∀ q ∈ S, x < q) (hd : demands S ∣ D * primesProduct S) :
    abundancy S ≤ (1+2/(x:ℚ))^D.primeFactorsList.length * mersenneBound s := by
  apply le_trans (compatible_tail_bound S demand hx' hD (fun q hq =>
    ⟨(hp q hq).1,hr q hq,Nat.ordCompl_pos 2 (by omega),
      twice_oddPart_shift_le ((hp q hq).1.odd_of_ne_two (hp q hq).2)⟩) hd)
  exact mul_le_mul_of_nonneg_left (shifted_roots_tail S hs hx hr) (by positivity)

/-- A bound on the total reciprocal loss at starts bounds the product of all paths. -/
theorem reciprocal_product {ι : Type*} (I : Finset ι) (loss : ι → ℚ)
    (h : ∀ i ∈ I, 0 ≤ loss i ∧ loss i ≤ 1) :
    1-(∑ i ∈ I, loss i) ≤ ∏ i ∈ I, (1-loss i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hi' := h i (Finset.mem_insert_self _ _)
    have hI := fun j hj => h j (Finset.mem_insert_of_mem hj : j ∈ insert i I)
    have hs : 0 ≤ ∑ j ∈ I, loss j := Finset.sum_nonneg (fun j hj => (hI j hj).1)
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    calc
      _ ≤ (1-loss i)*(1-∑ j ∈ I, loss j) := by nlinarith [mul_nonneg hi'.1 hs]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hI) (by linarith)

/-- The cost coefficient of a path after adjoining its first prime.
Here m*q is one more than the successor prime. -/
theorem path_coefficient_step {q m B : ℚ} (hq : 0 < q) (hm : 0 < m) (hB : 0 < B) :
    (q+1)*(1-1/((1+1/q)*B)) = 1 + (m*q*(1-1/B))/m := by
  field_simp
  ring

/-- Removing new core factors and their dependent paths preserves a certified gap. -/
theorem transfer_window {y t z L : ℚ} (hy : 0 < y) (hy' : y ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ y/64) (hz : 0 ≤ z) (hz' : z ≤ y/8)
    (hL : 0 ≤ L) (hL' : L ≤ 6*t) :
    2-y < 2*(1-L)*(1-t*t)/(1+z) ∧ 1-y/4 < (1-L)*(1-t*t) := by
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t*t ≤ t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have hkeep : 1-7*t ≤ (1-L)*(1-t*t) := by
    nlinarith [mul_nonneg hL (mul_nonneg ht ht)]
  constructor
  · apply (lt_div_iff₀ (by linarith : 0 < 1+z)).2
    nlinarith [mul_nonneg hy.le hz]
  · linarith

/-- A removed Fermat divisor and the power of two cannot both be large at a seed-three gap. -/
theorem removed_prime_window {y u z : ℚ} (hy : 0 < y) (hy' : y ≤ 1)
    (hu : 0 ≤ u) (hu' : u ≤ y/4) (hz : 0 ≤ z) (hz' : z ≤ y/4) :
    2-y < 2/((1+u)*(1+z)) := by
  apply (lt_div_iff₀ (mul_pos (by linarith) (by linarith))).2
  have hnext := mul_le_mul (show 1+u ≤ 1+y/4 by linarith)
    (show 1+z ≤ 1+y/4 by linarith) (by linarith : 0 ≤ 1+z) (by linarith : 0 ≤ 1+y/4)
  have ht := mul_le_mul_of_nonneg_left hnext (show 0 ≤ 2-y by linarith)
  nlinarith [sq_pos_of_pos hy, mul_nonneg hy.le (sq_nonneg y)]

/-- Every nonzero initial residue has a multiple of s among its s-1 binary shifts. -/
def coversBinaryShifts (s : ℕ) : Bool :=
  (List.range' 1 (s-1)).all fun u =>
    (List.range (s-1)).any fun j => (1+2^j*u) % s == 0

theorem short_shift_moduli :
    coversBinaryShifts 11 ∧ coversBinaryShifts 13 ∧ coversBinaryShifts 19 := by
  decide +kernel

end Erdos1052.FixedCoreGaps
