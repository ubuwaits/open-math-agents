import Mathlib

/-! The modified Dedekind-psi height and a necessary equation for the odd core. -/

namespace Erdos1052.AdditiveHeight

/-- Defant's completely additive height, recursively evaluated on prime factors. -/
def height (n : ℕ) : ℕ :=
  (n.primeFactorsList.attach.map fun p =>
    if p.val = 2 then 1 else 1 + height ((p.val+1)/2)).sum
termination_by n
decreasing_by
  have hle := Nat.le_of_mem_primeFactorsList p.property
  have htwo := (Nat.prime_of_mem_primeFactorsList p.property).two_le
  omega

def primeWeight (p : ℕ) : ℕ :=
  if p = 2 then 1 else 1 + height ((p+1)/2)

theorem height_eq (n : ℕ) : height n = (n.primeFactorsList.map primeWeight).sum := by
  rw [height]
  simp
  rfl

@[simp] theorem height_one : height 1 = 0 := by simp [height_eq]

@[simp] theorem height_two : height 2 = 1 := by simp [height_eq,primeWeight]

theorem height_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    height (m*n) = height m + height n := by
  simp only [height_eq]
  simpa using ((Nat.perm_primeFactorsList_mul hm hn).map primeWeight).sum_eq

theorem height_prime {p : ℕ} (hp : p.Prime) : height p = primeWeight p := by
  simp [height_eq,Nat.primeFactorsList_prime hp]

theorem height_shift {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) : height (p+1) = height p := by
  have odd := hp.odd_of_ne_two ho
  obtain ⟨k,hk⟩ := odd
  have half : (p+1)/2 = k+1 := by omega
  have eqn : p+1 = 2*(k+1) := by omega
  rw [height_prime hp,primeWeight,if_neg ho,half,eqn,height_mul (by decide) (by omega),height_two]

theorem height_pow_two (a : ℕ) : height (2^a) = a := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ,height_mul (by positivity) (by decide),ih,height_two]

theorem height_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) : height (∏ i ∈ s, f i) = ∑ i ∈ s, height (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, 0 < f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,height_mul
      (hf a (Finset.mem_insert_self ..)).ne' (Finset.prod_pos hs).ne',ih hs]

/-- Every simple odd-prime factor cancels from the height equation. -/
theorem core_balance {a c sigma : ℕ} (s : Finset ℕ) (hc : 0 < c) (hu : 0 < sigma)
    (hp : ∀ q ∈ s, q.Prime ∧ q ≠ 2)
    (balance : (2^a+1)*sigma*(∏ q ∈ s, (q+1)) = 2^(a+1)*c*(∏ q ∈ s, q)) :
    height (2^a+1) + height sigma = (a+1) + height c := by
  have hq : ∀ q ∈ s, 0 < q := fun q hq => (hp q hq).1.pos
  have hs : (∑ q ∈ s, height (q+1)) = ∑ q ∈ s, height q :=
    Finset.sum_congr rfl fun q hq => height_shift (hp q hq).1 (hp q hq).2
  have h := congrArg height balance
  rw [height_mul (by positivity) (Finset.prod_pos (fun _ _ => Nat.succ_pos _)).ne',
    height_mul (by positivity) hu.ne',height_prod s (fun q => q+1) (fun _ _ => Nat.succ_pos _),
    height_mul (by positivity) (Finset.prod_pos hq).ne',height_mul (by positivity) hc.ne',
    height_prod s (fun q => q) hq,height_pow_two,hs] at h
  omega

/-- The integer height bounds the binary size of every positive input. -/
theorem le_pow_height (n : ℕ) : n ≤ 2^height n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 1
    · have : 0 < (2:ℕ)^height n := by positivity
      omega
    by_cases hp : n.Prime
    · by_cases he : n=2
      · subst n; simp
      have hhalf : (n+1)/2 < n := by omega
      have hb := ih ((n+1)/2) hhalf
      obtain ⟨k,hk⟩ := hp.odd_of_ne_two he
      rw [height_prime hp,primeWeight,if_neg he,pow_add,pow_one]
      omega
    · obtain ⟨u,v,hu,hv,hprod⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hp
      have hne : u*v ≠ 0 := by omega
      have hb := Nat.mul_le_mul (ih u hu) (ih v hv)
      simpa only [← hprod, height_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne),
        pow_add] using hb

theorem base_excess (a : ℕ) : a+1 ≤ height (2^a+1) := by
  by_contra! h
  have hu := Nat.pow_le_pow_right (n := 2) (by decide) (show height (2^a+1) ≤ a by omega)
  have hl := le_pow_height (2^a+1)
  omega

/-- Any value in the upper half of the dyadic interval already costs j height units. -/
theorem layer_height {n j : ℕ} (lo : 2^j < 2*n) : j ≤ height n := by
  by_contra! h
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show height n+1 ≤ j by omega)
  rw [pow_succ] at hp
  have hn := le_pow_height n
  omega

/-- The extra height unit of a cyclotomic factor lying above its leading power. -/
theorem extra_unit {n j : ℕ} (lo : 2^j < n) : j+1 ≤ height n := by
  by_contra! h
  have hu := Nat.pow_le_pow_right (n := 2) (by decide) (show height n ≤ j by omega)
  have hn := le_pow_height n
  omega

/-- Uniform bounds for both signs of the first Möbius factor, down to the base two. -/
theorem mobius_windows {y t : ℚ} (hy : 0 < y) (hy' : y ≤ 1/2)
    (ht : 0 ≤ t) (ht' : t ≤ y/3) :
    1/2 < (1-t)/(1+y) ∧ 1 < (1+y)*(1-t) ∧ (1+y)/(1-t) < 2 := by
  have hyt := mul_le_mul_of_nonneg_right hy' ht
  have hd : 0 < 1-t := by linarith
  constructor
  · rw [lt_div_iff₀ (by linarith : 0 < 1+y)]
    linarith
  constructor
  · nlinarith
  · rw [div_lt_iff₀ hd]
    linarith

/-- Add the height units forced by all cyclotomic factors simultaneously. -/
theorem sum_layer_costs {ι : Type*} (s : Finset ι) (value degree bonus : ι → ℕ)
    {h a : ℕ} (positive : ∀ i ∈ s, 0 < value i)
    (factors : (2^h+1)*(∏ i ∈ s, value i) = 2^a+1)
    (cost : ∀ i ∈ s, degree i + bonus i ≤ height (value i)) :
    height (2^h+1) + (∑ i ∈ s, degree i) + (∑ i ∈ s, bonus i) ≤ height (2^a+1) := by
  have total := Finset.sum_le_sum cost
  rw [Finset.sum_add_distrib] at total
  rw [← factors,height_mul (by positivity) (Finset.prod_pos positive).ne',height_prod s value positive]
  omega

/-- The smallest possible height in a prime-power layer requires loss at least y/2. -/
theorem prime_power_loss {y z : ℚ} (hy : 0 < y) (hu : y ≤ 1/2)
    (hz : z ≤ y^3) : y/2 ≤ (y-z)/(1+y) := by
  rw [le_div_iff₀ (by linarith : 0 < 1+y)]
  have htwo := mul_le_mul_of_nonneg_right hu hy.le
  have hthree := mul_le_mul_of_nonneg_right hu (sq_nonneg y)
  nlinarith

/-- An odd prime of the assigned residual already contributes its own shift cost. -/
theorem divisor_cost {p d : ℕ} (hp : p.Prime) (ho : p ≠ 2) (hd : 0 < d)
    (hpd : p ∣ d) : (p+1)*d ≤ p*2^height d := by
  obtain ⟨k,rfl⟩ := hpd
  have hk : k ≠ 0 := right_ne_zero_of_mul hd.ne'
  have hp1 := le_pow_height (p+1)
  rw [height_shift hp ho] at hp1
  rw [height_mul hp.ne_zero hk,pow_add]
  calc
    (p+1)*(p*k) = p*((p+1)*k) := by ring
    _ ≤ p*(2^height p*2^height k) := Nat.mul_le_mul_left p (Nat.mul_le_mul hp1 (le_pow_height k))

/-- At large enough scale the neutral paths in a charged residue class are too small. -/
theorem neutral_loss_gap {y z : ℚ} (hy : 0 < y) (hu : y ≤ 1/32)
    (hz : z ≤ y^3) : (23/24)*y < (y-z)/(1+y) := by
  rw [lt_div_iff₀ (by linarith : 0 < 1+y)]
  have htwo := mul_le_mul_of_nonneg_right hu hy.le
  have hthree := mul_le_mul_of_nonneg_right hu (sq_nonneg y)
  nlinarith

theorem two_step_count {e J k : ℕ} (hb : (e-J)/2 ≤ k) : e ≤ J+2*k+1 := by omega

/-- Count occurrences of one marked odd prime in the full prime-shift recursion. -/
def visits (m n : ℕ) : ℕ :=
  (n.primeFactorsList.attach.map fun p =>
    if p.val = 2 then 0 else (if p.val = m then 1 else 0) + visits m ((p.val+1)/2)).sum
termination_by n
decreasing_by
  have hle := Nat.le_of_mem_primeFactorsList p.property
  have htwo := (Nat.prime_of_mem_primeFactorsList p.property).two_le
  omega

private def visitWeight (m p : ℕ) : ℕ :=
  if p = 2 then 0 else (if p = m then 1 else 0) + visits m ((p+1)/2)

private theorem visits_eq (m n : ℕ) : visits m n = (n.primeFactorsList.map (visitWeight m)).sum := by
  rw [visits]
  change (n.primeFactorsList.attach.map (fun p => visitWeight m p.val)).sum = _
  simp

theorem visits_mul (m : ℕ) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    visits m (x*y) = visits m x + visits m y := by
  simp only [visits_eq]
  simpa using ((Nat.perm_primeFactorsList_mul hx hy).map (visitWeight m)).sum_eq

@[simp] theorem visits_two (m : ℕ) : visits m 2 = 0 := by simp [visits_eq,visitWeight]

theorem visits_pow_two (m b : ℕ) : visits m (2^b) = 0 := by
  induction b with
  | zero => simp [visits_eq]
  | succ b ih => rw [pow_succ,visits_mul m (by positivity) (by decide),visits_two,ih]

theorem visits_shift (m : ℕ) {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    visits m p = visits m (p+1) + (if p = m then 1 else 0) := by
  obtain ⟨k,hk⟩ := hp.odd_of_ne_two hne
  have half : (p+1)/2 = k+1 := by omega
  have eqn : p+1 = 2*(k+1) := by omega
  have hw : visits m p = visitWeight m p := by simp [visits_eq,Nat.primeFactorsList_prime hp]
  rw [hw,visitWeight,if_neg hne,half,eqn,visits_mul m (by decide) (by omega),visits_two]
  omega

private theorem visits_prod (m : ℕ) {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hg : ∀ i ∈ s, 0 < g i) : visits m (∏ i ∈ s, g i) = ∑ i ∈ s, visits m (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [visits_eq]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, 0 < g i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,visits_mul m
      (hg a (Finset.mem_insert_self ..)).ne' (Finset.prod_pos hs).ne',ih hs]

/-- Each distinct ordinary prime contributes exactly one possible extra occurrence. -/
theorem marker_group (m : ℕ) {A d b : ℕ} (s : Finset ℕ) (hA : 0 < A) (hd : 0 < d)
    (hp : ∀ q ∈ s, q.Prime ∧ q ≠ 2)
    (bal : A * (∏ q ∈ s, (q+1)) = d * 2^b * (∏ q ∈ s, q)) :
    visits m A = visits m d + (if m ∈ s then 1 else 0) := by
  classical
  have hq : ∀ q ∈ s, 0 < q := fun q h => (hp q h).1.pos
  have hs : (∑ q ∈ s, visits m q) = (∑ q ∈ s, visits m (q+1)) + (if m ∈ s then 1 else 0) := by
    calc (∑ q ∈ s, visits m q) = ∑ q ∈ s, (visits m (q+1) + (if q = m then 1 else 0)) :=
           Finset.sum_congr rfl fun q h => visits_shift m (hp q h).1 (hp q h).2
         _ = _ := by rw [Finset.sum_add_distrib]; simp
  have h := congrArg (visits m) bal
  rw [visits_mul m hA.ne' (Finset.prod_pos (fun _ _ => Nat.succ_pos _)).ne',
    visits_prod m s (fun q => q+1) (fun _ _ => Nat.succ_pos _),
    visits_mul m (by positivity) (Finset.prod_pos hq).ne',visits_mul m hd.ne' (by positivity),
    visits_pow_two,visits_prod m s (fun q => q) hq,hs] at h
  omega

theorem marker_core (m : ℕ) {a c sigma : ℕ} (s : Finset ℕ) (hc : 0 < c) (hu : 0 < sigma)
    (hp : ∀ q ∈ s, q.Prime ∧ q ≠ 2)
    (bal : (2^a+1)*sigma*(∏ q ∈ s, (q+1)) = 2^(a+1)*c*(∏ q ∈ s, q)) :
    visits m (2^a+1) + visits m sigma = visits m c + (if m ∈ s then 1 else 0) := by
  rw [mul_comm (2^(a+1)) c] at bal
  have h := marker_group m s (by positivity) hc hp bal
  rwa [visits_mul m (by positivity) hu.ne'] at h

theorem squarefree_abundancy_bound :
    (5/4:ℚ)*2*(4/3)*(16/15)*(64/63)*(2048/2047) < 4 := by norm_num

theorem extra_leaf_mass {y mass loss : ℚ} (hy : 0 < y) (hu : y ≤ 1/65536)
    (hl : y*(1-y) ≤ loss) (hc : loss ≤ 23*y/24 + mass) : y/25 < mass := by
  have := mul_le_mul_of_nonneg_left hu hy.le
  nlinarith

end Erdos1052.AdditiveHeight
