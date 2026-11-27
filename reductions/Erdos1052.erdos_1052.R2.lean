import FormalConjectures.ErdosProblems.«1052»

/-!
# Erdős 1052 and odd squarefree completions

Write n = 2^a c s. The odd factor c contains the full powers of the odd
primes occurring at least twice. The remaining factor s is squarefree.
For each fixed pair (a,c) there is at most one possible s. If s has at
most three prime factors, then n is 6, 60 or 90. In the five
known examples the values of c are 1, 9 and 625. S. W. Graham classified
the case c = 1 in the Fibonacci Quarterly (1989). Jennifer DeBoer classified
c = 9 in Nonexistence of Certain Unitary Perfect Numbers (1993).

Credit: @ubuwaits. The divisor-sum lemmas below are from @adammcarter.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2

-- Bound c on the remaining solutions, those with at least four odd primes
-- occurring to the first power. All other solutions are classified below.
def H1 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    4 ≤ (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card →
    (∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1),
      p ^ n.factorization p) ≤ B

-- For each fixed odd powerful c, only finitely many exponents a >= 5 pass
-- the following finite arithmetic test. An odd integer is powerful if every
-- prime dividing it occurs at least twice. The value c = 1 is included.
-- Set b = 2^a c and u = sigma*(b). Every potential prime of s lies in [3,u].
-- At least four primes must be chosen when a >= 5 (proved below).
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}.Finite

-- The following unitary-divisor product formula and prime-power factorization
-- lemmas are from @adammcarter's accepted reduction R1 for this problem.
-- Membership in the set of all unitary divisors of n (n itself included).
theorem mem_udiv {n d : ℕ} :
    d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [and_assoc]

theorem self_mem_udiv {n : ℕ} (hn : n ≠ 0) :
    n ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  rw [mem_udiv, Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact ⟨dvd_rfl, hn, Nat.coprime_one_right n⟩

theorem proper_eq_erase (n : ℕ) :
    Erdos1052.properUnitaryDivisors n = (Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors).erase n := by
  ext d
  simp only [Erdos1052.properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hc⟩
    exact ⟨h2.ne, ⟨hd, by omega⟩, hc⟩
  · rintro ⟨hne, ⟨hd, hn⟩, hc⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
    exact ⟨⟨Nat.pos_of_ne_zero hd0,
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hne⟩, hd, hc⟩

theorem sum_udiv_eq_sum_proper_add {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      (∑ i ∈ Erdos1052.properUnitaryDivisors n, i) + n := by
  rw [proper_eq_erase, Finset.sum_erase_add _ _ (self_mem_udiv hn)]

-- A unitary perfect number is positive and its unitary divisor sum equals 2 * n.
theorem sum_udiv_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    0 < n ∧ ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d = 2 * n := by
  obtain ⟨hs, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [sum_udiv_eq_sum_proper_add hpos.ne', hs]
  ring

theorem factorization_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) (p : ℕ) :
    d.factorization p = if p ∈ d.primeFactors then n.factorization p else 0 := by
  obtain ⟨hd, hn, hc⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hq : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  split_ifs with hp
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n / d := by
      intro h'
      have := Nat.dvd_gcd hpd h'
      rw [hc.gcd_eq_one] at this
      exact hpp.not_dvd_one this
    conv_rhs => rw [hmul]
    rw [Nat.factorization_mul hd0 hq, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · by_contra h'
    exact hp (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr h')

theorem ppart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ^ n.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

theorem factorization_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (q : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p).factorization q = if q ∈ S then n.factorization q else 0 := by
  rw [Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (hS hp)).factorization_pow, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

theorem primeFactors_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_ppart hS]
  split_ifs with h
  · simp only [h, iff_true]
    exact Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hS h)
  · simp [h]

theorem ppart_mem_udiv {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  have h0 := ppart_ne_zero hS
  have hdvd : (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd h0 hn]
    intro q
    rw [factorization_ppart hS]
    split_ifs <;> simp
  refine mem_udiv.mpr ⟨hdvd, hn, Nat.coprime_of_dvd fun p hp h1 h2 => ?_⟩
  have hq : n / (∏ p ∈ S, p ^ n.factorization p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero h0)).ne'
  have e1 := (hp.dvd_iff_one_le_factorization h0).mp h1
  have e2 := (hp.dvd_iff_one_le_factorization hq).mp h2
  rw [factorization_ppart hS] at e1
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, factorization_ppart hS] at e2
  split_ifs at e1 e2 <;> omega

theorem eq_ppart_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  obtain ⟨hd, hn, -⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hsub := Nat.primeFactors_mono hd hn
  exact Nat.eq_of_factorization_eq hd0 (ppart_ne_zero hsub) fun q => by
    rw [factorization_of_mem_udiv h, factorization_ppart hsub]

-- Product formula: the unitary divisor sum of n is the product of (1 + p^a) over p^a || n.
theorem sum_udiv_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ n.factorization p)
    (fun d hd => Finset.mem_powerset.mpr (Nat.primeFactors_mono (mem_udiv.mp hd).1 hn))
    (fun S hS => ppart_mem_udiv hn (Finset.mem_powerset.mp hS))
    (fun d hd => (eq_ppart_of_mem_udiv hd).symm)
    (fun S hS => primeFactors_ppart (Finset.mem_powerset.mp hS))
    (fun d hd => eq_ppart_of_mem_udiv hd)

theorem prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
  (eq_ppart_of_mem_udiv (self_mem_udiv hn)).symm

-- If P is the largest odd prime in a support, it divides none of the
-- numbers q + 1 contributed by that support.
theorem max_not_dvd_shift {S : Finset ℕ} (hs : S.Nonempty)
    (hprime : ∀ q ∈ S, q.Prime ∧ q ≠ 2) :
    ¬ S.max' hs ∣ ∏ q ∈ S, (1 + q) := by
  let P := S.max' hs
  have hP := hprime P (Finset.max'_mem S hs)
  intro hd
  obtain ⟨q, hq, hdiv⟩ := (hP.1.prime.dvd_finsetProd_iff _).mp hd
  have hqP : q ≤ P := Finset.le_max' S q hq
  by_cases heq : q = P
  · subst q
    exact hP.1.not_dvd_one ((Nat.dvd_add_iff_left dvd_rfl).mpr hdiv)
  · have hoP := hP.1.odd_of_ne_two hP.2
    have hoq := (hprime q hq).1.odd_of_ne_two (hprime q hq).2
    obtain ⟨i, hi⟩ := hoP
    obtain ⟨j, hj⟩ := hoq
    have hle := Nat.le_of_dvd (by omega : 0 < 1 + q) hdiv
    omega

theorem max_dvd_denominator {S : Finset ℕ} {u v : ℕ} (hs : S.Nonempty)
    (hprime : ∀ q ∈ S, q.Prime ∧ q ≠ 2)
    (hbal : u * (∏ p ∈ S, (1 + p)) = v * ∏ p ∈ S, p) :
    S.max' hs ∣ u := by
  have hm := Finset.max'_mem S hs
  have hd : S.max' hs ∣ v * ∏ p ∈ S, p :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p : ℕ => p) hm) v
  rw [← hbal] at hd
  exact ((hprime _ hm).1.dvd_mul.mp hd).resolve_right (max_not_dvd_shift hs hprime)

-- For a reduced target ratio v/u the largest remaining prime is exactly
-- the largest prime factor of u. Dividing by its factor (1+p)/p therefore
-- gives a deterministic search in strictly decreasing odd primes.
theorem largest_reduced_denominator {S : Finset ℕ} {u v : ℕ} (hs : S.Nonempty)
    (hu : u ≠ 0) (hc : u.Coprime v) (hprime : ∀ q ∈ S, q.Prime ∧ q ≠ 2)
    (hbal : u * (∏ p ∈ S, (1 + p)) = v * ∏ p ∈ S, p) :
    S.max' hs ∈ u.primeFactors ∧ ∀ q ∈ u.primeFactors, q ≤ S.max' hs := by
  refine ⟨Nat.mem_primeFactors.mpr ⟨(hprime _ (Finset.max'_mem S hs)).1,
    max_dvd_denominator hs hprime hbal, hu⟩, ?_⟩
  intro q hq
  have hq' := Nat.prime_of_mem_primeFactors hq
  have hqu := Nat.dvd_of_mem_primeFactors hq
  have hqv : ¬ q ∣ v := by
    intro hd
    have h := Nat.dvd_gcd hqu hd
    rw [hc.gcd_eq_one] at h
    exact hq'.not_dvd_one h
  have hd : q ∣ v * ∏ p ∈ S, p := hbal ▸ dvd_mul_of_dvd_left hqu _
  obtain ⟨p, hp, hqp⟩ := (hq'.prime.dvd_finsetProd_iff (fun p : ℕ => p)).mp
    ((hq'.dvd_mul.mp hd).resolve_left hqv)
  have heq := ((hprime p hp).1.dvd_iff_eq hq'.ne_one).mp hqp
  exact Finset.le_max' S q (heq ▸ hp)

theorem support_bound {S : Finset ℕ} {u v : ℕ} (hu : 0 < u)
    (hprime : ∀ q ∈ S, q.Prime ∧ q ≠ 2)
    (hbal : u * (∏ p ∈ S, (1 + p)) = v * ∏ p ∈ S, p) :
    S ⊆ Finset.Icc 3 u := by
  intro p hp
  have hs : S.Nonempty := ⟨p, hp⟩
  have h := hprime p hp
  have h2 := h.1.two_le
  refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
  exact (Finset.le_max' S p hp).trans (Nat.le_of_dvd hu (max_dvd_denominator hs hprime hbal))

-- Equality of the two squarefree abundancy ratios is written with natural
-- cross products. The largest prime from S is forced into T. Cancel it and
-- repeat on a strictly smaller set.
theorem equal_support_of_cross_product {S T : Finset ℕ}
    (hs : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (ht : ∀ p ∈ T, p.Prime ∧ p ≠ 2)
    (hbal : (∏ p ∈ T, p) * (∏ p ∈ S, (1 + p)) =
      (∏ p ∈ T, (1 + p)) * ∏ p ∈ S, p) : S = T := by
  induction S using Finset.strongInduction generalizing T with
  | H S ih =>
    by_cases hne : S.Nonempty
    · let p := S.max' hne
      have hps : p ∈ S := Finset.max'_mem _ _
      have hp := (hs p hps).1
      have hd : p ∣ ∏ q ∈ T, q := max_dvd_denominator hne hs hbal
      obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
      have hpt : p ∈ T := ((ht q hq).1.dvd_iff_eq hp.ne_one).mp hpq ▸ hq
      have hsmall :
          (∏ q ∈ T.erase p, q) * (∏ q ∈ S.erase p, (1 + q)) =
          (∏ q ∈ T.erase p, (1 + q)) * ∏ q ∈ S.erase p, q := by
        rw [← Finset.mul_prod_erase T (fun q : ℕ => q) hpt,
          ← Finset.mul_prod_erase S (fun q : ℕ => 1 + q) hps,
          ← Finset.mul_prod_erase T (fun q : ℕ => 1 + q) hpt,
          ← Finset.mul_prod_erase S (fun q : ℕ => q) hps] at hbal
        apply mul_left_cancel₀ (a := p * (1 + p)) (Nat.mul_ne_zero hp.ne_zero (by omega))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hbal
      have hst := ih _ (Finset.erase_ssubset hps)
        (fun q hq => hs q (Finset.mem_of_mem_erase hq))
        (fun q hq => ht q (Finset.mem_of_mem_erase hq)) hsmall
      calc S = insert p (S.erase p) := (Finset.insert_erase hps).symm
        _ = insert p (T.erase p) := congrArg (insert p) hst
        _ = T := Finset.insert_erase hpt
    · have he := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      by_contra hT
      have hneT : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Ne.symm hT)
      have hm : T.max' hneT ∣ 1 := max_dvd_denominator (v := 1) hneT ht (by simpa using hbal.symm)
      exact (ht _ (Finset.max'_mem T hneT)).1.not_dvd_one hm

theorem unique_squarefree_completion {S T : Finset ℕ} {u v : ℕ} (hu : u ≠ 0)
    (hs : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (ht : ∀ p ∈ T, p.Prime ∧ p ≠ 2)
    (hS : u * (∏ p ∈ S, (1 + p)) = v * ∏ p ∈ S, p)
    (hT : u * (∏ p ∈ T, (1 + p)) = v * ∏ p ∈ T, p) : S = T := by
  apply equal_support_of_cross_product hs ht
  apply mul_left_cancel₀ hu
  calc u * ((∏ p ∈ T, p) * (∏ p ∈ S, (1 + p))) =
        (∏ p ∈ T, p) * (u * ∏ p ∈ S, (1 + p)) := by ac_rfl
    _ = (∏ p ∈ T, p) * (v * ∏ p ∈ S, p) := by rw [hS]
    _ = (v * ∏ p ∈ T, p) * ∏ p ∈ S, p := by ac_rfl
    _ = (u * ∏ p ∈ T, (1 + p)) * ∏ p ∈ S, p := by rw [hT]
    _ = u * ((∏ p ∈ T, (1 + p)) * ∏ p ∈ S, p) := by ac_rfl


-- A telescoping majorant for the contribution of odd prime powers with
-- exponent at least two. For odd p the next possible base is at least p+2.
theorem odd_square_tail (T : Finset ℕ) (k : ℕ) (hk : 3 ≤ k)
    (h : ∀ p ∈ T, k ≤ p ∧ Odd p) :
    (∏ p ∈ T, (1 + ((p : ℚ)^2)⁻¹)) ≤ 1 + (2 * (k : ℚ) - 3)⁻¹ := by
  induction T using Finset.strongInduction generalizing k with
  | H T ih =>
    have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℚ) < 2 * k - 3 := by linarith
    by_cases hne : T.Nonempty
    · let p := T.min' hne
      have hp := Finset.min'_mem T hne
      have hkp := (h p hp).1
      have hp' : (3 : ℚ) ≤ p := by exact_mod_cast (hk.trans hkp)
      have hp0 : (0 : ℚ) < p := by linarith
      have hppos : (0 : ℚ) < 2 * p - 3 := by linarith
      have hnext : ∀ q ∈ T.erase p, p + 2 ≤ q ∧ Odd q := by
        intro q hq
        obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
        have hpq : p ≤ q := Finset.min'_le T q hqT
        have ho := (h q hqT).2
        refine ⟨?_, ho⟩
        obtain ⟨i, hi⟩ := (h p hp).2
        obtain ⟨j, hj⟩ := ho
        omega
      have hrest := ih _ (Finset.erase_ssubset hp) (p + 2) (by omega) hnext
      have hstep : (1 + ((p : ℚ)^2)⁻¹) * (1 + (2 * ((p + 2 : ℕ) : ℚ) - 3)⁻¹) ≤
          1 + (2 * (p : ℚ) - 3)⁻¹ := by
        push_cast
        have hnextpos : (0 : ℚ) < 2 * ((p : ℚ) + 2) - 3 := by linarith
        rw [show 1 + (2 * (p : ℚ) - 3)⁻¹ =
            ((2 * (p : ℚ) - 3) + 1) / (2 * (p : ℚ) - 3) by
              rw [add_div, div_self hppos.ne', one_div], le_div_iff₀ hppos]
        field_simp [hnextpos, hp0]
        nlinarith
      have hanti : (2 * (p : ℚ) - 3)⁻¹ ≤ (2 * (k : ℚ) - 3)⁻¹ := by
        apply inv_anti₀ hkpos
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hkp) (by norm_num)) _
      rw [← Finset.mul_prod_erase T (fun p => 1 + ((p : ℚ)^2)⁻¹) hp]
      exact (mul_le_mul_of_nonneg_left hrest (by positivity)).trans (hstep.trans (by linarith))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne, le_of_lt hkpos]

-- Charge a factor 10/9 for each prime occurring once. For 3, 5 and 7 the
-- remaining weight is at most (9/10)(1+1/p). For p >= 11 it is at most
-- 1+1/p^2. With at most three charges, the product is bounded by
-- (4/3)(6/5)(8/7)(20/19) = 256/133.
theorem few_simple_odd_product {T : Finset ℕ} {e : ℕ → ℕ}
    (hprime : ∀ p ∈ T, p.Prime ∧ p ≠ 2 ∧ 0 < e p)
    (hfew : (T.filter (fun p => e p = 1)).card ≤ 3) :
    (∏ p ∈ T, (1 + ((p : ℚ) ^ e p)⁻¹)) ≤ 256 / 133 := by
  let A : Finset ℕ := {3, 5, 7}
  let w := fun p : ℕ => if p ∈ A then (9 / 10 : ℚ) * (1 + (p : ℚ)⁻¹)
    else 1 + ((p : ℚ)^2)⁻¹
  let m := fun p : ℕ => if e p = 1 then (10 / 9 : ℚ) else 1
  have hA : ∀ p ∈ A, 1 ≤ w p ∧ 1 + ((p : ℚ)^2)⁻¹ ≤ w p := by
    intro p hp
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num [w, A]
  have h11 : ∀ p ∈ T, p ∉ A → 11 ≤ p := by
    intro p hp hpa
    have hpr := hprime p hp
    by_contra! hsmall
    interval_cases p <;> norm_num [A] at *
  have hpoint : ∀ p ∈ T, 1 + ((p : ℚ) ^ e p)⁻¹ ≤ m p * w p := by
    intro p hp
    have hpr := hprime p hp
    have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hpr.1.two_le
    have hp0 : (0 : ℚ) < p := by linarith
    by_cases h1 : e p = 1
    · by_cases ha : p ∈ A
      · simp [h1, m, w, ha]
        ring_nf
        exact le_rfl
      · have hp11 : (11 : ℚ) ≤ p := by exact_mod_cast h11 p hp ha
        have hv : (p : ℚ)⁻¹ ≤ (9 : ℚ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
        have hsq : 0 ≤ ((p : ℚ)^2)⁻¹ := by positivity
        simp [h1, m, w, ha]
        linarith
    · have he2 : 2 ≤ e p := by omega
      have hs := inv_anti₀ (sq_pos_of_pos hp0) (pow_le_pow_right₀ (show (1 : ℚ) ≤ p by linarith) he2)
      simp only [m, if_neg h1, one_mul]
      by_cases ha : p ∈ A
      · exact (add_le_add_right hs 1).trans (hA p ha).2
      · simpa [w, ha] using (add_le_add_right hs 1)
  have hpos : ∀ p, 0 ≤ w p := by
    intro p
    dsimp [w]
    split <;> positivity
  have hlo : (∏ p ∈ T ∩ A, w p) ≤ ∏ p ∈ A, w p :=
    Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right (fun p _ => hpos p)
      (fun p hp _ => (hA p hp).1)
  have htail := odd_square_tail (T \ A) 11 (by decide) (fun p hp => by
    obtain ⟨hT, hNA⟩ := Finset.mem_sdiff.mp hp
    exact ⟨h11 p hT hNA, (hprime p hT).1.odd_of_ne_two (hprime p hT).2.1⟩)
  have hhi : (∏ p ∈ T \ A, w p) ≤ (20 / 19 : ℚ) := by
    rw [Finset.prod_congr rfl (fun p hp => if_neg (Finset.mem_sdiff.mp hp).2 : ∀ p ∈ T \ A,
      w p = 1 + ((p : ℚ)^2)⁻¹)]
    norm_num at htail ⊢
    exact htail
  have hm : (∏ p ∈ T, m p) ≤ (10 / 9 : ℚ)^3 := by
    change (∏ p ∈ T, if e p = 1 then (10 / 9 : ℚ) else 1) ≤ _
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    exact pow_le_pow_right₀ (by norm_num) hfew
  calc (∏ p ∈ T, (1 + ((p : ℚ) ^ e p)⁻¹))
      ≤ ∏ p ∈ T, m p * w p := Finset.prod_le_prod (fun _ _ => by positivity) hpoint
    _ = (∏ p ∈ T, m p) * ((∏ p ∈ T ∩ A, w p) * ∏ p ∈ T \ A, w p) := by
      rw [Finset.prod_mul_distrib, Finset.prod_inter_mul_prod_sdiff]
    _ ≤ (10 / 9 : ℚ)^3 * ((∏ p ∈ A, w p) * (20 / 19)) := by
      have hleft : 0 ≤ ∏ p ∈ T ∩ A, w p := Finset.prod_nonneg fun p _ => hpos p
      have hright : 0 ≤ ∏ p ∈ T \ A, w p := Finset.prod_nonneg fun p _ => hpos p
      have hall : 0 ≤ ∏ p ∈ A, w p := Finset.prod_nonneg fun p _ => hpos p
      exact mul_le_mul hm (mul_le_mul hlo hhi hright hall) (mul_nonneg hleft hright) (by norm_num)
    _ = 256 / 133 := by norm_num [A, w]

-- If 32 divides a unitary perfect number, at least four distinct odd primes
-- occur in it to the first power, regardless of its repeated prime powers.
theorem many_simple_primes {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (ha : 5 ≤ n.factorization 2) :
    4 ≤ (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card := by
  let T := n.primeFactors.erase 2
  have h2 : 2 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hprim : ∀ p ∈ T, p.Prime ∧ p ≠ 2 ∧ 0 < n.factorization p := by
    intro p hp
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hm
    exact ⟨hprime, hne, hprime.factorization_pos_of_dvd hn.2.ne' (Nat.dvd_of_mem_primeFactors hm)⟩
  have hfilter : T.filter (fun p => n.factorization p = 1) =
      n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1) := by
    ext p
    simp [T]
    tauto
  by_contra! hfew
  have hcard : (T.filter (fun p => n.factorization p = 1)).card ≤ 3 := by
    rw [hfilter]
    omega
  have hodd := few_simple_odd_product hprim hcard
  obtain ⟨hnpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hnpos.ne'] at hsum
  have hnum : (∏ p ∈ n.primeFactors, (1 + (p : ℚ) ^ n.factorization p)) = 2 * n := by
    exact_mod_cast hsum
  have hden : (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) = n := by
    exact_mod_cast prod_primeFactors_pow_self hnpos.ne'
  have hquot : ∀ p ∈ n.primeFactors, 1 + ((p : ℚ) ^ n.factorization p)⁻¹ =
      (1 + (p : ℚ) ^ n.factorization p) / ((p : ℚ) ^ n.factorization p) := by
    intro p hp
    have hp0 : 0 < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    field_simp
    ring
  have hratio : (∏ p ∈ n.primeFactors, (1 + ((p : ℚ) ^ n.factorization p)⁻¹)) = 2 := by
    rw [Finset.prod_congr rfl hquot, Finset.prod_div_distrib, hnum, hden]
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    field_simp
  rw [← Finset.mul_prod_erase n.primeFactors (fun p => 1 + ((p : ℚ) ^ n.factorization p)⁻¹) h2] at hratio
  have hinv := inv_anti₀ (by norm_num : (0 : ℚ) < 2^5)
    (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℚ)) ha)
  have heven : (1 : ℚ) + (2 ^ n.factorization 2 : ℚ)⁻¹ ≤ 33 / 32 := by
    norm_num at hinv
    linarith
  have hpos : 0 ≤ ∏ p ∈ T, (1 + ((p : ℚ) ^ n.factorization p)⁻¹) :=
    Finset.prod_nonneg fun _ _ => by positivity
  have hbound := mul_le_mul heven hodd hpos (by norm_num : 0 ≤ (33 / 32 : ℚ))
  change ((1 : ℚ) + (2 ^ n.factorization 2 : ℚ)⁻¹) *
    (∏ p ∈ T, (1 + ((p : ℚ) ^ n.factorization p)⁻¹)) = 2 at hratio
  rw [hratio] at hbound
  norm_num at hbound

-- For a <= 4, split the odd prime powers at 11. A larger component q
-- contributes at most 14/13 to the abundancy ratio and costs at least one
-- power of two in the divisor sum. This finite certificate includes every
-- subset of the five small odd values. The components 3 and 9 share a base.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem small_exponent_certificate :
    ∀ a ∈ Finset.range 5, ∀ L ∈ ({3, 5, 7, 9, 11} : Finset ℕ).powerset, ∀ j ∈ Finset.range 6,
      ¬ (3 ∈ L ∧ 9 ∈ L) →
      j + (∏ q ∈ L, (1 + q)).factorization 2 ≤ a + 1 →
      let b := 2 ^ a * ∏ q ∈ L, q
      let u := (if a = 0 then 1 else 1 + 2 ^ a) * ∏ q ∈ L, (1 + q)
      (if j = 0 then u = 2 * b else u < 2 * b ∧ 2 * b * 13 ^ j ≤ u * 14 ^ j) →
      j = 0 ∧ (b = 6 ∨ b = 60 ∨ b = 90) := by
  decide +kernel

theorem odd_component_data {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) :
    let a := n.factorization 2
    ∃ Q : Finset ℕ, (∀ q ∈ Q, Odd q ∧ 3 ≤ q) ∧ ¬ (3 ∈ Q ∧ 9 ∈ Q) ∧
      n = 2 ^ a * (∏ q ∈ Q, q) ∧
      (if a = 0 then 1 else 1 + 2 ^ a) * (∏ q ∈ Q, (1 + q)) = 2 * n := by
  let P := n.primeFactors.erase 2
  let comp := fun p : ℕ => p ^ n.factorization p
  let Q := P.image comp
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ 0 < n.factorization p := by
    intro p hp
    obtain ⟨hp2, hm⟩ := Finset.mem_erase.mp hp
    have hpr := Nat.prime_of_mem_primeFactors hm
    exact ⟨hpr, hp2, hpr.factorization_pos_of_dvd hn.2.ne' (Nat.dvd_of_mem_primeFactors hm)⟩
  have hdiv : ∀ p ∈ P, p ∣ comp p :=
    fun p hp => dvd_pow_self p (hP p hp).2.2.ne'
  have hbase : Set.InjOn comp P := by
    intro p hp q hq he
    have h1 := Nat.primeFactors_prime_pow (hP p hp).2.2.ne' (hP p hp).1
    have h2 := Nat.primeFactors_prime_pow (hP q hq).2.2.ne' (hP q hq).1
    change p ^ n.factorization p = q ^ n.factorization q at he
    rw [he, h2] at h1
    exact (Finset.singleton_inj.mp h1).symm
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hh := hP p hp
    have hp0 : 0 < comp p := pow_pos hh.1.pos _
    have hle := Nat.le_of_dvd hp0 (hdiv p hp)
    have := hh.1.two_le
    exact ⟨(hh.1.odd_of_ne_two hh.2.1).pow, by omega⟩
  · rintro ⟨h3, h9⟩
    obtain ⟨p, hp, he3⟩ := Finset.mem_image.mp h3
    obtain ⟨q, hq, he9⟩ := Finset.mem_image.mp h9
    have hp3 : p ∣ 3 := he3 ▸ hdiv p hp
    have hq9 : q ∣ 3 ^ 2 := by simpa using (he9 ▸ hdiv q hq : q ∣ 9)
    have hq3 := (hP q hq).1.dvd_of_dvd_pow hq9
    have hp' := (Nat.prime_three.dvd_iff_eq (hP p hp).1.ne_one).mp hp3
    have hq' := (Nat.prime_three.dvd_iff_eq (hP q hq).1.ne_one).mp hq3
    have heq : p = q := hp'.symm.trans hq'
    rw [heq, he9] at he3
    contradiction
  · change n = 2 ^ n.factorization 2 * (∏ q ∈ P.image comp, q)
    rw [Finset.prod_image hbase]
    have hself := prod_primeFactors_pow_self hn.2.ne'
    by_cases hm : 2 ∈ n.primeFactors
    · exact hself.symm.trans (Finset.mul_prod_erase n.primeFactors comp hm).symm
    · have h0 : n.factorization 2 = 0 := Finsupp.notMem_support_iff.mp (by
        rwa [Nat.support_factorization])
      simpa [h0, P, Finset.erase_eq_of_notMem hm, comp] using hself.symm
  · change (if n.factorization 2 = 0 then 1 else 1 + 2 ^ n.factorization 2) *
        (∏ q ∈ P.image comp, (1 + q)) = 2 * n
    rw [Finset.prod_image hbase]
    obtain ⟨hpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
    rw [sum_udiv_eq_prod hpos.ne'] at hsum
    by_cases hm : 2 ∈ n.primeFactors
    · have he := Nat.prime_two.factorization_pos_of_dvd hpos.ne' (Nat.dvd_of_mem_primeFactors hm)
      rw [if_neg he.ne']
      exact (Finset.mul_prod_erase n.primeFactors (fun p => 1 + comp p) hm).trans hsum
    · have h0 : n.factorization 2 = 0 := Finsupp.notMem_support_iff.mp (by
        rwa [Nat.support_factorization])
      simpa [h0, P, Finset.erase_eq_of_notMem hm, comp] using hsum

theorem small_two_exponent {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (ha : n.factorization 2 < 5) : n = 6 ∨ n = 60 ∨ n = 90 := by
  let a := n.factorization 2
  let t := if a = 0 then 1 else 1 + 2 ^ a
  obtain ⟨Q, hodd, h39, hself, hsum⟩ := odd_component_data hn
  let A : Finset ℕ := {3, 5, 7, 9, 11}
  let L := Q ∩ A
  let H := Q \ A
  let j := H.card
  let l := ∏ q ∈ L, (1 + q)
  let b := 2 ^ a * ∏ q ∈ L, q
  let u := t * l
  let d := ∏ q ∈ H, q
  let h := ∏ q ∈ H, (1 + q)
  have h13 : ∀ q ∈ H, 13 ≤ q := by
    intro q hq
    obtain ⟨hqQ, hqA⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨⟨i, hi⟩, h3⟩ := hodd q hqQ
    simp [A] at hqA
    omega
  have ht0 : 0 < t := by
    dsimp [t]
    split <;> positivity
  have hl0 : 0 < l := Finset.prod_pos fun _ _ => by omega
  have hu0 : 0 < u := Nat.mul_pos ht0 hl0
  have hd0 : 0 < d := Finset.prod_pos fun q hq => by have := h13 q hq; omega
  have hprod : n = b * d := by
    calc n = 2 ^ a * (∏ q ∈ Q, q) := hself
      _ = 2 ^ a * ((∏ q ∈ L, q) * d) :=
        congrArg (fun x => 2 ^ a * x) (Finset.prod_inter_mul_prod_sdiff Q A _).symm
      _ = b * d := (Nat.mul_assoc _ _ _).symm
  have hsum' : u * h = 2 * n := by
    calc u * h = t * (l * h) := Nat.mul_assoc _ _ _
      _ = t * ∏ q ∈ Q, (1 + q) :=
        congrArg (fun x => t * x) (Finset.prod_inter_mul_prod_sdiff Q A _)
      _ = 2 * n := hsum
  have hbal : u * h = (2 * b) * d :=
    hsum'.trans ((congrArg (fun x => 2 * x) hprod).trans (Nat.mul_assoc _ _ _).symm)
  have htwo : 2 ^ j ∣ h := by
    change 2 ^ H.card ∣ ∏ q ∈ H, (1 + q)
    rw [← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun q hq => ?_
    rw [add_comm, ← even_iff_two_dvd]
    exact (hodd q (Finset.mem_sdiff.mp hq).1).1.add_one
  have hbgt : j + l.factorization 2 ≤ a + 1 := by
    have hdvd : (2 ^ j) * l ∣ 2 * n := by
      rw [← hsum']
      have h1 : 2 ^ j * l ∣ h * l := Nat.mul_dvd_mul_right htwo l
      have h2 : h * l ∣ u * h := by
        change h * l ∣ t * l * h
        rw [mul_comm h l, mul_assoc]
        exact dvd_mul_left _ _
      exact h1.trans h2
    have hh := (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero (by positivity) hl0.ne')
      (Nat.mul_ne_zero (by decide) hn.2.ne')).mpr hdvd 2
    rw [Nat.factorization_mul (by positivity) hl0.ne', Nat.factorization_mul (by decide) hn.2.ne',
      Finsupp.add_apply, Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.prime_two.factorization_self] at hh
    change j + l.factorization 2 ≤ n.factorization 2 + 1
    omega
  have hcase : if j = 0 then u = 2 * b else u < 2 * b ∧ 2 * b * 13 ^ j ≤ u * 14 ^ j := by
    split_ifs with hj
    · have hempty := Finset.card_eq_zero.mp (show H.card = 0 from hj)
      simpa [h, d, hempty] using hbal
    · have hne : H.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hj)
      have hlt : d < h := Finset.prod_lt_prod_of_nonempty
        (fun q hq => by have := h13 q hq; omega) (fun q _ => by omega) hne
      have hstrict := Nat.mul_lt_mul_of_pos_left hlt hu0
      rw [hbal] at hstrict
      refine ⟨Nat.lt_of_mul_lt_mul_right hstrict, Nat.le_of_mul_le_mul_right ?_ hd0⟩
      have hratio : 13 ^ j * h ≤ 14 ^ j * d := by
        have hh : (∏ q ∈ H, 13 * (1 + q)) ≤ ∏ q ∈ H, 14 * q :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun q hq => by have := h13 q hq; omega)
        rw [Finset.prod_mul_distrib (s := H) (f := fun _ => 13) (g := fun q : ℕ => 1 + q),
          Finset.prod_mul_distrib (s := H) (f := fun _ => 14) (g := fun q : ℕ => q)] at hh
        simpa only [Finset.prod_const] using hh
      calc (2 * b * 13 ^ j) * d = ((2 * b) * d) * 13 ^ j := by ac_rfl
        _ = (u * h) * 13 ^ j := by rw [hbal]
        _ = u * (13 ^ j * h) := by ac_rfl
        _ ≤ u * (14 ^ j * d) := Nat.mul_le_mul_left _ hratio
        _ = (u * 14 ^ j) * d := (Nat.mul_assoc _ _ _).symm
  have hja : j < 6 := by change n.factorization 2 < 5 at ha; dsimp [a] at hbgt; omega
  have hcert := small_exponent_certificate a (Finset.mem_range.mpr ha) L
    (Finset.mem_powerset.mpr Finset.inter_subset_right) j (Finset.mem_range.mpr hja)
    (fun hbad => h39 ⟨(Finset.mem_inter.mp hbad.1).1, (Finset.mem_inter.mp hbad.2).1⟩) hbgt hcase
  have hempty := Finset.card_eq_zero.mp (show H.card = 0 from hcert.1)
  have hnb : n = b := by simpa [d, hempty] using hprod
  exact hnb ▸ hcert.2

-- This classification has no upper bound on the integer n.
theorem classification_few_simple_primes {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hfew : (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card ≤ 3) :
    n = 6 ∨ n = 60 ∨ n = 90 := by
  apply small_two_exponent hn
  by_contra! hlarge
  have := many_simple_primes hn hlarge
  omega

-- Decompose a solution, retain the coprimality constraints, and certify the
-- finite search interval for every prime occurring to the first power.
theorem decompose {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) :
    let c := ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1),
      p ^ n.factorization p
    let b := 2 ^ n.factorization 2 * c
    let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
    Odd c ∧ (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) ∧
      ∃ S : Finset ℕ, S ⊆ Finset.Icc 3 u ∧ (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
        u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) ∧
        n = b * (∏ p ∈ S, p) ∧ (5 ≤ n.factorization 2 → 4 ≤ S.card) := by
  let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
  let V := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  let T := n.primeFactors \ S
  let c := ∏ p ∈ V, p ^ n.factorization p
  let b := 2 ^ n.factorization 2 * c
  let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
  change Odd c ∧ _ ∧ ∃ S : Finset ℕ, S ⊆ Finset.Icc 3 u ∧ _ ∧ _ ∧ _
  have hS : S ⊆ n.primeFactors := Finset.filter_subset _ _
  have hV : V ⊆ n.primeFactors := Finset.filter_subset _ _
  have hT : T ⊆ n.primeFactors := Finset.sdiff_subset
  have hVT : T.erase 2 = V := by
    ext p
    simp [T, S, V]
    tauto
  have hb : b = ∏ p ∈ T, p ^ n.factorization p := by
    by_cases h2 : 2 ∈ T
    · rw [← Finset.mul_prod_erase T (fun p => p ^ n.factorization p) h2, hVT]
    · have h2n : 2 ∉ n.primeFactors := by simpa [T, S] using h2
      have he : n.factorization 2 = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rwa [Nat.support_factorization]
      have ht : T = V := by simpa [Finset.erase_eq_of_notMem h2] using hVT
      simp [b, he, ht, c]
  have hbp : b.primeFactors = T := by rw [hb, primeFactors_ppart hT]
  have hcp : c.primeFactors = V := primeFactors_ppart hV
  have hb0 : b ≠ 0 := hb ▸ ppart_ne_zero hT
  have hodd : Odd c := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hd
    have hmem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, ppart_ne_zero hV⟩
    rw [hcp] at hmem
    exact (Finset.mem_filter.mp hmem).2.1 rfl
  have hpower : ∀ p ∈ c.primeFactors, 2 ≤ c.factorization p := by
    intro p hp
    rw [hcp] at hp
    have hm := Finset.mem_filter.mp hp
    have he := (Nat.prime_of_mem_primeFactors (hV hp)).factorization_pos_of_dvd
      hn.2.ne' (Nat.dvd_of_mem_primeFactors (hV hp))
    change 2 ≤ (∏ q ∈ V, q ^ n.factorization q).factorization p
    rw [factorization_ppart hV, if_pos hp]
    omega
  have hsprops : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors (hS hp), (Finset.mem_filter.mp hp).2.1⟩
  have hcop : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ b := by
    intro p hp
    refine ⟨(hsprops p hp).1, fun hd => ?_⟩
    have hm := Nat.mem_primeFactors.mpr ⟨(hsprops p hp).1, hd, hb0⟩
    rw [hbp] at hm
    exact (Finset.mem_sdiff.mp hm).2 hp
  have hsplit : n = b * ∏ p ∈ S, p := by
    calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        (prod_primeFactors_pow_self hn.2.ne').symm
      _ = b * ∏ p ∈ S, p ^ n.factorization p := by rw [hb, Finset.prod_sdiff hS]
      _ = b * ∏ p ∈ S, p := by
        congr 1
        exact Finset.prod_congr rfl fun p hp => by
          rw [(Finset.mem_filter.mp hp).2.2, pow_one]
  have hu : u = ∏ p ∈ T, (1 + p ^ n.factorization p) := by
    change (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) = _
    rw [hbp]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hb, factorization_ppart hT, if_pos hp]
  have hbal : u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p := by
    obtain ⟨hpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
    rw [sum_udiv_eq_prod hpos.ne', ← Finset.prod_sdiff hS] at hsum
    have hsprod : (∏ p ∈ S, (1 + p ^ n.factorization p)) = ∏ p ∈ S, (1 + p) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2.2, pow_one]
    rw [hsprod] at hsum
    calc u * (∏ p ∈ S, (1 + p)) = 2 * n := by rwa [hu]
      _ = 2 * (b * ∏ p ∈ S, p) := congrArg (fun t => 2 * t) hsplit
      _ = (2 * b) * ∏ p ∈ S, p := (Nat.mul_assoc _ _ _).symm
  have hu0 : 0 < u := Finset.prod_pos fun _ _ => by omega
  exact ⟨hodd, hpower, S, support_bound hu0 hsprops hbal, hcop, hbal, hsplit,
    fun ha => many_simple_primes hn ha⟩

-- Unconditional lemmas for H1 and H2.
namespace CoreBounds

theorem squarefree_product_valuation (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (p : ℕ) :
    (∏ q ∈ S, q).factorization p = if p ∈ S then 1 else 0 := by
  rw [Nat.factorization_prod (fun q hq => (hS q hq).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun q hq => by rw [(hS q hq).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S p _

theorem square_obstruction {p v : ℕ} {S : Finset ℕ} (hp : p.Prime)
    (hv : v ≠ 0) (hpv : ¬ p ∣ v) (hS : ∀ q ∈ S, q.Prime) :
    ¬ p ^ 2 ∣ v * ∏ q ∈ S, q := by
  have hprod := Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero)
  intro hd
  have h := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) (mul_ne_zero hv hprod)).2 hd p
  rw [hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_mul hv hprod,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpv, zero_add,
    squarefree_product_valuation S hS] at h
  split at h <;> omega

theorem forced_member {p u v : ℕ} {S : Finset ℕ} (hp : p.Prime) (hpv : ¬ p ∣ v)
    (hS : ∀ q ∈ S, q.Prime) (hbal : u * (∏ q ∈ S, (1 + q)) = v * ∏ q ∈ S, q)
    (hd : p ∣ u * ∏ q ∈ S, (1 + q)) : p ∈ S := by
  rw [hbal] at hd
  obtain ⟨q, hq, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp
    ((hp.dvd_mul.mp hd).resolve_left hpv)
  simpa only [((hS q hq).dvd_iff_eq hp.ne_one).mp hdiv] using hq

theorem sigma_factor {b p : ℕ} (hp : p ∈ b.primeFactors) :
    1 + p ^ b.factorization p ∣ (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) :=
  Finset.dvd_prod_of_mem (fun q => 1 + q ^ b.factorization q) hp

theorem obstruction_from_core_factor {a c p r : ℕ}
    (hc : c ≠ 0) (hr : r.Prime) (hr2 : ¬ r ∣ 2) (hrc : ¬ r ∣ c)
    (hp : p ∈ c.primeFactors) (hp2 : p ≠ 2) (hd : r ^ 2 ∣ 1 + p ^ c.factorization p) :
    let b := 2 ^ a * c
    ¬ ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) * (∏ q ∈ S, (1 + q)) =
        (2 * b) * ∏ q ∈ S, q := by
  let b := 2 ^ a * c
  have htwo : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hb : b ≠ 0 := mul_ne_zero htwo hc
  have hrv : ¬ r ∣ 2 * b := by
    simpa [b, hr.dvd_mul, hrc, hr2] using
      (show ¬ r ∣ 2 ^ a from fun h => hr2 (hr.dvd_of_dvd_pow h))
  have hpb := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp, dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) _, hb⟩
  have he : b.factorization p = c.factorization p := by
    simp [b, Nat.factorization_mul htwo hc, Nat.prime_two.factorization_pow, Ne.symm hp2]
  dsimp only
  rintro ⟨S, hS, hbal⟩
  apply square_obstruction hr (mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hb) hrv hS
  rw [← hbal]
  apply dvd_mul_of_dvd_left _ _
  apply dvd_trans hd
  simpa only [← he] using sigma_factor hpb

theorem nine_dvd_five_power (k : ℕ) : 9 ∣ 1 + 5 ^ (6 * k + 3) := by
  have ho : Odd (2 * k + 1) := ⟨k, rfl⟩
  have h := ho.nat_add_dvd_pow_add_pow (5 ^ 3) 1
  rw [one_pow, ← pow_mul, show 3 * (2 * k + 1) = 6 * k + 3 by omega] at h
  rw [Nat.add_comm]
  exact dvd_trans (by decide : 9 ∣ 5 ^ 3 + 1) h

theorem excludes_five_component {a c k : ℕ} (hc : c ≠ 0) (h3 : ¬ 3 ∣ c)
    (h5 : 5 ∈ c.primeFactors) (he : c.factorization 5 = 6 * k + 3) : let b := 2 ^ a * c
    ¬ ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) * (∏ q ∈ S, (1 + q)) =
        (2 * b) * ∏ q ∈ S, q := by
  apply obstruction_from_core_factor hc Nat.prime_three (by decide) h3 h5 (by decide)
  rw [he]
  exact nine_dvd_five_power k

theorem excludes_five_power (a k : ℕ) : let b := 2 ^ a * (5 ^ (6 * k + 3))
    ¬ ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) * (∏ q ∈ S, (1 + q)) =
        (2 * b) * ∏ q ∈ S, q := by
  have hp : Nat.Prime 5 := by decide
  have h3 : ¬ 3 ∣ 5 ^ (6 * k + 3) := fun h =>
    (by decide : ¬ 3 ∣ 5) (Nat.prime_three.dvd_of_dvd_pow h)
  have hm : 5 ∈ (5 ^ (6 * k + 3)).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, dvd_pow_self _ (by omega), pow_ne_zero _ hp.ne_zero⟩
  apply excludes_five_component (pow_ne_zero _ hp.ne_zero) h3 hm (k := k)
  simp [hp.factorization_pow]

theorem excluded_cores_of_perfect {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (k : ℕ) :
    (∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1), p ^ n.factorization p) ≠
      5 ^ (6 * k + 3) := by
  intro he
  obtain ⟨_, _, S, _, hS, hbal, _, _⟩ := decompose hn
  have bad := excludes_five_power (n.factorization 2) k
  rw [← he] at bad
  exact bad ⟨S, fun q hq => (hS q hq).1, hbal⟩

set_option maxRecDepth 4096 in
theorem forced_primes_at_625 {a : ℕ} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hbal : (∏ q ∈ (2 ^ a * 625).primeFactors, (1 + q ^ (2 ^ a * 625).factorization q)) * (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * 625)) * ∏ q ∈ S, q) :
    313 ∈ S ∧ 157 ∈ S ∧ 79 ∈ S := by
  let b := 2 ^ a * 625
  have htwo : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hb : b ≠ 0 := mul_ne_zero htwo (by decide)
  have h5 : 5 ∈ b.primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide, dvd_mul_of_dvd_right (by decide : 5 ∣ 625) _, hb⟩
  have he : b.factorization 5 = 4 := by
    rw [show b = 2 ^ a * 5 ^ 4 by rfl,
      Nat.factorization_mul htwo (by decide), Nat.prime_two.factorization_pow,
      (by decide : Nat.Prime 5).factorization_pow]
    simp
  have hv (p : ℕ) (hp : p.Prime) (h2p : ¬ p ∣ 2) (h5p : ¬ p ∣ 625) : ¬ p ∣ 2 * b := by
    simpa [b, hp.dvd_mul, h2p, h5p] using
      (show ¬ p ∣ 2 ^ a from fun h => h2p (hp.dvd_of_dvd_pow h))
  have h313 : 313 ∈ S := forced_member (by decide : Nat.Prime 313)
    (hv 313 (by decide) (by decide) (by decide)) hS hbal
    (dvd_mul_of_dvd_left (dvd_trans (by decide : 313 ∣ 1 + 5 ^ 4) (he ▸ sigma_factor h5)) _)
  have step {q p : ℕ} (hq : q ∈ S) (hp : p.Prime) (h2p : ¬ p ∣ 2) (h5p : ¬ p ∣ 625)
      (hd : p ∣ 1 + q) : p ∈ S :=
    forced_member hp (hv _ hp h2p h5p) hS hbal
      (dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem (fun r : ℕ => 1 + r) hq)) _)
  have h157 := step h313 (by decide : Nat.Prime 157) (by decide) (by decide) (by decide)
  exact ⟨h313, h157, step h157 (by decide) (by decide) (by decide) (by decide)⟩

theorem excludes_625_four_mod_eight (k : ℕ) : let b := 2 ^ (8 * k + 4) * 625
    ¬ ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) * (∏ q ∈ S, (1 + q)) =
        (2 * b) * ∏ q ∈ S, q := by
  let a := 8 * k + 4
  let b := 2 ^ a * 625
  have htwo : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hb : b ≠ 0 := mul_ne_zero htwo (by decide)
  have h2 : 2 ∈ b.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, dvd_mul_of_dvd_left (dvd_pow_self _ (show a ≠ 0 by dsimp [a]; omega)) _, hb⟩
  have he : b.factorization 2 = a := by
    simp [b, Nat.factorization_mul htwo (by decide : (625 : ℕ) ≠ 0),
      Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 625)]
  have ho : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hd := ho.nat_add_dvd_pow_add_pow (2 ^ 4) 1
  rw [one_pow, ← pow_mul, show 4 * (2 * k + 1) = a by dsimp [a]; omega, Nat.add_comm (2 ^ a) 1] at hd
  have hsigma : 17 ∣ (∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)) := dvd_trans hd (he ▸ sigma_factor h2)
  have hv (p : ℕ) (hp : p.Prime) (h2p : ¬ p ∣ 2) (h5p : ¬ p ∣ 625) : ¬ p ∣ 2 * b := by
    simpa [b, hp.dvd_mul, h2p, h5p] using
      (show ¬ p ∣ 2 ^ a from fun h => h2p (hp.dvd_of_dvd_pow h))
  dsimp only
  rintro ⟨S, hS, hbal⟩
  have h17 : 17 ∈ S := forced_member (by decide : Nat.Prime 17)
    (hv 17 (by decide) (by decide) (by decide)) hS hbal (dvd_mul_of_dvd_left hsigma _)
  have h18 := Finset.dvd_prod_of_mem (fun q : ℕ => 1 + q) h17
  apply square_obstruction Nat.prime_three (mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hb)
    (hv 3 Nat.prime_three (by decide) (by decide)) hS
  rw [← hbal]
  exact dvd_mul_of_dvd_right (dvd_trans (by decide : 3 ^ 2 ∣ 1 + 17) h18) _

theorem oddPart_prod (S : Finset ℕ) (f : ℕ → ℕ) :
    ordCompl[2] (∏ q ∈ S, f q) = ∏ q ∈ S, ordCompl[2] (f q) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, ← ih]
    exact Nat.ordCompl_mul _ _ 2

theorem compatible_from_balance {u c a : ℕ} {S : Finset ℕ}
    (hbal : u * (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * c)) * ∏ q ∈ S, q) :
    ordCompl[2] u * (∏ q ∈ S, ordCompl[2] (1 + q)) ∣ c * ∏ q ∈ S, q := by
  have hb : 2 * (2 ^ a * c) * (∏ q ∈ S, q) = 2 ^ (a + 1) * (c * ∏ q ∈ S, q) := by
    rw [pow_succ]
    ac_rfl
  have h := congrArg (fun n : ℕ => ordCompl[2] n) (hbal.trans hb)
  change ordCompl[2] (u * (∏ q ∈ S, (1 + q))) = ordCompl[2] (2 ^ (a + 1) * (c * ∏ q ∈ S, q)) at h
  rw [Nat.ordCompl_mul, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two] at h
  rw [← oddPart_prod]
  exact dvd_trans (dvd_of_eq h) (Nat.ordCompl_dvd _ _)

theorem twice_oddPart_shift_le {q : ℕ} (hq : Odd q) : 2 * ordCompl[2] (1 + q) ≤ q + 1 := by
  have h2 : 2 ∣ 1 + q := by
    rw [Nat.add_comm, ← even_iff_two_dvd]
    exact hq.add_one
  obtain ⟨r, hr⟩ := h2
  have hpart : ordCompl[2] (1 + q) = ordCompl[2] r := by
    rw [hr, show 2 * r = 2 ^ 1 * r by simp]
    exact Nat.ordCompl_self_pow_mul _ _ Nat.prime_two
  have hle := Nat.le_of_dvd (by omega : 0 < r) (Nat.ordCompl_dvd r 2)
  rw [hpart]
  omega

theorem compatible_tail_bound {x D : ℕ} (S : Finset ℕ) (d : ℕ → ℕ) (hx : 1 ≤ x)
    (hD : D ≠ 0) (hS : ∀ q ∈ S, q.Prime ∧ x < q ∧ 0 < d q ∧ 2 * d q ≤ q + 1)
    (hdvd : (∏ q ∈ S, d q) ∣ D * ∏ q ∈ S, q) :
    (∏ q ∈ S, (1 + 1 / (q : ℚ))) ≤
      (1 + 2 / (x : ℚ)) ^ D.primeFactorsList.length *
        ∏ q ∈ S, (if d q = 1 then ((q : ℚ) + 1) / ((q : ℚ) - 1) else 1) := by
  let weight (x p : ℕ) : ℚ :=
    if p ≤ x then 1 + 2 / (x : ℚ) else (p : ℚ) / (p - 1 : ℚ)

  let weightProd (x n : ℕ) : ℚ := (n.primeFactorsList.map (weight x)).prod

  have weight_bounds {x : ℕ} (hx : 1 ≤ x) (p : ℕ) :
      1 ≤ weight x p ∧ weight x p ≤ 1 + 2 / (x : ℚ) := by
    have hx' : (0 : ℚ) < x := by exact_mod_cast (show 0 < x by omega)
    by_cases hp : p ≤ x
    · simp only [weight, if_pos hp]
      constructor <;> linarith [show 0 ≤ 2 / (x : ℚ) by positivity]
    · simp only [weight, if_neg hp]
      have hpx : (x : ℚ) + 1 ≤ p := by exact_mod_cast (show x + 1 ≤ p by omega)
      have hden : (0 : ℚ) < p - 1 := by linarith
      constructor
      · apply (le_div_iff₀ hden).2
        linarith
      · rw [div_le_iff₀ hden]
        field_simp
        nlinarith

  have weightProd_bounds {x : ℕ} (hx : 1 ≤ x) (n : ℕ) :
      1 ≤ weightProd x n ∧ weightProd x n ≤ (1 + 2 / (x : ℚ)) ^ n.primeFactorsList.length := by
    unfold weightProd
    induction n.primeFactorsList with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      obtain ⟨h1, h2⟩ := weight_bounds hx p
      constructor
      · simpa using mul_le_mul h1 ih.1 (by norm_num : (0 : ℚ) ≤ 1) (by linarith)
      · rw [mul_comm (weight x p)]
        exact mul_le_mul ih.2 h2 (by linarith) (by positivity)

  have weightProd_prime (x : ℕ) {p : ℕ} (hp : p.Prime) : weightProd x p = weight x p := by
    simp [weightProd, Nat.primeFactorsList_prime hp]

  have weightProd_mul (x : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
      weightProd x (a*b) = weightProd x a * weightProd x b := by
    simpa [weightProd] using ((Nat.perm_primeFactorsList_mul ha hb).map (weight x)).prod_eq

  have weightProd_dvd {x a b : ℕ} (hx : 1 ≤ x) (hb : b ≠ 0) (hd : a ∣ b) :
      weightProd x a ≤ weightProd x b := by
    obtain ⟨k, rfl⟩ := hd
    obtain ⟨ha, hk⟩ := mul_ne_zero_iff.mp hb
    rw [weightProd_mul x ha hk]
    have h1 := (weightProd_bounds hx a).1
    have h2 := (weightProd_bounds hx k).1
    simpa using mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ weightProd x a)

  have weightProd_finset (x : ℕ) (S : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ q ∈ S, f q ≠ 0) :
      weightProd x (∏ q ∈ S, f q) = ∏ q ∈ S, weightProd x (f q) := by
    induction S using Finset.induction_on with
    | empty => simp [weightProd]
    | @insert p S hp ih =>
      have hS (q : ℕ) (hq : q ∈ S) := hf q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp, Finset.prod_insert hp,
        weightProd_mul x (hf _ (Finset.mem_insert_self p S)) (Finset.prod_ne_zero_iff.mpr hS),
        ih hS]

  let pathBound (q : ℕ) : ℚ := ((q : ℚ) + 1) / ((q : ℚ) - 1)

  have local_weight {x q d : ℕ} (hx : 1 ≤ x) (hq : q.Prime) (hxq : x < q)
      (hd : 0 < d) (hsize : 2*d ≤ q+1) :
      (1 + 1 / (q : ℚ)) * weightProd x q ≤
        weightProd x d * (if d = 1 then pathBound q else 1) := by
    rw [weightProd_prime x hq]
    simp only [weight, if_neg (by omega : ¬ q ≤ x)]
    have hx' : (0 : ℚ) < x := by exact_mod_cast (show 0 < x by omega)
    have hq' : (1 : ℚ) < q := by exact_mod_cast hq.one_lt
    have hqx : (x : ℚ) + 1 ≤ q := by exact_mod_cast (show x+1 ≤ q by omega)
    have hid : (1 + 1 / (q : ℚ)) * ((q : ℚ) / (q - 1 : ℚ)) = pathBound q := by
      unfold pathBound
      field_simp
    rw [hid]
    by_cases hroot : d = 1
    · subst d
      simp [weightProd]
    · rw [if_neg hroot, mul_one]
      let p := d.minFac
      have hp : p.Prime := Nat.minFac_prime hroot
      have hpd : p ∣ d := Nat.minFac_dvd d
      have hpd' := Nat.le_of_dvd hd hpd
      have htwop : 2 * (p : ℚ) ≤ q + 1 := by exact_mod_cast (show 2*p ≤ q+1 by omega)
      have hp' : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
      have hw := weightProd_dvd hx hd.ne' hpd
      rw [weightProd_prime x hp] at hw
      apply le_trans _ hw
      unfold pathBound weight
      split_ifs with hpx
      · apply (div_le_iff₀ (by linarith)).2
        field_simp
        nlinarith
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
  let U := ∏ q ∈ S, weightProd x q
  let M := ∏ q ∈ S, (if d q = 1 then pathBound q else 1)
  have hpos : 0 < U := Finset.prod_pos fun q _ => lt_of_lt_of_le zero_lt_one (weightProd_bounds hx q).1
  have hM : 0 ≤ M := by
    apply Finset.prod_nonneg
    intro q hq
    have hmin : (1 : ℚ) < q := by exact_mod_cast (hS q hq).1.one_lt
    split_ifs
    · unfold pathBound
      positivity
    · norm_num
  have hlocal := Finset.prod_le_prod (s := S)
    (f := fun q : ℕ => (1 + 1 / (q : ℚ)) * weightProd x q)
    (g := fun q : ℕ => weightProd x (d q) * (if d q = 1 then pathBound q else 1))
    (fun q _ => mul_nonneg (by positivity) (le_trans zero_le_one (weightProd_bounds hx q).1))
    (fun q hq => local_weight hx (hS q hq).1 (hS q hq).2.1 (hS q hq).2.2.1 (hS q hq).2.2.2)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hlocal
  have hq0 (q : ℕ) (hq : q ∈ S) := (hS q hq).1.ne_zero
  have hprod0 := Finset.prod_ne_zero_iff.mpr hq0
  have hg := weightProd_dvd hx (mul_ne_zero hD hprod0) hdvd
  rw [weightProd_mul x hD hprod0, weightProd_finset x S d (fun q hq => (hS q hq).2.2.1.ne'),
    weightProd_finset x S (fun q => q) hq0] at hg
  apply (le_of_mul_le_mul_right (a := U) _ hpos)
  calc (∏ q ∈ S, (1 + 1 / (q : ℚ))) * U ≤ (∏ q ∈ S, weightProd x (d q)) * M := hlocal
    _ ≤ (weightProd x D * U) * M := mul_le_mul_of_nonneg_right hg hM
    _ = (weightProd x D * M) * U := by ring
    _ ≤ ((1 + 2 / (x : ℚ)) ^ D.primeFactorsList.length * M) * U :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (weightProd_bounds hx D).2 hM) hpos.le

end CoreBounds

theorem main : H1 → H2 → type_of% @Erdos1052.erdos_1052 := by
  intro h1 h2
  obtain ⟨B, hB⟩ := h1
  let cores := {c : ℕ | c ≤ B ∧ Odd c ∧ ∀ p ∈ c.primeFactors, 2 ≤ c.factorization p}
  have hcores : cores.Finite := (Set.finite_Iic B).subset fun _ h => h.1
  let completions := fun (b : ℕ) =>
    let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
    {n : ℕ | ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≠ 2) ∧
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) ∧ n = b * ∏ p ∈ S, p}
  have hfinite : ∀ b, (completions b).Finite := by
    intro b
    apply Set.Subsingleton.finite
    rintro x ⟨S, hs, hbS, rfl⟩ y ⟨T, ht, hbT, rfl⟩
    have hu : 0 < ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q) :=
      Finset.prod_pos fun _ _ => by omega
    rw [unique_squarefree_completion hu.ne' hs ht hbS hbT]
  refine ((hcores.biUnion fun c hc => (h2 c hc.2.1 hc.2.2).biUnion
    fun a _ => hfinite (2 ^ a * c)).union
    (((Set.finite_singleton 90).insert 60).insert 6)).subset ?_
  intro n hn
  by_cases ha : n.factorization 2 < 5
  · exact Or.inr (small_two_exponent hn ha)
  · have hlarge := Nat.le_of_not_gt ha
    let c := ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1),
      p ^ n.factorization p
    obtain ⟨ho, hp, S, hS, hc, he, hnS, hfour⟩ := decompose hn
    refine Or.inl (Set.mem_biUnion (x := c) ⟨hB n hn (many_simple_primes hn hlarge), ho, hp⟩
      (Set.mem_biUnion (x := n.factorization 2) ⟨hlarge, S, hfour hlarge, hS, hc, he⟩
        ⟨S, fun p hp => ⟨(hc p hp).1, by
          have h3 := (Finset.mem_Icc.mp (hS hp)).1
          omega⟩, he, hnS⟩))

end OMA.R_Erdos1052_erdos_1052_R2
