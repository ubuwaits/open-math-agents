import OMAReductions.R_Erdos1052_erdos_1052_R2

/-!
# Prime-doubled exponents at odd repeated core 625 in Erdős problem 1052

For a unitary perfect integer n with odd repeated core 625, its two-adic exponent
cannot equal twice any prime. More generally it cannot equal twice an odd integer
at least 25. Both exclusions also apply directly to the arithmetic test of R2.H2.
The four required rational gaps have finite certificates covering arbitrarily large primes.
The final theorems are in the namespace Erdos1052.Core625.

The import is the accepted R2 in project pull request 5438, revision
365e7419f6fa7a2c184f5bef0d6b96104b4c2f63.
-/

/- Unconditional obstructions to the two parameter tests in reduction R2. -/

namespace Erdos1052.CoreBounds

abbrev sigmaU (b : ℕ) := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)

def Admits (c a : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
    sigmaU (2 ^ a * c) * (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * c)) * ∏ q ∈ S, q

abbrev core (n : ℕ) :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1), p ^ n.factorization p

theorem admits_of_perfect {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) :
    Admits (core n) (n.factorization 2) := by
  obtain ⟨_, _, S, _, hS, hbal, _, _⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  exact ⟨S, fun q hq => (hS q hq).1, hbal⟩

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
    1 + p ^ b.factorization p ∣ sigmaU b :=
  Finset.dvd_prod_of_mem (fun q => 1 + q ^ b.factorization q) hp

theorem obstruction_from_core_factor {a c p r : ℕ}
    (hc : c ≠ 0) (hr : r.Prime) (hr2 : ¬ r ∣ 2) (hrc : ¬ r ∣ c)
    (hp : p ∈ c.primeFactors) (hp2 : p ≠ 2) (hd : r ^ 2 ∣ 1 + p ^ c.factorization p) :
    ¬ Admits c a := by
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
    (h5 : 5 ∈ c.primeFactors) (he : c.factorization 5 = 6 * k + 3) : ¬ Admits c a := by
  apply obstruction_from_core_factor hc Nat.prime_three (by decide) h3 h5 (by decide)
  rw [he]
  exact nine_dvd_five_power k

theorem excludes_five_power (a k : ℕ) : ¬ Admits (5 ^ (6 * k + 3)) a := by
  have hp : Nat.Prime 5 := by decide
  have h3 : ¬ 3 ∣ 5 ^ (6 * k + 3) := fun h =>
    (by decide : ¬ 3 ∣ 5) (Nat.prime_three.dvd_of_dvd_pow h)
  have hm : 5 ∈ (5 ^ (6 * k + 3)).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, dvd_pow_self _ (by omega), pow_ne_zero _ hp.ne_zero⟩
  apply excludes_five_component (pow_ne_zero _ hp.ne_zero) h3 hm (k := k)
  simp [hp.factorization_pow]

theorem excluded_cores_of_perfect {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (k : ℕ) :
    core n ≠ 5 ^ (6 * k + 3) := by
  intro he
  have h := admits_of_perfect hn
  rw [he] at h
  exact excludes_five_power _ _ h

theorem five_power_exponents_empty (k : ℕ) :
    {a : ℕ | Admits (5 ^ (6 * k + 3)) a} = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun a => excludes_five_power a k

set_option maxRecDepth 4096 in
theorem forced_primes_at_625 {a : ℕ} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hbal : sigmaU (2 ^ a * 625) * (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * 625)) * ∏ q ∈ S, q) :
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

theorem excludes_625_four_mod_eight (k : ℕ) : ¬ Admits 625 (8 * k + 4) := by
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
  have hsigma : 17 ∣ sigmaU b := dvd_trans hd (he ▸ sigma_factor h2)
  have hv (p : ℕ) (hp : p.Prime) (h2p : ¬ p ∣ 2) (h5p : ¬ p ∣ 625) : ¬ p ∣ 2 * b := by
    simpa [b, hp.dvd_mul, h2p, h5p] using
      (show ¬ p ∣ 2 ^ a from fun h => h2p (hp.dvd_of_dvd_pow h))
  rintro ⟨S, hS, hbal⟩
  have h17 : 17 ∈ S := forced_member (by decide : Nat.Prime 17)
    (hv 17 (by decide) (by decide) (by decide)) hS hbal (dvd_mul_of_dvd_left hsigma _)
  have h18 := Finset.dvd_prod_of_mem (fun q : ℕ => 1 + q) h17
  apply square_obstruction Nat.prime_three (mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hb)
    (hv 3 Nat.prime_three (by decide) (by decide)) hS
  rw [← hbal]
  exact dvd_mul_of_dvd_right (dvd_trans (by decide : 3 ^ 2 ∣ 1 + 17) h18) _

-- A multiplicative weight bounds the entire contribution of primes above x.
-- For an odd prime q in the completion, d q is the odd part of q+1.
def weight (x p : ℕ) : ℚ :=
  if p ≤ x then 1 + 2 / (x : ℚ) else (p : ℚ) / (p - 1 : ℚ)

def weightProd (x n : ℕ) : ℚ := (n.primeFactorsList.map (weight x)).prod

theorem weight_bounds {x : ℕ} (hx : 1 ≤ x) (p : ℕ) :
    1 ≤ weight x p ∧ weight x p ≤ 1 + 2 / (x : ℚ) := by
  have hx' : (0 : ℚ) < x := by exact_mod_cast (show 0 < x by omega)
  by_cases hp : p ≤ x
  · rw [weight, if_pos hp]
    constructor <;> linarith [show 0 ≤ 2 / (x : ℚ) by positivity]
  · rw [weight, if_neg hp]
    have hpx : (x : ℚ) + 1 ≤ p := by exact_mod_cast (show x + 1 ≤ p by omega)
    have hden : (0 : ℚ) < p - 1 := by linarith
    constructor
    · apply (le_div_iff₀ hden).2
      linarith
    · rw [div_le_iff₀ hden]
      field_simp
      nlinarith

theorem weightProd_bounds {x : ℕ} (hx : 1 ≤ x) (n : ℕ) :
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

theorem weightProd_prime (x : ℕ) {p : ℕ} (hp : p.Prime) : weightProd x p = weight x p := by
  simp [weightProd, Nat.primeFactorsList_prime hp]

theorem weightProd_mul (x : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    weightProd x (a*b) = weightProd x a * weightProd x b := by
  simpa [weightProd] using ((Nat.perm_primeFactorsList_mul ha hb).map (weight x)).prod_eq

theorem weightProd_dvd {x a b : ℕ} (hx : 1 ≤ x) (hb : b ≠ 0) (hd : a ∣ b) :
    weightProd x a ≤ weightProd x b := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨ha, hk⟩ := mul_ne_zero_iff.mp hb
  rw [weightProd_mul x ha hk]
  have h1 := (weightProd_bounds hx a).1
  have h2 := (weightProd_bounds hx k).1
  simpa using mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ weightProd x a)

theorem weightProd_finset (x : ℕ) (S : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ q ∈ S, f q ≠ 0) :
    weightProd x (∏ q ∈ S, f q) = ∏ q ∈ S, weightProd x (f q) := by
  induction S using Finset.induction_on with
  | empty => simp [weightProd]
  | @insert p S hp ih =>
    have hS (q : ℕ) (hq : q ∈ S) := hf q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      weightProd_mul x (hf _ (Finset.mem_insert_self p S)) (Finset.prod_ne_zero_iff.mpr hS),
      ih hS]

def pathBound (q : ℕ) : ℚ := ((q : ℚ) + 1) / ((q : ℚ) - 1)

abbrev oddPart (n : ℕ) := ordCompl[2] n

theorem oddPart_prod (S : Finset ℕ) (f : ℕ → ℕ) :
    oddPart (∏ q ∈ S, f q) = ∏ q ∈ S, oddPart (f q) := by
  induction S using Finset.induction_on with
  | empty => simp [oddPart]
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, ← ih]
    exact Nat.ordCompl_mul _ _ 2

theorem compatible_from_balance {u c a : ℕ} {S : Finset ℕ}
    (hbal : u * (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * c)) * ∏ q ∈ S, q) :
    oddPart u * (∏ q ∈ S, oddPart (1 + q)) ∣ c * ∏ q ∈ S, q := by
  have hb : 2 * (2 ^ a * c) * (∏ q ∈ S, q) = 2 ^ (a + 1) * (c * ∏ q ∈ S, q) := by
    rw [pow_succ]
    ac_rfl
  have h := congrArg oddPart (hbal.trans hb)
  change ordCompl[2] (u * (∏ q ∈ S, (1 + q))) = ordCompl[2] (2 ^ (a + 1) * (c * ∏ q ∈ S, q)) at h
  rw [Nat.ordCompl_mul, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two] at h
  rw [← oddPart_prod]
  exact dvd_trans (dvd_of_eq h) (Nat.ordCompl_dvd _ _)

theorem twice_oddPart_shift_le {q : ℕ} (hq : Odd q) : 2 * oddPart (1 + q) ≤ q + 1 := by
  have h2 : 2 ∣ 1 + q := by
    rw [Nat.add_comm, ← even_iff_two_dvd]
    exact hq.add_one
  obtain ⟨r, hr⟩ := h2
  have hpart : oddPart (1 + q) = oddPart r := by
    rw [hr, show 2 * r = 2 ^ 1 * r by simp]
    exact Nat.ordCompl_self_pow_mul _ _ Nat.prime_two
  have hle := Nat.le_of_dvd (by omega : 0 < r) (Nat.ordCompl_dvd r 2)
  rw [hpart]
  change r / _ ≤ r at hle
  dsimp [oddPart]
  omega

theorem local_weight {x q d : ℕ} (hx : 1 ≤ x) (hq : q.Prime) (hxq : x < q)
    (hd : 0 < d) (hsize : 2*d ≤ q+1) :
    (1 + 1 / (q : ℚ)) * weightProd x q ≤
      weightProd x d * (if d = 1 then pathBound q else 1) := by
  rw [weightProd_prime x hq, weight, if_neg (by omega : ¬ q ≤ x)]
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

theorem compatible_tail_bound {x D : ℕ} (S : Finset ℕ) (d : ℕ → ℕ) (hx : 1 ≤ x)
    (hD : D ≠ 0) (hS : ∀ q ∈ S, q.Prime ∧ x < q ∧ 0 < d q ∧ 2 * d q ≤ q + 1)
    (hdvd : (∏ q ∈ S, d q) ∣ D * ∏ q ∈ S, q) :
    (∏ q ∈ S, (1 + 1 / (q : ℚ))) ≤
      (1 + 2 / (x : ℚ)) ^ D.primeFactorsList.length *
        ∏ q ∈ S, (if d q = 1 then pathBound q else 1) := by
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

end Erdos1052.CoreBounds

/- Arithmetic and support decomposition for the core 625. -/

namespace Erdos1052.Core625

open Erdos1052.CoreBounds

def chain (k i : ℕ) := 1 + 2 ^ i * (2 ^ k - 1)

theorem chain_cast (k i m : ℕ) :
    (chain k i : ZMod m) = 1 + 2 ^ i * (2 ^ k - 1) := by
  have h : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by decide)
  simp [chain, Nat.cast_sub h]

theorem four_power_residue (t : ℕ) : (4^(t+1) : ℕ) % 12 = 4 := by
  induction t with
  | zero => decide
  | succ t ih => rw [pow_succ, Nat.mul_mod, ih]

theorem no_prime_chain {k : ℕ} (hk : 12 ≤ k) :
    ¬ ∀ i : ℕ, 1 ≤ i → i ≤ k+1 → (chain k i).Prime := by
  intro hall
  have hlarge (i : ℕ) (hi : 1 ≤ i) : 13 < chain k i := by
    have hx : 2 ^ 12 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) hk
    have hy : 2 ^ 1 ≤ (2:ℕ)^i := Nat.pow_le_pow_right (by decide) hi
    unfold chain
    norm_num at hx hy
    have ht : 13 < 2^k - 1 := by omega
    exact lt_trans ht (by nlinarith only [Nat.mul_le_mul_right (2 ^ k - 1) (show 1 ≤ 2^i by omega)])
  obtain ⟨m, d, hd, hkd⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
  let u := 2 ^ m
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by decide)
  change k = u * d at hkd
  by_cases hsingle : d = 1
  · have hpower : k = 2^m := by simpa [hsingle, u] using hkd
    have hm2 : 2 ≤ m := by
      by_contra! hh
      have := Nat.pow_le_pow_right (n := 2) (by decide) (show m ≤ 1 by omega)
      omega
    rcases Nat.even_or_odd m with hm | hm
    · obtain ⟨v, hv⟩ := hm
      have hv1 : 1 ≤ v := by omega
      obtain ⟨t, ht⟩ : ∃ t, v = t+1 := ⟨v-1, by omega⟩
      have hmod : k % 12 = 4 := by
        rw [hpower, show m = 2 * (t+1) by omega, pow_mul]
        exact four_power_residue t
      have hk12 : k = 12 * (k / 12) + 4 := by omega
      have hx : (2 : ZMod 13)^k = 3 := by
        conv_lhs => rw [hk12, pow_add, pow_mul]
        rw [show (2 : ZMod 13)^12 = 1 by decide, one_pow, one_mul]
        decide
      have hdiv : 13 ∣ chain k (k+1) := (ZMod.natCast_eq_zero_iff _ _).1 (by
        rw [chain_cast, pow_succ, hx]
        decide)
      have heq := ((hall _ (by omega) (by omega)).dvd_iff_eq (by decide : 13 ≠ 1)).1 hdiv
      have := hlarge (k+1) (by omega)
      omega
    · obtain ⟨v, hv⟩ := hm
      have hmod : k % 3 = 2 := by
        rw [hpower, show m = 2 * v + 1 by omega, pow_succ, pow_mul,
          Nat.mul_mod, Nat.pow_mod]
        simp
      have hk3 : k + 1 = 3 * ((k+1)/3) := by omega
      have hx : (2:ZMod 7)^(k+1) = 1 := by
        conv_lhs => rw [hk3, pow_mul]
        rw [show (2 : ZMod 7)^3 = 1 by decide, one_pow]
      have hdiv : 7 ∣ chain k 1 := (ZMod.natCast_eq_zero_iff _ _).1 (by
        rw [chain_cast]
        rw [pow_succ] at hx
        linear_combination hx)
      have heq := ((hall 1 (by decide) (by omega)).dvd_iff_eq (by decide : 7 ≠ 1)).1 hdiv
      have := hlarge 1 (by decide)
      omega
  · have hd3 : 3 ≤ d := by obtain ⟨v,hv⟩ := hd; omega
    let N := 2^u + 1
    let i := 2*u-1
    have hk' : 3*u ≤ k := by rw [hkd]; nlinarith [Nat.mul_le_mul_left u hd3]
    have hi : 1 ≤ i := by dsimp [i]; omega
    have hile : i ≤ k+1 := by dsimp [i]; omega
    have hix : i+1 = 2*u := by dsimp [i]; omega
    have hneg : (2:ZMod N)^u = -1 := by
      have hh : ((2:ZMod N)^u + 1) = 0 := by
        have hh' := ZMod.natCast_self N
        change (((2^u+1 : ℕ) : ZMod N)) = 0 at hh'
        push_cast at hh'
        exact hh'
      linear_combination hh
    have hx : (2:ZMod N)^k = -1 := by rw [hkd, pow_mul, hneg, hd.neg_one_pow]
    have hy : (2:ZMod N)^i * 2 = 1 := by
      rw [← pow_succ, hix, mul_comm 2 u, pow_mul, hneg]
      norm_num
    have hdiv : N ∣ chain k i := (ZMod.natCast_eq_zero_iff _ _).1 (by
      rw [chain_cast, hx]
      linear_combination -hy)
    have hN : 1 < N := by dsimp [N]; have := Nat.two_pow_pos u; omega
    have hexp : 2^(u+1) ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hexp
    have hge : 2 ^ 1 ≤ (2:ℕ)^i := Nat.pow_le_pow_right (by decide) hi
    have hu2 : 2 ≤ (2:ℕ)^u := by exact Nat.pow_le_pow_right (n := 2) (by decide) hu
    have hnq : N < chain k i := by
      dsimp [N, chain]
      have hsub : 2^k - 1 ≥ 2^u := by omega
      have hh := Nat.mul_le_mul (show 2 ≤ 2^i by simpa using hge) hsub
      omega
    have heq := ((hall i hi hile).dvd_iff_eq hN.ne').1 hdiv
    omega

abbrev demand (q : ℕ) := oddPart (1 + q)
abbrev demands (T : Finset ℕ) := ∏ q ∈ T, demand q
abbrev primesProduct (T : Finset ℕ) := ∏ q ∈ T, q
abbrev primeSupport (T : Finset ℕ) := ∀ q ∈ T, q.Prime ∧ q ≠ 2

def Splits (A B D : ℕ) (R : Finset ℕ) : Prop :=
  ∃ T U : Finset ℕ, ∃ d e : ℕ, Disjoint T U ∧ T ∪ U = R ∧ d * e = D ∧
    A * demands T = d * primesProduct T ∧ B * demands U = e * primesProduct U

theorem split_support (R : Finset ℕ) {A B D : ℕ} (hR : primeSupport R)
    (hbal : A * B * demands R = D * primesProduct R) : Splits A B D R := by
  induction R using Finset.strongInductionOn generalizing A B with
  | _ R ih =>
    rcases R.eq_empty_or_nonempty with hr | hr
    · subst R
      exact ⟨∅, ∅, A, B, by simp, by simp, by simpa using hbal, by simp, by simp⟩
    let p := R.max' hr
    have hp : p ∈ R := Finset.max'_mem R hr
    have hprime := (hR p hp).1
    have hnot : ¬ p ∣ demands R := by
      intro h
      apply OMA.R_Erdos1052_erdos_1052_R2.max_not_dvd_shift hr hR
      exact h.trans (Finset.prod_dvd_prod_of_dvd _ _ fun q _ => Nat.ordCompl_dvd (1+q) 2)
    have hdiv : p ∣ A * B := by
      have h : p ∣ D * primesProduct R := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp) D
      rw [← hbal] at h
      exact (hprime.dvd_mul.mp h).resolve_right hnot
    have leftCase (a b : ℕ) (hb : a * b * demands R = D * primesProduct R) (hpa : p ∣ a) :
        Splits a b D R := by
      obtain ⟨w, rfl⟩ := hpa
      have hrem : w * demand p * b * demands (R.erase p) = D * primesProduct (R.erase p) := by
        apply Nat.eq_of_mul_eq_mul_left hprime.pos
        calc p * (w * demand p * b * demands (R.erase p))
            = (p*w) * b * (demand p * demands (R.erase p)) := by ac_rfl
          _ = (p*w) * b * demands R := by rw [Finset.mul_prod_erase R demand hp]
          _ = D * primesProduct R := hb
          _ = p * (D * primesProduct (R.erase p)) := by
            rw [show primesProduct R = p * primesProduct (R.erase p) from
              (Finset.mul_prod_erase R (fun q : ℕ => q) hp).symm]
            ac_rfl
      obtain ⟨T,U,d,e,hdis,heq,hde,ht,hu⟩ := ih (R.erase p) (Finset.erase_ssubset hp)
        (fun q hq => hR q (Finset.mem_of_mem_erase hq)) hrem
      have hout : p ∉ T ∪ U := by simp [heq]
      have hT : p ∉ T := fun h => hout (Finset.mem_union_left U h)
      have hU : p ∉ U := fun h => hout (Finset.mem_union_right T h)
      refine ⟨insert p T,U,d,e,Finset.disjoint_insert_left.mpr ⟨hU,hdis⟩, ?_,hde, ?_,hu⟩
      · rw [Finset.insert_union, heq, Finset.insert_erase hp]
      · change p*w * (∏ q ∈ insert p T, demand q) = d * ∏ q ∈ insert p T, q
        rw [Finset.prod_insert hT, Finset.prod_insert hT]
        change p*w * (demand p * demands T) = d * (p * primesProduct T)
        calc p*w * (demand p * demands T) = p * (w * demand p * demands T) := by ac_rfl
          _ = p * (d * primesProduct T) := by rw [ht]
          _ = d * (p * primesProduct T) := by ac_rfl
    rcases hprime.dvd_mul.mp hdiv with ha | hb
    · exact leftCase A B hbal ha
    · obtain ⟨T,U,d,e,hd,he,hde,ht,hu⟩ := leftCase B A (by simpa [mul_comm B A] using hbal) hb
      exact ⟨U,T,e,d,hd.symm, (Finset.union_comm U T).trans he, (Nat.mul_comm e d).trans hde, hu, ht⟩

abbrev gain (q : ℕ) : ℚ := 1 + 1 / (q : ℚ)
abbrev abundancy (T : Finset ℕ) : ℚ := ∏ q ∈ T, gain q

theorem gain_one_le (q : ℕ) : 1 ≤ gain q :=
  le_add_of_nonneg_right (by positivity)

theorem gain_le_total {T : Finset ℕ} {q : ℕ} (hq : q ∈ T) : gain q ≤ abundancy T := by
  have h : 1 ≤ abundancy (T.erase q) := Finset.one_le_prod fun r _ => gain_one_le r
  calc gain q = gain q * 1 := (mul_one _).symm
    _ ≤ gain q * abundancy (T.erase q) := mul_le_mul_of_nonneg_left h (zero_le_one.trans (gain_one_le _))
    _ = abundancy T := Finset.mul_prod_erase T gain hq

theorem prime_mem_of_dvd {R : Finset ℕ} (hr : primeSupport R) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ primesProduct R) : p ∈ R := by
  obtain ⟨q,hq,hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
  simpa only [((hr q hq).1.dvd_iff_eq hp.ne_one).mp hdiv] using hq

theorem neutral_group_impossible {k : ℕ} (hk : 12 ≤ k) {T : Finset ℕ} (hp : primeSupport T)
    (hbal : chain k (k+1) * demands T = primesProduct T)
    (hratio : (chain k (k+1) : ℚ) * abundancy T = 2 * ((2:ℚ)^k)^2) : False := by
  let X := 2^k
  let Y := X-1
  let A := chain k (k+1)
  have hX : 2 ≤ X := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ k by omega)
  have hxy : Y+1 = X := by dsimp [Y]; omega
  have hY : 1 ≤ Y := by omega
  have ha : A = 1+2*X*Y := by dsimp [A,chain,Y,X]; rw [pow_succ]; ring
  have hasq : A < (2*Y+1)^2 := by rw [ha, ← hxy]; nlinarith
  have ha1 : 1 < A := by rw [ha]; nlinarith
  change A * demands T = primesProduct T at hbal
  change (A : ℚ) * abundancy T = _ at hratio
  have hratX : (A : ℚ) * abundancy T = 2 * (X : ℚ)^2 := by simpa [X] using hratio
  have lower (q : ℕ) (hq : q ∈ T) : X ≤ q := by
    have hq0 : 0 < (q : ℚ) := by exact_mod_cast (hp q hq).1.pos
    have haQ : (A : ℚ) = 1+2*(X : ℚ)*(Y : ℚ) := by exact_mod_cast ha
    have hxyQ : (Y : ℚ)+1 = X := by exact_mod_cast hxy
    have hYQ : (1 : ℚ) ≤ Y := by exact_mod_cast hY
    have h := mul_le_mul_of_nonneg_left (gain_le_total hq) (by positivity : (0:ℚ) ≤ A)
    rw [hratX] at h
    change (A : ℚ) * (1+1/(q:ℚ)) ≤ _ at h
    field_simp at h
    by_contra! hsmall
    have hqY : (q : ℚ) ≤ Y := by exact_mod_cast (show q ≤ Y by omega)
    rw [haQ, ← hxyQ] at h
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2*(Y:ℚ)+1) (sub_nonneg.mpr hqY)]
  have hT : T.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    rintro rfl
    simp at hbal
    omega
  let r := T.min' hT
  have hr : r ∈ T := Finset.min'_mem T hT
  have hdp (q : ℕ) (hq : q ∈ T) : demand q ∣ primesProduct T := by
    rw [← hbal]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem demand hq) A
  have hdr : demand r = 1 := by
    by_contra hn
    obtain ⟨p, hprime, hd⟩ := Nat.exists_prime_and_dvd hn
    have hmem := prime_mem_of_dvd hp hprime (hd.trans (hdp r hr))
    have hle : r ≤ p := Finset.min'_le T p hmem
    have hdo := twice_oddPart_shift_le ((hp _ hr).1.odd_of_ne_two (hp _ hr).2)
    have hpd := Nat.le_of_dvd (Nat.ordCompl_pos 2 (by omega : 1 + r ≠ 0)) hd
    change p ≤ demand r at hpd
    change 2 * demand r ≤ r+1 at hdo
    have := (hp r hr).1.two_le
    omega
  have rootpow := Nat.ordProj_mul_ordCompl_eq_self (1+r) 2
  change 2 ^ (1+r).factorization 2 * demand r = 1+r at rootpow
  rw [hdr,mul_one] at rootpow
  have hkr : k < (1+r).factorization 2 := by
    by_contra! he
    have hh := Nat.pow_le_pow_right (n := 2) (by decide) he
    rw [rootpow] at hh
    have := lower r hr
    change _ ≤ X at hh
    omega
  have hh := Nat.pow_le_pow_right (n := 2) (by decide) (show k+1 ≤ (1+r).factorization 2 by omega)
  rw [rootpow, pow_succ] at hh
  change X*2 ≤ 1+r at hh
  have hmin (p : ℕ) (h : p ∈ T) : 2*Y+1 ≤ p := by
    have hle : r ≤ p := Finset.min'_le T p h
    omega
  have small (v : ℕ) (hv : 1 < v) (hs : v < (2*Y+1)^2) (hd : v ∣ primesProduct T) : v ∈ T := by
    apply prime_mem_of_dvd hp _ hd
    by_contra hnp
    have hmf := prime_mem_of_dvd hp (Nat.minFac_prime hv.ne') ((Nat.minFac_dvd v).trans hd)
    have hlow := Nat.pow_le_pow_left (hmin _ hmf) 2
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < v) hnp
    omega
  have hA : A ∈ T := small A ha1 hasq (hbal ▸ dvd_mul_right _ _)
  have hchain (i : ℕ) (hi : i ≤ k+1) : 1 ≤ i → chain k i ∈ T := by
    induction hi using Nat.decreasingInduction with
    | self => exact fun _ => hA
    | of_succ i hi ih =>
      intro hi1
      have hcur := ih (by omega : 1 ≤ i+1)
      have h1 : 1 < chain k i := by
        change 1 < 1 + 2^i*Y
        have := Nat.two_pow_pos i
        exact Nat.lt_add_of_pos_right (Nat.mul_pos this (by omega))
      have hle : chain k i ≤ A := by
        change 1 + 2^i * Y ≤ 1 + 2^(k+1) * Y
        gcongr
        omega
      have hodd : ¬ 2 ∣ chain k i := by
        have h2i : 2 ∣ 2^i := dvd_pow_self _ (by omega)
        change ¬ 2 ∣ 1 + 2^i * Y
        have hmul := dvd_mul_of_dvd_left h2i Y
        exact fun h => (by decide : ¬ 2 ∣ 1) ((Nat.dvd_add_iff_left hmul).mpr h)
      have hd : demand (chain k (i+1)) = chain k i := by
        have hs : 1+chain k (i+1) = 2^1 * chain k i := by unfold chain; rw [pow_succ]; ring
        dsimp only [demand, oddPart]
        rw [hs]
        exact Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two hodd
      exact small _ h1 (lt_of_le_of_lt hle hasq) (hd ▸ hdp _ hcur)
  exact no_prime_chain hk (fun i hi hj => (hp _ (hchain i hj hi)).1)

end Erdos1052.Core625

/- Normalize the balance at core 625 and constrain the two factors of the seed. -/

namespace Erdos1052.Core625

open Erdos1052.CoreBounds

abbrev shifted (S : Finset ℕ) := ∏ q ∈ S, (1+q)
abbrev twoCount (S : Finset ℕ) := ∑ q ∈ S, (1+q).factorization 2

theorem abundancy_cross {S : Finset ℕ} (hp : primeSupport S) :
    abundancy S * (primesProduct S : ℚ) = (shifted S : ℚ) := by
  simp only [primesProduct, shifted, Nat.cast_prod, Nat.cast_add, Nat.cast_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  have H : (q : ℚ) ≠ 0 := by exact_mod_cast (hp q hq).1.ne_zero
  unfold gain
  field_simp
  ring

theorem shifted_eq (S : Finset ℕ) : shifted S = 2^twoCount S * demands S := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun q _ => (Nat.ordProj_mul_ordCompl_eq_self (1+q) 2).symm)

theorem group_ratio {S : Finset ℕ} (hp : primeSupport S) {A j : ℕ}
    (hb : A * demands S = 5^j * primesProduct S) :
    (A : ℚ) * abundancy S = (2:ℚ)^twoCount S * 5^j := by
  have h : (A : ℚ) * (demands S : ℚ) = (5 : ℚ)^j * (primesProduct S : ℚ) := by exact_mod_cast hb
  have hz : primesProduct S ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hp q hq).1.ne_zero)
  have hzn : (primesProduct S : ℚ) ≠ 0 := by exact_mod_cast hz
  apply mul_right_cancel₀ hzn
  rw [mul_assoc, abundancy_cross hp, shifted_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc (A : ℚ) * (2 ^ twoCount S * (demands S : ℚ))
      = 2 ^ twoCount S * (A * (demands S : ℚ)) := by ring
    _ = _ := by rw [h]; ring

theorem sigma_625 {a : ℕ} (ha : a ≠ 0) :
    sigmaU (2 ^ a * 625) = 626 * (2^a+1) := by
  have hb : (2 : ℕ)^a ≠ 0 := pow_ne_zero _ (by decide)
  have h5 : Nat.Prime 5 := by decide
  have hpf : (2^a*625 : ℕ).primeFactors = {2,5} := by
    rw [show (625:ℕ)=5^4 by rfl, Nat.primeFactors_mul hb (by decide),
      Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow (by decide) h5]
    rfl
  have hfac (p : ℕ) : (2^a*625 : ℕ).factorization p =
      (if 2=p then a else 0)+(if 5=p then 4 else 0) := by
    rw [show (625:ℕ)=5^4 by rfl, Nat.factorization_mul hb (by decide),
      Nat.prime_two.factorization_pow, h5.factorization_pow]
    simp [Finsupp.single_apply, eq_comm]
  unfold sigmaU
  rw [hpf]
  simp only [Finset.prod_insert (by decide : 2 ∉ ({5} : Finset ℕ)), Finset.prod_singleton, hfac]
  norm_num
  ring

set_option maxRecDepth 8192 in
theorem remove_forced {a : ℕ} (ha : a ≠ 0) {S : Finset ℕ}
    (hp : ∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2^a*625)
    (hb : sigmaU (2^a*625) * shifted S = 2*(2^a*625)*primesProduct S) :
    ∃ R : Finset ℕ, primeSupport R ∧ (∀ q ∈ R, q ∉ ({5,79,157,313} : Finset ℕ)) ∧
      (2^a+1) * demands R = 125 * primesProduct R ∧ abundancy R < 125/64 := by
  obtain ⟨h313,h157,h79⟩ := forced_primes_at_625 (fun q hq => (hp q hq).1) hb
  let F : Finset ℕ := {313,157,79}
  let R := S \ F
  have hFS : F ⊆ S := by simpa [F, Finset.insert_subset_iff] using And.intro h313 (And.intro h157 h79)
  have hdis : Disjoint F R := Finset.disjoint_left.mpr (fun p hf hr => (Finset.mem_sdiff.mp hr).2 hf)
  have hun : F ∪ R = S := by
    ext q
    simp only [R, Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (hFS ·) And.left, fun h => or_iff_not_imp_left.mpr (fun hf => ⟨h,hf⟩)⟩
  have h2 : 2 ∣ 2^a*625 := dvd_mul_of_dvd_left (dvd_pow_self 2 ha) _
  have h5 : 5 ∣ 2^a*625 := dvd_mul_of_dvd_right (by decide : 5 ∣ 625) _
  have hpr : primeSupport R := fun q hq =>
    ⟨(hp q (Finset.mem_sdiff.mp hq).1).1, fun he => (hp q (Finset.mem_sdiff.mp hq).1).2 (he ▸ h2)⟩
  have hban (q : ℕ) (hq : q ∈ R) : q ∉ ({5,79,157,313} : Finset ℕ) := by
    have hnf := (Finset.mem_sdiff.mp hq).2
    have hn5 : q ≠ 5 := fun he => (hp q (Finset.mem_sdiff.mp hq).1).2 (he ▸ h5)
    simp [F] at hnf
    simp [hn5, hnf]
  have unpack (f : ℕ → ℕ) : (∏ q ∈ S, f q) = (f 313*f 157*f 79)*(∏ q ∈ R, f q) := by
    conv_lhs => rw [← hun, Finset.prod_union hdis]
    simp [F, mul_assoc]
  rw [sigma_625 ha, show shifted S = _ from unpack (fun q => 1+q),
    show primesProduct S = _ from unpack id] at hb
  have hcross : 64*((2^a+1)*shifted R) = 125*(2^a*primesProduct R) := by
    change 626 * (2^a+1) * ((314*158*80) * shifted R) =
      2*(2^a*625)*((313*157*79)*primesProduct R) at hb
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 38821390)
    linear_combination (norm := ring_nf) hb
  have hpow : ¬ 2 ∣ 2^a+1 := by have := dvd_pow_self 2 ha; omega
  have hor : oddPart (primesProduct R) = primesProduct R := by
    apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr
    right
    intro h
    obtain ⟨q,hq,hd⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp h
    exact (hpr q hq).2 (((hpr q hq).1.dvd_iff_eq (by decide : 2 ≠ 1)).mp hd)
  have ho := congrArg oddPart hcross
  change oddPart (2^6*((2^a+1)*shifted R)) = oddPart (125*(2^a*primesProduct R)) at ho
  have strip (s t : ℕ) : oddPart (2^s*t) = oddPart t := Nat.ordCompl_self_pow_mul _ _ Nat.prime_two
  have mult (s t : ℕ) : oddPart (s*t) = oddPart s*oddPart t := Nat.ordCompl_mul _ _ _
  rw [strip, mult, mult 125, strip,
    show oddPart (2^a+1) = 2^a+1 from (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (.inr hpow)] at ho
  have hop := oddPart_prod R (fun q => 1+q)
  change oddPart (shifted R) = demands R at hop
  have hh : oddPart 125 = 125 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (.inr (by decide))
  have ho' : (2^a+1)*demands R = 125*primesProduct R := by simpa only [hop, hor, hh] using ho
  refine ⟨R,hpr,hban,ho',?_⟩
  have hc : (64:ℚ)*((2^a+1)*(shifted R : ℚ)) = 125*(2^a*(primesProduct R : ℚ)) := by exact_mod_cast hcross
  rw [← abundancy_cross hpr] at hc
  have hpos : 0 < (primesProduct R : ℚ) := by
    exact_mod_cast (Finset.prod_pos (fun q hq => (hpr q hq).1.pos))
  have hc' : (64:ℚ)*(2^a+1)*abundancy R = 125*2^a := by
    apply mul_right_cancel₀ hpos.ne'
    linear_combination hc
  by_contra! h
  have hle := mul_le_mul_of_nonneg_left h (show 0 ≤ (64:ℚ)*(2^a+1) by positivity)
  linarith

theorem round_group {l E j : ℕ} (hj : j ≤ 3) {A B : ℚ} (hA : 0 < A)
    (hB : 1 ≤ B) (hmax : B < 125/64)
    (hlo : (1-1/2048)*A < 2^l) (hhi : (2:ℚ)^l < (1+1/2048)*A)
    (heq : A*B = 2^E*5^j) :
    A*B = (2:ℚ)^l*(5/4)^j ∧ (5/4)^j*(1-1/2048) ≤ B ∧ B < (5/4)^j*(1+1/2048) := by
  let t : ℚ := (5/4)^j
  have ht : 1 ≤ t ∧ t ≤ 125/64 := by dsimp [t]; interval_cases j <;> norm_num
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have representation : A*B = (2:ℚ)^(E+2*j)*t := by
    rw [heq, pow_add, pow_mul, mul_assoc, ← mul_pow]
    norm_num
  have leading : E+2*j = l := by
    rcases lt_trichotomy (E+2*j) l with h | h | h
    · have hh : (2:ℚ)^(E+2*j+1) ≤ 2^l := pow_le_pow_right₀ (by norm_num) h
      rw [pow_succ] at hh
      have hm := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (2:ℚ)^(E+2*j) by positivity)
      have hbase : A ≤ A*B := by simpa using mul_le_mul_of_nonneg_left hB hA.le
      linarith
    · exact h
    · have hh : (2:ℚ)^(l+1) ≤ 2^(E+2*j) := pow_le_pow_right₀ (by norm_num) h
      rw [pow_succ] at hh
      have hm := mul_le_mul_of_nonneg_left ht.1 (show 0 ≤ (2:ℚ)^(E+2*j) by positivity)
      have hbase := mul_lt_mul_of_pos_left hmax hA
      linarith
  rw [leading] at representation
  refine ⟨representation, ?_, ?_⟩
  · apply (le_of_mul_le_mul_left _ hA)
    calc A*(t*(1-1/2048)) = ((1-1/2048)*A)*t := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hlo.le htpos.le).trans representation.symm.le
  · apply (lt_of_mul_lt_mul_left _ hA.le)
    calc A*B = (2:ℚ)^l*t := representation
      _ < ((1+1/2048)*A)*t := mul_lt_mul_of_pos_right hhi htpos
      _ = _ := by ring

end Erdos1052.Core625

/- A finite rational certificate with a bound on all omitted primes. -/

namespace Erdos1052.Core625

open Erdos1052.CoreBounds

def mersenneFactor (t : ℕ) : ℚ := (2:ℚ)^t / (2^t-2)
def mersenneBound (t : ℕ) : ℚ := (2:ℚ)^t / (2^t-4)

theorem large_mersenne_product (K : Finset ℕ) {s : ℕ} (hs : 13 ≤ s)
    (hK : ∀ t ∈ K, s ≤ t) : (∏ t ∈ K, mersenneFactor t) ≤ mersenneBound s := by
  induction K using Finset.strongInductionOn generalizing s with
  | _ K ih =>
    have hs0 : (4:ℚ) < 2^s := lt_of_lt_of_le (by norm_num : (4:ℚ) < 2^13)
      (pow_le_pow_right₀ (by norm_num) hs)
    rcases K.eq_empty_or_nonempty with hk | hk
    · subst K
      simp only [Finset.prod_empty, mersenneBound]
      apply (le_div_iff₀ (by linarith)).2
      linarith
    let t := K.min' hk
    have ht := Finset.min'_mem K hk
    have hst : s ≤ t := hK t ht
    have hpow : (2:ℚ)^s ≤ 2^t := pow_le_pow_right₀ (by norm_num) hst
    have hinc : ∀ j ∈ K.erase t, t+1 ≤ j := by
      intro j hj
      obtain ⟨hne,hj⟩ := Finset.mem_erase.mp hj
      have := Finset.min'_le K j hj
      change t ≤ j at this
      omega
    have hrec := ih (K.erase t) (Finset.erase_ssubset ht) (s := t+1) (by omega) hinc
    rw [← Finset.mul_prod_erase K mersenneFactor ht]
    calc mersenneFactor t * (∏ j ∈ K.erase t, mersenneFactor j)
        ≤ mersenneFactor t * mersenneBound (t+1) :=
          mul_le_mul_of_nonneg_left hrec (div_nonneg (by positivity) (by linarith))
      _ ≤ mersenneBound t := by
        unfold mersenneFactor mersenneBound
        have h2 : 0 < (2:ℚ)^t-2 := by linarith
        have h4 : 0 < (2:ℚ)^t*2-4 := by linarith
        rw [pow_succ, div_mul_div_comm, div_le_div_iff₀ (mul_pos h2 h4) (by linarith)]
        nlinarith
      _ ≤ mersenneBound s := by
        unfold mersenneBound
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith

abbrev smallMersennes : Finset ℕ := {3,7,31,127}
def tail (x D : ℕ) : ℚ := (1+2/(x:ℚ)) ^ D.primeFactorsList.length *
  ((2048/2047) * ∏ p ∈ smallMersennes.filter (x < ·), pathBound p)

set_option maxRecDepth 8192 in
theorem roots_bound {x : ℕ} (S : Finset ℕ) (hp : primeSupport S) (hxS : ∀ q ∈ S, x < q) :
    (∏ q ∈ S, if demand q = 1 then pathBound q else 1) ≤
      (2048/2047 : ℚ) * ∏ p ∈ smallMersennes.filter (x < ·), pathBound p := by
  let R := S.filter (fun q => demand q = 1)
  have hR (q : ℕ) (hq : q ∈ R) : q ∈ S ∧ demand q = 1 := Finset.mem_filter.mp hq
  let t := fun q : ℕ => (1+q).factorization 2
  have hpow (q : ℕ) (hq : q ∈ R) : 2 ^ t q = 1+q := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
    change 2 ^ t q * demand q = 1+q at h
    simpa only [(hR q hq).2, mul_one] using h
  let small := R.filter (fun q => t q < 13)
  let big := R.filter (fun q => ¬ t q < 13)
  have hfinite : ∀ j ∈ Finset.range 13, (2^j-1 : ℕ).Prime → 2^j-1 ∈ smallMersennes := by
    decide +kernel
  have hsub : small ⊆ smallMersennes.filter (x < ·) := by
    intro q hq
    obtain ⟨hr,ht⟩ := Finset.mem_filter.mp hq
    have hs := (hR q hr).1
    have hval : 2 ^ t q - 1 = q := by have := hpow q hr; omega
    have hh := hfinite (t q) (Finset.mem_range.mpr ht)
    rw [hval] at hh
    exact Finset.mem_filter.mpr ⟨hh (hp q hs).1, hxS q hs⟩
  have pathpos {q : ℕ} (hq : 1 < q) : 1 ≤ pathBound q := by
    unfold pathBound
    have : (1:ℚ) < q := by exact_mod_cast hq
    apply (le_div_iff₀ (by linarith)).2
    linarith
  have hsmall : (∏ q ∈ small, pathBound q) ≤ ∏ p ∈ smallMersennes.filter (x < ·), pathBound p := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    · intro q hq
      exact zero_le_one.trans (pathpos (hp q (hR q (Finset.mem_filter.mp hq).1).1).1.one_lt)
    · intro q hq _
      have hq' := (Finset.mem_filter.mp hq).1
      have hgt : ∀ p ∈ smallMersennes, 1 < p := by decide
      exact pathpos (hgt q hq')
  have hb (q : ℕ) (hq : q ∈ big) := (Finset.mem_filter.mp hq).1
  have hinj : Set.InjOn t big := by
    intro q hq p hp he
    have h1 := hpow q (hb q hq)
    have h2 := hpow p (hb p hp)
    rw [show t q = t p from he] at h1
    omega
  have hid (q : ℕ) (hq : q ∈ big) : pathBound q = mersenneFactor (t q) := by
    have hv : (2:ℚ) ^ t q = 1+q := by exact_mod_cast hpow q (hb q hq)
    unfold pathBound mersenneFactor
    rw [hv]
    congr 1 <;> ring
  have hbig : (∏ q ∈ big, pathBound q) ≤ (2048/2047 : ℚ) := by
    have heq : (∏ q ∈ big, pathBound q) = ∏ j ∈ big.image t, mersenneFactor j := by
      rw [Finset.prod_image hinj]
      exact Finset.prod_congr rfl hid
    rw [heq]
    apply le_trans (large_mersenne_product (big.image t) (s := 13) (by decide) ?_)
    · norm_num [mersenneBound]
    · intro j hj
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
      exact Nat.le_of_not_gt (Finset.mem_filter.mp hq).2
  change _ ≤ _ * _
  rw [← Finset.prod_filter]
  change (∏ q ∈ R, pathBound q) ≤ _
  rw [← Finset.prod_filter_mul_prod_filter_not R (fun q => t q < 13) pathBound]
  rw [mul_comm (2048/2047 : ℚ)]
  exact mul_le_mul hsmall hbig
    (Finset.prod_nonneg fun q hq => zero_le_one.trans (pathpos (hp q (hR q (hb q hq)).1).1.one_lt))
    (le_trans (Finset.prod_nonneg (fun q hq => zero_le_one.trans
      (pathpos (hp q (hR q (Finset.mem_filter.mp hq).1).1).1.one_lt))) hsmall)

theorem tail_covers {x D : ℕ} (S : Finset ℕ) (hx : 1 ≤ x) (hD : D ≠ 0)
    (hp : primeSupport S) (hr : ∀ q ∈ S, x < q) (hd : demands S ∣ D * primesProduct S) :
    abundancy S ≤ tail x D := by
  apply le_trans (compatible_tail_bound S demand hx hD (fun q hq =>
    ⟨(hp q hq).1,hr q hq,Nat.ordCompl_pos 2 (by omega),
      twice_oddPart_shift_le ((hp q hq).1.odd_of_ne_two (hp q hq).2)⟩) hd)
  exact mul_le_mul_of_nonneg_left (roots_bound S hp hr) (by positivity)

def Gap (ban : Finset ℕ) (L H A : ℚ) (x D : ℕ) : Prop :=
  ∀ S : Finset ℕ, primeSupport S → (∀ q ∈ S, x < q ∧ q ∉ ban) →
    demands S ∣ D * primesProduct S → ¬ (L ≤ A * abundancy S ∧ A * abundancy S < H)

def nextPrimes (ban : Finset ℕ) (x y D : ℕ) : Finset ℕ :=
  (Finset.Icc (x+1) y).filter (fun q => q ∉ ban ∧ q.Prime ∧ demand q ∣ D)

theorem gap_high {ban : Finset ℕ} {L H A : ℚ} {x D : ℕ} (ha : 0 ≤ A) (hh : H ≤ A) :
    Gap ban L H A x D := by
  intro S _ _ _ hbad
  have h := mul_le_mul_of_nonneg_left (Finset.one_le_prod (s := S) (fun q _ => gain_one_le q)) ha
  exact (not_lt_of_ge (hh.trans (by simpa using h))) hbad.2

theorem gap_split {ban : Finset ℕ} {L H A : ℚ} {x y D : ℕ}
    (hy : 1 ≤ y) (hD : D ≠ 0) (ha : 0 ≤ A) (hleaf : A * tail y D < L)
    (children : ∀ q ∈ nextPrimes ban x y D,
      Gap ban L H (A * gain q) q (D / demand q * q)) : Gap ban L H A x D := by
  intro S hp hs hd bad
  by_cases habove : ∀ q ∈ S, y < q
  · exact (not_lt_of_ge bad.1) ((mul_le_mul_of_nonneg_left (tail_covers S hy hD hp habove hd) ha).trans_lt hleaf)
  push Not at habove
  obtain ⟨r,hr,hry⟩ := habove
  let q := S.min' ⟨r,hr⟩
  have hq : q ∈ S := Finset.min'_mem S _
  have hqy : q ≤ y := (Finset.min'_le S r hr).trans hry
  have hdo := twice_oddPart_shift_le ((hp q hq).1.odd_of_ne_two (hp q hq).2)
  change 2 * demand q ≤ q+1 at hdo
  have hdpos : 0 < demand q := Nat.ordCompl_pos 2 (by omega)
  have hc : (demand q).Coprime (primesProduct S) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hP
    apply Nat.Coprime.symm
    apply (hp p hP).1.coprime_iff_not_dvd.mpr
    intro hdiv
    have hlow : q ≤ p := Finset.min'_le S p hP
    have hhigh := Nat.le_of_dvd hdpos hdiv
    have := (hp q hq).1.two_le
    omega
  have hdD : demand q ∣ D := hc.dvd_of_dvd_mul_right
    ((Finset.dvd_prod_of_mem demand hq).trans hd)
  have hsel : q ∈ nextPrimes ban x y D := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨(hs q hq).1,hqy⟩,(hs q hq).2,(hp q hq).1,hdD⟩
  have hrest : demands (S.erase q) ∣ (D / demand q * q) * primesProduct (S.erase q) := by
    apply (Nat.mul_dvd_mul_iff_left hdpos).1
    rw [show demand q * demands (S.erase q) = demands S from Finset.mul_prod_erase S demand hq]
    convert hd using 1
    calc demand q * (D / demand q * q * primesProduct (S.erase q))
        = (D / demand q * demand q) * (q * primesProduct (S.erase q)) := by ac_rfl
      _ = D * primesProduct S := by rw [Nat.div_mul_cancel hdD, Finset.mul_prod_erase S (fun p : ℕ => p) hq]
  have hresult := children q hsel (S.erase q) (fun p hP => hp p (Finset.mem_of_mem_erase hP))
    (fun p hP => ⟨lt_of_le_of_ne (Finset.min'_le S p (Finset.mem_of_mem_erase hP))
      (Finset.mem_erase.mp hP).1.symm,(hs p (Finset.mem_of_mem_erase hP)).2⟩) hrest
  rw [mul_assoc, show gain q * abundancy (S.erase q) = abundancy S from Finset.mul_prod_erase S gain hq] at hresult
  exact hresult bad

abbrev CutTable := List (ℕ × ℕ × ℕ)

def cutoff (table : CutTable) (x D : ℕ) : ℕ :=
  ((table.find? (fun row => row.1 == x && row.2.1 == D)).map (fun row => row.2.2)).getD 0

def stripTwos : ℕ → ℕ → ℕ
  | 0, n => n
  | f+1, n => if 2 ∣ n then stripTwos f (n/2) else n

theorem stripTwos_eq {f n : ℕ} (hn : 0 < n) (hb : n < 2^f) :
    stripTwos f n = oddPart n := by
  induction f generalizing n with
  | zero => simp at hb; omega
  | succ f ih =>
    rw [stripTwos]
    split_ifs with h
    · obtain ⟨w,rfl⟩ := h
      rw [Nat.mul_div_cancel_left _ (by decide)]
      rw [show 2*w=2^1*w by simp,show oddPart (2^1*w) = oddPart w from
        Nat.ordCompl_self_pow_mul _ _ Nat.prime_two]
      exact ih (by omega) (by rw [pow_succ] at hb; omega)
    · exact ((Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (.inr h)).symm

def trialDivisors : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]

def possiblePrime (q : ℕ) := trialDivisors.all (fun p => q == p || q % p != 0)

theorem prime_possible {q : ℕ} (hq : q.Prime) : possiblePrime q = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have ho : 1 ∉ trialDivisors := by decide
  have hne : p ≠ 1 := fun h => ho (h ▸ hp)
  by_cases h : p ∣ q
  · simp [((hq.dvd_iff_eq hne).mp h).symm]
  · simp [show q%p ≠ 0 from fun he => h (Nat.dvd_of_mod_eq_zero he)]

def knownPrimes : List ℕ := [3,5,7,11,13,19,23,29,31,37,43,47,61,73,103,127,151,223,367,1777]
theorem known_primes : ∀ q ∈ knownPrimes, Nat.Prime q := by
  simp only [knownPrimes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
  norm_num

def factorWitness (D : ℕ) : List ℕ :=
  let data : List (ℕ × List ℕ) :=
    [(5,[5]),(7,[7]),(13,[13]),(15,[3,5]),(29,[29]),(35,[5,7]),(55,[5,11]),
     (57,[3,19]),(65,[5,13]),(103,[103]),(111,[3,37]),(115,[5,23]),(133,[7,19]),
     (209,[11,19]),(215,[5,43]),(217,[7,31]),(259,[7,37]),(427,[7,61]),(437,[19,23]),
     (515,[5,103]),(851,[23,37]),(1651,[13,127]),(1661,[11,151]),(1679,[23,73]),
     (1739,[37,47]),(3431,[47,73]),(8251,[37,223]),(8255,[5,13,127]),(16891,[7,19,127]),
     (26543,[11,19,127]),(32893,[7,37,127]),(54229,[7,61,127]),(65749,[37,1777]),
     (108077,[23,37,127]),(134239,[7,127,151]),(210947,[11,127,151]),(213233,[23,73,127]),
     (435737,[47,73,127]),(3402457,[73,127,367]),(4276471,[127,151,223])]
  ((data.find? (fun row => row.1 == D)).map Prod.snd).getD []

def explicitTail (y w : ℕ) : ℚ :=
  (1+2/(y:ℚ))^w * ((2048/2047) * ∏ p ∈ smallMersennes.filter (y < ·), pathBound p)

def verifies (table : CutTable) (ban : Finset ℕ) (L H : ℚ) : ℕ → ℚ → ℕ → ℕ → Bool
  | 0, A, _, _ => decide (0 ≤ A ∧ H ≤ A)
  | fuel+1, A, x, D =>
    if H ≤ A then decide (0 ≤ A) else
      let y := cutoff table x D
      let fs := factorWitness D
      decide (1 ≤ y ∧ y < 4094 ∧ D ≠ 0 ∧ 0 ≤ A ∧ fs.prod = D ∧
        (∀ p ∈ fs, p ∈ knownPrimes) ∧ A * explicitTail y fs.length < L) &&
      (List.range' (x+1) (y-x)).all (fun q =>
        let d := stripTwos 12 (1+q)
        if d ∣ D ∧ q ∉ ban ∧ possiblePrime q = true then
          verifies table ban L H fuel (A * gain q) q (D / d * q) else true)

theorem verifies_sound {table : CutTable} {ban : Finset ℕ} {L H A : ℚ} {x D fuel : ℕ}
    (h : verifies table ban L H fuel A x D = true) : Gap ban L H A x D := by
  induction fuel generalizing A x D with
  | zero =>
    have hh : 0 ≤ A ∧ H ≤ A := of_decide_eq_true h
    exact gap_high hh.1 hh.2
  | succ fuel ih =>
    rw [verifies] at h
    split_ifs at h with hh
    · exact gap_high (of_decide_eq_true h) hh
    · obtain ⟨ht,hchildren⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨hy,hbound,hD,ha,hprod,hpr,hleaf⟩ := of_decide_eq_true ht
      have he := (Nat.primeFactorsList_unique hprod (fun p hp => known_primes p (hpr p hp))).length_eq
      have leaf : A * tail (cutoff table x D) D < L := by
        rwa [show tail (cutoff table x D) D = explicitTail (cutoff table x D) (factorWitness D).length
          from congrArg (explicitTail (cutoff table x D)) he.symm]
      apply gap_split hy hD ha leaf
      intro q hq
      obtain ⟨hqxy,hban,hprime,hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hxq,hqy⟩ := Finset.mem_Icc.mp hqxy
      have hqs : q ∈ List.range' (x+1) (cutoff table x D-x) := by
        rw [List.mem_range'_1]; omega
      have hs := List.all_eq_true.mp hchildren q hqs
      have heq : stripTwos 12 (1+q) = demand q := stripTwos_eq (by omega) (by norm_num; omega)
      simp only [heq, hd, hban, prime_possible hprime] at hs
      exact ih hs

def forbidden : Finset ℕ := {5,79,157,313}
def lowerEdge (j : ℕ) : ℚ := (5/4)^j * (1-1/2048)
def upperEdge (j : ℕ) : ℚ := (5/4)^j * (1+1/2048)

def cutsOne : CutTable :=
  [(1,1,7),(7,7,31),(13,13,137),(103,103,411),(127,1651,598),
   (31,217,97),(61,427,127),(127,54229,183)]

def cutsSeven : CutTable := [(1,5,14)]

def cutsThirtyOne : CutTable :=
  [(1,5,14),(7,35,54),(13,65,275),(103,515,822),(127,8255,897),
   (19,133,127),(37,259,374),(127,32893,2119),(1777,65749,1777),
   (223,8251,645),(127,16891,203),(151,134239,262),(223,4276471,325)]

def cutsSecond : CutTable :=
  [(1,5,7),(3,15,31),(11,55,72),(19,209,207),(127,26543,522),
   (151,210947,1229),(151,1661,314),(43,215,125),(19,57,44),
   (23,437,83),(37,851,127),(73,1679,170),(127,213233,383),
   (367,3402457,463),(127,108077,205),(37,111,62),(47,1739,93),
   (73,3431,127),(127,435737,161),(23,115,40),(29,29,31)]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem four_gaps :
    Gap (insert 3 forbidden) (lowerEdge 1) (upperEdge 1) 1 1 1 ∧
    Gap (insert 3 (insert 7 forbidden)) (lowerEdge 1) (upperEdge 1) 1 1 5 ∧
    Gap (insert 3 (insert 31 forbidden)) (lowerEdge 1) (upperEdge 1) 1 1 5 ∧
    Gap (insert 7 (insert 31 forbidden)) (lowerEdge 2) (upperEdge 2) 1 1 5 := by
  refine ⟨verifies_sound (table := cutsOne) (fuel := 12) ?_,
    verifies_sound (table := cutsSeven) (fuel := 12) ?_,
    verifies_sound (table := cutsThirtyOne) (fuel := 12) ?_,
    verifies_sound (table := cutsSecond) (fuel := 12) ?_⟩ <;> decide +kernel

end Erdos1052.Core625

/- The unconditional large-exponent exclusion at repeated odd core 625. -/

namespace Erdos1052.Core625

open Erdos1052.CoreBounds

theorem forbid_mixed {A B : ℕ} {T U : Finset ℕ}
    (ht : primeSupport T) (hu : primeSupport U)
    (hft : ∀ q ∈ T, q ∉ forbidden) (hfu : ∀ q ∈ U, q ∉ forbidden) (hdis : Disjoint T U)
    (h5 : 5 ∣ A*B) (ha : A*demands T = 5*primesProduct T)
    (hb : B*demands U = 25*primesProduct U)
    (hi : lowerEdge 1 ≤ abundancy T ∧ abundancy T < upperEdge 1)
    (hj : lowerEdge 2 ≤ abundancy U ∧ abundancy U < upperEdge 2) : False := by
  obtain ⟨g₀,g₇,g₃₁,g₂⟩ := four_gaps
  have h3 : 3 ∉ T := by
    intro h
    have hh := (gain_le_total h).trans_lt hi.2
    norm_num [gain, upperEdge] at hh
  have rule {V : Finset ℕ} {P : Finset ℕ} {j D : ℕ} (g : Gap P (lowerEdge j) (upperEdge j) 1 1 D)
      (hp : primeSupport V) (hf : ∀ q ∈ V, q ∉ P) (hd : demands V ∣ D*primesProduct V)
      (hband : lowerEdge j ≤ abundancy V ∧ abundancy V < upperEdge j) : False :=
    g V hp (fun q hq => ⟨(hp q hq).1.one_lt,hf q hq⟩) hd (by simpa using hband)
  have cancel {Z W V M p : ℕ} (h : p ∣ Z) (hpos : 0<p) (he : Z*W=(p*M)*V) : W ∣ M*V := by
    obtain ⟨u,rfl⟩ := h
    exact ⟨u, by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc p*(M*V) = (p*M)*V := by ac_rfl
        _ = p*u*W := he.symm
        _ = _ := by ac_rfl⟩
  have d5 : demands T ∣ 5*primesProduct T := ⟨A, by simpa [Nat.mul_comm] using ha.symm⟩
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5 with h | h
  · have hd := cancel (M:=1) h (by decide) (by simpa using ha)
    exact rule g₀ ht (fun q hq => by simp [hft q hq]; exact fun e => h3 (e ▸ hq)) hd hi
  · have force {p : ℕ} (g : Gap (insert 3 (insert p forbidden)) (lowerEdge 1) (upperEdge 1) 1 1 5) :
        p ∈ T := by
      by_contra hn
      apply rule g ht _ d5 hi
      intro q hq
      have hn3 : q ≠ 3 := fun e => h3 (e ▸ hq)
      have hnp : q ≠ p := fun e => hn (e ▸ hq)
      simp [hn3,hnp,hft q hq]
    have h7 := force g₇
    have h31 := force g₃₁
    have hd := cancel (M:=5) h (by decide) (by simpa using hb)
    apply rule g₂ hu _ hd hj
    intro q hq
    have hn7 : q ≠ 7 := fun e => (Finset.disjoint_left.mp hdis h7) (e ▸ hq)
    have hn31 : q ≠ 31 := fun e => (Finset.disjoint_left.mp hdis h31) (e ▸ hq)
    simp [hn7,hn31,hfu q hq]

theorem exclude_large {k : ℕ} (hk : 12 ≤ k) {R : Finset ℕ}
    (hp : primeSupport R) (hf : ∀ q ∈ R, q ∉ forbidden)
    (hb : (2^(2*(2*k+1))+1) * demands R = 125*primesProduct R)
    (hm : abundancy R < 125/64) : False := by
  let X : ℕ := 2^k
  let l := 2*k+1
  let L : ℕ := 2^l
  let A := 1+2*X*(X+1)
  let B := chain k (k+1)
  have hx : 4096 ≤ X := Nat.pow_le_pow_right (n:=2) (by decide) hk
  have lx : L = 2*X^2 := by dsimp [L,l,X]; rw [pow_succ, Nat.mul_comm 2 k,pow_mul]; ring
  have bx : B = 1+2*X*(X-1) := by dsimp [B,chain,X]; rw [pow_succ]; ring
  have hAB : A*B = 2^(2*(2*k+1))+1 := by
    rw [show 2^(2*(2*k+1)) = L^2 by dsimp [L,l]; rw [Nat.mul_comm 2 (2*k+1),pow_mul],lx,bx]
    let Y := X-1
    change (1+2*X*(X+1))*(1+2*X*Y) = (2*X^2)^2+1
    have hX : X = Y+1 := by dsimp [Y]; omega
    rw [hX]
    ring
  have five : 5 ∣ A*B := by
    rw [hAB]
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [show 2*(2*k+1)=4*k+2 by omega, pow_add,pow_mul,
      show (2 : ZMod 5)^4 = 1 by decide, one_pow, one_mul]
    decide
  have hsplit := split_support R hp (show A*B*demands R = _ by rw [hAB]; exact hb)
  obtain ⟨T,U,d,e,hdis,hunion,hde,hdt,heu⟩ := hsplit
  have hT : T ⊆ R := hunion ▸ Finset.subset_union_left
  have hU : U ⊆ R := hunion ▸ Finset.subset_union_right
  have ht : primeSupport T := fun q hq => hp q (hT hq)
  have hu : primeSupport U := fun q hq => hp q (hU hq)
  have mag {V : Finset ℕ} (hs : V ⊆ R) : abundancy V < 125/64 :=
    (Finset.prod_le_prod_of_subset_of_one_le hs (fun q _ => zero_le_one.trans (gain_one_le q))
      (fun q _ _ => gain_one_le q)).trans_lt hm
  obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5) (m:=3)).1
    (show d ∣ 5^3 from ⟨e,hde.symm⟩)
  obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5) (m:=3)).1
    (show e ∣ 5^3 from ⟨5^j,by simpa [mul_comm] using hde.symm⟩)
  have hsum : j+i=3 := by
    apply Nat.pow_right_injective (by decide : 1 < 5)
    simpa [pow_add] using hde
  have lxq : (2:ℚ)^l = 2*(X:ℚ)^2 := by exact_mod_cast lx
  have axq : (A:ℚ) = 1+2*(X:ℚ)*(X+1) := by dsimp only [A]; push_cast; ring
  have bxq : (B:ℚ) = 1+2*(X:ℚ)*(X-1) := by
    rw [bx]; push_cast [Nat.cast_sub (show 1 ≤ X by omega)]; ring
  have hxq : (4096:ℚ) ≤ X := by exact_mod_cast hx
  have hin := mul_nonneg (show (0:ℚ) ≤ X by positivity) (sub_nonneg.mpr hxq)
  have hA : 0 < (A:ℚ) := by rw [axq]; positivity
  have hB : 0 < (B:ℚ) := by rw [bxq]; nlinarith
  have rt := round_group hj hA (Finset.one_le_prod (fun q (_ : q ∈ T) => gain_one_le q)) (mag hT)
    (by rw [lxq,axq]; nlinarith) (by rw [lxq,axq]; nlinarith) (group_ratio ht hdt)
  have ru := round_group hi hB (Finset.one_le_prod (fun q (_ : q ∈ U) => gain_one_le q)) (mag hU)
    (by rw [lxq,bxq]; nlinarith) (by rw [lxq,bxq]; nlinarith) (group_ratio hu heu)
  have hjpos : j ≠ 0 := by
    rintro rfl
    have hh := rt.1
    have hl := mul_le_mul_of_nonneg_left (Finset.one_le_prod (fun q (_ : q ∈ T) => gain_one_le q)) hA.le
    rw [pow_zero,mul_one,lxq] at hh
    rw [axq] at hl hh
    nlinarith
  have hft := fun q (hq : q ∈ T) => hf q (hT hq)
  have hfu := fun q (hq : q ∈ U) => hf q (hU hq)
  rcases (show (j=1 ∧ i=2) ∨ (j=2 ∧ i=1) ∨ (j=3 ∧ i=0) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact forbid_mixed ht hu hft hfu hdis five hdt heu rt.2 ru.2
  · exact forbid_mixed hu ht hfu hft hdis.symm (by simpa [mul_comm] using five) heu hdt ru.2 rt.2
  · apply neutral_group_impossible hk hu (by simpa [B] using heu)
    simpa [B,X,lxq] using ru.1

theorem no_large_odd_double_test {a k : ℕ} {S : Finset ℕ} (hk : 12 ≤ k)
    (hp : ∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2^a*625)
    (hb : sigmaU (2^a*625) * shifted S = 2*(2^a*625)*primesProduct S) :
    a ≠ 2*(2*k+1) := by
  rintro rfl
  obtain ⟨R,hR,hf,hbR,hm⟩ := remove_forced (by omega) hp hb
  exact exclude_large hk hR hf hbR hm

theorem no_large_odd_double {n k : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (hc : core n=625)
    (hk : 12 ≤ k) : n.factorization 2 ≠ 2*(2*k+1) := by
  obtain ⟨_,_,S,_,hp,hb,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2^n.factorization 2 * core n at hp
  change sigmaU (2^n.factorization 2 * core n) * shifted S =
    2*(2^n.factorization 2 * core n)*primesProduct S at hb
  rw [hc] at hp hb
  exact no_large_odd_double_test hk hp hb

/- Exact forced-prime contradictions for the primes below 25. -/

def routeRejects : List ℕ → ℕ → ℕ → List ℕ → Bool
  | [], _, _, _ => false
  | p::steps, u, v, banned =>
    let g := u.gcd v
    let s := u/g
    let t := v/g
    decide (0 < u ∧ p.Prime ∧ p ∣ s ∧ ¬ p ∣ t) &&
      (if p ∈ banned then true else routeRejects steps (s*(1+p)) (t*p) (p::banned))

theorem routeRejects_sound {steps banned : List ℕ} {u v : ℕ} {S : Finset ℕ}
    (hp : ∀ q ∈ S, q.Prime) (hf : ∀ q ∈ S, q ∉ banned)
    (hb : u*shifted S = v*primesProduct S) (hr : routeRejects steps u v banned = true) : False := by
  induction steps generalizing S u v banned with
  | nil => simp [routeRejects] at hr
  | cons p steps ih =>
    let g := u.gcd v
    let s := u/g
    let t := v/g
    obtain ⟨hcheck,hnext⟩ := Bool.and_eq_true_iff.mp hr
    obtain ⟨hpos,hprim,hps,hpt⟩ := of_decide_eq_true hcheck
    have hg : 0 < g := Nat.gcd_pos_of_pos_left v hpos
    have hbs : s*shifted S = t*primesProduct S := by
      apply Nat.eq_of_mul_eq_mul_left hg
      have hgu : g*s=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hgv : g*t=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      rwa [← mul_assoc,hgu,← mul_assoc,hgv]
    have hm := forced_member hprim hpt hp hbs (dvd_mul_of_dvd_left hps _)
    by_cases hforb : p ∈ banned
    · exact hf p hm hforb
    · have hrem : (s*(1+p))*shifted (S.erase p) = (t*p)*primesProduct (S.erase p) := by
        rw [mul_assoc,mul_assoc,show (1+p)*shifted (S.erase p) = shifted S from
          Finset.mul_prod_erase S (fun q => 1+q) hm,
          show p*primesProduct (S.erase p) = primesProduct S from Finset.mul_prod_erase S id hm]
        exact hbs
      exact ih (fun q hq => hp q (Finset.mem_of_mem_erase hq)) (fun q hq => by
        simp only [List.mem_cons, not_or]; exact ⟨(Finset.mem_erase.mp hq).1, hf q (Finset.mem_of_mem_erase hq)⟩)
        hrem (if_neg hforb ▸ hnext)

def smallRoute : ℕ → List ℕ
  | 2 => [17,3,3]
  | 3 => [13,7,313,157,79,2]
  | 5 => [41,3,7,313,157,79,2]
  | 7 => [29,3,113,3]
  | 11 => [313,157,79,397,199,2113,7,151,19,5]
  | 13 => [53,3,3]
  | 17 => [137,3,23,3]
  | 19 => [229,23,3,313,157,79,457,229]
  | 23 => [277,139,7,313,157,79,1013,3,13,7]
  | _ => []

set_option maxRecDepth 8192 in
theorem small_routes : ∀ l ∈ Finset.Icc 2 24, Nat.Prime l →
    routeRejects (smallRoute l) (626*(2^(2*l)+1)) (2*(2^(2*l)*625)) [2,5] = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem no_prime_double_test {a l : ℕ} {S : Finset ℕ} (hl : l.Prime)
    (hp : ∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2^a*625)
    (hb : sigmaU (2^a*625) * shifted S = 2*(2^a*625)*primesProduct S) : a ≠ 2*l := by
  by_cases hlarge : 25 ≤ l
  · obtain ⟨k,hk⟩ := hl.odd_of_ne_two (by omega)
    have he : l = 2*k+1 := by omega
    exact he ▸ no_large_odd_double_test (k:=k) (by omega) hp hb
  rintro rfl
  have hlow := hl.two_le
  have hroute := small_routes l (Finset.mem_Icc.mpr ⟨hlow,by omega⟩) hl
  rw [sigma_625 (by omega)] at hb
  apply routeRejects_sound (fun q hq => (hp q hq).1) _ hb hroute
  intro q hq
  have h2 : 2 ∣ 2^(2*l)*625 := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  have h5 : 5 ∣ 2^(2*l)*625 := dvd_mul_of_dvd_right (by decide : 5 ∣ 625) _
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨fun e => (hp q hq).2 (e ▸ h2),fun e => (hp q hq).2 (e ▸ h5)⟩

theorem no_prime_double {n l : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (hc : core n=625)
    (hl : l.Prime) : n.factorization 2 ≠ 2*l := by
  obtain ⟨_,_,S,_,hp,hb,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2^n.factorization 2 * core n at hp
  change sigmaU (2^n.factorization 2 * core n) * shifted S =
    2*(2^n.factorization 2 * core n)*primesProduct S at hb
  rw [hc] at hp hb
  exact no_prime_double_test hl hp hb

end Erdos1052.Core625
