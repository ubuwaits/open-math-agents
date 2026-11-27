import OMAReductions.R_Erdos1052_erdos_1052_R2
import Mathlib.NumberTheory.LucasLehmer

/-!
# Prime factors of the odd part of the exponent in Erdős 1052

Write n = 2^a c s for a unitary perfect number with repeated odd core c and
squarefree simple support s. For a = h b with h even, h ≥ 16, and b odd, let
C be the odd part of the unitary divisor sum of c, and let K count the prime
factors of c / gcd(c,C(2^h + 1)), including multiplicities.

In the namespace Erdos1052.OddExponent, three_bound_of_perfect proves
v₃(b) ≤ K. The theorem omega_bound_of_perfect bounds the total number of
prime factors of b using two auxiliary primes. The theorem uniform_omega_bound
gives the coarser explicit bound h ((h + 2)(K + 1) + 1) without auxiliary
parameters. The theorem finite_smooth_exponents gives finiteness for any
prescribed upper bound on the prime divisors of b at fixed h and c.
The final theorem excludes every exponent at c = 65537^(16(2k+1)).

The general finiteness question remains open. This file uses the accepted R2
reduction and contains the required support decomposition and estimates.
-/

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

theorem no_prime_chain_before {k : ℕ} (hk : 12 ≤ k) :
    ¬ ∀ i : ℕ, 1 ≤ i → i ≤ k → (chain k i).Prime := by
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
      have hdiv : 13 ∣ chain k 5 := (ZMod.natCast_eq_zero_iff _ _).1 (by
        rw [chain_cast, hx]
        decide)
      have heq := ((hall _ (by omega) (by omega)).dvd_iff_eq (by decide : 13 ≠ 1)).1 hdiv
      have := hlarge 5 (by omega)
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
    have hile : i ≤ k := by dsimp [i]; omega
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

theorem no_prime_chain {k : ℕ} (hk : 12 ≤ k) :
    ¬ ∀ i : ℕ, 1 ≤ i → i ≤ k+1 → (chain k i).Prime :=
  fun h => no_prime_chain_before hk (fun i hi hj => h i hi (by omega))

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

theorem excludes_chain_support {k t : ℕ} (hk : 12 ≤ k) (hkt : k ≤ t)
    {T : Finset ℕ} (hp : primeSupport T) (hbal : chain k t * demands T = primesProduct T)
    (hlarge : ∀ q ∈ T, 2^k ≤ q) (hasq : chain k t < (2*(2^k-1)+1)^2) : False := by
  let X := 2^k
  let Y := X-1
  let A := chain k t
  have hX : 2 ≤ X := Nat.pow_le_pow_right (n:=2) (by decide) (show 1 ≤ k by omega)
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have ha1 : 1 < A := by
    change 1 < 1+2^t*Y
    exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.two_pow_pos _) hY)
  change A * demands T = primesProduct T at hbal
  change A < (2*Y+1)^2 at hasq
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
    have := hlarge r hr
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
  have hchain (i : ℕ) (hi : i ≤ t) : 1 ≤ i → chain k i ∈ T := by
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
        change 1 + 2^i * Y ≤ 1 + 2^t * Y
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
  exact no_prime_chain_before hk (fun i hi hj => (hp _ (hchain i (hj.trans hkt) hi)).1)

end Erdos1052.Core625

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

end Erdos1052.Core625

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

end Erdos1052.Core625

namespace Erdos1052.OddExponent

open Erdos1052.Core625 Erdos1052.CoreBounds

/-- A factor with no remaining core divisor has exactly the displayed 2-adic size. -/
theorem neutral_size {T : Finset ℕ} (hp : primeSupport T) {s w A : ℕ}
    (hs : 2 ≤ s) (hw : 2*s ≤ w)
    (hA : A*(2^s+1) = 2^s*2^w+1)
    (hd : A*demands T = primesProduct T) (hb : abundancy T < 2) :
    (A:ℚ)*abundancy T = 2^w ∧ (∀ q ∈ T, 2^s < q) := by
  let Y : ℚ := 2^s
  let L : ℚ := 2^w
  have hY : (4:ℚ) ≤ Y := calc
    (4:ℚ) = 2^2 := by norm_num
    _ ≤ Y := pow_le_pow_right₀ (by norm_num) hs
  have hL : Y^2 ≤ L := by
    dsimp [Y,L]
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ha : (A:ℚ)*(Y+1) = Y*L+1 := by dsimp [Y,L]; exact_mod_cast hA
  have large : 1 < L := by nlinarith [sq_nonneg (Y-4)]
  have hlt : (A:ℚ) < L := by
    apply (lt_of_mul_lt_mul_right (a:=Y+1) _ (by linarith))
    nlinarith
  have hgt : L < 2*(A:ℚ) := by
    apply (lt_of_mul_lt_mul_right (a:=Y+1) _ (by linarith))
    nlinarith [mul_nonneg (show 0 ≤ Y-1 by linarith) (show 0 ≤ L by linarith)]
  have eq : (A:ℚ)*abundancy T = 2^twoCount T := by
    simpa using group_ratio hp (j:=0) (by simpa using hd)
  have hlow := mul_le_mul_of_nonneg_left
    (Finset.one_le_prod (s:=T) fun q _ => gain_one_le q) (show 0 ≤ (A:ℚ) by positivity)
  have hhigh := mul_lt_mul_of_pos_left hb (show 0 < (A:ℚ) by linarith)
  have he : twoCount T = w := by
    rcases lt_trichotomy (twoCount T) w with h|h|h
    · have hx : (2:ℚ)^(twoCount T+1) ≤ L := pow_le_pow_right₀ (by norm_num) h
      rw [pow_succ] at hx
      linarith
    · exact h
    · have hx : (2:ℚ)^(w+1) ≤ 2^twoCount T := pow_le_pow_right₀ (by norm_num) h
      rw [pow_succ] at hx
      change L*2 ≤ _ at hx
      linarith
  rw [he] at eq
  refine ⟨eq,?_⟩
  intro q hq
  by_contra! hn
  have hnq : (q:ℚ) ≤ Y := by dsimp [Y]; exact_mod_cast hn
  have qpos : 0 < (q:ℚ) := by exact_mod_cast (hp q hq).1.pos
  have hg := mul_le_mul_of_nonneg_left (gain_le_total hq) (show 0 ≤ (A:ℚ) by positivity)
  rw [eq] at hg
  change (A:ℚ)*(1+1/(q:ℚ)) ≤ L at hg
  have hg' := (mul_le_mul_iff_of_pos_right qpos).mpr hg
  field_simp at hg'
  nlinarith [mul_nonneg (sub_nonneg.mpr hnq) (sub_nonneg.mpr hlt.le)]

theorem neutral_root_tail {T : Finset ℕ} (hp : primeSupport T) {s : ℕ}
    (hs : 13 ≤ s) (heven : Even s) (hcomp : ¬(2^(s+1)-1 : ℕ).Prime)
    (hb : ∀ q ∈ T, 2^s < q) (hd : demands T ∣ primesProduct T) :
    abundancy T ≤ mersenneBound (s+3) := by
  let R := T.filter (fun q => demand q = 1)
  let t := fun q : ℕ => (1+q).factorization 2
  have hR (q : ℕ) (hq : q ∈ R) : q ∈ T ∧ demand q = 1 := Finset.mem_filter.mp hq
  have hpow (q : ℕ) (hq : q ∈ R) : 2 ^ t q = 1+q := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
    change 2 ^ t q * demand q = 1+q at h
    simpa only [(hR q hq).2,mul_one] using h
  have hinj : Set.InjOn t R := by
    intro q hq p hp he
    have h1 := hpow q hq
    have h2 := hpow p hp
    rw [show t q = t p from he] at h1
    omega
  have hmin (q : ℕ) (hq : q ∈ R) : s+3 ≤ t q := by
    have hv := hpow q hq
    have hval : 2^t q - 1 = q := by omega
    have hq' := (hp q (hR q hq).1).1
    have ht : s < t q := by
      by_contra! hn
      have := Nat.pow_le_pow_right (n:=2) (by decide) hn
      have := hb q (hR q hq).1
      omega
    have h1 : t q ≠ s+1 := by
      intro he
      rw [he] at hval
      exact hcomp (hval ▸ hq')
    have hprime : (t q).Prime := Nat.Prime.of_mersenne (by simpa [mersenne,hval] using hq')
    have hodd := hprime.odd_of_ne_two (by omega)
    obtain ⟨j,hj⟩ := hodd
    obtain ⟨k,hk⟩ := heven
    omega
  have hid (q : ℕ) (hq : q ∈ R) : pathBound q = mersenneFactor (t q) := by
    have hv : (2:ℚ) ^ t q = 1+q := by exact_mod_cast hpow q hq
    unfold pathBound mersenneFactor
    rw [hv]
    congr 1 <;> ring
  have hweight := compatible_tail_bound T demand (x:=1) (D:=1) (by decide) (by decide)
    (fun q hq => ⟨(hp q hq).1,(hp q hq).1.one_lt,Nat.ordCompl_pos 2 (by omega),
      twice_oddPart_shift_le ((hp q hq).1.odd_of_ne_two (hp q hq).2)⟩) (by simpa using hd)
  have hr : abundancy T ≤ ∏ q ∈ R, pathBound q := by
    simpa [R, Finset.prod_filter, abundancy, gain] using hweight
  apply hr.trans
  have heq : (∏ q ∈ R, pathBound q) = ∏ j ∈ R.image t, mersenneFactor j := by
    rw [Finset.prod_image hinj]
    exact Finset.prod_congr rfl hid
  rw [heq]
  apply large_mersenne_product (R.image t) (by omega)
  intro j hj
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
  exact hmin q hq

/-- Any such quotient requires at least one prime factor of the repeated core. -/
theorem nonneutral_block {T : Finset ℕ} (hp : primeSupport T) {A D s w : ℕ}
    (hs : 16 ≤ s) (heven : Even s) (hcomp : ¬(2^(s+1)-1 : ℕ).Prime)
    (hw : 2*s ≤ w) (hA : A*(2^s+1) = 2^s*2^w+1)
    (hd : A*demands T = D*primesProduct T) (hb : abundancy T < 2) : D ≠ 1 := by
  rintro rfl
  rw [one_mul] at hd
  obtain ⟨heq,hq⟩ := neutral_size hp (by omega) hw hA hd hb
  have ht := neutral_root_tail hp (by omega) heven hcomp hq
    (show demands T ∣ primesProduct T from hd ▸ dvd_mul_left _ _)
  let Y : ℚ := 2^s
  let L : ℚ := 2^w
  have hy : (4:ℚ) ≤ Y := calc
    (4:ℚ) = 2^2 := by norm_num
    _ ≤ Y := pow_le_pow_right₀ (by norm_num) (show 2 ≤ s by omega)
  have hl : Y^2 ≤ L := by
    dsimp [Y,L]; rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ha : (A:ℚ)*(Y+1) = Y*L+1 := by dsimp [Y,L]; exact_mod_cast hA
  change (A:ℚ)*abundancy T = L at heq
  unfold mersenneBound at ht
  rw [pow_add] at ht
  change abundancy T ≤ Y*8/(Y*8-4) at ht
  have hprod := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ (show 0<Y*8-4 by linarith)).mp ht) (show 0 ≤ (A:ℚ) by positivity)
  have hlin : L*(2*Y-1) ≤ (A:ℚ)*2*Y := by nlinarith only [hprod, heq, congrArg (fun x => x*Y) heq]
  have hh := mul_le_mul_of_nonneg_right hlin (show 0 ≤ Y+1 by linarith)
  nlinarith [congrArg (fun x => x*Y) ha, mul_nonneg (show 0≤Y-1 by linarith) (sub_nonneg.mpr hl),
    mul_nonneg (show 0 ≤ Y-3 by linarith) (sq_nonneg Y), sq_nonneg (Y-2)]

/-- A cubic quotient must use a core divisor even when the first Mersenne candidate is prime. -/
theorem nonneutral_cubic {T : Finset ℕ} (hp : primeSupport T) {s D : ℕ}
    (hs : 16 ≤ s) (hd : chain s s * demands T = D * primesProduct T)
    (hb : abundancy T < 2) : D ≠ 1 := by
  rintro rfl
  rw [one_mul] at hd
  let X := 2^s
  let Z := X-1
  have hx : 2 ≤ X := Nat.pow_le_pow_right (n:=2) (by decide) (show 1 ≤ s by omega)
  have hz : X = Z+1 := by dsimp [Z]; omega
  have ha : chain s s * (2^s+1) = 2^s*2^(2*s)+1 := by
    rw [show 2^(2*s)=(2^s)^2 by rw [Nat.mul_comm 2 s,pow_mul]]
    change (1+X*Z)*(X+1)=X*X^2+1
    rw [hz]; ring
  obtain ⟨_,hgt⟩ := neutral_size hp (by omega) (le_refl _) ha hd hb
  apply excludes_chain_support (k:=s) (t:=s) (by omega) (le_refl _) hp hd (fun q h => (hgt q h).le)
  change 1+X*Z < (2*Z+1)^2
  rw [hz]
  nlinarith [show 1 ≤ Z by omega]

def requiresCore (A : ℕ) : Prop := ∀ (T : Finset ℕ), primeSupport T →
  ∀ D : ℕ, A*demands T = D*primesProduct T → abundancy T < 2 → D ≠ 1

/-- Charge each required factor separately using the decreasing-prime partition.
    The common divisor g of the base factor and the core remains available at every split. -/
theorem count_required (As : List ℕ) {S : Finset ℕ} {C D g : ℕ}
    (hAs : ∀ A ∈ As, requiresCore A) (hp : primeSupport S) (hb : abundancy S < 2)
    (hD : D ≠ 0) (hg : g ∣ C) (hcop : ∀ q ∈ S, ¬ q ∣ g)
    (hd : As.prod*C*demands S = D*primesProduct S) :
    As.length + g.primeFactorsList.length ≤ D.primeFactorsList.length := by
  induction As generalizing S D with
  | nil =>
    simp only [List.prod_nil, one_mul] at hd
    have hh : g ∣ D*primesProduct S := hd ▸ dvd_mul_of_dvd_left hg _
    have hc : g.Coprime (primesProduct S) := Nat.coprime_prod_right_iff.mpr
      (fun q hq => ((hp q hq).1.coprime_iff_not_dvd.mpr (hcop q hq)).symm)
    simpa using (Nat.primeFactorsList_sublist_of_dvd (hc.dvd_of_dvd_mul_right hh) hD).length_le
  | cons A As ih =>
    have hsplit := split_support S hp
      (show A*(As.prod*C)*demands S = D*primesProduct S by
        simpa only [List.prod_cons, mul_assoc] using hd)
    obtain ⟨T,U,d,e,hdis,hunion,hde,ht,hu⟩ := hsplit
    have hT : T ⊆ S := hunion ▸ Finset.subset_union_left
    have hU : U ⊆ S := hunion ▸ Finset.subset_union_right
    have mag {V : Finset ℕ} (hs : V ⊆ S) : abundancy V < 2 :=
      (Finset.prod_le_prod_of_subset_of_one_le hs (fun q _ => zero_le_one.trans (gain_one_le q))
        (fun q _ _ => gain_one_le q)).trans_lt hb
    have hd1 := hAs A List.mem_cons_self T (fun q h => hp q (hT h)) d ht (mag hT)
    have hd0 : d ≠ 0 := fun H => hD (by simpa [H] using hde.symm)
    have he0 : e ≠ 0 := fun H => hD (by simpa [H] using hde.symm)
    have hlen : 0 < d.primeFactorsList.length := List.length_pos_iff.mpr
      ((Nat.primeFactorsList_ne_nil d).mpr (by omega))
    have hrec := ih (fun t ht => hAs t (List.mem_cons_of_mem A ht))
      (fun q h => hp q (hU h)) (mag hU) he0 (fun q h => hcop q (hU h)) hu
    have hsum := (Nat.perm_primeFactorsList_mul hd0 he0).length_eq
    simp only [List.length_append,hde] at hsum
    simp only [List.length_cons]
    omega

theorem cubic_identity (s : ℕ) : chain s s * (2^s+1) = 2^(s*3)+1 := by
  let X := 2^s
  let Z := X-1
  have hx : 0 < X := Nat.two_pow_pos _
  have hz : X = Z+1 := by dsimp [Z]; omega
  rw [pow_mul]
  change (1+X*Z)*(X+1)=X^3+1
  rw [hz]; ring

def cubicLayers (s : ℕ) : ℕ → List ℕ
  | 0 => []
  | i+1 => chain (s*3^i) (s*3^i) :: cubicLayers s i

theorem cubic_product (s t : ℕ) : (cubicLayers s t).prod*(2^s+1) = 2^(s*3^t)+1 := by
  induction t with
  | zero => simp [cubicLayers]
  | succ i ih =>
    rw [cubicLayers,List.prod_cons,mul_assoc,ih,cubic_identity,pow_succ,← Nat.mul_assoc]

theorem cubic_length (s t : ℕ) : (cubicLayers s t).length = t := by
  induction t with
  | zero => rfl
  | succ i ih => simp [cubicLayers,ih]

theorem cubic_required {s : ℕ} (hs : 16 ≤ s) (t : ℕ) : ∀ A ∈ cubicLayers s t, requiresCore A := by
  induction t with
  | zero => simp [cubicLayers]
  | succ i ih =>
    intro A hA
    rcases List.mem_cons.mp hA with rfl | ht
    · intro T hT D hd hb
      exact nonneutral_cubic hT (hs.trans (Nat.le_mul_of_pos_right _ (by positivity))) hd hb
    · exact ih _ ht

theorem three_exponent_bound {s t J C c : ℕ} (hs : 16 ≤ s) (hj : Odd J)
    {S : Finset ℕ} (hp : primeSupport S) (hb : abundancy S < 2)
    (hc : c ≠ 0) (hout : ∀ q ∈ S, ¬q ∣ c)
    (hd : C*(2^(s*3^t*J)+1)*demands S = c*primesProduct S) :
    t + (c.gcd (C*(2^s+1))).primeFactorsList.length ≤ c.primeFactorsList.length := by
  have hf : 2^(s*3^t)+1 ∣ 2^(s*3^t*J)+1 := by
    rw [pow_mul (2:ℕ) (s*3^t) J]
    simpa only [one_pow] using hj.nat_add_dvd_pow_add_pow (2^(s*3^t)) 1
  obtain ⟨z,hz⟩ := hf
  let g := c.gcd (C*(2^s+1))
  have htag : g ∣ (C*(2^s+1))*z := dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  have hfull : (cubicLayers s t).prod * (C*(2^s+1)*z) * demands S = c*primesProduct S := by
    calc _ = C * (((cubicLayers s t).prod*(2^s+1))*z)*demands S := by ac_rfl
      _ = _ := by rw [cubic_product,← hz]; exact hd
  have h := count_required (cubicLayers s t) (cubic_required hs t) hp hb hc htag
    (fun q hq hdiv => hout q hq (hdiv.trans (Nat.gcd_dvd_left _ _))) hfull
  simpa only [cubic_length] using h

theorem sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) (hc0 : c ≠ 0) :
    sigmaU (2^a*c) = (2^a+1)*sigmaU c := by
  have hb : (2:ℕ)^a ≠ 0 := pow_ne_zero _ (by decide)
  have h2c : ¬2 ∣ c := by obtain ⟨i,hi⟩ := hc; omega
  have h2 : 2 ∉ c.primeFactors := fun h => h2c (Nat.dvd_of_mem_primeFactors h)
  have hfac (p : ℕ) : (2^a*c).factorization p =
      (if 2=p then a else 0) + c.factorization p := by
    rw [Nat.factorization_mul hb hc0,Nat.prime_two.factorization_pow]
    simp [Finsupp.single_apply,eq_comm]
  have h2val : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2c
  unfold sigmaU
  rw [Nat.primeFactors_mul hb hc0,Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
    Finset.singleton_union,Finset.prod_insert h2,hfac]
  simp only [if_true,h2val,add_zero,Nat.add_comm 1 (2^a)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have he : 2 ≠ p := fun e => h2 (e ▸ hp)
  rw [hfac, if_neg he, zero_add]

theorem normalize {a c : ℕ} (ha : 0 < a) (hc : Odd c) (hc0 : c ≠ 0)
    {S : Finset ℕ} (hp : ∀ q ∈ S, q.Prime ∧ ¬q ∣ 2^a*c)
    (hd : sigmaU (2^a*c)*shifted S = 2*(2^a*c)*primesProduct S) :
    primeSupport S ∧ (∀ q ∈ S, ¬ q ∣ c) ∧ abundancy S < 2 ∧
    oddPart (sigmaU c)*(2^a+1)*demands S = c*primesProduct S := by
  have h2d : 2 ∣ 2^a*c := dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') _
  have hs : primeSupport S := fun q hq =>
    ⟨(hp q hq).1, fun he => (hp q hq).2 (he ▸ h2d)⟩
  have hcop (q : ℕ) (hq : q ∈ S) (hu : q ∣ c) : False := (hp q hq).2 (dvd_mul_of_dvd_right hu _)
  rw [sigma_power_two_times ha hc hc0] at hd
  refine ⟨hs,hcop,?_,?_⟩
  · have hsig : c ≤ sigmaU c := calc
      c = _ := (OMA.R_Erdos1052_erdos_1052_R2.prod_primeFactors_pow_self hc0).symm
      _ ≤ _ := Finset.prod_le_prod' (fun q _ => Nat.le_add_left _ _)
    have hcQ : (0:ℚ) < c := by exact_mod_cast (Nat.pos_of_ne_zero hc0)
    have hsQ : (c:ℚ) ≤ sigmaU c := by exact_mod_cast hsig
    have hprod : 0 < (primesProduct S:ℚ) := by exact_mod_cast (Finset.prod_pos fun q hq => (hs q hq).1.pos)
    have hh : ((2:ℚ)^a+1)*(sigmaU c:ℚ)*(shifted S:ℚ) =
        2*(2^a*(c:ℚ))*(primesProduct S:ℚ) := by exact_mod_cast hd
    rw [← abundancy_cross hs,← mul_assoc] at hh
    have ht := mul_right_cancel₀ hprod.ne' hh
    by_contra! hn
    have h1 := mul_le_mul_of_nonneg_left hn (show (0:ℚ) ≤ (2^a+1)*(sigmaU c:ℚ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsQ (show (0:ℚ) ≤ 2^a by positivity)
    linarith
  · have mult (u v : ℕ) : oddPart (u*v) = oddPart u * oddPart v := Nat.ordCompl_mul _ _ _
    have strip (j u : ℕ) : oddPart (2^j*u)=oddPart u := Nat.ordCompl_self_pow_mul _ _ Nat.prime_two
    have hr : 2*(2^a*c)*primesProduct S = 2^(a+1)*(c*primesProduct S) := by rw [pow_succ]; ac_rfl
    have H := congrArg oddPart (hd.trans hr)
    have hM : ¬2 ∣ 2^a+1 := by have := dvd_pow_self 2 ha.ne'; omega
    have hm : oddPart (2^a+1)=2^a+1 := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (.inr hM)
    have hodd : oddPart c=c := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr
      (.inr (by obtain ⟨i,hi⟩ := hc; omega))
    have hpr : oddPart (primesProduct S) = primesProduct S := by
      apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr
      right
      intro h
      obtain ⟨q,hq,hq2⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp h
      exact (hs q hq).2 (((hs q hq).1.dvd_iff_eq (by decide : 2 ≠ 1)).mp hq2)
    rw [mult,mult (2^a+1),strip,mult c,hm,hodd,hpr] at H
    have hop : oddPart (shifted S)=demands S := oddPart_prod S _
    simpa only [hop,mul_comm (2^a+1) (oddPart (sigmaU c))] using H

theorem three_bound_of_perfect {n s t J : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hs : 16 ≤ s) (hj : Odd J) (he : n.factorization 2 = s*3^t*J) :
    t + ((core n).gcd (oddPart (sigmaU (core n))*(2^s+1))).primeFactorsList.length ≤
      (core n).primeFactorsList.length := by
  obtain ⟨hc,_,S,_,hp,hb,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change Odd (core n) at hc
  change ∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2^n.factorization 2*core n at hp
  change sigmaU (2^n.factorization 2*core n)*shifted S = 2*(2^n.factorization 2*core n)*primesProduct S at hb
  have hj0 : 0 < J := by obtain ⟨i,hi⟩ := hj; omega
  have hc0 : core n ≠ 0 := by obtain ⟨i,hi⟩ := hc; omega
  have ha : 0 < n.factorization 2 := by rw [he]; positivity
  obtain ⟨hS,hout,hB,hd⟩ := normalize ha hc hc0 hp hb
  rw [he] at hd
  exact three_exponent_bound hs hj hS hB hc0 hout hd

private theorem block_requires {s f : ℕ} (hs : 16 ≤ s) (he : Even s)
    (hn : ¬(s+1).Prime) (hf : 3 ≤ f) (ho : Odd f) :
    ∃ A, requiresCore A ∧ A*(2^s+1) = 2^(s*f)+1 := by
  have hd : 2^s+1 ∣ 2^(s*f)+1 := by
    rw [pow_mul]
    simpa only [one_pow] using ho.nat_add_dvd_pow_add_pow (2^s) 1
  obtain ⟨A,hA⟩ := hd
  have ha : A*(2^s+1) = 2^(s*f)+1 := by rw [hA,mul_comm]
  refine ⟨A,?_,ha⟩
  intro T hT D hD hB
  apply nonneutral_block hT hs he (fun h => hn (Nat.Prime.of_mersenne h)) (w:=s*(f-1)) _ _ hD hB
  · nlinarith [Nat.mul_le_mul_left s (show 2 ≤ f-1 by omega)]
  · rw [ha,← pow_add]
    congr 2
    obtain ⟨z,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show f ≠ 0 by omega)
    simp [Nat.mul_succ,Nat.add_comm]

private theorem product_layers (p : ℕ) (hp : 2 ≤ p) (fs : List ℕ) (z : ℕ)
    (hfs : ∀ f ∈ fs, 3 ≤ f ∧ Odd f ∧ Nat.ModEq p f 1)
    (hz : 3 ≤ z) (hoz : Odd z) {s : ℕ} (hs : 16 ≤ s) (he : Even s)
    (hd : p ∣ s+1) (hlt : p < s+1) :
    ∃ As : List ℕ, As.length = fs.length + 1 ∧ (∀ A ∈ As, requiresCore A) ∧
      As.prod*(2^s+1) = 2^(s*fs.prod*z)+1 := by
  induction fs generalizing s with
  | nil =>
    obtain ⟨A,hA,ha⟩ := block_requires hs he (Nat.not_prime_of_dvd_of_lt hd hp hlt) hz hoz
    exact ⟨[A],by simp,by simpa using hA,by simpa using ha⟩
  | cons f fs ih =>
    obtain ⟨hf,ho,hm⟩ := hfs f List.mem_cons_self
    have hs' : s ≤ s*f := Nat.le_mul_of_pos_right s (by omega)
    have hm' : Nat.ModEq p (s*f+1) (s+1) := by simpa using (hm.mul_left s).add_right 1
    have hd' := Nat.modEq_zero_iff_dvd.mp (hm'.trans (Nat.modEq_zero_iff_dvd.mpr hd))
    obtain ⟨A,hA,ha⟩ := block_requires hs he (Nat.not_prime_of_dvd_of_lt hd hp hlt) hf ho
    obtain ⟨As,hlen,hAs,heq⟩ := ih (fun t ht => hfs t (List.mem_cons_of_mem f ht))
      (hs.trans hs') (he.mul_right _) hd' (by omega)
    refine ⟨A :: As,by simp [hlen],?_,?_⟩
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      exacts [hA,hAs B hB]
    · rw [List.prod_cons,List.prod_cons,show A*As.prod*(2^s+1)=As.prod*(A*(2^s+1)) by ac_rfl,ha,heq]
      rw [Nat.mul_assoc s f]

private theorem charge_congr_blocks {h u J p z C c : ℕ} (fs : List ℕ)
    (hfs : ∀ f ∈ fs, 3 ≤ f ∧ Odd f ∧ Nat.ModEq p f 1)
    (hz : 3 ≤ z) (hoz : Odd z) (hu : Odd u) (hJ : Odd J) (hp : 2 ≤ p)
    (hs : 16 ≤ h*u) (he : Even (h*u)) (hd : p ∣ h*u+1) (hlt : p < h*u+1)
    {S : Finset ℕ} (hS : primeSupport S) (hB : abundancy S < 2)
    (hc : c ≠ 0) (hout : ∀ q ∈ S, ¬ q ∣ c)
    (hbal : C*(2^(h*u*fs.prod*z*J)+1)*demands S = c*primesProduct S) :
    fs.length + 1 + (c.gcd (C*(2^h+1))).primeFactorsList.length ≤ c.primeFactorsList.length := by
  obtain ⟨As,hlen,hA,ha⟩ := product_layers p hp fs z hfs hz hoz hs he hd hlt
  have expDvd (a b : ℕ) (hb : Odd b) : 2^a+1 ∣ 2^(a*b)+1 := by
    rw [pow_mul]; simpa only [one_pow] using hb.nat_add_dvd_pow_add_pow (2^a) 1
  obtain ⟨x,hx⟩ := expDvd (h*u*fs.prod*z) J hJ
  let g := c.gcd (C*(2^h+1))
  have hg : g ∣ C*(2^(h*u)+1)*x := dvd_mul_of_dvd_left
    ((Nat.gcd_dvd_right _ _).trans (Nat.mul_dvd_mul_left C (expDvd h u hu))) _
  have eq : As.prod*(C*(2^(h*u)+1)*x)*demands S = c*primesProduct S := by
    calc _ = C*((As.prod*(2^(h*u)+1))*x)*demands S := by ac_rfl
         _ = _ := by rw [ha,← hx]; exact hbal
  simpa only [hlen] using count_required As hA hS hB hc hg
    (fun q hq hdiv => hout q hq (hdiv.trans (Nat.gcd_dvd_left _ _))) eq

private theorem odd_list_prod (L : List ℕ) (h : ∀ f ∈ L, Odd f) : Odd L.prod := by
  induction L with
  | nil => simp
  | cons f L ih =>
    exact (h f List.mem_cons_self).mul (ih (fun t ht => h t (List.mem_cons_of_mem f ht)))

private theorem product_large {L : List ℕ} (hn : L ≠ []) (h : ∀ f ∈ L, 3 ≤ f) : 3 ≤ L.prod := by
  rcases L with _ | ⟨x,X⟩
  · contradiction
  · have hh := List.prod_pos (s:=X) (fun q hq => (by have := h q (List.mem_cons_of_mem x hq); omega))
    exact (h x List.mem_cons_self).trans (Nat.le_mul_of_pos_right _ hh)

private theorem extract_block {p : ℕ} (hp : p.Prime) (L : List ℕ)
    (hL : ∀ f ∈ L, 3 ≤ f ∧ Odd f ∧ ¬ p ∣ f) (hlen : p-1 ≤ L.length) :
    ∃ (f : ℕ) (R : List ℕ), 3 ≤ f ∧ Odd f ∧ Nat.ModEq p f 1 ∧
      (∀ t ∈ R, t ∈ L) ∧ L.length ≤ R.length+(p-1) ∧ f*R.prod=L.prod := by
  let pre (i : ℕ) := (L.take i).prod
  have copList (X : List ℕ) (hX : ∀ x ∈ X, ¬p ∣ x) : p.Coprime X.prod := by
    induction X with
    | nil => simp
    | cons x X ih =>
      simpa only [List.prod_cons,Nat.coprime_mul_iff_right] using
        And.intro (hp.coprime_iff_not_dvd.mpr (hX x List.mem_cons_self))
          (ih (fun y hy => hX y (List.mem_cons_of_mem x hy)))
  have cop (i : ℕ) : p.Coprime (pre i) := copList (L.take i)
    (fun x hx => (hL x (List.mem_of_mem_take hx)).2.2)
  have p2 := hp.two_le
  have maps (i : ℕ) (_ : i ∈ Finset.range p) : pre i % p ∈ Finset.Ico 1 p := by
    have ne : pre i % p ≠ 0 := fun h => (hp.coprime_iff_not_dvd.mp (cop i)) (Nat.dvd_of_mod_eq_zero h)
    exact Finset.mem_Ico.mpr ⟨by omega,Nat.mod_lt _ hp.pos⟩
  obtain ⟨i,hi,j,hj,hne,eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s:=Finset.range p) (t:=Finset.Ico 1 p) (by simp; omega) maps
  have pick : ∃ i j : ℕ, i < j ∧ j < p ∧ Nat.ModEq p (pre i) (pre j) := by
    rcases lt_or_gt_of_ne hne with h|h
    exacts [⟨i,j,h,Finset.mem_range.mp hj,eq⟩,⟨j,i,h,Finset.mem_range.mp hi,eq.symm⟩]
  obtain ⟨i,j,hij,hjp,hm⟩ := pick
  let T := (L.take j).drop i
  let R := L.take i ++ L.drop j
  have hjL : j ≤ L.length := by omega
  have hiL : i ≤ L.length := by omega
  have dec : pre i*T.prod=pre j := by
    have hh := (L.take j).prod_take_mul_prod_drop i
    simpa [pre,T,List.take_take,Nat.min_eq_left hij.le] using hh
  have hsub (x : ℕ) (hx : x ∈ T) : x ∈ L := List.mem_of_mem_take (List.mem_of_mem_drop hx)
  have hneT : T ≠ [] := by
    have hlenT : T.length = j-i := by simp [T,Nat.min_eq_left hjL]
    intro he
    rw [he] at hlenT
    simp only [List.length_nil] at hlenT
    omega
  have hm' : Nat.ModEq p (pre i*T.prod) (pre i*1) := by simpa [dec] using hm.symm
  refine ⟨T.prod,R,product_large hneT (fun x hx => (hL x (hsub x hx)).1),
    odd_list_prod T (fun x hx => (hL x (hsub x hx)).2.1),
    Nat.ModEq.cancel_left_of_coprime (cop i) hm',?_,?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h|h
    exacts [List.mem_of_mem_take h,List.mem_of_mem_drop h]
  · simp [R,Nat.min_eq_left hiL]; omega
  · change T.prod*(L.take i ++ L.drop j).prod=L.prod
    rw [List.prod_append,← L.prod_take_mul_prod_drop j]
    change T.prod*(pre i*(L.drop j).prod) = pre j*(L.drop j).prod
    rw [← dec]; ac_rfl

private theorem pack_blocks {p : ℕ} (hp : p.Prime) (k : ℕ) (L : List ℕ)
    (hL : ∀ f ∈ L, 3 ≤ f ∧ Odd f ∧ ¬p ∣ f) (hlen : (p-1)*k ≤ L.length) :
    ∃ (fs : List ℕ) (R : ℕ), fs.length=k ∧ (∀ f ∈ fs, 3 ≤ f ∧ Odd f ∧ Nat.ModEq p f 1) ∧
      fs.prod*R=L.prod := by
  induction k generalizing L with
  | zero => exact ⟨[],L.prod,rfl,by simp,by simp⟩
  | succ k ih =>
    rw [Nat.mul_succ] at hlen
    obtain ⟨f,R,hf,ho,hm,hsub,hR,hdiv⟩ := extract_block hp L hL (by omega)
    obtain ⟨fs,J,hk,hfs,hJ⟩ := ih R (fun t ht => hL t (hsub t ht)) (by omega)
    refine ⟨f::fs,J,by simp [hk],?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      exacts [⟨hf,ho,hm⟩,hfs a ha]
    · rw [List.prod_cons,Nat.mul_assoc,hJ,hdiv]

/-- The non-p factors form only a bounded number of blocks congruent to one modulo p. -/
private theorem coprime_count {h b C c p : ℕ} {S : Finset ℕ} (hh : 16 ≤ h) (he : Even h)
    (hb : Odd b) (hp : p.Prime) (hpdiv : p ∣ h+1) (L : List ℕ)
    (hL : ∀ f ∈ L, 3 ≤ f ∧ Odd f ∧ ¬ p ∣ f) (hdiv : L.prod ∣ b)
    (hS : primeSupport S) (hB : abundancy S < 2) (hc : c ≠ 0)
    (hout : ∀ q ∈ S, ¬ q ∣ c) (hbal : C*(2^(h*b)+1)*demands S = c*primesProduct S) :
    L.length < (p-1)*(c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length+2) := by
  let K := c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length
  by_contra! H
  obtain ⟨fs,J,hlen,hfs,hprod⟩ := pack_blocks hp (K+2) L hL H
  cases fs with
  | nil => simp at hlen
  | cons u fs =>
    cases fs with
    | nil => simp at hlen
    | cons z rs =>
      obtain ⟨hu,hou,hmu⟩ := hfs u List.mem_cons_self
      obtain ⟨hz,hoz,_⟩ := hfs z (by simp)
      have hlen' : rs.length = K := by simpa using hlen
      have hu' : h < h*u := by
        have := Nat.mul_le_mul_left h hu
        omega
      have hpmax := Nat.le_of_dvd (by omega : 0<h+1) hpdiv
      have hmu' : Nat.ModEq p (h*u+1) (h+1) := by simpa using (hmu.mul_left h).add_right 1
      obtain ⟨w,hw⟩ := hdiv
      have eqb : b=u*rs.prod*z*(J*w) := by
        rw [hw,← hprod,List.prod_cons,List.prod_cons]; ac_rfl
      have hJ : Odd (J*w) := hb.of_dvd_nat (eqb ▸ dvd_mul_left _ _)
      have hbalance : C*(2^(h*u*rs.prod*z*(J*w))+1)*demands S=c*primesProduct S := by
        convert hbal using 1
        rw [eqb]; ac_rfl
      have hres := charge_congr_blocks rs (fun f hf => hfs f (by simp [hf])) hz hoz hou hJ
        hp.two_le (by omega : 16 ≤ h*u) (he.mul_right u)
        (Nat.modEq_zero_iff_dvd.mp (hmu'.trans (Nat.modEq_zero_iff_dvd.mpr hpdiv))) (by omega)
        hS hB hc hout hbalance
      dsimp [K] at hlen'
      omega

private theorem power_count {h b C c p q m : ℕ} {S : Finset ℕ} (hh : 16 ≤ h) (he : Even h)
    (hb : Odd b) (hp : p.Prime) (hop : Odd p) (hq : q.Prime) (hqdiv : q ∣ h*p+1)
    (hm : 0 < m) (hmq : Nat.ModEq q (p^m) 1)
    (hS : primeSupport S) (hB : abundancy S < 2) (hc : c ≠ 0) (hout : ∀ r ∈ S, ¬ r ∣ c)
    (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    b.factorization p ≤ 1+(c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length+1)*m := by
  let K := c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length
  let f := p^m
  have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨j,hj⟩ := hop; omega
  have hf : 3 ≤ f := hp3.trans (Nat.le_pow hm)
  let u := p*f
  let fs := List.replicate K f
  by_contra! H
  have hlarge : 2+(K+1)*m ≤ b.factorization p := by dsimp [K]; omega
  obtain ⟨J,hJ⟩ := (Nat.pow_dvd_pow p hlarge).trans (Nat.ordProj_dvd b p)
  have hj : Odd J := hb.of_dvd_nat (hJ ▸ dvd_mul_left _ _)
  have hs : h*p < h*u := by
    have hx := Nat.mul_le_mul_left (h*p) hf
    have hy : 0 < h*p := Nat.mul_pos (by omega) hp.pos
    dsimp [u]; rw [← Nat.mul_assoc]; omega
  have hqbound := Nat.le_of_dvd (show 0<h*p+1 by omega) hqdiv
  have hmu : Nat.ModEq q (h*u+1) (h*p+1) := by
    dsimp [u,f]; rw [← Nat.mul_assoc]
    simpa using (hmq.mul_left (h*p)).add_right 1
  have eq : u*fs.prod*p = p^(2+(K+1)*m) := by
    dsimp [u,fs,f]; rw [List.prod_replicate,← pow_mul]
    calc p*p^m*p^(m*K)*p = p^(1+m+(m*K)+1) := by simp only [pow_add,pow_one]
         _ = _ := by congr 1; ring
  have hbalance : C*(2^(h*u*fs.prod*p*J)+1)*demands S=c*primesProduct S := by
    convert hbal using 1
    rw [hJ,← eq]; ac_rfl
  have hres := charge_congr_blocks (h:=h) (u:=u) fs (fun t ht => by
      obtain rfl := (List.mem_replicate.mp ht).2
      exact ⟨hf,hop.pow,hmq⟩) hp3 hop (hop.mul hop.pow) hj hq.two_le
    (by have := Nat.le_mul_of_pos_right h hp.pos; omega : 16 ≤ h*u) (he.mul_right u)
    (Nat.modEq_zero_iff_dvd.mp (hmu.trans (Nat.modEq_zero_iff_dvd.mpr hqdiv))) (show q < h*u+1 by omega)
    hS hB hc hout hbalance
  simp only [fs,List.length_replicate,K] at hres
  omega

/-- Explicit uniform count of prime factors, counted with multiplicity, in the odd part.
    Any positive period m of p modulo q can be used. -/
theorem omega_from_balance {h b C c p q m : ℕ} {S : Finset ℕ} (hh : 16 ≤ h) (he : Even h)
    (hb : Odd b) (hp : p.Prime) (hpdiv : p ∣ h+1) (hq : q.Prime) (hqdiv : q ∣ h*p+1)
    (hm : 0 < m) (hmq : Nat.ModEq q (p^m) 1)
    (hS : primeSupport S) (hB : abundancy S < 2) (hc : c ≠ 0) (hout : ∀ r ∈ S, ¬ r ∣ c)
    (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    let K := c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length
    b.primeFactorsList.length ≤ (p-1)*(K+2)+m*(K+1) := by
  let z := b/p^b.factorization p
  have hz := Nat.ordCompl_dvd b p
  have hz0 : z ≠ 0 := (Nat.ordCompl_pos p hb.pos.ne').ne'
  have hpz : ¬ p ∣ z := Nat.not_dvd_ordCompl hp hb.pos.ne'
  have hL (f : ℕ) (hf : f ∈ z.primeFactorsList) : 3 ≤ f ∧ Odd f ∧ ¬ p ∣ f := by
    have hd := Nat.dvd_of_mem_primeFactorsList hf
    have hfprime := Nat.prime_of_mem_primeFactorsList hf
    have ho := hb.of_dvd_nat (hd.trans hz)
    exact ⟨by have := hfprime.two_le; obtain ⟨j,hj⟩ := ho; omega,ho,fun h => hpz (h.trans hd)⟩
  have h1 := coprime_count hh he hb hp hpdiv z.primeFactorsList hL (by rwa [Nat.prod_primeFactorsList hz0])
    hS hB hc hout hbal
  have h2 := power_count hh he hb hp ((he.add_odd odd_one).of_dvd_nat hpdiv) hq hqdiv hm hmq
    hS hB hc hout hbal
  have lengths := (Nat.perm_primeFactorsList_mul (pow_ne_zero (b.factorization p) hp.ne_zero) hz0).length_eq
  have eq : p^b.factorization p*z=b := Nat.ordProj_mul_ordCompl_eq_self b p
  rw [eq,hp.primeFactorsList_pow,List.length_append,List.length_replicate] at lengths
  dsimp only
  rw [Nat.mul_comm m]
  omega

theorem omega_bound_of_perfect {n h b p q m : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hh : 16 ≤ h) (he : Even h) (hb : Odd b) (hexp : n.factorization 2 = h*b)
    (hp : p.Prime) (hpdiv : p ∣ h+1) (hq : q.Prime) (hqdiv : q ∣ h*p+1)
    (hm : 0 < m) (hmq : Nat.ModEq q (p^m) 1) :
    let c := core n
    let K := c.primeFactorsList.length-(c.gcd (oddPart (sigmaU c)*(2^h+1))).primeFactorsList.length
    b.primeFactorsList.length ≤ (p-1)*(K+2)+m*(K+1) := by
  obtain ⟨hc,_,S,_,hpS,hbal,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change Odd (core n) at hc
  change ∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2^n.factorization 2*core n at hpS
  change sigmaU (2^n.factorization 2*core n)*shifted S = 2*(2^n.factorization 2*core n)*primesProduct S at hbal
  have ha : 0 < n.factorization 2 := by rw [hexp]; exact Nat.mul_pos (by omega) hb.pos
  obtain ⟨hS,hout,hB,hd⟩ := normalize ha hc hc.pos.ne' hpS hbal
  rw [hexp] at hd
  exact omega_from_balance hh he hb hp hpdiv hq hqdiv hm hmq hS hB hc.pos.ne' hout hd

/-- A bound involving only the repeated core and the power-of-two part h. -/
theorem uniform_omega_bound {n h b : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hh : 16 ≤ h) (he : Even h) (hb : Odd b) (hexp : n.factorization 2=h*b) :
    let c := core n
    let K := c.primeFactorsList.length-(c.gcd (oddPart (sigmaU c)*(2^h+1))).primeFactorsList.length
    b.primeFactorsList.length ≤ h*((h+2)*(K+1)+1) := by
  let p := (h+1).minFac
  let q := (h*p+1).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ h+1 := Nat.minFac_dvd _
  have hp' : p ≤ h+1 := Nat.le_of_dvd (by omega) hd
  have hz : 0<h*p := Nat.mul_pos (by omega) hp.pos
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hdq : q ∣ h*p+1 := Nat.minFac_dvd _
  have hq' : q ≤ h*p+1 := Nat.le_of_dvd (by omega) hdq
  have cop : p.Coprime q := hq.coprime_iff_not_dvd.mpr (by
    intro H
    have hqp : q ∣ h*p := dvd_mul_of_dvd_right H h
    have h1 : q ∣ 1 := (Nat.dvd_add_iff_right hqp).mpr hdq
    exact hq.not_dvd_one h1) |>.symm
  have hm := Nat.ModEq.pow_totient cop
  have hr := omega_bound_of_perfect hn hh he hb hexp hp hd hq hdq (Nat.totient_pos.mpr hq.pos) hm
  let K := (core n).primeFactorsList.length-((core n).gcd (oddPart (sigmaU (core n))*(2^h+1))).primeFactorsList.length
  change b.primeFactorsList.length ≤ (p-1)*(K+2)+q.totient*(K+1) at hr
  change b.primeFactorsList.length ≤ h*((h+2)*(K+1)+1)
  rw [Nat.totient_prime hq] at hr
  have ht : q-1 ≤ h*(h+1) := (show q-1 ≤ h*p by omega).trans (Nat.mul_le_mul_left _ hp')
  calc _ ≤ _ := hr
       _ ≤ h*(K+2)+(h*(h+1))*(K+1) :=
         Nat.add_le_add (Nat.mul_le_mul_right _ (show p-1 ≤ h by omega)) (Nat.mul_le_mul_right _ ht)
       _ = _ := by ring

/-- Finiteness for every specified bound on the prime divisors of the odd part. -/
theorem finite_smooth_exponents (h c L : ℕ) (hh : 16 ≤ h) (he : Even h) (hL : 1 ≤ L) :
    {b : ℕ | Odd b ∧ (∀ p ∈ b.primeFactorsList, p ≤ L) ∧
      ∃ n, Erdos1052.IsUnitaryPerfect n ∧ core n = c ∧ n.factorization 2=h*b}.Finite := by
  let K := c.primeFactorsList.length-(c.gcd (oddPart (sigmaU c)*(2^h+1))).primeFactorsList.length
  let B := h*((h+2)*(K+1)+1)
  refine (Set.finite_Iic (L^B)).subset ?_
  intro b hb
  obtain ⟨ho,hfac,n,hn,hc,hexp⟩ := hb
  have hc' := uniform_omega_bound hn hh he ho hexp
  simp only [hc] at hc'
  have prodBound (F : List ℕ) (hf : ∀ p ∈ F, p ≤ L) : F.prod ≤ L^F.length := by
    induction F with
    | nil => simp
    | cons p F ih =>
      simp only [List.prod_cons,List.length_cons,pow_succ']
      exact Nat.mul_le_mul (hf p List.mem_cons_self) (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))
  have hz := prodBound b.primeFactorsList hfac
  rw [Nat.prod_primeFactorsList ho.pos.ne'] at hz
  exact hz.trans (Nat.pow_le_pow_right (by omega) hc')

/-- A simple prime forced by a repeated component cannot have a shift divisible
    by the square of another prime outside the core. -/
theorem double_shift_obstruction {a c p r t : ℕ} (hc : c ≠ 0)
    (hp : p ∈ c.primeFactors) (hp2 : p ≠ 2)
    (hr : r.Prime) (hr2 : ¬r ∣ 2) (hrc : ¬r ∣ c)
    (ht : t.Prime) (ht2 : ¬t ∣ 2) (htc : ¬t ∣ c)
    (hrp : r ∣ 1+p^c.factorization p) (htr : t^2 ∣ 1+r) : ¬ Admits c a := by
  let b := 2^a*c
  have hpow : (2:ℕ)^a ≠ 0 := by positivity
  have hb : b ≠ 0 := mul_ne_zero hpow hc
  have outside {z : ℕ} (hz : z.Prime) (h2 : ¬z ∣ 2) (hzc : ¬z ∣ c) : ¬z ∣ 2*b := by
    simpa [b,hz.dvd_mul,hzc,h2] using (show ¬z ∣ 2^a from fun H => h2 (hz.dvd_of_dvd_pow H))
  have hpb : p ∈ b.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp,dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) _,hb⟩
  have hval : b.factorization p = c.factorization p := by
    simp [b,Nat.factorization_mul hpow hc,Nat.prime_two.factorization_pow,Ne.symm hp2]
  rintro ⟨S,hS,hbal⟩
  have hrS := forced_member hr (outside hr hr2 hrc) hS hbal
    (dvd_mul_of_dvd_left (hrp.trans (hval ▸ sigma_factor hpb)) _)
  apply square_obstruction ht (mul_ne_zero (by decide : (2:ℕ) ≠ 0) hb) (outside ht ht2 htc) hS
  rw [← hbal]
  exact dvd_mul_of_dvd_right (htr.trans (Finset.dvd_prod_of_mem (fun z : ℕ => 1+z) hrS)) _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- In particular, every exponent is excluded for this infinite family of fixed cores. -/
theorem no_65537_sixteen_class (a k : ℕ) : ¬ Admits (65537^(16*(2*k+1))) a := by
  let e := 16*(2*k+1)
  have hp : Nat.Prime 65537 := by norm_num1
  have hr : Nat.Prime 4365089 := by norm_num1
  have ho : Odd (2*k+1) := ⟨k,rfl⟩
  have ha := ho.nat_add_dvd_pow_add_pow (65537^16) 1
  rw [one_pow,← pow_mul] at ha
  have hv : 4365089 ∣ 1+65537^e := by
    rw [Nat.add_comm]
    exact dvd_trans (by decide +kernel : 4365089 ∣ 65537^16+1) ha
  have hmem := Nat.mem_primeFactors.mpr
    ⟨hp,dvd_pow_self 65537 (show e ≠ 0 by dsimp [e]; omega),pow_ne_zero e hp.ne_zero⟩
  apply double_shift_obstruction (pow_ne_zero e hp.ne_zero) hmem (by decide) hr (by decide)
    (fun h => (by decide : ¬4365089 ∣ 65537) (hr.dvd_of_dvd_pow h))
    Nat.prime_three (by decide) (fun h => (by decide : ¬3 ∣ 65537) (Nat.prime_three.dvd_of_dvd_pow h))
    _ (by decide)
  simpa [hp.factorization_pow] using hv

end Erdos1052.OddExponent
