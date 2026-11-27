import OMAReductions.R_Erdos1052_erdos_1052_R2
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Exponent finiteness at sparse prime-square cores

Theorem Erdos1052.PrimeSquare.prime_square_of_perfect proves that the odd multiplier equals one under the sparse order and divisibility hypotheses. The full arithmetic argument and the finite certificates for those hypotheses are in the companion proof.
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

theorem compatible_weight_bound {x D : ℕ} (S : Finset ℕ) (d : ℕ → ℕ) (hx : 1 ≤ x)
    (hD : D ≠ 0) (hS : ∀ q ∈ S, q.Prime ∧ x < q ∧ 0 < d q ∧ 2 * d q ≤ q + 1)
    (hdvd : (∏ q ∈ S, d q) ∣ D * ∏ q ∈ S, q) :
    (∏ q ∈ S, (1 + 1 / (q : ℚ))) ≤
      weightProd x D *
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

theorem compatible_tail_bound {x D : ℕ} (S : Finset ℕ) (d : ℕ → ℕ) (hx : 1 ≤ x)
    (hD : D ≠ 0) (hS : ∀ q ∈ S, q.Prime ∧ x < q ∧ 0 < d q ∧ 2 * d q ≤ q + 1)
    (hdvd : (∏ q ∈ S, d q) ∣ D * ∏ q ∈ S, q) :
    (∏ q ∈ S, (1 + 1 / (q : ℚ))) ≤
      (1 + 2 / (x : ℚ)) ^ D.primeFactorsList.length *
        ∏ q ∈ S, (if d q = 1 then pathBound q else 1) := by
  apply (compatible_weight_bound S d hx hD hS hdvd).trans
  apply mul_le_mul_of_nonneg_right (weightProd_bounds hx D).2
  apply Finset.prod_nonneg
  intro q hq
  have hmin : (1 : ℚ) < q := by exact_mod_cast (hS q hq).1.one_lt
  split_ifs
  · unfold pathBound; positivity
  · norm_num

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

/-
# Distinct prime multipliers charge the core separately

The prime-index quotients at the same base are different cyclotomic
layers. They can be split off simultaneously, together with every cubic
layer. This counts the copies of three plus the distinct other primes.
-/

namespace Erdos1052.DistinctFactors

open Polynomial Erdos1052.CoreBounds Erdos1052.Core625 Erdos1052.OddExponent

noncomputable def layer (h i : ℕ) : ℕ := (eval (-(2:ℤ)^h) (cyclotomic i ℤ)).natAbs

theorem all_layers (h : ℕ) {b : ℕ} (hb : Odd b) :
    (∏ i ∈ b.divisors, layer h i)=2^(h*b)+1 := by
  have hv := congrArg (eval (-(2:ℤ)^h)) (prod_cyclotomic_eq_X_pow_sub_one hb.pos ℤ)
  rw [eval_prod,eval_sub,eval_pow,eval_X,eval_one,hb.neg_pow,← pow_mul] at hv
  have hh := congrArg Int.natAbsHom hv
  rw [map_prod] at hh
  change (∏ i ∈ b.divisors, layer h i)= (-(2:ℤ)^(h*b)-1).natAbs at hh
  rw [show -(2:ℤ)^(h*b)-1= -((2:ℤ)^(h*b)+1) by ring,Int.natAbs_neg] at hh
  have hvn : (2:ℤ)^(h*b)+1 = ((2^(h*b)+1:ℕ):ℤ) := by push_cast; rfl
  simpa only [hvn,Int.natAbs_natCast] using hh

theorem layer_one (h : ℕ) : layer h 1=2^h+1 := by
  simpa using all_layers h (b:=1) odd_one

theorem prime_layer (h : ℕ) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    layer h p*(2^h+1)=2^(h*p)+1 := by
  have hh := all_layers h ho
  rw [hp.divisors,Finset.prod_insert (by simpa using hp.ne_one.symm),Finset.prod_singleton,
    layer_one,Nat.mul_comm] at hh
  exact hh

theorem prime_power_layer (h : ℕ) {p : ℕ} (hp : p.Prime) (ho : Odd p) (j : ℕ) :
    layer h (p^(j+1))*(2^(h*p^j)+1)=2^(h*p^(j+1))+1 := by
  have hj := all_layers h (show Odd (p^j) from ho.pow)
  have hn := all_layers h (show Odd (p^(j+1)) from ho.pow)
  rw [Nat.prod_divisors_prime_pow hp] at hj hn
  rwa [Finset.prod_range_succ,hj,mul_comm] at hn

/-- All prime-index factors in P divide the remaining quotient simultaneously;
no pairwise-coprimality assumption on their evaluated integer values is needed. -/
theorem independent_layers (h : ℕ) {b j : ℕ} (hb : Odd b) (hj : Odd j) (hjb : j∣b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p∣b ∧ ¬ p∣j) :
    (∏ p ∈ P, layer h p)*(2^(h*j)+1) ∣ 2^(h*b)+1 := by
  have hdis : Disjoint P j.divisors := Finset.disjoint_left.mpr fun p hp h =>
    (hP p hp).2 (Nat.mem_divisors.mp h).1
  have hsub : P ∪ j.divisors ⊆ b.divisors := by
    intro p hp
    rcases Finset.mem_union.mp hp with hm | hm
    · exact Nat.mem_divisors.mpr ⟨(hP p hm).1,hb.pos.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hm).1.trans hjb,hb.pos.ne'⟩
  have hdiv := Finset.prod_dvd_prod_of_subset _ _ (layer h) hsub
  rwa [Finset.prod_union hdis,all_layers h hj,all_layers h hb] at hdiv

/-- Every selected nontrivial cyclotomic index is charged to the core separately. -/
theorem count_layer_subset {h b C c : ℕ} {S U : Finset ℕ} (hb : Odd b)
    (hU : ∀ i∈U, i∣b ∧ i≠1 ∧ requiresCore (layer h i))
    (hS : primeSupport S) (hSmall : abundancy S<2) (hc : c≠0)
    (hout : ∀ q∈S, ¬q∣c) (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    U.card+(c.gcd (C*(2^h+1))).primeFactorsList.length ≤ c.primeFactorsList.length := by
  have hd := independent_layers h hb odd_one (one_dvd b) U (fun i hi =>
    ⟨(hU i hi).1, fun hh => (hU i hi).2.1 (Nat.dvd_one.mp hh)⟩)
  rw [mul_one] at hd
  obtain ⟨v,hv⟩ := hd
  let As := U.toList.map (layer h)
  have ha : ∀ A ∈ As, requiresCore A := by
    intro A hA
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hA
    exact (hU i (Finset.mem_toList.mp hi)).2.2
  have hprod : As.prod*((C*(2^h+1))*v)*demands S=c*primesProduct S := by
    rw [← hbal,hv]
    dsimp [As]
    rw [Finset.prod_map_toList]
    ac_rfl
  have hl := count_required As ha hS hSmall hc
    (dvd_mul_of_dvd_left (Nat.gcd_dvd_right c (C*(2^h+1))) v)
    (fun q hq hd => hout q hq (hd.trans (Nat.gcd_dvd_left _ _))) hprod
  simpa only [As,List.length_map,Finset.length_toList] using hl

theorem charged_count {h b C c : ℕ} {S : Finset ℕ} (hh : 16≤h) (hb : Odd b)
    (hP : ∀ p ∈ b.primeFactors.erase 3, requiresCore (layer h p))
    (hS : primeSupport S) (hSmall : abundancy S<2) (hc : c≠0)
    (hout : ∀ q∈S, ¬q∣c) (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    b.factorization 3+(b.primeFactors.erase 3).card+
      (c.gcd (C*(2^h+1))).primeFactorsList.length ≤ c.primeFactorsList.length := by
  let t := b.factorization 3
  let P := b.primeFactors.erase 3
  have hp (p : ℕ) (hp : p∈P) : p∣b ∧ ¬p∣3^t := by
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hp
    have hpr := Nat.prime_of_mem_primeFactors hmem
    exact ⟨Nat.dvd_of_mem_primeFactors hmem,fun hd =>
      hne ((Nat.prime_three.dvd_iff_eq hpr.ne_one).mp (hpr.dvd_of_dvd_pow hd)).symm⟩
  have hd := independent_layers h hb (by exact (by decide : Odd 3).pow : Odd (3^t))
    (Nat.ordProj_dvd b 3) P hp
  obtain ⟨v,hv⟩ := hd
  let As := P.toList.map (layer h) ++ cubicLayers h t
  have ha : ∀ A ∈ As, requiresCore A := by
    intro A hA
    rcases List.mem_append.mp hA with hm | hm
    · obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hm
      exact hP p (show p∈P from Finset.mem_toList.mp hp')
    · exact cubic_required hh t A hm
  have hprod : As.prod*((C*(2^h+1))*v)*demands S=c*primesProduct S := by
    rw [← hbal,hv,← cubic_product h t]
    dsimp [As]
    rw [List.prod_append,Finset.prod_map_toList]
    ac_rfl
  have hcount := count_required As ha hS hSmall hc
    (dvd_mul_of_dvd_left (Nat.gcd_dvd_right c (C*(2^h+1))) v)
    (fun q hq hd => hout q hq (hd.trans (Nat.gcd_dvd_left _ _))) hprod
  simpa only [As,List.length_append,List.length_map,Finset.length_toList,cubic_length,
    Nat.add_comm P.card t] using hcount

theorem composite_start_charges {h p : ℕ} (hh : 16≤h) (he : Even h)
    (hc : ¬ (2^(h+1)-1).Prime) (hp : p.Prime) (ho : Odd p) :
    requiresCore (layer h p) := by
  intro T hT D hd hsmall
  have hp3 : 3≤p := by have := hp.two_le; obtain ⟨u,hu⟩ := ho; omega
  have hw : 2*h≤h*(p-1) := by
    rw [Nat.mul_comm 2 h]
    exact Nat.mul_le_mul_left h (by omega)
  apply nonneutral_block hT hh he hc hw _ hd hsmall
  rw [← pow_add,show h+h*(p-1)=h*p by
    rw [Nat.add_comm,← Nat.mul_succ]; congr 1; omega]
  exact prime_layer h hp ho

theorem prime_power_charges {h p j : ℕ} (hh : 16≤h) (he : Even h)
    (hp : p.Prime) (ho : Odd p) (hc : ¬(h*p^j+1).Prime) :
    requiresCore (layer h (p^(j+1))) := by
  have hs : 16≤h*p^j := hh.trans (Nat.le_mul_of_pos_right _ (pow_pos hp.pos _))
  have hw : 2*(h*p^j)≤(h*p^j)*(p-1) := by
    rw [Nat.mul_comm 2 _]
    apply Nat.mul_le_mul_left
    have := hp.two_le
    obtain ⟨k,hk⟩ := ho
    omega
  intro T hT D hD hsmall
  apply nonneutral_block hT hs (he.mul_right _) (fun hpr => hc (Nat.Prime.of_mersenne hpr))
    hw _ hD hsmall
  rw [← pow_add,show h*p^j+(h*p^j)*(p-1)=h*p^(j+1) by
    rw [pow_succ,← Nat.mul_assoc,Nat.add_comm,← Nat.mul_succ]; congr 1; have := hp.pos; omega]
  exact prime_power_layer h hp ho j

theorem count_prime_power_indices {h b C c : ℕ} {S : Finset ℕ} (hb : Odd b)
    (J : ℕ → Finset ℕ) (hJ : ∀ p∈b.primeFactors, ∀ j∈J p,
      j<b.factorization p ∧ requiresCore (layer h (p^(j+1))))
    (hS : primeSupport S) (hSmall : abundancy S<2) (hc : c≠0)
    (hout : ∀ q∈S, ¬q∣c) (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    (∑ p∈b.primeFactors, (J p).card)+(c.gcd (C*(2^h+1))).primeFactorsList.length
      ≤ c.primeFactorsList.length := by
  let V := fun p => (J p).image (fun j => p^(j+1))
  have hd : (↑b.primeFactors : Set ℕ).PairwiseDisjoint V := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ht
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ht'
    exact hpq ((Nat.prime_of_mem_primeFactors hp).pow_inj (Nat.prime_of_mem_primeFactors hq)
      (hi.trans hj.symm)).1
  have hsize (p : ℕ) (hp : p∈b.primeFactors) : (V p).card=(J p).card := by
    apply Finset.card_image_iff.mpr
    intro i _ j _ hij
    exact ((Nat.prime_of_mem_primeFactors hp).pow_inj (Nat.prime_of_mem_primeFactors hp) hij).2
  have hU (d : ℕ) (hd : d∈b.primeFactors.biUnion V) : d∣b ∧ d≠1 ∧ requiresCore (layer h d) := by
    obtain ⟨p,hp,hd⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hlt,hr⟩ := hJ p hp j hj
    exact ⟨(Nat.pow_dvd_pow p hlt).trans (Nat.ordProj_dvd b p),
      ne_of_gt (one_lt_pow₀ (Nat.prime_of_mem_primeFactors hp).one_lt (by omega)),hr⟩
  have hh := count_layer_subset hb hU hS hSmall hc hout hbal
  rwa [Finset.card_biUnion hd,Finset.sum_congr rfl hsize] at hh

theorem cubic_layer_charges {h : ℕ} (hh : 16≤h) (j : ℕ) :
    requiresCore (layer h (3^(j+1))) := by
  have hp := prime_power_layer h Nat.prime_three (by decide) j
  have hchain := cubic_identity (h*3^j)
  rw [pow_succ,← Nat.mul_assoc] at hp
  have h : layer h (3^(j+1)) = chain (h*3^j) (h*3^j) :=
    Nat.eq_of_mul_eq_mul_right (by positivity) (hp.trans hchain.symm)
  rw [h]
  intro T hT D hD hB
  exact nonneutral_cubic hT (hh.trans (Nat.le_mul_of_pos_right _ (by positivity))) hD hB

/-- At h congruent to 2 modulo 3, at least every other prime-power layer is forced. -/
theorem double_omega_bound {h b C c : ℕ} {S : Finset ℕ} (hh : 16≤h) (he : Even h)
    (hm : h%3=2) (hb : Odd b) (hS : primeSupport S) (hSmall : abundancy S<2)
    (hc : c≠0) (hout : ∀ q∈S, ¬q∣c)
    (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    b.primeFactorsList.length ≤
      2*(c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length) := by
  let J := fun p => (Finset.range ((b.factorization p+1)/2)).image (fun k=>2*k)
  have hJ (p : ℕ) (hp : p∈b.primeFactors) (j : ℕ) (hj : j∈J p) :
      j<b.factorization p ∧ requiresCore (layer h (p^(j+1))) := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_range.mp hk
    refine ⟨by omega,?_⟩
    by_cases hp3 : p=3
    · subst p; exact cubic_layer_charges hh _
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hnon : ¬3∣p := fun hd => hp3 ((Nat.dvd_prime hpr).mp hd |>.resolve_left (by decide)).symm
    have hsq : Nat.ModEq 3 (p^2) 1 := by
      simpa only [show Nat.totient 3=2 by decide] using
        Nat.ModEq.pow_totient ((Nat.prime_three.coprime_iff_not_dvd.mpr hnon).symm)
    have hpow : Nat.ModEq 3 (p^(2*k)) 1 := by simpa [pow_mul] using hsq.pow k
    have hdiv : 3∣h*p^(2*k)+1 := Nat.modEq_zero_iff_dvd.mp <|
      (((hpow.mul_left h).add_right 1).trans (by change (h*1+1)%3=0%3; omega))
    have hlarge := hh.trans (Nat.le_mul_of_pos_right h (pow_pos hpr.pos (2*k)))
    apply prime_power_charges hh he hpr (hb.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    intro hcand
    rcases (Nat.dvd_prime hcand).mp hdiv with ha|ha <;> omega
  have hcount := count_prime_power_indices hb J hJ hS hSmall hc hout hbal
  have hcard (p : ℕ) : (J p).card=(b.factorization p+1)/2 := by
    dsimp [J]
    rw [Finset.card_image_iff.mpr (by intro i _ j _ hij; dsimp at hij; omega),Finset.card_range]
  have hsum : b.primeFactorsList.length ≤ 2*∑ p∈b.primeFactors, (J p).card := by
    rw [← ArithmeticFunction.cardFactors_apply,ArithmeticFunction.cardFactors_eq_sum_factorization,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    change b.factorization p≤2*(J p).card
    rw [hcard]; omega
  omega

end Erdos1052.DistinctFactors

/- A neutral cyclotomic layer cannot start at an even exponent equal to 1 modulo 5. -/

namespace Erdos1052.OddResidue

open Erdos1052.Core625 Erdos1052.CoreBounds Erdos1052.OddExponent Erdos1052.DistinctFactors

def oddTail (s : ℕ) : ℚ := (3*2^s)/(3*2^s-8)

theorem odd_roots_product (K : Finset ℕ) {s : ℕ} (hs : 3 ≤ s)
    (hK : ∀ t∈K, s≤t ∧ Odd t) : (∏ t∈K, mersenneFactor t) ≤ oddTail s := by
  induction K using Finset.strongInductionOn generalizing s with
  | _ K ih =>
    have hs0 : (4:ℚ)<2^s := lt_of_lt_of_le (by norm_num : (4:ℚ)<2^3)
      (pow_le_pow_right₀ (by norm_num) hs)
    rcases K.eq_empty_or_nonempty with hk|hk
    · subst K; simp only [Finset.prod_empty,oddTail]
      apply (le_div_iff₀ (by linarith)).mpr; linarith
    let t := K.min' hk
    have ht := Finset.min'_mem K hk
    obtain ⟨hst,hto⟩ := hK t ht
    have hpow : (2:ℚ)^s≤2^t := pow_le_pow_right₀ (by norm_num) hst
    have hinc (j : ℕ) (hj : j∈K.erase t) : t+2≤j ∧ Odd j := by
      obtain ⟨hne,hj⟩ := Finset.mem_erase.mp hj
      have hle : t≤j := Finset.min'_le K j hj
      have hjo := (hK j hj).2
      refine ⟨?_,hjo⟩
      obtain ⟨x,hx⟩ := hto; obtain ⟨y,hy⟩ := hjo; omega
    have hrec := ih (K.erase t) (Finset.erase_ssubset ht) (s:=t+2) (by omega) hinc
    rw [← Finset.mul_prod_erase K mersenneFactor ht]
    calc mersenneFactor t * (∏ j∈K.erase t, mersenneFactor j)
         ≤ mersenneFactor t * oddTail (t+2) :=
           mul_le_mul_of_nonneg_left hrec (div_nonneg (by positivity) (by linarith))
      _ ≤ oddTail t := by
        unfold mersenneFactor oddTail
        rw [pow_add,show (2:ℚ)^2=4 by norm_num,div_mul_div_comm,
          div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
        nlinarith
      _ ≤ oddTail s := by
        unfold oddTail
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith

private theorem tail_after_root {V : Finset ℕ} {s : ℕ} (hs : 16 ≤ s) (he : Even s)
    (hp : primeSupport V) (hlarge : ∀ q∈V, 2^s<q) (habs : 2^(s+1)-1∉V) :
    (∏ q∈V, if demand q=1 then pathBound q else 1) ≤ oddTail (s+3) := by
  let R := V.filter fun q => demand q=1
  let t := fun q : ℕ => (1+q).factorization 2
  have hR (q : ℕ) (hq : q∈R) : q∈V ∧ demand q=1 := Finset.mem_filter.mp hq
  have hpow (q : ℕ) (hq : q∈R) : 2^t q=1+q := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
    change 2^t q*demand q=1+q at h
    simpa only [(hR q hq).2,mul_one] using h
  have hmin (q : ℕ) (hq : q∈R) : s+3≤t q ∧ Odd (t q) := by
    have hv := hpow q hq
    have hval : 2^t q-1=q := by omega
    have ht : s<t q := by
      by_contra! hn
      have := Nat.pow_le_pow_right (n:=2) (by decide) hn
      have := hlarge q (hR q hq).1
      omega
    have h1 : t q≠s+1 := fun hh => habs (by rw [← hh,hval]; exact (hR q hq).1)
    have hprime : (t q).Prime := Nat.Prime.of_mersenne (by simpa [mersenne,hval] using (hp q (hR q hq).1).1)
    have ho := hprime.odd_of_ne_two (by omega)
    refine ⟨?_,ho⟩
    obtain ⟨j,hj⟩ := ho; obtain ⟨k,hk⟩ := he; omega
  have hinj : Set.InjOn t R := by
    intro q hq p hp heq
    have h1 := hpow q hq; have h2 := hpow p hp
    rw [show t q=t p from heq] at h1; omega
  have hid (q : ℕ) (hq : q∈R) : pathBound q=mersenneFactor (t q) := by
    have hv : (2:ℚ)^t q=1+q := by exact_mod_cast hpow q hq
    unfold pathBound mersenneFactor; rw [hv]; congr 1 <;> ring
  change (∏ q∈V, if demand q=1 then pathBound q else 1)≤_
  rw [← Finset.prod_filter]
  change (∏ q∈R, pathBound q)≤_
  have heq : (∏ q∈R, pathBound q)=∏ j∈R.image t, mersenneFactor j := by
    rw [Finset.prod_image hinj]; exact Finset.prod_congr rfl hid
  rw [heq]; apply odd_roots_product _ (by omega)
  intro j hj; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
  exact hmin q hq

private theorem no_doubled_prime {T : Finset ℕ} (hT : primeSupport T) {r : ℕ} (hr : r.Prime) :
    ¬r*r∣primesProduct T := by
  intro hd
  have hm := prime_mem_of_dvd hT hr ((dvd_mul_right r r).trans hd)
  rw [show primesProduct T=r*primesProduct (T.erase r) from
    (Finset.mul_prod_erase T id hm).symm] at hd
  have h := prime_mem_of_dvd (R:=T.erase r) (fun q hq => hT q (Finset.mem_of_mem_erase hq))
    hr ((Nat.mul_dvd_mul_iff_left hr.pos).mp hd)
  exact (Finset.mem_erase.mp h).1 rfl

private theorem one_supplier {T : Finset ℕ} (hT : primeSupport T) {r x y : ℕ} (hr : r.Prime)
    (hd : demands T∣primesProduct T) (hx : x∈T) (hy : y∈T)
    (hxr : r∣demand x) (hyr : r∣demand y) : x=y := by
  by_contra hne
  have hsub : ({x,y} : Finset ℕ)⊆T := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hq|hq
    · exact hq ▸ hx
    · exact (Finset.mem_singleton.mp hq) ▸ hy
  have hdiv := Finset.prod_dvd_prod_of_subset _ _ demand hsub
  rw [Finset.prod_insert (by simpa using hne),Finset.prod_singleton] at hdiv
  exact no_doubled_prime hT hr (((Nat.mul_dvd_mul hxr hyr).trans hdiv).trans hd)

private theorem path_bound_anti {x y : ℕ} (hx : 1<x) (hxy : x≤y) : pathBound y≤pathBound x := by
  have hx' : (1:ℚ)<x := by exact_mod_cast hx
  have hxy' : (x:ℚ)≤y := by exact_mod_cast hxy
  unfold pathBound
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

private theorem one_le_path {x : ℕ} (hx : 1<x) : 1≤pathBound x := by
  have hx' : (1:ℚ)<x := by exact_mod_cast hx
  apply (le_div_iff₀ (by linarith : 0<(x:ℚ)-1)).mpr; linarith

/-- Removing r can introduce at most one additional root. Its size is at least H. -/
private theorem trim_root {T : Finset ℕ} (hp : primeSupport T) {r H : ℕ} (hr : r.Prime)
    (hH : 1<H) (hd : demands T∣primesProduct T)
    (hnext : ∀ q∈T, r∣demand q → H≤q) :
    abundancy (T.erase r) ≤ pathBound H *
      ∏ q∈T.erase r, if demand q=1 then pathBound q else 1 := by
  let V := T.erase r
  let f := fun q => ordCompl[r] (demand q)
  have hv (q : ℕ) (hq : q∈V) : q∈T := Finset.mem_of_mem_erase hq
  have hpos (q : ℕ) : 0<demand q := Nat.ordCompl_pos 2 (by omega)
  have hfd (q : ℕ) : f q∣demand q := Nat.ordCompl_dvd _ _
  have hd0 : (∏ q∈V, f q)∣primesProduct T :=
    ((Finset.prod_dvd_prod_of_dvd f demand (fun q _ => hfd q)).trans
      (Finset.prod_dvd_prod_of_subset _ _ demand (Finset.erase_subset r T))).trans hd
  have hfdV : (∏ q∈V, f q)∣primesProduct V := by
    by_cases hm : r∈T
    · rw [show primesProduct T=r*primesProduct V from (Finset.mul_prod_erase T id hm).symm] at hd0
      have hcop : r.Coprime (∏ q∈V, f q) := Nat.coprime_prod_right_iff.mpr
        fun q _ => Nat.coprime_ordCompl hr (hpos q).ne'
      exact hcop.symm.dvd_of_dvd_mul_left hd0
    · simpa [V,Finset.erase_eq_of_notMem hm] using hd0
  have hlocal := compatible_tail_bound V f (x:=1) (D:=1) (by decide) (by decide)
    (fun q hq => ⟨(hp q (hv q hq)).1,(hp q (hv q hq)).1.one_lt,
      Nat.ordCompl_pos r (hpos q).ne',
      (Nat.mul_le_mul_left 2 (Nat.le_of_dvd (hpos q) (hfd q))).trans
        (twice_oddPart_shift_le ((hp q (hv q hq)).1.odd_of_ne_two (hp q (hv q hq)).2))⟩)
    (by simpa using hfdV)
  have hl : abundancy V≤∏ q∈V, if f q=1 then pathBound q else 1 := by simpa [abundancy,gain] using hlocal
  let W := V.filter (fun q => r∣demand q)
  have hmem (q : ℕ) (hq : q∈W) : q∈V ∧ r∣demand q := Finset.mem_filter.mp hq
  have hW : (∏ q∈W, pathBound q)≤pathBound H := by
    rcases W.eq_empty_or_nonempty with h|h
    · rw [h,Finset.prod_empty]; exact one_le_path hH
    · obtain ⟨t,ht⟩ := h
      have ht' := hmem t ht
      have heq : W={t} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ht,fun q hq =>
        one_supplier hp hr hd (hv q (hmem q hq).1) (hv t ht'.1) (hmem q hq).2 ht'.2⟩
      rw [heq,Finset.prod_singleton]
      exact path_bound_anti hH (hnext t (hv t ht'.1) ht'.2)
  have hroot (q : ℕ) (hq : q∈V) : 0 ≤ (if demand q=1 then pathBound q else 1) := by
    split <;> first | exact zero_le_one | exact zero_le_one.trans (one_le_path (hp q (hv q hq)).1.one_lt)
  have hcomb : (∏ q∈V, if f q=1 then pathBound q else 1) ≤
      (∏ q∈V, if r∣demand q then pathBound q else 1)*∏ q∈V, if demand q=1 then pathBound q else 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro q hq; split <;> first | exact zero_le_one | exact zero_le_one.trans (one_le_path (hp q (hv q hq)).1.one_lt)
    · intro q hq
      by_cases hq' : r∣demand q
      · have hn : demand q≠1 := fun heq => hr.ne_one (Nat.dvd_one.mp (heq ▸ hq'))
        simp only [if_pos hq',if_neg hn,mul_one]
        split <;> first | exact le_rfl | exact one_le_path (hp q (hv q hq)).1.one_lt
      · have hf : f q=demand q := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hr).mpr (.inr hq')
        simp only [if_neg hq',one_mul,hf,le_refl]
  have hfirst : (∏ q∈V, if r∣demand q then pathBound q else 1)≤pathBound H := by
    simpa only [W,Finset.prod_filter] using hW
  exact (hl.trans hcomb).trans (mul_le_mul_of_nonneg_right hfirst (Finset.prod_nonneg hroot))

private theorem no_small_supplier {T : Finset ℕ} (hp : primeSupport T) {s : ℕ}
    (hs : 16 ≤ s) (he : Even s) (hm : s%10=6) (hlarge : ∀ q∈T, 2^s<q)
    (hd : demands T∣primesProduct T) {q : ℕ} (hq : q∈T)
    (hrd : 2^(s+1)-1∣demand q) : 8*(2^(s+1)-1)-1≤q := by
  let Y := 2^s
  let r := 2^(s+1)-1
  have hY : 65536≤Y := Nat.pow_le_pow_right (n:=2) (by decide) hs
  have hr : r+1=2*Y := by dsimp [r,Y]; rw [pow_succ]; omega
  have hqpr := (hp q hq).1
  have hqodd := hqpr.odd_of_ne_two (hp q hq).2
  have hqr : r∣1+q := hrd.trans (Nat.ordCompl_dvd _ 2)
  obtain ⟨k,hk⟩ := hqr
  have hmod11 : (2^(s+2))%11=3 := by
    have hs' : s+2=10*(s/10)+8 := by omega
    rw [hs',pow_add,pow_mul]
    have hv : Nat.ModEq 11 ((2^10)^(s/10)*2^8) (1^(s/10)*2^8) :=
      ((by decide : Nat.ModEq 11 (2^10) 1).pow _).mul_right _
    simpa [Nat.ModEq] using hv
  have hmod3 : Y%3=1 := by
    obtain ⟨u,hu⟩ := he
    have hs' : s=2*u := by omega
    dsimp [Y]; rw [hs',pow_mul]
    simpa [Nat.ModEq] using (by decide : Nat.ModEq 3 (2^2) 1).pow u
  have hh : 2^(s+2)=4*Y := by dsimp [Y]; rw [pow_add]; ring
  have hqY := hlarge q hq
  change Y<q at hqY
  change 8*r-1≤q
  by_contra! hn
  have hklt : k<8 := by
    by_contra! hge
    have := Nat.mul_le_mul_left r hge
    omega
  obtain ⟨z,hz⟩ := hqodd
  interval_cases k <;> norm_num at hk <;> try omega
  all_goals first
    | exact ((Nat.dvd_prime hqpr).mp (show 11∣q by omega)).elim (by decide) (by omega)
    | exact ((Nat.dvd_prime hqpr).mp (show 3∣q by omega)).elim (by decide) (by omega)
    | have h3 : 3∣demand q := Nat.dvd_ordCompl_of_dvd_not_dvd (show 3∣1+q by omega) (by decide)
      have hmem := prime_mem_of_dvd hp Nat.prime_three
        ((h3.trans (Finset.dvd_prod_of_mem demand hq)).trans hd)
      have := hlarge 3 hmem
      change Y<3 at this
      omega

theorem slow_root_tail {T : Finset ℕ} (hp : primeSupport T) {s : ℕ} (hs : 16 ≤ s)
    (he : Even s) (hm : s%10=6) (hlarge : ∀ q∈T, 2^s<q) (hd : demands T∣primesProduct T) :
    abundancy T < 1+63/(64*(2:ℚ)^s) := by
  let r := 2^(s+1)-1
  let H := 8*r-1
  have hYn : 65536≤2^s := Nat.pow_le_pow_right (n:=2) (by decide) hs
  have hrn : r+1=2*2^s := by dsimp [r]; rw [pow_succ]; omega
  have hHn : H+1=8*r := by dsimp [H]; omega
  have hH : 1<H := by omega
  have ht : 0≤oddTail (s+3) := by
    have hv : (4:ℚ)<2^(s+3) := lt_of_lt_of_le (by norm_num : (4:ℚ)<2^13)
      (pow_le_pow_right₀ (by norm_num) (by omega))
    exact div_nonneg (by positivity) (by linarith)
  have hupper : abundancy T≤gain r*pathBound H*oddTail (s+3) := by
    by_cases hrT : r∈T
    · have hsupply := trim_root hp (hp r hrT).1 hH hd (fun q hq hrd => no_small_supplier hp hs he hm hlarge hd hq hrd)
      have hafter := tail_after_root (V:=T.erase r) hs he (fun q hq => hp q (Finset.mem_of_mem_erase hq))
        (fun q hq => hlarge q (Finset.mem_of_mem_erase hq)) (Finset.notMem_erase _ _)
      rw [show abundancy T=gain r*abundancy (T.erase r) from (Finset.mul_prod_erase T gain hrT).symm,mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsupply.trans
        (mul_le_mul_of_nonneg_left hafter (zero_le_one.trans (one_le_path hH)))) (zero_le_one.trans (gain_one_le r))
    · have hlocal := compatible_tail_bound T demand (x:=1) (D:=1) (by decide) (by decide)
        (fun q hq => ⟨(hp q hq).1,(hp q hq).1.one_lt,Nat.ordCompl_pos 2 (by omega),
          twice_oddPart_shift_le ((hp q hq).1.odd_of_ne_two (hp q hq).2)⟩) (by simpa using hd)
      have hlocal' : abundancy T ≤ ∏ q∈T, if demand q=1 then pathBound q else 1 := by simpa [abundancy,gain] using hlocal
      exact (hlocal'.trans (tail_after_root hs he hp hlarge hrT)).trans
        (le_mul_of_one_le_left ht (one_le_mul_of_one_le_of_one_le (gain_one_le r) (one_le_path hH)))
  let X : ℚ := 2^s
  have hX : (65536:ℚ)≤X := by dsimp [X]; exact_mod_cast hYn
  have hrq : (r:ℚ)+1=2*X := by dsimp [X]; exact_mod_cast hrn
  have hHq : (H:ℚ)+1=8*r := by exact_mod_cast hHn
  have hri : (r:ℚ)=2*X-1 := by linarith
  have hHi : (H:ℚ)=16*X-9 := by linarith
  apply lt_of_le_of_lt hupper
  unfold gain pathBound oddTail
  rw [hri,hHi,pow_add,show (2:ℚ)^3=8 by norm_num]
  change (1+1/(2*X-1))*((16*X-9+1)/(16*X-9-1))*((3*(X*8))/(3*(X*8)-8)) < 1+63/(64*X)
  have hc1 : (1+1/(2*X-1))*((16*X-9+1)/(16*X-9-1))=8*X/(8*X-5) := by
    have hfirst : 1+1/(2*X-1)=2*X/(2*X-1) := by
      apply (eq_div_iff (by linarith : 2*X-1≠0)).mpr
      rw [add_mul,div_mul_cancel₀ _ (by linarith)]; ring
    rw [hfirst,div_mul_div_comm,div_eq_div_iff
      (mul_ne_zero (by linarith) (by linarith)) (by linarith)]
    ring
  have hc2 : (3*(X*8))/(3*(X*8)-8)=3*X/(3*X-1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  have hc3 : 1+63/(64*X)=(64*X+63)/(64*X) := by
    field_simp [show X≠0 by linarith]
  rw [hc1,hc2,hc3,div_mul_div_comm,
    div_lt_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
  nlinarith [mul_nonneg (show 0≤X-100 by linarith) (show 0≤X by linarith)]

theorem nonneutral_six {s w A D : ℕ} {T : Finset ℕ} (hp : primeSupport T)
    (hs : 16 ≤ s) (he : Even s) (hm : s%10=6) (hw : 2*s≤w)
    (hA : A*(2^s+1)=2^s*2^w+1) (hd : A*demands T=D*primesProduct T)
    (hB : abundancy T<2) : D≠1 := by
  rintro rfl; rw [one_mul] at hd
  obtain ⟨heq,hlarge⟩ := neutral_size hp (by omega) hw hA hd hB
  have htail := slow_root_tail hp hs he hm hlarge (hd ▸ dvd_mul_left _ _)
  let X : ℚ := 2^s
  let L : ℚ := 2^w
  have hX : (65536:ℚ)≤X := by dsimp [X]; exact_mod_cast Nat.pow_le_pow_right (n:=2) (by decide) hs
  have hL : (65536:ℚ)≤L := by
    change (2:ℚ)^16≤2^w
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ha : (A:ℚ)*(X+1)=X*L+1 := by dsimp [X,L]; exact_mod_cast hA
  change (A:ℚ)*abundancy T=L at heq
  change abundancy T < 1+63/(64*X) at htail
  have hdiff : 64*X*(abundancy T-1)<63 := by
    have hh := (lt_div_iff₀ (by linarith : 0<64*X)).mp
      (show abundancy T-1<63/(64*X) by linarith)
    linarith
  have hapos : 0<(A:ℚ) := by
    by_contra! H
    have h0 : (A:ℚ)=0 := le_antisymm H (by positivity)
    rw [h0,zero_mul] at ha
    nlinarith [mul_pos (show 0<X by linarith) (show 0<L by linarith)]
  have hb' : 64*X*(L-(A:ℚ)) < 63*A := by
    have hh := mul_lt_mul_of_pos_left hdiff hapos
    nlinarith only [hh,congrArg (fun z : ℚ => z*(64*X)) heq]
  have hlt := mul_lt_mul_of_pos_right hb' (show 0<X+1 by linarith)
  nlinarith only [hlt,congrArg (fun z : ℚ => z*(64*X)) ha,ha,hX,
    mul_nonneg (show 0≤X by linarith) (show 0≤L-65 by linarith)]

private theorem five_charge {h p j : ℕ} (hh : 16≤h) (he : Even h) (hp : p.Prime) (ho : Odd p)
    (hm : (h*p^j)%5=1 ∨ (h*p^j)%5=4) : requiresCore (layer h (p^(j+1))) := by
  let s := h*p^j
  have hs : 16 ≤ s := hh.trans (Nat.le_mul_of_pos_right _ (pow_pos hp.pos _))
  have he' : Even s := he.mul_right _
  change s%5=1 ∨ s%5=4 at hm
  rcases hm with h1|h4
  · have hs10 : s%10=6 := by obtain ⟨u,hu⟩ := he'; omega
    have hw : 2*s ≤ s*(p-1) := by
      rw [Nat.mul_comm 2 _]; apply Nat.mul_le_mul_left
      have := hp.two_le; obtain ⟨k,hk⟩ := ho; omega
    intro T hT D hD hB
    apply nonneutral_six hT hs he' hs10 hw _ hD hB
    have heq : s+s*(p-1)=h*p^(j+1) := by
      dsimp [s]; rw [pow_succ,← Nat.mul_assoc,Nat.add_comm,← Nat.mul_succ]
      congr 1; have := hp.pos; omega
    rw [← pow_add,heq]; exact prime_power_layer h hp ho j
  · apply prime_power_charges hh he hp ho
    intro hpr
    have hd : 5∣s+1 := by omega
    rcases (Nat.dvd_prime hpr).mp hd with H|H <;> omega

private theorem square_mod_five {x : ℕ} (hx : ¬5∣x) : x^2%5=1 ∨ x^2%5=4 := by
  have hlt := Nat.mod_lt x (by decide : 0<5)
  rw [pow_two,Nat.mul_mod]
  have hne : x%5≠0 := fun hh => hx (Nat.dvd_of_mod_eq_zero hh)
  generalize x%5=t at *
  interval_cases t <;> first | contradiction | decide

theorem double_omega_square {h b C c : ℕ} {S : Finset ℕ} (hh : 16≤h) (he : Even h)
    (hm3 : h%3=1) (hm5 : h%5=1 ∨ h%5=4) (hb : Odd b)
    (hS : primeSupport S) (hB : abundancy S<2) (hc : c≠0)
    (hout : ∀ q∈S, ¬q∣c) (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    b.primeFactorsList.length ≤
      2*(c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length) := by
  let idx := fun p k : ℕ => if p=5 then 2*k-1 else 2*k
  let J := fun p => (Finset.range ((b.factorization p+1)/2)).image (idx p)
  have hJ (p : ℕ) (hp : p∈b.primeFactors) (j : ℕ) (hj : j∈J p) :
      j<b.factorization p ∧ requiresCore (layer h (p^(j+1))) := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_range.mp hk
    have hpr := Nat.prime_of_mem_primeFactors hp
    have ho := hb.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    by_cases hp5 : p=5
    · subst p
      simp only [idx,if_true]
      refine ⟨by omega,?_⟩
      cases k with
      | zero => exact five_charge hh he hpr ho (by simpa using hm5)
      | succ k =>
        have hpow : Nat.ModEq 3 (5^(2*(k+1)-1)) 2 := by
          rw [show 2*(k+1)-1=2*k+1 by omega,pow_succ,pow_mul]
          have ht : Nat.ModEq 3 ((5^2)^k*5) 5 := by
            simpa using ((by decide : Nat.ModEq 3 (5^2) 1).pow k).mul_right 5
          exact ht.trans (by decide)
        have hm : Nat.ModEq 3 h 1 := hm3
        have hd : 3∣h*5^(2*(k+1)-1)+1 := Nat.modEq_zero_iff_dvd.mp
          (((hm.mul hpow).add_right 1).trans (by decide))
        apply prime_power_charges hh he hpr ho
        intro hprime
        have hsize := hh.trans (Nat.le_mul_of_pos_right h (pow_pos hpr.pos (2*(k+1)-1)))
        rcases (Nat.dvd_prime hprime).mp hd with H|H <;> omega
    · simp only [idx,if_neg hp5]
      refine ⟨by omega,five_charge hh he hpr ho ?_⟩
      have hnot : ¬5∣p^k := fun hd => hp5
        (((Nat.dvd_prime hpr).mp ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd)).resolve_left (by decide)).symm
      have hsquare := square_mod_five hnot
      rw [show 2*k=k*2 by omega,pow_mul,Nat.mul_mod]
      rcases hm5 with h|h <;> rcases hsquare with hs|hs <;> simp [h,hs]
  have hcount := count_prime_power_indices hb J hJ hS hB hc hout hbal
  have hcard (p : ℕ) : (J p).card=(b.factorization p+1)/2 := by
    dsimp [J]; rw [Finset.card_image_iff.mpr ?_,Finset.card_range]
    intro i _ j _ hij
    dsimp [idx] at hij; split at hij <;> omega
  have hsum : b.primeFactorsList.length≤2*∑ p∈b.primeFactors, (J p).card := by
    rw [← ArithmeticFunction.cardFactors_apply,ArithmeticFunction.cardFactors_eq_sum_factorization,Finset.mul_sum]
    apply Finset.sum_le_sum; intro p _
    change b.factorization p≤2*(J p).card
    rw [hcard]; omega
  omega

theorem uniform_two_count {v h b C c : ℕ} {S : Finset ℕ} (hv : h=2^v) (hh : 16≤h)
    (hb : Odd b) (hS : primeSupport S) (hB : abundancy S<2) (hc : c≠0)
    (hout : ∀ q∈S, ¬q∣c) (hbal : C*(2^(h*b)+1)*demands S=c*primesProduct S) :
    b.primeFactorsList.length ≤
      2*(c.primeFactorsList.length-(c.gcd (C*(2^h+1))).primeFactorsList.length) := by
  have hvpos : v≠0 := by rintro rfl; simp at hv; omega
  have he : Even h := by rw [hv]; exact Even.pow_of_ne_zero (by decide : Even 2) hvpos
  rcases Nat.even_or_odd v with h|h
  · obtain ⟨u,hu⟩ := h
    have hh' : h=(2^u)^2 := by rw [hv,hu,pow_add,pow_two]
    have hm3 : h%3=1 := by
      rw [hv,show v=2*u by omega,pow_mul]
      simpa [Nat.ModEq] using (by decide : Nat.ModEq 3 (2^2) 1).pow u
    have hm5 : h%5=1 ∨ h%5=4 := by
      rw [hh']; exact square_mod_five (fun hd => (by decide : ¬5∣2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd))
    exact double_omega_square hh he hm3 hm5 hb hS hB hc hout hbal
  · obtain ⟨u,hu⟩ := h
    have hm3 : h%3=2 := by
      rw [hv,show v=2*u+1 by omega,pow_succ,pow_mul]
      simpa [Nat.ModEq] using ((by decide : Nat.ModEq 3 (2^2) 1).pow u).mul_right 2
    exact double_omega_bound hh he hm3 hb hS hB hc hout hbal

/-- For a unitary perfect number the odd part has at most two prime factors
with multiplicity per available prime factor of the repeated odd core. -/
theorem two_count_of_perfect {n v h b : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hv : h=2^v) (hh : 16≤h) (hb : Odd b) (hexp : n.factorization 2=h*b) :
    let c := core n
    let K := c.primeFactorsList.length-(c.gcd (oddPart (sigmaU c)*(2^h+1))).primeFactorsList.length
    b.primeFactorsList.length≤2*K := by
  obtain ⟨hc,_,S,_,hpS,hbal,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change Odd (core n) at hc
  change ∀ q∈S, q.Prime ∧ ¬q∣2^n.factorization 2*core n at hpS
  change sigmaU (2^n.factorization 2*core n)*shifted S=2*(2^n.factorization 2*core n)*primesProduct S at hbal
  have ha : 0<n.factorization 2 := by rw [hexp]; exact Nat.mul_pos (by omega) hb.pos
  obtain ⟨hS,hout,hB,hd⟩ := normalize ha hc hc.pos.ne' hpS hbal
  rw [hexp] at hd
  exact uniform_two_count hv hh hb hS hB hc.pos.ne' hout hd

theorem first_layer_charges {v h p : ℕ} (hv : h=2^v) (hh : 16≤h) (hp : p.Prime)
    (ho : Odd p) : requiresCore (layer h p) := by
  have hvpos : v≠0 := by rintro rfl; simp at hv; omega
  have he : Even h := by rw [hv]; exact Even.pow_of_ne_zero (by decide : Even 2) hvpos
  rcases Nat.even_or_odd v with h|h
  · obtain ⟨u,hu⟩ := h
    have hh' : h=(2^u)^2 := by rw [hv,hu,pow_add,pow_two]
    have hm5 : h%5=1 ∨ h%5=4 := by
      rw [hh']; exact square_mod_five (fun hd => (by decide : ¬5∣2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd))
    simpa using (five_charge (j:=0) hh he hp ho (by simpa using hm5))
  · obtain ⟨u,hu⟩ := h
    have hm3 : h%3=2 := by
      rw [hv,show v=2*u+1 by omega,pow_succ,pow_mul]
      simpa [Nat.ModEq] using ((by decide : Nat.ModEq 3 (2^2) 1).pow u).mul_right 2
    have hn : ¬(h+1).Prime := by
      intro H; rcases (Nat.dvd_prime H).mp (show 3∣h+1 by omega) with h|h <;> omega
    simpa using (prime_power_charges (j:=0) hh he hp ho (by simpa using hn))

theorem mixed_count_of_perfect {n v h b : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hv : h=2^v) (hh : 16≤h) (hb : Odd b) (hexp : n.factorization 2=h*b) :
    let c := core n
    b.factorization 3+(b.primeFactors.erase 3).card+
      (c.gcd (oddPart (sigmaU c)*(2^h+1))).primeFactorsList.length≤c.primeFactorsList.length := by
  obtain ⟨hc,_,S,_,hpS,hbal,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change Odd (core n) at hc
  change ∀ q∈S, q.Prime ∧ ¬q∣2^n.factorization 2*core n at hpS
  change sigmaU (2^n.factorization 2*core n)*shifted S=2*(2^n.factorization 2*core n)*primesProduct S at hbal
  have ha : 0<n.factorization 2 := by rw [hexp]; exact Nat.mul_pos (by omega) hb.pos
  obtain ⟨hS,hout,hB,hd⟩ := normalize ha hc hc.pos.ne' hpS hbal
  rw [hexp] at hd
  apply charged_count hh hb _ hS hB hc.pos.ne' hout hd
  intro p hp
  have hp' := Finset.mem_of_mem_erase hp
  exact first_layer_charges hv hh (Nat.prime_of_mem_primeFactors hp') (hb.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp'))

theorem smooth_bound_of_perfect {n v h b L : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hv : h=2^v) (hh : 16≤h) (hb : Odd b) (hexp : n.factorization 2=h*b)
    (hL : 1≤L) (hfac : ∀ p∈b.primeFactorsList, p≤L) :
    let c := core n
    let K := c.primeFactorsList.length-(c.gcd (oddPart (sigmaU c)*(2^h+1))).primeFactorsList.length
    b≤L^(2*K) := by
  have prodBound (fs : List ℕ) (hf : ∀ p∈fs, p≤L) : fs.prod≤L^fs.length := by
    induction fs with
    | nil => simp
    | cons p fs ih =>
      simp only [List.prod_cons,List.length_cons,pow_succ']
      exact Nat.mul_le_mul (hf p List.mem_cons_self) (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))
  have hprod := prodBound _ hfac
  rw [Nat.prod_primeFactorsList hb.pos.ne'] at hprod
  exact hprod.trans (Nat.pow_le_pow_right (by omega) (two_count_of_perfect hn hv hh hb hexp))

end Erdos1052.OddResidue

/- Separation of two disjoint groups in the prime-square core problem. -/

namespace Erdos1052.PrimeSquare

open Erdos1052.CoreBounds Erdos1052.Core625 Erdos1052.OddResidue

def rootExponents (S : Finset ℕ) : Finset ℕ :=
  (S.filter fun q => demand q=1).image fun q => (1+q).factorization 2

def loss (B : ℚ) : ℚ := 1-1/B

private theorem root_power {q : ℕ} (h : demand q=1) :
    2^(1+q).factorization 2=1+q := by
  have H := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
  change 2^(1+q).factorization 2*demand q=1+q at H
  simpa [h] using H

private theorem root_member {S : Finset ℕ} {t : ℕ} (ht : t ∈ rootExponents S) :
    2^t-1 ∈ S := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hs,hd⟩ := Finset.mem_filter.mp hq
  rw [root_power hd]
  simpa using hs

private theorem root_odd {S : Finset ℕ} (hp : primeSupport S) (h3 : 3∉S)
    {t : ℕ} (ht : t∈rootExponents S) : 3≤t ∧ Odd t := by
  have hm := root_member ht
  have hprime := Nat.Prime.of_mersenne (p:=t) (by simpa [mersenne] using (hp _ hm).1)
  have hn : t≠2 := by rintro rfl; exact h3 (by simpa using hm)
  exact ⟨by have := hprime.two_le; omega, hprime.odd_of_ne_two hn⟩

private theorem root_bound {S : Finset ℕ} {D : ℕ} (hp : primeSupport S) (hD : D≠0)
    (hd : demands S ∣ D*primesProduct S) :
    abundancy S ≤ weightProd 1 D * ∏ t∈rootExponents S, mersenneFactor t := by
  have H := compatible_weight_bound S demand (x:=1) (by decide) hD
    (fun q hq => ⟨(hp q hq).1,(hp q hq).1.one_lt,Nat.ordCompl_pos 2 (by omega),
      twice_oddPart_shift_le ((hp q hq).1.odd_of_ne_two (hp q hq).2)⟩) hd
  let R := S.filter fun q => demand q=1
  let e := fun q : ℕ => (1+q).factorization 2
  have he (q : ℕ) (hq : q∈R) : 2^e q=1+q := root_power (Finset.mem_filter.mp hq).2
  have hinj : Set.InjOn e R := by
    intro q hq r hr hh
    have hq' := he q hq
    rw [show e q=e r from hh, he r hr] at hq'
    omega
  have hfactor (q : ℕ) (hq : q∈R) : pathBound q=mersenneFactor (e q) := by
    have HH : (2:ℚ)^e q=1+q := by exact_mod_cast he q hq
    unfold pathBound mersenneFactor; rw [HH]; congr 1 <;> ring
  change abundancy S ≤ weightProd 1 D * ∏ t∈R.image e, mersenneFactor t
  rw [Finset.prod_image hinj, ←Finset.prod_congr rfl hfactor]
  simpa only [R, Finset.prod_filter, abundancy, gain] using H

private theorem one_le_abund (S : Finset ℕ) : 1≤abundancy S :=
  Finset.one_le_prod fun q _ => gain_one_le q

private theorem lower_loss {S : Finset ℕ} (hp : primeSupport S) {t : ℕ}
    (ht : t∈rootExponents S) : 1/(2:ℚ)^t ≤ loss (abundancy S) := by
  let q := 2^t-1
  have hq : q∈S := root_member ht
  have hpos : (0:ℚ)<q := by exact_mod_cast (hp q hq).1.pos
  have hu : (2:ℚ)^t=1+q := by
    exact_mod_cast (show 2^t=1+q by dsimp [q]; have := Nat.two_pow_pos t; omega)
  have hi := one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (gain_one_le q)) (gain_le_total hq)
  have he : 1/(2:ℚ)^t=1-1/gain q := by rw [hu]; unfold gain; field_simp; ring
  unfold loss; rw [he]; linarith

private theorem upper_loss {S : Finset ℕ} {D t : ℕ} (hp : primeSupport S)
    (hD : D≠0) (hd : demands S ∣ D*primesProduct S) (ht : 3≤t)
    (hm : ∀ j∈rootExponents S, t+2≤j ∧ Odd j) :
    loss (abundancy S) ≤ loss (weightProd 1 D)+(2/3)*(1/(2:ℚ)^t) := by
  have hw := (weightProd_bounds (by decide : 1≤1) D).1
  have hb := (root_bound hp hD hd).trans (mul_le_mul_of_nonneg_left
    (odd_roots_product _ (by omega) hm) (zero_le_one.trans hw))
  have hpos := lt_of_lt_of_le zero_lt_one (one_le_abund S)
  have hpw : (8:ℚ)≤2^t := (by exact pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) ht)
  have ht' : oddTail (t+2)= (3*(2:ℚ)^t)/(3*2^t-2) := by
    unfold oddTail
    rw [pow_add,show (2:ℚ)^2=4 by norm_num]
    apply (div_eq_div_iff (by linarith) (by linarith)).mpr
    ring
  rw [ht'] at hb
  have hi := one_div_le_one_div_of_le hpos hb
  let W := weightProd 1 D
  let X : ℚ := 2^t
  change 1 /(W*(3*X/(3*X-2))) ≤ 1/abundancy S at hi
  change 1≤W at hw
  change 8≤X at hpw
  have heq : 1 /(W*(3*X/(3*X-2)))=1/W-(2/3)*(1/X)/W := by field_simp
  rw [heq] at hi
  have hcor : (2/3)*(1/X)/W≤(2/3)*(1/X) := by
    apply div_le_self (by positivity) hw
  change 1-1/abundancy S≤1-1/W+(2/3)*(1/X)
  linarith

/-- The least Mersenne start separates the two reciprocal losses, with a
correction for the prime factors available to the smaller group. -/
theorem separated_groups {S T : Finset ℕ} {D E : ℕ} (hD : D≠0) (hE : E≠0)
    (hS : primeSupport S) (hT : primeSupport T) (hs3 : 3∉S) (ht3 : 3∉T)
    (hdis : Disjoint S T) (hs : demands S∣D*primesProduct S) (ht : demands T∣E*primesProduct T) :
    loss (abundancy S)≤loss (weightProd 1 D)+(2/3)*loss (abundancy T) ∨
      loss (abundancy T)≤loss (weightProd 1 E)+(2/3)*loss (abundancy S) := by
  let K := rootExponents S ∪ rootExponents T
  rcases K.eq_empty_or_nonempty with he|hne
  · have hR : rootExponents S=∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun q hq => Finset.notMem_empty q ((he ▸ Finset.mem_union_left (rootExponents T) hq) : q∈(∅:Finset ℕ)))
    have hb := root_bound hS hD hs
    rw [hR,Finset.prod_empty,mul_one] at hb
    have hu := one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (one_le_abund S)) hb
    have H : 1/abundancy T≤1 := (div_le_one (by linarith [one_le_abund T])).mpr (one_le_abund T)
    left; unfold loss; linarith
  let t := K.min' hne
  have hmem : t∈rootExponents S ∨ t∈rootExponents T := Finset.mem_union.mp (K.min'_mem hne)
  have hsep {U V : Finset ℕ} (hup : primeSupport U) (hu3 : 3∉U)
      (hd' : Disjoint U V) (hv' : t∈rootExponents V)
      (hodd : Odd t) (hsub : rootExponents U ⊆ K) :
      ∀ j∈rootExponents U, t+2≤j ∧ Odd j := by
    intro j hj
    have hle : t≤j := K.min'_le _ (hsub hj)
    have hne' : j≠t := by
      rintro rfl
      exact Finset.disjoint_left.mp hd' (root_member hj) (root_member hv')
    have hjo := (root_odd hup hu3 hj).2
    refine ⟨?_,hjo⟩
    obtain ⟨m,hm⟩ := hodd; obtain ⟨n,hn⟩ := hjo; omega
  rcases hmem with hh|hh
  · right
    have ho := root_odd hS hs3 hh
    have he := upper_loss hT hE ht ho.1
      (hsep hT ht3 hdis.symm hh ho.2 Finset.subset_union_right)
    linarith [lower_loss hS hh]
  · left
    have ho := root_odd hT ht3 hh
    have he := upper_loss hS hD hs ho.1
      (hsep hS hs3 hdis hh ho.2 Finset.subset_union_left)
    linarith [lower_loss hT hh]

theorem competing_losses {S T : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hS : primeSupport S) (hT : primeSupport T) (hs3 : 3∉S) (ht3 : 3∉T)
    (hdis : Disjoint S T) (hs : demands S∣primesProduct S) (ht : demands T∣p*primesProduct T) :
    loss (abundancy S)≤(2/3)*loss (abundancy T) ∨
      loss (abundancy T)≤1/(p:ℚ)+(2/3)*loss (abundancy S) := by
  have hwp : loss (weightProd 1 p)=1/(p:ℚ) := by
    have hp' : (1:ℚ)<p := by exact_mod_cast hp.one_lt
    rw [weightProd_prime _ hp,weight,if_neg (by have := hp.one_lt; omega)]
    unfold loss; field_simp; ring
  have hws : loss (weightProd 1 1)=0 := by norm_num [weightProd,loss]
  simpa only [hwp,hws,zero_add] using
    separated_groups (by decide : (1:ℕ)≠0) hp.ne_zero hS hT hs3 ht3 hdis (by simpa using hs) ht

theorem close_to_power {p u Y Z V A : ℚ} (hp : 0<p) (hu : 0<u) (hY : u≤Y)
    (hZ : Y<Z) (hv : V=p/u/(1+1/Y)) (ha : A=p/u*(1+1/Y)/(1+1/Z))
    (h : loss V≤(2/3)*loss A ∨ loss A≤1/p+(2/3)*loss V) : p-u≤5 := by
  have hY0 := lt_of_lt_of_le hu hY
  have hZ0 := hY0.trans hZ
  let d := (p-u)/p
  have hor : (u/p)/Y≤1/p := by
    apply (div_le_iff₀ hY0).mpr
    rw [div_mul_eq_mul_div,one_mul]
    exact div_le_div_of_nonneg_right hY hp.le
  have hv' : loss V=d-(u/p)/Y := by rw [hv]; unfold loss d; field_simp; ring
  have hadd : loss A=d+(u/p)*((Z-Y)/(Z*(Y+1))) := by
    rw [ha]; unfold loss d
    field_simp
    ring
  have hpos : 0≤(Z-Y)/(Z*(Y+1)) := div_nonneg (by linarith) (by positivity)
  have hlimit : (Z-Y)/(Z*(Y+1))≤1/Y := by
    apply (div_le_div_iff₀ (by positivity) hY0).mpr
    nlinarith [sq_nonneg Y]
  have hmax : (u/p)*((Z-Y)/(Z*(Y+1)))≤(u/p)/Y := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlimit (show 0≤u/p by positivity)
  have hmin : 0≤(u/p)*((Z-Y)/(Z*(Y+1))) := mul_nonneg (by positivity) hpos
  have hVlo : d-1/p≤loss V := by linarith only [hv',hor]
  have hVhi : loss V≤d := by linarith only [hv',show 0≤(u/p)/Y by positivity]
  have hAlo : d≤loss A := by linarith only [hadd,hmin]
  have hAhi : loss A≤d+1/p := by linarith only [hadd,hmax,hor]
  have hfinal : d≤5*(1/p) := by
    rcases h with h|h <;> linarith only [h,hVlo,hVhi,hAlo,hAhi,show 0≤1/p by positivity]
  have hd : d≤5/p := by simpa only [mul_one_div] using hfinal
  exact (div_le_div_iff_of_pos_right hp).mp hd

private theorem dyadic_unique {B R : ℚ} {j k : ℕ} (hB : 1≤B ∧ B<2)
    (hR : 1≤R ∧ R<2) (he : B*2^j=R*2^k) : B=R := by
  have impossible {X Y : ℚ} {a b : ℕ} (hX : 1≤X) (hY : Y<2) (hab : a<b) :
      Y*2^a < X*2^b := by
    calc Y*2^a < 2*2^a := mul_lt_mul_of_pos_right hY (by positivity)
         _ = (2:ℚ)^(a+1) := by rw [pow_succ]; ring
         _ ≤ 2^b := pow_le_pow_right₀ (by norm_num) hab
         _ ≤ X*2^b := le_mul_of_one_le_left (by positivity) hX
  rcases lt_trichotomy j k with hj|rfl|hk
  · exact False.elim ((impossible hR.1 hB.2 hj).ne he)
  · exact mul_right_cancel₀ (by positivity : (2:ℚ)^j≠0) he
  · exact False.elim ((impossible hB.1 hR.2 hk).ne he.symm)

private theorem group_value {S : Finset ℕ} {m D : ℕ} (hp : primeSupport S)
    (hd : m*demands S=D*primesProduct S) :
    (m:ℚ)*abundancy S=(2:ℚ)^twoCount S*D := by
  have h : (m:ℚ)*(demands S:ℚ)=(D:ℚ)*(primesProduct S:ℚ) := by exact_mod_cast hd
  have hz : primesProduct S≠0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hp q hq).1.ne_zero
  apply mul_right_cancel₀ (by exact_mod_cast hz : (primesProduct S:ℚ)≠0)
  rw [mul_assoc,abundancy_cross hp,shifted_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linear_combination ((2:ℚ)^twoCount S)*h

private theorem window {p k h : ℕ} (hl : 2^k<p) (hu : p<2^(k+1)) (hh : 4≤h)
    (hf : p≤2^h+1) : 2^k≤2^h ∧ p*(2^h+1)<2*2^k*2^h := by
  have hY : 16≤2^h := Nat.pow_le_pow_right (n:=2) (by decide) hh
  constructor
  · omega
  rw [pow_succ] at hu
  by_cases hc : k<h
  · have hU := Nat.pow_le_pow_right (n:=2) (by decide) (show k+1≤h by omega)
    rw [pow_succ] at hU
    nlinarith [Nat.mul_le_mul (show p+1≤2*2^k by omega) (le_refl (2^h))]
  · have hmid := Nat.pow_le_pow_right (n:=2) (by decide) (show h≤k by omega)
    have he : p=2^h+1 := by omega
    nlinarith [Nat.mul_le_mul hmid (le_refl (2^h)),Nat.mul_le_mul (show 3≤2^h by omega) (le_refl (2^h))]

private theorem ratio_ranges {P U Y Z : ℚ} (hU : 0<U) (hP : U+1≤P)
    (hUY : U≤Y) (hZ : Y<Z) (hP2 : P<2*U) (hw : P*(Y+1)<2*U*Y) :
    (1≤P/U/(1+1/Y) ∧ P/U/(1+1/Y)<2) ∧
    (1≤P/U*(1+1/Y)/(1+1/Z) ∧ P/U*(1+1/Y)/(1+1/Z)<2) := by
  have hY := hU.trans_le hUY
  have hZ0 := hY.trans hZ
  have hx : 1≤P/U := (one_le_div hU).mpr (by linarith)
  have hB : 0<1+1/Y := by positivity
  have hB' : 0<1+1/Z := by positivity
  have hv : 1+1/Y≤P/U := by
    apply (le_div_iff₀ hU).mpr
    have e : (1+1/Y)*U=U+U/Y := by ring
    rw [e]
    linarith [(div_le_one hY).mpr hUY]
  have hsmall : P/U*(1+1/Y)<2 := by
    apply (lt_of_mul_lt_mul_right (a:=U*Y) _ (by positivity))
    calc P/U*(1+1/Y)*(U*Y) = P*(Y+1) := by field_simp
         _ < 2*(U*Y) := by linarith
  refine ⟨⟨(one_le_div hB).mpr hv,(div_lt_iff₀ hB).mpr ?_⟩,
    ⟨(one_le_div hB').mpr ?_,(div_lt_iff₀ hB').mpr ?_⟩⟩
  · have hu := (div_lt_iff₀ hU).mpr (show P<2*U from hP2)
    linarith [show 0<1/Y by positivity]
  · have hInv := one_div_le_one_div_of_le hY hZ.le
    exact (show 1+1/Z≤1+1/Y by linarith).trans (le_mul_of_one_le_left hB.le hx)
  · linarith [show 0<1/Z by positivity]

/-- The balance for the neutral Fermat cofactor and the group using p
determines both abundancies, including their powers of two. -/
theorem square_ratios {S T : Finset ℕ} {p k h b V A : ℕ}
    (hS : primeSupport S) (hT : primeSupport T) (hBS : abundancy S<2) (hBT : abundancy T<2)
    (hl : 2^k<p) (hu : p<2^(k+1)) (hh : 4≤h) (hb : 1<b)
    (hV : p*V=2^h+1) (hA : A*(2^h+1)=2^(h*b)+1)
    (hs : V*demands S=primesProduct S) (ht : A*demands T=p*primesProduct T) :
    abundancy S=(p:ℚ)/2^k/(1+1/2^h) ∧
    abundancy T=(p:ℚ)/2^k*(1+1/2^h)/(1+1/2^(h*b)) := by
  have hp0 : 0<p := by omega
  have hdiv : p∣2^h+1 := ⟨V,hV.symm⟩
  have hbound := window hl hu hh (Nat.le_of_dvd (by positivity) hdiv)
  have hN : h<h*b := by nlinarith [Nat.mul_le_mul (le_refl h) (show 2≤b by omega)]
  have hZ : (2:ℚ)^h<2^(h*b) := pow_lt_pow_right₀ (by norm_num) hN
  have hP : 0<(p:ℚ) := by exact_mod_cast hp0
  have hbound' : (p:ℚ)*((2:ℚ)^h+1)<2*2^k*2^h := by exact_mod_cast hbound.2
  have hp2 : (p:ℚ)<2*2^k := by rw [pow_succ] at hu; exact_mod_cast (by omega : p<2*2^k)
  have hr := ratio_ranges (by positivity : (0:ℚ)<2^k) (by exact_mod_cast (show 2^k+1≤p by omega))
    (by exact_mod_cast hbound.1) hZ hp2 hbound'
  have vp : (p:ℚ)*V=(2:ℚ)^h+1 := by exact_mod_cast hV
  have ap : (A:ℚ)*((2:ℚ)^h+1)=(2:ℚ)^(h*b)+1 := by exact_mod_cast hA
  have ss := group_value hS (D:=1) (by simpa using hs)
  have ts := group_value hT ht
  rw [Nat.cast_one,mul_one] at ss
  constructor
  · apply dyadic_unique (j:=h) (k:=twoCount S+k) ⟨one_le_abund S,hBS⟩ hr.1
    rw [pow_add]
    field_simp
    linear_combination p*ss - abundancy S*vp
  · apply dyadic_unique (j:=h*b) (k:=twoCount T+k+h) ⟨one_le_abund T,hBT⟩ hr.2
    rw [pow_add,pow_add]
    field_simp
    linear_combination ((2:ℚ)^h+1)*ts - abundancy T*ap

theorem short_gap_forces_Fermat {p k v : ℕ} (hp : 5<p) (hv : 4≤v)
    (hl : 2^k<p) (hu : p<2^(k+1)) (hd : 2^(v+1)∣p-1) (hgap : p-2^k≤5) :
    p=2^k+1 := by
  have hbase : 32≤2^(v+1) := Nat.pow_le_pow_right (n:=2) (by decide) (show 5≤v+1 by omega)
  have hle := Nat.le_of_dvd (by omega : 0<p-1) hd
  have hvk : v+1≤k := by
    by_contra! hh
    have := Nat.pow_le_pow_right (n:=2) (by decide) (show k+1≤v+1 by omega)
    omega
  have hd' : 2^(v+1)∣p-1-2^k := Nat.dvd_sub hd (pow_dvd_pow 2 hvk)
  by_contra h
  have := Nat.le_of_dvd (by omega : 0<p-1-2^k) hd'
  omega

theorem five_divides_Fermat_square {p k : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (he : p=2^k+1) : 5∣p^2+1 := by
  have hmod (m : ℕ) (h : Nat.ModEq m (2^4) 1) : Nat.ModEq m (2^k) (2^(k%4)) := by
    conv_lhs => rw [show k=4*(k/4)+k%4 by omega,pow_add,pow_mul]
    simpa using (h.pow (k/4)).mul_right (2^(k%4))
  have h3 := hmod 3 (by decide)
  have h5 := hmod 5 (by decide)
  have hu : ¬3∣p := by intro hh; rcases (Nat.dvd_prime hp).mp hh with h|h <;> omega
  have hv : ¬5∣p := by intro hh; rcases (Nat.dvd_prime hp).mp hh with h|h <;> omega
  have hc := Nat.mod_lt k (by decide : 0<4)
  interval_cases hk : k%4 <;> norm_num [Nat.ModEq] at h3 h5
  · obtain ⟨q,hq⟩ : 5∣p-2 := by omega
    have hh : p=5*q+2 := by omega
    rw [hh]
    exact ⟨5*q^2+4*q+1,by ring⟩
  all_goals omega

/-- The prime-square arithmetic balance is incompatible with an odd
multiplier greater than one under the sparse Fermat-order and support conditions. -/
theorem prime_square_group_exclusion {S T : Finset ℕ} {p k v h b V A : ℕ}
    (hp : p.Prime) (hp5 : 5<p) (hf : ¬5∣p^2+1) (hv : 4≤v) (hh : h=2^v)
    (ho : 2^(v+1)∣p-1) (hl : 2^k<p) (hu : p<2^(k+1)) (hb : 1<b)
    (hV : p*V=2^h+1) (hA : A*(2^h+1)=2^(h*b)+1)
    (hS : primeSupport S) (hT : primeSupport T) (hs3 : 3∉S) (ht3 : 3∉T)
    (hdis : Disjoint S T) (hBS : abundancy S<2) (hBT : abundancy T<2)
    (hs : V*demands S=primesProduct S) (ht : A*demands T=p*primesProduct T) : False := by
  have hlarge : 16≤h := hh ▸ Nat.pow_le_pow_right (n:=2) (by decide) hv
  obtain ⟨hsv,hta⟩ := square_ratios hS hT hBS hBT hl hu (by omega) hb hV hA hs ht
  have hs' : demands S∣primesProduct S := hs ▸ dvd_mul_left _ _
  have ht' : demands T∣p*primesProduct T := ht ▸ dvd_mul_left _ _
  have sep := competing_losses hp hS hT hs3 ht3 hdis hs' ht'
  have hd : p∣2^h+1 := ⟨V,hV.symm⟩
  have hwin := window hl hu (by omega) (Nat.le_of_dvd (by positivity) hd)
  have hz : (2:ℚ)^h<2^(h*b) := pow_lt_pow_right₀ (by norm_num)
    (by nlinarith [Nat.mul_le_mul (le_refl h) (show 2≤b by omega)] : h<h*b)
  have hgap := close_to_power (by exact_mod_cast hp.pos : (0:ℚ)<p) (by positivity : (0:ℚ)<2^k)
    (by exact_mod_cast hwin.1) hz hsv hta sep
  have ha : (p:ℚ)≤2^k+5 := by linarith
  have han : p≤2^k+5 := by exact_mod_cast ha
  exact hf (five_divides_Fermat_square hp hp5 (short_gap_forces_Fermat hp5 hv hl hu ho (by omega)))

open Erdos1052.OddExponent Erdos1052.DistinctFactors

private theorem subgroup_le {U S : Finset ℕ} (h : U⊆S) : abundancy U≤abundancy S :=
  Finset.prod_le_prod_of_subset_of_one_le h (fun q _ => zero_le_one.trans (gain_one_le q))
    (fun q _ _ => gain_one_le q)

private theorem odd_quotient_charged {h v b : ℕ} (hv : h=2^v) (hh : 16≤h)
    (hb : Odd b) (hb1 : 1<b) :
    ∃ A, A*(2^h+1)=2^(h*b)+1 ∧ requiresCore A := by
  obtain ⟨r,hr,hrb⟩ := Nat.exists_prime_and_dvd (by omega : b≠1)
  have hd := independent_layers h hb odd_one (one_dvd b) {r} (by
    intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact ⟨hrb,fun h => hr.ne_one (Nat.dvd_one.mp h)⟩)
  simp only [Finset.prod_singleton,mul_one] at hd
  obtain ⟨j,hj⟩ := hd
  refine ⟨layer h r*j,by rw [hj]; ac_rfl,?_⟩
  intro S hp D hbal hB h1
  subst D
  obtain ⟨T,U,d,e,_,hunion,hde,ht,_⟩ := split_support S hp hbal
  have hT : T⊆S := hunion ▸ Finset.subset_union_left
  exact first_layer_charges hv hh hr (hb.of_dvd_nat hrb) T (fun q hq => hp q (hT hq)) d ht
    ((subgroup_le hT).trans_lt hB) (by simpa using (Nat.dvd_one.mp (show d∣1 from ⟨e,hde.symm⟩)))

private theorem five_forces_three {S : Finset ℕ} {m D : ℕ} (hp : primeSupport S)
    (hD : ¬3∣D) (he : m*demands S=D*primesProduct S) (h5 : 5∈S) : 3∈S := by
  have h3 : (3:ℕ).Prime := by decide
  have hd : 3∣demands S := by
    have h : demand 5=3 := by
      change oddPart (2^1*3)=3
      rw [show oddPart (2^1*3)=oddPart 3 from Nat.ordCompl_self_pow_mul _ _ Nat.prime_two]
      exact (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (.inr (by decide))
    exact h ▸ Finset.dvd_prod_of_mem demand h5
  have hprod := (h3.dvd_mul.mp (he ▸ dvd_mul_of_dvd_right hd m)).resolve_left hD
  obtain ⟨q,hq,hq'⟩ := ((Nat.prime_iff.mp h3).dvd_finsetProd_iff id).mp hprod
  simpa only [((Nat.prime_dvd_prime_iff_eq h3 (hp q hq).1).mp hq').symm] using hq

private theorem three_five_bound {S : Finset ℕ} (h3 : 3∈S) (h5 : 5∈S) :
    (8/5:ℚ)≤abundancy S := by
  have sub : ({3,5}:Finset ℕ)⊆S := fun q hq => by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl <;> assumption
  exact (by norm_num [abundancy,gain] : (8/5:ℚ)=abundancy {3,5}).le.trans (subgroup_le sub)

private theorem small_groups {x Y Z V A : ℚ} (hx : 0<x) (hY : 32≤Y)
    (hZ : Y<Z) (hv : V=x/(1+1/Y)) (ha : A=x*(1+1/Y)/(1+1/Z))
    (hb : V*A<2) : V<8/5 ∧ A<8/5 := by
  have Ypos : 0<Y := by linarith
  have Zpos : 0<Z := by linarith
  have h32 : 1/Z≤1/32 := one_div_le_one_div_of_le (by norm_num) (hY.trans hZ.le)
  have h32' : 1/Y≤1/32 := one_div_le_one_div_of_le (by norm_num) hY
  have he : V*A=x^2/(1+1/Z) := by rw [hv,ha]; field_simp
  rw [he,div_lt_iff₀ (by positivity)] at hb
  have hx' : x<3/2 := by nlinarith [sq_nonneg (x-3/2)]
  have hV : V≤x := by rw [hv]; exact div_le_self hx.le (by linarith [show 0≤1/Y by positivity])
  have hA : A≤x*(1+1/Y) := by
    rw [ha]; exact div_le_self (by positivity) (by linarith [show 0≤1/Z by positivity])
  have hu := mul_le_mul h32' hx'.le hx.le (by norm_num : (0:ℚ)≤1/32)
  constructor <;> nlinarith

/-- Starting from the full odd-part balance for a prime square, the sparse
hypotheses force the entire odd multiplier to equal one. -/
theorem prime_square_odd_part {S : Finset ℕ} {p v h b C : ℕ}
    (hp : p.Prime) (hp5 : 5<p) (hf : ¬5∣p^2+1) (hv : 4≤v) (hh : h=2^v)
    (ho : 2^(v+1)∣p-1) (hF : p∣2^h+1) (hb : Odd b)
    (hS : primeSupport S) (h5 : 5∈S) (hB : abundancy S<2)
    (hbal : C*(2^(h*b)+1)*demands S=p^2*primesProduct S) : b=1 := by
  by_contra hn
  have hb1 : 1<b := by have := hb.pos; omega
  have hh16 : 16≤h := hh ▸ Nat.pow_le_pow_right (n:=2) (by decide) hv
  obtain ⟨A,hA,hcharge⟩ := odd_quotient_charged hh hh16 hb hb1
  obtain ⟨V,hV'⟩ := hF
  have he : A*(V*C)*demands S=p*primesProduct S := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc p*(A*(V*C)*demands S) = C*(A*(p*V))*demands S := by ring
         _ = p^2*primesProduct S := by rwa [←hV',hA]
         _ = p*(p*primesProduct S) := by ring
  obtain ⟨T,W,d,e,hd,hTW,hde,ht,hw⟩ := split_support S hS he
  have hT : T⊆S := hTW ▸ Finset.subset_union_left
  have hW : W⊆S := hTW ▸ Finset.subset_union_right
  have hTp : primeSupport T := fun q hq => hS q (hT hq)
  have hWp : primeSupport W := fun q hq => hS q (hW hq)
  have hd1 := hcharge T hTp d ht ((subgroup_le hT).trans_lt hB)
  have hdp := ((Nat.dvd_prime hp).mp (show d∣p from ⟨e,hde.symm⟩)).resolve_left hd1
  subst d
  have he1 : e=1 := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using hde : p*e=p*1)
  subst e
  obtain ⟨U,K,i,j,hdis,hUK,hij,hu,hc⟩ := split_support W hWp hw
  have hi : i=1 := Nat.dvd_one.mp ⟨j,hij.symm⟩
  subst i
  have hj : j=1 := by simpa using hij
  subst j
  have hU : U⊆W := hUK ▸ Finset.subset_union_left
  have hK : K⊆W := hUK ▸ Finset.subset_union_right
  have hUp : primeSupport U := fun q hq => hWp q (hU hq)
  have hKp : primeSupport K := fun q hq => hWp q (hK hq)
  have huv : V*demands U=primesProduct U := by simpa using hu
  let k := Nat.log 2 p
  have hupp : p<2^(k+1) := Nat.lt_pow_succ_log_self (by decide) p
  have hlo : 2^k<p := by
    refine lt_of_le_of_ne (Nat.pow_log_le_self 2 hp.ne_zero) ?_
    intro hh'
    have h2 : 2∣p := by
      rw [←hh']; exact dvd_pow_self 2 (by intro h0; rw [h0, pow_zero] at hh'; omega)
    exact (hp.odd_of_ne_two (by omega)).not_two_dvd_nat h2
  have huB := (subgroup_le (hU.trans hW)).trans_lt hB
  have htB := (subgroup_le hT).trans_lt hB
  obtain ⟨ru,rt⟩ := square_ratios hUp hTp huB htB hlo hupp (by omega) hb1 hV'.symm hA huv ht
  have dut : Disjoint U T := hd.symm.mono_left hU
  have total : abundancy U*abundancy T<2 := by
    have h := (subgroup_le (Finset.union_subset (hU.trans hW) hT)).trans_lt hB
    simpa only [abundancy,Finset.prod_union dut] using h
  have hY : (32:ℚ)≤2^h := (by exact pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (by omega : 5≤h))
  have hZ : (2:ℚ)^h<2^(h*b) := pow_lt_pow_right₀ (by norm_num)
    (by nlinarith [Nat.mul_le_mul (le_refl h) (show 2≤b by omega)] : h<h*b)
  have hx : (0:ℚ)<p/2^k := div_pos (by exact_mod_cast hp.pos) (by positivity)
  have ⟨us,ts⟩ := small_groups hx
    hY hZ ru rt total
  have np : ¬3∣p := by intro H; rcases (Nat.dvd_prime hp).mp H with h|h <;> omega
  have t5 : 5∉T := fun H => (three_five_bound (five_forces_three hTp np ht H) H).not_gt ts
  have u5 : 5∉U := fun H => (three_five_bound (five_forces_three hUp (by decide) hu H) H).not_gt us
  have k5 : 5∈K := by
    rw [←hTW,Finset.mem_union] at h5
    have hw5 := h5.resolve_left t5
    rw [←hUK,Finset.mem_union] at hw5
    exact hw5.resolve_left u5
  have k3 := five_forces_three hKp (by decide) hc k5
  exact prime_square_group_exclusion hp hp5 hf hv hh ho hlo hupp hb1 hV'.symm hA
    hUp hTp (fun H => Finset.disjoint_left.mp hdis H k3)
    (fun H => Finset.disjoint_left.mp hd H (hK k3)) dut huB htB huv ht

/-- For a unitary perfect number with repeated odd core p², the cited
sparse-core conditions on its prime factors and on h imply a=h. -/
theorem prime_square_of_perfect {n p v h b : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hc : core n=p^2) (hp : p.Prime) (hp5 : 5<p) (hf : ¬5∣p^2+1) (hv : 4≤v)
    (hh : h=2^v) (ho : 2^(v+1)∣p-1) (hF : p∣2^h+1) (hb : Odd b)
    (hexp : n.factorization 2=h*b) (h5 : 5∣n) : n.factorization 2=h := by
  obtain ⟨hcOdd,_,S,_,hS,hbal,hprod,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change Odd (core n) at hcOdd
  change ∀ q∈S, q.Prime ∧ ¬q∣2^n.factorization 2*core n at hS
  change sigmaU (2^n.factorization 2*core n)*shifted S=2*(2^n.factorization 2*core n)*primesProduct S at hbal
  change n=2^n.factorization 2*core n*primesProduct S at hprod
  have ha : 0<n.factorization 2 := by rw [hexp,hh]; exact Nat.mul_pos (by positivity) hb.pos
  obtain ⟨hsp,_,hB,hd⟩ := normalize ha hcOdd hcOdd.pos.ne' hS hbal
  rw [hc,hexp] at hd
  have hpFive : (5:ℕ).Prime := by decide
  have hn5 : ¬5∣2^n.factorization 2*core n := by
    rw [hc]
    intro H
    rcases hpFive.dvd_mul.mp H with h|h
    · exact (by decide : ¬5∣2) (hpFive.dvd_of_dvd_pow h)
    · have he := (Nat.prime_dvd_prime_iff_eq hpFive hp).mp (hpFive.dvd_of_dvd_pow h)
      omega
  have h5p := (hpFive.dvd_mul.mp (hprod ▸ h5)).resolve_left hn5
  obtain ⟨q,hq,hq'⟩ := ((Nat.prime_iff.mp hpFive).dvd_finsetProd_iff id).mp h5p
  have h5S : 5∈S := by simpa only [((Nat.prime_dvd_prime_iff_eq hpFive (hsp q hq).1).mp hq').symm] using hq
  rw [hexp,prime_square_odd_part hp hp5 hf hv hh ho hF hb hsp h5S hB hd,mul_one]

end Erdos1052.PrimeSquare

namespace Erdos1052.Stripped

open Erdos1052.CoreBounds Erdos1052.Core625

/-- Remove all powers of p from every demand. The remaining supply is
independent of the multiplicity of p available in the original group. -/
theorem strip_balance {S : Finset ℕ} {p u D : ℕ} (hp : p.Prime)
    (hd : demands S∣p^u*(D*primesProduct S)) :
    (∏ q∈S, ordCompl[p] (demand q))∣D*primesProduct S := by
  have hprod (T : Finset ℕ) : ordCompl[p] (demands T) = ∏ q∈T, ordCompl[p] (demand q) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert q T hq ih =>
      simp only [demands,Finset.prod_insert hq] at ih ⊢
      rw [Nat.ordCompl_mul,ih]
  have H := Nat.ordCompl_dvd_ordCompl_of_dvd hd p
  rw [hprod, Nat.ordCompl_self_pow_mul _ _ hp] at H
  exact H.trans (Nat.ordCompl_dvd _ _)

/-- A compatible group's tail is controlled by the simple tokens and
starts q whose odd shift is a power of p. -/
theorem strip_tail {S : Finset ℕ} {p u D x : ℕ} (hp : p.Prime) (hx : 1≤x)
    (hD : D≠0) (hS : primeSupport S) (hcut : ∀ q∈S, x<q)
    (hd : demands S∣p^u*(D*primesProduct S)) :
    abundancy S ≤ weightProd x D *
      ∏ q∈S, (if ordCompl[p] (demand q)=1 then pathBound q else 1) := by
  apply compatible_weight_bound S (fun q => ordCompl[p] (demand q)) hx hD _ (strip_balance hp hd)
  intro q hq
  obtain ⟨hpr,h2⟩ := hS q hq
  refine ⟨hpr,hcut q hq,Nat.ordCompl_pos _ (Nat.ordCompl_pos 2 (by omega)).ne',?_⟩
  exact (Nat.mul_le_mul_left 2 (Nat.ordCompl_le _ _)).trans
    (twice_oddPart_shift_le (hpr.odd_of_ne_two h2))

end Erdos1052.Stripped
