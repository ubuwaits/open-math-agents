import OMAReductions.R_Erdos1052_erdos_1052_R2
import Mathlib.NumberTheory.LucasPrimality

/-!
# Repeated cores whose only prime is 65537

A prime divisor of a core shift and its descending shifts can exhaust the
multiplicity of a smaller prime. The modular and primality certificates
give uniform exclusions for whole classes of the exponent of 65537.
-/

namespace Erdos1052.CoreBounds

abbrev sigmaU (b : ℕ) := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)

def Admits (c a : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
    sigmaU (2 ^ a * c) * (∏ q ∈ S, (1 + q)) = (2 * (2 ^ a * c)) * ∏ q ∈ S, q

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

end Erdos1052.CoreBounds



namespace Erdos1052.CoreFermat

open Erdos1052.CoreBounds

private def modPower {M : Type*} [Monoid M] : ℕ → ℕ → M → M → M
  | 0, _, _, y => y
  | t+1, k, x, y => modPower t (k/2) (x*x) (if k%2=0 then y else y*x)

private theorem modPower_spec {M : Type*} [CommMonoid M] (t k : ℕ) (x y : M)
    (hk : k<2^t) : modPower t k x y=y*x^k := by
  induction t generalizing x y k with
  | zero =>
    have hk0 : k=0 := by simpa using hk
    simp [modPower,hk0]
  | succ t ih =>
    have hhalf : k/2<2^t := by rw [pow_succ] at hk; omega
    rw [modPower,ih _ _ _ hhalf,← pow_two,← pow_mul]
    split
    · congr 2
      omega
    · rw [mul_assoc,← pow_succ']
      congr 2
      omega

private theorem pow_certificate {p g k z : ℕ} (hk : k<2^48)
    (h : modPower 48 k (g : ZMod p) 1 = (z : ZMod p)) :
    (g : ZMod p)^k=(z : ZMod p) := by
  simpa only [modPower_spec _ _ _ _ hk,one_mul] using h

theorem forced_shifts {a e : ℕ} (he : 0<e) (h : Admits (65537^e) a) :
    ∃ S : Finset ℕ,
    (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 65537 → r ∣ 1+65537^e → r∈S) ∧
    (∀ x ∈ S, ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 65537 → r ∣ 1+x → r∈S) ∧
    (∀ x ∈ S, ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 65537 → ¬p^2 ∣ 1+x) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 65537 →
      p ∣ 1+x → ¬p ∣ 1+y) := by
  have hp : Nat.Prime 65537 := by norm_num1
  let b := 2^a*65537^e
  have hb : b≠0 := by dsimp [b]; positivity
  have outside {r : ℕ} (hr : r.Prime) (h₂ : r≠2) (hₚ : r≠65537) : ¬r ∣ 2*b := by
    have h2 : ¬r ∣ 2 := fun hd => h₂ ((Nat.prime_two.dvd_iff_eq hr.ne_one).mp hd).symm
    have hP : ¬r ∣ 65537 := fun hd => hₚ ((hp.dvd_iff_eq hr.ne_one).mp hd).symm
    intro hd
    rcases hr.dvd_mul.mp ((hr.dvd_mul.mp hd).resolve_left h2) with h1 | h1
    · exact h2 (hr.dvd_of_dvd_pow h1)
    · exact hP (hr.dvd_of_dvd_pow h1)
  obtain ⟨S,hS,hbal⟩ := h
  change sigmaU b * _ = 2*b * _ at hbal
  have hpb : 65537∈b.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp,dvd_mul_of_dvd_right (dvd_pow_self 65537 he.ne') _,hb⟩
  have hev : b.factorization 65537=e := by
    simp [b,Nat.factorization_mul (Nat.two_pow_pos a).ne' (pow_ne_zero e hp.ne_zero),
      Nat.prime_two.factorization_pow,hp.factorization_pow]
  have hs : 1+65537^e ∣ sigmaU b := by simpa only [hev] using sigma_factor hpb
  have shift {x : ℕ} (hx : x∈S) : 1+x ∣ ∏ q ∈ S, (1+q) := Finset.dvd_prod_of_mem _ hx
  have nosquare {p : ℕ} (hp' : p.Prime) (h2 : p≠2) (hP : p≠65537) :
      ¬ p^2 ∣ sigmaU b*(∏ q ∈ S, (1+q)) := by
    rw [hbal]
    exact square_obstruction hp' (mul_ne_zero (by decide) hb) (outside hp' h2 hP) hS
  refine ⟨S,fun r hr h2 hP hd => forced_member hr (outside hr h2 hP) hS hbal
    (dvd_mul_of_dvd_left (hd.trans hs) _),
    fun x hx r hr h2 hP hd => forced_member hr (outside hr h2 hP) hS hbal
      (dvd_mul_of_dvd_right (hd.trans (shift hx)) _),
    fun x hx p hp' h2 hP hd => nosquare hp' h2 hP
      (dvd_mul_of_dvd_right (hd.trans (shift hx)) _),?_⟩
  intro x hx y hy hxy p hp' h2 hP hpx hpy
  have hsub : ({x,y} : Finset ℕ) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    exact hz.elim (fun h => h ▸ hx) (fun h => h ▸ hy)
  have hd := Finset.prod_dvd_prod_of_subset {x,y} S (fun z : ℕ => 1+z) hsub
  have hd' : (1+x)*(1+y) ∣ ∏ q ∈ S, (1+q) := by simpa [hxy] using hd
  exact nosquare hp' h2 hP (dvd_mul_of_dvd_right
    (by simpa [pow_two] using (Nat.mul_dvd_mul hpx hpy).trans hd') _)

private theorem odd_multiple_seed {d r : ℕ} (k : ℕ) (hr : r ∣ 65537^d+1) :
    r ∣ 1+65537^(d*(2*k+1)) := by
  have hodd : Odd (2*k+1) := ⟨k,rfl⟩
  have h := hodd.nat_add_dvd_pow_add_pow (65537^d) 1
  rw [one_pow,← pow_mul] at h
  rw [Nat.add_comm]
  exact hr.trans h

-- Computed prime certificates use the order of the displayed witness modulo p.
private theorem pow_not_one_certificate {p g k : ℕ} (hk : k<2^48)
    (h : modPower 48 k (g : ZMod p) 1 ≠ 1) : (g : ZMod p)^k≠1 := by
  simpa only [modPower_spec _ _ _ _ hk,one_mul] using h

private theorem modular_seed {r d : ℕ} (hd : d<2^48)
    (hv : modPower 48 d (65537 : ZMod r) 1 + 1 = 0) : r ∣ 65537^d+1 := by
  apply (ZMod.natCast_eq_zero_iff (65537^d+1) r).mp
  push_cast
  simpa only [modPower_spec _ _ _ _ hd,one_mul] using hv

private theorem prime_70657 : Nat.Prime 70657 := by
  apply lucas_primality 70657 (7 : ZMod 70657)
  · exact pow_certificate (g:=7) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 70657-1 ≠ 0)⟩
    rw [show (70657-1 : ℕ).primeFactors = {2,3,23} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=7) (by decide) (by decide +kernel)

private theorem prime_752299 : Nat.Prime 752299 := by
  apply lucas_primality 752299 (2 : ZMod 752299)
  · exact pow_certificate (g:=2) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 752299-1 ≠ 0)⟩
    rw [show (752299-1 : ℕ).primeFactors = {2,3,125383} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=2) (by decide) (by decide +kernel)

private theorem prime_786433 : Nat.Prime 786433 := by
  apply lucas_primality 786433 (10 : ZMod 786433)
  · exact pow_certificate (g:=10) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 786433-1 ≠ 0)⟩
    rw [show (786433-1 : ℕ).primeFactors = {2,3} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    all_goals exact pow_not_one_certificate (g:=10) (by decide) (by decide +kernel)

private theorem prime_3604481 : Nat.Prime 3604481 := by
  apply lucas_primality 3604481 (3 : ZMod 3604481)
  · exact pow_certificate (g:=3) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 3604481-1 ≠ 0)⟩
    rw [show (3604481-1 : ℕ).primeFactors = {2,5,11} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=3) (by decide) (by decide +kernel)

private theorem prime_4513793 : Nat.Prime 4513793 := by
  apply lucas_primality 4513793 (3 : ZMod 4513793)
  · exact pow_certificate (g:=3) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 4513793-1 ≠ 0)⟩
    rw [show (4513793-1 : ℕ).primeFactors = {2,19,29} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=3) (by decide) (by decide +kernel)

private theorem prime_170557441 : Nat.Prime 170557441 := by
  apply lucas_primality 170557441 (11 : ZMod 170557441)
  · exact pow_certificate (g:=11) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 170557441-1 ≠ 0)⟩
    rw [show (170557441-1 : ℕ).primeFactors = {2,3,5,347} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=11) (by decide) (by decide +kernel)

private theorem prime_211812353 : Nat.Prime 211812353 := by
  apply lucas_primality 211812353 (3 : ZMod 211812353)
  · exact pow_certificate (g:=3) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 211812353-1 ≠ 0)⟩
    rw [show (211812353-1 : ℕ).primeFactors = {2,101} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    all_goals exact pow_not_one_certificate (g:=3) (by decide) (by decide +kernel)

private theorem prime_341114881 : Nat.Prime 341114881 := by
  apply lucas_primality 341114881 (11 : ZMod 341114881)
  · exact pow_certificate (g:=11) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 341114881-1 ≠ 0)⟩
    rw [show (341114881-1 : ℕ).primeFactors = {2,3,5,347} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=11) (by decide) (by decide +kernel)

private theorem prime_730882049 : Nat.Prime 730882049 := by
  apply lucas_primality 730882049 (3 : ZMod 730882049)
  · exact pow_certificate (g:=3) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 730882049-1 ≠ 0)⟩
    rw [show (730882049-1 : ℕ).primeFactors = {2,13,6863} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=3) (by decide) (by decide +kernel)

private theorem prime_2967994369 : Nat.Prime 2967994369 := by
  apply lucas_primality 2967994369 (13 : ZMod 2967994369)
  · exact pow_certificate (g:=13) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 2967994369-1 ≠ 0)⟩
    rw [show (2967994369-1 : ℕ).primeFactors = {2,3,17,37} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=13) (by decide) (by decide +kernel)

private theorem prime_3238002689 : Nat.Prime 3238002689 := by
  apply lucas_primality 3238002689 (3 : ZMod 3238002689)
  · exact pow_certificate (g:=3) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 3238002689-1 ≠ 0)⟩
    rw [show (3238002689-1 : ℕ).primeFactors = {2,193} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    all_goals exact pow_not_one_certificate (g:=3) (by decide) (by decide +kernel)

private theorem prime_14379237889 : Nat.Prime 14379237889 := by
  apply lucas_primality 14379237889 (29 : ZMod 14379237889)
  · exact pow_certificate (g:=29) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 14379237889-1 ≠ 0)⟩
    rw [show (14379237889-1 : ℕ).primeFactors = {2,3,23,191,2131} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=29) (by decide) (by decide +kernel)

private theorem prime_2478250459649 : Nat.Prime 2478250459649 := by
  apply lucas_primality 2478250459649 (3 : ZMod 2478250459649)
  · exact pow_certificate (g:=3) (z:=1) (by decide) (by decide +kernel)
  · intro q hq hd
    have hm := Nat.mem_primeFactors.mpr ⟨hq,hd,(by decide : 2478250459649-1 ≠ 0)⟩
    rw [show (2478250459649-1 : ℕ).primeFactors = {2,47,241,427327} by decide +kernel] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals exact pow_not_one_certificate (g:=3) (by decide) (by decide +kernel)

/-- Each listed two-part of the core exponent excludes every exponent of 2. -/
theorem no_65537_shift_classes (a k d : ℕ) (hd : d ∈ ({128,256,512,1024,2048,4096,32768,131072,262144,1048576,8388608} : Finset ℕ)) :
    ¬ Admits (65537^(d*(2*k+1))) a := by
  have hd0 : 0<d := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    omega
  intro h
  obtain ⟨S,hseed,hnext,hsquare,hdup⟩ := forced_shifts (Nat.mul_pos hd0 (by omega)) h
  have first (r : ℕ) (hr : r.Prime) (h2 : r≠2) (hp : r≠65537) (hs : r ∣ 65537^d+1) :
      r∈S := hseed r hr h2 hp (odd_multiple_seed k hs)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h14379237889 := first 14379237889 prime_14379237889 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    have h5 := hnext 14379237889 h14379237889 5 (by norm_num1) (by decide) (by decide) (by decide)
    have h83 := hnext 14379237889 h14379237889 83 (by norm_num1) (by decide) (by decide) (by decide)
    exact hdup 5 h5 83 h83 (by decide) 3 (by norm_num1) (by decide) (by decide) (by decide) (by decide)
  · have h2478250459649 := first 2478250459649 prime_2478250459649 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    exact hsquare 2478250459649 h2478250459649 5 (by norm_num1) (by decide) (by decide) (by decide)
  · have h70657 := first 70657 prime_70657 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    exact hsquare 70657 h70657 7 (by norm_num1) (by decide) (by decide) (by decide)
  · have h341114881 := first 341114881 prime_341114881 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    have h170557441 := hnext 341114881 h341114881 170557441 prime_170557441 (by decide) (by decide) (by decide)
    have h11 := hnext 170557441 h170557441 11 (by norm_num1) (by decide) (by decide) (by decide)
    have h12647 := hnext 170557441 h170557441 12647 (by norm_num1) (by decide) (by decide) (by decide)
    exact hdup 11 h11 12647 h12647 (by decide) 3 (by norm_num1) (by decide) (by decide) (by decide) (by decide)
  · have h730882049 := first 730882049 prime_730882049 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    exact hsquare 730882049 h730882049 5 (by norm_num1) (by decide) (by decide) (by decide)
  · have h4513793 := first 4513793 prime_4513793 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    have h752299 := hnext 4513793 h4513793 752299 prime_752299 (by decide) (by decide) (by decide)
    exact hsquare 752299 h752299 5 (by norm_num1) (by decide) (by decide) (by decide)
  · have h3604481 := first 3604481 prime_3604481 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    exact hsquare 3604481 h3604481 3 (by norm_num1) (by decide) (by decide) (by decide)
  · have h786433 := first 786433 prime_786433 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    have h35747 := hnext 786433 h786433 35747 (by norm_num1) (by decide) (by decide) (by decide)
    exact hsquare 35747 h35747 3 (by norm_num1) (by decide) (by decide) (by decide)
  · have h2967994369 := first 2967994369 prime_2967994369 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    have h5 := hnext 2967994369 h2967994369 5 (by norm_num1) (by decide) (by decide) (by decide)
    have h11 := hnext 2967994369 h2967994369 11 (by norm_num1) (by decide) (by decide) (by decide)
    exact hdup 5 h5 11 h11 (by decide) 3 (by norm_num1) (by decide) (by decide) (by decide) (by decide)
  · have h211812353 := first 211812353 prime_211812353 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    exact hsquare 211812353 h211812353 3 (by norm_num1) (by decide) (by decide) (by decide)
  · have h3238002689 := first 3238002689 prime_3238002689 (by decide) (by decide)
      (modular_seed (by decide) (by decide +kernel))
    have h5 := hnext 3238002689 h3238002689 5 (by norm_num1) (by decide) (by decide) (by decide)
    exact hdup 3238002689 h3238002689 5 h5 (by decide) 3 (by norm_num1) (by decide) (by decide) (by decide) (by decide)

end Erdos1052.CoreFermat
