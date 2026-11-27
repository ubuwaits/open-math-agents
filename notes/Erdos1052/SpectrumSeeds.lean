import OMAReductions.R_Erdos1052_erdos_1052_R2

/-! Two unconditional odd-multiplier obstructions at v₂(a)=4 when
3,7,97,193,449 are absent from the repeated core. -/

namespace Erdos1052.SpectrumSeeds

open OMA.R_Erdos1052_erdos_1052_R2.CoreBounds

abbrev repeatedCore (n : ℕ) := ∏ p ∈ n.primeFactors.filter
  (fun p => p ≠ 2 ∧ n.factorization p ≠ 1), p^n.factorization p

private theorem seed_multiple {b t p : ℕ} (hb : Odd b) (ht : t ∣ b)
    (hp : p ∣ 2^(16*t)+1) : p ∣ 2^(16*b)+1 := by
  obtain ⟨k,h⟩ := ht
  have hk : Odd k := hb.of_dvd_nat ⟨t,by simpa [Nat.mul_comm] using h⟩
  have hd := hk.nat_add_dvd_pow_add_pow (2^(16*t)) 1
  rw [one_pow,←pow_mul,Nat.mul_assoc,←h] at hd
  exact hp.trans hd

set_option maxRecDepth 8192 in
theorem exclude_three_seven {n b : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hb : Odd b) (ha : n.factorization 2 = 16*b)
    (hsmall : ∀ p ∈ ({3,7,97,193,449}:Finset ℕ), ¬p ∣ repeatedCore n) :
    ¬3 ∣ b ∧ ¬7 ∣ b := by
  let c := repeatedCore n
  obtain ⟨hc,_,S,_,hsp,hbal,_,_⟩ := OMA.R_Erdos1052_erdos_1052_R2.decompose hn
  change Odd c at hc
  rw [ha] at hbal
  let v := 2^(16*b)*c
  let u := ∏ p ∈ v.primeFactors, (1+p^v.factorization p)
  change u*(∏ p ∈ S, (1+p)) = 2*v*(∏ p ∈ S, p) at hbal
  have hc0 : c ≠ 0 := by obtain ⟨k,h⟩ := hc; omega
  have hb0 : 16*b ≠ 0 := by obtain ⟨k,h⟩ := hb; omega
  have hpow : (2:ℕ)^(16*b) ≠ 0 := by positivity
  have hv0 : v ≠ 0 := mul_ne_zero hpow hc0
  have hv2 : 2 ∈ v.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, dvd_mul_of_dvd_left (dvd_pow_self 2 hb0) _, hv0⟩
  have he : v.factorization 2 = 16*b := by
    dsimp [v]
    simp [Nat.factorization_mul hpow hc0, Nat.prime_two.factorization_pow,
          Nat.factorization_eq_zero_of_not_dvd hc.not_two_dvd_nat]
  have hseed : 2^(16*b)+1 ∣ u := by
    rw [Nat.add_comm (2^(16*b)) 1]
    simpa only [he] using sigma_factor hv2
  have hnop {p : ℕ} (hp : p.Prime) (ht : ¬p ∣ 2)
      (hm : p∈({3,7,97,193,449}:Finset ℕ)) : ¬p ∣ 2*v := by
    dsimp [v,c]
    simp only [hp.dvd_mul, not_or]
    exact ⟨ht,fun h => ht (hp.dvd_of_dvd_pow h),hsmall p hm⟩
  have hpr (p : ℕ) (hp : p∈S) := (hsp p hp).1
  have shift {q r : ℕ} (hq : q∈S) (hd : r ∣ 1+q) :
      r ∣ u*(∏ p ∈ S,(1+p)) := dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem _ hq)) _
  constructor
  · intro h
    have h193 := forced_member (by decide : Nat.Prime 193) (hnop (by decide) (by decide) (by decide))
      hpr hbal (dvd_mul_of_dvd_left ((seed_multiple hb h (by decide : 193 ∣ 2^(16*3)+1)).trans hseed) _)
    have h97 := forced_member (by decide : Nat.Prime 97) (hnop (by decide) (by decide) (by decide))
      hpr hbal (shift h193 (by decide : 97 ∣ 1+193))
    apply square_obstruction (by decide : Nat.Prime 7) (mul_ne_zero (by decide) hv0)
      (hnop (by decide) (by decide) (by decide)) hpr
    rw [←hbal]
    exact shift h97 (by decide : 7^2 ∣ 1+97)
  · intro h
    have h449 := forced_member (by decide : Nat.Prime 449) (hnop (by decide) (by decide) (by decide))
      hpr hbal (dvd_mul_of_dvd_left ((seed_multiple hb h (by decide : 449 ∣ 2^(16*7)+1)).trans hseed) _)
    apply square_obstruction (by decide : Nat.Prime 3) (mul_ne_zero (by decide) hv0)
      (hnop (by decide) (by decide) (by decide)) hpr
    rw [←hbal]
    exact shift h449 (by decide : 3^2 ∣ 1+449)

end Erdos1052.SpectrumSeeds
