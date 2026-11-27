import OMAReductions.R_Erdos1052_erdos_1052_R2

/-!
# A bounded prime path in Erdős 1052

Erdos1052.SinglePath.bounded_paths verifies the forbidden-interval argument for a path with off-path abundance at most 1+η. The subtree construction is in section 8 of the accompanying proof.
-/

namespace Erdos1052.CoreBounds

abbrev sigmaU (b : ℕ) := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)

abbrev oddPart (n : ℕ) := ordCompl[2] n

theorem oddPart_prod (S : Finset ℕ) (f : ℕ → ℕ) :
    oddPart (∏ q ∈ S, f q) = ∏ q ∈ S, oddPart (f q) := by
  induction S using Finset.induction_on with
  | empty => simp [oddPart]
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, ← ih]
    exact Nat.ordCompl_mul _ _ 2

end Erdos1052.CoreBounds

namespace Erdos1052.Core625

open Erdos1052.CoreBounds

abbrev demand (q : ℕ) := oddPart (1 + q)
abbrev demands (T : Finset ℕ) := ∏ q ∈ T, demand q
abbrev primesProduct (T : Finset ℕ) := ∏ q ∈ T, q
abbrev primeSupport (T : Finset ℕ) := ∀ q ∈ T, q.Prime ∧ q ≠ 2

abbrev gain (q : ℕ) : ℚ := 1 + 1 / (q : ℚ)
abbrev abundancy (T : Finset ℕ) : ℚ := ∏ q ∈ T, gain q

theorem prime_mem_of_dvd {R : Finset ℕ} (hr : primeSupport R) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ primesProduct R) : p ∈ R := by
  obtain ⟨q,hq,hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
  simpa only [((hr q hq).1.dvd_iff_eq hp.ne_one).mp hdiv] using hq

abbrev shifted (S : Finset ℕ) := ∏ q ∈ S, (1+q)

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

end Erdos1052.Core625

namespace Erdos1052.OddExponent

open Erdos1052.Core625 Erdos1052.CoreBounds

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

end Erdos1052.OddExponent

namespace Erdos1052.LargePrimes

open Erdos1052.CoreBounds Erdos1052.Core625 Erdos1052.OddExponent

def Smooth (B z : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ z → p ≤ B

/-- Apart from a B-smooth factor, z is one or a prime. -/
def OneLarge (B z : ℕ) : Prop :=
  ∃ t r : ℕ, z=t*r ∧ Smooth B t ∧ (r=1 ∨ r.Prime ∧ B<r)

private theorem smooth_mul {B u v : ℕ} (hu : Smooth B u) (hv : Smooth B v) : Smooth B (u*v) := by
  intro p hp h
  exact (hp.dvd_mul.mp h).elim (hu p hp) (hv p hp)

private theorem smooth_coprime {B d : ℕ} (hd : Smooth B d) {T : Finset ℕ}
    (hT : ∀ q ∈ T, q.Prime ∧ B<q) : d.Coprime (primesProduct T) :=
  Nat.coprime_prod_right_iff.mpr fun q hq =>
    ((hT q hq).1.coprime_iff_not_dvd.mpr (fun h => (hT q hq).2.not_ge (hd q (hT q hq).1 h))).symm

/-- A whole interval of exponents excludes every bounded odd offset and denominator. -/
theorem prime_power_free_interval (D : ℕ) :
    ∃ W : ℕ, 2*D+1 < W ∧ ∀ E u d q k : ℕ, W ≤ E → E ≤ W+2*D →
      Odd u → u ≤ D → 0 < d → d ≤ D → q.Prime → d*q^k ≠ 2^E+u := by
  let L := 2*D+2
  let M := 2^(L+2*D)+D
  let P := (2*D+2)*(M^2).factorial
  have hP : 2*D+2 ≤ P := Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
  refine ⟨P+L,by dsimp [L]; omega,?_⟩
  intro E u d q k hlow hhigh hu hud hd hdD hq heq
  let e := E-P
  have he : E=e+P := by dsimp [e]; omega
  have hel : L ≤ e := by dsimp [e]; omega
  have heh : e ≤ L+2*D := by dsimp [e]; omega
  have he0 : 0 < e := by dsimp [L] at hel; omega
  let m := 2^e+u
  have hlo : D < 2^e := by
    have h := Nat.lt_two_pow_self (n:=e)
    dsimp [L] at hel; omega
  have hmododd : Odd m := (even_two.pow_of_ne_zero he0.ne').add_odd hu
  have hmD : D < m := by dsimp [m]; omega
  have hmm : m ≤ M := Nat.add_le_add (Nat.pow_le_pow_right (by decide) heh) hud
  have hm2 : Odd (m^2) := hmododd.pow
  have hmm2 : m^2 ≤ M^2 := Nat.pow_le_pow_left hmm _
  have hper : (m^2).totient ∣ P := dvd_mul_of_dvd_right
    (Nat.dvd_factorial ((Nat.totient_pos).mpr hm2.pos) ((Nat.totient_le _).trans hmm2)) _
  obtain ⟨z,hz⟩ := hper
  have hpmod : Nat.ModEq (m^2) (2^P) 1 := by
    rw [hz,pow_mul]
    simpa only [one_pow] using (Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hm2)).pow z
  have hpow := Nat.two_pow_pos P
  obtain ⟨b,hb⟩ := (Nat.modEq_iff_dvd' (show 1≤2^P by omega)).mp hpmod.symm
  have hpid : 2^P=m^2*b+1 := by omega
  let t := 1+2^e*m*b
  have hmt : m*t=d*q^k := by
    rw [heq,he,pow_add,hpid]
    dsimp [t,m]
    ring
  have hPbig : 2*D < 2^P := lt_trans (by omega) Nat.lt_two_pow_self
  have hbound : D*m < 2^E := calc
    D*m ≤ D*(2*2^e) := Nat.mul_le_mul_left _ (by dsimp [m]; omega)
    _ = 2*D*2^e := by ring
    _ < 2^P*2^e := Nat.mul_lt_mul_of_pos_right hPbig (Nat.two_pow_pos _)
    _ = _ := by rw [he,pow_add,Nat.mul_comm (2^P)]
  have htD : D<t := by
    by_contra! hx
    have hv := Nat.mul_le_mul_right m hx
    rw [Nat.mul_comm t m,hmt,heq] at hv
    omega
  have divides {x : ℕ} (hx : D<x) (hxq : x ∣ d*q^k) : q ∣ x := by
    by_contra hn
    have hcop := ((hq.coprime_iff_not_dvd.mpr hn).symm).pow_right k
    have := Nat.le_of_dvd hd (hcop.dvd_of_dvd_mul_right hxq)
    omega
  have hqm := divides hmD (hmt ▸ dvd_mul_right m t)
  have hqt := divides htD (hmt ▸ dvd_mul_left t m)
  have hqm' : q ∣ 2^e*m*b := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqm _) _
  have hbad : q ∣ 1 := (Nat.dvd_add_iff_left hqm').mpr hqt
  exact hq.not_dvd_one hbad

theorem prime_free_interval (D : ℕ) :
    ∃ W : ℕ, 2*D+1 < W ∧ ∀ E u d q : ℕ, W ≤ E → E ≤ W+2*D →
      Odd u → u ≤ D → 0 < d → d ≤ D → q.Prime → d*q ≠ 2^E+u := by
  obtain ⟨W,hW,h⟩ := prime_power_free_interval D
  exact ⟨W,hW,fun E u d q h1 h2 h3 h4 h5 h6 h7 => by
    simpa only [pow_one] using h E u d q 1 h1 h2 h3 h4 h5 h6 h7⟩

/-- One step of the chain. The offset is positive, odd, and never exceeds
the current denominator, so the loss of binary digits has a fixed bound. -/
private theorem next_exponent {D E u d r : ℕ} (hu : 0<u) (huD : u≤d)
    (hdb : d≤D) (hodd : Odd d) (hr : Odd r)
    (he : 2*D+1 < E) (heq : d*r=2^E+u) :
    ∃ j w, j ≤ 2*D ∧ Odd w ∧ w ≤ d ∧ d*demand r=2^(E-j)+w := by
  let j := (1+r).factorization 2
  have hshift : 2^j*demand r=1+r := Nat.ordProj_mul_ordCompl_eq_self (1+r) 2
  have hjpos : 0<j := by
    have hnon : ¬ 2 ∣ demand r := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
    have h2 : 2 ∣ 1+r := by obtain ⟨z,hz⟩ := hr; omega
    by_contra! hx
    have hj0 : j=0 := by omega
    rw [hj0,pow_zero,one_mul] at hshift
    exact hnon (hshift ▸ h2)
  have hx : d*(1+r)=2^E+(u+d) := by rw [Nat.mul_add,Nat.mul_one,heq]; omega
  have hjbound : j ≤ 2*D := by
    by_contra! H
    let k := 2*D+1
    have hkd : 2^k ∣ d*(1+r) := dvd_mul_of_dvd_right
      ((Nat.pow_dvd_pow 2 H).trans (hshift ▸ dvd_mul_right _ _)) d
    rw [hx] at hkd
    have := Nat.le_of_dvd (show 0<u+d by omega)
      ((Nat.dvd_add_iff_right (Nat.pow_dvd_pow 2 (show k≤E by dsimp [k]; omega))).mpr hkd)
    have hy := Nat.lt_two_pow_self (n:=k)
    dsimp [k] at hy this
    omega
  have hje : j<E := by omega
  have hv : 2^j ∣ u+d := (Nat.dvd_add_iff_right (Nat.pow_dvd_pow 2 hje.le)).mpr <| by
    rw [← hx,← hshift]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  obtain ⟨w,hw⟩ := hv
  have he2 : (2:ℕ)^E=2^j*2^(E-j) := by rw [← pow_add]; congr 1; omega
  have heq' : d*demand r=2^(E-j)+w := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos j) <| calc
    2^j*(d*demand r)=d*(1+r) := by rw [← hshift]; ac_rfl
    _ = _ := by rw [hx,hw,he2,Nat.mul_add]
  have hdmod : ¬2 ∣ demand r := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have hod : Odd (d*demand r) := hodd.mul (Nat.not_even_iff_odd.mp
    (fun H => hdmod (even_iff_two_dvd.mp H)))
  have how : Odd w := by
    have h2 : 2 ∣ (2:ℕ)^(E-j) := dvd_pow_self 2 (by omega)
    rw [heq'] at hod
    obtain ⟨z,hz⟩ := hod
    exact Nat.odd_iff.mpr (by omega)
  have hwle : w≤d := by
    have hh : 2 ≤ (2:ℕ)^j := Nat.le_pow hjpos
    have := Nat.mul_le_mul_right w hh
    omega
  exact ⟨j,w,hjbound,how,hwle,heq'⟩

private theorem smooth_of_dvd {B u v : ℕ} (hv : Smooth B v) (hd : u ∣ v) : Smooth B u :=
  fun p hp h => hv p hp (h.trans hd)

theorem one_large_of_dvd {B u v : ℕ} (hv : OneLarge B v) (hd : u ∣ v) : OneLarge B u := by
  obtain ⟨t,r,rfl,ht,hr⟩ := hv
  rcases hr with rfl | ⟨hp,hm⟩
  · rw [mul_one] at hd
    exact ⟨u,1,by simp,smooth_of_dvd ht hd,.inl rfl⟩
  · by_cases hru : r ∣ u
    · obtain ⟨z,hz⟩ := hru
      have hzt : z ∣ t := (Nat.mul_dvd_mul_iff_left hp.pos).mp (by
        simpa [hz,Nat.mul_comm t r] using hd)
      exact ⟨z,r,by rw [hz,Nat.mul_comm],smooth_of_dvd ht hzt,.inr ⟨hp,hm⟩⟩
    · have h := (hp.coprime_iff_not_dvd.mpr hru).symm.dvd_of_dvd_mul_right hd
      exact ⟨u,1,by simp,smooth_of_dvd ht h,.inl rfl⟩

private theorem chain_bound {B D W : ℕ} (hB : 2 ≤ B) (hD : 0<D) (hsD : Smooth B D)
    (hW : 2*D+1<W)
    (hgap : ∀ E u d q : ℕ, W≤E → E≤W+2*D → Odd u → u≤D →
      0<d → d≤D → q.Prime → d*q ≠ 2^E+u)
    (T : Finset ℕ) (hT : ∀ r ∈ T, r.Prime ∧ B<r)
    (hthin : ∀ r ∈ T, OneLarge B (demand r)) {E u d H : ℕ}
    (hd : Odd d) (hH : Odd H) (hu : Odd u) (hud : u≤d) (hsd : Smooth B d)
    (hone : OneLarge B H) (heq : d*H=2^E+u)
    (hbudget : d*H*demands T ∣ D*primesProduct T) : E<W := by
  induction T using Finset.strongInductionOn generalizing E u d H with
  | _ T ih =>
    by_contra! hWE
    obtain ⟨t,r,hfac,hts,hr⟩ := hone
    have ht : Odd t := hH.of_dvd_nat (hfac ▸ dvd_mul_right _ _)
    have hsdt := smooth_mul hsd hts
    have hdtleft : d*t ∣ d*H*demands T := by
      refine ⟨r*demands T,?_⟩
      rw [hfac]; ac_rfl
    have hdtD := (smooth_coprime hsdt hT).dvd_of_dvd_mul_right (hdtleft.trans hbudget)
    have hdtle := Nat.le_of_dvd hD hdtD
    have hddt := Nat.le_mul_of_pos_right d ht.pos
    have hdtodd := hd.mul ht
    have hmain : d*t*r=2^E+u := by rw [Nat.mul_assoc,← hfac,heq]
    rcases hr with rfl | ⟨hrp,hBr⟩
    · rw [Nat.mul_one] at hmain
      have := Nat.lt_two_pow_self (n:=E)
      omega
    · have hwide : W+2*D<E := by
        by_contra! hn
        exact hgap E u (d*t) r hWE hn hu (hud.trans (hddt.trans hdtle)) hdtodd.pos hdtle hrp hmain
      have hdvd : r ∣ D*primesProduct T := (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (hfac ▸ dvd_mul_left r t) d) (demands T)).trans hbudget
      have hprod := (hrp.dvd_mul.mp hdvd).resolve_left (fun h => hBr.not_ge (hsD r hrp h))
      have hrT := prime_mem_of_dvd (fun q h => ⟨(hT q h).1,by have := (hT q h).2; omega⟩) hrp hprod
      have hrOdd := hrp.odd_of_ne_two (by omega)
      obtain ⟨j,w,hj,hw,hwle,hnex⟩ :=
        next_exponent hu.pos (hud.trans hddt) hdtle hdtodd hrOdd (by omega) hmain
      have hdemOdd : Odd (demand r) := Nat.not_even_iff_odd.mp (fun h =>
        (Nat.not_dvd_ordCompl Nat.prime_two (show 1+r ≠ 0 by omega)) (even_iff_two_dvd.mp h))
      have hdprod : demand r*demands (T.erase r)=demands T := Finset.mul_prod_erase T demand hrT
      have hpProd : r*primesProduct (T.erase r)=primesProduct T := Finset.mul_prod_erase T (fun z : ℕ => z) hrT
      have hnext : (d*t)*demand r*demands (T.erase r) ∣ D*primesProduct (T.erase r) := by
        apply Nat.dvd_of_mul_dvd_mul_left hrp.pos
        rw [show r*(d*t*demand r*demands (T.erase r))=d*H*(demand r*demands (T.erase r)) by rw [hfac]; ac_rfl,
          show r*(D*primesProduct (T.erase r))=D*(r*primesProduct (T.erase r)) by ac_rfl,hdprod,hpProd]
        exact hbudget
      have bound := ih _ (Finset.erase_ssubset hrT) (fun q h => hT q (Finset.mem_of_mem_erase h))
        (fun q h => hthin q (Finset.mem_of_mem_erase h)) hdtodd hdemOdd hw hwle hsdt (hthin r hrT) hnex hnext
      omega

def smallProduct (B : ℕ) : ℕ := ∏ p ∈ (Finset.range (B+1)).filter Nat.Prime, p

private theorem smallProduct_pos (B : ℕ) : 0 < smallProduct B :=
  Finset.prod_pos (fun _ hp => (Finset.mem_filter.mp hp).2.pos)

private theorem smallProduct_smooth (B : ℕ) : Smooth B (smallProduct B) := by
  intro p hp hd
  obtain ⟨r,hr,hpr⟩ := (hp.prime.dvd_finsetProd_iff (fun x : ℕ => x)).mp hd
  have h := Finset.mem_filter.mp hr
  have he := (h.2.dvd_iff_eq hp.ne_one).mp hpr
  have hrB := Finset.mem_range.mp h.1
  omega

/-- The bound is uniform in the simple support and the seed divisor m.
    The numerator 2^E+1 may be divided by any fixed odd d₀ before the
    descending-prime test. -/
theorem fixed_core_seed_bound {B c d₀ : ℕ} (hB : 2≤B) (hc : 0<c) (hcB : Smooth B c)
    (hd : Odd d₀) (hdB : Smooth B d₀) :
    ∃ W : ℕ, ∀ (S : Finset ℕ) (m E : ℕ), primeSupport S →
      m*demands S ∣ c*primesProduct S → Odd m → d₀*m=2^E+1 →
      OneLarge B m → (∀ q ∈ S, B<q → OneLarge B (demand q)) → E<W := by
  let D := d₀*(c*smallProduct B)
  have hD : 0<D := Nat.mul_pos hd.pos (Nat.mul_pos hc (smallProduct_pos B))
  have hsD : Smooth B D := smooth_mul hdB (smooth_mul hcB (smallProduct_smooth B))
  obtain ⟨W,hW,hgap⟩ := prime_free_interval D
  refine ⟨W,?_⟩
  intro S m E hS hbal hm heq hone hsh
  let T := S.filter (fun q => B<q)
  let U := S.filter (fun q => ¬ B<q)
  have ht (q : ℕ) (hq : q∈T) : q∈S ∧ B<q := Finset.mem_filter.mp hq
  have hTU : primesProduct T*primesProduct U=primesProduct S :=
    Finset.prod_filter_mul_prod_filter_not S (fun q : ℕ => B<q) (fun q : ℕ => q)
  have hsub : U ⊆ (Finset.range (B+1)).filter Nat.Prime := by
    intro q hq
    obtain ⟨hqS,hqB⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),(hS q hqS).1⟩
  have hdiv : primesProduct U ∣ smallProduct B := Finset.prod_dvd_prod_of_subset U _ _ hsub
  have hu : primesProduct S ∣ smallProduct B*primesProduct T := by
    rw [← hTU,Nat.mul_comm (smallProduct B)]
    exact Nat.mul_dvd_mul_left _ hdiv
  have hleft : demands T ∣ demands S :=
    Finset.prod_dvd_prod_of_subset T S demand (fun q hq => (ht q hq).1)
  have hbudget : d₀*m*demands T ∣ D*primesProduct T := by
    dsimp [D]
    rw [Nat.mul_assoc d₀,Nat.mul_assoc d₀,Nat.mul_assoc c]
    exact Nat.mul_dvd_mul_left d₀ (((Nat.mul_dvd_mul_left m hleft).trans hbal).trans (Nat.mul_dvd_mul_left c hu))
  exact chain_bound hB hD hsD hW hgap T (fun q h => ⟨(hS q (ht q h).1).1,(ht q h).2⟩)
    (fun q h => hsh q (ht q h).1 (ht q h).2) hd hm odd_one hd.pos hdB hone heq hbudget

/-- The exponent test in R2 is finite under the one-large-prime assumption. -/
theorem finite_one_large_test {c B : ℕ} (hc : Odd c) (hB : 2≤B) (hcB : Smooth B c) :
    {a : ℕ | 0<a ∧ OneLarge B (2^a+1) ∧ ∃ S : Finset ℕ,
      (∀ q ∈ S, q.Prime ∧ ¬ q ∣ 2^a*c) ∧
      (∀ q ∈ S, B<q → OneLarge B (1+q)) ∧
      sigmaU (2^a*c)*shifted S=2*(2^a*c)*primesProduct S}.Finite := by
  have h1 : Smooth B 1 := fun p hp h => False.elim (hp.not_dvd_one h)
  obtain ⟨W,hW⟩ := fixed_core_seed_bound (d₀:=1) hB hc.pos hcB odd_one h1
  apply (Set.finite_Iio W).subset
  intro a ha
  obtain ⟨ha,hseed,S,hp,hshift,heq⟩ := ha
  obtain ⟨hS,_,_,hd⟩ := normalize ha hc hc.pos.ne' hp heq
  have hm : Odd (2^a+1) := (even_two.pow_of_ne_zero ha.ne').add_odd odd_one
  have hdiv : (2^a+1)*demands S ∣ c*primesProduct S := by
    rw [← hd,Nat.mul_assoc]
    exact dvd_mul_left _ _
  exact hW S _ a hS hdiv hm (by simp) hseed
    (fun q hq hqB => one_large_of_dvd (hshift q hq hqB) (Nat.ordCompl_dvd _ _))

/-- The offending pair can be localized to the factors descending from a chosen
    cyclotomic quotient; the hypotheses on the displayed support are only divisibility. -/
theorem quotient_bound {c B h : ℕ} (hB : 2≤B) (hc : 0<c) (hcB : Smooth B c)
    (hh : 0<h) (hFB : Smooth B (2^h+1)) :
    ∃ W : ℕ, ∀ (b A : ℕ) (T : Finset ℕ), primeSupport T → Odd A →
      (2^h+1)*A=2^(h*b)+1 → A*demands T ∣ c*primesProduct T →
      OneLarge B A → (∀ r ∈ T, B<r → OneLarge B (1+r)) → h*b<W := by
  obtain ⟨W,hW⟩ := fixed_core_seed_bound hB hc hcB
    ((even_two.pow_of_ne_zero hh.ne').add_odd odd_one) hFB
  exact ⟨W,fun b A T hT hA heq hd hthin ht => hW T A (h*b) hT hd hA heq hthin
    (fun q hq hqB => one_large_of_dvd (ht q hq hqB) (Nat.ordCompl_dvd _ _))⟩

/-- A finite path whose large entries are whole odd prime powers. The second
index multiplies the odd factors extracted along the path. -/
inductive PrimePowerPath : ℕ → ℕ → Prop
  | stop (t : ℕ) (ht : Odd t) : PrimePowerPath t t
  | step (t p e cost : ℕ) (ht : Odd t) (hp : p.Prime) (ho : Odd p) (he : 0<e)
      (next : PrimePowerPath (demand (p^e)) cost) : PrimePowerPath (t*p^e) (t*cost)

private theorem PrimePowerPath.cost_pos {u t : ℕ} (h : PrimePowerPath u t) : 0<t := by
  induction h with
  | stop t ht => exact ht.pos
  | step t p e cost ht _ _ _ _ ih => exact Nat.mul_pos ht.pos ih

/-- Even with arbitrarily large multiplicities, a single path with bounded
product of the extracted factors cannot start from arbitrarily large 2^E+1. -/
theorem bounded_prime_power_paths (D : ℕ) :
    ∃ W : ℕ, ∀ H T : ℕ, PrimePowerPath H T → ∀ E u d : ℕ, Odd d → Odd u →
      u≤d → d*T≤D → d*H=2^E+u → E<W := by
  obtain ⟨W,hW,hgap⟩ := prime_power_free_interval D
  refine ⟨W,?_⟩
  intro H T ht
  induction ht with
  | stop t ht =>
    intro E u d hd hu hud hcap hval
    have := Nat.lt_two_pow_self (n:=E)
    omega
  | step t p e cost ht hp ho _ next ih =>
    intro E u d hd hu hud hcap hval
    by_contra! hE
    have hdt : d*t≤D := (Nat.le_mul_of_pos_right (d*t) next.cost_pos).trans
      (by simpa only [Nat.mul_assoc] using hcap)
    have hud' : u≤d*t := hud.trans (Nat.le_mul_of_pos_right d ht.pos)
    have hmain : d*t*p^e=2^E+u := by rwa [Nat.mul_assoc]
    have hwide : W+2*D<E := by
      by_contra! hn
      exact hgap E u (d*t) p e hE hn hu (hud'.trans hdt) (hd.mul ht).pos hdt hp hmain
    obtain ⟨j,w,hj,hw,hle,hnext⟩ := next_exponent hu.pos hud' hdt (hd.mul ht) ho.pow (by omega) hmain
    have hlt := ih (E-j) w (d*t) (hd.mul ht) hw hle
      (by simpa only [Nat.mul_assoc] using hcap) hnext
    omega

end Erdos1052.LargePrimes

/-
# A prime path with arbitrarily many off-path factors

The off-path groups have a total abundancy close to one. This file verifies
the numerical crossing argument of section 8 of the accompanying proof.
Each step records exactly the inequalities proved there from the divisor
balance. An arbitrarily long drop is impossible if it lands near or below
the forbidden interval, even when the new binary exponent is negative.
-/

namespace Erdos1052.SinglePath

/-- After a step the odd path value is the product of its bounded denominator
and the next prime (or one at termination). -/
structure Step (D : ℕ) (η : ℚ) (E : ℤ) where
  loss : ℕ
  d : ℕ
  r : ℕ
  K : ℚ
  tail : ℚ
  dOdd : Odd d
  rOdd : Odd r
  cap : d≤D
  lower : 1≤K
  upper : K≤1+η
  positive : 0<tail
  bound : tail≤(1+η)*d
  drop : tail*2^loss≤2*(1+η)*D
  value : (d:ℚ)*r=K*2^(E-loss)+tail

inductive Path (D : ℕ) (η : ℚ) : ℤ → Prop
  | stop {E : ℤ} (s : Step D η E) (h : s.r=1) : Path D η E
  | next {E : ℤ} (s : Step D η E) (h : s.r.Prime) (rest : Path D η (E-s.loss)) : Path D η E

private theorem scale_le {E : ℤ} {Z : ℕ} (h : E≤Z) : (2:ℚ)^E≤(2:ℚ)^Z := by
  simpa only [zpow_natCast] using zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) h

private theorem small_landing {D Z J : ℕ} {η : ℚ} {E : ℤ} (s : Step D η E)
    (hη : 0<η) (heighth : η≤1/8) (hscale : η*(2:ℚ)^Z<1/8)
    (hwidth : 8*D<2^J) (hland : E-s.loss≤Z) : s.loss<J := by
  by_contra! hb
  have hnat : 8*D<2^s.loss := hwidth.trans_le (Nat.pow_le_pow_right (by decide) hb)
  have hp : (8:ℚ)*D<2^s.loss := by exact_mod_cast hnat
  have hD : (0:ℚ)<D := by exact_mod_cast s.dOdd.pos.trans_le s.cap
  have ht : s.tail<1/3 := by
    by_contra! ht
    have lower := mul_le_mul_of_nonneg_right ht (show 0≤(2:ℚ)^s.loss by positivity)
    have upper := mul_le_mul_of_nonneg_right heighth hD.le
    linarith [s.drop]
  let v := E-s.loss
  have hv : (2:ℚ)^v≤(2:ℚ)^Z := scale_le hland
  have hvpos : (0:ℚ)<2^v := by positivity
  have hsmall := mul_le_mul_of_nonneg_left hv hη.le
  have hinc := mul_le_mul_of_nonneg_right s.upper hvpos.le
  have hn := mul_le_mul_of_nonneg_right s.lower hvpos.le
  have heq : (s.d:ℚ)*s.r=s.K*2^v+s.tail := s.value
  by_cases hneg : v<0
  · have hhalf : (2:ℚ)^v≤1/2 := by
      have H := zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) (show v≤-1 by omega)
      norm_num at H ⊢
      exact H
    have hηhalf := mul_le_mul_of_nonneg_left hhalf hη.le
    have hm : (1:ℚ)≤(s.d:ℚ)*s.r := by exact_mod_cast (Nat.mul_pos s.dOdd.pos s.rOdd.pos)
    nlinarith
  · have hnon : 0≤v := by omega
    have hz : (2:ℚ)^v = (2:ℚ)^v.toNat := by rw [← zpow_natCast,Int.toNat_of_nonneg hnon]
    rw [hz] at heq hn hinc hsmall
    have hlo : (2:ℕ)^v.toNat<s.d*s.r := by exact_mod_cast
      (show (2:ℚ)^v.toNat < (s.d:ℚ)*s.r by linarith [s.positive])
    have hhi : s.d*s.r < (2:ℕ)^v.toNat+1 := by exact_mod_cast
      (show (s.d:ℚ)*s.r < (2:ℚ)^v.toNat+1 by linarith)
    omega

private theorem gap_landing {D W Z : ℕ} {η : ℚ} {E : ℤ} (s : Step D η E)
    (hη : 0<η) (hsmall : η*((2:ℚ)^Z+D)<1) (hW : 0<W)
    (hgap : ∀ e u d r : ℕ, W≤e → e≤Z → Odd u → u≤D → 0<d → d≤D →
      r.Prime → d*r≠2^e+u)
    (hr : s.r.Prime) (hlo : (W:ℤ)≤E-s.loss) (hhi : E-s.loss≤Z) : False := by
  let e := (E-s.loss).toNat
  have hnon : 0≤E-s.loss := by omega
  have he : (e:ℤ)=E-s.loss := Int.toNat_of_nonneg hnon
  have hel : W≤e := by omega
  have heh : e≤Z := by omega
  have heq := s.value
  rw [← he,zpow_natCast] at heq
  have hp : (0:ℚ)<2^e := by positivity
  have hl := mul_le_mul_of_nonneg_right s.lower hp.le
  have hu := mul_le_mul_of_nonneg_right s.upper hp.le
  have heZ : (2:ℚ)^e≤2^Z := pow_le_pow_right₀ (by norm_num) heh
  have hcap : (s.d:ℚ)≤D := by exact_mod_cast s.cap
  have hsum := mul_le_mul_of_nonneg_left (add_le_add heZ hcap) hη.le
  have hl' : 2^e<s.d*s.r := by exact_mod_cast
    (show (2:ℚ)^e<(s.d:ℚ)*s.r by linarith [s.positive])
  have hu' : s.d*s.r<2^e+s.d+1 := by exact_mod_cast
    (show (s.d:ℚ)*s.r<2^e+s.d+1 by linarith [s.bound])
  let u := s.d*s.r-2^e
  have hid : s.d*s.r=2^e+u := by dsimp [u]; omega
  have hud : u≤D := by dsimp [u]; have := s.cap; omega
  have evenp : Even ((2:ℕ)^e) := even_two.pow_of_ne_zero (by omega)
  have huodd : Odd u := (Nat.odd_sub hl'.le).mpr
    ⟨fun _ => evenp,fun _ => s.dOdd.mul s.rOdd⟩
  exact hgap e u s.d s.r hel heh huodd hud s.dOdd.pos s.cap hr hid

/-- For each denominator budget, some positive allowance for surplus from
side branches still leaves a uniform bound on the initial binary exponent. -/
theorem bounded_paths (D : ℕ) : ∃ Z : ℕ, ∃ η : ℚ, 0<η ∧
    ∀ E : ℤ, Path D η E → E≤Z := by
  let Q := D+4
  have hDQ : D≤Q := by dsimp [Q]; omega
  obtain ⟨W,hW,hgap⟩ := Erdos1052.LargePrimes.prime_free_interval Q
  let J := 2*Q
  let Z := W+J
  have hwidth : 8*D<2^J := calc
    8*D < 8*2^D := Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by decide)
    _ = 2^(D+3) := by rw [pow_add]; ring
    _ ≤ 2^J := Nat.pow_le_pow_right (by decide) (by dsimp [J,Q]; omega)
  let V : ℚ := 2^Z+D
  have hV : 0<V := by dsimp [V]; positivity
  let η : ℚ := 1/(16*(V+1))
  have hdpos : (0:ℚ)<16*(V+1) := by linarith
  have hη : 0<η := one_div_pos.mpr hdpos
  have heta8 : η≤1/8 := by
    change 1/(16*(V+1)) ≤ 1/8
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hclose : η*((2:ℚ)^Z+D)<1/8 := by
    change (1/(16*(V+1)))*V<1/8
    rw [one_div_mul_eq_div,div_lt_iff₀ hdpos]
    linarith
  have hscale : η*(2:ℚ)^Z<1/8 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity : (0:ℚ)≤D)) hη.le) hclose
  have hDW : D≤2^W := hDQ.trans ((show Q≤W by omega).trans Nat.lt_two_pow_self.le)
  have stay {E : ℤ} (s : Step D η E) (hi : (Z:ℤ)<E) : (W:ℤ)≤E-s.loss := by
    by_contra! hbelow
    have hlo : E-s.loss≤Z := by dsimp [Z]; omega
    have := small_landing s hη heta8 hscale hwidth hlo
    dsimp [Z] at hi
    omega
  refine ⟨Z,η,hη,?_⟩
  intro E path
  induction path with
  | @stop E s hr =>
    by_contra! hi
    have hl := stay s hi
    have h := zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) hl
    rw [zpow_natCast] at h
    have he := s.value
    rw [hr,Nat.cast_one,mul_one] at he
    have hks := mul_le_mul_of_nonneg_right s.lower (by positivity :
      (0:ℚ)≤2^(E-(s.loss:ℤ)))
    have hcap : (s.d:ℚ)≤D := by exact_mod_cast s.cap
    have hbig : (D:ℚ)≤2^W := by exact_mod_cast hDW
    linarith [s.positive]
  | @next E s hr _ ih =>
    by_contra! hi
    apply gap_landing s hη (by linarith [hclose]) (by omega : 0<W) _ hr (stay s hi) ih
    intro e u d r hlow hhigh hu hud hd hdQ hp
    exact hgap e u d r hlow hhigh hu (hud.trans hDQ) hd (hdQ.trans hDQ) hp

end Erdos1052.SinglePath
