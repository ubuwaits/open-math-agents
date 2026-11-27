import Mathlib

/-! Quantitative exponent bounds and an obstruction to a rational product
on a single infinite path of shifted primes. -/

namespace Erdos1052.Spectrum

/-- A lower gap at the limiting simple-prime abundancy bounds the exponent. -/
theorem exponent_le_of_gap {a m : ℕ} {R B : ℚ} (hR : 0 < R) (hupper : R ≤ 2)
    (hbalance : B=R/(1+1/(2:ℚ)^a))
    (hgap : ¬ (R-1/(2:ℚ)^m ≤ B ∧ B < R)) : a ≤ m := by
  by_contra! h
  have hpow : 2*(2:ℚ)^m ≤ 2^a := by
    rw [mul_comm, ←pow_succ]
    exact pow_le_pow_right₀ (by norm_num) h
  have hpos : (0:ℚ) < 2^a := by positivity
  have hdiff : R-B=R/((2:ℚ)^a+1) := by
    rw [hbalance]
    field_simp
    ring
  have hlt : R/((2:ℚ)^a+1) < 1/(2:ℚ)^m := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hx := mul_le_mul_of_nonneg_right hupper (show 0 ≤ (2:ℚ)^m by positivity)
    nlinarith
  exact hgap ⟨by linarith, by linarith [show 0 < R/((2:ℚ)^a+1) by positivity]⟩

def unitarySum (n : ℕ) := ∏ q ∈ n.primeFactors, (1+q^n.factorization q)

def target (c : ℕ) : ℚ := 2*c/unitarySum c

def simpleProduct (S : Finset ℕ) : ℚ := ∏ q ∈ S, ((1+q)/q : ℚ)

private theorem split_two {a c : ℕ} (ha : a ≠ 0) (hc : Odd c) :
    unitarySum (2^a*c) = (1+2^a)*unitarySum c := by
  have hc0 : c ≠ 0 := by obtain ⟨k,h⟩ := hc; omega
  have hb : (2:ℕ)^a ≠ 0 := by positivity
  have hn : 2 ∉ c.primeFactors := fun h => hc.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors h)
  have hf (q : ℕ) : (2^a*c).factorization q =
      (if 2=q then a else 0)+c.factorization q := by
    rw [Nat.factorization_mul hb hc0, Finsupp.add_apply, Nat.prime_two.factorization_pow,
      Finsupp.single_apply]
  unfold unitarySum
  rw [Nat.primeFactors_mul hb hc0, Nat.primeFactors_prime_pow ha Nat.prime_two,
    Finset.singleton_union, Finset.prod_insert hn, hf, if_pos rfl,
    Nat.factorization_eq_zero_of_not_dvd hc.not_two_dvd_nat, add_zero]
  congr 1
  refine Finset.prod_congr rfl fun q hq => ?_
  have hnq : 2 ≠ q := fun he => hn (he ▸ hq)
  rw [hf,if_neg hnq,zero_add]

/-- The gap criterion for the integer balance used in the accepted R2 test. -/
theorem test_exponent_bound {a c m : ℕ} {S : Finset ℕ} (ha : a ≠ 0) (hc : Odd c)
    (hp : ∀ q ∈ S, q.Prime)
    (hb : unitarySum (2^a*c) * (∏ q ∈ S, (1+q)) = 2*(2^a*c)*(∏ q ∈ S, q))
    (hg : ¬ (target c-1/(2:ℚ)^m ≤ simpleProduct S ∧ simpleProduct S < target c)) :
    a ≤ m := by
  have hc0 : 0 < c := by obtain ⟨k,h⟩ := hc; omega
  have hsig : c ≤ unitarySum c := by
    calc c = ∏ q ∈ c.primeFactors, q^c.factorization q :=
          Nat.prod_primeFactors_pow_factorization hc0.ne'
       _ ≤ _ := Finset.prod_le_prod' fun q _ => by omega
  have hcR : (0:ℚ) < c := by exact_mod_cast hc0
  have hsR : (c:ℚ) ≤ unitarySum c := by exact_mod_cast hsig
  have hs0 := hcR.trans_le hsR
  have hp0 : (∏ q ∈ S, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hp q hq).ne_zero
  have hn0 : (∏ q ∈ S, (q:ℚ)) ≠ 0 := by rw [←Nat.cast_prod]; exact_mod_cast hp0
  rw [split_two ha hc] at hb
  have hh : (1+(2:ℚ)^a)*(unitarySum c : ℚ)*(∏ q ∈ S, (1+(q:ℚ))) =
      2*(2^a*(c:ℚ))*(∏ q ∈ S, (q:ℚ)) := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_prod]
      using congrArg (Nat.cast : ℕ → ℚ) hb
  apply exponent_le_of_gap (R:=target c) (B:=simpleProduct S) (by unfold target; positivity) _ _ hg
  · unfold target
    apply (div_le_iff₀ hs0).mpr; linarith
  · unfold simpleProduct target
    rw [Finset.prod_div_distrib]
    field_simp
    nlinarith

/-- Any certified lower interval gap for the allowed supports gives a finite
set of exponents, uniformly over the sizes of the simple primes. -/
theorem finite_test_of_gap {c m : ℕ} (hc : Odd c) (allowed : Finset ℕ → Prop)
    (hg : ∀ S, allowed S → ¬ (target c-1/(2:ℚ)^m ≤ simpleProduct S ∧ simpleProduct S < target c)) :
    {a : ℕ | a ≠ 0 ∧ ∃ S, allowed S ∧ (∀ q ∈ S, q.Prime) ∧
      unitarySum (2^a*c) * (∏ q ∈ S, (1+q)) = 2*(2^a*c)*(∏ q ∈ S, q)}.Finite := by
  apply (Set.finite_Iic m).subset
  rintro a ⟨ha,S,hS,hp,hb⟩
  exact test_exponent_bound ha hc hp hb (hg S hS)

private def block (j : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => block j i t + j (i+t)

private theorem same_step {z j : ℕ → ℕ} {B : ℕ} (hpos : ∀ n, 0 < z n)
    (hbound : ∀ n, z n ≤ B) (hz : ∀ n, z (n+1)+B=2^(j n)*z n)
    {i k : ℕ} (he : z i=z k) : j i=j k ∧ z (i+1)=z (k+1) := by
  have unique {i k : ℕ} (e : z i=z k) : ¬j i < j k := by
    intro hlt
    have hp : 2^(j i+1) ≤ (2:ℕ)^(j k) := Nat.pow_le_pow_right (by decide) hlt
    rw [pow_succ] at hp
    have hm := Nat.mul_le_mul_right (z k) hp
    have h1 := hz i
    rw [e] at h1
    have h2 := hz k
    have h3 := hpos (i+1)
    have h4 := hbound (k+1)
    nlinarith
  have h := Nat.le_antisymm (Nat.le_of_not_gt (unique he.symm)) (Nat.le_of_not_gt (unique he))
  exact ⟨h,by have hi := hz i; rw [he,h,←hz k] at hi; omega⟩

/-- The bounded positive integer errors of a rational binary limit cannot
follow an infinite increasing path of odd primes. -/
theorem no_bounded_errors {q j z : ℕ → ℕ} {B : ℕ}
    (hq : ∀ n, (q n).Prime) (hodd : ∀ n, q n ≠ 2) (hinc : StrictMono q)
    (hstep : ∀ n, q (n+1)+1=2^(j n)*q n)
    (hpos : ∀ n, 0 < z n) (hbound : ∀ n, z n ≤ B)
    (hz : ∀ n, z (n+1)+B=2^(j n)*z n) : False := by
  have hB : 0 < B := (hpos 0).trans_le (hbound 0)
  have sync {u v : ℕ} (he : z u=z v) (t : ℕ) :
      z (u+t)=z (v+t) ∧ block j u t=block j v t := by
    induction t with
    | zero => exact ⟨by simpa using he,rfl⟩
    | succ t ih =>
      obtain ⟨h1,h2⟩ := same_step hpos hbound hz ih.1
      exact ⟨by simpa [Nat.add_assoc] using h2, by simp only [block,ih.2,h1]⟩
  obtain ⟨u,v,huv,heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f:=fun n : ℕ => z (B+1+n)) (t:=Set.Iic B) (fun n => hbound _) (Set.finite_Iic B)
  let i := B+1+u
  let T := v-u
  have hT : 0 < T := by dsimp [T]; omega
  have hcycle : z (i+T)=z i := by
    dsimp [i,T]
    rwa [show B+1+u+(v-u)=B+1+v by omega,eq_comm]
  let W := fun n => B*q n-z n
  have hW n : W n+z n=B*q n := by
    apply Nat.sub_add_cancel
    have hl : 1 ≤ q n := (hq n).one_lt.le
    exact (hbound n).trans (by simpa using Nat.mul_le_mul_left B hl)
  have stepW n : W (n+1)=2^(j n)*W n := by
    have hh := congrArg (fun x : ℕ => B*x) (hstep n)
    have h1 := hW (n+1)
    have h2 := congrArg (fun x : ℕ => 2^(j n)*x) (hW n)
    have h3 := hz n
    try dsimp at hh h2
    nlinarith
  have steps u t : W (u+t)=2^(block j u t)*W u := by
    induction t with
    | zero => simp [block]
    | succ t ih =>
      rw [Nat.add_succ,stepW,ih,block,pow_add]; ring
  let M := 2^(block j i T)
  have repeats (k : ℕ) : z (i+T*k)=z i ∧ W (i+T*k)=M^k*W i := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨h1,h2⟩ := sync ih.1 T
      have hi : i+T*(k+1)=(i+T*k)+T := by ring
      rw [hi]
      refine ⟨h1.trans hcycle,?_⟩
      rw [steps,h2,ih.2,pow_succ]
      dsimp only [M]; ring
  let p := q i
  have hp : p.Prime := hq i
  have hpB : B < p := by have hi := hinc.id_le i; dsimp [p,i] at *; omega
  have h2p : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (fun hd =>
    hodd i ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
  have hMp : M.Coprime p := h2p.symm.pow_left _
  let k := p.totient
  have hk : 0 < k := Nat.totient_pos.mpr hp.pos
  have hmod : M^k ≡ 1 [MOD p] := by
    change M^p.totient % p=1%p
    rw [Nat.pow_totient_mod_eq_one hp.one_lt hMp,Nat.mod_eq_of_lt hp.one_lt]
  obtain ⟨her,hscale⟩ := repeats k
  have hwmod : W (i+T*k) ≡ W i [MOD p] := by simpa [hscale] using hmod.mul_right (W i)
  have hqmod : B*q (i+T*k) ≡ B*q i [MOD p] := by
    rw [←hW,←hW,her]
    exact hwmod.add_right _
  have hcop : p.Coprime B := hp.coprime_iff_not_dvd.mpr (fun hd => (Nat.not_le_of_lt hpB) (Nat.le_of_dvd hB hd))
  have := Nat.ModEq.cancel_left_of_coprime hcop hqmod
  have hd : p∣q (i+T*k) := Nat.modEq_zero_iff_dvd.mp
    (this.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)))
  have he := (Nat.prime_dvd_prime_iff_eq hp (hq _)).mp hd
  exact (hinc (show i < i+T*k by have := Nat.mul_pos hT hk; omega)).ne he

/-- A rational limit A/B, with each dyadic truncation lying in (0,1]
above that limit after scaling, supplies the forbidden bounded errors. -/
theorem no_rational_shadow {q j s : ℕ → ℕ} {A B : ℕ}
    (hq : ∀ n, (q n).Prime) (hodd : ∀ n, q n ≠ 2) (hinc : StrictMono q)
    (hs : ∀ n, s (n+1)=s n+j n)
    (hstep : ∀ n, q (n+1)+1=2^(j n)*q n)
    (hlo : ∀ n, A*2^(s n) < B*q n)
    (hhi : ∀ n, B*q n ≤ A*2^(s n)+B) : False := by
  let z := fun n => B*q n-A*2^(s n)
  have hdecomp n : z n+A*2^(s n)=B*q n := Nat.sub_add_cancel (hlo n).le
  apply no_bounded_errors (z:=z) (B:=B) hq hodd hinc hstep
  · intro n; dsimp [z]; exact Nat.sub_pos_of_lt (hlo n)
  · intro n; have := hhi n; have := hdecomp n; omega
  · intro n
    have h1 := congrArg (fun x : ℕ => B*x) (hstep n)
    have h2 := hdecomp (n+1)
    have h3 := congrArg (fun x : ℕ => (2:ℕ)^(j n)*x) (hdecomp n)
    rw [hs,pow_add] at h2
    try dsimp at h1 h3
    nlinarith


open Filter
open scoped Topology

/-- The normalized truncations of any infinite dyadic chain of odd primes
converge to an irrational real number. -/
theorem prime_path_irrational_limit {q j s : ℕ → ℕ}
    (hq : ∀ n, (q n).Prime) (hodd : ∀ n, q n ≠ 2)
    (hj : ∀ n, 1 ≤ j n) (hs : ∀ n, s (n+1) = s n+j n)
    (hstep : ∀ n, q (n+1)+1 = 2^(j n)*q n) :
    ∃ x : ℝ, Irrational x ∧ Tendsto (fun n => (q n : ℝ)/2^(s n)) atTop (𝓝 x) := by
  let U := fun n => (q n : ℝ)/2^(s n)
  let L := fun n => ((q n : ℝ)-1)/2^(s n)
  have scale n : (2:ℝ)^(s (n+1)) = 2^(j n)*2^(s n) := by rw [hs,pow_add,mul_comm]
  have stepR n : (q (n+1):ℝ)+1 = 2^(j n)*(q n:ℝ) := by exact_mod_cast hstep n
  have jtwo n : 2 ≤ (2:ℕ)^(j n) := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (hj n)
  have hinc : StrictMono q := strictMono_nat_of_lt_succ fun n => by
    have h := Nat.mul_le_mul_right (q n) (jtwo n)
    have hq2 := (hq n).one_lt
    have hh := hstep n
    omega
  have hu : StrictAnti U := strictAnti_nat_of_succ_lt fun n => by
    dsimp [U]; rw [scale, ←div_div]
    apply div_lt_div_of_pos_right _ (by positivity)
    apply (div_lt_iff₀ (by positivity)).2
    linarith [stepR n, mul_comm ((q n):ℝ) ((2:ℝ)^(j n))]
  have hl : Monotone L := monotone_nat_of_le_succ fun n => by
    dsimp [L]; rw [scale, ←div_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (le_div_iff₀ (by positivity)).2
    have htwo : 2 ≤ (2:ℝ)^(j n) := by exact_mod_cast jtwo n
    nlinarith [stepR n]
  have hlu n : L n ≤ U n := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  let x := iInf U
  have hlim : Tendsto U atTop (𝓝 x) := tendsto_atTop_ciInf hu.antitone
    ⟨0, by rintro y ⟨n,rfl⟩; dsimp [U]; positivity⟩
  have lower n : L n ≤ x := ge_of_tendsto hlim
    ((eventually_ge_atTop n).mono fun k hk => (hl hk).trans (hlu k))
  have upper n : x < U n := (le_of_tendsto hlim
    ((eventually_ge_atTop (n+1)).mono fun k hk => hu.antitone hk)).trans_lt (hu (Nat.lt_succ_self n))
  refine ⟨x,?_,hlim⟩
  rintro ⟨r,hr⟩
  have hnonneg : (0:ℝ) ≤ L 0 := by
    dsimp [L]
    apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (by exact_mod_cast (hq 0).one_lt.le)
  have hr0 : 0 ≤ r := Rat.cast_nonneg.mp (hr ▸ (hnonneg.trans (lower 0)) : (0:ℝ) ≤ r)
  let A := r.num.toNat
  let B := r.den
  have hbpos : (0:ℝ) < B := by exact_mod_cast r.den_pos
  have hfrac : x = (A:ℝ)/B := by
    rw [←hr, Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr0)).symm
  apply no_rational_shadow (A:=A) (B:=B) hq hodd hinc hs hstep
  · intro n
    have hh := upper n
    change x < (q n:ℝ)/2^(s n) at hh
    rw [hfrac] at hh
    have hm := (div_lt_div_iff₀ hbpos (by positivity)).mp hh
    exact_mod_cast (by linarith [mul_comm (B:ℝ) (q n)] : (A:ℝ)*2^(s n) < B*(q n:ℝ))
  · intro n
    have hh := lower n
    change ((q n:ℝ)-1)/2^(s n) ≤ x at hh
    rw [hfrac] at hh
    have hm := (div_le_div_iff₀ (by positivity) hbpos).mp hh
    exact_mod_cast (by nlinarith : (B:ℝ)*(q n:ℝ) ≤ A*2^(s n)+B)

/-- An infinite increasing chain of odd primes with shifts equal to a power
of two times their predecessor has irrational limiting abundancy. -/
theorem prime_path_product_irrational {q j : ℕ → ℕ}
    (hq : ∀ n, (q n).Prime) (hodd : ∀ n, q n ≠ 2) (hj : ∀ n, 1 ≤ j n)
    (hstep : ∀ n, q (n+1)+1 = 2^(j n)*q n) :
    ∃ y : ℝ, Irrational y ∧ Tendsto (fun n => ∏ k ∈ Finset.range (n+1),
        (((q k : ℝ)+1)/(q k : ℝ))) atTop (𝓝 y) := by
  let s (n : ℕ) := ∑ k ∈ Finset.range n, j k
  have hs n : s (n+1) = s n+j n := Finset.sum_range_succ j n
  obtain ⟨x,hx,ht⟩ := prime_path_irrational_limit hq hodd hj hs hstep
  have hpositive n : (0:ℝ) < q n := by exact_mod_cast (hq n).pos
  have partialprod n : (∏ k ∈ Finset.range (n+1), (((q k : ℝ)+1)/(q k : ℝ))) =
      ((q 0:ℝ)+1)/((q n : ℝ)/2^(s n)) := by
    induction n with
    | zero => simp [s]
    | succ n ih =>
      rw [Finset.prod_range_succ,ih,hs,pow_add]
      have hr : (q (n+1):ℝ)+1 = 2^(j n)*(q n:ℝ) := by exact_mod_cast hstep n
      rw [hr]
      field_simp [(hpositive n).ne',(hpositive (n+1)).ne']
  refine ⟨((q 0:ℝ)+1)/x,?_,?_⟩
  · have hy : Irrational (((q 0+1:ℕ):ℝ)/x) :=
      irrational_natCast_div_iff.mpr ⟨by omega,hx⟩
    simpa using hy
  · simpa only [partialprod] using
      (show Tendsto (fun n => ((q 0:ℝ)+1)/((q n:ℝ)/2^(s n))) atTop
        (𝓝 (((q 0:ℝ)+1)/x)) from tendsto_const_nhds.div ht hx.ne_zero)

end Erdos1052.Spectrum
