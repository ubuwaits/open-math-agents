import Mathlib

/-! Rounded powers of two on a descending chain of shifted odd primes. -/

namespace Erdos1052.PrimeRuns

/-- If `d*r = 2^E + u` and `0 < u ≤ d`, this is the only possible `r`. -/
def rounded (d E : ℕ) : ℕ := 2^E/d+1

theorem rounded_of_balance {d E u r : ℕ} (hu : 0 < u) (hud : u ≤ d)
    (heq : d*r = 2^E+u) : rounded d E = r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by
    intro h; have := Nat.two_pow_pos E; rw [h, Nat.mul_zero] at heq; omega)
  unfold rounded
  have hdiv : 2^E/d = r := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  omega

/-- All intermediate lower exponents skipped by a pure prime shift have even value. -/
theorem rounded_at_shift {d e k r v : ℕ} (hk : 0 < k)
    (hr : rounded d (e+k) = r) (hv : r+1 = 2^k*v) :
    rounded d e = v := by
  have hcut : (2^(e+k)/d)/2^k = 2^e/d := by
    rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]
  have hvpos : 0 < v := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hv
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hvpos.ne'
  have htwo : 2 ≤ 2^k := Nat.le_pow hk
  have hfloor : (2^(e+k)/d)/2^k = v := by
    unfold rounded at hr
    apply Nat.div_eq_of_lt_le <;> nlinarith
  unfold rounded
  omega

private def geom (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => b * geom b n + 1

private theorem geom_eq {b q : ℕ} (hb : b = q+1) (n : ℕ) :
    b^n = q*geom b n+1 := by
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    rw [pow_succ, ih, geom]
    nlinarith [congrArg (fun t : ℕ => t+q*geom b n*b) hb]

/-- An odd `d` and `q=2^k-1` have a common binary period of at most `k*d`
even when they share prime factors. The modulus here is their product. -/
theorem short_period {d q k : ℕ} (hd : Odd d) (hq : Odd q) (hk : 2^k = q+1) :
    ∃ m : ℕ, 0 < m ∧ m ≤ d ∧ 2^(k*m) ≡ 1 [MOD q*d] := by
  classical
  let b := 2^k
  let f (i : Fin (d+1)) : Fin d := ⟨geom b i % d, Nat.mod_lt _ hd.pos⟩
  obtain ⟨x,y,hne,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have collision (i j : Fin (d+1)) (hij : i < j) (h : f i = f j) :
      ∃ m : ℕ, 0 < m ∧ m ≤ d ∧ 2^(k*m) ≡ 1 [MOD q*d] := by
    have ltij : (i : ℕ) < j := hij
    have hz : geom b i ≡ geom b j [MOD d] := congrArg Fin.val h
    have hp : b^(i : ℕ) ≡ b^(j : ℕ) [MOD q*d] := by
      rw [geom_eq hk, geom_eq hk]
      exact (hz.mul_left' q).add_right 1
    have hc : (q*d).Coprime (b^(i : ℕ)) :=
      ((Nat.coprime_two_left.mpr (hq.mul hd)).pow_left k |>.pow_left (i : ℕ)).symm
    have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ)-i) := by omega
    rw [hj] at hp
    rw [pow_add] at hp
    have he : 1 ≡ b^((j : ℕ)-i) [MOD q*d] :=
      Nat.ModEq.cancel_left_of_coprime hc (by simpa using hp)
    refine ⟨(j : ℕ)-i,by omega,by have := j.isLt; omega,?_⟩
    simpa only [pow_mul, b] using he.symm
  rcases lt_or_gt_of_ne hne with h|h
  · exact collision x y h heq
  · exact collision y x h heq.symm

/-- A small odd rounded value repeats as a proper divisor on its period. -/
theorem composite_on_period {d e q P : ℕ} (hd : 0 < d) (he : 0 < e)
    (hq : rounded d e = q) (hodd : Odd q) (hq' : 1 < q) (hP : 0 < P)
    (hper : 2^P ≡ 1 [MOD q*d]) (t : ℕ) (ht : 0 < t) :
    Odd (rounded d (e+P*t)) ∧ ¬ (rounded d (e+P*t)).Prime := by
  have hpow : 1 ≡ 2^(P*t) [MOD q*d] := by simpa only [pow_mul,one_pow] using (hper.pow t).symm
  obtain ⟨z,hz⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hpow
  have hp : 2^(P*t) = q*d*z+1 := by have := Nat.two_pow_pos (P*t); omega
  have hzpos : 0 < z := by
    have hh : 1 < 2^(P*t) := one_lt_pow₀ (by decide) (Nat.mul_pos hP ht).ne'
    by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hp; omega
  have hbig : rounded d (e+P*t) = q+q*(2^e*z) := by
    unfold rounded at *
    have expand : 2^(e+P*t) = 2^e + d*(q*(2^e*z)) := by rw [pow_add,hp]; ring
    rw [expand, Nat.add_mul_div_left _ _ hd]
    omega
  rw [hbig]
  have heven : Even (q*(2^e*z)) := ((even_two.pow_of_ne_zero he.ne').mul_right z).mul_left q
  refine ⟨hodd.add_even heven,?_⟩
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd q (dvd_add (dvd_refl q) (dvd_mul_right _ _)) with h|h
  · omega
  · have := Nat.mul_pos (show 0 < q by omega) (Nat.mul_pos (Nat.two_pow_pos e) hzpos)
    omega

/-- A small initial odd rounded value is itself one less than a power of two. -/
theorem small_witness {d : ℕ} (hd : Odd d) :
    ∃ e k q : ℕ, 0 < e ∧ e ≤ 2*(Nat.log 2 d+1) ∧ 0 < k ∧ k ≤ Nat.log 2 d+2 ∧
      Odd q ∧ 1 < q ∧ 2^k = q+1 ∧ rounded d e = q := by
  by_cases hd1 : d = 1
  · subst d; exact ⟨1,2,3,by decide⟩
  have hpos := hd.pos
  let L := Nat.log 2 d+1
  have hlo : d < 2^L := Nat.lt_pow_succ_log_self (by decide) d
  have hstrict : 2^(Nat.log 2 d) < d := by
    refine lt_of_le_of_ne (Nat.pow_log_le_self _ hpos.ne') ?_
    intro h
    by_cases hz : Nat.log 2 d = 0
    · simp [hz] at h; omega
    · exact (Nat.not_even_iff_odd.mpr hd) (h ▸ even_two.pow_of_ne_zero hz)
  have hhi : 2^L < 2*d := by dsimp [L]; rw [pow_succ]; omega
  let w := 2*d-2^L
  have hw : 0 < w ∧ w < d ∧ 2^L+w = 2*d := by dsimp [w]; omega
  have hex : ∃ t : ℕ, d < 2^t*w :=
    ⟨L,lt_of_lt_of_le hlo (Nat.le_mul_of_pos_right _ hw.1)⟩
  let t := Nat.find hex
  have ht : d < 2^t*w := Nat.find_spec hex
  have htL : t ≤ L := Nat.find_min' hex (lt_of_lt_of_le hlo (Nat.le_mul_of_pos_right _ hw.1))
  have htpos : 0 < t := by
    by_contra! h
    have ht0 : t = 0 := by omega
    simp [ht0] at ht
    omega
  have hprev : 2^(t-1)*w ≤ d := Nat.le_of_not_gt (Nat.find_min hex (show t-1<t by omega))
  have htwice : 2^t*w ≤ 2*d := by
    have h : (t-1)+1 = t := by omega
    calc
      2^t*w = 2*(2^(t-1)*w) := by nth_rw 1 [← h]; rw [pow_succ]; ring
      _ ≤ 2*d := by omega
  let q := 2^(t+1)-1
  have ht2 : 2 ≤ 2^t := Nat.le_pow htpos
  have hq : q+1 = 2^(t+1) := by dsimp [q]; have := Nat.two_pow_pos (t+1); omega
  have hq' : q+1 = 2^t*2 := by rw [hq, pow_succ]
  refine ⟨L+t,t+1,q,by dsimp [L]; omega,by change L+t ≤ 2*L; omega,
    by omega,by dsimp [L] at htL; omega,⟨2^t-1,by omega⟩,by omega,hq.symm,?_⟩
  have hprod : 2^(L+t)+2^t*w = 2^(t+1)*d := calc
    _ = 2^t*(2^L+w) := by rw [pow_add]; ring
    _ = _ := by rw [hw.2.2, pow_succ]; ring
  apply rounded_of_balance (u := 2^t*w-d) (by omega) (by omega)
  have hsub : 2^t*w-d+d = 2^t*w := by omega
  nlinarith [congrArg (fun x : ℕ => d*x) hq]

/-- Every interval of this explicit length contains an odd composite rounded value. -/
theorem prime_run_gap {d : ℕ} (hd : Odd d) (start : ℕ) :
    ∃ E : ℕ, start ≤ E ∧ E ≤ start+(d+2)*(Nat.log 2 d+2) ∧
      Odd (rounded d E) ∧ ¬ (rounded d E).Prime := by
  obtain ⟨e,k,q,he,hemax,hk,hkmax,hq,hq',hkq,hr⟩ := small_witness hd
  obtain ⟨m,hm,hmd,hper⟩ := short_period hd hq hkq
  let P := k*m
  have hP : 0 < P := Nat.mul_pos hk hm
  have hPmax : P ≤ (Nat.log 2 d+2)*d := Nat.mul_le_mul hkmax hmd
  let t := start/P+1
  have ht : 0 < t := Nat.succ_pos _
  have hdiv := Nat.div_add_mod start P
  have hmod := Nat.mod_lt start hP
  have hPt : P*t = P*(start/P)+P := by dsimp [t]; ring
  refine ⟨e+P*t,by omega,?_,composite_on_period hd.pos he hr hq hq' hP hper _ ht⟩
  calc
    e+P*t ≤ e+(start+P) := by omega
    _ ≤ 2*(Nat.log 2 d+2)+(start+(Nat.log 2 d+2)*d) :=
      Nat.add_le_add (by omega) (Nat.add_le_add_left hPmax _)
    _ = _ := by ring

/-- Each edge divides the shifted prime by its whole power of two.
The lower endpoint is included in the run. -/
inductive PureRun (d : ℕ) : ℕ → ℕ → Prop
  | point {e} : (rounded d e).Prime → PureRun d e e
  | step {e j bottom} : 0 < j → (rounded d (e+j)).Prime →
      rounded d (e+j)+1 = 2^j*rounded d e →
      PureRun d e bottom → PureRun d (e+j) bottom

theorem prime_at_odd_position {d top bottom s : ℕ} (run : PureRun d top bottom)
    (hlo : bottom ≤ s) (hhi : s ≤ top) (ho : Odd (rounded d s)) :
    (rounded d s).Prime := by
  induction run with
  | @point e hp =>
    have h : s = e := by omega
    simpa only [h] using hp
  | @step e j bottom hj hp hshift _ ih =>
    by_cases hs : s ≤ e
    · exact ih hlo hs
    by_cases ht : s = e+j
    · simpa only [ht] using hp
    let k := e+j-s
    let a := s-e
    have hk : 0 < k := by dsimp [k]; omega
    have ha : 0 < a := by dsimp [a]; omega
    have htop : s+k = e+j := by dsimp [k]; omega
    have hsum : k+a = j := by dsimp [k,a]; omega
    have heq : rounded d (e+j)+1 = 2^k*(2^a*rounded d e) := by
      rw [← mul_assoc, ← pow_add, hsum, hshift]
    have hval := rounded_at_shift (d := d) (e := s) hk (congrArg (rounded d) htop) heq
    exact False.elim ((Nat.not_even_iff_odd.mpr ho)
      (hval ▸ (even_two.pow_of_ne_zero ha.ne').mul_right _))

/-- An explicit bound on the span of a whole pure run of primes. -/
theorem pure_span {d top bottom : ℕ} (hd : Odd d) (run : PureRun d top bottom) :
    top < bottom+(d+2)*(Nat.log 2 d+2) := by
  obtain ⟨s,hlo,hhi,ho,hnp⟩ := prime_run_gap hd bottom
  by_contra! h
  exact hnp (prime_at_odd_position run hlo (hhi.trans h) ho)

/-- The power of two in the next shift cannot take a large exponent down by more
than the binary length of the current denominator. The minimum also covers a
shift that reaches exponent zero. -/
theorem shift_decrement {d E u r j : ℕ} (hu : 0 < u) (hud : u ≤ d)
    (hr : d*r = 2^E+u) (hj : 2^j ∣ r+1) :
    min j E ≤ Nat.log 2 d+1 := by
  let K := Nat.log 2 d+2
  have hsize : 2*d < 2^K := by
    dsimp [K]
    rw [show Nat.log 2 d+2 = (Nat.log 2 d+1)+1 by omega, pow_succ]
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) d
    omega
  by_contra! h
  have hk : K ≤ j ∧ K ≤ E := by dsimp [K]; omega
  have H : 2^K ∣ d*(r+1) :=
    dvd_mul_of_dvd_right ((Nat.pow_dvd_pow 2 hk.1).trans hj) d
  rw [Nat.mul_add, Nat.mul_one, hr, Nat.add_assoc] at H
  have dvd := (Nat.dvd_add_iff_right (Nat.pow_dvd_pow 2 hk.2)).mpr H
  have := Nat.le_of_dvd (show 0 < u+d by omega) dvd
  omega

/-- Consecutive pure runs with a growing odd denominator at their intervening
mixed edges. The last run may end before a further branching edge. -/
inductive Trace (D : ℕ) : ℕ → ℕ → ℕ → Prop
  | last {d top bottom} : Odd d → d ≤ D → PureRun d top bottom → Trace D d top bottom
  | mixed {d nextD top e next bottom} : Odd d → d ≤ D → 3*d ≤ nextD →
      PureRun d top e → e ≤ next+(Nat.log 2 d+1) →
      Trace D nextD next bottom → Trace D d top bottom

/-- The lengths of all pure runs add to a bound in the largest denominator. -/
theorem trace_span {D d top bottom : ℕ} (tr : Trace D d top bottom) :
    top + 2*d*(Nat.log 2 D+2) ≤ bottom + 6*D*(Nat.log 2 D+2) := by
  let H := Nat.log 2 D+2
  change top+2*d*H ≤ bottom+6*D*H
  induction tr with
  | @last d top bottom hd hD run =>
    have hH : Nat.log 2 d+2 ≤ H := Nat.add_le_add_right (Nat.log_mono_right hD) _
    have hs := (pure_span hd run).le.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left (d+2) hH) bottom)
    have hle : 3*d+2 ≤ 6*D := by have := hd.pos; omega
    calc
      top+2*d*H ≤ (bottom+(d+2)*H)+2*d*H := by omega
      _ = bottom+(3*d+2)*H := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right H hle) _
  | @mixed d nextD top e next bottom hd hD hg run hstep _ ih =>
    have hH : Nat.log 2 d+2 ≤ H := Nat.add_le_add_right (Nat.log_mono_right hD) _
    have hs := (pure_span hd run).le.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left (d+2) hH) e)
    have hle : 3*d+3 ≤ 2*nextD := by have := hd.pos; omega
    calc
      top+2*d*H ≤ (next+H)+(d+2)*H+2*d*H := by omega
      _ = next+(3*d+3)*H := by ring
      _ ≤ next+2*nextD*H := Nat.add_le_add_left (Nat.mul_le_mul_right H hle) _
      _ ≤ _ := ih

end Erdos1052.PrimeRuns
