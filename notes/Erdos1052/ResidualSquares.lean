import Mathlib

/-! Rational inequalities and finite residue calculations for squared Mersenne
and Fermat residual divisors in the sparse-core problem. -/

namespace Erdos1052.ResidualSquares

/-- All larger Fermat bases together have a telescoping normalized product. -/
theorem fermat_product (x : ℚ) (n : ℕ) :
    (1-x^2)*(∏ i ∈ Finset.range n, (1+x^(2^(i+1)))) = 1-x^(2^(n+1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ,←mul_assoc,ih]
    rw [show 2^(n+1+1)=2^(n+1)*2 by ring, pow_mul]
    ring

/-- The two upper thresholds that exclude a small Mersenne start or the
simultaneous occurrence of the start and its first doubling. -/
theorem fermat_thresholds {x : ℚ} (hx : 0<x) (hs : x<1/3) :
    (1+x^2)/(1-x)^2 < 1/(1-2*x) ∧ (1+x)/(1-x)^2 < 1/(1-3*x) := by
  have h1 : 0 < (1-x)^2 := sq_pos_of_pos (by linarith)
  constructor
  · apply (div_lt_div_iff₀ h1 (by linarith)).mpr
    nlinarith [mul_pos hx (sq_pos_of_pos hx)]
  · apply (div_lt_div_iff₀ h1 (by linarith)).mpr
    nlinarith [sq_pos_of_pos hx]

/-- A root followed no earlier than `u*r-1`. -/
theorem root_loss (r u : ℚ) (hr : 1<r) (hu : 2≤u) :
    1-1/(((r+1)/r)*((u*r)/(u*r-2)))=(1+2/u)/(r+1) := by
  have ht : 0<u*r-2 := by nlinarith [mul_pos (show 0<u by linarith) (show 0<r-1 by linarith)]
  field_simp; ring

/-- A root whose first successor is `2*r-1` and whose next multiplier is at least 8. -/
theorem two_step_loss (r : ℚ) (hr : 1<r) :
    1-1/(((r+1)/r)*(2*r/(2*r-1))*(8*(2*r-1)/(8*(2*r-1)-2)))=(13/8)/(r+1) := by
  have h1 : 0<2*r-1 := by linarith
  have h2 : 0<8*(2*r-1)-2 := by linarith
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r+1 ≠ 0 := by linarith
  field_simp [h1.ne',h2.ne',hr0,hr1]
  ring_nf
  field_simp [show -1+r*2 ≠ 0 by linarith]
  ring

/-- All geometric starts involving some larger Fermat base cost less than `3*x²`. -/
theorem larger_fermat_roots {x : ℚ} (hx : 0<x) (hs : x<1/3) :
    2*(1+x)*(1/(1-x^2)-1) < 3*x^2 := by
  have h : 0<1-x^2 := by nlinarith [mul_pos (show 0<1-x by linarith) (show 0<1+x by linarith)]
  field_simp
  nlinarith [mul_pos (sq_pos_of_pos hx) (mul_pos (show 0<1-3*x by linarith) (show 0<1+x by linarith))]

/-- The three near-one thresholds have enough room for every larger Fermat base. -/
theorem fermat_gaps {X : ℚ} (hX : 65536≤X) :
    507/(512*(X-1))+3/X^2 < 1/(X+1) ∧
    13/(8*X)+5/X^2 < 2/(X+2) ∧ 287/(96*X)+3/X^2 < 3/(X+3) := by
  have hx : 0<X := by linarith
  have h1 : 0<X-1 := by linarith
  have h2 : 0<X+2 := by linarith
  have h3 : 0<X+3 := by linarith
  have h4 : 0<X+1 := by linarith
  have A := mul_nonneg (show 0≤X-65536 by linarith) (sq_nonneg X)
  have B := mul_nonneg (show 0≤X-65536 by linarith) (show 0≤X by linarith)
  refine ⟨?_,?_,?_⟩ <;> field_simp <;> nlinarith [sq_nonneg X]

/-- Lower loss for a square Mersenne residual above the Fermat scale. -/
theorem mersenne_lower {d y z : ℚ} (hd : 0≤d) (hd' : d≤1/8)
    (hy : 0<y) (hy' : y≤1/65536) (hz : 0≤z) (hz' : z≤y^3) :
    (1-2*d)*y-3*y^2 ≤ 1-(1+z)/((1+y)*(1-d*y)^2) := by
  let t := (1+y)*(1-d*y)^2-1
  have hdy : 0≤d*y := mul_nonneg hd hy.le
  have hdy' : d*y≤y/8 := by nlinarith [mul_nonneg (sub_nonneg.mpr hd') hy.le]
  have hv : 0<1-d*y := by linarith
  have ht : (1-2*d)*y-2*d*y^2≤t := by
    dsimp [t]; nlinarith [mul_nonneg (show 0≤1+y by linarith) (sq_nonneg (d*y))]
  have htl : 0≤t := by
    have := mul_nonneg (show 0≤(1:ℚ)/8-d by linarith) (sq_nonneg y)
    have := mul_nonneg (show 0≤1-y by linarith) hy.le
    nlinarith
  have htu : t≤y := by
    dsimp [t]; nlinarith [mul_nonneg (show 0≤1+y by linarith) (mul_nonneg hdy (show 0≤2-d*y by linarith))]
  have ht1 : 0<1+t := by linarith
  have hb : t-t^2-z ≤ 1-(1+z)/(1+t) := by
    rw [le_sub_iff_add_le,←le_sub_iff_add_le']
    apply (div_le_iff₀ ht1).mpr
    nlinarith [mul_nonneg htl (sq_nonneg t),mul_nonneg htl hz]
  have hs : (1+y)*(1-d*y)^2=1+t := by dsimp [t]; ring
  rw [hs]
  apply le_trans _ hb
  have hsq := mul_nonneg (sub_nonneg.mpr htu) (show 0≤y+t by linarith)
  have h3 := mul_nonneg (sq_nonneg y) (show 0≤1-y by linarith)
  have h4 := mul_nonneg (sq_nonneg y) (show 0≤1-2*d by linarith)
  nlinarith

/-- Exact margins for the two upper Mersenne cases. -/
theorem mersenne_gaps {y d : ℚ} (hy : 0<y) (hs : y≤1/65536) (ht : d≤1/32) :
    (23/24-2*d)*y+5*d*y/(4*(1-d*y)) < (1-2*d)*y-3*y^2 ∧
    31*y/48+11*y/(16*(8-y)) < 3*y/4-3*y^2 := by
  have hb : d*y≤y/32 := by nlinarith [mul_nonneg (show 0≤1/32-d by linarith) hy.le]
  have h1 : 0<1-d*y := by linarith
  have h2 : 0<8-y := by linarith
  have low : 999/1000≤1-d*y := by linarith
  have hA : 5*d/(4*(1-d*y)) ≤ 1/25 := by
    apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hB : 11/(16*(8-y)) ≤ 9/100 := by
    apply (div_le_iff₀ (by positivity)).mpr; linarith
  have a := mul_le_mul_of_nonneg_right hA hy.le
  have b := mul_le_mul_of_nonneg_right hB hy.le
  have c := mul_nonneg (sub_nonneg.mpr hs) hy.le
  constructor
  · rw [show 5*d*y/(4*(1-d*y))=5*d/(4*(1-d*y))*y by ring]
    nlinarith
  · rw [show 11*y/(16*(8-y))=11/(16*(8-y))*y by ring]
    nlinarith

/-- An entire ten-term string of odd halves avoiding 11 starts at 1 modulo 11. -/
theorem ten_halves : ∀ a : ZMod 11,
    (∀ i : Fin 10, 1+(a-1)*6^i.val ≠ 0) → a=1 := by decide

private theorem powers (v : ℕ) : let y := (2:ZMod 11)^(2^v); y≠0 ∧ y^2≠1 := by
  induction v with
  | zero => decide
  | succ v ih =>
    simp only [pow_succ 2 v,pow_mul]
    exact (by decide : ∀ z : ZMod 11, z≠0 ∧ z^2≠1 → z^2≠0 ∧ (z^2)^2≠1) _ ih

/-- Two consecutive odd quotient blocks cannot both have all ten odd halves
free of multiples of 11. -/
theorem terminal_halves (v m : ℕ) (a b : ZMod 11) (y : ZMod 11)
    (hy : y=(2:ZMod 11)^(2^v)) (ha : (y+1)*a=y^m+1)
    (hb : (y+1)*b=y^(m+2)+1) (h1 : ∀ i : Fin 10, 1+(a-1)*6^i.val≠0)
    (h2 : ∀ i : Fin 10, 1+(b-1)*6^i.val≠0) : False := by
  obtain ⟨hn,hn2⟩ := hy ▸ powers v
  rw [ten_halves a h1,mul_one] at ha
  rw [ten_halves b h2,mul_one,pow_add] at hb
  have he : y=y^m := by linear_combination ha
  rw [←he] at hb
  have hf : y*(y^2-1)=0 := by linear_combination -hb
  exact (by decide : ∀ z : ZMod 11, z≠0 → z^2≠1 → z*(z^2-1)≠0) y hn hn2 hf

end Erdos1052.ResidualSquares
