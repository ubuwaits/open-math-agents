import Mathlib

/-! Dyadic separation and the logarithmic widths of the mandatory-block intervals. -/

namespace Erdos1052.WindowBounds

abbrev Interval := ℚ × ℚ

def allocations : List ℚ → List Interval
  | [] => [(1,2)]
  | w::ws => (allocations ws).flatMap fun (l,u) => [(w*l,u),(l,u/w)]

def raw : List Interval :=
  allocations [1024/607,256/223,4096/3967] ++
  allocations [1024/607,256/223,32/31,8192/8191] ++
  allocations [32/19,2048/1783,1024/991]

def windows : List Interval :=
  [(1,33572107/33554432),(32/31,135361/131072),(1024/991,33877/32768),
   (256/223,18817/16384),(2048/1783,18829/16384),(8192/6913,607/512),
   (2097152/1766953,19/16),(32/19,1766953/1048576),(1024/607,6913/4096),
   (32768/18829,1783/1024),(32768/18817,223/128),(65536/33877,991/512),
   (262144/135361,31/16),(67108864/33572107,2)]

def wideWindows : List Interval :=
  [(1,33572107/33554432),(2097152/2031647,135361/131072),
   (67108864/64947167,33877/32768),(16777216/14614751,18817/16384),
   (134217728/116852471,18829/16384),(536870912/453057281,607/512),
   (137438953472/115800798761,19/16),(2097152/1245203,1766953/1048576),
   (67108864/39780959,6913/4096),(2147483648/1233996173,1783/1024),
   (2147483648/1233209729,223/128),(4294967296/2220196949,991/512),
   (17179869184/8871153857,31/16),(4398046511104/2200215176459,2)]

def widen (w : Interval) : List Interval :=
  let l := w.1*65536/65537
  if l<1 then [(1,w.2),(2*l,2)] else [(l,w.2)]

def covers (W : List Interval) (w : Interval) : Bool :=
  W.any fun t => decide (t.1≤w.1 ∧ w.2≤t.2)

def widthProduct (W : List Interval) : ℚ := (W.map fun w => w.2/w.1).prod

theorem covers_all_allocations : raw.all (covers windows) = true ∧
    (raw.flatMap widen).all (covers wideWindows) = true := by decide +kernel

theorem upper_dyadic : windows.all (fun w =>
    decide (w.2≤2 ∧ (w.2*(2:ℚ)^25).den=1)) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem total_width : widthProduct windows ^ 100 < 2 ∧
    widthProduct wideWindows ^ 97 < 2 := by decide +kernel

/-- Numerators over a common dyadic denominator separate by at least one. -/
theorem separation {a m u p : ℕ} (hu : u ≤ 2 ^ (m + 1)) (hgap : u < p)
    (hclose : 2 ^ a * p < (2 ^ a + 1) * u) : a ≤ m := by
  by_contra! hm
  have h₁ : 2 ^ (m + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) hm
  have h₂ := Nat.mul_le_mul_left (2 ^ a) (show u + 1 ≤ p by omega)
  rw [Nat.mul_add, Nat.mul_one] at h₂
  rw [Nat.add_mul, Nat.one_mul] at hclose
  omega

theorem odd_multiplier {h b s : ℕ} (hh : 16 ≤ h) (hb : Odd b)
    (hcap : h * b ≤ max (h + s) 35) : h * (b - 1) ≤ s := by
  by_cases hsmall : b ≤ 1
  · simp [show b - 1 = 0 by omega]
  obtain ⟨k,hk⟩ := hb
  have hb3 : 3 ≤ b := by omega
  have h35 : 35 < h * b :=
    lt_of_lt_of_le (show 35 < h * 3 by omega) (Nat.mul_le_mul_left h hb3)
  have he : h * b ≤ h + s := by omega
  have he' : h * b = h * (b - 1) + h := by
    conv_lhs => rw [show b = (b - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
  omega

/-- Multiplying the group by the binary correction puts the core abundancy
in the complementary upper endpoint for every exponent. -/
theorem corrected_allocation {B C ρ z l w : ℚ} (hB : 0<B) (hw : 0<w)
    (hρ : 1<ρ) (hz : 0<z) (hC : w≤C) (hl : l≤B)
    (h : B*(1+z)*C*ρ=2) :
    l<B*(1+z) ∧ B*(1+z)≤2/(ρ*w) ∧ B*(1+z)<2/w := by
  have hbz : 0<B*(1+z) := by positivity
  have hwc := mul_le_mul_of_nonneg_left hC hbz.le
  have hρp : 0<ρ := by linarith
  have hcap := mul_le_mul_of_nonneg_right hwc hρp.le
  constructor
  · nlinarith [mul_pos hB hz]
  constructor
  · apply (le_div_iff₀ (mul_pos hρp hw)).mpr
    nlinarith
  · apply (lt_div_iff₀ hw).mpr
    nlinarith [mul_pos (mul_pos hbz hw) (sub_pos.mpr hρ)]

/-- Two positive dyadic normalizations in one octave must coincide. -/
theorem unique_octave {x y : ℚ} {j k : ℤ} (hx : 1≤x) (hx' : x<2)
    (hy : 1≤y) (hy' : y<2) (eqn : x*(2:ℚ)^j=y*2^k) : x=y := by
  have ordered {a b : ℤ} {r t : ℚ} (hr : r < 2) (ht : 1 ≤ t) (hab : a < b) :
      r*(2:ℚ)^a < t*2^b := calc
    r*(2:ℚ)^a < 2^a*2 := by rw [mul_comm (2^a)]; gcongr
    _ = 2^(a+1) := (zpow_add_one₀ (by norm_num : (2:ℚ)≠0) _).symm
    _ ≤ 2^b := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ ≤ t*2^b := le_mul_of_one_le_left (by positivity) ht
  rcases lt_trichotomy j k with hj | rfl | hk
  · exact False.elim ((ordered hx' hy hj).ne eqn)
  · exact mul_right_cancel₀ (by positivity : (2:ℚ)^j≠0) eqn
  · exact False.elim ((ordered hy' hx hk).ne eqn.symm)

/-- A terminal divisor is bounded by its original seed. -/
theorem terminal_le_seed {A D : ℕ} {s : Finset ℕ} (hp : ∀ q∈s, q.Prime ∧ q≠2)
    (h : A*(∏ q∈s, ordCompl[2] (1+q))=D*(∏ q∈s, q)) : D≤A := by
  have hprod : (∏ q∈s, ordCompl[2] (1+q)) ≤ ∏ q∈s, q := by
    apply Finset.prod_le_prod'
    intro q hq
    have hodd := ((hp q hq).1.eq_two_or_odd).resolve_left (hp q hq).2
    have hval := Nat.prime_two.factorization_pos_of_dvd (n:=1+q) (by omega) (by omega)
    have ht := Nat.le_pow hval (a:=2)
    have he := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
    have hm := Nat.mul_le_mul_right (ordCompl[2] (1+q)) ht
    omega
  have hs := Finset.prod_pos (fun q hq => (hp q hq).1.pos)
  apply Nat.le_of_mul_le_mul_right _ hs
  rw [←h]
  exact Nat.mul_le_mul_left _ hprod

end Erdos1052.WindowBounds
