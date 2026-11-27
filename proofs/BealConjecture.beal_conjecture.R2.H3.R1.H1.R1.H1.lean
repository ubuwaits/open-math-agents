import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1
import Mathlib

-- Credit: @ubuwaits

/-!
# Integral square roots in the pure cubic ring

At an odd square, the two cubic factors of the dyadic difference are relatively prime. The norm and the parity of two coordinates determine the unit modulo squares.
-/

namespace BealDescent

/-- Integral coordinates in the basis 1, α, α², where α³ = 2. -/
structure Cubic where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

namespace Cubic

theorem ext {x y : Cubic} (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) : x = y := by
  cases x; cases y; congr

instance : Add Cubic := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg Cubic := ⟨fun x => ⟨-x.a, -x.b, -x.c⟩⟩
instance : Zero Cubic := ⟨⟨0, 0, 0⟩⟩
instance : One Cubic := ⟨⟨1, 0, 0⟩⟩
instance : Mul Cubic := ⟨fun x y =>
  ⟨x.a*y.a + 2*(x.b*y.c + x.c*y.b),
   x.a*y.b + x.b*y.a + 2*x.c*y.c,
   x.a*y.c + x.b*y.b + x.c*y.a⟩⟩

theorem mul_a (x y : Cubic) : (x*y).a = x.a*y.a+2*(x.b*y.c+x.c*y.b) := rfl
theorem mul_b (x y : Cubic) : (x*y).b = x.a*y.b+x.b*y.a+2*x.c*y.c := rfl
theorem mul_c (x y : Cubic) : (x*y).c = x.a*y.c+x.b*y.b+x.c*y.a := rfl
theorem add_a (x y : Cubic) : (x+y).a = x.a+y.a := rfl
theorem add_b (x y : Cubic) : (x+y).b = x.b+y.b := rfl
theorem add_c (x y : Cubic) : (x+y).c = x.c+y.c := rfl
theorem neg_a (x : Cubic) : (-x).a = -x.a := rfl
theorem neg_b (x : Cubic) : (-x).b = -x.b := rfl
theorem neg_c (x : Cubic) : (-x).c = -x.c := rfl
theorem zero_a : (0 : Cubic).a = 0 := rfl
theorem zero_b : (0 : Cubic).b = 0 := rfl
theorem zero_c : (0 : Cubic).c = 0 := rfl
theorem one_a : (1 : Cubic).a = 1 := rfl
theorem one_b : (1 : Cubic).b = 0 := rfl
theorem one_c : (1 : Cubic).c = 0 := rfl

instance : CommRing Cubic := by
  apply CommRing.ofMinimalAxioms <;> intros <;>
    apply Cubic.ext <;> simp only [mul_a, mul_b, mul_c, add_a, add_b, add_c, neg_a, neg_b, neg_c, zero_a, zero_b, zero_c, one_a, one_b, one_c] <;> ring

instance : Nontrivial Cubic := ⟨0, 1, by decide⟩

def scalar (z : ℤ) : Cubic := ⟨z,0,0⟩

def intMap : ℤ →+* Cubic where
  toFun := scalar
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intro x y; apply ext <;> simp [scalar, add_a, add_b, add_c]
  map_mul' := by intro x y; apply ext <;> simp [scalar, mul_a, mul_b, mul_c]

theorem scalar_eq (z : ℤ) : scalar z = (z : Cubic) := map_intCast intMap z

def norm (x : Cubic) : ℤ := x.a^3 + 2*x.b^3 + 4*x.c^3 - 6*x.a*x.b*x.c

theorem norm_mul (x y : Cubic) : norm (x*y) = norm x * norm y := by
  change (x.a*y.a + 2*(x.b*y.c + x.c*y.b))^3 + 2*(x.a*y.b+x.b*y.a+2*x.c*y.c)^3
    + 4*(x.a*y.c + x.b*y.b + x.c*y.a)^3
    - 6*(x.a*y.a + 2*(x.b*y.c + x.c*y.b))*(x.a*y.b+x.b*y.a+2*x.c*y.c)*
      (x.a*y.c + x.b*y.b + x.c*y.a) = _
  simp only [norm]
  ring

theorem norm_one : norm 1 = 1 := rfl

theorem norm_zero : norm 0 = 0 := rfl

theorem norm_scalar (z : ℤ) : norm (scalar z) = z^3 := by simp [norm, scalar]

def adj (x : Cubic) : Cubic :=
  ⟨x.a^2-2*x.b*x.c, 2*x.c^2-x.a*x.b, x.b^2-x.a*x.c⟩

theorem mul_adj (x : Cubic) : x * adj x = scalar (norm x) := by
  apply ext <;> simp only [mul_a,mul_b,mul_c,adj,scalar,norm] <;> ring

theorem norm_adj (x : Cubic) : norm (adj x) = (norm x)^2 := by
  simp only [adj, norm]; ring

theorem even_of_cube_even {z : ℤ} (hz : 2 ∣ z^3) : 2 ∣ z :=
  Int.prime_two.dvd_of_dvd_pow hz

private theorem even_coordinates {x : Cubic} (hx : norm x = 0) :
    2 ∣ x.a ∧ 2 ∣ x.b ∧ 2 ∣ x.c := by
  rcases x with ⟨a,b,c⟩
  change a^3 + 2*b^3 + 4*c^3 - 6*a*b*c = 0 at hx
  have ha : 2 ∣ a := even_of_cube_even ⟨-b^3 - 2*c^3 + 3*a*b*c, by linarith⟩
  obtain ⟨u, rfl⟩ := ha
  have hb : 2 ∣ b := even_of_cube_even ⟨-2*u^3 - c^3 + 3*u*b*c, by nlinarith only [hx]⟩
  obtain ⟨v, rfl⟩ := hb
  have hc : 2 ∣ c := even_of_cube_even ⟨-u^3 - 2*v^3 + 3*u*v*c, by nlinarith only [hx]⟩
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hc⟩

theorem eq_zero_of_norm_zero (x : Cubic) (hx : norm x = 0) : x = 0 := by
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩,⟨w,hw⟩⟩ := even_coordinates hx
  by_cases h : u = 0 ∧ v = 0 ∧ w = 0
  · rcases h with ⟨rfl,rfl,rfl⟩
    exact ext (by simpa [zero_a] using hu) (by simpa [zero_b] using hv) (by simpa [zero_c] using hw)
  · let y : Cubic := ⟨u,v,w⟩
    have hy : norm y = 0 := by
      dsimp [norm] at hx
      rw [hu,hv,hw] at hx
      dsimp [y,norm]
      nlinarith only [hx]
    have hsmall : u.natAbs + v.natAbs + w.natAbs < x.a.natAbs + x.b.natAbs + x.c.natAbs := by
      rw [hu,hv,hw]
      simp only [Int.natAbs_mul, show (2:ℤ).natAbs = 2 from rfl]
      have := Int.natAbs_eq_zero (a := u)
      have := Int.natAbs_eq_zero (a := v)
      have := Int.natAbs_eq_zero (a := w)
      omega
    have he := eq_zero_of_norm_zero y hy
    exact False.elim (h ⟨congrArg a he, congrArg b he, congrArg c he⟩)
termination_by x.a.natAbs + x.b.natAbs + x.c.natAbs
decreasing_by exact hsmall

end Cubic

end BealDescent

namespace BealDescent

namespace NormCover

/-- Endpoints of a rational interval. -/
structure Box where
  lo : ℚ
  hi : ℚ

def Box.contains (I : Box) (x : ℚ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

def Box.mul (I J : Box) : Box :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩

private theorem linear_between {x l h s : ℚ} {I : Box} (hx : l ≤ x ∧ x ≤ h)
    (hl : I.contains (l*s)) (hh : I.contains (h*s)) : I.contains (x*s) := by
  rcases le_total 0 s with hs | hs
  · exact ⟨hl.1.trans (mul_le_mul_of_nonneg_right hx.1 hs),
      (mul_le_mul_of_nonneg_right hx.2 hs).trans hh.2⟩
  · exact ⟨hh.1.trans (mul_le_mul_of_nonpos_right hx.2 hs),
      (mul_le_mul_of_nonpos_right hx.1 hs).trans hl.2⟩

theorem Box.contains_mul {I J : Box} {x y : ℚ} (hx : I.contains x) (hy : J.contains y) :
    (I.mul J).contains (x*y) := by
  apply linear_between hx
  all_goals rw [mul_comm _ y]; apply linear_between hy
  all_goals dsimp only [Box.mul, Box.contains]; simp only [min_le_iff, le_max_iff]; constructor <;> first | left; left; exact le_of_eq (mul_comm ..) | left; right; exact le_of_eq (mul_comm ..) | right; left; exact le_of_eq (mul_comm ..) | right; right; exact le_of_eq (mul_comm ..)

def cell (i : Fin 6) (u : Fin 2) : Box :=
  let a : ℚ := (i.val : ℚ) - 6 * (u.val : ℚ)
  ⟨a, a+1⟩

def good (I J K : Box) : Prop :=
  let P := (I.mul J).mul K
  (-216 : ℚ) < I.lo^3 + 2*J.lo^3 + 4*K.lo^3 - 6*P.hi ∧
    I.hi^3 + 2*J.hi^3 + 4*K.hi^3 - 6*P.lo < 216

instance (I J K : Box) : Decidable (good I J K) := by unfold good; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem cells_cover : ∀ i j k : Fin 6, ∃ u v w : Fin 2,
    good (cell i u) (cell j v) (cell k w) := by decide +kernel

private theorem choose_cell (x : ℚ) :
    ∃ n : ℤ, ∃ i : Fin 6, (i.val : ℚ) ≤ 6*(x-n) ∧ 6*(x-n) ≤ i.val + 1 := by
  let n := ⌊x⌋
  let r := 6*(x-(n:ℚ))
  have hn := Int.floor_le x
  have hn' := Int.lt_floor_add_one x
  have hr : 0 ≤ r := by change 0 ≤ 6*(x-↑⌊x⌋); linarith
  have hr' : r < 6 := by change 6*(x-↑⌊x⌋) < 6; linarith
  have hi : 0 ≤ ⌊r⌋ := Int.floor_nonneg.mpr hr
  have hi' : ⌊r⌋ < 6 := (Int.floor_lt).mpr (by exact_mod_cast hr')
  refine ⟨n, ⟨⌊r⌋.toNat, by omega⟩, ?_, ?_⟩
  · change (⌊r⌋.toNat : ℚ) ≤ r
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hi]
    exact Int.floor_le r
  · change r ≤ (⌊r⌋.toNat : ℚ) + 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hi]
    exact (Int.lt_floor_add_one r).le

private theorem shifted_cell {x : ℚ} {n : ℤ} {i : Fin 6}
    (h : (i.val : ℚ) ≤ 6*(x-n) ∧ 6*(x-n) ≤ i.val+1) (u : Fin 2) :
    (cell i u).contains (6*(x-((n+(u.val:ℤ):ℤ):ℚ))) := by
  dsimp [cell, Box.contains]
  push_cast
  constructor <;> linarith [h.1,h.2]

def form (x y z : ℚ) : ℚ := x^3 + 2*y^3 + 4*z^3 - 6*x*y*z

private theorem bound {I J K : Box} (hg : good I J K) {x y z : ℚ}
    (hx : I.contains x) (hy : J.contains y) (hz : K.contains z) :
    |form x y z| < 216 := by
  have hp := Box.contains_mul (Box.contains_mul hx hy) hz
  have cube_mono : Monotone (fun v : ℚ => v^3) := (by decide : Odd 3).strictMono_pow.monotone
  rcases hg with ⟨hl,hh⟩
  apply abs_lt.mpr
  dsimp [form]
  constructor
  · linarith only [cube_mono hx.1,cube_mono hy.1,cube_mono hz.1,hp.2,hl]
  · linarith only [cube_mono hx.2,cube_mono hy.2,cube_mono hz.2,hp.1,hh]

/-- Every rational triple has an integral translate of absolute norm less than one. -/
theorem round (x y z : ℚ) : ∃ a b c : ℤ, |form (x-a) (y-b) (z-c)| < 1 := by
  obtain ⟨n,i,hi⟩ := choose_cell x
  obtain ⟨m,j,hj⟩ := choose_cell y
  obtain ⟨l,k,hk⟩ := choose_cell z
  obtain ⟨u,v,w,h⟩ := cells_cover i j k
  refine ⟨n+u.val,m+v.val,l+w.val,?_⟩
  have hb := bound h (shifted_cell hi u) (shifted_cell hj v) (shifted_cell hk w)
  have scale (A B C : ℚ) : form (6*A) (6*B) (6*C) = 216 * form A B C := by dsimp [form]; ring
  rw [scale, abs_mul] at hb
  norm_num at hb
  push_cast
  exact hb

end NormCover

end BealDescent

namespace BealDescent.Cubic

/-- Divide in the cubic field, then round its three rational coordinates. -/
theorem division (x y : Cubic) (hy : y ≠ 0) :
    ∃ t : Cubic, |norm (x-y*t)| < |norm y| := by
  let d := norm y
  let e := x * adj y
  have hdi : d ≠ 0 := fun h => hy (eq_zero_of_norm_zero y h)
  have hd : (d:ℚ) ≠ 0 := by exact_mod_cast hdi
  obtain ⟨u,v,w,h⟩ := NormCover.round (e.a/d) (e.b/d) (e.c/d)
  let t : Cubic := ⟨u,v,w⟩
  refine ⟨t, ?_⟩
  have he : (x-y*t)*adj y = e - scalar d * t := by
    dsimp only [e,d]
    rw [← mul_adj]; ring
  have hn : norm (x-y*t) * d^2 = norm (e-scalar d*t) := by
    rw [← he,norm_mul,norm_adj]
  have hc : (norm (e-scalar d*t) : ℚ) =
      (d:ℚ)^3 * NormCover.form (e.a/d-u) (e.b/d-v) (e.c/d-w) := by
    simp only [sub_eq_add_neg,norm,add_a,add_b,add_c,neg_a,neg_b,neg_c,mul_a,mul_b,mul_c,
      scalar,t,Int.cast_add,Int.cast_neg,Int.cast_mul,Int.cast_pow,Int.cast_zero,Int.cast_ofNat,NormCover.form]
    field_simp
    ring
  have hnq : (norm (x-y*t) : ℚ) * (d:ℚ)^2 = (norm (e-scalar d*t) : ℚ) := by exact_mod_cast hn
  have hr : (norm (x-y*t):ℚ) / d = NormCover.form (e.a/d-u) (e.b/d-v) (e.c/d-w) := by
    apply (div_eq_iff hd).2
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    linear_combination hnq.trans hc
  rw [← hr,abs_div,div_lt_one (abs_pos.mpr hd)] at h
  exact_mod_cast h

noncomputable def quotient (x y : Cubic) : Cubic :=
  if h : y = 0 then 0 else (division x y h).choose

noncomputable instance : EuclideanDomain Cubic where
  quotient := quotient
  quotient_zero _ := dif_pos rfl
  remainder x y := x-y*quotient x y
  quotient_mul_add_remainder_eq x y := by ring
  r x y := (norm x).natAbs < (norm y).natAbs
  r_wellFounded := (measure fun x : Cubic => (norm x).natAbs).wf
  remainder_lt x y hy := by
    rw [quotient,dif_neg hy]
    have transfer (a b : ℤ) (h : |a| < |b|) : a.natAbs < b.natAbs := by
      simp only [Int.abs_eq_natAbs] at h
      exact_mod_cast h
    exact transfer _ _ (division x y hy).choose_spec
  mul_left_not_lt x y hy := by
    rw [norm_mul,Int.natAbs_mul]
    have hb := Nat.pos_of_ne_zero (fun h => hy (eq_zero_of_norm_zero _ (Int.natAbs_eq_zero.mp h)))
    nlinarith only [Nat.mul_le_mul_left (norm x).natAbs hb]

end BealDescent.Cubic

namespace BealDescent.Cubic

noncomputable def root : ℝ := (2 : ℝ) ^ ((3 : ℝ)⁻¹)

theorem root_cube : root ^ 3 = 2 :=
  Real.rpow_inv_natCast_pow (n := 3) (by norm_num) (by decide)

theorem root_bounds : 1 < root ∧ root < 13/10 := by
  have h := root_cube
  have hm : StrictMono (fun t : ℝ => t^3) := (by decide : Odd 3).strictMono_pow
  exact ⟨hm.lt_iff_lt.mp (by norm_num [h]), hm.lt_iff_lt.mp (by norm_num [h])⟩

noncomputable def realValue : Cubic →+* ℝ where
  toFun x := x.a + x.b*root + x.c*root^2
  map_zero' := by simp [zero_a,zero_b,zero_c]
  map_one' := by simp [one_a,one_b,one_c]
  map_add' := by intro x y; simp only [add_a,add_b,add_c,Int.cast_add]; ring
  map_mul' := by
    intro x y
    simp only [mul_a,mul_b,mul_c,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    linear_combination -((x.b:ℝ)*y.c+x.c*y.b+x.c*y.c*root) * root_cube

def normHom : Cubic →* ℤ where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

theorem unit_norm (u : Cubicˣ) : norm (u:Cubic) = 1 ∨ norm (u:Cubic) = -1 :=
  Int.isUnit_iff.mp (u.isUnit.map normHom)

def epsilon : Cubicˣ := ⟨⟨1,1,1⟩,⟨-1,1,0⟩,by decide,by decide⟩

theorem epsilon_value : realValue (epsilon:Cubic) = 1 + root + root^2 := by
  norm_num [realValue,epsilon]

private theorem epsilon_bounds : 1 < realValue (epsilon:Cubic) ∧ realValue (epsilon:Cubic) < 4 := by
  rw [epsilon_value]
  have h := root_bounds
  constructor
  · nlinarith only [h.1,sq_nonneg root]
  · have hs : root^2 < (13/10 : ℝ)^2 := by
      exact pow_lt_pow_left₀ h.2 (by linarith [h.1]) (by decide)
    linarith

private theorem coord_choices (n : ℤ) (t S : ℝ) (ht : 1 ≤ t)
    (hs : 1 ≤ S ∧ S < 4) (hc : (3*((n:ℝ)*t)-S)^2 ≤ 2^2) : n=0 ∨ n=1 := by
  obtain ⟨hl,hh⟩ := abs_le_of_sq_le_sq' hc (by norm_num : (0:ℝ) ≤ 2)
  by_contra! h
  rcases (show n ≤ -1 ∨ 2 ≤ n by omega) with hn | hn
  · have hn' : (n:ℝ) ≤ -1 := by exact_mod_cast hn
    have := mul_le_mul_of_nonneg_right hn' (by linarith : 0 ≤ t)
    linarith [hs.1]
  · have hn' : 2 ≤ (n:ℝ) := by exact_mod_cast hn
    have := mul_le_mul_of_nonneg_right hn' (by linarith : 0 ≤ t)
    linarith [hs.2]

/-- No unit has real value strictly between 1 and 1 + α + α². -/
theorem unit_in_interval (u : Cubicˣ) (hl : 1 ≤ realValue (u:Cubic))
    (hh : realValue (u:Cubic) < realValue (epsilon:Cubic)) : u = 1 := by
  let x : Cubic := u
  let A : ℝ := x.a
  let B : ℝ := x.b * root
  let C : ℝ := x.c * root^2
  let S := A+B+C
  let Q := A^2+B^2+C^2-A*B-A*C-B*C
  have hN : S*Q = (norm x : ℝ) := by
    dsimp only [S,Q,A,B,C,norm]
    push_cast
    linear_combination ((x.b:ℝ)^3+(x.c:ℝ)^3*(root^3+2)-3*x.a*x.b*x.c)*root_cube
  have hs : 1 ≤ S ∧ S < 4 := ⟨hl, hh.trans epsilon_bounds.2⟩
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    nlinarith only [sq_nonneg (A-B),sq_nonneg (A-C),sq_nonneg (B-C)]
  have norm1 : norm x = 1 := by
    rcases unit_norm u with h | h
    · exact h
    · change norm x = -1 at h
      rw [h] at hN
      norm_num at hN
      nlinarith [mul_nonneg (show 0 ≤ S by linarith [hs.1]) hQ]
  have hQ' : Q ≤ 1 := by
    rw [norm1,Int.cast_one] at hN
    nlinarith [mul_nonneg (show 0 ≤ S-1 by linarith [hs.1]) hQ]
  have coeff (D E F : ℝ) (hS : S = D+E+F) (hq : Q=D^2+E^2+F^2-D*E-D*F-E*F) :
      (3*D-S)^2 ≤ 2^2 := by
    rw [hS]
    rw [hq] at hQ'
    nlinarith only [hQ',sq_nonneg (E-F)]
  have aa := coeff A B C rfl rfl
  have bb := coeff B A C (by dsimp [S]; ring) (by dsimp [Q]; ring)
  have cc := coeff C A B (by dsimp [S]; ring) (by dsimp [Q]; ring)
  have ha := coord_choices x.a 1 S le_rfl hs (by simpa [A] using aa)
  have hb := coord_choices x.b root S root_bounds.1.le hs bb
  have hc := coord_choices x.c (root^2) S (by nlinarith [root_bounds.1, sq_nonneg (root-1)]) hs cc
  change realValue x < realValue (epsilon:Cubic) at hh
  have hval : realValue x = (x.a:ℝ)+x.b*root+x.c*root^2 := rfl
  rw [epsilon_value, hval] at hh
  dsimp only [norm] at norm1
  apply Units.ext
  change x = 1
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    first | exact ext ha hb hc | solve | norm_num [ha,hb,hc] at norm1 | simp [ha,hb,hc] at hh

private theorem realValue_zpow (u : Cubicˣ) (n : ℤ) :
    realValue ((u ^ n : Cubicˣ) : Cubic) = realValue (u:Cubic) ^ n := by
  change ((Units.map realValue.toMonoidHom (u^n) : ℝˣ) : ℝ) = _
  rw [map_zpow,Units.val_zpow_eq_zpow_val]
  rfl

private theorem positive_units (u : Cubicˣ) (hu : 0 < realValue (u:Cubic)) :
    ∃ n : ℤ, u = epsilon^n := by
  obtain ⟨n,hn,hn'⟩ := exists_mem_Ico_zpow hu epsilon_bounds.1
  let v : Cubicˣ := u / epsilon^n
  have epos : 0 < realValue (epsilon:Cubic) := lt_trans zero_lt_one epsilon_bounds.1
  have vp : realValue (v:Cubic) = realValue (u:Cubic) / realValue (epsilon:Cubic)^n := by
    change realValue ((u:Cubic) * ↑((epsilon^n)⁻¹ : Cubicˣ)) = _
    rw [map_mul, map_units_inv, realValue_zpow, div_eq_mul_inv]
  have hvl : 1 ≤ realValue (v:Cubic) := by
    rw [vp,le_div_iff₀ (zpow_pos epos _),one_mul]
    exact hn
  have hvh : realValue (v:Cubic) < realValue (epsilon:Cubic) := by
    rw [vp,div_lt_iff₀ (zpow_pos epos _)]
    rwa [zpow_add_one₀ epos.ne',mul_comm] at hn'
  have hv := unit_in_interval v hvl hvh
  exact ⟨n, div_eq_one.mp hv⟩

theorem all_units (u : Cubicˣ) : ∃ n : ℤ, u = epsilon⁻¹^n ∨ u = -(epsilon⁻¹^n) := by
  have hne : realValue (u:Cubic) ≠ 0 := (u.isUnit.map realValue).ne_zero
  rcases lt_or_gt_of_ne hne with h | h
  · have hn : 0 < realValue ((-u : Cubicˣ) : Cubic) := by simpa using h
    obtain ⟨n,hn⟩ := positive_units (-u) hn
    refine ⟨-n, Or.inr ?_⟩
    rw [inv_zpow,zpow_neg,inv_inv,← hn,neg_neg]
  · obtain ⟨n,hn⟩ := positive_units u h
    refine ⟨-n, Or.inl ?_⟩
    rw [inv_zpow,zpow_neg,inv_inv,hn]

end BealDescent.Cubic

namespace BealDescent.Cubic

def alpha : Cubic := ⟨0,1,0⟩

theorem alpha_cubed : alpha^3 = 2 := by decide

end BealDescent.Cubic

namespace BealDescent.Cubic

private theorem unit_mod_squares (v : Cubicˣ) : ∃ w : Cubicˣ,
    v=w^2 ∨ v= -(w^2) ∨ v=epsilon⁻¹*w^2 ∨ v= -(epsilon⁻¹*w^2) := by
  obtain ⟨m,hm⟩ := all_units v
  let w := epsilon⁻¹^(m/2)
  have he : (epsilon⁻¹)^m=(epsilon⁻¹)^(m%2)*w^2 := by
    dsimp [w]
    rw [←zpow_natCast (epsilon⁻¹^(m/2)) 2,←zpow_mul,←zpow_add]
    congr 1
    omega
  refine ⟨w,?_⟩
  have modtwo : m%2=0 ∨ m%2=1 := by omega
  rcases modtwo with e|e <;> rw [he,e] at hm
  · simp only [zpow_zero,one_mul] at hm
    exact hm.imp_right Or.inl
  · simp only [zpow_one] at hm
    exact Or.inr (Or.inr hm)

private theorem odd_unit_coeff (z : Cubic) :
    Even ((((epsilon⁻¹:Cubicˣ):Cubic)*z^2).a+(((epsilon⁻¹:Cubicˣ):Cubic)*z^2).b) := by
  refine ⟨2*z.a*z.c+z.b^2-z.a*z.b-z.c^2,?_⟩
  simp [epsilon,pow_two,mul_a,mul_b,mul_c]
  ring

private theorem integral_square {x y v : Cubic} (rel : IsRelPrime x y)
    (hp : x*y=v^2) (pos : 0<norm x) (ho : x.a%2=1) (he : x.b%2=0) :
    ∃ w : Cubic, w^2=x := by
  let _ := IsBezout.toGCDDomain Cubic
  obtain ⟨w,u,hw⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr rel) hp
  obtain ⟨t,h|h|h|h⟩ := unit_mod_squares u
  · exact ⟨w*(t:Cubic),by simpa only [mul_pow,Units.val_pow_eq_pow_val,h] using hw⟩
  · let z := w*(t:Cubic)
    have hz : -(z^2)=x := by simpa only [z,mul_pow,h,Units.val_neg,Units.val_pow_eq_pow_val,mul_neg] using hw
    have normneg (a : Cubic) : norm (-a) = -norm a := by simp [norm,neg_a,neg_b,neg_c]; ring
    rw [←hz,normneg,pow_two,norm_mul] at pos
    nlinarith [sq_nonneg (norm z)]
  · let z := w*(t:Cubic)
    have hz : ((epsilon⁻¹:Cubicˣ):Cubic)*z^2=x := by
      rw [←hw,h,Units.val_mul,Units.val_pow_eq_pow_val]
      dsimp [z]; ring
    obtain ⟨a,ha⟩ := odd_unit_coeff z
    rw [hz] at ha
    omega
  · let z := w*(t:Cubic)
    have hz : -(((epsilon⁻¹:Cubicˣ):Cubic)*z^2)=x := by
      rw [←hw,h,Units.val_neg,Units.val_mul,Units.val_pow_eq_pow_val]
      dsimp [z]; ring
    obtain ⟨a,ha⟩ := odd_unit_coeff z
    rw [←hz,neg_a] at ho
    rw [←hz,neg_b] at he
    omega

/-- The cubic factor of an odd square is an actual square at a dyadic
shift. The norm selects the sign and reduction modulo two selects the unit. -/
theorem dyadic_square_coordinates {d u q j : ℕ} (hd : d%2=1) (hu : u%2=1)
    (cop : d.Coprime u) (hq : 0<q) (hj : j=1 ∨ j=2)
    (equation : d^3+u^2=2^(3*q+j)) :
    ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
      2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
      2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0) := by
  have eqn : (d:ℤ)^3+(u:ℤ)^2=2^j*((2:ℤ)^q)^3 := by
    rw [←pow_mul,Nat.mul_comm q 3,←pow_add,Nat.add_comm]
    exact_mod_cast equation
  have cp3 : IsCoprime (3:ℤ) (u:ℤ) := by
    apply (show Prime (3:ℤ) by norm_num).irreducible.coprime_iff_not_dvd.mpr
    intro du
    have nine : (9:ℤ)∣(u:ℤ)^2 := pow_dvd_pow_of_dvd du 2
    have tab : ∀ x y : ZMod 9, x^3=2*y^3 ∨ x^3=4*y^3 → y^3=0 := by decide +kernel
    have he := congrArg (fun w : ℤ => (w:ZMod 9)) eqn
    have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr nine
    push_cast at he zero
    rw [zero,add_zero] at he
    have : Fact (1<9) := ⟨by decide⟩
    have htwo : IsUnit (2:ZMod 9) := ⟨⟨2,5,by decide,by decide⟩,rfl⟩
    exact ((htwo.pow q).pow 3).ne_zero (tab _ _ (by
      rcases hj with rfl|rfl
      · exact Or.inl (by simpa using he)
      · exact Or.inr (by simpa only [show (2:ZMod 9)^2=4 by decide] using he)))
  have cp : IsCoprime ((u:ℤ)^2) (3*(d:ℤ)^2) :=
    (cp3.symm.mul_right cop.isCoprime.symm.pow_right).pow_left
  have icp : IsCoprime ((u:Cubic)^2) (3*(d:Cubic)^2) := by simpa using cp.intCast (R:=Cubic)
  let s : Cubic := (2:Cubic)^q*alpha^j
  let x := s-(d:Cubic)
  let y := s^2+s*d+(d:Cubic)^2
  have e : (alpha^j)^3=(alpha^3)^j := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have ss : s^3=(2:Cubic)^j*((2:Cubic)^q)^3 := by dsimp [s]; rw [mul_pow,e,alpha_cubed,mul_comm]
  have heq := congrArg (fun w : ℤ => (w:Cubic)) eqn
  push_cast at heq
  have hp : x*y=(u:Cubic)^2 := by dsimp [x,y]; linear_combination ss-heq
  have diff : y-(s+2*d)*x=3*(d:Cubic)^2 := by dsimp [x,y]; ring
  have rel : IsRelPrime x y := by
    intro a ha hb
    apply icp.isRelPrime
    · rw [←hp]; exact ha.trans (dvd_mul_right _ _)
    · rw [←diff]; exact dvd_sub hb (dvd_mul_of_dvd_right ha _)
  have form : x=⟨-(d:ℤ),if j=1 then (2:ℤ)^q else 0,if j=2 then (2:ℤ)^q else 0⟩ := by
    have hs : (2:Cubic)^q=scalar ((2:ℤ)^q) := by rw [scalar_eq]; push_cast; rfl
    have nd : (d:Cubic)=scalar (d:ℤ) := by rw [scalar_eq,Int.cast_natCast]
    have aa : alpha^2=⟨0,0,1⟩ := by decide
    dsimp only [x,s]
    rw [hs,nd,sub_eq_add_neg]
    rcases hj with rfl|rfl
    · rw [pow_one]
      apply ext <;> simp [alpha,scalar,add_a,add_b,add_c,neg_a,neg_b,neg_c,mul_a,mul_b,mul_c]
    · rw [aa]
      apply ext <;> simp [scalar,add_a,add_b,add_c,neg_a,neg_b,neg_c,mul_a,mul_b,mul_c]
  have pos : 0<norm x := by
    have ugt : 0<(u:ℤ)^2 := sq_pos_of_pos (by exact_mod_cast (show 0<u by omega))
    rw [form,norm]
    rcases hj with rfl|rfl <;> norm_num at eqn ⊢ <;> linarith
  have xa : x.a%2=1 := by rw [form]; change (-(d:ℤ))%2=1; omega
  have xb : x.b%2=0 := by
    rw [form]
    change (if j=1 then (2:ℤ)^q else 0)%2=0
    have dv := dvd_pow_self (2:ℤ) (show q≠0 by omega)
    split <;> simp [Int.emod_eq_zero_of_dvd dv]
  obtain ⟨w,hw⟩ := integral_square rel hp pos xa xb
  rw [form,pow_two] at hw
  have a := congrArg Cubic.a hw
  have b := congrArg Cubic.b hw
  have c := congrArg Cubic.c hw
  simp only [mul_a,mul_b,mul_c] at a b c
  exact ⟨w.a,w.b,w.c,by linear_combination a,by linear_combination b,by linear_combination c⟩

end BealDescent.Cubic

theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1.H1 := by
  exact BealDescent.Cubic.dyadic_square_coordinates

/-- All positive solutions of the square-and-cube equation with dyadic output. -/
theorem BealMordell.positive_solutions {u d k : ℕ} (hu : 0<u) (hd : 0<d) :
    u^2+d^3=2^k ↔ ∃ t : ℕ,
      (u=2^(3*t) ∧ d=2^(2*t) ∧ k=6*t+1) ∨
      (u=13*2^(3*t) ∧ d=7*2^(2*t) ∧ k=6*t+9) :=
  OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1.BealMordell.classify_positive BealDescent.Cubic.dyadic_square_coordinates hu hd
