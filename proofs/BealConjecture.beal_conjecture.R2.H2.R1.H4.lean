import OMAReductions.R_BealConjecture_beal_conjecture_R2_H2_R1
import Mathlib

-- Credit: @ubuwaits
-- The cube-root-of-two descent for exponents 5 and 7 in @Hennyrick's reductions motivated the exponent-23 calculation.

/-!
# A cube and a 23rd power summing to a power of two

For coprime integers a and b, a³ + b²³ = 2ᵏ forces k to be divisible by 3 or
23, or congruent to 1 modulo 69. The last theorem states this result.

The proof factors a difference of cubes in ℤ[∛2], proves norm-Euclidean
division and determines the units. Three finite residue calculations use
the same global unit exponent at all three roots in each residue field.
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

private theorem index_split (m : ℤ) {n : ℕ} (hn : 0 < n) :
    ∃ i : Fin n, epsilon⁻¹ ^ m = epsilon⁻¹ ^ i.val * (epsilon⁻¹ ^ (m/n)) ^ n := by
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  have rpos := Int.emod_nonneg m hn'.ne'
  have rlt := Int.emod_lt_of_pos m hn'
  let i : Fin n := ⟨(m%n).toNat, by omega⟩
  have hi : (i.val : ℤ) = m%n := Int.toNat_of_nonneg rpos
  refine ⟨i,?_⟩
  rw [← zpow_natCast (epsilon⁻¹) i.val,← zpow_natCast (epsilon⁻¹ ^ (m/n)) n,
    ← zpow_mul, ← zpow_add, hi, mul_comm]
  rw [Int.emod_add_mul_ediv]

/-- A factor of a power coprime to its cofactor is a power times one of n fixed units. -/
theorem primitive_factor {x y b : Cubic} {n : ℕ} (hc : IsRelPrime x y) (h : x*y=b^n)
    (hn : Odd n) : ∃ i : Fin n, ∃ z : Cubic, (↑(epsilon⁻¹ ^ i.val) : Cubic) * z^n = x := by
  let _ := IsBezout.toGCDDomain Cubic
  obtain ⟨w,u,hu⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr hc) h
  obtain ⟨m,hm⟩ := all_units u
  obtain ⟨i,hi⟩ := index_split m (show 0 < n by obtain ⟨d,hd⟩ := hn; omega)
  let v : Cubicˣ := epsilon⁻¹ ^ (m/n)
  rcases hm with hm | hm
  · refine ⟨i,w*(v:Cubic),?_⟩
    rw [← hu,hm,hi,Units.val_mul,Units.val_pow_eq_pow_val,mul_pow]
    simp only [v,Units.val_pow_eq_pow_val]; ring
  · refine ⟨i,-(w*(v:Cubic)),?_⟩
    rw [← hu,hm,hi,Units.val_neg,Units.val_mul,Units.val_pow_eq_pow_val,hn.neg_pow,mul_pow]
    simp only [v,Units.val_pow_eq_pow_val]; ring

def alpha : Cubic := ⟨0,1,0⟩

theorem alpha_cubed : alpha^3 = 2 := by decide

end BealDescent.Cubic

namespace BealDescent.Cubic

/-- Specialize the cubic generator to any root of T³ − 2. -/
def specialize {R : Type*} [CommRing R] (r : R) (hr : r^3=2) : Cubic →+* R where
  toFun x := (x.a:R)+x.b*r+x.c*r^2
  map_zero' := by simp [zero_a,zero_b,zero_c]
  map_one' := by simp [one_a,one_b,one_c]
  map_add' := by intro x y; simp only [add_a,add_b,add_c,Int.cast_add]; ring
  map_mul' := by
    intro x y
    simp only [mul_a,mul_b,mul_c,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    linear_combination -((x.b:R)*y.c+x.c*y.b+x.c*y.c*r)*hr

theorem specialize_alpha {R : Type*} [CommRing R] {r : R} (hr : r^3=2) :
    specialize r hr alpha = r := by simp [specialize,alpha]

theorem specialize_delta {R : Type*} [CommRing R] {r : R} (hr : r^3=2) :
    specialize r hr (epsilon⁻¹:Cubicˣ) = r-1 := by simp [specialize,epsilon]; ring

private theorem three_coprime_signed {a b : ℤ} {q n j : ℕ} (hn : 2 ≤ n)
    (hj : j=1 ∨ j=2) (h : a^3+b^n=2^j*(2^q)^3) : IsCoprime 3 b := by
  apply (show Prime (3:ℤ) by norm_num).irreducible.coprime_iff_not_dvd.mpr
  intro hb
  have hd : (9:ℤ) ∣ b^n := (pow_dvd_pow_of_dvd hb 2).trans (pow_dvd_pow b hn)
  have h' := congrArg (fun t : ℤ => (t : ZMod 9)) h
  have hz : ((b^n:ℤ) : ZMod 9) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hd
  simp only [Int.cast_add, Int.cast_mul] at h'
  rw [hz,add_zero] at h'
  push_cast at h'
  have table : ∀ x y : ZMod 9, x^3=2*y^3 ∨ x^3=4*y^3 → y^3=0 := by decide +kernel
  have : Fact (1 < 9) := ⟨by decide⟩
  have hu : IsUnit (2 : ZMod 9) := ⟨⟨2,5,by decide,by decide⟩,rfl⟩
  apply ((hu.pow q).pow 3).ne_zero
  apply table (a:ZMod 9)
  rcases hj with rfl | rfl
  · exact Or.inl (by simpa using h')
  · exact Or.inr (by simpa only [show (2:ZMod 9)^2=4 by decide] using h')

/-- A primitive signed equation gives the same unit representative at every auxiliary prime. -/
theorem signed_descent {a b : ℤ} {q n j : ℕ} (hc : IsCoprime a b) (hn : 2 ≤ n)
    (ho : Odd n) (hj : j=1 ∨ j=2) (eqn : a^3+b^n=(2:ℤ)^(3*q+j)) :
    ∃ i : Fin n, ∃ z : Cubic,
      (↑(epsilon⁻¹ ^ i.val) : Cubic) * z^n = (2:Cubic)^q * alpha^j - (a:Cubic) := by
  have h : a^3+b^n=2^j*(2^q)^3 := by
    rw [eqn,pow_add,Nat.mul_comm 3 q,pow_mul,mul_comm]
  have cp : IsCoprime (b^n) (3*a^2) :=
    ((three_coprime_signed hn hj h).symm.mul_right (hc.symm.pow_right)).pow_left
  have icp : IsCoprime ((b:Cubic)^n) (3*(a:Cubic)^2) := by simpa using cp.intCast (R := Cubic)
  let s : Cubic := (2:Cubic)^q * alpha^j
  let x := s - (a:Cubic)
  let y := s^2+s*a+(a:Cubic)^2
  have e : (alpha^j)^3 = (alpha^3)^j := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have ss : s^3 = (2:Cubic)^j*((2:Cubic)^q)^3 := by dsimp [s]; rw [mul_pow,e,alpha_cubed,mul_comm]
  have h' := congrArg (fun t : ℤ => (t:Cubic)) h
  push_cast at h'
  have hp : x*y = (b:Cubic)^n := by dsimp [x,y]; linear_combination ss - h'
  have hp' : y-(s+2*a)*x=3*(a:Cubic)^2 := by dsimp [x,y]; ring
  have rel : IsRelPrime x y := by
    intro l hl hr
    apply icp.isRelPrime
    · rw [← hp]; exact hl.trans (dvd_mul_right _ _)
    · rw [← hp']; exact dvd_sub hr (dvd_mul_of_dvd_right hl _)
  exact primitive_factor rel hp ho

end BealDescent.Cubic

namespace BealDescent.TwentyThree

/-- Three roots of T³ − 2, with data for testing whether a residue is a 23rd power. -/
structure Test (l : ℕ) where
  r₀ : ZMod l
  r₁ : ZMod l
  r₂ : ZMod l
  e₁ : ZMod l
  e₂ : ZMod l
  half : ZMod l
  powers : List (ZMod l)
  mask : ℕ

/-- Only positive membership checks are needed for the sieve to be necessary. -/
structure Test.Valid {l : ℕ} (T : Test l) : Prop where
  h₀ : T.r₀^3=2
  h₁ : T.r₁^3=2
  h₂ : T.r₂^3=2
  inv₁ : (T.r₁-1)*T.e₁=1
  inv₂ : (T.r₂-1)*T.e₂=1
  double : 2*T.half=1
  inList (x : ZMod l) : x^23 ∈ T.powers
  bit (x : ZMod l) : T.mask.testBit (x^23).val = true

def Test.allows {l : ℕ} (T : Test l) (i t j : ℕ) : Bool :=
  let v₀ := (T.r₀-1)^i
  let d₁ := 2^t * (T.r₁^j-T.r₀^j)
  let d₂ := 2^t * (T.r₂^j-T.r₀^j)
  let v₁ := T.e₁^i
  let v₂ := T.e₂^i
  T.powers.any fun s =>
    T.mask.testBit (((v₀*s+d₁)*v₁).val) && T.mask.testBit (((v₀*s+d₂)*v₂).val)

def test277 : Test 277 where
  r₀ := 152
  r₁ := 181
  r₂ := 221
  e₁ := 257
  e₂ := 34
  half := 139
  powers := [0, 1, 35, 60, 95, 116, 117, 160, 161, 182, 217, 242, 276]
  mask := 0x1000000004000002000000004000030000000000300000800000001000000800000003

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem check277 : test277.Valid := by
  constructor <;> decide +kernel

def test691 : Test 691 where
  r₀ := 94
  r₁ := 288
  r₂ := 309
  e₁ := 313
  e₂ := 433
  half := 346
  powers := [0, 1, 89, 113, 132, 149, 159, 197, 228, 253, 254, 258, 286, 308, 320, 331, 360, 371, 383, 405, 433, 437, 438, 463, 494, 532, 542, 559, 578, 602, 690]
  mask := 0x40000000000000000000004000004000080004010000000004000000080000062000000200000800801000000080100100000400000046000001000000020000000008020001000020000020000000000000000000003

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem check691 : test691.Valid := by
  constructor <;> decide +kernel

def test1657 : Test 1657 where
  r₀ := 49
  r₁ := 116
  r₂ := 1492
  e₁ := 317
  e₂ := 549
  half := 829
  powers := [0, 1, 12, 63, 70, 71, 76, 104, 109, 129, 138, 144, 158, 160, 183, 239, 263, 282, 349, 381, 399, 409, 425, 446, 461, 498, 539, 546, 561, 652, 655, 745, 756, 783, 787, 805, 817, 840, 852, 870, 874, 901, 912, 1002, 1005, 1096, 1111, 1118, 1159, 1196, 1211, 1232, 1248, 1258, 1276, 1308, 1375, 1394, 1418, 1474, 1497, 1499, 1513, 1519, 1528, 1548, 1553, 1581, 1586, 1587, 1594, 1645, 1656]
  mask := 0x100200000000000040c200000021000010082000a00000400000000000004000004000080000000000000001000000010000401000100000800100000000080000000004080010000000000000000000000240000000000000000000001002000000440001001000002002000088000001002000000000000000000000090000000000000000000000200040800000000040000000020004000020002008000200000002000000000000000040000800000800000000000008000014001040200002100000010c08000000000001003

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem check1657 : test1657.Valid := by
  constructor <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem square_coefficient_table : ∀ i t : Fin 23,
    test277.allows i.val t.val 2 = true → test691.allows i.val t.val 2 = true → t.val = 7 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem linear_coefficient_table : ∀ i t : Fin 23,
    test277.allows i.val t.val 1 = true → test691.allows i.val t.val 1 = true →
    test1657.allows i.val t.val 1 = true → t.val = 0 ∨ t.val = 15 := by
  decide +kernel

end BealDescent.TwentyThree

namespace BealDescent.TwentyThree

open BealDescent.Cubic

private theorem rescale {R : Type*} [CommMonoid R] {x y : R} (h : x*y=1) (q : ℕ) :
    x^q * (y^(q/23))^23=x^(q%23) := by
  calc
    _ = (x^(q%23)*x^(23*(q/23))) * y^(23*(q/23)) := by
      rw [←pow_add,Nat.mod_add_div,←pow_mul,Nat.mul_comm (q/23)]
    _ = x^(q%23) := by rw [mul_assoc,←mul_pow,h,one_pow,mul_one]

/-- The same index and constant term must pass all three evaluations in each residue field. -/
theorem Test.necessary {l : ℕ} (T : Test l) (ok : T.Valid) {q j i : ℕ} {a : ℤ} {z : Cubic}
    (h : (↑(epsilon⁻¹ ^ i) : Cubic) * z^23 = (2:Cubic)^q * alpha^j - (a:Cubic)) :
    T.allows i (q%23) j = true := by
  let d := T.half^(q/23)
  let constant := -(a:ZMod l)*d^23
  let shift := (2:ZMod l)^(q%23)
  have scaled := rescale ok.double q
  change (2:ZMod l)^q * d^23 = shift at scaled
  have image (r : ZMod l) (hr : r^3=2) :
      ∃ w : ZMod l, (r-1)^i*w^23 = constant + shift*r^j := by
    let f := specialize r hr
    refine ⟨f z * d,?_⟩
    have hf := congrArg f h
    simp only [Units.val_pow_eq_pow_val, map_mul,map_pow,map_sub,map_ofNat,map_intCast,
      f,specialize_alpha,specialize_delta] at hf
    rw [mul_pow,←mul_assoc,hf]
    dsimp only [constant]
    linear_combination r^j * scaled
  obtain ⟨w₀,h₀⟩ := image T.r₀ ok.h₀
  obtain ⟨w₁,h₁⟩ := image T.r₁ ok.h₁
  obtain ⟨w₂,h₂⟩ := image T.r₂ ok.h₂
  have translate (r e w : ZMod l) (inv : (r-1)*e=1)
      (hr : (r-1)^i*w^23=constant+shift*r^j) :
      (((T.r₀-1)^i*w₀^23 + shift*(r^j-T.r₀^j))*e^i) = w^23 := by
    have hinv : (r-1)^i*e^i=1 := by rw [←mul_pow,inv,one_pow]
    calc
      _ = ((r-1)^i*w^23)*e^i := by rw [h₀,hr]; ring
      _ = w^23 := by linear_combination w^23*hinv
  apply List.any_eq_true.mpr
  refine ⟨w₀^23,ok.inList _,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · rw [translate _ _ _ ok.inv₁ h₁]; exact ok.bit _
  · rw [translate _ _ _ ok.inv₂ h₂]; exact ok.bit _

/-- For a primitive signed solution, either the power of two is a cube or a 23rd power,
or its exponent is congruent to one modulo 69. -/
theorem exponent_obstruction {a b : ℤ} {k : ℕ} (hc : IsCoprime a b)
    (h : a^3+b^23=(2:ℤ)^k) : 3 ∣ k ∨ 23 ∣ k ∨ k%69=1 := by
  let q := k/3
  let j := k%3
  by_cases h₃ : 3 ∣ k
  · exact Or.inl h₃
  have hj : j=1 ∨ j=2 := by dsimp [j]; omega
  have hk : k=3*q+j := by dsimp [q,j]; omega
  rw [hk] at h
  obtain ⟨i,z,hr⟩ := signed_descent hc (by decide) (by decide : Odd 23) hj h
  let t : Fin 23 := ⟨q%23,Nat.mod_lt _ (by decide)⟩
  have h₁ := test277.necessary check277 hr
  have h₂ := test691.necessary check691 hr
  rcases hj with hj | hj
  · have h₃' := test1657.necessary check1657 hr
    rw [hj] at h₁ h₂ h₃'
    have hh := linear_coefficient_table i t h₁ h₂ h₃'
    change q%23=0 ∨ q%23=15 at hh
    omega
  · rw [hj] at h₁ h₂
    have hh := square_coefficient_table i t h₁ h₂
    change q%23=7 at hh
    omega

end BealDescent.TwentyThree

theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H2_R1.H4 := by
  exact fun h e => BealDescent.TwentyThree.exponent_obstruction h e
