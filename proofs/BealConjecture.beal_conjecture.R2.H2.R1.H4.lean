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
theorem dyadic_square_coordinates_int {d : ℤ} {u q j : ℕ} (hd : d%2=1) (hu : u%2=1)
    (cop : IsCoprime d (u:ℤ)) (hq : 0<q) (hj : j=1 ∨ j=2)
    (equation : d^3+(u:ℤ)^2=2^(3*q+j)) :
    ∃ a b c : ℤ, a^2+4*b*c= -d ∧
      2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
      2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0) := by
  have eqn : d^3+(u:ℤ)^2=2^j*((2:ℤ)^q)^3 := by
    rw [←pow_mul,Nat.mul_comm q 3,←pow_add,Nat.add_comm]
    exact equation
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
  have cp : IsCoprime ((u:ℤ)^2) (3*d^2) :=
    (cp3.symm.mul_right cop.symm.pow_right).pow_left
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
  have form : x=⟨-d,if j=1 then (2:ℤ)^q else 0,if j=2 then (2:ℤ)^q else 0⟩ := by
    have hs : (2:Cubic)^q=scalar ((2:ℤ)^q) := by rw [scalar_eq]; push_cast; rfl
    have nd : (d:Cubic)=scalar d := by rw [scalar_eq]
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
  have xa : x.a%2=1 := by rw [form]; change (-d)%2=1; omega
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

theorem dyadic_square_coordinates {d u q j : ℕ} (hd : d%2=1) (hu : u%2=1)
    (cop : d.Coprime u) (hq : 0<q) (hj : j=1 ∨ j=2)
    (equation : d^3+u^2=2^(3*q+j)) :
    ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
      2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
      2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0) := by
  exact dyadic_square_coordinates_int (by omega) hu cop.isCoprime hq hj (by exact_mod_cast equation)

end BealDescent.Cubic

namespace BealMordell

/-- A positive cube equal to a difference of distinct powers of two has
its lower exponent divisible by three. -/
theorem cube_gap_valuation {a k h : ℕ} (ha : 0<a) (gap : a^3+2^k=2^h) : 3∣k := by
  have less : k<h := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
    have := Nat.pow_pos (n:=3) ha
    omega)
  let z := 2^(h-k)-1
  have big : 1 < 2^(h-k) := Nat.one_lt_two_pow (by omega)
  have pe : 2∣2^(h-k) := dvd_pow_self _ (by omega)
  have oz : ¬2∣z := by dsimp [z]; omega
  have nz : z≠0 := by dsimp [z]; omega
  have f : a^3=2^k*z := by
    have ep : 2^h=2^k*2^(h-k) := by rw [←pow_add]; congr 1; omega
    have ez : 2^(h-k)=z+1 := by dsimp [z]; omega
    rw [ep,ez,Nat.mul_add,Nat.mul_one] at gap
    omega
  have val := congrArg (fun n : ℕ => n.factorization 2) f
  rw [Nat.factorization_mul (by positivity) nz,Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,Nat.factorization_eq_zero_of_not_dvd oz,
    Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at val
  exact ⟨a.factorization 2,by omega⟩

/-- The symmetric functions of a square root in the pure cubic field
give integral coordinates A,B with B dividing A² and B²=A³+2ᵏ.
Positivity of A then forces three to divide k. -/
theorem square_coordinates_point {d : ℤ} {k : ℕ}
    {a b c P Q : ℤ} (ha : a^2+4*b*c= -d)
    (hb : 2*a*b+2*c^2=P) (hc : 2*a*c+b^2=Q) (pq : P*Q=0)
    (power : 2*P^3+4*Q^3=(2:ℤ)^k) :
    ∃ A B : ℤ, ∃ h : ℕ, 2*A=(3*a)^2+d ∧ 2*a*B=A^2 ∧ B^2=A^3+(2:ℤ)^k ∧ B.natAbs=2^h := by
  let T := 3*a
  let S := 3*(a^2-2*b*c)
  let N := a^3+2*b^3+4*c^3-6*a*b*c
  have ht : T^2=2*S-3*d := by dsimp [T,S]; linear_combination 3*ha
  have hs : S^2-2*T*N=3*d^2 := by
    have e : S^2-2*T*N=3*((a^2+4*b*c)^2-2*(2*a*b+2*c^2)*(2*a*c+b^2)) := by
      dsimp [S,T,N]; ring
    rw [e,ha,hb,hc]
    linear_combination -6*pq
  have hn : N^2+d^3=(2:ℤ)^k := by
    have e : N^2=(a^2+4*b*c)^3+2*(2*a*b+2*c^2)^3+4*(2*a*c+b^2)^3-
        6*(a^2+4*b*c)*(2*a*b+2*c^2)*(2*a*c+b^2) := by dsimp [N]; ring
    rw [e,ha,hb,hc]
    linear_combination power+6*d*pq
  let A := S-d
  let B := T*S-N
  have eA : 2*T*B=3*A^2 := by
    dsimp [A,B]
    linear_combination 2*S*ht+hs
  have eB : B^2=A^3+(2:ℤ)^k := by
    dsimp [A,B]
    linear_combination S^2*ht+S*hs+hn
  have dvdA : B∣A^2 := ⟨2*a,by dsimp [T] at eA; linarith only [eA]⟩
  have dvdA' : B∣A^3 := dvdA.trans (pow_dvd_pow A (by decide : 2≤3))
  have dvdB : B∣(2:ℤ)^k := by
    rw [show (2:ℤ)^k=B^2-A^3 by omega]
    exact dvd_sub (dvd_pow_self _ (by decide : 2≠0)) dvdA'
  have nd : B.natAbs∣(2:ℕ)^k := by
    simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 by decide] using (Int.natAbs_dvd_natAbs.mpr dvdB)
  obtain ⟨h,_,bh⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp nd
  refine ⟨A,B,h,?_,?_,eB,bh⟩
  · dsimp [A]; change 2*(S-d)=T^2+d; linarith
  · dsimp [T] at eA; linarith only [eA]

theorem square_coordinates_force_three {d k : ℕ} (hd : 0<d)
    {a b c P Q : ℤ} (ha : a^2+4*b*c= -(d:ℤ))
    (hb : 2*a*b+2*c^2=P) (hc : 2*a*c+b^2=Q) (pq : P*Q=0)
    (power : 2*P^3+4*Q^3=(2:ℤ)^k) : 3∣k := by
  obtain ⟨A,B,h,hab,_,eB,bh⟩ := square_coordinates_point ha hb hc pq power
  have apos : 0<A := by nlinarith [sq_nonneg (3*a)]
  have b2 : B^2=(2:ℤ)^(2*h) := by
    have n : (B.natAbs:ℤ)^2=B^2 := by rw [Int.natCast_natAbs,sq_abs]
    rw [←n,bh]
    push_cast
    rw [←pow_mul,Nat.mul_comm]
  have aeq : (A.toNat:ℤ)=A := Int.toNat_of_nonneg apos.le
  have agap : A.toNat^3+2^k=2^(2*h) := by
    exact_mod_cast (show (A.toNat:ℤ)^3+(2:ℤ)^k=(2:ℤ)^(2*h) by rw [aeq,←eB,b2])
  exact cube_gap_valuation (by omega) agap

end BealMordell

namespace BealMordell

theorem square_parts {A B u : ℕ} (ha : 0<A) (h : A*B=u^2) :
    ∃ a b : ℕ, A=A.gcd B*a^2 ∧ B=A.gcd B*b^2 := by
  let g := A.gcd B
  let x := A/g
  let y := B/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left B ha
  have cx : g*x=A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have cy : g*y=B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  have cp : x.Coprime y := Nat.coprime_div_gcd_div_gcd gp
  have du : g^2∣u^2 := ⟨x*y,by rw [←h,←cx,←cy]; ring⟩
  obtain ⟨v,hv⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp du
  have hxy : x*y=v^2 := by
    apply Nat.mul_left_cancel (Nat.pow_pos (n:=2) gp)
    rw [←cx,←cy,hv] at h
    linear_combination h
  obtain ⟨a,ea⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cp)) hxy
  obtain ⟨b,eb⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cp.symm)) ((Nat.mul_comm _ _).trans hxy)
  exact ⟨a,b,by rw [←ea]; exact cx.symm,by rw [←eb]; exact cy.symm⟩

private theorem base_seven {u d k : ℕ} (hu : u%2=1) (hk : 2<k)
    (eqn : u^2+d^3=2^k) : d%8=7 := by
  obtain ⟨v,hv⟩ := Nat.odd_iff.mpr hu
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  have h := congrArg (fun w : ℕ => (w:ZMod 8)) eqn
  rw [zero,hv] at h
  push_cast at h
  have tab : ∀ a b : ZMod 8, (2*a+1)^2+b^3=0 → b=7 := by decide +kernel
  have result := congrArg ZMod.val (tab _ _ h)
  simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using result

private theorem cubic_cofactor_square {d t u : ℕ} (ht : 3≤t) (hd : d%8=7)
    (hlt : d<2^t) (eqn : u^2+d^3=(2^t)^3) :
    ∃ z : ℕ, (2^t)^2+2^t*d+d^2=z^2 := by
  let W := 2^t
  let A := W-d
  let B := W^2+W*d+d^2
  let g := A.gcd B
  have WA : W=A+d := by dsimp [A,W]; omega
  have pos : 0<A := by dsimp [A,W]; omega
  have product : A*B=u^2 := by
    change u^2+d^3=W^3 at eqn
    dsimp [B]
    rw [WA] at eqn ⊢
    linear_combination -eqn
  have wd : W.Coprime d := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left t
  have cp : A.Coprime d := Nat.coprime_add_self_left.mp (WA ▸ wd)
  have ga : g∣A := Nat.gcd_dvd_left _ _
  have gb : g∣B := Nat.gcd_dvd_right _ _
  have identity : B=A*(W+2*d)+3*d^2 := by dsimp [B]; rw [WA]; ring
  have g3d : g∣3*d^2 := (Nat.dvd_add_iff_right (ga.trans (dvd_mul_right _ _))).mpr (identity ▸ gb)
  have g3 : g∣3 := ((Nat.Coprime.coprime_dvd_left ga cp).pow_right 2).dvd_of_dvd_mul_right g3d
  obtain ⟨a,b,eqA,eqB⟩ := square_parts pos product
  change A=g*a^2 at eqA
  change B=g*b^2 at eqB
  rcases (Nat.dvd_prime Nat.prime_three).mp g3 with one|three
  · exact ⟨b,by simpa [one] using eqB⟩
  have wz : (W:ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 ht)
  have dz : (d:ZMod 8)=7 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using hd
  have eq := congrArg (fun v : ℕ => (v:ZMod 8)) (WA.trans (by rw [eqA,three]))
  push_cast at eq
  rw [wz,dz] at eq
  exact ((by decide +kernel : ∀ a : ZMod 8, 0≠3*a^2+7) _ eq).elim

private theorem square_cofactor_small {d z t : ℕ} (hd : d%2=1)
    (hlt : d<2^t) (he : (2^t)^2+2^t*d+d^2=z^2) : t<5 := by
  by_contra! ht
  let L := 2^(t-2)
  let W := 2^t
  let S := d+2*L
  have lp : 0<L := Nat.two_pow_pos _
  have wL : W=4*L := by
    change 2^t=4*2^(t-2)
    calc
      2^t=2^(2+(t-2)) := by congr 1; omega
      _=4*2^(t-2) := by rw [pow_add]; rfl
  change W^2+W*d+d^2=z^2 at he
  change d<W at hlt
  have diff : z^2=S^2+12*L^2 := by dsimp [S]; rw [wL] at he; linear_combination -he
  have gt : S<z := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by nlinarith [Nat.pow_pos (n:=2) lp])
  have zlt : z<2*W := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    rw [←he]
    nlinarith [Nat.pow_lt_pow_left hlt (by decide : 2≠0),Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos t)]
  have oddS : S%2=1 := by dsimp [S]; omega
  have oddZ : z%2=1 := by
    have e := congrArg (fun n : ℕ => n%2) diff
    change z^2%2=(S^2+12*L^2)%2 at e
    have ev : (12*L^2)%2=0 := Nat.mod_eq_zero_of_dvd ((by decide : 2∣12).trans (dvd_mul_right _ _))
    rw [Nat.pow_mod z,Nat.add_mod (S^2),Nat.pow_mod S,oddS,ev] at e
    by_contra hn
    have e0 : z%2=0 := by omega
    simp [e0] at e
  let r := (z-S)/2
  let v := r+S
  have zr : z=2*r+S := by dsimp [r]; omega
  have prod : r*v=3*L^2 := by
    dsimp [v]; rw [zr] at diff; nlinarith only [diff]
  let e := 2*(t-2)
  have dv : 2^e∣r*v := by rw [prod]; dsimp [e,L]; rw [Nat.mul_comm 2 (t-2),pow_mul]; exact dvd_mul_left _ _
  have vt : v≤z := by dsimp [v]; omega
  have rt : r≤z := by omega
  have bound : 2^e≤z := by
    by_cases oddr : r%2=1
    · have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣r)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [v]; omega) (cp.dvd_of_dvd_mul_left dv)).trans vt
    · have oddv : v%2=1 := by dsimp [v]; omega
      have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣v)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [r]; omega) (cp.dvd_of_dvd_mul_right dv)).trans rt
  have grow : 2*W≤2^e := by
    change 2*2^t≤2^e
    rw [Nat.mul_comm,←pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  omega

/-- When the exponent of two is a positive multiple of three, the
difference of cubes has only the solution 13²+7³=2⁹ for k>2. -/
theorem triple_shift {u d k : ℕ} (hu : u%2=1)
    (hk : 2<k) (divides : 3∣k) (eqn : u^2+d^3=2^k) :
    u=13 ∧ d=7 ∧ k=9 := by
  obtain ⟨t,et⟩ := divides
  have e : u^2+d^3=(2^t)^3 := by rw [←pow_mul,Nat.mul_comm t 3,←et]; exact eqn
  have lt : d<2^t := (Nat.pow_lt_pow_iff_left (by decide : 3≠0)).mp (by have := Nat.pow_pos (n:=2) (show 0<u by omega); omega)
  have seven := base_seven hu hk eqn
  have th : 3≤t := by
    by_contra! h
    have bound := Nat.pow_le_pow_right (n:=2) (by decide) (show t≤2 by omega)
    norm_num at bound
    omega
  obtain ⟨z,hz⟩ := cubic_cofactor_square th seven lt e
  have small := square_cofactor_small (by omega) lt hz
  have eqt : t=3 := by
    by_contra neq
    have t4 : t=4 := by omega
    rw [t4] at lt
    norm_num at lt
    have choices : d=7 ∨ d=15 := by omega
    have ek : k=12 := by omega
    have e11 := congrArg (fun v : ℕ => (v:ZMod 11)) eqn
    have tab : ∀ x : ZMod 11, x^2+7^3≠2^12 ∧ x^2+15^3≠2^12 := by decide +kernel
    rw [ek] at e11
    rcases choices with rfl|rfl
    · exact (tab u).1 (by exact_mod_cast e11)
    · exact (tab u).2 (by exact_mod_cast e11)
  have eqk : k=9 := by omega
  rw [eqt] at lt
  have eqd : d=7 := by norm_num at lt; omega
  rw [eqk,eqd] at eqn
  norm_num at eqn
  exact ⟨by nlinarith,eqd,eqk⟩

end BealMordell

namespace BealMordell

private theorem coprime_bases {u d k : ℕ} (hu : u%2=1) (eqn : u^2+d^3=2^k) :
    d.Coprime u := by
  apply Nat.coprime_of_dvd
  intro l lp ld lu
  have dv : l∣2^k := eqn ▸ dvd_add (lu.trans (dvd_pow_self _ (by decide : 2≠0)))
    (ld.trans (dvd_pow_self _ (by decide : 3≠0)))
  have p2 := (Nat.prime_dvd_prime_iff_eq lp Nat.prime_two).mp (lp.dvd_of_dvd_pow dv)
  subst l
  omega

/-- The pure cubic square descent is the only number-field input to the
complete classification with odd bases. -/
theorem cubic_from_coordinates
    (roots : ∀ {d u q j : ℕ}, d%2=1 → u%2=1 → d.Coprime u → 0<q → (j=1 ∨ j=2) →
      d^3+u^2=2^(3*q+j) → ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
        2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
        2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0))
    {u d k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k) (eqn : u^2+d^3=2^k) :
    u=13 ∧ d=7 ∧ k=9 := by
  apply triple_shift hu hk _ eqn
  by_contra bad
  let q := k/3
  let j := k%3
  have sj : j=1 ∨ j=2 := by dsimp [j]; omega
  have kk : k=3*q+j := by dsimp [q,j]; omega
  have h : d^3+u^2=2^(3*q+j) := by rw [←kk,Nat.add_comm]; exact eqn
  obtain ⟨a,b,c,ha,hb,hc⟩ := roots hd hu (coprime_bases hu eqn) (by dsimp [q]; omega) sj h
  apply bad (square_coordinates_force_three (by omega : 0<d) ha hb hc _ _)
  · rcases sj with e|e <;> simp [e]
  · rw [kk]
    have p : ((2:ℤ)^q)^3=(2:ℤ)^(3*q) := by rw [←pow_mul,Nat.mul_comm]
    rcases sj with e|e <;> simp [e,p,pow_add] <;> ring

end BealMordell

namespace BealMordell

/-- The sole positive odd-base solution for k above two. -/
theorem classify_odd {u d k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k)
    (eqn : u^2+d^3=2^k) : u=13 ∧ d=7 ∧ k=9 :=
  cubic_from_coordinates BealDescent.Cubic.dyadic_square_coordinates hu hd hk eqn

private theorem equal_two_orders {p q k a b : ℕ} (ha : a%2=1) (hb : b%2=1)
    (eqn : 2^p*a+2^q*b=2^k) : p=q := by
  have exclude {p q a b : ℕ} (lt : p<q) (oa : a%2=1) (ob : b%2=1)
      (h : 2^p*a+2^q*b=2^k) : False := by
    have qsplit : 2^q=2^p*2^(q-p) := by rw [←pow_add]; congr 1; omega
    let z := a+2^(q-p)*b
    have f : 2^p*z=2^k := by dsimp [z]; rw [qsplit] at h; linear_combination h
    have g : 1<z := by
      dsimp [z]
      have pos := Nat.mul_pos (Nat.two_pow_pos (q-p)) (show 0<b by omega)
      omega
    have pk : p<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
      rw [←f]; simpa using Nat.mul_lt_mul_of_pos_left g (Nat.two_pow_pos p))
    have ksplit : 2^k=2^p*2^(k-p) := by rw [←pow_add]; congr 1; omega
    rw [ksplit] at f
    have ez := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos p) f
    have dv : 2∣z := ez ▸ dvd_pow_self 2 (by omega)
    have ev : 2∣2^(q-p)*b := (dvd_pow_self 2 (by omega : q-p≠0)).trans (dvd_mul_right _ _)
    dsimp [z] at dv
    omega
  rcases lt_trichotomy p q with lt|eq|lt
  · exact (exclude lt ha hb eqn).elim
  · exact eq
  · exact (exclude lt hb ha ((Nat.add_comm _ _).trans eqn)).elim

/-- Every positive solution is a weighted power-of-two multiple of
(1,1,1) or (13,7,9). -/
theorem classify_positive {u d k : ℕ} (hu : 0<u) (hd : 0<d) :
    u^2+d^3=2^k ↔ ∃ t : ℕ,
      (u=2^(3*t) ∧ d=2^(2*t) ∧ k=6*t+1) ∨
      (u=13*2^(3*t) ∧ d=7*2^(2*t) ∧ k=6*t+9) := by
  constructor
  · intro h
    obtain ⟨i,a,oa,eu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.ne' 2 (by decide)
    obtain ⟨j,b,ob,ed⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' 2 (by decide)
    have opa : a^2%2=1 := by rw [Nat.pow_mod,show a%2=1 by omega]
    have opb : b^3%2=1 := by rw [Nat.pow_mod,show b%2=1 by omega]
    have f : 2^(i*2)*a^2+2^(j*3)*b^3=2^k := by simpa only [eu,ed,mul_pow,←pow_mul] using h
    have same := equal_two_orders opa opb f
    let t := i/3
    have ei : i=3*t := by dsimp [t]; omega
    have ej : j=2*t := by dsimp [t]; omega
    have fact : 2^(6*t)*(a^2+b^3)=2^k := by
      rw [show i*2=6*t by omega,show j*3=6*t by omega,←Nat.mul_add] at f
      exact f
    have sum : 1<a^2+b^3 := by omega
    have kk : 6*t<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
      rw [←fact]; simpa using Nat.mul_lt_mul_of_pos_left sum (Nat.two_pow_pos (6*t)))
    let l := k-6*t
    have kl : k=6*t+l := by dsimp [l]; omega
    have red : a^2+b^3=2^l := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (6*t))
      rw [fact,←pow_add,←kl]
    refine ⟨t,?_⟩
    by_cases large : 2<l
    · obtain ⟨ea,eb,el⟩ := classify_odd (by omega) (by omega) large red
      right
      exact ⟨by rw [eu,ei,ea,Nat.mul_comm],by rw [ed,ej,eb,Nat.mul_comm],by omega⟩
    · have bound : 2^l≤4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : l≤2)
      have ea : a=1 := by
        by_contra n
        have := Nat.pow_le_pow_left (show 2≤a by omega) 2
        norm_num at this; omega
      have eb : b=1 := by
        by_contra n
        have := Nat.pow_le_pow_left (show 2≤b by omega) 3
        norm_num at this; omega
      have el : l=1 := by
        rw [ea,eb] at red
        have e : (2:ℕ)^1=2^l := by simpa using red
        exact ((Nat.pow_right_inj (by decide : 1<2)).mp e).symm
      left
      exact ⟨by rw [eu,ei,ea,Nat.mul_one],by rw [ed,ej,eb,Nat.mul_one],by omega⟩
  · rintro ⟨t,h|h⟩ <;> obtain ⟨rfl,rfl,rfl⟩ := h <;>
      simp only [mul_pow,←pow_mul,pow_add,show 3*t*2=6*t by omega,
        show 2*t*3=6*t by omega] <;> ring

/-- If one summand has an even exponent above two and the other has
exponent divisible by three, a power-of-two output forces two even bases. -/
theorem even_bases_of_dyadic_result {a b x y k : ℕ} (hx : 2<x) (hy : 0<y) (hk : 2<k)
    (dx : 2∣x) (dy : 3∣y) (h : a^x+b^y=2^k) : 2∣a ∧ 2∣b := by
  obtain ⟨r,er⟩ := dx
  obtain ⟨s,es⟩ := dy
  have hr : 1<r := by omega
  have hs : 0<s := by omega
  have e : (a^r)^2+(b^s)^3=2^k := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm r 2,Nat.mul_comm s 3,←er,←es]; exact h
  have parity (A n : ℕ) (hn : 0<n) : A^n%2=A%2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one A with he|he <;> rw [he] <;> simp [hn.ne']
  have even : (2^k)%2=0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have pe := congrArg (fun n : ℕ => n%2) h
  change (a^x+b^y)%2=(2^k)%2 at pe
  rw [Nat.add_mod,parity a x (by omega),parity b y hy,even] at pe
  by_contra! no
  have oa : a%2=1 := by omega
  have ob : b%2=1 := by omega
  have az : a^r%2=1 := (parity a r (by omega)).trans oa
  have bz : b^s%2=1 := (parity b s hs).trans ob
  have sol := (classify_odd az bz hk e).1
  have unit := (Nat.Prime.pow_eq_iff (by decide : Nat.Prime 13)).mp sol
  omega

/-- Beal's stated common-divisor conclusion for either order of an even
exponent and a multiple of three when the output base is a power of two. -/
theorem beal_even_cube_dyadic {a b c x y z : ℕ} (ha : a≠0) (hx : 2<x) (hy : 2<y) (hz : 2<z)
    (output : ∃ t : ℕ, 0<t ∧ c=2^t)
    (exponents : (2∣x ∧ 3∣y) ∨ (3∣x ∧ 2∣y)) (h : a^x+b^y=c^z) :
    1 < Finset.gcd {a,b,c} id := by
  obtain ⟨t,ht,ec⟩ := output
  have kt : 2<t*z := by nlinarith
  rw [ec,←pow_mul] at h
  have bases : 2∣a ∧ 2∣b := by
    rcases exponents with ⟨dx,dy⟩|⟨dx,dy⟩
    · exact even_bases_of_dyadic_result hx (by omega) kt dx dy h
    · exact (even_bases_of_dyadic_result hy (by omega) kt dy dx ((Nat.add_comm _ _).trans h)).symm
  have dc : 2∣c := ec ▸ dvd_pow_self _ ht.ne'
  have dv : 2 ∣ Finset.gcd {a,b,c} id := by
    apply Finset.dvd_gcd
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl
    · exact bases.1
    · exact bases.2
    · exact dc
  have pos : Finset.gcd {a,b,c} id ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨a,Finset.mem_insert_self _ _,ha⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero pos) dv

end BealMordell

namespace BealMordell

private theorem coprime_difference {d u k : ℕ} (hu : u%2=1) (eqn : d^3+2^k=u^2) :
    d.Coprime u := by
  apply Nat.coprime_of_dvd
  intro l lp ld lu
  have dl : l∣d^3 := ld.trans (dvd_pow_self _ (by decide : 3≠0))
  have ul : l∣u^2 := lu.trans (dvd_pow_self _ (by decide : 2≠0))
  rw [←eqn] at ul
  have dv : l∣2^k := (Nat.dvd_add_iff_right dl).mpr ul
  have p2 := (Nat.prime_dvd_prime_iff_eq lp Nat.prime_two).mp (lp.dvd_of_dvd_pow dv)
  subst l
  omega

private theorem reflected_coordinates {d u k : ℕ} (hu : u%2=1) (hd : d%2=1)
    (hk : 2<k) (nontriple : ¬3∣k) (eqn : d^3+2^k=u^2) :
    ∃ a A B : ℤ, ∃ h : ℕ, a%2=1 ∧ 2*A=(3*a)^2-(d:ℤ) ∧
      2*a*B=A^2 ∧ B^2=A^3+(2:ℤ)^k ∧ B.natAbs=2^h := by
  let q := k/3
  let j := k%3
  have sj : j=1 ∨ j=2 := by dsimp [j]; omega
  have kk : k=3*q+j := by dsimp [q,j]; omega
  have e : (d:ℤ)^3+(2:ℤ)^k=(u:ℤ)^2 := by exact_mod_cast eqn
  have en : (-(d:ℤ))^3+(u:ℤ)^2=(2:ℤ)^(3*q+j) := by rw [←kk]; linarith
  have cop : IsCoprime (-(d:ℤ)) (u:ℤ) := (coprime_difference hu eqn).isCoprime.neg_left
  obtain ⟨a,b,c,ha,hb,hc⟩ := BealDescent.Cubic.dyadic_square_coordinates_int
    (by omega : (-(d:ℤ))%2=1) hu cop (by dsimp [q]; omega) sj en
  let P : ℤ := if j=1 then 2^q else 0
  let Q : ℤ := if j=2 then 2^q else 0
  have pq : P*Q=0 := by rcases sj with ee|ee <;> simp [P,Q,ee]
  have pow : 2*P^3+4*Q^3=(2:ℤ)^k := by
    rw [kk]
    have p : ((2:ℤ)^q)^3=(2:ℤ)^(3*q) := by rw [←pow_mul,Nat.mul_comm]
    rcases sj with e|e <;> simp [P,Q,e,p,pow_add] <;> ring
  obtain ⟨A,B,h,hA,hm,he,hB⟩ := square_coordinates_point ha hb hc pq pow
  have ad : a^2+4*b*c=(d:ℤ) := by simpa using ha
  have ao : a%2=1 := by
    have z := congrArg (fun w : ℤ => (w:ZMod 2)) ad
    have dz : (d:ZMod 2)=1 := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast, show (1:ZMod 2).val=1 by decide] using hd
    push_cast at z
    rw [dz] at z
    have tab : ∀ x y w : ZMod 2, x^2+4*y*w=1 → x=1 := by decide
    have result : (a:ZMod 2)=((1:ℤ):ZMod 2) := tab _ _ _ z
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at result
    omega
  exact ⟨a,A,B,h,ao,by simpa only [sub_eq_add_neg] using hA,hm,he,hB⟩

/-- An odd cube plus a power of two with exponent prime to three is a
square only for 17³ + 2⁷ = 71², once the exponent is above two. -/
theorem odd_difference_nontriple {d u k : ℕ} (hu : u%2=1) (hd : d%2=1)
    (hk : 2<k) (nontriple : ¬3∣k) (eqn : d^3+2^k=u^2) :
    d=17 ∧ u=71 ∧ k=7 := by
  obtain ⟨a,A,B,h,ao,hA,hm,he,hB⟩ := reflected_coordinates hu hd hk nontriple eqn
  have bpos : 0<B.natAbs := hB ▸ Nat.two_pow_pos h
  have b2 : (B.natAbs:ℤ)^2=B^2 := by rw [Int.natCast_natAbs,sq_abs]
  have neg : A<0 := by
    by_contra! nonneg
    rcases eq_or_lt_of_le nonneg with az|apos
    · have bn : B≠0 := by omega
      rw [←az,zero_pow (by decide : 2≠0)] at hm
      exact (mul_ne_zero (mul_ne_zero (by decide) (by omega)) bn) hm
    · have ca : (A.toNat:ℤ)=A := Int.toNat_of_nonneg apos.le
      have gap : A.toNat^3+2^k=2^(2*h) := by
        have z : (A.toNat:ℤ)^3+(2:ℤ)^k=(2:ℤ)^(2*h) := by
          rw [ca,←he,←b2,hB]
          push_cast
          rw [←pow_mul,Nat.mul_comm]
        exact_mod_cast z
      exact nontriple (cube_gap_valuation (by omega) gap)
  have na : ((-A).toNat:ℤ)= -A := Int.toNat_of_nonneg (by omega)
  have pos : B.natAbs^2+(-A).toNat^3=2^k := by
    have z : (B.natAbs:ℤ)^2+((-A).toNat:ℤ)^3=(2:ℤ)^k := by rw [b2,na]; linarith
    exact_mod_cast z
  obtain ⟨t,fam|fam⟩ := (classify_positive bpos (by omega)).mp pos
  · obtain ⟨eB,eA,ek⟩ := fam
    have aa : A.natAbs=(-A).toNat := by omega
    have m := congrArg Int.natAbs hm
    simp only [Int.natAbs_mul,Int.natAbs_pow,show (2:ℤ).natAbs=2 by decide] at m
    rw [aa,eA,eB] at m
    have atwo : 2*a.natAbs=2^t := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (3*t))
      calc
        2*a.natAbs*2^(3*t)=(2^(2*t))^2 := m
        _=2^t*2^(3*t) := by rw [←pow_mul,←pow_add]; congr 1; omega
    have te : t=1 := by
      by_cases zero : t=0
      · rw [zero] at atwo; norm_num at atwo
      by_contra bad
      have four : 4∣2^t := pow_dvd_pow 2 (show 2≤t by omega)
      rw [←atwo] at four
      omega
    rw [te] at atwo eA ek
    norm_num at atwo eA ek
    have val : a=1 ∨ a= -1 := by omega
    have de : d=17 := by rcases val with ee|ee <;> rw [ee] at hA <;> norm_num at hA <;> omega
    rw [de,ek] at eqn
    norm_num at eqn
    exact ⟨de,by nlinarith,ek⟩
  · obtain ⟨eB,_,_⟩ := fam
    have dvd : 13∣2^h := by rw [←hB,eB]; exact dvd_mul_right _ _
    have := (show Nat.Prime 13 by decide).dvd_of_dvd_pow dvd
    omega

end BealMordell

namespace BealMordell

private theorem dyadic_cube_residue {u d k : ℕ} (hu : u%2=1) (hk : 2<k)
    (eqn : d^3+2^k=u^2) : d%8=1 := by
  obtain ⟨v,hv⟩ := Nat.odd_iff.mpr hu
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  have h := congrArg (fun w : ℕ => (w:ZMod 8)) eqn
  simp only [Nat.cast_add] at h
  rw [zero,hv] at h
  push_cast at h
  have tab : ∀ a b : ZMod 8, b^3+0=(2*a+1)^2 → b=1 := by decide +kernel
  have result := congrArg ZMod.val (tab _ _ h)
  simpa only [ZMod.val_natCast,show (1:ZMod 8).val=1 by decide] using result

private theorem sum_cube_factors {d t u : ℕ} (hd : d%2=1) (eqn : d^3+(2^t)^3=u^2) :
    ∃ g a b : ℕ, (g=1 ∨ g=3) ∧ d+2^t=g*a^2 ∧
      (d:ℤ)^2-(2:ℤ)^t*d+((2:ℤ)^t)^2=g*(b:ℤ)^2 := by
  let W := 2^t
  let A := d+W
  let B := (((d:ℤ)-(W:ℤ))^2+W*d).toNat
  let g := A.gcd B
  have BC : (B:ℤ)=(d:ℤ)^2-W*d+(W:ℤ)^2 := by
    dsimp only [B]
    rw [Int.toNat_of_nonneg (by positivity)]
    ring
  have pos : 0<A := by dsimp [A,W]; positivity
  have product : A*B=u^2 := by
    have z : (d:ℤ)^3+(W:ℤ)^3=(u:ℤ)^2 := by exact_mod_cast eqn
    have prod : (A:ℤ)*B=(u:ℤ)^2 := by dsimp [A]; rw [BC]; linear_combination z
    exact_mod_cast prod
  have wd : d.Coprime W := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.pow_right t
  have cp : A.Coprime W := Nat.coprime_add_self_left.mpr wd
  have ga : g∣A := Nat.gcd_dvd_left _ _
  have gb : g∣B := Nat.gcd_dvd_right _ _
  have identity : B+A*(3*W)=A^2+3*W^2 := by
    have z : (B:ℤ)+(A:ℤ)*(3*W)=(A:ℤ)^2+3*(W:ℤ)^2 := by dsimp [A]; rw [BC]; ring
    exact_mod_cast z
  have g3w : g∣3*W^2 := (Nat.dvd_add_iff_right (ga.trans (dvd_pow_self _ (by decide : 2≠0)))).mpr
    (identity ▸ dvd_add gb (ga.trans (dvd_mul_right _ _)))
  have g3 : g∣3 := ((Nat.Coprime.coprime_dvd_left ga cp).pow_right 2).dvd_of_dvd_mul_right g3w
  obtain ⟨a,b,eqA,eqB⟩ := square_parts pos product
  refine ⟨g,a,b,(Nat.dvd_prime Nat.prime_three).mp g3,eqA,?_⟩
  change B=g*b^2 at eqB
  have co : (B:ℤ)=(g:ℤ)*(b:ℤ)^2 := by exact_mod_cast eqB
  simpa [W] using BC.symm.trans co

/-- The odd factor of a product equal to three times a power of two is
either one or three. -/
private theorem odd_factor {p q e : ℕ} (oddp : p%2=1) (he : p*q=3*(2^e)^2) : p=1 ∨ p=3 := by
  have cp : p.Coprime ((2^e)^2) := ((Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.pow_right e).pow_right 2
  apply (Nat.dvd_prime Nat.prime_three).mp
  exact cp.dvd_of_dvd_mul_right (he ▸ dvd_mul_right p q)

private theorem no_shifted_square {d z e : ℕ} (hd : d%8=1) (ep : 0<e)
    (cofactor : (z:ℤ)^2=((d:ℤ)-2*(2:ℤ)^e)^2+12*((2:ℤ)^e)^2) : False := by
  let L := 2^e
  let V := (d:ℤ)-2*L
  have hl : 2≤L := Nat.le_of_dvd (Nat.two_pow_pos e) (dvd_pow_self _ ep.ne')
  have evL : 2∣L := dvd_pow_self _ ep.ne'
  have zsq : (z:ℤ)^2=V^2+12*(L:ℤ)^2 := by simpa [V,L] using cofactor
  have vodd : V%2=1 := by dsimp [V]; omega
  have zodd : z%2=1 := by
    have zmod := congrArg (fun w : ℤ => (w:ZMod 2)) zsq
    have vm : (V:ZMod 2)=1 := by
      change (V:ZMod 2)=((1:ℤ):ZMod 2)
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      omega
    push_cast at zmod
    rw [vm] at zmod
    have result := congrArg ZMod.val ((by decide : ∀ x y : ZMod 2, x^2=1^2+12*y^2 → x=1) _ _ zmod)
    simpa only [ZMod.val_natCast,show (1:ZMod 2).val=1 by decide] using result
  have abslt : |V|<(z:ℤ) := by
    by_contra! h
    have ll : (0:ℤ)<L := by exact_mod_cast (show 0<L by omega)
    nlinarith [sq_abs V,sq_nonneg ((z:ℤ)-|V|), mul_self_le_mul_self (show (0:ℤ)≤z by positivity) h]
  let p := ((((z:ℤ)+V)/2)).toNat
  let q := ((((z:ℤ)-V)/2)).toNat
  have bounds := abs_lt.mp abslt
  have e1 : 2*(p:ℤ)=(z:ℤ)+V := by dsimp [p]; omega
  have e2 : 2*(q:ℤ)=(z:ℤ)-V := by dsimp [q]; omega
  have diff : (d:ℤ)=2*L+(p:ℤ)-q := by dsimp [V] at e1 e2; omega
  have eq : p*q=3*L^2 := by
    have prod : (p:ℤ)*(q:ℤ)=3*(L:ℤ)^2 := by
      have four : 4*((p:ℤ)*q)=12*(L:ℤ)^2 := by
        linear_combination ((z:ℤ)-V)*e1+2*(p:ℤ)*e2+zsq
      linarith only [four]
    exact_mod_cast prod
  have poq : p%2=1 ∨ q%2=1 := by omega
  obtain ⟨j,evenL⟩ := evL
  have dz : (d:ZMod 8)=1 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,show (1:ZMod 8).val=1 by decide] using hd
  have modtest : ∀ x : ZMod 8,
      1≠2*(2*x)+3*(2*x)^2-1 ∧ 1≠2*(2*x)+3-(2*x)^2 ∧ 1≠2*(2*x)+(2*x)^2-3 := by decide
  have toMod := congrArg (fun v : ℤ => (v:ZMod 8)) diff
  push_cast at toMod
  rw [dz,evenL] at toMod
  push_cast at toMod
  rcases poq with op|oq
  · rcases odd_factor op eq with hp|hp
    · rw [hp] at eq diff
      simp only [one_mul] at eq
      have c : (q:ℤ)=3*(L:ℤ)^2 := by exact_mod_cast eq
      have two : (2:ℤ)≤L := by exact_mod_cast hl
      nlinarith [sq_nonneg ((L:ℤ)-2)]
    · rw [hp] at eq toMod
      have qeq : q=L^2 := Nat.eq_of_mul_eq_mul_left (by decide : 0<3) eq
      rw [qeq,evenL] at toMod
      push_cast at toMod
      exact (modtest j).2.1 toMod
  · rcases odd_factor oq ((Nat.mul_comm _ _).trans eq) with hq|hq
    · rw [hq] at eq toMod
      simp only [mul_one] at eq
      rw [eq,evenL] at toMod
      push_cast at toMod
      exact (modtest j).1 toMod
    · rw [hq,Nat.mul_comm p 3] at eq
      have peq : p=L^2 := Nat.eq_of_mul_eq_mul_left (by decide : 0<3) eq
      rw [hq,peq,evenL] at toMod
      push_cast at toMod
      exact (modtest j).2.2 toMod

/-- Above exponent three there are no odd solutions when three divides the dyadic exponent. -/
theorem odd_difference_triple {u d k : ℕ} (hu : u%2=1) (hk : 3<k) (triple : 3∣k)
    (eqn : d^3+2^k=u^2) : False := by
  obtain ⟨t,et⟩ := triple
  have e : d^3+(2^t)^3=u^2 := by rw [←pow_mul,Nat.mul_comm t 3,←et]; exact eqn
  have mod8 := dyadic_cube_residue hu (by omega) eqn
  obtain ⟨g,a,z,hg,factor,cofactor⟩ := sum_cube_factors (by omega) e
  have dz : (d:ZMod 8)=1 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,show (1:ZMod 8).val=1 by decide] using mod8
  have modf := congrArg (fun n : ℕ => (n:ZMod 8)) factor
  push_cast at modf
  rw [dz] at modf
  by_cases t2 : t=2
  · rw [t2] at modf
    rcases hg with e|e <;> rw [e] at modf
    · exact ((by decide : ∀ a : ZMod 8, 1+2^2≠1*a^2) _ modf)
    · exact ((by decide : ∀ a : ZMod 8, 1+2^2≠3*a^2) _ modf)
  have t3 : 3≤t := by omega
  have zero : (2:ZMod 8)^t=0 := by
    have := (ZMod.natCast_eq_zero_iff (2^t) 8).mpr (pow_dvd_pow 2 t3)
    exact_mod_cast this
  rw [zero] at modf
  have one : g=1 := by
    rcases hg with h|h
    · exact h
    · rw [h] at modf
      exact ((by decide : ∀ x : ZMod 8, 1+0≠3*x^2) _ modf).elim
  let e := t-2
  have wL : (2:ℤ)^t=4*(2:ℤ)^e := by
    change (2:ℤ)^t=4*2^(t-2)
    calc
      (2:ℤ)^t=2^(2+(t-2)) := by congr 1; omega
      _=4*2^(t-2) := by rw [pow_add]; rfl
  apply no_shifted_square (z:=z) (e:=e) mod8 (by dsimp [e]; omega)
  rw [one,wL] at cofactor
  push_cast at cofactor
  linear_combination -cofactor

end BealMordell

namespace BealThueEight

/-- Integral coordinates in the basis 1, α, α², where α³ = 3α + 6. -/
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
  ⟨x.a*y.a + 6*(x.b*y.c + x.c*y.b),
   x.a*y.b + x.b*y.a + 3*(x.b*y.c+x.c*y.b)+6*x.c*y.c,
   x.a*y.c + x.b*y.b + x.c*y.a + 3*x.c*y.c⟩⟩

theorem mul_a (x y : Cubic) : (x*y).a = x.a*y.a+6*(x.b*y.c+x.c*y.b) := rfl
theorem mul_b (x y : Cubic) : (x*y).b = x.a*y.b+x.b*y.a+3*(x.b*y.c+x.c*y.b)+6*x.c*y.c := rfl
theorem mul_c (x y : Cubic) : (x*y).c = x.a*y.c+x.b*y.b+x.c*y.a+3*x.c*y.c := rfl
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

def norm (x : Cubic) : ℤ :=
  x.a*((x.a+3*x.c)^2-x.b*(3*x.b+6*x.c))+
    6*(x.b*(x.b^2-x.c*(x.a+3*x.c))+x.c*(6*x.c^2-x.a*x.b))

def adj (x : Cubic) : Cubic :=
  ⟨(x.a+3*x.c)^2-x.b*(3*x.b+6*x.c),6*x.c^2-x.a*x.b,x.b^2-x.c*(x.a+3*x.c)⟩

theorem mul_adj (x : Cubic) : x*adj x=scalar (norm x) := by
  apply ext <;> simp only [adj,norm,scalar,mul_a,mul_b,mul_c] <;> ring

theorem norm_mul (x y : Cubic) : norm (x*y)=norm x*norm y := by
  simp only [norm,mul_a,mul_b,mul_c]
  ring

def normHom : Cubic →* ℤ where
  toFun := norm
  map_one' := by decide
  map_mul' := norm_mul

def epsilon : Cubicˣ := ⟨⟨79,73,31⟩,⟨19,-1,-3⟩,by decide,by decide⟩

private theorem exists_root : ∃ r : ℝ, (235:ℝ)/100≤r ∧ r≤236/100 ∧ r^3=3*r+6 := by
  let f : ℝ → ℝ := fun x => x^3-3*x-6
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨r,hr,h⟩ := intermediate_value_Icc (f:=f) (by norm_num : (235:ℝ)/100≤236/100)
    hf.continuousOn (show (0:ℝ) ∈ Set.Icc (f (235/100)) (f (236/100)) by norm_num [f,Set.mem_Icc])
  exact ⟨r,hr.1,hr.2,by dsimp [f] at h; linarith⟩

noncomputable def root : ℝ := exists_root.choose

theorem root_cube : root^3=3*root+6 := exists_root.choose_spec.2.2

theorem root_bounds : (235:ℝ)/100≤root ∧ root≤236/100 :=
  ⟨exists_root.choose_spec.1,exists_root.choose_spec.2.1⟩

private theorem root_four : root^4=3*root^2+6*root := by
  linear_combination root*root_cube

noncomputable def value : Cubic →+* ℝ where
  toFun x := x.a+x.b*root+x.c*root^2
  map_zero' := by simp [zero_a,zero_b,zero_c]
  map_one' := by simp [one_a,one_b,one_c]
  map_add' := by intro x y; simp only [add_a,add_b,add_c,Int.cast_add]; ring
  map_mul' := by
    intro x y
    simp only [mul_a,mul_b,mul_c,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    linear_combination -((x.b:ℝ)*y.c+x.c*y.b)*root_cube-(x.c:ℝ)*y.c*root_four

theorem value_epsilon : value (epsilon:Cubic)=79+73*root+31*root^2 := by
  norm_num [value,epsilon]

theorem epsilon_bounds : 1<value (epsilon:Cubic) ∧ value (epsilon:Cubic)<440 := by
  have h := root_bounds
  have hr : root^2≤(236/100:ℝ)^2 := pow_le_pow_left₀ (by linarith [h.1]) h.2 2
  rw [value_epsilon]
  constructor <;> nlinarith [sq_nonneg root]

end Cubic
end BealThueEight

namespace BealThueEight.Cubic

private theorem real_norm (x : BealThueEight.Cubic) :
    value x*(((x.a:ℝ)-x.b*root/2+x.c*(3-root^2/2))^2+
      (3*root^2/4-3)*((x.b:ℝ)-x.c*root)^2)=(norm x:ℝ) := by
  have h4 : root^4=3*root^2+6*root := by linear_combination root*root_cube

  have h6 : root^6=9*root^2+36*root+36 := by linear_combination (root^3+3*root+6)*root_cube
  change ((x.a:ℝ)+x.b*root+x.c*root^2)*_=_
  simp only [norm,Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_pow,Int.cast_ofNat]
  ring_nf
  simp only [h6,h4,root_cube]
  ring

set_option maxRecDepth 120000 in
set_option maxHeartbeats 15000000 in
private theorem box_table : ∀ i : Fin 49, ∀ j : Fin 27, ∀ k : Fin 6,
    norm ⟨(i.val:ℤ)-24,(j.val:ℤ)-13,(k.val:ℤ)-2⟩=1 → i.val=25 ∧ j.val=13 ∧ k.val=2 := by
  decide +kernel

private theorem box_unit (x : BealThueEight.Cubic) (h : norm x=1) (a1 : -24≤x.a) (a2 : x.a≤24)
    (b1 : -13≤x.b) (b2 : x.b≤13) (c1 : -2≤x.c) (c2 : x.c≤3) : x=1 := by
  let i : Fin 49 := ⟨(x.a+24).toNat,by omega⟩
  let j : Fin 27 := ⟨(x.b+13).toNat,by omega⟩
  let k : Fin 6 := ⟨(x.c+2).toNat,by omega⟩
  have ai : (i.val:ℤ)-24=x.a := by dsimp [i]; omega
  have bj : (j.val:ℤ)-13=x.b := by dsimp [j]; omega
  have ck : (k.val:ℤ)-2=x.c := by dsimp [k]; omega
  obtain ⟨aa,bb,cc⟩ := box_table i j k (by rw [ai,bj,ck]; exact h)
  rw [aa] at ai; rw [bb] at bj; rw [cc] at ck
  apply ext <;> simp only [one_a,one_b,one_c] <;> norm_num at ai bj ck <;> omega

private theorem abs_product {x y p q : ℝ} (hx : |x|≤p) (hy : |y|≤q) : |x*y|≤p*q := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

private theorem fundamental_interval (u : BealThueEight.Cubicˣ)
    (lo : 1≤20*value (u:BealThueEight.Cubic)) (hi : 20*value (u:BealThueEight.Cubic)<value (epsilon:BealThueEight.Cubic)) :
    u=1 := by
  let x : BealThueEight.Cubic := u
  let S := value x
  let U := (x.a:ℝ)-x.b*root/2+x.c*(3-root^2/2)
  let F := (x.b:ℝ)-x.c*root
  let H := 3*root^2/4-3
  let M := 3*root^2-3
  let Q := U^2+H*F^2
  have s1 : 1≤20*S := lo
  have s2 : S<22 := by change 20*S<_ at hi; linarith [epsilon_bounds.2]
  have rb := root_bounds
  have r2lo : (235/100:ℝ)^2≤root^2 := pow_le_pow_left₀ (by norm_num) rb.1 2
  have r2hi : root^2≤(236/100:ℝ)^2 := pow_le_pow_left₀ (by linarith [rb.1]) rb.2 2
  have hH : 1≤H := by dsimp [H]; linarith only [r2lo]
  have hM : 13≤M := by dsimp [M]; linarith only [r2lo]
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hN : S*Q=(norm x:ℝ) := real_norm x
  have norm1 : norm x=1 := by
    rcases Int.isUnit_iff.mp (u.isUnit.map normHom) with h|h
    · exact h
    · change norm x= -1 at h
      rw [h] at hN
      norm_num at hN
      nlinarith [mul_nonneg (show 0≤S by linarith) hQ]
  rw [norm1,Int.cast_one] at hN
  have small : Q≤20 := by nlinarith [mul_nonneg (show 0≤20*S-1 by linarith) hQ]
  have fs : F^2≤Q := by dsimp [Q]; nlinarith [sq_nonneg U,mul_nonneg (show 0≤H-1 by linarith) (sq_nonneg F)]
  have us : U^2≤Q := by dsimp [Q]; nlinarith [mul_nonneg (show 0≤H by linarith) (sq_nonneg F)]
  have bf : |F|≤5 := abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith : F^2≤(5:ℝ)^2) (by norm_num))
  have bu : |U|≤5 := abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith : U^2≤(5:ℝ)^2) (by norm_num))
  have boundedF := abs_le.mp bf
  have boundedU := abs_le.mp bu
  have wr : |3*root/2|≤18/5 := by rw [abs_le]; constructor <;> linarith [rb.1,rb.2]
  have op := abs_le.mp (abs_product wr bf)
  have identity : S=(x.c:ℝ)*M+(3*root/2)*F+U := by
    change (x.a:ℝ)+x.b*root+x.c*root^2=_
    dsimp [M,F,U]; ring
  have cM : -23≤(x.c:ℝ)*M ∧ (x.c:ℝ)*M≤45 := by constructor <;> linarith [op.1,op.2,boundedU.1,boundedU.2]
  have cl : -2≤x.c := by
    by_contra! e
    have e' : (x.c:ℝ)≤ -3 := by exact_mod_cast (show x.c≤ -3 by omega)
    linarith [mul_le_mul_of_nonpos_left hM (show (x.c:ℝ)≤0 by linarith),cM.1]
  have ch : x.c≤3 := by
    by_contra! e
    have e' : (4:ℝ)≤x.c := by exact_mod_cast (show 4≤x.c by omega)
    linarith [mul_le_mul_of_nonneg_left hM (show (0:ℝ)≤x.c by linarith),cM.2]
  have ac : |(x.c:ℝ)|≤3 := abs_le.mpr ⟨by exact_mod_cast (show -3≤x.c by omega),by exact_mod_cast ch⟩
  have rr : |root|≤12/5 := by rw [abs_le]; constructor <;> linarith [rb.1,rb.2]
  have cr := abs_le.mp (abs_product ac rr)
  have bnd : |(x.b:ℝ)|≤13 := by rw [abs_le]; dsimp [F] at boundedF; constructor <;> linarith [boundedF.1,boundedF.2,cr.1,cr.2]
  have br := abs_le.mp (abs_product bnd rr)
  have vbound : |3-root^2/2|≤1 := by rw [abs_le]; constructor <;> linarith only [r2lo,r2hi]
  have cv := abs_le.mp (abs_product ac vbound)
  have abnd : |(x.a:ℝ)|≤24 := by
    rw [abs_le]; dsimp [U] at boundedU
    constructor <;> linarith [boundedU.1,boundedU.2,br.1,br.2,cv.1,cv.2]
  apply Units.ext
  exact box_unit x norm1 (by exact_mod_cast (abs_le.mp abnd).1) (by exact_mod_cast (abs_le.mp abnd).2)
    (by exact_mod_cast (abs_le.mp bnd).1) (by exact_mod_cast (abs_le.mp bnd).2) cl ch

private theorem value_zpow (u : BealThueEight.Cubicˣ) (n : ℤ) :
    value ((u^n:BealThueEight.Cubicˣ):BealThueEight.Cubic)=value (u:BealThueEight.Cubic)^n := by
  change ((Units.map value.toMonoidHom (u^n):ℝˣ):ℝ)=_
  rw [map_zpow,Units.val_zpow_eq_zpow_val]; rfl

/-- Positive units of the cubic order are generated by 79+73θ+31θ². -/
theorem positive_units (u : BealThueEight.Cubicˣ) (hu : 0<value (u:BealThueEight.Cubic)) :
    ∃ n : ℤ, u=epsilon^n := by
  obtain ⟨n,hn,hn'⟩ := exists_mem_Ico_zpow (show 0<20*value (u:BealThueEight.Cubic) by positivity) epsilon_bounds.1
  let v : BealThueEight.Cubicˣ := u/epsilon^n
  have ep : 0<value (epsilon:BealThueEight.Cubic) := lt_trans zero_lt_one epsilon_bounds.1
  have vv : value (v:BealThueEight.Cubic)=value (u:BealThueEight.Cubic)/value (epsilon:BealThueEight.Cubic)^n := by
    change value ((u:BealThueEight.Cubic)*↑((epsilon^n)⁻¹:BealThueEight.Cubicˣ))=_
    rw [map_mul,map_units_inv,value_zpow,div_eq_mul_inv]
  have l : 1≤20*value (v:BealThueEight.Cubic) := by
    rw [vv,←mul_div_assoc,le_div_iff₀ (zpow_pos ep _),one_mul]; exact hn
  have h : 20*value (v:BealThueEight.Cubic)<value (epsilon:BealThueEight.Cubic) := by
    rw [vv,←mul_div_assoc,div_lt_iff₀ (zpow_pos ep _)]
    rw [zpow_add_one₀ ep.ne'] at hn'
    simpa only [mul_comm (value (epsilon:BealThueEight.Cubic)^n)] using hn'
  exact ⟨n,div_eq_one.mp (fundamental_interval v l h)⟩

end BealThueEight.Cubic

namespace BealThueEight.Cubic

private theorem odd_iterate {v : BealThueEight.Cubic}
    (va : (v.a:ZMod 2)=1) (vb : (v.b:ZMod 2)=1) (vc : (v.c:ZMod 2)=1) (j : ℕ) :
    ((v^(2*j+1)).a:ZMod 2)=1 ∧ ((v^(2*j+1)).b:ZMod 2)=1 ∧ ((v^(2*j+1)).c:ZMod 2)=1 := by
  have s : ((v^2).a:ZMod 2)=1 ∧ ((v^2).b:ZMod 2)=0 ∧ ((v^2).c:ZMod 2)=0 := by
    simp only [pow_two,mul_a,mul_b,mul_c,Int.cast_add,Int.cast_mul,Int.cast_ofNat,va,vb,vc]
    decide
  induction j with
  | zero => simpa using And.intro va (And.intro vb vc)
  | succ j ih =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add]
    simp only [mul_a,mul_b,mul_c,Int.cast_add,Int.cast_mul,Int.cast_ofNat,ih.1,ih.2.1,ih.2.2,s.1,s.2.1,s.2.2]
    decide

/-- After s successive squarings of a triple of odd coordinates, the last two
coordinates are exactly divisible by 2 to the power s. -/
private theorem repeated_square {v : BealThueEight.Cubic} {a b c : ℤ}
    (va : v.a=2*a+1) (vb : v.b=2*b+1) (vc : v.c=2*c+1) (s : ℕ) :
    ∃ A B C : ℤ, (v^(2^s)).a=2*A+1 ∧ (v^(2^s)).b=2^s*(2*B+1) ∧ (v^(2^s)).c=2^s*(2*C+1) := by
  induction s with
  | zero => exact ⟨a,b,c,by simpa using va,by simpa using vb,by simpa using vc⟩
  | succ s ih =>
    obtain ⟨A,B,C,hA,hB,hC⟩ := ih
    let D : ℤ := 2^s
    let X := 2*B+1
    let Y := 2*C+1
    refine ⟨2*A^2+2*A+6*D^2*X*Y,A*X+B+3*D*Y*(B+C+1),
      A*Y+C+D*(B^2+B+3*C^2+3*C+1),?_⟩
    rw [show (2:ℕ)^(s+1)=2^s*2 by rw [pow_succ],pow_mul]
    simp only [pow_two,mul_a,mul_b,mul_c,hA,hB,hC,pow_succ (2:ℤ) s]
    dsimp [D,X,Y]
    constructor
    · ring
    · constructor <;> ring

private theorem int_odd_of_cast {a : ℤ} (h : (a:ZMod 2)=1) : Odd a := by
  change (a:ZMod 2)=((1:ℤ):ZMod 2) at h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  exact Int.odd_iff.mpr (by omega)

theorem power_last_nonzero {v : BealThueEight.Cubic}
    (va : (v.a:ZMod 2)=1) (vb : (v.b:ZMod 2)=1) (vc : (v.c:ZMod 2)=1)
    {n : ℕ} (hn : 0<n) : (v^n).c≠0 := by
  obtain ⟨s,m,om,em⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by decide)
  obtain ⟨j,ej⟩ := Nat.odd_iff.mpr (show m%2=1 by omega)
  obtain ⟨oa,ob,oc⟩ := odd_iterate va vb vc j
  rw [←ej] at oa ob oc
  obtain ⟨a,ha⟩ := int_odd_of_cast oa
  obtain ⟨b,hb⟩ := int_odd_of_cast ob
  obtain ⟨c,hc⟩ := int_odd_of_cast oc
  obtain ⟨A,B,C,_,_,eq⟩ := repeated_square ha hb hc s
  rw [em,Nat.mul_comm,pow_mul,eq]
  exact mul_ne_zero (by positivity) (by omega)

theorem zero_coefficient_power {n : ℤ} (h : ((epsilon^n:BealThueEight.Cubicˣ):BealThueEight.Cubic).c=0) : n=0 := by
  cases n with
  | ofNat n =>
    by_cases hz : n=0
    · subst n; rfl
    exfalso
    have pos : 0<n := Nat.pos_of_ne_zero hz
    have nz := power_last_nonzero (v:=(epsilon:BealThueEight.Cubic)) (by decide) (by decide) (by decide) pos
    exact nz (by simpa only [Int.ofNat_eq_natCast,zpow_natCast,Units.val_pow_eq_pow_val] using h)
  | negSucc n =>
    have nz := power_last_nonzero (v:=((epsilon⁻¹:BealThueEight.Cubicˣ):BealThueEight.Cubic)) (by decide) (by decide) (by decide)
      (Nat.zero_lt_succ n)
    have ep : epsilon^(Int.negSucc n)=(epsilon⁻¹)^(n+1) := by rw [zpow_negSucc,inv_pow]
    rw [ep,Units.val_pow_eq_pow_val] at h
    exact (nz h).elim

end BealThueEight.Cubic

namespace BealThueEight
namespace Cubic

private theorem positive_linear_unit (u : Cubicˣ) (hv : 0<value (u:Cubic)) (hc : (u:Cubic).c=0) : u=1 := by
  obtain ⟨n,rfl⟩ := positive_units u hv
  rw [zero_coefficient_power hc,zpow_zero]

theorem linear_unit (u : Cubicˣ) (hc : (u:Cubic).c=0) : u=1 ∨ u= -1 := by
  have nz := (u.isUnit.map value).ne_zero
  rcases lt_or_gt_of_ne nz with n|p
  · have v := positive_linear_unit (-u) (by simpa using n) (by simp [Units.val_neg,neg_c,hc])
    exact Or.inr (by rwa [neg_eq_iff_eq_neg] at v)
  · exact Or.inl (positive_linear_unit u p hc)

end Cubic

/-- All integral solutions of the cubic Thue equation of discriminant −864
that occurs in the odd part of the Mordell curve y²=x³+8. -/
theorem fixed_cubic {x c : ℤ} (eqn : x^3-3*x*c^2-6*c^3= -1) : x= -1 ∧ c=0 := by
  let w : Cubic := ⟨-x,c,0⟩
  have hn : w.norm=1 := by dsimp [w,Cubic.norm]; linear_combination -eqn
  let u : Cubicˣ := ⟨w,w.adj,by rw [Cubic.mul_adj,hn]; rfl,by rw [mul_comm,Cubic.mul_adj,hn]; rfl⟩
  have h : (u:Cubic).c=0 := rfl
  have cb : c=0 := by
    rcases Cubic.linear_unit u h with e|e
    · have b := congrArg (fun v : Cubicˣ => (v:Cubic).b) e
      exact b
    · have b := congrArg (fun v : Cubicˣ => (v:Cubic).b) e
      exact b
  rw [cb] at eqn
  norm_num at eqn
  exact ⟨by nlinarith [sq_nonneg (x-1),sq_nonneg (x+1)],cb⟩

end BealThueEight

namespace BealRealQuadratic

open Zsqrtd

private theorem rounded_square (a : ℤ) (m : ℕ) (hm : 0 < m) :
    4*(a-(m:ℤ)*a.bdiv m)^2 ≤ (m:ℤ)^2 := by
  rw [←Int.bmod_eq_self_sub_mul_bdiv]
  have lo := Int.le_bmod (x:=a) hm
  have hi := Int.bmod_le (x:=a) hm
  have h₁ : 0 ≤ (m:ℤ) - 2*a.bmod m := by omega
  have h₂ : 0 ≤ (m:ℤ) + 2*a.bmod m := by omega
  nlinarith only [mul_nonneg h₁ h₂]

private theorem norm_zero (y : Zsqrtd 2) : y.norm=0 ↔ y=0 := by
  apply Zsqrtd.norm_eq_zero
  intro n eq
  have l : -1≤n := by
    by_contra! h
    have s := mul_self_le_mul_self (by decide : (0:ℤ)≤2) (show (2:ℤ)≤ -n by omega)
    nlinarith
  have h : n≤1 := by
    by_contra! e
    have s := mul_self_le_mul_self (by decide : (0:ℤ)≤2) (show (2:ℤ)≤n by omega)
    nlinarith
  interval_cases n <;> norm_num at eq

private theorem division (x y : Zsqrtd 2) (hy : y≠0) :
    ∃ q : Zsqrtd 2, (x-y*q).norm.natAbs<y.norm.natAbs := by
  let m := y.norm.natAbs
  have hp : 0< m := Nat.pos_of_ne_zero (fun h => hy ((norm_zero y).mp (Int.natAbs_eq_zero.mp h)))
  let e := x*star y
  let r : Zsqrtd 2 := ⟨e.re.bdiv m,e.im.bdiv m⟩
  have qexists : ∃ q : Zsqrtd 2, (y.norm:Zsqrtd 2)*q=(m:Zsqrtd 2)*r := by
    by_cases nn : 0≤y.norm
    · refine ⟨r,?_⟩
      have em : (m:ℤ)=y.norm := Int.natAbs_of_nonneg nn
      rw [←em,Int.cast_natCast]
    · refine ⟨-r,?_⟩
      have neg : y.norm= -(m:ℤ) := by dsimp [m]; omega
      rw [neg,Int.cast_neg,Int.cast_natCast,neg_mul_neg]
  obtain ⟨q,hq⟩ := qexists
  refine ⟨q,?_⟩
  have hf : (x-y*q)*star y=e-(m:Zsqrtd 2)*r := by
    dsimp only [e]; rw [←hq,norm_eq_mul_conj]; ring
  have hn := congrArg Zsqrtd.norm hf
  rw [norm_mul,norm_conj] at hn
  have rb := rounded_square e.re m hp
  have ib := rounded_square e.im m hp
  have herm : (e-(m:Zsqrtd 2)*r).norm=(e.re-(m:ℤ)*e.re.bdiv m)^2-2*(e.im-(m:ℤ)*e.im.bdiv m)^2 := by
    simp [norm_def,r]; ring
  rw [herm] at hn
  have bound : |(x-y*q).norm*y.norm|<(m:ℤ)^2 := by
    rw [hn,abs_lt]
    have pos : (0:ℤ)< m := by exact_mod_cast hp
    constructor <;> nlinarith only [rb,ib,sq_pos_of_pos pos,
      sq_nonneg (e.re-(m:ℤ)*e.re.bdiv m),sq_nonneg (e.im-(m:ℤ)*e.im.bdiv m)]
  rw [abs_mul,←Int.natCast_natAbs,←Int.natCast_natAbs] at bound
  have b : (x-y*q).norm.natAbs*m< m*m := by exact_mod_cast (by simpa only [pow_two] using bound :
    ((x-y*q).norm.natAbs:ℤ)*(m:ℤ)<(m:ℤ)*(m:ℤ))
  exact (Nat.mul_lt_mul_right hp).mp b

private noncomputable instance euclid : EuclideanDomain (Zsqrtd 2) := by
  let q (x y : Zsqrtd 2) := if h : y=0 then 0 else (division x y h).choose
  exact {
    quotient := q
    quotient_zero := fun _ => dif_pos rfl
    remainder := fun x y => x-y*q x y
    quotient_mul_add_remainder_eq := fun _ _ => by ring
    r := fun x y => x.norm.natAbs<y.norm.natAbs
    r_wellFounded := (measure fun x : Zsqrtd 2 => x.norm.natAbs).wf
    remainder_lt := by intro x y hy; simpa only [q,dif_neg hy] using (division x y hy).choose_spec
    mul_left_not_lt := by
      intro x y hy
      rw [Zsqrtd.norm_mul,Int.natAbs_mul]
      have hz : 0<y.norm.natAbs := Nat.pos_of_ne_zero (fun h => hy ((norm_zero y).mp (Int.natAbs_eq_zero.mp h)))
      exact not_lt_of_ge (by simpa using Nat.mul_le_mul_left x.norm.natAbs hz) }

def epsilon : (Zsqrtd 2)ˣ := ⟨⟨1,1⟩,⟨-1,1⟩,by decide,by decide⟩

noncomputable def realValue : Zsqrtd 2 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2,by simpa only [←pow_two,Int.cast_ofNat] using Real.sq_sqrt (by norm_num : (0:ℝ)≤2)⟩

private theorem realValue_def (x : Zsqrtd 2) : realValue x=(x.re:ℝ)+x.im*Real.sqrt 2 := by
  simp [realValue,Zsqrtd.lift]

private theorem ev : realValue (epsilon:Zsqrtd 2)=1+Real.sqrt 2 := by rw [realValue_def]; norm_num [epsilon]

private theorem epos : 1<realValue (epsilon:Zsqrtd 2) := by rw [ev]; linarith [Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)]

private theorem unit_in_interval (u : (Zsqrtd 2)ˣ) (lo : 1≤realValue (u:Zsqrtd 2))
    (hi : realValue (u:Zsqrtd 2)<realValue (epsilon:Zsqrtd 2)) : u=1 := by
  let x : Zsqrtd 2 := u
  let V := realValue x
  let T := (x.re:ℝ)-x.im*Real.sqrt 2
  have sv : V=(x.re:ℝ)+x.im*Real.sqrt 2 := realValue_def x
  have s2 : Real.sqrt 2^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have rb : 1<Real.sqrt 2 ∧ Real.sqrt 2<2 := by
    have pos := Real.sqrt_nonneg 2
    constructor <;> nlinarith
  have n : V*T=(x.norm:ℝ) := by
    rw [sv,Zsqrtd.norm_def]; dsimp [T]; push_cast
    linear_combination -(x.im:ℝ)^2*s2
  have unit : x.norm.natAbs=1 := Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  have un : x.norm=1 ∨ x.norm= -1 := by omega
  have normabs : |V*T|=1 := by rw [n]; rcases un with e|e <;> rw [e] <;> norm_num
  have v1 : 1≤V := lo
  have v2 : V<1+Real.sqrt 2 := ev ▸ hi
  rw [abs_mul,abs_of_pos (by linarith : 0<V)] at normabs
  have t1 : |T|≤1 := by nlinarith [mul_nonneg (show 0≤V-1 by linarith) (abs_nonneg T)]
  obtain ⟨tl,th⟩ := abs_le.mp t1
  have rel : 2*(x.im:ℝ)*Real.sqrt 2=V-T := by rw [sv]; dsimp [T]; ring
  have ip : 0≤x.im := by
    by_contra! e
    have m := mul_neg_of_neg_of_pos (by exact_mod_cast e : (x.im:ℝ)<0) (by positivity : 0<Real.sqrt 2)
    linarith
  have il : x.im≤1 := by
    by_contra! e
    have e' : (2:ℝ)≤x.im := by exact_mod_cast (show 2≤x.im by omega)
    have m := mul_le_mul_of_nonneg_right e' (Real.sqrt_nonneg 2)
    linarith [rb.1]
  have im : x.im=0 := by
    by_contra nz
    have im1 : x.im=1 := by omega
    rw [im1,Int.cast_one,one_mul] at sv
    have z : x.re=0 := by
      have lt : (x.re:ℝ)<1 := by linarith
      have gt : (-1:ℝ)<x.re := by linarith [rb.2]
      exact_mod_cast (show x.re=0 by
        have l : x.re<1 := by exact_mod_cast lt
        have g : -1<x.re := by exact_mod_cast gt
        omega)
    rcases un with h|h <;> norm_num [Zsqrtd.norm_def,im1,z] at h
  rw [im,Int.cast_zero,zero_mul,add_zero] at sv
  have a : x.re=1 := by
    have l : (1:ℤ)≤x.re := by exact_mod_cast (show (1:ℝ)≤x.re by linarith)
    rcases un with h|h <;> simp [Zsqrtd.norm_def,im] at h <;> nlinarith [sq_nonneg (x.re-1)]
  apply Units.ext
  change x=1
  exact Zsqrtd.ext a im

private theorem zvalue (u : (Zsqrtd 2)ˣ) (n : ℤ) :
    realValue ((u^n:(Zsqrtd 2)ˣ):Zsqrtd 2)=realValue (u:Zsqrtd 2)^n := by
  change ((Units.map realValue.toMonoidHom (u^n):ℝˣ):ℝ)=_
  rw [map_zpow,Units.val_zpow_eq_zpow_val]; rfl

private theorem positive_units (u : (Zsqrtd 2)ˣ) (hp : 0<realValue (u:Zsqrtd 2)) : ∃ n : ℤ, u=epsilon^n := by
  obtain ⟨n,lo,hi⟩ := exists_mem_Ico_zpow hp epos
  let v : (Zsqrtd 2)ˣ := u/epsilon^n
  have positive : 0<realValue (epsilon:Zsqrtd 2) := lt_trans zero_lt_one epos
  have hv : realValue (v:Zsqrtd 2)=realValue (u:Zsqrtd 2)/realValue (epsilon:Zsqrtd 2)^n := by
    change realValue ((u:Zsqrtd 2)*↑((epsilon^n)⁻¹:(Zsqrtd 2)ˣ))=_
    rw [map_mul,map_units_inv,zvalue,div_eq_mul_inv]
  have low : 1≤realValue (v:Zsqrtd 2) := by rw [hv,le_div_iff₀ (zpow_pos positive n),one_mul]; exact lo
  have high : realValue (v:Zsqrtd 2)<realValue (epsilon:Zsqrtd 2) := by
    rw [hv,div_lt_iff₀ (zpow_pos positive n)]
    simpa only [zpow_add_one₀ positive.ne',mul_comm (realValue (epsilon:Zsqrtd 2)^n)] using hi
  exact ⟨n,div_eq_one.mp (unit_in_interval v low high)⟩

private theorem all_units (u : (Zsqrtd 2)ˣ) : ∃ n : ℤ, u=epsilon^n ∨ u= -(epsilon^n) := by
  have nz := (u.isUnit.map realValue).ne_zero
  rcases lt_or_gt_of_ne nz with n|p
  · obtain ⟨m,em⟩ := positive_units (-u) (by simpa using n)
    exact ⟨m,Or.inr (by rw [←em,neg_neg])⟩
  · obtain ⟨m,em⟩ := positive_units u p
    exact ⟨m,Or.inl em⟩

/-- Coprime conjugates over the integers of Q(√2) yield a cube times
one of three unit representatives. -/
theorem conjugate_cube {d u : ℕ} (hd : d%2=1) (eqn : d^3+8=u^2) :
    ∃ w : Zsqrtd 2, ∃ r : ℤ, (r=0 ∨ r=1 ∨ r= -1) ∧
      (↑(epsilon^r):Zsqrtd 2)*w^3=⟨(u:ℤ),2⟩ := by
  let _ := IsBezout.toGCDDomain (Zsqrtd 2)
  let z : Zsqrtd 2 := ⟨u,2⟩
  have normz : z.norm=(d:ℤ)^3 := by
    have eqZ : (d:ℤ)^3+8=(u:ℤ)^2 := by exact_mod_cast eqn
    simp only [z,norm_def]; linear_combination -eqZ
  have hp : z*star z=(d:Zsqrtd 2)^3 := by
    rw [←norm_eq_mul_conj,normz,Int.cast_pow,Int.cast_natCast]
  have diff : (z-star z)*(⟨0,1⟩:Zsqrtd 2)=8 := by
    apply Zsqrtd.ext <;> simp [z,re_mul,im_mul]
  have cp : IsCoprime (d:ℤ) 2 := by
    apply IsCoprime.symm
    apply Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    omega
  have cop : IsCoprime ((d:Zsqrtd 2)^3) 8 := by
    have m := ((cp.pow_left (m:=3)).pow_right (n:=3)).map (Int.castRingHom (Zsqrtd 2))
    norm_num at m
    exact m
  have rel : IsRelPrime z (star z) := by
    intro a hz hz'
    apply cop.isRelPrime
    · rw [←hp]; exact hz.trans (dvd_mul_right _ _)
    · rw [←diff]; exact (dvd_sub hz hz').trans (dvd_mul_right _ _)
  obtain ⟨w,v,hv⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr rel) hp
  obtain ⟨n,hn⟩ := all_units v
  obtain ⟨w,ew⟩ : ∃ w : Zsqrtd 2, (↑(epsilon^n):Zsqrtd 2)*w^3=z := by
    rcases hn with h|h
    · exact ⟨w,by rw [←h,mul_comm]; exact hv⟩
    · refine ⟨-w,?_⟩
      rw [h,Units.val_neg] at hv
      linear_combination hv
  let t := (n+1)/3
  let r := n-3*t
  have rep : epsilon^n=epsilon^r*(epsilon^t)^3 := by
    rw [←zpow_natCast (epsilon^t) 3,←zpow_mul,←zpow_add]
    congr 1
    dsimp [r]; omega
  refine ⟨(↑(epsilon^t):Zsqrtd 2)*w,r,by dsimp [r,t]; omega,?_⟩
  rw [rep,Units.val_mul,Units.val_pow_eq_pow_val] at ew
  rw [mul_pow,←mul_assoc]
  exact ew

end BealRealQuadratic

namespace BealRealQuadratic
open Zsqrtd

private theorem cube_real (w : Zsqrtd 2) : (w^3).re=w.re^3+6*w.re*w.im^2 := by
  simp [pow_succ,re_mul,im_mul]; ring

private theorem cube_imaginary (w : Zsqrtd 2) : (w^3).im=3*w.re^2*w.im+2*w.im^3 := by
  simp [pow_succ,re_mul,im_mul]; ring

private theorem cubic_representative {a b : ℤ} (ao : a%2=1)
    (h : a^3+3*a^2*b+6*a*b^2+2*b^3=2) : a=1 ∧ b= -1 := by
  have am : (a:ZMod 2)=((1:ℤ):ZMod 2) := by rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; omega
  have eqm := congrArg (fun w : ℤ => (w:ZMod 2)) h
  push_cast at eqm
  rw [am] at eqm
  have bm : (b:ZMod 2)=((1:ℤ):ZMod 2) :=
    (by decide : ∀ b : ZMod 2, 1^3+3*1^2*b+6*1*b^2+2*b^3=2 → b=1) _ eqm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at bm
  let c := (a+b)/2
  let x := b-c
  have aa : a=2*c-b := by dsimp [c]; omega
  have f : x^3-3*x*c^2-6*c^3= -1 := by dsimp only [x]; rw [aa] at h; nlinarith only [h]
  obtain ⟨ex,ec⟩ := BealThueEight.fixed_cubic f
  dsimp [x] at ex
  omega

/-- The odd positive integral solutions on y²=x³+8 consist of (1,3). -/
theorem odd_eight {d u : ℕ} (hd : d%2=1) (hu : u%2=1) (eqn : d^3+8=u^2) : d=1 ∧ u=3 := by
  obtain ⟨w,r,hr,ew⟩ := conjugate_cube hd eqn
  let v : Zsqrtd 2 := ↑(epsilon^r)*w^2
  have vw : v*w=⟨(u:ℤ),2⟩ := by dsimp [v]; rw [mul_assoc,←pow_succ]; exact ew
  have rprod : v.re*w.re+2*v.im*w.im=(u:ℤ) := congrArg Zsqrtd.re vw
  have odda : w.re%2=1 := by
    by_contra bad
    have ae : (2:ℤ)∣w.re := by omega
    have dd : (2:ℤ)∣(u:ℤ) := by
      rw [←rprod]
      exact dvd_add (dvd_mul_of_dvd_right ae _) (by rw [mul_assoc]; exact dvd_mul_right _ _)
    omega
  rcases hr with e|e|e <;> subst r
  · simp only [zpow_zero,Units.val_one,one_mul] at ew
    have imag := congrArg Zsqrtd.im ew
    change (w^3).im=2 at imag
    rw [cube_imaginary] at imag
    have a2 : 0<w.re^2 := sq_pos_of_ne_zero (by omega)
    have prod : w.im*(3*w.re^2+2*w.im^2)=2 := by linear_combination imag
    have bp : 0<w.im := by
      by_contra! e
      have := mul_nonpos_of_nonpos_of_nonneg e (show 0≤3*w.re^2+2*w.im^2 by positivity)
      omega
    have small := mul_le_mul_of_nonneg_left (show 3≤3*w.re^2+2*w.im^2 by nlinarith [sq_nonneg w.im]) bp.le
    omega
  · rw [zpow_one] at ew
    have imag := congrArg Zsqrtd.im ew
    change (↑epsilon*w^3:Zsqrtd 2).im=2 at imag
    rw [im_mul,cube_imaginary,cube_real] at imag
    change 1*(3*w.re^2*w.im+2*w.im^3)+1*(w.re^3+6*w.re*w.im^2)=2 at imag
    obtain ⟨a,b⟩ := cubic_representative (b:=w.im) odda (by linear_combination imag)
    have rep : w=(⟨1,-1⟩:Zsqrtd 2) := Zsqrtd.ext a b
    rw [rep,show (↑epsilon:Zsqrtd 2)*⟨1,-1⟩^3=⟨-3,2⟩ by decide] at ew
    have ur : (-3:ℤ)=u := congrArg Zsqrtd.re ew
    omega
  · rw [zpow_neg_one] at ew
    have imag := congrArg Zsqrtd.im ew
    change (↑(epsilon⁻¹)*w^3:Zsqrtd 2).im=2 at imag
    rw [im_mul,cube_imaginary,cube_real] at imag
    change (-1)*(3*w.re^2*w.im+2*w.im^3)+1*(w.re^3+6*w.re*w.im^2)=2 at imag
    obtain ⟨a,b⟩ := cubic_representative (b:= -w.im) odda (by linear_combination imag)
    have rep : w=(⟨1,1⟩:Zsqrtd 2) := Zsqrtd.ext a (by change w.im=1; omega)
    rw [rep,show (↑(epsilon⁻¹):Zsqrtd 2)*⟨1,1⟩^3=⟨3,2⟩ by decide] at ew
    have ur : (3:ℤ)=u := congrArg Zsqrtd.re ew
    have eu : u=3 := by omega
    rw [eu] at eqn
    have ed : d^3=1 := by omega
    refine ⟨?_,eu⟩
    by_contra bad
    have ge := Nat.pow_le_pow_left (show 2≤d by omega) 3
    omega

end BealRealQuadratic

namespace BealMordell

/-- The primitive positive solutions of d³+2ᵏ=u² for every Beal exponent k. -/
theorem classify_cube_plus_dyadic {d u k : ℕ} (hd : d%2=1) (hu : u%2=1) (hk : 2<k) :
    d^3+2^k=u^2 ↔ (d=1 ∧ u=3 ∧ k=3) ∨ (d=17 ∧ u=71 ∧ k=7) := by
  constructor
  · intro eqn
    by_cases three : k=3
    · have small : d^3+8=u^2 := by simpa [three] using eqn
      obtain ⟨ed,eu⟩ := BealRealQuadratic.odd_eight hd hu small
      exact Or.inl ⟨ed,eu,three⟩
    by_cases ht : 3∣k
    · exact (odd_difference_triple hu (by omega) ht eqn).elim
    · exact Or.inr (odd_difference_nontriple hu hd hk ht eqn)
  · rintro (⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩) <;> decide

/-- Odd signed square-and-cube representations of a positive power of two. -/
theorem signed_dyadic_square {a b : ℤ} {k : ℕ} (ha : Odd a) (hb : Odd b) (hk : 2<k)
    (eqn : a^3+b^2=(2:ℤ)^k) :
    (a=7 ∧ b.natAbs=13 ∧ k=9) ∨ (a= -1 ∧ b.natAbs=3 ∧ k=3) ∨ (a= -17 ∧ b.natAbs=71 ∧ k=7) := by
  have bo : b.natAbs%2=1 := by have := Int.odd_iff.mp hb; omega
  have b2 : (b.natAbs:ℤ)^2=b^2 := by rw [Int.natCast_natAbs,sq_abs]
  by_cases nn : 0≤a
  · have aa : (a.toNat:ℤ)=a := Int.toNat_of_nonneg nn
    have ao : a.toNat%2=1 := by have := Int.odd_iff.mp ha; omega
    have h : b.natAbs^2+a.toNat^3=2^k := by
      have z : (b.natAbs:ℤ)^2+(a.toNat:ℤ)^3=(2:ℤ)^k := by rw [aa,b2,add_comm]; exact eqn
      exact_mod_cast z
    obtain ⟨er,ed,ek⟩ := classify_odd bo ao hk h
    exact Or.inl ⟨by omega,er,ek⟩
  · have aa : ((-a).toNat:ℤ)= -a := Int.toNat_of_nonneg (by omega)
    have ao : (-a).toNat%2=1 := by have := Int.odd_iff.mp ha; omega
    have h : (-a).toNat^3+2^k=b.natAbs^2 := by
      have z : ((-a).toNat:ℤ)^3+(2:ℤ)^k=(b.natAbs:ℤ)^2 := by rw [aa,b2]; linarith
      exact_mod_cast z
    rcases (classify_cube_plus_dyadic ao bo hk).mp h with ⟨ed,er,ek⟩|⟨ed,er,ek⟩
    · exact Or.inr (Or.inl ⟨by omega,er,ek⟩)
    · exact Or.inr (Or.inr ⟨by omega,er,ek⟩)

private theorem prime_square_not_high_power {v c r : ℕ} (hv : v.Prime) (hr : 2<r) : c^r≠v^2 := by
  intro h
  have dv : c∣v^2 := h ▸ dvd_pow_self _ (by omega)
  obtain ⟨j,_,cj⟩ := (Nat.dvd_prime_pow hv).mp dv
  rw [cj,←pow_mul] at h
  have jr := (Nat.pow_right_inj hv.one_lt).mp h
  by_cases zero : j=0
  · rw [zero] at jr; omega
  have bound := Nat.mul_le_mul_right r (show 1≤j by omega)
  omega

private theorem pow_parity {b n : ℕ} (hn : 0<n) : b^n%2=b%2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one b with e|e <;> rw [e] <;> simp [hn.ne']

/-- For a dyadic summand, the other two terms cannot be respectively
a cube and a square in either order, even if their displayed exponents
are odd primes and the powers occur in the bases. -/
theorem mixed_power_restrictions {b c p r k : ℕ} (hb : b%2=1) (hc : c%2=1)
    (hr : 2<r) (hk : 2<k) (eqn : 2^k+b^p=c^r) :
    (∀ d u : ℕ, b^p=d^3 → c^r≠u^2) ∧ (∀ u d : ℕ, b^p=u^2 → c^r≠d^3) := by
  have bp : b^p%2=1 := by rw [Nat.pow_mod,hb]; simp
  have cr : c^r%2=1 := by rw [Nat.pow_mod,hc]; simp
  constructor
  · intro d u cube square
    rw [cube,pow_parity (by decide : 0<3)] at bp
    rw [square,pow_parity (by decide : 0<2)] at cr
    rw [cube,square,Nat.add_comm] at eqn
    rcases (classify_cube_plus_dyadic bp cr hk).mp eqn with ⟨_,eu,_⟩|⟨_,eu,_⟩ <;> rw [eu] at square
    · exact prime_square_not_high_power (by decide : Nat.Prime 3) hr square
    · exact prime_square_not_high_power (by decide : Nat.Prime 71) hr square
  · intro u d square cube
    rw [square,pow_parity (by decide : 0<2)] at bp
    rw [cube,pow_parity (by decide : 0<3)] at cr
    rw [square,cube,Nat.add_comm] at eqn
    have := OMA.R_BealConjecture_beal_conjecture_R2_H2_R1.BealQuadratic.classify_square_through_thirty bp cr hk (by decide : 2<3) (by decide) eqn
    omega

private theorem dyadic_summand_even {a b c x y z : ℕ} (hx : 2<x) (hy : 2<y) (hz : 2<z)
    (dyadic : ∃ t : ℕ, 0<t ∧ a=2^t) (exps : (3∣y ∧ 2∣z) ∨ (2∣y ∧ 3∣z))
    (eqn : a^x+b^y=c^z) : 2∣a ∧ 2∣b ∧ 2∣c := by
  obtain ⟨t,ht,ea⟩ := dyadic
  have da : 2∣a := ea ▸ dvd_pow_self _ ht.ne'
  refine ⟨da,?_⟩
  have hk : 2<t*x := by nlinarith
  rw [ea,←pow_mul] at eqn
  have par := congrArg (fun w : ℕ => w%2) eqn
  change (2^(t*x)+b^y)%2=c^z%2 at par
  have ev : 2^(t*x)%2=0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self _ (by omega))
  rw [Nat.add_mod,ev,pow_parity (by omega : 0<y),pow_parity (by omega : 0<z)] at par
  simp only [zero_add,Nat.mod_mod] at par
  by_contra! bad
  have bo : b%2=1 := by omega
  have co : c%2=1 := by omega
  have forbid := mixed_power_restrictions bo co hz hk eqn
  rcases exps with ⟨⟨s,es⟩,⟨r,er⟩⟩|⟨⟨r,er⟩,⟨s,es⟩⟩
  · apply forbid.1 (b^s) (c^r)
    · rw [←pow_mul,es,Nat.mul_comm]
    · rw [←pow_mul,er,Nat.mul_comm]
  · apply forbid.2 (b^r) (c^s)
    · rw [←pow_mul,er,Nat.mul_comm]
    · rw [←pow_mul,es,Nat.mul_comm]

/-- Beal's gcd conclusion for all placements of a power-of-two base,
when the other two exponents are divisible by two and three in either order. -/
theorem beal_dyadic_square_cube {a b c x y z : ℕ} (ha : a≠0) (hx : 2<x) (hy : 2<y) (hz : 2<z)
    (pattern :
      ((∃ t : ℕ, 0<t ∧ a=2^t) ∧ ((3∣y ∧ 2∣z) ∨ (2∣y ∧ 3∣z))) ∨
      ((∃ t : ℕ, 0<t ∧ b=2^t) ∧ ((3∣x ∧ 2∣z) ∨ (2∣x ∧ 3∣z))) ∨
      ((∃ t : ℕ, 0<t ∧ c=2^t) ∧ ((2∣x ∧ 3∣y) ∨ (3∣x ∧ 2∣y))))
    (eqn : a^x+b^y=c^z) : (2∣a ∧ 2∣b ∧ 2∣c) ∧ 1<Finset.gcd {a,b,c} id := by
  have even : 2∣a ∧ 2∣b ∧ 2∣c := by
    rcases pattern with ⟨dy,ex⟩|⟨dy,ex⟩|⟨⟨t,ht,ec⟩,ex⟩
    · exact dyadic_summand_even hx hy hz dy ex eqn
    · obtain ⟨B,A,C⟩ := dyadic_summand_even hy hx hz dy ex ((Nat.add_comm _ _).trans eqn)
      exact ⟨A,B,C⟩
    · have hk : 2<t*z := by nlinarith
      rw [ec,←pow_mul] at eqn
      have AB : 2∣a ∧ 2∣b := by
        rcases ex with ⟨dx,dy⟩|⟨dx,dy⟩
        · exact even_bases_of_dyadic_result hx (by omega) hk dx dy eqn
        · exact (even_bases_of_dyadic_result hy (by omega) hk dy dx ((Nat.add_comm _ _).trans eqn)).symm
      exact ⟨AB.1,AB.2,ec ▸ dvd_pow_self _ ht.ne'⟩
  refine ⟨even,?_⟩
  have dv : 2∣Finset.gcd {a,b,c} id := by
    apply Finset.dvd_gcd
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl
    · exact even.1
    · exact even.2.1
    · exact even.2.2
  have pos := Finset.gcd_ne_zero_iff.mpr (show ∃ n ∈ ({a,b,c}:Finset ℕ), id n≠0 from ⟨a,Finset.mem_insert_self _ _,ha⟩)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero pos) dv

end BealMordell

theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H2_R1.H4 := by
  intro a b k
  exact ⟨fun h e => BealDescent.TwentyThree.exponent_obstruction h e,
    fun ha hb hk he => BealMordell.signed_dyadic_square ha hb hk he⟩
