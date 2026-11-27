import Mathlib

/-! Numerical inequalities and the integer-product argument for section 13. -/

namespace Erdos1052.LayerConstants

theorem path_loss {Y k : ℚ} (h : 1 < k) (hY : k < Y) :
    1 / (1 - (k-1)/(k*Y)) < Y^2 / (Y^2-Y+1) := by
  have hy : 0 < Y := by linarith
  have hk : 0 < k := by linarith
  have hprod : 0 < k * Y := mul_pos hk hy
  have hden : 0 < Y^2-Y+1 := by nlinarith [sq_nonneg (Y-1/2)]
  have hpos : 0 < 1-(k-1)/(k*Y) := by
    have hlt : (k-1)/(k*Y) < 1 := (div_lt_one hprod).mpr (by nlinarith [mul_pos hk (show 0 < Y-1 by linarith)])
    linarith
  rw [div_lt_div_iff₀ hpos hden]
  field_simp
  nlinarith [mul_pos hy (sub_pos.mpr hY)]

theorem losses :
    (5/8+1/3 : ℚ)=23/24 ∧ 13/16+5/32+1/48=(95/96 : ℚ) ∧
    101/128+13/64+1/192=(383/384 : ℚ) := by norm_num

def potential (xs : List ℤ) : ℤ := (xs.map fun z => |z|+1).prod

private theorem potential_nonneg (xs : List ℤ) : 0 ≤ potential xs := by
  induction xs with
  | nil => simp [potential]
  | cons x xs ih =>
    change 0 ≤ (|x|+1)*potential xs
    exact mul_nonneg (by positivity) ih

private theorem abs_prod_le_potential (xs : List ℤ) : |xs.prod| ≤ potential xs := by
  induction xs with
  | nil => simp [potential]
  | cons x xs ih =>
    change |x*xs.prod| ≤ (|x|+1)*potential xs
    rw [abs_mul]
    exact mul_le_mul (by linarith) ih (abs_nonneg _) (by positivity)

private theorem prod_margin (xs : List ℤ) (hne : xs ≠ []) :
    |xs.prod|+1 ≤ potential xs := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    change |x*xs.prod|+1 ≤ (|x|+1)*potential xs
    rw [abs_mul]
    have hfac := abs_prod_le_potential xs
    have hpos : 1 ≤ potential xs := by
      unfold potential
      apply List.one_le_prod
      intro t ht
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp ht
      linarith [abs_nonneg z]
    nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hfac)]

/-- Replace a nonempty group of predecessor constants by the constant of
its successor. The middle argument is the product of the shift multipliers. -/
inductive Moves : List ℤ → ℤ → List ℤ → Prop
  | done (xs) : Moves xs 1 xs
  | step {xs factors rest zs k D} (hk : 2 ≤ k) (hf : factors ≠ [])
      (hp : xs.Perm (factors ++ rest))
      (ht : Moves ((k*factors.prod-1)::rest) D zs) : Moves xs (k*D) zs

private theorem step_lower (k m : ℤ) (hk : 2 ≤ k) : |m| ≤ |k*m-1| := by
  rcases le_or_gt m 0 with hm|hm
  · rw [abs_of_nonpos hm, abs_of_nonpos (by nlinarith [mul_nonpos_of_nonneg_of_nonpos (by omega : 0≤k-1) hm] : k*m-1≤0)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by omega : 0≤k-1) hm]
  · have h : 0 ≤ (k-1)*m-1 := by
      nlinarith [mul_nonneg (by omega : 0 ≤ k-2) (by omega : 0 ≤ m), (show 1 ≤ m by omega)]
    rw [abs_of_pos hm, abs_of_nonneg (by nlinarith : 0≤k*m-1)]
    nlinarith

theorem moves_bounds {xs ys : List ℤ} {D : ℤ} (h : Moves xs D ys) :
    1≤D ∧ |xs.prod|≤|ys.prod| ∧ potential ys≤D*potential xs := by
  induction h with
  | done xs => simp
  | @step xs fs rest ys k D hk hf hp ht ih =>
    obtain ⟨hD,hl,hu⟩ := ih
    have hpp : potential xs=potential fs*potential rest := by
      unfold potential
      rw [(hp.map (fun z : ℤ => |z|+1)).prod_eq, List.map_append, List.prod_append]
    have hm : |k*fs.prod-1|+1 ≤ k*potential fs := by
      have H : |k*fs.prod-1| ≤ |k*fs.prod|+1 := by
        simpa using (abs_sub_le (k*fs.prod) 0 1)
      rw [abs_mul, abs_of_nonneg (by omega : 0≤k)] at H
      nlinarith [mul_nonneg (by omega : 0≤k) (sub_nonneg.mpr (prod_margin fs hf))]
    refine ⟨by nlinarith [mul_nonneg (by omega : 0≤k) (by omega : 0≤D-1)], ?_, ?_⟩
    · rw [hp.prod_eq, List.prod_append,abs_mul]
      apply le_trans _ hl
      simpa only [List.prod_cons,abs_mul] using
        mul_le_mul_of_nonneg_right (step_lower k fs.prod hk) (abs_nonneg rest.prod)
    · change potential ys ≤ D*((|k*fs.prod-1|+1)*potential rest) at hu
      rw [hpp]
      calc potential ys ≤ D*((|k*fs.prod-1|+1)*potential rest) := hu
           _ ≤ D*((k*potential fs)*potential rest) :=
               mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (potential_nonneg rest)) (by omega)
           _ = k*D*(potential fs*potential rest) := by ring

/-- With the first forced successor processed, a neutral quintic layer
would supply exactly this frontier, multiplier product and congruence. -/
theorem quintic_frontier_impossible {Y D : ℤ} {ys : List ℤ}
    (hy : 4096*D=Y) (h : Moves [-3,-1,-1] D ys) (hm : Y ∣ ys.prod-1) : False := by
  obtain ⟨hD,hl,hu⟩ := moves_bounds h
  norm_num [potential] at hl hu
  have hab := (abs_prod_le_potential ys).trans hu
  obtain ⟨t,ht⟩ := hm
  have ht0 : t≠0 := by
    rintro rfl
    have heq : ys.prod=1 := by simpa only [mul_zero,sub_eq_zero] using ht
    rw [heq] at hl
    norm_num at hl
  have hbig : Y ≤ |Y*t| := by
    rw [abs_mul,abs_of_pos (by omega : 0<Y)]
    have ht1 : 1≤|t| := by have := abs_pos.mpr ht0; omega
    nlinarith [mul_nonneg (by omega : 0≤Y) (by omega : 0≤|t|-1)]
  rw [←ht] at hbig
  have H : |ys.prod-1| ≤ |ys.prod|+1 := by simpa using (abs_sub_le ys.prod 0 1)
  omega

/-- At a prime on the path to a seed divisor, an affine representation of
the endpoint bounds the prime together with any common shift divisor. -/
theorem affine_shift_bound {q L u p H Z T : ℤ} (hq : 1 < q) (hH : 0 < H)
    (hu0 : 0 ≤ u) (hu : u < L) (hp : p=L*q-u) (hn : H*p=Z+1)
    (hz : T ∣ Z) (ht : T ∣ q+1) : (q-1)*(T-1) < 2*(Z+1) := by
  have hi : H*(L+u)+1=(H*L)*(q+1)-Z := by rw [hp] at hn; linear_combination -hn
  have hd : T ∣ H*(L+u)+1 := hi ▸ dvd_sub (dvd_mul_of_dvd_right ht _) hz
  have pos : 0 < L+u := by omega
  have upper := Int.le_of_dvd (by positivity : 0 < H*(L+u)+1) hd
  have hq' : 0 < q-1 := by omega
  have hp' : L*(q-1) < p := by rw [hp]; linarith
  calc (q-1)*(T-1) ≤ (q-1)*(H*(L+u)) := by
        apply mul_le_mul_of_nonneg_left _ hq'.le; omega
       _ < (q-1)*(H*(2*L)) := by
        apply mul_lt_mul_of_pos_left _ hq'
        apply mul_lt_mul_of_pos_left _ hH
        omega
       _ = (2*H)*(L*(q-1)) := by ring
       _ < (2*H)*p := mul_lt_mul_of_pos_left hp' (by positivity)
       _ = 2*(Z+1) := by rw [←hn]; ring

end Erdos1052.LayerConstants
