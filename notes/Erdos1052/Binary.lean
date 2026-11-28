import Mathlib

/-! A binary lower bound for cyclotomic quotients multiplied by the denominators
of constant runs in a tree of shifted primes. All jump sizes may vary. -/

namespace Erdos1052.Binary

/-- Denominators obtained by summing finite geometric progressions. -/
def mask (jumps : List ℕ) : ℤ := (jumps.map (fun j => (2:ℤ)^j-1)).prod

private theorem high_mask (t : ℕ) (js : List ℕ) (hh : ∀ j ∈ js, t≤j) :
    mask js ≡ (-1:ℤ)^js.length [ZMOD (2:ℤ)^t] := by
  induction js with
  | nil => simp [mask]
  | cons j js ih =>
    have hd : (2:ℤ)^t ∣ (2:ℤ)^j := pow_dvd_pow _ (hh j (by simp))
    have hm : (2:ℤ)^j-1 ≡ -1 [ZMOD (2:ℤ)^t] := by
      apply Int.modEq_iff_dvd.mpr
      rw [show (-1:ℤ)-(2^j-1) = -(2^j) by ring]
      exact dvd_neg.mpr hd
    simpa [mask,pow_succ,mul_comm] using hm.mul (ih (fun i hi => hh i (by simp [hi])))

/-- Find a block of `width` bits where the mask is congruent to a small
integer still indivisible by the designated prime. -/
theorem mask_window {p : ℤ} (hp : Prime p) (width s : ℕ) (c : ℤ) (js : List ℕ)
    (hc : |c| ≤ (2:ℤ)^s) (hpc : ¬ p ∣ c) (hj : ∀ j ∈ js, ¬ p ∣ (2:ℤ)^j-1) :
    ∃ u k, s≤u ∧ u+width≤2^js.length*(s+width) ∧ |k| ≤ (2:ℤ)^u ∧ ¬p ∣ k ∧
      c*mask js ≡ k [ZMOD (2:ℤ)^(u+width)] := by
  classical
  by_cases h : ∃ j ∈ js, j < s+width
  · obtain ⟨j,hmem,hsmall⟩ := h
    let m := (2:ℤ)^j-1
    have hm : |m| ≤ (2:ℤ)^j := by
      have h1 : 1 ≤ (2:ℤ)^j := one_le_pow₀ (by norm_num)
      dsimp [m]; rw [abs_of_nonneg (by linarith)]; omega
    have hcn : |c*m| ≤ (2:ℤ)^(s+j) := by
      rw [abs_mul,pow_add]; exact mul_le_mul hc hm (abs_nonneg _) (by positivity)
    have hpn : ¬p ∣ c*m := fun hh => (hp.dvd_mul.mp hh).elim hpc (hj j hmem)
    obtain ⟨u,k,hu,hub,hk,hpk,hkey⟩ := mask_window hp width (s+j) (c*m) (js.erase j)
      hcn hpn (fun i hi => hj i (List.mem_of_mem_erase hi))
    have hlen : js.length = (js.erase j).length+1 := (List.perm_cons_erase hmem).length_eq
    have hre : mask js=m*mask (js.erase j) :=
      ((List.perm_cons_erase hmem).map (fun i => (2:ℤ)^i-1)).prod_eq
    refine ⟨u,k,by omega,hub.trans ?_,hk,hpk,?_⟩
    · rw [hlen,pow_succ,mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    · simpa only [hre,mul_assoc] using hkey
  · have hh : ∀ j ∈ js, s+width≤j := fun j hmem => Nat.le_of_not_gt (fun hs => h ⟨j,hmem,hs⟩)
    refine ⟨s,c*(-1)^js.length,le_rfl,Nat.le_mul_of_pos_left _ (by positivity),?_,?_,
      (high_mask _ js hh).mul_left c⟩
    · simpa [abs_mul,abs_pow] using hc
    · intro hd
      rcases hp.dvd_mul.mp hd with hd | hd
      · exact hpc hd
      · exact hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_neg_one.pow _))
termination_by js.length
decreasing_by
  have := (List.perm_cons_erase hmem).length_eq
  simp only [List.length_cons] at this
  omega

/-- Every block of `h+1` binary places in the indicated range must
contain a term in any signed representation with distinct exponents. -/
private theorem term_in_block {x h : ℕ} (hh : 0<h) (pos : Finset ℕ) (sgn : ℕ → ℤ)
    (hb : ∀ i ∈ pos, |sgn i| ≤ 1) {k : ℤ} (hk : |k| ≤ (2:ℤ)^x)
    (hn : ¬ ((2:ℤ)^h+1) ∣ k)
    (hm : ((2:ℤ)^h+1)*(∑ i ∈ pos, sgn i*2^i) ≡ k [ZMOD (2:ℤ)^(x+(h+1))]) :
    ∃ i ∈ pos, x ≤ i ∧ i < x+(h+1) := by
  classical
  by_contra! none
  let low := pos.filter (·<x)
  let a := ∑ i ∈ low, sgn i*(2:ℤ)^i
  have habs : |a| < (2:ℤ)^x := by
    have hlo : ∀ i ∈ low, i<x := fun i hi => (Finset.mem_filter.mp hi).2
    have hgeom := Nat.geomSum_lt (m:=2) (by decide) hlo
    calc |a| ≤ ∑ i ∈ low, |sgn i*(2:ℤ)^i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ low, (2:ℤ)^i := Finset.sum_le_sum fun i hi => by
        rw [abs_mul,abs_of_nonneg (show 0 ≤ (2:ℤ)^i by positivity)]
        exact (mul_le_mul_of_nonneg_right (hb i (Finset.mem_filter.mp hi).1) (by positivity)).trans_eq (one_mul _)
      _ < (2:ℤ)^x := by exact_mod_cast hgeom
  have hrest : (2:ℤ)^(x+(h+1)) ∣ ∑ i ∈ pos with ¬i<x, sgn i*2^i :=
    Finset.dvd_sum fun i hi => dvd_mul_of_dvd_right
      (pow_dvd_pow _ (none i (Finset.mem_filter.mp hi).1 (by have := (Finset.mem_filter.mp hi).2; omega))) _
  have hmod : a ≡ ∑ i ∈ pos, sgn i*2^i [ZMOD (2:ℤ)^(x+(h+1))] := by
    apply Int.modEq_iff_dvd.mpr
    rw [← Finset.sum_filter_add_sum_filter_not pos (·<x) (fun i => sgn i*(2:ℤ)^i)]
    simpa only [a,low,add_sub_cancel_left] using hrest
  let F := (2:ℤ)^h+1
  have hd : (2:ℤ)^(x+(h+1)) ∣ k-F*a := Int.modEq_iff_dvd.mp ((hmod.mul_left F).trans hm)
  have hne : k-F*a ≠ 0 := by
    intro he; exact hn ⟨a,by dsimp only [F] at he; omega⟩
  have hbig : (2:ℤ)^(x+(h+1)) ≤ |k-F*a| :=
    Int.le_of_dvd (abs_pos.mpr hne) (by
      rcases le_total 0 (k-F*a) with h | h
      · simpa [abs_of_nonneg h] using hd
      · simpa only [abs_of_nonpos h] using dvd_neg.mpr hd)
  have hp : 2 ≤ (2:ℤ)^h := by simpa using (pow_le_pow_right₀ (show (1:ℤ)≤2 by norm_num) hh : (2:ℤ)^1 ≤ 2^h)
  have hF : 0 < F := by dsimp [F]; positivity
  have hsmall := abs_sub_le k 0 (F*a)
  have htri : |k-F*a| ≤ |k|+F*|a| := by
    simpa only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos hF] using hsmall
  rw [pow_add,pow_succ] at hbig
  dsimp only [F] at htri
  have h1 := mul_lt_mul_of_pos_left habs hF
  dsimp only [F] at h1
  have h2 := mul_nonneg (show 0≤ (2:ℤ)^h-2 by omega) (show 0≤(2:ℤ)^x by positivity)
  nlinarith

/-- A closed bound, uniform in the individual geometric denominators. -/
theorem binary_bound {p : ℤ} (hp : Prime p) {h N : ℕ} (hh : 0<h)
    (hF : p ∣ (2:ℤ)^h+1) (js : List ℕ) (hj : ∀ j ∈ js, ¬ p ∣ (2:ℤ)^j-1)
    (pos : Finset ℕ) (sgn : ℕ → ℤ) (hb : ∀ i ∈ pos, |sgn i|≤1)
    (heq : ((2:ℤ)^h+1)*(∑ i ∈ pos, sgn i*2^i)=((2:ℤ)^N+1)*mask js) :
    N < 2^js.length*((pos.card+1)*(h+1)) := by
  classical
  let L := (pos.card+1)*(h+1)
  by_contra! hN
  obtain ⟨u,k,_,hwidth,hk,hpk,hm⟩ := mask_window hp L 0 1 js (by simp) hp.not_dvd_one hj
  simp only [zero_add,one_mul] at hwidth hm
  have hut : u+L≤N := hwidth.trans hN
  have base : ((2:ℤ)^N+1)*mask js ≡ mask js [ZMOD (2:ℤ)^(u+L)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [show mask js-((2:ℤ)^N+1)*mask js = (2:ℤ)^N*(-mask js) by ring]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ hut) _
  have noF : ¬ ((2:ℤ)^h+1) ∣ k := fun hd => hpk (hF.trans hd)
  have find (i : ℕ) (hi : i<pos.card+1) : ∃ e ∈ pos,
      u+i*(h+1)≤e ∧ e<u+(i+1)*(h+1) := by
    have hle : u+i*(h+1)+(h+1)≤u+L := by
      dsimp only [L]; rw [Nat.add_assoc,←Nat.succ_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
    have hkb : |k| ≤ (2:ℤ)^(u+i*(h+1)) := hk.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    obtain ⟨e,he,h1,h2⟩ := term_in_block hh pos sgn hb hkb noF
      (Int.ModEq.of_dvd (pow_dvd_pow _ hle) (heq ▸ base.trans hm))
    exact ⟨e,he,h1,by simpa [Nat.succ_mul,Nat.add_assoc] using h2⟩
  let D := Finset.range (pos.card+1)
  let f : ℕ → ℕ := fun i => if H : i<pos.card+1 then (find i H).choose else 0
  have fs i (hi : i∈D) : f i∈pos ∧ u+i*(h+1)≤f i ∧ f i<u+(i+1)*(h+1) := by
    have H := Finset.mem_range.mp hi
    simpa only [f,dif_pos H] using (find i H).choose_spec
  have strict {i j : ℕ} (hi : i∈D) (hj : j∈D) (hlt : i<j) : f i < f j :=
    (fs i hi).2.2.trans_le ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hlt) u).trans (fs j hj).2.1)
  have hc := Finset.card_le_card_of_injOn f (s:=D) (t:=pos) (fun i hi => (fs i hi).1) (by
    intro i hi j hj he; by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact (strict hi hj h).ne he
    · exact (strict hj hi h).ne he.symm)
  simp [D] at hc

/-- A signed power of two, with `true` for the positive sign. -/
def digit (d : Bool × ℕ) : ℤ := if d.1 then 2^d.2 else -(2^d.2)

def value (ds : List (Bool × ℕ)) : ℤ := (ds.map digit).sum

private theorem insert_digit (a : Bool × ℕ) (xs : List (Bool × ℕ))
    (hn : (xs.map Prod.snd).Nodup) :
    ∃ ys : List (Bool × ℕ), (ys.map Prod.snd).Nodup ∧ ys.length≤xs.length+1 ∧
      value ys=digit a+value xs := by
  classical
  by_cases H : ∃ b ∈ xs, b.2=a.2
  · obtain ⟨b,hb,he⟩ := H
    have per := List.perm_cons_erase hb
    have len := per.length_eq
    simp only [List.length_cons] at len
    have hv : value xs = digit b+value (xs.erase b) := (per.map digit).sum_eq
    have hr := (per.map Prod.snd).nodup_iff.mp hn
    simp only [List.map_cons,List.nodup_cons] at hr
    by_cases eq : b.1=a.1
    · obtain ⟨ys,hn',hl,hy⟩ := insert_digit (a.1,a.2+1) (xs.erase b) hr.2
      refine ⟨ys,hn',by omega,?_⟩
      have carry : digit (a.1,a.2+1)=digit a+digit b := by
        simp only [digit,eq,he,pow_succ]; split <;> ring
      rw [hy,carry,hv,add_assoc]
    · refine ⟨xs.erase b,hr.2,by omega,?_⟩
      have cancel : digit a+digit b=0 := by
        rcases a with ⟨sa,ea⟩; rcases b with ⟨sb,eb⟩
        cases sa <;> cases sb <;> simp_all [digit]
      rw [hv,←add_assoc,cancel,zero_add]
  · refine ⟨a::xs,?_,by simp,rfl⟩
    simpa [List.nodup_cons,hn] using H
termination_by xs.length
decreasing_by
  have H := (List.perm_cons_erase hb).length_eq
  simp only [List.length_cons] at H
  omega

/-- Equal powers can be carried or cancelled without increasing the number
of signed digits. -/
theorem normalize_digits (xs : List (Bool × ℕ)) :
    ∃ ys : List (Bool × ℕ), (ys.map Prod.snd).Nodup ∧ ys.length≤xs.length ∧ value ys=value xs := by
  induction xs with
  | nil => exact ⟨[],by simp,le_rfl,rfl⟩
  | cons a xs ih =>
    obtain ⟨zs,hn,hl,hz⟩ := ih
    obtain ⟨ys,hyn,hyl,hy⟩ := insert_digit a zs hn
    exact ⟨ys,hyn,hyl.trans (by simpa using Nat.add_le_add_right hl 1),by rw [hy,hz]; rfl⟩

private theorem odd_mask {p h j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : p ∣ 2^h+1)
    (hj : Odd j) : ¬ (p:ℤ) ∣ (2:ℤ)^j-1 := by
  intro hd
  have e1 : (2:ℤ)^j ≡ 1 [ZMOD (p:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [show 1-(2:ℤ)^j=-(2^j-1) by ring]; exact dvd_neg.mpr hd
  have hfi : (p:ℤ) ∣ (2:ℤ)^h+1 := by exact_mod_cast hf
  have e2 : (2:ℤ)^h ≡ -1 [ZMOD (p:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [show -1-(2:ℤ)^h=-(2^h+1) by ring]; exact dvd_neg.mpr hfi
  have H := (e1.pow h).symm
  rw [one_pow,←pow_mul,Nat.mul_comm,pow_mul] at H
  have bad := Int.modEq_iff_dvd.mp (H.trans (e2.pow j))
  rw [hj.neg_one_pow] at bad
  have hh : (p:ℤ) ∣ (2:ℤ) := by simpa using (dvd_neg.mp (show (p:ℤ) ∣ -(2:ℤ) by convert bad using 1; norm_num))
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp (by exact_mod_cast hh))

/-- The bound for arbitrary signed expressions in place of an already
normalized expansion. Every odd jump is automatically admissible. -/
theorem quotient_bound (h N : ℕ) (hh : 0<h) (js : List ℕ) (hj : ∀ j ∈ js, Odd j)
    (xs : List (Bool × ℕ)) (heq : ((2:ℤ)^h+1)*value xs=((2:ℤ)^N+1)*mask js) :
    N < 2^js.length*((xs.length+1)*(h+1)) := by
  obtain ⟨p,hp,hf⟩ := Nat.exists_prime_and_dvd (n:=(2:ℕ)^h+1) (by have := Nat.two_pow_pos h; omega)
  have hp2 : p≠2 := by
    intro e; subst p
    exact ((even_two.pow_of_ne_zero hh.ne').add_odd odd_one).not_two_dvd_nat hf
  obtain ⟨ys,hn,hl,hy⟩ := normalize_digits xs
  let f := fun i : ℕ => if (true,i) ∈ ys then (1:ℤ) else -1
  let pos := (ys.map Prod.snd).toFinset
  have card : pos.card=ys.length := by simpa [pos] using List.toFinset_card_of_nodup hn
  have he : (∑ i ∈ pos, f i*2^i)=value ys := by
    rw [show pos=(ys.map Prod.snd).toFinset from rfl,List.sum_toFinset _ hn,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    rintro ⟨b,i⟩ hmem
    cases b with
    | true => simp [f,hmem,digit]
    | false =>
      have H : (true,i) ∉ ys := by
        intro hh
        have inj := (List.nodup_map_iff_inj_on (hn.of_map Prod.snd)).mp hn
        have := inj (true,i) hh (false,i) hmem rfl
        cases this
      simp [f,H,digit]
  have key := binary_bound (Nat.prime_iff_prime_int.mp hp) (h:=h) (N:=N) hh (by exact_mod_cast hf)
    js (fun j hj' => odd_mask hp hp2 hf (hj j hj')) pos f
    (fun i _ => by dsimp [f]; split <;> norm_num) (by rw [he,hy,heq])
  rw [card] at key
  exact key.trans_le (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))

/-- Representation by at most `k` signed binary terms. -/
def Sparse (z : ℤ) (k : ℕ) : Prop := ∃ xs, value xs=z ∧ xs.length≤k

private theorem digit_shift (a : Bool × ℕ) (j : ℕ) :
    digit (a.1,a.2+j)=2^j*digit a := by
  cases a with | mk b e => cases b <;> simp [digit,pow_add,mul_comm]

private theorem sparseShift {z : ℤ} {n : ℕ} (h : Sparse z n) (j : ℕ) : Sparse (2^j*z) n := by
  obtain ⟨xs,hx,hl⟩ := h
  let f := fun a : Bool × ℕ => (a.1,a.2+j)
  refine ⟨xs.map f,?_,by simpa using hl⟩
  rw [value,List.map_map]
  have change : digit ∘ f = fun a => (2:ℤ)^j*digit a := funext (fun a => digit_shift a j)
  rw [change,List.sum_map_mul_left,show (xs.map digit).sum=z from hx]

private theorem sparseNeg {z : ℤ} {n : ℕ} (h : Sparse z n) : Sparse (-z) n := by
  obtain ⟨xs,hx,hl⟩ := h
  let f := fun a : Bool × ℕ => (!a.1,a.2)
  have hneg : digit ∘ f=fun a => -digit a := by
    funext a; rcases a with ⟨b,e⟩; cases b <;> simp [digit,f]
  refine ⟨xs.map f,?_,by simpa using hl⟩
  rw [value,List.map_map,hneg]
  calc _ = (List.map Neg.neg (xs.map digit)).sum := by rw [List.map_map]; rfl
       _ = -z := by
         have negSum (l : List ℤ) : (l.map Neg.neg).sum = -l.sum := by
           induction l with
           | nil => simp
           | cons a l ih => simp [ih,add_comm]
         rw [negSum,show (xs.map digit).sum=z from hx]

private theorem sparseAdd {z y : ℤ} {n m : ℕ} (a : Sparse z n) (b : Sparse y m) :
    Sparse (z+y) (n+m) := by
  obtain ⟨x,hx,hl⟩ := a; obtain ⟨w,hw,hm⟩ := b
  exact ⟨x++w,by simpa [value] using congrArg₂ (·+·) hx hw,by simpa using Nat.add_le_add hl hm⟩

private theorem sparseSmallMul {z : ℤ} {n : ℕ} (hz : Sparse z n) (m : ℕ) :
    Sparse (m*z) (m*n) := by
  induction m with
  | zero => exact ⟨[],by simp [value],by simp⟩
  | succ m ih => simpa [Nat.succ_mul,add_mul] using sparseAdd ih hz

/-- Distinct subtrees combine by multiplying their signed representations. -/
theorem sparseMul {z y : ℤ} {n m : ℕ} (ha : Sparse z n) (hb : Sparse y m) : Sparse (z*y) (n*m) := by
  obtain ⟨xs,hx,hl⟩ := ha
  have go (ds : List (Bool × ℕ)) : Sparse (value ds*y) (ds.length*m) := by
    induction ds with
    | nil => exact ⟨[],by simp [value],by simp⟩
    | cons a ds ih =>
      have hv : value (a::ds)=digit a+value ds := rfl
      rw [hv,add_mul,List.length_cons,Nat.succ_mul,Nat.add_comm]
      have hd : Sparse (digit a*y) m := by
        rcases a with ⟨b,e⟩; cases b with
        | false => simpa [digit] using sparseNeg (sparseShift hb e)
        | true => simpa [digit] using sparseShift hb e
      exact sparseAdd hd ih
  obtain ⟨zs,h,hs⟩ := go xs
  exact ⟨zs,h.trans (by rw [hx]),hs.trans (Nat.mul_le_mul_right _ hl)⟩

/-- Numerator and denominator costs at a vertex with core factor `m`. -/
theorem marked_cost {N H : ℤ} {n d : ℕ} (hn : Sparse N n) (hd : Sparse H d)
    (m j : ℕ) (hm : 1 ≤ m) :
    Sparse (2^j*(m:ℤ)*N-H) (m*n+d) ∧ (m*n+d)+d≤3*m*(n+d) := by
  constructor
  · simpa [mul_assoc,sub_eq_add_neg] using sparseAdd (sparseShift (sparseSmallMul hn m) j) (sparseNeg hd)
  · nlinarith [Nat.mul_le_mul_right d hm]

/-- An arbitrary constant run has no cost depending on its length or jump. -/
theorem run_cost {N H : ℤ} {n d : ℕ} (hn : Sparse N n) (hd : Sparse H d) (j s : ℕ) :
    Sparse ((2:ℤ)^s*(2^j-1)*N-(2^s-1)*H) ((n+n)+(d+d)) ∧
      Sparse ((2^j-1)*H) (d+d) ∧ (n+n+(d+d))+(d+d)≤4*(n+d) := by
  have sub {z : ℤ} {a : ℕ} (h : Sparse z a) (t : ℕ) : Sparse ((2^t-1)*z) (a+a) := by
    rw [sub_mul,one_mul,sub_eq_add_neg]
    exact sparseAdd (sparseShift h t) (sparseNeg h)
  refine ⟨?_,sub hd j,by omega⟩
  simpa [mul_assoc,sub_eq_add_neg] using sparseAdd (sparseShift (sub hn j) s) (sparseNeg (sub hd s))

/-- The constant for the bound obtained after at most five runs per marked vertex. -/
theorem multiplier_bound {h b D M : ℕ} (hh : 0<h) (hD : 0<D) (js : List ℕ)
    (hj : ∀ j ∈ js, Odd j) (hc : js.length≤5*M) (z : ℤ)
    (hz : Sparse z (D*3^M*4^js.length))
    (heq : ((2:ℤ)^h+1)*z=((2:ℤ)^(h*b)+1)*mask js) : b < 4*D*2^(17*M) := by
  obtain ⟨xs,hx,hl⟩ := hz
  have hbound := quotient_bound h (h*b) hh js hj xs (hx ▸ heq)
  let W := D*3^M*4^js.length
  have hW : 0<W := by dsimp [W]; positivity
  have hW' : xs.length+1 ≤ 2*W := by change xs.length≤W at hl; omega
  have hle := Nat.mul_le_mul hW' (show h+1≤h*2 by omega)
  have H : h*b < h*(4*D*(3^M*8^js.length)) := calc
    _ < 2^js.length*((xs.length+1)*(h+1)) := hbound
    _ ≤ 2^js.length*(2*W*(h*2)) := Nat.mul_le_mul_left _ hle
    _ = _ := by dsimp only [W]; rw [show (8:ℕ)=2*4 by decide,mul_pow]; ring
  have hpow : 3^M*8^js.length ≤ 2^(17*M) := calc
    _ ≤ 3^M*8^(5*M) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hc)
    _ = (3*8^5)^M := by rw [mul_pow,pow_mul]
    _ ≤ (2^17)^M := Nat.pow_le_pow_left (by decide) M
    _ = 2^(17*M) := (pow_mul _ _ _).symm
  exact (Nat.lt_of_mul_lt_mul_left H).trans_le (Nat.mul_le_mul_left _ hpow)

end Erdos1052.Binary
