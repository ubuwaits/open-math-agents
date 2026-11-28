import Mathlib

-- Credit: @ubuwaits

/-!
# An ordered incidence model avoiding the overlapping grid

For every positive integer m, 16m continuous real graphs with at most one
bend determine at least m² fourfold crossings. Each pair changes order
exactly once, and at most four graphs meet. No injective assignment realizes
the seven-row, ten-column harmonic grid, or even the six specified cells
on fourteen labels. A separate fourteen-point straight-line configuration
realizes these six cells.
-/

/- A family of continuous real graphs with one common bend abscissa.
Every pair changes order at exactly one crossing, and at most four meet at any
point. A square grid gives a quadratic number of fourfold crossings. -/

noncomputable section
namespace Erdos101OneBend

open Finset
open scoped Classical

abbrev Wire (m : ℕ) := Fin 4 × Fin (4*m)

def slope {m} (w : Wire m) : ℝ := w.1.val
def offset {m} (w : Wire m) : ℝ := (w.2.val : ℝ)/(4*m+1)

def graph {m} (w : Wire m) (x : ℝ) : ℝ :=
  slope w*x+offset w-offset w^2*max 0 (x-1)

theorem continuous_graph {m} (w : Wire m) : Continuous (graph w) := by
  unfold graph
  fun_prop

theorem left_eq {m} (w : Wire m) {x : ℝ} (hx : x ≤ 1) :
    graph w x = slope w*x+offset w := by
  simp [graph,max_eq_left (by linarith : x-1 ≤ 0)]

theorem right_eq {m} (w : Wire m) {x : ℝ} (hx : 1 ≤ x) :
    graph w x = (slope w+offset w)+(slope w-offset w^2)*(x-1) := by
  rw [graph,max_eq_right (by linarith : 0 ≤ x-1)]
  ring

private lemma bounds {m} (w : Wire m) : 0 ≤ offset w ∧ offset w < 1 := by
  have h : (w.2.val : ℝ) < 4*(m : ℝ) := by exact_mod_cast w.2.isLt
  have d : (0:ℝ)<4*m+1 := by positivity
  exact ⟨div_nonneg (Nat.cast_nonneg _) d.le,(div_lt_one d).mpr (by linarith)⟩

private lemma offset_inj {m} {u v : Wire m} (h : offset u=offset v) : u.2=v.2 := by
  have d : (4*(m:ℝ)+1) ≠ 0 := by positivity
  unfold offset at h
  have e := (div_left_inj' d).mp h
  apply Fin.ext
  exact_mod_cast e

private lemma sep_right {m} {u v : Wire m} (h : u.1<v.1) {x : ℝ} (hx : 1 ≤ x) :
    graph u x < graph v x := by
  have gap : slope u+1 ≤ slope v := by
    unfold slope
    exact_mod_cast (show u.1.val+1 ≤ v.1.val from h)
  obtain ⟨u₀,u₁⟩ := bounds u
  obtain ⟨v₀,v₁⟩ := bounds v
  have change : 0 ≤ (slope v-offset v^2)-(slope u-offset u^2) := by
    nlinarith [sq_nonneg (offset u),mul_pos (sub_pos.mpr v₁) (by linarith : 0 < 1+offset v)]
  rw [right_eq _ hx,right_eq _ hx]
  nlinarith only [mul_nonneg change (sub_nonneg.mpr hx),gap,u₁,v₀]

def ChangesOnce (f g : ℝ → ℝ) : Prop :=
  ∃ t : ℝ, f t=g t ∧ (∀ x<t, g x<f x) ∧ (∀ x>t, f x<g x)

private lemma different {m} {u v : Wire m} (h : u.1<v.1) :
    ChangesOnce (graph u) (graph v) := by
  have gap : slope u+1 ≤ slope v := by
    unfold slope
    exact_mod_cast (show u.1.val+1 ≤ v.1.val from h)
  have d : 0<slope v-slope u := by linarith
  let t := (offset u-offset v)/(slope v-slope u)
  have eq : t*(slope v-slope u)=offset u-offset v := div_mul_cancel₀ _ d.ne'
  have before : t<1 := (div_lt_one d).mpr (by linarith [(bounds u).2,(bounds v).1])
  refine ⟨t,?_,?_,?_⟩
  · rw [left_eq _ before.le,left_eq _ before.le]
    linarith only [eq]
  · intro x hx
    rw [left_eq _ (hx.trans before).le,left_eq _ (hx.trans before).le]
    nlinarith only [eq,mul_pos (sub_pos.mpr hx) d]
  · intro x hx
    by_cases side : x ≤ 1
    · rw [left_eq _ side,left_eq _ side]
      nlinarith only [eq,mul_pos (sub_pos.mpr hx) d]
    · exact sep_right h (le_of_not_ge side)

private lemma same {m} {u v : Wire m} (hs : u.1=v.1) (hb : offset v<offset u) :
    ChangesOnce (graph u) (graph v) := by
  have eq : slope u=slope v := congrArg (fun a : Fin 4 => (a.val : ℝ)) hs
  have d : 0<offset u+offset v := by linarith [(bounds v).1]
  let t := 1+1/(offset u+offset v)
  have after : 1<t := by dsimp [t]; linarith [one_div_pos.mpr d]
  have prod : (offset u+offset v)*(t-1)=1 := by dsimp [t]; field_simp; ring
  have diff (x : ℝ) (hx : 1 ≤ x) :
      graph u x-graph v x=(offset u-offset v)*
        (1-(offset u+offset v)*(x-1)) := by
    rw [right_eq _ hx,right_eq _ hx,eq]; ring
  refine ⟨t,?_,?_,?_⟩
  · have h := diff t after.le
    rw [prod] at h
    linarith
  · intro x hx
    by_cases side : x ≤ 1
    · rw [left_eq _ side,left_eq _ side,eq]; linarith
    · have sh := diff x (le_of_not_ge side)
      have b : 0<1-(offset u+offset v)*(x-1) := by nlinarith only [prod,mul_pos d (sub_pos.mpr hx)]
      linarith only [sh,mul_pos (sub_pos.mpr hb) b]
  · intro x hx
    have sh := diff x (after.trans hx).le
    have b : 1-(offset u+offset v)*(x-1)<0 := by nlinarith only [prod,mul_pos d (sub_pos.mpr hx)]
    linarith only [sh,mul_neg_of_pos_of_neg (sub_pos.mpr hb) b]

theorem pair_crosses {m} {u v : Wire m} (h : u ≠ v) :
    ChangesOnce (graph u) (graph v) ∨ ChangesOnce (graph v) (graph u) := by
  rcases lt_trichotomy u.1 v.1 with a|a|a
  · exact Or.inl (different a)
  · rcases lt_trichotomy (offset u) (offset v) with b|b|b
    · exact Or.inr (same a.symm b)
    · exact False.elim (h (Prod.ext a (offset_inj b)))
    · exact Or.inl (same a b)
  · exact Or.inr (different a)

def through (m : ℕ) (x y : ℝ) := (Finset.univ : Finset (Wire m)).filter (fun w => graph w x=y)

private lemma same_offset_right {m} {u v : Wire m} {x : ℝ} (side : 1 ≤ x)
    (hs : v.1 = u.1) (hit : graph v x = graph u x) :
    offset v = offset u ∨ (offset v + offset u)*(x-1) = 1 := by
  rw [right_eq _ side,right_eq _ side] at hit
  have e : slope v=slope u := congrArg (fun a : Fin 4 => (a.val : ℝ)) hs
  rw [e] at hit
  have prod : (offset v-offset u)*(1-(offset v+offset u)*(x-1))=0 := by
    linear_combination hit
  rcases mul_eq_zero.mp prod with h|h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linarith)

theorem right_le_two (m : ℕ) {x : ℝ} (hx : 1<x) (y : ℝ) : (through m x y).card ≤ 2 := by
  classical
  by_cases nonempty : (through m x y).Nonempty
  · obtain ⟨u,hu⟩ := nonempty
    have hit {v : Wire m} (hv : v ∈ through m x y) :
        graph v x = graph u x := (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hu).2.symm
    have slope_eq {v : Wire m} (hv : v ∈ through m x y) : v.1=u.1 := by
      rcases lt_trichotomy v.1 u.1 with h|h|h
      · exact False.elim ((sep_right h hx.le).ne (hit hv))
      · exact h
      · exact False.elim ((sep_right h hx.le).ne (hit hv).symm)
    have image : (through m x y).image offset ⊆ {offset u, 1/(x-1)-offset u} := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      rcases same_offset_right hx.le (slope_eq hv) (hit hv) with e|e
      · simp [e]
      · have e' := (eq_div_iff (sub_pos.mpr hx).ne').mpr e
        exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by linarith))
    have inj : (through m x y : Set (Wire m)).InjOn offset := by
      intro v hv w hw e
      exact Prod.ext ((slope_eq hv).trans (slope_eq hw).symm) (offset_inj e)
    have count := Finset.card_le_card image
    rw [Finset.card_image_of_injOn inj] at count
    exact count.trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

theorem through_le_four (m : ℕ) (x y : ℝ) : (through m x y).card ≤ 4 := by
  classical
  by_cases side : x ≤ 1
  · calc (through m x y).card ≤ Fintype.card (Fin 4) := by
           apply Finset.card_le_card_of_injOn (fun w : Wire m => w.1) (by simp)
           intro u hu v hv eq
           have e := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
           rw [left_eq _ side,left_eq _ side] at e
           have s : slope u=slope v := congrArg (fun a : Fin 4 => (a.val : ℝ)) eq
           rw [s] at e
           exact Prod.ext eq (offset_inj (add_left_cancel e))
         _ = 4 := Fintype.card_fin 4
  · exact (right_le_two m (lt_of_not_ge side) y).trans (by decide)

def grid (m i j : ℕ) : ℝ × ℝ := ((i:ℝ)/(4*m+1),((j:ℝ)+3*m)/(4*m+1))

theorem grid_exact {m i j : ℕ} (hi : i < m) (hj : j < m) :
    (through m (grid m i j).1 (grid m i j).2).card = 4 := by
  classical
  let wire (s : Fin 4) : Wire m :=
    (s,⟨j+3*m-s.val*i,by have := s.isLt; omega⟩)
  have term (s : Fin 4) : s.val*i ≤ j+3*m := by
    have := Nat.mul_le_mul (show s.val ≤ 3 by omega) hi.le
    omega
  have denom : (0:ℝ)<4*m+1 := by positivity
  have side : (grid m i j).1 ≤ 1 := (div_le_one denom).mpr (by exact_mod_cast (show i ≤ 4*m+1 by omega))
  have inc : Finset.univ.image wire ⊆ through m (grid m i j).1 (grid m i j).2 := by
    intro w hw
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [left_eq _ side]
    change (s.val:ℝ)*((i:ℝ)/(4*m+1))+(↑(j+3*m-s.val*i):ℝ)/(4*m+1) = ((j:ℝ)+3*m)/(4*m+1)
    rw [Nat.cast_sub (term s)]
    push_cast
    field_simp
    ring
  apply le_antisymm (through_le_four ..)
  have h := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.fst he),Finset.card_univ,Fintype.card_fin] at h
  exact h

theorem quadratic (m : ℕ) : ∃ P : Finset (ℝ × ℝ),
    Fintype.card (Wire m)=16*m ∧ P.card=m^2 ∧
    ∀ p∈P, (through m p.1 p.2).card=4 := by
  classical
  let gridMap (p : Fin m × Fin m) := grid m p.1.val p.2.val
  refine ⟨Finset.univ.image gridMap,by simp [Wire]; omega,?_,?_⟩
  · have d : (4*(m:ℝ)+1)≠0 := by positivity
    have inj : Function.Injective gridMap := by
      intro a b e
      have h := (div_left_inj' d).mp (congrArg Prod.fst e)
      have k := (div_left_inj' d).mp (congrArg Prod.snd e)
      exact Prod.ext (Fin.ext (by exact_mod_cast h)) (Fin.ext (by exact_mod_cast (add_right_cancel k)))
    rw [Finset.card_image_of_injective _ inj]
    simp [pow_two]
  · intro p hp
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
    exact grid_exact a.1.isLt a.2.isLt

end Erdos101OneBend

/- Six crossings from the harmonic grid with labels i, j, i+j, i+2j.
A positive-density family of one-bend pseudolines avoids these six crossings
under every injective relabeling. The proof determines the slope colors from
incidences and then computes the required cross-ratio. -/

noncomputable section
namespace Erdos101SixCrossings
open Finset Erdos101OneBend
open scoped Classical

/-- Rows 0,2,4 have labels 0,1,2. Columns 0,1,2 have labels 3,4,5.
Sum labels 0,2,3,4 become 6,7,8,9 and doubled-column labels 0,2,4,6
become 10,11,12,13. Only the displayed six cells are used. -/
def face : Fin 6 → Fin 4 → Fin 14 :=
  ![![0,3,6,10], ![0,5,7,12], ![1,3,7,11], ![1,4,8,12], ![1,5,9,13], ![2,3,9,12]]

private theorem distinct_slots : ∀ f : Fin 6, Function.Injective (face f) := by decide

private def together (i j : Fin 14) := ∃ f : Fin 6, ∃ a b : Fin 4, a≠b ∧ face f a=i ∧ face f b=j
private instance (i j : Fin 14) : Decidable (together i j) := by unfold together; infer_instance

private lemma palette : ∀ a b c d : Fin 4, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
    ∀ x : Fin 4, x=a ∨ x=b ∨ x=c ∨ x=d := by decide

def nonharmonic (s : Fin 4 → ℝ) := ∀ a b c d : Fin 4,
  a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
  2*(s b-s d)*(s c-s a)-(s d-s a)*(s b-s c)≠0

theorem integer_slopes_nonharmonic : nonharmonic (fun i : Fin 4 => (i.val : ℝ)) := by
  have tab : ∀ a b c d : Fin 4, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
      2*((b.val:ℤ)-d.val)*((c.val:ℤ)-a.val)-((d.val:ℤ)-a.val)*((b.val:ℤ)-c.val)≠0 := by decide
  intro a b c d ab ac ad bc bd cd
  let H : ℤ := 2*((b.val:ℤ)-d.val)*((c.val:ℤ)-a.val)-((d.val:ℤ)-a.val)*((b.val:ℤ)-c.val)
  have hH : H≠0 := tab a b c d ab ac ad bc bd cd
  have realNe : (H:ℝ)≠0 := Int.cast_ne_zero.mpr hH
  dsimp only [H] at realNe
  push_cast at realNe
  exact realNe

theorem forces_harmonic (k : Fin 14 → Fin 4) (v : Fin 14 → ℝ) (s : Fin 4 → ℝ)
    (distinct : Function.Injective (fun i => (k i,v i)))
    (colors : ∀ f, Function.Injective (fun t => k (face f t)))
    (hits : ∀ f : Fin 6, ∃ x y : ℝ, ∀ t : Fin 4,
      s (k (face f t))*x+v (face f t)=y) : ¬nonharmonic s := by
  have diff (i j : Fin 14) (h : together i j) : k i≠k j := by
    obtain ⟨f,a,b,ne,rfl,rfl⟩ := h
    exact fun e => ne (colors f e)
  have choices := palette (k 0) (k 3) (k 7) (k 12)
    (diff 0 3 (by decide)) (diff 0 7 (by decide)) (diff 0 12 (by decide))
    (diff 3 7 (by decide)) (diff 3 12 (by decide)) (diff 7 12 (by decide))
  have b : k 5=k 3 := by
    have h₀ := diff 5 0 (by decide)
    have h₇ := diff 5 7 (by decide)
    have hd := diff 5 12 (by decide)
    rcases choices (k 5) with h|h|h|h <;> tauto
  have p : k 1=k 0 := by
    have h₃ := diff 1 3 (by decide)
    have h₇ := diff 1 7 (by decide)
    have hd := diff 1 12 (by decide)
    rcases choices (k 1) with h|h|h|h <;> tauto
  have c : k 9=k 7 := by
    have h₀ := diff 9 1 (by decide)
    have h₃ := diff 9 5 (by decide)
    have hd := diff 9 12 (by decide)
    rw [p] at h₀; rw [b] at h₃
    rcases choices (k 9) with h|h|h|h <;> tauto
  have q : k 2=k 0 := by
    have h₃ := diff 2 3 (by decide)
    have h₇ := diff 2 9 (by decide)
    have hd := diff 2 12 (by decide)
    rw [c] at h₇
    rcases choices (k 2) with h|h|h|h <;> tauto
  let mix (i j l : Fin 14) :=
    (s (k j)-s (k i))*v l=(s (k j)-s (k l))*v i+(s (k l)-s (k i))*v j
  have mix_face (f : Fin 6) (t : Fin 4) : mix (face f 0) (face f 1) (face f t) := by
    obtain ⟨x,y,h⟩ := hits f
    dsimp only [mix]
    linear_combination (s (k (face f 1))-s (k (face f 0)))*(h t) -
      (s (k (face f 1))-s (k (face f t)))*(h 0) -
      (s (k (face f t))-s (k (face f 0)))*(h 1)
  have e₁ : mix 0 5 7 := mix_face 1 2
  have e₂ : mix 1 3 7 := mix_face 2 2
  have e₃ : mix 1 5 9 := mix_face 4 2
  have e₄ : mix 2 3 9 := mix_face 5 2
  have e₅ : mix 0 5 12 := mix_face 1 3
  have e₆ : mix 2 3 12 := mix_face 5 3
  simp only [mix,b,p,c,q] at e₁ e₂ e₃ e₄ e₅ e₆
  have vanishes :
      (2*(s (k 3)-s (k 12))*(s (k 7)-s (k 0))-
        (s (k 12)-s (k 0))*(s (k 3)-s (k 7)))*(v 5-v 3)=0 := by
    linear_combination (s (k 3)-s (k 12))*(e₂-e₁+e₄-e₃) -
      (s (k 3)-s (k 7))*(e₆-e₅)
  intro nh
  have coeff := nh (k 0) (k 3) (k 7) (k 12) (diff 0 3 (by decide)) (diff 0 7 (by decide))
    (diff 0 12 (by decide)) (diff 3 7 (by decide)) (diff 3 12 (by decide)) (diff 7 12 (by decide))
  have eq := sub_eq_zero.mp ((mul_eq_zero.mp vanishes).resolve_left coeff)
  exact (by decide : (5 : Fin 14)≠3) (distinct (Prod.ext b eq))

/-- No uncolored copy of the six indicated harmonic-grid cells occurs anywhere
in the one-bend example, including outside the designated rich square. -/
theorem no_six {m : ℕ} (w : Fin 14 ↪ Wire m) :
    ¬∀ f : Fin 6, ∃ x y : ℝ, ∀ t : Fin 4, graph (w (face f t)) x=y := by
  intro hits
  let k (i : Fin 14) := (w i).1
  let v (i : Fin 14) := offset (w i)
  have inj : Function.Injective (fun i => (k i,v i)) := by
    intro a b e
    have off : offset (w a)=offset (w b) := congrArg Prod.snd e
    have den : (4*(m:ℝ)+1)≠0 := by positivity
    have same := (div_left_inj' den).mp off
    have kEq : k a=k b := congrArg (fun t : Fin 4 × ℝ => t.1) e
    exact w.injective (Prod.ext kEq (Fin.ext (by exact_mod_cast same)))
  have straight (f : Fin 6) : ∃ x y : ℝ, ∀ t : Fin 4,
      ((k (face f t)).val:ℝ)*x+v (face f t)=y := by
    obtain ⟨x,y,h⟩ := hits f
    have mapinj : Function.Injective (fun t => w (face f t)) := w.injective.comp (distinct_slots f)
    have sub : Finset.univ.image (fun t => w (face f t)) ⊆ through m x y := by
      intro z hz
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h t⟩
    have low := Finset.card_le_card sub
    rw [Finset.card_image_of_injective _ mapinj,Finset.card_univ,Fintype.card_fin] at low
    have left : x≤1 := by
      by_contra! right
      have := right_le_two m right y
      omega
    exact ⟨x,y,fun t => (left_eq _ left).symm.trans (h t)⟩
  have colors (f : Fin 6) : Function.Injective (fun t => k (face f t)) := by
    obtain ⟨x,y,h⟩ := straight f
    intro t u eq
    have ht := h t; have hu := h u
    change k (face f t)=k (face f u) at eq
    rw [eq] at ht
    exact distinct_slots f (inj (Prod.ext eq (add_left_cancel (ht.trans hu.symm))))
  exact forces_harmonic k v _ inj colors straight integer_slopes_nonharmonic


/-- These are the same four label ranges as the seven-row, ten-column
overlapping grid for straight lines. -/
def largeCell (i : Fin 9) (j : Fin 10) : Fin 4 → Fin 64 :=
  ![⟨i.val,by omega⟩,⟨9+j.val,by omega⟩,⟨19+i.val+j.val,by omega⟩,
    ⟨37+i.val+2*j.val,by omega⟩]

private def labels : Fin 14 ↪ Fin 64 :=
  ⟨![0,2,4,9,10,11,19,21,22,23,37,39,41,43],by decide⟩

private def positions : Fin 6 → Fin 9 × Fin 10 :=
  ![(0,0),(0,2),(2,0),(2,1),(2,2),(4,0)]

theorem no_overlapping_grid {m : ℕ} (w : Fin 64 ↪ Wire m) :
    ¬∀ (i : Fin 9) (j : Fin 10), (i.val<5 ∨ i.val%2=0) →
      ∃ x y : ℝ, ∀ t : Fin 4, graph (w (largeCell i j t)) x=y := by
  intro hits
  apply no_six (labels.trans w)
  intro f
  have active : ∀ f : Fin 6, (positions f).1.val<5 := by decide
  obtain ⟨x,y,h⟩ := hits (positions f).1 (positions f).2 (Or.inl (active f))
  have same : ∀ (f : Fin 6) (t : Fin 4),
      labels (face f t)=largeCell (positions f).1 (positions f).2 t := by decide
  exact ⟨x,y,fun t => by change graph (w (labels (face f t))) x=y; rw [same]; exact h t⟩

/-- Arbitrarily large families with crossing density at least 1/256 avoid
even six cells of the earlier overlapping-grid obstruction. -/
theorem dense_and_avoids (m : ℕ) : ∃ P : Finset (ℝ × ℝ),
    Fintype.card (Wire m)=16*m ∧ P.card=m^2 ∧
    (∀ p∈P, (through m p.1 p.2).card=4) ∧
    (∀ x y : ℝ, (through m x y).card≤4) ∧
    (∀ u v : Wire m, u≠v → ChangesOnce (graph u) (graph v) ∨ ChangesOnce (graph v) (graph u)) ∧
    ∀ w : Fin 14 ↪ Wire m, ¬∀ f : Fin 6, ∃ x y : ℝ, ∀ t : Fin 4, graph (w (face f t)) x=y := by
  obtain ⟨P,size,points,hits⟩ := quadratic m
  exact ⟨P,size,points,hits,through_le_four m,fun _ _ ne => pair_crosses ne,no_six⟩

/-- A straight-line realization of the six smaller cells. The four columns
have 3, 3, 4 and 4 points. The larger overlapping grid is a separate condition. -/
private def X : Fin 14 → ℕ := ![0,0,0,6,6,6,2,2,2,2,3,3,3,3]
private def Y : Fin 14 → ℕ := ![0,12,24,0,12,24,0,8,12,16,0,6,12,18]
def realPoints : Fin 14 ↪ ℝ × ℝ where
  toFun i := ((X i:ℝ),(Y i:ℝ))
  inj' := by
    intro i j h
    have rx : (X i:ℝ)=X j := congrArg Prod.fst h
    have ry : (Y i:ℝ)=Y j := congrArg Prod.snd h
    have ix : X i=X j := by exact_mod_cast rx
    have iy : Y i=Y j := by exact_mod_cast ry
    exact (by decide : Function.Injective (fun i : Fin 14 => (X i,Y i))) (Prod.ext ix iy)

theorem real_model_cap (a b c : ℝ) (proper : a≠0 ∨ b≠0) :
    (Finset.univ.filter (fun i : Fin 14 => a*(realPoints i).1+b*(realPoints i).2=c)).card≤4 := by
  let H := Finset.univ.filter (fun i : Fin 14 => a*(realPoints i).1+b*(realPoints i).2=c)
  by_cases nonempty : H.Nonempty
  · obtain ⟨i,hi⟩ := nonempty
    by_cases hb : b=0
    · have ha := proper.resolve_right (not_not.mpr hb)
      have sub : H⊆Finset.univ.filter (fun j => X j=X i) := by
        intro j hj
        have hit := (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hi).2.symm
        change a*(X j:ℝ)+b*(Y j:ℝ)=a*(X i:ℝ)+b*(Y i:ℝ) at hit
        rw [hb] at hit
        have eq : a*(X j:ℝ)=a*(X i:ℝ) := by simpa only [zero_mul,add_zero] using hit
        have same := mul_left_cancel₀ ha eq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by exact_mod_cast same⟩
      exact (Finset.card_le_card sub).trans ((by decide : ∀ i : Fin 14, (Finset.univ.filter (fun j => X j=X i)).card≤4) i)
    · have inj : (H : Set (Fin 14)).InjOn X := by
        intro j hj k hk eq
        have hit := (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm
        change a*(X j:ℝ)+b*(Y j:ℝ)=a*(X k:ℝ)+b*(Y k:ℝ) at hit
        rw [eq] at hit
        have same := mul_left_cancel₀ hb (add_left_cancel hit)
        have tab : Function.Injective (fun j : Fin 14 => (X j,Y j)) := by decide
        exact tab (Prod.ext eq (by exact_mod_cast same))
      have sub : H.image X⊆Finset.univ.image X := Finset.image_subset_image (Finset.subset_univ H)
      have h := Finset.card_le_card sub
      rw [Finset.card_image_of_injOn inj] at h
      exact h.trans (by decide)
  · change H.card≤4
    simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

theorem real_model_hits (f : Fin 6) : ∃ a b : ℝ, ∀ t : Fin 4,
    (realPoints (face f t)).2=a*(realPoints (face f t)).1+b := by
  let a : Fin 6 → ℤ := ![0,4,-2,0,2,-4]
  let b : Fin 6 → ℤ := ![0,0,12,12,12,24]
  have tab : ∀ (f : Fin 6) (t : Fin 4),
      (Y (face f t):ℤ)=a f*(X (face f t):ℤ)+b f := by decide
  refine ⟨a f,b f,fun t => ?_⟩
  change (Y (face f t):ℝ)=(a f:ℝ)*(X (face f t):ℝ)+(b f:ℝ)
  exact_mod_cast tab f t

end Erdos101SixCrossings
