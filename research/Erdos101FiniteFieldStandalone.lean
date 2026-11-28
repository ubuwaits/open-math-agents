import Mathlib

/-!
# Four-point lines on two translated parabolas over a finite field

This is a comparison for Erdős problem 101. All affine lines are included.
The field has odd characteristic in the counting results.
-/

noncomputable section

namespace Erdos101FiniteField

open Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

def roots (w : F) : Finset F := univ.filter (fun x => x^2 = w)

@[simp] theorem mem_roots {x w : F} : x ∈ roots w ↔ x^2 = w := by simp [roots]

theorem roots_square (u : F) : roots (u^2) = {u,-u} := by
  ext x
  simp only [mem_roots, sq_eq_sq_iff_eq_or_eq_neg, mem_insert, mem_singleton]

theorem roots_le_two (w : F) : (roots w).card ≤ 2 := by
  by_cases h : (roots w).Nonempty
  · obtain ⟨u,hu⟩ := h
    rw [← mem_roots.mp hu,roots_square]
    exact card_le_two
  · simp [not_nonempty_iff_eq_empty.mp h]

omit [Fintype F] in
private theorem signed_ne (two : (2:F) ≠ 0) {u : F} (hu : u ≠ 0) : u ≠ -u := by
  intro h
  apply mul_ne_zero two hu
  linear_combination h

@[simp] theorem roots_zero : roots (0:F) = {0} := by
  ext x
  simp

theorem roots_one (two : (2:F) ≠ 0) : (roots (1:F)).card = 2 := by
  have eq := roots_square (1:F)
  rw [one_pow] at eq
  rw [eq,card_pair (signed_ne two one_ne_zero)]

theorem roots_two_or_zero (two : (2:F) ≠ 0) {w : F} (hw : w ≠ 0) :
    (roots w).card = 2 ∨ (roots w).card = 0 := by
  by_cases h : (roots w).Nonempty
  · obtain ⟨u,hu⟩ := h
    have eq := mem_roots.mp hu
    have pos : u ≠ 0 := by rintro rfl; simp at eq; exact hw eq.symm
    left
    rw [←eq,roots_square,card_pair (signed_ne two pos)]
  · right
    rw [not_nonempty_iff_eq_empty.mp h,card_empty]

def levels (F : Type*) [Field F] [Fintype F] : Finset F :=
  univ.filter (fun w => (roots w).card=2 ∧ (roots (w-1)).card=2)

def hyperbola (F : Type*) [Field F] [Fintype F] : Finset (F × F) :=
  univ.filter (fun uv => uv.1^2-uv.2^2=1)

omit [Fintype F] in
private theorem factors {u v : F} (h : u^2-v^2=1) : (u+v)*(u-v)=1 := by
  linear_combination h

theorem hyperbola_card (two : (2:F) ≠ 0) : (hyperbola F).card+1=Fintype.card F := by
  let f (uv : F × F) := uv.1+uv.2
  have inj : Set.InjOn f (hyperbola F : Set (F × F)) := by
    rintro ⟨u,v⟩ huv ⟨a,b⟩ hab he
    change u+v=a+b at he
    have h₁ := factors (mem_filter.mp huv).2
    have h₂ := factors (mem_filter.mp hab).2
    have nz : u+v≠0 := left_ne_zero_of_mul (h₁.trans_ne one_ne_zero)
    rw [←he] at h₂
    have e := mul_left_cancel₀ nz (h₁.trans h₂.symm)
    apply Prod.ext
    · apply mul_left_cancel₀ two; linear_combination he+e
    · apply mul_left_cancel₀ two; linear_combination he-e
  have imageEq : (hyperbola F).image f = (univ : Finset F).erase 0 := by
    ext r
    constructor
    · intro hr
      obtain ⟨⟨u,v⟩,huv,rfl⟩ := mem_image.mp hr
      exact mem_erase.mpr ⟨left_ne_zero_of_mul ((factors (mem_filter.mp huv).2).trans_ne one_ne_zero),mem_univ _⟩
    · intro hr
      have nr := (mem_erase.mp hr).1
      let u := (r+r⁻¹)/2
      let v := (r-r⁻¹)/2
      have plus : u+v=r := by dsimp [u,v]; field_simp; ring
      have minus : u-v=r⁻¹ := by dsimp [u,v]; field_simp; ring
      refine mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨mem_univ _,?_⟩,plus⟩
      change u^2-v^2=1
      calc _ = (u+v)*(u-v) := by ring
           _ = 1 := by rw [plus,minus,mul_inv_cancel₀ nr]
  have eqCard := congrArg Finset.card imageEq
  rw [card_image_of_injOn inj] at eqCard
  rw [eqCard,card_erase_add_one (mem_univ (0:F)),card_univ]

private theorem fiber_eq (w : F) :
    (hyperbola F).filter (fun z => z.1^2=w) = roots w ×ˢ roots (w-1) := by
  ext ⟨u,v⟩
  simp only [hyperbola,mem_filter,mem_univ,true_and,mem_product,mem_roots]
  constructor
  · rintro ⟨h,h'⟩; exact ⟨h',by linear_combination h'-h⟩
  · rintro ⟨hu,hv⟩; exact ⟨by linear_combination hu-hv,hu⟩

private theorem root_product (two : (2:F) ≠ 0) (w : F) :
    (roots w).card*(roots (w-1)).card =
      (if w∈levels F then 4 else 0) +
      (if w=0 then (roots (-1:F)).card else 0) + (if w=1 then 2 else 0) := by
  by_cases zero : w=0
  · subst w; simp [levels]
  by_cases one : w=1
  · subst w; simp [levels,roots_one two]
  rw [if_neg zero,if_neg one,add_zero,add_zero]
  rcases roots_two_or_zero two zero with a|a <;>
    rcases roots_two_or_zero two (sub_ne_zero.mpr one) with b|b <;> simp [levels,a,b]

/-- For a field of order q, four times the number of square levels equals
q minus three minus the number of square roots of minus one. -/
theorem level_count (two : (2:F) ≠ 0) :
    4*(levels F).card+3+(roots (-1:F)).card=Fintype.card F := by
  have parts : (hyperbola F).card = ∑ w : F, (roots w).card*(roots (w-1)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=fun z : F × F => z.1^2) (t:=(univ : Finset F))
      (s:=hyperbola F) (fun _ _ => mem_univ _)]
    exact sum_congr rfl (fun w _ => by rw [fiber_eq,card_product])
  have count := hyperbola_card two
  rw [parts] at count
  simp_rw [root_product two] at count
  simp only [Finset.sum_add_distrib] at count
  have memsum : (∑ w : F, if w∈levels F then 4 else 0) = (levels F).card*4 := by
    rw [←Finset.sum_filter]; simp
  rw [memsum] at count
  simp at count
  omega

def pt (t x : F) : F × F := (x,x^2+t)

def layer (t : F) : Finset (F × F) := univ.image (pt t)

def configuration (F : Type*) [Field F] [Fintype F] := layer (0:F) ∪ layer (1:F)

private theorem layer_mem (t : F) (p : F × F) : p ∈ layer t ↔ p.2=p.1^2+t := by
  constructor
  · rintro hp
    obtain ⟨x,_,rfl⟩ := mem_image.mp hp
    rfl
  · intro h
    exact mem_image.mpr ⟨p.1,mem_univ _,Prod.ext rfl h.symm⟩

private theorem layers_disjoint : Disjoint (layer (0:F)) (layer (1:F)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have a := (layer_mem _ _).mp hp
  have b := (layer_mem _ _).mp hq
  exact one_ne_zero (by linear_combination a-b)

theorem configuration_card : (configuration F).card=2*Fintype.card F := by
  have each (t:F) : (layer t).card=Fintype.card F := by
    rw [layer,card_image_of_injOn (fun _ _ _ _ h => congrArg Prod.fst h),card_univ]
  rw [configuration,card_union_of_disjoint layers_disjoint,each,each,two_mul]

def incident (L : AffineSubspace F (F × F)) := (configuration F).filter (fun p => p∈L)

def graphLine (m c : F) := line[F,((0,c) : F×F),(1,m+c)]

omit [Fintype F] in
theorem graph_mem (m c : F) (p : F×F) : p ∈ graphLine m c ↔ p.2=m*p.1+c := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
    have hx := congrArg Prod.fst ht
    have hy := congrArg Prod.snd ht
    simp [AffineMap.lineMap_apply_module] at hx hy
    linear_combination m*hx-hy
  · intro h
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨p.1,Prod.ext ?_ ?_⟩
    · simp [AffineMap.lineMap_apply_module]
    · simp [AffineMap.lineMap_apply_module]
      linear_combination -h

/-- Reparametrize a nonvertical line by its slope divided by two and its
completed-square value on the lower parabola. -/
def secant (h w : F) := graphLine (2*h) (w-h^2)

private theorem layer_hits (t h w : F) :
    ((layer t).filter (fun p => p∈secant h w)).card = (roots (w-t)).card := by
  let embed (u : F) := pt t (h+u)
  have eq : (layer t).filter (fun p => p∈secant h w) = (roots (w-t)).image embed := by
    ext p
    constructor
    · intro hp
      obtain ⟨inLayer,onLine⟩ := mem_filter.mp hp
      have a := (layer_mem _ _).mp inLayer
      have b := (graph_mem _ _ _).mp onLine
      refine mem_image.mpr ⟨p.1-h,mem_roots.mpr (by linear_combination b-a),?_⟩
      dsimp [embed,pt]; rw [add_sub_cancel]; exact Prod.ext rfl a.symm
    · intro hp
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hp
      refine mem_filter.mpr ⟨mem_image.mpr ⟨h+u,mem_univ _,rfl⟩,(graph_mem _ _ _).mpr ?_⟩
      change (h+u)^2+t = 2*h*(h+u)+(w-h^2)
      linear_combination mem_roots.mp hu
  rw [eq,card_image_of_injOn]
  intro u _ v _ e
  exact add_left_cancel (show h+u=h+v from congrArg Prod.fst e)

theorem secant_count (h w : F) :
    (incident (secant h w)).card=(roots w).card+(roots (w-1)).card := by
  rw [incident,configuration,Finset.filter_union,card_union_of_disjoint,layer_hits,layer_hits,sub_zero]
  exact Disjoint.mono (filter_subset ..) (filter_subset ..) layers_disjoint

private theorem vertical_bound {p q : F × F} (same : p.1=q.1) :
    (incident (line[F,p,q])).card ≤ 2 := by
  have bound : incident (line[F,p,q]) ⊆ {pt 0 p.1,pt 1 p.1} := by
    intro z hz
    obtain ⟨cfg,onLine⟩ := mem_filter.mp hz
    obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp onLine
    have hx := congrArg Prod.fst ht
    simp [AffineMap.lineMap_apply_module,←same] at hx
    have x : p.1=z.1 := by linear_combination hx
    rcases mem_union.mp cfg with bot|top
    · exact mem_insert.mpr (Or.inl (Prod.ext x.symm (by rw [layer_mem] at bot; simpa [pt,x] using bot)))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext x.symm (by rw [layer_mem] at top; simpa [pt,x] using top))))
  exact (card_le_card bound).trans card_le_two

omit [Fintype F] in
private theorem nonvertical {p q : F × F} (different : p.1≠q.1) (two : (2:F)≠0) :
    ∃h w : F, line[F,p,q]=secant h w := by
  let m := (q.2-p.2)/(q.1-p.1)
  let c := p.2-m*p.1
  have sm : m*(q.1-p.1)=q.2-p.2 := div_mul_cancel₀ _ (sub_ne_zero.mpr different.symm)
  have onP : p∈graphLine m c := (graph_mem ..).mpr (by dsimp [c]; ring)
  have onQ : q∈graphLine m c := (graph_mem ..).mpr (by dsimp [c]; linear_combination -sm)
  refine ⟨m/2,c+(m/2)^2,?_⟩
  rw [secant,add_sub_cancel_right,show 2*(m/2)=m from by field_simp]
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne onP onQ (fun h => different (congrArg Prod.fst h))

theorem no_five (two : (2:F)≠0) (p q : F×F) : (incident (line[F,p,q])).card ≤ 4 := by
  by_cases e : p.1=q.1
  · exact (vertical_bound e).trans (by decide)
  obtain ⟨h,w,eq⟩ := nonvertical e two
  rw [eq,secant_count]
  exact Nat.add_le_add (roots_le_two _) (roots_le_two _)

def fourLines (F : Type*) [Field F] [Fintype F] : Finset (AffineSubspace F (F × F)) :=
  ((univ : Finset F) ×ˢ levels F).image (fun hw => secant hw.1 hw.2)

theorem all_four (two : (2:F)≠0) (p q : F×F) :
    line[F,p,q] ∈ fourLines F ↔ (incident (line[F,p,q])).card=4 := by
  constructor
  · intro h
    obtain ⟨⟨a,w⟩,hw,eq⟩ := mem_image.mp h
    obtain ⟨r,s⟩ := (mem_filter.mp (mem_product.mp hw).2).2
    rw [←eq,secant_count,r,s]
  · intro h
    have diff : p.1≠q.1 := by
      intro same; have b := vertical_bound same; omega
    obtain ⟨a,w,eq⟩ := nonvertical diff two
    rw [eq,secant_count] at h
    have b := roots_le_two w
    have c := roots_le_two (w-1)
    have both : (roots w).card=2 ∧ (roots (w-1)).card=2 := ⟨by omega,by omega⟩
    exact mem_image.mpr ⟨(a,w),mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,both⟩⟩,eq.symm⟩

theorem four_card (two : (2:F)≠0) : (fourLines F).card=Fintype.card F*(levels F).card := by
  rw [fourLines,card_image_of_injOn,card_product,card_univ]
  rintro ⟨h,w⟩ _ ⟨k,v⟩ _ e
  change secant h w=secant k v at e
  have first : (0,w-h^2)∈secant k v := e ▸ left_mem_affineSpan_pair ..
  have second : (1,2*h+(w-h^2))∈secant k v := e ▸ right_mem_affineSpan_pair ..
  have a := (graph_mem _ _ _).mp first
  have b := (graph_mem _ _ _).mp second
  simp at a b
  have hk : h=k := by apply mul_left_cancel₀ two; linear_combination b-a
  exact Prod.ext hk (by rw [hk] at a; linear_combination a)

theorem exact_count (two : (2:F)≠0) :
    4*(fourLines F).card + Fintype.card F*(3+(roots (-1:F)).card)=(Fintype.card F)^2 := by
  rw [four_card two]
  calc _ = Fintype.card F*(4*(levels F).card+3+(roots (-1:F)).card) := by ring
       _ = _ := by rw [level_count two,pow_two]

/-- For every prime p >= 11 the 2p-point configuration has at least
(2p)^2/32 distinct exactly-four lines. -/
theorem prime_density (p : ℕ) [Fact p.Prime] (large : 11 ≤ p) :
    (configuration (ZMod p)).card^2 ≤ 32*(fourLines (ZMod p)).card := by
  have two : (2:ZMod p)≠0 := by
    intro h
    have dvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have le := Nat.le_of_dvd (by decide : 0<2) dvd
    omega
  have h := level_count two
  rw [ZMod.card] at h
  have bound := roots_le_two (-1:ZMod p)
  have ratio : p ≤ 8*(levels (ZMod p)).card := by omega
  rw [configuration_card,four_card two,ZMod.card]
  calc (2*p)^2 = (4*p)*p := by ring
       _ ≤ (4*p)*(8*(levels (ZMod p)).card) := Nat.mul_le_mul_left _ ratio
       _ = _ := by ring

end Erdos101FiniteField
