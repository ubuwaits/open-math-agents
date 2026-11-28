import OMAReductions.R_Erdos101_erdos_101_R3
import Mathlib

-- Credit: @ubuwaits

/-!
# Extracting a configuration from square-root many anchors

First retain a core with large minimum degree. Color its points independently
and use one color as the anchors. At each point, pairs on distinct incident
lines are disjoint. A second-moment estimate supplies one anchor set for
which few points fail to have two pairs. Delete the affected four-point
lines and retain all four original points on each remaining line.
-/

noncomputable section
namespace Erdos101AnchorGeometry
open EuclideanGeometry Finset
open scoped Classical

abbrev Line := AffineSubspace ℝ ℝ²

def pencil (p : ℝ²) (I : Finset ℝ²) := I.image (fun q => line[ℝ,p,q])

def determined (S : Finset ℝ²) : Finset Line := S.offDiag.image (fun e => line[ℝ,e.1,e.2])
def incident (S : Finset ℝ²) (L : Line) := S.filter (fun p => p∈L)
def mult (S : Finset ℝ²) (L : Line) := (incident S L).card

theorem mem_determined {S : Finset ℝ²} {L : Line} :
    L∈determined S ↔ ∃ a∈S, ∃ b∈S, a≠b ∧ line[ℝ,a,b]=L := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hab,eq⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hb,ne⟩ := Finset.mem_offDiag.mp hab
    exact ⟨a,ha,b,hb,ne,eq⟩
  · rintro ⟨a,ha,b,hb,ne,eq⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_offDiag.mpr ⟨ha,hb,ne⟩,eq⟩

theorem unique_line {S : Finset ℝ²} {L : Line} (hL : L∈determined S) {p q : ℝ²}
    (hp : p∈L) (hq : q∈L) (ne : p≠q) : line[ℝ,p,q]=L := by
  obtain ⟨_,_,_,_,_,rfl⟩ := mem_determined.mp hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq ne

private theorem through_insert {I S : Finset ℝ²} {p : ℝ²} (sub : I⊆S) (ps : p∈S) (new : p∉I) :
    (determined S).filter (fun L => p∈L ∧ (incident I L).Nonempty) = pencil p I := by
  ext L
  constructor
  · intro h
    obtain ⟨ld,pl,q,hq⟩ := Finset.mem_filter.mp h
    obtain ⟨qi,ql⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_image.mpr ⟨q,qi,unique_line ld pl ql (fun e => new (e ▸ qi))⟩
  · intro h
    obtain ⟨q,qi,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨mem_determined.mpr ⟨p,ps,q,sub qi,fun e => new (e ▸ qi),rfl⟩,
      left_mem_affineSpan_pair ..,q,Finset.mem_filter.mpr ⟨qi,right_mem_affineSpan_pair ..⟩⟩

theorem full_pencil {S : Finset ℝ²} {p : ℝ²} (ps : p∈S) :
    pencil p (S.erase p)=(determined S).filter (fun L => p∈L) := by
  rw [← through_insert (Finset.erase_subset ..) ps (Finset.notMem_erase p S)]
  apply Finset.filter_congr
  intro L hl
  constructor
  · exact And.left
  · intro pl
    obtain ⟨a,ha,b,hb,ne,rfl⟩ := mem_determined.mp hl
    refine ⟨pl,?_⟩
    by_cases e : a=p
    · exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun eq => ne (e.trans eq.symm),hb⟩,
        right_mem_affineSpan_pair ..⟩⟩
    · exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨e,ha⟩,left_mem_affineSpan_pair ..⟩⟩

def count (S : Finset ℝ²) (k : ℕ) := ((determined S).filter (fun L => mult S L=k)).card

theorem count_eq (S : Finset ℝ²) (k : ℕ) : count S k=(linesWithPointsFor k (S : Set ℝ²)).ncard := by
  have eq : (↑((determined S).filter (fun L => mult S L=k)) : Set Line)=linesWithPointsFor k (S : Set ℝ²) := by
    ext L
    have coe : (incident S L : Set ℝ²)=(L : Set ℝ²) ∩ S := by ext p; simp [incident,and_comm]
    simp only [Finset.mem_coe,Finset.mem_filter,mem_determined,linesWithPointsFor,Set.mem_ofPred_eq,
      mult,← Set.ncard_coe_finset,coe]
    simp [exists_prop]
  rw [← eq,Set.ncard_coe_finset,count]

end Erdos101AnchorGeometry

/- Sampling a common set of anchors. Disjoint pairs on the lines through
one point give pairwise independent events. A second-moment bound controls
the number of points with fewer than two available lines. -/
noncomputable section
namespace Erdos101AnchorSampling
open Finset
open scoped BigOperators Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def anchors {k : ℕ} [NeZero k] (c : α → Fin k) := Finset.univ.filter (fun a => c a=0)
def indicator {k : ℕ} [NeZero k] (T : Finset α) (c : α → Fin k) : ℝ :=
  if T⊆anchors c then 1 else 0

private theorem fixed_count {k : ℕ} [NeZero k] (T : Finset α) :
    (Finset.univ.filter (fun c : α → Fin k => T⊆anchors c)).card=k^(Fintype.card α-T.card) := by
  let P (a : α) : Finset (Fin k) := if a∈T then {0} else Finset.univ
  have eq : Finset.univ.filter (fun c : α → Fin k => T⊆anchors c)=Fintype.piFinset P := by
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro sub a
      by_cases h : a∈T
      · simpa [P,h] using (Finset.mem_filter.mp (sub h)).2
      · simp [P,h]
    · intro all a h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [P,h] using all a⟩
  rw [eq,Fintype.card_piFinset]
  have split := Finset.prod_sdiff (f:=fun a => (P a).card) (Finset.subset_univ T)
  rw [← split]
  have a : (∏ i∈T, (P i).card)=1 := Finset.prod_eq_one (fun i hi => by simp [P,hi])
  have b : ∀ i∈Finset.univ\T, (P i).card=k := fun i hi => by simp [P,(Finset.mem_sdiff.mp hi).2]
  rw [a,mul_one,Finset.prod_congr rfl b]
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ T)]

theorem mean_indicator {k : ℕ} [NeZero k] (T : Finset α) :
    (𝔼 c : α → Fin k, indicator T c)=1/(k:ℝ)^T.card := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [indicator,Finset.sum_boole,fixed_count,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  have le := Finset.card_le_univ T
  have eq : Fintype.card α=Fintype.card α-T.card+T.card := (Nat.sub_add_cancel le).symm
  nth_rw 2 [eq]
  rw [pow_add]
  have pos : 0<(k:ℝ) := by exact_mod_cast NeZero.pos k
  field_simp

private theorem multiply {k : ℕ} [NeZero k] (A B : Finset α) (c : α → Fin k) :
    indicator A c*indicator B c=indicator (A∪B) c := by
  by_cases ha : A⊆anchors c <;> by_cases hb : B⊆anchors c <;> simp [indicator,Finset.union_subset_iff,ha,hb]

def hits {k : ℕ} [NeZero k] (B : Finset (Finset α)) (c : α → Fin k) :=
  (B.filter (fun T => T⊆anchors c)).card

private theorem sum_indicator {k : ℕ} [NeZero k] (B : Finset (Finset α)) (c : α → Fin k) :
    (∑ T∈B, indicator T c)=(hits B c:ℝ) := by simp [indicator,hits]

private theorem centered {k : ℕ} [NeZero k] {A B : Finset α} (ha : A.card=2) (hb : B.card=2) :
    (𝔼 c : α → Fin k, (indicator A c-1/(k:ℝ)^2)*(indicator B c-1/(k:ℝ)^2)) =
      1/(k:ℝ)^(A∪B).card-(1/(k:ℝ)^2)^2 := by
  let a := 1/(k:ℝ)^2
  have expand (c : α → Fin k) : (indicator A c-a)*(indicator B c-a) =
      (indicator (A∪B) c-indicator A c*a)-a*indicator B c+a*a := by rw [← multiply]; ring
  change (𝔼 c : α → Fin k, (indicator A c-a)*(indicator B c-a))=_
  simp_rw [expand]
  rw [Finset.expect_add_distrib,Finset.expect_sub_distrib,Finset.expect_sub_distrib,
    ← Finset.expect_mul,← Finset.mul_expect,Fintype.expect_const,mean_indicator,mean_indicator,
    mean_indicator,ha,hb]
  dsimp [a]; ring

theorem variance_bound {k : ℕ} [NeZero k] (B : Finset (Finset α))
    (two : ∀ T∈B,T.card=2) (dis : (B : Set (Finset α)).PairwiseDisjoint id) :
    (𝔼 c : α → Fin k, ((hits B c:ℝ)-(B.card:ℝ)/(k:ℝ)^2)^2) ≤ (B.card:ℝ)/(k:ℝ)^2 := by
  let a := 1/(k:ℝ)^2
  have expand (c : α → Fin k) :
      ((hits B c:ℝ)-(B.card:ℝ)/(k:ℝ)^2)^2 =
        ∑ T∈B, ∑ U∈B, (indicator T c-a)*(indicator U c-a) := by
    rw [← Finset.sum_mul_sum]
    have sub : (∑ T∈B, (indicator T c-a))=(hits B c:ℝ)-(B.card:ℝ)/(k:ℝ)^2 := by
      rw [Finset.sum_sub_distrib,sum_indicator]; simp [a,div_eq_mul_inv]
    rw [sub,pow_two]
  simp_rw [expand,Finset.expect_sum_comm]
  have off (T) (ht : T∈B) (U) (hu : U∈B) (ne : U≠T) :
      (𝔼 c : α → Fin k, (indicator T c-a)*(indicator U c-a))=0 := by
    rw [centered (two T ht) (two U hu),Finset.card_union_of_disjoint (show Disjoint T U from dis ht hu ne.symm),two T ht,two U hu]
    dsimp [a]; ring
  have diag (T) (ht : T∈B) : (𝔼 c : α → Fin k, (indicator T c-a)*(indicator T c-a)) ≤ a := by
    rw [centered (two T ht) (two T ht),Finset.union_idempotent,two T ht]
    exact sub_le_self _ (sq_nonneg _)
  calc (∑ T∈B, ∑ U∈B, 𝔼 c : α → Fin k, (indicator T c-a)*(indicator U c-a)) ≤ ∑ _T∈B, a := by
         apply Finset.sum_le_sum; intro T ht
         rw [Finset.sum_eq_single_of_mem T ht (off T ht)]
         exact diag T ht
       _ = _ := by simp [a,div_eq_mul_inv]

/-- If d disjoint pairs are available, a uniform 1/k sample misses the
two-pair threshold with probability at most 2k²/d. -/
theorem miss_bound {k : ℕ} [NeZero k] (B : Finset (Finset α))
    (two : ∀ T∈B,T.card=2) (dis : (B : Set (Finset α)).PairwiseDisjoint id)
    (degree : 4*k^2 ≤ B.card) :
    (𝔼 c : α → Fin k, if hits B c < 2 then (1:ℝ) else 0) ≤ 2*(k:ℝ)^2/B.card := by
  let mu := (B.card:ℝ)/(k:ℝ)^2
  have kp : 0<(k:ℝ) := by exact_mod_cast NeZero.pos k
  have hm : 4 ≤ mu := (le_div_iff₀ (sq_pos_of_pos kp)).mpr (by exact_mod_cast degree)
  have pos : 0 < mu := by linarith
  have per (c : α → Fin k) : (if hits B c<2 then (1:ℝ) else 0)*(mu^2/2) ≤ ((hits B c:ℝ)-mu)^2 := by
    split_ifs with small
    · have val : (hits B c:ℝ)≤1 := by exact_mod_cast (show hits B c≤1 by omega)
      have b : 3*mu/4 ≤ mu-(hits B c:ℝ) := by linarith
      nlinarith only [sq_nonneg mu,sq_le_sq' (by linarith : -(mu-(hits B c:ℝ)) ≤ 3*mu/4) b]
    · simpa using sq_nonneg ((hits B c:ℝ)-mu)
  have ineq := Finset.expect_le_expect (s:=Finset.univ) (fun c _ => per c)
  rw [← Finset.expect_mul] at ineq
  have h := ineq.trans (variance_bound B two dis)
  have bound : (𝔼 c : α → Fin k, if hits B c<2 then (1:ℝ) else 0) ≤ 2/mu := by
    apply (le_div_iff₀ pos).mpr
    apply le_of_mul_le_mul_right (a:=mu) _ pos
    nlinarith only [h]
  exact bound.trans_eq (by simp [mu,div_eq_mul_inv,mul_comm,mul_assoc])

theorem mean_anchors {k : ℕ} [NeZero k] :
    (𝔼 c : α → Fin k, ((anchors c).card:ℝ))=(Fintype.card α:ℝ)/k := by
  have eq (c : α → Fin k) : ((anchors c).card:ℝ)=∑ p : α, indicator {p} c := by
    simp [indicator,anchors]
  simp_rw [eq,Finset.expect_sum_comm,mean_indicator]
  simp [div_eq_mul_inv]

end Erdos101AnchorSampling

namespace Erdos101AnchorField
open EuclideanGeometry Finset
open scoped Classical

def determinedBy (B : Finset ℝ²) (p : ℝ²) := ∃ a∈B, ∃ b∈B, ∃ c∈B, ∃ d∈B,
  a≠b ∧ c≠d ∧ line[ℝ,a,b]≠line[ℝ,c,d] ∧ p∈line[ℝ,a,b] ∧ p∈line[ℝ,c,d]

end Erdos101AnchorField

/- Simultaneous reconstruction by one round of intersections of joins.
The same random anchors are used for every point and every line. -/
noncomputable section
namespace Erdos101AnchorJoins
open Erdos101AnchorSampling Erdos101AnchorField Erdos101AnchorGeometry EuclideanGeometry Finset
open scoped BigOperators Classical

def sample {k : ℕ} [NeZero k] {U : Finset ℝ²} (color : U → Fin k) : Finset ℝ² :=
  (anchors color).image Subtype.val
def missed (U B : Finset ℝ²) := U.filter (fun p => ¬determinedBy B p)
def star (A : Finset Line) (p : ℝ²) := A.filter (fun L => p∈L)

theorem sample_sub {k : ℕ} [NeZero k] {U : Finset ℝ²} (c : U → Fin k) : sample c⊆U := by
  intro p hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
  exact a.property

theorem sample_card {k : ℕ} [NeZero k] {U : Finset ℝ²} (c : U → Fin k) :
    (sample c).card=(anchors c).card := Finset.card_image_of_injective _ Subtype.val_injective

private theorem pair_at {U : Finset ℝ²} {L : Line} {p : U} (onL : p.val∈L)
    (three : 3 ≤ mult U L) :
    ∃ T : Finset U, T.card=2 ∧ ∀ t∈T, t≠p ∧ t.val∈L := by
  let I := (incident U L).erase p.val
  have many : 1<I.card := by
    have h : ((incident U L).erase p.val).card=(incident U L).card-1 :=
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨p.property,onL⟩)
    change 1<((incident U L).erase p.val).card
    change 3≤(incident U L).card at three
    omega
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp many
  obtain ⟨ap,am⟩ := Finset.mem_erase.mp ha
  obtain ⟨bp,bm⟩ := Finset.mem_erase.mp hb
  obtain ⟨au,al⟩ := Finset.mem_filter.mp am
  obtain ⟨bu,bl⟩ := Finset.mem_filter.mp bm
  let a' : U := ⟨a,au⟩
  let b' : U := ⟨b,bu⟩
  have ne' : a'≠b' := fun e => ne (congrArg Subtype.val e)
  refine ⟨{a',b'},Finset.card_pair ne',?_⟩
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl|h
  · exact ⟨fun e => ap (congrArg Subtype.val e),al⟩
  · obtain rfl := Finset.mem_singleton.mp h
    exact ⟨fun e => bp (congrArg Subtype.val e),bl⟩

theorem pair_family {S U : Finset ℝ²} {A : Finset Line} (proper : A⊆determined S)
    (three : ∀ L∈A,3 ≤ mult U L) (p : U) :
    ∃ B : Finset (Finset U), B.card=(star A p.val).card ∧
      (∀T∈B,T.card=2) ∧ (B : Set (Finset U)).PairwiseDisjoint id ∧
      ∀ {k : ℕ} [NeZero k] (c : U → Fin k), 2≤hits B c → determinedBy (sample c) p.val := by
  classical
  let H := star A p.val
  have properties (L : H) := Finset.mem_filter.mp L.property
  choose mask size data using fun L : H => pair_at (p:=p) (properties L).2 (three L.val (properties L).1)
  have dis {L M : H} (ne : L≠M) : Disjoint (mask L) (mask M) := by
    apply Finset.disjoint_left.mpr
    intro w wl wm
    obtain ⟨wp,wL⟩ := data L w wl
    have wM := (data M w wm).2
    have sep : p.val≠w.val := fun e => wp (Subtype.ext e.symm)
    exact ne (Subtype.ext ((unique_line (proper (properties L).1) (properties L).2 wL sep).symm.trans
      (unique_line (proper (properties M).1) (properties M).2 wM sep)))
  have inj : Function.Injective mask := by
    intro L M eq
    by_contra ne
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by rw [size L]; decide)
    exact Finset.disjoint_left.mp (dis ne) hw (eq ▸ hw)
  let B := Finset.univ.image mask
  refine ⟨B,by simp [B,H,Finset.card_image_of_injective _ inj],?_,?_,?_⟩
  · intro T ht
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp ht
    exact size L
  · intro T ht V hv ne
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨M,_,rfl⟩ := Finset.mem_image.mp hv
    exact dis (fun e => ne (congrArg mask e))
  · intro k _ c many
    obtain ⟨T,ht,V,hv,ne⟩ := Finset.one_lt_card.mp many
    obtain ⟨tm,ts⟩ := Finset.mem_filter.mp ht
    obtain ⟨vm,vs⟩ := Finset.mem_filter.mp hv
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp tm
    obtain ⟨M,_,rfl⟩ := Finset.mem_image.mp vm
    have join (J : H) (inside : mask J⊆anchors c) :
        ∃ a∈sample c, ∃ b∈sample c, a≠b ∧ line[ℝ,a,b]=J.val := by
      obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp (show 1<(mask J).card by rw [size J]; decide)
      have diff : u.val≠v.val := fun eq => uv (Subtype.ext eq)
      exact ⟨u.val,Finset.mem_image_of_mem _ (inside hu),v.val,Finset.mem_image_of_mem _ (inside hv),diff,
        unique_line (proper (properties J).1) (data J u hu).2 (data J v hv).2 diff⟩
    obtain ⟨a,ha,b,hb,ab,lab⟩ := join L ts
    obtain ⟨d,hd,e,he,de,lde⟩ := join M vs
    refine ⟨a,ha,b,hb,d,hd,e,he,ab,de,?_,lab ▸ (properties L).2,lde ▸ (properties M).2⟩
    rw [lab,lde]
    exact fun eq => ne (congrArg mask (Subtype.ext eq))

theorem mean_missed {S U : Finset ℝ²} {A : Finset Line} (proper : A⊆determined S)
    (three : ∀ L∈A,3 ≤ mult U L) {k d : ℕ} [NeZero k] (threshold : 4*k^2≤d)
    (minimum : ∀p∈U, d≤(star A p).card) :
    (𝔼 c : U → Fin k, ((missed U (sample c)).card:ℝ)) ≤
        U.card*(2*(k:ℝ)^2/d) := by
  classical
  have hk := NeZero.pos k
  have dp : 0<(d:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0<4*k^2) threshold)
  have point (p : U) : (𝔼 c : U → Fin k, if ¬determinedBy (sample c) p.val then (1:ℝ) else 0)
      ≤ 2*(k:ℝ)^2/d := by
    obtain ⟨B,count,two,dis,good⟩ := pair_family proper three p
    have deg : d≤B.card := count ▸ minimum p.val p.property
    have per (c : U → Fin k) : (if ¬determinedBy (sample c) p.val then (1:ℝ) else 0) ≤
        if hits B c<2 then (1:ℝ) else 0 := by
      by_cases small : hits B c<2
      · simp [small]; split_ifs <;> norm_num
      · simp [small,good c (le_of_not_gt small)]
    apply (Finset.expect_le_expect (fun c _ => per c)).trans
    exact (miss_bound B two dis (threshold.trans deg)).trans
      (div_le_div_of_nonneg_left (by positivity) dp (by exact_mod_cast deg))
  have num (c : U → Fin k) : ((missed U (sample c)).card:ℝ) =
      ∑ p : U, if ¬determinedBy (sample c) p.val then (1:ℝ) else 0 := by
    rw [Finset.sum_boole]
    change _ = ((U.attach.filter (fun p : U => ¬determinedBy (sample c) p.val)).card:ℝ)
    rw [Finset.filter_attach (fun p : ℝ² => ¬determinedBy (sample c) p) U]
    simp [missed]
  simp_rw [num,Finset.expect_sum_comm]
  exact (Finset.sum_le_sum (fun p _ => point p)).trans_eq (by simp)

theorem common_anchors {S U : Finset ℝ²} {A : Finset Line} (proper : A⊆determined S)
    (three : ∀ L∈A,3 ≤ mult U L) {k d : ℕ} [NeZero k] (threshold : 4*k^2≤d)
    (minimum : ∀p∈U, d≤(star A p).card) :
    ∃ B⊆U, k*B.card≤2*U.card ∧ d*(missed U B).card≤4*k^2*U.card := by
  let w := (d:ℝ)/(2*(k:ℝ)^2)
  have kp : 0<(k:ℝ) := by exact_mod_cast NeZero.pos k
  have hk := NeZero.pos k
  have dp : 0<(d:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0<4*k^2) threshold)
  have wp : 0≤w := by dsimp [w]; positivity
  have mean := mean_missed proper three threshold minimum (k:=k)
  have scaled := mul_le_mul_of_nonneg_left mean wp
  have clean : w*(U.card*(2*(k:ℝ)^2/d))=(U.card:ℝ) := by dsimp [w]; field_simp
  rw [clean] at scaled
  have total : (𝔼 c : U → Fin k, ((k:ℝ)*(anchors c).card+w*(missed U (sample c)).card))≤2*U.card := by
    rw [Finset.expect_add_distrib,← Finset.mul_expect,← Finset.mul_expect,mean_anchors]
    simp only [Fintype.card_coe]
    have cancel : (k:ℝ)*(U.card/k)=U.card := by field_simp
    rw [cancel]; linarith
  obtain ⟨c,_,hc⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty total
  refine ⟨sample c,sample_sub c,?_,?_⟩
  · rw [sample_card]
    have a : (k:ℝ)*(anchors c).card ≤ 2*U.card := by linarith only [hc,mul_nonneg wp (Nat.cast_nonneg (missed U (sample c)).card)]
    exact_mod_cast a
  · have b : w*(missed U (sample c)).card ≤ 2*U.card := by linarith only [hc,mul_nonneg kp.le (Nat.cast_nonneg (anchors c).card)]
    have t := mul_le_mul_of_nonneg_left b (show 0≤2*(k:ℝ)^2 by positivity)
    dsimp [w] at t
    have eq : (2*(k:ℝ)^2)*(d/(2*k^2)*(missed U (sample c)).card)=d*(missed U (sample c)).card := by field_simp
    rw [eq] at t
    exact_mod_cast (by linarith only [t] : (d:ℝ)*(missed U (sample c)).card ≤ 4*(k:ℝ)^2*U.card)

end Erdos101AnchorJoins

namespace Erdos101AnchorCore
open Erdos101AnchorGeometry Erdos101AnchorField Erdos101AnchorJoins Erdos101AnchorSampling
open EuclideanGeometry Finset
open scoped BigOperators Classical

def active (r : ℕ) (A : Finset Line) (U : Finset ℝ²) := A.filter (fun L => r ≤ mult U L)

theorem peel (S : Finset ℝ²) (A : Finset Line) (r d : ℕ) (rich : ∀L∈A, r ≤ mult S L) :
    ∃ U⊆S, ∃ F⊆A, (∀L∈F,r ≤ mult U L) ∧
      A.card≤F.card+d*(S.card-U.card) ∧ ∀p∈U, d≤(star F p).card := by
  let score (U : Finset ℝ²) : ℤ := ((active r A U).card:ℤ)-(d:ℤ)*U.card
  obtain ⟨U,us,best⟩ := S.powerset.exists_max_image score ⟨S,Finset.mem_powerset.mpr Finset.Subset.rfl⟩
  have sub := Finset.mem_powerset.mp us
  let F := active r A U
  have init := best S (Finset.mem_powerset.mpr Finset.Subset.rfl)
  have full : active r A S=A := Finset.filter_true_of_mem rich
  dsimp only [score] at init
  rw [full] at init
  refine ⟨U,sub,F,Finset.filter_subset ..,fun L hl => (Finset.mem_filter.mp hl).2,?_,?_⟩
  · have eq := Nat.sub_add_cancel (Finset.card_le_card sub)
    have z : ((S.card-U.card:ℕ):ℤ)=(S.card:ℤ)-U.card := by omega
    have goal : (A.card:ℤ) ≤ (F.card:ℤ)+(d:ℤ)*((S.card-U.card:ℕ):ℤ) := by
      rw [z]; dsimp only [F]; linarith only [init]
    exact_mod_cast goal
  · intro p hp
    let F' := active r A (U.erase p)
    have inc : F.filter (fun L => p∉L)⊆F' := by
      intro L hl
      obtain ⟨inF,off⟩ := Finset.mem_filter.mp hl
      obtain ⟨inA,count⟩ := Finset.mem_filter.mp inF
      have eq : incident (U.erase p) L=incident U L := by
        ext q
        simp only [incident,Finset.mem_filter,Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨fun e => off (e ▸ h.2),h.1⟩,h.2⟩⟩
      exact Finset.mem_filter.mpr ⟨inA,by simpa only [mult,eq] using count⟩
    have card : F.card ≤ (star F p).card+F'.card := by
      have split := Finset.card_filter_add_card_filter_not (s:=F) (fun L => p∈L)
      exact split ▸ Nat.add_le_add_left (Finset.card_le_card inc) _
    have drop := best (U.erase p) (Finset.mem_powerset.mpr ((Finset.erase_subset ..).trans sub))
    change (F'.card:ℤ)-d*(U.erase p).card≤(F.card:ℤ)-d*U.card at drop
    have size : ((U.erase p).card:ℤ)=(U.card:ℤ)-1 := by
      have h := Finset.card_erase_add_one hp; omega
    rw [size] at drop
    have cc : (F.card:ℤ)≤(star F p).card+(F'.card:ℤ) := by exact_mod_cast card
    exact_mod_cast (by linarith only [drop,cc] : (d:ℤ)≤(star F p).card)

end Erdos101AnchorCore

namespace Erdos101AnchorCore
open Erdos101AnchorGeometry Erdos101AnchorField Erdos101AnchorJoins
open EuclideanGeometry Finset
open scoped Classical

def fourFamily (S : Finset ℝ²) := (determined S).filter (fun L => mult S L=4)

theorem fourFamily_eq (S : Finset ℝ²) : (fourFamily S).card=(linesWithPointsFor 4 (S : Set ℝ²)).ncard := count_eq S 4

theorem determined_of_two {S U : Finset ℝ²} {L : Line} (proper : L∈determined S) (two : 2 ≤ mult U L) :
    L∈determined U := by
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp two
  obtain ⟨au,al⟩ := Finset.mem_filter.mp ha
  obtain ⟨bu,bl⟩ := Finset.mem_filter.mp hb
  exact mem_determined.mpr ⟨a,au,b,bu,ne,unique_line proper al bl ne⟩

theorem incident_mono {U S : Finset ℝ²} (sub : U⊆S) (L : Line) : incident U L ⊆ incident S L :=
  Finset.filter_subset_filter _ sub

end Erdos101AnchorCore

/- Positive-density four-point line families contain a positive-density
subfamily whose points are all intersections of two joins of a single
set of order square root of the ambient size. -/
noncomputable section
namespace Erdos101AnchorCore
open Erdos101AnchorGeometry Erdos101AnchorField Erdos101AnchorJoins
open EuclideanGeometry Finset
open scoped Classical

private theorem star_le {S : Finset ℝ²} {A : Finset Line} (prop : A⊆determined S) {p : ℝ²} (hp : p∈S) :
    (star A p).card≤S.card := by
  have sub : star A p ⊆ (determined S).filter (fun L => p∈L) := Finset.filter_subset_filter _ prop
  rw [← full_pencil hp] at sub
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (Finset.card_le_card (Finset.erase_subset ..)))

theorem compress {S : Finset ℝ²} {A : Finset Line} (four : A⊆fourFamily S)
    (s k : ℕ) (sp : 0<s) (kp : 0<k) (large : 32*s^2*k^2 ≤ S.card)
    (dense : S.card^2 ≤ s*A.card) :
    ∃ B⊆S, k*B.card≤2*S.card ∧ ∃ G⊆A, A.card≤4*G.card ∧
      ∀L∈G, ∀p∈S, p∈L → determinedBy B p := by
  classical
  let d := 16*s*k^2
  have sp' : s≥1 := sp
  have threshold : 4*k^2≤d := by
    dsimp [d]
    exact Nat.mul_le_mul_right _ (by omega)
  have prop : A⊆determined S := four.trans (Finset.filter_subset ..)
  have size (L) (hl : L∈A) : mult S L=4 := (Finset.mem_filter.mp (four hl)).2
  obtain ⟨U,us,F,fa,rich,keep,minD⟩ := peel S A 4 d (fun L h => (size L h).ge)
  have : NeZero k := ⟨kp.ne'⟩
  obtain ⟨B,bu,cheap,miss⟩ := common_anchors (fa.trans prop)
    (fun L hl => (by decide : 3≤4).trans (rich L hl)) threshold minD
  let M := missed U B
  have uc := Finset.card_le_card us
  have few : 4*s*M.card≤S.card := by
    apply Nat.le_of_mul_le_mul_left (c:=4*k^2) _ (by positivity)
    calc 4*k^2*(4*s*M.card) = d*M.card := by dsimp only [d]; ring
         _ ≤ 4*k^2*U.card := miss
         _ ≤ 4*k^2*S.card := Nat.mul_le_mul_left _ uc
  have half : A.card≤2*F.card := by
    have dSize : 2*d*S.card ≤ A.card := by
      apply Nat.le_of_mul_le_mul_left (c:=s) _ sp
      calc s*(2*d*S.card)=(32*s^2*k^2)*S.card := by dsimp only [d]; ring
           _ ≤ S.card*S.card := Nat.mul_le_mul_right _ large
           _ ≤ s*A.card := by simpa only [pow_two] using dense
    have cost := Nat.mul_le_mul_left d (Nat.sub_le S.card U.card)
    have dd : 2*d*S.card=2*(d*S.card) := by ring
    omega
  let bad := M.biUnion (star F)
  let G := F\bad
  have badsize : bad.card≤M.card*S.card := by
    apply (Finset.card_biUnion_le (s:=M) (t:=star F)).trans
    exact (Finset.sum_le_sum (fun p hp => star_le (fa.trans prop) (us (Finset.mem_filter.mp hp).1))).trans_eq (by simp [M,missed])
  have q : 4*bad.card≤A.card := by
    apply Nat.le_of_mul_le_mul_left (c:=s) _ sp
    calc s*(4*bad.card) ≤ s*(4*(M.card*S.card)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ badsize)
         _ = (4*s*M.card)*S.card := by ring
         _ ≤ S.card*S.card := Nat.mul_le_mul_right _ few
         _ ≤ s*A.card := by simpa only [pow_two] using dense
  have dis : bad⊆F := by
    intro L hL
    obtain ⟨p,_,h⟩ := Finset.mem_biUnion.mp hL
    exact (Finset.mem_filter.mp h).1
  have sum : G.card+bad.card=F.card := Finset.card_sdiff_add_card_eq_card dis
  refine ⟨B,bu.trans us,cheap.trans (Nat.mul_le_mul_left _ uc),G,(Finset.sdiff_subset).trans fa,by omega,?_⟩
  intro L hl p ps pl
  obtain ⟨lf,avoid⟩ := Finset.mem_sdiff.mp hl
  have inc := incident_mono us L
  have eq : incident U L=incident S L :=
    Finset.eq_of_subset_of_card_le inc (by change mult S L ≤ mult U L; rw [size _ (fa lf)]; exact rich L lf)
  have inside : p∈incident U L := by rw [eq]; exact Finset.mem_filter.mpr ⟨ps,pl⟩
  have pu : p∈U := (Finset.mem_filter.mp inside).1
  by_contra no
  exact avoid (Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨pu,no⟩,Finset.mem_filter.mpr ⟨lf,pl⟩⟩)

private theorem choose_scale (n s : ℕ) (sp : 0<s) (large : (8*s)^2≤n) :
    ∃ k : ℕ, 0<k ∧ 32*s^2*k^2≤n ∧ n≤256*s^2*k^2 := by
  let k := n.sqrt/(8*s)
  have ep : 0<8*s := by positivity
  have es : 8*s≤n.sqrt := Nat.le_sqrt'.mpr large
  have kp : 0<k := (Nat.div_pos es ep)
  have lo : k*(8*s)≤n.sqrt := Nat.div_mul_le_self _ _
  have upper := Nat.mod_lt n.sqrt ep
  have division := Nat.mod_add_div n.sqrt (8*s)
  change n.sqrt%(8*s)+8*s*k=n.sqrt at division
  have next : n.sqrt+1≤2*(k*(8*s)) := by
    have small := Nat.mul_le_mul_left (8*s) (show 1≤k from kp)
    rw [Nat.mul_one, Nat.mul_comm (8*s) k] at small
    rw [Nat.mul_comm (8*s) k] at division
    omega
  refine ⟨k,kp,?_,?_⟩
  · have sq := (Nat.pow_le_pow_left lo 2).trans (Nat.sqrt_le' n)
    nlinarith only [sq,Nat.zero_le (32*s^2*k^2)]
  · have sq := (Nat.lt_succ_sqrt' n).le.trans (Nat.pow_le_pow_left next 2)
    nlinarith only [sq]

/-- At fixed density n²/s, at least one quarter of the lines are retained,
and every one of their original points is recovered in a single intersection
step. The number b of chosen anchors satisfies b² ≤ 1024 s² n. -/
theorem sqrt_anchors {S : Finset ℝ²} {A : Finset Line} (four : A⊆fourFamily S)
    (s : ℕ) (sp : 0<s) (large : (8*s)^2≤S.card) (dense : S.card^2 ≤ s*A.card) :
    ∃ B⊆S, B.card^2≤1024*s^2*S.card ∧ ∃ G⊆A, A.card≤4*G.card ∧
      ∀L∈G, ∀p∈S, p∈L → determinedBy B p := by
  obtain ⟨k,kp,lo,hi⟩ := choose_scale S.card s sp large
  obtain ⟨B,bs,cheap,G,ga,keep,points⟩ := compress four s k sp kp lo dense
  refine ⟨B,bs,?_,G,ga,keep,points⟩
  apply Nat.le_of_mul_le_mul_left (c:=k^2) _ (by positivity)
  calc k^2*B.card^2=(k*B.card)^2 := (mul_pow ..).symm
       _ ≤ (2*S.card)^2 := Nat.pow_le_pow_left cheap 2
       _ = 4*S.card*S.card := by ring
       _ ≤ 4*(256*s^2*k^2)*S.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hi)
       _ = k^2*(1024*s^2*S.card) := by ring

end Erdos101AnchorCore

namespace Erdos101AnchorCore
open Erdos101AnchorGeometry Erdos101AnchorField
open EuclideanGeometry Finset Filter Asymptotics
open scoped Classical

theorem fourFamily_le_square (T : Finset ℝ²) : (fourFamily T).card ≤ T.card^2 := by
  calc (fourFamily T).card ≤ (determined T).card := Finset.card_filter_le ..
       _ ≤ T.offDiag.card := Finset.card_image_le
       _ ≤ T.card^2 := by rw [Finset.offDiag_card,pow_two]; omega

/-- A counterexample of density 1/s would give another of density at least
1/(4s) on a positive fraction of its points, with all nonanchors reconstructed
by one intersection from a common set of at most O_s(√n) anchors. -/
theorem anchored_witness : OMA.R_Erdos101_erdos_101_R3.H1 := by
  intro s sp
  refine ⟨(8*s)^2,?_⟩
  intro S large _cap dense
  rw [← fourFamily_eq] at dense
  obtain ⟨B,bs,cheap,G,ga,keep,points⟩ := sqrt_anchors (A:=fourFamily S) Finset.Subset.rfl s sp large dense
  let T := B ∪ S.filter (determinedBy B)
  have ts : T ⊆ S := Finset.union_subset bs (Finset.filter_subset ..)
  have bt : B ⊆ T := Finset.subset_union_left
  have rich : G ⊆ fourFamily T := by
    intro L hl
    obtain ⟨proper,card⟩ := Finset.mem_filter.mp (ga hl)
    have eq : incident T L = incident S L := by
      apply Finset.Subset.antisymm (incident_mono ts L)
      intro p hp
      obtain ⟨ps,pl⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ps,points L hl p ps pl⟩),pl⟩
    have four : mult T L = 4 := (congrArg Finset.card eq).trans card
    exact Finset.mem_filter.mpr ⟨determined_of_two proper (by omega),four⟩
  have sd : S.card^2 ≤ 4*s*(fourFamily T).card := calc
    S.card^2 ≤ s*(fourFamily S).card := dense
    _ ≤ s*(4*G.card) := Nat.mul_le_mul_left _ keep
    _ ≤ s*(4*(fourFamily T).card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Finset.card_le_card rich))
    _ = 4*s*(fourFamily T).card := by ring
  have tc := Finset.card_le_card ts
  have positive : 0 < S.card := lt_of_lt_of_le (by positivity : 0 < (8*s)^2) large
  have size : S.card ≤ 4*s*T.card := by
    apply Nat.le_of_mul_le_mul_right _ positive
    rw [← pow_two]
    apply sd.trans
    calc 4*s*(fourFamily T).card ≤ 4*s*T.card^2 := Nat.mul_le_mul_left _ (fourFamily_le_square _)
         _ = 4*s*T.card*T.card := by ring
         _ ≤ 4*s*T.card*S.card := Nat.mul_le_mul_left _ tc
  refine ⟨T,B,ts,bt,size,?_,?_,?_⟩
  · exact cheap.trans ((Nat.mul_le_mul_left (1024*s^2) size).trans_eq (by ring))
  · rw [← fourFamily_eq]
    exact (Nat.pow_le_pow_left tc 2).trans sd
  · intro p hp
    rcases Finset.mem_union.mp hp with h|h
    · exact Or.inl h
    · exact Or.inr (show determinedBy B p from (Finset.mem_filter.mp h).2)

end Erdos101AnchorCore

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R3.H1 := Erdos101AnchorCore.anchored_witness
