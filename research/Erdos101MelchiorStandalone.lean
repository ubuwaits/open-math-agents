import Mathlib
import FormalConjectures.ErdosProblems.«101»

-- Credit: @ubuwaits

/-!
# Melchior's inequality and Erdős 101

For every real point set of size n ≥ 5 with no five collinear,
14 t₄ + 6 t₃ + 6 ≤ n(n−1). This file proves Melchior's classical inequality
and applies it to the exact supremum in the problem. The proof enumerates
the sign regions of affine functions by inserting one constraint at a time.

E. Melchior, Über Vielseite der projektiven Ebene, Deutsche Mathematik 5
(1941), 461–475.
-/

/- Strict sign regions of real linear forms. Inserting one form counts the
regions it cuts on its kernel. The same restrictions count the chamber facets. -/

noncomputable section
namespace Erdos101Chambers

open Finset Filter
open scoped Classical Topology

variable {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

abbrev Forms (ι V : Type*) [AddCommGroup V] [Module ℝ V] := ι → V →ₗ[ℝ] ℝ

def oriented (A : Forms ι V) (T : Finset ι) (i : ι) : V →ₗ[ℝ] ℝ :=
  if i ∈ T then A i else -A i

def strict (A : Forms ι V) (S T : Finset ι) (w : V) : Prop :=
  ∀ i∈S, 0 < oriented A T i w

def regions (A : Forms ι V) (S : Finset ι) (K : Submodule ℝ V) : Finset (Finset ι) :=
  S.powerset.filter (fun T => ∃ w∈K, strict A S T w)

@[simp] theorem mem_regions {A : Forms ι V} {S T : Finset ι} {K : Submodule ℝ V} :
    T ∈ regions A S K ↔ T ⊆ S ∧ ∃ w∈K, strict A S T w := by
  simp [regions]

@[simp] theorem regions_empty (A : Forms ι V) (K : Submodule ℝ V) :
    regions A ∅ K = {∅} := by
  ext T
  simp [Finset.subset_empty,strict,Finset.mem_singleton]
  exact fun _ => ⟨0,K.zero_mem⟩

theorem perturb (A : Forms ι V) {S T : Finset ι} {w : V} (h : strict A S T w) (z : V) :
    ∃ t : ℝ, 0<t ∧ strict A S T (w+t • z) := by
  have near : ∀ᶠ t : ℝ in 𝓝 0, ∀ i∈S, 0 < oriented A T i w+t*oriented A T i z := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have cont : Continuous (fun t : ℝ => oriented A T i w+t*oriented A T i z) := by fun_prop
    apply cont.continuousAt (eventually_gt_nhds _)
    simpa using h i hi
  have pos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  obtain ⟨t,ht,hs⟩ := (pos.and (near.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨t,ht,fun i hi => by simpa using hs i hi⟩

def positive (A : Forms ι V) (S : Finset ι) (K : Submodule ℝ V) (j : ι) :=
  S.powerset.filter (fun T => ∃ w∈K, strict A S T w ∧ 0 < A j w)

def negative (A : Forms ι V) (S : Finset ι) (K : Submodule ℝ V) (j : ι) :=
  S.powerset.filter (fun T => ∃ w∈K, strict A S T w ∧ A j w < 0)

@[simp] theorem mem_pos {A : Forms ι V} {S T : Finset ι} {K : Submodule ℝ V} {j : ι} :
    T ∈ positive A S K j ↔ T ⊆ S ∧ ∃ w∈K, strict A S T w ∧ 0 < A j w := by simp [positive]
@[simp] theorem mem_neg {A : Forms ι V} {S T : Finset ι} {K : Submodule ℝ V} {j : ι} :
    T ∈ negative A S K j ↔ T ⊆ S ∧ ∃ w∈K, strict A S T w ∧ A j w < 0 := by simp [negative]

theorem slice_sides {A : Forms ι V} {S T : Finset ι} {K : Submodule ℝ V} {j : ι}
    (nonzero : ∃ z∈K, 0<A j z)
    (h : T ∈ regions A S (K ⊓ (A j).ker)) :
    T ∈ positive A S K j ∧ T ∈ negative A S K j := by
  obtain ⟨sub,w,⟨wk,wz⟩,hw⟩ := mem_regions.mp h
  change A j w=0 at wz
  obtain ⟨z,zk,az⟩ := nonzero
  obtain ⟨t,ht,hp⟩ := perturb A hw z
  obtain ⟨s,hs,hn⟩ := perturb A hw (-z)
  refine ⟨mem_pos.mpr ⟨sub,_,K.add_mem wk (K.smul_mem t zk),hp,?_⟩,
    mem_neg.mpr ⟨sub,_,K.add_mem wk (K.smul_mem s (K.neg_mem zk)),hn,?_⟩⟩
  · simpa [wz] using mul_pos ht az
  · simpa [wz] using mul_neg_of_pos_of_neg hs (neg_neg_of_pos az)

theorem sides_slice {A : Forms ι V} {S T : Finset ι} {K : Submodule ℝ V} {j : ι}
    (hp : T ∈ positive A S K j) (hn : T ∈ negative A S K j) :
    T ∈ regions A S (K ⊓ (A j).ker) := by
  obtain ⟨sub,x,xk,sx,px⟩ := mem_pos.mp hp
  obtain ⟨_,y,yk,sy,ny⟩ := mem_neg.mp hn
  let w := (A j x) • y + (-(A j y)) • x
  refine mem_regions.mpr ⟨sub,w,⟨K.add_mem (K.smul_mem _ yk) (K.smul_mem _ xk),?_⟩,?_⟩
  · change A j w=0
    simp [w]; ring
  · intro i hi
    simpa [w] using add_pos (mul_pos px (sy i hi)) (mul_pos (neg_pos.mpr ny) (sx i hi))

theorem sides_union {A : Forms ι V} {S : Finset ι} {K : Submodule ℝ V} {j : ι}
    (nonzero : ∃ z∈K, 0<A j z) :
    positive A S K j ∪ negative A S K j = regions A S K := by
  ext T
  rw [Finset.mem_union]
  constructor
  · rintro (hp|hn)
    · obtain ⟨sub,w,wk,ww,_⟩ := mem_pos.mp hp
      exact mem_regions.mpr ⟨sub,w,wk,ww⟩
    · obtain ⟨sub,w,wk,ww,_⟩ := mem_neg.mp hn
      exact mem_regions.mpr ⟨sub,w,wk,ww⟩
  · intro h
    obtain ⟨sub,w,wk,ww⟩ := mem_regions.mp h
    rcases lt_trichotomy (A j w) 0 with h|h|h
    · exact Or.inr (mem_neg.mpr ⟨sub,w,wk,ww,h⟩)
    · exact Or.inl (slice_sides nonzero (mem_regions.mpr ⟨sub,w,⟨wk,h⟩,ww⟩)).1
    · exact Or.inl (mem_pos.mpr ⟨sub,w,wk,ww,h⟩)

theorem strict_insert {A : Forms ι V} {S T : Finset ι} {j : ι} (fresh : j∉S) (sub : T⊆S) (w : V) :
    (strict A (insert j S) (insert j T) w ↔ strict A S T w ∧ 0<A j w) ∧
    (strict A (insert j S) T w ↔ strict A S T w ∧ A j w<0) := by
  have agree (i) (hi : i∈S) : oriented A (insert j T) i = oriented A T i := by
    have ne : i≠j := fun h => fresh (h ▸ hi)
    simp [oriented,ne]
  have jt : j∉T := fun h => fresh (sub h)
  unfold strict
  simp only [Finset.forall_mem_insert]
  have pj : oriented A (insert j T) j = A j := by simp [oriented]
  have nj : oriented A T j = -A j := by simp [oriented,jt]
  simp only [pj,nj,LinearMap.neg_apply,neg_pos]
  constructor
  · constructor
    · exact fun ⟨h,k⟩ => ⟨fun i hi => by simpa only [← agree i hi] using k i hi,h⟩
    · exact fun ⟨k,h⟩ => ⟨h,fun i hi => by simpa only [agree i hi] using k i hi⟩
  · exact and_comm

def halves (P N : Finset (Finset ι)) (j : ι) := P.image (insert j) ∪ N

theorem in_halves {P N : Finset (Finset ι)} {j : ι} {T : Finset ι} :
    T∈halves P N j ↔ (∃ U∈P, insert j U=T) ∨ T∈N := by simp [halves]

theorem regions_halves {A : Forms ι V} {S : Finset ι} {K : Submodule ℝ V} {j : ι}
    (fresh : j∉S) :
    regions A (insert j S) K = halves (positive A S K j) (negative A S K j) j := by
  ext T
  rw [in_halves]
  constructor
  · intro h
    obtain ⟨sub,w,wk,ww⟩ := mem_regions.mp h
    by_cases inT : j∈T
    · let U := T.erase j
      have us : U⊆S := by
        intro i hi
        exact (Finset.mem_insert.mp (sub (Finset.mem_erase.mp hi).2)).resolve_left (Finset.mem_erase.mp hi).1
      have eq : insert j U=T := Finset.insert_erase inT
      exact Or.inl ⟨U,mem_pos.mpr ⟨us,w,wk,(strict_insert fresh us w).1.mp (eq.symm ▸ ww)⟩,eq⟩
    · have ts : T⊆S := by
        intro i hi
        exact (Finset.mem_insert.mp (sub hi)).resolve_left (fun e => inT (e ▸ hi))
      exact Or.inr (mem_neg.mpr ⟨ts,w,wk,(strict_insert fresh ts w).2.mp ww⟩)
  · rintro (⟨U,hU,rfl⟩|hT)
    · obtain ⟨sub,w,wk,ww⟩ := mem_pos.mp hU
      exact mem_regions.mpr ⟨Finset.insert_subset_insert _ sub,w,wk,(strict_insert fresh sub w).1.mpr ww⟩
    · obtain ⟨sub,w,wk,ww⟩ := mem_neg.mp hT
      exact mem_regions.mpr ⟨sub.trans (Finset.subset_insert ..),w,wk,(strict_insert fresh sub w).2.mpr ww⟩

theorem card_halves {P N : Finset (Finset ι)} {j : ι}
    (hp : ∀T∈P, j∉T) (hn : ∀T∈N, j∉T) : (halves P N j).card=P.card+N.card := by
  have dis : Disjoint (P.image (insert j)) N := by
    apply Finset.disjoint_left.mpr
    intro T hT hN
    obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hT
    exact hn _ hN (Finset.mem_insert_self ..)
  have inj : (P : Set (Finset ι)).InjOn (insert j) := by
    intro T ht U hu eq
    simpa [Finset.erase_insert (hp T ht),Finset.erase_insert (hp U hu)] using
      congrArg (fun X : Finset ι => X.erase j) eq
  rw [halves,Finset.card_union_of_disjoint dis,Finset.card_image_of_injOn inj]

theorem region_recurrence {A : Forms ι V} {S : Finset ι} {K : Submodule ℝ V} {j : ι}
    (fresh : j∉S) (nonzero : ∃ z∈K, 0<A j z) :
    (regions A (insert j S) K).card=(regions A S K).card+(regions A S (K ⊓ (A j).ker)).card := by
  have both : positive A S K j ∩ negative A S K j = regions A S (K ⊓ (A j).ker) := by
    ext T
    rw [Finset.mem_inter]
    exact ⟨fun ⟨p,n⟩ => sides_slice p n,slice_sides nonzero⟩
  rw [regions_halves fresh,card_halves (fun _ ht hj => fresh ((mem_pos.mp ht).1 hj))
    (fun _ ht hj => fresh ((mem_neg.mp ht).1 hj)),← sides_union nonzero,← both]
  exact (Finset.card_union_add_card_inter ..).symm

def walls (A : Forms ι V) (S T : Finset ι) (K : Submodule ℝ V) :=
  S.filter (fun j => ∃ w∈K, A j w=0 ∧ strict A (S.erase j) T w)

theorem wall_count {A : Forms ι V} {S : Finset ι} {K : Submodule ℝ V} {j : ι}
    (fresh : j∉S) (nonzero : ∃ z∈K, 0<A j z) :
    ((regions A (insert j S) K).filter (fun T => j∈walls A (insert j S) T K)).card =
      2*(regions A S (K ⊓ (A j).ker)).card := by
  let R := regions A S (K ⊓ (A j).ker)
  have eq : ((regions A (insert j S) K).filter (fun T => j∈walls A (insert j S) T K)) = halves R R j := by
    ext T
    rw [Finset.mem_filter,regions_halves fresh,in_halves,in_halves]
    have erase : (insert j S).erase j=S := Finset.erase_insert fresh
    have sw (U : Finset ι) (w : V) : strict A S (insert j U) w ↔ strict A S U w := by
      unfold strict
      apply forall₂_congr
      intro i hi
      have ne : i≠j := fun e => fresh (e ▸ hi)
      simp [oriented,ne]
    constructor
    · rintro ⟨hT,hw⟩
      obtain ⟨_,w,wk,zero,hs⟩ := Finset.mem_filter.mp hw
      rw [erase] at hs
      rcases hT with ⟨U,hU,rfl⟩|hU
      · exact Or.inl ⟨U,mem_regions.mpr ⟨(mem_pos.mp hU).1,w,⟨wk,zero⟩,(sw U w).mp hs⟩,rfl⟩
      · exact Or.inr (mem_regions.mpr ⟨(mem_neg.mp hU).1,w,⟨wk,zero⟩,hs⟩)
    · rintro (⟨U,hU,rfl⟩|hU)
      · obtain ⟨_,w,⟨wk,zero⟩,hs⟩ := mem_regions.mp hU
        exact ⟨Or.inl ⟨U,(slice_sides nonzero hU).1,rfl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_insert_self ..,w,wk,zero,erase.symm ▸ (sw U w).mpr hs⟩⟩
      · obtain ⟨_,w,⟨wk,zero⟩,hs⟩ := mem_regions.mp hU
        exact ⟨Or.inr (slice_sides nonzero hU).2,
          Finset.mem_filter.mpr ⟨Finset.mem_insert_self ..,w,wk,zero,erase.symm ▸ hs⟩⟩
  have avoid : ∀ U∈R, j∉U := fun _ h hj => fresh ((mem_regions.mp h).1 hj)
  rw [eq,card_halves avoid avoid,two_mul]

end Erdos101Chambers

/- Each sign chamber of an essential rank-three arrangement has at least
three walls. The proof uses a minimal subfamily of closed linear inequalities. -/
noncomputable section
namespace Erdos101Chambers
open Finset
open scoped Classical
variable {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

def weak (A : Forms ι V) (S T : Finset ι) (w : V) := ∀ i∈S, 0 ≤ oriented A T i w

lemma oriented_zero {A : Forms ι V} {T : Finset ι} {i : ι} {w : V} :
    oriented A T i w=0 ↔ A i w=0 := by by_cases h : i∈T <;> simp [oriented,h]

theorem three_walls {A : Forms ι V} {K : Submodule ℝ V} {S T : Finset ι}
    (region : T∈regions A S K)
    (pair : ∀ j∈S, ∀ i∈S, i≠j → ∃ z∈K, A j z=0 ∧ A i z≠0)
    (essential : ∀ J⊆S, J.card≤2 →
      ∃ z∈K, (∀ j∈J, A j z=0) ∧ ∃ i∈S, A i z≠0) :
    3 ≤ (walls A S T K).card := by
  classical
  obtain ⟨_,x,xk,sx⟩ := mem_regions.mp region
  let good (J : Finset ι) := ∀ w∈K, weak A J T w → weak A S T w
  let choices := S.powerset.filter good
  have mem (J : Finset ι) : J∈choices ↔ J⊆S ∧ good J := by simp [choices]
  have start : S∈choices := (mem S).mpr ⟨Finset.Subset.rfl,fun _ _ h => h⟩
  obtain ⟨J,inJ,minJ⟩ := choices.exists_min_image Finset.card ⟨S,start⟩
  obtain ⟨sub,suff⟩ := (mem J).mp inJ
  have enough : 3≤J.card := by
    by_contra! small
    obtain ⟨z,zk,zero,i,is,nonzero⟩ := essential J sub (by omega)
    have z0 (j) (hj : j∈J) : oriented A T j z=0 := oriented_zero.mpr (zero j hj)
    have plus := suff z zk (fun j hj => (z0 j hj).ge) i is
    have minus := suff (-z) (K.neg_mem zk) (fun j hj => by simp [z0 j hj]) i is
    rw [map_neg] at minus
    exact nonzero (oriented_zero.mp (le_antisymm (by linarith) plus))
  apply enough.trans (Finset.card_le_card _)
  intro j hj
  have js := sub hj
  have notgood : ¬good (J.erase j) := by
    intro g
    have smaller := minJ _ ((mem _).mpr ⟨(Finset.erase_subset ..).trans sub,g⟩)
    exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hj)) smaller
  change ¬∀ v∈K, weak A (J.erase j) T v → weak A S T v at notgood
  push Not at notgood
  obtain ⟨v,vk,weakv,bad⟩ := notgood
  have jv : oriented A T j v<0 := by
    by_contra! h
    apply bad (suff v vk _)
    intro i hi
    by_cases e : i=j
    · simpa [e] using h
    · exact weakv i (Finset.mem_erase.mpr ⟨e,hi⟩)
  let w := (oriented A T j x) • v+(-(oriented A T j v)) • x
  have wk : w∈K := K.add_mem (K.smul_mem _ vk) (K.smul_mem _ xk)
  have jzero : oriented A T j w=0 := by simp [w]; ring
  have other : strict A (J.erase j) T w := by
    intro i hi
    simpa [w] using add_pos_of_nonneg_of_pos (mul_nonneg (sx j js).le (weakv i hi))
      (mul_pos (neg_pos.mpr jv) (sx i (sub (Finset.mem_erase.mp hi).2)))
  have weakw : weak A S T w := by
    apply suff w wk
    intro i hi
    by_cases e : i=j
    · simpa [e] using jzero.ge
    · exact (other i (Finset.mem_erase.mpr ⟨e,hi⟩)).le
  refine Finset.mem_filter.mpr ⟨js,w,wk,oriented_zero.mp jzero,?_⟩
  intro i hi
  obtain ⟨ne,is⟩ := Finset.mem_erase.mp hi
  apply lt_of_le_of_ne (weakw i is)
  intro eq
  obtain ⟨z,zk,jz,iz⟩ := pair j js i is ne
  have iz' : oriented A T i z≠0 := fun h => iz (oriented_zero.mp h)
  have dir : ∃ u∈K, oriented A T j u=0 ∧ oriented A T i u<0 := by
    rcases lt_or_gt_of_ne iz' with h|h
    · exact ⟨z,zk,oriented_zero.mpr jz,h⟩
    · exact ⟨-z,K.neg_mem zk,by simp [(oriented_zero.mpr jz : oriented A T j z=0)],by simpa using neg_neg_of_pos h⟩
  obtain ⟨u,uk,ju,iu⟩ := dir
  obtain ⟨t,ht,step⟩ := perturb A other u
  have all := suff (w+t • u) (K.add_mem wk (K.smul_mem _ uk)) (by
    intro k hk
    by_cases e : k=j
    · subst k; simp [jzero,ju]
    · exact (step k (Finset.mem_erase.mpr ⟨e,hk⟩)).le)
  have fail := all i is
  simp [← eq] at fail
  exact (mul_neg_of_pos_of_neg ht iu).not_ge fail

end Erdos101Chambers

/- Count the signs of affine functions constrained to vanish on a point,
or on a pair of points, in the real plane. -/
noncomputable section
namespace Erdos101PlaneChambers
open Erdos101Chambers EuclideanGeometry Finset
open scoped Classical
abbrev Weight := Fin 3 → ℝ
abbrev Line := AffineSubspace ℝ ℝ²

def ev (p : ℝ²) : Weight →ₗ[ℝ] ℝ where
  toFun w := w 0+p 0*w 1+p 1*w 2
  map_add' u v := by simp; ring
  map_smul' t w := by simp; ring

def normal (p q : ℝ²) : Weight := ![p 0*q 1-q 0*p 1,p 1-q 1,q 0-p 0]

lemma ev_apply (p : ℝ²) (w : Weight) : ev p w=w 0+p 0*w 1+p 1*w 2 := rfl

@[simp] lemma first_zero (p q : ℝ²) : ev p (normal p q)=0 := by simp [ev_apply,normal]; ring
@[simp] lemma second_zero (p q : ℝ²) : ev q (normal p q)=0 := by simp [ev_apply,normal]; ring

lemma separates {p q : ℝ²} (ne : p≠q) : ∃ z∈(ev p).ker, 0<ev q z := by
  have dir : ∃ z∈(ev p).ker, ev q z≠0 := by
    by_cases nx : p 0=q 0
    · have ny : p 1≠q 1 := by intro eq; apply ne; ext i; fin_cases i <;> assumption
      refine ⟨![-p 1,0,1],?_,?_⟩
      · change -p 1+p 0*0+p 1*1=0; ring
      · change -p 1+q 0*0+q 1*1≠0; intro eq; apply ny; linarith
    · refine ⟨![-p 0,1,0],?_,?_⟩
      · change -p 0+p 0*1+p 1*0=0; ring
      · change -p 0+q 0*1+q 1*0≠0; intro eq; apply nx; linarith
  obtain ⟨z,zp,zq⟩ := dir
  rcases lt_or_gt_of_ne zq with h|h
  · exact ⟨-z,(ev p).ker.neg_mem zp, by rw [map_neg]; linarith⟩
  · exact ⟨z,zp,h⟩

theorem two_kernels {p q : ℝ²} (ne : p≠q) {w : Weight} (pzero : ev p w=0) (qzero : ev q w=0) :
    ∃ t : ℝ, w=t • normal p q := by
  rw [ev_apply] at pzero qzero
  by_cases xeq : q 0=p 0
  · have dy : p 1-q 1≠0 := by
      apply sub_ne_zero.mpr; intro he; apply ne; ext i; fin_cases i
      · exact xeq.symm
      · exact he
    have z : w 2=0 := by
      apply (mul_eq_zero.mp (show (p 1-q 1)*w 2=0 by rw [xeq] at qzero; linarith only [pzero,qzero])).resolve_left dy
    refine ⟨w 1/(p 1-q 1),?_⟩
    ext i; fin_cases i <;> simp [normal,z,xeq] at * <;> field_simp [dy]; linear_combination (p 1-q 1)*pzero
  · have dx := sub_ne_zero.mpr xeq
    refine ⟨w 2/(q 0-p 0),?_⟩
    ext i; fin_cases i <;> simp [normal] <;> field_simp [dx] <;>
      first | linear_combination q 0*pzero-p 0*qzero | linear_combination qzero-pzero

theorem on_line {p q r : ℝ²} (ne : p≠q) : ev r (normal p q)=0 ↔ r∈line[ℝ,p,q] := by
  change p 0*q 1-q 0*p 1+r 0*(p 1-q 1)+r 1*(q 0-p 0)=0 ↔ _
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · intro h
    by_cases xeq : q 0=p 0
    · have dy : q 1-p 1≠0 := by
        apply sub_ne_zero.mpr; intro he; apply ne; ext i; fin_cases i <;> symm <;> assumption
      have rx : r 0=p 0 := by
        apply sub_eq_zero.mp ((mul_eq_zero.mp (show (r 0-p 0)*(q 1-p 1)=0 by rw [xeq] at h; linear_combination -h)).resolve_right dy)
      refine ⟨(r 1-p 1)/(q 1-p 1),?_⟩
      ext i; fin_cases i <;> simp [AffineMap.lineMap_apply_module,xeq,rx] <;> field_simp [dy] <;> ring
    · have dx := sub_ne_zero.mpr xeq
      refine ⟨(r 0-p 0)/(q 0-p 0),?_⟩
      ext i; fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> field_simp [dx] <;>
        first | linear_combination -h | ring
  · rintro ⟨t,rfl⟩
    simp [AffineMap.lineMap_apply_module]
    ring

private lemma strict_signs {S T : Finset ℝ²} {w : Weight} (sub : T⊆S) (h : strict ev S T w) :
    T = S.filter (fun i => 0 < ev i w) := by
  ext i
  rw [Finset.mem_filter]
  by_cases hi : i∈T
  · have := h i (sub hi)
    exact ⟨fun _ => ⟨sub hi,by simpa [oriented,hi] using this⟩,fun _ => hi⟩
  · refine ⟨fun a => False.elim (hi a),?_⟩
    rintro ⟨is,pos⟩
    have neg : ev i w<0 := by simpa [oriented,hi] using h i is
    exact False.elim ((lt_asymm neg pos))

private lemma signs_strict {S : Finset ℝ²} {w : Weight} (h : ∀i∈S, ev i w≠0) :
    strict ev S (S.filter (fun i => 0 < ev i w)) w := by
  intro i hi
  rcases lt_or_gt_of_ne (h i hi) with neg|pos
  · simp [oriented,hi,not_lt_of_gt neg,neg]
  · simp [oriented,hi,pos]

def pencil (p : ℝ²) (I : Finset ℝ²) := I.image (fun q => line[ℝ,p,q])

theorem double_count {p q : ℝ²} (ne : p≠q) {I : Finset ℝ²} (nonempty : I.Nonempty)
    (fresh : p∉I) :
    (regions ev I ((ev p).ker ⊓ (ev q).ker)).card =
      if line[ℝ,p,q]∈pencil p I then 0 else 2 := by
  classical
  have member (i : ℝ²) (hi : i∈I) : i∈line[ℝ,p,q] ↔ line[ℝ,p,i]=line[ℝ,p,q] := by
    constructor
    · intro h; exact affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ..) h (fun he => fresh (he ▸ hi))
    · intro h; exact h ▸ right_mem_affineSpan_pair ℝ p i
  by_cases repeated : line[ℝ,p,q] ∈ pencil p I
  · rw [if_pos repeated,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    obtain ⟨_,w,⟨wp,wq⟩,sw⟩ := mem_regions.mp hT
    obtain ⟨t,rfl⟩ := two_kernels ne wp wq
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp repeated
    have e : ev i (normal p q)=0 := (on_line ne).mpr ((member i hi).mpr eq)
    have h := sw i hi
    by_cases z : i∈T <;> simp [oriented,z,e,map_smul] at h
  · rw [if_neg repeated]
    let n := normal p q
    let P := I.filter (fun i => 0<ev i n)
    let N := I.filter (fun i => ev i n<0)
    have nz (i) (hi : i∈I) : ev i n≠0 := fun e =>
      repeated (Finset.mem_image.mpr ⟨i,hi,(member i hi).mp ((on_line ne).mp e)⟩)
    have seteq : regions ev I ((ev p).ker ⊓ (ev q).ker)={P,N} := by
      ext T
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · intro h
        obtain ⟨sub,w,⟨wp,wq⟩,sw⟩ := mem_regions.mp h
        obtain ⟨t,rfl⟩ := two_kernels ne wp wq
        have eq := strict_signs sub sw
        rcases lt_trichotomy t 0 with ht|rfl|ht
        · right; rw [eq]; apply Finset.filter_congr; intro i _
          change 0 < ev i (t • n) ↔ ev i n < 0
          rw [map_smul]; change 0 < t*ev i n ↔ _
          simp [mul_pos_iff,ht,not_lt_of_gt ht]
        · obtain ⟨i,hi⟩ := nonempty
          have h := sw i hi
          simp at h
        · left; rw [eq]; apply Finset.filter_congr; intro i _
          change 0 < ev i (t • n) ↔ 0 < ev i n
          rw [map_smul]; exact mul_pos_iff_of_pos_left ht
      · rintro (rfl|rfl)
        · exact mem_regions.mpr ⟨Finset.filter_subset ..,n,⟨first_zero ..,second_zero ..⟩,signs_strict nz⟩
        · have same : N=I.filter (fun i => 0<ev i (-n)) := by simp only [map_neg,neg_pos]; rfl
          rw [same]
          exact mem_regions.mpr ⟨Finset.filter_subset ..,-n,
            ⟨(ev p).ker.neg_mem (first_zero ..),(ev q).ker.neg_mem (second_zero ..)⟩,
            signs_strict (fun i hi => by simpa only [map_neg,neg_ne_zero] using nz i hi)⟩
    have pn : P≠N := by
      obtain ⟨i,hi⟩ := nonempty
      intro he
      have m : i∈P ↔ i∈N := he ▸ Iff.rfl
      change i∈I.filter (fun k => 0<ev k n) ↔ i∈I.filter (fun k => ev k n<0) at m
      simp only [Finset.mem_filter,hi,true_and] at m
      rcases lt_or_gt_of_ne (nz i hi) with neg|pos
      · exact (lt_asymm neg (m.mpr neg))
      · exact (lt_asymm pos (m.mp pos))
    rw [seteq,Finset.card_pair pn]

theorem pencil_regions (p : ℝ²) (I : Finset ℝ²) (fresh : p∉I) (nonempty : I.Nonempty) :
    (regions ev I (ev p).ker).card=2*(pencil p I).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at nonempty
  | @insert q I new ih =>
    have notq : p≠q := fun h => fresh (h ▸ Finset.mem_insert_self ..)
    have notI : p∉I := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [region_recurrence new (separates notq)]
    by_cases any : I.Nonempty
    · rw [ih notI any,double_count notq any notI]
      have add : pencil p (insert q I)=insert (line[ℝ,p,q]) (pencil p I) := Finset.image_insert ..
      rw [add]
      by_cases rep : line[ℝ,p,q]∈pencil p I
      · rw [if_pos rep,Finset.insert_eq_of_mem rep,Nat.add_zero]
      · rw [if_neg rep,Finset.card_insert_of_notMem rep]; omega
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp any
      simp [pencil]

end Erdos101PlaneChambers

/- Melchior's inequality for arbitrary finite noncollinear real point sets.
The enumeration uses sign regions of affine functions and their walls. -/

noncomputable section
namespace Erdos101Melchior
open Erdos101Chambers Erdos101PlaneChambers EuclideanGeometry Finset
open scoped Classical

def determined (S : Finset ℝ²) : Finset Line := S.offDiag.image (fun e => line[ℝ,e.1,e.2])
def incident (S : Finset ℝ²) (L : Line) := S.filter (fun p => p∈L)
def mult (S : Finset ℝ²) (L : Line) := (incident S L).card
def excess (I : Finset ℝ²) (L : Line) := mult I L-1

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

theorem mult_two {S : Finset ℝ²} {L : Line} (hL : L∈determined S) : 2 ≤ mult S L := by
  obtain ⟨a,ha,b,hb,ne,rfl⟩ := mem_determined.mp hL
  exact Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,left_mem_affineSpan_pair ..⟩,
    b,Finset.mem_filter.mpr ⟨hb,right_mem_affineSpan_pair ..⟩,ne⟩

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

private theorem excess_insert {S I : Finset ℝ²} {p : ℝ²} (sub : I⊆S) (ps : p∈S) (new : p∉I) :
    (∑ L∈determined S, excess (insert p I) L)=(∑ L∈determined S, excess I L)+(pencil p I).card := by
  have step (L : Line) :
      excess (insert p I) L = excess I L + if p∈L ∧ (incident I L).Nonempty then 1 else 0 := by
    by_cases pl : p∈L
    · have new' : p∉incident I L := fun h => new (Finset.mem_filter.mp h).1
      have ins : incident (insert p I) L=insert p (incident I L) := by simp [incident,Finset.filter_insert,pl]
      rw [excess,mult,ins,Finset.card_insert_of_notMem new']
      unfold excess mult
      by_cases h : (incident I L).Nonempty
      · simp [pl,h]
      · simp [pl,Finset.not_nonempty_iff_eq_empty.mp h]
    · have ins : incident (insert p I) L=incident I L := by simp [incident,Finset.filter_insert,pl]
      simp [excess,mult,ins,pl]
  simp_rw [step]
  rw [Finset.sum_add_distrib,← through_insert sub ps new]
  simp

theorem full_regions {S I : Finset ℝ²} (sub : I⊆S) (nonempty : I.Nonempty) :
    (regions ev I ⊤).card=2+2*∑ L∈determined S, excess I L := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at nonempty
  | @insert p I new ih =>
    have nz : ∃ w∈(⊤ : Submodule ℝ Weight), 0<ev p w := ⟨![1,0,0],Submodule.mem_top,by simp [ev_apply]⟩
    have ps := sub (Finset.mem_insert_self ..)
    have ins := (Finset.subset_insert p I).trans sub
    rw [region_recurrence new nz,top_inf_eq]
    by_cases any : I.Nonempty
    · rw [ih ins any,pencil_regions p I new any,excess_insert ins ps new]
      omega
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp any
      have zero (L : Line) : excess {p} L=0 := by by_cases h : p∈L <;> simp [excess,mult,incident,Finset.filter_singleton,h]
      simp [zero]

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

def noncollinear (S : Finset ℝ²) := ∀ p∈S, ∀ q∈S, p≠q → ∃ r∈S, r∉line[ℝ,p,q]

theorem wall_minimum {S T : Finset ℝ²} (two : 2≤S.card) (noncol : noncollinear S)
    (ht : T∈regions ev S ⊤) : 3≤(walls ev S T ⊤).card := by
  apply three_walls ht
  · intro j _ i _ ne
    obtain ⟨z,jz,iz⟩ := separates ne.symm
    exact ⟨z,Submodule.mem_top,jz,iz.ne'⟩
  · intro J js small
    obtain ⟨B,jb,bs,size⟩ := Finset.exists_subsuperset_card_eq js small two
    obtain ⟨p,q,ne,rfl⟩ := Finset.card_eq_two.mp size
    obtain ⟨r,rs,rl⟩ := noncol p (bs (by simp)) q (bs (by simp)) ne
    refine ⟨normal p q,Submodule.mem_top,?_,r,rs,fun h => rl ((on_line ne).mp h)⟩
    intro i hi
    have e := jb hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with rfl|rfl
    · exact first_zero ..
    · exact second_zero ..

theorem chamber_bound {S : Finset ℝ²} (two : 2≤S.card) (noncol : noncollinear S) :
    3*(2+2*∑ L∈determined S, excess S L) ≤ 4*∑ L∈determined S, mult S L := by
  let R := regions ev S ⊤
  have lower : 3*R.card ≤ ∑ T∈R, (walls ev S T ⊤).card := by
    calc 3*R.card = ∑ _T∈R, 3 := by simp [Nat.mul_comm]
         _ ≤ _ := Finset.sum_le_sum fun T ht => wall_minimum two noncol ht
  have right (p : ℝ²) (ps : p∈S) :
      (R.filter (fun T => p∈walls ev S T ⊤)).card =
        4*((determined S).filter (fun L => p∈L)).card := by
    have any : (S.erase p).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ps]; omega)
    have nz : ∃ w∈(⊤ : Submodule ℝ Weight), 0<ev p w := ⟨![1,0,0],Submodule.mem_top,by simp [ev_apply]⟩
    have eq := wall_count (S := S.erase p) (Finset.notMem_erase p S) nz
    rw [Finset.insert_erase ps,top_inf_eq,pencil_regions p _ (Finset.notMem_erase p S) any,full_pencil ps] at eq
    exact eq.trans (by omega)
  have swap : (∑ T∈R, (walls ev S T ⊤).card)=∑ p∈S, (R.filter (fun T => p∈walls ev S T ⊤)).card := by
    have keep (T : Finset ℝ²) : walls ev S T ⊤ = S.filter (fun p => p∈walls ev S T ⊤) := by
      ext p; simp [walls]
    conv_lhs => arg 2; ext T; rw [keep T]
    exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
  have swap' : (∑ p∈S, ((determined S).filter (fun L => p∈L)).card) = ∑ L∈determined S, mult S L :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun p L => p∈L)
  rw [swap,Finset.sum_congr rfl right,← Finset.mul_sum,swap'] at lower
  change 3*(regions ev S ⊤).card ≤ _ at lower
  rwa [full_regions (Finset.Subset.rfl (s:=S)) (Finset.card_pos.mp (by omega))] at lower

end Erdos101Melchior

/- The classical Melchior inequality, the exact pair partition, and an
unconditional finite bound on the precise maximum in Erdős problem 101. -/

noncomputable section
namespace Erdos101Melchior
open Erdos101PlaneChambers EuclideanGeometry Finset
open scoped Classical

def count (S : Finset ℝ²) (k : ℕ) := ((determined S).filter (fun L => mult S L=k)).card

theorem count_eq (S : Finset ℝ²) (k : ℕ) : count S k=(linesWithPointsFor k (S : Set ℝ²)).ncard := by
  have eq : (↑((determined S).filter (fun L => mult S L=k)) : Set Line)=linesWithPointsFor k (S : Set ℝ²) := by
    ext L
    have coe : (incident S L : Set ℝ²)=(L : Set ℝ²) ∩ S := by ext p; simp [incident,and_comm]
    simp only [Finset.mem_coe,Finset.mem_filter,mem_determined,linesWithPointsFor,Set.mem_ofPred_eq,
      mult,← Set.ncard_coe_finset,coe]
    simp [exists_prop]
  rw [← eq,Set.ncard_coe_finset,count]

theorem melchior {S : Finset ℝ²} (two : 2≤S.card) (noncol : noncollinear S) :
    3+(∑ L∈determined S, (mult S L-3)) ≤ count S 2 := by
  let D := determined S
  have e (L : Line) (hl : L∈D) : mult S L=excess S L+1 := by
    have := mult_two hl
    unfold excess
    omega
  have eSum : (∑ L∈D, mult S L)=(∑ L∈D, excess S L)+D.card := by
    rw [Finset.sum_congr rfl e,Finset.sum_add_distrib]; simp
  have ch := chamber_bound two noncol
  change 3*(2+2*∑ L∈D, excess S L) ≤ 4*∑ L∈D, mult S L at ch
  have arith : 3+∑ L∈D, mult S L ≤ 3*D.card := by omega
  have localEq (L : Line) (hl : L∈D) :
      mult S L+(if mult S L=2 then 1 else 0)=3+(mult S L-3) := by
    have := mult_two hl
    split_ifs <;> omega
  have total := Finset.sum_congr (s₁:=D) rfl localEq
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at total
  have count' : (∑ L∈D, if mult S L=2 then 1 else 0)=count S 2 := by simp [count,D]
  rw [count'] at total
  change 3+∑ L∈D, (mult S L-3) ≤ count S 2
  omega

theorem pairs_partition (S : Finset ℝ²) : (∑ L∈determined S, mult S L*(mult S L-1))=S.card*(S.card-1) := by
  let make (e : ℝ² × ℝ²) := line[ℝ,e.1,e.2]
  have fiber (L : Line) (hL : L∈determined S) :
      S.offDiag.filter (fun e => make e=L)=(incident S L).offDiag := by
    ext ⟨a,b⟩
    simp only [Finset.mem_filter,Finset.mem_offDiag,incident]
    constructor
    · rintro ⟨⟨ha,hb,ne⟩,he⟩
      exact ⟨⟨ha,he ▸ left_mem_affineSpan_pair ℝ a b⟩,⟨hb,he ▸ right_mem_affineSpan_pair ℝ a b⟩,ne⟩
    · rintro ⟨⟨ha,al⟩,⟨hb,bl⟩,ne⟩
      exact ⟨⟨ha,hb,ne⟩,unique_line hL al bl ne⟩
  have eq := Finset.card_eq_sum_card_image make S.offDiag
  change S.offDiag.card=∑ L∈determined S, (S.offDiag.filter (fun e => make e=L)).card at eq
  rw [Finset.sum_congr rfl (fun L hl => congrArg Finset.card (fiber L hl))] at eq
  simpa only [mult,Finset.offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one] using eq.symm

theorem capped {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) {a b : ℝ²} :
    mult S (line[ℝ,a,b]) ≤ 4 := by
  by_contra! h
  obtain ⟨U,sub,size⟩ := Finset.exists_subset_card_eq (show 5 ≤ (incident S (line[ℝ,a,b])).card from h)
  apply hcap (U : Set ℝ²) (Finset.coe_subset.mpr (sub.trans (Finset.filter_subset ..))) U.finite_toSet (by simpa using size)
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨a,b -ᵥ a,?_⟩
  intro p hp
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (Finset.mem_filter.mp (sub hp)).2
  exact ⟨t,ht.symm⟩

theorem capped_noncollinear {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) (five : 5≤S.card) :
    noncollinear S := by
  intro p _ q _ _
  by_contra! inside
  have eq : incident S (line[ℝ,p,q])=S := Finset.filter_true_of_mem (fun i hi => inside i hi)
  have h := capped (a:=p) (b:=q) hcap
  rw [mult,eq] at h
  omega

theorem capped_ordinary {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) (five : 5≤S.card) :
    3+count S 4 ≤ count S 2 := by
  have main := melchior (by omega : 2≤S.card) (capped_noncollinear hcap five)
  have same (L : Line) (hl : L∈determined S) : mult S L-3=(if mult S L=4 then 1 else 0) := by
    obtain ⟨a,_,b,_,_,rfl⟩ := mem_determined.mp hl
    have h := capped (a:=a) (b:=b) hcap
    split_ifs <;> omega
  simpa [Finset.sum_congr rfl same,count] using main

theorem capped_partition {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) :
    2*count S 2+6*count S 3+12*count S 4=S.card*(S.card-1) := by
  have localEq (L : Line) (hl : L∈determined S) : mult S L*(mult S L-1) =
      2*(if mult S L=2 then 1 else 0)+6*(if mult S L=3 then 1 else 0)+12*(if mult S L=4 then 1 else 0) := by
    have lo := mult_two hl
    obtain ⟨a,_,b,_,_,rfl⟩ := mem_determined.mp hl
    have hi := capped (a:=a) (b:=b) hcap
    interval_cases v : mult S (line[ℝ,a,b]) <;> decide
  have sum := pairs_partition S
  rw [Finset.sum_congr rfl localEq] at sum
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,Nat.cast_id,count] using sum

theorem real_four_bound {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) (five : 5≤S.card) :
    14*count S 4+6*count S 3+6 ≤ S.card*(S.card-1) := by
  have ord := capped_ordinary hcap five
  have all := capped_partition hcap
  omega

theorem max_four_bound (n : ℕ) (five : 5≤n) : 14*Erdos101.numLinesWithFourPointMax n+6 ≤ n*(n-1) := by
  have six : 6≤n*(n-1) := (show 6≤5*4 by decide).trans (Nat.mul_le_mul five (by omega))
  suffices bound : Erdos101.numLinesWithFourPointMax n ≤ (n*(n-1)-6)/14 by omega
  apply csSup_le'
  rintro b ⟨S,hs,fin,cap,rfl⟩
  let T := fin.toFinset
  have eq : (T : Set ℝ²)=S := fin.coe_toFinset
  have size : T.card=n := by simpa [T,← Set.ncard_eq_toFinset_card] using hs
  have main := real_four_bound (S:=T) (eq.symm ▸ cap) (size.symm ▸ five)
  rw [count_eq T 4,eq,size] at main
  omega

end Erdos101Melchior
