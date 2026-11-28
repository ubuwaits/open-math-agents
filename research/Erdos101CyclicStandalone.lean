import Mathlib
import FormalConjectures.ErdosProblems.«101»

/-! # Four-point lines in sparse prime Fourier orbits

For an injective parametrization `z(t) = ∑ cⱼ exp(2πi eⱼ t / p)` with rational
coefficients, a subset of size `n` determines at most `[5 + (1+6k²)²] n` lines
containing exactly four of its points. The prime and frequencies can vary.
The same little-o conclusion holds with `k⁴ = o(n)` and `o(n)` arbitrary outliers.
For arbitrary complex coefficients there is still a uniform linear bound per fixed
number of terms. `Erdos101CyclicNear.littleO` and `Erdos101CyclicComplex.littleO`
give the corresponding asymptotic estimates. -/

noncomputable section

namespace Erdos101PlaneChambers
open EuclideanGeometry Finset
open scoped Classical
abbrev Weight := Fin 3 → ℝ
abbrev Line := AffineSubspace ℝ ℝ²

def ev (p : ℝ²) : Weight →ₗ[ℝ] ℝ where
  toFun w := w 0+p 0*w 1+p 1*w 2
  map_add' u v := by simp; ring
  map_smul' t w := by simp; ring

def normal (p q : ℝ²) : Weight := ![p 0*q 1-q 0*p 1,p 1-q 1,q 0-p 0]

lemma ev_apply (p : ℝ²) (w : Weight) : ev p w=w 0+p 0*w 1+p 1*w 2 := rfl

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

end Erdos101PlaneChambers

namespace Erdos101Melchior
open Erdos101PlaneChambers EuclideanGeometry Finset
open scoped Classical
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

def count (S : Finset ℝ²) (k : ℕ) := ((determined S).filter (fun L => mult S L=k)).card

theorem count_eq (S : Finset ℝ²) (k : ℕ) : count S k=(linesWithPointsFor k (S : Set ℝ²)).ncard := by
  have eq : (↑((determined S).filter (fun L => mult S L=k)) : Set Line)=linesWithPointsFor k (S : Set ℝ²) := by
    ext L
    have coe : (incident S L : Set ℝ²)=(L : Set ℝ²) ∩ S := by ext p; simp [incident,and_comm]
    simp only [Finset.mem_coe,Finset.mem_filter,mem_determined,linesWithPointsFor,Set.mem_ofPred_eq,
      mult,← Set.ncard_coe_finset,coe]
    simp [exists_prop]
  rw [← eq,Set.ncard_coe_finset,count]

end Erdos101Melchior

/- A finite set closed under a mixed linear operation on distinct inputs
has at most three elements, unless its size is exceptional in the ground
characteristic. The proof counts the missing value of each injective row
and compares the first three power sums. -/
namespace Erdos101RestrictedSums
open Finset Polynomial
open scoped Classical

variable {K : Type*} [Field K]

private theorem missing {A : Finset K} {u v d x : K} (v0 : v≠0) (hx : x∈A)
    (closed : ∀x∈A,∀y∈A,x≠y → u*x+(v*y+d)∈A) :
    ∃ z : K, ∀ H : K → K, (∑ y∈A,H (u*x+(v*y+d)))+H z=(∑ y∈A,H y)+H ((u+v)*x+d) := by
  classical
  let g (y : K) := u*x+(v*y+d)
  let I := (A.erase x).image g
  have inj : Function.Injective g := fun a b h => mul_left_cancel₀ v0 (add_right_cancel (add_left_cancel h))
  have sub : I⊆A := by
    intro w hw
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    exact closed x hx y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1.symm
  have card : I.card+1=A.card := by
    rw [show I.card=(A.erase x).card from Finset.card_image_of_injective _ inj]
    exact Finset.card_erase_add_one hx
  have part := Finset.card_sdiff_add_card_eq_card sub
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp (show (A\I).card=1 by omega)
  refine ⟨z,?_⟩
  intro H
  have sums := Finset.sum_sdiff sub (f:=H)
  rw [hz,Finset.sum_singleton] at sums
  have im : ∑ t∈I,H t=∑ y∈A.erase x,H (g y) := Finset.sum_image (fun _ _ _ _ e => inj e)
  have er := Finset.sum_erase_add (s:=A) (fun y => H (g y)) hx
  rw [im] at sums
  have val : (u+v)*x+d=g x := by dsimp [g]; ring
  rw [val]
  change (∑y∈A,H (g y))+H z=_
  rw [←er,←sums]
  abel

private def affinePoly (v b : K) : K[X] := C v*X+C b

private theorem linDeg (v b : K) : (affinePoly v b).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le (by simpa using natDegree_C_mul_X_pow_le v 1) (by simp)

private theorem leading (a b : K) (r : ℕ) : ((affinePoly a b)^r).coeff r=a^r := by
  have h := coeff_pow_of_natDegree_le (m:=r) (linDeg a b)
  simpa [affinePoly] using h

private theorem top_moment {A : Finset K} {u v d : K} (v0 : v≠0)
    (closed : ∀x∈A,∀y∈A,x≠y → u*x+(v*y+d)∈A) {r : ℕ} (rp : 0<r) (small : r<A.card) :
    ((u+v)-(A.card:K)*u)^r+(A.card:K)*u^r-(u+v)^r=0 := by
  classical
  let m : K := A.card
  let k := (u+v)-m*u
  let c := (1-v)*(∑ y∈A,y)+(1-m)*d
  let P : K[X] := (affinePoly k c)^r + ∑ y∈A,(affinePoly u (v*y+d))^r -
    (affinePoly (u+v) d)^r - C (∑ y∈A,y^r)
  have power (a b : K) : ((affinePoly a b)^r).natDegree ≤ r :=
    natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left r (linDeg a b))
  have nd : P.natDegree ≤ r := by
    apply (natDegree_sub_le ..).trans (max_le _ _)
    · apply (natDegree_sub_le ..).trans (max_le _ _)
      · exact natDegree_add_le_of_degree_le (power ..) ((natDegree_sum_le ..).trans (Finset.sup_le (fun y _ => power ..)))
      · exact power ..
    · rw [natDegree_C]; exact Nat.zero_le _
  have van (x) (hx : x∈A) : P.eval x=0 := by
    obtain ⟨z,miss⟩ := missing v0 hx closed
    have first := miss id
    simp only [id_eq,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at first
    have sm : v*(∑y∈A,y)=∑y∈A,v*y := Finset.mul_sum ..
    rw [←sm] at first
    have eq : z=k*x+c := by
      dsimp [k,c,m]; linear_combination first
    have rest := miss (fun y => y^r)
    rw [eq] at rest
    simp only [P,affinePoly,eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_finsetSum]
    linear_combination rest
  have eq : P=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P A van (nd.trans_lt small)
  have top := congrArg (fun f : K[X] => f.coeff r) eq
  simp only [P,coeff_sub,coeff_add,finsetSum_coeff,leading,coeff_C,if_neg rp.ne',coeff_zero,sub_zero,
    Finset.sum_const,nsmul_eq_mul] at top
  exact top

/-- In any field the first three power sums leave only the residues 0, 1,
and -1 as possible cardinalities for a restricted-sum closed set of size ≥4. -/
theorem affine_card_residue {A : Finset K} {u v d : K} (u0 : u≠0) (v0 : v≠0)
    (closed : ∀x∈A,∀y∈A,x≠y → u*x+(v*y+d)∈A) (four : 4≤A.card) :
    (A.card:K)=0 ∨ (A.card:K)=1 ∨ (A.card:K)=-1 := by
  let m : K := A.card
  let t := u+v
  by_cases mz : m=0
  · exact Or.inl mz
  have e2 : (t-m*u)^2+m*u^2-t^2=0 := top_moment v0 closed (by decide : 0<2) (by omega)
  have e3 : (t-m*u)^3+m*u^3-t^3=0 := top_moment v0 closed (by decide : 0<3) (by omega)
  have a : (m*u)*((m+1)*u-2*t)=0 := by linear_combination e2
  have b := (mul_eq_zero.mp a).resolve_left (mul_ne_zero mz u0)
  have c : (m*u^3)*((m-1)*(m+1))=0 := by
    linear_combination -4*e3+3*m*u*(2*t-(m-1)*u)*b
  have z := (mul_eq_zero.mp c).resolve_left (mul_ne_zero mz (pow_ne_zero _ u0))
  rcases mul_eq_zero.mp z with h|h
  · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

/-- Over a prime field, four indices on a line subject to a mixed
restricted-sum law force all but at most one of the field elements onto it. -/
theorem affine_prime_full {p : ℕ} [Fact p.Prime] {A : Finset (ZMod p)} {u v d : ZMod p}
    (u0 : u≠0) (v0 : v≠0) (closed : ∀x∈A,∀y∈A,x≠y → u*x+(v*y+d)∈A) (four : 4≤A.card) :
    p ≤ A.card+1 := by
  by_contra! small
  have k : A.card<p := by omega
  have val : ((A.card : ZMod p)).val=A.card := ZMod.val_natCast_of_lt k
  rcases affine_card_residue u0 v0 closed four with h|h|h
  · rw [h,ZMod.val_zero] at val; omega
  · rw [h,ZMod.val_one] at val; omega
  · have eq : ((A.card+1 : ℕ) : ZMod p)=0 := by push_cast; rw [h]; ring
    have z := (ZMod.natCast_eq_zero_iff ..).mp eq
    exact (Nat.not_dvd_of_pos_of_lt (by omega) small) z

theorem card_residue {A : Finset K} {u v : K} (u0 : u≠0) (v0 : v≠0)
    (closed : ∀x∈A,∀y∈A,x≠y → u*x+v*y∈A) (four : 4≤A.card) :
    (A.card:K)=0 ∨ (A.card:K)=1 ∨ (A.card:K)=-1 :=
  affine_card_residue (d:=0) u0 v0 (by simpa using closed) four

theorem prime_full {p : ℕ} [Fact p.Prime] {A : Finset (ZMod p)} {u v : ZMod p}
    (u0 : u≠0) (v0 : v≠0) (closed : ∀x∈A,∀y∈A,x≠y → u*x+v*y∈A) (four : 4≤A.card) :
    p ≤ A.card+1 := affine_prime_full (d:=0) u0 v0 (by simpa using closed) four

end Erdos101RestrictedSums

/- A nontrivial homogeneous linear parametrization of collinear triples
in a prime-indexed orbit is incompatible with four points on a line and
two more points outside it. -/
namespace Erdos101CyclicLaws
open EuclideanGeometry Finset Erdos101PlaneChambers Erdos101Melchior
open scoped Classical

variable {p : ℕ} [Fact p.Prime]
abbrev F (p : ℕ) := ZMod p
abbrev V (p : ℕ) := Fin 3 → F p

def richOrbit (f : F p → ℝ²) := ∃ a b : ℝ²,
  4 ≤ (Finset.univ.filter (fun i => f i∈line[ℝ,a,b])).card ∧
  2 ≤ (Finset.univ.filter (fun i => f i∉line[ℝ,a,b])).card

def law (f : F p → ℝ²) (u v : F p) :=
  ∀ x y, Collinear ℝ ({f x,f y,f (u*x+v*y)} : Set ℝ²)

private theorem not_all_on_line {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    (u v : ℝ²) : ¬∀i,f i∈line[ℝ,u,v] := by
  obtain ⟨a,b,h1,h2⟩ := rich
  obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1<4) h1)
  have ia := (Finset.mem_filter.mp hi).2
  have ja := (Finset.mem_filter.mp hj).2
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) h2)
  intro all
  have eq := (affineSpan_pair_eq_of_mem_of_mem_of_ne ia ja (inj.ne ne)).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne (all i) (all j) (inj.ne ne))
  exact (Finset.mem_filter.mp hz).2 (eq ▸ all z)

theorem trivial_law {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {u v : F p} (h : law f u v) : (u=1 ∧ v=0) ∨ (u=0 ∧ v=1) := by
  by_cases v0 : v=0
  · refine Or.inl ⟨?_,v0⟩
    by_contra u1
    apply not_all_on_line inj rich (f 1) (f u)
    intro y
    have col := h 1 y
    simp only [v0,zero_mul,mul_one,add_zero] at col
    exact col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (inj.ne (Ne.symm u1))
  by_cases u0 : u=0
  · refine Or.inr ⟨u0,?_⟩
    by_contra v1
    apply not_all_on_line inj rich (f 1) (f v)
    intro x
    have col := h x 1
    simp only [u0,zero_mul,mul_one,zero_add] at col
    exact col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (inj.ne (Ne.symm v1))
  exfalso
  obtain ⟨a,b,h1,h2⟩ := rich
  let A := Finset.univ.filter (fun i => f i∈line[ℝ,a,b])
  have closed (x) (hx : x∈A) (y) (hy : y∈A) (xy : x≠y) : u*x+v*y∈A := by
    have m := (h x y).mem_affineSpan_of_mem_of_ne (p₁:=f x) (p₂:=f y) (p₃:=f (u*x+v*y))
      (by simp) (by simp) (by simp) (inj.ne xy)
    rw [affineSpan_pair_eq_of_mem_of_mem_of_ne (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (inj.ne xy)] at m
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,m⟩
  have upper := Erdos101RestrictedSums.prime_full u0 v0 closed h1
  have sum := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => f i∈line[ℝ,a,b])
  rw [Finset.card_univ,ZMod.card] at sum
  change p ≤ A.card+1 at upper
  change A.card+_=p at sum
  omega

def triple (f : F p → ℝ²) (w : V p) := Collinear ℝ (Set.range (fun i => f (w i)))

/-- A family of triples closed under homogeneous linear combinations cannot
contain two different tuples with the same nonzero first entry. -/
theorem fiber_unique {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {w z : V p} (diff : Function.Injective w) (nonzero : w 0≠0) (same : z 0=w 0)
    (all : ∀a b : F p,triple f (fun i => a*w i+b*z i)) : w=z := by
  have cannot (j k : Fin 3) (jk : j≠k) (k0 : k≠0) (changeJ : z j≠w j) : False := by
    let d (i : Fin 3) := z i-w i
    have dj : d j≠0 := sub_ne_zero.mpr changeJ
    have d0 : d 0=0 := sub_eq_zero.mpr same
    let v := d k/d j
    let u := (w k-v*w j)/w 0
    have hits : law f u v := by
      intro x y
      let r := x/w 0
      let s := (y-r*w j)/d j
      let q (i : Fin 3) := (r-s)*w i+s*z i
      have form (i) : q i=r*w i+s*d i := by dsimp [q,d]; ring
      have a0 : q 0=x := by rw [form,d0,mul_zero,add_zero]; exact div_mul_cancel₀ _ nonzero
      have aj : q j=y := by rw [form,show s*d j=y-r*w j from div_mul_cancel₀ _ dj]; ring
      have ak : q k=u*x+v*y := by rw [form]; dsimp [u,v,s,r]; field_simp [nonzero,dj]; ring
      have col := all (r-s) s
      apply col.subset
      intro t ht
      change t∈Set.range (fun i => f (q i))
      rcases ht with e|e|e
      · exact ⟨0,(congrArg f a0).trans e.symm⟩
      · exact ⟨j,(congrArg f aj).trans e.symm⟩
      · exact ⟨k,(congrArg f ak).trans e.symm⟩
    have agree : u*w 0+v*w j=w k := by dsimp [u]; rw [div_mul_cancel₀ _ nonzero]; ring
    rcases trivial_law inj rich hits with ⟨h1,h2⟩|⟨h1,h2⟩
    · simp [h1,h2] at agree
      exact k0 (diff agree.symm)
    · simp [h1,h2] at agree
      exact jk (diff agree)
  funext i
  fin_cases i
  · exact same.symm
  · by_contra h
    exact cannot 1 2 (by decide) (by decide) (Ne.symm h)
  · by_contra h
    exact cannot 2 1 (by decide) (by decide) (Ne.symm h)

end Erdos101CyclicLaws

/- A zero-sum rational relation between prime-order roots of unity
remains a relation whenever its equal exponents stay equal. -/
namespace Erdos101Cyclotomic
open Polynomial Finset
open scoped Classical ComplexConjugate

variable {p : ℕ} [Fact p.Prime]
abbrev chi (e : ZMod p) : ℂ := ZMod.stdAddChar e

lemma chi_nat (n : ℕ) : chi (n : ZMod p)=chi (1:ZMod p)^n := by
  simpa [chi,nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow n (1 : ZMod p)

lemma chi_val (e : ZMod p) : chi (1:ZMod p)^e.val=chi e := by
  rw [←chi_nat,ZMod.natCast_zmod_val]

lemma chi_neg (t : ZMod p) : chi (-t)=conj (chi t) := by
  change (↑(ZMod.toCircle (-t)) : ℂ)=conj (↑(ZMod.toCircle t) : ℂ)
  rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

lemma primitive : IsPrimitiveRoot (chi (1:ZMod p)) p := by
  constructor
  · rw [←chi_nat,ZMod.natCast_self]; exact ZMod.stdAddChar.map_zero_eq_one
  · intro n h
    rw [←chi_nat] at h
    exact (ZMod.natCast_eq_zero_iff ..).mp (ZMod.injective_stdAddChar (h.trans ZMod.stdAddChar.map_zero_eq_one.symm))

variable {J : Type*} [Fintype J]

/-- Every exponent has coefficient sum zero when the relation vanishes
both at a primitive root and at one. -/
theorem group_zero {a : J → ℚ} {e : J → ZMod p} (aug : ∑ j,a j=0)
    (van : ∑ j,(a j:ℂ)*chi (e j)=0) (r : ZMod p) : ∑ j with e j=r,a j=0 := by
  classical
  let P : ℚ[X] := ∑ j,C (a j)*X^(e j).val
  have one : P.eval 1=0 := by simpa [P,eval_finsetSum] using aug
  have z : aeval (chi (1:ZMod p)) P=0 := by simpa [P,chi_val] using van
  have hp : Nat.Prime p := Fact.out
  have nd : P.natDegree≤p-1 := by
    apply (natDegree_sum_le ..).trans (Finset.sup_le (fun j _ => ?_))
    exact (natDegree_C_mul_X_pow_le ..).trans (by have := (e j).val_lt; omega)
  have divides := minpoly.dvd ℚ _ z
  rw [←primitive.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hp.pos)] at divides
  have eq : P=0 := by
    obtain ⟨Q,fact⟩ := divides
    by_contra hn
    have qn : Q≠0 := fun h => hn (by simp [fact,h])
    rw [fact,natDegree_mul (cyclotomic_ne_zero p ℚ) qn,natDegree_cyclotomic,Nat.totient_prime hp] at nd
    have qc := eq_C_of_natDegree_eq_zero (show Q.natDegree=0 by omega)
    rw [fact,eval_mul,eval_one_cyclotomic_prime,qc,eval_C] at one
    have zero := (mul_eq_zero.mp one).resolve_left (by exact_mod_cast hp.ne_zero)
    exact qn (qc.trans (by simp [zero]))
  have cf := congrArg (fun q : ℚ[X] => q.coeff r.val) eq
  simp only [P,finsetSum_coeff,coeff_C_mul_X_pow,coeff_zero,(ZMod.val_injective p).eq_iff] at cf
  simpa only [Finset.sum_filter,eq_comm] using cf

/-- Coarsening the equality relation among exponents preserves vanishing. -/
theorem transfer {a : J → ℚ} {e d : J → ZMod p} (aug : ∑ j,a j=0)
    (van : ∑ j,(a j:ℂ)*chi (e j)=0) (coarse : ∀i j,e i=e j → d i=d j) :
    ∑ j,(a j:ℂ)*chi (d j)=0 := by
  classical
  rw [←Finset.sum_fiberwise Finset.univ e (fun j => (a j:ℂ)*chi (d j))]
  apply Finset.sum_eq_zero
  intro r _
  by_cases h : ∃ j,e j=r
  · obtain ⟨i,hi⟩ := h
    calc
      _ = ∑ j with e j=r,(a j:ℂ)*chi (d i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [coarse j i ((Finset.mem_filter.mp hj).2.trans hi.symm)]
      _ = (↑(∑ j with e j=r,a j) : ℂ)*chi (d i) := by rw [Rat.cast_sum,Finset.sum_mul]
      _ = 0 := by simp [group_zero aug van r]
  · apply Finset.sum_eq_zero
    intro j hj
    exact (h ⟨j,(Finset.mem_filter.mp hj).2⟩).elim

end Erdos101Cyclotomic

/- Rational sparse Fourier parametrizations of the plane: the exponent
collision pattern of a collinear triple gives a whole subspace of such triples. -/
namespace Erdos101CyclicFourier
open Erdos101CyclicLaws Erdos101Cyclotomic Erdos101PlaneChambers EuclideanGeometry Finset
open scoped ComplexConjugate Classical

variable {p k : ℕ} [Fact p.Prime]

def pack (a : ℝ²) : ℂ := ⟨a 0,a 1⟩
def pair (a b : ℝ²) := pack a*conj (pack b)
def orient (a b c : ℝ²) := pair a b+pair b c+pair c a-(pair b a+pair c b+pair a c)

private lemma real_zero (a b c : ℝ²) : (orient a b c).re=0 := by
  simp [orient,pair,pack,Complex.add_re,Complex.sub_re,Complex.mul_re]; ring
private lemma imaginary (a b c : ℝ²) : (orient a b c).im=(-2)*ev c (normal a b) := by
  simp [orient,pair,pack,Complex.add_im,Complex.sub_im,Complex.mul_im,ev_apply,normal]; ring

lemma geometric (a b c : ℝ²) : Collinear ℝ ({c,a,b}:Set ℝ²) ↔ orient a b c=0 := by
  have eq : orient a b c=0 ↔ ev c (normal a b)=0 := by
    constructor
    · intro h; have hi := imaginary a b c; rw [h,Complex.zero_im] at hi; linarith
    · intro h; apply Complex.ext
      · exact real_zero ..
      · rw [imaginary,h,Complex.zero_im,mul_zero]
  rw [eq]
  by_cases same : a=b
  · subst b; simp [ev_apply,normal,collinear_pair]
  rw [on_line same]
  exact ⟨fun h => h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) same,
    collinear_insert_of_mem_affineSpan_pair⟩

def parametrizes (f : F p → ℝ²) (c : Fin k → ℚ) (e : Fin k → F p) :=
  ∀ x,pack (f x)=∑ j,(c j : ℂ)*chi (e j*x)

lemma chi_sub (x y : F p) : chi (x-y)=chi x*conj (chi y) := by
  rw [sub_eq_add_neg,show chi (x+ -y)=chi x*chi (-y) from ZMod.stdAddChar.map_add_eq_mul ..,chi_neg]

private lemma product_expansion {f : F p → ℝ²} {c : Fin k → ℚ} {e : Fin k → F p}
    (rep : parametrizes f c e) (x y : F p) :
    pair (f x) (f y)=∑ j,∑ l,((c j*c l : ℚ):ℂ)*chi (e j*x-e l*y) := by
  unfold pair
  rw [rep x,rep y,map_sum,Finset.sum_mul]
  simp only [map_mul,map_ratCast,Finset.mul_sum,Rat.cast_mul,chi_sub]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _; ring

abbrev Term (k : ℕ) := Bool × Fin 3 × Fin k × Fin k

def weight (c : Fin k → ℚ) (t : Term k) :=
  if t.1 then c t.2.2.1*c t.2.2.2 else -(c t.2.2.1*c t.2.2.2)

def exponent (e : Fin k → F p) (w : V p) (t : Term k) : F p :=
  let i := t.2.1
  if t.1 then e t.2.2.1*w i-e t.2.2.2*w (i+1)
  else e t.2.2.1*w (i+1)-e t.2.2.2*w i

lemma weight_sum (c : Fin k → ℚ) : ∑ t : Term k, weight c t=0 := by
  simp [weight,Fintype.sum_prod_type,Finset.sum_neg_distrib]

private lemma expansion {f : F p → ℝ²} {c : Fin k → ℚ} {e : Fin k → F p}
    (rep : parametrizes f c e) (w : V p) :
    orient (f (w 0)) (f (w 1)) (f (w 2))=∑ t : Term k,(weight c t : ℂ)*chi (exponent e w t) := by
  simp [orient,product_expansion rep,weight,exponent,Fintype.sum_prod_type,
    Fin.sum_univ_three,Finset.sum_neg_distrib,show (0+1:Fin 3)=1 by decide,
    show (1+1:Fin 3)=2 by decide,show (2+1:Fin 3)=0 by decide]
  abel

lemma characterize {f : F p → ℝ²} {c : Fin k → ℚ} {e : Fin k → F p}
    (rep : parametrizes f c e) (w : V p) :
    triple f w ↔ ∑ t : Term k,(weight c t : ℂ)*chi (exponent e w t)=0 := by
  have range : Set.range (fun i => f (w i))=({f (w 2),f (w 0),f (w 1)} : Set ℝ²) := by
    ext a; constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp
    · rintro (h|h|h)
      · exact ⟨2,h.symm⟩
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
  rw [triple,range,geometric,expansion rep]

lemma linear_exp (e : Fin k → F p) (w z : V p) (a b : F p) (t : Term k) :
    exponent e (fun i => a*w i+b*z i) t=a*exponent e w t+b*exponent e z t := by
  cases h : t.1 <;> simp [exponent,h] <;> ring

def pattern (e : Fin k → F p) (w : V p) :=
  Finset.univ.filter (fun t : Term k × Term k => exponent e w t.1=exponent e w t.2)

/-- On any pattern shared with a collinear triple, all linear combinations
of the two parameter triples stay collinear. -/
theorem span_collinear {f : F p → ℝ²} {c : Fin k → ℚ} {e : Fin k → F p}
    (rep : parametrizes f c e) {w z : V p} (col : triple f w) (same : pattern e w=pattern e z)
    (a b : F p) : triple f (fun i => a*w i+b*z i) := by
  apply (characterize rep _).mpr
  apply transfer (weight_sum c) ((characterize rep _).mp col)
  intro i j h
  have mem : (i,j)∈pattern e w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  rw [same] at mem
  have h' : exponent e z i=exponent e z j := (Finset.mem_filter.mp mem).2
  rw [linear_exp,linear_exp,h,h']

end Erdos101CyclicFourier

/- A nonzero rational character sum on a linear space has its zeros
on at most one proper hyperplane per term. Two cuts suffice to count
nonzero leading coordinates of genuine collinear triples. -/
namespace Erdos101CyclicCuts
open EuclideanGeometry Erdos101CyclicLaws Erdos101Cyclotomic Erdos101CyclicFourier Finset Module
open scoped Classical
variable {p k : ℕ} [Fact p.Prime]
variable {J : Type*} [Fintype J]

/-- A nonzero weighted sum detects some nonzero sum over a fiber. -/
lemma exposed {B : Type*} (a : J → ℚ) (g : J → B) (h : B → ℂ)
    (nz : ∑ j,(a j:ℂ)*h (g j)≠0) : ∃ i,∑ j with g j=g i,a j≠0 := by
  classical
  by_contra! none
  apply nz
  rw [←Finset.sum_fiberwise_of_maps_to (t:=Finset.univ.image g) (fun j hj => Finset.mem_image_of_mem g hj)]
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
  calc
    _=∑ j with g j=g i,(a j:ℂ)*h (g i) := by
      apply Finset.sum_congr rfl
      intro j hj; rw [(Finset.mem_filter.mp hj).2]
    _=(↑(∑ j with g j=g i,a j):ℂ)*h (g i) := by rw [Rat.cast_sum,Finset.sum_mul]
    _=0 := by rw [none i]; simp

lemma crossing {B : Type*} (a : J → ℚ) (g : J → B) (v : J → F p) (i : J)
    (refines : ∀j,g j=g i → v j=v i) (pos : ∑ j with g j=g i,a j≠0)
    (aug : ∑j,a j=0) (zero : ∑j,(a j:ℂ)*chi (v j)=0) : ∃j,g j≠g i ∧ v j=v i := by
  classical
  by_contra! none
  have eq : Finset.univ.filter (fun j => g j=g i)=Finset.univ.filter (fun j => v j=v i) := by
    ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨refines j,fun h => by_contra fun ne => none j ne h⟩
  exact pos (eq ▸ group_zero aug zero (v i))

def form (e : Fin k → F p) (t : Term k) : V p →ₗ[F p] F p where
  toFun w := exponent e w t
  map_add' w z := by
    change exponent e (fun i => w i+z i) t=_
    simpa using linear_exp e w z 1 1 t
  map_smul' a w := by
    change exponent e (fun i => a*w i) t=a*exponent e w t
    simpa using linear_exp e w w a 0 t

private lemma cuts {f : F p → ℝ²} {c : Fin k → ℚ} {e : Fin k → F p}
    (rep : parametrizes f c e) (W : Submodule (F p) (V p)) (bad : ¬∀w∈W,triple f w) :
    ∃ U : Finset (Term k), ∃ D : Term k → Submodule (F p) (V p),
      (∀j∈U,D j<W) ∧ ∀w∈W,triple f w → ∃j∈U,w∈D j := by
  classical
  push Not at bad
  obtain ⟨z,hz,hn⟩ := bad
  let g (j : Term k) (v : W) := form e j v
  have nz : ∑j,(weight c j:ℂ)*chi (g j ⟨z,hz⟩)≠0 := fun h => hn ((characterize rep z).mpr h)
  obtain ⟨i,hi⟩ := exposed (weight c) g (fun q => chi (q ⟨z,hz⟩)) nz
  let U := Finset.univ.filter (fun j => g j≠g i)
  let D (j : Term k) := W ⊓ (form e j-form e i).ker
  refine ⟨U,D,?_,?_⟩
  · intro j hj
    apply lt_of_le_of_ne inf_le_left
    intro eq
    apply (Finset.mem_filter.mp hj).2
    funext x
    have hx : (x:V p)∈D j := by rw [show D j=W from eq]; exact x.property
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hx.2)
  · intro w hw col
    obtain ⟨j,diff,same⟩ := crossing (weight c) g (fun j => form e j w) i
      (fun j h => congrFun h ⟨w,hw⟩) hi (weight_sum c) ((characterize rep w).mp col)
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,diff⟩,hw,LinearMap.mem_ker.mpr (sub_eq_zero.mpr same)⟩

/-- Intersection with a fixed nonzero first-coordinate slice is unique in a
one-dimensional vector space. -/
private lemma slice_one {W : Submodule (F p) (V p)} (rank : finrank (F p) W≤1)
    {w z : V p} (hw : w∈W) (hz : z∈W) (nonzero : w 0≠0) (same : w 0=z 0) : w=z := by
  obtain ⟨v,h⟩ := finrank_le_one_iff.mp rank
  obtain ⟨a,ha⟩ := h ⟨w,hw⟩
  obtain ⟨b,hb⟩ := h ⟨z,hz⟩
  have la := congrArg (fun v : W => v.val 0) ha
  have lb := congrArg (fun v : W => v.val 0) hb
  change a*v.val 0=w 0 at la
  change b*v.val 0=z 0 at lb
  have vn : v.val 0≠0 := fun h => nonzero (by simpa [h] using la.symm)
  have ab := mul_right_cancel₀ vn (la.trans (same.trans lb.symm))
  exact congrArg Subtype.val (ha.symm.trans (ab ▸ hb))

/-- A family of distinct genuine collinear triples whose first entries range
over `I` has at most `(1+6k²)² |I|` members. -/
theorem bound {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {c : Fin k → ℚ} {e : Fin k → F p} (rep : parametrizes f c e) (B : Finset (V p)) (I : Finset (F p))
    (good : ∀w∈B,Function.Injective w ∧ w 0≠0 ∧ w 0∈I ∧ triple f w) :
    B.card ≤ (1+6*k^2)^2*I.card := by
  classical
  let m := 1+Fintype.card (Term k)
  have mp : 0 < m := by dsimp [m]; omega
  let part (W : Submodule (F p) (V p)) := B.filter (fun w => w∈W)
  have claim (d : ℕ) (W : Submodule (F p) (V p)) (dim : finrank (F p) W≤d+1) :
      (part W).card ≤ m^d*I.card := by
    induction d generalizing W with
    | zero =>
      simp only [pow_zero,one_mul]
      exact Finset.card_le_card_of_injOn (fun w => w 0)
        (fun w hw => (good w (Finset.mem_filter.mp hw).1).2.2.1) (fun w hw z hz same =>
          slice_one dim (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hz).2
            (good w (Finset.mem_filter.mp hw).1).2.1 same)
    | succ d ih =>
      by_cases all : ∀w∈W,triple f w
      · have small : (part W).card≤I.card := by
          apply Finset.card_le_card_of_injOn (fun w => w 0)
          · exact fun w hw => (good w (Finset.mem_filter.mp hw).1).2.2.1
          · intro w hw z hz same
            obtain ⟨wb,ww⟩ := Finset.mem_filter.mp hw
            obtain ⟨_,zw⟩ := Finset.mem_filter.mp hz
            exact fiber_unique inj rich (good w wb).1 (good w wb).2.1 same.symm
              (fun a b => all _ (W.add_mem (W.smul_mem a ww) (W.smul_mem b zw)))
        exact small.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos mp))
      · obtain ⟨U,D,proper,cover⟩ := cuts rep W all
        have sub : part W ⊆ U.biUnion (fun j => part (D j)) := by
          intro w hw
          obtain ⟨wb,ww⟩ := Finset.mem_filter.mp hw
          obtain ⟨j,hj,h⟩ := cover w ww (good w wb).2.2.2
          exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨wb,h⟩⟩
        have uc : U.card ≤ m := (Finset.card_le_univ U).trans (Nat.le_add_left ..)
        calc
          _ ≤ (U.biUnion (fun j => part (D j))).card := Finset.card_le_card sub
          _ ≤ ∑j∈U,(part (D j)).card := Finset.card_biUnion_le
          _ ≤ ∑_∈U,m^d*I.card := Finset.sum_le_sum (fun j hj => ih _ (by
            have less := Submodule.finrank_lt_finrank_of_lt (proper j hj); omega))
          _ = U.card*(m^d*I.card) := by simp
          _ ≤ m*(m^d*I.card) := Nat.mul_le_mul_right _ uc
          _ = m^(d+1)*I.card := by ring
  have top := claim 2 ⊤ (by simp [V,F])
  have size : m=1+6*k^2 := by simp [m,Term,pow_two]; ring
  simpa [part,size] using top

end Erdos101CyclicCuts

/- Uniformly few four-point lines in subsets of prime Fourier orbits,
with a constant depending only on the number of Fourier terms. -/
namespace Erdos101CyclicCount
open Erdos101CyclicLaws Erdos101CyclicFourier Erdos101PlaneChambers Erdos101Melchior
open EuclideanGeometry Finset
open scoped Classical
variable {p k : ℕ} [Fact p.Prime]

/-- Each four-point line has a representative given by the indices of three points,
with nonzero first entry. Any bound for such triples transfers to lines. -/
theorem from_triples {f : F p → ℝ²} (inj : Function.Injective f) (K : ℕ) (I : Finset (F p))
    (estimate : richOrbit f → ∀B : Finset (V p),
      (∀w∈B,Function.Injective w ∧ w 0≠0 ∧ (∀i,w i∈I) ∧ triple f w) → B.card≤K*I.card) :
    (linesWithPointsFor 4 (↑(I.image f) : Set ℝ²)).ncard ≤ (5+K)*I.card := by
  classical
  let S := I.image f
  let A := (determined S).filter (fun L => mult S L=4)
  have countA : A.card=(linesWithPointsFor 4 (S : Set ℝ²)).ncard := count_eq S 4
  change (linesWithPointsFor 4 (S : Set ℝ²)).ncard≤_
  rw [←countA]
  have siz : S.card=I.card := Finset.card_image_of_injective _ inj
  by_cases small : I.card≤5
  · calc A.card ≤ (determined S).card := Finset.card_filter_le ..
         _ ≤ S.offDiag.card := Finset.card_image_le
         _ ≤ I.card*I.card := by rw [Finset.offDiag_card,siz]; omega
         _ ≤ (5+K)*I.card := Nat.mul_le_mul_right _ (small.trans (Nat.le_add_right ..))
  by_cases has : A.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp has]
  let indices (L : Line) := I.filter (fun t => f t∈L)
  have nc (L : Line) : (indices L).card=mult S L := by
    have eq : (indices L).image f=incident S L := by
      ext a
      simp [indices,incident,S,Finset.mem_image]
      aesop
    rw [mult,←eq,Finset.card_image_of_injective _ inj]
  have rich : richOrbit f := by
    obtain ⟨L,hL⟩ := has
    obtain ⟨proper,nfour⟩ := Finset.mem_filter.mp hL
    obtain ⟨a,_,b,_,_,rfl⟩ := mem_determined.mp proper
    have sz : (indices (line[ℝ,a,b])).card=4 := (nc _).trans nfour
    refine ⟨a,b,?_,?_⟩
    · rw [←sz]; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ I))
    · have parts := Finset.card_filter_add_card_filter_not (s:=I) (fun i => f i∈line[ℝ,a,b])
      change (indices (line[ℝ,a,b])).card+_=I.card at parts
      exact (show 2≤(I.filter (fun i => f i∉line[ℝ,a,b])).card by omega).trans
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ I)))
  have choose (L : A) : ∃ w : V p, Function.Injective w ∧ w 0≠0 ∧ (∀ i,w i∈indices L.val) := by
    have n : (indices L.val).card=4 := (nc _).trans (Finset.mem_filter.mp L.property).2
    let B := (indices L.val).erase 0
    have three : 3≤B.card := by
      by_cases h : (0:F p)∈indices L.val
      · have := Finset.card_erase_add_one h; change 3≤((indices L.val).erase 0).card; omega
      · simp [B,Finset.erase_eq_of_notMem h,n]
    let width : Fin 3 ↪ Fin B.card := Fin.castLEEmb three
    let w (i : Fin 3) : F p := (B.equivFin.symm (width i)).val
    have diff : Function.Injective w := Subtype.val_injective.comp (B.equivFin.symm.injective.comp width.injective)
    have inside (i : Fin 3) := Finset.mem_erase.mp (B.equivFin.symm (width i)).property
    exact ⟨w,diff,(inside 0).1,fun i => (inside i).2⟩
  choose w diff nonzero on using choose
  have proper (L : A) : L.val∈determined S := (Finset.mem_filter.mp L.property).1
  have hits (L : A) (i : Fin 3) : f (w L i)∈L.val := (Finset.mem_filter.mp (on L i)).2
  have col (L : A) : triple f (w L) := by
    obtain ⟨a,_,b,_,_,eq⟩ := mem_determined.mp (proper L)
    apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
    refine ⟨a,b -ᵥ a,?_⟩
    rintro q ⟨i,rfl⟩
    obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (eq ▸ hits L i)
    exact ⟨t,ht.symm⟩
  have winj : Function.Injective w := by
    intro L M eq
    have ne := inj.ne ((diff L).ne (show (0:Fin 3)≠1 by decide))
    have l1 := unique_line (proper L) (hits L 0) (hits L 1) ne
    have l2 := unique_line (proper M) (hits M 0) (hits M 1) (eq ▸ ne)
    rw [←eq] at l2
    exact Subtype.ext (l1.symm.trans l2)
  let B := Finset.univ.image w
  have good (z) (hz : z∈B) : Function.Injective z ∧ z 0≠0 ∧ (∀i,z i∈I) ∧ triple f z := by
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨diff L,nonzero L,fun i => (Finset.mem_filter.mp (on L i)).1,col L⟩
  have result := estimate rich B good
  have card : B.card=A.card := by simp [B,Finset.card_image_of_injective _ winj]
  rw [card] at result
  exact result.trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..))

/-- The number of four-point lines is linear in the sample size and at most
quartic in the number of Fourier terms. The frequencies and the prime
order of the orbit are unrestricted. -/
theorem four_bound {f : F p → ℝ²} (inj : Function.Injective f)
    {c : Fin k → ℚ} {e : Fin k → F p} (rep : parametrizes f c e) (I : Finset (F p)) :
    (linesWithPointsFor 4 (↑(I.image f) : Set ℝ²)).ncard ≤ (5+(1+6*k^2)^2)*I.card := by
  apply from_triples inj
  intro rich B good
  exact Erdos101CyclicCuts.bound inj rich rep B I (fun w hw =>
    ⟨(good w hw).1,(good w hw).2.1,(good w hw).2.2.1 0,(good w hw).2.2.2⟩)

end Erdos101CyclicCount

/- A sparse prime Fourier representation covering all but a vanishing
fraction of the points also gives the little-o estimate for the full set. -/
namespace Erdos101CyclicNear
open Erdos101CyclicLaws Erdos101CyclicFourier Erdos101PlaneChambers Erdos101Melchior
open EuclideanGeometry Finset Filter Asymptotics
open scoped Classical Topology
variable {p k : ℕ} [Fact p.Prime]

/-- Every lost four-point line is determined by an exceptional point and
one further point of the original set. -/
theorem delete_points {S T : Finset ℝ²} (sub : T⊆S) : count S 4≤count T 4+(S\T).card*S.card := by
  classical
  let A (U : Finset ℝ²) := (determined U).filter (fun L => mult U L=4)
  let bad := A S\A T
  have choose (L : bad) : ∃q∈S\T,∃r∈S,q≠r ∧ q∈L.val ∧ r∈L.val := by
    obtain ⟨hl,miss⟩ := Finset.mem_sdiff.mp L.property
    obtain ⟨prop,size⟩ := Finset.mem_filter.mp hl
    have gone : ∃q∈incident S L.val,q∉T := by
      by_contra! all
      have eq : incident S L.val=incident T L.val := by
        apply Finset.Subset.antisymm _ (Finset.filter_subset_filter _ sub)
        intro q h; exact Finset.mem_filter.mpr ⟨all q h,(Finset.mem_filter.mp h).2⟩
      have two : 1<(incident T L.val).card := by rw [←eq]; change 1 < mult S L.val; omega
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp two
      obtain ⟨at',al⟩ := Finset.mem_filter.mp ha
      obtain ⟨bt,bl⟩ := Finset.mem_filter.mp hb
      apply miss
      exact Finset.mem_filter.mpr ⟨mem_determined.mpr ⟨a,at',b,bt,ne,unique_line prop al bl ne⟩,
        (congrArg Finset.card eq).symm.trans size⟩
    obtain ⟨q,hq,qt⟩ := gone
    have er := Finset.card_erase_add_one hq
    change (incident S L.val).card=4 at size
    obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0<((incident S L.val).erase q).card by omega)
    obtain ⟨rq,ri⟩ := Finset.mem_erase.mp hr
    exact ⟨q,Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hq).1,qt⟩,r,(Finset.mem_filter.mp ri).1,
      rq.symm,(Finset.mem_filter.mp hq).2,(Finset.mem_filter.mp ri).2⟩
  choose q qs r rs ne ql rl using choose
  let key (L : bad) := (q L,r L)
  have inj : Function.Injective key := by
    intro L M he
    have proper (N : bad) := (Finset.mem_filter.mp (Finset.mem_sdiff.mp N.property).1).1
    have e1 := unique_line (proper L) (ql L) (rl L) (ne L)
    have e2 := unique_line (proper M) (ql M) (rl M) (ne M)
    have pair := congrArg (fun z : ℝ² × ℝ² => line[ℝ,z.1,z.2]) he
    exact Subtype.ext (e1.symm.trans (pair.trans e2))
  have inside : Finset.univ.image key ⊆ (S\T) ×ˢ S := by
    rintro z hz; obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨qs L,rs L⟩
  have h := Finset.card_le_card inside
  simp only [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_coe,Finset.card_product] at h
  have part := Finset.card_sdiff_add_card_inter (A S) (A T)
  have kept := Finset.card_le_card (Finset.inter_subset_right (s₁:=A S) (s₂:=A T))
  change (A S).card≤(A T).card+_
  dsimp only [bad] at h
  omega

theorem near_bound {f : F p → ℝ²} (inj : Function.Injective f) {c : Fin k → ℚ}
    {e : Fin k → F p} (rep : parametrizes f c e) {I : Finset (F p)} {S : Finset ℝ²}
    (sub : I.image f⊆S) : (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤
      (5+(1+6*k^2)^2+(S\I.image f).card)*S.card := by
  rw [←count_eq]
  have cyl := Erdos101CyclicCount.four_bound inj rep I
  rw [←count_eq] at cyl
  have num : I.card≤S.card := (Finset.card_image_of_injective I inj) ▸ Finset.card_le_card sub
  have keep := cyl.trans (Nat.mul_le_mul_left _ num)
  exact (delete_points sub).trans (by rw [Nat.add_mul]; omega)

/-- All but `b` points belong to an injectively indexed prime orbit with
`k` Fourier terms. The prime, frequencies and coefficients can vary. -/
def covered (S : Finset ℝ²) (k b : ℕ) := ∃ (p : ℕ) (hp : p.Prime),
  letI : Fact p.Prime := ⟨hp⟩
  ∃ (f : F p → ℝ²) (c : Fin k → ℚ) (e : Fin k → F p) (I : Finset (F p)),
    Function.Injective f ∧ parametrizes f c e ∧ I.image f⊆S ∧ (S\I.image f).card≤b

theorem covered_bound {S : Finset ℝ²} {k b : ℕ} (h : covered S k b) :
    (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤ (5+(1+6*k^2)^2+b)*S.card := by
  obtain ⟨p,hp,rest⟩ := h
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨f,c,e,I,inj,rep,sub,num⟩ := rest
  exact (near_bound inj rep sub).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_left num _))

/-- The Erdős 101 conclusion for arbitrary configurations admitting these
covers with `k⁴ = o(n)` and `b = o(n)`. -/
theorem littleO (S : ℕ → Finset ℝ²) (k b : ℕ → ℕ) (size : ∀n,(S n).card≤n)
    (cover : ∀n,covered (S n) (k n) (b n))
    (terms : (fun n => (k n:ℝ)^4) =o[atTop] (fun n => (n:ℝ)))
    (outliers : (fun n => (b n:ℝ)) =o[atTop] (fun n => (n:ℝ))) :
    (fun n => ((linesWithPointsFor 4 (S n : Set ℝ²)).ncard : ℝ)) =o[atTop] (fun n => (n:ℝ)^2) := by
  apply IsLittleO.of_bound
  intro ε ep
  let r := ε/128
  have rp : 0<r := by dsimp [r]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (1/r)
  filter_upwards [eventually_ge_atTop N,terms.bound rp,outliers.bound rp] with n hn hk hb
  have castN : (N:ℝ)≤n := by exact_mod_cast hn
  have one : 1≤r*(n:ℝ) := ((div_lt_iff₀ rp).mp hN).le.trans
    ((mul_le_mul_of_nonneg_right castN rp.le).trans_eq (mul_comm ..))
  change ‖(k n:ℝ)^4‖≤r*‖(n:ℝ)‖ at hk
  change ‖(b n:ℝ)‖≤r*‖(n:ℝ)‖ at hb
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg n)] at hk hb
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
  have h := (covered_bound (cover n)).trans (Nat.mul_le_mul_left _ (size n))
  have coeff : 5+(1+6*(k n:ℝ)^2)^2+b n≤ε*n := by
    have power := sq_nonneg ((k n:ℝ)^2-1)
    dsimp [r] at one hk hb
    nlinarith only [hk,hb,one,power]
  calc
    _ ≤ (5+(1+6*(k n:ℝ)^2)^2+b n)*n := by exact_mod_cast h
    _ ≤ (ε*n)*n := mul_le_mul_of_nonneg_right coeff (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos101CyclicNear

/- An affine flat of prime-indexed collinear triples with one genuine triple
is separated by one of the three coordinate projections. -/
namespace Erdos101CyclicLaws
open EuclideanGeometry Finset
open scoped Classical
variable {p : ℕ} [Fact p.Prime]

def affineLaw (f : F p → ℝ²) (u v d : F p) :=
  ∀ x y, Collinear ℝ ({f x,f y,f (u*x+(v*y+d))} : Set ℝ²)

private lemma collapsed {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    (x z : F p) (all : ∀y, Collinear ℝ ({f x,f y,f z} : Set ℝ²)) : x=z := by
  by_contra ne
  have lineAll (y) := (all y).mem_affineSpan_of_mem_of_ne (p₁:=f x) (p₂:=f z) (p₃:=f y)
    (by simp) (by simp) (by simp) (inj.ne ne)
  obtain ⟨a,b,h1,h2⟩ := rich
  obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1<4) h1)
  have eq := (affineSpan_pair_eq_of_mem_of_mem_of_ne (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (inj.ne ij)).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne (lineAll i) (lineAll j) (inj.ne ij))
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) h2)
  exact (Finset.mem_filter.mp ht).2 (eq ▸ lineAll t)

theorem trivial_affine {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {u v d : F p} (h : affineLaw f u v d) : (u=1 ∧ v=0 ∧ d=0) ∨ (u=0 ∧ v=1 ∧ d=0) := by
  by_cases v0 : v=0
  · have eq (x : F p) : x=u*x+d := collapsed inj rich _ _ (fun y => by simpa [v0] using h x y)
    have dz : d=0 := by simpa using (eq 0).symm
    exact Or.inl ⟨by simpa [dz] using (eq 1).symm,v0,dz⟩
  by_cases u0 : u=0
  · have eq (y : F p) : y=v*y+d := collapsed inj rich _ _ (fun x => by simpa [u0,Set.insert_comm] using h x y)
    have dz : d=0 := by simpa using (eq 0).symm
    exact Or.inr ⟨u0,by simpa [dz] using (eq 1).symm,dz⟩
  exfalso
  obtain ⟨a,b,h1,h2⟩ := rich
  let A := Finset.univ.filter (fun i => f i∈line[ℝ,a,b])
  have closed (x) (hx : x∈A) (y) (hy : y∈A) (xy : x≠y) : u*x+(v*y+d)∈A := by
    have m := (h x y).mem_affineSpan_of_mem_of_ne (p₁:=f x) (p₂:=f y) (p₃:=f (u*x+(v*y+d)))
      (by simp) (by simp) (by simp) (inj.ne xy)
    rw [affineSpan_pair_eq_of_mem_of_mem_of_ne (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (inj.ne xy)] at m
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,m⟩
  have upper := Erdos101RestrictedSums.affine_prime_full u0 v0 closed h1
  have sum := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => f i∈line[ℝ,a,b])
  rw [Finset.card_univ,ZMod.card] at sum
  change p≤A.card+1 at upper
  change A.card+_=p at sum
  omega

/-- With one genuine triple, two independent directions cannot stay in the
collinearity locus. The two directions are put in triangular form. -/
theorem no_plane {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {w v t : V p} (gen : Function.Injective w) {j k l : Fin 3} (jl : j≠l) (kl : k≠l)
    (lead : v j≠0) (fixed : t j=0) (tail : t k≠0)
    (all : ∀a b : F p,triple f (fun i => w i+a*v i+b*t i)) : False := by
  let B := t l/t k
  let A := (v l-B*v k)/v j
  let D := w l-A*w j-B*w k
  have h : affineLaw f A B D := by
    intro x y
    let a := (x-w j)/v j
    let b := (y-w k-a*v k)/t k
    let q (i) := w i+a*v i+b*t i
    have aj : q j=x := by dsimp [q,a]; rw [fixed,mul_zero,add_zero,div_mul_cancel₀ _ lead]; ring
    have ak : q k=y := by dsimp [q,b]; rw [div_mul_cancel₀ _ tail]; ring
    have al : q l=A*x+(B*y+D) := by dsimp [q,a,b,A,B,D]; field_simp [lead,tail]; ring
    apply (all a b).subset
    rintro z (e|e|e)
    · exact ⟨j,(congrArg f aj).trans e.symm⟩
    · exact ⟨k,(congrArg f ak).trans e.symm⟩
    · exact ⟨l,(congrArg f al).trans e.symm⟩
  have base : A*w j+(B*w k+D)=w l := by dsimp [D]; ring
  rcases trivial_affine inj rich h with ⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩
  · simp [h₁,h₂,h₃] at base; exact jl (gen base)
  · simp [h₁,h₂,h₃] at base; exact kl (gen base)

/-- Every affine space of collinear triples containing one tuple with
three distinct entries has a coordinate projection separating all points. -/
theorem flat_coordinate {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {s : AffineSubspace (F p) (V p)} {w : V p} (hw : w∈s) (gen : Function.Injective w)
    (all : ∀x∈s,triple f x) : ∃j : Fin 3, Set.InjOn (fun x : V p => x j) s := by
  classical
  by_cases one : ∀x∈s,x=w
  · exact ⟨0,fun x hx y hy _ => (one x hx).trans (one y hy).symm⟩
  push Not at one
  obtain ⟨z,hz,zw⟩ := one
  let v : V p := z-w
  obtain ⟨j,dj⟩ := Function.ne_iff.mp zw
  have vn : v j≠0 := sub_ne_zero.mpr dj
  refine ⟨j,?_⟩
  intro x hx y hy same
  by_contra xy
  let t : V p := x-y
  obtain ⟨k,dk⟩ := Function.ne_iff.mp xy
  have tn : t k≠0 := sub_ne_zero.mpr dk
  have tj : t j=0 := sub_eq_zero.mpr same
  have comp : ∃l : Fin 3,j≠l ∧ k≠l := by fin_cases j <;> fin_cases k <;> decide
  obtain ⟨l,jl,kl⟩ := comp
  apply no_plane inj rich gen jl kl vn tj tn
  intro a b
  have vd : v∈s.direction := s.vsub_mem_direction hz hw
  have td : t∈s.direction := s.vsub_mem_direction hx hy
  have member := s.vadd_mem_of_mem_direction (s.direction.add_mem (s.direction.smul_mem a vd) (s.direction.smul_mem b td)) hw
  apply all
  convert! member using 1
  ext i; change w i+a*v i+b*t i=a*v i+b*t i+w i; ring

end Erdos101CyclicLaws

/- Eliminate arbitrary complex amplitudes in a finite Fourier sum on a
prime vector space. The zero set is the simultaneous zero set of bounded
rational sums with affine exponents. The bound is independent of the prime. -/
namespace Erdos101CyclicElimination
open Erdos101CyclicLaws Erdos101Cyclotomic Finset
open scoped Classical
variable {p : ℕ} [Fact p.Prime]

abbrev Form (p : ℕ) [Fact p.Prime] := (V p →ₗ[F p] F p) × F p

def value (l : Form p) (x : V p) : F p := l.1 x+l.2

def plusConst (l : Form p) (b : F p) : Form p := (l.1,l.2+b)

structure Packet (p : ℕ) [Fact p.Prime] (J : Type) where
  coeff : J → ℚ
  freq : J → Form p

variable {J C : Type} [Fintype J]

def total (u : Packet p J) := ∑j,u.coeff j

def run (u : Packet p J) (x : V p) := ∑j,(u.coeff j:ℂ)*chi (value (u.freq j) x)

def cross (u v : Packet p J) (base : V p) : Packet p (Bool × J × J) where
  coeff t := if t.1 then u.coeff t.2.1*v.coeff t.2.2 else -(u.coeff t.2.1*v.coeff t.2.2)
  freq t := if t.1 then plusConst (v.freq t.2.2) (value (u.freq t.2.1) base)
    else plusConst (u.freq t.2.1) (value (v.freq t.2.2) base)

lemma cross_total (u v : Packet p J) (z : V p) : total (cross u v z)=0 := by
  simp [total,cross,Fintype.sum_prod_type,Finset.sum_neg_distrib]

private lemma chi_add (x y : F p) : chi (x+y)=chi x*chi y := ZMod.stdAddChar.map_add_eq_mul ..

lemma cross_run (u v : Packet p J) (z x : V p) :
    run (cross u v z) x=run u z*run v x-run v z*run u x := by
  have expansion (a b : V p) : run u a*run v b=
      ∑j,∑l,(u.coeff j:ℂ)*(v.coeff l:ℂ)*(chi (value (u.freq j) a)*chi (value (v.freq l) b)) := by
    unfold run
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro l _; ring
  have shift (l : Form p) (b : F p) : value (plusConst l b) x=value l x+b := by simp [value,plusConst,add_assoc]
  rw [mul_comm (run v z) (run u x),expansion,expansion]
  simp [run,cross,Fintype.sum_prod_type,shift,chi_add,Finset.sum_neg_distrib,sub_eq_add_neg,mul_comm]

def sizeBound : ℕ → ℕ → ℕ
  | 0,q => q
  | n+1,q => max q (sizeBound n (2*q^2))

lemma sizeBound_ge (n q : ℕ) : q ≤ sizeBound n q := by cases n <;> simp [sizeBound]

/-- A simultaneous system of rational character equations with boundedly
many tests and terms. Each test has zero coefficient sum. -/
def certified (X : Set (V p)) (tests width : ℕ) : Prop :=
  ∃ (B K : Type) (_ : Fintype B) (_ : Fintype K), Fintype.card B ≤ tests ∧ Fintype.card K ≤ width ∧
    ∃ words : B → Packet p K, (∀i,total (words i)=0) ∧ ∀x,x∈X ↔ ∀i,run (words i) x=0

def weighted (S : Finset C) (a : C → ℂ) (w : C → Packet p J) (x : V p) :=
  ∑i∈S,a i*run (w i) x

private lemma elimination_step (S : Finset C) (a : C → ℂ) (w : C → Packet p J)
    (i : C) (hi : i∈S) (z : V p) (zero : weighted S a w z=0) (x : V p) :
    weighted (S.erase i) a (fun j => cross (w i) (w j) z) x=run (w i) z*weighted S a w x := by
  classical
  let r (j : C) := cross (w i) (w j) z
  have e := Finset.sum_erase_add S (fun j => a j*run (r j) x) hi
  have self : run (r i) x=0 := by rw [show r i=cross (w i) (w i) z from rfl,cross_run]; ring
  rw [self,mul_zero,add_zero] at e
  calc
    _ = ∑j∈S,a j*run (r j) x := e
    _ = run (w i) z*weighted S a w x-run (w i) x*weighted S a w z := by
      simp only [weighted,r,cross_run,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by rw [zero,mul_zero,sub_zero]

/-- Elimination uses one vanishing input as a pivot, and removes one
complex amplitude at each step. At termination every active rational test
vanishes on the common zero set. -/
theorem eliminate (m n q : ℕ) (X : Set (V p)) (S : Finset C) (a : C → ℂ) (w : C → Packet p J)
    (character : ∀x,x∈X ↔ weighted S a w x=0) (aug : ∀i∈S,total (w i)=0)
    (height : S.card ≤ n) (length : Fintype.card J ≤ q) (num : S.card ≤ m) : certified X m (sizeBound n q) := by
  classical
  induction n generalizing J q S with
  | zero =>
    have empty : S=∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨S,J,inferInstance,inferInstance,by simpa using num,by simpa [sizeBound] using length,
      fun i => w i.val,fun i => aug _ i.property,?_⟩
    intro x; rw [character]; simp [weighted,empty]
  | succ n ih =>
    by_cases pivot : ∃z∈X,∃i∈S,run (w i) z≠0
    · obtain ⟨z,zx,i,hi,nz⟩ := pivot
      let next (j : C) := cross (w i) (w j) z
      have rep (x : V p) : x∈X ↔ weighted (S.erase i) a next x=0 := by
        rw [character,elimination_step _ _ _ _ hi _ ((character z).mp zx),mul_eq_zero]
        simp [nz]
      have depth : (S.erase i).card ≤ n := by have := Finset.card_erase_add_one hi; omega
      have width : Fintype.card (Bool × J × J) ≤ 2*q^2 := by
        simp only [Fintype.card_prod,Fintype.card_bool,pow_two]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul length length)
      have res := ih (2*q^2) (S.erase i) next rep (fun j _ => cross_total ..) depth width
        ((Finset.card_le_card (Finset.erase_subset ..)).trans num)
      obtain ⟨B,K,ib,ik,bs,ks,u,ut,ux⟩ := res
      exact ⟨B,K,ib,ik,bs,ks.trans (le_max_right ..),u,ut,ux⟩
    · push Not at pivot
      refine ⟨S,J,inferInstance,inferInstance,by simpa using num,length.trans (sizeBound_ge ..),
        fun i => w i.val,fun i => aug _ i.property,?_⟩
      intro x
      constructor
      · exact fun hx i => pivot _ hx i.val i.property
      · intro all; apply (character x).mpr
        exact Finset.sum_eq_zero (fun j hj => by rw [all ⟨j,hj⟩,mul_zero])

end Erdos101CyclicElimination

/- Count genuine collinear triples when their indices satisfy a bounded
system of rational character equations with affine exponents. -/
namespace Erdos101CyclicCells
open Erdos101CyclicLaws Erdos101CyclicElimination Erdos101Cyclotomic EuclideanGeometry Finset
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {B J : Type} [Fintype B] [Fintype J]

lemma value_affine (l : Form p) (a : F p) (x y z : V p) :
    value l (a • (x-y)+z)=a*(value l x-value l y)+value l z := by
  simp [value]; ring

private def pattern (v : B → Packet p J) (w : V p) :=
  Finset.univ.filter (fun t : B × J × J => value ((v t.1).freq t.2.1) w=value ((v t.1).freq t.2.2) w)

private def cell (v : B → Packet p J) (w : V p) : AffineSubspace (F p) (V p) where
  carrier := {z | ∀b i j,value ((v b).freq i) w=value ((v b).freq j) w →
    value ((v b).freq i) z=value ((v b).freq j) z}
  smul_vsub_vadd_mem' a x y z hx hy hz := by
    intro b i j h
    change value _ (a • (x-y)+z)=value _ (a • (x-y)+z)
    rw [value_affine,value_affine,
      hx b i j h,hy b i j h,hz b i j h]

private lemma belongs {v : B → Packet p J} {w z : V p} (same : pattern v w=pattern v z) : z∈cell v w := by
  intro b i j eq
  have mem : (b,i,j)∈pattern v w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩
  rw [same] at mem
  exact (Finset.mem_filter.mp mem).2

/-- A bounded certificate for collinearity, together with a line containing
four indices and missing two, gives a linear bound for arbitrary samples. -/
theorem count {f : F p → ℝ²} (inj : Function.Injective f) (rich : richOrbit f)
    {tests width : ℕ} (cert : certified {x | triple f x} tests width)
    (D : Finset (V p)) (I : Finset (F p)) (good : ∀w∈D, Function.Injective w ∧ (∀j,w j∈I) ∧ triple f w) :
    D.card ≤ 2^(tests*width^2)*I.card := by
  classical
  obtain ⟨B,J,ib,ij,bs,js,words,aug,character⟩ := cert
  let codes := D.image (pattern words)
  have num (c) (hc : c∈codes) : (D.filter (fun x => pattern words x=c)).card≤I.card := by
    obtain ⟨w,wd,rfl⟩ := Finset.mem_image.mp hc
    have inside (x) (hx : x∈cell words w) : triple f x := by
      apply (character x).mpr
      intro b
      exact transfer (aug b) ((character w).mp (good w wd).2.2 b) (hx b)
    obtain ⟨j,proj⟩ := flat_coordinate inj rich (belongs (w:=w) (v:=words) rfl) (good w wd).1 inside
    apply Finset.card_le_card_of_injOn (fun x => x j)
    · exact fun x hx => (good x (Finset.mem_filter.mp hx).1).2.1 j
    · intro x hx y hy eq
      exact proj (belongs (Finset.mem_filter.mp hx).2.symm) (belongs (Finset.mem_filter.mp hy).2.symm) eq
  have ceiling : codes.card ≤ 2^(tests*width^2) := by
    have sub : codes ⊆ (Finset.univ : Finset (B × J × J)).powerset := fun c _ => Finset.mem_powerset.mpr (Finset.subset_univ c)
    have le := Finset.card_le_card sub
    simp only [Finset.card_powerset,Finset.card_univ,Fintype.card_prod] at le
    rw [pow_two width]
    exact le.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul bs (Nat.mul_le_mul js js)))
  calc
    D.card = ∑c∈codes,(D.filter (fun x => pattern words x=c)).card := Finset.card_eq_sum_card_image ..
    _ ≤ ∑_∈codes,I.card := Finset.sum_le_sum num
    _ = codes.card*I.card := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ ceiling

end Erdos101CyclicCells

/- A uniform four-point line bound on every subset of an injective prime
Fourier orbit with arbitrary complex amplitudes. -/
namespace Erdos101CyclicComplex
open Erdos101CyclicLaws Erdos101Cyclotomic Erdos101CyclicFourier Erdos101CyclicCuts
open Erdos101CyclicElimination EuclideanGeometry Finset Asymptotics Filter
open scoped ComplexConjugate Classical Topology
variable {p k : ℕ} [Fact p.Prime]

def represents (f : F p → ℝ²) (c : Fin k → ℂ) (e : Fin k → F p) :=
  ∀ x,pack (f x)=∑ j,c j*chi (e j*x)

private lemma pair_sum {f : F p → ℝ²} {c : Fin k → ℂ} {e : Fin k → F p}
    (rep : represents f c e) (x y : F p) :
    pair (f x) (f y)=∑ j,∑ l,(c j*conj (c l))*chi (e j*x-e l*y) := by
  unfold pair
  rw [rep x,rep y,map_sum,Finset.sum_mul]
  simp only [map_mul,Finset.mul_sum,chi_sub]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro l _; ring

private def coefficient (c : Fin k → ℂ) (t : Term k) :=
  if t.1 then c t.2.2.1*conj (c t.2.2.2) else -(c t.2.2.1*conj (c t.2.2.2))

private lemma coefficient_zero (c : Fin k → ℂ) : ∑t,coefficient c t=0 := by
  simp [coefficient,Fintype.sum_prod_type,Finset.sum_neg_distrib]

private lemma char_eq {f : F p → ℝ²} {c : Fin k → ℂ} {e : Fin k → F p}
    (rep : represents f c e) (w : V p) :
    triple f w ↔ ∑t,coefficient c t*chi (exponent e w t)=0 := by
  have range : Set.range (fun i => f (w i))=({f (w 2),f (w 0),f (w 1)} : Set ℝ²) := by
    ext a; constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp
    · rintro (h|h|h)
      · exact ⟨2,h.symm⟩
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
  rw [triple,range,geometric]
  suffices eq : orient (f (w 0)) (f (w 1)) (f (w 2))=∑t,coefficient c t*chi (exponent e w t) by rw [eq]
  simp [orient,pair_sum rep,coefficient,exponent,Fintype.sum_prod_type,Fin.sum_univ_three,
    Finset.sum_neg_distrib,show (0+1:Fin 3)=1 by decide,show (1+1:Fin 3)=2 by decide,show (2+1:Fin 3)=0 by decide]
  abel

private def initial (e : Fin k → F p) (t : Term k) : Packet p Bool where
  coeff b := if b then 1 else -1
  freq b := if b then (form e t,0) else (0,0)

private lemma initial_total (e : Fin k → F p) (t : Term k) : total (initial e t)=0 := by
  simp [total,initial]

private lemma initial_run (e : Fin k → F p) (t : Term k) (x : V p) :
    run (initial e t) x=chi (exponent e x t)-1 := by
  simp [run,initial,value,form,chi,sub_eq_add_neg]

theorem certificate {f : F p → ℝ²} {c : Fin k → ℂ} {e : Fin k → F p} (rep : represents f c e) :
    certified {x | triple f x} (6*k^2) (sizeBound (6*k^2) 2) := by
  have card : Fintype.card (Term k)=6*k^2 := by simp [Term,pow_two]; ring
  apply eliminate (S:=Finset.univ) (a:=coefficient c) (w:=initial e)
  · intro x
    change triple f x ↔ _
    rw [char_eq rep]
    simp only [weighted,initial_run,mul_sub,mul_one,Finset.sum_sub_distrib,coefficient_zero,sub_zero]
  · exact fun i _ => initial_total ..
  · simp [card]
  · simp
  · simp [card]

def constant (k : ℕ) := 5+2^((6*k^2)*(sizeBound (6*k^2) 2)^2)

/-- A single constant works for every prime, sampling density, choice of
frequencies and complex amplitudes for this fixed number of Fourier terms. -/
theorem four_bound {f : F p → ℝ²} (inj : Function.Injective f) {c : Fin k → ℂ}
    {e : Fin k → F p} (rep : represents f c e) (I : Finset (F p)) :
    (linesWithPointsFor 4 (↑(I.image f) : Set ℝ²)).ncard ≤ constant k*I.card := by
  apply Erdos101CyclicCount.from_triples inj
  intro rich D good
  exact Erdos101CyclicCells.count inj rich (certificate rep) D I (fun w hw =>
    ⟨(good w hw).1,(good w hw).2.2.1,(good w hw).2.2.2⟩)

/-- The prime, frequencies, complex amplitudes and indices may all change
from one configuration to the next. -/
def covered (S : Finset ℝ²) (k b : ℕ) := ∃ (p : ℕ) (hp : p.Prime),
  letI : Fact p.Prime := ⟨hp⟩
  ∃ (f : F p → ℝ²) (c : Fin k → ℂ) (e : Fin k → F p) (I : Finset (F p)),
    Function.Injective f ∧ represents f c e ∧ I.image f⊆S ∧ (S\I.image f).card≤b

theorem near_bound {S : Finset ℝ²} {k b : ℕ} (h : covered S k b) :
    (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤ (constant k+b)*S.card := by
  obtain ⟨p,hp,rest⟩ := h
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨f,c,e,I,inj,rep,sub,num⟩ := rest
  have inside := four_bound inj rep I
  rw [←Erdos101Melchior.count_eq] at inside ⊢
  have size : I.card≤S.card := (Finset.card_image_of_injective I inj) ▸ Finset.card_le_card sub
  exact (Erdos101CyclicNear.delete_points sub).trans (by
    rw [Nat.add_mul]; exact Nat.add_le_add (inside.trans (Nat.mul_le_mul_left _ size)) (Nat.mul_le_mul_right _ num))

/-- For a fixed term count, the little-o conclusion survives arbitrary
changes in coefficients and a sublinear number of exceptional points. -/
theorem littleO (k : ℕ) (S : ℕ → Finset ℝ²) (b : ℕ → ℕ) (size : ∀n,(S n).card≤n)
    (cover : ∀n,covered (S n) k (b n))
    (outliers : (fun n => (b n:ℝ)) =o[atTop] (fun n => (n:ℝ))) :
    (fun n => ((linesWithPointsFor 4 (S n : Set ℝ²)).ncard : ℝ)) =o[atTop] (fun n => (n:ℝ)^2) := by
  apply IsLittleO.of_bound
  intro ε ep
  let r := ε/2
  have rp : 0<r := by dsimp [r]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt ((constant k:ℝ)/r)
  filter_upwards [eventually_ge_atTop N,outliers.bound rp] with n hn hb
  have castN : (N:ℝ)≤n := by exact_mod_cast hn
  have coeff : (constant k:ℝ)≤r*(n:ℝ) := ((div_lt_iff₀ rp).mp hN).le.trans
    ((mul_le_mul_of_nonneg_right castN rp.le).trans_eq (mul_comm ..))
  change ‖(b n:ℝ)‖≤r*‖(n:ℝ)‖ at hb
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg _)] at hb
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
  have h := (near_bound (cover n)).trans (Nat.mul_le_mul_left _ (size n))
  have lin : (constant k:ℝ)+b n≤ε*n := by dsimp [r] at hb coeff; linarith
  calc
    _ ≤ ((constant k:ℝ)+b n)*n := by exact_mod_cast h
    _ ≤ (ε*n)*n := mul_le_mul_of_nonneg_right lin (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos101CyclicComplex
