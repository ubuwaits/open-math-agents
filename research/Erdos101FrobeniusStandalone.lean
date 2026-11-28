import Mathlib

/-!
# Dense four-point lines escaping every bounded-degree curve in characteristic two

In a single algebraically closed field of characteristic two, take the graph
of x ↦ x^(4^k) on the subfield with 4^(2k+1) elements. Every secant contains
exactly four graph points. Substituting into any polynomial of total degree
d < 4^k gives a nonzero polynomial of degree at most d*4^k.
-/

noncomputable section

namespace Erdos101Frobenius

open Finset
open scoped Classical Polynomial

variable {K : Type*} [Field K] [CharP K 2]

def degree (k : ℕ) : ℕ := 4^k

private lemma power_two (k : ℕ) : degree k=2^(2*k) := by
  rw [degree,pow_mul]; norm_num

private lemma add_frob (k : ℕ) (a b : K) : (a+b)^degree k=a^degree k+b^degree k := by
  rw [power_two,add_pow_char_pow]

private lemma sub_frob (k : ℕ) (a b : K) : (a-b)^degree k=a^degree k-b^degree k := by
  rw [power_two,sub_pow_char_pow]

private lemma period (k : ℕ) : degree (2*k+1) = degree k*degree k*4 := by
  simp only [degree,pow_succ,←pow_add]; congr 2; omega

def parameters (K : Type*) [Field K] (j : ℕ) : Finset K :=
  ((Polynomial.X^(degree j)-Polynomial.X : K[X]).roots).toFinset

private lemma degree_gt (j : ℕ) (pos : 0<j) : 1<degree j :=
  Nat.one_lt_pow (by omega) (by decide)

omit [CharP K 2] in
theorem mem_parameters {j : ℕ} (pos : 0<j) (x : K) :
    x∈parameters K j ↔ x^degree j=x := by
  have nz : (Polynomial.X^degree j-Polynomial.X : K[X])≠0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K (degree_gt j pos)
  simp [parameters,Polynomial.mem_roots nz,Polynomial.IsRoot.def,sub_eq_zero]

variable [IsAlgClosed K]

theorem parameters_card {j : ℕ} (pos : 0<j) :
    (parameters K j).card=degree j := by
  let f := (Polynomial.X^degree j-Polynomial.X : K[X])
  have div : 2∣degree j := by
    rw [power_two]; exact dvd_pow_self _ (by omega)
  have sep : f.Separable := galois_poly_separable 2 _ div
  rw [parameters,Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots sep),
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits f),
    FiniteField.X_pow_card_sub_X_natDegree_eq K (degree_gt j pos)]

omit [CharP K 2] [IsAlgClosed K] in
private theorem fixed_powers {u : K} (h : u^4=u) (j : ℕ) : u^degree j=u := by
  induction j with
  | zero => simp [degree]
  | succ j ih =>
    change u^(4^(j+1))=u
    rw [pow_succ,pow_mul]; exact (congrArg (fun x : K => x^4) ih).trans h

omit [CharP K 2] [IsAlgClosed K] in
private theorem short_period {k : ℕ} {t : K} (a : t^degree k=t)
    (b : t^degree (2*k+1)=t) : t^4=t := by
  rw [period,pow_mul,pow_mul,a,a] at b
  exact b

def point (h : ℕ) (x : K) : K × K := (x,x^h)

def configuration (K : Type*) [Field K] (k : ℕ) : Finset (K × K) :=
  (parameters K (2*k+1)).image (point (degree k))

theorem configuration_card (k : ℕ) : (configuration K k).card=degree (2*k+1) := by
  rw [configuration,card_image_of_injOn (fun _ _ _ _ e => congrArg Prod.fst e),parameters_card (by omega)]

def incident (k : ℕ) (L : AffineSubspace K (K × K)) :=
  (configuration K k).filter (fun p => p∈L)

omit [CharP K 2] [IsAlgClosed K] in
private theorem line_parameter {x y z : K} {h : ℕ}
    (onLine : point h z∈line[K,point h x,point h y]) :
    ∃t : K, z=x+t*(y-x) ∧ z^h=x^h+t*(y^h-x^h) := by
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp onLine
  have u := congrArg Prod.fst ht
  have v := congrArg Prod.snd ht
  simp [AffineMap.lineMap_apply_module,point] at u v
  exact ⟨t,by linear_combination -u,by linear_combination -v⟩

omit [IsAlgClosed K] in
private theorem on_secant {k : ℕ} {x y t : K} (fixed : t^degree k=t) :
    point (degree k) (x+t*(y-x))∈line[K,point (degree k) x,point (degree k) y] := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨t,Prod.ext ?_ ?_⟩
  · simp [point,AffineMap.lineMap_apply_module]; ring
  · rw [AffineMap.lineMap_apply_module]
    change (1-t)*x^degree k+t*y^degree k=(x+t*(y-x))^degree k
    rw [add_frob,mul_pow,sub_frob,fixed]; ring

omit [IsAlgClosed K] in
private theorem affine_fixed (d : ℕ) {x y t : K} (xf : x^degree d=x) (yf : y^degree d=y)
    (tf : t^degree d=t) : (x+t*(y-x))^degree d=x+t*(y-x) := by
  rw [add_frob,mul_pow,sub_frob,xf,yf,tf]

/-- Normalize a chord by sending its first parameter to zero and its second to one.
The remaining parameters of that chord are exactly the four elements fixed by fourth power. -/
theorem chord_card {k : ℕ} {x y : K} (hx : x∈parameters K (2*k+1))
    (hy : y∈parameters K (2*k+1)) (ne : x≠y) :
    (incident k (line[K,point (degree k) x,point (degree k) y])).card=4 := by
  let d := 2*k+1
  have dp : 0<d := by dsimp [d]; omega
  have xf := (mem_parameters dp x).mp hx
  have yf := (mem_parameters dp y).mp hy
  let emb (t : K) := point (degree k) (x+t*(y-x))
  have nz : y-x≠0 := sub_ne_zero.mpr ne.symm
  have eq : incident k (line[K,point (degree k) x,point (degree k) y])=(parameters K 1).image emb := by
    ext p
    constructor
    · intro hp
      obtain ⟨cfg,line⟩ := mem_filter.mp hp
      obtain ⟨z,hz,rfl⟩ := mem_image.mp cfg
      obtain ⟨t,zt,zp⟩ := line_parameter line
      have coeff (i : ℕ) : z^degree i=x^degree i + t^degree i*(y-x)^degree i := by
        rw [zt,add_frob,mul_pow]
      have tf : t^degree k=t := by
        apply mul_right_cancel₀ (pow_ne_zero (degree k) nz)
        have c := coeff k
        rw [sub_frob] at c ⊢
        linear_combination zp-c
      have td : t^degree d=t := by
        apply mul_right_cancel₀ nz
        have c := coeff d
        rw [(mem_parameters dp z).mp hz,xf,sub_frob,yf,xf] at c
        linear_combination zt-c
      exact mem_image.mpr ⟨t,(mem_parameters (by decide : 0<1) t).mpr (short_period tf td),
        congrArg (point (degree k)) zt.symm⟩
    · intro hp
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
      have tf : t^4=t := (mem_parameters (by decide : 0<1) t).mp ht
      exact mem_filter.mpr ⟨mem_image.mpr ⟨x+t*(y-x),(mem_parameters dp _).mpr
        (affine_fixed d xf yf (fixed_powers tf d)),rfl⟩,on_secant (fixed_powers tf k)⟩
  rw [eq,card_image_of_injOn,parameters_card (by decide : 0<1)]
  · rfl
  · intro a _ b _ e
    have ab : x+a*(y-x)=x+b*(y-x) := congrArg Prod.fst e
    exact mul_right_cancel₀ nz (add_left_cancel ab)

def secants (K : Type*) [Field K] (k : ℕ) : Finset (AffineSubspace K (K × K)) :=
  (configuration K k).offDiag.image (fun e => line[K,e.1,e.2])

theorem every_secant {k : ℕ} {L : AffineSubspace K (K × K)} (hl : L∈secants K k) :
    (incident k L).card=4 := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hl
  obtain ⟨ha,hb,ne⟩ := mem_offDiag.mp hab
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
  exact chord_card hx hy (fun e => ne (congrArg (point (degree k)) e))

theorem no_five (k : ℕ) (p q : K × K) : (incident k (line[K,p,q])).card ≤ 4 := by
  by_contra! large
  obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp (show 1<(incident k (line[K,p,q])).card by omega)
  obtain ⟨pa,al⟩ := mem_filter.mp ha
  obtain ⟨pb,bl⟩ := mem_filter.mp hb
  have eq := affineSpan_pair_eq_of_mem_of_mem_of_ne al bl ne
  have hl : line[K,p,q]∈secants K k :=
    mem_image.mpr ⟨(a,b),mem_offDiag.mpr ⟨pa,pb,ne⟩,eq⟩
  have := every_secant hl; omega

/-- Ordered pairs of distinct points partition into twelve per secant. -/
theorem secant_count (k : ℕ) :
    12*(secants K k).card=(configuration K k).card*((configuration K k).card-1) := by
  let S := configuration K k
  let make (e : (K×K) × (K×K)) := line[K,e.1,e.2]
  have fiber (L : AffineSubspace K (K×K)) (hl : L∈secants K k) :
      S.offDiag.filter (fun e => make e=L) = (incident k L).offDiag := by
    obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_image.mp hl
    ext ⟨a,b⟩
    simp only [Finset.mem_filter,Finset.mem_offDiag,incident]
    constructor
    · rintro ⟨⟨ha,hb,ne⟩,eq⟩
      exact ⟨⟨ha,eq ▸ left_mem_affineSpan_pair K a b⟩,⟨hb,eq ▸ right_mem_affineSpan_pair K a b⟩,ne⟩
    · rintro ⟨⟨ha,al⟩,⟨hb,bl⟩,ne⟩
      exact ⟨⟨ha,hb,ne⟩,affineSpan_pair_eq_of_mem_of_mem_of_ne al bl ne⟩
  have partition := card_eq_sum_card_image make S.offDiag
  change S.offDiag.card=∑ L∈secants K k, (S.offDiag.filter (fun e => make e=L)).card at partition
  rw [sum_congr rfl (fun L hl => congrArg Finset.card (fiber L hl))] at partition
  have counts (L : AffineSubspace K (K×K)) (hl : L∈secants K k) : (incident k L).offDiag.card=12 := by
    rw [offDiag_card,every_secant hl]
  rw [sum_congr rfl counts] at partition
  simpa [S,offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_comm] using partition.symm

section Curves

variable {A : Type*} [Field A]

private def code (h : ℕ) (v : Fin 2 →₀ ℕ) := v 0+h*(v 1)

private theorem degree_sum {P : MvPolynomial (Fin 2) A} {v : Fin 2 →₀ ℕ} (hv : v∈P.support) :
    v 0+v 1 ≤ P.totalDegree := by
  have e := MvPolynomial.le_totalDegree hv
  rwa [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two] at e

private theorem code_injective {h : ℕ} {P : MvPolynomial (Fin 2) A} (small : P.totalDegree<h) :
    Set.InjOn (code h) (P.support : Set (Fin 2 →₀ ℕ)) := by
  intro a ha b hb he
  have ca := degree_sum ha; have cb := degree_sum hb
  have first : a 0=b 0 := by
    have e := congrArg (fun j : ℕ => j%h) he
    simpa [code,Nat.add_mod,Nat.mod_eq_of_lt (show a 0<h by omega),Nat.mod_eq_of_lt (show b 0<h by omega)] using e
  have second : a 1=b 1 := by
    change a 0+h*(a 1)=b 0+h*(b 1) at he
    rw [first] at he
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<h) (Nat.add_left_cancel he)
  ext i; fin_cases i <;> assumption

def substitution (h : ℕ) (P : MvPolynomial (Fin 2) A) : A[X] :=
  ∑ v ∈ P.support, Polynomial.monomial (code h v) (P.coeff v)

theorem substitution_ne {h : ℕ} {P : MvPolynomial (Fin 2) A} (nz : P≠0) (small : P.totalDegree<h) :
    substitution h P≠0 := by
  have notEmp : P.support.Nonempty := by simpa using nz
  obtain ⟨v,hv⟩ := notEmp
  have get : (substitution h P).coeff (code h v)=P.coeff v := by
    rw [substitution,Polynomial.finsetSum_coeff,Finset.sum_eq_single v]
    · simp
    · intro w hw ne
      have diff : code h w≠code h v := fun e => ne (code_injective small hw hv e)
      simp [Polynomial.coeff_monomial,diff]
    · exact fun no => False.elim (no hv)
  intro eq
  rw [eq,Polynomial.coeff_zero] at get
  exact (MvPolynomial.mem_support_iff.mp hv) get.symm

theorem substitution_degree (h : ℕ) (pos : 1≤h) (P : MvPolynomial (Fin 2) A) :
    (substitution h P).natDegree ≤ h*P.totalDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  apply (Polynomial.natDegree_monomial_le _).trans
  calc code h v = v 0+h*(v 1) := rfl
       _ ≤ h*(v 0)+h*(v 1) := Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right (v 0) pos) _
       _ ≤ h*P.totalDegree := by rw [←Nat.mul_add]; exact Nat.mul_le_mul_left _ (degree_sum hv)

theorem eval_substitution (h : ℕ) (P : MvPolynomial (Fin 2) A) (x : A) :
    (substitution h P).eval x=MvPolynomial.eval ![x,x^h] P := by
  conv_rhs => rw [P.as_sum,map_sum]
  rw [substitution,Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Polynomial.eval_monomial,MvPolynomial.eval_monomial,Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_two]
  simp [code,pow_add,pow_mul]

/-- Every degree-d curve with d < h meets the graph over any finite
parameter set in at most h*d points. -/
theorem curve_bound (B : Finset A) {h : ℕ} (pos : 1≤h) {P : MvPolynomial (Fin 2) A}
    (nonzero : P≠0) (small : P.totalDegree<h) :
    ((B.image (point h)).filter (fun p => MvPolynomial.eval ![p.1,p.2] P=0)).card ≤ h*P.totalDegree := by
  let T := B.filter (fun x => MvPolynomial.eval ![x,x^h] P=0)
  have eq : (B.image (point h)).filter (fun p => MvPolynomial.eval ![p.1,p.2] P=0)=T.image (point h) := by
    ext p
    constructor
    · intro hp; obtain ⟨inB,on⟩ := mem_filter.mp hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp inB
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,on⟩,rfl⟩
    · intro hp; obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
  rw [eq]
  apply (card_image_le).trans
  apply (Polynomial.card_le_degree_of_subset_roots (p:=substitution h P) (Z:=T) ?_).trans (substitution_degree h pos P)
  intro x hx
  exact (Polynomial.mem_roots (substitution_ne nonzero small)).mpr
    ((eval_substitution h P x).trans (mem_filter.mp hx).2)

end Curves

omit [CharP K 2] [IsAlgClosed K] in
/-- A nonzero degree-d plane curve contains at most d*4^k points of
the 4^(2k+1)-point configuration, even when its coefficients depend on k. -/
theorem escape (k : ℕ) {P : MvPolynomial (Fin 2) K} (nonzero : P≠0) (small : P.totalDegree<degree k) :
    ((configuration K k).filter (fun p => MvPolynomial.eval ![p.1,p.2] P=0)).card ≤ degree k*P.totalDegree :=
  curve_bound _ (Nat.one_le_pow _ _ (by decide)) nonzero small


def curvePoints (k : ℕ) (P : MvPolynomial (Fin 2) K) :=
  (configuration K k).filter (fun p => MvPolynomial.eval ![p.1,p.2] P=0)

def pairedLines (k : ℕ) (P : MvPolynomial (Fin 2) K) :=
  (secants K k).filter (fun L => 2 ≤ ((curvePoints k P).filter (fun p => p∈L)).card)

/-- At most n*d^2/4 of the roughly n^2/12 secants have even two
configuration points on a prescribed curve of degree d. -/
theorem pair_escape (k : ℕ) {P : MvPolynomial (Fin 2) K} (nonzero : P≠0) (small : P.totalDegree<degree k) :
    4*(pairedLines k P).card ≤ (configuration K k).card*P.totalDegree^2 := by
  let U := curvePoints k P
  let make (e : (K×K) × (K×K)) := line[K,e.1,e.2]
  have sub : pairedLines k P ⊆ U.offDiag.image make := by
    intro L hl
    obtain ⟨sec,two⟩ := mem_filter.mp hl
    obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_image.mp sec
    obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp two
    obtain ⟨au,al⟩ := mem_filter.mp ha
    obtain ⟨bu,bl⟩ := mem_filter.mp hb
    exact mem_image.mpr ⟨(a,b),mem_offDiag.mpr ⟨au,bu,ne⟩,affineSpan_pair_eq_of_mem_of_mem_of_ne al bl ne⟩
  have cnt : (pairedLines k P).card ≤ U.card^2 := calc
    _ ≤ (U.offDiag.image make).card := card_le_card sub
    _ ≤ U.offDiag.card := card_image_le
    _ ≤ U.card^2 := by rw [offDiag_card,pow_two]; exact Nat.sub_le .. 
  have bound := Nat.pow_le_pow_left (escape k nonzero small) 2
  rw [configuration_card,period]
  calc _ ≤ 4*U.card^2 := Nat.mul_le_mul_left _ cnt
       _ ≤ 4*(degree k*P.totalDegree)^2 := Nat.mul_le_mul_left _ bound
       _ = _ := by ring

/-- In one field, for arbitrary size and density thresholds, the pair of points
on a bounded-degree curve required by the real curve-extraction strategy
need not exist on any fixed positive fraction of the four-point lines. -/
theorem no_uniform_pair_capture (K : Type*) [Field K] [CharP K 2] [IsAlgClosed K] (N D s : ℕ) :
    ∃k : ℕ, N ≤ (configuration K k).card ∧
      (∀p q : K×K, (incident k (line[K,p,q])).card ≤ 4) ∧
      12*(secants K k).card=(configuration K k).card*((configuration K k).card-1) ∧
      ∀P : MvPolynomial (Fin 2) K, P≠0 → P.totalDegree ≤ D →
        s*(pairedLines k P).card < (secants K k).card := by
  let k := N+D+12*(s*D^2)+4
  have grow (j : ℕ) : j<degree j :=
    (show j<2^j from Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by decide : 2≤4) _)
  have sz := configuration_card (K:=K) k
  have pos := grow (2*k+1)
  have big : N ≤ (configuration K k).card := by dsimp [k] at *; omega
  refine ⟨k,big,no_five k,secant_count k,?_⟩
  intro P nz low
  have sk := grow k
  have sm : P.totalDegree<degree k := by dsimp [k] at *; omega
  have e := pair_escape k nz sm
  have below : (pairedLines k P).card ≤ (configuration K k).card*D^2 := by
    exact (show (pairedLines k P).card ≤ 4*(pairedLines k P).card by omega).trans
      (e.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left low 2)))
  have room : 12*(s*D^2)<(configuration K k).card-1 := by dsimp [k] at *; omega
  have positive : 0<(configuration K k).card := by omega
  have strict : 12*(s*(pairedLines k P).card)<12*(secants K k).card := calc
    _ ≤ 12*(s*((configuration K k).card*D^2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ below)
    _ = (12*(s*D^2))*(configuration K k).card := by ring
    _ < ((configuration K k).card-1)*(configuration K k).card := Nat.mul_lt_mul_of_pos_right room positive
    _ = 12*(secants K k).card := by rw [secant_count,Nat.mul_comm]
  omega

end Erdos101Frobenius
