import Erdos64TwoOrbits

/-! A nonidentity prime-order automorphism on twice as many vertices forces
a dyadic cycle. In particular this handles vertex-transitive graphs of order 2p. -/

namespace Erdos64TwicePrime

open Function SimpleGraph MulAction Erdos64TwoOrbits Erdos64TriangleExpansion

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If a nontrivial abelian group acts regularly on just one orbit and fixes
all remaining vertices, minimum degree three already forces a square. -/
theorem one_moving_orbit {A : Type*} [AddCommGroup A] [Nontrivial A]
    (f : A ↪ V) (act : A → V → V)
    (shift : ∀ a x, act a (f x)=f (a+x))
    (auto : ∀ a {u v}, G.Adj u v → G.Adj (act a u) (act a v))
    (fixed : ∀ z, z ∉ Set.range f → ∀ a, act a z=z)
    (degree : 3 ≤ G.degree (f 0)) : cycleGraph 4 ⊑ G := by
  classical
  obtain ⟨u,v,w,hu,hv,hw,uv,uw,vw⟩ := Finset.two_lt_card_iff.mp degree
  rw [mem_neighborFinset] at hu hv hw
  have translate {y : V} (h : y ∉ Set.range f) (e : G.Adj (f 0) y) (x : A) :
      G.Adj (f x) y := by simpa [shift,fixed _ h] using auto x e
  by_cases closed : ∀ z, G.Adj (f 0) z → z ∈ Set.range f
  · obtain ⟨a,rfl⟩ := closed _ hu
    obtain ⟨b,rfl⟩ := closed _ hv
    obtain ⟨c,rfl⟩ := closed _ hw
    apply internal_square f a b c (fun h => uv (congrArg f h)) (fun h => uw (congrArg f h))
      (fun h => vw (congrArg f h))
    rintro x d (rfl|rfl|rfl)
    · simpa [shift] using auto x hu
    · simpa [shift] using auto x hv
    · simpa [shift] using auto x hw
  · push Not at closed
    obtain ⟨z,hz,out⟩ := closed
    obtain ⟨a,ha⟩ := exists_ne (0 : A)
    have distinct : f 0 ≠ f a := fun h => ha (f.injective h).symm
    have opposite {i j : V} (ei : G.Adj (f 0) i) (ej : G.Adj (f 0) j) (ij : i≠j)
        (same : i ∈ Set.range f ↔ j ∈ Set.range f) : cycleGraph 4 ⊑ G := by
      by_cases mem : i ∈ Set.range f
      · obtain ⟨a,eq⟩ := mem
        obtain ⟨b,ejb⟩ := same.mp ⟨a,eq⟩
        exact square_of_four ei (eq ▸ translate out hz a) (ejb ▸ (translate out hz b).symm)
          ej.symm (fun h => out ⟨0,h⟩) ij
      · have other := mt same.mpr mem
        exact square_of_four ei (translate mem ei a).symm (translate other ej a) ej.symm distinct ij
    by_contra no
    have h1 := fun h => no (opposite hu hv uv h)
    have h2 := fun h => no (opposite hu hw uw h)
    have h3 := fun h => no (opposite hv hw vw h)
    tauto

omit [Fintype V] in
theorem prime_orbit {B : Type*} [Group B] [MulAction B V] [(Fact (Nat.card B).Prime)]
    (x : V) (moves : ∃ b : B, b • x ≠ x) : Injective (fun b : B => b • x) := by
  obtain ⟨b,hb⟩ := moves
  have bot : stabilizer B x = ⊥ := (stabilizer B x).eq_bot_or_eq_top_of_prime_card.resolve_right
    (fun h => hb (mem_stabilizer_iff.mp (h ▸ Subgroup.mem_top b)))
  intro u v h
  change u • x=v • x at h
  have mem : u⁻¹*v ∈ stabilizer B x := by rw [mem_stabilizer_iff,mul_smul,←h,inv_smul_smul]
  have id : u⁻¹*v=1 := Subgroup.mem_bot.mp (bot ▸ mem)
  exact inv_mul_eq_one.mp id

/-- A prime-order group acting nontrivially by automorphisms on 2p vertices
has one moving orbit and fixed points, or a pair of regular orbits. -/
theorem prime_action {B : Type*} [CommGroup B] [Fintype B] [MulAction B V]
    (prime : (Nat.card B).Prime) (size : Fintype.card V=2*Fintype.card B)
    (moved : ∃ (x : V) (b : B), b • x≠x)
    (auto : ∀ (b : B) {u v : V}, G.Adj u v → G.Adj (b • u) (b • v))
    (degree : ∀ v, 3 ≤ G.degree v) : Short G := by
  classical
  let : Fact (Nat.card B).Prime := ⟨prime⟩
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp prime.one_lt
  obtain ⟨x,b,hb⟩ := moved
  let f : Additive B ↪ V := ⟨fun a => a.toMul • x,(prime_orbit (B:=B) x ⟨b,hb⟩).comp Additive.toMul.injective⟩
  have shift (d a : Additive B) : d.toMul • f a=f (d+a) := (mul_smul _ _ _).symm
  by_cases single : ∀ y, y ∉ Set.range f → ∀ b : B, b • y=y
  · exact Or.inl (one_moving_orbit G f (fun a z => a.toMul • z) shift
      (fun a _ _ e => auto a.toMul e) (fun z hz a => single z hz a.toMul) (degree _))
  push Not at single
  obtain ⟨y,out,c,hc⟩ := single
  let g : Additive B ↪ V := ⟨fun a => a.toMul • y,(prime_orbit (B:=B) y ⟨c,hc⟩).comp Additive.toMul.injective⟩
  have apart (a d : Additive B) : f a ≠ g d := by
    intro eq
    apply out
    refine ⟨Additive.ofMul (d.toMul⁻¹ * a.toMul),?_⟩
    change (d.toMul⁻¹ * a.toMul) • x=y
    rw [mul_smul]
    exact (congrArg (fun z => d.toMul⁻¹ • z) eq).trans (inv_smul_smul _ _)
  let pair : Bool × Additive B → V
    | (false,a) => f a
    | (true,a) => g a
  have inj : Injective pair := by
    rintro ⟨i,a⟩ ⟨j,t⟩ h
    cases i <;> cases j
    · exact Prod.ext rfl (f.injective h)
    · exact (apart _ _ h).elim
    · exact (apart _ _ h.symm).elim
    · exact Prod.ext rfl (g.injective h)
  let e := Equiv.ofBijective pair ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨inj,by simpa using size.symm⟩)
  let K := G.comap e
  let iso : K ≃g G := SimpleGraph.Iso.comap e G
  have coord (i : Bool) (d a : Additive B) : e (i,d+a)=d.toMul • e (i,a) := by
    cases i <;> exact mul_smul _ _ _
  have inv : Invariant K := by
    intro d i j a t h
    change G.Adj (e (i,d+a)) (e (j,d+t))
    rw [coord,coord]
    exact auto _ h
  have deg (z) : 3 ≤ K.degree z := (degree (iso z)).trans_eq (iso.degree_eq z)
  exact short_map (isContained_iff_exists_le_comap.mpr ⟨e.toEmbedding,le_rfl⟩)
    (two_regular_orbits K inv deg)

/-- A prime divisor of the order of a transitive automorphism group gives the
prime-order action by Cauchy's theorem. No bound on the valency above three. -/
theorem vertex_transitive_twice_prime {p : ℕ} (prime : p.Prime) (size : Fintype.card V=2*p)
    (transitive : ∀ x y : V, ∃ g : G ≃g G, g x=y) (degree : ∀ v, 3 ≤ G.degree v) :
    Short G := by
  classical
  let : Fact p.Prime := ⟨prime⟩
  let A : Subgroup (Equiv.Perm V) :=
    { carrier := {g | ∀ u v, G.Adj (g u) (g v) ↔ G.Adj u v}
      mul_mem' := fun hg hh u v => (hg _ _).trans (hh u v)
      one_mem' := fun _ _ => Iff.rfl
      inv_mem' := fun {g} hg u v => by simpa using (hg (g.symm u) (g.symm v)).symm }
  let : IsPretransitive A V := ⟨fun u v => by
    obtain ⟨g,h⟩ := transitive u v
    exact ⟨⟨g.toEquiv,fun _ _ => g.map_rel_iff⟩,h⟩⟩
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (size ▸ Nat.mul_pos (by decide) prime.pos)
  have dv := (stabilizer A x).index_dvd_card
  rw [index_stabilizer_of_transitive A x, Nat.card_eq_fintype_card, size] at dv
  obtain ⟨g,ord⟩ := exists_prime_orderOf_dvd_card' (G:=A) p ((dvd_mul_left p 2).trans dv)
  let B := Subgroup.zpowers g
  let : CommGroup B := IsCyclic.commGroup
  have count : Nat.card B=p := (Nat.card_zpowers g).trans ord
  have moves : ∃ y : V, g.val y ≠ y := by
    by_contra! fixed
    have eq : g=1 := Subtype.ext (Equiv.ext fixed)
    rw [eq,orderOf_one] at ord
    exact prime.ne_one ord.symm
  obtain ⟨y,hy⟩ := moves
  apply prime_action (B:=B) G (count ▸ prime) (by simpa [← Nat.card_eq_fintype_card, count] using size)
    ⟨y,⟨g,Subgroup.mem_zpowers g⟩,hy⟩ _ degree
  exact fun b _ _ h => (b.val.property _ _).mpr h

end Erdos64TwicePrime
