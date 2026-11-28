import Erdos64TriangleExpansion

namespace Erdos64CubicTriangle

open SimpleGraph Function Erdos64TriangleExpansion

/-- Project a walk when an edge may collapse to one vertex. -/
theorem project_reachable {V W : Type*} {G : SimpleGraph V} {B : SimpleGraph W}
    (p : V → W) (step : ∀ x y, G.Adj x y → B.Reachable (p x) (p y))
    {a b : V} (reach : G.Reachable a b) : B.Reachable (p a) (p b) := by
  obtain ⟨w⟩ := reach
  induction w with
  | nil => exact .refl _
  | cons adj tail ih => exact (step _ _ adj).trans ih

/-- A projection with a unique lift of each surviving edge preserves bridgelessness. -/
theorem bridges_project {V W : Type*} (G : SimpleGraph V) (p : V → W)
    (bridgeless : ∀ ⦃x y⦄, G.Adj x y → ¬G.IsBridge s(x,y))
    (unique : ∀ ⦃a b x y⦄, G.Adj a b → G.Adj x y → p a ≠ p b →
      p a = p x → p b = p y → a = x ∧ b = y) :
    ∀ ⦃u v⦄, (G.map p).Adj u v → ¬(G.map p).IsBridge s(u,v) := by
  classical
  intro u v h
  obtain ⟨diff,a,b,ab,rfl,rfl⟩ := (map_adj' p G _ _).mp h
  apply fun bridge => (isBridge_iff.mp bridge) ?_
  have bypass : (G.deleteEdges {s(a,b)}).Reachable a b := by
    by_contra missing
    exact bridgeless ab (isBridge_iff.mpr missing)
  apply project_reachable p _ bypass
  intro x y hxy
  obtain ⟨xy, keep⟩ := deleteEdges_adj.mp hxy
  by_cases eq : p x = p y
  · exact eq ▸ Reachable.refl _
  apply Adj.reachable
  apply deleteEdges_adj.mpr
  refine ⟨(map_adj' p G _ _).mpr ⟨eq,x,y,xy,rfl,rfl⟩,?_⟩
  intro removed
  apply keep
  apply Set.mem_singleton_iff.mpr
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp removed) with h | h
  · exact Sym2.eq_iff.mpr (Or.inl (unique xy ab eq h.1 h.2))
  · exact Sym2.eq_iff.mpr (Or.inr (unique xy ab.symm eq h.1 h.2))

/-- In a square-free cubic graph the three edges leaving a triangle end
at three distinct outside vertices, one for each triangle vertex. -/
theorem triangle_exits {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (cubic : ∀ x, G.degree x = 3) (nosq : ¬cycleGraph 4 ⊑ G)
    (e : Fin 3 ↪ V) (triangle : ∀ i j, i ≠ j → G.Adj (e i) (e j)) :
    ∃ out : Fin 3 ↪ V, (∀ i, out i ∉ Set.range e) ∧
      (∀ i, G.Adj (e i) (out i)) ∧
      (∀ i x, x ∉ Set.range e → G.Adj (e i) x → out i = x) := by
  classical
  let T := Finset.univ.map e
  have member (x : V) : x ∈ T ↔ x ∈ Set.range e := by simp [T,Set.mem_range]
  have sizeT : T.card = 3 := by simp [T]
  have inside (i : Fin 3) : e i ∈ T := (member _).mpr ⟨i,rfl⟩
  have boundary (i : Fin 3) : G.neighborFinset (e i) ∩ T = T.erase (e i) := by
    ext x
    simp only [Finset.mem_inter,mem_neighborFinset,Finset.mem_erase]
    constructor
    · rintro ⟨adj,hmem⟩
      exact ⟨adj.ne.symm,hmem⟩
    · rintro ⟨diff,hmem⟩
      obtain ⟨j,rfl⟩ := (member _).mp hmem
      exact ⟨triangle i j (fun h => diff (congrArg e h.symm)),hmem⟩
  have one (i : Fin 3) : ∃ y, (G.neighborFinset (e i) \ T) = {y} := by
    apply Finset.card_eq_one.mp
    have count := Finset.card_sdiff_add_card_inter (G.neighborFinset (e i)) T
    rw [boundary,Finset.card_erase_of_mem (inside i),sizeT,card_neighborFinset_eq_degree,cubic] at count
    omega
  choose f hf using one
  have spec (i : Fin 3) (x : V) : G.Adj (e i) x ∧ x ∉ Set.range e ↔ x = f i := by
    rw [←Finset.mem_singleton,←hf]
    simp [member]
  have outside (i : Fin 3) := ((spec i (f i)).mpr rfl).2
  have adjacent (i : Fin 3) := ((spec i (f i)).mpr rfl).1
  have inj : Injective f := by
    intro i j same
    by_contra diff
    have other : ∀ a b : Fin 3, a ≠ b → a ≠ -(a+b) ∧ -(a+b) ≠ b := by decide
    let k := -(i+j)
    obtain ⟨ik,kj⟩ := other i j diff
    have close : G.Adj (e j) (f i) := same.symm ▸ adjacent j
    exact nosq (square_of_four (adjacent i).symm (triangle i k ik) (triangle k j kj) close
      (fun h => outside i ⟨k,h.symm⟩) (fun h => diff (e.injective h)))
  exact ⟨⟨f,inj⟩,outside,adjacent,fun i x off adj => ((spec i x).mp ⟨adj,off⟩).symm⟩


/-- Contracting one triangle in a square-free connected bridgeless cubic graph
produces a strictly smaller graph with all three properties. The projection
also records exactly the two cycle lifts needed at its distinguished vertex. -/
theorem contract_triangle {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected) (cubic : ∀ x, G.degree x = 3)
    (bridgeless : ∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b))
    (nosq : ¬cycleGraph 4 ⊑ G) (e : Fin 3 ↪ V)
    (triangle : ∀ i j, i ≠ j → G.Adj (e i) (e j)) :
    ∃ (W : Type) (_ : Fintype W) (B : SimpleGraph W) (_ : DecidableRel B.Adj) (root : W),
      Fintype.card W < Fintype.card V ∧ B.Connected ∧ (∀ w, B.degree w = 3) ∧
      (∀ ⦃a b⦄, B.Adj a b → ¬ B.IsBridge s(a,b)) ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ c : (cycleGraph n).Copy B,
        (root ∉ Set.range c → cycleGraph n ⊑ G) ∧
        (root ∈ Set.range c → cycleGraph (n+1) ⊑ G ∧ cycleGraph (n+2) ⊑ G) := by
  classical
  obtain ⟨out,outside,edge,only⟩ := triangle_exits G cubic nosq e triangle
  let Off := {x : V // x ∉ Set.range e}
  let W := Option Off
  let p (x : V) : W := if h : x ∈ Set.range e then none else some ⟨x,h⟩
  let B := G.map p
  have atTriangle (i : Fin 3) : p (e i) = none := dif_pos ⟨i,rfl⟩
  have off (x : Off) : p x.val = some x := dif_neg x.property
  have pn (x : V) : p x = none ↔ x ∈ Set.range e := by
    by_cases h : x ∈ Set.range e
    · exact ⟨fun _ => h,fun _ => dif_pos h⟩
    · refine ⟨?_,fun mem => (h mem).elim⟩
      intro eq
      have impossible : some (⟨x,h⟩ : Off) = none := (off ⟨x,h⟩).symm.trans eq
      cases impossible
  have ps (x : V) (y : Off) : p x = some y ↔ x = y.val := by
    constructor
    · intro h
      by_cases mem : x ∈ Set.range e
      · rw [(pn x).mpr mem] at h
        contradiction
      · have eq := (off ⟨x,mem⟩).symm.trans h
        exact congrArg Subtype.val (Option.some.inj eq)
    · rintro rfl
      exact off y
  have onto : Surjective p := by
    rintro (_ | x)
    · exact ⟨e 0,atTriangle 0⟩
    · exact ⟨x.val,off x⟩
  have shrink : Fintype.card W < Fintype.card V := by
    apply Fintype.card_lt_of_surjective_not_injective p onto
    intro inj
    exact (by decide : (0:Fin 3) ≠ 1) (e.injective (inj ((atTriangle 0).trans (atTriangle 1).symm)))
  have projects {a b : V} (h : G.Adj a b) (diff : p a ≠ p b) : B.Adj (p a) (p b) :=
    (map_adj' p G _ _).mpr ⟨diff,a,b,h,rfl,rfl⟩
  have conn : B.Connected := by
    refine ⟨?_⟩
    intro u v
    obtain ⟨a,rfl⟩ := onto u
    obtain ⟨b,rfl⟩ := onto v
    apply project_reachable p _ (connected a b)
    intro x y xy
    by_cases eq : p x = p y
    · exact eq ▸ Reachable.refl _
    · exact (projects xy eq).reachable
  have sameNeighbor (z : Off) {x y : V} (zx : G.Adj z.val x) (zy : G.Adj z.val y)
      (eq : p x = p y) : x = y := by
    cases which : p x with
    | some w => exact ((ps x w).mp which).trans (((ps y w).mp (eq.symm.trans which)).symm)
    | none =>
      obtain ⟨i,rfl⟩ := (pn x).mp which
      obtain ⟨j,rfl⟩ := (pn y).mp (eq.symm.trans which)
      exact congrArg e (out.injective ((only i z.val z.property zx.symm).trans
        (only j z.val z.property zy.symm).symm))
  have unique ⦃a b x y : V⦄ (ab : G.Adj a b) (xy : G.Adj x y)
      (diff : p a ≠ p b) (ax : p a = p x) (by' : p b = p y) : a=x ∧ b=y := by
    cases ha : p a with
    | some w =>
      have aw := (ps a w).mp ha
      have xw := (ps x w).mp (ax.symm.trans ha)
      exact ⟨aw.trans xw.symm,sameNeighbor w (aw ▸ ab) (xw ▸ xy) by'⟩
    | none =>
      cases hb : p b with
      | none => exact (diff (ha.trans hb.symm)).elim
      | some w =>
        have bw := (ps b w).mp hb
        have yw := (ps y w).mp (by'.symm.trans hb)
        exact ⟨sameNeighbor w (bw ▸ ab.symm) (yw ▸ xy.symm) ax,bw.trans yw.symm⟩
  have noBridge : ∀ ⦃a b⦄, B.Adj a b → ¬B.IsBridge s(a,b) := bridges_project G p bridgeless unique
  let exit (i : Fin 3) : Off := ⟨out i,outside i⟩
  have exitInj : Injective exit := fun _ _ h => out.injective (congrArg Subtype.val h)
  have rootAdj (x : Off) : B.Adj none (some x) ↔ x ∈ Set.range exit := by
    constructor
    · intro h
      obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' p G _ _).mp h
      obtain ⟨i,rfl⟩ := (pn a).mp ha
      obtain rfl := (ps b x).mp hb
      exact ⟨i,Subtype.ext (only i _ x.property ab)⟩
    · rintro ⟨i,rfl⟩
      exact (map_adj' p G _ _).mpr ⟨by simp,e i,out i,edge i,atTriangle i,off (exit i)⟩
  have leafAdj (a b : Off) : B.Adj (some a) (some b) ↔ G.Adj a.val b.val := by
    constructor
    · intro h
      obtain ⟨_,x,y,xy,hx,hy⟩ := (map_adj' p G _ _).mp h
      rwa [(ps x a).mp hx,(ps y b).mp hy] at xy
    · intro h
      exact (map_adj' p G _ _).mpr ⟨fun eq => h.ne (congrArg Subtype.val (Option.some.inj eq)),
        a.val,b.val,h,off a,off b⟩
  have deg : ∀ w, B.degree w=3 := by
    rintro (_ | x)
    · let ends (i : Fin 3) : W := some (exit i)
      have rootNbr : B.neighborFinset none = Finset.univ.image ends := by
        ext w
        cases w with
        | none => simp [ends]
        | some x =>
          rw [mem_neighborFinset,rootAdj,Finset.mem_image]
          exact ⟨fun ⟨i,hi⟩ => ⟨i,Finset.mem_univ _,congrArg some hi⟩,
            fun ⟨i,_,hi⟩ => ⟨i,Option.some.inj hi⟩⟩
      rw [←card_neighborFinset_eq_degree,rootNbr,
        Finset.card_image_of_injective _ (fun _ _ h => exitInj (Option.some.inj h))]
      simp
    · have nbr : B.neighborFinset (some x) = (G.neighborFinset x.val).image p := by
        ext w
        simp only [mem_neighborFinset,Finset.mem_image]
        constructor
        · intro h
          obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' p G _ _).mp h
          exact ⟨b,(ps a x).mp ha ▸ ab,hb⟩
        · rintro ⟨b,h,rfl⟩
          have diff : some x ≠ p b := fun eq => h.ne (((ps b x).mp eq.symm).symm)
          exact (map_adj' p G _ _).mpr ⟨diff,x.val,b,h,off x,rfl⟩
      rw [←card_neighborFinset_eq_degree,nbr,Finset.card_image_of_injOn,
        card_neighborFinset_eq_degree,cubic]
      exact fun _ hx _ hy eq => sameNeighbor x ((mem_neighborFinset _ _ _).mp hx)
        ((mem_neighborFinset _ _ _).mp hy) eq
  let point : W → Fin 3 → V
    | none,i => e i
    | some x,_ => x.val
  let port : W → W → Fin 3
    | none,some x => invFun exit x
    | _,_ => 0
  have atExit (i : Fin 3) : invFun exit (exit i)=i := leftInverse_invFun exitInj i
  have designation : ∀ (v : W) (i : Fin 3), p (point v i)=v := by
    rintro (_ | x) i
    · exact atTriangle i
    · exact off x
  have separate : ∀ v ∈ ({none} : Set W), ∀ x y, B.Adj v x → B.Adj v y → x≠y →
      port v x≠port v y := by
    rintro v hv x y hx hy diff
    obtain rfl : v=none := hv
    cases x with
    | none => exact (hx.ne rfl).elim
    | some a =>
      cases y with
      | none => exact (hy.ne rfl).elim
      | some b =>
        obtain ⟨i,rfl⟩ := (rootAdj a).mp hx
        obtain ⟨j,rfl⟩ := (rootAdj b).mp hy
        change invFun exit (exit i) ≠ invFun exit (exit j)
        rw [atExit,atExit]
        exact fun h => diff (congrArg (fun t => some (exit t)) h)
  have internal : ∀ v ∈ ({none} : Set W), ∀ i j, i≠j → G.Adj (point v i) (point v j) := by
    rintro v hv
    obtain rfl : v=none := hv
    exact triangle
  have inject : ∀ v ∈ ({none} : Set W), Injective (point v) := by
    rintro v hv
    obtain rfl : v=none := hv
    exact e.injective
  have single : ∀ v ∉ ({none} : Set W), ∀ i j, point v i=point v j := by
    rintro (_ | x) h i j
    · exact (h rfl).elim
    · rfl
  have external : ∀ v w, B.Adj v w → G.Adj (point v (port v w)) (point w (port w v)) := by
    rintro (_ | a) (_ | b) h
    · exact (h.ne rfl).elim
    · obtain ⟨i,rfl⟩ := (rootAdj b).mp h
      change G.Adj (e (invFun exit (exit i))) (out i)
      rw [atExit]
      exact edge i
    · obtain ⟨i,rfl⟩ := (rootAdj a).mp h.symm
      change G.Adj (out i) (e (invFun exit (exit i)))
      rw [atExit]
      exact (edge i).symm
    · exact (leafAdj a b).mp h
  refine ⟨W,inferInstance,B,inferInstance,none,shrink,conn,deg,noBridge,?_⟩
  intro n large c
  exact single_vertex_lengths
    ⟨{none},p,point,designation,port,separate,inject,internal,single,external⟩ none rfl large c

end Erdos64CubicTriangle
