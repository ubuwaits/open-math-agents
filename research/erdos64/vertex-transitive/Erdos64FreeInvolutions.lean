import Erdos64BinaryQuotients

/-! Fixed-point-free involutions in a smallest counterexample to Erdős–Gyárfás.
The quotient forgets the edges joining a vertex to its mate. Such pairs form
an independent set in the quotient, and precisely those pairs lose one degree. -/

namespace Erdos64FreeInvolutions

open SimpleGraph Function Erdos64TriangleExpansion Erdos64SymmetricCycles Erdos64BinaryQuotients

theorem involution_quotient {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (nosq : ¬cycleGraph 4 ⊑ G) (t : V → V) (twice : ∀ x,t (t x)=x)
    (free : ∀ x,t x≠x) (sym : ∀ a b,G.Adj a b → G.Adj (t a) (t b)) :
    ∃ (W : Type) (_ : Fintype W) (B : SimpleGraph W) (_ : DecidableRel B.Adj) (q : V → W),
      Surjective q ∧ Fintype.card V=2*Fintype.card W ∧
      (∀ x, B.degree (q x) + (if G.Adj x (t x) then 1 else 0) = G.degree x) ∧
      (∀ x y, B.Adj (q x) (q y) → ¬(G.Adj x (t x) ∧ G.Adj y (t y))) ∧
      (∀ n : ℕ, 3≤n → cycleGraph n ⊑ B → cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G) := by
  classical
  obtain ⟨W,fw,q,onto,pair,card,fib⟩ := pair_projection t twice free
  let : Fintype W := fw
  have fixed (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have neighborInj {x y z : V} (xy : G.Adj x y) (xz : G.Adj x z) (eq : q y=q z) : y=z := by
    rcases (pair _ _).mp eq with done|rfl
    · exact done
    · have across : G.Adj z (t x) := (show G.Adj (t x) z from (twice z) ▸ sym _ _ xy).symm
      exact (nosq (square_of_four xz across (sym _ _ xz) xy.symm (free x).symm (free z).symm)).elim
  let B := G.map q
  have lift (x : V) (w : W) (edge : B.Adj (q x) w) :
      ∃! y, G.Adj x y ∧ q y=w := by
    obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' q G _ _).mp edge
    have existsLift : ∃ y, G.Adj x y ∧ q y=w := by
      rcases (pair _ _).mp ha with rfl|rfl
      · exact ⟨b,ab,hb⟩
      · exact ⟨t b,(twice x) ▸ sym _ _ ab,(fixed b).trans hb⟩
    obtain ⟨y,xy,hy⟩ := existsLift
    exact ⟨y,⟨xy,hy⟩,fun z hz => neighborInj hz.1 xy (hz.2.trans hy.symm)⟩
  have degree (x : V) : B.degree (q x)+(if G.Adj x (t x) then 1 else 0)=G.degree x := by
    let kept := (G.neighborFinset x).erase (t x)
    have nbr : B.neighborFinset (q x)=kept.image q := by
      ext z
      simp only [mem_neighborFinset,Finset.mem_image]
      constructor
      · intro adj
        obtain ⟨y,xy,hy⟩ := (lift x z adj).exists
        refine ⟨y,Finset.mem_erase.mpr ⟨?_,(G.mem_neighborFinset _ _).mpr xy⟩,hy⟩
        intro eq
        exact adj.ne (hy ▸ ((congrArg q eq).trans (fixed x)).symm)
      · rintro ⟨y,hy,rfl⟩
        obtain ⟨neq,mem⟩ := Finset.mem_erase.mp hy
        have xy := (G.mem_neighborFinset _ _).mp mem
        have diff : q x≠q y := fun eq => ((pair y x).mp eq.symm).elim xy.ne.symm neq
        exact (map_adj' q G _ _).mpr ⟨diff,x,y,xy,rfl,rfl⟩
    have inj : Set.InjOn q kept := fun _ hx _ hy eq =>
      neighborInj ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hx).2)
        ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hy).2) eq
    rw [←card_neighborFinset_eq_degree,nbr,Finset.card_image_of_injOn inj]
    by_cases edge : G.Adj x (t x)
    · have mem := (G.mem_neighborFinset x (t x)).mpr edge
      change ((G.neighborFinset x).erase (t x)).card + _ = _
      rw [Finset.card_erase_of_mem mem,card_neighborFinset_eq_degree,if_pos edge]
      have pos := (G.degree_pos_iff_exists_adj x).mpr ⟨_,edge⟩
      omega
    · simp [kept,edge,card_neighborFinset_eq_degree]
  have independent (x y : V) (adj : B.Adj (q x) (q y)) (both : G.Adj x (t x) ∧ G.Adj y (t y)) :
      False := by
    obtain ⟨z,xz,hz⟩ := (lift x _ adj).exists
    have loop : G.Adj z (t z) := by
      rcases (pair z y).mp hz with rfl|rfl
      · exact both.2
      · simpa only [twice] using both.2.symm
    have outside : q x≠q z := hz ▸ adj.ne
    have a : x≠t z := fun e => outside ((congrArg q e).trans (fixed z))
    have b : z≠t x := fun e => outside (((congrArg q e).trans (fixed x)).symm)
    exact nosq (square_of_four xz loop (sym _ _ xz).symm both.1.symm a b)
  refine ⟨W,fw,B,inferInstance,q,onto,card.trans (Nat.mul_comm _ _),degree,independent,?_⟩
  rintro n large ⟨c⟩
  exact lift_two q onto (fun w => (fib w).le) large c lift

/-- Every free involutory automorphism of a minimum-order counterexample
has both adjacent and nonadjacent vertex-mate pairs. -/
theorem mixed_pairs_in_smallest {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (degree : ∀ v, 3 ≤ G.degree v)
    (fail : ¬∃ k : ℕ, 2≤k ∧ cycleGraph (2^k) ⊑ G)
    (smaller : ∀ (W : Type) [Fintype W] [Nonempty W] (B : SimpleGraph W) [DecidableRel B.Adj],
      Fintype.card W<Fintype.card V → (∀ w, 3 ≤ B.degree w) → ∃ k : ℕ, 2≤k ∧ cycleGraph (2^k) ⊑ B)
    (t : V → V) (twice : ∀ x,t (t x)=x) (free : ∀ x,t x≠x)
    (sym : ∀ a b,G.Adj a b → G.Adj (t a) (t b)) :
    (∃ x, G.Adj x (t x)) ∧ (∃ y, ¬G.Adj y (t y)) := by
  classical
  have nosq : ¬cycleGraph 4 ⊑ G := fun h => fail ⟨2,by decide,h⟩
  obtain ⟨W,fw,B,db,q,onto,card,deg,indep,lift⟩ := involution_quotient G nosq t twice free sym
  let : Fintype W := fw
  let : DecidableRel B.Adj := db
  let : Nonempty W := ⟨q (Classical.choice inferInstance)⟩
  constructor
  · by_contra! none
    have lower (w : W) : 3≤B.degree w := by
      obtain ⟨x,rfl⟩ := onto w
      have equal := deg x
      rw [if_neg (none x),Nat.add_zero] at equal
      exact equal ▸ degree x
    have pos := Fintype.card_pos (α := W)
    obtain ⟨k,hk,c⟩ := smaller W B (by omega) lower
    have four : 4≤2^k := Nat.pow_le_pow_right (by decide : 0<2) hk
    rcases lift _ (by omega) c with keep|double
    · exact fail ⟨k,hk,keep⟩
    · exact fail ⟨k+1,by omega,by rwa [pow_succ']⟩
  · by_contra! allAdjacent
    let x : V := Classical.choice inferInstance
    have positive : 0 < B.degree (q x) := by
      have d := deg x
      rw [if_pos (allAdjacent x)] at d
      have := degree x
      omega
    obtain ⟨w,adj⟩ := (B.degree_pos_iff_exists_adj _).mp positive
    obtain ⟨y,rfl⟩ := onto w
    exact indep x y adj ⟨allAdjacent x,allAdjacent y⟩

end Erdos64FreeInvolutions
