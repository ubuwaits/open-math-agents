import Erdos64TriangleExpansion
import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1

/-! Dyadic cycles in graphs admitting an abelian group with two regular orbits.
The three-matching case uses the merged Haar graph theorem of José Mejias (@mejiasd3v) from upstream PR 5246. -/

namespace Erdos64TwoOrbits
open SimpleGraph Function Erdos64TriangleExpansion

abbrev Short {V : Type*} (G : SimpleGraph V) : Prop :=
  cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G

theorem short_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : G ⊑ H) : Short G → Short H := by
  rintro (c|c|c)
  · exact Or.inl (c.trans h)
  · exact Or.inr (Or.inl (c.trans h))
  · exact Or.inr (Or.inr (c.trans h))

private theorem ring {V : Type*} (G : SimpleGraph V) (l : List V) (big : 3 ≤ l.length)
    (nd : l.Nodup) (path : l.IsChain G.Adj)
    (close : ∀ h : l≠[], G.Adj (l.getLast h) (l.head h)) : cycleGraph l.length ⊑ G := by
  have ne : l≠[] := List.length_pos_iff.mp (by omega)
  have len : (List.ofFn (n:=1) (fun _ => l)).flatten.length = l.length := by simp
  have h := cycle_of_chunks G (n:=1) (fun _ => l) (fun _ => ne) (fun _ => nd)
    (fun i j h => (h (Subsingleton.elim i j)).elim) (fun _ => path)
    (fun _ => close ne) (len ▸ big)
  rw [len] at h
  exact h

variable {A : Type*} [AddCommGroup A]
variable {V : Type*} {G : SimpleGraph V}

/-- Two different, nonopposite internal steps and the matching between the
rows trace the eight corners of a rectangle. Coincident steps give a square. -/
theorem matched_steps (l r : A ↪ V) (apart : ∀ x y, l x ≠ r y)
    (s t : A) (hs : s ≠ 0) (ht : t ≠ 0)
    (left : ∀ x, G.Adj (l x) (l (x+s))) (right : ∀ x, G.Adj (r x) (r (x+t)))
    (rung : ∀ x, G.Adj (l x) (r x)) : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G := by
  have ls : G.Adj (l 0) (l s) := by simpa using left 0
  have rt : G.Adj (r 0) (r t) := by simpa using right 0
  have sq (edge : G.Adj (r 0) (r s)) : cycleGraph 4 ⊑ G :=
    square_of_four ls (rung _) edge.symm (rung _).symm (apart _ _) (apart _ _)
  by_cases eq : s=t
  · exact Or.inl (sq (eq ▸ rt))
  by_cases cancel : s+t=0
  · exact Or.inl (sq (by simpa [cancel] using (right s).symm))
  have ss : s ≠ s+t := by simpa using ht
  have tt : t ≠ s+t := by simpa using hs
  have reduced (x y : A) : r x ≠ l y := (apart y x).symm
  apply Or.inr
  let seq := [l 0,l s,r s,r (s+t),l (s+t),l t,r t,r 0]
  have nd : seq.Nodup := by
    simp [seq,apart,reduced,hs,hs.symm,ht,ht.symm,eq,cancel,Ne.symm cancel,
      ss,tt.symm]
  have back : G.Adj (l (s+t)) (l t) := by simpa [add_comm] using (left t).symm
  have chain : seq.IsChain G.Adj := by
    simp [seq,ls,rung, right s,(rung (s+t)).symm,back,rt.symm]
  exact ring G seq (by simp [seq]) nd chain (by simpa [seq] using (rung 0).symm)

/-- A layer with three distinct internal neighbours contains a square. -/
theorem internal_square (f : A ↪ V) (a b c : A) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (edge : ∀ x u, u=a ∨ u=b ∨ u=c → G.Adj (f x) (f (x+u))) : cycleGraph 4 ⊑ G := by
  have make (u : A) (au : a≠u) (sum : a+u≠0) (mem : u=b ∨ u=c) : cycleGraph 4 ⊑ G := by
    have h1 : G.Adj (f 0) (f a) := by simpa using edge 0 a (Or.inl rfl)
    have h2 := edge a u (Or.inr mem)
    have h3 : G.Adj (f (a+u)) (f u) := by simpa [add_comm] using (edge u a (Or.inl rfl)).symm
    have h4 : G.Adj (f u) (f 0) := by simpa using (edge 0 u (Or.inr mem)).symm
    exact square_of_four h1 h2 h3 h4 (fun h => sum (f.injective h).symm)
      (fun h => au (f.injective h))
  by_cases zero : a+b=0
  · exact make c ac (fun h => bc (add_left_cancel (zero.trans h.symm))) (Or.inr rfl)
  · exact make b ab zero (Or.inl rfl)

def chart (b : Bool) (c : A) : (Bool × A) ≃ (Bool × A) where
  toFun | (false,x) => (b,x) | (true,x) => (!b,x+c)
  invFun := fun (i,x) => if i=b then (false,x) else (true,x-c)
  left_inv := by rintro ⟨i,x⟩; cases i <;> cases b <;> simp
  right_inv := by rintro ⟨i,x⟩; cases i <;> cases b <;> simp

variable (K : SimpleGraph (Bool × A))
abbrev Invariant := ∀ (d : A) {i j : Bool} {x y : A}, K.Adj (i,x) (j,y) → K.Adj (i,d+x) (j,d+y)

theorem three_cross (inv : Invariant K) (b : Bool) (c u v : A)
    (cu : c≠u) (cv : c≠v) (uv : u≠v) (h0 : K.Adj (b,0) (!b,c))
    (h1 : K.Adj (b,0) (!b,u)) (h2 : K.Adj (b,0) (!b,v)) : Short K := by
  let e := chart b c
  let J := K.comap e
  have sub : J ⊑ K := isContained_iff_exists_le_comap.mpr ⟨e.toEmbedding,le_rfl⟩
  apply short_map sub
  apply OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.HaarShort.haar_short_cycle J (u-c) (v-c)
      (sub_ne_zero.mpr cu.symm) (sub_ne_zero.mpr cv.symm) (fun h => uv (sub_left_inj.mp h))
  · intro x; simpa [J,e,chart] using inv x h0
  · intro x; simpa [J,e,chart,add_assoc] using inv x h1
  · intro x; simpa [J,e,chart,add_assoc] using inv x h2

variable [Fintype A] [DecidableRel K.Adj]

private theorem neighbours_in_row (degree : ∀ x, 3 ≤ K.degree x) (b i : Bool)
    (side : ∀ y, K.Adj (b,0) y → y.1=i) :
    ∃ a c d : A, a≠c ∧ a≠d ∧ c≠d ∧ K.Adj (b,0) (i,a) ∧
      K.Adj (b,0) (i,c) ∧ K.Adj (b,0) (i,d) := by
  obtain ⟨⟨j,a⟩,⟨k,c⟩,⟨m,d⟩,ha,hc,hd,ac,ad,cd⟩ :=
    Finset.two_lt_card_iff.mp (degree (b,0))
  rw [mem_neighborFinset] at ha hc hd
  obtain rfl : j=i := side _ ha
  obtain rfl : k=j := side _ hc
  obtain rfl : m=k := side _ hd
  exact ⟨a,c,d,fun h => ac (h ▸ rfl),fun h => ad (h ▸ rfl),fun h => cd (h ▸ rfl),ha,hc,hd⟩

/-- Every finite graph of minimum degree three invariant under simultaneous
translation of two copies of an abelian group has a 4-, 8-, or 16-cycle. -/
theorem two_regular_orbits (inv : Invariant K) (degree : ∀ x, 3 ≤ K.degree x) : Short K := by
  classical
  let layer (b : Bool) : A ↪ Bool × A := ⟨fun x => (b,x),fun _ _ e => congrArg Prod.snd e⟩
  by_cases across : ∃ c, K.Adj (false,0) (true,c)
  · obtain ⟨c,hc⟩ := across
    by_cases inside : ∀ b : Bool, ∃ s, K.Adj (b,0) (b,s)
    · obtain ⟨s,hs⟩ := inside false
      obtain ⟨t,ht⟩ := inside true
      let r : A ↪ Bool × A := (Equiv.addRight c).toEmbedding.trans (layer true)
      have h := matched_steps (G:=K) (layer false) r (fun _ _ h => Bool.false_ne_true (congrArg Prod.fst h))
        s t (fun h => hs.ne (h ▸ rfl)) (fun h => ht.ne (h ▸ rfl))
        (fun x => by change K.Adj (false,x) (false,x+s); simpa using inv x hs)
        (fun x => by change K.Adj (true,x+c) (true,x+t+c); simpa [add_assoc,add_comm c t] using inv (x+c) ht)
        (fun x => by change K.Adj (false,x) (true,x+c); simpa using inv x hc)
      exact h.imp_right Or.inl
    · push Not at inside
      obtain ⟨b,hb⟩ := inside
      obtain ⟨c,u,v,cu,cv,uv,e,f,g⟩ := neighbours_in_row K degree b (!b) (by
        rintro ⟨i,x⟩ adj
        cases b <;> cases i <;> simp_all)
      exact three_cross K inv b c u v cu cv uv e f g
  · push Not at across
    obtain ⟨a,b,c,ab,ac,bc,e,f,g⟩ := neighbours_in_row K degree false false (by
      rintro ⟨i,x⟩ adj; cases i <;> simp_all)
    apply Or.inl (internal_square (layer false) a b c ab ac bc ?_)
    rintro x u (rfl|rfl|rfl)
    · change K.Adj (false,x) (false,x+u); simpa using inv x e
    · change K.Adj (false,x) (false,x+u); simpa using inv x f
    · change K.Adj (false,x) (false,x+u); simpa using inv x g

end Erdos64TwoOrbits
