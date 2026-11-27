import SparseOddExponent

/-! Multiplicative terminal bounds for simultaneous prime-power layers. -/

namespace Erdos1052.LayerMass

open Erdos1052.Core625 Erdos1052.DistinctFactors

/-- Split the actual squarefree support between all seeds before multiplying
the lower bounds on their terminal divisors. -/
theorem terminal_product (seeds : List ℕ) {S V : Finset ℕ} {C D D₀ m : ℕ}
    (hsubset : S ⊆ V) (hpr : primeSupport S) (hD : D ≠ 0) (hdiv : D ∣ D₀)
    (hcost : ∀ A ∈ seeds, ∀ T ⊆ V, ∀ d, d ∣ D₀ →
      A*demands T=d*primesProduct T → m≤d)
    (hbal : seeds.prod*C*demands S=D*primesProduct S) : m^seeds.length≤D := by
  induction seeds generalizing S D with
  | nil => simp only [List.length_nil, pow_zero]; omega
  | cons A rest ih =>
    obtain ⟨T,U,d,e,_,hTU,hde,ht,hu⟩ := split_support S hpr
      (show A*(rest.prod*C)*demands S=D*primesProduct S by
        simpa only [List.prod_cons, mul_assoc] using hbal)
    have hT : T ⊆ S := hTU ▸ Finset.subset_union_left
    have hU : U ⊆ S := hTU ▸ Finset.subset_union_right
    have hd : d ∣ D := ⟨e,hde.symm⟩
    have he : e ∣ D := ⟨d,by simpa [mul_comm] using hde.symm⟩
    have hm := hcost A List.mem_cons_self T (hT.trans hsubset) d (hd.trans hdiv) ht
    have he₀ : e≠0 := fun h => hD (by simpa [h] using hde.symm)
    have hr := ih (hU.trans hsubset) (fun q hq => hpr q (hU hq)) he₀ (he.trans hdiv)
      (fun a ha => hcost a (List.mem_cons_of_mem A ha)) hu
    simpa [pow_succ, hde, mul_comm] using Nat.mul_le_mul hm hr

/-- Apply the terminal bound to the actual simultaneous prime-power factors
of (2^(h*b)+1)/(2^h+1), using the residual group balance. -/
theorem prime_power_mass {b h D A m : ℕ} {S : Finset ℕ} (hb : Odd b)
    (hD : D≠0) (hp : primeSupport S) (hseed : A*(2^h+1)=2^(h*b)+1)
    (hbal : A*demands S=D*primesProduct S)
    (hcost : ∀ p ∈ b.primeFactors, ∀ j < b.factorization p, ∀ T ⊆ S,
      ∀ d, d ∣ D → layer h (p^(j+1))*demands T=d*primesProduct T → m≤d) :
    m^(∑ p ∈ b.primeFactors, b.factorization p) ≤ D := by
  let V := fun p => (Finset.range (b.factorization p)).image (fun j => p^(j+1))
  let U := b.primeFactors.biUnion V
  have hmem {i : ℕ} (hi : i∈U) :
      ∃ p ∈ b.primeFactors, ∃ j < b.factorization p, p^(j+1)=i := by
    obtain ⟨p,hp,ht⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ht
    exact ⟨p,hp,j,Finset.mem_range.mp hj,he⟩
  have hsz : U.card=∑ p ∈ b.primeFactors, b.factorization p := by
    have dis : (↑b.primeFactors : Set ℕ).PairwiseDisjoint V := by
      intro p hp q hq hn
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hy
      exact hn ((Nat.prime_of_mem_primeFactors hp).pow_inj (Nat.prime_of_mem_primeFactors hq)
        (hi.trans hj.symm)).1
    rw [show U=b.primeFactors.biUnion V by rfl, Finset.card_biUnion dis]
    apply Finset.sum_congr rfl
    intro p hp
    change (Finset.image _ _).card=_
    rw [Finset.card_image_of_injOn,Finset.card_range]
    intro i _ j _ he
    have hh := ((Nat.prime_of_mem_primeFactors hp).pow_inj (Nat.prime_of_mem_primeFactors hp) he).2
    omega
  have hd := independent_layers h hb odd_one (one_dvd b) U (by
    intro i hi
    obtain ⟨p,hp,j,hj,rfl⟩ := hmem hi
    exact ⟨(Nat.pow_dvd_pow p hj).trans (Nat.ordProj_dvd b p), fun hh =>
      (ne_of_gt (one_lt_pow₀ (Nat.prime_of_mem_primeFactors hp).one_lt (by omega))) (Nat.dvd_one.mp hh)⟩)
  rw [mul_one, ←hseed] at hd
  have ha : (∏ i ∈ U, layer h i) ∣ A := Nat.dvd_of_mul_dvd_mul_right (by positivity) hd
  obtain ⟨C,hC⟩ := ha
  let seeds := U.toList.map (layer h)
  have hs : seeds.prod*C*demands S=D*primesProduct S := by
    simpa [seeds, Finset.prod_map_toList, ←hC] using hbal
  have hh := terminal_product seeds (S:=S) (V:=S) (D₀:=D) (m:=m)
    (fun _ hi => hi) hp hD (dvd_refl D) (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      obtain ⟨p,hp,j,hj,rfl⟩ := hmem (Finset.mem_toList.mp hi)
      exact hcost p hp j hj) hs
  simpa only [seeds,List.length_map,Finset.length_toList,hsz] using hh

end Erdos1052.LayerMass
