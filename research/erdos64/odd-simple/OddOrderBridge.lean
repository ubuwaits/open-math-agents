import Mathlib

/-- Specialize the independently verified odd-order theorem to the precise
simple-group target used in the Erdős 64 reduction. -/
theorem odd_simple_from_odd_order
    (oddOrder : ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → Group.IsSolvable G)
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (odd : Odd (Nat.card S)) :
    ∀ a b : S, a * b = b * a :=
  IsSimpleGroup.comm_iff_isSolvable.mpr (oddOrder S odd)

#print axioms odd_simple_from_odd_order
