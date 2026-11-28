import Mathlib

/-! Arithmetic and the finite digit obstruction for a pair of prime chains. -/

namespace Erdos1052.PairChains

theorem product_lift (F p q b x y : ℕ) :
    F*(p+b*x)*(q+b*y) = F*p*q + b*(F*(x*q+y*p+b*x*y)) := by ring

theorem two_additions (b u v : ℕ) :
    (1+2*b)*(1+b*u)*(1+b*v) =
      1+b*(2+u+v+b*(u*v+2*u+2*v)+2*b^2*u*v) := by ring

/-- The first two coefficients read by the three-root digit check at scale b = 2^m. -/
theorem three_additions (b u v w : ℕ) :
    (1+4*b)*(1+b*u)*(1+b*v)*(1+b*w) =
      1+b*(4+u+v+w+b*(u*v+u*w+v*w+4*(u+v+w))+
        b^2*(u*v*w+4*(u*v+u*w+v*w))+4*b^3*u*v*w) := by ring

theorem strip_odd_shift {q r j : ℕ} (hr : 0<r) (hj : 0<j) (hq : q+1=2^j*r) :
    q-1=2^j*(r-1)+(2^j-2) := by
  have hj' : 2≤2^j := by
    calc 2 = (2:ℕ)^1 := by decide
         _ ≤ 2^j := Nat.pow_le_pow_right (by decide) hj
  have he : 2^j*r=2^j*(r-1)+2^j := by
    conv_lhs => rw [show r=(r-1)+1 by omega, Nat.mul_add, Nat.mul_one]
  omega

theorem initial_residues :
    (∀ a : ZMod 5, (∀ i : Fin 4, 1+(a-1)*3^i.val≠0) → a=1) ∧
    (∀ a : ZMod 11, (∀ i : Fin 10, 1+(a-1)*6^i.val≠0) → a=1) ∧
    (∀ a : ZMod 13, (∀ i : Fin 12, 1+(a-1)*7^i.val≠0) → a=1) ∧
    (∀ a : ZMod 29, (∀ i : Fin 28, 1+(a-1)*15^i.val≠0) → a=1) := by
  decide

structure Word where
  run : ℕ
  residue : ℕ
  deriving DecidableEq

/-- Read the next low bit of an endpoint minus one, sieving modulo eleven. -/
def readBit (x : ℕ) (s : Word) : Option Word :=
  if x=0 ∧ (s.run≠0 ∨ s.residue=9 ∨ s.residue=10) then none
  else some ⟨if x=0 then 0 else (s.run+1)%4, ((s.residue+11-x)*6)%11⟩

structure Pair where
  p : ℕ
  q : ℕ
  carry : ℕ
  left : Word
  right : Word

/-- All one-bit lifts of 65537 times a product, fixing the order on equal prefixes. -/
def lift (place : ℕ) (s : Pair) (x : ℕ) : Option Pair := do
  let y := (s.carry+x)%2
  if s.p=s.q ∧ y<x then none else
    let l ← readBit x s.left
    let r ← readBit y s.right
    let extra := 65537*(x*s.q+y*s.p+place*x*y)
    return ⟨s.p+place*x,s.q+place*y,(s.carry+extra)/2,l,r⟩

def survives : ℕ → ℕ → Pair → Bool
  | 0, _, _ => true
  | n+1, place, s => [0,1].any fun x =>
      ((lift place s x).map (survives n (2*place))).getD false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Bits 15 through 47 leave no pair even with a single sieving modulus. -/
theorem obstruction_sixteen :
    survives 33 (2^15) ⟨1,1,2,⟨0,0⟩,⟨0,0⟩⟩ = false := by decide

end Erdos1052.PairChains
