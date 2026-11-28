import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Tetrahedral covers on the finite Heisenberg group

Chad Mazzola (@ubuwaits), using Codex.

The sheets are triples (x,y,z) over Z/n. Two chords act by left
multiplication by (1,0,0) and (0,1,0) in the upper unitriangular
group of size n cubed. The third chord is the identity. One simple
32-cycle works at every modulus at least four. The explicit shorter
cycles cover the remaining moduli and show the positive half of the
shortest-length classification.
-/

namespace Erdos64Heisenberg

open Function SimpleGraph Fin.NatCast

abbrev Sheet (R : Type) := R × R × R

def shiftX {R : Type} [Ring R] (s : Sheet R) : Sheet R := (s.1+1,s.2.1,s.2.2+s.2.1)
def shiftY {R : Type} [Ring R] (s : Sheet R) : Sheet R := (s.1,s.2.1+1,s.2.2)

/-- Tree matchings and chord 31 preserve the sheet. -/
def oriented {R : Type} [Ring R] (u v : Fin 4 × Sheet R) : Prop :=
  (u.1=0 ∧ v.1≠0 ∧ v.2=u.2) ∨ (u.1=1 ∧ v.1=2 ∧ v.2=shiftX u.2) ∨
  (u.1=2 ∧ v.1=3 ∧ v.2=shiftY u.2) ∨ (u.1=3 ∧ v.1=1 ∧ v.2=u.2)

def graph (R : Type) [Ring R] : SimpleGraph (Fin 4 × Sheet R) := SimpleGraph.fromRel oriented

instance {R : Type} [Ring R] [DecidableEq R] : DecidableRel (graph R).Adj := fun u v => by
  change Decidable (u ≠ v ∧ (oriented u v ∨ oriented v u))
  unfold oriented
  infer_instance

private theorem cycle_of_table {V : Type} (G : SimpleGraph V) {m : ℕ} [NeZero m]
    (size : 3 ≤ m) (a : Fin m → V) (distinct : Injective a) (edges : ∀ i, G.Adj (a i) (a (i+1))) :
    cycleGraph m ⊑ G := by
  refine ⟨⟨⟨a,?_⟩,distinct⟩⟩
  intro i j h
  have one : 1 < m := by omega
  have diff : i-j=1 ∨ j-i=1 := by
    simpa only [Fin.ext_iff, Fin.val_one',Nat.mod_eq_of_lt one] using cycleGraph_adj'.mp h
  rcases diff with h | h
  · have eq : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [eq] using (edges j).symm
  · have eq : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [eq] using edges i

private def castSheet (n : ℕ) (s : Sheet ℤ) : Sheet (ZMod n) :=
  ((s.1 : ZMod n),(s.2.1 : ZMod n),(s.2.2 : ZMod n))

private theorem map_edge (n : ℕ) {v w : Fin 4 × Sheet ℤ} (h : (graph ℤ).Adj v w) :
    (graph (ZMod n)).Adj (v.1,castSheet n v.2) (w.1,castSheet n w.2) := by
  have dir {v w : Fin 4 × Sheet ℤ} (h : oriented v w) :
      (graph (ZMod n)).Adj (v.1,castSheet n v.2) (w.1,castSheet n w.2) := by
    obtain ⟨i,s⟩ := v
    obtain ⟨j,t⟩ := w
    rcases h with h | h | h | h
    · obtain ⟨rfl,hj,rfl⟩ := h
      simp [graph,oriented,hj,Ne.symm hj]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      simp [graph,oriented,castSheet,shiftX]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      simp [graph,oriented,castSheet,shiftY]
    · obtain ⟨rfl,rfl,rfl⟩ := h
      simp [graph,oriented]
  exact h.2.elim dir (fun edge => (dir edge).symm)

private abbrev Code := Fin 4 × Fin 4 × Fin 3 × Fin 3

private def decode (t : Code) : Fin 4 × Sheet ℤ :=
  (t.1,(t.2.1.val : ℤ)-3,(t.2.2.1.val : ℤ)-1,(t.2.2.2.val : ℤ))

private def table32 : Fin 32 → Code :=
  ![(0,3,1,0), (1,3,1,0), (3,3,1,0), (2,3,0,0),
    (1,2,0,1), (0,2,0,1), (2,2,0,1), (1,1,0,2),
    (0,1,0,2), (2,1,0,2), (3,1,1,2), (1,1,1,2),
    (2,2,1,2), (3,2,2,2), (0,2,2,2), (2,2,2,2),
    (1,1,2,1), (0,1,2,1), (2,1,2,1), (1,0,2,0),
    (0,0,2,0), (3,0,2,0), (2,0,1,0), (0,0,1,0),
    (1,0,1,0), (2,1,1,0), (0,1,1,0), (1,1,1,0),
    (2,2,1,0), (0,2,1,0), (1,2,1,0), (2,3,1,0)]
private theorem cast_small {m n : ℕ} [NeZero n] (hm : m ≤ n) :
    Injective (fun x : Fin m => (x.val : ZMod n)) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (a.isLt.trans_le hm),
    Nat.mod_eq_of_lt (b.isLt.trans_le hm)] using hv

private theorem decode_injective (n : ℕ) (hn : 4 ≤ n) :
    Injective (fun t : Code => ((decode t).1,castSheet n (decode t).2)) := by
  let : NeZero n := ⟨by omega⟩
  rintro ⟨i,x,y,z⟩ ⟨j,u,v,w⟩ h
  simp only [decode, castSheet, Int.cast_sub,Int.cast_natCast,Int.cast_ofNat,
    Int.cast_one,Prod.mk.injEq] at h
  obtain ⟨hij,hx,hy,hz⟩ := h
  have ex : x = u := cast_small hn (sub_left_inj.mp hx)
  have ey : y = v := cast_small (show 3 ≤ n by omega)
    (sub_left_inj.mp hy)
  exact Prod.ext hij (Prod.ext ex (Prod.ext ey (cast_small (by omega) hz)))

/-- An integral color word gives a simple cycle for every modulus at least four. -/
theorem cycle_32 {n : ℕ} (hn : 4 ≤ n) : cycleGraph 32 ⊑ graph (ZMod n) := by
  have inj : Injective table32 := by decide
  have edges : ∀ i : Fin 32, (graph ℤ).Adj (decode (table32 i)) (decode (table32 (i+1))) := by decide
  exact cycle_of_table _ (by decide) _ ((decode_injective n hn).comp inj) (fun i => map_edge n (edges i))

theorem modulus_1 : cycleGraph 4 ⊑ graph (ZMod 1) := by
  let a : Fin 4 → Fin 4 × Sheet (ZMod 1) :=
    ![(0,0,0,0), (1,0,0,0), (2,0,0,0), (3,0,0,0)]
  exact cycle_of_table _ (by decide) a (by decide) (by decide)

theorem modulus_2 : cycleGraph 8 ⊑ graph (ZMod 2) := by
  let a : Fin 8 → Fin 4 × Sheet (ZMod 2) :=
    ![(0,0,0,0), (1,0,0,0), (3,0,0,0), (2,0,1,0),
    (0,0,1,0), (1,0,1,0), (3,0,1,0), (2,0,0,0)]
  exact cycle_of_table _ (by decide) a (by decide) (by decide)

theorem modulus_3 : cycleGraph 16 ⊑ graph (ZMod 3) := by
  let a : Fin 16 → Fin 4 × Sheet (ZMod 3) :=
    ![(0,0,0,0), (1,0,0,0), (2,1,0,0), (0,1,0,0),
    (1,1,0,0), (2,2,0,0), (0,2,0,0), (1,2,0,0),
    (2,0,0,0), (3,0,1,0), (0,0,1,0), (2,0,1,0),
    (3,0,2,0), (0,0,2,0), (2,0,2,0), (3,0,0,0)]
  exact cycle_of_table _ (by decide) a (by decide) (by decide)

theorem modulus_4 : cycleGraph 16 ⊑ graph (ZMod 4) := by
  let a : Fin 16 → Fin 4 × Sheet (ZMod 4) :=
    ![(0,0,0,0), (1,0,0,0), (2,1,0,0), (0,1,0,0),
    (1,1,0,0), (2,2,0,0), (3,2,1,0), (1,2,1,0),
    (2,3,1,1), (3,3,2,1), (0,3,2,1), (2,3,2,1),
    (3,3,3,1), (1,3,3,1), (2,0,3,0), (3,0,0,0)]
  exact cycle_of_table _ (by decide) a (by decide) (by decide)

theorem modulus_5 : cycleGraph 16 ⊑ graph (ZMod 5) := by
  let a : Fin 16 → Fin 4 × Sheet (ZMod 5) :=
    ![(0,0,0,0), (1,0,0,0), (2,1,0,0), (0,1,0,0),
    (1,1,0,0), (2,2,0,0), (0,2,0,0), (1,2,0,0),
    (2,3,0,0), (0,3,0,0), (1,3,0,0), (2,4,0,0),
    (0,4,0,0), (3,4,0,0), (1,4,0,0), (2,0,0,0)]
  exact cycle_of_table _ (by decide) a (by decide) (by decide)

/-- Each positive modulus has a simple cycle of power-of-two length at most 32. -/
theorem power_cycle (n : ℕ) (positive : 0 < n) :
    ∃ k : ℕ, 2 ≤ k ∧ 2^k ≤ 32 ∧ cycleGraph (2^k) ⊑ graph (ZMod n) := by
  by_cases hn : 4 ≤ n
  · exact ⟨5,by decide,by decide,cycle_32 hn⟩
  interval_cases n
  · exact ⟨2,by decide,by decide,modulus_1⟩
  · exact ⟨3,by decide,by decide,modulus_2⟩
  · exact ⟨4,by decide,by decide,modulus_3⟩

end Erdos64Heisenberg
