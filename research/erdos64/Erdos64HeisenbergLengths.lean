import Erdos64Heisenberg

/-!
# Exact shortest power-of-two cycles in the Heisenberg covers

Chad Mazzola (@ubuwaits), using Codex.
The integral walk starting on the identity sheet tracks any color sequence.
Its reduction modulo n and right translation recover the same walk from an
arbitrary starting sheet. Finite enumeration bounds a nonzero coordinate of
the return whenever the projected walk could have been a short simple cycle.
The entire enumeration is verified by the Lean kernel.
-/

namespace Erdos64Heisenberg

/-- Sheet reached by the matching from color i to color j. -/
def move {R : Type} [Ring R] (i j : Fin 4) (s : Sheet R) : Sheet R :=
  if i=1 ∧ j=2 then shiftX s else
  if i=2 ∧ j=1 then (s.1-1,s.2.1,s.2.2-s.2.1) else
  if i=2 ∧ j=3 then shiftY s else
  if i=3 ∧ j=2 then (s.1,s.2.1-1,s.2.2) else s

/-- At least one final coordinate is nonzero and has magnitude at most B. -/
def escapes (B : ℕ) (s : Sheet ℤ) : Bool :=
  let small (x : ℤ) := decide (0 < x.natAbs ∧ x.natAbs ≤ B)
  small s.1 || small s.2.1 || small s.2.2

/-- Check every simple continuation of this integral prefix before its final edge. -/
def certified (B : ℕ) (first : Fin 4) : ℕ → Fin 4 × Sheet ℤ → List (Fin 4 × Sheet ℤ) → Bool
  | 0, v, _ => decide (v.1=first) || escapes B (move v.1 first v.2)
  | fuel+1, v, seen => [0,1,2,3].all fun j =>
      let w := (j,move v.1 j v.2)
      decide (j=v.1) || decide (w ∈ seen) || certified B first fuel w (w::seen)

/-- Start the enumeration at a specified color on the identity sheet. -/
def starts (B steps : ℕ) (i : Fin 4) : Bool :=
  certified B i steps (i,0,0,0) [(i,0,0,0)]


open Function SimpleGraph Fin.NatCast

private theorem backtrack {R : Type} [Ring R] (i j : Fin 4) (s : Sheet R) :
    move j i (move i j s) = s := by
  rcases s with ⟨x,y,z⟩
  fin_cases i <;> fin_cases j <;> simp [move,shiftX,shiftY]

private theorem edge_move {R : Type} [Ring R] {v w : Fin 4 × Sheet R} (h : (graph R).Adj v w) :
    v.1 ≠ w.1 ∧ move v.1 w.1 v.2 = w.2 := by
  have directed {v w : Fin 4 × Sheet R} (o : oriented v w) :
      v.1 ≠ w.1 ∧ move v.1 w.1 v.2 = w.2 := by
    obtain ⟨i,x⟩ := v
    obtain ⟨j,y⟩ := w
    rcases o with o | o | o | o
    · obtain ⟨rfl,hj,rfl⟩ := o
      exact ⟨Ne.symm hj,by simp [move]⟩
    · obtain ⟨rfl,rfl,rfl⟩ := o
      exact ⟨by simp,rfl⟩
    · obtain ⟨rfl,rfl,rfl⟩ := o
      exact ⟨by simp,rfl⟩
    · obtain ⟨rfl,rfl,rfl⟩ := o
      exact ⟨by simp,rfl⟩
  rcases h.2 with edge | edge
  · exact directed edge
  · obtain ⟨colors,h⟩ := directed edge
    exact ⟨colors.symm,by rw [← h,backtrack]⟩

/-- Reduction modulo n followed by right translation to the chosen starting sheet. -/
private def translate (n : ℕ) (s : Sheet (ZMod n)) (v : Sheet ℤ) : Sheet (ZMod n) :=
  ((v.1 : ZMod n)+s.1, (v.2.1 : ZMod n)+s.2.1,
    (v.2.2 : ZMod n)+s.2.2+(v.1 : ZMod n)*s.2.1)

private theorem translate_step (n : ℕ) (s : Sheet (ZMod n)) (i j : Fin 4) (v : Sheet ℤ) :
    translate n s (move i j v) = move i j (translate n s v) := by
  obtain ⟨x,y,z⟩ := v
  obtain ⟨a,b,c⟩ := s
  fin_cases i <;> fin_cases j <;> simp [move,translate,shiftX,shiftY,add_mul,sub_mul] <;>
    first | (apply And.intro <;> ring) | ring

private theorem exclude_small {B n : ℕ} (large : B < n) (s : Sheet (ZMod n)) (v : Sheet ℤ)
    (closed : translate n s v = s) : escapes B v = false := by
  have xzero : (v.1 : ZMod n) = 0 := by
    have h := congrArg Prod.fst closed
    change (v.1 : ZMod n)+s.1=s.1 at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have yzero : (v.2.1 : ZMod n) = 0 := by
    have h := congrArg (fun z : Sheet (ZMod n) => z.2.1) closed
    change (v.2.1 : ZMod n)+s.2.1=s.2.1 at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have zzero : (v.2.2 : ZMod n) = 0 := by
    have h := congrArg (fun z : Sheet (ZMod n) => z.2.2) closed
    change (v.2.2 : ZMod n)+s.2.2+(v.1 : ZMod n)*s.2.1 = s.2.2 at h
    rw [xzero,zero_mul,add_zero] at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have noSmall (a : ℤ) (zero : (a : ZMod n) = 0) : ¬ (0 < a.natAbs ∧ a.natAbs ≤ B) := by
    rintro ⟨pos,upper⟩
    have h : (n : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp zero
    have absdiv : n ∣ a.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h)
    exact (Nat.not_lt_of_ge ((Nat.le_of_dvd pos absdiv).trans upper)) large
  simp only [escapes, decide_eq_false (noSmall _ xzero), decide_eq_false (noSmall _ yzero),
    decide_eq_false (noSmall _ zzero), Bool.false_or]

/-- A verified integer-path census rules out all moduli exceeding its bound. -/
theorem excluded {m B n : ℕ} (len : 3 ≤ m) (large : B < n)
    (check : ∀ i, starts B (m-1) i = true) : ¬ cycleGraph m ⊑ graph (ZMod n) := by
  classical
  let : NeZero m := ⟨by omega⟩
  rintro ⟨path⟩
  let a (t : ℕ) := path (t : Fin m)
  let color (t : ℕ) := (a t).1
  let sheet := (a 0).2
  have side (t : ℕ) : (graph (ZMod n)).Adj (a t) (a (t+1)) := by
    apply path.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    rw [Nat.cast_succ,add_sub_cancel_left]
    simp [Nat.mod_eq_of_lt (show 1 < m by omega)]
  have colorDiff (t : ℕ) : color t ≠ color (t+1) := (edge_move (side t)).1
  let lift : ℕ → Fin 4 × Sheet ℤ := Nat.rec (color 0,0,0,0)
    (fun t v => (color (t+1),move v.1 (color (t+1)) v.2))
  have colorEq (t : ℕ) : (lift t).1 = color t := by cases t <;> rfl
  have project (t : ℕ) : ((lift t).1, translate n sheet (lift t).2) = a t := by
    induction t with
    | zero => exact Prod.ext rfl (by simp [lift,translate,sheet])
    | succ t ih =>
      apply Prod.ext (colorEq (t+1))
      change translate n sheet (move (lift t).1 (color (t+1)) (lift t).2) = _
      have sheets : translate n sheet (lift t).2 = (a t).2 := congrArg Prod.snd ih
      rw [translate_step,colorEq,sheets]
      exact (edge_move (side t)).2
  have distinct {r t : ℕ} (hr : r<m) (ht : t<m) (equal : lift r = lift t) : r=t := by
    have h := congrArg (fun v : Fin 4 × Sheet ℤ => (v.1,translate n sheet v.2)) equal
    change ((lift r).1,_) = ((lift t).1,_) at h
    rw [project,project] at h
    have e := congrArg Fin.val (path.injective h)
    simpa only [Fin.val_natCast,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt ht] using e
  let seen : ℕ → List (Fin 4 × Sheet ℤ) := Nat.rec [lift 0] (fun t l => lift (t+1)::l)
  have before (t : ℕ) {v} (hv : v ∈ seen t) : ∃ r ≤ t, v=lift r := by
    induction t with
    | zero =>
      change v ∈ [lift 0] at hv
      exact ⟨0,le_rfl,List.mem_singleton.mp hv⟩
    | succ t ih =>
      change v ∈ lift (t+1)::seen t at hv
      rcases List.mem_cons.mp hv with h | h
      · exact ⟨t+1,le_rfl,h⟩
      · obtain ⟨r,hr,e⟩ := ih h
        exact ⟨r,by omega,e⟩
  have colors : ∀ i : Fin 4, i ∈ ([0,1,2,3] : List (Fin 4)) := by decide
  have running (t : ℕ) (ht : t<m) :
      certified B (color 0) (m-(t+1)) (lift t) (seen t) = true := by
    induction t with
    | zero => exact check (color 0)
    | succ t ih =>
      have prev := ih (by omega)
      rw [show m-(t+1)=(m-(t+2))+1 by omega,certified,List.all_eq_true] at prev
      have c := prev (color (t+1)) (colors _)
      have diff : color (t+1) ≠ (lift t).1 := (colorEq t) ▸ (colorDiff t).symm
      have fresh : lift (t+1) ∉ seen t := by
        intro mem
        obtain ⟨r,hr,equal⟩ := before t mem
        have := distinct ht (by omega) equal
        omega
      rcases Bool.or_eq_true_iff.mp c with early | next
      · rcases Bool.or_eq_true_iff.mp early with eqColor | duplicate
        · exact (diff (of_decide_eq_true eqColor)).elim
        · simp only [decide_eq_true_eq] at duplicate
          exact (fresh duplicate).elim
      · exact next
  let last := m-1
  have lastLt : last<m := by dsimp [last]; omega
  have done := running last lastLt
  rw [show m-(last+1)=0 by dsimp [last]; omega,certified] at done
  have lap : a (last+1) = a 0 := by
    change path ((last+1 : ℕ) : Fin m) = path (0 : Fin m)
    rw [show last+1=m by dsimp [last]; omega]
    simp
  have sameColor : color (last+1) = color 0 := congrArg Prod.fst lap
  have different : (lift last).1 ≠ color 0 := by
    rw [colorEq,← sameColor]
    exact colorDiff last
  have closed := congrArg Prod.snd ((project (last+1)).trans lap)
  change translate n sheet (move (lift last).1 (color (last+1)) (lift last).2) = sheet at closed
  rw [sameColor] at closed
  simp only [decide_eq_false different,Bool.false_or,exclude_small large sheet _ closed] at done
  contradiction


theorem check4 : ∀ i, starts 1 3 i = true := by decide
theorem check8 : ∀ i, starts 2 7 i = true := by decide

/-- Split off the four possible next colors before evaluating a continuation. -/
private theorem prefix_node {B : ℕ} {first : Fin 4} {n : ℕ} {v : Fin 4 × Sheet ℤ}
    {seen : List (Fin 4 × Sheet ℤ)} (children : ∀ j : Fin 4,
      let w := (j,move v.1 j v.2)
      ((decide (j=v.1) || decide (w ∈ seen)) || certified B first n w (w::seen)) = true) :
    certified B first (n+1) v seen = true := by
  rw [certified,List.all_eq_true]
  exact fun j _ => children j

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
/-- Normalize the first three edges of each prefix before checking its remaining continuations. -/
theorem check16 : ∀ i, starts 5 15 i = true := by
  intro i
  fin_cases i <;> unfold starts
  iterate 3
    all_goals
      apply prefix_node
      intro j
      fin_cases j <;> first
        | exact Bool.or_eq_true_iff.mpr (.inl (by decide))
        | apply Bool.or_eq_true_iff.mpr; right; norm_num [move,shiftX,shiftY]
  all_goals decide +kernel

/-- Exponent of the least power-of-two simple cycle length. -/
def leastExponent (n : ℕ) : ℕ :=
  if n = 1 then 2 else if n = 2 then 3 else if n ≤ 5 then 4 else 5

private theorem classify_of_checks
    (four : ∀ i, starts 1 3 i = true) (eight : ∀ i, starts 2 7 i = true)
    (sixteen : ∀ i, starts 5 15 i = true) (n : ℕ) (positive : 0 < n) :
    cycleGraph (2^(leastExponent n)) ⊑ graph (ZMod n) ∧
    ∀ k : ℕ, 2 ≤ k → k < leastExponent n → ¬ cycleGraph (2^k) ⊑ graph (ZMod n) := by
  constructor
  · by_cases large : 6 ≤ n
    · have e : leastExponent n = 5 := by
        simp [leastExponent,show n ≠ 1 by omega,show n ≠ 2 by omega,show ¬n ≤ 5 by omega]
      rw [e]
      exact cycle_32 (by omega)
    · have h : n ≤ 5 := by omega
      interval_cases n
      · exact modulus_1
      · exact modulus_2
      · exact modulus_3
      · exact modulus_4
      · exact modulus_5
  · intro k lower upper
    have maxExp : leastExponent n ≤ 5 := by unfold leastExponent; split_ifs <;> decide
    have small : k ≤ 4 := by omega
    interval_cases k
    · apply excluded (m := 4) (B := 1) (by decide) _ four
      unfold leastExponent at upper
      split_ifs at upper <;> omega
    · apply excluded (m := 8) (B := 2) (by decide) _ eight
      unfold leastExponent at upper
      split_ifs at upper <;> omega
    · apply excluded (m := 16) (B := 5) (by decide) _ sixteen
      unfold leastExponent at upper
      split_ifs at upper <;> omega


/-- The shortest dyadic cycle length is 4 at n=1, 8 at n=2, 16 at n=3,4,5,
and 32 for every n at least six. -/
theorem exact_shortest_power (n : ℕ) (positive : 0 < n) :
    cycleGraph (2^(leastExponent n)) ⊑ graph (ZMod n) ∧
    ∀ k : ℕ, 2 ≤ k → k < leastExponent n → ¬ cycleGraph (2^k) ⊑ graph (ZMod n) :=
  classify_of_checks check4 check8 check16 n positive

end Erdos64Heisenberg
