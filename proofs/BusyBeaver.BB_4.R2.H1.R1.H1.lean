import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1

-- Checker and branch certificates from @hyprspacecoyote, PR 4446.
namespace OMA.BB4H1

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Key := State × Symbol
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move

def Table.empty : Table := ⟨none, none, none, none, none, none, none, none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _, _ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq, Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1), ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position) (m : Move) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0, _ => []
  | k + 1, [] => 0 :: takePad k []
  | k + 1, x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad, List.foldr_cons, List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad, List.foldr_cons, List.drop_succ_cons]
      rw [ih xs, ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0, q, a, near, rs => some (q, a, near, rs)
  | k + 1, q, a, near, rs =>
    match tb.get q a with
    | none => none
    | some m =>
      if m.left then
        match near with
        | [] => none
        | a' :: near' => runGuardedLeft tb k m.state a' near' (push m.write rs)
      else
        runGuardedLeft tb k m.state (symHead rs) (m.write :: near) rs.tail

def checkGuardedLeft (tb : Table) (p : ℕ) (q : State) (a : Symbol)
    (near rs : List Symbol) : Bool :=
  match runGuardedLeft tb p q a near rs with
  | none => false
  | some (q', a', near', rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q', a', near', rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q', ⟨a', near'.foldr ListBlank.cons tail, ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | true =>
        simp only [hd, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, (x :: xs).foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
              some ⟨some m.state, ⟨x, xs.foldr ListBlank.cons tail, ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
            some ⟨some m.state, ⟨symHead rs, (m.write :: near).foldr ListBlank.cons tail, ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q', a', near', ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q', ⟨a', ListBlank.mk ls', near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht, Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip, hd, Bool.not_false, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, (x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state, ⟨x, ListBlank.mk (push m.write ls), xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state, ⟨symHead ls, ListBlank.mk ls.tail, (m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q, ⟨a, near.foldr ListBlank.cons tail', ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', rs'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hrs⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', ls'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hls⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedRight_sound hm p q' a' near ls' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

structure HistItem where
  step : ℕ
  pos : ℕ
  c : Position

def findRepAux (tb : Table) (cur : HistItem) (minp maxp : ℕ) : List HistItem → Bool
  | [] => false
  | hi :: rest =>
    let minp' := if Nat.ble minp hi.pos then minp else hi.pos
    let maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    let ok :=
      if Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val then
        let p := cur.step - hi.step
        let leftOk :=
          if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
            let dL := hi.pos - minp'
            let near := takePad dL hi.c.ls
            if listEq (takePad dL cur.c.ls) near then
              checkGuardedLeft tb p hi.c.state hi.c.head near hi.c.rs
            else false
          else false
        if leftOk then true
        else if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
          let dR := maxp' - hi.pos
          let near := takePad dR hi.c.rs
          if listEq (takePad dR cur.c.rs) near then
            checkGuardedLeft tb.flip p hi.c.state hi.c.head near hi.c.ls
          else false
        else false
      else false
    if ok then true else findRepAux tb cur minp' maxp' rest

def findRep (tb : Table) (cur : HistItem) (prev : List HistItem) : Bool :=
  findRepAux tb cur 1000 0 prev

def HistValid (M : Machine4) (hist : List HistItem) : Prop :=
  ∀ h ∈ hist, h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg Symbol State)
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')

theorem findRepAux_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem}
    (hcur : cur.step ≤ 107) (hvalid : HistValid M prev)
    {minp maxp : ℕ} (h : findRepAux tb cur minp maxp prev = true) : False := by
  induction prev generalizing minp maxp with
  | nil => simp [findRepAux] at h
  | cons hi rest ih =>
    unfold findRepAux at h
    dsimp only at h
    set minp' := if Nat.ble minp hi.pos then minp else hi.pos
    set maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    by_cases hcond : (Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val) = true
    · simp only [hcond, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq_true_eq] at hcond
      have ⟨hstep_hi, hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
      have hp_pos : 0 < cur.step - hi.step := by omega
      have hp_le : hi.step + (cur.step - hi.step) ≤ 107 := by omega
      by_cases hleft : (if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
          if listEq (takePad (hi.pos - minp') cur.c.ls) (takePad (hi.pos - minp') hi.c.ls) then
            checkGuardedLeft tb (cur.step - hi.step) hi.c.state hi.c.head (takePad (hi.pos - minp') hi.c.ls) hi.c.rs
          else false else false) = true
      · split at hleft
        · split at hleft
          · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head true
              (takePad (hi.pos - minp') hi.c.ls) (ListBlank.mk hi.c.rs)
              hp_pos hp_le
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')), by
                simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)), by
                  simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright, Bool.false_eq_true, ↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h

-- ============================================================
-- FAR (Finite Automata Reduction) certificate verifier
-- ============================================================

inductive CanStop (tb : Table) : Position → Prop
  | missing {c} : tb.get c.state c.head = none → CanStop tb c
  | move {c m} : tb.get c.state c.head = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Table} {c : Position} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip, h]
    · rwa [← flip_move]

theorem cannot_stop_run {M : Machine4} {tb : Table}
    (hm : Matches M tb) (c : Position) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get c.state c.head with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move hm c m h, Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  fin_cases a
  · cases xs with
    | nil => exact D.blank.symm
    | cons x xs => rfl
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := val / 2 % 16
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 32 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 32 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, by simp [edge_none], .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      have hn := allNodes ht q
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    exact Reads.push (show cert.edge (some (c.state, cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd, Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, symHead_eq_headI, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push, symHead_eq_headI] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq, if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state, cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he', if_true] at h''
      have h''' := allNodes h'' t
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      simp [hf'] at h'''
      exact Reads.push h''' ht

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, startPos, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

-- ============================================================
-- Symmetry: swapping states 2 and 3
-- ============================================================

def swap23 : Equiv.Perm State := Equiv.swap (2 : State) (3 : State)

theorem swap23_0 : swap23 0 = 0 := by decide
theorem swap23_1 : swap23 1 = 1 := by decide
theorem swap23_2 : swap23 2 = 3 := by decide
theorem swap23_3 : swap23 3 = 2 := by decide
theorem swap23_inv (q : State) : swap23.symm q = swap23 q := by fin_cases q <;> decide

def reindex23 (M : Machine4) : Machine4 :=
  fun q a => (M (swap23 q) a).map fun (s, b) => (s.map swap23, b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23, c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step, mapCfg23, Option.map_some, reindex23]
    have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
    rw [hinv]
    cases M q t.head with
    | none => rfl
    | some entry => rfl

theorem reindex23_multi (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    (reindex23 M).multiStep (mapCfg23 c) k = (M.multiStep c k).map mapCfg23 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23, Machine.init, swap23_0]

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨swap23 q0, t0, ?_⟩
    rw [← mapCfg23_init, reindex23_multi, hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q', z, h⟩
    · left; simp [reindex23, h]
    · right; exact ⟨swap23 q', z, by simp [reindex23, h]⟩
  · exact ⟨swap23 qm, am, by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23, this, hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
    have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23, cfgM, cfg, this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail, ht⟩ := hEnter
      rw [← mapCfg23_init, reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi, Option.map_some, Option.some.injEq] at ht
        refine ⟨tail, ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht
        rcases ht with ⟨hq', ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht']
    · intro tail
      obtain ⟨tail', ht'⟩ := hCycle tail
      rw [← hmap tail, reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp, Option.map_some, Option.some.injEq] at ht'
        refine ⟨tail', ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq', ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht'']
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m, tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get, h01.1, h01.2.1] at hget
    · fin_cases a <;> simp [Table.get, h01.2.2.1, h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23, hsq, hm q a m hget, Move.command, Option.map_some, hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist, h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle, hrun⟩ := hv h hh
  refine ⟨hle, ?_⟩
  rw [← mapCfg23_init, reindex23_multi, hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23, Position.view, hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q, a) := by
  ext ⟨q', a'⟩
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e, e]

def moves12 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q, a, d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed, moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed, moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | holesLeft + 1, used2, tb, rem, cur, prev, certs =>
    match stepLoop tb rem cur prev with
    | .rep => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some certs
      else
        checkMoves (fun m rest =>
          checkTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) certs

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : ((Nat.beq (cur.step + 1) 6 || Nat.beq (cur.step + 1) 12 || Nat.beq (cur.step + 1) 24 ||
          Nat.beq (cur.step + 1) 48 || Nat.beq (cur.step + 1) 107) && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01

theorem usesOnly01_set {tb : Table} (h01 : UsesOnly01 tb) {q : State} {a : Symbol} {m : Move}
    (hq : q = 0 ∨ q = 1) (hm : m.state = 0 ∨ m.state = 1) :
    UsesOnly01 (tb.set q a m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q', a') = (q, a)
    · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm hG hsum hv hu
    cases hsl : stepLoop tb rem cur prev with
    | rep => rw [hsl] at hstep; exact hstep
    | done =>
      simp only [hsl] at hCheck
      cases a with
      | nil => simp at hCheck
      | cons v rest =>
        simp only at hCheck
        split at hCheck
        · rename_i hcert
          have hns := certificate_sound hcert
          obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2
          exact cannot_stop_run hm startPos hns (k + 1) hk
        · simp at hCheck
    | missing q a rem' cur' prev' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z, M q a = some (some q', z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ, hcur'_run]
            simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
          obtain ⟨q0, t0, hrun107⟩ := hG.1
          rw [h107] at hrun107
          contradiction
        · exact hMsome
      obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
      split at hCheck
      · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
        rename_i h0
        have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
        have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard1 : (holes tb).card = 1 :=
          le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
        obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
        have hqm_mem : (qm, am) ∈ holes tb := by
          simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hget : tb.get qm am with
          | none => rfl
          | some m =>
            have := hm qm am m hget
            rw [hMmiss] at this
            simp [Move.command] at this
        have heq_key : (qm, am) = (q, a) := by
          have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
          have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
          rw [← hEq, Finset.mem_singleton] at hqm_mem
          exact hqm_mem
        rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
        rw [hMmiss] at hMqa
        contradiction
      · -- Branch on movesAllowed used2
        let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
        have hm_cmd : M q a = m.command := by
          cases d <;> simpa [m, Move.command] using hMqa
        have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
          rw [holes_set, Finset.card_erase_of_mem hmem_hole]
          omega
        by_cases hswap : used2 = false ∧ q' = 3
        · rcases hswap with ⟨hu2, rfl⟩
          have ⟨h01, hprev01⟩ := hu' hu2
          let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
          have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
          have hM2qa : (reindex23 M) q a = m2.command := by
            cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
          have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
            (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
            (histValid_reindex23 hv' hprev01) (by simp [m2])
        · have hmem_m : m ∈ movesAllowed used2 :=
            mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
          refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
          intro hnext_u2
          simp only [Bool.or_eq_false_iff] at hnext_u2
          have ⟨h01, hprev01⟩ := hu' hnext_u2.1
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hm01 : m.state = 0 ∨ m.state = 1 := by
            have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
            have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
            fin_cases q' <;> simp_all [m]
          exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4, GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
    False

theorem branch_one {tb : Table} {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    {q : State} {a : Symbol} {rem' : ℕ} {cur' : HistItem} {prev' : List HistItem}
    (hsl : stepLoop tb rem cur prev = .missing q a rem' cur' prev')
    (hChildren : ∀ m ∈ movesAllowed used2,
      TreeValid (tb.set q a m) (used2 || Nat.beq m.state.val 2) rem' cur' prev') :
    TreeValid tb used2 rem cur prev := by
  intro M hG hm hsum hv hu
  have hstep := stepLoop_sound hm hG hsum hv hu
  simp only [hsl] at hstep
  obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z, M q a = some (some q', z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ, hcur'_run]
        simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0, t0, hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m, Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2, rfl⟩
    have ⟨h01, hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01, hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580684011931872, 580684011931872, 580684011866336, 580684011931872, 158471546996960, 158471546996960, 
    1461864025806835825412678583131432658718136235426, 72637628284961, 580684011931872, 48526606668273970384418392398631364281246430626, 580684011931872, 48526606668273970384418392398631364281246430626, 
    580617440004320, 191040945127532847629300509356555999372904753959216939898340931399547246124086739196944426639436543684, 191040945127532847629300509356555999372904753959216939898340931399547246124086739196944426639436543684, 16641875742412316784231806828678235166152644401024368103843871060332942088075137478093709091165173444, 291962732323023105017040792183882716068349226897511959278923674891309007423795579466369408460912324, 158471546996960, 
    564085168276513, 567521314084001, 564085168276513, 565219040692321, 1464361709266407596774665301421331909814746903970, 286431641864672, 
    1461864025804172166982813300974795293326077097378, 567631740537312, 2078206948827074159375332889422874939590137389076423151170880409906798680308466164372084064303493988, 145274082689057, 145274082689057, 265783660764111914541556245094158712558996068906704784612334075791772037429517506785635263835129038532, 
    265783407324249547732709478571536249826391226881233229475747986536557712154044511808615161745599775588, 290829688375776, 290829688375776, 2124839861432418469047889324897625585685455500713237997818109983295315661194931613666459051307976388, 81924626647520, 72843721705569, 
    145274183353377, 75327556880864, 286431641864672, 1461864025804172197446119159257036339490260039074, 1461864025804172167022504753779530703569383110050, 567631740537312, 
    74836651540513, 1461864036693207908492535584607518141385965876642, 966163864949330575067660639101841903340483281678925007982733308351952403605275703249339514173968322356365245739748840004236785185550584347072057599281379955134014964848422, 145274183353377, 183045214854273533296870515141649719302077817763, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 
    265783534044183563548419933159424916287270605315382975296643102090471733918175766779926587316802070884, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 564085168047137, 81640091560289, 565425198925921, 
    565184680724577, 565184680724577, 72843990141025, 562985655369761, 564085168047137, 564085168047137, 
    1461864025806835825412678583131432658718136235426, 480481078833541558372121462767058613307873924962920186088194706406010124923268226939886532098741224425175891637053312431695069872734913197141436719131945492178930912715200195697501938512575117016823125087790228818151848229321345239175273267320316075823875138107022760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580683911268576, 565219911008289, 88031864553505, 580684012325088, 580684012325088, 158471681476832, 
    145277541943520, 71814270682145, 71814270682145, 282851783738401, 282851783738401, 282851783738401, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 286014896081120, 
    145277407725792, 149675722672352, 185544998536624000785095688723326351708275619234, 145277541943520, 730764756684370999216842858312302753416413708707, 145277541943520, 
    145277541943520, 145277541943520, 145277541943520, 145277541943520, 71814270682145, 71814270682145, 
    142251736435809, 282851783738401, 282851783738401, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 143078384470240, 143078384470240, 74908663548128, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 149675454236896, 149675454236896, 141908001687649, 
    286156764219872, 567631606712800, 145419141646816, 145419141646816, 145419141646816, 145419141646816, 
    564326525075489, 149817188157920, 154219798071776, 290554810730976, 154219798071776, 290554810730976, 
    154219798071776, 290554810730976, 149817188157920, 154219798071776, 567631606450656, 567631606450656, 
    1461685619845278754530431049358269582390216660258, 426898681760224, 426898681760224, 145423705049568, 286156764219872, 426898681760224, 
    286156898437600, 154219798071776, 154219798071776, 154219798071776, 154219798071776, 564326525075489, 
    564326525075489, 564326525075489, 564326558663713, 564326525075489, 286156764219872]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [732180859417103219741646552571096028979260872098, 290829688375776, 81922479163872, 290554810730976, 290554810730976, 290554676513248, 
    290554810730976, 290554810730976, 290554810730976, 154215503104480, 290314560735712, 290348652300768, 
    290555079166432, 290555079166432]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [564332967526433, 1461596415859588307719953399713296801748937610658, 564092482946081, 564126842684449, 564092482946081, 564126842684449, 
    564092482946081, 564332967526433, 480481077047106023417608928812220475712048137818800171737751120387406436719275197176533274904672894140098364687896727385014741869774464733091026800344425099455506766902882340132742928865222891890352906868447283992574381794009696294307269548711554727666518016249598761, 265750974941130293871093805119180229696112387423225465719412172432125437306600020704316720672220716421, 265750998701117567785135337399778734287374456057272334838877809611977130463277651675415980239042197253, 73121889781984, 
    265785688283061832415414176102327130081379350843061641403582205801031731801182001067991249762921268932, 265783692444095654529754258157132933653233741495699195484660648685283563346634496493094720695008020164, 265783660764111914541557124390336307247081315727011007187349948896249769008261544033900408960472106692, 265783660764111914541556245094158712558996068903636332651711142391133821283244734069739918465278985924, 265785688283061832415413296806149484211520353100894231679781945032085677093148826436962689672593065668, 73121889781984, 
    37939664980192, 73121889585376, 73121889585376, 564126842684449, 564401720788001, 282858024862753, 
    282858226189345, 81928921614816, 290829688375776, 81928921614816, 265751220461005753993844546341317621682939675694486723364493120751120303530710484590202875928299839941, 565226355820641, 
    362922862184928, 265783660764111914541556245094158712558996068906704784612334075791772037429517506785635263835129038532, 72640786598112, 74908663548128, 74908663548128, 74908663548128, 
    286014896081120, 730842809590322014007978904938306793188778576291, 290554810730976, 154219798071776, 75320912840928, 74839944071392, 
    74839944071392, 286152335034592, 145273514952928, 145273515149536, 145273246976224, 74839876962528, 
    215577432426720, 215577432426720, 215577432426720, 356315054999776, 74839876962528, 145273515411680, 
    145273515411680]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [576290260388320, 576290260388320, 730753606960454507600780929026791259587553564066, 265783407324249547732709478517868270233747802871595241414039453732061746482578784331726944183223731044, 265801654994861121644809591719385693117368448515566517904420884528327316475311152927895313741653362276, 576290260388320, 
    154353076144608, 286157032393184, 265783407324249547732710350944544528245248527191015350476459753188153791862184825727933514881230324580, 265783407324249547732709478517868270233747802871595241414039454375543096160799972335511354263470228324, 154078197975520, 154078197975520, 
    1461864025123623010071203430819158246129893160354, 290829688375776, 567494167366112, 567494167366112, 567494167366112, 732180859417113604374977703483485258768691271074, 
    290829688375776, 145694019291616, 145694019291616, 91522971547888857395043688949275964138152564002, 290829688375776, 290829688375776, 
    290829688375776, 567494167300576, 567494167366112, 1461685634813684030859603079684764069293292295458, 567494167366112, 732178425706991521291988479732015723888100545954, 
    732180864850997610578894585201201794802640262562, 132932253051187826038216600160633821912733318628792445810531936654202295780415130060727081661416539940, 132928197518239160296252839338300567627568738030203427658482599210172780792077480314606629879088825668, 732180864850997610578894585201203483658942977442, 132936307594016172501722152760385591613218619609478603005418557076013995662884815527341765537793459524, 132875514200551213644534064180571755713789664955394532205846980777143850355863748065873559265606137893, 
    145694019291616, 732180854653160467481684471974821248125706474914, 265783407324244827047202888824329598517106474595004228889892674607339666133582215839654971309214148964, 265783660764111914541557124329959829405642254442371872873000396231510036260982346041722933822489898180, 265783660764111914541556245033782234717557007618997198337361589726394088535965536077562443327296777412, 265783660764111914541556245033782234717557007618997198337022897158691404697003462356296596336924699844, 
    145694019291616, 732180854653160467481549072283024409658139383202, 732180855333725201323445342096674434883309311394, 145694019291616, 732180855333725201323445342096674434883309311394, 91522607445766636584894994473903720401723757986, 
    290829688375776, 73126184749536, 265783407324249547732709478517868270233747802871595241371364190209093951593101274134627687044344857444, 24307904844490680048574324743678009382734960034, 37941812464096, 73126184552928, 
    73126184552928, 265783407324249547732709478517868270233747802868776811461856685138289891984819223577938243243707876196, 81922479163872, 571892214270432, 290554810730976, 149679749204448, 
    290554810730976, 290554810730976, 149817188157920, 290554810730976, 16658095707978888284936390092739011560132949983119440263989784339057180843171274592131891862505146052, 16658095707978888284936390092739011560132949983119440263989784339057190394188305009906401566779393732, 
    435484388493792, 154009143347680, 290829688637920, 1461864025804187743912926824097645053462578771362, 567494167497184, 732178425717625385822932270923380545371777832354, 
    435553040861664, 91522966103370986660028273535286467363101775138, 145281971128800, 290554810730976, 732180864861631475109838376392570556951023883682, 568490633333216, 
    154352942057952, 290554810730976, 567494167759328, 290554810730976, 154215503104480, 290554810730976, 
    290554676513248, 290554676513248, 149817188157920, 290554810730976, 1676866272193029428224668747729329813283935139089169660721959467708462956904925217182976993634276637624988923245421837832753016488666279681327020981945238313850569392335469385868558290514247917128265678796435960394703167552783795695057493068667094534243801093991211133478246567138606766983193216521756177038720270235733818648207672939993184210947413055947362204031115085924882731, 290554810730976, 
    290554810730976, 290554810730976, 290554810730976, 145281836911072, 72610988165217, 283717220698209, 
    265783660764111914541556245033782234717557007622065650297984523127032304682238308793457788697146830020, 145281836911072, 294815552506336, 145281836911072, 294815552506336, 145281836911072, 
    145281836911072, 290554810730976, 145281836911072, 154352942057952, 74912958515680, 145281702693344, 
    145281702693344, 154215503104480, 431430006082016, 281758583491040, 281758986144224, 281758986144224, 
    290314560735712, 183045214849122755164619662596591743744591799203, 290348652300768, 154352942057952, 154352942057952, 145419141646816, 
    145419141646816, 290554810730976, 290554810730976, 290554810730976, 435828052593120, 45398345648608, 
    290554676513248, 81716320930272, 290555079166432, 145419543841248, 435827583224288, 508464070134240, 
    145419544300000, 72851508431328, 149679749204448, 145282105084384, 290417237559776, 74912958515680, 
    145281971128800, 145281702693344, 145281702693344, 154353076144608, 154215234669024, 145281971128800]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [182699551982448538483871585870120436487502181794, 177061641717984, 141979275102432, 564092482946081, 564092449357857, 265783407324249547732710350998212508637607160194970589769867792677302300990370559273977811455718369636, 
    265783407324249547732710350998212508637607160194970589769867792677302300990370559273977811455718369636, 564161202390049, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 564092449357857, 
    1978658779495010857921506726200232164528366838699012772719397962302619655919008423645291325574162769445726095809830140478843302902742075953910171079142816872601772234632061734, 1978658779495010857921506726200232164528366838699012772719397962302619655919008423775152369066431120893736001765391488026156327108997908966715037020333792788594842191700943654, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 39724693719264, 39724693719264, 
    282858091979041, 71545633899553, 71545633899553, 71545633899553, 71820713133089, 71820713133089, 
    45688651768710295826204242405163238663634551203, 71545633899553, 71545633899553, 71683148358945, 71820713133089, 71820713133089, 
    365387953549772900424076687473194784146648465827, 294819981298144, 730764756684390470404493508777943231771598389667, 3880105118047768846394620327283782093906973322392707030678619764866093703414944052293556817807879468197293099426186646868134473607109491904001994574569304319993241500902182, 286157032393184, 1461529513368780940654873184803806379990997015970, 
    265750982861126169859575712062919439118885473262705519378809920469697500622777743723809452544267944612, 72029021997536, 177061641717984, 141979275102432, 423600280701408, 265750982861126169859575712060836187381901825641925603183642976093626336587611897850977116665022284452, 
    36426158835936, 141979275102432, 141908408076512, 72020230473952, 564126809128993, 564332967755809, 
    564332967755809, 282857991307297, 282857991307297, 2108651412944397531248975787398815768503372911912022126785821771912679366014506495951811615950161604, 288883718757581814639357502268263608443556619061697295821962734157977466187276923088106278310172477124, 365400497777422781968571539224039523926692894498, 
    265751093741551359815597357742025736477031684847739505043953262227883620024068628245151179779112469156, 1461596415859588307715001639556155280649341115810, 564126842684449, 564126842684449, 564333001114657, 564126809096225, 
    564332967526433, 265751093741560801186412709230651528542611869959522053443466751091364939718712477893831119560315273892, 265750998701117921836539515394583362414103864088443582216233754924302842966324483738004218339540350213, 265751093741560801186412709230638937826269143936509197155749002189158621896686769844285999157084979876, 265750998701117685802269164924509481987166814854404721376687276611779660223477377309629506086103545893, 265751093741557024638086212107827582504101473898755778006348080600805244750335079359970926132231701156, 
    564126976976161, 265750998701117685802269164924509481987166814854404721376687276611779650597255631826510417815240570917, 91433229900140350837969651909778910487111015842, 73119742298336, 4152489478245602117955526758703453987170327755107281322127504604204307814394009096889994354017206948, 4152485765747535248354634534461186861078629238806133865958687819838338866034090278208847334775489188, 
    73119742298336, 37935370012896, 73119742101728, 73119742101728, 71545633899553, 45699802183844857002892318197230395972613308835, 
    71545633899553, 282858024862753, 564126809128993, 564332967755809, 564332967755809, 282857991307297, 
    282857991307297, 265751980780607960614139557135854550829071753816617439658305889261277971747595721958358078651001242276, 265751980780609848888302800541157235821504972276301404728686813571001389699192895080688048138804298404, 71545633899553, 282858226189345, 142120603623713, 
    81924626647520, 81924626647520, 1046199806655456814187289393594413257587936909703652206502778551305981597252821962769338994877301412, 81924626647520, 81924626647520, 989329153831664413307367360831762574958688210718350727286345516776997829561037152940185599306628707724280030804318251811574814218121628005406517354647144357090647193510881062, 
    290829688375776, 290829688375776, 143078384470240, 72709640292576, 143078384470240, 143078384470240, 
    143078384470240, 213380556654816, 143078384470240, 564332967526433, 566531992915041, 143078384470240, 
    72709640292576, 143078384470240, 283824462760416, 143078384470240, 283957740964320, 565432514250849, 
    143224681794016, 283957740964320, 213380556654816, 143078384470240, 424699390069216, 213380556654816, 
    143078384470240, 424699390069216, 72709640292576, 143078384470240, 1462216657701427443207918435248570820287176655267, 143078384470240, 
    143078384470240, 143078384470240, 143078384470240, 565501300779361, 2056190593532831424095101229665769924006714840994099866984816984117853030709734507365486021127700995869072132569587419514032725628522790310616124465537295995408585916068904742, 565226355361889, 
    565226355361889, 565432715118689, 61847696334955086639193660342125235548647797212825073714617519020510908910759352988928277499025276705475720542289689917751744724064655541740266170897703757862161917835695910, 213380556654816, 213380556654816, 213380556654816, 
    217783032351200, 37701493983329, 72640920815840, 72640920815840, 217778670274784, 296952365844960, 
    730845771408054078489696041063275168424015169955, 5798215870075658211420407184615404719312994723, 1978658307751508209731300482704683227442739315060202944742355810210052925488133860707147554529465363902491473403150856877441974211778165720607072601573412913097483662964512550, 74908663548128, 74908663548128, 145277407725792, 
    145277407725792, 74908663548128, 145277407725792, 145277407725792, 145277407725792, 286023486015968, 
    294819847473632, 730842809590332398641310055850696022978208991651, 86052291742176, 290554810730976, 86052291742176, 86052291742176, 
    154219798071776, 154219798071776, 154219798071776, 154219798071776, 290554810730976, 39724693719264, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277810378976, 145277810378976, 1461864025802879279964657466935371208675916518818, 145277810116832, 145277810116832, 1461864025802214663426512048385318981052773440930, 
    145277541943520, 39724693719264, 145277809985760, 286514784692988995531271664605112892427522164224121171407313906901527830849294242339521686549914240324, 74908663548128, 145277407725792, 
    145277407725792, 74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277810378976, 
    36567487357217, 145419544300000, 426898815846880, 145419544037856, 145419544037856, 426898681760224, 
    149675454236896, 149675454236896, 149675454236896, 149675454236896, 92771453940858257491769166654789332028654884258, 79716811868384, 
    44542070163936, 149675454236896, 149675722672352, 184758223112416, 219977626421472]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_0
  · exact tv_b8_1
  · exact tv_b8_2
  · exact tv_b8_3
  · exact tv_b8_4
  · exact tv_b8_5
  · exact tv_b8_6
  · exact tv_b8_7
  · exact tv_b8_8
  · exact tv_b8_9
  · exact tv_b8_10
  · exact tv_b8_11
  · exact tv_b8_12
  · exact tv_b8_13
  · exact tv_b8_14
  · exact tv_b8_15

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_branch (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (q' : State) (hq' : q' ≠ 3)
    (hM10 : M 1 0 = some (some q', Stmt.write 0 Dir.right)) : False := by
  let m : Move := ⟨q', 0, false⟩
  have hm_cmd : M 1 0 = m.command := hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
  fin_cases q'
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
    exact tv_b0 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    exact tv_b4 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · exact tv_b8 M hG hm1 rfl hv (by simp)
  · exact absurd rfl hq'

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H1 := by
  intro M hFirst second hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 0, false⟩ rfl
  have hv : HistValid M [h1, h0] := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact ⟨by decide, hrun1⟩
    · exact ⟨by decide, rfl⟩
  obtain ⟨q', hM10⟩ := second
  by_cases h3 : q' = 3
  · subst h3
    have h01_base : UsesOnly01 baseTable := by
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro q a m' hget
      fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
      subst hget; exact Or.inr rfl
    have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
      intro h hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
    have hM10' : (reindex23 M) 1 0 = some (some 2, Stmt.write 0 Dir.right) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    exact solve_branch (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01)
      2 (by decide) hM10'
  · exact solve_branch M hG hm0 hv q' h3 hM10

end OMA.BB4H1

-- Adaptation by @ubuwaits.
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H1 := OMA.BB4H1.h1_proof
