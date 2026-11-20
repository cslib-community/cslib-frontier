/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# The DPLL solver on the word RAM: what the scan computes

The scan of the word-RAM DPLL solver (`Cslib.Algorithms.WordRAM.DPLL.scan`) makes one pass over the
clauses. This file states what it computes as a fold over the clauses and their literal
occurrences (`Cslib.Algorithms.WordRAM.DPLL.formulaScan`), and proves that the fold gives the
status of the trail (`Cslib.Algorithms.Lean.DPLL.status`): a falsified clause, satisfaction, the
literal of the first unit clause, and the first open variable in the order of `φ.vars.dedup`.

The last part needs the order of `List.dedup`, which keeps the *last* occurrence of each element
(`Cslib.Algorithms.WordRAM.DPLL.find?_dedup`): the first open variable of `φ.vars.dedup` is the
variable of the first literal occurrence that is open and is the last occurrence of its
variable. The program records the address of the last occurrence of each variable before the
search (`Cslib.Algorithms.WordRAM.DPLL.lastPos`).
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Algorithms.WordRAM.ClauseCode
open Cslib.Algorithms.Lean.DPLL

/-! ### The first open variable in the order of `List.dedup` -/

/-- The first element satisfying `q` that does not occur later in the list. -/
def firstLast (q : ℕ → Bool) : List ℕ → Option ℕ
  | [] => none
  | x :: xs => if q x && !xs.contains x then some x else firstLast q xs

/-- **`List.dedup` keeps last occurrences**: its first element satisfying `q` is the first
element satisfying `q` that does not occur later. -/
theorem find?_dedup (q : ℕ → Bool) : (xs : List ℕ) → xs.dedup.find? q = firstLast q xs
  | [] => rfl
  | x :: xs => by
    by_cases hx : x ∈ xs
    · rw [List.dedup_cons_of_mem hx, find?_dedup q xs, firstLast]
      simp [hx]
    · rw [List.dedup_cons_of_notMem hx, List.find?_cons, find?_dedup q xs, firstLast]
      cases q x <;> simp [hx]

/-! ### Literal occurrences -/

/-- The variable of a literal occurrence. -/
def occVar : ℕ × Literal ℕ → ℕ
  | (_, l) => l.1

@[simp] theorem occVar_mk (p : ℕ) (l : Literal ℕ) : occVar (p, l) = l.1 := rfl

/-- The occurrences of the literals of `c`, with their addresses from `p`. -/
def litOccs : ℕ → Clause ℕ → List (ℕ × Literal ℕ)
  | _, [] => []
  | p, l :: ls => (p, l) :: litOccs (p + 1) ls

/-- The literal occurrences of the clauses stored from address `a`, with their addresses. -/
def occs : CNF ℕ → ℕ → List (ℕ × Literal ℕ)
  | [], _ => []
  | c :: φ, a => litOccs (a + 1) c ++ occs φ (a + c.length + 1)

theorem map_litOccs (p : ℕ) (c : Clause ℕ) : (litOccs p c).map Prod.snd = c := by
  induction c generalizing p with
  | nil => rfl
  | cons l ls ih => simp [litOccs, ih]

theorem map_occs (φ : CNF ℕ) (a : ℕ) : (occs φ a).map occVar = φ.vars := by
  induction φ generalizing a with
  | nil => rfl
  | cons c φ ih =>
    have : (litOccs (a + 1) c).map occVar = c.map Prod.fst := by
      conv_rhs => rw [← map_litOccs (a + 1) c]
      rw [List.map_map]; rfl
    simp only [occs, List.map_append, this, ih]
    simp [CNF.vars]

theorem bounds_litOccs (p : ℕ) (c : Clause ℕ) :
    ∀ e ∈ litOccs p c, p ≤ e.1 ∧ e.1 < p + c.length := by
  induction c generalizing p with
  | nil => simp [litOccs]
  | cons l ls ih =>
    intro e he
    simp only [litOccs, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · have := ih (p + 1) e he; simp only [List.length_cons]; omega

theorem pairwise_litOccs (p : ℕ) (c : Clause ℕ) :
    (litOccs p c).Pairwise fun e e' => e.1 < e'.1 := by
  induction c generalizing p with
  | nil => simp [litOccs]
  | cons l ls ih =>
    simp only [litOccs, List.pairwise_cons]
    exact ⟨fun e he => by have := (bounds_litOccs (p + 1) ls e he).1; omega, ih (p + 1)⟩

/-- The total length of the encodings of the clauses. -/
theorem bounds_occs (φ : CNF ℕ) (a : ℕ) :
    ∀ e ∈ occs φ a, a < e.1 ∧ e.1 < a + 1 + (φ.flatMap encodeClause).length := by
  induction φ generalizing a with
  | nil => simp [occs]
  | cons c φ ih =>
    intro e he
    simp only [occs, List.mem_append] at he
    simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]
    rcases he with he | he
    · have := bounds_litOccs (a + 1) c e he; omega
    · have := ih (a + c.length + 1) e he; omega

theorem pairwise_occs (φ : CNF ℕ) (a : ℕ) : (occs φ a).Pairwise fun e e' => e.1 < e'.1 := by
  induction φ generalizing a with
  | nil => simp [occs]
  | cons c φ ih =>
    simp only [occs, List.pairwise_append]
    refine ⟨pairwise_litOccs _ _, ih _, fun e he e' he' => ?_⟩
    have := (bounds_litOccs _ _ e he).2
    have := (bounds_occs φ _ e' he').1
    omega

/-- The address of the last occurrence of the variable `x`, or `m` if there is none. -/
def lastFrom (m : ℕ) (os : List (ℕ × Literal ℕ)) (x : ℕ) : ℕ :=
  os.foldl (fun m e => if occVar e = x then e.1 else m) m

/-- The address of the last occurrence of the variable `x`, or `0`. -/
abbrev lastPos (os : List (ℕ × Literal ℕ)) (x : ℕ) : ℕ := lastFrom 0 os x

theorem lastFrom_of_not_mem {m : ℕ} {os : List (ℕ × Literal ℕ)} {x : ℕ}
    (h : x ∉ os.map occVar) : lastFrom m os x = m := by
  induction os generalizing m with
  | nil => rfl
  | cons e os ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : ¬ occVar e = x := fun h' => h.1 h'.symm
    simp only [lastFrom, List.foldl_cons, hne, ↓reduceIte]
    exact ih h.2

theorem lastFrom_mem {m : ℕ} {os : List (ℕ × Literal ℕ)} {x : ℕ}
    (h : x ∈ os.map occVar) : ∃ e ∈ os, lastFrom m os x = e.1 := by
  induction os generalizing m with
  | nil => simp at h
  | cons e os ih =>
    simp only [lastFrom, List.foldl_cons]
    by_cases hx : x ∈ os.map occVar
    · obtain ⟨e', he', h'⟩ := ih (m := if occVar e = x then e.1 else m) hx
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · have hex : occVar e = x := by simp_all
      refine ⟨e, List.mem_cons_self, ?_⟩
      rw [ite_eq_left_iff.2 (fun h => absurd hex h)]
      exact lastFrom_of_not_mem hx

theorem lastFrom_append (m : ℕ) (os os' : List (ℕ × Literal ℕ)) (x : ℕ) :
    lastFrom m (os ++ os') x = lastFrom (lastFrom m os x) os' x := by
  simp [lastFrom, List.foldl_append]

/-! ### The fold of the scan -/

/-- The registers of the current clause: the number of its literals not falsified so far, the
code of the last of them, and whether one of them is true. -/
structure ClauseRegs where
  /-- The number of literals not falsified so far. -/
  cnt : ℕ
  /-- The code of the last such literal. -/
  uc : ℕ
  /-- Whether a true literal was found. -/
  sat : Bool
  deriving DecidableEq, Repr

/-- One literal of a clause against the partial assignment `π`. -/
def clauseLit (π : List (Literal ℕ)) (r : ClauseRegs) (l : Literal ℕ) : ClauseRegs :=
  if π.contains l.negate then r else ⟨r.cnt + 1, litCode l, r.sat || π.contains l⟩

/-- One literal occurrence at address `p` in the search for the first open variable: an open
variable whose last occurrence (`lastOf`) is at `p`, if none was found before. -/
def openLit (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (o : Option ℕ) (p : ℕ) (l : Literal ℕ) :
    Option ℕ :=
  match o with
  | some x => some x
  | none => if !π.contains l && !π.contains l.negate && lastOf l.1 == p then some l.1 else none

/-- The literal loop: the literals `ls` from address `p`. -/
def litsScan (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) :
    ClauseRegs × Option ℕ → ℕ → Clause ℕ → ClauseRegs × Option ℕ
  | s, _, [] => s
  | s, p, l :: ls => litsScan π lastOf (clauseLit π s.1 l, openLit π lastOf s.2 p l) (p + 1) ls

/-- Whether some literal of `π` has the code `u`. -/
def codeOn (π : List (Literal ℕ)) (u : ℕ) : Bool := π.any fun l => litCode l == u

/-- The registers of the scan: a falsified clause, whether every clause has a true literal, the
code of the literal of the first unit clause, and the first open variable. -/
structure ScanRegs where
  /-- A falsified clause was found. -/
  conf : Bool
  /-- Every clause so far has a true literal. -/
  alls : Bool
  /-- The code of the literal of the first unit clause not on the trail. -/
  unit : Option ℕ
  /-- The first open variable. -/
  opened : Option ℕ
  deriving DecidableEq, Repr

/-- The registers at the start of the scan. -/
def ScanRegs.init : ScanRegs := ⟨false, true, none, none⟩

/-- One clause, stored at address `a`. -/
def clauseScan (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (s : ScanRegs) (a : ℕ) (c : Clause ℕ) :
    ScanRegs :=
  let r := litsScan π lastOf (⟨0, 0, false⟩, s.opened) (a + 1) c
  ⟨s.conf || r.1.cnt == 0, s.alls && r.1.sat,
    match s.unit with
    | some u => some u
    | none => if r.1.cnt == 1 && !codeOn π r.1.uc then some r.1.uc else none,
    r.2⟩

/-- **The scan** of the clauses stored from address `a`. -/
def formulaScan (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) : ScanRegs → ℕ → CNF ℕ → ScanRegs
  | s, _, [] => s
  | s, a, c :: φ => formulaScan π lastOf (clauseScan π lastOf s a c) (a + c.length + 1) φ

/-! ### The fold computes the status -/

theorem fst_litsScan (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (s : ClauseRegs × Option ℕ) (p : ℕ)
    (ls : Clause ℕ) : (litsScan π lastOf s p ls).1 = ls.foldl (clauseLit π) s.1 := by
  induction ls generalizing s p with
  | nil => rfl
  | cons l ls ih => simp [litsScan, ih]

/-- The literals of a clause not falsified by `π`. -/
abbrev notFalse (π : List (Literal ℕ)) (c : Clause ℕ) : Clause ℕ :=
  c.filter fun l => !π.contains l.negate

theorem foldl_clauseLit (π : List (Literal ℕ)) (ls : Clause ℕ) (r : ClauseRegs) :
    (ls.foldl (clauseLit π) r).cnt = r.cnt + (notFalse π ls).length ∧
      (ls.foldl (clauseLit π) r).sat = (r.sat || ls.any (Holds π)) ∧
      (ls.foldl (clauseLit π) r).uc = ((notFalse π ls).getLast?.map litCode).getD r.uc := by
  induction ls generalizing r with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih (clauseLit π r l)
    rw [List.foldl_cons, h₁, h₂, h₃]
    have hnf : notFalse π (l :: ls) =
        if π.contains l.negate then notFalse π ls else l :: notFalse π ls := by
      simp only [notFalse, List.filter_cons]; cases π.contains l.negate <;> rfl
    rw [hnf]
    unfold clauseLit
    cases hn : π.contains l.negate
    · have hn' : l.negate ∉ π := by simpa using hn
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.any_cons]
      refine ⟨by omega, by simp [Holds, hn', Bool.or_assoc], ?_⟩
      cases notFalse π ls with
      | nil => simp
      | cons a f =>
        cases h : (a :: f).getLast? with
        | none => simp at h
        | some y => simp [h]
    · have hn' : l.negate ∈ π := by simpa using hn
      simp [Holds, hn']

theorem notFalse_eq_nil_iff (π : List (Literal ℕ)) (c : Clause ℕ) :
    notFalse π c = [] ↔ Falsifies π c = true := by
  simp [notFalse, List.filter_eq_nil_iff, Falsifies]

/-- The code of the literal of a unit clause. -/
def unitCode (π : List (Literal ℕ)) (c : Clause ℕ) : Option ℕ :=
  match Clause.unit? (notFalse π c) with
  | some l => if π.contains l then none else some (litCode l)
  | none => none

theorem codeOn_litCode (π : List (Literal ℕ)) (l : Literal ℕ) :
    codeOn π (litCode l) = π.contains l := by
  unfold codeOn
  rw [Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨l', hl', h⟩
    obtain rfl := litCodeBy_injective Function.injective_id (by simpa using h)
    exact hl'
  · exact fun h => ⟨l, h, by simp⟩

theorem unitCode_eq (π : List (Literal ℕ)) (c : Clause ℕ) :
    (let r := c.foldl (clauseLit π) ⟨0, 0, false⟩
      if r.cnt == 1 && !codeOn π r.uc then some r.uc else none) = unitCode π c := by
  obtain ⟨h₁, -, h₃⟩ := foldl_clauseLit π c ⟨0, 0, false⟩
  simp only at h₁ h₃
  simp only [h₁, h₃, unitCode, Nat.zero_add]
  rcases hf : notFalse π c with _ | ⟨l, _ | ⟨l', f⟩⟩
  · simp
  · simp [Clause.unit?, codeOn_litCode]
  · simp [Clause.unit?]

theorem map_findSome? {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.findSome? f).map g = l.findSome? fun x => (f x).map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.findSome?_cons]; cases f a <;> simp [ih]

theorem unitLiteral?_map (φ : CNF ℕ) (π : List (Literal ℕ)) :
    (unitLiteral? φ π).map litCode = φ.findSome? (unitCode π) := by
  rw [unitLiteral?, map_findSome?]
  congr 1
  funext c
  cases h : Clause.unit? (notFalse π c) with
  | none => simp [unitCode, h]
  | some l => by_cases hl : l ∈ π <;> simp [unitCode, h, hl]

/-- The open-variable part of the scan is a fold over the literal occurrences. -/
def openFold (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (o : Option ℕ)
    (os : List (ℕ × Literal ℕ)) : Option ℕ :=
  os.foldl (fun o e => openLit π lastOf o e.1 e.2) o

theorem snd_litsScan (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (s : ClauseRegs × Option ℕ)
    (p : ℕ) (ls : Clause ℕ) :
    (litsScan π lastOf s p ls).2 = openFold π lastOf s.2 (litOccs p ls) := by
  induction ls generalizing s p with
  | nil => rfl
  | cons l ls ih => simp [litsScan, ih, openFold, litOccs]

/-- **What the scan computes.** -/
theorem formulaScan_eq (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (φ : CNF ℕ) (s : ScanRegs)
    (a : ℕ) :
    formulaScan π lastOf s a φ =
      ⟨s.conf || φ.any (Falsifies π), s.alls && φ.all (fun c => c.any (Holds π)),
        s.unit.or (φ.findSome? (unitCode π)), openFold π lastOf s.opened (occs φ a)⟩ := by
  induction φ generalizing s a with
  | nil => cases s; simp [formulaScan, occs, openFold]
  | cons c φ ih =>
    rw [formulaScan, ih]
    obtain ⟨h₁, h₂, -⟩ := foldl_clauseLit π c ⟨0, 0, false⟩
    have hu := unitCode_eq π c
    simp only at h₁ h₂ hu
    simp only [clauseScan, fst_litsScan, snd_litsScan]
    rw [hu]
    simp only [h₁, h₂, Nat.zero_add, Bool.false_or, List.any_cons, List.all_cons,
      List.findSome?_cons, occs, openFold, List.foldl_append]
    refine ScanRegs.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨?_, ?_, ?_, rfl⟩
    · have hF : Falsifies π c = ((notFalse π c).length == 0) := by
        rw [Bool.eq_iff_iff, ← notFalse_eq_nil_iff]; simp
      rw [hF, Bool.or_assoc]
    · simp [Bool.and_assoc]
    · cases s.unit <;> cases unitCode π c <;> rfl

/-- Assignment of a variable through the two literals on it. -/
theorem not_assigned_iff (π : List (Literal ℕ)) (l : Literal ℕ) :
    (!π.contains l && !π.contains l.negate) = !Assigned π l.1 := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [Assigned, Std.Sat.Literal.negate, Bool.and_comm]

theorem openFold_some (π : List (Literal ℕ)) (lastOf : ℕ → ℕ) (x : ℕ)
    (os : List (ℕ × Literal ℕ)) : openFold π lastOf (some x) os = some x := by
  induction os with
  | nil => rfl
  | cons e os ih => exact ih

/-- **The open-variable search finds the first open variable of `φ.vars.dedup`**, with the
addresses of the last occurrences. -/
theorem openFold_occs (π : List (Literal ℕ)) (pre os : List (ℕ × Literal ℕ))
    (hpw : (pre ++ os).Pairwise fun e e' => e.1 < e'.1) :
    openFold π (lastPos (pre ++ os)) none os =
      firstLast (fun x => !Assigned π x) (os.map occVar) := by
  induction os generalizing pre with
  | nil => rfl
  | cons e os ih =>
    obtain ⟨p, l⟩ := e
    have hlast : (lastPos (pre ++ (p, l) :: os) l.1 == p) =
        !(os.map occVar).contains l.1 := by
      change (lastFrom 0 (pre ++ (p, l) :: os) l.1 == p) = _
      rw [lastFrom_append]
      simp only [lastFrom, List.foldl_cons, occVar_mk, ↓reduceIte]
      change (lastFrom p os l.1 == p) = _
      by_cases hm : l.1 ∈ os.map occVar
      · obtain ⟨e', he', h'⟩ := lastFrom_mem (m := p) hm
        have hlt : p < e'.1 := by
          have := List.pairwise_append.1 hpw
          exact (List.pairwise_cons.1 this.2.1).1 e' he'
        simp [h', hm, Nat.ne_of_gt hlt]
      · simp [lastFrom_of_not_mem hm, hm]
    simp only [openFold, List.foldl_cons, openLit, List.map_cons, firstLast, occVar_mk]
    rw [not_assigned_iff, hlast]
    split
    · exact openFold_some π _ l.1 os
    · rw [show pre ++ (p, l) :: os = (pre ++ [(p, l)]) ++ os by simp]
      exact ih (pre ++ [(p, l)]) (by simpa using hpw)

/-- **The scan computes the status of the trail**, given the addresses of the last occurrences of
the variables of the clauses stored from address `a`: whether a clause is falsified, whether every
clause has a true literal, the code of the literal of the first unit clause, and the first open
variable of `φ.vars.dedup`. -/
theorem formulaScan_init (π : List (Literal ℕ)) (φ : CNF ℕ) (a : ℕ) :
    formulaScan π (lastPos (occs φ a)) .init a φ =
      ⟨φ.any (Falsifies π), φ.all (fun c => c.any (Holds π)), (unitLiteral? φ π).map litCode,
        φ.vars.dedup.find? fun x => !Assigned π x⟩ := by
  rw [formulaScan_eq, unitLiteral?_map, find?_dedup, ← map_occs φ a]
  have := openFold_occs π [] (occs φ a) (by simpa using pairwise_occs φ a)
  simp only [List.nil_append] at this
  simp [ScanRegs.init, this]

/-! ### The literal loop -/

/-- The literal array at `T` holds the partial assignment `π` on the variables below `N`: the cell
`T + 2 v + b` is `1` when `(v, b)` is in `π` and `0` otherwise. -/
def LitArr (mem : ℕ → ℕ) (T N : ℕ) (π : List (Literal ℕ)) : Prop :=
  ∀ l : Literal ℕ, l.1 < N → mem (T + litCode l) = (π.contains l).toNat

theorem litCode_lt {l : Literal ℕ} {N : ℕ} (h : l.1 < N) : litCode l < 2 * N := by
  obtain ⟨v, b⟩ := l
  simp only at h
  cases b <;> simp [litCodeBy] <;> omega

open Cslib.WordRAM Cslib.WordRAM.Block Reg

section Specs

variable {w : ℕ}

/-- One literal of the scan performs `clauseLit` and `openLit`. -/
theorem litBody_spec (π : List (Literal ℕ)) (l : Literal ℕ) (r : ClauseRegs) (o : Option ℕ)
    (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hlit : x.mem (x.regs lptr) = litCode l) (hlN : l.1 < N)
    (hπ : LitArr x.mem (x.regs tb) N π)
    (hcnt : x.regs cnt = r.cnt) (huc : x.regs uc = r.uc) (hsat : x.regs sat = r.sat.toNat)
    (hopf : x.regs opf = o.isSome.toNat) (hov : x.regs ov = o.getD 0)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitB : Fits w (x.regs lb + N))
    (hfitp : Fits w (x.regs lptr + 1)) (hfitc : Fits w (r.cnt + 1)) :
    ∃ y, ExecWithin w litBody x y 30 ∧ y.mem = x.mem ∧
      y.regs cnt = (clauseLit π r l).cnt ∧ y.regs uc = (clauseLit π r l).uc ∧
      y.regs sat = (clauseLit π r l).sat.toNat ∧
      y.regs opf = (openLit π (fun v => x.mem (x.regs lb + v)) o (x.regs lptr) l).isSome.toNat ∧
      y.regs ov = (openLit π (fun v => x.mem (x.regs lb + v)) o (x.regs lptr) l).getD 0 ∧
      y.regs lptr = x.regs lptr + 1 := by
  have hc := litCode_lt hlN
  have hnc := litCode_lt (l := l.negate) hlN
  have : Fits w (litCode l) := hfit.of_le (by omega)
  have : Fits w (x.regs tb + litCode l) := hfit.of_le (by omega)
  have : Fits w (litCode l.negate) := hfit.of_le (by omega)
  have : Fits w (x.regs tb + litCode l.negate) := hfit.of_le (by omega)
  have : Fits w l.1 := hfitB.of_le (by omega)
  have : Fits w (x.regs lb + l.1) := hfitB.of_le (by omega)
  have : Fits w 1 := hfitp.of_le (by omega)
  have hvl := hπ l hlN
  have hvn := hπ l.negate hlN
  have hxor : litCode l ^^^ 1 = litCode l.negate := litCodeBy_xor_one _root_.id l
  have hshr : litCode l >>> 1 = l.1 := litCodeBy_shiftRight _root_.id l
  refine WP.exists_execWithin ?_
  unfold litBody
  cases hn : π.contains l.negate <;> cases hp : π.contains l <;>
    simp only [hn, hp, Bool.toNat_false, Bool.toNat_true] at hvl hvn
  all_goals rcases o with _ | x₀ <;> by_cases hL : x.mem (x.regs lb + l.1) = x.regs lptr
  all_goals
    simp only [Option.isSome_none, Option.isSome_some, Bool.toNat_false, Bool.toNat_true,
      Option.getD_none, Option.getD_some] at hopf hov
  all_goals
    wram_exec [hlit, hone, hzero, hvl, hvn, hxor, hshr, hcnt, huc, hsat, hopf, hov, hL]
    wram_simp
    have hn' : l.negate ∈ π ↔ π.contains l.negate = true := List.contains_iff_mem.symm
    have hp' : l ∈ π ↔ π.contains l = true := List.contains_iff_mem.symm
    rw [hn] at hn'
    rw [hp] at hp'
    simp [clauseLit, openLit, hn', hp', hL, huc, hsat, hov]

theorem clauseLit_cnt_le (π : List (Literal ℕ)) (r : ClauseRegs) (l : Literal ℕ) :
    (clauseLit π r l).cnt ≤ r.cnt + 1 := by
  unfold clauseLit; split <;> simp

/-- **The literal loop** computes `litsScan` over the literals at `lptr`, with the last
occurrences read from `lb`, and leaves memory unchanged. -/
theorem litLoop_spec (π : List (Literal ℕ)) (ls : Clause ℕ) (r : ClauseRegs) (o : Option ℕ)
    (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hend : x.regs lend = x.regs lptr + ls.length) (hN : ∀ l ∈ ls, l.1 < N)
    (hπ : LitArr x.mem (x.regs tb) N π)
    (hcnt : x.regs cnt = r.cnt) (huc : x.regs uc = r.uc) (hsat : x.regs sat = r.sat.toNat)
    (hopf : x.regs opf = o.isSome.toNat) (hov : x.regs ov = o.getD 0)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitB : Fits w (x.regs lb + N))
    (hfitp : Fits w (x.regs lend + 1)) (hfitc : Fits w (r.cnt + ls.length + 1)) :
    ∃ y, ExecWithin w litLoop x y (32 * ls.length + 2) ∧ y.mem = x.mem ∧
      y.regs cnt = (litsScan π (fun v => x.mem (x.regs lb + v)) (r, o) (x.regs lptr) ls).1.cnt ∧
      y.regs uc = (litsScan π (fun v => x.mem (x.regs lb + v)) (r, o) (x.regs lptr) ls).1.uc ∧
      y.regs sat =
        (litsScan π (fun v => x.mem (x.regs lb + v)) (r, o) (x.regs lptr) ls).1.sat.toNat ∧
      y.regs opf =
        (litsScan π (fun v => x.mem (x.regs lb + v)) (r, o) (x.regs lptr) ls).2.isSome.toNat ∧
      y.regs ov = (litsScan π (fun v => x.mem (x.regs lb + v)) (r, o) (x.regs lptr) ls).2.getD 0 ∧
      y.regs lptr = x.regs lend := by
  induction ls generalizing x r o with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), rfl, hcnt, huc, hsat, hopf, hov,
      by simp [hend]⟩
    simp [Cond.holds_lt, hend]
  | cons l ls ih =>
    simp only [List.length_cons] at hend hfitc
    have hc : (Cond.lt lptr lend).Holds x := by simp only [Cond.holds_lt, hend]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp (by simpa using hl)
    obtain ⟨y, hy, hym, hyc, hyu, hys, hyo, hyv, hyp⟩ := litBody_spec π l r o x N hzero hone hlit
      (hN l (by simp)) hπ hcnt huc hsat hopf hov hfit hfitB (hfitp.of_le (by omega))
      (hfitc.of_le (by omega))
    have hy0 : y.regs zero = 0 := (hy.regs_eq (by decide)).trans hzero
    have hy1 : y.regs one = 1 := (hy.regs_eq (by decide)).trans hone
    have hytb : y.regs tb = x.regs tb := hy.regs_eq (by decide)
    have hylb : y.regs lb = x.regs lb := hy.regs_eq (by decide)
    have hyle : y.regs lend = x.regs lend := hy.regs_eq (by decide)
    have hcle := clauseLit_cnt_le π r l
    obtain ⟨z, hz, hzm, hzc, hzu, hzs, hzo, hzv, hzp⟩ := ih (clauseLit π r l)
      (openLit π (fun v => x.mem (x.regs lb + v)) o (x.regs lptr) l) y hy0 hy1
      (by rw [hym, hyp]; exact hrest) (by rw [hyle, hyp, hend]; omega)
      (fun l' hl' => hN l' (by simp [hl'])) (by rw [hym, hytb]; exact hπ) hyc hyu hys hyo hyv
      (by rw [hytb]; exact hfit) (by rw [hylb]; exact hfitB) (by rw [hyle]; exact hfitp)
      (hfitc.of_le (by omega))
    rw [hym, hylb, hyp] at hzc hzu hzs hzo hzv
    refine ⟨z, (ExecWithin.loop_iter hc hy hz).mono (by simp only [List.length_cons]; omega),
      by rw [hzm, hym], ?_⟩
    simp only [litsScan]
    exact ⟨hzc, hzu, hzs, hzo, hzv, by rw [hzp, hyle]⟩

/-- The end of a clause: record a falsified clause, a clause without a true literal, and the
first unit clause. -/
theorem clauseEnd_spec (π : List (Literal ℕ)) (k u : ℕ) (b : Bool) (s : ScanRegs) (x : Data 32)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcnt : x.regs cnt = k) (huc : x.regs uc = u) (hsat : x.regs sat = b.toNat)
    (hconf : x.regs conf = s.conf.toNat) (halls : x.regs alls = s.alls.toNat)
    (huf : x.regs uf = s.unit.isSome.toNat) (hunit : x.regs unit = s.unit.getD 0)
    (hu : k = 1 → x.mem (x.regs tb + u) = (codeOn π u).toNat) (hfit : Fits w (x.regs tb + u)) :
    ∃ y, ExecWithin w clauseEnd x y 20 ∧ y.mem = x.mem ∧
      y.regs conf = (s.conf || k == 0).toNat ∧ y.regs alls = (s.alls && b).toNat ∧
      y.regs uf = (match s.unit with
        | some u' => some u'
        | none => if k == 1 && !codeOn π u then some u else none).isSome.toNat ∧
      y.regs unit = (match s.unit with
        | some u' => some u'
        | none => if k == 1 && !codeOn π u then some u else none).getD 0 ∧
      y.regs ptr = x.regs lend := by
  obtain ⟨sc, sa, su, so⟩ := s
  simp only at hconf halls huf hunit ⊢
  refine WP.exists_execWithin ?_
  unfold clauseEnd
  by_cases hk0 : k = 0
  · subst hk0
    cases su <;> cases b <;> cases sc <;> cases sa <;>
      wram_exec [hcnt, huc, hsat, hconf, halls, huf, hunit, hzero, hone, Bool.toNat_false,
        Bool.toNat_true, Option.isSome_none, Option.isSome_some, Option.getD_none,
        Option.getD_some] <;>
      wram_simp <;> simp [hunit]
  · by_cases hk1 : k = 1
    · subst hk1
      have hmem := hu rfl
      cases su <;> cases b <;> cases sc <;> cases sa <;> cases hco : codeOn π u <;>
        rw [hco] at hmem <;>
        wram_exec [hcnt, huc, hsat, hconf, halls, huf, hunit, hzero, hone, hmem,
          Bool.toNat_false, Bool.toNat_true, Option.isSome_none, Option.isSome_some,
          Option.getD_none, Option.getD_some] <;>
        wram_simp <;> simp [hunit]
    · have hk0' : (k == 0) = false := by simpa using hk0
      have hk1' : (k == 1) = false := by simpa using hk1
      cases su <;> cases b <;> cases sc <;> cases sa <;>
        wram_exec [hcnt, huc, hsat, hconf, halls, huf, hunit, hzero, hone, hk0, hk1,
          Bool.toNat_false, Bool.toNat_true, Option.isSome_none, Option.isSome_some,
          Option.getD_none, Option.getD_some] <;>
        wram_simp <;> simp [hk0', hk1', hunit]

/-- The scan registers hold `s`. -/
def ScanAt (y : Data 32) (s : ScanRegs) : Prop :=
  y.regs conf = s.conf.toNat ∧ y.regs alls = s.alls.toNat ∧ y.regs uf = s.unit.isSome.toNat ∧
    y.regs unit = s.unit.getD 0 ∧ y.regs opf = s.opened.isSome.toNat ∧
    y.regs ov = s.opened.getD 0

theorem uc_foldl_clauseLit (π : List (Literal ℕ)) (c : Clause ℕ) :
    (c.foldl (clauseLit π) ⟨0, 0, false⟩).uc = 0 ∨
      ∃ l ∈ notFalse π c, (c.foldl (clauseLit π) ⟨0, 0, false⟩).uc = litCode l := by
  obtain ⟨-, -, h⟩ := foldl_clauseLit π c ⟨0, 0, false⟩
  rw [h]
  cases hl : (notFalse π c).getLast? with
  | none => simp
  | some l => exact .inr ⟨l, List.mem_of_getLast? hl, by simp⟩

theorem uc_of_cnt_eq_one (π : List (Literal ℕ)) (c : Clause ℕ)
    (h : (c.foldl (clauseLit π) ⟨0, 0, false⟩).cnt = 1) :
    ∃ l ∈ notFalse π c, (c.foldl (clauseLit π) ⟨0, 0, false⟩).uc = litCode l := by
  obtain ⟨h₁, -, h₃⟩ := foldl_clauseLit π c ⟨0, 0, false⟩
  rw [h₃]
  cases hl : (notFalse π c).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl
    rw [h, hl] at h₁
    simp at h₁
  | some l => exact ⟨l, List.mem_of_getLast? hl, by simp⟩

/-- **One clause** of the scan performs `clauseScan`. -/
theorem clauseBody_spec (π : List (Literal ℕ)) (c : Clause ℕ) (s : ScanRegs) (x : Data 32)
    (N : ℕ) (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcl : HoldsList (x.regs ptr) (encodeClause c) x.mem) (hN : ∀ l ∈ c, l.1 < N)
    (hπ : LitArr x.mem (x.regs tb) N π) (hs : ScanAt x s)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitB : Fits w (x.regs lb + N))
    (hfitp : Fits w (x.regs ptr + c.length + 2)) :
    ∃ y, ExecWithin w clauseBody x y (32 * c.length + 30) ∧ y.mem = x.mem ∧
      ScanAt y (clauseScan π (fun v => x.mem (x.regs lb + v)) s (x.regs ptr) c) ∧
      y.regs ptr = x.regs ptr + c.length + 1 := by
  obtain ⟨hconf, halls, huf, hunit, hopf, hov⟩ := hs
  obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp hcl
  have : Fits w (x.regs ptr + 1) := hfitp.of_le (by omega)
  have : Fits w (x.regs ptr + 1 + c.length) := hfitp.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold clauseBody
  wram_exec [hlen, hone, hzero]
  refine WP.name fun x₁ hx₁ => ?_
  obtain ⟨x₂, hlit, hm₂, hc₂, hu₂, hs₂, ho₂, hv₂, hp₂⟩ := litLoop_spec (w := w) π c
    ⟨0, 0, false⟩ s.opened x₁ N
    (by subst hx₁; wram_simp [hzero]) (by subst hx₁; wram_simp [hone])
    (by subst hx₁; wram_simp; exact hlits) (by subst hx₁; wram_simp)
    hN (by subst hx₁; wram_simp; exact hπ) (by subst hx₁; wram_simp [hzero])
    (by subst hx₁; wram_simp [hzero]) (by subst hx₁; wram_simp [hzero, Bool.toNat_false])
    (by subst hx₁; wram_simp; exact hopf) (by subst hx₁; wram_simp; exact hov)
    (by subst hx₁; wram_simp; exact hfit) (by subst hx₁; wram_simp; exact hfitB)
    (by subst hx₁; wram_simp; exact hfitp.of_le (by omega))
    (hfitp.of_le (by simp; omega))
  have hz₂ : x₂.regs zero = 0 := (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hzero])
  have ho₂' : x₂.regs one = 1 := (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hone])
  have htb₂ : x₂.regs tb = x.regs tb := (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp)
  have hlb₂ : x₂.regs lb = x.regs lb := (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp)
  have hcf₂ : x₂.regs conf = s.conf.toNat :=
    (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hconf])
  have hal₂ : x₂.regs alls = s.alls.toNat :=
    (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [halls])
  have huf₂ : x₂.regs uf = s.unit.isSome.toNat :=
    (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [huf])
  have hun₂ : x₂.regs unit = s.unit.getD 0 :=
    (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hunit])
  have hle₂ : x₂.regs lend = x.regs ptr + 1 + c.length :=
    (hlit.regs_eq (by decide)).trans (by subst hx₁; wram_simp)
  subst hx₁
  wram_simp at hm₂ hc₂ hu₂ hs₂ ho₂ hv₂
  rw [fst_litsScan] at hc₂ hu₂ hs₂
  rw [snd_litsScan] at ho₂ hv₂
  simp only at hc₂ hu₂ hs₂ ho₂ hv₂
  set r := c.foldl (clauseLit π) ⟨0, 0, false⟩ with hr
  have hu : r.cnt = 1 → x₂.mem (x₂.regs tb + r.uc) = (codeOn π r.uc).toNat := by
    intro h1
    obtain ⟨l, hl, hul⟩ := uc_of_cnt_eq_one π c h1
    have hlc : l ∈ c := List.mem_of_mem_filter hl
    rw [hul, hm₂, htb₂, codeOn_litCode]
    exact hπ l (hN l hlc)
  have hucN : r.uc ≤ 2 * N := by
    rcases uc_foldl_clauseLit π c with h | ⟨l, hl, h⟩
    · rw [h]; omega
    · rw [h]; exact (litCode_lt (hN l (List.mem_of_mem_filter hl))).le
  refine WP.of_execWithin hlit ?_
  obtain ⟨y, hy, hym, hyc, hya, hyf, hyu, hyp⟩ := clauseEnd_spec (w := w) π r.cnt r.uc r.sat s x₂
    hz₂ ho₂' hc₂ hu₂ hs₂ hcf₂ hal₂ huf₂ hun₂ hu (by rw [htb₂]; exact hfit.of_le (by omega))
  refine WP.of_execWithin hy ?_
  refine ⟨by omega, by rw [hym, hm₂], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hyp, hle₂]; omega⟩
  · rw [hyc]; simp [clauseScan, fst_litsScan, ← hr]
  · rw [hya]; simp [clauseScan, fst_litsScan, ← hr]
  · rw [hyf]; simp [clauseScan, fst_litsScan, ← hr]
  · rw [hyu]; simp [clauseScan, fst_litsScan, ← hr]
  · rw [(hy.regs_eq (by decide)).trans ho₂]; simp [clauseScan, snd_litsScan]
  · rw [(hy.regs_eq (by decide)).trans hv₂]; simp [clauseScan, snd_litsScan]

/-- **The clause loop** performs `formulaScan` over the clauses from `ptr` to `cend`. -/
theorem clauseLoop_spec (π : List (Literal ℕ)) (ψ : CNF ℕ) (s : ScanRegs) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcl : HoldsList (x.regs ptr) (ψ.flatMap encodeClause) x.mem)
    (hend : x.regs ptr + (ψ.flatMap encodeClause).length = x.regs cend)
    (hN : ∀ c ∈ ψ, ∀ l ∈ c, l.1 < N) (hπ : LitArr x.mem (x.regs tb) N π) (hs : ScanAt x s)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitB : Fits w (x.regs lb + N))
    (hfitp : Fits w (x.regs cend + 1)) :
    ∃ y, ExecWithin w clauseLoop x y (32 * (ψ.flatMap encodeClause).length + 2) ∧
      y.mem = x.mem ∧
      ScanAt y (formulaScan π (fun v => x.mem (x.regs lb + v)) s (x.regs ptr) ψ) := by
  induction ψ generalizing x s with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono le_rfl, rfl, hs⟩
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero] at hend
    simp [Cond.holds_lt, hend]
  | cons c ψ ih =>
    simp only [List.flatMap_cons] at hcl hend
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hcl
    simp only [List.length_append, length_encodeClauseBy] at hend hpψ
    have hc : (Cond.lt ptr cend).Holds x := by simp only [Cond.holds_lt]; omega
    obtain ⟨y, hy, hym, hys, hyp⟩ := clauseBody_spec π c s x N hzero hone hpc
      (hN c (by simp)) hπ hs hfit hfitB (hfitp.of_le (by omega))
    have hy0 : y.regs zero = 0 := (hy.regs_eq (by decide)).trans hzero
    have hy1 : y.regs one = 1 := (hy.regs_eq (by decide)).trans hone
    have hytb : y.regs tb = x.regs tb := hy.regs_eq (by decide)
    have hylb : y.regs lb = x.regs lb := hy.regs_eq (by decide)
    have hyce : y.regs cend = x.regs cend := hy.regs_eq (by decide)
    obtain ⟨z, hz, hzm, hzs⟩ := ih _ y hy0 hy1
      (by rw [hym, hyp, show x.regs ptr + c.length + 1 = x.regs ptr + (c.length + 1) by omega]
          exact hpψ)
      (by rw [hyp, hyce]; omega) (fun c' hc' => hN c' (by simp [hc'])) (by rw [hym, hytb]; exact hπ)
      hys (by rw [hytb]; exact hfit) (by rw [hylb]; exact hfitB) (by rw [hyce]; exact hfitp)
    rw [hym, hylb, hyp] at hzs
    refine ⟨z, (ExecWithin.loop_iter hc hy hz).mono ?_, by rw [hzm, hym], ?_⟩
    · simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]; omega
    · simpa [formulaScan] using hzs

/-- **The scan** of the clauses `φ` stored from address `2` to `cend` against the trail `π`: the
registers end with `formulaScan` from the initial registers, and memory is unchanged. -/
theorem scan_spec (π : List (Literal ℕ)) (φ : CNF ℕ) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hcl : HoldsList 2 (φ.flatMap encodeClause) x.mem)
    (hend : 2 + (φ.flatMap encodeClause).length = x.regs cend)
    (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) (hπ : LitArr x.mem (x.regs tb) N π)
    (hfit : Fits w (x.regs tb + 2 * N)) (hfitB : Fits w (x.regs lb + N))
    (hfitp : Fits w (x.regs cend + 1)) :
    ∃ y, ExecWithin w scan x y (32 * (φ.flatMap encodeClause).length + 9) ∧ y.mem = x.mem ∧
      ScanAt y (formulaScan π (fun v => x.mem (x.regs lb + v)) .init 2 φ) := by
  refine WP.exists_execWithin ?_
  unfold scan
  wram_exec [hzero, hone, htwo]
  wram_call (clauseLoop_spec (w := w) π φ .init _ N (by wram_simp [hzero]) (by wram_simp [hone])
    (by wram_simp [htwo]; exact hcl) (by wram_simp [htwo]; exact hend) hN
    (by wram_simp; exact hπ)
    (by wram_simp [hzero, hone, ScanAt, ScanRegs.init]; simp)
    (by wram_simp; exact hfit) (by wram_simp; exact hfitB) (by wram_simp; exact hfitp))
    with y ⟨hym, hys⟩
  refine ⟨by omega, by simpa using hym, ?_⟩
  wram_simp [htwo] at hys
  exact hys

end Specs

end Cslib.Algorithms.WordRAM.DPLL

end
