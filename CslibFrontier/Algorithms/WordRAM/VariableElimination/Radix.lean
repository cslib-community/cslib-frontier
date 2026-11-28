/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Realize

/-!
# Integer Power (`powProg`) and Mixed-Radix Lookup (`lookupAssign`)

Realizable exact-basis Word-RAM routines for computing `d ^ n` and extracting the assigned value of
a variable from an LSB mixed-radix index over an array scope.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.powProg`: repeated multiplication computing `d ^ n`.
* `Cslib.Algorithms.WordRAM.VariableElimination.lookupAssign`: radix assignment value lookup.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Primitive 3: Power `d ^ n`, radix assignment lookup, and scope evaluation -/

/-- Arguments `(base, exp)` for `powProg`. -/
structure PowArgs where
  /-- Field `base` of `PowArgs`. -/
  base : ℕ
  /-- Field `exp` of `PowArgs`. -/
  exp : ℕ

/-- Product equivalence encoding `PowArgs` as words. -/
@[expose] def PowArgs.equiv : PowArgs ≃ ℕ × ℕ where
  toFun a := (a.base, a.exp)
  invFun := fun (base, exp) => ⟨base, exp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PowArgs := .ofEquiv PowArgs.equiv

private def powStep (env : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  pure (env.2 * env.1)

/-- Exact-basis Word-RAM program computing `base ^ exp`. -/
def powProg (args : PowArgs) : Memory.Prog ℕ :=
  iterate powStep args.base args.exp 1

theorem powProg_state (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (powProg args) = s :=
  clientState_iterate_eq_of powStep args.base (fun _ _ => rfl) args.exp 1 s

theorem powProg_cost (args : PowArgs) (s : Memory.State) :
    memoryCost (powProg args) s ≤ args.exp := by
  unfold powProg
  simpa using memoryCost_iterate_le_of powStep 1 args.base (fun _ _ => le_rfl) args.exp 1 s

theorem powProg_valid {w : ℕ} (args : PowArgs) {s : Memory.State} (hs : 0 < s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (powProg args)) :=
  validHistory_iterate_inv (fun t => 0 < t.frontier) powStep args.base
    (fun _ t ht => validHistory_read_bind ht (validHistory_pure w t _)) args.exp 1 hs

theorem powProg_result (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp := by
  unfold powProg
  suffices ∀ n acc, (Memory.spec 0).clientResult s (iterate powStep args.base n acc) =
      acc * args.base ^ n by
    simpa using this args.exp 1
  intro n
  induction n with
  | zero => exact fun acc => (Nat.mul_one acc).symm
  | succ n ih =>
    intro acc
    rw [iterate, StateTransitionSpec.clientResult_bind]
    exact (ih (acc * args.base)).trans (by rw [pow_succ', Nat.mul_assoc])

theorem powProg_realizes :
    Realizes .exact powProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w ((max 1 args.base) ^ args.exp)) (fun _ _ => 0) := by
  unfold powProg
  realize
  · exact h.1
  · refine iterationSafe_of_stepInv _ _ w d
      (fun j acc _ => acc * (max 1 d.base) ^ j ≤ (max 1 d.base) ^ d.exp)
      (fun j acc t hinv => ?_) (Nat.one_mul _).le
    have h2 : acc * d.base * (max 1 d.base) ^ j ≤ (max 1 d.base) ^ d.exp := by
      rw [pow_succ', ← Nat.mul_assoc] at hinv
      exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left acc (le_max_right 1 d.base))).trans hinv
    exact ⟨h.2.of_le
      ((Nat.le_mul_of_pos_right _ (Nat.one_le_pow j _ (le_max_left 1 d.base))).trans h2), h2⟩

/-- Arguments for reading the value of variable `v` in a mixed-radix assignment. -/
structure LookupArgs where
  /-- Field `dom` of `LookupArgs`. -/
  dom : ℕ
  /-- Field `target` of `LookupArgs`. -/
  target : ℕ
  /-- Field `outPtr` of `LookupArgs`. -/
  outPtr : ℕ
  /-- Field `outLen` of `LookupArgs`. -/
  outLen : ℕ
  /-- Field `idx` of `LookupArgs`. -/
  idx : ℕ

/-- Product equivalence encoding `LookupArgs` as words. -/
@[expose] def LookupArgs.equiv : LookupArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.dom, a.target), a.outPtr), a.outLen), a.idx)
  invFun := fun ((((dom, target), outPtr), outLen), idx) => ⟨dom, target, outPtr, outLen, idx⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding LookupArgs := .ofEquiv LookupArgs.equiv

private structure LookupEnv where
  dom : ℕ
  target : ℕ

private def LookupEnv.equiv : LookupEnv ≃ ℕ × ℕ where
  toFun e := (e.dom, e.target)
  invFun := fun (dom, target) => ⟨dom, target⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupEnv := .ofEquiv LookupEnv.equiv

private structure LookupState where
  cur : ℕ
  remIdx : ℕ
  found : ℕ
  ans : ℕ

private def LookupState.equiv : LookupState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.cur, s.remIdx), s.found), s.ans)
  invFun := fun (((cur, remIdx), found), ans) => ⟨cur, remIdx, found, ans⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupState := .ofEquiv LookupState.equiv

private def lookupStep (p : LookupEnv × LookupState) : Memory.Prog LookupState := do
  let u ← Memory.read p.2.cur
  let dig := p.2.remIdx % p.1.dom
  let nextIdx := p.2.remIdx / p.1.dom
  if p.2.found = 0 ∧ u = p.1.target then
    pure ⟨p.2.cur + 1, nextIdx, 1, dig⟩
  else
    pure ⟨p.2.cur + 1, nextIdx, p.2.found, p.2.ans⟩

/-- Look up variable `v` in an LSB-encoded radix-`dom` assignment. -/
def lookupAssign (args : LookupArgs) : Memory.Prog ℕ := do
  let res ← iterate lookupStep ⟨args.dom, args.target⟩ args.outLen ⟨args.outPtr, args.idx, 0, 0⟩
  pure res.ans

private theorem lookupStep_eval (env : LookupEnv) (st : LookupState) (t : Memory.State) :
    (Memory.spec 0).clientState t (lookupStep (env, st)) = t ∧
      (Memory.spec 0).clientResult t (lookupStep (env, st)) =
        if st.found = 0 ∧ t.mem st.cur = env.target then
          ⟨st.cur + 1, st.remIdx / env.dom, 1, st.remIdx % env.dom⟩
        else ⟨st.cur + 1, st.remIdx / env.dom, st.found, st.ans⟩ := by
  unfold lookupStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read]
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem lookup_iterate_succ (env : LookupEnv) (n : ℕ) (st : LookupState)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (iterate lookupStep env (n + 1) st) =
      (Memory.spec 0).clientResult s (iterate lookupStep env n
        (if st.found = 0 ∧ s.mem st.cur = env.target then
          ⟨st.cur + 1, st.remIdx / env.dom, 1, st.remIdx % env.dom⟩
        else ⟨st.cur + 1, st.remIdx / env.dom, st.found, st.ans⟩)) := by
  obtain ⟨hst, hres⟩ := lookupStep_eval env st s
  rw [iterate, StateTransitionSpec.clientResult_bind, hst, hres]

theorem lookupAssign_state (args : LookupArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (lookupAssign args) = s := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of lookupStep _ (fun a t => (lookupStep_eval _ a t).1)
    args.outLen _ s

theorem lookupAssign_cost (args : LookupArgs) (s : Memory.State) :
    memoryCost (lookupAssign args) s ≤ args.outLen := by
  unfold lookupAssign
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of lookupStep 1 ⟨args.dom, args.target⟩
    (fun a t => by
      unfold lookupStep
      rw [memoryCost_bind', memoryCost_read]
      split_ifs <;> simp)
    args.outLen ⟨args.outPtr, args.idx, 0, 0⟩ s

theorem lookupAssign_valid {w : ℕ} (args : LookupArgs) {s : Memory.State}
    (hb : args.outPtr + args.outLen ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (lookupAssign args)) := by
  obtain ⟨-, h⟩ := Memory.FramedTriple.iterate (w := w) (s := s) (body := lookupStep)
    (safe := fun _ _ _ => True) (d := ⟨args.dom, args.target⟩) (n := args.outLen)
    (a₀ := ⟨args.outPtr, args.idx, 0, 0⟩) (c := 1) (S := ∅) (Q := fun _ _ => True)
    (fun k st _ => st.cur = args.outPtr + k) rfl (fun k hk st t hst hm => ⟨trivial, by
      have := hm.1; unfold lookupStep; framed_triple⟩)
    fun _ _ _ _ => trivial
  unfold lookupAssign
  exact (Memory.FramedTriple.call (c₂ := 0) h subset_rfl fun _ _ _ _ =>
    Memory.FramedTriple.pure (Q := fun _ _ => True) trivial).validHistory

theorem lookupAssign_result {args : LookupArgs} {us : List ℕ} {s : Memory.State}
    (hus : Block.HoldsList args.outPtr us s.mem) (hlen : us.length = args.outLen) :
    (Memory.spec 0).clientResult s (lookupAssign args) =
      assignScope us (lsbDecode args.dom us.length args.idx) args.target := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientResult_bind, ← hlen]
  have hfound1 : ∀ (n cur remIdx ans : ℕ),
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ n ⟨cur, remIdx, 1, ans⟩)).ans = ans := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro cur remIdx ans
      rw [lookup_iterate_succ, ite_eq_right (fun h => absurd h.1 one_ne_zero)]
      exact ih _ _ _
  suffices ∀ (zs : List ℕ) (cur remIdx : ℕ), Block.HoldsList cur zs s.mem →
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ zs.length ⟨cur, remIdx, 0, 0⟩)).ans =
      assignScope zs (lsbDecode args.dom zs.length remIdx) args.target from
    this us args.outPtr args.idx hus
  intro zs
  induction zs with
  | nil => intro cur remIdx _; rfl
  | cons u rest ih =>
    intro cur remIdx hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    rw [List.length_cons, lookup_iterate_succ]
    dsimp only
    rw [hhead]
    by_cases htu : args.target = u
    · rw [ite_eq_left ⟨rfl, htu.symm⟩, hfound1]
      simp [lsbDecode, assignScope, htu]
    · rw [ite_eq_right (fun h => htu h.2.symm), ih (cur + 1) (remIdx / args.dom) htail]
      simp [lsbDecode, assignScope, htu]

theorem lookupAssign_realizes :
    Realizes .exact lookupAssign WordEncoding.encode WordEncoding.encode
      (fun w args _ => 0 < args.dom ∧ Fits w 1 ∧ Fits w (args.outPtr + args.outLen))
      (fun _ _ => 0) := by
  unfold lookupAssign
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.cur + j = d.outPtr + d.outLen) (fun j st t hinv => ?_) rfl
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact ⟨h.1.ne', h.2.2.of_le (by omega), h.2.1⟩
    all_goals exact ⟨h.1.ne', h.2.2.of_le (by omega)⟩
  · rw [(lookupStep_eval _ st t).2]
    split_ifs <;> (dsimp only; omega)

theorem lookupAssign_lt {args : LookupArgs} (hd : 0 < args.dom) (s : Memory.State) :
    (Memory.spec 0).clientResult s (lookupAssign args) < args.dom := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ (n cur remIdx found ans : ℕ), ans < args.dom →
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ n ⟨cur, remIdx, found, ans⟩)).ans <
      args.dom from
    this args.outLen args.outPtr args.idx 0 0 hd
  intro n
  induction n with
  | zero => intro _ _ _ _ hans; exact hans
  | succ n ih =>
    intro cur remIdx found ans hans
    rw [lookup_iterate_succ]
    split_ifs
    exacts [ih _ _ _ _ (Nat.mod_lt _ hd), ih _ _ _ _ hans]

end Cslib.Algorithms.WordRAM.VariableElimination
