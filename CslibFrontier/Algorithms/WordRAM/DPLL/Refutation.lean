/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Solver
public import CslibFrontier.Algorithms.Lean.DPLL.SearchTree
public import CslibFrontier.Computability.WordRAM.OutputLowerBound
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop

/-!
# The DPLL solver on the word RAM writing its search tree

This file gives a variant of the word-RAM DPLL solver (`Cslib.Algorithms.WordRAM.DPLL.program`)
that also writes the tree its search explores (`Cslib.Algorithms.WordRAM.DPLL.programLog`), and
uses it to transfer the lower bound of Beyersdorff, Galesi and Lauria
[BeyersdorffGalesiLauria2010, Theorem 2] on tree-like refutations of the pigeonhole formulas to a
lower bound on instructions.

## The output

The variant runs the same steps of the search with an explicit trail
(`Cslib.Algorithms.Lean.DPLL.Trail.run`), and logs one word at each node of the tree it explores
(`Cslib.Algorithms.Lean.DPLL.searchTree`), in preorder
(`Cslib.Algorithms.WordRAM.DPLL.treeWords`):

* at a partial assignment that falsifies a clause, the address in the input of the first falsified
  clause, which is below the end `T` of the clauses (`Cslib.Algorithms.WordRAM.DPLL.clauseAddr`);
* at a branching on the literal `l = (v, b)`, tried first, the address `T + 2 v + b` of the cell of
  `l` in the solver's literal array, which is at least `T`.

The words thus tell leaves from branchings, name the clause at each leaf and the variable and the
first branch at each branching, and so determine the tree: reading them back
(`Cslib.Algorithms.WordRAM.DPLL.decodeTree`) gives the tree
(`Cslib.Algorithms.WordRAM.DPLL.decodeTree_treeWords`). On an unsatisfiable formula this tree
finds a falsified clause on every assignment
(`Cslib.Algorithms.Lean.DPLL.findsFalsifiedClause_searchTree`), and so is a tree-like resolution
refutation in decision-tree form
(`Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation`). The output
(`Cslib.Algorithms.WordRAM.DPLL.refutationWords`) is that of the solver, `[0]` or `1` followed by
the model, followed for an unsatisfiable formula by these words. The log grows from `T + 4 N + 2`,
after the trail; the register `lg` points past it.

## The lower bound

Every word of the tree is at least `2`, and is written to a cell above the input, which starts at
`0`; so each costs a store (`Cslib.WordRAM.Runs.block_lowerBound`), and every halting run takes at
least as many instructions as the tree has leaves
(`Cslib.Algorithms.WordRAM.DPLL.leafCount_searchTree_le_of_executes`). On `PHP^m_n`, `m > n`, with
its variables numbered by an injective map, the tree has at least `(n / 2 + 1) ^ (n / 2)`
leaves (`Cslib.Algorithms.Lean.DPLL.pow_half_le_leafCount_searchTree_pigeonhole`), and so the
variant takes at least `(n / 2 + 1) ^ (n / 2)` instructions
(`Cslib.Algorithms.WordRAM.DPLL.programLog_pigeonhole`).

Writing the tree costs a pass over the clauses at each leaf, to find the falsified clause, and a
few instructions at each node, so the variant halts within `2 ^ (d + 1) (60 E + 78) + 10 N + 15`
instructions, `d` the number of distinct variables and `E` the length of the input
(`Cslib.Algorithms.WordRAM.DPLL.programLog_spec`), and within `301 · 2 ^ N · E`
(`Cslib.Algorithms.WordRAM.DPLL.programLog_spec_pow`). The word size must fit the addresses of
the log, up to `E + 5 N + 3 + 2 ^ (d + 1)`.

## Main definitions

* `Cslib.Algorithms.WordRAM.DPLL.programLog`: the variant.
* `Cslib.Algorithms.WordRAM.DPLL.treeWords`, `Cslib.Algorithms.WordRAM.DPLL.refutationWords`: the
  words of the search tree and the output of the variant.
* `Cslib.Algorithms.WordRAM.DPLL.decodeTree`: reading the words back to a decision tree.

## Main results

* `Cslib.Algorithms.WordRAM.DPLL.programLog_spec`,
  `Cslib.Algorithms.WordRAM.DPLL.programLog_spec_pow`: the output and the upper bounds.
* `Cslib.Algorithms.WordRAM.DPLL.decodeTree_treeWords`: on an unsatisfiable formula, the words of
  the tree read back to a decision tree finding a falsified clause, a tree-like refutation.
* `Cslib.Algorithms.WordRAM.DPLL.leafCount_searchTree_le_of_executes`: an instruction per leaf.
* `Cslib.Algorithms.WordRAM.DPLL.programLog_pigeonhole`: at least `(n / 2 + 1) ^ (n / 2)`
  instructions on `PHP^m_n`, `m > n`, and at most `301 · 2 ^ N · E`.

## References

* [O. Beyersdorff, N. Galesi, M. Lauria, *A lower bound for the pigeonhole principle in tree-like
  Resolution by asymmetric Prover–Delayer games*][BeyersdorffGalesiLauria2010]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Algorithms.WordRAM.ClauseCode Cslib.Algorithms.Lean.DPLL Reg

/-! ### The program -/

/-- One clause of the search for a falsified clause: the literal loop counts the literals of the
clause at `ptr` not falsified; with none, the search stops at it, and otherwise moves on. -/
def findBody : Code .standard 32 := ram[
  len ← *ptr; lptr ← ptr + one; lend ← lptr + len; cnt ← zero; uc ← zero; sat ← zero;
  opf ← zero; ov ← zero; ⟪litLoop⟫;
  if cnt = zero then [ aux ← zero ] else [ ptr ← lend ] ]

/-- The search for the first falsified clause from `ptr`. -/
def findLoop : Code .standard 32 := .loop (.eq aux one) findBody

/-- Log the address of the first falsified clause. -/
def logConflict : Code .standard 32 := ram[
  ptr ← two; aux ← one; ⟪findLoop⟫; *lg ← ptr; lg ← lg + one ]

/-- Log the cell of the literal on top of the trail in the literal array. -/
def logBranch : Code .standard 32 := ram[
  addr ← tp - two; addr ← *addr; addr ← tb + addr; *lg ← addr; lg ← lg + one ]

/-- Set the length of the output `[0, …]` to cover the log. -/
def fixHeader : Code .standard 32 := ram[ addr ← lg - ob; addr ← addr - one; *ob ← addr ]

/-- **One step of the search, logged**: the step of `Cslib.Algorithms.WordRAM.DPLL.stepBody`,
logging the first falsified clause before backtracking and the pushed literal after branching. -/
def stepBodyLog : Code .standard 32 := ram[
  ⟪scan⟫;
  if conf = one then [
    ⟪logConflict⟫; ⟪backtrack⟫; if go = zero then [ ⟪fixHeader⟫ ] else [ go ← go ] ]
  else [
    if alls = one then [ ⟪outSat⟫ ] else [ ⟪push⟫; ⟪logBranch⟫ ] ] ]

/-- The logged search: logged steps while `go = 1`. -/
def mainLoopLog : Code .standard 32 := .loop (.eq go one) stepBodyLog

/-- **The DPLL solver writing its search tree** on the input `encode N φ`, leaving the address of
its output in `out`. -/
def solverLog : Code .standard 32 := ram[ ⟪setup⟫; lg ← ob + two; ⟪mainLoopLog⟫ ]

/-- **The DPLL solver writing its search tree** as a flat program returning its output list. -/
def programLog : Program .standard 32 := solverLog.program out

/-! ### The log -/

/-- The address in the input `encode N φ` of the clause `i` of `φ`: its length word. -/
def clauseAddr (φ : CNF ℕ) (i : ℕ) : ℕ := 2 + ((φ.take i).flatMap encodeClause).length

/-- The words logged at the partial assignment `π`: at a falsified clause, the address of the
first falsified clause; at a branching on `l`, the address `T + 2 v + b` of the cell of
`l = (v, b)` in the literal array, where `T` is the end of the clauses. -/
def logOut (φ : CNF ℕ) (π : List (Literal ℕ)) : List ℕ :=
  match status φ π with
  | .conflict => [clauseAddr φ (φ.findIdx (Falsifies π))]
  | .branch l => [2 + (φ.flatMap encodeClause).length + litCode l]
  | .sat => []

/-- **The words of the search tree**: the words of its nodes in preorder, the address of a
falsified clause at each leaf and the literal array cell of the first branch at each branching. -/
def treeWords (φ : CNF ℕ) : List ℕ := preorder φ (logOut φ) (depth φ) []

/-- The output of the variant: the output of the solver, `[0]` or the model, followed for an
unsatisfiable formula by the words of the search tree. -/
def refutationWords (N : ℕ) (φ : CNF ℕ) : List ℕ :=
  answerWords N φ ++
    match solve φ with
    | .sat _ => []
    | .unsat _ => treeWords φ

/-- The output for an answer of the search and the log: the model, or `0` followed by the log. -/
def answerLog (N : ℕ) : Trail.Answer → List ℕ → List ℕ
  | .sat π, _ => modelWords N π
  | .unsat, log => 0 :: log

/-- The log `log` is stored from `T + 4 N + 2`, and `lg` points past it. -/
def LogAt (N T : ℕ) (x : Data 32) (log : List ℕ) : Prop :=
  x.regs lg = T + 4 * N + 2 + log.length ∧ HoldsList (T + 4 * N + 2) log x.mem

private theorem length_logOut_le (φ : CNF ℕ) (π : List (Literal ℕ)) : (logOut φ π).length ≤ 1 := by
  unfold logOut
  split <;> simp

/-- A store at or above `T + 4 N` keeps the memory of a trail. -/
theorem MemAt.update_ge {φ : CNF ℕ} {N T : ℕ} {mem : ℕ → ℕ} {t : Trail} (h : MemAt φ N T mem t)
    {a : ℕ} (ha : T + 4 * N ≤ a) (v : ℕ) : MemAt φ N T (Function.update mem a v) t := by
  have hlen := h.ok.length_le fun v hv => mem_vars_lt h hv
  have hT := h.hT
  refine ⟨h.clauses.frame fun b _ hb => Function.update_of_ne (by omega) _ _, h.hT, h.vars,
    h.lits.update_ge (by omega) v, h.trail.frame fun b _ hb => ?_, h.ok⟩
  rw [length_trailWords] at hb
  exact Function.update_of_ne (by omega) _ _

/-! ### Reading the tree back -/

/-- The clause whose length word is at the address `a` of the input, for the clauses of `φ` from
address `2`; the empty clause if there is none. -/
def clauseAt : CNF ℕ → ℕ → Clause ℕ
  | [], _ => []
  | c :: φ, a => if a = 2 then c else clauseAt φ (a - (c.length + 1))

/-- **Reading the words of a tree** of the clauses `φ`: a word below the end
`T = 2 + (φ.flatMap encodeClause).length` of the clauses is a leaf with the clause at that address;
a word `T + 2 v + b` is a branching on `v`, its first branch `(v, b)` followed by its second
branch. With `k` words to read at most, the tree and the words after it. -/
def decodeTree (φ : CNF ℕ) : ℕ → List ℕ → Option (DecisionTree ℕ (Clause ℕ) × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, a :: rest =>
    if a < 2 + (φ.flatMap encodeClause).length then some (.leaf (clauseAt φ a), rest)
    else
      let u := a - (2 + (φ.flatMap encodeClause).length)
      match decodeTree φ k rest with
      | none => none
      | some (t₁, rest₁) =>
        match decodeTree φ k rest₁ with
        | none => none
        | some (t₂, rest₂) =>
          some (if u % 2 = 1 then .node (u / 2) t₂ t₁ else .node (u / 2) t₁ t₂, rest₂)

theorem clauseAt_clauseAddr (φ : CNF ℕ) (p : Clause ℕ → Bool) :
    clauseAt φ (clauseAddr φ (φ.findIdx p)) = (φ.find? p).getD [] := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    by_cases hc : p c = true
    · simp [clauseAt, clauseAddr, List.findIdx_cons, hc]
    · have : clauseAddr (c :: φ) (φ.findIdx p + 1) = clauseAddr φ (φ.findIdx p) + (c.length + 1) :=
        by simp [clauseAddr]; omega
      simp only [List.findIdx_cons, hc, this, clauseAt, List.find?_cons, Bool.false_eq_true,
        ↓reduceIte]
      rw [ite_eq_right (by simp [clauseAddr]; omega), Nat.add_sub_cancel, ih]

private theorem clauseAddr_lt {φ : CNF ℕ} {i : ℕ} (h : i < φ.length) :
    clauseAddr φ i < 2 + (φ.flatMap encodeClause).length := by
  induction φ generalizing i with
  | nil => simp at h
  | cons c φ ih =>
    cases i with
    | zero => simp [clauseAddr]
    | succ i =>
      have := ih (i := i) (by simpa using h)
      simp only [clauseAddr, List.take_succ_cons, List.flatMap_cons, List.length_append,
        length_encodeClauseBy] at this ⊢
      omega

/-- **The words of a subtree read back to it**, when it has no model. -/
theorem decodeTree_preorder (φ : CNF ℕ) :
    (fuel : ℕ) → (π : List (Literal ℕ)) → (openVars φ π).length ≤ fuel →
      dfs φ fuel π = none → (k : ℕ) → (preorder φ (logOut φ) fuel π).length ≤ k →
      (rest : List ℕ) →
        decodeTree φ k (preorder φ (logOut φ) fuel π ++ rest) =
          some (searchTree φ fuel π, rest)
  | fuel, π, hf, hd, k, hk, rest => by
    cases hs : status φ π with
    | sat => cases fuel <;> simp [dfs, hs] at hd
    | conflict =>
      have hidx : φ.findIdx (Falsifies π) < φ.length :=
        List.findIdx_lt_length_of_exists (by simpa using any_falsifies_of_status_eq_conflict hs)
      cases k with
      | zero => cases fuel <;> simp [preorder, logOut, hs] at hk
      | succ k =>
        cases fuel <;> simp only [preorder, logOut, searchTree, falsifiedClause, hs,
          List.singleton_append, decodeTree, ite_eq_left (clauseAddr_lt hidx), clauseAt_clauseAddr]
    | branch l =>
      obtain ⟨fuel, rfl, hlen⟩ := length_openVars_cons_le hs hf
      rw [dfs, hs, Option.or_eq_none_iff] at hd
      have hp : preorder φ (logOut φ) (fuel + 1) π =
          (2 + (φ.flatMap encodeClause).length + litCode l) ::
            (preorder φ (logOut φ) fuel (l :: π) ++ preorder φ (logOut φ) fuel (l.negate :: π)) :=
        by simp [preorder, logOut, hs]
      rw [hp] at hk ⊢
      simp only [List.length_cons, List.length_append] at hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have ih₁ := decodeTree_preorder φ fuel _ (hlen l rfl) hd.1 k (by omega)
        (preorder φ (logOut φ) fuel (l.negate :: π) ++ rest)
      have ih₂ := decodeTree_preorder φ fuel _ (hlen l.negate rfl) hd.2 k (by omega) rest
      rw [List.cons_append, decodeTree, ite_eq_right (by omega), Nat.add_sub_cancel_left,
        List.append_assoc, ih₁]
      simp only [ih₂]
      obtain ⟨v, b⟩ := l
      cases b <;> simp [searchTree, hs, litCode, litCodeBy, Std.Sat.Literal.negate]
      omega
  termination_by fuel => fuel

/-- **The output determines a tree-like refutation**: on an unsatisfiable formula, the words of the
search tree read back to a decision tree that finds a falsified clause of `φ` on every assignment,
which is a tree-like resolution refutation of `φ`
(`Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation`). -/
theorem decodeTree_treeWords {φ : CNF ℕ} (h : ¬ φ.Satisfiable) :
    ∃ t, decodeTree φ (treeWords φ).length (treeWords φ) = some (t, []) ∧
      t.FindsFalsifiedClause φ := by
  refine ⟨_, ?_, findsFalsifiedClause_searchTree h⟩
  simpa [treeWords] using decodeTree_preorder φ (depth φ) [] (by simp [openVars_nil, depth])
    (dfs_eq_none_of_not_satisfiable h) _ le_rfl []

/-! ### Finding the falsified clause -/

section Specs

variable {w : ℕ}

attribute [local wram_simps] LitAt Bool.toNat_false Bool.toNat_true Option.isSome_none
  Option.getD_none

/-- **The search for a falsified clause** among the clauses `ψ` from `ptr`, one of which `π`
falsifies, stops at the address of the first of them, and leaves memory unchanged. -/
theorem findLoop_spec (π : List (Literal ℕ)) (ψ : CNF ℕ) (x : Data 32) (N : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (haux : x.regs aux = 1)
    (hcl : HoldsList (x.regs ptr) (ψ.flatMap encodeClause) x.mem)
    (hN : ∀ c ∈ ψ, ∀ l ∈ c, l.1 < N) (hπ : LitArr x.mem (x.regs tb) N π)
    (hfit : Fits w (x.regs tb + 2 * N))
    (hfitp : Fits w (x.regs ptr + (ψ.flatMap encodeClause).length + 1))
    (hf : ψ.any (Falsifies π) = true) :
    ∃ y, ExecWithin w findLoop x y (23 * (ψ.flatMap encodeClause).length) ∧ y.mem = x.mem ∧
      y.regs ptr =
        x.regs ptr + ((ψ.take (ψ.findIdx (Falsifies π))).flatMap encodeClause).length := by
  induction ψ generalizing x with
  | nil => simp at hf
  | cons c ψ ih =>
    simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy] at hcl hfitp ⊢
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hcl
    obtain ⟨hlen, hlits⟩ := holdsList_cons_iff.mp hpc
    simp only [length_encodeClauseBy] at hpψ
    have hpψ' : HoldsList (x.regs ptr + 1 + c.length) (ψ.flatMap encodeClause) x.mem :=
      Nat.add_right_comm (x.regs ptr) 1 c.length ▸ hpψ
    have hNψ : ∀ c ∈ ψ, ∀ l ∈ c, l.1 < N := fun c' h => hN c' (by simp [h])
    have hNc := hN c (by simp)
    obtain ⟨hcnt, -⟩ := foldl_litStep π c ⟨0, 0, false, none⟩
    refine WP.exists_execWithin (WP.loop_iter (by simp [Cond.holds_eq, haux, hone]) ?_)
    unfold findBody
    wram_exec [hlen, hone, hzero]
    wram_call (litLoop_spec (w := w) π c ⟨0, 0, false, none⟩ _ N ..) framed
      with v₂ m₂ ⟨rfl, ⟨hcnt₂, -⟩, hp₂⟩
    rw [hcnt] at hcnt₂
    by_cases hc : Falsifies π c = true
    · wram_exec [hcnt₂, List.length_eq_zero_iff.2 ((notFalse_eq_nil_iff π c).2 hc), hzero]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_eq, hone])) ?_
      refine ⟨by omega, ?_⟩
      wram_simp [List.findIdx_cons, hc]
      simp
    · have h0 : (notFalse π c).length ≠ 0 := by
        rwa [Ne, List.length_eq_zero_iff, notFalse_eq_nil_iff]
      have hfψ' : ψ.any (Falsifies π) = true := by simpa [hc] using hf
      wram_exec [hcnt₂, h0, hzero]
      wram_call (ih _ ..) framed with v₃ m₃ ⟨rfl, hp₃⟩
      refine ⟨by omega, rfl, ?_⟩
      simp [hp₃, List.findIdx_cons, hc]
      omega

attribute [local wram_simps] StateAt LogAt ScanAt

/-- **Logging a falsified clause**: the address of the first clause falsified by the trail. -/
theorem logConflict_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (log : List ℕ) (x : Data 32)
    (hs : StateAt φ N T x t) (hl : LogAt N T x log)
    (hc : status φ (Trail.lits t) = .conflict) (hfit : Fits w (T + 5 * N + 3 + log.length)) :
    ∃ y, ExecWithin w logConflict x y (23 * (φ.flatMap encodeClause).length + 6) ∧
      StateAt φ N T y t ∧ LogAt N T y (log ++ logOut φ (Trail.lits t)) := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := id hs
  obtain ⟨hlg, hlog⟩ := hl
  have hT := hmem.hT
  have hany := any_falsifies_of_status_eq_conflict hc
  have hcl := hmem.clauses
  have hvars := hmem.vars
  have hlits := hmem.lits
  have hmem' := hmem.update_ge (a := T + 4 * N + 2 + log.length) (by omega)
    (clauseAddr φ (φ.findIdx (Falsifies (Trail.lits t))))
  have hlog' := hlog.append_one (clauseAddr φ (φ.findIdx (Falsifies (Trail.lits t))))
  have hout : logOut φ (Trail.lits t) = [clauseAddr φ (φ.findIdx (Falsifies (Trail.lits t)))] := by
    simp only [logOut, hc]
  refine WP.exists_execWithin ?_
  unfold logConflict
  wram_exec [h2, h1]
  wram_call (findLoop_spec (w := w) (Trail.lits t) φ _ N ..) framed [*] with v m ⟨rfl, hptr⟩
  wram_exec [*]
  wram_simp [*]
  exact ⟨hmem', by simp; omega, hlog'⟩

/-- **Logging a branching**: the cell of the literal on top of the trail. -/
theorem logBranch_spec (φ : CNF ℕ) (N T : ℕ) (l : Literal ℕ) (t : Trail) (log : List ℕ)
    (x : Data 32) (hs : StateAt φ N T x (⟨l, false⟩ :: t)) (hl : LogAt N T x log)
    (hfit : Fits w (T + 5 * N + 3 + log.length)) :
    ∃ y, ExecWithin w logBranch x y 5 ∧ StateAt φ N T y (⟨l, false⟩ :: t) ∧
      LogAt N T y (log ++ [T + litCode l]) := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := id hs
  obtain ⟨hlg, hlog⟩ := hl
  obtain ⟨hcode, -⟩ := hmem.top
  have hlen := hmem.ok.length_le fun v hv => mem_vars_lt hmem hv
  have hcl := litCode_lt (mem_vars_lt hmem (hmem.ok.2 ⟨l, false⟩ List.mem_cons_self))
  simp only [List.length_cons] at hlen htp
  have e2 : T + 2 * N + 2 * (t.length + 1) - 2 = T + 2 * N + 2 * t.length := by omega
  have hmem' := hmem.update_ge (a := T + 4 * N + 2 + log.length) (by omega) (T + litCode l)
  have hlog' := hlog.append_one (T + litCode l)
  refine WP.exists_execWithin ?_
  unfold logBranch
  wram_exec [*]
  wram_simp [*]
  exact ⟨by simp, by simp; omega⟩

/-- The instructions of one logged step: those of `Cslib.Algorithms.WordRAM.DPLL.stepTime`, a
search for the falsified clause, and the log. -/
def stepTimeLog (φ : CNF ℕ) (N : ℕ) (t : Trail) : ℕ :=
  stepTime φ N t + 23 * (φ.flatMap encodeClause).length + 16

/-- **One logged step of the search**: the state and the log of the next trail, or the output of
the answer and the log at `T + 4 N`. -/
theorem stepBodyLog_spec (φ : CNF ℕ) (N T : ℕ) (t : Trail) (log : List ℕ) (x : Data 32)
    (hs : StateAt φ N T x t) (hl : LogAt N T x log) (hfit : Fits w (T + 5 * N + 3 + log.length)) :
    ∃ y, ExecWithin w stepBodyLog x y (stepTimeLog φ N t) ∧
      match Trail.step φ t with
      | .inr t' => StateAt φ N T y t' ∧ LogAt N T y (log ++ logOut φ (Trail.lits t))
      | .inl a => y.regs go = 0 ∧ y.regs out = T + 4 * N ∧
          outputList y.mem (T + 4 * N) = answerLog N a (log ++ logOut φ (Trail.lits t)) := by
  obtain ⟨hz, h1, h2, htb, hce, hsb, hob, hnv, hgo, htp, hmem⟩ := id hs
  obtain ⟨hlg, hlog⟩ := id hl
  set π := Trail.lits t with hπdef
  have hT := hmem.hT
  have hcl := hmem.clauses
  have hvars := hmem.vars
  have hlits := hmem.lits
  have hfit' : Fits w (T + 5 * N + 2) := hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold stepBodyLog
  refine WP.seq ?_
  wram_call (scan_spec (w := w) π φ _ N ..) framed [hz, h1, h2, htb, hce]
    with v m ⟨rfl, hconf, halls, huf, hunit, hopf, hov⟩
  have hs' : StateAt φ N T (x.havoc scan v x.mem) t := by wram_simp [*]
  have hl' : LogAt N T (x.havoc scan v x.mem) log := by wram_simp [*]
  unfold stepTimeLog stepTime
  by_cases hc : φ.any (Falsifies π) = true
  · have hstat := status_eq_conflict hc
    have hstep := Trail.step_of_status_eq_conflict hstat
    rw [hc, Bool.toNat_true] at hconf
    wram_exec [hconf, h1]
    wram_call (logConflict_spec (w := w) φ N T t log _ hs' hl' hstat hfit) framed with v₁ m₁
      ⟨⟨-, -, -, -, -, -, -, -, -, -, hmem₁⟩, hlg₁, hlog₁⟩
    have hs₁ : StateAt φ N T (Data.havoc logConflict (x.havoc scan v x.mem) v₁ m₁) t := by
      wram_simp [*]
    refine WP.seq ?_
    wram_call (backtrack_spec (w := w) φ N T t _ hs₁ hfit') framed with v₂ m₂ ⟨h₂, hfr₂⟩
    rw [hstep]
    have hlog₂ : HoldsList (T + 4 * N + 2) (log ++ logOut φ (Trail.lits t)) m₂ :=
      hlog₁.frame fun a ha _ => by simpa using hfr₂ a ha
    have hlen' : (log ++ logOut φ (Trail.lits t)).length = log.length + 1 := by
      simp [logOut, ← hπdef, hstat]
    have e₁ : T + 4 * N + 2 + (log.length + 1) - (T + 4 * N) = log.length + 3 := by omega
    have hfa : Fits w (log.length + 3) := hfit.of_le (by omega)
    have hfa' : Fits w (log.length + 3 - 1) := hfit.of_le (by omega)
    cases hb : Trail.backtrack t <;> rw [hb] at h₂ <;> simp only at h₂ ⊢
    · obtain ⟨hgo₂, hout₂, hl₂⟩ := h₂
      obtain ⟨hh₂, hz₂⟩ := outputList_eq_iff.1 hl₂
      have hz₂' : m₂ (T + 4 * N + 1) = 0 := (holdsList_cons_iff.1 hz₂).1
      wram_exec [hgo₂, hz]
      unfold fixHeader
      wram_exec [*, hlen', e₁]
      refine ⟨by wram_simp [*], by wram_simp [*], ?_⟩
      rw [outputList_eq_iff]
      wram_simp [*]
      refine ⟨by simp [answerLog, hlen'], ?_⟩
      rw [answerLog, holdsList_cons_iff]
      exact ⟨by rw [Function.update_of_ne (by omega)]; exact hz₂',
        hlog₂.frame fun a ha _ => Function.update_of_ne (by omega) _ _⟩
    · obtain ⟨-, -, -, -, -, -, -, -, hgo₂, htp₂, hmem₂⟩ := h₂
      wram_exec [hgo₂, hz]
      wram_simp [*]
  · rw [Bool.not_eq_true] at hc
    rw [hc, Bool.toNat_false] at hconf
    by_cases ha : (φ.all fun c => c.any (Holds π)) = true
    · have hstep := Trail.step_of_status_eq_sat (status_eq_sat hc ha)
      rw [ha, Bool.toNat_true] at halls
      wram_exec [hconf, halls, h1]
      wram_call (outSat_spec (w := w) φ N T t _ hs' hfit') framed with v₂ m₂ hz₂
      rw [hstep]
      exact ⟨by simp only; omega, hz₂⟩
    · rw [Bool.not_eq_true] at ha
      rw [ha, Bool.toNat_false] at halls
      have hstat := status_eq_branch hc ha
      have hstep := Trail.step_of_status_eq_branch hstat
      obtain ⟨hv, hun⟩ := assigned_of_status_eq_branch hstat
      have hcode := branchCode_eq φ π huf hunit hov
      have hout : logOut φ (Trail.lits t) = [T + litCode (nextLiteral φ π)] := by
        simp [logOut, ← hπdef, hstat, ← hT]
      wram_exec [hconf, halls, h1]
      wram_call (push_spec (w := w) φ N T _ t _ hs' (by wram_simp; exact hcode) hv hun hfit')
        framed with v₂ m₂ ⟨⟨-, -, -, -, -, -, -, -, -, htp₂, hmem₂⟩, hfr₂⟩
      have hl₂ : LogAt N T (Data.havoc push (x.havoc scan v x.mem) v₂ m₂) log := by
        wram_simp [*]
        exact hlog.frame fun a ha _ => by simpa using hfr₂ a (by omega)
      have hs₂' : StateAt φ N T (Data.havoc push (x.havoc scan v x.mem) v₂ m₂)
          (⟨nextLiteral φ π, false⟩ :: t) := by
        wram_simp [*]
        exact hmem₂
      wram_call (logBranch_spec (w := w) φ N T _ t log _ hs₂' hl₂ hfit) framed
        with v₃ m₃ ⟨hs₃, hl₃⟩
      rw [hstep, hout]
      exact ⟨by simp only; omega, hs₃, hl₃⟩

/-- **The logged main loop runs the search**: from the state of the trail `t` and the log `log`,
if the run of `k` steps from `t` ends with the answer `a`, the loop writes at `T + 4 N` the output
of `a` and of the log extended by the words of the run. -/
theorem mainLoopLog_spec (φ : CNF ℕ) (N T : ℕ) :
    ∀ (k : ℕ) (t : Trail) (log : List ℕ) (x : Data 32) (a : Trail.Answer), StateAt φ N T x t →
      LogAt N T x log → Fits w (T + 5 * N + 3 + log.length + k) → Trail.run φ k t = some a →
      ∃ y, ExecWithin w mainLoopLog x y
          (k * (60 * (φ.flatMap encodeClause).length + 78) + 10 * N + 2) ∧
        y.regs out = T + 4 * N ∧
        outputList y.mem (T + 4 * N) = answerLog N a (log ++ Trail.runLog φ (logOut φ) k t)
  | 0, _, _, _, _, _, _, _, h => by simp [Trail.run] at h
  | k + 1, t, log, x, a, hs, hl, hfit, h => by
    obtain ⟨-, h1, -, -, -, -, -, -, hgo, -, hmem⟩ := id hs
    have hc : (Cond.eq go one).Holds x := by simp [Cond.holds_eq, hgo, h1]
    have hlenL : t.length ≤ (φ.flatMap encodeClause).length :=
      hmem.ok.length_le_vars.trans (length_vars_le φ)
    have hlo := length_logOut_le φ (Trail.lits t)
    obtain ⟨y, hy, hys⟩ := stepBodyLog_spec (w := w) φ N T t log x hs hl (hfit.of_le (by omega))
    unfold Trail.run at h
    unfold stepTimeLog stepTime at hy
    rw [Trail.runLog]
    split at h
    · rename_i a' hst
      cases h
      rw [hst] at hys hy
      obtain ⟨hgo', hout, hlist⟩ := hys
      have hone : y.regs one = 1 := (hy.regs_eq (by decide)).trans h1
      have hx : ¬(Cond.eq go one).Holds y := by simp [Cond.holds_eq, hgo', hone]
      exact ⟨y, (ExecWithin.loop_iter hc hy (ExecWithin.loop_exit hx)).mono (by nlinarith),
        hout, by simpa [hst] using hlist⟩
    · rename_i t' hst
      rw [hst] at hys hy
      obtain ⟨hs', hl'⟩ := hys
      obtain ⟨z, hz, hzo, hzl⟩ := mainLoopLog_spec φ N T k t' _ y a hs' hl'
        (hfit.of_le (by simp only [List.length_append]; omega)) h
      exact ⟨z, (ExecWithin.loop_iter hc hy hz).mono (by nlinarith),
        hzo, by simpa [hst] using hzl⟩

/-- The run of the search, `nodes` steps long, ends with the answer of the search, and its log is
the output of the variant. -/
private theorem run_nodes (N : ℕ) (φ : CNF ℕ) :
    Trail.run φ (Trail.nodes φ (depth φ) []) [] = some (Trail.answer φ) ∧
      answerLog N (Trail.answer φ) (Trail.runLog φ (logOut φ) (Trail.nodes φ (depth φ) []) []) =
        refutationWords N φ := by
  have hlen : (openVars φ (Trail.lits [])).length ≤ depth φ := by
    simp [Trail.lits, openVars_nil, depth]
  have hrun := Trail.run_add_nodes φ (depth φ) [] 0 hlen
  simp only [Nat.zero_add, Trail.lits_nil] at hrun
  unfold Trail.answer refutationWords
  cases hd : dfs φ (depth φ) [] with
  | some π =>
    rw [hd] at hrun
    have hs : solve φ = .sat (assignment π) := solve_eq_sat_iff_dfs.2 ⟨π, hd, rfl⟩
    refine ⟨hrun, ?_⟩
    simpa [answerLog, answerList, Trail.answer, hd, hs] using answerList_answer N φ
  | none =>
    rw [hd] at hrun
    have hs : (solve φ).isSat = false := by simp [isSat_solve_eq_isSome_dfs, hd]
    have hlog := Trail.runLog_add_nodes φ (logOut φ) (depth φ) [] 0 hlen hd
    simp only [Nat.zero_add, Trail.lits_nil] at hlog
    cases hsol : solve φ with
    | sat σ => exact Bool.noConfusion (hsol ▸ hs)
    | unsat c =>
      exact ⟨hrun, by simp [hlog, answerLog, answerWords, hsol, treeWords, Trail.backtrack]⟩

/-- **The variant on the word RAM** ends with the output `refutationWords N φ` at the address in
`out`. -/
theorem solverLog_spec (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N)
    (hfit : Fits w ((encode N φ).length + 5 * N + 3 + 2 ^ (depth φ + 1))) :
    ∃ y, ExecWithin w solverLog (Data.init (encode N φ)) y
        (2 ^ (depth φ + 1) * (60 * (encode N φ).length + 78) + 10 * N + 14) ∧
      y.regs out = (encode N φ).length + 1 + 4 * N ∧
      outputList y.mem (y.regs out) = refutationWords N φ := by
  have hLF : (encode N φ).length = 1 + (φ.flatMap encodeClause).length := Nat.add_comm _ 1
  have hnodes := Trail.nodes_lt φ (depth φ) []
  have hfit' : Fits w
      ((encode N φ).length + 1 + 5 * N + 3 + ([] : List ℕ).length + Trail.nodes φ (depth φ) []) :=
    hfit.of_le (by simp only [List.length_nil]; omega)
  have hm1 : (Data.init (encode N φ) : Data 32).mem 1 = N := by
    rw [Data.init_mem_succ]; rfl
  obtain ⟨hrun, hwords⟩ := run_nodes N φ
  refine WP.exists_execWithin ?_
  unfold solverLog setup
  wram_exec [Data.init_regs, Data.init_mem_zero, hm1]
  wram_call (mainLoopLog_spec φ N ((encode N φ).length + 1) _ [] [] _ (Trail.answer φ) ..)
    framed [memAt_init N φ hN, Data.init_regs, List.length_nil, holdsList_nil] with v m ⟨ho, hl⟩
  refine ⟨?_, by omega, by rw [ho, hl, List.nil_append, hwords]⟩
  have : Trail.nodes φ (depth φ) [] * (60 * (φ.flatMap encodeClause).length + 78) ≤
      2 ^ (depth φ + 1) * (60 * (encode N φ).length + 78) :=
    Nat.mul_le_mul hnodes.le (by omega)
  omega

end Specs

/-! ### The program -/

private theorem two_le_of_mem_treeWords {φ : CNF ℕ} {a : ℕ} (h : a ∈ treeWords φ) : 2 ≤ a := by
  obtain ⟨π, hπ⟩ := exists_mem_of_mem_preorder φ (logOut φ) _ _ h
  unfold logOut at hπ
  split at hπ <;> simp [clauseAddr] at hπ <;> omega

private theorem length_treeWords_lt (φ : CNF ℕ) : (treeWords φ).length < 2 ^ (depth φ + 1) :=
  (length_preorder_le φ (logOut φ) (length_logOut_le φ) _ _).trans_lt (Trail.nodes_lt φ _ _)

private theorem length_refutationWords_le (N : ℕ) (φ : CNF ℕ) :
    (refutationWords N φ).length ≤ N + 2 ^ (depth φ + 1) := by
  have := length_treeWords_lt φ
  unfold refutationWords answerWords
  cases solve φ <;> simp <;> omega

/-- **The DPLL solver writing its search tree, on the word RAM.** At any word size `w` that fits
`E + 5 N + 3 + 2 ^ (d + 1)`, the program run on the input `encode N φ` of length `E`, where every
variable of `φ` is below `N` and `d = Cslib.Algorithms.Lean.DPLL.depth φ` is the number of
distinct variables of `φ`, returns `refutationWords N φ`: the output of
`Cslib.Algorithms.Lean.DPLL.solve` as in `Cslib.Algorithms.WordRAM.DPLL.program_spec`, followed
for an unsatisfiable formula by the words of the search tree. It halts within
`2 ^ (d + 1) (60 E + 78) + 10 N + 15` instructions, the final halt included. -/
theorem programLog_spec (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 5 * N + 3 + 2 ^ (depth φ + 1))) :
    ∃ n ≤ 2 ^ (depth φ + 1) * (60 * (encode N φ).length + 78) + 10 * N + 15,
      ExecutesList w programLog (State.init (encode N φ)) (refutationWords N φ) n := by
  obtain ⟨y, ⟨n, hn, he⟩, hyo, hyl⟩ := solverLog_spec N φ hN hfit
  have hlen := length_refutationWords_le N φ
  exact ⟨n + 1, by omega,
    hyl ▸ he.executesList out (by rw [hyl, hyo]; exact hfit.of_le (by omega))⟩

/-- **The variant takes an instruction per leaf of the search tree**: on an unsatisfiable
formula, every halting run of the program on `encode N φ` takes at least as many instructions as
the tree explored by the search has leaves. Each leaf and each branching of the tree is a word of
the output, written to a cell above the input, which starts at `0`; each such cell costs a store
(`Cslib.WordRAM.Runs.block_lowerBound`). -/
theorem leafCount_searchTree_le_of_executes (N : ℕ) (φ : CNF ℕ)
    (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) (hφ : ¬ φ.Satisfiable) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 5 * N + 3 + 2 ^ (depth φ + 1))) {v n : ℕ}
    (h : Executes w programLog (State.init (encode N φ)) v n) :
    (searchTree φ (depth φ) []).leafCount ≤ n := by
  obtain ⟨y, ⟨n', -, he⟩, hyo, hyl⟩ := solverLog_spec N φ hN hfit
  set L := (encode N φ).length
  -- the run is the one of the specification
  have hrun := he.runs (pc := 0) (p := solverLog.program out) (Program.Contains.self _).append_left
  have hex := (he.executesList out (by
    rw [hyl, hyo]; exact hfit.of_le (by have := length_refutationWords_le N φ; omega))).executes
  obtain ⟨v', hv'⟩ := hex
  obtain ⟨-, rfl⟩ := hv'.unique h
  -- the words of the tree are in the output
  cases hc : solve φ with
  | sat σ => exact absurd ⟨σ, solve_sat hc⟩ hφ
  | unsat c =>
  have hout : outputList y.mem (L + 1 + 4 * N) = 0 :: treeWords φ := by
    simpa [← hyo, refutationWords, answerWords, hc] using hyl
  obtain ⟨-, -, htree⟩ : _ ∧ _ ∧ HoldsList (L + 1 + 4 * N + 1 + 1) (treeWords φ) y.mem := by
    simpa [outputList_eq_iff, holdsList_cons_iff] using hout
  have hb := hrun.block_lowerBound ⟨L + 1 + 4 * N + 1 + 1, (treeWords φ).length⟩ fun i => by
    simp only
    rw [htree.get i i.isLt, Data.init_mem_of_length_lt (by omega)]
    have := two_le_of_mem_treeWords (List.getElem_mem i.isLt)
    omega
  have hleaf := leafCount_searchTree_le_length_preorder φ (logOut φ)
    (fun π hπ => by unfold logOut; cases hs : status φ π <;> simp_all) (depth φ) []
    (by simp [openVars_nil, depth]) (dfs_eq_none_of_not_satisfiable hφ)
  dsimp only [treeWords] at hb
  omega

/-- **The running time in the form `c · 2 ^ N · E`**: the variant halts within `301 · 2 ^ N · E`
instructions on the input `encode N φ` of length `E`. -/
theorem programLog_spec_pow (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 5 * N + 3 + 2 ^ (N + 1))) :
    ∃ n ≤ 301 * 2 ^ N * (encode N φ).length,
      ExecutesList w programLog (State.init (encode N φ)) (refutationWords N φ) n := by
  have hd : 2 ^ (depth φ + 1) ≤ 2 ^ (N + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := depth_le hN; omega)
  obtain ⟨n, hn, he⟩ := programLog_spec N φ hN (hfit.of_le (by omega))
  refine ⟨n, hn.trans ?_, he⟩
  set E := (encode N φ).length
  have hE : 1 ≤ E := by simp [E, encode]
  have hd' : 2 ^ (depth φ + 1) ≤ 2 * 2 ^ N := by rw [Nat.pow_succ] at hd; omega
  linarith [Nat.mul_le_mul_right (60 * E + 78) hd', Nat.mul_le_mul_left (2 ^ N) hE,
    Nat.one_le_two_pow (n := N), Nat.lt_two_pow_self (n := N)]

/-- **The variant takes `2 ^ Ω(n log n)` instructions on the pigeonhole formulas.** For `m > n`, an
injective map `f` numbering the variables of `PHP^m_n` below `N`, and a word size `w` that fits
`E + 5 N + 3 + 2 ^ (N + 1)`, where `E` is the length of the input `encode N φ` of the renamed
formula `φ`, the variant returns `refutationWords N φ`, `0` followed by the words of its search
tree, within `301 · 2 ^ N · E` instructions, and every halting run of it on that input takes at
least `(n / 2 + 1) ^ (n / 2)` instructions. The lower bound is that of
[BeyersdorffGalesiLauria2010, Theorem 2] on the leaves of every tree-like refutation of
`PHP^m_n`: the search tree is one with at most as many leaves, and each of its leaves costs a store
(`Cslib.Algorithms.WordRAM.DPLL.leafCount_searchTree_le_of_executes`). -/
theorem programLog_pigeonhole {m n : ℕ} {f : Fin m × Fin n → ℕ} (hf : Function.Injective f)
    (hnm : n < m) (N : ℕ) (hN : ∀ c ∈ (pigeonhole m n).relabel f, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N ((pigeonhole m n).relabel f)).length + 5 * N + 3 + 2 ^ (N + 1))) :
    (∃ k ≤ 301 * 2 ^ N * (encode N ((pigeonhole m n).relabel f)).length,
        ExecutesList w programLog (State.init (encode N ((pigeonhole m n).relabel f)))
          (refutationWords N ((pigeonhole m n).relabel f)) k) ∧
      ∀ v k, Executes w programLog (State.init (encode N ((pigeonhole m n).relabel f))) v k →
        (n / 2 + 1) ^ (n / 2) ≤ k := by
  refine ⟨programLog_spec_pow N _ hN hfit, fun v k h => ?_⟩
  have hd : 2 ^ (depth ((pigeonhole m n).relabel f) + 1) ≤ 2 ^ (N + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := depth_le hN; omega)
  exact (pow_half_le_leafCount_searchTree_pigeonhole hf hnm).trans
    (leafCount_searchTree_le_of_executes N _ hN
      (by rw [satisfiable_relabel hf]; exact not_satisfiable_pigeonhole hnm)
      (hfit.of_le (by omega)) h)

end Cslib.Algorithms.WordRAM.DPLL

end
