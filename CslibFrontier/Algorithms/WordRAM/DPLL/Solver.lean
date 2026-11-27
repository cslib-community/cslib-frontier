/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Steps
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop

/-!
# The DPLL solver on the word RAM: correctness and running time

This file proves the main theorem about the word-RAM DPLL solver
(`Cslib.Algorithms.WordRAM.DPLL.program`). On the input `encode N φ` of length `E`, where every
variable of `φ` is below `N`, it returns the output of `Cslib.Algorithms.Lean.DPLL.solve`
(`Cslib.Algorithms.WordRAM.DPLL.answerWords`): `[0]` when `φ` is unsatisfiable, and `1` followed by
the bits of the solver's model otherwise. It halts within
`2 ^ (d + 1) (37 E + 62) + 10 N + 14` instructions, where `d` is the number of distinct
variables of `φ` (`Cslib.Algorithms.WordRAM.DPLL.program_spec`), and so within `222 · 2 ^ N · E`
(`Cslib.Algorithms.WordRAM.DPLL.program_spec_pow`).

Each iteration of the main loop runs one step of the search with an explicit trail
(`Cslib.Algorithms.Lean.DPLL.Trail.step`) in `O(E)` instructions, and the search ends within
`2 ^ (d + 1)` steps (`Cslib.Algorithms.Lean.DPLL.Trail.run_answer`). The term `10 N` is charged
once, on the exit that writes a model: it writes one word for each of the `N` variables. It is
not covered by the `O(E)` cost of a step, because the header `N` is only an upper bound on the
variables and can exceed the input length `E`.

## Main results

* `Cslib.Algorithms.WordRAM.DPLL.mainLoop_spec`: the main loop runs the search.
* `Cslib.Algorithms.WordRAM.DPLL.program_spec`, `Cslib.Algorithms.WordRAM.DPLL.program_spec_pow`:
  correctness and the instruction bounds.
-/

public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Algorithms.WordRAM.ClauseCode Cslib.Algorithms.Lean.DPLL Reg

section Specs

variable {w : ℕ}

attribute [local wram_simps] StateAt

/-- **The main loop runs the search**: from the state of the trail `t`, if the run of `k` steps
from `t` ends with the answer `a`, the loop writes the output of `a` at `T + 4 N`. -/
theorem mainLoop_spec (φ : CNF ℕ) (N T : ℕ) (hfit : Fits w (T + 5 * N + 2)) :
    ∀ (k : ℕ) (t : Trail) (x : Data 32) (a : Trail.Answer), StateAt φ N T x t →
      Trail.run φ k t = some a →
      ∃ y, ExecWithin w mainLoop x y
          (k * (37 * (φ.flatMap encodeClause).length + 62) + 10 * N + 2) ∧
        y.regs out = T + 4 * N ∧ outputList y.mem (T + 4 * N) = answerList N a
  | 0, _, _, _, _, h => by simp [Trail.run] at h
  | k + 1, t, x, a, hs, h => by
    obtain ⟨-, h1, -, -, -, -, -, -, hgo, -, hmem⟩ := id hs
    have hc : (Cond.eq go one).Holds x := by simp [Cond.holds_eq, hgo, h1]
    have hlenL : t.length ≤ (φ.flatMap encodeClause).length :=
      hmem.ok.length_le_vars.trans (length_vars_le φ)
    obtain ⟨y, hy, hys⟩ := stepBody_spec (w := w) φ N T t x hs hfit
    unfold Trail.run at h
    unfold stepTime at hy
    split at h
    · rename_i a' hst
      cases h
      rw [hst] at hys hy
      obtain ⟨hgo', hout, hlist⟩ := hys
      have hone : y.regs one = 1 := (hy.regs_eq (by decide)).trans h1
      have hx : ¬(Cond.eq go one).Holds y := by simp [Cond.holds_eq, hgo', hone]
      refine ⟨y, (ExecWithin.loop_iter hc hy (ExecWithin.loop_exit hx)).mono ?_, hout, hlist⟩
      simp only [Nat.add_one_mul]; omega
    · rename_i t' hst
      rw [hst] at hys hy
      obtain ⟨z, hz, hzo, hzl⟩ := mainLoop_spec φ N T hfit k t' y a hys h
      refine ⟨z, (ExecWithin.loop_iter hc hy hz).mono ?_, hzo, hzl⟩
      simp only [Nat.add_one_mul]; omega

theorem answerList_answer (N : ℕ) (φ : CNF ℕ) :
    answerList N (Trail.answer φ) = answerWords N φ := by
  unfold Trail.answer answerWords
  cases hd : dfs φ (depth φ) [] with
  | some π =>
    rw [(solve_eq_sat_iff_dfs (σ := assignment π)).2 ⟨π, hd, rfl⟩]
    rfl
  | none =>
    cases hs : solve φ with
    | sat σ =>
      obtain ⟨π, hπ, -⟩ := solve_eq_sat_iff_dfs.1 hs
      simp [hd] at hπ
    | unsat _ => rfl

/-- The memory of the input `encode N φ` of length `E` is that of the empty trail, with the end of
the clauses at `T = E + 1`. -/
theorem memAt_init (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) :
    MemAt φ N ((encode N φ).length + 1) (Data.init (encode N φ) : Data 32).mem [] := by
  have hlen : (encode N φ).length = 1 + (φ.flatMap encodeClause).length := by
    simp [encode]; omega
  have hF : HoldsList 2 (φ.flatMap encodeClause) (Data.init (encode N φ) : Data 32).mem := by
    have h := Data.init_realizes_append (r := 32) [N] (φ.flatMap encodeClause) []
    rw [List.length_singleton, List.append_nil, List.singleton_append] at h
    exact h
  exact ⟨hF, by omega, hN,
    fun l hl => by rw [Data.init_mem_of_length_lt (by omega)]; simp [Trail.lits],
    holdsList_nil _ _, by simp [TrailOK]⟩

/-- **The solver on the word RAM** ends with the output `answerWords N φ` at the address in
`out`. -/
theorem solver_spec (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N)
    (hfit : Fits w ((encode N φ).length + 5 * N + 3)) :
    ∃ y, ExecWithin w solver (Data.init (encode N φ)) y
        (2 ^ (depth φ + 1) * (37 * (encode N φ).length + 62) + 10 * N + 13) ∧
      y.regs out = (encode N φ).length + 1 + 4 * N ∧
      outputList y.mem (y.regs out) = answerWords N φ := by
  set input := encode N φ with hinput
  obtain ⟨L, hL⟩ : ∃ L, L = input.length := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = L + 1 := ⟨_, rfl⟩
  have hinputeq : input = N :: φ.flatMap encodeClause := rfl
  have hLF : L = 1 + (φ.flatMap encodeClause).length := by simp [hL, hinputeq]; omega
  rw [← hL] at hfit ⊢
  have hfit' : Fits w (T + 5 * N + 2) := hfit.of_le (by omega)
  have hm0 : (Data.init input : Data 32).mem 0 = L := hL ▸ Data.init_mem_zero input
  have hm1 : (Data.init input : Data 32).mem 1 = N := by simp [Data.init_mem_succ, hinputeq]
  have hmem : MemAt φ N T (Data.init input : Data 32).mem [] := hT ▸ hL ▸ memAt_init N φ hN
  obtain ⟨k, hk, hrun⟩ := Trail.run_answer φ
  refine WP.exists_execWithin ?_
  unfold solver setup
  wram_exec [Data.init_regs, hm0, hm1]
  wram_call (mainLoop_spec φ N T hfit' k [] _ (Trail.answer φ) ..) framed
    [hmem, Data.init_regs, List.length_nil] with v m ⟨ho, hl⟩
  refine ⟨?_, by omega, by rw [ho, hl, answerList_answer]⟩
  have := Nat.mul_le_mul hk (by omega : 37 * (φ.flatMap encodeClause).length + 62 ≤ 37 * L + 62)
  omega

end Specs

theorem length_answerWords_le (N : ℕ) (φ : CNF ℕ) : (answerWords N φ).length ≤ N + 1 := by
  unfold answerWords
  split <;> simp

/-- **The DPLL solver on the word RAM.** At any word size `w` that fits `E + 5 N + 3`, the program
run on the input `encode N φ` of length `E`, where every variable of `φ` is below `N`, returns the
output of `Cslib.Algorithms.Lean.DPLL.solve`: `[0]` when `φ` is unsatisfiable, and `1` followed by
the bits of the solver's model on the variables below `N` otherwise. It halts within
`2 ^ (d + 1) (37 E + 62) + 10 N + 14` instructions, the final halt included, where
`d = Cslib.Algorithms.Lean.DPLL.depth φ` is the number of distinct variables of `φ`. -/
theorem program_spec (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 5 * N + 3)) :
    ∃ n ≤ 2 ^ (depth φ + 1) * (37 * (encode N φ).length + 62) + 10 * N + 14,
      ExecutesList w program (State.init (encode N φ)) (answerWords N φ) n := by
  obtain ⟨y, ⟨n, hn, he⟩, hyo, hyl⟩ := solver_spec N φ hN hfit
  have hlen := length_answerWords_le N φ
  exact ⟨n + 1, by omega,
    hyl ▸ he.executesList out (by rw [hyl, hyo]; exact hfit.of_le (by omega))⟩

theorem depth_le {N : ℕ} {φ : CNF ℕ} (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) : depth φ ≤ N := by
  have := ((List.nodup_eraseDups φ.vars).subperm (l₂ := List.range N) fun v hv => by
    obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.1 (List.mem_eraseDups.1 hv)
    exact List.mem_range.2 (hN c hc _ hl)).length_le
  simpa [depth] using this

/-- **The running time in the form `c · 2 ^ N · E`**: the program halts within
`222 · 2 ^ N · E` instructions on the input `encode N φ` of length `E`. -/
theorem program_spec_pow (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 5 * N + 3)) :
    ∃ n ≤ 222 * 2 ^ N * (encode N φ).length,
      ExecutesList w program (State.init (encode N φ)) (answerWords N φ) n := by
  obtain ⟨n, hn, he⟩ := program_spec N φ hN hfit
  refine ⟨n, hn.trans ?_, he⟩
  set E := (encode N φ).length
  have hE : 1 ≤ E := by simp [E, encode]
  have hd : 2 ^ (depth φ + 1) ≤ 2 * 2 ^ N := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (depth_le hN))
  have h₁ : 2 ^ (depth φ + 1) * (37 * E + 62) ≤ 198 * (2 ^ N * E) :=
    (Nat.mul_le_mul hd (by omega : 37 * E + 62 ≤ 99 * E)).trans_eq (by ring)
  have hNE : 2 ^ N ≤ 2 ^ N * E := Nat.le_mul_of_pos_right _ hE
  have hNp : N < 2 ^ N := Nat.lt_two_pow_self
  have h1 : 1 ≤ 2 ^ N * E := Nat.mul_pos Nat.one_le_two_pow hE
  have : 222 * 2 ^ N * E = 222 * (2 ^ N * E) := by ring
  omega

end Cslib.Algorithms.WordRAM.DPLL

end
