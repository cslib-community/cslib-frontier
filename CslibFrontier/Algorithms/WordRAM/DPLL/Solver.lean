/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DPLL.Steps
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# The DPLL solver on the word RAM: correctness and running time

This file proves the main theorem about the word-RAM DPLL solver
(`Cslib.Algorithms.WordRAM.DPLL.program`). On the input `encode N φ` of length `E`, where every
variable of `φ` is below `N`, it returns the output of `Cslib.Algorithms.Lean.DPLL.solve`
(`Cslib.Algorithms.WordRAM.DPLL.answerWords`): `[0]` when `φ` is unsatisfiable, and `1` followed by
the bits of the solver's model otherwise. It halts within
`2 ^ (d + 1) (46 E + 64) + 10 N + 8 E + 21` instructions, where `d` is the number of distinct
variables of `φ` (`Cslib.Algorithms.WordRAM.DPLL.program_spec`), and so within `260 · 2 ^ N · E`
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

/-- **The main loop runs the search**: from the state of the trail `t`, if the run of `k` steps
from `t` ends with the answer `a`, the loop writes the output of `a` at `T + 5 N`. -/
theorem mainLoop_spec (φ : CNF ℕ) (N T : ℕ) (hfit : Fits w (T + 6 * N + 2)) :
    ∀ (k : ℕ) (t : Trail) (x : Data 32) (a : Trail.Answer), StateAt φ N T x t →
      Trail.run φ k t = some a →
      ∃ y, ExecWithin w mainLoop x y
          (k * (46 * (φ.flatMap encodeClause).length + 64) + 10 * N + 4) ∧
        y.regs out = T + 5 * N ∧ outputList y.mem (T + 5 * N) = answerList N a
  | 0, _, _, _, _, h => by simp [Trail.run] at h
  | k + 1, t, x, a, hs, h => by
    have hc : (Cond.eq go one).Holds x := by simp [Cond.holds_eq, hs.go, hs.one]
    have hlenL : t.length ≤ (φ.flatMap encodeClause).length :=
      hs.mem.ok.length_le_vars.trans (length_vars_le φ)
    obtain ⟨y, hy, hys⟩ := stepBody_spec (w := w) φ N T t x hs hfit
    unfold Trail.run at h
    unfold stepTime at hy
    split at h
    · rename_i a' hst
      cases h
      rw [hst] at hys hy
      obtain ⟨hgo, hout, hlist⟩ := hys
      have hone : y.regs one = 1 := (hy.regs_eq (by decide)).trans hs.one
      have hx : ¬ (Cond.eq go one).Holds y := by simp [Cond.holds_eq, hgo, hone]
      refine ⟨y, (ExecWithin.loop_iter hc hy (ExecWithin.loop_exit hx)).mono ?_, hout, hlist⟩
      simp only
      nlinarith
    · rename_i t' hst
      rw [hst] at hys hy
      obtain ⟨z, hz, hzo, hzl⟩ := mainLoop_spec φ N T hfit k t' y a hys h
      refine ⟨z, (ExecWithin.loop_iter hc hy hz).mono ?_, hzo, hzl⟩
      simp only
      nlinarith

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

/-- **The solver on the word RAM** ends with the output `answerWords N φ` at the address in
`out`. -/
theorem solver_spec (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N)
    (hfit : Fits w ((encode N φ).length + 6 * N + 3)) :
    ∃ y, ExecWithin w solver (Data.init (encode N φ)) y
        (2 ^ (depth φ + 1) * (46 * (encode N φ).length + 64) + 10 * N +
          8 * (encode N φ).length + 20) ∧
      y.regs out = (encode N φ).length + 1 + 5 * N ∧
      outputList y.mem (y.regs out) = answerWords N φ := by
  set input := encode N φ with hinput
  set L := input.length
  set T := L + 1
  set F := φ.flatMap encodeClause
  have hinputeq : input = N :: F := rfl
  have hL : L = 1 + F.length := by simp [L, hinputeq]; omega
  have hLdef : input.length = L := rfl
  have hFdef : (φ.flatMap encodeClause).length = F.length := rfl
  have hfit' : Fits w (T + 6 * N + 2) := hfit.of_le (by omega)
  have hzeroT : ∀ a, T ≤ a → (Data.init input : Data 32).mem a = 0 := fun a ha => by
    change (if a = 0 then L else input.getD (a - 1) 0) = 0
    simp only [show ¬ a = 0 by omega, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have hF : HoldsList 2 F (Data.init input : Data 32).mem := fun i => by
    change (Data.init input : Data 32).mem (2 + i.val) = F[i.val]
    rw [show 2 + i.val = (1 + i.val) + 1 by omega, Data.init_mem_succ]
    simp only [hinputeq, Nat.add_comm 1 i.val, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
    rfl
  have hm1 : (Data.init input : Data 32).mem 1 = N := by
    rw [Data.init_mem_succ]; simp [hinputeq]
  have : Fits w 1 := hfit'.of_le (by omega)
  have : Fits w 2 := hfit'.of_le (by omega)
  have : Fits w L := hfit'.of_le (by omega)
  have : Fits w (L + 1) := hfit'.of_le (by omega)
  have : Fits w N := hfit'.of_le (by omega)
  have : Fits w (N + N) := hfit'.of_le (by omega)
  have : Fits w (L + 1 + (N + N)) := hfit'.of_le (by omega)
  have : Fits w (L + 1 + (N + N) + N) := hfit'.of_le (by omega)
  have : Fits w (L + 1 + (N + N) + N + (N + N)) := hfit'.of_le (by omega)
  obtain ⟨k, hk, hrun⟩ := Trail.run_answer φ
  refine WP.exists_execWithin ?_
  unfold solver setup
  wram_exec [Data.init_regs, Data.init_mem_zero, hm1]
  refine WP.name fun x₁ hx₁ => ?_
  obtain ⟨x₂, hx₂, hm₂⟩ := lastPass_spec (w := w) φ x₁ N (by subst hx₁; wram_simp)
    (by subst hx₁; wram_simp) (by subst hx₁; wram_simp; exact hF)
    (by subst hx₁; wram_simp; omega) hN (by subst hx₁; wram_simp; omega)
    (by subst hx₁; wram_simp; exact hfit'.of_le (by omega)) (hfit'.of_le (by omega))
  refine WP.of_execWithin hx₂ ?_
  have hr : ∀ r ∈ ({Reg.zero, Reg.one, Reg.two, Reg.tb, Reg.cend, Reg.lb, Reg.sb, Reg.ob,
      Reg.nv, Reg.go, Reg.tp} : Finset (Fin 32)), lastPass.Preserves r := by decide
  have hm₁ : x₁.mem = (Data.init input : Data 32).mem := by subst hx₁; wram_simp
  have hlb₁ : x₁.regs lb = T + 2 * N := by subst hx₁; wram_simp; omega
  rw [hm₁, hlb₁] at hm₂
  have hs : StateAt φ N T x₂ [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals
      first
      | (rw [hx₂.regs_eq (hr _ (by decide))]; subst hx₁; wram_simp [Data.init_regs]; done)
      | (rw [hx₂.regs_eq (hr _ (by decide))]; subst hx₁; wram_simp [Data.init_regs]; omega)
      | (rw [hx₂.regs_eq (hr _ (by decide))]; subst hx₁; simp only [List.length_nil];
          wram_simp [Data.init_regs]; omega)
    rw [hm₂]
    refine ⟨hF.frame fun a _ ha => writeLast_of_lt _ _ _ (by omega), by omega, hN,
      fun l hl => ?_, fun v hv => ?_, holdsList_nil _ _, by simp [TrailOK]⟩
    · have := litCode_lt hl
      rw [writeLast_of_lt _ _ _ (by omega), hzeroT _ (by omega)]
      simp [Trail.lits]
    · rw [writeLast_cell, hzeroT _ (by omega)]
  obtain ⟨y, hy, hyo, hyl⟩ := mainLoop_spec φ N T hfit' k [] x₂ (Trail.answer φ) hs hrun
  refine WP.of_execWithin hy ⟨?_, hyo, by rw [hyo, hyl, answerList_answer]⟩
  have : k * (46 * F.length + 64) ≤ 2 ^ (depth φ + 1) * (46 * L + 64) :=
    Nat.mul_le_mul hk (by omega)
  rw [hFdef]
  omega

end Specs

theorem length_answerWords_le (N : ℕ) (φ : CNF ℕ) : (answerWords N φ).length ≤ N + 1 := by
  unfold answerWords
  split <;> simp

/-- **The DPLL solver on the word RAM.** At any word size `w` that fits `E + 6 N + 3`, the program
run on the input `encode N φ` of length `E`, where every variable of `φ` is below `N`, returns the
output of `Cslib.Algorithms.Lean.DPLL.solve`: `[0]` when `φ` is unsatisfiable, and `1` followed by
the bits of the solver's model on the variables below `N` otherwise. It halts within
`2 ^ (d + 1) (46 E + 64) + 10 N + 8 E + 21` instructions, the final halt included, where
`d = Cslib.Algorithms.Lean.DPLL.depth φ` is the number of distinct variables of `φ`. -/
theorem program_spec (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 6 * N + 3)) :
    ∃ n ≤ 2 ^ (depth φ + 1) * (46 * (encode N φ).length + 64) + 10 * N +
        8 * (encode N φ).length + 21,
      ExecutesList w program (State.init (encode N φ)) (answerWords N φ) n := by
  obtain ⟨y, ⟨n, hn, he⟩, hyo, hyl⟩ := solver_spec N φ hN hfit
  have hlen := length_answerWords_le N φ
  refine ⟨n + 1, by omega, ?_⟩
  have := he.executesList out (by rw [hyl, hyo]; exact hfit.of_le (by omega))
  rw [hyl] at this
  exact this

theorem depth_le {N : ℕ} {φ : CNF ℕ} (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) : depth φ ≤ N := by
  have := ((List.nodup_dedup φ.vars).subperm (l₂ := List.range N) fun v hv => by
    obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.1 (List.mem_dedup.1 hv)
    exact List.mem_range.2 (hN c hc _ hl)).length_le
  simpa [depth] using this

/-- **The running time in the form `c · 2 ^ N · E`**: the program halts within
`260 · 2 ^ N · E` instructions on the input `encode N φ` of length `E`. -/
theorem program_spec_pow (N : ℕ) (φ : CNF ℕ) (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) {w : ℕ}
    (hfit : Fits w ((encode N φ).length + 6 * N + 3)) :
    ∃ n ≤ 260 * 2 ^ N * (encode N φ).length,
      ExecutesList w program (State.init (encode N φ)) (answerWords N φ) n := by
  obtain ⟨n, hn, he⟩ := program_spec N φ hN hfit
  refine ⟨n, hn.trans ?_, he⟩
  set E := (encode N φ).length
  have hE : 1 ≤ E := by simp [E, encode]
  have hd : 2 ^ (depth φ + 1) ≤ 2 * 2 ^ N := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (depth_le hN))
  have hp : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have hNp : N < 2 ^ N := Nat.lt_two_pow_self
  have h₁ : 2 ^ (depth φ + 1) * (46 * E + 64) ≤ 2 * 2 ^ N * (110 * E) :=
    Nat.mul_le_mul hd (by omega)
  have h₂ : 10 * N ≤ 10 * (2 ^ N * E) := by
    have : 2 ^ N ≤ 2 ^ N * E := Nat.le_mul_of_pos_right _ hE
    omega
  have h₃ : 8 * E + 21 ≤ 29 * (2 ^ N * E) := by
    have : E ≤ 2 ^ N * E := Nat.le_mul_of_pos_left _ hp
    omega
  have : 2 * 2 ^ N * (110 * E) = 220 * (2 ^ N * E) := by ring
  have : 260 * 2 ^ N * E = 260 * (2 ^ N * E) := by ring
  omega


end Cslib.Algorithms.WordRAM.DPLL

end
