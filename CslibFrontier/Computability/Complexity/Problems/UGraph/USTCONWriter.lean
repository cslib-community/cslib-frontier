/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.UGraph
public import CslibFrontier.Computability.Complexity.Problems.USTCON
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Boolean
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output

/-!
# Writing instances of undirected connectivity from undirected graphs in logarithmic space

Many logarithmic-space reductions to undirected `s`–`t` connectivity build, from an undirected
graph `G` on `n` vertices, an instance on `N` vertices with source `0` and target `1` whose
adjacency matrix has entries of two kinds: an entry that copies one entry of the input matrix,
and an entry that is arithmetic in `n` and its row and column. The counter program
`Cslib.Complexity.UGraphInstance.ustconWriter` writes such an instance. It takes four expressions
over the registers `[n, r, c]`: the number of vertices `N`, a test whether the entry `(r, c)`
copies an input bit, the position of that bit in the encoded graph, and the arithmetic entry. It
counts the unary header `1^n 0` of the encoded graph, writes the header `1^N 0 0 1 0` of the
instance, and writes its matrix entry by entry. When `N` is polynomial in the length of the
encoded graph, the registers hold logarithmically many bits, and the instance is computed in
logarithmic space (`Cslib.Complexity.UGraphInstance.computableInLogSpace_of_entryExprs`).

## Main definitions

* `Cslib.Complexity.UGraphInstance.ustconWriter`: the counter program.

## Main results

* `Cslib.Complexity.UGraphInstance.computableInLogSpace_of_entryExprs`: an instance whose
  entries the four expressions describe is computed in logarithmic space.
-/

public section

namespace Cslib.Complexity

namespace UGraphInstance

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr _root_.Turing.MultiTapeTM

/-- **The writer** of an instance of undirected connectivity with source `0` and target `1`, on
the encoded graph. The expressions are evaluated on the registers `[n, r, c]`: `numV` is the
number of vertices of the instance; the entry `(r, c)` is the input bit at `position` when
`within` is positive, and otherwise whether `endpoint` is positive. Register `0` receives `n`,
register `1` counts the unary header and then runs over the rows, register `2` over the columns.
Labels `0` and `1` count the header of the input; the loop at label `2` and labels `6` to `9`
write the header `1^N 0 0 1 0` of the instance; the nested loops at labels `10` and `13` write
the matrix, the entry at labels `16` to `20`; label `21` halts. -/
def ustconWriter (numV within position endpoint : Expr) : CounterProgram where
  code := List.flatten [
    [read (reg 0) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0],
    forCode 2 1 numV 5 6,
    [emit true 4, emit false 7, emit false 8, emit true 9, emit false 10],
    forCode 10 1 numV 13 21, forCode 13 2 numV 16 12,
    [lt (const 0) within 17 18,
     read position 19 20 20,
     lt (const 0) endpoint 19 20,
     emit true 15,
     emit false 15,
     halt []]]
  registers := 3

variable {numV within position endpoint : Expr} (G : UGraphInstance) {B : ℕ}

/-- The entry `(r, c)` that the writer emits. -/
private def entryOf (within position endpoint : Expr) (G : UGraphInstance) (r c : ℕ) : Bool :=
  if 0 < within.eval [G.n, r, c] then G.encode[position.eval [G.n, r, c]]?.getD false
  else decide (0 < endpoint.eval [G.n, r, c])

private theorem bounded3 {a₀ a₁ a₂ : ℕ} (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B) :
    ∀ x ∈ [a₀, a₁, a₂], x ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Writing the entry `(r, c)` of the matrix. -/
private theorem reachesOut_entry {r c : ℕ} (hb : ∀ z ∈ [G.n, r, c], z ≤ B) :
    (ustconWriter numV within position endpoint).ReachesOut G.encode
      ((ustconWriter numV within position endpoint).Active B) (16, [G.n, r, c])
      (15, [G.n, r, c]) [entryOf within position endpoint G r c] := by
  have hemit (b : Bool) (l : ℕ)
      (hl : (ustconWriter numV within position endpoint).instr l =
        if b then emit true 15 else emit false 15) :
      (ustconWriter numV within position endpoint).ReachesOut G.encode
        ((ustconWriter numV within position endpoint).Active B) (l, [G.n, r, c])
        (15, [G.n, r, c]) [b] := by
    cases b <;> exact ReachesOut.emit hl hb (.refl _)
  refine ReachesOut.lt rfl hb ?_
  rw [eval_const]
  by_cases hw : 0 < within.eval [G.n, r, c]
  · -- an entry that copies an input bit
    rw [ite_eq_left hw, entryOf, ite_eq_left hw]
    refine ReachesOut.read rfl hb ?_
    rcases G.encode[position.eval [G.n, r, c]]? with _ | _ | _
    · exact hemit false 20 rfl
    · exact hemit false 20 rfl
    · exact hemit true 19 rfl
  · -- an arithmetic entry
    rw [ite_eq_right hw, entryOf, ite_eq_right hw]
    refine ReachesOut.lt rfl hb ?_
    rw [eval_const]
    by_cases he : 0 < endpoint.eval [G.n, r, c]
    · rw [ite_eq_left he, decide_eq_true he]
      exact hemit true 19 rfl
    · rw [ite_eq_right he, decide_eq_false he]
      exact hemit false 20 rfl

/-- **The matrix row by row**, by the nested loops at labels `10` and `13`. -/
private theorem reachesOut_rows {N : ℕ} (hN : ∀ r c, numV.eval [G.n, r, c] = N) (hnB : G.n ≤ B)
    (hB : N ≤ B) {i₀ : ℕ} (hi₀ : i₀ ≤ B) :
    ∃ regs, (ustconWriter numV within position endpoint).ReachesOut G.encode
      ((ustconWriter numV within position endpoint).Active B) (10, [G.n, i₀, 0]) (21, regs)
      ((List.range N).flatMap fun r =>
        (List.range N).map (entryOf within position endpoint G r)) ∧ ∀ x ∈ regs, x ≤ B := by
  have hreg {r c : ℕ} (hr : r ≤ N) (hc : c ≤ N) := bounded3 hnB (hr.trans hB) (hc.trans hB)
  have hcode₁ : (ustconWriter numV within position endpoint).CodeAt 10 (forCode 10 1 numV 13 21) :=
    codeAt_of_prefix ⟨_, rfl⟩
  have hcode₂ : (ustconWriter numV within position endpoint).CodeAt 13 (forCode 13 2 numV 16 12) :=
    codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨regs, hreach, x, rfl, -, hx⟩ := reachesOut_forCode (w := G.encode)
    (N := N) (o := fun r => (List.range N).map (entryOf within position endpoint G r))
    hcode₁ (fun r regs => ∃ x, regs = [G.n, r, x] ∧ r ≤ N ∧ x ≤ N) hB
    (by
      rintro r _ ⟨x, rfl, hr, hx⟩
      exact ⟨rfl, hN r x, by simp, hreg hr hx⟩)
    (by
      rintro r hr _ ⟨x, rfl, -, hx⟩
      obtain ⟨_, hreach, rfl, -⟩ := reachesOut_forCode (w := G.encode)
        (N := N) (o := fun c => [entryOf within position endpoint G r c]) hcode₂
        (fun c regs => regs = [G.n, r, c] ∧ c ≤ N) hB
        (by
          rintro c _ ⟨rfl, hc⟩
          exact ⟨rfl, hN r c, by simp, hreg hr.le hc⟩)
        (by
          rintro c hc _ ⟨rfl, -⟩
          exact ⟨_, reachesOut_entry G (hreg hr.le hc.le), rfl, hreg hr.le hc.le,
            by simp, by omega⟩)
        [G.n, r, x] (hreg hr.le hx) ⟨by simp, Nat.zero_le _⟩
      rw [← List.map_eq_flatMap] at hreach
      exact ⟨_, hreach, rfl, hreg hr.le le_rfl, N, by simp, by omega, le_rfl⟩)
    [G.n, i₀, 0] (bounded3 hnB hi₀ (Nat.zero_le _)) ⟨0, by simp, Nat.zero_le _, Nat.zero_le _⟩
  exact ⟨_, hreach, hreg le_rfl hx⟩

/-- **Instances whose entries are input bits or arithmetic are computed in logarithmic space.**
Let `F` map undirected graphs to instances of undirected connectivity with source `0` and target
`1`, on at most `(m + 1) ^ k` vertices for encoded graphs of length `m`, and let the expressions
describe `F` over the registers `[n, r, c]`: `numV` evaluates to the number of vertices, and the
entry `(r, c)` is the bit of the encoded graph at `position` when `within` is positive, and
otherwise whether `endpoint` is positive. Then `ustconWriter numV within position endpoint`
computes `F` in logarithmic space. -/
theorem computableInLogSpace_of_entryExprs {F : UGraphInstance → USTCONInstance} (k : ℕ)
    (hN : ∀ G r c, numV.eval [G.n, r, c] = (F G).n)
    (hbound : ∀ G, (F G).n ≤ (G.encode.length + 1) ^ k)
    (hs : ∀ G, ((F G).s : ℕ) = 0) (ht : ∀ G, ((F G).t : ℕ) = 1)
    (hentry : ∀ G (r c : Fin (F G).n), (F G).adj r c =
      if 0 < within.eval [G.n, r, c] then G.encode[position.eval [G.n, r, c]]?.getD false
      else decide (0 < endpoint.eval [G.n, r, c])) :
    ComputableInLogSpace F encUGraph encUSTCON := by
  refine (ustconWriter numV within position endpoint).computableInLogSpace_of_reachesOut (k + 1)
    fun G => ?_
  simp only [encUGraph_apply]
  set B := (G.encode.length + 1) ^ (k + 1)
  have hlen := G.length_encode
  have hB : (F G).n ≤ B := (hbound G).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn : G.n ≤ B :=
    calc G.n ≤ G.encode.length + 1 := by omega
      _ = (G.encode.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hreg {u : ℕ} (hu : u ≤ (F G).n) := bounded3 hn (hu.trans hB) (Nat.zero_le _)
  -- the header of the input
  have hcount := reachesOut_count (P := ustconWriter numV within position endpoint)
    (w := G.encode) (c := 0) (n := G.n) (fun j => [j, 0, 0]) (u := 0) rfl rfl (fun _ _ => by simp)
    (fun j hj => bounded3 (hj.trans hn) (Nat.zero_le _) (Nat.zero_le _))
    (fun j hj => by
      rw [eval_reg, List.getD_cons_zero, G.getElem?_encode_n hj.le]
      simp [hj])
    (by
      rw [eval_reg, List.getD_cons_zero, G.getElem?_encode_n le_rfl]
      simp) 0 (Nat.zero_le _)
  -- the unary header `1^N` of the output
  have hcode : (ustconWriter numV within position endpoint).CodeAt 2 (forCode 2 1 numV 5 6) :=
    codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨_, hones, rfl, -⟩ := reachesOut_forCode (w := G.encode) (N := (F G).n)
    (o := fun _ => [true]) hcode (fun u regs => regs = [G.n, u, 0] ∧ u ≤ (F G).n) hB
    (by
      rintro u _ ⟨rfl, hu⟩
      exact ⟨rfl, hN G u 0, by simp, hreg hu⟩)
    (by
      rintro u hu _ ⟨rfl, -⟩
      exact ⟨_, ReachesOut.emit rfl (hreg hu.le) (.refl _), rfl, hreg hu.le, by simp, by omega⟩)
    [G.n, 0, 0] (hreg (Nat.zero_le _)) ⟨by simp, Nat.zero_le _⟩
  rw [List.flatMap_def, List.map_const', List.length_range,
    List.flatten_replicate_singleton] at hones
  obtain ⟨regs, hrows, hregs⟩ := reachesOut_rows G (hN G) hn hB (i₀ := (F G).n) hB
  have hr := hreg le_rfl
  refine ⟨(21, regs), _, [], hcount.trans (hones.trans
    (.emit rfl hr (.emit rfl hr (.emit rfl hr (.emit rfl hr hrows))))), rfl, ?_, hregs⟩
  rw [encUSTCON, Function.Embedding.coeFn_mk, USTCONInstance.encode,
    USTCONInstance.toSTCONInstance, STCONInstance.encode,
    STCONInstance.matrix_eq_flatMap _ (entryOf within position endpoint G)
      fun a b => (hentry G a b).trans rfl]
  simp [hs G, ht G]

end UGraphInstance

end Cslib.Complexity
