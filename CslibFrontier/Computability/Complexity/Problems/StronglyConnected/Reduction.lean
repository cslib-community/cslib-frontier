/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
public import CslibFrontier.Computability.Complexity.Problems.STCON.Header

/-!
# Directed connectivity as strong connectivity

An instance `I` of directed `s`–`t` connectivity becomes the digraph
`Cslib.Complexity.StronglyConnected.ofSTCON I` on the same vertices, with the arcs of `I`, an
arc from every vertex to `s` and an arc from `t` to every vertex. It is strongly connected exactly
when `t` is reachable from `s` in `I` (`Cslib.Complexity.StronglyConnected.ofSTCON_mem_iff`): a
path from `s` to `t` gives the path `a → s ⇝ t → b` between any two vertices, and conversely a
path from `s` that uses a new arc either returns to `s` or leaves `t` after reaching it.

The digraph is written in logarithmic space by a counter program with output
(`Cslib.Complexity.StronglyConnected.writer`), which reads the header of the encoded instance
(`Cslib.Complexity.STCONInstance.headerCode`), writes the unary header `1^n 0`, and then writes the
matrix entry by entry, reading the entry of `I` unless the column is `s` or the row is `t`
(`Cslib.Complexity.StronglyConnected.computableInLogSpace_ofSTCON`).

## Main definitions

* `Cslib.Complexity.StronglyConnected.ofSTCON`: the digraph of an instance.
* `Cslib.Complexity.StronglyConnected.writer`: the counter program writing its encoding.

## Main results

* `Cslib.Complexity.StronglyConnected.ofSTCON_mem_iff`: the digraph is strongly connected exactly
  when `t` is reachable from `s`.
* `Cslib.Complexity.StronglyConnected.computableInLogSpace_ofSTCON`: the digraph is computed in
  logarithmic space.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Exercise 4.4][AroraBarak09]
-/

public section

namespace Cslib.Complexity

namespace StronglyConnected

/-- **The digraph of an instance of directed connectivity**: the arcs of the instance, an arc from
every vertex to `s` and an arc from `t` to every vertex. -/
@[expose] def ofSTCON (I : STCONInstance) : DigraphInstance where
  n := I.n
  adj a b := I.adj a b || decide (b = I.s) || decide (a = I.t)

/-- A path from `s` in the digraph either is a path of the instance, or the instance reaches `t`
from `s`. -/
private theorem reflTransGen_or_of_ofSTCON {I : STCONInstance} {x : Fin I.n}
    (h : Relation.ReflTransGen (ofSTCON I).Adj I.s x) :
    Relation.ReflTransGen I.Adj I.s x ∨ Relation.ReflTransGen I.Adj I.s I.t := by
  induction h with
  | refl => exact .inl .refl
  | @tail y z _ hyz ih =>
    simp only [DigraphInstance.Adj, ofSTCON, Bool.or_eq_true, decide_eq_true_eq] at hyz
    rcases hyz with (hyz | rfl) | rfl
    · exact ih.imp_left (·.tail hyz)
    · exact .inl .refl
    · exact .inr (ih.elim id id)

/-- **The digraph is strongly connected exactly when `t` is reachable from `s`.** -/
theorem ofSTCON_mem_iff (I : STCONInstance) : ofSTCON I ∈ StronglyConnected ↔ I ∈ STCON := by
  rw [mem_StronglyConnected, mem_STCON]
  refine ⟨fun h => (reflTransGen_or_of_ofSTCON (h I.s I.t)).elim id id, fun h a b => ?_⟩
  have hmono : Relation.ReflTransGen (ofSTCON I).Adj I.s I.t :=
    Relation.ReflTransGen.mono (fun x y (hxy : I.adj x y = true) => by
      simp [DigraphInstance.Adj, ofSTCON, hxy]) _ _ h
  refine (Relation.ReflTransGen.single ?_).trans (hmono.tail ?_)
  · simp [DigraphInstance.Adj, ofSTCON]
  · simp [DigraphInstance.Adj, ofSTCON]

/-! ### The writer -/

section Writer

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr _root_.Turing.MultiTapeTM

/-- **The writer** of the encoded digraph, on the encoded instance. Registers `0`, `1` and `2`
receive the header values `n`, `s` and `t`; register `3` counts the unary header and then runs
over the rows, register `4` over the columns. Labels `0` to `5` read the header, the loop at label
`6` writes the unary header `1^n 0`, the nested loops at labels `11` and `14` write the matrix, the
entry at labels `17` to `23`, and label `24` halts. -/
def writer : CounterProgram where
  code := List.flatten [
    STCONInstance.headerCode 0,
    forCode 6 3 (reg 0) 9 10, [emit true 8, emit false 11],
    forCode 11 3 (reg 0) 14 24, forCode 14 4 (reg 0) 17 13,
    [lt (reg 4) (reg 1) 19 18,
     lt (reg 1) (reg 4) 19 23,
     lt (reg 3) (reg 2) 21 20,
     lt (reg 2) (reg 3) 21 23,
     read (add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3))
       (add (mul (reg 3) (reg 0)) (reg 4))) 23 22 22,
     emit false 16,
     emit true 16,
     halt []]]
  registers := 5

variable (I : STCONInstance) {B : ℕ}

/-- The entries of the matrix of `ofSTCON I`, on natural numbers. -/
private def entry (u v : ℕ) : Bool :=
  if v = I.s ∨ u = I.t then true
  else if h : u < I.n ∧ v < I.n then I.adj ⟨u, h.1⟩ ⟨v, h.2⟩ else false

private theorem entry_eq (a b : Fin (ofSTCON I).n) : (ofSTCON I).adj a b = entry I a b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [ofSTCON] at ha hb
  by_cases hbs : b = I.s <;> by_cases hat : a = I.t <;>
    simp [ofSTCON, entry, Fin.ext_iff, ha, hb, hbs, hat]

/-- Two `lt` instructions at `l` and `l + 1` comparing registers `r₁` and `r₂` branch to `eq` when
their values agree and to `neq` otherwise. -/
private theorem reachesOut_eq_branch {l r₁ r₂ neq eq : ℕ}
    (h₁ : writer.instr l = lt (reg r₁) (reg r₂) neq (l + 1))
    (h₂ : writer.instr (l + 1) = lt (reg r₂) (reg r₁) neq eq)
    {regs : List ℕ} (hb : ∀ z ∈ regs, z ≤ B) :
    writer.ReachesOut I.encode (writer.Active B) (l, regs)
      (if regs.getD r₁ 0 = regs.getD r₂ 0 then eq else neq, regs) [] := by
  refine ReachesOut.lt h₁ hb ?_
  by_cases hlt : regs.getD r₁ 0 < regs.getD r₂ 0
  · simp only [eval_reg, hlt, ↓reduceIte, show regs.getD r₁ 0 ≠ regs.getD r₂ 0 by omega]
    exact ReachesOut.refl _
  · simp only [eval_reg, hlt, ↓reduceIte]
    refine ReachesOut.lt h₂ hb ?_
    by_cases hgt : regs.getD r₂ 0 < regs.getD r₁ 0
    · simp only [eval_reg, hgt, ↓reduceIte, show regs.getD r₁ 0 ≠ regs.getD r₂ 0 by omega]
      exact ReachesOut.refl _
    · simp only [eval_reg, show regs.getD r₁ 0 = regs.getD r₂ 0 by omega, lt_irrefl, ↓reduceIte]
      exact ReachesOut.refl _

/-- Writing the entry `(u, v)` of the matrix. -/
private theorem reachesOut_entry (hB : I.n ≤ B) {u v : ℕ} (hu : u < I.n) (hv : v < I.n) :
    writer.ReachesOut I.encode (writer.Active B)
      (17, [I.n, I.s, I.t, u, v]) (16, [I.n, I.s, I.t, u, v]) [entry I u v] := by
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hb : ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, v], z ≤ B :=
    I.regs_le hB (by omega) (by omega)
  have hone : writer.ReachesOut I.encode (writer.Active B) (23, [I.n, I.s, I.t, u, v])
      (16, [I.n, I.s, I.t, u, v]) [true] :=
    ReachesOut.emit (show writer.instr 23 = _ from rfl) hb (ReachesOut.refl _)
  have h17 := reachesOut_eq_branch I (l := 17) (r₁ := 4) (r₂ := 1) (neq := 19) (eq := 23) rfl rfl hb
  have h19 := reachesOut_eq_branch I (l := 19) (r₁ := 3) (r₂ := 2) (neq := 21) (eq := 23) rfl rfl hb
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h17 h19
  by_cases hvs : v = I.s
  · rw [ite_eq_left hvs] at h17
    simpa [entry, hvs] using h17.trans hone
  · rw [ite_eq_right hvs] at h17
    refine h17.trans ?_
    by_cases hut : u = I.t
    · rw [ite_eq_left hut] at h19
      simpa [entry, hut] using h19.trans hone
    · rw [ite_eq_right hut] at h19
      refine h19.trans (ReachesOut.read (show writer.instr 21 = _ from rfl) hb ?_)
      simp only [eval_add, eval_mul, eval_reg, eval_const, List.getD_cons_zero,
        List.getD_cons_succ, I.getElem?_encode_matrix hu hv]
      have he : entry I u v = I.adj ⟨u, hu⟩ ⟨v, hv⟩ := by simp [entry, hvs, hut, hu, hv]
      rw [he]
      cases I.adj ⟨u, hu⟩ ⟨v, hv⟩
      · exact ReachesOut.emit (show writer.instr 22 = _ from rfl) hb (ReachesOut.refl _)
      · exact hone

/-- **The matrix row by row**, by the nested loops at labels `11` and `14`. -/
private theorem reachesOut_rows (hB : I.n ≤ B) {i₀ : ℕ} (hi₀ : i₀ ≤ I.n) :
    ∃ regs, writer.ReachesOut I.encode (writer.Active B)
      (11, [I.n, I.s, I.t, i₀, 0]) (24, regs)
      ((List.range I.n).flatMap fun u => (List.range I.n).map (entry I u)) ∧
      ∀ x ∈ regs, x ≤ B := by
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hreg : ∀ {u v : ℕ}, u ≤ I.n → v ≤ I.n → ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, v], z ≤ B :=
    fun hu hv => I.regs_le hB (hu.trans hB) (hv.trans hB)
  have hcode₁ : writer.CodeAt 11 (forCode 11 3 (reg 0) 14 24) := codeAt_of_prefix ⟨_, rfl⟩
  have hcode₂ : writer.CodeAt 14 (forCode 14 4 (reg 0) 17 13) := codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨regs, hreach, x, rfl, -, hx⟩ := reachesOut_forCode (w := I.encode) (N := I.n)
    (o := fun u => (List.range I.n).map (entry I u)) hcode₁
    (fun u regs => ∃ x, regs = [I.n, I.s, I.t, u, x] ∧ u ≤ I.n ∧ x ≤ I.n) hB
    (by
      rintro u regs ⟨x, rfl, hu, hx⟩
      exact ⟨rfl, rfl, by simp, hreg hu hx⟩)
    (by
      rintro u hu regs ⟨x, rfl, -, hx⟩
      obtain ⟨regs', hreach, rfl, -⟩ := reachesOut_forCode (w := I.encode) (N := I.n)
        (o := fun v => [entry I u v]) hcode₂
        (fun v regs => regs = [I.n, I.s, I.t, u, v] ∧ v ≤ I.n) hB
        (by
          rintro v regs ⟨rfl, hv⟩
          exact ⟨rfl, rfl, by simp, hreg hu.le hv⟩)
        (by
          rintro v hv regs ⟨rfl, -⟩
          exact ⟨_, reachesOut_entry I hB hu hv, rfl, hreg hu.le hv.le, by simp, by omega⟩)
        [I.n, I.s, I.t, u, x] (hreg hu.le hx) ⟨by simp, by omega⟩
      refine ⟨_, ?_, rfl, hreg hu.le le_rfl, I.n, by simp, by omega, le_rfl⟩
      rwa [← List.map_eq_flatMap] at hreach)
    [I.n, I.s, I.t, i₀, 0] (hreg hi₀ (Nat.zero_le _)) ⟨0, by simp, by omega, by omega⟩
  exact ⟨_, hreach, hreg le_rfl hx⟩

/-- **The digraph is computed in logarithmic space** from the encoded instance. -/
theorem computableInLogSpace_ofSTCON : ComputableInLogSpace ofSTCON encSTCON encDigraph := by
  refine writer.computableInLogSpace_of_reachesOut 1 fun I => ?_
  simp only [encSTCON_apply, pow_one]
  have hlen := I.length_encode
  have hB : I.n ≤ I.encode.length + 1 := by omega
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hreg : ∀ {u : ℕ}, u ≤ I.n →
      ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, 0], z ≤ I.encode.length + 1 :=
    fun hu => I.regs_le hB (by omega) (Nat.zero_le _)
  -- the unary header `1^n`
  have hcode : writer.CodeAt 6 (forCode 6 3 (reg 0) 9 10) := codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨regs₁, hones, rfl, -⟩ := reachesOut_forCode (w := I.encode) (N := I.n)
    (o := fun _ => [true]) hcode
    (fun u regs => regs = [I.n, I.s, I.t, u, 0] ∧ u ≤ I.n) hB
    (by
      rintro u regs ⟨rfl, hu⟩
      exact ⟨rfl, rfl, by simp, hreg hu⟩)
    (by
      rintro u hu regs ⟨rfl, -⟩
      exact ⟨_, ReachesOut.emit (show writer.instr 9 = _ from rfl) (hreg hu.le)
        (ReachesOut.refl _), rfl, hreg hu.le, by simp, by omega⟩)
    [I.n, I.s, I.t, 0, 0] (hreg (Nat.zero_le _)) ⟨by simp, by omega⟩
  rw [List.flatMap_def, List.map_const', List.length_range,
    List.flatten_replicate_singleton] at hones
  obtain ⟨regs, hrows, hregs⟩ := reachesOut_rows I hB (i₀ := I.n) le_rfl
  have hchain := (I.reachesOut_headerCode (P := writer) (codeAt_of_prefix ⟨_, rfl⟩) hB
    (rest := [0, 0]) (by simp)).trans (hones.trans (ReachesOut.emit
      (show writer.instr 10 = _ from rfl) (hreg le_rfl) hrows))
  refine ⟨(24, regs), _, [], hchain, rfl, ?_, hregs⟩
  rw [encDigraph_apply, DigraphInstance.encode,
    adjacencyMatrix_eq_flatMap _ (entry I) (entry_eq I)]
  simp [ofSTCON]

end Writer

end StronglyConnected

end Cslib.Complexity
