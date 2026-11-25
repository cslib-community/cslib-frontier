/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Code
public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.TrieModel
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Phase 1: Setup, Workspace Zero-Fill, and `TrieMem` Invariant

Verifies `setupAndClearCode`: reads header metadata (`σ`, `|P|`, `‖P‖`, `|t|`), pins the 18
layout registers (`LayoutInv`), and zero-fills all scratch arrays in `O((‖P‖ + 1) · σ)` steps,
establishing `TrieMem inp PTrie.init`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.trie`: opaque pure trie for `inp.patterns`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.TrieMem`: memory invariant relating Word-RAM memory to a
  partial `PTrie`.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.trie_spec`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.Input.char_iff`: pure trie guarantees linked to `maxS`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.exec_setupAndClear`: execution proof for Phase 1.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

/-- Pure integer-state trie built from `inp.patterns`. -/
def Input.trie (inp : Input) : PTrie := PTrie.build inp.patterns

/-- Unfolding equation for opaque `Input.trie`. -/
theorem Input.trie_eq (inp : Input) : inp.trie = PTrie.build inp.patterns := by rfl

/-- Specification of `inp.trie` under `inp.Valid`. -/
theorem Input.trie_spec {inp : Input} (hv : inp.Valid) :
    TreeInv inp.alphabetSize inp.trie ∧
    inp.trie.numStates ≤ inp.maxS ∧
    (∀ u < inp.trie.numStates, IsNode inp.patterns (inp.trie.strOf u)) ∧
    (∀ w, IsNode inp.patterns w → ∃ u < inp.trie.numStates, inp.trie.strOf u = w) ∧
    (∀ u < inp.trie.numStates, inp.trie.isTerm u =
      if inp.trie.strOf u ≠ [] ∧ inp.trie.strOf u ∈ inp.patterns then 1 else 0) := by
  have hmax : inp.maxS = totalPatternLen inp.patterns + 1 := (layout_order inp).1
  rw [hmax, Input.trie_eq]
  exact build_trie_spec inp.patterns inp.alphabetSize hv.1

/-- Positive trie transition equivalence with `IsNode`. -/
theorem Input.char_iff {inp : Input} (hv : inp.Valid) :
    ∀ u < inp.trie.numStates, ∀ c < inp.alphabetSize,
      IsNode inp.patterns (inp.trie.strOf u ++ [c]) ↔ 0 < inp.trie.trie u c := by
  rw [Input.trie_eq]
  exact trie_char_pos_iff inp.patterns inp.alphabetSize hv.1

/-! ## Phase 1: Setup and scratch-table clearing -/

/-- Word-RAM memory invariant pairing serialized patterns, text, trie table cells, depth/term
arrays, and zero-initialized remaining scratch buffers with a partial `PTrie`. -/
structure TrieMem (inp : Input) (T : PTrie) (mem : ℕ → ℕ) : Prop where
  pats : Block.HoldsList 5 (encodePatterns inp.patterns) mem
  txt : Block.HoldsList inp.textBase inp.text mem
  trie_cell : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
    mem (inp.trieBase + u * inp.alphabetSize + c) = T.trie u c
  depth_cell : ∀ u < inp.maxS, mem (inp.depthBase + u) = T.depth u
  term_cell : ∀ u < inp.maxS, mem (inp.termBase + u) = T.isTerm u
  zero_df : ∀ a, inp.deltaBase ≤ a → a < inp.depthBase → mem a = 0
  zero_rest : ∀ a, inp.outHeadBase ≤ a → a < inp.outBase → mem a = 0

private theorem exec_setupCode (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    (d₀ : Data 26)
    (hm1 : d₀.mem 1 = inp.alphabetSize)
    (hm2 : d₀.mem 2 = inp.patterns.length)
    (hm3 : d₀.mem 3 = totalPatternLen inp.patterns)
    (hm4 : d₀.mem 4 = inp.text.length) :
    ∃ x₀, ExecWithin w setupCode d₀ x₀ 25 ∧
      LayoutInv inp x₀ ∧ x₀.regs r1 = inp.trieBase ∧ x₀.mem = d₀.mem := by
  obtain ⟨hmaxS_eq, htb_eq, htr_eq, hdb_eq, hfb_eq, hdp_eq, htm_eq, hoh_eq, hon_eq, hqb_eq,
    hob_eq⟩ := layout_order inp
  have hob : inp.outBase = inp.trieBase + (2 * (inp.maxS * inp.alphabetSize) + 6 * inp.maxS) := by
    omega
  have hf1 : Fits w 1 := fits_of_le_outBase hw (by omega)
  have hf2 : Fits w 2 := fits_of_le_outBase hw (by omega)
  have hf3 : Fits w 3 := fits_of_le_outBase hw (by omega)
  have hf4 : Fits w 4 := fits_of_le_outBase hw (by omega)
  have hf5 : Fits w 5 := fits_of_le_outBase hw (by omega)
  have hf_maxS : Fits w inp.maxS := fits_of_le_outBase hw (by omega)
  have hf_maxS' : Fits w (totalPatternLen inp.patterns + 1) := by rw [← hmaxS_eq]; exact hf_maxS
  have hf_tb1 : Fits w (5 + inp.patterns.length) := fits_of_le_outBase hw (by omega)
  have hf_tb2 : Fits w (5 + inp.patterns.length + totalPatternLen inp.patterns) :=
    fits_of_le_outBase hw (by omega)
  have hf_tr : Fits w inp.trieBase := fits_of_le_outBase hw (by omega)
  have hf_msig : Fits w (inp.maxS * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_db : Fits w inp.deltaBase := fits_of_le_outBase hw (by omega)
  have hf_fb : Fits w inp.failBase := fits_of_le_outBase hw (by omega)
  have hf_dp : Fits w inp.depthBase := fits_of_le_outBase hw (by omega)
  have hf_tm : Fits w inp.termBase := fits_of_le_outBase hw (by omega)
  have hf_oh : Fits w inp.outHeadBase := fits_of_le_outBase hw (by omega)
  have hf_on : Fits w inp.outNextBase := fits_of_le_outBase hw (by omega)
  have hf_qb : Fits w inp.queueBase := fits_of_le_outBase hw (by omega)
  have hf_ob : Fits w inp.outBase := fits_of_le_outBase hw (Nat.le_refl _)
  have h1 : ∃ x₁, ExecWithin w setupHeaderCode d₀ x₁ 12 ∧
      x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧
      x₁.regs sigma = inp.alphabetSize ∧ x₁.regs numPat = inp.patterns.length ∧
      x₁.regs totPat = totalPatternLen inp.patterns ∧ x₁.regs textLen = inp.text.length ∧
      x₁.regs maxS = inp.maxS ∧ x₁.regs patBase = 5 ∧ x₁.mem = d₀.mem := by
    refine WP.exists_execWithin ?_
    unfold setupHeaderCode
    wram_exec [hf1, hf2, hf3, hf4, hf5, hm1, hm2, hm3, hm4, hf_maxS']
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp [hmaxS_eq], by wram_simp, by wram_simp⟩
  obtain ⟨x₁, he₁, hz1, ho1, hsig1, hnp1, htp1, htl1, hms1, hpb1, hmem1⟩ := h1
  have h2 : ∃ x₀, ExecWithin w setupBaseCode x₁ x₀ 13 ∧
      LayoutInv inp x₀ ∧ x₀.regs r1 = inp.trieBase ∧ x₀.mem = x₁.mem := by
    refine WP.exists_execWithin ?_
    unfold setupBaseCode
    wram_exec [hpb1, hnp1, htp1, htl1, hms1, hsig1, hf_tb1, hf_tb2, htb_eq.symm, hf_tr,
      htr_eq.symm, hf_msig, hf_db, hdb_eq.symm, hf_fb, hfb_eq.symm, hf_dp, hdp_eq.symm,
      hf_tm, htm_eq.symm, hf_oh, hoh_eq.symm, hf_on, hon_eq.symm, hf_qb, hqb_eq.symm,
      hf_ob, hob_eq.symm]
    refine ⟨?_, by wram_simp, by wram_simp⟩
    constructor <;> wram_simp <;> assumption
  obtain ⟨x₀, he₂, hL₀, hr1₀, hmem0⟩ := h2
  exact ⟨x₀, he₁.seq he₂, hL₀, hr1₀, hmem0.trans hmem1⟩

private theorem trieMem_of_clear_init {inp : Input} {mem : ℕ → ℕ}
    (hpats : Block.HoldsList 5 (encodePatterns inp.patterns) mem)
    (htxt : Block.HoldsList inp.textBase inp.text mem) :
    TrieMem inp PTrie.init
      (Cslib.WordRAM.clear mem inp.trieBase
        (2 * (inp.maxS * inp.alphabetSize) + 6 * inp.maxS)) := by
  have hlo := layout_order inp
  have hlen := length_encodePatterns inp.patterns
  refine
    { pats := hpats.frame fun a _ hlt =>
        Cslib.WordRAM.clear_of_not_owns fun hown => by have : inp.trieBase ≤ a := hown.1; omega
      txt := htxt.frame fun a _ hlt =>
        Cslib.WordRAM.clear_of_not_owns fun hown => by have : inp.trieBase ≤ a := hown.1; omega
      trie_cell := fun u hu c hc => by
        have := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        exact Cslib.WordRAM.clear_of_owns ⟨by dsimp only; omega, by dsimp only; omega⟩
      depth_cell := fun u hu =>
        Cslib.WordRAM.clear_of_owns ⟨by dsimp only; omega, by dsimp only; omega⟩
      term_cell := fun u hu =>
        Cslib.WordRAM.clear_of_owns ⟨by dsimp only; omega, by dsimp only; omega⟩
      zero_df := fun a ha1 ha2 =>
        Cslib.WordRAM.clear_of_owns ⟨by dsimp only; omega, by dsimp only; omega⟩
      zero_rest := fun a ha1 ha2 =>
        Cslib.WordRAM.clear_of_owns ⟨by dsimp only; omega, by dsimp only; omega⟩ }

theorem exec_setupAndClear (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound) :
    ∃ y, ExecWithin w setupAndClearCode (.init inp.encode) y
        (8 * inp.maxS * inp.alphabetSize + 24 * inp.maxS + 31) ∧
      LayoutInv inp y ∧
      TrieMem inp PTrie.init y.mem := by
  have hlo := layout_order inp
  have hob : inp.outBase = inp.trieBase + (2 * (inp.maxS * inp.alphabetSize) + 6 * inp.maxS) := by
    omega
  have hf_ob : Fits w inp.outBase := fits_of_le_outBase hw (Nat.le_refl _)
  generalize hd₀ : (Data.init inp.encode : Data 26) = d₀
  have hinit_list : Block.HoldsList 1
      (inp.alphabetSize :: inp.patterns.length :: totalPatternLen inp.patterns ::
        inp.text.length :: (encodePatterns inp.patterns ++ inp.text)) d₀.mem := by
    rw [← hd₀]
    exact (outputList_eq_iff.mp (outputList_init inp.encode)).2
  obtain ⟨hm1, hinit1⟩ := Block.holdsList_cons_iff.mp hinit_list
  obtain ⟨hm2', hinit2⟩ := Block.holdsList_cons_iff.mp hinit1
  obtain ⟨hm3', hinit3⟩ := Block.holdsList_cons_iff.mp hinit2
  obtain ⟨hm4', hinit4⟩ := Block.holdsList_cons_iff.mp hinit3
  obtain ⟨hpats0', htxt0⟩ := Block.holdsList_append_iff.mp hinit4
  have hpats0 : Block.HoldsList 5 (encodePatterns inp.patterns) d₀.mem := hpats0'
  have htxt0' : Block.HoldsList inp.textBase inp.text d₀.mem := by
    have heq : 1 + 1 + 1 + 1 + 1 + (encodePatterns inp.patterns).length = inp.textBase := by
      rw [length_encodePatterns]; omega
    rwa [heq] at htxt0
  obtain ⟨x₀, he₀, hL₀, hr1₀, hm₀⟩ := exec_setupCode inp w hw d₀ hm1 hm2' hm3' hm4'
  have hzf := (zeroFill_exec (w := w) (cur := r1) (stop := out) (zero := zero) (one := one)
    (x := x₀) (by decide) (by decide) (by decide) hL₀.h_zero hL₀.h_one
    (by rw [hr1₀, hL₀.h_out]; omega) (by rw [hL₀.h_out]; exact hf_ob)).within
  have he_tot : ExecWithin w setupAndClearCode d₀
      ⟨Function.update x₀.regs r1 (x₀.regs out),
        Cslib.WordRAM.clear x₀.mem (x₀.regs r1) (x₀.regs out - x₀.regs r1)⟩
      (8 * inp.maxS * inp.alphabetSize + 24 * inp.maxS + 31) := by
    refine (he₀.seq hzf).mono ?_
    rw [hr1₀, hL₀.h_out, hob, Nat.mul_assoc]
    omega
  refine ⟨_, he_tot, hL₀.of_preserves hzf, ?_⟩
  dsimp only
  have hsub : inp.outBase - inp.trieBase = 2 * (inp.maxS * inp.alphabetSize) + 6 * inp.maxS := by
    omega
  rw [hm₀, hr1₀, hL₀.h_out, hsub]
  exact trieMem_of_clear_init hpats0 htxt0'

end Cslib.Algorithms.WordRAM.AhoCorasick
