/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Structured
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.PreservesMask
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.Nat.Div
import Mathlib.Data.Finset.Card

/-!
# Aho–Corasick Multi-Pattern Matching on the Word-RAM

Linear-time implementation of the Aho–Corasick multi-pattern string matching machine
(`[AhoCorasick1975]`, Algorithms 1, 2, and 3 and Section 6) on the `Basis.standard` Word-RAM over
bounded integer alphabets `[0, σ)`:

1. **Array-trie construction** inserts all keywords `P` (`|P|` keywords of total length
   `‖P‖ = totalPatternLen P`) into a flat `(‖P‖ + 1) × σ` integer-state goto table with root `0`
   in `O((‖P‖ + 1) · σ + |P|)` instructions.
2. **Breadth-first failure, next-move, and output-link construction** populates `fail[s]`,
   `delta[s * σ + a]`, `outHead[s]`, and `outNext[s]` over an explicit FIFO queue in
   `O((‖P‖ + 1) · σ)` instructions, visiting each shared trie state once.
3. **Amortized text scanning** executes Algorithm 1 along `trie` and `fail` using the failure-depth
   potential `depth[u]` (`[AhoCorasick1975]`, Theorem 2) and emits each reported keyword occurrence
   as `[endPos, keywordLen]` via `outHead` / `outNext` in `O(|t| + occ)` instructions (independent
   of `σ` during the scan).

Together, `searchCode` and `searchProgram` compute `encodeOccurrences (occurrences P t)` (from which
`decodeOccurrences_encodeOccurrences` recovers `occurrences P t` losslessly) within
`searchTime inp = O((‖P‖ + 1) · σ + |P| + |t| + occ)` instructions at any word width `w` with
`Fits w inp.wordBound`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input`: integer-alphabet multi-pattern matching instance.
* `Cslib.Algorithms.WordRAM.AhoCorasick.totalPatternLen`: total keyword length `‖P‖`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.Valid`: alphabet validity `< σ`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.encodePatterns`, `Input.encode`: flat word-array input
  encoding.
* `Cslib.Algorithms.WordRAM.AhoCorasick.encodeOccurrences`, `decodeOccurrences`: flat `[pos, len]`
  occurrence encoding and lossless decoder.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.wordBound`, `searchTime`: word-width threshold and
  instruction bound.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Reg.out`: output header register.
* `Cslib.Algorithms.WordRAM.AhoCorasick.searchCode`, `searchProgram`: structured and flat Word-RAM
  Aho–Corasick multi-pattern matcher.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.decodeOccurrences_encodeOccurrences`: `decodeOccurrences t`
  recovers `occurrences P t` from `encodeOccurrences (occurrences P t)`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.wordBound_le`: polynomial upper bound on `inp.wordBound`
  independent of `occ`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.Valid.inputFits`: `InputFits w inp.encode` from
  `inp.Valid` and `Fits w inp.wordBound`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.searchCode_exec`, `searchProgram_computesListInTime`,
  `searchProgram_executesList`: linear `O((‖P‖ + 1) · σ + |P| + |t| + occ)` Word-RAM running time.

## References

* [A. V. Aho and M. J. Corasick, *Efficient String Matching: An Aid to Bibliographic
  Search*][AhoCorasick1975]
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick

/-! ## Input/output encodings and pure bounds -/

/-- Input to the integer-alphabet Aho–Corasick matcher: strict alphabet upper bound `alphabetSize`
(`σ`), keyword list `patterns` (`P`), and text `text` (`t`). -/
structure Input where
  /-- Strict upper bound `σ` on alphabet symbols. -/
  alphabetSize : ℕ
  /-- Keyword list `P`. -/
  patterns : List (List ℕ)
  /-- Text `t` to scan. -/
  text : List ℕ
  deriving DecidableEq, Repr

/-- Total length `‖P‖ = ∑_{p ∈ P} |p|` of all keywords in `P`. -/
@[expose] def totalPatternLen (P : List (List ℕ)) : ℕ :=
  (P.map List.length).sum

@[simp] theorem totalPatternLen_nil : totalPatternLen [] = 0 := rfl

@[simp] theorem totalPatternLen_cons (p : List ℕ) (ps : List (List ℕ)) :
    totalPatternLen (p :: ps) = p.length + totalPatternLen ps := by
  simp [totalPatternLen]

/-- Every symbol of every keyword and of the text lies in `[0, inp.alphabetSize)`. -/
@[expose] def Input.Valid (inp : Input) : Prop :=
  (∀ p ∈ inp.patterns, ∀ a ∈ p, a < inp.alphabetSize) ∧
    (∀ a ∈ inp.text, a < inp.alphabetSize)

instance (inp : Input) : Decidable inp.Valid :=
  inferInstanceAs (Decidable
    ((∀ p ∈ inp.patterns, ∀ a ∈ p, a < inp.alphabetSize) ∧
      (∀ a ∈ inp.text, a < inp.alphabetSize)))

/-- Flat word-list encoding of `P`: `[|p₁|, p₁..., |p₂|, p₂..., ...]`. -/
@[expose] def encodePatterns : List (List ℕ) → List ℕ
  | [] => []
  | p :: ps => p.length :: (p ++ encodePatterns ps)

@[simp] theorem length_encodePatterns : ∀ P : List (List ℕ),
    (encodePatterns P).length = P.length + totalPatternLen P
  | [] => rfl
  | p :: ps => by
    simp only [encodePatterns, List.length_cons, List.length_append, length_encodePatterns ps,
      totalPatternLen_cons]
    omega

/-- Input word-array encoding `[σ, |P|, ‖P‖, |t|] ++ encodePatterns P ++ t`. -/
@[expose] def Input.encode (inp : Input) : List ℕ :=
  inp.alphabetSize :: inp.patterns.length :: totalPatternLen inp.patterns :: inp.text.length ::
    (encodePatterns inp.patterns ++ inp.text)

@[simp] theorem length_encode (inp : Input) :
    inp.encode.length =
      4 + inp.patterns.length + totalPatternLen inp.patterns + inp.text.length := by
  simp only [Input.encode, List.length_cons, List.length_append, length_encodePatterns]
  omega

/-- Flat word-list encoding of occurrences `[(pos₁, y₁), ...]`: `[pos₁, |y₁|, pos₂, |y₂|, ...]`. -/
@[expose] def encodeOccurrences (occs : List (ℕ × List ℕ)) : List ℕ :=
  occs.flatMap fun p => [p.1, p.2.length]

@[simp] theorem encodeOccurrences_nil : encodeOccurrences [] = [] := rfl

theorem encodeOccurrences_append (xs ys : List (ℕ × List ℕ)) :
    encodeOccurrences (xs ++ ys) = encodeOccurrences xs ++ encodeOccurrences ys := by
  simp [encodeOccurrences, List.flatMap_append]

@[simp] theorem length_encodeOccurrences : ∀ occs : List (ℕ × List ℕ),
    (encodeOccurrences occs).length = 2 * occs.length
  | [] => rfl
  | p :: xs => by
    change ([p.1, p.2.length] ++ encodeOccurrences xs).length = 2 * (xs.length + 1)
    simp only [List.cons_append, List.nil_append, List.length_cons, length_encodeOccurrences xs]
    omega

/-- Recover `(endPos, keyword)` pairs from `encodeOccurrences` and `t`. -/
@[expose] def decodeOccurrences (t : List ℕ) : List ℕ → List (ℕ × List ℕ)
  | pos :: len :: rest => (pos, (t.take pos).drop (pos - len)) :: decodeOccurrences t rest
  | _ => []

private theorem decodeOccurrences_aux (t : List ℕ) :
    ∀ occs : List (ℕ × List ℕ),
      (∀ x ∈ occs, x.1 ≤ t.length ∧ x.2 <:+ t.take x.1) →
      decodeOccurrences t (encodeOccurrences occs) = occs
  | [], _ => rfl
  | (pos, y) :: rest, h => by
    obtain ⟨hpos, hsuf⟩ := h (pos, y) List.mem_cons_self
    have htake_len : (t.take pos).length = pos := List.length_take_of_le hpos
    have hy_eq : (t.take pos).drop (pos - y.length) = y := by
      have hs := (List.suffix_iff_eq_drop.mp hsuf).symm
      rwa [htake_len] at hs
    change (pos, (t.take pos).drop (pos - y.length)) ::
        decodeOccurrences t (encodeOccurrences rest) = (pos, y) :: rest
    rw [hy_eq, decodeOccurrences_aux t rest fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `decodeOccurrences t` losslessly recovers `occurrences P t` from its flat word encoding. -/
theorem decodeOccurrences_encodeOccurrences (P : List (List ℕ)) (t : List ℕ) :
    decodeOccurrences t (encodeOccurrences (occurrences P t)) = occurrences P t := by
  refine decodeOccurrences_aux t _ fun ⟨pos, y⟩ hmem => ?_
  obtain ⟨hpos, -, -, hsuf⟩ := mem_occurrences_iff.mp hmem
  exact ⟨hpos, hsuf⟩

/-- Word-width threshold for `searchCode` and `searchProgram`. -/
@[expose] def Input.wordBound (inp : Input) : ℕ :=
  let M := totalPatternLen inp.patterns
  let S := M + 1
  5 + inp.patterns.length + M + inp.text.length + 2 * S * inp.alphabetSize + 6 * S +
    2 * (occurrences inp.patterns inp.text).length + 4

/-- Instruction bound `O((‖P‖ + 1) · σ + |P| + |t| + occ)` for `searchProgram`. -/
@[expose] def searchTime (inp : Input) : ℕ :=
  let M := totalPatternLen inp.patterns
  let S := M + 1
  64 * S * inp.alphabetSize + 80 * S + 20 * inp.patterns.length + 50 * inp.text.length +
    16 * (occurrences inp.patterns inp.text).length + 120

/-- Polynomial upper bound on `inp.wordBound` in terms of `|P|`, `‖P‖`, `|t|`, and `σ` alone. -/
theorem wordBound_le (inp : Input) :
    inp.wordBound ≤
      5 + inp.patterns.length + totalPatternLen inp.patterns + inp.text.length +
        2 * (totalPatternLen inp.patterns + 1) * inp.alphabetSize +
        6 * (totalPatternLen inp.patterns + 1) +
        2 * (inp.text.length * inp.patterns.length) + 4 := by
  have hocc := length_occurrences_le inp.patterns inp.text
  dsimp only [Input.wordBound]
  omega

/-! ## Pure integer-state trie model -/

private structure PTrie where
  numStates : ℕ
  strOf : ℕ → List ℕ
  trie : ℕ → ℕ → ℕ
  depth : ℕ → ℕ
  isTerm : ℕ → ℕ

private def PTrie.init : PTrie where
  numStates := 1
  strOf _ := []
  trie _ _ := 0
  depth _ := 0
  isTerm _ := 0

private def PTrie.stepChar (T : PTrie) (u a : ℕ) : PTrie × ℕ :=
  if T.trie u a = 0 then
    let s := T.numStates
    ({ numStates := s + 1
       strOf := Function.update T.strOf s (T.strOf u ++ [a])
       trie := fun x c => if x = u ∧ c = a then s else T.trie x c
       depth := Function.update T.depth s (T.depth u + 1)
       isTerm := T.isTerm }, s)
  else
    (T, T.trie u a)

private def PTrie.insertChars : PTrie → ℕ → List ℕ → PTrie × ℕ
  | T, u, [] => (T, u)
  | T, u, a :: as =>
    let res := T.stepChar u a
    res.1.insertChars res.2 as

private def PTrie.insertPat (T : PTrie) (p : List ℕ) : PTrie :=
  let res := T.insertChars 0 p
  if 0 < res.2 then { res.1 with isTerm := Function.update res.1.isTerm res.2 1 } else res.1

private def PTrie.build (P : List (List ℕ)) : PTrie :=
  P.foldl PTrie.insertPat PTrie.init

private structure TreeInv (σ : ℕ) (T : PTrie) : Prop where
  one_le : 1 ≤ T.numStates
  str_zero : T.strOf 0 = []
  depth_zero : T.depth 0 = 0
  term_zero : T.isTerm 0 = 0
  str_ne_nil : ∀ u, 0 < u → u < T.numStates → T.strOf u ≠ []
  depth_eq : ∀ u < T.numStates, T.depth u = (T.strOf u).length
  str_inj : ∀ u < T.numStates, ∀ v < T.numStates, T.strOf u = T.strOf v → u = v
  trie_lt : ∀ u < T.numStates, ∀ a < σ, T.trie u a < T.numStates
  trie_spec : ∀ u < T.numStates, ∀ a < σ,
    T.trie u a = 0 ∨ (0 < T.trie u a ∧ T.strOf (T.trie u a) = T.strOf u ++ [a])
  parent_exists : ∀ w, 0 < w → w < T.numStates →
    ∃ u < w, ∃ a < σ, T.trie u a = w ∧ T.strOf w = T.strOf u ++ [a]
  trie_oob : ∀ u, T.numStates ≤ u → ∀ a, T.trie u a = 0
  depth_oob : ∀ u, T.numStates ≤ u → T.depth u = 0
  term_oob : ∀ u, T.numStates ≤ u → T.isTerm u = 0

private theorem treeInv_init (σ : ℕ) : TreeInv σ PTrie.init where
  one_le := Nat.le_refl 1
  str_zero := rfl
  depth_zero := rfl
  term_zero := rfl
  str_ne_nil := fun _ hpos hlt => by simp only [PTrie.init] at hlt; omega
  depth_eq := fun u hlt => by
    simp only [PTrie.init] at hlt
    have : u = 0 := by omega
    subst this; rfl
  str_inj := fun u hu v hv _ => by simp only [PTrie.init] at hu hv; omega
  trie_lt := fun _ _ _ _ => Nat.zero_lt_one
  trie_spec := fun _ _ _ _ => Or.inl rfl
  parent_exists := fun _ hpos hlt => by simp only [PTrie.init] at hlt; omega
  trie_oob := fun _ _ _ => rfl
  depth_oob := fun _ _ => rfl
  term_oob := fun _ _ => rfl

private theorem TreeInv.trie_eq_of_strOf {σ : ℕ} {T : PTrie} (hT : TreeInv σ T)
    {u v a : ℕ} (hu : u < T.numStates) (hv : v < T.numStates)
    (hstr : T.strOf v = T.strOf u ++ [a]) :
    0 < v ∧ T.trie u a = v := by
  have hv_pos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | hp
    · rw [hT.str_zero] at hstr
      exact absurd hstr.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a []))
    · exact hp
  obtain ⟨u', hu'v, a', _, htrie', hstr'⟩ := hT.parent_exists v hv_pos hv
  have hinj := List.append_inj' (hstr'.symm.trans hstr) rfl
  have ha_eq : a' = a := List.head_eq_of_cons_eq hinj.2
  have hu_eq : u' = u := hT.str_inj u' (by omega) u hu hinj.1
  subst ha_eq; subst hu_eq
  exact ⟨hv_pos, htrie'⟩

private theorem stepChar_spec {σ : ℕ} {T : PTrie} (hT : TreeInv σ T) {u a : ℕ}
    (hu : u < T.numStates) (ha : a < σ) :
    let res := T.stepChar u a
    TreeInv σ res.1 ∧
      T.numStates ≤ res.1.numStates ∧
      res.1.numStates ≤ T.numStates + 1 ∧
      0 < res.2 ∧ res.2 < res.1.numStates ∧
      res.1.strOf res.2 = T.strOf u ++ [a] ∧
      (∀ v < T.numStates, res.1.strOf v = T.strOf v ∧ res.1.isTerm v = T.isTerm v) := by
  dsimp only [PTrie.stepChar]
  split_ifs with h0
  · dsimp only
    set s := T.numStates
    have hs_pos : 0 < s := hT.one_le
    have hfresh : ∀ v < s, T.strOf v ≠ T.strOf u ++ [a] := fun v hv heq => by
      have := hT.trie_eq_of_strOf hu hv heq
      omega
    refine ⟨?_, by omega, by omega, hs_pos, by omega, Function.update_self s _ T.strOf,
      fun v hv => ⟨Function.update_of_ne (by omega) _ _, rfl⟩⟩
    refine
      { one_le := by dsimp only; omega
        str_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT.str_zero
        depth_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT.depth_zero
        term_zero := hT.term_zero
        str_ne_nil := fun w hw0 hws => by
          dsimp only at hws ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hws) with hlt | rfl
          · rw [Function.update_of_ne (by omega)]; exact hT.str_ne_nil w hw0 hlt
          · rw [Function.update_self]
            exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil a [])
        depth_eq := fun w hws => by
          dsimp only at hws ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hws) with hlt | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hT.depth_eq w hlt
          · rw [Function.update_self, Function.update_self, hT.depth_eq u hu,
              List.length_append, List.length_singleton]
        str_inj := fun x hx y hy hxy => by
          dsimp only at hx hy hxy
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hxl | rfl <;>
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy) with hyl | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hxy
            exact hT.str_inj x hxl y hyl hxy
          · rw [Function.update_of_ne (by omega), Function.update_self] at hxy
            exact absurd hxy (hfresh x hxl)
          · rw [Function.update_self, Function.update_of_ne (by omega)] at hxy
            exact absurd hxy.symm (hfresh y hyl)
          · rfl
        trie_lt := fun x hx c hc => by
          dsimp only at hx ⊢
          split_ifs with hxc
          · omega
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hxl | rfl
            · have := hT.trie_lt x hxl c hc; omega
            · rw [hT.trie_oob s (Nat.le_refl s) c]; omega
        trie_spec := fun x hx c hc => by
          dsimp only at hx ⊢
          split_ifs with hxc
          · obtain ⟨rfl, rfl⟩ := hxc
            refine Or.inr ⟨hs_pos, ?_⟩
            rw [Function.update_self, Function.update_of_ne (by omega)]
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hxl | rfl
            · rcases hT.trie_spec x hxl c hc with hnil | ⟨hpos, hstr⟩
              · exact Or.inl hnil
              · have hlt_s := hT.trie_lt x hxl c hc
                refine Or.inr ⟨hpos, ?_⟩
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hstr
            · exact Or.inl (hT.trie_oob s (Nat.le_refl s) c)
        parent_exists := fun w hw0 hws => by
          dsimp only at hws ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hws) with hwl | rfl
          · obtain ⟨u₀, hu₀w, a₀, ha₀, ht₀, hs₀⟩ := hT.parent_exists w hw0 hwl
            have hne_ua : ¬(u₀ = u ∧ a₀ = a) := by
              rintro ⟨rfl, rfl⟩; omega
            refine ⟨u₀, hu₀w, a₀, ha₀, ?_, ?_⟩
            · simp only [hne_ua, ↓reduceIte]; exact ht₀
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hs₀
          · refine ⟨u, hu, a, ha, by simp, ?_⟩
            rw [Function.update_self, Function.update_of_ne (by omega)]
        trie_oob := fun x hx c => by
          dsimp only at hx ⊢
          have hne : ¬(x = u ∧ c = a) := by omega
          simp only [hne, ↓reduceIte]
          exact hT.trie_oob x (by omega) c
        depth_oob := fun x hx => by
          dsimp only at hx ⊢
          rw [Function.update_of_ne (by omega)]
          exact hT.depth_oob x (by omega)
        term_oob := fun x hx => by
          dsimp only at hx ⊢
          exact hT.term_oob x (by omega) }
  · rcases hT.trie_spec u hu a ha with hnil | ⟨hpos, hstr⟩
    · exact absurd hnil h0
    · exact ⟨hT, Nat.le_refl _, Nat.le_succ _, hpos, hT.trie_lt u hu a ha, hstr,
        fun _ _ => ⟨rfl, rfl⟩⟩

private theorem insertChars_spec {σ : ℕ} :
    ∀ (xs : List ℕ) (T : PTrie) (u : ℕ),
      TreeInv σ T → u < T.numStates → (∀ a ∈ xs, a < σ) →
      let res := T.insertChars u xs
      TreeInv σ res.1 ∧
        T.numStates ≤ res.1.numStates ∧
        res.1.numStates ≤ T.numStates + xs.length ∧
        res.2 < res.1.numStates ∧
        res.1.strOf res.2 = T.strOf u ++ xs ∧
        (xs ≠ [] → 0 < res.2) ∧
        (∀ v < T.numStates, res.1.strOf v = T.strOf v ∧ res.1.isTerm v = T.isTerm v) ∧
        (∀ w, T.numStates ≤ w → w < res.1.numStates →
          res.1.isTerm w = 0 ∧ ∃ q, q ≠ [] ∧ q <+: xs ∧ res.1.strOf w = T.strOf u ++ q) ∧
        (∀ q, q <+: xs → ∃ v < res.1.numStates, res.1.strOf v = T.strOf u ++ q)
  | [], T, u, hT, hu, _ => by
    dsimp only [PTrie.insertChars]
    refine ⟨hT, Nat.le_refl _, by simp, hu, by simp, fun h => absurd rfl h,
      fun _ _ => ⟨rfl, rfl⟩, fun _ hge hlt => by omega, fun q hq => ?_⟩
    rw [List.prefix_nil.mp hq, List.append_nil]
    exact ⟨u, hu, rfl⟩
  | a :: as, T, u, hT, hu, hxs => by
    dsimp only [PTrie.insertChars]
    have ha : a < σ := hxs a List.mem_cons_self
    have has : ∀ b ∈ as, b < σ := fun b hb => hxs b (List.mem_cons_of_mem a hb)
    obtain ⟨hT₁, hle₁, hub₁, hs_pos, hs_lt, hs_str, hpres₁⟩ := stepChar_spec hT hu ha
    set T₁ := (T.stepChar u a).1
    set s := (T.stepChar u a).2
    obtain ⟨hT₂, hle₂, hub₂, hu₂_lt, hu₂_str, hu₂_pos, hpres₂, hnew₂, hpref₂⟩ :=
      insertChars_spec as T₁ s hT₁ hs_lt has
    set T₂ := (T₁.insertChars s as).1
    set u₂ := (T₁.insertChars s as).2
    refine ⟨hT₂, le_trans hle₁ hle₂, by simp only [List.length_cons]; omega, hu₂_lt, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [hu₂_str, hs_str, List.append_assoc, List.singleton_append]
    · intro _
      by_cases hnil : as = []
      · subst hnil
        simpa only [u₂, PTrie.insertChars] using hs_pos
      · exact hu₂_pos hnil
    · intro v hv
      obtain ⟨hs1, ht1⟩ := hpres₁ v hv
      obtain ⟨hs2, ht2⟩ := hpres₂ v (lt_of_lt_of_le hv hle₁)
      exact ⟨hs2.trans hs1, ht2.trans ht1⟩
    · intro w hge hlt
      rcases lt_or_ge w T₁.numStates with hw₁ | hw₁
      · have hw_eq : w = T.numStates := by omega
        have hs_eq : s = w := by
          dsimp only [T₁, s, PTrie.stepChar] at hle₁ hub₁ hs_lt hw₁ ⊢
          split_ifs at hle₁ hub₁ hs_lt hw₁ ⊢ with h0 <;>
            dsimp only at hle₁ hub₁ hs_lt hw₁ ⊢ <;> omega
        obtain ⟨hs2, ht2⟩ := hpres₂ w hw₁
        have ht1_0 : T₁.isTerm w = 0 := by
          dsimp only [T₁, PTrie.stepChar]
          split_ifs
          · exact hT.term_oob w hge
          · exact hT.term_oob w hge
        refine ⟨ht2.trans ht1_0, [a], List.cons_ne_nil a [], List.cons_prefix_cons.mpr
          ⟨rfl, List.nil_prefix⟩, ?_⟩
        rw [hs2, ← hs_eq, hs_str]
      · obtain ⟨ht_0, q', hq'_ne, hq'_pref, hq'_str⟩ := hnew₂ w hw₁ hlt
        refine ⟨ht_0, a :: q', List.cons_ne_nil a q',
          List.cons_prefix_cons.mpr ⟨rfl, hq'_pref⟩, ?_⟩
        rw [hq'_str, hs_str, List.append_assoc, List.singleton_append]
    · intro q hq
      rcases q with _ | ⟨b, q'⟩
      · refine ⟨u, lt_of_lt_of_le hu (le_trans hle₁ hle₂), ?_⟩
        rw [List.append_nil, (hpres₂ u (lt_of_lt_of_le hu hle₁)).1, (hpres₁ u hu).1]
      · obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
        obtain ⟨v, hv, hv_str⟩ := hpref₂ q' hq'
        refine ⟨v, hv, ?_⟩
        rw [hv_str, hs_str, List.append_assoc, List.singleton_append]

private theorem build_trie_spec (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    TreeInv σ (PTrie.build P) ∧
      (PTrie.build P).numStates ≤ totalPatternLen P + 1 ∧
      (∀ u < (PTrie.build P).numStates, IsNode P ((PTrie.build P).strOf u)) ∧
      (∀ w, IsNode P w → ∃ u < (PTrie.build P).numStates, (PTrie.build P).strOf u = w) ∧
      (∀ u < (PTrie.build P).numStates,
        (PTrie.build P).isTerm u =
          if (PTrie.build P).strOf u ≠ [] ∧ (PTrie.build P).strOf u ∈ P then 1 else 0) := by
  suffices ∀ (ps Q : List (List ℕ)) (T : PTrie),
      (∀ p ∈ ps, ∀ a ∈ p, a < σ) →
      TreeInv σ T →
      T.numStates ≤ totalPatternLen Q + 1 →
      (∀ u < T.numStates, IsNode Q (T.strOf u)) →
      (∀ w, IsNode Q w → ∃ u < T.numStates, T.strOf u = w) →
      (∀ u < T.numStates, T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ Q then 1 else 0) →
      TreeInv σ (ps.foldl PTrie.insertPat T) ∧
        (ps.foldl PTrie.insertPat T).numStates ≤ totalPatternLen (Q ++ ps) + 1 ∧
        (∀ u < (ps.foldl PTrie.insertPat T).numStates,
          IsNode (Q ++ ps) ((ps.foldl PTrie.insertPat T).strOf u)) ∧
        (∀ w, IsNode (Q ++ ps) w →
          ∃ u < (ps.foldl PTrie.insertPat T).numStates,
            (ps.foldl PTrie.insertPat T).strOf u = w) ∧
        (∀ u < (ps.foldl PTrie.insertPat T).numStates,
          (ps.foldl PTrie.insertPat T).isTerm u =
            if (ps.foldl PTrie.insertPat T).strOf u ≠ [] ∧
              (ps.foldl PTrie.insertPat T).strOf u ∈ Q ++ ps then 1 else 0) by
    exact this P [] PTrie.init hvalid (treeInv_init σ) (Nat.le_refl 1)
        (fun u hu => by
          simp only [PTrie.init] at hu
          have : u = 0 := by omega
          subst this; exact isNode_nil [])
        (fun w hw => by
          rcases hw with rfl | ⟨_, hp, _⟩
          · exact ⟨0, Nat.zero_lt_one, rfl⟩
          · exact absurd hp List.not_mem_nil)
        (fun u hu => by
          simp only [PTrie.init] at hu
          have : u = 0 := by omega
          subst this; simp [PTrie.init])
  intro ps
  induction ps with
  | nil =>
    intro Q T _ hT hnum hnode hcomp hterm
    simpa only [List.foldl_nil, List.append_nil] using ⟨hT, hnum, hnode, hcomp, hterm⟩
  | cons p ps ih =>
    intro Q T hps hT hnum hnode hcomp hterm
    have hp_val : ∀ a ∈ p, a < σ := hps p List.mem_cons_self
    have hps_val : ∀ q ∈ ps, ∀ a ∈ q, a < σ := fun q hq => hps q (List.mem_cons_of_mem p hq)
    obtain ⟨hT₁, hle₁, hub₁, hu_lt, hu_str, hu_pos, hpres₁, hnew₁, hpref₁⟩ :=
      insertChars_spec p T 0 hT hT.one_le hp_val
    simp only [hT.str_zero, List.nil_append] at hu_str hnew₁ hpref₁
    set T₁ := (T.insertChars 0 p).1
    set u := (T.insertChars 0 p).2
    set T₂ := PTrie.insertPat T p
    have hT₂_str : T₂.strOf = T₁.strOf := by
      dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
    have hT₂_num : T₂.numStates = T₁.numStates := by
      dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
    have hT₂_inv : TreeInv σ T₂ := by
      dsimp only [T₂, PTrie.insertPat]
      split_ifs with hpos
      · refine { hT₁ with
          term_zero := by
            dsimp only; rw [Function.update_of_ne (by omega)]; exact hT₁.term_zero
          term_oob := fun x hx => by
            dsimp only [T₁, u] at hu_lt hx ⊢
            rw [Function.update_of_ne (by omega)]; exact hT₁.term_oob x hx }
      · exact hT₁
    have hnum₂ : T₂.numStates ≤ totalPatternLen (Q ++ [p]) + 1 := by
      rw [hT₂_num]
      have htot : totalPatternLen (Q ++ [p]) = totalPatternLen Q + p.length := by
        simp [totalPatternLen, List.map_append, List.sum_append]
      omega
    have hnode₂ : ∀ v < T₂.numStates, IsNode (Q ++ [p]) (T₂.strOf v) := by
      intro v hv
      rw [hT₂_num] at hv
      rw [hT₂_str]
      rcases lt_or_ge v T.numStates with hv₀ | hv₀
      · rw [(hpres₁ v hv₀).1]
        rcases hnode v hv₀ with hnil | ⟨r, hr, hvr⟩
        · exact Or.inl hnil
        · exact Or.inr ⟨r, List.mem_append_left _ hr, hvr⟩
      · obtain ⟨_, q, _, hqp, hqstr⟩ := hnew₁ v hv₀ hv
        rw [hqstr]
        exact Or.inr ⟨p, List.mem_append_right _ (by simp), hqp⟩
    have hcomp₂ : ∀ w, IsNode (Q ++ [p]) w → ∃ v < T₂.numStates, T₂.strOf v = w := by
      intro w hw
      rw [hT₂_num, hT₂_str]
      rcases hw with rfl | ⟨r, hr, hwr⟩
      · exact ⟨0, hT₁.one_le, hT₁.str_zero⟩
      · rcases List.mem_append.mp hr with hrQ | hrp
        · obtain ⟨v, hv, hvw⟩ := hcomp w (Or.inr ⟨r, hrQ, hwr⟩)
          exact ⟨v, lt_of_lt_of_le hv hle₁, (hpres₁ v hv).1.trans hvw⟩
        · rw [List.mem_singleton.mp hrp] at hwr
          exact hpref₁ w hwr
    have hterm₂ : ∀ v < T₂.numStates,
        T₂.isTerm v = if T₂.strOf v ≠ [] ∧ T₂.strOf v ∈ Q ++ [p] then 1 else 0 := by
      intro v hv
      rw [hT₂_num] at hv
      rw [hT₂_str]
      have hT₂_term : T₂.isTerm v =
          (if 0 < u then Function.update T₁.isTerm u 1 else T₁.isTerm) v := by
        dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
      rw [hT₂_term]
      by_cases hp_nil : p = []
      · subst hp_nil
        have hu0 : u = 0 := by
          dsimp only [u, PTrie.insertChars]
        have hnot_pos : ¬(0 < u) := by omega
        simp only [hnot_pos, ↓reduceIte]
        have hv₀ : v < T.numStates := by
          dsimp only [T₁, PTrie.insertChars] at hv; exact hv
        rw [(hpres₁ v hv₀).2, (hpres₁ v hv₀).1, hterm v hv₀]
        by_cases hne : T.strOf v = []
        · simp [hne]
        · simp [hne, List.mem_append]
      · have hu_p : 0 < u := hu_pos hp_nil
        simp only [hu_p, ↓reduceIte]
        by_cases hvu : v = u
        · subst hvu
          rw [Function.update_self]
          simp [hu_str, hp_nil]
        · rw [Function.update_of_ne hvu]
          have hne_p : T₁.strOf v ≠ p := fun heq =>
            hvu (hT₁.str_inj v hv u hu_lt (heq.trans hu_str.symm))
          rcases lt_or_ge v T.numStates with hv₀ | hv₀
          · rw [(hpres₁ v hv₀).2, hterm v hv₀, ← (hpres₁ v hv₀).1]
            simp [List.mem_append, hne_p]
          · obtain ⟨ht0, _⟩ := hnew₁ v hv₀ hv
            have hnot_Q : T₁.strOf v ∉ Q := by
              intro hmQ
              obtain ⟨w, hw, hws⟩ := hcomp (T₁.strOf v) (isNode_of_mem hmQ)
              have hw_str : T₁.strOf w = T₁.strOf v := (hpres₁ w hw).1.trans hws
              have hweq := hT₁.str_inj w (lt_of_lt_of_le hw hle₁) v hv hw_str
              omega
            rw [ht0]
            simp [List.mem_append, hnot_Q, hne_p]
    have hRes := ih (Q ++ [p]) T₂ hps_val hT₂_inv hnum₂ hnode₂ hcomp₂ hterm₂
    have hqp : (Q ++ [p]) ++ ps = Q ++ p :: ps := by simp
    rw [hqp] at hRes
    exact hRes

private theorem trie_char_iff (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    ∀ u < (PTrie.build P).numStates, ∀ a < σ,
      (IsNode P ((PTrie.build P).strOf u ++ [a]) →
        0 < (PTrie.build P).trie u a ∧
          (PTrie.build P).trie u a < (PTrie.build P).numStates ∧
          (PTrie.build P).strOf ((PTrie.build P).trie u a) = (PTrie.build P).strOf u ++ [a]) ∧
      (¬IsNode P ((PTrie.build P).strOf u ++ [a]) → (PTrie.build P).trie u a = 0) := by
  obtain ⟨hT, _, hnode, hcomp, _⟩ := build_trie_spec P σ hvalid
  intro u hu a ha
  refine ⟨fun his => ?_, fun hnot => ?_⟩
  · obtain ⟨w, hw, hws⟩ := hcomp _ his
    obtain ⟨hw_pos, htw⟩ := hT.trie_eq_of_strOf hu hw hws
    rw [htw]
    exact ⟨hw_pos, hw, hws⟩
  · rcases hT.trie_spec u hu a ha with h0 | ⟨_, hstr⟩
    · exact h0
    · exact absurd (hstr ▸ hnode _ (hT.trie_lt u hu a ha)) hnot

private theorem trie_char_pos_iff (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    ∀ u < (PTrie.build P).numStates, ∀ a < σ,
      IsNode P ((PTrie.build P).strOf u ++ [a]) ↔ 0 < (PTrie.build P).trie u a := by
  intro u hu a ha
  have h := trie_char_iff P σ hvalid u hu a ha
  refine ⟨fun his => (h.1 his).1, fun hpos => ?_⟩
  by_contra hnot
  have h0 := h.2 hnot
  omega


/-! ## Pure BFS failure, next-move, and output-link construction -/

private theorem depth_le_self {σ : ℕ} {T : PTrie} (hT : TreeInv σ T) :
    ∀ w < T.numStates, T.depth w ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases Nat.eq_zero_or_pos w with rfl | hpos
    · rw [hT.depth_zero]
    · obtain ⟨u, huw, a, _, _, hstr⟩ := hT.parent_exists w hpos hw
      have hdu := ih u huw (lt_trans huw hw)
      rw [hT.depth_eq w hw, hstr, List.length_append, List.length_singleton,
        ← hT.depth_eq u (lt_trans huw hw)]
      omega

private theorem parent_unique {σ : ℕ} {T : PTrie} (hT : TreeInv σ T)
    {u₁ c₁ u₂ c₂ : ℕ} (hu₁ : u₁ < T.numStates) (hc₁ : c₁ < σ)
    (hu₂ : u₂ < T.numStates) (hc₂ : c₂ < σ)
    (hpos : 0 < T.trie u₁ c₁) (heq : T.trie u₁ c₁ = T.trie u₂ c₂) :
    u₁ = u₂ ∧ c₁ = c₂ := by
  rcases hT.trie_spec u₁ hu₁ c₁ hc₁ with h0 | ⟨_, hs₁⟩
  · omega
  · rcases hT.trie_spec u₂ hu₂ c₂ hc₂ with h0 | ⟨_, hs₂⟩
    · omega
    · rw [heq] at hs₁
      have hinj := List.append_inj' (hs₁.symm.trans hs₂) rfl
      exact ⟨hT.str_inj u₁ hu₁ u₂ hu₂ hinj.1, List.head_eq_of_cons_eq hinj.2⟩

private def followOut (depth outNext : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, q => if q = 0 then [] else depth q :: followOut depth outNext k (outNext q)

private theorem followOut_zero_right (depth outNext : ℕ → ℕ) :
    ∀ k, followOut depth outNext k 0 = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem followOut_pos (depth outNext : ℕ → ℕ) {k q : ℕ} (hq : 0 < q) :
    followOut depth outNext (k + 1) q = depth q :: followOut depth outNext k (outNext q) := by
  have hne : q ≠ 0 := by omega
  simp only [followOut, hne, ↓reduceIte]

private theorem followOut_congr_on {depth outNext outNext' : ℕ → ℕ} {D : Finset ℕ}
    (hclosed : ∀ x ∈ D, 0 < x → outNext x ∈ D)
    (heq : ∀ x ∈ D, outNext' x = outNext x) :
    ∀ k, ∀ q ∈ D, followOut depth outNext' k q = followOut depth outNext k q
  | 0, _, _ => rfl
  | k + 1, q, hq => by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simp only [followOut_zero_right]
    · rw [followOut_pos _ _ hpos, followOut_pos _ _ hpos, heq q hq,
        followOut_congr_on hclosed heq k (outNext q) (hclosed q hq hpos)]

private theorem followOut_fuel_eq {depth outNext : ℕ → ℕ} {D : Finset ℕ}
    (hstep : ∀ x ∈ D, 0 < x → outNext x ∈ D ∧ (outNext x = 0 ∨ depth (outNext x) < depth x)) :
    ∀ k₁ k₂, ∀ q ∈ D, (q = 0 ∨ depth q < k₁) → (q = 0 ∨ depth q < k₂) →
      followOut depth outNext k₁ q = followOut depth outNext k₂ q
  | 0, k₂, q, _, h₁, _ => by
    rcases h₁ with rfl | hlt
    · simp only [followOut_zero_right]
    · omega
  | k₁ + 1, k₂, q, hq, h₁, h₂ => by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simp only [followOut_zero_right]
    · have hk₁ : depth q < k₁ + 1 := h₁.resolve_left (by omega)
      have hk₂ : depth q < k₂ := h₂.resolve_left (by omega)
      cases k₂ with
      | zero => omega
      | succ m =>
        obtain ⟨hmem', hdec⟩ := hstep q hq hpos
        rw [followOut_pos _ _ hpos, followOut_pos _ _ hpos]
        congr 1
        refine followOut_fuel_eq hstep k₁ m (outNext q) hmem' ?_ ?_
        · rcases hdec with h0 | hlt
          · exact Or.inl h0
          · exact Or.inr (by omega)
        · rcases hdec with h0 | hlt
          · exact Or.inl h0
          · exact Or.inr (by omega)

private structure PBFS where
  delta : ℕ → ℕ → ℕ
  fail : ℕ → ℕ
  outHead : ℕ → ℕ
  outNext : ℕ → ℕ
  queue : ℕ → ℕ
  qHead : ℕ
  qTail : ℕ

private def PBFS.disc (B : PBFS) : Finset ℕ :=
  insert 0 ((Finset.range B.qTail).image B.queue)

private def PBFS.expAt (B : PBFS) (h : ℕ) : Finset ℕ :=
  insert 0 ((Finset.range h).image B.queue)

private def PBFS.init : PBFS where
  delta _ _ := 0
  fail _ := 0
  outHead _ := 0
  outNext _ := 0
  queue _ := 0
  qHead := 0
  qTail := 0

private def PBFS.rootStep (T : PTrie) (B : PBFS) (a : ℕ) : PBFS :=
  let s := T.trie 0 a
  if 0 < s then
    { delta := fun u c => if u = 0 ∧ c = a then s else B.delta u c
      fail := Function.update B.fail s 0
      outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else 0)
      outNext := Function.update B.outNext s 0
      queue := Function.update B.queue B.qTail s
      qHead := B.qHead
      qTail := B.qTail + 1 }
  else
    { B with delta := fun u c => if u = 0 ∧ c = a then 0 else B.delta u c }

private def PBFS.rootLoop (T : PTrie) : ℕ → ℕ → PBFS → PBFS
  | 0, _, B => B
  | k + 1, a, B => PBFS.rootLoop T k (a + 1) (PBFS.rootStep T B a)

private def PBFS.innerStep (T : PTrie) (r fr : ℕ) (B : PBFS) (a : ℕ) : PBFS :=
  let s := T.trie r a
  let df := B.delta fr a
  if 0 < s then
    let oh := B.outHead df
    { delta := fun u c => if u = r ∧ c = a then s else B.delta u c
      fail := Function.update B.fail s df
      outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else oh)
      outNext := Function.update B.outNext s oh
      queue := Function.update B.queue B.qTail s
      qHead := B.qHead
      qTail := B.qTail + 1 }
  else
    { B with delta := fun u c => if u = r ∧ c = a then df else B.delta u c }

private def PBFS.innerLoop (T : PTrie) (r fr : ℕ) : ℕ → ℕ → PBFS → PBFS
  | 0, _, B => B
  | k + 1, a, B => PBFS.innerLoop T r fr k (a + 1) (PBFS.innerStep T r fr B a)

private def PBFS.outerLoop (T : PTrie) (σ : ℕ) : ℕ → PBFS → PBFS
  | 0, B => B
  | fuel + 1, B =>
    if B.qHead < B.qTail then
      let r := B.queue B.qHead
      let fr := B.fail r
      let B₁ := { B with qHead := B.qHead + 1 }
      let B₂ := PBFS.innerLoop T r fr σ 0 B₁
      PBFS.outerLoop T σ fuel B₂
    else B

private def PBFS.build (T : PTrie) (σ : ℕ) : PBFS :=
  PBFS.outerLoop T σ T.numStates (PBFS.rootLoop T σ 0 PBFS.init)

private theorem card_disc {B : PBFS}
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i)
    (hq_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j) :
    B.disc.card = B.qTail + 1 := by
  dsimp only [PBFS.disc]
  have h0 : 0 ∉ (Finset.range B.qTail).image B.queue := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi heq
    have := hq_pos i hi
    omega
  rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hq_inj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij

private theorem qTail_lt_numStates {N : ℕ} {B : PBFS} (hN : 1 ≤ N)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < N)
    (hq_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j) :
    B.qTail < N := by
  have hsub : B.disc ⊆ Finset.range N := by
    intro x hx
    simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hx ⊢
    rcases hx with rfl | ⟨i, hi, rfl⟩
    · exact hN
    · exact (hq_pos i hi).2
  have hle := Finset.card_le_card hsub
  rw [card_disc (fun i hi => (hq_pos i hi).1) hq_inj, Finset.card_range] at hle
  omega

private theorem qTail_succ_lt_numStates {N s : ℕ} {B : PBFS} (hN : 1 ≤ N)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < N)
    (hq_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j)
    (hs_lt : s < N) (hs_not : s ∉ B.disc) :
    B.qTail + 1 < N := by
  have hsub : insert s B.disc ⊆ Finset.range N := by
    intro x hx
    simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hx ⊢
    rcases hx with rfl | rfl | ⟨i, hi, rfl⟩
    · exact hs_lt
    · exact hN
    · exact (hq_pos i hi).2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hs_not,
    card_disc (fun i hi => (hq_pos i hi).1) hq_inj, Finset.card_range] at hle
  omega

private theorem mem_disc_lt {N : ℕ} {B : PBFS} (hN : 1 ≤ N)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < N) {x : ℕ} (hx : x ∈ B.disc) :
    x < N := by
  simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hx
  rcases hx with rfl | ⟨i, hi, rfl⟩
  · exact hN
  · exact (hq_pos i hi).2

private structure TablesInv (P : List (List ℕ)) (T : PTrie) (B : PBFS) : Prop where
  zero_vals : B.fail 0 = 0 ∧ B.outHead 0 = 0 ∧ B.outNext 0 = 0
  fail_spec : ∀ x ∈ B.disc, 0 < x → B.fail x ∈ B.disc ∧ T.strOf (B.fail x) = failure P (T.strOf x)
  outHead_spec : ∀ x ∈ B.disc, B.outHead x ∈ B.disc ∧ T.depth (B.outHead x) ≤ T.depth x
  outNext_spec : ∀ x ∈ B.disc, 0 < x →
    B.outNext x ∈ B.disc ∧ (B.outNext x = 0 ∨ T.depth (B.outNext x) < T.depth x)
  follow_spec : ∀ x ∈ B.disc,
    followOut T.depth B.outNext T.numStates (B.outHead x) =
      (output P (T.strOf x)).map List.length

private theorem tablesInv_push {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {B B' : PBFS} (htab : TablesInv P T B)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates)
    {s df : ℕ} (hs_pos : 0 < s) (hs_lt : s < T.numStates) (hs_not : s ∉ B.disc)
    (hdf_disc : df ∈ B.disc) (hdf_str : T.strOf df = failure P (T.strOf s))
    (hdisc' : B'.disc = insert s B.disc)
    (hfail' : B'.fail = Function.update B.fail s df)
    (houtHead' : B'.outHead =
      Function.update B.outHead s (if 0 < T.isTerm s then s else B.outHead df))
    (houtNext' : B'.outNext = Function.update B.outNext s (B.outHead df)) :
    TablesInv P T B' := by
  have h0_disc : 0 ∈ B.disc := Finset.mem_insert_self 0 _
  have hs_ne0 : s ≠ 0 := by omega
  have hdf_lt : df < T.numStates := mem_disc_lt hT.one_le hq_pos hdf_disc
  have hs_str_ne : T.strOf s ≠ [] := hT.str_ne_nil s hs_pos hs_lt
  have hdf_depth_lt : T.depth df < T.depth s := by
    rw [hT.depth_eq df hdf_lt, hT.depth_eq s hs_lt, hdf_str]
    exact length_failure_lt P hs_str_ne
  obtain ⟨hoh_disc, hoh_depth⟩ := htab.outHead_spec df hdf_disc
  have hoh_lt : B.outHead df < T.numStates := mem_disc_lt hT.one_le hq_pos hoh_disc
  have hcongr : ∀ k, ∀ q ∈ B.disc,
      followOut T.depth B'.outNext k q = followOut T.depth B.outNext k q := by
    refine followOut_congr_on (fun x hx hxp => (htab.outNext_spec x hx hxp).1) ?_
    intro x hx
    rw [houtNext', Function.update_of_ne (by rintro rfl; exact hs_not hx)]
  refine
    { zero_vals := ?_
      fail_spec := ?_
      outHead_spec := ?_
      outNext_spec := ?_
      follow_spec := ?_ }
  · rw [hfail', houtHead', houtNext', Function.update_of_ne hs_ne0.symm,
      Function.update_of_ne hs_ne0.symm, Function.update_of_ne hs_ne0.symm]
    exact htab.zero_vals
  · intro x hx hxp
    rw [hdisc'] at hx ⊢
    rw [hfail']
    rcases Finset.mem_insert.mp hx with rfl | hx_old
    · rw [Function.update_self]
      exact ⟨Finset.mem_insert_of_mem hdf_disc, hdf_str⟩
    · rw [Function.update_of_ne (by rintro rfl; exact hs_not hx_old)]
      obtain ⟨hf_d, hf_s⟩ := htab.fail_spec x hx_old hxp
      exact ⟨Finset.mem_insert_of_mem hf_d, hf_s⟩
  · intro x hx
    rw [hdisc'] at hx ⊢
    rw [houtHead']
    rcases Finset.mem_insert.mp hx with hxs | hx_old
    · subst x
      rw [Function.update_self]
      split_ifs
      · exact ⟨Finset.mem_insert_self s _, Nat.le_refl _⟩
      · exact ⟨Finset.mem_insert_of_mem hoh_disc, by omega⟩
    · rw [Function.update_of_ne (by rintro rfl; exact hs_not hx_old)]
      obtain ⟨h1, h2⟩ := htab.outHead_spec x hx_old
      exact ⟨Finset.mem_insert_of_mem h1, h2⟩
  · intro x hx hxp
    rw [hdisc'] at hx ⊢
    rw [houtNext']
    rcases Finset.mem_insert.mp hx with rfl | hx_old
    · rw [Function.update_self]
      refine ⟨Finset.mem_insert_of_mem hoh_disc, Or.inr (by omega)⟩
    · rw [Function.update_of_ne (by rintro rfl; exact hs_not hx_old)]
      obtain ⟨h1, h2⟩ := htab.outNext_spec x hx_old hxp
      exact ⟨Finset.mem_insert_of_mem h1, h2⟩
  · intro x hx
    rw [hdisc'] at hx
    rcases Finset.mem_insert.mp hx with hxs | hx_old
    · subst x
      rw [houtHead', Function.update_self]
      have hterm_s := hterm s hs_lt
      simp only [hs_str_ne, ne_eq, not_false_eq_true, true_and] at hterm_s
      rw [output_eq_of_ne_nil P hs_str_ne, List.map_append, ← hdf_str]
      by_cases hmemP : T.strOf s ∈ P
      · simp only [hmemP, ↓reduceIte] at hterm_s ⊢
        simp only [hterm_s, Nat.zero_lt_one, ↓reduceIte, List.map_cons, List.map_nil,
          List.singleton_append]
        have hs_depth_lt : T.depth s < T.numStates :=
          lt_of_le_of_lt (depth_le_self hT s hs_lt) hs_lt
        cases hN : T.numStates with
        | zero => omega
        | succ m =>
          rw [followOut_pos _ _ hs_pos, houtNext', Function.update_self, ← houtNext',
            hcongr m (B.outHead df) hoh_disc, ← hT.depth_eq s hs_lt]
          congr 1
          have hfuel := followOut_fuel_eq
            (fun y hy hyp => htab.outNext_spec y hy hyp)
            m T.numStates (B.outHead df) hoh_disc
            (Or.inr (by omega))
            (Or.inr (lt_of_le_of_lt (depth_le_self hT _ hoh_lt) hoh_lt))
          rw [hfuel, htab.follow_spec df hdf_disc]
      · simp only [hmemP, ↓reduceIte] at hterm_s ⊢
        simp only [hterm_s, lt_self_iff_false, ↓reduceIte, List.map_nil, List.nil_append]
        rw [hcongr T.numStates (B.outHead df) hoh_disc, htab.follow_spec df hdf_disc]
    · rw [houtHead', Function.update_of_ne (by rintro rfl; exact hs_not hx_old),
        hcongr T.numStates (B.outHead x) (htab.outHead_spec x hx_old).1,
        htab.follow_spec x hx_old]

private theorem disc_push_queue (B : PBFS) (s : ℕ) :
    PBFS.disc { B with queue := Function.update B.queue B.qTail s, qTail := B.qTail + 1 } =
      insert s B.disc := by
  ext x
  simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · rw [Function.update_of_ne (by omega)]
        exact Or.inr (Or.inr ⟨i, hlt, rfl⟩)
      · rw [Function.update_self]
        exact Or.inl rfl
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
    · refine Or.inr ⟨B.qTail, Nat.lt_succ_self _, ?_⟩
      rw [Function.update_self]
    · exact Or.inl rfl
    · refine Or.inr ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      rw [Function.update_of_ne (by omega)]

private structure RootLoopInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie) (a : ℕ) (B : PBFS) :
    Prop where
  qHead_zero : B.qHead = 0
  q_bounds : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates ∧ T.depth (B.queue i) = 1
  q_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j
  disc_iff : ∀ w < T.numStates, w ∈ B.disc ↔ w = 0 ∨ ∃ c < a, T.trie 0 c = w
  delta_zero : ∀ c < a, B.delta 0 c ∈ B.disc ∧ T.strOf (B.delta 0 c) = nextMove P [] c
  tables : TablesInv P T B

private theorem rootStep_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {a : ℕ} (ha : a < σ) {B : PBFS} (hinv : RootLoopInv P σ T a B) :
    RootLoopInv P σ T (a + 1) (PBFS.rootStep T B a) := by
  have htrie_iff := hchar 0 hT.one_le a ha
  rw [hT.str_zero, List.nil_append] at htrie_iff
  dsimp only [PBFS.rootStep]
  set s := T.trie 0 a
  by_cases hs_pos : 0 < s
  · simp only [hs_pos, ↓reduceIte]
    have hs_lt : s < T.numStates := hT.trie_lt 0 hT.one_le a ha
    rcases hT.trie_spec 0 hT.one_le a ha with h0 | ⟨_, hs_str⟩
    · omega
    · rw [hT.str_zero, List.nil_append] at hs_str
      have hs_depth : T.depth s = 1 := by
        rw [hT.depth_eq s hs_lt, hs_str, List.length_singleton]
      have hs_not : s ∉ B.disc := by
        intro hmem
        rcases (hinv.disc_iff s hs_lt).mp hmem with hs0 | ⟨c, hca, htc⟩
        · omega
        · have ⟨_, hceq⟩ :=
            parent_unique hT hT.one_le ha hT.one_le (lt_trans hca ha) hs_pos htc.symm
          omega
      set B' : PBFS :=
        { delta := fun u c => if u = 0 ∧ c = a then s else B.delta u c
          fail := Function.update B.fail s 0
          outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else 0)
          outNext := Function.update B.outNext s 0
          queue := Function.update B.queue B.qTail s
          qHead := B.qHead
          qTail := B.qTail + 1 }
      have hdisc' : B'.disc = insert s B.disc := disc_push_queue B s
      have hnode_a : IsNode P [a] := htrie_iff.mpr hs_pos
      have hfail_s : T.strOf 0 = failure P (T.strOf s) := by
        rw [hT.str_zero, hs_str, failure_eq_nil_of_length_le_one P (by simp)]
      refine
        { qHead_zero := hinv.qHead_zero
          q_bounds := fun i hi => by
            dsimp only [B'] at hi ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
            · rw [Function.update_of_ne (by omega)]
              exact hinv.q_bounds i hlt
            · rw [Function.update_self]
              exact ⟨hs_pos, hs_lt, hs_depth⟩
          q_inj := fun i hi j hj hij => by
            dsimp only [B'] at hi hj hij
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl <;>
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hij
              exact hinv.q_inj i hil j hjl hij
            · rw [Function.update_of_ne (by omega), Function.update_self] at hij
              exfalso; apply hs_not
              rw [← hij]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hil, rfl⟩)
            · rw [Function.update_self, Function.update_of_ne (by omega)] at hij
              exfalso; apply hs_not
              rw [hij]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjl, rfl⟩)
            · rfl
          disc_iff := fun w hw => by
            rw [hdisc', Finset.mem_insert, hinv.disc_iff w hw]
            constructor
            · rintro (rfl | rfl | ⟨c, hca, htc⟩)
              · exact Or.inr ⟨a, Nat.lt_succ_self a, rfl⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨c, Nat.lt_succ_of_lt hca, htc⟩
            · rintro (rfl | ⟨c, hca, htc⟩)
              · exact Or.inr (Or.inl rfl)
              · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hca) with hlt | rfl
                · exact Or.inr (Or.inr ⟨c, hlt, htc⟩)
                · exact Or.inl htc.symm
          delta_zero := fun c hc => by
            rw [hdisc']
            dsimp only [B']
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
            · have hne : c ≠ a := by omega
              simp only [true_and, hne, ↓reduceIte]
              obtain ⟨hd1, hd2⟩ := hinv.delta_zero c hlt
              exact ⟨Finset.mem_insert_of_mem hd1, hd2⟩
            · simp only [and_self, ↓reduceIte]
              refine ⟨Finset.mem_insert_self s _, ?_⟩
              rw [hs_str, nextMove_of_isNode (by simpa using hnode_a), List.nil_append]
          tables := tablesInv_push hT hterm hinv.tables
            (fun i hi => ⟨(hinv.q_bounds i hi).1, (hinv.q_bounds i hi).2.1⟩)
            hs_pos hs_lt hs_not (Finset.mem_insert_self 0 _) hfail_s hdisc' rfl
            (by dsimp only [B']; rw [hinv.tables.zero_vals.2.1])
            (by dsimp only [B']; rw [hinv.tables.zero_vals.2.1]) }
  · simp only [hs_pos, ↓reduceIte]
    have hs0 : s = 0 := by omega
    have hnot_node : ¬IsNode P ([] ++ [a]) := by
      simpa only [List.nil_append] using mt htrie_iff.mp hs_pos
    refine
      { qHead_zero := hinv.qHead_zero
        q_bounds := hinv.q_bounds
        q_inj := hinv.q_inj
        disc_iff := fun w hw => by
          change w ∈ B.disc ↔ _
          rw [hinv.disc_iff w hw]
          constructor
          · rintro (rfl | ⟨c, hca, htc⟩)
            · exact Or.inl rfl
            · exact Or.inr ⟨c, Nat.lt_succ_of_lt hca, htc⟩
          · rintro (rfl | ⟨c, hca, htc⟩)
            · exact Or.inl rfl
            · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hca) with hlt | rfl
              · exact Or.inr ⟨c, hlt, htc⟩
              · exact Or.inl (htc.symm.trans hs0)
        delta_zero := fun c hc => by
          change (if 0 = 0 ∧ c = a then 0 else B.delta 0 c) ∈ B.disc ∧ _
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
          · have hne : c ≠ a := by omega
            simp only [true_and, hne, ↓reduceIte]
            exact hinv.delta_zero c hlt
          · simp only [and_self, ↓reduceIte]
            refine ⟨Finset.mem_insert_self 0 _, ?_⟩
            rw [hT.str_zero, nextMove_of_not_isNode_of_eq_nil hnot_node rfl]
        tables := ⟨hinv.tables.zero_vals, hinv.tables.fail_spec, hinv.tables.outHead_spec,
          hinv.tables.outNext_spec, hinv.tables.follow_spec⟩ }

private theorem rootLoop_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0) :
    ∀ k a B, a + k ≤ σ → RootLoopInv P σ T a B →
      RootLoopInv P σ T (a + k) (PBFS.rootLoop T k a B)
  | 0, a, B, _, hinv => by simpa only [PBFS.rootLoop, Nat.add_zero] using hinv
  | k + 1, a, B, hle, hinv => by
    have hstep := rootStep_spec hT hchar hterm (by omega) hinv
    have ih := rootLoop_spec hT hchar hterm k (a + 1) (PBFS.rootStep T B a) (by omega) hstep
    rwa [Nat.add_right_comm, ← PBFS.rootLoop] at ih

private structure BFSInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie) (B : PBFS) : Prop where
  qHead_le : B.qHead ≤ B.qTail
  q_bounds : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates
  q_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j
  disc_iff : ∀ w < T.numStates,
    w ∈ B.disc ↔ w = 0 ∨ ∃ u ∈ B.expAt B.qHead, ∃ c < σ, T.trie u c = w
  q_mono : ∀ i j, i ≤ j → j < B.qTail → T.depth (B.queue i) ≤ T.depth (B.queue j)
  q_depth_ub : ∀ j < B.qTail, B.qHead < B.qTail →
    T.depth (B.queue j) ≤ T.depth (B.queue B.qHead) + 1
  lt_depth_mem_exp : ∀ v < T.numStates, B.qHead < B.qTail →
    T.depth v < T.depth (B.queue B.qHead) → v ∈ B.expAt B.qHead
  delta_spec : ∀ u ∈ B.expAt B.qHead, ∀ c < σ,
    B.delta u c ∈ B.disc ∧ T.strOf (B.delta u c) = nextMove P (T.strOf u) c
  tables : TablesInv P T B

private structure InnerLoopInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie)
    (qHead₀ r fr a : ℕ) (B : PBFS) : Prop where
  qHead_eq : B.qHead = qHead₀ + 1
  qHead_le : B.qHead ≤ B.qTail
  r_eq : B.queue qHead₀ = r
  q_bounds : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates
  q_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j
  disc_iff : ∀ w < T.numStates,
    w ∈ B.disc ↔ w = 0 ∨ (∃ u ∈ B.expAt qHead₀, ∃ c < σ, T.trie u c = w) ∨
      (∃ c < a, T.trie r c = w)
  q_mono : ∀ i j, i ≤ j → j < B.qTail → T.depth (B.queue i) ≤ T.depth (B.queue j)
  q_depth_ub : ∀ j < B.qTail, T.depth (B.queue j) ≤ T.depth r + 1
  lt_depth_mem_exp : ∀ v < T.numStates, T.depth v < T.depth r → v ∈ B.expAt qHead₀
  le_depth_mem_disc : ∀ v < T.numStates, T.depth v ≤ T.depth r → v ∈ B.disc
  delta_exp : ∀ u ∈ B.expAt qHead₀, ∀ c < σ,
    B.delta u c ∈ B.disc ∧ T.strOf (B.delta u c) = nextMove P (T.strOf u) c
  delta_r : ∀ c < a, B.delta r c ∈ B.disc ∧ T.strOf (B.delta r c) = nextMove P (T.strOf r) c
  fr_mem : fr ∈ B.expAt qHead₀
  fr_str : T.strOf fr = failure P (T.strOf r)
  tables : TablesInv P T B

private theorem expAt_congr {B B' : PBFS} {h : ℕ} (heq : ∀ i < h, B'.queue i = B.queue i) :
    B'.expAt h = B.expAt h := by
  ext x
  simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨i, hi, hq⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hi, (heq i hi).symm.trans hq⟩
  · rintro (rfl | ⟨i, hi, hq⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hi, (heq i hi).trans hq⟩

private theorem innerStep_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {qHead₀ r fr a : ℕ} (ha : a < σ) {B : PBFS}
    (hinv : InnerLoopInv P σ T qHead₀ r fr a B) :
    InnerLoopInv P σ T qHead₀ r fr (a + 1) (PBFS.innerStep T r fr B a) := by
  have hqh_eq := hinv.qHead_eq
  have hqh_le := hinv.qHead_le
  have hqh_lt : qHead₀ < B.qTail := by omega
  obtain ⟨hr_pos, hr_lt⟩ := by
    have h := hinv.q_bounds qHead₀ hqh_lt
    rwa [hinv.r_eq] at h
  have hr_ne_nil : T.strOf r ≠ [] := hT.str_ne_nil r hr_pos hr_lt
  have hr_not_exp : r ∉ B.expAt qHead₀ := by
    simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or,
      not_exists, not_and]
    refine ⟨by omega, fun i hi hqi => ?_⟩
    have := hinv.q_inj i (lt_trans hi hqh_lt) qHead₀ hqh_lt (hqi.trans hinv.r_eq.symm)
    omega
  have hr_ne_fr : r ≠ fr := fun h => hr_not_exp (h ▸ hinv.fr_mem)
  obtain ⟨hdf_disc_raw, hdf_str_raw⟩ := hinv.delta_exp fr hinv.fr_mem a ha
  set df := B.delta fr a
  have hdf_lt : df < T.numStates := mem_disc_lt hT.one_le hinv.q_bounds hdf_disc_raw
  have hdf_fail_ra : T.strOf df = failure P (T.strOf r ++ [a]) := by
    rw [hdf_str_raw, hinv.fr_str, failure_append_singleton P hr_ne_nil a]
  have htrie_iff := hchar r hr_lt a ha
  dsimp only [PBFS.innerStep]
  set s := T.trie r a
  by_cases hs_pos : 0 < s
  · simp only [hs_pos, ↓reduceIte]
    have hs_lt : s < T.numStates := hT.trie_lt r hr_lt a ha
    rcases hT.trie_spec r hr_lt a ha with h0 | ⟨_, hs_str⟩
    · omega
    · have hs_depth : T.depth s = T.depth r + 1 := by
        rw [hT.depth_eq s hs_lt, hs_str, List.length_append, List.length_singleton,
          ← hT.depth_eq r hr_lt]
      have hs_not : s ∉ B.disc := by
        intro hmem
        rcases (hinv.disc_iff s hs_lt).mp hmem with hs0 | ⟨u, hu_exp, c, hc, htuc⟩ | ⟨c, hca, htrc⟩
        · omega
        · have hu_lt : u < T.numStates := by
            simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hu_exp
            rcases hu_exp with rfl | ⟨i, hi, rfl⟩
            · exact hT.one_le
            · exact (hinv.q_bounds i (lt_trans hi hqh_lt)).2
          have ⟨hru, _⟩ := parent_unique hT hr_lt ha hu_lt hc hs_pos htuc.symm
          exact hr_not_exp (hru ▸ hu_exp)
        · have ⟨_, hca_eq⟩ :=
            parent_unique hT hr_lt ha hr_lt (lt_trans hca ha) hs_pos htrc.symm
          omega
      set oh := B.outHead df
      set B' : PBFS :=
        { delta := fun u c => if u = r ∧ c = a then s else B.delta u c
          fail := Function.update B.fail s df
          outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else oh)
          outNext := Function.update B.outNext s oh
          queue := Function.update B.queue B.qTail s
          qHead := B.qHead
          qTail := B.qTail + 1 }
      have hdisc' : B'.disc = insert s B.disc := disc_push_queue B s
      have hexp' : B'.expAt qHead₀ = B.expAt qHead₀ :=
        expAt_congr fun i hi => Function.update_of_ne (by omega) _ _
      have hnode_ra : IsNode P (T.strOf r ++ [a]) := htrie_iff.mpr hs_pos
      refine
        { qHead_eq := hinv.qHead_eq
          qHead_le := by dsimp only [B']; omega
          r_eq := by
            dsimp only [B']
            rw [Function.update_of_ne (by omega)]
            exact hinv.r_eq
          q_bounds := fun i hi => by
            dsimp only [B'] at hi ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
            · rw [Function.update_of_ne (by omega)]; exact hinv.q_bounds i hlt
            · rw [Function.update_self]; exact ⟨hs_pos, hs_lt⟩
          q_inj := fun i hi j hj hij => by
            dsimp only [B'] at hi hj hij
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl <;>
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hij
              exact hinv.q_inj i hil j hjl hij
            · rw [Function.update_of_ne (by omega), Function.update_self] at hij
              exfalso; apply hs_not; rw [← hij]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hil, rfl⟩)
            · rw [Function.update_self, Function.update_of_ne (by omega)] at hij
              exfalso; apply hs_not; rw [hij]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjl, rfl⟩)
            · rfl
          disc_iff := fun w hw => by
            rw [hdisc', hexp', Finset.mem_insert, hinv.disc_iff w hw]
            constructor
            · rintro (rfl | rfl | hexp | ⟨c, hca, htc⟩)
              · exact Or.inr (Or.inr ⟨a, Nat.lt_succ_self a, rfl⟩)
              · exact Or.inl rfl
              · exact Or.inr (Or.inl hexp)
              · exact Or.inr (Or.inr ⟨c, Nat.lt_succ_of_lt hca, htc⟩)
            · rintro (rfl | hexp | ⟨c, hca, htc⟩)
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl hexp))
              · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hca) with hlt | rfl
                · exact Or.inr (Or.inr (Or.inr ⟨c, hlt, htc⟩))
                · exact Or.inl htc.symm
          q_mono := fun i j hij hj => by
            dsimp only [B'] at hj ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hinv.q_mono i j hij hjl
            · rcases Nat.lt_or_eq_of_le hij with hil | rfl
              · rw [Function.update_of_ne (by omega), Function.update_self, hs_depth]
                exact hinv.q_depth_ub i hil
              · exact Nat.le_refl _
          q_depth_ub := fun j hj => by
            dsimp only [B'] at hj ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega)]; exact hinv.q_depth_ub j hjl
            · rw [Function.update_self, hs_depth]
          lt_depth_mem_exp := fun v hv hdv => by
            rw [hexp']; exact hinv.lt_depth_mem_exp v hv hdv
          le_depth_mem_disc := fun v hv hdv => by
            rw [hdisc']; exact Finset.mem_insert_of_mem (hinv.le_depth_mem_disc v hv hdv)
          delta_exp := fun u hu c hc => by
            change u ∈ B'.expAt qHead₀ at hu
            rw [hexp'] at hu
            rw [hdisc']
            dsimp only [B']
            have hur : ¬(u = r ∧ c = a) := fun h => hr_not_exp (h.1 ▸ hu)
            simp only [hur, ↓reduceIte]
            obtain ⟨h1, h2⟩ := hinv.delta_exp u hu c hc
            exact ⟨Finset.mem_insert_of_mem h1, h2⟩
          delta_r := fun c hc => by
            rw [hdisc']
            dsimp only [B']
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
            · have hne : c ≠ a := by omega
              simp only [true_and, hne, ↓reduceIte]
              obtain ⟨h1, h2⟩ := hinv.delta_r c hlt
              exact ⟨Finset.mem_insert_of_mem h1, h2⟩
            · simp only [and_self, ↓reduceIte]
              refine ⟨Finset.mem_insert_self s _, ?_⟩
              rw [hs_str, nextMove_of_isNode hnode_ra]
          fr_mem := by
            rw [hexp']; exact hinv.fr_mem
          fr_str := hinv.fr_str
          tables := tablesInv_push hT hterm hinv.tables hinv.q_bounds
            hs_pos hs_lt hs_not hdf_disc_raw (hs_str ▸ hdf_fail_ra) hdisc' rfl rfl rfl }
  · simp only [hs_pos, ↓reduceIte]
    have hs0 : s = 0 := by omega
    have hnot_node : ¬IsNode P (T.strOf r ++ [a]) := mt htrie_iff.mp hs_pos
    refine
      { qHead_eq := hinv.qHead_eq
        qHead_le := hinv.qHead_le
        r_eq := hinv.r_eq
        q_bounds := hinv.q_bounds
        q_inj := hinv.q_inj
        disc_iff := fun w hw => by
          change w ∈ B.disc ↔ _
          rw [hinv.disc_iff w hw]
          constructor
          · rintro (rfl | hexp | ⟨c, hca, htc⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hexp)
            · exact Or.inr (Or.inr ⟨c, Nat.lt_succ_of_lt hca, htc⟩)
          · rintro (rfl | hexp | ⟨c, hca, htc⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hexp)
            · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hca) with hlt | rfl
              · exact Or.inr (Or.inr ⟨c, hlt, htc⟩)
              · exact Or.inl (htc.symm.trans hs0)
        q_mono := hinv.q_mono
        q_depth_ub := hinv.q_depth_ub
        lt_depth_mem_exp := hinv.lt_depth_mem_exp
        le_depth_mem_disc := hinv.le_depth_mem_disc
        delta_exp := fun u hu c hc => by
          change (if u = r ∧ c = a then df else B.delta u c) ∈ B.disc ∧ _
          have hur : ¬(u = r ∧ c = a) := fun h => hr_not_exp (h.1 ▸ hu)
          simp only [hur, ↓reduceIte]
          exact hinv.delta_exp u hu c hc
        delta_r := fun c hc => by
          change (if r = r ∧ c = a then df else B.delta r c) ∈ B.disc ∧ _
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
          · have hne : c ≠ a := by omega
            simp only [true_and, hne, ↓reduceIte]
            exact hinv.delta_r c hlt
          · simp only [and_self, ↓reduceIte]
            refine ⟨hdf_disc_raw, ?_⟩
            rw [hdf_str_raw, hinv.fr_str, nextMove_of_not_isNode hnot_node hr_ne_nil]
        fr_mem := hinv.fr_mem
        fr_str := hinv.fr_str
        tables := ⟨hinv.tables.zero_vals, hinv.tables.fail_spec, hinv.tables.outHead_spec,
          hinv.tables.outNext_spec, hinv.tables.follow_spec⟩ }

private theorem innerLoop_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    (qHead₀ r fr : ℕ) :
    ∀ k a B, a + k ≤ σ → InnerLoopInv P σ T qHead₀ r fr a B →
      InnerLoopInv P σ T qHead₀ r fr (a + k) (PBFS.innerLoop T r fr k a B)
  | 0, a, B, _, hinv => by simpa only [PBFS.innerLoop, Nat.add_zero] using hinv
  | k + 1, a, B, hle, hinv => by
    have hstep := innerStep_spec hT hchar hterm (by omega) hinv
    have ih :=
      innerLoop_spec hT hchar hterm qHead₀ r fr k (a + 1) (PBFS.innerStep T r fr B a)
        (by omega) hstep
    rwa [Nat.add_right_comm, ← PBFS.innerLoop] at ih

private theorem le_depth_mem_disc_of_bfsInv {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T) {B : PBFS} (hinv : BFSInv P σ T B) (hlt : B.qHead < B.qTail) :
    ∀ v < T.numStates, T.depth v ≤ T.depth (B.queue B.qHead) → v ∈ B.disc := by
  intro v hv hdv
  rcases Nat.eq_zero_or_pos v with rfl | hv_pos
  · exact Finset.mem_insert_self 0 _
  · obtain ⟨u, huv, c, hc, htuc, hstr⟩ := hT.parent_exists v hv_pos hv
    have hu_lt : u < T.numStates := lt_trans huv hv
    have hdu : T.depth u < T.depth (B.queue B.qHead) := by
      rw [hT.depth_eq v hv, hstr, List.length_append, List.length_singleton,
        ← hT.depth_eq u hu_lt] at hdv
      omega
    have hu_exp := hinv.lt_depth_mem_exp u hu_lt hlt hdu
    exact (hinv.disc_iff v hv).mpr (Or.inr ⟨u, hu_exp, c, hc, htuc⟩)

private theorem expAt_succ (B : PBFS) (h : ℕ) :
    B.expAt (h + 1) = insert (B.queue h) (B.expAt h) := by
  ext x
  simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact Or.inr (Or.inr ⟨i, hlt, rfl⟩)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
    · exact Or.inr ⟨h, Nat.lt_succ_self h, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

private theorem innerLoopInv_of_bfsInv {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T) {B : PBFS} (hinv : BFSInv P σ T B) (hlt : B.qHead < B.qTail) :
    InnerLoopInv P σ T B.qHead (B.queue B.qHead) (B.fail (B.queue B.qHead)) 0
      { B with qHead := B.qHead + 1 } := by
  set qh := B.qHead
  set r := B.queue qh
  set fr := B.fail r
  obtain ⟨hr_pos, hr_lt⟩ := hinv.q_bounds qh hlt
  have hr_disc : r ∈ B.disc :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨qh, Finset.mem_range.mpr hlt, rfl⟩)
  obtain ⟨hfr_disc, hfr_str⟩ := hinv.tables.fail_spec r hr_disc hr_pos
  have hfr_lt : fr < T.numStates := mem_disc_lt hT.one_le hinv.q_bounds hfr_disc
  have hfr_depth : T.depth fr < T.depth r := by
    rw [hT.depth_eq fr hfr_lt, hT.depth_eq r hr_lt, hfr_str]
    exact length_failure_lt P (hT.str_ne_nil r hr_pos hr_lt)
  have hfr_exp : fr ∈ B.expAt qh := hinv.lt_depth_mem_exp fr hfr_lt hlt hfr_depth
  exact
    { qHead_eq := rfl
      qHead_le := by dsimp only; omega
      r_eq := rfl
      q_bounds := hinv.q_bounds
      q_inj := hinv.q_inj
      disc_iff := fun w hw => by
        change w ∈ B.disc ↔ _
        rw [hinv.disc_iff w hw]
        simp only [Nat.not_lt_zero, false_and, exists_false, or_false]
        rfl
      q_mono := hinv.q_mono
      q_depth_ub := fun j hj => hinv.q_depth_ub j hj hlt
      lt_depth_mem_exp := fun v hv hdv => hinv.lt_depth_mem_exp v hv hlt hdv
      le_depth_mem_disc := le_depth_mem_disc_of_bfsInv hT hinv hlt
      delta_exp := hinv.delta_spec
      delta_r := fun _ hc => absurd hc (Nat.not_lt_zero _)
      fr_mem := hfr_exp
      fr_str := hfr_str
      tables := ⟨hinv.tables.zero_vals, hinv.tables.fail_spec, hinv.tables.outHead_spec,
        hinv.tables.outNext_spec, hinv.tables.follow_spec⟩ }

private theorem outerStep_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {B : PBFS} (hinv : BFSInv P σ T B) (hlt : B.qHead < B.qTail) :
    let r := B.queue B.qHead
    let fr := B.fail r
    let B₂ := PBFS.innerLoop T r fr σ 0 { B with qHead := B.qHead + 1 }
    BFSInv P σ T B₂ ∧ B₂.qHead = B.qHead + 1 := by
  set qh := B.qHead
  set r := B.queue qh
  set fr := B.fail r
  set B₁ : PBFS := { B with qHead := qh + 1 }
  have hInner₀ : InnerLoopInv P σ T qh r fr 0 B₁ := innerLoopInv_of_bfsInv hT hinv hlt
  have hInner := innerLoop_spec hT hchar hterm qh r fr σ 0 B₁ (by omega) hInner₀
  rw [Nat.zero_add] at hInner
  set B₂ := PBFS.innerLoop T r fr σ 0 B₁
  have hexp₂ : B₂.expAt B₂.qHead = insert r (B₂.expAt qh) := by
    rw [hInner.qHead_eq, expAt_succ, hInner.r_eq]
  change BFSInv P σ T B₂ ∧ B₂.qHead = B.qHead + 1
  refine ⟨?_, hInner.qHead_eq⟩
  refine
    { qHead_le := hInner.qHead_le
      q_bounds := hInner.q_bounds
      q_inj := hInner.q_inj
      disc_iff := fun w hw => by
        rw [hexp₂, hInner.disc_iff w hw]
        constructor
        · rintro (rfl | ⟨u, hu, c, hc, ht⟩ | ⟨c, hc, ht⟩)
          · exact Or.inl rfl
          · exact Or.inr ⟨u, Finset.mem_insert_of_mem hu, c, hc, ht⟩
          · exact Or.inr ⟨r, Finset.mem_insert_self r _, c, hc, ht⟩
        · rintro (rfl | ⟨u, hu, c, hc, ht⟩)
          · exact Or.inl rfl
          · rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact Or.inr (Or.inr ⟨c, hc, ht⟩)
            · exact Or.inr (Or.inl ⟨u, hu', c, hc, ht⟩)
      q_mono := hInner.q_mono
      q_depth_ub := fun j hj hlt₂ => by
        have hge : T.depth r ≤ T.depth (B₂.queue B₂.qHead) := by
          rw [← hInner.r_eq]
          exact hInner.q_mono qh B₂.qHead (by rw [hInner.qHead_eq]; omega) hlt₂
        have hub := hInner.q_depth_ub j hj
        omega
      lt_depth_mem_exp := fun v hv hlt₂ hdv => by
        have hub := hInner.q_depth_ub B₂.qHead hlt₂
        rcases lt_or_ge (T.depth v) (T.depth r) with hlt_r | hge_r
        · rw [hexp₂]; exact Finset.mem_insert_of_mem (hInner.lt_depth_mem_exp v hv hlt_r)
        · have hdv_le : T.depth v ≤ T.depth r := by omega
          have hv_disc := hInner.le_depth_mem_disc v hv hdv_le
          simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hv_disc
          rcases hv_disc with rfl | ⟨i, hi, rfl⟩
          · exact Finset.mem_insert_self 0 _
          · have hi_lt : i < B₂.qHead := by
              by_contra hge
              have hmono := hInner.q_mono B₂.qHead i (by omega) hi
              omega
            exact Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt, rfl⟩)
      delta_spec := fun u hu c hc => by
        rw [hexp₂] at hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hInner.delta_r c hc
        · exact hInner.delta_exp u hu' c hc
      tables := hInner.tables }

private theorem outerLoop_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0) :
    ∀ fuel B, BFSInv P σ T B → T.numStates ≤ B.qHead + fuel →
      BFSInv P σ T (PBFS.outerLoop T σ fuel B) ∧
        (PBFS.outerLoop T σ fuel B).qHead = (PBFS.outerLoop T σ fuel B).qTail
  | 0, B, hinv, hfuel => by
    have hqt : B.qTail < T.numStates := qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj
    have hge : ¬(B.qHead < B.qTail) := by omega
    have hle := hinv.qHead_le
    exact ⟨hinv, by omega⟩
  | fuel + 1, B, hinv, hfuel => by
    dsimp only [PBFS.outerLoop]
    split_ifs with hlt
    · obtain ⟨hinv₂, hqh₂⟩ := outerStep_spec hT hchar hterm hinv hlt
      exact outerLoop_spec hT hchar hterm fuel _ hinv₂ (by omega)
    · have hle := hinv.qHead_le
      exact ⟨hinv, by omega⟩

private structure AutomatonInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie) (B : PBFS) : Prop where
  qHead_eq_qTail : B.qHead = B.qTail
  qTail_lt : B.qTail < T.numStates
  fail_zero : B.fail 0 = 0
  fail_spec : ∀ u < T.numStates, 0 < u →
    B.fail u < T.numStates ∧
      T.strOf (B.fail u) = failure P (T.strOf u) ∧
      T.depth (B.fail u) < T.depth u
  delta_spec : ∀ u < T.numStates, ∀ a < σ,
    B.delta u a < T.numStates ∧ T.strOf (B.delta u a) = nextMove P (T.strOf u) a
  outHead_zero : B.outHead 0 = 0
  outHead_spec : ∀ u < T.numStates,
    B.outHead u < T.numStates ∧ T.depth (B.outHead u) ≤ T.depth u
  outNext_spec : ∀ q < T.numStates, 0 < q →
    B.outNext q < T.numStates ∧ (B.outNext q = 0 ∨ T.depth (B.outNext q) < T.depth q)
  follow_spec : ∀ u < T.numStates,
    followOut T.depth B.outNext T.numStates (B.outHead u) =
      (output P (T.strOf u)).map List.length

private theorem rootLoopInv_init {P : List (List ℕ)} {σ : ℕ} {T : PTrie} (hT : TreeInv σ T) :
    RootLoopInv P σ T 0 PBFS.init := by
  have hinit_disc : PBFS.init.disc = {0} := by
    simp only [PBFS.init, PBFS.disc, Finset.range_zero, Finset.image_empty]
    rfl
  exact
    { qHead_zero := rfl
      q_bounds := fun _ hi => absurd hi (Nat.not_lt_zero _)
      q_inj := fun _ hi => absurd hi (Nat.not_lt_zero _)
      disc_iff := fun w _ => by
        rw [hinit_disc]
        simp only [Finset.mem_singleton, Nat.not_lt_zero, false_and, exists_false, or_false]
      delta_zero := fun _ hc => absurd hc (Nat.not_lt_zero _)
      tables :=
        { zero_vals := ⟨rfl, rfl, rfl⟩
          fail_spec := fun x hx _ => by
            rw [hinit_disc, Finset.mem_singleton] at hx
            omega
          outHead_spec := fun x hx => by
            rw [hinit_disc] at hx ⊢
            rw [Finset.mem_singleton] at hx
            subst hx
            exact ⟨Finset.mem_singleton_self 0, Nat.le_refl _⟩
          outNext_spec := fun x hx _ => by
            rw [hinit_disc, Finset.mem_singleton] at hx
            omega
          follow_spec := fun x hx => by
            rw [hinit_disc, Finset.mem_singleton] at hx
            subst hx
            rw [hT.str_zero, output_nil, List.map_nil]
            exact followOut_zero_right _ _ _ } }

private theorem bfsInv_rootLoop {P : List (List ℕ)} {σ : ℕ} {T : PTrie} (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates, T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0) :
    let B₀ := PBFS.rootLoop T σ 0 PBFS.init
    BFSInv P σ T B₀ ∧ B₀.qHead = 0 := by
  have hRoot := rootLoop_spec hT hchar hterm σ 0 PBFS.init (by omega) (rootLoopInv_init hT)
  rw [Nat.zero_add] at hRoot
  set B₀ := PBFS.rootLoop T σ 0 PBFS.init
  have hexp₀ : B₀.expAt B₀.qHead = {0} := by
    rw [hRoot.qHead_zero]
    simp only [PBFS.expAt, Finset.range_zero, Finset.image_empty]
    rfl
  refine ⟨?_, hRoot.qHead_zero⟩
  exact
    { qHead_le := by rw [hRoot.qHead_zero]; exact Nat.zero_le _
      q_bounds := fun i hi => ⟨(hRoot.q_bounds i hi).1, (hRoot.q_bounds i hi).2.1⟩
      q_inj := hRoot.q_inj
      disc_iff := fun w hw => by
        rw [hexp₀, hRoot.disc_iff w hw]
        simp only [Finset.mem_singleton, exists_eq_left]
      q_mono := fun i j hij hj => by
        rw [(hRoot.q_bounds i (lt_of_le_of_lt hij hj)).2.2, (hRoot.q_bounds j hj).2.2]
      q_depth_ub := fun j hj _ => by
        rw [(hRoot.q_bounds j hj).2.2]
        omega
      lt_depth_mem_exp := fun v hv hlt hdv => by
        rw [hexp₀, Finset.mem_singleton]
        rw [hRoot.qHead_zero] at hlt hdv
        rw [(hRoot.q_bounds 0 hlt).2.2, hT.depth_eq v hv] at hdv
        have hv_nil : T.strOf v = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hT.str_inj v hv 0 hT.one_le (hv_nil.trans hT.str_zero.symm)
      delta_spec := fun u hu c hc => by
        rw [hexp₀, Finset.mem_singleton] at hu
        subst hu
        obtain ⟨h1, h2⟩ := hRoot.delta_zero c hc
        rw [hT.str_zero]
        exact ⟨h1, h2⟩
      tables := hRoot.tables }

private theorem build_bfs_spec (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    AutomatonInv P σ (PTrie.build P) (PBFS.build (PTrie.build P) σ) := by
  obtain ⟨hT, _, _, _, hterm⟩ := build_trie_spec P σ hvalid
  have hchar := trie_char_pos_iff P σ hvalid
  set T := PTrie.build P
  set B₀ := PBFS.rootLoop T σ 0 PBFS.init
  obtain ⟨hBFS₀, hqh₀⟩ := bfsInv_rootLoop hT hchar hterm
  have hOuter := outerLoop_spec hT hchar hterm T.numStates B₀ hBFS₀ (by omega)
  change BFSInv P σ T (PBFS.build T σ) ∧
    (PBFS.build T σ).qHead = (PBFS.build T σ).qTail at hOuter
  obtain ⟨hFinal, hqh_eq⟩ := hOuter
  set B := PBFS.build T σ
  have hexp_eq_disc : B.expAt B.qHead = B.disc := by
    dsimp only [PBFS.expAt, PBFS.disc]
    rw [hqh_eq]
  have hall_disc : ∀ w < T.numStates, w ∈ B.disc := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      rcases Nat.eq_zero_or_pos w with rfl | hpos
      · exact Finset.mem_insert_self 0 _
      · obtain ⟨u, huw, c, hc, htuc, _⟩ := hT.parent_exists w hpos hw
        have hu_disc : u ∈ B.disc := ih u huw (lt_trans huw hw)
        have hu_exp : u ∈ B.expAt B.qHead := hexp_eq_disc.symm ▸ hu_disc
        exact (hFinal.disc_iff w hw).mpr (Or.inr ⟨u, hu_exp, c, hc, htuc⟩)
  refine
    { qHead_eq_qTail := hqh_eq
      qTail_lt := qTail_lt_numStates hT.one_le hFinal.q_bounds hFinal.q_inj
      fail_zero := hFinal.tables.zero_vals.1
      fail_spec := fun u hu hup => by
        obtain ⟨hf_d, hf_s⟩ := hFinal.tables.fail_spec u (hall_disc u hu) hup
        have hf_lt := mem_disc_lt hT.one_le hFinal.q_bounds hf_d
        refine ⟨hf_lt, hf_s, ?_⟩
        rw [hT.depth_eq _ hf_lt, hT.depth_eq u hu, hf_s]
        exact length_failure_lt P (hT.str_ne_nil u hup hu)
      delta_spec := fun u hu a ha => by
        have hu_exp : u ∈ B.expAt B.qHead := hexp_eq_disc.symm ▸ hall_disc u hu
        obtain ⟨hd_d, hd_s⟩ := hFinal.delta_spec u hu_exp a ha
        exact ⟨mem_disc_lt hT.one_le hFinal.q_bounds hd_d, hd_s⟩
      outHead_zero := hFinal.tables.zero_vals.2.1
      outHead_spec := fun u hu => by
        obtain ⟨h1, h2⟩ := hFinal.tables.outHead_spec u (hall_disc u hu)
        exact ⟨mem_disc_lt hT.one_le hFinal.q_bounds h1, h2⟩
      outNext_spec := fun q hq hqp => by
        obtain ⟨h1, h2⟩ := hFinal.tables.outNext_spec q (hall_disc q hq) hqp
        exact ⟨mem_disc_lt hT.one_le hFinal.q_bounds h1, h2⟩
      follow_spec := fun u hu => hFinal.tables.follow_spec u (hall_disc u hu) }


/-! ## Word-RAM register and memory layout (`Fin 26`, `Basis.standard`) -/

private def Input.maxS (inp : Input) : ℕ := totalPatternLen inp.patterns + 1
private def Input.textBase (inp : Input) : ℕ :=
  5 + inp.patterns.length + totalPatternLen inp.patterns
private def Input.trieBase (inp : Input) : ℕ := inp.textBase + inp.text.length
private def Input.deltaBase (inp : Input) : ℕ := inp.trieBase + inp.maxS * inp.alphabetSize
private def Input.failBase (inp : Input) : ℕ := inp.deltaBase + inp.maxS * inp.alphabetSize
private def Input.depthBase (inp : Input) : ℕ := inp.failBase + inp.maxS
private def Input.termBase (inp : Input) : ℕ := inp.depthBase + inp.maxS
private def Input.outHeadBase (inp : Input) : ℕ := inp.termBase + inp.maxS
private def Input.outNextBase (inp : Input) : ℕ := inp.outHeadBase + inp.maxS
private def Input.queueBase (inp : Input) : ℕ := inp.outNextBase + inp.maxS
private def Input.outBase (inp : Input) : ℕ := inp.queueBase + inp.maxS

private theorem wordBound_eq_outBase (inp : Input) :
    inp.wordBound = inp.outBase + 2 * (occurrences inp.patterns inp.text).length + 4 := by
  dsimp only [Input.wordBound, Input.outBase, Input.queueBase, Input.outNextBase,
    Input.outHeadBase, Input.termBase, Input.depthBase, Input.failBase, Input.deltaBase,
    Input.trieBase, Input.textBase, Input.maxS]
  rw [Nat.mul_assoc]
  omega

private theorem layout_order (inp : Input) :
    inp.maxS = totalPatternLen inp.patterns + 1 ∧
    inp.textBase = 5 + inp.patterns.length + totalPatternLen inp.patterns ∧
    inp.trieBase = inp.textBase + inp.text.length ∧
    inp.deltaBase = inp.trieBase + inp.maxS * inp.alphabetSize ∧
    inp.failBase = inp.deltaBase + inp.maxS * inp.alphabetSize ∧
    inp.depthBase = inp.failBase + inp.maxS ∧
    inp.termBase = inp.depthBase + inp.maxS ∧
    inp.outHeadBase = inp.termBase + inp.maxS ∧
    inp.outNextBase = inp.outHeadBase + inp.maxS ∧
    inp.queueBase = inp.outNextBase + inp.maxS ∧
    inp.outBase = inp.queueBase + inp.maxS :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fits_of_le_outBase {inp : Input} {w v : ℕ} (hw : Fits w inp.wordBound)
    (hv : v ≤ inp.outBase) : Fits w v :=
  hw.of_le (by have := wordBound_eq_outBase inp; omega)

private def Input.trie (inp : Input) : PTrie := PTrie.build inp.patterns
private def Input.bfs (inp : Input) : PBFS := PBFS.build inp.trie inp.alphabetSize

private theorem Input.trie_eq (inp : Input) : inp.trie = PTrie.build inp.patterns := rfl
private theorem Input.bfs_eq (inp : Input) : inp.bfs = PBFS.build inp.trie inp.alphabetSize := rfl

private theorem Input.trie_spec {inp : Input} (hv : inp.Valid) :
    TreeInv inp.alphabetSize inp.trie ∧
    inp.trie.numStates ≤ inp.maxS ∧
    (∀ u < inp.trie.numStates, IsNode inp.patterns (inp.trie.strOf u)) ∧
    (∀ w, IsNode inp.patterns w → ∃ u < inp.trie.numStates, inp.trie.strOf u = w) ∧
    (∀ u < inp.trie.numStates, inp.trie.isTerm u =
      if inp.trie.strOf u ≠ [] ∧ inp.trie.strOf u ∈ inp.patterns then 1 else 0) :=
  build_trie_spec inp.patterns inp.alphabetSize hv.1

private theorem Input.char_iff {inp : Input} (hv : inp.Valid) :
    ∀ u < inp.trie.numStates, ∀ c < inp.alphabetSize,
      IsNode inp.patterns (inp.trie.strOf u ++ [c]) ↔ 0 < inp.trie.trie u c :=
  trie_char_pos_iff inp.patterns inp.alphabetSize hv.1

private theorem Input.bfs_spec {inp : Input} (hv : inp.Valid) :
    AutomatonInv inp.patterns inp.alphabetSize inp.trie inp.bfs :=
  build_bfs_spec inp.patterns inp.alphabetSize hv.1

attribute [irreducible] Input.trie Input.bfs Input.maxS Input.textBase Input.trieBase
  Input.deltaBase Input.failBase Input.depthBase Input.termBase Input.outHeadBase
  Input.outNextBase Input.queueBase Input.outBase

private theorem mem_encodePatterns_fits {P : List (List ℕ)} {σ w B : ℕ}
    (hP : ∀ p ∈ P, ∀ a ∈ p, a < σ) (hw : Fits w B)
    (hM : totalPatternLen P ≤ B) (hσ : σ ≤ B) :
    ∀ x ∈ encodePatterns P, Fits w x := by
  induction P with
  | nil => intro _ hx; exact absurd hx List.not_mem_nil
  | cons p ps ih =>
    intro x hx
    simp only [encodePatterns, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hxp | hxps
    · have : p.length ≤ totalPatternLen (p :: ps) := by
        simp only [totalPatternLen_cons]; omega
      exact hw.of_le (by omega)
    · have ha : x < σ := hP p List.mem_cons_self x hxp
      exact hw.of_le (by omega)
    · refine ih (fun q hq => hP q (List.mem_cons_of_mem p hq)) ?_ x hxps
      have : totalPatternLen ps ≤ totalPatternLen (p :: ps) := by
        simp only [totalPatternLen_cons]; omega
      omega

/-- Under `inp.Valid` and `Fits w inp.wordBound`, every word of `inp.encode` and its length fit in
width `w`. -/
theorem Input.Valid.inputFits {inp : Input} {w : ℕ} (hv : inp.Valid)
    (hw : Fits w inp.wordBound) : InputFits w inp.encode := by
  have hlo := layout_order inp
  have hwb := wordBound_eq_outBase inp
  have hS_pos : 1 ≤ inp.maxS := by omega
  have hsig_le : inp.alphabetSize ≤ inp.outBase := by
    have : 1 * inp.alphabetSize ≤ inp.maxS * inp.alphabetSize :=
      Nat.mul_le_mul_right _ hS_pos
    omega
  refine ⟨hw.of_le (by rw [length_encode]; omega), ?_⟩
  intro x hx
  simp only [Input.encode, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | rfl | rfl | rfl | hx_pat | hx_txt
  · exact hw.of_le (by omega)
  · exact hw.of_le (by omega)
  · exact hw.of_le (by omega)
  · exact hw.of_le (by omega)
  · exact mem_encodePatterns_fits hv.1 hw (by omega) (by omega) x hx_pat
  · have hlt : x < inp.alphabetSize := hv.2 x hx_txt
    exact hw.of_le (by omega)

namespace Reg

private abbrev sigma : Fin 26 := 0
private abbrev numPat : Fin 26 := 1
private abbrev totPat : Fin 26 := 2
private abbrev textLen : Fin 26 := 3
private abbrev maxS : Fin 26 := 4
private abbrev patBase : Fin 26 := 5
private abbrev textBase : Fin 26 := 6
private abbrev trieBase : Fin 26 := 7
private abbrev deltaBase : Fin 26 := 8
private abbrev failBase : Fin 26 := 9
private abbrev depthBase : Fin 26 := 10
private abbrev termBase : Fin 26 := 11
private abbrev outHeadBase : Fin 26 := 12
private abbrev outNextBase : Fin 26 := 13
/-- Output block header register returned by `searchProgram`. -/
abbrev out : Fin 26 := 14
private abbrev queueBase : Fin 26 := 15
private abbrev zero : Fin 26 := 16
private abbrev one : Fin 26 := 17
private abbrev rState : Fin 26 := 18
private abbrev r1 : Fin 26 := 19
private abbrev r2 : Fin 26 := 20
private abbrev r3 : Fin 26 := 21
private abbrev r4 : Fin 26 := 22
private abbrev r5 : Fin 26 := 23
private abbrev r6 : Fin 26 := 24
private abbrev r7 : Fin 26 := 25

end Reg

open Reg

private structure LayoutInv (inp : Input) (x : Data 26) : Prop where
  h_sigma : x.regs sigma = inp.alphabetSize
  h_numPat : x.regs numPat = inp.patterns.length
  h_totPat : x.regs totPat = totalPatternLen inp.patterns
  h_textLen : x.regs textLen = inp.text.length
  h_maxS : x.regs maxS = inp.maxS
  h_patBase : x.regs patBase = 5
  h_textBase : x.regs textBase = inp.textBase
  h_trieBase : x.regs trieBase = inp.trieBase
  h_deltaBase : x.regs deltaBase = inp.deltaBase
  h_failBase : x.regs failBase = inp.failBase
  h_depthBase : x.regs depthBase = inp.depthBase
  h_termBase : x.regs termBase = inp.termBase
  h_outHeadBase : x.regs outHeadBase = inp.outHeadBase
  h_outNextBase : x.regs outNextBase = inp.outNextBase
  h_out : x.regs out = inp.outBase
  h_queueBase : x.regs queueBase = inp.queueBase
  h_zero : x.regs zero = 0
  h_one : x.regs one = 1

private theorem LayoutInv.of_preserves {inp : Input} {x y : Data 26} {w t : ℕ}
    {c : Code .standard 26} (hL : LayoutInv inp x) (he : ExecWithin w c x y t)
    (hk : 18 ≤ c.writeStart := by decide) : LayoutInv inp y where
  h_sigma := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_sigma
  h_numPat := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_numPat
  h_totPat := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_totPat
  h_textLen := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_textLen
  h_maxS := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_maxS
  h_patBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_patBase
  h_textBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_textBase
  h_trieBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_trieBase
  h_deltaBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_deltaBase
  h_failBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_failBase
  h_depthBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_depthBase
  h_termBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_termBase
  h_outHeadBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_outHeadBase
  h_outNextBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_outNextBase
  h_out := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_out
  h_queueBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_queueBase
  h_zero := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_zero
  h_one := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_one

/-! ## Word-RAM structured code -/

private def setupHeaderCode : Code .standard 26 := ram[
  zero ← #0;
  one ← #1;
  r6 ← #1; sigma ← *r6;
  r6 ← #2; numPat ← *r6;
  r6 ← #3; totPat ← *r6;
  r6 ← #4; textLen ← *r6;
  maxS ← totPat + one;
  patBase ← #5 ]

private def setupBaseCode : Code .standard 26 := ram[
  textBase ← patBase + numPat;
  textBase ← textBase + totPat;
  trieBase ← textBase + textLen;
  r7 ← maxS * sigma;
  deltaBase ← trieBase + r7;
  failBase ← deltaBase + r7;
  depthBase ← failBase + maxS;
  termBase ← depthBase + maxS;
  outHeadBase ← termBase + maxS;
  outNextBase ← outHeadBase + maxS;
  queueBase ← outNextBase + maxS;
  out ← queueBase + maxS;
  r1 ← trieBase ]

private def setupCode : Code .standard 26 :=
  .seq setupHeaderCode setupBaseCode

private def setupAndClearCode : Code .standard 26 :=
  .seq setupCode (zeroFill r1 out zero one)

private def trieCharBranchCode : Code .standard 26 :=
  .branch (.lt zero r7)
    (ram[ r4 ← r7 ])
    (ram[
      *r6 ← rState;
      r7 ← depthBase + r4;
      r7 ← *r7;
      r7 ← r7 + one;
      r6 ← depthBase + rState;
      *r6 ← r7;
      r4 ← rState;
      rState ← rState + one ])

private def trieCharStepCode : Code .standard 26 :=
  .seq
    (ram[
      r5 ← *r2;
      r2 ← r2 + one;
      r3 ← r3 - one;
      r6 ← r4 * sigma;
      r6 ← r6 + r5;
      r6 ← trieBase + r6;
      r7 ← *r6 ])
    trieCharBranchCode

private def triePatBranchCode : Code .standard 26 :=
  .branch (.lt zero r4)
    (ram[ r6 ← termBase + r4; *r6 ← one; r1 ← r1 - one ])
    (ram[ r1 ← r1 - one ])

private def triePatStepCode : Code .standard 26 :=
  .seq
    (ram[
      r3 ← *r2;
      r2 ← r2 + one;
      r4 ← #0 ])
    (.seq
      (.loop (.lt zero r3) trieCharStepCode)
      triePatBranchCode)

private def buildTrieCode : Code .standard 26 :=
  .seq
    (ram[ rState ← #1; r1 ← numPat; r2 ← patBase ])
    (.loop (.lt zero r1) triePatStepCode)

private def bfsRootStepCode : Code .standard 26 :=
  .seq (ram[ r6 ← trieBase + r5; r6 ← *r6 ])
    (.branch (.lt zero r6)
      (.seq
        (ram[
          r7 ← deltaBase + r5; *r7 ← r6;
          r7 ← failBase + r6; *r7 ← zero;
          r7 ← queueBase + r2; *r7 ← r6;
          r2 ← r2 + one;
          r7 ← outNextBase + r6; *r7 ← zero;
          rState ← termBase + r6; rState ← *rState ])
        (.branch (.lt zero rState)
          (ram[ r7 ← outHeadBase + r6; *r7 ← r6; r5 ← r5 + one ])
          (ram[ r7 ← outHeadBase + r6; *r7 ← zero; r5 ← r5 + one ])))
      (ram[ r7 ← deltaBase + r5; *r7 ← zero; r5 ← r5 + one ]))

private def bfsInnerStoreCode : Code .standard 26 := ram[
  rState ← r3 * sigma; rState ← rState + r5; rState ← deltaBase + rState; *rState ← r6;
  rState ← failBase + r6; *rState ← r7;
  rState ← queueBase + r2; *rState ← r6;
  r2 ← r2 + one ]

private def bfsInnerLinkCode : Code .standard 26 := ram[
  r7 ← outHeadBase + r7; r7 ← *r7;
  rState ← outNextBase + r6; *rState ← r7;
  rState ← termBase + r6; rState ← *rState ]

private def bfsInnerStepCode : Code .standard 26 :=
  .seq
    (ram[
      r6 ← r3 * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6;
      r7 ← r4 * sigma; r7 ← r7 + r5; r7 ← deltaBase + r7; r7 ← *r7 ])
    (.branch (.lt zero r6)
      (.seq
        (.seq bfsInnerStoreCode bfsInnerLinkCode)
        (.branch (.lt zero rState)
          (ram[ rState ← outHeadBase + r6; *rState ← r6; r5 ← r5 + one ])
          (ram[ rState ← outHeadBase + r6; *rState ← r7; r5 ← r5 + one ])))
      (ram[
        rState ← r3 * sigma; rState ← rState + r5; rState ← deltaBase + rState; *rState ← r7;
        r5 ← r5 + one ]))

private def bfsOuterStepCode : Code .standard 26 :=
  .seq
    (ram[
      r3 ← queueBase + r1; r3 ← *r3;
      r1 ← r1 + one;
      r4 ← failBase + r3; r4 ← *r4;
      r5 ← #0 ])
    (.loop (.lt r5 sigma) bfsInnerStepCode)

private def bfsBuildCode : Code .standard 26 :=
  .seq
    (.seq (ram[ r1 ← #0; r2 ← #0; r5 ← #0 ]) (.loop (.lt r5 sigma) bfsRootStepCode))
    (.loop (.lt r1 r2) bfsOuterStepCode)

private def computeFailCond : Code .standard 26 :=
  .seq (ram[ r7 ← #0 ])
    (.branch (.lt zero rState)
      (.seq
        (ram[
          r6 ← rState * sigma;
          r6 ← r6 + r5;
          r6 ← trieBase + r6;
          r6 ← *r6 ])
        (.branch (.lt zero r6)
          (ram[ r7 ← #0 ])
          (ram[ r7 ← #1 ])))
      (ram[ r7 ← #0 ]))

private def stepCode : Code .standard 26 :=
  .seq computeFailCond
    (.seq
      (.loop (.lt zero r7)
        (.seq (ram[ r6 ← failBase + rState; rState ← *r6 ]) computeFailCond))
      (ram[
        r6 ← rState * sigma;
        r6 ← r6 + r5;
        r6 ← trieBase + r6;
        rState ← *r6 ]))

private def emitStepCode : Code .standard 26 := ram[
  r6 ← depthBase + r4;
  r6 ← *r6;
  *r2 ← r3;
  r2 ← r2 + one;
  *r2 ← r6;
  r2 ← r2 + one;
  r6 ← outNextBase + r4;
  r4 ← *r6 ]

private def emitCode : Code .standard 26 :=
  .seq (ram[ r6 ← outHeadBase + rState; r4 ← *r6 ])
    (.loop (.lt zero r4) emitStepCode)

private def scanStepCode : Code .standard 26 :=
  .seq
    (ram[
      r6 ← textBase + r1;
      r5 ← *r6;
      r3 ← r1 + one ])
    (.seq stepCode (.seq emitCode (ram[ r1 ← r3 ])))

private def scanCode : Code .standard 26 :=
  .seq
    (ram[
      rState ← #0;
      r1 ← #0;
      r2 ← out + one ])
    (.seq
      (.loop (.lt r1 textLen) scanStepCode)
      (ram[
        r6 ← out + one;
        r6 ← r2 - r6;
        *out ← r6 ]))

/-- Structured Word-RAM implementation of Aho–Corasick multi-pattern string matching:
initializes and clears the scratch tables, builds the array trie, runs breadth-first failure,
next-move, and output-link construction, and scans the text emitting `[endPos, keywordLen]` pairs
at `Reg.out`. -/
def searchCode : Code .standard 26 :=
  .seq setupAndClearCode (.seq buildTrieCode (.seq bfsBuildCode scanCode))

/-- Flat Word-RAM program computing `encodeOccurrences (occurrences inp.patterns inp.text)` from
`inp.encode`. -/
def searchProgram : Program .standard 26 :=
  searchCode.program out

/-! ## Phase 1: Setup and scratch-table clearing -/

private structure TrieMem (inp : Input) (T : PTrie) (mem : ℕ → ℕ) : Prop where
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
    exact
      { h_sigma := by wram_simp [hsig1]
        h_numPat := by wram_simp [hnp1]
        h_totPat := by wram_simp [htp1]
        h_textLen := by wram_simp [htl1]
        h_maxS := by wram_simp [hms1]
        h_patBase := by wram_simp [hpb1]
        h_textBase := by wram_simp
        h_trieBase := by wram_simp
        h_deltaBase := by wram_simp
        h_failBase := by wram_simp
        h_depthBase := by wram_simp
        h_termBase := by wram_simp
        h_outHeadBase := by wram_simp
        h_outNextBase := by wram_simp
        h_out := by wram_simp
        h_queueBase := by wram_simp
        h_zero := by wram_simp [hz1]
        h_one := by wram_simp [ho1] }
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

private theorem exec_setupAndClear (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound) :
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

/-! ## Phase 2: Array-trie construction (`buildTrieCode`) -/

private theorem trieMem_stepChar_new {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    {u₀ a : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hs : T.numStates < inp.maxS) (h0 : T.trie u₀ a = 0)
    (hM : TrieMem inp T mem) :
    TrieMem inp (T.stepChar u₀ a).1
      (Function.update
        (Function.update mem (inp.trieBase + u₀ * inp.alphabetSize + a) T.numStates)
        (inp.depthBase + T.numStates) (T.depth u₀ + 1)) := by
  have hlo := layout_order inp
  have hrm₀ := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu₀ ha
  have hlen := length_encodePatterns inp.patterns
  dsimp only [PTrie.stepChar]
  simp only [h0, ↓reduceIte]
  refine
    { pats := hM.pats.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      txt := hM.txt.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have huc_lt := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        dsimp only
        rw [Function.update_of_ne (by omega)]
        by_cases huc : u = u₀ ∧ c = a
        · obtain ⟨rfl, rfl⟩ := huc
          simp only [and_self, ↓reduceIte, Function.update_self]
        · simp only [huc, ↓reduceIte]
          have hne_addr : inp.trieBase + u * inp.alphabetSize + c ≠
              inp.trieBase + u₀ * inp.alphabetSize + a := fun heq => by
            obtain ⟨hc_eq, hu_eq⟩ := Nat.eq_of_add_mul_eq (b := u) (b' := u₀) hc ha (by omega)
            exact huc ⟨hu_eq, hc_eq⟩
          rw [Function.update_of_ne hne_addr]
          exact hM.trie_cell u hu c hc
      depth_cell := fun u hu => by
        dsimp only
        by_cases hus : u = T.numStates
        · subst hus
          rw [Function.update_self, Function.update_self]
        · simp (disch := omega) only [Function.update_of_ne]
          exact hM.depth_cell u hu
      term_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.term_cell u hu
      zero_df := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_df addr ha1 ha2
      zero_rest := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_rest addr ha1 ha2 }

private theorem trieMem_insertPat_pos {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    {u₁ : ℕ} (hu₁ : u₁ < inp.maxS) (hM : TrieMem inp T mem) :
    TrieMem inp { T with isTerm := Function.update T.isTerm u₁ 1 }
      (Function.update mem (inp.termBase + u₁) 1) := by
  have hlo := layout_order inp
  have hlen := length_encodePatterns inp.patterns
  refine
    { pats := hM.pats.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      txt := hM.txt.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have huc_lt := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.trie_cell u hu c hc
      depth_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.depth_cell u hu
      term_cell := fun u hu => by
        dsimp only
        by_cases huu : u = u₁
        · subst huu; rw [Function.update_self, Function.update_self]
        · simp (disch := omega) only [Function.update_of_ne]
          exact hM.term_cell u hu
      zero_df := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_df addr ha1 ha2
      zero_rest := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_rest addr ha1 ha2 }

private theorem exec_trieCharLoop (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound) :
    ∀ (chars rest : List ℕ) (T : PTrie) (x : Data 26),
      LayoutInv inp x →
      TrieMem inp T x.mem →
      TreeInv inp.alphabetSize T →
      T.numStates + chars.length ≤ inp.maxS →
      x.regs rState = T.numStates →
      x.regs r4 < T.numStates →
      x.regs r3 = chars.length →
      x.regs r2 + (chars ++ rest).length ≤ inp.textBase →
      Block.HoldsList (x.regs r2) (chars ++ rest) x.mem →
      (∀ a ∈ chars, a < inp.alphabetSize) →
      ∃ y, ExecWithin w (.loop (.lt zero r3) trieCharStepCode) x y (19 * chars.length + 2) ∧
        LayoutInv inp y ∧
        TrieMem inp (T.insertChars (x.regs r4) chars).1 y.mem ∧
        y.regs rState = (T.insertChars (x.regs r4) chars).1.numStates ∧
        y.regs r4 = (T.insertChars (x.regs r4) chars).2 ∧
        y.regs r2 = x.regs r2 + chars.length ∧
        y.regs r1 = x.regs r1 ∧
        Block.HoldsList (y.regs r2) rest y.mem := by
  intro chars
  have hlo := layout_order inp
  induction chars with
  | nil =>
    intro rest T x hL hM _ _ hrS _ hr3 _ hhold _
    have hstop : ¬(Cond.lt zero r3).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr3, List.length_nil]; omega
    refine ⟨x, ExecWithin.loop_exit hstop, hL, hM, hrS, rfl, by simp, rfl, ?_⟩
    simpa only [List.nil_append, Nat.add_zero] using hhold
  | cons a as ih =>
    intro rest T x hL hM hT hbud hrS hu_lt hr3 hptr_ub hhold hchars
    have hc : (Cond.lt zero r3).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr3, List.length_cons]; omega
    have ha_lt : a < inp.alphabetSize := hchars a List.mem_cons_self
    have has_lt : ∀ b ∈ as, b < inp.alphabetSize := fun b hb =>
      hchars b (List.mem_cons_of_mem a hb)
    obtain ⟨hm_a, hhold_tail⟩ := Block.holdsList_cons_iff.mp hhold
    have hu_maxS : x.regs r4 < inp.maxS := by simp only [List.length_cons] at hbud; omega
    have hrm_lt : x.regs r4 * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
      Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu_maxS ha_lt
    have htrie_read :
        x.mem (inp.trieBase + (x.regs r4 * inp.alphabetSize + a)) = T.trie (x.regs r4) a := by
      rw [← Nat.add_assoc]; exact hM.trie_cell (x.regs r4) hu_maxS a ha_lt
    have hf_ptr1 : Fits w (x.regs r2 + 1) := fits_of_le_outBase hw (by
      simp only [List.cons_append, List.length_cons, List.length_append] at hptr_ub; omega)
    have hf_rem1 : Fits w (x.regs r3 - 1) := fits_of_le_outBase hw (by
      rw [hr3]; simp only [List.cons_append, List.length_cons, List.length_append] at hptr_ub ⊢
      omega)
    have hf_mul : Fits w (x.regs r4 * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
    have hf_rm : Fits w (x.regs r4 * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
    have hf_taddr : Fits w (inp.trieBase + (x.regs r4 * inp.alphabetSize + a)) :=
      fits_of_le_outBase hw (by omega)
    have hhead : ∃ x₁, ExecWithin w (ram[
        r5 ← *r2;
        r2 ← r2 + one;
        r3 ← r3 - one;
        r6 ← r4 * sigma;
        r6 ← r6 + r5;
        r6 ← trieBase + r6;
        r7 ← *r6 ]) x x₁ 7 ∧
      x₁.regs r2 = x.regs r2 + 1 ∧
      x₁.regs r3 = as.length ∧
      x₁.regs r4 = x.regs r4 ∧
      x₁.regs r5 = a ∧
      x₁.regs r6 = inp.trieBase + x.regs r4 * inp.alphabetSize + a ∧
      x₁.regs r7 = T.trie (x.regs r4) a ∧
      x₁.regs rState = T.numStates ∧
      x₁.regs r1 = x.regs r1 ∧
      x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hm_a, hL.h_one, hL.h_sigma, hL.h_trieBase, htrie_read, hf_ptr1, hf_rem1,
        hf_mul, hf_rm, hf_taddr]
      refine ⟨by wram_simp, ?_, by wram_simp, by wram_simp,
        by wram_simp; omega, by wram_simp, by wram_simp [hrS], by wram_simp, by wram_simp⟩
      wram_simp [hr3]
      simp only [List.length_cons, Nat.add_sub_cancel]
    obtain ⟨x₁, he_hd, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_r6, hx₁_r7, hx₁_rS, hx₁_r1,
      hx₁_mem⟩ := hhead
    have hL₁ : LayoutInv inp x₁ := hL.of_preserves he_hd
    obtain ⟨hT_step, _, hub_step, _, hs_lt_step, _, _⟩ := stepChar_spec hT hu_lt ha_lt
    dsimp only [PTrie.insertChars]
    generalize hT₁_def : (T.stepChar (x.regs r4) a).1 = T₁ at hT_step hub_step hs_lt_step ⊢
    generalize hu₁_def : (T.stepChar (x.regs r4) a).2 = u₁ at hs_lt_step ⊢
    have hbranch : ∃ x₂, ExecWithin w trieCharBranchCode x₁ x₂ 10 ∧
      LayoutInv inp x₂ ∧
      TrieMem inp T₁ x₂.mem ∧
      x₂.regs rState = T₁.numStates ∧
      x₂.regs r4 = u₁ ∧
      x₂.regs r2 = x.regs r2 + 1 ∧
      x₂.regs r3 = as.length ∧
      x₂.regs r1 = x.regs r1 ∧
      Block.HoldsList (x.regs r2 + 1) (as ++ rest) x₂.mem := by
      by_cases hpos : 0 < T.trie (x.regs r4) a
      · have hcond : (Cond.lt zero r7).Holds x₁ := by
          simp only [Cond.holds_lt, hL₁.h_zero, hx₁_r7]; exact hpos
        have hnot0 : T.trie (x.regs r4) a ≠ 0 := by omega
        have hT₁_eq : T₁ = T := by
          rw [← hT₁_def]; dsimp only [PTrie.stepChar]; simp only [hnot0, ↓reduceIte]
        have hu₁_eq : u₁ = T.trie (x.regs r4) a := by
          rw [← hu₁_def]; dsimp only [PTrie.stepChar]; simp only [hnot0, ↓reduceIte]
        have hpos_step : ∃ x₂, ExecWithin (B := .standard) w (ram[ r4 ← r7 ]) x₁ x₂ 1 ∧
            x₂.regs r4 = u₁ ∧ x₂.regs rState = T.numStates ∧
            x₂.regs r2 = x₁.regs r2 ∧ x₂.regs r3 = x₁.regs r3 ∧
            x₂.regs r1 = x₁.regs r1 ∧ x₂.mem = x₁.mem := by
          refine WP.exists_execWithin ?_
          wram_exec
          exact ⟨by wram_simp [hx₁_r7, hu₁_eq], by wram_simp [hx₁_rS], by wram_simp,
            by wram_simp, by wram_simp, by wram_simp⟩
        obtain ⟨x₂, he_p, hx₂_r4, hx₂_rS, hx₂_r2, hx₂_r3, hx₂_r1, hx₂_mem⟩ := hpos_step
        have he_br : ExecWithin w trieCharBranchCode x₁ x₂ 10 :=
          (ExecWithin.branch_pos hcond he_p).mono (by omega)
        have hL₂ : LayoutInv inp x₂ := hL₁.of_preserves he_br
        refine ⟨x₂, he_br, hL₂, ?_, hx₂_rS.trans (congrArg PTrie.numStates hT₁_eq.symm), hx₂_r4,
          hx₂_r2.trans hx₁_r2, hx₂_r3.trans hx₁_r3, hx₂_r1.trans hx₁_r1, ?_⟩
        · rwa [hx₂_mem, hx₁_mem, hT₁_eq]
        · rwa [hx₂_mem, hx₁_mem]
      · have h0 : T.trie (x.regs r4) a = 0 := by omega
        have hcond : ¬(Cond.lt zero r7).Holds x₁ := by
          simp only [Cond.holds_lt, hL₁.h_zero, hx₁_r7, h0]; omega
        have hs_maxS : T.numStates < inp.maxS := by simp only [List.length_cons] at hbud; omega
        have hdu_le : T.depth (x.regs r4) < T.numStates :=
          lt_of_le_of_lt (depth_le_self hT _ hu_lt) hu_lt
        have hd_read : x₁.mem (inp.depthBase + x.regs r4) = T.depth (x.regs r4) := by
          rw [hx₁_mem]; exact hM.depth_cell (x.regs r4) hu_maxS
        have hf_dpu : Fits w (inp.depthBase + x.regs r4) := fits_of_le_outBase hw (by omega)
        have hf_du1 : Fits w (T.depth (x.regs r4) + 1) := fits_of_le_outBase hw (by omega)
        have hf_dps : Fits w (inp.depthBase + T.numStates) := fits_of_le_outBase hw (by omega)
        have hf_s1 : Fits w (T.numStates + 1) := fits_of_le_outBase hw (by omega)
        have hne_dp_tr :
            inp.depthBase + x.regs r4 ≠ inp.trieBase + x.regs r4 * inp.alphabetSize + a := by
          omega
        have hneg_step : ∃ x₂, ExecWithin w (ram[
            *r6 ← rState;
            r7 ← depthBase + r4;
            r7 ← *r7;
            r7 ← r7 + one;
            r6 ← depthBase + rState;
            *r6 ← r7;
            r4 ← rState;
            rState ← rState + one ]) x₁ x₂ 8 ∧
          x₂.regs rState = T.numStates + 1 ∧
          x₂.regs r4 = T.numStates ∧
          x₂.regs r2 = x₁.regs r2 ∧
          x₂.regs r3 = x₁.regs r3 ∧
          x₂.regs r1 = x₁.regs r1 ∧
          x₂.mem = Function.update
            (Function.update x.mem (inp.trieBase + x.regs r4 * inp.alphabetSize + a) T.numStates)
            (inp.depthBase + T.numStates) (T.depth (x.regs r4) + 1) := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₁.h_depthBase, hL₁.h_one, hx₁_r4, hx₁_r6, hx₁_rS, hd_read,
            hf_dpu, hf_du1, hf_dps, hf_s1, hne_dp_tr]
          exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
            by wram_simp [hx₁_mem]⟩
        obtain ⟨x₂, he_n, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r3, hx₂_r1, hx₂_mem⟩ := hneg_step
        have he_br : ExecWithin w trieCharBranchCode x₁ x₂ 10 := ExecWithin.branch_neg hcond he_n
        have hL₂ : LayoutInv inp x₂ := hL₁.of_preserves he_br
        have hT₁_num : T₁.numStates = T.numStates + 1 := by
          rw [← hT₁_def]; dsimp only [PTrie.stepChar]; simp only [h0, ↓reduceIte]
        have hu₁_eq : u₁ = T.numStates := by
          rw [← hu₁_def]; dsimp only [PTrie.stepChar]; simp only [h0, ↓reduceIte]
        have hM₂ : TrieMem inp T₁ x₂.mem := by
          rw [hx₂_mem, ← hT₁_def]
          exact trieMem_stepChar_new hu_maxS ha_lt hs_maxS h0 hM
        have hhold₂ : Block.HoldsList (x.regs r2 + 1) (as ++ rest) x₂.mem := by
          rw [hx₂_mem]
          refine hhold_tail.frame fun addr ha1 ha2 => ?_
          simp only [List.append_eq, List.cons_append, List.length_cons, List.length_append]
            at hptr_ub ha2
          simp (disch := omega) only [Function.update_of_ne]
        exact ⟨x₂, he_br, hL₂, hM₂, hx₂_rS.trans hT₁_num.symm, hx₂_r4.trans hu₁_eq.symm,
          hx₂_r2.trans hx₁_r2, hx₂_r3.trans hx₁_r3, hx₂_r1.trans hx₁_r1, hhold₂⟩
    obtain ⟨x₂, he_br, hL₂, hM₂, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r3, hx₂_r1, hhold₂⟩ := hbranch
    have hT₁_bud : T₁.numStates + as.length ≤ inp.maxS := by
      simp only [List.length_cons] at hbud
      omega
    obtain ⟨y, he_tl, hLy, hMy, hy_rS, hy_r4, hy_r2, hy_r1, hholdy⟩ :=
      ih rest T₁ x₂ hL₂ hM₂ hT_step hT₁_bud hx₂_rS
        (by rw [hx₂_r4]; exact hs_lt_step) hx₂_r3
        (by
          rw [hx₂_r2]
          simp only [List.cons_append, List.length_cons, List.length_append] at hptr_ub ⊢
          omega)
        (by rwa [hx₂_r2]) has_lt
    rw [hx₂_r4] at hMy hy_rS hy_r4
    refine ⟨y, (ExecWithin.loop_iter hc (he_hd.seq he_br) he_tl).mono
      (by simp only [List.length_cons]; omega),
      hLy, hMy, hy_rS, hy_r4, ?_, hy_r1.trans hx₂_r1, hholdy⟩
    rw [hy_r2, hx₂_r2, List.length_cons]
    omega

private theorem exec_triePatLoop (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound) :
    ∀ (ps : List (List ℕ)) (T : PTrie) (x : Data 26),
      LayoutInv inp x →
      TrieMem inp T x.mem →
      TreeInv inp.alphabetSize T →
      T.numStates + totalPatternLen ps ≤ inp.maxS →
      x.regs rState = T.numStates →
      x.regs r1 = ps.length →
      x.regs r2 + (encodePatterns ps).length ≤ inp.textBase →
      Block.HoldsList (x.regs r2) (encodePatterns ps) x.mem →
      (∀ p ∈ ps, ∀ a ∈ p, a < inp.alphabetSize) →
      ∃ y, ExecWithin w (.loop (.lt zero r1) triePatStepCode) x y
          (19 * totalPatternLen ps + 11 * ps.length + 2) ∧
        LayoutInv inp y ∧
        TrieMem inp (ps.foldl PTrie.insertPat T) y.mem ∧
        y.regs rState = (ps.foldl PTrie.insertPat T).numStates
  | [], T, x, hL, hM, _, _, hrS, hr1, _, _, _ => by
    have hstop : ¬(Cond.lt zero r1).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr1, List.length_nil]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hrS⟩
  | p :: ps, T, x, hL, hM, hT, hbud, hrS, hr1, hptr_ub, hhold, hps => by
    have hlo := layout_order inp
    have hc : (Cond.lt zero r1).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr1, List.length_cons]; omega
    have hp_val : ∀ a ∈ p, a < inp.alphabetSize := hps p List.mem_cons_self
    have hps_val : ∀ q ∈ ps, ∀ a ∈ q, a < inp.alphabetSize := fun q hq =>
      hps q (List.mem_cons_of_mem p hq)
    dsimp only [encodePatterns] at hhold hptr_ub
    obtain ⟨hm_plen, hhold_body⟩ := Block.holdsList_cons_iff.mp hhold
    have hf_ptr1 : Fits w (x.regs r2 + 1) := fits_of_le_outBase hw (by
      simp only [List.length_cons, List.length_append] at hptr_ub; omega)
    have hpat_hd : ∃ x₁, ExecWithin w (ram[ r3 ← *r2; r2 ← r2 + one; r4 ← #0 ]) x x₁ 3 ∧
        x₁.regs r3 = p.length ∧ x₁.regs r2 = x.regs r2 + 1 ∧ x₁.regs r4 = 0 ∧
        x₁.regs rState = T.numStates ∧ x₁.regs r1 = x.regs r1 ∧ x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hm_plen, hL.h_one, hf_ptr1]
      exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp [hrS], by wram_simp,
        by wram_simp⟩
    obtain ⟨x₁, he_hd, hx₁_r3, hx₁_r2, hx₁_r4, hx₁_rS, hx₁_r1, hx₁_mem⟩ := hpat_hd
    have hL₁ : LayoutInv inp x₁ :=
      hL.of_preserves he_hd
    obtain ⟨hT₁_inv, _, hub₁, hu₁_lt, _, _, _, _, _⟩ :=
      insertChars_spec p T 0 hT hT.one_le hp_val
    obtain ⟨x₂, he_chars, hL₂, hM₂, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r1, hhold₂⟩ :=
      exec_trieCharLoop inp w hw p (encodePatterns ps) T x₁ hL₁ (by rwa [hx₁_mem]) hT
        (by simp only [totalPatternLen_cons] at hbud; omega) hx₁_rS
        (by rw [hx₁_r4]; exact hT.one_le) hx₁_r3
        (by rw [hx₁_r2]; simp only [List.length_cons, List.length_append] at hptr_ub ⊢; omega)
        (by rwa [hx₁_r2, hx₁_mem]) hp_val
    rw [hx₁_r4] at hM₂ hx₂_rS hx₂_r4
    set T₁ := (T.insertChars 0 p).1
    set u₁ := (T.insertChars 0 p).2
    set T₂ := PTrie.insertPat T p
    have hT₁_maxS : T₁.numStates ≤ inp.maxS := by
      simp only [totalPatternLen_cons] at hbud; omega
    have hu₁_maxS : u₁ < inp.maxS := lt_of_lt_of_le hu₁_lt hT₁_maxS
    have hf_p1 : Fits w (x₂.regs r1 - 1) := fits_of_le_outBase hw (by
      rw [hx₂_r1, hx₁_r1, hr1]
      simp only [List.length_cons, List.length_append, length_encodePatterns] at hptr_ub ⊢
      omega)
    have hpat_tl : ∃ x₃, ExecWithin w triePatBranchCode x₂ x₃ 4 ∧
      LayoutInv inp x₃ ∧
      TrieMem inp T₂ x₃.mem ∧
      x₃.regs rState = T₂.numStates ∧
      x₃.regs r1 = ps.length ∧
      x₃.regs r2 = x₂.regs r2 ∧
      Block.HoldsList (x₂.regs r2) (encodePatterns ps) x₃.mem := by
      by_cases hpos : 0 < u₁
      · have hcond : (Cond.lt zero r4).Holds x₂ := by
          simp only [Cond.holds_lt, hL₂.h_zero, hx₂_r4]; exact hpos
        have hf_taddr : Fits w (inp.termBase + u₁) := fits_of_le_outBase hw (by omega)
        have hpos_tl : ∃ x₃, ExecWithin w
            (ram[ r6 ← termBase + r4; *r6 ← one; r1 ← r1 - one ]) x₂ x₃ 3 ∧
            x₃.regs rState = x₂.regs rState ∧ x₃.regs r1 = ps.length ∧
            x₃.regs r2 = x₂.regs r2 ∧
            x₃.mem = Function.update x₂.mem (inp.termBase + u₁) 1 := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₂.h_termBase, hL₂.h_one, hx₂_r4, hf_taddr, hf_p1]
          exact ⟨by wram_simp, by wram_simp [hx₂_r1, hx₁_r1, hr1]; simp, by wram_simp,
            by wram_simp⟩
        obtain ⟨x₃, he_p, hx₃_rS, hx₃_r1, hx₃_r2, hx₃_mem⟩ := hpos_tl
        have he_br : ExecWithin w triePatBranchCode x₂ x₃ 4 := ExecWithin.branch_pos hcond he_p
        have hL₃ : LayoutInv inp x₃ :=
          hL₂.of_preserves he_br
        have hpos' : 0 < (T.insertChars 0 p).2 := hpos
        have hT₂_eq : T₂ = { T₁ with isTerm := Function.update T₁.isTerm u₁ 1 } := by
          dsimp only [T₂, PTrie.insertPat]; simp only [hpos', ↓reduceIte]; rfl
        have hM₃ : TrieMem inp T₂ x₃.mem := by
          rw [hx₃_mem, hT₂_eq]
          exact trieMem_insertPat_pos hu₁_maxS hM₂
        have hhold₃ : Block.HoldsList (x₂.regs r2) (encodePatterns ps) x₃.mem := by
          rw [hx₃_mem]
          refine hhold₂.frame fun addr ha1 ha2 => ?_
          have : x₂.regs r2 + (encodePatterns ps).length ≤ inp.textBase := by
            rw [hx₂_r2, hx₁_r2]
            simp only [List.length_cons, List.length_append] at hptr_ub
            omega
          simp (disch := omega) only [Function.update_of_ne]
        exact ⟨x₃, he_br, hL₃, hM₃, by rw [hx₃_rS, hx₂_rS, hT₂_eq], hx₃_r1, hx₃_r2, hhold₃⟩
      · have hpos' : ¬0 < (T.insertChars 0 p).2 := hpos
        have hcond : ¬(Cond.lt zero r4).Holds x₂ := by
          simp only [Cond.holds_lt, hL₂.h_zero, hx₂_r4]; exact hpos
        have hneg_tl : ∃ x₃, ExecWithin w (ram[ r1 ← r1 - one ]) x₂ x₃ 1 ∧
            x₃.regs rState = x₂.regs rState ∧ x₃.regs r1 = ps.length ∧
            x₃.regs r2 = x₂.regs r2 ∧ x₃.mem = x₂.mem := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₂.h_one, hf_p1]
          exact ⟨by wram_simp, by wram_simp [hx₂_r1, hx₁_r1, hr1]; simp, by wram_simp,
            by wram_simp⟩
        obtain ⟨x₃, he_n, hx₃_rS, hx₃_r1, hx₃_r2, hx₃_mem⟩ := hneg_tl
        have he_br : ExecWithin w triePatBranchCode x₂ x₃ 4 :=
          (ExecWithin.branch_neg hcond he_n).mono (by omega)
        have hL₃ : LayoutInv inp x₃ := hL₂.of_preserves he_br
        have hT₂_eq : T₂ = T₁ := by
          dsimp only [T₂, PTrie.insertPat]; simp only [hpos', ↓reduceIte]; rfl
        refine ⟨x₃, he_br, hL₃, ?_,
          (hx₃_rS.trans hx₂_rS).trans (congrArg PTrie.numStates hT₂_eq.symm),
          hx₃_r1, hx₃_r2, ?_⟩
        · rwa [hx₃_mem, hT₂_eq]
        · rwa [hx₃_mem]
    obtain ⟨x₃, he_tl_br, hL₃, hM₃, hx₃_rS, hx₃_r1, hx₃_r2, hhold₃⟩ := hpat_tl
    have hT₂_inv : TreeInv inp.alphabetSize T₂ := by
      dsimp only [T₂, PTrie.insertPat]
      split_ifs with hp0
      · refine { hT₁_inv with
          term_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT₁_inv.term_zero
          term_oob := fun z hz => by
            dsimp only [T₁, u₁] at hu₁_lt hz ⊢
            rw [Function.update_of_ne (by omega)]; exact hT₁_inv.term_oob z hz }
      · exact hT₁_inv
    have hT₂_num_eq : T₂.numStates = T₁.numStates := by
      dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
    obtain ⟨y, he_rest, hLy, hMy, hy_rS⟩ :=
      exec_triePatLoop inp w hw ps T₂ x₃ hL₃ hM₃ hT₂_inv
        (by rw [hT₂_num_eq]; simp only [totalPatternLen_cons] at hbud; omega)
        hx₃_rS hx₃_r1
        (by
          rw [hx₃_r2, hx₂_r2, hx₁_r2]
          simp only [List.length_cons, List.length_append] at hptr_ub
          omega)
        (by rwa [hx₃_r2]) hps_val
    refine ⟨y, (ExecWithin.loop_iter hc (he_hd.seq (he_chars.seq he_tl_br)) he_rest).mono
      (by simp only [totalPatternLen_cons, List.length_cons]; omega), hLy, hMy, hy_rS⟩

private theorem exec_buildTrie (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x) (hM : TrieMem inp PTrie.init x.mem) :
    ∃ y, ExecWithin w buildTrieCode x y
        (19 * inp.maxS + 11 * inp.patterns.length + 5) ∧
      LayoutInv inp y ∧
      TrieMem inp inp.trie y.mem := by
  have hlo := layout_order inp
  have hf1 : Fits w 1 := fits_of_le_outBase hw (by omega)
  have hinit : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ rState ← #1; r1 ← numPat; r2 ← patBase ]) x x₀ 3 ∧
      x₀.regs rState = 1 ∧ x₀.regs r1 = inp.patterns.length ∧ x₀.regs r2 = 5 ∧
      x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hf1, hL.h_numPat, hL.h_patBase]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hrS₀, hr1₀, hr2₀, hm₀⟩ := hinit
  have hL₀ : LayoutInv inp x₀ :=
    hL.of_preserves he₀
  obtain ⟨y, he_loop, hLy, hMy, _⟩ :=
    exec_triePatLoop inp w hw inp.patterns PTrie.init x₀ hL₀ (by rwa [hm₀])
      (treeInv_init _) (by dsimp only [PTrie.init]; omega)
      hrS₀ hr1₀
      (by rw [hr2₀, length_encodePatterns]; omega)
      (by rw [hr2₀, hm₀]; exact hM.pats) hvalid.1
  rw [Input.trie_eq]
  exact ⟨y, (he₀.seq he_loop).mono (by omega), hLy, hMy⟩

/-! ## Phase 3: Breadth-first automaton construction (`bfsBuildCode`) -/

private structure BFSMem (inp : Input) (T : PTrie) (B : PBFS) (mem : ℕ → ℕ) : Prop where
  txt : Block.HoldsList inp.textBase inp.text mem
  trie_cell : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
    mem (inp.trieBase + u * inp.alphabetSize + c) = T.trie u c
  delta_cell : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
    mem (inp.deltaBase + u * inp.alphabetSize + c) = B.delta u c
  fail_cell : ∀ u < inp.maxS, mem (inp.failBase + u) = B.fail u
  depth_cell : ∀ u < inp.maxS, mem (inp.depthBase + u) = T.depth u
  term_cell : ∀ u < inp.maxS, mem (inp.termBase + u) = T.isTerm u
  outHead_cell : ∀ u < inp.maxS, mem (inp.outHeadBase + u) = B.outHead u
  outNext_cell : ∀ u < inp.maxS, mem (inp.outNextBase + u) = B.outNext u
  queue_cell : ∀ i < inp.maxS, mem (inp.queueBase + i) = B.queue i

private theorem bfsMem_init {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    (hM : TrieMem inp T mem) : BFSMem inp T PBFS.init mem where
  txt := hM.txt
  trie_cell := hM.trie_cell
  delta_cell := fun u hu c hc => by
    have hlo := layout_order inp
    have hlt := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
    exact hM.zero_df _ (by omega) (by omega)
  fail_cell := fun u hu => by
    have hlo := layout_order inp
    exact hM.zero_df _ (by omega) (by omega)
  depth_cell := hM.depth_cell
  term_cell := hM.term_cell
  outHead_cell := fun u hu => by
    have hlo := layout_order inp
    exact hM.zero_rest _ (by omega) (by omega)
  outNext_cell := fun u hu => by
    have hlo := layout_order inp
    exact hM.zero_rest _ (by omega) (by omega)
  queue_cell := fun i hi => by
    have hlo := layout_order inp
    exact hM.zero_rest _ (by omega) (by omega)

private theorem bfsMem_of_set_delta {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {u₀ a dval : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with delta := fun u c => if u = u₀ ∧ c = a then dval else B.delta u c }
      (Function.update mem (inp.deltaBase + (u₀ * inp.alphabetSize + a)) dval) := by
  have hlo := layout_order inp
  have hrm₀ := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu₀ ha
  refine
    { txt := hM.txt.frame fun addr ha1 ha2 => Function.update_of_ne (by omega) _ _
      trie_cell := fun u hu c hc => by
        have huc := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        rw [Function.update_of_ne (by omega)]
        exact hM.trie_cell u hu c hc
      delta_cell := fun u hu c hc => by
        dsimp only
        by_cases hrc : u = u₀ ∧ c = a
        · obtain ⟨rfl, rfl⟩ := hrc
          simp only [and_self, ↓reduceIte]
          rw [← Nat.add_assoc, Function.update_self]
        · simp only [hrc, ↓reduceIte]
          have hne : inp.deltaBase + u * inp.alphabetSize + c ≠
              inp.deltaBase + (u₀ * inp.alphabetSize + a) := fun heq => by
            obtain ⟨hc_eq, hu_eq⟩ := Nat.eq_of_add_mul_eq (b := u) (b' := u₀) hc ha (by omega)
            exact hrc ⟨hu_eq, hc_eq⟩
          rw [Function.update_of_ne hne]
          exact hM.delta_cell u hu c hc
      fail_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.fail_cell u hu
      depth_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.depth_cell u hu
      term_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.term_cell u hu
      outHead_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.outHead_cell u hu
      outNext_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.outNext_cell u hu
      queue_cell := fun i hi => by
        rw [Function.update_of_ne (by omega)]; exact hM.queue_cell i hi }

private theorem bfsMem_of_set_fail_queue {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {s fval : ℕ} (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        fail := Function.update B.fail s fval
        queue := Function.update B.queue B.qTail s
        qTail := B.qTail + 1 }
      (Function.update (Function.update mem (inp.failBase + s) fval)
        (inp.queueBase + B.qTail) s) := by
  have hlo := layout_order inp
  refine
    { txt := hM.txt.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have huc := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.trie_cell u hu c hc
      delta_cell := fun u hu c hc => by
        have huc := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.delta_cell u hu c hc
      fail_cell := fun u hu => by
        dsimp only
        rw [Function.update_of_ne (by omega)]
        by_cases hus : u = s
        · subst hus; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne hus]
          exact hM.fail_cell u hu
      depth_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.depth_cell u hu
      term_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.term_cell u hu
      outHead_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.outHead_cell u hu
      outNext_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.outNext_cell u hu
      queue_cell := fun i hi => by
        dsimp only
        by_cases hiq : i = B.qTail
        · subst hiq; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne hiq]
          exact hM.queue_cell i hi }

private theorem bfsMem_of_set_out {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {s onval ohval : ℕ} (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        outHead := Function.update B.outHead s ohval
        outNext := Function.update B.outNext s onval }
      (Function.update (Function.update mem (inp.outNextBase + s) onval)
        (inp.outHeadBase + s) ohval) := by
  have hlo := layout_order inp
  refine
    { txt := hM.txt.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have huc := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.trie_cell u hu c hc
      delta_cell := fun u hu c hc => by
        have huc := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.delta_cell u hu c hc
      fail_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.fail_cell u hu
      depth_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.depth_cell u hu
      term_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.term_cell u hu
      outHead_cell := fun u hu => by
        dsimp only
        by_cases hus : u = s
        · subst hus; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne hus]
          exact hM.outHead_cell u hu
      outNext_cell := fun u hu => by
        dsimp only
        rw [Function.update_of_ne (by omega)]
        by_cases hus : u = s
        · subst hus; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne hus]
          exact hM.outNext_cell u hu
      queue_cell := fun i hi => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.queue_cell i hi }

private theorem bfsMem_of_enqueue {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {u₀ a s fval onval ohval : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        delta := fun u c => if u = u₀ ∧ c = a then s else B.delta u c
        fail := Function.update B.fail s fval
        outHead := Function.update B.outHead s ohval
        outNext := Function.update B.outNext s onval
        queue := Function.update B.queue B.qTail s
        qTail := B.qTail + 1 }
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update mem (inp.deltaBase + (u₀ * inp.alphabetSize + a)) s)
              (inp.failBase + s) fval)
            (inp.queueBase + B.qTail) s)
          (inp.outNextBase + s) onval)
        (inp.outHeadBase + s) ohval) :=
  bfsMem_of_set_out hs (bfsMem_of_set_fail_queue hs (bfsMem_of_set_delta hu₀ ha hM))

private theorem exec_bfsRootLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (k a : ℕ) (B : PBFS) (x : Data 26),
      a + k = inp.alphabetSize →
      LayoutInv inp x →
      BFSMem inp inp.trie B x.mem →
      RootLoopInv inp.patterns inp.alphabetSize inp.trie a B →
      x.regs r1 = 0 →
      x.regs r2 = B.qTail →
      x.regs r5 = a →
      ∃ y, ExecWithin w (.loop (.lt r5 sigma) bfsRootStepCode) x y (21 * k + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie (PBFS.rootLoop inp.trie k a B) y.mem ∧
        y.regs r1 = 0 ∧
        y.regs r2 = (PBFS.rootLoop inp.trie k a B).qTail := by
  intro k
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  induction k with
  | zero =>
    intro a B x hak hL hM _ hr1 hr2 hr5
    have hstop : ¬(Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hr1, hr2⟩
  | succ k ih =>
    intro a B x hak hL hM hinv hr1 hr2 hr5
    have ha : a < inp.alphabetSize := by omega
    have hc : (Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; exact ha
    have h0_maxS : 0 < inp.maxS := by omega
    have ha_rm : a < inp.maxS * inp.alphabetSize := by
      simpa only [Nat.mul_zero, Nat.zero_add] using Nat.mul_add_lt_mul_of_lt_of_lt h0_maxS ha
    have ht_read : x.mem (inp.trieBase + a) = inp.trie.trie 0 a := by
      simpa only [Nat.zero_mul, Nat.add_zero] using hM.trie_cell 0 h0_maxS a ha
    have hf_ta : Fits w (inp.trieBase + a) := fits_of_le_outBase hw (by omega)
    have hf_da : Fits w (inp.deltaBase + a) := fits_of_le_outBase hw (by omega)
    have hf_a1 : Fits w (a + 1) := fits_of_le_outBase hw (by omega)
    have hinv_next := rootStep_spec hT hchar hterm ha hinv
    set B' := PBFS.rootStep inp.trie B a
    have hstep : ∃ x₁, ExecWithin w bfsRootStepCode x x₁ 19 ∧
        LayoutInv inp x₁ ∧ BFSMem inp inp.trie B' x₁.mem ∧
        x₁.regs r1 = 0 ∧ x₁.regs r2 = B'.qTail ∧ x₁.regs r5 = a + 1 := by
      have hld : ∃ x₀, ExecWithin w (ram[ r6 ← trieBase + r5; r6 ← *r6 ]) x x₀ 2 ∧
          x₀.regs r6 = inp.trie.trie 0 a ∧ x₀.regs r1 = 0 ∧ x₀.regs r2 = B.qTail ∧
          x₀.regs r5 = a ∧ x₀.mem = x.mem := by
        refine WP.exists_execWithin ?_
        wram_exec [hL.h_trieBase, hr5, ht_read, hf_ta]
        exact ⟨by wram_simp, by wram_simp [hr1], by wram_simp [hr2], by wram_simp [hr5],
          by wram_simp⟩
      obtain ⟨x₀, he₀, hx₀_r6, hx₀_r1, hx₀_r2, hx₀_r5, hx₀_mem⟩ := hld
      have hL₀ : LayoutInv inp x₀ :=
        hL.of_preserves he₀
      by_cases hs_pos : 0 < inp.trie.trie 0 a
      · set s := inp.trie.trie 0 a
        have hs_pos' : 0 < inp.trie.trie 0 a := hs_pos
        have hcond_s : (Cond.lt zero r6).Holds x₀ := by
          simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
        have hs_lt : s < inp.trie.numStates := hT.trie_lt 0 hT.one_le a ha
        have hs_maxS : s < inp.maxS := lt_of_lt_of_le hs_lt hT_maxS
        have hqt_lt : B.qTail < inp.trie.numStates :=
          qTail_lt_numStates hT.one_le
            (fun i hi => ⟨(hinv.q_bounds i hi).1, (hinv.q_bounds i hi).2.1⟩) hinv.q_inj
        have hqt_maxS : B.qTail < inp.maxS := lt_of_lt_of_le hqt_lt hT_maxS
        have hf_fs : Fits w (inp.failBase + s) := fits_of_le_outBase hw (by omega)
        have hf_qt : Fits w (inp.queueBase + B.qTail) := fits_of_le_outBase hw (by omega)
        have hf_qt1 : Fits w (B.qTail + 1) := fits_of_le_outBase hw (by omega)
        have hf_ons : Fits w (inp.outNextBase + s) := fits_of_le_outBase hw (by omega)
        have hf_tms : Fits w (inp.termBase + s) := fits_of_le_outBase hw (by omega)
        have hf_ohs : Fits w (inp.outHeadBase + s) := fits_of_le_outBase hw (by omega)
        have htm_read : x₀.mem (inp.termBase + s) = inp.trie.isTerm s := by
          rw [hx₀_mem]; exact hM.term_cell s hs_maxS
        have hmid : ∃ x_m, ExecWithin w (ram[
            r7 ← deltaBase + r5; *r7 ← r6;
            r7 ← failBase + r6; *r7 ← zero;
            r7 ← queueBase + r2; *r7 ← r6;
            r2 ← r2 + one;
            r7 ← outNextBase + r6; *r7 ← zero;
            rState ← termBase + r6; rState ← *rState ]) x₀ x_m 11 ∧
          x_m.regs rState = inp.trie.isTerm s ∧ x_m.regs r6 = s ∧
          x_m.regs r1 = 0 ∧ x_m.regs r2 = B.qTail + 1 ∧ x_m.regs r5 = a ∧
          x_m.mem = Function.update
            (Function.update
              (Function.update
                (Function.update x.mem (inp.deltaBase + a) s)
                (inp.failBase + s) 0)
              (inp.queueBase + B.qTail) s)
            (inp.outNextBase + s) 0 := by
          refine WP.exists_execWithin ?_
          have hne1 : inp.termBase + s ≠ inp.outNextBase + s := by omega
          have hne2 : inp.termBase + s ≠ inp.queueBase + B.qTail := by omega
          have hne3 : inp.termBase + s ≠ inp.failBase + s := by omega
          have hne4 : inp.termBase + s ≠ inp.deltaBase + a := by omega
          wram_exec [hL₀.h_deltaBase, hL₀.h_failBase, hL₀.h_queueBase, hL₀.h_outNextBase,
            hL₀.h_termBase, hL₀.h_zero, hL₀.h_one, hx₀_r5, hx₀_r6, hx₀_r2, hf_da, hf_fs,
            hf_qt, hf_qt1, hf_ons, hf_tms, htm_read, hne1, hne2, hne3, hne4]
          exact ⟨by wram_simp, by wram_simp [hx₀_r6], by wram_simp [hx₀_r1], by wram_simp,
            by wram_simp [hx₀_r5], by wram_simp [hx₀_mem]⟩
        obtain ⟨x_m, he_m, hxm_rS, hxm_r6, hxm_r1, hxm_r2, hxm_r5, hxm_mem⟩ := hmid
        have hL_m : LayoutInv inp x_m :=
          hL₀.of_preserves he_m
        have hoh_br : ∃ x₁, ExecWithin w
            (.branch (.lt zero rState)
              (ram[ r7 ← outHeadBase + r6; *r7 ← r6; r5 ← r5 + one ])
              (ram[ r7 ← outHeadBase + r6; *r7 ← zero; r5 ← r5 + one ])) x_m x₁ 5 ∧
            x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail + 1 ∧ x₁.regs r5 = a + 1 ∧
            x₁.mem = Function.update x_m.mem (inp.outHeadBase + s)
              (if 0 < inp.trie.isTerm s then s else 0) := by
          by_cases ht_pos : 0 < inp.trie.isTerm s
          · have hct : (Cond.lt zero rState).Holds x_m := by
              simp only [Cond.holds_lt, hL_m.h_zero, hxm_rS]; exact ht_pos
            have hp : ∃ x₁, ExecWithin w
                (ram[ r7 ← outHeadBase + r6; *r7 ← r6; r5 ← r5 + one ]) x_m x₁ 3 ∧
                x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail + 1 ∧ x₁.regs r5 = a + 1 ∧
                x₁.mem = Function.update x_m.mem (inp.outHeadBase + s) s := by
              refine WP.exists_execWithin ?_
              wram_exec [hL_m.h_outHeadBase, hL_m.h_one, hxm_r6, hxm_r5, hf_ohs, hf_a1]
              exact ⟨by wram_simp [hxm_r1], by wram_simp [hxm_r2], by wram_simp, by wram_simp⟩
            obtain ⟨x₁, hep, h1, h2, h5, hm1⟩ := hp
            simp only [ht_pos, ↓reduceIte]
            exact ⟨x₁, (ExecWithin.branch_pos hct hep).mono (by omega), h1, h2, h5, hm1⟩
          · have hct : ¬(Cond.lt zero rState).Holds x_m := by
              simp only [Cond.holds_lt, hL_m.h_zero, hxm_rS]; exact ht_pos
            have hn : ∃ x₁, ExecWithin w
                (ram[ r7 ← outHeadBase + r6; *r7 ← zero; r5 ← r5 + one ]) x_m x₁ 3 ∧
                x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail + 1 ∧ x₁.regs r5 = a + 1 ∧
                x₁.mem = Function.update x_m.mem (inp.outHeadBase + s) 0 := by
              refine WP.exists_execWithin ?_
              wram_exec [hL_m.h_outHeadBase, hL_m.h_zero, hL_m.h_one, hxm_r6, hxm_r5,
                hf_ohs, hf_a1]
              exact ⟨by wram_simp [hxm_r1], by wram_simp [hxm_r2], by wram_simp, by wram_simp⟩
            obtain ⟨x₁, hen, h1, h2, h5, hm1⟩ := hn
            simp only [ht_pos, ↓reduceIte]
            exact ⟨x₁, ExecWithin.branch_neg hct hen, h1, h2, h5, hm1⟩
        obtain ⟨x₁, he_oh, hx₁_r1, hx₁_r2, hx₁_r5, hx₁_mem⟩ := hoh_br
        have he_tot : ExecWithin w bfsRootStepCode x x₁ 19 :=
          (he₀.seq (ExecWithin.branch_pos hcond_s (he_m.seq he_oh))).mono (by omega)
        have hL₁ : LayoutInv inp x₁ :=
          hL.of_preserves he_tot
        have hB'_qt : B'.qTail = B.qTail + 1 := by
          dsimp only [B', PBFS.rootStep]; simp only [hs_pos', ↓reduceIte]
        refine ⟨x₁, he_tot, hL₁, ?_, hx₁_r1, hx₁_r2.trans hB'_qt.symm, hx₁_r5⟩
        rw [hx₁_mem, hxm_mem]
        dsimp only [B', PBFS.rootStep]
        simp only [hs_pos', ↓reduceIte]
        simpa only [Nat.zero_mul, Nat.zero_add] using
          bfsMem_of_enqueue h0_maxS ha hs_maxS hM
      · have hs_pos' : ¬0 < inp.trie.trie 0 a := hs_pos
        have hcond_s : ¬(Cond.lt zero r6).Holds x₀ := by
          simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
        have hneg : ∃ x₁, ExecWithin w
            (ram[ r7 ← deltaBase + r5; *r7 ← zero; r5 ← r5 + one ]) x₀ x₁ 3 ∧
            x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail ∧ x₁.regs r5 = a + 1 ∧
            x₁.mem = Function.update x.mem (inp.deltaBase + a) 0 := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₀.h_deltaBase, hL₀.h_zero, hL₀.h_one, hx₀_r5, hf_da, hf_a1]
          exact ⟨by wram_simp [hx₀_r1], by wram_simp [hx₀_r2], by wram_simp,
            by wram_simp [hx₀_mem]⟩
        obtain ⟨x₁, he_n, hx₁_r1, hx₁_r2, hx₁_r5, hx₁_mem⟩ := hneg
        have he_tot : ExecWithin w bfsRootStepCode x x₁ 19 :=
          (he₀.seq (ExecWithin.branch_neg hcond_s he_n)).mono (by omega)
        have hL₁ : LayoutInv inp x₁ :=
          hL.of_preserves he_tot
        have hB'_qt : B'.qTail = B.qTail := by
          dsimp only [B', PBFS.rootStep]; simp only [hs_pos', ↓reduceIte]
        refine ⟨x₁, he_tot, hL₁, ?_, hx₁_r1, hx₁_r2.trans hB'_qt.symm, hx₁_r5⟩
        rw [hx₁_mem]
        dsimp only [B', PBFS.rootStep]
        simp only [hs_pos', ↓reduceIte]
        simpa only [Nat.zero_mul, Nat.zero_add] using bfsMem_of_set_delta h0_maxS ha hM
    obtain ⟨x₁, he_st, hL₁, hM₁, hx₁_r1, hx₁_r2, hx₁_r5⟩ := hstep
    obtain ⟨y, he_tl, hLy, hMy, hy_r1, hy_r2⟩ :=
      ih (a + 1) B' x₁ (by omega) hL₁ hM₁ hinv_next hx₁_r1 hx₁_r2 hx₁_r5
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hy_r1, hy_r2⟩

private theorem exec_bfsInnerStore (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {r a s df qt : ℕ} {x₀ : Data 26} {mem₀ : ℕ → ℕ}
    (ha : a < inp.alphabetSize) (hr_maxS : r < inp.maxS)
    (hs_maxS : s < inp.maxS) (hqt_maxS : qt < inp.maxS)
    (hL₀ : LayoutInv inp x₀)
    (hx₀_r2 : x₀.regs r2 = qt) (hx₀_r3 : x₀.regs r3 = r)
    (hx₀_r5 : x₀.regs r5 = a) (hx₀_r6 : x₀.regs r6 = s) (hx₀_r7 : x₀.regs r7 = df)
    (hx₀_mem : x₀.mem = mem₀) :
    ∃ x_s, ExecWithin w bfsInnerStoreCode x₀ x_s 9 ∧
      LayoutInv inp x_s ∧
      x_s.regs r6 = s ∧ x_s.regs r7 = df ∧
      x_s.regs r1 = x₀.regs r1 ∧ x_s.regs r2 = qt + 1 ∧
      x_s.regs r3 = r ∧ x_s.regs r4 = x₀.regs r4 ∧ x_s.regs r5 = a ∧
      x_s.mem = Function.update
        (Function.update
          (Function.update mem₀ (inp.deltaBase + (r * inp.alphabetSize + a)) s)
          (inp.failBase + s) df)
        (inp.queueBase + qt) s := by
  have hlo := layout_order inp
  have hrm_r := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hr_maxS ha
  have hf_mr : Fits w (r * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_ra : Fits w (r * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_dra : Fits w (inp.deltaBase + (r * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_fs : Fits w (inp.failBase + s) := fits_of_le_outBase hw (by omega)
  have hf_qt : Fits w (inp.queueBase + qt) := fits_of_le_outBase hw (by omega)
  have hf_qt1 : Fits w (qt + 1) := fits_of_le_outBase hw (by omega)
  have hm1 : ∃ x_s, ExecWithin w bfsInnerStoreCode x₀ x_s 9 ∧
      x_s.regs r6 = s ∧ x_s.regs r7 = df ∧
      x_s.regs r1 = x₀.regs r1 ∧ x_s.regs r2 = qt + 1 ∧
      x_s.regs r3 = r ∧ x_s.regs r4 = x₀.regs r4 ∧ x_s.regs r5 = a ∧
      x_s.mem = Function.update
        (Function.update
          (Function.update mem₀ (inp.deltaBase + (r * inp.alphabetSize + a)) s)
          (inp.failBase + s) df)
        (inp.queueBase + qt) s := by
    refine WP.exists_execWithin ?_
    unfold bfsInnerStoreCode
    wram_exec [hL₀.h_sigma, hL₀.h_deltaBase, hL₀.h_failBase, hL₀.h_queueBase, hL₀.h_one,
      hx₀_r3, hx₀_r5, hx₀_r6, hx₀_r7, hx₀_r2, hf_mr, hf_ra, hf_dra, hf_fs, hf_qt, hf_qt1]
    exact ⟨by wram_simp [hx₀_r6], by wram_simp [hx₀_r7], by wram_simp,
      by wram_simp, by wram_simp [hx₀_r3], by wram_simp, by wram_simp [hx₀_r5],
      by wram_simp [hx₀_mem]⟩
  obtain ⟨x_s, he_s, r6s, r7s, r1s, r2s, r3s, r4s, r5s, mems⟩ := hm1
  exact ⟨x_s, he_s, hL₀.of_preserves he_s, r6s, r7s, r1s, r2s, r3s, r4s, r5s, mems⟩

private theorem exec_bfsInnerLink (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {r a s df qt ohdf tms : ℕ} {x_s : Data 26} {mem₀ : ℕ → ℕ}
    (ha : a < inp.alphabetSize) (hr_maxS : r < inp.maxS)
    (hdf_maxS : df < inp.maxS) (hs_maxS : s < inp.maxS)
    (hL_s : LayoutInv inp x_s)
    (hxs_r6 : x_s.regs r6 = s) (hxs_r7 : x_s.regs r7 = df)
    (hxs_mem : x_s.mem = Function.update
      (Function.update
        (Function.update mem₀ (inp.deltaBase + (r * inp.alphabetSize + a)) s)
        (inp.failBase + s) df)
      (inp.queueBase + qt) s)
    (hoh_read : mem₀ (inp.outHeadBase + df) = ohdf)
    (htm_read : mem₀ (inp.termBase + s) = tms) :
    ∃ x_m, ExecWithin w bfsInnerLinkCode x_s x_m 6 ∧
      LayoutInv inp x_m ∧
      x_m.regs rState = tms ∧ x_m.regs r6 = s ∧ x_m.regs r7 = ohdf ∧
      x_m.regs r1 = x_s.regs r1 ∧ x_m.regs r2 = x_s.regs r2 ∧
      x_m.regs r3 = x_s.regs r3 ∧ x_m.regs r4 = x_s.regs r4 ∧ x_m.regs r5 = x_s.regs r5 ∧
      x_m.mem = Function.update x_s.mem (inp.outNextBase + s) ohdf := by
  have hlo := layout_order inp
  have hrm_r := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hr_maxS ha
  have hf_ohdf : Fits w (inp.outHeadBase + df) := fits_of_le_outBase hw (by omega)
  have hf_ons : Fits w (inp.outNextBase + s) := fits_of_le_outBase hw (by omega)
  have hf_tms : Fits w (inp.termBase + s) := fits_of_le_outBase hw (by omega)
  have hoh_xs : x_s.mem (inp.outHeadBase + df) = ohdf := by
    rw [hxs_mem]
    simp (disch := omega) only [Function.update_of_ne]
    exact hoh_read
  have htm_xs : x_s.mem (inp.termBase + s) = tms := by
    rw [hxs_mem]
    simp (disch := omega) only [Function.update_of_ne]
    exact htm_read
  have hne_tm_on : inp.termBase + s ≠ inp.outNextBase + s := by omega
  have hm2 : ∃ x_m, ExecWithin w bfsInnerLinkCode x_s x_m 6 ∧
      x_m.regs rState = tms ∧ x_m.regs r6 = s ∧ x_m.regs r7 = ohdf ∧
      x_m.regs r1 = x_s.regs r1 ∧ x_m.regs r2 = x_s.regs r2 ∧
      x_m.regs r3 = x_s.regs r3 ∧ x_m.regs r4 = x_s.regs r4 ∧ x_m.regs r5 = x_s.regs r5 ∧
      x_m.mem = Function.update x_s.mem (inp.outNextBase + s) ohdf := by
    refine WP.exists_execWithin ?_
    unfold bfsInnerLinkCode
    wram_exec [hL_s.h_outHeadBase, hL_s.h_outNextBase, hL_s.h_termBase,
      hxs_r6, hxs_r7, hf_ohdf, hf_ons, hf_tms, hoh_xs, htm_xs, hne_tm_on]
    exact ⟨by wram_simp, by wram_simp [hxs_r6], by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x_m, he_l, rSm, r6m, r7m, r1m, r2m, r3m, r4m, r5m, memm⟩ := hm2
  exact ⟨x_m, he_l, hL_s.of_preserves he_l, rSm, r6m, r7m, r1m, r2m, r3m, r4m, r5m, memm⟩

private theorem exec_bfsInnerBranch (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {a s ohdf tms : ℕ} {x_m : Data 26}
    (ha : a < inp.alphabetSize) (hs_maxS : s < inp.maxS)
    (hL_m : LayoutInv inp x_m)
    (hxm_rS : x_m.regs rState = tms) (hxm_r6 : x_m.regs r6 = s)
    (hxm_r7 : x_m.regs r7 = ohdf) (hxm_r5 : x_m.regs r5 = a) :
    ∃ x₁, ExecWithin w
        (.branch (.lt zero rState)
          (ram[ rState ← outHeadBase + r6; *rState ← r6; r5 ← r5 + one ])
          (ram[ rState ← outHeadBase + r6; *rState ← r7; r5 ← r5 + one ])) x_m x₁ 5 ∧
      x₁.regs r1 = x_m.regs r1 ∧ x₁.regs r2 = x_m.regs r2 ∧
      x₁.regs r3 = x_m.regs r3 ∧ x₁.regs r4 = x_m.regs r4 ∧ x₁.regs r5 = a + 1 ∧
      x₁.mem = Function.update x_m.mem (inp.outHeadBase + s)
        (if 0 < tms then s else ohdf) := by
  have hlo := layout_order inp
  have h0_maxS : 0 < inp.maxS := by omega
  have ha_rm := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt h0_maxS ha
  have hf_ohs : Fits w (inp.outHeadBase + s) := fits_of_le_outBase hw (by omega)
  have hf_a1 : Fits w (a + 1) := fits_of_le_outBase hw (by omega)
  by_cases ht_pos : 0 < tms
  · have hct : (Cond.lt zero rState).Holds x_m := by
      simp only [Cond.holds_lt, hL_m.h_zero, hxm_rS]; exact ht_pos
    have hp : ∃ x₁, ExecWithin w
        (ram[ rState ← outHeadBase + r6; *rState ← r6; r5 ← r5 + one ]) x_m x₁ 3 ∧
        x₁.regs r1 = x_m.regs r1 ∧ x₁.regs r2 = x_m.regs r2 ∧
        x₁.regs r3 = x_m.regs r3 ∧ x₁.regs r4 = x_m.regs r4 ∧ x₁.regs r5 = a + 1 ∧
        x₁.mem = Function.update x_m.mem (inp.outHeadBase + s) s := by
      refine WP.exists_execWithin ?_
      wram_exec [hL_m.h_outHeadBase, hL_m.h_one, hxm_r6, hxm_r5, hf_ohs, hf_a1]
      exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
    obtain ⟨x₁, hep, h1, h2, h3, h4, h5, hm_p⟩ := hp
    simp only [ht_pos, ↓reduceIte]
    exact ⟨x₁, (ExecWithin.branch_pos hct hep).mono (by omega), h1, h2, h3, h4, h5, hm_p⟩
  · have hct : ¬(Cond.lt zero rState).Holds x_m := by
      simp only [Cond.holds_lt, hL_m.h_zero, hxm_rS]; exact ht_pos
    have hn : ∃ x₁, ExecWithin w
        (ram[ rState ← outHeadBase + r6; *rState ← r7; r5 ← r5 + one ]) x_m x₁ 3 ∧
        x₁.regs r1 = x_m.regs r1 ∧ x₁.regs r2 = x_m.regs r2 ∧
        x₁.regs r3 = x_m.regs r3 ∧ x₁.regs r4 = x_m.regs r4 ∧ x₁.regs r5 = a + 1 ∧
        x₁.mem = Function.update x_m.mem (inp.outHeadBase + s) ohdf := by
      refine WP.exists_execWithin ?_
      wram_exec [hL_m.h_outHeadBase, hL_m.h_one, hxm_r6, hxm_r7, hxm_r5, hf_ohs, hf_a1]
      exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
    obtain ⟨x₁, hen, h1, h2, h3, h4, h5, hm_n⟩ := hn
    simp only [ht_pos, ↓reduceIte]
    exact ⟨x₁, ExecWithin.branch_neg hct hen, h1, h2, h3, h4, h5, hm_n⟩

private theorem exec_bfsInnerStep_pos (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) {qh r fr a s df : ℕ} {B : PBFS} {x x₀ : Data 26}
    (ha : a < inp.alphabetSize) (hr_maxS : r < inp.maxS) (hdf_maxS : df < inp.maxS)
    (hs_pos : 0 < s) (hs_lt : s < inp.trie.numStates)
    (hL : LayoutInv inp x) (hM : BFSMem inp inp.trie B x.mem)
    (hinv : InnerLoopInv inp.patterns inp.alphabetSize inp.trie qh r fr a B)
    (he₀ : ExecWithin w (ram[r6 ← r3 * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6;
      r7 ← r4 * sigma; r7 ← r7 + r5; r7 ← deltaBase + r7; r7 ← *r7]) x x₀ 8)
    (hx₀_r6 : x₀.regs r6 = s) (hx₀_r7 : x₀.regs r7 = df)
    (hx₀_r1 : x₀.regs r1 = B.qHead) (hx₀_r2 : x₀.regs r2 = B.qTail)
    (hx₀_r3 : x₀.regs r3 = r) (hx₀_r4 : x₀.regs r4 = fr) (hx₀_r5 : x₀.regs r5 = a)
    (hx₀_mem : x₀.mem = x.mem)
    (hs_eq : inp.trie.trie r a = s) (hdf_eq : B.delta fr a = df) :
    ∃ x₁, ExecWithin w bfsInnerStepCode x x₁ 29 ∧
      LayoutInv inp x₁ ∧ BFSMem inp inp.trie (PBFS.innerStep inp.trie r fr B a) x₁.mem ∧
      x₁.regs r1 = (PBFS.innerStep inp.trie r fr B a).qHead ∧
      x₁.regs r2 = (PBFS.innerStep inp.trie r fr B a).qTail ∧
      x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = a + 1 := by
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hL₀ : LayoutInv inp x₀ := hL.of_preserves he₀
  have hs_maxS : s < inp.maxS := lt_of_lt_of_le hs_lt hT_maxS
  have hqt_maxS : B.qTail < inp.maxS :=
    lt_of_lt_of_le (qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj) hT_maxS
  have hcond_s : (Cond.lt zero r6).Holds x₀ := by
    simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
  obtain ⟨x_s, he_s, hL_s, hxs_r6, hxs_r7, hxs_r1, hxs_r2, hxs_r3, hxs_r4, hxs_r5, hxs_mem⟩ :=
    exec_bfsInnerStore inp w hw ha hr_maxS hs_maxS hqt_maxS hL₀ hx₀_r2 hx₀_r3 hx₀_r5 hx₀_r6
      hx₀_r7 hx₀_mem
  obtain ⟨x_m, he_l, hL_m, hxm_rS, hxm_r6, hxm_r7, hxm_r1, hxm_r2, hxm_r3, hxm_r4, hxm_r5,
      hxm_mem⟩ :=
    exec_bfsInnerLink inp w hw ha hr_maxS hdf_maxS hs_maxS hL_s hxs_r6 hxs_r7 hxs_mem
      (hM.outHead_cell df hdf_maxS) (hM.term_cell s hs_maxS)
  obtain ⟨x₁, he_oh, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_mem⟩ :=
    exec_bfsInnerBranch inp w hw ha hs_maxS hL_m hxm_rS hxm_r6 hxm_r7 (hxm_r5.trans hxs_r5)
  have he_tot : ExecWithin w bfsInnerStepCode x x₁ 29 :=
    (he₀.seq (ExecWithin.branch_pos hcond_s ((he_s.seq he_l).seq he_oh))).mono (by omega)
  have hB'_eq : PBFS.innerStep inp.trie r fr B a =
      { B with
        delta := fun u c => if u = r ∧ c = a then s else B.delta u c
        fail := Function.update B.fail s df
        outHead := Function.update B.outHead s
          (if 0 < inp.trie.isTerm s then s else B.outHead df)
        outNext := Function.update B.outNext s (B.outHead df)
        queue := Function.update B.queue B.qTail s
        qTail := B.qTail + 1 } := by
    dsimp only [PBFS.innerStep]
    simp only [hs_eq, hdf_eq, hs_pos, ↓reduceIte]
  rw [hB'_eq]
  refine ⟨x₁, he_tot, hL.of_preserves he_tot, ?_,
    hx₁_r1.trans (hxm_r1.trans (hxs_r1.trans hx₀_r1)),
    hx₁_r2.trans (hxm_r2.trans hxs_r2),
    hx₁_r3.trans (hxm_r3.trans hxs_r3),
    hx₁_r4.trans (hxm_r4.trans (hxs_r4.trans hx₀_r4)),
    hx₁_r5⟩
  rw [hx₁_mem, hxm_mem, hxs_mem]
  exact bfsMem_of_enqueue hr_maxS ha hs_maxS hM

private theorem exec_bfsInnerStep (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) {qh r fr a : ℕ} {B : PBFS} {x : Data 26}
    (ha : a < inp.alphabetSize) (hL : LayoutInv inp x) (hM : BFSMem inp inp.trie B x.mem)
    (hinv : InnerLoopInv inp.patterns inp.alphabetSize inp.trie qh r fr a B)
    (hr1 : x.regs r1 = B.qHead) (hr2 : x.regs r2 = B.qTail)
    (hr3 : x.regs r3 = r) (hr4 : x.regs r4 = fr) (hr5 : x.regs r5 = a) :
    ∃ x₁, ExecWithin w bfsInnerStepCode x x₁ 29 ∧
      LayoutInv inp x₁ ∧ BFSMem inp inp.trie (PBFS.innerStep inp.trie r fr B a) x₁.mem ∧
      x₁.regs r1 = (PBFS.innerStep inp.trie r fr B a).qHead ∧
      x₁.regs r2 = (PBFS.innerStep inp.trie r fr B a).qTail ∧
      x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = a + 1 := by
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hlo := layout_order inp
  have hqh_lt : qh < B.qTail := by
    have := hinv.qHead_eq; have := hinv.qHead_le; omega
  have hr_lt : r < inp.trie.numStates := by
    have h := (hinv.q_bounds qh hqh_lt).2
    rwa [hinv.r_eq] at h
  have hr_maxS : r < inp.maxS := lt_of_lt_of_le hr_lt hT_maxS
  have hfr_lt : fr < inp.trie.numStates := by
    have hfexp := hinv.fr_mem
    simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hfexp
    rcases hfexp with rfl | ⟨i, hi, rfl⟩
    · exact hT.one_le
    · exact (hinv.q_bounds i (lt_trans hi hqh_lt)).2
  have hfr_maxS : fr < inp.maxS := lt_of_lt_of_le hfr_lt hT_maxS
  have hrm_r : r * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hr_maxS ha
  have hrm_fr : fr * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hfr_maxS ha
  have ht_read : x.mem (inp.trieBase + (r * inp.alphabetSize + a)) = inp.trie.trie r a := by
    rw [← Nat.add_assoc]; exact hM.trie_cell r hr_maxS a ha
  have hd_read : x.mem (inp.deltaBase + (fr * inp.alphabetSize + a)) = B.delta fr a := by
    rw [← Nat.add_assoc]; exact hM.delta_cell fr hfr_maxS a ha
  have hdf_lt : B.delta fr a < inp.trie.numStates :=
    mem_disc_lt hT.one_le hinv.q_bounds (hinv.delta_exp fr hinv.fr_mem a ha).1
  have hdf_maxS : B.delta fr a < inp.maxS := lt_of_lt_of_le hdf_lt hT_maxS
  have hf_mr : Fits w (r * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_ra : Fits w (r * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_tra : Fits w (inp.trieBase + (r * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_dra : Fits w (inp.deltaBase + (r * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_mfr : Fits w (fr * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_fra : Fits w (fr * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_dfra : Fits w (inp.deltaBase + (fr * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_a1 : Fits w (a + 1) := fits_of_le_outBase hw (by omega)
  have hld : ∃ x₀, ExecWithin w (ram[
      r6 ← r3 * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6;
      r7 ← r4 * sigma; r7 ← r7 + r5; r7 ← deltaBase + r7; r7 ← *r7 ]) x x₀ 8 ∧
      x₀.regs r6 = inp.trie.trie r a ∧ x₀.regs r7 = B.delta fr a ∧
      x₀.regs r1 = B.qHead ∧ x₀.regs r2 = B.qTail ∧
      x₀.regs r3 = r ∧ x₀.regs r4 = fr ∧ x₀.regs r5 = a ∧ x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hL.h_sigma, hL.h_trieBase, hL.h_deltaBase, hr3, hr4, hr5, ht_read, hd_read,
      hf_mr, hf_ra, hf_tra, hf_mfr, hf_fra, hf_dfra]
    exact ⟨by wram_simp, by wram_simp, by wram_simp [hr1], by wram_simp [hr2],
      by wram_simp [hr3], by wram_simp [hr4], by wram_simp [hr5], by wram_simp⟩
  obtain ⟨x₀, he₀, hx₀_r6, hx₀_r7, hx₀_r1, hx₀_r2, hx₀_r3, hx₀_r4, hx₀_r5, hx₀_mem⟩ := hld
  by_cases hs_pos : 0 < inp.trie.trie r a
  · exact exec_bfsInnerStep_pos inp w hvalid hw ha hr_maxS hdf_maxS hs_pos
      (hT.trie_lt r hr_lt a ha) hL hM hinv he₀ hx₀_r6 hx₀_r7 hx₀_r1 hx₀_r2 hx₀_r3 hx₀_r4
      hx₀_r5 hx₀_mem rfl rfl
  · have hL₀ : LayoutInv inp x₀ := hL.of_preserves he₀
    have hcond_s : ¬(Cond.lt zero r6).Holds x₀ := by
      simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
    generalize hdf_eq : B.delta fr a = df at hx₀_r7
    have hneg : ∃ x₁, ExecWithin w (ram[
        rState ← r3 * sigma; rState ← rState + r5; rState ← deltaBase + rState; *rState ← r7;
        r5 ← r5 + one ]) x₀ x₁ 5 ∧
        x₁.regs r1 = B.qHead ∧ x₁.regs r2 = B.qTail ∧
        x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = a + 1 ∧
        x₁.mem = Function.update x.mem (inp.deltaBase + (r * inp.alphabetSize + a)) df := by
      refine WP.exists_execWithin ?_
      wram_exec [hL₀.h_sigma, hL₀.h_deltaBase, hL₀.h_one, hx₀_r3, hx₀_r5, hx₀_r7,
        hf_mr, hf_ra, hf_dra, hf_a1]
      exact ⟨by wram_simp [hx₀_r1], by wram_simp [hx₀_r2], by wram_simp [hx₀_r3],
        by wram_simp [hx₀_r4], by wram_simp, by wram_simp [hx₀_mem]⟩
    obtain ⟨x₁, he_n, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_mem⟩ := hneg
    have he_tot : ExecWithin w bfsInnerStepCode x x₁ 29 :=
      (he₀.seq (ExecWithin.branch_neg hcond_s he_n)).mono (by omega)
    have hL₁ : LayoutInv inp x₁ := hL.of_preserves he_tot
    have hB'_eq : PBFS.innerStep inp.trie r fr B a =
        { B with delta := fun u c => if u = r ∧ c = a then df else B.delta u c } := by
      dsimp only [PBFS.innerStep]
      simp only [hs_pos, hdf_eq, ↓reduceIte]
    rw [hB'_eq]
    refine ⟨x₁, he_tot, hL₁, ?_, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5⟩
    rw [hx₁_mem]
    exact bfsMem_of_set_delta hr_maxS ha hM

private theorem exec_bfsInnerLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (qh r fr k a : ℕ) (B : PBFS) (x : Data 26),
      a + k = inp.alphabetSize →
      LayoutInv inp x →
      BFSMem inp inp.trie B x.mem →
      InnerLoopInv inp.patterns inp.alphabetSize inp.trie qh r fr a B →
      x.regs r1 = B.qHead →
      x.regs r2 = B.qTail →
      x.regs r3 = r →
      x.regs r4 = fr →
      x.regs r5 = a →
      ∃ y, ExecWithin w (.loop (.lt r5 sigma) bfsInnerStepCode) x y (31 * k + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie (PBFS.innerLoop inp.trie r fr k a B) y.mem ∧
        y.regs r1 = (PBFS.innerLoop inp.trie r fr k a B).qHead ∧
        y.regs r2 = (PBFS.innerLoop inp.trie r fr k a B).qTail := by
  intro qh r fr k
  obtain ⟨hT, _, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  induction k with
  | zero =>
    intro a B x hak hL hM _ hr1 hr2 _ _ hr5
    have hstop : ¬(Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hr1, hr2⟩
  | succ k ih =>
    intro a B x hak hL hM hinv hr1 hr2 hr3 hr4 hr5
    have ha : a < inp.alphabetSize := by omega
    have hc : (Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; exact ha
    have hinv_next := innerStep_spec hT hchar hterm ha hinv
    obtain ⟨x₁, he_st, hL₁, hM₁, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5⟩ :=
      exec_bfsInnerStep inp w hvalid hw ha hL hM hinv hr1 hr2 hr3 hr4 hr5
    obtain ⟨y, he_tl, hLy, hMy, hy_r1, hy_r2⟩ :=
      ih (a + 1) (PBFS.innerStep inp.trie r fr B a) x₁ (by omega) hL₁ hM₁ hinv_next
        hx₁_r1 hx₁_r2 hx₁_r3 hx₁_r4 hx₁_r5
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hy_r1, hy_r2⟩

private theorem exec_bfsOuterLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (fuel : ℕ) (B : PBFS) (x : Data 26),
      LayoutInv inp x →
      BFSMem inp inp.trie B x.mem →
      BFSInv inp.patterns inp.alphabetSize inp.trie B →
      inp.trie.numStates ≤ B.qHead + fuel →
      x.regs r1 = B.qHead →
      x.regs r2 = B.qTail →
      ∃ y, ExecWithin w (.loop (.lt r1 r2) bfsOuterStepCode) x y
          ((31 * inp.alphabetSize + 10) * fuel + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie (PBFS.outerLoop inp.trie inp.alphabetSize fuel B) y.mem := by
  intro fuel
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  induction fuel with
  | zero =>
    intro B x hL hM hinv hfuel hr1 hr2
    have hqt : B.qTail < inp.trie.numStates := qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj
    have hstop : ¬(Cond.lt r1 r2).Holds x := by
      simp only [Cond.holds_lt, hr1, hr2]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM⟩
  | succ fuel ih =>
    intro B x hL hM hinv hfuel hr1 hr2
    dsimp only [PBFS.outerLoop]
    by_cases hlt : B.qHead < B.qTail
    · simp only [hlt, ↓reduceIte]
      have hc : (Cond.lt r1 r2).Holds x := by
        simp only [Cond.holds_lt, hr1, hr2]; exact hlt
      set qh := B.qHead
      set r := B.queue qh
      set fr := B.fail r
      obtain ⟨_, hr_lt⟩ := hinv.q_bounds qh hlt
      have hr_maxS : r < inp.maxS := lt_of_lt_of_le hr_lt hT_maxS
      have hqt_lt : B.qTail < inp.trie.numStates :=
        qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj
      have hqh_maxS : qh < inp.maxS := lt_of_lt_of_le (lt_trans hlt hqt_lt) hT_maxS
      have hInner₀ := innerLoopInv_of_bfsInv hT hinv hlt
      have hq_read : x.mem (inp.queueBase + qh) = r := hM.queue_cell qh hqh_maxS
      have hf_read : x.mem (inp.failBase + r) = fr := hM.fail_cell r hr_maxS
      have hf_qaddr : Fits w (inp.queueBase + qh) := fits_of_le_outBase hw (by omega)
      have hf_qh1 : Fits w (qh + 1) := fits_of_le_outBase hw (by omega)
      have hf_faddr : Fits w (inp.failBase + r) := fits_of_le_outBase hw (by omega)
      have hhd : ∃ x₁, ExecWithin w (ram[
          r3 ← queueBase + r1; r3 ← *r3;
          r1 ← r1 + one;
          r4 ← failBase + r3; r4 ← *r4;
          r5 ← #0 ]) x x₁ 6 ∧
          x₁.regs r1 = qh + 1 ∧ x₁.regs r2 = B.qTail ∧
          x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = 0 ∧ x₁.mem = x.mem := by
        refine WP.exists_execWithin ?_
        wram_exec [hL.h_queueBase, hL.h_failBase, hL.h_one, hr1, hq_read, hf_read,
          hf_qaddr, hf_qh1, hf_faddr]
        exact ⟨by wram_simp, by wram_simp [hr2], by wram_simp, by wram_simp, by wram_simp,
          by wram_simp⟩
      obtain ⟨x₁, he_hd, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_mem⟩ := hhd
      have hL₁ : LayoutInv inp x₁ :=
        hL.of_preserves he_hd
      set B₁ : PBFS := { B with qHead := qh + 1 }
      have hM₁ : BFSMem inp inp.trie B₁ x₁.mem := by
        rw [hx₁_mem]
        exact ⟨hM.txt, hM.trie_cell, hM.delta_cell, hM.fail_cell, hM.depth_cell, hM.term_cell,
          hM.outHead_cell, hM.outNext_cell, hM.queue_cell⟩
      obtain ⟨x₂, he_in, hL₂, hM₂, hx₂_r1, hx₂_r2⟩ :=
        exec_bfsInnerLoop inp w hvalid hw qh r fr inp.alphabetSize 0 B₁ x₁
          (Nat.zero_add _) hL₁ hM₁ hInner₀ hx₁_r1 hx₁_r2 hx₁_r3 hx₁_r4 hx₁_r5
      obtain ⟨hinv₂, hqh₂⟩ := outerStep_spec hT hchar hterm hinv hlt
      have hqh₂' : (PBFS.innerLoop inp.trie r fr inp.alphabetSize 0 B₁).qHead = B.qHead + 1 :=
        hqh₂
      obtain ⟨y, he_tl, hLy, hMy⟩ :=
        ih (PBFS.innerLoop inp.trie r fr inp.alphabetSize 0 B₁) x₂ hL₂ hM₂ hinv₂
          (by omega) hx₂_r1 hx₂_r2
      refine ⟨y, (ExecWithin.loop_iter hc (he_hd.seq he_in) he_tl).mono ?_, hLy, hMy⟩
      rw [Nat.mul_succ]
      omega
    · simp only [hlt, ↓reduceIte]
      have hstop : ¬(Cond.lt r1 r2).Holds x := by
        simp only [Cond.holds_lt, hr1, hr2]; exact hlt
      exact ⟨x, (ExecWithin.loop_exit hstop).mono (by omega), hL, hM⟩

private theorem exec_bfsBuild (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x) (hM : TrieMem inp inp.trie x.mem) :
    ∃ y, ExecWithin w bfsBuildCode x y
        (52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7) ∧
      LayoutInv inp y ∧
      BFSMem inp inp.trie inp.bfs y.mem := by
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  have h1_maxS : 1 ≤ inp.maxS := by omega
  have h0_code : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ r1 ← #0; r2 ← #0; r5 ← #0 ]) x x₀ 3 ∧
      x₀.regs r1 = 0 ∧ x₀.regs r2 = 0 ∧ x₀.regs r5 = 0 ∧ x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hx₀_r1, hx₀_r2, hx₀_r5, hx₀_mem⟩ := h0_code
  have hL₀ : LayoutInv inp x₀ := hL.of_preserves he₀
  obtain ⟨x₁, he_rt, hL₁, hM₁, hx₁_r1, hx₁_r2⟩ :=
    exec_bfsRootLoop inp w hvalid hw inp.alphabetSize 0 PBFS.init x₀ (Nat.zero_add _)
      hL₀ (bfsMem_init (by rwa [hx₀_mem])) (rootLoopInv_init hT) hx₀_r1 hx₀_r2 hx₀_r5
  set B₀ := PBFS.rootLoop inp.trie inp.alphabetSize 0 PBFS.init
  obtain ⟨hBFS₀, hqh₀⟩ := bfsInv_rootLoop hT hchar hterm
  obtain ⟨y, he_out, hLy, hMy⟩ :=
    exec_bfsOuterLoop inp w hvalid hw inp.trie.numStates B₀ x₁ hL₁ hM₁ hBFS₀
      (by rw [hqh₀]; omega) (hx₁_r1.trans hqh₀.symm) hx₁_r2
  have hcost_le :
      3 + (21 * inp.alphabetSize + 2) + ((31 * inp.alphabetSize + 10) * inp.trie.numStates + 2) ≤
        52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7 := by
    have hmul1 : 21 * inp.alphabetSize ≤ 21 * (inp.maxS * inp.alphabetSize) :=
      Nat.mul_le_mul_left 21 (by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right inp.alphabetSize h1_maxS)
    have hmul2 : (31 * inp.alphabetSize + 10) * inp.trie.numStates ≤
        (31 * inp.alphabetSize + 10) * inp.maxS :=
      Nat.mul_le_mul_left _ hT_maxS
    simp only [Nat.add_mul] at hmul2 ⊢
    have hcomm : 31 * inp.alphabetSize * inp.maxS = 31 * (inp.maxS * inp.alphabetSize) := by
      rw [Nat.mul_assoc, Nat.mul_comm inp.alphabetSize inp.maxS]
    have hsum : 52 * inp.maxS * inp.alphabetSize =
        21 * (inp.maxS * inp.alphabetSize) + 31 * (inp.maxS * inp.alphabetSize) := by
      rw [Nat.mul_assoc]; omega
    omega
  rw [Input.bfs_eq]
  exact ⟨y, ((he₀.seq he_rt).seq he_out).mono hcost_le, hLy, hMy⟩

/-! ## Phase 4: Amortized text scanning (`scanCode`) -/

private theorem exec_set_r7 {w v : ℕ} (hv : Fits w v) (x : Data 26) :
    ∃ y, ExecWithin (B := .standard) w (ram[ r7 ← #v ]) x y 1 ∧
      y.regs r7 = v ∧ y.regs rState = x.regs rState ∧ y.regs r1 = x.regs r1 ∧
      y.regs r2 = x.regs r2 ∧ y.regs r3 = x.regs r3 ∧ y.regs r5 = x.regs r5 ∧
      y.mem = x.mem := by
  refine WP.exists_execWithin ?_; wram_exec [hv]
  exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp⟩

private theorem exec_computeFailCond (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {T : PTrie} {B : PBFS} {x : Data 26}
    (hL : LayoutInv inp x) (hM : BFSMem inp T B x.mem)
    (hu : x.regs rState < inp.maxS) (ha : x.regs r5 < inp.alphabetSize) :
    ∃ y, ExecWithin w computeFailCond x y 9 ∧
      LayoutInv inp y ∧
      y.mem = x.mem ∧
      y.regs rState = x.regs rState ∧
      y.regs r1 = x.regs r1 ∧
      y.regs r2 = x.regs r2 ∧
      y.regs r3 = x.regs r3 ∧
      y.regs r5 = x.regs r5 ∧
      y.regs r7 =
        (if 0 < x.regs rState ∧ T.trie (x.regs rState) (x.regs r5) = 0 then 1 else 0) := by
  have hlo := layout_order inp
  have hf0 : Fits w 0 := fits_zero w
  have hf1 : Fits w 1 := fits_of_le_outBase hw (by omega)
  obtain ⟨x₀, he₀, _, hs0, h10, h20, h30, h50, hm0⟩ := exec_set_r7 hf0 x
  have hL₀ : LayoutInv inp x₀ :=
    hL.of_preserves he₀
  by_cases hupos : 0 < x.regs rState
  · have hc1 : (Cond.lt zero rState).Holds x₀ := by
      simp only [Cond.holds_lt, hL₀.h_zero, hs0]; exact hupos
    have hrm := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu ha
    have hf_m : Fits w (x.regs rState * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
    have hf_a : Fits w (x.regs rState * inp.alphabetSize + x.regs r5) :=
      fits_of_le_outBase hw (by omega)
    have hf_t : Fits w (inp.trieBase + (x.regs rState * inp.alphabetSize + x.regs r5)) :=
      fits_of_le_outBase hw (by omega)
    have ht_read : x₀.mem (inp.trieBase + (x.regs rState * inp.alphabetSize + x.regs r5)) =
        T.trie (x.regs rState) (x.regs r5) := by
      rw [hm0, ← Nat.add_assoc]; exact hM.trie_cell _ hu _ ha
    have hld : ∃ x₁, ExecWithin w (ram[
        r6 ← rState * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6 ]) x₀ x₁ 4 ∧
        x₁.regs r6 = T.trie (x.regs rState) (x.regs r5) ∧
        x₁.regs rState = x.regs rState ∧ x₁.regs r1 = x.regs r1 ∧ x₁.regs r2 = x.regs r2 ∧
        x₁.regs r3 = x.regs r3 ∧ x₁.regs r5 = x.regs r5 ∧ x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hL₀.h_sigma, hL₀.h_trieBase, hs0, h50, ht_read, hf_m, hf_a, hf_t]
      exact ⟨by wram_simp, by wram_simp [hs0], by wram_simp [h10], by wram_simp [h20],
        by wram_simp [h30], by wram_simp [h50], by wram_simp [hm0]⟩
    obtain ⟨x₁, he₁, hr6₁, hs1, h11, h21, h31, h51, hm1⟩ := hld
    have hL₁ : LayoutInv inp x₁ :=
      hL₀.of_preserves he₁
    by_cases htpos : 0 < T.trie (x.regs rState) (x.regs r5)
    · have hc2 : (Cond.lt zero r6).Holds x₁ := by
        simp only [Cond.holds_lt, hL₁.h_zero, hr6₁]; exact htpos
      obtain ⟨y, hep, hr7y, hsy, h1y, h2y, h3y, h5y, hmy⟩ := exec_set_r7 hf0 x₁
      have hetot : ExecWithin w computeFailCond x y 9 :=
        (he₀.seq (ExecWithin.branch_pos hc1 (he₁.seq (ExecWithin.branch_pos hc2 hep)))).mono
          (by omega)
      have hLy := hL.of_preserves hetot
      have hnot0 : T.trie (x.regs rState) (x.regs r5) ≠ 0 := by omega
      simp only [hupos, hnot0, and_false, ↓reduceIte]
      exact ⟨y, hetot, hLy, hmy.trans hm1, hsy.trans hs1, h1y.trans h11, h2y.trans h21,
        h3y.trans h31, h5y.trans h51, hr7y⟩
    · have ht0 : T.trie (x.regs rState) (x.regs r5) = 0 := by omega
      have hc2 : ¬(Cond.lt zero r6).Holds x₁ := by
        simp only [Cond.holds_lt, hL₁.h_zero, hr6₁, ht0]; omega
      obtain ⟨y, hen, hr7y, hsy, h1y, h2y, h3y, h5y, hmy⟩ := exec_set_r7 hf1 x₁
      have hetot : ExecWithin w computeFailCond x y 9 :=
        (he₀.seq (ExecWithin.branch_pos hc1 (he₁.seq (ExecWithin.branch_neg hc2 hen)))).mono
          (by omega)
      have hLy := hL.of_preserves hetot
      simp only [hupos, ht0, and_self, ↓reduceIte]
      exact ⟨y, hetot, hLy, hmy.trans hm1, hsy.trans hs1, h1y.trans h11, h2y.trans h21,
        h3y.trans h31, h5y.trans h51, hr7y⟩
  · have hc1 : ¬(Cond.lt zero rState).Holds x₀ := by
      simp only [Cond.holds_lt, hL₀.h_zero, hs0]; exact hupos
    obtain ⟨y, hen, hr7y, hsy, h1y, h2y, h3y, h5y, hmy⟩ := exec_set_r7 hf0 x₀
    have hetot : ExecWithin w computeFailCond x y 9 :=
      (he₀.seq (ExecWithin.branch_neg hc1 hen)).mono (by omega)
    have hLy := hL.of_preserves hetot
    simp only [hupos, false_and, ↓reduceIte]
    exact ⟨y, hetot, hLy, hmy.trans hm0, hsy.trans hs0, h1y.trans h10, h2y.trans h20,
      h3y.trans h30, h5y.trans h50, hr7y⟩

private theorem exec_failLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (d : ℕ) (x : Data 26),
      LayoutInv inp x →
      BFSMem inp inp.trie inp.bfs x.mem →
      x.regs rState < inp.trie.numStates →
      inp.trie.depth (x.regs rState) = d →
      x.regs r5 < inp.alphabetSize →
      x.regs r7 =
        (if 0 < x.regs rState ∧ inp.trie.trie (x.regs rState) (x.regs r5) = 0 then 1 else 0) →
      ∃ y, ∃ u_exit < inp.trie.numStates,
        ExecWithin w
          (.loop (.lt zero r7)
            (.seq (ram[ r6 ← failBase + rState; rState ← *r6 ]) computeFailCond))
          x y (13 * (d - inp.trie.depth u_exit) + 2) ∧
        LayoutInv inp y ∧
        y.mem = x.mem ∧
        y.regs rState = u_exit ∧
        inp.trie.depth u_exit ≤ d ∧
        ¬(0 < u_exit ∧ inp.trie.trie u_exit (x.regs r5) = 0) ∧
        nextMove inp.patterns (inp.trie.strOf u_exit) (x.regs r5) =
          nextMove inp.patterns (inp.trie.strOf (x.regs rState)) (x.regs r5) ∧
        y.regs r1 = x.regs r1 ∧
        y.regs r2 = x.regs r2 ∧
        y.regs r3 = x.regs r3 ∧
        y.regs r5 = x.regs r5 := by
  intro d
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hB := inp.bfs_spec hvalid
  have hlo := layout_order inp
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro x hL hM hu_lt hd_eq ha_lt hr7
    by_cases hgo : 0 < x.regs rState ∧ inp.trie.trie (x.regs rState) (x.regs r5) = 0
    · obtain ⟨hupos, ht0⟩ := hgo
      have hc : (Cond.lt zero r7).Holds x := by
        simp only [Cond.holds_lt, hL.h_zero, hr7, hupos, ht0, and_self, ↓reduceIte]
        exact Nat.zero_lt_one
      obtain ⟨hfu_lt, hfu_str, hfu_depth⟩ := hB.fail_spec (x.regs rState) hu_lt hupos
      have hu_maxS : x.regs rState < inp.maxS := lt_of_lt_of_le hu_lt hT_maxS
      have hfu_maxS : inp.bfs.fail (x.regs rState) < inp.maxS := lt_of_lt_of_le hfu_lt hT_maxS
      have hf_read : x.mem (inp.failBase + x.regs rState) = inp.bfs.fail (x.regs rState) :=
        hM.fail_cell _ hu_maxS
      have hf_addr : Fits w (inp.failBase + x.regs rState) := fits_of_le_outBase hw (by omega)
      have hhop : ∃ x₁, ExecWithin w (ram[ r6 ← failBase + rState; rState ← *r6 ]) x x₁ 2 ∧
          x₁.regs rState = inp.bfs.fail (x.regs rState) ∧
          x₁.regs r1 = x.regs r1 ∧ x₁.regs r2 = x.regs r2 ∧ x₁.regs r3 = x.regs r3 ∧
          x₁.regs r5 = x.regs r5 ∧ x₁.mem = x.mem := by
        refine WP.exists_execWithin ?_
        wram_exec [hL.h_failBase, hf_read, hf_addr]
        exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
      obtain ⟨x₁, he_hop, hs1, h11, h21, h31, h51, hm1⟩ := hhop
      have hL₁ := hL.of_preserves he_hop
      obtain ⟨x₂, he_cond, hL₂, hm2, hs2, h12, h22, h32, h52, hr7_2⟩ :=
        exec_computeFailCond inp w hw hL₁ (by rwa [hm1]) (by rw [hs1]; exact hfu_maxS)
          (by rw [h51]; exact ha_lt)
      rw [hs1, h51] at hr7_2
      have hfu_d_lt : inp.trie.depth (inp.bfs.fail (x.regs rState)) < d := by rwa [← hd_eq]
      obtain ⟨y, u_exit, hu_ex_lt, he_tl, hLy, hmy, hsy, hd_ex, hstop_ex, hnm_ex,
        h1y, h2y, h3y, h5y⟩ :=
        ih (inp.trie.depth (inp.bfs.fail (x.regs rState))) hfu_d_lt x₂ hL₂ (by rwa [hm2, hm1])
          (by rw [hs2, hs1]; exact hfu_lt) (by rw [hs2, hs1])
          (by rw [h52, h51]; exact ha_lt) (by rw [hs2, hs1, h52, h51]; exact hr7_2)
      rw [h52, h51] at hstop_ex hnm_ex
      rw [hs2, hs1] at hnm_ex
      have hnot_node : ¬IsNode inp.patterns (inp.trie.strOf (x.regs rState) ++ [x.regs r5]) := by
        intro his
        have hpos_t := (hchar _ hu_lt _ ha_lt).1 his
        omega
      have hnm_step :
          nextMove inp.patterns (inp.trie.strOf (x.regs rState)) (x.regs r5) =
            nextMove inp.patterns (inp.trie.strOf (inp.bfs.fail (x.regs rState))) (x.regs r5) := by
        rw [hfu_str]
        exact nextMove_of_not_isNode hnot_node (hT.str_ne_nil _ hupos hu_lt)
      refine ⟨y, u_exit, hu_ex_lt,
        (ExecWithin.loop_iter hc (he_hop.seq he_cond) he_tl).mono (by omega),
        hLy, hmy.trans (hm2.trans hm1), hsy, by omega, hstop_ex, hnm_ex.trans hnm_step.symm,
        h1y.trans (h12.trans h11), h2y.trans (h22.trans h21),
        h3y.trans (h32.trans h31), h5y.trans (h52.trans h51)⟩
    · have hstop : ¬(Cond.lt zero r7).Holds x := by
        simp only [Cond.holds_lt, hL.h_zero, hr7, hgo, ↓reduceIte]; omega
      exact ⟨x, x.regs rState, hu_lt,
        (ExecWithin.loop_exit hstop).mono (by rw [hd_eq, Nat.sub_self]),
        hL, rfl, rfl, le_of_eq hd_eq, hgo, rfl, rfl, rfl, rfl, rfl⟩

private theorem exec_stepCode (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x)
    (hM : BFSMem inp inp.trie inp.bfs x.mem)
    (hu_lt : x.regs rState < inp.trie.numStates)
    (ha_lt : x.regs r5 < inp.alphabetSize) :
    ∃ y, ∃ u' < inp.trie.numStates,
      ExecWithin w stepCode x y
        (13 * (inp.trie.depth (x.regs rState) + 1 - inp.trie.depth u') + 15) ∧
      LayoutInv inp y ∧
      y.mem = x.mem ∧
      y.regs rState = u' ∧
      inp.trie.strOf u' = nextMove inp.patterns (inp.trie.strOf (x.regs rState)) (x.regs r5) ∧
      inp.trie.depth u' ≤ inp.trie.depth (x.regs rState) + 1 ∧
      y.regs r1 = x.regs r1 ∧
      y.regs r2 = x.regs r2 ∧
      y.regs r3 = x.regs r3 ∧
      y.regs r5 = x.regs r5 := by
  obtain ⟨hT, hT_maxS, hnode, _, _⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  obtain ⟨x₁, he_c0, hL₁, hm1, hs1, h11, h21, h31, h51, hr7_1⟩ :=
    exec_computeFailCond inp w hw hL hM (lt_of_lt_of_le hu_lt hT_maxS) ha_lt
  obtain ⟨x₂, u_ex, hu_ex_lt, he_fl, hL₂, hm2, hs2, hd_ex, hstop_ex, hnm_ex,
    h12, h22, h32, h52⟩ :=
    exec_failLoop inp w hvalid hw (inp.trie.depth (x.regs rState)) x₁ hL₁ (by rwa [hm1])
      (by rw [hs1]; exact hu_lt) (by rw [hs1]) (by rw [h51]; exact ha_lt)
      (by rw [hs1, h51]; exact hr7_1)
  rw [h51] at hstop_ex hnm_ex
  rw [hs1] at hnm_ex
  set a := x.regs r5
  set u' := inp.trie.trie u_ex a
  have hu'_lt : u' < inp.trie.numStates := hT.trie_lt u_ex hu_ex_lt a ha_lt
  have hu_ex_maxS : u_ex < inp.maxS := lt_of_lt_of_le hu_ex_lt hT_maxS
  have hrm := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu_ex_maxS ha_lt
  have ht_read : x₂.mem (inp.trieBase + (u_ex * inp.alphabetSize + a)) = u' := by
    rw [hm2, hm1, ← Nat.add_assoc]; exact hM.trie_cell u_ex hu_ex_maxS a ha_lt
  have hf_m : Fits w (u_ex * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_a : Fits w (u_ex * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_t : Fits w (inp.trieBase + (u_ex * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hfin : ∃ y, ExecWithin w (ram[
      r6 ← rState * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; rState ← *r6 ]) x₂ y 4 ∧
      y.regs rState = u' ∧ y.regs r1 = x₂.regs r1 ∧ y.regs r2 = x₂.regs r2 ∧
      y.regs r3 = x₂.regs r3 ∧ y.regs r5 = x₂.regs r5 ∧ y.mem = x₂.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hL₂.h_sigma, hL₂.h_trieBase, hs2, h52, h51, ht_read, hf_m, hf_a, hf_t]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨y, he_fin, hsy, h1y, h2y, h3y, h5y, hmy⟩ := hfin
  have hLy := hL₂.of_preserves he_fin
  have hu'_props :
      inp.trie.strOf u' = nextMove inp.patterns (inp.trie.strOf u_ex) a ∧
        inp.trie.depth u' ≤ inp.trie.depth u_ex + 1 := by
    rcases hT.trie_spec u_ex hu_ex_lt a ha_lt with h0 | ⟨_, hstr⟩
    · have hu_ex0 : u_ex = 0 := by omega
      subst hu_ex0
      have hnot_node : ¬IsNode inp.patterns ([] ++ [a]) := by
        intro his
        have hp := (hchar 0 hT.one_le a ha_lt).1 (by rwa [hT.str_zero])
        omega
      have hu'0 : u' = 0 := h0
      rw [hu'0, hT.str_zero, hT.depth_zero, nextMove_of_not_isNode_of_eq_nil hnot_node rfl]
      exact ⟨rfl, Nat.zero_le _⟩
    · have hnode_u' : IsNode inp.patterns (inp.trie.strOf u_ex ++ [a]) := by
        rw [← hstr]; exact hnode u' hu'_lt
      refine ⟨hstr.trans (nextMove_of_isNode hnode_u').symm, ?_⟩
      rw [hT.depth_eq u' hu'_lt, hstr, List.length_append, List.length_singleton,
        ← hT.depth_eq u_ex hu_ex_lt]
  refine ⟨y, u', hu'_lt,
    (he_c0.seq (he_fl.seq he_fin)).mono (by have := hu'_props.2; omega),
    hLy, hmy.trans (hm2.trans hm1), hsy, hu'_props.1.trans hnm_ex, by have := hu'_props.2; omega,
    h1y.trans (h12.trans h11), h2y.trans (h22.trans h21),
    h3y.trans (h32.trans h31), h5y.trans (h52.trans h51)⟩

private theorem bfsMem_of_eq_below_outBase {inp : Input} {T : PTrie} {B : PBFS}
    {mem mem' : ℕ → ℕ} (heq : ∀ a < inp.outBase, mem' a = mem a)
    (hM : BFSMem inp T B mem) : BFSMem inp T B mem' where
  txt := hM.txt.frame fun a _ hlt => by
    have hlo := layout_order inp; exact heq a (by omega)
  trie_cell := fun u hu c hc => by
    have hlo := layout_order inp
    have := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
    rw [heq _ (by omega)]; exact hM.trie_cell u hu c hc
  delta_cell := fun u hu c hc => by
    have hlo := layout_order inp
    have := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
    rw [heq _ (by omega)]; exact hM.delta_cell u hu c hc
  fail_cell := fun u hu => by
    have hlo := layout_order inp; rw [heq _ (by omega)]; exact hM.fail_cell u hu
  depth_cell := fun u hu => by
    have hlo := layout_order inp; rw [heq _ (by omega)]; exact hM.depth_cell u hu
  term_cell := fun u hu => by
    have hlo := layout_order inp; rw [heq _ (by omega)]; exact hM.term_cell u hu
  outHead_cell := fun u hu => by
    have hlo := layout_order inp; rw [heq _ (by omega)]; exact hM.outHead_cell u hu
  outNext_cell := fun u hu => by
    have hlo := layout_order inp; rw [heq _ (by omega)]; exact hM.outNext_cell u hu
  queue_cell := fun i hi => by
    have hlo := layout_order inp; rw [heq _ (by omega)]; exact hM.queue_cell i hi

private theorem length_flatMap_pair (pos : ℕ) : ∀ ls : List ℕ,
    (ls.flatMap fun len => [pos, len]).length = 2 * ls.length
  | [] => rfl
  | l :: ls => by
    change ([pos, l] ++ ls.flatMap fun len => [pos, len]).length = 2 * (ls.length + 1)
    simp only [List.cons_append, List.nil_append, List.length_cons, length_flatMap_pair pos ls]
    omega

private theorem flatMap_length_eq_encodeOccurrences (pos : ℕ) : ∀ ys : List (List ℕ),
    (ys.map List.length).flatMap (fun len => [pos, len]) =
      encodeOccurrences (ys.map fun y => (pos, y))
  | [] => rfl
  | y :: ys => by
    change [pos, y.length] ++ (ys.map List.length).flatMap (fun len => [pos, len]) =
      [pos, y.length] ++ encodeOccurrences (ys.map fun y => (pos, y))
    rw [flatMap_length_eq_encodeOccurrences pos ys]

private theorem exec_emitLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (fuel : ℕ) (acc : List ℕ) (x : Data 26),
      LayoutInv inp x →
      BFSMem inp inp.trie inp.bfs x.mem →
      x.regs r4 < inp.trie.numStates →
      (x.regs r4 = 0 ∨ inp.trie.depth (x.regs r4) < fuel) →
      x.regs r2 = inp.outBase + 1 + acc.length →
      Block.HoldsList (inp.outBase + 1) acc x.mem →
      acc.length + 2 * (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).length ≤
        2 * (occurrences inp.patterns inp.text).length →
      ∃ y, ExecWithin w (.loop (.lt zero r4) emitStepCode) x y
          (10 * (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).length + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie inp.bfs y.mem ∧
        Block.HoldsList (inp.outBase + 1)
          (acc ++ (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).flatMap
            fun len => [x.regs r3, len])
          y.mem ∧
        y.regs r2 = inp.outBase + 1 + acc.length +
          2 * (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).length ∧
        y.regs rState = x.regs rState ∧
        y.regs r1 = x.regs r1 ∧
        y.regs r3 = x.regs r3 := by
  intro fuel
  obtain ⟨_, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hB := inp.bfs_spec hvalid
  have hlo := layout_order inp
  have hwb := wordBound_eq_outBase inp
  induction fuel with
  | zero =>
    intro acc x hL hM _ hfuel hr2 hhold _
    have hq0 : x.regs r4 = 0 := hfuel.resolve_right (Nat.not_lt_zero _)
    have hstop : ¬(Cond.lt zero r4).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hq0]; omega
    simp only [followOut, List.flatMap_nil, List.append_nil, List.length_nil, Nat.mul_zero,
      Nat.add_zero]
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hhold, hr2, rfl, rfl, rfl⟩
  | succ fuel ih =>
    intro acc x hL hM hq_lt hfuel hr2 hhold hbud
    rcases Nat.eq_zero_or_pos (x.regs r4) with hq0 | hqpos
    · have hstop : ¬(Cond.lt zero r4).Holds x := by
        simp only [Cond.holds_lt, hL.h_zero, hq0]; omega
      rw [hq0, followOut_zero_right]
      simp only [List.flatMap_nil, List.append_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hhold, hr2, rfl, rfl, rfl⟩
    · have hc : (Cond.lt zero r4).Holds x := by
        simp only [Cond.holds_lt, hL.h_zero]; exact hqpos
      rw [followOut_pos _ _ hqpos] at hbud ⊢
      simp only [List.length_cons] at hbud ⊢
      have hq_maxS : x.regs r4 < inp.maxS := lt_of_lt_of_le hq_lt hT_maxS
      obtain ⟨hqn_lt, hqn_dec⟩ := hB.outNext_spec (x.regs r4) hq_lt hqpos
      have hd_read : x.mem (inp.depthBase + x.regs r4) = inp.trie.depth (x.regs r4) :=
        hM.depth_cell _ hq_maxS
      have hon_read : x.mem (inp.outNextBase + x.regs r4) = inp.bfs.outNext (x.regs r4) :=
        hM.outNext_cell _ hq_maxS
      have hf_dp : Fits w (inp.depthBase + x.regs r4) := hw.of_le (by omega)
      have hf_p1 : Fits w (inp.outBase + 1 + acc.length + 1) := hw.of_le (by omega)
      have hf_p2 : Fits w (inp.outBase + 1 + acc.length + 1 + 1) := hw.of_le (by omega)
      have hf_on : Fits w (inp.outNextBase + x.regs r4) := hw.of_le (by omega)
      have hst : ∃ x₁, ExecWithin w emitStepCode x x₁ 8 ∧
          x₁.regs r4 = inp.bfs.outNext (x.regs r4) ∧
          x₁.regs r2 = inp.outBase + 1 + acc.length + 2 ∧
          x₁.regs rState = x.regs rState ∧ x₁.regs r1 = x.regs r1 ∧ x₁.regs r3 = x.regs r3 ∧
          x₁.mem = Function.update
            (Function.update x.mem (inp.outBase + 1 + acc.length) (x.regs r3))
            (inp.outBase + 1 + acc.length + 1) (inp.trie.depth (x.regs r4)) := by
        refine WP.exists_execWithin ?_
        unfold emitStepCode
        wram_exec [hL.h_depthBase, hL.h_outNextBase, hL.h_one, hr2, hd_read, hon_read,
          hf_dp, hf_p1, hf_p2, hf_on]
        exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
          by wram_simp⟩
      obtain ⟨x₁, he_st, hx₁_r4, hx₁_r2, hx₁_rS, hx₁_r1, hx₁_r3, hx₁_mem⟩ := hst
      have hL₁ := hL.of_preserves he_st
      have hM₁ : BFSMem inp inp.trie inp.bfs x₁.mem :=
        bfsMem_of_eq_below_outBase (fun addr hlt_ob => by
          rw [hx₁_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]) hM
      have hhold₁ : Block.HoldsList (inp.outBase + 1)
          (acc ++ [x.regs r3, inp.trie.depth (x.regs r4)]) x₁.mem := by
        have hh1 := hhold.append_one (x.regs r3)
        have hh2 := hh1.append_one (inp.trie.depth (x.regs r4))
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at hh2
        rwa [show inp.outBase + 1 + (acc.length + 1) = inp.outBase + 1 + acc.length + 1 by omega,
          ← hx₁_mem] at hh2
      have hfuel₁ : x₁.regs r4 = 0 ∨ inp.trie.depth (x₁.regs r4) < fuel := by
        rw [hx₁_r4]
        have hdq : inp.trie.depth (x.regs r4) < fuel + 1 := hfuel.resolve_left (by omega)
        rcases hqn_dec with h0 | hlt_d
        · exact Or.inl h0
        · exact Or.inr (by omega)
      obtain ⟨y, he_tl, hLy, hMy, hholdy, hy_r2, hy_rS, hy_r1, hy_r3⟩ :=
        ih (acc ++ [x.regs r3, inp.trie.depth (x.regs r4)]) x₁ hL₁ hM₁
          (by rw [hx₁_r4]; exact hqn_lt) hfuel₁
          (by rw [hx₁_r2, List.length_append]; simp only [List.length_cons, List.length_nil]; omega)
          hhold₁
          (by rw [hx₁_r4, List.length_append]; simp only [List.length_cons, List.length_nil]; omega)
      rw [hx₁_r4] at he_tl hholdy hy_r2
      rw [hx₁_r3] at hholdy
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc]
        at hholdy ⊢
      refine ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hholdy, ?_,
        hy_rS.trans hx₁_rS, hy_r1.trans hx₁_r1, hy_r3.trans hx₁_r3⟩
      rw [hy_r2, List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega

private theorem exec_emitCode (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (acc : List ℕ) (x : Data 26)
    (hL : LayoutInv inp x)
    (hM : BFSMem inp inp.trie inp.bfs x.mem)
    (hu_lt : x.regs rState < inp.trie.numStates)
    (hr2 : x.regs r2 = inp.outBase + 1 + acc.length)
    (hhold : Block.HoldsList (inp.outBase + 1) acc x.mem)
    (hbud : acc.length + 2 * (output inp.patterns (inp.trie.strOf (x.regs rState))).length ≤
      2 * (occurrences inp.patterns inp.text).length) :
    ∃ y, ExecWithin w emitCode x y
        (10 * (output inp.patterns (inp.trie.strOf (x.regs rState))).length + 4) ∧
      LayoutInv inp y ∧
      BFSMem inp inp.trie inp.bfs y.mem ∧
      Block.HoldsList (inp.outBase + 1)
        (acc ++ encodeOccurrences
          ((output inp.patterns (inp.trie.strOf (x.regs rState))).map fun p => (x.regs r3, p)))
        y.mem ∧
      y.regs r2 = inp.outBase + 1 + acc.length +
        2 * (output inp.patterns (inp.trie.strOf (x.regs rState))).length ∧
      y.regs rState = x.regs rState ∧
      y.regs r1 = x.regs r1 ∧
      y.regs r3 = x.regs r3 := by
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hB := inp.bfs_spec hvalid
  have hlo := layout_order inp
  have hu_maxS : x.regs rState < inp.maxS := lt_of_lt_of_le hu_lt hT_maxS
  obtain ⟨hoh_lt, _⟩ := hB.outHead_spec (x.regs rState) hu_lt
  have hoh_depth_lt : inp.trie.depth (inp.bfs.outHead (x.regs rState)) < inp.trie.numStates :=
    lt_of_le_of_lt (depth_le_self hT _ hoh_lt) hoh_lt
  have hfol_eq := hB.follow_spec (x.regs rState) hu_lt
  have hfol_len :
      (followOut inp.trie.depth inp.bfs.outNext inp.trie.numStates
        (inp.bfs.outHead (x.regs rState))).length =
        (output inp.patterns (inp.trie.strOf (x.regs rState))).length := by
    rw [hfol_eq, List.length_map]
  have hoh_read : x.mem (inp.outHeadBase + x.regs rState) = inp.bfs.outHead (x.regs rState) :=
    hM.outHead_cell _ hu_maxS
  have hf_oh : Fits w (inp.outHeadBase + x.regs rState) := fits_of_le_outBase hw (by omega)
  have hld : ∃ x₀, ExecWithin w (ram[ r6 ← outHeadBase + rState; r4 ← *r6 ]) x x₀ 2 ∧
      x₀.regs r4 = inp.bfs.outHead (x.regs rState) ∧
      x₀.regs r2 = x.regs r2 ∧ x₀.regs rState = x.regs rState ∧
      x₀.regs r1 = x.regs r1 ∧ x₀.regs r3 = x.regs r3 ∧ x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hL.h_outHeadBase, hoh_read, hf_oh]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hx₀_r4, hx₀_r2, hx₀_rS, hx₀_r1, hx₀_r3, hx₀_mem⟩ := hld
  have hL₀ := hL.of_preserves he₀
  obtain ⟨y, he_lp, hLy, hMy, hholdy, hy_r2, hy_rS, hy_r1, hy_r3⟩ :=
    exec_emitLoop inp w hvalid hw inp.trie.numStates acc x₀ hL₀ (by rwa [hx₀_mem])
      (by rw [hx₀_r4]; exact hoh_lt) (Or.inr (by rw [hx₀_r4]; exact hoh_depth_lt))
      (hx₀_r2.trans hr2) (by rwa [hx₀_mem])
      (by rw [hx₀_r4, hfol_len]; exact hbud)
  rw [hx₀_r4, hx₀_r3, hfol_eq, flatMap_length_eq_encodeOccurrences] at hholdy
  rw [hx₀_r4, hfol_len] at he_lp hy_r2
  exact ⟨y, (he₀.seq he_lp).mono (by omega), hLy, hMy, hholdy, hy_r2,
    hy_rS.trans hx₀_rS, hy_r1.trans hx₀_r1, hy_r3.trans hx₀_r3⟩

private theorem exec_scanLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (ts pref : List ℕ) (x : Data 26),
      pref ++ ts = inp.text →
      LayoutInv inp x →
      BFSMem inp inp.trie inp.bfs x.mem →
      x.regs rState < inp.trie.numStates →
      inp.trie.strOf (x.regs rState) = longestNodeSuffix inp.patterns pref →
      x.regs r1 = pref.length →
      x.regs r2 = inp.outBase + 1 + 2 * (occurrences inp.patterns pref).length →
      Block.HoldsList (inp.outBase + 1) (encodeOccurrences (occurrences inp.patterns pref)) x.mem →
      ∃ y, ExecWithin w (.loop (.lt r1 textLen) scanStepCode) x y
          (13 * inp.trie.depth (x.regs rState) + 38 * ts.length +
            10 * ((occurrences inp.patterns inp.text).length -
              (occurrences inp.patterns pref).length) + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie inp.bfs y.mem ∧
        Block.HoldsList (inp.outBase + 1)
          (encodeOccurrences (occurrences inp.patterns inp.text)) y.mem ∧
        y.regs r2 = inp.outBase + 1 + 2 * (occurrences inp.patterns inp.text).length := by
  intro ts
  have hlo := layout_order inp
  induction ts with
  | nil =>
    intro pref x hpt hL hM _ _ hr1 hr2 hhold
    rw [List.append_nil] at hpt
    subst hpt
    have hstop : ¬(Cond.lt r1 textLen).Holds x := by
      simp only [Cond.holds_lt, hr1, hL.h_textLen]; omega
    exact ⟨x, (ExecWithin.loop_exit hstop).mono (by omega), hL, hM, hhold, hr2⟩
  | cons a ts ih =>
    intro pref x hpt hL hM hu_lt hu_str hr1 hr2 hhold
    have ht_len : pref.length + (a :: ts).length = inp.text.length := by
      rw [← List.length_append, hpt]
    simp only [List.length_cons] at ht_len
    have hc : (Cond.lt r1 textLen).Holds x := by
      simp only [Cond.holds_lt, hr1, hL.h_textLen]; omega
    have ha_mem : a ∈ inp.text := by
      rw [← hpt]; exact List.mem_append_right _ List.mem_cons_self
    have ha_lt : a < inp.alphabetSize := hvalid.2 a ha_mem
    have ht_hold : Block.HoldsList inp.textBase (pref ++ a :: ts) x.mem := hpt ▸ hM.txt
    have ht_read : x.mem (inp.textBase + pref.length) = a :=
      (Block.holdsList_cons_iff.mp (Block.holdsList_append_iff.mp ht_hold).2).1
    have hf_taddr : Fits w (inp.textBase + pref.length) := fits_of_le_outBase hw (by omega)
    have hf_pos : Fits w (pref.length + 1) := fits_of_le_outBase hw (by omega)
    have hhd : ∃ x₁, ExecWithin w
        (ram[ r6 ← textBase + r1; r5 ← *r6; r3 ← r1 + one ]) x x₁ 3 ∧
        x₁.regs rState = x.regs rState ∧ x₁.regs r1 = pref.length ∧
        x₁.regs r2 = x.regs r2 ∧ x₁.regs r3 = pref.length + 1 ∧
        x₁.regs r5 = a ∧ x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hL.h_textBase, hL.h_one, hr1, ht_read, hf_taddr, hf_pos]
      exact ⟨by wram_simp, by wram_simp [hr1], by wram_simp, by wram_simp, by wram_simp,
        by wram_simp⟩
    obtain ⟨x₁, he_hd, hs1, h11, h21, h31, h51, hm1⟩ := hhd
    have hL₁ := hL.of_preserves he_hd
    obtain ⟨x₂, u', hu'_lt, he_st, hL₂, hm2, hs2, hu'_str, hu'_depth, h12, h22, h32, _⟩ :=
      exec_stepCode inp w hvalid hw x₁ hL₁ (by rwa [hm1]) (by rw [hs1]; exact hu_lt)
        (by rw [h51]; exact ha_lt)
    rw [hs1] at he_st hu'_str hu'_depth
    rw [h51] at hu'_str
    have hu'_lns : inp.trie.strOf u' = longestNodeSuffix inp.patterns (pref ++ [a]) := by
      rw [hu'_str, hu_str, ← longestNodeSuffix_append_singleton_eq_nextMove]
    have hout_eq : output inp.patterns (inp.trie.strOf u') = output inp.patterns (pref ++ [a]) := by
      rw [hu'_lns, output_longestNodeSuffix]
    have hocc_next :
        occurrences inp.patterns (pref ++ [a]) =
          occurrences inp.patterns pref ++
            (output inp.patterns (pref ++ [a])).map fun y => (pref.length + 1, y) :=
      occurrences_append_singleton inp.patterns pref a
    have hocc_pref_le :
        (occurrences inp.patterns (pref ++ [a])).length ≤
          (occurrences inp.patterns inp.text).length := by
      have hp := occurrences_prefix_append inp.patterns (pref ++ [a]) ts
      rw [List.append_assoc, List.singleton_append, hpt] at hp
      exact hp.length_le
    have hocc_next_len :
        (occurrences inp.patterns (pref ++ [a])).length =
          (occurrences inp.patterns pref).length +
            (output inp.patterns (pref ++ [a])).length := by
      rw [hocc_next, List.length_append, List.length_map]
    obtain ⟨x₃, he_em, hL₃, hM₃, hhold₃, hr2₃, hs3, _, hr3₃⟩ :=
      exec_emitCode inp w hvalid hw (encodeOccurrences (occurrences inp.patterns pref)) x₂
        hL₂ (by rwa [hm2, hm1]) (by rw [hs2]; exact hu'_lt)
        (by rw [h22, h21, hr2, length_encodeOccurrences])
        (by rwa [hm2, hm1])
        (by rw [hs2, hout_eq, length_encodeOccurrences]; omega)
    rw [hs2, hout_eq] at he_em hhold₃ hr2₃
    rw [h32, h31, ← encodeOccurrences_append, ← hocc_next] at hhold₃
    rw [length_encodeOccurrences] at hr2₃
    have hadv : ∃ x₄, ExecWithin (B := .standard) w (ram[ r1 ← r3 ]) x₃ x₄ 1 ∧
        x₄.regs rState = u' ∧ x₄.regs r1 = (pref ++ [a]).length ∧
        x₄.regs r2 = x₃.regs r2 ∧ x₄.mem = x₃.mem := by
      refine WP.exists_execWithin ?_; wram_exec
      refine ⟨by wram_simp [hs3, hs2], ?_, by wram_simp, by wram_simp⟩
      wram_simp [hr3₃, h32, h31]
      simp only [List.length_append, List.length_singleton]
    obtain ⟨x₄, he_adv, hs4, h14, h24, hm4⟩ := hadv
    have hL₄ := hL₃.of_preserves he_adv
    obtain ⟨y, he_tl, hLy, hMy, hholdy, hy_r2⟩ :=
      ih (pref ++ [a]) x₄ (by rw [List.append_assoc, List.singleton_append, hpt])
        hL₄ (by rwa [hm4]) (by rw [hs4]; exact hu'_lt) (by rw [hs4]; exact hu'_lns)
        h14 (by rw [h24, hr2₃, hocc_next_len]; omega) (by rwa [hm4])
    rw [hs4] at he_tl
    refine ⟨y,
      (ExecWithin.loop_iter hc (he_hd.seq (he_st.seq (he_em.seq he_adv))) he_tl).mono ?_,
      hLy, hMy, hholdy, hy_r2⟩
    simp only [List.length_cons]
    omega

private theorem exec_scanCode (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x)
    (hM : BFSMem inp inp.trie inp.bfs x.mem) :
    ∃ y, ExecWithin w scanCode x y
        (38 * inp.text.length + 10 * (occurrences inp.patterns inp.text).length + 8) ∧
      LayoutInv inp y ∧
      outputList y.mem (y.regs out) =
        encodeOccurrences (occurrences inp.patterns inp.text) := by
  obtain ⟨hT, _, _, _, _⟩ := inp.trie_spec hvalid
  have hlo := layout_order inp
  have hwb := wordBound_eq_outBase inp
  have hf_ob1 : Fits w (inp.outBase + 1) := hw.of_le (by omega)
  have hinit : ∃ x₀, ExecWithin w (ram[ rState ← #0; r1 ← #0; r2 ← out + one ]) x x₀ 3 ∧
      x₀.regs rState = 0 ∧ x₀.regs r1 = 0 ∧ x₀.regs r2 = inp.outBase + 1 ∧ x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hL.h_out, hL.h_one, hf_ob1]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hs0, h10, h20, hm0⟩ := hinit
  have hL₀ := hL.of_preserves he₀
  obtain ⟨x₁, he_lp, hL₁, _, hhold₁, hr2₁⟩ :=
    exec_scanLoop inp w hvalid hw inp.text [] x₀ (List.nil_append _) hL₀ (by rwa [hm0])
      (by rw [hs0]; exact hT.one_le)
      (by rw [hs0, hT.str_zero, longestNodeSuffix_nil])
      h10
      (by rw [h20, occurrences_nil, List.length_nil, Nat.mul_zero, Nat.add_zero])
      (by rw [occurrences_nil, encodeOccurrences_nil]; exact Block.holdsList_nil _ _)
  rw [hs0, hT.depth_zero, occurrences_nil, List.length_nil, Nat.sub_zero, Nat.mul_zero,
    Nat.zero_add] at he_lp
  have hf_sub : Fits w (x₁.regs r2 - (inp.outBase + 1)) := hw.of_le (by rw [hr2₁]; omega)
  have hfin : ∃ y, ExecWithin w (ram[ r6 ← out + one; r6 ← r2 - r6; *out ← r6 ]) x₁ y 3 ∧
      y.mem =
        Function.update x₁.mem inp.outBase (2 * (occurrences inp.patterns inp.text).length) := by
    refine WP.exists_execWithin ?_
    wram_exec [hL₁.h_out, hL₁.h_one, hf_ob1, hf_sub]
    wram_simp [hr2₁]
  obtain ⟨y, he_fin, hy_mem⟩ := hfin
  have hLy := hL₁.of_preserves he_fin
  refine ⟨y, (he₀.seq (he_lp.seq he_fin)).mono (by omega), hLy, ?_⟩
  rw [hLy.h_out, hy_mem, outputList_eq_iff]
  exact ⟨by rw [Function.update_self, length_encodeOccurrences],
    hhold₁.frame fun a ha _ => Function.update_of_ne (by omega) _ _⟩

/-! ## Top-level Word-RAM running-time theorems -/

/-- `searchCode` computes `encodeOccurrences (occurrences inp.patterns inp.text)` at `Reg.out`
within `searchTime inp - 1` instructions at any word width `w` with `Fits w inp.wordBound`. -/
theorem searchCode_exec (inp : Input) (w : ℕ)
    (hvalid : inp.Valid) (hw : Fits w inp.wordBound) :
    ∃ y, ExecWithin w searchCode (.init inp.encode) y (searchTime inp - 1) ∧
      outputList y.mem (y.regs out) =
        encodeOccurrences (occurrences inp.patterns inp.text) ∧
      Fits w (y.regs out + (encodeOccurrences (occurrences inp.patterns inp.text)).length) := by
  obtain ⟨x₁, he₁, hL₁, hM₁⟩ := exec_setupAndClear inp w hw
  obtain ⟨x₂, he₂, hL₂, hM₂⟩ := exec_buildTrie inp w hvalid hw x₁ hL₁ hM₁
  obtain ⟨x₃, he₃, hL₃, hM₃⟩ := exec_bfsBuild inp w hvalid hw x₂ hL₂ hM₂
  obtain ⟨y, he₄, hLy, hout⟩ := exec_scanCode inp w hvalid hw x₃ hL₃ hM₃
  have hcost :
      (8 * inp.maxS * inp.alphabetSize + 24 * inp.maxS + 31) +
        ((19 * inp.maxS + 11 * inp.patterns.length + 5) +
          ((52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7) +
            (38 * inp.text.length + 10 * (occurrences inp.patterns inp.text).length + 8))) ≤
      searchTime inp - 1 := by
    have hmaxS := (layout_order inp).1
    dsimp only [searchTime]
    rw [hmaxS]
    simp only [Nat.mul_assoc]
    omega
  refine ⟨y, (he₁.seq (he₂.seq (he₃.seq he₄))).mono hcost, hout, ?_⟩
  rw [hLy.h_out, length_encodeOccurrences]
  exact hw.of_le (by rw [wordBound_eq_outBase]; omega)

/-- `searchProgram` computes `encodeOccurrences (occurrences inp.patterns inp.text)` within
`searchTime inp = O((‖P‖ + 1) · σ + |P| + |t| + occ)` instructions at any fitting width with
`inp.Valid` and `Fits w inp.wordBound`. -/
theorem searchProgram_computesListInTime :
    searchProgram.ComputesListInTime
      (fun _ (inp : Input) => inp.encode)
      (fun inp _ => searchTime inp)
      (fun inp w => inp.Valid ∧ Fits w inp.wordBound)
      (fun inp => encodeOccurrences (occurrences inp.patterns inp.text)) :=
  searchCode.computesListInTime_program out fun inp w ⟨hvalid, hw⟩ _ =>
    searchCode_exec inp w hvalid hw

/-- Direct `ExecutesList` corollary for `searchProgram` discharging `InputFits` automatically from
`inp.Valid` and `Fits w inp.wordBound`. -/
theorem searchProgram_executesList (inp : Input) (w : ℕ)
    (hvalid : inp.Valid) (hw : Fits w inp.wordBound) :
    ∃ t, ExecutesList w searchProgram (.init inp.encode)
        (encodeOccurrences (occurrences inp.patterns inp.text)) t ∧
      t ≤ searchTime inp :=
  searchProgram_computesListInTime inp w ⟨hvalid, hw⟩ (hvalid.inputFits hw)

end Cslib.Algorithms.WordRAM.AhoCorasick
