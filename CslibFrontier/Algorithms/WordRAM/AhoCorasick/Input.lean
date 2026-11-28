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

/-!
# Aho–Corasick Word-RAM Input/Output Encodings and Bounds

Public problem instance, word-array encoding, occurrence encoding/decoding, register-output slot,
and width/time thresholds for the integer-alphabet Aho–Corasick Word-RAM realization.

This module has no dependency on `Structured`, `SymbolicExec`, or the pure BFS/trie models, so
clients inspecting `Input`, `encodeOccurrences`, `decodeOccurrences`, `wordBound`, or `searchTime`
avoid elaborating the machine-level proof stack.

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
* `Cslib.Algorithms.WordRAM.AhoCorasick.Reg.out`: output header register (`14 : Fin 26`).

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.decodeOccurrences_encodeOccurrences`: `decodeOccurrences t`
  recovers `occurrences P t` from `encodeOccurrences (occurrences P t)`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.wordBound_le`: polynomial upper bound on `inp.wordBound`
  independent of `occ`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.Valid.inputFits`: `InputFits w inp.encode` from
  `inp.Valid` and `Fits w inp.wordBound`.
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
    have hy : (t.take pos).drop (pos - y.length) = y := by
      simpa [List.length_take_of_le hpos] using (List.suffix_iff_eq_drop.mp hsuf).symm
    change (pos, (t.take pos).drop (pos - y.length)) ::
        decodeOccurrences t (encodeOccurrences rest) = (pos, y) :: rest
    rw [hy, decodeOccurrences_aux t rest fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `decodeOccurrences t` losslessly recovers `occurrences P t` from its flat word encoding. -/
theorem decodeOccurrences_encodeOccurrences (P : List (List ℕ)) (t : List ℕ) :
    decodeOccurrences t (encodeOccurrences (occurrences P t)) = occurrences P t :=
  decodeOccurrences_aux t _ fun _ hmem =>
    let ⟨hpos, _, _, hsuf⟩ := mem_occurrences_iff.mp hmem
    ⟨hpos, hsuf⟩

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
    · exact hw.of_le (by simp only [totalPatternLen_cons] at hM; omega)
    · have := hP p List.mem_cons_self x hxp
      exact hw.of_le (by omega)
    · exact ih (fun q hq => hP q (List.mem_cons_of_mem p hq))
        (by simp only [totalPatternLen_cons] at hM; omega) x hxps

/-- Under `inp.Valid` and `Fits w inp.wordBound`, every word of `inp.encode` and its length fit in
width `w`. -/
theorem Input.Valid.inputFits {inp : Input} {w : ℕ} (hv : inp.Valid)
    (hw : Fits w inp.wordBound) : InputFits w inp.encode := by
  dsimp only [Input.wordBound] at hw
  have hsig_le : inp.alphabetSize ≤ 2 * (totalPatternLen inp.patterns + 1) * inp.alphabetSize := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_right inp.alphabetSize
      (show 1 ≤ 2 * (totalPatternLen inp.patterns + 1) by omega)
  refine ⟨hw.of_le (by rw [length_encode]; omega), fun x hx => ?_⟩
  simp only [Input.encode, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | rfl | rfl | rfl | hx_pat | hx_txt
  · exact hw.of_le (by omega)
  · exact hw.of_le (by omega)
  · exact hw.of_le (by omega)
  · exact hw.of_le (by omega)
  · exact mem_encodePatterns_fits hv.1 hw (by omega) (by omega) x hx_pat
  · have := hv.2 x hx_txt
    exact hw.of_le (by omega)

namespace Reg

/-- Output block header register returned by `searchProgram`. -/
abbrev out : Fin 26 := 14

end Reg

end Cslib.Algorithms.WordRAM.AhoCorasick
