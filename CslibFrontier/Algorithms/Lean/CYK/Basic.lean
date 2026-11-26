/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Languages.ChomskyNormalForm

/-!
# The Cocke–Younger–Kasami algorithm

Membership in the language of a grammar in Chomsky normal form, decided by dynamic programming
over subwords [Kasami][Kasami1965] [Younger][Younger1967] [Hopcroft, Motwani and Ullman,
Section 7.4.4][Hopcroft2006]. The table holds, for each subword `w[i, i + l)` of the input, the
list of nonterminals deriving it. Cells of length one are read off the rules `A → a`. A cell of
length `l ≥ 2` is filled by trying every split point `k` and every rule `A → B C` with `B` in the
cell of the first `k + 1` letters and `C` in the cell of the remaining `l - k - 1`. The input is
accepted when the start symbol is in the cell of the whole word, or, for the empty word, when the
grammar has the rule `S → ε`.

This is the algorithm in the proof of [Sipser, Theorem 7.16][Sipser2013] that every context-free
language is in P, for a grammar that is already in Chomsky normal form. Conversion of an arbitrary
context-free grammar to Chomsky normal form is not formalized here; a Word-RAM implementation and
`O((|R| + 1)(|w| + 1)³)` running-time bound are proved in `CslibFrontier.Algorithms.WordRAM.CYK`.

## Main definitions

* `Cslib.Algorithms.Lean.CYK.table`: the table, filled level by level (by subword length).
* `Cslib.Algorithms.Lean.CYK.cyk`: the membership test.

## Main results

* `Cslib.Algorithms.Lean.CYK.mem_table_iff`: a nonterminal is in a table cell iff it derives the
  subword of the cell, in the sense of Mathlib's `ContextFreeGrammar.Derives` for
  `ChomskyNormalFormGrammar.toCFG`.
* `Cslib.Algorithms.Lean.CYK.cyk_eq_true_iff`: CYK accepts exactly the words of the language.
* `Cslib.Algorithms.Lean.CYK.decidableMemLanguage`: membership in the language of a grammar in
  Chomsky normal form is decidable.
* `Cslib.Algorithms.Lean.CYK.nodup_table_and_length_le`: every cell is a list without repetitions
  of at most `|R|` nonterminals.

## References

* [T. Kasami, *An efficient recognition and syntax-analysis algorithm for context-free
  languages*][Kasami1965]
* [D. H. Younger, *Recognition and parsing of context-free languages in time n³*][Younger1967]
* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages,
  and Computation*][Hopcroft2006]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Algorithms.Lean.CYK

open ChomskyNormalFormGrammar ChomskyNormalFormRule

variable {T : Type*} [DecidableEq T] (G : ChomskyNormalFormGrammar T) [DecidableEq G.NT]

/-- The left-hand side `A` of a rule `A → a` with `x = some a`. -/
@[expose] def leafMatch (x : Option T) : ChomskyNormalFormRule T G.NT → Option G.NT
  | leaf A a => if x = some a then some A else none
  | node .. => none

/-- The left-hand side `A` of a rule `A → B C` with `B ∈ L` and `C ∈ R`. -/
@[expose] def nodeMatch (L R : List G.NT) : ChomskyNormalFormRule T G.NT → Option G.NT
  | leaf .. => none
  | node A B C => if B ∈ L ∧ C ∈ R then some A else none

/-- Scan the rules once, adding the nonterminal of every match to `acc` unless it is already there
(`List.insert`). -/
@[expose] def scan (f : ChomskyNormalFormRule T G.NT → Option G.NT) (acc : List G.NT) :
    List G.NT :=
  G.rules.foldl (fun acc r => (f r).elim acc (acc.insert ·)) acc

/-- A CYK table: `tbl i l` lists nonterminals for the subword of length `l` starting at `i`. -/
abbrev Table (G : ChomskyNormalFormGrammar T) := ℕ → ℕ → List G.NT

variable (w : List T)

/-- The cell of the letter at position `i`: the nonterminals `A` with a rule `A → w[i]`. -/
@[expose] def leafCell (i : ℕ) : List G.NT := scan G (leafMatch G w[i]?) []

/-- The cell of the subword of length `l ≥ 2` at `i`, from the cells of shorter subwords: the
nonterminals `A` with a rule `A → B C`, `B` in the cell of the first `k + 1` letters and `C` in
the cell of the remaining `l - k - 1`, for some split `k < l - 1`. -/
@[expose] def nodeCell (tbl : Table G) (i l : ℕ) : List G.NT :=
  (List.range (l - 1)).foldl (fun acc k =>
    scan G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) []

/-- The cell of the subword of length `l` at `i`. -/
@[expose] def cell (tbl : Table G) (i l : ℕ) : List G.NT :=
  if l = 1 then leafCell G w i else nodeCell G tbl i l

/-- Overwrite the cell `(i, l)` of a table. -/
@[expose] def setCell (tbl : Table G) (i l : ℕ) (c : List G.NT) : Table G :=
  fun i' l' => if i' = i ∧ l' = l then c else tbl i' l'

/-- Fill the cells of length `l` at every start position `i` with `i + l ≤ |w|`. -/
@[expose] def level (tbl : Table G) (l : ℕ) : Table G :=
  (List.range (w.length + 1 - l)).foldl (fun t i => setCell G t i l (cell G w tbl i l)) tbl

/-- The table with the cells of lengths `1, …, L` filled, in order of length. -/
@[expose] def table : ℕ → Table G
  | 0 => fun _ _ => []
  | L + 1 => level G w (table L) (L + 1)

/-- The CYK membership test: accept the empty word when the grammar has the rule `S → ε`, and a
nonempty word when the start symbol is in the cell of the whole word. -/
@[expose] def cyk : Bool :=
  if w = [] then G.nilRule else G.initial ∈ table G w w.length 0 w.length

/-! ### Correctness -/

variable {G w}

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem mem_foldl_elim {α β : Type*} [DecidableEq β] (f : α → Option β) (l : List α)
    (acc : List β) (b : β) : b ∈ l.foldl (fun acc r => (f r).elim acc (acc.insert ·)) acc ↔
      b ∈ acc ∨ ∃ r ∈ l, f r = some b := by
  induction l generalizing acc with
  | nil => simp
  | cons r l ih =>
    rw [List.foldl_cons, ih]
    cases h : f r with
    | none => simp [h]
    | some c =>
      simp only [Option.elim_some, List.mem_insert_iff, List.mem_cons, exists_eq_or_imp, h,
        Option.some.injEq, eq_comm (a := c)]
      tauto

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem nodup_foldl_elim {α β : Type*} [DecidableEq β] (f : α → Option β) (l : List α)
    {acc : List β} (h : acc.Nodup) :
    (l.foldl (fun acc r => (f r).elim acc (acc.insert ·)) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons r l ih =>
    rw [List.foldl_cons]
    cases f r with
    | none => exact ih h
    | some _ => exact ih h.insert

omit [DecidableEq T] in
/-- A scan adds exactly the matches of the rules. -/
theorem mem_scan {f : ChomskyNormalFormRule T G.NT → Option G.NT} {acc : List G.NT} {A : G.NT} :
    A ∈ scan G f acc ↔ A ∈ acc ∨ ∃ r ∈ G.rules, f r = some A :=
  mem_foldl_elim f G.rules acc A

omit [DecidableEq T] in
/-- A scan adds no repetitions. -/
theorem nodup_scan {f : ChomskyNormalFormRule T G.NT → Option G.NT} {acc : List G.NT}
    (h : acc.Nodup) : (scan G f acc).Nodup :=
  nodup_foldl_elim f G.rules h

theorem mem_leafCell {i : ℕ} {A : G.NT} :
    A ∈ leafCell G w i ↔ ∃ a, w[i]? = some a ∧ leaf A a ∈ G.rules := by
  simp only [leafCell, mem_scan, List.not_mem_nil, false_or]
  constructor
  · rintro ⟨⟨B, a⟩ | ⟨_, _, _⟩, hr, h⟩
    · obtain ⟨ha, rfl⟩ := by
        simpa only [leafMatch, Option.ite_none_right_eq_some, Option.some.injEq] using h
      exact ⟨a, ha, hr⟩
    · cases h
  · rintro ⟨a, h, hr⟩
    exact ⟨leaf A a, hr, by simp [leafMatch, h]⟩

omit [DecidableEq T] in
theorem mem_nodeCell {tbl : Table G} {i l : ℕ} {A : G.NT} :
    A ∈ nodeCell G tbl i l ↔ ∃ k < l - 1, ∃ B C, node A B C ∈ G.rules ∧
      B ∈ tbl i (k + 1) ∧ C ∈ tbl (i + k + 1) (l - k - 1) := by
  have hnm (L R : List G.NT) :
      (∃ r ∈ G.rules, nodeMatch G L R r = some A) ↔
        ∃ B C, node A B C ∈ G.rules ∧ B ∈ L ∧ C ∈ R := by
    constructor
    · rintro ⟨⟨_, _⟩ | ⟨A', B, C⟩, hr, h⟩
      · cases h
      · obtain ⟨⟨hB, hC⟩, heq⟩ := Option.ite_none_right_eq_some.1 h
        exact ⟨B, C, Option.some.inj heq ▸ hr, hB, hC⟩
    · exact fun ⟨B, C, hr, hB, hC⟩ => ⟨node A B C, hr, ite_eq_left ⟨hB, hC⟩⟩
  have key : ∀ (ks : List ℕ) (acc : List G.NT), A ∈ ks.foldl (fun acc k =>
      scan G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) acc ↔
      A ∈ acc ∨ ∃ k ∈ ks, ∃ B C, node A B C ∈ G.rules ∧
        B ∈ tbl i (k + 1) ∧ C ∈ tbl (i + k + 1) (l - k - 1) := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih =>
      intro acc
      simp only [List.foldl_cons, ih, mem_scan, hnm, List.mem_cons, exists_eq_or_imp, or_assoc]
  simpa [nodeCell] using key (List.range (l - 1)) []

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem foldl_setCell (c : ℕ → List G.NT) (l : ℕ) (is : List ℕ) (tbl : Table G)
    (i' l' : ℕ) : is.foldl (fun t i => setCell G t i l (c i)) tbl i' l' =
      if l' = l ∧ i' ∈ is then c i' else tbl i' l' := by
  induction is generalizing tbl with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons, ih]
    by_cases h₁ : l' = l <;> by_cases h₂ : i' ∈ is <;> by_cases h₃ : i' = i <;>
      simp_all [setCell]

/-- Filling level `l` sets the cells of length `l` that fit in the word, and nothing else. -/
theorem level_apply (tbl : Table G) (l i' l' : ℕ) :
    level G w tbl l i' l' =
      if l' = l ∧ i' + l ≤ w.length then cell G w tbl i' l else tbl i' l' := by
  rw [level, foldl_setCell]
  exact if_congr (and_congr_right fun _ => by simp; omega) rfl rfl

/-- Once level `l` has been filled (`l ≤ L`), cells of length `l` are unchanged by later levels. -/
theorem table_eq_of_le {l L : ℕ} (hl : l ≤ L) (i : ℕ) :
    table G w L i l = table G w l i l := by
  induction hl with
  | refl => rfl
  | step hm ih => rw [table, level_apply, ite_eq_right (fun h => (Nat.lt_succ_of_le hm).ne h.1), ih]

/-- The cell of length `L + 1` at `i` lists exactly the nonterminals deriving the subword, given
that the table is correct for all shorter subwords. -/
private theorem mem_cell_iff {tbl : Table G} {L i : ℕ} (hi : i + (L + 1) ≤ w.length)
    (htbl : ∀ i l, 0 < l → l ≤ L → i + l ≤ w.length → ∀ A : G.NT,
      A ∈ tbl i l ↔ G.toCFG.Derives [.nonterminal A] (((w.drop i).take l).map .terminal))
    (A : G.NT) :
    A ∈ cell G w tbl i (L + 1) ↔
      G.toCFG.Derives [.nonterminal A] (((w.drop i).take (L + 1)).map .terminal) := by
  set s := (w.drop i).take (L + 1) with hs
  have hlen : s.length = L + 1 := by simp only [hs, List.length_take, List.length_drop]; omega
  have hne : s ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [derives_iff_of_ne_nil hne]
  rcases L with _ | L
  · -- a single letter
    have hsi : s = [w[i]] := by rw [hs, List.drop_eq_getElem_cons (by omega)]; rfl
    rw [cell, ite_eq_left rfl, mem_leafCell, List.getElem?_eq_getElem (by omega)]
    constructor
    · rintro ⟨a, ha, hr⟩
      exact Or.inl ⟨a, by rw [hsi, Option.some.inj ha], hr⟩
    · rintro (⟨a, ha, hr⟩ | ⟨_, _, u, v, -, hu, hv, huv, -⟩)
      · rw [hsi, List.singleton_inj] at ha
        exact ⟨a, by rw [ha], hr⟩
      · have := congrArg List.length huv
        rw [hlen, List.length_append] at this
        have := List.length_pos_of_ne_nil hu
        have := List.length_pos_of_ne_nil hv
        omega
  · -- at least two letters
    rw [cell, ite_eq_right (by omega), mem_nodeCell]
    have hleft : ¬ ∃ a, s = [a] ∧ leaf A a ∈ G.rules := fun ⟨a, ha, _⟩ => by
      rw [ha, List.length_singleton] at hlen; omega
    rw [or_iff_right hleft]
    have hcell : ∀ k < L + 1, ∀ B C,
        (B ∈ tbl i (k + 1) ∧ C ∈ tbl (i + k + 1) (L + 1 + 1 - k - 1)) ↔
        (G.toCFG.Derives [.nonterminal B] ((s.take (k + 1)).map .terminal) ∧
          G.toCFG.Derives [.nonterminal C] ((s.drop (k + 1)).map .terminal)) := fun k hk B C => by
      have h1 : s.take (k + 1) = (w.drop i).take (k + 1) := by
        rw [hs, List.take_take, Nat.min_eq_left (by omega)]
      have h2 : s.drop (k + 1) = (w.drop (i + k + 1)).take (L + 1 + 1 - k - 1) := by
        rw [hs, List.drop_take, List.drop_drop, Nat.sub_sub, ← Nat.add_assoc]
      rw [h1, h2]
      exact and_congr (htbl i (k + 1) (Nat.succ_pos k) hk (by omega) B)
        (htbl (i + k + 1) (L + 1 + 1 - k - 1) (by omega) (by omega) (by omega) C)
    constructor
    · rintro ⟨k, hk, B, C, hr, hB, hC⟩
      have hk' : k < L + 1 := by omega
      obtain ⟨hB', hC'⟩ := (hcell k hk' B C).mp ⟨hB, hC⟩
      exact ⟨B, C, s.take (k + 1), s.drop (k + 1), hr,
        List.ne_nil_of_length_pos (by rw [List.length_take]; omega),
        List.ne_nil_of_length_pos (by rw [List.length_drop]; omega),
        (List.take_append_drop (k + 1) s).symm, hB', hC'⟩
    · rintro ⟨B, C, u, v, hr, hu, hv, huv, hB, hC⟩
      have hu' := List.length_pos_of_ne_nil hu
      have hv' := List.length_pos_of_ne_nil hv
      have hlen' : u.length + v.length = L + 2 := by rw [← List.length_append, ← huv, hlen]
      have hk : u.length - 1 < L + 1 := by omega
      have htk : s.take (u.length - 1 + 1) = u := by
        rw [Nat.sub_add_cancel hu', huv, List.take_left]
      have hdp : s.drop (u.length - 1 + 1) = v := by
        rw [Nat.sub_add_cancel hu', huv, List.drop_left]
      obtain ⟨hB', hC'⟩ := (hcell (u.length - 1) hk B C).mpr ⟨htk.symm ▸ hB, hdp.symm ▸ hC⟩
      exact ⟨u.length - 1, hk, B, C, hr, hB', hC'⟩

/-- **Correctness of the CYK table**: after filling the levels `1, …, L`, the cell of a subword of
length `l ≤ L` lists exactly the nonterminals deriving it. -/
theorem mem_table_iff {L i l : ℕ} (hl : 0 < l) (hlL : l ≤ L) (hi : i + l ≤ w.length)
    (A : G.NT) :
    A ∈ table G w L i l ↔
      G.toCFG.Derives [.nonterminal A] (((w.drop i).take l).map .terminal) := by
  induction L generalizing i l A with
  | zero => omega
  | succ L ih =>
    rw [table, level_apply]
    split_ifs with h
    · obtain ⟨rfl, -⟩ := h
      exact mem_cell_iff hi (fun i l hl hlL hi A => ih hl hlL hi A) A
    · exact ih hl (by omega) hi A

/-- **Correctness of CYK** [Hopcroft, Motwani and Ullman, Section 7.4.4][Hopcroft2006]: the test
accepts exactly the words of the language of the grammar. -/
theorem cyk_eq_true_iff : cyk G w = true ↔ w ∈ G.toCFG.language := by
  rw [cyk]
  split_ifs with hw
  · exact hw ▸ mem_language_nil_iff.symm
  · simp [mem_table_iff (List.length_pos_of_ne_nil hw) le_rfl (Nat.zero_add _).le]

/-- Membership in the language of a grammar in Chomsky normal form is decidable, by CYK. -/
instance decidableMemLanguage : DecidablePred (· ∈ G.toCFG.language) :=
  fun w => decidable_of_iff _ (cyk_eq_true_iff (G := G) (w := w))

/-! ### Size of the cells -/

/-- Every nonterminal in a cell is the left-hand side of a rule. -/
theorem exists_rule_of_mem_cell {tbl : Table G} {i l : ℕ} {A : G.NT}
    (h : A ∈ cell G w tbl i l) : ∃ r ∈ G.rules, r.input = A := by
  unfold cell at h
  split_ifs at h
  · obtain ⟨a, -, hr⟩ := mem_leafCell.mp h
    exact ⟨_, hr, rfl⟩
  · obtain ⟨k, -, B, C, hr, -⟩ := mem_nodeCell.mp h
    exact ⟨_, hr, rfl⟩

theorem nodup_cell (tbl : Table G) (i l : ℕ) : (cell G w tbl i l).Nodup := by
  unfold cell nodeCell leafCell
  split_ifs
  · exact nodup_scan List.nodup_nil
  · suffices ∀ (ks : List ℕ) (acc : List G.NT), acc.Nodup → (ks.foldl (fun acc k =>
        scan G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) acc).Nodup from
      this _ _ List.nodup_nil
    intro ks
    induction ks with
    | nil => exact fun _ h => h
    | cons k ks ih => exact fun acc h => ih _ (nodup_scan h)

/-- A cell has at most one entry per rule. -/
theorem length_cell_le (tbl : Table G) (i l : ℕ) : (cell G w tbl i l).length ≤ G.rules.length := by
  have hsub : cell G w tbl i l ⊆ G.rules.map ChomskyNormalFormRule.input := fun A hA => by
    obtain ⟨r, hr, rfl⟩ := exists_rule_of_mem_cell hA
    exact List.mem_map_of_mem hr
  simpa using ((nodup_cell tbl i l).subperm hsub).length_le

/-- Every cell of the table is a list without repetitions of at most `|R|` nonterminals, for a
grammar with `|R|` rules. -/
theorem nodup_table_and_length_le (L i l : ℕ) :
    (table G w L i l).Nodup ∧ (table G w L i l).length ≤ G.rules.length := by
  induction L generalizing i l with
  | zero => simp [table]
  | succ L ih =>
    rw [table, level_apply]
    split_ifs
    · exact ⟨nodup_cell _ _ _, length_cell_le _ _ _⟩
    · exact ih i l

end Cslib.Algorithms.Lean.CYK
