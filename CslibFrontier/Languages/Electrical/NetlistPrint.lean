/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Electrical.NetlistCertificate

/-!
# Printing netlists, with a round-trip theorem

A printer `Cslib.Electrical.Text.print` for the netlists read by
`Cslib.Electrical.Text.parse`, and the theorem that the reader reads back what the printer
writes: `parse (print P) = .ok P` for every `P` in the printable normal form
(`Cslib.Electrical.Text.parse_print`). With it, the guarantee of the end-to-end checker holds
for a netlist built in Lean from the acceptance of a certificate against its printed text, so
that for such netlists the reader drops out of the trusted base: what remains is this printer,
which writes one line per branch and per probe in the grammar of
`CslibFrontier.Languages.Electrical.NetlistText`.

**The text.** `print P` writes the title line `.title netlist`, then a line per branch,
`name n+ n- [nc+ nc-] [dc] value [ac]` (with `dc` for a source), a line `.probe v p q` or
`.probe i name` per probe, and `.end`. Nodes are written with their names in `P.nodeNames`
(`0` for the ground). A value `q` whose denominator divides a power of ten is written as the
integer `q 10ᵏ` followed by `e-k` (or as an integer).

**The normal form** (`Cslib.Electrical.Text.ParsedNetlist.isPrintable`) is the form the reader
produces: the node names are well formed, not `0` and distinct up to case, and the nodes are
numbered in order of first appearance; the branch names are well formed, distinct up to case,
one per branch, and start with the letter of their element; the input ports are numbered in the
order of their sources; every value has a decimal expansion; and every probe refers to an
existing node or branch.

## Main definitions

* `Cslib.Electrical.Text.print`, `Cslib.Electrical.Text.printValue`.
* `Cslib.Electrical.Text.ParsedNetlist.isPrintable`.

## Main statements

* `Cslib.Electrical.Text.value?_printValue`: values are read back.
* `Cslib.Electrical.Text.parse_print`: the round trip.
* `Cslib.Electrical.Text.guarantee_of_checkText_print`: the end-to-end guarantee for a netlist
  from the acceptance of a certificate against its printed text.
-/

@[expose] public section

namespace Cslib.Electrical.Text

/-! ### The printer -/

/-- The least `k ≤ d` with `d ∣ 10 ^ k`, if any. -/
def decExp (d : ℕ) : Option ℕ := (List.range (d + 1)).find? fun k => 10 ^ k % d == 0

/-- **The text of a value** whose denominator divides a power of ten: the integer `q 10ᵏ`
followed by `e-k`, or just the integer for an integer `q`. -/
def printValue (q : ℚ) : List Char :=
  if q.den = 1 then Int.toDecimal q.num else
    match decExp q.den with
    | some k => Int.toDecimal (q.num * ((10 ^ k / q.den : ℕ) : ℤ)) ++ ['e', '-'] ++
        Nat.toDecimal k
    | none => []

/-- The words of a card. -/
def cardWords : Card → List (List Char)
  | .element name nodes v ac => name :: nodes ++
      (if isSource (name.headD 'x').toLower then [['d', 'c']] else []) ++
      printValue v :: if ac then [['a', 'c']] else []
  | .probeV p q => [".probe".toList, ['v'], p, q]
  | .probeI n => [".probe".toList, ['i'], n]

/-- The name of node `k`. -/
def nodeName (names : List (List Char)) (k : ℕ) : List Char :=
  if k = 0 then ['0'] else names.getD (k - 1) []

/-- The value of an element. -/
def elemValue : Element → ℚ
  | .resistor v | .capacitor v | .inductor v | .voltageSource v _ | .currentSource v _
  | .vccs v _ _ | .vcvs v _ _ => v

/-- The input port of an element. -/
def elemInput : Element → Option ℕ
  | .voltageSource _ input | .currentSource _ input => input
  | _ => none

/-- The nodes of a branch: its terminals, then the control nodes of a controlled source. -/
def branchNodes (br : Branch) : List ℕ :=
  br.pos :: br.neg :: match br.elem with
    | .vccs _ cp cn | .vcvs _ cp cn => [cp, cn]
    | _ => []

/-- The element card of a branch with name `name`. -/
def branchCard (names : List (List Char)) (name : List Char) (br : Branch) : Card :=
  .element name ((branchNodes br).map (nodeName names)) (elemValue br.elem)
    (elemInput br.elem).isSome

/-- The card of a probe. -/
def probeCardOf (P : ParsedNetlist) : Probe → Card
  | .voltage p q => .probeV (nodeName P.nodeNames p) (nodeName P.nodeNames q)
  | .current b => .probeI (P.branchNames.getD b [])

/-- The cards of a netlist: its branches, then its probes. -/
def toCards (P : ParsedNetlist) : List Card :=
  List.zipWith (branchCard P.nodeNames) P.branchNames P.netlist.branches ++
    P.probes.map (probeCardOf P)

/-- A line of words. -/
def line (ws : List (List Char)) : List Char := [' '].intercalate ws ++ ['\n']

/-- The text of a list of cards: a title line, a line per card, and `.end`. -/
def printCards (cs : List Card) : List Char :=
  line [".title".toList, "netlist".toList] ++ cs.flatMap (fun c => line (cardWords c)) ++
    line [".end".toList]

/-- **The printer.** -/
def print (P : ParsedNetlist) : String := String.ofList (printCards (toCards P))

/-! ### The normal form -/

/-- The letter of an element. -/
def elemLetter : Element → Char
  | .resistor _ => 'r' | .capacitor _ => 'c' | .inductor _ => 'l'
  | .voltageSource _ _ => 'v' | .currentSource _ _ => 'i' | .vccs _ _ _ => 'g'
  | .vcvs _ _ _ => 'e'

/-- Whether a value has a decimal expansion that `printValue` writes. -/
def isDecimal (q : ℚ) : Bool := q.den == 1 || (decExp q.den).isSome

/-- The nonzero node numbers of the branches, in order. -/
def nodeRefIdx (c : Netlist) : List ℕ :=
  c.branches.flatMap fun br => (branchNodes br).filter (· != 0)

/-- **The printable normal form**, which the reader produces; see the module documentation. -/
def ParsedNetlist.isPrintable (P : ParsedNetlist) : Bool :=
  P.netlist.nodes == P.nodeNames.length &&
    P.nodeNames.all (fun w => isNodeName w && w != ['0']) && (P.nodeNames.map lower).Nodup &&
    firstOccurrences [] (nodeRefIdx P.netlist) == List.range' 1 P.nodeNames.length &&
    P.branchNames.length == P.netlist.branches.length &&
    (List.zip P.branchNames P.netlist.branches).all (fun nb =>
      nb.1.all isNameChar && (nb.1.head?.map Char.toLower) == some (elemLetter nb.2.elem)) &&
    (P.branchNames.map lower).Nodup &&
    P.netlist.branches.filterMap (fun br => elemInput br.elem) == List.range P.netlist.inputs &&
    P.netlist.branches.all (fun br => isDecimal (elemValue br.elem)) &&
    P.probes.all (·.check P.netlist)

/-! ### Lines and words -/

section RoundTrip

variable {p : Char → Bool}

private theorem splitBy_append_cons {l : List Char} (hl : ∀ x ∈ l, p x = false) {c : Char}
    (hc : p c = true) (rest : List Char) :
    splitBy p (l ++ c :: rest) = l :: splitBy p rest := by
  induction l with
  | nil => simp [splitBy, hc]
  | cons x l ih =>
    simp only [List.cons_append, splitBy, hl x List.mem_cons_self, Bool.false_eq_true,
      ↓reduceIte, ih fun y hy => hl y (List.mem_cons_of_mem _ hy), List.headD_cons,
      List.tail_cons]

private theorem splitBy_of_forall {l : List Char} (hl : ∀ x ∈ l, p x = false) :
    splitBy p l = [l] := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [splitBy, hl x List.mem_cons_self, Bool.false_eq_true, ↓reduceIte,
      ih fun y hy => hl y (List.mem_cons_of_mem _ hy), List.headD_cons, List.tail_cons]

/-- A word of the printer: nonempty, without blanks or line breaks. -/
private def IsWord (w : List Char) : Prop := w ≠ [] ∧ ∀ c ∈ w, isBlank c = false ∧ c ≠ '\n'

private theorem splitBy_intercalate :
    ∀ {ws : List (List Char)}, ws ≠ [] → (∀ w ∈ ws, ∀ c ∈ w, isBlank c = false) →
      splitBy isBlank ([' '].intercalate ws) = ws
  | [], h, _ => absurd rfl h
  | [w], _, hw => by simpa using splitBy_of_forall (hw w List.mem_cons_self)
  | w :: w' :: ws, _, hw => by
    rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
      splitBy_append_cons (hw w List.mem_cons_self) (by decide),
      splitBy_intercalate (List.cons_ne_nil _ _) fun v hv => hw v (List.mem_cons_of_mem _ hv)]

private theorem words_line {ws : List (List Char)} (hw : ∀ w ∈ ws, IsWord w) :
    words ([' '].intercalate ws) = ws := by
  rcases ws with _ | ⟨w, ws⟩
  · rfl
  · rw [words, splitBy_intercalate (List.cons_ne_nil _ _) fun v hv c hc => ((hw v hv).2 c hc).1]
    exact List.filter_eq_self.2 fun v hv => by simpa using (hw v hv).1

private theorem newline_not_mem_line :
    ∀ {ws : List (List Char)}, (∀ w ∈ ws, IsWord w) →
      ∀ c ∈ [' '].intercalate ws, (c == '\n') = false
  | [], _, c, hc => by simp at hc
  | [w], hw, c, hc => by
    simpa using ((hw w List.mem_cons_self).2 c (by simpa using hc)).2
  | w :: w' :: ws, hw, c, hc => by
    rw [List.intercalate_cons_cons, List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · simpa using ((hw w List.mem_cons_self).2 c hc).2
    · simp only [List.mem_singleton] at hc; subst hc; decide
    · exact newline_not_mem_line (fun v hv => hw v (List.mem_cons_of_mem _ hv)) c hc

/-! ### Values -/

private theorem digits_append :
    ∀ {l : List Char}, (∀ c ∈ l, c.isDigit = true) → ∀ {r : List Char},
      (∀ c ∈ r.head?, c.isDigit = false) → digits (l ++ r) = (l, r)
  | [], _, [], _ => rfl
  | [], _, c :: r, hr => by simp [digits, hr c rfl]
  | x :: l, hl, r, hr => by
    rw [List.cons_append, digits, ite_eq_left (hl x List.mem_cons_self),
      digits_append (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hr]

private theorem fraction_cons {c : Char} (hc : c ≠ '.') (cs : List Char) :
    fraction (c :: cs) = ([], c :: cs) := by
  unfold fraction
  split
  · rename_i h; cases h; exact absurd rfl hc
  · rfl

private theorem digitsVal_nil : digitsVal [] = 0 := rfl

private theorem digitsVal_toDecimal (n : ℕ) : digitsVal (Nat.toDecimal n) = n := by
  have := (Nat.ofDecimal?_eq_some_iff.1 (Nat.ofDecimal?_toDecimal n)).2.2
  rwa [digitsVal, Nat.foldl_digitStep_eq_ofDigitChars]

private theorem sign_of_isDigit {d : Char} (hd : d.isDigit = true) (cs : List Char) :
    sign (d :: cs) = (false, d :: cs) := by
  unfold sign
  split
  · rename_i h; cases h; simp at hd
  · rename_i h; cases h; simp at hd
  · rfl

private theorem toDecimal_digits (n : ℕ) (r : List Char) (hr : ∀ c ∈ r.head?, c.isDigit = false) :
    digits (Nat.toDecimal n ++ r) = (Nat.toDecimal n, r) :=
  digits_append (fun _ hc => Nat.isDigit_of_mem_toDecimal hc) hr

/-- The sign and the digits of `Int.toDecimal a`. -/
private theorem sign_intToDecimal (a : ℤ) (r : List Char) :
    sign (Int.toDecimal a ++ r) = (decide (a < 0), Nat.toDecimal a.natAbs ++ r) := by
  unfold Int.toDecimal
  split_ifs with h
  · simp [sign, h]
  · obtain ⟨d, ds, he, hd⟩ := Nat.exists_toDecimal_eq_cons a.natAbs
    rw [he, List.cons_append, sign_of_isDigit hd]
    simp [h]

private theorem intCast_natAbs_sign (a : ℤ) :
    ((if decide (a < 0) = true then -1 else 1) * ((a.natAbs : ℕ) : ℚ)) = (a : ℚ) := by
  by_cases h : a < 0
  · simp only [h, decide_true, ↓reduceIte, neg_mul, one_mul]
    have : (a.natAbs : ℤ) = -a := by omega
    rw [← Int.cast_natCast, this, Int.cast_neg, neg_neg]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, one_mul]
    have : (a.natAbs : ℤ) = a := by omega
    rw [← Int.cast_natCast, this]

private theorem value?_intToDecimal (a : ℤ) : value? (Int.toDecimal a) = some (a : ℚ) := by
  have h := sign_intToDecimal a []
  rw [List.append_nil] at h
  simp only [value?, h, List.append_nil]
  rw [show digits (Nat.toDecimal a.natAbs) = (Nat.toDecimal a.natAbs, []) by
    simpa using toDecimal_digits a.natAbs [] (by simp)]
  simp only [fraction, exponent, lower, List.map_nil, suffixExp, digitsVal_toDecimal, digitsVal_nil,
    List.isEmpty_iff, Nat.toDecimal_ne_nil, ↓reduceIte, List.length_nil,
    pow_zero, Nat.cast_zero, zero_div, add_zero, zpow_zero, mul_one, intCast_natAbs_sign]

private theorem decExp_dvd {d k : ℕ} (h : decExp d = some k) : d ∣ 10 ^ k := by
  have := List.find?_some h
  simpa [Nat.dvd_iff_mod_eq_zero] using this

/-- **Values are read back.** -/
theorem value?_printValue {q : ℚ} (hq : isDecimal q = true) : value? (printValue q) = some q := by
  unfold printValue
  split_ifs with h1
  · rw [value?_intToDecimal]
    exact congrArg some (Rat.intCast_num_of_den_eq_one h1)
  · have hk : ∃ k, decExp q.den = some k := by
      simp only [isDecimal, Bool.or_eq_true, beq_iff_eq, h1, false_or,
        Option.isSome_iff_exists] at hq
      exact hq
    obtain ⟨k, hk⟩ := hk
    rw [hk]
    dsimp only
    set m := q.num * ((10 ^ k / q.den : ℕ) : ℤ)
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    have hd : digits (Nat.toDecimal m.natAbs ++ 'e' :: '-' :: Nat.toDecimal k) =
        (Nat.toDecimal m.natAbs, 'e' :: '-' :: Nat.toDecimal k) :=
      toDecimal_digits _ _ (by simp)
    have he : exponent ('e' :: '-' :: Nat.toDecimal k) = (-(k : ℤ), []) := by
      have h2 : digits (Nat.toDecimal k) = (Nat.toDecimal k, []) := by
        simpa using toDecimal_digits k [] (by simp)
      simp [exponent, sign, h2, Nat.toDecimal_ne_nil, digitsVal_toDecimal]
    simp only [value?, sign_intToDecimal, hd, fraction_cons (show 'e' ≠ '.' by decide), he,
      lower, List.map_nil, suffixExp, digitsVal_nil,
      List.isEmpty_iff, Nat.toDecimal_ne_nil, ↓reduceIte, List.length_nil, pow_zero,
      Nat.cast_zero, zero_div, add_zero, digitsVal_toDecimal]
    rw [← mul_assoc, intCast_natAbs_sign]
    obtain ⟨c, hc⟩ := decExp_dvd hk
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hc' : (10 ^ k / q.den : ℕ) = c := by
      rw [hc, Nat.mul_div_cancel_left _ q.den_pos]
    have hcq : ((10 : ℚ) ^ k) = q.den * c := by exact_mod_cast hc
    congr 1
    simp only [m, hc', Int.cast_mul, Int.cast_natCast, zpow_neg, zpow_natCast, hcq]
    have hc0 : (c : ℚ) ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hcq; exact pow_ne_zero k (by norm_num) hcq
    rw [mul_inv, ← mul_assoc]
    calc (q.num : ℚ) * c * (q.den : ℚ)⁻¹ * (c : ℚ)⁻¹ = q.num / q.den := by
          field_simp
      _ = q := Rat.num_div_den q

/-! ### Cards -/

/-- Whether the printer writes a card in a form that the reader reads back: well-formed names
and nodes, a supported element letter with its number of nodes, an input port only on a
source, and a decimal value. -/
private def Card.Printable : Card → Prop
  | .element name nodes v ac => ∃ c rest, name = c :: rest ∧ name.all isNameChar = true ∧
      arity c.toLower = nodes.length ∧ nodes.length ≠ 0 ∧ (∀ n ∈ nodes, isNodeName n = true) ∧
      isDecimal v = true ∧ (ac = true → isSource c.toLower = true)
  | .probeV p q => isNodeName p = true ∧ isNodeName q = true
  | .probeI n => n ≠ [] ∧ n.all isNameChar = true

private theorem isWord_lit {w : List Char} (hne : w ≠ [])
    (h : w.all (fun c => !isBlank c && c != '\n') = true) : IsWord w :=
  ⟨hne, fun c hc => by simpa using List.all_eq_true.1 h c hc⟩

private theorem not_blank_of_isNameChar {c : Char} (h : isNameChar c = true) :
    isBlank c = false ∧ c ≠ '\n' := by
  refine ⟨?_, ?_⟩
  · cases hb : isBlank c
    · rfl
    · simp only [isBlank, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with (rfl | rfl) | rfl <;> exact absurd h (by decide)
  · rintro rfl; exact absurd h (by decide)

private theorem isWord_of_name {w : List Char} (hne : w ≠ []) (h : w.all isNameChar = true) :
    IsWord w :=
  ⟨hne, fun c hc => not_blank_of_isNameChar (List.all_eq_true.1 h c hc)⟩

private theorem isWord_of_isNodeName {w : List Char} (h : isNodeName w = true) : IsWord w := by
  simp only [isNodeName, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  exact isWord_of_name h.1.1 h.1.2

private theorem printValue_chars {q : ℚ} :
    ∀ c ∈ printValue q, c.isDigit = true ∨ c = '-' ∨ c = 'e' := by
  intro c hc
  unfold printValue at hc
  have hint : ∀ a : ℤ, ∀ c ∈ Int.toDecimal a, c.isDigit = true ∨ c = '-' ∨ c = 'e' := by
    intro a c hc
    unfold Int.toDecimal at hc
    split_ifs at hc
    · simp only [List.mem_cons] at hc
      rcases hc with h | hc
      · exact .inr (.inl h)
      · exact .inl (Nat.isDigit_of_mem_toDecimal hc)
    · exact .inl (Nat.isDigit_of_mem_toDecimal hc)
  split_ifs at hc
  · exact hint _ c hc
  · split at hc
    · rw [List.mem_append, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact hint _ c hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with h | h
        · exact .inr (.inr h)
        · exact .inr (.inl h)
      · exact .inl (Nat.isDigit_of_mem_toDecimal hc)
    · simp at hc

private theorem printValue_ne_nil {q : ℚ} (hq : isDecimal q = true) : printValue q ≠ [] := by
  intro h
  have := value?_printValue hq
  rw [h] at this
  simp [value?, sign, digits] at this

private theorem isWord_printValue {q : ℚ} (hq : isDecimal q = true) : IsWord (printValue q) := by
  refine ⟨printValue_ne_nil hq, fun c hc => ?_⟩
  rcases printValue_chars c hc with h | rfl | rfl
  · refine ⟨?_, ?_⟩
    · simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [isBlank, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro rfl <;> simp_all
    · rintro rfl; simp at h
  · decide
  · decide

private theorem isWord_cardWords {c : Card} (hc : c.Printable) : ∀ w ∈ cardWords c, IsWord w := by
  cases c with
  | element name nodes v ac =>
    obtain ⟨c, rest, rfl, hn, -, -, hnodes, hv, -⟩ := hc
    intro w hw
    simp only [cardWords, List.cons_append, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | ((hw | hw) | rfl | hw)
    · exact isWord_of_name (List.cons_ne_nil _ _) hn
    · exact isWord_of_isNodeName (hnodes w hw)
    · split_ifs at hw
      · simp only [List.mem_singleton] at hw; subst hw
        exact isWord_lit (by simp) (by decide)
      · simp at hw
    · exact isWord_printValue hv
    · split_ifs at hw
      · simp only [List.mem_singleton] at hw; subst hw
        exact isWord_lit (by simp) (by decide)
      · simp at hw
  | probeV p q =>
    intro w hw
    simp only [cardWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact isWord_lit (by simp) (by decide)
    · exact isWord_lit (by simp) (by decide)
    · exact isWord_of_isNodeName hc.1
    · exact isWord_of_isNodeName hc.2
  | probeI n =>
    intro w hw
    simp only [cardWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact isWord_lit (by simp) (by decide)
    · exact isWord_lit (by simp) (by decide)
    · exact isWord_of_name hc.1 hc.2

private theorem arity_ne_zero {c : Char} (h : arity c ≠ 0) :
    c ≠ '*' ∧ c ≠ '.' := by
  refine ⟨?_, ?_⟩ <;> rintro rfl <;> exact h (by decide)

private theorem elementCard_cardWords {name : List Char} {nodes : List (List Char)} {v : ℚ}
    {ac : Bool}
    (h : (Card.element name nodes v ac).Printable) :
    elementCard name ((cardWords (.element name nodes v ac)).tail) =
      .ok (.element name nodes v ac) := by
  obtain ⟨c, rest, rfl, hn, har, hne, hnodes, hv, hac⟩ := h
  have hnodes' : nodes.all isNodeName = true := List.all_eq_true.2 hnodes
  simp only [cardWords, List.cons_append, List.tail_cons, List.headD_cons, elementCard, har,
    List.append_assoc, List.take_left' rfl, List.drop_left' rfl, hne, hn, hnodes',
    bne_self_eq_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hs : isSource c.toLower = true
  · have hdc : (List.map Char.toLower ['d', 'c'] == "dc".toList) = true := by decide
    simp only [hs, ↓reduceIte, List.singleton_append, sourceSpec, lower, hdc,
      value?_printValue hv]
    cases ac <;> rfl
  · have hac' : ac = false := by cases ac <;> simp_all
    subst hac'
    simp only [hs, Bool.false_eq_true, ↓reduceIte, List.nil_append, value?_printValue hv]

private theorem end_toList : ".end".toList = ['.', 'e', 'n', 'd'] := rfl

private theorem probe_toList : ".probe".toList = ['.', 'p', 'r', 'o', 'b', 'e'] := rfl

private theorem cards_cardWords (rest : List (List Char)) :
    ∀ {cs : List Card}, (∀ c ∈ cs, c.Printable) →
      cards ((cs.map fun c => [' '].intercalate (cardWords c)) ++
        [' '].intercalate [".end".toList] :: rest) = .ok cs
  | [], _ => by
    have h : words ([' '].intercalate [".end".toList]) = [".end".toList] := by decide
    simp only [List.map_nil, List.nil_append, cards, h]
    rfl
  | c :: cs, hcs => by
    have ih := cards_cardWords rest fun d hd => hcs d (List.mem_cons_of_mem _ hd)
    have hc := hcs c List.mem_cons_self
    rw [List.map_cons, List.cons_append, cards, words_line (isWord_cardWords hc)]
    cases c with
    | element name nodes v ac =>
      have hw := elementCard_cardWords hc
      obtain ⟨d, rest', rfl, -, har, hne, -⟩ := hc
      have ha : arity d.toLower ≠ 0 := har ▸ hne
      have hstar : d ≠ '*' := by rintro rfl; exact ha (by decide)
      have hdot : d ≠ '.' := by rintro rfl; exact ha (by decide)
      have hdot' : d.toLower ≠ '.' := by intro h; rw [h] at ha; exact ha (by decide)
      have hcw : cardWords (.element (d :: rest') nodes v ac) =
          (d :: rest') :: (cardWords (.element (d :: rest') nodes v ac)).tail := rfl
      rw [hcw, ih]
      simp only [List.head?_cons, beq_iff_eq, Option.some.injEq, hstar, hdot, ↓reduceIte, lower,
        List.map_cons, end_toList, probe_toList, List.cons.injEq, hdot', false_and, hw]
    | probeV p q =>
      rw [ih]
      simp only [cardWords, probe_toList, List.head?_cons, beq_iff_eq, Option.some.injEq,
        lower, List.map_cons, List.map_nil, end_toList, List.cons.injEq, ↓reduceIte, probeCard,
        hc.1, hc.2]
      simp +decide
    | probeI n =>
      rw [ih]
      simp only [cardWords, probe_toList, List.head?_cons, beq_iff_eq, Option.some.injEq,
        lower, List.map_cons, List.map_nil, end_toList, List.cons.injEq, ↓reduceIte, probeCard]
      simp +decide

private theorem lines_flatMap (rest : List Char) :
    ∀ {ls : List (List Char)}, (∀ l ∈ ls, ∀ c ∈ l, (c == '\n') = false) →
      lines (ls.flatMap (· ++ ['\n']) ++ rest) = ls ++ lines rest
  | [], _ => rfl
  | l :: ls, h => by
    rw [List.flatMap_cons, List.append_assoc, List.append_assoc, List.singleton_append, lines,
      splitBy_append_cons (h l List.mem_cons_self) (by decide), ← lines,
      lines_flatMap rest fun m hm => h m (List.mem_cons_of_mem _ hm), List.cons_append]

private theorem lines_printCards {cs : List Card} (hcs : ∀ c ∈ cs, c.Printable) :
    lines (printCards cs) = [' '].intercalate [".title".toList, "netlist".toList] ::
      ((cs.map fun c => [' '].intercalate (cardWords c)) ++
        [' '].intercalate [".end".toList] :: [[]]) := by
  have h : printCards cs = ([' '].intercalate [".title".toList, "netlist".toList] ::
      ((cs.map fun c => [' '].intercalate (cardWords c)) ++
        [[' '].intercalate [".end".toList]])).flatMap (· ++ ['\n']) ++ [] := by
    simp [printCards, line, List.flatMap_append, List.flatMap_map]
  rw [h, lines_flatMap]
  · simp [lines, splitBy]
  · intro l hl
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | ⟨c, hc, rfl⟩ | rfl
    · exact newline_not_mem_line fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact isWord_lit (by simp) (by decide)
    · exact newline_not_mem_line (isWord_cardWords (hcs c hc))
    · exact newline_not_mem_line fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; exact isWord_lit (by simp) (by decide)

/-- **The reader reads back the printed cards**, before resolving their names. -/
private theorem parse_printCards {cs : List Card} (hcs : ∀ c ∈ cs, c.Printable) :
    parse (String.ofList (printCards cs)) = resolve cs := by
  rw [parse, String.toList_ofList, lines_printCards hcs]
  simp only [cards_cardWords [[]] hcs]

/-! ### Resolving the printed names -/

private theorem firstOccurrences_map {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) : ∀ (seen l : List α), Set.InjOn f {x | x ∈ seen ∨ x ∈ l} →
      firstOccurrences (seen.map f) (l.map f) = (firstOccurrences seen l).map f
  | seen, [], _ => by simp [firstOccurrences, List.map_reverse]
  | seen, a :: l, hf => by
    have hc : (seen.map f).contains (f a) = seen.contains a := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
      exact ⟨fun ⟨x, hx, he⟩ => hf (.inl hx) (.inr List.mem_cons_self) he ▸ hx,
        fun h => ⟨a, h, rfl⟩⟩
    rw [List.map_cons, firstOccurrences, firstOccurrences, hc]
    split_ifs
    · exact firstOccurrences_map f seen l fun x hx y hy => hf
        (hx.imp_right (List.mem_cons_of_mem _)) (hy.imp_right (List.mem_cons_of_mem _))
    · rw [← List.map_cons]
      refine firstOccurrences_map f (a :: seen) l fun x hx y hy => hf ?_ ?_
      · rcases hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact .inr List.mem_cons_self
          · exact .inl hx
        · exact .inr (List.mem_cons_of_mem _ hx)
      · rcases hy with hy | hy
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact .inr List.mem_cons_self
          · exact .inl hy
        · exact .inr (List.mem_cons_of_mem _ hy)

private theorem mem_firstOccurrences {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (seen l : List α) (x : α), x ∈ seen ∨ x ∈ l → x ∈ firstOccurrences seen l
  | seen, [], x, h => by simpa [firstOccurrences] using h
  | seen, a :: l, x, h => by
    rw [firstOccurrences]
    split_ifs with ha
    · refine mem_firstOccurrences seen l x ?_
      rcases h with h | h
      · exact .inl h
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl (List.contains_iff_mem.1 ha)
        · exact .inr h
    · refine mem_firstOccurrences (a :: seen) l x ?_
      rcases h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr h

private theorem map_nodeName_range' (names : List (List Char)) :
    (List.range' 1 names.length).map (nodeName names) = names := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [nodeName, List.getD_eq_getElem?_getD, h₂]

private theorem nodeIndex_nodeName {names : List (List Char)} (hnd : names.Nodup)
    (h0 : ['0'] ∉ names) {k : ℕ} (hk : k ≤ names.length) :
    nodeIndex names (nodeName names k) = k := by
  rcases k with _ | k
  · rfl
  · have hk' : k < names.length := by omega
    have hne : names[k] ≠ ['0'] := fun h => h0 (h ▸ List.getElem_mem hk')
    simp [nodeName, nodeIndex, List.getD_eq_getElem?_getD, hk', hne, hnd.idxOf_getElem k hk']

private theorem nodeName_eq_zero {names : List (List Char)} (h0 : ['0'] ∉ names) {k : ℕ} :
    nodeName names k = ['0'] ↔ k = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, nodeName]⟩
  by_contra hk
  simp only [nodeName, hk, ↓reduceIte, List.getD_eq_getElem?_getD] at h
  rcases hg : names[k - 1]? with _ | w
  · rw [hg] at h; simp at h
  · rw [hg, Option.getD_some] at h
    exact h0 (h ▸ List.mem_of_getElem? hg)

private theorem nodeName_injOn {names : List (List Char)} (hnd : names.Nodup) :
    Set.InjOn (nodeName names) {k | k ∈ List.range' 1 names.length} := by
  intro x hx y hy he
  simp only [Set.mem_ofPred_eq, List.mem_range'_1] at hx hy
  simp only [nodeName, show x ≠ 0 by omega, show y ≠ 0 by omega, ↓reduceIte,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x - 1 < names.length by omega),
    List.getElem?_eq_getElem (show y - 1 < names.length by omega), Option.getD_some] at he
  have := (hnd.getElem_inj_iff).1 he
  omega

private theorem toBranch_branchCard {names : List (List Char)} (hnd : names.Nodup)
    (h0 : ['0'] ∉ names)
    {nm : List Char} {br : Branch} {k : ℕ} (hk : ∀ j ∈ branchNodes br, j ≤ names.length)
    (hl : (nm.headD 'x').toLower = elemLetter br.elem)
    (hin : ∀ j, elemInput br.elem = some j → j = k) :
    toBranch names k (branchCard names nm br) = br := by
  obtain ⟨pos, neg, elem⟩ := br
  have hp : nodeIndex names (nodeName names pos) = pos :=
    nodeIndex_nodeName hnd h0 (hk pos (by simp [branchNodes]))
  have hn : nodeIndex names (nodeName names neg) = neg :=
    nodeIndex_nodeName hnd h0 (hk neg (by simp [branchNodes]))
  cases elem with
  | voltageSource v input =>
    have hi : (if input.isSome then some k else none) = input := by
      cases input with
      | none => rfl
      | some j => simp [hin j rfl]
    simp_all [toBranch, branchCard, branchNodes, elemLetter, elemValue, elemInput]
  | currentSource v input =>
    have hi : (if input.isSome then some k else none) = input := by
      cases input with
      | none => rfl
      | some j => simp [hin j rfl]
    simp_all [toBranch, branchCard, branchNodes, elemLetter, elemValue, elemInput]
  | vccs g cp cn =>
    have hcp : nodeIndex names (nodeName names cp) = cp :=
      nodeIndex_nodeName hnd h0 (hk cp (by simp [branchNodes]))
    have hcn : nodeIndex names (nodeName names cn) = cn :=
      nodeIndex_nodeName hnd h0 (hk cn (by simp [branchNodes]))
    simp_all [toBranch, branchCard, branchNodes, elemLetter, elemValue, elemInput]
  | vcvs g cp cn =>
    have hcp : nodeIndex names (nodeName names cp) = cp :=
      nodeIndex_nodeName hnd h0 (hk cp (by simp [branchNodes]))
    have hcn : nodeIndex names (nodeName names cn) = cn :=
      nodeIndex_nodeName hnd h0 (hk cn (by simp [branchNodes]))
    simp_all [toBranch, branchCard, branchNodes, elemLetter, elemValue, elemInput]
  | _ => simp_all [toBranch, branchCard, branchNodes, elemLetter, elemValue, elemInput]

private theorem branchesOf_probeCards (P : ParsedNetlist) (names : List (List Char)) (k : ℕ) :
    ∀ ps : List Probe, branchesOf names k (ps.map (probeCardOf P)) = []
  | [] => rfl
  | .voltage _ _ :: ps => by simp only [List.map_cons, probeCardOf, branchesOf,
      branchesOf_probeCards P names k ps]
  | .current _ :: ps => by simp only [List.map_cons, probeCardOf, branchesOf,
      branchesOf_probeCards P names k ps]

private theorem branchesOf_zipWith {names : List (List Char)} (hnd : names.Nodup)
    (h0 : ['0'] ∉ names)
    (rest : List Card) (hrest : ∀ k, branchesOf names k rest = []) :
    ∀ (nms : List (List Char)) (bs : List Branch) (k m : ℕ), nms.length = bs.length →
      (∀ br ∈ bs, ∀ j ∈ branchNodes br, j ≤ names.length) →
      (∀ nb ∈ List.zip nms bs, (nb.1.headD 'x').toLower = elemLetter nb.2.elem) →
      bs.filterMap (fun br => elemInput br.elem) = List.range' k m →
      branchesOf names k (List.zipWith (branchCard names) nms bs ++ rest) = bs
  | [], [], k, _, _, _, _, _ => by simpa using hrest k
  | nm :: nms, br :: bs, k, m, hl, hk, hn, hin => by
    have hl' : nms.length = bs.length := by simpa using hl
    simp only [List.zipWith_cons_cons, List.cons_append, branchCard, branchesOf]
    rw [← branchCard]
    have hk' := fun b hb => hk b (List.mem_cons_of_mem _ hb)
    have hn' := fun nb hnb => hn nb (List.mem_cons_of_mem _ hnb)
    rcases hi : elemInput br.elem with _ | j
    · rw [List.filterMap_cons, hi] at hin
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [toBranch_branchCard hnd h0 (hk br List.mem_cons_self) (hn _ List.mem_cons_self)
        (by simp [hi]), branchesOf_zipWith hnd h0 rest hrest nms bs k m hl' hk' hn' hin]
    · rw [List.filterMap_cons, hi] at hin
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        rcases m with _ | m'
        · simp at hin
        · exact ⟨m', rfl⟩
      rw [List.range'_succ, List.cons.injEq] at hin
      simp only [Option.isSome_some, ↓reduceIte]
      rw [toBranch_branchCard hnd h0 (hk br List.mem_cons_self) (hn _ List.mem_cons_self)
        (by intro j' hj'; rw [hi] at hj'; cases hj'; exact hin.1),
        branchesOf_zipWith hnd h0 rest hrest nms bs (k + 1) m' hl' hk' hn' (by simpa using hin.2)]

private theorem nodeRefs_toCards {P : ParsedNetlist} (h0 : ['0'] ∉ P.nodeNames)
    (hl : P.branchNames.length = P.netlist.branches.length) :
    nodeRefs (toCards P) = (nodeRefIdx P.netlist).map (nodeName P.nodeNames) := by
  have hp : nodeRefs (P.probes.map (probeCardOf P)) = [] := by
    simp only [nodeRefs, List.flatMap_eq_nil_iff, List.mem_map]
    rintro _ ⟨p, -, rfl⟩
    cases p <;> rfl
  have key : ∀ (nms : List (List Char)) (bs : List Branch), nms.length = bs.length →
      nodeRefs (List.zipWith (branchCard P.nodeNames) nms bs) =
        (bs.flatMap fun br => (branchNodes br).filter (· != 0)).map (nodeName P.nodeNames) := by
    intro nms bs h
    induction nms generalizing bs with
    | nil => cases bs <;> simp_all [nodeRefs]
    | cons nm nms ih =>
      rcases bs with _ | ⟨br, bs⟩
      · simp at h
      · simp only [List.zipWith_cons_cons, nodeRefs, List.flatMap_cons, List.map_append] at ih ⊢
        rw [ih bs (by simpa using h), branchCard]
        dsimp only
        rw [List.filter_map]
        congr 2
        refine List.filter_congr fun k _ => ?_
        rw [Bool.eq_iff_iff]
        simp only [Function.comp, bne_iff_ne, ne_eq, nodeName_eq_zero h0]
  rw [toCards, show nodeRefs (List.zipWith (branchCard P.nodeNames) P.branchNames
      P.netlist.branches ++ P.probes.map (probeCardOf P)) =
      nodeRefs (List.zipWith (branchCard P.nodeNames) P.branchNames P.netlist.branches) ++
        nodeRefs (P.probes.map (probeCardOf P)) from List.flatMap_append,
    hp, List.append_nil, key _ _ hl, nodeRefIdx]

private theorem elementNames_toCards {P : ParsedNetlist}
    (hl : P.branchNames.length = P.netlist.branches.length) :
    elementNames (toCards P) = P.branchNames := by
  have hp : elementNames (P.probes.map (probeCardOf P)) = [] := by
    simp only [elementNames, List.filterMap_eq_nil_iff, List.mem_map]
    rintro _ ⟨p, -, rfl⟩
    cases p <;> rfl
  have key : ∀ (nms : List (List Char)) (bs : List Branch), nms.length = bs.length →
      elementNames (List.zipWith (branchCard P.nodeNames) nms bs) = nms := by
    intro nms bs h
    induction nms generalizing bs with
    | nil => rfl
    | cons nm nms ih =>
      rcases bs with _ | ⟨br, bs⟩
      · simp at h
      · simp only [List.zipWith_cons_cons, elementNames, List.filterMap_cons, branchCard] at ih ⊢
        rw [ih bs (by simpa using h)]
  rw [toCards, elementNames, List.filterMap_append, ← elementNames, ← elementNames, hp,
    List.append_nil, key _ _ hl]

private theorem inputCount_toCards {P : ParsedNetlist}
    (hl : P.branchNames.length = P.netlist.branches.length) :
    inputCount (toCards P) =
      (P.netlist.branches.filterMap fun br => elemInput br.elem).length := by
  have key : ∀ (nms : List (List Char)) (bs : List Branch), nms.length = bs.length →
      inputCount (List.zipWith (branchCard P.nodeNames) nms bs ++
          P.probes.map (probeCardOf P)) =
        (bs.filterMap fun br => elemInput br.elem).length := by
    intro nms bs h
    induction nms generalizing bs with
    | nil =>
      cases bs
      · simp only [inputCount, List.zipWith_nil_left, List.nil_append, List.filterMap_nil,
          List.length_nil, List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_map]
        rintro _ ⟨p, -, rfl⟩
        cases p <;> simp [probeCardOf]
      · simp at h
    | cons nm nms ih =>
      rcases bs with _ | ⟨br, bs⟩
      · simp at h
      · have := ih bs (by simpa using h)
        simp only [inputCount, List.zipWith_cons_cons, List.cons_append, List.filter_cons,
          branchCard, List.filterMap_cons, List.filter_append, List.length_append] at this ⊢
        rcases elemInput br.elem with _ | j <;> simp [this]
  exact key _ _ hl

private theorem mapM_toProbe {P : ParsedNetlist} (hnd : P.nodeNames.Nodup)
    (h0 : ['0'] ∉ P.nodeNames)
    (hbnd : P.branchNames.Nodup) (hn : P.netlist.nodes = P.nodeNames.length)
    (hl : P.branchNames.length = P.netlist.branches.length) :
    ∀ ps : List Probe, (∀ p ∈ ps, p.check P.netlist = true) →
      (ps.map (probeCardOf P)).mapM (toProbe P.nodeNames P.branchNames) = .ok ps
  | [], _ => rfl
  | p :: ps, h => by
    have ih := mapM_toProbe hnd h0 hbnd hn hl ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    have hmem : ∀ {k}, k ≤ P.nodeNames.length →
        nodeName P.nodeNames k = ['0'] ∨ nodeName P.nodeNames k ∈ P.nodeNames := by
      intro k hk
      rcases k with _ | k
      · exact .inl rfl
      · refine .inr ?_
        have hk' : k < P.nodeNames.length := by omega
        simp only [nodeName, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem hk', Option.getD_some]
        exact List.getElem_mem _
    rw [List.map_cons, List.mapM_cons, ih]
    cases p with
    | voltage a b =>
      simp only [Probe.check, Bool.and_eq_true, decide_eq_true_eq, hn] at hp
      simp only [probeCardOf, toProbe, hmem hp.1, hmem hp.2, and_self, ↓reduceIte,
        nodeIndex_nodeName hnd h0 hp.1, nodeIndex_nodeName hnd h0 hp.2]
      rfl
    | current b =>
      simp only [Probe.check, decide_eq_true_eq, ← hl] at hp
      have he : P.branchNames.getD b [] = P.branchNames[b] := by
        simp [List.getD_eq_getElem?_getD, hp]
      simp only [probeCardOf, toProbe, he, List.getElem_mem, ↓reduceIte,
        hbnd.idxOf_getElem b hp]
      rfl

private theorem arity_elemLetter (br : Branch) :
    arity (elemLetter br.elem) = (branchNodes br).length := by
  obtain ⟨pos, neg, elem⟩ := br
  cases elem <;> rfl

private theorem nodeBound {P : ParsedNetlist}
    (horder : firstOccurrences [] (nodeRefIdx P.netlist) = List.range' 1 P.nodeNames.length)
    {br : Branch} (hbr : br ∈ P.netlist.branches) {j : ℕ} (hj : j ∈ branchNodes br) :
    j ≤ P.nodeNames.length := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact Nat.zero_le _
  · have hmem : j ∈ nodeRefIdx P.netlist :=
      List.mem_flatMap.2 ⟨br, hbr, List.mem_filter.2 ⟨hj, by simp; omega⟩⟩
    have := mem_firstOccurrences [] _ j (.inr hmem)
    rw [horder, List.mem_range'_1] at this
    omega

private theorem isNodeName_nodeName {names : List (List Char)}
    (hv : ∀ w ∈ names, isNodeName w = true) {k : ℕ} (hk : k ≤ names.length) :
    isNodeName (nodeName names k) = true := by
  rcases k with _ | k
  · change isNodeName ['0'] = true; decide
  · have hk' : k < names.length := by omega
    simp only [nodeName, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hk', Option.getD_some]
    exact hv _ (List.getElem_mem _)

/-- **The round trip**: the reader reads back every printable netlist that the printer
writes. -/
theorem parse_print {P : ParsedNetlist} (h : P.isPrintable = true) : parse (print P) = .ok P := by
  simp only [ParsedNetlist.isPrintable, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hv⟩, hlow⟩, horder⟩, hl⟩, hbn⟩, hblow⟩, hin⟩, hval⟩, hpr⟩ := h
  have hnd : P.nodeNames.Nodup := hlow.of_map _
  have hbnd : P.branchNames.Nodup := hblow.of_map _
  have h0 : ['0'] ∉ P.nodeNames := fun h => by simpa using (hv _ h).2
  have hv' : ∀ w ∈ P.nodeNames, isNodeName w = true := fun w hw => (hv w hw).1
  have hzip : ∀ nb ∈ List.zip P.branchNames P.netlist.branches,
      ∃ c rest, nb.1 = c :: rest ∧ c.toLower = elemLetter nb.2.elem := by
    intro nb hnb
    obtain ⟨h1, h2⟩ := hbn nb hnb
    rcases hnm : nb.1 with _ | ⟨c, rest⟩
    · rw [hnm] at h2; simp at h2
    · rw [hnm] at h2; exact ⟨c, rest, rfl, by simpa using h2⟩
  -- the cards are printable
  have hprint : ∀ c ∈ toCards P, c.Printable := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · rw [← List.map_uncurry_zip_eq_zipWith, List.mem_map] at hc
      obtain ⟨⟨nm, br⟩, hnb, rfl⟩ := hc
      obtain ⟨d, rest, hnm, hd⟩ := hzip _ hnb
      have hbr : br ∈ P.netlist.branches := (List.of_mem_zip hnb).2
      dsimp only at hnm hd
      refine ⟨d, rest, hnm, List.all_eq_true.2 (hbn _ hnb).1, ?_, ?_, ?_, hval br hbr, ?_⟩
      · rw [hd, arity_elemLetter, List.length_map]
      · rw [List.length_map]; obtain ⟨pos, neg, elem⟩ := br; cases elem <;> simp [branchNodes]
      · intro w hw
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
        exact isNodeName_nodeName hv' (nodeBound horder hbr hj)
      · intro hac
        rw [hd]
        obtain ⟨pos, neg, elem⟩ := br
        cases elem <;> simp_all [elemInput, elemLetter, isSource]
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      have hpc := hpr p hp
      cases p with
      | voltage a b =>
        simp only [Probe.check, Bool.and_eq_true, decide_eq_true_eq, hn] at hpc
        exact ⟨isNodeName_nodeName hv' hpc.1, isNodeName_nodeName hv' hpc.2⟩
      | current b =>
        simp only [Probe.check, decide_eq_true_eq, ← hl] at hpc
        have hmem : (P.branchNames[b], P.netlist.branches[b]'(hl ▸ hpc)) ∈
            List.zip P.branchNames P.netlist.branches := by
          rw [List.mem_iff_getElem]
          exact ⟨b, by simp [hpc, ← hl], by simp⟩
        obtain ⟨d, rest, hnm, -⟩ := hzip _ hmem
        have he : P.branchNames.getD b [] = P.branchNames[b] := by
          simp [List.getD_eq_getElem?_getD, hpc]
        refine ⟨by rw [he]; dsimp only at hnm; simp [hnm],
          by rw [he]; exact List.all_eq_true.2 (hbn _ hmem).1⟩
  have hfo : firstOccurrences [] ((nodeRefIdx P.netlist).map (nodeName P.nodeNames)) =
      P.nodeNames := by
    have := firstOccurrences_map (nodeName P.nodeNames) [] (nodeRefIdx P.netlist) (by
      intro x hx y hy hxy
      refine nodeName_injOn hnd ?_ ?_ hxy
      · have := mem_firstOccurrences [] _ x hx
        rwa [horder] at this
      · have := mem_firstOccurrences [] _ y hy
        rwa [horder] at this)
    rw [List.map_nil] at this
    rw [this, horder, map_nodeName_range']
  have hfilter : (toCards P).filter isProbeCard =
      P.probes.map (probeCardOf P) := by
    rw [toCards, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append,
      List.filter_eq_self.2]
    · rintro _ hc
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hc
      cases p <;> rfl
    · intro c hc
      rw [← List.map_uncurry_zip_eq_zipWith, List.mem_map] at hc
      obtain ⟨_, -, rfl⟩ := hc
      simp [isProbeCard, branchCard, Function.uncurry]
  have hletter : ∀ nb ∈ List.zip P.branchNames P.netlist.branches,
      (nb.1.headD 'x').toLower = elemLetter nb.2.elem := by
    intro nb hnb
    obtain ⟨c, rest, h1, h2⟩ := hzip nb hnb
    rw [h1, List.headD_cons, h2]
  rw [print, parse_printCards hprint, resolve, nodeRefs_toCards h0 hl, hfo,
    elementNames_toCards hl, probesOf, hfilter, mapM_toProbe hnd h0 hbnd hn hl P.probes hpr]
  simp only [hlow, hblow, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [inputCount_toCards hl, hin, List.length_range, toCards,
    branchesOf_zipWith hnd h0 _ (fun k => branchesOf_probeCards P _ k _) _ _ 0
      P.netlist.inputs hl (fun br hbr j hj => nodeBound horder hbr hj) hletter
      (by rw [hin, List.range_eq_range']), ← hn]

/-- **The guarantee from the printed text.** If a certificate is accepted against the printed
text of a printable netlist `P`, the guarantee holds for `P` itself: the reader is not in the
statement. -/
theorem guarantee_of_checkText_print {P : ParsedNetlist} {cert : NetlistCert}
    (hP : P.isPrintable = true) (h : checkText (print P) cert = true) : cert.Guarantee P := by
  obtain ⟨P', h1, h2⟩ := exists_parse_of_checkText h
  rw [parse_print hP] at h1
  cases h1
  exact h2

end RoundTrip


end Cslib.Electrical.Text
