/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetForm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeNum

/-!
# The first clique as numbers (Lemma 4.3 (c))

The machine of Lemma 6.4 never builds the first clique of `FirstClique.lean`: it recomputes the
groups, positions and widths of Lemma 4.3 by scans over the vertices and edges of the network, and
reads the labels of a table entry from their codes (Lemma 4.1) without decoding them. This module
gives these computations as plain functions on `ℕ`, which the terms of `NetTerms.lean` and
`FirstTerm.lean` compute exactly, and identifies them with the definitions of `FirstClique.lean`
and `Formula.lean`.

## Main definitions

* The network as numbers: `uN`, `wN` (the ends of an edge), `degN` (the length of a port list),
  `portN` (a port), `evalN` (a vertex function at the bits of a number, as a natural number).
* Counts: `degC` (`deg`), `preC` (`pre`), `vgroupC` (`vgroup`), `edgePosC` (`edgePos`), `tgroupC`
  (`tgroup`), `heCnt`, `widthC` (`width`) and `hePosC`, the position of a half-edge in its list
  `halfEdges`.
* Labels from codes: `labOf a c` (the label coded by `c`, or the empty label), `decBitC` (its bit
  `p`, `decEnc`), `IsEncC` (the encoding test `IsEnc`); `slotN` (the code of the label to node `n`
  in an argument code, read through the budget array).
* `firstDigit`: the budget array of the first clique, digit by digit (layout `arrN` of
  `BudgetNum.lean`).
* `factor0C`: the leaf factors of the first clique.

## Main results

* `degC_eq`, `preC_eq`, `vgroupC_eq`, `edgePosC_eq`, `tgroupC_eq`, `widthC_eq`: the counts.
* `heBit_eq_hePosC`: the bit of a half-edge is the bit at position `hePosC` of the string.
* `decEnc_labOf`, `isEnc_labOf_iff`: the bits and the encoding test, from a code.
* `arrN_firstBudget`: the budget array of the first clique from `firstDigit`.
* `factor0C_eq`: `factor0C` is `Setup.factor0`, for networks with nonnegative vertex functions.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset NtimeDspace.Cube NtimeDspace.Cross

/-! ### Lists and sums -/

theorem listSum_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem ofBits_eq_sum (l : List Bool) :
    ofBits l = ∑ j ∈ range l.length, (l.getD j false).toNat * 2 ^ j := by
  induction l with
  | nil => simp [ofBits]
  | cons b l ih =>
    rw [ofBits, Nat.bit_val, ih, List.length_cons, sum_range_succ', Finset.mul_sum]
    congr 1
    · refine sum_congr rfl fun j _ => ?_
      rw [List.getD_cons_succ, pow_succ]
      ring
    · simp

theorem flatMap_filter_eq {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap fun a => if p a then f a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem flatMap_range_split {α : Type} (f : ℕ → List α) {k n : ℕ} (hk : k < n) :
    ∃ R, (List.range n).flatMap f = (List.range k).flatMap f ++ (f k ++ R) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
  refine ⟨((List.range m).map (k + 1 + ·)).flatMap f, ?_⟩
  simp [List.range_add, List.range_succ, List.flatMap_append]

/-! ### The network as numbers -/

section Net

variable {V : ℕ} (G : EdgeNet ℤ (Fin V))

/-- The first end of edge `i`, as a number (`0` out of range). -/
def uN (i : ℕ) : ℕ := if h : i < G.M then (G.u ⟨i, h⟩ : ℕ) else 0

/-- The second end of edge `i`, as a number (`0` out of range). -/
def wN (i : ℕ) : ℕ := if h : i < G.M then (G.w ⟨i, h⟩ : ℕ) else 0

/-- The length of the port list of vertex `v` (`0` out of range). -/
def degN (v : ℕ) : ℕ := if h : v < V then (G.ports ⟨v, h⟩).length else 0

/-- Port `j` of vertex `v`, an edge number (`0` out of range). -/
def portN (v j : ℕ) : ℕ := if h : v < V then ((G.ports ⟨v, h⟩).map Fin.val).getD j 0 else 0

/-- The vertex function of `v` at the bits of `A` on its ports (bit `j` on port `j`), as a natural
number (`0` out of range). -/
def evalN (v A : ℕ) : ℕ :=
  if h : v < V then
    (G.eval ⟨v, h⟩ (List.ofFn fun j : Fin (G.ports ⟨v, h⟩).length => A.testBit j)).toNat
  else 0

/-- The vertex functions are nonnegative (at arguments of the length of the port list). -/
def EvalNonneg : Prop := ∀ v (x : List Bool), x.length = (G.ports v).length → 0 ≤ G.eval v x

variable {G}

theorem uN_fin (e : Fin G.M) : uN G e = G.u e := by simp [uN]
theorem wN_fin (e : Fin G.M) : wN G e = G.w e := by simp [wN]
theorem degN_fin (v : Fin V) : degN G v = (G.ports v).length := by simp [degN]

theorem uN_lt {i : ℕ} (hi : i < G.M) : uN G i < V := by
  rw [show i = ((⟨i, hi⟩ : Fin G.M) : ℕ) from rfl, uN_fin]; exact (G.u _).isLt

theorem wN_lt {i : ℕ} (hi : i < G.M) : wN G i < V := by
  rw [show i = ((⟨i, hi⟩ : Fin G.M) : ℕ) from rfl, wN_fin]; exact (G.w _).isLt

theorem portN_fin (v : Fin V) {j : ℕ} (hj : j < (G.ports v).length) :
    portN G v j = ((G.ports v)[j] : ℕ) := by
  simp [portN, List.getD_eq_getElem?_getD, hj]

theorem portN_lt {v j : ℕ} (hv : v < V) (hj : j < degN G v) : portN G v j < G.M := by
  rw [show v = ((⟨v, hv⟩ : Fin V) : ℕ) from rfl, degN_fin] at hj
  rw [show v = ((⟨v, hv⟩ : Fin V) : ℕ) from rfl, portN_fin _ hj]
  exact Fin.isLt _

end Net

/-! ### The counts of Lemma 4.3 (c) -/

section Counts

variable {V : ℕ} (G : EdgeNet ℤ (Fin V)) (K : ℕ)

/-- The number of edges at vertex `v` (`deg`), by a scan over the edges. -/
def degC (v : ℕ) : ℕ := ∑ e ∈ range G.M, if uN G e = v ∨ wN G e = v then 1 else 0

/-- The ports of the vertices before `v` (`pre`), by a scan over the vertices. -/
def preC (v : ℕ) : ℕ := ∑ u ∈ range V, if u < v then degC G u else 0

/-- The vertex group of vertex `v` (`vgroup`). -/
def vgroupC (v : ℕ) : ℕ := min (K - 1) (preC G v / blockD G K)

/-- Two pairs of groups are equal as sets. -/
def ClsEq (a b c d : ℕ) : Prop := (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance (a b c d : ℕ) : Decidable (ClsEq a b c d) :=
  inferInstanceAs (Decidable ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))

/-- The position of edge `e` among the edges between the groups of its ends (`edgePos`), by a scan
over the edges before it. -/
def edgePosC (e : ℕ) : ℕ :=
  ∑ e' ∈ range e, if ClsEq (vgroupC G K (uN G e')) (vgroupC G K (wN G e'))
    (vgroupC G K (uN G e)) (vgroupC G K (wN G e)) then 1 else 0

/-- The test group of edge `e` (`tgroup`). -/
def tgroupC (e : ℕ) : ℕ := edgePosC G K e % K

/-- The number of half-edges of edge `e` on the pair (vertex group `i`, test group `τ`). -/
def heCnt (i τ e : ℕ) : ℕ :=
  if tgroupC G K e = τ then
    (if vgroupC G K (uN G e) = i then 1 else 0) + (if vgroupC G K (wN G e) = i then 1 else 0)
  else 0

/-- The width of the pair (vertex group `i`, test group `τ`) (`width`). -/
def widthC (i τ : ℕ) : ℕ := ∑ e ∈ range G.M, heCnt G K i τ e

/-- The position of the half-edge `(e, b)` in `halfEdges i τ`: the half-edges of the earlier
edges, and the `u` end before the `w` end. -/
def hePosC (i τ e : ℕ) (b : Bool) : ℕ :=
  ∑ e' ∈ range e, heCnt G K i τ e' + if b = true ∧ vgroupC G K (uN G e) = i then 1 else 0

variable {G K}

theorem degC_eq (v : Fin V) : degC G v = deg G v := by
  rw [degC, deg, card_filter,
    ← Fin.sum_univ_eq_sum_range (fun e => if uN G e = (v : ℕ) ∨ wN G e = v then 1 else 0)]
  refine sum_congr rfl fun e _ => ?_
  simp only [uN_fin, wN_fin, Fin.val_inj]

theorem preC_eq (v : Fin V) : preC G v = pre G v := by
  rw [preC, pre, ← Fin.sum_univ_eq_sum_range (fun u => if u < (v : ℕ) then degC G u else 0)]
  refine sum_congr rfl fun u _ => ?_
  rw [degC_eq]
  exact if_congr Fin.lt_def.symm rfl rfl

theorem vgroupC_eq (v : Fin V) : vgroupC G K v = vgroup G K v := by
  rw [vgroupC, vgroup, preC_eq]

theorem sum_range_lt (g : ℕ → ℕ) {e n : ℕ} (hen : e ≤ n) :
    ∑ k ∈ range e, g k = ∑ k ∈ range n, if k < e then g k else 0 := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_range, mem_filter]
  omega

theorem edgePosC_eq (e : Fin G.M) : edgePosC G K e = edgePos G K e := by
  rw [edgePosC, sum_range_lt _ e.isLt.le, edgePos, card_filter,
    ← Fin.sum_univ_eq_sum_range (fun k => if k < (e : ℕ) then
      (if ClsEq (vgroupC G K (uN G k)) (vgroupC G K (wN G k))
        (vgroupC G K (uN G e)) (vgroupC G K (wN G e)) then 1 else 0) else 0)]
  refine sum_congr rfl fun k _ => ?_
  simp only [uN_fin, wN_fin, vgroupC_eq]
  rw [ite_and]
  exact if_congr Fin.lt_def.symm (if_congr pair_eq_pair_iff'.symm rfl rfl) rfl

theorem tgroupC_eq (e : Fin G.M) : tgroupC G K e = tgroup G K e := by
  rw [tgroupC, tgroup, edgePosC_eq]

theorem heCnt_fin (i τ : ℕ) (e : Fin G.M) : heCnt G K i τ e = if tgroup G K e = τ then
    (if vgroup G K (G.u e) = i then 1 else 0) + (if vgroup G K (G.w e) = i then 1 else 0)
    else 0 := by
  simp only [heCnt, tgroupC_eq, uN_fin, wN_fin, vgroupC_eq]

theorem widthC_eq (i τ : ℕ) : widthC G K i τ = width G K i τ := by
  rw [width_eq, widthC, ← Fin.sum_univ_eq_sum_range (heCnt G K i τ)]
  exact sum_congr rfl fun e _ => heCnt_fin i τ e

/-! #### The position of a half-edge -/

variable (G K) in
/-- The half-edges of edge number `k` on the pair (vertex group `i`, test group `τ`). -/
def segN (i τ k : ℕ) : List (Fin G.M × Bool) :=
  if h : k < G.M then
    (if tgroup G K ⟨k, h⟩ = τ then
      (if vgroup G K (G.u ⟨k, h⟩) = i then [(⟨k, h⟩, false)] else []) ++
        (if vgroup G K (G.w ⟨k, h⟩) = i then [(⟨k, h⟩, true)] else [])
    else [])
  else []

theorem halfEdges_eq_range (i τ : ℕ) :
    halfEdges G K i τ = (List.range G.M).flatMap (segN G K i τ) := by
  rw [halfEdges, flatMap_filter_eq, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext e
  simp [segN]

theorem length_segN (i τ : ℕ) {k : ℕ} (hk : k < G.M) : (segN G K i τ k).length = heCnt G K i τ
    k := by
  rw [show heCnt G K i τ k = heCnt G K i τ ((⟨k, hk⟩ : Fin G.M) : ℕ) from rfl, heCnt_fin, segN,
    dite_eq_left hk]
  split_ifs <;> simp

theorem length_flatMap_segN (i τ : ℕ) {e : ℕ} (he : e ≤ G.M) :
    ((List.range e).flatMap (segN G K i τ)).length = ∑ k ∈ range e, heCnt G K i τ k := by
  rw [List.length_flatMap, ← listSum_range]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  exact length_segN i τ (by have := List.mem_range.mp hk; omega)

theorem getElem?_halfEdges {i τ : ℕ} (e : Fin G.M) (b : Bool)
    (h : tgroup G K e = τ ∧ vgroup G K (if b then G.w e else G.u e) = i) :
    (halfEdges G K i τ)[hePosC G K i τ e b]? = some (e, b) := by
  obtain ⟨R, hR⟩ := flatMap_range_split (segN G K i τ) e.isLt
  rw [halfEdges_eq_range, hR, hePosC]
  rw [List.getElem?_append_right (by rw [length_flatMap_segN i τ e.isLt.le]; omega),
    length_flatMap_segN i τ e.isLt.le, Nat.add_sub_cancel_left]
  have hseg : segN G K i τ e = (if vgroup G K (G.u e) = i then [(e, false)] else []) ++
      (if vgroup G K (G.w e) = i then [(e, true)] else []) := by
    rw [segN, dite_eq_left e.isLt, ite_eq_left h.1]
  rw [hseg, uN_fin, vgroupC_eq]
  obtain ⟨h1, h2⟩ := h
  cases b
  · simp only [Bool.false_eq_true, ite_false] at h2
    simp [h2]
  · simp only [ite_true] at h2
    by_cases hu : vgroup G K (G.u e) = i
    · simp [hu, h2]
    · simp [hu, h2]

/-- **The bit of a half-edge** is the bit at position `hePosC` of the string. -/
theorem heBit_eq_hePosC (l : Label) {i τ : ℕ} (e : Fin G.M) (b : Bool)
    (h : tgroup G K e = τ ∧ vgroup G K (if b then G.w e else G.u e) = i) :
    heBit G K l i τ (e, b) = decEnc l (hePosC G K i τ e b) := by
  obtain ⟨hn, hx⟩ := List.getElem?_eq_some_iff.mp (getElem?_halfEdges e b h)
  rw [← hx, heBit_getElem _ _ _ _ hn]

end Counts

/-! ### Labels from their codes -/

section Labels

/-- The label coded by `c` at budget `a` (the empty label if `c` is not a code). -/
def labOf (a c : ℕ) : Label :=
  match decodeLabel a c with
  | some l => l
  | none => (0, 0)

/-- Bit `p` of the string encoded by the label coded by `c` (`decEnc`), read from the code. -/
def decBitC (a c p : ℕ) : Bool :=
  decide (validN a (codeWidth a) c = 1 ∧ 0 < countN (codeWidth a) c 0 p)

/-- The encoding test `IsEnc b` of the label coded by `c`, read from the code: every type below `b`
occurs once in the two multisets together, and there are `b` requests. -/
def IsEncC (a b c : ℕ) : Prop :=
  if validN a (codeWidth a) c = 1 then
    (∀ p < b, countN (codeWidth a) c 0 p + countN (codeWidth a) c (msEnd (codeWidth a) c 0) p = 1) ∧
      cardN (codeWidth a) c 0 + cardN (codeWidth a) c (msEnd (codeWidth a) c 0) = b
  else b = 0

instance (a b c : ℕ) : Decidable (IsEncC a b c) := by unfold IsEncC; infer_instance

theorem countN_zero_fuel (c q y : ℕ) : countN 0 c q y = 0 := by
  simp [countN, msFoldN, msN]

theorem cardN_zero_fuel (c q : ℕ) : cardN 0 c q = 0 := by
  simp [cardN, msN]

theorem isEnc_iff_count (s t : Multiset ℕ) (b : ℕ) :
    s + t = ↑(List.range b) ↔
      (∀ p < b, s.count p + t.count p = 1) ∧ Multiset.card s + Multiset.card t = b := by
  rw [Multiset.coe_range]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [← Multiset.count_add, h]
      exact Multiset.count_eq_one_of_mem (Multiset.nodup_range b) (Multiset.mem_range.mpr hp)
    · rw [← Multiset.card_add, h, Multiset.card_range]
  · rintro ⟨hc, hcard⟩
    symm
    refine Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.mpr fun p => ?_) ?_
    · by_cases hp : p < b
      · rw [Multiset.count_eq_one_of_mem (Multiset.nodup_range b) (Multiset.mem_range.mpr hp),
          Multiset.count_add, hc p hp]
      · rw [Multiset.count_eq_zero_of_notMem (fun h => hp (Multiset.mem_range.mp h))]
        exact Nat.zero_le _
    · rw [Multiset.card_add, Multiset.card_range]; omega

/-- The two multiset codes of the label coded by `c`. -/
theorem bitsAt_of_decode {a c : ℕ} {l : Label} (hc : c < 2 ^ codeWidth a) (ha : a ≠ 0)
    (hd : decodeLabel a c = some l) :
    BitsAt c 0 (msCode l.1) ∧ BitsAt c (msEnd (codeWidth a) c 0) (msCode l.2) ∧
      (msCode l.1).length ≤ codeWidth a ∧ (msCode l.2).length ≤ codeWidth a := by
  obtain ⟨hwt, hcode⟩ := labelCode_decode hc hd
  have hb := bitsAt_labelCode ha l
  rw [hcode, bitsAt_append, Nat.zero_add] at hb
  have hlen := msCode_length_le (Nat.one_le_iff_ne_zero.mpr ha) l hwt
  have he := (msParse_msCode hb.1 (B := codeWidth a) (by omega)).2.1
  rw [Nat.zero_add] at he
  rw [he]
  exact ⟨hb.1, hb.2, by omega, by omega⟩

theorem labOf_zero_budget {c : ℕ} (hc : c < 2 ^ codeWidth 0) : labOf 0 c = (0, 0) := by
  simp only [codeWidth, ↓reduceIte, pow_zero, Nat.lt_one_iff] at hc
  subst hc
  simp [labOf, decodeLabel]

theorem decEnc_labOf {a c : ℕ} (hc : c < 2 ^ codeWidth a) (p : ℕ) :
    decEnc (labOf a c) p = decBitC a c p := by
  have hv := validN_eq hc
  by_cases ha : a = 0
  · subst ha
    rw [labOf_zero_budget hc]
    simp [decEnc, decBitC, codeWidth, countN_zero_fuel]
  rcases hd : decodeLabel a c with _ | l
  · rw [hd] at hv
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hv
    simp [labOf, hd, decEnc, decBitC, hv]
  · rw [hd] at hv
    simp only [Option.isSome_some, ite_true] at hv
    obtain ⟨h1, -, l1, -⟩ := bitsAt_of_decode hc ha hd
    rw [decBitC, hv, countN_msCode h1 l1]
    simp [labOf, hd, decEnc, Multiset.count_pos]

theorem isEnc_labOf_iff {a c : ℕ} (hc : c < 2 ^ codeWidth a) (b : ℕ) :
    IsEnc b (labOf a c) ↔ IsEncC a b c := by
  have hv := validN_eq hc
  unfold IsEnc
  by_cases ha : a = 0
  · subst ha
    have hc0 : c = 0 := by simpa [codeWidth] using hc
    subst hc0
    rw [labOf_zero_budget hc, isEnc_iff_count, IsEncC, ite_eq_left (by simp [validN])]
    simp only [codeWidth, ↓reduceIte, countN_zero_fuel, cardN_zero_fuel, Multiset.count_zero,
      Multiset.card_zero]
  rcases hd : decodeLabel a c with _ | l
  · rw [hd] at hv
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hv
    rw [IsEncC, ite_eq_right (by omega), labOf, hd, isEnc_iff_count]
    simp only [Multiset.count_zero, Multiset.card_zero]
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h; subst h; exact ⟨fun p hp => absurd hp (Nat.not_lt_zero _), rfl⟩
  · rw [hd] at hv
    simp only [Option.isSome_some, ite_true] at hv
    obtain ⟨h1, h2, l1, l2⟩ := bitsAt_of_decode hc ha hd
    rw [IsEncC, ite_eq_left hv, labOf, hd, isEnc_iff_count]
    simp only [countN_msCode h1 l1, countN_msCode h2 l2, cardN_msCode h1 l1, cardN_msCode h2 l2]

/-- The labels of an argument code, read through the budget array. -/
theorem decodeArgs_eq_labOf {fw : ℕ} (C : Clique) (hC : Fits fw C.a) (v u : Fin C.q) (huv : u ≠ v)
    (args : ℕ) :
    decodeArgs C v args u = labOf (budgetN (arrN C.q fw (extN C.a)) C.q fw v u)
      (args / 2 ^ argOffN (arrN C.q fw (extN C.a)) C.q fw v u %
        2 ^ codeWidth (budgetN (arrN C.q fw (extN C.a)) C.q fw v u)) := by
  rw [budgetN_ext hC (Ne.symm huv), argOffN_eq C hC]
  simp only [decodeArgs, huv, ite_false]
  rfl

end Labels

/-! ### The budget array of the first clique -/

section Budget

variable {V : ℕ} (G : EdgeNet ℤ (Fin V)) (K : ℕ)

/-- Digit `t` of the budget array of the first clique (node pair `(t / 2K, t mod 2K)`): the budget
`b(b+1)/2` of a (vertex group, test group) pair of width `b`, `0` elsewhere. -/
def firstDigit (t : ℕ) : ℕ :=
  if t / (2 * K) < K ∧ K ≤ t % (2 * K) then
    widthC G K (t / (2 * K)) (t % (2 * K) - K) * (widthC G K (t / (2 * K)) (t % (2 * K) - K) + 1) /
        2
  else 0

theorem firstDigit_eq {t : ℕ} (ht : t < 2 * K * (2 * K)) :
    (if t / (2 * K) < t % (2 * K) then extN (firstBudget G K) (t / (2 * K)) (t % (2 * K)) else 0) =
      firstDigit G K t := by
  have hq : 0 < 2 * K := by
    rcases Nat.eq_zero_or_pos (2 * K) with h0 | h0
    · simp [h0] at ht
    · exact h0
  have hd := (Nat.div_lt_iff_lt_mul hq).mpr ht
  have hm := Nat.mod_lt t hq
  rw [firstDigit, extN, dite_eq_left ⟨hd, hm⟩, firstBudget]
  simp only [widthC_eq]
  generalize t / (2 * K) = x at *
  generalize t % (2 * K) = y at *
  split_ifs <;> first | rfl | omega

/-- **The budget array of the first clique**, digit by digit. -/
theorem arrN_firstBudget (fw : ℕ) :
    arrN (2 * K) fw (extN (firstBudget G K)) = packN fw (2 * K * (2 * K)) (firstDigit G K) := by
  unfold arrN packN
  refine sum_congr rfl fun t ht => ?_
  congr 1
  exact firstDigit_eq G K (mem_range.mp ht)

/-- The digits of the budget array fit in the field width when the budgets do. -/
theorem firstDigit_lt {fw : ℕ} (hC : Fits fw (firstBudget G K)) {t : ℕ}
    (ht : t < 2 * K * (2 * K)) : firstDigit G K t < 2 ^ fw := by
  rw [← firstDigit_eq G K ht]
  exact arrN_digits_lt hC.arr t ht

end Budget

/-! ### The leaf factors of the first clique -/

section Leaf

variable {V : ℕ} (G : EdgeNet ℤ (Fin V)) (K ar fw v args : ℕ)

/-- The budget of the pair `{v, n}`, read from the array. -/
def budAt (n : ℕ) : ℕ := budgetN ar (2 * K) fw v n

/-- The code of the label to node `n` in the argument code `args` of node `v`. -/
def slotN (n : ℕ) : ℕ :=
  args / 2 ^ argOffN ar (2 * K) fw v n % 2 ^ codeWidth (budAt K ar fw v n)

/-- The bit `p` of the string of the label to node `n`. -/
def bitAt (n p : ℕ) : Bool := decBitC (budAt K ar fw v n) (slotN K ar fw v args n) p

/-- The bit carried by port `j` of vertex `x` (of vertex group `v`) in the label of its test group.
-/
def vbitC (x j : ℕ) : Bool :=
  bitAt K ar fw v args (K + tgroupC G K (portN G x j))
    (hePosC G K v (tgroupC G K (portN G x j)) (portN G x j) (decide (wN G (portN G x j) = x)))

/-- The number whose bit `j` is the bit carried by port `j` of vertex `x`. -/
def argA (x : ℕ) : ℕ := ∑ j ∈ range (degN G x), (vbitC G K ar fw v args x j).toNat * 2 ^ j

/-- The bit of the half-edge `(e, b)` of an edge of test group `v - K`, from the label of the
vertex group `i` of that end. -/
def tbitC (e : ℕ) (b : Bool) : Bool :=
  bitAt K ar fw v args (vgroupC G K (if b then wN G e else uN G e))
    (hePosC G K (vgroupC G K (if b then wN G e else uN G e)) (v - K) e b)

/-- **The leaf factor `f` of the entry of node `v`** of the first clique at the argument code
`args`, as a number: the encoding test (`f = 0`), then the vertices (`v < K`) or the edges. -/
def factor0C (f : ℕ) : ℕ :=
  if f = 0 then
    if v < K then
      (if ∀ τ < K, IsEncC (budAt K ar fw v (K + τ)) (widthC G K v τ) (slotN K ar fw v args (K + τ))
        then 1 else 0)
    else
      (if ∀ j < K, IsEncC (budAt K ar fw v j) (widthC G K j (v - K)) (slotN K ar fw v args j)
        then 1 else 0)
  else if v < K then
    if f - 1 < V then
      (if vgroupC G K (f - 1) = v then evalN G (f - 1) (argA G K ar fw v args (f - 1)) else 1)
    else 1
  else if f - 1 < G.M then
    (if tgroupC G K (f - 1) = v - K then
      (if tbitC G K ar fw v args (f - 1) false = tbitC G K ar fw v args (f - 1) true then 1 else 0)
    else 1)
  else 1

variable {G K ar fw v args}

theorem slotN_lt (n : ℕ) : slotN K ar fw v args n < 2 ^ codeWidth (budAt K ar fw v n) :=
  Nat.mod_lt _ (by positivity)

/-- The labels of the entry of node `v < 2K` at `args`, at every node `n ≠ v`. -/
theorem labelOfNode_factor0 (S : Setup) (hC : Fits S.fw S.C₀.a) {v : ℕ} (hv : v < 2 * S.K)
    (args : ℕ) {n : ℕ} (hn : n < 2 * S.K) (hnv : n ≠ v) :
    labelOfNode S.K (fun u : Fin (2 * S.K) =>
        if h : v < S.C₀.q then decodeArgs S.C₀ ⟨v, h⟩ args ⟨u.val, by simp [Setup.C₀, firstClique]⟩
        else (0, 0)) n =
      labOf (budAt S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v n)
        (slotN S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args n) := by
  rw [labelOfNode, dite_eq_left hn]
  have hv' : v < S.C₀.q := hv
  simp only [dite_eq_left hv']
  exact decodeArgs_eq_labOf (fw := S.fw) S.C₀ hC ⟨v, hv'⟩ ⟨n, hn⟩
      (fun h => hnv (congrArg Fin.val h))
    args

theorem testBit_ofFn_argA {x : Fin V} (g : Fin G.M → Bool)
    (hg : ∀ j (hj : j < (G.ports x).length), vbitC G K ar fw v args x j = g ((G.ports x)[j])) :
    (List.ofFn fun j : Fin (G.ports x).length => (argA G K ar fw v args x).testBit j) =
      (G.ports x).map g := by
  have hA : argA G K ar fw v args x = ofBits ((G.ports x).map g) := by
    rw [argA, ofBits_eq_sum, List.length_map, degN_fin]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [hg j hj']
    simp [List.getD_eq_getElem?_getD, hj']
  rw [hA]
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  rw [List.getElem_ofFn, testBit_ofBits, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- **The leaf factors of the first clique.** For a network with nonnegative vertex functions, a
node `v < 2K` and budgets that fit in the field width `fw` of the array, `factor0C` computes
`Setup.factor0` from the argument code and the budget array. -/
theorem factor0C_eq (S : Setup) (hK : 1 ≤ S.K) (hC : Fits S.fw S.C₀.a) (hnn : EvalNonneg S.G)
    {v : ℕ} (hv : v < 2 * S.K) (args f : ℕ) :
    (factor0C S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args f : ℤ) =
      S.factor0 v args f := by
  have hΘ := fun (n : ℕ) (hn : n < 2 * S.K) (hnv : n ≠ v) =>
    labelOfNode_factor0 S hC hv args hn hnv
  unfold Setup.factor0
  dsimp only
  unfold factor0C
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  by_cases hf : f = 0
  · rw [ite_eq_left hf, ite_eq_left hf]
    by_cases hvK : v < S.K
    · rw [ite_eq_left hvK, ite_eq_left hvK]
      refine if_congr (forall₂_congr fun τ hτ => ?_) rfl rfl
      rw [hΘ (S.K + τ) (by omega) (by omega), isEnc_labOf_iff (slotN_lt _), widthC_eq]
    · rw [ite_eq_right hvK, ite_eq_right hvK]
      refine if_congr (forall₂_congr fun j hj => ?_) rfl rfl
      rw [hΘ j (by omega) (by omega), isEnc_labOf_iff (slotN_lt _), widthC_eq]
  rw [ite_eq_right hf, ite_eq_right hf]
  by_cases hvK : v < S.K
  · rw [ite_eq_left hvK, ite_eq_left hvK]
    by_cases hx : f - 1 < S.V
    · rw [ite_eq_left hx, dite_eq_left hx]
      set x : Fin S.V := ⟨f - 1, hx⟩ with hxdef
      have hgx : vgroupC S.G S.K (f - 1) = vgroup S.G S.K x := vgroupC_eq x
      by_cases hgv : vgroup S.G S.K x = v
      · rw [ite_eq_left (hgx.trans hgv), ite_eq_left hgv]
        obtain ⟨g, hgdef⟩ : ∃ g : Fin S.G.M → Bool, g = fun e => heBit S.G S.K
            (labelOfNode S.K (fun u : Fin (2 * S.K) =>
              if h : v < S.C₀.q then decodeArgs S.C₀ ⟨v, h⟩ args
                  ⟨u.val, by simp [Setup.C₀, firstClique]⟩
              else (0, 0)) (S.K + tgroup S.G S.K e)) v (tgroup S.G S.K e)
                  (e, decide (S.G.w e = x)) :=
          ⟨_, rfl⟩
        have hports : ∀ j (hj : j < (S.G.ports x).length),
            vbitC S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args x j =
              g ((S.G.ports x)[j]) := by
          intro j hj
          rw [hgdef]
          set e := (S.G.ports x)[j] with he
          have hpe : portN S.G x j = (e : ℕ) := portN_fin x hj
          have hmem : e ∈ S.G.ports x := List.getElem_mem hj
          have htg := tgroup_lt hK e
          have hdec : decide ((S.G.w e : ℕ) = (x : ℕ)) = decide (S.G.w e = x) := by
            simp [Fin.ext_iff]
          beta_reduce
          rw [vbitC, hpe, tgroupC_eq, wN_fin, hdec, heBit_eq_hePosC _ e _ ⟨rfl, ?_⟩, bitAt,
            hΘ (S.K + tgroup S.G S.K e) (by omega) (by omega), decEnc_labOf (slotN_lt _)]
          rcases (S.G.hports x e).mp hmem with h | h
          · have hne : S.G.w e ≠ x := h ▸ (S.G.huw e).symm
            simp [hne, h, hgv]
          · simp [h, hgv]
        rw [evalN, dite_eq_left hx]
        change ((S.G.eval x (List.ofFn fun j : Fin (S.G.ports x).length =>
          (argA S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args x).testBit
            j)).toNat : ℤ) = _
        rw [testBit_ofFn_argA g hports, Int.toNat_of_nonneg (hnn x _ (List.length_map _)), hgdef]
      · rw [ite_eq_right (fun h => hgv (hgx.symm.trans h)), ite_eq_right hgv]
    · rw [ite_eq_right hx, dite_eq_right hx]
  · rw [ite_eq_right hvK, ite_eq_right hvK]
    by_cases he : f - 1 < S.G.M
    · rw [ite_eq_left he, dite_eq_left he]
      set e : Fin S.G.M := ⟨f - 1, he⟩ with hedef
      have hte : tgroupC S.G S.K (f - 1) = tgroup S.G S.K e := tgroupC_eq e
      by_cases ht : tgroup S.G S.K e = v - S.K
      · rw [ite_eq_left (hte.trans ht), ite_eq_left ht]
        have hu := vgroup_lt (G := S.G) hK (S.G.u e)
        have hw := vgroup_lt (G := S.G) hK (S.G.w e)
        have h1 : tbitC S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args e
            false =
            heBit S.G S.K (labelOfNode S.K (fun u : Fin (2 * S.K) =>
              if h : v < S.C₀.q then decodeArgs S.C₀ ⟨v, h⟩ args
                  ⟨u.val, by simp [Setup.C₀, firstClique]⟩
              else (0, 0)) (vgroup S.G S.K (S.G.u e))) (vgroup S.G S.K (S.G.u e)) (v - S.K)
            (e, false) := by
          rw [tbitC, heBit_eq_hePosC _ e false
            ⟨ht, (rfl : vgroup S.G S.K (S.G.u e) = vgroup S.G S.K (S.G.u e))⟩, ite_eq_right
                Bool.false_ne_true, uN_fin,
            vgroupC_eq, bitAt, hΘ (vgroup S.G S.K (S.G.u e)) (by omega) (by omega),
            decEnc_labOf (slotN_lt _)]
        have h2 : tbitC S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args e
            true =
            heBit S.G S.K (labelOfNode S.K (fun u : Fin (2 * S.K) =>
              if h : v < S.C₀.q then decodeArgs S.C₀ ⟨v, h⟩ args
                  ⟨u.val, by simp [Setup.C₀, firstClique]⟩
              else (0, 0)) (vgroup S.G S.K (S.G.w e))) (vgroup S.G S.K (S.G.w e)) (v - S.K)
            (e, true) := by
          rw [tbitC, heBit_eq_hePosC _ e true
            ⟨ht, (rfl : vgroup S.G S.K (S.G.w e) = vgroup S.G S.K (S.G.w e))⟩, ite_eq_left
                (rfl : true = true), wN_fin,
            vgroupC_eq, bitAt, hΘ (vgroup S.G S.K (S.G.w e)) (by omega) (by omega),
            decEnc_labOf (slotN_lt _)]
        change (if tbitC S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args e
            false =
          tbitC S.G S.K (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) S.fw v args e true
          then (1 : ℤ) else 0) = _
        rw [h1, h2]
      · rw [ite_eq_right (fun h => ht (hte.symm.trans h)), ite_eq_right ht]
    · rw [ite_eq_right he, dite_eq_right he]

end Leaf

end Cslib.Complexity.NtimeDspace.Cube.Num
