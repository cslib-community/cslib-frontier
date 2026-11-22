/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Codes
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Clique
import Mathlib.Data.List.GetD

/-!
# Label codes read and written as numbers

The programs of Lemma 6.4 cannot decode a label: a multiset of weight `W ≈ F²` has a list of
`≈ F log F` bits. They work on the codes of Lemma 4.1 (`Codes.lean`) as numbers, streaming. This
file gives the arithmetic specifications of the streaming procedures, the functions on `ℕ` that the
program terms of `CodeTerm.lean` compute exactly, and relates them to multisets and labels.

A code is held by a number `c` from bit position `q` on (`BitsAt c q l`). All readers take a
*fuel* `B`, the length of the region they may read: a gamma code with `B` leading zeros, or a
multiset code with more than `B` entries, is not read further.

## Main definitions

* `BitsAt c q l`: `c` holds the bit list `l` from bit `q` on.
* `zeroRun`, `readBits`, `gammaN B c q`: the value and the end of the gamma code at bit `q`.
* `stepC`, `entryAt`, `ctrl`: the streaming parse of the entries of a multiset code; `msN` (the
  number of entries), `entE`, `entM` (the element and the multiplicity of entry `k`), `msEnd`
  (the end of the code), `msReads` (all entries), `msFoldN` (a fold over the entries).
* `entries σ`: the distinct elements of `σ` in increasing order, with their multiplicities.
* Readers: `wtN`, `cardN`, `countN`, `topN` (one more than the largest element), `kthN`, `leN`,
  `labelWtN`, `validN`; `sqrtN`, `codeWidthN`.
* Writers: `topBit`, `gammaNum`, `appendN` (append a gamma code within a width `W`); `msOfCount`
  (the code of the multiset with a given count function); `addN`, `subN` (`σ + τ`, `σ - τ`).

## Main results

* `gammaN_gamma`, `gammaN_sound`: reading a gamma code, and what a read with fewer than `B`
  leading zeros means.
* `msParse_msCode`: on `msCode σ` at bit `q` (followed by anything) with `|msCode σ| ≤ B`, the parse
  reads `entries σ` and ends at `q + |msCode σ|`; `msFoldN_msCode`, `msSum_msCode`.
* `msCode_of_msEnd`: a parse that ends within the fuel (`msEnd B c q ≤ q + B`) read the code of a
  multiset.
* `wtN_msCode`, `cardN_msCode`, `countN_msCode`, `lt_topN_msCode`, `kthN_msCode`, `leN_msCode`;
  `labelWtN_labelCode`, `validN_eq` (`validN a (w(a)) i = 1` iff `decodeLabel a i` is some label),
  `labelWtN_decode`.
* `appendN_ofBits`, `msOfCount_eq`, `addN_msCode`, `subN_msCode`: the writers; `codeWidthN_eq`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

/-! ### Bits at a position -/

/-- `c` holds the bit list `l` from bit `q` on: bit `q + k` of `c` is entry `k` of `l`. -/
def BitsAt (c q : ℕ) (l : List Bool) : Prop := ∀ k < l.length, c.testBit (q + k) = l.getD k false

theorem bitsAt_append {c q : ℕ} {l₁ l₂ : List Bool} :
    BitsAt c q (l₁ ++ l₂) ↔ BitsAt c q l₁ ∧ BitsAt c (q + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [h k (by rw [List.length_append]; omega), List.getD_append _ _ _ _ hk]
    · rw [Nat.add_assoc, h _ (by rw [List.length_append]; omega),
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  · rintro ⟨h1, h2⟩ k hk
    rw [List.length_append] at hk
    by_cases hk1 : k < l₁.length
    · rw [h1 k hk1, List.getD_append _ _ _ _ hk1]
    · have := h2 (k - l₁.length) (by omega)
      rw [show q + l₁.length + (k - l₁.length) = q + k by omega] at this
      rw [this, List.getD_append_right _ _ _ _ (by omega)]

theorem bitsAt_replicate {c q n : ℕ} {b : Bool} :
    BitsAt c q (List.replicate n b) ↔ ∀ j < n, c.testBit (q + j) = b := by
  simp only [BitsAt, List.length_replicate]
  refine forall₂_congr fun j hj => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate]

theorem getD_digits (f : ℕ → Bool) {n j : ℕ} (hj : j < n) :
    ((List.range n).reverse.map f).getD j false = f (n - 1 - j) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]

theorem bitsAt_digits {c q n : ℕ} {f : ℕ → Bool} :
    BitsAt c q ((List.range n).reverse.map f) ↔ ∀ j < n, c.testBit (q + j) = f (n - 1 - j) := by
  simp only [BitsAt, List.length_map, List.length_reverse, List.length_range]
  exact forall₂_congr fun j hj => by rw [getD_digits f hj]

theorem bitsAt_gamma {c q x : ℕ} : BitsAt c q (gamma x) ↔
    (∀ j < Nat.log 2 x, c.testBit (q + j) = false) ∧
      ∀ j < Nat.log 2 x + 1, c.testBit (q + Nat.log 2 x + j) = x.testBit (Nat.log 2 x - j) := by
  rw [gamma, bitsAt_append, bitsAt_replicate, bitsAt_digits, List.length_replicate]
  simp only [Nat.add_sub_cancel]

theorem bitsAt_ofBits (l : List Bool) : BitsAt (ofBits l) 0 l := fun k _ => by
  rw [Nat.zero_add, testBit_ofBits]

theorem bitsAt_toBits (W i : ℕ) : BitsAt i 0 (toBits W i) := by
  intro k hk
  rw [toBits_eq] at hk ⊢
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hk]
  simp

theorem ofBits_append (l m : List Bool) : ofBits (l ++ m) = ofBits l + 2 ^ l.length * ofBits m := by
  induction l with
  | nil => simp [ofBits]
  | cons b l ih =>
    rw [List.cons_append, ofBits, ofBits, Nat.bit_val, Nat.bit_val, ih, List.length_cons, pow_succ]
    ring

theorem eq_ofBits_of_bitsAt {c : ℕ} {l : List Bool} (h : BitsAt c 0 l) (hc : c < 2 ^ l.length) :
    c = ofBits l := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_ofBits]
  by_cases hk : k < l.length
  · simpa using h k hk
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))),
      List.getD_eq_default _ _ (by omega)]

theorem bitsAt_labelCode {a : ℕ} (ha : a ≠ 0) (l : Label) :
    BitsAt (labelCode a l) 0 (msCode l.1 ++ msCode l.2) := by
  simp only [labelCode, ha, ↓reduceIte]; exact bitsAt_ofBits _

/-! ### Reading a gamma code -/

/-- The number of consecutive zero bits of `c` from bit `q` on, at most `B`. -/
def zeroRun (B c q : ℕ) : ℕ :=
  (List.range B).foldl (fun z i => if z = i ∧ c.testBit (q + i) = false then z + 1 else z) 0

theorem zeroRun_succ (B c q : ℕ) : zeroRun (B + 1) c q =
    if zeroRun B c q = B ∧ c.testBit (q + B) = false then zeroRun B c q + 1 else zeroRun B c q := by
  unfold zeroRun; rw [List.range_succ, List.foldl_append]; rfl

theorem zeroRun_spec (B c q : ℕ) : zeroRun B c q ≤ B ∧
    (∀ j < zeroRun B c q, c.testBit (q + j) = false) ∧
    (zeroRun B c q < B → c.testBit (q + zeroRun B c q) = true) := by
  induction B with
  | zero => simp [zeroRun]
  | succ B ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [zeroRun_succ]
    split_ifs with h
    · obtain ⟨hz, hb⟩ := h
      refine ⟨by omega, fun j hj => ?_, fun hj => by omega⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact h2 j hj
      · rw [hj, hz]; exact hb
    · refine ⟨by omega, h2, fun _ => ?_⟩
      by_cases hz : zeroRun B c q = B
      · rw [hz]; simpa [hz] using h
      · exact h3 (by omega)

theorem zeroRun_le (B c q : ℕ) : zeroRun B c q ≤ B := (zeroRun_spec B c q).1

theorem zeroRun_eq {B c q z : ℕ} (hz : z ≤ B) (h0 : ∀ j < z, c.testBit (q + j) = false)
    (h1 : z < B → c.testBit (q + z) = true) : zeroRun B c q = z := by
  obtain ⟨s1, s2, s3⟩ := zeroRun_spec B c q
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := s3 (by omega); rw [h0 _ h] at this; exact Bool.false_ne_true this
  · have := h1 (by omega); rw [s2 _ h] at this; exact Bool.false_ne_true this

/-- `n` bits of `c` from bit `q` on, the first one the most significant. -/
def readBits (c q n : ℕ) : ℕ := (List.range n).foldl (fun a j => 2 * a + (c.testBit (q + j)).toNat)
    0

theorem readBits_succ (c q n : ℕ) :
    readBits c q (n + 1) = 2 * readBits c q n + (c.testBit (q + n)).toNat := by
  simp only [readBits, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem readBits_lt (c q n : ℕ) : readBits c q n < 2 ^ n := by
  induction n with
  | zero => simp [readBits]
  | succ n
      ih => rw [readBits_succ, pow_succ]; cases c.testBit (q + n) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem testBit_readBits (c q n i : ℕ) :
    (readBits c q n).testBit i = (decide (i < n) && c.testBit (q + (n - 1 - i))) := by
  induction n generalizing i with
  | zero => simp [readBits]
  | succ n ih =>
    rw [readBits_succ, ← Nat.bit_val]
    cases i with
    | zero => simp
    | succ i =>
      rw [Nat.testBit_bit_succ, ih, show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
      simp

theorem readBits_eq {c q n x : ℕ} (h : ∀ j < n, c.testBit (q + j) = x.testBit (n - 1 - j)) :
    readBits c q n = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_readBits, Nat.testBit_mod_two_pow]
  by_cases hi : i < n
  · simp only [hi, decide_true, Bool.true_and]
    rw [h _ (by omega), show n - 1 - (n - 1 - i) = i by omega]
  · simp [hi]

/-- **Reading a gamma code** at bit `q` of `c`, with at most `B` leading zeros: the value and the
end position. -/
def gammaN (B c q : ℕ) : ℕ × ℕ :=
  (readBits c (q + zeroRun B c q) (zeroRun B c q + 1), q + 2 * zeroRun B c q + 1)

theorem gammaN_snd (B c q : ℕ) : (gammaN B c q).2 = q + 2 * zeroRun B c q + 1 := rfl

theorem gammaN_fst_lt (B c q : ℕ) : (gammaN B c q).1 < 2 ^ (B + 1) :=
  (readBits_lt _ _ _).trans_le (Nat.pow_le_pow_right (by norm_num)
      (by have := zeroRun_le B c q; omega))

theorem gammaN_snd_le (B c q : ℕ) : (gammaN B c q).2 ≤ q + 2 * B + 1 := by
  rw [gammaN_snd]; have := zeroRun_le B c q; omega

/-- A failed read (`B` leading zeros) ends `2B + 1` bits on. -/
theorem gammaN_snd_of_not_lt {B c q : ℕ} (h : ¬ zeroRun B c q < B) :
    (gammaN B c q).2 = q + 2 * B + 1 := by
  rw [gammaN_snd]; have := zeroRun_le B c q; omega

private theorem testBit_log {x : ℕ} (hx : 1 ≤ x) : x.testBit (Nat.log 2 x) = true := by
  obtain ⟨z, hz⟩ : ∃ z, Nat.log 2 x = z := ⟨_, rfl⟩
  have hlo : 2 ^ z ≤ x := hz ▸ Nat.pow_log_le_self 2 (by omega)
  have hhi : x < 2 ^ (z + 1) := hz ▸ Nat.lt_pow_succ_log_self (by norm_num) x
  rw [hz]
  have e : x = 2 ^ z + (x - 2 ^ z) := by omega
  rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by rw [pow_succ] at hhi; omega)]
  rfl

theorem gammaN_gamma {B c q x : ℕ} (hx : 1 ≤ x) (hB : Nat.log 2 x < B) (h : BitsAt c q (gamma x)) :
    gammaN B c q = (x, q + (gamma x).length) := by
  obtain ⟨h0, h1⟩ := bitsAt_gamma.mp h
  have hz : zeroRun B c q = Nat.log 2 x :=
    zeroRun_eq hB.le h0 (fun _ => by simpa [testBit_log hx] using h1 0 (by omega))
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  rw [gammaN, hz, length_gamma, readBits_eq (x := x)
      (fun j hj => by rw [h1 j hj, Nat.add_sub_cancel]),
    Nat.mod_eq_of_lt hlt]
  simp only [Prod.mk.injEq, true_and]
  omega

theorem gammaN_gamma_of_length {B c q x : ℕ} (hx : 1 ≤ x) (hB : (gamma x).length ≤ B)
    (h : BitsAt c q (gamma x)) : gammaN B c q = (x, q + (gamma x).length) :=
  gammaN_gamma hx (by rw [length_gamma] at hB; omega) h

/-- A read with fewer than `B` leading zeros reads a gamma code. -/
theorem gammaN_sound {B c q : ℕ} (hz : zeroRun B c q < B) :
    1 ≤ (gammaN B c q).1 ∧ BitsAt c q (gamma (gammaN B c q).1) ∧
      (gammaN B c q).2 = q + (gamma (gammaN B c q).1).length := by
  obtain ⟨-, s2, s3⟩ := zeroRun_spec B c q
  obtain ⟨z, hzd⟩ : ∃ z, zeroRun B c q = z := ⟨_, rfl⟩
  rw [hzd] at s2 s3 hz
  have hv : (gammaN B c q).1 = readBits c (q + z) (z + 1) := by rw [gammaN, hzd]
  obtain ⟨v, hvd⟩ : ∃ v, readBits c (q + z) (z + 1) = v := ⟨_, rfl⟩
  rw [hvd] at hv
  have hvz : v.testBit z = true := by
    rw [← hvd, testBit_readBits]; simpa using s3 hz
  have hvlt : v < 2 ^ (z + 1) := hvd ▸ readBits_lt _ _ _
  have hvge : 2 ^ z ≤ v := Nat.ge_two_pow_of_testBit hvz
  have hlog : Nat.log 2 v = z :=
    (Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)).mpr ⟨hvge, hvlt⟩
  rw [hv]
  refine ⟨le_trans Nat.one_le_two_pow hvge, ?_, ?_⟩
  · rw [bitsAt_gamma, hlog]
    refine ⟨s2, fun j hj => ?_⟩
    rw [← hvd, testBit_readBits, show z + 1 - 1 - (z - j) = j by omega]
    simp [show z - j < z + 1 by omega]
  · rw [gammaN_snd, hzd, length_gamma, hlog]; omega

/-! ### Streaming over the entries of a multiset code -/

/-- The codes of the entries `(x, μ)` (a weight and a multiplicity) of a multiset code, the weights
counted from `p`: the gamma codes of the gap `x - p` and of `μ`. -/
def entCode : ℕ → List (ℕ × ℕ) → List Bool
  | _, [] => []
  | p, e :: es => gamma (e.1 - p) ++ gamma e.2 ++ entCode e.1 es

/-- One entry, from a state (position, weight): the position and the weight after it. -/
def stepC (B c : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  ((gammaN B c (gammaN B c s.1).2).2, s.2 + (gammaN B c s.1).1)

/-- The entry read at a state: its element (the weight minus one) and its multiplicity. -/
def entryAt (B c : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  (s.2 + (gammaN B c s.1).1 - 1, (gammaN B c (gammaN B c s.1).2).1)

theorem stepC_fst_ge (B c : ℕ) (s : ℕ × ℕ) : s.1 + 2 ≤ (stepC B c s).1 := by
  simp only [stepC, gammaN_snd]; omega

theorem iterate_stepC_fst_ge (B c : ℕ) : ∀ (k : ℕ) (s : ℕ × ℕ),
    s.1 + 2 * k ≤ ((stepC B c)^[k] s).1
  | 0, s => by simp
  | k + 1, s => by
    rw [Function.iterate_succ_apply]
    have := iterate_stepC_fst_ge B c k (stepC B c s)
    have := stepC_fst_ge B c s
    omega

theorem length_gamma_pos (x : ℕ) : 1 ≤ (gamma x).length := by rw [length_gamma]; omega

theorem length_entCode_ge : ∀ (p : ℕ) (ys : List (ℕ × ℕ)), 2 * ys.length ≤ (entCode p ys).length
  | _, [] => by simp [entCode]
  | p, e :: es => by
    have := length_entCode_ge e.1 es
    have := length_gamma_pos (e.1 - p)
    have := length_gamma_pos e.2
    simp only [entCode, List.length_append, List.length_cons]
    omega

/-- Reading the entries of a code. -/
theorem iterate_entCode {B c : ℕ} : ∀ (ys : List (ℕ × ℕ)) (q p : ℕ),
    List.Pairwise (· < ·) (p :: ys.map Prod.fst) → (∀ e ∈ ys, 1 ≤ e.2) →
    BitsAt c q (entCode p ys) → (entCode p ys).length ≤ B →
    ((stepC B c)^[ys.length] (q, p)).1 = q + (entCode p ys).length ∧
    ∀ k (hk : k < ys.length), entryAt B c ((stepC B c)^[k] (q, p)) = (ys[k].1 - 1, ys[k].2)
  | [], q, p, _, _, _, _ => by simp [entCode]
  | e :: es, q, p, hp, hμ, hb, hB => by
    obtain ⟨x, μ⟩ := e
    simp only [List.map_cons, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hp
    obtain ⟨⟨hpx, -⟩, hx, hp'⟩ := hp
    have hμ0 : 1 ≤ μ := hμ _ List.mem_cons_self
    have hμ' : ∀ e ∈ es, 1 ≤ e.2 := fun e he => hμ e (List.mem_cons_of_mem _ he)
    simp only [entCode] at hb hB
    rw [List.length_append, List.length_append] at hB
    rw [bitsAt_append, bitsAt_append] at hb
    obtain ⟨⟨hg, hm⟩, hr⟩ := hb
    have e1 := gammaN_gamma_of_length (B := B) (by omega : 1 ≤ x - p) (by omega) hg
    have e2 := gammaN_gamma_of_length (B := B) hμ0 (by omega) hm
    have hstep : stepC B c (q, p) = (q + (gamma (x - p)).length + (gamma μ).length, x) := by
      simp only [stepC, e1, e2, Prod.mk.injEq, true_and]; omega
    have hent : entryAt B c (q, p) = (x - 1, μ) := by
      simp only [entryAt, e1, e2, Prod.mk.injEq, and_true]; omega
    rw [List.length_append, ← Nat.add_assoc] at hr
    obtain ⟨ih1, ih2⟩ := iterate_entCode (B := B) (c := c) es
        (q + (gamma (x - p)).length + (gamma μ).length) x
      (List.pairwise_cons.mpr ⟨hx, hp'⟩) hμ' hr (by omega)
    refine ⟨?_, fun k hk => ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, hstep, ih1]
      simp only [entCode, List.length_append]; omega
    · rcases k with _ | k
      · simpa using hent
      · rw [Function.iterate_succ_apply, hstep, ih2 k (by simpa using hk)]
        simp

/-- A parse that ends within the fuel read entry codes. -/
theorem iterate_sound {B c : ℕ} : ∀ (k q p : ℕ), ((stepC B c)^[k] (q, p)).1 ≤ q + B →
    ∃ ys : List (ℕ × ℕ), ys.length = k ∧ List.Pairwise (· < ·) (p :: ys.map Prod.fst) ∧
      (∀ e ∈ ys, 1 ≤ e.2) ∧ BitsAt c q (entCode p ys) ∧
      ((stepC B c)^[k] (q, p)).1 = q + (entCode p ys).length
  | 0, q, p, _ => ⟨[], rfl, by simp, by simp, by simp [entCode, BitsAt], by simp [entCode]⟩
  | k + 1, q, p, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    have hge := iterate_stepC_fst_ge B c k (stepC B c (q, p))
    -- the two reads succeed
    have hz1 : zeroRun B c q < B := by
      by_contra hz
      have := gammaN_snd_of_not_lt hz
      have : (gammaN B c q).2 + 1 ≤ (stepC B c (q, p)).1 := by simp only [stepC, gammaN_snd]; omega
      omega
    obtain ⟨g1, gb, ge⟩ := gammaN_sound hz1
    have hz2 : zeroRun B c (gammaN B c q).2 < B := by
      by_contra hz
      have := gammaN_snd_of_not_lt hz
      have : (gammaN B c (gammaN B c q).2).2 = (stepC B c (q, p)).1 := rfl
      have := gammaN_snd B c q
      omega
    obtain ⟨m1, mb, me⟩ := gammaN_sound hz2
    obtain ⟨g, hgd⟩ : ∃ g, (gammaN B c q).1 = g := ⟨_, rfl⟩
    obtain ⟨μ, hμd⟩ : ∃ μ, (gammaN B c (gammaN B c q).2).1 = μ := ⟨_, rfl⟩
    rw [hgd] at g1 gb ge
    rw [hμd] at m1 mb me
    rw [ge] at mb me
    have hstep : stepC B c (q, p) = (q + (gamma g).length + (gamma μ).length, p + g) := by
      simp only [stepC, hgd, ge, me]
    rw [hstep] at h hge ⊢
    obtain ⟨ys, hl, hp, hμ, hb, he⟩ := iterate_sound (B := B) (c := c) k
        (q + (gamma g).length + (gamma μ).length) (p + g) (by simp only at hge; omega)
    refine ⟨(p + g, μ) :: ys, by simp [hl], ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun y hy => ?_, hp⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := (List.pairwise_cons.mp hp).1 y hy; omega
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact m1
      · exact hμ e he
    · simp only [entCode, Nat.add_sub_cancel_left]
      rw [bitsAt_append, bitsAt_append, List.length_append, ← Nat.add_assoc]
      exact ⟨⟨gb, mb⟩, hb⟩
    · rw [he]; simp only [entCode, Nat.add_sub_cancel_left, List.length_append]; omega

/-! ### The parse of a multiset code -/

/-- The number of entries of the multiset code at bit `q`, at most `B`. -/
def msN (B c q : ℕ) : ℕ := min ((gammaN B c q).1 - 1) B

/-- The parse state after `k` entries (at most `B`): position and weight. -/
def ctrl (B c q k : ℕ) : ℕ × ℕ := (stepC B c)^[min k B] ((gammaN B c q).2, 0)

/-- The element of entry `k`. -/
def entE (B c q k : ℕ) : ℕ := (entryAt B c (ctrl B c q k)).1

/-- The multiplicity of entry `k`. -/
def entM (B c q k : ℕ) : ℕ := (entryAt B c (ctrl B c q k)).2

/-- The end of the multiset code at bit `q`. -/
def msEnd (B c q : ℕ) : ℕ := (ctrl B c q (msN B c q)).1

/-- The entries read. -/
def msReads (B c q : ℕ) : List (ℕ × ℕ) :=
    (List.range (msN B c q)).map fun k => (entE B c q k, entM B c q k)

/-- **A fold over the entries** of the multiset code at bit `q`, in increasing order. -/
def msFoldN {α : Type*} (G : α → ℕ → ℕ → α) (a : α) (B c q : ℕ) : α :=
  (List.range (msN B c q)).foldl (fun a k => G a (entE B c q k) (entM B c q k)) a

theorem msFoldN_eq {α : Type*} (G : α → ℕ → ℕ → α) (a : α) (B c q : ℕ) :
    msFoldN G a B c q = (msReads B c q).foldl (fun a e => G a e.1 e.2) a := by
  rw [msFoldN, msReads, List.foldl_map]

theorem msN_le (B c q : ℕ) : msN B c q ≤ B := min_le_right _ _

/-- The distinct elements of a multiset in increasing order, with their multiplicities. -/
def entries (σ : Multiset ℕ) : List (ℕ × ℕ) :=
  (σ.toFinset.sort (· ≤ ·)).map fun e => (e, σ.count e)

/-! ### The structure of a multiset code -/

theorem pairwise_sort (s : Finset ℕ) : List.Pairwise (· < ·) (s.sort (· ≤ ·)) :=
  (Finset.sortedLT_sort s).pairwise

theorem distinctWts_eq (σ : Multiset ℕ) : distinctWts σ = (σ.toFinset.sort (· ≤ ·)).map
    (· + 1) := by
  unfold distinctWts
  refine List.SortedLT.eq_of_mem_iff (Finset.sortedLT_sort _) ?_ fun x => ?_
  · exact (List.pairwise_map.mpr ((pairwise_sort _).imp fun h => by omega)).sortedLT
  · simp [Finset.mem_sort]

private theorem flatMap_range_eq (h : ℕ → ℕ) : ∀ (ps : List ℕ) (p : ℕ),
    (List.range ps.length).flatMap (fun ν => gamma (ps.getD ν 0 -
      (if ν = 0 then p else ps.getD (ν - 1) 0)) ++ gamma (h (ps.getD ν 0))) =
      entCode p (ps.map fun x => (x, h x))
  | [], p => by simp [entCode]
  | x :: ps, p => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.map_cons,
      entCode, ← flatMap_range_eq h ps x]
    congr 1
    congr 1
    funext ν
    cases ν <;> simp

/-- The code of `σ`: the gamma code of the number of entries plus one, then the entry codes, the
weights being the elements plus one. -/
theorem msCode_eq_entCode (σ : Multiset ℕ) : msCode σ = gamma ((entries σ).length + 1) ++
    entCode 0 ((entries σ).map fun e => (e.1 + 1, e.2)) := by
  have h := flatMap_range_eq (fun x => σ.count (x - 1)) (distinctWts σ) 0
  rw [msCode, h, distinctWts_eq]
  simp [entries, List.map_map, Function.comp_def]

theorem mem_entries {σ : Multiset ℕ} {e : ℕ × ℕ} : e ∈ entries σ ↔ e.1 ∈ σ ∧ e.2 = σ.count e.1 := by
  obtain ⟨a, b⟩ := e
  simp only [entries, List.mem_map, Finset.mem_sort, Multiset.mem_toFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨hx, rfl⟩
  · rintro ⟨hx, rfl⟩; exact ⟨a, hx, rfl, rfl⟩

theorem entries_keys (σ : Multiset ℕ) : (entries σ).map Prod.fst = σ.toFinset.sort (· ≤ ·) := by
  simp [entries, List.map_map, Function.comp_def]

private theorem wEntries_good (σ : Multiset ℕ) :
    List.Pairwise (· < ·) (0 :: ((entries σ).map fun e => (e.1 + 1, e.2)).map Prod.fst) ∧
      ∀ e ∈ (entries σ).map (fun e => (e.1 + 1, e.2)), 1 ≤ e.2 := by
  refine ⟨?_, fun e he => ?_⟩
  · rw [List.map_map, List.pairwise_cons]
    have hk : (entries σ).map ((fun e : ℕ × ℕ => e.1) ∘ fun e => (e.1 + 1, e.2)) =
        ((entries σ).map Prod.fst).map (· + 1) := by simp [List.map_map, Function.comp_def]
    rw [hk, entries_keys]
    exact ⟨fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; omega,
      List.pairwise_map.mpr ((pairwise_sort _).imp fun h => by omega)⟩
  · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    have := mem_entries.mp he'
    rw [this.2]; exact Multiset.count_pos.mpr this.1

/-! ### Reading a multiset code -/

/-- **The parse of a multiset code**: on the code of `σ` at bit `q`, within the fuel, it reads the
entries of `σ` and ends after the code. -/
theorem msParse_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) : msN B c q = (entries σ).length ∧
      msEnd B c q = q + (msCode σ).length ∧ msReads B c q = entries σ := by
  rw [msCode_eq_entCode] at h hB
  obtain ⟨ys, hys⟩ : ∃ ys, (entries σ).map (fun e => (e.1 + 1, e.2)) = ys := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (entries σ).length = n := ⟨_, rfl⟩
  have hlen : ys.length = n := by rw [← hys, List.length_map, hn]
  have hgood := wEntries_good σ
  rw [hys] at h hB hgood
  rw [hn] at h hB ⊢
  rw [List.length_append] at hB
  rw [bitsAt_append] at h
  have hg := gammaN_gamma_of_length (B := B) (by omega : 1 ≤ n + 1) (by omega) h.1
  have h2n := length_entCode_ge 0 ys
  have hnB : n ≤ B := by omega
  have hN : msN B c q = n := by rw [msN, hg]; show min (n + 1 - 1) B = n; omega
  obtain ⟨it1, it2⟩ := iterate_entCode (B := B) (c := c) ys _ 0 hgood.1 hgood.2 h.2 (by omega)
  refine ⟨hN, ?_, ?_⟩
  · simp only [msEnd, ctrl, hN, Nat.min_eq_left hnB, hg]
    rw [hlen] at it1
    rw [it1, msCode_eq_entCode, hn, hys, List.length_append]; omega
  · apply List.ext_getElem (by simp [msReads, hN, hn])
    intro k hk1 hk2
    have hk : k < n := by simpa [msReads, hN] using hk1
    have e := it2 k (by omega)
    simp only [msReads, List.getElem_map, List.getElem_range, entE, entM, ctrl,
      Nat.min_eq_left (by omega : k ≤ B), hg, e]
    subst hys
    simp

theorem msEnd_ge (B c q : ℕ) : q + 1 ≤ msEnd B c q := by
  have := iterate_stepC_fst_ge B c (min (msN B c q) B) ((gammaN B c q).2, 0)
  have := gammaN_snd B c q
  simp only [msEnd, ctrl]; omega

private theorem count_rep_eq_zero {zs : List (ℕ × ℕ)} {a : ℕ} (h : ∀ e ∈ zs, e.1 ≠ a) :
    (zs.flatMap fun e => List.replicate e.2 e.1).count a = 0 := by
  rw [List.count_eq_zero]
  intro ha
  obtain ⟨e, he, hae⟩ := List.mem_flatMap.mp ha
  exact h e he (List.eq_of_mem_replicate hae).symm

private theorem count_rep : ∀ (zs : List (ℕ × ℕ)), List.Pairwise (· < ·) (zs.map Prod.fst) →
    ∀ e ∈ zs, (zs.flatMap fun e => List.replicate e.2 e.1).count e.1 = e.2
  | [], _, e, he => absurd he (by simp)
  | (x, μ) :: zs, hp, e, he => by
    rw [List.map_cons, List.pairwise_cons] at hp
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp he with rfl | he
    · rw [List.count_replicate_self, count_rep_eq_zero fun e he => by
        have := hp.1 e.1 (List.mem_map_of_mem he); simp only at this; omega]
      simp
    · have hlt := hp.1 e.1 (List.mem_map_of_mem he)
      rw [count_rep zs hp.2 e he, List.count_replicate]
      simp only at hlt
      simp [show ¬ x = e.1 by omega]

/-- A multiset given by its entries. -/
theorem entries_ofList {zs : List (ℕ × ℕ)} (hp : List.Pairwise (· < ·) (zs.map Prod.fst))
    (hμ : ∀ e ∈ zs, 1 ≤ e.2) :
    entries (↑(zs.flatMap fun e => List.replicate e.2 e.1) : Multiset ℕ) = zs := by
  have hnd : (zs.map Prod.fst).Nodup := hp.imp fun h => Nat.ne_of_lt h
  have hfs : (↑(zs.flatMap fun e => List.replicate e.2 e.1) : Multiset ℕ).toFinset =
      (zs.map Prod.fst).toFinset := by
    ext a
    simp only [Multiset.mem_toFinset, Multiset.mem_coe, List.mem_toFinset, List.mem_flatMap,
      List.mem_replicate, List.mem_map]
    constructor
    · rintro ⟨e, he, -, rfl⟩; exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨e, he, by have := hμ e he; omega, rfl⟩
  have hsort : (zs.map Prod.fst).toFinset.sort (· ≤ ·) = zs.map Prod.fst :=
    (List.toFinset_sort _ hnd).mpr (hp.imp le_of_lt)
  rw [entries, hfs, hsort, List.map_map]
  conv_rhs => rw [← List.map_id zs]
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp_apply, Multiset.coe_count, count_rep zs hp e he, id]

/-- **A successful parse reads a code**: a parse that ends within the fuel read the code of a
multiset. -/
theorem msCode_of_msEnd {B c q : ℕ} (h : msEnd B c q ≤ q + B) :
    ∃ σ : Multiset ℕ, BitsAt c q (msCode σ) ∧ (msCode σ).length ≤ B := by
  have hge := iterate_stepC_fst_ge B c (min (msN B c q) B) ((gammaN B c q).2, 0)
  simp only [msEnd, ctrl] at h hge
  have hz : zeroRun B c q < B := by
    by_contra hz; have := gammaN_snd_of_not_lt hz; omega
  obtain ⟨m1, hb, he⟩ := gammaN_sound hz
  obtain ⟨m, hm⟩ : ∃ m, (gammaN B c q).1 = m := ⟨_, rfl⟩
  rw [hm] at m1 hb he
  have hnB : m - 1 ≤ B := by
    by_contra hc
    have hmB : min (msN B c q) B = B := by simp only [msN, hm]; omega
    rw [hmB] at hge h; omega
  have hmin : min (msN B c q) B = m - 1 := by simp only [msN, hm]; omega
  rw [hmin, he] at h
  obtain ⟨ys, hl, hp, hμ, hbs, hend⟩ := iterate_sound (B := B) (c := c) (m - 1)
      (q + (gamma m).length) 0 (by omega)
  rw [List.pairwise_cons] at hp
  have hpos : ∀ e ∈ ys, 1 ≤ e.1 := fun e he => hp.1 e.1 (List.mem_map_of_mem he)
  obtain ⟨zs, hzs⟩ : ∃ zs, ys.map (fun e => (e.1 - 1, e.2)) = zs := ⟨_, rfl⟩
  have hzp : List.Pairwise (· < ·) (zs.map Prod.fst) := by
    rw [← hzs, List.map_map]
    have : ys.map ((fun e : ℕ × ℕ => e.1) ∘ fun e => (e.1 - 1, e.2)) =
        (ys.map Prod.fst).map (· - 1) := by simp [List.map_map, Function.comp_def]
    rw [this, List.pairwise_map]
    exact hp.2.imp_of_mem fun {a b} ha _ hab => by have := hp.1 a ha; omega
  have hzμ : ∀ e ∈ zs, 1 ≤ e.2 := by
    rw [← hzs]; intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.mp he; exact hμ e' he'
  have hent := entries_ofList hzp hzμ
  have hback : zs.map (fun e => (e.1 + 1, e.2)) = ys := by
    rw [← hzs, List.map_map]
    conv_rhs => rw [← List.map_id ys]
    refine List.map_congr_left fun e he => ?_
    have := hpos e he
    exact Prod.ext (show e.1 - 1 + 1 = e.1 by omega) rfl
  refine ⟨↑(zs.flatMap fun e => List.replicate e.2 e.1), ?_, ?_⟩
  · rw [msCode_eq_entCode, hent, hback, bitsAt_append,
      show zs.length + 1 = m by rw [← hzs, List.length_map, hl]; omega]
    exact ⟨hb, hbs⟩
  · rw [msCode_eq_entCode, hent, hback, List.length_append,
      show zs.length + 1 = m by rw [← hzs, List.length_map, hl]; omega]
    omega

/-! ### Folds over the entries -/

theorem msFoldN_msCode {α : Type*} {G : α → ℕ → ℕ → α} {a : α} {B c q : ℕ} {σ : Multiset ℕ}
    (h : BitsAt c q (msCode σ)) (hB : (msCode σ).length ≤ B) :
    msFoldN G a B c q = (entries σ).foldl (fun a e => G a e.1 e.2) a := by
  rw [msFoldN_eq, (msParse_msCode h hB).2.2]

private theorem sum_range_list (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => simp
  | succ n
      ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_entries (σ : Multiset ℕ) (f : ℕ → ℕ → ℕ) :
    ((entries σ).map fun e => f e.1 e.2).sum = ∑ e ∈ σ.toFinset, f e (σ.count e) := by
  rw [entries, List.map_map, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rfl

/-- A sum over the entries. -/
theorem msSum_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (f : ℕ → ℕ → ℕ) :
    ∑ k ∈ Finset.range (msN B c q), f (entE B c q k) (entM B c q k) =
      ∑ e ∈ σ.toFinset, f e (σ.count e) := by
  rw [← sum_range_list, ← sum_entries, ← (msParse_msCode h hB).2.2, msReads, List.map_map]
  rfl

/-- The weight of the multiset code at bit `q`. -/
def wtN (B c q : ℕ) : ℕ := ∑ k ∈ Finset.range (msN B c q), (entE B c q k + 1) * entM B c q k

/-- The cardinality of the multiset code at bit `q`. -/
def cardN (B c q : ℕ) : ℕ := ∑ k ∈ Finset.range (msN B c q), entM B c q k

theorem wtN_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) : wtN B c q = wt σ := by
  rw [wtN, msSum_msCode h hB (fun e μ => (e + 1) * μ), wt, Finset.sum_multiset_map_count]
  simp [mul_comm]

theorem cardN_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) : cardN B c q = Multiset.card σ := by
  rw [cardN, msSum_msCode h hB (fun _ μ => μ), Multiset.toFinset_sum_count_eq]

private theorem foldl_last (y v : ℕ) : ∀ (l : List (ℕ × ℕ)) (a : ℕ), (∀ e ∈ l, e.1 = y → e.2 = v) →
    l.foldl (fun a e => if e.1 = y then e.2 else a) a = if y ∈ l.map Prod.fst then v else a
  | [], a, _ => by simp
  | e :: l, a, h => by
    rw [List.foldl_cons, foldl_last y v l _ fun e' he' => h e' (List.mem_cons_of_mem _ he')]
    by_cases hy : y ∈ l.map Prod.fst
    · simp [hy]
    · by_cases he : e.1 = y
      · simp [hy, he, h e List.mem_cons_self he]
      · simp [hy, he, Ne.symm he]

/-- The multiplicity of `y` in the multiset code at bit `q`. -/
def countN (B c q y : ℕ) : ℕ := msFoldN (fun a e μ => if e = y then μ else a) 0 B c q

theorem countN_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (y : ℕ) : countN B c q y = σ.count y := by
  rw [countN, msFoldN_msCode h hB, foldl_last y (σ.count y) _ _ fun e he hey => by
    rw [(mem_entries.mp he).2, hey], entries_keys]
  by_cases hy : y ∈ σ
  · simp [Finset.mem_sort, hy]
  · simp [Finset.mem_sort, hy]

private theorem foldl_max_ge (f : ℕ × ℕ → ℕ) : ∀ (l : List (ℕ × ℕ)) (a : ℕ),
    a ≤ l.foldl (fun a e => max a (f e)) a ∧ ∀ e ∈ l, f e ≤ l.foldl (fun a e => max a (f e)) a
  | [], a => by simp
  | e :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (max a (f e))
    rw [List.foldl_cons]
    refine ⟨le_trans (le_max_left _ _) h1, fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · exact le_trans (le_max_right _ _) h1
    · exact h2 e' he'

/-- One more than the largest element of the multiset code at bit `q` (`0` if it is empty). -/
def topN (B c q : ℕ) : ℕ := msFoldN (fun a e _ => max a (e + 1)) 0 B c q

theorem lt_topN_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) {e : ℕ} (he : e ∈ σ) : e < topN B c q := by
  rw [topN, msFoldN_msCode h hB]
  have := (foldl_max_ge (fun e => e.1 + 1) (entries σ) 0).2 (e, σ.count e)
    (mem_entries.mpr ⟨he, rfl⟩)
  simp only at this; omega

/-- The sorted list of a multiset is read off its entries. -/
theorem sort_eq_flatMap (σ : Multiset ℕ) :
    σ.sort (· ≤ ·) = (entries σ).flatMap fun e => List.replicate e.2 e.1 := by
  have hp : List.Pairwise (· < ·) ((entries σ).map Prod.fst) := by
    rw [entries_keys]; exact pairwise_sort _
  have hcoe : (↑((entries σ).flatMap fun e => List.replicate e.2 e.1) : Multiset ℕ) = σ := by
    ext a
    rw [Multiset.coe_count]
    by_cases ha : a ∈ σ
    · exact count_rep _ hp (a, σ.count a) (mem_entries.mpr ⟨ha, rfl⟩)
    · rw [count_rep_eq_zero fun e he hea => ha (by rw [← hea]; exact (mem_entries.mp he).1),
        Multiset.count_eq_zero_of_notMem ha]
  refine List.Perm.eq_of_sortedLE ((Multiset.pairwise_sort σ (· ≤ ·)).sortedLE) ?_ ?_
  · refine (List.pairwise_flatMap.mpr ⟨fun e
      _ => List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩).sortedLE
    refine (List.pairwise_map.mp hp).imp fun {a b} hab x hx y hy => ?_
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]; exact le_of_lt hab
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, hcoe]

/-- The step of `kthN`: while `s ≤ k`, `s` is the rank still to skip; then `k + 1 + e`. -/
def kthStep (k s e μ : ℕ) : ℕ := if k < s then s else if s < μ then k + 1 + e else s - μ

/-- The `k`-th element (from `0`) of the sorted multiset code at bit `q`, default `d`. -/
def kthN (B c q k d : ℕ) : ℕ :=
  if k < msFoldN (kthStep k) k B c q then msFoldN (kthStep k) k B c q - (k + 1) else d

private theorem foldl_kth_stay (k : ℕ) : ∀ (l : List (ℕ × ℕ)) (s : ℕ), k < s →
    l.foldl (fun a e => kthStep k a e.1 e.2) s = s
  | [], _, _ => rfl
  | e :: l, s, h => by rw [List.foldl_cons, kthStep, if_pos h, foldl_kth_stay k l s h]

private theorem foldl_kth (k : ℕ) : ∀ (l : List (ℕ × ℕ)) (r : ℕ), r ≤ k →
    l.foldl (fun a e => kthStep k a e.1 e.2) r =
      if r < (l.flatMap fun e => List.replicate e.2 e.1).length then
        k + 1 + (l.flatMap fun e => List.replicate e.2 e.1).getD r 0
      else r - (l.flatMap fun e => List.replicate e.2 e.1).length
  | [], r, _ => by simp
  | (x, μ) :: l, r, hr => by
    rw [List.foldl_cons, List.flatMap_cons, List.length_append, List.length_replicate]
    have hs : kthStep k r x μ = if r < μ then k + 1 + x else r - μ := by
      simp [kthStep, show ¬ k < r by omega]
    simp only
    rw [hs]
    by_cases hrμ : r < μ
    · rw [if_pos hrμ, foldl_kth_stay k l _ (by omega), if_pos (by omega),
        List.getD_append _ _ _ _ (by simpa using hrμ), List.getD_eq_getElem _ _
            (by simpa using hrμ)]
      simp
    · rw [if_neg hrμ, foldl_kth k l (r - μ) (by omega),
        List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
        List.length_replicate]
      by_cases h2 : r - μ < (l.flatMap fun e => List.replicate e.2 e.1).length
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]; omega

theorem kthN_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (k d : ℕ) : kthN B c q k d = (σ.sort (· ≤ ·)).getD k d := by
  rw [kthN, msFoldN_msCode h hB, foldl_kth k _ k le_rfl, sort_eq_flatMap]
  by_cases hk : k < ((entries σ).flatMap fun e => List.replicate e.2 e.1).length
  · rw [if_pos hk, if_pos (by omega), List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
    omega
  · rw [if_neg hk, if_neg (by omega), List.getD_eq_default _ _ (by omega)]

private theorem foldl_all (P : ℕ × ℕ → Prop) [DecidablePred P] : ∀ (l : List (ℕ × ℕ)) (a : ℕ),
    l.foldl (fun a e => if P e then a else 0) a = if ∀ e ∈ l, P e then a else 0
  | [], a => by simp
  | e :: l, a => by
    rw [List.foldl_cons, foldl_all P l]
    by_cases he : P e
    · split_ifs with h1 h2 h2
      · rfl
      · exact absurd (List.forall_mem_cons.mpr ⟨he, h1⟩) h2
      · exact absurd (List.forall_mem_cons.mp h2).2 h1
      · rfl
    · have : l.foldl (fun a e => if P e then a else 0) 0 = 0 := by
        rw [foldl_all P l]; simp
      simp [he]

/-- The test `σ ≤ τ` on two multiset codes: `1` or `0`. -/
def leN (B c q c' q' : ℕ) : ℕ := msFoldN (fun a e μ => if μ ≤ countN B c' q' e then a else 0) 1 B c
    q

theorem leN_msCode {B c q c' q' : ℕ} {σ τ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (h' : BitsAt c' q' (msCode τ)) (hB' : (msCode τ).length ≤ B) :
    leN B c q c' q' = if σ ≤ τ then 1 else 0 := by
  rw [leN, msFoldN_msCode h hB,
    foldl_all (fun e => e.2 ≤ countN B c' q' e.1) (entries σ) 1]
  congr 1
  simp only [countN_msCode h' hB', eq_iff_iff, Multiset.le_iff_count]
  constructor
  · intro H a
    by_cases ha : a ∈ σ
    · exact H (a, σ.count a) (mem_entries.mpr ⟨ha, rfl⟩)
    · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
  · intro H e he
    rw [(mem_entries.mp he).2]; exact H e.1

/-! ### Labels -/

/-- The weight of the label whose code is held by `i` from bit `0` on. -/
def labelWtN (B i : ℕ) : ℕ := wtN B i 0 + wtN B i (msEnd B i 0)

theorem labelWtN_labelCode {a B : ℕ} (ha : a ≠ 0) {l : Label} (hl : labelWt l ≤ a)
    (hB : codeWidth a ≤ B) : labelWtN B (labelCode a l) = labelWt l := by
  have hlen := msCode_length_le (by omega) l hl
  have h := bitsAt_labelCode ha l
  rw [bitsAt_append, Nat.zero_add] at h
  rw [labelWtN, wtN_msCode h.1 (by omega), (msParse_msCode h.1 (by omega)).2.1, Nat.zero_add,
    wtN_msCode h.2 (by omega), labelWt]

/-- **The validity test** of an index `i` of `W` bits (`W = w(a)`): `1` if it decodes to a label of
weight at most `a`, else `0`. -/
def validN (a W i : ℕ) : ℕ :=
  if a = 0 then (if i = 0 then 1 else 0) else
    if msEnd W i (msEnd W i 0) ≤ W ∧ i < 2 ^ min (msEnd W i (msEnd W i 0)) W ∧
      wtN W i 0 + wtN W i (msEnd W i 0) ≤ a then 1 else 0

theorem validN_eq {a i : ℕ} (hi : i < 2 ^ codeWidth a) :
    validN a (codeWidth a) i = if (decodeLabel a i).isSome then 1 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [codeWidth, ↓reduceIte, pow_zero, Nat.lt_one_iff] at hi
    subst hi
    simp [validN, decodeLabel]
  set W := codeWidth a with hW
  simp only [validN, ha, ↓reduceIte]
  by_cases hd : (decodeLabel a i).isSome
  · obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨hwt, hcode⟩ := labelCode_decode hi hl
    have hlen := msCode_length_le (by omega) l hwt
    have h := bitsAt_labelCode ha l
    rw [hcode] at h
    have hlt : i < 2 ^ (msCode l.1 ++ msCode l.2).length := by
      rw [← hcode, labelCode, if_neg ha]; exact ofBits_lt _
    rw [bitsAt_append, Nat.zero_add] at h
    have p1 := msParse_msCode h.1 (B := W) (by omega)
    have p2 := msParse_msCode h.2 (B := W) (by omega)
    rw [Nat.zero_add] at p1
    rw [p1.2.1, p2.2.1, wtN_msCode h.1 (by omega), wtN_msCode h.2 (by omega), if_pos hd,
      if_pos]
    refine ⟨by omega, by rw [Nat.min_eq_left (by omega), ← List.length_append]; exact hlt, ?_⟩
    have := hwt; unfold labelWt at this; exact this
  · rw [if_neg hd, if_neg]
    rintro ⟨h2, hlt, hwt⟩
    apply hd
    have he1 := msEnd_ge W i (msEnd W i 0)
    obtain ⟨σ₁, b1, l1⟩ := msCode_of_msEnd (B := W) (c := i) (q := 0) (by omega)
    obtain ⟨σ₂, b2, l2⟩ := msCode_of_msEnd (B := W) (c := i) (q := msEnd W i 0) (by omega)
    have p1 := msParse_msCode b1 l1
    have p2 := msParse_msCode b2 l2
    rw [Nat.zero_add] at p1
    rw [p1.2.1] at b2 p2 hwt h2 hlt
    rw [p2.2.1] at h2 hlt
    have hb : BitsAt i 0 (msCode σ₁ ++ msCode σ₂) := bitsAt_append.mpr ⟨b1, by rwa [Nat.zero_add]⟩
    have hi' : i = labelCode a (σ₁, σ₂) := by
      rw [labelCode, if_neg ha]
      refine eq_ofBits_of_bitsAt hb ?_
      rw [List.length_append]; rwa [Nat.min_eq_left h2] at hlt
    rw [wtN_msCode b1 l1, wtN_msCode b2 l2] at hwt
    rw [hi', decode_labelCode (l := (σ₁, σ₂)) (by unfold labelWt; exact hwt)]
    rfl

theorem labelWtN_decode {a i : ℕ} {l : Label} (hi : i < 2 ^ codeWidth a)
    (h : decodeLabel a i = some l) : labelWtN (codeWidth a) i = labelWt l := by
  by_cases ha : a = 0
  · subst ha
    have hl : l = (0, 0) := by
      simp only [decodeLabel, ↓reduceIte] at h
      split_ifs at h
      exact (Option.some.inj h).symm
    have hw : ∀ q, wtN 0 i q = 0 := fun q => by
      simp [wtN, show msN 0 i q = 0 from Nat.le_zero.mp (msN_le 0 i q)]
    subst hl
    simp [labelWtN, codeWidth, hw, labelWt, wt]
  · obtain ⟨hwt, rfl⟩ := labelCode_decode hi h
    exact labelWtN_labelCode ha hwt le_rfl

/-! ### Writing gamma codes -/

/-- The index of the highest one bit of `x` below bit `K` (`0` if there is none). -/
def topBit (K x : ℕ) : ℕ := (List.range K).foldl (fun a j => if x.testBit j then j else a) 0

theorem topBit_eq {K x : ℕ} (hx : x < 2 ^ K) : topBit K x = Nat.log 2 x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · have : ∀ n, (List.range n).foldl (fun a j => if (0 : ℕ).testBit j then j else a) 0 = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp
    rw [topBit, this]; simp
  · have hz : Nat.log 2 x < K := Nat.log_lt_of_lt_pow (by omega) hx
    have htop := testBit_log (by omega : 1 ≤ x)
    have hhi : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
    have key : ∀ n, Nat.log 2 x + 1 ≤ n →
        (List.range n).foldl (fun a j => if x.testBit j then j else a) 0 = Nat.log 2 x := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rw [List.range_succ, List.foldl_append]; simp [htop]
      | succ n hn ih =>
        rw [List.range_succ, List.foldl_append, ih]
        have : x.testBit n = false :=
          Nat.testBit_lt_two_pow (hhi.trans_le (Nat.pow_le_pow_right (by norm_num) hn))
        simp [this]
    exact key K (by omega)

/-- The gamma code of `x` as a number, `x < 2^K`. -/
def gammaNum (K x : ℕ) : ℕ := 2 ^ topBit K x * readBits x 0 (topBit K x + 1)

theorem gammaNum_lt (K x : ℕ) : gammaNum K x < 2 ^ (2 * topBit K x + 1) := by
  rw [gammaNum, show 2 * topBit K x + 1 = topBit K x + (topBit K x + 1) by omega, pow_add]
  exact Nat.mul_lt_mul_of_pos_left (readBits_lt _ _ _) (by positivity)

theorem gammaNum_eq {K x : ℕ} (hx : x < 2 ^ K) : gammaNum K x = ofBits (gamma x) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [gammaNum, topBit_eq hx, testBit_ofBits, mul_comm, Nat.testBit_mul_two_pow, testBit_readBits,
    gamma]
  obtain ⟨z, hz⟩ : ∃ z, Nat.log 2 x = z := ⟨_, rfl⟩
  rw [hz]
  by_cases h1 : k < z
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    simp [show ¬ z ≤ k by omega]
  · by_cases h2 : k < 2 * z + 1
    · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
        List.length_replicate,
        getD_digits _ (by omega)]
      simp [show z ≤ k by omega, show k - z < z + 1 by omega]
    · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_replicate,
        List.length_map, List.length_reverse, List.length_range]; omega)]
      simp [show ¬ k - z < z + 1 by omega]

/-- **Writing a gamma code**: append the gamma code of `x` at bit `q` of the accumulator `acc`, if
it
ends by bit `W`; the new position saturates at `W + 1`. -/
def appendN (W acc q x : ℕ) : ℕ × ℕ :=
  (if q + 2 * topBit W x + 1 ≤ W then acc + 2 ^ q * gammaNum W x else acc,
    min (q + 2 * topBit W x + 1) (W + 1))

theorem appendN_ofBits {W x : ℕ} {l : List Bool} (h : (l ++ gamma x).length ≤ W) :
    appendN W (ofBits l) l.length x = (ofBits (l ++ gamma x), (l ++ gamma x).length) := by
  rw [List.length_append, length_gamma] at h
  have hxW : x < 2 ^ W := (Nat.lt_pow_succ_log_self (by norm_num) x).trans_le
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [appendN, topBit_eq hxW, if_pos (by omega), gammaNum_eq hxW, ofBits_append, List.length_append,
    length_gamma]
  simp only [Prod.mk.injEq, true_and]
  omega

theorem appendN_snd_le (W acc q x : ℕ) : (appendN W acc q x).2 ≤ W + 1 := min_le_right _ _

theorem appendN_lt {W acc q x : ℕ} (h : acc < 2 ^ min q W) :
    (appendN W acc q x).1 < 2 ^ min (appendN W acc q x).2 W := by
  unfold appendN
  have hg := gammaNum_lt W x
  split_ifs with hw
  · rw [show min (min (q + 2 * topBit W x + 1) (W + 1)) W = q + 2 * topBit W x + 1 by omega,
      pow_add, pow_add]
    rw [min_eq_left (by omega)] at h
    have : 2 ^ q * gammaNum W x + 2 ^ q ≤ 2 ^ q * (2 ^ (2 * topBit W x) * 2 ^ 1) := by
      rw [← mul_add_one, ← pow_add]; exact Nat.mul_le_mul_left _ hg
    rw [mul_assoc]; omega
  · exact h.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ### The code of a multiset with given multiplicities -/

/-- The step of `msOfCount` at the candidate element `k`: the state is the code written so far,
its length and the previous weight. -/
def ocStep (W : ℕ) (cnt : ℕ → ℕ) (s : ℕ × ℕ × ℕ) (k : ℕ) : ℕ × ℕ × ℕ :=
  if 0 < cnt k then
    let a := appendN W s.1 s.2.1 (k + 1 - s.2.2)
    let b := appendN W a.1 a.2 (cnt k)
    (b.1, b.2, k + 1)
  else s

/-- The number of `k < X` with `cnt k > 0`. -/
def ocNum (X : ℕ) (cnt : ℕ → ℕ) : ℕ := ∑ k ∈ Finset.range X, if 0 < cnt k then 1 else 0

/-- **The code of the multiset** with multiplicities `cnt k` (`k < X`), written within `W` bits:
the code and its length. -/
def msOfCount (W X : ℕ) (cnt : ℕ → ℕ) : ℕ × ℕ :=
  let h := appendN W 0 0 (ocNum X cnt + 1)
  let s := (List.range X).foldl (ocStep W cnt) (h.1, h.2, 0)
  (s.1, s.2.1)

private theorem ocNum_eq (X : ℕ) (cnt : ℕ → ℕ) :
    ocNum X cnt = ((List.range X).filter (0 < cnt ·)).length := by
  induction X with
  | zero => rfl
  | succ X ih =>
    rw [ocNum, Finset.sum_range_succ, ← ocNum, ih, List.range_succ, List.filter_append,
      List.length_append]
    by_cases h : 0 < cnt X <;> simp [h]

private theorem foldl_ocStep (W : ℕ) (cnt : ℕ → ℕ) : ∀ (ks : List ℕ) (l : List Bool) (p : ℕ),
    (l ++ entCode p ((ks.filter (0 < cnt ·)).map fun k => (k + 1, cnt k))).length ≤ W →
    ((ks.foldl (ocStep W cnt) (ofBits l, l.length, p)).1,
      (ks.foldl (ocStep W cnt) (ofBits l, l.length, p)).2.1) =
      (ofBits (l ++ entCode p ((ks.filter (0 < cnt ·)).map fun k => (k + 1, cnt k))),
        (l ++ entCode p ((ks.filter (0 < cnt ·)).map fun k => (k + 1, cnt k))).length)
  | [], l, p, _ => by simp [entCode]
  | k :: ks, l, p, h => by
    rw [List.foldl_cons]
    by_cases hk : 0 < cnt k
    · rw [List.filter_cons_of_pos (by simpa using hk), List.map_cons, entCode] at h ⊢
      simp only [List.length_append] at h
      have e1 := appendN_ofBits (W := W) (x := k + 1 - p) (l := l)
          (by simp only [List.length_append]; omega)
      have e2 := appendN_ofBits (W := W) (x := cnt k) (l := l ++ gamma (k + 1 - p))
        (by simp only [List.length_append]; omega)
      have hs : ocStep W cnt (ofBits l, l.length, p) k =
          (ofBits (l ++ gamma (k + 1 - p) ++ gamma (cnt k)),
            (l ++ gamma (k + 1 - p) ++ gamma (cnt k)).length, k + 1) := by
        simp only [ocStep, hk, ↓reduceIte, e1, e2]
      rw [hs, foldl_ocStep W cnt ks _ (k + 1) (by simp only [List.length_append]; omega)]
      simp only [List.append_assoc]
    · rw [List.filter_cons_of_neg (by simpa using hk)] at h ⊢
      have hs : ocStep W cnt (ofBits l, l.length, p) k = (ofBits l, l.length, p) := by
        simp [ocStep, hk]
      rw [hs, foldl_ocStep W cnt ks l p h]

theorem entries_of_count {X : ℕ} {cnt : ℕ → ℕ} {ρ : Multiset ℕ} (hc : ∀ k < X, cnt k = ρ.count k)
    (hX : ∀ e ∈ ρ, e < X) :
    entries ρ = ((List.range X).filter (0 < cnt ·)).map fun k => (k, cnt k) := by
  have hnd : ((List.range X).filter (0 < cnt ·)).Nodup := List.nodup_range.filter _
  have hfs : ρ.toFinset = ((List.range X).filter (0 < cnt ·)).toFinset := by
    ext a
    simp only [Multiset.mem_toFinset, List.mem_toFinset, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    constructor
    · intro ha; have := hX a ha; rw [hc a this]; exact ⟨this, Multiset.count_pos.mpr ha⟩
    · rintro ⟨h1, h2⟩; rw [hc a h1] at h2; exact Multiset.count_pos.mp h2
  have hsort : ((List.range X).filter (0 < cnt ·)).toFinset.sort (· ≤ ·) =
      (List.range X).filter (0 < cnt ·) :=
    (List.toFinset_sort _ hnd).mpr ((List.pairwise_lt_range.filter _).imp le_of_lt)
  rw [entries, hfs, hsort]
  refine List.map_congr_left fun k hk => ?_
  have := (List.mem_filter.mp hk).1
  rw [hc k (List.mem_range.mp this)]

theorem msOfCount_eq {W X : ℕ} {cnt : ℕ → ℕ} {ρ : Multiset ℕ} (hc : ∀ k < X, cnt k = ρ.count k)
    (hX : ∀ e ∈ ρ, e < X) (hW : (msCode ρ).length ≤ W) :
    msOfCount W X cnt = (ofBits (msCode ρ), (msCode ρ).length) := by
  have hent := entries_of_count hc hX
  have hm : ocNum X cnt = (entries ρ).length := by rw [ocNum_eq, hent, List.length_map]
  have hcode : msCode ρ = gamma (ocNum X cnt + 1) ++
      entCode 0 (((List.range X).filter (0 < cnt ·)).map fun k => (k + 1, cnt k)) := by
    rw [msCode_eq_entCode, hm, hent, List.map_map]; rfl
  rw [hcode] at hW ⊢
  have hh := appendN_ofBits (W := W) (x := ocNum X cnt + 1) (l := [])
    (by rw [List.nil_append]; rw [List.length_append] at hW; omega)
  simp only [List.nil_append, List.length_nil] at hh
  simp only [msOfCount, show ofBits [] = 0 from rfl] at hh ⊢
  rw [hh]
  exact foldl_ocStep W cnt _ _ 0 hW

/-- The code of `σ + τ` from the codes of `σ` and `τ`, within `W` bits. -/
def addN (B W c q c' q' : ℕ) : ℕ × ℕ :=
  msOfCount W (max (topN B c q) (topN B c' q')) fun k => countN B c q k + countN B c' q' k

/-- The code of `σ - τ` from the codes of `σ` and `τ`, within `W` bits. -/
def subN (B W c q c' q' : ℕ) : ℕ × ℕ :=
  msOfCount W (topN B c q) fun k => countN B c q k - countN B c' q' k

theorem addN_msCode {B W c q c' q' : ℕ} {σ τ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (h' : BitsAt c' q' (msCode τ)) (hB' : (msCode τ).length ≤ B)
    (hW : (msCode (σ + τ)).length ≤ W) :
    addN B W c q c' q' = (ofBits (msCode (σ + τ)), (msCode (σ + τ)).length) := by
  refine msOfCount_eq (fun k _ => ?_) (fun e he => ?_) hW
  · rw [countN_msCode h hB, countN_msCode h' hB', Multiset.count_add]
  · rcases Multiset.mem_add.mp he with he | he
    · exact (lt_topN_msCode h hB he).trans_le (le_max_left _ _)
    · exact (lt_topN_msCode h' hB' he).trans_le (le_max_right _ _)

theorem subN_msCode {B W c q c' q' : ℕ} {σ τ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (h' : BitsAt c' q' (msCode τ)) (hB' : (msCode τ).length ≤ B)
    (hW : (msCode (σ - τ)).length ≤ W) :
    subN B W c q c' q' = (ofBits (msCode (σ - τ)), (msCode (σ - τ)).length) := by
  refine msOfCount_eq (fun k _ => ?_) (fun e he => ?_) hW
  · rw [countN_msCode h hB, countN_msCode h' hB', Multiset.count_sub]
  · exact lt_topN_msCode h hB (Multiset.mem_of_le (Multiset.sub_le_self σ τ) he)

/-! ### The code width -/

/-- `⌊√n⌋` as a count: the number of `k ≤ n` with `(k + 1)² ≤ n`. -/
def sqrtN (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), if (k + 1) * (k + 1) ≤ n then 1 else 0

theorem sqrtN_eq (n : ℕ) : sqrtN n = Nat.sqrt n := by
  rw [sqrtN, ← Finset.card_filter]
  have : (Finset.range (n + 1)).filter (fun k => (k + 1) * (k + 1) ≤ n) = Finset.range
      (Nat.sqrt n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, ← Nat.le_sqrt]
    have := Nat.sqrt_le_self n
    omega
  rw [this, Finset.card_range]

/-- `w(a)` with `sqrtN`. -/
def codeWidthN (a : ℕ) : ℕ := if 0 < a then sqrtN (784 * a) + 2 else 0

theorem codeWidthN_eq (a : ℕ) : codeWidthN a = codeWidth a := by
  rw [codeWidthN, codeWidth, sqrtN_eq]
  by_cases ha : a = 0 <;> simp [ha, Nat.pos_iff_ne_zero]

end Cslib.Complexity.NtimeDspace.Cube.Num
