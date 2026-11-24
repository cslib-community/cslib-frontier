/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Net
public import CslibFrontier.Logics.Propositional.CNF

/-!
# Reading a 3-CNF formula from its encoding

Formulas are CNF formulas `φ : CNF (Fin n)` over the variables `Fin n` (`Cslib.Logic.PL.CNF`),
written by the slot encoding `encSlots`: `1ⁿ 0`, then for every clause three slots of
`⌊log₂ 2n⌋ + 1` bits each, low bit first, slot `j` holding `slot C[j]?` (`0` for no literal,
`2i + 1 + b` for the literal `xᵢ = b`). Clauses with more than three literals are cut to their
first three slots, so the encoding is meant for 3-CNF formulas. An input word is a framed word
`frame x` (which carries the bit index of the query, see `ThreeSatFinal.lean`) followed by
`encSlots φ`.

`rawW w s` reads raw slot data from any word `w`, looking only at its first `(s + 2)^2 + 1`
positions and keeping at most `s` clauses: the length `lenW`, the end `offW` of the leading frame,
the number `nW` of leading ones after it, the slot width `widW`, the number of clauses `mW` and the
slot values `svW`. Every quantity is a short loop or arithmetic over input bits, which is how the
terms of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Terms.lean`
compute them.

## Main definitions

* `slot`, `encSlots`: the slot encoding of 3-CNF formulas.
* `numModels`, `EveryVarOccurs`.
* `lenW`, `offW`, `nW`, `widW`, `mW`, `svW`, `rawW`.

## Main results

* `rawW_enc`: on `frame x ++ encSlots φ` with `φ` a 3-CNF formula, `|w| ≤ (s+2)^2` and at most `s`
  clauses, `rawW` returns `φ.length` clauses and the slot values of `φ`.
* `value_net_enc`: for such a word and `φ` in which every variable occurs, the network of
  `rawW w s` has value `numModels φ`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open Finset NtimeDspace.Cross.TermBlocks Cslib.Logic.PL _root_.Turing.MultiTapeTM

/-! ### The slot encoding -/

/-- A slot of a clause as a number: `0` for no literal, `2i + 1 + b` for the literal `xᵢ = b`. -/
def slot {n : ℕ} : Option (Literal (Fin n)) → ℕ
  | none => 0
  | some l => 2 * l.1.val + 1 + l.2.toNat

/-- The slot encoding of a 3-CNF formula on `n` variables: `1ⁿ 0`, then for every clause three
slots of `⌊log₂ 2n⌋ + 1` bits each, low bit first, slot `j` holding `slot C[j]?`. -/
def encSlots {n : ℕ} (φ : CNF (Fin n)) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit

/-! ### Model counts -/

/-- The number of satisfying assignments of a CNF formula `φ` on `n` variables. -/
def numModels {n : ℕ} (φ : CNF (Fin n)) : ℕ :=
  (univ.filter fun a : Fin n → Bool => ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2).card

/-- Every variable `v < n` occurs in some clause of `φ`. -/
def EveryVarOccurs {n : ℕ} (φ : CNF (Fin n)) : Prop :=
  ∀ v : Fin n, ∃ C ∈ φ, ∃ l ∈ C, l.1 = v

theorem numModels_le {n : ℕ} (φ : CNF (Fin n)) : numModels φ ≤ 2 ^ n := by
  unfold numModels
  calc _ ≤ (univ : Finset (Fin n → Bool)).card := card_filter_le _ _
    _ = 2 ^ n := by simp

/-- For a 3-CNF formula in which every variable occurs, `n ≤ 3m`. -/
theorem n_le_three_mul {n : ℕ} (φ : CNF (Fin n)) (h3 : ∀ C ∈ φ, C.length ≤ 3)
    (hocc : EveryVarOccurs φ) : n ≤ 3 * φ.length := by
  classical
  have hsub : (univ : Finset (Fin n)) ⊆ (φ.flatten.map Prod.fst).toFinset := by
    intro v _
    obtain ⟨C, hC, l, hl, rfl⟩ := hocc v
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨l, List.mem_flatten.mpr ⟨C, hC, hl⟩, rfl⟩
  have h1 := card_le_card hsub
  rw [card_univ, Fintype.card_fin] at h1
  have h2 := List.toFinset_card_le (φ.flatten.map Prod.fst)
  have h3' : (φ.flatten.map Prod.fst).length ≤ 3 * φ.length := by
    rw [List.length_map, List.length_flatten]
    clear hocc hsub h1 h2
    induction φ with
    | nil => simp
    | cons C φ ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := h3 C (by simp)
      have := ih fun C' h' => h3 C' (by simp [h'])
      omega
  omega

/-! ### Reading words -/

/-- The input value at position `i`: `1`, `0`, or `2` past the end. -/
abbrev ib (w : List Bool) (i : ℕ) : ℕ := ProgLang.Prog.inputValue w i

/-- The positions read: `(s + 2)^2 + 1`. -/
def bnd (s : ℕ) : ℕ := (s + 2) ^ 2

/-- The length of `w`, capped at `bnd s + 1`. -/
def lenW (w : List Bool) (s : ℕ) : ℕ :=
  firstNat (bnd s + 1) (fun i => ib w i == 2) (bnd s + 1)

/-- The position after the leading frame. -/
def offW (w : List Bool) (s : ℕ) : ℕ :=
  firstNat (lenW w s) (fun i => i % 2 == 0 && ib w i != 1) (lenW w s) + 1

/-- The number of ones after the leading frame (the number of variables). -/
def nW (w : List Bool) (s : ℕ) : ℕ :=
  firstNat (lenW w s - offW w s) (fun k => ib w (offW w s + k) != 1) (lenW w s - offW w s)

/-- The slot width `⌊log₂ (2n + 1)⌋ + 1 = ⌊log₂ 2n⌋ + 1`. -/
def widW (w : List Bool) (s : ℕ) : ℕ := Nat.log 2 (2 * nW w s + 1) + 1

/-- The number of clauses, at most `s`. -/
def mW (w : List Bool) (s : ℕ) : ℕ :=
  min ((lenW w s - offW w s - nW w s - 1) / (3 * widW w s)) s

/-- The value of slot `t`. -/
def svW (w : List Bool) (s : ℕ) (t : ℕ) : ℕ :=
  bitsNum (widW w s) fun b => ib w (offW w s + nW w s + 1 + t * widW w s + b)

/-- The raw slot data read from `w` at size `s`. -/
def rawW (w : List Bool) (s : ℕ) : Raw := ⟨mW w s, svW w s⟩

theorem mW_le (w : List Bool) (s : ℕ) : mW w s ≤ s := min_le_right _ _

/-! ### Layout of the encoding -/

theorem ib_some {w : List Bool} {i : ℕ} {b : Bool} (h : w[i]? = some b) : ib w i = b.toNat := by
  cases b <;> simp [ib, ProgLang.Prog.inputValue, h]

theorem ib_none {w : List Bool} {i : ℕ} (h : w.length ≤ i) : ib w i = 2 := by
  simp [ib, ProgLang.Prog.inputValue, List.getElem?_eq_none h]

/-- Blocks of a uniform length in a `flatMap`. -/
theorem getElem?_flatMap_uniform {α β : Type} (l : List α) (f : α → List β) (K : ℕ)
    (hK : ∀ a ∈ l, (f a).length = K) (i r : ℕ) (hr : r < K) :
    (l.flatMap f)[i * K + r]? = (l[i]?).bind fun a => (f a)[r]? := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    have ha := hK a (by simp)
    cases i with
    | zero => rw [List.getElem?_append_left (by omega)]; simp
    | succ i =>
      rw [List.getElem?_append_right (by rw [ha]; nlinarith), ha,
        show (i + 1) * K + r - K = i * K + r by rw [Nat.succ_mul]; omega,
        ih (fun a h => hK a (by simp [h])) i]
      simp

/-- The slot width of `encSlots`. -/
abbrev width (n : ℕ) : ℕ := Nat.log2 (2 * n) + 1

theorem log_two_mul_add_one (n : ℕ) : Nat.log 2 (2 * n + 1) = Nat.log2 (2 * n) := by
  rw [Nat.log2_eq_log_two]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine le_antisymm ?_ (Nat.log_mono_right (by omega))
    have h1 := Nat.pow_log_le_self 2 (show 2 * n + 1 ≠ 0 by omega)
    have hk : 1 ≤ Nat.log 2 (2 * n + 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have : 2 ^ Nat.log 2 (2 * n + 1) ≠ 2 * n + 1 := by
      intro h
      have he : 2 ∣ 2 ^ Nat.log 2 (2 * n + 1) := dvd_pow_self 2 (by omega)
      rw [h] at he; omega
    omega

/-- The block of one clause. -/
def clauseBlock (W : ℕ) {n : ℕ} (C : List (Literal (Fin n))) : List Bool :=
  (List.range 3).flatMap fun j => (List.range W).map (slot C[j]?).testBit

theorem enc_eq {n : ℕ} (φ : CNF (Fin n)) :
    encSlots φ = List.replicate n true ++ false :: φ.flatMap (clauseBlock (width n)) := rfl

theorem length_clauseBlock (W : ℕ) {n : ℕ} (C : List (Literal (Fin n))) :
    (clauseBlock W C).length = 3 * W := by
  simp [clauseBlock, List.length_flatMap]; ring

theorem length_enc {n : ℕ} (φ : CNF (Fin n)) : (encSlots φ).length = n + 1 + φ.length *
    (3 * width n) := by
  rw [enc_eq]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_flatMap,
    length_clauseBlock, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem getElem?_enc_slot {n : ℕ} (φ : CNF (Fin n)) {c j b : ℕ} (hc : c < φ.length) (hj : j < 3)
    (hb : b < width n) :
    (encSlots φ)[n + 1 + ((3 * c + j) * width n + b)]? = some ((slot (φ[c])[j]?).testBit b) := by
  rw [enc_eq, List.getElem?_append_right (by simp; omega), List.length_replicate,
    show n + 1 + ((3 * c + j) * width n + b) - n = ((3 * c + j) * width n + b) + 1 by omega,
    List.getElem?_cons_succ,
    show (3 * c + j) * width n + b = c * (3 * width n) + (j * width n + b) by ring,
    getElem?_flatMap_uniform _ _ _ (fun C _ => length_clauseBlock _ C) _ _ (by nlinarith),
    List.getElem?_eq_getElem hc, Option.bind_some, clauseBlock,
    getElem?_flatMap_uniform _ _ (width n) (fun j _ => by simp) _ _ hb]
  simp [hj, hb]

theorem slot_lt {n : ℕ} (o : Option (Literal (Fin n))) : slot o < 2 ^ width n := by
  have h : slot o ≤ 2 * n := by
    cases o with
    | none => simp [slot]
    | some l =>
      obtain ⟨i, b⟩ := l
      have := i.2
      cases b <;> simp [slot]; omega
  refine h.trans_lt ?_
  rw [width, Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by norm_num) _

/-! ### Decoding -/

section Valid

variable {x : List Bool} {n : ℕ} {φ : CNF (Fin n)} {s : ℕ}

theorem lenW_eq {w : List Bool} (hw : w.length ≤ bnd s) : lenW w s = w.length := by
  rw [lenW, firstNat_eq_iff _ _ _ (by omega)]
  refine ⟨by simp [ib_none le_rfl], fun i hi => ?_⟩
  rw [ib_some (List.getElem?_eq_getElem hi)]
  cases w[i] <;> simp

theorem getElem?_frame_lt {i : ℕ} (hi : i < 2 * x.length) :
    (frame x)[i]? = some (if i % 2 = 0 then true else x[i / 2]'(by omega)) := by
  rw [List.getElem?_eq_getElem (by simp; omega), getElem_frame, dite_eq_left hi]

theorem offW_eq (hw : (frame x ++ encSlots φ).length ≤ bnd s) :
    offW (frame x ++ encSlots φ) s = 2 * x.length + 1 := by
  rw [offW, lenW_eq hw]
  congr 1
  have hlen : 2 * x.length < (frame x ++ encSlots φ).length := by simp; omega
  rw [firstNat_eq_iff _ _ _ hlen]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [ib_some (b := false)]
    · simp
    · rw [List.getElem?_append_left (by simp), List.getElem?_eq_getElem (by simp),
        getElem_frame, dite_eq_right (by omega)]
  · rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [ib_some (b := true)]
      · simp [h]
      · rw [List.getElem?_append_left (by simp; omega), getElem?_frame_lt hi, ite_eq_left h]
    · simp [h]

theorem getElem?_after (k : ℕ) :
    (frame x ++ encSlots φ)[2 * x.length + 1 + k]? = (encSlots φ)[k]? := by
  rw [List.getElem?_append_right (by simp)]
  simp

theorem nW_eq (hw : (frame x ++ encSlots φ).length ≤ bnd s) : nW (frame x ++ encSlots φ) s = n := by
  rw [nW, offW_eq hw, lenW_eq hw]
  have hlen : (frame x ++ encSlots φ).length - (2 * x.length + 1) = (encSlots φ).length := by simp
  rw [hlen]
  have hn : n < (encSlots φ).length := by rw [length_enc]; omega
  rw [firstNat_eq_iff _ _ _ hn]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [ib_some (b := false)]
    · simp
    · rw [getElem?_after, enc_eq, List.getElem?_append_right (by simp)]
      simp
  · rw [ib_some (b := true)]
    · simp
    · rw [getElem?_after, enc_eq, List.getElem?_append_left (by simp; omega)]
      simp [hi]

theorem widW_eq (hw : (frame x ++ encSlots φ).length ≤ bnd s) : widW (frame x ++ encSlots φ) s =
    width n := by
  rw [widW, nW_eq hw, log_two_mul_add_one]

theorem mW_eq (hw : (frame x ++ encSlots φ).length ≤ bnd s) (hm : φ.length ≤ s) :
    mW (frame x ++ encSlots φ) s = φ.length := by
  rw [mW, widW_eq hw, nW_eq hw, offW_eq hw, lenW_eq hw]
  have : (frame x ++ encSlots φ).length - (2 * x.length + 1) - n - 1 = φ.length *
      (3 * width n) := by
    simp [length_enc]; omega
  rw [this, Nat.mul_div_cancel _ (by positivity)]
  exact min_eq_left hm

theorem svW_eq (hw : (frame x ++ encSlots φ).length ≤ bnd s) {c j : ℕ}
    (hc : c < φ.length) (hj : j < 3) :
    svW (frame x ++ encSlots φ) s (3 * c + j) = slot (φ[c])[j]? := by
  rw [svW, widW_eq hw, nW_eq hw, offW_eq hw]
  conv_rhs => rw [← bitsNum_digits (slot_lt (φ[c])[j]?)]
  refine bitsNum_congr fun b hb => ?_
  rw [show 2 * x.length + 1 + n + 1 + (3 * c + j) * width n + b =
      2 * x.length + 1 + (n + 1 + ((3 * c + j) * width n + b)) by ring,
    ib_some (by rw [getElem?_after, getElem?_enc_slot φ hc hj hb]), Nat.toNat_testBit]

end Valid

/-! ### The network of an encoded formula -/

theorem slot_none_or {n : ℕ} (C : List (Literal (Fin n))) (j : ℕ) :
    (C.length ≤ j ∧ slot C[j]? = 0) ∨
      ∃ h : j < C.length, slot C[j]? = 2 * (C[j]).1.val + 1 + (C[j]).2.toNat := by
  by_cases h : j < C.length
  · right; exact ⟨h, by simp [List.getElem?_eq_getElem h, slot]⟩
  · left; exact ⟨by omega, by simp [List.getElem?_eq_none (by omega : C.length ≤ j), slot]⟩

/-- **The value of the network of an encoded formula.** If `w = frame x ++ encSlots φ` with `φ` a
3-CNF formula in which every variable occurs, `|w| ≤ (s+2)^2` and `φ.length ≤ s`, then the
network of `rawW w s` has value `numModels φ`. -/
theorem value_net_enc (R : Type) [CommRing R] (x : List Bool) {n : ℕ} (φ : CNF (Fin n)) (s : ℕ)
    (h3 : ∀ C ∈ φ, C.length ≤ 3) (hocc : EveryVarOccurs φ)
    (hw : (frame x ++ encSlots φ).length ≤ bnd s) (hm : φ.length ≤ s) :
    ((rawW (frame x ++ encSlots φ) s).net R).value = (numModels φ : R) := by
  obtain ⟨d, hd⟩ : ∃ d, d = rawW (frame x ++ encSlots φ) s := ⟨_, rfl⟩
  rw [← hd]
  have hdm : d.m = φ.length := hd ▸ mW_eq hw hm
  -- slot `t` of `d` is slot `t % 3` of clause `t / 3`
  have hsv : ∀ t (ht : t < 3 * d.m), d.sv t = slot (φ[t / 3]'(by omega))[t % 3]? := fun t ht => by
    have := svW_eq hw (c := t / 3) (j := t % 3) (by omega) (Nat.mod_lt _ (by norm_num))
    rw [show 3 * (t / 3) + t % 3 = t by omega] at this
    have e : d.sv t = svW (frame x ++ encSlots φ) s t := by rw [hd]; rfl
    rw [e]; exact this
  have hlit : ∀ t (ht : t < 3 * d.m), d.pres t = true →
      ∃ h : t % 3 < (φ[t / 3]'(by omega)).length,
        d.var t = ((φ[t / 3]'(by omega))[t % 3]).1.val ∧ d.sign t =
            ((φ[t / 3]'(by omega))[t % 3]).2 := by
    intro t ht hp
    rcases slot_none_or (φ[t / 3]'(by omega)) (t % 3) with ⟨-, h0⟩ | ⟨h, hs⟩
    · simp [Raw.pres, hsv t ht, h0] at hp
    · have hb := Bool.toNat_le ((φ[t / 3]'(by omega))[t % 3]).2
      refine ⟨h, ?_, ?_⟩
      · simp only [Raw.var, hsv t ht, hs]; omega
      · simp only [Raw.sign, hsv t ht, hs]
        cases ((φ[t / 3]'(by omega))[t % 3]).2 <;> simp
  have hpres : ∀ t (ht : t < 3 * d.m), t % 3 < (φ[t / 3]'(by omega)).length → d.pres t = true := by
    intro t ht h
    simp [Raw.pres, hsv t ht, List.getElem?_eq_getElem h, slot]
  rw
      [Raw.value_net R n
      (fun t ht hp => by obtain ⟨_, hv, -⟩ := hlit t ht hp; rw [hv]; exact Fin.isLt _)
    (fun k hk => ?_)]
  · -- the satisfying assignments are the models
    rw [numModels]
    congr 2
    ext a
    simp only [mem_filter, mem_univ, true_and, Raw.SatA, hdm]
    constructor
    · intro h C hC
      obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hC
      obtain ⟨j, hj, hp, hs⟩ := h c hc
      have ht : 3 * c + j < 3 * d.m := by omega
      obtain ⟨hjl, hv, hsg⟩ := hlit _ ht hp
      have e1 : (3 * c + j) / 3 = c := by omega
      have e2 : (3 * c + j) % 3 = j := by omega
      simp only [e1, e2] at hjl hv hsg
      refine ⟨(φ[c])[j], List.getElem_mem _, ?_⟩
      rw [Raw.extA, dite_eq_left (by rw [hv]; exact Fin.isLt _)] at hs
      rw [← hsg, ← hs]
      congr 1; exact Fin.ext hv.symm
    · intro h c hc
      obtain ⟨l, hl, hal⟩ := h (φ[c]) (List.getElem_mem _)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
      have hj3 : j < 3 := lt_of_lt_of_le hj (h3 _ (List.getElem_mem _))
      have ht : 3 * c + j < 3 * d.m := by omega
      have e1 : (3 * c + j) / 3 = c := by omega
      have e2 : (3 * c + j) % 3 = j := by omega
      have hp : d.pres (3 * c + j) = true := hpres _ ht (by simp only [e1, e2]; exact hj)
      obtain ⟨hjl, hv, hsg⟩ := hlit _ ht hp
      simp only [e1, e2] at hjl hv hsg
      refine ⟨j, hj3, hp, ?_⟩
      rw [Raw.extA, dite_eq_left (by rw [hv]; exact Fin.isLt _), hsg, ← hal]
      congr 1; exact Fin.ext hv
  · -- every variable occurs
    obtain ⟨C, hC, l, hl, hlk⟩ := hocc ⟨k, hk⟩
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hC
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have hj3 : j < 3 := lt_of_lt_of_le hj (h3 _ (List.getElem_mem _))
    have ht : 3 * c + j < 3 * d.m := by omega
    have e1 : (3 * c + j) / 3 = c := by omega
    have e2 : (3 * c + j) % 3 = j := by omega
    have hp : d.pres (3 * c + j) = true := hpres _ ht (by simp only [e1, e2]; exact hj)
    obtain ⟨hjl, hv, -⟩ := hlit _ ht hp
    simp only [e1, e2] at hjl hv
    exact ⟨3 * c + j, ht, hp, by rw [hv, hlk]⟩

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
