/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundTr
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.StCode
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.PathTerm
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PathsAux
import Mathlib.Data.List.GetD

/-!
# The transport machine on state codes (Lemma 5.6)

The explicit machine of Lemma 5.6 (appendix of `separating-ntime-from-space.tex`, last paragraph)
follows an address from
the root keeping only the current source interval and the current multiset of targets. This file
gives its steps as plain functions on the codes of the transport states (`Setup.code` of `tr`,
`trm`, `trr`, kinds `7`, `8`, `9`), with the agreement lemmas against `Setup.gen`. Labels are never
decoded: every reader works on the Lemma 4.1 codes inside `lcode x`, `lcode y`, `lcode m` and the
three part codes of `tcode up T`, through the streaming readers of `CodeNum.lean`, with a fuel `B`
bounding the code lengths.

## Main definitions

* Sources: `srcLenN`, `srcPlN`, `srcTyN` (the length of `srcList`, and the place index and type of
  source `k`, from the three source multisets: `x.1`, `y.1` at bit `0` of their codes and the
  message multiset at `msgPos`); `srcWtN` (the weight of the sources `lo ≤ k < hi`).
* Targets: `tWtN` (the weight of `T` from its three part codes); `trWN` (the weight `W(l, T)`).
* Pivot indices: `PartOkN` (a field of `T₁` holds the code of a label `(σ, 0)`), `leCntN` (a
  comparison of a multiset code with a count function), `restCnt`, `pivL1N`, and **`PivOkN`**, the
  test `PivotValid` on codes. `restN`: the code of a part of `T₂ = T - T₁ - {t}`.
* Rules: `ruleZ` (the coefficient `[z^c] R(s, t)` in closed form from `d`, `χ` and the place
  indices) and `ruleN` (its zigzag code from the zigzag code of `c`); `zzSubN`, `zzAddN`, `plOfN`,
  `plIdxN` (integers and places).
* **The steps**: `trTagN`, `trWidthN`, `trLeafN`, and the children `trChildN` (kind `7`, at a pivot
  index), `trmChildN` (kind `8`), `trrChildN` (kind `9`), dispatched by `trChildAllN`.
* `TrFit A B up x y m T`: `1 ≤ A`, `w(A) ≤ B`, the weights of `x, y, m` and `T` total at most `A`,
  and every target has a place of the half-routing. `TrInv A B`: the invariant of the transport
  states (`TrFit` for every multiset of targets, a valid pivot target).

## Main results

* `pivOkN_iff`: `PivOkN` decides `PivotValid`.
* `hRule_coeff`, `ruleN_eq`: the closed form of the rule coefficients.
* `trChildN_code`, `trmChildN_code`, `trrChildN_code`: the child codes.
* `trInv_child`: every child of a state of the invariant is in the invariant, `zero` or a literal.
* **`tr_agree`**: on a state of `TrInv A B`, the kind is `7`, `8` or `9`, and `trTagN`,
  `trWidthN`, `trLeafN` and `trChildAllN B · i` (every `i`) give `kindTag (gen.kind st)`,
  `gen.width st`, `gen.leafVal st` and `code (gen.child st i)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset SumProduct

/-! ### Fuel -/

theorem msCode_length_le_of_wt {A : ℕ} (hA : 1 ≤ A) {σ : Multiset ℕ} (h : wt σ ≤ A) :
    (msCode σ).length ≤ codeWidth A := by
  have := msCode_length_le hA (σ, 0) (by simp [labelWt, h])
  simp only at this
  omega

theorem codeWidth_le_of_le {a b : ℕ} (h : a ≤ b) : codeWidth a ≤ codeWidth b := by
  unfold codeWidth
  split_ifs with ha hb hb
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.add_le_add_right (Nat.sqrt_le_sqrt (by omega)) 2

theorem wt_eq_zero {σ : Multiset ℕ} (h : wt σ = 0) : σ = 0 :=
  Multiset.card_eq_zero.mp (by have := card_le_wt σ; omega)

/-! ### The codes held by labels and targets -/

theorem bitsAt_mcode (σ : Multiset ℕ) : BitsAt (mcode σ) 0 (msCode σ) := by
  unfold mcode; exact bitsAt_ofBits _

theorem bitsAt_lcode_fst (l : Label) : BitsAt (lcode l) 0 (msCode l.1) := by
  unfold lcode; exact (bitsAt_append.mp (bitsAt_ofBits _)).1

theorem bitsAt_lcode_snd (l : Label) : BitsAt (lcode l) (msCode l.1).length (msCode l.2) := by
  unfold lcode
  have := (bitsAt_append.mp (bitsAt_ofBits (msCode l.1 ++ msCode l.2))).2
  rwa [Nat.zero_add] at this

theorem msEnd_lcode_fst {B : ℕ} {l : Label} (h : (msCode l.1).length ≤ B) :
    msEnd B (lcode l) 0 = (msCode l.1).length := by
  have := (msParse_msCode (bitsAt_lcode_fst l) h).2.1; rwa [Nat.zero_add] at this

/-- The multiset of the message whose requests are sources: `m.2` above the cut, `m.1` below. -/
def msgMs (up : Bool) (m : Label) : Multiset ℕ := if up then m.2 else m.1

/-- The bit position of the message sources in the code of the message. -/
def msgPos (B up M : ℕ) : ℕ := if up = 1 then msEnd B M 0 else 0

theorem bitsAt_msg {B : ℕ} (up : Bool) {m : Label} (h : (msCode m.1).length ≤ B) :
    BitsAt (lcode m) (msgPos B up.toNat (lcode m)) (msCode (msgMs up m)) := by
  cases up
  · simpa [msgPos, msgMs] using bitsAt_lcode_fst m
  · simp only [msgPos, msgMs, Bool.toNat_true, ↓reduceIte, msEnd_lcode_fst h]
    exact bitsAt_lcode_snd m

theorem getF_tcode (up : Bool) (T : Multiset (HPlace × ℕ)) {p : ℕ} (hp : p < 3) :
    getF (tcode up T) p = mcode (tpart up T p) := by
  unfold tcode
  rw [getF_enc _ _ (by simpa using hp)]
  interval_cases p <;> rfl

/-! ### Parts of multisets of typed targets -/

theorem count_tpart (up : Bool) (T : Multiset (HPlace × ℕ)) (p e : ℕ) :
    (tpart up T p).count e = T.count (placeOf up p, e) := by
  induction T using Multiset.induction_on with
  | empty => simp [tpart]
  | cons a T ih =>
    unfold tpart at ih ⊢
    rw [Multiset.filter_cons, Multiset.count_cons]
    by_cases h : a.1 = placeOf up p
    · rw [ite_eq_left h, Multiset.map_add, Multiset.map_singleton, Multiset.count_add, ih,
        Multiset.count_singleton]
      have : (e = a.2) ↔ ((placeOf up p, e) = a) := by
        constructor
        · rintro rfl; rw [← h]
        · rintro rfl; rfl
      by_cases he : e = a.2
      · rw [ite_eq_left he, ite_eq_left (this.mp he)]; omega
      · rw [ite_eq_right he, ite_eq_right (fun h' => he (this.mpr h'))]; omega
    · rw [ite_eq_right h, zero_add, ih, ite_eq_right (by rintro rfl; exact h rfl), add_zero]

theorem tpart_zero (up : Bool) (p : ℕ) : tpart up 0 p = 0 := by simp [tpart]

theorem eq_zero_of_tpart {up : Bool} {T : Multiset (HPlace × ℕ)} (hT : ∀ s ∈ T, ValidPl up s.1)
    (h : ∀ p < 3, tpart up T p = 0) : T = 0 := by
  rw [← filter_places T hT]
  have h' : ∀ p < 3, (T.filter fun s => s.1 = placeOf up p) = 0 := fun p hp =>
    Multiset.map_eq_zero.mp (h p hp)
  rw [h' 0 (by omega), h' 1 (by omega), h' 2 (by omega)]; rfl

theorem wt_tpart (up : Bool) (T : Multiset (HPlace × ℕ)) (p : ℕ) :
    wt (tpart up T p) = ((T.filter fun s => s.1 = placeOf up p).map lwt).sum := by
  simp only [wt, tpart, Multiset.map_map]; rfl

theorem sum_lwt_tparts {up : Bool} {T : Multiset (HPlace × ℕ)} (hT : ∀ s ∈ T, ValidPl up s.1) :
    (T.map lwt).sum = wt (tpart up T 0) + wt (tpart up T 1) + wt (tpart up T 2) := by
  conv_lhs => rw [← filter_places T hT]
  simp only [Multiset.map_add, Multiset.sum_add, wt_tpart]

theorem wt_tpart_le (up : Bool) (T : Multiset (HPlace × ℕ)) (p : ℕ) :
    wt (tpart up T p) ≤ (T.map lwt).sum := wt_partOf_le (up := up) T p

/-! ### The sources -/

theorem srcList_eq (up : Bool) (x y m : Label) :
    srcList up x y m = (x.1.sort (· ≤ ·)).map (fun i => (placeOf up 0, i)) ++
      (y.1.sort (· ≤ ·)).map (fun i => (placeOf up 1, i)) ++
        ((msgMs up m).sort (· ≤ ·)).map (fun i => (placeOf up 2, i)) := by
  cases up <;> simp [srcList, placeOf, msgMs]

/-- The number of sources. -/
def srcLenN (B up X Y M : ℕ) : ℕ := cardN B X 0 + cardN B Y 0 + cardN B M (msgPos B up M)

/-- The place index of source `k`. -/
def srcPlN (B X Y k : ℕ) : ℕ :=
  if k < cardN B X 0 then 0 else if k < cardN B X 0 + cardN B Y 0 then 1 else 2

/-- The type of source `k`. -/
def srcTyN (B up X Y M k : ℕ) : ℕ :=
  if k < cardN B X 0 then kthN B X 0 k 0
  else if k < cardN B X 0 + cardN B Y 0 then kthN B Y 0 (k - cardN B X 0) 0
  else kthN B M (msgPos B up M) (k - cardN B X 0 - cardN B Y 0) 0

/-- The codes of the two multisets of a label fit the fuel. -/
def LFits (B : ℕ) (l : Label) : Prop := (msCode l.1).length ≤ B ∧ (msCode l.2).length ≤ B

theorem LFits.of_wt {A B : ℕ} (hA : 1 ≤ A) (hB : codeWidth A ≤ B) {l : Label} (h : labelWt l ≤ A) :
    LFits B l := by
  have := msCode_length_le hA l h
  exact ⟨by omega, by omega⟩

theorem LFits.msg {B : ℕ} {m : Label} (h : LFits B m) (up : Bool) :
    (msCode (msgMs up m)).length ≤ B := by
  cases up
  · exact h.1
  · exact h.2

private theorem getD_map_pair (p : HPlace) (a : List ℕ) {k : ℕ} (hk : k < a.length)
    (t : HPlace × ℕ) : (a.map fun i => (p, i)).getD k t = (p, a.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

section Sources

variable {B : ℕ} (up : Bool) {x y m : Label} (hx : LFits B x) (hy : LFits B y) (hm : LFits B m)
include hx hy hm

theorem srcLenN_eq : srcLenN B up.toNat (lcode x) (lcode y) (lcode m) =
    (srcList up x y m).length := by
  rw [srcLenN, cardN_msCode (bitsAt_lcode_fst x) hx.1, cardN_msCode (bitsAt_lcode_fst y) hy.1,
    cardN_msCode (bitsAt_msg up hm.1) (hm.msg up), srcList_eq]
  simp [Nat.add_assoc]

theorem srcList_getD {k : ℕ} (hk : k < (srcList up x y m).length) (t : HPlace × ℕ) :
    (srcList up x y m).getD k t =
      (placeOf up (srcPlN B (lcode x) (lcode y) k), srcTyN B up.toNat (lcode x) (lcode y)
          (lcode m) k) := by
  have c1 := cardN_msCode (bitsAt_lcode_fst x) hx.1
  have c2 := cardN_msCode (bitsAt_lcode_fst y) hy.1
  have k1 := kthN_msCode (bitsAt_lcode_fst x) hx.1
  have k2 := kthN_msCode (bitsAt_lcode_fst y) hy.1
  have k3 := kthN_msCode (bitsAt_msg up hm.1) (hm.msg up)
  rw [srcList_eq] at hk ⊢
  simp only [List.length_append, List.length_map, Multiset.length_sort] at hk
  simp only [srcPlN, srcTyN, c1, c2, k1, k2, k3]
  by_cases h1 : k < Multiset.card x.1
  · rw [ite_eq_left h1, ite_eq_left h1, List.getD_append _ _ _ _
      (by simp only [List.length_append, List.length_map, Multiset.length_sort]; omega),
      List.getD_append _ _ _ _ (by simpa using h1), getD_map_pair _ _ (by simpa using h1)]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : k < Multiset.card x.1 + Multiset.card y.1
    · rw [ite_eq_left h2, ite_eq_left h2, List.getD_append _ _ _ _
        (by simp only [List.length_append, List.length_map, Multiset.length_sort]; omega),
        List.getD_append_right _ _ _ _
            (by simp only [List.length_map, Multiset.length_sort]; omega), getD_map_pair _ _
            (by simp only [List.length_map, Multiset.length_sort]; omega)]
      simp
    · rw [ite_eq_right h2, ite_eq_right h2, List.getD_append_right _ _ _ _
        (by simp only [List.length_append, List.length_map, Multiset.length_sort]; omega),
        getD_map_pair _ _
            (by simp only [List.length_append, List.length_map, Multiset.length_sort]; omega)]
      simp only [List.length_append, List.length_map, Multiset.length_sort]
      congr 2
      omega

end Sources

theorem srcPlN_lt (B X Y k : ℕ) : srcPlN B X Y k < 3 := by
  unfold srcPlN; split_ifs <;> omega

/-! ### Weights of source intervals and of targets -/

theorem sum_take_drop {α : Type*} (L : List α) (f : α → ℕ) (lo n : ℕ) (t : α) :
    (((L.drop lo).take n).map f).sum =
      ∑ k ∈ range n, if lo + k < L.length then f (L.getD (lo + k) t) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.take_add_one, List.map_append, List.sum_append, ih, sum_range_succ, List.getElem?_drop]
    congr 1
    by_cases h : lo + n < L.length
    · rw [List.getElem?_eq_getElem h, ite_eq_left h, List.getD_eq_getElem _ _ h]; simp
    · rw [List.getElem?_eq_none (by omega), ite_eq_right h]; simp

/-- The weight of the sources `lo ≤ k < hi`. -/
def srcWtN (B up X Y M lo hi : ℕ) : ℕ :=
  ∑ k ∈ range (hi - lo),
    if lo + k < srcLenN B up X Y M then srcTyN B up X Y M (lo + k) + 1 else 0

theorem srcWtN_eq {B : ℕ} (up : Bool) {x y m : Label} (hx : LFits B x) (hy : LFits B y)
    (hm : LFits B m) (lo hi : ℕ) :
    srcWtN B up.toNat (lcode x) (lcode y) (lcode m) lo hi =
        ((srcSub up x y m lo hi).map lwt).sum := by
  rw [srcSub, sum_take_drop _ _ _ _ (none, 0), srcWtN, srcLenN_eq up hx hy hm]
  refine sum_congr rfl fun k _ => ?_
  by_cases h : lo + k < (srcList up x y m).length
  · rw [ite_eq_left h, ite_eq_left h, srcList_getD up hx hy hm h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]

/-- The weight of a multiset of typed targets, from its code. -/
def tWtN (B Tc : ℕ) : ℕ := wtN B (getF Tc 0) 0 + wtN B (getF Tc 1) 0 + wtN B (getF Tc 2) 0

/-- The parts of a multiset of typed targets fit the fuel. -/
def TFits (B : ℕ) (up : Bool) (T : Multiset (HPlace × ℕ)) : Prop :=
  ∀ p < 3, (msCode (tpart up T p)).length ≤ B

theorem TFits.of_wt {A B : ℕ} (hA : 1 ≤ A) (hB : codeWidth A ≤ B) {up : Bool}
    {T : Multiset (HPlace × ℕ)} (h : (T.map lwt).sum ≤ A) : TFits B up T := fun p _ =>
  (msCode_length_le_of_wt hA ((wt_tpart_le up T p).trans h)).trans hB

theorem bitsAt_part (up : Bool) (T : Multiset (HPlace × ℕ)) {p : ℕ} (hp : p < 3) :
    BitsAt (getF (tcode up T) p) 0 (msCode (tpart up T p)) := by
  rw [getF_tcode up T hp]; exact bitsAt_mcode _

theorem tWtN_eq {B : ℕ} {up : Bool} {T : Multiset (HPlace × ℕ)} (hT : ∀ s ∈ T, ValidPl up s.1)
    (hf : TFits B up T) : tWtN B (tcode up T) = (T.map lwt).sum := by
  rw [tWtN, sum_lwt_tparts hT, wtN_msCode (bitsAt_part up T (by omega)) (hf 0 (by omega)),
    wtN_msCode (bitsAt_part up T (by omega)) (hf 1 (by omega)),
    wtN_msCode (bitsAt_part up T (by omega)) (hf 2 (by omega))]

/-- **The weight `W(l, T)`** of a transport state, from the codes of its fields. -/
def trWN (B up X Y M lo hi Tc : ℕ) : ℕ := srcWtN B up X Y M lo hi + tWtN B Tc

theorem trWN_eq {B : ℕ} (up : Bool) {x y m : Label} (hx : LFits B x) (hy : LFits B y)
    (hm : LFits B m) (lo hi : ℕ) {T : Multiset (HPlace × ℕ)} (hT : ∀ s ∈ T, ValidPl up s.1)
    (hf : TFits B up T) :
    trWN B up.toNat (lcode x) (lcode y) (lcode m) lo hi (tcode up T) = tWt
        (srcSub up x y m lo hi) T := by
  rw [trWN, srcWtN_eq up hx hy hm, tWtN_eq hT hf, tWt]


/-! ### Located parts -/

/-- The multiset of typed targets with the parts `σ₀, σ₁, σ₂` at the places `0, 1, 2`. -/
def loc3 (up : Bool) (σ₀ σ₁ σ₂ : Multiset ℕ) : Multiset (HPlace × ℕ) :=
  located (placeOf up 0) σ₀ + located (placeOf up 1) σ₁ + located (placeOf up 2) σ₂

theorem tpart_located_eq (up : Bool) (P : HPlace) (σ : Multiset ℕ) (k : ℕ) :
    tpart up (located P σ) k = if P = placeOf up k then σ else 0 := proj_located _ _ _

theorem tpart_add_eq (up : Bool) (T T' : Multiset (HPlace × ℕ)) (k : ℕ) :
    tpart up (T + T') k = tpart up T k + tpart up T' k := by
  simp [tpart, Multiset.filter_add, Multiset.map_add]

theorem tpart_loc3 (up : Bool) (σ₀ σ₁ σ₂ : Multiset ℕ) {k : ℕ} (hk : k < 3) :
    tpart up (loc3 up σ₀ σ₁ σ₂) k = if k = 0 then σ₀ else if k = 1 then σ₁ else σ₂ := by
  simp only [loc3, tpart_add_eq, tpart_located_eq]
  interval_cases k <;> cases up <;> simp [placeOf]

theorem loc3_valid (up : Bool) (σ₀ σ₁ σ₂ : Multiset ℕ) : ∀ s ∈ loc3 up σ₀ σ₁ σ₂,
    ValidPl up s.1 := by
  intro s hs
  simp only [loc3, located, Multiset.mem_add, Multiset.mem_map] at hs
  rcases hs with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨2, by omega, rfl⟩

theorem sum_lwt_loc3 (up : Bool) (σ₀ σ₁ σ₂ : Multiset ℕ) :
    ((loc3 up σ₀ σ₁ σ₂).map lwt).sum = wt σ₀ + wt σ₁ + wt σ₂ := by
  simp only [loc3, Multiset.map_add, Multiset.sum_add,
    show (lwt : HPlace × ℕ → ℕ) = fun s => s.2 + 1 from rfl, sum_map_located_succ]

/-! ### Fields of pivot codes -/

/-- The multiset of a field of a pivot code: the first multiset of the label it decodes to. -/
def fldMs (W d : ℕ) : Multiset ℕ :=
  match decodeLabel W d with
  | some l => l.1
  | none => 0

/-- The sub-multiset `T₁` of a pivot index. -/
def pivT₁ (up : Bool) (W i : ℕ) : Multiset (HPlace × ℕ) :=
  loc3 up (fldMs W (Radix.dig (pivW W) i 2)) (fldMs W (Radix.dig (pivW W) i 3))
    (fldMs W (Radix.dig (pivW W) i 4))

theorem decodePivot_eq' (up : Bool) (W i : ℕ) : decodePivot up W i =
    (Radix.dig (pivW W) i 0, (placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3),
      pivT₁ up W i, (Radix.dig (pivW W) i 5 : ℤ) - W, (Radix.dig (pivW W) i 6 : ℤ) - W) := by
  rw [decodePivot_eq]
  simp only [pivT₁, loc3, fldMs, Prod.mk.injEq, true_and, and_true]
  cases decodeLabel W (Radix.dig (pivW W) i 2) <;> cases decodeLabel W (Radix.dig (pivW W) i 3) <;>
    cases decodeLabel W (Radix.dig (pivW W) i 4) <;> simp [located]

theorem pivW_part (W : ℕ) {j : ℕ} (h2 : 2 ≤ j) (h4 : j ≤ 4) : pivW W j = codeWidth W := by
  unfold pivW; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h4]

theorem dig_part_lt (W i : ℕ) {j : ℕ} (h2 : 2 ≤ j) (h4 : j ≤ 4) :
    Radix.dig (pivW W) i j < 2 ^ codeWidth W := by
  rw [← pivW_part W h2 h4]; exact Radix.dig_lt _ _ _

theorem labelWt_fldMs {W d : ℕ} (hd : d < 2 ^ codeWidth W) : labelWt (fldMs W d, 0) ≤ W := by
  unfold fldMs
  rcases h : decodeLabel W d with _ | l
  · simp [labelWt]
  · have := (labelCode_decode hd h).1
    simp only [labelWt, wt_zero, add_zero] at this ⊢; omega

/-- **Canonical pivot codes**: a pivot index is the code of its decoded fields if and only if it has
`pivWidth W` bits and each of its three fields of `T₁` is the code of a label `(σ, 0)`. -/
theorem pivCodeX_decode_iff (up : Bool) (W i : ℕ) :
    pivCodeX up W (decodePivot up W i) = i ↔ i < 2 ^ pivWidth W ∧
      ∀ k < 3, labelCode W (fldMs W (Radix.dig (pivW W) i (k + 2)), 0) = Radix.dig (pivW W) i
          (k + 2) := by
  set D := pivDigits up W (decodePivot up W i).1 (decodePivot up W i).2.1 (decodePivot up W i).2.2.1
    (decodePivot up W i).2.2.2.1 (decodePivot up W i).2.2.2.2 with hDdef
  have hcode : pivCodeX up W (decodePivot up W i) = Radix.enc (pivW W) D 7 := by
    rw [pivCodeX, pivotCode_eq]
  have hD : ∀ j < 7, D j = if 2 ≤ j ∧ j ≤ 4 then labelCode W (fldMs W (Radix.dig (pivW W) i j), 0)
      else Radix.dig (pivW W) i j := by
    intro j hj
    rw [hDdef, decodePivot_eq']
    have hp := Nat.mod_lt (Radix.dig (pivW W) i 1) (show 0 < 3 by omega)
    have ep : ∀ T k, partOf up T k = tpart up T k := fun _ _ => rfl
    interval_cases j <;> simp only [pivDigits, ep, pivT₁]
    all_goals first
      | (simp [tpart_loc3]; done)
      | (simp (config := { decide := true }) only [↓reduceIte, placeIdx_placeOf hp]; omega)
  have hb : ∀ j < 7, D j < 2 ^ pivW W j := by
    intro j hj
    rw [hD j hj]
    split_ifs with h
    · rw [pivW_part W h.1 h.2]
      exact labelCode_lt (labelWt_fldMs (dig_part_lt W i h.1 h.2))
    · exact Radix.dig_lt _ _ _
  rw [hcode, pivWidth_eq]
  constructor
  · intro h
    have hlt : i < 2 ^ Radix.off (pivW W) 7 := h ▸ Radix.enc_lt 7 _ _ hb
    refine ⟨hlt, fun k hk => ?_⟩
    have e := Radix.dig_enc 7 _ _ hb (k + 2) (by omega)
    rw [h, hD _ (by omega), ite_eq_left (by omega)] at e
    exact e.symm
  · rintro ⟨hlt, hk⟩
    rw [Radix.enc_congr (d' := Radix.dig (pivW W) i) fun j hj => ?_, Radix.enc_dig 7 _ _ hlt]
    rw [hD j hj]
    split_ifs with h
    · have := hk (j - 2) (by omega)
      rwa [show j - 2 + 2 = j by omega] at this
    · rfl

/-- A field of a pivot code holds a part of `T₁`: it decodes, and the second multiset is empty. -/
def PartOkN (B W d : ℕ) : Prop := validN W (codeWidth W) d = 1 ∧ wtN B d (msEnd B d 0) = 0

instance (B W d : ℕ) : Decidable (PartOkN B W d) := by unfold PartOkN; infer_instance

theorem bitsAt_labelCode_zero {W : ℕ} (hW : W ≠ 0) {σ : Multiset ℕ} {d : ℕ}
    (h : labelCode W (σ, 0) = d) : BitsAt d 0 (msCode σ ++ msCode 0) := by
  have := bitsAt_labelCode hW (σ, 0); rwa [h] at this

theorem partOkN_iff {B W d : ℕ} (hW : W ≠ 0) (hB : codeWidth W ≤ B) (hd : d < 2 ^ codeWidth W) :
    PartOkN B W d ↔ labelCode W (fldMs W d, 0) = d := by
  constructor
  · rintro ⟨hv, hw⟩
    rw [validN_eq hd] at hv
    have hs : (decodeLabel W d).isSome := by
      by_contra hc; rw [ite_eq_right hc] at hv; exact absurd hv (by decide)
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hwt, hcode⟩ := labelCode_decode hd hl
    have hlen := msCode_length_le (by omega) l hwt
    have hb := bitsAt_labelCode hW l
    rw [hcode, bitsAt_append, Nat.zero_add] at hb
    have hend := (msParse_msCode (B := B) hb.1 (by omega)).2.1
    rw [Nat.zero_add] at hend
    rw [hend, wtN_msCode hb.2 (by omega)] at hw
    have h2 : l.2 = 0 := wt_eq_zero hw
    have hf : fldMs W d = l.1 := by unfold fldMs; rw [hl]
    rw [hf, ← h2]
    exact hcode
  · intro h
    have hwt := labelWt_fldMs hd
    have hdec : decodeLabel W d = some (fldMs W d, 0) := by
      rw [← decode_labelCode hwt, h]
    have hlen := msCode_length_le (by omega) _ hwt
    simp only at hlen
    have hb := bitsAt_labelCode_zero hW h
    rw [bitsAt_append, Nat.zero_add] at hb
    have hend := (msParse_msCode (B := B) hb.1 (by omega)).2.1
    rw [Nat.zero_add] at hend
    refine ⟨?_, ?_⟩
    · rw [validN_eq hd, hdec]; rfl
    · rw [hend, wtN_msCode hb.2 (by omega), wt_zero]

theorem mcode_of_labelCode {W B : ℕ} (hW : W ≠ 0) {σ : Multiset ℕ} {d : ℕ}
    (h : labelCode W (σ, 0) = d) (hB : (msCode σ).length ≤ B) :
    d % 2 ^ min (msEnd B d 0) B = mcode σ := by
  have hb := bitsAt_labelCode_zero hW h
  rw [bitsAt_append, Nat.zero_add] at hb
  have hend := (msParse_msCode hb.1 hB).2.1
  rw [Nat.zero_add] at hend
  rw [hend, Nat.min_eq_left hB, ← h]
  simp only [labelCode, hW, ↓reduceIte, ofBits_append, mcode]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ofBits_lt _)]

/-! ### Comparing multisets of typed targets part by part -/

/-- The test `∀ e, count e σ ≤ cnt e` on the multiset code at bit `q`: `1` or `0`. -/
def leCntN (B c q : ℕ) (cnt : ℕ → ℕ) : ℕ :=
  msFoldN (fun a e μ => if μ ≤ cnt e then a else 0) 1 B c q

private theorem foldl_le_cnt (cnt : ℕ → ℕ) : ∀ (l : List (ℕ × ℕ)) (a : ℕ),
    l.foldl (fun a e => if e.2 ≤ cnt e.1 then a else 0) a = if ∀ e ∈ l, e.2 ≤ cnt e.1 then a else 0
  | [], a => by simp
  | e :: l, a => by
    rw [List.foldl_cons, foldl_le_cnt cnt l]
    by_cases he : e.2 ≤ cnt e.1
    · exact if_congr (by simp [he]) (ite_eq_left he) rfl
    · simp [he]

theorem leCntN_msCode {B c q : ℕ} {σ : Multiset ℕ} (h : BitsAt c q (msCode σ))
    (hB : (msCode σ).length ≤ B) (cnt : ℕ → ℕ) :
    leCntN B c q cnt = 1 ↔ ∀ e, σ.count e ≤ cnt e := by
  rw [leCntN, msFoldN_msCode h hB, foldl_le_cnt]
  have key : (∀ e ∈ entries σ, e.2 ≤ cnt e.1) ↔ ∀ e, σ.count e ≤ cnt e := by
    refine ⟨fun H a => ?_, fun H e he => ?_⟩
    · by_cases ha : a ∈ σ
      · exact H (a, σ.count a) (mem_entries.mpr ⟨ha, rfl⟩)
      · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
    · rw [(mem_entries.mp he).2]; exact H e.1
  by_cases H : ∀ e ∈ entries σ, e.2 ≤ cnt e.1
  · rw [ite_eq_left H]; exact ⟨fun _ => key.mp H, fun _ => rfl⟩
  · rw [ite_eq_right H]; exact ⟨fun h => absurd h (by decide), fun h => absurd (key.mpr h) H⟩

theorem placeOf_pair_eq {up : Bool} {k p e j : ℕ} (hk : k < 3) (hp : p < 3) :
    ((placeOf up k, e) = (placeOf up p, j)) ↔ (k = p ∧ e = j) := by
  rw [Prod.mk.injEq]
  exact ⟨fun h => ⟨placeOf_inj hk hp h.1, h.2⟩, fun h => ⟨by rw [h.1], h.2⟩⟩

theorem le_sub_iff_parts {up : Bool} {T₁ T : Multiset (HPlace × ℕ)}
    (hT₁ : ∀ s ∈ T₁, ValidPl up s.1) {p j : ℕ} (hp : p < 3) :
    T₁ ≤ T - {(placeOf up p, j)} ↔ ∀ k < 3, ∀ e,
      (tpart up T₁ k).count e ≤ (tpart up T k).count e - (if k = p ∧ e = j then 1 else 0) := by
  rw [Multiset.le_iff_count]
  constructor
  · intro H k hk e
    have := H (placeOf up k, e)
    rw [Multiset.count_sub, Multiset.count_singleton] at this
    rw [count_tpart, count_tpart]
    refine this.trans_eq ?_
    congr 1
    exact if_congr (placeOf_pair_eq hk hp) rfl rfl
  · intro H s
    rw [Multiset.count_sub, Multiset.count_singleton]
    by_cases hs : s ∈ T₁
    · obtain ⟨k, hk, hks⟩ := hT₁ s hs
      have e : s = (placeOf up k, s.2) := Prod.ext hks rfl
      have := H k hk s.2
      rw [count_tpart, count_tpart, ← e] at this
      refine this.trans_eq ?_
      congr 1
      rw [e]
      exact (if_congr (placeOf_pair_eq hk hp) rfl rfl).symm
    · rw [Multiset.count_eq_zero_of_notMem hs]; exact Nat.zero_le _

theorem count_tpart_rest (up : Bool) (T T₁ : Multiset (HPlace × ℕ)) {k p : ℕ} (hk : k < 3)
    (hp : p < 3) (j e : ℕ) :
    (tpart up (T - T₁ - {(placeOf up p, j)}) k).count e =
      (tpart up T k).count e - (tpart up T₁ k).count e - (if k = p ∧ e = j then 1 else 0) := by
  rw [count_tpart, count_tpart, count_tpart, Multiset.count_sub, Multiset.count_sub,
    Multiset.count_singleton]
  congr 1
  exact if_congr (placeOf_pair_eq hk hp) rfl rfl


/-! ### The fit of a transport state -/

/-- **The fit of a transport state** to the weight bound `A` and the fuel `B`: the weights of its
labels and targets total at most `A ≥ 1`, codes of weight-`A` labels have at most `B` bits, and
every target has a place of the half-routing. -/
structure TrFit (A B : ℕ) (up : Bool) (x y m : Label) (T : Multiset (HPlace × ℕ)) : Prop where
  one_le : 1 ≤ A
  width_le : codeWidth A ≤ B
  wt_le : labelWt x + labelWt y + labelWt m + (T.map lwt).sum ≤ A
  valid : ∀ s ∈ T, ValidPl up s.1

theorem sum_sort_map (σ : Multiset ℕ) (g : ℕ → ℕ) : ((σ.sort (· ≤ ·)).map g).sum =
    (σ.map g).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]

theorem sum_lwt_srcList (up : Bool) (x y m : Label) :
    ((srcList up x y m).map lwt).sum = wt x.1 + wt y.1 + wt (msgMs up m) := by
  rw [srcList_eq]
  simp only [List.map_append, List.sum_append, List.map_map]
  have e : ∀ P : HPlace, (lwt ∘ fun i : ℕ => (P, i)) = fun i => i + 1 := fun _ => rfl
  simp only [e, sum_sort_map, wt]

theorem sum_lwt_srcSub_le (up : Bool) (x y m : Label) (lo hi : ℕ) :
    ((srcSub up x y m lo hi).map lwt).sum ≤ ((srcList up x y m).map lwt).sum := by
  rw [srcSub, List.map_take, List.map_drop]
  have h1 := List.sum_take_add_sum_drop (((srcList up x y m).map lwt).drop lo) (hi - lo)
  have h2 := List.sum_take_add_sum_drop ((srcList up x y m).map lwt) lo
  omega

theorem wt_msgMs_le (up : Bool) (m : Label) : wt (msgMs up m) ≤ labelWt m := by
  cases up <;> simp [msgMs, labelWt]

namespace TrFit

variable {A B : ℕ} {up : Bool} {x y m : Label} {T : Multiset (HPlace × ℕ)}

theorem lx (h : TrFit A B up x y m T) : LFits B x :=
  LFits.of_wt h.one_le h.width_le (by have := h.wt_le; omega)

theorem ly (h : TrFit A B up x y m T) : LFits B y :=
  LFits.of_wt h.one_le h.width_le (by have := h.wt_le; omega)

theorem lm (h : TrFit A B up x y m T) : LFits B m :=
  LFits.of_wt h.one_le h.width_le (by have := h.wt_le; omega)

theorem tf (h : TrFit A B up x y m T) : TFits B up T :=
  TFits.of_wt h.one_le h.width_le (by have := h.wt_le; omega)

theorem mono (h : TrFit A B up x y m T) {T' : Multiset (HPlace × ℕ)} (hT' : T' ≤ T) :
    TrFit A B up x y m T' :=
  ⟨h.one_le, h.width_le, by have := sum_lwt_mono hT'; have := h.wt_le; omega,
    fun s hs => h.valid s (Multiset.mem_of_le hT' hs)⟩

theorem tWt_le (h : TrFit A B up x y m T) (lo hi : ℕ) : tWt (srcSub up x y m lo hi) T ≤ A := by
  have h1 := sum_lwt_srcSub_le up x y m lo hi
  have h2 := sum_lwt_srcList up x y m
  have h3 := wt_msgMs_le up m
  have h4 := h.wt_le
  unfold labelWt at h3 h4
  unfold tWt
  omega

end TrFit

/-! ### The pivot test -/

/-- The weight of the first subproblem of a pivot index: the sources before the pivot and `T₁`. -/
def pivL1N (B up X Y M lo W i : ℕ) : ℕ :=
  srcWtN B up X Y M lo (lo + Radix.dig (pivW W) i 0) + wtN B (Radix.dig (pivW W) i 2) 0 +
    wtN B (Radix.dig (pivW W) i 3) 0 + wtN B (Radix.dig (pivW W) i 4) 0

/-- The multiplicities of part `k` of `T - {t}`, `t` of place index `p` and type `j`. -/
def restCnt (B Tc p j k : ℕ) : ℕ → ℕ := fun e =>
  countN B (getF Tc k) 0 e - if k = p ∧ e = j then 1 else 0

/-- **The pivot test** on codes (`PivotValid`): the pivot index is canonical, the pivot position
lies in the interval, the target lies in `T`, `T₁ ≤ T - {t}` part by part, the pivot condition
holds,
and the exponents lie in `[-W, W]`. -/
def PivOkN (B up X Y M lo hi Tc W i : ℕ) : Prop :=
  (i < 2 ^ pivWidth W ∧ PartOkN B W (Radix.dig (pivW W) i 2) ∧ PartOkN B W
      (Radix.dig (pivW W) i 3) ∧
      PartOkN B W (Radix.dig (pivW W) i 4)) ∧
    Radix.dig (pivW W) i 0 < min (hi - lo) (srcLenN B up X Y M - lo) ∧
    0 < countN B (getF Tc (Radix.dig (pivW W) i 1 % 3)) 0 (Radix.dig (pivW W) i 1 / 3) ∧
    (∀ k < 3, leCntN B (Radix.dig (pivW W) i (k + 2)) 0
      (restCnt B Tc (Radix.dig (pivW W) i 1 % 3) (Radix.dig (pivW W) i 1 / 3) k) = 1) ∧
    (2 * pivL1N B up X Y M lo W i < W ∧
      W ≤ 2 * (pivL1N B up X Y M lo W i + (srcTyN B up X Y M (lo + Radix.dig (pivW W) i 0) + 1) +
        (Radix.dig (pivW W) i 1 / 3 + 1))) ∧
    Radix.dig (pivW W) i 5 ≤ 2 * W ∧ Radix.dig (pivW W) i 6 ≤ 2 * W

instance (B up X Y M lo hi Tc W i : ℕ) : Decidable (PivOkN B up X Y M lo hi Tc W i) := by
  unfold PivOkN; infer_instance

theorem tpart_pivT₁ (up : Bool) (W i : ℕ) {k : ℕ} (hk : k < 3) :
    tpart up (pivT₁ up W i) k = fldMs W (Radix.dig (pivW W) i (k + 2)) := by
  rw [pivT₁, tpart_loc3 up _ _ _ hk]
  interval_cases k <;> rfl

/-- Under canonical fields, the fields hold the codes of the parts of `T₁`. -/
theorem canon_facts {B W i : ℕ} (hW : W ≠ 0) (hWB : codeWidth W ≤ B)
    (hc : ∀ k < 3, labelCode W (fldMs W (Radix.dig (pivW W) i (k + 2)), 0) = Radix.dig
        (pivW W) i (k + 2))
    {k : ℕ} (hk : k < 3) :
    BitsAt (Radix.dig (pivW W) i (k + 2)) 0 (msCode (fldMs W (Radix.dig (pivW W) i (k + 2)))) ∧
      (msCode (fldMs W (Radix.dig (pivW W) i (k + 2)))).length ≤ B := by
  refine ⟨(bitsAt_append.mp (bitsAt_labelCode_zero hW (hc k hk))).1, ?_⟩
  have := labelWt_fldMs (dig_part_lt W i (j := k + 2) (by omega) (by omega))
  simp only [labelWt, wt_zero, add_zero] at this
  exact (msCode_length_le_of_wt (by omega) this).trans hWB

/-- **The pivot test decides `PivotValid`.** -/
theorem pivOkN_iff {A B : ℕ} {up : Bool} {x y m : Label} {T : Multiset (HPlace × ℕ)}
    (hf : TrFit A B up x y m T) (lo hi i : ℕ) :
    PivotValid up x y m lo hi T i ↔ PivOkN B up.toNat (lcode x) (lcode y) (lcode m) lo hi
        (tcode up T)
      (tWt (srcSub up x y m lo hi) T) i := by
  have hx := hf.lx; have hy := hf.ly; have hm := hf.lm; have hTf := hf.tf; have hT := hf.valid
  have hWA := hf.tWt_le lo hi
  have hlW := length_le_tWt (srcSub up x y m lo hi) T
  have hlen : (srcSub up x y m lo hi).length =
      min (hi - lo) (srcLenN B up.toNat (lcode x) (lcode y) (lcode m) - lo) := by
    rw [srcLenN_eq up hx hy hm]; simp [srcSub]
  rw [pivotValid_iff, pivCodeX_decode_iff]
  unfold PivOK PivOkN PivotCond
  rw [decodePivot_eq']
  dsimp only
  rw [← hlen]
  set W := tWt (srcSub up x y m lo hi) T with hW
  set l := srcSub up x y m lo hi with hl
  have hp : Radix.dig (pivW W) i 1 % 3 < 3 := Nat.mod_lt _ (by omega)
  have hWB : codeWidth W ≤ B := (codeWidth_le_of_le hWA).trans hf.width_le
  -- the canonical fields
  have hcan : W ≠ 0 → ((∀ k < 3, labelCode W (fldMs W (Radix.dig (pivW W) i (k + 2)), 0) = Radix.dig
      (pivW W) i (k + 2)) ↔
      (PartOkN B W (Radix.dig (pivW W) i 2) ∧ PartOkN B W (Radix.dig (pivW W) i 3) ∧ PartOkN B W
          (Radix.dig (pivW W) i 4))) := by
    intro hW0
    have e := fun k (hk : k < 3) =>
      partOkN_iff (B := B) hW0 hWB (dig_part_lt W i (j := k + 2) (by omega) (by omega))
    constructor
    · intro h
      exact ⟨(e 0 (by omega)).mpr (h 0 (by omega)), (e 1 (by omega)).mpr (h 1 (by omega)),
        (e 2 (by omega)).mpr (h 2 (by omega))⟩
    · rintro ⟨h0, h1, h2⟩ k hk
      interval_cases k
      · exact (e 0 (by omega)).mp h0
      · exact (e 1 (by omega)).mp h1
      · exact (e 2 (by omega)).mp h2
  -- the target
  have ht : (placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3) ∈ T ↔ 0 < countN B
      (getF (tcode up T) (Radix.dig (pivW W) i 1 % 3)) 0 (Radix.dig (pivW W) i 1 / 3) := by
    rw [countN_msCode (bitsAt_part up T hp) (hTf _ hp), count_tpart, Multiset.count_pos]
  -- `T₁ ≤ T - {t}`
  have hT1 : W ≠ 0 → (∀ k < 3, labelCode W (fldMs W (Radix.dig (pivW W) i (k + 2)), 0) = Radix.dig
      (pivW W) i (k + 2)) →
      (pivT₁ up W i ≤ T - {(placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3)} ↔
        ∀ k < 3, leCntN B (Radix.dig (pivW W) i (k + 2)) 0
            (restCnt B (tcode up T) (Radix.dig (pivW W) i 1 % 3)
                (Radix.dig (pivW W) i 1 / 3) k) = 1) := by
    intro hW0 hc
    rw [le_sub_iff_parts (T₁ := pivT₁ up W i) (loc3_valid _ _ _ _) hp]
    refine forall₂_congr fun k hk => ?_
    obtain ⟨hb, hbl⟩ := canon_facts hW0 hWB hc hk
    rw [leCntN_msCode hb hbl, tpart_pivT₁ up W i hk]
    refine forall_congr' fun e => ?_
    rw [restCnt, countN_msCode (bitsAt_part up T hk) (hTf _ hk)]
  -- the pivot condition
  have hpc : Radix.dig (pivW W) i 0 < l.length → W ≠ 0 →
      (∀ k < 3, labelCode W (fldMs W (Radix.dig (pivW W) i (k + 2)), 0) = Radix.dig
          (pivW W) i (k + 2)) →
      ((2 * tWt (l.take (Radix.dig (pivW W) i 0)) (pivT₁ up W i) < W ∧
        W ≤ 2 * (tWt (l.take (Radix.dig (pivW W) i 0)) (pivT₁ up W i) + lwt
            (l.getD (Radix.dig (pivW W) i 0)
            (placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3)) +
          lwt (placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3))) ↔
      (2 * pivL1N B up.toNat (lcode x) (lcode y) (lcode m) lo W i < W ∧
        W ≤ 2 * (pivL1N B up.toNat (lcode x) (lcode y) (lcode m) lo W i +
          (srcTyN B up.toNat (lcode x) (lcode y) (lcode m) (lo + Radix.dig (pivW W) i 0) + 1) +
              (Radix.dig (pivW W) i 1 / 3 + 1)))) := by
    intro hν hW0 hc
    rw [hlen] at hν
    have hν' : Radix.dig (pivW W) i 0 < hi - lo := lt_of_lt_of_le hν (min_le_left _ _)
    have hν'' : lo + Radix.dig (pivW W) i 0 < (srcList up x y m).length := by
      have := lt_of_lt_of_le hν (min_le_right _ _)
      rw [srcLenN_eq up hx hy hm] at this; omega
    have e1 : tWt (l.take (Radix.dig (pivW W) i 0)) (pivT₁ up W i) = pivL1N B up.toNat (lcode x)
        (lcode y) (lcode m) lo W i := by
      rw [tWt, hl, take_srcSub up x y m hν'.le, ← srcWtN_eq up hx hy hm, pivT₁,
          sum_lwt_loc3, pivL1N]
      obtain ⟨b0, l0⟩ : BitsAt (Radix.dig (pivW W) i 2) 0
          (msCode (fldMs W (Radix.dig (pivW W) i 2))) ∧
          (msCode (fldMs W (Radix.dig (pivW W) i 2))).length ≤ B := canon_facts hW0 hWB hc
              (k := 0) (by omega)
      obtain ⟨b1, l1⟩ : BitsAt (Radix.dig (pivW W) i 3) 0
          (msCode (fldMs W (Radix.dig (pivW W) i 3))) ∧
          (msCode (fldMs W (Radix.dig (pivW W) i 3))).length ≤ B := canon_facts hW0 hWB hc
              (k := 1) (by omega)
      obtain ⟨b2, l2⟩ : BitsAt (Radix.dig (pivW W) i 4) 0
          (msCode (fldMs W (Radix.dig (pivW W) i 4))) ∧
          (msCode (fldMs W (Radix.dig (pivW W) i 4))).length ≤ B := canon_facts hW0 hWB hc
              (k := 2) (by omega)
      rw [wtN_msCode b0 l0, wtN_msCode b1 l1, wtN_msCode b2 l2]
      omega
    have e2 : lwt (l.getD (Radix.dig (pivW W) i 0)
        (placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3)) =
        srcTyN B up.toNat (lcode x) (lcode y) (lcode m) (lo + Radix.dig (pivW W) i 0) + 1 := by
      rw [hl, getD_srcSub up x y m hν', srcList_getD up hx hy hm hν'']; rfl
    rw [e1, e2]; rfl
  have hc5 : ∀ n : ℕ, |((n : ℤ) - W)| ≤ W ↔ n ≤ 2 * W := fun n => by rw [abs_le]; omega
  constructor
  · rintro ⟨⟨hi', hc⟩, hν, ht', hT1', hpc', h5, h6⟩
    have hW0 : W ≠ 0 := by omega
    exact ⟨⟨hi', (hcan hW0).mp hc⟩, hν, ht.mp ht', (hT1 hW0 hc).mp hT1', (hpc hν hW0 hc).mp hpc',
      (hc5 _).mp h5, (hc5 _).mp h6⟩
  · rintro ⟨⟨hi', hc⟩, hν, ht', hT1', hpc', h5, h6⟩
    have hW0 : W ≠ 0 := by omega
    have hc' := (hcan hW0).mpr hc
    exact ⟨⟨hi', hc'⟩, hν, ht.mpr ht', (hT1 hW0 hc').mpr hT1', (hpc hν hW0 hc').mpr hpc',
      (hc5 _).mpr h5, (hc5 _).mpr h6⟩


/-! ### Integers and places as numbers -/

theorem zz_unzz (n : ℕ) : zz (unzz n) = n := by
  unfold zz unzz
  split_ifs <;> omega

theorem zz_inj {a b : ℤ} : zz a = zz b ↔ a = b :=
  ⟨fun h => by rw [← unzz_zz a, h, unzz_zz], fun h => h ▸ rfl⟩

/-- `zz (a - b)` for naturals `a`, `b`. -/
def zzSubN (a b : ℕ) : ℕ := if b ≤ a then 2 * (a - b) else 2 * (b - a) - 1

theorem zzSubN_eq (a b : ℕ) : zzSubN a b = zz ((a : ℤ) - b) := by
  unfold zzSubN zz; split_ifs <;> omega

/-- `zz (unzz z + a - b)`. -/
def zzAddN (z a b : ℕ) : ℕ := if z % 2 = 0 then zzSubN (z / 2 + a) b else zzSubN a (b + (z + 1) / 2)

theorem zzAddN_eq (z a b : ℕ) : zzAddN z a b = zz (unzz z + a - b) := by
  unfold zzAddN unzz
  by_cases h : z % 2 = 0
  · rw [ite_eq_left h, ite_eq_left h, zzSubN_eq]; congr 1
  · rw [ite_eq_right h, ite_eq_right h, zzSubN_eq]; congr 1; push_cast; ring

/-- The number `plNum (placeOf up p)` of the place of index `p`. -/
def plOfN (up p : ℕ) : ℕ :=
  if p = 0 then (if up = 1 then 1 else 3) else if p = 1 then (if up = 1 then 2 else 4) else 0

theorem plOfN_eq (up : Bool) {p : ℕ} (hp : p < 3) : plOfN up.toNat p = plNum (placeOf up p) := by
  interval_cases p <;> cases up <;> rfl

/-- The place index of a place number. -/
def plIdxN (pn : ℕ) : ℕ := if pn = 0 then 2 else if pn = 1 ∨ pn = 3 then 0 else 1

theorem plIdxN_plNum (up : Bool) {p : ℕ} (hp : p < 3) : plIdxN (plNum (placeOf up p)) = p := by
  interval_cases p <;> cases up <;> rfl

theorem tgtNum_valid {up : Bool} {t : HPlace × ℕ} (ht : ValidPl up t.1) :
    t = (placeOf up (plIdxN (tgtNum t % 8)), tgtNum t / 8) ∧ plIdxN (tgtNum t % 8) < 3 := by
  obtain ⟨k, hk, hkt⟩ := ht
  have h5 := plNum_lt t.1
  have e1 : tgtNum t % 8 = plNum t.1 := by unfold tgtNum; omega
  have e2 : tgtNum t / 8 = t.2 := by unfold tgtNum; omega
  rw [e1, e2, hkt, plIdxN_plNum up hk]
  exact ⟨Prod.ext hkt rfl, hk⟩

/-! ### The codes of the parts of `T₂ = T - T₁ - {t}` -/

/-- The code of part `k` of `T - T₁ - {t}` (`t` of place index `p` and type `j`), from the code of
`T` and the code `dk` of part `k` of `T₁`. -/
def restN (B Tc p j k dk : ℕ) : ℕ :=
  (msOfCount B (topN B (getF Tc k) 0) fun e =>
    countN B (getF Tc k) 0 e - countN B dk 0 e - if k = p ∧ e = j then 1 else 0).1

theorem restN_eq {A B : ℕ} {up : Bool} {x y m : Label} {T T₁ : Multiset (HPlace × ℕ)}
    (hf : TrFit A B up x y m T) {k p : ℕ} (hk : k < 3) (hp : p < 3) (j : ℕ) {dk : ℕ}
    (hb : BitsAt dk 0 (msCode (tpart up T₁ k))) (hbl : (msCode (tpart up T₁ k)).length ≤ B) :
    restN B (tcode up T) p j k dk = mcode (tpart up (T - T₁ - {(placeOf up p, j)}) k) := by
  have hTk := bitsAt_part up T hk
  have hTl := hf.tf k hk
  have hcnt := count_tpart_rest up T T₁ hk hp j
  have hle : tpart up (T - T₁ - {(placeOf up p, j)}) k ≤ tpart up T k :=
    Multiset.le_iff_count.mpr fun e => by rw [hcnt]; omega
  have hlen : (msCode (tpart up (T - T₁ - {(placeOf up p, j)}) k)).length ≤ B := by
    have := wt_tpart_le up T k
    have := hf.wt_le
    exact (msCode_length_le_of_wt hf.one_le (le_trans (wt_mono hle) (by omega))).trans hf.width_le
  rw [restN, msOfCount_eq (ρ := tpart up (T - T₁ - {(placeOf up p, j)}) k) (fun e _ => ?_)
      (fun e he => ?_) hlen]
  · rfl
  · rw [hcnt, countN_msCode hTk hTl, countN_msCode hb hbl]
  · exact lt_topN_msCode hTk hTl (Multiset.mem_of_le hle he)

/-! ### The children of a transport sum -/

/-- **The child of a transport sum** (`tr`, kind `7`) at the pivot index `i`: the code of the
product `trm` if the index is valid, else the code of `zero`. -/
def trChildN (B e i : ℕ) : ℕ :=
  let up := getF e 1; let X := getF e 2; let Y := getF e 3; let M := getF e 4
  let lo := getF e 5; let hi := getF e 6; let Tc := getF e 7
  let W := trWN B up X Y M lo hi Tc
  let d := Radix.dig (pivW W) i
  if PivOkN B up X Y M lo hi Tc W i then
    NatList.enc [8, up, X, Y, M, lo, lo + d 0, hi, plOfN up (d 1 % 3) + 8 * (d 1 / 3),
      NatList.enc [d 2 % 2 ^ min (msEnd B (d 2) 0) B, d 3 % 2 ^ min (msEnd B (d 3) 0) B,
        d 4 % 2 ^ min (msEnd B (d 4) 0) B],
      NatList.enc [restN B Tc (d 1 % 3) (d 1 / 3) 0 (d 2), restN B Tc (d 1 % 3) (d 1 / 3) 1 (d 3),
        restN B Tc (d 1 % 3) (d 1 / 3) 2 (d 4)],
      zzSubN (d 5) W, zzSubN (d 6) W, zzAddN (getF e 8) (2 * W) (d 5 + d 6)]
  else NatList.enc [0]

theorem getF_lit (l : List ℕ) {k : ℕ} (h : k < l.length) : getF (NatList.enc l) k = l[k] :=
  getF_enc l k h

/-! ### The fields of the codes of transport states -/

section Fields

variable (S : Setup) (up : Bool) (x y m : Label) (lo pos hi : ℕ) (t : HPlace × ℕ)
  (T T₁ T₂ : Multiset (HPlace × ℕ)) (c c₁ c₀ c₂ : ℤ)

theorem fields_tr :
      getF (S.code (.tr up x y m lo hi T c)) 0 = 7 ∧
      getF (S.code (.tr up x y m lo hi T c)) 1 = up.toNat ∧
      getF (S.code (.tr up x y m lo hi T c)) 2 = lcode x ∧
      getF (S.code (.tr up x y m lo hi T c)) 3 = lcode y ∧
      getF (S.code (.tr up x y m lo hi T c)) 4 = lcode m ∧
      getF (S.code (.tr up x y m lo hi T c)) 5 = lo ∧
      getF (S.code (.tr up x y m lo hi T c)) 6 = hi ∧
      getF (S.code (.tr up x y m lo hi T c)) 7 = tcode up T ∧
      getF (S.code (.tr up x y m lo hi T c)) 8 = zz c :=
  ⟨getF_enc _ 0 (by simp), getF_enc _ 1 (by simp), getF_enc _ 2 (by simp), getF_enc _ 3 (by simp),
      getF_enc _ 4 (by simp), getF_enc _ 5 (by simp), getF_enc _ 6 (by simp), getF_enc _ 7
      (by simp), getF_enc _ 8 (by simp)⟩

theorem fields_trm :
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 0 = 8 ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 1 = up.toNat ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 2 = lcode x ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 3 = lcode y ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 4 = lcode m ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 5 = lo ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 6 = pos ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 7 = hi ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 8 = tgtNum t ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 9 = tcode up T₁ ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 10 = tcode up T₂ ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 11 = zz c₁ ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 12 = zz c₀ ∧
      getF (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) 13 = zz c₂ :=
  ⟨getF_enc _ 0 (by simp), getF_enc _ 1 (by simp), getF_enc _ 2 (by simp), getF_enc _ 3 (by simp),
      getF_enc _ 4 (by simp), getF_enc _ 5 (by simp), getF_enc _ 6 (by simp), getF_enc _ 7
      (by simp), getF_enc _ 8 (by simp), getF_enc _ 9 (by simp), getF_enc _ 10 (by simp), getF_enc _
      11 (by simp), getF_enc _ 12 (by simp), getF_enc _ 13 (by simp)⟩

theorem fields_trr :
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 0 = 9 ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 1 = up.toNat ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 2 = lcode x ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 3 = lcode y ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 4 = lcode m ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 5 = pos ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 6 = hi ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 7 = tgtNum t ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 8 = tcode up T₂ ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 9 = zz c₀ ∧
      getF (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) 10 = zz c₂ :=
  ⟨getF_enc _ 0 (by simp), getF_enc _ 1 (by simp), getF_enc _ 2 (by simp), getF_enc _ 3 (by simp),
      getF_enc _ 4 (by simp), getF_enc _ 5 (by simp), getF_enc _ 6 (by simp), getF_enc _ 7
      (by simp), getF_enc _ 8 (by simp), getF_enc _ 9 (by simp), getF_enc _ 10 (by simp)⟩

end Fields

open Classical in
theorem gen_child_tr (S : Setup) (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ))
    (c : ℤ) (i : ℕ) : S.gen.child (.tr up x y m lo hi T c) i =
      if PivotValid up x y m lo hi T i then
        .trm up x y m lo (lo + (decodePivot up (tWt (srcSub up x y m lo hi) T) i).1) hi
          (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.1
          (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.2.1
          (T - (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.2.1 -
            {(decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.1})
          (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.2.2.1
          (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.2.2.2
          (c - (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.2.2.1 -
            (decodePivot up (tWt (srcSub up x y m lo hi) T) i).2.2.2.2)
      else .zero := by
  change (if _ then _ else _) = _
  split_ifs
  · generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d
    obtain ⟨ν, t, T₁, c₁, c₀⟩ := d
    rfl
  · rfl

theorem trChildN_code (S : Setup) {A B : ℕ} {up : Bool} {x y m : Label} {lo hi : ℕ}
    {T : Multiset (HPlace × ℕ)} (hf : TrFit A B up x y m T) (c : ℤ) (i : ℕ) :
    trChildN B (S.code (.tr up x y m lo hi T c)) i = S.code
        (S.gen.child (.tr up x y m lo hi T c) i) := by
  rw [gen_child_tr]
  obtain ⟨-, f1, f2, f3, f4, f5, f6, f7, f8⟩ := fields_tr S up x y m lo hi T c
  simp only [trChildN, f1, f2, f3, f4, f5, f6, f7, f8]
  rw [trWN_eq up hf.lx hf.ly hf.lm lo hi hf.valid hf.tf]
  by_cases hv : PivotValid up x y m lo hi T i
  · rw [ite_eq_left ((pivOkN_iff hf lo hi i).mp hv), ite_eq_left hv]
    have hv' := (pivotValid_iff up x y m lo hi T i).mp hv
    rw [pivCodeX_decode_iff] at hv'
    obtain ⟨⟨-, hc⟩, hok⟩ := hv'
    unfold PivOK at hok
    rw [decodePivot_eq'] at hok ⊢
    dsimp only at hok ⊢
    obtain ⟨hν, -⟩ := hok
    set W := tWt (srcSub up x y m lo hi) T with hW
    have hW0 : W ≠ 0 := by
      have := length_le_tWt (srcSub up x y m lo hi) T; omega
    have hWB : codeWidth W ≤ B := (codeWidth_le_of_le (hf.tWt_le lo hi)).trans hf.width_le
    have hp : Radix.dig (pivW W) i 1 % 3 < 3 := Nat.mod_lt _ (by omega)
    have hm3 : ∀ k < 3, Radix.dig (pivW W) i (k + 2) % 2 ^ min
        (msEnd B (Radix.dig (pivW W) i (k + 2)) 0) B =
        mcode (tpart up (pivT₁ up W i) k) := by
      intro k hk
      rw [tpart_pivT₁ up W i hk]
      exact mcode_of_labelCode hW0 (hc k hk) (canon_facts hW0 hWB hc hk).2
    have hr3 : ∀ k < 3, restN B (tcode up T) (Radix.dig (pivW W) i 1 % 3)
        (Radix.dig (pivW W) i 1 / 3) k (Radix.dig (pivW W) i (k + 2)) =
        mcode (tpart up (T - pivT₁ up W i -
            {(placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3)}) k) := by
      intro k hk
      obtain ⟨hb, hbl⟩ := canon_facts hW0 hWB hc hk
      rw [← tpart_pivT₁ up W i hk] at hb hbl
      exact restN_eq hf hk hp _ hb hbl
    simp only [Setup.code, tcode]
    rw [plOfN_eq up hp, ← hm3 0 (by omega), ← hm3 1 (by omega), ← hm3 2 (by omega),
      ← hr3 0 (by omega), ← hr3 1 (by omega), ← hr3 2 (by omega), zzSubN_eq, zzSubN_eq, zzAddN_eq,
      unzz_zz]
    rw [show c - ((Radix.dig (pivW W) i 5 : ℕ) - (W : ℤ)) -
        ((Radix.dig (pivW W) i 6 : ℕ) - (W : ℤ)) =
      c + ((2 * W : ℕ) : ℤ) - ((Radix.dig (pivW W) i 5 + Radix.dig (pivW W) i 6 : ℕ) :
          ℤ) by push_cast; ring]
    rfl
  · rw [ite_eq_right (fun h => hv ((pivOkN_iff hf lo hi i).mpr h)), ite_eq_right hv]
    rfl

/-- The children of a product of two transport coefficients (`trm`, kind `8`). -/
def trmChildN (e b : ℕ) : ℕ :=
  if b = 0 then NatList.enc [7, getF e 1, getF e 2, getF e 3, getF e 4, getF e 5, getF e 6, getF e
      9, getF e 11]
  else NatList.enc [9, getF e 1, getF e 2, getF e 3, getF e 4, getF e 6, getF e 7, getF e 8, getF e
      10,
    getF e 12, getF e 13]

theorem trmChildN_code (S : Setup) (up : Bool) (x y m : Label) (lo pos hi : ℕ) (t : HPlace × ℕ)
    (T₁ T₂ : Multiset (HPlace × ℕ)) (c₁ c₀ c₂ : ℤ) (b : ℕ) :
    trmChildN (S.code (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) b =
      S.code (S.gen.child (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂) b) := by
  have hch : S.gen.child (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂) b =
      if b = 0 then .tr up x y m lo pos T₁ c₁ else .trr up x y m pos hi t T₂ c₀ c₂ := rfl
  rw [hch]
  obtain ⟨-, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ :=
    fields_trm S up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂
  simp only [trmChildN, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13]
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ite_eq_left hb]; rfl
  · rw [ite_eq_right hb, ite_eq_right hb]; rfl

/-! ### The rule coefficients -/

/-- **The coefficient `[z^c] R(s, t)`** of a half-rule, for a source of type `i` at the place of
index `ps` and a target of type `j` at the place of index `pt`: `0` at the same place; between the
corners,
`χ z^{-d}` (below the cut) and `(1 - z^{-2}) χ z^{-d}` (above); between the cut and the corner `x`
(above) or `v` (below), `(1 - z²) χ z^d` and `χ z^d`; between the cut and the copying corner,
`[i = j][c = 0]`. Here `d = d(i, j)` and `χ = χ(i, j)`. -/
def ruleZ (up : Bool) (ps i pt j : ℕ) (c : ℤ) : ℤ :=
  if ps = pt then 0
  else if ps ≠ 2 ∧ pt ≠ 2 then
    (if up then (if -(d i j : ℤ) = c then chi i j else 0) -
        (if -(d i j : ℤ) - 2 = c then chi i j else 0)
     else if -(d i j : ℤ) = c then chi i j else 0)
  else if (if up then ps = 0 ∨ pt = 0 else ps = 1 ∨ pt = 1) then
    (if up then (if (d i j : ℤ) = c then chi i j else 0) -
        (if (d i j : ℤ) + 2 = c then chi i j else 0)
     else if (d i j : ℤ) = c then chi i j else 0)
  else if i = j ∧ c = 0 then 1 else 0

theorem coeff_CT (s n e : ℤ) :
    (LaurentPolynomial.C s * LaurentPolynomial.T n : Lp).coeff e = if n = e then s else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem coeff_cubeC (i j : ℕ) (e : ℤ) : (Cube.C i j).coeff e = if (d i j : ℤ) =
    e then chi i j else 0 :=
  coeff_CT _ _ _

theorem coeff_bar_cubeC (i j : ℕ) (e : ℤ) :
    (bar (Cube.C i j)).coeff e = if -(d i j : ℤ) = e then chi i j else 0 := by
  rw [bar, Cube.C, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  exact coeff_CT _ _ _

theorem coeff_oneSubZ2_cubeC (i j : ℕ) (e : ℤ) : (oneSubZ2 * Cube.C i j).coeff e =
    (if (d i j : ℤ) = e then chi i j else 0) - (if (d i j : ℤ) + 2 = e then chi i j else 0) := by
  have h : oneSubZ2 * Cube.C i j = LaurentPolynomial.C (chi i j) * LaurentPolynomial.T (d i j : ℤ) -
      LaurentPolynomial.C (chi i j) * LaurentPolynomial.T ((d i j : ℤ) + 2) := by
    unfold oneSubZ2 Cube.C; rw [LaurentPolynomial.T_add]; ring
  rw [h, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_CT, coeff_CT]

theorem coeff_oneSubZm2_bar (i j : ℕ) (e : ℤ) : (oneSubZm2 * bar (Cube.C i j)).coeff e =
    (if -(d i j : ℤ) = e then chi i j else 0) - (if -(d i j : ℤ) - 2 = e then chi i j else 0) := by
  have h : oneSubZm2 * bar (Cube.C i j) =
      LaurentPolynomial.C (chi i j) * LaurentPolynomial.T (-(d i j : ℤ)) -
        LaurentPolynomial.C (chi i j) * LaurentPolynomial.T (-(d i j : ℤ) - 2) := by
    rw [bar, Cube.C, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    unfold oneSubZm2; rw [sub_eq_add_neg (-(d i j : ℤ)), LaurentPolynomial.T_add]; ring
  rw [h, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_CT, coeff_CT]

theorem coeff_eqL (i j : ℕ) (e : ℤ) : (eqL i j).coeff e = if i = j ∧ e = 0 then 1 else 0 := by
  unfold eqL
  by_cases h : i = j
  · rw [ite_eq_left h, show (1 : Lp) = LaurentPolynomial.C 1 * LaurentPolynomial.T 0 by simp,
      coeff_CT]
    simp [h, eq_comm]
  · simp [h]

theorem eqL_comm (i j : ℕ) : eqL i j = eqL j i := by
  unfold eqL; simp [eq_comm]

theorem coeff_zero_Lp (e : ℤ) : (0 : Lp).coeff e = 0 := rfl

theorem hRule_coeff (up : Bool) {ps pt : ℕ} (hps : ps < 3) (hpt : pt < 3) (i j : ℕ) (c : ℤ) :
    (hRule up (placeOf up ps) i (placeOf up pt) j).coeff c = ruleZ up ps i pt j c := by
  interval_cases ps <;> interval_cases pt <;> cases up <;>
    simp (config := { decide := true }) only [hRule, placeOf, upRule, downRule, ruleZ,
      ↓reduceIte] <;>
    first
    | exact coeff_zero_Lp c
    | exact coeff_cubeC i j c
    | exact coeff_bar_cubeC i j c
    | exact coeff_oneSubZ2_cubeC i j c
    | exact coeff_oneSubZm2_bar i j c
    | exact coeff_eqL i j c
    | (rw [C_comm j i]
       first
       | exact coeff_cubeC i j c
       | exact coeff_bar_cubeC i j c
       | exact coeff_oneSubZ2_cubeC i j c
       | exact coeff_oneSubZm2_bar i j c)
    | (rw [eqL_comm j i]; exact coeff_eqL i j c)

theorem chi_eq (i j : ℕ) : chi i j = if ip i j % 2 = 0 then 1 else -1 := by
  unfold chi
  rcases Nat.even_or_odd (ip i j) with h | h
  · rw [h.neg_one_pow, ite_eq_left (Nat.even_iff.mp h)]
  · rw [h.neg_one_pow, ite_eq_right (by have := Nat.odd_iff.mp h; omega)]

/-- **The rule coefficient as a zigzag code**, from the zigzag code `z` of the exponent. -/
def ruleN (up ps i pt j z : ℕ) : ℕ :=
  if ps = pt then 0
  else if ps ≠ 2 ∧ pt ≠ 2 then
    (if up = 1 then
      (if z = zzSubN 0 (d i j) then (if ip i j % 2 = 0 then 2 else 1)
       else if z = 2 * d i j + 3 then (if ip i j % 2 = 0 then 1 else 2) else 0)
     else if z = zzSubN 0 (d i j) then (if ip i j % 2 = 0 then 2 else 1) else 0)
  else if (if up = 1 then ps = 0 ∨ pt = 0 else ps = 1 ∨ pt = 1) then
    (if up = 1 then
      (if z = 2 * d i j then (if ip i j % 2 = 0 then 2 else 1)
       else if z = 2 * d i j + 4 then (if ip i j % 2 = 0 then 1 else 2) else 0)
     else if z = 2 * d i j then (if ip i j % 2 = 0 then 2 else 1) else 0)
  else if i = j ∧ z = 0 then 2 else 0

theorem ruleN_eq (up : Bool) (ps i pt j : ℕ) (c : ℤ) :
    ruleN up.toNat ps i pt j (zz c) = zz (ruleZ up ps i pt j c) := by
  have h1 : zz c = 2 * d i j ↔ (d i j : ℤ) = c := by
    rw [show 2 * d i j = zz (d i j : ℤ) by simp [zz], zz_inj, eq_comm]
  have h2 : zz c = 2 * d i j + 4 ↔ (d i j : ℤ) + 2 = c := by
    rw [show 2 * d i j + 4 = zz ((d i j : ℤ) +
        2) by unfold zz; split_ifs <;> omega, zz_inj, eq_comm]
  have h3 : zz c = zzSubN 0 (d i j) ↔ -(d i j : ℤ) = c := by
    rw [zzSubN_eq, zz_inj, eq_comm]; push_cast; simp
  have h4 : zz c = 2 * d i j + 3 ↔ -(d i j : ℤ) - 2 = c := by
    rw [show 2 * d i j + 3 = zz (-(d i j : ℤ) -
        2) by unfold zz; split_ifs <;> omega, zz_inj, eq_comm]
  have h5 : zz c = 0 ↔ c = 0 := by rw [show (0 : ℕ) = zz 0 by rfl, zz_inj]
  have hz1 : zz 1 = 2 := by decide
  have hzm1 : zz (-1) = 1 := by decide
  unfold ruleN ruleZ
  rw [chi_eq]
  simp only [h1, h2, h3, h4, h5]
  cases up <;>
    simp (config := { decide := true }) only [↓reduceIte] <;>
    split_ifs <;> first | omega | decide


/-! ### The children of a rule product -/

/-- The children of a product of a rule coefficient and a transport coefficient (`trr`, kind `9`):
the literal `[z^{c₀}] R(s, t)` (with `s` the source at the pivot position, or `t` past the end) and
the transport sum of the rest. -/
def trrChildN (B e b : ℕ) : ℕ :=
  if b = 0 then
    NatList.enc [1, ruleN (getF e 1)
      (if getF e 5 < srcLenN B (getF e 1) (getF e 2) (getF e 3) (getF e 4)
        then srcPlN B (getF e 2) (getF e 3) (getF e 5) else plIdxN (getF e 7 % 8))
      (if getF e 5 < srcLenN B (getF e 1) (getF e 2) (getF e 3) (getF e 4)
        then srcTyN B (getF e 1) (getF e 2) (getF e 3) (getF e 4) (getF e 5) else getF e 7 / 8)
      (plIdxN (getF e 7 % 8)) (getF e 7 / 8) (getF e 9)]
  else NatList.enc [7, getF e 1, getF e 2, getF e 3, getF e 4, getF e 5 + 1, getF e 6, getF e 8,
      getF e 10]

theorem tgtNum_placeOf (up : Bool) {k : ℕ} (hk : k < 3) (j : ℕ) :
    plIdxN (tgtNum (placeOf up k, j) % 8) = k ∧ tgtNum (placeOf up k, j) / 8 = j := by
  have h5 := plNum_lt (placeOf up k)
  have e1 : tgtNum (placeOf up k, j) % 8 = plNum (placeOf up k) := by simp only [tgtNum]; omega
  have e2 : tgtNum (placeOf up k, j) / 8 = j := by simp only [tgtNum]; omega
  rw [e1, e2, plIdxN_plNum up hk]
  exact ⟨rfl, rfl⟩

theorem trrChildN_code (S : Setup) {A B : ℕ} {up : Bool} {x y m : Label} {pos hi : ℕ}
    {t : HPlace × ℕ} {T₂ : Multiset (HPlace × ℕ)} (hf : TrFit A B up x y m T₂) (ht : ValidPl up t.1)
    (c₀ c₂ : ℤ) (b : ℕ) :
    trrChildN B (S.code (.trr up x y m pos hi t T₂ c₀ c₂)) b =
      S.code (S.gen.child (.trr up x y m pos hi t T₂ c₀ c₂) b) := by
  have hch : S.gen.child (.trr up x y m pos hi t T₂ c₀ c₂) b =
      if b = 0 then .lit ((hRule up ((srcList up x y m).getD pos t).1
          ((srcList up x y m).getD pos t).2
        t.1 t.2).coeff c₀) else .tr up x y m (pos + 1) hi T₂ c₂ := rfl
  rw [hch]
  obtain ⟨-, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := fields_trr S up x y m pos hi t T₂ c₀ c₂
  simp only [trrChildN, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ite_eq_left hb, srcLenN_eq up hf.lx hf.ly hf.lm]
    obtain ⟨t1, t2⟩ := t
    obtain ⟨k, hk, rfl⟩ := ht
    obtain ⟨e1, e2⟩ := tgtNum_placeOf up hk t2
    rw [e1, e2]
    have key : (hRule up ((srcList up x y m).getD pos (placeOf up k, t2)).1
        ((srcList up x y m).getD pos (placeOf up k, t2)).2 (placeOf up k) t2).coeff c₀ =
        ruleZ up (if pos < (srcList up x y m).length then srcPlN B (lcode x) (lcode y) pos else k)
          (if pos < (srcList up x y m).length then srcTyN B up.toNat (lcode x)
              (lcode y) (lcode m) pos
            else t2) k t2 c₀ := by
      by_cases hp : pos < (srcList up x y m).length
      · rw [srcList_getD up hf.lx hf.ly hf.lm hp, ite_eq_left hp, ite_eq_left hp]
        exact hRule_coeff up (srcPlN_lt _ _ _ _) hk _ _ _
      · rw [List.getD_eq_default _ _ (by omega), ite_eq_right hp, ite_eq_right hp]
        exact hRule_coeff up hk hk _ _ _
    rw [ruleN_eq, ← key]
    rfl
  · rw [ite_eq_right hb, ite_eq_right hb]; rfl

/-! ### Tags, index lengths and leaves -/

/-- The tag of a transport state from its code: a sum over the pivot indices while the source
interval is nonempty, else a leaf (kind `7`); a product (kinds `8`, `9`). -/
def trTagN (e : ℕ) : ℕ := if getF e 0 = 7 then (if getF e 5 < getF e 6 then 1 else 0) else 2

/-- The index length of a transport state: `pivWidth W` for kind `7`, else `0`. -/
def trWidthN (B e : ℕ) : ℕ :=
  if getF e 0 = 7 then
    pivWidth (trWN B (getF e 1) (getF e 2) (getF e 3) (getF e 4) (getF e 5) (getF e 6) (getF e 7))
  else 0

/-- The leaf value `[T = 0][c = 0]` of a transport state of kind `7` (else `0`). -/
def trLeafN (B e : ℕ) : ℕ :=
  if getF e 0 = 7 ∧ cardN B (getF (getF e 7) 0) 0 = 0 ∧ cardN B (getF (getF e 7) 1) 0 = 0 ∧
    cardN B (getF (getF e 7) 2) 0 = 0 ∧ getF e 8 = 0 then 1 else 0

/-- **The child of a transport state** from its code, by its kind `7`, `8` or `9`. -/
def trChildAllN (B e i : ℕ) : ℕ :=
  if getF e 0 = 7 then trChildN B e i else if getF e 0 = 8 then trmChildN e i else trrChildN B e i

/-! ### The invariant -/

/-- **The invariant of the transport states**: every multiset of targets fits `A` and `B`, and the
pivot target has a place of the half-routing. -/
def TrInv (A B : ℕ) : St → Prop
  | .tr up x y m _ _ T _ => TrFit A B up x y m T
  | .trm up x y m _ _ _ t T₁ T₂ _ _
      _ => TrFit A B up x y m T₁ ∧ TrFit A B up x y m T₂ ∧ ValidPl up t.1
  | .trr up x y m _ _ t T₂ _ _ => TrFit A B up x y m T₂ ∧ ValidPl up t.1
  | _ => False

theorem trInv_child (S : Setup) {A B : ℕ} {st : St} (h : TrInv A B st) (i : ℕ) :
    TrInv A B (S.gen.child st i) ∨ S.gen.child st i = .zero ∨ ∃ v, S.gen.child st i = .lit v := by
  cases st with
  | tr up x y m lo hi T c =>
    rw [gen_child_tr]
    split_ifs with hv
    · left
      obtain ⟨-, -, h2, h3, -⟩ := (pivotValid_iff up x y m lo hi T i).mp hv
      generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d at h2 h3 ⊢
      exact ⟨h.mono (h3.trans tsub_le_self), h.mono (tsub_le_self.trans tsub_le_self), h.valid _ h2⟩
    · exact Or.inr (Or.inl rfl)
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
    left
    change TrInv A B (if i = 0 then .tr up x y m lo pos T₁ c₁ else .trr up x y m pos hi t T₂ c₀ c₂)
    split_ifs
    · exact h.1
    · exact ⟨h.2.1, h.2.2⟩
  | trr up x y m pos hi t T₂ c₀ c₂ =>
    by_cases hi0 : i = 0
    · exact Or.inr (Or.inr ⟨_, by change (if i = 0 then _ else _) = _; rw [ite_eq_left hi0]⟩)
    · left
      change TrInv A B (if i = 0 then _ else .tr up x y m (pos + 1) hi T₂ c₂)
      rw [ite_eq_right hi0]
      exact h.1
  | _ => exact (h : False).elim

/-! ### Agreement -/

section Agree

variable (S : Setup) {A B : ℕ}

theorem trLeafN_tr {up : Bool} {x y m : Label} {lo hi : ℕ} {T : Multiset (HPlace × ℕ)}
    (hf : TrFit A B up x y m T) (c : ℤ) :
    (trLeafN B (S.code (.tr up x y m lo hi T c)) : ℤ) = S.gen.leafVal (.tr up x y m lo hi T c) := by
  obtain ⟨f0, -, -, -, -, -, -, f7, f8⟩ := fields_tr S up x y m lo hi T c
  have hc : ∀ k < 3, cardN B (getF (tcode up T) k) 0 = Multiset.card (tpart up T k) := fun k hk =>
    cardN_msCode (bitsAt_part up T hk) (hf.tf k hk)
  have key : (7 = 7 ∧ Multiset.card (tpart up T 0) = 0 ∧ Multiset.card (tpart up T 1) = 0 ∧
      Multiset.card (tpart up T 2) = 0 ∧ zz c = 0) ↔ (T = 0 ∧ c = 0) := by
    have hz : zz c = 0 ↔ c = 0 := by rw [show (0 : ℕ) = zz 0 from rfl, zz_inj]
    simp only [hz, Multiset.card_eq_zero, true_and]
    constructor
    · rintro ⟨h0, h1, h2, hc⟩
      refine ⟨eq_zero_of_tpart hf.valid fun p hp => ?_, hc⟩
      interval_cases p <;> assumption
    · rintro ⟨rfl, rfl⟩
      exact ⟨tpart_zero _ _, tpart_zero _ _, tpart_zero _ _, rfl⟩
  rw [trLeafN, f0, f7, f8, hc 0 (by omega), hc 1 (by omega), hc 2 (by omega)]
  change _ = (if _ then _ else _)
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.mp h1) h2
  · exact absurd (key.mpr h2) h1
  · rfl

/-- **Agreement at the transport states**: on a state of the invariant, the numeric functions give
the tag, the index length, the leaf value and the code of every child. -/
theorem tr_agree {st : St} (h : TrInv A B st) :
    (getF (S.code st) 0 = 7 ∨ getF (S.code st) 0 = 8 ∨ getF (S.code st) 0 = 9) ∧
    trTagN (S.code st) = AGen.kindTag (S.gen.kind st) ∧
    trWidthN B (S.code st) = S.gen.width st ∧
    (trLeafN B (S.code st) : ℤ) = S.gen.leafVal st ∧
    ∀ i, trChildAllN B (S.code st) i = S.code (S.gen.child st i) := by
  cases st with
  | tr up x y m lo hi T c =>
    obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, -⟩ := fields_tr S up x y m lo hi T c
    refine ⟨Or.inl f0, ?_, ?_, trLeafN_tr S h c, fun i => ?_⟩
    · rw [trTagN, f0, ite_eq_left rfl, f5, f6]
      change _ = AGen.kindTag (if lo < hi then .sum else .leaf)
      split_ifs <;> rfl
    · rw [trWidthN, f0, ite_eq_left rfl, f1, f2, f3, f4, f5, f6, f7,
        trWN_eq up h.lx h.ly h.lm lo hi h.valid h.tf]
      rfl
    · rw [trChildAllN, f0, ite_eq_left rfl]
      exact trChildN_code S h c i
  | trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
    obtain ⟨f0, -⟩ := fields_trm S up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂
    refine ⟨Or.inr (Or.inl f0), ?_, ?_, ?_, fun i => ?_⟩
    · rw [trTagN, f0]; rfl
    · rw [trWidthN, f0]; rfl
    · rw [trLeafN, f0]; rfl
    · rw [trChildAllN, f0]
      exact trmChildN_code S up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ i
  | trr up x y m pos hi t T₂ c₀ c₂ =>
    obtain ⟨f0, -⟩ := fields_trr S up x y m pos hi t T₂ c₀ c₂
    refine ⟨Or.inr (Or.inr f0), ?_, ?_, ?_, fun i => ?_⟩
    · rw [trTagN, f0]; rfl
    · rw [trWidthN, f0]; rfl
    · rw [trLeafN, f0]; rfl
    · rw [trChildAllN, f0]
      exact trrChildN_code S h.1 h.2 c₀ c₂ i
  | _ => exact (h : False).elim

end Agree

end Cslib.Complexity.NtimeDspace.Cube.Num
