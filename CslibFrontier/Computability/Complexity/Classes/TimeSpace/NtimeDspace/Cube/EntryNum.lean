/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetForm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PathsAux
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Sound
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.StCode
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.ListTerm

/-!
# The entry and range states as numbers (Lemma 6.4)

The machine of Lemma 6.4 keeps one state code (`Setup.code`, `StCode.lean`) and computes, from it
alone, the kind of the node, its index width and the code of each child. This module gives these
computations, in plain arithmetic on `ℕ`, for the clique states `cl`, the last labels `last`, the
entries `ent` and the factor ranges `rng`, and proves that they agree with `Setup.gen` on the
reachable states (`Setup.Inv` of `Sound.lean`).

Labels are never decoded. The argument of an old table entry is a slice of `ξ`, read off the
parent budget array (`sliceN`); a label inside an argument or copy code is a field of it, and its
code `lcode` is that field when the budget is nonzero and the field decodes (`argLabN`, tested by
`validN`), and `lcode (0, 0) = 3` otherwise. Unpacking stream `s` of a packed label keeps the types
`≡ s (mod L)` and divides them by `L` (`unpackN`, through `countN` and `msOfCount`); swapping a
label exchanges its two multiset codes (`swapN`); label equality is code equality
(`lcode_injective`); the weight tests use `labelWtN`; validity of a packed label is a scan of its
code (`labOkN`).

All readers take one fuel `B`; the agreement lemmas need `codeWidth (Φ₀ / 2^e) + 2 ≤ B` for the
potential `Φ₀` of the first clique and `2K = 2^(2^e)`: the potential halves at every merge, so every
budget along a valid path is at most `Φ₀ / 2^e` (`budget_le_path`).

## Main definitions

* `stGet n k`: entry `k` of the list coded by `n`; `cQ`, `cA` (`pQ`, `pA`): the node count and
  budget array of the first (second) clique of a cache.
* Label codes: `LB`, `swapN`, `unpackN`, `labOkN`, `zzSub`, `trRootN` (the code of the root
  transport state of a rectangle factor), `argLabN` (the code of a label of an argument code).
* `copiesOkN`, `argsOkN`: `CopiesValid`, `ArgsValid`.
* `psiN`, `factorGN`, `factorN`: the codes of the factor states (`psiG`, `factorG`,
  `Setup.factorSt`).
* `clTagN`, `clWidthN`, `clChildN`, `lastChildN`, `entTagN`, `entWidthN`, `entChildN`,
  `rngChildN`; the dispatch on the tag `eTag`, `eWidth`, `eChild`.

## Main results

* `argLabN_eq`, `unpackN_lcode`, `swapN_lcode`, `labOkN_lcode`, `labelWtN_lcode`, `trRootN_eq`,
  `copiesOkN_iff`, `argsOkN_iff`.
* `code_psiG`, `code_factorG`, `code_factorSt`: the factor states.
* `clTagN_eq`, `clWidthN_eq`, `clChildN_eq` (with the cache update `childN` on a valid choice),
  `entTagN_eq`, `entWidthN_eq`, `entChildN_eq`, `rngChildN_eq`.
* `entry_agree`: on the reachable entry states, `eTag`, `eWidth`, `eChild` compute
  `kindTag ∘ kind`, `width` and the codes of the children, and the leaf value is `0`.
* `fits_path`: every budget along a valid path fits the field width (`Fits`).
* `pathOK_chainOK`, `spair_le_path`, `budget_le_path`: for `2K = 2^(2^e)`, a valid path is a chain
  of at most `e` merges, and the budget sum (so every budget) along it is at most `Φ₀ / 2^e`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Setup

variable (S : Setup)

/-- A path of valid choice codes is a chain of at most `D` merges. -/
theorem pathOK_chainOK {D : ℕ} (he : 2 * S.K = 2 ^ 2 ^ D) : ∀ chs, S.PathOK chs → S.ChainOK D chs
  | [], _ => trivial
  | i :: rest, ⟨hp, h4, h, hv⟩ => by
    refine ⟨pathOK_chainOK he rest hp, ?_, h, hv⟩
    obtain ⟨hq, -⟩ := S.q_path he rest hp
    by_contra hc
    rw [show D - rest.length = 0 by omega] at hq
    rw [hq] at h4
    norm_num at h4

end Cslib.Complexity.NtimeDspace.Cube.Setup

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset SumProduct

/-! ### Lists -/

/-- Entry `k` of the list coded by `n`. -/
def stGet (n k : ℕ) : ℕ := hdF (tlF^[k] n)

@[simp] theorem stGet_cons_zero (x : ℕ) (l : List ℕ) : stGet (NatList.enc (x :: l)) 0 = x := by
  simp [stGet]

@[simp] theorem stGet_cons_succ (x : ℕ) (l : List ℕ) (k : ℕ) :
    stGet (NatList.enc (x :: l)) (k + 1) = stGet (NatList.enc l) k := by
  simp only [stGet, Function.iterate_succ_apply, tlF_enc_cons]

/-- The code of the leaf `0`. -/
def zeroC : ℕ := NatList.enc [0]

/-- The code of the literal with zigzag code `z`. -/
def litC (z : ℕ) : ℕ := NatList.enc [1, z]

/-- `rangeSt` on codes: the literal `1`, a single factor, or a range. -/
def rangeN (mk : ℕ → ℕ) (mkR : ℕ → ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  if hi ≤ lo then litC 2 else if hi = lo + 1 then mk lo else mkR lo hi

theorem zz_zero : zz 0 = 0 := by norm_num [zz]

theorem zz_one : zz 1 = 2 := by norm_num [zz]

/-- `zz (a - b)` for naturals `a`, `b`. -/
def zzSub (a b : ℕ) : ℕ := if b ≤ a then 2 * (a - b) else 2 * (b - a) - 1

theorem zzSub_eq (a b : ℕ) : zzSub a b = zz ((a : ℤ) - b) := by
  unfold zzSub zz; split_ifs <;> omega

/-! ### Label codes -/

theorem msCode_zero : msCode 0 = [true] := by
  simp [msCode, distinctWts, gamma]

theorem lcode_zero : lcode (0, 0) = 3 := by
  show ofBits (msCode 0 ++ msCode 0) = 3
  rw [msCode_zero]; rfl

/-- The code of a label has at most `B` bits. -/
def LB (B : ℕ) (l : Label) : Prop := (msCode l.1).length + (msCode l.2).length ≤ B

theorem eq_zero_of_labelWt {l : Label} (h : labelWt l = 0) : l = (0, 0) := by
  have h1 := card_le_wt l.1
  have h2 := card_le_wt l.2
  unfold labelWt at h
  exact Prod.ext (Multiset.card_eq_zero.mp (by omega)) (Multiset.card_eq_zero.mp (by omega))

theorem codeWidth_mono {a b : ℕ} (h : a ≤ b) : codeWidth a ≤ codeWidth b := by
  unfold codeWidth
  split_ifs with ha hb hb
  · omega
  · omega
  · omega
  · exact Nat.add_le_add_right (Nat.sqrt_le_sqrt (by omega)) 2

theorem lb_of_le {B Φ : ℕ} {l : Label} (hl : labelWt l ≤ Φ) (hB : codeWidth Φ + 2 ≤ B) : LB B
    l := by
  unfold LB
  by_cases h0 : labelWt l = 0
  · rw [eq_zero_of_labelWt h0]; simp only [msCode_zero, List.length_singleton]; omega
  · have := msCode_length_le (a := labelWt l) (by omega) l le_rfl
    have := codeWidth_mono hl
    omega

theorem lcode_eq (l : Label) : lcode l = mcode l.1 + 2 ^ (msCode l.1).length * mcode l.2 :=
  ofBits_append _ _

theorem mcode_lt (σ : Multiset ℕ) : mcode σ < 2 ^ (msCode σ).length := ofBits_lt _

theorem lcode_mod (l : Label) : lcode l % 2 ^ (msCode l.1).length = mcode l.1 := by
  rw [lcode_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mcode_lt _)]

theorem lcode_div (l : Label) : lcode l / 2 ^ (msCode l.1).length = mcode l.2 := by
  rw [lcode_eq, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (mcode_lt _),
      Nat.zero_add]

theorem bits1 (l : Label) : BitsAt (lcode l) 0 (msCode l.1) :=
  (bitsAt_append.mp (bitsAt_ofBits (msCode l.1 ++ msCode l.2))).1

theorem bits2 (l : Label) : BitsAt (lcode l) (msCode l.1).length (msCode l.2) := by
  have := (bitsAt_append.mp (bitsAt_ofBits (msCode l.1 ++ msCode l.2))).2
  rwa [Nat.zero_add] at this

theorem msEnd_lcode {B : ℕ} {l : Label} (h : LB B l) : msEnd B (lcode l) 0 =
    (msCode l.1).length := by
  have := (msParse_msCode (bits1 l) (B := B) (by unfold LB at h; omega)).2.1
  rwa [Nat.zero_add] at this

theorem msEnd2_lcode {B : ℕ} {l : Label} (h : LB B l) :
    msEnd B (lcode l) (msCode l.1).length = (msCode l.1).length + (msCode l.2).length :=
  (msParse_msCode (bits2 l) (B := B) (by unfold LB at h; omega)).2.1

/-- **Codes of labels are canonical.** -/
theorem lcode_injective : Function.Injective lcode := by
  intro l l' h
  have ha : labelWt l + labelWt l' + 1 ≠ 0 := by omega
  have e1 := decode_labelCode (a := labelWt l + labelWt l' + 1) (l := l) (by omega)
  have e2 := decode_labelCode (a := labelWt l + labelWt l' + 1) (l := l') (by omega)
  rw [labelCode_eq_lcode ha] at e1 e2
  rw [h, e2] at e1
  exact (Option.some.inj e1).symm

theorem labelWtN_lcode {B : ℕ} {l : Label} (h : LB B l) : labelWtN B (lcode l) = labelWt l := by
  unfold labelWtN
  rw [msEnd_lcode h, wtN_msCode (bits1 l) (by unfold LB at h; omega),
    wtN_msCode (bits2 l) (by unfold LB at h; omega)]
  rfl

theorem cardN_lcode1 {B : ℕ} {l : Label} (h : LB B l) : cardN B (lcode l) 0 = Multiset.card l.1 :=
  cardN_msCode (bits1 l) (by unfold LB at h; omega)

theorem cardN_lcode2 {B : ℕ} {l : Label} (h : LB B l) :
    cardN B (lcode l) (msEnd B (lcode l) 0) = Multiset.card l.2 := by
  rw [msEnd_lcode h]; exact cardN_msCode (bits2 l) (by unfold LB at h; omega)

/-! ### Swapping and unpacking -/

/-- The code of `swapLabel l` from the code of `l`: its two multiset codes exchanged. -/
def swapN (B c : ℕ) : ℕ :=
  c / 2 ^ msEnd B c 0 + 2 ^ (msEnd B c (msEnd B c 0) - msEnd B c 0) * (c % 2 ^ msEnd B c 0)

theorem swapN_lcode {B : ℕ} {l : Label} (h : LB B l) : swapN B (lcode l) = lcode (swapLabel l) := by
  unfold swapN
  rw [msEnd_lcode h, msEnd2_lcode h, lcode_div, lcode_mod, Nat.add_sub_cancel_left]
  exact (lcode_eq (swapLabel l)).symm

theorem labelWt_swap (l : Label) : labelWt (swapLabel l) = labelWt l := by
  show wt l.2 + wt l.1 = wt l.1 + wt l.2; omega

theorem count_unpackDir {L s : ℕ} (hs : s < L) (σ : Multiset ℕ) (k : ℕ) :
    (unpackDir L σ s).count k = σ.count (L * k + s) := by
  unfold unpackDir
  rw [Multiset.count_map, Multiset.filter_filter, Multiset.count_eq_card_filter_eq]
  congr 1
  refine Multiset.filter_congr fun t _ => ?_
  constructor
  · rintro ⟨rfl, h2⟩
    rw [← h2]; exact Nat.div_add_mod t L
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_left s k (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]

theorem wt_unpackDir_le (L : ℕ) (σ : Multiset ℕ) (s : ℕ) : wt (unpackDir L σ s) ≤ wt σ := by
  unfold unpackDir
  have h1 : wt ((σ.filter fun t => t % L = s).map fun t => t / L) ≤ wt
      (σ.filter fun t => t % L = s) := by
    unfold wt
    rw [Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ fun t _ => by
      simp only [Function.comp_apply]; have := Nat.div_le_self t L; omega
  have h2 : wt (σ.filter fun t => t % L = s) ≤ wt σ := by
    have e := Multiset.filter_add_not (fun t => t % L = s) σ
    have : wt σ = wt (σ.filter fun t => t % L = s) + wt (σ.filter fun t => ¬ t % L = s) := by
      conv_lhs => rw [← e]
      unfold wt; rw [Multiset.map_add, Multiset.sum_add]
    omega
  omega

theorem labelWt_unpack_le (L : ℕ) (l : Label) (s : ℕ) : labelWt (unpack L l s) ≤ labelWt l := by
  have := wt_unpackDir_le L l.1 s
  have := wt_unpackDir_le L l.2 s
  show wt (unpackDir L l.1 s) + wt (unpackDir L l.2 s) ≤ wt l.1 + wt l.2; omega

theorem mem_unpackDir_le {L s e : ℕ} {σ : Multiset ℕ} (h : e ∈ unpackDir L σ s) : ∃ t ∈ σ, e ≤
    t := by
  unfold unpackDir at h
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp h
  exact ⟨t, (Multiset.mem_filter.mp ht).1, Nat.div_le_self t L⟩

/-- **Unpacking stream `s`** on a label code: in each direction, the multiset code with the
multiplicities of the types `L k + s`. -/
def unpackN (B L s c : ℕ) : ℕ :=
  (msOfCount B (topN B c 0) fun k => countN B c 0 (L * k + s)).1 +
    2 ^ (msOfCount B (topN B c 0) fun k => countN B c 0 (L * k + s)).2 *
      (msOfCount B (topN B c (msEnd B c 0)) fun k => countN B c (msEnd B c 0) (L * k + s)).1

theorem unpackN_lcode {B L s Φ : ℕ} {l : Label} (hs : s < L) (hl : labelWt l ≤ Φ)
    (hB : codeWidth Φ + 2 ≤ B) : unpackN B L s (lcode l) = lcode (unpack L l s) := by
  have hlb := lb_of_le hl hB
  have hlu := lb_of_le ((labelWt_unpack_le L l s).trans hl) hB
  have hlb' := hlb
  unfold LB at hlb' hlu
  simp only [unpack] at hlu
  have e1 : (msOfCount B (topN B (lcode l) 0) fun k => countN B (lcode l) 0 (L * k + s)) =
      (ofBits (msCode (unpackDir L l.1 s)), (msCode (unpackDir L l.1 s)).length) :=
    msOfCount_eq (fun k _ => by rw [countN_msCode (bits1 l) (by omega), count_unpackDir hs])
      (fun e he => by
        obtain ⟨t, ht, hle⟩ := mem_unpackDir_le he
        exact lt_of_le_of_lt hle (lt_topN_msCode (bits1 l) (by omega) ht)) (by omega)
  have e2 : (msOfCount B (topN B (lcode l) (msCode l.1).length)
      fun k => countN B (lcode l) (msCode l.1).length (L * k + s)) =
      (ofBits (msCode (unpackDir L l.2 s)), (msCode (unpackDir L l.2 s)).length) :=
    msOfCount_eq (fun k _ => by rw [countN_msCode (bits2 l) (by omega), count_unpackDir hs])
      (fun e he => by
        obtain ⟨t, ht, hle⟩ := mem_unpackDir_le he
        exact lt_of_le_of_lt hle (lt_topN_msCode (bits2 l) (by omega) ht)) (by omega)
  unfold unpackN
  rw [msEnd_lcode hlb, e1, e2]
  exact (ofBits_append _ _).symm

/-! ### Validity of a packed label, by scanning its code -/

theorem foldl_kill (P : ℕ × ℕ → Prop) [DecidablePred P] :
    ∀ (l : List (ℕ × ℕ)) (a : ℕ), l.foldl (fun a e => if P e then 0 else a) a =
      if ∃ e ∈ l, P e then 0 else a
  | [], a => by simp
  | e :: l, a => by
    rw [List.foldl_cons, foldl_kill P l]
    by_cases he : P e <;> by_cases hl : ∃ e' ∈ l, P e' <;> simp [he, hl]

theorem fold_ok (σ : Multiset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (entries σ).foldl (fun a e => if P e.1 then 0 else a) 1 = 1 ↔ ∀ t ∈ σ, ¬ P t := by
  rw [foldl_kill (fun e => P e.1)]
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨e, he, hp⟩ := h
    exact ⟨e.1, (mem_entries.mp he).1, hp⟩
  · simp only [true_iff]
    intro t ht hp
    exact h ⟨(t, σ.count t), mem_entries.mpr ⟨ht, rfl⟩, hp⟩

/-- **Validity of a packed label** (`validLabel L`), by a scan of its code: no type `≡ 0 (mod L)`
other than `0` in the first multiset, none in the second. -/
def labOkN (B L c : ℕ) : Prop :=
  msFoldN (fun a e _ => if e % L = 0 ∧ e ≠ 0 then 0 else a) 1 B c 0 = 1 ∧
    msFoldN (fun a e _ => if e % L = 0 then 0 else a) 1 B c (msEnd B c 0) = 1

instance (B L c : ℕ) : Decidable (labOkN B L c) := by unfold labOkN; infer_instance

theorem labOkN_lcode {B L : ℕ} {l : Label} (h : LB B l) : labOkN B L (lcode l) ↔ validLabel L
    l := by
  unfold labOkN validLabel
  rw [msFoldN_msCode (bits1 l) (by unfold LB at h; omega), msEnd_lcode h,
    msFoldN_msCode (bits2 l) (by unfold LB at h; omega)]
  rw [fold_ok l.1 (fun t => t % L = 0 ∧ t ≠ 0), fold_ok l.2 (fun t => t % L = 0)]
  refine and_congr ?_ Iff.rfl
  refine forall₂_congr fun t _ => ?_
  tauto

theorem validLabel_zero (L : ℕ) : validLabel L (0, 0) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;> simp at ht

/-! ### The code of the root transport state of a rectangle factor -/

/-- The code of `.tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) e` from the codes of
`x`, `y`, `m` and `zz e`. -/
def trRootN (B : ℕ) (up : Bool) (xC yC mC zc : ℕ) : ℕ :=
  NatList.enc [7, up.toNat, xC, yC, mC, 0,
    cardN B xC 0 + cardN B yC 0 + (if up then cardN B mC (msEnd B mC 0) else cardN B mC 0),
    NatList.enc [xC / 2 ^ msEnd B xC 0, yC / 2 ^ msEnd B yC 0,
      if up then mC % 2 ^ msEnd B mC 0 else mC / 2 ^ msEnd B mC 0], zc]

theorem tpart_add (up : Bool) (T₁ T₂ : Multiset (HPlace × ℕ)) (p : ℕ) :
    tpart up (T₁ + T₂) p = tpart up T₁ p + tpart up T₂ p := by
  unfold tpart; rw [Multiset.filter_add, Multiset.map_add]

theorem tpart_located (up : Bool) (pl : HPlace) (σ : Multiset ℕ) (p : ℕ) :
    tpart up (located pl σ) p = if pl = placeOf up p then σ else 0 := by
  unfold tpart located
  split_ifs with h
  · rw [Multiset.filter_eq_self.mpr (fun s
      hs => by obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hs; exact h),
      Multiset.map_map]
    exact Multiset.map_id' σ
  · rw [Multiset.filter_eq_nil.mpr (fun s
      hs => by obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hs; exact h)]
    rfl

theorem tcode_tgtMs (up : Bool) (x y m : Label) :
    tcode up (tgtMs up x y m) = NatList.enc
        [mcode x.2, mcode y.2, mcode (if up then m.1 else m.2)] := by
  cases up <;> simp [tcode, tgtMs, tpart_add, tpart_located, placeOf]

theorem length_srcList (up : Bool) (x y m : Label) :
    (srcList up x y m).length =
      Multiset.card x.1 + Multiset.card y.1 + Multiset.card (if up then m.2 else m.1) := by
  cases up <;> simp [srcList] <;> omega

theorem trRootN_eq (S : Setup) {B : ℕ} (up : Bool) {x y m : Label} (hx : LB B x) (hy : LB B y)
    (hm : LB B m) (e : ℤ) :
    trRootN B up (lcode x) (lcode y) (lcode m) (zz e) =
      S.code (.tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) e) := by
  have hd : ∀ {l : Label}, LB B l → lcode l / 2 ^ msEnd B (lcode l) 0 = mcode l.2 := fun h => by
    rw [msEnd_lcode h, lcode_div]
  have hmd : ∀ {l : Label}, LB B l → lcode l % 2 ^ msEnd B (lcode l) 0 = mcode l.1 := fun h => by
    rw [msEnd_lcode h, lcode_mod]
  simp only [Setup.code, trRootN, cardN_lcode1 hx, cardN_lcode1 hy, hd hx, hd hy, length_srcList,
    tcode_tgtMs]
  cases up <;> simp [cardN_lcode1 hm, cardN_lcode2 hm, hd hm, hmd hm]

/-! ### Budgets along a valid path -/

theorem pair_le_potential (C : Clique) {u v : Fin C.q} (h : u < v) : C.a u v ≤ C.potential := by
  have h1 : C.a u v ≤ ∑ p : Pairs C.q, C.a p.1.1 p.1.2 :=
    Finset.single_le_sum (f := fun p : Pairs C.q => C.a p.1.1 p.1.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨(u, v), h⟩)
  have hq : 1 ≤ (C.q - 1) ^ 2 :=
    Nat.one_le_pow _ _ (by have := v.isLt; have : u.val < v.val := h; omega)
  unfold Clique.potential
  calc C.a u v ≤ ∑ p : Pairs C.q, C.a p.1.1 p.1.2 := h1
    _ ≤ (C.q - 1) ^ 2 * ∑ p : Pairs C.q, C.a p.1.1 p.1.2 := Nat.le_mul_of_pos_left _ hq

theorem budget_le_potential (C : Clique) {u v : Fin C.q} (huv : u ≠ v) :
    budget C.a u v ≤ C.potential := by
  unfold budget
  rcases lt_or_gt_of_ne huv with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact pair_le_potential C h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact pair_le_potential C h

/-- **The budget sum along a valid path is at most `Φ₀ / 2^e`** for `2K = 2^(2^e)`
(`Setup.spair_mul_le`). -/
theorem spair_le_path (S : Setup) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {chs : List ℕ}
    (hp : S.PathOK chs) : (S.clique chs).spair ≤ S.C₀.potential / 2 ^ e :=
  (Nat.le_div_iff_mul_le (by positivity)).mpr (S.spair_mul_le he (S.pathOK_chainOK he chs hp))

/-- **Every budget along a valid path is at most `Φ₀ / 2^e`** for `2K = 2^(2^e)`. -/
theorem budget_le_path (S : Setup) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {chs : List ℕ}
    (hp : S.PathOK chs) :
    ∀ u v : Fin (S.clique chs).q, u ≠ v →
      budget (S.clique chs).a u v ≤ S.C₀.potential / 2 ^ e :=
  fun _ _ h => ((S.clique chs).budget_le_spair h).trans (spair_le_path S he hp)

/-- **Every budget along a valid path fits the field width.** -/
theorem fits_path (S : Setup) (hS : S.Good) {chs : List ℕ} (hp : S.PathOK chs) :
    Fits S.fw (S.clique chs).a := fun u v h => by
  have h1 := (pair_le_potential _ h).trans (S.potential_path chs hp)
  have h2 := hS.2.2
  have h3 : 2 ^ (S.fw - 1) ≤ 2 ^ S.fw := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### Labels of argument codes -/

/-- The label at `u` of an argument code `x` of node `v` (`(0, 0)` off the nodes). -/
def argLab (C : Clique) (v x u : ℕ) : Label :=
  if h : v < C.q ∧ u < C.q then decodeArgs C ⟨v, h.1⟩ x ⟨u, h.2⟩ else (0, 0)

/-- **The code of the label at `u`** of an argument code `x` of node `v`, from the budget array:
the field, if the budget is nonzero and the field decodes, else `lcode (0, 0) = 3`. -/
def argLabN (ar q fw v x u : ℕ) : ℕ :=
  if v < q ∧ u < q ∧ u ≠ v then
    (if budgetN ar q fw v u ≠ 0 ∧ validN (budgetN ar q fw v u) (codeWidth (budgetN ar q fw v u))
        (x / 2 ^ argOffN ar q fw v u % 2 ^ codeWidth (budgetN ar q fw v u)) = 1 then
      x / 2 ^ argOffN ar q fw v u % 2 ^ codeWidth (budgetN ar q fw v u) else 3)
  else 3

theorem argLabN_eq (C : Clique) {fw : ℕ} (hf : Fits fw C.a) (v x u : ℕ) :
    argLabN (arrN C.q fw (extN C.a)) C.q fw v x u = lcode (argLab C v x u) := by
  unfold argLabN argLab
  by_cases h : v < C.q ∧ u < C.q
  · rw [dite_eq_left h]
    by_cases huv : u = v
    · rw [ite_eq_right (fun h' => h'.2.2 huv), decodeArgs_eq, ite_eq_left (Fin.ext huv), lcode_zero]
    · have hb : budgetN (arrN C.q fw (extN C.a)) C.q fw v u = budget C.a ⟨v, h.1⟩ ⟨u, h.2⟩ :=
        budgetN_ext hf (u := ⟨v, h.1⟩) (v := ⟨u, h.2⟩) (fun e => huv (congrArg Fin.val e).symm)
      have hfo : fieldOf C ⟨v, h.1⟩ ⟨u, h.2⟩ x =
          x / 2 ^ argOffset C v u % 2 ^ codeWidth (budget C.a ⟨v, h.1⟩ ⟨u, h.2⟩) := rfl
      rw [ite_eq_left ⟨h.1, h.2, huv⟩, hb, argOffN_eq C hf, decodeArgs_eq,
        ite_eq_right (fun e => huv (congrArg Fin.val e)), hfo]
      generalize budget C.a ⟨v, h.1⟩ ⟨u, h.2⟩ = b
      have hlt : x / 2 ^ argOffset C v u % 2 ^ codeWidth b < 2 ^ codeWidth b := Nat.mod_lt _
          (by positivity)
      generalize x / 2 ^ argOffset C v u % 2 ^ codeWidth b = fld at hlt ⊢
      rw [validN_eq hlt]
      rcases hd : decodeLabel b fld with _ | l
      · simp [lcode_zero]
      · by_cases hb0 : b = 0
        · subst hb0
          simp only [decodeLabel, ↓reduceIte] at hd
          split_ifs at hd
          obtain rfl := (Option.some.inj hd).symm
          simp [lcode_zero]
        · obtain ⟨-, hc⟩ := labelCode_decode hlt hd
          rw [labelCode_eq_lcode hb0] at hc
          simp [hb0, hc]
  · rw [dite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩), lcode_zero]

theorem labelWt_argLab_le (C : Clique) {Φ : ℕ} (hΦ : ∀ u v : Fin C.q, u ≠ v → budget C.a u v ≤ Φ)
    (v x u : ℕ) : labelWt (argLab C v x u) ≤ Φ := by
  unfold argLab
  split_ifs with h
  · by_cases he : (⟨u, h.2⟩ : Fin C.q) = ⟨v, h.1⟩
    · rw [decodeArgs_eq, ite_eq_left he]; simp [labelWt]
    · exact (labelWt_decodeArgs_le C _ _ x).trans (hΦ _ _ (Ne.symm he))
  · simp [labelWt]

theorem copyAt_eq_argLab (C : Clique) (nodes : ℕ → ℕ) (ξ p u : ℕ) :
    copyAt C nodes ξ p u = argLab C (nodes p) (slice C nodes ξ p) u := rfl

theorem Θof_eq_argLab (Cc : Clique) (v args o : ℕ) : Θof Cc v args o = argLab Cc v args o := by
  unfold Θof argLab
  by_cases h : o < Cc.q ∧ v < Cc.q
  · rw [dite_eq_left h, dite_eq_left ⟨h.2, h.1⟩]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]

/-! ### Validity of copies and of arguments -/

/-- **All copies decode to labels of exact weight** (`CopiesValid`), from the array. -/
def copiesOkN (ar q fw g : ℕ) (nodes : ℕ → ℕ) (ξ : ℕ) : Prop :=
  ∀ p < g, nodes p < q → ∀ u < q, u ≠ nodes p →
    validN (budgetN ar q fw (nodes p) u) (codeWidth (budgetN ar q fw (nodes p) u))
        (sliceN ar q fw nodes ξ p / 2 ^ argOffN ar q fw (nodes p) u %
          2 ^ codeWidth (budgetN ar q fw (nodes p) u)) = 1 ∧
      labelWtN (codeWidth (budgetN ar q fw (nodes p) u))
        (sliceN ar q fw nodes ξ p / 2 ^ argOffN ar q fw (nodes p) u %
          2 ^ codeWidth (budgetN ar q fw (nodes p) u)) = budgetN ar q fw (nodes p) u

instance (ar q fw g : ℕ) (nodes : ℕ → ℕ) (ξ : ℕ) : Decidable (copiesOkN ar q fw g nodes ξ) := by
  unfold copiesOkN; infer_instance

theorem exact_iff {b fld : ℕ} (hlt : fld < 2 ^ codeWidth b) :
    (validN b (codeWidth b) fld = 1 ∧ labelWtN (codeWidth b) fld = b) ↔
      ∃ l, decodeLabel b fld = some l ∧ labelWt l = b := by
  rw [validN_eq hlt]
  by_cases hb : b = 0
  · subst hb
    have h0 : fld = 0 := by simpa [codeWidth] using hlt
    subst h0
    simp [decodeLabel, labelWtN, wtN, msN, labelWt, codeWidth]
  · rcases hd : decodeLabel b fld with _ | l
    · simp
    · have := labelWtN_decode hlt hd
      simp [this]

theorem copiesOkN_iff (C : Clique) {fw : ℕ} (hf : Fits fw C.a) (nodes : ℕ → ℕ) (g ξ : ℕ) :
    copiesOkN (arrN C.q fw (extN C.a)) C.q fw g nodes ξ ↔ CopiesValid C nodes g ξ := by
  unfold copiesOkN CopiesValid
  constructor
  · intro H p hp w u hw hu
    have hpw : nodes p < C.q := hw ▸ w.isLt
    have hb := budgetN_ext hf (u := w) (v := u) (fun e => hu e.symm)
    obtain ⟨h1, h2⟩ := H p hp hpw u u.isLt (fun e => hu (Fin.ext (e.trans hw.symm)))
    rw [← hw, hb, argOffN_eq C hf, sliceN_eq C hf] at h1 h2
    exact (exact_iff (Nat.mod_lt _ (by positivity))).mp ⟨h1, h2⟩
  · intro H p hp hpq u hu hne
    have := H p hp ⟨nodes p, hpq⟩ ⟨u, hu⟩ rfl (fun e => hne (congrArg Fin.val e))
    have hb : budgetN (arrN C.q fw (extN C.a)) C.q fw (nodes p) u =
        budget C.a ⟨nodes p, hpq⟩ ⟨u, hu⟩ :=
      budgetN_ext hf (u := ⟨nodes p, hpq⟩) (v := ⟨u, hu⟩) (fun e => hne (congrArg Fin.val e).symm)
    rw [hb, argOffN_eq C hf, sliceN_eq C hf]
    exact (exact_iff (Nat.mod_lt _ (by positivity))).mpr this

/-- **The labels of an argument code are valid packed labels** (`ArgsValid`), by scanning. -/
def argsOkN (B fw ar q L v x : ℕ) : Prop := ∀ u < q, labOkN B L (argLabN ar q fw v x u)

instance (B fw ar q L v x : ℕ) : Decidable (argsOkN B fw ar q L v x) := by
  unfold argsOkN; infer_instance

theorem argsOkN_iff (C : Clique) {fw B Φ : ℕ} (hf : Fits fw C.a)
    (hΦ : ∀ u v : Fin C.q, u ≠ v → budget C.a u v ≤ Φ) (hB : codeWidth Φ + 2 ≤ B) (L v x : ℕ) :
    argsOkN B fw (arrN C.q fw (extN C.a)) C.q L v x ↔ Setup.ArgsValid C v x L := by
  have e : ∀ u, labOkN B L (argLabN (arrN C.q fw (extN C.a)) C.q fw v x u) ↔
      validLabel L (argLab C v x u) := fun u => by
    rw [argLabN_eq C hf]; exact labOkN_lcode (lb_of_le (labelWt_argLab_le C hΦ v x u) hB)
  unfold argsOkN
  simp only [e]
  constructor
  · intro H w u hw hu
    subst hw
    have := H u u.isLt
    unfold argLab at this
    rwa [dite_eq_left ⟨w.isLt, u.isLt⟩] at this
  · intro H u _
    unfold argLab
    split_ifs with h
    · rw [decodeArgs_eq]
      split_ifs with he
      · exact validLabel_zero L
      · have := H ⟨v, h.1⟩ ⟨u, h.2⟩ rfl he
        rwa [decodeArgs_eq, ite_eq_right he] at this
    · exact validLabel_zero L

/-! ### The rectangle factor -/

/-- The stream of the rectangle on columns `B < B'` (`rStream`). -/
def rStreamN (g B B' : ℕ) : ℕ := 1 + g + ((∑ b ∈ range B, (g - 1 - b)) + (B' - B - 1))

theorem rowTest_iff (w H D Q : ℕ) :
    ((w : ℤ) ≤ (H : ℤ) + ((D : ℤ) - (Q : ℤ)) / 2) ↔ 2 * w + Q ≤ 2 * H + D := by omega

theorem colTest_iff (w H D Q : ℕ) :
    ((w : ℤ) ≤ (H : ℤ) - ((D : ℤ) - (Q : ℤ)) / 2) ↔ D + 2 * w ≤ 2 * H + Q + 1 := by omega

theorem zz_kc (D Cs Q : ℕ) : zzSub D Cs = zz (((D : ℤ) - Q) - ((Cs : ℤ) - Q)) := by
  rw [zzSub_eq]; congr 1; ring

theorem zz_nkc (D Cs Q : ℕ) : zzSub (2 * Q) (D + Cs) = zz (-((D : ℤ) - Q) - ((Cs : ℤ) - Q)) := by
  rw [zzSub_eq]; congr 1; push_cast; ring

/-- **The code of the rectangle factor** at the quadruple `(A₁, A₂, B₁, B₂)` (`psiG`), from the
parent array `ar` on `q = g·g` nodes, the choice code `i`, the orientation, and the codes `cp p u`
of the copies and `th o` of the packed labels. -/
def psiN (B fw ar q g i : ℕ) (row : Bool) (v : ℕ) (cp : ℕ → ℕ → ℕ) (th : ℕ → ℕ)
    (A₁ A₂ B₁ B₂ : ℕ) : ℕ :=
  if A₁ < A₂ ∧ B₁ < B₂ ∧ A₂ < g ∧ B₂ < g then
    let x := ((A₁ * g + A₂) * g + B₁) * g + B₂
    let D := digitN fw i (2 * x)
    let Cs := digitN fw i (2 * x + 1)
    let Q := 2 ^ (fw - 1)
    let H := diagN ar q fw g x
    if row then
      if v = A₁ then
        if 2 * labelWtN B (unpackN B (packL g) (rStreamN g B₁ B₂) (th A₂)) + Q ≤ 2 * H + D then
          trRootN B true (cp B₁ (A₂ * g + B₂)) (cp B₂ (A₂ * g + B₁))
            (unpackN B (packL g) (rStreamN g B₁ B₂) (th A₂)) (zzSub D Cs)
        else zeroC
      else if v = A₂ then
        if 2 * labelWtN B (unpackN B (packL g) (rStreamN g B₁ B₂) (th A₁)) + Q ≤ 2 * H + D then
          trRootN B false (swapN B (cp B₁ (A₁ * g + B₂))) (swapN B (cp B₂ (A₁ * g + B₁)))
            (unpackN B (packL g) (rStreamN g B₁ B₂) (th A₁)) (zzSub Cs Q)
        else zeroC
      else litC 2
    else
      if v = B₁ then
        if D + 2 * labelWtN B (unpackN B (packL g) (rStreamN g A₁ A₂) (th B₂)) ≤ 2 * H + Q + 1 then
          trRootN B true (cp A₁ (A₂ * g + B₂)) (swapN B (cp A₂ (A₁ * g + B₂)))
            (unpackN B (packL g) (rStreamN g A₁ A₂) (th B₂)) (zzSub (2 * Q) (D + Cs))
        else zeroC
      else if v = B₂ then
        if D + 2 * labelWtN B (unpackN B (packL g) (rStreamN g A₁ A₂) (th B₁)) ≤ 2 * H + Q + 1 then
          trRootN B false (cp A₁ (A₂ * g + B₁)) (swapN B (cp A₂ (A₁ * g + B₁)))
            (unpackN B (packL g) (rStreamN g A₁ A₂) (th B₁)) (zzSub Cs Q)
        else zeroC
      else litC 2
  else litC 2

theorem split_eq {g fw i : ℕ} (r : Rect g) :
    (decodeChoice g fw i r).2 = (digitN fw i (2 * rectIdx r + 1) : ℤ) -
        ((2 ^ (fw - 1) : ℕ) : ℤ) := by
  show field fw i (2 * rectIdx r + 1) = _
  rw [field_eq_digitN]; push_cast; rfl

theorem rStreamN_lt {g B B' : ℕ} (h : B < B') (h' : B' < g) : rStreamN g B B' < packL g := by
  have := MergeProof.pairRank_lt_choose (g := g) (B := ⟨B, by omega⟩) (B' := ⟨B', h'⟩) h
  unfold pairRank at this
  dsimp only at this
  unfold packL rStreamN; omega

theorem code_zero (S : Setup) : S.code .zero = zeroC := rfl

theorem code_lit (S : Setup) (w : ℤ) : S.code (.lit w) = litC (zz w) := rfl

theorem trRoot_code (S : Setup) {B : ℕ} (up : Bool) {x y m : Label} (hx : LB B x) (hy : LB B y)
    (hm : LB B m) (e : ℤ) :
    S.code (.tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) e) =
      trRootN B up (lcode x) (lcode y) (lcode m) (zz e) := (trRootN_eq S up hx hy hm e).symm

theorem code_psiG (S : Setup) {B fw g i Φ : ℕ} {a : Fin (g * g) → Fin (g * g) → ℕ} (hf : Fits fw a)
    (P Cc : Clique) (row : Bool) (v args ξ : ℕ) (cp : ℕ → ℕ → ℕ) (th : ℕ → ℕ)
    (hB : codeWidth Φ + 2 ≤ B)
    (hcp : ∀ p u, cp p u = lcode (copyAt P (Setup.holders g v row) ξ p u))
    (hcw : ∀ p u, labelWt (copyAt P (Setup.holders g v row) ξ p u) ≤ Φ)
    (hth : ∀ o, th o = lcode (Θof Cc v args o)) (htw : ∀ o, labelWt (Θof Cc v args o) ≤ Φ)
    (A₁ A₂ B₁ B₂ : ℕ) :
    S.code (psiG P Cc g a (decodeChoice g fw i) row v args ξ A₁ A₂ B₁ B₂) =
      psiN B fw (arrN (g * g) fw (extN a)) (g * g) g i row v cp th A₁ A₂ B₁ B₂ := by
  unfold psiG psiN
  by_cases h : A₁ < A₂ ∧ B₁ < B₂ ∧ A₂ < g ∧ B₂ < g
  swap
  · rw [dite_eq_right h, ite_eq_right h, code_lit, zz_one]
  rw [dite_eq_left h, ite_eq_left h]
  dsimp only
  have hH : diagWt a ⟨((⟨A₁, by omega⟩, ⟨A₂, h.2.2.1⟩), (⟨B₁, by omega⟩, ⟨B₂, h.2.2.2⟩)), h.1,
      h.2.1⟩ =
      diagN (arrN (g * g) fw (extN a)) (g * g) fw g (((A₁ * g + A₂) * g + B₁) * g + B₂) :=
    (diagN_eq hf _).symm
  have hk : (decodeChoice g fw i
      ⟨((⟨A₁, by omega⟩, ⟨A₂, h.2.2.1⟩), (⟨B₁, by omega⟩, ⟨B₂, h.2.2.2⟩)), h.1, h.2.1⟩).1 =
      (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂)) : ℤ) - ((2 ^ (fw - 1) : ℕ) : ℤ) :=
    grade_eq _
  have hc : (decodeChoice g fw i
      ⟨((⟨A₁, by omega⟩, ⟨A₂, h.2.2.1⟩), (⟨B₁, by omega⟩, ⟨B₂, h.2.2.2⟩)), h.1, h.2.1⟩).2 =
      (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂) + 1) : ℤ) - ((2 ^ (fw - 1) : ℕ) : ℤ) :=
    split_eq _
  have hsB : rStream g ⟨B₁, by omega⟩ ⟨B₂, h.2.2.2⟩ = rStreamN g B₁ B₂ := rfl
  have hsA : rStream g ⟨A₁, by omega⟩ ⟨A₂, h.2.2.1⟩ = rStreamN g A₁ A₂ := rfl
  have hu : ∀ o s, s < packL g →
      unpackN B (packL g) s (th o) = lcode (unpack (packL g) (Θof Cc v args o) s) :=
    fun o s hs => by rw [hth]; exact unpackN_lcode hs (htw o) hB
  have hwU : ∀ o s, labelWt (unpack (packL g) (Θof Cc v args o) s) ≤ Φ :=
    fun o s => (labelWt_unpack_le _ _ _).trans (htw o)
  have hlw : ∀ o s, labelWtN B (lcode (unpack (packL g) (Θof Cc v args o) s)) =
      labelWt (unpack (packL g) (Θof Cc v args o) s) := fun o
          s => labelWtN_lcode (lb_of_le (hwU o s) hB)
  have hsw : ∀ p u, swapN B (lcode (copyAt P (Setup.holders g v row) ξ p u)) =
      lcode (swapLabel (copyAt P (Setup.holders g v row) ξ p u)) :=
    fun p u => swapN_lcode (lb_of_le (hcw p u) hB)
  have lbc : ∀ p u, LB B (copyAt P (Setup.holders g v row) ξ p u) := fun p
      u => lb_of_le (hcw p u) hB
  have lbs : ∀ p u, LB B (swapLabel (copyAt P (Setup.holders g v row) ξ p u)) := fun p u =>
    lb_of_le ((labelWt_swap _).trans_le (hcw p u)) hB
  have lbu : ∀ o s, LB B (unpack (packL g) (Θof Cc v args o) s) := fun o s => lb_of_le (hwU o s) hB
  rw [hu A₂ _ (rStreamN_lt h.2.1 h.2.2.2), hu A₁ _ (rStreamN_lt h.2.1 h.2.2.2),
    hu B₂ _ (rStreamN_lt h.1 h.2.2.1), hu B₁ _ (rStreamN_lt h.1 h.2.2.1),
    zz_kc (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂)))
      (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂) + 1)) (2 ^ (fw - 1)),
    zz_nkc (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂)))
      (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂) + 1)) (2 ^ (fw - 1)),
    zzSub_eq (digitN fw i (2 * (((A₁ * g + A₂) * g + B₁) * g + B₂) + 1)) (2 ^ (fw - 1))]
  simp only [apply_ite S.code, hH, hk, hc, hsB, hsA, hlw, hcp, hsw, rowTest_iff, colTest_iff,
    trRoot_code S (B := B), lbc, lbs, lbu, code_zero, code_lit, zz_one]

/-! ### The factor states -/

/-- **The code of a factor state** (`factorG`): an old table entry, a test, or a rectangle factor.
The parent array is `arP` on `qP` nodes (`g × g`), `rC`, `cR` are the codes of the path and of the
cache one level up, and `cp`, `th` give the codes of the copies and of the packed labels. -/
def factorGN (B fw rC cR arP qP g i : ℕ) (row : Bool) (v ξ : ℕ) (cp : ℕ → ℕ → ℕ) (th : ℕ → ℕ)
    (f : ℕ) : ℕ :=
  if f < g then NatList.enc [4, rC, cR, Setup.holders g v row f,
    sliceN arP qP fw (Setup.holders g v row) ξ f]
  else if f < g + g * g then
    litC (if (f - g) / g < (f - g) % g ∧
        cp ((f - g) / g) (Setup.holders g v row ((f - g) % g)) ≠
          cp ((f - g) % g) (Setup.holders g v row ((f - g) / g)) then 0 else 2)
  else if f < g + g * g + g * g then
    litC (if (f - g - g * g) / g ≠ v ∧
        cp ((f - g - g * g) % g) (if row = true then (f - g - g * g) / g * g + (f - g - g * g) % g
          else (f - g - g * g) % g * g + (f - g - g * g) / g) ≠
          unpackN B (packL g) (1 + (f - g - g * g) % g) (th ((f - g - g * g) / g)) then 0 else 2)
  else
    psiN B fw arP qP g i row v cp th (qd g (f - g - g * g - g * g) 3)
        (qd g (f - g - g * g - g * g) 2)
      (qd g (f - g - g * g - g * g) 1) (qd g (f - g - g * g - g * g) 0)

theorem lcode_ne_iff (x y : Label) : lcode x ≠ lcode y ↔ x ≠ y := lcode_injective.ne_iff

theorem code_factorG (S : Setup) {B fw g i Φ : ℕ} {a : Fin (g * g) → Fin (g * g) → ℕ}
    (hf : Fits fw a) (rest : List ℕ) (P Cc : Clique) (hfP : Fits fw P.a) (hq : P.q = g * g)
    (harr : arrN P.q fw (extN P.a) = arrN (g * g) fw (extN a))
    (row : Bool) (v args ξ : ℕ) (cp : ℕ → ℕ → ℕ) (th : ℕ → ℕ) (hB : codeWidth Φ + 2 ≤ B)
    (hcp : ∀ p u, cp p u = lcode (copyAt P (Setup.holders g v row) ξ p u))
    (hcw : ∀ p u, labelWt (copyAt P (Setup.holders g v row) ξ p u) ≤ Φ)
    (hth : ∀ o, th o = lcode (Θof Cc v args o)) (htw : ∀ o, labelWt (Θof Cc v args o) ≤ Φ)
    (f : ℕ) :
    S.code (factorG rest P Cc g a (decodeChoice g fw i) row v args ξ f) =
      factorGN B fw (NatList.enc rest) (S.cacheC rest) (arrN P.q fw (extN P.a)) P.q g i row v ξ cp
          th f := by
  unfold factorG factorGN
  dsimp only
  by_cases h1 : f < g
  · rw [ite_eq_left h1, ite_eq_left h1]
    simp only [Setup.code]
    rw [sliceN_eq P hfP]
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : f < g + g * g
  · rw [ite_eq_left h2, ite_eq_left h2]
    simp only [code_lit, hcp, lcode_ne_iff, apply_ite zz, zz_zero, zz_one]
  rw [ite_eq_right h2, ite_eq_right h2]
  by_cases h3 : f < g + g * g + g * g
  · rw [ite_eq_left h3, ite_eq_left h3]
    have hg : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · subst h0; omega
      · exact h0
    have hs : 1 + (f - g - g * g) % g < packL g := by
      have := Nat.mod_lt (f - g - g * g) hg; unfold packL; omega
    rw [hth, unpackN_lcode hs (htw _) hB]
    simp only [code_lit, hcp, lcode_ne_iff, apply_ite zz, zz_zero, zz_one]
  rw [ite_eq_right h3, ite_eq_right h3, Num.quad_eq]
  dsimp only
  rw [harr, hq]
  exact code_psiG S hf P Cc row v args ξ cp th hB hcp hcw hth htw _ _ _ _

/-! ### Caches -/

/-- The node count of the first clique of a cache. -/
def cQ (c : ℕ) : ℕ := stGet (stGet c 0) 0

/-- The budget array of the first clique of a cache. -/
def cA (c : ℕ) : ℕ := stGet (stGet c 0) 1

/-- The node count of the second clique of a cache (the parent). -/
def pQ (c : ℕ) : ℕ := stGet (stGet c 1) 0

/-- The budget array of the second clique of a cache. -/
def pA (c : ℕ) : ℕ := stGet (stGet c 1) 1

section Cache

variable (S : Setup)

theorem stGet_cacheC (chs : List ℕ) : stGet (S.cacheC chs) 0 = S.arrAt chs := by
  cases chs <;> simp [Setup.cacheC, Setup.cacheL]

theorem cQ_eq (chs : List ℕ) : cQ (S.cacheC chs) = (S.clique chs).q := by
  unfold cQ; rw [stGet_cacheC]; simp [Setup.arrAt]

theorem cA_eq (chs : List ℕ) :
    cA (S.cacheC chs) = arrN (S.clique chs).q S.fw (extN (S.clique chs).a) := by
  unfold cA; rw [stGet_cacheC]; simp [Setup.arrAt]

theorem tlF_cacheC (i : ℕ) (rest : List ℕ) : tlF (S.cacheC (i :: rest)) = S.cacheC rest := by
  simp [Setup.cacheC, Setup.cacheL]

theorem pQ_eq (i : ℕ) (rest : List ℕ) : pQ (S.cacheC (i :: rest)) = (S.clique rest).q := by
  unfold pQ
  have : stGet (S.cacheC (i :: rest)) 1 = stGet (S.cacheC rest) 0 := by
    simp [Setup.cacheC, Setup.cacheL]
  rw [this, stGet_cacheC]; simp [Setup.arrAt]

theorem pA_eq (i : ℕ) (rest : List ℕ) :
    pA (S.cacheC (i :: rest)) = arrN (S.clique rest).q S.fw (extN (S.clique rest).a) := by
  unfold pA
  have : stGet (S.cacheC (i :: rest)) 1 = stGet (S.cacheC rest) 0 := by
    simp [Setup.cacheC, Setup.cacheL]
  rw [this, stGet_cacheC]; simp [Setup.arrAt]

end Cache

theorem orientN_recast {g fw i : ℕ} (C : Clique) (hsq : C.q = g * g) (h : Fits fw C.a)
    (he : ∀ r, Even (decodeChoice g fw i r).1) :
    orientN (arrN C.q fw (extN C.a)) C.q fw g i =
      orientRow (C.recast _ hsq).a fun r => (decodeChoice g fw i r).1 := by
  have e : ∀ n (hn : C.q = n),
      orientN (arrN n fw (extN (q := n) (C.recast n hn).a)) n fw g i =
      orientN (arrN C.q fw (extN C.a)) C.q fw g i := by
    intro n hn; subst hn; rfl
  exact (e _ hsq).symm.trans (orientN_eq (h.recast _ hsq) he)

theorem validN_recast {g fw i : ℕ} (C : Clique) (hsq : C.q = g * g) (h : Fits fw C.a) (hfw : 1 ≤ fw)
    :
    ValidN (arrN C.q fw (extN C.a)) C.q fw g i ↔ ValidChoiceCode (C.recast _ hsq).a fw i := by
  have e : ∀ n (hn : C.q = n),
      ValidN (arrN n fw (extN (q := n) (C.recast n hn).a)) n fw g i ↔
      ValidN (arrN C.q fw (extN C.a)) C.q fw g i := by
    intro n hn; subst hn; exact Iff.rfl
  exact (e _ hsq).symm.trans (validN_iff (h.recast _ hsq) hfw)

theorem arr_recast {fw : ℕ} (C : Clique) {n : ℕ} (h : C.q = n) :
    arrN C.q fw (extN C.a) = arrN n fw (extN (C.recast n h).a) :=
  (congrArg (fun m => arrN m fw (extN C.a)) h).trans (congrArg (arrN n fw) (extN_recast C n h).symm)

/-- **The code of a factor state of an entry**, from the codes of the path `i :: rest` and of its
cache (the child array first, the parent array second). -/
def factorN (fw B chC c v x ξ f : ℕ) : ℕ :=
  if pQ c = Nat.sqrt (pQ c) * Nat.sqrt (pQ c) then
    factorGN B fw (tlF chC) (tlF c) (pA c) (pQ c) (Nat.sqrt (pQ c)) (stGet chC 0)
      (orientN (pA c) (pQ c) fw (Nat.sqrt (pQ c)) (stGet chC 0)) v ξ
      (fun p u => argLabN (pA c) (pQ c) fw
        (Setup.holders (Nat.sqrt (pQ c)) v
            (orientN (pA c) (pQ c) fw (Nat.sqrt (pQ c)) (stGet chC 0)) p)
        (sliceN (pA c) (pQ c) fw
          (Setup.holders (Nat.sqrt (pQ c)) v
              (orientN (pA c) (pQ c) fw (Nat.sqrt (pQ c)) (stGet chC 0))) ξ p) u)
      (fun o => argLabN (cA c) (cQ c) fw v x o) f
  else zeroC

section States

variable (S : Setup)

theorem code_factorSt (hS : S.Good) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {B : ℕ}
    (hB : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B) (rest : List ℕ)
    (i : ℕ) (hp : S.PathOK (i :: rest)) (v args ξ f : ℕ) :
    S.code (S.factorSt rest i v args ξ f) =
      factorN S.fw B (NatList.enc (i :: rest)) (S.cacheC (i :: rest)) v args ξ f := by
  have hp0 := hp
  obtain ⟨hp', -, h, hvc⟩ := hp
  have hfP := fits_path S hS hp'
  have hfC := fits_path S hS hp0
  rw [S.factorSt_eq rest i v args ξ f h]
  unfold factorN
  rw [pQ_eq, pA_eq, cA_eq, cQ_eq, tlF_cacheC, tlF_enc_cons, stGet_cons_zero, ite_eq_left h,
    orientN_recast (S.clique rest) h hfP (fun r => ValidChoiceCode.even hvc r)]
  refine code_factorG S (hfP.recast _ h) rest (S.clique rest) (S.clique (i :: rest)) hfP h
    (arr_recast (S.clique rest) h) _ v args ξ _ _ hB (fun p u => ?_) (fun p u => ?_) (fun o => ?_)
    (fun o => ?_) f
  · rw [argLabN_eq _ hfP, sliceN_eq _ hfP]; rfl
  · rw [copyAt_eq_argLab]; exact labelWt_argLab_le _ (budget_le_path S he hp') _ _ _
  · rw [argLabN_eq _ hfC, Θof_eq_argLab]
  · rw [Θof_eq_argLab]; exact labelWt_argLab_le _ (budget_le_path S he hp0) _ _ _

theorem code_cl (chs : List ℕ) : S.code (.cl chs) = NatList.enc
    [2, NatList.enc chs, S.cacheC chs] := rfl

theorem code_last (chs : List ℕ) (i : ℕ) :
    S.code (.last chs i) = NatList.enc [3, NatList.enc chs, S.cacheC chs, i] := rfl

theorem code_ent (chs : List ℕ) (v x : ℕ) :
    S.code (.ent chs v x) = NatList.enc [4, NatList.enc chs, S.cacheC chs, v, x] := rfl

theorem code_rng (chs : List ℕ) (v x ξ lo hi : ℕ) :
    S.code (.rng chs v x ξ lo hi) = NatList.enc
        [5, NatList.enc chs, S.cacheC chs, v, x, ξ, lo, hi] := rfl

theorem code_rangeSt (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi : ℕ) :
    S.code (Setup.rangeSt mk mkR lo hi) =
      rangeN (fun f => S.code (mk f)) (fun a b => S.code (mkR a b)) lo hi := by
  unfold Setup.rangeSt rangeN; split_ifs <;> rfl

/-! #### Clique states -/

/-- The tag of a clique state: a sum node at two nodes or at `g × g ≥ 4` nodes. -/
def clTagN (n : ℕ) : ℕ :=
  if cQ (stGet n 2) = 2 ∨ (4 ≤ cQ (stGet n 2) ∧
      cQ (stGet n 2) = Nat.sqrt (cQ (stGet n 2)) * Nat.sqrt (cQ (stGet n 2))) then 1 else 0

/-- The width of a clique state: the code width of the one budget, or the choice width. -/
def clWidthN (fw n : ℕ) : ℕ :=
  if cQ (stGet n 2) = 2 then codeWidth (budgetN (cA (stGet n 2)) (cQ (stGet n 2)) fw 0 1)
  else choiceWidth (Nat.sqrt (cQ (stGet n 2))) fw

/-- The child of a clique state: `last` at a code of a label of exact weight (two nodes), or the
clique one level down at a valid choice code, with the child array pushed on the cache. -/
def clChildN (fw n i : ℕ) : ℕ :=
  let c := stGet n 2
  let q := cQ c
  if q = 2 then
    let b := budgetN (cA c) q fw 0 1
    if (b = 0 ∧ i = 0) ∨ (b ≠ 0 ∧ validN b (codeWidth b) (i % 2 ^ codeWidth b) = 1 ∧
        labelWtN (codeWidth b) (i % 2 ^ codeWidth b) = b) then NatList.enc [3, stGet n 1, c, i]
    else zeroC
  else if q = Nat.sqrt q * Nat.sqrt q then
    if ValidN (cA c) q fw (Nat.sqrt q) i then
      NatList.enc [2, consF i (stGet n 1),
        consF (NatList.enc [Nat.sqrt q, childN (cA c) q fw (Nat.sqrt q) i]) c]
    else zeroC
  else zeroC

theorem clTagN_eq (chs : List ℕ) : clTagN (S.code (.cl chs)) = AGen.kindTag
    (S.gen.kind (.cl chs)) := by
  rw [code_cl]
  simp only [clTagN, stGet_cons_zero, stGet_cons_succ, cQ_eq]
  show _ = AGen.kindTag (if (S.clique chs).q = 2 then Kind.sum else
    if 4 ≤ (S.clique chs).q ∧ (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt
        (S.clique chs).q
    then .sum else .leaf)
  by_cases h1 : (S.clique chs).q = 2
  · rw [ite_eq_left (Or.inl h1), ite_eq_left h1]; rfl
  · by_cases h2 : 4 ≤ (S.clique chs).q ∧
        (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q
    · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_left h2]; rfl
    · rw [ite_eq_right (fun h => h.elim h1 h2), ite_eq_right h1, ite_eq_right h2]; rfl

theorem clWidthN_eq (chs : List ℕ) (hf : Fits S.fw (S.clique chs).a) :
    clWidthN S.fw (S.code (.cl chs)) = S.gen.width (.cl chs) := by
  rw [code_cl]
  simp only [clWidthN, stGet_cons_zero, stGet_cons_succ, cQ_eq, cA_eq]
  show _ = if h : (S.clique chs).q = 2 then codeWidth ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩)
    else choiceWidth (Nat.sqrt (S.clique chs).q) S.fw
  by_cases h : (S.clique chs).q = 2
  · rw [ite_eq_left h, dite_eq_left h]
    exact congrArg codeWidth (budgetN_ext_lt hf (u := ⟨0, by omega⟩) (v := ⟨1, by omega⟩)
      (Fin.mk_lt_mk.mpr (by norm_num)))
  · rw [ite_eq_right h, dite_eq_right h]

theorem decodeLabel_mod {a i : ℕ} (ha : a ≠ 0) :
    decodeLabel a i = decodeLabel a (i % 2 ^ codeWidth a) := by
  have e : toBits (codeWidth a) i = toBits (codeWidth a) (i % 2 ^ codeWidth a) := by
    rw [toBits_eq, toBits_eq]
    refine List.map_congr_left fun j hj => ?_
    rw [Nat.testBit_mod_two_pow]
    simp [List.mem_range.mp hj]
  unfold decodeLabel
  rw [ite_eq_right ha, ite_eq_right ha, e]

theorem clChildN_eq (hS : S.Good) {chs : List ℕ} (hp : S.PathOK chs) (i : ℕ) :
    clChildN S.fw (S.code (.cl chs)) i = S.code (S.gen.child (.cl chs) i) := by
  classical
  have hf := fits_path S hS hp
  rw [code_cl]
  simp only [clChildN, stGet_cons_zero, stGet_cons_succ, cQ_eq, cA_eq]
  show _ = S.code (if h : (S.clique chs).q = 2 then
      match decodeLabel ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) i with
      | some
          l => if labelWt l = (S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩ then .last chs i else .zero
      | none => .zero
    else if h : (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q then
      if ValidChoiceCode ((S.clique chs).recast _ h).a S.fw i then .cl (i :: chs) else .zero
    else .zero)
  by_cases h2 : (S.clique chs).q = 2
  · rw [ite_eq_left h2, dite_eq_left h2]
    have hb : budgetN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw 0 1
        =
        (S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩ :=
      budgetN_ext_lt hf (u := ⟨0, by omega⟩) (v := ⟨1, by omega⟩) (Fin.mk_lt_mk.mpr (by norm_num))
    rw [hb]
    generalize (S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩ = b
    by_cases hb0 : b = 0
    · subst hb0
      by_cases hi : i = 0
      · subst hi
        have hd : decodeLabel 0 0 = some (0, 0) := by simp [decodeLabel]
        rw [hd, ite_eq_left (Or.inl ⟨rfl, rfl⟩)]
        dsimp only
        rw [ite_eq_left (by simp [labelWt])]
        rfl
      · have hd : decodeLabel 0 i = none := by simp [decodeLabel, hi]
        rw [hd, ite_eq_right (by simp [hi])]
        rfl
    · have hlt : i % 2 ^ codeWidth b < 2 ^ codeWidth b := Nat.mod_lt _ (by positivity)
      rw [decodeLabel_mod hb0]
      rcases hd : decodeLabel b (i % 2 ^ codeWidth b) with _ | l
      · rw [ite_eq_right]
        · rfl
        · rintro (⟨h, -⟩ | ⟨-, hv, -⟩)
          · exact hb0 h
          · rw [validN_eq hlt, hd] at hv; simp at hv
      · dsimp only
        have hw := labelWtN_decode hlt hd
        by_cases hlw : labelWt l = b
        · rw [ite_eq_left hlw, ite_eq_left (Or.inr ⟨hb0, by rw [validN_eq hlt, hd]; rfl,
            by rw [hw]; exact hlw⟩)]
          rfl
        · rw [ite_eq_right hlw, ite_eq_right]
          · rfl
          · rintro (⟨h, -⟩ | ⟨-, -, hv⟩)
            · exact hb0 h
            · exact hlw (hw ▸ hv)
  · rw [ite_eq_right h2, dite_eq_right h2]
    by_cases hsq : (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q
    · rw [ite_eq_left hsq, dite_eq_left hsq]
      have hV := validN_recast (i := i) (S.clique chs) hsq hf (S.one_le_fw hS)
      by_cases hv : ValidChoiceCode ((S.clique chs).recast _ hsq).a S.fw i
      · rw [ite_eq_left (hV.mpr hv), ite_eq_left hv]
        have hq' : (S.clique (i :: chs)).q = Nat.sqrt (S.clique chs).q := by
          show (childAt S.fw (S.clique chs) i).q = _
          unfold childAt; rw [dite_eq_left hsq]; exact mergeStep_q _ _ _
        have ha' : arrN (S.clique (i :: chs)).q S.fw (extN (S.clique (i :: chs)).a) =
            childN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw
              (Nat.sqrt (S.clique chs).q) i :=
          (congrArg (fun n => arrN n S.fw (extN (S.clique (i :: chs)).a)) hq').trans
            (childN_eq_childAt _ hsq hf (fun r => ValidChoiceCode.even hv r))
        have hc : S.cacheC (i :: chs) = consF (NatList.enc [Nat.sqrt (S.clique chs).q,
            childN (arrN (S.clique chs).q S.fw (extN (S.clique chs).a)) (S.clique chs).q S.fw
              (Nat.sqrt (S.clique chs).q) i]) (S.cacheC chs) := by
          show NatList.enc (S.arrAt (i :: chs) :: S.cacheL chs) = consF _
              (NatList.enc (S.cacheL chs))
          rw [consF_enc]
          show NatList.enc (NatList.enc [(S.clique (i :: chs)).q,
            arrN (S.clique (i :: chs)).q S.fw (extN (S.clique (i :: chs)).a)] :: S.cacheL chs) = _
          rw [ha', hq']
        rw [code_cl, hc, consF_enc]
      · rw [ite_eq_right (mt hV.mp hv), ite_eq_right hv]
        rfl
    · rw [ite_eq_right hsq, dite_eq_right hsq]
      rfl

/-! #### Last labels -/

/-- The child `b` of `last chs i`: the entry of node `b` at the label coded by `i`. -/
def lastChildN (n b : ℕ) : ℕ := NatList.enc [4, stGet n 1, stGet n 2, b, stGet n 3]

theorem lastChildN_eq (chs : List ℕ) (i b : ℕ) :
    lastChildN (S.code (.last chs i)) b = S.code (S.gen.child (.last chs i) b) := by
  rw [code_last]
  simp only [lastChildN, stGet_cons_zero, stGet_cons_succ]
  rfl

/-! #### Entries -/

theorem enc_cons_ne_one (i : ℕ) (rest : List ℕ) : NatList.enc (i :: rest) ≠ 1 := by
  have := NatList.two_le_enc_cons i rest; omega

/-- The tag of an entry: a product at the first clique; higher up, a sum node if the packed labels
are valid, else a leaf. -/
def entTagN (B fw n : ℕ) : ℕ :=
  if stGet n 1 = 1 then 2
  else if pQ (stGet n 2) = Nat.sqrt (pQ (stGet n 2)) * Nat.sqrt (pQ (stGet n 2)) then
    (if argsOkN B fw (cA (stGet n 2)) (cQ (stGet n 2)) (packL (Nat.sqrt (pQ (stGet n 2))))
        (stGet n 3)
      (stGet n 4) then 1 else 0)
  else 0

/-- The width of an entry: the width of the copies (`xiWidth`). -/
def entWidthN (fw n : ℕ) : ℕ :=
  if stGet n 1 = 1 then 0
  else if pQ (stGet n 2) = Nat.sqrt (pQ (stGet n 2)) * Nat.sqrt (pQ (stGet n 2)) then
    xiWidN (pA (stGet n 2)) (pQ (stGet n 2)) fw (Nat.sqrt (pQ (stGet n 2))) (stGet (stGet n 1) 0)
      (stGet n 3)
  else 0

/-- The child of an entry: at the first clique, the two halves of the factors (the code of the
literal of a single factor `f` is `f0 v args f`); higher up, the range of all factors of the
summand of `ξ` if the copies are valid. -/
def entChildN (fw K V M : ℕ) (f0 : ℕ → ℕ → ℕ → ℕ) (n ξ : ℕ) : ℕ :=
  let chC := stGet n 1
  let c := stGet n 2
  let v := stGet n 3
  let x := stGet n 4
  if chC = 1 then
    if ξ = 0 then rangeN (f0 v x) (fun lo hi => NatList.enc [6, c, v, x, lo, hi]) 0
      ((1 + if v < K then V else M) / 2)
    else rangeN (f0 v x) (fun lo hi => NatList.enc [6, c, v, x, lo, hi])
      ((1 + if v < K then V else M) / 2) (1 + if v < K then V else M)
  else if pQ c = Nat.sqrt (pQ c) * Nat.sqrt (pQ c) then
    if copiesOkN (pA c) (pQ c) fw (Nat.sqrt (pQ c))
        (Setup.holders (Nat.sqrt (pQ c)) v
            (orientN (pA c) (pQ c) fw (Nat.sqrt (pQ c)) (stGet chC 0)))
        ξ then
      NatList.enc [5, chC, c, v, x, ξ, 0, nFac (Nat.sqrt (pQ c))]
    else zeroC
  else zeroC

theorem entTagN_eq (hS : S.Good) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {B : ℕ}
    (hB : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B) {chs : List ℕ}
    (hp : S.PathOK chs) (v args : ℕ) :
    entTagN B S.fw (S.code (.ent chs v args)) = AGen.kindTag (S.gen.kind (.ent chs v args)) := by
  classical
  cases chs with
  | nil =>
    rw [code_ent]
    simp only [entTagN, stGet_cons_zero, stGet_cons_succ, NatList.enc_nil, ↓reduceIte]
    rfl
  | cons i rest =>
    have hp0 := hp
    obtain ⟨-, -, h, -⟩ := hp
    have hpg := S.parentGrid_eq rest i h
    have hk : S.gen.kind (.ent (i :: rest) v args) =
        if Setup.ArgsValid (S.clique (i :: rest)) v args (packL (Nat.sqrt (S.clique rest).q))
        then .sum else .leaf := by
      simp only [Setup.gen, hpg]
    rw [hk]
    rw [code_ent]
    simp only [entTagN, stGet_cons_zero, stGet_cons_succ, pQ_eq, cA_eq, cQ_eq]
    rw [ite_eq_right (enc_cons_ne_one i rest), ite_eq_left h]
    have hA := argsOkN_iff (S.clique (i :: rest)) (fits_path S hS hp0) (budget_le_path S he hp0) hB
      (packL (Nat.sqrt (S.clique rest).q)) v args
    by_cases hav : Setup.ArgsValid (S.clique (i :: rest)) v args
        (packL (Nat.sqrt (S.clique rest).q))
    · rw [ite_eq_left (hA.mpr hav), ite_eq_left hav]; rfl
    · rw [ite_eq_right (mt hA.mp hav), ite_eq_right hav]; rfl

theorem entWidthN_eq (hS : S.Good) {chs : List ℕ} (hp : S.PathOK chs) (v args : ℕ) :
    entWidthN S.fw (S.code (.ent chs v args)) = S.gen.width (.ent chs v args) := by
  cases chs with
  | nil =>
    rw [code_ent]
    simp only [entWidthN, stGet_cons_zero, stGet_cons_succ, NatList.enc_nil, ↓reduceIte]
    rfl
  | cons i rest =>
    obtain ⟨hp', -, h, hvc⟩ := hp
    show _ = S.xiWidth rest i v
    rw [code_ent]
    simp only [entWidthN, stGet_cons_zero, stGet_cons_succ, pQ_eq, pA_eq]
    rw [ite_eq_right (enc_cons_ne_one i rest), ite_eq_left h]
    exact xiWidN_eq S rest i v h (fits_path S hS hp') (fun r => ValidChoiceCode.even hvc r)

theorem entChildN_eq (hS : S.Good) {f0 : ℕ → ℕ → ℕ → ℕ}
    (hf0 : ∀ v x f, f0 v x f = S.code (.lit (S.factor0 v x f))) {chs : List ℕ} (hp : S.PathOK chs)
    (v args ξ : ℕ) :
    entChildN S.fw S.K S.V S.G.M f0 (S.code (.ent chs v args)) ξ =
      S.code (S.gen.child (.ent chs v args) ξ) := by
  classical
  cases chs with
  | nil =>
    have hch : S.gen.child (.ent [] v args) ξ =
        if ξ = 0 then Setup.rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) 0
            (S.nFac0 v / 2)
        else Setup.rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) (S.nFac0 v / 2)
          (S.nFac0 v) := rfl
    have e : (fun f => S.code (.lit (S.factor0 v args f))) = f0 v args :=
      funext fun f => (hf0 v args f).symm
    rw [hch]
    rw [code_ent]
    simp only [entChildN, stGet_cons_zero, stGet_cons_succ, NatList.enc_nil, ↓reduceIte]
    by_cases hξ : ξ = 0
    · rw [ite_eq_left hξ, ite_eq_left hξ, code_rangeSt, e]; rfl
    · rw [ite_eq_right hξ, ite_eq_right hξ, code_rangeSt, e]; rfl
  | cons i rest =>
    obtain ⟨hp', -, h, hvc⟩ := hp
    have hfP := fits_path S hS hp'
    have hpg := S.parentGrid_eq rest i h
    have hch : S.gen.child (.ent (i :: rest) v args) ξ =
        if CopiesValid (S.clique rest) (Setup.holders (Nat.sqrt (S.clique rest).q) v
          (orientRow ((S.clique rest).recast _ h).a
            fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q) ξ
        then .rng (i :: rest) v args ξ 0 (nFac (Nat.sqrt (S.clique rest).q)) else .zero := by
      simp only [Setup.gen, hpg]
    rw [hch]
    rw [code_ent]
    simp only [entChildN, stGet_cons_zero, stGet_cons_succ, pQ_eq, pA_eq]
    rw [ite_eq_right (enc_cons_ne_one i rest), ite_eq_left h,
      orientN_recast (S.clique rest) h hfP (fun r => ValidChoiceCode.even hvc r)]
    have hC := copiesOkN_iff (S.clique rest) hfP (Setup.holders (Nat.sqrt (S.clique rest).q) v
      (orientRow ((S.clique rest).recast _ h).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q) ξ
    by_cases hc : CopiesValid (S.clique rest) (Setup.holders (Nat.sqrt (S.clique rest).q) v
        (orientRow ((S.clique rest).recast _ h).a
          fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q) ξ
    · rw [ite_eq_left (hC.mpr hc), ite_eq_left hc]; rfl
    · rw [ite_eq_right (mt hC.mp hc), ite_eq_right hc]; rfl

/-! #### Factor ranges -/

/-- The child `b` of a factor range: its lower or upper half, a single factor by `factorN`. -/
def rngChildN (fw B n b : ℕ) : ℕ :=
  if b = 0 then
    rangeN (factorN fw B (stGet n 1) (stGet n 2) (stGet n 3) (stGet n 4) (stGet n 5))
      (fun a b => NatList.enc [5, stGet n 1, stGet n 2, stGet n 3, stGet n 4, stGet n 5, a, b])
      (stGet n 6) ((stGet n 6 + stGet n 7) / 2)
  else
    rangeN (factorN fw B (stGet n 1) (stGet n 2) (stGet n 3) (stGet n 4) (stGet n 5))
      (fun a b => NatList.enc [5, stGet n 1, stGet n 2, stGet n 3, stGet n 4, stGet n 5, a, b])
      ((stGet n 6 + stGet n 7) / 2) (stGet n 7)

theorem rngChildN_eq (hS : S.Good) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {B : ℕ}
    (hB : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B) {i : ℕ}
    {rest : List ℕ} (hp : S.PathOK (i :: rest)) (v args ξ lo hi b : ℕ) :
    rngChildN S.fw B (S.code (.rng (i :: rest) v args ξ lo hi)) b =
      S.code (S.gen.child (.rng (i :: rest) v args ξ lo hi) b) := by
  have hch : S.gen.child (.rng (i :: rest) v args ξ lo hi) b =
      if b = 0 then Setup.rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) lo
          ((lo + hi) / 2)
      else Setup.rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) ((lo + hi) / 2)
          hi := rfl
  have e : (fun f => S.code (S.factorSt rest i v args ξ f)) =
      factorN S.fw B (NatList.enc (i :: rest)) (S.cacheC (i :: rest)) v args ξ :=
    funext fun f => code_factorSt S hS he hB rest i hp v args ξ f
  rw [hch]
  rw [code_rng]
  simp only [rngChildN, stGet_cons_zero, stGet_cons_succ]
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ite_eq_left hb, code_rangeSt, e]; rfl
  · rw [ite_eq_right hb, ite_eq_right hb, code_rangeSt, e]; rfl

/-! #### Dispatch on the tag -/

/-- The kind tag of a state with tag `2`–`5`. -/
def eTag (B fw n : ℕ) : ℕ :=
  if stGet n 0 = 2 then clTagN n else if stGet n 0 = 4 then entTagN B fw n else 2

/-- The index width of a state with tag `2`–`5`. -/
def eWidth (fw n : ℕ) : ℕ :=
  if stGet n 0 = 2 then clWidthN fw n else if stGet n 0 = 4 then entWidthN fw n else 0

/-- The code of child `i` of a state with tag `2`–`5`. -/
def eChild (fw B K V M : ℕ) (f0 : ℕ → ℕ → ℕ → ℕ) (n i : ℕ) : ℕ :=
  if stGet n 0 = 2 then clChildN fw n i
  else if stGet n 0 = 3 then lastChildN n i
  else if stGet n 0 = 4 then entChildN fw K V M f0 n i
  else rngChildN fw B n i

/-- The entry states: cliques, last labels, entries and factor ranges. -/
def EntrySt : St → Prop
  | .cl _ | .last _ _ | .ent _ _ _ | .rng _ _ _ _ _ _ => True
  | _ => False

/-- **Agreement on the entry states.** On a reachable state (`Setup.Inv`) among `cl`, `last`,
`ent`, `rng`, for a good setup with `2K = 2^(2^e)` and a fuel `B ≥ w(Φ₀ / 2^e) + 2`, the numeric
tag, width and children are those of `Setup.gen`, and the leaf value is `0`. The codes of the leaf
factors of the first clique are supplied as `f0`. -/
theorem entry_agree (hS : S.Good) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {B : ℕ}
    (hB : codeWidth (S.C₀.potential / 2 ^ e) + 2 ≤ B)
    {f0 : ℕ → ℕ → ℕ → ℕ} (hf0 : ∀ v x f, f0 v x f = S.code (.lit (S.factor0 v x f))) {D : ℕ}
    (st : St) (hst : EntrySt st) (hinv : S.Inv D st) :
    eTag B S.fw (S.code st) = AGen.kindTag (S.gen.kind st) ∧ eWidth S.fw (S.code st) = S.gen.width
        st ∧
      (∀ i, eChild S.fw B S.K S.V S.G.M f0 (S.code st) i = S.code (S.gen.child st i)) ∧
      S.gen.leafVal st = 0 := by
  cases st with
  | cl chs =>
    have ht : stGet (S.code (.cl chs)) 0 = 2 := by simp [Setup.code]
    simp only [eTag, eWidth, eChild, ht]
    exact ⟨clTagN_eq S chs, clWidthN_eq S chs (fits_path S hS hinv.1),
      fun i => clChildN_eq S hS hinv.1 i, rfl⟩
  | last chs j =>
    have ht : stGet (S.code (.last chs j)) 0 = 3 := by simp [Setup.code]
    simp only [eTag, eWidth, eChild, ht]
    exact ⟨rfl, rfl, fun i => lastChildN_eq S chs j i, rfl⟩
  | ent chs v args =>
    have ht : stGet (S.code (.ent chs v args)) 0 = 4 := by simp [Setup.code]
    simp only [eTag, eWidth, eChild, ht]
    exact ⟨entTagN_eq S hS he hB hinv.1 v args, entWidthN_eq S hS hinv.1 v args,
      fun i => entChildN_eq S hS hf0 hinv.1 v args i, by cases chs <;> rfl⟩
  | rng chs v args ξ lo hi =>
    cases chs with
    | nil => exact hinv.elim
    | cons j rest =>
      have ht : stGet (S.code (.rng (j :: rest) v args ξ lo hi)) 0 = 5 := by simp [Setup.code]
      simp only [eTag, eWidth, eChild, ht]
      exact ⟨rfl, rfl, fun b => rngChildN_eq S hS he hB hinv.1 v args ξ lo hi b, rfl⟩
  | _ => exact hst.elim

end States

end Cslib.Complexity.NtimeDspace.Cube.Num
