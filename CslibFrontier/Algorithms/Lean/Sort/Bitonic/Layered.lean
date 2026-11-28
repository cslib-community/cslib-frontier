/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Sort.Bitonic.Correctness
import CslibFrontier.Foundations.Data.Nat.Bitwise.Carry
import Mathlib.Data.List.GetD

/-!
# Batcher's network as global layers

The recursive sorter of `Cslib.BitonicSort.sort` is unfolded here into a list of layers acting on
all `2 ^ τ` positions at once, indexed by natural numbers. A layer with exponent `e` pairs the
positions that differ in bit `e` and exchanges each pair according to a flag read at its lower
position (`Cslib.BitonicSort.swapLayer`). The layers of the network (`schedule τ`) run through the
merge levels `d = 1, …, τ`, each with exponents `d - 1, …, 0`.

Two facts are proved:

* With arbitrary flags, every stage of the network permutes the positions below `2 ^ τ`
  (`Cslib.BitonicSort.exists_perm_stage`).
* With the flags of comparisons, in direction `true` on the last merge level and, on lower levels,
  ascending exactly on the positions whose bit `d` is clear, the network computes
  `Cslib.BitonicSort.sort` (`Cslib.BitonicSort.cmpRun_schedule`). In particular its keys are
  sorted (`Cslib.BitonicSort.monotone_cmpRun_schedule`).

A formula that checks the network layer by layer can therefore leave the flags free and check
sortedness at the end: any satisfying assignment permutes its records, and the flags of an actual
sort satisfy it.

## Main definitions

* `Cslib.BitonicSort.swapLayer`: exchanges at distance `2 ^ e` controlled by flags.
* `Cslib.BitonicSort.schedule`: the merge levels and exponents of the layers.
* `Cslib.BitonicSort.stage`: the positions after the first `ℓ` layers, with given flags.
* `Cslib.BitonicSort.cmpFlag`, `Cslib.BitonicSort.cmpRun`: comparison flags and the network
  they drive.

## Main results

* `Cslib.BitonicSort.exists_perm_stage`: every stage is a permutation of the input.
* `Cslib.BitonicSort.cmpRun_schedule`: the comparator network is Batcher's sorter.
* `Cslib.BitonicSort.stage_cmpFlags`: the comparator network is a stage of the switching network.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.BitonicSort

variable {α κ : Type*}

/-! ### Switching layers -/

/-- The position paired with `w` at distance `2 ^ e`: the one whose bit `e` differs. -/
def partner (e w : ℕ) : ℕ := if w.testBit e then w - 2 ^ e else w + 2 ^ e

/-- The lower position of the pair of `w` at distance `2 ^ e`. -/
def low (e w : ℕ) : ℕ := if w.testBit e then w - 2 ^ e else w

/-- The source of position `w` in a switching layer: its partner when the flag at the lower
position of its pair is set, and `w` itself otherwise. -/
def swapSource (e : ℕ) (flag : ℕ → Bool) (w : ℕ) : ℕ :=
  if flag (low e w) then partner e w else w

/-- One layer of exchanges at distance `2 ^ e`: the pair of `w` is exchanged when the flag at its
lower position is set. -/
def swapLayer (e : ℕ) (flag : ℕ → Bool) (A : ℕ → α) (w : ℕ) : α :=
  A (swapSource e flag w)

/-- The layers of Batcher's network on `2 ^ τ` positions, as pairs of a merge level `d` and an
exponent `e < d`: the merge levels `1, …, τ`, each with exponents `d - 1, …, 0`. -/
def schedule : ℕ → List (ℕ × ℕ)
  | 0 => []
  | τ + 1 => schedule τ ++ (List.range (τ + 1)).reverse.map fun e => (τ + 1, e)

/-- The positions after the first `ℓ` layers of `sch`, with the flags `flag ℓ` at layer `ℓ`.
It is meant for `ℓ ≤ sch.length`: past the end the `getD` default supplies a further layer of
exponent `0` instead of stopping. -/
def stage (sch : List (ℕ × ℕ)) (flag : ℕ → ℕ → Bool) (A : ℕ → α) : ℕ → ℕ → α
  | 0 => A
  | ℓ + 1 => swapLayer (sch.getD ℓ (0, 0)).2 (flag ℓ) (stage sch flag A ℓ)

/-- Adding `2 ^ e` to a number with bit `e` clear sets that bit. -/
private theorem testBit_add_two_pow_self {e w : ℕ} (hb : w.testBit e = false) :
    (w + 2 ^ e).testBit e = true := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, hb]
  rfl

/-- The lower position of a pair is at most the position. -/
theorem low_le (e w : ℕ) : low e w ≤ w := by
  unfold low
  split_ifs
  · exact Nat.sub_le _ _
  · exact le_rfl

/-- The lower position of a pair has its bit clear. -/
private theorem testBit_low (e w : ℕ) : (low e w).testBit e = false := by
  unfold low
  split_ifs with hb
  · simpa using Nat.testBit_sub_two_pow hb e
  · simpa using hb

/-- The partner of the lower position is `2 ^ e` above it. -/
private theorem partner_low (e w : ℕ) : partner e (low e w) = low e w + 2 ^ e := by
  unfold partner
  rw [testBit_low]
  rfl

/-- The partner of a position below `2 ^ m` is below `2 ^ m`, for exponents below `m`. -/
theorem partner_lt {e m w : ℕ} (he : e < m) (hw : w < 2 ^ m) : partner e w < 2 ^ m := by
  unfold partner
  split_ifs with hb
  · exact lt_of_le_of_lt (Nat.sub_le _ _) hw
  · -- `w / 2 ^ e` is even and below the even number `2 ^ (m - e)`
    have hpow : 2 ^ m = 2 ^ e * 2 ^ (m - e) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hM : 2 ^ (m - e) = 2 * 2 ^ (m - e - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    have hq : w / 2 ^ e % 2 = 0 := by
      have h := Nat.testBit_eq_decide_div_mod_eq (x := w) (i := e)
      rw [h] at hb
      simp only [decide_eq_true_eq] at hb
      omega
    have hlt : w / 2 ^ e < 2 ^ (m - e) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← hpow]
      exact hw
    have hq2 : w / 2 ^ e + 2 ≤ 2 ^ (m - e) := by omega
    have hd := Nat.div_add_mod w (2 ^ e)
    have hr := Nat.mod_lt w (Nat.two_pow_pos e)
    have : 2 ^ e * (w / 2 ^ e + 2) ≤ 2 ^ e * 2 ^ (m - e) := Nat.mul_le_mul_left _ hq2
    rw [Nat.mul_add] at this
    rw [hpow]
    have h5 : w + 2 ^ e < 2 ^ e * (w / 2 ^ e) + 2 ^ e * 2 := by omega
    exact lt_of_lt_of_le h5 this

/-- The partner of the partner is the position itself. -/
theorem partner_partner (e w : ℕ) : partner e (partner e w) = w := by
  unfold partner
  by_cases hb : w.testBit e
  · have hle : 2 ^ e ≤ w := Nat.ge_two_pow_of_testBit hb
    simp [hb, Nat.testBit_sub_two_pow hb, Nat.sub_add_cancel hle]
  · have hb' : w.testBit e = false := by simpa using hb
    simp [hb', testBit_add_two_pow_self hb']

/-- A pair has the same lower position from either of its positions. -/
private theorem low_partner (e w : ℕ) : low e (partner e w) = low e w := by
  unfold low partner
  by_cases hb : w.testBit e
  · simp [hb, Nat.testBit_sub_two_pow hb]
  · have hb' : w.testBit e = false := by simpa using hb
    simp [hb', testBit_add_two_pow_self hb']

/-- The upper position of a pair below `2 ^ m` is below `2 ^ m`. -/
private theorem low_add_lt {e m w : ℕ} (he : e < m) (hw : w < 2 ^ m) : low e w + 2 ^ e < 2 ^ m := by
  rw [← partner_low]
  exact partner_lt he (lt_of_le_of_lt (low_le e w) hw)

/-- Adding `2 ^ m` shifts the lower position, for exponents below `m`. -/
private theorem low_add_two_pow {e m : ℕ} (he : e < m) (w : ℕ) :
    low e (w + 2 ^ m) = low e w + 2 ^ m := by
  have htb : (w + 2 ^ m).testBit e = w.testBit e := by
    rw [Nat.add_comm]
    exact Nat.testBit_two_pow_add_gt he w
  unfold low
  rw [htb]
  split_ifs with hb
  · exact Nat.sub_add_comm (Nat.ge_two_pow_of_testBit hb)
  · rfl

/-- Adding `2 ^ m` shifts the partner, for exponents below `m`. -/
private theorem partner_add_two_pow {e m : ℕ} (he : e < m) (w : ℕ) :
    partner e (w + 2 ^ m) = partner e w + 2 ^ m := by
  have htb : (w + 2 ^ m).testBit e = w.testBit e := by
    rw [Nat.add_comm]
    exact Nat.testBit_two_pow_add_gt he w
  unfold partner
  rw [htb]
  split_ifs with hb
  · exact Nat.sub_add_comm (Nat.ge_two_pow_of_testBit hb)
  · exact Nat.add_right_comm _ _ _

/-- The source of the source of a position is the position. -/
private theorem swapSource_swapSource (e : ℕ) (flag : ℕ → Bool) (w : ℕ) :
    swapSource e flag (swapSource e flag w) = w := by
  unfold swapSource
  by_cases hf : flag (low e w)
  · rw [ite_eq_left hf, low_partner, ite_eq_left hf, partner_partner]
  · rw [ite_eq_right hf, ite_eq_right hf]

/-- The source of a position below `2 ^ m` is below `2 ^ m`, for exponents below `m`. -/
private theorem swapSource_lt {e m : ℕ} (he : e < m) (flag : ℕ → Bool) {w : ℕ} (hw : w < 2 ^ m) :
    swapSource e flag w < 2 ^ m := by
  unfold swapSource
  split_ifs
  · exact partner_lt he hw
  · exact hw

/-- A switching layer as a permutation of the positions below `2 ^ m`. -/
private def swapPerm {e m : ℕ} (he : e < m) (flag : ℕ → Bool) : Equiv.Perm (Fin (2 ^ m)) where
  toFun w := ⟨swapSource e flag w, swapSource_lt he flag w.isLt⟩
  invFun w := ⟨swapSource e flag w, swapSource_lt he flag w.isLt⟩
  left_inv w := Fin.ext (swapSource_swapSource e flag w)
  right_inv w := Fin.ext (swapSource_swapSource e flag w)

/-- **With arbitrary flags, every stage permutes the positions below `2 ^ m`**, when every
exponent of `sch` is below `m`. -/
theorem exists_perm_stage {m : ℕ} {sch : List (ℕ × ℕ)} (hsch : ∀ p ∈ sch, p.2 < m)
    (flag : ℕ → ℕ → Bool) (A : ℕ → α) (ℓ : ℕ) (hℓ : ℓ ≤ sch.length) :
    ∃ π : Equiv.Perm (Fin (2 ^ m)), ∀ w : Fin (2 ^ m), stage sch flag A ℓ w = A (π w) := by
  induction ℓ with
  | zero => exact ⟨Equiv.refl _, fun w => rfl⟩
  | succ ℓ ih =>
    obtain ⟨π, hπ⟩ := ih (by omega)
    have he : (sch.getD ℓ (0, 0)).2 < m := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hsch _ (List.getElem_mem _)
    refine ⟨(swapPerm he (flag ℓ)).trans π, fun w => ?_⟩
    rw [stage]
    exact hπ ⟨_, swapSource_lt he (flag ℓ) w.isLt⟩

/-! ### Comparator flags -/

/-- The flag of a comparison at merge level `d` and exponent `e`, read at the lower position `w`:
in direction `dir d w`, exchange when the pair is out of order. Ascending exchanges strict
inversions only; descending exchanges ties too, as in `Cslib.BitonicSort.compareLayer`. -/
def cmpFlag [LinearOrder κ] (key : α → κ) (dir : ℕ → ℕ → Bool) (d e : ℕ) (B : ℕ → α) (w : ℕ) :
    Bool :=
  if dir d w then decide (key (B (w + 2 ^ e)) < key (B w))
  else !decide (key (B (w + 2 ^ e)) < key (B w))

/-- The comparator network along a list of layers. -/
def cmpRun [LinearOrder κ] (key : α → κ) (dir : ℕ → ℕ → Bool) :
    List (ℕ × ℕ) → (ℕ → α) → ℕ → α
  | [], A => A
  | p :: rest, A => cmpRun key dir rest (swapLayer p.2 (cmpFlag key dir p.1 p.2 A) A)

/-- The comparator network along two lists of layers runs one after the other. -/
private theorem cmpRun_append [LinearOrder κ] (key : α → κ) (dir : ℕ → ℕ → Bool)
    (s₁ s₂ : List (ℕ × ℕ)) (A : ℕ → α) :
    cmpRun key dir (s₁ ++ s₂) A = cmpRun key dir s₂ (cmpRun key dir s₁ A) := by
  induction s₁ generalizing A with
  | nil => rfl
  | cons p rest ih => exact ih _

/-- The comparator network only reads the positions below `2 ^ m` to fill them, and only reads the
directions of their lower positions. -/
private theorem cmpRun_congr [LinearOrder κ] (key : α → κ) {m : ℕ} {sch : List (ℕ × ℕ)}
    (hsch : ∀ p ∈ sch, p.2 < m) {dir₁ dir₂ : ℕ → ℕ → Bool}
    (hdir : ∀ p ∈ sch, ∀ w < 2 ^ m, dir₁ p.1 w = dir₂ p.1 w) {A₁ A₂ : ℕ → α}
    (hA : ∀ w < 2 ^ m, A₁ w = A₂ w) :
    ∀ w < 2 ^ m, cmpRun key dir₁ sch A₁ w = cmpRun key dir₂ sch A₂ w := by
  induction sch generalizing A₁ A₂ with
  | nil => exact hA
  | cons p rest ih =>
    have he : p.2 < m := hsch _ List.mem_cons_self
    refine ih (fun q hq => hsch q (List.mem_cons_of_mem _ hq))
      (fun q hq => hdir q (List.mem_cons_of_mem _ hq)) fun w hw => ?_
    have hlow : low p.2 w < 2 ^ m := lt_of_le_of_lt (low_le _ _) hw
    have hhi : low p.2 w + 2 ^ p.2 < 2 ^ m := low_add_lt he hw
    have hflag : cmpFlag key dir₁ p.1 p.2 A₁ (low p.2 w) =
        cmpFlag key dir₂ p.1 p.2 A₂ (low p.2 w) := by
      simp only [cmpFlag, hdir p List.mem_cons_self _ hlow, hA _ hlow, hA _ hhi]
    unfold swapLayer swapSource
    rw [hflag]
    split_ifs
    · exact hA _ (partner_lt he hw)
    · exact hA _ hw

/-- Shifting the input by `2 ^ m` shifts the comparator network, when every exponent is below
`m`. -/
private theorem cmpRun_shift [LinearOrder κ] (key : α → κ) {m : ℕ} {sch : List (ℕ × ℕ)}
    (hsch : ∀ p ∈ sch, p.2 < m) (dir : ℕ → ℕ → Bool) (A : ℕ → α) (w : ℕ) :
    cmpRun key dir sch A (w + 2 ^ m) =
      cmpRun key (fun d v => dir d (v + 2 ^ m)) sch (fun v => A (v + 2 ^ m)) w := by
  induction sch generalizing A w with
  | nil => rfl
  | cons p rest ih =>
    have he : p.2 < m := hsch _ List.mem_cons_self
    simp only [cmpRun]
    rw [ih (fun q hq => hsch q (List.mem_cons_of_mem _ hq))]
    congr 1
    funext v
    simp only [swapLayer, swapSource, cmpFlag, low_add_two_pow he, partner_add_two_pow he,
      Nat.add_right_comm (low p.2 v) (2 ^ m) (2 ^ p.2)]
    split_ifs <;> rfl

/-! ### The comparator network is Batcher's sorter -/

/-- The first `n + n` positions are the first `n` positions followed by the first `n` positions
of the array shifted by `n`. -/
private theorem append_comp_val (n : ℕ) (A : ℕ → α) :
    Fin.append (A ∘ (Fin.val : Fin n → ℕ)) ((fun v => A (v + n)) ∘ (Fin.val : Fin n → ℕ)) =
      (A ∘ (Fin.val : Fin (n + n) → ℕ)) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    rfl
  | right i =>
    rw [Fin.append_right]
    simp only [Function.comp_apply, Fin.val_natAdd]
    rw [Nat.add_comm]

/-- The merge layers at level `D` with exponents `m - 1, …, 0`. -/
def mergeLayers (D m : ℕ) : List (ℕ × ℕ) := (List.range m).reverse.map fun e => (D, e)

/-- One more exponent puts the layer with the highest exponent first. -/
private theorem mergeLayers_succ (D m : ℕ) : mergeLayers D (m + 1) = (D, m) :: mergeLayers D m := by
  simp [mergeLayers, List.range_succ]

/-- The layers of a merge have its level and exponents below its size. -/
private theorem mem_mergeLayers {D m : ℕ} {p : ℕ × ℕ} (hp : p ∈ mergeLayers D m) :
    p.1 = D ∧ p.2 < m := by
  simp only [mergeLayers, List.mem_map, List.mem_reverse, List.mem_range] at hp
  obtain ⟨e, he, rfl⟩ := hp
  exact ⟨rfl, he⟩

/-- One more merge level appends its layers. -/
theorem schedule_succ (τ : ℕ) :
    schedule (τ + 1) = schedule τ ++ mergeLayers (τ + 1) (τ + 1) :=
  rfl

/-- Every layer of the schedule has exponent below its merge level, at most `τ`. -/
theorem mem_schedule {τ : ℕ} {p : ℕ × ℕ} (hp : p ∈ schedule τ) : p.2 < p.1 ∧ p.1 ≤ τ := by
  induction τ with
  | zero => simp [schedule] at hp
  | succ τ ih =>
    rw [schedule_succ, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨(ih hp).1, by have := (ih hp).2; omega⟩
    · obtain ⟨h1, h2⟩ := mem_mergeLayers hp
      exact ⟨by omega, by omega⟩

/-- The first layer of a merge is `Cslib.BitonicSort.compareLayer`. -/
private theorem compareLayer_comp_val [LinearOrder κ] (key : α → κ) (m : ℕ) (top : Bool) (D : ℕ)
    (dir : ℕ → ℕ → Bool) (hdir : ∀ w < 2 ^ m, dir D w = top) (A : ℕ → α) :
    compareLayer key top (A ∘ (Fin.val : Fin (arity m + arity m) → ℕ)) =
      ((swapLayer m (cmpFlag key dir D m A) A) ∘ (Fin.val : Fin (arity m + arity m) → ℕ)) := by
  funext i
  have hm : arity m = 2 ^ m := arity_eq_two_pow m
  cases i using Fin.addCases with
  | left i =>
    have hi : (i : ℕ) < 2 ^ m := hm ▸ i.isLt
    have hb : (i : ℕ).testBit m = false := Nat.testBit_lt_two_pow hi
    have hl : low m i = i := by simp [low, hb]
    have hp : partner m i = i + 2 ^ m := by simp [partner, hb]
    simp only [compareLayer, compareLayer.source, Function.comp_apply, Fin.addCases_left,
      Fin.val_natAdd, Fin.val_castAdd, swapLayer, swapSource, hl, hp, cmpFlag, hdir _ hi, hm]
    by_cases h : key (A (i + 2 ^ m)) < key (A i) <;> cases top <;>
      simp [h, Nat.add_comm (2 ^ m)]
  | right i =>
    have hi : (i : ℕ) < 2 ^ m := hm ▸ i.isLt
    have hb : (2 ^ m + (i : ℕ)).testBit m = true := by
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hi]
      rfl
    have hl : low m (2 ^ m + i) = i := by simp [low, hb]
    have hp : partner m (2 ^ m + i) = i := by simp [partner, hb]
    simp only [compareLayer, compareLayer.source, Function.comp_apply, Fin.addCases_right,
      Fin.val_natAdd, Fin.val_castAdd, swapLayer, swapSource, hm, hl, hp, cmpFlag, hdir _ hi]
    by_cases h : key (A (i + 2 ^ m)) < key (A i) <;> cases top <;>
      simp [h, Nat.add_comm (2 ^ m)]

/-- **The merge layers compute Batcher's merge**, when the direction is constant on them. -/
private theorem cmpRun_mergeLayers [LinearOrder κ] (key : α → κ) (D : ℕ) (top : Bool) :
    ∀ (m : ℕ) (dir : ℕ → ℕ → Bool), (∀ w < 2 ^ m, dir D w = top) → ∀ (A : ℕ → α),
      ((cmpRun key dir (mergeLayers D m) A) ∘ Fin.val) = merge key m top (A ∘ Fin.val)
  | 0, _, _, A => rfl
  | m + 1, dir, hdir, A => by
    have hm : arity m = 2 ^ m := arity_eq_two_pow m
    rw [mergeLayers_succ]
    simp only [cmpRun, merge]
    set B := swapLayer m (cmpFlag key dir D m A) A with hB
    set C := cmpRun key dir (mergeLayers D m) B with hC
    have hdir' : ∀ w < 2 ^ m, dir D w = top := fun w hw => hdir w (by rw [Nat.pow_succ]; omega)
    have hcmp : compareLayer key (n := arity m) top
        (A ∘ (Fin.val : Fin (arity (m + 1)) → ℕ)) =
        (B ∘ (Fin.val : Fin (arity (m + 1)) → ℕ)) :=
      compareLayer_comp_val key m top D dir hdir' A
    have hlay : ∀ p ∈ mergeLayers D m, p.2 < m := fun p hp => (mem_mergeLayers hp).2
    have hleft : (C ∘ Fin.val) = merge key m top (B ∘ Fin.val) :=
      cmpRun_mergeLayers key D top m dir hdir' B
    have hright : ((fun v => C (v + arity m)) ∘ Fin.val) =
        merge key m top ((fun v => B (v + 2 ^ m)) ∘ Fin.val) := by
      rw [← cmpRun_mergeLayers key D top m (fun d v => dir d (v + 2 ^ m))
        (fun w hw => hdir _ (by rw [Nat.pow_succ]; omega)) (fun v => B (v + 2 ^ m))]
      funext i
      simp only [Function.comp_apply, hC]
      have hi : (i : ℕ) + arity m = (i : ℕ) + 2 ^ m := by omega
      rw [hi]
      exact cmpRun_shift key hlay dir B i
    have hfun : (fun v => B (arity m + v)) = fun v => B (v + 2 ^ m) := by
      funext v
      congr 1
      omega
    erw [hcmp]
    change (C ∘ Fin.val) = Fin.append (merge key m top (B ∘ Fin.val))
      (merge key m top ((fun v => B (arity m + v)) ∘ Fin.val))
    rw [hfun, ← hleft, ← hright]
    exact (append_comp_val (arity m) C).symm

/-- The directions of the network on `2 ^ τ` positions: `top` on merge level `τ`, and, on lower
levels `d`, ascending exactly on the positions whose bit `d` is clear. -/
def dirFn (τ : ℕ) (top : Bool) (d w : ℕ) : Bool := if τ ≤ d then top else !w.testBit d

/-- **The comparator network is Batcher's sorter.** -/
theorem cmpRun_schedule [LinearOrder κ] (key : α → κ) :
    ∀ (τ : ℕ) (top : Bool) (A : ℕ → α),
      ((cmpRun key (dirFn τ top) (schedule τ) A) ∘ Fin.val) =
        sort key τ top (A ∘ Fin.val)
  | 0, _, _ => rfl
  | τ + 1, top, A => by
    have hτ : arity τ = 2 ^ τ := arity_eq_two_pow τ
    rw [schedule_succ, cmpRun_append]
    simp only [sort]
    set B := cmpRun key (dirFn (τ + 1) top) (schedule τ) A with hB
    have hsch : ∀ p ∈ schedule τ, p.2 < τ := fun p hp => by
      have := mem_schedule hp
      omega
    -- the left half is the ascending sort of the left half
    have hleft : (B ∘ Fin.val) = sort key τ true (A ∘ Fin.val) := by
      rw [← cmpRun_schedule key τ true A]
      funext i
      have hi : (i : ℕ) < 2 ^ τ := hτ ▸ i.isLt
      refine cmpRun_congr key hsch (fun p hp w hw => ?_) (fun _ _ => rfl) _ hi
      have := mem_schedule hp
      simp only [dirFn]
      by_cases hd : τ ≤ p.1
      · have hd' : p.1 = τ := by omega
        rw [ite_eq_right (by omega), ite_eq_left hd, hd', Nat.testBit_lt_two_pow hw]
        rfl
      · rw [ite_eq_right (by omega), ite_eq_right hd]
    -- the right half is the descending sort of the right half
    have hright : ((fun v => B (v + arity τ)) ∘ Fin.val) =
        sort key τ false ((fun v => A (v + 2 ^ τ)) ∘ Fin.val) := by
      rw [← cmpRun_schedule key τ false (fun v => A (v + 2 ^ τ))]
      funext i
      have hi : (i : ℕ) < 2 ^ τ := hτ ▸ i.isLt
      simp only [Function.comp_apply]
      have hi' : (i : ℕ) + arity τ = (i : ℕ) + 2 ^ τ := by omega
      rw [hi', hB, cmpRun_shift key hsch]
      refine cmpRun_congr key hsch (fun p hp w hw => ?_) (fun _ _ => rfl) _ hi
      have := mem_schedule hp
      simp only [dirFn]
      by_cases hd : τ ≤ p.1
      · have hd' : p.1 = τ := by omega
        rw [ite_eq_right (by omega), ite_eq_left hd, hd', Nat.add_comm,
          Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hw]
        rfl
      · rw [ite_eq_right (by omega), ite_eq_right hd, Nat.add_comm _ (2 ^ τ),
          Nat.testBit_two_pow_add_gt (by omega)]
    have hmerge := cmpRun_mergeLayers key (τ + 1) top (τ + 1) (dirFn (τ + 1) top)
      (fun w _ => by simp [dirFn]) B
    rw [hmerge]
    refine congrArg (merge key (τ + 1) top) ?_
    have hfun : (fun v => A (arity τ + v)) = fun v => A (v + 2 ^ τ) := by
      funext v
      congr 1
      omega
    change (B ∘ Fin.val) = Fin.append (sort key τ true (A ∘ Fin.val))
      (sort key τ false ((fun v => A (arity τ + v)) ∘ Fin.val))
    rw [hfun, ← hleft, ← hright]
    exact (append_comp_val (arity τ) B).symm

/-- **The keys after the comparator network are sorted.** -/
theorem monotone_cmpRun_schedule [LinearOrder κ] (key : α → κ) (τ : ℕ) (A : ℕ → α) :
    Monotone (key ∘ ((cmpRun key (dirFn τ true) (schedule τ) A) ∘
      (Fin.val : Fin (arity τ) → ℕ))) := by
  rw [cmpRun_schedule]
  exact monotone_sort key τ _

/-! ### The comparator network as a stage of the switching network -/

/-- The flags the comparator network uses at each layer: those of the comparator at layer `ℓ`,
read from the array after the first `ℓ` layers. It is meant for `ℓ < sch.length`: past the end the
`getD` default supplies a further comparator of merge level and exponent `0`. -/
def cmpFlags [LinearOrder κ] (key : α → κ) (dir : ℕ → ℕ → Bool) (sch : List (ℕ × ℕ))
    (A : ℕ → α) (ℓ : ℕ) : ℕ → Bool :=
  cmpFlag key dir (sch.getD ℓ (0, 0)).1 (sch.getD ℓ (0, 0)).2 (cmpRun key dir (sch.take ℓ) A)

/-- One more layer of the comparator network: the array after the first `ℓ + 1` layers. -/
theorem cmpRun_take_succ [LinearOrder κ] (key : α → κ) (dir : ℕ → ℕ → Bool)
    {sch : List (ℕ × ℕ)} (A : ℕ → α) {ℓ : ℕ} (hℓ : ℓ < sch.length) :
    cmpRun key dir (sch.take (ℓ + 1)) A =
      swapLayer (sch.getD ℓ (0, 0)).2 (cmpFlags key dir sch A ℓ)
        (cmpRun key dir (sch.take ℓ) A) := by
  rw [List.take_succ_eq_append_getElem hℓ, cmpRun_append]
  simp only [cmpRun, cmpFlags, List.getD_eq_getElem _ _ hℓ]

/-- **The comparator network is a stage of the switching network** with the flags of the
comparators: the first `ℓ` layers give the same array. -/
theorem stage_cmpFlags [LinearOrder κ] (key : α → κ) (dir : ℕ → ℕ → Bool)
    (sch : List (ℕ × ℕ)) (A : ℕ → α) :
    ∀ ℓ, ℓ ≤ sch.length → stage sch (cmpFlags key dir sch A) A ℓ = cmpRun key dir (sch.take ℓ) A
  | 0, _ => rfl
  | ℓ + 1, h => by
    rw [cmpRun_take_succ key dir A (by omega), stage, stage_cmpFlags key dir sch A ℓ (by omega)]

end Cslib.BitonicSort
