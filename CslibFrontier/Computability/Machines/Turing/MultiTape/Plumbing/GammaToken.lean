/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import Mathlib.Tactic.FinCases

/-!
# Reading an Elias gamma token in linear time

The first work head scans a gamma token. Each leading zero moves the second head one cell away
from its fixed origin marker. Each payload bit moves it one cell back. Reaching the marker ends
the token, leaving the first head on the next token. Keeping the payload emits the
positive integer in little-endian order, including its final leading one. Skipping the payload
emits one success bit.
-/

public section

namespace Turing.MultiTapeTM.GammaToken

open Cslib.BitString

private def move (ds dm : SignType) (out : Option Bool) (q : Option Bool) : Action 2 Bool Bool :=
  ⟨0, ![(none, ds), (none, dm)], out, q⟩

private def instruction (keep payload : Bool) (src marker : Option Bool) : Action 2 Bool Bool :=
  if payload then
    if marker.isSome then move 0 0 (some true) none
    else match src with
      | some b => move 1 (-1) (if keep then some b else none) (some true)
      | none => move 0 0 (some false) none
  else match src with
    | some false => move 1 1 none (some false)
    | some true => move 1 0 none (some true)
    | none => move 0 0 (some false) none

/-- Read or skip one gamma token, with a stationary one-cell marker on the second work tape. -/
def machine (keep : Bool) : MultiTapeTM 2 Bool Bool :=
  .ofTr false fun payload _ work => instruction keep payload (work 0) (work 1)

/-- The two head coordinates on the source word and the marked tape. Both tapes are read-only. -/
@[expose] def config {input : List Bool} (ip : Fin (input.length + 2)) (out word : List Bool)
    (src marker : ℤ) (q : Option Bool) : Cfg 2 Bool Bool input :=
  ⟨q, ip, ![tapeOfList word, tapeOfList [true]], ![src, marker], out⟩

private theorem apply_move {input : List Bool} (ip : Fin (input.length + 2)) (out word : List Bool)
    (p d : ℤ) (q next : Option Bool) (ds dm : SignType) (emit : Option Bool) :
    (move ds dm emit next).apply (config ip out word p d q) =
      config ip (out ++ emit.toList) word (p + ds) (d + dm) next := by
  apply Cfg.ext
  · rfl
  · simp [Action.apply, move, config]
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · rfl

private theorem step_instr (keep state : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) :
    (machine keep).step (config ip out word p d (some state)) =
      (instruction keep state word[p]? ([true] : List Bool)[d]?).apply
        (config ip out word p d (some state)) := by
  rw [step_of_state rfl]
  simp [machine, tr_ofTr, config, Cfg.workTapeSymbols, tapeOfList_ofNat]

private theorem prefix_run (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d n : ℕ) (h : ∀ j < n, word[p + j]? = some false) :
    (machine keep).runFrom (config ip out word p d (some false)) n =
      config ip out word (p + n : ℕ) (d + n : ℕ) (some false) := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    rw [runFrom_add, ih (fun j hj => h j (by omega)), runFrom_one,
      step_instr]
    simp [instruction, h n (by omega), apply_move, SignType.cast, Int.add_assoc]

private theorem payload_run (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out word bits : List Bool) (p d : ℕ)
    (h : ∀ j < bits.length, word[p + j]? = bits[j]?) :
    (machine keep).runFrom (config ip out word p (bits.length + d : ℕ) (some true)) bits.length =
      config ip (out ++ if keep then bits else []) word (p + bits.length : ℕ) d (some true) := by
  induction bits generalizing p out with
  | nil => simp [runFrom]
  | cons b bs ih =>
    have hb : word[p]? = some b := by simpa using h 0 (by simp)
    have ht (j) (hj : j < bs.length) : word[p + 1 + j]? = bs[j]? := by
      have he := h (j + 1) (by simp; omega)
      simpa [show p + 1 + j = p + (j + 1) by omega] using he
    have hnil : ([true] : List Bool)[1 + bs.length + d]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [show (b :: bs).length = 1 + bs.length by simp [Nat.add_comm], runFrom_add, runFrom_one]
    rw [step_instr]
    simp only [instruction, hnil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hb,
      apply_move]
    have hp : ((p : ℤ) + (1 : SignType)) = (p + 1 : ℕ) := by simp
    have hd : (((1 + bs.length + d : ℕ) : ℤ) + (-1 : SignType)) = (bs.length + d : ℕ) := by
      simp [SignType.cast]; omega
    rw [hp, hd, ih _ _ ht]
    cases keep <;> simp [List.append_assoc, Nat.add_assoc]

private theorem scan_prefix (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre tail : List Bool) (k : ℕ) :
    let word := pre ++ (List.replicate k false ++ true :: tail)
    (machine keep).runFrom (config ip out word pre.length 0 (some false)) (k + 1) =
      config ip out word (pre.length + k + 1 : ℕ) k (some true) := by
  let word := pre ++ (List.replicate k false ++ true :: tail)
  change (machine keep).runFrom (config ip out word pre.length 0 _) _ = config ip out word _ _ _
  have hp (j) (hj : j < k) : word[pre.length + j]? = some false := by
    simp [word, List.getElem?_append, hj]
  have hd : word[pre.length + k]? = some true := by simp [word]
  have hpre := prefix_run keep ip out word pre.length 0 k hp
  simp only [Nat.cast_zero, Nat.zero_add] at hpre
  rw [runFrom_add, hpre, runFrom_one, step_instr]
  simp [instruction, hd, apply_move, SignType.cast]

private theorem scan_payload (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre bits tail : List Bool) (k : ℕ) (hbits : bits.length ≤ k)
    (hstop : bits.length = k ∨ tail = []) :
    let word := pre ++ (List.replicate k false ++ true :: (bits ++ tail))
    (machine keep).runFrom (config ip out word pre.length 0 (some false))
        (k + 1 + bits.length + 1) =
      config ip (out ++ (if keep then bits else []) ++ [decide (bits.length = k)])
        word (pre.length + k + 1 + bits.length : ℕ) (k - bits.length : ℕ) none := by
  let word := pre ++ (List.replicate k false ++ true :: (bits ++ tail))
  change (machine keep).runFrom (config ip out word pre.length 0 _) _ = config ip _ word _ _ _
  have hb (j) (hj : j < bits.length) : word[pre.length + k + 1 + j]? = bits[j]? := by
    simp [word, List.getElem?_append, Nat.add_assoc, show 1 + j = j + 1 by omega, hj]
  have hpre := scan_prefix keep ip out pre (bits ++ tail) k
  change (machine keep).runFrom (config ip out word pre.length 0 _) (k + 1) =
    config ip out word (pre.length + k + 1 : ℕ) k (some true) at hpre
  have hpay := payload_run keep ip out word bits (pre.length + k + 1) (k - bits.length) hb
  rw [show bits.length + (k - bits.length) = k by omega] at hpay
  rw [runFrom_add, runFrom_add, hpre, hpay, runFrom_one, step_instr]
  by_cases he : bits.length = k
  · simp [he, instruction, apply_move, SignType.cast]
  · have hn : ([true] : List Bool)[k - bits.length]? = none :=
      List.getElem?_eq_none (by simp; omega)
    have ht : word[pre.length + k + 1 + bits.length]? = none :=
      List.getElem?_eq_none (by simp [word, hstop.resolve_left he]; omega)
    simp [instruction, he, hn, ht, apply_move, SignType.cast]

/-- Scan a token at an arbitrary word offset. The source head lands exactly at the suffix, the
marker head returns to zero, and the clock is the token length plus one. -/
theorem runFrom_word (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre tail : List Bool) (v : ℕ) :
    let token := eliasGamma v
    (machine keep).runFrom (config ip out (pre ++ token ++ tail) pre.length 0
      (some (machine keep).q₀)) (token.length + 1) =
      config ip (out ++ (if keep then lowBits (Nat.log 2 v) v else []) ++ [true])
        (pre ++ token ++ tail) (pre.length + token.length : ℕ) 0 none := by
  let k := Nat.log 2 v
  have h := scan_payload keep ip out pre (lowBits k v) tail k (by simp) (Or.inl (by simp))
  change (machine keep).runFrom (config ip out _ pre.length 0 (some false)) _ = _
  simpa [eliasGamma, List.append_assoc, k, two_mul, add_assoc, add_left_comm, add_comm] using h

/-- A truncated payload consumes every available bit and emits a final failure flag. The
marker head records the missing bits. No unread source cells or partial successful token remain. -/
theorem runFrom_truncated (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre bits : List Bool) (k : ℕ) (h : bits.length < k) :
    let word := pre ++ (List.replicate k false ++ true :: bits)
    (machine keep).runFrom (config ip out word pre.length 0 (some (machine keep).q₀))
        (k + 1 + bits.length + 1) =
      config ip (out ++ (if keep then bits else []) ++ [false]) word word.length
        (k - bits.length : ℕ) none := by
  change (machine keep).runFrom (config ip out _ pre.length 0 (some false)) _ = _
  have hrun := scan_payload keep ip out pre bits [] k h.le (Or.inr rfl)
  simpa [h.ne, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hrun

/-- A source ending in zeroes without a delimiter rejects with the cursor at the final blank. -/
theorem runFrom_no_delimiter (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre : List Bool) (k : ℕ) :
    let word := pre ++ List.replicate k false
    (machine keep).runFrom (config ip out word pre.length 0 (some (machine keep).q₀)) (k + 1) =
      config ip (out ++ [false]) word word.length k none := by
  let word := pre ++ List.replicate k false
  change (machine keep).runFrom (config ip out word pre.length 0 (some false)) _ = _
  have hp (j) (hj : j < k) : word[pre.length + j]? = some false := by simp [word, hj]
  have hpre := prefix_run keep ip out word pre.length 0 k hp
  simp only [Nat.cast_zero, Nat.zero_add] at hpre
  rw [runFrom_add, hpre, runFrom_one, step_instr]
  simp [instruction, apply_move, word, SignType.cast]

private theorem step_progress (keep state : Bool) {input : List Bool}
    (ip : Fin (input.length + 2)) (out word : List Bool) (p d : ℕ) :
    let next := (machine keep).step (config ip out word p d (some state))
    (∃ out', next = config ip out' word p d none) ∨
      (p < word.length ∧ ∃ (state' : Bool) (out' : List Bool) (d' : ℕ),
      next = config ip out' word (p + 1 : ℕ) d' (some state')) := by
  simp only [step_instr]
  cases hb : word[p]? with
  | none =>
    left
    refine ⟨out ++ [state && decide (d = 0)], ?_⟩
    cases state <;> cases d <;> simp [instruction, apply_move, SignType.cast]
  | some b =>
    have hp : p < word.length := (List.getElem?_eq_some_iff.mp hb).choose
    cases state with
    | false =>
      cases b
      · exact Or.inr ⟨hp, false, out, d + 1, by simp [instruction, apply_move, SignType.cast]⟩
      · exact Or.inr ⟨hp, true, out, d, by simp [instruction, apply_move, SignType.cast]⟩
    | true =>
      cases d with
      | zero => exact Or.inl ⟨out ++ [true], by simp [instruction, apply_move, SignType.cast]⟩
      | succ d =>
        refine Or.inr ⟨hp, true, out ++ (if keep then some b else none).toList, d, ?_⟩
        simp [instruction, apply_move, SignType.cast]

/-- On an arbitrary source the scanner consumes some number of remaining cells and spends
exactly one further transition to halt. Its heads and output can be reused by the next scan. -/
theorem exists_run (keep state : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) :
    ∃ (n : ℕ) (out' : List Bool) (d' : ℕ), n ≤ word.length - p ∧
      (machine keep).runFrom (config ip out word p d (some state)) (n + 1) =
        config ip out' word (p + n : ℕ) d' none := by
  generalize hN : word.length - p = N
  induction N using Nat.strong_induction_on generalizing state out p d with
  | ind N ih =>
    rcases step_progress keep state ip out word p d with ⟨out', halt⟩ |
      ⟨hp, state', out', d', step⟩
    · exact ⟨0, out', d, Nat.zero_le _, by simpa only [Nat.zero_add, Nat.add_zero, runFrom_one]
        using halt⟩
    · obtain ⟨n, result, marker, hn, hr⟩ := ih (word.length - (p + 1))
        (by omega) state' out' (p + 1) d' rfl
      refine ⟨n + 1, result, marker, by omega, ?_⟩
      rw [show n + 1 + 1 = 1 + (n + 1) by omega, runFrom_add, runFrom_one, step, hr]
      congr 2
      omega

/-- Even a malformed or truncated token halts after at most one step per remaining source cell
plus one. This bound applies to arbitrary tape words, both phases and any marker displacement. -/
theorem exists_halts_le (keep state : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) :
    ∃ t ≤ word.length - p + 1,
      ((machine keep).runFrom (config ip out word p d (some state)) t).state = none := by
  obtain ⟨n, out', d', hn, hr⟩ := exists_run keep state ip out word p d
  exact ⟨n + 1, by omega, by rw [hr]; rfl⟩

/-- The exact clocks for consecutively positioned tokens total at most twice the compressed
length, for arbitrary token values and either payload mode. -/
theorem sum_clocks_le (values : List ℕ) :
    (values.map fun v => (eliasGamma v).length + 1).sum ≤
      2 * (values.flatMap eliasGamma).length := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    have hp := List.length_pos_iff.mpr (eliasGamma_ne_nil v)
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    omega

end Turing.MultiTapeTM.GammaToken
