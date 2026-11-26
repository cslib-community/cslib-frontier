/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.CircuitCounting
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.InputTime
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.ModulusCounter.Basic
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Remainder
import Mathlib.Tactic.Linarith

/-!
# Modular-counter remainders, short-exponent circuits, and variable-time equivalence

Computing `ModulusCounter.power T` on `2 k` bits is equivalent up to `O(k)` gates to computing the
fixed-integer remainder `x ↦ T % x` on `k`-bit moduli (`ModulusCounter.remainder_of_power`,
`ModulusCounter.power_of_remainder`, `counter_powers_compute_remainders`). Likewise, variable-time
iteration of `counterStep k` for an `m`-bit input time is equivalent up to `O(k)` gates to `m`-bit
division remainder (`variable_time_counter_iff_remainder`).

Hardwiring `m` numerator bits into the streaming remainder circuit of `Remainder.lean` shows that
any exponent `T < 2 ^ m` has a power circuit of size at most `110 * (m + 1) * (k + 1)`
(`ModulusCounter.short_power_circuit`). Consequently, every hard power requires an exponent of
binary length `m = Ω(2 ^ k / k ^ 2)` (`ModulusCounter.hard_power_requires_long_exponent`,
`ModulusCounter.hard_power_exponent_capacity`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.remainder`: fixed-integer remainder on `k`-bit
  words.
* `Cslib.Circuits.Boolean.Iteration.counterInput`: input packing for remainder reductions; the
  counter state is read back with `Cslib.BitString.sndBits`.
* `Cslib.Circuits.Boolean.Iteration.inputTimeRemainder`: two-input remainder on `m` numerator bits
  and `k` modulus bits.

## Main results

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.remainder_of_power`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.power_of_remainder`,
  `Cslib.Circuits.Boolean.Iteration.counter_powers_compute_remainders`: equivalence between
  fixed-exponent counter powers and fixed-integer remainders.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.short_remainder_circuit`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.short_power_circuit`: linear-in-`m * k` circuits
  for exponents `T < 2 ^ m`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.hard_power_requires_long_exponent`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.hard_power_exponent_capacity`: exponential lower
  bound on the binary length of hard exponents.
* `Cslib.Circuits.Boolean.Iteration.variable_time_counter_iff_remainder`: equivalence between
  variable-time counter iteration and two-input remainder.

## References

* Adapted from lean/Proofs/{CounterRemainders,ExponentLength}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean
open BitString (equivBitVec getLsbD_equivBitVec equivBitVec_getLsbD)

namespace ModulusCounter

variable {k : ℕ}

/-! ### Fixed-integer remainders and equivalence with counter powers -/

/-- Fixed-integer remainder `x ↦ T % x` on `k`-bit words, with `0` on modulus `0`. -/
def remainder (T : ℕ) (x : BitString k) : BitString k :=
  fun i =>
    (BitVec.ofNat k (if (equivBitVec x).toNat = 0 then 0 else T % (equivBitVec x).toNat)).getLsbD
      i.val

/-- Packing `remainder T x` into a `BitVec k` gives `T % (equivBitVec x).toNat` (or `0` when
`(equivBitVec x).toNat = 0`). -/
theorem remainder_word (T : ℕ) (x : BitString k) :
    equivBitVec (remainder T x) =
      BitVec.ofNat k (if (equivBitVec x).toNat = 0 then 0 else T % (equivBitVec x).toNat) :=
  equivBitVec_getLsbD _

/-- When `r` encodes `T % a.toNat` for positive `a`, `addResidue a b r` encodes
`advance a.toNat b.toNat T`. -/
theorem addResidue_spec (a b r : BitVec k) (T : ℕ)
    (hr : 0 < a.toNat → r.toNat = T % a.toNat) :
    addResidue a b r = BitVec.ofNat k (advance a.toNat b.toNat T) := by
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by omega
    have hrlt : r.toNat < a.toNat := by rw [hr ha]; exact Nat.mod_lt _ ha
    apply BitVec.eq_of_toNat_eq
    rw [toNat_addResidue a b r h hrlt, hr ha]
    simp only [advance, ha, h, and_self, ↓reduceIte, BitVec.toNat_ofNat, Nat.add_mod_mod,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ ha).trans a.isLt)]
  · simp [addResidue, BitVec.ult, h, advance]

/-- The counter-state bits of `power T` on modulus `x` and initial state `0` are
`remainder T x`. -/
private theorem power_pack_zero (T : ℕ) (x : BitString k) (i : Fin k) :
    power T (pack (equivBitVec x) 0) (Fin.natAdd k i) = remainder T x i := by
  dsimp only [power]
  rw [leftWord_pack, rightWord_pack]
  simp only [pack, Fin.append_right]
  by_cases hz : (equivBitVec x).toNat = 0
  · simp [advance, remainder, hz]
  · simp [advance, remainder, hz, Nat.pos_of_ne_zero hz]

/-- A circuit for `power T` yields a circuit for `remainder T` with at most one extra gate. -/
theorem remainder_of_power (T : ℕ) (c : Circuit signature (k + k) (k + k))
    (hc : c.Computes interpretation (power T)) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (remainder T) ∧ out.size ≤ c.size + 1 := by
  let s := inputs k ∪ {fun _ : BitString k => false}
  let init := fun x : BitString k => pack (equivBitVec x) (0 : BitVec k)
  have hi (i : Fin (k + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, funext fun x => by simp [init, pack]⟩
    | right i =>
      exact Or.inr (funext fun x => by
        simp only [init, pack, Fin.append_right, BitVec.ofNat_eq_ofNat,
          BitString.equivBitVec_symm_zero, Pi.zero_apply, Bool.zero_eq_false])
  have h := (Synthesis.const (s := inputs k) false).trans
    (Synthesis.circuit (I := interpretation) (s := s) c (fun i x => init x i) hi)
  have hout : wires (remainder (k := k) T) ⊆
      wires (fun x => c.eval interpretation (init x)) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.natAdd k i,
      funext fun x => (congrFun (hc (init x)) _).trans (power_pack_zero T x i)⟩
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by nlinarith⟩

/-- The construction behind `power_of_remainder`: if `c`, read on the input bits `init x`, returns
the remainder of `time x` modulo `(a x).toNat`, then `100 * (k + 1)` further gates compute
`pack (a x) (advance (a x).toNat (b x).toNat (time x))`. -/
private theorem exists_pack_advance {n m : ℕ} (a b : BitString n → BitVec k)
    (time : BitString n → ℕ) (init : BitString n → BitString m) (c : Circuit signature m k)
    (ha : wordWires a ⊆ inputs n) (hb : wordWires b ⊆ inputs n)
    (hinit : ∀ i, (fun x => init x i) ∈ inputs n)
    (hc : ∀ x, equivBitVec (c.eval interpretation (init x)) =
      BitVec.ofNat k (if (a x).toNat = 0 then 0 else time x % (a x).toNat))
    (f : BitString n → BitString (k + k))
    (hf : ∀ x, f x = pack (a x) (BitVec.ofNat k (advance (a x).toNat (b x).toNat (time x)))) :
    ∃ out : Circuit signature n (k + k),
      out.Computes interpretation f ∧ out.size ≤ c.size + 100 * (k + 1) := by
  let r := fun x => equivBitVec (c.eval interpretation (init x))
  let s := inputs n ∪ wires (fun x => c.eval interpretation (init x))
  have ha' : wordWires a ⊆ s := ha.trans Set.subset_union_left
  have hr : wordWires r ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [r, getLsbD_equivBitVec] using
      (show (fun x => c.eval interpretation (init x) i) ∈ s from Or.inr ⟨i, rfl⟩)
  have hs := synthesis_addResidue s a b r ha' (hb.trans Set.subset_union_left) hr
  have hcirc := Synthesis.circuit (I := interpretation) (s := inputs n) c (fun i x => init x i)
    hinit
  have h : Synthesis interpretation (inputs n)
      (s ∪ wordWires (fun x => addResidue (a x) (b x) (r x))) (c.size + 100 * (k + 1)) := by
    simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
      (Synthesis.of_subset (I := interpretation)
        (s := inputs n) (t := inputs n) Set.Subset.rfl).union (hcirc.comp hs)
  have hspec (x : BitString n) : addResidue (a x) (b x) (r x) =
      BitVec.ofNat k (advance (a x).toNat (b x).toNat (time x)) := by
    refine addResidue_spec _ _ _ _ fun hpos => ?_
    simp only [r, hc x, Nat.ne_of_gt hpos, ite_false, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (a x).isLt)]
  have hout : wires f ⊆ s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)) := by
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      exact Or.inl (by simpa only [hf, pack, Fin.append_left, BitString.equivBitVec_symm_apply,
        BitVec.getLsbD_eq_getElem, i.isLt] using ha' ⟨i, rfl⟩)
    | right i =>
      exact Or.inr ⟨i, funext fun x => by
        simp only [hspec, hf, pack, Fin.append_right, BitString.equivBitVec_symm_apply,
          BitVec.getLsbD_eq_getElem, i.isLt]⟩
  obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by simpa only [Nat.zero_add] using hsize⟩

/-- A circuit for `remainder T` yields a circuit for `power T` with at most `100 * (k + 1)` extra
gates. -/
theorem power_of_remainder (T : ℕ) (c : Circuit signature k k)
    (hc : c.Computes interpretation (remainder T)) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (power T) ∧ out.size ≤ c.size + 100 * (k + 1) := by
  refine exists_pack_advance leftWord rightWord (fun _ => T) (fun x i => x (Fin.castAdd k i)) c
    ?_ ?_ (fun i => ⟨Fin.castAdd k i, rfl⟩)
    (fun x => (congrArg equivBitVec (hc _)).trans (remainder_word _ _)) _ fun _ => rfl
  · rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd k i, funext fun x => by simp only [leftWord, getLsbD_equivBitVec]⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨Fin.natAdd k i, funext fun x => by simp only [rightWord, getLsbD_equivBitVec]⟩

/-! ### Short-exponent upper bounds and exponent-length lower bounds -/

/-- Hardwiring `m` numerator bits into `bounded_modulus_remainder` and masking modulus zero gives a
circuit for `remainder T` of size linear in `m * (k + 1)`. -/
theorem short_remainder_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (remainder T) ∧
      out.size ≤ m * (51 * (k + 1) + 4) + 10 * (k + 1) := by
  obtain ⟨rem, hrem, hsize⟩ := bounded_modulus_remainder m k
  let constants : Set (BooleanFunction k) := {fun _ => false, fun _ => true}
  let s := inputs k ∪ constants
  have hc (b : Bool) : (fun _ : BitString k => b) ∈ s := by cases b <;> simp [s, constants]
  let bits := fun i : Fin m => (BitVec.ofNat m T).getLsbD i.val
  let init := fun x : BitString k => Fin.append bits x
  let r := fun x => equivBitVec (rem.eval interpretation (init x))
  have hi (i : Fin (m + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, Fin.append_left] using hc (bits i)
    | right i => simpa only [init, Fin.append_right] using
        (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
  have hr := Synthesis.circuit (I := interpretation) (s := s) rem (fun i x => init x i) hi
  have hz := Synthesis.word_eq_const (s := s) (fun x : BitString k => equivBitVec x)
    (fun i => by simpa only [getLsbD_equivBitVec] using
      (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)) 0
  let s1 := s ∪ (wires (fun x => rem.eval interpretation (init x)) ∪
    {fun x => decide (equivBitVec x = (0 : BitVec k))})
  have hm := Synthesis.word_mux (s := s1) (fun _ => (0 : BitVec k)) r
    (fun x => decide (equivBitVec x = (0 : BitVec k))) (Or.inr (Or.inr rfl))
    (fun _ => Or.inl (hc _)) (fun i => by
      simpa only [r, getLsbD_equivBitVec] using
        (show (fun x => rem.eval interpretation (init x) i) ∈ s1 from
          Or.inr (Or.inl ⟨i, rfl⟩)))
  have hconst : Synthesis interpretation (inputs k) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have h := hconst.trans ((hr.union hz).trans hm)
  have hval (x : BitString k) :
      (if decide (equivBitVec x = (0 : BitVec k)) then (0 : BitVec k) else r x) =
        equivBitVec (remainder T x) := by
    rw [remainder_word]
    have hzero : equivBitVec x = (0 : BitVec k) ↔ (equivBitVec x).toNat = 0 := by grind
    simp only [decide_eq_true_eq, hzero]
    split_ifs with h0
    · simp
    · have hp : 0 < (equivBitVec x).toNat := Nat.pos_of_ne_zero h0
      have hspec := hrem (init x)
      simp only [init, Fin.append_right, Fin.append_left, bits, equivBitVec_getLsbD,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at hspec
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans (equivBitVec x).isLt)]
      exact hspec hp
  have hout : wires (remainder (k := k) T) ⊆
      wordWires (fun x => if decide (equivBitVec x = (0 : BitVec k)) then 0 else r x) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, funext fun x => by simp only [hval, getLsbD_equivBitVec]⟩
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by nlinarith⟩

/-- A fixed exponent `T < 2 ^ m` gives a circuit for `power T` of size at most
`110 * (m + 1) * (k + 1)`. -/
theorem short_power_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (power T) ∧
      out.size ≤ 110 * (m + 1) * (k + 1) := by
  obtain ⟨rem, hr, hs⟩ := short_remainder_circuit k m T hT
  obtain ⟨out, ho, hb⟩ := power_of_remainder T rem hr
  refine ⟨out, ho, ?_⟩
  have hm : 4 * m ≤ 4 * m * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- Any exponent whose counter power requires more than `lowerBudget k` gates needs
`lowerBudget k < 110 * (m + 1) * (k + 1)`. -/
theorem hard_power_requires_long_exponent (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power T) → lowerBudget k < c.size) :
    lowerBudget k < 110 * (m + 1) * (k + 1) := by
  obtain ⟨out, ho, hs⟩ := short_power_circuit k m T hT
  exact (hard out ho).trans_le hs

/-- Explicit exponential lower bound on the binary length `m` of any hard exponent `T < 2 ^ m`. -/
theorem hard_power_exponent_capacity (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power T) → lowerBudget k < c.size) :
    2 ^ k < 112640 * (m + 1) * (k + 1) ^ 2 := by
  have h := hard_power_requires_long_exponent k m T hT hard
  change 2 ^ k / (1024 * (k + 1)) < _ at h
  have hn := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 1024 * (k + 1))).mp h
  nlinarith

end ModulusCounter

/-! ### Remainder helpers and variable-time equivalence -/

variable {k : ℕ}

/-- Pack a `k`-bit modulus `x` with initial counter state `0`. -/
def counterInput (x : BitString k) : BitString (k + k) :=
  ModulusCounter.pack (equivBitVec x) 0

/-- The modulus word of `counterInput x` has natural value `(equivBitVec x).toNat`. -/
@[simp] theorem counterInput_modulus_toNat (x : BitString k) :
    (ModulusCounter.leftWord (counterInput x)).toNat = (equivBitVec x).toNat := by
  simp [counterInput]

/-- The initial counter state word of `counterInput x` has natural value `0`. -/
@[simp] theorem counterInput_state_toNat (x : BitString k) :
    (ModulusCounter.rightWord (counterInput x)).toNat = 0 := by
  simp [counterInput]

/-- Computing `ModulusCounter.power T` and computing `ModulusCounter.remainder T` are equivalent up
to linear additive overhead. -/
theorem counter_powers_compute_remainders (k T : ℕ) :
    (∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (ModulusCounter.power T) →
      ∃ out : Circuit signature k k,
        out.Computes interpretation (ModulusCounter.remainder T) ∧ out.size ≤ c.size + 1) ∧
    (∀ c : Circuit signature k k,
      c.Computes interpretation (ModulusCounter.remainder T) →
      ∃ out : Circuit signature (k + k) (k + k),
        out.Computes interpretation (ModulusCounter.power T) ∧
          out.size ≤ c.size + 100 * (k + 1)) :=
  ⟨ModulusCounter.remainder_of_power T, ModulusCounter.power_of_remainder T⟩

/-- Two-input remainder function on `m` numerator bits followed by `k` modulus bits, returning `0`
when the modulus is `0`. -/
def inputTimeRemainder (m k : ℕ) (x : BitString (m + k)) : BitString k :=
  ModulusCounter.remainder
    (equivBitVec fun j : Fin m => x (Fin.castAdd k j)).toNat
    (fun i : Fin k => x (Fin.natAdd m i))

/-- Variable-time iteration of `counterStep k` for an `m`-bit input time is equivalent up to
`O(k)` gates to computing the `m`-bit remainder `inputTimeRemainder m k`. -/
theorem variable_time_counter_iff_remainder (m k : ℕ) :
    (∀ c : Circuit signature ((k + k) + m) (k + k),
      c.Computes interpretation (inputTimeIterate (counterStep k) m) →
      ∃ out : Circuit signature (m + k) k,
        out.Computes interpretation (inputTimeRemainder m k) ∧ out.size ≤ c.size + 1) ∧
    (∀ c : Circuit signature (m + k) k,
      c.Computes interpretation (inputTimeRemainder m k) →
      ∃ out : Circuit signature ((k + k) + m) (k + k),
        out.Computes interpretation (inputTimeIterate (counterStep k) m) ∧
          out.size ≤ c.size + 100 * (k + 1)) := by
  constructor
  · intro c hc
    let s := inputs (m + k) ∪ {fun _ : BitString (m + k) => false}
    let init := fun x : BitString (m + k) =>
      Fin.append (counterInput fun i : Fin k => x (Fin.natAdd m i))
        (fun j : Fin m => x (Fin.castAdd k j))
    have hi (i : Fin ((k + k) + m)) : (fun x => init x i) ∈ s := by
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          exact Or.inl ⟨Fin.natAdd m i,
            funext fun x => by simp [init, counterInput, ModulusCounter.pack]⟩
        | right i =>
          exact Or.inr (funext fun x => by
            simp only [init, Fin.append_left, counterInput, ModulusCounter.pack, Fin.append_right,
              BitVec.ofNat_eq_ofNat, BitString.equivBitVec_symm_zero, Pi.zero_apply,
              Bool.zero_eq_false])
      | right j => exact Or.inl ⟨Fin.castAdd k j, funext fun x => by simp [init]⟩
    have h := (Synthesis.const (s := inputs (m + k)) false).trans
      (Synthesis.circuit (I := interpretation) (s := s) c (fun i x => init x i) hi)
    have hout : wires (inputTimeRemainder m k) ⊆
        wires (fun x => c.eval interpretation (init x)) := by
      rintro _ ⟨i, rfl⟩
      refine ⟨Fin.natAdd k i, funext fun x => (congrFun (hc (init x)) _).trans ?_⟩
      simpa only [inputTimeIterate, inputTimeRemainder, init, Fin.append_right, Fin.append_left,
        counterInput, counterStep, ModulusCounter.iterate_power] using
        ModulusCounter.power_pack_zero _ _ i
    obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
    exact ⟨out, ho, by omega⟩
  · intro c hc
    let init := fun x : BitString ((k + k) + m) =>
      Fin.append (fun j : Fin m => x (Fin.natAdd (k + k) j))
        (fun i : Fin k => x (Fin.castAdd m (Fin.castAdd k i)))
    refine ModulusCounter.exists_pack_advance
      (fun x => ModulusCounter.leftWord fun i => x (Fin.castAdd m i))
      (fun x => ModulusCounter.rightWord fun i => x (Fin.castAdd m i))
      (fun x => (equivBitVec fun j : Fin m => x (Fin.natAdd (k + k) j)).toNat) init c ?_ ?_
      (fun i => ?_) (fun x => ?_) _ fun x => ?_
    · rintro _ ⟨i, rfl⟩
      exact ⟨Fin.castAdd m (Fin.castAdd k i), funext fun x => by
        simp only [ModulusCounter.leftWord, getLsbD_equivBitVec]⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨Fin.castAdd m (Fin.natAdd k i), funext fun x => by
        simp only [ModulusCounter.rightWord, getLsbD_equivBitVec]⟩
    · induction i using Fin.addCases with
      | left j => exact ⟨Fin.natAdd (k + k) j, funext fun x => by simp [init]⟩
      | right i => exact ⟨Fin.castAdd m (Fin.castAdd k i), funext fun x => by simp [init]⟩
    · simp only [hc (init x), inputTimeRemainder, ModulusCounter.remainder_word, init,
        Fin.append_left, Fin.append_right]
      rfl
    · rw [inputTimeIterate, counterStep, ModulusCounter.iterate_power]
      rfl

end Cslib.Circuits.Boolean.Iteration
