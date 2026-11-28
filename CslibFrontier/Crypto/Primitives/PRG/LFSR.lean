/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.NextBit
public import CslibFrontier.Foundations.Data.BitString.List.Dot

/-!
# Linear feedback shift registers are predictable

An `n`-bit linear feedback shift register (LFSR) with a set of tap positions in `{0, …, n - 1}`
holds a state `(b_{n-1}, …, b_0)`. Each clock cycle outputs `b_0`, computes the feedback bit, the
exclusive or of the bits at the tap positions, and shifts the register to
`(b, b_{n-1}, …, b_1)` [Boneh and Shoup, Section 3.8, p. 75][BonehShoup2023].

Here the register is a list of bits starting with `b_0`, and the tap set is a tap mask: a list
`taps` in which position `v` is a tap when `taps[v] = true`. Mask bits beyond the register length
are ignored. The feedback bit is the inner product `Cslib.BitString.listDot taps state`.

Any `n` consecutive output bits are the state of the register at the time the first of them was
output, so they determine all later output bits. In particular output bit `i ≥ n` is the feedback
bit of the `n` bits before it, and the predictor that computes it wins Attack Game 3.2 at every
position `i ≥ n` with probability `1`. The statements hold for every seed, including the
all-zero seed that [BonehShoup2023] excludes.

## Main definitions

* `Cslib.Crypto.PRG.LFSR.step`: one clock cycle.
* `Cslib.Crypto.PRG.LFSR.output`: the first `ℓ` output bits.
* `Cslib.Crypto.PRG.LFSR.generator`: the register as a generator from `n` bits to `ℓ` bits.
* `Cslib.Crypto.PRG.LFSR.predictor`: the predictor for output bit `i`.

## Main results

* `Cslib.Crypto.PRG.LFSR.drop_output_eq_output_take_drop`: `n` consecutive output bits determine
  all later output bits.
* `Cslib.Crypto.PRG.LFSR.getD_output_add`: the linear recurrence of the output.
* `Cslib.Crypto.PRG.LFSR.listDot_drop_take_generator`: for every seed, output bit `i ≥ n` is the
  feedback bit of the `n` bits before it.
* `Cslib.Crypto.PRG.LFSR.predictionExperiment_predictor`: the predictor is always right.
* `Cslib.Crypto.PRG.LFSR.advantage_predictionTest_predictor`: the test built from the predictor
  has advantage `1 / 2` in Attack Game 3.1.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 3.8, p. 75.
-/

public section

namespace Cslib.Crypto.PRG.LFSR

open Probability
open Cslib.BitString (listDot)

/-- One clock cycle of a linear feedback shift register
[Boneh and Shoup, Section 3.8, p. 75][BonehShoup2023]. The register is listed from the bit `b_0`
that is output next, and position `v` is a tap when `taps[v] = true`. The feedback bit
`listDot taps state` enters at the high end and `b_0` leaves. -/
@[expose] def step (taps state : List Bool) : List Bool :=
  (state ++ [listDot taps state]).tail

/-- The first `ℓ` output bits of the register started in `state`: each clock cycle outputs `b_0`
and then applies `step`. An empty register outputs `false`. -/
@[expose] def output (taps : List Bool) : ℕ → List Bool → List Bool
  | 0, _ => []
  | ℓ + 1, state => state.headD false :: output taps ℓ (step taps state)

@[simp] theorem output_zero (taps state : List Bool) : output taps 0 state = [] := rfl

theorem output_succ (taps : List Bool) (ℓ : ℕ) (state : List Bool) :
    output taps (ℓ + 1) state = state.headD false :: output taps ℓ (step taps state) := rfl

private theorem step_cons (taps : List Bool) (b : Bool) (state : List Bool) :
    step taps (b :: state) = state ++ [listDot taps (b :: state)] := rfl

/-- A clock cycle preserves the register length. -/
@[simp] theorem length_step (taps state : List Bool) :
    (step taps state).length = state.length := by
  simp [step]

/-- Clock cycles preserve the register length. -/
@[simp] theorem length_iterate_step (taps : List Bool) (t : ℕ) (state : List Bool) :
    ((step taps)^[t] state).length = state.length := by
  induction t generalizing state with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, ih, length_step]

/-- The register outputs exactly `ℓ` bits. -/
@[simp] theorem length_output (taps : List Bool) (ℓ : ℕ) (state : List Bool) :
    (output taps ℓ state).length = ℓ := by
  induction ℓ generalizing state with
  | zero => rfl
  | succ ℓ ih => simp [output_succ, ih]

/-- The first output bits are the low bits of the seed. -/
theorem take_output (taps : List Bool) {k ℓ : ℕ} {state : List Bool}
    (hk : k ≤ state.length) (hℓ : k ≤ ℓ) : (output taps ℓ state).take k = state.take k := by
  induction k generalizing ℓ state with
  | zero => simp
  | succ k ih =>
    obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : ℓ ≠ 0)
    rcases state with _ | ⟨b, state⟩
    · simp at hk
    · rw [List.length_cons] at hk
      rw [output_succ, step_cons, List.take_succ_cons, List.take_succ_cons,
        ih (by rw [List.length_append]; omega) (by omega),
        List.take_append_of_le_length (by omega), List.headD_cons]

/-- The first `n` output bits of an `n`-bit register are its seed. -/
theorem take_length_output (taps : List Bool) {ℓ : ℕ} {state : List Bool}
    (hℓ : state.length ≤ ℓ) : (output taps ℓ state).take state.length = state := by
  rw [take_output taps le_rfl hℓ, List.take_length]

/-- An `n`-bit register clocked `n` times outputs its seed. -/
theorem output_length (taps state : List Bool) : output taps state.length state = state := by
  have h := take_length_output taps (ℓ := state.length) (state := state) le_rfl
  rwa [List.take_of_length_le (by rw [length_output])] at h

/-- The output after the first `t` bits is the output of the register after `t` clock cycles. -/
theorem drop_output (taps : List Bool) (t ℓ : ℕ) (state : List Bool) :
    (output taps ℓ state).drop t = output taps (ℓ - t) ((step taps)^[t] state) := by
  induction t generalizing ℓ state with
  | zero => rfl
  | succ t ih =>
    cases ℓ with
    | zero => simp
    | succ ℓ =>
      rw [output_succ, List.drop_succ_cons, ih, Function.iterate_succ_apply, Nat.add_sub_add_right]

/-- Any `n` consecutive output bits of an `n`-bit register are its state at the time the first of
them was output. -/
theorem take_drop_output (taps : List Bool) {t ℓ : ℕ} {state : List Bool}
    (h : t + state.length ≤ ℓ) :
    ((output taps ℓ state).drop t).take state.length = (step taps)^[t] state := by
  have := take_length_output taps (ℓ := ℓ - t) (state := (step taps)^[t] state)
    (by rw [length_iterate_step]; omega)
  rwa [length_iterate_step, ← drop_output] at this

/-- **A single LFSR is predictable** [Boneh and Shoup, Section 3.8, p. 75][BonehShoup2023]: any
`n` consecutive output bits of an `n`-bit register determine all later output bits, which are the
output of the register started on those `n` bits. When fewer than `n` bits remain after position
`t`, the statement says only that a register clocked as often as it is long outputs its state. -/
theorem drop_output_eq_output_take_drop (taps : List Bool) (t ℓ : ℕ) (state : List Bool) :
    (output taps ℓ state).drop t =
      output taps (ℓ - t) (((output taps ℓ state).drop t).take state.length) := by
  by_cases h : t + state.length ≤ ℓ
  · rw [take_drop_output taps h, drop_output]
  · have hlen : ((output taps ℓ state).drop t).length = ℓ - t := by
      rw [List.length_drop, length_output]
    rw [List.take_of_length_le (by omega), ← hlen, output_length]

/-- The output bit that follows the seed is the feedback bit of the seed. -/
theorem getD_output_length (taps : List Bool) {ℓ : ℕ} {state : List Bool}
    (h : state.length < ℓ) :
    (output taps ℓ state).getD state.length false = listDot taps state := by
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : ℓ ≠ 0)
  rcases state with _ | ⟨b, state⟩
  · simp [output_succ]
  · have hget := congrArg (fun l => l.getD state.length false)
      (take_output taps (k := state.length + 1) (ℓ := ℓ)
        (state := state ++ [listDot taps (b :: state)]) (by simp) (by simpa using h))
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, Nat.lt_add_one, ↓reduceIte] at hget
    simp [output_succ, step_cons, List.getD_eq_getElem?_getD, hget]

/-- The linear recurrence of an `n`-bit register: output bit `t + n` is the feedback bit of
output bits `t, …, t + n - 1`. -/
theorem getD_output_add (taps : List Bool) {t ℓ : ℕ} {state : List Bool}
    (h : t + state.length < ℓ) :
    (output taps ℓ state).getD (t + state.length) false =
      listDot taps (((output taps ℓ state).drop t).take state.length) := by
  have h' := getD_output_length taps (ℓ := ℓ - t) (state := (step taps)^[t] state)
    (by rw [length_iterate_step]; omega)
  rw [length_iterate_step, ← drop_output] at h'
  rw [take_drop_output taps h.le, ← h', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- Output bit `i ≥ n` of an `n`-bit register is the feedback bit of the last `n` of the first
`i` output bits. -/
private theorem getD_output (taps : List Bool) {i ℓ : ℕ} {state : List Bool}
    (hn : state.length ≤ i) (hi : i < ℓ) :
    (output taps ℓ state).getD i false =
      listDot taps (((output taps ℓ state).take i).drop (i - state.length)) := by
  have := getD_output_add taps (t := i - state.length) (ℓ := ℓ) (state := state) (by omega)
  rw [Nat.sub_add_cancel hn] at this
  rw [this, List.drop_take, Nat.sub_sub_self hn]

/-! ### The generator and Attack Game 3.2 -/

/-- The LFSR with tap mask `taps`, an `n`-bit register and `ℓ` output bits, as a generator on
bit strings. Seed bit `j` is the register bit `b_j`. -/
@[expose] def generator (taps : List Bool) (n ℓ : ℕ) : Generator (BitString n) (BitString ℓ) :=
  ⟨fun seed => BitString.ofList ℓ (output taps ℓ (List.ofFn seed))⟩

/-- The bits of the generated string are the output of the register. -/
theorem ofFn_generator (taps : List Bool) (n ℓ : ℕ) (seed : BitString n) :
    List.ofFn (generator taps n ℓ seed) = output taps ℓ (List.ofFn seed) :=
  BitString.ofFn_ofList (length_output ..)

/-- The predictor for output bit `i` of an `n`-bit register: the feedback bit of the last `n` of
the `i` bits it is given. It is deterministic. -/
@[expose] noncomputable def predictor (taps : List Bool) (n i : ℕ) : Adversary (Fin i → Bool) :=
  fun x => PMF.pure (listDot taps ((List.ofFn x).drop (i - n)))

/-- For every seed, the feedback bit of the `n` output bits before position `i ≥ n` is output
bit `i`. -/
theorem listDot_drop_take_generator (taps : List Bool) {n ℓ : ℕ} (i : Fin ℓ) (hi : n ≤ i)
    (seed : BitString n) :
    listDot taps ((List.ofFn (Fin.take i i.isLt.le (generator taps n ℓ seed))).drop (i - n)) =
      generator taps n ℓ seed i := by
  have h := getD_output taps (i := i) (ℓ := ℓ) (state := List.ofFn seed) (by simpa using hi) i.isLt
  rw [List.length_ofFn] at h
  rw [Fin.ofFn_take_eq_take_ofFn, ofFn_generator, ← h]; rfl

/-- **A single LFSR is predictable** [Boneh and Shoup, Section 3.8, p. 75][BonehShoup2023], in
Attack Game 3.2: for every position `i ≥ n`, the predictor guesses output bit `i` of an `n`-bit
register with probability `1`. -/
theorem predictionExperiment_predictor (taps : List Bool) {n ℓ : ℕ} (i : Fin ℓ) (hi : n ≤ i) :
    (generator taps n ℓ).predictionExperiment i (predictor taps n i) = PMF.pure true := by
  rw [Generator.predictionExperiment_eq_bind, Generator.outputDist, PMF.monad_bind_eq_bind,
    PMF.bind_map]
  simp only [Function.comp_def, predictor, PMF.pure_map, listDot_drop_take_generator taps i hi,
    decide_true, PMF.bind_const]

/-- The predictor has the largest possible advantage `1 / 2` in Attack Game 3.2. -/
theorem predictionAdvantage_predictor (taps : List Bool) {n ℓ : ℕ} (i : Fin ℓ) (hi : n ≤ i) :
    (generator taps n ℓ).predictionAdvantage i (predictor taps n i) = 1 / 2 := by
  rw [Generator.predictionAdvantage, predictionExperiment_predictor taps i hi]; norm_num

/-- The test built from the predictor distinguishes the LFSR output from a uniform string with
advantage `1 / 2` in Attack Game 3.1. -/
theorem advantage_predictionTest_predictor (taps : List Bool) {n ℓ : ℕ} (i : Fin ℓ) (hi : n ≤ i) :
    (generator taps n ℓ).advantage (predictionTest i (predictor taps n i)) = 1 / 2 := by
  rw [Generator.advantage_predictionTest, predictionAdvantage_predictor taps i hi]

end Cslib.Crypto.PRG.LFSR
