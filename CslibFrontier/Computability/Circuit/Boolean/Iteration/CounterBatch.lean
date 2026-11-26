/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.ModulusCounter
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.SharedDictionary
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Remainder-power equivalence and batched powers of the modular counter

Computing the `T`-th power of the `2 k`-bit modular counter (`counterStep k`) is equivalent up to
linear additive overhead to computing the fixed-integer remainder `x ↦ T % x` on `k`-bit moduli
(`counterRemainder_of_power`, `counterPower_of_remainder`).

On a batch of `r` independent `2 k`-bit modular counters (`counterBatchPower`), all `r` members can
share a single hardwired lookup dictionary `a ↦ T % a` over the `2 ^ k - 1` positive `k`-bit moduli
(`residueKeys`, `residueValues`). Each member then needs only the linear carry-safe residue addition
(`addResidue`), giving a circuit of size at most `40000 * (k + 1) ^ 3 * (2 ^ k + r)` for every
`r ≤ 2 ^ (k + k)` (`batched_counter_power`). Conversely, one block of a batched circuit computes the
single power with no extra gates (`counterPower_of_batched`), and whenever the power is not the
identity every block requires its own output gate (`counterBatch_size_ge_of_ne_id`). Together with
the counting lower bound for `counterStep k`, this yields, for every `k ≥ 64`, an exponent `T` whose
batched power has `Ω(2 ^ k / k + r)` and `O(k ^ 3 * (2 ^ k + r))` bounds for all
`0 < r ≤ 2 ^ (k + k)`, a factor polynomial in `k` apart (`batched_hard_counter_power`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.counterRemainder`: fixed-integer remainder `x ↦ T % x` on
  `k`-bit words (zero on modulus zero).
* `Cslib.Circuits.Boolean.Iteration.counterBlock`: block `member` of an `r`-way batched `2 k`-bit
  state.
* `Cslib.Circuits.Boolean.Iteration.counterBatchPower`: the `T`-step modular counter applied
  independently to each of `r` blocks.
* `Cslib.Circuits.Boolean.Iteration.residueKeys`,
  `Cslib.Circuits.Boolean.Iteration.residueValues`: shared dictionary keys `1, …, 2 ^ k - 1` and
  payloads `T % a`.

## Main results

* `Cslib.Circuits.Boolean.Iteration.counterRemainder_of_power`,
  `Cslib.Circuits.Boolean.Iteration.counterPower_of_remainder`: circuit equivalence between
  `(counterStep k)^[T]` and `counterRemainder T`.
* `Cslib.Circuits.Boolean.Iteration.batched_counter_power`: shared-dictionary upper bound
  `40000 * (k + 1) ^ 3 * (2 ^ k + r)` for `r ≤ 2 ^ (k + k)`.
* `Cslib.Circuits.Boolean.Iteration.counterPower_of_batched`,
  `Cslib.Circuits.Boolean.Iteration.counterBatch_size_ge_of_ne_id`,
  `Cslib.Circuits.Boolean.Iteration.counterBatch_lower_bounds`: single-block and per-block output
  lower bounds.
* `Cslib.Circuits.Boolean.Iteration.batched_hard_counter_power`: combined upper and lower bounds for
  hard exponents at `k ≥ 64`.

## References

* Adapted from lean/Proofs/{CounterRemainders,CounterBatch}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean

variable {k r : ℕ}

/-! ### Remainder-power equivalence for `counterStep` -/

/-- Fixed-integer remainder `x ↦ T % x` on `k`-bit words, returning `0` when the modulus is `0`. -/
abbrev counterRemainder (T : ℕ) (x : BitString k) : BitString k :=
  ModulusCounter.remainder T x

/-- The `BitVec k` word of `counterRemainder T x` is `T % (BitString.equivBitVec x).toNat` for
nonzero `BitString.equivBitVec x` and `0` otherwise. -/
theorem word_counterRemainder (T : ℕ) (x : BitString k) :
    BitString.equivBitVec (counterRemainder T x) =
      BitVec.ofNat k
        (if (BitString.equivBitVec x).toNat = 0 then 0 else T % (BitString.equivBitVec x).toNat) :=
  ModulusCounter.remainder_word T x

/-- A circuit for `(counterStep k)^[T]` yields a circuit for `counterRemainder T` with at most one
extra gate. -/
theorem counterRemainder_of_power (T : ℕ) (c : Circuit signature (k + k) (k + k))
    (hc : c.Computes interpretation (counterStep k)^[T]) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (counterRemainder T) ∧ out.size ≤ c.size + 1 := by
  rw [counterStep, ModulusCounter.iterate_power] at hc
  exact ModulusCounter.remainder_of_power T c hc

/-- A circuit for `counterRemainder T` yields a circuit for `(counterStep k)^[T]` with at most
`100 * (k + 1)` extra gates. -/
theorem counterPower_of_remainder (T : ℕ) (c : Circuit signature k k)
    (hc : c.Computes interpretation (counterRemainder T)) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (counterStep k)^[T] ∧ out.size ≤ c.size + 100 * (k + 1) := by
  rw [counterStep, ModulusCounter.iterate_power]
  exact ModulusCounter.power_of_remainder T c hc

/-! ### Batched modular-counter states and dictionary -/

/-- The quotient `divNat` of `finProdFinEquiv (a, b)` recovers the first coordinate `a`. -/
@[simp] theorem divNat_finProdFinEquiv {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a, b))

/-- The remainder `modNat` of `finProdFinEquiv (a, b)` recovers the second coordinate `b`. -/
@[simp] theorem modNat_finProdFinEquiv {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, b))

/-- Block `member` of a batched `r * (k + k)`-bit state. -/
def counterBlock (x : BitString (r * (k + k))) (member : Fin r) : BitString (k + k) :=
  fun bit => x (finProdFinEquiv (member, bit))

/-- The batched modular-counter power: `ModulusCounter.power T` applied independently to each of `r`
blocks. -/
def counterBatchPower (T : ℕ) (x : BitString (r * (k + k))) : BitString (r * (k + k)) :=
  fun i =>
    ModulusCounter.power T (counterBlock x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

/-- At coordinate `finProdFinEquiv (member, bit)`, `counterBatchPower T x` evaluates bit `bit` of
`ModulusCounter.power T` on block `member`. -/
@[simp] theorem counterBatchPower_apply (T : ℕ) (x : BitString (r * (k + k))) (member : Fin r)
    (bit : Fin (k + k)) :
    counterBatchPower T x (finProdFinEquiv (member, bit)) =
      ModulusCounter.power T (counterBlock x member) bit := by
  simp [counterBatchPower]

/-- Extracting block `member` from `counterBatchPower T x` yields `ModulusCounter.power T` applied
to `counterBlock x member`. -/
@[simp] theorem counterBlock_counterBatchPower (T : ℕ) (x : BitString (r * (k + k)))
    (member : Fin r) :
    counterBlock (counterBatchPower T x) member =
      ModulusCounter.power T (counterBlock x member) := by
  funext bit
  simp [counterBlock]

/-- The batched power is the `T`-th iterate of the single-step batched update. -/
theorem iterate_counterBatchPower (T : ℕ) :
    (counterBatchPower (r := r) (k := k) 1)^[T] = counterBatchPower T := by
  induction T with
  | zero =>
    ext x i
    obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp [counterBlock]
  | succ T ih =>
    ext x i
    obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp [Function.iterate_succ_apply', ih, ModulusCounter.power_add]

/-- The left half (the modulus) of every state is preserved by `ModulusCounter.power T`. -/
private theorem counterStep_iterate_left (T : ℕ) (y : BitString (k + k)) (i : Fin k) :
    ModulusCounter.power T y (Fin.castAdd k i) = y (Fin.castAdd k i) := by
  simp [ModulusCounter.power, ModulusCounter.pack, ModulusCounter.leftWord]

/-- States with modulus zero are fixed by `ModulusCounter.power T`. -/
private theorem counterStep_iterate_joinState_zero (T : ℕ) (b : BitVec k) :
    ModulusCounter.power T (ModulusCounter.pack 0 b) = ModulusCounter.pack 0 b := by
  simp [ModulusCounter.power, ModulusCounter.advance]

private theorem joinState_zero_zero : ModulusCounter.pack (0 : BitVec k) 0 = fun _ => false := by
  funext bit
  induction bit using Fin.addCases <;>
    simp only [ModulusCounter.pack, Fin.append_left, Fin.append_right, BitVec.ofNat_eq_ofNat,
      BitString.equivBitVec_symm_zero, Pi.zero_apply, Bool.zero_eq_false]

/-- Dictionary keys: the positive `k`-bit moduli `1, …, 2 ^ k - 1`. -/
def residueKeys (k : ℕ) (j : Fin (2 ^ k - 1)) : BitString k :=
  fun bit => (BitVec.ofNat k (j.val + 1)).getLsbD bit.val

/-- Dictionary payloads: `T % a` for the key `a = j.val + 1`. -/
def residueValues (k T : ℕ) (j : Fin (2 ^ k - 1)) : BitString k :=
  fun bit => (BitVec.ofNat k (T % (j.val + 1))).getLsbD bit.val

/-- The dictionary key map `residueKeys k` over the `2 ^ k - 1` positive `k`-bit moduli is
injective. -/
theorem residueKeys_injective (k : ℕ) : Function.Injective (residueKeys k) := by
  intro i j h
  have hn := congrArg BitVec.toNat
    (BitVec.eq_of_getLsbD_eq fun b hb => congrFun h ⟨b, hb⟩ :
      BitVec.ofNat k (i.val + 1) = BitVec.ofNat k (j.val + 1))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i.val + 1 < 2 ^ k),
    Nat.mod_eq_of_lt (by omega : j.val + 1 < 2 ^ k)] at hn
  exact Fin.ext (by omega)

private theorem clog_two_pow_add_le (hr : r ≤ 2 ^ (k + k)) :
    Nat.clog 2 (r + (2 ^ k - 1)) ≤ 2 * k + 1 := by
  apply Nat.clog_le_of_le_pow
  have h1 : 2 ^ k ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [show 2 * k + 1 = (k + k) + 1 by omega, pow_succ]
  omega

/-- **Batched modular-counter upper bound.** Using one shared residue dictionary, `r` independent
`2 k`-bit modular counters can be advanced by `T` steps in size at most
`40000 * (k + 1) ^ 3 * (2 ^ k + r)` for every `r ≤ 2 ^ (k + k)`. -/
theorem batched_counter_power (T r : ℕ) (hr : r ≤ 2 ^ (k + k)) :
    ∃ out : Circuit signature (r * (k + k)) (r * (k + k)),
      out.Computes interpretation (counterBatchPower T) ∧
        out.size ≤ 40000 * (k + 1) ^ 3 * (2 ^ k + r) := by
  classical
  let queries : BitString (r * (k + k)) → Fin r → BitString k :=
    fun x member bit => counterBlock x member (Fin.castAdd k bit)
  have hdict := synthesis_lookupOr (inputs (r * (k + k))) (residueKeys k) (residueValues k T)
    queries (fun member bit => ⟨finProdFinEquiv (member, Fin.castAdd k bit), rfl⟩)
  let s1 := inputs (r * (k + k)) ∪
    ⋃ member, wires fun x => lookupOr (residueKeys k) (residueValues k T) (queries x member)
  let a := fun (member : Fin r) (x : BitString (r * (k + k))) =>
    ModulusCounter.leftWord (counterBlock x member)
  let b := fun (member : Fin r) (x : BitString (r * (k + k))) =>
    ModulusCounter.rightWord (counterBlock x member)
  let rem := fun (member : Fin r) (x : BitString (r * (k + k))) =>
    BitString.equivBitVec (lookupOr (residueKeys k) (residueValues k T) (queries x member))
  have ha (member : Fin r) : wordWires (a member) ⊆ s1 := fun _ ⟨i, h⟩ =>
    h ▸ .inl ⟨finProdFinEquiv (member, Fin.castAdd k i),
      funext fun x => by simp [a, ModulusCounter.leftWord, counterBlock]⟩
  have hb (member : Fin r) : wordWires (b member) ⊆ s1 := fun _ ⟨i, h⟩ =>
    h ▸ .inl ⟨finProdFinEquiv (member, Fin.natAdd k i),
      funext fun x => by simp [b, ModulusCounter.rightWord, counterBlock]⟩
  have hrem (member : Fin r) : wordWires (rem member) ⊆ s1 := fun _ ⟨i, h⟩ =>
    h ▸ .inr (Set.mem_iUnion.mpr ⟨member, i, funext fun x => by simp [rem]⟩)
  have hadd (member : Fin r) := synthesis_addResidue s1 (a member) (b member) (rem member)
    (ha member) (hb member) (hrem member)
  have hfam := Synthesis.iUnion (fun member => wordWires fun x =>
      addResidue (a member x) (b member x) (rem member x)) (fun _ => 100 * (k + 1)) hadd
  have hspec (member : Fin r) (x : BitString (r * (k + k))) :
      addResidue (a member x) (b member x) (rem member x) =
        BitVec.ofNat k (ModulusCounter.advance (a member x).toNat (b member x).toNat T) := by
    apply ModulusCounter.addResidue_spec
    intro hpos
    let j : Fin (2 ^ k - 1) := ⟨(a member x).toNat - 1, by have := (a member x).isLt; omega⟩
    have hj1 : j.val + 1 = (a member x).toNat := Nat.sub_add_cancel hpos
    have hkey : residueKeys k j = queries x member := by
      funext bit
      simp [residueKeys, queries, hj1, a, ModulusCounter.leftWord]
    have hrw : rem member x = BitVec.ofNat k (T % (a member x).toNat) := by
      simp only [rem, lookupOr_of_eq (residueValues k T) (residueKeys_injective k) hkey]
      unfold residueValues
      rw [BitString.equivBitVec_getLsbD, hj1]
    rw [hrw, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (a member x).isLt)]
  have h := (Synthesis.of_subset (I := interpretation) (s := inputs (r * (k + k)))
    (t := inputs (r * (k + k))) Set.Subset.rfl).union (hdict.trans hfam)
  have hout : wires (counterBatchPower (r := r) (k := k) T) ⊆
      inputs (r * (k + k)) ∪
        ⋃ member, wordWires fun x => addResidue (a member x) (b member x) (rem member x) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective i
    induction bit using Fin.addCases with
    | left i =>
      refine .inl ⟨finProdFinEquiv (member, Fin.castAdd k i), funext fun x => ?_⟩
      simp only [counterBatchPower_apply, counterStep_iterate_left, counterBlock]
    | right i =>
      refine .inr (Set.mem_iUnion.mpr ⟨member, i, funext fun x => ?_⟩)
      simp only [hspec, counterBatchPower_apply, ModulusCounter.power, ModulusCounter.pack,
        Fin.append_right, BitString.equivBitVec_symm_apply, BitVec.getLsbD_eq_getElem, i.isLt, a, b]
  obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  refine ⟨out, ho, hsize.trans ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.zero_add]
  have hM : r + (2 ^ k - 1) + 1 = 2 ^ k + r := by have := @Nat.one_le_two_pow k; omega
  rw [hM]
  have hc := clog_two_pow_add_le hr
  have hw : (Nat.clog 2 (r + (2 ^ k - 1)) + 1) ^ 2 * (k + k + 1) ≤ 8 * (k + 1) ^ 3 :=
    calc _ ≤ (2 * (k + 1)) ^ 2 * (2 * (k + 1)) := by gcongr <;> omega
      _ = 8 * (k + 1) ^ 3 := by ring
  nlinarith [Nat.mul_le_mul_left (48 * (2 ^ k + r)) hw,
    Nat.mul_le_mul_left (100 * r) (Nat.le_self_pow (by norm_num : 3 ≠ 0) (k + 1)),
    Nat.zero_le (2 ^ k * (k + 1) ^ 3), Nat.zero_le (r * (k + 1) ^ 3)]

/-- One block of a batched circuit computes the single power with no extra gates: feed the same
state to every block. -/
theorem counterPower_of_batched (T : ℕ) (member : Fin r)
    (c : Circuit signature (r * (k + k)) (r * (k + k)))
    (hc : c.Computes interpretation (counterBatchPower T)) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (ModulusCounter.power T) ∧ out.size ≤ c.size := by
  let init : BitString (k + k) → BitString (r * (k + k)) :=
    fun y i => y (finProdFinEquiv.symm i).2
  have h := Synthesis.circuit (I := interpretation) (s := inputs (k + k)) c
    (fun i y => init y i) (fun i => ⟨_, rfl⟩)
  have hout : wires (ModulusCounter.power (k := k) T) ⊆
      wires (fun y => c.eval interpretation (init y)) := by
    rintro _ ⟨bit, rfl⟩
    refine ⟨finProdFinEquiv (member, bit), funext fun y => ?_⟩
    change c.eval interpretation (init y) _ = ModulusCounter.power T y bit
    rw [hc, counterBatchPower_apply]
    exact congrArg (ModulusCounter.power T · bit) (funext fun b => by simp [counterBlock, init])
  exact (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs

/-- If `ModulusCounter.power T` is not the identity, every block needs its own output gate. -/
theorem counterBatch_size_ge_of_ne_id (T : ℕ) (hT : ModulusCounter.power (k := k) T ≠ id)
    (c : Circuit signature (r * (k + k)) (r * (k + k)))
    (hc : c.Computes interpretation (counterBatchPower T)) : r ≤ c.size := by
  classical
  obtain ⟨y, bit, hy⟩ : ∃ y : BitString (k + k), ∃ bit, ModulusCounter.power T y bit ≠ y bit := by
    by_contra! hn
    exact hT (funext fun y => funext (hn y))
  obtain ⟨j, rfl⟩ : ∃ j : Fin k, bit = Fin.natAdd k j := by
    induction bit using Fin.addCases with
    | left i => exact absurd (counterStep_iterate_left T y i) hy
    | right j => exact ⟨j, rfl⟩
  let g : BitString (k + k) → Bool := fun z => ModulusCounter.power T z (Fin.natAdd k j)
  let e : BitVec k := BitVec.twoPow k j.val
  have he (i : Fin k) : e[i.val] = decide (i = j) := by
    simp [e, Fin.val_inj, eq_comm]
  have hge : g (ModulusCounter.pack 0 e) = true :=
    (congrFun (counterStep_iterate_joinState_zero T e) (Fin.natAdd k j)).trans
      (by simp only [ModulusCounter.pack, Fin.append_right, BitString.equivBitVec_symm_apply, he,
        decide_true])
  have hgz : g (fun _ => false) = false := by
    change ModulusCounter.power T (fun _ => false) (Fin.natAdd k j) = false
    rw [← joinState_zero_zero, counterStep_iterate_joinState_zero, joinState_zero_zero]
  let xe : Fin r → BitString (r * (k + k)) := fun member i =>
    if (finProdFinEquiv.symm i).1 = member then
      ModulusCounter.pack 0 e (finProdFinEquiv.symm i).2
    else false
  have hxe_same (member : Fin r) : counterBlock (xe member) member = ModulusCounter.pack 0 e :=
    funext fun b => by simp [xe, counterBlock]
  have hxe_other {member other : Fin r} (h : other ≠ member) :
      counterBlock (xe member) other = fun _ => false :=
    funext fun b => by simp [xe, counterBlock, h]
  let o : Fin r → Fin (r * (k + k)) := fun member => finProdFinEquiv (member, Fin.natAdd k j)
  have heval (member : Fin r) (x : BitString (r * (k + k))) :
      c.program.trace interpretation x (c.outputs (o member)) = g (counterBlock x member) := by
    change c.eval interpretation x (o member) = _
    rw [hc, counterBatchPower_apply]
  have hgate (member : Fin r) : ∃ γ, c.outputs (o member) = Wire.gate γ := by
    cases hw : c.outputs (o member) with
    | gate γ => exact ⟨γ, rfl⟩
    | input i =>
      exfalso
      have hi (x : BitString (r * (k + k))) : x i = g (counterBlock x member) := by
        rw [← heval member x, hw, Program.trace_input]
      have h1 : xe member i = true := (hi (xe member)).trans (by rw [hxe_same, hge])
      have hi_eq : i = o member := by
        obtain ⟨⟨m', q⟩, rfl⟩ := finProdFinEquiv.surjective i
        simp only [xe, Equiv.symm_apply_apply] at h1
        split_ifs at h1 with hm
        subst hm
        induction q using Fin.addCases with
        | left q => simp [ModulusCounter.pack, Bool.zero_eq_false] at h1
        | right q =>
          simp only [ModulusCounter.pack, Fin.append_right, BitString.equivBitVec_symm_apply, he,
            decide_eq_true_eq] at h1
          rw [h1]
      let xy : BitString (r * (k + k)) := fun i => y (finProdFinEquiv.symm i).2
      have hb : counterBlock xy member = y := funext fun b => by simp [xy, counterBlock]
      exact hy (by simpa only [hb, hi_eq, xy, o, g, Equiv.symm_apply_apply] using (hi xy).symm)
  choose γ hγ using hgate
  have hinj : Function.Injective γ := by
    intro m m' hmm
    by_contra hne
    have h1 := heval m (xe m)
    have h2 := heval m' (xe m)
    rw [hγ m, hmm, ← hγ m', h2, hxe_same, hxe_other (Ne.symm hne), hge, hgz] at h1
    exact Bool.false_ne_true h1
  simpa using Fintype.card_le_of_injective γ hinj

/-- Both lower bounds: a batched circuit is at least as large as any circuit for the single power,
and, unless the power is the identity, has size at least `r`. -/
theorem counterBatch_lower_bounds (T : ℕ) (hr : 0 < r)
    (c : Circuit signature (r * (k + k)) (r * (k + k)))
    (hc : c.Computes interpretation (counterBatchPower T)) :
    (∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (ModulusCounter.power T) ∧ out.size ≤ c.size) ∧
    (ModulusCounter.power (k := k) T ≠ id → r ≤ c.size) :=
  ⟨counterPower_of_batched T ⟨0, hr⟩ c hc, fun h => counterBatch_size_ge_of_ne_id T h c hc⟩

/-- **Batched hard modular-counter powers.** For `k ≥ 64`, there exists an exponent
`T < ModulusCounter.period k` such that for every `0 < r ≤ 2 ^ (k + k)`, `counterBatchPower T` has
a circuit of size at most `40000 * (k + 1) ^ 3 * (2 ^ k + r)` and every circuit computing it has
size greater than `lowerBudget k` and at least `r`. -/
theorem batched_hard_counter_power (k : ℕ) (hk : 64 ≤ k) :
    ∃ T < ModulusCounter.period k, ∀ r, 0 < r → r ≤ 2 ^ (k + k) →
      (∃ out : Circuit signature (r * (k + k)) (r * (k + k)),
        out.Computes interpretation (counterBatchPower T) ∧
          out.size ≤ 40000 * (k + 1) ^ 3 * (2 ^ k + r)) ∧
      ∀ c : Circuit signature (r * (k + k)) (r * (k + k)),
        c.Computes interpretation (counterBatchPower T) →
          lowerBudget k < c.size ∧ r ≤ c.size := by
  obtain ⟨T, hT, hh⟩ := exists_hard_counter_power k hk
  refine ⟨T, hT, fun r hr hrN => ⟨batched_counter_power T r hrN, fun c hc => ?_⟩⟩
  obtain ⟨out, ho, hs⟩ := counterPower_of_batched T ⟨0, hr⟩ c hc
  refine ⟨(hh out ho).trans_le hs, counterBatch_size_ge_of_ne_id T ?_ c hc⟩
  intro hid
  have h0 := hh (Circuit.id signature (k + k)) (fun x => by rw [hid]; rfl)
  simp at h0

end Cslib.Circuits.Boolean.Iteration
