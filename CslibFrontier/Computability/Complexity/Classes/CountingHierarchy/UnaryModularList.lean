/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Same-level unary modular collection and summation

`unaryModularList` collects polynomially many binary oracle values in order, reducing each
before appending it. The loop invariant bounds the index, list length and every stored entry
under every supported reply of an arbitrary stateful handler. `unaryModularList_mem` therefore
retains one fixed counting oracle at the original level.

`unaryModularSum` reuses this list and the certified binary sum program. The complete reduced
list has polynomial encoded length because the count is unary and the modulus is binary.
This construction preserves the counting level and polynomial storage; it does not claim a
small scalar accumulator-space bound. Its total modulus-zero value is the ordinary natural
sum. Both operations also have direct plain polynomial-time certificates for plain callbacks,
without requiring the modulus to be positive.

Adapted from `LeanCanny.CountingHierarchy.UnaryModularList` and the sum in
`UnaryModularAggregation` at lean-canny commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM
open scoped BigOperators

/-- Collect the first `n` values in order, reducing each at modulus `p`. -/
@[expose] def unaryModularList (n p : ℕ) (f : ℕ → ℕ) : List ℕ :=
  (List.range n).map (fun i => f i % p)

@[simp] theorem unaryModularList_length (n p : ℕ) (f : ℕ → ℕ) :
    (unaryModularList n p f).length = n := by
  simp [unaryModularList]

/-- Every genuine index reads exactly the corresponding modular value. -/
theorem unaryModularList_get (n p : ℕ) (f : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    (unaryModularList n p f)[i]?.getD 0 = f i % p := by
  simp [unaryModularList, hi]

/-- A plain polynomial-time callback yields a polynomial-time modular list.
No positive-modulus hypothesis is needed: at modulus zero its values are unchanged. -/
theorem unaryModularList_polyTime {α : Type} {enc : α ↪ List Bool}
    {count modulus : α → ℕ} {f : α × ℕ → ℕ}
    (hcount : ComputableInPolyTime count enc encUnary)
    (hmod : ComputableInPolyTime modulus enc encNat)
    (hf : ComputableInPolyTime f (encPair enc encNat) encNat) :
    ComputableInPolyTime
      (fun w => unaryModularList (count w) (modulus w) (fun i => f (w, i)))
      enc (encList encNat) := by
  have harg : ComputableInPolyTime (fun q : α × ℕ => (q.1, q.2))
      (encPair enc encUnary) (encPair enc encNat) :=
    (ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  have hvalue := hf.comp harg
  have hm := hmod.comp (ComputableInPolyTime.fst enc encUnary)
  simpa only [unaryModularList, Function.comp_def] using
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hcount)
      (ComputableInPolyTime.binary_mod.comp (hvalue.prod hm))

/-- All stateful handlers obey the storage bound, because each returned
oracle value is reduced before it is appended to the output list. -/
theorem unaryModularList_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {count modulus : α → ℕ} {f : α × ℕ → ℕ}
    (hcount : ComputableInPolyTime count enc encUnary)
    (hmod : ComputableInPolyTime modulus enc encNat) (hpos : ∀ w, 0 < modulus w)
    (hf : f ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => unaryModularList (count w) (modulus w) (fun i => f (w, i))) ∈
      CountingFunction a enc (encList encNat) := by
  let stateEncoding := encPair encNat (encList encNat)
  let callEncoding := encPair enc stateEncoding
  have hf' : (fun q : α × (ℕ × List ℕ) => f (q.1, q.2.1)) ∈
      CountingFunction a callEncoding encNat := CountingFunction.preprocess hf (by fun_prop)
  obtain ⟨A, hA, program, hprogram, heq⟩ := hf'
  let body (w : α) (s : ℕ × List ℕ) : WordQueryComp Unit (ℕ × List ℕ) :=
    (fun v => (s.1 + 1, s.2 ++ [v % modulus w])) <$> program (w, s)
  have hi : ComputableInPolyTime
      (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.1 + 1)
      (encPair callEncoding encNat) encNat := by fun_prop
  have hv : ComputableInPolyTime
      (fun q : (α × (ℕ × List ℕ)) × ℕ => q.2 % modulus q.1.1)
      (encPair callEncoding encNat) encNat :=
    ComputableInPolyTime.binary_mod.comp ((ComputableInPolyTime.snd _ _).prod
      (hmod.comp (by fun_prop)))
  have ht : ComputableInPolyTime
      (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.2)
      (encPair callEncoding encNat) (encList encNat) := by fun_prop
  have hpost := hi.prod (ComputableInPolyTime.listAppend' ht
    (ComputableInPolyTime.cons' hv (ComputableInPolyTime.const [])))
  have hstep : IsOraclePPTOn callEncoding stateEncoding (fun q : α × (ℕ × List ℕ) =>
      OracleComp.interpret ProbOracleComp.query (body q.1 q.2)) := by
    simp only [body, OracleComp.interpret_map]
    exact hprogram.map_with hpost
  have hcanonical := (ComputableInPolyTime.unary_to_binary.comp hcount).prod
    (ComputableInPolyTime.replicate hcount hmod)
  have hpreserve (w : α) (i : ℕ) (s : ℕ × List ℕ) (_hi : i < count w)
      (hinv : s.1 = i ∧ s.2.length = i ∧ ∀ v ∈ s.2, v < modulus w)
      (next : ℕ × List ℕ)
      (hnext : next ∈ OracleComp.support (OracleComp.interpret ProbOracleComp.query (body w s))) :
      next.1 = i + 1 ∧ next.2.length = i + 1 ∧ ∀ v ∈ next.2, v < modulus w := by
    simp only [body, OracleComp.interpret_map] at hnext
    obtain ⟨v, _hv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    refine ⟨by simp only; omega, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hinv.2.2 x hx
      · have he : x = v % modulus w := List.mem_singleton.mp hx
        exact he ▸ Nat.mod_lt _ (hpos w)
  have hbound (w : α) (i : ℕ) (s : ℕ × List ℕ) (hi : i ≤ count w)
      (hinv : s.1 = i ∧ s.2.length = i ∧ ∀ v ∈ s.2, v < modulus w) :
      (stateEncoding s).length ≤
        (stateEncoding (count w, List.replicate (count w) (modulus w))).length := by
    have hx : s.1.size ≤ (count w).size := Nat.size_le_size (by omega)
    have hl := length_encList_le encNat s.2 (b := (encNat (modulus w)).length)
      (fun v hv => by
        simpa only [encNat_apply, Nat.size_eq_bits_len] using
          Nat.size_le_size (hinv.2.2 v hv).le)
    have hr : (encList encNat (List.replicate (count w) (modulus w))).length =
        count w * (2 * (encNat (modulus w)).length + 1) := by
      simp only [length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
    simp only [stateEncoding, length_encPair, hr, encNat_apply, Nat.size_eq_bits_len] at hl ⊢
    rw [hinv.2.1] at hl
    nlinarith
  have hloop := (IsOraclePPTOn.iterateWith_spec
    (step := fun w s => OracleComp.interpret ProbOracleComp.query (body w s))
    hcount (ComputableInPolyTime.const ((0 : ℕ), ([] : List ℕ))) hstep
    (fun w i s => s.1 = i ∧ s.2.length = i ∧ ∀ v ∈ s.2, v < modulus w)
    (fun _ => ⟨rfl, rfl, by simp⟩) hpreserve hcanonical.polyBounded_length hbound).1
  refine ⟨A, hA, (fun w => Prod.snd <$> OracleComp.iterate (count w) (body w) (0, [])), ?_, ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hloop.map (ComputableInPolyTime.snd encNat (encList encNat))
  · intro w
    rw [OracleComp.interpret_map]
    change (OracleComp.interpret (m := Id) (languageOracle A)
      (OracleComp.iterate (count w) (body w) (0, []))).2 = _
    rw [OracleComp.interpret_id_iterate]
    simp only [body, OracleComp.interpret_map, heq]
    change ((fun s : ℕ × List ℕ =>
      (s.1 + 1, s.2 ++ [f (w, s.1) % modulus w]))^[count w] (0, [])).2 = _
    have hiter (k : ℕ) :
        ((fun s : ℕ × List ℕ => (s.1 + 1, s.2 ++ [f (w, s.1) % modulus w]))^[k] (0, [])) =
          (k, (List.range k).map (fun i => f (w, i) % modulus w)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih]
        simp only [List.range_succ, List.map_append, List.map_singleton]
    exact congrArg Prod.snd (hiter (count w))

/-- Sum a polynomially long list of reduced values and reduce the sum once more.
The total modulus-zero value is the unreduced natural sum. -/
@[expose] def unaryModularSum (n p : ℕ) (v : ℕ → ℕ) : ℕ :=
  (unaryModularList n p v).sum % p

/-- Reducing the summands before adding gives the actual sum modulo `p`, including `p = 0`. -/
theorem unaryModularSum_eq (n p : ℕ) (v : ℕ → ℕ) :
    unaryModularSum n p v = (∑ i ∈ Finset.range n, v i) % p := by
  have h := List.sum_nat_mod ((List.range n).map v) p
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range] at h
  simpa only [unaryModularSum, unaryModularList, List.map_map,
    Function.comp_def] using h.symm

/-- At unary arity, a plain polynomial-time summand gives a plain polynomial-time modular sum. -/
theorem unaryModularSum_polyTime {α : Type} {enc : α ↪ List Bool}
    {n p : α → ℕ} {v : α × ℕ → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encNat)
    (hv : ComputableInPolyTime v (encPair enc encNat) encNat) :
    ComputableInPolyTime (fun w => unaryModularSum (n w) (p w) (fun i => v (w, i)))
      enc encNat := by
  simpa only [unaryModularSum, Function.comp_def] using ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_sum.comp (unaryModularList_polyTime hn hp hv)).prod hp)

/-- Polynomially many modular summands use one fixed oracle at the original function level.
The unary count bounds the collected list; no exponential index enumeration is used. -/
theorem unaryModularSum_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {n p : α → ℕ} {v : α × ℕ → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encNat) (hpos : ∀ w, 0 < p w)
    (hv : v ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => unaryModularSum (n w) (p w) (fun i => v (w, i))) ∈
      CountingFunction a enc encNat := by
  have hsum := CountingFunction.map (unaryModularList_mem hn hp hpos hv)
    ComputableInPolyTime.binary_sum
  simpa only [unaryModularSum] using
    CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

/-- The total sum evaluator casts to the actual finite sum, for every modulus. -/
theorem unaryModularSum_cast (n p : ℕ) (v : ℕ → ℕ) :
    (unaryModularSum n p v : ZMod p) = ∑ i : Fin n, (v i.val : ZMod p) := by
  rw [unaryModularSum_eq, ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range]

end Cslib.Complexity
