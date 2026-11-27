/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Interactive.GKR.Protocol
public import CslibFrontier.Computability.Interactive.GKR.Uniform
public import CslibFrontier.Computability.Interactive.ToIP
public import CslibFrontier.Computability.Probabilistic.Oracle.Time
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.CoeffList
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Polynomial-time word verifier from polynomial-time wiring extensions

A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3; see also
[Thaler, §4.6][Thaler2022]): given a `UniformGKRFamily I encI` (which pairs `IsLogSpaceUniform`
with a caller-supplied `HasPolyTimeWiringMLE` oracle; compiling general `IsLogSpaceUniform` wiring
without `HasPolyTimeWiringMLE` and `poly(S)` prover word-TM runtime remain open on `#892`), this
module constructs the executable word-level interactive verifier `UniformGKRFamily.verifier` over
prime fields `ZMod p` with `p` and field coordinates encoded in **binary** (`encNat`), and
establishes its verifier runtime, completeness, and soundness:

* **Polynomial-time word verifier runtime** (`UniformGKRFamily.isOraclePPTOn_verifier`,
  `UniformGKRFamily.exists_computesOracleInTimeOn_verifier`): `F.verifier` is realized by a
  strict oracle PPT multi-tape Turing machine running in time polynomial in
  `|encI ι| + log p + |input| log p + |claimedOutput| log p` — independent of the internal layer
  widths `2 ^ width i` and total circuit size `S` whenever `|encI ι| = O(d + log S)`.
  (Note: `F.verifier` uses `F.uniform.depth_polyTime`, `F.uniform.width_polyTime`, and
  `F.wiringMLE`.) No `TimeM` charges are used; the runtime bound comes from the native multi-tape
  Turing machine semantics (`IsOraclePPTOn` / `ComputesOracleInTimeOn`).
* **Exact completeness** (`UniformGKRFamily.acceptProb_verifier_complete`): when `p` is prime,
  `minModulus (F.circuit ι) ≤ p`, and the claimed output matches `C.output` on the input table,
  an honest word prover is accepted with probability `1`.
* **Soundness** (`UniformGKRFamily.acceptProb_verifier_sound`): when `p` is prime and the
  claimed output disagrees with `C.output`, every stateful randomized word prover
  `P : Cslib.Complexity.Prover Unit` is accepted with probability at most
  `(1 + width depth + ∑ i < depth, 5 * width i) / p`, combining GKR soundness (`Protocol.lean`)
  with `< 1 / p` total variation distance from fair-coin modular sampling.
* **`IP` membership on prime-modulus instances** (`UniformGKRFamily.mem_IP_primeInstance`):
  since binary-input deterministic primality checking (AKS) is not yet available in the library,
  `Cslib.Complexity.IP` membership is stated on the prime-modulus promise subtype `PrimeInstance I`,
  while all verifier runtime, completeness, and soundness theorems are proved directly on the
  general `Instance I` type and encoding `encInstance I encI`.

Note: primary-source page/theorem locators in `[GoldwasserKalaiRothblum2015]` and `[Thaler2022]`
are from recorded repository documentation (locator not re-verified against primary PDF). General
`IsLogSpaceUniform` wiring compilation without `HasPolyTimeWiringMLE`, the prover's `poly(S)`
word-TM accounting under `#892`, and `CslibFrontierResults` registration remain open for follow-up.

## Main definitions

* `Cslib.Interactive.GKR.Instance`, `Cslib.Interactive.GKR.encInstance`: instance record `(ι, p,
  input, claimedOutput)` with binary field modulus and coordinate lists.
* `Cslib.Interactive.GKR.tableFn`, `Cslib.Interactive.GKR.Instance.CorrectOutput`: input/output
  table representation on `{0, 1}^k` and output-correctness predicate.
* `Cslib.Interactive.GKR.layerCost`, `Cslib.Interactive.GKR.minModulus`: soundness error numerator
  and `3 * layerCost C` modulus threshold for soundness error `≤ 1 / 3`.
* `Cslib.Interactive.GKR.UniformGKRFamily.verifier`: executable word-oracle verifier iterating
  sumcheck and line-reduction steps from the output layer down to the input layer.
* `Cslib.Interactive.GKR.PrimeInstance`, `Cslib.Interactive.GKR.encPrimeInstance`: prime-modulus
  promise domain for `Cslib.Complexity.IP`.

## Main results

* `Cslib.Interactive.GKR.UniformGKRFamily.verifier_of_lt_minModulus`: immediate rejection below
  `minModulus`.
* `Cslib.Interactive.GKR.UniformGKRFamily.isOraclePPTOn_verifier`,
  `Cslib.Interactive.GKR.UniformGKRFamily.exists_computesOracleInTimeOn_verifier`: native Turing
  machine polynomial-time runtime for the `HasPolyTimeWiringMLE` word verifier (step toward `#892`).
* `Cslib.Interactive.GKR.UniformGKRFamily.acceptProb_verifier_complete`: exact `= 1` completeness.
* `Cslib.Interactive.GKR.UniformGKRFamily.acceptProb_verifier_sound`: soundness against all
  stateful randomized word provers `Cslib.Complexity.Prover Unit`.
* `Cslib.Interactive.GKR.UniformGKRFamily.isInteractiveProof_primeInstance`,
  `Cslib.Interactive.GKR.UniformGKRFamily.mem_IP_primeInstance`: `IP` membership on the
  `PrimeInstance` promise domain.

## References

* [S. Goldwasser, Y. T. Kalai, G. N. Rothblum, *Delegating computation: interactive proofs for
  muggles*][GoldwasserKalaiRothblum2015], Theorem 1.1 and Section 3 (locator not re-verified
  against primary PDF)
* [J. Thaler, *Proofs, Arguments, and Zero-Knowledge*][Thaler2022], Section 4.6 (locator not
  re-verified against primary PDF)
-/

public section

namespace Cslib.Interactive.GKR

open MvPolynomial Cslib.BitString Cslib.ProbComp Cslib.Probability Cslib.Complexity
  Turing.MultiTapeTM Spec
open scoped ENNReal

/-! ### Instances, table encoding, and modular arithmetic -/

/-- Input instance for verifying `F.circuit index` over `ZMod modulus`: the circuit index, binary
prime modulus `p`, input values `vals`, and claimed output values `claimedOutput`. -/
structure Instance (I : Type) where
  /-- Circuit family index. -/
  index : I
  /-- Field modulus `p` (encoded in binary `encNat`). -/
  modulus : ℕ
  /-- Input gate values ordered by big-endian bit label (`vals[binaryValue a]`), padded with `0`. -/
  input : List ℕ
  /-- Claimed output gate values ordered by big-endian bit label, padded with `0`. -/
  claimedOutput : List ℕ

/-- Tuple encoding of `Instance I` keeping `modulus`, `input`, and `claimedOutput` in binary. -/
enc_structure encInstance (I : Type) (encI : I ↪ List Bool) : Instance I where
  index : encI,
  modulus : encNat,
  input : encNatList,
  claimedOutput : encNatList

/-- Prime-modulus promise domain for `IP` membership on `Instance I`. -/
@[expose]
def PrimeInstance (I : Type) : Type :=
  {inst : Instance I // Nat.Prime inst.modulus}

/-- Canonical injective bit-word encoding of `PrimeInstance I` inherited from `encInstance`. -/
@[expose]
def encPrimeInstance (I : Type) (encI : I ↪ List Bool) : PrimeInstance I ↪ List Bool :=
  ⟨fun a => encInstance I encI a.1, fun _ _ h => Subtype.ext ((encInstance I encI).injective h)⟩

/-- Interpret a list of field-element representatives `vals` as a Boolean-cube table
`(Fin k → Bool) → ZMod p`, reading index `binaryValue (List.ofFn a)` and defaulting to `0`. -/
@[expose]
def tableFn (p k : ℕ) (vals : List ℕ) (a : Fin k → Bool) : ZMod p :=
  ((vals.getD (binaryValue (List.ofFn a)) 0 : ℕ) : ZMod p)

/-- Correct-output predicate for `inst` with respect to `F : UniformGKRFamily I encI`. -/
@[expose]
def Instance.CorrectOutput {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) : Prop :=
  let C := F.circuit inst.index
  tableFn inst.modulus (C.width C.depth) inst.claimedOutput =
    C.output (tableFn inst.modulus (C.width 0) inst.input)

/-- Total number of scalar challenges drawn across the GKR protocol on `C`:
`width depth` coordinates in the output step plus `2 * width i + 1` in each layer `i < depth`. -/
private def challengeCount (C : LayeredCircuit) : ℕ :=
  C.width C.depth + ((List.range C.depth).map fun i => 2 * C.width i + 1).sum

/-- Total soundness numerator `1 + width depth + ∑ i < depth, 5 * width i` (including `1` for
fair-coin modular sampling approximation error `≤ 1 / p`). -/
@[expose]
def layerCost (C : LayeredCircuit) : ℕ :=
  1 + C.width C.depth + ((List.range C.depth).map fun i => 5 * C.width i).sum

/-- Minimum field modulus `3 * layerCost C` required for soundness error at most `1 / 3`. -/
@[expose]
def minModulus (C : LayeredCircuit) : ℕ :=
  3 * layerCost C

/-- Fair-coin bit width `2 * (log₂ p + 1) + (log₂ (M + 1) + 1)` per modular field sample. -/
private def coinBits (p M : ℕ) : ℕ :=
  2 * (Nat.log 2 p + 1) + (Nat.log 2 (M + 1) + 1)

/-- Binary bit width `Nat.log 2 p + 1` of one residue modulo `p`. -/
private def elemWidth (p : ℕ) : ℕ :=
  Nat.log 2 p + 1

/-- Bit-length limit `(D + 1) * elemWidth p` read from each prover message of degree at most `D`. -/
private def polyLimit (p D : ℕ) : ℕ :=
  (D + 1) * elemWidth p

/-- Modular line point `y + t * (w - y) mod p` on `Fin k` coordinates represented as a `k`-element
list of residues below `p`. -/
private def lineMod (p k : ℕ) (y w : List ℕ) (t : ℕ) : List ℕ :=
  if p = 0 then List.replicate k 0
  else (List.range k).map fun j =>
    (y.getD j 0 + t * subModNat p (w.getD j 0) (y.getD j 0)) % p

/-- Modular Horner evaluation of coefficient list `l` (constant term first) at `z` modulo `p`,
returning `0` when `p = 0`. -/
private def hornerModBin (p z : ℕ) (l : List ℕ) : ℕ :=
  if p = 0 then 0 else l.reverse.foldl (fun acc a => (a + z * acc) % max p 1) 0

/-- Decode a prover bit word as `D + 1` binary residues modulo `p` (`[]` when `p = 0`). -/
private def decodeResidues (p D : ℕ) (word : List Bool) : List ℕ :=
  if p = 0 then []
  else (listRows (D + 1) (elemWidth p) word).map fun row => binaryValue row % p

/-- Encode a list of residues `< p` into concatenated `elemWidth p`-bit big-endian words. -/
private def encodeResidues (p : ℕ) (l : List ℕ) : List Bool :=
  l.flatMap (binaryWord (elemWidth p))

/-- Sparse polynomial-time evaluator for `eval (vecOfList p k r) (multilinearExtension
(tableFn p k vals))` modulo `p`: loops only over `idx < vals.length` with `idx.bits.length ≤ k`
(i.e. `idx < 2 ^ k`), avoiding `2 ^ k` blowup when `k` is large. -/
private def evalTableMLEMod (p k : ℕ) (vals r : List ℕ) : ℕ :=
  if p = 0 then 0
  else
    ((List.range vals.length).map fun idx =>
      if decide (idx.bits.length ≤ k) then
        let w := binaryWord k idx
        let basis := ((List.range k).map fun j =>
          litFactorNat p (w.getD j false) (r.getD j 0)).prod % p
        ((vals.getD idx 0 % p) * basis) % p
      else 0).sum % p

private theorem layerCost_pos (C : LayeredCircuit) : 0 < layerCost C := by
  unfold layerCost
  omega

private theorem layerCost_eq_finset (C : LayeredCircuit) :
    layerCost C = 1 + C.width C.depth + ∑ i ∈ Finset.range C.depth, 5 * C.width i := by
  unfold layerCost
  have hsum : ∀ n : ℕ, ((List.range n).map fun i => 5 * C.width i).sum =
      ∑ i ∈ Finset.range n, 5 * C.width i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton, Finset.sum_range_succ, ih]
  rw [hsum]

private theorem challengeCount_eq_finset (C : LayeredCircuit) :
    challengeCount C = C.width C.depth + ∑ i ∈ Finset.range C.depth, (2 * C.width i + 1) := by
  unfold challengeCount
  have hsum : ∀ n : ℕ, ((List.range n).map fun i => 2 * C.width i + 1).sum =
      ∑ i ∈ Finset.range n, (2 * C.width i + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton, Finset.sum_range_succ, ih]
  rw [hsum]

private theorem length_lineMod (p k : ℕ) (y w : List ℕ) (t : ℕ) :
    (lineMod p k y w t).length = k := by
  unfold lineMod
  split_ifs <;> simp

private theorem mem_lineMod_lt {p k : ℕ} (hp : 0 < p) (y w : List ℕ) (t : ℕ) :
    ∀ v ∈ lineMod p k y w t, v < p := by
  intro v hv
  simp only [lineMod, hp.ne', ↓reduceIte, List.mem_map, List.mem_range] at hv
  obtain ⟨j, _, rfl⟩ := hv
  exact Nat.mod_lt _ hp

private theorem vecOfList_lineMod {p k : ℕ} [Fact p.Prime] (y w : List ℕ) (t : ℕ) :
    vecOfList p k (lineMod p k y w t) =
      GKR.line (vecOfList p k y) (vecOfList p k w) (t : ZMod p) := by
  funext j
  simp only [vecOfList, lineMod, NeZero.ne p, ↓reduceIte, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range j.isLt, Option.map_some, Option.getD_some,
    ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, natCast_subModNat]
  rfl

private theorem foldl_horner_lt {p z : ℕ} (l : List ℕ) :
    l.foldl (fun acc a => (a + z * acc) % max p 1) 0 < max p 1 := by
  have hpos : 0 < max p 1 := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right p 1)
  induction l using List.reverseRecOn with
  | nil => simp [hpos]
  | append_singleton l a _ =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.mod_lt _ hpos

private theorem hornerModBin_lt {p : ℕ} (hp : 0 < p) (z : ℕ) (l : List ℕ) :
    hornerModBin p z l < p := by
  simp only [hornerModBin, hp.ne', ↓reduceIte]
  simpa only [Nat.max_eq_left hp] using foldl_horner_lt (p := p) (z := z) l.reverse

private theorem natCast_hornerModBin {p : ℕ} [NeZero p] (z : ℕ) (l : List ℕ) :
    ((hornerModBin p z l : ℕ) : ZMod p) =
      Polynomial.evalCoeffList (z : ZMod p) (l.map Nat.cast) := by
  simp only [hornerModBin, NeZero.ne p, ↓reduceIte, Nat.max_eq_left (NeZero.one_le),
    List.foldl_reverse]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ih, List.map_cons,
      Polynomial.evalCoeffList_cons]

private theorem length_decodeResidues {p : ℕ} (hp : 0 < p) (D : ℕ) (word : List Bool) :
    (decodeResidues p D word).length = D + 1 := by
  simp [decodeResidues, hp.ne']

private theorem listRow_encodeResidues {p : ℕ} (l : List ℕ) (hl : ∀ a ∈ l, a < p) (i : ℕ) :
    listRow (elemWidth p) i (encodeResidues p l) =
      if h : i < l.length then binaryWord (elemWidth p) l[i]
      else List.replicate (elemWidth p) false := by
  induction l generalizing i with
  | nil => simp [listRow, encodeResidues]
  | cons a l ih =>
    have hlt : a < 2 ^ elemWidth p :=
      (hl a List.mem_cons_self).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p)
    have ha := length_binaryWord hlt
    have ih' := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    cases i with
    | zero =>
      simp [listRow, encodeResidues, List.take_append_of_le_length (le_of_eq ha.symm),
        List.take_of_length_le (le_of_eq ha)]
    | succ i =>
      have hi := ih' i
      simp only [listRow, encodeResidues] at hi ⊢
      rw [List.flatMap_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
        List.drop_append_of_le_length (le_of_eq ha.symm), List.drop_of_length_le (le_of_eq ha),
        List.nil_append, hi]
      simp

private theorem decodeResidues_encodeResidues {p : ℕ} (hp : 0 < p) (D : ℕ) {l : List ℕ}
    (hl : ∀ a ∈ l, a < p) (hlen : l.length ≤ D + 1) :
    decodeResidues p D ((encodeResidues p l).take (polyLimit p D)) =
      (List.range (D + 1)).map fun i => l.getD i 0 := by
  have hlt : ∀ a ∈ l, a < 2 ^ elemWidth p := fun a ha =>
    (hl a ha).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p)
  have hlength : (encodeResidues p l).length ≤ polyLimit p D := by
    have hflat : ∀ (xs : List ℕ), (∀ a ∈ xs, a < 2 ^ elemWidth p) →
        (xs.flatMap (binaryWord (elemWidth p))).length = xs.length * elemWidth p := by
      intro xs hxs
      induction xs with
      | nil => simp
      | cons a xs ihxs =>
        rw [List.flatMap_cons, List.length_append,
          length_binaryWord (hxs a List.mem_cons_self),
          ihxs (fun b hb => hxs b (List.mem_cons_of_mem a hb)),
          List.length_cons, Nat.succ_mul, Nat.add_comm]
    rw [encodeResidues, hflat l hlt, polyLimit]
    exact Nat.mul_le_mul_right _ hlen
  rw [List.take_of_length_le hlength]
  simp only [decodeResidues, hp.ne', ↓reduceIte, listRows, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, listRow_encodeResidues l hl]
  split_ifs with hi
  · rw [binaryValue_binaryWord, Nat.mod_eq_of_lt (hl _ (List.getElem_mem hi)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · have hnone : l[i]? = none := List.getElem?_eq_none (not_lt.1 hi)
    rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    have hzero : binaryValue (List.replicate (elemWidth p) false) = 0 := by
      rw [← List.append_nil (List.replicate _ _), binaryValue_replicate_false_append]
      rfl
    rw [hzero, Nat.zero_mod]

private theorem evalTableMLEMod_lt {p : ℕ} (hp : 0 < p) (k : ℕ) (vals r : List ℕ) :
    evalTableMLEMod p k vals r < p := by
  simp only [evalTableMLEMod, hp.ne', ↓reduceIte]
  exact Nat.mod_lt _ hp

private theorem natCast_evalTableMLEMod {p : ℕ} [NeZero p] (k : ℕ) (vals r : List ℕ) :
    ((evalTableMLEMod p k vals r : ℕ) : ZMod p) =
      eval (vecOfList p k r) (multilinearExtension (tableFn p k vals)) := by
  simp only [evalTableMLEMod, NeZero.ne p, ↓reduceIte, ZMod.natCast_mod]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Nat.cast_sum]
  let term (idx : ℕ) : ZMod p :=
    ((vals.getD idx 0 : ℕ) : ZMod p) *
      ∏ j : Fin k, WireLit.litFactor ((binaryWord k idx).getD j.val false) (vecOfList p k r j)
  have hcast : ∀ idx : ℕ,
      (((if decide (idx.bits.length ≤ k) then
          (vals.getD idx 0 % p *
            (((List.range k).map fun j =>
              litFactorNat p ((binaryWord k idx).getD j false) (r.getD j 0)).prod % p)) % p
        else 0 : ℕ) : ZMod p)) =
        if idx < 2 ^ k then term idx else 0 := by
    intro idx
    have hltIff : idx.bits.length ≤ k ↔ idx < 2 ^ k := by
      rw [Nat.size_eq_bits_len, Nat.size_le]
    by_cases h : idx < 2 ^ k
    · have hb : idx.bits.length ≤ k := hltIff.mpr h
      simp only [hb, decide_true, ↓reduceIte, h, term, ZMod.natCast_mod, Nat.cast_mul]
      rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range, Nat.cast_prod,
        Finset.prod_range]
      simp only [natCast_litFactorNat, vecOfList]
    · have hb : ¬ idx.bits.length ≤ k := mt hltIff.mp h
      simp [hb, h]
  simp_rw [hcast]
  have hsum : (∑ idx ∈ Finset.range vals.length, if idx < 2 ^ k then term idx else 0) =
      ∑ idx ∈ Finset.range (2 ^ k), term idx := by
    have hmin : ∀ m, (∑ idx ∈ Finset.range m, if idx < 2 ^ k then term idx else 0) =
        ∑ idx ∈ (Finset.range m).filter (· < 2 ^ k), term idx := fun m => by
      rw [Finset.sum_filter]
    rw [hmin]
    have hflt : (Finset.range vals.length).filter (· < 2 ^ k) =
        Finset.range (min vals.length (2 ^ k)) := by
      ext idx
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
    rw [hflt]
    by_cases hle : vals.length ≤ 2 ^ k
    · rw [Nat.min_eq_left hle, ← Finset.sum_range_add_sum_Ico term hle]
      have hzero : ∑ idx ∈ Finset.Ico vals.length (2 ^ k), term idx = 0 :=
        Finset.sum_eq_zero fun idx hidx => by
          have hi : vals.length ≤ idx := (Finset.mem_Ico.mp hidx).1
          simp [term, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
      rw [hzero, add_zero]
    · have hge : 2 ^ k ≤ vals.length := le_of_not_ge hle
      rw [Nat.min_eq_right hge]
  rw [hsum, eval_multilinearExtension_eq_sum]
  symm
  refine Finset.sum_bij (fun a _ => binaryValue (List.ofFn a)) ?_ ?_ ?_ ?_
  · intro a _
    have hlen : (List.ofFn a).length = k := List.length_ofFn
    simpa only [Finset.mem_range, hlen] using binaryValue_lt_two_pow (List.ofFn a)
  · intro a₁ _ a₂ _ hEq
    exact List.ofFn_injective (binaryValue_injective_of_length_eq (by simp) hEq)
  · intro idx hidx
    rw [Finset.mem_range] at hidx
    obtain ⟨a, ha⟩ := exists_binaryValue_eq hidx
    exact ⟨a, Finset.mem_univ a, ha⟩
  · intro a _
    have hlt : binaryValue (List.ofFn a) < 2 ^ k := by
      simpa only [List.length_ofFn] using binaryValue_lt_two_pow (List.ofFn a)
    have hword : binaryWord k (binaryValue (List.ofFn a)) = List.ofFn a :=
      binaryValue_injective_of_length_eq (by simp [length_binaryWord hlt])
        (by rw [binaryValue_binaryWord])
    rw [tableFn, eval_indicatorPoly_apply]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj : (List.ofFn a).getD j.val false = a j := by
      simp [List.getD_eq_getElem?_getD]
    rw [hword, hj]
    rfl

/-! ### Polynomial-time certificates for verifier subroutines -/

section PolyTime

open ComputableInPolyTime

private lemma bitsBinaryValue_mod_pt {γ : Type} {encIn : γ ↪ List Bool}
    {w : γ → List Bool} {p : γ → ℕ}
    (hw : ComputableInPolyTime w encIn encBits)
    (hp : ComputableInPolyTime p encIn encNat) :
    ComputableInPolyTime (fun x => binaryValue (w x) % p x) encIn encNat :=
  binary_mod' (bitsBinaryValue.comp hw) hp

private lemma elemWidth_pt {γ : Type} {encIn : γ ↪ List Bool} {p : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encNat) :
    ComputableInPolyTime (fun x => elemWidth (p x)) encIn encUnary := by
  unfold elemWidth
  have hlog : ComputableInPolyTime (fun x => Nat.log 2 (p x)) encIn encUnary :=
    binary_log_two.comp hp
  exact hlog.unary_add' (const 1)

private lemma polyLimit_pt {γ : Type} {encIn : γ ↪ List Bool} {p D : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hD : ComputableInPolyTime D encIn encUnary) :
    ComputableInPolyTime (fun x => polyLimit (p x) (D x)) encIn encUnary := by
  unfold polyLimit
  have h1 := hD.unary_add' (const 1)
  have hw := elemWidth_pt hp
  exact unary_mul.comp (h1.prod hw)

private lemma unary_sum_pt : ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have hfold := foldl' (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    (list := fun l => l) (init := fun _ => 0) (step := (· + ·))
    id' (const 0) unary_add
    (B := fun l => (encList encUnary l).length) .self fun l i _ => by
      have htake : ((l.take i).foldl (· + ·) 0) = (l.take i).sum :=
        (List.sum_eq_foldl_nat (xs := l.take i)).symm
      rw [htake]
      simp only [encUnary_apply, List.length_replicate]
      have hsub : (l.take i).sum ≤ l.sum := by
        calc (l.take i).sum ≤ (l.take i).sum + (l.drop i).sum := Nat.le_add_right _ _
          _ = ((l.take i) ++ l.drop i).sum := (List.sum_append).symm
          _ = l.sum := by rw [List.take_append_drop]
      have hlen : ∀ xs : List ℕ, xs.sum ≤ (encList encUnary xs).length := by
        intro xs
        rw [length_encList]
        induction xs with
        | nil => simp
        | cons a xs ih =>
          rw [List.sum_cons, List.map_cons, List.sum_cons]
          have ha : (encUnary a).length = a := by simp [encUnary_apply]
          omega
      exact hsub.trans (hlen l)
  simpa only [← List.sum_eq_foldl_nat, id_eq] using hfold

private lemma challengeCount_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime (fun ι => challengeCount (F.circuit ι)) encI encUnary := by
  unfold challengeCount
  have hd := F.uniform.depth_polyTime
  have hw := F.uniform.width_polyTime
  have hwd := hw.comp (id'.prod hd)
  have hrng : ComputableInPolyTime (fun ι => List.range (F.circuit ι).depth)
      encI (encList encUnary) := range.comp hd
  have hterm : ComputableInPolyTime (fun q : I × ℕ => 2 * (F.circuit q.1).width q.2 + 1)
      (encPair encI encUnary) encUnary :=
    ((const 2).unary_mul' hw).unary_add' (const 1)
  exact hwd.unary_add' (unary_sum_pt.comp (mapWith hterm id' hrng))

private lemma layerCost_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime (fun ι => layerCost (F.circuit ι)) encI encUnary := by
  unfold layerCost
  have hd := F.uniform.depth_polyTime
  have hw := F.uniform.width_polyTime
  have hwd := hw.comp (id'.prod hd)
  have hrng : ComputableInPolyTime (fun ι => List.range (F.circuit ι).depth)
      encI (encList encUnary) := range.comp hd
  have hterm : ComputableInPolyTime (fun q : I × ℕ => 5 * (F.circuit q.1).width q.2)
      (encPair encI encUnary) encUnary :=
    (const 5).unary_mul' hw
  exact ((const 1).unary_add' hwd).unary_add' (unary_sum_pt.comp (mapWith hterm id' hrng))

private lemma minModulus_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime (fun ι => minModulus (F.circuit ι)) encI encUnary := by
  unfold minModulus
  exact (const 3).unary_mul' (layerCost_pt F)

private lemma coinBits_pt {γ : Type} {encIn : γ ↪ List Bool} {p M : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hM : ComputableInPolyTime M encIn encUnary) :
    ComputableInPolyTime (fun x => coinBits (p x) (M x)) encIn encUnary := by
  unfold coinBits
  have h1 := ((const 2).unary_mul' ((binary_log_two.comp hp).unary_add' (const 1)))
  have h2 := (unary_log_two.comp (hM.unary_add' (const 1))).unary_add' (const 1)
  exact h1.unary_add' h2

private lemma lineMod_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p k t : γ → ℕ} {y w : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hy : ComputableInPolyTime y encIn encNatList)
    (hw : ComputableInPolyTime w encIn encNatList)
    (ht : ComputableInPolyTime t encIn encNat) :
    ComputableInPolyTime (fun x => lineMod (p x) (k x) (y x) (w x) (t x)) encIn encNatList := by
  unfold lineMod
  have hp0 : ComputableInPolyTime (fun x => decide (p x = 0)) encIn encBool :=
    decide_eq' hp (const 0)
  have hnil : ComputableInPolyTime (fun x => List.replicate (k x) 0) encIn encNatList :=
    replicate (encA := encNat) (encIn := encIn) hk (const 0)
  have hrng : ComputableInPolyTime (fun x => List.range (k x)) encIn (encList encUnary) :=
    range.comp hk
  have hcoord : ComputableInPolyTime
      (fun q : γ × ℕ =>
        ((y q.1).getD q.2 0 +
          t q.1 * subModNat (p q.1) ((w q.1).getD q.2 0) ((y q.1).getD q.2 0)) % p q.1)
      (encPair encIn encUnary) encNat := by
    have hyj := listGetDWithInput (hy.comp (fst _ _)) (snd _ _) 0
    have hwj := listGetDWithInput (hw.comp (fst _ _)) (snd _ _) 0
    have hsub := computableInPolyTime_subModNat (hp.comp (fst _ _)) hwj hyj
    exact binary_mod' (binary_add' hyj (binary_mul' (ht.comp (fst _ _)) hsub)) (hp.comp (fst _ _))
  exact ite_decide hp0 hnil (mapWith hcoord id' hrng)

private lemma hornerModBin_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p z : γ → ℕ} {l : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hz : ComputableInPolyTime z encIn encNat)
    (hl : ComputableInPolyTime l encIn encNatList) :
    ComputableInPolyTime (fun x => hornerModBin (p x) (z x) (l x)) encIn encNat := by
  unfold hornerModBin
  have hp0 : ComputableInPolyTime (fun x => decide (p x = 0)) encIn encBool :=
    decide_eq' hp (const 0)
  have hmod : ComputableInPolyTime (fun x => max (p x) 1) encIn encNat :=
    (ite_decide hp0 (const 1) hp).of_enc_eq fun x => by
      by_cases h : p x = 0
      · simp [h]
      · have : 1 ≤ p x := Nat.one_le_iff_ne_zero.mpr h
        simp [h, Nat.max_eq_left this]
  have hrev : ComputableInPolyTime (fun x => (l x).reverse) encIn encNatList :=
    (listReverse encNat).comp hl
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × ℕ => (q.2 + q.1.1.2 * q.1.2) % q.1.1.1)
      (encPair (encPair (encPair encNat encNat) encNat) encNat) encNat := by
    let E := encPair (encPair (encPair encNat encNat) encNat) encNat
    have hm' : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ => q.1.1.1) E encNat := by
      fun_prop
    have hz' : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ => q.1.1.2) E encNat := by
      fun_prop
    have hacc : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ => q.1.2) E encNat := by
      fun_prop
    have ha : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ => q.2) E encNat := by
      fun_prop
    exact binary_mod' (binary_add' ha (binary_mul' hz' hacc)) hm'
  have hfold := foldlWith (encA := encNat) (encB := encNat) (encL := encNatList)
    (encP := encPair encNat encNat)
    (par := fun x => (max (p x) 1, z x)) (list := fun x => (l x).reverse) (init := fun _ => 0)
    (step := fun par acc a => (a + par.2 * acc) % par.1)
    (hmod.prod hz) hrev (const (encIn := encIn) (encOut := encNat) 0) hstep
    (B := fun x => (encNat (p x)).length + 1)
    (hp.polyBounded_length.add (.const 1))
    (fun x i _ => by
      have hlt := foldl_horner_lt (p := p x) (z := z x) (List.take i (l x).reverse)
      simp only [encNat_apply, Nat.size_eq_bits_len]
      have hmle : max (p x) 1 < 2 ^ ((p x).size + 1) := by
        rw [Nat.pow_succ]
        have hpLt := Nat.lt_size_self (p x)
        have hpos : 0 < 2 ^ (p x).size := by positivity
        exact max_lt (hpLt.trans (by omega)) (by omega)
      exact Nat.size_le.2 (hlt.trans hmle))
  exact ite_decide hp0 (const 0) hfold

private lemma decodeResidues_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p D : γ → ℕ} {word : γ → List Bool}
    (hp : ComputableInPolyTime p encIn encNat)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hword : ComputableInPolyTime word encIn encBits) :
    ComputableInPolyTime (fun x => decodeResidues (p x) (D x) (word x)) encIn encNatList := by
  unfold decodeResidues
  have hp0 : ComputableInPolyTime (fun x => decide (p x = 0)) encIn encBool :=
    decide_eq' hp (const 0)
  have hrows : ComputableInPolyTime (fun x => listRows (D x + 1) (elemWidth (p x)) (word x))
      encIn (encList encBits) :=
    bitsRowsWithInput (hD.unary_add' (const 1)) (elemWidth_pt hp) hword
  have hmap := mapWith (bitsBinaryValue_mod_pt (snd encIn encBits) (hp.comp (fst encIn encBits)))
    id' hrows
  exact ite_decide hp0 (const []) hmap

private lemma evalTableMLEMod_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p k : γ → ℕ} {vals r : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hvals : ComputableInPolyTime vals encIn encNatList)
    (hr : ComputableInPolyTime r encIn encNatList) :
    ComputableInPolyTime (fun x => evalTableMLEMod (p x) (k x) (vals x) (r x)) encIn encNat := by
  unfold evalTableMLEMod
  have hp0 : ComputableInPolyTime (fun x => decide (p x = 0)) encIn encBool :=
    decide_eq' hp (const 0)
  have hlen : ComputableInPolyTime (fun x => (vals x).length) encIn encUnary :=
    (length_list encNat).comp hvals
  have hrngV : ComputableInPolyTime (fun x => List.range (vals x).length)
      encIn (encList encUnary) :=
    range.comp hlen
  have hidxBits : ComputableInPolyTime (fun q : γ × ℕ => q.2.bits)
      (encPair encIn encUnary) encBits :=
    natBits.comp (unary_to_binary.comp (snd encIn encUnary))
  have hcond : ComputableInPolyTime (fun q : γ × ℕ => decide (q.2.bits.length ≤ k q.1))
      (encPair encIn encUnary) encBool :=
    unary_le.comp ((length_bits.comp hidxBits).prod (hk.comp (fst _ _)))
  have hw : ComputableInPolyTime (fun q : γ × ℕ => binaryWord (k q.1) q.2)
      (encPair encIn encUnary) encBits := by
    unfold binaryWord
    have hpad := (bitsReplicate false).comp
      (unary_sub.comp ((hk.comp (fst _ _)).prod (length_bits.comp hidxBits)))
    have hrev := bitsReverse.comp hidxBits
    exact bitsAppend hpad hrev
  have hrngK : ComputableInPolyTime (fun q : γ × ℕ => List.range (k q.1))
      (encPair encIn encUnary) (encList encUnary) :=
    range.comp (hk.comp (fst _ _))
  have hlit : ComputableInPolyTime
      (fun u : (γ × ℕ) × ℕ =>
        litFactorNat (p u.1.1) ((binaryWord (k u.1.1) u.1.2).getD u.2 false)
          ((r u.1.1).getD u.2 0))
      (encPair (encPair encIn encUnary) encUnary) encNat :=
    computableInPolyTime_litFactorNat (hp.comp ((fst _ _).comp (fst _ _)))
      (bitsGetDWithInput (hw.comp (fst _ _)) (snd _ _) false)
      (listGetDWithInput (hr.comp ((fst _ _).comp (fst _ _))) (snd _ _) 0)
  have hbasis : ComputableInPolyTime
      (fun q : γ × ℕ =>
        ((List.range (k q.1)).map fun j =>
          litFactorNat (p q.1) ((binaryWord (k q.1) q.2).getD j false) ((r q.1).getD j 0)).prod %
            p q.1)
      (encPair encIn encUnary) encNat :=
    binary_mod' (binary_prod.comp (mapWith hlit id' hrngK)) (hp.comp (fst _ _))
  have hterm : ComputableInPolyTime
      (fun q : γ × ℕ =>
        if decide (q.2.bits.length ≤ k q.1) then
          (((vals q.1).getD q.2 0 % p q.1) *
            (((List.range (k q.1)).map fun j =>
              litFactorNat (p q.1) ((binaryWord (k q.1) q.2).getD j false)
                ((r q.1).getD j 0)).prod % p q.1)) % p q.1
        else 0)
      (encPair encIn encUnary) encNat :=
    ite_decide hcond
      (binary_mod'
        (binary_mul' (binary_mod' (listGetDWithInput (hvals.comp (fst _ _)) (snd _ _) 0)
          (hp.comp (fst _ _))) hbasis)
        (hp.comp (fst _ _)))
      (const 0)
  exact ite_decide hp0 (const 0) (binary_mod' (binary_sum.comp (mapWith hterm id' hrngV)) hp)

end PolyTime

/-! ### Executable polynomial-time word GKR verifier -/

/-- State tracked across the `2 * width i` sumcheck rounds of one GKR layer. -/
private structure SumcheckState where
  /-- Accumulated sumcheck challenges `(y, w)` (length `j ≤ 2 * width i`). -/
  challenges : List ℕ
  /-- Current claimed partial sum modulo `p`. -/
  claim : ℕ
  /-- Accumulated check bit across sumcheck rounds completed so far. -/
  ok : Bool

/-- Tuple encoding of `SumcheckState`, keeping `challenges` and `claim` in binary. -/
private enc_structure encSumcheckState : SumcheckState where
  challenges : encNatList,
  claim : encNat,
  ok : encBool

/-- State tracked across the layer-by-layer GKR descent (`depth` down to `0`). -/
private structure LayerState where
  /-- Number of layers still to descend (`depth` initially, `0` before the input step). -/
  remaining : ℕ
  /-- Claimed evaluation point at layer `remaining`. -/
  point : List ℕ
  /-- Claimed value `W̃_{remaining}(point) mod p`. -/
  value : ℕ
  /-- Accumulated check bit across all rounds completed so far. -/
  ok : Bool

/-- Tuple encoding of `LayerState`, with `remaining` in unary and coordinates/value in binary. -/
private enc_structure encLayerState : LayerState where
  remaining : encUnary,
  point : encNatList,
  value : encNat,
  ok : encBool

/-- One sumcheck round of GKR on binary modulus `p` and coin width `coinWidth`: read the degree-`2`
prover polynomial `g`, draw a challenge `r ← sampleModNat coinWidth p`, send `encNat r`, verify
`g(0) + g(1) ≡ sc.claim (mod p)`, and update the challenge list and claim. -/
private noncomputable def sumcheckStep (p coinWidth : ℕ) (sc : SumcheckState) :
    WordOracleComp Unit SumcheckState := do
  let raw ← List.take (polyLimit p 2) <$> ProbOracleComp.query ((), [])
  let r ← ProbOracleComp.sample (sampleModNat coinWidth p)
  let _ ← List.take 0 <$> ProbOracleComp.query ((), encNat r)
  let rs := decodeResidues p 2 raw
  let stepOk := decide ((hornerModBin p 0 rs + hornerModBin p 1 rs) % p = sc.claim % p)
  return ⟨sc.challenges ++ [r], hornerModBin p r rs, sc.ok && stepOk⟩

/-- The GKR line-reduction step after layer `i := st.remaining - 1` sumcheck finishes: read the
degree-`width i` line polynomial `q`, evaluate `F.evalWiring` for `.add` and `.mul` at `(z, y, w)`,
draw `t ← sampleModNat coinWidth p`, send `encNat t`, check
`sc.claim ≡ ãdd*(q 0 + q 1) + m̃ult*(q 0 * q 1)`, and output the reduced claim on `line y w t`. -/
private noncomputable def lineStepExec {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) (coinWidth : ℕ)
    (st : LayerState) (sc : SumcheckState) : WordOracleComp Unit LayerState := do
  let p := inst.modulus
  let i := st.remaining - 1
  let kIn := (F.circuit inst.index).width i
  let y := sc.challenges.take kIn
  let w := (sc.challenges.drop kIn).take kIn
  let raw ← List.take (polyLimit p kIn) <$> ProbOracleComp.query ((), [])
  let t ← ProbOracleComp.sample (sampleModNat coinWidth p)
  let _ ← List.take 0 <$> ProbOracleComp.query ((), encNat t)
  let rs := decodeResidues p kIn raw
  let addVal := F.evalWiring ⟨inst.index, .add, i, p, st.point, y, w⟩
  let mulVal := F.evalWiring ⟨inst.index, .mul, i, p, st.point, y, w⟩
  let q0 := hornerModBin p 0 rs
  let q1 := hornerModBin p 1 rs
  let rhs := (addVal * ((q0 + q1) % p) + mulVal * ((q0 * q1) % p)) % p
  let lineOk := decide (sc.claim % p = rhs)
  return ⟨i, lineMod p kIn y w t, hornerModBin p t rs, sc.ok && lineOk⟩

/-- One complete GKR layer reduction (`sumcheckStage` followed by `lineStepExec`) descending from
layer `st.remaining` to `st.remaining - 1`. -/
private noncomputable def layerExec {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) (coinWidth : ℕ)
    (st : LayerState) : WordOracleComp Unit LayerState := do
  let i := st.remaining - 1
  let kIn := (F.circuit inst.index).width i
  let sc ← OracleComp.iterate (2 * kIn) (sumcheckStep inst.modulus coinWidth)
    ⟨[], st.value, st.ok⟩
  lineStepExec F inst coinWidth st sc

/-- **Executable polynomial-time word GKR verifier** for a `UniformGKRFamily I encI`
(a verifier-side, `HasPolyTimeWiringMLE` step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] §3 / [Thaler, §4.6][Thaler2022]).
Rejects immediately whenever `inst.modulus < minModulus (F.circuit inst.index)`. Otherwise samples a
random output evaluation point, evaluates the claimed-output multilinear extension sparsely,
descends `depth` layers of sumcheck and line reduction using `F.evalWiring`, and checks the final
input-layer evaluation against `inst.input`. -/
noncomputable def UniformGKRFamily.verifier {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) : WordOracleComp Unit Bool :=
  let C := F.circuit inst.index
  let d := C.depth
  let kOut := C.width d
  let kIn := C.width 0
  let M := challengeCount C
  let coinWidth := coinBits inst.modulus M
  if decide (minModulus C ≤ inst.modulus) then do
    let r ← ProbOracleComp.sample (OracleComp.replicate kOut (sampleModNat coinWidth inst.modulus))
    let _ ← List.take 0 <$> ProbOracleComp.query ((), encNatList r)
    let init : LayerState :=
      ⟨d, r, evalTableMLEMod inst.modulus kOut inst.claimedOutput r, true⟩
    let final ← OracleComp.iterate d (layerExec F inst coinWidth) init
    return final.ok && decide
      (evalTableMLEMod inst.modulus kIn inst.input final.point = final.value % inst.modulus)
  else
    pure false

/-- `UniformGKRFamily.verifier` rejects immediately whenever `inst.modulus` is below
`minModulus (F.circuit inst.index)`. -/
theorem UniformGKRFamily.verifier_of_lt_minModulus {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) {inst : Instance I}
    (hlt : inst.modulus < minModulus (F.circuit inst.index)) :
    F.verifier inst = pure false := by
  have hnot : ¬ minModulus (F.circuit inst.index) ≤ inst.modulus := not_le.mpr hlt
  simp [UniformGKRFamily.verifier, hnot]

/-! ### Native multi-tape Turing-machine polynomial-time runtime -/

section Runtime

open ComputableInPolyTime

private lemma sampleModNat_support_size_le {coinWidth p r : ℕ}
    (hr : r ∈ (ProbComp.eval (sampleModNat coinWidth p)).support) :
    (encNat r).length ≤ (encNat p).length + coinWidth + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h' : r ∈ (ProbComp.eval (sampleBinaryNat coinWidth)).support := by
      simpa [sampleModNat, ProbComp.eval_map] using hr
    have hlt := (ProbComp.mem_support_sampleBinaryNat_iff coinWidth r).mp h'
    exact (Nat.size_le.2 hlt).trans (by omega)
  · rw [sampleModNat, ProbComp.eval_map, PMF.mem_support_map_iff] at hr
    obtain ⟨x, _, rfl⟩ := hr
    have hlt : x % p < p := Nat.mod_lt _ hp
    exact (Nat.size_le_size hlt.le).trans (by omega)

private lemma hornerModBin_size_le {p z : ℕ} {l : List ℕ} :
    (encNat (hornerModBin p z l)).length ≤ (encNat p).length + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [hornerModBin]
  · have hlt := hornerModBin_lt hp z l
    exact (Nat.size_le_size hlt.le).trans (Nat.le_succ _)

private lemma evalTableMLEMod_size_le {p k : ℕ} {vals r : List ℕ} :
    (encNat (evalTableMLEMod p k vals r)).length ≤ (encNat p).length + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [evalTableMLEMod]
  · have hlt := evalTableMLEMod_lt hp k vals r
    exact (Nat.size_le_size hlt.le).trans (Nat.le_succ _)

private lemma length_encNatList_of_forall_size {xs : List ℕ} {B : ℕ}
    (hxs : ∀ v ∈ xs, (encNat v).length ≤ B) :
    (encNatList xs).length ≤ xs.length * (2 * B + 1) := by
  rw [length_encList]
  calc (xs.map fun a => 2 * (encNat a).length + 1).sum
      ≤ (xs.map fun _ => 2 * B + 1).sum :=
        List.sum_le_sum fun a ha => by have := hxs a ha; omega
    _ = xs.length * (2 * B + 1) := by simp

private lemma uniform_width_polyBounded {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ∃ cW dW : ℕ, ∀ (ι : I) (i : ℕ), i ≤ (F.circuit ι).depth →
      (F.circuit ι).width i ≤ cW * ((encI ι).length + 1) ^ dW := by
  obtain ⟨cD, dD, hD⟩ := F.uniform.depth_polyTime.polyBounded.exists_le
  obtain ⟨cW, dW, hW⟩ := F.uniform.width_polyTime.polyBounded.exists_le
  refine ⟨cW * (2 * cD + 5) ^ dW, dD * dW + dW, fun ι i hi => ?_⟩
  have hwi := hW (ι, i)
  have hid : i ≤ cD * ((encI ι).length + 1) ^ dD := hi.trans (hD ι)
  have hpair : (encPair encI encUnary (ι, i)).length = 2 * (encI ι).length + 1 + i := by
    simp [encUnary_apply, List.length_replicate]
  rw [hpair] at hwi
  set n := (encI ι).length + 1
  have hn1 : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
  have hpowD : 1 ≤ n ^ dD := Nat.one_le_pow _ _ hn1
  have hlen : 2 * (encI ι).length + 1 + i + 1 ≤ (2 * cD + 5) * n ^ max 1 dD := by
    have hn_le : n ≤ n ^ max 1 dD := Nat.le_self_pow (by omega) n
    have hD_le : n ^ dD ≤ n ^ max 1 dD := Nat.pow_le_pow_right hn1 (le_max_right _ _)
    have hone : 1 ≤ n ^ max 1 dD := Nat.one_le_pow _ _ hn1
    have hc : 2 * n + cD * n ^ dD ≤ 2 * n ^ max 1 dD + cD * n ^ max 1 dD := by
      gcongr
    have hi' : i ≤ cD * n ^ dD := hid
    have hn' : (encI ι).length + 1 = n := rfl
    calc 2 * (encI ι).length + 1 + i + 1
        ≤ 2 * n + cD * n ^ dD := by omega
      _ ≤ 2 * n ^ max 1 dD + cD * n ^ max 1 dD := hc
      _ = (2 + cD) * n ^ max 1 dD := by ring
      _ ≤ (2 * cD + 5) * n ^ max 1 dD := Nat.mul_le_mul_right _ (by omega)
  have hw' := hwi.trans (Nat.mul_le_mul_left cW (Nat.pow_le_pow_left hlen dW))
  rw [Nat.mul_pow, ← Nat.pow_mul] at hw'
  have hexp : max 1 dD * dW ≤ dD * dW + dW := by
    rcases Nat.eq_zero_or_pos dD with rfl | hpos
    · simp
    · rw [max_eq_right hpos]; exact Nat.le_add_right _ _
  calc (F.circuit ι).width i
      ≤ cW * ((2 * cD + 5) ^ dW * n ^ (max 1 dD * dW)) := hw'
    _ = cW * (2 * cD + 5) ^ dW * n ^ (max 1 dD * dW) := by ring
    _ ≤ cW * (2 * cD + 5) ^ dW * n ^ (dD * dW + dW) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 hexp)

private lemma sumcheckStep_ppt :
    IsOraclePPTOn (encPair (encPair encNat encUnary) encSumcheckState) encSumcheckState
      (fun pair : (ℕ × ℕ) × SumcheckState => sumcheckStep pair.1.1 pair.1.2 pair.2) := by
  unfold sumcheckStep
  let encIn := encPair (encPair encNat encUnary) encSumcheckState
  have hp : ComputableInPolyTime (fun x : (ℕ × ℕ) × SumcheckState => x.1.1) encIn encNat := by
    fun_prop
  have hcw : ComputableInPolyTime (fun x : (ℕ × ℕ) × SumcheckState => x.1.2) encIn encUnary := by
    fun_prop
  have hsc : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × SumcheckState => x.2) encIn encSumcheckState := by
    fun_prop
  have hAsk : IsOraclePPTOn encIn encBits
      (fun x => List.take (polyLimit x.1.1 2) <$> ProbOracleComp.query ((), [])) :=
    IsOraclePPTOn.query_take () (const []) (polyLimit_pt hp (const 2))
  have hSample : IsOraclePPTOn (encPair encIn encBits) encNat
      (fun u => ProbOracleComp.sample (sampleModNat u.1.1.2 u.1.1.1)) :=
    (isPPTOn_sampleModNat (hcw.comp (fst _ _)) (hp.comp (fst _ _))).isOraclePPTOn
      (Operation := Unit)
  have hSend : IsOraclePPTOn (encPair (encPair encIn encBits) encNat) encBits
      (fun u => List.take 0 <$> ProbOracleComp.query ((), encNat u.2)) :=
    IsOraclePPTOn.query_take ()
      ((of_eq (f := encNat) (encIn := encNat) (encOut := encBits) fun _ => rfl).comp
        (snd (encPair encIn encBits) encNat))
      (const 0)
  have hPost : ComputableInPolyTime
      (fun u : ((((ℕ × ℕ) × SumcheckState) × List Bool) × ℕ) × List Bool =>
        let x := u.1.1.1
        let raw := u.1.1.2
        let r := u.1.2
        let rs := decodeResidues x.1.1 2 raw
        let stepOk := decide ((hornerModBin x.1.1 0 rs + hornerModBin x.1.1 1 rs) % x.1.1 =
          x.2.claim % x.1.1)
        ({ challenges := x.2.challenges ++ [r],
           claim := hornerModBin x.1.1 r rs,
           ok := x.2.ok && stepOk } : SumcheckState))
      (encPair (encPair (encPair encIn encBits) encNat) encBits) encSumcheckState := by
    let encAll := encPair (encPair (encPair encIn encBits) encNat) encBits
    have hx : ComputableInPolyTime (fun u => u.1.1.1) encAll encIn := by fun_prop
    have hp' := hp.comp hx
    have hsc' := hsc.comp hx
    have hraw : ComputableInPolyTime (fun u => u.1.1.2) encAll encBits := by fun_prop
    have hr : ComputableInPolyTime (fun u => u.1.2) encAll encNat := by fun_prop
    have hrs := decodeResidues_pt hp' (const 2) hraw
    have h0 := hornerModBin_pt hp' (const 0) hrs
    have h1 := hornerModBin_pt hp' (const 1) hrs
    have hrVal := hornerModBin_pt hp' hr hrs
    have hSum := binary_mod' (binary_add' h0 h1) hp'
    have hClaimMod := binary_mod' (encSumcheckState_claim_polyTime hsc') hp'
    have hStepOk := decide_eq' hSum hClaimMod
    have hChall := (encSumcheckState_challenges_polyTime hsc').listAppend' (hr.cons' (const []))
    have hOk := (encSumcheckState_ok_polyTime hsc').bool_and' hStepOk
    exact encSumcheckState_mk_polyTime hChall hrVal hOk
  exact hAsk.bind_with (hSample.bind_with (hSend.bind_with
    (hPost.isOraclePPTOn (Operation := Unit))))

private lemma lineStepExec_post_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime
      (fun q :
          ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        let u := q.1.1.1
        let raw := q.1.1.2
        let t := q.1.2
        let p := u.1.1.modulus
        let i := u.2.1.remaining - 1
        let kIn := (F.circuit u.1.1.index).width i
        let y := u.2.2.challenges.take kIn
        let w := (u.2.2.challenges.drop kIn).take kIn
        let rs := decodeResidues p kIn raw
        let addVal := F.evalWiring ⟨u.1.1.index, .add, i, p, u.2.1.point, y, w⟩
        let mulVal := F.evalWiring ⟨u.1.1.index, .mul, i, p, u.2.1.point, y, w⟩
        let q0 := hornerModBin p 0 rs
        let q1 := hornerModBin p 1 rs
        let rhs := (addVal * ((q0 + q1) % p) + mulVal * ((q0 * q1) % p)) % p
        let lineOk := decide (u.2.2.claim % p = rhs)
        ({ remaining := i,
           point := lineMod p kIn y w t,
           value := hornerModBin p t rs,
           ok := u.2.2.ok && lineOk } : LayerState))
      (encPair (encPair (encPair
        (encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState))
        encBits) encNat) encBits)
      encLayerState := by
  let encIn :=
    encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState)
  let encAll := encPair (encPair (encPair encIn encBits) encNat) encBits
  have hu : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.1.1) encAll encIn := by fun_prop
  have hraw : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.1.2) encAll encBits := by fun_prop
  have ht : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.2) encAll encNat := by fun_prop
  have hInst : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.1.1) encIn (encInstance I encI) := by fun_prop
  have hSt : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.2.1) encIn encLayerState := by fun_prop
  have hSc : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.2.2) encIn encSumcheckState := by fun_prop
  have hInst' := hInst.comp hu
  have hSt' := hSt.comp hu
  have hSc' := hSc.comp hu
  have hp' := encInstance_modulus_polyTime I encI hInst'
  have hIdx' := encInstance_index_polyTime I encI hInst'
  have hi' := unary_sub.comp ((encLayerState_remaining_polyTime hSt').prod (const 1))
  have hkIn' := F.uniform.width_polyTime.comp (ComputableInPolyTime.prod hIdx' hi')
  have hCh := encSumcheckState_challenges_polyTime hSc'
  have hy := listTakeWithInput hCh hkIn'
  have hw := listTakeWithInput (listDropWithInput hCh hkIn') hkIn'
  have hz := encLayerState_point_polyTime hSt'
  have hAddQ := encWiringMLEQuery_mk_polyTime I encI hIdx' (const Gate.add) hi' hp' hz hy hw
  have hMulQ := encWiringMLEQuery_mk_polyTime I encI hIdx' (const Gate.mul) hi' hp' hz hy hw
  have hAdd := F.wiringMLE.polyTime.comp hAddQ
  have hMul := F.wiringMLE.polyTime.comp hMulQ
  have hrs := decodeResidues_pt hp' hkIn' hraw
  have hq0 := hornerModBin_pt hp' (const 0) hrs
  have hq1 := hornerModBin_pt hp' (const 1) hrs
  have hrhs := binary_mod' (binary_add'
    (binary_mul' hAdd (binary_mod' (binary_add' hq0 hq1) hp'))
    (binary_mul' hMul (binary_mod' (binary_mul' hq0 hq1) hp'))) hp'
  have hlineOk := decide_eq' (binary_mod' (encSumcheckState_claim_polyTime hSc') hp') hrhs
  have hLineMod := lineMod_pt hp' hkIn' hy hw ht
  have hVal := hornerModBin_pt hp' ht hrs
  have hOk := (encSumcheckState_ok_polyTime hSc').bool_and' hlineOk
  exact encLayerState_mk_polyTime hi' hLineMod hVal hOk

private lemma lineStepExec_ppt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn
      (encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState))
      encLayerState
      (fun u => lineStepExec F u.1.1 u.1.2 u.2.1 u.2.2) := by
  unfold lineStepExec
  let encIn :=
    encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState)
  have hInst : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.1.1) encIn (encInstance I encI) := by fun_prop
  have hcw : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.1.2) encIn encUnary := by fun_prop
  have hSt : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.2.1) encIn encLayerState := by fun_prop
  have hP := encInstance_modulus_polyTime I encI hInst
  have hIdx := encInstance_index_polyTime I encI hInst
  have hLayer : ComputableInPolyTime (fun u => u.2.1.remaining - 1) encIn encUnary :=
    unary_sub.comp ((encLayerState_remaining_polyTime hSt).prod (const 1))
  have hkIn : ComputableInPolyTime
      (fun u => (F.circuit u.1.1.index).width (u.2.1.remaining - 1)) encIn encUnary :=
    F.uniform.width_polyTime.comp (ComputableInPolyTime.prod hIdx hLayer)
  have hAsk : IsOraclePPTOn encIn encBits
      (fun u =>
        List.take (polyLimit u.1.1.modulus ((F.circuit u.1.1.index).width (u.2.1.remaining - 1)))
          <$> ProbOracleComp.query ((), [])) :=
    IsOraclePPTOn.query_take () (const []) (polyLimit_pt hP hkIn)
  have hSample : IsOraclePPTOn (encPair encIn encBits) encNat
      (fun q => ProbOracleComp.sample (sampleModNat q.1.1.2 q.1.1.1.modulus)) :=
    (isPPTOn_sampleModNat (hcw.comp (fst _ _)) (hP.comp (fst _ _))).isOraclePPTOn
      (Operation := Unit)
  have hSend : IsOraclePPTOn (encPair (encPair encIn encBits) encNat) encBits
      (fun q => List.take 0 <$> ProbOracleComp.query ((), encNat q.2)) :=
    IsOraclePPTOn.query_take ()
      ((of_eq (f := encNat) (encIn := encNat) (encOut := encBits) fun _ => rfl).comp
        (snd (encPair encIn encBits) encNat))
      (const 0)
  exact hAsk.bind_with (hSample.bind_with (hSend.bind_with
    ((lineStepExec_post_pt F).isOraclePPTOn (Operation := Unit))))

private lemma layerExec_sumcheckLoop_ppt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn (encPair (encPair (encInstance I encI) encUnary) encLayerState) encSumcheckState
      (fun pair => OracleComp.iterate
        (2 * (F.circuit pair.1.1.index).width (pair.2.remaining - 1))
        (sumcheckStep pair.1.1.modulus pair.1.2)
        ⟨[], pair.2.value, pair.2.ok⟩) := by
  let encOuter := encPair (encPair (encInstance I encI) encUnary) encLayerState
  have hInst : ComputableInPolyTime (fun p : (Instance I × ℕ) × LayerState => p.1.1)
      encOuter (encInstance I encI) := by fun_prop
  have hcw : ComputableInPolyTime (fun p : (Instance I × ℕ) × LayerState => p.1.2)
      encOuter encUnary := by fun_prop
  have hSt : ComputableInPolyTime (fun p : (Instance I × ℕ) × LayerState => p.2)
      encOuter encLayerState := by fun_prop
  have hkIn : ComputableInPolyTime
      (fun p : (Instance I × ℕ) × LayerState =>
        (F.circuit p.1.1.index).width (p.2.remaining - 1)) encOuter encUnary :=
    F.uniform.width_polyTime.comp
      (ComputableInPolyTime.prod (encInstance_index_polyTime I encI hInst)
        (unary_sub.comp ((encLayerState_remaining_polyTime hSt).prod (const 1))))
  have hCount : ComputableInPolyTime
      (fun p : (Instance I × ℕ) × LayerState =>
        2 * (F.circuit p.1.1.index).width (p.2.remaining - 1)) encOuter encUnary :=
    (const 2).unary_mul' hkIn
  have hInit : ComputableInPolyTime
      (fun p : (Instance I × ℕ) × LayerState =>
        ({ challenges := [], claim := p.2.value, ok := p.2.ok } : SumcheckState))
      encOuter encSumcheckState :=
    encSumcheckState_mk_polyTime (const []) (encLayerState_value_polyTime hSt)
      (encLayerState_ok_polyTime hSt)
  have hStep' : IsOraclePPTOn (encPair encOuter encSumcheckState) encSumcheckState
      (fun q => sumcheckStep q.1.1.1.modulus q.1.1.2 q.2) := by
    have hPre : ComputableInPolyTime
        (fun q : ((Instance I × ℕ) × LayerState) × SumcheckState =>
          ((q.1.1.1.modulus, q.1.1.2), q.2))
        (encPair encOuter encSumcheckState)
        (encPair (encPair encNat encUnary) encSumcheckState) := by
      have hp := encInstance_modulus_polyTime I encI (hInst.comp (fst encOuter encSumcheckState))
      have hc := hcw.comp (fst encOuter encSumcheckState)
      exact (hp.prod hc).prod (snd encOuter encSumcheckState)
    exact sumcheckStep_ppt.preprocess hPre
  obtain ⟨cK, dK, hK⟩ := hkIn.polyBounded.exists_le
  let scSizeFun : ℕ → ℕ := fun n =>
    2 * (2 * (cK * (n + 1) ^ dK) * (2 * (2 * n + 1) + 1)) + 2 * (2 * n + 1) + 16
  have hSizeFun : PolynomiallyBounded scSizeFun := by
    dsimp only [scSizeFun]
    fun_prop
  have hSize : PolyBounded (fun p => (encOuter p).length)
      (fun p => scSizeFun (encOuter p).length) :=
    PolyBounded.of_polynomiallyBounded (fun p => (encOuter p).length) hSizeFun
  let scInv (p : (Instance I × ℕ) × LayerState) (j : ℕ) (sc : SumcheckState) : Prop :=
    sc.challenges.length = j ∧
      (∀ v ∈ sc.challenges, (encNat v).length ≤ (encNat p.1.1.modulus).length + p.1.2 + 1) ∧
      (encNat sc.claim).length ≤ (encNat p.1.1.modulus).length + (encLayerState p.2).length + 1
  exact (IsOraclePPTOn.iterateWith_spec hCount hInit hStep' scInv
    (fun p => ⟨rfl, fun _ h => absurd h List.not_mem_nil, by
      have hvl := encLayerState_value_length_le p.2
      dsimp only
      omega⟩)
    (fun p j sc hj hsc next hnext => by
      simp only [sumcheckStep, OracleComp.mem_supportWith_bind_iff,
        OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
        ProbOracleComp.support_sample] at hnext
      obtain ⟨raw, -, r, hr, _, -, rfl⟩ := hnext
      refine ⟨by simp [hsc.1], fun v hv => ?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hsc.2.1 v hv
        · exact sampleModNat_support_size_le hr
      · exact (hornerModBin_size_le).trans (by omega))
    hSize
    (fun p j sc hj hsc => by
      have hOuterLen : (encPair (encInstance I encI) encUnary p.1).length ≤
          (encOuter p).length :=
        length_le_encPair_left _ _ p
      have hInstLen : (encInstance I encI p.1.1).length ≤ (encOuter p).length :=
        (length_le_encPair_left _ _ p.1).trans hOuterLen
      have hcwLen : p.1.2 ≤ (encOuter p).length := by
        refine le_trans ?_ ((length_le_encPair_right _ _ p.1).trans hOuterLen)
        simp [encUnary_apply]
      have hModLen : (encNat p.1.1.modulus).length ≤ (encOuter p).length :=
        (encInstance_modulus_length_le I encI p.1.1).trans hInstLen
      have hStLen : (encLayerState p.2).length ≤ (encOuter p).length :=
        length_le_encPair_right _ _ p
      have hchLen := length_encNatList_of_forall_size hsc.2.1
      have hj' : j ≤ 2 * (cK * ((encOuter p).length + 1) ^ dK) :=
        hj.trans (Nat.mul_le_mul_left 2 (hK p))
      rw [hsc.1] at hchLen
      have hB1 : (encNatList sc.challenges).length ≤
          2 * (cK * ((encOuter p).length + 1) ^ dK) * (2 * (2 * (encOuter p).length + 1) + 1) :=
        hchLen.trans (Nat.mul_le_mul (Nat.le_of_eq rfl |>.trans hj') (by omega))
      have hB2 : (encNat sc.claim).length ≤ 2 * (encOuter p).length + 1 := by omega
      dsimp only [scSizeFun]
      enc_len [encSumcheckState_apply, encSumcheckStateFields])).1

private lemma layerExec_ppt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn (encPair (encPair (encInstance I encI) encUnary) encLayerState) encLayerState
      (fun pair => layerExec F pair.1.1 pair.1.2 pair.2) := by
  let encOuter := encPair (encPair (encInstance I encI) encUnary) encLayerState
  have h1 : ComputableInPolyTime (fun q : ((Instance I × ℕ) × LayerState) × SumcheckState =>
      q.1.1) (encPair encOuter encSumcheckState) (encPair (encInstance I encI) encUnary) :=
    (fst (encPair (encInstance I encI) encUnary) encLayerState).comp
      (fst encOuter encSumcheckState)
  have h2 : ComputableInPolyTime (fun q : ((Instance I × ℕ) × LayerState) × SumcheckState =>
      q.1.2) (encPair encOuter encSumcheckState) encLayerState :=
    (snd (encPair (encInstance I encI) encUnary) encLayerState).comp
      (fst encOuter encSumcheckState)
  have h3 : ComputableInPolyTime (fun q : ((Instance I × ℕ) × LayerState) × SumcheckState =>
      q.2) (encPair encOuter encSumcheckState) encSumcheckState :=
    snd encOuter encSumcheckState
  have hLinePre := h1.prod (h2.prod h3)
  have hLine : IsOraclePPTOn (encPair encOuter encSumcheckState) encLayerState
      (fun q => lineStepExec F q.1.1.1 q.1.1.2 q.1.2 q.2) := by
    refine ((lineStepExec_ppt F).preprocess hLinePre).congr fun q State oracle s =>
      congrArg (fun p => ProbOracleComp.runWith oracle p s) ?_
    dsimp only [Function.comp_def]
  have hBound := (layerExec_sumcheckLoop_ppt F).bind_with
    (second := fun pair sc => lineStepExec F pair.1.1 pair.1.2 pair.2 sc) hLine
  refine hBound.congr fun pair State oracle s =>
    congrArg (fun p => ProbOracleComp.runWith oracle p s) ?_
  dsimp only [layerExec]

private lemma verifier_layerLoop_ppt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn (encPair (encPair (encInstance I encI) encNatList) encBits) encLayerState
      (fun p =>
        OracleComp.iterate (F.circuit p.1.1.index).depth
          (layerExec F p.1.1
            (coinBits p.1.1.modulus (challengeCount (F.circuit p.1.1.index))))
          ({ remaining := (F.circuit p.1.1.index).depth,
             point := p.1.2,
             value := evalTableMLEMod p.1.1.modulus
               ((F.circuit p.1.1.index).width (F.circuit p.1.1.index).depth)
               p.1.1.claimedOutput p.1.2,
             ok := true } : LayerState)) := by
  let encA := encPair (encPair (encInstance I encI) encNatList) encBits
  have h1 : ComputableInPolyTime (fun p : (Instance I × List ℕ) × List Bool => p.1.1)
      encA (encInstance I encI) :=
    (fst (encInstance I encI) encNatList).comp (fst _ encBits)
  have hr : ComputableInPolyTime (fun p : (Instance I × List ℕ) × List Bool => p.1.2)
      encA encNatList :=
    (snd (encInstance I encI) encNatList).comp (fst _ encBits)
  have hIdx := encInstance_index_polyTime I encI h1
  have hP := encInstance_modulus_polyTime I encI h1
  have hOut := encInstance_claimedOutput_polyTime I encI h1
  have hd := F.uniform.depth_polyTime.comp hIdx
  have hkOut := F.uniform.width_polyTime.comp (hIdx.prod hd)
  have hcw := coinBits_pt hP ((challengeCount_pt F).comp hIdx)
  have hval := evalTableMLEMod_pt hP hkOut hOut hr
  have hInit : ComputableInPolyTime
      (fun p : (Instance I × List ℕ) × List Bool =>
        ({ remaining := (F.circuit p.1.1.index).depth,
           point := p.1.2,
           value := evalTableMLEMod p.1.1.modulus
             ((F.circuit p.1.1.index).width (F.circuit p.1.1.index).depth)
             p.1.1.claimedOutput p.1.2,
           ok := true } : LayerState))
      encA encLayerState :=
    encLayerState_mk_polyTime hd hr hval (const true)
  have hStep : IsOraclePPTOn (encPair encA encLayerState) encLayerState
      (fun q => layerExec F q.1.1.1 (coinBits q.1.1.1.modulus
        (challengeCount (F.circuit q.1.1.1.index))) q.2) :=
    (layerExec_ppt F).preprocess
      (((h1.comp (fst encA encLayerState)).prod
          (hcw.comp (fst encA encLayerState))).prod
        (snd encA encLayerState))
  obtain ⟨cD, dD, hD⟩ := F.uniform.depth_polyTime.polyBounded.exists_le
  obtain ⟨cW, dW, hW⟩ := uniform_width_polyBounded F
  let layerSizeFun : ℕ → ℕ := fun n =>
    2 * (cD * (n + 1) ^ dD) +
      2 * ((cW * (n + 1) ^ dW + n) * (2 * (n + 1) + 1)) +
      2 * (n + 1) + 16
  have hLayerSizeFun : PolynomiallyBounded layerSizeFun := by
    dsimp only [layerSizeFun]
    fun_prop
  have hLayerSize : PolyBounded (fun a => (encA a).length)
      (fun a => layerSizeFun (encA a).length) :=
    PolyBounded.of_polynomiallyBounded (fun a => (encA a).length) hLayerSizeFun
  let lInv (a : (Instance I × List ℕ) × List Bool) (_ : ℕ) (st : LayerState) : Prop :=
    st.remaining ≤ (F.circuit a.1.1.index).depth ∧
      st.point.length ≤ (F.circuit a.1.1.index).width st.remaining + a.1.2.length ∧
      (∀ v ∈ st.point, (encNat v).length ≤ (encA a).length + 1) ∧
      (encNat st.value).length ≤ (encA a).length + 1
  have haBounds : ∀ a : (Instance I × List ℕ) × List Bool,
      (encI a.1.1.index).length ≤ (encA a).length ∧
      (encNat a.1.1.modulus).length ≤ (encA a).length ∧
      a.1.2.length ≤ (encA a).length ∧
      (∀ v ∈ a.1.2, (encNat v).length ≤ (encA a).length) := by
    intro a
    have hPair : (encPair (encInstance I encI) encNatList a.1).length ≤ (encA a).length :=
      length_le_encPair_left _ _ a
    have hInst : (encInstance I encI a.1.1).length ≤ (encA a).length :=
      (length_le_encPair_left _ _ a.1).trans hPair
    have hList : (encNatList a.1.2).length ≤ (encA a).length :=
      (length_le_encPair_right _ _ a.1).trans hPair
    refine ⟨(encInstance_index_length_le I encI a.1.1).trans hInst,
      (encInstance_modulus_length_le I encI a.1.1).trans hInst,
      (length_le_length_encList encNat a.1.2).trans hList, fun v hv => ?_⟩
    exact (length_le_encList_of_mem encNat hv).trans hList
  exact (IsOraclePPTOn.iterateWith_spec hd hInit hStep lInv
    (fun a => ⟨le_rfl, Nat.le_add_left _ _,
      fun v hv => ((haBounds a).2.2.2 v hv).trans (Nat.le_succ _), by
        have hMod := (haBounds a).2.1
        have hSz := evalTableMLEMod_size_le (p := a.1.1.modulus)
          (k := (F.circuit a.1.1.index).width (F.circuit a.1.1.index).depth)
          (vals := a.1.1.claimedOutput) (r := a.1.2)
        dsimp only
        exact hSz.trans (by omega)⟩)
    (fun a stepIdx st hstep hst next hnext => by
      simp only [layerExec, OracleComp.mem_supportWith_bind_iff] at hnext
      obtain ⟨sc, -, hline⟩ := hnext
      simp only [lineStepExec, OracleComp.mem_supportWith_bind_iff,
        OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
        ProbOracleComp.support_sample] at hline
      obtain ⟨raw, -, t, -, _, -, rfl⟩ := hline
      have hMod := (haBounds a).2.1
      refine ⟨Nat.le_trans (Nat.sub_le _ _) hst.1, ?_, fun v hv => ?_, ?_⟩
      · rw [length_lineMod]
        exact Nat.le_add_right _ _
      · rcases Nat.eq_zero_or_pos a.1.1.modulus with hp0 | hpos
        · simp only [lineMod, hp0, ↓reduceIte, List.mem_replicate] at hv
          rcases hv with ⟨_, rfl⟩
          have h0 : (encNat 0).length = 0 := rfl
          omega
        · have hvlt := mem_lineMod_lt hpos _ _ _ v hv
          simp only [encNat_apply, Nat.size_eq_bits_len] at hMod ⊢
          exact (Nat.size_le_size hvlt.le).trans (by omega)
      · have hSz := hornerModBin_size_le (p := a.1.1.modulus) (z := t)
          (l := decodeResidues a.1.1.modulus ((F.circuit a.1.1.index).width (st.remaining - 1)) raw)
        dsimp only
        exact hSz.trans (by omega))
    hLayerSize
    (fun a stepIdx st _ hst => by
      obtain ⟨hIdx, hMod, hrLen, _⟩ := haBounds a
      have hdLe : st.remaining ≤ cD * ((encA a).length + 1) ^ dD :=
        hst.1.trans ((hD a.1.1.index).trans (Nat.mul_le_mul_left cD
          (Nat.pow_le_pow_left (by omega) dD)))
      have hwLe : st.point.length ≤ cW * ((encA a).length + 1) ^ dW + (encA a).length := by
        have hW' := hW a.1.1.index st.remaining hst.1
        have hPow : ((encI a.1.1.index).length + 1) ^ dW ≤ ((encA a).length + 1) ^ dW :=
          Nat.pow_le_pow_left (by omega) dW
        have := hW'.trans (Nat.mul_le_mul_left cW hPow)
        omega
      have hptLen : (encNatList st.point).length ≤
          (cW * ((encA a).length + 1) ^ dW + (encA a).length) * (2 * ((encA a).length + 1) + 1) :=
        (length_encNatList_of_forall_size hst.2.2.1).trans
          (Nat.mul_le_mul_right (2 * ((encA a).length + 1) + 1) hwLe)
      have hremLen : (encUnary st.remaining).length ≤ cD * ((encA a).length + 1) ^ dD := by
        simpa [encUnary_apply] using hdLe
      have hvalLen : (encNat st.value).length ≤ (encA a).length + 1 := hst.2.2.2
      dsimp only [layerSizeFun]
      enc_len [encLayerState_apply, encLayerStateFields])).1

/-- A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3; see also
[Thaler, §4.6][Thaler2022] — locator not re-verified against primary PDF): `F.verifier` is realized
by a strict oracle PPT multi-tape Turing machine relative to `encInstance I encI`, running in time
polynomial in `|encI ι| + log p + |input| log p + |claimedOutput| log p` using `F.uniform` for
`depth`/`width` and `F.wiringMLE` for `ãdd_i`/`m̃ult_i`. Compiling arbitrary `IsLogSpaceUniform`
wiring without a supplied `HasPolyTimeWiringMLE` oracle and `poly(S)` prover word-TM runtime remain
open on `#892`. -/
theorem UniformGKRFamily.isOraclePPTOn_verifier {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn (encInstance I encI) encBool F.verifier := by
  unfold UniformGKRFamily.verifier
  have hIdx : ComputableInPolyTime (fun inst : Instance I => inst.index)
      (encInstance I encI) encI := encInstance_index_polyTime I encI id'
  have hP : ComputableInPolyTime (fun inst : Instance I => inst.modulus)
      (encInstance I encI) encNat := encInstance_modulus_polyTime I encI id'
  have hInput : ComputableInPolyTime (fun inst : Instance I => inst.input)
      (encInstance I encI) encNatList := encInstance_input_polyTime I encI id'
  have hM := (challengeCount_pt F).comp hIdx
  have hMin := (minModulus_pt F).comp hIdx
  have hcw := coinBits_pt hP hM
  have hkOut := F.uniform.width_polyTime.comp (hIdx.prod (F.uniform.depth_polyTime.comp hIdx))
  have hkIn := F.uniform.width_polyTime.comp (hIdx.prod (const 0))
  have hCond : ComputableInPolyTime
      (fun inst : Instance I => decide (minModulus (F.circuit inst.index) ≤ inst.modulus))
      (encInstance I encI) encBool :=
    binary_le' (unary_to_binary.comp hMin) hP
  have hSampleVec : IsOraclePPTOn (encInstance I encI) encNatList
      (fun inst => ProbOracleComp.sample
        (OracleComp.replicate ((F.circuit inst.index).width (F.circuit inst.index).depth)
          (sampleModNat (coinBits inst.modulus (challengeCount (F.circuit inst.index)))
            inst.modulus))) :=
    ((isPPTOn_sampleModNat hcw hP).replicate hkOut).isOraclePPTOn (Operation := Unit)
  have hSend : IsOraclePPTOn (encPair (encInstance I encI) encNatList) encBits
      (fun p => List.take 0 <$> ProbOracleComp.query ((), encNatList p.2)) :=
    IsOraclePPTOn.query_take ()
      ((of_eq (f := encNatList) (encIn := encNatList) (encOut := encBits) fun _ => rfl).comp
        (snd (encInstance I encI) encNatList))
      (const 0)
  let encA := encPair (encPair (encInstance I encI) encNatList) encBits
  have hFinal : ComputableInPolyTime
      (fun p : ((Instance I × List ℕ) × List Bool) × LayerState =>
        p.2.ok && decide
          (evalTableMLEMod p.1.1.1.modulus ((F.circuit p.1.1.1.index).width 0)
            p.1.1.1.input p.2.point = p.2.value % p.1.1.1.modulus))
      (encPair encA encLayerState) encBool := by
    let encB := encPair encA encLayerState
    have hpa : ComputableInPolyTime (fun p : ((Instance I × List ℕ) × List Bool) × LayerState =>
        p.1.1.1) encB (encInstance I encI) :=
      (fst (encInstance I encI) encNatList).comp ((fst _ encBits).comp (fst encA encLayerState))
    have hpst : ComputableInPolyTime (fun p : ((Instance I × List ℕ) × List Bool) × LayerState =>
        p.2) encB encLayerState := snd encA encLayerState
    have hmle := evalTableMLEMod_pt (hP.comp hpa) (hkIn.comp hpa) (hInput.comp hpa)
      (encLayerState_point_polyTime hpst)
    have hvalMod := binary_mod' (encLayerState_value_polyTime hpst) (hP.comp hpa)
    exact (encLayerState_ok_polyTime hpst).bool_and' (decide_eq' hmle hvalMod)
  have hTail : IsOraclePPTOn (encPair (encInstance I encI) encNatList) encBool
      (fun a : Instance I × List ℕ => do
        let _ ← List.take 0 <$> ProbOracleComp.query ((), encNatList a.2)
        let init : LayerState :=
          ⟨(F.circuit a.1.index).depth, a.2, evalTableMLEMod a.1.modulus
            ((F.circuit a.1.index).width (F.circuit a.1.index).depth) a.1.claimedOutput a.2, true⟩
        let final ← OracleComp.iterate (F.circuit a.1.index).depth
          (layerExec F a.1 (coinBits a.1.modulus (challengeCount (F.circuit a.1.index)))) init
        return final.ok && decide
          (evalTableMLEMod a.1.modulus ((F.circuit a.1.index).width 0) a.1.input final.point =
            final.value % a.1.modulus)) :=
    hSend.bind_with
      ((verifier_layerLoop_ppt F).bind_with
        (second := fun pair final =>
          (pure (final.ok && decide
            (evalTableMLEMod pair.1.1.modulus ((F.circuit pair.1.1.index).width 0)
              pair.1.1.input final.point = final.value % pair.1.1.modulus)) :
            WordOracleComp Unit Bool))
        (hFinal.isOraclePPTOn (Operation := Unit)))
  have hBody : IsOraclePPTOn (encInstance I encI) encBool
      (fun inst => do
        let r ← ProbOracleComp.sample (OracleComp.replicate
          ((F.circuit inst.index).width (F.circuit inst.index).depth)
          (sampleModNat (coinBits inst.modulus (challengeCount (F.circuit inst.index)))
            inst.modulus))
        let _ ← List.take 0 <$> ProbOracleComp.query ((), encNatList r)
        let init : LayerState :=
          ⟨(F.circuit inst.index).depth, r, evalTableMLEMod inst.modulus
            ((F.circuit inst.index).width (F.circuit inst.index).depth) inst.claimedOutput r, true⟩
        let final ← OracleComp.iterate (F.circuit inst.index).depth
          (layerExec F inst (coinBits inst.modulus (challengeCount (F.circuit inst.index)))) init
        return final.ok && decide
          (evalTableMLEMod inst.modulus ((F.circuit inst.index).width 0) inst.input final.point =
            final.value % inst.modulus)) :=
    hSampleVec.bind_with hTail
  exact IsOraclePPTOn.cond hCond hBody
    (ComputableInPolyTime.isOraclePPTOn (f := fun _ : Instance I => false) (const false))

/-- A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3): there exists a
polynomial-time step schedule `t` and a halting probabilistic multi-tape Turing machine realizing
`F.verifier` on every `Instance I` within `t inst` steps across every stateful prover oracle
(general `IsLogSpaceUniform` wiring compilation without `HasPolyTimeWiringMLE` and `poly(S)` prover
runtime remain open on `#892`). -/
theorem UniformGKRFamily.exists_computesOracleInTimeOn_verifier {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ∃ t : Instance I → ℕ,
      PolyBounded (fun inst => (encInstance I encI inst).length) t ∧
      ComputesOracleInTimeOn (encInstance I encI) encBool t F.verifier :=
  isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn.mp F.isOraclePPTOn_verifier

end Runtime

/-! ### Word-level bridge, exact simulation, soundness, and completeness -/

section Correctness

/-- Decode a truncated bit word into a univariate polynomial over `ZMod p` of degree at most `D`. -/
private noncomputable def decodePoly (p : ℕ) [Fact p.Prime] (D : ℕ) (word : List Bool) :
    Polynomial (ZMod p) :=
  Polynomial.ofCoeffList ((decodeResidues p D word).map Nat.cast)

/-- Encode the coefficients `X^0, …, X^D` of a polynomial over `ZMod p` as fixed-width big-endian
binary residues. -/
private noncomputable def encodePoly (p : ℕ) [Fact p.Prime] (D : ℕ) (g : Polynomial (ZMod p)) :
    List Bool :=
  encodeResidues p ((g.coeffsBelow (D + 1)).map ZMod.val)

/-- Word-level prover codec for univariate polynomials of degree at most `D` over `ZMod p`. -/
private noncomputable def polyProverCodec (p : ℕ) [Fact p.Prime] (D : ℕ) :
    ProverCodec (Polynomial (ZMod p)) :=
  ProverCodec.ofTotal (encodePoly p D) (decodePoly p D) 0 (polyLimit p D)

/-- Challenge codec for single field elements in `ZMod p` represented as binary naturals. -/
private noncomputable def fieldChallengeCodec (p : ℕ) : ChallengeCodec (ZMod p) where
  encode x := encNat x.val
  decode w := (Decoder.nat.decode w : ZMod p)

/-- Challenge codec for output-layer vectors `Fin k → ZMod p` represented as `encNatList`. -/
private noncomputable def vecChallengeCodec (p k : ℕ) : ChallengeCodec (Fin k → ZMod p) where
  encode v := encNatList (List.ofFn fun j => (v j).val)
  decode w := vecOfList p k ((Decoder.list Decoder.nat).decode w)

private theorem fieldChallengeCodec_lawful {p : ℕ} [NeZero p] :
    (fieldChallengeCodec p).Lawful := by
  intro x
  change ((Decoder.nat.decode (encNat x.val) : ℕ) : ZMod p) = x
  rw [Decoder.nat.decode_enc, ZMod.natCast_zmod_val]

private theorem vecChallengeCodec_lawful {p k : ℕ} [NeZero p] :
    (vecChallengeCodec p k).Lawful := by
  intro v
  have hdec : (Decoder.list Decoder.nat).decode
      (encNatList (List.ofFn fun j : Fin k => (v j).val)) =
      List.ofFn (fun j : Fin k => (v j).val) :=
    (Decoder.list Decoder.nat).decode_enc _
  change vecOfList p k ((Decoder.list Decoder.nat).decode
      (encNatList (List.ofFn fun j : Fin k => (v j).val))) = v
  rw [hdec, vecOfList_ofFn]

private theorem natDegree_decodePoly_le {p : ℕ} [Fact p.Prime] (D : ℕ) (word : List Bool) :
    (decodePoly p D word).natDegree ≤ D := by
  have hp : 0 < p := Nat.Prime.pos Fact.out
  refine (Polynomial.natDegree_ofCoeffList_le _).trans ?_
  rw [List.length_map, length_decodeResidues hp]
  omega

private theorem eval_decodePoly {p : ℕ} [Fact p.Prime] (D : ℕ) (word : List Bool) (z : ℕ) :
    (decodePoly p D word).eval (z : ZMod p) =
      ((hornerModBin p z (decodeResidues p D word) : ℕ) : ZMod p) := by
  rw [decodePoly, Polynomial.eval_ofCoeffList, natCast_hornerModBin]

private theorem decodePoly_take_encodePoly {p : ℕ} [Fact p.Prime] {D : ℕ}
    {g : Polynomial (ZMod p)} (hdeg : g.natDegree ≤ D) :
    decodePoly p D ((encodePoly p D g).take (polyLimit p D)) = g := by
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have hl : ∀ a ∈ (g.coeffsBelow (D + 1)).map ZMod.val, a < p := by
    rintro a ha
    rw [List.mem_map] at ha
    obtain ⟨c, _, rfl⟩ := ha
    exact ZMod.val_lt c
  have hlen : ((g.coeffsBelow (D + 1)).map ZMod.val).length ≤ D + 1 := by
    simp
  rw [encodePoly, decodePoly, decodeResidues_encodeResidues hp D hl hlen, List.map_map]
  have hmap : ((List.range (D + 1)).map
      (Nat.cast ∘ fun i => ((g.coeffsBelow (D + 1)).map ZMod.val).getD i 0)) =
      g.coeffsBelow (D + 1) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hi'' : i < D + 1 := by simpa using hi
    simp only [Function.comp_apply, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_map, Polynomial.coeffsBelow,
      List.getElem?_range hi'', Option.map_some, Option.getD_some, ZMod.natCast_zmod_val]
  rw [hmap]
  exact Polynomial.ofCoeffList_coeffsBelow (by omega)

/-- Concatenate round codecs along two sequential protocol specifications. -/
private def roundCodecsAppend :
    (s₁ : Spec) → {s₂ : Spec} → RoundCodecs s₁ → RoundCodecs s₂ → RoundCodecs (s₁ ++ s₂)
  | [], _, (), cs₂ => cs₂
  | .prover _ _ :: s₁, _, (c, cs₁), cs₂ => (c, roundCodecsAppend s₁ cs₁ cs₂)
  | .verifier _ :: s₁, _, (c, cs₁), cs₂ => (c, roundCodecsAppend s₁ cs₁ cs₂)

/-- Word codecs for `k` sumcheck rounds of degree `2` over `ZMod p`. -/
private noncomputable def sumcheckCodecs (p : ℕ) [Fact p.Prime] :
    (k : ℕ) → RoundCodecs (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
  | 0 => ()
  | k + 1 => roundCodecsAppend (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (sumcheckCodecs p k) (polyProverCodec p 2, fieldChallengeCodec p, ())

/-- Challenge samplers for `k` sumcheck rounds drawing from `Nat.cast <$> sampleModNat ℓ p`. -/
private noncomputable def sumcheckSamplersApprox (p ℓ : ℕ) [Fact p.Prime] :
    (k : ℕ) → PerChallenge ProbComp (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
  | 0 => ()
  | k + 1 => PerChallenge.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (Sumcheck.roundSpec (ZMod p))
      (sumcheckSamplersApprox p ℓ k) (Nat.cast <$> sampleModNat ℓ p, ())

/-- Word codecs for layer `i`: `2 * width i` degree-`2` sumcheck rounds plus the degree-`width i`
line step. -/
private noncomputable def layerCodecs (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] (i : ℕ) :
    RoundCodecs (C.layerSpec (F := ZMod p) i) :=
  roundCodecsAppend (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars i))
    (sumcheckCodecs p (C.sumcheckVars i))
    (polyProverCodec p (C.width i), fieldChallengeCodec p, ())

/-- Approximate challenge samplers for layer `i`. -/
private noncomputable def layerSamplersApprox (C : LayeredCircuit) (p ℓ : ℕ) [Fact p.Prime]
    (i : ℕ) : PerChallenge ProbComp (C.layerSpec (F := ZMod p) i) :=
  PerChallenge.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars i))
    (Sumcheck.roundSpec (ZMod p))
    (sumcheckSamplersApprox p ℓ (C.sumcheckVars i))
    (Nat.cast <$> sampleModNat ℓ p, ())

/-- Word codecs for `C.descendSpec m`. -/
private noncomputable def descendCodecs (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] :
    (m : ℕ) → RoundCodecs (C.descendSpec (F := ZMod p) m)
  | 0 => ()
  | m + 1 => roundCodecsAppend (C.layerSpec (F := ZMod p) m)
      (layerCodecs C p m) (descendCodecs C p m)

/-- Approximate challenge samplers for `C.descendSpec m`. -/
private noncomputable def descendSamplersApprox (C : LayeredCircuit) (p ℓ : ℕ) [Fact p.Prime] :
    (m : ℕ) → PerChallenge ProbComp (C.descendSpec (F := ZMod p) m)
  | 0 => ()
  | m + 1 => PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
      (layerSamplersApprox C p ℓ m) (descendSamplersApprox C p ℓ m)

/-- Word codecs for the full GKR protocol `C.outputSpec ++ C.descendSpec C.depth`. -/
private noncomputable def gkrCodecs (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] :
    RoundCodecs (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth) :=
  roundCodecsAppend (C.outputSpec (F := ZMod p))
    (vecChallengeCodec p (C.width C.depth), ()) (descendCodecs C p C.depth)

/-- Approximate challenge samplers for the full GKR protocol. -/
private noncomputable def gkrSamplers (C : LayeredCircuit) (p ℓ : ℕ) [Fact p.Prime] :
    PerChallenge ProbComp (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth) :=
  PerChallenge.append (C.outputSpec (F := ZMod p)) (C.descendSpec (F := ZMod p) C.depth)
    (OracleComp.replicateFin (C.width C.depth) (Nat.cast <$> sampleModNat ℓ p), ())
    (descendSamplersApprox C p ℓ C.depth)

private theorem runWordRounds_append :
    ∀ (s₁ : Spec) {s₂ : Spec} (c₁ : RoundCodecs s₁) (c₂ : RoundCodecs s₂)
      (smp₁ : PerChallenge ProbComp s₁) (smp₂ : PerChallenge ProbComp s₂),
      runWordRounds (s₁ ++ s₂) (roundCodecsAppend s₁ c₁ c₂)
          (PerChallenge.append s₁ s₂ smp₁ smp₂) =
        runWordRounds s₁ c₁ smp₁ >>= fun (ok₁, τ₁) =>
          (fun (ok₂, τ₂) => (ok₁ && ok₂, Transcript.append s₁ s₂ τ₁ τ₂)) <$>
            runWordRounds s₂ c₂ smp₂
  | [], _, (), _, (), _ => by
      simp [runWordRounds, roundCodecsAppend, PerChallenge.append, Transcript.append]
  | .prover _ _ :: s₁, _, (c, c₁), c₂, smp₁, smp₂ => by
      simp only [List.cons_append, runWordRounds, roundCodecsAppend, PerChallenge.append,
        bind_assoc]
      congr 1 with raw : 1
      rw [runWordRounds_append s₁ c₁ c₂ smp₁ smp₂]
      simp [map_bind, bind_map_left, Functor.map_map, Transcript.append, Bool.and_assoc]
  | .verifier _ :: s₁, _, (c, c₁), c₂, (smp, smp₁), smp₂ => by
      simp only [List.cons_append, runWordRounds, roundCodecsAppend, PerChallenge.append,
        bind_assoc]
      congr 1 with ch : 1
      congr 1 with _ : 1
      rw [runWordRounds_append s₁ c₁ c₂ smp₁ smp₂]
      simp [map_bind, bind_map_left, Functor.map_map, Transcript.append]

/-- Stateful execution of an interactive verifier passing an optional intermediate statement. -/
private noncomputable def runWordState {s : Spec} {S₁ S₂ : Type}
    (V : Verifier OracleSpec.empty s S₁ S₂) (codecs : RoundCodecs s)
    (smp : PerChallenge ProbComp s) (x? : Option S₁) : WordOracleComp Unit (Option S₂) :=
  (fun out : Bool × Transcript s => if out.1 then x?.bind (V.outputOn · out.2) else none) <$>
    runWordRounds s codecs smp

private theorem wordVerifierWith_eq_runWordState {s : Spec} {S₁ S₂ : Type}
    (V : Verifier OracleSpec.empty s S₁ S₂) (codecs : RoundCodecs s)
    (smp : PerChallenge ProbComp s) (x : S₁) :
    V.wordVerifierWith codecs smp x =
      Option.isSome <$> runWordState V codecs smp (some x) := by
  simp only [Verifier.wordVerifierWith, runWordState, Functor.map_map]
  congr 1 with ⟨ok, τ⟩ : 1
  cases ok <;> simp

private theorem runWordState_append {s₁ s₂ : Spec} {S₁ S₂ S₃ : Type}
    (V₁ : Verifier OracleSpec.empty s₁ S₁ S₂) (V₂ : Verifier OracleSpec.empty s₂ S₂ S₃)
    (c₁ : RoundCodecs s₁) (c₂ : RoundCodecs s₂)
    (smp₁ : PerChallenge ProbComp s₁) (smp₂ : PerChallenge ProbComp s₂)
    (x? : Option S₁) :
    runWordState (V₁.append V₂) (roundCodecsAppend s₁ c₁ c₂)
        (PerChallenge.append s₁ s₂ smp₁ smp₂) x? =
      runWordState V₁ c₁ smp₁ x? >>= runWordState V₂ c₂ smp₂ := by
  simp only [runWordState, runWordRounds_append, map_bind, bind_map_left, Functor.map_map]
  congr 1 with ⟨ok₁, τ₁⟩ : 1
  congr 1 with ⟨ok₂, τ₂⟩ : 1
  cases ok₁ <;> cases ok₂ <;> simp [outputOn_append, Transcript.split_append, Option.bind_assoc]

private theorem runWordState_bundle {s : Spec} {Θ : Type} {S₁ S₂ : Θ → Type}
    (smpFull : PerChallenge ProbComp s)
    (V : (θ : Θ) → Verifier OracleSpec.empty s (S₁ θ) (S₂ θ))
    (codecs : RoundCodecs s) (smp : PerChallenge ProbComp s) (θ : Θ) (x? : Option (S₁ θ)) :
    runWordState (Verifier.bundle smpFull V) codecs smp (x?.map (Sigma.mk θ)) =
      (Option.map (Sigma.mk θ)) <$> runWordState (V θ) codecs smp x? := by
  simp only [runWordState, Functor.map_map]
  congr 1 with ⟨ok, τ⟩ : 1
  cases ok <;> cases x? <;> simp [Verifier.outputOn_bundle]

private def SumcheckState.toClaim? (p j : ℕ) (sc : SumcheckState) :
    Option (Sumcheck.Claim (ZMod p) j) :=
  if sc.ok then some ⟨vecOfList p j sc.challenges, (sc.claim : ZMod p)⟩ else none

private def LayerState.toClaim? (C : LayeredCircuit) (p m : ℕ) (st : LayerState) :
    Option (LayerClaim C (ZMod p) m) :=
  if st.ok then some (.ofPoint (vecOfList p (C.width m) st.point) (st.value : ZMod p)) else none

private theorem runWith_map_bind_eq {α β γ₁ γ₂ δ State : Type}
    (respond : Unit × List Bool → StateT State PMF (List Bool))
    (p₁ : WordOracleComp Unit α) (p₂ : WordOracleComp Unit β) (proj : α → β)
    (k₁ : α → WordOracleComp Unit γ₁) (k₂ : β → WordOracleComp Unit γ₂)
    (out₁ : γ₁ → δ) (out₂ : γ₂ → δ) (s : State)
    (hp : (ProbOracleComp.runWith respond p₁ s).map (Prod.map proj id) =
      ProbOracleComp.runWith respond p₂ s)
    (hk : ∀ a ∈ OracleComp.support p₁, ∀ s',
      (ProbOracleComp.runWith respond (k₁ a) s').map (Prod.map out₁ id) =
        (ProbOracleComp.runWith respond (k₂ (proj a)) s').map (Prod.map out₂ id)) :
    (ProbOracleComp.runWith respond (p₁ >>= k₁) s).map (Prod.map out₁ id) =
      (ProbOracleComp.runWith respond (p₂ >>= k₂) s).map (Prod.map out₂ id) := by
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind, PMF.map_bind, PMF.map_bind]
  have hleft :
      ((ProbOracleComp.runWith respond p₁ s).bind fun x =>
          PMF.map (Prod.map out₁ id) (ProbOracleComp.runWith respond (k₁ x.1) x.2)) =
        (ProbOracleComp.runWith respond p₁ s).bind fun x =>
          PMF.map (Prod.map out₂ id) (ProbOracleComp.runWith respond (k₂ (proj x.1)) x.2) := by
    refine Probability.PMF.bind_congr_on_support _ _ _ fun x hx => ?_
    exact hk x.1 (ProbOracleComp.mem_support_of_mem respond hx) x.2
  rw [hleft, ← hp, PMF.bind_map]
  rfl

private theorem vecOfList_append_singleton {p j : ℕ} {xs : List ℕ}
    (hlen : xs.length = j) (r : ℕ) :
    vecOfList p (j + 1) (xs ++ [r]) = Fin.snoc (vecOfList p j xs) (r : ZMod p) := by
  funext k
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp [vecOfList, List.getD_eq_getElem?_getD, hlen]
  · simp only [vecOfList, Fin.snoc_castSucc, Fin.val_castSucc, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show (k' : ℕ) < xs.length by omega)]

private theorem vecOfList_take_castAdd {p k : ℕ} (xs : List ℕ) :
    vecOfList p k (xs.take k) = vecOfList p (k + k) xs ∘ Fin.castAdd k := by
  funext j
  simp [vecOfList, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt]

private theorem vecOfList_drop_natAdd {p k : ℕ} (xs : List ℕ) :
    vecOfList p k ((xs.drop k).take k) = vecOfList p (k + k) xs ∘ Fin.natAdd k := by
  funext j
  simp [vecOfList, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt,
    List.getElem?_drop, Nat.add_comm]

private theorem sumcheck_round_outputOn {p n j : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (x : Sumcheck.Claim (ZMod p) j)
    (τ : Transcript (Sumcheck.roundSpec (ZMod p))) :
    (Sumcheck.round 2 P j).verifier.outputOn x τ =
      if Sumcheck.accepts 2 x.value τ.1 then some ⟨Fin.snoc x.challenges τ.2.1, τ.1.eval τ.2.1⟩
      else none :=
  rfl

private theorem reduction_id_outputOn {S W : Type} (x : S) :
    (Reduction.id (oP := OracleSpec.empty) (oV := OracleSpec.empty) (S := S)
      (W := W)).verifier.outputOn x () = some x :=
  rfl

private theorem lineStep_outputOn' (C : LayeredCircuit) {p : ℕ} [Fact p.Prime]
    (i : ℕ) (W : (Fin (C.width i) → Bool) → ZMod p)
    (x : SumcheckEnd C (ZMod p) i) (τ : Transcript (Sumcheck.roundSpec (ZMod p))) :
    (C.lineStep i W).verifier.outputOn x τ =
      if C.lineAccepts i x τ.1 then some (C.lineClaim i x τ.1 τ.2.1) else none :=
  rfl

private theorem inputStep_outputOn (C : LayeredCircuit) {p : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p) (y : LayerClaim C (ZMod p) 0) :
    (C.inputStep x).verifier.outputOn y () =
      if eval y.point (multilinearExtension x) = y.value then some () else none :=
  rfl

private theorem val_natCast_of_mem_sampleModNat {p cw t : ℕ} (hp : 0 < p)
    (ht : t ∈ (ProbComp.eval (sampleModNat cw p)).support) : ((t : ZMod p)).val = t := by
  rw [sampleModNat, ProbComp.eval_map, PMF.mem_support_map_iff] at ht
  obtain ⟨x, _, rfl⟩ := ht
  exact ZMod.val_natCast_of_lt (Nat.mod_lt _ hp)

private theorem runWith_sumcheckStep_eq {p coinWidth n j : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (sc : SumcheckState) (hlen : sc.challenges.length = j)
    {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool)) (s : State) :
    (ProbOracleComp.runWith respond (sumcheckStep p coinWidth sc) s).map
        (Prod.map (SumcheckState.toClaim? p (j + 1)) id) =
      ProbOracleComp.runWith respond
        (runWordState (Sumcheck.round 2 P j).verifier
          (polyProverCodec p 2, fieldChallengeCodec p, ())
          (Nat.cast <$> sampleModNat coinWidth p, ())
          (sc.toClaim? p j)) s := by
  have hp : 0 < p := Nat.Prime.pos Fact.out
  simp only [sumcheckStep, runWordState, runWordRounds, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_sample,
    ProbComp.eval_map, PMF.map_bind, PMF.bind_map, ProbOracleComp.runWith_pure,
    Function.comp_def, Prod.map]
  congr 1 with ⟨raw, s₁⟩ : 1
  simp only [fieldChallengeCodec]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun r hr => ?_
  rw [val_natCast_of_mem_sampleModNat hp hr]
  congr 1 with ⟨_, s₂⟩ : 1
  simp only [PMF.pure_map, Prod.map, id_eq]
  congr 2
  simp only [polyProverCodec, ProverCodec.ofTotal, ProverCodec.decodeOrDefault,
    Option.isSome_some, Option.getD_some, Bool.true_and, SumcheckState.toClaim?]
  by_cases hok : sc.ok
  · simp only [hok, ↓reduceIte, Option.bind_some]
    rw [sumcheck_round_outputOn]
    have hdeg : (decodePoly p 2 (raw.take (polyLimit p 2))).natDegree ≤ 2 :=
      natDegree_decodePoly_le 2 _
    have heval01 :
        ((decodePoly p 2 (raw.take (polyLimit p 2))).eval 0 +
          (decodePoly p 2 (raw.take (polyLimit p 2))).eval 1 = (sc.claim : ZMod p)) ↔
        (hornerModBin p 0 (decodeResidues p 2 (raw.take (polyLimit p 2))) +
          hornerModBin p 1 (decodeResidues p 2 (raw.take (polyLimit p 2)))) % p =
          sc.claim % p := by
      rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) by simp,
        show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp,
        eval_decodePoly, eval_decodePoly, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
    by_cases hstep : (hornerModBin p 0 (decodeResidues p 2 (raw.take (polyLimit p 2))) +
        hornerModBin p 1 (decodeResidues p 2 (raw.take (polyLimit p 2)))) % p = sc.claim % p
    · have ha : Sumcheck.accepts 2 (sc.claim : ZMod p)
          (decodePoly p 2 (raw.take (polyLimit p 2))) := ⟨hdeg, heval01.mpr hstep⟩
      simp only [hstep, decide_true, Bool.true_and, ↓reduceIte]
      rw [ite_eq_left ha]
      simp [vecOfList_append_singleton hlen r, (eval_decodePoly 2 _ r).symm]
    · have ha : ¬ Sumcheck.accepts 2 (sc.claim : ZMod p)
          (decodePoly p 2 (raw.take (polyLimit p 2))) := fun h => hstep (heval01.mp h.2)
      simp only [hstep, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right ha]
  · simp [hok]

private theorem runWith_sumcheck_iterate {p coinWidth n : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (sc₀ : SumcheckState) (h0 : sc₀.challenges = []) :
    ∀ (k : ℕ) {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool))
      (s : State),
      (ProbOracleComp.runWith respond (OracleComp.iterate k (sumcheckStep p coinWidth) sc₀) s).map
          (Prod.map (SumcheckState.toClaim? p k) id) =
        ProbOracleComp.runWith respond
          (runWordState
            (Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
              (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit) (Sumcheck.round 2 P) k).verifier
            (sumcheckCodecs p k) (sumcheckSamplersApprox p coinWidth k)
            (sc₀.toClaim? p 0)) s
  | 0, State, respond, s => by
      simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure, PMF.pure_map, Prod.map,
        id_eq, Reduction.iterate, iterSpec, sumcheckCodecs, sumcheckSamplersApprox,
        runWordState, runWordRounds, ProbOracleComp.runWith_map]
      have hel : vecOfList p 0 sc₀.challenges = Fin.elim0 := funext fun j => j.elim0
      by_cases hok : sc₀.ok
      · simp [SumcheckState.toClaim?, reduction_id_outputOn, hok, hel]
      · simp [SumcheckState.toClaim?, hok]
  | k + 1, State, respond, s => by
      rw [OracleComp.iterate_succ]
      change (ProbOracleComp.runWith respond
        (OracleComp.iterate k (sumcheckStep p coinWidth) sc₀ >>= sumcheckStep p coinWidth) s).map
        (Prod.map (SumcheckState.toClaim? p (k + 1)) id) = _
      have hlen :
          ∀ sc ∈ OracleComp.support (OracleComp.iterate k (sumcheckStep p coinWidth) sc₀),
            sc.challenges.length = k := by
        intro sc hsc
        refine OracleComp.iterate_invariant (fun j x => x.challenges.length = j)
          (by simp [h0]) (fun j st _ hj next hnext => ?_) sc hsc
        simp only [sumcheckStep, OracleComp.mem_supportWith_bind_iff,
          OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
          ProbOracleComp.support_sample] at hnext
        obtain ⟨raw, -, r, -, _, -, rfl⟩ := hnext
        simp [hj]
      have hV :
          (Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
            (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
            (Sumcheck.round 2 P) (k + 1)).verifier =
          (Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
            (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
            (Sumcheck.round 2 P) k).verifier.append (Sumcheck.round 2 P k).verifier := rfl
      rw [hV, sumcheckCodecs, sumcheckSamplersApprox]
      change _ = ProbOracleComp.runWith respond
        (runWordState
          ((Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
            (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
            (Sumcheck.round 2 P) k).verifier.append (Sumcheck.round 2 P k).verifier)
          (roundCodecsAppend (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
            (sumcheckCodecs p k) (polyProverCodec p 2, fieldChallengeCodec p, ()))
          (PerChallenge.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
            (Sumcheck.roundSpec (ZMod p)) (sumcheckSamplersApprox p coinWidth k)
            (Nat.cast <$> sampleModNat coinWidth p, ()))
          (sc₀.toClaim? p 0)) s
      rw [runWordState_append]
      simpa only [Prod.map_id, PMF.map_id] using
        runWith_map_bind_eq respond
          (OracleComp.iterate k (sumcheckStep p coinWidth) sc₀)
          (runWordState
            (Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
              (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
              (Sumcheck.round 2 P) k).verifier
            (sumcheckCodecs p k) (sumcheckSamplersApprox p coinWidth k)
            (sc₀.toClaim? p 0))
          (SumcheckState.toClaim? p k)
          (fun sc => sumcheckStep p coinWidth sc)
          (runWordState (Sumcheck.round 2 P k).verifier
            (polyProverCodec p 2, fieldChallengeCodec p, ())
            (Nat.cast <$> sampleModNat coinWidth p, ()))
          (SumcheckState.toClaim? p (k + 1)) id s
          (runWith_sumcheck_iterate P sc₀ h0 k respond s)
          fun sc hsc s' => by
            simpa only [PMF.map_id, Prod.map_id] using
              runWith_sumcheckStep_eq P sc (hlen sc hsc) respond s'

private theorem runWith_lineStep_eq {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) [Fact inst.modulus.Prime]
    (coinWidth i : ℕ) (hi : i < (F.circuit inst.index).depth)
    (W : (Fin ((F.circuit inst.index).width i) → Bool) → ZMod inst.modulus)
    (st : LayerState) (hrem : st.remaining = i + 1) (sc : SumcheckState)
    (_ : sc.challenges.length = (F.circuit inst.index).sumcheckVars i)
    {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool)) (s : State) :
    (ProbOracleComp.runWith respond (lineStepExec F inst coinWidth st sc) s).map
        (Prod.map (LayerState.toClaim? (F.circuit inst.index) inst.modulus i) id) =
      ProbOracleComp.runWith respond
        (runWordState ((F.circuit inst.index).lineStep i W).verifier
          (polyProverCodec inst.modulus ((F.circuit inst.index).width i),
            fieldChallengeCodec inst.modulus, ())
          (Nat.cast <$> sampleModNat coinWidth inst.modulus, ())
          ((sc.toClaim? inst.modulus ((F.circuit inst.index).sumcheckVars i)).map
            (fun c : Sumcheck.Claim (ZMod inst.modulus) ((F.circuit inst.index).sumcheckVars i) =>
              (⟨vecOfList inst.modulus ((F.circuit inst.index).width (i + 1)) st.point, c⟩ :
                SumcheckEnd (F.circuit inst.index) (ZMod inst.modulus) i))))
        s := by
  let C := F.circuit inst.index
  let p := inst.modulus
  have hp : 0 < p := Nat.Prime.pos Fact.out
  change (ProbOracleComp.runWith respond (lineStepExec F inst coinWidth st sc) s).map
      (Prod.map (LayerState.toClaim? C p i) id) = _
  simp only [lineStepExec, hrem, Nat.add_sub_cancel, runWordState, runWordRounds,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_sample, ProbComp.eval_map, PMF.map_bind, PMF.bind_map,
    ProbOracleComp.runWith_pure, Function.comp_def, Prod.map]
  congr 1 with ⟨raw, s₁⟩ : 1
  simp only [fieldChallengeCodec]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun t ht => ?_
  rw [val_natCast_of_mem_sampleModNat hp ht]
  congr 1 with ⟨_, s₂⟩ : 1
  simp only [PMF.pure_map, Prod.map, id_eq]
  congr 2
  simp only [polyProverCodec, ProverCodec.ofTotal, ProverCodec.decodeOrDefault,
    Option.isSome_some, Option.getD_some, Bool.true_and, SumcheckState.toClaim?]
  by_cases hok : sc.ok
  · simp only [hok, ↓reduceIte, Option.map_some, Option.bind_some]
    rw [lineStep_outputOn']
    let y := sc.challenges.take (C.width i)
    let w := (sc.challenges.drop (C.width i)).take (C.width i)
    let rs := decodeResidues p (C.width i) (raw.take (polyLimit p (C.width i)))
    let q : Polynomial (ZMod p) := decodePoly p (C.width i) (raw.take (polyLimit p (C.width i)))
    let xEnd : SumcheckEnd C (ZMod p) i :=
      ⟨vecOfList p (C.width (i + 1)) st.point,
        ⟨vecOfList p (C.sumcheckVars i) sc.challenges, (sc.claim : ZMod p)⟩⟩
    have hy : xEnd.left = vecOfList p (C.width i) y := (vecOfList_take_castAdd sc.challenges).symm
    have hw : xEnd.right = vecOfList p (C.width i) w := (vecOfList_drop_natAdd sc.challenges).symm
    have hwire : ∀ g : Gate,
        ((F.evalWiring ⟨inst.index, g, i, p, st.point, y, w⟩ : ℕ) : ZMod p) =
          eval (Sum.elim xEnd.point (Sum.elim xEnd.left xEnd.right))
            (multilinearExtension (C.wiringPred (R := ZMod p) g i)) := by
      intro g
      rw [hy, hw]
      exact F.wiringMLE.eval_eq inst.index p g i hi st.point y w
    have hq0 : q.eval 0 = ((hornerModBin p 0 rs : ℕ) : ZMod p) := by
      rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) by simp]
      exact eval_decodePoly (C.width i) _ 0
    have hq1 : q.eval 1 = ((hornerModBin p 1 rs : ℕ) : ZMod p) := by
      rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp]
      exact eval_decodePoly (C.width i) _ 1
    have hdeg : q.natDegree ≤ C.width i := natDegree_decodePoly_le (C.width i) _
    let rhs := (F.evalWiring ⟨inst.index, .add, i, p, st.point, y, w⟩ *
        ((hornerModBin p 0 rs + hornerModBin p 1 rs) % p) +
      F.evalWiring ⟨inst.index, .mul, i, p, st.point, y, w⟩ *
        ((hornerModBin p 0 rs * hornerModBin p 1 rs) % p)) % p
    have hcomb :
        ((sc.claim : ZMod p) = C.combine i xEnd.point xEnd.left xEnd.right (q.eval 0) (q.eval 1)) ↔
          sc.claim % p = rhs := by
      have hrhsCast : (rhs : ZMod p) =
          C.combine i xEnd.point xEnd.left xEnd.right (q.eval 0) (q.eval 1) := by
        simp only [rhs, LayeredCircuit.combine, hwire .add, hwire .mul, hq0, hq1,
          ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
      rw [← hrhsCast, ZMod.natCast_eq_natCast_iff']
      simp [rhs]
    by_cases hline : sc.claim % p = rhs
    · have ha : C.lineAccepts i xEnd q := ⟨hdeg, hcomb.mpr hline⟩
      rw [ite_eq_left ha]
      simp only [LayerState.toClaim?, Bool.true_and]
      change (if decide (sc.claim % p = rhs) = true then
          some (LayerClaim.ofPoint (vecOfList p (C.width i) (lineMod p (C.width i) y w t))
            ((hornerModBin p t rs : ℕ) : ZMod p))
        else none) = some (C.lineClaim i xEnd q (t : ZMod p))
      simp only [hline, decide_true, ↓reduceIte, LayeredCircuit.lineClaim]
      rw [vecOfList_lineMod, ← hy, ← hw, ← eval_decodePoly (C.width i) _ t]
    · have ha : ¬ C.lineAccepts i xEnd q := fun h => hline (hcomb.mp h.2)
      rw [ite_eq_right ha]
      simp only [LayerState.toClaim?, Bool.true_and]
      change (if decide (sc.claim % p = rhs) = true then
          some (LayerClaim.ofPoint (vecOfList p (C.width i) (lineMod p (C.width i) y w t))
            ((hornerModBin p t rs : ℕ) : ZMod p))
        else none) = none
      simp only [hline, decide_false, Bool.false_eq_true, ↓reduceIte]
  · simp [hok, LayerState.toClaim?]

private theorem runWith_layerExec_eq {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) [Fact inst.modulus.Prime]
    (coinWidth i : ℕ) (hi : i < (F.circuit inst.index).depth)
    (x : (Fin ((F.circuit inst.index).width 0) → Bool) → ZMod inst.modulus)
    (st : LayerState) (hrem : st.remaining = i + 1)
    {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool)) (s : State) :
    (ProbOracleComp.runWith respond (layerExec F inst coinWidth st) s).map
        (Prod.map (LayerState.toClaim? (F.circuit inst.index) inst.modulus i) id) =
      ProbOracleComp.runWith respond
        (runWordState ((F.circuit inst.index).layer x i).verifier
          (layerCodecs (F.circuit inst.index) inst.modulus i)
          (layerSamplersApprox (F.circuit inst.index) inst.modulus coinWidth i)
          (st.toClaim? (F.circuit inst.index) inst.modulus (i + 1))) s := by
  let C := F.circuit inst.index
  let p := inst.modulus
  let W := C.value x i
  let z := vecOfList p (C.width (i + 1)) st.point
  let sc₀ : SumcheckState := ⟨[], st.value, st.ok⟩
  have hLayerDef :
      (C.layer x i).verifier =
        (C.sumcheckStage i W).verifier.append (C.lineStep i W).verifier := rfl
  change (ProbOracleComp.runWith respond (layerExec F inst coinWidth st) s).map
      (Prod.map (LayerState.toClaim? C p i) id) =
    ProbOracleComp.runWith respond
      (runWordState (C.layer x i).verifier (layerCodecs C p i) (layerSamplersApprox C p coinWidth i)
        (st.toClaim? C p (i + 1))) s
  rw [hLayerDef, layerCodecs, layerSamplersApprox, runWordState_append]
  have hExec : layerExec F inst coinWidth st =
      OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀ >>=
        lineStepExec F inst coinWidth st := by
    simp only [layerExec, hrem, Nat.add_sub_cancel, two_mul, LayeredCircuit.sumcheckVars]
    rfl
  rw [hExec]
  have hStart : st.toClaim? C p (i + 1) = (sc₀.toClaim? p 0).map (Sigma.mk z) := by
    have hel : Fin.elim0 = vecOfList p 0 [] := funext fun j => j.elim0
    by_cases hok : st.ok <;> simp [LayerState.toClaim?, SumcheckState.toClaim?, sc₀, hok, z, hel]
  have hStage :
      (ProbOracleComp.runWith respond
          (OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀) s).map
          (Prod.map
            (fun sc => (sc.toClaim? p (C.sumcheckVars i)).map
              (fun c : Sumcheck.Claim (ZMod p) (C.sumcheckVars i) =>
                (⟨z, c⟩ : SumcheckEnd C (ZMod p) i)))
            id) =
        ProbOracleComp.runWith respond
          (runWordState (C.sumcheckStage i W).verifier
            (sumcheckCodecs p (C.sumcheckVars i))
            (sumcheckSamplersApprox p coinWidth (C.sumcheckVars i))
            (st.toClaim? C p (i + 1))) s := by
    have hV :
        (C.sumcheckStage i W).verifier =
          Verifier.bundle (LayeredCircuit.sumcheckSamplers (F := ZMod p) (C.sumcheckVars i))
            fun z' => (Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
              (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
              (Sumcheck.round 2 (C.summand i W z')) (C.sumcheckVars i)).verifier := rfl
    rw [hStart, hV, runWordState_bundle, ProbOracleComp.runWith_map]
    have hIter :
        (ProbOracleComp.runWith respond
            (OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀) s).map
            (Prod.map (SumcheckState.toClaim? p (C.sumcheckVars i)) id) =
          ProbOracleComp.runWith respond
            (runWordState
              (Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
                (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
                (Sumcheck.round 2 (C.summand i W z)) (C.sumcheckVars i)).verifier
              (sumcheckCodecs p (C.sumcheckVars i))
              (sumcheckSamplersApprox p coinWidth (C.sumcheckVars i))
              (sc₀.toClaim? p 0)) s :=
      runWith_sumcheck_iterate (coinWidth := coinWidth) (C.summand i W z) sc₀ rfl
        (C.sumcheckVars i) respond s
    rw [← hIter, PMF.map_comp]
    congr 1
  have hlen :
      ∀ sc ∈ OracleComp.support
          (OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀),
        sc.challenges.length = C.sumcheckVars i := by
    intro sc hsc
    refine OracleComp.iterate_invariant (fun j x => x.challenges.length = j) rfl
      (fun j _ _ hj next hnext => ?_) sc hsc
    simp only [sumcheckStep, OracleComp.mem_supportWith_bind_iff,
      OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
      ProbOracleComp.support_sample] at hnext
    obtain ⟨raw, -, r, -, _, -, rfl⟩ := hnext
    simp [hj]
  simpa only [Prod.map_id, PMF.map_id] using
    runWith_map_bind_eq respond
      (OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀)
      (runWordState (C.sumcheckStage i W).verifier
        (sumcheckCodecs p (C.sumcheckVars i))
        (sumcheckSamplersApprox p coinWidth (C.sumcheckVars i))
        (st.toClaim? C p (i + 1)))
      (fun sc => (sc.toClaim? p (C.sumcheckVars i)).map
        (fun c : Sumcheck.Claim (ZMod p) (C.sumcheckVars i) =>
          (⟨z, c⟩ : SumcheckEnd C (ZMod p) i)))
      (lineStepExec F inst coinWidth st)
      (runWordState (C.lineStep i W).verifier
        (polyProverCodec p (C.width i), fieldChallengeCodec p, ())
        (Nat.cast <$> sampleModNat coinWidth p, ()))
      (LayerState.toClaim? C p i) id s hStage
      fun sc hsc s' => by
        simpa only [PMF.map_id, Prod.map_id] using
          runWith_lineStep_eq F inst coinWidth i hi W st hrem sc (hlen sc hsc) respond s'

private noncomputable def LayerState.toInput? {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) [Fact inst.modulus.Prime]
    (x : (Fin ((F.circuit inst.index).width 0) → Bool) → ZMod inst.modulus)
    (st : LayerState) : Option Unit :=
  (st.toClaim? (F.circuit inst.index) inst.modulus 0).bind
    fun y => ((F.circuit inst.index).inputStep x).verifier.outputOn y ()

private theorem runWith_descend_eq {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) [Fact inst.modulus.Prime]
    (coinWidth : ℕ)
    (x : (Fin ((F.circuit inst.index).width 0) → Bool) → ZMod inst.modulus) :
    ∀ (m : ℕ), m ≤ (F.circuit inst.index).depth →
      ∀ (st : LayerState), st.remaining = m →
      ∀ {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool)) (s : State),
      (ProbOracleComp.runWith respond (OracleComp.iterate m (layerExec F inst coinWidth) st) s).map
          (Prod.map (LayerState.toInput? F inst x) id) =
        ProbOracleComp.runWith respond
          (runWordState ((F.circuit inst.index).descend x m).verifier
            (descendCodecs (F.circuit inst.index) inst.modulus m)
            (descendSamplersApprox (F.circuit inst.index) inst.modulus coinWidth m)
            (st.toClaim? (F.circuit inst.index) inst.modulus m)) s
  | 0, _, st, _, State, respond, s => by
      simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure, PMF.pure_map, Prod.map,
        id_eq, LayeredCircuit.descend, LayeredCircuit.descendSpec, descendCodecs,
        descendSamplersApprox, runWordState, runWordRounds, ProbOracleComp.runWith_map,
        LayerState.toInput?, ↓reduceIte]
  | m + 1, hm, st, hrem, State, respond, s => by
      rw [OracleComp.iterate_succ_bind]
      have hV :
          ((F.circuit inst.index).descend x (m + 1)).verifier =
            ((F.circuit inst.index).layer x m).verifier.append
              ((F.circuit inst.index).descend x m).verifier := rfl
      rw [hV, descendCodecs, descendSamplersApprox]
      change _ = ProbOracleComp.runWith respond
        (runWordState
          (((F.circuit inst.index).layer x m).verifier.append
            ((F.circuit inst.index).descend x m).verifier)
          (roundCodecsAppend ((F.circuit inst.index).layerSpec (F := ZMod inst.modulus) m)
            (layerCodecs (F.circuit inst.index) inst.modulus m)
            (descendCodecs (F.circuit inst.index) inst.modulus m))
          (PerChallenge.append ((F.circuit inst.index).layerSpec (F := ZMod inst.modulus) m)
            ((F.circuit inst.index).descendSpec (F := ZMod inst.modulus) m)
            (layerSamplersApprox (F.circuit inst.index) inst.modulus coinWidth m)
            (descendSamplersApprox (F.circuit inst.index) inst.modulus coinWidth m))
          (st.toClaim? (F.circuit inst.index) inst.modulus (m + 1))) s
      rw [runWordState_append]
      have hNextRem : ∀ next ∈ OracleComp.support (layerExec F inst coinWidth st),
          next.remaining = m := by
        intro next hnext
        simp only [layerExec, OracleComp.mem_supportWith_bind_iff] at hnext
        obtain ⟨sc, -, hline⟩ := hnext
        simp only [lineStepExec, OracleComp.mem_supportWith_bind_iff,
          OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
          ProbOracleComp.support_sample] at hline
        obtain ⟨raw, -, t, -, _, -, rfl⟩ := hline
        dsimp only
        omega
      simpa only [Prod.map_id, PMF.map_id] using
        runWith_map_bind_eq respond
          (layerExec F inst coinWidth st)
          (runWordState ((F.circuit inst.index).layer x m).verifier
            (layerCodecs (F.circuit inst.index) inst.modulus m)
            (layerSamplersApprox (F.circuit inst.index) inst.modulus coinWidth m)
            (st.toClaim? (F.circuit inst.index) inst.modulus (m + 1)))
          (LayerState.toClaim? (F.circuit inst.index) inst.modulus m)
          (OracleComp.iterate m (layerExec F inst coinWidth))
          (runWordState ((F.circuit inst.index).descend x m).verifier
            (descendCodecs (F.circuit inst.index) inst.modulus m)
            (descendSamplersApprox (F.circuit inst.index) inst.modulus coinWidth m))
          (LayerState.toInput? F inst x) id s
          (runWith_layerExec_eq F inst coinWidth m (by omega) x st hrem respond s)
          fun next hnext s' => by
            simpa only [Prod.map_id, PMF.map_id] using
              runWith_descend_eq F inst coinWidth x m (by omega) next
                (hNextRem next hnext) respond s'

private theorem runWith_verifier_eq_wordVerifierWith {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) [Fact inst.modulus.Prime]
    (hmin : minModulus (F.circuit inst.index) ≤ inst.modulus)
    {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool)) (s : State) :
    ProbOracleComp.runWith respond (F.verifier inst) s =
      ProbOracleComp.runWith respond
        (((F.circuit inst.index).protocol (tableFn inst.modulus
            ((F.circuit inst.index).width 0) inst.input)).verifier.wordVerifierWith
          (gkrCodecs (F.circuit inst.index) inst.modulus)
          (gkrSamplers (F.circuit inst.index) inst.modulus
            (coinBits inst.modulus (challengeCount (F.circuit inst.index))))
          (tableFn inst.modulus ((F.circuit inst.index).width (F.circuit inst.index).depth)
            inst.claimedOutput))
        s := by
  let C := F.circuit inst.index
  let p := inst.modulus
  let cw := coinBits p (challengeCount C)
  let x := tableFn p (C.width 0) inst.input
  let D := tableFn p (C.width C.depth) inst.claimedOutput
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have hProtoV :
      (C.protocol x).verifier =
        (C.outputStep (F := ZMod p)).verifier.append (C.descend x C.depth).verifier := rfl
  rw [wordVerifierWith_eq_runWordState, hProtoV, gkrCodecs, gkrSamplers, runWordState_append,
    ProbOracleComp.runWith_map]
  have hVerDef : F.verifier inst = (do
      let r ← ProbOracleComp.sample
        (OracleComp.replicate (C.width C.depth) (sampleModNat cw p))
      let _ ← List.take 0 <$> ProbOracleComp.query ((), encNatList r)
      let init : LayerState :=
        ⟨C.depth, r, evalTableMLEMod p (C.width C.depth) inst.claimedOutput r, true⟩
      let final ← OracleComp.iterate C.depth (layerExec F inst cw) init
      return final.ok && decide
        (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) := by
    simp [UniformGKRFamily.verifier, hmin, C, p, cw]
  let prefixL : WordOracleComp Unit LayerState := do
    let r ← ProbOracleComp.sample (OracleComp.replicate (C.width C.depth) (sampleModNat cw p))
    let _ ← List.take 0 <$> ProbOracleComp.query ((), encNatList r)
    pure ⟨C.depth, r, evalTableMLEMod p (C.width C.depth) inst.claimedOutput r, true⟩
  have hLHS : F.verifier inst =
      prefixL >>= fun init =>
        (fun final : LayerState => final.ok && decide
          (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) <$>
          OracleComp.iterate C.depth (layerExec F inst cw) init := by
    rw [hVerDef]
    simp only [prefixL, bind_assoc, map_eq_pure_bind, pure_bind]
  rw [hLHS]
  have hPrefixEq :
      (ProbOracleComp.runWith respond prefixL s).map
          (Prod.map (LayerState.toClaim? C p C.depth) id) =
        ProbOracleComp.runWith respond
          (runWordState (C.outputStep (F := ZMod p)).verifier
            (vecChallengeCodec p (C.width C.depth), ())
            (OracleComp.replicateFin (C.width C.depth) (Nat.cast <$> sampleModNat cw p), ())
            (some D)) s := by
    dsimp only [prefixL]
    rw [← OracleComp.map_ofFn_replicateFin]
    simp only [runWordState, runWordRounds, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, PMF.map_bind, PMF.bind_map, ProbComp.eval_map,
      ProbComp.eval_replicateFin_map_coords, Function.comp_def, Prod.map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun u hu => ?_
    have huLt : ∀ j : Fin (C.width C.depth), u j < p := fun j => by
      have hj := (ProbComp.mem_support_replicateFin_iff _ _ _).mp hu j
      rw [sampleModNat, ProbComp.eval_map, PMF.mem_support_map_iff] at hj
      obtain ⟨y, _, hy⟩ := hj
      rw [← hy]
      exact Nat.mod_lt _ hp
    have henc :
        (vecChallengeCodec p (C.width C.depth)).encode (fun j => (u j : ZMod p)) =
          encNatList (List.ofFn u) := by
      simp only [vecChallengeCodec]
      congr 1
      refine List.ext_getElem (by simp) fun j hj _ => ?_
      have hj' : j < C.width C.depth := by simpa using hj
      simp only [List.getElem_ofFn, ZMod.val_natCast_of_lt (huLt ⟨j, hj'⟩)]
    rw [henc]
    congr 1 with ⟨_, s₁⟩ : 1
    simp only [PMF.pure_map, Prod.map, id_eq]
    congr 1
    simp only [LayerState.toClaim?, ↓reduceIte, Option.bind_some,
      LayeredCircuit.outputStep_outputOn, LayerClaim.ofPoint]
    have hvec : vecOfList p (C.width C.depth) (List.ofFn u) = fun j => (u j : ZMod p) := by
      funext j
      simp [vecOfList, List.getD_eq_getElem?_getD]
    rw [hvec]
    simp [D, natCast_evalTableMLEMod, hvec]
  have hPrefixRem : ∀ init ∈ OracleComp.support prefixL, init.remaining = C.depth := by
    intro init hinit
    simp only [prefixL, OracleComp.mem_supportWith_bind_iff,
      OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
      ProbOracleComp.support_sample] at hinit
    obtain ⟨r, -, _, -, _, -, rfl⟩ := hinit
    rfl
  have hOutEq : ∀ final : LayerState,
      (final.ok &&
        decide (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) =
        (LayerState.toInput? F inst x final).isSome := by
    intro final
    have hLlt : evalTableMLEMod p (C.width 0) inst.input final.point < p :=
      evalTableMLEMod_lt hp _ _ _
    by_cases hok : final.ok
    · have hEqIff :
          (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p) ↔
            eval (vecOfList p (C.width 0) final.point) (multilinearExtension x) =
              (final.value : ZMod p) := by
        rw [← natCast_evalTableMLEMod]
        constructor
        · intro h
          rw [h, ZMod.natCast_mod]
        · intro h
          have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
          simpa only [Nat.ModEq, Nat.mod_eq_of_lt hLlt, Nat.mod_mod] using hmod
      dsimp only [C, p] at hEqIff
      by_cases hcmp : evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p
      · simp only [LayerState.toInput?, LayerState.toClaim?, hok, ↓reduceIte, Option.bind_some,
          inputStep_outputOn, LayerClaim.ofPoint, LayerClaim.point, LayerClaim.value,
          hEqIff.mp hcmp, Option.isSome_some, hcmp, decide_true, Bool.true_and]
      · simp only [LayerState.toInput?, LayerState.toClaim?, hok, ↓reduceIte, Option.bind_some,
          inputStep_outputOn, LayerClaim.ofPoint, LayerClaim.point, LayerClaim.value,
          mt hEqIff.mpr hcmp, Option.isSome_none, hcmp, decide_false, Bool.and_false]
    · simp [LayerState.toInput?, LayerState.toClaim?, hok]
  have hEq := runWith_map_bind_eq respond prefixL
    (runWordState (C.outputStep (F := ZMod p)).verifier
      (vecChallengeCodec p (C.width C.depth), ())
      (OracleComp.replicateFin (C.width C.depth) (Nat.cast <$> sampleModNat cw p), ())
      (some D))
    (LayerState.toClaim? C p C.depth)
    (fun init => (fun final : LayerState => final.ok && decide
      (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) <$>
      OracleComp.iterate C.depth (layerExec F inst cw) init)
    (fun y? => runWordState (C.descend x C.depth).verifier
      (descendCodecs C p C.depth) (descendSamplersApprox C p cw C.depth) y?)
    id Option.isSome s hPrefixEq
    fun init hinit s' => by
      have hDesc := runWith_descend_eq F inst cw x C.depth le_rfl init (hPrefixRem init hinit)
        respond s'
      have hMap := congrArg (PMF.map (Prod.map Option.isSome id)) hDesc
      simpa only [Prod.map_id, PMF.map_id, ProbOracleComp.runWith_map, PMF.map_comp,
        Function.comp_def, Prod.map, id_eq, hOutEq] using hMap
  simpa only [PMF.map_id, Prod.map_id, ProbOracleComp.runWith_map] using hEq

/-! ### Statistical closeness, soundness, completeness, and `IP` membership -/

private theorem coinBits_spec (p M : ℕ) : M * p ^ 2 ≤ 2 ^ coinBits p M := by
  have hp : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by decide) p
  have hM : M + 1 < 2 ^ (Nat.log 2 (M + 1) + 1) := Nat.lt_pow_succ_log_self (by decide) (M + 1)
  have hp2 : p ^ 2 ≤ 2 ^ (2 * (Nat.log 2 p + 1)) := by
    calc p ^ 2 = p * p := by ring
      _ ≤ 2 ^ (Nat.log 2 p + 1) * 2 ^ (Nat.log 2 p + 1) := Nat.mul_le_mul hp.le hp.le
      _ = 2 ^ (2 * (Nat.log 2 p + 1)) := by rw [← Nat.pow_add, two_mul]
  calc M * p ^ 2
      ≤ 2 ^ (Nat.log 2 (M + 1) + 1) * 2 ^ (2 * (Nat.log 2 p + 1)) :=
        Nat.mul_le_mul (by omega) hp2
    _ = 2 ^ coinBits p M := by
        rw [mul_comm, ← Nat.pow_add]
        rfl

private theorem mul_div_coinBits_le {p M : ℕ} (hp : 0 < p) :
    (M : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / 2 ^ coinBits p M) ≤ 1 / (p : ℝ≥0∞) := by
  have hreal : (M : ℝ) * ((p : ℝ) / 2 ^ coinBits p M) ≤ 1 / (p : ℝ) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hpowR : (0 : ℝ) < (2 : ℝ) ^ coinBits p M := by positivity
    rw [← mul_div_assoc, div_le_div_iff₀ hpowR hpR]
    have hbound : (M : ℝ) * (p : ℝ) * (p : ℝ) ≤ (2 : ℝ) ^ coinBits p M := by
      have hN := coinBits_spec p M
      exact_mod_cast (show M * p * p ≤ 2 ^ coinBits p M by simpa [pow_two, mul_assoc] using hN)
    linarith
  have hENN := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_div_of_pos (by exact_mod_cast hp),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast] at hENN
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast]
  exact hENN

private theorem closeTo_replicateFin_sampleModNat {p cw : ℕ} [NeZero p] :
    ∀ k : ℕ, Probability.CloseTo
      (ProbComp.eval (ProbComp.uniform (Fin k → ZMod p)))
      (ProbComp.eval (OracleComp.replicateFin k (Nat.cast <$> sampleModNat cw p)))
      ((k : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / 2 ^ cw))
  | 0 => by
      have h1 : ProbComp.eval (ProbComp.uniform (Fin 0 → ZMod p)) = PMF.pure Fin.elim0 := by
        rw [ProbComp.eval_uniform]
        ext f
        have hf : f = Fin.elim0 := funext fun i => i.elim0
        subst hf
        simp
      rw [h1, OracleComp.replicateFin_zero, ProbComp.eval_pure]
      simp
  | k + 1 => by
      have h1 : ProbComp.eval (ProbComp.uniform (Fin (k + 1) → ZMod p)) =
          ProbComp.eval (OracleComp.replicateFin (k + 1) (ProbComp.uniform (ZMod p))) := by
        rw [OracleComp.replicateFin_eq_pi, ProbComp.eval_pi_uniform, ProbComp.eval_uniform]
      rw [h1, OracleComp.replicateFin_succ, OracleComp.replicateFin_succ, ProbComp.eval_bind,
        ProbComp.eval_bind]
      have hSingle :
          Probability.CloseTo (ProbComp.eval (ProbComp.uniform (ZMod p)))
            (ProbComp.eval (Nat.cast <$> sampleModNat cw p))
            (ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) := by
        rw [ProbComp.eval_uniform, ProbComp.eval_map]
        exact (closeTo_of_dist_le_ofReal (ProbComp.dist_map_natCast_eval_sampleModNat_le cw p)).symm
      have hRest := closeTo_replicateFin_sampleModNat (p := p) (cw := cw) k
      have hCont :
          ∀ ch ∈ (ProbComp.eval ((Nat.cast : ℕ → ZMod p) <$> sampleModNat cw p)).support,
            Probability.CloseTo
              (ProbComp.eval (Fin.cons (α := fun _ => ZMod p) ch <$>
                OracleComp.replicateFin k (ProbComp.uniform (ZMod p))))
              (ProbComp.eval
                (Fin.cons (α := fun _ => ZMod p) ch <$>
                  OracleComp.replicateFin k ((Nat.cast : ℕ → ZMod p) <$> sampleModNat cw p)))
              ((k : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) := by
        intro ch _
        rw [ProbComp.eval_map, ProbComp.eval_map, OracleComp.replicateFin_eq_pi,
          ProbComp.eval_pi_uniform, ← ProbComp.eval_uniform (Fin k → ZMod p)]
        exact hRest.map (Fin.cons (α := fun _ : Fin (k + 1) => ZMod p) ch)
      have hBind := hSingle.bind hCont
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hBind

private noncomputable def sumcheckCloseErrors (p : ℕ) [Fact p.Prime] (ε : ℝ≥0∞) :
    (k : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
  | 0 => ()
  | k + 1 => PerChallenge.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (Sumcheck.roundSpec (ZMod p)) (sumcheckCloseErrors p ε k) (ε, ())

private noncomputable def layerCloseErrors (C : LayeredCircuit) (p : ℕ) [Fact p.Prime]
    (ε : ℝ≥0∞) (i : ℕ) : PerChallenge (fun _ => ℝ≥0∞) (C.layerSpec (F := ZMod p) i) :=
  PerChallenge.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars i))
    (Sumcheck.roundSpec (ZMod p)) (sumcheckCloseErrors p ε (C.sumcheckVars i)) (ε, ())

private noncomputable def descendCloseErrors (C : LayeredCircuit) (p : ℕ) [Fact p.Prime]
    (ε : ℝ≥0∞) : (m : ℕ) → PerChallenge (fun _ => ℝ≥0∞) (C.descendSpec (F := ZMod p) m)
  | 0 => ()
  | m + 1 => PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
      (layerCloseErrors C p ε m) (descendCloseErrors C p ε m)

private noncomputable def gkrCloseErrors (C : LayeredCircuit) (p cw : ℕ) [Fact p.Prime] :
    PerChallenge (fun _ => ℝ≥0∞)
      (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth) :=
  let ε : ℝ≥0∞ := ENNReal.ofReal ((p : ℝ) / 2 ^ cw)
  PerChallenge.append (C.outputSpec (F := ZMod p)) (C.descendSpec (F := ZMod p) C.depth)
    ((C.width C.depth : ℝ≥0∞) * ε, ()) (descendCloseErrors C p ε C.depth)

private theorem sum_sumcheckCloseErrors {p : ℕ} [Fact p.Prime] (ε : ℝ≥0∞) :
    ∀ k, PerChallenge.sum (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
        (sumcheckCloseErrors p ε k) = (k : ℝ≥0∞) * ε
  | 0 => by simp [sumcheckCloseErrors, iterSpec, PerChallenge.sum]
  | k + 1 => by
      change PerChallenge.sum (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k ++
          Sumcheck.roundSpec (ZMod p))
        (PerChallenge.append _ _ (sumcheckCloseErrors p ε k) (ε, ())) = _
      rw [PerChallenge.sum_append, sum_sumcheckCloseErrors ε k]
      simp [PerChallenge.sum, add_mul, Nat.cast_add]

private theorem sum_descendCloseErrors {C : LayeredCircuit} {p : ℕ} [Fact p.Prime] (ε : ℝ≥0∞) :
    ∀ m, PerChallenge.sum (C.descendSpec (F := ZMod p) m)
        (descendCloseErrors C p ε m) =
      ((∑ i ∈ Finset.range m, (2 * C.width i + 1) : ℕ) : ℝ≥0∞) * ε
  | 0 => by simp [descendCloseErrors, LayeredCircuit.descendSpec, PerChallenge.sum]
  | m + 1 => by
      change PerChallenge.sum (C.layerSpec (F := ZMod p) m ++ C.descendSpec (F := ZMod p) m)
        (PerChallenge.append _ _ (layerCloseErrors C p ε m)
          (descendCloseErrors C p ε m)) = _
      rw [PerChallenge.sum_append, layerCloseErrors, PerChallenge.sum_append,
        sum_sumcheckCloseErrors ε (C.sumcheckVars m), sum_descendCloseErrors ε m,
        Finset.sum_range_succ, Nat.cast_add, add_mul]
      simp only [PerChallenge.sum, add_zero]
      push_cast
      ring

private theorem sum_gkrCloseErrors_le (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] :
    PerChallenge.sum (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
        (gkrCloseErrors C p (coinBits p (challengeCount C))) ≤ 1 / (p : ℝ≥0∞) := by
  have hp : 0 < p := Nat.Prime.pos Fact.out
  change PerChallenge.sum (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
    (PerChallenge.append (C.outputSpec (F := ZMod p)) (C.descendSpec (F := ZMod p) C.depth)
      _ (descendCloseErrors C p _ C.depth)) ≤ _
  rw [PerChallenge.sum_append, sum_descendCloseErrors]
  simp only [PerChallenge.sum, add_zero]
  rw [← add_mul, ← Nat.cast_add, ← challengeCount_eq_finset]
  exact mul_div_coinBits_le hp

private theorem closeTo_perChallenge_append {s₁ s₂ : Spec}
    {smp₁ smp₁' : PerChallenge ProbComp s₁} {smp₂ smp₂' : PerChallenge ProbComp s₂}
    {δ₁ : PerChallenge (fun _ => ℝ≥0∞) s₁} {δ₂ : PerChallenge (fun _ => ℝ≥0∞) s₂}
    (h1 : PerChallenge.CloseTo s₁ smp₁ smp₁' δ₁)
    (h2 : PerChallenge.CloseTo s₂ smp₂ smp₂' δ₂) :
    PerChallenge.CloseTo (s₁ ++ s₂)
      (PerChallenge.append s₁ s₂ smp₁ smp₂)
      (PerChallenge.append s₁ s₂ smp₁' smp₂')
      (PerChallenge.append s₁ s₂ δ₁ δ₂) := by
  induction s₁ with
  | nil => exact h2
  | cons r s₁ ih =>
    cases r with
    | prover _ _ => exact ih h1
    | verifier _ => exact ⟨h1.1, ih h1.2⟩

private theorem closeTo_sumcheckSamplers {p cw : ℕ} [Fact p.Prime] :
    ∀ k, PerChallenge.CloseTo (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (LayeredCircuit.sumcheckSamplers (F := ZMod p) k)
      (sumcheckSamplersApprox p cw k)
      (sumcheckCloseErrors p (ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) k)
  | 0 => trivial
  | k + 1 => by
      refine closeTo_perChallenge_append (closeTo_sumcheckSamplers k) ⟨?_, trivial⟩
      rw [ProbComp.eval_uniform, ProbComp.eval_map]
      exact (closeTo_of_dist_le_ofReal (ProbComp.dist_map_natCast_eval_sampleModNat_le cw p)).symm

private theorem closeTo_descendSamplers (C : LayeredCircuit) {p cw : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p) :
    ∀ m, PerChallenge.CloseTo (C.descendSpec (F := ZMod p) m)
      (C.descend x m).verifier.samplers
      (descendSamplersApprox C p cw m)
      (descendCloseErrors C p (ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) m)
  | 0 => trivial
  | m + 1 => by
      change PerChallenge.CloseTo (C.layerSpec (F := ZMod p) m ++ C.descendSpec (F := ZMod p) m)
        (PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
          (C.layer x m).verifier.samplers (C.descend x m).verifier.samplers)
        (PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
          (layerSamplersApprox C p cw m) (descendSamplersApprox C p cw m))
        (PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
          (layerCloseErrors C p _ m) (descendCloseErrors C p _ m))
      refine closeTo_perChallenge_append ?_ (closeTo_descendSamplers C x m)
      change PerChallenge.CloseTo
        (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars m) ++
          Sumcheck.roundSpec (ZMod p))
        (PerChallenge.append _ _ (LayeredCircuit.sumcheckSamplers (C.sumcheckVars m))
          (ProbComp.uniform (ZMod p), ()))
        (PerChallenge.append _ _ (sumcheckSamplersApprox p cw (C.sumcheckVars m))
          (Nat.cast <$> sampleModNat cw p, ()))
        (PerChallenge.append _ _ (sumcheckCloseErrors p _ (C.sumcheckVars m))
          (ENNReal.ofReal ((p : ℝ) / 2 ^ cw), ()))
      refine closeTo_perChallenge_append (closeTo_sumcheckSamplers (C.sumcheckVars m)) ⟨?_, trivial⟩
      rw [ProbComp.eval_uniform, ProbComp.eval_map]
      exact (closeTo_of_dist_le_ofReal (ProbComp.dist_map_natCast_eval_sampleModNat_le cw p)).symm

private theorem closeTo_gkrSamplers (C : LayeredCircuit) {p cw : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p) :
    PerChallenge.CloseTo (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
      (C.protocol x).verifier.samplers
      (gkrSamplers C p cw)
      (gkrCloseErrors C p cw) := by
  change PerChallenge.CloseTo (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
    (PerChallenge.append (C.outputSpec (F := ZMod p)) (C.descendSpec (F := ZMod p) C.depth)
      (ProbComp.uniform _, ()) (C.descend x C.depth).verifier.samplers)
    (gkrSamplers C p cw) (gkrCloseErrors C p cw)
  refine closeTo_perChallenge_append ⟨?_, trivial⟩ (closeTo_descendSamplers C x C.depth)
  exact closeTo_replicateFin_sampleModNat (C.width C.depth)

/-- A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3; see also
[Thaler, §4.6][Thaler2022] — locator not re-verified against primary PDF): whenever `inst.modulus`
is prime and the claimed output disagrees with `C.output` on the input table, every stateful
randomized word prover `P : Cslib.Complexity.Prover Unit` is accepted by `F.verifier inst` with
probability at most `(1 + width depth + ∑ i < depth, 5 * width i) / inst.modulus` (general
`IsLogSpaceUniform` wiring compilation without `HasPolyTimeWiringMLE` and `poly(S)` prover runtime
remain open on `#892`). -/
theorem UniformGKRFamily.acceptProb_verifier_sound {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) (hp : Nat.Prime inst.modulus)
    (hbad : ¬ inst.CorrectOutput F) (P : Cslib.Complexity.Prover Unit) :
    Complexity.acceptProb (F.verifier inst) P ≤
      (layerCost (F.circuit inst.index) : ℝ≥0∞) / inst.modulus := by
  let C := F.circuit inst.index
  let p := inst.modulus
  by_cases hmin : minModulus C ≤ p
  · have : Fact p.Prime := ⟨hp⟩
    let cw := coinBits p (challengeCount C)
    let x := tableFn p (C.width 0) inst.input
    let D := tableFn p (C.width C.depth) inst.claimedOutput
    have hD : D ∉ ({C.output x} : Set ((Fin (C.width C.depth) → Bool) → ZMod p)) := by
      simpa [Instance.CorrectOutput, C, p, x, D] using hbad
    have hSim : Complexity.acceptProb (F.verifier inst) P =
        Complexity.acceptProb
          ((C.protocol x).verifier.wordVerifierWith (gkrCodecs C p) (gkrSamplers C p cw) D) P := by
      simp only [Complexity.acceptProb, Complexity.Prover.run_eq_runWith,
        runWith_verifier_eq_wordVerifierWith F inst hmin]
      rfl
    rw [hSim]
    have hSound :
        Complexity.acceptProb ((C.protocol x).verifier.wordVerifier (gkrCodecs C p) D) P ≤
          ((C.width C.depth + ∑ i ∈ Finset.range C.depth, 5 * C.width i : ℕ) : ℝ≥0∞) /
            Fintype.card (ZMod p) :=
      (C.protocol_sound (F := ZMod p) x).acceptProb_wordVerifier (gkrCodecs C p) hD P
    have hTV := (C.protocol x).verifier.acceptProb_wordVerifierWith_le_wordVerifier_add
      (gkrCodecs C p) (closeTo_gkrSamplers C (cw := cw) x) D P
    refine hTV.trans (add_le_add hSound (sum_gkrCloseErrors_le C p) |>.trans ?_)
    rw [ZMod.card p, ← ENNReal.add_div, add_comm, ← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add,
      ← Nat.add_assoc, ← layerCost_eq_finset]
  · have hzero : Complexity.acceptProb (F.verifier inst) P = 0 := by
      refine Complexity.acceptProb_eq_zero P fun r hr => ?_
      have hfalse : F.verifier inst = pure false := by simp [UniformGKRFamily.verifier, hmin, C, p]
      rw [hfalse, Complexity.Prover.run_pure, PMF.mem_support_pure_iff] at hr
      simp [hr]
    rw [hzero]
    exact zero_le

private def ChallengeCodecsLawful : {s : Spec} → RoundCodecs s → Prop
  | [], () => True
  | .prover _ _ :: _, (_, cs) => ChallengeCodecsLawful cs
  | .verifier _ :: _, (c, cs) => c.Lawful ∧ ChallengeCodecsLawful cs

private theorem challengeCodecsLawful_append :
    ∀ {s₁ s₂ : Spec} {c₁ : RoundCodecs s₁} {c₂ : RoundCodecs s₂},
      ChallengeCodecsLawful c₁ → ChallengeCodecsLawful c₂ →
      ChallengeCodecsLawful (roundCodecsAppend s₁ c₁ c₂)
  | [], _, (), _, _, h2 => h2
  | .prover _ _ :: s₁, _, (_, _), _, h1, h2 => challengeCodecsLawful_append (s₁ := s₁) h1 h2
  | .verifier _ :: s₁, _, (_, _), _, ⟨hc, h1⟩, h2 =>
      ⟨hc, challengeCodecsLawful_append (s₁ := s₁) h1 h2⟩

private theorem challengeCodecsLawful_sumcheck (p : ℕ) [Fact p.Prime] :
    ∀ k, ChallengeCodecsLawful (sumcheckCodecs p k)
  | 0 => trivial
  | k + 1 => challengeCodecsLawful_append (challengeCodecsLawful_sumcheck p k)
      ⟨fieldChallengeCodec_lawful, trivial⟩

private theorem challengeCodecsLawful_descend (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] :
    ∀ m, ChallengeCodecsLawful (descendCodecs C p m)
  | 0 => trivial
  | m + 1 => challengeCodecsLawful_append
      (challengeCodecsLawful_append (challengeCodecsLawful_sumcheck p (C.sumcheckVars m))
        ⟨fieldChallengeCodec_lawful, trivial⟩)
      (challengeCodecsLawful_descend C p m)

private theorem challengeCodecsLawful_gkrCodecs (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] :
    ChallengeCodecsLawful (gkrCodecs C p) :=
  challengeCodecsLawful_append ⟨vecChallengeCodec_lawful, trivial⟩
    (challengeCodecsLawful_descend C p C.depth)

private def ValidStrat {α : Type} (Q : α → Prop) :
    (s : Spec) → RoundCodecs s → ProverStrategy (ProbOracleComp OracleSpec.empty) s α → Prop
  | [], _, a => Q a
  | .prover _ _ :: s, (c, cs), st =>
      ∀ m st', (m, st') ∈ OracleComp.support st →
        c.decode ((c.encode m).take c.limit) = some m ∧ ValidStrat Q s cs st'
  | .verifier C :: s, (_, cs), st =>
      ∀ ch : C, ∀ st' ∈ OracleComp.support (st ch), ValidStrat Q s cs st'

private theorem validStrat_append {α β : Type} {Q : α → Prop} {R : β → Prop} :
    ∀ (s₁ : Spec) {s₂ : Spec} (c₁ : RoundCodecs s₁) (c₂ : RoundCodecs s₂)
      (st₁ : ProverStrategy (ProbOracleComp OracleSpec.empty) s₁ α)
      (next : α → ProbOracleComp OracleSpec.empty
        (ProverStrategy (ProbOracleComp OracleSpec.empty) s₂ β)),
      ValidStrat Q s₁ c₁ st₁ →
      (∀ a, Q a → ∀ st₂ ∈ OracleComp.support (next a), ValidStrat R s₂ c₂ st₂) →
      ∀ st ∈ OracleComp.support (ProverStrategy.append s₁ s₂ st₁ next),
        ValidStrat R (s₁ ++ s₂) (roundCodecsAppend s₁ c₁ c₂) st
  | [], _, (), _, a, next, h1, h2, st, hst => h2 a h1 st hst
  | .prover _ _ :: s₁, s₂, (c, cs₁), c₂, st₁, next, h1, h2, st, hst => by
      simp only [ProverStrategy.append, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hst
      subst hst
      intro m rest hm
      simp only [OracleComp.mem_supportWith_bind_iff, OracleComp.supportWith_pure,
        Set.mem_singleton_iff] at hm
      obtain ⟨⟨m', st₁'⟩, hst1, rest', hrest', hEq⟩ := hm
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      obtain ⟨hdec, hvalid1⟩ := h1 m st₁' hst1
      exact ⟨hdec, validStrat_append s₁ cs₁ c₂ st₁' next hvalid1 h2 rest hrest'⟩
  | .verifier _ :: s₁, s₂, (_, cs₁), c₂, st₁, next, h1, h2, st, hst => by
      simp only [ProverStrategy.append, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hst
      subst hst
      intro ch rest hrest
      simp only [OracleComp.mem_supportWith_bind_iff] at hrest
      obtain ⟨st₁', hst1, hrest'⟩ := hrest
      exact validStrat_append s₁ cs₁ c₂ st₁' next (h1 ch st₁' hst1) h2 rest hrest'

private theorem validStrat_bindLeaf {α β : Type} {Q : α → Prop} :
    ∀ (s : Spec) (c : RoundCodecs s)
      (st : ProverStrategy (ProbOracleComp OracleSpec.empty) s α)
      (f : Transcript s → α → ProbOracleComp OracleSpec.empty β),
      ValidStrat Q s c st →
      ∀ st' ∈ OracleComp.support (ProverStrategy.bindLeaf s st f),
        ValidStrat (fun _ => True) s c st'
  | [], (), _, _, _, _, _ => trivial
  | .prover _ _ :: s, (c, cs), st, f, h, st', hst' => by
      simp only [ProverStrategy.bindLeaf, OracleComp.supportWith_pure,
        Set.mem_singleton_iff] at hst'
      subst hst'
      intro m rest hm
      simp only [OracleComp.mem_supportWith_bind_iff, OracleComp.supportWith_pure,
        Set.mem_singleton_iff] at hm
      obtain ⟨⟨m', st₁⟩, hst1, rest', hrest', hEq⟩ := hm
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      obtain ⟨hdec, hv⟩ := h m st₁ hst1
      exact ⟨hdec, validStrat_bindLeaf s cs st₁ _ hv rest hrest'⟩
  | .verifier _ :: s, (_, cs), st, f, h, st', hst' => by
      simp only [ProverStrategy.bindLeaf, OracleComp.supportWith_pure,
        Set.mem_singleton_iff] at hst'
      subst hst'
      intro ch rest hrest
      simp only [OracleComp.mem_supportWith_bind_iff] at hrest
      obtain ⟨st₁, hst1, hrest'⟩ := hrest
      exact validStrat_bindLeaf s cs st₁ _ (h ch st₁ hst1) rest hrest'

private theorem mem_support_of_mem_plainLaw {α : Type} {p : ProbOracleComp OracleSpec.empty α}
    {a : α} (ha : a ∈ (plainLaw p).support) : a ∈ OracleComp.support p := by
  have hsub : (plainLaw p).support ⊆ OracleComp.support p := by
    rw [plainLaw, ← OracleComp.evalWith_eq_interpret, OracleComp.support_evalWith]
    exact OracleComp.supportWith_mono (fun _ => Set.subset_univ _) p
  exact hsub ha

private theorem runWith_honestWordState_runWordRounds_embed_of_valid {α : Type} (Q : α → Prop) :
    ∀ (s : Spec) (codecs : RoundCodecs s), ChallengeCodecsLawful codecs →
      ∀ (smp : PerChallenge ProbComp s)
        (P : ProbOracleComp OracleSpec.empty
          (ProverStrategy (ProbOracleComp OracleSpec.empty) s α))
        {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool))
        (embed : HonestWordState α s → State),
        (∀ q st, respond q (embed st) =
          (HonestWordState.respond s codecs q st).map (Prod.map id embed)) →
        (∀ st ∈ OracleComp.support P, ValidStrat Q s codecs st) →
        (ProbOracleComp.runWith respond (runWordRounds s codecs smp)
            (embed (HonestWordState.init s P))).map Prod.fst =
          (plainLaw (P >>= runStrategy s smp)).map (fun r => (true, r.1))
  | [], (), _, (), P, _, _, _, _, _ => by
      simp [runWordRounds, runStrategy, PMF.map, Function.comp_def]
  | .prover _ _ :: s, (c, cs), hChal, smp, P, State, respond, embed, hemb, hValid => by
      have hemb' : ∀ q st, respond q (embed (.inr st)) =
          (HonestWordState.respond s cs q st).map (Prod.map id (embed ∘ Sum.inr)) := by
        intro q st
        rw [hemb q (.inr st), HonestWordState.respond, PMF.map_comp]
        rfl
      rw [runWordRounds, HonestWordState.init, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hemb]
      simp only [HonestWordState.respond, PMF.bind_map, PMF.map_bind,
        ProbOracleComp.runWith_map, PMF.map_comp, Function.comp_def, Prod.map, id_eq]
      have hleft :
          ((plainLaw (P >>= id)).bind fun x : _ × _ =>
            PMF.map
              (fun a : (Bool × Transcript s) × State =>
                ((c.decode ((c.encode x.1).take c.limit)).isSome && a.1.1,
                  (c.decodeOrDefault ((c.encode x.1).take c.limit), a.1.2)))
              (ProbOracleComp.runWith respond (runWordRounds s cs smp)
                (embed (.inr (HonestWordState.init s (pure x.2)))))) =
          (plainLaw (P >>= id)).bind fun x =>
            PMF.map (fun r : Transcript s × α => (true, (x.1, r.1)))
              (plainLaw (pure x.2 >>= runStrategy s smp)) := by
        refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨m, next⟩ hmx => ?_
        have hSupp := mem_support_of_mem_plainLaw hmx
        simp only [OracleComp.mem_supportWith_bind_iff, id_eq] at hSupp
        obtain ⟨st, hst, hm⟩ := hSupp
        obtain ⟨hdec, hcont⟩ := hValid st hst m next hm
        have ih := runWith_honestWordState_runWordRounds_embed_of_valid Q s cs hChal smp (pure next)
          respond (embed ∘ Sum.inr) hemb'
          (fun st' hst' => OracleComp.eq_of_mem_supportWith_pure hst' ▸ hcont)
        have hmap := congrArg (PMF.map fun p : Bool × Transcript s =>
          ((c.decode ((c.encode m).take c.limit)).isSome && p.1,
            (c.decodeOrDefault ((c.encode m).take c.limit), p.2))) ih
        simpa [PMF.map_comp, Function.comp_def, hdec, ProverCodec.decodeOrDefault] using hmap
      rw [hleft]
      simp only [runStrategy, plainLaw_bind, id_eq, PMF.bind_bind,
        plainLaw_pure, PMF.pure_bind, PMF.map, Function.comp_def]
  | .verifier _ :: s, (c, cs), ⟨hc, hcs⟩, (smp, smps), P, State, respond, embed, hemb, hValid => by
      have hemb' : ∀ q st, respond q (embed (.inr st)) =
          (HonestWordState.respond s cs q st).map (Prod.map id (embed ∘ Sum.inr)) := by
        intro q st
        rw [hemb q (.inr st), HonestWordState.respond, PMF.map_comp]
        rfl
      rw [runWordRounds, HonestWordState.init, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_sample]
      simp only [PMF.bind_map, PMF.map_bind, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hemb,
        HonestWordState.respond, Pure.pure, PMF.pure_map, PMF.pure_bind,
        PMF.map_comp, Function.comp_def, Prod.map, id_eq]
      have hleft :
          ((ProbComp.eval smp).bind fun ch =>
            PMF.map (fun a : (Bool × Transcript s) × State => (a.1.1, (ch, a.1.2)))
              (ProbOracleComp.runWith respond (runWordRounds s cs smps)
                (embed (.inr (HonestWordState.init s
                  (P >>= fun k => k (c.decode (c.encode ch)))))))) =
          (ProbComp.eval smp).bind fun ch =>
            PMF.map (fun r : Transcript s × α => (true, (ch, r.1)))
              (plainLaw ((P >>= fun k => k ch) >>= runStrategy s smps)) := by
        refine congrArg (PMF.bind (ProbComp.eval smp)) (funext fun ch => ?_)
        rw [hc ch]
        have hch : ∀ st' ∈ OracleComp.support (P >>= fun k => k ch), ValidStrat Q s cs st' := by
          intro st' hst'
          obtain ⟨k, hk, hk'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst'
          exact hValid k hk ch st' hk'
        have ih := runWith_honestWordState_runWordRounds_embed_of_valid Q s cs hcs smps
          (P >>= fun k => k ch) respond (embed ∘ Sum.inr) hemb' hch
        have hmap := congrArg (PMF.map fun p : Bool × Transcript s => (p.1, (ch, p.2))) ih
        simpa [PMF.map_comp, Function.comp_def] using hmap
      rw [hleft]
      simp only [runStrategy, plainLaw_bind, plainLaw_sample, PMF.map_bind, PMF.bind_bind]
      rw [PMF.bind_comm]
      refine congrArg (PMF.bind (plainLaw P)) (funext fun k => ?_)
      refine congrArg (PMF.bind (ProbComp.eval smp)) (funext fun ch => ?_)
      simp [plainLaw_pure, PMF.map, Function.comp_def]

private def PerChallenge.SuppSub :
    (s : Spec) → PerChallenge ProbComp s → PerChallenge ProbComp s → Prop
  | [], (), () => True
  | .prover _ _ :: s, smp₁, smp₂ => PerChallenge.SuppSub s smp₁ smp₂
  | .verifier _ :: s, (d₁, smp₁), (d₂, smp₂) =>
      (ProbComp.eval d₁).support ⊆ (ProbComp.eval d₂).support ∧ PerChallenge.SuppSub s smp₁ smp₂

private theorem support_runStrategy_mono {α : Type} :
    ∀ (s : Spec) (smp₁ smp₂ : PerChallenge ProbComp s),
      PerChallenge.SuppSub s smp₁ smp₂ →
      ∀ (st : ProverStrategy (ProbOracleComp OracleSpec.empty) s α),
        (plainLaw (runStrategy s smp₁ st)).support ⊆
          (plainLaw (runStrategy s smp₂ st)).support
  | [], (), (), _, _, _, hx => hx
  | .prover _ _ :: s, smp₁, smp₂, hsub, st, ⟨⟨m, τ⟩, a⟩, hx => by
      simp only [runStrategy, plainLaw_bind, plainLaw_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hx ⊢
      obtain ⟨⟨m', st'⟩, hst', ⟨τ', a'⟩, hr, ⟨rfl, rfl⟩, rfl⟩ := hx
      exact ⟨⟨m, st'⟩, hst', (τ, a),
        support_runStrategy_mono s smp₁ smp₂ hsub st' hr, ⟨rfl, rfl⟩, rfl⟩
  | .verifier _ :: s, (d₁, smp₁), (d₂, smp₂), ⟨hd, hsub⟩, st, ⟨⟨ch, τ⟩, a⟩, hx => by
      simp only [runStrategy, plainLaw_bind, plainLaw_sample, plainLaw_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx ⊢
      obtain ⟨ch', hch', st', hst', ⟨τ', a'⟩, hr, ⟨rfl, rfl⟩, rfl⟩ := hx
      exact ⟨ch, hd hch', st', hst', (τ, a),
        support_runStrategy_mono s smp₁ smp₂ hsub st' hr, ⟨rfl, rfl⟩, rfl⟩

private theorem support_plainLaw_runStrategy_mono {α : Type}
    (s : Spec) {smp₁ smp₂ : PerChallenge ProbComp s} (hsub : PerChallenge.SuppSub s smp₁ smp₂)
    (P : ProbOracleComp OracleSpec.empty (ProverStrategy (ProbOracleComp OracleSpec.empty) s α)) :
    (plainLaw (P >>= runStrategy s smp₁)).support ⊆
      (plainLaw (P >>= runStrategy s smp₂)).support := by
  intro x hx
  simp only [plainLaw_bind, PMF.mem_support_bind_iff] at hx ⊢
  obtain ⟨st, hst, hx'⟩ := hx
  exact ⟨st, hst, support_runStrategy_mono s smp₁ smp₂ hsub st hx'⟩

private theorem suppSub_perChallenge_append :
    ∀ {s₁ s₂ : Spec} {a₁ b₁ : PerChallenge ProbComp s₁} {a₂ b₂ : PerChallenge ProbComp s₂},
      PerChallenge.SuppSub s₁ a₁ b₁ → PerChallenge.SuppSub s₂ a₂ b₂ →
      PerChallenge.SuppSub (s₁ ++ s₂) (PerChallenge.append s₁ s₂ a₁ a₂)
        (PerChallenge.append s₁ s₂ b₁ b₂)
  | [], _, _, _, _, _, _, h2 => h2
  | .prover _ _ :: s₁, _, _, _, _, _, h1, h2 =>
      suppSub_perChallenge_append (s₁ := s₁) h1 h2
  | .verifier _ :: s₁, _, _, _, _, _, ⟨hd, h1⟩, h2 =>
      ⟨hd, suppSub_perChallenge_append (s₁ := s₁) h1 h2⟩

private theorem suppSub_gkrSamplers (C : LayeredCircuit) {p cw : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p) :
    PerChallenge.SuppSub (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
      (gkrSamplers C p cw) (C.protocol x).verifier.samplers := by
  have hunif : ∀ {α : Type} [Fintype α] [Nonempty α] (d : ProbComp α),
      (ProbComp.eval d).support ⊆ (ProbComp.eval (ProbComp.uniform α)).support := fun d y _ => by
    rw [ProbComp.eval_uniform, PMF.mem_support_iff, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hsc : ∀ k, PerChallenge.SuppSub (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (sumcheckSamplersApprox p cw k) (LayeredCircuit.sumcheckSamplers k) := by
    intro k
    induction k with
    | zero => trivial
    | succ k ih => exact suppSub_perChallenge_append ih ⟨hunif _, trivial⟩
  have hdesc : ∀ m, PerChallenge.SuppSub (C.descendSpec (F := ZMod p) m)
      (descendSamplersApprox C p cw m) (C.descend x m).verifier.samplers := by
    intro m
    induction m with
    | zero => trivial
    | succ m ih =>
      change PerChallenge.SuppSub (C.layerSpec (F := ZMod p) m ++ C.descendSpec (F := ZMod p) m)
        (PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
          (layerSamplersApprox C p cw m) (descendSamplersApprox C p cw m))
        (PerChallenge.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
          (C.layer x m).verifier.samplers (C.descend x m).verifier.samplers)
      refine suppSub_perChallenge_append ?_ ih
      change PerChallenge.SuppSub
        (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars m) ++
          Sumcheck.roundSpec (ZMod p))
        (PerChallenge.append _ _ (sumcheckSamplersApprox p cw (C.sumcheckVars m))
          (Nat.cast <$> sampleModNat cw p, ()))
        (PerChallenge.append _ _ (LayeredCircuit.sumcheckSamplers (C.sumcheckVars m))
          (ProbComp.uniform (ZMod p), ()))
      exact suppSub_perChallenge_append (hsc (C.sumcheckVars m)) ⟨hunif _, trivial⟩
  change PerChallenge.SuppSub
    (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
    (gkrSamplers C p cw)
    (PerChallenge.append (C.outputSpec (F := ZMod p)) (C.descendSpec (F := ZMod p) C.depth)
      (ProbComp.uniform _, ()) (C.descend x C.depth).verifier.samplers)
  exact suppSub_perChallenge_append ⟨hunif _, trivial⟩ (hdesc C.depth)

private theorem natDegree_roundPoly_le_of_complete {p n j : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (hP : ∀ v, P.degreeOf v ≤ 2) (hj : j < n)
    (r : Fin j → ZMod p) : (Sumcheck.roundPoly P r).natDegree ≤ 2 := by
  let x : Sumcheck.Claim (ZMod p) j := ⟨r, Sumcheck.partialSum P r⟩
  have hcomp := Sumcheck.round_complete 2 P hP hj x () rfl
  let bad : Set (Execution (Sumcheck.roundSpec (ZMod p)) (Sumcheck.Claim (ZMod p) (j + 1))
      (Sumcheck.Claim (ZMod p) (j + 1) × Unit)) :=
    {e | ¬ (e.output = some e.result.1 ∧ Sumcheck.rel P (j + 1) e.result.1 e.result.2)}
  let z0 : ZMod p := 0
  let g := Sumcheck.roundPoly P r
  let res : Sumcheck.Claim (ZMod p) (j + 1) × Unit := (⟨Fin.snoc r z0, g.eval z0⟩, ())
  let τ : Transcript (Sumcheck.roundSpec (ZMod p)) := (g, (z0, ()))
  let out := (Sumcheck.round 2 P j).verifier.outputOn x τ
  have hsupp : (τ, out, res) ∈ (World.plain.eval ((Sumcheck.round 2 P j).run x ())).support := by
    rw [Reduction.run, World.plain_eval_execute, PMF.support_map]
    refine ⟨(τ, res), ?_, rfl⟩
    simp only [Sumcheck.round, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample,
      PMF.bind_bind, PMF.pure_bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    refine ⟨z0, ?_, ?_⟩
    · rw [ProbComp.eval_uniform, PMF.mem_support_iff, PMF.uniformOfFintype_apply]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    · rfl
  have hgood : out = some res.1 := by
    by_contra hnot
    have hmem : (τ, out, res) ∈ bad := fun h => hnot h.1
    have hzero : World.plain.eval ((Sumcheck.round 2 P j).run x ()) (τ, out, res) = 0 := by
      rw [← PMF.toOuterMeasure_apply_singleton]
      exact le_antisymm
        ((MeasureTheory.OuterMeasure.mono _ (Set.singleton_subset_iff.mpr hmem)).trans hcomp)
        zero_le
    exact (PMF.mem_support_iff _ _).mp hsupp hzero
  have houtDef : out = if Sumcheck.accepts 2 x.value g then some res.1 else none := rfl
  rw [houtDef] at hgood
  split_ifs at hgood with hacc
  exact hacc.1

private theorem validStrat_protocol (C : LayeredCircuit) {p : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p)
    (D : (Fin (C.width C.depth) → Bool) → ZMod p) :
    ∀ st ∈ OracleComp.support ((C.protocol x).prover D ()),
      ValidStrat (fun _ => True)
        (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
        (gkrCodecs C p) st := by
  have hSumcheck : ∀ {n : ℕ} (P : MvPolynomial (Fin n) (ZMod p)), (∀ v, P.degreeOf v ≤ 2) →
      ∀ k, k ≤ n → ∀ (claim : Sumcheck.Claim (ZMod p) 0) st,
        st ∈ OracleComp.support
          ((Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
            (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
            (Sumcheck.round 2 P) k).prover claim ()) →
        ValidStrat (fun _ => True) (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
          (sumcheckCodecs p k) st := by
    intro n P hP k hk
    induction k with
    | zero => intro _ _ _; trivial
    | succ k ih =>
      intro claim st hst
      change st ∈ OracleComp.support
        (((Reduction.iterate (s := fun _ => Sumcheck.roundSpec (ZMod p))
          (S := Sumcheck.Claim (ZMod p)) (W := fun _ => Unit)
          (Sumcheck.round 2 P) k).prover claim ()) >>= fun st₁ =>
          ProverStrategy.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
            (Sumcheck.roundSpec (ZMod p)) st₁ fun ⟨claim', _⟩ =>
            (Sumcheck.round 2 P k).prover claim' ()) at hst
      obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
      refine validStrat_append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
        (sumcheckCodecs p k) (polyProverCodec p 2, fieldChallengeCodec p, ())
        st₁ _ (ih (by omega) claim st₁ hst₁) ?_ st hst'
      intro ⟨claim', _⟩ _ st₂ hst₂
      simp only [Sumcheck.round, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hst₂
      subst hst₂
      intro g st₃ hg
      simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hg
      rcases hg with ⟨rfl, rfl⟩
      refine ⟨?_, fun _ _ _ => trivial⟩
      simp only [polyProverCodec, ProverCodec.ofTotal]
      congr 1
      exact decodePoly_take_encodePoly (natDegree_roundPoly_le_of_complete P hP (by omega) _)
  have hLayer : ∀ i (claim : LayerClaim C (ZMod p) (i + 1)) st,
        st ∈ OracleComp.support ((C.layer x i).prover claim ()) →
      ValidStrat (fun _ => True) (C.layerSpec (F := ZMod p) i) (layerCodecs C p i) st := by
    intro i claim st hst
    change st ∈ OracleComp.support
      (((C.sumcheckStage i (C.value x i)).prover claim ()) >>= fun st₁ =>
        ProverStrategy.append (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars i))
          (Sumcheck.roundSpec (ZMod p)) st₁ fun ⟨endClaim, _⟩ =>
          (C.lineStep i (C.value x i)).prover endClaim ()) at hst
    obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
    have hv1 : ValidStrat (fun _ => True)
        (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) (C.sumcheckVars i))
        (sumcheckCodecs p (C.sumcheckVars i)) st₁ := by
      simp only [LayeredCircuit.sumcheckStage, Reduction.bundle,
        OracleComp.mem_supportWith_bind_iff] at hst₁
      obtain ⟨st₀, hst₀, hbl⟩ := hst₁
      exact validStrat_bindLeaf _ _ st₀ _
        (hSumcheck (C.summand i (C.value x i) claim.1)
          (C.degreeOf_summand_le i (C.value x i) claim.1)
          (C.sumcheckVars i) le_rfl claim.2 st₀ hst₀) st₁ hbl
    refine validStrat_append _ (sumcheckCodecs p (C.sumcheckVars i))
      (polyProverCodec p (C.width i), fieldChallengeCodec p, ()) st₁ _ hv1 ?_ st hst'
    intro ⟨endClaim, _⟩ _ st₂ hst₂
    simp only [LayeredCircuit.lineStep, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hst₂
    subst hst₂
    intro q st₃ hq
    simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩
    refine ⟨?_, fun _ _ _ => trivial⟩
    simp only [polyProverCodec, ProverCodec.ofTotal]
    congr 1
    exact decodePoly_take_encodePoly (natDegree_restrictLine_le _ _ _)
  have hDesc : ∀ m (claim : LayerClaim C (ZMod p) m) st,
        st ∈ OracleComp.support ((C.descend x m).prover claim ()) →
      ValidStrat (fun _ => True) (C.descendSpec (F := ZMod p) m) (descendCodecs C p m) st := by
    intro m
    induction m with
    | zero => intro _ _ _; trivial
    | succ m ih =>
      intro claim st hst
      change st ∈ OracleComp.support
        (((C.layer x m).prover claim ()) >>= fun st₁ =>
          ProverStrategy.append (C.layerSpec (F := ZMod p) m) (C.descendSpec (F := ZMod p) m)
            st₁ fun ⟨nextClaim, _⟩ => (C.descend x m).prover nextClaim ()) at hst
      obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
      refine validStrat_append _ (layerCodecs C p m) (descendCodecs C p m) st₁ _
        (hLayer m claim st₁ hst₁) (fun ⟨nextClaim, _⟩ _ st₂ hst₂ =>
          ih nextClaim st₂ hst₂) st hst'
  intro st hst
  change st ∈ OracleComp.support
    (((C.outputStep (F := ZMod p)).prover D ()) >>= fun st₁ =>
      ProverStrategy.append (C.outputSpec (F := ZMod p))
        (C.descendSpec (F := ZMod p) C.depth) st₁ fun ⟨nextClaim, _⟩ =>
        (C.descend x C.depth).prover nextClaim ()) at hst
  obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
  simp only [LayeredCircuit.outputStep, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hst₁
  subst hst₁
  refine validStrat_append (Q := fun _ : LayerClaim C (ZMod p) C.depth × Unit => True)
    (R := fun _ : Unit × Unit => True) (C.outputSpec (F := ZMod p))
    (vecChallengeCodec p (C.width C.depth), ()) (descendCodecs C p C.depth)
    (fun r => pure (.ofPoint r (eval r (multilinearExtension D)), ()))
    (fun ⟨nextClaim, _⟩ => (C.descend x C.depth).prover nextClaim ())
    (fun ch st₂ hst₂ => by
      simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff] at hst₂
      subst hst₂
      trivial)
    (fun ⟨nextClaim, _⟩ _ st₂ hst₂ => hDesc C.depth nextClaim st₂ hst₂) st hst'

/-- A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3; see also
[Thaler, §4.6][Thaler2022] — locator not re-verified against primary PDF): whenever `inst.modulus`
is prime, `minModulus (F.circuit inst.index) ≤ inst.modulus`, and the claimed output matches
`C.output` on the input table, there exists a stateful word prover accepted by `F.verifier inst`
with probability `1` (general `IsLogSpaceUniform` wiring compilation without `HasPolyTimeWiringMLE`
and `poly(S)` prover runtime remain open on `#892`). -/
theorem UniformGKRFamily.acceptProb_verifier_complete {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) (inst : Instance I) (hp : Nat.Prime inst.modulus)
    (hmin : minModulus (F.circuit inst.index) ≤ inst.modulus)
    (hcorr : inst.CorrectOutput F) :
    ∃ P : Cslib.Complexity.Prover Unit, Complexity.acceptProb (F.verifier inst) P = 1 := by
  have : Fact inst.modulus.Prime := ⟨hp⟩
  let C := F.circuit inst.index
  let p := inst.modulus
  let cw := coinBits p (challengeCount C)
  let x := tableFn p (C.width 0) inst.input
  let D := tableFn p (C.width C.depth) inst.claimedOutput
  let Pcomp := (C.protocol x).prover D ()
  let P : Cslib.Complexity.Prover Unit := honestWordProver (gkrCodecs C p) Pcomp
  refine ⟨P, ?_⟩
  have hRunSim :
      (P.run (F.verifier inst) P.init).map Prod.fst =
        (P.run ((C.protocol x).verifier.wordVerifierWith (gkrCodecs C p) (gkrSamplers C p cw) D)
          P.init).map Prod.fst := by
    simp only [Complexity.Prover.run_eq_runWith, runWith_verifier_eq_wordVerifierWith F inst hmin]
    rfl
  have hLaw :
      (P.run ((C.protocol x).verifier.wordVerifierWith (gkrCodecs C p) (gkrSamplers C p cw) D)
        P.init).map Prod.fst =
        (plainLaw (Pcomp >>= runStrategy _ (gkrSamplers C p cw))).map
          (fun r => true && ((C.protocol x).verifier.outputOn D r.1).isSome) := by
    have hEmbed :=
      runWith_honestWordState_runWordRounds_embed_of_valid (fun _ => True)
        (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth) (gkrCodecs C p)
        (challengeCodecsLawful_gkrCodecs C p) (gkrSamplers C p cw) Pcomp
        (HonestWordState.respond _ (gkrCodecs C p)) id
        (fun _ _ => by simp [Prod.map_id, PMF.map_id]) (validStrat_protocol C x D)
    have hMap := congrArg (PMF.map (fun out : Bool × Transcript
        (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth) =>
      out.1 && ((C.protocol x).verifier.outputOn D out.2).isSome)) hEmbed
    simpa only [Complexity.Prover.run_eq_runWith, Verifier.wordVerifierWith,
      ProbOracleComp.runWith_map, P, honestWordProver, PMF.map_comp, Function.comp_def,
      Prod.map, id_eq] using hMap
  have hFalse : ((P.run (F.verifier inst) P.init).map Prod.fst) false = 0 := by
    rw [hRunSim, hLaw, PMF.apply_eq_zero_iff, PMF.support_map]
    rintro ⟨r, hr, hfalse⟩
    have hrFull := support_plainLaw_runStrategy_mono _ (suppSub_gkrSamplers C x) Pcomp hr
    have hComp := C.protocol_complete x D ()
      (by simpa [Instance.CorrectOutput, C, p, x, D] using hcorr)
    rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hComp
    have hNotIn : (r.1, (C.protocol x).verifier.outputOn D r.1, r.2) ∉
        {e | ¬ (e.2.1 = some e.2.2.1 ∧ Accept e.2.2.1 e.2.2.2)} := by
      intro hmem
      have hzero : plainLaw (Pcomp >>= runStrategy _ (C.protocol x).verifier.samplers) r = 0 := by
        have h1 :
            plainLaw (Pcomp >>= runStrategy _ (C.protocol x).verifier.samplers) r ≤
              (plainLaw (Pcomp >>= runStrategy _ (C.protocol x).verifier.samplers)).toOuterMeasure
                {e | (e.1, (C.protocol x).verifier.outputOn D e.1, e.2) ∈
                  {e' | ¬ (e'.2.1 = some e'.2.2.1 ∧ Accept e'.2.2.1 e'.2.2.2)}} := by
          rw [← PMF.toOuterMeasure_apply_singleton]
          exact MeasureTheory.OuterMeasure.mono _ (Set.singleton_subset_iff.mpr hmem)
        exact le_antisymm (h1.trans hComp) zero_le
      exact (PMF.mem_support_iff _ _).mp hrFull hzero
    simp only [Set.mem_ofPred_eq, not_not] at hNotIn
    obtain ⟨hout, _⟩ := hNotIn
    dsimp only at hfalse
    rw [hout] at hfalse
    simp at hfalse
  have hSum := ((P.run (F.verifier inst) P.init).map Prod.fst).tsum_coe
  rw [tsum_bool] at hSum
  rw [hFalse, zero_add] at hSum
  exact hSum

/-- A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3) on the prime-modulus
promise domain `PrimeInstance I`: `F.verifier` is an interactive proof with completeness `1` and
soundness error `1 / 3` for prime-modulus instances with `minModulus (F.circuit inst.index) ≤
inst.modulus` and `inst.CorrectOutput F` (general `IsLogSpaceUniform` wiring compilation without
`HasPolyTimeWiringMLE`, unconditional primality checking, and `poly(S)` prover runtime remain open
on `#892`). -/
theorem UniformGKRFamily.isInteractiveProof_primeInstance {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsInteractiveProof (fun a : PrimeInstance I => F.verifier a.1)
      {a : PrimeInstance I |
        minModulus (F.circuit a.1.index) ≤ a.1.modulus ∧ a.1.CorrectOutput F}
      1 (1 / 3) := by
  refine ⟨fun ⟨inst, hp⟩ ⟨hmin, hcorr⟩ => ?_, fun ⟨inst, hp⟩ hnot P => ?_⟩
  · obtain ⟨P, hP⟩ := F.acceptProb_verifier_complete inst hp hmin hcorr
    exact ⟨P, hP.ge⟩
  · by_cases hmin : minModulus (F.circuit inst.index) ≤ inst.modulus
    · have hbad : ¬ inst.CorrectOutput F := fun hc => hnot ⟨hmin, hc⟩
      have hs := F.acceptProb_verifier_sound inst hp hbad P
      have hp_ge : (3 * (layerCost (F.circuit inst.index) : ℝ≥0∞)) ≤ (inst.modulus : ℝ≥0∞) := by
        exact_mod_cast hmin
      have hL0 : (layerCost (F.circuit inst.index) : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.mpr (layerCost_pos _).ne'
      have hLt : (layerCost (F.circuit inst.index) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      refine hs.trans ((ENNReal.div_le_div_left hp_ge _).trans ?_)
      rw [mul_comm (3 : ℝ≥0∞), div_eq_mul_inv, ENNReal.mul_inv (Or.inl hL0) (Or.inl hLt),
        ← mul_assoc, ENNReal.mul_inv_cancel hL0 hLt, one_mul, ← one_div]
    · have hzero : Complexity.acceptProb (F.verifier inst) P = 0 := by
        refine Complexity.acceptProb_eq_zero P fun r hr => ?_
        have hfalse : F.verifier inst = pure false := by simp [UniformGKRFamily.verifier, hmin]
        rw [hfalse, Complexity.Prover.run_pure, PMF.mem_support_pure_iff] at hr
        simp [hr]
      rw [hzero]
      exact zero_le

/-- A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3; see also
[Thaler, §4.6][Thaler2022] — locator not re-verified against primary PDF) on the prime-modulus
promise domain `PrimeInstance I` (used because binary-input deterministic primality testing is not
yet formalized): for any `UniformGKRFamily I encI`, verifying circuit output on `PrimeInstance I`
belongs to `Cslib.Complexity.IP` (general `IsLogSpaceUniform` wiring compilation without
`HasPolyTimeWiringMLE` and `poly(S)` prover runtime remain open on `#892`). -/
theorem UniformGKRFamily.mem_IP_primeInstance {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    {a : PrimeInstance I |
      minModulus (F.circuit a.1.index) ≤ a.1.modulus ∧ a.1.CorrectOutput F} ∈
      IP (encPrimeInstance I encI) :=
  mem_IP_of
    (F.isOraclePPTOn_verifier.preprocess
      (ComputableInPolyTime.of_eq (f := Subtype.val)
        (encIn := encPrimeInstance I encI) (encOut := encInstance I encI) fun _ => rfl))
    F.isInteractiveProof_primeInstance
    (ENNReal.div_le_of_le_mul (by norm_num)) le_rfl

end Correctness

end Cslib.Interactive.GKR
