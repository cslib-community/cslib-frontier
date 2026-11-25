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
  unfold layerCost; omega

private theorem layerCost_eq_finset (C : LayeredCircuit) :
    layerCost C = 1 + C.width C.depth + ∑ i ∈ Finset.range C.depth, 5 * C.width i := by
  rw [layerCost, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

private theorem challengeCount_eq_finset (C : LayeredCircuit) :
    challengeCount C = C.width C.depth + ∑ i ∈ Finset.range C.depth, (2 * C.width i + 1) := by
  rw [challengeCount, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

private theorem length_lineMod (p k : ℕ) (y w : List ℕ) (t : ℕ) :
    (lineMod p k y w t).length = k := by
  unfold lineMod; split_ifs <;> simp

private theorem mem_lineMod_lt {p k : ℕ} (hp : 0 < p) (y w : List ℕ) (t : ℕ) :
    ∀ v ∈ lineMod p k y w t, v < p := by
  simp only [lineMod, hp.ne', ↓reduceIte, List.mem_map, List.mem_range]
  rintro _ ⟨j, _, rfl⟩
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
  have hlength : (encodeResidues p l).length ≤ polyLimit p D := by
    have hlt : ∀ a ∈ l, a < 2 ^ elemWidth p := fun a ha =>
      (hl a ha).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p)
    rw [encodeResidues, List.length_flatMap,
      List.map_congr_left fun a ha => length_binaryWord (hlt a ha),
      List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hlen
  rw [List.take_of_length_le hlength]
  simp only [decodeResidues, hp.ne', ↓reduceIte, listRows, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, listRow_encodeResidues l hl]
  split_ifs with hi
  · rw [binaryValue_binaryWord, Nat.mod_eq_of_lt (hl _ (List.getElem_mem hi)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · have hzero : binaryValue (List.replicate (elemWidth p) false) = 0 := by
      rw [← List.append_nil (List.replicate _ _), binaryValue_replicate_false_append]; rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hi), Option.getD_none,
      hzero, Nat.zero_mod]

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
        else 0 : ℕ) : ZMod p)) = if idx < 2 ^ k then term idx else 0 := fun idx => by
    have hltIff : idx.bits.length ≤ k ↔ idx < 2 ^ k := by rw [Nat.size_eq_bits_len, Nat.size_le]
    by_cases h : idx < 2 ^ k
    · simp only [hltIff.mpr h, decide_true, ↓reduceIte, h, term, ZMod.natCast_mod, Nat.cast_mul]
      rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range, Nat.cast_prod,
        Finset.prod_range]
      simp only [natCast_litFactorNat, vecOfList]
    · simp [mt hltIff.mp h, h]
  simp_rw [hcast]
  rw [← Finset.sum_filter,
    Finset.sum_subset (fun idx h => Finset.mem_range.mpr (Finset.mem_filter.mp h).2)
      fun idx h1 h2 => by
        simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
        have hi : vals.length ≤ idx := by omega
        simp [term, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi],
    eval_multilinearExtension_eq_sum]
  refine (Finset.sum_bij (fun a _ => binaryValue (List.ofFn a))
    (fun a _ => by simpa only [Finset.mem_range, List.length_ofFn] using
      binaryValue_lt_two_pow (List.ofFn a))
    (fun _ _ _ _ hEq => List.ofFn_injective (binaryValue_injective_of_length_eq (by simp) hEq))
    (fun idx hidx => let ⟨a, ha⟩ := exists_binaryValue_eq (Finset.mem_range.mp hidx);
      ⟨a, Finset.mem_univ a, ha⟩)
    fun a _ => ?_).symm
  have hlt : binaryValue (List.ofFn a) < 2 ^ k := by
    simpa only [List.length_ofFn] using binaryValue_lt_two_pow (List.ofFn a)
  have hword : binaryWord k (binaryValue (List.ofFn a)) = List.ofFn a :=
    binaryValue_injective_of_length_eq (by simp [length_binaryWord hlt])
      (binaryValue_binaryWord _ _)
  rw [tableFn, eval_indicatorPoly_apply]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hword, show (List.ofFn a).getD j.val false = a j by simp [List.getD_eq_getElem?_getD]]
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
    ComputableInPolyTime (fun x => elemWidth (p x)) encIn encUnary :=
  (binary_log_two.comp hp).unary_add' (const 1)

private lemma polyLimit_pt {γ : Type} {encIn : γ ↪ List Bool} {p D : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hD : ComputableInPolyTime D encIn encUnary) :
    ComputableInPolyTime (fun x => polyLimit (p x) (D x)) encIn encUnary :=
  unary_mul.comp ((hD.unary_add' (const 1)).prod (elemWidth_pt hp))

private lemma unary_sum_pt : ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have hfold := foldl' (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    (list := fun l => l) (init := fun _ => 0) (step := (· + ·))
    id' (const 0) unary_add (B := fun l => (encList encUnary l).length) .self fun l i _ => by
      rw [← List.sum_eq_foldl_nat, encUnary_apply, List.length_replicate, length_encList]
      have hsub : (l.take i).sum ≤ l.sum := by
        conv_rhs => rw [← List.take_append_drop i l]
        rw [List.sum_append]; omega
      exact hsub.trans (by
        simpa only [List.map_id] using
          List.sum_le_sum (f := id) (g := fun a => 2 * (encUnary a).length + 1)
            fun a _ => by simp [encUnary_apply]; omega)
  simpa only [← List.sum_eq_foldl_nat, id_eq] using hfold

private lemma challengeCount_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime (fun ι => challengeCount (F.circuit ι)) encI encUnary :=
  (F.uniform.width_polyTime.comp (id'.prod F.uniform.depth_polyTime)).unary_add'
    (unary_sum_pt.comp (mapWith (((const 2).unary_mul' F.uniform.width_polyTime).unary_add'
      (const 1)) id' (range.comp F.uniform.depth_polyTime)))

private lemma layerCost_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime (fun ι => layerCost (F.circuit ι)) encI encUnary :=
  ((const 1).unary_add'
      (F.uniform.width_polyTime.comp (id'.prod F.uniform.depth_polyTime))).unary_add'
    (unary_sum_pt.comp (mapWith ((const 5).unary_mul' F.uniform.width_polyTime) id'
      (range.comp F.uniform.depth_polyTime)))

private lemma minModulus_pt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ComputableInPolyTime (fun ι => minModulus (F.circuit ι)) encI encUnary :=
  (const 3).unary_mul' (layerCost_pt F)

private lemma coinBits_pt {γ : Type} {encIn : γ ↪ List Bool} {p M : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hM : ComputableInPolyTime M encIn encUnary) :
    ComputableInPolyTime (fun x => coinBits (p x) (M x)) encIn encUnary :=
  ((const 2).unary_mul' ((binary_log_two.comp hp).unary_add' (const 1))).unary_add'
    ((unary_log_two.comp (hM.unary_add' (const 1))).unary_add' (const 1))

private lemma lineMod_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p k t : γ → ℕ} {y w : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hy : ComputableInPolyTime y encIn encNatList)
    (hw : ComputableInPolyTime w encIn encNatList)
    (ht : ComputableInPolyTime t encIn encNat) :
    ComputableInPolyTime (fun x => lineMod (p x) (k x) (y x) (w x) (t x)) encIn encNatList := by
  have hyj := listGetDWithInput (hy.comp (fst _ _)) (snd _ _) 0
  have hwj := listGetDWithInput (hw.comp (fst _ _)) (snd _ _) 0
  have hp' := hp.comp (fst encIn encUnary)
  exact ite_decide (decide_eq' hp (const 0)) (replicate (encA := encNat) hk (const 0))
    (mapWith (binary_mod' (binary_add' hyj (binary_mul' (ht.comp (fst _ _))
      (computableInPolyTime_subModNat hp' hwj hyj))) hp') id' (range.comp hk))

private lemma hornerModBin_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p z : γ → ℕ} {l : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hz : ComputableInPolyTime z encIn encNat)
    (hl : ComputableInPolyTime l encIn encNatList) :
    ComputableInPolyTime (fun x => hornerModBin (p x) (z x) (l x)) encIn encNat := by
  have hp0 := decide_eq' hp (const 0)
  have hmod : ComputableInPolyTime (fun x => max (p x) 1) encIn encNat :=
    (ite_decide hp0 (const 1) hp).of_enc_eq fun x => by cases p x <;> simp
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × ℕ => (q.2 + q.1.1.2 * q.1.2) % q.1.1.1)
      (encPair (encPair (encPair encNat encNat) encNat) encNat) encNat :=
    binary_mod' (binary_add' (by fun_prop) (binary_mul' (by fun_prop) (by fun_prop))) (by fun_prop)
  exact ite_decide hp0 (const 0) (foldlWith (encA := encNat) (encB := encNat) (encL := encNatList)
    (encP := encPair encNat encNat)
    (par := fun x => (max (p x) 1, z x)) (list := fun x => (l x).reverse) (init := fun _ => 0)
    (step := fun par acc a => (a + par.2 * acc) % par.1)
    (hmod.prod hz) ((listReverse encNat).comp hl) (const 0) hstep
    (B := fun x => (encNat (p x)).length + 1) (hp.polyBounded_length.add (.const 1))
    fun x i _ => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      have hlt := foldl_horner_lt (p := p x) (z := z x) (List.take i (l x).reverse)
      have hpLt := Nat.lt_size_self (p x)
      have hpos : 0 < 2 ^ (p x).size := by positivity
      exact Nat.size_le.2 (hlt.trans (by rw [Nat.pow_succ]; exact max_lt (by omega) (by omega))))

private lemma decodeResidues_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p D : γ → ℕ} {word : γ → List Bool}
    (hp : ComputableInPolyTime p encIn encNat)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hword : ComputableInPolyTime word encIn encBits) :
    ComputableInPolyTime (fun x => decodeResidues (p x) (D x) (word x)) encIn encNatList :=
  ite_decide (decide_eq' hp (const 0)) (const [])
    (mapWith (bitsBinaryValue_mod_pt (snd encIn encBits) (hp.comp (fst encIn encBits))) id'
      (bitsRowsWithInput (hD.unary_add' (const 1)) (elemWidth_pt hp) hword))

private lemma evalTableMLEMod_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p k : γ → ℕ} {vals r : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hvals : ComputableInPolyTime vals encIn encNatList)
    (hr : ComputableInPolyTime r encIn encNatList) :
    ComputableInPolyTime (fun x => evalTableMLEMod (p x) (k x) (vals x) (r x)) encIn encNat := by
  unfold evalTableMLEMod
  have hp' := hp.comp (fst encIn encUnary)
  have hk' := hk.comp (fst encIn encUnary)
  have hidxBits : ComputableInPolyTime (fun q : γ × ℕ => q.2.bits)
      (encPair encIn encUnary) encBits := natBits.comp (unary_to_binary.comp (snd encIn encUnary))
  have hcond : ComputableInPolyTime (fun q : γ × ℕ => decide (q.2.bits.length ≤ k q.1))
      (encPair encIn encUnary) encBool :=
    unary_le.comp ((length_bits.comp hidxBits).prod hk')
  have hw : ComputableInPolyTime (fun q : γ × ℕ => binaryWord (k q.1) q.2)
      (encPair encIn encUnary) encBits :=
    bitsAppend ((bitsReplicate false).comp (unary_sub.comp (hk'.prod (length_bits.comp hidxBits))))
      (bitsReverse.comp hidxBits)
  have hlit := computableInPolyTime_litFactorNat (hp'.comp (fst _ _))
    (bitsGetDWithInput (hw.comp (fst _ _)) (snd _ _) false)
    (listGetDWithInput (hr.comp ((fst _ _).comp (fst _ _))) (snd _ _) 0)
  have hbasis := binary_mod' (binary_prod.comp (mapWith hlit id' (range.comp hk'))) hp'
  have hterm : ComputableInPolyTime
      (fun q : γ × ℕ => if decide (q.2.bits.length ≤ k q.1) then
        (((vals q.1).getD q.2 0 % p q.1) *
          (((List.range (k q.1)).map fun j =>
            litFactorNat (p q.1) ((binaryWord (k q.1) q.2).getD j false)
              ((r q.1).getD j 0)).prod % p q.1)) % p q.1 else 0)
      (encPair encIn encUnary) encNat :=
    ite_decide hcond
      (binary_mod' (binary_mul'
        (binary_mod' (listGetDWithInput (hvals.comp (fst _ _)) (snd _ _) 0) hp') hbasis) hp')
      (const 0)
  exact ite_decide (decide_eq' hp (const 0)) (const 0)
    (binary_mod' (binary_sum.comp (mapWith hterm id'
      (range.comp ((length_list encNat).comp hvals)))) hp)

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
  simp [UniformGKRFamily.verifier, not_le.mpr hlt]

/-! ### Native multi-tape Turing-machine polynomial-time runtime -/

section Runtime

open ComputableInPolyTime

private lemma query_send_ppt {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} :
    IsOraclePPTOn (encPair encA encB) encBits
      (fun u => List.take 0 <$> ProbOracleComp.query ((), encB u.2)) :=
  IsOraclePPTOn.query_take ()
    ((of_eq (f := encB) (encIn := encB) (encOut := encBits) fun _ => rfl).comp (snd encA encB))
    (const 0)

private lemma mem_support_sumcheckStep {p cw : ℕ} {sc next : SumcheckState}
    (hnext : next ∈ OracleComp.support (sumcheckStep p cw sc)) :
    ∃ raw r, r ∈ (ProbComp.eval (sampleModNat cw p)).support ∧
      next = ⟨sc.challenges ++ [r], hornerModBin p r (decodeResidues p 2 raw),
        sc.ok && decide ((hornerModBin p 0 (decodeResidues p 2 raw) +
          hornerModBin p 1 (decodeResidues p 2 raw)) % p = sc.claim % p)⟩ := by
  simp only [sumcheckStep, OracleComp.mem_supportWith_bind_iff,
    OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
    ProbOracleComp.support_sample] at hnext
  obtain ⟨raw, -, r, hr, _, -, rfl⟩ := hnext
  exact ⟨raw, r, hr, rfl⟩

private lemma iterate_sumcheckStep_length {p cw : ℕ} {sc₀ : SumcheckState}
    (h0 : sc₀.challenges = []) (k : ℕ) {sc : SumcheckState}
    (hsc : sc ∈ OracleComp.support (OracleComp.iterate k (sumcheckStep p cw) sc₀)) :
    sc.challenges.length = k :=
  OracleComp.iterate_invariant (fun j x => x.challenges.length = j) (by simp [h0])
    (fun _ _ _ hj _ hnext => by
      obtain ⟨_, _, _, rfl⟩ := mem_support_sumcheckStep hnext; simp [hj])
    sc hsc

private lemma mem_support_layerExec {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) {inst : Instance I} {cw : ℕ} {st next : LayerState}
    (hnext : next ∈ OracleComp.support (layerExec F inst cw st)) :
    ∃ (sc : SumcheckState) (raw : List Bool) (t : ℕ),
      let i := st.remaining - 1
      let kIn := (F.circuit inst.index).width i
      let y := sc.challenges.take kIn
      let w := (sc.challenges.drop kIn).take kIn
      next.remaining = i ∧
      next.point = lineMod inst.modulus kIn y w t ∧
      next.value = hornerModBin inst.modulus t (decodeResidues inst.modulus kIn raw) := by
  simp only [layerExec, lineStepExec, OracleComp.mem_supportWith_bind_iff,
    OracleComp.mem_supportWith_map_iff, OracleComp.supportWith_pure, Set.mem_singleton_iff,
    ProbOracleComp.support_sample] at hnext
  obtain ⟨sc, -, raw, -, t, -, _, -, rfl⟩ := hnext
  exact ⟨sc, raw, t, rfl, rfl, rfl⟩

private lemma sampleModNat_support_size_le {coinWidth p r : ℕ}
    (hr : r ∈ (ProbComp.eval (sampleModNat coinWidth p)).support) :
    (encNat r).length ≤ (encNat p).length + coinWidth + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hlt := (ProbComp.mem_support_sampleBinaryNat_iff coinWidth r).mp
      (by simpa [sampleModNat, ProbComp.eval_map] using hr)
    exact (Nat.size_le.2 hlt).trans (by omega)
  · rw [sampleModNat, ProbComp.eval_map, PMF.mem_support_map_iff] at hr
    obtain ⟨x, _, rfl⟩ := hr
    exact (Nat.size_le_size (Nat.mod_lt _ hp).le).trans (by omega)

private lemma hornerModBin_size_le {p z : ℕ} {l : List ℕ} :
    (encNat (hornerModBin p z l)).length ≤ (encNat p).length + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [hornerModBin]
  · exact (Nat.size_le_size (hornerModBin_lt hp z l).le).trans (Nat.le_succ _)

private lemma evalTableMLEMod_size_le {p k : ℕ} {vals r : List ℕ} :
    (encNat (evalTableMLEMod p k vals r)).length ≤ (encNat p).length + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [evalTableMLEMod]
  · exact (Nat.size_le_size (evalTableMLEMod_lt hp k vals r).le).trans (Nat.le_succ _)

private lemma length_encNatList_of_forall_size {xs : List ℕ} {B : ℕ}
    (hxs : ∀ v ∈ xs, (encNat v).length ≤ B) :
    (encNatList xs).length ≤ xs.length * (2 * B + 1) := by
  rw [length_encList]
  exact (List.sum_le_sum (g := fun _ => 2 * B + 1) fun a ha => by
    have := hxs a ha; omega).trans (by simp)

private lemma uniform_width_polyBounded {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    ∃ cW dW : ℕ, ∀ (ι : I) (i : ℕ), i ≤ (F.circuit ι).depth →
      (F.circuit ι).width i ≤ cW * ((encI ι).length + 1) ^ dW := by
  obtain ⟨cD, dD, hD⟩ := F.uniform.depth_polyTime.polyBounded.exists_le
  obtain ⟨cW, dW, hW⟩ := F.uniform.width_polyTime.polyBounded.exists_le
  refine ⟨cW * (2 * cD + 5) ^ dW, dD * dW + dW, fun ι i hi => ?_⟩
  have hwi := hW (ι, i)
  have hid : i ≤ cD * ((encI ι).length + 1) ^ dD := hi.trans (hD ι)
  simp only [length_encPair, encUnary_apply, List.length_replicate] at hwi
  set n := (encI ι).length + 1
  have hn1 : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
  have hlen : 2 * (encI ι).length + 1 + i + 1 ≤ (2 * cD + 5) * n ^ max 1 dD := by
    have hn_le : n ≤ n ^ max 1 dD := Nat.le_self_pow (by omega) n
    have hD_le : n ^ dD ≤ n ^ max 1 dD := Nat.pow_le_pow_right hn1 (le_max_right _ _)
    have hn' : (encI ι).length + 1 = n := rfl
    calc 2 * (encI ι).length + 1 + i + 1
        ≤ 2 * n + cD * n ^ dD := by omega
      _ ≤ 2 * n ^ max 1 dD + cD * n ^ max 1 dD := by gcongr
      _ = (2 + cD) * n ^ max 1 dD := by ring
      _ ≤ (2 * cD + 5) * n ^ max 1 dD := Nat.mul_le_mul_right _ (by omega)
  have hw' := hwi.trans (Nat.mul_le_mul_left cW (Nat.pow_le_pow_left hlen dW))
  rw [Nat.mul_pow, ← Nat.pow_mul, ← mul_assoc] at hw'
  have hexp : max 1 dD * dW ≤ dD * dW + dW := by
    rcases Nat.eq_zero_or_pos dD with rfl | hpos
    · simp
    · rw [max_eq_right hpos]; exact Nat.le_add_right _ _
  exact hw'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 hexp))

private lemma sumcheckStep_ppt :
    IsOraclePPTOn (encPair (encPair encNat encUnary) encSumcheckState) encSumcheckState
      (fun pair : (ℕ × ℕ) × SumcheckState => sumcheckStep pair.1.1 pair.1.2 pair.2) := by
  unfold sumcheckStep
  let encIn := encPair (encPair encNat encUnary) encSumcheckState
  let encAll := encPair (encPair (encPair encIn encBits) encNat) encBits
  have hp : ComputableInPolyTime (fun x : (ℕ × ℕ) × SumcheckState => x.1.1) encIn encNat := by
    fun_prop
  have hcw : ComputableInPolyTime (fun x : (ℕ × ℕ) × SumcheckState => x.1.2) encIn encUnary := by
    fun_prop
  have hp' : ComputableInPolyTime
      (fun u : ((((ℕ × ℕ) × SumcheckState) × List Bool) × ℕ) × List Bool => u.1.1.1.1.1)
      encAll encNat := by fun_prop
  have hsc' : ComputableInPolyTime
      (fun u : ((((ℕ × ℕ) × SumcheckState) × List Bool) × ℕ) × List Bool => u.1.1.1.2)
      encAll encSumcheckState := by fun_prop
  have hr : ComputableInPolyTime
      (fun u : ((((ℕ × ℕ) × SumcheckState) × List Bool) × ℕ) × List Bool => u.1.2)
      encAll encNat := by fun_prop
  have hraw : ComputableInPolyTime
      (fun u : ((((ℕ × ℕ) × SumcheckState) × List Bool) × ℕ) × List Bool => u.1.1.2)
      encAll encBits := by fun_prop
  have hrs := decodeResidues_pt hp' (const 2) hraw
  have hStepOk := decide_eq' (binary_mod' (binary_add' (hornerModBin_pt hp' (const 0) hrs)
      (hornerModBin_pt hp' (const 1) hrs)) hp')
    (binary_mod' (encSumcheckState_claim_polyTime hsc') hp')
  have hPost := encSumcheckState_mk_polyTime
    ((encSumcheckState_challenges_polyTime hsc').listAppend' (hr.cons' (const [])))
    (hornerModBin_pt hp' hr hrs) ((encSumcheckState_ok_polyTime hsc').bool_and' hStepOk)
  exact (IsOraclePPTOn.query_take () (const []) (polyLimit_pt hp (const 2))).bind_with
    (((isPPTOn_sampleModNat (hcw.comp (fst _ _)) (hp.comp (fst _ _))).isOraclePPTOn
        (Operation := Unit)).bind_with
      (query_send_ppt.bind_with (hPost.isOraclePPTOn (Operation := Unit))))

private lemma lineStepExec_ppt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn
      (encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState))
      encLayerState
      (fun u => lineStepExec F u.1.1 u.1.2 u.2.1 u.2.2) := by
  unfold lineStepExec
  let encIn :=
    encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState)
  let encAll := encPair (encPair (encPair encIn encBits) encNat) encBits
  have hInst : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.1.1) encIn (encInstance I encI) := by fun_prop
  have hcw : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.1.2) encIn encUnary := by fun_prop
  have hSt : ComputableInPolyTime (fun u : (Instance I × ℕ) × (LayerState × SumcheckState) =>
      u.2.1) encIn encLayerState := by fun_prop
  have hP := encInstance_modulus_polyTime I encI hInst
  have hkIn := F.uniform.width_polyTime.comp
    ((encInstance_index_polyTime I encI hInst).prod
      (unary_sub.comp ((encLayerState_remaining_polyTime hSt).prod (const 1))))
  have hu : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.1.1) encAll encIn := by fun_prop
  have hSc' : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.1.1.2.2) encAll encSumcheckState := by fun_prop
  have ht : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.2) encAll encNat := by fun_prop
  have hraw : ComputableInPolyTime
      (fun q : ((((Instance I × ℕ) × (LayerState × SumcheckState)) × List Bool) × ℕ) × List Bool =>
        q.1.1.2) encAll encBits := by fun_prop
  have hp' := hP.comp hu
  have hIdx' := (encInstance_index_polyTime I encI hInst).comp hu
  have hi' := unary_sub.comp ((encLayerState_remaining_polyTime (hSt.comp hu)).prod (const 1))
  have hkIn' := hkIn.comp hu
  have hCh := encSumcheckState_challenges_polyTime hSc'
  have hy := listTakeWithInput hCh hkIn'
  have hw := listTakeWithInput (listDropWithInput hCh hkIn') hkIn'
  have hz := encLayerState_point_polyTime (hSt.comp hu)
  have hAdd := F.wiringMLE.polyTime.comp
    (encWiringMLEQuery_mk_polyTime I encI hIdx' (const Gate.add) hi' hp' hz hy hw)
  have hMul := F.wiringMLE.polyTime.comp
    (encWiringMLEQuery_mk_polyTime I encI hIdx' (const Gate.mul) hi' hp' hz hy hw)
  have hrs := decodeResidues_pt hp' hkIn' hraw
  have hq0 := hornerModBin_pt hp' (const 0) hrs
  have hq1 := hornerModBin_pt hp' (const 1) hrs
  have hrhs := binary_mod' (binary_add'
    (binary_mul' hAdd (binary_mod' (binary_add' hq0 hq1) hp'))
    (binary_mul' hMul (binary_mod' (binary_mul' hq0 hq1) hp'))) hp'
  have hPost := encLayerState_mk_polyTime hi' (lineMod_pt hp' hkIn' hy hw ht)
    (hornerModBin_pt hp' ht hrs)
    ((encSumcheckState_ok_polyTime hSc').bool_and'
      (decide_eq' (binary_mod' (encSumcheckState_claim_polyTime hSc') hp') hrhs))
  exact (IsOraclePPTOn.query_take () (const []) (polyLimit_pt hP hkIn)).bind_with
    (((isPPTOn_sampleModNat (hcw.comp (fst _ _)) (hP.comp (fst _ _))).isOraclePPTOn
        (Operation := Unit)).bind_with
      (query_send_ppt.bind_with (hPost.isOraclePPTOn (Operation := Unit))))

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
  have hkIn := F.uniform.width_polyTime.comp
    ((encInstance_index_polyTime I encI hInst).prod
      (unary_sub.comp ((encLayerState_remaining_polyTime hSt).prod (const 1))))
  have hStep' : IsOraclePPTOn (encPair encOuter encSumcheckState) encSumcheckState
      (fun q => sumcheckStep q.1.1.1.modulus q.1.1.2 q.2) :=
    sumcheckStep_ppt.preprocess
      (((encInstance_modulus_polyTime I encI (hInst.comp (fst _ _))).prod
        (hcw.comp (fst _ _))).prod (snd _ _))
  obtain ⟨cK, dK, hK⟩ := hkIn.polyBounded.exists_le
  let scSizeFun : ℕ → ℕ := fun n =>
    2 * (2 * (cK * (n + 1) ^ dK) * (2 * (2 * n + 1) + 1)) + 2 * (2 * n + 1) + 16
  have hSizeFun : PolynomiallyBounded scSizeFun := by dsimp only [scSizeFun]; fun_prop
  let scInv (p : (Instance I × ℕ) × LayerState) (j : ℕ) (sc : SumcheckState) : Prop :=
    sc.challenges.length = j ∧
      (∀ v ∈ sc.challenges, (encNat v).length ≤ (encNat p.1.1.modulus).length + p.1.2 + 1) ∧
      (encNat sc.claim).length ≤ (encNat p.1.1.modulus).length + (encLayerState p.2).length + 1
  exact (IsOraclePPTOn.iterateWith_spec ((const 2).unary_mul' hkIn)
    (encSumcheckState_mk_polyTime (const []) (encLayerState_value_polyTime hSt)
      (encLayerState_ok_polyTime hSt))
    hStep' scInv
    (fun p => ⟨rfl, fun _ h => absurd h List.not_mem_nil, by
      have := encLayerState_value_length_le p.2; dsimp only; omega⟩)
    (fun p j sc _ hsc next hnext => by
      obtain ⟨raw, r, hr, rfl⟩ := mem_support_sumcheckStep hnext
      refine ⟨by simp [hsc.1], fun v hv => ?_, hornerModBin_size_le.trans (by omega)⟩
      rcases List.mem_append.mp hv with hv | hv
      · exact hsc.2.1 v hv
      · rw [List.mem_singleton.mp hv]; exact sampleModNat_support_size_le hr)
    (PolyBounded.of_polynomiallyBounded (fun p => (encOuter p).length) hSizeFun)
    (fun p j sc hj hsc => by
      have hOuterLen : (encPair (encInstance I encI) encUnary p.1).length ≤ (encOuter p).length :=
        length_le_encPair_left _ _ p
      have hcwLen : p.1.2 ≤ (encOuter p).length := by
        simpa [encUnary_apply] using (length_le_encPair_right _ _ p.1).trans hOuterLen
      have hModLen : (encNat p.1.1.modulus).length ≤ (encOuter p).length :=
        (encInstance_modulus_length_le I encI p.1.1).trans
          ((length_le_encPair_left _ _ p.1).trans hOuterLen)
      have hStLen : (encLayerState p.2).length ≤ (encOuter p).length :=
        length_le_encPair_right _ _ p
      have hchLen := length_encNatList_of_forall_size hsc.2.1
      rw [hsc.1] at hchLen
      have hB1 : (encNatList sc.challenges).length ≤
          2 * (cK * ((encOuter p).length + 1) ^ dK) * (2 * (2 * (encOuter p).length + 1) + 1) :=
        hchLen.trans (Nat.mul_le_mul (hj.trans (Nat.mul_le_mul_left 2 (hK p))) (by omega))
      have hB2 : (encNat sc.claim).length ≤ 2 * (encOuter p).length + 1 := by omega
      dsimp only [scSizeFun]
      enc_len [encSumcheckState_apply, encSumcheckStateFields])).1

private lemma layerExec_ppt {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) :
    IsOraclePPTOn (encPair (encPair (encInstance I encI) encUnary) encLayerState) encLayerState
      (fun pair => layerExec F pair.1.1 pair.1.2 pair.2) := by
  let encOuter := encPair (encPair (encInstance I encI) encUnary) encLayerState
  have hLinePre : ComputableInPolyTime
      (fun q : ((Instance I × ℕ) × LayerState) × SumcheckState => (q.1.1, (q.1.2, q.2)))
      (encPair encOuter encSumcheckState)
      (encPair (encPair (encInstance I encI) encUnary) (encPair encLayerState encSumcheckState)) :=
    ((fst (encPair (encInstance I encI) encUnary) encLayerState).comp (fst _ _)).prod
      (((snd (encPair (encInstance I encI) encUnary) encLayerState).comp (fst _ _)).prod (snd _ _))
  have hLine : IsOraclePPTOn (encPair encOuter encSumcheckState) encLayerState
      (fun q => lineStepExec F q.1.1.1 q.1.1.2 q.1.2 q.2) :=
    ((lineStepExec_ppt F).preprocess hLinePre).congr fun _ _ oracle s =>
      congrArg (fun p => ProbOracleComp.runWith oracle p s) rfl
  exact ((layerExec_sumcheckLoop_ppt F).bind_with
    (second := fun pair sc => lineStepExec F pair.1.1 pair.1.2 pair.2 sc) hLine).congr
    fun _ _ oracle s => congrArg (fun p => ProbOracleComp.runWith oracle p s) rfl

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
      encA (encInstance I encI) := by fun_prop
  have hr : ComputableInPolyTime (fun p : (Instance I × List ℕ) × List Bool => p.1.2)
      encA encNatList := by fun_prop
  have hIdx := encInstance_index_polyTime I encI h1
  have hP := encInstance_modulus_polyTime I encI h1
  have hd := F.uniform.depth_polyTime.comp hIdx
  have hcw := coinBits_pt hP ((challengeCount_pt F).comp hIdx)
  have hInit := encLayerState_mk_polyTime hd hr
    (evalTableMLEMod_pt hP (F.uniform.width_polyTime.comp (hIdx.prod hd))
      (encInstance_claimedOutput_polyTime I encI h1) hr)
    (const true)
  have hStep := (layerExec_ppt F).preprocess
    (((h1.comp (fst encA encLayerState)).prod (hcw.comp (fst encA encLayerState))).prod
      (snd encA encLayerState))
  obtain ⟨cD, dD, hD⟩ := F.uniform.depth_polyTime.polyBounded.exists_le
  obtain ⟨cW, dW, hW⟩ := uniform_width_polyBounded F
  let layerSizeFun : ℕ → ℕ := fun n =>
    2 * (cD * (n + 1) ^ dD) + 2 * ((cW * (n + 1) ^ dW + n) * (2 * (n + 1) + 1)) + 2 * (n + 1) + 16
  have hLayerSizeFun : PolynomiallyBounded layerSizeFun := by dsimp only [layerSizeFun]; fun_prop
  let lInv (a : (Instance I × List ℕ) × List Bool) (_ : ℕ) (st : LayerState) : Prop :=
    st.remaining ≤ (F.circuit a.1.1.index).depth ∧
      st.point.length ≤ (F.circuit a.1.1.index).width st.remaining + a.1.2.length ∧
      (∀ v ∈ st.point, (encNat v).length ≤ (encA a).length + 1) ∧
      (encNat st.value).length ≤ (encA a).length + 1
  have haBounds (a : (Instance I × List ℕ) × List Bool) :
      (encI a.1.1.index).length ≤ (encA a).length ∧
      (encNat a.1.1.modulus).length ≤ (encA a).length ∧
      a.1.2.length ≤ (encA a).length ∧
      (∀ v ∈ a.1.2, (encNat v).length ≤ (encA a).length) := by
    have hPair : (encPair (encInstance I encI) encNatList a.1).length ≤ (encA a).length :=
      length_le_encPair_left _ _ a
    have hInst := (length_le_encPair_left _ _ a.1).trans hPair
    have hList := (length_le_encPair_right _ _ a.1).trans hPair
    exact ⟨(encInstance_index_length_le I encI a.1.1).trans hInst,
      (encInstance_modulus_length_le I encI a.1.1).trans hInst,
      (length_le_length_encList encNat a.1.2).trans hList,
      fun _ hv => (length_le_encList_of_mem encNat hv).trans hList⟩
  exact (IsOraclePPTOn.iterateWith_spec hd hInit hStep lInv
    (fun a => ⟨le_rfl, Nat.le_add_left _ _,
      fun v hv => ((haBounds a).2.2.2 v hv).trans (Nat.le_succ _),
      evalTableMLEMod_size_le.trans (by have := (haBounds a).2.1; omega)⟩)
    (fun a _ st _ hst next hnext => by
      obtain ⟨sc, raw, t, hrem, hpt, hval⟩ := mem_support_layerExec F hnext
      have hMod := (haBounds a).2.1
      refine ⟨hrem ▸ (Nat.sub_le _ _).trans hst.1, by rw [hpt, hrem, length_lineMod]; omega,
        fun v hv => ?_, hval ▸ hornerModBin_size_le.trans (by omega)⟩
      rw [hpt] at hv
      rcases Nat.eq_zero_or_pos a.1.1.modulus with hp0 | hpos
      · simp only [lineMod, hp0, ↓reduceIte, List.mem_replicate] at hv
        rcases hv with ⟨_, rfl⟩
        exact Nat.zero_le _
      · simp only [encNat_apply, Nat.size_eq_bits_len] at hMod ⊢
        exact (Nat.size_le_size (mem_lineMod_lt hpos _ _ _ v hv).le).trans (by omega))
    (PolyBounded.of_polynomiallyBounded (fun a => (encA a).length) hLayerSizeFun)
    (fun a _ st _ hst => by
      obtain ⟨hIdx, _, hrLen, _⟩ := haBounds a
      have hdLe : st.remaining ≤ cD * ((encA a).length + 1) ^ dD :=
        hst.1.trans ((hD a.1.1.index).trans (Nat.mul_le_mul_left cD
          (Nat.pow_le_pow_left (by omega) dD)))
      have hwLe : st.point.length ≤ cW * ((encA a).length + 1) ^ dW + (encA a).length := by
        have : (F.circuit a.1.1.index).width st.remaining ≤ cW * ((encA a).length + 1) ^ dW :=
          (hW a.1.1.index st.remaining hst.1).trans
            (Nat.mul_le_mul_left cW (Nat.pow_le_pow_left (by omega) dW))
        omega
      have hptLen : (encNatList st.point).length ≤
          (cW * ((encA a).length + 1) ^ dW + (encA a).length) * (2 * ((encA a).length + 1) + 1) :=
        (length_encNatList_of_forall_size hst.2.2.1).trans (Nat.mul_le_mul_right _ hwLe)
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
  have hIdx := encInstance_index_polyTime I encI id'
  have hP := encInstance_modulus_polyTime I encI id'
  have hInput := encInstance_input_polyTime I encI id'
  have hcw := coinBits_pt hP ((challengeCount_pt F).comp hIdx)
  have hkOut := F.uniform.width_polyTime.comp (hIdx.prod (F.uniform.depth_polyTime.comp hIdx))
  have hkIn := F.uniform.width_polyTime.comp (hIdx.prod (const 0))
  have hCond := binary_le' (unary_to_binary.comp ((minModulus_pt F).comp hIdx)) hP
  have hSampleVec :=
    ((isPPTOn_sampleModNat hcw hP).replicate hkOut).isOraclePPTOn (Operation := Unit)
  let encA := encPair (encPair (encInstance I encI) encNatList) encBits
  have hpa : ComputableInPolyTime (fun p : ((Instance I × List ℕ) × List Bool) × LayerState =>
      p.1.1.1) (encPair encA encLayerState) (encInstance I encI) := by fun_prop
  have hpst : ComputableInPolyTime (fun p : ((Instance I × List ℕ) × List Bool) × LayerState =>
      p.2) (encPair encA encLayerState) encLayerState := snd encA encLayerState
  have hFinal := (encLayerState_ok_polyTime hpst).bool_and' (decide_eq'
    (evalTableMLEMod_pt (hP.comp hpa) (hkIn.comp hpa) (hInput.comp hpa)
      (encLayerState_point_polyTime hpst))
    (binary_mod' (encLayerState_value_polyTime hpst) (hP.comp hpa)))
  exact IsOraclePPTOn.cond hCond
    (hSampleVec.bind_with (query_send_ppt.bind_with
      ((verifier_layerLoop_ppt F).bind_with
        (second := fun pair final =>
          (pure (final.ok && decide
            (evalTableMLEMod pair.1.1.modulus ((F.circuit pair.1.1.index).width 0)
              pair.1.1.input final.point = final.value % pair.1.1.modulus)) :
            WordOracleComp Unit Bool))
        (hFinal.isOraclePPTOn (Operation := Unit)))))
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
    (fieldChallengeCodec p).Lawful := fun x => by
  change ((Decoder.nat.decode (encNat x.val) : ℕ) : ZMod p) = x
  rw [Decoder.nat.decode_enc, ZMod.natCast_zmod_val]

private theorem vecChallengeCodec_lawful {p k : ℕ} [NeZero p] :
    (vecChallengeCodec p k).Lawful := fun v => by
  simp [vecChallengeCodec, (Decoder.list Decoder.nat).decode_enc, vecOfList_ofFn]

private theorem natDegree_decodePoly_le {p : ℕ} [Fact p.Prime] (D : ℕ) (word : List Bool) :
    (decodePoly p D word).natDegree ≤ D :=
  (Polynomial.natDegree_ofCoeffList_le _).trans
    (by rw [List.length_map, length_decodeResidues (Nat.Prime.pos Fact.out)]; omega)

private theorem eval_decodePoly {p : ℕ} [Fact p.Prime] (D : ℕ) (word : List Bool) (z : ℕ) :
    (decodePoly p D word).eval (z : ZMod p) =
      ((hornerModBin p z (decodeResidues p D word) : ℕ) : ZMod p) := by
  rw [decodePoly, Polynomial.eval_ofCoeffList, natCast_hornerModBin]

private theorem decodePoly_take_encodePoly {p : ℕ} [Fact p.Prime] {D : ℕ}
    {g : Polynomial (ZMod p)} (hdeg : g.natDegree ≤ D) :
    decodePoly p D ((encodePoly p D g).take (polyLimit p D)) = g := by
  have hl : ∀ a ∈ (g.coeffsBelow (D + 1)).map ZMod.val, a < p := by
    rintro _ ha; obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha; exact ZMod.val_lt c
  rw [encodePoly, decodePoly, decodeResidues_encodeResidues (Nat.Prime.pos Fact.out) D hl (by simp),
    List.map_map]
  have hmap : ((List.range (D + 1)).map
      (Nat.cast ∘ fun i => ((g.coeffsBelow (D + 1)).map ZMod.val).getD i 0)) =
      g.coeffsBelow (D + 1) :=
    List.ext_getElem (by simp) fun i hi _ => by
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
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind, PMF.map_bind, PMF.map_bind,
    ← hp, PMF.bind_map]
  exact Probability.PMF.bind_congr_on_support _ _ _ fun x hx =>
    hk x.1 (ProbOracleComp.mem_support_of_mem respond hx) x.2

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
  · simp only [hok, ↓reduceIte, Option.bind_some, sumcheck_round_outputOn]
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
          (decodePoly p 2 (raw.take (polyLimit p 2))) :=
        ⟨natDegree_decodePoly_le 2 _, heval01.mpr hstep⟩
      simp [hstep, ha, vecOfList_append_singleton hlen r, (eval_decodePoly 2 _ r).symm]
    · have ha : ¬ Sumcheck.accepts 2 (sc.claim : ZMod p)
          (decodePoly p 2 (raw.take (polyLimit p 2))) := fun h => hstep (heval01.mp h.2)
      simp [hstep, ha]
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
  | 0, _, _, _ => by
      simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure, PMF.pure_map, Prod.map,
        id_eq, Reduction.iterate, iterSpec, sumcheckCodecs, sumcheckSamplersApprox,
        runWordState, runWordRounds, ProbOracleComp.runWith_map]
      have hel : vecOfList p 0 sc₀.challenges = Fin.elim0 := funext fun j => j.elim0
      by_cases hok : sc₀.ok <;> simp [SumcheckState.toClaim?, reduction_id_outputOn, hok, hel]
  | k + 1, State, respond, s => by
      rw [OracleComp.iterate_succ]
      dsimp only [Reduction.iterate, Reduction.append, iterSpec, sumcheckCodecs,
        sumcheckSamplersApprox]
      rw [runWordState_append]
      simpa only [Prod.map_id, PMF.map_id] using
        runWith_map_bind_eq respond
          (OracleComp.iterate k (sumcheckStep p coinWidth) sc₀) _
          (SumcheckState.toClaim? p k) (sumcheckStep p coinWidth) _
          (SumcheckState.toClaim? p (k + 1)) id s
          (runWith_sumcheck_iterate P sc₀ h0 k respond s)
          fun sc hsc s' => by
            simpa only [PMF.map_id, Prod.map_id] using
              runWith_sumcheckStep_eq P sc (iterate_sumcheckStep_length h0 k hsc) respond s'

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
  · simp only [hok, ↓reduceIte, Option.map_some, Option.bind_some, lineStep_outputOn']
    let y := sc.challenges.take (C.width i)
    let w := (sc.challenges.drop (C.width i)).take (C.width i)
    let rs := decodeResidues p (C.width i) (raw.take (polyLimit p (C.width i)))
    let q : Polynomial (ZMod p) := decodePoly p (C.width i) (raw.take (polyLimit p (C.width i)))
    let xEnd : SumcheckEnd C (ZMod p) i :=
      ⟨vecOfList p (C.width (i + 1)) st.point,
        ⟨vecOfList p (C.sumcheckVars i) sc.challenges, (sc.claim : ZMod p)⟩⟩
    have hy : xEnd.left = vecOfList p (C.width i) y := (vecOfList_take_castAdd sc.challenges).symm
    have hw : xEnd.right = vecOfList p (C.width i) w := (vecOfList_drop_natAdd sc.challenges).symm
    have hwire (g : Gate) :
        ((F.evalWiring ⟨inst.index, g, i, p, st.point, y, w⟩ : ℕ) : ZMod p) =
          eval (Sum.elim xEnd.point (Sum.elim xEnd.left xEnd.right))
            (multilinearExtension (C.wiringPred (R := ZMod p) g i)) := by
      rw [hy, hw]; exact F.wiringMLE.eval_eq inst.index p g i hi st.point y w
    have hq0 : q.eval 0 = ((hornerModBin p 0 rs : ℕ) : ZMod p) := by
      simpa using eval_decodePoly (C.width i) (raw.take (polyLimit p (C.width i))) 0
    have hq1 : q.eval 1 = ((hornerModBin p 1 rs : ℕ) : ZMod p) := by
      simpa using eval_decodePoly (C.width i) (raw.take (polyLimit p (C.width i))) 1
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
    have hacc : C.lineAccepts i xEnd q ↔ sc.claim % p = rhs :=
      ⟨fun h => hcomb.mp h.2, fun h => ⟨natDegree_decodePoly_le (C.width i) _, hcomb.mpr h⟩⟩
    change (LayerState.toClaim? C p i ⟨i, lineMod p (C.width i) y w t, hornerModBin p t rs,
        true && decide (sc.claim % p = rhs)⟩) =
      if C.lineAccepts i xEnd q then some (C.lineClaim i xEnd q (t : ZMod p)) else none
    simp only [LayerState.toClaim?, Bool.true_and, decide_eq_true_eq, hacc]
    split_ifs with hline
    · simp only [LayeredCircuit.lineClaim]
      rw [vecOfList_lineMod, ← hy, ← hw, ← eval_decodePoly (C.width i) _ t]
    · rfl
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
  dsimp only [LayeredCircuit.layer, Reduction.append, layerCodecs, layerSamplersApprox]
  rw [runWordState_append]
  have hExec : layerExec F inst coinWidth st =
      OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀ >>=
        lineStepExec F inst coinWidth st := by
    simp only [layerExec, hrem, Nat.add_sub_cancel, two_mul, LayeredCircuit.sumcheckVars]; rfl
  rw [hExec]
  have hStart : st.toClaim? C p (i + 1) = (sc₀.toClaim? p 0).map (Sigma.mk z) := by
    have hel : Fin.elim0 = vecOfList p 0 [] := funext fun j => j.elim0
    by_cases hok : st.ok <;> simp [LayerState.toClaim?, SumcheckState.toClaim?, sc₀, hok, z, hel]
  have hStage :
      (ProbOracleComp.runWith respond
          (OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀) s).map
          (Prod.map (fun sc => (sc.toClaim? p (C.sumcheckVars i)).map (Sigma.mk z)) id) =
        ProbOracleComp.runWith respond
          (runWordState (C.sumcheckStage i W).verifier
            (sumcheckCodecs p (C.sumcheckVars i))
            (sumcheckSamplersApprox p coinWidth (C.sumcheckVars i))
            (st.toClaim? C p (i + 1))) s := by
    dsimp only [LayeredCircuit.sumcheckStage, Reduction.bundle]
    rw [hStart, runWordState_bundle, ProbOracleComp.runWith_map,
      ← runWith_sumcheck_iterate (coinWidth := coinWidth) (C.summand i W z) sc₀ rfl
        (C.sumcheckVars i) respond s, PMF.map_comp]
    congr 1
  simpa only [Prod.map_id, PMF.map_id] using
    runWith_map_bind_eq respond
      (OracleComp.iterate (C.sumcheckVars i) (sumcheckStep p coinWidth) sc₀) _
      (fun sc => (sc.toClaim? p (C.sumcheckVars i)).map (Sigma.mk z))
      (lineStepExec F inst coinWidth st) _ (LayerState.toClaim? C p i) id s hStage
      fun sc hsc s' => by
        simpa only [PMF.map_id, Prod.map_id] using
          runWith_lineStep_eq F inst coinWidth i hi W st hrem sc
            (iterate_sumcheckStep_length rfl _ hsc) respond s'

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
  | 0, _, _, _, _, _, _ => by
      simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure, PMF.pure_map, Prod.map,
        id_eq, LayeredCircuit.descend, LayeredCircuit.descendSpec, descendCodecs,
        descendSamplersApprox, runWordState, runWordRounds, ProbOracleComp.runWith_map,
        LayerState.toInput?, ↓reduceIte]
  | m + 1, hm, st, hrem, State, respond, s => by
      rw [OracleComp.iterate_succ_bind]
      dsimp only [LayeredCircuit.descend, Reduction.append, LayeredCircuit.descendSpec,
        descendCodecs, descendSamplersApprox]
      rw [runWordState_append]
      simpa only [Prod.map_id, PMF.map_id] using
        runWith_map_bind_eq respond (layerExec F inst coinWidth st) _
          (LayerState.toClaim? (F.circuit inst.index) inst.modulus m)
          (OracleComp.iterate m (layerExec F inst coinWidth)) _
          (LayerState.toInput? F inst x) id s
          (runWith_layerExec_eq F inst coinWidth m (by omega) x st hrem respond s)
          fun next hnext s' => by
            obtain ⟨_, _, _, hnextRem, _, _⟩ := mem_support_layerExec F hnext
            simpa only [Prod.map_id, PMF.map_id] using
              runWith_descend_eq F inst coinWidth x m (by omega) next (by omega) respond s'

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
  dsimp only [LayeredCircuit.protocol, Reduction.append, gkrCodecs, gkrSamplers]
  rw [wordVerifierWith_eq_runWordState, runWordState_append, ProbOracleComp.runWith_map]
  let prefixL : WordOracleComp Unit LayerState := do
    let r ← ProbOracleComp.sample (OracleComp.replicate (C.width C.depth) (sampleModNat cw p))
    let _ ← List.take 0 <$> ProbOracleComp.query ((), encNatList r)
    pure ⟨C.depth, r, evalTableMLEMod p (C.width C.depth) inst.claimedOutput r, true⟩
  have hLHS : F.verifier inst =
      prefixL >>= fun init =>
        (fun final : LayerState => final.ok && decide
          (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) <$>
          OracleComp.iterate C.depth (layerExec F inst cw) init := by
    simp only [UniformGKRFamily.verifier, hmin, decide_true, ↓reduceIte, prefixL, bind_assoc,
      map_eq_pure_bind, pure_bind, C, p, cw]
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
    have huLt (j : Fin (C.width C.depth)) : u j < p := by
      have hj := (ProbComp.mem_support_replicateFin_iff _ _ _).mp hu j
      rw [sampleModNat, ProbComp.eval_map, PMF.mem_support_map_iff] at hj
      obtain ⟨y, _, hy⟩ := hj; rw [← hy]; exact Nat.mod_lt _ hp
    have henc :
        (vecChallengeCodec p (C.width C.depth)).encode (fun j => (u j : ZMod p)) =
          encNatList (List.ofFn u) := by
      simp only [vecChallengeCodec]
      congr 1
      refine List.ext_getElem (by simp) fun j hj _ => by
        simp only [List.getElem_ofFn, ZMod.val_natCast_of_lt (huLt ⟨j, by simpa using hj⟩)]
    rw [henc]
    congr 1 with ⟨_, s₁⟩ : 1
    simp only [PMF.pure_map, Prod.map, id_eq]
    congr 1
    have hvec : vecOfList p (C.width C.depth) (List.ofFn u) = fun j => (u j : ZMod p) :=
      funext fun j => by simp [vecOfList, List.getD_eq_getElem?_getD]
    simp [LayerState.toClaim?, LayeredCircuit.outputStep_outputOn, LayerClaim.ofPoint, D,
      natCast_evalTableMLEMod, hvec]
  have hPrefixRem : ∀ init ∈ OracleComp.support prefixL, init.remaining = C.depth := by
    intro init hinit
    simp only [prefixL, OracleComp.mem_supportWith_bind_iff, OracleComp.mem_supportWith_map_iff,
      OracleComp.supportWith_pure, Set.mem_singleton_iff, ProbOracleComp.support_sample] at hinit
    obtain ⟨_, -, _, -, _, -, rfl⟩ := hinit; rfl
  have hOutEq (final : LayerState) :
      (final.ok &&
        decide (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) =
        (LayerState.toInput? F inst x final).isSome := by
    by_cases hok : final.ok
    · have hEqIff :
          (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p) ↔
            eval (vecOfList p (C.width 0) final.point) (multilinearExtension x) =
              (final.value : ZMod p) := by
        rw [← natCast_evalTableMLEMod, ZMod.natCast_eq_natCast_iff']
        simp only [Nat.mod_eq_of_lt (evalTableMLEMod_lt hp _ _ _)]
      dsimp only [C, p] at hEqIff
      simp only [LayerState.toInput?, LayerState.toClaim?, hok, ↓reduceIte, Option.bind_some,
        inputStep_outputOn, LayerClaim.ofPoint, LayerClaim.point, LayerClaim.value, Bool.true_and]
      by_cases hcmp : evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p
      · simp [hcmp, hEqIff.mp hcmp]
      · simp [hcmp, mt hEqIff.mpr hcmp]
    · simp [LayerState.toInput?, LayerState.toClaim?, hok]
  have hEq := runWith_map_bind_eq respond prefixL _ (LayerState.toClaim? C p C.depth)
    (fun init => (fun final : LayerState => final.ok && decide
      (evalTableMLEMod p (C.width 0) inst.input final.point = final.value % p)) <$>
      OracleComp.iterate C.depth (layerExec F inst cw) init)
    (runWordState (C.descend x C.depth).verifier
      (descendCodecs C p C.depth) (descendSamplersApprox C p cw C.depth))
    id Option.isSome s hPrefixEq
    fun init hinit s' => by
      have hMap := congrArg (PMF.map (Prod.map Option.isSome id))
        (runWith_descend_eq F inst cw x C.depth le_rfl init (hPrefixRem init hinit) respond s')
      simpa only [Prod.map_id, PMF.map_id, ProbOracleComp.runWith_map, PMF.map_comp,
        Function.comp_def, Prod.map, id_eq, hOutEq] using hMap
  simpa only [PMF.map_id, Prod.map_id, ProbOracleComp.runWith_map] using hEq

/-! ### Statistical closeness, soundness, completeness, and `IP` membership -/

private theorem coinBits_spec (p M : ℕ) : M * p ^ 2 ≤ 2 ^ coinBits p M := by
  have hp : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by decide) p
  have hM : M + 1 < 2 ^ (Nat.log 2 (M + 1) + 1) := Nat.lt_pow_succ_log_self (by decide) (M + 1)
  have hp2 : p ^ 2 ≤ 2 ^ (2 * (Nat.log 2 p + 1)) := by
    rw [sq, two_mul, Nat.pow_add]; exact Nat.mul_le_mul hp.le hp.le
  calc M * p ^ 2
      ≤ 2 ^ (Nat.log 2 (M + 1) + 1) * 2 ^ (2 * (Nat.log 2 p + 1)) := Nat.mul_le_mul (by omega) hp2
    _ = 2 ^ coinBits p M := by rw [mul_comm, ← Nat.pow_add]; rfl

private theorem mul_div_coinBits_le {p M : ℕ} (hp : 0 < p) :
    (M : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / 2 ^ coinBits p M) ≤ 1 / (p : ℝ≥0∞) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hreal : (M : ℝ) * ((p : ℝ) / 2 ^ coinBits p M) ≤ 1 / (p : ℝ) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hpR]
    have hbound : (M : ℝ) * (p : ℝ) * (p : ℝ) ≤ (2 : ℝ) ^ coinBits p M := by
      exact_mod_cast (by simpa [pow_two, mul_assoc] using coinBits_spec p M : M * p * p ≤ _)
    linarith
  have hENN := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos hpR, ENNReal.ofReal_one, ENNReal.ofReal_natCast] at hENN
  exact hENN

private theorem closeTo_replicateFin_sampleModNat {p cw : ℕ} [NeZero p] :
    ∀ k : ℕ, Probability.CloseTo
      (ProbComp.eval (ProbComp.uniform (Fin k → ZMod p)))
      (ProbComp.eval (OracleComp.replicateFin k (Nat.cast <$> sampleModNat cw p)))
      ((k : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / 2 ^ cw))
  | 0 => by
      have h1 : ProbComp.eval (ProbComp.uniform (Fin 0 → ZMod p)) = PMF.pure Fin.elim0 := by
        rw [ProbComp.eval_uniform]; ext f; obtain rfl : f = Fin.elim0 := funext fun i => i.elim0
        simp
      simp [h1, OracleComp.replicateFin_zero]
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
      have hCont :
          ∀ ch ∈ (ProbComp.eval ((Nat.cast : ℕ → ZMod p) <$> sampleModNat cw p)).support,
            Probability.CloseTo
              (ProbComp.eval (Fin.cons (α := fun _ => ZMod p) ch <$>
                OracleComp.replicateFin k (ProbComp.uniform (ZMod p))))
              (ProbComp.eval (Fin.cons (α := fun _ => ZMod p) ch <$>
                OracleComp.replicateFin k ((Nat.cast : ℕ → ZMod p) <$> sampleModNat cw p)))
              ((k : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) := fun ch _ => by
        rw [ProbComp.eval_map, ProbComp.eval_map, OracleComp.replicateFin_eq_pi,
          ProbComp.eval_pi_uniform, ← ProbComp.eval_uniform (Fin k → ZMod p)]
        exact (closeTo_replicateFin_sampleModNat (p := p) (cw := cw) k).map
          (Fin.cons (α := fun _ : Fin (k + 1) => ZMod p) ch)
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hSingle.bind hCont

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
      dsimp only [iterSpec, sumcheckCloseErrors]
      rw [PerChallenge.sum_append, sum_sumcheckCloseErrors ε k]
      simp [PerChallenge.sum, add_mul, Nat.cast_add]

private theorem sum_descendCloseErrors {C : LayeredCircuit} {p : ℕ} [Fact p.Prime] (ε : ℝ≥0∞) :
    ∀ m, PerChallenge.sum (C.descendSpec (F := ZMod p) m)
        (descendCloseErrors C p ε m) =
      ((∑ i ∈ Finset.range m, (2 * C.width i + 1) : ℕ) : ℝ≥0∞) * ε
  | 0 => by simp [descendCloseErrors, LayeredCircuit.descendSpec, PerChallenge.sum]
  | m + 1 => by
      dsimp only [LayeredCircuit.descendSpec, descendCloseErrors, LayeredCircuit.layerSpec,
        layerCloseErrors]
      rw [PerChallenge.sum_append, PerChallenge.sum_append,
        sum_sumcheckCloseErrors ε (C.sumcheckVars m), sum_descendCloseErrors ε m,
        Finset.sum_range_succ, Nat.cast_add, add_mul]
      simp only [PerChallenge.sum, add_zero]
      push_cast
      ring

private theorem sum_gkrCloseErrors_le (C : LayeredCircuit) (p : ℕ) [Fact p.Prime] :
    PerChallenge.sum (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
        (gkrCloseErrors C p (coinBits p (challengeCount C))) ≤ 1 / (p : ℝ≥0∞) := by
  dsimp only [gkrCloseErrors]
  rw [PerChallenge.sum_append, sum_descendCloseErrors]
  simp only [PerChallenge.sum, add_zero]
  rw [← add_mul, ← Nat.cast_add, ← challengeCount_eq_finset]
  exact mul_div_coinBits_le (Nat.Prime.pos Fact.out)

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
  | cons r s₁ ih => cases r with
    | prover _ _ => exact ih h1
    | verifier _ => exact ⟨h1.1, ih h1.2⟩

private theorem closeTo_sumcheckSamplers {p cw : ℕ} [Fact p.Prime] :
    ∀ k, PerChallenge.CloseTo (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (LayeredCircuit.sumcheckSamplers (F := ZMod p) k)
      (sumcheckSamplersApprox p cw k)
      (sumcheckCloseErrors p (ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) k)
  | 0 => trivial
  | k + 1 => closeTo_perChallenge_append (closeTo_sumcheckSamplers k)
      ⟨by rw [ProbComp.eval_uniform, ProbComp.eval_map]
          exact (closeTo_of_dist_le_ofReal
            (ProbComp.dist_map_natCast_eval_sampleModNat_le cw p)).symm,
        trivial⟩

private theorem closeTo_descendSamplers (C : LayeredCircuit) {p cw : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p) :
    ∀ m, PerChallenge.CloseTo (C.descendSpec (F := ZMod p) m)
      (C.descend x m).verifier.samplers
      (descendSamplersApprox C p cw m)
      (descendCloseErrors C p (ENNReal.ofReal ((p : ℝ) / 2 ^ cw)) m)
  | 0 => trivial
  | m + 1 =>
      closeTo_perChallenge_append
        (closeTo_perChallenge_append (closeTo_sumcheckSamplers (C.sumcheckVars m))
          ⟨by rw [ProbComp.eval_uniform, ProbComp.eval_map]
              exact (closeTo_of_dist_le_ofReal
                (ProbComp.dist_map_natCast_eval_sampleModNat_le cw p)).symm,
            trivial⟩)
        (closeTo_descendSamplers C x m)

private theorem closeTo_gkrSamplers (C : LayeredCircuit) {p cw : ℕ} [Fact p.Prime]
    (x : (Fin (C.width 0) → Bool) → ZMod p) :
    PerChallenge.CloseTo (C.outputSpec (F := ZMod p) ++ C.descendSpec (F := ZMod p) C.depth)
      (C.protocol x).verifier.samplers
      (gkrSamplers C p cw)
      (gkrCloseErrors C p cw) :=
  closeTo_perChallenge_append ⟨closeTo_replicateFin_sampleModNat (C.width C.depth), trivial⟩
    (closeTo_descendSamplers C x C.depth)

private theorem acceptProb_verifier_eq_zero_of_not_le {I : Type} {encI : I ↪ List Bool}
    (F : UniformGKRFamily I encI) {inst : Instance I}
    (hmin : ¬ minModulus (F.circuit inst.index) ≤ inst.modulus)
    (P : Cslib.Complexity.Prover Unit) :
    Complexity.acceptProb (F.verifier inst) P = 0 :=
  Complexity.acceptProb_eq_zero P fun r hr => by
    rw [F.verifier_of_lt_minModulus (lt_of_not_ge hmin), Complexity.Prover.run_pure,
      PMF.mem_support_pure_iff] at hr
    simp [hr]

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
    have hSim : Complexity.acceptProb (F.verifier inst) P =
        Complexity.acceptProb
          ((C.protocol x).verifier.wordVerifierWith (gkrCodecs C p) (gkrSamplers C p cw) D) P := by
      simp only [Complexity.acceptProb, Complexity.Prover.run_eq_runWith,
        runWith_verifier_eq_wordVerifierWith F inst hmin]; rfl
    rw [hSim]
    have hSound := (C.protocol_sound (F := ZMod p) x).acceptProb_wordVerifier (gkrCodecs C p)
      (by simpa [Instance.CorrectOutput, C, p, x, D] using hbad) P
    have hTV := (C.protocol x).verifier.acceptProb_wordVerifierWith_le_wordVerifier_add
      (gkrCodecs C p) (closeTo_gkrSamplers C (cw := cw) x) D P
    refine hTV.trans (add_le_add hSound (sum_gkrCloseErrors_le C p) |>.trans ?_)
    rw [ZMod.card p, ← ENNReal.add_div, add_comm, ← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add,
      ← Nat.add_assoc, ← layerCost_eq_finset]
  · rw [acceptProb_verifier_eq_zero_of_not_le F hmin P]; exact zero_le

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
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst
      intro m rest hm
      simp only [OracleComp.mem_supportWith_bind_iff, OracleComp.supportWith_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨m', st₁'⟩, hst1, rest', hrest', rfl, rfl⟩ := hm
      obtain ⟨hdec, hvalid1⟩ := h1 m st₁' hst1
      exact ⟨hdec, validStrat_append s₁ cs₁ c₂ st₁' next hvalid1 h2 rest hrest'⟩
  | .verifier _ :: s₁, s₂, (_, cs₁), c₂, st₁, next, h1, h2, st, hst => by
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst
      intro ch rest hrest
      obtain ⟨st₁', hst1, hrest'⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
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
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst'
      intro m rest hm
      simp only [OracleComp.mem_supportWith_bind_iff, OracleComp.supportWith_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨m', st₁⟩, hst1, rest', hrest', rfl, rfl⟩ := hm
      obtain ⟨hdec, hv⟩ := h m st₁ hst1
      exact ⟨hdec, validStrat_bindLeaf s cs st₁ _ hv rest hrest'⟩
  | .verifier _ :: s, (_, cs), st, f, h, st', hst' => by
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst'
      intro ch rest hrest
      obtain ⟨st₁, hst1, hrest'⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
      exact validStrat_bindLeaf s cs st₁ _ (h ch st₁ hst1) rest hrest'

private theorem mem_support_of_mem_plainLaw {α : Type} {p : ProbOracleComp OracleSpec.empty α}
    {a : α} (ha : a ∈ (plainLaw p).support) : a ∈ OracleComp.support p := by
  rw [plainLaw, ← OracleComp.evalWith_eq_interpret, OracleComp.support_evalWith] at ha
  exact OracleComp.supportWith_mono (fun _ => Set.subset_univ _) p ha

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
          (HonestWordState.respond s cs q st).map (Prod.map id (embed ∘ Sum.inr)) := fun q st => by
        rw [hemb q (.inr st), HonestWordState.respond, PMF.map_comp]; rfl
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
              (plainLaw (pure x.2 >>= runStrategy s smp)) :=
        Probability.PMF.bind_congr_on_support _ _ _ fun ⟨m, next⟩ hmx => by
          obtain ⟨st, hst, hm⟩ := OracleComp.mem_supportWith_bind_iff.mp
            (mem_support_of_mem_plainLaw hmx)
          obtain ⟨hdec, hcont⟩ := hValid st hst m next hm
          have ih := runWith_honestWordState_runWordRounds_embed_of_valid Q s cs hChal smp
            (pure next) respond (embed ∘ Sum.inr) hemb'
            (fun _ hst' => OracleComp.eq_of_mem_supportWith_pure hst' ▸ hcont)
          simpa [PMF.map_comp, Function.comp_def, hdec, ProverCodec.decodeOrDefault] using
            congrArg (PMF.map fun p : Bool × Transcript s =>
              ((c.decode ((c.encode m).take c.limit)).isSome && p.1,
                (c.decodeOrDefault ((c.encode m).take c.limit), p.2))) ih
      rw [hleft]
      simp only [runStrategy, plainLaw_bind, id_eq, PMF.bind_bind,
        plainLaw_pure, PMF.pure_bind, PMF.map, Function.comp_def]
  | .verifier _ :: s, (c, cs), ⟨hc, hcs⟩, (smp, smps), P, State, respond, embed, hemb, hValid => by
      have hemb' : ∀ q st, respond q (embed (.inr st)) =
          (HonestWordState.respond s cs q st).map (Prod.map id (embed ∘ Sum.inr)) := fun q st => by
        rw [hemb q (.inr st), HonestWordState.respond, PMF.map_comp]; rfl
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
              (plainLaw ((P >>= fun k => k ch) >>= runStrategy s smps)) :=
        congrArg (PMF.bind (ProbComp.eval smp)) (funext fun ch => by
          rw [hc ch]
          have ih := runWith_honestWordState_runWordRounds_embed_of_valid Q s cs hcs smps
            (P >>= fun k => k ch) respond (embed ∘ Sum.inr) hemb' fun st' hst' => by
              obtain ⟨k, hk, hk'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst'
              exact hValid k hk ch st' hk'
          simpa [PMF.map_comp, Function.comp_def] using
            congrArg (PMF.map fun p : Bool × Transcript s => (p.1, (ch, p.2))) ih)
      rw [hleft]
      simp only [runStrategy, plainLaw_bind, plainLaw_sample, PMF.map_bind, PMF.bind_bind]
      rw [PMF.bind_comm]
      refine congrArg (PMF.bind (plainLaw P)) (funext fun k =>
        congrArg (PMF.bind (ProbComp.eval smp)) (funext fun ch => by
          simp [plainLaw_pure, PMF.map, Function.comp_def]))

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
      (plainLaw (P >>= runStrategy s smp₂)).support := fun x hx => by
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
      (ProbComp.eval d).support ⊆ (ProbComp.eval (ProbComp.uniform α)).support := fun d _ _ => by
    rw [ProbComp.eval_uniform, PMF.mem_support_iff, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hsc : ∀ k, PerChallenge.SuppSub (iterSpec (fun _ => Sumcheck.roundSpec (ZMod p)) k)
      (sumcheckSamplersApprox p cw k) (LayeredCircuit.sumcheckSamplers k) := fun k => by
    induction k with
    | zero => trivial
    | succ k ih => exact suppSub_perChallenge_append ih ⟨hunif _, trivial⟩
  have hdesc : ∀ m, PerChallenge.SuppSub (C.descendSpec (F := ZMod p) m)
      (descendSamplersApprox C p cw m) (C.descend x m).verifier.samplers := fun m => by
    induction m with
    | zero => trivial
    | succ m ih =>
      exact suppSub_perChallenge_append
        (suppSub_perChallenge_append (hsc (C.sumcheckVars m)) ⟨hunif _, trivial⟩) ih
  exact suppSub_perChallenge_append ⟨hunif _, trivial⟩ (hdesc C.depth)

private theorem not_mem_of_toOuterMeasure_le_zero {α : Type*} {μ : PMF α} {S : Set α}
    (hμ : μ.toOuterMeasure S ≤ 0) {a : α} (ha : a ∈ μ.support) : a ∉ S := fun hmem =>
  (PMF.mem_support_iff _ _).mp ha (le_antisymm
    ((show μ a ≤ μ.toOuterMeasure S by
        rw [← PMF.toOuterMeasure_apply_singleton]
        exact MeasureTheory.OuterMeasure.mono _ (Set.singleton_subset_iff.mpr hmem)).trans hμ)
    zero_le)

private theorem natDegree_roundPoly_le_of_complete {p n j : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (hP : ∀ v, P.degreeOf v ≤ 2) (hj : j < n)
    (r : Fin j → ZMod p) : (Sumcheck.roundPoly P r).natDegree ≤ 2 := by
  let x : Sumcheck.Claim (ZMod p) j := ⟨r, Sumcheck.partialSum P r⟩
  let g := Sumcheck.roundPoly P r
  let res : Sumcheck.Claim (ZMod p) (j + 1) × Unit := (⟨Fin.snoc r 0, g.eval 0⟩, ())
  let τ : Transcript (Sumcheck.roundSpec (ZMod p)) := (g, (0, ()))
  let out := (Sumcheck.round 2 P j).verifier.outputOn x τ
  have hsupp : (τ, out, res) ∈ (World.plain.eval ((Sumcheck.round 2 P j).run x ())).support := by
    rw [Reduction.run, World.plain_eval_execute, PMF.support_map]
    refine ⟨(τ, res), ?_, rfl⟩
    simp only [Sumcheck.round, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample,
      PMF.bind_bind, PMF.pure_bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    refine ⟨0, ?_, rfl⟩
    rw [ProbComp.eval_uniform, PMF.mem_support_iff, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hgood := not_mem_of_toOuterMeasure_le_zero (Sumcheck.round_complete 2 P hP hj x () rfl) hsupp
  simp only [Set.mem_ofPred_eq, not_not] at hgood
  have hgood' := hgood.1
  change (if Sumcheck.accepts 2 x.value g then some res.1 else none) = some res.1 at hgood'
  split_ifs at hgood' with hacc
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
          (sumcheckCodecs p k) st := fun {n} P hP k hk => by
    induction k with
    | zero => intro _ _ _; trivial
    | succ k ih =>
      intro claim st hst
      obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
      refine validStrat_append _ (sumcheckCodecs p k)
        (polyProverCodec p 2, fieldChallengeCodec p, ())
        st₁ _ (ih (by omega) claim st₁ hst₁) ?_ st hst'
      intro ⟨claim', _⟩ _ st₂ hst₂
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst₂
      intro g st₃ hg
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.eq_of_mem_supportWith_pure hg)
      exact ⟨congrArg some (decodePoly_take_encodePoly
        (natDegree_roundPoly_le_of_complete P hP (by omega) _)), fun _ _ _ => trivial⟩
  have hLayer : ∀ i (claim : LayerClaim C (ZMod p) (i + 1)) st,
        st ∈ OracleComp.support ((C.layer x i).prover claim ()) →
      ValidStrat (fun _ => True) (C.layerSpec (F := ZMod p) i) (layerCodecs C p i) st :=
    fun i claim st hst => by
      obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
      obtain ⟨st₀, hst₀, hbl⟩ := OracleComp.mem_supportWith_bind_iff.mp hst₁
      have hv1 := validStrat_bindLeaf _ (sumcheckCodecs p (C.sumcheckVars i)) st₀ _
        (hSumcheck (C.summand i (C.value x i) claim.1)
          (C.degreeOf_summand_le i (C.value x i) claim.1)
          (C.sumcheckVars i) le_rfl claim.2 st₀ hst₀) st₁ hbl
      refine validStrat_append _ (sumcheckCodecs p (C.sumcheckVars i))
        (polyProverCodec p (C.width i), fieldChallengeCodec p, ()) st₁ _ hv1 ?_ st hst'
      intro ⟨endClaim, _⟩ _ st₂ hst₂
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst₂
      intro q st₃ hq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.eq_of_mem_supportWith_pure hq)
      exact ⟨congrArg some (decodePoly_take_encodePoly (natDegree_restrictLine_le _ _ _)),
        fun _ _ _ => trivial⟩
  have hDesc : ∀ m (claim : LayerClaim C (ZMod p) m) st,
        st ∈ OracleComp.support ((C.descend x m).prover claim ()) →
      ValidStrat (fun _ => True) (C.descendSpec (F := ZMod p) m) (descendCodecs C p m) st :=
    fun m => by
      induction m with
      | zero => intro _ _ _; trivial
      | succ m ih =>
        intro claim st hst
        obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
        exact validStrat_append _ (layerCodecs C p m) (descendCodecs C p m) st₁ _
          (hLayer m claim st₁ hst₁) (fun ⟨nextClaim, _⟩ _ st₂ hst₂ => ih nextClaim st₂ hst₂)
          st hst'
  intro st hst
  obtain ⟨st₁, hst₁, hst'⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
  obtain rfl := OracleComp.eq_of_mem_supportWith_pure hst₁
  exact validStrat_append (Q := fun _ : LayerClaim C (ZMod p) C.depth × Unit => True)
    (R := fun _ : Unit × Unit => True) (C.outputSpec (F := ZMod p))
    (vecChallengeCodec p (C.width C.depth), ()) (descendCodecs C p C.depth) _ _
    (fun _ _ _ => trivial) (fun ⟨nextClaim, _⟩ _ st₂ hst₂ => hDesc C.depth nextClaim st₂ hst₂)
    st hst'

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
      runWith_honestWordState_runWordRounds_embed_of_valid (fun _ => True) _ (gkrCodecs C p)
        (challengeCodecsLawful_gkrCodecs C p) (gkrSamplers C p cw) Pcomp
        (HonestWordState.respond _ (gkrCodecs C p)) id
        (fun _ _ => by simp [Prod.map_id, PMF.map_id]) (validStrat_protocol C x D)
    simpa only [Complexity.Prover.run_eq_runWith, Verifier.wordVerifierWith,
      ProbOracleComp.runWith_map, P, honestWordProver, PMF.map_comp, Function.comp_def,
      Prod.map, id_eq] using congrArg (PMF.map fun out : Bool × Transcript _ =>
        out.1 && ((C.protocol x).verifier.outputOn D out.2).isSome) hEmbed
  have hFalse : ((P.run (F.verifier inst) P.init).map Prod.fst) false = 0 := by
    rw [hRunSim, hLaw, PMF.apply_eq_zero_iff, PMF.support_map]
    rintro ⟨r, hr, hfalse⟩
    have hrFull := support_plainLaw_runStrategy_mono _ (suppSub_gkrSamplers C x) Pcomp hr
    have hComp := C.protocol_complete x D ()
      (by simpa [Instance.CorrectOutput, C, p, x, D] using hcorr)
    rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hComp
    have hNotIn := not_mem_of_toOuterMeasure_le_zero hComp hrFull
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not, Execution.output] at hNotIn
    simp [hNotIn.1] at hfalse
  have hSum := ((P.run (F.verifier inst) P.init).map Prod.fst).tsum_coe
  rw [tsum_bool, hFalse, zero_add] at hSum
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
    · have hp_ge : (3 * (layerCost (F.circuit inst.index) : ℝ≥0∞)) ≤ (inst.modulus : ℝ≥0∞) := by
        exact_mod_cast hmin
      have hL0 : (layerCost (F.circuit inst.index) : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.mpr (layerCost_pos _).ne'
      have hLt : (layerCost (F.circuit inst.index) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      refine (F.acceptProb_verifier_sound inst hp (fun hc => hnot ⟨hmin, hc⟩) P).trans
        ((ENNReal.div_le_div_left hp_ge _).trans ?_)
      rw [mul_comm (3 : ℝ≥0∞), div_eq_mul_inv, ENNReal.mul_inv (Or.inl hL0) (Or.inl hLt),
        ← mul_assoc, ENNReal.mul_inv_cancel hL0 hLt, one_mul, ← one_div]
    · rw [acceptProb_verifier_eq_zero_of_not_le F hmin P]; exact zero_le

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
