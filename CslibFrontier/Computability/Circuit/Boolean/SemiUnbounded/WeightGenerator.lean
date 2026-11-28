/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedRank
public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.MinIsolation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.JustesenBit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization

/-!
# Native AND-level-scaled weight generator for semi-unbounded circuits

This module implements Work Package 2 of cslib-frontier #7920: a native small-space weight
generator for layered semi-unbounded Boolean circuits, reusing `Cslib.Code.JustesenFamily` and
the retained-rank digit accumulator `Cslib.Reachability.Hoza.SeedRank.accumulateRank` directly.

Compared with Hoza's layered-digraph generator (`Cslib.Reachability.Hoza.SeedWeight`), the
2-adic halving loop of `CslibFrontier/Algorithms/Reachability/MinIsolation/Generator/Scale.lean`
is replaced by direct AND-level scaling `scaleByLevel andLevel acc = 6 ^ andLevel * acc`,
certified in workspace linear in the encoded pair plus the numeric `andLevel` via
`Turing.MultiTapeTM.ComputableInSpace.budget_natPow_variable`. Leaves and OR gates receive
weight `0`.

Two entry points are provided:
* **Retained-rank interface (`WeightGenerator.gateWeightRank`)**: takes a code-bit callback, a
  `SeedRank.Request`, the gate's `andLevel`, and its `isAnd` flag from the circuit interface,
  running in workspace linear in the encoded request plus `seed.width + andLevel`
  (`gateWeightRank_inSpace`, `gateWeightRank_justesen_inSpace`) and composing with any logspace
  request producer (`gateWeightRank_inLogSpace`).
* **Standalone streaming query (`WeightGenerator.evalInput`)**: takes binary circuit size `N`,
  gate metadata (`andLevel`, `isAnd`, `gate`), and raw seed bits in increasing index order,
  matching `SeedDigits.maskedPrefix` via `ofBits` (`evalInput_eq_gateWeightRank`) and
  `LayeredSemiUnboundedCircuit.generatedGateWeight` (`evalInput_canonicalInput`). One fixed
  deterministic multitape Turing machine evaluates it in workspace `O(andLevel + log₂ N + 1)`
  (`generatedGateWeight_computesInTimeAndSpace`), giving logarithmic workspace `O(log N)`,
  logarithmic seed length `ℓ = O(log N)`, and polynomial weights `ρ < 6 ^ (K + ℓ) = poly(N)`
  whenever `K = O(log N)` (`generatedGateWeight_certified`).

This is original library development for #7920 (not a registered cited result); AuxPDA models,
uniform circuit interfaces, unambiguous proof-tree scans, and `LogCFL = UAuxPDA(log n, poly)`
remain tracked in #7920.

## Main definitions

All declarations below live in `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit` (with the
generator interface under the `WeightGenerator` sub-namespace):

* `isAndGate`: Boolean test for AND gates.
* `scaleByLevel`: direct scaling by `6 ^ andLevel`.
* `WeightGenerator.GateRequest`: retained-rank seed request paired with `andLevel` and `isAnd`.
* `WeightGenerator.gateWeightRank`: native retained-rank gate-weight evaluator.
* `WeightGenerator.Header`, `WeightGenerator.Input`, `WeightGenerator.evalInput`: standalone
  binary-metadata and raw-seed weight query.

## Main results

* `scaleByLevel_inSpace`: native workspace certificate for `6 ^ andLevel * acc`.
* `WeightGenerator.gateWeightRank_eq_seededGateWeight` and
  `WeightGenerator.gateWeightRank_justesen_eq`: agreement of the retained-rank evaluator with
  `seededGateWeight` and `generatedGateWeight`.
* `WeightGenerator.gateWeightRank_inSpace`, `WeightGenerator.gateWeightRank_justesen_inSpace`,
  and `WeightGenerator.gateWeightRank_inLogSpace`: native space and logspace-composition
  certificates for the retained-rank evaluator.
* `WeightGenerator.generatedGateWeightBound_inSpace`: native workspace bound for the uniform
  ceiling `6 ^ (K + codeLength N 0)`.
* `WeightGenerator.generatedGateWeight_computesInTimeAndSpace`: one fixed Turing machine
  computing `generatedGateWeight` in `O(andLevel + log₂ N + 1)` space.
* `WeightGenerator.generatedGateWeight_certified`: joint isolation, seed-length, polynomial
  magnitude, and logspace evaluation certificate.
-/

public section

namespace Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit

open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- Boolean predicate identifying AND gates (leaves and OR gates return `false`). -/
@[expose] def isAndGate {G : Type*} (C : LayeredSemiUnboundedCircuit G) (g : G) : Bool :=
  match C.kind g with
  | .and _ => true
  | .leaf _ | .or => false

/-- Scale an accumulated base-six masked-seed digit sum by `6 ^ andLevel`. -/
@[expose] def scaleByLevel (andLevel accumulator : ℕ) : ℕ :=
  6 ^ andLevel * accumulator

/-- Direct AND-level scaling `6 ^ andLevel * accumulator` runs in native workspace linear in
the encoded binary pair plus the numeric `andLevel`. -/
theorem scaleByLevel_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => scaleByLevel p.1 p.2)
      (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length + p.1) := by
  let B (p : ℕ × ℕ) := (encPair encNat encNat p).length + p.1
  have hin : (fun p : ℕ × ℕ => (encPair encNat encNat p).length) ≼ B :=
    .of_le fun _ => Nat.le_add_right _ _
  have hpow : ComputableInSpace (fun p : ℕ × ℕ => 6 ^ p.1) (encPair encNat encNat) encNat B :=
    budget_natPow_variable (budget_const 6) ((fst encNat encNat).weaken hin) <|
      .of_le_linear 4 4 fun p => by
        rw [show (encNat 6).length = 3 from rfl]
        have : (encNat p.1).length ≤ (encPair encNat encNat p).length := by
          simp only [length_encPair]; omega
        dsimp only [B]; omega
  exact (budget_natMul hpow ((snd encNat encNat).weaken hin)).of_enc_eq fun _ => rfl

namespace WeightGenerator

/-- A retained-rank seed request paired with the gate's AND-level and AND-gate flag supplied by
the circuit interface. -/
structure GateRequest (κ : Type) where
  /-- Code context, candidate seed rank, and seed width for `SeedRank.accumulateRank`. -/
  seed : SeedRank.Request κ
  /-- Zero-based AND-level of the gate (`C.andLevel g`). -/
  andLevel : ℕ
  /-- Whether the gate is an AND gate (`true`) or an OR gate / leaf (`false`). -/
  isAnd : Bool

variable {κ : Type}

/-- Framed retained-rank seed request and binary AND-level, followed by the unframed AND-gate
flag. -/
enc_structure encGateRequest (encContext : κ ↪ List Bool) : GateRequest κ where
  seed : (SeedRank.encRequest encContext), andLevel : encNat, isAnd : encBool

/-- Compute the AND-level-scaled gate weight from a retained binary seed rank, returning `0`
for leaves and OR gates (`isAnd = false`). -/
@[expose] def gateWeightRank (code : κ → ℕ → Bool) (q : GateRequest κ) : ℕ :=
  if q.isAnd then scaleByLevel q.andLevel (SeedRank.accumulateRank code q.seed) else 0

/-- Any code-bit callback agreeing with `word g` on `Fin ℓ` makes `gateWeightRank` agree with
`LayeredSemiUnboundedCircuit.seededGateWeight`. -/
theorem gateWeightRank_eq_seededGateWeight {G : Type*} {ℓ : ℕ}
    (C : LayeredSemiUnboundedCircuit G) (code : κ → ℕ → Bool) (ctx : κ)
    (word : G → Fin ℓ → Bool) (rank : Fin (2 ^ ℓ)) (g : G)
    (hcode : ∀ j : Fin ℓ, code ctx j.val = word g j) :
    gateWeightRank code ⟨⟨ctx, rank.val, ℓ⟩, C.andLevel g, C.isAndGate g⟩ =
      C.seededGateWeight word ((BitString.equivFin ℓ).symm rank) g := by
  unfold gateWeightRank seededGateWeight isAndGate scaleByLevel
  cases C.kind g with
  | leaf _ | or => rfl
  | and _ =>
    simp only [↓reduceIte, SeedRank.accumulateRank_eq_seed, hcode]
    exact six_pow_mul_accumulateWeightDigits_eq_levelWeight (C.andLevel g) (word g)
      ((BitString.equivFin ℓ).symm rank)

/-- Any callback giving the table-free Justesen coordinate makes `gateWeightRank` agree with
`LayeredSemiUnboundedCircuit.generatedGateWeight`. -/
theorem gateWeightRank_eq_generatedGateWeight {N : ℕ}
    (C : LayeredSemiUnboundedCircuit (Fin N)) (code : κ → ℕ → Bool) (ctx : κ)
    (rank : Fin (2 ^ codeLength N 0)) (g : Fin N)
    (hcode : ∀ j : Fin (codeLength N 0), code ctx j.val = indexedCodewordMod (n := 0) g j) :
    gateWeightRank code ⟨⟨ctx, rank.val, codeLength N 0⟩, C.andLevel g, C.isAndGate g⟩ =
      C.generatedGateWeight ((BitString.equivFin _).symm rank) g :=
  gateWeightRank_eq_seededGateWeight C code ctx (indexedCodeword (n := 0)) rank g fun j =>
    (hcode j).trans (indexedCodewordMod_eq (n := 0) g j)

/-- Compute the AND-level-scaled gate weight using a supplied linear-space code-bit routine.
Both the seed width and the gate's AND-level are charged numerically, while the context, rank,
and flag are charged through the encoded request. -/
theorem gateWeightRank_inSpace [Inhabited κ] (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length)) :
    ComputableInSpace (gateWeightRank code) (encGateRequest encContext) encNat
      (fun q => (encGateRequest encContext q).length + q.seed.width + q.andLevel) := by
  let B (q : GateRequest κ) := (encGateRequest encContext q).length + q.seed.width + q.andLevel
  have hid := budget_id (show (fun q => (encGateRequest encContext q).length) ≼ B from
    .of_le fun _ => (Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hacc := budget_comp (SeedRank.accumulateRank_inSpace encContext code hc)
    (encGateRequest_seed_budget encContext hid) (.of_le fun q => by
      simp only [B, encGateRequest_apply, encGateRequestFields, length_encPair]; omega)
  have hpair := budget_prod (encGateRequest_andLevel_budget encContext hid) hacc
  exact (budget_ite (encGateRequest_isAnd_budget encContext hid)
    (budget_comp scaleByLevel_inSpace hpair
      (hpair.length_le.add (.of_le fun _ => by dsimp only [B]; omega)))
    (budget_const 0)).of_enc_eq fun q => by simp [gateWeightRank]

/-- Code-bit callback reading one indexed Justesen coordinate from a retained field context and
binary gate index. -/
@[expose] def justesenCodeBit (p : FieldContext × ℕ) (index : ℕ) : Bool :=
  p.1.indexedBit p.2 index

/-- With the retained Justesen field context and binary gate index, `gateWeightRank` evaluates
`LayeredSemiUnboundedCircuit.generatedGateWeight` exactly. -/
theorem gateWeightRank_justesen_eq {N : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
    (rank : Fin (2 ^ codeLength N 0)) (g : Fin N) :
    gateWeightRank justesenCodeBit
        ⟨⟨(fieldContext N 0, g.val), rank.val, codeLength N 0⟩, C.andLevel g, C.isAndGate g⟩ =
      C.generatedGateWeight ((BitString.equivFin _).symm rank) g :=
  gateWeightRank_eq_generatedGateWeight C justesenCodeBit (fieldContext N 0, g.val) rank g
    (fieldContext_indexedBit_eq (n := 0) g)

/-- Native workspace certificate for the Justesen-instantiated retained-rank gate-weight
evaluator. -/
theorem gateWeightRank_justesen_inSpace :
    ComputableInSpace (gateWeightRank justesenCodeBit)
      (encGateRequest (encPair encFieldContext encNat)) encNat
      (fun q => (encGateRequest (encPair encFieldContext encNat) q).length +
        q.seed.width + q.andLevel) := by
  let : Inhabited (FieldContext × ℕ) := ⟨(⟨0, 0, []⟩, 0)⟩
  exact gateWeightRank_inSpace (encPair encFieldContext encNat) justesenCodeBit
    fieldContext_indexedBit_inSpace

/-- Composing `gateWeightRank` with any logspace request producer whose encoded request, seed
width, and AND-level are all logarithmic in the input length yields a `ComputableInLogSpace`
gate-weight evaluator. -/
theorem gateWeightRank_inLogSpace [Inhabited κ] {α : Type} {encIn : α ↪ List Bool}
    (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length))
    {req : α → GateRequest κ}
    (hreq : ComputableInLogSpace req encIn (encGateRequest encContext))
    (hbound : ∃ C, ∀ a,
      (encGateRequest encContext (req a)).length + (req a).seed.width + (req a).andLevel ≤
        C * (Nat.log2 (encIn a).length + 1)) :
    ComputableInLogSpace (fun a => gateWeightRank code (req a)) encIn encNat := by
  obtain ⟨t, c, hwork, -⟩ := (gateWeightRank_inSpace encContext code hc).comp_logSpace hreq
  obtain ⟨C, hC⟩ := hbound
  refine ⟨t, c * (C + 1), hwork.mono (fun _ => le_rfl) fun a => ?_⟩
  have hCa := hC a
  dsimp only
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left c (by rw [Nat.add_mul, Nat.one_mul]; omega)

/-- Computing the seed-independent gate-weight bound `6 ^ (maxAndLevel + codeLength gateCount 0)`
uses workspace linear in the encoded binary pair `(gateCount, maxAndLevel)` plus the numeric
`maxAndLevel`. -/
theorem generatedGateWeightBound_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => generatedGateWeightBound p.1 p.2)
      (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length + p.2) := by
  have hin : (fun p : ℕ × ℕ => (encPair encNat encNat p).length) ≼
      fun p => (encPair encNat encNat p).length + p.2 := .of_le fun _ => Nat.le_add_right _ _
  have hexp := budget_natAdd ((snd encNat encNat).weaken hin) <| budget_comp_linear
    codeLength_inSpace (budget_prod ((fst encNat encNat).weaken hin) (budget_const 0))
  have hpair := budget_prod hexp (budget_const (encB := encNat) 1)
  refine (budget_comp scaleByLevel_inSpace hpair <| hpair.length_le.add
    (show (fun p : ℕ × ℕ => p.2 + codeLength p.1 0) ≼ _ from
      .of_le_linear (268435456 + 1) 268435456 fun p => ?_)).of_enc_eq fun p =>
      congrArg encNat (by simp [generatedGateWeightBound, scaleByLevel])
  have hc := codeLength_le_encodedDimensions (p.1, 0)
  have h0 : (encNat 0).length = 0 := rfl
  have : (encPair encNat encNat (p.1, 0)).length ≤ (encPair encNat encNat p).length := by
    simp only [length_encPair, h0]; omega
  dsimp only at hc; omega

/-- Binary circuit size and gate metadata supplied by the circuit interface for a standalone
gate-weight query. -/
structure Header where
  /-- Number of gates `N` in the circuit (`Fin N`). -/
  gateCount : ℕ
  /-- Zero-based AND-level of the queried gate (`C.andLevel g`). -/
  andLevel : ℕ
  /-- Whether the queried gate is an AND gate (`true`) or an OR gate / leaf (`false`). -/
  isAnd : Bool
  /-- Binary index of the queried gate (`g.val`). -/
  gate : ℕ

/-- Framed binary gate count, AND-level, and AND-gate flag, followed by the binary gate index. -/
enc_structure encHeader : Header where
  gateCount : encNat, andLevel : encNat, isAnd : encBool, gate : encNat

/-- A standalone gate-weight query pairing binary circuit/gate metadata with raw seed bits in
increasing index order. -/
structure Input where
  /-- Binary circuit size and gate metadata. -/
  header : Header
  /-- Raw seed bits in increasing index order. -/
  seed : List Bool

/-- Framed binary header followed by the raw seed bits without additional framing. -/
enc_structure encInput : Input where
  header : encHeader, seed : encBits

/-- Evaluate the AND-level-scaled Justesen gate weight on a standalone query input by streaming
the raw seed bits in increasing index order (`SeedDigits.maskedPrefix`). -/
@[expose] def evalInput (x : Input) : ℕ :=
  if x.header.isAnd then
    scaleByLevel x.header.andLevel
      (SeedDigits.maskedPrefix (justesenCodeBit (fieldContext x.header.gateCount 0, x.header.gate))
        x.seed x.seed.length)
  else 0

/-- Construct the canonical standalone query input for a circuit on `Fin N`, a Justesen seed in
increasing index order, and a gate `g : Fin N`. -/
@[expose] def canonicalInput {N : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
    (seed : Fin (codeLength N 0) → Bool) (g : Fin N) : Input :=
  ⟨⟨N, C.andLevel g, C.isAndGate g, g.val⟩, List.ofFn seed⟩

/-- Reading the raw seed through `ofBits` and `List.length` makes `gateWeightRank` agree with
the streaming `SeedDigits.maskedPrefix` evaluator `evalInput` on every input, including trailing
`false` bits and empty seeds. -/
theorem evalInput_eq_gateWeightRank (x : Input) :
    evalInput x = gateWeightRank justesenCodeBit
      ⟨⟨(fieldContext x.header.gateCount 0, x.header.gate), ofBits x.seed, x.seed.length⟩,
        x.header.andLevel, x.header.isAnd⟩ := by
  unfold evalInput gateWeightRank
  split_ifs
  · congr 1
    unfold SeedDigits.maskedPrefix SeedRank.accumulateRank ofBits
    congr 1
    funext j
    rw [← Cslib.BitString.lsbValue_eq_foldr_bit, Cslib.BitString.testBit_lsbValue]; rfl
  · rfl

/-- On canonical inputs, `evalInput` returns the exact weight `C.generatedGateWeight seed g`. -/
theorem evalInput_canonicalInput {N : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
    (seed : Fin (codeLength N 0) → Bool) (g : Fin N) :
    evalInput (canonicalInput C seed g) = C.generatedGateWeight seed g := by
  unfold evalInput canonicalInput generatedGateWeight seededGateWeight isAndGate scaleByLevel
  cases C.kind g with
  | leaf _ | or => rfl
  | and _ =>
    simp only [↓reduceIte, List.length_ofFn, SeedDigits.maskedPrefix_ofFn, justesenCodeBit,
      fieldContext_indexedBit_eq (n := 0) g, indexedCodewordMod_eq (n := 0) g]
    exact six_pow_mul_accumulateWeightDigits_eq_levelWeight (C.andLevel g)
      (indexedCodeword (n := 0) g) seed

/-- One native machine prepares the Justesen field context and evaluates `evalInput` from the
binary header and raw seed in workspace linear in `(encInput x).length + x.header.andLevel + 1`. -/
theorem evalInput_inSpace :
    ComputableInSpace evalInput encInput encNat
      (fun x => (encInput x).length + x.header.andLevel + 1) := by
  let B (x : Input) := (encInput x).length + x.header.andLevel + 1
  have hid := budget_id (show (fun x => (encInput x).length) ≼ B from
    .of_le fun _ => (Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hheader := encInput_header_budget hid
  have hseed := encInput_seed_budget hid
  have hfield := budget_comp_linear fieldContext_inSpace
    (budget_prod (encHeader_gateCount_budget hheader) (budget_const 0))
  have hseedReq := SeedRank.encRequest_mk_budget (encPair encFieldContext encNat)
    (budget_prod hfield (encHeader_gate_budget hheader))
    (budget_comp_linear (of_inO ComputableInO.bitsToNat) hseed)
    (budget_comp_linear (of_inO ComputableInO.lengthNat) hseed)
  have hreq := encGateRequest_mk_budget (encPair encFieldContext encNat) hseedReq
    (encHeader_andLevel_budget hheader) (encHeader_isAnd_budget hheader)
  have hseedLe : (fun x : Input => x.seed.length) ≼ B := .of_le fun x => by
    simp only [B, encInput_apply, encInputFields, length_encPair, encBits_apply]; omega
  exact (budget_comp gateWeightRank_justesen_inSpace hreq
    ((hreq.length_le.add hseedLe).add (.of_le fun _ => by dsimp only [B]; omega))).of_enc_eq
      fun x => congrArg encNat (evalInput_eq_gateWeightRank x)

private theorem length_canonicalInput_add_level_le {N : ℕ}
    (C : LayeredSemiUnboundedCircuit (Fin N)) (seed : Fin (codeLength N 0) → Bool) (g : Fin N) :
    (encInput (canonicalInput C seed g)).length + C.andLevel g + 2 ≤
      (268435456 + 20) * (C.andLevel g + Nat.log2 N + 1) := by
  let L := Nat.log2 N + 1
  have hN : (encNat N).length ≤ L := length_encNat_le_log2 le_rfl
  have hg : (encNat g.val).length ≤ L := (length_encNat_mono g.isLt.le).trans hN
  have hlev : (encNat (C.andLevel g)).length ≤ C.andLevel g :=
    length_encNat_eq_size _ ▸ Nat.size_le_self _
  have hseed : codeLength N 0 ≤ 268435456 * L := by
    simpa only [Nat.zero_add, Nat.mul_one, ← Nat.log2_eq_log_two] using (codeLength_bounds N 0).2
  simp only [canonicalInput, encInput_apply, encInputFields, encHeader_apply, encHeaderFields,
    length_encPair, encBits_apply, encBool_apply, List.length_ofFn, List.length_singleton]
  dsimp only [L] at *; omega

/-- One fixed deterministic multitape Turing machine evaluates `C.generatedGateWeight seed g` on
every canonical input in workspace and binary output length `O(C.andLevel g + Nat.log2 N + 1)`. -/
theorem generatedGateWeight_computesInTimeAndSpace :
    ∃ (time : Input → ℕ) (spaceFactor k : ℕ) (State : Type) (_ : Finite State)
        (tm : MultiTapeTM k Bool State),
      ∀ {N : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
        (seed : Fin (codeLength N 0) → Bool) (g : Fin N),
        let x := canonicalInput C seed g
        let budget := spaceFactor * (C.andLevel g + Nat.log2 N + 1)
        tm.ComputesInTimeAndSpace (encInput x) (encNat (C.generatedGateWeight seed g))
          (time x) budget ∧
        (encNat (C.generatedGateWeight seed g)).length ≤ budget := by
  obtain ⟨time, A, ⟨k, State, hfinite, tm, hrun⟩, hout⟩ := evalInput_inSpace
  refine ⟨time, A * (268435456 + 20), k, State, hfinite, tm, fun {N} C seed g => ?_⟩
  intro x budget
  have hbound : A * ((encInput x).length + x.header.andLevel + 1 + 1) ≤ budget := by
    simpa only [budget, x, canonicalInput, Nat.mul_assoc] using
      Nat.mul_le_mul_left A (length_canonicalInput_add_level_le C seed g)
  obtain ⟨houtput, htime, hspace⟩ := hrun x
  rw [← evalInput_canonicalInput C seed g]
  exact ⟨⟨houtput, htime, hspace.mono hbound⟩, (hout x).trans hbound⟩

/-- Joint isolation, seed-length, magnitude, and native logspace evaluation certificate for
AND-level-scaled Justesen gate weights on layered semi-unbounded circuits of size `N`.

One fixed deterministic multitape Turing machine evaluates `C.generatedGateWeight seed g` on
`encInput (canonicalInput C seed g)`. Across all circuit sizes `N` and logarithmic AND-depth
constants `c` (`C.andLevel g ≤ c * (Nat.log2 N + 1)`):
* the seed length satisfies `codeLength N 0 ≤ seedFactor * (Nat.log2 N + 1)`;
* every normal-form circuit admits a min-isolating seed;
* every generated gate weight satisfies `ρ < 6 ^ (C.andLevel g + codeLength N 0)` and
  `ρ < (2 * (N + 1)) ^ weightDegree c`;
* the machine computes `encNat (C.generatedGateWeight seed g)` in logarithmic workspace
  `spaceFactor * (c + 1) * (Nat.log2 N + 1)`.

This is original formalization for Work Package 2 of cslib-frontier #7920 (not a registered
cited result). -/
theorem generatedGateWeight_certified :
    ∃ (seedFactor spaceFactor : ℕ) (weightDegree : ℕ → ℕ)
      (time : Input → ℕ) (k : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM k Bool State),
      ∀ N : ℕ,
        codeLength N 0 ≤ seedFactor * (Nat.log2 N + 1) ∧
        (∀ (C : LayeredSemiUnboundedCircuit (Fin N)), C.InNormalForm →
          ∃ seed, C.IsMinIsolating (C.generatedGateWeight seed)) ∧
        ∀ (c : ℕ) (C : LayeredSemiUnboundedCircuit (Fin N))
          (seed : Fin (codeLength N 0) → Bool) (g : Fin N),
          C.andLevel g ≤ c * (Nat.log2 N + 1) →
            let input := canonicalInput C seed g
            C.generatedGateWeight seed g < 6 ^ (C.andLevel g + codeLength N 0) ∧
            C.generatedGateWeight seed g < (2 * (N + 1)) ^ weightDegree c ∧
            tm.ComputesInTimeAndSpace (encInput input)
              (encNat (C.generatedGateWeight seed g))
              (time input) (spaceFactor * (c + 1) * (Nat.log2 N + 1)) := by
  choose weightDegree hpoly using generatedGateWeight_polynomial_of_log_depth
  obtain ⟨time, spaceFactor, k, State, hfinite, tm, hrun⟩ :=
    generatedGateWeight_computesInTimeAndSpace
  refine ⟨268435456, spaceFactor, weightDegree, time, k, State, hfinite, tm, fun N => ?_⟩
  refine ⟨?_, fun C hnorm => C.exists_generatedGateWeight_isMinIsolating hnorm,
    fun c C seed g hdepth => ?_⟩
  · simpa only [Nat.zero_add, Nat.mul_one, ← Nat.log2_eq_log_two] using (codeLength_bounds N 0).2
  · obtain ⟨⟨houtput, htime, hspace⟩, -⟩ := hrun C seed g
    refine ⟨C.generatedGateWeight_lt_pow seed g,
      hpoly c N C seed g (by simpa only [← Nat.log2_eq_log_two] using hdepth),
      ⟨houtput, htime, hspace.mono ?_⟩⟩
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left spaceFactor (by rw [Nat.add_mul, Nat.one_mul]; omega)

end WeightGenerator

end Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit
