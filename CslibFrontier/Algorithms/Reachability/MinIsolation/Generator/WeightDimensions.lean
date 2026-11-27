/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedWeight
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Offset
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FramePrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Native Justesen weights from binary dimensions

The request frames binary graph dimensions and vertex coordinates ahead of the raw seed bits.
One native initializer prepares the field data and returns the offset of the seed on the
original input in workspace linear in the header length. The seed suffix may have any length.
The compiled pass reads through this offset and computes the weight in space linear in the
encoded graph dimensions on canonical inputs, supplying the generator space bound in
[Hoza2026NLUL, Theorem 1.3].
-/

public section

namespace Cslib.Reachability.Hoza.SeedWeight.Dimensions

open Cslib.Code.JustesenFamily
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- Graph dimensions and the coordinates of the vertex whose weight is requested. -/
structure Header where
  /-- Number of columns in a layer. -/
  width : ℕ
  /-- Last layer of the graph. -/
  horizon : ℕ
  /-- Layer of the requested vertex. -/
  layer : ℕ
  /-- Column of the requested vertex. -/
  column : ℕ

/-- Framed binary width, horizon and layer, followed by the binary column. -/
enc_structure encHeader : Header where
  width : encNat, horizon : encNat, layer : encNat, column : encNat

/-- A weight request with unprepared dimensions and a raw seed in increasing index order. -/
structure Input where
  /-- Binary graph and vertex parameters. -/
  header : Header
  /-- The seed read by the weight pass. -/
  seed : List Bool

/-- Framed binary header followed by the original seed bits without further framing. -/
enc_structure encInput : Input where
  header : encHeader, seed : encBits

/-- Prepare the Justesen context and locate the first seed bit on the original input. -/
@[expose] def load (x : Input) : QueryMachine.Located Context :=
  ⟨(frame (encHeader x.header)).length,
    ⟨fieldContext x.header.width x.header.horizon, x.header.layer, x.header.column⟩⟩

/-- The offset returned by initialization selects exactly the original raw seed. -/
theorem drop_seed (x : Input) : (encInput x).drop (load x).offset = x.seed := by
  simp [load, encInput_apply, encInputFields, encPair_apply, encBits_apply]

/-- Native initialization uses workspace linear in the encoded binary header length,
independently of the seed suffix. -/
theorem load_inSpace :
    ComputableInSpace load encInput (QueryMachine.encLocated Context encContext)
      (fun x => (encHeader x.header).length) := by
  have hheader := ComputableInSpace.framedPrefix Input.header encInput encHeader Input.seed
    (fun x => by simp [encInput_apply, encInputFields])
  have hdim := budget_prod (encHeader_width_budget hheader) (encHeader_horizon_budget hheader)
  have hfield := budget_comp_linear fieldContext_inSpace hdim
  have hcontext := encContext_mk_budget hfield
    (encHeader_layer_budget hheader) (encHeader_column_budget hheader)
  exact QueryMachine.encLocated_mk_budget Context encContext hheader.frameLength hcontext

private theorem length_encInput (x : Input) :
    (encInput x).length = 2 * (encHeader x.header).length + 1 + x.seed.length := by
  simp only [encInput_apply, encInputFields, length_encPair, encBits_apply]

/-- One native machine initializes the field and evaluates the weight from the original seed
suffix. The workspace and binary output length are linear in the complete encoded request. -/
theorem weight_inSpace :
    ComputableInSpace (fun x : Input => SeedWeight.weight (load x).inner x.seed)
      encInput encNat (fun x => (encInput x).length + 1) :=
  Runtime.weight_inSpace_of_locate
    (load_inSpace.mono_le fun x => by rw [length_encInput]; omega) drop_seed

/-- Supply the graph dimensions, a valid vertex, and a seed in increasing index order. -/
@[expose] def canonicalInput {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : Input :=
  ⟨⟨w, n, z.1.val, z.2.val⟩, List.ofFn seed⟩

private theorem length_canonicalInput_le_encodedDimensions :
    ∃ C : ℕ, ∀ {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
      (encInput (canonicalInput seed z)).length + 2 ≤
        C * ((encPair encNat encNat (w, n)).length + 1) := by
  obtain ⟨S, hS⟩ : (fun p : ℕ × ℕ => codeLength p.1 p.2) ≼
      fun p => (encPair encNat encNat p).length := ⟨_, codeLength_le_encodedDimensions⟩
  refine ⟨S + 11, fun {w n} seed z => ?_⟩
  let x := canonicalInput seed z
  let dim := (encPair encNat encNat (w, n)).length + 1
  have hcolumn := length_encNat_mono z.2.isLt.le
  have hlayer := length_encNat_mono (Nat.le_of_lt_succ z.1.isLt)
  have hheader : (encHeader x.header).length ≤ 4 * dim := by
    dsimp only [x, canonicalInput, Input.header, dim]
    simp only [encHeader_apply, encHeaderFields, length_encPair]
    omega
  have hseed : x.seed.length ≤ S * dim := by
    simpa only [x, canonicalInput, Input.seed, List.length_ofFn, dim] using hS (w, n)
  change (encInput x).length + 2 ≤ (S + 11) * dim
  rw [length_encInput, Nat.add_mul]
  omega

/-- The native weight computation on binary graph dimensions, a valid vertex and a canonical
read-only seed. A single machine computes the existing generated weight for all dimensions.
Its workspace and binary output length are linear in the encoded dimensions. The time bound
is existential and indexed by the complete request. -/
theorem generatedWeight_computesInTimeAndSpace :
    ∃ (time : Input → ℕ) (C k : ℕ) (State : Type) (_ : Finite State)
        (tm : MultiTapeTM k Bool State),
      ∀ {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
        let x := canonicalInput seed z
        let budget := C * ((encPair encNat encNat (w, n)).length + 1)
        tm.ComputesInTimeAndSpace (encInput x) (encNat (generatedWeight seed z)) (time x) budget ∧
          (encNat (generatedWeight seed z)).length ≤ budget := by
  obtain ⟨time, A, ⟨k, State, hfinite, tm, hrun⟩, hout⟩ := weight_inSpace
  obtain ⟨C, hC⟩ := length_canonicalInput_le_encodedDimensions
  refine ⟨time, A * C, k, State, hfinite, tm, fun {w n} seed z => ?_⟩
  intro x budget
  have hbound : A * ((encInput x).length + 2) ≤ budget :=
    (Nat.mul_le_mul_left A (hC seed z)).trans_eq (Nat.mul_assoc _ _ _).symm
  obtain ⟨houtput, htime, hspace⟩ := hrun x
  rw [← weight_eq_generatedWeight seed z]
  exact ⟨⟨houtput, htime, hspace.mono hbound⟩, (hout x).trans hbound⟩

end Cslib.Reachability.Hoza.SeedWeight.Dimensions
