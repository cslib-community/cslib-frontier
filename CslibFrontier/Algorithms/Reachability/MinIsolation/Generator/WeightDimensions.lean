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

/-!
# Raw-input initialization for the Justesen weight pass

The request frames binary graph dimensions and vertex coordinates ahead of the raw seed bits.
One native initializer prepares the field data and returns the offset of the seed on the
original input in workspace linear in the header length. The seed suffix may have any length.
This supplies the entry data for the dimension-based weight generator. Compiling the initializer
and weight pass together is the next step toward the space guarantee in [Hoza2026NLUL, Theorem 1.3].
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

end Cslib.Reachability.Hoza.SeedWeight.Dimensions
