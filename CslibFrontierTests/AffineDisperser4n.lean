/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n

/-!
# Tests for the `4n - 9d` circuit lower bound

Non-vacuous client examples checking `0/5` parameter weights, zero-locus pair operations
(`addPair`), concrete `2`- and `4`-input circuits (including a circuit bloated with free constants
and unary negations where `binaryB2Cost = 0` strictly beats `size = 8`) against
`four_mul_le_cost_add`, `four_mul_le_size_add`, and `exists_affine_subspace_const_of_cost_lt`, and
non-vacuous `d = 11` witnesses via `exists_isAffineDisperser` (`301 ≤ C.program.cost binaryB2Cost`
at `n = 100`).
-/

set_option linter.privateModule false

public section

namespace CslibFrontierTests.AffineDisperser4n

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.SemiCircuit Cslib.Circuits.Boolean.AffineDisperser4n

/-- Basic checks on `0/5` weights and zero-locus pairs. -/
example : weight 0 = 0 ∧ weight 1 = 5 ∧ weight 3 = 5 ∧
    (⟨0, false, 1, true⟩ : ZeroPair).Holds (fun i => if i = 0 then false else false) ∧
    ¬ (⟨0, false, 1, true⟩ : ZeroPair).Holds (fun i => if i = 0 then true else false) := by
  refine ⟨rfl, rfl, rfl, Or.inl rfl, ?_⟩
  decide

/-- A concrete `2`-input `2`-affine disperser `f x = x 0 && x 1` and a `1`-gate circuit computing
it, witnessing `4 * 2 ≤ 1 + 9 * 2`. -/
private def and2Fn : BooleanFunction 2 := fun x => x 0 && x 1

private theorem and2Fn_disperser : IsAffineDisperser and2Fn 2 := by
  intro g _ hinj
  have himg : (Finset.univ.image g : Finset (BitString 2)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_image_of_injective _ hinj]
      decide)
  obtain ⟨u, _, hu⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ (fun _ => false))
  obtain ⟨v, _, hv⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ (fun _ => true))
  exact ⟨u, v, by rw [hu, hv]; decide⟩

private def and2Circuit : Circuit (fullSignature 2 Bool) 2 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 && xs 1, fun i => Wire.input i⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

example : and2Circuit.size = 1 ∧
    4 * 2 ≤ and2Circuit.program.cost binaryB2Cost + 9 * 2 ∧
    4 * 2 ≤ and2Circuit.size + 9 * 2 := by
  have hcomp : and2Circuit.Computes fullInterpretation (single and2Fn) := by
    intro x
    ext i
    rw [Fin.eq_zero i]
    rfl
  exact ⟨rfl, four_mul_le_cost_add and2Fn_disperser and2Circuit hcomp,
    four_mul_le_size_add and2Fn_disperser and2Circuit hcomp⟩

/-- An `8`-gate circuit on `4` bits built solely from constants and unary negations/projections:
`size + 9 * 1 = 17 ≥ 4 * 4`, yet `binaryB2Cost = 0` (`0 + 9 * 1 < 4 * 4`), so
`exists_affine_subspace_const_of_cost_lt` applies while `size` alone is too large. -/
private def bloatedUnary4Circuit : Circuit (fullSignature 2 Bool) 4 1 :=
  let p0 : Program (fullSignature 2 Bool) 4 0 := Program.empty
  let p1 := p0.gate ⟨FullOp.con false, Fin.elim0⟩
  let p2 := p1.gate ⟨FullOp.con true, Fin.elim0⟩
  let p3 := p2.gate ⟨FullOp.fn fun _ => true, fun _ => Wire.input ⟨0, by decide⟩⟩
  let p4 := p3.gate ⟨FullOp.fn fun xs => !xs 0, fun _ => Wire.input ⟨0, by decide⟩⟩
  let p5 := p4.gate ⟨FullOp.fn fun xs => xs 1, fun _ => Wire.gate ⟨3, by decide⟩⟩
  let p6 := p5.gate ⟨FullOp.fn fun xs => !xs 1, fun _ => Wire.gate ⟨4, by decide⟩⟩
  let p7 := p6.gate ⟨FullOp.fn fun xs => xs 0, fun _ => Wire.gate ⟨5, by decide⟩⟩
  let p8 := p7.gate ⟨FullOp.fn fun xs => !xs 0, fun _ => Wire.gate ⟨6, by decide⟩⟩
  ⟨p8, fun _ => Wire.gate ⟨7, by decide⟩⟩

example : bloatedUnary4Circuit.size = 8 ∧
    bloatedUnary4Circuit.program.cost binaryB2Cost = 0 ∧
    (∃ g : BitString 1 → BitString 4, IsAffine g ∧ Function.Injective g ∧
      ∃ b : Bool, ∀ u, bloatedUnary4Circuit.eval fullInterpretation (g u) 0 = b) :=
  ⟨rfl, by decide, exists_affine_subspace_const_of_cost_lt bloatedUnary4Circuit (by decide)⟩

/-- A `0`-gate circuit on `4` bits has `size + 9 * 1 < 4 * 4`, so it is constant on some
`1`-dimensional injective affine subspace. -/
private def proj4Circuit : Circuit (fullSignature 2 Bool) 4 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

example : ∃ g : BitString 1 → BitString 4, IsAffine g ∧ Function.Injective g ∧
    ∃ b : Bool, ∀ u, proj4Circuit.eval fullInterpretation (g u) 0 = b :=
  exists_affine_subspace_const_of_size_lt proj4Circuit (by decide)

/-- A `0`-gate circuit on `100` bits has `size + 9 * 11 < 4 * 100`, so it disagrees on some input
with a genuine `11`-affine disperser obtained from `exists_isAffineDisperser`. -/
private def proj100Circuit : Circuit (fullSignature 2 Bool) 100 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

example : ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
    ∃ x : BitString 100, proj100Circuit.eval fullInterpretation x 0 ≠ f x := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨f, hf, exists_disagreeing_input_of_size_lt hf proj100Circuit (by decide)⟩

/-- Non-vacuous numerical consequence at `n = 100, d = 11`: any circuit computing a genuine
`11`-affine disperser on `100` bits requires at least `301` genuinely binary `B₂` gates (whereas
`3.5n - 7d` gives `273` and `4n - 10d` gives `290`). -/
example : ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
    ∀ C : Circuit (fullSignature 2 Bool) 100 1, C.Computes fullInterpretation (single f) →
      301 ≤ C.program.cost binaryB2Cost ∧ 301 ≤ C.size := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  refine ⟨f, hf, fun C hC => ?_⟩
  have hcost := four_mul_le_cost_add hf C hC
  have hsize := four_mul_le_size_add hf C hC
  omega

/-- Exercise `(PC)` (`addPair`) on an initial state of `and2Circuit`: pairing `(0, false, 1, false)`
preserves validity and lowers potential by `7`. -/
example :
    let S := initialState and2Circuit
    let pr : ZeroPair := ⟨0, false, 1, false⟩
    S.AddPairOK pr ∧ (S.addPair pr).Valid and2Fn ∧ (S.addPair pr).a + 1 = S.a := by
  have hcomp : and2Circuit.Computes fullInterpretation (single and2Fn) := by
    intro x; ext i; rw [Fin.eq_zero i]; rfl
  have hS : (initialState and2Circuit).Valid and2Fn := initialState_valid hcomp
  have hok : (initialState and2Circuit).AddPairOK ⟨0, false, 1, false⟩ :=
    ⟨by simp [AffineDisperserCore.State.unpaired, AffineDisperserCore.State.Paired, initialState,
          ofCircuitBinary_params],
      by simp [AffineDisperserCore.State.unpaired, AffineDisperserCore.State.Paired, initialState,
          ofCircuitBinary_params],
      by decide⟩
  refine ⟨hok, State.Valid.addPair hS hok, ?_⟩
  have hq := AffineDisperserCore.State.addPair_q hok
  have hm : ((initialState and2Circuit).addPair ⟨0, false, 1, false⟩).m =
      (initialState and2Circuit).m := by
    simp [AffineDisperserCore.State.m, AffineDisperserCore.State.addPair_params]
  have hqm := hS.q_le_m
  have hqm' := (State.Valid.addPair hS hok).q_le_m
  unfold AffineDisperserCore.State.a at *
  omega

end CslibFrontierTests.AffineDisperser4n
