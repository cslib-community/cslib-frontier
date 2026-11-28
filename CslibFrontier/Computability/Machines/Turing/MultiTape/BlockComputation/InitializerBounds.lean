/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.InitializerCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Space for streamed runtime initialization

Every allocation clock retains one metadata record, a prefix of the padded bank and the
growing assignment capacity. A uniform bound is linear in the number of field cells and
their binary width, including the capacity accumulated by repeated multiplication.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Initializer

open MultiTapeTM
open Cslib.TreeEval.Ary.Packed

/-- Metadata plus a constant number of bank-width allocations pays every initializer state. -/
@[expose] noncomputable def space (k : ℕ) (metadata : Metadata) : ℕ :=
  let (_, (_, _, alphabet, p)) := metadata
  16 * ((encMetadata metadata).length + 1) +
    16 * bankCells k metadata * ((encNat p).length + (encNat alphabet).length + 1)

/-- The power accumulator and allocated list fit the same bank-width budget at every prefix. -/
theorem prefixState_encoding_le (k : ℕ) (metadata : Metadata) (j : ℕ)
    (hj : j ≤ bankCells k metadata) :
    (encState (prefixState k metadata j)).length ≤ space k metadata := by
  rcases metadata with ⟨args, m, r, alphabet, p⟩
  dsimp only [bankCells] at hj
  have hcursor := length_encNat_le_self j
  have hlist := length_encList_le encNat (List.replicate j p) (b := (encNat p).length)
    (fun _ h => List.eq_of_mem_replicate h ▸ le_rfl)
  simp only [List.length_replicate] at hlist
  have hbank := hlist.trans (Nat.mul_le_mul_right (2 * (encNat p).length + 1) hj)
  have hpower := Nat.size_pow_le alphabet (min j ((k * 3 + 1) * r))
  have hmul := Nat.mul_le_mul_right alphabet.size
    ((Nat.min_le_left j ((k * 3 + 1) * r)).trans hj)
  simp only [prefixState, encState, length_encPair, space, bankCells,
    length_encNat_eq_size]
  simp only [length_encNat_eq_size] at hcursor hbank
  nlinarith

/-- Every physical clock obeys one explicit state bound: the machine halts at the last allocation
clock and stays put afterwards. -/
theorem length_runFrom_le (k : ℕ) (metadata : Metadata) (w : List Bool) (j : ℕ) :
    (encState ((machine k).runFrom w (metadata, 0, [], 1) j)).length ≤ space k metadata := by
  by_cases hj : j ≤ bankCells k metadata
  · rw [runFrom_prefix k metadata w j hj]
    exact prefixState_encoding_le k metadata j hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (by omega : bankCells k metadata ≤ j)
  have hfix {s} (hs : (machine k).halted s = true) : (machine k).runFrom w s n = s :=
    Function.iterate_fixed (by simp [QueryMachine.step, hs]) n
  rcases metadata with ⟨args, m, r, alphabet, p⟩
  rw [QueryMachine.runFrom_add]
  dsimp only [bankCells]
  rw [hfix (halted_complete k args m r alphabet p w),
    runFrom_prefix k (args, m, r, alphabet, p) w ((k * 3 + 1 + 1) * r) le_rfl]
  exact prefixState_encoding_le _ _ _ le_rfl

/-- In particular, the runtime-selected initialization has a bound at every clock. -/
theorem length_runFrom_prepare_le (k s : ℕ) (args : Args) (w : List Bool) (j : ℕ) :
    (encState ((machine k).runFrom w (prepare k s args) j)).length ≤
      space k ((prepare k s args).1) :=
  length_runFrom_le k ((prepare k s args).1) w j

/-- Selected initialization uses linear value-width storage, apart from its retained metadata. -/
theorem space_prepare_le (k s N b σ q : ℕ) :
    let d := k * 3 + 1
    let B := Encoding.width k s b
    space k ((prepare k s (N, b, σ, q)).1) ≤
      16 * ((encMetadata ((prepare k s (N, b, σ, q)).1)).length + 1) +
        192 * (d + 1) * (2 * B + d.size) := by
  intro d B
  have htotal := Nat.mul_le_mul_left (16 * (d + 1))
    (chunkCount_mul_parameter_sizes_le (by omega : 0 < d) (Encoding.width_pos k s b))
  have hm := chunkWidth_le d B
  have hfinal := Nat.mul_le_mul_left (192 * (d + 1))
    (by omega : B + chunkWidth d B ≤ 2 * B + d.size)
  simp only [space, prepare, parameters, bankCells, length_encNat_eq_size]
  dsimp only [d, B] at htotal hfinal ⊢
  nlinarith

end Turing.MultiTapePTM.BlockComputation.Initializer
