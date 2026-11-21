/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Streaming
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Native read-only seed accumulation

Read a seed word in index order. A code-bit function of the retained context and the index
masks each bit before the shared base-six update. The first absent bit halts the scan. The
resource certificate assumes a native linear-space code-bit function on the encoded context
and binary index.
-/

public section

namespace Cslib.Reachability.Hoza.SeedDigits

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- The code context and the registers for a single read-only seed scan. -/
structure State (κ : Type) where
  /-- Retained parameters of the code-bit calculation. -/
  context : κ
  /-- The index of the next seed bit. -/
  cursor : ℕ
  /-- The base-six value of the masked prefix. -/
  accumulator : ℕ
  /-- Whether the input end was reached. -/
  done : Bool

/-- Framed context, binary index and binary accumulator, followed by the unframed end flag. -/
enc_structure encState (κ : Type) (encContext : κ ↪ List Bool) : State κ where
  context : encContext, cursor : encNat, accumulator : encNat, done : encBool

variable {κ : Type}

private theorem maskedPrefix_succ (code : ℕ → Bool) (seed : List Bool) (t : ℕ) :
    maskedPrefix code seed (t + 1) =
      appendWeightDigit (maskedPrefix code seed t) (code t && (seed[t]?).getD false) := by
  simp only [maskedPrefix, accumulateWeightDigits_succ,
    Fin.val_castSucc, Fin.val_last]

/-- Scan the seed from index zero and return the accumulated binary weight at the first
absent input bit. -/
@[expose] def machine (code : κ → ℕ → Bool) (context : κ) : QueryMachine (State κ) where
  init := ⟨context, 0, 0, false⟩
  query := State.cursor
  next p := match p.2 with
    | some bit =>
      ⟨p.1.context, p.1.cursor + 1,
        appendWeightDigit p.1.accumulator (code p.1.context p.1.cursor && bit), false⟩
    | none => {p.1 with done := true}
  emit _ := []
  halted := State.done
  finish s := encNat s.accumulator

/-- A prefix of present bits leaves the scan live and returns its exact base-six value. -/
theorem run_prefix (code : κ → ℕ → Bool) (context : κ) (seed : List Bool) (t : ℕ)
    (ht : t ≤ seed.length) :
    (machine code context).run seed t =
      ⟨context, t, maskedPrefix (code context) seed t, false⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < seed.length := by omega
    rw [QueryMachine.run_succ, ih hlt.le, maskedPrefix_succ]
    simp [QueryMachine.step, QueryMachine.read, machine, List.getElem?_eq_getElem hlt]

/-- Reading the first missing bit halts and retains the value of the complete seed. -/
theorem run_at_end (code : κ → ℕ → Bool) (context : κ) (seed : List Bool) :
    (machine code context).run seed (seed.length + 1) =
      ⟨context, seed.length, maskedPrefix (code context) seed seed.length, true⟩ := by
  rw [QueryMachine.run_succ, run_prefix code context seed _ le_rfl]
  simp [QueryMachine.step, QueryMachine.read, machine]

private theorem length_maskedPrefix_le (code : ℕ → Bool) (seed : List Bool) (t : ℕ) :
    (encNat (maskedPrefix code seed t)).length ≤ 3 * t := by
  rw [length_encNat_eq_size]
  exact size_accumulateWeightDigits_le _

private theorem length_prefix_state (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (context : κ) (seed : List Bool) (t : ℕ) (done : Bool) (ht : t ≤ seed.length) :
    (encState κ encContext ⟨context, t, maskedPrefix (code context) seed t, done⟩).length ≤
      2 * (encContext context).length + 8 * seed.length + 4 := by
  have hcur : (encNat t).length ≤ t := length_encNat_eq_size t ▸ Nat.size_le_self t
  have hacc := length_maskedPrefix_le (code context) seed t
  simp only [encState_apply, encStateFields, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- The retained code context and both numeric registers fit the stated bound at every clock. -/
theorem length_run_le (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (context : κ) (seed : List Bool) (t : ℕ) :
    (encState κ encContext ((machine code context).run seed t)).length ≤
      2 * (encContext context).length + 8 * seed.length + 4 := by
  by_cases ht : t ≤ seed.length
  · rw [run_prefix code context seed t ht]
    exact length_prefix_state encContext code context seed t false ht
  · have hstop : (machine code context).halted
        ((machine code context).run seed (seed.length + 1)) = true := by
      rw [run_at_end]
      rfl
    rw [(machine code context).run_eq_of_le seed hstop (by omega), run_at_end]
    exact length_prefix_state encContext code context seed seed.length true le_rfl

/-- The five scan components have native linear-space certificates given a binary-indexed
code-bit certificate on the retained context. -/
theorem parts_inSpace (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool) (context : κ)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length)) :
    let M := machine code context
    let e := encState κ encContext
    let eR := QueryMachine.encStateRead e
    ComputableInSpace M.query e encNat (fun s => (e s).length) ∧
    ComputableInSpace M.next eR e (fun p => (eR p).length) ∧
    ComputableInSpace M.emit eR encBits (fun p => (eR p).length) ∧
    ComputableInSpace M.halted e encBool (fun s => (e s).length) ∧
    ComputableInSpace M.finish e encBits (fun s => (e s).length) := by
  let e := encState κ encContext
  have hid := budget_id (BigOLe.refl fun s => (e s).length)
  have hstate := fst e (encOption encBool)
  have hread := snd e (encOption encBool)
  have hin := BigOLe.refl fun p => (QueryMachine.encStateRead e p).length
  have hcontext := encState_context_budget κ encContext hstate
  have hcursor := encState_cursor_budget κ encContext hstate
  have hacc := encState_accumulator_budget κ encContext hstate
  have hcode := budget_comp_linear hc (budget_prod hcontext hcursor)
  have hmasked := budget_boolAnd hcode (budget_optionGetD false hread)
  have hdigit := budget_finite (encC := encNat) Bool.toNat hmasked
  have hnew := budget_natAdd (budget_natMul (budget_const 6 hin) hacc) hdigit
  have hsome := budget_finite (encC := encBool) Option.isSome hread
  have hnext := budget_ite hsome
    (encState_mk_budget κ encContext hcontext (budget_natSucc hcursor) hnew
      (budget_const false hin))
    (encState_mk_budget κ encContext hcontext hcursor hacc (budget_const true hin))
  refine ⟨encState_cursor_budget κ encContext hid, hnext.of_enc_eq ?_, budget_const [] hin,
    encState_done_budget κ encContext hid,
    (encState_accumulator_budget κ encContext hid).of_enc_eq (fun _ => rfl)⟩
  rintro ⟨s, b⟩
  cases b <;> rfl

/-- For a fixed initial code context, accumulate a raw seed word in native linear space.
The uniform code-bit certificate is used at every read. -/
theorem maskedSeed_inSpace (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool) (context : κ)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length)) :
    ComputableInSpace (fun seed => maskedPrefix (code context) seed seed.length)
      encBits encNat List.length := by
  let M := machine code context
  obtain ⟨hq, hn, he, hh, hf⟩ := parts_inSpace encContext code context hc
  have hstop (seed : List Bool) : M.halted (M.run seed (seed.length + 1)) = true := by
    dsimp only [M]
    rw [run_at_end]
    rfl
  have hlive (seed : List Bool) (t : ℕ) (ht : t < seed.length + 1) :
      M.halted (M.run seed t) = false := by
    dsimp only [M]
    rw [run_prefix code context seed t (by omega)]
    rfl
  have hout (seed : List Bool) :
      encNat (maskedPrefix (code context) seed seed.length) = M.output seed (seed.length + 1) := by
    rw [M.output_eq_of_not_halted seed (hlive seed)]
    have hend : M.run seed (seed.length + 1) =
        ⟨context, seed.length, maskedPrefix (code context) seed seed.length, true⟩ :=
      run_at_end code context seed
    rw [hend]
    simp [M, machine]
  have hlog (seed : List Bool) : Nat.log2 (encBits seed).length + 1 ≤ seed.length + 1 := by
    rw [encBits_apply]
    exact Nat.add_le_add_right
      ((Nat.log2_le_size seed.length).trans (Nat.size_le_self seed.length)) _
  have hsize : ∃ C, ∀ (seed : List Bool) t, t ≤ seed.length + 1 →
      (encState κ encContext (M.run (encBits seed) t)).length ≤ C * (seed.length + 1) := by
    refine ⟨2 * (encContext context).length + 8, fun seed t _ => ?_⟩
    rw [encBits_apply]
    exact (length_run_le encContext code context seed t).trans (by nlinarith)
  obtain ⟨time, c, hnativ⟩ := QueryMachine.computableInSpace
    (enc := encBits) (encOut := encNat)
    (f := fun seed => maskedPrefix (code context) seed seed.length)
    M hq hn he hh hf (fun seed => seed.length + 1) hstop hlive hout
    (fun seed => seed.length + 1) hlog hsize
  refine ⟨time, c + 3, hnativ.mono (fun _ => le_rfl) ?_, fun seed => ?_⟩
  · exact fun seed => Nat.mul_le_mul_right (seed.length + 1) (Nat.le_add_right _ _)
  · exact (length_maskedPrefix_le (code context) seed seed.length).trans (by nlinarith)

end Cslib.Reachability.Hoza.SeedDigits
