/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Query machines with a runtime input offset

`withOffset` retains a binary offset alongside the complete supplied machine state and adds it
only to input queries. The other components delegate unchanged. `withOffset_runFrom` proves
agreement at every clock with the original machine on `word.drop offset`, including absent reads
when the offset or query is past the end of the word. No prefix, suffix or transcript is stored.

The five native component certificates preserve a supplied linear encoded-state workspace
contract. `withOffset_runFrom_encoding_le` charges the framed binary offset in addition to the
complete inner-state bound; that bound must include any suspended caller/callee context.
These are original operational/component facts, not a native initializer/executor composition.
A native execution compiler must separately charge its original-input position and supply its
initialization, halting and physical callee resource contracts. Time is not bounded by space here.
-/

public section
namespace Turing.QueryMachine
open MultiTapeTM ComputableInSpace

/-- A runtime input offset and the complete active or suspended machine state. -/
structure Located (σ : Type) where
  /-- First cell of the logical input within the original word. -/
  offset : ℕ
  /-- Complete state of the supplied machine. -/
  inner : σ

/-- Framed binary offset followed by the supplied state word, with no additional framing. -/
enc_structure encLocated (σ : Type) (encS : σ ↪ List Bool) : Located σ where
  offset : encNat, inner : encS

/-- Exact charge for retaining a binary offset with a complete supplied state. -/
theorem length_encLocated {σ : Type} (encS : σ ↪ List Bool) (s : Located σ) :
    (encLocated σ encS s).length = 2 * (encNat s.offset).length + 1 + (encS s.inner).length := by
  simp only [encLocated_apply, encLocatedFields, length_encPair]

/-- Relocate queries using a runtime offset, delegating all remaining components unchanged.
The default initial offset is zero; a caller can supply a located runtime state with `runFrom`. -/
@[expose] def withOffset {σ : Type} (M : QueryMachine σ) : QueryMachine (Located σ) where
  init := ⟨0, M.init⟩
  query q := q.offset + M.query q.inner
  next p := ⟨p.1.offset, M.next (p.1.inner, p.2)⟩
  emit p := M.emit (p.1.inner, p.2)
  halted q := M.halted q.inner
  finish q := M.finish q.inner

/-- Exact all-clock dropped-word simulation, including halted and out-of-range states. -/
theorem withOffset_runFrom {σ : Type} (M : QueryMachine σ) (word : List Bool)
    (offset : ℕ) (start : σ) (t : ℕ) :
    M.withOffset.runFrom word ⟨offset, start⟩ t =
      ⟨offset, M.runFrom (word.drop offset) start t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ, ih, runFrom_succ]
    unfold step read
    simp only [withOffset, List.getElem?_drop]
    split <;> rename_i h <;> simp [h]

private theorem inner_inSpace {σ : Type} (encS : σ ↪ List Bool) :
    ComputableInSpace (Located.inner (σ := σ)) (encLocated σ encS) encS
      (fun q => (encLocated σ encS q).length) :=
  encLocated_inner_budget σ encS
    (of_inO (ComputableInDegree.id' (enc := encLocated σ encS)).inO_one)

private theorem innerRead_inSpace {σ : Type} (encS : σ ↪ List Bool) :
    ComputableInSpace (fun p : Located σ × Option Bool => (p.1.inner, p.2))
      (encStateRead (encLocated σ encS)) (encStateRead encS)
      (fun p => (encStateRead (encLocated σ encS) p).length) :=
  budget_prod (budget_comp_linear (inner_inSpace encS)
    (fst (encLocated σ encS) (encOption encBool)))
    (snd (encLocated σ encS) (encOption encBool))

/-- Native query dispatch charges addition of the retained binary offset. -/
theorem withOffset_query_inSpace {σ : Type} (M : QueryMachine σ) (encS : σ ↪ List Bool)
    (hq : ComputableInSpace M.query encS encNat (fun s => (encS s).length)) :
    ComputableInSpace M.withOffset.query (encLocated σ encS) encNat
      (fun q => (encLocated σ encS q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encLocated σ encS)).inO_one
  exact (budget_natAdd (encLocated_offset_budget σ encS hid)
    (budget_comp_linear hq (inner_inSpace encS))).of_enc_eq fun _ => rfl

/-- Native transition dispatch retains the offset and applies the supplied transition once. -/
theorem withOffset_next_inSpace {σ : Type} (M : QueryMachine σ) (encS : σ ↪ List Bool)
    (hn : ComputableInSpace M.next (encStateRead encS) encS
      (fun p => (encStateRead encS p).length)) :
    ComputableInSpace M.withOffset.next (encStateRead (encLocated σ encS))
      (encLocated σ encS) (fun p => (encStateRead (encLocated σ encS) p).length) := by
  exact (encLocated_mk_budget σ encS
    (encLocated_offset_budget σ encS (fst (encLocated σ encS) (encOption encBool)))
    (budget_comp_linear hn (innerRead_inSpace encS))).of_enc_eq fun _ => rfl

/-- Native emissions use the supplied component on the unchanged inner state and reply. -/
theorem withOffset_emit_inSpace {σ : Type} (M : QueryMachine σ) (encS : σ ↪ List Bool)
    (he : ComputableInSpace M.emit (encStateRead encS) encBits
      (fun p => (encStateRead encS p).length)) :
    ComputableInSpace M.withOffset.emit (encStateRead (encLocated σ encS)) encBits
      (fun p => (encStateRead (encLocated σ encS) p).length) :=
  (budget_comp_linear he (innerRead_inSpace encS)).of_enc_eq fun _ => rfl

/-- Native halting dispatch tests the unchanged inner state. -/
theorem withOffset_halted_inSpace {σ : Type} (M : QueryMachine σ) (encS : σ ↪ List Bool)
    (hh : ComputableInSpace M.halted encS encBool (fun s => (encS s).length)) :
    ComputableInSpace M.withOffset.halted (encLocated σ encS) encBool
      (fun q => (encLocated σ encS q).length) :=
  (budget_comp_linear hh (inner_inSpace encS)).of_enc_eq fun _ => rfl

/-- Native final-output dispatch uses the unchanged supplied final-output component. -/
theorem withOffset_finish_inSpace {σ : Type} (M : QueryMachine σ) (encS : σ ↪ List Bool)
    (hf : ComputableInSpace M.finish encS encBits (fun s => (encS s).length)) :
    ComputableInSpace M.withOffset.finish (encLocated σ encS) encBits
      (fun q => (encLocated σ encS q).length) :=
  (budget_comp_linear hf (inner_inSpace encS)).of_enc_eq fun _ => rfl

/-- Every clock charges the framed binary offset in addition to the supplied complete state
bound. The inner bound must already include any suspended caller and callee. -/
theorem withOffset_runFrom_encoding_le {σ : Type} (M : QueryMachine σ)
    (encS : σ ↪ List Bool) (word : List Bool) (offset : ℕ) (start : σ) (B T : ℕ)
    (h : ∀ t ≤ T, (encS (M.runFrom (word.drop offset) start t)).length ≤ B) :
    ∀ t ≤ T, (encLocated σ encS (M.withOffset.runFrom word ⟨offset, start⟩ t)).length ≤
      2 * (encNat offset).length + 1 + B := by
  intro t ht
  rw [withOffset_runFrom, length_encLocated]
  exact Nat.add_le_add_left (h t ht) _

end Turing.QueryMachine
