/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Offset

/-! # Ordinary-import runtime query-offset clients -/
public section
namespace Turing.QueryMachine.OffsetTests
open MultiTapeTM ComputableInSpace

-- One real optional read: true halts, false or absent input leaves the machine live.
private def reader : QueryMachine Bool where
  init := false
  query _ := 0
  next p := p.2.getD false
  emit _ := []
  halted b := b
  finish b := [b]

-- The shared encoding keeps the formerly application-local words unchanged.
theorem encoded_words_unchanged (q : Located Bool) :
    encLocated Bool encBool q = encPair encNat encBool (q.offset, q.inner) := rfl

example : reader.withOffset.runFrom [false, true] ⟨1, false⟩ 7 = ⟨1, true⟩ := by rfl
example : reader.withOffset.runFrom [true] ⟨3, false⟩ 7 = ⟨3, false⟩ := by rfl
example : reader.withOffset.runFrom [] ⟨3, true⟩ 7 = ⟨3, true⟩ := by rfl

private theorem next_space : ComputableInSpace reader.next (encStateRead encBool) encBool
    (fun p => (encStateRead encBool p).length) :=
  (budget_optionGetD false (snd encBool (encOption encBool))).of_enc_eq fun _ => rfl

example : ComputableInSpace reader.withOffset.query (encLocated Bool encBool) encNat
    (fun q => (encLocated Bool encBool q).length) :=
  reader.withOffset_query_inSpace encBool (budget_const 0 (.refl _))

example : ComputableInSpace reader.withOffset.next (encStateRead (encLocated Bool encBool))
    (encLocated Bool encBool) (fun p => (encStateRead (encLocated Bool encBool) p).length) :=
  reader.withOffset_next_inSpace encBool next_space

example : ComputableInSpace reader.withOffset.emit (encStateRead (encLocated Bool encBool))
    encBits (fun p => (encStateRead (encLocated Bool encBool) p).length) :=
  reader.withOffset_emit_inSpace encBool (budget_const [] (.refl _))

example : ComputableInSpace reader.withOffset.halted (encLocated Bool encBool) encBool
    (fun q => (encLocated Bool encBool q).length) :=
  reader.withOffset_halted_inSpace encBool
    (of_inO (ComputableInDegree.id' (enc := encBool)).inO_one)

example : ComputableInSpace reader.withOffset.finish (encLocated Bool encBool) encBits
    (fun q => (encLocated Bool encBool q).length) :=
  reader.withOffset_finish_inSpace encBool
    ((of_inO (ComputableInDegree.id' (enc := encBool)).inO_one).of_enc_eq fun _ => rfl)

-- Every clock, including clocks after halting, retains the explicit binary offset.
example (word : List Bool) (offset T : ℕ) : ∀ t ≤ T,
    (encLocated Bool encBool (reader.withOffset.runFrom word ⟨offset, false⟩ t)).length ≤
      2 * (encNat offset).length + 1 + 1 :=
  reader.withOffset_runFrom_encoding_le encBool word offset false 1 T (fun _ _ => by
    simp only [encBool_apply, List.length_singleton, Nat.le_refl])

end Turing.QueryMachine.OffsetTests
