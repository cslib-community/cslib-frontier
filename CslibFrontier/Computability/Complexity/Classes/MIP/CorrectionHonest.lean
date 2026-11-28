/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.MIP.Correction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# An honest static table for line correction

For each point and direction of a multilinear assignment, the prover stores one padded
coefficient word at the tagged correction key. The remaining proof addresses can carry
other parts of the verifier's proof.

## Main results

* `extendCorrectionTable` stores the coefficients at all the canonical correction keys.
* `correctionAnswer_extendCorrectionTable` proves that every direction yields the value
  of the prescribed assignment, including the zero direction.
-/

public section

namespace Cslib.Complexity.MIP

open Polynomial (evalCoeffListMod_lt_modulus)

open Cslib.Code Turing.MultiTapeTM QBFProtocol

private def lineKey {n p : ℕ} (z : (Fin n → ZMod p) × (Fin n → ZMod p)) : List Bool :=
  correctionKey (List.ofFn fun i => (z.1 i).val) (List.ofFn fun i => (z.2 i).val)

private theorem lineKey_injective {n p : ℕ} [NeZero p] :
    Function.Injective (lineKey (n := n) (p := p)) := by
  have coords : Function.Injective (fun x : Fin n → ZMod p => List.ofFn fun i => (x i).val) := by
    intro x y h
    exact funext fun i => ZMod.val_injective p (congrFun (List.ofFn_injective h) i)
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  simp only [lineKey, correctionKey, List.cons.injEq, true_and] at h
  obtain ⟨hx, hv⟩ := Prod.mk.inj ((encPair (encList encUnary) (encList encUnary)).injective h)
  exact Prod.ext (coords hx) (coords hv)

private noncomputable def replyWord {p n : ℕ} [Fact p.Prime] {f : (Fin n → ZMod p) → ZMod p}
    (hf : IsMultilinear f) (x v : Fin n → ZMod p) : List Bool :=
  List.ofFn (BitString.ofList (replyLimit p n) (Classical.choose (exists_checkLineReply hf x v)))

private theorem decodeReply_replyWord {p n : ℕ} [Fact p.Prime] {f : (Fin n → ZMod p) → ZMod p}
    (hf : IsMultilinear f) (x v : Fin n → ZMod p) :
    decodeReply p n (replyWord hf x v) =
      decodeReply p n (Classical.choose (exists_checkLineReply hf x v)) := by
  simp only [decodeReply, replyWord, replyLimit, BitString.listRows_eq_ofFn, BitString.ofList_ofFn]

/-- A single natural-valued table stores an honest coefficient word for every canonical
point–direction pair, with precisely the verifier's reply width. Other keys keep the
background table. -/
noncomputable def extendCorrectionTable {p n : ℕ} [Fact p.Prime] {f : (Fin n → ZMod p) → ZMod p}
    (hf : IsMultilinear f) (other : List Bool → ℕ) : List Bool → ℕ :=
  Function.extend (lineKey (n := n) (p := p)) (fun z => ofBits (replyWord hf z.1 z.2)) other

/-- The correction table leaves all keys outside the `111` prefix available to the other
oracle checks. -/
theorem extendCorrectionTable_of_take_ne {p n : ℕ} [Fact p.Prime]
    {f : (Fin n → ZMod p) → ZMod p} (hf : IsMultilinear f) (other : List Bool → ℕ)
    {key : List Bool} (h : key.take 3 ≠ [true, true, true]) :
    extendCorrectionTable hf other key = other key := by
  apply Function.extend_apply'
  rintro ⟨z, rfl⟩
  exact h rfl

/-- On an honest point table, representing the correction table at its own keys and width
makes every deterministic line check return the value at the requested point. -/
theorem correctionAnswer_extendCorrectionTable {p n : ℕ} [Fact p.Prime]
    {f : (Fin n → ZMod p) → ZMod p} (hf : IsMultilinear f)
    (other : List Bool → ℕ) (π : List Bool → Bool) (hpoint : proofPoint π p = f)
    (hπ : ∀ key : List Bool, key.take 3 = [true, true, true] →
      ProofWord.value π key (replyLimit p n) =
        extendCorrectionTable hf other key % 2 ^ replyLimit p n)
    (x v : Fin n → ZMod p) : correctionAnswer π x v = some (f x).val := by
  have hlen : (replyWord hf x v).length = replyLimit p n := List.length_ofFn
  have small : ofBits (replyWord hf x v) < 2 ^ replyLimit p n :=
    hlen ▸ ofBits_lt_two_pow (replyWord hf x v)
  have hval := hπ (lineKey (x, v)) rfl
  rw [extendCorrectionTable, lineKey_injective.extend_apply, Nat.mod_eq_of_lt small] at hval
  have hword : correctionReply π x v = replyWord hf x v :=
    ofBits_injective_of_length_eq (List.length_ofFn.trans hlen.symm) hval
  obtain ⟨_, hcheck, heval⟩ := Classical.choose_spec (exists_checkLineReply hf x v)
  have replace {a b : List Bool} (h : decodeReply p n a = decodeReply p n b) (reads : List ℕ) :
      checkLineReply p n a reads = checkLineReply p n b reads := by
    rw [checkLineReply, checkLineReply, h]
  rw [correctionAnswer, hword, hpoint]
  dsimp only
  rw [replace (decodeReply_replyWord hf x v), ite_eq_left hcheck, decodeReply_replyWord]
  exact congrArg some ((ZMod.val_natCast_of_lt (evalCoeffListMod_lt_modulus _ _)).symm.trans
    (congrArg ZMod.val heval))

end Cslib.Complexity.MIP
