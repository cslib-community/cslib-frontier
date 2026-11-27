/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Words
public import CslibFrontier.Foundations.Data.Code.Multilinearity
public import CslibFrontier.Foundations.Data.Code.SelfCorrection
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Checking a proof oracle's value at an arbitrary field point

At a point `x`, the prover gives coefficients for the polynomial on a line through `x`.
The verifier compares evaluations at the nonzero nodes `1, …, n + 1` with the oracle.
The modulus and dimension are in unary. Coefficients use the fixed-width binary residue
words of `QBFProtocol.decodeReply`.

## Main definitions

* `Cslib.Complexity.MIP.checkLineReply` tests the supplied polynomial at consecutive nonzero nodes.

## Main results

* `Cslib.Complexity.MIP.computableInPolyTime_checkLineReply` bounds the running time.
* `Cslib.Complexity.MIP.exists_checkLineReply` supplies honest replies along every direction.
* `Cslib.Complexity.MIP.card_checkLineReply_wrong_le` bounds the number of directions on
  which an arbitrary reply passes and gives the wrong value at the point.
-/

@[expose] public section

namespace Cslib.Complexity.MIP

open Cslib.Code Cslib.BitString Turing.MultiTapeTM QBFProtocol Finset
open scoped Polynomial

/-- Check a degree-`n` coefficient reply against the oracle values at nodes `1, …, n + 1`
in that order. Missing coefficients and oracle values are zero-padded. -/
def checkLineReply (p n : ℕ) (reply : List Bool) (reads : List ℕ) : Bool :=
  (List.range (n + 1)).all fun i =>
    decide (hornerMod p (i + 1) (decodeReply p n reply) = reads.getD i 0)

/-- Checking all the line samples is polynomial-time for unary dimension, modulus and samples. -/
@[fun_prop] theorem computableInPolyTime_checkLineReply {α : Type} {enc : α ↪ List Bool}
    {p n : α → ℕ} {reply : α → List Bool} {reads : α → List ℕ}
    (hp : ComputableInPolyTime p enc encUnary) (hn : ComputableInPolyTime n enc encUnary)
    (hr : ComputableInPolyTime reply enc encBits)
    (hw : ComputableInPolyTime reads enc (encList encUnary)) :
    ComputableInPolyTime (fun a => checkLineReply (p a) (n a) (reply a) (reads a)) enc encBool := by
  unfold checkLineReply
  apply ComputableInPolyTime.allWithInput
    (ComputableInPolyTime.range.comp (hn.unary_add' (.const 1)))
  have hpar := ComputableInPolyTime.fst enc encUnary
  have hidx := ComputableInPolyTime.snd enc encUnary
  exact (computableInPolyTime_hornerMod (hp.comp hpar) (hidx.unary_add' (.const 1))
    ((computableInPolyTime_decodeReply hp hn hr).comp hpar)).decide_eq'
      (ComputableInPolyTime.listGetDWithInput (hw.comp hpar) hidx 0)

private def node {n p : ℕ} [Fact p.Prime] (hp : n + 1 < p) : Fin (n + 1) ↪ ZMod p where
  toFun i := ((i.val + 1 : ℕ) : ZMod p)
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega : i.val + 1 < p),
      ZMod.val_natCast_of_lt (by omega : j.val + 1 < p)] at hh
    omega

private noncomputable def linePolynomial (p n : ℕ) (reply : List Bool) : Polynomial (ZMod p) :=
  Polynomial.ofCoeffList ((decodeReply p n reply).map Nat.cast)

private theorem eval_linePolynomial {p : ℕ} [NeZero p] (n z : ℕ) (reply : List Bool) :
    (linePolynomial p n reply).eval (z : ZMod p) =
      (hornerMod p z (decodeReply p n reply) : ZMod p) := by
  rw [linePolynomial, Polynomial.eval_ofCoeffList, natCast_hornerMod]

private theorem mem_reedMuller_of_multilinear {F : Type*} [Field F] {n : ℕ}
    {f : (Fin n → F) → F} (hf : IsMultilinear f) : f ∈ reedMuller F n n := by
  rw [isMultilinear_iff_eq_eval_multilinearExtension.mp hf]
  apply eval_mem_reedMuller
  simpa using totalDegree_multilinearExtension_le (R := F) (fun b => f (bitPoint b))

private theorem exists_linePolynomial {p n : ℕ} [Fact p.Prime] (P : Polynomial (ZMod p))
    (hP : P.natDegree ≤ n) : ∃ reply, linePolynomial p n reply = P := by
  let vals := (P.coeffsBelow (n + 1)).map ZMod.val
  have hlen : vals.length = n + 1 := by simp [vals]
  have hval (a : ℕ) (ha : a ∈ vals) : a < p := by
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
    exact ZMod.val_lt z
  refine ⟨(encodeReply p vals).take (replyLimit p n), ?_⟩
  rw [linePolynomial, decodeReply_encodeReply hval hlen.le, List.map_range_eq_ofFn,
    List.ofFn_getD_eq_of_length 0 hlen]
  simpa [vals, List.map_map, Function.comp_def] using
    (Polynomial.ofCoeffList_coeffsBelow (P := P) (by omega : P.natDegree < n + 1))

/-- An honest oracle has a bounded-degree reply along every direction, including the zero
direction. The reply passes every check and gives the prescribed value at zero. -/
theorem exists_checkLineReply {p n : ℕ} [Fact p.Prime] {f : (Fin n → ZMod p) → ZMod p}
    (hf : IsMultilinear f) (x v : Fin n → ZMod p) :
    ∃ reply, checkLineReply p n reply (List.ofFn fun i : Fin (n + 1) =>
        (f (x + ((i.val + 1 : ℕ) : ZMod p) • v)).val) = true ∧
      (hornerMod p 0 (decodeReply p n reply) : ZMod p) = f x := by
  obtain ⟨P, hdeg, hP⟩ := exists_natDegree_le_eval_eq_of_mem_reedMuller
    (mem_reedMuller_of_multilinear hf) x v
  obtain ⟨reply, heq⟩ := exists_linePolynomial P hdeg
  have heval (z : ℕ) : hornerMod p z (decodeReply p n reply) =
      (f (x + (z : ZMod p) • v)).val := by
    rw [← hP, ← heq, eval_linePolynomial, ZMod.val_natCast_of_lt (hornerMod_lt _ _)]
  refine ⟨reply, List.all_eq_true.mpr ?_, ?_⟩
  · intro i hi
    have hi' := List.mem_range.mp hi
    simp only [decide_eq_true_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left hi', Option.getD_some, heval]
  · simp only [heval, Nat.cast_zero, zero_smul, add_zero, ZMod.natCast_zmod_val]

/-- For each fixed input point, among all directions at most `(n + 1) * Δ(w, f)` pass the
coefficient checks with a wrong value at zero. The proof word may depend on the direction. -/
theorem card_checkLineReply_wrong_le {p n : ℕ} [Fact p.Prime] (hp : n + 1 < p)
    {f : (Fin n → ZMod p) → ZMod p} (hf : IsMultilinear f) (w : (Fin n → ZMod p) → ZMod p)
    (x : Fin n → ZMod p) (reply : (Fin n → ZMod p) → List Bool) :
    #{v | checkLineReply p n (reply v) (List.ofFn fun i : Fin (n + 1) =>
        (w (x + ((i.val + 1 : ℕ) : ZMod p) • v)).val) = true ∧
      (hornerMod p 0 (decodeReply p n (reply v)) : ZMod p) ≠ f x} ≤
      (n + 1) * #{y | w y ≠ f y} := by
  classical
  have hnode (i : Fin (n + 1)) : node hp i ≠ 0 := by
    intro hz
    have hh := congrArg ZMod.val hz
    change (((i.val + 1 : ℕ) : ZMod p)).val = (0 : ZMod p).val at hh
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hh
    omega
  refine (card_le_card ?_).trans (card_false_line_claim_le (node hp) hnode
    (mem_reedMuller_of_multilinear hf) w x
    (fun v => linePolynomial p n (reply v)))
  intro v hv
  simp only [mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨hcheck, hwrong⟩ := hv
  refine ⟨(Polynomial.natDegree_ofCoeffList_le _).trans (by simp [length_decodeReply]), ?_, ?_⟩
  · intro i
    have h := (List.all_eq_true.mp hcheck) i.val (List.mem_range.mpr i.isLt)
    simp only [decide_eq_true_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left i.isLt, Option.getD_some] at h
    change (linePolynomial p n (reply v)).eval ((i.val + 1 : ℕ) : ZMod p) = _
    rw [eval_linePolynomial, h, ZMod.natCast_zmod_val]
    rfl
  · simpa only [← Nat.cast_zero (R := ZMod p), eval_linePolynomial] using hwrong

end Cslib.Complexity.MIP
