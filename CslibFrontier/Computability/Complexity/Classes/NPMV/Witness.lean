/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Witnesses for multivalued NP functions

Pack an output word and an NP certificate for the output graph into one fixed-length guess.
The deterministic computation checks the certificate and tags the output on success.
## Main results

* `Cslib.Complexity.exists_outputVerifier_of_mem_NPMV`
-/

public section

namespace Cslib.Complexity

open Polynomial Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop}

private def checkOutput (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : (α × List Bool) × List Bool → Bool) (aw : α × List Bool) : List Bool :=
  let out := unframe aw.2
  let cert := unframe (dropFrame aw.2)
  let pair := (aw.1, out)
  if decide (cert.length = p.eval (encPair enc encBits pair).length) && V (pair, cert) then
    true :: out
  else []

private theorem checkOutput_polyTime (p : Polynomial ℕ)
    {V : (α × List Bool) × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool) :
    ComputableInPolyTime (checkOutput enc p V) (encPair enc encBits) encBits := by
  let input := encPair enc encBits
  have hw := ComputableInPolyTime.snd enc encBits
  have hout := ComputableInPolyTime.unframe.comp hw
  have hc := ComputableInPolyTime.unframe.comp (ComputableInPolyTime.dropFrame.comp hw)
  have hpair := (ComputableInPolyTime.fst enc encBits).prod hout
  have hlen := (ComputableInPolyTime.encoding_length encBits).comp hc
  have hbudget := (ComputableInPolyTime.unary_eval p).comp
    ((ComputableInPolyTime.encoding_length input).comp hpair)
  exact ComputableInPolyTime.ite'
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.unary_eq' hlen hbudget)
      (hV.comp (hpair.prod hc)))
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [true]) hout)
    (ComputableInPolyTime.const [])

/-- An NPMV graph has a deterministic polynomial-time decoder of fixed-length guesses.
The successful decoder outputs are exactly the graph's values, with an acceptance tag. -/
theorem exists_outputVerifier_of_mem_NPMV (h : R ∈ NPMV enc) :
    ∃ (q : Polynomial ℕ) (f : α × List Bool → List Bool),
      ComputableInPolyTime f (encPair enc encBits) encBits ∧
      ∀ a y, R a y ↔ ∃ w : List Bool, w.length = q.eval (enc a).length ∧ f (a, w) = true :: y := by
  obtain ⟨⟨b, hb⟩, p, V, hV, hspec⟩ := h
  let q := (2 * b + 1) + (2 * p.comp (2 * X + 1 + b) + 1)
  refine ⟨q, checkOutput enc p V, checkOutput_polyTime p hV, fun a y => ?_⟩
  constructor
  · intro hy
    obtain ⟨cert, hlen, hvalid⟩ := (hspec (a, y)).mp hy
    have hcert : cert.length ≤ p.eval (2 * (enc a).length + 1 + b.eval (enc a).length) := by
      rw [hlen, length_encPair, encBits_apply]
      exact p.eval_mono (Nat.add_le_add_left (hb a y hy) _)
    have hfit : (frame y ++ frame cert).length ≤ q.eval (enc a).length := by
      simp only [List.length_append, length_frame, q, eval_add, eval_mul, eval_comp, eval_X,
        eval_ofNat, eval_one]
      have := hb a y hy
      omega
    let pad := List.replicate (q.eval (enc a).length - (frame y ++ frame cert).length) false
    refine ⟨(frame y ++ frame cert) ++ pad, ?_, ?_⟩
    · simp only [List.length_append, pad, List.length_replicate]
      exact Nat.add_sub_of_le (by simpa only [List.length_append] using hfit)
    · simp [checkOutput, List.append_assoc, hlen, hvalid]
  · rintro ⟨w, -, hw⟩
    change (if decide ((unframe (dropFrame w)).length =
        p.eval (encPair enc encBits (a, unframe w)).length) &&
        V ((a, unframe w), unframe (dropFrame w)) then true :: unframe w else []) = true :: y at hw
    split at hw
    · rename_i hv
      have hy : unframe w = y := (List.cons.inj hw).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [hy] at hv
      exact (hspec (a, y)).mpr ⟨_, hv.1, hv.2⟩
    · contradiction

end Cslib.Complexity
