/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Init
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Foundations.Data.BitString.List.Rows

/-!
# The Boneh–Shoup cascade on words

The cascade of [BonehShoup2023], v0.6, Section 6.4.2, Figure 6.3b (printed pp. 226 and 229),
starts at the secret key and evaluates the base function with the current state as its key
and the next message block as its input. The input block width may differ from the key width.

The evaluator reads as many whole blocks as fit in the message at the width determined by
the initial key length. It returns the initial key on an empty message. For a base function
with outputs the size of its key, the same width applies throughout the evaluation. Its
polynomial-time certificate uses that bound on intermediate states.

## Main definitions

* `Cslib.Crypto.cascadeFamily`: the word-level cascade.

## Main results

* `Cslib.Crypto.length_cascadeFamily`: the output retains the key width.
* `Cslib.Crypto.cascadeFamily_append`: continue from the tag to evaluate an aligned suffix,
  as in equation (6.16), printed p. 230.
* `Cslib.Crypto.computableInPolyTime_cascadeFamily`: polynomial-time evaluation.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Evaluate the key-chaining cascade on the full blocks of `msg`, using `inLen key.length`
bits per block. When this width is zero the fold processes no blocks. -/
@[expose]
def cascadeFamily (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (key msg : List Bool) : List Bool :=
  let width := inLen key.length
  (BitString.listRows (msg.length / width) width msg).foldl family key

private theorem length_cascadeFold {inLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (key : List Bool) {blocks : List (List Bool)}
    (hblocks : ∀ block ∈ blocks, block.length = inLen key.length) :
    (blocks.foldl family key).length = key.length :=
  List.foldl_rel (b := ()) (g := fun _ _ => ()) (r := fun state _ => state.length = key.length)
    rfl fun block hb state _ hs =>
      (hlen state block ((hblocks block hb).trans (congrArg inLen hs.symm))).trans hs

/-- A base function with outputs in its key space gives cascade outputs of the same key width. -/
theorem length_cascadeFamily {inLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (key msg : List Bool) :
    (cascadeFamily inLen family key msg).length = key.length :=
  length_cascadeFold hlen key fun _ hb => BitString.length_of_mem_listRows hb

/-- The empty message returns the initial key. -/
@[simp]
theorem cascadeFamily_nil (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (key : List Bool) : cascadeFamily inLen family key [] = key := by
  simp [cascadeFamily, BitString.listRows]

/-- On aligned words the tag of a prefix is the key for its suffix. This gives the cascade
extension identity (6.16) of [BonehShoup2023], v0.6, Section 6.4.3, printed p. 230. -/
theorem cascadeFamily_append {inLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (key : List Bool) {msg suffix : List Bool}
    (hwidth : 0 < inLen key.length) (hmsg : inLen key.length ∣ msg.length)
    (hsuffix : inLen key.length ∣ suffix.length) :
    cascadeFamily inLen family key (msg ++ suffix) =
      cascadeFamily inLen family (cascadeFamily inLen family key msg) suffix := by
  conv_lhs =>
    rw [cascadeFamily]
    dsimp only
    rw [BitString.listRows_append_aligned hwidth hmsg hsuffix, List.foldl_append]
  conv_rhs => rw [cascadeFamily, length_cascadeFamily hlen]
  rfl

/-- Evaluate the cascade in polynomial time using the base function's fixed-width outputs
on valid blocks to bound the accumulator. -/
theorem computableInPolyTime_cascadeFamily {inLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool}
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool => cascadeFamily inLen family p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hKey := ComputableInPolyTime.fst encBits encBits
  have hMsg := ComputableInPolyTime.snd encBits encBits
  have hWidth := hIn.comp (ComputableInPolyTime.length_bits.comp hKey)
  have hBlocks := ComputableInPolyTime.bitsRowsWithInput
    (ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hMsg) hWidth)
    hWidth hMsg
  unfold cascadeFamily
  refine ComputableInPolyTime.foldl' hBlocks hKey hEval
    (B := fun p : List Bool × List Bool => (encPair encBits encBits p).length)
    PolyBounded.self fun p i _ => ?_
  rw [encBits_apply, length_cascadeFold hLen p.1
    (fun _ hb => BitString.length_of_mem_listRows (List.mem_of_mem_take hb))]
  simp only [length_encPair, encBits_apply]
  omega

end Cslib.Crypto
