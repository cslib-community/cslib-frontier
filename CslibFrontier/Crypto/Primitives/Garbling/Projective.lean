/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime

/-!
# Projective encoding of garbled inputs on words, with tokens of one width

[BellareHoangRogaway2012], §3.2 (p. 8), calls a garbling scheme *projective* when, for inputs `x`
and `x'` of `n` bits, `En(e, x)` and `En(e, x')` are vectors `(X₁, …, Xₙ)` and `(X₁', …, Xₙ')` with
`|Xᵢ| = |Xᵢ'|`, and `Xᵢ = Xᵢ'` whenever `x` and `x'` have the same bit `i`. The section first
describes the common way to meet this, which §7.1 (p. 35) also uses: `e` lists a pair of tokens for
each input bit, `e = (X₁⁰, X₁¹, …, Xₙ⁰, Xₙ¹)`, and `En(e, x)` selects `(X₁^{x₁}, …, Xₙ^{xₙ})`.

`projectiveEncode` is that token-list form on words, in the layout of the point-and-permute and
half-gates schemes: `e` is the concatenation of the `2 n` tokens, all of one width `|e| / (2 n)`,
and the garbled input is the concatenation of the selected tokens. `projectiveToken e n i b` is the
token of bit `b` of input `i`. The layout is narrower than the definition of §3.2, which allows
tokens of different widths at different coordinates and fixes no layout of `e`.

Yao's protocol over a garbling scheme with this encoding sends each token on its own: the
garbler's tokens in its message and the evaluator's through oblivious transfer.
`projectiveEncode_polyTime` certifies the encoding and `projectiveEncode_eq_flatten_ofFn` writes it
as the concatenation of the tokens of the bits of `x`.

## Main definitions

* `Cslib.Crypto.Garbling.projectiveToken`: the token of one bit of one input.
* `Cslib.Crypto.Garbling.projectiveEncode`: the projective encoding `En(e, x)` on words, with
  tokens of one width.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM

/-- The token of bit `b` of input `i` among `n` inputs, read from the encoding information `e`: row
`2 i + b` of `e`, in rows of `|e| / (2 n)` bits. -/
@[expose] def projectiveToken (e : List Bool) (n i : ℕ) (b : Bool) : List Bool :=
  BitString.listRow (e.length / (2 * n)) (if b then 2 * i + 1 else 2 * i) e

/-- **The projective encoding** `En(e, x)` on words, with tokens of one width: the concatenation of
the tokens of the bits of `x`, read from `e` as two tokens per input, each `|e| / (2 |x|)` bits. It
is projective in the sense of [BellareHoangRogaway2012], §3.2, in one fixed layout. -/
@[expose] def projectiveEncode (e x : List Bool) : List Bool :=
  ((List.range x.length).map fun i => projectiveToken e x.length i (x.getD i false)).flatten

/-- `En` runs in polynomial time. -/
theorem projectiveEncode_polyTime :
    ComputableInPolyTime (fun (e, x) => projectiveEncode e x) (encPair encBits encBits)
      encBits := by
  polytime [projectiveEncode, projectiveToken, BitString.listRow]

/-- The projective encoding of `x` is the concatenation of the tokens of its bits. -/
theorem projectiveEncode_eq_flatten_ofFn (e x : List Bool) :
    projectiveEncode e x =
      (List.ofFn fun i : Fin x.length => projectiveToken e x.length i x[i]).flatten := by
  refine congrArg List.flatten (List.ext_getElem (by simp) fun i h₁ h₂ => ?_)
  simp only [List.length_map, List.length_range] at h₁
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

end Cslib.Crypto.Garbling
