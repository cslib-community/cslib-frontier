/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Extracting children from flat constructor streams

`RecursiveEncoding.child? arity index` discards the root token, skips `index` complete subtrees,
and returns the next complete subtree. It returns `none` on missing or incomplete subtrees.
It does not check the root's constructor or declared arity: a generated constructor projection
checks its constructor separately before selecting the corresponding recursive field.

For each fixed field index, extraction has a native polynomial-time certificate on
`encList encToken`, assuming native polynomial-time arity recognition and a fixed maximum arity.
No token decoder or token inhabitant is assumed. This is extraction on typed token streams,
not decoding of arbitrary Boolean words.
-/

public section

namespace Turing.MultiTapeTM.RecursiveEncoding

variable {τ : Type}

private def forestAt? (arity : τ → ℕ) : ℕ → List τ → Option (List τ)
  | 0, tokens => (splitTree arity tokens).map Prod.fst
  | index + 1, tokens =>
    (splitTree arity tokens).bind fun parts => forestAt? arity index parts.2

/-- Extract a complete child stream at a fixed zero-based recursive-field index. The root's
constructor and arity are not checked; constructor projections supply that check separately. -/
def child? (arity : τ → ℕ) (index : ℕ) (tokens : List τ) : Option (List τ) :=
  forestAt? arity index tokens.tail

private theorem forestAt?_flatten {arity : τ → ℕ} (children : List (List τ))
    (hchildren : ∀ child ∈ children, Forest arity 1 child)
    (index : ℕ) (hindex : index < children.length) (suffix : List τ) :
    forestAt? arity index (children.flatten ++ suffix) = some children[index] := by
  induction children generalizing index with
  | nil => simp at hindex
  | cons child children ih =>
    have hchild := hchildren child (List.mem_cons_self ..)
    have hrest : ∀ tree ∈ children, Forest arity 1 tree :=
      fun tree htree => hchildren tree (List.mem_cons_of_mem _ htree)
    cases index with
    | zero =>
      simp only [List.flatten_cons, List.append_assoc, forestAt?,
        splitTree_append hchild, Option.map_some, List.getElem_cons_zero]
    | succ index =>
      have hi : index < children.length := by simpa using hindex
      simpa only [List.flatten_cons, List.append_assoc, forestAt?, splitTree_append hchild,
        Option.bind_some, List.getElem_cons_succ] using ih hrest index hi

/-- In a valid sequence of child streams, extraction preserves the selected child exactly,
independently of any following suffix. -/
theorem child?_node {arity : τ → ℕ} (root : τ) (children : List (List τ))
    (hchildren : ∀ child ∈ children, Forest arity 1 child)
    (index : ℕ) (hindex : index < children.length) (suffix : List τ) :
    child? arity index (root :: (children.flatten ++ suffix)) = some children[index] :=
  forestAt?_flatten children hchildren index hindex suffix

open ComputableInPolyTime

private theorem forestAt?_polyTime {encToken : τ ↪ List Bool} {arity : τ → ℕ}
    (harity : ComputableInPolyTime arity encToken encUnary)
    {maximum : ℕ} (hmax : ∀ token, arity token ≤ maximum) (index : ℕ) :
    ComputableInPolyTime (forestAt? arity index) (encList encToken)
      (encOption (encList encToken)) := by
  let encTokens := encList encToken
  have hsplit := splitTree_polyTime harity hmax
  induction index with
  | zero =>
    have hfront : ComputableInPolyTime (fun p : List τ × (List τ × List τ) => some p.2.1)
        (encPair encTokens (encPair encTokens encTokens)) (encOption encTokens) :=
      (optionSome encTokens).comp ((fst encTokens encTokens).comp
        (snd encTokens (encPair encTokens encTokens)))
    apply (optionElimWithInput (encC := encOption encTokens)
      (body := fun (_ : List τ) parts => some parts.1) hsplit
      (const (none : Option (List τ))) hfront).of_enc_eq
    intro tokens
    cases h : splitTree arity tokens <;> simp [forestAt?, h, encTokens]
  | succ index ih =>
    have hrest : ComputableInPolyTime
        (fun p : List τ × (List τ × List τ) => forestAt? arity index p.2.2)
        (encPair encTokens (encPair encTokens encTokens)) (encOption encTokens) :=
      ih.comp ((snd encTokens encTokens).comp
        (snd encTokens (encPair encTokens encTokens)))
    apply (optionElimWithInput (encC := encOption encTokens)
      (body := fun (_ : List τ) parts => forestAt? arity index parts.2) hsplit
      (const (none : Option (List τ))) hrest).of_enc_eq
    intro tokens
    cases h : splitTree arity tokens <;> simp [forestAt?, h, encTokens]

/-- For any fixed recursive-field index, subtree extraction has a native polynomial-time
certificate. Token arities need a native certificate and a fixed bound; token decoding is not
assumed. -/
theorem child?_polyTime {encToken : τ ↪ List Bool} {arity : τ → ℕ}
    (harity : ComputableInPolyTime arity encToken encUnary)
    {maximum : ℕ} (hmax : ∀ token, arity token ≤ maximum) (index : ℕ) :
    ComputableInPolyTime (child? arity index) (encList encToken)
      (encOption (encList encToken)) :=
  (forestAt?_polyTime harity hmax index).comp
    (tail (encA := encToken) (encL := encList encToken))

end Turing.MultiTapeTM.RecursiveEncoding
