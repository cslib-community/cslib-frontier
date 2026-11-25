/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive
public import CslibFrontier.Foundations.Syntax.PrefixParser
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Mathlib.Data.List.OfFn

/-!
# Native decoding of flat constructor streams

`RecursiveEncoding.readNode` interprets each constructor token by its arity and constructor.
When constructing a node writes that token followed by its children's streams, the generic
prefix parser accepts exactly the complete one-root forests. Its successful output has exactly
the original token stream as its encoding. Consequently decoding typed tokens has a native
polynomial-time certificate whenever token arities can be read in polynomial time and have a
fixed bound. This does not supply a decoder for arbitrary bit-word embeddings of scalar fields.
-/

public section

namespace Turing.MultiTapeTM.RecursiveEncoding

open Cslib.PrefixParser

variable {τ α : Type}

/-- Interpret a constructor token using its recursive arity and constructor function. -/
@[expose] def readNode (arity : τ → ℕ)
    (make : (token : τ) → (Fin (arity token) → α) → α) (token : τ) : Option (Step α) :=
  some (.node (arity token) (make token))

private theorem forest_split {arity : τ → ℕ} {pending : ℕ} {stream : List τ}
    (h : Forest arity pending stream) :
    ∀ n m, pending = n + m → ∃ left right,
      Forest arity n left ∧ Forest arity m right ∧ left ++ right = stream := by
  induction h with
  | nil =>
    intro n m h
    obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    exact ⟨[], [], .nil, .nil, rfl⟩
  | @cons pending token stream h ih =>
    rintro (_ | n) m heq
    · exact ⟨[], token :: stream, .nil, (by omega : pending + 1 = m) ▸ Forest.cons h, rfl⟩
    · obtain ⟨left, right, hl, hr, rfl⟩ := ih (n + arity token) m (by omega)
      exact ⟨token :: left, right, .cons hl, hr, rfl⟩

private theorem ofFn_prepend {n : ℕ} (first : α) (others : Fin n → α)
    (f : Fin (n + 1) → α) (h0 : f 0 = first) (hs : ∀ i : Fin n, f i.succ = others i) :
    List.ofFn f = first :: List.ofFn others := by
  rw [List.ofFn_succ, h0, funext hs]

private theorem operands_sound {arity : τ → ℕ} {tokens : α → List τ}
    {read : List τ → Option (α × List τ)}
    (hread : ∀ stream value rest, read stream = some (value, rest) →
      tokens value ++ rest = stream ∧ Forest arity 1 (tokens value)) :
    ∀ n stream children rest, parseOperands read n stream = some (children, rest) →
      (List.ofFn children).flatMap tokens ++ rest = stream ∧
        Forest arity n ((List.ofFn children).flatMap tokens) := by
  intro n
  induction n with
  | zero =>
    rintro stream children rest ⟨⟩
    exact ⟨rfl, .nil⟩
  | succ n ih =>
    intro stream children rest h
    simp only [parseOperands, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨first, tail⟩, hfirst, ⟨others, final⟩, hothers, rfl, rfl⟩ := h
    obtain ⟨rfl, htree⟩ := hread stream first tail hfirst
    obtain ⟨rfl, hforest⟩ := ih tail others final hothers
    rw [ofFn_prepend first others _ rfl fun ⟨_, _⟩ => rfl]
    simp only [List.flatMap_cons, List.append_assoc]
    exact ⟨trivial, Nat.add_comm 1 n ▸ htree.append hforest⟩

/-- Every successful node parse produces a complete tree prefix and preserves its suffix. -/
theorem parseFuel_readNode_sound (arity : τ → ℕ)
    (make : (token : τ) → (Fin (arity token) → α) → α) (tokens : α → List τ)
    (htokens : ∀ token children,
      tokens (make token children) = token :: (List.ofFn children).flatMap tokens) :
    ∀ fuel stream value rest,
      parseFuel (readNode arity make) fuel stream = some (value, rest) →
        tokens value ++ rest = stream ∧ Forest arity 1 (tokens value) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ h
    simp [parseFuel] at h
  | succ fuel ih =>
    rintro (_ | ⟨token, stream⟩) value rest h
    · simp [parseFuel] at h
    · simp only [parseFuel, readNode, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨children, tail⟩, hchildren, rfl, rfl⟩ := h
      obtain ⟨rfl, hforest⟩ := operands_sound ih (arity token) stream children tail hchildren
      rw [htokens]
      exact ⟨rfl, .cons (pending := 0) (by simpa using hforest)⟩

private theorem operands_complete {arity : τ → ℕ} {tokens : α → List τ}
    {read : List τ → Option (α × List τ)} {bound : ℕ}
    (hread : ∀ tree, Forest arity 1 tree → tree.length ≤ bound → ∀ rest,
      ∃ value, read (tree ++ rest) = some (value, rest) ∧ tokens value = tree) :
    ∀ n stream, Forest arity n stream → stream.length ≤ bound → ∀ rest,
      ∃ children, parseOperands read n (stream ++ rest) = some (children, rest) ∧
        (List.ofFn children).flatMap tokens = stream := by
  intro n
  induction n with
  | zero =>
    rintro stream ⟨⟩ _ rest
    exact ⟨Fin.elim0, rfl, rfl⟩
  | succ n ih =>
    intro stream hforest hlength rest
    obtain ⟨tree, others, htree, hothers, rfl⟩ := forest_split hforest 1 n (by omega)
    rw [List.length_append] at hlength
    obtain ⟨first, hfirst, hfirst_tokens⟩ := hread tree htree (by omega) (others ++ rest)
    obtain ⟨values, hvalues, hvalues_tokens⟩ := ih others hothers (by omega) rest
    refine ⟨fun | ⟨0, _⟩ => first | ⟨Nat.succ i, h⟩ => values ⟨i, Nat.lt_of_succ_lt_succ h⟩,
      ?_, ?_⟩
    · simp only [List.append_assoc, parseOperands, Option.bind_eq_bind, hfirst, Option.bind_some,
        hvalues, Option.pure_def, Option.some.injEq, Prod.mk.injEq, and_true]
      exact funext (Fin.cases rfl fun _ => rfl)
    · rw [ofFn_prepend first values _ rfl fun ⟨_, _⟩ => rfl]
      simp only [List.flatMap_cons, hfirst_tokens, hvalues_tokens]

/-- A complete node stream is parsed with fuel at least its token count, preserving every
following token. No semantic inhabitant or field decoder is required. -/
theorem parseFuel_readNode_complete (arity : τ → ℕ)
    (make : (token : τ) → (Fin (arity token) → α) → α) (tokens : α → List τ)
    (htokens : ∀ token children,
      tokens (make token children) = token :: (List.ofFn children).flatMap tokens) :
    ∀ fuel tree, Forest arity 1 tree → tree.length ≤ fuel → ∀ rest,
      ∃ value, parseFuel (readNode arity make) fuel (tree ++ rest) = some (value, rest) ∧
        tokens value = tree := by
  intro fuel
  induction fuel with
  | zero =>
    rintro tree htree hlength _
    obtain rfl : tree = [] := List.length_eq_zero_iff.mp (by omega)
    cases htree
  | succ fuel ih =>
    intro tree htree hlength rest
    cases htree with | @cons _ token tail hforest =>
    simp only [Nat.zero_add] at hforest
    simp only [List.length_cons] at hlength
    obtain ⟨children, hchildren, hchildren_tokens⟩ :=
      operands_complete ih (arity token) tail hforest (by omega) rest
    exact ⟨make token children, by simp [parseFuel, readNode, hchildren],
      by rw [htokens, hchildren_tokens]⟩

/-- Decoding succeeds exactly on complete node streams, and re-encoding its value recovers
every input token. Missing operands and trailing input are rejected. -/
theorem decode_readNode_tokens (arity : τ → ℕ)
    (make : (token : τ) → (Fin (arity token) → α) → α) (tokens : α → List τ)
    (htokens : ∀ token children,
      tokens (make token children) = token :: (List.ofFn children).flatMap tokens)
    (stream : List τ) :
    (decode (readNode arity make) stream).map tokens =
      if isTree arity stream then some stream else none := by
  cases hv : isTree arity stream with
  | true =>
    obtain ⟨value, hvalue, htokens_value⟩ := parseFuel_readNode_complete arity make tokens htokens
      stream.length stream (isTree_eq_true_iff.mp hv) le_rfl []
    rw [List.append_nil] at hvalue
    simp [decode, parse, hvalue, htokens_value]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, decode, parse]
    split
    · next value hparse =>
      obtain ⟨heq, hforest⟩ := parseFuel_readNode_sound arity make tokens htokens _ _ _ _ hparse
      rw [List.append_nil] at heq
      exact absurd (isTree_eq_true_iff.mpr (heq ▸ hforest)) (by simp [hv])
    · rfl

/-- Typed constructor-stream decoding has a native polynomial-time certificate. Its machine
validates the stream and emits its original encoded word; it need not build semantic Lean
values. The token embedding supplies no decoder for arbitrary bit words. -/
theorem decode_readNode_polyTime {encToken : τ ↪ List Bool} {encTree : α ↪ List Bool}
    (arity : τ → ℕ) (make : (token : τ) → (Fin (arity token) → α) → α)
    (tokens : α → List τ)
    (htokens : ∀ token children,
      tokens (make token children) = token :: (List.ofFn children).flatMap tokens)
    (henc : ∀ value, encTree value = encList encToken (tokens value))
    (harity : ComputableInPolyTime arity encToken encUnary)
    {maximum : ℕ} (hmax : ∀ token, arity token ≤ maximum) :
    ComputableInPolyTime (decode (readNode arity make)) (encList encToken)
      (encOption encTree) := by
  refine ((isTree_polyTime harity hmax).ite
    ((ComputableInPolyTime.optionSome (encList encToken)).comp .id')
    (.const none)).of_enc_eq fun stream => ?_
  have h := decode_readNode_tokens arity make tokens htokens stream
  have hword : encOption encTree (decode (readNode arity make) stream) =
      encOption (encList encToken) ((decode (readNode arity make) stream).map tokens) := by
    cases decode (readNode arity make) stream <;> simp [Option.map_some, encOption_some, henc]
  rw [hword, h]
  split <;> rfl

end Turing.MultiTapeTM.RecursiveEncoding
