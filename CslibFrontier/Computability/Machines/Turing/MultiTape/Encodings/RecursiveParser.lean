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
    have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n m
    exact ⟨[], [], .nil, .nil, rfl⟩
  | @cons pending token stream h ih =>
    intro n m heq
    cases n with
    | zero =>
      have hm : pending + 1 = m := by omega
      exact ⟨[], token :: stream, .nil, hm ▸ Forest.cons h, rfl⟩
    | succ n =>
      obtain ⟨left, right, hl, hr, heq'⟩ :=
        ih (n + arity token) m (by omega)
      exact ⟨token :: left, right, .cons hl, hr, by simpa using congrArg (token :: ·) heq'⟩

private theorem ofFn_prepend {n : ℕ} (first : α) (others : Fin n → α) :
    List.ofFn (fun i : Fin (n + 1) =>
      match i with
      | ⟨0, _⟩ => first
      | ⟨index + 1, h⟩ => others ⟨index, Nat.lt_of_succ_lt_succ h⟩) =
      first :: List.ofFn others := by
  rw [← List.ofFn_cons]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

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
    intro stream children rest h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, .nil⟩
  | succ n ih =>
    intro stream children rest h
    change (read stream).bind (fun p => (parseOperands read n p.2).bind (fun q =>
      let values : Fin (n + 1) → α
        | ⟨0, _⟩ => p.1
        | ⟨index + 1, h⟩ => q.1 ⟨index, Nat.lt_of_succ_lt_succ h⟩
      some (values, q.2))) = some (children, rest) at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨first, tail⟩, hfirst, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨others, final⟩, hothers, h⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨heq, htree⟩ := hread stream first tail hfirst
    obtain ⟨heq', hforest⟩ := ih tail others final hothers
    simp only [ofFn_prepend, List.flatMap_cons]
    constructor
    · rw [List.append_assoc, heq', heq]
    · simpa only [Nat.add_comm] using htree.append hforest

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
  | zero => intro stream value rest h; simp [parseFuel] at h
  | succ fuel ih =>
    intro stream value rest h
    cases stream with
    | nil => simp [parseFuel] at h
    | cons token stream =>
      change (parseOperands (parseFuel (readNode arity make) fuel) (arity token) stream).bind
        (fun p => some (make token p.1, p.2)) = some (value, rest) at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨children, tail⟩, hchildren, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨heq, hforest⟩ := operands_sound ih (arity token) stream children tail hchildren
      rw [htokens]
      exact ⟨by simpa using congrArg (token :: ·) heq,
        .cons (pending := 0) (by simpa using hforest)⟩

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
    intro stream hforest hlength rest
    cases hforest
    exact ⟨Fin.elim0, rfl, rfl⟩
  | succ n ih =>
    intro stream hforest hlength rest
    obtain ⟨tree, others, htree, hothers, heq⟩ :=
      forest_split hforest 1 n (by omega)
    have hlength' : tree.length + others.length ≤ bound := by
      simpa only [← heq, List.length_append] using hlength
    obtain ⟨first, hfirst, hfirst_tokens⟩ :=
      hread tree htree (by omega) (others ++ rest)
    obtain ⟨values, hvalues, hvalues_tokens⟩ :=
      ih others hothers (by omega) rest
    let children : Fin (n + 1) → α
      | ⟨0, _⟩ => first
      | ⟨index + 1, h⟩ => values ⟨index, Nat.lt_of_succ_lt_succ h⟩
    refine ⟨children, ?_, ?_⟩
    · rw [← heq, List.append_assoc]
      change (read (tree ++ (others ++ rest))).bind
        (fun p => (parseOperands read n p.2).bind (fun q =>
          let operands : Fin (n + 1) → α
            | ⟨0, _⟩ => p.1
            | ⟨index + 1, h⟩ => q.1 ⟨index, Nat.lt_of_succ_lt_succ h⟩
          some (operands, q.2))) = some (children, rest)
      rw [hfirst]
      simp only [Option.bind_some]
      rw [hvalues]
      rfl
    · simp only [children, ofFn_prepend, List.flatMap_cons,
        hfirst_tokens, hvalues_tokens, heq]

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
    intro tree htree hlength rest
    have hnil : tree = [] := List.length_eq_zero_iff.mp (by omega)
    subst tree
    cases htree
  | succ fuel ih =>
    intro tree htree hlength rest
    cases htree with
    | @cons _ token tail hforest =>
      simp only [Nat.zero_add] at hforest
      have htail : tail.length ≤ fuel := by
        simp only [List.length_cons] at hlength
        omega
      obtain ⟨children, hchildren, hchildren_tokens⟩ :=
        operands_complete ih (arity token) tail hforest htail rest
      refine ⟨make token children, ?_, ?_⟩
      · change (parseOperands (parseFuel (readNode arity make) fuel) (arity token)
          (tail ++ rest)).bind (fun p => some (make token p.1, p.2)) = _
        rw [hchildren]
        rfl
      · rw [htokens, hchildren_tokens]

/-- Decoding succeeds exactly on complete node streams, and re-encoding its value recovers
every input token. Missing operands and trailing input are rejected. -/
theorem decode_readNode_tokens (arity : τ → ℕ)
    (make : (token : τ) → (Fin (arity token) → α) → α) (tokens : α → List τ)
    (htokens : ∀ token children,
      tokens (make token children) = token :: (List.ofFn children).flatMap tokens)
    (stream : List τ) :
    (decode (readNode arity make) stream).map tokens =
      if isTree arity stream then some stream else none := by
  by_cases htree : Forest arity 1 stream
  · have hv := (isTree_eq_true_iff.mpr htree)
    rw [hv, ite_eq_left rfl]
    obtain ⟨value, hvalue, htokens_value⟩ :=
      parseFuel_readNode_complete arity make tokens htokens stream.length stream htree le_rfl []
    simp only [List.append_nil] at hvalue
    simp only [decode, parse, hvalue, Option.map_some, htokens_value]
  · have hv : isTree arity stream = false := by
      cases h : isTree arity stream with
      | false => rfl
      | true => exact False.elim (htree (isTree_eq_true_iff.mp h))
    rw [hv, ite_eq_right Bool.false_ne_true]
    unfold decode parse
    cases hparse : parseFuel (readNode arity make) stream.length stream with
    | none => rfl
    | some p =>
      obtain ⟨value, rest⟩ := p
      cases rest with
      | nil =>
        obtain ⟨heq, hforest⟩ :=
          parseFuel_readNode_sound arity make tokens htokens _ _ _ _ hparse
        simp only [List.append_nil] at heq
        exact False.elim (htree (heq ▸ hforest))
      | cons token rest => rfl

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
  have hcopy := (ComputableInPolyTime.optionSome (encList encToken)).comp
    (ComputableInPolyTime.id' (encIn := encList encToken))
  apply ((isTree_polyTime harity hmax).ite hcopy (ComputableInPolyTime.const none)).of_enc_eq
  intro stream
  have h := decode_readNode_tokens arity make tokens htokens stream
  have hword : encOption encTree (decode (readNode arity make) stream) =
      encOption (encList encToken) ((decode (readNode arity make) stream).map tokens) := by
    cases decode (readNode arity make) stream with
    | none => rfl
    | some value => simp only [Option.map_some, encOption_some, henc]
  rw [hword, h]
  split <;> rfl

end Turing.MultiTapeTM.RecursiveEncoding
