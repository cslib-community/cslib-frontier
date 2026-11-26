/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# Splitting flat recursive constructor streams

A token's arity is its number of directly recursive fields. A tree is its constructor token,
followed by the streams of its children, in field order. `RecursiveEncoding.splitTree` separates
one complete tree from the following tokens and rejects a stream with missing children.
`RecursiveEncoding.isTree` additionally rejects trailing tokens.

The native polynomial-time certificate operates on `encList encToken`, which frames each token
once. It assumes a native certificate for reading the token arity and a fixed maximum arity.
It requires no decoder for the token embedding: its input is a typed token stream. The certificate
does not assert efficient decoding of arbitrary bit words or evaluation of arbitrary recursive
functions.
-/

public section

namespace Turing.MultiTapeTM.RecursiveEncoding

variable {τ : Type}

/-- A complete forest with `pending` roots, in prefix constructor order. -/
inductive Forest (arity : τ → ℕ) : ℕ → List τ → Prop where
  /-- No roots require no tokens. -/
  | nil : Forest arity 0 []
  /-- Reading one root replaces it by the token's recursive children. -/
  | cons {pending : ℕ} {token : τ} {tokens : List τ}
      (rest : Forest arity (pending + arity token) tokens) :
      Forest arity (pending + 1) (token :: tokens)

namespace Forest

/-- Concatenating complete forests adds their numbers of roots. -/
theorem append {arity : τ → ℕ} {n m : ℕ} {left right : List τ}
    (hl : Forest arity n left) (hr : Forest arity m right) :
    Forest arity (n + m) (left ++ right) := by
  induction hl with
  | nil => simpa using hr
  | @cons pending token tokens h ih =>
    have hi : Forest arity (pending + m + arity token) (tokens ++ right) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
    simpa only [List.cons_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Forest.cons hi : Forest arity (pending + m + 1) (token :: (tokens ++ right)))

/-- Concatenating tree streams yields a forest with one root per stream. -/
theorem flatten {arity : τ → ℕ} {children : List (List τ)}
    (hchildren : ∀ child ∈ children, Forest arity 1 child) :
    Forest arity children.length children.flatten := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
    simpa only [List.length_cons, List.flatten_cons, Nat.add_comm] using
      (hchildren child (List.mem_cons_self ..)).append
        (ih fun child h => hchildren child (List.mem_cons_of_mem _ h))

/-- A constructor followed by one complete stream per child is a tree. -/
theorem node {arity : τ → ℕ} {token : τ} {children : List (List τ)}
    (hcount : children.length = arity token)
    (hchildren : ∀ child ∈ children, Forest arity 1 child) :
    Forest arity 1 (token :: children.flatten) := by
  have h := flatten hchildren
  rw [hcount] at h
  exact .cons (pending := 0) (by simpa using h)

end Forest

/-- Read a specified number of roots, preserving the unconsumed suffix. -/
@[expose] def splitForest (arity : τ → ℕ) : ℕ → List τ → Option (List τ × List τ)
  | 0, tokens => some ([], tokens)
  | _ + 1, [] => none
  | pending + 1, token :: tokens => do
    let (front, rest) ← splitForest arity (pending + arity token) tokens
    return (token :: front, rest)

/-- Separate one complete tree from the following constructor tokens. -/
@[expose] def splitTree (arity : τ → ℕ) (tokens : List τ) :
    Option (List τ × List τ) := splitForest arity 1 tokens

/-- The splitter succeeds exactly on a complete prefix forest and its untouched suffix. -/
theorem splitForest_eq_some_iff {arity : τ → ℕ} {pending : ℕ}
    {tokens front rest : List τ} :
    splitForest arity pending tokens = some (front, rest) ↔
      Forest arity pending front ∧ front ++ rest = tokens := by
  fun_induction splitForest arity pending tokens generalizing front rest with
  | case1 tokens => -- no pending roots
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨.nil, rfl⟩
    · rintro ⟨h, heq⟩
      cases h
      simpa using heq.symm
  | case2 pending => -- roots pending, no tokens left
    constructor
    · simp
    · rintro ⟨h, heq⟩
      cases h
      simp at heq
  | case3 pending token tokens ih => -- roots pending, `token :: tokens`
    change (splitForest arity (pending + arity token) tokens).bind
      (fun p => some (token :: p.1, p.2)) = some (front, rest) ↔ _
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨⟨front', rest'⟩, hparse, hresult⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hresult)
      obtain ⟨hforest, hrest⟩ := ih.mp hparse
      exact ⟨.cons hforest, by simpa using congrArg (token :: ·) hrest⟩
    · rintro ⟨h, heq⟩
      cases h with
      | cons h =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, heq⟩ := heq
        exact ⟨_, ih.mpr ⟨h, heq⟩, rfl⟩

/-- A successful tree split recognizes exactly a complete tree prefix. -/
theorem splitTree_eq_some_iff {arity : τ → ℕ} {tokens front rest : List τ} :
    splitTree arity tokens = some (front, rest) ↔
      Forest arity 1 front ∧ front ++ rest = tokens := splitForest_eq_some_iff

/-- Reading an encoded tree leaves any following tree or other suffix untouched. -/
theorem splitTree_append {arity : τ → ℕ} {tree : List τ}
    (h : Forest arity 1 tree) (rest : List τ) :
    splitTree arity (tree ++ rest) = some (tree, rest) :=
  splitTree_eq_some_iff.mpr ⟨h, rfl⟩

/-- Recognize exactly one complete tree, rejecting missing children and trailing tokens. -/
@[expose] def isTree (arity : τ → ℕ) (tokens : List τ) : Bool :=
  (splitTree arity tokens).elim false fun p => p.2.isEmpty

/-- Full-stream recognition holds exactly for a complete one-root forest. -/
theorem isTree_eq_true_iff {arity : τ → ℕ} {tokens : List τ} :
    isTree arity tokens = true ↔ Forest arity 1 tokens := by
  unfold isTree
  cases hs : splitTree arity tokens with
  | none =>
    simp only [Option.elim_none, Bool.false_eq_true, false_iff]
    intro hforest
    have h := splitTree_append hforest []
    simp only [List.append_nil, hs] at h
    contradiction
  | some p =>
    obtain ⟨front, rest⟩ := p
    simp only [Option.elim_some, List.isEmpty_iff]
    obtain ⟨hforest, hrest⟩ := splitTree_eq_some_iff.mp hs
    refine ⟨fun h => by subst h; simpa [← hrest] using hforest, fun hfull => ?_⟩
    have h := splitTree_append hfull []
    simp only [List.append_nil, hs, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2

/-- The counter scanner's state. It stops counting at the end of its initial forest. -/
private structure ScanState where
  /-- Roots still needed to complete the current forest. -/
  pending : ℕ
  /-- Number of tokens consumed before completion. -/
  consumed : ℕ

/-- Unary counters, with the pending-root counter framed before the consumed-token counter. -/
private enc_structure encScanState : ScanState where pending : encUnary, consumed : encUnary

/-- Consume a token only while roots remain; completion freezes both counters. -/
private def scanStep (arity : τ → ℕ) (state : ScanState) (token : τ) : ScanState :=
  if state.pending = 0 then state
  else ⟨state.pending - 1 + arity token, state.consumed + 1⟩

private theorem scanStep_zero (arity : τ → ℕ) (count : ℕ) (tokens : List τ) :
    tokens.foldl (scanStep arity) ⟨0, count⟩ = ⟨0, count⟩ := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    change tokens.foldl (scanStep arity) ⟨0, count⟩ = ⟨0, count⟩
    exact ih

private theorem consumed_le_scan (arity : τ → ℕ) (tokens : List τ) (state : ScanState) :
    state.consumed ≤ (tokens.foldl (scanStep arity) state).consumed := by
  induction tokens generalizing state with
  | nil => exact Nat.le_refl _
  | cons token tokens ih =>
    exact Nat.le_trans (show state.consumed ≤ (scanStep arity state token).consumed from by
      unfold scanStep
      split <;> simp) (ih _)

private theorem splitForest_eq_scan (arity : τ → ℕ) (tokens : List τ) (pending count : ℕ) :
    splitForest arity pending tokens =
      let state := tokens.foldl (scanStep arity) ⟨pending, count⟩
      if state.pending = 0 then
        some (tokens.take (state.consumed - count), tokens.drop (state.consumed - count))
      else none := by
  fun_induction splitForest arity pending tokens generalizing count with
  | case1 => rw [scanStep_zero]; simp -- no pending roots
  | case2 => simp -- roots pending, no tokens left
  | case3 pending token tokens ih => -- roots pending, `token :: tokens`
    change (splitForest arity (pending + arity token) tokens).bind
      (fun p => some (token :: p.1, p.2)) = _
    rw [ih (count + 1)]
    simp only [List.foldl_cons, scanStep, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    set state := tokens.foldl (scanStep arity) ⟨pending + arity token, count + 1⟩
    by_cases h : state.pending = 0
    · simp only [h, ite_true, Option.bind_some]
      have hc : count + 1 ≤ state.consumed :=
        consumed_le_scan arity tokens ⟨pending + arity token, count + 1⟩
      have hsub : state.consumed - count = state.consumed - (count + 1) + 1 := by omega
      rw [hsub, List.take_succ_cons, List.drop_succ_cons]
    · simp [h]

/-- The token scanner's arithmetic state grows at most linearly with the number of tokens. -/
private theorem scan_bounds (arity : τ → ℕ) {maximum : ℕ}
    (hmax : ∀ token, arity token ≤ maximum)
    (tokens : List τ) (state : ScanState) :
    (tokens.foldl (scanStep arity) state).pending ≤ state.pending + maximum * tokens.length ∧
      (tokens.foldl (scanStep arity) state).consumed ≤ state.consumed + tokens.length := by
  induction tokens generalizing state with
  | nil => simp
  | cons token tokens ih =>
    obtain ⟨hp, hc⟩ := ih (scanStep arity state token)
    have hm := hmax token
    have hstep : (scanStep arity state token).pending ≤ state.pending + maximum ∧
        (scanStep arity state token).consumed ≤ state.consumed + 1 := by
      unfold scanStep
      split <;> (try dsimp) <;> omega
    simp only [List.foldl_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    constructor <;> omega

open ComputableInPolyTime

private theorem scanStep_polyTime {encToken : τ ↪ List Bool} {arity : τ → ℕ}
    (harity : ComputableInPolyTime arity encToken encUnary) :
    ComputableInPolyTime (fun p : ScanState × τ => scanStep arity p.1 p.2)
      (encPair encScanState encToken) encScanState := by
  have hs := fst encScanState encToken
  have hp := encScanState_pending_polyTime hs
  have hc := encScanState_consumed_polyTime hs
  exact ite_decide (unary_eq' hp (const 0)) hs
    (encScanState_mk_polyTime
      (unary_add' (unary_sub' hp (const 1)) (harity.comp (snd encScanState encToken)))
      (unary_succ.comp hc))

/-- Scanning typed constructor tokens is natively polynomial-time. Its two unary counters have
linear encoded size when arities have a fixed bound. No token decoder is assumed. -/
private theorem scan_polyTime {encToken : τ ↪ List Bool} {arity : τ → ℕ}
    (harity : ComputableInPolyTime arity encToken encUnary)
    {maximum : ℕ} (hmax : ∀ token, arity token ≤ maximum) :
    ComputableInPolyTime (fun tokens => tokens.foldl (scanStep arity) ⟨1, 0⟩)
      (encList encToken) encScanState := by
  apply ComputableInPolyTime.foldl' ComputableInPolyTime.id'
    (ComputableInPolyTime.const ⟨1, 0⟩) (scanStep_polyTime harity)
    (B := fun tokens => (2 * maximum + 1) * (encList encToken tokens).length + 3)
    (((PolyBounded.const (2 * maximum + 1)).mul PolyBounded.self).add (.const 3))
  intro tokens i _
  obtain ⟨hp, hc⟩ := scan_bounds arity hmax (tokens.take i) ⟨1, 0⟩
  have hi := (List.length_take_le' i tokens).trans
    (SizedListEncoding.length_le (encA := encToken) (encL := encList encToken) tokens)
  have hm := Nat.mul_le_mul_left maximum hi
  simp only [encScanState_apply, encScanStateFields, length_encPair,
    encUnary_apply, List.length_replicate] at hp hc ⊢
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  omega

/-- Splitting one typed tree has a native polynomial-time certificate, assuming only native
arity recognition and a fixed arity bound. The returned prefix and suffix retain the token
encoding; arbitrary bit-word decoding is a separate operation. -/
theorem splitTree_polyTime {encToken : τ ↪ List Bool} {arity : τ → ℕ}
    (harity : ComputableInPolyTime arity encToken encUnary)
    {maximum : ℕ} (hmax : ∀ token, arity token ≤ maximum) :
    ComputableInPolyTime (splitTree arity) (encList encToken)
      (encOption (encPair (encList encToken) (encList encToken))) := by
  have hs := scan_polyTime harity hmax
  have hp := encScanState_pending_polyTime hs
  have hc := encScanState_consumed_polyTime hs
  have hout := (optionSome (encPair (encList encToken) (encList encToken))).comp
    ((listTakeWithInput id' hc).prod (listDropWithInput id' hc))
  apply (ite_decide (unary_eq' hp (const 0)) hout (const none)).of_enc_eq
  intro tokens
  unfold splitTree
  rw [splitForest_eq_scan arity tokens 1 0]
  simp only [Nat.sub_zero, Function.comp_apply]

/-- Native polynomial-time validity checking for a complete typed token stream. No semantic
tree decoder or token decoder is required. -/
theorem isTree_polyTime {encToken : τ ↪ List Bool} {arity : τ → ℕ}
    (harity : ComputableInPolyTime arity encToken encUnary)
    {maximum : ℕ} (hmax : ∀ token, arity token ≤ maximum) :
    ComputableInPolyTime (isTree arity) (encList encToken) encBool := by
  have hrest : ComputableInPolyTime (fun p : List τ × (List τ × List τ) => p.2.2)
      (encPair (encList encToken) (encPair (encList encToken) (encList encToken)))
      (encList encToken) :=
    (snd (encList encToken) (encList encToken)).comp
      (snd (encList encToken) (encPair (encList encToken) (encList encToken)))
  exact optionElimWithInput (splitTree_polyTime harity hmax) (const false)
    ((listIsEmpty (encA := encToken) (encL := encList encToken)).comp hrest)

end Turing.MultiTapeTM.RecursiveEncoding
