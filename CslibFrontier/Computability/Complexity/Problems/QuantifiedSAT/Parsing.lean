/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix

/-!
# Extracting a bounded quantifier prefix

`PrenexQBF.parse q i` extracts `i` maximal alternating blocks from an existing `QBF`.
It never changes the formula: a missing block is empty, and a remaining quantifier is retained
in the matrix, where the well-formedness test rejects it. Thus the level languages are total
languages on the existing `QBF ℕ` domain with its existing `encQBF` encoding.
-/

public section

namespace Cslib.Complexity.PrenexQBF

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime TQBF

/-- The maximal initial block of quantifiers of polarity `q`. -/
@[expose] def initialVars : Bool → QBF ℕ → List ℕ
  | true, .ex v φ => v :: initialVars true φ
  | false, .all v φ => v :: initialVars false φ
  | _, _ => []

/-- The formula remaining after the maximal initial block of polarity `q`. -/
@[expose] def initialBody : Bool → QBF ℕ → QBF ℕ
  | true, .ex _ φ => initialBody true φ
  | false, .all _ φ => initialBody false φ
  | _, φ => φ

private theorem initial_reconstruct (q : Bool) (φ : QBF ℕ) :
    (if q then QBF.exs (initialVars q φ) (initialBody q φ)
      else QBF.alls (initialVars q φ) (initialBody q φ)) = φ := by
  induction φ generalizing q <;> cases q <;> simp_all [initialVars, initialBody, QBF.exs, QBF.alls]

/-- Extract exactly `i` alternating blocks. The remaining syntax is the matrix. -/
@[expose] def parse (q : Bool) : ℕ → QBF ℕ → PrenexQBF
  | 0, φ => ⟨[], φ⟩
  | i + 1, φ =>
    let tail := parse (!q) i (initialBody q φ)
    ⟨initialVars q φ :: tail.blocks, tail.matrix⟩

/-- Extracting the prefix and rebuilding the formula is exact, even on malformed inputs. -/
theorem formula_parse (q : Bool) (i : ℕ) (φ : QBF ℕ) :
    (parse q i φ).formula q = φ := by
  induction i generalizing q φ with
  | zero => rfl
  | succ i ih =>
    cases q
    · exact (congrArg (QBF.alls _) (ih true _)).trans (initial_reconstruct false φ)
    · exact (congrArg (QBF.exs _) (ih false _)).trans (initial_reconstruct true φ)

/-- Parsing produces the requested number of blocks, padding by empty blocks as necessary. -/
theorem length_parse (q : Bool) (i : ℕ) (φ : QBF ℕ) : (parse q i φ).blocks.length = i := by
  induction i generalizing q φ with
  | zero => rfl
  | succ i ih => simp only [parse, List.length_cons, ih]

private def isInitial (q : Bool) (t : QBF.Kind × ℕ) : Bool :=
  if q then t.1 == .ex else t.1 == .all

private theorem initial_tokens (q : Bool) (φ : QBF ℕ) :
    initialVars q φ = (φ.tokens.takeWhile (isInitial q)).map Prod.snd ∧
      (initialBody q φ).tokens = φ.tokens.dropWhile (isInitial q) := by
  induction φ generalizing q <;> cases q <;>
    simp_all [initialVars, initialBody, QBF.tokens, isInitial]

private theorem isInitial_polyTime (q : Bool) :
    ComputableInPolyTime (isInitial q) encToken encBool :=
  (of_finite (encIn := encKind) (encOut := encBool)
    (fun k => if q then k == .ex else k == .all)).comp (fst _ _)

private theorem initialVars_polyTime (q : Bool) :
    ComputableInPolyTime (initialVars q) encQBF (encList encNat) := by
  have := isInitial_polyTime q
  have heq : initialVars q = fun φ => (φ.tokens.takeWhile (isInitial q)).map Prod.snd :=
    funext fun φ => (initial_tokens q φ).1
  rw [heq]
  fun_prop

private theorem initialBody_polyTime (q : Bool) :
    ComputableInPolyTime (initialBody q) encQBF encQBF :=
  have := isInitial_polyTime q
  TQBF.computableInPolyTime_of_tokens (by fun_prop) fun φ => (initial_tokens q φ).2

/-- Bounded-prefix extraction is polynomial-time, for each fixed level. -/
theorem parse_polyTime (q : Bool) (i : ℕ) :
    ComputableInPolyTime (parse q i) encQBF encPrenexQBF := by
  induction i generalizing q with
  | zero => change ComputableInPolyTime (fun φ => PrenexQBF.mk [] φ) _ _; fun_prop
  | succ i ih =>
    have := (ih (!q)).comp (initialBody_polyTime q)
    have := initialVars_polyTime q
    change ComputableInPolyTime (fun φ => PrenexQBF.mk
      (initialVars q φ :: (parse (!q) i (initialBody q φ)).blocks)
      (parse (!q) i (initialBody q φ)).matrix) _ _
    fun_prop

private theorem initial_matrix {φ : QBF ℕ} (h : φ.QuantifierFree) (q : Bool) :
    initialVars q φ = [] ∧ initialBody q φ = φ := by
  cases φ <;> cases q <;> simp_all [initialVars, initialBody]

private theorem initial_opposite (q : Bool) {bs : List (List ℕ)} (h : bs ≠ [])
    (hne : ∀ vs ∈ bs, vs ≠ []) (φ : QBF ℕ) :
    initialVars q (QBF.blocks (!q) bs φ) = [] ∧
      initialBody q (QBF.blocks (!q) bs φ) = QBF.blocks (!q) bs φ := by
  obtain ⟨vs, bs, rfl⟩ := List.exists_cons_of_ne_nil h
  obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil (hne _ List.mem_cons_self)
  cases q <;> exact ⟨rfl, rfl⟩

private theorem initial_block (q : Bool) (vs : List ℕ) {φ : QBF ℕ}
    (h : initialVars q φ = [] ∧ initialBody q φ = φ) :
    initialVars q (if q then QBF.exs vs φ else QBF.alls vs φ) = vs ∧
      initialBody q (if q then QBF.exs vs φ else QBF.alls vs φ) = φ := by
  induction vs with
  | nil => simpa only [QBF.exs, QBF.alls, List.foldr_nil, ite_self] using h
  | cons v vs ih => cases q <;> simpa [QBF.exs, QBF.alls, initialVars, initialBody] using ih

/-- Nonempty alternating blocks with a quantifier-free matrix are recovered exactly.
This is used on the nonempty blocks produced by the hardness reduction. -/
theorem parse_formula (q : Bool) (a : PrenexQBF) (hqf : a.matrix.QuantifierFree)
    (hne : ∀ vs ∈ a.blocks, vs ≠ []) :
    parse q a.blocks.length (a.formula q) = a := by
  obtain ⟨bs, φ⟩ := a
  induction bs generalizing q with
  | nil => rfl
  | cons vs bs ih =>
    have hne' : ∀ b ∈ bs, b ≠ [] := fun b hb => hne b (.tail _ hb)
    have htail : initialVars q (QBF.blocks (!q) bs φ) = [] ∧
        initialBody q (QBF.blocks (!q) bs φ) = QBF.blocks (!q) bs φ :=
      match bs, hne' with
      | [], _ => initial_matrix hqf q
      | _ :: _, hne' => initial_opposite q (List.cons_ne_nil _ _) hne' φ
    have hb := initial_block q vs htail
    have hh : parse (!q) bs.length (QBF.blocks (!q) bs φ) = ⟨bs, φ⟩ := ih (!q) hqf hne'
    have hs : QBF.blocks q (vs :: bs) φ = if q then QBF.exs vs (QBF.blocks (!q) bs φ)
        else QBF.alls vs (QBF.blocks (!q) bs φ) := by cases q <;> rfl
    change parse q (bs.length + 1) (QBF.blocks q (vs :: bs) φ) = ⟨vs :: bs, φ⟩
    rw [hs, parse, hb.1, hb.2, hh]

/-- Writing a prefix of fixed block count is polynomial-time. -/
theorem formula_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → PrenexQBF}
    (hf : ComputableInPolyTime f enc encPrenexQBF) (q : Bool) (i : ℕ)
    (hlen : ∀ a, (f a).blocks.length = i) :
    ComputableInPolyTime (fun a => (f a).formula q) enc encQBF := by
  suffices ∀ (bs : α → List (List ℕ)) (φ : α → QBF ℕ),
      ComputableInPolyTime bs enc (encList (encList encNat)) →
      ComputableInPolyTime φ enc encQBF → (∀ a, (bs a).length = i) →
      ComputableInPolyTime (fun a => QBF.blocks q (bs a) (φ a)) enc encQBF from
    this _ _ (encPrenexQBF_blocks_polyTime hf) (encPrenexQBF_matrix_polyTime hf) hlen
  clear hf hlen f
  induction i generalizing q with
  | zero =>
    intro bs φ _ hm hl
    simpa only [show ∀ a, bs a = [] from fun a => List.length_eq_zero_iff.mp (hl a),
      QBF.blocks] using hm
  | succ i ih =>
    intro bs φ hb hm hl
    have ht := ih (!q) (fun a => (bs a).tail) φ (by fun_prop) hm
      (fun a => by simp only [List.length_tail, hl, Nat.add_sub_cancel])
    have hhead : ComputableInPolyTime (fun a => (bs a).headD []) enc (encList encNat) := by
      fun_prop
    have hsplit a : QBF.blocks q (bs a) (φ a) =
        if q then QBF.exs ((bs a).headD []) (QBF.blocks (!q) (bs a).tail (φ a))
          else QBF.alls ((bs a).headD []) (QBF.blocks (!q) (bs a).tail (φ a)) := by
      cases ha : bs a with
      | nil => exact absurd (ha ▸ hl a) (by simp)
      | cons _ _ => cases q <;> rfl
    simp_rw [hsplit]
    cases q <;> simp only [Bool.not_true, Bool.not_false] at ht ⊢ <;> fun_prop

/-- Check that the first actual quantifier has the requested polarity; a quantifier-free
formula has no first quantifier and is allowed. -/
@[expose] def startsCorrectly (q : Bool) (φ : QBF ℕ) : Bool :=
  decide φ.QuantifierFree || !(initialVars q φ).isEmpty

/-- Testing the initial quantifier polarity is polynomial-time. -/
theorem startsCorrectly_polyTime (q : Bool) :
    ComputableInPolyTime (startsCorrectly q) encQBF encBool := by
  have := computableInPolyTime_decide_quantifierFree
  have := initialVars_polyTime q
  unfold startsCorrectly
  fun_prop

/-- A nonempty initial block starts with the declared polarity. -/
theorem startsCorrectly_formula (a : PrenexQBF) (q : Bool) (h : a.blocks ≠ [])
    (hne : ∀ b ∈ a.blocks, b ≠ []) : startsCorrectly q (a.formula q) = true := by
  obtain ⟨bs, φ⟩ := a
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil h
  obtain ⟨v, b, rfl⟩ := List.exists_cons_of_ne_nil (hne _ List.mem_cons_self)
  cases q <;> simp [startsCorrectly, formula, QBF.blocks, QBF.exs, QBF.alls, initialVars]

end Cslib.Complexity.PrenexQBF

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- True closed prenex QBFs with at most `i` alternating quantifier blocks, existential first.
Empty blocks allow fewer effective blocks. Instances retain the existing `encQBF` encoding.
At level zero this means true closed quantifier-free formulas; hardness is only claimed for
positive levels. This is [Arora–Barak, Example 5.9, display (1), and Exercise 5 §1][AroraBarak07]
and [Goldreich, Exercise 3.7][Goldreich2007DraftR2]. -/
@[expose] def SigmaSAT (i : ℕ) : Set (QBF ℕ) :=
  {φ | PrenexQBF.startsCorrectly true φ = true} ∩
    (PrenexQBF.parse true i) ⁻¹' PrenexQBF.SigmaSAT i

/-- The universal-first dual of `SigmaSAT`, on the existing quantified-formula syntax. -/
@[expose] def PiSAT (i : ℕ) : Set (QBF ℕ) :=
  {φ | PrenexQBF.startsCorrectly false φ = true} ∩
    (PrenexQBF.parse false i) ⁻¹' PrenexQBF.PiSAT i

instance (i : ℕ) : DecidablePred (fun φ => φ ∈ SigmaSAT i) := fun φ =>
  inferInstanceAs (Decidable (PrenexQBF.startsCorrectly true φ = true ∧
    (PrenexQBF.parse true i φ).WellFormed i ∧
    ((PrenexQBF.parse true i φ).formula true).eval (fun _ => false) = true))

instance (i : ℕ) : DecidablePred (fun φ => φ ∈ PiSAT i) := fun φ =>
  inferInstanceAs (Decidable (PrenexQBF.startsCorrectly false φ = true ∧
    (PrenexQBF.parse false i φ).WellFormed i ∧
    ((PrenexQBF.parse false i φ).formula false).eval (fun _ => false) = true))

end Cslib.Complexity
