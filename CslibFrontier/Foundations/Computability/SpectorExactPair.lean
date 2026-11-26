/-
Copyright (c) 2026 Matthew Doty, Vinicius de Padua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Vinicius de Padua
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/TuringDegree.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.KleenePost
public import CslibFrontier.Foundations.Computability.TuringJoin
import CslibFrontier.Foundations.Computability.RecursiveInEvalnPrimrec
import CslibFrontier.Foundations.Data.List.Primrec

/-!
# Spector's exact pair theorem for degrees of sets

Spector proved that every countable ideal of Turing degrees of sets has an exact pair: two sets
`A` and `B` whose common lower bounds among sets are precisely the members of the ideal
[Spector1956] (see also [Soare1987]; original-source locators remain unverified). In particular,
applying the construction to a strictly ascending sequence of sets yields two degrees of sets with
no greatest lower bound, showing that the Turing degrees of sets (and of total functions) do not
form a lattice [KleenePost1954], [Spector1956].

## Scope

Mathlib's `TuringDegree` is the quotient of partial functions `ℕ →. ℕ` under Turing equivalence.
The exact pair construction and non-lattice corollary in this file are proved for **degrees of
sets** (`TuringDegree.IsSetDegree`, represented by `{0, 1}`-valued indicator functions), which
coincide with **degrees of total functions** (`TuringDegree.IsTotalDegree`, represented by total
`f : ℕ → ℕ`) by `TuringDegree.isSetDegree_iff_isTotalDegree`, not for arbitrary partial-function
degrees.

## Main definitions

* `TuringDegree.setDegree`, `TuringDegree.IsSetDegree`, `TuringDegree.IsTotalDegree`: degrees of
  sets and of total functions inside `TuringDegree`.
* `Nat.RecursiveIn.setJoin`, `Nat.RecursiveIn.prefixJoin`: binary and finite-prefix joins of sets
  of natural numbers.
* `Nat.RecursiveIn.diagSet`, `Nat.RecursiveIn.strictAscSeq`: a direct diagonalization operator
  (defined without formalizing the Turing jump operator) and the resulting strictly ascending
  sequence of sets under `≤ᵀ`.
* `TuringDegree.IsSetDegreeIdeal`: ideals inside the degrees of sets.
* `TuringDegree.IsExactPairForSetDegrees`: exact pair predicate for ideals of degrees of sets.

## Main results

* `Nat.RecursiveIn.exists_exactPair_seq`: for every sequence of sets `C : ℕ → Set ℕ`, there exist
  sets `A` and `B` above every finite prefix join `prefixJoin C n` such that every total function
  `f ≤ᵀ A, B` is Turing reducible to `prefixJoin C n` for some `n`.
* `TuringDegree.isSetDegree_iff_isTotalDegree`: degrees of sets coincide with degrees of total
  functions.
* `TuringDegree.spector_exact_pair_setDegrees`: every countable ideal of degrees of sets has an
  exact pair of degrees of sets.
* `TuringDegree.exists_exactPair_strictMono_no_inf`, `TuringDegree.exists_setDegree_no_inf`: any
  strictly increasing sequence of set degrees yields an exact pair with no greatest lower bound, so
  the degrees of sets (equivalently, of total functions) do not form a lattice.

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [C. Spector, *On Degrees of Recursive Unsolvability*][Spector1956]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable
open scoped Computability

namespace Nat.RecursiveIn

/-! ### Helper combinators for total functions recursive in an oracle -/

private theorem bind_pfun (x : Part ℕ) (f : ℕ →. ℕ) : x >>= f = x.bind fun y => f y := rfl

private theorem recursiveIn_add {O : Set (ℕ →. ℕ)} :
    Nat.RecursiveIn O (fun n => n.unpair.1 + n.unpair.2 : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
    (_root_.Primrec.nat_add.comp (_root_.Primrec.fst.comp _root_.Primrec.unpair)
      (_root_.Primrec.snd.comp _root_.Primrec.unpair)))

private theorem recursiveIn_ite_computable {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ → ℕ}
    (hc : Computable c) (hf : Nat.RecursiveIn O (f : ℕ →. ℕ))
    (hg : Nat.RecursiveIn O (g : ℕ →. ℕ)) :
    Nat.RecursiveIn O (fun n => if c n then f n else g n : ℕ → ℕ) := by
  have hnot : Computable (fun n => !(c n)) := _root_.Primrec.not.to_comp.comp hc
  refine (recursiveIn_add.comp ((cond_const hc hf 0).pair (cond_const hnot hg 0))).of_eq fun n => ?_
  cases h : c n <;>
    simp [h, Seq.seq, bind_pfun, PFun.coe_val, Part.bind_some_eq_map, Part.map_some]

private theorem recursiveIn_of_eventually_eq {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ} {L : ℕ}
    (hfg : ∀ n, L ≤ n → f n = g n) (hg : Nat.RecursiveIn O (g : ℕ →. ℕ)) :
    Nat.RecursiveIn O (f : ℕ → ℕ) := by
  let vals : List ℕ := (List.range L).map f
  have hfin : Nat.RecursiveIn O (fun n => vals.getD n 0 : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
      ((_root_.Primrec.list_getD 0).comp (_root_.Primrec.const vals) _root_.Primrec.id))
  have hcond : Computable (fun n : ℕ => decide (n < L)) :=
    (PrimrecRel.comp _root_.Primrec.nat_lt _root_.Primrec.id
      (_root_.Primrec.const L)).decide.to_comp
  refine (recursiveIn_ite_computable hcond hfin hg).of_eq fun n => ?_
  by_cases hn : n < L
  · simp [hn, vals, List.getD_eq_getElem?_getD]
  · simp [hn, hfg n (Nat.le_of_not_lt hn)]

/-! ### Binary and finite-prefix joins of sets -/

/-- The disjoint-union join of two sets of natural numbers, coded by parity. -/
@[expose] def setJoin (A B : Set ℕ) : Set ℕ :=
  {n | bif n.bodd then n.div2 ∈ B else n.div2 ∈ A}

private theorem setJoin_indicator_even (A B : Set ℕ) (n : ℕ) :
    ((setJoin A B).indicator 1 : ℕ → ℕ) (2 * n) = (A.indicator 1 : ℕ → ℕ) n := by
  by_cases h : n ∈ A <;> simp [setJoin, Set.indicator, Nat.bodd_mul, h]

private theorem setJoin_indicator_odd (A B : Set ℕ) (n : ℕ) :
    ((setJoin A B).indicator 1 : ℕ → ℕ) (2 * n + 1) = (B.indicator 1 : ℕ → ℕ) n := by
  by_cases h : n ∈ B <;> simp [setJoin, Set.indicator, Nat.bodd_mul, h]

/-- `A` is Turing reducible to `setJoin A B`. -/
theorem left_le_setJoin (A B : Set ℕ) :
    ((A.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ ((setJoin A B).indicator 1 : ℕ → ℕ) :=
  RecursiveIn.iff_nat.2 <|
    ((Nat.RecursiveIn.oracle_self _).comp_at_even).of_eq fun n => by
      simp [PFun.coe_val, setJoin_indicator_even]

/-- `B` is Turing reducible to `setJoin A B`. -/
theorem right_le_setJoin (A B : Set ℕ) :
    ((B.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ ((setJoin A B).indicator 1 : ℕ → ℕ) :=
  RecursiveIn.iff_nat.2 <|
    ((Nat.RecursiveIn.oracle_self _).comp_at_odd).of_eq fun n => by
      simp [PFun.coe_val, setJoin_indicator_odd]

/-- If `A` and `B` are both Turing reducible to `h`, then `setJoin A B` is reducible to `h`. -/
theorem setJoin_turingReducible {A B : Set ℕ} {h : ℕ →. ℕ}
    (hA : ((A.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ h)
    (hB : ((B.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ h) :
    (((setJoin A B).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ h := by
  have hA' : Nat.RecursiveIn {h} (fun n => A.indicator 1 n.div2 : ℕ → ℕ) :=
    ((RecursiveIn.iff_nat.1 hA).comp Nat.RecursiveIn.div2).of_eq fun _ => Part.bind_some _ _
  have hB' : Nat.RecursiveIn {h} (fun n => B.indicator 1 n.div2 : ℕ → ℕ) :=
    ((RecursiveIn.iff_nat.1 hB).comp Nat.RecursiveIn.div2).of_eq fun _ => Part.bind_some _ _
  refine RecursiveIn.iff_nat.2 <|
    (recursiveIn_ite_computable _root_.Primrec.nat_bodd.to_comp hB' hA').of_eq fun n => ?_
  cases hb : n.bodd
  · by_cases hm : n.div2 ∈ A <;> simp [setJoin, Set.indicator, hb, hm]
  · by_cases hm : n.div2 ∈ B <;> simp [setJoin, Set.indicator, hb, hm]

/-- The finite prefix join of a sequence of sets `C : ℕ → Set ℕ`, coding `C 0, …, C n` into the
first `n + 1` columns via `Nat.pair`. -/
@[expose] def prefixJoin (C : ℕ → Set ℕ) (n : ℕ) : Set ℕ :=
  {p | p.unpair.1 ≤ n ∧ p.unpair.2 ∈ C p.unpair.1}

/-- Each column `C k` with `k ≤ n` is Turing reducible to `prefixJoin C n`. -/
theorem turingReducible_prefixJoin (C : ℕ → Set ℕ) {k n : ℕ} (hk : k ≤ n) :
    (((C k).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ ((prefixJoin C n).indicator 1 : ℕ → ℕ) := by
  have hpair : Nat.RecursiveIn {(((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ)}
      (fun m => Nat.pair k m : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
      (Primrec₂.natPair.comp (_root_.Primrec.const k) _root_.Primrec.id))
  refine RecursiveIn.iff_nat.2 <|
    ((Nat.RecursiveIn.oracle_self _).comp hpair).of_eq fun m => ?_
  by_cases hm : m ∈ C k <;>
    simp [bind_pfun, PFun.coe_val, Part.bind_some, prefixJoin, hk, hm, Set.indicator]

/-- If every `C k` for `k ≤ n` is Turing reducible to `h`, then `prefixJoin C n` is reducible to
`h`. -/
theorem prefixJoin_turingReducible (C : ℕ → Set ℕ) (n : ℕ) {h : ℕ →. ℕ}
    (hh : ∀ k ≤ n, (((C k).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ h) :
    (((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ h := by
  induction n with
  | zero =>
    have h0 : Nat.RecursiveIn {h} (fun p => (C 0).indicator 1 p.unpair.2 : ℕ → ℕ) :=
      ((RecursiveIn.iff_nat.1 (hh 0 le_rfl)).comp Nat.Primrec.right.recursiveIn).of_eq fun _ =>
        Part.bind_some _ _
    have hconst0 : Nat.RecursiveIn {h} (fun _ : ℕ => (0 : ℕ) : ℕ → ℕ) :=
      Nat.Primrec.zero.recursiveIn
    have hc : Computable (fun p : ℕ => decide (p.unpair.1 = 0)) :=
      (PrimrecRel.comp _root_.Primrec.eq (_root_.Primrec.fst.comp _root_.Primrec.unpair)
        (_root_.Primrec.const 0)).decide.to_comp
    refine RecursiveIn.iff_nat.2 <| (recursiveIn_ite_computable hc h0 hconst0).of_eq fun p => ?_
    by_cases hp : p.unpair.1 = 0
    · by_cases hm : p.unpair.2 ∈ C 0 <;> simp [prefixJoin, hp, hm, Set.indicator]
    · simp [prefixJoin, hp, Set.indicator]
  | succ n ih =>
    have hprev : Nat.RecursiveIn {h} (((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) :=
      RecursiveIn.iff_nat.1 (ih fun k hk => hh k (Nat.le_succ_of_le hk))
    have hnext : Nat.RecursiveIn {h} (fun p => (C (n + 1)).indicator 1 p.unpair.2 : ℕ → ℕ) :=
      ((RecursiveIn.iff_nat.1 (hh (n + 1) le_rfl)).comp Nat.Primrec.right.recursiveIn).of_eq
        fun _ => Part.bind_some _ _
    have hconst0 : Nat.RecursiveIn {h} (fun _ : ℕ => (0 : ℕ) : ℕ → ℕ) :=
      Nat.Primrec.zero.recursiveIn
    have hc1 : Computable (fun p : ℕ => decide (p.unpair.1 ≤ n)) :=
      (PrimrecRel.comp _root_.Primrec.nat_le (_root_.Primrec.fst.comp _root_.Primrec.unpair)
        (_root_.Primrec.const n)).decide.to_comp
    have hc2 : Computable (fun p : ℕ => decide (p.unpair.1 = n + 1)) :=
      (PrimrecRel.comp _root_.Primrec.eq (_root_.Primrec.fst.comp _root_.Primrec.unpair)
        (_root_.Primrec.const (n + 1))).decide.to_comp
    have hbranch2 := recursiveIn_ite_computable hc2 hnext hconst0
    refine RecursiveIn.iff_nat.2 <|
      (recursiveIn_ite_computable hc1 hprev hbranch2).of_eq fun p => ?_
    by_cases hp1 : p.unpair.1 ≤ n
    · have hp1' : p.unpair.1 ≤ n + 1 := Nat.le_succ_of_le hp1
      by_cases hm : p.unpair.2 ∈ C p.unpair.1 <;> simp [prefixJoin, hp1, hp1', hm, Set.indicator]
    · by_cases hp2 : p.unpair.1 = n + 1
      · by_cases hm : p.unpair.2 ∈ C (n + 1) <;>
          simp [prefixJoin, hp2, hm, Set.indicator]
      · have hgt : ¬p.unpair.1 ≤ n + 1 := by omega
        simp [prefixJoin, hp1, hp2, hgt, Set.indicator]

/-! ### Finite-extension exact pair construction -/

namespace SpectorExactPair

open Code

open Classical in
private noncomputable def colBit (C : ℕ → Set ℕ) (i : ℕ) : Bool :=
  decide (i.unpair.2 ∈ C i.unpair.1)

private def ValidExt (C : ℕ → Set ℕ) (s : ℕ) (σ σ' : List Bool) : Prop :=
  σ <+: σ' ∧
    ∀ i (hi : i < σ'.length), σ.length ≤ i → i.unpair.1 < s → σ'[i] = colBit C i

private theorem validExt_refl (C : ℕ → Set ℕ) (s : ℕ) (σ : List Bool) : ValidExt C s σ σ :=
  ⟨List.prefix_refl σ, fun _ hi hge => absurd hge (not_le_of_gt hi)⟩

private theorem validExt_trans {C : ℕ → Set ℕ} {s : ℕ} {σ₁ σ₂ σ₃ : List Bool}
    (h12 : ValidExt C s σ₁ σ₂) (h23 : ValidExt C s σ₂ σ₃) : ValidExt C s σ₁ σ₃ := by
  refine ⟨h12.1.trans h23.1, fun i hi hge hcol => ?_⟩
  by_cases hlt : i < σ₂.length
  · rw [← h23.1.getElem hlt]
    exact h12.2 i hlt hge hcol
  · exact h23.2 i hi (Nat.le_of_not_lt hlt) hcol

private theorem validExt_mono_stage {C : ℕ → Set ℕ} {s t : ℕ} {σ σ' : List Bool}
    (hst : s ≤ t) (h : ValidExt C t σ σ') : ValidExt C s σ σ' :=
  ⟨h.1, fun i hi hge hcol => h.2 i hi hge (lt_of_lt_of_le hcol hst)⟩

private noncomputable def pad (C : ℕ → Set ℕ) (σ : List Bool) (n : ℕ) : List Bool :=
  σ ++ (List.range (n - σ.length)).map fun j => colBit C (σ.length + j)

private theorem length_pad (C : ℕ → Set ℕ) (σ : List Bool) (n : ℕ) :
    n ≤ (pad C σ n).length := by
  simp only [pad, List.length_append, List.length_map, List.length_range]
  omega

private theorem validExt_pad (C : ℕ → Set ℕ) (s : ℕ) (σ : List Bool) (n : ℕ) :
    ValidExt C s σ (pad C σ n) := by
  refine ⟨List.prefix_append _ _, fun i hi hge _ => ?_⟩
  simp only [pad] at hi ⊢
  rw [List.getElem_append_right hge]
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.add_sub_cancel' hge]

private structure SplitWitness where
  input : ℕ
  extA : List Bool
  extB : List Bool
  stageA : ℕ
  stageB : ℕ
  outA : ℕ
  outB : ℕ

private def IsSplitWitness (C : ℕ → Set ℕ) (s : ℕ) (σ τ : List Bool) (c d : Code)
    (w : SplitWitness) : Prop :=
  ValidExt C s σ w.extA ∧ ValidExt C s τ w.extB ∧
    w.outA ∈ evaln (KleenePost.bits w.extA) w.stageA c w.input ∧
    w.outB ∈ evaln (KleenePost.bits w.extB) w.stageB d w.input ∧
    w.outA ≠ w.outB

private def Splits (C : ℕ → Set ℕ) (s : ℕ) (σ τ : List Bool) (c d : Code) : Prop :=
  ∃ w : SplitWitness, IsSplitWitness C s σ τ c d w

open Classical in
private noncomputable def step (C : ℕ → Set ℕ) (s : ℕ) (σ τ : List Bool) :
    List Bool × List Bool :=
  let c := ofNat Code s.unpair.1
  let d := ofNat Code s.unpair.2
  if h : Splits C s σ τ c d then
    let w := Classical.choose h
    (pad C w.extA (s + 1), pad C w.extB (s + 1))
  else
    (pad C σ (s + 1), pad C τ (s + 1))

private noncomputable def stage (C : ℕ → Set ℕ) : ℕ → List Bool × List Bool
  | 0 => ([], [])
  | s + 1 => step C s (stage C s).1 (stage C s).2

private theorem validExt_stage_succ (C : ℕ → Set ℕ) (s : ℕ) :
    ValidExt C s (stage C s).1 (stage C (s + 1)).1 ∧
      ValidExt C s (stage C s).2 (stage C (s + 1)).2 := by
  simp only [stage, step]
  split_ifs with h
  · have hw := Classical.choose_spec h
    exact ⟨validExt_trans hw.1 (validExt_pad C s _ _),
      validExt_trans hw.2.1 (validExt_pad C s _ _)⟩
  · exact ⟨validExt_pad C s _ _, validExt_pad C s _ _⟩

private theorem validExt_stage (C : ℕ → Set ℕ) {s t : ℕ} (h : s ≤ t) :
    ValidExt C s (stage C s).1 (stage C t).1 ∧
      ValidExt C s (stage C s).2 (stage C t).2 := by
  induction h with
  | refl => exact ⟨validExt_refl C s _, validExt_refl C s _⟩
  | @step m hst ih =>
    have hsucc := validExt_stage_succ C m
    exact ⟨validExt_trans ih.1 (validExt_mono_stage hst hsucc.1),
      validExt_trans ih.2 (validExt_mono_stage hst hsucc.2)⟩

private theorem length_stage (C : ℕ → Set ℕ) (s : ℕ) :
    s ≤ (stage C s).1.length ∧ s ≤ (stage C s).2.length := by
  cases s with
  | zero => simp [stage]
  | succ s =>
    simp only [stage, step]
    split_ifs
    · exact ⟨length_pad C _ (s + 1), length_pad C _ (s + 1)⟩
    · exact ⟨length_pad C _ (s + 1), length_pad C _ (s + 1)⟩

private noncomputable def limA (C : ℕ → Set ℕ) (n : ℕ) : Bool :=
  (stage C (n + 1)).1.getD n false

private noncomputable def limB (C : ℕ → Set ℕ) (n : ℕ) : Bool :=
  (stage C (n + 1)).2.getD n false

private theorem agrees_limA (C : ℕ → Set ℕ) (s : ℕ) : KleenePost.Agrees (stage C s).1 (limA C) :=
  KleenePost.agrees_of_prefix (idx := fun n => n + 1) (fun h => (validExt_stage C h).1.1)
    (fun i => Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (length_stage C (i + 1)).1) s

private theorem agrees_limB (C : ℕ → Set ℕ) (s : ℕ) : KleenePost.Agrees (stage C s).2 (limB C) :=
  KleenePost.agrees_of_prefix (idx := fun n => n + 1) (fun h => (validExt_stage C h).2.1)
    (fun i => Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (length_stage C (i + 1)).2) s

private theorem agrees_of_prefix_of_agrees {σ σ' : List Bool} {g : ℕ → Bool}
    (hpref : σ <+: σ') (hag : KleenePost.Agrees σ' g) : KleenePost.Agrees σ g := fun i hi => by
  rw [hpref.getElem hi]
  exact hag i (lt_of_lt_of_le hi hpref.length_le)

private theorem compat_limA (C : ℕ → Set ℕ) (s : ℕ) :
    ∀ i, (stage C s).1.length ≤ i → i.unpair.1 < s → limA C i = colBit C i := by
  intro i hge hcol
  let t := max s (i + 1)
  have hst : s ≤ t := le_max_left s (i + 1)
  have hit : i < (stage C t).1.length :=
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right s (i + 1)))
      (length_stage C t).1
  rw [← agrees_limA C t i hit]
  exact (validExt_stage C hst).1.2 i hit hge hcol

private theorem compat_limB (C : ℕ → Set ℕ) (s : ℕ) :
    ∀ i, (stage C s).2.length ≤ i → i.unpair.1 < s → limB C i = colBit C i := by
  intro i hge hcol
  let t := max s (i + 1)
  have hst : s ≤ t := le_max_left s (i + 1)
  have hit : i < (stage C t).2.length :=
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right s (i + 1)))
      (length_stage C t).2
  rw [← agrees_limB C t i hit]
  exact (validExt_stage C hst).2.2 i hit hge hcol

private theorem col_le_lim {C : ℕ → Set ℕ} {g : ℕ → Bool} {L : ℕ} (k : ℕ)
    (hcompat : ∀ i, L ≤ i → i.unpair.1 < k + 1 → g i = colBit C i) :
    (((C k).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ (fun n => (g n).toNat : ℕ → ℕ) := by
  have hpair : Nat.RecursiveIn {(fun n => (g n).toNat : ℕ →. ℕ)}
      (fun m => Nat.pair k m : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
      (Primrec₂.natPair.comp (_root_.Primrec.const k) _root_.Primrec.id))
  have hcolRec : Nat.RecursiveIn {(fun n => (g n).toNat : ℕ →. ℕ)}
      (fun m => (g (Nat.pair k m)).toNat : ℕ → ℕ) :=
    ((Nat.RecursiveIn.oracle_self _).comp hpair).of_eq fun _ => Part.bind_some _ _
  refine RecursiveIn.iff_nat.2 (recursiveIn_of_eventually_eq (L := L) (fun m hm => ?_) hcolRec)
  have hL : L ≤ Nat.pair k m := le_trans hm (Nat.right_le_pair k m)
  have hbit := hcompat (Nat.pair k m) hL (by rw [Nat.unpair_pair]; exact Nat.lt_succ_self k)
  rw [hbit]
  by_cases hmem : m ∈ C k <;> simp [colBit, hmem, Set.indicator]

private theorem prefixJoin_le_limA (C : ℕ → Set ℕ) (n : ℕ) :
    (((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ (fun i => (limA C i).toNat : ℕ → ℕ) :=
  prefixJoin_turingReducible C n fun k _ => col_le_lim k (compat_limA C (k + 1))

private theorem prefixJoin_le_limB (C : ℕ → Set ℕ) (n : ℕ) :
    (((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ (fun i => (limB C i).toNat : ℕ → ℕ) :=
  prefixJoin_turingReducible C n fun k _ => col_le_lim k (compat_limB C (k + 1))

private theorem evaln_sound_agrees {σ : List Bool} {g : ℕ → Bool} {k : ℕ} {c : Code} {x y : ℕ}
    (hag : KleenePost.Agrees σ g) (heval : y ∈ evaln (KleenePost.bits σ) k c x) :
    y ∈ eval (fun n => (g n).toNat : ℕ → ℕ) c x :=
  evaln_sound (fun i hi => by
    simp only [KleenePost.bits, List.getElem_map, hag i (by simpa [KleenePost.bits] using hi),
      PFun.coe_val]
    exact Part.mem_some _) heval

private theorem not_splits_of_eq {C : ℕ → Set ℕ} {f : ℕ → ℕ} {c d : Code}
    (hc : eval (fun n => (limA C n).toNat : ℕ → ℕ) c = (f : ℕ →. ℕ))
    (hd : eval (fun n => (limB C n).toNat : ℕ → ℕ) d = (f : ℕ →. ℕ)) :
    let s := Nat.pair (encode c) (encode d)
    ¬Splits C s (stage C s).1 (stage C s).2 c d := by
  intro s hsp
  have hstep :
      stage C (s + 1) =
        (pad C (Classical.choose hsp).extA (s + 1),
          pad C (Classical.choose hsp).extB (s + 1)) := by
    simp only [stage, step, s, Nat.unpair_pair, ofNat_encode, hsp, ↓reduceDIte]
  have hw := Classical.choose_spec hsp
  have hagA : KleenePost.Agrees (Classical.choose hsp).extA (limA C) :=
    agrees_of_prefix_of_agrees (validExt_pad C (s + 1) _ _).1
      (by simpa [hstep] using agrees_limA C (s + 1))
  have hagB : KleenePost.Agrees (Classical.choose hsp).extB (limB C) :=
    agrees_of_prefix_of_agrees (validExt_pad C (s + 1) _ _).1
      (by simpa [hstep] using agrees_limB C (s + 1))
  have hy1 : (Classical.choose hsp).outA ∈ (f : ℕ →. ℕ) (Classical.choose hsp).input :=
    hc ▸ evaln_sound_agrees hagA hw.2.2.1
  have hy2 : (Classical.choose hsp).outB ∈ (f : ℕ →. ℕ) (Classical.choose hsp).input :=
    hd ▸ evaln_sound_agrees hagB hw.2.2.2.1
  exact hw.2.2.2.2 (Part.mem_unique hy1 hy2)

/-! ### Oracle-relative search in the no-splitting case -/

private def decodeBoolList (a : ℕ) : List Bool :=
  (decode (α := List Bool) a).getD []

private theorem primrec_decodeBoolList : _root_.Primrec decodeBoolList :=
  (_root_.Primrec.option_casesOn _root_.Primrec.decode
    (_root_.Primrec.const ([] : List Bool)) _root_.Primrec.snd.to₂).of_eq fun a => by
    dsimp only [decodeBoolList]
    cases decode (α := List Bool) a <;> rfl

private def checkBitOk (s L : ℕ) (σ : List Bool) (j pj : ℕ) : Bool :=
  if L ≤ j ∧ j.unpair.1 < s then
    match σ[j]? with
    | some b => b == decide (pj = 1)
    | none => false
  else
    true

private theorem primrec_checkBitOk (s L : ℕ) :
    _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => checkBitOk s L q.1.1 q.1.2 q.2) := by
  have hσ : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => q.1.1) :=
    _root_.Primrec.fst.comp _root_.Primrec.fst
  have hj : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => q.1.2) :=
    _root_.Primrec.snd.comp _root_.Primrec.fst
  have hpj : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => q.2) := _root_.Primrec.snd
  have hcond1 : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => decide (L ≤ q.1.2)) :=
    (PrimrecRel.comp _root_.Primrec.nat_le (_root_.Primrec.const L) hj).decide
  have hcond2 : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => decide (q.1.2.unpair.1 < s)) :=
    (PrimrecRel.comp _root_.Primrec.nat_lt (_root_.Primrec.fst.comp (_root_.Primrec.unpair.comp hj))
      (_root_.Primrec.const s)).decide
  have hcond : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ =>
      decide (L ≤ q.1.2) && decide (q.1.2.unpair.1 < s)) :=
    _root_.Primrec.and.comp hcond1 hcond2
  have hpjBit : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => decide (q.2 = 1)) :=
    (PrimrecRel.comp _root_.Primrec.eq hpj (_root_.Primrec.const 1)).decide
  have hget : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ => q.1.1[q.1.2]?) :=
    _root_.Primrec.list_getElem?.comp hσ hj
  have hmatch : _root_.Primrec (fun q : (List Bool × ℕ) × ℕ =>
      match q.1.1[q.1.2]? with
      | some b => b == decide (q.2 = 1)
      | none => false) :=
    (_root_.Primrec.option_casesOn hget (_root_.Primrec.const false)
      (_root_.Primrec.beq.comp _root_.Primrec.snd (hpjBit.comp _root_.Primrec.fst)).to₂).of_eq
      fun q => by
        cases q.1.1[q.1.2]? <;> rfl
  exact (_root_.Primrec.cond hcond hmatch (_root_.Primrec.const true)).of_eq fun q => by
    dsimp only [checkBitOk]
    by_cases h1 : L ≤ q.1.2 <;> by_cases h2 : q.1.2.unpair.1 < s <;> simp [h1, h2]

private def checkUpTo (P : ℕ → ℕ) (s L : ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if checkUpTo P s L a j = 0 ∧ checkBitOk s L (decodeBoolList a) j (P j) then 0 else 1

private theorem checkUpTo_eq_zero_iff (P : ℕ → ℕ) (s L : ℕ) (σ : List Bool) (m : ℕ) :
    checkUpTo P s L (encode σ) m = 0 ↔ ∀ j < m, checkBitOk s L σ j (P j) = true := by
  induction m with
  | zero => simp [checkUpTo]
  | succ m ih =>
    simp only [checkUpTo, decodeBoolList, Encodable.encodek, Option.getD_some]
    split_ifs with h
    · refine ⟨fun _ j hj => ?_, fun _ => rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
      · exact ih.1 h.1 j hlt
      · exact h.2
    · refine ⟨fun h1 => h1.elim, fun hall => ?_⟩
      exact (h ⟨ih.2 fun j hj => hall j (Nat.lt_succ_of_lt hj), hall m (Nat.lt_succ_self m)⟩).elim

private theorem recursiveIn_checkUpTo (P : ℕ → ℕ) (s L : ℕ) :
    Nat.RecursiveIn {(P : ℕ →. ℕ)} (Nat.unpaired (checkUpTo P s L) : ℕ → ℕ) := by
  let stepPrim : ℕ → ℕ := fun r =>
    let q := r.unpair.1
    let pj := r.unpair.2
    let a := q.unpair.1
    let j := q.unpair.2.unpair.1
    let ih := q.unpair.2.unpair.2
    if ih = 0 ∧ checkBitOk s L (decodeBoolList a) j pj then 0 else 1
  have hstepPrim : _root_.Primrec stepPrim := by
    have hq : _root_.Primrec (fun r : ℕ => r.unpair.1) :=
      _root_.Primrec.fst.comp _root_.Primrec.unpair
    have hpj : _root_.Primrec (fun r : ℕ => r.unpair.2) :=
      _root_.Primrec.snd.comp _root_.Primrec.unpair
    have ha : _root_.Primrec (fun r : ℕ => r.unpair.1.unpair.1) :=
      _root_.Primrec.fst.comp (_root_.Primrec.unpair.comp hq)
    have hq2 : _root_.Primrec (fun r : ℕ => r.unpair.1.unpair.2) :=
      _root_.Primrec.snd.comp (_root_.Primrec.unpair.comp hq)
    have hj : _root_.Primrec (fun r : ℕ => r.unpair.1.unpair.2.unpair.1) :=
      _root_.Primrec.fst.comp (_root_.Primrec.unpair.comp hq2)
    have hih : _root_.Primrec (fun r : ℕ => r.unpair.1.unpair.2.unpair.2) :=
      _root_.Primrec.snd.comp (_root_.Primrec.unpair.comp hq2)
    have hih0 : _root_.Primrec (fun r : ℕ => decide (r.unpair.1.unpair.2.unpair.2 = 0)) :=
      (PrimrecRel.comp _root_.Primrec.eq hih (_root_.Primrec.const 0)).decide
    have hbit : _root_.Primrec (fun r : ℕ =>
        checkBitOk s L (decodeBoolList r.unpair.1.unpair.1) r.unpair.1.unpair.2.unpair.1
          r.unpair.2) :=
      (primrec_checkBitOk s L).comp (((primrec_decodeBoolList.comp ha).pair hj).pair hpj)
    exact (_root_.Primrec.cond (_root_.Primrec.and.comp hih0 hbit)
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).of_eq fun r => by
      dsimp only [stepPrim]
      by_cases h1 : r.unpair.1.unpair.2.unpair.2 = 0 <;>
        by_cases h2 : checkBitOk s L (decodeBoolList r.unpair.1.unpair.1)
          r.unpair.1.unpair.2.unpair.1 r.unpair.2 = true <;>
        simp [h1, h2]
  have hjProj : Nat.RecursiveIn {(P : ℕ →. ℕ)} (fun q : ℕ => q.unpair.2.unpair.1 : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
      (_root_.Primrec.fst.comp
        (_root_.Primrec.unpair.comp (_root_.Primrec.snd.comp _root_.Primrec.unpair))))
  have hpjRec : Nat.RecursiveIn {(P : ℕ →. ℕ)} (fun q : ℕ => P q.unpair.2.unpair.1 : ℕ → ℕ) :=
    ((Nat.RecursiveIn.oracle_self (P : ℕ →. ℕ)).comp hjProj).of_eq fun _ => Part.bind_some _ _
  have hstep : Nat.RecursiveIn {(P : ℕ →. ℕ)}
      (fun q : ℕ => stepPrim (Nat.pair q (P q.unpair.2.unpair.1)) : ℕ → ℕ) :=
    ((Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1 hstepPrim)).comp
      (Nat.Primrec.id.recursiveIn.pair hpjRec)).of_eq fun _ => by
      simp [Seq.seq, PFun.coe_val, Part.bind_some_eq_map, Part.map_some]
  refine (Nat.RecursiveIn.prec Nat.Primrec.zero.recursiveIn hstep).of_eq fun n => ?_
  simp only [Nat.unpaired, PFun.coe_val]
  generalize n.unpair.1 = a
  induction n.unpair.2 with
  | zero => rfl
  | succ j ih =>
    dsimp only
    rw [ih]
    simp [stepPrim, checkUpTo]

private def primSearchCheck (σ₀ : List Bool) (c : Code) (q : ℕ) : Bool :=
  match decode (α := List Bool × ℕ × ℕ) q.unpair.2 with
  | some p =>
    decide (σ₀ <+: p.1) && decide (evaln (KleenePost.bits p.1) p.2.1 c q.unpair.1 = some p.2.2)
  | none => false

private theorem primrec_primSearchCheck (σ₀ : List Bool) (c : Code) :
    _root_.Primrec (primSearchCheck σ₀ c) := by
  have hx : _root_.Primrec (fun q : ℕ => q.unpair.1) :=
    _root_.Primrec.fst.comp _root_.Primrec.unpair
  have hw : _root_.Primrec (fun q : ℕ => q.unpair.2) :=
    _root_.Primrec.snd.comp _root_.Primrec.unpair
  have hbody : Primrec₂ (fun (q : ℕ) (p : List Bool × ℕ × ℕ) =>
      decide (σ₀ <+: p.1) &&
        decide (evaln (KleenePost.bits p.1) p.2.1 c q.unpair.1 = some p.2.2)) := by
    have hp1 : _root_.Primrec (fun r : ℕ × (List Bool × ℕ × ℕ) => decide (σ₀ <+: r.2.1)) :=
      (PrimrecRel.comp _root_.Primrec.list_isPrefix (_root_.Primrec.const σ₀)
        (_root_.Primrec.fst.comp _root_.Primrec.snd)).decide
    have heval : _root_.Primrec (fun r : ℕ × (List Bool × ℕ × ℕ) =>
        evaln (KleenePost.bits r.2.1) r.2.2.1 c r.1.unpair.1) :=
      primrec_evaln.comp
        ((KleenePost.primrec_bits.comp (_root_.Primrec.fst.comp _root_.Primrec.snd)).pair
          (((_root_.Primrec.fst.comp (_root_.Primrec.snd.comp _root_.Primrec.snd)).pair
            (_root_.Primrec.const c)).pair (hx.comp _root_.Primrec.fst)))
    have hp2 : _root_.Primrec (fun r : ℕ × (List Bool × ℕ × ℕ) =>
        decide (evaln (KleenePost.bits r.2.1) r.2.2.1 c r.1.unpair.1 = some r.2.2.2)) :=
      (PrimrecRel.comp _root_.Primrec.eq heval
        (_root_.Primrec.option_some.comp
          (_root_.Primrec.snd.comp (_root_.Primrec.snd.comp _root_.Primrec.snd)))).decide
    exact _root_.Primrec.and.comp hp1 hp2
  exact (_root_.Primrec.option_casesOn (_root_.Primrec.decode.comp hw)
    (_root_.Primrec.const false) hbody).of_eq fun q => by
    dsimp only [primSearchCheck]
    cases decode (α := List Bool × ℕ × ℕ) q.unpair.2 <;> rfl

private def witnessList (w : ℕ) : List Bool :=
  match decode (α := List Bool × ℕ × ℕ) w with
  | some p => p.1
  | none => []

private theorem primrec_witnessList : _root_.Primrec witnessList :=
  (_root_.Primrec.option_casesOn _root_.Primrec.decode (_root_.Primrec.const ([] : List Bool))
    (_root_.Primrec.fst.comp _root_.Primrec.snd).to₂).of_eq fun w => by
    dsimp only [witnessList]
    cases decode (α := List Bool × ℕ × ℕ) w <;> rfl

private def witnessOut (w : ℕ) : ℕ :=
  match decode (α := List Bool × ℕ × ℕ) w with
  | some p => p.2.2
  | none => 0

private theorem primrec_witnessOut : _root_.Primrec witnessOut :=
  (_root_.Primrec.option_casesOn _root_.Primrec.decode (_root_.Primrec.const 0)
    (_root_.Primrec.snd.comp (_root_.Primrec.snd.comp _root_.Primrec.snd)).to₂).of_eq fun w => by
    dsimp only [witnessOut]
    cases decode (α := List Bool × ℕ × ℕ) w <;> rfl

private theorem validExt_prefix_of_compat {C : ℕ → Set ℕ} {s : ℕ} {σ : List Bool} {g : ℕ → Bool}
    (hag : KleenePost.Agrees σ g) (hcompat : ∀ i, σ.length ≤ i → i.unpair.1 < s → g i = colBit C i)
    {M : ℕ} (hM : σ.length ≤ M) :
    ValidExt C s σ ((List.range M).map g) := by
  refine ⟨?_, fun i hi hge hcol => ?_⟩
  · rw [List.prefix_iff_eq_take]
    exact List.ext_getElem (by simp; omega) fun i h₁ _ => by simp [hag i h₁]
  · simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    exact hcompat i hge hcol

private theorem exists_validExt_evaln {C : ℕ → Set ℕ} {s : ℕ} {σ : List Bool} {g : ℕ → Bool}
    {c : Code} {x y : ℕ} (hag : KleenePost.Agrees σ g)
    (hcompat : ∀ i, σ.length ≤ i → i.unpair.1 < s → g i = colBit C i)
    (heval : y ∈ eval (fun n => (g n).toNat : ℕ → ℕ) c x) :
    ∃ σ' k, ValidExt C s σ σ' ∧ y ∈ evaln (KleenePost.bits σ') k c x := by
  obtain ⟨N, k, hk⟩ := evaln_complete.1 heval
  let M := max N σ.length
  refine ⟨(List.range M).map g, k,
    validExt_prefix_of_compat hag hcompat (le_max_right N σ.length), ?_⟩
  rw [show KleenePost.bits ((List.range M).map g) = prefixOf (fun n => (g n).toNat) M from
    KleenePost.prefixOf_bool_eq_bits _ M]
  exact evaln_mono (prefixOf_prefix _ (le_max_left N σ.length)) le_rfl hk

private theorem turingReducible_prefixJoin_of_no_splits {C : ℕ → Set ℕ} {f : ℕ → ℕ} {c d : Code}
    (hc : eval (fun n => (limA C n).toNat : ℕ → ℕ) c = (f : ℕ →. ℕ))
    (hd : eval (fun n => (limB C n).toNat : ℕ → ℕ) d = (f : ℕ →. ℕ)) :
    let s := Nat.pair (encode c) (encode d)
    (f : ℕ →. ℕ) ≤ᵀ ((prefixJoin C s).indicator 1 : ℕ → ℕ) := by
  intro s
  have hns : ¬Splits C s (stage C s).1 (stage C s).2 c d := not_splits_of_eq hc hd
  set P : ℕ → ℕ := (prefixJoin C s).indicator 1
  set σ₀ : List Bool := (stage C s).1
  set τ₀ : List Bool := (stage C s).2
  have hPbit : ∀ j, j.unpair.1 < s → decide (P j = 1) = colBit C j := fun j hj => by
    have hle : j.unpair.1 ≤ s := Nat.le_of_lt hj
    by_cases hmem : j.unpair.2 ∈ C j.unpair.1 <;>
      simp [P, prefixJoin, hle, hmem, colBit]
  let test : ℕ → ℕ := fun q =>
    (if primSearchCheck σ₀ c q then 0 else 1) +
      checkUpTo P s σ₀.length (encode (witnessList q.unpair.2)) (witnessList q.unpair.2).length
  have htest1 : Nat.RecursiveIn {(P : ℕ →. ℕ)}
      (fun q => if primSearchCheck σ₀ c q then 0 else 1 : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
      ((_root_.Primrec.cond (primrec_primSearchCheck σ₀ c)
        (_root_.Primrec.const 0) (_root_.Primrec.const 1)).of_eq fun q => by
        cases primSearchCheck σ₀ c q <;> rfl))
  have harg2 : Nat.RecursiveIn {(P : ℕ →. ℕ)}
      (fun q => Nat.pair (encode (witnessList q.unpair.2)) (witnessList q.unpair.2).length :
        ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
      (Primrec₂.natPair.comp
        (_root_.Primrec.encode.comp
          (primrec_witnessList.comp (_root_.Primrec.snd.comp _root_.Primrec.unpair)))
        (_root_.Primrec.list_length.comp
          (primrec_witnessList.comp (_root_.Primrec.snd.comp _root_.Primrec.unpair)))))
  have htest2 : Nat.RecursiveIn {(P : ℕ →. ℕ)}
      (fun q => checkUpTo P s σ₀.length (encode (witnessList q.unpair.2))
        (witnessList q.unpair.2).length : ℕ → ℕ) :=
    ((recursiveIn_checkUpTo P s σ₀.length).comp harg2).of_eq fun q => by
      simp [bind_pfun, Nat.unpaired, PFun.coe_val, Part.bind_some]
  have htest : Nat.RecursiveIn {(P : ℕ →. ℕ)} (test : ℕ → ℕ) :=
    (recursiveIn_add.comp (htest1.pair htest2)).of_eq fun q => by
      simp [test, Seq.seq, bind_pfun, PFun.coe_val, Part.bind_some_eq_map, Part.map_some]
  have htest_iff : ∀ x w, test (Nat.pair x w) = 0 ↔
      ∃ p : List Bool × ℕ × ℕ,
        decode (α := List Bool × ℕ × ℕ) w = some p ∧
          ValidExt C s σ₀ p.1 ∧ p.2.2 ∈ evaln (KleenePost.bits p.1) p.2.1 c x := by
    intro x w
    simp only [test, Nat.add_eq_zero_iff, Nat.unpair_pair]
    constructor
    · rintro ⟨h1, h2⟩
      have hprim : primSearchCheck σ₀ c (Nat.pair x w) = true := by
        by_contra hne
        simp [hne] at h1
      cases hw : decode (α := List Bool × ℕ × ℕ) w with
      | none => simp [primSearchCheck, hw] at hprim
      | some p =>
        simp only [primSearchCheck, Nat.unpair_pair, hw, Bool.and_eq_true,
          decide_eq_true_eq] at hprim
        have hwl : witnessList w = p.1 := by simp [witnessList, hw]
        rw [hwl, checkUpTo_eq_zero_iff] at h2
        refine ⟨p, rfl, ⟨hprim.1, fun j hj hge hcol => ?_⟩, hprim.2⟩
        have hok := h2 j hj
        simp only [checkBitOk, hge, hcol, and_self, ↓reduceIte, List.getElem?_eq_getElem hj,
          beq_iff_eq] at hok
        rw [hok, hPbit j hcol]
    · rintro ⟨p, hw, hval, heval⟩
      refine ⟨?_, ?_⟩
      · simp [primSearchCheck, hw, hval.1, Option.mem_def.1 heval]
      · have hwl : witnessList w = p.1 := by simp [witnessList, hw]
        rw [hwl, checkUpTo_eq_zero_iff]
        intro j hj
        dsimp only [checkBitOk]
        split_ifs with hcond
        · simp only [List.getElem?_eq_getElem hj, beq_iff_eq]
          rw [hPbit j hcond.2]
          exact hval.2 j hj hcond.1 hcond.2
        · rfl
  have hrfind : Nat.RecursiveIn {(P : ℕ →. ℕ)}
      (fun x => Nat.rfind fun w => (fun m => m = 0) <$> (test : ℕ →. ℕ) (Nat.pair x w)) :=
    Nat.RecursiveIn.rfind htest
  have hout : Nat.RecursiveIn {(P : ℕ →. ℕ)} (witnessOut : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1 primrec_witnessOut)
  refine RecursiveIn.iff_nat.2 ((hout.comp hrfind).of_eq fun x => ?_)
  have hex : ∃ w, test (Nat.pair x w) = 0 := by
    have hfx : f x ∈ eval (fun n => (limA C n).toNat : ℕ → ℕ) c x := by
      rw [hc, PFun.coe_val]; exact Part.mem_some _
    obtain ⟨σ', k, hvalA, hevalA⟩ :=
      exists_validExt_evaln (agrees_limA C s) (compat_limA C s) hfx
    exact ⟨encode (σ', k, f x),
      (htest_iff x _).2 ⟨(σ', k, f x), Encodable.encodek _, hvalA, hevalA⟩⟩
  have hdom : (Nat.rfind fun w => (fun m => m = 0) <$> (test : ℕ →. ℕ) (Nat.pair x w)).Dom :=
    Nat.rfind_dom.2 (let ⟨w, hw⟩ := hex; ⟨w, by simp [PFun.coe_val, hw], fun _ => trivial⟩)
  set w := (Nat.rfind fun w => (fun m => m = 0) <$> (test : ℕ →. ℕ) (Nat.pair x w)).get hdom
  have hwmem : w ∈ Nat.rfind fun w => (fun m => m = 0) <$> (test : ℕ →. ℕ) (Nat.pair x w) :=
    Part.get_mem hdom
  have hw0 : test (Nat.pair x w) = 0 := by
    have htrue := (Nat.mem_rfind.1 hwmem).1
    simpa [PFun.coe_val] using htrue
  obtain ⟨p, hwdec, hvalA, hevalA⟩ := (htest_iff x w).1 hw0
  have hyeq : p.2.2 = f x := by
    by_contra hne
    have hfxB : f x ∈ eval (fun n => (limB C n).toNat : ℕ → ℕ) d x := by
      rw [hd, PFun.coe_val]; exact Part.mem_some _
    obtain ⟨τ', k₂, hvalB, hevalB⟩ :=
      exists_validExt_evaln (agrees_limB C s) (compat_limB C s) hfxB
    exact hns ⟨⟨x, p.1, τ', p.2.1, k₂, p.2.2, f x⟩, hvalA, hvalB, hevalA, hevalB, hne⟩
  have hrf_eq : (Nat.rfind fun w => (fun m => m = 0) <$> (test : ℕ →. ℕ) (Nat.pair x w)) =
      Part.some w := Part.eq_some_iff.2 hwmem
  change (Nat.rfind fun w => (fun m => m = 0) <$> (test : ℕ →. ℕ) (Nat.pair x w)).bind
      (fun u => Part.some (witnessOut u)) = Part.some (f x)
  rw [hrf_eq, Part.bind_some]
  simp [witnessOut, hwdec, hyeq]

end SpectorExactPair

/-- **Spector's exact pair theorem for sequences of sets**: for every sequence `C : ℕ → Set ℕ`,
there exist sets `A` and `B` above every finite prefix join `prefixJoin C n` such that every total
function `f : ℕ → ℕ` Turing reducible to both `A` and `B` is already Turing reducible to
`prefixJoin C n` for some `n`. -/
theorem exists_exactPair_seq (C : ℕ → Set ℕ) :
    ∃ A B : Set ℕ,
      (∀ n, (((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ (A.indicator 1 : ℕ → ℕ) ∧
        (((prefixJoin C n).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ)) ∧
      ∀ f : ℕ → ℕ,
        (f : ℕ →. ℕ) ≤ᵀ (A.indicator 1 : ℕ → ℕ) →
        (f : ℕ →. ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ) →
        ∃ n, (f : ℕ →. ℕ) ≤ᵀ ((prefixJoin C n).indicator 1 : ℕ → ℕ) := by
  refine ⟨{n | SpectorExactPair.limA C n = true}, {n | SpectorExactPair.limB C n = true}, ?_, ?_⟩
  · rw [KleenePost.indicator_eq, KleenePost.indicator_eq]
    exact fun n => ⟨SpectorExactPair.prefixJoin_le_limA C n,
      SpectorExactPair.prefixJoin_le_limB C n⟩
  · rw [KleenePost.indicator_eq, KleenePost.indicator_eq]
    intro f hA hB
    obtain ⟨c, hc⟩ := Code.turingReducible_iff_exists_code.1 hA
    obtain ⟨d, hd⟩ := Code.turingReducible_iff_exists_code.1 hB
    exact ⟨Nat.pair (encode c) (encode d),
      SpectorExactPair.turingReducible_prefixJoin_of_no_splits hc hd⟩

/-! ### Strictly ascending sequence of sets via direct diagonalization -/

/-- A diagonal set that is not Turing reducible to `S`: `n ∈ diagSet S` iff the `n`-th oracle code
relative to `S` does not output `1` on input `n`. -/
@[expose] def diagSet (S : Set ℕ) : Set ℕ :=
  {n | ¬(1 ∈ Code.eval (S.indicator 1 : ℕ → ℕ) (ofNat Code n) n)}

/-- `diagSet S` is never Turing reducible to `S`. -/
theorem not_diagSet_turingReducible (S : Set ℕ) :
    ¬(((diagSet S).indicator 1 : ℕ → ℕ) : ℕ →. ℕ) ≤ᵀ (S.indicator 1 : ℕ → ℕ) := by
  intro h
  obtain ⟨c, hc⟩ := Code.turingReducible_iff_exists_code.1 h
  have hval := congrFun hc (encode c)
  by_cases hm : encode c ∈ diagSet S
  · have h1 : 1 ∈ Code.eval (S.indicator 1 : ℕ → ℕ) c (encode c) := by
      rw [hval, PFun.coe_val, Set.indicator_of_mem hm]
      exact Part.mem_some 1
    exact hm (by simpa [ofNat_encode] using h1)
  · apply hm
    intro h1
    rw [ofNat_encode, hval, PFun.coe_val, Set.indicator_of_notMem hm] at h1
    exact Nat.one_ne_zero (Part.mem_some_iff.1 h1)

/-- A strictly ascending sequence of sets under Turing reducibility, defined directly by iterated
joining with `diagSet` without formalizing the Turing jump operator. -/
@[expose] def strictAscSeq : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 => setJoin (strictAscSeq n) (diagSet (strictAscSeq n))

end Nat.RecursiveIn

/-! ### Degrees of sets, countable ideals, and the non-lattice corollaries -/

namespace TuringDegree

open Nat.RecursiveIn

/-- The Turing degree of a set `A : Set ℕ`, represented by its `{0, 1}`-valued indicator
function. -/
@[expose] noncomputable def setDegree (A : Set ℕ) : TuringDegree :=
  toAntisymmetrization _ (A.indicator 1 : ℕ → ℕ)

/-- A Turing degree is a *degree of a set* if it is represented by the indicator function of some
set `A : Set ℕ`. -/
@[expose] def IsSetDegree (d : TuringDegree) : Prop :=
  ∃ A : Set ℕ, d = setDegree A

/-- A Turing degree is a *degree of a total function* if it is represented by some total function
`f : ℕ → ℕ`. -/
@[expose] def IsTotalDegree (d : TuringDegree) : Prop :=
  ∃ f : ℕ → ℕ, d = toAntisymmetrization _ (f : ℕ →. ℕ)

/-- A Turing degree is a degree of a set if and only if it is a degree of a total function:
every total `f : ℕ → ℕ` is Turing equivalent to the indicator function of its graph. -/
theorem isSetDegree_iff_isTotalDegree {d : TuringDegree} : IsSetDegree d ↔ IsTotalDegree d := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.indicator 1, rfl⟩
  · rintro ⟨f, rfl⟩
    let G : Set ℕ := {p | f p.unpair.1 = p.unpair.2}
    refine ⟨G, le_antisymm ?_ ?_⟩
    · have hflip : Nat.RecursiveIn {(((G.indicator 1 : ℕ → ℕ) : ℕ →. ℕ))}
          (fun m => (decide (m = 0)).toNat : ℕ → ℕ) :=
        Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
          ((_root_.Primrec.dom_bool Bool.toNat).comp
            (PrimrecRel.comp _root_.Primrec.eq _root_.Primrec.id (_root_.Primrec.const 0)).decide))
      have htest : Nat.RecursiveIn {(((G.indicator 1 : ℕ → ℕ) : ℕ →. ℕ))}
          (fun q => (decide (G.indicator 1 q = 0)).toNat : ℕ → ℕ) :=
        (hflip.comp (Nat.RecursiveIn.oracle_self _)).of_eq fun q => by
          simp [bind_pfun, PFun.coe_val, Part.bind_some]
      refine RecursiveIn.iff_nat.2 ((Nat.RecursiveIn.rfind htest).of_eq fun x => ?_)
      refine Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨?_, ?_⟩)
      · simp [PFun.coe_val, G, Set.indicator]
      · intro y hy
        simp [PFun.coe_val, G, Set.indicator, ne_of_gt hy]
    · have hf1 : Nat.RecursiveIn {(f : ℕ →. ℕ)} (fun p => f p.unpair.1 : ℕ → ℕ) :=
        ((Nat.RecursiveIn.oracle_self _).comp
          (Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
            (_root_.Primrec.fst.comp _root_.Primrec.unpair)))).of_eq fun _ => Part.bind_some _ _
      have hp2 : Nat.RecursiveIn {(f : ℕ →. ℕ)} (fun p => p.unpair.2 : ℕ → ℕ) :=
        Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
          (_root_.Primrec.snd.comp _root_.Primrec.unpair))
      have heq_ind : Nat.RecursiveIn {(f : ℕ →. ℕ)}
          (fun n => (decide (n.unpair.1 = n.unpair.2)).toNat : ℕ → ℕ) :=
        Nat.Primrec.recursiveIn (_root_.Primrec.nat_iff.1
          ((_root_.Primrec.dom_bool Bool.toNat).comp
            (PrimrecRel.comp _root_.Primrec.eq
              (_root_.Primrec.fst.comp _root_.Primrec.unpair)
              (_root_.Primrec.snd.comp _root_.Primrec.unpair)).decide))
      refine RecursiveIn.iff_nat.2 ((heq_ind.comp (hf1.pair hp2)).of_eq fun p => ?_)
      by_cases h : f p.unpair.1 = p.unpair.2 <;>
        simp [Seq.seq, bind_pfun, PFun.coe_val, Part.bind_some_eq_map, Part.map_some, G,
          Set.indicator, h]

/-- The Turing degree of `setJoin A B` is the join `setDegree A ⊔ setDegree B`. -/
theorem setDegree_setJoin (A B : Set ℕ) :
    setDegree (setJoin A B) = setDegree A ⊔ setDegree B :=
  le_antisymm
    (setJoin_turingReducible (left_le_join _ _) (right_le_join _ _))
    (sup_le (left_le_setJoin A B) (right_le_setJoin A B))

/-- Degrees of sets are closed under binary joins `⊔`. -/
theorem IsSetDegree.sup {a b : TuringDegree} (ha : IsSetDegree a) (hb : IsSetDegree b) :
    IsSetDegree (a ⊔ b) := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  exact ⟨setJoin A B, (setDegree_setJoin A B).symm⟩

/-- The `0`-th finite prefix join has the same Turing degree as `C 0`. -/
theorem setDegree_prefixJoin_zero (C : ℕ → Set ℕ) :
    setDegree (prefixJoin C 0) = setDegree (C 0) :=
  le_antisymm
    (prefixJoin_turingReducible C 0 fun k hk => by
      rw [Nat.le_zero.1 hk]
      exact TuringReducible.refl _)
    (turingReducible_prefixJoin C le_rfl)

/-- Extending a finite prefix join by one column takes the Turing join with `C (n + 1)`. -/
theorem setDegree_prefixJoin_succ (C : ℕ → Set ℕ) (n : ℕ) :
    setDegree (prefixJoin C (n + 1)) = setDegree (prefixJoin C n) ⊔ setDegree (C (n + 1)) := by
  refine le_antisymm ?_ ?_
  · refine prefixJoin_turingReducible C (n + 1) fun k hk => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
    · exact (turingReducible_prefixJoin C (Nat.le_of_lt_succ hlt)).trans (left_le_join _ _)
    · exact right_le_join _ _
  · refine sup_le ?_ (turingReducible_prefixJoin C le_rfl)
    exact prefixJoin_turingReducible C n fun k hk =>
      turingReducible_prefixJoin C (Nat.le_succ_of_le hk)

/-- The sequence of set degrees of `strictAscSeq` is strictly increasing. -/
theorem strictMono_setDegree_strictAscSeq :
    StrictMono (fun n => setDegree (strictAscSeq n)) :=
  strictMono_nat_of_lt_succ fun n =>
    lt_of_le_not_ge
      (left_le_setJoin (strictAscSeq n) (diagSet (strictAscSeq n)))
      (fun h => not_diagSet_turingReducible (strictAscSeq n)
        ((right_le_setJoin (strictAscSeq n) (diagSet (strictAscSeq n))).trans h))

/-- An *ideal of degrees of sets* is a nonempty set of degrees of sets that is downward closed
among degrees of sets and closed under binary joins `⊔`. -/
structure IsSetDegreeIdeal (I : Set TuringDegree) : Prop where
  nonempty : I.Nonempty
  subset_setDegrees : ∀ d ∈ I, IsSetDegree d
  lower : ∀ ⦃d₁ d₂⦄, d₁ ∈ I → IsSetDegree d₂ → d₂ ≤ d₁ → d₂ ∈ I
  sup_mem : ∀ ⦃d₁ d₂⦄, d₁ ∈ I → d₂ ∈ I → d₁ ⊔ d₂ ∈ I

/-- `(a, b)` is an *exact pair* for `I` in the degrees of sets if `a` and `b` are degrees of sets
whose common lower bounds among degrees of sets are precisely the elements of `I`. -/
structure IsExactPairForSetDegrees (I : Set TuringDegree) (a b : TuringDegree) : Prop where
  left_isSet : IsSetDegree a
  right_isSet : IsSetDegree b
  mem_iff : ∀ d, IsSetDegree d → (d ∈ I ↔ d ≤ a ∧ d ≤ b)

/-- **Spector's exact pair theorem** for countable ideals of degrees of sets: every countable ideal
`I` of degrees of sets has an exact pair `(a, b)` of degrees of sets. -/
theorem spector_exact_pair_setDegrees {I : Set TuringDegree}
    (hI : IsSetDegreeIdeal I) (hcount : I.Countable) :
    ∃ a b : TuringDegree, IsExactPairForSetDegrees I a b := by
  obtain ⟨g, hg⟩ := hcount.exists_eq_range hI.nonempty
  have hmem : ∀ n, g n ∈ I := fun n => hg ▸ Set.mem_range_self n
  choose C hC using fun n => hI.subset_setDegrees (g n) (hmem n)
  obtain ⟨A, B, hupper, hlower⟩ := exists_exactPair_seq C
  have hpref_mem : ∀ n, setDegree (prefixJoin C n) ∈ I := by
    intro n
    induction n with
    | zero =>
      rw [setDegree_prefixJoin_zero, ← hC 0]
      exact hmem 0
    | succ n ih =>
      rw [setDegree_prefixJoin_succ, ← hC (n + 1)]
      exact hI.sup_mem ih (hmem (n + 1))
  refine ⟨setDegree A, setDegree B, ⟨A, rfl⟩, ⟨B, rfl⟩, fun d hd => ?_⟩
  constructor
  · intro hdI
    rw [hg] at hdI
    obtain ⟨n, rfl⟩ := hdI
    rw [hC n]
    have hle : setDegree (C n) ≤ setDegree (prefixJoin C n) := turingReducible_prefixJoin C le_rfl
    exact ⟨hle.trans (hupper n).1, hle.trans (hupper n).2⟩
  · rintro ⟨hda, hdb⟩
    obtain ⟨D, rfl⟩ := hd
    obtain ⟨n, hn⟩ := hlower (D.indicator 1) hda hdb
    exact hI.lower (hpref_mem n) ⟨D, rfl⟩ hn

/-- If `I` is an ideal of degrees of sets with no greatest element, then any exact pair `(a, b)`
for `I` has no greatest lower bound among degrees of sets. -/
theorem IsExactPairForSetDegrees.no_inf_of_no_top {I : Set TuringDegree} {a b : TuringDegree}
    (hI : IsSetDegreeIdeal I) (hp : IsExactPairForSetDegrees I a b)
    (hnotop : ∀ d ∈ I, ∃ d' ∈ I, d < d') :
    ∀ m, IsSetDegree m → m ≤ a → m ≤ b → ∃ d, IsSetDegree d ∧ d ≤ a ∧ d ≤ b ∧ m < d := by
  intro m hm hma hmb
  obtain ⟨d, hdI, hmd⟩ := hnotop m ((hp.mem_iff m hm).2 ⟨hma, hmb⟩)
  have hd : IsSetDegree d := hI.subset_setDegrees d hdI
  have hdb := (hp.mem_iff d hd).1 hdI
  exact ⟨d, hd, hdb.1, hdb.2, hmd⟩

/-- Any strictly increasing sequence of sets yields two sets `A` and `B` above every member of
the sequence whose degrees have no greatest lower bound among degrees of sets. -/
theorem exists_exactPair_strictMono_no_inf {C : ℕ → Set ℕ}
    (hC : StrictMono fun n => setDegree (C n)) :
    ∃ A B : Set ℕ,
      (∀ n, setDegree (C n) ≤ setDegree A ∧ setDegree (C n) ≤ setDegree B) ∧
      ∀ m, IsSetDegree m → m ≤ setDegree A → m ≤ setDegree B →
        ∃ d, IsSetDegree d ∧ d ≤ setDegree A ∧ d ≤ setDegree B ∧ m < d := by
  obtain ⟨A, B, hupper, hlower⟩ := exists_exactPair_seq C
  refine ⟨A, B, fun n => ?_, fun m hm hma hmb => ?_⟩
  · have hle : setDegree (C n) ≤ setDegree (prefixJoin C n) :=
      turingReducible_prefixJoin C le_rfl
    exact ⟨hle.trans (hupper n).1, hle.trans (hupper n).2⟩
  · obtain ⟨D, rfl⟩ := hm
    obtain ⟨n, hn⟩ := hlower (D.indicator 1) hma hmb
    have hpref_le : setDegree (prefixJoin C n) ≤ setDegree (C n) :=
      prefixJoin_turingReducible C n fun k hk => hC.monotone hk
    have hlt : setDegree D < setDegree (C (n + 1)) :=
      lt_of_le_of_lt (le_trans hn hpref_le) (hC (Nat.lt_succ_self n))
    have hnext_le : setDegree (C (n + 1)) ≤ setDegree (prefixJoin C (n + 1)) :=
      turingReducible_prefixJoin C le_rfl
    exact ⟨setDegree (C (n + 1)), ⟨C (n + 1), rfl⟩,
      hnext_le.trans (hupper (n + 1)).1, hnext_le.trans (hupper (n + 1)).2, hlt⟩

/-- The Turing degrees of sets (equivalently, of total functions) do not form a lattice: there
exist two degrees of sets `a` and `b` with no greatest lower bound among degrees of sets. -/
theorem exists_setDegree_no_inf :
    ∃ a b : TuringDegree, IsSetDegree a ∧ IsSetDegree b ∧
      ∀ m, IsSetDegree m → m ≤ a → m ≤ b →
        ∃ d, IsSetDegree d ∧ d ≤ a ∧ d ≤ b ∧ m < d := by
  obtain ⟨A, B, -, hno⟩ := exists_exactPair_strictMono_no_inf strictMono_setDegree_strictAscSeq
  exact ⟨setDegree A, setDegree B, ⟨A, rfl⟩, ⟨B, rfl⟩, hno⟩

end TuringDegree
