/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.SearchStep
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Data.BinaryBranching
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen

/-!
# Size-sensitive reductions, summed disjoint-instance lists, and live-workspace accumulation

Fine-grained and exact exponential reductions fall into three reusable patterns:

1. **Single-instance size-sensitive reductions (`Cslib.Complexity.SizeSensitiveReduction`):** a
   polynomial-time map `toFun : α → β` with an explicit affine parameter bound
   `μB (toFun a) ≤ scale * μA a + offset`. Keeping `scale` and `offset` separate preserves the
   exact multiplicative rate `scale * δ` when transferring `2 ^ (δ * μB)` bounds, while absorbing
   `2 ^ (δ * offset)` into the leading constant (`SizeSensitiveReduction.decidableInExpTime`,
   `SizeSensitiveReduction.decidableInSubexpTime`) and bounding workspace in terms of input,
   intermediate instance length, and simulated space rather than simulated running time
   (`SizeSensitiveReduction.exists_computableInO_comp`).
2. **Materialized disjoint-instance batches (`Cslib.Complexity.InstanceBatch`,
   `Cslib.Complexity.CNFInstanceBatch`, `Cslib.Complexity.DisjointBatchReduction`):** a batch of
   instances `xs : InstanceBatch β` with summed parameter `xs.sumMeasure μ = (xs.items.map μ).sum`
   processed sequentially via `Turing.MultiTapeTM.ComputableInO.foldl`, together with a capped
   binary counter `Cslib.Complexity.CappedNatAcc` keeping live accumulator bit-length polynomial
   during exact counting sums.
3. **Depth-first stack accumulation (`Cslib.Complexity.StackAccumulationSpec`):** sequential
   depth-first generation and accumulation over up to `2 ^ ν(a)` leaf subinstances without
   materializing the exponentially long output list, abstracting the disjoint-list / sparsification
   search pattern (`Cslib.BinaryBranching`). Time accumulates across all rounds while maximum live
   workspace depends only on the live stack, accumulator, binary round counter, and single-leaf
   solver space.

## Main definitions

* `Cslib.Complexity.SizeSensitiveReduction`: polynomial-time map with
  `μB (f a) ≤ scale * μA a + offset`.
* `Cslib.Complexity.InstanceBatch`, `Cslib.Complexity.CNFInstanceBatch`: instance lists with summed
  parameter measures and `enc_structure`-backed declared-variable CNF batches.
* `Cslib.Complexity.CappedNatAcc`: `enc_structure`-backed capped binary sum accumulator with
  polynomially bounded bit length.
* `Cslib.Complexity.DisjointBatchReduction`: polynomial-time reduction producing an `InstanceBatch`
  with linearly bounded `sumMeasure`.
* `Cslib.Complexity.StackSearchState`, `Cslib.Complexity.StackNodeInput`,
  `Cslib.Complexity.StackCombineInput`, `Cslib.Complexity.StackAccumulationSpec`: depth-first stack
  generation and sequential leaf accumulation with independent time and live-workspace bounds.

## Main results

* `Cslib.Complexity.SizeSensitiveReduction.refl`, `.trans`, `.decidableInExpTime`,
  `.decidableInSubexpTime`, `.exists_computableInO_comp`, `.computableInPolySpace_comp`.
* `Cslib.Complexity.DisjointBatchReduction.exists_computableInO_foldl`,
  `.decidableInExpTime_or`, `.decidableInSubexpTime_or`, `.exists_computableInO_cappedSum`.
* `Cslib.Complexity.StackAccumulationSpec.exists_computableInO_run`,
  `.decidableInExpTime_of_stack`, `.decidableInSubexpTime_of_stack`,
  `.exists_computableInO_cappedSum_of_stack`, `.run_eq_foldl_leafWords`,
  `.run_cappedSum_eq_root`.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Single-instance size-sensitive reductions -/

/-- A **size-sensitive reduction** from `(α, encA, μA)` to `(β, encB, μB)`
[ImpagliazzoPaturiZane2001]: a polynomial-time map `toFun : α → β` with explicit multiplicative
scale `scale` and additive offset `offset` bounding `μB (toFun a) ≤ scale * μA a + offset`. -/
structure SizeSensitiveReduction {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (μA : α → ℕ) (μB : β → ℕ) where
  /-- The instance map. -/
  toFun : α → β
  /-- Multiplicative parameter factor. -/
  scale : ℕ
  /-- Additive parameter offset. -/
  offset : ℕ
  /-- Polynomial-time certificate for `toFun`. -/
  computableInPolyTime_toFun : ComputableInPolyTime toFun encA encB
  /-- Affine parameter bound on reduced instances. -/
  measure_le : ∀ a, μB (toFun a) ≤ scale * μA a + offset

namespace SizeSensitiveReduction

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {μA : α → ℕ} {μB : β → ℕ} {μC : γ → ℕ}

/-- Identity size-sensitive reduction (`scale = 1`, `offset = 0`). -/
@[expose]
def refl (encA : α ↪ List Bool) (μA : α → ℕ) : SizeSensitiveReduction encA encA μA μA where
  toFun := id
  scale := 1
  offset := 0
  computableInPolyTime_toFun := .id'
  measure_le a := by simp

/-- Composition of size-sensitive reductions, multiplying scales and composing offsets. -/
@[expose]
def trans (r : SizeSensitiveReduction encA encB μA μB)
    (s : SizeSensitiveReduction encB encC μB μC) : SizeSensitiveReduction encA encC μA μC where
  toFun := s.toFun ∘ r.toFun
  scale := s.scale * r.scale
  offset := s.scale * r.offset + s.offset
  computableInPolyTime_toFun := s.computableInPolyTime_toFun.comp r.computableInPolyTime_toFun
  measure_le a := by
    have h₁ := s.measure_le (r.toFun a)
    have h₂ := r.measure_le a
    calc μC (s.toFun (r.toFun a))
        ≤ s.scale * μB (r.toFun a) + s.offset := h₁
      _ ≤ s.scale * (r.scale * μA a + r.offset) + s.offset :=
          Nat.add_le_add_right (Nat.mul_le_mul_left s.scale h₂) s.offset
      _ = (s.scale * r.scale) * μA a + (s.scale * r.offset + s.offset) := by ring

@[simp]
theorem refl_toFun (encA : α ↪ List Bool) (μA : α → ℕ) :
    (refl encA μA).toFun = id := rfl

@[simp]
theorem trans_toFun (r : SizeSensitiveReduction encA encB μA μB)
    (s : SizeSensitiveReduction encB encC μB μC) :
    (r.trans s).toFun = s.toFun ∘ r.toFun := rfl

/-- Encoded output length of a size-sensitive reduction is polynomially bounded in encoded input
length. -/
theorem polyBounded_output_length (r : SizeSensitiveReduction encA encB μA μB) :
    PolyBounded (fun a => (encA a).length) (fun a => (encB (r.toFun a)).length) :=
  r.computableInPolyTime_toFun.polyBounded_length

/-- A membership-preserving `SizeSensitiveReduction` induces `PolyTimeReducible`. -/
theorem toPolyTimeReducible (r : SizeSensitiveReduction encA encB μA μB)
    {A : Set α} {B : Set β} (hAB : ∀ a, a ∈ A ↔ r.toFun a ∈ B) :
    PolyTimeReducible encA encB A B :=
  ⟨r.toFun, r.computableInPolyTime_toFun, hAB⟩

/-- A count-preserving `SizeSensitiveReduction` induces `ParsimoniousReducible`. -/
theorem toParsimoniousReducible (r : SizeSensitiveReduction encA encB μA μB)
    {f : α → ℕ} {g : β → ℕ} (hfg : ∀ a, f a = g (r.toFun a)) :
    ParsimoniousReducible encA encB f g :=
  ⟨r.toFun, r.computableInPolyTime_toFun, hfg⟩

/-- **Exact-scale exponential-time transfer.** A decider for `B` within time
`2 ^ (δ * μB b) * poly(|b|)` transfers along `r` to a decider for `A` within time
`2 ^ (r.scale * δ * μA a) * poly(|a|)`, keeping `r.scale * δ` independent of `r.offset`. -/
theorem decidableInExpTime (r : SizeSensitiveReduction encA encB μA μB)
    {A : Set α} {B : Set β} (hAB : ∀ a, a ∈ A ↔ r.toFun a ∈ B)
    {δ : ℝ} (hδ : 0 ≤ δ) (hB : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (r.scale * δ) := by
  obtain ⟨e, h⟩ := hB
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨d, _, hf⟩ := r.computableInPolyTime_toFun.exists_degree
  obtain ⟨l, hl⟩ := hf.inO.length_le_time
  set K : ℝ := 1 + k * 2 ^ (δ * r.offset) * (2 * l + 1) ^ e + k
  refine DecidableInExpTime.of_computableInO (hg.comp hf.inO)
    (fun a => (hAB a).trans (hgB (r.toFun a))) ⌈K⌉₊ (d * (e + 1)) fun a => ?_
  set P : ℝ := ((encA a).length + 1 : ℝ) ^ d
  set X : ℝ := 2 ^ ((r.scale * δ) * μA a)
  have hP : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hexp : (2 : ℝ) ^ (δ * μB (r.toFun a)) ≤ 2 ^ (δ * r.offset) * X := by
    rw [← Real.rpow_add (by norm_num)]
    have hm : (μB (r.toFun a) : ℝ) ≤ r.scale * μA a + r.offset := by exact_mod_cast r.measure_le a
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  push_cast
  rw [pow_mul]
  exact (reduction_add_time_le (C := (2 : ℝ) ^ (δ * r.offset)) hP hX (by positivity)
    ((Nat.cast_le.mpr (hl a)).trans_eq (by simp [P])) hexp (ht (r.toFun a))).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))

/-- **Subexponential-time transfer along a size-sensitive reduction.** -/
theorem decidableInSubexpTime (r : SizeSensitiveReduction encA encB μA μB)
    {A : Set α} {B : Set β} (hAB : ∀ a, a ∈ A ↔ r.toFun a ∈ B)
    (hB : DecidableInSubexpTime B encB μB) : DecidableInSubexpTime A encA μA := by
  intro ε hε
  refine (r.decidableInExpTime hAB (by positivity)
    (hB (ε / (r.scale + 1)) (by positivity))).mono (natCast_mul_div_add_one_le hε.le r.scale)

/-- **Independent time and live-workspace composition.** Composing `g` (`ComputableInO g encB encC
Tg Sg`) with `r` bounds workspace by a polynomial in `|encA a|` plus `Sg (r.toFun a)` (never by
`Tg (r.toFun a)`), so polynomial space transfers without bounding space by simulated time. -/
theorem exists_computableInO_comp (r : SizeSensitiveReduction encA encB μA μB)
    {g : β → γ} {Tg Sg : β → ℕ} (hg : ComputableInO g encB encC Tg Sg)
    (hSg : PolyBounded (fun b => (encB b).length) Sg) :
    ∃ d : ℕ, ∃ S : α → ℕ,
      PolyBounded (fun a => (encA a).length) S ∧
      ComputableInO (g ∘ r.toFun) encA encC
        (fun a => ((encA a).length + 1) ^ d + Tg (r.toFun a)) S := by
  obtain ⟨d, _, hf⟩ := r.computableInPolyTime_toFun.exists_degree
  refine ⟨d, _, ?_, hg.comp hf.inO⟩
  growth_poly [r.polyBounded_output_length]

/-- Polynomial space transfers along any `SizeSensitiveReduction`. -/
theorem computableInPolySpace_comp (r : SizeSensitiveReduction encA encB μA μB)
    {g : β → γ} (hg : ComputableInPolySpace g encB encC) :
    ComputableInPolySpace (g ∘ r.toFun) encA encC :=
  hg.comp (.of_polyTime r.computableInPolyTime_toFun)

end SizeSensitiveReduction

/-! ### Summed parameter lists and capped binary accumulators -/

@[expose] section
/-- A batch of subinstances `items : List α`, used to track summed and maximum parameter measures
across disjoint-instance reductions. -/
@[ext]
structure InstanceBatch (α : Type) where
  /-- The ordered list of subinstances. -/
  items : List α
  deriving DecidableEq, Repr
end

namespace InstanceBatch

variable {α : Type}

/-- The empty batch of subinstances. -/
@[expose] def nil : InstanceBatch α := ⟨[]⟩

/-- A single-element batch. -/
@[expose] def singleton (a : α) : InstanceBatch α := ⟨[a]⟩

/-- Concatenation of two subinstance batches. -/
@[expose] def append (xs ys : InstanceBatch α) : InstanceBatch α := ⟨xs.items ++ ys.items⟩

/-- Number of subinstances in the batch. -/
@[expose] def length (xs : InstanceBatch α) : ℕ := xs.items.length

/-- Summed parameter measure `∑ a ∈ xs.items, μ a`. -/
@[expose] def sumMeasure (μ : α → ℕ) (xs : InstanceBatch α) : ℕ :=
  (xs.items.map μ).sum

/-- Maximum parameter measure `max_{a ∈ xs.items} μ a` (`0` on the empty batch). -/
@[expose] def maxMeasure (μ : α → ℕ) (xs : InstanceBatch α) : ℕ :=
  listMax μ xs.items

@[simp] theorem sumMeasure_nil (μ : α → ℕ) : (nil : InstanceBatch α).sumMeasure μ = 0 := rfl

@[simp] theorem sumMeasure_singleton (μ : α → ℕ) (a : α) :
    (singleton a).sumMeasure μ = μ a := by
  simp [singleton, sumMeasure]

@[simp] theorem sumMeasure_append (μ : α → ℕ) (xs ys : InstanceBatch α) :
    (xs.append ys).sumMeasure μ = xs.sumMeasure μ + ys.sumMeasure μ := by
  simp [append, sumMeasure, List.map_append, List.sum_append]

@[simp] theorem length_nil : (nil : InstanceBatch α).length = 0 := rfl

@[simp] theorem length_singleton (a : α) : (singleton a).length = 1 := rfl

@[simp] theorem length_append (xs ys : InstanceBatch α) :
    (xs.append ys).length = xs.length + ys.length := by
  simp [append, length]

/-- Every subinstance in a batch has measure at most the batch's summed measure. -/
theorem le_sumMeasure_of_mem (μ : α → ℕ) {xs : InstanceBatch α} {a : α} (ha : a ∈ xs.items) :
    μ a ≤ xs.sumMeasure μ :=
  List.single_le_sum (fun _ _ => Nat.zero_le _) (μ a) (List.mem_map_of_mem ha)

/-- The maximum subinstance measure is bounded by the summed measure. -/
theorem maxMeasure_le_sumMeasure (μ : α → ℕ) (xs : InstanceBatch α) :
    xs.maxMeasure μ ≤ xs.sumMeasure μ :=
  listMax_le fun _ ha => le_sumMeasure_of_mem μ ha

end InstanceBatch

/-- Encoding of `InstanceBatch α` as the framed list of its items (`encList encA`). -/
@[expose]
def encInstanceBatch {α : Type} (encA : α ↪ List Bool) : InstanceBatch α ↪ List Bool :=
  (⟨InstanceBatch.items, fun _ _ h => InstanceBatch.ext h⟩ : InstanceBatch α ↪ List α).trans
    (encList encA)

@[simp]
theorem encInstanceBatch_apply {α : Type} (encA : α ↪ List Bool) (xs : InstanceBatch α) :
    encInstanceBatch encA xs = encList encA xs.items := rfl

@[fun_prop]
theorem computableInPolyTime_instanceBatch_items {α γ : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {f : γ → InstanceBatch α}
    (hf : ComputableInPolyTime f encIn (encInstanceBatch encA)) :
    ComputableInPolyTime (fun x => (f x).items) encIn (encList encA) :=
  hf.of_enc_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_instanceBatch_mk {α γ : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {f : γ → List α}
    (hf : ComputableInPolyTime f encIn (encList encA)) :
    ComputableInPolyTime (fun x => InstanceBatch.mk (f x)) encIn (encInstanceBatch encA) :=
  hf.of_enc_eq fun _ => rfl

@[expose] section
/-- A concrete batch of CNF formulas over a shared number `declaredVars` of declared variables,
as produced by disjoint/counting sparsification. -/
@[ext]
structure CNFInstanceBatch where
  /-- Shared number of declared variables `0, …, declaredVars - 1`. -/
  declaredVars : ℕ
  /-- Disjoint subformulas whose satisfying assignments partition or cover the target set. -/
  formulas : List (CNF ℕ)
  deriving DecidableEq, Repr
end

/-- Framed encoding of a `CNFInstanceBatch`: `declaredVars` in unary followed by the framed list of
CNF formulas. -/
enc_structure encCNFInstanceBatch : CNFInstanceBatch where
  declaredVars : encUnary, formulas : (encList encCNF)

namespace CNFInstanceBatch

/-- View a `CNFInstanceBatch` as an `InstanceBatch (CNF ℕ)`. -/
@[expose] def toInstanceBatch (b : CNFInstanceBatch) : InstanceBatch (CNF ℕ) := ⟨b.formulas⟩

/-- Sum of declared-variable model counts across all formulas in `b`. -/
@[expose] noncomputable def totalModelCountOn (b : CNFInstanceBatch) : ℕ :=
  (b.formulas.map fun ψ => ψ.modelCountOn (Finset.range b.declaredVars)).sum

/-- Disjunctive satisfiability across the formulas in `b`. -/
@[expose] def anySatisfiable (b : CNFInstanceBatch) : Prop :=
  ∃ ψ ∈ b.formulas, ψ ∈ SAT

/-- Summed distinct-variable measure across the formulas in `b`. -/
@[expose] def sumNumVars (b : CNFInstanceBatch) : ℕ :=
  b.toInstanceBatch.sumMeasure CNF.numVars

end CNFInstanceBatch

@[expose] section
/-- A capped binary accumulator `(cap, total)` keeping `total ≤ cap` at every step so its encoded
bit-length stays bounded by `O(log₂ cap)` regardless of the number of accumulated terms. -/
@[ext]
structure CappedNatAcc where
  /-- Upper cap on the running sum. -/
  cap : ℕ
  /-- Current capped sum (`total ≤ cap` along initialized runs). -/
  total : ℕ
  deriving DecidableEq, Repr
end

/-- Framed binary encoding of `CappedNatAcc`. -/
enc_structure encCappedNatAcc : CappedNatAcc where
  cap : encNat, total : encNat

namespace CappedNatAcc

/-- Initialize a capped accumulator at `0` with cap `c`. -/
@[expose] def init (c : ℕ) : CappedNatAcc := ⟨c, 0⟩

/-- Add `v` to `acc`, clamping at `acc.cap`. -/
@[expose] def add (acc : CappedNatAcc) (v : ℕ) : CappedNatAcc :=
  ⟨acc.cap, min acc.cap (acc.total + v)⟩

@[simp] theorem init_cap (c : ℕ) : (init c).cap = c := rfl
@[simp] theorem init_total (c : ℕ) : (init c).total = 0 := rfl
@[simp] theorem add_cap (acc : CappedNatAcc) (v : ℕ) : (acc.add v).cap = acc.cap := rfl
@[simp] theorem add_total (acc : CappedNatAcc) (v : ℕ) :
    (acc.add v).total = min acc.cap (acc.total + v) := rfl

theorem add_total_le_cap (acc : CappedNatAcc) (v : ℕ) : (acc.add v).total ≤ acc.cap :=
  Nat.min_le_left _ _

/-- Folding `CappedNatAcc.add` over `xs` preserves `cap` and computes `min cap (acc.total + sum)`.
-/
theorem foldl_add_eq {β : Type} (g : β → ℕ) (xs : List β) (acc : CappedNatAcc)
    (hacc : acc.total ≤ acc.cap) :
    xs.foldl (fun s b => s.add (g b)) acc =
      ⟨acc.cap, min acc.cap (acc.total + (xs.map g).sum)⟩ := by
  induction xs generalizing acc with
  | nil => exact CappedNatAcc.ext rfl (Nat.min_eq_right hacc).symm
  | cons b xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (acc.add (g b)) (acc.add_total_le_cap (g b))]
    exact CappedNatAcc.ext rfl (by simp only [add_cap, add_total]; omega)

/-- Folding `CappedNatAcc.add` from `init c` yields `min c ((xs.map g).sum)`. -/
theorem foldl_add_init_total {β : Type} (g : β → ℕ) (xs : List β) (c : ℕ) :
    (xs.foldl (fun s b => s.add (g b)) (init c)).total = min c ((xs.map g).sum) := by
  simp [foldl_add_eq g xs (init c) (Nat.zero_le c)]

/-- When the true sum does not exceed `c`, the capped fold computes `(xs.map g).sum` exactly. -/
theorem foldl_add_init_total_eq_sum {β : Type} (g : β → ℕ) (xs : List β) {c : ℕ}
    (hsum : (xs.map g).sum ≤ c) :
    (xs.foldl (fun s b => s.add (g b)) (init c)).total = (xs.map g).sum := by
  rw [foldl_add_init_total, Nat.min_eq_right hsum]

/-- Whenever `acc.total ≤ acc.cap` and `acc.cap ≤ 2 ^ k`, the framed binary encoding of `acc` has
length at most `3 * (k + 1) + 2`. -/
theorem length_encCappedNatAcc_le_of_le_two_pow {acc : CappedNatAcc} {k : ℕ}
    (htot : acc.total ≤ acc.cap) (hcap : acc.cap ≤ 2 ^ k) :
    (encCappedNatAcc acc).length ≤ 3 * (k + 1) + 2 := by
  have hc : (encNat acc.cap).length ≤ k + 1 := length_encNat_two_pow k ▸ length_encNat_mono hcap
  have ht : (encNat acc.total).length ≤ k + 1 :=
    length_encNat_two_pow k ▸ length_encNat_mono (htot.trans hcap)
  rw [encCappedNatAcc_apply]
  enc_len [encCappedNatAccFields]

open ComputableInPolyTime in
@[fun_prop]
theorem computableInPolyTime_init {α : Type} {encA : α ↪ List Bool} {c : α → ℕ}
    (hc : ComputableInPolyTime c encA encNat) :
    ComputableInPolyTime (fun a => init (c a)) encA encCappedNatAcc :=
  encCappedNatAcc_mk_polyTime hc (.const 0)

open ComputableInPolyTime in
@[fun_prop]
theorem computableInPolyTime_add :
    ComputableInPolyTime (fun p : CappedNatAcc × ℕ => p.1.add p.2)
      (encPair encCappedNatAcc encNat) encCappedNatAcc := by
  have hsum := binary_add' (encCappedNatAcc_total_polyTime (fst encCappedNatAcc encNat))
    (snd encCappedNatAcc encNat)
  have hcap := encCappedNatAcc_cap_polyTime (fst encCappedNatAcc encNat)
  refine encCappedNatAcc_mk_polyTime hcap
    ((ComputableInPolyTime.ite' (binary_le' hcap hsum) hcap hsum).of_enc_eq fun p => ?_)
  by_cases h : p.1.cap ≤ p.1.total + p.2 <;> simp [h, Nat.min_def]

end CappedNatAcc

private theorem computableInO_cappedAcc_total {α : Type} {encA : α ↪ List Bool}
    {res : α → CappedNatAcc} {countA T₀ S₀ B : α → ℕ}
    (hres : ComputableInO res encA encCappedNatAcc T₀ S₀)
    (hS₀ : PolyBounded (fun a => (encA a).length) S₀)
    (hB_poly : PolyBounded (fun a => (encA a).length) B)
    (hB : ∀ a, (encCappedNatAcc (res a)).length ≤ B a)
    (hcount : ∀ a, (res a).total = countA a) :
    ∃ dtot : ℕ, ∃ Space : α → ℕ,
      PolyBounded (fun a => (encA a).length) Space ∧
      ComputableInO countA encA encNat (fun a => T₀ a + (B a + 1) ^ dtot) Space ∧
      ComputableInPolySpace countA encA encNat := by
  obtain ⟨dtot, _, htot_pt⟩ := (encCappedNatAcc_total_polyTime
    (ComputableInPolyTime.id' (encIn := encCappedNatAcc))).exists_degree
  have hout_raw := (htot_pt.inO.comp hres).of_enc_eq (encC := encNat) (g := countA) fun a => by
    simp only [Function.comp_apply, hcount a]
  have hout : ComputableInO countA encA encNat
      (fun a => T₀ a + (B a + 1) ^ dtot) (fun a => S₀ a + (B a + 1) ^ dtot) :=
    hout_raw.mono_le
      (fun a => Nat.add_le_add_left (Nat.pow_le_pow_left (Nat.add_le_add_right (hB a) 1) dtot) _)
      (fun a => Nat.add_le_add_left (Nat.pow_le_pow_left (Nat.add_le_add_right (hB a) 1) dtot) _)
  have hSpace : PolyBounded (fun a => (encA a).length) (fun a => S₀ a + (B a + 1) ^ dtot) := by
    growth_poly
  exact ⟨dtot, _, hSpace, hout,
    ComputableInPolySpace.of_inSpace hSpace (ComputableInSpace.of_inO hout)⟩

private theorem cast_listMax_le {β : Type} (f : β → ℕ) (xs : List β) {B : ℝ} (hB0 : 0 ≤ B)
    (hf : ∀ b ∈ xs, (f b : ℝ) ≤ B) : (listMax f xs : ℝ) ≤ B := by
  induction xs with
  | nil => simp [listMax, hB0]
  | cons b xs ih =>
    simp only [listMax, List.map_cons, List.foldr_cons, Nat.cast_max]
    exact max_le (hf b (List.mem_cons_self ..))
      (ih fun b' hb' => hf b' (List.mem_cons_of_mem b hb'))

/-! ### Materialized disjoint-instance list reductions with summed measure -/

/-- A polynomial-time reduction mapping each source instance `a : α` to an `InstanceBatch β` whose
summed target measure `sumMeasure μB` is bounded by `scale * μA a + offset`. -/
structure DisjointBatchReduction {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (μA : α → ℕ) (μB : β → ℕ) where
  /-- Batch generator. -/
  toBatch : α → InstanceBatch β
  /-- Multiplicative parameter factor on the summed target measure. -/
  scale : ℕ
  /-- Additive parameter offset on the summed target measure. -/
  offset : ℕ
  /-- Polynomial-time certificate for `toBatch`. -/
  computableInPolyTime_toBatch : ComputableInPolyTime toBatch encA (encInstanceBatch encB)
  /-- Summed measure bound `∑ b ∈ (toBatch a).items, μB b ≤ scale * μA a + offset`. -/
  sumMeasure_le : ∀ a, (toBatch a).sumMeasure μB ≤ scale * μA a + offset

namespace DisjointBatchReduction

variable {α β γ δ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encG : γ ↪ List Bool} {encD : δ ↪ List Bool} {μA : α → ℕ} {μB : β → ℕ}

/-- Every `SizeSensitiveReduction` embeds as a singleton `DisjointBatchReduction` with the same
`scale` and `offset`. -/
@[expose]
def ofSizeSensitive (r : SizeSensitiveReduction encA encB μA μB) :
    DisjointBatchReduction encA encB μA μB where
  toBatch a := InstanceBatch.singleton (r.toFun a)
  scale := r.scale
  offset := r.offset
  computableInPolyTime_toBatch := by
    have hcons : ComputableInPolyTime (fun a => [r.toFun a]) encA (encList encB) :=
      ComputableInPolyTime.cons' r.computableInPolyTime_toFun (.const [])
    exact computableInPolyTime_instanceBatch_mk hcons
  sumMeasure_le a := by
    rw [InstanceBatch.sumMeasure_singleton]
    exact r.measure_le a

/-- Every subinstance in `r.toBatch a` individually satisfies `μB b ≤ r.scale * μA a + r.offset`.
-/
theorem measure_mem_le (r : DisjointBatchReduction encA encB μA μB) (a : α) {b : β}
    (hb : b ∈ (r.toBatch a).items) :
    μB b ≤ r.scale * μA a + r.offset :=
  (InstanceBatch.le_sumMeasure_of_mem μB hb).trans (r.sumMeasure_le a)

/-- Encoded length of the materialized batch `r.toBatch a` is polynomially bounded in `|encA a|`. -/
theorem polyBounded_batch_length (r : DisjointBatchReduction encA encB μA μB) :
    PolyBounded (fun a => (encA a).length)
      (fun a => (encList encB (r.toBatch a).items).length) := by
  simpa only [encInstanceBatch_apply] using r.computableInPolyTime_toBatch.polyBounded_length

private theorem listMax_exp_le (r : DisjointBatchReduction encA encB μA μB)
    {t : β → ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {k e : ℕ}
    (ht : ∀ b, (t b : ℝ) ≤ k * (2 ^ (δ * μB b) * ((encB b).length + 1) ^ e) + k) (a : α) :
    (listMax t (r.toBatch a).items : ℝ) ≤
      k * 2 ^ (δ * r.offset) * 2 ^ ((r.scale * δ) * μA a) *
        (((encList encB (r.toBatch a).items).length : ℝ) + 1) ^ e + k := by
  refine cast_listMax_le t (r.toBatch a).items (by positivity) fun b hb => ?_
  have hexp : (2 : ℝ) ^ (δ * μB b) ≤ 2 ^ (δ * r.offset) * 2 ^ ((r.scale * δ) * μA a) := by
    rw [← Real.rpow_add (by norm_num)]
    have hm : (μB b : ℝ) ≤ r.scale * μA a + r.offset := by exact_mod_cast r.measure_mem_le a hb
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hpow : (((encB b).length : ℝ) + 1) ^ e ≤
      (((encList encB (r.toBatch a).items).length : ℝ) + 1) ^ e :=
    pow_le_pow_left₀ (by positivity)
      (add_le_add_left (Nat.cast_le.mpr (length_le_encList_of_mem encB hb)) 1) e
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul hexp hpow (by positivity) (by positivity))
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith [ht b]

private theorem batch_exp_absorb_le {base itemsLen listLen perItem maxT Cp k e offset : ℕ}
    {δ X P : ℝ} (hP0 : 0 ≤ P) (hX1 : 1 ≤ X)
    (hitems : itemsLen ≤ listLen)
    (hpoly : (base : ℝ) + ((listLen : ℝ) + 1) * ((perItem : ℝ) + ((listLen : ℝ) + 1) ^ e) ≤
      Cp * P)
    (hmax : (maxT : ℝ) ≤ k * 2 ^ (δ * offset) * X * ((listLen : ℝ) + 1) ^ e + k) :
    ((base + (itemsLen + 1) * (perItem + maxT) : ℕ) : ℝ) ≤
      Cp * (1 + k * 2 ^ (δ * offset) + k) * (X * P) := by
  have h0 : (0 : ℝ) ≤ (base : ℝ) + ((listLen : ℝ) + 1) * (perItem : ℝ) := by positivity
  have hl_e : ((listLen : ℝ) + 1) * ((listLen : ℝ) + 1) ^ e ≤ Cp * P := by linarith
  have hl_1 : ((listLen : ℝ) + 1) ≤ Cp * P :=
    (le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg listLen)))).trans hl_e
  have hit_len : ((itemsLen : ℝ) + 1) ≤ (listLen : ℝ) + 1 := mod_cast Nat.add_le_add_right hitems 1
  have hXP : Cp * P ≤ Cp * (X * P) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hP0 hX1) (Nat.cast_nonneg Cp)
  have h₁ : ((itemsLen : ℝ) + 1) * (perItem : ℝ) ≤
      ((listLen : ℝ) + 1) * ((perItem : ℝ) + ((listLen : ℝ) + 1) ^ e) :=
    mul_le_mul hit_len (le_add_of_nonneg_right (by positivity)) (by positivity) (by positivity)
  have h₂ := mul_le_mul hit_len hmax (by positivity) (by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hl_e (by positivity : (0 : ℝ) ≤ k * 2 ^ (δ * offset) * X)
  have h₄ : ((listLen : ℝ) + 1) * k ≤ Cp * k * (X * P) :=
    (mul_le_mul_of_nonneg_right (hl_1.trans hXP) (Nat.cast_nonneg k)).trans_eq
      (mul_right_comm _ _ _)
  push_cast
  linarith

private theorem batch_poly_exp_le (r : DisjointBatchReduction encA encB μA μB)
    {base perItem : α → ℕ} {t : β → ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {k e : ℕ}
    (hbasePoly : PolyBounded (fun a => (encA a).length) base)
    (hperPoly : PolyBounded (fun a => (encA a).length) perItem)
    (ht : ∀ b, (t b : ℝ) ≤ k * (2 ^ (δ * μB b) * ((encB b).length + 1) ^ e) + k) :
    ∃ C₀ E : ℕ, ∀ a,
      ((base a + ((r.toBatch a).length + 1) *
          (perItem a + listMax t (r.toBatch a).items) : ℕ) : ℝ) ≤
        C₀ * (2 ^ ((r.scale * δ) * μA a) * (((encA a).length : ℝ) + 1) ^ E) := by
  let listLen (a : α) : ℕ := (encList encB (r.toBatch a).items).length
  have hpoly : PolyBounded (fun a => (encA a).length)
      (fun a => base a + (listLen a + 1) * (perItem a + (listLen a + 1) ^ e)) := by
    have hll : PolyBounded (fun a => (encA a).length) listLen := r.polyBounded_batch_length
    growth_poly
  obtain ⟨Cp, E, hCp⟩ := hpoly.exists_le
  set K : ℝ := Cp * (1 + k * 2 ^ (δ * r.offset) + k)
  refine ⟨⌈K⌉₊, E, fun a => ?_⟩
  have hCp_a : (base a : ℝ) + ((listLen a : ℝ) + 1) *
      ((perItem a : ℝ) + ((listLen a : ℝ) + 1) ^ e) ≤
        Cp * (((encA a).length : ℝ) + 1) ^ E := by exact_mod_cast hCp a
  have habs := batch_exp_absorb_le (by positivity)
    (Real.one_le_rpow (by norm_num) (by positivity) : 1 ≤ (2 : ℝ) ^ ((r.scale * δ) * μA a))
    (SizedListEncoding.length_le (encA := encB) (encL := encList encB) (r.toBatch a).items)
    hCp_a (r.listMax_exp_le hδ ht a)
  exact habs.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))

private theorem exists_computableInO_foldl_of_ansBound
    (r : DisjointBatchReduction encA encB μA μB)
    {init : α → δ} (hinit : ComputableInPolyTime init encA encD)
    {combine : δ → γ → δ}
    (hcombine : ComputableInPolyTime (fun p : δ × γ => combine p.1 p.2)
      (encPair encD encG) encD)
    {g : β → γ} {Tg Sg : β → ℕ} (hg : ComputableInO g encB encG Tg Sg)
    {accBound ansMax sgMax : α → ℕ}
    (haccPoly : PolyBounded (fun a => (encA a).length) accBound)
    (hansPoly : PolyBounded (fun a => (encA a).length) ansMax)
    (hacc : ∀ a, ∀ i ≤ (r.toBatch a).items.length,
      (encD (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a))).length ≤
        accBound a)
    (hans : ∀ a, ∀ b ∈ (r.toBatch a).items, (encG (g b)).length ≤ ansMax a)
    (hsg : ∀ a, ∀ b ∈ (r.toBatch a).items, Sg b ≤ sgMax a) :
    ∃ c e : ℕ,
      ComputableInO
        (fun a => ((r.toBatch a).items).foldl (fun s b => combine s (g b)) (init a))
        encA encD
        (fun a => c * ((encA a).length + 1) ^ e +
          ((r.toBatch a).length + 1) *
            (c * ((encA a).length + 1) ^ e + listMax Tg (r.toBatch a).items))
        (fun a => c * ((encA a).length + 1) ^ e + sgMax a) := by
  have hlist_pt : ComputableInPolyTime (fun a => (r.toBatch a).items) encA (encList encB) :=
    computableInPolyTime_instanceBatch_items r.computableInPolyTime_toBatch
  obtain ⟨dl, _, hlist⟩ := hlist_pt.exists_degree
  obtain ⟨di, _, hi⟩ := hinit.exists_degree
  obtain ⟨dc, _, hc⟩ := hcombine.exists_degree
  have hstep := hc.inO.comp ((ComputableInO.fst encD encB).prod
    (hg.comp (ComputableInO.snd encD encB)))
  let listLen (a : α) : ℕ := (encList encB (r.toBatch a).items).length
  let pairBound (a : α) : ℕ := 2 * accBound a + listLen a + 1
  let ansPairBound (a : α) : ℕ := 2 * accBound a + ansMax a + 1
  let stepPoly (a : α) : ℕ := 2 * pairBound a + (ansPairBound a + 1) ^ dc
  let R (a : α) : ℕ := stepPoly a + listMax Tg (r.toBatch a).items
  let Q (a : α) : ℕ := stepPoly a + sgMax a
  have hbase (a : α) {i : ℕ} (hi : i < (r.toBatch a).items.length) {F : β → ℕ} {fBound : ℕ}
      (hf : F (r.toBatch a).items[i] ≤ fBound) :
      (encPair encD encB
          (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a),
            (r.toBatch a).items[i])).length +
        ((encPair encD encB
            (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a),
              (r.toBatch a).items[i])).length + F (r.toBatch a).items[i]) +
        ((encPair encD encG
          (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a),
            g (r.toBatch a).items[i])).length + 1) ^ dc ≤
        stepPoly a + fBound := by
    have hblen : (encB (r.toBatch a).items[i]).length ≤ listLen a :=
      length_le_encList_of_mem encB (List.getElem_mem hi)
    have hacc_i := hacc a i hi.le
    have hg_i := hans a _ (List.getElem_mem hi)
    have hp : (encPair encD encB
        (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a),
          (r.toBatch a).items[i])).length ≤ pairBound a := by
      enc_len [pairBound]
    have hp_ans : (encPair encD encG
        (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a),
          g (r.toBatch a).items[i])).length ≤ ansPairBound a := by
      enc_len [ansPairBound]
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hp_ans 1) dc
    dsimp only [stepPoly]
    omega
  have hfold := ComputableInO.foldl (encL := encList encB) hlist.inO hi.inO hstep
    (R := R) (Q := Q) (B := accBound)
    (fun a i hi => hbase a hi (le_listMax (List.getElem_mem hi)))
    (fun a i hi => hbase a hi (hsg a _ (List.getElem_mem hi)))
    hacc
  have hlistPoly : PolyBounded (fun a => (encA a).length) listLen := r.polyBounded_batch_length
  have hOverhead : PolyBounded (fun a => (encA a).length)
      (fun a => ((encA a).length + 1) ^ dl + ((encA a).length + 1) ^ di +
        stepPoly a + accBound a + listLen a) := by
    growth_poly
  obtain ⟨c, e, hce⟩ := hOverhead.exists_le
  refine ⟨c, e, hfold.mono_le (fun a => ?_) (fun a => ?_)⟩
  · have h₁ := hce a
    dsimp only [InstanceBatch.length, R, listLen] at h₁ ⊢
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  · have h₁ := hce a
    dsimp only [Q, listLen] at h₁ ⊢; omega

/-- **Sequential left-fold resource transfer with bounded live workspace.**
Evaluating `g : β → γ` sequentially across `(r.toBatch a).items` and folding answers via a
polynomial-time `combine : δ → γ → δ` whose prefix accumulators stay polynomially bounded in bit
length runs in polynomial live workspace whenever `g` has polynomial workspace `Sg`, and within
accumulated time `O(poly(|a|) + ((r.toBatch a).length + 1) * (poly(|a|) + listMax Tg ...))`. -/
theorem exists_computableInO_foldl (r : DisjointBatchReduction encA encB μA μB)
    {init : α → δ} (hinit : ComputableInPolyTime init encA encD)
    {combine : δ → γ → δ}
    (hcombine : ComputableInPolyTime (fun p : δ × γ => combine p.1 p.2)
      (encPair encD encG) encD)
    {g : β → γ} {Tg Sg : β → ℕ} (hg : ComputableInO g encB encG Tg Sg)
    (hSg : PolyBounded (fun b => (encB b).length) Sg)
    {accBound : α → ℕ} (haccPoly : PolyBounded (fun a => (encA a).length) accBound)
    (hacc : ∀ a, ∀ i ≤ (r.toBatch a).items.length,
      (encD (((r.toBatch a).items.take i).foldl (fun s b => combine s (g b)) (init a))).length ≤
        accBound a) :
    ∃ c e : ℕ, ∃ S : α → ℕ,
      PolyBounded (fun a => (encA a).length) S ∧
      ComputableInO
        (fun a => ((r.toBatch a).items).foldl (fun s b => combine s (g b)) (init a))
        encA encD
        (fun a => c * ((encA a).length + 1) ^ e +
          ((r.toBatch a).length + 1) *
            (c * ((encA a).length + 1) ^ e + listMax Tg (r.toBatch a).items))
        S := by
  obtain ⟨kg, hglen⟩ := hg.length_le
  obtain ⟨cs, ds, hSg_le⟩ := hSg.exists_le
  let sgMax (a : α) : ℕ := cs * ((encList encB (r.toBatch a).items).length + 1) ^ ds
  have hsg_mem (a : α) (b : β) (hb : b ∈ (r.toBatch a).items) : Sg b ≤ sgMax a :=
    (hSg_le b).trans (Nat.mul_le_mul_left cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right (length_le_encList_of_mem encB hb) 1) ds))
  have hansPoly : PolyBounded (fun a => (encA a).length) (fun a => kg * (sgMax a + 1)) := by
    growth_poly [r.polyBounded_batch_length]
  obtain ⟨c, e, hfold⟩ := r.exists_computableInO_foldl_of_ansBound hinit hcombine hg haccPoly
    hansPoly hacc (fun a b hb => (hglen b).trans
      (Nat.mul_le_mul_left kg (Nat.add_le_add_right (hsg_mem a b hb) 1))) hsg_mem
  refine ⟨c, e, _, ?_, hfold⟩
  growth_poly [r.polyBounded_batch_length]

/-- **Exponential-time OR transfer over a summed-measure disjoint-instance batch.**
If `a ∈ A ↔ ∃ b ∈ (r.toBatch a).items, b ∈ B`, then a decider for `B` within time
`2 ^ (δ * μB b) * poly(|b|)` transfers to a decider for `A` within time
`2 ^ (r.scale * δ * μA a) * poly(|a|)`. -/
theorem decidableInExpTime_or (r : DisjointBatchReduction encA encB μA μB)
    {A : Set α} {B : Set β} (hAB : ∀ a, a ∈ A ↔ ∃ b ∈ (r.toBatch a).items, b ∈ B)
    {δ : ℝ} (hδ : 0 ≤ δ) (hB : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (r.scale * δ) := by
  obtain ⟨e, h⟩ := hB
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨c, ef, hfold⟩ := r.exists_computableInO_foldl_of_ansBound (.const false)
    ComputableInPolyTime.bool_or hg (PolyBounded.const 1) (PolyBounded.const 1)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ hb => le_listMax hb)
  have hfold_eq (xs : List β) (acc : Bool) :
      xs.foldl (fun s b => s || g b) acc = (acc || xs.any g) := by
    induction xs generalizing acc with
    | nil => simp
    | cons b xs ih => rw [List.foldl_cons, ih, List.any_cons, Bool.or_assoc]
  obtain ⟨C₀, E, hT⟩ := r.batch_poly_exp_le hδ
    (base := fun a => c * ((encA a).length + 1) ^ ef)
    (perItem := fun a => c * ((encA a).length + 1) ^ ef)
    (by growth_poly) (by growth_poly) ht
  exact DecidableInExpTime.of_computableInO hfold
    (fun a => by simp only [hAB a, hfold_eq, Bool.false_or, List.any_eq_true, ← hgB]) C₀ E hT

/-- **Subexponential-time OR transfer over a summed-measure disjoint-instance batch.** -/
theorem decidableInSubexpTime_or (r : DisjointBatchReduction encA encB μA μB)
    {A : Set α} {B : Set β} (hAB : ∀ a, a ∈ A ↔ ∃ b ∈ (r.toBatch a).items, b ∈ B)
    (hB : DecidableInSubexpTime B encB μB) : DecidableInSubexpTime A encA μA := by
  intro ε hε
  refine (r.decidableInExpTime_or hAB (by positivity)
    (hB (ε / (r.scale + 1)) (by positivity))).mono (natCast_mul_div_add_one_le hε.le r.scale)

/-- **Capped summed-counting transfer with polynomial live workspace.**
When `countA a = ((r.toBatch a).items.map countB).sum ≤ 2 ^ capBits a` with `capBits` computable
in polynomial time in unary, and `countB` has `ComputableInO countB encB encNat Tg Sg` with
`PolyBounded length Sg` and `Tg b ≤ k * (2 ^ (δ * μB b) * (|b| + 1) ^ e) + k`, `countA` is
computable in time `O(2 ^ (r.scale * δ * μA a) * (|a| + 1) ^ E)` AND polynomial live workspace
(`ComputableInPolySpace countA encA encNat`). -/
theorem exists_computableInO_cappedSum (r : DisjointBatchReduction encA encB μA μB)
    {countA : α → ℕ} {countB : β → ℕ} {capBits : α → ℕ}
    (hcap : ComputableInPolyTime capBits encA encUnary)
    (hsum : ∀ a, countA a = ((r.toBatch a).items.map countB).sum)
    (hle : ∀ a, countA a ≤ 2 ^ capBits a)
    {Tg Sg : β → ℕ} (hg : ComputableInO countB encB encNat Tg Sg)
    (hSg : PolyBounded (fun b => (encB b).length) Sg)
    {δ : ℝ} (hδ : 0 ≤ δ) {k e : ℕ}
    (hTg : ∀ b, (Tg b : ℝ) ≤ k * (2 ^ (δ * μB b) * ((encB b).length + 1) ^ e) + k) :
    ∃ T S : α → ℕ, ∃ C₀ E : ℕ,
      PolyBounded (fun a => (encA a).length) S ∧
      ComputableInO countA encA encNat T S ∧
      ComputableInPolySpace countA encA encNat ∧
      ∀ a, (T a : ℝ) ≤
        C₀ * (2 ^ ((r.scale * δ) * μA a) * (((encA a).length : ℝ) + 1) ^ E) + C₀ := by
  have hcapPow : ComputableInPolyTime (fun a => 2 ^ capBits a) encA encNat :=
    ComputableInPolyTime.binary_two_pow.comp hcap
  have hinit : ComputableInPolyTime (fun a => CappedNatAcc.init (2 ^ capBits a))
      encA encCappedNatAcc :=
    CappedNatAcc.computableInPolyTime_init hcapPow
  have haccPoly : PolyBounded (fun a => (encA a).length)
      (fun a => 3 * (capBits a + 1) + 2) := by growth_poly
  have haccBound (a : α) (i : ℕ) (_ : i ≤ (r.toBatch a).items.length) :
      (encCappedNatAcc (((r.toBatch a).items.take i).foldl
        (fun s b => s.add (countB b)) (CappedNatAcc.init (2 ^ capBits a)))).length ≤
        3 * (capBits a + 1) + 2 := by
    rw [CappedNatAcc.foldl_add_eq countB _ _ (Nat.zero_le _)]
    exact CappedNatAcc.length_encCappedNatAcc_le_of_le_two_pow (Nat.min_le_left _ _) le_rfl
  obtain ⟨cf, ef, S₀, hS₀, hfold⟩ := r.exists_computableInO_foldl hinit
    CappedNatAcc.computableInPolyTime_add hg hSg haccPoly haccBound
  obtain ⟨dtot, Space, hSpacePoly, hout, hps⟩ := computableInO_cappedAcc_total hfold hS₀ haccPoly
    (fun a => List.take_length (l := (r.toBatch a).items) ▸ haccBound a _ le_rfl)
    (fun a => (CappedNatAcc.foldl_add_init_total_eq_sum countB _ (hsum a ▸ hle a)).trans
      (hsum a).symm)
  obtain ⟨C₀, E, hT⟩ := r.batch_poly_exp_le hδ
    (base := fun a => cf * ((encA a).length + 1) ^ ef + (3 * (capBits a + 1) + 2 + 1) ^ dtot)
    (perItem := fun a => cf * ((encA a).length + 1) ^ ef)
    (by growth_poly) (by growth_poly) hTg
  refine ⟨_, Space, C₀, E, hSpacePoly, hout, hps, fun a => ?_⟩
  rw [Nat.add_right_comm]
  exact (hT a).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

end DisjointBatchReduction

/-! ### Depth-first stack accumulation over exponentially many disjoint subinstances -/

@[expose] section
/-- State of a depth-first stack accumulation: immutable runtime context `ctx`, live node stack
`stack`, and running answer accumulator `acc`. -/
@[ext]
structure StackSearchState (κ σ δ : Type) where
  /-- Captured runtime context. -/
  ctx : κ
  /-- Pending search nodes (top of stack is head). -/
  stack : List σ
  /-- Running answer accumulator. -/
  acc : δ
  deriving DecidableEq, Repr

/-- Node-inspection input pairing the runtime context with the current top-of-stack node. -/
@[ext]
structure StackNodeInput (κ σ : Type) where
  /-- Captured runtime context. -/
  ctx : κ
  /-- Current node inspected at the top of the stack. -/
  node : σ
  deriving DecidableEq, Repr

/-- Leaf-update input pairing the runtime context, current accumulator, and leaf solver answer. -/
@[ext]
structure StackCombineInput (κ δ γ : Type) where
  /-- Captured runtime context. -/
  ctx : κ
  /-- Current running accumulator. -/
  acc : δ
  /-- Leaf solver output on the popped leaf subinstance. -/
  leafVal : γ
  deriving DecidableEq, Repr
end

/-- Framed encoding of `StackSearchState κ σ δ`. -/
@[expose]
def encStackSearchState {κ σ δ : Type} (encK : κ ↪ List Bool) (encS : σ ↪ List Bool)
    (encD : δ ↪ List Bool) : StackSearchState κ σ δ ↪ List Bool :=
  (⟨fun s => (s.ctx, s.stack, s.acc),
    fun x y h => by cases x; cases y; simp_all⟩ : StackSearchState κ σ δ ↪ _).trans
    (encPair encK (encPair (encList encS) encD))

@[simp]
theorem encStackSearchState_apply {κ σ δ : Type} (encK : κ ↪ List Bool) (encS : σ ↪ List Bool)
    (encD : δ ↪ List Bool) (s : StackSearchState κ σ δ) :
    encStackSearchState encK encS encD s =
      encPair encK (encPair (encList encS) encD) (s.ctx, s.stack, s.acc) := rfl

/-- Framed encoding of `StackNodeInput κ σ`. -/
@[expose]
def encStackNodeInput {κ σ : Type} (encK : κ ↪ List Bool) (encS : σ ↪ List Bool) :
    StackNodeInput κ σ ↪ List Bool :=
  (⟨fun s => (s.ctx, s.node),
    fun x y h => by cases x; cases y; simp_all⟩ : StackNodeInput κ σ ↪ _).trans
    (encPair encK encS)

@[simp]
theorem encStackNodeInput_apply {κ σ : Type} (encK : κ ↪ List Bool) (encS : σ ↪ List Bool)
    (s : StackNodeInput κ σ) :
    encStackNodeInput encK encS s = encPair encK encS (s.ctx, s.node) := rfl

/-- Framed encoding of `StackCombineInput κ δ γ`. -/
@[expose]
def encStackCombineInput {κ δ γ : Type} (encK : κ ↪ List Bool) (encD : δ ↪ List Bool)
    (encG : γ ↪ List Bool) : StackCombineInput κ δ γ ↪ List Bool :=
  (⟨fun s => (s.ctx, s.acc, s.leafVal),
    fun x y h => by cases x; cases y; simp_all⟩ : StackCombineInput κ δ γ ↪ _).trans
    (encPair encK (encPair encD encG))

section StackEncPolyTime

open ComputableInPolyTime

variable {α κ σ δ γ : Type} {encIn : α ↪ List Bool}
  {encK : κ ↪ List Bool} {encS : σ ↪ List Bool} {encD : δ ↪ List Bool} {encG : γ ↪ List Bool}

private theorem stackSearchState_parts :
    ComputableInPolyTime (fun s : StackSearchState κ σ δ => (s.ctx, s.stack, s.acc))
      (encStackSearchState encK encS encD) (encPair encK (encPair (encList encS) encD)) :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_stackSearchState_ctx {f : α → StackSearchState κ σ δ}
    (hf : ComputableInPolyTime f encIn (encStackSearchState encK encS encD)) :
    ComputableInPolyTime (fun a => (f a).ctx) encIn encK :=
  stackSearchState_parts.fst'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackSearchState_stack {f : α → StackSearchState κ σ δ}
    (hf : ComputableInPolyTime f encIn (encStackSearchState encK encS encD)) :
    ComputableInPolyTime (fun a => (f a).stack) encIn (encList encS) :=
  stackSearchState_parts.snd'.fst'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackSearchState_acc {f : α → StackSearchState κ σ δ}
    (hf : ComputableInPolyTime f encIn (encStackSearchState encK encS encD)) :
    ComputableInPolyTime (fun a => (f a).acc) encIn encD :=
  stackSearchState_parts.snd'.snd'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackSearchState_mk
    {c : α → κ} {stk : α → List σ} {ac : α → δ}
    (hc : ComputableInPolyTime c encIn encK)
    (hstk : ComputableInPolyTime stk encIn (encList encS))
    (hac : ComputableInPolyTime ac encIn encD) :
    ComputableInPolyTime (fun a => StackSearchState.mk (c a) (stk a) (ac a))
      encIn (encStackSearchState encK encS encD) :=
  (hc.prod (hstk.prod hac)).of_enc_eq fun _ => rfl

private theorem stackNodeInput_parts :
    ComputableInPolyTime (fun s : StackNodeInput κ σ => (s.ctx, s.node))
      (encStackNodeInput encK encS) (encPair encK encS) :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_stackNodeInput_ctx {f : α → StackNodeInput κ σ}
    (hf : ComputableInPolyTime f encIn (encStackNodeInput encK encS)) :
    ComputableInPolyTime (fun a => (f a).ctx) encIn encK :=
  stackNodeInput_parts.fst'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackNodeInput_node {f : α → StackNodeInput κ σ}
    (hf : ComputableInPolyTime f encIn (encStackNodeInput encK encS)) :
    ComputableInPolyTime (fun a => (f a).node) encIn encS :=
  stackNodeInput_parts.snd'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackNodeInput_mk {c : α → κ} {nd : α → σ}
    (hc : ComputableInPolyTime c encIn encK) (hnd : ComputableInPolyTime nd encIn encS) :
    ComputableInPolyTime (fun a => StackNodeInput.mk (c a) (nd a))
      encIn (encStackNodeInput encK encS) :=
  (hc.prod hnd).of_enc_eq fun _ => rfl

private theorem stackCombineInput_parts :
    ComputableInPolyTime (fun s : StackCombineInput κ δ γ => (s.ctx, s.acc, s.leafVal))
      (encStackCombineInput encK encD encG) (encPair encK (encPair encD encG)) :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_stackCombineInput_ctx {f : α → StackCombineInput κ δ γ}
    (hf : ComputableInPolyTime f encIn (encStackCombineInput encK encD encG)) :
    ComputableInPolyTime (fun a => (f a).ctx) encIn encK :=
  stackCombineInput_parts.fst'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackCombineInput_acc {f : α → StackCombineInput κ δ γ}
    (hf : ComputableInPolyTime f encIn (encStackCombineInput encK encD encG)) :
    ComputableInPolyTime (fun a => (f a).acc) encIn encD :=
  stackCombineInput_parts.snd'.fst'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackCombineInput_leafVal {f : α → StackCombineInput κ δ γ}
    (hf : ComputableInPolyTime f encIn (encStackCombineInput encK encD encG)) :
    ComputableInPolyTime (fun a => (f a).leafVal) encIn encG :=
  stackCombineInput_parts.snd'.snd'.comp hf

@[fun_prop]
theorem computableInPolyTime_stackCombineInput_mk {c : α → κ} {ac : α → δ} {lv : α → γ}
    (hc : ComputableInPolyTime c encIn encK) (hac : ComputableInPolyTime ac encIn encD)
    (hlv : ComputableInPolyTime lv encIn encG) :
    ComputableInPolyTime (fun a => StackCombineInput.mk (c a) (ac a) (lv a))
      encIn (encStackCombineInput encK encD encG) :=
  (hc.prod (hac.prod hlv)).of_enc_eq fun _ => rfl

end StackEncPolyTime

/-- **Depth-first stack accumulation specification.**
Packages a polynomial-time stack generator and accumulator over nodes `σ` producing leaf
subinstances `β` whose solver outputs `γ` are folded into `δ` over `rounds a` binary-counted
iterations without materializing the exponentially long leaf list. -/
structure StackAccumulationSpec {α κ σ β γ δ : Type}
    (encA : α ↪ List Bool) (encK : κ ↪ List Bool) (encS : σ ↪ List Bool)
    (encB : β ↪ List Bool) (encG : γ ↪ List Bool) (encD : δ ↪ List Bool) where
  /-- Fallback node used by `List.headD` on empty stacks (never inspected on active steps). -/
  defaultNode : σ
  /-- Runtime context extracted from input `a`. -/
  initCtx : α → κ
  /-- Initial node stack extracted from input `a`. -/
  initStack : α → List σ
  /-- Initial accumulator extracted from input `a`. -/
  initAcc : α → δ
  /-- Binary round budget for the depth-first traversal. -/
  rounds : α → ℕ
  /-- Leaf test on `(ctx, topNode)`. -/
  isLeaf : StackNodeInput κ σ → Bool
  /-- Leaf subinstance extracted at a leaf node `(ctx, topNode)`. -/
  leafInstance : StackNodeInput κ σ → β
  /-- Children pushed in place of a non-leaf node `(ctx, topNode)`. -/
  expand : StackNodeInput κ σ → List σ
  /-- Accumulator update at a leaf given `(ctx, acc, leafVal)`. -/
  combine : StackCombineInput κ δ γ → δ
  /-- Polynomial-time certificate for `initCtx`. -/
  computableInPolyTime_initCtx : ComputableInPolyTime initCtx encA encK
  /-- Polynomial-time certificate for `initStack`. -/
  computableInPolyTime_initStack : ComputableInPolyTime initStack encA (encList encS)
  /-- Polynomial-time certificate for `initAcc`. -/
  computableInPolyTime_initAcc : ComputableInPolyTime initAcc encA encD
  /-- Polynomial-time certificate for `rounds` in binary (`encNat`). -/
  computableInPolyTime_rounds : ComputableInPolyTime rounds encA encNat
  /-- Polynomial-time certificate for `isLeaf`. -/
  computableInPolyTime_isLeaf : ComputableInPolyTime isLeaf (encStackNodeInput encK encS) encBool
  /-- Polynomial-time certificate for `leafInstance`. -/
  computableInPolyTime_leafInstance :
    ComputableInPolyTime leafInstance (encStackNodeInput encK encS) encB
  /-- Polynomial-time certificate for `expand`. -/
  computableInPolyTime_expand :
    ComputableInPolyTime expand (encStackNodeInput encK encS) (encList encS)
  /-- Polynomial-time certificate for `combine`. -/
  computableInPolyTime_combine :
    ComputableInPolyTime combine (encStackCombineInput encK encD encG) encD

namespace StackAccumulationSpec

variable {α κ σ β γ δ : Type}
  {encA : α ↪ List Bool} {encK : κ ↪ List Bool} {encS : σ ↪ List Bool}
  {encB : β ↪ List Bool} {encG : γ ↪ List Bool} {encD : δ ↪ List Bool}

/-- Initial `StackSearchState` on input `a`. -/
@[expose]
def initState (S : StackAccumulationSpec encA encK encS encB encG encD) (a : α) :
    StackSearchState κ σ δ :=
  ⟨S.initCtx a, S.initStack a, S.initAcc a⟩

/-- Current `(ctx, head)` node pair on top of `st.stack`. -/
@[expose]
def topNode (S : StackAccumulationSpec encA encK encS encB encG encD)
    (st : StackSearchState κ σ δ) : StackNodeInput κ σ :=
  ⟨st.ctx, st.stack.headD S.defaultNode⟩

/-- Whether `st` is at an active leaf step (`st.stack` is nonempty and its head is a leaf). -/
@[expose]
def isActiveLeaf (S : StackAccumulationSpec encA encK encS encB encG encD)
    (st : StackSearchState κ σ δ) : Bool :=
  !st.stack.isEmpty && S.isLeaf (S.topNode st)

/-- One step of depth-first stack accumulation with leaf solver `g : β → γ`. -/
@[expose]
def step (S : StackAccumulationSpec encA encK encS encB encG encD) (g : β → γ)
    (st : StackSearchState κ σ δ) : StackSearchState κ σ δ :=
  if st.stack.isEmpty then st
  else if S.isLeaf (S.topNode st) then
    ⟨st.ctx, st.stack.tail, S.combine ⟨st.ctx, st.acc, g (S.leafInstance (S.topNode st))⟩⟩
  else
    ⟨st.ctx, S.expand (S.topNode st) ++ st.stack.tail, st.acc⟩

/-- Execute `S.rounds a` depth-first steps and return the final accumulator. -/
@[expose]
def run (S : StackAccumulationSpec encA encK encS encB encG encD) (g : β → γ) (a : α) : δ :=
  ((S.step g)^[S.rounds a] (S.initState a)).acc

@[simp]
theorem step_empty (S : StackAccumulationSpec encA encK encS encB encG encD) (g : β → γ)
    (c : κ) (ac : δ) :
    S.step g ⟨c, [], ac⟩ = ⟨c, [], ac⟩ := rfl

theorem iterate_step_empty (S : StackAccumulationSpec encA encK encS encB encG encD) (g : β → γ)
    (c : κ) (ac : δ) (n : ℕ) :
    (S.step g)^[n] ⟨c, [], ac⟩ = ⟨c, [], ac⟩ :=
  Function.iterate_fixed (S.step_empty g c ac) n

theorem iterate_step_ctx (S : StackAccumulationSpec encA encK encS encB encG encD) (g : β → γ)
    (st : StackSearchState κ σ δ) (n : ℕ) :
    ((S.step g)^[n] st).ctx = st.ctx := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    unfold step
    split_ifs <;> rfl

open ComputableInPolyTime in
/-- **Single-step independent time and space bound** via `exists_computableInO_searchStep`. -/
theorem exists_computableInO_step (S : StackAccumulationSpec encA encK encS encB encG encD)
    {g : β → γ} {Tg Sg : β → ℕ} (hg : ComputableInO g encB encG Tg Sg) :
    ∃ d : ℕ, ComputableInO (S.step g)
      (encStackSearchState encK encS encD) (encStackSearchState encK encS encD)
      (fun st => ((encStackSearchState encK encS encD st).length + 1) ^ d +
        if st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true then
          Tg (S.leafInstance (S.topNode st)) +
            ((encStackSearchState encK encS encD st).length +
              (encG (g (S.leafInstance (S.topNode st)))).length + 1) ^ d
        else 0)
      (fun st => ((encStackSearchState encK encS encD st).length + 1) ^ d +
        if st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true then
          Sg (S.leafInstance (S.topNode st)) +
            ((encStackSearchState encK encS encD st).length +
              (encG (g (S.leafInstance (S.topNode st)))).length + 1) ^ d
        else 0) := by
  let encSt := encStackSearchState encK encS encD
  have := S.computableInPolyTime_isLeaf
  have := S.computableInPolyTime_leafInstance
  have := S.computableInPolyTime_expand
  have := S.computableInPolyTime_combine
  have htopNode : ComputableInPolyTime S.topNode encSt (encStackNodeInput encK encS) :=
    computableInPolyTime_stackNodeInput_mk (by fun_prop) (by fun_prop)
  obtain ⟨d, h⟩ := exists_computableInO_searchStep (encS := encSt)
    (done := fun st => st.stack.isEmpty) (isLeaf := fun st => S.isLeaf (S.topNode st))
    (top := fun st => S.leafInstance (S.topNode st))
    (expand := fun st => ⟨st.ctx, S.expand (S.topNode st) ++ st.stack.tail, st.acc⟩)
    (record := fun p => ⟨p.1.ctx, p.1.stack.tail, S.combine ⟨p.1.ctx, p.1.acc, p.2⟩⟩)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hg
  exact ⟨d, h.of_enc_eq fun _ => rfl⟩

private theorem topNode_encLength_le (S : StackAccumulationSpec encA encK encS encB encG encD)
    (st : StackSearchState κ σ δ) :
    (encStackNodeInput encK encS (S.topNode st)).length ≤
      2 * (encStackSearchState encK encS encD st).length + (encS S.defaultNode).length + 2 := by
  cases hstk : st.stack with
  | nil =>
    have hctx_le : (encK st.ctx).length ≤ (encStackSearchState encK encS encD st).length := by
      enc_len [encStackSearchState_apply]
    enc_len [topNode, hstk, List.headD_nil, encStackNodeInput_apply]
  | cons hd tl =>
    have hhd : (encS hd).length ≤ (encList encS (hd :: tl)).length :=
      length_le_encList_of_mem encS (List.mem_cons_self ..)
    have hpair : 2 * (encK st.ctx).length + (encList encS (hd :: tl)).length ≤
        (encStackSearchState encK encS encD st).length := by
      enc_len [encStackSearchState_apply, hstk]
    enc_len [topNode, hstk, List.headD_cons, encStackNodeInput_apply]

private theorem stack_exp_absorb {A_ov B_ov R_cnt leafMax Cp : ℝ} {K₀ K₁ M scale offset k e : ℕ}
    {δ : ℝ} (hδ : 0 ≤ δ) {μ L leafLen : ℕ} {E : ℕ}
    (hCp0 : 0 ≤ Cp) (hB0 : 0 ≤ B_ov) (hleaf0 : 0 ≤ leafMax)
    (hA : A_ov ≤ Cp * ((L : ℝ) + 1) ^ E)
    (hB : B_ov ≤ Cp * ((L : ℝ) + 1) ^ E)
    (hR : R_cnt ≤ (K₀ * 2 ^ K₁ + 1) * 2 ^ ((1 / M : ℝ) * μ))
    (hleaf : leafMax ≤
      k * ((2 : ℝ) ^ (δ * ((scale * μ + offset : ℕ) : ℝ)) * ((leafLen : ℝ) + 1) ^ e) + (k + 1))
    (hll : ((leafLen : ℝ) + 1) ^ e ≤ Cp * ((L : ℝ) + 1) ^ E) :
    A_ov + R_cnt * (B_ov + leafMax) ≤
      (Cp + (K₀ * 2 ^ K₁ + 1) * (Cp + k * 2 ^ (δ * offset) * Cp + (k + 1))) *
        (2 ^ ((1 / M + scale * δ) * μ) * ((L : ℝ) + 1) ^ E) := by
  set P : ℝ := ((L : ℝ) + 1) ^ E
  set X : ℝ := 2 ^ ((1 / M : ℝ) * μ)
  set Y : ℝ := 2 ^ ((scale * δ) * μ)
  have hP1 : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hexp : (2 : ℝ) ^ (δ * ((scale * μ + offset : ℕ) : ℝ)) = 2 ^ (δ * offset) * Y := by
    rw [← Real.rpow_add (by norm_num)]
    exact congrArg (2 ^ ·) (by push_cast; ring)
  have hmul : k * 2 ^ (δ * offset) * Y * ((leafLen : ℝ) + 1) ^ e ≤
      k * 2 ^ (δ * offset) * Cp * Y * P :=
    (mul_le_mul_of_nonneg_left hll (by positivity)).trans_eq (by ring)
  have hleaf' : leafMax ≤ k * 2 ^ (δ * offset) * Cp * Y * P + (k + 1) := by
    rw [hexp, ← mul_assoc] at hleaf
    linarith
  have hXY : (2 : ℝ) ^ ((1 / M + scale * δ) * μ) = X * Y := by
    rw [← Real.rpow_add (by norm_num)]
    exact congrArg (2 ^ ·) (by ring)
  have hround_sum : B_ov + leafMax ≤ (Cp + k * 2 ^ (δ * offset) * Cp + (k + 1)) * (Y * P) := by
    linarith [mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity : 0 ≤ P) hY1) hCp0,
      le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ k + 1)
        (one_le_mul_of_one_le_of_one_le hY1 hP1)]
  have hprod : R_cnt * (B_ov + leafMax) ≤
      (K₀ * 2 ^ K₁ + 1) * (Cp + k * 2 ^ (δ * offset) * Cp + (k + 1)) * (X * Y * P) := by
    linarith [mul_le_mul hR hround_sum (by linarith) (by positivity)]
  have hA_xyp : Cp * P ≤ Cp * (X * Y * P) :=
    mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hX1 hY1)) hCp0
  rw [hXY]
  linarith

private theorem rounds_succ_exp_le {rounds ν μA : α → ℕ} {K₀ K₁ M : ℕ}
    (hrounds : ∀ a, rounds a ≤ K₀ * 2 ^ (ν a)) (hν : ∀ a, ν a ≤ μA a / M + K₁) (a : α) :
    ((rounds a + 1 : ℕ) : ℝ) ≤ (K₀ * 2 ^ K₁ + 1) * 2 ^ ((1 / M : ℝ) * μA a) := by
  have h₁ : rounds a ≤ K₀ * 2 ^ K₁ * 2 ^ (μA a / M) := by
    calc rounds a ≤ K₀ * 2 ^ (ν a) := hrounds a
      _ ≤ K₀ * 2 ^ (μA a / M + K₁) :=
          Nat.mul_le_mul_left K₀ (Nat.pow_le_pow_right two_pos (hν a))
      _ = K₀ * 2 ^ K₁ * 2 ^ (μA a / M) := by rw [pow_add]; ring
  have h₂ : ((2 ^ (μA a / M) : ℕ) : ℝ) ≤ 2 ^ ((1 / M : ℝ) * μA a) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, one_div_mul_eq_div]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) Nat.cast_div_le
  have h₃ : (1 : ℝ) ≤ 2 ^ ((1 / M : ℝ) * μA a) := Real.one_le_rpow (by norm_num) (by positivity)
  have h₄ : (rounds a : ℝ) ≤ (K₀ * 2 ^ K₁ : ℝ) * 2 ^ ((1 / M : ℝ) * μA a) :=
    (show (rounds a : ℝ) ≤ (K₀ * 2 ^ K₁ : ℝ) * ((2 ^ (μA a / M) : ℕ) : ℝ) from mod_cast h₁).trans
      (mul_le_mul_of_nonneg_left h₂ (by positivity))
  rw [Nat.cast_succ]
  linarith

private theorem stack_poly_exp_le
    {α : Type} {encA : α ↪ List Bool} {μA ν rounds leafLen leafMax A_ov B_ov : α → ℕ}
    {K₀ M K₁ scale offset k e : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA_poly : PolyBounded (fun a => (encA a).length) A_ov)
    (hB_poly : PolyBounded (fun a => (encA a).length) B_ov)
    (hleafPoly : PolyBounded (fun a => (encA a).length) leafLen)
    (hrounds : ∀ a, rounds a ≤ K₀ * 2 ^ (ν a))
    (hν : ∀ a, ν a ≤ μA a / M + K₁)
    (hleafMax_le : ∀ a, (leafMax a : ℝ) ≤
      k * ((2 : ℝ) ^ (δ * ((scale * μA a + offset : ℕ) : ℝ)) * ((leafLen a : ℝ) + 1) ^ e) +
        (k + 1)) :
    ∃ C₀ E : ℕ, ∀ a,
      ((A_ov a + (rounds a + 1) * (B_ov a + leafMax a) : ℕ) : ℝ) ≤
        C₀ * (2 ^ ((1 / M + scale * δ) * μA a) * (((encA a).length : ℝ) + 1) ^ E) := by
  have hpoly : PolyBounded (fun a => (encA a).length)
      (fun a => A_ov a + B_ov a + (leafLen a + 1) ^ e) := by growth_poly
  obtain ⟨Cp, E, hCp⟩ := hpoly.exists_le
  set K : ℝ := Cp + (K₀ * 2 ^ K₁ + 1) * (Cp + k * 2 ^ (δ * offset) * Cp + (k + 1))
  refine ⟨⌈K⌉₊, E, fun a => ?_⟩
  have hCp_a := Nat.cast_le (α := ℝ).mpr (hCp a)
  push_cast at hCp_a
  have h0 : (0 : ℝ) ≤ ((leafLen a : ℝ) + 1) ^ e := by positivity
  have hll : ((leafLen a : ℝ) + 1) ^ e ≤ Cp * (((encA a).length : ℝ) + 1) ^ E := by
    linarith [Nat.cast_nonneg (α := ℝ) (A_ov a), Nat.cast_nonneg (α := ℝ) (B_ov a)]
  have habs := stack_exp_absorb (A_ov := A_ov a) hδ (Nat.cast_nonneg Cp)
    (Nat.cast_nonneg (B_ov a)) (Nat.cast_nonneg _)
    (by linarith [Nat.cast_nonneg (α := ℝ) (B_ov a)])
    (by linarith [Nat.cast_nonneg (α := ℝ) (A_ov a)])
    (rounds_succ_exp_le hrounds hν a) (hleafMax_le a) hll
  push_cast at habs ⊢
  exact habs.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))

private theorem step_cost_le (S : StackAccumulationSpec encA encK encS encB encG encD)
    {g : β → γ} {F : β → ℕ} {st : StackSearchState κ σ δ} {stateBound ansBound fBound d : ℕ}
    (hst : (encStackSearchState encK encS encD st).length ≤ stateBound)
    (hans : st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
      (encG (g (S.leafInstance (S.topNode st)))).length ≤ ansBound)
    (hf : st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
      F (S.leafInstance (S.topNode st)) ≤ fBound) :
    ((encStackSearchState encK encS encD st).length + 1) ^ d +
      (if st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true then
        F (S.leafInstance (S.topNode st)) +
          ((encStackSearchState encK encS encD st).length +
            (encG (g (S.leafInstance (S.topNode st)))).length + 1) ^ d
      else 0) ≤
      ((stateBound + 1) ^ d + (stateBound + ansBound + 1) ^ d) + fBound := by
  have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hst 1) d
  split_ifs with hact
  · have hp2 := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hst (hans hact)) 1) d
    have := hf hact
    omega
  · omega

private theorem exists_leafLen_le (S : StackAccumulationSpec encA encK encS encB encG encD)
    {g : β → γ} {stateBound : α → ℕ}
    (hstatePoly : PolyBounded (fun a => (encA a).length) stateBound)
    (hstate : ∀ a, ∀ i ≤ S.rounds a,
      (encStackSearchState encK encS encD ((S.step g)^[i] (S.initState a))).length ≤ stateBound a) :
    ∃ leafLen : α → ℕ, PolyBounded (fun a => (encA a).length) leafLen ∧
      ∀ a, ∀ i ≤ S.rounds a,
        (encB (S.leafInstance (S.topNode ((S.step g)^[i] (S.initState a))))).length ≤
          leafLen a := by
  obtain ⟨cl, dl, hleaf_len⟩ := S.computableInPolyTime_leafInstance.polyBounded_length.exists_le
  let leafLen (a : α) : ℕ :=
    cl * (2 * stateBound a + (encS S.defaultNode).length + 3) ^ dl
  refine ⟨leafLen, by growth_poly, fun a i hi => ?_⟩
  have hst := hstate a i hi
  have htn : (encStackNodeInput encK encS
      (S.topNode ((S.step g)^[i] (S.initState a)))).length ≤
      2 * stateBound a + (encS S.defaultNode).length + 2 :=
    (S.topNode_encLength_le _).trans (by omega)
  exact (hleaf_len _).trans (Nat.mul_le_mul_left cl (Nat.pow_le_pow_left (by omega) dl))

private theorem exists_leafMax_exp_le (S : StackAccumulationSpec encA encK encS encB encG encD)
    {g : β → γ} {Tg : β → ℕ} {μA : α → ℕ} {μB : β → ℕ} {stateBound : α → ℕ}
    (hstatePoly : PolyBounded (fun a => (encA a).length) stateBound)
    {scale offset k e : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hstate : ∀ a, ∀ i ≤ S.rounds a,
      (encStackSearchState encK encS encD ((S.step g)^[i] (S.initState a))).length ≤ stateBound a)
    (hmeas : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step g)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        μB (S.leafInstance (S.topNode st)) ≤ scale * μA a + offset)
    (hTg : ∀ b, (Tg b : ℝ) ≤ k * (2 ^ (δ * μB b) * ((encB b).length + 1) ^ e) + k) :
    ∃ leafLen leafMax : α → ℕ,
      PolyBounded (fun a => (encA a).length) leafLen ∧
      (∀ a, (leafMax a : ℝ) ≤
      k * ((2 : ℝ) ^ (δ * ((scale * μA a + offset : ℕ) : ℝ)) * ((leafLen a : ℝ) + 1) ^ e) +
        (k + 1)) ∧
      (∀ a, ∀ i ≤ S.rounds a,
        let st := (S.step g)^[i] (S.initState a)
        st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
          Tg (S.leafInstance (S.topNode st)) ≤ leafMax a) := by
  obtain ⟨leafLen, hleafPoly, hleafLen⟩ := S.exists_leafLen_le hstatePoly hstate
  let leafMax (a : α) : ℕ :=
    ⌈(k : ℝ) * (2 ^ (δ * ((scale * μA a + offset : ℕ) : ℝ)) * ((leafLen a : ℝ) + 1) ^ e) + k⌉₊
  have hceil (a : α) : (leafMax a : ℝ) ≤
      k * ((2 : ℝ) ^ (δ * ((scale * μA a + offset : ℕ) : ℝ)) * ((leafLen a : ℝ) + 1) ^ e) +
        (k + 1) :=
    (Nat.ceil_lt_add_one (by positivity)).le.trans_eq (add_assoc ..)
  refine ⟨leafLen, leafMax, hleafPoly, hceil, fun a i hi hact => ?_⟩
  set b := S.leafInstance (S.topNode ((S.step g)^[i] (S.initState a)))
  have hexp : (2 : ℝ) ^ (δ * μB b) ≤ 2 ^ (δ * ((scale * μA a + offset : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmeas a i hi hact) hδ)
  have hpow : (((encB b).length : ℝ) + 1) ^ e ≤ ((leafLen a : ℝ) + 1) ^ e := by
    have hblen : (encB b).length ≤ leafLen a := hleafLen a i hi
    gcongr
  refine Nat.cast_le.mp ((hTg b).trans ((?_ : _ ≤ _).trans (Nat.le_ceil _)))
  gcongr

private theorem exists_computableInO_run_of_spaceBound
    (S : StackAccumulationSpec encA encK encS encB encG encD)
    {g : β → γ} {Tg Sg : β → ℕ} (hg : ComputableInO g encB encG Tg Sg)
    {stateBound ansBound leafMax sgBound : α → ℕ}
    (hstatePoly : PolyBounded (fun a => (encA a).length) stateBound)
    (hansPoly : PolyBounded (fun a => (encA a).length) ansBound)
    (hstate : ∀ a, ∀ i ≤ S.rounds a,
      (encStackSearchState encK encS encD ((S.step g)^[i] (S.initState a))).length ≤ stateBound a)
    (hans : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step g)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        (encG (g (S.leafInstance (S.topNode st)))).length ≤ ansBound a)
    (htime : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step g)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        Tg (S.leafInstance (S.topNode st)) ≤ leafMax a)
    (hsg : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step g)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        Sg (S.leafInstance (S.topNode st)) ≤ sgBound a) :
    ∃ c e : ℕ,
      ComputableInO (S.run g) encA encD
        (fun a => c * ((encA a).length + 1) ^ e +
          (S.rounds a + 1) * (c * ((encA a).length + 1) ^ e + leafMax a))
        (fun a => c * ((encA a).length + 1) ^ e + sgBound a) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, 0,
      ((ComputableInO.const (encIn := encA) (encMid := encBits) ([] : List Bool)).mono_le
        (fun a => hα.elim a) (fun a => hα.elim a)).of_enc_eq fun a => hα.elim a⟩
  obtain ⟨a₀⟩ := hα
  let _ : Inhabited (StackSearchState κ σ δ) := ⟨S.initState a₀⟩
  let encSt := encStackSearchState encK encS encD
  obtain ⟨d, hstep⟩ := S.exists_computableInO_step hg
  have hinit_pt : ComputableInPolyTime S.initState encA encSt :=
    computableInPolyTime_stackSearchState_mk S.computableInPolyTime_initCtx
      S.computableInPolyTime_initStack S.computableInPolyTime_initAcc
  have hacc_pt : ComputableInPolyTime (fun st : StackSearchState κ σ δ => st.acc) encSt encD :=
    computableInPolyTime_stackSearchState_acc .id'
  obtain ⟨dn, _, hn⟩ := S.computableInPolyTime_rounds.exists_degree
  obtain ⟨di, _, hi⟩ := hinit_pt.exists_degree
  obtain ⟨da, _, ha⟩ := hacc_pt.exists_degree
  let stepPoly (a : α) : ℕ :=
    (stateBound a + 1) ^ d + (stateBound a + ansBound a + 1) ^ d
  have hloop := ComputableInO.iterate hn.inO hi.inO hstep
    (R := fun a => stepPoly a + leafMax a) (Q := fun a => stepPoly a + sgBound a)
    (fun a i hi => S.step_cost_le (hstate a i hi) (hans a i hi) (htime a i hi))
    (fun a i hi => S.step_cost_le (hstate a i hi) (hans a i hi) (hsg a i hi))
    hstate
  have hwhole := (ha.inO.comp hloop).of_enc_eq (g := S.run g) fun _ => rfl
  let clockLen (a : α) : ℕ := (encNat (S.rounds a)).length
  have hOverhead : PolyBounded (fun a => (encA a).length)
      (fun a => ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
        (stateBound a + 1) ^ da + stepPoly a + stateBound a +
        (clockLen a + 1) ^ 2 + clockLen a) := by
    growth_poly [S.computableInPolyTime_rounds]
  obtain ⟨c, e, hce⟩ := hOverhead.exists_le
  dsimp only [clockLen] at hce
  have hfin (a : α) : ((encSt ((S.step g)^[S.rounds a] (S.initState a))).length + 1) ^ da ≤
      (stateBound a + 1) ^ da :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a (S.rounds a) le_rfl) 1) da
  refine ⟨c, e, hwhole.mono_le (fun a => ?_) (fun a => ?_)⟩
  · have hfa := hfin a
    have h₁ := hce a
    rw [Nat.add_right_comm]
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  · have hfa := hfin a
    have h₁ := hce a
    omega

/-- **Accumulated-time and polynomial-live-workspace transfer for `S.run g`.**
When the live encoded search state and leaf answers are polynomially bounded along `S.rounds a`
and `g` has polynomial workspace `Sg`, `S.run g` runs in **polynomial live workspace**
(`ComputableInPolySpace (S.run g) encA encD`) and within accumulated time
`O(poly(|a|) + (S.rounds a + 1) * (poly(|a|) + leafMax a))`, without materializing the leaf list. -/
theorem exists_computableInO_run (S : StackAccumulationSpec encA encK encS encB encG encD)
    {g : β → γ} {Tg Sg : β → ℕ} (hg : ComputableInO g encB encG Tg Sg)
    (hSg : PolyBounded (fun b => (encB b).length) Sg)
    {stateBound ansBound leafMax : α → ℕ}
    (hstatePoly : PolyBounded (fun a => (encA a).length) stateBound)
    (hansPoly : PolyBounded (fun a => (encA a).length) ansBound)
    (hstate : ∀ a, ∀ i ≤ S.rounds a,
      (encStackSearchState encK encS encD ((S.step g)^[i] (S.initState a))).length ≤ stateBound a)
    (hans : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step g)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        (encG (g (S.leafInstance (S.topNode st)))).length ≤ ansBound a)
    (htime : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step g)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        Tg (S.leafInstance (S.topNode st)) ≤ leafMax a) :
    ∃ c e : ℕ, ∃ Space : α → ℕ,
      PolyBounded (fun a => (encA a).length) Space ∧
      ComputableInO (S.run g) encA encD
        (fun a => c * ((encA a).length + 1) ^ e +
          (S.rounds a + 1) * (c * ((encA a).length + 1) ^ e + leafMax a))
        Space ∧
      ComputableInPolySpace (S.run g) encA encD := by
  obtain ⟨leafLen, hleafPoly, hleafLen⟩ := S.exists_leafLen_le hstatePoly hstate
  obtain ⟨cs, ds, hSg_le⟩ := hSg.exists_le
  let sgBound (a : α) : ℕ := cs * (leafLen a + 1) ^ ds
  obtain ⟨c, e, hcert⟩ := S.exists_computableInO_run_of_spaceBound hg hstatePoly hansPoly
    hstate hans htime fun a i hi _ => (hSg_le _).trans
      (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (Nat.add_le_add_right (hleafLen a i hi) 1) ds))
  have hSpacePoly : PolyBounded (fun a => (encA a).length)
      (fun a => c * ((encA a).length + 1) ^ e + sgBound a) := by growth_poly
  exact ⟨c, e, _, hSpacePoly, hcert, .of_inSpace hSpacePoly (.of_inO hcert)⟩

/-- **Exponential-time decision transfer along a Boolean-OR `StackAccumulationSpec`.**
When `S.rounds a ≤ K₀ * 2 ^ (ν a)` with `ν a ≤ μA a / M + K₁` and every active leaf subinstance
satisfies `μB b ≤ scale * μA a + offset`, a decider for `B` within time
`2 ^ (δ * μB b) * poly(|b|)` transfers to `A` within time
`2 ^ ((1 / M + scale * δ) * μA a) * poly(|a|)`. -/
theorem decidableInExpTime_of_stack
    (S : StackAccumulationSpec encA encK encS encB encBool encBool)
    {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    {ν : α → ℕ} {K₀ M K₁ scale offset : ℕ}
    (hrounds : ∀ a, S.rounds a ≤ K₀ * 2 ^ (ν a))
    (hν : ∀ a, ν a ≤ μA a / M + K₁)
    {stateBound : α → ℕ} (hstatePoly : PolyBounded (fun a => (encA a).length) stateBound)
    (hAB : ∀ (g : β → Bool), (∀ b, b ∈ B ↔ g b = true) →
      ∀ a, (a ∈ A ↔ S.run g a = true) ∧
        (∀ i ≤ S.rounds a,
          (encStackSearchState encK encS encBool ((S.step g)^[i] (S.initState a))).length ≤
            stateBound a) ∧
        (∀ i ≤ S.rounds a,
          let st := (S.step g)^[i] (S.initState a)
          st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
            μB (S.leafInstance (S.topNode st)) ≤ scale * μA a + offset))
    {δ : ℝ} (hδ : 0 ≤ δ) (hB : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (1 / M + scale * δ) := by
  obtain ⟨e, h⟩ := hB
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  have hspec := hAB g hgB
  obtain ⟨leafLen, leafMax, hleafPoly, hleafMax_le, htime⟩ :=
    S.exists_leafMax_exp_le hstatePoly hδ (fun a => (hspec a).2.1) (fun a => (hspec a).2.2) ht
  obtain ⟨cs, es, hrun⟩ := S.exists_computableInO_run_of_spaceBound hg hstatePoly
    (PolyBounded.const 1) (fun a => (hspec a).2.1) (fun _ _ _ _ => by simp) htime htime
  obtain ⟨C₀, E, hT⟩ := stack_poly_exp_le hδ
    (A_ov := fun a => cs * ((encA a).length + 1) ^ es)
    (B_ov := fun a => cs * ((encA a).length + 1) ^ es)
    (by growth_poly) (by growth_poly) hleafPoly hrounds hν hleafMax_le
  exact DecidableInExpTime.of_computableInO hrun (fun a => (hspec a).1) C₀ E hT

/-- **Subexponential-time decision transfer along a family of Boolean-OR stack reductions.** -/
theorem decidableInSubexpTime_of_stack
    {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ} {scale : ℕ}
    (hfamily : ∀ M > 0, ∃ (S : StackAccumulationSpec encA encK encS encB encBool encBool)
      (ν stateBound : α → ℕ) (K₀ K₁ offset : ℕ),
      (∀ a, S.rounds a ≤ K₀ * 2 ^ (ν a)) ∧
      (∀ a, ν a ≤ μA a / M + K₁) ∧
      PolyBounded (fun a => (encA a).length) stateBound ∧
      ∀ (g : β → Bool), (∀ b, b ∈ B ↔ g b = true) →
        ∀ a, (a ∈ A ↔ S.run g a = true) ∧
          (∀ i ≤ S.rounds a,
            (encStackSearchState encK encS encBool ((S.step g)^[i] (S.initState a))).length ≤
              stateBound a) ∧
          (∀ i ≤ S.rounds a,
            let st := (S.step g)^[i] (S.initState a)
            st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
              μB (S.leafInstance (S.topNode st)) ≤ scale * μA a + offset))
    (hB : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  obtain ⟨S, ν, stateBound, K₀, K₁, offset, hrounds, hν, hstatePoly, hAB⟩ :=
    hfamily M (Nat.cast_pos.mp hMpos)
  set δ : ℝ := ε / 2 / (scale + 1)
  have hδ : 0 < δ := by positivity
  refine (S.decidableInExpTime_of_stack hrounds hν hstatePoly hAB hδ.le (hB δ hδ)).mono ?_
  have hMε : 1 / (M : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hMpos]
    linarith [(div_lt_iff₀ hε).mp hM]
  have hcδ : (scale : ℝ) * δ ≤ ε / 2 := natCast_mul_div_add_one_le (half_pos hε).le scale
  linarith

/-- **Capped summed-counting transfer along `StackAccumulationSpec` with polynomial live
workspace.**
Given a `CappedNatAcc`-accumulating stack specification `S` whose final `(S.run countB a).total`
equals `countA a`, with `S.rounds a ≤ K₀ * 2 ^ (ν a)`, `ν a ≤ μA a / M + K₁`, leaf measure
`μB b ≤ scale * μA a + offset`, and leaf counter `ComputableInO countB encB encNat Tg Sg` with
`PolyBounded length Sg`, `countA` is computable in **polynomial live workspace** AND time
`O(2 ^ ((1 / M + scale * δ) * μA a) * (|a| + 1) ^ E)`. -/
theorem exists_computableInO_cappedSum_of_stack
    (S : StackAccumulationSpec encA encK encS encB encNat encCappedNatAcc)
    {countA : α → ℕ} {countB : β → ℕ} {μA : α → ℕ} {μB : β → ℕ}
    {ν stateBound ansBound : α → ℕ} {K₀ M K₁ scale offset : ℕ}
    (hrounds : ∀ a, S.rounds a ≤ K₀ * 2 ^ (ν a))
    (hν : ∀ a, ν a ≤ μA a / M + K₁)
    (hstatePoly : PolyBounded (fun a => (encA a).length) stateBound)
    (hansPoly : PolyBounded (fun a => (encA a).length) ansBound)
    (hcorrect : ∀ a, (S.run countB a).total = countA a)
    (hstate : ∀ a, ∀ i ≤ S.rounds a,
      (encStackSearchState encK encS encCappedNatAcc ((S.step countB)^[i] (S.initState a))).length ≤
        stateBound a)
    (hans : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step countB)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        (encNat (countB (S.leafInstance (S.topNode st)))).length ≤ ansBound a)
    (hmeas : ∀ a, ∀ i ≤ S.rounds a,
      let st := (S.step countB)^[i] (S.initState a)
      st.stack.isEmpty = false ∧ S.isLeaf (S.topNode st) = true →
        μB (S.leafInstance (S.topNode st)) ≤ scale * μA a + offset)
    {Tg Sg : β → ℕ} (hg : ComputableInO countB encB encNat Tg Sg)
    (hSg : PolyBounded (fun b => (encB b).length) Sg)
    {δ : ℝ} (hδ : 0 ≤ δ) {k e : ℕ}
    (hTg : ∀ b, (Tg b : ℝ) ≤ k * (2 ^ (δ * μB b) * ((encB b).length + 1) ^ e) + k) :
    ∃ T Space : α → ℕ, ∃ C₀ E : ℕ,
      PolyBounded (fun a => (encA a).length) Space ∧
      ComputableInO countA encA encNat T Space ∧
      ComputableInPolySpace countA encA encNat ∧
      ∀ a, (T a : ℝ) ≤
        C₀ * (2 ^ ((1 / M + scale * δ) * μA a) * (((encA a).length : ℝ) + 1) ^ E) + C₀ := by
  obtain ⟨leafLen, leafMax, hleafPoly, hleafMax_le, htime⟩ :=
    S.exists_leafMax_exp_le hstatePoly hδ hstate hmeas hTg
  obtain ⟨cs, es, Space₀, hSpace₀, hrun, _⟩ :=
    S.exists_computableInO_run hg hSg hstatePoly hansPoly hstate hans htime
  have hrun_len (a : α) : (encCappedNatAcc (S.run countB a)).length ≤ stateBound a :=
    (show (encCappedNatAcc ((S.step countB)^[S.rounds a] (S.initState a)).acc).length ≤
        (encStackSearchState encK encS encCappedNatAcc
          ((S.step countB)^[S.rounds a] (S.initState a))).length by
      enc_len [encStackSearchState_apply]).trans (hstate a (S.rounds a) le_rfl)
  obtain ⟨dtot, Space, hSpacePoly, hout, hps⟩ :=
    computableInO_cappedAcc_total hrun hSpace₀ hstatePoly hrun_len hcorrect
  obtain ⟨C₀, E, hT⟩ := stack_poly_exp_le hδ
    (A_ov := fun a => cs * ((encA a).length + 1) ^ es + (stateBound a + 1) ^ dtot)
    (B_ov := fun a => cs * ((encA a).length + 1) ^ es)
    (by growth_poly) (by growth_poly) hleafPoly hrounds hν hleafMax_le
  refine ⟨_, Space, C₀, E, hSpacePoly, hout, hps, fun a => ?_⟩
  rw [Nat.add_right_comm]
  exact (hT a).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

/-! ### Bridge to `BinaryBranching` and disjoint sparsification -/

/-- When `S` expands inner states to the two children `[T.next s false, T.next s true]` of a
`BinaryBranching` rule `T`, iterating `S.step g` agrees at every step with `T.searchStep`. -/
theorem iterate_step_eq_binaryBranching
    (S : StackAccumulationSpec encA encK encS encB encG encD)
    (g : β → γ) (c : κ) (T : BinaryBranching σ)
    (hleaf : ∀ s, S.isLeaf ⟨c, s⟩ = true ↔ T.IsLeaf s)
    (hexp : ∀ s, ¬ T.IsLeaf s → S.expand ⟨c, s⟩ = [T.next s false, T.next s true])
    (n : ℕ) (stk : List σ) (ac : δ) :
    (S.step g)^[n] ⟨c, stk, ac⟩ =
      let p := (T.searchStep (fun d s => S.combine ⟨c, d, g (S.leafInstance ⟨c, s⟩)⟩))^[n] (stk, ac)
      ⟨c, p.1, p.2⟩ := by
  induction n generalizing stk ac with
  | zero => rfl
  | succ n ih =>
    have hone : S.step g ⟨c, stk, ac⟩ =
        let p := T.searchStep (fun d s => S.combine ⟨c, d, g (S.leafInstance ⟨c, s⟩)⟩) (stk, ac)
        ⟨c, p.1, p.2⟩ := by
      cases stk with
      | nil => rfl
      | cons s rest =>
        by_cases hs : T.IsLeaf s
        · simp [step, topNode, BinaryBranching.searchStep, hs, (hleaf s).mpr hs]
        · simp [step, topNode, BinaryBranching.searchStep, hs,
            Bool.eq_false_iff.mpr (mt (hleaf s).mp hs), hexp s hs]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hone]
    exact ih _ _

/-- **Leaf-word fold theorem (`BinaryBranching` / sparsification bridge).**
For a terminating `BinaryBranching` rule `T` on input `a` starting at `[root]` with leaf depth at
most `h` and `2 * L.length ≤ S.rounds a` on the duplicate-free list `L` of leaf words, `S.run g a`
equals the fold over all leaf states `L.map (T.walk root)` while every intermediate stack has
length at most `h + 1` and holds only tree nodes of depth at most `h`. -/
theorem run_eq_foldl_leafWords
    (S : StackAccumulationSpec encA encK encS encB encG encD)
    (g : β → γ) (a : α) (T : BinaryBranching σ) (hT : T.Terminating)
    {root : σ} (hinit : S.initStack a = [root])
    (hleaf : ∀ s, S.isLeaf ⟨S.initCtx a, s⟩ = true ↔ T.IsLeaf s)
    (hexp : ∀ s, ¬ T.IsLeaf s →
      S.expand ⟨S.initCtx a, s⟩ = [T.next s false, T.next s true])
    {h : ℕ} (hh : ∀ w, T.IsLeafWord root w → w.length ≤ h)
    (hrounds : ∀ (L : List (List Bool)), L.Nodup → (∀ w, w ∈ L ↔ T.IsLeafWord root w) →
      2 * L.length ≤ S.rounds a + 1) :
    ∃ L : List (List Bool), L.Nodup ∧ (∀ w, w ∈ L ↔ T.IsLeafWord root w) ∧
      S.run g a = (L.map (T.walk root)).foldl
        (fun d s => S.combine ⟨S.initCtx a, d, g (S.leafInstance ⟨S.initCtx a, s⟩)⟩)
        (S.initAcc a) ∧
      ∀ i ≤ S.rounds a,
        let st := (S.step g)^[i] (S.initState a)
        st.stack.length ≤ h + 1 ∧
        (∀ t ∈ st.stack, ∃ w, T.IsNodeWord root w ∧ w.length ≤ h ∧ T.walk root w = t) ∧
        ∃ L', L' <+: L ∧ st.acc = (L'.map (T.walk root)).foldl
          (fun d s => S.combine ⟨S.initCtx a, d, g (S.leafInstance ⟨S.initCtx a, s⟩)⟩)
          (S.initAcc a) := by
  let f := fun (d : δ) (s : σ) =>
    S.combine ⟨S.initCtx a, d, g (S.leafInstance ⟨S.initCtx a, s⟩)⟩
  obtain ⟨L, hnd, hL, N, hN, hsearch⟩ := T.exists_iterate_searchStep hT f root hh
  have hrl := hrounds L hnd hL
  obtain ⟨hfin, hpref⟩ := hsearch [] (S.initAcc a)
  have hfix := Function.iterate_fixed (f := T.searchStep f)
    (x := ([], (L.map (T.walk root)).foldl f (S.initAcc a))) rfl
  have hafter (m : ℕ) (hm : N ≤ m) :
      (T.searchStep f)^[m] ([root], S.initAcc a) =
        ([], (L.map (T.walk root)).foldl f (S.initAcc a)) := by
    rw [← Nat.sub_add_cancel hm, Function.iterate_add_apply, hfin, hfix]
  refine ⟨L, hnd, hL, ?_, fun i hi => ?_⟩
  · simp only [run, initState, hinit]
    rw [S.iterate_step_eq_binaryBranching g (S.initCtx a) T hleaf hexp (S.rounds a) [root]
      (S.initAcc a), hafter (S.rounds a) (by omega)]
  · dsimp only [initState]
    rw [hinit, S.iterate_step_eq_binaryBranching g (S.initCtx a) T hleaf hexp i [root]
      (S.initAcc a)]
    by_cases hiN : i ≤ N
    · obtain ⟨stk, L', hL', heq, hlen, hmem⟩ := hpref i hiN
      rw [List.append_nil] at heq
      exact heq ▸ ⟨hlen, hmem, L', hL', rfl⟩
    · rw [hafter i (by omega)]
      exact ⟨Nat.zero_le _, fun _ ht => by simp at ht, L, List.prefix_rfl, rfl⟩

/-- **Exact additive root recovery for capped disjoint-branching sums.**
When `val : σ → ℕ` is additive across the children of every inner state (`val t = val (next false) +
val (next true)`), `g` computes `val` on leaves, and `val root ≤ cap`, a `CappedNatAcc` stack
traversal recovers `val root` exactly. -/
theorem run_cappedSum_eq_root
    (S : StackAccumulationSpec encA encK encS encB encNat encCappedNatAcc)
    (g : β → ℕ) (a : α) (T : BinaryBranching σ) (hT : T.Terminating)
    {root : σ} {cap : ℕ}
    (hinit : S.initStack a = [root])
    (hinitAcc : S.initAcc a = CappedNatAcc.init cap)
    (hcombine : ∀ d v, S.combine ⟨S.initCtx a, d, v⟩ = d.add v)
    (hleaf : ∀ s, S.isLeaf ⟨S.initCtx a, s⟩ = true ↔ T.IsLeaf s)
    (hexp : ∀ s, ¬ T.IsLeaf s →
      S.expand ⟨S.initCtx a, s⟩ = [T.next s false, T.next s true])
    {h : ℕ} (hh : ∀ w, T.IsLeafWord root w → w.length ≤ h)
    (hrounds : ∀ (L : List (List Bool)), L.Nodup → (∀ w, w ∈ L ↔ T.IsLeafWord root w) →
      2 * L.length ≤ S.rounds a + 1)
    {val : σ → ℕ}
    (hadd : ∀ t, ¬ T.IsLeaf t → val t = val (T.next t false) + val (T.next t true))
    (hval_leaf : ∀ t, T.IsLeaf t → g (S.leafInstance ⟨S.initCtx a, t⟩) = val t)
    (hcap : val root ≤ cap) :
    (S.run g a).total = val root := by
  classical
  obtain ⟨L, hnd, hL, hrun_eq, _⟩ :=
    S.run_eq_foldl_leafWords g a T hT hinit hleaf hexp hh hrounds
  have hcomb_eq : (fun (d : CappedNatAcc) (s : σ) =>
      S.combine ⟨S.initCtx a, d, g (S.leafInstance ⟨S.initCtx a, s⟩)⟩) =
      fun d s => d.add (g (S.leafInstance ⟨S.initCtx a, s⟩)) :=
    funext₂ fun d _ => hcombine d _
  have hsum_eq := T.sum_leafWords_eq hT hadd root fun w => List.mem_toFinset.trans (hL w)
  rw [hrun_eq, hinitAcc, hcomb_eq, CappedNatAcc.foldl_add_init_total, List.map_map,
    Function.comp_def]
  rw [List.map_congr_left fun w hw => hval_leaf _ ((hL w).mp hw).isLeaf_walk,
    ← List.sum_toFinset _ hnd, hsum_eq, Nat.min_eq_right hcap]

end StackAccumulationSpec

end Cslib.Complexity
