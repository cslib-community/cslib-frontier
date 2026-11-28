/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Basis.U2.Compression
public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Circuit
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.WeightedMatching
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Nat.Card
import CslibFrontier.Foundations.Data.Nat.IntermediateValue
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import CslibFrontier.Tactic.LRATTauto

/-!
# `3`-state pair-compressed branching programs for `U₂` circuits

Compiles a `U₂` circuit network equipped with clean matched-pair layout data (`U2PairData`) into an
unambiguous layered `ReadOnceNBP` (`U2PairData.branchingProgram`). Whenever both high-score outer
wires `(b_e, d_e)` of an equal-key clean matched pair `e` cross the frontier, the compiler replaces
their `4` wire assignments with `Fin 3` indexing the unambiguous `3`-rectangle cover from
`CslibFrontier.Computability.Circuit.Frontier.Basis.PairAtlas`, reducing the frontier width at step
`t` from `2^{|cut|}` to `2^{|cut| - 2 |active|} · 3^{|active|}`.

## Main definitions

* `Cslib.Circuits.Frontier.Compiler.U2PairData`: saturated compression, clean matching, edge scores,
  and `PairNode` layout of a `U₂` circuit.
* `Cslib.Circuits.Frontier.Compiler.U2PairData.branchingProgram`: the `3`-state pair-compressed
  layered `ReadOnceNBP`.

## Main results

* `Cslib.Circuits.Frontier.Compiler.U2PairData.accepted_branchingProgram`,
  `Cslib.Circuits.Frontier.Compiler.U2PairData.unambiguous_branchingProgram`: exact acceptance and
  path uniqueness of `U2PairData.branchingProgram`.
* `Cslib.Circuits.Frontier.Compiler.U2PairData.size_branchingProgram_le`,
  `Cslib.Circuits.Frontier.Compiler.U2PairData.mul_size_branchingProgram_le_rpow`: total edge-count
  bounds in terms of the `(2 - log₂ 3)`-discounted effective cut.
* `Cslib.Circuits.Frontier.Compiler.U2PairData.sq_correlation_quadForm_le`: single-circuit
  quadratic-form correlation bound from `U2PairData`.
-/

public section

namespace Cslib.Circuits.Frontier.Compiler

open Set Matrix Cslib.Circuits.Frontier.Basis

section U2BranchingProgram

variable {σ : Signature} {m_in m_out : ℕ}

/-- Clean matched-pair layout data on a budget-`3` saturated compression of `Compiler.graph c`. -/
structure U2PairData (c : Circuit σ m_in m_out) (I : Interpretation σ Bool) where
  /-- Underlying budget-`3` edge-contraction compression of `Compiler.graph c`. -/
  Q : (graph c).Compression 3
  /-- Proof that `Q` cannot contract any remaining low-degree block. -/
  hsat : Q.Saturated
  /-- Clean edge matching in the quotient multigraph `Q.quotient`. -/
  M : Set Q.external
  /-- Cubic regularity of `Q.quotient` whenever `M` is nonempty. -/
  h3 : M.Nonempty → ∀ B : Q.blocks, (Q.quotient.incidenceSet B).ncard = 3
  /-- Vertex disjointness of the matched edges `M`. -/
  hM : Q.quotient.IsMatching M
  /-- Cleanliness (`COPY` or `U₂` gate) of both endpoint blocks of every edge in `M`. -/
  hclean : ∀ e ∈ M, CleanBlock3 I {v | v ∈ (Q.quotient.src e).val} ∧
    CleanBlock3 I {v | v ∈ (Q.quotient.tgt e).val}
  /-- Real score function on external quotient wires orienting each clean pair's outer wires. -/
  score : Q.external → ℝ
  /-- Linear layout of singletons and equal-key clean pairs of `Q.quotient`. -/
  pairLay : Layout (Q.quotient.PairNode M M score)

namespace U2PairData

variable {c : Circuit σ m_in m_out} {I : Interpretation σ Bool} (D : U2PairData c I)

/-- Equal-key clean matched pairs of `D`. -/
noncomputable def eqPairs : Set D.Q.external :=
  D.Q.quotient.equalKeyPairs D.M D.M D.score

private theorem isMatching_eqPairs : D.Q.quotient.IsMatching D.eqPairs :=
  fun _ h₁ _ h₂ hne => D.hM h₁.1 h₂.1 hne

private def pairVerts (e : D.eqPairs) : Set (Vertex c) :=
  {v | v ∈ (D.Q.quotient.src e.val).val} ∪ {v | v ∈ (D.Q.quotient.tgt e.val).val}

private theorem mem_pairVerts_iff (e : D.eqPairs) (v : Vertex c) :
    v ∈ D.pairVerts e ↔
      D.Q.blockOf v = D.Q.quotient.src e.val ∨ D.Q.blockOf v = D.Q.quotient.tgt e.val := by
  simp only [pairVerts, mem_union, mem_ofPred_eq, D.Q.mem_iff_blockOf_eq]

private theorem isCleanVertex_of_mem_pairVerts (e : D.eqPairs) {v : Vertex c}
    (hv : v ∈ D.pairVerts e) : IsCleanVertex v := by
  rcases hv with hv₁ | hv₂
  · exact (D.hclean e.val e.property.1).1.1 v hv₁
  · exact (D.hclean e.val e.property.1).2.1 v hv₂

private theorem disjoint_pairVerts {e₁ e₂ : D.eqPairs} (hne : e₁ ≠ e₂) :
    Disjoint (D.pairVerts e₁) (D.pairVerts e₂) := by
  refine disjoint_left.mpr fun v hv₁ hv₂ => ?_
  have hne_val : e₁.val ≠ e₂.val := fun h => hne (Subtype.ext h)
  exact disjoint_left.mp (D.isMatching_eqPairs e₁.property e₂.property hne_val)
    ((D.mem_pairVerts_iff e₁ v).mp hv₁) ((D.mem_pairVerts_iff e₂ v).mp hv₂)

private noncomputable def pinA (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerLow D.score (D.Q.quotient.src e.val) e.val

private noncomputable def pinB (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerHigh D.score (D.Q.quotient.src e.val) e.val

private noncomputable def pinC (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerLow D.score (D.Q.quotient.tgt e.val) e.val

private noncomputable def pinD (e : D.eqPairs) : D.Q.external :=
  D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt e.val) e.val

private theorem block_edgeCut_sdiff (hM_ne : D.M.Nonempty) (B : D.Q.blocks) (f : D.Q.external)
    (hf : f ∈ D.Q.quotient.incidenceSet B) :
    (D.Q.quotient.outerLow D.score B f).val ≠ (D.Q.quotient.outerHigh D.score B f).val ∧
      (graph c).edgeCut {v | v ∈ B.val} \ {f.val} =
        {(D.Q.quotient.outerLow D.score B f).val, (D.Q.quotient.outerHigh D.score B f).val} := by
  have := Fintype.ofFinite (Edge c)
  have hspec := Multigraph.outerLow_outerHigh_spec (D.h3 hM_ne) D.score hf
  refine ⟨fun h => hspec.1 (Subtype.ext h), ?_⟩
  have hpre : D.Q.blockOf ⁻¹' ({B} : Set D.Q.blocks) = {v | v ∈ B.val} := by
    ext v; simp [D.Q.mem_iff_blockOf_eq]
  have hcut : (graph c).edgeCut {v | v ∈ B.val} =
      Subtype.val '' D.Q.quotient.incidenceSet B := by
    rw [← hpre, ← Multigraph.edgeCut_singleton _ D.Q.quotient_loopless]
    ext g
    simp only [Multigraph.mem_edgeCut, mem_preimage, mem_singleton_iff, mem_image,
      Subtype.exists, exists_and_right, exists_eq_right, Multigraph.Compression.quotient_src,
      Multigraph.Compression.quotient_tgt]
    exact ⟨fun h => ⟨fun heq => h (by rw [heq]), h⟩, fun ⟨_, h⟩ => h⟩
  rw [hcut]
  ext g
  simp only [mem_sdiff, mem_image, mem_singleton_iff, mem_insert_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    have hx' : x ∈ D.Q.quotient.incidenceSet B \ {f} := ⟨hx, fun h => hne (congrArg Subtype.val h)⟩
    rw [hspec.2.1] at hx'
    rcases hx' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · have hm : D.Q.quotient.outerLow D.score B f ∈ D.Q.quotient.incidenceSet B \ {f} := by
        rw [hspec.2.1]; simp
      exact ⟨⟨_, hm.1, rfl⟩, fun h => hm.2 (Subtype.ext h)⟩
    · have hm : D.Q.quotient.outerHigh D.score B f ∈ D.Q.quotient.incidenceSet B \ {f} := by
        rw [hspec.2.1]; simp
      exact ⟨⟨_, hm.1, rfl⟩, fun h => hm.2 (Subtype.ext h)⟩

private theorem edgeCut_src_inter_tgt (e : D.eqPairs) :
    (graph c).edgeCut {v | v ∈ (D.Q.quotient.src e.val).val} ∩
      (graph c).edgeCut {v | v ∈ (D.Q.quotient.tgt e.val).val} = {e.val.val} := by
  have := Fintype.ofFinite (Edge c)
  have hinj := D.hsat.injective_ends_quotient
  set B₁ := D.Q.quotient.src e.val
  set B₂ := D.Q.quotient.tgt e.val
  have hneB : B₁ ≠ B₂ := D.Q.quotient_loopless e.val
  ext g
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hg₁, hg₂⟩
    rw [D.Q.mem_edgeCut_block] at hg₁ hg₂
    have hext : g ∈ D.Q.external := fun heq => hg₁ (by rw [heq])
    let gx : D.Q.external := ⟨g, hext⟩
    suffices gx = e.val from congrArg Subtype.val this
    apply hinj
    simp only [Multigraph.ends, Multigraph.Compression.quotient_src,
      Multigraph.Compression.quotient_tgt, Sym2.eq_iff]
    change (D.Q.blockOf (src g) = B₁ ∧ D.Q.blockOf (tgt g) = B₂) ∨
      (D.Q.blockOf (src g) = B₂ ∧ D.Q.blockOf (tgt g) = B₁)
    by_cases hs₁ : D.Q.blockOf (src g) = B₁
    · have ht_ne₁ : D.Q.blockOf (tgt g) ≠ B₁ := fun h => hg₁ (iff_of_true hs₁ h)
      by_cases hs₂ : D.Q.blockOf (src g) = B₂
      · exact (hneB (hs₁.symm.trans hs₂)).elim
      · have ht₂ : D.Q.blockOf (tgt g) = B₂ := by_contra fun hn => hg₂ (iff_of_false hs₂ hn)
        exact Or.inl ⟨hs₁, ht₂⟩
    · have ht₁ : D.Q.blockOf (tgt g) = B₁ := by_contra fun hn => hg₁ (iff_of_false hs₁ hn)
      have ht_ne₂ : D.Q.blockOf (tgt g) ≠ B₂ := fun h => hneB (ht₁.symm.trans h)
      have hs₂ : D.Q.blockOf (src g) = B₂ := by_contra fun hn => hg₂ (iff_of_false hn ht_ne₂)
      exact Or.inr ⟨hs₂, ht₁⟩
  · rintro rfl
    rw [D.Q.mem_edgeCut_block, D.Q.mem_edgeCut_block]
    exact ⟨fun h => hneB (h.mp rfl).symm, fun h => hneB (h.mpr rfl)⟩

private theorem edgeCut_pairVerts (e : D.eqPairs) :
    (graph c).edgeCut (D.pairVerts e) =
      {(D.pinA e).val, (D.pinB e).val, (D.pinC e).val, (D.pinD e).val} := by
  have hd : Disjoint {v | v ∈ (D.Q.quotient.src e.val).val}
      {v | v ∈ (D.Q.quotient.tgt e.val).val} :=
    D.Q.disjoint_of_ne (D.Q.quotient_loopless e.val)
  obtain ⟨hc_u, _⟩ := edgeCut_union_of_inter_singleton hd (D.edgeCut_src_inter_tgt e)
  have hs₁ :=
    (D.block_edgeCut_sdiff ⟨e.val, e.property.1⟩ (D.Q.quotient.src e.val) e.val (Or.inl rfl)).2
  have hs₂ :=
    (D.block_edgeCut_sdiff ⟨e.val, e.property.1⟩ (D.Q.quotient.tgt e.val) e.val (Or.inr rfl)).2
  dsimp only [pairVerts, pinA, pinB, pinC, pinD]
  rw [hc_u, hs₁, hs₂]
  ext g
  simp only [mem_union, mem_insert_iff, mem_singleton_iff]
  tauto

private theorem exists_rect_cover (e : D.eqPairs) :
    ∃ (row col : Fin 3 → Bool × Bool → Bool),
      (∀ α, GateSatisfies I (D.pairVerts e) α →
        ∃! r : Fin 3, (row r (α (D.pinB e).val, α (D.pinD e).val) &&
          col r (α (D.pinA e).val, α (D.pinC e).val)) = true) ∧
      (∀ (r : Fin 3) (α : Edge c → Bool),
        (row r (α (D.pinB e).val, α (D.pinD e).val) &&
          col r (α (D.pinA e).val, α (D.pinC e).val)) = true →
        ∃ β, EqOn β α (internalEdges c (D.pairVerts e))ᶜ ∧ GateSatisfies I (D.pairVerts e) β) := by
  set B₁ := D.Q.quotient.src e.val
  set B₂ := D.Q.quotient.tgt e.val
  have hd : Disjoint {v | v ∈ B₁.val} {v | v ∈ B₂.val} :=
    D.Q.disjoint_of_ne (D.Q.quotient_loopless e.val)
  have hint := D.edgeCut_src_inter_tgt e
  have he_cut₁ : e.val.val ∈ (graph c).edgeCut {v | v ∈ B₁.val} := (hint.symm ▸ mem_singleton _).1
  have he_cut₂ : e.val.val ∈ (graph c).edgeCut {v | v ∈ B₂.val} := (hint.symm ▸ mem_singleton _).2
  obtain ⟨hne₁, hs₁⟩ := D.block_edgeCut_sdiff ⟨e.val, e.property.1⟩ B₁ e.val (Or.inl rfl)
  obtain ⟨hne₂, hs₂⟩ := D.block_edgeCut_sdiff ⟨e.val, e.property.1⟩ B₂ e.val (Or.inr rfl)
  obtain ⟨hb₁, hb₂⟩ := D.hclean e.val e.property.1
  obtain ⟨rel₁, hU₁, hsd₁, hrl₁⟩ :=
    (hb₁.2.2 _ _ e.val.val hne₁ hs₁ he_cut₁).1 (D.Q.mem_blockOf (src e.val.val))
  obtain ⟨rel₂, hI₂, hsd₂, hrl₂⟩ :=
    (hb₂.2.2 _ _ e.val.val hne₂ hs₂ he_cut₂).2 (D.Q.mem_blockOf (tgt e.val.val))
  obtain ⟨row, col, hcov⟩ := hasUnambiguousRectangles_u2 hU₁ hI₂
  refine ⟨row, col, fun α hsat => ?_, fun r α hr => ?_⟩
  · have h1 := hsd₁ α fun v hv => hsat v (Or.inl hv)
    have h2 := hsd₂ α fun v hv => hsat v (Or.inr hv)
    have hpm : pairMatrix rel₁ rel₂ (α (D.pinB e).val, α (D.pinD e).val)
        (α (D.pinA e).val, α (D.pinC e).val) = true := by
      dsimp only [pinA, pinB, pinC, pinD, B₁, B₂] at h1 h2 ⊢
      rcases Bool.dichotomy (α e.val.val) with hα | hα <;> rw [hα] at h1 h2
      · simp only [pairMatrix, h1, h2, Bool.and_self, Bool.true_or]
      · simp only [pairMatrix, h1, h2, Bool.and_self, Bool.or_true]
    have hcard := hcov (α (D.pinB e).val, α (D.pinD e).val) (α (D.pinA e).val, α (D.pinC e).val)
    simp only [hpm, ↓reduceIte] at hcard
    obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hcard
    refine ⟨r₀, ?_, fun r' hr' => ?_⟩
    · have hm : r₀ ∈ Finset.univ.filter _ := hr₀ ▸ Finset.mem_singleton_self r₀
      exact (Finset.mem_filter.mp hm).2
    · have hm : r' ∈ ({r₀} : Finset (Fin 3)) := hr₀ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'⟩
      exact Finset.mem_singleton.mp hm
  · classical
    have hcard := hcov (α (D.pinB e).val, α (D.pinD e).val) (α (D.pinA e).val, α (D.pinC e).val)
    have hpos : 0 < (Finset.univ.filter fun r' : Fin 3 =>
        row r' (α (D.pinB e).val, α (D.pinD e).val) &&
          col r' (α (D.pinA e).val, α (D.pinC e).val)).card :=
      Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    have hpm : pairMatrix rel₁ rel₂ (α (D.pinB e).val, α (D.pinD e).val)
        (α (D.pinA e).val, α (D.pinC e).val) = true := by
      by_contra hfalse
      simp only [Bool.not_eq_true] at hfalse
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hcard
      omega
    simp only [pairMatrix, Bool.or_eq_true, Bool.and_eq_true] at hpm
    have hex_val : ∃ val_e : Bool, rel₁ (α (D.pinA e).val) (α (D.pinB e).val) val_e = true ∧
        rel₂ (α (D.pinC e).val) (α (D.pinD e).val) val_e = true :=
      hpm.elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
    obtain ⟨val_e, hv₁, hv₂⟩ := hex_val
    let α₀ : Edge c → Bool := fun g => if g = e.val.val then val_e else α g
    have ha_mem : (D.pinA e).val ∈ (graph c).edgeCut {v | v ∈ B₁.val} \ {e.val.val} := by
      rw [hs₁]; exact Or.inl rfl
    have hb_mem : (D.pinB e).val ∈ (graph c).edgeCut {v | v ∈ B₁.val} \ {e.val.val} := by
      rw [hs₁]; exact Or.inr rfl
    have hc_mem : (D.pinC e).val ∈ (graph c).edgeCut {v | v ∈ B₂.val} \ {e.val.val} := by
      rw [hs₂]; exact Or.inl rfl
    have hd_mem : (D.pinD e).val ∈ (graph c).edgeCut {v | v ∈ B₂.val} \ {e.val.val} := by
      rw [hs₂]; exact Or.inr rfl
    refine patch_union hd hint α α₀ (fun g hne => ite_eq_right hne) ?_ ?_
    · refine hrl₁ α₀ ?_
      have hA : α₀ (D.pinA e).val = α (D.pinA e).val := ite_eq_right ha_mem.2
      have hB : α₀ (D.pinB e).val = α (D.pinB e).val := ite_eq_right hb_mem.2
      have hE : α₀ e.val.val = val_e := ite_eq_left rfl
      dsimp only [pinA, pinB] at hA hB hv₁
      rwa [hA, hB, hE]
    · intro β₁ hβ₁
      refine hrl₂ β₁ ?_
      have hC : β₁ (D.pinC e).val = α (D.pinC e).val := (hβ₁ hc_mem.1).trans (ite_eq_right hc_mem.2)
      have hD : β₁ (D.pinD e).val = α (D.pinD e).val := (hβ₁ hd_mem.1).trans (ite_eq_right hd_mem.2)
      have hE : β₁ e.val.val = val_e := (hβ₁ he_cut₂).trans (ite_eq_left rfl)
      dsimp only [pinC, pinD] at hC hD hv₂
      rwa [hC, hD, hE]

private noncomputable def rowPred (e : D.eqPairs) : Fin 3 → Bool × Bool → Bool :=
  (D.exists_rect_cover e).choose

private noncomputable def colPred (e : D.eqPairs) : Fin 3 → Bool × Bool → Bool :=
  (D.exists_rect_cover e).choose_spec.choose

private noncomputable def rectIdxAux (e : D.eqPairs) (b d a c_val : Bool) : Fin 3 :=
  letI := Classical.dec
  if h : ∃ r : Fin 3, (D.rowPred e r (b, d) && D.colPred e r (a, c_val)) = true then
    h.choose
  else 0

private noncomputable def rectIdx (e : D.eqPairs) (α : Edge c → Bool) : Fin 3 :=
  D.rectIdxAux e (α (D.pinB e).val) (α (D.pinD e).val) (α (D.pinA e).val) (α (D.pinC e).val)

private theorem rectIdx_congr (e : D.eqPairs) {α β : Edge c → Bool}
    (hA : α (D.pinA e).val = β (D.pinA e).val) (hB : α (D.pinB e).val = β (D.pinB e).val)
    (hC : α (D.pinC e).val = β (D.pinC e).val) (hD : α (D.pinD e).val = β (D.pinD e).val) :
    D.rectIdx e α = D.rectIdx e β := by
  unfold rectIdx
  rw [hB, hD, hA, hC]

private theorem rectIdx_spec_of_sat (e : D.eqPairs) {α : Edge c → Bool}
    (hsat : GateSatisfies I (D.pairVerts e) α) :
    D.rowPred e (D.rectIdx e α) (α (D.pinB e).val, α (D.pinD e).val) = true ∧
      D.colPred e (D.rectIdx e α) (α (D.pinA e).val, α (D.pinC e).val) = true := by
  obtain ⟨r, hr, _⟩ := (D.exists_rect_cover e).choose_spec.choose_spec.1 α hsat
  have hex : ∃ r' : Fin 3, (D.rowPred e r' (α (D.pinB e).val, α (D.pinD e).val) &&
      D.colPred e r' (α (D.pinA e).val, α (D.pinC e).val)) = true := ⟨r, hr⟩
  dsimp only [rectIdx, rectIdxAux]
  rw [dite_eq_left hex]
  exact Bool.and_eq_true_iff.mp hex.choose_spec

private theorem rectIdx_eq_and_realize (e : D.eqPairs) {r : Fin 3} {α : Edge c → Bool}
    (hrc : D.rowPred e r (α (D.pinB e).val, α (D.pinD e).val) = true ∧
      D.colPred e r (α (D.pinA e).val, α (D.pinC e).val) = true) :
    D.rectIdx e α = r ∧
      ∃ β, EqOn β α (internalEdges c (D.pairVerts e))ᶜ ∧ GateSatisfies I (D.pairVerts e) β := by
  have hand : (D.rowPred e r (α (D.pinB e).val, α (D.pinD e).val) &&
      D.colPred e r (α (D.pinA e).val, α (D.pinC e).val)) = true :=
    Bool.and_eq_true_iff.mpr hrc
  obtain ⟨β, hβ_eq, hβ_sat⟩ := (D.exists_rect_cover e).choose_spec.choose_spec.2 r α hand
  refine ⟨?_, β, hβ_eq, hβ_sat⟩
  -- `β` agrees with `α` on all four external pins of `pairVerts e`.
  have hnot_int {g : Edge c} (hg : g ∈ (graph c).edgeCut (D.pairVerts e)) :
      g ∉ internalEdges c (D.pairVerts e) := fun hin => hg (iff_of_true hin.1 hin.2)
  have hA : β (D.pinA e).val = α (D.pinA e).val :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  have hB : β (D.pinB e).val = α (D.pinB e).val :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  have hC : β (D.pinC e).val = α (D.pinC e).val :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  have hD : β (D.pinD e).val = α (D.pinD e).val :=
    hβ_eq (hnot_int (by rw [D.edgeCut_pairVerts]; simp))
  obtain ⟨r₀, _, huniq⟩ := (D.exists_rect_cover e).choose_spec.choose_spec.1 β hβ_sat
  have hex : ∃ r' : Fin 3, (D.rowPred e r' (α (D.pinB e).val, α (D.pinD e).val) &&
      D.colPred e r' (α (D.pinA e).val, α (D.pinC e).val)) = true := ⟨r, hand⟩
  dsimp only [rectIdx, rectIdxAux]
  rw [dite_eq_left hex]
  have h1 : hex.choose = r₀ := huniq hex.choose (by rw [hB, hD, hA, hC]; exact hex.choose_spec)
  have h2 : r = r₀ := huniq r (by rw [hB, hD, hA, hC]; exact hand)
  exact h1.trans h2.symm

/-- Individual vertices outside equal-key clean pairs, plus one super-node per `e : D.eqPairs`. -/
private abbrev SingleVert :=
  {v : Vertex c // D.Q.blockOf v ∉ D.Q.quotient.matchedVertices D.eqPairs}

private abbrev StepNode := D.SingleVert ⊕ D.eqPairs

private instance : Finite D.StepNode := by
  have := Finite.of_injective (fun u : D.SingleVert => u.val) Subtype.val_injective
  have := Fintype.ofFinite (Edge c)
  infer_instance

private theorem card_stepNode_le : Nat.card D.StepNode ≤ Nat.card (Vertex c) := by
  let rep : D.StepNode → Vertex c
    | .inl u => u.val
    | .inr e => (D.Q.quotient.src e.val).val.head (D.Q.ne_nil _ (D.Q.quotient.src e.val).property)
  refine Nat.card_le_card_of_injective rep ?_
  rintro (u₁ | e₁) (u₂ | e₂) h <;> dsimp only [rep] at h
  · exact congrArg Sum.inl (Subtype.ext h)
  · have hm : rep (.inr e₂) ∈ (D.Q.quotient.src e₂.val).val := List.head_mem _
    dsimp only [rep] at hm
    rw [← h] at hm
    exact (u₁.property ⟨e₂.val, e₂.property, Or.inl (D.Q.mem_iff_blockOf_eq.mp hm).symm⟩).elim
  · have hm : rep (.inr e₁) ∈ (D.Q.quotient.src e₁.val).val := List.head_mem _
    dsimp only [rep] at hm
    rw [h] at hm
    exact (u₂.property ⟨e₁.val, e₁.property, Or.inl (D.Q.mem_iff_blockOf_eq.mp hm).symm⟩).elim
  · have hm₁ : rep (.inr e₁) ∈ D.pairVerts e₁ := Or.inl (List.head_mem _)
    have hm₂ : rep (.inr e₂) ∈ D.pairVerts e₂ := Or.inl (List.head_mem _)
    dsimp only [rep] at hm₁ hm₂
    rw [h] at hm₁
    by_contra hne
    exact disjoint_left.mp (D.disjoint_pairVerts fun heq => hne (congrArg Sum.inr heq)) hm₁ hm₂

private noncomputable def stepPairNode : D.StepNode → D.Q.quotient.PairNode D.M D.M D.score
  | .inl u => .inl ⟨D.Q.blockOf u.val, u.property⟩
  | .inr e => .inr e

open Classical in
private noncomputable def stepSubIdx : D.StepNode → ℕ
  | .inl u => (D.Q.blockOf u.val).val.idxOf u.val
  | .inr _ => 0

private noncomputable def stepKey (x : D.StepNode) : ℕ ×ₗ ℕ :=
  toLex ((D.pairLay (D.stepPairNode x) : ℕ), D.stepSubIdx x)

private theorem stepKey_injective : Function.Injective D.stepKey := by
  classical
  rintro (u₁ | e₁) (u₂ | e₂) h
  · obtain ⟨hp, hi⟩ := Prod.mk.inj (toLex.injective h)
    have hb : D.Q.blockOf u₁.val = D.Q.blockOf u₂.val :=
      Subtype.mk.inj (Sum.inl.inj (D.pairLay.injective (Fin.ext hp)))
    dsimp only [stepSubIdx] at hi
    rw [hb] at hi
    exact congrArg Sum.inl
      (Subtype.ext ((List.idxOf_inj (D.Q.mem_iff_blockOf_eq.mpr hb)).mp hi))
  · exact absurd (D.pairLay.injective (Fin.ext (Prod.mk.inj (toLex.injective h)).1))
      (by simp [stepPairNode])
  · exact absurd (D.pairLay.injective (Fin.ext (Prod.mk.inj (toLex.injective h)).1))
      (by simp [stepPairNode])
  · exact congrArg Sum.inr
      (Sum.inr.inj (D.pairLay.injective (Fin.ext (Prod.mk.inj (toLex.injective h)).1)))

private noncomputable def stepLayout : Layout D.StepNode :=
  (Layout.exists_lt_iff D.stepKey_injective).choose

private theorem stepLayout_lt_iff (x y : D.StepNode) :
    D.stepLayout x < D.stepLayout y ↔ D.stepKey x < D.stepKey y :=
  (Layout.exists_lt_iff D.stepKey_injective).choose_spec x y

private def nodeVerts : D.StepNode → Set (Vertex c)
  | .inl u => {u.val}
  | .inr e => D.pairVerts e

private theorem pairwiseDisjoint_nodeVerts :
    (univ : Set D.StepNode).PairwiseDisjoint D.nodeVerts := by
  rintro (u₁ | e₁) - (u₂ | e₂) - hne
  · refine disjoint_singleton.mpr fun h => hne (congrArg Sum.inl (Subtype.ext h))
  · refine disjoint_singleton_left.mpr fun hm => u₁.property ?_
    exact ⟨e₂.val, e₂.property, (D.mem_pairVerts_iff e₂ u₁.val).mp hm |>.imp Eq.symm Eq.symm⟩
  · refine disjoint_singleton_right.mpr fun hm => u₂.property ?_
    exact ⟨e₁.val, e₁.property, (D.mem_pairVerts_iff e₁ u₂.val).mp hm |>.imp Eq.symm Eq.symm⟩
  · exact D.disjoint_pairVerts fun h => hne (congrArg Sum.inr h)

private theorem exists_mem_nodeVerts (v : Vertex c) : ∃ x : D.StepNode, v ∈ D.nodeVerts x := by
  by_cases hv : D.Q.blockOf v ∈ D.Q.quotient.matchedVertices D.eqPairs
  · obtain ⟨e, he, hev⟩ := hv
    exact ⟨.inr ⟨e, he⟩, (D.mem_pairVerts_iff ⟨e, he⟩ v).mpr (hev.imp Eq.symm Eq.symm)⟩
  · exact ⟨.inl ⟨v, hv⟩, rfl⟩

private noncomputable def pastVerts (t : ℕ) : Set (Vertex c) :=
  ⋃ x ∈ D.stepLayout.initial t, D.nodeVerts x

private theorem pastVerts_zero : D.pastVerts 0 = ∅ := by
  simp [pastVerts]

private theorem pastVerts_of_card_le {t : ℕ} (ht : Nat.card D.StepNode ≤ t) :
    D.pastVerts t = univ := by
  ext v
  simp only [pastVerts, D.stepLayout.initial_of_card_le ht, mem_iUnion, mem_univ, exists_prop,
    true_and, iff_true]
  exact D.exists_mem_nodeVerts v

private theorem pastVerts_mono : Monotone D.pastVerts :=
  fun _ _ hst => biUnion_mono (fun _ hx => lt_of_lt_of_le hx hst) fun _ _ => subset_rfl

/-- An edge with an endpoint in `P` that touches `Pᶜ` crosses `P`. -/
private theorem mem_edgeCut_of_touching {P : Set (Vertex c)} {g : Edge c}
    (hend : src g ∈ P ∨ tgt g ∈ P) (htc : g ∈ (graph c).touching Pᶜ) :
    g ∈ (graph c).edgeCut P := by
  rcases hend with hs | ht <;> rcases htc with hc | hc
  · exact (hc hs).elim
  · exact fun hiff => hc (hiff.mp hs)
  · exact fun hiff => hc (hiff.mpr ht)
  · exact (hc ht).elim

/-- An edge crossing `P` touches `Qᶜ` for every `Q ⊆ P`. -/
private theorem mem_touching_compl_of_mem_edgeCut {P Q : Set (Vertex c)} (hQP : Q ⊆ P)
    {g : Edge c} (hg : g ∈ (graph c).edgeCut P) : g ∈ (graph c).touching Qᶜ := by
  by_contra hnt
  rw [Multigraph.mem_touching, mem_compl_iff, mem_compl_iff, not_or, not_not, not_not] at hnt
  exact hg (iff_of_true (hQP hnt.1) (hQP hnt.2))

/-- An edge crossing `P` has an endpoint in `P`. -/
private theorem end_mem_of_mem_edgeCut {P : Set (Vertex c)} {g : Edge c}
    (hg : g ∈ (graph c).edgeCut P) : src g ∈ P ∨ tgt g ∈ P :=
  by_contra fun h => hg (iff_of_false (fun hs => h (.inl hs)) fun ht => h (.inr ht))

/-- An edge crossing `P` with an endpoint in `Q ⊆ P` crosses `Q`. -/
private theorem mem_edgeCut_of_subset {P Q : Set (Vertex c)} (hQP : Q ⊆ P) {g : Edge c}
    (hend : src g ∈ Q ∨ tgt g ∈ Q) (hg : g ∈ (graph c).edgeCut P) : g ∈ (graph c).edgeCut Q :=
  mem_edgeCut_of_touching hend (mem_touching_compl_of_mem_edgeCut hQP hg)

private theorem disjoint_nodeVerts_pastVerts {x : D.StepNode} {t : ℕ}
    (hx : x ∉ D.stepLayout.initial t) : Disjoint (D.nodeVerts x) (D.pastVerts t) :=
  disjoint_iUnion₂_right.mpr fun _ _ =>
    D.pairwiseDisjoint_nodeVerts trivial trivial fun heq => hx (by rwa [heq])

private theorem pastVerts_succ_sdiff {t : ℕ} (ht : t < Nat.card D.StepNode) :
    D.pastVerts (t + 1) \ D.pastVerts t = D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩) ∧
      D.pastVerts (t + 1) = D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩) ∪ D.pastVerts t ∧
      Disjoint (D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩)) (D.pastVerts t) := by
  set x := D.stepLayout.symm ⟨t, ht⟩
  have hx_not : x ∉ D.stepLayout.initial t := by simp [x, Layout.mem_initial]
  have hun : D.pastVerts (t + 1) = D.nodeVerts x ∪ D.pastVerts t := by
    simp only [pastVerts, D.stepLayout.initial_succ ht, biUnion_insert]
    rfl
  have hdisj := D.disjoint_nodeVerts_pastVerts hx_not
  refine ⟨?_, hun, hdisj⟩
  rw [hun]
  ext v
  simp only [mem_sdiff, mem_union]
  have hd : v ∈ D.nodeVerts x → v ∉ D.pastVerts t := fun hv => disjoint_left.mp hdisj hv
  tauto

private theorem pairVerts_subset_pastVerts_iff (e : D.eqPairs) (t : ℕ) :
    D.pairVerts e ⊆ D.pastVerts t ↔ .inr e ∈ D.stepLayout.initial t := by
  refine ⟨fun hsub => ?_, fun hm v hv => mem_biUnion hm hv⟩
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (D.Q.ne_nil _ (D.Q.quotient.src e.val).property)
  have hv_pair : v ∈ D.pairVerts e := Or.inl hv
  obtain ⟨y, hy_in, hvy⟩ := mem_iUnion₂.mp (hsub hv_pair)
  have hy_eq : y = .inr e := by
    by_contra hne
    exact disjoint_left.mp (D.pairwiseDisjoint_nodeVerts trivial trivial hne) hvy hv_pair
  rwa [← hy_eq]

private theorem end_mem_pastVerts {e : D.eqPairs} {t : ℕ} (he : .inr e ∈ D.stepLayout.initial t)
    {g : Edge c} (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e) :
    src g ∈ D.pastVerts t ∨ tgt g ∈ D.pastVerts t :=
  hend.imp (fun h => mem_biUnion he h) fun h => mem_biUnion he h

private noncomputable def actPairs (t : ℕ) : Set D.eqPairs :=
  {e | .inr e ∈ D.stepLayout.initial t ∧
    (D.pinB e).val ∈ (graph c).edgeCut (D.pastVerts t) ∧
    (D.pinD e).val ∈ (graph c).edgeCut (D.pastVerts t)}

private noncomputable def singleCut (t : ℕ) : Set (Edge c) :=
  (graph c).edgeCut (D.pastVerts t) \ ⋃ e ∈ D.actPairs t, {(D.pinB e).val, (D.pinD e).val}

private theorem pinB_ne_pinD (e : D.eqPairs) : (D.pinB e).val ≠ (D.pinD e).val := by
  have := Fintype.ofFinite (Edge c)
  intro h
  exact Multigraph.outerHigh_src_ne_tgt D.Q.quotient_loopless
    D.hsat.injective_ends_quotient (D.h3 ⟨e.val, e.property.1⟩) D.score e.val (Subtype.ext h)

private theorem pin_end_in_pairVerts (e : D.eqPairs) (g : Edge c)
    (hg : g ∈ ({(D.pinA e).val, (D.pinB e).val, (D.pinC e).val, (D.pinD e).val} : Set (Edge c))) :
    src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e :=
  end_mem_of_mem_edgeCut (D.edgeCut_pairVerts e ▸ hg)

private theorem pinA_end (e : D.eqPairs) :
    src (D.pinA e).val ∈ D.pairVerts e ∨ tgt (D.pinA e).val ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinA e).val (by simp)

private theorem pinB_end (e : D.eqPairs) :
    src (D.pinB e).val ∈ D.pairVerts e ∨ tgt (D.pinB e).val ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinB e).val (by simp)

private theorem pinC_end (e : D.eqPairs) :
    src (D.pinC e).val ∈ D.pairVerts e ∨ tgt (D.pinC e).val ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinC e).val (by simp)

private theorem pinD_end (e : D.eqPairs) :
    src (D.pinD e).val ∈ D.pairVerts e ∨ tgt (D.pinD e).val ∈ D.pairVerts e :=
  D.pin_end_in_pairVerts e (D.pinD e).val (by simp)

private theorem pinBD_end (e : D.eqPairs) {g : Edge c}
    (hg : g ∈ ({(D.pinB e).val, (D.pinD e).val} : Set (Edge c))) :
    src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e := by
  rcases hg with rfl | rfl
  · exact D.pinB_end e
  · exact D.pinD_end e

private theorem mem_edgeCut_of_mem_pinBD {t : ℕ} {e : D.eqPairs} (he : e ∈ D.actPairs t)
    {g : Edge c} (hg : g ∈ ({(D.pinB e).val, (D.pinD e).val} : Set (Edge c))) :
    g ∈ (graph c).edgeCut (D.pastVerts t) := by
  rcases hg with rfl | rfl
  exacts [he.2.1, he.2.2]

/-- An edge with endpoints in two distinct pairs inside `D.pastVerts t` does not cross it. -/
private theorem notMem_edgeCut_of_ends {e₁ e₂ : D.eqPairs} (hne : e₁ ≠ e₂) {t : ℕ}
    (h₁ : .inr e₁ ∈ D.stepLayout.initial t) (h₂ : .inr e₂ ∈ D.stepLayout.initial t) {g : Edge c}
    (hend₁ : src g ∈ D.pairVerts e₁ ∨ tgt g ∈ D.pairVerts e₁)
    (hend₂ : src g ∈ D.pairVerts e₂ ∨ tgt g ∈ D.pairVerts e₂) :
    g ∉ (graph c).edgeCut (D.pastVerts t) := by
  have hsub₁ := (D.pairVerts_subset_pastVerts_iff e₁ t).mpr h₁
  have hsub₂ := (D.pairVerts_subset_pastVerts_iff e₂ t).mpr h₂
  rcases hend₁ with hs₁ | ht₁ <;> rcases hend₂ with hs₂ | ht₂
  · exact (disjoint_left.mp (D.disjoint_pairVerts hne) hs₁ hs₂).elim
  · exact fun h => h (iff_of_true (hsub₁ hs₁) (hsub₂ ht₂))
  · exact fun h => h (iff_of_true (hsub₂ hs₂) (hsub₁ ht₁))
  · exact (disjoint_left.mp (D.disjoint_pairVerts hne) ht₁ ht₂).elim

/-- A pair active at `t` whose vertices lie in `D.pastVerts s` for some `s ≤ t` is active at `s`. -/
private theorem mem_actPairs_of_le {s t : ℕ} (hst : s ≤ t) {e : D.eqPairs}
    (he : e ∈ D.actPairs t) (hs : .inr e ∈ D.stepLayout.initial s) : e ∈ D.actPairs s :=
  ⟨hs, mem_edgeCut_of_subset (D.pastVerts_mono hst) (D.end_mem_pastVerts hs (D.pinB_end e)) he.2.1,
    mem_edgeCut_of_subset (D.pastVerts_mono hst) (D.end_mem_pastVerts hs (D.pinD_end e)) he.2.2⟩

private theorem pairwiseDisjoint_actPairs (t : ℕ) :
    (D.actPairs t).PairwiseDisjoint fun e => ({(D.pinB e).val, (D.pinD e).val} : Set (Edge c)) := by
  intro e₁ he₁ e₂ he₂ hne
  exact disjoint_left.mpr fun g hg₁ hg₂ => D.notMem_edgeCut_of_ends hne he₁.1 he₂.1
    (D.pinBD_end e₁ hg₁) (D.pinBD_end e₂ hg₂) (D.mem_edgeCut_of_mem_pinBD he₁ hg₁)

private theorem ncard_singleCut_add_actPairs (t : ℕ) :
    (D.singleCut t).ncard + 2 * (D.actPairs t).ncard =
      ((graph c).edgeCut (D.pastVerts t)).ncard := by
  classical
  have := Fintype.ofFinite (Edge c)
  set U := ⋃ e ∈ D.actPairs t, ({(D.pinB e).val, (D.pinD e).val} : Set (Edge c))
  have hU_sub : U ⊆ (graph c).edgeCut (D.pastVerts t) := by
    rintro g ⟨_, ⟨e, rfl⟩, _, ⟨he, rfl⟩, hg⟩
    exact D.mem_edgeCut_of_mem_pinBD he hg
  have hU_card : U.ncard = 2 * (D.actPairs t).ncard := by
    have := Fintype.ofFinite D.eqPairs
    let Afin : Finset D.eqPairs := (D.actPairs t).toFinset
    have hU_eq : U = ((Afin.biUnion fun e => {(D.pinB e).val, (D.pinD e).val}) : Set (Edge c)) := by
      ext g
      simp only [U, Afin, Finset.coe_biUnion, Finset.mem_coe, mem_toFinset, mem_iUnion,
        Finset.coe_insert, Finset.coe_singleton]
    rw [hU_eq, ncard_coe_finset, Finset.card_biUnion]
    · have h2 (e : D.eqPairs) : ({(D.pinB e).val, (D.pinD e).val} : Finset (Edge c)).card = 2 :=
        Finset.card_pair (D.pinB_ne_pinD e)
      simp only [h2, Finset.sum_const, smul_eq_mul, mul_comm _ 2, Afin, ncard_eq_toFinset_card']
    · intro e₁ he₁ e₂ he₂ hne
      dsimp only [Function.onFun]
      rw [← Finset.disjoint_coe, Finset.coe_insert, Finset.coe_singleton, Finset.coe_insert,
        Finset.coe_singleton]
      exact D.pairwiseDisjoint_actPairs t (mem_toFinset.mp he₁) (mem_toFinset.mp he₂) hne
  have hsdiff := ncard_sdiff_add_ncard_of_subset hU_sub
  change (D.singleCut t).ncard + U.ncard = _ at hsdiff
  rw [hU_card] at hsdiff
  exact hsdiff

private theorem pinAC_notMem_masked (t : ℕ) {e : D.eqPairs} (he : e ∈ D.actPairs t) :
    (D.pinA e).val ∉ (⋃ e' ∈ D.actPairs t, ({(D.pinB e').val, (D.pinD e').val} : Set (Edge c))) ∧
      (D.pinC e).val ∉
        (⋃ e' ∈ D.actPairs t, ({(D.pinB e').val, (D.pinD e').val} : Set (Edge c))) := by
  have check (g : D.Q.external) (hg_end : g ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.val) \
      {e.val} ∪ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.val) \ {e.val})
      (hg_ne_B : g.val ≠ (D.pinB e).val) (hg_ne_D : g.val ≠ (D.pinD e).val) :
      g.val ∉ ⋃ e' ∈ D.actPairs t, ({(D.pinB e').val, (D.pinD e').val} : Set (Edge c)) := by
    rintro ⟨_, ⟨e', rfl⟩, _, ⟨he', rfl⟩, hmem⟩
    by_cases hee' : e = e'
    · subst hee'
      rcases hmem with h | h
      · exact hg_ne_B h
      · exact hg_ne_D h
    · have hend₁ : src g.val ∈ D.pairVerts e ∨ tgt g.val ∈ D.pairVerts e := by
        rcases hg_end with hg₁ | hg₂
        · have hs₁ :=
            (D.block_edgeCut_sdiff ⟨e.val, e.property.1⟩ (D.Q.quotient.src e.val)
              e.val (Or.inl rfl)).2
          have hm :
              g.val ∈ (graph c).edgeCut {v | v ∈ (D.Q.quotient.src e.val).val} \ {e.val.val} := by
            have := Fintype.ofFinite (Edge c)
            have hspec := (Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score
              (v := D.Q.quotient.src e.val) (Or.inl rfl)).2.1
            rw [hspec] at hg₁
            rw [hs₁]
            rcases hg₁ with rfl | rfl <;> simp
          rw [hs₁] at hm
          rcases hm with h | h <;> rw [h]
          · exact D.pinA_end e
          · exact D.pinB_end e
        · have hs₂ :=
            (D.block_edgeCut_sdiff ⟨e.val, e.property.1⟩ (D.Q.quotient.tgt e.val)
              e.val (Or.inr rfl)).2
          have hm :
              g.val ∈ (graph c).edgeCut {v | v ∈ (D.Q.quotient.tgt e.val).val} \ {e.val.val} := by
            have := Fintype.ofFinite (Edge c)
            have hspec := (Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score
              (v := D.Q.quotient.tgt e.val) (Or.inr rfl)).2.1
            rw [hspec] at hg₂
            rw [hs₂]
            rcases hg₂ with rfl | rfl <;> simp
          rw [hs₂] at hm
          rcases hm with h | h <;> rw [h]
          · exact D.pinC_end e
          · exact D.pinD_end e
      exact D.notMem_edgeCut_of_ends hee' he.1 he'.1 hend₁ (D.pinBD_end e' hmem)
        (D.mem_edgeCut_of_mem_pinBD he' hmem)
  have := Fintype.ofFinite (Edge c)
  have hinj := D.hsat.injective_ends_quotient
  have hbs := Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score
    (v := D.Q.quotient.src e.val) (Or.inl rfl)
  have hdt := Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score
    (v := D.Q.quotient.tgt e.val) (Or.inr rfl)
  have ha_mem : D.pinA e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.val) \ {e.val} := by
    dsimp only [pinA]; rw [hbs.2.1]; simp
  have hc_mem : D.pinC e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.val) \ {e.val} := by
    dsimp only [pinC]; rw [hdt.2.1]; simp
  have hd_mem : D.pinD e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.val) \ {e.val} := by
    dsimp only [pinD]; rw [hdt.2.1]; simp
  have hb_mem : D.pinB e ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.val) \ {e.val} := by
    dsimp only [pinB]; rw [hbs.2.1]; simp
  have no_cross {x y : D.Q.external}
      (hx : x ∈ D.Q.quotient.incidenceSet (D.Q.quotient.src e.val) \ {e.val})
      (hy : y ∈ D.Q.quotient.incidenceSet (D.Q.quotient.tgt e.val) \ {e.val}) : x.val ≠ y.val := by
    intro hxy
    have hxy' : x = y := Subtype.ext hxy
    subst hxy'
    rcases hx.1 with hs | ht <;> rcases hy.1 with hs' | ht'
    · exact D.Q.quotient_loopless e.val (hs.symm.trans hs')
    · exact hx.2 (hinj (by simp only [Multigraph.ends, hs, ht']))
    · exact hx.2 (hinj (by simp only [Multigraph.ends, ht, hs', Sym2.eq_swap]))
    · exact D.Q.quotient_loopless e.val (ht.symm.trans ht')
  exact ⟨check (D.pinA e) (Or.inl ha_mem) (fun h => hbs.1 (Subtype.ext h)) (no_cross ha_mem hd_mem),
    check (D.pinC e) (Or.inr hc_mem) (fun h => no_cross hb_mem hc_mem h.symm)
      (fun h => hdt.1 (Subtype.ext h))⟩

private theorem notMem_internalEdges_pairVerts {e : D.eqPairs} {g : D.Q.external}
    (hg_not : g ∉ D.eqPairs) : g.val ∉ internalEdges c (D.pairVerts e) := by
  rintro ⟨hs, ht⟩
  have hinj := D.hsat.injective_ends_quotient
  rw [D.mem_pairVerts_iff] at hs ht
  rcases hs with hs₁ | hs₂ <;> rcases ht with ht₁ | ht₂
  · exact g.property (hs₁.trans ht₁.symm)
  · change D.Q.quotient.src g = _ at hs₁
    change D.Q.quotient.tgt g = _ at ht₂
    have hge : g = e.val := hinj (by simp only [Multigraph.ends, hs₁, ht₂])
    exact hg_not (hge ▸ e.property)
  · change D.Q.quotient.src g = _ at hs₂
    change D.Q.quotient.tgt g = _ at ht₁
    have hge : g = e.val := hinj (by simp only [Multigraph.ends, hs₂, ht₁, Sym2.eq_swap])
    exact hg_not (hge ▸ e.property)
  · exact g.property (hs₂.trans ht₂.symm)

private theorem pin_notMem_eqPairs {B : D.Q.blocks} {e : D.eqPairs}
    (hB : B = D.Q.quotient.src e.val ∨ B = D.Q.quotient.tgt e.val) (g : D.Q.external)
    (hg : g ∈ D.Q.quotient.incidenceSet B \ {e.val}) : g ∉ D.eqPairs := by
  intro hg_eq
  refine hg.2 ?_
  by_contra hne
  exact disjoint_left.mp (D.isMatching_eqPairs hg_eq e.property hne) (hg.1.imp Eq.symm Eq.symm) hB

private theorem pinA_notMem_eqPairs (e : D.eqPairs) : D.pinA e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inl rfl) (D.pinA e) ?_
  dsimp only [pinA]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score (Or.inl rfl)).2.1]
  exact Or.inl rfl

private theorem pinB_notMem_eqPairs (e : D.eqPairs) : D.pinB e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inl rfl) (D.pinB e) ?_
  dsimp only [pinB]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score (Or.inl rfl)).2.1]
  exact Or.inr rfl

private theorem pinC_notMem_eqPairs (e : D.eqPairs) : D.pinC e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inr rfl) (D.pinC e) ?_
  dsimp only [pinC]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score (Or.inr rfl)).2.1]
  exact Or.inl rfl

private theorem pinD_notMem_eqPairs (e : D.eqPairs) : D.pinD e ∉ D.eqPairs := by
  have := Fintype.ofFinite (Edge c)
  refine D.pin_notMem_eqPairs (e := e) (Or.inr rfl) (D.pinD e) ?_
  dsimp only [pinD]
  rw [(Multigraph.outerLow_outerHigh_spec (D.h3 ⟨e.val, e.property.1⟩) D.score (Or.inr rfl)).2.1]
  exact Or.inr rfl

open Classical in
private noncomputable def intraPrefix : D.StepNode → Set (Vertex c)
  | .inl u => {v | v ∈ (D.Q.blockOf u.val).val.take ((D.Q.blockOf u.val).val.idxOf u.val)}
  | .inr _ => ∅

private theorem disjoint_preimage_intraPrefix (x : D.StepNode) :
    Disjoint (D.Q.blockOf ⁻¹' D.Q.quotient.pairNodeVerts D.M D.M D.score
      (D.pairLay.initial (D.pairLay (D.stepPairNode x) : ℕ))) (D.intraPrefix x) := by
  classical
  rcases x with u | e
  · refine disjoint_left.mpr fun v hvP hvT => ?_
    have hB : D.Q.blockOf v = D.Q.blockOf u.val :=
      D.Q.mem_iff_blockOf_eq.mp (List.mem_of_mem_take hvT)
    rw [mem_preimage, hB, Multigraph.mem_pairNodeVerts_of_notMem u.property,
      Layout.mem_initial] at hvP
    exact lt_irrefl _ hvP
  · exact disjoint_empty _

private theorem ncard_edgeCut_intraPrefix_le (x : D.StepNode) :
    ((graph c).edgeCut (D.intraPrefix x)).ncard ≤ 3 * Nat.log 2 (Nat.card (Vertex c)) := by
  classical
  have := Fintype.ofFinite (Vertex c)
  rcases x with u | e
  · dsimp only [intraPrefix]
    refine (D.Q.ncard_edgeCut_take_le _ (D.Q.blockOf u.val).property _
      (List.idxOf_lt_length_of_mem (D.Q.mem_blockOf u.val))).trans
      (Nat.mul_le_mul_left 3 (Nat.log_mono_right ?_))
    rw [Nat.card_eq_fintype_card]
    exact (D.Q.nodup _ (D.Q.blockOf u.val).property).length_le_card
  · dsimp only [intraPrefix]; simp

private theorem pastVerts_eq_preimage_union {t : ℕ} (ht : t < Nat.card D.StepNode) :
    let x := D.stepLayout.symm ⟨t, ht⟩
    let s := (D.pairLay (D.stepPairNode x) : ℕ)
    D.pastVerts t =
      D.Q.blockOf ⁻¹' D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s) ∪
        D.intraPrefix x := by
  classical
  dsimp only
  set x := D.stepLayout.symm ⟨t, ht⟩ with hx_def
  ext v
  simp only [pastVerts, Layout.initial_eq_of_lt_iff D.stepLayout_lt_iff ht, ← hx_def,
    mem_iUnion, mem_ofPred_eq, stepKey, Prod.Lex.toLex_lt_toLex, mem_union, mem_preimage]
  constructor
  · rintro ⟨y, hlt | ⟨hp_eq, hsub_lt⟩, hvy⟩
    · left
      rcases y with u' | e'
      · rcases hvy with rfl
        exact (Multigraph.mem_pairNodeVerts_of_notMem u'.property).mpr hlt
      · obtain hblk := (D.mem_pairVerts_iff e' v).mp hvy
        exact (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) e'
          (hblk.imp Eq.symm Eq.symm)).mpr hlt
    · right
      have hp_node : D.stepPairNode y = D.stepPairNode x :=
        D.pairLay.injective (Fin.ext hp_eq)
      rcases x with u | e
      · rcases y with u' | e'
        · have hb : D.Q.blockOf u'.val = D.Q.blockOf u.val :=
            Subtype.mk.inj (Sum.inl.inj hp_node)
          rcases hvy with rfl
          dsimp only [stepSubIdx, intraPrefix] at hsub_lt ⊢
          rw [hb] at hsub_lt
          exact (List.mem_take_iff_idxOf_lt (D.Q.mem_iff_blockOf_eq.mpr hb)).mpr hsub_lt
        · cases hp_node
      · dsimp only [stepSubIdx] at hsub_lt
        omega
  · rintro (hvP | hvT)
    · by_cases hv_mat : D.Q.blockOf v ∈ D.Q.quotient.matchedVertices D.eqPairs
      · obtain ⟨e₀, he₀, hev⟩ := hv_mat
        have hinr :=
          (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) ⟨e₀, he₀⟩ hev).mp hvP
        exact ⟨.inr ⟨e₀, he₀⟩, Or.inl hinr,
          (D.mem_pairVerts_iff ⟨e₀, he₀⟩ v).mpr (hev.imp Eq.symm Eq.symm)⟩
      · have hinl := (Multigraph.mem_pairNodeVerts_of_notMem hv_mat).mp hvP
        exact ⟨.inl ⟨v, hv_mat⟩, Or.inl hinl, rfl⟩
    · rcases x with u | e
      · dsimp only [intraPrefix] at hvT
        have hv_mem : v ∈ (D.Q.blockOf u.val).val := List.mem_of_mem_take hvT
        have hblk : D.Q.blockOf v = D.Q.blockOf u.val := D.Q.mem_iff_blockOf_eq.mp hv_mem
        have hp_eq : D.stepPairNode (.inl ⟨v, hblk ▸ u.property⟩) = D.stepPairNode (.inl u) := by
          dsimp only [stepPairNode]
          exact congrArg Sum.inl (Subtype.ext hblk)
        refine ⟨.inl ⟨v, hblk ▸ u.property⟩, Or.inr ⟨?_, ?_⟩, rfl⟩
        · exact congrArg (fun p => (D.pairLay p : ℕ)) hp_eq
        · dsimp only [stepSubIdx]
          rw [hblk]
          exact (List.mem_take_iff_idxOf_lt hv_mem).mp hvT
      · exact hvT.elim

/-- Effective real cut of `D` at step `t`, bounded by `D.pairLay`'s whole-block bound plus at most
`6 log₂ |Vertex c|` from the single unmatched block being expanded. -/
private theorem effective_cut_le {lam B_sup : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (1 - lam) * ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup)
    (t : ℕ) :
    ((D.singleCut t).ncard : ℝ) + (1 + lam) * ((D.actPairs t).ncard : ℝ) ≤
      B_sup + 6 * Nat.log 2 (Nat.card (Vertex c)) := by
  classical
  have := Fintype.ofFinite (Vertex c)
  have := Fintype.ofFinite (Edge c)
  have h1lam : 0 ≤ 1 - lam := by linarith
  have h1lam_le : 1 - lam ≤ 1 := by linarith
  have hB0 : 0 ≤ B_sup := by
    have hend := hsup (Nat.card (D.Q.quotient.PairNode D.M D.M D.score))
    dsimp only at hend
    have hinit : D.pairLay.initial (Nat.card (D.Q.quotient.PairNode D.M D.M D.score)) = univ :=
      D.pairLay.initial_of_card_le le_rfl
    have hP_u : D.Q.quotient.pairNodeVerts D.M D.M D.score univ = univ := by
      ext B; simp only [mem_univ, iff_true]
      by_cases hm : B ∈ D.Q.quotient.matchedVertices D.eqPairs
      · obtain ⟨e₀, he₀, heB⟩ := hm
        exact (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) ⟨e₀, he₀⟩ heB).mpr trivial
      · exact (Multigraph.mem_pairNodeVerts_of_notMem hm).mpr trivial
    rw [hinit, hP_u] at hend
    have hc0 : D.Q.quotient.edgeCut univ = ∅ := by ext g; simp
    have ha0 : D.Q.quotient.activeCleanPairs D.M D.M D.score univ = ∅ := by
      ext g; simp [Multigraph.activeCleanPairs, hc0]
    rw [hc0, ha0] at hend
    simpa using hend
  have hident : ((D.singleCut t).ncard : ℝ) + (1 + lam) * ((D.actPairs t).ncard : ℝ) =
      (((graph c).edgeCut (D.pastVerts t)).ncard : ℝ) -
        (1 - lam) * ((D.actPairs t).ncard : ℝ) := by
    have h := D.ncard_singleCut_add_actPairs t
    have hR : ((D.singleCut t).ncard : ℝ) + 2 * ((D.actPairs t).ncard : ℝ) =
        (((graph c).edgeCut (D.pastVerts t)).ncard : ℝ) := by exact_mod_cast h
    linarith
  rw [hident]
  rcases lt_or_ge t (Nat.card D.StepNode) with ht | ht
  · let x := D.stepLayout.symm ⟨t, ht⟩
    let s := (D.pairLay (D.stepPairNode x) : ℕ)
    let P_s := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
    let T_part := D.intraPrefix x
    have hT_disj : Disjoint (D.Q.blockOf ⁻¹' P_s) T_part := D.disjoint_preimage_intraPrefix x
    have hT_cut : ((graph c).edgeCut T_part).ncard ≤ 3 * Nat.log 2 (Nat.card (Vertex c)) :=
      D.ncard_edgeCut_intraPrefix_le x
    have hpast_eq : D.pastVerts t = D.Q.blockOf ⁻¹' P_s ∪ T_part := D.pastVerts_eq_preimage_union ht
    have hcut_le : ((graph c).edgeCut (D.pastVerts t)).ncard ≤
        (D.Q.quotient.edgeCut P_s).ncard + ((graph c).edgeCut T_part).ncard := by
      rw [hpast_eq, ← D.Q.ncard_edgeCut_preimage P_s]
      exact (graph c).ncard_edgeCut_union_le _ _
    let Lost : Set D.Q.external :=
      {e₀ | ∃ he : e₀ ∈ D.Q.quotient.activeCleanPairs D.M D.M D.score P_s,
        (⟨e₀, ⟨he.1, he.2.1⟩⟩ : D.eqPairs) ∉ D.actPairs t}
    have hact_split : (D.Q.quotient.activeCleanPairs D.M D.M D.score P_s).ncard ≤
        (D.actPairs t).ncard + Lost.ncard := by
      have hsub : D.Q.quotient.activeCleanPairs D.M D.M D.score P_s ⊆
          (Subtype.val '' D.actPairs t) ∪ Lost := by
        intro e₀ he₀
        by_cases hm : (⟨e₀, ⟨he₀.1, he₀.2.1⟩⟩ : D.eqPairs) ∈ D.actPairs t
        · exact Or.inl ⟨_, hm, rfl⟩
        · exact Or.inr ⟨he₀, hm⟩
      refine (ncard_le_ncard hsub).trans ((ncard_union_le _ _).trans ?_)
      rw [ncard_image_of_injective _ Subtype.val_injective]
    have hLost_le : Lost.ncard ≤ ((graph c).edgeCut T_part).ncard := by
      have h_wit : ∀ e₀ ∈ Lost, ∃ g ∈ (graph c).edgeCut T_part,
          g ∈ ({(D.Q.quotient.outerHigh D.score (D.Q.quotient.src e₀) e₀).val,
            (D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt e₀) e₀).val} : Set (Edge c)) := by
        rintro e₀ ⟨he₀, hnot⟩
        let e : D.eqPairs := ⟨e₀, ⟨he₀.1, he₀.2.1⟩⟩
        have hinr_s : .inr e ∈ D.pairLay.initial s :=
          (Multigraph.mem_pairNodeVerts_of_mem D.hM (Subset.refl _) e (Or.inl rfl)).mp he₀.2.2.1
        have hinr_t : .inr e ∈ D.stepLayout.initial t := by
          simp only [Layout.initial_eq_of_lt_iff D.stepLayout_lt_iff ht, mem_ofPred_eq, stepKey,
            Prod.Lex.toLex_lt_toLex]
          exact Or.inl hinr_s
        have hB_pre : (D.pinB e).val ∈ (graph c).edgeCut (D.Q.blockOf ⁻¹' P_s) := he₀.2.2.2.2.1
        have hD_pre : (D.pinD e).val ∈ (graph c).edgeCut (D.Q.blockOf ⁻¹' P_s) := he₀.2.2.2.2.2
        have sdiff_cut {g : Edge c} (hg₁ : g ∈ (graph c).edgeCut (D.Q.blockOf ⁻¹' P_s))
            (hg₂ : g ∉ (graph c).edgeCut (D.pastVerts t)) : g ∈ (graph c).edgeCut T_part := by
          rw [hpast_eq] at hg₂
          simp only [Multigraph.mem_edgeCut, mem_union, not_not] at hg₁ hg₂ ⊢
          lrat_tauto [(disjoint_left.mp hT_disj) (a := (graph c).src g),
            (disjoint_left.mp hT_disj) (a := (graph c).tgt g)]
        by_cases hB_t : (D.pinB e).val ∈ (graph c).edgeCut (D.pastVerts t)
        · have hD_not : (D.pinD e).val ∉ (graph c).edgeCut (D.pastVerts t) :=
            fun hD_t => hnot ⟨hinr_t, hB_t, hD_t⟩
          exact ⟨(D.pinD e).val, sdiff_cut hD_pre hD_not, Or.inr rfl⟩
        · exact ⟨(D.pinB e).val, sdiff_cut hB_pre hB_t, Or.inl rfl⟩
      choose g_of hg_cut hg_pair using fun e₀ : Lost => h_wit e₀.val e₀.property
      have hinj_g : Function.Injective fun e₀ : Lost =>
          (⟨g_of e₀, hg_cut e₀⟩ : (graph c).edgeCut T_part) := by
        intro x₁ x₂ heq
        have hg_eq : g_of x₁ = g_of x₂ := congrArg Subtype.val heq
        by_contra hne
        have hne_val : x₁.val ≠ x₂.val := fun h => hne (Subtype.ext h)
        have hdisj := Multigraph.pairwiseDisjoint_activeCleanPairs D.hM (Subset.refl _)
          (D.h3 ⟨x₁.val, x₁.property.1.1⟩) D.score P_s x₁.property.1 x₂.property.1 hne_val
        have hg_ext : g_of x₁ ∈ D.Q.external := by
          rcases hg_pair x₁ with h | h <;> rw [h] <;> exact Subtype.prop _
        let gx : D.Q.external := ⟨g_of x₁, hg_ext⟩
        have hm₁ : gx ∈ ({D.Q.quotient.outerHigh D.score (D.Q.quotient.src x₁.val) x₁.val,
            D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt x₁.val) x₁.val} : Set D.Q.external) :=
          Or.imp Subtype.ext Subtype.ext (hg_pair x₁)
        have hm₂ : gx ∈ ({D.Q.quotient.outerHigh D.score (D.Q.quotient.src x₂.val) x₂.val,
            D.Q.quotient.outerHigh D.score (D.Q.quotient.tgt x₂.val) x₂.val} : Set D.Q.external) :=
          Or.imp (fun h => Subtype.ext (hg_eq.trans h)) (fun h => Subtype.ext (hg_eq.trans h))
            (hg_pair x₂)
        exact disjoint_left.mp hdisj hm₁ hm₂
      have h1 := Nat.card_le_card_of_injective _ hinj_g
      rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
    have hsup_s := hsup s
    dsimp only at hsup_s
    have hcut_R : (((graph c).edgeCut (D.pastVerts t)).ncard : ℝ) ≤
        ((D.Q.quotient.edgeCut P_s).ncard : ℝ) + ((graph c).edgeCut T_part).ncard := by
      exact_mod_cast hcut_le
    have hact_R : ((D.Q.quotient.activeCleanPairs D.M D.M D.score P_s).ncard : ℝ) ≤
        ((D.actPairs t).ncard : ℝ) + ((graph c).edgeCut T_part).ncard := by
      exact_mod_cast hact_split.trans (Nat.add_le_add_left hLost_le _)
    have hT_R : (((graph c).edgeCut T_part).ncard : ℝ) ≤
        3 * Nat.log 2 (Nat.card (Vertex c)) := by exact_mod_cast hT_cut
    have hm1 := mul_le_mul_of_nonneg_left hact_R h1lam
    have hm2 := mul_le_mul_of_nonneg_right h1lam_le
      (Nat.cast_nonneg ((graph c).edgeCut T_part).ncard)
    linarith
  · have hp_univ : D.pastVerts t = univ := D.pastVerts_of_card_le ht
    have hc0 : (graph c).edgeCut (D.pastVerts t) = ∅ := by ext g; simp [hp_univ]
    have ha0 : D.actPairs t = ∅ := by ext e; simp [actPairs, hc0]
    rw [hc0, ha0]
    simp only [ncard_empty, Nat.cast_zero, mul_zero, sub_zero]
    positivity

/-- State of `D.branchingProgram` at layer `t` induced by an edge assignment `α`. -/
private noncomputable def stateAt (t : ℕ) (α : Edge c → Bool) :
    (Edge c → Option Bool) × (D.eqPairs → Option (Fin 3)) :=
  letI := Classical.propDecidable
  (fun f => if f ∈ D.singleCut t then some (α f) else none,
    fun e => if e ∈ D.actPairs t then some (D.rectIdx e α) else none)

private theorem stateAt_zero (α : Edge c → Bool) :
    D.stateAt 0 α = (fun _ => none, fun _ => none) := by
  have hc0 : (graph c).edgeCut (D.pastVerts 0) = ∅ := by simp [D.pastVerts_zero]
  have hs0 : D.singleCut 0 = ∅ := by simp [singleCut, hc0]
  have ha0 : D.actPairs 0 = ∅ := by ext e; simp [actPairs, hc0]
  ext f <;> simp [stateAt, hs0, ha0]

private theorem stateAt_of_card_le {t : ℕ} (ht : Nat.card D.StepNode ≤ t) (α : Edge c → Bool) :
    D.stateAt t α = (fun _ => none, fun _ => none) := by
  have hc0 : (graph c).edgeCut (D.pastVerts t) = ∅ := by
    ext g; simp [D.pastVerts_of_card_le ht]
  have hs0 : D.singleCut t = ∅ := by simp [singleCut, hc0]
  have ha0 : D.actPairs t = ∅ := by ext e; simp [actPairs, hc0]
  ext f <;> simp [stateAt, hs0, ha0]

private theorem stateAt_eq_iff {t : ℕ} {α β : Edge c → Bool} :
    D.stateAt t α = D.stateAt t β ↔
      EqOn α β (D.singleCut t) ∧ ∀ e ∈ D.actPairs t, D.rectIdx e α = D.rectIdx e β := by
  simp only [stateAt, Prod.mk.injEq]
  refine and_congr ?_ ?_
  · refine ⟨fun h f hf => ?_, fun h => funext fun f => ?_⟩
    · simpa [hf] using congrFun h f
    · by_cases hf : f ∈ D.singleCut t
      · simp [hf, h hf]
      · simp [hf]
  · refine ⟨fun h e he => ?_, fun h => funext fun e => ?_⟩
    · simpa [he] using congrFun h e
    · by_cases he : e ∈ D.actPairs t
      · simp [he, h e he]
      · simp [he]

/-- **`3`-state pair-compressed read-once branching program** associated with `D` and a constraint
network `N` on `Compiler.graph c`. -/
noncomputable def branchingProgram {ι : Type*}
    (N : Network Bool ι (Vertex c) (Edge c)) :
    ReadOnceNBP ι Bool ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) where
  length := Nat.card D.StepNode + 1
  revealed t := if t ≤ Nat.card D.StepNode then N.readIn (D.pastVerts t) else univ
  revealed_zero := by simp [D.pastVerts_zero]
  revealed_length := by simp
  revealed_mono s t hst := by
    dsimp only
    split_ifs with hs ht ht
    · rintro i ⟨v, hv, hi⟩
      exact ⟨v, D.pastVerts_mono hst hv, hi⟩
    · exact subset_univ _
    · exact absurd (hst.trans ht) hs
    · exact le_rfl
  start := (fun _ => none, fun _ => none)
  accept := (fun _ => none, fun _ => none)
  Edge t m a m' := ∃ (β : Edge c → Bool) (y : ι → Bool),
    m = D.stateAt t β ∧ m' = D.stateAt (t + 1) β ∧
    ((if t + 1 ≤ Nat.card D.StepNode then N.readIn (D.pastVerts (t + 1)) else univ) \
      (if t ≤ Nat.card D.StepNode then N.readIn (D.pastVerts t) else univ)).domRestrict y = a ∧
    (∀ v ∈ D.pastVerts (t + 1) \ D.pastVerts t, N.Constraint v y β) ∧
    (∀ e ∈ D.actPairs t, GateSatisfies I (D.pairVerts e) β)

/-- `D.branchingProgram N` always has positive length. -/
theorem length_branchingProgram_pos {ι : Type*}
    (N : Network Bool ι (Vertex c) (Edge c)) : 0 < (D.branchingProgram N).length :=
  Nat.succ_pos _

section NetworkProps

variable {ι : Type*} (N : Network Bool ι (Vertex c) (Edge c))
  (hG : N.toMultigraph = graph c)
  (hclean_N : ∀ v, IsCleanVertex v →
    (∀ x α, N.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
      N.readAt v = ∅)

include hG hclean_N

omit hG in
private theorem isAcceptingPath_stateAt {x : ι → Bool} {α : Edge c → Bool}
    (hα : N.Satisfies x α) :
    (D.branchingProgram N).IsAcceptingPath x fun t => D.stateAt t α where
  start := D.stateAt_zero α
  accept := D.stateAt_of_card_le (Nat.le_succ _) α
  edge _ _ := ⟨α, x, rfl, rfl, rfl, fun v _ => hα v,
    fun e _ v hv => (hclean_N v (D.isCleanVertex_of_mem_pairVerts e hv)).1 x α |>.mp (hα v)⟩

/-- **Three-region prefix gluing.** An accepting path of `D.branchingProgram N` comes from a global
satisfying assignment `α` whose `stateAt` matches the path at every layer. -/
private theorem exists_satisfies_of_isAcceptingPath {x : ι → Bool}
    {γ : ℕ → (Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))}
    (hγ : (D.branchingProgram N).IsAcceptingPath x γ) :
    ∃ α, N.Satisfies x α ∧ ∀ s ≤ Nat.card D.StepNode + 1, γ s = D.stateAt s α := by
  classical
  -- Prove by induction on `t ≤ Nat.card D.StepNode + 1`.
  suffices ∀ t ≤ Nat.card D.StepNode + 1, ∃ (α : Edge c → Bool) (x_t : ι → Bool),
      EqOn x_t x ((D.branchingProgram N).revealed t) ∧
      (∀ v ∈ D.pastVerts t, N.Constraint v x_t α) ∧
      (∀ s ≤ t, γ s = D.stateAt s α) by
    obtain ⟨α, x_T, hx_T, hsat_T, hγ_T⟩ := this (Nat.card D.StepNode + 1) le_rfl
    have hx_eq : x_T = x := funext fun i => hx_T (by
      change i ∈ (D.branchingProgram N).revealed (D.branchingProgram N).length
      rw [(D.branchingProgram N).revealed_length]
      trivial)
    rw [hx_eq, D.pastVerts_of_card_le (Nat.le_succ _)] at hsat_T
    exact ⟨α, fun v => hsat_T v trivial, hγ_T⟩
  intro t ht_all
  induction t with
  | zero =>
    refine ⟨fun _ => false, x, eqOn_refl _ _, ?_, fun s hs => ?_⟩
    · rw [D.pastVerts_zero]; intro v hv; exact hv.elim
    · obtain rfl : s = 0 := Nat.eq_zero_of_le_zero hs
      exact hγ.start.trans (D.stateAt_zero _).symm
  | succ t ih =>
    obtain ⟨α_t, x_t, hx_t, hsat_t, hγ_t⟩ := ih (Nat.le_of_succ_le ht_all)
    obtain ⟨β, y, hm, hm', hdom, hcon_step, hgate_β⟩ := hγ.edge t ht_all
    have hst_eq : D.stateAt t α_t = D.stateAt t β := (hγ_t t le_rfl).symm.trans hm
    obtain ⟨heq_single, heq_rect⟩ := D.stateAt_eq_iff.mp hst_eq
    -- Splice inputs on `revealed t`.
    let x' : ι → Bool := fun i => if i ∈ (D.branchingProgram N).revealed t then x_t i else y i
    have hx'_eq : EqOn x' x ((D.branchingProgram N).revealed (t + 1)) := by
      intro i hi
      by_cases hit : i ∈ (D.branchingProgram N).revealed t
      · dsimp only [x']; rw [ite_eq_left hit]; exact hx_t hit
      · dsimp only [x']; rw [ite_eq_right hit]
        exact congrFun hdom ⟨i, hi, hit⟩
    have hrev (ht : t ≤ Nat.card D.StepNode) :
        (D.branchingProgram N).revealed t = N.readIn (D.pastVerts t) := ite_eq_left ht
    -- At `t = Nat.card D.StepNode`, `pastVerts t = univ` and only unread inputs are updated.
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp ht_all) with rfl | ht_lt
    · refine ⟨α_t, x', hx'_eq, ?_, fun s hs => ?_⟩
      · intro v hv
        refine N.constraint_congr v x_t x' α_t α_t (fun i hsite => ?_) (fun _ _ => rfl)
          (hsat_t v (by rw [D.pastVerts_of_card_le le_rfl]; trivial))
        have hirev : i ∈ (D.branchingProgram N).revealed (Nat.card D.StepNode) := by
          rw [hrev le_rfl, D.pastVerts_of_card_le le_rfl]; exact ⟨v, trivial, hsite⟩
        dsimp only [x']; exact (ite_eq_left hirev).symm
      · rcases Nat.of_le_succ hs with hs' | rfl
        · exact hγ_t s hs'
        · exact hγ.accept.trans (D.stateAt_of_card_le (Nat.le_succ _) α_t).symm
    -- Main step `t < Nat.card D.StepNode`: three-region splice of `α_t` and `β`.
    -- Baseline assignment `γ₀`: `β` on `(graph c).touching (D.pastVerts t)ᶜ`, `α_t` elsewhere.
    let γ₀ : Edge c → Bool := fun g =>
      if g ∈ (graph c).touching (D.pastVerts t)ᶜ then β g else α_t g
    -- `γ₀ = α_t` on edges with an endpoint in `D.pastVerts t` that, if they cross it, are not
    -- masked pins of an active pair.
    have hγ₀_eq {g : Edge c} (hend : src g ∈ D.pastVerts t ∨ tgt g ∈ D.pastVerts t)
        (hnotM : g ∈ (graph c).edgeCut (D.pastVerts t) →
          g ∉ ⋃ e' ∈ D.actPairs t, ({(D.pinB e').val, (D.pinD e').val} : Set (Edge c))) :
        γ₀ g = α_t g := by
      dsimp only [γ₀]
      split_ifs with htc
      · have hg_cut := mem_edgeCut_of_touching hend htc
        exact (heq_single ⟨hg_cut, hnotM hg_cut⟩).symm
      · rfl
    -- On every `e ∈ D.actPairs t`, check `(γ₀ pinB, γ₀ pinD) = (β pinB, β pinD)` and
    -- `(γ₀ pinA, γ₀ pinC) = (α_t pinA, α_t pinC)`, giving internal witness `β_e`.
    have hex_patch : ∀ e : D.actPairs t,
        D.rectIdx e.val γ₀ = D.rectIdx e.val α_t ∧
        ∃ β_e : Edge c → Bool,
          EqOn β_e γ₀ (internalEdges c (D.pairVerts e.val))ᶜ ∧
          GateSatisfies I (D.pairVerts e.val) β_e := by
      rintro ⟨e, he⟩
      obtain ⟨hA_notM, hC_notM⟩ := D.pinAC_notMem_masked t he
      have hB : γ₀ (D.pinB e).val = β (D.pinB e).val :=
        ite_eq_left (mem_touching_compl_of_mem_edgeCut subset_rfl he.2.1)
      have hD : γ₀ (D.pinD e).val = β (D.pinD e).val :=
        ite_eq_left (mem_touching_compl_of_mem_edgeCut subset_rfl he.2.2)
      have hA := hγ₀_eq (D.end_mem_pastVerts he.1 (D.pinA_end e)) fun _ => hA_notM
      have hC := hγ₀_eq (D.end_mem_pastVerts he.1 (D.pinC_end e)) fun _ => hC_notM
      have hsat_α : GateSatisfies I (D.pairVerts e) α_t := fun v hv =>
        (hclean_N v (D.isCleanVertex_of_mem_pairVerts e hv)).1 x_t α_t |>.mp
          (hsat_t v (mem_biUnion he.1 hv))
      have hrc_α := D.rectIdx_spec_of_sat e hsat_α
      have hrc_β := D.rectIdx_spec_of_sat e (hgate_β e he)
      rw [← heq_rect e he] at hrc_β
      exact D.rectIdx_eq_and_realize e (r := D.rectIdx e α_t)
        ⟨by rw [hB, hD]; exact hrc_β.1, by rw [hA, hC]; exact hrc_α.2⟩
    choose hrect_γ₀ β_patch hβ_eq hβ_sat using hex_patch
    -- Assemble `α'` by patching `internalEdges c (D.pairVerts e)` for each `e : D.actPairs t`.
    let α' : Edge c → Bool := fun g =>
      if h : ∃ e : D.actPairs t, g ∈ internalEdges c (D.pairVerts e.val) then
        β_patch h.choose g
      else γ₀ g
    have hα'_not_int {g : Edge c}
        (hn : ¬∃ e : D.actPairs t, g ∈ internalEdges c (D.pairVerts e.val)) : α' g = γ₀ g := by
      dsimp only [α']; exact dite_eq_right hn
    have hα'_on_pair (e : D.actPairs t) :
        EqOn α' (β_patch e) ((graph c).touching (D.pairVerts e.val)) := by
      intro g hg
      dsimp only [α']
      split_ifs with hex
      · set e' := hex.choose
        have he' : g ∈ internalEdges c (D.pairVerts e'.val) := hex.choose_spec
        suffices e' = e by rw [this]
        by_contra hne
        have hne_val : e'.val ≠ e.val := fun h => hne (Subtype.ext h)
        rcases hg with hs | ht
        · exact disjoint_left.mp (D.disjoint_pairVerts hne_val) he'.1 hs
        · exact disjoint_left.mp (D.disjoint_pairVerts hne_val) he'.2 ht
      · have hni : g ∉ internalEdges c (D.pairVerts e.val) := fun hin => hex ⟨e, hin⟩
        exact (hβ_eq e hni).symm
    have hα'_touch_compl : EqOn α' β ((graph c).touching (D.pastVerts t)ᶜ) := by
      intro g hg
      rw [hα'_not_int]
      · exact ite_eq_left hg
      · rintro ⟨⟨e, he⟩, hin⟩
        have hsub_e := (D.pairVerts_subset_pastVerts_iff e t).mpr he.1
        rcases hg with hs | ht
        · exact hs (hsub_e hin.1)
        · exact ht (hsub_e hin.2)
    -- Pins are never internal to a pair, so `α'` and `γ₀` have the same rectangle indices.
    have hrect_α' (e : D.eqPairs) : D.rectIdx e α' = D.rectIdx e γ₀ := by
      have hpin (p : D.Q.external) (hp : p ∉ D.eqPairs) : α' p.val = γ₀ p.val :=
        hα'_not_int fun ⟨_, hin⟩ => D.notMem_internalEdges_pairVerts hp hin
      exact D.rectIdx_congr e (hpin _ (D.pinA_notMem_eqPairs e)) (hpin _ (D.pinB_notMem_eqPairs e))
        (hpin _ (D.pinC_notMem_eqPairs e)) (hpin _ (D.pinD_notMem_eqPairs e))
    refine ⟨α', x', hx'_eq, ?_, ?_⟩
    · -- Satisfaction on `D.pastVerts (t + 1)`.
      obtain ⟨hsdiff, hun, _⟩ := D.pastVerts_succ_sdiff ht_lt
      rw [hun]
      rintro v (hv_new | hv_old)
      · -- Vertex in `D.nodeVerts x = pastVerts (t + 1) \ pastVerts t ⊆ (pastVerts t)ᶜ`.
        have hv_compl : v ∈ (D.pastVerts t)ᶜ :=
          disjoint_left.mp (D.pastVerts_succ_sdiff ht_lt).2.2 hv_new
        refine N.constraint_congr v y x' β α' (fun i hsite => ?_) (fun g hg => ?_)
          (hcon_step v (hsdiff ▸ hv_new))
        · have hnot_rev : i ∉ (D.branchingProgram N).revealed t := by
            rw [hrev ht_lt.le]
            rintro ⟨u, hu, husite⟩
            exact hv_compl (Option.some.inj (husite.symm.trans hsite) ▸ hu)
          dsimp only [x']; exact (ite_eq_right hnot_rev).symm
        · symm
          apply hα'_touch_compl
          rw [hG] at hg
          rcases hg with hs | ht
          · exact Or.inl (hs.symm ▸ hv_compl)
          · exact Or.inr (ht.symm ▸ hv_compl)
      · -- Vertex in `D.pastVerts t`: either in some `pairVerts e` (`e ∈ actPairs t`) or outside.
        by_cases hv_act : ∃ e : D.actPairs t, v ∈ D.pairVerts e.val
        · obtain ⟨e, hve⟩ := hv_act
          have hv_cl := D.isCleanVertex_of_mem_pairVerts e.val hve
          rw [(hclean_N v hv_cl).1 x' α']
          exact gateSatisfies_congr (fun g hg => (hα'_on_pair e hg).symm) (hβ_sat e) v hve
        · refine N.constraint_congr v x_t x' α_t α' (fun i hsite => ?_) (fun g hg => ?_)
            (hsat_t v hv_old)
          · have hirev : i ∈ (D.branchingProgram N).revealed t := by
              rw [hrev ht_lt.le]; exact ⟨v, hv_old, hsite⟩
            dsimp only [x']; exact (ite_eq_left hirev).symm
          · rw [hG] at hg
            symm
            rw [hα'_not_int]
            · refine hγ₀_eq ?_ fun hg_cut => ?_
              · rcases hg with hs | ht
                · exact .inl (show (graph c).src g ∈ _ from hs ▸ hv_old)
                · exact .inr (show (graph c).tgt g ∈ _ from ht ▸ hv_old)
              rintro ⟨_, ⟨e', rfl⟩, _, ⟨he', rfl⟩, hmem⟩
              have hsub := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'.1
              refine hv_act ⟨⟨e', he'⟩, ?_⟩
              rcases hg with hs | ht <;> rcases D.pinBD_end e' hmem with hs' | ht'
              · exact hs ▸ hs'
              · exact (hg_cut (iff_of_true (hs.symm ▸ hv_old) (hsub ht'))).elim
              · exact (hg_cut (iff_of_true (hsub hs') (ht.symm ▸ hv_old))).elim
              · exact ht ▸ ht'
            · rintro ⟨e', hin⟩
              rcases hg with hs | ht
              · exact hv_act ⟨e', hs ▸ hin.1⟩
              · exact hv_act ⟨e', ht ▸ hin.2⟩
    · -- Path agreement `∀ s ≤ t + 1, γ s = D.stateAt s α'`.
      intro s hs_le
      rcases Nat.of_le_succ hs_le with hs_lt | rfl
      · -- Earlier layer `s ≤ t`: show `D.stateAt s α' = D.stateAt s α_t`.
        rw [hγ_t s hs_lt, eq_comm, D.stateAt_eq_iff]
        have hpast_sub : D.pastVerts s ⊆ D.pastVerts t := D.pastVerts_mono hs_lt
        refine ⟨fun g hg => ?_, fun e he_s => ?_⟩
        · -- `g ∈ D.singleCut s`: cannot be internal to any `pairVerts e'`.
          rw [hα'_not_int]
          · refine hγ₀_eq ((end_mem_of_mem_edgeCut hg.1).imp (fun h => hpast_sub h)
              fun h => hpast_sub h) fun hg_cut_t => ?_
            -- If `g ∈ {pinB e', pinD e'}` for `e' ∈ actPairs t`, then `e' ∈ actPairs s`,
            -- contradicting `g ∈ singleCut s`!
            rintro ⟨_, ⟨e', rfl⟩, _, ⟨he'_t, rfl⟩, hmem⟩
            have hinr_s : .inr e' ∈ D.stepLayout.initial s := by
              by_contra hnot_s
              -- One endpoint of `g` is in `pairVerts e'` (`∉ pastVerts s`) and the other is in
              -- `(pastVerts t)ᶜ ⊆ (pastVerts s)ᶜ`, contradicting `g ∈ edgeCut (pastVerts s)`!
              have hdisj_s := D.disjoint_nodeVerts_pastVerts hnot_s
              have hsub_t := (D.pairVerts_subset_pastVerts_iff e' t).mpr he'_t.1
              rcases D.pinBD_end e' hmem with hs_p | ht_p
              · exact hg.1 (iff_of_false (disjoint_left.mp hdisj_s hs_p)
                  fun ht_in => hg_cut_t (iff_of_true (hsub_t hs_p) (hpast_sub ht_in)))
              · exact hg.1 (iff_of_false
                  (fun hs_in => hg_cut_t (iff_of_true (hpast_sub hs_in) (hsub_t ht_p)))
                  (disjoint_left.mp hdisj_s ht_p))
            exact hg.2 (mem_biUnion (D.mem_actPairs_of_le hs_lt he'_t hinr_s) hmem)
          · rintro ⟨⟨e', he'⟩, hin⟩
            by_cases hinr_s : .inr e' ∈ D.stepLayout.initial s
            · have hsub_s := (D.pairVerts_subset_pastVerts_iff e' s).mpr hinr_s
              exact hg.1 (iff_of_true (hsub_s hin.1) (hsub_s hin.2))
            · have hdisj_s := D.disjoint_nodeVerts_pastVerts hinr_s
              exact hg.1 (iff_of_false (disjoint_left.mp hdisj_s hin.1)
                (disjoint_left.mp hdisj_s hin.2))
        · -- `e ∈ D.actPairs s`: check `D.rectIdx e α' = D.rectIdx e α_t`.
          have hinr_t : .inr e ∈ D.stepLayout.initial t := lt_of_lt_of_le he_s.1 hs_lt
          rw [hrect_α']
          by_cases he_t : e ∈ D.actPairs t
          · exact hrect_γ₀ ⟨e, he_t⟩
          · -- When `e ∉ actPairs t`, no pin of `e` is a masked pin of some `e' ∈ actPairs t`,
            -- so `γ₀` agrees with `α_t` on all 4 pins of `e`!
            have pin_eq (g : Edge c) (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e) :
                γ₀ g = α_t g := by
              refine hγ₀_eq (D.end_mem_pastVerts hinr_t hend) fun hg_cut_t => ?_
              rintro ⟨_, ⟨e', rfl⟩, _, ⟨he'_t, rfl⟩, hmem⟩
              exact D.notMem_edgeCut_of_ends (fun (hee' : e = e') => he_t (hee' ▸ he'_t)) hinr_t
                he'_t.1 hend (D.pinBD_end e' hmem) hg_cut_t
            exact D.rectIdx_congr e (pin_eq _ (D.pinA_end e)) (pin_eq _ (D.pinB_end e))
              (pin_eq _ (D.pinC_end e)) (pin_eq _ (D.pinD_end e))
      · -- Layer `t + 1`: show `γ (t + 1) = D.stateAt (t + 1) α'`.
        rw [hm', eq_comm, D.stateAt_eq_iff]
        refine ⟨fun g hg => hα'_touch_compl
          (mem_touching_compl_of_mem_edgeCut (D.pastVerts_mono (Nat.le_succ t)) hg.1),
          fun e he_t1 => ?_⟩
        -- Either `e ∈ actPairs t`, or `e` was processed at step `t` (`pairVerts e ⊆
        -- (pastVerts t)ᶜ`, so all 4 pins touch `(pastVerts t)ᶜ`)!
        by_cases hinr_t : .inr e ∈ D.stepLayout.initial t
        · have he_t := D.mem_actPairs_of_le (Nat.le_succ t) he_t1 hinr_t
          rw [hrect_α', hrect_γ₀ ⟨e, he_t⟩, heq_rect e he_t]
        · have hdisj_e := D.disjoint_nodeVerts_pastVerts hinr_t
          have touch_pin {g : Edge c} (hend : src g ∈ D.pairVerts e ∨ tgt g ∈ D.pairVerts e) :
              g ∈ (graph c).touching (D.pastVerts t)ᶜ :=
            hend.imp (fun hs => disjoint_left.mp hdisj_e hs) (fun ht => disjoint_left.mp hdisj_e ht)
          exact D.rectIdx_congr e (hα'_touch_compl (touch_pin (D.pinA_end e)))
            (hα'_touch_compl (touch_pin (D.pinB_end e)))
            (hα'_touch_compl (touch_pin (D.pinC_end e)))
            (hα'_touch_compl (touch_pin (D.pinD_end e)))

theorem accepted_branchingProgram : (D.branchingProgram N).accepted = N.accepted := by
  ext x
  exact ⟨fun ⟨γ, hγ⟩ => by
      obtain ⟨α, hα, -⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N hγ
      exact ⟨α, hα⟩,
    fun ⟨α, hα⟩ => ⟨_, D.isAcceptingPath_stateAt N hclean_N hα⟩⟩

theorem unambiguous_branchingProgram
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β) :
    (D.branchingProgram N).Unambiguous := by
  intro x γ δ hγ hδ t ht
  obtain ⟨α, hα, hγα⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N hγ
  obtain ⟨β, hβ, hδβ⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N hδ
  rw [hγα t ht, hδβ t ht, hunique x α β hα hβ]

omit hG in
private theorem ncard_newly_le [Finite ι] (hm : ∀ v, (N.readAt v).ncard ≤ 1)
    {t : ℕ} (ht : t < Nat.card D.StepNode) :
    ((D.branchingProgram N).newly t).ncard ≤ 1 := by
  have hsub : (D.branchingProgram N).newly t ⊆
      N.readIn (D.nodeVerts (D.stepLayout.symm ⟨t, ht⟩)) := by
    rintro i ⟨hi₁, hi₂⟩
    dsimp only [branchingProgram] at hi₁ hi₂
    rw [ite_eq_left (Nat.succ_le_of_lt ht)] at hi₁
    rw [ite_eq_left ht.le] at hi₂
    obtain ⟨v, hv, hsite⟩ := hi₁
    rw [(D.pastVerts_succ_sdiff ht).2.1] at hv
    rcases hv with hv_node | hv_old
    · exact ⟨v, hv_node, hsite⟩
    · exact (hi₂ ⟨v, hv_old, hsite⟩).elim
  refine (ncard_le_ncard hsub).trans ?_
  rcases D.stepLayout.symm ⟨t, ht⟩ with u | e
  · have hread_eq : N.readIn {u.val} = N.readAt u.val := by
      ext i; simp [Network.readIn, Network.readAt]
    dsimp only [nodeVerts]
    rw [hread_eq]
    exact hm u.val
  · have hem : N.readIn (D.pairVerts e) = ∅ := by
      ext i
      simp only [Network.readIn, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨v, hv, hsite⟩
      have hem_v := (hclean_N v (D.isCleanVertex_of_mem_pairVerts e hv)).2
      have hi_mem : i ∈ N.readAt v := hsite
      rw [hem_v] at hi_mem
      exact hi_mem
    dsimp only [nodeVerts]
    rw [hem, ncard_empty]
    exact Nat.zero_le 1

omit hG in
private theorem exists_ncard_revealed_eq [Finite ι] (hm : ∀ v, (N.readAt v).ncard ≤ 1)
    {k : ℕ} (hk : k ≤ N.read.ncard) :
    ∃ t ≤ Nat.card D.StepNode, ((D.branchingProgram N).revealed t).ncard = k := by
  have hlast : ((D.branchingProgram N).revealed (Nat.card D.StepNode)).ncard = N.read.ncard := by
    dsimp only [branchingProgram]
    rw [ite_eq_left le_rfl, D.pastVerts_of_card_le le_rfl]
    rfl
  refine Nat.exists_eq_of_forall_le_add_one
    (a := fun t => ((D.branchingProgram N).revealed t).ncard)
    (by rw [(D.branchingProgram N).revealed_zero, ncard_empty]; exact Nat.zero_le k)
    (by rw [hlast]; exact hk) fun t ht => ?_
  have hun : (D.branchingProgram N).revealed (t + 1) =
      (D.branchingProgram N).revealed t ∪ (D.branchingProgram N).newly t := by
    ext i
    simp only [ReadOnceNBP.newly, mem_union, mem_sdiff]
    have hmono := @(D.branchingProgram N).revealed_mono t (t + 1) (Nat.le_succ t) i
    tauto
  rw [hun]
  exact (ncard_union_le _ _).trans
    (Nat.add_le_add_left (D.ncard_newly_le N hclean_N hm ht) _)

private theorem ncard_image_path_le {t : ℕ} (ht : t ≤ Nat.card D.StepNode + 1) :
    ((fun x => (D.branchingProgram N).path x t) '' N.accepted).ncard ≤
      2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard := by
  classical
  have := Fintype.ofFinite (Edge c)
  have := Fintype.ofFinite D.eqPairs
  set F := D.singleCut t
  set A := D.actPairs t
  let φ : (F → Bool) × (A → Fin 3) →
      (Edge c → Option Bool) × (D.eqPairs → Option (Fin 3)) := fun sr =>
    (fun f => if hf : f ∈ F then some (sr.1 ⟨f, hf⟩) else none,
      fun e => if he : e ∈ A then some (sr.2 ⟨e, he⟩) else none)
  have hsub : (fun x => (D.branchingProgram N).path x t) '' N.accepted ⊆ range φ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← D.accepted_branchingProgram N hG hclean_N] at hx
    obtain ⟨α, -, hα⟩ := D.exists_satisfies_of_isAcceptingPath N hG hclean_N
      ((D.branchingProgram N).isAcceptingPath_path hx)
    refine ⟨(F.domRestrict α, A.domRestrict (D.rectIdx · α)), ?_⟩
    dsimp only [φ]
    rw [hα t ht]
    ext f <;> simp only [stateAt, domRestrict_apply] <;> split_ifs <;> rfl
  calc _ ≤ (range φ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card ((F → Bool) × (A → Fin 3)) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = 2 ^ F.ncard * 3 ^ A.ncard := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
          Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

omit hG hclean_N in
private theorem ncard_edges_last_le [Finite ι] :
    ((D.branchingProgram N).edges (Nat.card D.StepNode)).ncard ≤ 2 ^ N.readᶜ.ncard := by
  have hnewly : (D.branchingProgram N).newly (Nat.card D.StepNode) = N.readᶜ := by
    change (if Nat.card D.StepNode + 1 ≤ Nat.card D.StepNode then _ else univ) \
      (if Nat.card D.StepNode ≤ Nat.card D.StepNode then _ else univ) = _
    rw [ite_eq_right (by omega), ite_eq_left le_rfl, D.pastVerts_of_card_le le_rfl,
      compl_eq_univ_sdiff]
    rfl
  let φ : ((D.branchingProgram N).newly (Nat.card D.StepNode) → Bool) →
      ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) ×
        ((D.branchingProgram N).newly (Nat.card D.StepNode) → Bool) ×
        ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) := fun a =>
    ((fun _ => none, fun _ => none), a, (fun _ => none, fun _ => none))
  have hsub : (D.branchingProgram N).edges (Nat.card D.StepNode) ⊆ range φ := by
    rintro ⟨m, a, m'⟩ ⟨β, y, rfl, rfl, ha, -, -⟩
    refine ⟨a, ?_⟩
    subst ha
    dsimp only [φ]
    rw [D.stateAt_of_card_le le_rfl, D.stateAt_of_card_le (Nat.le_succ _)]
  calc _ ≤ (range φ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card ((D.branchingProgram N).newly (Nat.card D.StepNode) → Bool) := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = 2 ^ N.readᶜ.ncard := by
        rw [Nat.card_fun, Nat.card_coe_set_eq, hnewly,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

omit hG in
private theorem ncard_edges_step_le [Finite ι] (hdeg : (graph c).MaxDegreeLE 3)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {t : ℕ} (ht : t < Nat.card D.StepNode) :
    ((D.branchingProgram N).edges t).ncard ≤
      24576 * (2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard) := by
  classical
  have := Fintype.ofFinite (Edge c)
  have := Fintype.ofFinite D.eqPairs
  set x := D.stepLayout.symm ⟨t, ht⟩
  obtain ⟨_, hun, hdisj⟩ := D.pastVerts_succ_sdiff ht
  set E_touch : Set (Edge c) := (graph c).edgeCut (D.nodeVerts x)
  have htouch_le : E_touch.ncard ≤ 4 := by
    rcases x with u | e
    · dsimp only [E_touch, nodeVerts]
      rw [Multigraph.edgeCut_singleton _ loopless]
      exact (hdeg u.val).trans (by decide)
    · dsimp only [E_touch, nodeVerts]
      rw [D.edgeCut_pairVerts e]
      refine (ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
      refine (ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
      refine (ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
      simp
  set A_lost : Set D.eqPairs := D.actPairs t \ D.actPairs (t + 1)
  have hAlost_le : A_lost.ncard ≤ 4 := by
    have sdiff_cut {g : Edge c} (hg₀ : g ∈ (graph c).edgeCut (D.pastVerts t))
        (hg₁ : g ∉ (graph c).edgeCut (D.pastVerts (t + 1))) : g ∈ E_touch := by
      rw [hun] at hg₁
      simp only [Multigraph.mem_edgeCut, mem_union, not_not] at hg₀ hg₁
      simp only [E_touch, Multigraph.mem_edgeCut]
      lrat_tauto [(disjoint_left.mp hdisj) (a := (graph c).src g),
        (disjoint_left.mp hdisj) (a := (graph c).tgt g)]
    have hwit : ∀ e ∈ A_lost, ∃ g ∈ E_touch,
        g ∈ ({(D.pinB e).val, (D.pinD e).val} : Set (Edge c)) := by
      rintro e ⟨he_t, he_not⟩
      have hinr_1 : .inr e ∈ D.stepLayout.initial (t + 1) :=
        lt_of_lt_of_le he_t.1 (Nat.le_succ t)
      by_cases hB₁ : (D.pinB e).val ∈ (graph c).edgeCut (D.pastVerts (t + 1))
      · have hD₁ : (D.pinD e).val ∉ (graph c).edgeCut (D.pastVerts (t + 1)) :=
          fun h => he_not ⟨hinr_1, hB₁, h⟩
        exact ⟨(D.pinD e).val, sdiff_cut he_t.2.2 hD₁, Or.inr rfl⟩
      · exact ⟨(D.pinB e).val, sdiff_cut he_t.2.1 hB₁, Or.inl rfl⟩
    choose g_of hg_mem hg_pin using fun e : A_lost => hwit e.val e.property
    have hinj : Function.Injective fun e : A_lost => (⟨g_of e, hg_mem e⟩ : E_touch) := by
      intro e₁ e₂ heq
      have hg_eq : g_of e₁ = g_of e₂ := congrArg Subtype.val heq
      by_contra hne
      have hne_val : e₁.val ≠ e₂.val := fun h => hne (Subtype.ext h)
      exact disjoint_left.mp (D.pairwiseDisjoint_actPairs t e₁.property.1 e₂.property.1 hne_val)
        (hg_pin e₁) (hg_eq.symm ▸ hg_pin e₂)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h1
    exact h1.trans htouch_le
  set E_unmask : Set (Edge c) := ⋃ e ∈ A_lost, ({(D.pinB e).val, (D.pinD e).val} : Set (Edge c))
  have hEunmask_le : E_unmask.ncard ≤ 8 := by
    let Lfin : Finset D.eqPairs := A_lost.toFinset
    have hU_eq : E_unmask =
        ((Lfin.biUnion fun e => {(D.pinB e).val, (D.pinD e).val}) : Set (Edge c)) := by
      ext g; simp [E_unmask, Lfin]
    rw [hU_eq, ncard_coe_finset]
    calc (Lfin.biUnion fun e => {(D.pinB e).val, (D.pinD e).val}).card
        ≤ ∑ e ∈ Lfin, ({(D.pinB e).val, (D.pinD e).val} : Finset (Edge c)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ Lfin, 2 := Finset.sum_le_sum fun _ _ => Finset.card_insert_le _ _
      _ = 2 * A_lost.ncard := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm, ← ncard_eq_toFinset_card']
      _ ≤ 8 := by omega
  set E_extra : Set (Edge c) := E_touch ∪ E_unmask
  have hEextra_le : E_extra.ncard ≤ 12 := (ncard_union_le _ _).trans (by omega)
  set A_gain : Set D.eqPairs := D.actPairs (t + 1) \ D.actPairs t
  have hAgain_le : A_gain.ncard ≤ 1 := by
    have hsub_x : A_gain ⊆ {e | (.inr e : D.StepNode) = x} := by
      rintro e ⟨he_1, he_not⟩
      have hinr := he_1.1
      rw [D.stepLayout.initial_succ ht, mem_insert_iff] at hinr
      exact hinr.resolve_right fun hinr_t =>
        he_not (D.mem_actPairs_of_le (Nat.le_succ t) he_1 hinr_t)
    exact (ncard_le_ncard hsub_x).trans (ncard_le_one_iff_subsingleton.mpr
      fun _ ha _ hb => Sum.inr_injective (Eq.trans ha (Eq.symm hb)))
  -- Every `f ∈ singleCut (t + 1) \ E_extra` lies in `singleCut t`.
  have hpersist_single {f : Edge c} (hf₁ : f ∈ D.singleCut (t + 1)) (hnot_ex : f ∉ E_extra) :
      f ∈ D.singleCut t := by
    have hf_not_touch : f ∉ E_touch := fun h => hnot_ex (Or.inl h)
    have hf_not_unmask : f ∉ E_unmask := fun h => hnot_ex (Or.inr h)
    have hf_cut_t : f ∈ (graph c).edgeCut (D.pastVerts t) := by
      have hf_cut_1 := hf₁.1
      rw [hun] at hf_cut_1
      simp only [Multigraph.mem_edgeCut, mem_union] at hf_cut_1
      simp only [E_touch, Multigraph.mem_edgeCut, not_not] at hf_not_touch
      simp only [Multigraph.mem_edgeCut]
      tauto
    refine ⟨hf_cut_t, ?_⟩
    rintro ⟨_, ⟨e', rfl⟩, _, ⟨he'_t, rfl⟩, hmem⟩
    by_cases he'_1 : e' ∈ D.actPairs (t + 1)
    · exact hf₁.2 (mem_biUnion he'_1 hmem)
    · exact hf_not_unmask (mem_biUnion ⟨he'_t, he'_1⟩ hmem)
  set F := D.singleCut t
  set A := D.actPairs t
  set Nw := (D.branchingProgram N).newly t
  let Dom := ((F → Bool) × (A → Fin 3)) × (E_extra → Bool) × (Nw → Bool) × (A_gain → Fin 3)
  let ψ : Dom → ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) ×
      (Nw → Bool) × ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) :=
    fun ⟨⟨fs, ar⟩, ex, nw, gn⟩ =>
      ((fun f => if hf : f ∈ F then some (fs ⟨f, hf⟩) else none,
          fun e => if he : e ∈ A then some (ar ⟨e, he⟩) else none),
        nw,
        (fun f =>
            if hf₁ : f ∈ D.singleCut (t + 1) then
              if hex : f ∈ E_extra then some (ex ⟨f, hex⟩)
              else some (fs ⟨f, hpersist_single hf₁ hex⟩)
            else none,
          fun e =>
            if he₁ : e ∈ D.actPairs (t + 1) then
              if he₀ : e ∈ A then some (ar ⟨e, he₀⟩)
              else some (gn ⟨e, ⟨he₁, he₀⟩⟩)
            else none))
  have hsub : (D.branchingProgram N).edges t ⊆ range ψ := by
    rintro ⟨m, a, m'⟩ ⟨β, y, rfl, rfl, ha, -, -⟩
    refine ⟨((F.domRestrict β, A.domRestrict (D.rectIdx · β)),
      E_extra.domRestrict β, a, A_gain.domRestrict (D.rectIdx · β)), ?_⟩
    subst ha
    dsimp only [ψ]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;>
      ext f <;> simp only [stateAt, domRestrict_apply] <;> split_ifs <;> rfl
  have hNw_le : Nw.ncard ≤ 1 := D.ncard_newly_le N hclean_N hm ht
  calc ((D.branchingProgram N).edges t).ncard
      ≤ (range ψ).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ Nat.card Dom := by
        rw [← image_univ]
        exact (ncard_image_le (toFinite _)).trans (ncard_univ _).le
    _ = (2 ^ F.ncard * 3 ^ A.ncard) * (2 ^ E_extra.ncard * (2 ^ Nw.ncard * 3 ^ A_gain.ncard)) := by
        dsimp only [Dom]
        simp only [Nat.card_prod, Nat.card_fun, Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
          Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    _ ≤ (2 ^ F.ncard * 3 ^ A.ncard) * (2 ^ 12 * (2 ^ 1 * 3 ^ 1)) := by
        gcongr
    _ = 24576 * (2 ^ F.ncard * 3 ^ A.ncard) := by ring

omit hG in
theorem size_branchingProgram_le [Finite ι] (hdeg : (graph c).MaxDegreeLE 3)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {B_sup : ℝ}
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup) :
    ((D.branchingProgram N).size : ℝ) ≤
      24576 * (Nat.card (Vertex c) : ℝ) *
        (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) +
      (2 : ℝ) ^ N.readᶜ.ncard := by
  have hlog23_lo : (1 : ℝ) ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    norm_num
  have hlog23_hi : Real.logb 2 3 ≤ 2 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    norm_num
  set lam : ℝ := Real.logb 2 3 - 1
  have hlam0 : 0 ≤ lam := by dsimp [lam]; linarith
  have hlam1 : lam ≤ 1 := by dsimp [lam]; linarith
  have h1m : 1 - lam = 2 - Real.logb 2 3 := by dsimp [lam]; ring
  have h1p : 1 + lam = Real.logb 2 3 := by dsimp [lam]; ring
  have hsup' : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (1 - lam) * ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup := by
    intro s; rw [h1m]; exact hsup s
  have hstate_rpow (t : ℕ) :
      ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
    have heff := D.effective_cut_le hlam0 hlam1 hsup' t
    rw [h1p] at heff
    have h3eq : ((3 : ℝ) ^ (D.actPairs t).ncard) =
        (2 : ℝ) ^ (Real.logb 2 3 * (D.actPairs t).ncard) := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
        Real.rpow_natCast]
    push_cast
    rw [h3eq, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) heff
  rw [ReadOnceNBP.size, show (D.branchingProgram N).length = Nat.card D.StepNode + 1 from rfl,
    Finset.sum_range_succ, Nat.cast_add, Nat.cast_sum]
  refine add_le_add ?_ ?_
  · calc ∑ t ∈ Finset.range (Nat.card D.StepNode), (((D.branchingProgram N).edges t).ncard : ℝ)
        ≤ ∑ _t ∈ Finset.range (Nat.card D.StepNode),
            24576 * (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht' := Finset.mem_range.mp ht
          have hstep : (((D.branchingProgram N).edges t).ncard : ℝ) ≤
              24576 * ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) := by
            exact_mod_cast D.ncard_edges_step_le N hclean_N hdeg hm ht'
          exact hstep.trans (mul_le_mul_of_nonneg_left (hstate_rpow t) (by norm_num))
      _ = (Nat.card D.StepNode : ℝ) *
            (24576 * (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c)))) := by
          simp
      _ ≤ 24576 * (Nat.card (Vertex c) : ℝ) *
            (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
          have hcard : (Nat.card D.StepNode : ℝ) ≤ Nat.card (Vertex c) := by
            exact_mod_cast D.card_stepNode_le
          have hrpos : 0 ≤ (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by positivity
          nlinarith
  · exact_mod_cast D.ncard_edges_last_le N

omit hG in
/-- Exponential bound on `(K - 1)² · (D.branchingProgram N).size` from an effective-cut bound. -/
theorem mul_size_branchingProgram_le_rpow [Finite ι]
    (hV_pos : 1 ≤ Nat.card (Vertex c)) (hdeg : (graph c).MaxDegreeLE 3)
    (hm : ∀ v, (N.readAt v).ncard ≤ 1) {K : ℕ} (hK : 1 ≤ K)
    (hu : 2 ^ N.readᶜ.ncard ≤ K) {B_sup : ℝ}
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup) :
    (((K - 1) ^ 2 * (D.branchingProgram N).size : ℕ) : ℝ) ≤
      (2 : ℝ) ^
        (max 0 B_sup + 15 + 3 * Real.logb 2 K + 7 * Real.logb 2 (Nat.card (Vertex c))) := by
  set V := Nat.card (Vertex c)
  set B' := max 0 B_sup
  have hsup' : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B' :=
    fun s => (hsup s).trans (le_max_right 0 B_sup)
  have hsize := D.size_branchingProgram_le N hclean_N hdeg hm hsup'
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV_pos
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have huR : (2 : ℝ) ^ N.readᶜ.ncard ≤ K := by exact_mod_cast hu
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) :=
    Real.one_le_rpow (by norm_num) (add_nonneg (le_max_left 0 B_sup) (by positivity))
  have hsize' : ((D.branchingProgram N).size : ℝ) ≤
      24577 * K * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by
    have hVK : (1 : ℝ) ≤ V * K := by nlinarith
    have hpow0 : 0 ≤ (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hVK hpow0,
      mul_le_mul_of_nonneg_left hK1 (by positivity : 0 ≤ 24576 * (V : ℝ) *
        (2 : ℝ) ^ (B' + 6 * Nat.log 2 V))]
  have hKsq : (((K - 1 : ℕ) ^ 2 : ℕ) : ℝ) ≤ (K : ℝ) ^ 2 := by
    have hle : (K - 1 : ℕ) ≤ K := Nat.sub_le K 1
    exact_mod_cast Nat.pow_le_pow_left hle 2
  have hprod : (((K - 1) ^ 2 * (D.branchingProgram N).size : ℕ) : ℝ) ≤
      24577 * (K : ℝ) ^ 3 * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by
    rw [Nat.cast_mul]
    calc (((K - 1 : ℕ) ^ 2 : ℕ) : ℝ) * ((D.branchingProgram N).size : ℝ)
        ≤ (K : ℝ) ^ 2 * (24577 * K * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V)) := by gcongr
      _ = 24577 * (K : ℝ) ^ 3 * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by ring
  have h15 : (24577 : ℝ) ≤ (2 : ℝ) ^ (15 : ℝ) := by norm_num
  have hK_rpow : (K : ℝ) ^ 3 = (2 : ℝ) ^ (3 * Real.logb 2 K) := by
    have hKr : (K : ℝ) = (2 : ℝ) ^ Real.logb 2 K :=
      (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
    conv_lhs => rw [hKr, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num)]
    ring_nf
  have hV_rpow : (V : ℝ) = (2 : ℝ) ^ Real.logb 2 V :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
  have hnatlog : (Nat.log 2 V : ℝ) ≤ Real.logb 2 V := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  refine hprod.trans ?_
  calc 24577 * (K : ℝ) ^ 3 * V * (2 : ℝ) ^ (B' + 6 * Nat.log 2 V)
      ≤ (2 : ℝ) ^ (15 : ℝ) * (2 : ℝ) ^ (3 * Real.logb 2 K) * (2 : ℝ) ^ Real.logb 2 V *
          (2 : ℝ) ^ (B' + 6 * Nat.log 2 V) := by
        rw [hK_rpow]
        conv_lhs => rw [show 24577 * (2 : ℝ) ^ (3 * Real.logb 2 K) * (V : ℝ) =
          24577 * (2 : ℝ) ^ (3 * Real.logb 2 K) * (2 : ℝ) ^ Real.logb 2 V by rw [← hV_rpow]]
        gcongr
    _ = (2 : ℝ) ^ (15 + 3 * Real.logb 2 K + Real.logb 2 V + (B' + 6 * Nat.log 2 V)) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
          ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (B' + 15 + 3 * Real.logb 2 K + 7 * Real.logb 2 V) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end NetworkProps

/-- Bound squared correlation of `c` with `BitString.quadForm Q` via `D.branchingProgram`. -/
theorem sq_correlation_quadForm_le {n : ℕ} {c : Circuit σ n 1}
    {I : Interpretation σ Bool} (D : U2PairData c I) (Acc : Set Bool)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e B_sup : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ (Q + Qᵀ).cutRank U + e)
    (hread : n / 2 ≤ (network c I fun _ => Acc).read.ncard)
    (hsup : ∀ s : ℕ,
      let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s)
      ((D.Q.quotient.edgeCut P).ncard : ℝ) -
          (2 - Real.logb 2 3) *
            ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤ B_sup) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 ≤
      (2 : ℝ) ^ (B_sup - (n : ℝ) / 2 + 6 * Nat.log 2 (Nat.card (Vertex c)) + e + 3 / 2) := by
  classical
  set T := {x : Fin n → Bool | c.eval I x 0 ∈ Acc}
  set N₁ := network c I fun _ => Acc
  set N₀ := network c I fun _ => Accᶜ
  have hclean₁ : ∀ v, IsCleanVertex v →
      (∀ x α, N₁.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
        N₁.readAt v = ∅ :=
    fun v hv => ⟨constraint_iff_of_isCleanVertex I _ hv, readAt_eq_empty_of_isCleanVertex I _ hv⟩
  have hclean₀ : ∀ v, IsCleanVertex v →
      (∀ x α, N₀.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
        N₀.readAt v = ∅ :=
    fun v hv => ⟨constraint_iff_of_isCleanVertex I _ hv, readAt_eq_empty_of_isCleanVertex I _ hv⟩
  set P₁ := D.branchingProgram N₁
  set P₀ := D.branchingProgram N₀
  have hT₁ : P₁.accepted = T := by
    rw [D.accepted_branchingProgram N₁ rfl hclean₁, accepted_network_eq_eval]
  have hT₀ : P₀.accepted = Tᶜ := by
    rw [D.accepted_branchingProgram N₀ rfl hclean₀, accepted_network_eq_eval]; rfl
  obtain ⟨t, ht, hX⟩ :=
    D.exists_ncard_revealed_eq N₁ hclean₁ (ncard_readAt_le I _) hread
  have hrev_eq : P₀.revealed t = P₁.revealed t := rfl
  have htP₁ : t ≤ P₁.length := Nat.le_succ_of_le ht
  have htP₀ : t ≤ P₀.length := Nat.le_succ_of_le ht
  let msg : (Fin n → Bool) →
      Bool × ((Edge c → Option Bool) × (D.eqPairs → Option (Fin 3))) := fun x =>
    if x ∈ T then (true, P₁.path x t) else (false, P₀.path x t)
  have hclass₁ {x : Fin n → Bool} (hx : x ∈ T) : {y | msg y = msg x} = P₁.sweep.peers t x := by
    ext y
    rw [mem_ofPred_eq, ReadOnceNBP.mem_peers_sweep, hT₁]
    by_cases hy : y ∈ T <;> simp [msg, hx, hy]
  have hclass₀ {x : Fin n → Bool} (hx : x ∉ T) : {y | msg y = msg x} = P₀.sweep.peers t x := by
    ext y
    rw [mem_ofPred_eq, ReadOnceNBP.mem_peers_sweep, hT₀]
    by_cases hy : y ∈ T <;> simp [msg, hx, hy]
  have H := sq_correlation_quadForm_mul_le Q T msg (P₁.revealed t)
    (fun x y h => by by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp_all [msg]) fun x => ?_
  · have hrange : range msg ⊆ Prod.mk true '' ((fun x => P₁.path x t) '' N₁.accepted) ∪
        Prod.mk false '' ((fun x => P₀.path x t) '' N₀.accepted) := by
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ T
      · refine Or.inl ⟨_, ⟨x, ?_, rfl⟩, by simp [msg, hx]⟩
        rwa [accepted_network_eq_eval]
      · refine Or.inr ⟨_, ⟨x, ?_, rfl⟩, by simp [msg, hx]⟩
        rw [accepted_network_eq_eval]; exact hx
    have h₁ := D.ncard_image_path_le N₁ rfl hclean₁ htP₁
    have h₀ := D.ncard_image_path_le N₀ rfl hclean₀ htP₀
    have hcount : (range msg).ncard ≤
        2 * (2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard) :=
      calc (range msg).ncard
          ≤ (Prod.mk true '' ((fun x => P₁.path x t) '' N₁.accepted)).ncard +
              (Prod.mk false '' ((fun x => P₀.path x t) '' N₀.accepted)).ncard :=
            (ncard_le_ncard hrange (toFinite _)).trans (ncard_union_le _ _)
        _ ≤ ((fun x => P₁.path x t) '' N₁.accepted).ncard +
              ((fun x => P₀.path x t) '' N₀.accepted).ncard :=
            Nat.add_le_add (ncard_image_le (toFinite _)) (ncard_image_le (toFinite _))
        _ ≤ 2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard +
              2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard :=
            Nat.add_le_add h₁ h₀
        _ = 2 * (2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard) := (two_mul _).symm
    have hlog23_lo : (1 : ℝ) ≤ Real.logb 2 3 := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
    have hlog23_hi : Real.logb 2 3 ≤ 2 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
    set lam : ℝ := Real.logb 2 3 - 1
    have heff := D.effective_cut_le (lam := lam) (by dsimp [lam]; linarith)
      (by dsimp [lam]; linarith) (fun s => by
        change _ - (1 - lam) * _ ≤ B_sup
        rw [show 1 - lam = 2 - Real.logb 2 3 by dsimp [lam]; ring]
        exact hsup s) t
    rw [show 1 + lam = Real.logb 2 3 by dsimp [lam]; ring] at heff
    have hstate_rpow :
        ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
      have h3eq : ((3 : ℝ) ^ (D.actPairs t).ncard) =
          (2 : ℝ) ^ (Real.logb 2 3 * (D.actPairs t).ncard) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
          Real.rpow_natCast]
      push_cast
      rw [h3eq, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) heff
    have hmul_le : correlation {x | BitString.quadForm Q x} T ^ 2 *
        2 ^ (Q + Qᵀ).cutRank (P₁.revealed t) ≤
          (2 : ℝ) ^ (1 + B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
      calc correlation {x | BitString.quadForm Q x} T ^ 2 *
            2 ^ (Q + Qᵀ).cutRank (P₁.revealed t)
          ≤ ((range msg).ncard : ℝ) := H
        _ ≤ 2 * ((2 ^ (D.singleCut t).ncard * 3 ^ (D.actPairs t).ncard : ℕ) : ℝ) := by
            exact_mod_cast hcount
        _ ≤ 2 * (2 : ℝ) ^ (B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by gcongr
        _ = (2 : ℝ) ^ (1 + B_sup + 6 * Nat.log 2 (Nat.card (Vertex c))) := by
            symm
            rw [add_assoc 1 B_sup _, Real.rpow_add (by norm_num), Real.rpow_one]
    have hpos : (0 : ℝ) < 2 ^ (Q + Qᵀ).cutRank (P₁.revealed t) := by positivity
    have hdiv : correlation {x | BitString.quadForm Q x} T ^ 2 ≤
        (2 : ℝ) ^ (1 + B_sup + 6 * Nat.log 2 (Nat.card (Vertex c)) -
          (Q + Qᵀ).cutRank (P₁.revealed t)) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
      exact (le_div_iff₀ hpos).mpr hmul_le
    have hcut_rk := hQ (P₁.revealed t) hX
    have hhalf : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
      linarith
    exact hdiv.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith only [hcut_rk, hhalf]))
  · have hex_rect {Y X : Set (Fin n)} (h : Y = X) (A : Set (Y → Bool))
        (B : Set (↥Yᶜ → Bool)) : ∃ A' B', rectangle Y A B = rectangle X A' B' :=
      h ▸ ⟨A, B, rfl⟩
    by_cases hx : x ∈ T
    · rw [hclass₁ hx, (D.unambiguous_branchingProgram N₁ rfl hclean₁
        fun _ _ _ => satisfies_unique).peers_eq_rectangle htP₁ x]
      exact ⟨_, _, rfl⟩
    · rw [hclass₀ hx, (D.unambiguous_branchingProgram N₀ rfl hclean₀
        fun _ _ _ => satisfies_unique).peers_eq_rectangle htP₀ x]
      exact hex_rect hrev_eq _ _

end U2PairData

end U2BranchingProgram

end Cslib.Circuits.Frontier.Compiler
