/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DeMorgan
public import CslibFrontier.Computability.Circuit.Frontier.Basis.PairAtlas
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Tactic.Linarith
import CslibFrontier.Tactic.LRATTauto

/-!
# `U₂` circuit interpretations and clean-block saturated compressions

Defines `Cslib.Circuits.Interpretation.IsU2` (fan-in at most two without `XOR`/`XNOR`, covering both
`Boolean.DeMorgan` and `Boolean`) and constructs a budget-`3` saturated edge-contraction compression
`exists_u2_saturated` of `Compiler.graph c` that tracks clean `3`-pin blocks (`CleanBlock3`,
realizing polarized `COPY` junctions or `AND`-type gates) alongside exact read-input and dirty-block
deficiency bounds.

## Main definitions

* `Cslib.Circuits.Interpretation.IsU2`: Boolean interpretations of arity `≤ 2` whose binary gates
  are polarized `AND`-type.
* `Cslib.Circuits.Frontier.Compiler.IsCleanVertex`,
  `Cslib.Circuits.Frontier.Compiler.GateSatisfies`,
  `Cslib.Circuits.Frontier.Compiler.CleanBlock3`: input/output-free vertices, local gate
  satisfaction, and clean `3`-pin blocks realizing `U2OutRel` / `U2InRel`.

## Main results

* `Cslib.Circuits.Boolean.DeMorgan.isU2`, `Cslib.Circuits.Boolean.isU2`: `IsU2` instances for the
  De Morgan and Boolean bases.
* `Cslib.Circuits.Frontier.Compiler.exists_u2_saturated`: saturated budget-`3` compression with
  `CleanBlock3` outside `dirty` and exact `|Q.blocks| + 2 R ≤ 2 s` and
  `|Q.blocks| + 2 |dirty| ≤ 2 s + 2` counts.
-/

public section

namespace Cslib.Circuits

/-! ### `U₂` interpretations and standard bases -/

/-- A Boolean circuit interpretation belongs to **`U₂`** (fan-in at most two without `XOR`/`XNOR`)
when every operation has arity at most `2` and every binary operation is an `AND`-type gate up to
input/output polarities (`AND`, `OR`, `NAND`, `NOR`, `IMP`, `NIMP`, etc.). Constants (arity `0`)
and arbitrary unary gates (arity `1`: `id`, `NOT`, or constants) are permitted. -/
structure Interpretation.IsU2 {σ : Signature} (I : Interpretation σ Bool) : Prop where
  /-- Every operation has fan-in at most `2`. -/
  arity_le_two : ∀ op : σ.Op, σ.Arity op ≤ 2
  /-- Every binary operation is an `AND`-type gate `((x₀ ^^ nx) && (x₁ ^^ ny)) ^^ nz`. -/
  binary_andType : ∀ (op : σ.Op) (h : σ.Arity op = 2), ∃ nx ny nz : Bool,
    ∀ x : Fin 2 → Bool, I op (x ∘ Fin.cast h) = (((x 0 ^^ nx) && (x 1 ^^ ny)) ^^ nz)

theorem Interpretation.IsU2.fanInAtMost_two {σ : Signature} {I : Interpretation σ Bool}
    (hI : I.IsU2) {n m : ℕ} (c : Circuit σ n m) : c.FanInAtMost 2 :=
  Program.fanInAtMost_iff.mpr fun _ => hI.arity_le_two _

/-- The constant-free De Morgan basis `Boolean.DeMorgan.interpretation` is a `U₂` basis. -/
theorem Boolean.DeMorgan.isU2 : Boolean.DeMorgan.interpretation.IsU2 where
  arity_le_two := Boolean.DeMorgan.arity_le_two
  binary_andType op h := by
    cases op with
    | not => cases h
    | and => exact ⟨false, false, false, fun x => by simp [Boolean.DeMorgan.interpretation]⟩
    | or =>
      refine ⟨true, true, true, fun x => ?_⟩
      simp only [Boolean.DeMorgan.interpretation, Fin.cast_refl, Function.comp_id]
      cases x 0 <;> cases x 1 <;> rfl

/-- cslib's Boolean basis `Boolean.interpretation` (De Morgan with constants) is a `U₂` basis. -/
theorem Boolean.isU2 : Boolean.interpretation.IsU2 where
  arity_le_two op := by cases op <;> simp
  binary_andType op h := by
    cases op with
    | const _ => cases h
    | not => cases h
    | and => exact ⟨false, false, false, fun x => by simp [Boolean.interpretation]⟩
    | or =>
      refine ⟨true, true, true, fun x => ?_⟩
      simp only [Boolean.interpretation, Fin.cast_refl, Function.comp_id]
      cases x 0 <;> cases x 1 <;> rfl

end Cslib.Circuits

namespace Cslib.Circuits.Frontier.Compiler

open Set Cslib.Circuits.Frontier.Basis

section CleanCompression

variable {σ : Signature} {m_in m_out : ℕ}

/-! ### Clean vertices, gate satisfaction, and block predicates -/

/-- Edges of `graph c` with both endpoints inside `S`. -/
@[expose]
def internalEdges (c : Circuit σ m_in m_out) (S : Set (Vertex c)) : Set (Edge c) :=
  {e | src e ∈ S ∧ tgt e ∈ S}

/-- Vertices that carry neither inputs nor circuit outputs: junctions and reachable gates. -/
@[expose]
def IsCleanVertex {c : Circuit σ m_in m_out} (v : Vertex c) : Prop :=
  (∀ (i : Fin m_in) (hi : Reach c (.input i)), v ≠ .signal ⟨.input i, hi⟩) ∧
    ∀ o : Fin m_out, v ≠ .output o

/-- Input- and output-independent local gate/junction satisfaction on `S`. -/
@[expose]
def GateSatisfies {c : Circuit σ m_in m_out} (I : Interpretation σ Bool) (S : Set (Vertex c))
    (α : Edge c → Bool) : Prop :=
  ∀ v ∈ S, Constraint I (fun _ => univ) v (fun _ => false) α

/-- At an input/output-free vertex, `Constraint` is independent of `Acc` and the input `x`. -/
theorem constraint_iff_of_isCleanVertex {c : Circuit σ m_in m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c} (hv : IsCleanVertex v)
    (x : Fin m_in → Bool) (α : Edge c → Bool) :
    Constraint I Acc v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α := by
  cases v with
  | signal w =>
    rcases w with ⟨i | g, hw⟩
    · exact (hv.1 i hw rfl).elim
    · rfl
  | junction _ => rfl
  | output o => exact (hv.2 o rfl).elim

/-- An input/output-free vertex reads no circuit input coordinates. -/
theorem readAt_eq_empty_of_isCleanVertex {c : Circuit σ m_in m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c}
    (hv : IsCleanVertex v) : ((network c I Acc).readAt v) = ∅ := by
  ext i
  simp only [Network.readAt, network_site, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hsite
  obtain ⟨hi, rfl⟩ := site_eq_some hsite
  exact hv.1 i hi rfl

/-- At an input/output-free vertex, `hiddenNetwork` has the same local gate constraint. -/
theorem hidden_constraint_iff_of_isCleanVertex {n k : ℕ} {c : Circuit σ (n + k) m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c}
    (hv : IsCleanVertex v) (x : Fin n → Bool) (α : Edge c → Bool) :
    (hiddenNetwork c I Acc).Constraint v x α ↔
      Constraint I (fun _ => univ) v (fun _ => false) α := by
  change (∃ y : Fin k → Bool, Constraint I Acc v _ α) ↔ _
  simp only [constraint_iff_of_isCleanVertex I Acc hv _ α, exists_const]

/-- An input/output-free vertex reads no visible coordinates in `hiddenNetwork`. -/
theorem readAt_hidden_eq_empty_of_isCleanVertex {n k : ℕ} {c : Circuit σ (n + k) m_out}
    (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) {v : Vertex c}
    (hv : IsCleanVertex v) :
    ((hiddenNetwork c I Acc).readAt v) = ∅ := by
  ext i
  simp only [hiddenNetwork, Network.readAt, Network.hide, Network.reindex, network_site,
    mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hsite
  obtain ⟨hi, rfl⟩ := site_eq_some hsite
  exact hv.1 _ hi rfl

/-- `GateSatisfies` depends only on edges touching `S`. -/
theorem gateSatisfies_congr {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S : Set (Vertex c)} {α β : Edge c → Bool}
    (h : EqOn α β ((graph c).touching S)) (hα : GateSatisfies I S α) :
    GateSatisfies I S β := by
  intro v hv
  refine (network c I fun _ => univ).constraint_congr v (fun _ => false) (fun _ => false) α β
    (fun _ _ => rfl) (fun e he => ?_) (hα v hv)
  exact h (he.imp (fun hs => by change (graph c).src e = v at hs; rw [hs]; exact hv)
    (fun ht => by change (graph c).tgt e = v at ht; rw [ht]; exact hv))

/-- A clean `2`-pin block acting as an oriented Boolean wire `α e_out = (α e_in ^^ neg)`. -/
private def CleanWire {c : Circuit σ m_in m_out} (I : Interpretation σ Bool)
    (S : Set (Vertex c)) : Prop :=
  ∃ (e_in e_out : Edge c) (neg : Bool),
    (∀ v ∈ S, IsCleanVertex v) ∧
    e_in ≠ e_out ∧
    (graph c).edgeCut S = {e_in, e_out} ∧
    tgt e_in ∈ S ∧ src e_out ∈ S ∧
    (∀ α, GateSatisfies I S α → α e_out = (α e_in ^^ neg)) ∧
    (∀ α, α e_out = (α e_in ^^ neg) →
      ∃ β, EqOn β α (internalEdges c S)ᶜ ∧ GateSatisfies I S β)

/-- A clean `3`-pin block whose every outgoing boundary edge realizes a `U2OutRel` and whose every
incoming boundary edge realizes a `U2InRel`. -/
@[expose]
def CleanBlock3 {c : Circuit σ m_in m_out} (I : Interpretation σ Bool) (S : Set (Vertex c)) :
    Prop :=
  (∀ v ∈ S, IsCleanVertex v) ∧
  ((graph c).edgeCut S).ncard = 3 ∧
  ∀ (p q e : Edge c), p ≠ q → (graph c).edgeCut S \ {e} = {p, q} → e ∈ (graph c).edgeCut S →
    (src e ∈ S → ∃ rel : Bool → Bool → Bool → Bool, U2OutRel rel ∧
      (∀ α, GateSatisfies I S α → rel (α p) (α q) (α e) = true) ∧
      (∀ α, rel (α p) (α q) (α e) = true →
        ∃ β, EqOn β α (internalEdges c S)ᶜ ∧ GateSatisfies I S β)) ∧
    (tgt e ∈ S → ∃ rel : Bool → Bool → Bool → Bool, U2InRel rel ∧
      (∀ α, GateSatisfies I S α → rel (α p) (α q) (α e) = true) ∧
      (∀ α, rel (α p) (α q) (α e) = true →
        ∃ β, EqOn β α (internalEdges c S)ᶜ ∧ GateSatisfies I S β))

/-! ### Gluing and wire-absorption merges -/

/-- Edge-cut and internal-edge decomposition across two disjoint sets sharing one cut edge. -/
theorem edgeCut_union_of_inter_singleton {V E : Type*} {G : Multigraph V E}
    {S₁ S₂ : Set V} (hd : Disjoint S₁ S₂) {f : E}
    (hint : G.edgeCut S₁ ∩ G.edgeCut S₂ = {f}) :
    G.edgeCut (S₁ ∪ S₂) = (G.edgeCut S₁ \ {f}) ∪ (G.edgeCut S₂ \ {f}) ∧
      {e | G.src e ∈ S₁ ∪ S₂ ∧ G.tgt e ∈ S₁ ∪ S₂} =
        {e | G.src e ∈ S₁ ∧ G.tgt e ∈ S₁} ∪ {e | G.src e ∈ S₂ ∧ G.tgt e ∈ S₂} ∪ {f} := by
  have hmem_f (e : E) : e = f ↔ e ∈ G.edgeCut S₁ ∧ e ∈ G.edgeCut S₂ := by
    rw [← mem_singleton_iff, ← hint, mem_inter_iff]
  have hdv (v : V) : v ∈ S₁ → v ∉ S₂ := fun hv => disjoint_left.mp hd hv
  constructor
  · ext e
    simp only [mem_union, mem_sdiff, mem_singleton_iff, hmem_f, Multigraph.mem_edgeCut]
    lrat_tauto [hdv (G.src e), hdv (G.tgt e)]
  · ext e
    simp only [mem_union, mem_singleton_iff, hmem_f, Multigraph.mem_edgeCut, mem_ofPred_eq]
    lrat_tauto [hdv (G.src e), hdv (G.tgt e)]

/-- Glue local wire-patching witnesses across two disjoint vertex sets joined by `f`. -/
theorem patch_union {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂) {f : Edge c}
    (hint : (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ = {f})
    (α α₀ : Edge c → Bool) (hα₀ : ∀ e ≠ f, α₀ e = α e)
    (h₁ : ∃ β₁, EqOn β₁ α₀ (internalEdges c S₁)ᶜ ∧ GateSatisfies I S₁ β₁)
    (h₂ : ∀ β₁, EqOn β₁ α₀ ((graph c).edgeCut S₂) →
      ∃ β₂, EqOn β₂ β₁ (internalEdges c S₂)ᶜ ∧ GateSatisfies I S₂ β₂) :
    ∃ β, EqOn β α (internalEdges c (S₁ ∪ S₂))ᶜ ∧ GateSatisfies I (S₁ ∪ S₂) β := by
  obtain ⟨β₁, hβ₁_eq, hβ₁_sat⟩ := h₁
  have hβ₁_cut₂ : EqOn β₁ α₀ ((graph c).edgeCut S₂) := by
    intro e he
    refine hβ₁_eq fun hin => ?_
    simp only [Multigraph.mem_edgeCut, graph_src, graph_tgt] at he
    exact he (iff_of_false (disjoint_left.mp hd hin.1) (disjoint_left.mp hd hin.2))
  obtain ⟨β₂, hβ₂_eq, hβ₂_sat⟩ := h₂ β₁ hβ₁_cut₂
  have hβ₂_touch₁ : EqOn β₁ β₂ ((graph c).touching S₁) := by
    intro e he
    symm
    refine hβ₂_eq fun hin => ?_
    rcases he with hs | ht
    · exact disjoint_left.mp hd hs hin.1
    · exact disjoint_left.mp hd ht hin.2
  have hint_eq := (edgeCut_union_of_inter_singleton hd hint).2
  dsimp only [graph_src, graph_tgt] at hint_eq
  refine ⟨β₂, fun e he => ?_, fun v hv => ?_⟩
  · change e ∉ {e | src e ∈ S₁ ∪ S₂ ∧ tgt e ∈ S₁ ∪ S₂} at he
    rw [hint_eq] at he
    simp only [mem_union, mem_singleton_iff, not_or] at he
    obtain ⟨⟨hn1, hn2⟩, hnf⟩ := he
    rw [hβ₂_eq hn2, hβ₁_eq hn1, hα₀ e hnf]
  · rcases hv with hv₁ | hv₂
    · exact gateSatisfies_congr hβ₂_touch₁ hβ₁_sat v hv₁
    · exact hβ₂_sat v hv₂

private theorem cleanWire_merge_wire_step {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂) {f : Edge c}
    (hint : (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ = {f})
    {a₁ b₁ a₂ b₂ : Edge c} {neg₁ neg₂ : Bool}
    (hcl₁ : ∀ v ∈ S₁, IsCleanVertex v) (hne₁ : a₁ ≠ b₁)
    (hcut₁ : (graph c).edgeCut S₁ = {a₁, b₁}) (hsrc₁ : src b₁ ∈ S₁)
    (hsd₁ : ∀ α, GateSatisfies I S₁ α → α b₁ = (α a₁ ^^ neg₁))
    (hrl₁ : ∀ α, α b₁ = (α a₁ ^^ neg₁) → ∃ β, EqOn β α (internalEdges c S₁)ᶜ ∧
      GateSatisfies I S₁ β)
    (hcl₂ : ∀ v ∈ S₂, IsCleanVertex v) (hne₂ : a₂ ≠ b₂)
    (hcut₂ : (graph c).edgeCut S₂ = {a₂, b₂}) (htgt₂ : tgt a₂ ∈ S₂)
    (hsd₂ : ∀ α, GateSatisfies I S₂ α → α b₂ = (α a₂ ^^ neg₂))
    (hrl₂ : ∀ α, α b₂ = (α a₂ ^^ neg₂) → ∃ β, EqOn β α (internalEdges c S₂)ᶜ ∧
      GateSatisfies I S₂ β)
    (hfa₁ : f = a₁) (hfb₂ : f = b₂) :
    CleanWire I (S₁ ∪ S₂) := by
  classical
  obtain ⟨hc_union, _⟩ := edgeCut_union_of_inter_singleton hd hint
  have hcl_u : ∀ v ∈ S₁ ∪ S₂, IsCleanVertex v := fun v hv => hv.elim (hcl₁ v) (hcl₂ v)
  have ha₂_ne_b₁ : a₂ ≠ b₁ := fun h => by
    have : a₂ ∈ (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ :=
      ⟨by rw [hcut₁, h]; simp, by rw [hcut₂]; simp⟩
    rw [hint, mem_singleton_iff, hfb₂] at this
    exact hne₂ this
  have hs₁ : (graph c).edgeCut S₁ \ {f} = {b₁} := by
    rw [hcut₁, hfa₁]; ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    exact ⟨fun ⟨h, hne⟩ => h.resolve_left hne, fun h => ⟨Or.inr h, h ▸ hne₁.symm⟩⟩
  have hs₂ : (graph c).edgeCut S₂ \ {f} = {a₂} := by
    rw [hcut₂, hfb₂]; ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    exact ⟨fun ⟨h, hne⟩ => h.resolve_right hne, fun h => ⟨Or.inl h, h ▸ hne₂⟩⟩
  refine ⟨a₂, b₁, neg₂ ^^ neg₁, hcl_u, ha₂_ne_b₁, ?_, Or.inr htgt₂, Or.inl hsrc₁, ?_, ?_⟩
  · rw [hc_union, hs₁, hs₂]; ext e; simp [or_comm]
  · intro α hsat
    have h1' := hsd₁ α fun v hv => hsat v (Or.inl hv)
    have h2' := hsd₂ α fun v hv => hsat v (Or.inr hv)
    rw [h1', ← hfa₁, hfb₂, h2', Bool.xor_assoc]
  · intro α hα
    let α₀ : Edge c → Bool := fun e => if e = f then (α a₂ ^^ neg₂) else α e
    refine patch_union hd hint α α₀ (fun e hne => ite_eq_right hne) ?_ ?_
    · refine hrl₁ α₀ ?_
      have hb₁_eq : α₀ b₁ = α b₁ := ite_eq_right (hfa₁ ▸ hne₁.symm)
      have ha₁_eq : α₀ a₁ = (α a₂ ^^ neg₂) := ite_eq_left hfa₁.symm
      rw [hb₁_eq, ha₁_eq, hα, Bool.xor_assoc]
    · intro β₁ hβ₁
      refine hrl₂ β₁ ?_
      have hb₂ : β₁ b₂ = (α a₂ ^^ neg₂) :=
        (hβ₁ (by rw [hcut₂]; simp)).trans (ite_eq_left hfb₂.symm)
      have ha₂ : β₁ a₂ = α a₂ :=
        (hβ₁ (by rw [hcut₂]; simp)).trans (ite_eq_right (hfb₂ ▸ hne₂))
      rw [hb₂, ha₂]

private theorem cleanWire_merge_wire {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂)
    (hw₁ : CleanWire I S₁) (hw₂ : CleanWire I S₂)
    (h1 : ((graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂).ncard = 1) :
    CleanWire I (S₁ ∪ S₂) := by
  obtain ⟨f, hint⟩ := ncard_eq_one.mp h1
  rcases hw₁ with ⟨a₁, b₁, neg₁, hcl₁, hne₁, hcut₁, htgt₁, hsrc₁, hsd₁, hrl₁⟩
  rcases hw₂ with ⟨a₂, b₂, neg₂, hcl₂, hne₂, hcut₂, htgt₂, hsrc₂, hsd₂, hrl₂⟩
  have hf₁ : f = a₁ ∨ f = b₁ := by
    have : f ∈ (graph c).edgeCut S₁ := (hint.symm ▸ mem_singleton f).1
    simpa [hcut₁] using this
  have hf₂ : f = a₂ ∨ f = b₂ := by
    have : f ∈ (graph c).edgeCut S₂ := (hint.symm ▸ mem_singleton f).2
    simpa [hcut₂] using this
  rcases hf₁ with hfa₁ | hfb₁ <;> rcases hf₂ with hfa₂ | hfb₂
  · exact (disjoint_left.mp hd (hfa₁ ▸ htgt₁) (hfa₂ ▸ htgt₂)).elim
  · exact cleanWire_merge_wire_step hd hint
      hcl₁ hne₁ hcut₁ hsrc₁ hsd₁ hrl₁ hcl₂ hne₂ hcut₂ htgt₂ hsd₂ hrl₂ hfa₁ hfb₂
  · rw [union_comm]
    exact cleanWire_merge_wire_step hd.symm (by rwa [inter_comm])
      hcl₂ hne₂ hcut₂ hsrc₂ hsd₂ hrl₂ hcl₁ hne₁ hcut₁ htgt₁ hsd₁ hrl₁ hfa₂ hfb₁
  · exact (disjoint_left.mp hd (hfb₁ ▸ hsrc₁) (hfb₂ ▸ hsrc₂)).elim

private theorem cleanWire_merge_block3 {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {S₁ S₂ : Set (Vertex c)} (hd : Disjoint S₁ S₂)
    (hw₁ : CleanWire I S₁) (hb₂ : CleanBlock3 I S₂)
    (h1 : ((graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂).ncard = 1) :
    CleanBlock3 I (S₁ ∪ S₂) := by
  classical
  have := Fintype.ofFinite (Edge c)
  obtain ⟨f, hint⟩ := ncard_eq_one.mp h1
  obtain ⟨hc_union, _⟩ := edgeCut_union_of_inter_singleton hd hint
  obtain ⟨w_in, w_out, neg, hcl₁, hne₁, hcut₁, htgt₁, hsrc₁, hsd₁, hrl₁⟩ := hw₁
  obtain ⟨hcl₂, hnc₂, hpin₂⟩ := hb₂
  have hf₁ : f = w_in ∨ f = w_out := by
    have : f ∈ (graph c).edgeCut S₁ := (hint.symm ▸ mem_singleton f).1
    simpa [hcut₁] using this
  have hf_cut₂ : f ∈ (graph c).edgeCut S₂ := (hint.symm ▸ mem_singleton f).2
  -- Identify the external surviving wire `w'` of `S₁`.
  let w' : Edge c := if f = w_in then w_out else w_in
  have hw'_ne_f : w' ≠ f := by
    dsimp only [w']
    rcases hf₁ with hfw | hfw
    · rw [ite_eq_left hfw, hfw]; exact hne₁.symm
    · rw [ite_eq_right (hfw ▸ hne₁.symm), hfw]; exact hne₁
  have hs₁ : (graph c).edgeCut S₁ \ {f} = {w'} := by
    dsimp only [w']
    rcases hf₁ with hfw | hfw
    · rw [ite_eq_left hfw, hcut₁, hfw]
      ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_left hne, fun h => ⟨Or.inr h, h ▸ hne₁.symm⟩⟩
    · rw [ite_eq_right (hfw ▸ hne₁.symm), hcut₁, hfw]
      ext e; simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨h, hne⟩ => h.resolve_right hne, fun h => ⟨Or.inl h, h ▸ hne₁⟩⟩
  have hw'_not_cut₂ : w' ∉ (graph c).edgeCut S₂ := fun hm => by
    have : w' ∈ (graph c).edgeCut S₁ ∩ (graph c).edgeCut S₂ :=
      ⟨((hs₁.symm ▸ mem_singleton w') : w' ∈ (graph c).edgeCut S₁ \ {f}).1, hm⟩
    rw [hint, mem_singleton_iff] at this
    exact hw'_ne_f this
  have hw'_not_s₂f : w' ∉ (graph c).edgeCut S₂ \ {f} := fun hm => hw'_not_cut₂ hm.1
  have hcut_u : (graph c).edgeCut (S₁ ∪ S₂) = insert w' ((graph c).edgeCut S₂ \ {f}) := by
    rw [hc_union, hs₁, singleton_union]
  have hnc_s₂ : ((graph c).edgeCut S₂ \ {f}).ncard = 2 := by
    have := ncard_sdiff_singleton_add_one hf_cut₂ (s := (graph c).edgeCut S₂)
    omega
  have hnc_u : ((graph c).edgeCut (S₁ ∪ S₂)).ncard = 3 := by
    rw [hcut_u, ncard_insert_of_notMem hw'_not_s₂f, hnc_s₂]
  -- Orientation & wire relation between `f` and `w'`.
  have horient : (src w' ∈ S₁ ∪ S₂ → src f ∈ S₂) ∧ (tgt w' ∈ S₁ ∪ S₂ → tgt f ∈ S₂) := by
    have hf_cut₂' : ¬(src f ∈ S₂ ↔ tgt f ∈ S₂) := hf_cut₂
    have hw'_cut_u' : ¬(src w' ∈ S₁ ∪ S₂ ↔ tgt w' ∈ S₁ ∪ S₂) := by
      have hm : w' ∈ (graph c).edgeCut (S₁ ∪ S₂) := by rw [hcut_u]; exact mem_insert _ _
      exact hm
    rcases hf₁ with hfw | hfw
    · have hw' : w' = w_out := ite_eq_left hfw
      refine ⟨fun _ => by_contra fun hn =>
        hf_cut₂' (iff_of_false hn (disjoint_left.mp hd (hfw ▸ htgt₁))),
        fun h => (hw'_cut_u' (iff_of_true (Or.inl (hw' ▸ hsrc₁)) h)).elim⟩
    · have hw' : w' = w_in := ite_eq_right (hfw ▸ hne₁.symm)
      refine ⟨fun h => (hw'_cut_u' (iff_of_true h (Or.inl (hw' ▸ htgt₁)))).elim,
        fun _ => by_contra fun hn =>
          hf_cut₂' (iff_of_false (disjoint_left.mp hd (hfw ▸ hsrc₁)) hn)⟩
  have hwire_sd : ∀ α, GateSatisfies I S₁ α → α f = (α w' ^^ neg) := by
    intro α hsat
    have h := hsd₁ α hsat
    dsimp only [w']
    rcases hf₁ with hfw | hfw
    · rw [ite_eq_left hfw, hfw, h]; cases α w_in <;> cases neg <;> rfl
    · rw [ite_eq_right (hfw ▸ hne₁.symm), hfw, h]
  let α₀_fn (α : Edge c → Bool) : Edge c → Bool := fun g => if g = f then (α w' ^^ neg) else α g
  have hwire_rl : ∀ α, ∃ β₁, EqOn β₁ (α₀_fn α) (internalEdges c S₁)ᶜ ∧ GateSatisfies I S₁ β₁ := by
    intro α
    refine hrl₁ (α₀_fn α) ?_
    dsimp only [α₀_fn, w']
    rcases hf₁ with hfw | hfw
    · have hne_of : w_out ≠ f := fun h => hne₁ (hfw.symm.trans h.symm)
      rw [ite_eq_right hne_of, ite_eq_left hfw.symm, ite_eq_left hfw]
      cases α w_out <;> cases neg <;> rfl
    · have hne_fi : f ≠ w_in := fun h => hne₁ (h.symm.trans hfw)
      rw [ite_eq_left hfw.symm, ite_eq_right hne_fi, ite_eq_right hne_fi.symm]
  refine ⟨fun v hv => hv.elim (hcl₁ v) (hcl₂ v), hnc_u, ?_⟩
  -- Each pin `g` of `S₁ ∪ S₂` is the pin `r g` of `S₂` (`w' ↦ f`), up to the polarity `t g`.
  let r (g : Edge c) : Edge c := if g = w' then f else g
  let t (g : Edge c) : Bool := decide (g = w') && neg
  have hpin {g : Edge c} (hg_u : g ∈ (graph c).edgeCut (S₁ ∪ S₂)) :
      r g ∈ (graph c).edgeCut S₂ ∧
        (src g ∈ S₁ ∪ S₂ → src (r g) ∈ S₂) ∧ (tgt g ∈ S₁ ∪ S₂ → tgt (r g) ∈ S₂) ∧
        (∀ α, GateSatisfies I S₁ α → α (r g) = (α g ^^ t g)) ∧
        ∀ α, α₀_fn α (r g) = (α g ^^ t g) := by
    by_cases hg_ne : g = w'
    · have hr : r g = f := ite_eq_left hg_ne
      have ht : t g = neg := by simp [t, hg_ne]
      rw [hr, ht, hg_ne]
      exact ⟨hf_cut₂, horient.1, horient.2, hwire_sd, fun α => ite_eq_left rfl⟩
    rw [hcut_u, mem_insert_iff] at hg_u
    have hg₂ : g ∈ (graph c).edgeCut S₂ \ {f} := hg_u.resolve_left hg_ne
    have hg_not_s₁ : src g ∉ S₁ ∧ tgt g ∉ S₁ := by
      have hg_not_cut₁ : g ∉ (graph c).edgeCut S₁ := fun hm => by
        have : g ∈ (graph c).edgeCut S₁ \ {f} := ⟨hm, hg₂.2⟩
        rw [hs₁, mem_singleton_iff] at this
        exact hg_ne this
      have hiff : src g ∈ S₁ ↔ tgt g ∈ S₁ := by
        simpa [Multigraph.mem_edgeCut] using hg_not_cut₁
      by_cases hs_in : src g ∈ S₁
      · have ht_in : tgt g ∈ S₁ := hiff.mp hs_in
        exact (hg₂.1 (iff_of_false (disjoint_left.mp hd hs_in) (disjoint_left.mp hd ht_in))).elim
      · exact ⟨hs_in, fun ht_in => hs_in (hiff.mpr ht_in)⟩
    have hr : r g = g := ite_eq_right hg_ne
    have ht : t g = false := by simp [t, hg_ne]
    simp only [hr, ht, Bool.xor_false]
    exact ⟨hg₂.1, fun h => h.resolve_left hg_not_s₁.1, fun h => h.resolve_left hg_not_s₁.2,
      fun _ _ => trivial, fun α => ite_eq_right hg₂.2⟩
  -- A pin relation of `S₂` on `(r p, r q, r e)` transfers to `S₁ ∪ S₂` on `(p, q, e)`.
  have transfer {p q e : Edge c} (hp : p ∈ (graph c).edgeCut (S₁ ∪ S₂))
      (hq : q ∈ (graph c).edgeCut (S₁ ∪ S₂)) (he : e ∈ (graph c).edgeCut (S₁ ∪ S₂))
      {P : (Bool → Bool → Bool → Bool) → Prop}
      (hflip : ∀ rel, P rel → P fun a b x => rel (a ^^ t p) (b ^^ t q) (x ^^ t e))
      (h : ∃ rel, P rel ∧
        (∀ α, GateSatisfies I S₂ α → rel (α (r p)) (α (r q)) (α (r e)) = true) ∧
        ∀ α, rel (α (r p)) (α (r q)) (α (r e)) = true →
          ∃ β, EqOn β α (internalEdges c S₂)ᶜ ∧ GateSatisfies I S₂ β) :
      ∃ rel, P rel ∧ (∀ α, GateSatisfies I (S₁ ∪ S₂) α → rel (α p) (α q) (α e) = true) ∧
        ∀ α, rel (α p) (α q) (α e) = true →
          ∃ β, EqOn β α (internalEdges c (S₁ ∪ S₂))ᶜ ∧ GateSatisfies I (S₁ ∪ S₂) β := by
    obtain ⟨rel₀, hP, hsd₀, hrl₀⟩ := h
    obtain ⟨hp₂, -, -, hp_sd, hp_rl⟩ := hpin hp
    obtain ⟨hq₂, -, -, hq_sd, hq_rl⟩ := hpin hq
    obtain ⟨he₂, -, -, he_sd, he_rl⟩ := hpin he
    refine ⟨fun a b x => rel₀ (a ^^ t p) (b ^^ t q) (x ^^ t e), hflip rel₀ hP,
      fun α hsat => ?_, fun α hrel => ?_⟩
    · have h₁ : GateSatisfies I S₁ α := fun v hv => hsat v (Or.inl hv)
      dsimp only
      rw [← hp_sd α h₁, ← hq_sd α h₁, ← he_sd α h₁]
      exact hsd₀ α fun v hv => hsat v (Or.inr hv)
    · refine patch_union hd hint α (α₀_fn α) (fun g hne => ite_eq_right hne) (hwire_rl α)
        fun β₁ hβ₁ => hrl₀ β₁ ?_
      rwa [hβ₁ hp₂, hβ₁ hq₂, hβ₁ he₂, hp_rl, hq_rl, he_rl]
  intro p q e hpq hrem he_u
  have hmem_u (g : Edge c) :
      g ∈ (graph c).edgeCut (S₁ ∪ S₂) ↔ g = w' ∨ g ∈ (graph c).edgeCut S₂ ∧ g ≠ f := by
    rw [hcut_u]; rfl
  have hmem_rem (g : Edge c) : g ∈ (graph c).edgeCut (S₁ ∪ S₂) ∧ g ≠ e ↔ g = p ∨ g = q :=
    Set.ext_iff.mp hrem g
  have hp_u := ((hmem_rem p).mpr (Or.inl rfl)).1
  have hq_u := ((hmem_rem q).mpr (Or.inr rfl)).1
  have hrem₂ : (graph c).edgeCut S₂ \ {r e} = {r p, r q} := by
    ext g
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, r]
    clear * - hmem_u hmem_rem hw'_not_cut₂ hw'_ne_f hf_cut₂ he_u hpq
    grind [hmem_u g, hmem_u p, hmem_u q, hmem_u e, hmem_rem g, hmem_rem p, hmem_rem q]
  have hpq₂ : r p ≠ r q := by
    simp only [r]
    clear * - hmem_u hmem_rem hpq hw'_not_cut₂ hw'_ne_f hf_cut₂ hp_u hq_u
    grind [hmem_u p, hmem_u q]
  obtain ⟨he₂, he_src, he_tgt, -, -⟩ := hpin he_u
  obtain ⟨h₂_out, h₂_in⟩ := hpin₂ (r p) (r q) (r e) hpq₂ hrem₂ he₂
  exact ⟨fun hs => transfer hp_u hq_u he_u (fun _ h => h.flip _ _ _) (h₂_out (he_src hs)),
    fun ht => transfer hp_u hq_u he_u (fun _ h => h.flip _ _ _) (h₂_in (he_tgt ht))⟩

/-! ### Singleton block classification -/

private theorem internalEdges_singleton_empty (c : Circuit σ m_in m_out) (v : Vertex c) :
    internalEdges c {v} = ∅ := by
  ext e
  simp only [internalEdges, mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
  rintro ⟨hs, ht⟩
  exact loopless e (hs.trans ht.symm)

/-- Every edge leaving the junction `⟨w, idx⟩` is its delivery edge or the next junction's feed. -/
private theorem eq_of_src_eq_junction {c : Circuit σ m_in m_out} {w : Signal c} {idx : ℕ}
    {hidx : idx < fanout c w} {e : Edge c} (hs : src e = .junction ⟨w, ⟨idx, hidx⟩⟩) :
    e = .deliver ⟨w, ⟨idx, hidx⟩⟩ ∨ ∃ h : idx + 1 < fanout c w, e = .feed ⟨w, ⟨idx + 1, h⟩⟩ := by
  rcases e with ⟨w', ⟨_ | k, hk⟩⟩ | j'
  · cases hs
  · obtain ⟨rfl, hfin⟩ := Sigma.mk.inj_iff.mp (Vertex.junction.inj hs)
    obtain rfl : k = idx := Fin.mk.inj_iff.mp (eq_of_heq hfin)
    exact Or.inr ⟨hk, rfl⟩
  · cases hs; exact Or.inl rfl

/-- The only edge entering a junction is its feed. -/
private theorem eq_feed_of_tgt_eq_junction {c : Circuit σ m_in m_out} {j : Junction c}
    {e : Edge c} (ht : tgt e = .junction j) : e = .feed j := by
  rcases e with j' | j'
  · cases ht; rfl
  · change owner (junctionEquiv c j') = _ at ht
    generalize junctionEquiv c j' = t at ht
    rcases t with a | o <;> cases ht

private theorem clean_junction_singleton {c : Circuit σ m_in m_out} (I : Interpretation σ Bool)
    (j : Junction c) :
    CleanWire I {.junction j} ∨ CleanBlock3 I {.junction j} := by
  rcases j with ⟨w, ⟨idx, hidx⟩⟩
  set j : Junction c := ⟨w, ⟨idx, hidx⟩⟩
  have hcl : ∀ v ∈ ({Vertex.junction j} : Set (Vertex c)), IsCleanVertex v := by
    intro v hv; rw [mem_singleton_iff] at hv; subst hv
    exact ⟨fun _ _ h => (nomatch h), fun _ h => (nomatch h)⟩
  have hint0 : (internalEdges c {.junction j})ᶜ = univ := by
    rw [internalEdges_singleton_empty, compl_empty]
  have hmem_cut (e : Edge c) : e ∈ (graph c).edgeCut {.junction j} ↔
      e = .feed j ∨ e = .deliver j ∨ ∃ h : idx + 1 < fanout c w, e = .feed ⟨w, ⟨idx + 1, h⟩⟩ := by
    rw [Multigraph.edgeCut_singleton _ loopless]
    simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt]
    constructor
    · rintro (hs | ht)
      · exact Or.inr (eq_of_src_eq_junction hs)
      · exact Or.inl (eq_feed_of_tgt_eq_junction ht)
    · rintro (rfl | rfl | ⟨_, rfl⟩)
      exacts [Or.inr rfl, Or.inl rfl, Or.inl rfl]
  by_cases hnext : idx + 1 < fanout c w
  · -- Non-last junction: `CleanBlock3` (`copyRel`)
    right
    set e_in : Edge c := .feed j
    set e_d : Edge c := .deliver j
    set e_f : Edge c := .feed ⟨w, ⟨idx + 1, hnext⟩⟩
    have h01 : e_in ≠ e_d := fun h => nomatch h
    have h02 : e_in ≠ e_f := fun h => by
      have := congrArg (fun x : Junction c => (x.2 : ℕ)) (Edge.feed.inj h)
      dsimp [j] at this; omega
    have h12 : e_d ≠ e_f := fun h => nomatch h
    have hcut : (graph c).edgeCut {.junction j} = {e_in, e_d, e_f} := by
      ext e
      exact (hmem_cut e).trans (or_congr_right (or_congr_right ⟨fun ⟨_, h⟩ => h, (⟨hnext, ·⟩)⟩))
    have hnc : ((graph c).edgeCut {.junction j}).ncard = 3 := by
      rw [hcut, ncard_insert_of_notMem (by simp [h01, h02]), ncard_pair h12]
    have hsat_iff (α : Edge c → Bool) :
        GateSatisfies I {.junction j} α ↔ α e_d = α e_in ∧ α e_f = α e_in := by
      simp only [GateSatisfies, mem_singleton_iff, forall_eq, Constraint]
      constructor
      · intro h; exact ⟨h e_d rfl, h e_f rfl⟩
      · rintro ⟨hd, hf⟩ e hs
        rcases eq_of_src_eq_junction hs with rfl | ⟨_, rfl⟩
        exacts [hd, hf]
    refine ⟨hcl, hnc, fun p q e hpq hrem he => ?_⟩
    have hall_eq (α : Edge c → Bool) :
        (α e_d = α e_in ∧ α e_f = α e_in) ↔ copyPolarRel false false (α p) (α q) (α e) = true := by
      have hp_rem : p ∈ (graph c).edgeCut {.junction j} \ {e} := by rw [hrem]; simp
      have hq_rem : q ∈ (graph c).edgeCut {.junction j} \ {e} := by rw [hrem]; simp
      have hp_mem : p ∈ ({e_in, e_d, e_f} : Set (Edge c)) := hcut ▸ hp_rem.1
      have hq_mem : q ∈ ({e_in, e_d, e_f} : Set (Edge c)) := hcut ▸ hq_rem.1
      have he_mem : e ∈ ({e_in, e_d, e_f} : Set (Edge c)) := by rwa [← hcut]
      have hp_ne_e : p ≠ e := hp_rem.2
      have hq_ne_e : q ≠ e := hq_rem.2
      rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl <;>
        rcases he_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim
        | exact (hp_ne_e rfl).elim
        | exact (hq_ne_e rfl).elim
        | (cases α e_in <;> cases α e_d <;> cases α e_f <;> decide)
    refine ⟨fun _ => ⟨copyPolarRel false false, .copy false false, ?_⟩,
      fun _ => ⟨copyPolarRel false false, .copy false false, ?_⟩⟩ <;>
    exact ⟨fun α h => (hall_eq α).mp ((hsat_iff α).mp h),
      fun α h => ⟨α, by rw [hint0]; exact eqOn_refl _ _, (hsat_iff α).mpr ((hall_eq α).mpr h)⟩⟩
  · -- Last junction: `CleanWire` (`neg = false`)
    left
    have hcut : (graph c).edgeCut {.junction j} = {.feed j, .deliver j} := by
      ext e
      exact (hmem_cut e).trans (or_congr_right (or_iff_left fun ⟨h, _⟩ => hnext h))
    refine ⟨.feed j, .deliver j, false, hcl, (fun h => nomatch h), hcut, rfl, rfl, ?_, ?_⟩
    · intro α hsat
      simp only [Bool.xor_false]
      exact hsat (.junction j) rfl (.deliver j) rfl
    · intro α hα
      simp only [Bool.xor_false] at hα
      refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, ?_⟩
      simp only [GateSatisfies, mem_singleton_iff, forall_eq, Constraint]
      intro e hs
      rcases eq_of_src_eq_junction hs with rfl | ⟨h, rfl⟩
      exacts [hα, absurd h hnext]

private theorem clean_unary_gate_singleton {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    {g : Fin c.size} (hg : Reach c (.gate g)) (h1 : σ.Arity (c.program.lines g).op = 1)
    (hnonconst : ¬∃ b : Bool, ∀ x, I (c.program.lines g).op x = b) :
    CleanWire I {.signal ⟨.gate g, hg⟩} := by
  set v : Vertex c := .signal ⟨.gate g, hg⟩
  set a0 : Fin (σ.Arity (c.program.lines g).op) := ⟨0, by omega⟩
  set e_in : Edge c := argEdge hg a0
  set e_out : Edge c := head ⟨.gate g, hg⟩
  let neg : Bool := I (c.program.lines g).op (fun _ => false)
  have hcl : ∀ u ∈ ({v} : Set (Vertex c)), IsCleanVertex u := by
    intro u hu; rw [mem_singleton_iff] at hu; rw [hu]
    exact ⟨fun _ _ h => (by dsimp [v] at h; cases h), fun _ h => (by dsimp [v] at h; cases h)⟩
  have hne : e_in ≠ e_out := fun h => nomatch h
  have hcut : (graph c).edgeCut {v} = {e_in, e_out} := by
    ext e
    rw [Multigraph.edgeCut_singleton _ loopless]
    simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro (hs | ht)
      · exact Or.inr (eq_head_of_src_eq_signal hs)
      · obtain ⟨⟨⟨g', a⟩, hg'⟩, hwg, rfl⟩ := exists_slot_of_tgt_eq_signal ht
        dsimp at hwg
        obtain rfl : g' = g := Wire.gate.inj hwg
        have ha : a = a0 := Fin.ext (by have := a.isLt; dsimp [a0]; omega)
        subst ha
        exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact Or.inr (tgt_deliverEdge _)
      · exact Or.inl rfl
  have hf_eq (b : Bool) : I (c.program.lines g).op (fun _ => b) = (b ^^ neg) := by
    have hdiff : I (c.program.lines g).op (fun _ => true) ≠ neg := by
      intro heq
      refine hnonconst ⟨neg, fun x => ?_⟩
      have hx : x = (fun _ => x a0) :=
        funext fun idx => congrArg x (Fin.ext (by have := idx.isLt; dsimp [a0]; omega))
      rw [hx]
      cases x a0
      · rfl
      · exact heq
    cases b
    · simp [neg]
    · dsimp only [neg] at hdiff ⊢
      cases hval : I (c.program.lines g).op (fun _ => false) <;>
        cases hval1 : I (c.program.lines g).op (fun _ => true) <;> simp_all
  have harg_eq (α : Edge c → Bool) :
      (fun a => α (argEdge hg a)) = fun _ => α e_in := by
    funext a
    have ha : a = a0 := Fin.ext (by have := a.isLt; dsimp [a0]; omega)
    rw [ha]
  have hint0 : (internalEdges c {v})ᶜ = univ := by
    rw [internalEdges_singleton_empty, compl_empty]
  refine ⟨e_in, e_out, neg, hcl, hne, hcut, tgt_deliverEdge _, rfl, ?_, ?_⟩
  · intro α hsat
    have h := hsat v rfl
    change α e_out = I (c.program.lines g).op (fun a => α (argEdge hg a)) at h
    rw [h, harg_eq, hf_eq]
  · intro α hα
    refine ⟨α, by rw [hint0]; exact eqOn_refl _ _, ?_⟩
    simp only [GateSatisfies, mem_singleton_iff, forall_eq]
    change α e_out = I (c.program.lines g).op (fun a => α (argEdge hg a))
    rw [harg_eq, hf_eq]
    exact hα

private theorem clean_binary_gate_singleton {c : Circuit σ m_in m_out} {I : Interpretation σ Bool}
    (hU2 : I.IsU2) {g : Fin c.size} (hg : Reach c (.gate g))
    (h2 : σ.Arity (c.program.lines g).op = 2) :
    CleanBlock3 I {.signal ⟨.gate g, hg⟩} := by
  obtain ⟨nx, ny, nz, hand⟩ := hU2.binary_andType (c.program.lines g).op h2
  set v : Vertex c := .signal ⟨.gate g, hg⟩
  set a0 : Fin (σ.Arity (c.program.lines g).op) := ⟨0, by omega⟩
  set a1 : Fin (σ.Arity (c.program.lines g).op) := ⟨1, by omega⟩
  set e0 : Edge c := argEdge hg a0
  set e1 : Edge c := argEdge hg a1
  set e_out : Edge c := head ⟨.gate g, hg⟩
  have hcl : ∀ u ∈ ({v} : Set (Vertex c)), IsCleanVertex u := by
    intro u hu; rw [mem_singleton_iff] at hu; rw [hu]
    exact ⟨fun _ _ h => (by dsimp [v] at h; cases h), fun _ h => (by dsimp [v] at h; cases h)⟩
  have h01 : e0 ≠ e1 := fun h => by
    have hdel := Edge.deliver.inj h
    have hcon := (junctionEquiv c).symm.injective hdel
    have hsl := Sum.inl.inj hcon
    have hfin : (a0 : ℕ) = (a1 : ℕ) := congrArg (fun s : Slot c => (s.1.2 : ℕ)) hsl
    dsimp [a0, a1] at hfin; omega
  have h02 : e0 ≠ e_out := fun h => nomatch h
  have h12 : e1 ≠ e_out := fun h => nomatch h
  have hcut : (graph c).edgeCut {v} = {e0, e1, e_out} := by
    ext e
    rw [Multigraph.edgeCut_singleton _ loopless]
    simp only [Multigraph.mem_incidenceSet, graph_src, graph_tgt, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro (hs | ht)
      · exact Or.inr (Or.inr (eq_head_of_src_eq_signal hs))
      · obtain ⟨⟨⟨g', a⟩, hg'⟩, hwg, rfl⟩ := exists_slot_of_tgt_eq_signal ht
        dsimp at hwg
        obtain rfl : g' = g := Wire.gate.inj hwg
        have hlt : (a : ℕ) < 2 := h2 ▸ a.isLt
        rcases (show (a : ℕ) = 0 ∨ (a : ℕ) = 1 by omega) with hz | ho
        · have ha : a = a0 := Fin.ext hz
          subst ha; exact Or.inl rfl
        · have ha : a = a1 := Fin.ext ho
          subst ha; exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inr (tgt_deliverEdge _)
      · exact Or.inr (tgt_deliverEdge _)
      · exact Or.inl rfl
  have hnc : ((graph c).edgeCut {v}).ncard = 3 := by
    rw [hcut, ncard_insert_of_notMem (by simp [h01, h02]), ncard_pair h12]
  have hint0 : (internalEdges c {v})ᶜ = univ := by
    rw [internalEdges_singleton_empty, compl_empty]
  have hsat_iff (α : Edge c → Bool) :
      GateSatisfies I {v} α ↔ andTypeRel nx ny nz 2 (α e0) (α e1) (α e_out) = true := by
    simp only [GateSatisfies, mem_singleton_iff, forall_eq]
    change (α e_out = I (c.program.lines g).op (fun a => α (argEdge hg a))) ↔ _
    let x2 : Fin 2 → Bool := ![α e0, α e1]
    have hx2 : (fun a => α (argEdge hg a)) = x2 ∘ Fin.cast h2 := by
      funext a
      have hlt : (a : ℕ) < 2 := h2 ▸ a.isLt
      rcases (show (a : ℕ) = 0 ∨ (a : ℕ) = 1 by omega) with hz | ho
      · have ha : a = a0 := Fin.ext hz
        subst ha; rfl
      · have ha : a = a1 := Fin.ext ho
        subst ha; rfl
    rw [hx2, hand x2]
    change (α e_out = (((α e0 ^^ nx) && (α e1 ^^ ny)) ^^ nz)) ↔
      ((((α e0 ^^ nx) && (α e1 ^^ ny)) ^^ nz) == α e_out) = true
    rw [beq_iff_eq, eq_comm]
  have mk {rel : Bool → Bool → Bool → Bool} {p' q' e' : Edge c}
      (hrel : ∀ α : Edge c → Bool,
        rel (α p') (α q') (α e') = andTypeRel nx ny nz 2 (α e0) (α e1) (α e_out)) :
      (∀ α, GateSatisfies I {v} α → rel (α p') (α q') (α e') = true) ∧
      (∀ α, rel (α p') (α q') (α e') = true →
        ∃ β, EqOn β α (internalEdges c {v})ᶜ ∧ GateSatisfies I {v} β) :=
    ⟨fun α h => by rw [hrel α]; exact (hsat_iff α).mp h,
      fun α h => ⟨α, by rw [hint0]; exact eqOn_refl _ _,
        (hsat_iff α).mpr (by rwa [← hrel α])⟩⟩
  refine ⟨hcl, hnc, fun p q e hpq hrem he => ?_⟩
  have hp_rem : p ∈ (graph c).edgeCut {v} \ {e} := by rw [hrem]; simp
  have hq_rem : q ∈ (graph c).edgeCut {v} \ {e} := by rw [hrem]; simp
  have hp_mem : p ∈ ({e0, e1, e_out} : Set (Edge c)) := hcut ▸ hp_rem.1
  have hq_mem : q ∈ ({e0, e1, e_out} : Set (Edge c)) := hcut ▸ hq_rem.1
  have he_mem : e ∈ ({e0, e1, e_out} : Set (Edge c)) := by rwa [← hcut]
  have hp_ne_e : p ≠ e := hp_rem.2
  have hq_ne_e : q ≠ e := hq_rem.2
  have ht0 : tgt e0 = v := tgt_deliverEdge (.inl ⟨⟨g, a0⟩, hg⟩)
  have ht1 : tgt e1 = v := tgt_deliverEdge (.inl ⟨⟨g, a1⟩, hg⟩)
  have hsrc_e0 : src e0 ≠ v := fun h => loopless e0 (h.trans ht0.symm)
  have hsrc_e1 : src e1 ≠ v := fun h => loopless e1 (h.trans ht1.symm)
  have htgt_out : tgt e_out ≠ v := fun h => loopless e_out h.symm
  constructor
  · intro hsrc_e
    rw [mem_singleton_iff] at hsrc_e
    rcases he_mem with rfl | rfl | rfl
    · exact (hsrc_e0 hsrc_e).elim
    · exact (hsrc_e1 hsrc_e).elim
    · rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim | exact (hp_ne_e rfl).elim | exact (hq_ne_e rfl).elim
        | exact ⟨andTypeRel nx ny nz 2, .gate nx ny nz, mk fun _ => rfl⟩
        | exact ⟨andTypeRel ny nx nz 2, .gate ny nx nz,
            mk fun α => by dsimp only [andTypeRel]; rw [Bool.and_comm]⟩
  · intro htgt_e
    rw [mem_singleton_iff] at htgt_e
    rcases he_mem with rfl | rfl | rfl
    · -- `e = e0`: remaining pins are `{e1, e_out}`
      rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim | exact (hp_ne_e rfl).elim | exact (hq_ne_e rfl).elim
        | exact ⟨fun c' d' e' => andTypeRel nx ny nz 0 d' c' e',
            (U2InRel.gate nx ny nz 0).swap, mk fun _ => rfl⟩
        | exact ⟨andTypeRel nx ny nz 0, U2InRel.gate nx ny nz 0, mk fun _ => rfl⟩
    · -- `e = e1`: remaining pins are `{e0, e_out}`
      rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim | exact (hp_ne_e rfl).elim | exact (hq_ne_e rfl).elim
        | exact ⟨andTypeRel nx ny nz 1, U2InRel.gate nx ny nz 1, mk fun _ => rfl⟩
        | exact ⟨fun c' d' e' => andTypeRel nx ny nz 1 d' c' e',
            (U2InRel.gate nx ny nz 1).swap, mk fun _ => rfl⟩
    · exact (htgt_out htgt_e).elim

/-! ### Dirty singletons and saturated compression -/

private def IsDirtySingleton (c : Circuit σ m_in m_out) (I : Interpretation σ Bool) :
    Vertex c → Prop
  | .signal ⟨.input _, _⟩ => True
  | .signal ⟨.gate g, _⟩ => σ.Arity (c.program.lines g).op = 0 ∨
      (σ.Arity (c.program.lines g).op = 1 ∧ ∃ b : Bool, ∀ x, I (c.program.lines g).op x = b)
  | .junction _ => False
  | .output _ => True

private structure U2CompressState {n k : ℕ} (c : Circuit σ (n + k) 1) (I : Interpretation σ Bool)
    (d₀ : ℕ) where
  cmp : (graph c).Compression 3
  dirty : Finset (List (Vertex c))
  dirty_sub : dirty ⊆ cmp.blocks
  clean : ∀ B ∈ cmp.blocks, B ∉ dirty → CleanWire I {v | v ∈ B} ∨ CleanBlock3 I {v | v ∈ B}
  count : dirty.card + Nat.card (Vertex c) ≤ d₀ + cmp.blocks.card +
    {e | ∃ B ∈ cmp.blocks, src e ∈ B ∧ tgt e ∈ B}.ncard

/-- **Saturated `U₂` compression.** Every circuit `c : Circuit σ (n + k) 1` over a `U₂` basis `I`
has a saturated budget-`3` compression `Q` of `Compiler.graph c` together with a dirty block set
`dirty ⊆ Q.blocks` such that, whenever `1 < Nat.card Q.blocks`:
* every block `B ∉ dirty` is a `CleanBlock3 I {v | v ∈ B}`;
* `Nat.card Q.blocks + 2 * (hiddenNetwork c I Acc).read.ncard ≤ 2 * c.innerSize`; and
* `Nat.card Q.blocks + 2 * dirty.card ≤ 2 * c.innerSize + 2`. -/
theorem exists_u2_saturated {n k : ℕ} (c : Circuit σ (n + k) 1) {I : Interpretation σ Bool}
    (hU2 : I.IsU2) (Acc : Fin 1 → Set Bool) :
    ∃ (Q : (graph c).Compression 3) (dirty : Finset (List (Vertex c))),
      Q.Saturated ∧ dirty ⊆ Q.blocks ∧
      (1 < Nat.card Q.blocks →
        (∀ B ∈ Q.blocks, B ∉ dirty → CleanBlock3 I {v | v ∈ B}) ∧
        Nat.card Q.blocks + 2 * (hiddenNetwork c I Acc).read.ncard ≤ 2 * c.innerSize ∧
        Nat.card Q.blocks + 2 * dirty.card ≤ 2 * c.innerSize + 2) := by
  classical
  have := Fintype.ofFinite (Vertex c)
  have := Fintype.ofFinite (Edge c)
  have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
  have hdeg : (graph c).MaxDegreeLE 3 := maxDegreeLE le_rfl hfan
  have har (g : Fin c.size) : σ.Arity (c.program.lines g).op = 0 ∨
      σ.Arity (c.program.lines g).op = 1 ∨ σ.Arity (c.program.lines g).op = 2 := by
    have := hU2.arity_le_two (c.program.lines g).op; omega
  let Dfin : Finset (Vertex c) := Finset.univ.filter (IsDirtySingleton c I)
  set d₀ : ℕ := Dfin.card
  -- Initial singleton state.
  let initCmp : (graph c).Compression 3 := Multigraph.Compression.singletons hdeg
  let initDirty : Finset (List (Vertex c)) := Dfin.image fun v => [v]
  have hinit : U2CompressState c I d₀ :=
    { cmp := initCmp
      dirty := initDirty
      dirty_sub := Finset.image_subset_image (Finset.filter_subset _ _)
      clean := by
        intro B hB hnot
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hB
        have hnotD : ¬IsDirtySingleton c I v := fun hd =>
          hnot (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hd⟩))
        have hset : {u : Vertex c | u ∈ [v]} = {v} := by ext u; simp
        rw [hset]
        cases v with
        | signal w =>
          rcases w with ⟨i | g, hw⟩
          · exact (hnotD trivial).elim
          · rcases har g with h0 | h1 | h2
            · exact (hnotD (Or.inl h0)).elim
            · have hnc : ¬∃ b : Bool, ∀ x, I (c.program.lines g).op x = b :=
                fun hc => hnotD (Or.inr ⟨h1, hc⟩)
              exact Or.inl (clean_unary_gate_singleton hw h1 hnc)
            · exact Or.inr (clean_binary_gate_singleton hU2 hw h2)
        | junction j => exact clean_junction_singleton I j
        | output o => exact (hnotD trivial).elim
      count := by
        have hc1 : initDirty.card = d₀ :=
          Finset.card_image_of_injective _ List.singleton_injective
        have hc2 : initCmp.blocks.card = Nat.card (Vertex c) := by
          dsimp only [initCmp, Multigraph.Compression.singletons]
          rw [Finset.card_image_of_injective _ List.singleton_injective, Finset.card_univ,
            Nat.card_eq_fintype_card]
        rw [hc1, hc2]
        exact Nat.le_add_right _ _ }
  -- Take a minimal-block state.
  obtain ⟨st, -, hmin⟩ :=
    (measure fun s : U2CompressState c I d₀ => s.cmp.blocks.card).wf.has_min univ ⟨hinit, trivial⟩
  -- Prove saturation by constructing the merged `U2CompressState`.
  have hsat : st.cmp.Saturated := by
    intro B₀ hB₀ B₀' hB₀' hne₀ hjoin₀
    by_contra! hcut₀
    suffices ∃ st' : U2CompressState c I d₀, st'.cmp.blocks.card < st.cmp.blocks.card by
      obtain ⟨st', hlt⟩ := this
      exact hmin st' trivial hlt
    -- Order `(B, B')` so `B'.length ≤ B.length`.
    have hex_pair : ∃ B B' : List (Vertex c), B ∈ st.cmp.blocks ∧ B' ∈ st.cmp.blocks ∧
        B ≠ B' ∧ B'.length ≤ B.length ∧
        ((graph c).edgeCut {v | v ∈ B} ∩ (graph c).edgeCut {v | v ∈ B'}).Nonempty ∧
        ((graph c).edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ≤ 3 := by
      rcases le_total B₀'.length B₀.length with hle | hle
      · exact ⟨B₀, B₀', hB₀, hB₀', hne₀, hle, hjoin₀, hcut₀⟩
      · refine ⟨B₀', B₀, hB₀', hB₀, hne₀.symm, hle, ?_, ?_⟩
        · rwa [inter_comm]
        · rwa [union_comm]
    obtain ⟨B, B', hB, hB', hne, hlen, hjoin, hcut⟩ := hex_pair
    have hd_set : Disjoint {v : Vertex c | v ∈ B} {v : Vertex c | v ∈ B'} :=
      disjoint_left.mpr fun v hv hv' => hne (st.cmp.eq_of_mem B hB B' hB' v hv hv')
    let cmp' : (graph c).Compression 3 := st.cmp.merge hB hB' hne hlen hjoin hcut
    let blocks' := cmp'.blocks
    have hmem {C : List (Vertex c)} : C ∈ blocks' ↔
        C = B ++ B' ∨ (C ≠ B' ∧ C ≠ B ∧ C ∈ st.cmp.blocks) := by
      simp only [blocks', cmp', Multigraph.Compression.blocks_merge, Finset.mem_insert,
        Finset.mem_erase]
    have hnot_app : B ++ B' ∉ st.cmp.blocks := st.cmp.notMem_blocks_append hB hB'
    have hcard : blocks'.card + 1 = st.cmp.blocks.card :=
      st.cmp.card_insert_append_erase_add_one hB hB' hne
    have happ (L L' : List (Vertex c)) : {v | v ∈ L ++ L'} = {v | v ∈ L} ∪ {v | v ∈ L'} :=
      Set.ext fun _ => List.mem_append
    set E_old : Set (Edge c) := {e | ∃ D ∈ st.cmp.blocks, src e ∈ D ∧ tgt e ∈ D}
    set E_join : Set (Edge c) := (graph c).edgeCut {v | v ∈ B} ∩ (graph c).edgeCut {v | v ∈ B'}
    set E_new : Set (Edge c) := {e | ∃ D ∈ blocks', src e ∈ D ∧ tgt e ∈ D}
    have hE_inc : E_old.ncard + E_join.ncard ≤ E_new.ncard :=
      st.cmp.ncard_internal_add_join_le hB hB' hne
    have hm_pos : 1 ≤ E_join.ncard := hjoin.ncard_pos
    have hcount {dirty' : Finset (List (Vertex c))}
        (h : dirty'.card + 1 ≤ st.dirty.card + E_join.ncard) :
        dirty'.card + Nat.card (Vertex c) ≤ d₀ + blocks'.card + E_new.ncard := by
      have hc := st.count
      change st.dirty.card + Nat.card (Vertex c) ≤ d₀ + st.cmp.blocks.card + E_old.ncard at hc
      omega
    -- Update `dirty'` according to the three merge cases.
    by_cases hdirty_or : B ∈ st.dirty ∨ B' ∈ st.dirty
    · let dirty' := insert (B ++ B') ((st.dirty.erase B).erase B')
      have hd_sub' : dirty' ⊆ blocks' := by
        intro C hC
        simp only [dirty', Finset.mem_insert, Finset.mem_erase] at hC
        rcases hC with rfl | ⟨h1, h2, h3⟩
        · exact Finset.mem_insert_self _ _
        · exact hmem.mpr (Or.inr ⟨h1, h2, st.dirty_sub h3⟩)
      have hd_card' : dirty'.card ≤ st.dirty.card := by
        have hss : (st.dirty.erase B).erase B' ⊂ st.dirty := by
          refine Finset.ssubset_iff_subset_ne.mpr
            ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), fun h => ?_⟩
          rcases hdirty_or with h' | h' <;> rw [← h] at h' <;> simp at h'
        exact (Finset.card_insert_le _ _).trans (Finset.card_lt_card hss)
      refine ⟨{ cmp := cmp', dirty := dirty', dirty_sub := hd_sub', count := hcount (by omega),
                clean := ?_ }, Nat.lt_of_succ_le hcard.le⟩
      intro C hC hnotC
      rcases hmem.mp hC with rfl | ⟨h1, h2, hCo⟩
      · exact (hnotC (Finset.mem_insert_self _ _)).elim
      · refine st.clean C hCo fun hCd => hnotC ?_
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h1, Finset.mem_erase.mpr ⟨h2, hCd⟩⟩)
    · rw [not_or] at hdirty_or
      by_cases hm2 : 2 ≤ E_join.ncard
      · let dirty' := insert (B ++ B') st.dirty
        have hd_sub' : dirty' ⊆ blocks' := by
          intro C hC
          rcases Finset.mem_insert.mp hC with rfl | hCd
          · exact Finset.mem_insert_self _ _
          · exact hmem.mpr (Or.inr ⟨fun h => hdirty_or.2 (h ▸ hCd),
              fun h => hdirty_or.1 (h ▸ hCd), st.dirty_sub hCd⟩)
        have hd_card' : dirty'.card ≤ st.dirty.card + 1 := Finset.card_insert_le _ _
        refine ⟨{ cmp := cmp', dirty := dirty', dirty_sub := hd_sub', count := hcount (by omega),
                  clean := ?_ }, Nat.lt_of_succ_le hcard.le⟩
        intro C hC hnotC
        rcases hmem.mp hC with rfl | ⟨_, _, hCo⟩
        · exact (hnotC (Finset.mem_insert_self _ _)).elim
        · exact st.clean C hCo fun hCd => hnotC (Finset.mem_insert_of_mem hCd)
      · have hm1 : E_join.ncard = 1 := by omega
        have hd_sub' : st.dirty ⊆ blocks' := fun C hCd =>
          hmem.mpr (Or.inr ⟨fun h => hdirty_or.2 (h ▸ hCd),
            fun h => hdirty_or.1 (h ▸ hCd), st.dirty_sub hCd⟩)
        have hmerged_clean : CleanWire I {v | v ∈ B ++ B'} ∨ CleanBlock3 I {v | v ∈ B ++ B'} := by
          rw [happ]
          rcases st.clean B hB hdirty_or.1 with hwB | hbB <;>
            rcases st.clean B' hB' hdirty_or.2 with hwB' | hbB'
          · exact Or.inl (cleanWire_merge_wire hd_set hwB hwB' hm1)
          · exact Or.inr (cleanWire_merge_block3 hd_set hwB hbB' hm1)
          · rw [union_comm]
            exact Or.inr (cleanWire_merge_block3 hd_set.symm hwB' hbB
              (by rwa [inter_comm]))
          · -- Two `3`-pin blocks sharing `1` edge have cut size `3 + 3 - 2 = 4 > 3`, impossible!
            have hadd := (graph c).ncard_edgeCut_union_add hd_set
            have h3B := hbB.2.1
            have h3B' := hbB'.2.1
            change ((graph c).edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard + 2 * E_join.ncard =
              ((graph c).edgeCut {v | v ∈ B}).ncard + ((graph c).edgeCut {v | v ∈ B'}).ncard at hadd
            omega
        refine ⟨{ cmp := cmp', dirty := st.dirty, dirty_sub := hd_sub', count := hcount (by omega),
                  clean := ?_ }, Nat.lt_of_succ_le hcard.le⟩
        intro C hC hnotC
        rcases hmem.mp hC with rfl | ⟨_, _, hCo⟩
        · exact hmerged_clean
        · exact st.clean C hCo hnotC
  -- Now establish the three saturation consequences when `1 < Nat.card st.cmp.blocks`.
  refine ⟨st.cmp, st.dirty, hsat, st.dirty_sub, fun htwo => ?_⟩
  have hconn : (graph c).toSimpleGraph.Connected := connected c
  -- 1. Every non-dirty block has cut size `3`, so it cannot be `CleanWire` (`ncard = 2`).
  have hclean3 : ∀ B ∈ st.cmp.blocks, B ∉ st.dirty → CleanBlock3 I {v | v ∈ B} := by
    intro B hB hnot
    rcases st.clean B hB hnot with hw | hb
    · obtain ⟨e₁, e₂, _, _, hne12, hcut2, _⟩ := hw
      have hnc2 : ((graph c).edgeCut {v | v ∈ B}).ncard = 2 := by rw [hcut2, ncard_pair hne12]
      have hnc3 : ((graph c).edgeCut {v | v ∈ B}).ncard = 3 := by
        rw [← st.cmp.ncard_incidenceSet_quotient ⟨B, hB⟩]
        exact hsat.ncard_incidenceSet_quotient hconn htwo ⟨B, hB⟩
      omega
    · exact hb
  -- 2 & 3. Exact vertex/edge/dirty accounting on `Compiler.graph c`.
  have hsum_ext : 3 * Nat.card st.cmp.blocks = 2 * Nat.card st.cmp.external := by
    have hsum := st.cmp.sum_ncard_edgeCut
    have h3_each (B : st.cmp.blocks) : ((graph c).edgeCut {v | v ∈ B.1}).ncard = 3 := by
      rw [← st.cmp.ncard_incidenceSet_quotient B]
      exact hsat.ncard_incidenceSet_quotient hconn htwo B
    simp only [h3_each, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, mul_comm _ 3] at hsum
    exact hsum
  set E_int : Set (Edge c) := {e | ∃ B ∈ st.cmp.blocks, src e ∈ B ∧ tgt e ∈ B}
  have hcompl_ext : st.cmp.externalᶜ = E_int := st.cmp.compl_external
  have hE_part : Nat.card st.cmp.external + E_int.ncard = Nat.card (Edge c) := by
    rw [Nat.card_coe_set_eq, ← hcompl_ext, ncard_add_ncard_compl]
  have hblk_card : st.cmp.blocks.card = Nat.card st.cmp.blocks :=
    (Nat.card_eq_finsetCard st.cmp.blocks).symm
  -- Partition `Signal c` into inputs and arity `0`, `1` (const/wire), and `2` gates.
  let isConst1 (g : Fin c.size) : Prop :=
    ∃ b : Bool, ∀ x, I (c.program.lines g).op x = b
  let InpFin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with | .input _ => true | .gate _ => false
  let G0Fin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with | .input _ => false | .gate g => decide (σ.Arity (c.program.lines g).op = 0)
  let G1cFin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with
    | .input _ => false
    | .gate g => decide (σ.Arity (c.program.lines g).op = 1 ∧ isConst1 g)
  let G1wFin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with
    | .input _ => false
    | .gate g => decide (σ.Arity (c.program.lines g).op = 1 ∧ ¬isConst1 g)
  let G2Fin : Finset (Signal c) := Finset.univ.filter fun w =>
    match w.1 with | .input _ => false | .gate g => decide (σ.Arity (c.program.lines g).op = 2)
  have hcard_sum (S : Finset (Signal c)) : S.card = ∑ w : Signal c, if w ∈ S then 1 else 0 := by
    rw [← Finset.card_filter, Finset.filter_univ_mem]
  have hsig_sum : Nat.card (Signal c) =
      InpFin.card + G0Fin.card + G1cFin.card + G1wFin.card + G2Fin.card := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    have hpart (w : Signal c) :
        (if w ∈ InpFin then 1 else 0) + (if w ∈ G0Fin then 1 else 0) +
          (if w ∈ G1cFin then 1 else 0) + (if w ∈ G1wFin then 1 else 0) +
          (if w ∈ G2Fin then 1 else 0) = 1 := by
      rcases w with ⟨i | g, hw⟩
      · simp [InpFin, G0Fin, G1cFin, G1wFin, G2Fin]
      · rcases har g with h | h | h <;> by_cases hc : isConst1 g <;>
          simp [InpFin, G0Fin, G1cFin, G1wFin, G2Fin, h, hc]
    rw [hcard_sum InpFin, hcard_sum G0Fin, hcard_sum G1cFin, hcard_sum G1wFin, hcard_sum G2Fin,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    simp only [hpart, Finset.sum_const, smul_eq_mul, mul_one]
  -- Count `Slot c` by grouping over `Signal c`.
  have hslot_sum : Nat.card (Slot c) = G1cFin.card + G1wFin.card + 2 * G2Fin.card := by
    let slotOwner (s : Slot c) : Signal c := ⟨.gate s.1.1, s.2⟩
    have := Fintype.ofFinite (Slot c)
    have hu : (Finset.univ : Finset (Slot c)) = Finset.univ.biUnion fun w : Signal c =>
        Finset.univ.filter fun s : Slot c => slotOwner s = w := by
      ext s; simp
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, hu,
      Finset.card_biUnion (fun w₁ _ w₂ _ hne => Finset.disjoint_left.mpr fun s hs1 hs2 =>
        hne ((Finset.mem_filter.mp hs1).2.symm.trans (Finset.mem_filter.mp hs2).2))]
    have hfib (w : Signal c) :
        (Finset.univ.filter fun s : Slot c => slotOwner s = w).card =
          (if w ∈ G1cFin then 1 else 0) + (if w ∈ G1wFin then 1 else 0) +
            2 * (if w ∈ G2Fin then 1 else 0) := by
      rcases w with ⟨i | g, hw⟩
      · have hem : (Finset.univ.filter fun s : Slot c => slotOwner s = ⟨.input i, hw⟩) = ∅ := by
          ext s; simp [slotOwner]
        rw [hem]; simp [G1cFin, G1wFin, G2Fin]
      · have hbij : (Finset.univ.filter fun s : Slot c => slotOwner s = ⟨.gate g, hw⟩).card =
            σ.Arity (c.program.lines g).op := by
          rw [← Fintype.card_fin (σ.Arity (c.program.lines g).op)]
          refine Finset.card_bij (fun a _ => ⟨⟨g, a⟩, hw⟩)
            (fun a _ => by simp [slotOwner])
            (fun a₁ _ a₂ _ h => by
              have hval : (a₁ : ℕ) = (a₂ : ℕ) :=
                congrArg (fun s : Slot c => (s.1.2 : ℕ)) h
              exact Fin.ext hval)
            (fun s hs => by
              have hsw : slotOwner s = ⟨.gate g, hw⟩ := (Finset.mem_filter.mp hs).2
              have hg_eq : s.1.1 = g := Wire.gate.inj (congrArg Subtype.val hsw)
              rcases s with ⟨⟨g', a⟩, hg'⟩
              dsimp at hg_eq
              subst hg_eq
              exact ⟨a, Finset.mem_univ a, rfl⟩)
            |>.symm
        rw [hbij]
        rcases har g with h | h | h <;> by_cases hc : isConst1 g <;>
          simp [G1cFin, G1wFin, G2Fin, h, hc]
    simp_rw [hfib]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← hcard_sum G1cFin, ← hcard_sum G1wFin, ← hcard_sum G2Fin]
  -- Bound `G1cFin.card + G1wFin.card + G2Fin.card ≤ c.innerSize`.
  have hinner_le : G1cFin.card + G1wFin.card + G2Fin.card ≤ c.innerSize := by
    have hdisj12 : Disjoint G1cFin G1wFin := Finset.disjoint_left.mpr fun w hw1 hw2 => by
      rcases w with ⟨i | g, hw⟩
      · simp [G1cFin] at hw1
      · simp only [G1cFin, G1wFin, Finset.mem_filter, Finset.mem_univ, true_and,
          decide_eq_true_eq] at hw1 hw2
        exact hw2.2 hw1.2
    have hdisj_2 : Disjoint (G1cFin ∪ G1wFin) G2Fin := Finset.disjoint_left.mpr fun w hw12 hw2 => by
      rcases w with ⟨i | g, hw⟩
      · simp [G2Fin] at hw2
      · simp only [Finset.mem_union, G1cFin, G1wFin, G2Fin, Finset.mem_filter, Finset.mem_univ,
          true_and, decide_eq_true_eq] at hw12 hw2
        rcases hw12 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    rw [← Finset.card_union_of_disjoint hdisj12, ← Finset.card_union_of_disjoint hdisj_2,
      Circuit.innerSize]
    by_cases hcs : 0 < c.size
    · refine Finset.card_le_card_of_injOn
        (fun w => match w.1 with | .input _ => ⟨0, hcs⟩ | .gate g => g)
        (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_)
      · rcases w with ⟨i | g, hreach⟩
        · simp [G1cFin, G1wFin, G2Fin] at hw
        · simp only [Finset.mem_coe, Program.mem_innerGates]
          simp only [Finset.mem_coe, Finset.mem_union, G1cFin, G1wFin, G2Fin, Finset.mem_filter,
            Finset.mem_univ, true_and, decide_eq_true_eq] at hw
          rcases hw with (⟨h1, _⟩ | ⟨h1, _⟩) | h2 <;> omega
      · rcases w₁ with ⟨i₁ | g₁, hr₁⟩
        · simp [G1cFin, G1wFin, G2Fin] at hw₁
        · rcases w₂ with ⟨i₂ | g₂, hr₂⟩
          · simp [G1cFin, G1wFin, G2Fin] at hw₂
          · dsimp at heq; subst heq; rfl
    · have hem : G1cFin ∪ G1wFin ∪ G2Fin = ∅ := by
        ext ⟨i | g, hr⟩
        · simp [G1cFin, G1wFin, G2Fin]
        · exact (hcs (Nat.zero_lt_of_lt g.isLt)).elim
      rw [hem]; exact Nat.zero_le _
  -- Relate `d₀` and `(hiddenNetwork c I Acc).read.ncard` to `InpFin, G0Fin, G1cFin`.
  have hd₀_eq : d₀ = InpFin.card + G0Fin.card + G1cFin.card + 1 := by
    have hpart_v (v : Vertex c) :
        (if v ∈ Dfin then 1 else 0) =
          (match v with
          | .signal w => (if w ∈ InpFin then 1 else 0) + (if w ∈ G0Fin then 1 else 0) +
              (if w ∈ G1cFin then 1 else 0)
          | .junction _ => 0
          | .output _ => 1) := by
      cases v with
      | signal w =>
        rcases w with ⟨i | g, hw⟩
        · simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin]
        · rcases har g with h | h | h
          · simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h]
          · by_cases hc : isConst1 g
            · have hc' : ∃ b : Bool, ∀ x, I (c.program.lines g).op x = b := hc
              simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h, hc, hc']
            · have hc' : ¬∃ b : Bool, ∀ x, I (c.program.lines g).op x = b := hc
              simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h, hc, hc']
          · simp [Dfin, IsDirtySingleton, InpFin, G0Fin, G1cFin, h]
      | junction _ => simp [Dfin, IsDirtySingleton]
      | output _ => simp [Dfin, IsDirtySingleton]
    have hD : d₀ = ∑ v : Vertex c, if v ∈ Dfin then 1 else 0 := by
      dsimp only [d₀]; rw [← Finset.card_filter, Finset.filter_univ_mem]
    rw [hD]
    simp_rw [hpart_v]
    rw [← Vertex.equiv.symm.sum_comp]
    simp only [Fintype.sum_sum_type, Vertex.equiv, Equiv.coe_fn_symm_mk, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hcard_sum InpFin, ← hcard_sum G0Fin,
      ← hcard_sum G1cFin]
    omega
  have hread_le : (hiddenNetwork c I Acc).read.ncard ≤ InpFin.card := by
    rw [← Nat.card_coe_set_eq]
    have hinj : Function.Injective
        (fun i : (hiddenNetwork c I Acc).read =>
          (⟨⟨Wire.input (finSumFinEquiv (.inl i.1)), by
            obtain ⟨v, _, hsite⟩ := i.2
            change site c (finSumFinEquiv (.inl i.1)) = some v at hsite
            exact (site_eq_some hsite).1⟩, by simp [InpFin]⟩ :
            {w : Signal c // w ∈ InpFin})) := by
      intro i₁ i₂ h
      have hw := Wire.input.inj (congrArg (fun x => x.1.1) h)
      exact Subtype.ext (Sum.inl.inj (finSumFinEquiv.injective hw))
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := {w : Signal c // w ∈ InpFin}), Fintype.card_coe] at hle
  -- Vertex and edge counts of `Compiler.graph c`.
  have hcard_cons : Nat.card (Consumer c) = Nat.card (Slot c) + 1 := by
    rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin 1), Fintype.card_fin]
  have hcard_V : Nat.card (Vertex c) = Nat.card (Signal c) + Nat.card (Consumer c) + 1 := by
    rw [Nat.card_congr Vertex.equiv, Nat.card_sum, Nat.card_sum,
      Nat.card_congr (junctionEquiv c), Nat.card_eq_fintype_card (α := Fin 1), Fintype.card_fin,
      add_assoc]
  have hcard_E : Nat.card (Edge c) = 2 * Nat.card (Consumer c) := card_edge
  have hcmp_le : Nat.card (Vertex c) ≤ st.cmp.blocks.card + E_int.ncard := st.cmp.card_le
  have hcnt : st.dirty.card + Nat.card (Vertex c) ≤ d₀ + st.cmp.blocks.card + E_int.ncard :=
    st.count
  refine ⟨hclean3, ?_, ?_⟩ <;> omega

end CleanCompression

end Cslib.Circuits.Frontier.Compiler
