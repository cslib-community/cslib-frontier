/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
public import CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
public import CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.Observables
-- `import all`: reads private active-decoupling, capped-wire-network, and single-cut inequality
-- lemmas from sibling `WireNetwork` modules.
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.OpenState
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.CappedNet
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.Observables
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.AcceptCutBounds
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.StateLinearCutBounds
import CslibFrontier.Foundations.Data.Set.Card

/-!
# Packaged compiled wire-segment tensor networks for quantum circuits

Packages the degree-`d` (`d ∈ {3, 4}`) compiled wire-segment multigraph (`CompiledQuantumNet`)
together with its vertex-count, component cycle-rank, and single-cut correlation / sign-rank /
fidelity / linear-synthesis bounds (`exists_compiledQuantumNet`).

## Main definitions

* `Cslib.Circuits.Frontier.CompiledQuantumNet`: packaged finite degree-`d` wire network compiled
  from `C : Quantum.Circuit N` together with its component cycle-rank and single-cut bounds.

## Main results

* `Cslib.Circuits.Frontier.exists_compiledQuantumNet`: compiles any `AllBondRankTwo` (`d = 3`) or
  `TwoLocal` (`d = 4`) quantum circuit into a `CompiledQuantumNet`.
-/

public section

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

/-! ### Packaged compiled wire network for quantum circuits -/

open Classical in
/-- Packaged finite degree-`d` wire-segment multigraph compiled from `C : Quantum.Circuit N`
with data qubits `e : Fin n ↪ Fin N` and extra tracked qubit `q_extra : Fin N`, bundling the
vertex bound, component cycle-rank inequalities, and single-cut rank/correlation/fidelity bounds. -/
structure CompiledQuantumNet {n N : ℕ} (d : ℕ) (e : Fin n ↪ Fin N) (q_extra : Fin N)
    (C : Quantum.Circuit N) where
  /-- Vertex type of the compiled wire network. -/
  V : Type
  /-- Edge type of the compiled wire network. -/
  E : Type
  instFV : Fintype V
  instFE : Fintype E
  instDE : DecidableEq E
  /-- Underlying loopless degree-`d` multigraph. -/
  G : Multigraph V E
  loopless : G.Loopless
  maxDeg : G.MaxDegreeLE d
  card_V_le : (Nat.card V : ℝ) ≤ 2 * n + 6 * (twoQubitCount C : ℝ) + 2
  /-- Input leaf vertices of the `n` data qubits. -/
  leafIn : Fin n ↪ V
  /-- Output leaf vertices of the `n` data qubits. -/
  leafOut : Fin n ↪ V
  /-- Joint `2 * n` input/output leaf vertices (`inl2n` = inputs, `inr2n` = outputs). -/
  leaf2n : Fin (2 * n) ↪ V
  cycleRank_leafIn_le : ∀ Comp : Set V, G.edgeCut Comp = ∅ →
    Comp.ncard ≤ (G.touching Comp).ncard + 1 →
    G.cycleRankOn Comp + {i : Fin n | leafIn i ∈ Comp}.ncard ≤ twoQubitCount C + 1
  cycleRank_leafOut_le : ∀ Comp : Set V, G.edgeCut Comp = ∅ →
    Comp.ncard ≤ (G.touching Comp).ncard + 1 →
    G.cycleRankOn Comp + {i : Fin n | leafOut i ∈ Comp}.ncard ≤ twoQubitCount C + 1
  cycleRank_leaf2n_le : ∀ Comp : Set V, G.edgeCut Comp = ∅ →
    Comp.ncard ≤ (G.touching Comp).ncard + 1 →
    2 * G.cycleRankOn Comp + {k : Fin (2 * n) | leaf2n k ∈ Comp}.ncard ≤
      2 * (twoQubitCount C + 1)
  sq_quantumCorrelation_mul_le : ∀ (x₀ : Fin N → Bool) (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Set V),
    quantumCorrelation {x | BitString.quadForm Q x} (quantumAcceptProb C q_extra e x₀) ^ 2 *
      (2 : ℝ) ^ (Q + Qᵀ).cutRank {i | leafIn i ∈ P} ≤
      4 * (4 : ℝ) ^ (G.edgeCut P).ncard
  signRank_uqp_le : ∀ (x₀ : Fin N → Bool) {f : (Fin n → Bool) → Bool} {θ : ℝ},
    (∀ x, if f x then θ < quantumAcceptProb C q_extra e x₀ x
      else quantumAcceptProb C q_extra e x₀ x < θ) →
    ∀ P : Set V,
    Communication.signRank (fun (a : {i | leafIn i ∈ P} → Bool)
        (b : ↥{i | leafIn i ∈ P}ᶜ → Bool) =>
      f ((Equiv.piEquivPiSubtypeProd (· ∈ {i | leafIn i ∈ P}) fun _ => Bool).symm (a, b))) ≤
      3 * 4 ^ (G.edgeCut P).ncard
  sq_fidelity_phaseState_mul_le : ∀ (x₀ : Fin N → Bool) (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Set V),
    ‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 *
      (2 : ℝ) ^ (Q + Qᵀ).cutRank {i | leafOut i ∈ P} ≤
      4 * (2 : ℝ) ^ (G.edgeCut P).ncard
  cutRank_linBlockMatrix_le : ∀ (x₀ : Fin N → Bool) {R : Matrix (Fin n) (Fin n) (ZMod 2)},
    (∀ x, C.run (Quantum.glue e x x₀) = Quantum.ket (Quantum.glue e (boolMulVec R x) x₀)) →
    ∀ P : Set V,
    (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank {k | leaf2n k ∈ P} ≤
      (G.edgeCut P).ncard + 1

attribute [instance] CompiledQuantumNet.instFV CompiledQuantumNet.instFE CompiledQuantumNet.instDE

/-- **Compile a two-local quantum circuit into a `CompiledQuantumNet`.** Under `AllBondRankTwo C`
(`d = 3`) or `TwoLocal C` (`d = 4`), decoupling inactive qubits and splitting active two-qubit
gates produces a `CompiledQuantumNet d e q_extra C`. -/
theorem exists_compiledQuantumNet {n N d : ℕ} (hd : d = 3 ∨ d = 4)
    (e : Fin n ↪ Fin N) (q_extra : Fin N) {C : Quantum.Circuit N}
    (hmodel : if d = 3 then AllBondRankTwo C else TwoLocal C) :
    Nonempty (CompiledQuantumNet d e q_extra C) := by
  have htwo : TwoLocal C := by
    rcases hd with rfl | rfl
    · exact fun g hg => (hmodel g hg).1
    · exact hmodel
  classical
  set Aset := activeSet e q_extra C
  have heA : Set.range e ⊆ Aset := range_subset_activeSet e q_extra C
  have hqA : q_extra ∈ Aset := mem_activeSet_extra e q_extra C
  have hneA : Nonempty ↥Aset := ⟨⟨q_extra, hqA⟩⟩
  obtain ⟨L, inactU, hlenL, hbondL, hsplit⟩ :=
    exists_active_split Aset C htwo (touchingIn_activeSet e q_extra C)
  have hcap : CappedWireNet d ↥Aset (evalAct L) (twoQubitCount C) := by
    rw [← hlenL]
    rcases hd with rfl | rfl
    · exact (exists_cappedWireNet L).2 (hbondL hmodel)
    · exact (exists_cappedWireNet L).1
  obtain ⟨V_fin, E_fin, instFV, _, instFE, instDE, G, inVert, outVert, F,
    hG_loop, hG_deg, hdisj_io, _, hreach, hV_card, hG_ρ, hcontract, hloc_in, hloc_out, hloc_edge⟩ :=
    hcap.exists_net
  let embA : Fin n ↪ ↥Aset :=
    ⟨fun i => ⟨e i, heA ⟨i, rfl⟩⟩, fun _ _ h => e.injective (congrArg Subtype.val h)⟩
  let leafIn : Fin n ↪ V_fin := embA.trans inVert
  let leafOut : Fin n ↪ V_fin := embA.trans outVert
  let leaf2n : Fin (2 * n) ↪ V_fin :=
    ⟨fun k => if hk : k.1 < n then leafIn ⟨k.1, hk⟩ else leafOut ⟨k.1 - n, by omega⟩,
      fun k₁ k₂ hk => by
        dsimp only at hk
        by_cases h1 : k₁.1 < n <;> by_cases h2 : k₂.1 < n <;> simp only [h1, h2, ↓reduceDIte] at hk
        · exact Fin.ext (Fin.mk.inj (leafIn.injective hk))
        · exact (Set.disjoint_left.mp hdisj_io ⟨_, rfl⟩ ⟨_, hk.symm⟩).elim
        · exact (Set.disjoint_left.mp hdisj_io ⟨_, rfl⟩ ⟨_, hk⟩).elim
        · have := Fin.mk.inj (leafOut.injective hk)
          ext; omega⟩
  have hleaf_in (i : Fin n) : leaf2n (inl2n n i) = leafIn i := dite_eq_left i.isLt
  have hleaf_out (j : Fin n) : leaf2n (inr2n n j) = leafOut j := by
    change (if hk : n + j.1 < n then _ else leafOut ⟨n + j.1 - n, _⟩) = _
    rw [dite_eq_right (by omega)]
    exact congrArg leafOut (Fin.ext (by dsimp; omega))
  have hV_ub : (Nat.card V_fin : ℝ) ≤ 2 * n + 6 * (twoQubitCount C : ℝ) + 2 := by
    rw [Nat.card_eq_fintype_card]
    have hA_card : Fintype.card ↥Aset ≤ n + 2 * twoQubitCount C + 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact ncard_activeSet_le e q_extra htwo
    exact_mod_cast (by omega : Fintype.card V_fin ≤ 2 * n + 6 * twoQubitCount C + 2)
  have hcard_le (Comp : Set V_fin) (f : Fin n → V_fin)
      (hf : ∀ i, f i ∈ Comp → inVert (embA i) ∈ Comp) :
      {i : Fin n | f i ∈ Comp}.ncard ≤ {q : ↥Aset | inVert q ∈ Comp}.ncard := by
    rw [← ncard_image_of_injective _ embA.injective]
    exact ncard_le_ncard (by rintro _ ⟨i, hi, rfl⟩; exact hf i hi) (toFinite _)
  have hout_le (Comp : Set V_fin) (hcut : G.edgeCut Comp = ∅) :=
    hcard_le Comp leafOut fun i hi => (mem_closed_iff_of_reachable hcut (hreach (embA i))).mpr hi
  refine ⟨{
    V := V_fin, E := E_fin, instFV, instFE, instDE, G
    loopless := hG_loop, maxDeg := hG_deg, card_V_le := hV_ub, leafIn, leafOut, leaf2n
    cycleRank_leafIn_le := fun Comp hcut hconn => by
      have := hcard_le Comp leafIn fun _ h => h
      have := hG_ρ Comp hcut hconn; omega
    cycleRank_leafOut_le := fun Comp hcut hconn => by
      have := hout_le Comp hcut
      have := hG_ρ Comp hcut hconn; omega
    cycleRank_leaf2n_le := fun Comp hcut hconn => by
      have hsub2n : {k : Fin (2 * n) | leaf2n k ∈ Comp} ⊆
          inl2n n '' {i | leafIn i ∈ Comp} ∪ inr2n n '' {j | leafOut j ∈ Comp} := fun k hk => by
        change (if hk : k.1 < n then leafIn ⟨k.1, hk⟩ else leafOut ⟨k.1 - n, _⟩) ∈ Comp at hk
        by_cases hk_lt : k.1 < n
        · simp only [hk_lt, ↓reduceDIte] at hk
          exact .inl ⟨⟨k.1, hk_lt⟩, hk, Fin.ext rfl⟩
        · simp only [hk_lt, ↓reduceDIte] at hk
          exact .inr ⟨⟨k.1 - n, by omega⟩, hk, Fin.ext (by simp [inr2n]; omega)⟩
      have hcard2n : {k : Fin (2 * n) | leaf2n k ∈ Comp}.ncard ≤
          2 * {q : ↥Aset | inVert q ∈ Comp}.ncard := by
        refine (ncard_le_ncard hsub2n (toFinite _)).trans ((ncard_union_le _ _).trans ?_)
        rw [ncard_image_of_injective _ (inl2n_injective n),
          ncard_image_of_injective _ (inr2n_injective n), two_mul]
        exact add_le_add (hcard_le Comp leafIn fun _ h => h) (hout_le Comp hcut)
      have := hG_ρ Comp hcut hconn; omega
    sq_quantumCorrelation_mul_le := fun x₀ Q P =>
      sq_quantumCorrelation_mul_le_of_capped (x₀ := x₀) heA hqA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge Q P
    signRank_uqp_le := fun x₀ {_ _} huqp P =>
      signRank_uqp_le_of_capped (x₀ := x₀) heA hqA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge huqp P
    sq_fidelity_phaseState_mul_le := fun x₀ Q P =>
      sq_fidelity_phaseState_mul_le_of_capped (x₀ := x₀) heA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge Q P
    cutRank_linBlockMatrix_le := fun x₀ {_} hlin P =>
      cutRank_linBlockMatrix_le_of_capped (x₀ := x₀) heA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge _ hlin leaf2n hleaf_in hleaf_out P }⟩


end Cslib.Circuits.Frontier
