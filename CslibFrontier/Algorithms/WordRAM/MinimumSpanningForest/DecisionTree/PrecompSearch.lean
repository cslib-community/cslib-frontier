/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompEval
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM Optimal Decision-Tree Search and Precomputation (`precomputeDTProg`)

Implements and verifies the exhaustive search over complete binary comparison skeletons and
top-level table builder `precomputeDTProg` as steps toward [PettieRamachandran2002], Theorem 5.8
(#8624; Section 4.1, p. 23 and Section 5.1, pp. 25–26, Corollary 5.6 and Theorem 5.8), reusing
`Memory.allocBlockDirty`, `fillConstProg`, `boundedWhile`, `iterate`, `word_enc_structure`,
`DecisionTree.PrecompKruskal`, and `DecisionTree.PrecompEval`.

## Main definitions

* `precomputeDTProg`: Word-RAM routine building the complete optimal-`MSFDT` lookup table for all
  simple graphs on `v ≤ r0` vertices (`mask < 2 ^ r0.choose 2`).
* `precomputeDTProgSafe`: clean word-fit precondition `Fits w (s.frontier + dtPrecompCost r0)`.
* `precomputeDTProgSafe_iff`: equivalence characterizing `precomputeDTProgSafe`.

## Main results

* `precomputeDTProg_spec`: framed specification proving `HoldsDTTable r0 tableBase s'.mem` and
  `DTTableInBounds r0 tableBase s'.frontier s'.mem` in `dtPrecompCost r0` time and frontier
  growth, modifying no cells below `s.frontier`.
* `realizes_precomputeDTProg`: uniform `Realizes .exact` certificate with `work = 0`.

## References

* [Seth Pettie and Vijaya Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), pp. 16–34, 2002][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Internal Search Structures and Arithmetic Bounds -/

private structure DTDecodePermEnv where
  powEArr : ℕ
  rankArr : ℕ
  orderArr : ℕ
  seenArr : ℕ
  e : ℕ
  code : ℕ
  deriving DecidableEq

private word_enc_structure dtDecodePermEnvWords : DTDecodePermEnv where
  powEArr : wordWords, rankArr : wordWords, orderArr : wordWords,
  seenArr : wordWords, e : wordWords, code : wordWords

private instance : WordEncoding DTDecodePermEnv := ⟨6, dtDecodePermEnvWords⟩

private structure DTSkelState where
  skelCode : ℕ
  found : ℕ
  cont : ℕ
  deriving DecidableEq

private word_enc_structure dtSkelStateWords : DTSkelState where
  skelCode : wordWords, found : wordWords, cont : wordWords

private instance : WordEncoding DTSkelState := ⟨3, dtSkelStateWords⟩

private structure DTDepthEnv where
  env : DTPrecompEnv
  mask : ℕ
  e : ℕ
  numPairs : ℕ
  permAns : ℕ
  powE : ℕ
  deriving DecidableEq

private word_enc_structure dtDepthEnvWords : DTDepthEnv where
  env : dtPrecompEnvWords, mask : wordWords, e : wordWords,
  numPairs : wordWords, permAns : wordWords, powE : wordWords

private instance : WordEncoding DTDepthEnv := ⟨25, dtDepthEnvWords⟩

private structure DTDepthState where
  d : ℕ
  found : ℕ
  deriving DecidableEq

private word_enc_structure dtDepthStateWords : DTDepthState where
  d : wordWords, found : wordWords

private instance : WordEncoding DTDepthState := ⟨2, dtDepthStateWords⟩

private structure DTBuildSearchArgs where
  env : DTPrecompEnv
  mask : ℕ
  e : ℕ
  deriving DecidableEq

private word_enc_structure dtBuildSearchArgsWords : DTBuildSearchArgs where
  env : dtPrecompEnvWords, mask : wordWords, e : wordWords

private instance : WordEncoding DTBuildSearchArgs := ⟨22, dtBuildSearchArgsWords⟩

private def dtSkelCompat {r0 e : ℕ} (he2 : 2 ≤ e) (mask : ℕ)
    (he_eq : e = (maskEdgePairs r0 mask).length) (sc d : ℕ) : Prop :=
  ∀ p q : Equiv.Perm (Fin e), walkSkelNode e he2 sc d 1 p = walkSkelNode e he2 sc d 1 q →
    let σ : Fin e ≃ Fin (maskEdgePairs r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
    Cslib.Multigraph.msf (endsOfMask r0 mask) (σ.symm.trans (p.trans σ)) Finset.univ =
      Cslib.Multigraph.msf (endsOfMask r0 mask) (σ.symm.trans (q.trans σ)) Finset.univ

private theorem dtMaskOfFinset_msf_cast {r0 e₁ e₂ : ℕ} (he : e₁ = e₂)
    (ends₁ : Fin e₁ → Sym2 (Fin r0)) (ends₂ : Fin e₂ → Sym2 (Fin r0))
    (hends : ∀ i : Fin e₁, ends₁ i = ends₂ ((Fin.castOrderIso he).toEquiv i))
    (p : Equiv.Perm (Fin e₁)) :
    let σ := (Fin.castOrderIso he).toEquiv
    maskOfFinset (Cslib.Multigraph.msf ends₁ p Finset.univ) =
      maskOfFinset (Cslib.Multigraph.msf ends₂ (σ.symm.trans (p.trans σ)) Finset.univ) := by
  subst he
  have hσ : (Fin.castOrderIso rfl).toEquiv = Equiv.refl (Fin e₁) := by ext x; rfl
  have he_eq : ends₁ = ends₂ := funext fun i => by simpa [hσ] using hends i
  subst he_eq
  have hp : (Equiv.refl (Fin e₁)).symm.trans (p.trans (Equiv.refl (Fin e₁))) = p := by ext x; rfl
  dsimp only; rw [hσ, hp]

private theorem framedTriple_with_modifies {α : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {c : ℕ} {S : Set ℕ} {Q : α → Memory.State → Prop}
    (h : Memory.FramedTriple w s p c S Q) :
    Memory.FramedTriple w s p c S fun a s' => Memory.Modifies S s s' ∧ Q a s' :=
  have hr := framedTriple_iff_realization.mp h
  framedTriple_iff_realization.mpr ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.1, hr.2.2.2⟩

private theorem framedTriple_above_frontier_to_empty {α : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {c : ℕ} {Q : α → Memory.State → Prop}
    (h : Memory.FramedTriple w s p c {a | s.frontier ≤ a} Q) :
    Memory.FramedTriple w s p c ∅ Q := by
  obtain ⟨hv, hc, hm, hq⟩ := framedTriple_iff_realization.mp h
  exact framedTriple_iff_realization.mpr ⟨hv, hc, ⟨hm.1, fun a ha _ =>
    hm.mem_eq_of_not_mem ha (by change ¬(s.frontier ≤ a); omega)⟩, hq⟩

private theorem boundedWhile_framedTriple_spec {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    {w : ℕ} {d : δ} {B : ℕ} {I : σ → Memory.State → Prop} {rank : σ → Memory.State → ℕ}
    {S : Set ℕ} (hzero : ∀ a s, I a s → rank a s = 0 → ¬guard d a)
    (hstep : ∀ a s, I a s → guard d a → safe w (d, a) s ∧
      Memory.FramedTriple w s (body (d, a)) B S fun a' s' => I a' s' ∧ rank a' s' < rank a s)
    {fuel : ℕ} {a : σ} {s : Memory.State} (hi : I a s) (hr : rank a s ≤ fuel) :
    whileSafe guard body safe w d fuel a s ∧
    Memory.FramedTriple w s (boundedWhile guard body d fuel a) (B * rank a s) S
      fun a' s' => ¬guard d a' ∧ I a' s' := by
  obtain ⟨hs, hv, hg, hi', hmod, hc⟩ := boundedWhile_spec guard body safe w d B I rank S hzero
    (fun a s hi hg => let ⟨hs', ht'⟩ := hstep a s hi hg
      ⟨hs', framedTriple_iff_realization.mp ht'⟩) fuel a s hi hr
  exact ⟨hs, framedTriple_iff_realization.mpr ⟨hv, hc, hmod, hg, hi'⟩⟩

private theorem framedTriple_bind_client {α β : Type} {w c₁ c₂ C : ℕ}
    {s : Memory.State} {S₁ S₂ S : Set ℕ} {p₁ : Memory.Prog α} {p₂ : α → Memory.Prog β}
    {Q₁ : α → Memory.State → Prop} {Q : β → Memory.State → Prop}
    (h₁ : Memory.FramedTriple w s p₁ c₁ S₁ Q₁) (hS₁ : S₁ ⊆ S) (hS₂ : S₂ ⊆ S)
    (hC : c₁ + c₂ ≤ C)
    (h₂ : let a₁ := (Memory.spec 0).clientResult s p₁
          let s₁ := (Memory.spec 0).clientState s p₁
          Q₁ a₁ s₁ → Memory.Modifies S₁ s s₁ → Memory.FramedTriple w s₁ (p₂ a₁) c₂ S₂ Q) :
    Memory.FramedTriple w s (p₁ >>= p₂) C S Q := by
  obtain ⟨hv₁, _, hm₁, hq₁⟩ := framedTriple_iff_realization.mp h₁
  obtain ⟨hv₂, _, hm₂, hq₂⟩ := framedTriple_iff_realization.mp (h₂ hq₁ hm₁)
  refine framedTriple_iff_realization.mpr
    ⟨(validHistory_bind' w p₁ p₂ s).mpr ⟨hv₁, hv₂⟩, by rw [memoryCost_bind']; omega, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind]; exact (hm₁.mono hS₁).trans (hm₂.mono hS₂)
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]; exact hq₂

private theorem dtExistsGoodSkel {r0 mask e d : ℕ} (he2 : 2 ≤ e)
    (he_eq : e = (maskEdgePairs r0 mask).length) (hopt : optDepth (endsOfMask r0 mask) ≤ d) :
    ∃ sc < (e.choose 2) ^ (2 ^ d - 1), dtSkelCompat he2 mask he_eq sc d := by
  subst he_eq
  obtain ⟨sc, hsc, hcompat⟩ := exists_skelCode_of_complete_correct he2 (endsOfMask r0 mask) hopt
  refine ⟨sc, hsc, fun p q heq => ?_⟩
  have hσ : (Fin.castOrderIso rfl).toEquiv =
      Equiv.refl (Fin (maskEdgePairs r0 mask).length) := by ext x; rfl
  simpa only [hσ, Equiv.refl_symm, Equiv.refl_trans, Equiv.trans_refl] using hcompat p q heq

private theorem le_dtPrecompCost_of_exp_le {r0 k x : ℕ} (hr2 : 2 ≤ r0)
    (hk : k ≤ 4 * r0 ^ 4 + 16) (hx : x ≤ 2 ^ (2 ^ k)) : x ≤ dtPrecompCost r0 := by
  have hnot1 : ¬ (r0 ≤ 1) := by omega
  dsimp only [dtPrecompCost]; simp only [hnot1, ↓reduceIte]
  exact hx.trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hk))

private theorem dtArith_poly_helper {r0 e mE mD P ee s2d T : ℕ}
    (h16 : 16 ≤ P) (hPT : P ≤ T) (_hT : 1 ≤ T)
    (hr0 : r0 ≤ P) (he : e ≤ P) (hmE : mE ≤ P) (hmD : mD ≤ P) (hee : ee ≤ P) (hs2d : s2d ≤ P) :
    5 * mE + (1 + 2 * e) + (3 + ee * (2 + 7 * e + r0 + e * (5 + 2 * r0)) + e * (1 + 2 * e)) ≤
      21 * P ^ 3 ∧
    (mD + 1) * (2 * s2d + 1 + T * (5 + 2 * e + 9 * s2d + ee * (4 + 5 * mD))) ≤
      26 * P ^ 3 * T ∧ r0 * (1 + 2 * r0) + 2 ≤ 4 * P ^ 2 := by
  have h1 : e * (5 + 2 * r0) ≤ P * (5 + 2 * P) := Nat.mul_le_mul he (by omega)
  have h2 : ee * (2 + 7 * e + r0 + e * (5 + 2 * r0)) ≤ P * (2 + 8 * P + P * (5 + 2 * P)) :=
    Nat.mul_le_mul hee (by omega)
  have h3 : e * (1 + 2 * e) ≤ P * (1 + 2 * P) := Nat.mul_le_mul he (by omega)
  have h4 : ee * (4 + 5 * mD) ≤ P * (4 + 5 * P) := Nat.mul_le_mul hee (by omega)
  have hm : 5 + 2 * e + 9 * s2d + ee * (4 + 5 * mD) ≤ 10 * P ^ 2 := by nlinarith
  have hTm : T * (5 + 2 * e + 9 * s2d + ee * (4 + 5 * mD)) ≤ 10 * P ^ 2 * T :=
    (Nat.mul_le_mul_left T hm).trans_eq (by ring)
  have h5 : 2 * s2d + 1 + T * (5 + 2 * e + 9 * s2d + ee * (4 + 5 * mD)) ≤ 13 * P ^ 2 * T := by
    have h2P : 2 * s2d + 1 ≤ 3 * P ^ 2 * T := by nlinarith
    exact (Nat.add_le_add h2P hTm).trans_eq (by ring)
  have h6 : (mD + 1) * (13 * P ^ 2 * T) ≤ 2 * P * (13 * P ^ 2 * T) :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨by nlinarith, (Nat.mul_le_mul_left _ h5).trans (h6.trans_eq (by ring)), by nlinarith⟩

private theorem dtPrecompArithBounds_core {r0 e A B P T : ℕ} (h16 : 16 ≤ A) (hB : B = 2 * A)
    (hP : P = 2 ^ A) (hT : T = 2 ^ (2 ^ B))
    (hr0 : r0 ≤ P) (he : e ≤ P) (hmE : r0.choose 2 ≤ P) (hmD : (r0.choose 2).choose 2 ≤ P)
    (hee : e ^ e ≤ P) (hs2d : 2 ^ (r0.choose 2).choose 2 ≤ P)
    (hsk : (e.choose 2) ^ (2 ^ (r0.choose 2).choose 2 - 1) ≤ T) :
    5 * r0.choose 2 + (1 + 2 * e) + (3 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) +
      e * (1 + 2 * e) + ((r0.choose 2).choose 2 + 1) * (2 * 2 ^ (r0.choose 2).choose 2 + 1 +
        (e.choose 2) ^ (2 ^ (r0.choose 2).choose 2 - 1) *
          (5 + 2 * e + 9 * 2 ^ (r0.choose 2).choose 2 +
            e ^ e * (4 + 5 * (r0.choose 2).choose 2)))) ≤ 2 ^ (2 ^ (B + 11)) ∧
    r0 * (1 + 2 * r0) + 2 ≤ 4 * P ^ 2 := by
  have h16_P : 16 ≤ P :=
    hP ▸ (by decide : 16 ≤ 2 ^ 16).trans (Nat.pow_le_pow_right (by decide) h16)
  have hT_pos : 1 ≤ T := hT ▸ Nat.one_le_two_pow
  have hPT : P ≤ T := hP ▸ hT ▸ Nat.pow_le_pow_right (by decide)
    ((by omega : A ≤ B).trans Nat.lt_two_pow_self.le)
  obtain ⟨hp1, hp2, hp3⟩ := dtArith_poly_helper h16_P hPT hT_pos hr0 he hmE hmD hee hs2d
  have hp2' := (Nat.mul_le_mul_left ((r0.choose 2).choose 2 + 1)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hsk) (2 * 2 ^ (r0.choose 2).choose 2 + 1))).trans
    hp2
  have hP3 : P ^ 3 ≤ 2 ^ (2 * B) := by
    have h2 : P ^ 2 = 2 ^ B := by rw [sq, hP, ← Nat.pow_add, show A + A = B by omega]
    have h3 : P ≤ 2 ^ B := hP ▸ Nat.pow_le_pow_right (by decide) (by omega)
    rw [show P ^ 3 = P ^ 2 * P by ring]
    exact (Nat.mul_le_mul h2.le h3).trans_eq (by rw [← Nat.pow_add, two_mul])
  have h1 := (Nat.mul_le_mul_left 21 hP3).trans (Nat.le_mul_of_pos_right _ hT_pos)
  have h2 := Nat.mul_le_mul_right T (Nat.mul_le_mul_left 26 hP3)
  have h47_sum : 47 * 2 ^ (2 * B) * T = 21 * 2 ^ (2 * B) * T + 26 * 2 ^ (2 * B) * T := by ring
  have htot := (Nat.add_le_add hp1 hp2').trans ((Nat.add_le_add h1 h2).trans_eq h47_sum.symm)
  have h47 : 47 * 2 ^ (2 * B) * T ≤ 2 ^ (2 ^ (B + 11)) := by
    have : 2 ^ (2 * B + 6) = 2 ^ (2 * B) * 64 := by rw [Nat.pow_add]
    have hm := (Nat.mul_le_mul_right T (by omega : 47 * 2 ^ (2 * B) ≤ 2 ^ (2 * B + 6))).trans_eq
      (by rw [hT, Nat.mul_comm, ← Nat.pow_add])
    have h1 : B ≤ 2 ^ B := Nat.lt_two_pow_self.le
    have h2 : 2 ^ (B + 11) = 2 ^ B * 2048 := by rw [Nat.pow_add]
    exact hm.trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨by simpa only [Nat.add_assoc] using htot.trans h47, hp3⟩

private theorem dtPrecompCost_tot_helper {r0 mE K x : ℕ} (hr2 : 2 ≤ r0)
    (hmE : 2 ^ mE ≤ 2 ^ (r0 ^ 4)) (hKlo : r0 ^ 4 + 1 ≤ K) (hKhi : K ≤ 2 * r0 ^ 4 + 11)
    (hx : x ≤ 2 ^ (2 ^ K)) : x + 2 ^ mE * 2 ^ (2 ^ K) ≤ dtPrecompCost r0 := by
  have hnot1 : ¬ (r0 ≤ 1) := by omega
  rw [show dtPrecompCost r0 = 2 ^ (2 ^ (4 * r0 ^ 4 + 16)) by
    simp only [dtPrecompCost, hnot1, ↓reduceIte]]
  have h1 : 1 + 2 ^ mE ≤ 2 ^ (r0 ^ 4 + 1) := by
    rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := r0 ^ 4); omega
  have hmul : (1 + 2 ^ mE) * 2 ^ (2 ^ K) ≤ 2 ^ (2 ^ K + r0 ^ 4 + 1) :=
    (Nat.mul_le_mul_right _ h1).trans_eq (by rw [Nat.mul_comm, ← Nat.pow_add, add_assoc])
  have hexp : 2 ^ K + r0 ^ 4 + 1 ≤ 2 ^ (4 * r0 ^ 4 + 16) := by
    have h1 := (Nat.pow_add 2 K (4 * r0 ^ 4 + 16 - K)).symm.trans
      (by rw [Nat.add_sub_of_le (by omega)])
    have h2 : 2 ≤ 2 ^ (4 * r0 ^ 4 + 16 - K) :=
      (by decide : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
    have h3 : r0 ^ 4 + 1 ≤ 2 ^ K := hKlo.trans Nat.lt_two_pow_self.le
    exact (by omega : 2 ^ K + r0 ^ 4 + 1 ≤ 2 ^ K * 2).trans
      ((Nat.mul_le_mul_left (2 ^ K) h2).trans h1.le)
  exact ((Nat.add_le_add_right hx _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])).trans
    (hmul.trans (Nat.pow_le_pow_right (by decide) hexp))

private theorem dtPrecompArithBounds {r0 e : ℕ} (hr2 : 2 ≤ r0) (he : e ≤ r0.choose 2) :
    let maxE := r0.choose 2; let maxD := maxE.choose 2; let numMasks := 2 ^ maxE
    let wsSz := 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1
    (e ^ e + (2 + e + 2 * (2 ^ maxD - 1) + 2 ^ maxD) ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 5))) ∧
    (e ^ e + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 5))) ∧
    ((e.choose 2) ^ (2 ^ maxD - 1) + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 11))) ∧
    (5 * maxE + (1 + 2 * e) + (3 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) +
      e * (1 + 2 * e) + (maxD + 1) * (2 * 2 ^ maxD + 1 + (e.choose 2) ^ (2 ^ maxD - 1) *
        (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD)))) ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 11))) ∧
    (5 * maxE + 9 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 11))) ∧ (1 ≤ maxE) ∧
    (numMasks + wsSz + numMasks * 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) ≤ dtPrecompCost r0) ∧
    (r0 * (1 + 2 * r0) + numMasks * 2 ^ (2 ^ (2 * r0 ^ 4 + 11)) + 2 ≤ dtPrecompCost r0) := by
  dsimp only
  have hc2 : ∀ n : ℕ, n.choose 2 ≤ n ^ 2 := fun n => by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ 2).trans
      ((Nat.mul_le_mul_left _ (Nat.sub_le _ 1)).trans_eq (sq n).symm)
  have h16 : 16 ≤ r0 ^ 4 := (by decide : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hr2 4)
  have h16_P : 16 ≤ 2 ^ (r0 ^ 4) :=
    (by decide : 16 ≤ 2 ^ 16).trans (Nat.pow_le_pow_right (by decide) h16)
  have hr0_sq : r0 ^ 2 ≤ r0 ^ 4 := (by nlinarith : r0 ^ 2 ≤ r0 ^ 2 * r0 ^ 2).trans_eq (by ring)
  have hmaxE_pos : 1 ≤ r0.choose 2 := Nat.choose_pos hr2
  have hmaxE_le : r0.choose 2 ≤ r0 ^ 2 := hc2 r0
  have he_sq_A : e ^ 2 ≤ r0 ^ 4 := (Nat.pow_le_pow_left (he.trans hmaxE_le) 2).trans_eq (by ring)
  have hmaxD_le : (r0.choose 2).choose 2 ≤ r0 ^ 4 :=
    (hc2 _).trans ((Nat.pow_le_pow_left hmaxE_le 2).trans_eq (by ring))
  have hr0_P : r0 ≤ 2 ^ (r0 ^ 4) :=
    (by nlinarith : r0 ≤ r0 ^ 2).trans (hr0_sq.trans Nat.lt_two_pow_self.le)
  have he_P : e ≤ 2 ^ (r0 ^ 4) := ((he.trans hmaxE_le).trans hr0_sq).trans Nat.lt_two_pow_self.le
  have hmaxE_P : r0.choose 2 ≤ 2 ^ (r0 ^ 4) := (hmaxE_le.trans hr0_sq).trans Nat.lt_two_pow_self.le
  have hmaxD_P : (r0.choose 2).choose 2 ≤ 2 ^ (r0 ^ 4) := hmaxD_le.trans Nat.lt_two_pow_self.le
  have hee_P : e ^ e ≤ 2 ^ (r0 ^ 4) :=
    ((Nat.pow_le_pow_left Nat.lt_two_pow_self.le e).trans_eq
      (by rw [← Nat.pow_mul, sq])).trans (Nat.pow_le_pow_right (by decide) he_sq_A)
  have h2d_P : 2 ^ (r0.choose 2).choose 2 ≤ 2 ^ (r0 ^ 4) :=
    Nat.pow_le_pow_right (by decide) hmaxD_le
  have h2e_P : 2 ^ r0.choose 2 ≤ 2 ^ (r0 ^ 4) :=
    Nat.pow_le_pow_right (by decide) (hmaxE_le.trans hr0_sq)
  have hsk : (e.choose 2) ^ (2 ^ (r0.choose 2).choose 2 - 1) ≤ 2 ^ (2 ^ (2 * r0 ^ 4)) := by
    have hb := ((Nat.choose_le_choose 2 he).trans hmaxD_le).trans Nat.lt_two_pow_self.le
    calc (e.choose 2) ^ (2 ^ (r0.choose 2).choose 2 - 1)
        ≤ (2 ^ (r0 ^ 4)) ^ (2 ^ (r0.choose 2).choose 2 - 1) := Nat.pow_le_pow_left hb _
      _ ≤ (2 ^ (r0 ^ 4)) ^ (2 ^ (r0 ^ 4)) :=
          Nat.pow_le_pow_right Nat.one_le_two_pow ((Nat.sub_le _ 1).trans h2d_P)
      _ ≤ 2 ^ (2 ^ (r0 ^ 4) * 2 ^ (r0 ^ 4)) := by
          rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide)
            (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le)
      _ = 2 ^ (2 ^ (2 * r0 ^ 4)) := by rw [← Nat.pow_add, two_mul]
  obtain ⟨hbig, hr0_bd⟩ := dtPrecompArithBounds_core h16 rfl rfl rfl
    hr0_P he_P hmaxE_P hmaxD_P hee_P h2d_P hsk
  have h8 : 2 ^ (r0 ^ 4 + 3) = 2 ^ (r0 ^ 4) * 8 := by rw [Nat.pow_add]
  have hfr : e ^ e + (2 + e + 2 * (2 ^ (r0.choose 2).choose 2 - 1) + 2 ^ (r0.choose 2).choose 2) ≤
      2 ^ (2 ^ (2 * r0 ^ 4 + 5)) := (by omega : _ ≤ 2 ^ (r0 ^ 4 + 3)).trans
    (Nat.pow_le_pow_right (by decide)
      ((by omega : r0 ^ 4 + 3 ≤ 2 * r0 ^ 4 + 5).trans Nat.lt_two_pow_self.le))
  have hee_le : e ^ e + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) :=
    (by have := Nat.one_le_two_pow (n := (r0.choose 2).choose 2); omega : e ^ e + 1 ≤ _).trans hfr
  have hns_le : (e.choose 2) ^ (2 ^ (r0.choose 2).choose 2 - 1) + 1 ≤
      2 ^ (2 ^ (2 * r0 ^ 4 + 11)) := by
    have hp := (Nat.add_le_add_right hsk 1).trans
      (Nat.add_le_add_left (Nat.one_le_two_pow : 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4))) _)
    have h2 : 2 ^ (2 * r0 ^ 4 + 11) = 2 ^ (2 * r0 ^ 4) * 2048 := by rw [Nat.pow_add]
    have := Nat.one_le_two_pow (n := 2 * r0 ^ 4)
    exact hp.trans ((by rw [← two_mul, mul_comm, ← Nat.pow_succ] :
      _ ≤ 2 ^ (2 ^ (2 * r0 ^ 4) + 1)).trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have htriv : 5 * r0.choose 2 + 9 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 11)) :=
    (by omega : _ ≤ 2 ^ (r0 ^ 4 + 3)).trans (Nat.pow_le_pow_right (by decide)
      ((by omega : r0 ^ 4 + 3 ≤ 2 * r0 ^ 4 + 11).trans Nat.lt_two_pow_self.le))
  have htot1 := dtPrecompCost_tot_helper hr2 h2e_P (by omega) (by omega)
    (show 2 ^ r0.choose 2 + (9 * r0.choose 2 + 2 * (r0.choose 2).choose 2 +
        3 * 2 ^ (r0.choose 2).choose 2 + r0 + 1) ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) by
      have : 2 ^ (r0 ^ 4 + 5) = 2 ^ (r0 ^ 4) * 32 := by rw [Nat.pow_add]
      exact (by omega : _ ≤ 2 ^ (r0 ^ 4 + 5)).trans (Nat.pow_le_pow_right (by decide)
        ((by omega : r0 ^ 4 + 5 ≤ 2 * r0 ^ 4 + 5).trans Nat.lt_two_pow_self.le)))
  have htot2 := dtPrecompCost_tot_helper hr2 h2e_P (by omega) (by omega)
    (show r0 * (1 + 2 * r0) + 2 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 11)) by
      have : 2 ^ (2 * r0 ^ 4 + 2) = 2 ^ (2 * r0 ^ 4) * 4 := by rw [Nat.pow_add]
      have hP2 : (2 ^ (r0 ^ 4)) ^ 2 = 2 ^ (2 * r0 ^ 4) := by rw [← Nat.pow_mul, Nat.mul_comm]
      exact (hP2 ▸ hr0_bd).trans ((by omega : 4 * 2 ^ (2 * r0 ^ 4) ≤ 2 ^ (2 * r0 ^ 4 + 2)).trans
        (Nat.pow_le_pow_right (by decide)
          ((by omega : 2 * r0 ^ 4 + 2 ≤ 2 * r0 ^ 4 + 11).trans Nat.lt_two_pow_self.le))))
  exact ⟨hfr, hee_le, hns_le, hbig, htriv, hmaxE_pos, htot1, by omega⟩

/-! ## Section 3: Skeleton Search, Permutation Table, Depth Search, and `precomputeDTProg` -/

private def dtSearchSkelStep (x : DTSkelEnv × DTSkelState) : Memory.Prog DTSkelState := do
  let _ ← Memory.read x.1.env.bufA.tableBase
  let ok ← dtTestSkelProg
    (⟨x.1.env, x.1.e, x.1.d, x.1.pow2d, x.1.numPairs, x.1.permAns, x.2.skelCode⟩, x.1.powE)
  if ok = 1 then dtWriteFoundEntry (x.1, x.2.skelCode); pure ⟨x.2.skelCode, 1, 0⟩
  else if x.2.skelCode + 1 < x.1.numSkels then pure ⟨x.2.skelCode + 1, 0, 1⟩
  else pure ⟨x.2.skelCode, 0, 0⟩

private def dtSearchSkelStepSafe (w : ℕ) (x : DTSkelEnv × DTSkelState)
    (s : Memory.State) : Prop :=
  let tArgs : DTCheckPermEnv × ℕ :=
    (⟨x.1.env, x.1.e, x.1.d, x.1.pow2d, x.1.numPairs, x.1.permAns, x.2.skelCode⟩, x.1.powE)
  let ok := (Memory.spec 0).clientResult s (dtTestSkelProg tArgs)
  let s1 := (Memory.spec 0).clientState s (dtTestSkelProg tArgs)
  Fits w 2 ∧ Fits w (x.2.skelCode + 1) ∧ x.1.env.bufA.tableBase < s.frontier ∧
  dtTestSkelProgSafe w tArgs s ∧
  (ok = 1 → dtWriteFoundEntrySafe w (x.1, x.2.skelCode) s1)

private theorem realizes_dtSearchSkelStep : Realizes .exact
    dtSearchSkelStep (appendWords dtSkelEnvWords dtSkelStateWords)
    dtSkelStateWords dtSearchSkelStepSafe (fun _ _ => 0) := by
  unfold dtSearchSkelStep
  realize [realizes_dtTestSkelProg, realizes_dtWriteFoundEntry]
  all_goals
    obtain ⟨h2, hsc, htb, htest, hwr⟩ := h
    have hfront := hmem.frontier_fits
    first | exact htest | exact hwr hc | omega | fits

private theorem dtSearchSkel_spec {w baseFront mask e d permAns : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s) (hlay : DTEnvLayout env baseFront)
    (hbf : baseFront ≤ permAns) (hpa_lt : permAns + e ^ e ≤ s.frontier) (he2 : 2 ≤ e)
    (he_le : e ≤ env.maxE) (he_eq : e = (maskEdgePairs env.r0 mask).length) (hd_le : d ≤ env.maxD)
    (hmask : mask < env.numMasks) (_hfit_nm : Fits w env.numMasks) (hfit_ee : Fits w (e ^ e + 1))
    (hfit_ns : Fits w ((e.choose 2) ^ (2 ^ d - 1) + 1))
    (hfit_fr : Fits w (s.frontier + (2 + e + 2 * (2 ^ d - 1) + 2 ^ d)))
    (hpows : ∀ k ≤ 2 ^ d - 1, s.mem (env.bufC.powSkelArr + k) = (e.choose 2) ^ k)
    (hm_in : DTMaskIn env he_eq permAns (by omega) s) :
    let numSkels := (e.choose 2) ^ (2 ^ d - 1)
    let sEnv : DTSkelEnv := ⟨env, mask, e, d, 2 ^ d, e.choose 2, permAns, e ^ e, numSkels⟩
    let S := {env.bufA.tableBase + mask} ∪ Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ d) ∪
      Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ d) ∪ {a | s.frontier ≤ a}
    whileSafe (fun (_ : DTSkelEnv) (st : DTSkelState) => st.cont ≠ 0)
      dtSearchSkelStep dtSearchSkelStepSafe w sEnv numSkels ⟨0, 0, 1⟩ s ∧
    Memory.FramedTriple w s (boundedWhile (fun (_ : DTSkelEnv) (st : DTSkelState) => st.cont ≠ 0)
      dtSearchSkelStep sEnv numSkels ⟨0, 0, 1⟩)
      (numSkels * (5 + 2 * e + 9 * 2 ^ d + e ^ e * (4 + 5 * d))) S
      fun res s' => (res.found = 0 ∨ res.found = 1) ∧ Memory.WellFormed w s' ∧
        (res.found = 0 → s'.frontier = s.frontier ∧ d < optDepth (endsOfMask env.r0 mask)) ∧
        (res.found = 1 → s'.frontier = s.frontier + (2 + e + 2 * (2 ^ d - 1) + 2 ^ d) ∧
          DTMaskEntryValid env.r0 env.bufA.tableBase mask d s' ∧
          s.frontier ≤ s'.mem (env.bufA.tableBase + mask)) := by
  have hr2 := hlay.r0_ge; have hmaxE := hlay.2.1; have hnm := hlay.2.2.1; have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9, hbb10,
    hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  have h2d_pos : 1 ≤ 2 ^ d := Nat.two_pow_pos d; have he_le_ee := (dtPow_le_self_bounds he2).1
  have h2d_le : 2 ^ d ≤ 2 ^ env.maxD := Nat.pow_le_pow_right (by decide) hd_le
  have hnp_le : e.choose 2 ≤ env.maxD := hmaxD ▸ Nat.choose_le_choose 2 he_le
  have hns_pos : 1 ≤ (e.choose 2) ^ (2 ^ d - 1) := Nat.pow_pos (Nat.choose_pos he2)
  let numSkels := (e.choose 2) ^ (2 ^ d - 1)
  let sEnv : DTSkelEnv := ⟨env, mask, e, d, 2 ^ d, e.choose 2, permAns, e ^ e, numSkels⟩
  let Stest := Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ d) ∪
    Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ d)
  let S := {env.bufA.tableBase + mask} ∪ Stest ∪ {a | s.frontier ≤ a}
  let C_step := 5 + 2 * e + 9 * 2 ^ d + e ^ e * (4 + 5 * d)
  let I (st : DTSkelState) (t : Memory.State) : Prop :=
    (st.found = 0 ∨ st.found = 1) ∧ Memory.WellFormed w t ∧
    (st.cont ≠ 0 → st.found = 0 ∧ st.skelCode < numSkels ∧ t.frontier = s.frontier ∧
      (∀ k ≤ 2 ^ d - 1, t.mem (env.bufC.powSkelArr + k) = (e.choose 2) ^ k) ∧
      DTMaskIn env he_eq permAns (by omega) t ∧
      (∀ sc < st.skelCode, ¬dtSkelCompat he2 mask he_eq sc d)) ∧
    (st.cont = 0 →
      (st.found = 0 → t.frontier = s.frontier ∧ d < optDepth (endsOfMask env.r0 mask)) ∧
      (st.found = 1 → t.frontier = s.frontier + (2 + e + 2 * (2 ^ d - 1) + 2 ^ d) ∧
        DTMaskEntryValid env.r0 env.bufA.tableBase mask d t ∧
        s.frontier ≤ t.mem (env.bufA.tableBase + mask)))
  let rank (st : DTSkelState) (_ : Memory.State) : ℕ :=
    if st.cont = 0 then 0 else numSkels - st.skelCode
  have hzero : ∀ st t, I st t → rank st t = 0 → ¬(st.cont ≠ 0) := fun st _ hi hr hc => by
    have hsc := (hi.2.2.1 hc).2.1; dsimp only [rank] at hr; simp only [hc, ↓reduceIte] at hr; omega
  have hsub_test : Stest ⊆ S := fun a ha => by simp only [Stest, S, Set.mem_union] at ha ⊢; tauto
  have hnot_Stest : ∀ a, (env.bufC.powSkelArr ≤ a ∧ a < env.bufC.powSkelArr + 2 ^ d) ∨
      (env.bufC.powEArr ≤ a ∧ a < env.bufC.powEArr + (e + 1)) ∨
      (env.bufB.allPairA ≤ a ∧ a < env.bufB.allPairA + e.choose 2) ∨
      (env.bufB.allPairB ≤ a ∧ a < env.bufB.allPairB + e.choose 2) ∨
      (env.bufA.edgePair ≤ a ∧ a < env.bufA.edgePair + e) ∨ (permAns ≤ a ∧ a < permAns + e ^ e) →
      a ∉ Stest := fun a ha => by simp only [Stest, Set.mem_union, Set.mem_Ico]; omega
  have hstep : ∀ st t, I st t → st.cont ≠ 0 → dtSearchSkelStepSafe w (sEnv, st) t ∧
      Memory.FramedTriple w t (dtSearchSkelStep (sEnv, st)) C_step S
        fun a' t' => I a' t' ∧ rank a' t' < rank st t := by
    intro st t ⟨_, hwt, hrun, _⟩ hc
    obtain ⟨_, hsc_lt, htfr, hpows_t, hmin_t, hnone⟩ := hrun hc
    obtain ⟨hts_safe, hts_tri⟩ := dtTestSkelProg_spec (w := w) (baseFront := baseFront)
      (mask := mask) (e := e) (d := d) (permAns := permAns) (skelCode := st.skelCode)
      h2 hwt hlay hbf (by omega) he2 he_le he_eq hd_le hfit_ee hpows_t hmin_t
    let cArgs : DTCheckPermEnv × ℕ := (⟨env, e, d, 2 ^ d, e.choose 2, permAns, st.skelCode⟩, e ^ e)
    let ok1 := (Memory.spec 0).clientResult t (dtTestSkelProg cArgs)
    let s1 := (Memory.spec 0).clientState t (dtTestSkelProg cArgs)
    obtain ⟨_, _, hts_mod, _, hts_fr, hts_wf, hts_llt, hts_good, hts_comp⟩ :=
      framedTriple_iff_realization.mp hts_tri
    have hp1 : ∀ k ≤ 2 ^ d - 1, s1.mem (env.bufC.powSkelArr + k) = (e.choose 2) ^ k := fun k hk =>
      (hts_mod.mem_eq_of_not_mem (by omega) (hnot_Stest _ (.inl ⟨by omega, by omega⟩))).trans
        (hpows_t k hk)
    have hm1 : DTMaskIn env he_eq permAns (by omega) s1 := dtMaskIn_of_modifies hmin_t hts_mod
      (by omega) (by omega) (by omega) (by omega) (by omega) fun a ha => hnot_Stest a (.inr ha)
    have hbr_safe_tri : (ok1 = 1 → dtWriteFoundEntrySafe w (sEnv, st.skelCode) s1) ∧
        Memory.FramedTriple w s1 (if ok1 = 1 then
            dtWriteFoundEntry (sEnv, st.skelCode) >>= fun _ => pure ⟨st.skelCode, 1, 0⟩
          else if st.skelCode + 1 < numSkels then pure ⟨st.skelCode + 1, 0, 1⟩
          else pure ⟨st.skelCode, 0, 0⟩) (4 + 2 * e + 7 * 2 ^ d) S
          fun a' t' => I a' t' ∧ rank a' t' < rank st t := by
      by_cases hok1 : ok1 = 1
      · simp only [hok1, ↓reduceIte]
        obtain ⟨hwr_safe, hwr_tri⟩ := dtWriteFoundEntry_spec (w := w) (baseFront := baseFront)
          (mask := mask) (e := e) (d := d) (permAns := permAns) (powE := e ^ e)
          (numSkels := numSkels) (skelCode := st.skelCode) (env := env) (s := s1) h2 hts_wf hlay
          (by rw [hts_fr, htfr]; omega) he2 he_le he_eq hd_le hmask
          (by rw [hts_fr, htfr]; exact hfit_fr)
          (fun k hk => hp1 k hk.le) hm1.2.1 hm1.2.2.1 hts_llt (hts_good hok1)
        refine ⟨fun _ => hwr_safe, framedTriple_bind_client hwr_tri (fun a ha => by
            simp only [S, Stest, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ico,
              Set.mem_ofPred_eq] at ha ⊢
            rcases ha with rfl | ⟨hle, _⟩ <;> [exact Or.inl (Or.inl rfl);
              exact Or.inr (by rw [hts_fr, htfr] at hle; exact hle)])
          Set.Subset.rfl (c₂ := 0) le_rfl fun ⟨hs2_fr, hs2_wf, hs2_val, hs2_ptr⟩ _ =>
            Memory.FramedTriple.pure ⟨⟨.inr rfl, hs2_wf, fun hc' => absurd rfl hc', fun _ =>
              ⟨fun h0 => absurd h0 Nat.one_ne_zero, fun _ =>
                ⟨by rw [hs2_fr, hts_fr, htfr], hs2_val, by rw [hs2_ptr, hts_fr, htfr]⟩⟩⟩,
              by dsimp only [rank]; simp only [hc, ↓reduceIte]; omega⟩⟩
      · simp only [hok1, ↓reduceIte]
        have hbad : ¬dtSkelCompat he2 mask he_eq st.skelCode d := fun h => hok1 (hts_comp h)
        refine ⟨False.elim, ?_⟩
        by_cases hnext : st.skelCode + 1 < numSkels <;> simp only [hnext, ↓reduceIte]
        · exact Memory.FramedTriple.pure ⟨⟨.inl rfl, hts_wf, fun _ => ⟨rfl, hnext,
              hts_fr.trans htfr, hp1, hm1, fun sc hsc => if heq : sc = st.skelCode then
                heq ▸ hbad else hnone sc (by dsimp only at hsc; omega)⟩,
            fun hc' => absurd hc' Nat.one_ne_zero⟩,
            by dsimp only [rank]; simp only [hc, Nat.one_ne_zero, ↓reduceIte]; omega⟩
        · have hlt_opt : d < optDepth (endsOfMask env.r0 mask) := by
            by_contra hge; obtain ⟨sc, _, hcompat⟩ := dtExistsGoodSkel he2 he_eq
              (Nat.le_of_not_lt hge)
            exact if heq : sc = st.skelCode then hbad (heq ▸ hcompat)
              else hnone sc (by omega) hcompat
          exact Memory.FramedTriple.pure ⟨⟨.inl rfl, hts_wf, fun hc' => absurd rfl hc', fun _ =>
              ⟨fun _ => ⟨hts_fr.trans htfr, hlt_opt⟩, fun h1 => absurd h1 Nat.zero_ne_one⟩⟩,
            by dsimp only [rank]; simp only [hc, ↓reduceIte]; omega⟩
    exact ⟨⟨h2, hfit_ns.of_le (by dsimp only [sEnv]; omega), by dsimp only [sEnv]; rw [htfr]; omega,
        hts_safe, fun hok => hbr_safe_tri.1 hok⟩, by
      dsimp only [dtSearchSkelStep, sEnv]
      exact Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := 2 * 2 ^ d + e ^ e *
          (4 + 5 * d) + (4 + 2 * e + 7 * 2 ^ d)) (by rw [htfr]; omega) (framedTriple_bind_client
        hts_tri hsub_test Set.Subset.rfl le_rfl fun _ _ => hbr_safe_tri.2))
        (by dsimp only [C_step]; omega) fun _ _ h => h⟩
  have hinit : I ⟨0, 0, 1⟩ s := ⟨.inl rfl, hwf, fun _ => ⟨rfl, hns_pos, rfl, hpows, hm_in,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun hc => absurd hc Nat.one_ne_zero⟩
  obtain ⟨hsafe, htri⟩ := boundedWhile_framedTriple_spec (fun (_ : DTSkelEnv) (st : DTSkelState) =>
      st.cont ≠ 0) dtSearchSkelStep dtSearchSkelStepSafe hzero hstep hinit (fuel := numSkels)
    (by dsimp only [rank]; simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_zero, le_rfl])
  refine ⟨hsafe, ?_⟩
  dsimp only [sEnv, numSkels, S, Stest, C_step, rank] at htri ⊢
  refine Memory.FramedTriple.frame_mono (htri.mono
    (by simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_zero]; rw [Nat.mul_comm])
    fun _ _ ⟨hnc, h01, hwf', _, hdone⟩ => ⟨h01, hwf', hdone (by omega)⟩)
    fun a ha => by simp only [Set.mem_union] at ha ⊢; tauto

private def dtDecodePermStep (x : DTDecodePermEnv × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let pw ← Memory.read (x.1.powEArr + x.2.1)
  let d := (x.1.code / pw) % x.1.e
  let s ← Memory.read (x.1.seenArr + d)
  Memory.write (x.1.rankArr + x.2.1) d; Memory.write (x.1.orderArr + d) x.2.1
  Memory.write (x.1.seenArr + d) 1
  if s = 1 then pure (x.2.1 + 1, 0) else pure (x.2.1 + 1, x.2.2)

private def dtDecodePermStepSafe (w : ℕ) (x : DTDecodePermEnv × (ℕ × ℕ))
    (s : Memory.State) : Prop :=
  Fits w 2 ∧ 1 ≤ x.1.e ∧ Fits w (x.2.1 + 1) ∧ s.mem (x.1.powEArr + x.2.1) ≠ 0 ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtDecodePermStep x))

private theorem realizes_dtDecodePermStep : Realizes .exact
    dtDecodePermStep (appendWords dtDecodePermEnvWords WordEncoding.encode)
    WordEncoding.encode dtDecodePermStepSafe (fun _ _ => 0) := by
  unfold dtDecodePermStep
  realize
  all_goals
    obtain ⟨h2, he, hidx, hnz, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtDecodePermStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
      Memory.valid] at hv
    first | exact hnz | omega | fits

private theorem dtDecodePerm_loop_spec {w e powEArr rankArr orderArr seenArr code : ℕ}
    {s : Memory.State} (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (he1 : 1 ≤ e) (he_fit : Fits w (e + 1))
    (hpe : powEArr + (e + 1) ≤ s.frontier) (hra : rankArr + e ≤ s.frontier)
    (hoa : orderArr + e ≤ s.frontier) (hsa : seenArr + e ≤ s.frontier)
    (hp_r : powEArr + (e + 1) ≤ rankArr ∨ rankArr + e ≤ powEArr)
    (hp_o : powEArr + (e + 1) ≤ orderArr ∨ orderArr + e ≤ powEArr)
    (hp_s : powEArr + (e + 1) ≤ seenArr ∨ seenArr + e ≤ powEArr)
    (hr_o : rankArr + e ≤ orderArr ∨ orderArr + e ≤ rankArr)
    (hr_s : rankArr + e ≤ seenArr ∨ seenArr + e ≤ rankArr)
    (ho_s : orderArr + e ≤ seenArr ∨ seenArr + e ≤ orderArr)
    (hpow : ∀ k ≤ e, s.mem (powEArr + k) = e ^ k)
    (hseen0 : ∀ d < e, s.mem (seenArr + d) = 0) :
    let env : DTDecodePermEnv := ⟨powEArr, rankArr, orderArr, seenArr, e, code⟩
    let S := Set.Ico rankArr (rankArr + e) ∪ Set.Ico orderArr (orderArr + e) ∪
      Set.Ico seenArr (seenArr + e)
    iterationSafe dtDecodePermStep dtDecodePermStepSafe w env e (0, 1) s ∧
    Memory.FramedTriple w s (iterate dtDecodePermStep env e (0, 1)) (6 * e) S fun res s' =>
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      (res.2 ≠ 0 ↔ CodeIsPerm e code) ∧
      (∀ hcp : CodeIsPerm e code, ∀ rk (hrk : rk < e),
        s'.mem (orderArr + rk) = ((permOfCode he1 code hcp).symm ⟨rk, hrk⟩).val) := by
  let env : DTDecodePermEnv := ⟨powEArr, rankArr, orderArr, seenArr, e, code⟩
  let S := Set.Ico rankArr (rankArr + e) ∪ Set.Ico orderArr (orderArr + e) ∪
    Set.Ico seenArr (seenArr + e)
  let dig (k : ℕ) := (code / e ^ k) % e
  let prefOk (k : ℕ) := ∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ → dig j₁ ≠ dig j₂
  let inv (k : ℕ) (st : ℕ × ℕ) (t : Memory.State) : Prop := st.1 = k ∧ t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧ Memory.Modifies S s t ∧
    (∀ d < e, t.mem (seenArr + d) = 1 ↔ ∃ j < k, dig j = d) ∧
    (∀ d < e, t.mem (seenArr + d) = 0 ∨ t.mem (seenArr + d) = 1) ∧
    (st.2 ≠ 0 ↔ prefOk k) ∧ (prefOk k → ∀ j < k, t.mem (orderArr + dig j) = j)
  have hstep : ∀ k < e, ∀ st t, inv k st t → dtDecodePermStepSafe w (env, st) t ∧
      Memory.FramedTriple w t (dtDecodePermStep (env, st)) 5 S (inv (k + 1)) := by
    intro k hk ⟨sidx, sacc⟩ t ⟨hidx, htfr, hwt, htmod, hseen_iff, hseen_01, hacc_iff, hord_k⟩
    dsimp only at hidx; subst sidx
    have hpow_k : t.mem (powEArr + k) = e ^ k := (htmod.mem_eq_of_not_mem (by omega) (by
      simp only [S, Set.mem_union, Set.mem_Ico]
      rcases hp_r with h | h <;> rcases hp_o with h1 | h1 <;>
        rcases hp_s with h2 | h2 <;> omega)).trans (hpow k hk.le)
    have hpow_nz : t.mem (powEArr + k) ≠ 0 := hpow_k ▸ Nat.ne_of_gt (Nat.pow_pos he1)
    have hdk_lt : dig k < e := Nat.mod_lt _ he1
    have htri_raw : Memory.FramedTriple w t (dtDecodePermStep (env, (k, sacc))) 5 S fun a' t' =>
        a' = (if t.mem (seenArr + dig k) = 1 then (k + 1, 0) else (k + 1, sacc)) ∧
        t'.frontier = s.frontier ∧ (∀ a < t.frontier, a ∉ S → t'.mem a = t.mem a) ∧
        t'.mem = Function.update (Function.update (Function.update t.mem (rankArr + k) (dig k))
          (orderArr + dig k) k) (seenArr + dig k) 1 := by
      dsimp only [dtDecodePermStep, env]; dsimp only [dig] at hdk_lt
      refine Memory.FramedTriple.read_bind (by omega) ?_; rw [hpow_k]
      refine Memory.FramedTriple.read_bind (by omega) (Memory.FramedTriple.write_bind_of_mem
        (by omega) (he_fit.of_le (by omega)) (.inl (.inl ⟨by omega, by omega⟩))
        (Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) (he_fit.of_le (by omega))
          (.inl (.inr ⟨by omega, by omega⟩)) (Memory.FramedTriple.write_bind_of_mem
            (by dsimp only; omega) (by fits) (.inr ⟨by omega, by omega⟩) ?_)))
      split_ifs <;> exact Memory.FramedTriple.pure ⟨rfl, htfr, fun a _ haS => by
        simp only [S, Set.mem_union, Set.mem_Ico] at haS; update_simp, rfl⟩
    have htri : Memory.FramedTriple w t (dtDecodePermStep (env, (k, sacc))) 5 S (inv (k + 1)) := by
      refine (htri_raw.wellFormed hwt).mono le_rfl fun a' t' ⟨⟨hres, ht'fr, ht'mod, ht'mem⟩,
          hwf'⟩ => ?_
      have hmem_s : ∀ d < e, t'.mem (seenArr + d) = if d = dig k then 1 else t.mem (seenArr + d) :=
        fun d hd => by
          rw [ht'mem]; by_cases hdd : d = dig k <;> simp only [hdd, ↓reduceIte]
          · exact Function.update_self ..
          · rw [Function.update_of_ne (by omega), Function.update_of_ne
                (by rcases ho_s with h | h <;> omega),
              Function.update_of_ne (by rcases hr_s with h | h <;> omega)]
      refine ⟨by rw [hres]; split_ifs <;> rfl, ht'fr, hwf', htmod.trans ⟨by omega, ht'mod⟩,
        fun d hd => by
          rw [hmem_s d hd]; by_cases hdd : d = dig k
          · simp only [hdd, ↓reduceIte, true_iff]; exact ⟨k, by omega, rfl⟩
          · simp only [hdd, ↓reduceIte, hseen_iff d hd]
            exact ⟨fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩, fun ⟨j, hj, h⟩ =>
              if hjk : j = k then absurd (hjk ▸ h).symm hdd else ⟨j, by omega, h⟩⟩,
        fun d hd => by rw [hmem_s d hd]; split_ifs <;> [exact .inr rfl; exact hseen_01 d hd],
        ?_, fun hok j hj => ?_⟩
      · rw [hres]; by_cases hseen1 : t.mem (seenArr + dig k) = 1
        · simp only [hseen1, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
          intro hok; obtain ⟨j, hj, hjd⟩ := (hseen_iff (dig k) hdk_lt).mp hseen1
          exact hok j (by omega) k (by omega) (by omega) hjd
        · simp only [hseen1, ↓reduceIte, hacc_iff]
          have hno : ¬ ∃ j < k, dig j = dig k := fun h => hseen1 ((hseen_iff _ hdk_lt).mpr h)
          exact ⟨fun hp j₁ hj₁ j₂ hj₂ hne => by
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj₁) with hj1 | rfl <;>
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj₂) with hj2 | rfl
              · exact hp j₁ hj1 j₂ hj2 hne
              · exact fun h => hno ⟨j₁, hj1, h⟩
              · exact fun h => hno ⟨j₂, hj2, h.symm⟩
              · exact absurd rfl hne, fun hp _ hj₁ _ hj₂ => hp _ (by omega) _ (by omega)⟩
      · rw [ht'mem]; by_cases hjk : j < k
        · have hne : dig j ≠ dig k := hok j (by omega) k (by omega) (by omega)
          have hdj_lt : dig j < e := Nat.mod_lt _ he1
          rw [Function.update_of_ne (by rcases ho_s with h | h <;> omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by rcases hr_o with h | h <;> omega)]
          exact hord_k (fun _ hj₁ _ hj₂ => hok _ (by omega) _ (by omega)) j hjk
        · rw [show j = k by omega, Function.update_of_ne (by rcases ho_s with h | h <;> omega),
            Function.update_self]
    exact ⟨⟨h2, he1, he_fit.of_le (by dsimp only; omega), hpow_nz,
      (framedTriple_iff_realization.mp htri).1⟩, htri⟩
  obtain ⟨hsafe, hv, hc, hmod, _, hfr, hwf', _, _, _, hacc, hord⟩ := iterate_potential_spec
    dtDecodePermStep dtDecodePermStepSafe w env 5 e inv (fun _ _ _ => 0) S
    (fun k hk a s ha => let ⟨hs', ht'⟩ := hstep k hk a s ha
      let ⟨hv', hc', hm', hi'⟩ := framedTriple_iff_realization.mp ht'
      ⟨hs', hv', by omega, hm', hi'⟩) (0, 1) s ⟨rfl, rfl, hwf, Memory.Modifies.refl S s,
      fun d hd => ⟨fun h => by rw [hseen0 d hd] at h; omega, fun ⟨_, hj, _⟩ => by omega⟩,
      fun d hd => .inl (hseen0 d hd), by simp [prefOk], fun _ _ hj => by omega⟩
  refine ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv, (by
      rw [Nat.add_zero, Nat.zero_add] at hc
      exact hc.trans (Nat.mul_le_mul_right e (by decide))),
    hmod, hfr, hwf', hacc, fun hcp rk hrk => by
    have hdig : dig ((permOfCode he1 code hcp).symm ⟨rk, hrk⟩).val = rk := by
      simpa only [permOfCode_apply_val] using
        congrArg Fin.val ((permOfCode he1 code hcp).apply_symm_apply ⟨rk, hrk⟩)
    have hres := hord hcp _ ((permOfCode he1 code hcp).symm ⟨rk, hrk⟩).isLt
    rwa [hdig] at hres⟩⟩

private def dtPermAnsStep (x : (DTPrecompEnv × ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read x.1.1.bufC.powEArr
  let _ ← fillConstProg x.1.1.bufC.seenArr 0 x.1.2.1
  let ok ← iterate dtDecodePermStep
    ⟨x.1.1.bufC.powEArr, x.1.1.bufB.rankArr, x.1.1.bufB.orderArr,
      x.1.1.bufC.seenArr, x.1.2.1, x.2⟩ x.1.2.1 (0, 1)
  if ok.2 = 0 then
    Memory.write (x.1.2.2 + x.2) 0
    pure (x.2 + 1)
  else
    let m ← dtKruskalMaskProg ⟨x.1.1.r0, x.1.2.1, x.1.1.bufA.edgeU, x.1.1.bufA.edgeV,
      x.1.1.bufB.orderArr, x.1.1.bufC.compArr⟩
    Memory.write (x.1.2.2 + x.2) (m + 1); pure (x.2 + 1)

private def dtPermAnsStepSafe (w : ℕ) (x : (DTPrecompEnv × ℕ × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  let env := x.1.1; let e := x.1.2.1; let permAns := x.1.2.2
  let s1 := (Memory.spec 0).clientState s (fillConstProg env.bufC.seenArr 0 e)
  let dec := iterate dtDecodePermStep
    ⟨env.bufC.powEArr, env.bufB.rankArr, env.bufB.orderArr, env.bufC.seenArr, e, x.2⟩ e (0, 1)
  let ok := (Memory.spec 0).clientResult s1 dec
  let s2 := (Memory.spec 0).clientState s1 dec
  let kArgs : DTKruskalProgArgs := ⟨env.r0, e, env.bufA.edgeU, env.bufA.edgeV,
    env.bufB.orderArr, env.bufC.compArr⟩
  let m := (Memory.spec 0).clientResult s2 (dtKruskalMaskProg kArgs)
  Fits w 2 ∧ Fits w (x.2 + 1) ∧ Fits w (permAns + x.2) ∧
  env.bufC.powEArr < s.frontier ∧ env.bufC.seenArr + e ≤ s.frontier ∧
  permAns + x.2 < s2.frontier ∧
  iterationSafe dtDecodePermStep dtDecodePermStepSafe w
    ⟨env.bufC.powEArr, env.bufB.rankArr, env.bufB.orderArr, env.bufC.seenArr, e, x.2⟩ e (0, 1) s1 ∧
  (ok.2 ≠ 0 → dtKruskalMaskProgSafe w kArgs s2 ∧ Fits w (m + 1) ∧
    permAns + x.2 < ((Memory.spec 0).clientState s2 (dtKruskalMaskProg kArgs)).frontier)

private theorem realizes_dtPermAnsStep : Realizes .exact
    dtPermAnsStep (appendWords (appendWords dtPrecompEnvWords
      (appendWords wordWords wordWords)) WordEncoding.encode)
    WordEncoding.encode dtPermAnsStepSafe (fun _ _ => 0) := by
  unfold dtPermAnsStep
  realize [realizes_fillConstProg, realizes_dtDecodePermStep, realizes_dtKruskalMaskProg]
  all_goals
    obtain ⟨h2, hidx, hpa, hpe, hsa, hps2, hdec, hbr⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact hsa | exact iterationSafe_imp hdec (fun _ => rfl) (fun _ _ hs => hs)
    | exact (hbr hc).1 | exact (hbr hc).2.1 | fits

private theorem dtPermAns_loop_spec {w baseFront mask e permAns : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (hlay : DTEnvLayout env baseFront) (hbf : baseFront ≤ permAns)
    (he2 : 2 ≤ e) (he_le : e ≤ env.maxE) (he_eq : e = (maskEdgePairs env.r0 mask).length)
    (hpa_lt : permAns + e ^ e ≤ s.frontier) (hfit_ee : Fits w (e ^ e + 1))
    (hpow : ∀ j ≤ e, s.mem (env.bufC.powEArr + j) = e ^ j)
    (hends : ∀ j (hj : j < (maskEdgePairs env.r0 mask).length),
      s.mem (env.bufA.edgeU + j) = (maskEdgePairs env.r0 mask)[j].1.val ∧
      s.mem (env.bufA.edgeV + j) = (maskEdgePairs env.r0 mask)[j].2.val) :
    let S := Set.Ico env.bufB.rankArr (env.bufB.rankArr + env.maxE) ∪
      Set.Ico env.bufB.orderArr (env.bufB.orderArr + env.maxE) ∪
      Set.Ico env.bufC.seenArr (env.bufC.seenArr + env.maxE) ∪
      Set.Ico env.bufC.compArr (env.bufC.compArr + env.r0) ∪ Set.Ico permAns (permAns + e ^ e)
    iterationSafe dtPermAnsStep dtPermAnsStepSafe w (env, e, permAns) (e ^ e) 0 s ∧
    Memory.FramedTriple w s (iterate dtPermAnsStep (env, e, permAns) (e ^ e) 0)
      (e ^ e * (2 + 7 * e + env.r0 + e * (5 + 2 * env.r0))) S fun res s' =>
      res = e ^ e ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧ ∀ code < e ^ e,
        (s'.mem (permAns + code) = 0 ↔ ¬CodeIsPerm e code) ∧ ∀ hcp : CodeIsPerm e code,
          let σ := (Fin.castOrderIso he_eq).toEquiv
          let p' := σ.symm.trans ((permOfCode (by omega : 1 ≤ e) code hcp).trans σ)
          s'.mem (permAns + code) =
            maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask) p' Finset.univ) + 1 := by
  have hr2 := hlay.r0_ge; have hmaxE := hlay.2.1; have hnm := hlay.2.2.1; have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9, hbb10,
    hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  have he_le_ee := (dtPow_le_self_bounds he2).1; have h2e_le_ee := Nat.pow_le_pow_left he2 e
  have hfit_pa : Fits w (permAns + e ^ e) := hwf.frontier_fits.of_le hpa_lt
  have hfit_e1 : Fits w (e + 1) := hfit_ee.of_le (by omega)
  have hfit_2e : Fits w (2 ^ e) := hfit_ee.of_le (h2e_le_ee.trans (Nat.le_succ _))
  have hfit_r01 : Fits w (env.r0 + 1) := hwf.frontier_fits.of_le (by omega)
  let S_work := Set.Ico env.bufB.rankArr (env.bufB.rankArr + env.maxE) ∪
    Set.Ico env.bufB.orderArr (env.bufB.orderArr + env.maxE) ∪ Set.Ico env.bufC.seenArr
      (env.bufC.seenArr + env.maxE) ∪ Set.Ico env.bufC.compArr (env.bufC.compArr + env.r0)
  let S := S_work ∪ Set.Ico permAns (permAns + e ^ e)
  let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
  let ends : Fin e → Sym2 (Fin env.r0) := fun i => endsOfMask env.r0 mask (σ i)
  let C_step := 2 + 7 * e + env.r0 + e * (5 + 2 * env.r0)
  let invCore (k st : ℕ) (t : Memory.State) : Prop := st = k ∧ t.frontier = s.frontier ∧
    Memory.Modifies S s t ∧ ∀ code < k, ∀ (_ : code < e ^ e),
      (t.mem (permAns + code) = 0 ↔ ¬CodeIsPerm e code) ∧ ∀ hcp : CodeIsPerm e code,
        let p' := σ.symm.trans ((permOfCode (by omega : 1 ≤ e) code hcp).trans σ)
        t.mem (permAns + code) =
          maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask) p' Finset.univ) + 1
  let inv (k st : ℕ) (t : Memory.State) : Prop := invCore k st t ∧ Memory.WellFormed w t
  have hfc_sub_w : Set.Ico env.bufC.seenArr (env.bufC.seenArr + e) ⊆ S_work :=
    fun _ ha => .inl (.inr ⟨ha.1, ha.2.trans_le (by omega)⟩)
  have hdec_sub_w : (Set.Ico env.bufB.rankArr (env.bufB.rankArr + e) ∪
      Set.Ico env.bufB.orderArr (env.bufB.orderArr + e) ∪
      Set.Ico env.bufC.seenArr (env.bufC.seenArr + e)) ⊆ S_work := fun a ha => by
    simp only [S_work, Set.mem_union, Set.mem_Ico] at ha ⊢; omega
  have hkr_sub_w : Set.Ico env.bufC.compArr (env.bufC.compArr + env.r0) ⊆ S_work := fun _ => .inr
  have hstep : ∀ k < e ^ e, ∀ st t, inv k st t → dtPermAnsStepSafe w ((env, e, permAns), st) t ∧
      Memory.FramedTriple w t (dtPermAnsStep ((env, e, permAns), st)) C_step S (inv (k + 1)) := by
    intro k hk st t ⟨⟨hidx, htfr, htmod, hprev⟩, hwt⟩; subst st
    have hpow_t : ∀ j ≤ e, t.mem (env.bufC.powEArr + j) = e ^ j := fun j hj =>
      (htmod.mem_eq_of_not_mem (by omega)
        (by simp only [S, S_work, Set.mem_union, Set.mem_Ico]; omega)).trans (hpow j hj)
    have hends_t : ∀ j (hj : j < (maskEdgePairs env.r0 mask).length),
        t.mem (env.bufA.edgeU + j) = (maskEdgePairs env.r0 mask)[j].1.val ∧
        t.mem (env.bufA.edgeV + j) = (maskEdgePairs env.r0 mask)[j].2.val := fun j hj =>
      have : j < e := he_eq ▸ hj
      have hn : ∀ a, a = env.bufA.edgeU + j ∨ a = env.bufA.edgeV + j → a ∉ S := fun a ha => by
        simp only [S, S_work, Set.mem_union, Set.mem_Ico]; omega
      ⟨(htmod.mem_eq_of_not_mem (by omega) (hn _ (.inl rfl))).trans (hends j hj).1,
       (htmod.mem_eq_of_not_mem (by omega) (hn _ (.inr rfl))).trans (hends j hj).2⟩
    have hfc := fillConstProg_spec (w := w) (base := env.bufC.seenArr) (val := 0) (count := e)
      hwt (by fits) (hfit_e1.of_le (by omega)) (by rw [htfr]; omega)
    let s1 := (Memory.spec 0).clientState t (fillConstProg env.bufC.seenArr 0 e)
    obtain ⟨_, _, hfc_mod, hfc_fr, hfc_wf, hfc_arr⟩ := framedTriple_iff_realization.mp hfc
    have hpow_s1 : ∀ j ≤ e, s1.mem (env.bufC.powEArr + j) = e ^ j := fun j hj =>
      (hfc_mod.mem_eq_of_not_mem (by rw [htfr]; omega)
        (by simp only [Set.mem_Ico]; omega)).trans (hpow_t j hj)
    obtain ⟨hdec_safe, hdec_tri⟩ := dtDecodePerm_loop_spec (w := w) (e := e)
      (powEArr := env.bufC.powEArr) (rankArr := env.bufB.rankArr) (orderArr := env.bufB.orderArr)
      (seenArr := env.bufC.seenArr) (code := k) h2 hfc_wf (by omega) hfit_e1
      (by rw [hfc_fr, htfr]; omega) (by rw [hfc_fr, htfr]; omega) (by rw [hfc_fr, htfr]; omega)
      (by rw [hfc_fr, htfr]; omega) (by right; omega) (by right; omega) (by right; omega)
      (by left; omega) (by left; omega) (by left; omega) hpow_s1 hfc_arr
    let decEnv : DTDecodePermEnv := ⟨env.bufC.powEArr, env.bufB.rankArr, env.bufB.orderArr,
      env.bufC.seenArr, e, k⟩
    let ok := (Memory.spec 0).clientResult s1 (iterate dtDecodePermStep decEnv e (0, 1))
    let s2 := (Memory.spec 0).clientState s1 (iterate dtDecodePermStep decEnv e (0, 1))
    obtain ⟨_, _, hdec_mod, hdec_fr, hdec_wf, hdec_acc, hdec_ord⟩ :=
      framedTriple_iff_realization.mp hdec_tri
    have hs2_fr : s2.frontier = s.frontier := hdec_fr.trans (hfc_fr.trans htfr)
    have hts2_mod : Memory.Modifies S_work t s2 :=
      (hfc_mod.mono hfc_sub_w).trans (hdec_mod.mono hdec_sub_w)
    have hwr_perm : ∀ val u, u.frontier = s.frontier → Memory.WellFormed w u →
        Memory.Modifies S_work t u → Fits w val → ((val = 0 ↔ ¬CodeIsPerm e k) ∧ ∀ hcp, val =
          maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask)
            (σ.symm.trans ((permOfCode (by omega : 1 ≤ e) k hcp).trans σ)) Finset.univ) + 1) →
        Memory.FramedTriple w u (Memory.write (permAns + k) val >>= fun _ => pure (k + 1)) 1 S
          (inv (k + 1)) := fun val u hu_fr hu_wf hu_mod hval_fit hk_val =>
      Memory.FramedTriple.wellFormed hu_wf (Memory.FramedTriple.write_bind_of_mem
        (by rw [hu_fr]; omega) hval_fit (.inr ⟨by omega, by omega⟩) (Memory.FramedTriple.pure
          ⟨rfl, hu_fr, htmod.trans ((hu_mod.mono Set.subset_union_left).trans
            ⟨by dsimp only; omega, fun a _ h => by
              simp only [S_work, Set.mem_union, Set.mem_Ico] at h; dsimp only; update_simp⟩),
          fun code _ hc2 => if hck : code < k then by
            have := hu_mod.mem_eq_of_not_mem (a := permAns + code) (by rw [htfr]; omega)
              (by simp only [S_work, Set.mem_union, Set.mem_Ico]; omega)
            dsimp only; rw [Function.update_of_ne (by omega), this]; exact hprev code hck hc2
          else by
            have hce : code = k := by omega
            subst hce; dsimp only; update_simp; exact hk_val⟩))
    let kArgs : DTKruskalProgArgs :=
      ⟨env.r0, e, env.bufA.edgeU, env.bufA.edgeV, env.bufB.orderArr, env.bufC.compArr⟩
    have hbr_safe_tri : (ok.2 ≠ 0 → dtKruskalMaskProgSafe w kArgs s2 ∧
          Fits w ((Memory.spec 0).clientResult s2 (dtKruskalMaskProg kArgs) + 1) ∧
          permAns + k < ((Memory.spec 0).clientState s2 (dtKruskalMaskProg kArgs)).frontier) ∧
        Memory.FramedTriple w s2 (if ok.2 = 0 then
            Memory.write (permAns + k) 0 >>= fun _ => pure (k + 1)
          else dtKruskalMaskProg kArgs >>= fun m =>
            Memory.write (permAns + k) (m + 1) >>= fun _ => pure (k + 1))
          (1 + (env.r0 + e * (5 + 2 * env.r0))) S (inv (k + 1)) := by
      by_cases hok0 : ok.2 = 0
      · simp only [hok0, ↓reduceIte]
        have hncp : ¬CodeIsPerm e k := fun h => absurd hok0 (hdec_acc.mpr h)
        exact ⟨fun hnz => absurd rfl hnz, (hwr_perm 0 s2 hs2_fr hdec_wf hts2_mod (by fits)
          ⟨⟨fun _ => hncp, fun _ => rfl⟩, fun hcp => absurd hcp hncp⟩).mono
          (Nat.le_add_right _ _) fun _ _ h => h⟩
      · simp only [hok0, ↓reduceIte]
        have hcp : CodeIsPerm e k := hdec_acc.mp hok0
        have hend_s2 : ∀ i (hi : i < e),
            s2.mem (env.bufA.edgeU + i) = ((maskEdgePairs env.r0 mask)[i]'(he_eq ▸ hi)).1.val ∧
            s2.mem (env.bufA.edgeV + i) = ((maskEdgePairs env.r0 mask)[i]'(he_eq ▸ hi)).2.val :=
          fun i hi => have hn : ∀ a, a = env.bufA.edgeU + i ∨ a = env.bufA.edgeV + i → a ∉ S_work :=
            fun a ha => by simp only [S_work, Set.mem_union, Set.mem_Ico]; omega
          ⟨(hts2_mod.mem_eq_of_not_mem (by rw [htfr]; omega) (hn _ (.inl rfl))).trans
              (hends_t i (he_eq ▸ hi)).1,
           (hts2_mod.mem_eq_of_not_mem (by rw [htfr]; omega) (hn _ (.inr rfl))).trans
              (hends_t i (he_eq ▸ hi)).2⟩
        have hkr_safe : dtKruskalMaskProgSafe w kArgs s2 := by
          rw [dtKruskalMaskProgSafe_iff]; dsimp only [kArgs]
          exact ⟨h2, hfit_r01, hfit_e1, hfit_2e, by rw [hs2_fr]; omega, by rw [hs2_fr]; omega,
            by rw [hs2_fr]; omega, by rw [hs2_fr]; omega, by right; omega, by right; omega,
            by right; omega, fun rk hrk => by rw [hdec_ord hcp rk hrk]; exact
              ((permOfCode (by omega : 1 ≤ e) k hcp).symm ⟨rk, hrk⟩).isLt,
            fun i hi => by rw [(hend_s2 i hi).1, (hend_s2 i hi).2]; exact
              ⟨(maskEdgePairs env.r0 mask)[i].1.isLt, (maskEdgePairs env.r0 mask)[i].2.isLt⟩⟩
        have hkr_tri := dtKruskalMaskProg_spec hdec_wf hkr_safe
          (permOfCode (by omega : 1 ≤ e) k hcp) (fun rk hrk => hdec_ord hcp rk hrk) ends fun i =>
            ⟨(maskEdgePairs env.r0 mask)[(σ i).val].1, (maskEdgePairs env.r0 mask)[(σ i).val].2,
             rfl, by dsimp only [kArgs]; exact (hend_s2 i.val i.isLt).1,
             by dsimp only [kArgs]; exact (hend_s2 i.val i.isLt).2⟩
        dsimp only [kArgs] at hkr_tri
        obtain ⟨_, _, _, hm_eq, hs3_fr', _⟩ := framedTriple_iff_realization.mp hkr_tri
        have hm_fit : Fits w ((Memory.spec 0).clientResult s2 (dtKruskalMaskProg kArgs) + 1) :=
          hfit_ee.of_le (by
            dsimp only [kArgs] at hm_eq ⊢
            rw [hm_eq]; exact (maskOfFinset_lt _).trans_le (h2e_le_ee.trans (Nat.le_succ _)))
        refine ⟨fun _ => ⟨hkr_safe, hm_fit, by rw [hs3_fr', hs2_fr]; omega⟩,
          framedTriple_bind_client hkr_tri (hkr_sub_w.trans Set.subset_union_left) Set.Subset.rfl
            (Nat.add_comm _ 1).le fun ⟨hm_eq', hs3_fr, hs3_wf⟩ hs3_mod =>
          hwr_perm ((Memory.spec 0).clientResult s2 (dtKruskalMaskProg kArgs) + 1) _
            (hs3_fr.trans hs2_fr) hs3_wf (hts2_mod.trans (hs3_mod.mono hkr_sub_w)) hm_fit
            ⟨⟨fun h => by omega, fun h => absurd hcp h⟩, fun hcp' => by
              rw [show permOfCode (by omega : 1 ≤ e) k hcp' = permOfCode (by omega : 1 ≤ e) k hcp
                from by ext i; simp only [permOfCode_apply_val]]
              dsimp only [kArgs] at hm_eq' ⊢; rw [hm_eq', dtMaskOfFinset_msf_cast he_eq ends
                (endsOfMask env.r0 mask) (fun _ => rfl) (permOfCode (by omega : 1 ≤ e) k hcp)]⟩⟩
    exact ⟨⟨h2, hfit_ee.of_le (by dsimp only; omega), hfit_pa.of_le (by dsimp only; omega),
        by dsimp only; rw [htfr]; omega, by dsimp only; rw [htfr]; omega,
        by dsimp only; rw [hs2_fr]; omega, hdec_safe, by dsimp only; exact hbr_safe_tri.1⟩, by
      dsimp only [dtPermAnsStep]
      exact Memory.FramedTriple.mono (Memory.FramedTriple.read_bind
        (c := 7 * e + 1 + (env.r0 + e * (5 + 2 * env.r0))) (by omega)
        (framedTriple_bind_client hfc (hfc_sub_w.trans Set.subset_union_left) Set.Subset.rfl
          (c₂ := 6 * e + (1 + (env.r0 + e * (5 + 2 * env.r0)))) (by omega)
          fun _ _ => framedTriple_bind_client hdec_tri (hdec_sub_w.trans Set.subset_union_left)
            Set.Subset.rfl le_rfl fun _ _ => hbr_safe_tri.2))
        (by dsimp only [C_step]; omega) fun _ _ h => h⟩
  obtain ⟨hsafe, hv, hc, hmod, hpost⟩ := iterate_potential_spec dtPermAnsStep dtPermAnsStepSafe w
    (env, e, permAns) C_step (e ^ e) inv (fun _ _ _ => 0) S
    (fun k hk a s ha => let ⟨hs', ht'⟩ := hstep k hk a s ha
      let ⟨hv', hc', hm', hi'⟩ := framedTriple_iff_realization.mp ht'
      ⟨hs', hv', by omega, hm', hi'⟩)
    0 s ⟨⟨rfl, rfl, Memory.Modifies.refl S s, fun _ hc => absurd hc (Nat.not_lt_zero _)⟩, hwf⟩
  exact ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv, by
      dsimp only [C_step] at hc; rw [Nat.add_zero, Nat.zero_add, Nat.mul_comm] at hc; exact hc,
    hmod, hpost.1.1, hpost.1.2.1, hpost.2, fun code hc => hpost.1.2.2.2 code hc hc⟩⟩

private def dtTryDepthStep (x : DTDepthEnv × DTDepthState) : Memory.Prog DTDepthState := do
  let pow2d := 1 <<< x.2.d
  let _ ← dtFillPowProg ⟨x.1.env.bufC.powSkelArr, x.1.numPairs, pow2d - 1⟩
  let numSkels ← Memory.read (x.1.env.bufC.powSkelArr + (pow2d - 1))
  let sr ← boundedWhile (fun (_ : DTSkelEnv) (st : DTSkelState) => st.cont ≠ 0)
    dtSearchSkelStep ⟨x.1.env, x.1.mask, x.1.e, x.2.d, pow2d, x.1.numPairs, x.1.permAns,
      x.1.powE, numSkels⟩ numSkels ⟨0, 0, 1⟩
  if sr.found = 1 then pure ⟨x.2.d, 1⟩ else pure ⟨x.2.d + 1, 0⟩

private def dtTryDepthWhile (d : DTDepthEnv × ℕ) : Memory.Prog DTDepthState :=
  boundedWhile (fun (_ : DTDepthEnv × ℕ) (st : DTDepthState) => st.found = d.2)
    (fun x => dtTryDepthStep (x.1.1, x.2)) d (d.1.env.maxD + 1) ⟨0, 0⟩

private def dtTryDepthStepSafe (w : ℕ) (x : DTDepthEnv × DTDepthState)
    (s : Memory.State) : Prop :=
  let pow2d := 1 <<< x.2.d
  let pArgs : DTPowArgs := ⟨x.1.env.bufC.powSkelArr, x.1.numPairs, pow2d - 1⟩
  let s1 := (Memory.spec 0).clientState s (dtFillPowProg pArgs)
  let sEnv : DTSkelEnv := ⟨x.1.env, x.1.mask, x.1.e, x.2.d, pow2d, x.1.numPairs, x.1.permAns,
    x.1.powE, s1.mem (x.1.env.bufC.powSkelArr + (pow2d - 1))⟩
  Fits w 2 ∧ Fits w pow2d ∧ 1 ≤ pow2d ∧ Fits w (x.2.d + 1) ∧
  Fits w (x.1.env.bufC.powSkelArr + (pow2d - 1)) ∧ dtFillPowProgSafe w pArgs s ∧
  x.1.env.bufC.powSkelArr + (pow2d - 1) < s1.frontier ∧
  whileSafe (fun (_ : DTSkelEnv) (st : DTSkelState) => st.cont ≠ 0)
    dtSearchSkelStep dtSearchSkelStepSafe w sEnv sEnv.numSkels ⟨0, 0, 1⟩ s1

private theorem realizes_dtTryDepthStep : Realizes .exact
    dtTryDepthStep (appendWords dtDepthEnvWords dtDepthStateWords)
    dtDepthStateWords dtTryDepthStepSafe (fun _ _ => 0) := by
  unfold dtTryDepthStep
  realize [realizes_dtFillPowProg, realizes_dtSearchSkelStep]
  all_goals
    obtain ⟨h2, hp2, h1p, hd1, hps, hpow, hlt, hw⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact h1p | exact hpow
    | exact fun _ => whileSafe_imp _ _ (fun _ => Iff.rfl) (fun _ => rfl)
        (fun _ _ _ hs => ⟨hp2, hs⟩) hw
    | fits [hps, h2]

private theorem dtTryDepthStep_cost_pos (x : DTDepthEnv × DTDepthState) (s : Memory.State) :
    1 ≤ memoryCost (dtTryDepthStep x) s := by
  unfold dtTryDepthStep; dsimp only; simp only [Bind.bind]
  rw [memoryCost_bind, memoryCost_bind, memoryCost_read]; omega

private theorem realizes_dtTryDepthWhile : Realizes .exact dtTryDepthWhile
    (appendWords dtDepthEnvWords wordWords) dtDepthStateWords
    (fun w (d : DTDepthEnv × ℕ) s =>
      whileSafe (fun (d' : DTDepthEnv × ℕ) (st : DTDepthState) => st.found = d'.2)
        (fun x => dtTryDepthStep (x.1.1, x.2)) (fun w x s => dtTryDepthStepSafe w (x.1.1, x.2) s)
        w d (d.1.env.maxD + 1) ⟨0, 0⟩ s)
    (fun _ _ => 0) := by
  have hstep : Realizes .exact (fun x : (DTDepthEnv × ℕ) × DTDepthState =>
      dtTryDepthStep (x.1.1, x.2))
      (appendWords (appendWords dtDepthEnvWords wordWords) dtDepthStateWords)
      dtDepthStateWords (fun w x s => dtTryDepthStepSafe w (x.1.1, x.2) s) (fun _ _ => 0) := by
    realize [realizes_dtTryDepthStep]; exact h
  let cond : Cond (26 + 2) :=
    Cond.eq (Fin.natAdd 26 (1 : Fin 2)) (Fin.castAdd 2 (Fin.natAdd 25 (0 : Fin 1)))
  have hcond : ∀ (d : DTDepthEnv × ℕ) (st : DTDepthState), test cond
      (appendWords (appendWords dtDepthEnvWords wordWords) dtDepthStateWords (d, st)) ↔
      st.found = d.2 := fun d st => by
    dsimp only [cond, test, Cond.Holds]
    rw [appendWords_natAdd, appendWords_castAdd, appendWords_natAdd, dtDepthStateWords_coord_1]; rfl
  have hw0 := Realizes.while₀ (appendWords dtDepthEnvWords wordWords) dtDepthStateWords
    cond (fun x => x.1.1.env.maxD + 1) hstep fun x s => dtTryDepthStep_cost_pos (x.1.1, x.2) s
  have hpure : Realizes .exact (fun _ : DTDepthEnv × ℕ => pure (⟨0, 0⟩ : DTDepthState))
      (appendWords dtDepthEnvWords wordWords) dtDepthStateWords
      (fun _ _ _ => True) (fun _ _ => 0) := by realize
  have hseq := hpure.bind₀_of_run hw0 (fun _ _ => ⟨0, 0⟩) (fun _ s => s)
    (fun _ _ => rfl) fun _ _ => rfl
  have heq : (fun (d : DTDepthEnv × ℕ) => (pure (⟨0, 0⟩ : DTDepthState) : Memory.Prog _).bind
      (fun a => boundedWhile (fun d st => test cond (appendWords (appendWords dtDepthEnvWords
        wordWords) dtDepthStateWords (d, st))) (fun x => dtTryDepthStep (x.1.1, x.2)) d
        (d.1.env.maxD + 1) a)) = dtTryDepthWhile := funext fun d => by
    dsimp only [dtTryDepthWhile]; rw [PFunctor.FreeM.bind_eq_bind, pure_bind]
    exact boundedWhile_congr (fun d' st => test cond (appendWords
      (appendWords dtDepthEnvWords wordWords) dtDepthStateWords (d', st)))
      (fun _ st => st.found = d.2) (body := fun x => dtTryDepthStep (x.1.1, x.2))
      (body' := fun x => dtTryDepthStep (x.1.1, x.2)) (d := d) (d' := d)
      (fun a => hcond d a) (fun _ => rfl) (d.1.env.maxD + 1) ⟨0, 0⟩
  rw [heq] at hseq
  exact hseq.consequence (fun w d s _ _ h => ⟨trivial,
    whileSafe_imp (fun d' st => st.found = d'.2) (fun d' st => test cond (appendWords
      (appendWords dtDepthEnvWords wordWords) dtDepthStateWords (d', st)))
      (fun a => (hcond d a).symm) (fun _ => rfl) (fun _ _ _ hs => hs) h⟩) (fun _ _ => le_rfl)

private theorem dtTryDepth_spec {w baseFront mask e permAns : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (hlay : DTEnvLayout env baseFront) (hbf : baseFront ≤ permAns)
    (hpa_lt : permAns + e ^ e ≤ s.frontier)
    (he2 : 2 ≤ e) (he_le : e ≤ env.maxE) (he_eq : e = (maskEdgePairs env.r0 mask).length)
    (hmask : mask < env.numMasks)
    (hfit_nm : Fits w env.numMasks) (hfit_ee : Fits w (e ^ e + 1))
    (hfit_ns : Fits w ((e.choose 2) ^ (2 ^ env.maxD - 1) + 1))
    (hfit_fr : Fits w (s.frontier + (2 + e + 2 * (2 ^ env.maxD - 1) + 2 ^ env.maxD)))
    (hm_in : DTMaskIn env he_eq permAns (by omega) s) :
    let dEnv : DTDepthEnv := ⟨env, mask, e, e.choose 2, permAns, e ^ e⟩
    let optD := optDepth (endsOfMask env.r0 mask)
    let maxNumSkels := (e.choose 2) ^ (2 ^ env.maxD - 1)
    let S := {env.bufA.tableBase + mask} ∪
      Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ env.maxD) ∪
      Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ env.maxD) ∪
      Set.Ico env.bufC.powSkelArr (env.bufC.powSkelArr + 2 ^ env.maxD) ∪ {a | s.frontier ≤ a}
    whileSafe (fun (_ : DTDepthEnv) (st : DTDepthState) => st.found = 0)
      dtTryDepthStep dtTryDepthStepSafe w dEnv (env.maxD + 1) ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s (dtTryDepthWhile (dEnv, 0)) ((env.maxD + 1) * (2 * 2 ^ env.maxD + 1 +
        maxNumSkels * (5 + 2 * e + 9 * 2 ^ env.maxD + e ^ e * (4 + 5 * env.maxD)))) S
      fun res s' => res.found = 1 ∧ res.d = optD ∧ s.frontier ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (2 + e + 2 * (2 ^ env.maxD - 1) + 2 ^ env.maxD) ∧
        Memory.WellFormed w s' ∧ DTMaskEntryValid env.r0 env.bufA.tableBase mask optD s' ∧
        s.frontier ≤ s'.mem (env.bufA.tableBase + mask) := by
  have he_le_ee := (dtPow_le_self_bounds he2).1; have hnp_pos : 1 ≤ e.choose 2 := Nat.choose_pos he2
  have hr2 := hlay.r0_ge; have hmaxE := hlay.2.1; have hnm := hlay.2.2.1; have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9, hbb10,
    hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  have hnp_le : e.choose 2 ≤ env.maxD := by rw [hmaxD]; exact Nat.choose_le_choose 2 he_le
  let optD := optDepth (endsOfMask env.r0 mask)
  have hopt_le : optD ≤ env.maxD :=
    (optDepth_le_pairs (endsOfMask env.r0 mask)).trans (by rw [← he_eq]; exact hnp_le)
  let maxNumSkels := (e.choose 2) ^ (2 ^ env.maxD - 1)
  let dEnv : DTDepthEnv := ⟨env, mask, e, e.choose 2, permAns, e ^ e⟩
  let S := {env.bufA.tableBase + mask} ∪ Set.Ico env.bufB.leafSeen
    (env.bufB.leafSeen + 2 ^ env.maxD) ∪ Set.Ico env.bufB.leafAns
    (env.bufB.leafAns + 2 ^ env.maxD) ∪ Set.Ico env.bufC.powSkelArr
    (env.bufC.powSkelArr + 2 ^ env.maxD) ∪ {a | s.frontier ≤ a}
  let C_depth := 2 * 2 ^ env.maxD + 1 +
    maxNumSkels * (5 + 2 * e + 9 * 2 ^ env.maxD + e ^ e * (4 + 5 * env.maxD))
  let I (st : DTDepthState) (t : Memory.State) : Prop := (st.found = 0 ∨ st.found = 1) ∧
    (st.found = 0 → st.d ≤ optD ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
      Memory.Modifies S s t) ∧
    (st.found = 1 → st.d = optD ∧ s.frontier ≤ t.frontier ∧
      t.frontier ≤ s.frontier + (2 + e + 2 * (2 ^ env.maxD - 1) + 2 ^ env.maxD) ∧
      Memory.WellFormed w t ∧ DTMaskEntryValid env.r0 env.bufA.tableBase mask optD t ∧
      s.frontier ≤ t.mem (env.bufA.tableBase + mask))
  let rank (st : DTDepthState) (_ : Memory.State) : ℕ :=
    if st.found = 1 then 0 else optD + 1 - st.d
  have hzero : ∀ st t, I st t → rank st t = 0 → ¬(st.found = 0) := fun st _ hi hr hf0 => by
    have hd := (hi.2.1 hf0).1; dsimp only [rank] at hr
    simp only [hf0, Nat.zero_ne_one, ↓reduceIte] at hr; omega
  have hstep : ∀ st t, I st t → st.found = 0 → dtTryDepthStepSafe w (dEnv, st) t ∧
      Memory.FramedTriple w t (dtTryDepthStep (dEnv, st)) C_depth S
        fun a' t' => I a' t' ∧ rank a' t' < rank st t := by
    intro st t ⟨_, hrun, _⟩ hf0
    obtain ⟨hd_le_opt, htfr, hwt, htmod⟩ := hrun hf0
    have hd_le : st.d ≤ env.maxD := hd_le_opt.trans hopt_le
    have hpow2d : 1 <<< st.d = 2 ^ st.d := by simp [Nat.shiftLeft_eq]
    have h2d_le : 2 ^ st.d ≤ 2 ^ env.maxD := Nat.pow_le_pow_right (by decide) hd_le
    have h2d_pos : 1 ≤ 2 ^ st.d := Nat.two_pow_pos st.d
    have h2d_fit : Fits w (2 ^ st.d) := hwt.frontier_fits.of_le (by rw [htfr]; omega)
    have hns_le : (e.choose 2) ^ (2 ^ st.d - 1) ≤ maxNumSkels :=
      Nat.pow_le_pow_right hnp_pos (Nat.sub_le_sub_right h2d_le 1)
    have hps_fit : Fits w ((e.choose 2) ^ (2 ^ st.d - 1) + 1) := hfit_ns.of_le (by omega)
    let pArgs : DTPowArgs := ⟨env.bufC.powSkelArr, e.choose 2, 2 ^ st.d - 1⟩
    have hfp_safe : dtFillPowProgSafe w pArgs t := by
      rw [dtFillPowProgSafe_iff]; dsimp only [pArgs]
      exact ⟨h2, h2d_fit.of_le (by omega), by omega, hps_fit.of_le (by omega), by rw [htfr]; omega⟩
    have hfp_tri := dtFillPowProg_spec hwt hfp_safe
    let s1 := (Memory.spec 0).clientState t (dtFillPowProg pArgs)
    obtain ⟨_, _, hfp_mod, _, hfp_fr, hfp_wf, hfp_arr⟩ := framedTriple_iff_realization.mp hfp_tri
    dsimp only [pArgs] at hfp_mod hfp_arr
    have hs1_fr : s1.frontier = s.frontier := hfp_fr.trans htfr
    have hfp_sub : Set.Ico env.bufC.powSkelArr (env.bufC.powSkelArr + (2 ^ st.d - 1) + 1) ⊆ S :=
      fun a ha => by simp only [S, Set.mem_union, Set.mem_Ico, Set.mem_ofPred_eq] at ha ⊢; omega
    have hm1 : DTMaskIn env he_eq permAns (by omega) s1 :=
      dtMaskIn_of_modifies hm_in (htmod.trans (hfp_mod.mono hfp_sub))
        (by omega) (by omega) (by omega) (by omega) (by omega) fun a ha => by
          simp only [S, Set.mem_union, Set.mem_Ico, Set.mem_singleton_iff, Set.mem_ofPred_eq]
          omega
    obtain ⟨hsk_safe, hsk_tri⟩ := dtSearchSkel_spec (w := w) (baseFront := baseFront)
      (mask := mask) (e := e) (d := st.d) (permAns := permAns) h2 hfp_wf hlay hbf
      (hs1_fr.symm ▸ hpa_lt) he2 he_le he_eq hd_le hmask hfit_nm hfit_ee hps_fit
      (hs1_fr.symm ▸ hfit_fr.of_le (by have := Nat.sub_le_sub_right h2d_le 1; omega))
      (fun k hk => hfp_arr k hk) hm1
    have hsk_sub : {env.bufA.tableBase + mask} ∪
        Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ st.d) ∪
        Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ st.d) ∪ {a | s1.frontier ≤ a} ⊆ S :=
      fun a ha => by simp only [S, Set.mem_union, Set.mem_Ico, Set.mem_singleton_iff,
        Set.mem_ofPred_eq, hs1_fr] at ha ⊢; omega
    have hns_mul_le : (e.choose 2) ^ (2 ^ st.d - 1) *
        (5 + 2 * e + 9 * 2 ^ st.d + e ^ e * (4 + 5 * st.d)) ≤
        maxNumSkels * (5 + 2 * e + 9 * 2 ^ env.maxD + e ^ e * (4 + 5 * env.maxD)) :=
      Nat.mul_le_mul hns_le (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 9 h2d_le) _)
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left 5 hd_le) 4)))
    have hsk_num := hfp_arr (2 ^ st.d - 1) le_rfl
    let C_sk := (e.choose 2) ^ (2 ^ st.d - 1) * (5 + 2 * e + 9 * 2 ^ st.d + e ^ e * (4 + 5 * st.d))
    have htri_step : Memory.FramedTriple w t (dtTryDepthStep (dEnv, st)) C_depth S
        fun a' t' => I a' t' ∧ rank a' t' < rank st t := by
      dsimp only [dtTryDepthStep, dEnv]; rw [hpow2d]
      refine framedTriple_bind_client hfp_tri hfp_sub Set.Subset.rfl
        (c₂ := 1 + C_sk) (by dsimp only [C_depth, C_sk, pArgs]; omega) fun _ _ =>
        Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := C_sk)
          (by rw [hs1_fr]; omega) ?_) (by omega) fun _ _ h => h
      rw [show s1.mem (env.bufC.powSkelArr + (2 ^ st.d - 1)) = (e.choose 2) ^ (2 ^ st.d - 1)
        from hsk_num]
      exact framedTriple_bind_client hsk_tri hsk_sub Set.Subset.rfl (c₂ := 0) le_rfl
        fun ⟨hsr01, hs2_wf, hsr0, hsr1⟩ hs2_mod => by
          rcases hsr01 with h0 | h1
          · obtain ⟨hs2_fr, hlt_opt⟩ := hsr0 h0; simp only [h0, Nat.zero_ne_one, ↓reduceIte]
            exact Memory.FramedTriple.pure ⟨⟨.inl rfl, fun _ => ⟨hlt_opt, hs2_fr.trans hs1_fr,
                hs2_wf, htmod.trans ((hfp_mod.mono hfp_sub).trans (hs2_mod.mono hsk_sub))⟩,
              fun h => absurd h Nat.zero_ne_one⟩,
              by dsimp only [rank]; simp only [hf0, Nat.zero_ne_one, ↓reduceIte]; omega⟩
          · obtain ⟨hs2_fr, hval, hptr⟩ := hsr1 h1; simp only [h1, ↓reduceIte]
            have hdeq : st.d = optD := by
              obtain ⟨T, hc, hcor, _⟩ := hval.2.2.2.1
              have := (exists_complete_correct_iff (he_eq ▸ he2) (endsOfMask env.r0 mask) st.d).mp
                ⟨T, hc, hcor⟩; omega
            exact Memory.FramedTriple.pure ⟨⟨.inr rfl, fun h => absurd h Nat.one_ne_zero, fun _ =>
              ⟨hdeq, by rw [hs2_fr, hs1_fr]; omega, by rw [hs2_fr, hs1_fr]; omega, hs2_wf,
                hdeq ▸ hval, hs1_fr ▸ hptr⟩⟩,
              by dsimp only [rank]; simp only [hf0, Nat.zero_ne_one, ↓reduceIte]; omega⟩
    exact ⟨⟨h2, hpow2d ▸ h2d_fit, hpow2d ▸ h2d_pos,
        (by dsimp only [dEnv]; exact h2d_fit.of_le (by
          have := Nat.lt_two_pow_self (n := st.d); omega)),
        by dsimp only [dEnv]; rw [hpow2d]; exact hwt.frontier_fits.of_le (by rw [htfr]; omega),
        by dsimp only [dEnv]; simp only [hpow2d]; exact hfp_safe,
        by dsimp only [dEnv]; rw [hpow2d, hfp_fr, htfr]; omega,
        by dsimp only [dEnv, s1, pArgs] at hsk_num ⊢; simpa only [hpow2d, hsk_num] using hsk_safe⟩,
      htri_step⟩
  have hinit : I ⟨0, 0⟩ s :=
    ⟨.inl rfl, fun _ => ⟨Nat.zero_le _, rfl, hwf, Memory.Modifies.refl S s⟩,
      fun h => absurd h Nat.zero_ne_one⟩
  obtain ⟨hsafe, htri⟩ := boundedWhile_framedTriple_spec (fun (_ : DTDepthEnv)
      (st : DTDepthState) => st.found = 0) dtTryDepthStep dtTryDepthStepSafe hzero hstep
    hinit (fuel := env.maxD + 1) (by simp only [rank, Nat.zero_ne_one, ↓reduceIte]; omega)
  have heq_w : dtTryDepthWhile (dEnv, 0) = boundedWhile
      (fun (_ : DTDepthEnv) (st : DTDepthState) => st.found = 0) dtTryDepthStep dEnv
      (env.maxD + 1) ⟨0, 0⟩ := boundedWhile_congr (fun (_ : DTDepthEnv × ℕ) st => st.found = 0)
    (fun _ st => st.found = 0) (body := fun x => dtTryDepthStep (x.1.1, x.2))
    (body' := dtTryDepthStep) (fun _ => Iff.rfl) (fun _ => rfl) (env.maxD + 1) ⟨0, 0⟩
  change _ ∧ Memory.FramedTriple w s (dtTryDepthWhile (dEnv, 0)) _ _ _
  exact ⟨hsafe, heq_w ▸ htri.mono (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right C_depth (by
      simp only [rank, Nat.zero_ne_one, ↓reduceIte]; omega))
    fun res s' ⟨hstop, h01, _, hdone⟩ => have hf1 := h01.resolve_left hstop; ⟨hf1, hdone hf1⟩⟩

private def dtBuildAndSearchProg (d : DTBuildSearchArgs) : Memory.Prog Unit := do
  let powE ← Memory.read (d.env.bufC.powEArr + d.e); let permBlk ← Memory.allocBlockDirty powE
  let _ ← iterate dtPermAnsStep (d.env, d.e, permBlk.base) powE 0
  let _ ← dtFillAllPairsProg ⟨d.env.bufB.allPairA, d.env.bufB.allPairB, d.e⟩
  let _ ← dtTryDepthWhile (⟨d.env, d.mask, d.e, d.e * (d.e - 1) / 2, permBlk.base, powE⟩, 0)
  pure ()

private def dtBuildAndSearchProgSafe (w : ℕ) (d : DTBuildSearchArgs)
    (s : Memory.State) : Prop :=
  let powE := s.mem (d.env.bufC.powEArr + d.e)
  let s1 : Memory.State := ⟨s.mem, s.frontier + powE⟩
  let s2 := (Memory.spec 0).clientState s1 (iterate dtPermAnsStep (d.env, d.e, s.frontier) powE 0)
  let s3 := (Memory.spec 0).clientState s2
    (dtFillAllPairsProg ⟨d.env.bufB.allPairA, d.env.bufB.allPairB, d.e⟩)
  Fits w 2 ∧ d.env.bufC.powEArr + d.e < s.frontier ∧ Fits w (s.frontier + powE) ∧
  1 ≤ d.e ∧ Fits w (d.e * (d.e - 1)) ∧
  iterationSafe dtPermAnsStep dtPermAnsStepSafe w (d.env, d.e, s.frontier) powE 0 s1 ∧
  dtFillAllPairsProgSafe w ⟨d.env.bufB.allPairA, d.env.bufB.allPairB, d.e⟩ s2 ∧
  whileSafe (fun (_ : DTDepthEnv) (st : DTDepthState) => st.found = 0)
    dtTryDepthStep dtTryDepthStepSafe w
    ⟨d.env, d.mask, d.e, d.e * (d.e - 1) / 2, s.frontier, powE⟩ (d.env.maxD + 1) ⟨0, 0⟩ s3

private theorem realizes_dtBuildAndSearchProg : Realizes .exact
    dtBuildAndSearchProg dtBuildSearchArgsWords WordEncoding.encode
    dtBuildAndSearchProgSafe (fun _ _ => 0) := by
  unfold dtBuildAndSearchProg
  realize [realizes_allocBlockDirty, realizes_dtPermAnsStep, realizes_dtFillAllPairsProg,
    realizes_dtTryDepthWhile]
  all_goals
    repeat rw [Memory.clientState_allocBlockDirty] at *
    try simp only [Memory.clientResult_allocBlockDirty] at *
    obtain ⟨h2, hpe, hs1, he1, hmul, hit, hap, hw⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact whileSafe_imp (fun (_ : DTDepthEnv) (st : DTDepthState) => st.found = 0)
        (fun d' st => st.found = d'.2)
        (d' := (⟨d.env, d.mask, d.e, d.e * (d.e - 1) / 2, s.frontier,
          s.mem (d.env.bufC.powEArr + d.e)⟩, 0))
        (body' := fun x => dtTryDepthStep (x.1.1, x.2))
        (safe' := fun w x s => dtTryDepthStepSafe w (x.1.1, x.2) s)
        (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs => hs) hw
    | exact iterationSafe_imp hit (fun _ => rfl) (fun _ _ hs => hs)
    | exact hap | omega | fits [hmul]

private theorem dtBuildAndSearchProg_spec {w baseFront mask e : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s) (hlay : DTEnvLayout env baseFront)
    (hbf_lt : baseFront ≤ s.frontier) (he2 : 2 ≤ e) (he_le : e ≤ env.maxE)
    (he_eq : e = (maskEdgePairs env.r0 mask).length) (hmask : mask < env.numMasks)
    (hfit_nm : Fits w env.numMasks) (hfit_ee : Fits w (e ^ e + 1))
    (hfit_ns : Fits w ((e.choose 2) ^ (2 ^ env.maxD - 1) + 1))
    (hfit_fr : Fits w (s.frontier + e ^ e + (2 + e + 2 * (2 ^ env.maxD - 1) + 2 ^ env.maxD)))
    (hpowe : ∀ j ≤ e, s.mem (env.bufC.powEArr + j) = e ^ j)
    (hends : ∀ j (hj : j < (maskEdgePairs env.r0 mask).length),
      s.mem (env.bufA.edgeU + j) = (maskEdgePairs env.r0 mask)[j].1.val ∧
      s.mem (env.bufA.edgeV + j) = (maskEdgePairs env.r0 mask)[j].2.val)
    (hmask_ep : ∀ j (hj : j < (maskEdgePairs env.r0 mask).length), s.mem (env.bufA.edgePair + j) =
      pairIdx (maskEdgePairs env.r0 mask)[j].1.val (maskEdgePairs env.r0 mask)[j].2.val) :
    let maxNumSkels := (e.choose 2) ^ (2 ^ env.maxD - 1)
    let S := {a | (env.bufB.allPairA ≤ a ∧ a < baseFront) ∨
      a = env.bufA.tableBase + mask ∨ s.frontier ≤ a}
    dtBuildAndSearchProgSafe w ⟨env, mask, e⟩ s ∧
    Memory.FramedTriple w s (dtBuildAndSearchProg ⟨env, mask, e⟩)
      (2 + e ^ e * (2 + 7 * e + env.r0 + e * (5 + 2 * env.r0)) + e * (1 + 2 * e) +
        (env.maxD + 1) * (2 * 2 ^ env.maxD + 1 +
          maxNumSkels * (5 + 2 * e + 9 * 2 ^ env.maxD + e ^ e * (4 + 5 * env.maxD)))) S
      fun _ s' =>
        s'.frontier ≤ s.frontier + e ^ e + (2 + e + 2 * (2 ^ env.maxD - 1) + 2 ^ env.maxD) ∧
        Memory.WellFormed w s' ∧
        DTMaskEntryValid env.r0 env.bufA.tableBase mask (optDepth (endsOfMask env.r0 mask)) s' ∧
        s.frontier ≤ s'.mem (env.bufA.tableBase + mask) ∧ s.frontier ≤ s'.frontier := by
  have hr2 := hlay.r0_ge; have hmaxE := hlay.2.1; have hnm := hlay.2.2.1; have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9, hbb10,
    hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  obtain ⟨he_le_ee, hch_le_ee, hmul_ee⟩ := dtPow_le_self_bounds he2
  have hnp_le : e.choose 2 ≤ env.maxD := by rw [hmaxD]; exact Nat.choose_le_choose 2 he_le
  have hfit_pa : Fits w (s.frontier + e ^ e) := hfit_fr.of_le (by omega)
  have hpe_eq : s.mem (env.bufC.powEArr + e) = e ^ e := hpowe e le_rfl
  let permAns := s.frontier
  let S := {a | (env.bufB.allPairA ≤ a ∧ a < baseFront) ∨
    a = env.bufA.tableBase + mask ∨ s.frontier ≤ a}
  let s1 : Memory.State := ⟨s.mem, s.frontier + e ^ e⟩
  have hwf1 : Memory.WellFormed w s1 := ⟨hfit_pa, hwf.mem_fits⟩
  obtain ⟨hpa_safe, hpa_tri⟩ := dtPermAns_loop_spec (w := w) (baseFront := baseFront)
    (mask := mask) (e := e) (permAns := permAns) h2 hwf1 hlay hbf_lt he2 he_le he_eq
    (by dsimp only [s1, permAns]; omega) hfit_ee hpowe hends
  let s2 := (Memory.spec 0).clientState s1 (iterate dtPermAnsStep (env, e, permAns) (e ^ e) 0)
  obtain ⟨_, _, hpa_mod, _, hpa_fr, hpa_wf, hpa_arr⟩ := framedTriple_iff_realization.mp hpa_tri
  have hap_safe : dtFillAllPairsProgSafe w ⟨env.bufB.allPairA, env.bufB.allPairB, e⟩ s2 := by
    rw [dtFillAllPairsProgSafe_iff]; dsimp only
    exact ⟨h2, hfit_ee.of_le (by omega), hfit_ee.of_le (by omega),
      fun _ => by rw [hpa_fr]; dsimp only [s1]; omega,
      by rw [hpa_fr]; dsimp only [s1]; omega, by rw [hpa_fr]; dsimp only [s1]; omega,
      by left; omega⟩
  have hap_tri := dtFillAllPairsProg_spec hpa_wf hap_safe
  let s3 := (Memory.spec 0).clientState s2
    (dtFillAllPairsProg ⟨env.bufB.allPairA, env.bufB.allPairB, e⟩)
  obtain ⟨_, _, hap_mod, _, hap_fr, hap_wf, hap_arr⟩ := framedTriple_iff_realization.mp hap_tri
  dsimp only at hap_mod hap_fr hap_arr
  have hs3_fr : s3.frontier = s.frontier + e ^ e := hap_fr.trans hpa_fr
  have hpa_sub : (Set.Ico env.bufB.rankArr (env.bufB.rankArr + env.maxE) ∪
      Set.Ico env.bufB.orderArr (env.bufB.orderArr + env.maxE) ∪
      Set.Ico env.bufC.seenArr (env.bufC.seenArr + env.maxE) ∪
      Set.Ico env.bufC.compArr (env.bufC.compArr + env.r0) ∪
      Set.Ico permAns (permAns + e ^ e)) ⊆ S := fun a ha => by
    simp only [S, permAns, Set.mem_union, Set.mem_Ico, Set.mem_ofPred_eq] at ha ⊢; omega
  have hap_sub : (Set.Ico env.bufB.allPairA (env.bufB.allPairA + e.choose 2) ∪
      Set.Ico env.bufB.allPairB (env.bufB.allPairB + e.choose 2)) ⊆ S := fun a ha => by
    simp only [S, Set.mem_union, Set.mem_Ico, Set.mem_ofPred_eq] at ha ⊢; omega
  have hm_in : DTMaskIn env he_eq permAns (by omega) s3 := by
    have hpres : ∀ a < s.frontier,
        a ∉ Set.Ico env.bufB.allPairA (env.bufB.allPairA + e.choose 2) ∪
          Set.Ico env.bufB.allPairB (env.bufB.allPairB + e.choose 2) →
        a ∉ Set.Ico env.bufB.rankArr (env.bufB.rankArr + env.maxE) ∪
          Set.Ico env.bufB.orderArr (env.bufB.orderArr + env.maxE) ∪
          Set.Ico env.bufC.seenArr (env.bufC.seenArr + env.maxE) ∪
          Set.Ico env.bufC.compArr (env.bufC.compArr + env.r0) ∪
          Set.Ico permAns (permAns + e ^ e) → s3.mem a = s.mem a :=
      fun a ha ha1 ha2 => (hap_mod.mem_eq_of_not_mem (by rw [hpa_fr]; dsimp only [s1]; omega)
        ha1).trans (hpa_mod.mem_eq_of_not_mem (by dsimp only [s1]; omega) ha2)
    refine ⟨fun j hj => (hpres _ (by omega) (by simp; omega) (by simp; omega)).trans (hpowe j hj),
      hap_arr, fun j hj => (hpres _ (by have := he_eq ▸ hj; omega) (by simp; omega)
        (by simp; omega)).trans (hmask_ep j hj), fun code hc => by
          rw [hap_mod.mem_eq_of_not_mem (a := permAns + code)
            (by rw [hpa_fr]; dsimp only [s1, permAns]; omega)
            (by simp only [Set.mem_union, Set.mem_Ico]; omega)]
          exact hpa_arr code hc⟩
  obtain ⟨htry_safe, htry_tri⟩ := dtTryDepth_spec (w := w) (baseFront := baseFront)
    (mask := mask) (e := e) (permAns := permAns) h2 hap_wf hlay hbf_lt (by rw [hs3_fr]) he2 he_le
    he_eq hmask hfit_nm hfit_ee hfit_ns (by rw [hs3_fr]; exact hfit_fr) hm_in
  have htry_sub : ({env.bufA.tableBase + mask} ∪
      Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ env.maxD) ∪
      Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ env.maxD) ∪
      Set.Ico env.bufC.powSkelArr (env.bufC.powSkelArr + 2 ^ env.maxD) ∪
      {a | s3.frontier ≤ a}) ⊆ S := fun a ha => by
    simp only [S, Set.mem_union, Set.mem_Ico, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, hs3_fr] at ha ⊢; omega
  refine ⟨⟨h2, by dsimp only; omega, by dsimp only; rw [hpe_eq]; exact hfit_pa,
      by dsimp only; omega, by dsimp only; exact hfit_ee.of_le (by omega),
      by dsimp only; rw [hpe_eq]; exact hpa_safe, by dsimp only; rw [hpe_eq]; exact hap_safe,
      by dsimp only; simp only [hpe_eq, ← Nat.choose_two_right]; exact htry_safe⟩, ?_⟩
  dsimp only [dtBuildAndSearchProg]
  let C_try := (env.maxD + 1) * (2 * 2 ^ env.maxD + 1 + (e.choose 2) ^ (2 ^ env.maxD - 1) *
    (5 + 2 * e + 9 * 2 ^ env.maxD + e ^ e * (4 + 5 * env.maxD)))
  let C_pa := e ^ e * (2 + 7 * e + env.r0 + e * (5 + 2 * env.r0))
  refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind
    (c := C_pa + e * (1 + 2 * e) + C_try + 1) (by omega) ?_) (by dsimp only [C_pa, C_try]; omega)
    fun _ _ h => h
  rw [hpe_eq]; refine Memory.FramedTriple.allocBlockDirty_bind hfit_pa ?_
  rw [show e * (e - 1) / 2 = e.choose 2 from (Nat.choose_two_right e).symm]
  exact framedTriple_bind_client hpa_tri hpa_sub Set.Subset.rfl (c₂ := e * (1 + 2 * e) + C_try)
    (by dsimp only [C_pa]; omega) fun _ _ => framedTriple_bind_client hap_tri hap_sub Set.Subset.rfl
      (c₂ := C_try) (by dsimp only [C_try]; omega) fun _ _ => framedTriple_bind_client htry_tri
        htry_sub Set.Subset.rfl (c₂ := 0) le_rfl fun ⟨_, _, hs'_ge, hs'_le, hs'_wf, hs'_val,
          hs'_ptr⟩ _ => Memory.FramedTriple.pure ⟨by rw [hs3_fr] at hs'_le; exact hs'_le,
            hs'_wf, hs'_val, by rw [hs3_fr] at hs'_ptr; omega, by rw [hs3_fr] at hs'_ge; omega⟩

private def dtProcessMaskStep (x : DTPrecompEnv × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read x.1.bufA.tableBase
  let e ← dtDecodeMaskProg ⟨x.1.bufA.r0PairA, x.1.bufA.r0PairB, x.1.bufA.edgeU,
    x.1.bufA.edgeV, x.1.bufA.edgePair, x.2, x.1.maxE⟩
  if e ≤ 1 then
    dtWriteTrivialEntry (x.1.bufA.tableBase, x.2, e, x.1.bufA.edgePair); pure (x.2 + 1)
  else
    let _ ← dtFillPowProg ⟨x.1.bufC.powEArr, e, e⟩; dtBuildAndSearchProg ⟨x.1, x.2, e⟩
    pure (x.2 + 1)

private def dtProcessMaskStepSafe (w : ℕ) (x : DTPrecompEnv × ℕ) (s : Memory.State) : Prop :=
  let dArgs : DTDecodeMaskArgs := ⟨x.1.bufA.r0PairA, x.1.bufA.r0PairB, x.1.bufA.edgeU,
    x.1.bufA.edgeV, x.1.bufA.edgePair, x.2, x.1.maxE⟩
  let e := (Memory.spec 0).clientResult s (dtDecodeMaskProg dArgs)
  let s1 := (Memory.spec 0).clientState s (dtDecodeMaskProg dArgs)
  let s2 := (Memory.spec 0).clientState s1 (dtFillPowProg ⟨x.1.bufC.powEArr, e, e⟩)
  Fits w 2 ∧ Fits w (x.2 + 1) ∧ x.1.bufA.tableBase < s.frontier ∧
  dtDecodeMaskProgSafe w dArgs s ∧
  (e ≤ 1 → dtWriteTrivialEntrySafe w (x.1.bufA.tableBase, x.2, e, x.1.bufA.edgePair) s1) ∧
  (¬e ≤ 1 → dtFillPowProgSafe w ⟨x.1.bufC.powEArr, e, e⟩ s1 ∧
    dtBuildAndSearchProgSafe w ⟨x.1, x.2, e⟩ s2)

private theorem realizes_dtProcessMaskStep : Realizes .exact
    dtProcessMaskStep (appendWords dtPrecompEnvWords WordEncoding.encode)
    WordEncoding.encode dtProcessMaskStepSafe (fun _ _ => 0) := by
  unfold dtProcessMaskStep; realize [realizes_dtDecodeMaskProg, realizes_dtWriteTrivialEntry,
    realizes_dtFillPowProg, realizes_dtBuildAndSearchProg]
  all_goals
    obtain ⟨h2, hidx, htb, hdec, htriv, hbig⟩ := h; have hfront := hmem.frontier_fits
    first
    | exact hdec | exact htriv (by omega)
    | exact (hbig (by omega)).1 | exact (hbig (by omega)).2 | fits

private theorem dtProcessMaskStep_spec {w baseFront mask : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s) (hlay : DTEnvLayout env baseFront)
    (hbf_lt : baseFront ≤ s.frontier) (hmask : mask < env.numMasks) (hfit_nm : Fits w env.numMasks)
    (hfit_cost : Fits w (dtPrecompCost env.r0))
    (hfit_dt : Fits w (s.frontier + 2 ^ (2 ^ (2 * env.r0 ^ 4 + 5))))
    (hpairs_r0 : ∀ pk (hpk : pk < env.r0.choose 2),
      s.mem (env.bufA.r0PairA + pk) = ((allPairs env.r0)[pk]'(length_allPairs _ ▸ hpk)).1.val ∧
      s.mem (env.bufA.r0PairB + pk) = ((allPairs env.r0)[pk]'(length_allPairs _ ▸ hpk)).2.val) :
    let S := {a | (env.bufA.edgeU ≤ a ∧ a < baseFront) ∨
      a = env.bufA.tableBase + mask ∨ s.frontier ≤ a}
    dtProcessMaskStepSafe w (env, mask) s ∧ Memory.FramedTriple w s (dtProcessMaskStep (env, mask))
      (2 ^ (2 ^ (2 * env.r0 ^ 4 + 11))) S fun res s' =>
      res = mask + 1 ∧ s.frontier ≤ s'.frontier ∧
      s'.frontier ≤ s.frontier + 2 ^ (2 ^ (2 * env.r0 ^ 4 + 5)) ∧
      Memory.WellFormed w s' ∧
      DTMaskEntryValid env.r0 env.bufA.tableBase mask (optDepth (endsOfMask env.r0 mask)) s' ∧
      s.frontier ≤ s'.mem (env.bufA.tableBase + mask) := by
  have hr2 := hlay.r0_ge; have hmaxE := hlay.2.1; have hnm := hlay.2.2.1; have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9, hbb10,
    hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  have hfit_mE1 : Fits w (env.maxE + 1) := hfit_nm.of_le (by rw [hnm]; exact Nat.lt_two_pow_self)
  let dArgs : DTDecodeMaskArgs := ⟨env.bufA.r0PairA, env.bufA.r0PairB, env.bufA.edgeU,
    env.bufA.edgeV, env.bufA.edgePair, mask, env.maxE⟩
  have hdec_safe : dtDecodeMaskProgSafe w dArgs s := by
    rw [dtDecodeMaskProgSafe_iff]; dsimp only [dArgs]
    exact ⟨h2, hfit_mE1, by omega, by omega, by omega, by omega, by omega⟩
  have hdec_tri := dtDecodeMaskProg_spec hwf hdec_safe hmaxE hpairs_r0
    (.inl (hmaxE ▸ by dsimp only [dArgs]; omega)) (.inl (hmaxE ▸ by dsimp only [dArgs]; omega))
    (.inl (hmaxE ▸ by dsimp only [dArgs]; omega)) (.inr (hmaxE ▸ by dsimp only [dArgs]; omega))
    (.inr (hmaxE ▸ by dsimp only [dArgs]; omega)) (.inr (hmaxE ▸ by dsimp only [dArgs]; omega))
    (.inr (hmaxE ▸ by dsimp only [dArgs]; omega)) (.inr (hmaxE ▸ by dsimp only [dArgs]; omega))
    (.inr (hmaxE ▸ by dsimp only [dArgs]; omega))
  let e := (Memory.spec 0).clientResult s (dtDecodeMaskProg dArgs)
  let s1 := (Memory.spec 0).clientState s (dtDecodeMaskProg dArgs)
  obtain ⟨_, _, hdec_mod, hda, hdec_fr, hdec_wf, hdec_arr⟩ :=
    framedTriple_iff_realization.mp hdec_tri
  dsimp only [dArgs] at hda hdec_arr
  have he_le : e ≤ env.maxE := by
    dsimp only [e]; rw [hda, hmaxE, length_maskEdgePairs]
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have h4_le_exp : 4 ≤ 2 ^ (2 ^ (2 * env.r0 ^ 4 + 5)) := (by decide : 4 ≤ 2 ^ 5).trans
    ((Nat.pow_le_pow_right (by decide) (by omega)).trans Nat.lt_two_pow_self.le)
  let S := {a | (env.bufA.edgeU ≤ a ∧ a < baseFront) ∨
    a = env.bufA.tableBase + mask ∨ s.frontier ≤ a}
  have hdec_sub : (Set.Ico env.bufA.edgeU (env.bufA.edgeU + env.maxE) ∪
      Set.Ico env.bufA.edgeV (env.bufA.edgeV + env.maxE) ∪
      Set.Ico env.bufA.edgePair (env.bufA.edgePair + env.maxE)) ⊆ S := fun a ha => by
    simp only [S, Set.mem_union, Set.mem_Ico, Set.mem_ofPred_eq] at ha ⊢; omega
  by_cases he1 : e ≤ 1
  · obtain ⟨htr_safe, htr_tri⟩ := dtWriteTrivialEntry_spec (w := w) (r0 := env.r0)
      (tableBase := env.bufA.tableBase) (mask := mask) (e := e) (edgePair := env.bufA.edgePair)
      h2 hdec_wf he1 hda (by rw [hdec_fr, ← hmaxE]; omega) (by rw [← hmaxE, ← hnm]; exact hmask)
      (by rw [hdec_fr]; omega) (by left; rw [← hmaxE]; omega)
      (hfit_dt.of_le (by rw [hdec_fr]; omega)) (fun j hj => (hdec_arr j hj).2.2)
    have hopt0 : optDepth (endsOfMask env.r0 mask) = 0 :=
      optDepth_eq_zero_of_le_one (by rw [← hda]; exact he1) _
    refine ⟨⟨h2, hfit_nm.of_le (by omega), by dsimp only; omega, hdec_safe, fun _ => htr_safe,
        fun h => absurd he1 h⟩, ?_⟩
    dsimp only [dtProcessMaskStep]
    refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := 5 * env.maxE + 8)
      (by omega) (framedTriple_bind_client hdec_tri hdec_sub Set.Subset.rfl (c₂ := 8)
        (by dsimp only [dArgs]; omega) fun _ _ => ?_))
      (by obtain ⟨_, _, _, _, ht, _, _, _⟩ := dtPrecompArithBounds hr2 (hmaxE ▸ he_le)
          rw [← hmaxE] at ht; omega) fun _ _ h => h
    change Memory.FramedTriple w s1 (if e ≤ 1 then _ else _) _ S _; simp only [he1, ↓reduceIte]
    exact framedTriple_bind_client htr_tri (fun a ha => by
        simp only [S, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ico, Set.mem_ofPred_eq] at ha ⊢
        rcases ha with rfl | ⟨_, _⟩
        · exact .inr (.inl rfl)
        · exact .inr (.inr (by rw [hdec_fr] at *; omega)))
      Set.Subset.rfl (c₂ := 0) le_rfl fun ⟨hs2_fr, hs2_wf, hs2_ptr, hs2_val⟩ _ =>
        Memory.FramedTriple.pure ⟨rfl, by rw [hs2_fr, hdec_fr]; omega,
          by rw [hs2_fr, hdec_fr]; omega, hs2_wf, hopt0 ▸ hs2_val, by rw [hs2_ptr, hdec_fr]⟩
  · obtain ⟨har'_fr, har'_ee, har'_ns, har'_step, _, _, _, _⟩ :=
      dtPrecompArithBounds hr2 (hmaxE ▸ he_le)
    rw [← hmaxE, ← hmaxD] at har'_fr har'_step
    have he2 : 2 ≤ e := by omega
    have hfit_e1 : Fits w (e + 1) := hfit_mE1.of_le (by omega)
    have hfit_ee : Fits w (e ^ e + 1) :=
      hfit_cost.of_le (le_dtPrecompCost_of_exp_le hr2 (by omega) har'_ee)
    have hfit_ns : Fits w ((e.choose 2) ^ (2 ^ env.maxD - 1) + 1) := by
      rw [hmaxD, hmaxE]; exact hfit_cost.of_le (le_dtPrecompCost_of_exp_le hr2 (by omega) har'_ns)
    have hfp_safe : dtFillPowProgSafe w ⟨env.bufC.powEArr, e, e⟩ s1 := by
      rw [dtFillPowProgSafe_iff]; dsimp only
      exact ⟨h2, hfit_e1, by omega, hfit_ee.of_le (by omega), by rw [hdec_fr]; omega⟩
    have hfp_tri := dtFillPowProg_spec hdec_wf hfp_safe
    let s2 := (Memory.spec 0).clientState s1 (dtFillPowProg ⟨env.bufC.powEArr, e, e⟩)
    obtain ⟨_, _, hfp_mod, _, hfp_fr, hfp_wf, hfp_arr⟩ := framedTriple_iff_realization.mp hfp_tri
    dsimp only at hfp_mod hfp_fr hfp_arr
    have hs2_fr : s2.frontier = s.frontier := hfp_fr.trans hdec_fr
    have hfp_sub : Set.Ico env.bufC.powEArr (env.bufC.powEArr + e + 1) ⊆ S := fun a ha => by
      simp only [S, Set.mem_Ico, Set.mem_ofPred_eq] at ha ⊢; omega
    have hfp_pres_ev : ∀ a < baseFront, a < env.bufC.powEArr → s2.mem a = s1.mem a :=
      fun a ha1 ha2 => hfp_mod.mem_eq_of_not_mem (by rw [hdec_fr]; omega)
        (by simp only [Set.mem_Ico]; omega)
    obtain ⟨hbs_safe, hbs_tri⟩ := dtBuildAndSearchProg_spec (w := w) (baseFront := baseFront)
      (mask := mask) (e := e) h2 hfp_wf hlay (by rw [hs2_fr]; exact hbf_lt) he2 he_le hda hmask
      (hfit_nm.of_le (by omega)) hfit_ee hfit_ns (by rw [hs2_fr]; exact hfit_dt.of_le (by omega))
      hfp_arr
      (fun j hj => have := (hda ▸ hj).trans_le he_le; ⟨(hfp_pres_ev _ (by omega) (by omega)).trans
        (hdec_arr j hj).1, (hfp_pres_ev _ (by omega) (by omega)).trans (hdec_arr j hj).2.1⟩)
      (fun j hj => have := (hda ▸ hj).trans_le he_le; (hfp_pres_ev _ (by omega) (by omega)).trans
        (hdec_arr j hj).2.2)
    have hbs_sub : {a | (env.bufB.allPairA ≤ a ∧ a < baseFront) ∨
        a = env.bufA.tableBase + mask ∨ s2.frontier ≤ a} ⊆ S := fun a ha => by
      simp only [S, Set.mem_ofPred_eq, hs2_fr] at ha ⊢; rcases ha with ⟨_, _⟩ | rfl | _ <;> omega
    refine ⟨⟨h2, hfit_nm.of_le (by omega), by dsimp only; omega, hdec_safe,
        fun h => absurd h he1, fun _ => ⟨hfp_safe, hbs_safe⟩⟩, ?_⟩
    dsimp only [dtProcessMaskStep]
    let C_bs := 2 + e ^ e * (2 + 7 * e + env.r0 + e * (5 + 2 * env.r0)) + e * (1 + 2 * e) +
      (env.maxD + 1) * (2 * 2 ^ env.maxD + 1 + (e.choose 2) ^ (2 ^ env.maxD - 1) *
        (5 + 2 * e + 9 * 2 ^ env.maxD + e ^ e * (4 + 5 * env.maxD)))
    refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind
      (c := 5 * env.maxE + (1 + 2 * e) + C_bs) (by omega)
      (framedTriple_bind_client hdec_tri hdec_sub Set.Subset.rfl (c₂ := 1 + 2 * e + C_bs)
        (by dsimp only [dArgs]; omega) fun _ _ => ?_)) (by dsimp only [C_bs]; omega) fun _ _ h => h
    change Memory.FramedTriple w s1 (if e ≤ 1 then _ else _) _ S _; simp only [he1, ↓reduceIte]
    exact framedTriple_bind_client hfp_tri hfp_sub Set.Subset.rfl (c₂ := C_bs)
      (by dsimp only; omega) fun _ _ => framedTriple_bind_client hbs_tri hbs_sub Set.Subset.rfl
        (c₂ := 0) le_rfl fun ⟨hs3_fr, hs3_wf, hs3_val, hs3_ptr, hs3_ge⟩ _ =>
          Memory.FramedTriple.pure ⟨rfl, hs2_fr ▸ hs3_ge, by rw [hs2_fr] at hs3_fr; omega,
            hs3_wf, hs3_val, hs2_fr ▸ hs3_ptr⟩

private def dtPrecompTrivial (_ : Unit) : Memory.Prog ℕ := do
  let tblBlk ← Memory.allocBlockDirty 1; let epBlk ← Memory.allocBlockDirty 3
  Memory.write tblBlk.base epBlk.base; Memory.write epBlk.base 0
  Memory.write (epBlk.base + 1) 0; Memory.write (epBlk.base + 2) 0
  pure tblBlk.base

private def dtPrecompTrivialSafe (w : ℕ) (_ : Unit) (s : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (s.frontier + 4)

private theorem realizes_dtPrecompTrivial : Realizes .exact
    dtPrecompTrivial WordEncoding.encode WordEncoding.encode
    dtPrecompTrivialSafe (fun _ _ => 0) := by
  unfold dtPrecompTrivial; realize [realizes_allocBlockDirty]
  all_goals
    repeat rw [Memory.clientState_allocBlockDirty] at *
    try simp only [Memory.clientResult_allocBlockDirty] at *
    obtain ⟨h2, hfit⟩ := h; have hfront := hmem.frontier_fits; fits

private theorem dtPrecompTrivial_spec {w r0 : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hr1 : r0 ≤ 1)
    (hfit : Fits w (s.frontier + dtPrecompCost r0)) :
    Memory.FramedTriple w s (dtPrecompTrivial ()) (dtPrecompCost r0) ∅ fun res s' =>
      Memory.WellFormed w s' ∧ s'.frontier ≤ s.frontier + dtPrecompCost r0 ∧
      HoldsDTTable r0 res s'.mem ∧ DTTableInBounds r0 res s'.frontier s'.mem := by
  have hcost_val : dtPrecompCost r0 = 64 := by simp [dtPrecompCost, hr1]
  have hfit4 : Fits w (s.frontier + 4) := hfit.of_le (by rw [hcost_val]; omega)
  have h2 : Fits w 2 := hfit4.of_le (by omega)
  let tb := s.frontier; let ep := s.frontier + 1; let S : Set ℕ := {a | s.frontier ≤ a}
  have htri : Memory.FramedTriple w s (dtPrecompTrivial ()) 6 S fun res s' =>
      res = tb ∧ s'.frontier = s.frontier + 4 ∧ s'.mem tb = ep ∧
      s'.mem ep = 0 ∧ s'.mem (ep + 1) = 0 ∧ s'.mem (ep + 2) = 0 := by
    dsimp only [dtPrecompTrivial]
    have hsS : ∀ x, s.frontier ≤ x → x ∈ S := fun _ hx => hx
    refine Memory.FramedTriple.mono (Memory.FramedTriple.allocBlockDirty_bind (c := 5)
      (hfit4.of_le (by omega)) (Memory.FramedTriple.allocBlockDirty_bind (c := 4) hfit4
        (Memory.FramedTriple.write_bind_of_mem (by dsimp only [tb]; omega) (hfit4.of_le
          (by dsimp only; omega)) (hsS _ le_rfl) (Memory.FramedTriple.write_bind_of_mem
          (by dsimp only; omega) (by fits) (hsS _ (by dsimp only; omega))
          (Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) (by fits)
            (hsS _ (by dsimp only; omega)) (Memory.FramedTriple.write_bind_of_mem
              (by dsimp only; omega) (by fits) (hsS _ (by dsimp only; omega))
              (Memory.FramedTriple.pure ⟨rfl, rfl, by update_simp, by update_simp, by update_simp,
                by update_simp⟩))))))) le_rfl fun _ _ h => h
  refine (framedTriple_above_frontier_to_empty htri).wellFormed hwf |>.mono
    (by rw [hcost_val]; omega) ?_
  rintro res s' ⟨⟨rfl, hfr, hptr, hep0, hep1, hep2⟩, hwf'⟩
  have hmaxE0 : r0.choose 2 = 0 := by match r0 with | 0 | 1 => decide | _ + 2 => omega
  have hlen0 : (maskEdgePairs r0 0).length = 0 := by
    rw [length_maskEdgePairs, hmaxE0, Finset.range_zero, Finset.filter_empty, Finset.card_empty]
  have hopt0 : optDepth (endsOfMask r0 0) = 0 :=
    optDepth_eq_zero_of_le_one (by rw [hlen0]; exact Nat.zero_le _) _
  refine ⟨hwf', by rw [hfr, hcost_val]; omega, (holdsDTTable_iff _ _ _).mpr fun mask hm => by
      rw [show mask = 0 by rw [hmaxE0] at hm; omega]
      simp only [Nat.add_zero, hptr, hep0, hlen0, hep1, hopt0]
      exact ⟨trivial, trivial, fun _ hj => absurd hj (Nat.not_lt_zero _), ⟨.leaf ∅,
        MSFTree.isComplete_leaf, (MSFDT.correct_iff _ _).mpr fun _ => by
          ext x; exact absurd (x.isLt.trans_eq hlen0) (Nat.not_lt_zero _),
        holdsCompleteTree_leaf.mpr ⟨le_rfl, by decide, by simp only [Nat.pow_zero, Nat.sub_self,
          Nat.mul_zero, Nat.add_zero, hep2, maskOfFinset, Finset.sum_empty]⟩⟩⟩,
    (dtTableInBounds_iff _ _ _ _).mpr ⟨by rw [hmaxE0, hfr]; omega, fun mask hm => by
      rw [show mask = 0 by rw [hmaxE0] at hm; omega]
      simp only [Nat.add_zero, hptr, hlen0, hep1, hfr]; omega⟩⟩

private def dtRunPrecompLoop (env : DTPrecompEnv) : Memory.Prog ℕ :=
  iterate dtProcessMaskStep env env.numMasks 0

private theorem realizes_dtRunPrecompLoop : Realizes .exact
    dtRunPrecompLoop dtPrecompEnvWords WordEncoding.encode
    (fun w env s => iterationSafe dtProcessMaskStep dtProcessMaskStepSafe w env env.numMasks 0 s)
    (fun _ _ => 0) := by
  unfold dtRunPrecompLoop; realize [realizes_dtProcessMaskStep]; exact h

private def dtPrecompMain (r0 : ℕ) : Memory.Prog ℕ := do
  let maxE := r0 * (r0 - 1) / 2; let numMasks := 1 <<< maxE
  let maxD := maxE * (maxE - 1) / 2; let maxLeaves := 1 <<< maxD
  let wsSz := 9 * maxE + 2 * maxD + 3 * maxLeaves + r0 + 1
  let tblBlk ← Memory.allocBlockDirty numMasks
  let wsBlk ← Memory.allocBlockDirty wsSz; let b := wsBlk.base
  let bufA : DTPrecompBufA := ⟨tblBlk.base, b, b + maxE, b + 2 * maxE, b + 3 * maxE, b + 4 * maxE⟩
  let bufB : DTPrecompBufB := ⟨b + 5 * maxE, b + 5 * maxE + maxD, b + 5 * maxE + 2 * maxD,
    b + 5 * maxE + 2 * maxD + maxLeaves, b + 5 * maxE + 2 * maxD + 2 * maxLeaves,
    b + 6 * maxE + 2 * maxD + 2 * maxLeaves⟩
  let bufC : DTPrecompBufC := ⟨b + 7 * maxE + 2 * maxD + 2 * maxLeaves,
    b + 8 * maxE + 2 * maxD + 2 * maxLeaves, b + 8 * maxE + 2 * maxD + 2 * maxLeaves + r0,
    b + 9 * maxE + 2 * maxD + 2 * maxLeaves + r0 + 1⟩
  let _ ← dtFillAllPairsProg ⟨bufA.r0PairA, bufA.r0PairB, r0⟩
  let _ ← dtRunPrecompLoop ⟨r0, maxE, numMasks, maxD, bufA, bufB, bufC⟩; pure tblBlk.base

private def dtPrecompMainSafe (w r0 : ℕ) (s : Memory.State) : Prop :=
  let maxE := r0 * (r0 - 1) / 2; let numMasks := 1 <<< maxE; let maxD := maxE * (maxE - 1) / 2
  let maxLeaves := 1 <<< maxD; let wsSz := 9 * maxE + 2 * maxD + 3 * maxLeaves + r0 + 1
  let s2 : Memory.State := ⟨s.mem, s.frontier + numMasks + wsSz⟩; let b := s.frontier + numMasks
  let bufA : DTPrecompBufA := ⟨s.frontier, b, b + maxE, b + 2 * maxE, b + 3 * maxE, b + 4 * maxE⟩
  let bufB : DTPrecompBufB := ⟨b + 5 * maxE, b + 5 * maxE + maxD, b + 5 * maxE + 2 * maxD,
    b + 5 * maxE + 2 * maxD + maxLeaves, b + 5 * maxE + 2 * maxD + 2 * maxLeaves,
    b + 6 * maxE + 2 * maxD + 2 * maxLeaves⟩
  let bufC : DTPrecompBufC := ⟨b + 7 * maxE + 2 * maxD + 2 * maxLeaves,
    b + 8 * maxE + 2 * maxD + 2 * maxLeaves, b + 8 * maxE + 2 * maxD + 2 * maxLeaves + r0,
    b + 9 * maxE + 2 * maxD + 2 * maxLeaves + r0 + 1⟩
  let s3 := (Memory.spec 0).clientState s2 (dtFillAllPairsProg ⟨bufA.r0PairA, bufA.r0PairB, r0⟩)
  Fits w 2 ∧ 2 ≤ r0 ∧ Fits w (r0 * (r0 - 1)) ∧ Fits w numMasks ∧ Fits w (maxE * (maxE - 1)) ∧
  Fits w maxLeaves ∧ Fits w (s.frontier + numMasks + wsSz) ∧
  dtFillAllPairsProgSafe w ⟨bufA.r0PairA, bufA.r0PairB, r0⟩ s2 ∧
  iterationSafe dtProcessMaskStep dtProcessMaskStepSafe w
    ⟨r0, maxE, numMasks, maxD, bufA, bufB, bufC⟩ numMasks 0 s3

private theorem realizes_dtPrecompMain : Realizes .exact
    dtPrecompMain WordEncoding.encode WordEncoding.encode dtPrecompMainSafe (fun _ _ => 0) := by
  unfold dtPrecompMain; realize [realizes_allocBlockDirty, realizes_dtFillAllPairsProg,
    realizes_dtRunPrecompLoop]
  all_goals
    repeat rw [Memory.clientState_allocBlockDirty] at *
    try simp only [Memory.clientResult_allocBlockDirty] at *
    obtain ⟨h2, hr2, hmul1, hnm, hmul2, hml, halloc, hap, hit⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact hit | exact hap | exact halloc.of_le (Nat.le_add_left _ _)
    | exact h2 | exact hmul1 | exact hnm | exact hmul2 | exact hml | omega
    | (have hmaxE1 : 1 ≤ d * (d - 1) / 2 :=
        Nat.div_pos (Nat.mul_le_mul hr2 (Nat.sub_le_sub_right hr2 1)) (by omega)
       have h9 : Fits w 9 := halloc.of_le (Nat.le_trans (Nat.le_mul_of_pos_right 9 hmaxE1)
         ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
           ((Nat.le_add_right _ _).trans (Nat.le_add_left _ _))))))
       have hkm : ∀ k ≤ 9, k * (d * (d - 1) / 2) ≤ 9 * (d * (d - 1) / 2) :=
         fun _ hk => Nat.mul_le_mul_right _ hk
       have h8m := hkm 8 (by decide); have h7m := hkm 7 (by decide); have h6m := hkm 6 (by decide)
       have h5m := hkm 5 (by decide); have h4m := hkm 4 (by decide); have h3m := hkm 3 (by decide)
       have h2m := hkm 2 (by decide); let L := 1 <<< (d * (d - 1) / 2 * (d * (d - 1) / 2 - 1) / 2)
       have hml2 : 2 * L ≤ 3 * L := Nat.mul_le_mul_right L (by decide)
       have hml1 : L ≤ 3 * L := Nat.le_mul_of_pos_left L (by decide)
       have hmd1 : d * (d - 1) / 2 * (d * (d - 1) / 2 - 1) / 2 ≤ 2 * (d * (d - 1) / 2 *
         (d * (d - 1) / 2 - 1) / 2) := Nat.le_mul_of_pos_left _ (by decide)
       first | exact hmaxE1 | fits [hmul1, hnm, hmul2, hml, halloc])

private theorem dtPrecompMain_loop_spec {w baseFront : ℕ} {env : DTPrecompEnv}
    {s s0 : Memory.State} (h2 : Fits w 2) (hfit : Fits w (s.frontier + dtPrecompCost env.r0))
    (hlay : DTEnvLayout env baseFront) (hs_le : env.bufA.tableBase = s.frontier)
    (hbf_le : s0.frontier = baseFront)
    (hfr_add : s0.frontier + env.numMasks * 2 ^ (2 ^ (2 * env.r0 ^ 4 + 5)) ≤
      s.frontier + dtPrecompCost env.r0)
    (hfit_nm : Fits w env.numMasks) (hwf0 : Memory.WellFormed w s0)
    (hpairs0 : ∀ pk (hpk : pk < env.r0.choose 2),
      s0.mem (env.bufA.r0PairA + pk) = ((allPairs env.r0)[pk]'(length_allPairs _ ▸ hpk)).1.val ∧
      s0.mem (env.bufA.r0PairB + pk) = ((allPairs env.r0)[pk]'(length_allPairs _ ▸ hpk)).2.val) :
    let S : Set ℕ := {a | s.frontier ≤ a}
    iterationSafe dtProcessMaskStep dtProcessMaskStepSafe w env env.numMasks 0 s0 ∧
    Memory.FramedTriple w s0 (iterate dtProcessMaskStep env env.numMasks 0)
      (env.numMasks * 2 ^ (2 ^ (2 * env.r0 ^ 4 + 11))) S fun _ s4 =>
      Memory.WellFormed w s4 ∧ s4.frontier ≤ s.frontier + dtPrecompCost env.r0 ∧
      HoldsDTTable env.r0 env.bufA.tableBase s4.mem ∧
      DTTableInBounds env.r0 env.bufA.tableBase s4.frontier s4.mem := by
  have hr2 := hlay.r0_ge; have hmaxE := hlay.2.1; have hnm := hlay.2.2.1; have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9, hbb10,
    hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  have hfit_cost := hfit.of_le (Nat.le_add_left (dtPrecompCost env.r0) s.frontier)
  let S : Set ℕ := {a | s.frontier ≤ a}
  let inv (k st : ℕ) (t : Memory.State) : Prop := st = k ∧ s0.frontier ≤ t.frontier ∧
    t.frontier ≤ s0.frontier + k * 2 ^ (2 ^ (2 * env.r0 ^ 4 + 5)) ∧ Memory.WellFormed w t ∧
    (∀ pk (hpk : pk < env.r0.choose 2),
      t.mem (env.bufA.r0PairA + pk) = ((allPairs env.r0)[pk]'(length_allPairs _ ▸ hpk)).1.val ∧
      t.mem (env.bufA.r0PairB + pk) = ((allPairs env.r0)[pk]'(length_allPairs _ ▸ hpk)).2.val) ∧
    (∀ m < k, DTMaskEntryValid env.r0 env.bufA.tableBase m (optDepth (endsOfMask env.r0 m)) t ∧
      env.bufA.tableBase + m < env.bufA.edgeU ∧ s0.frontier ≤ t.mem (env.bufA.tableBase + m))
  have hstep : ∀ k < env.numMasks, ∀ st t, inv k st t →
      dtProcessMaskStepSafe w (env, st) t ∧
      Memory.FramedTriple w t (dtProcessMaskStep (env, st)) (2 ^ (2 ^ (2 * env.r0 ^ 4 + 11))) S
        (inv (k + 1)) := by
    intro k hk st t ⟨hst_eq, ht_ge, ht_le, hwt, hpairs_t, hprev_m⟩; subst st
    have hfit_step : Fits w (t.frontier + 2 ^ (2 ^ (2 * env.r0 ^ 4 + 5))) := hfit.of_le (by
      have := Nat.mul_le_mul_right (2 ^ (2 ^ (2 * env.r0 ^ 4 + 5)))
        (by omega : k + 1 ≤ env.numMasks)
      rw [Nat.add_mul, Nat.one_mul] at this; omega)
    obtain ⟨hpm_safe, hpm_tri⟩ := dtProcessMaskStep_spec (w := w) (baseFront := baseFront)
      (mask := k) h2 hwt hlay (hbf_le ▸ ht_ge) hk hfit_nm hfit_cost hfit_step hpairs_t
    let St := {a | (env.bufA.edgeU ≤ a ∧ a < baseFront) ∨
      a = env.bufA.tableBase + k ∨ t.frontier ≤ a}
    refine ⟨hpm_safe, ((framedTriple_with_modifies hpm_tri).frame_mono fun a ha => by
      simp only [S, Set.mem_ofPred_eq] at ha ⊢; rcases ha with ⟨_, _⟩ | rfl | _ <;> omega).mono
      le_rfl fun a' t' ⟨hpm_mod, hpm_res, hpm_fr_ge, hpm_fr_le, hpm_wf, hpm_val, hpm_ptr⟩ => ?_⟩
    have ht'_pres : ∀ a < t.frontier, a ∉ St → t'.mem a = t.mem a :=
      fun a ha haS => hpm_mod.mem_eq_of_not_mem ha haS
    refine ⟨hpm_res, ht_ge.trans hpm_fr_ge, by rw [Nat.add_mul, Nat.one_mul]; omega, hpm_wf,
      fun pk hpk =>
        ⟨(ht'_pres _ (by omega) (by simp only [St, Set.mem_ofPred_eq]; omega)).trans
            (hpairs_t pk hpk).1,
         (ht'_pres _ (by omega) (by simp only [St, Set.mem_ofPred_eq]; omega)).trans
            (hpairs_t pk hpk).2⟩,
      fun m hm => if hmk : m < k then by
          obtain ⟨hm_v, hm_lt, hm_p⟩ := hprev_m m hmk
          have hptr_eq := ht'_pres (env.bufA.tableBase + m) (by omega)
            (by simp only [St, Set.mem_ofPred_eq]; omega)
          exact ⟨dtMaskEntryValid_preserve hm_v hpm_fr_ge hptr_eq fun a _ ha2 =>
            ht'_pres a ha2 (by simp only [St, Set.mem_ofPred_eq]; omega),
            hm_lt, hptr_eq.symm ▸ hm_p⟩
        else by
          have hme : m = k := by omega
          subst hme; exact ⟨hpm_val, by omega, ht_ge.trans hpm_ptr⟩⟩
  obtain ⟨hpm_safe, hv, hc, hmod, ie⟩ := iterate_potential_spec dtProcessMaskStep
    dtProcessMaskStepSafe w env (2 ^ (2 ^ (2 * env.r0 ^ 4 + 11))) env.numMasks inv
    (fun _ _ _ => 0) S (fun k hk a s ha => let ⟨hs', ht'⟩ := hstep k hk a s ha
      let ⟨hv', hc', hm', hi'⟩ := framedTriple_iff_realization.mp ht'
      ⟨hs', hv', by omega, hm', hi'⟩) 0 s0
    ⟨rfl, le_rfl, by simp, hwf0, hpairs0, fun _ hm => absurd hm (Nat.not_lt_zero _)⟩
  refine ⟨hpm_safe, framedTriple_iff_realization.mpr ⟨hv, by
      simpa only [Nat.add_zero, Nat.zero_add, Nat.mul_comm] using hc, hmod, ie.2.2.2.1,
    ie.2.2.1.trans hfr_add, (holdsDTTable_iff _ _ _).mpr fun mask hm => by
      obtain ⟨he_v, hd_v, hp_v, hT, _⟩ := (ie.2.2.2.2.2 mask (by rw [hnm, hmaxE]; exact hm)).1
      dsimp only; rw [hd_v]; exact ⟨he_v, rfl, hp_v, hT⟩,
    (dtTableInBounds_iff _ _ _ _).mpr ⟨by have := ie.2.1; rw [← hmaxE, ← hnm]; omega,
      fun mask hm => let ⟨_, hd_v, _, _, hb⟩ := (ie.2.2.2.2.2 mask (by rw [hnm, hmaxE]; exact hm)).1
        by dsimp only; rw [hd_v]; exact hb⟩⟩⟩

private theorem dtPrecompMain_spec {w r0 : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hr2 : 2 ≤ r0) (hfit : Fits w (s.frontier + dtPrecompCost r0)) :
    dtPrecompMainSafe w r0 s ∧
    Memory.FramedTriple w s (dtPrecompMain r0) (dtPrecompCost r0) ∅ fun res s' =>
      Memory.WellFormed w s' ∧ s'.frontier ≤ s.frontier + dtPrecompCost r0 ∧
      HoldsDTTable r0 res s'.mem ∧ DTTableInBounds r0 res s'.frontier s'.mem := by
  have h2 : Fits w 2 := hfit.of_le (by have := dtPrecompCost_ge_64 r0; omega)
  have hmaxE_eq := (Nat.choose_two_right r0).symm
  let maxE := r0.choose 2; let numMasks := 2 ^ maxE; let maxD := maxE.choose 2
  let maxLeaves := 2 ^ maxD; let wsSz := 9 * maxE + 2 * maxD + 3 * maxLeaves + r0 + 1
  have hmaxE1 : 1 ≤ r0.choose 2 := Nat.choose_pos hr2
  have har := dtPrecompArithBounds (r0 := r0) (e := maxE) hr2 le_rfl
  have har_tot_fr := har.2.2.2.2.2.2.1; have har_tot_cost := har.2.2.2.2.2.2.2; clear har
  have hfit_alloc : Fits w (s.frontier + numMasks + wsSz) :=
    hfit.of_le (by dsimp only [wsSz, numMasks, maxLeaves, maxD, maxE] at *; omega)
  let b := s.frontier + numMasks
  let bufA : DTPrecompBufA := ⟨s.frontier, b, b + maxE, b + 2 * maxE, b + 3 * maxE, b + 4 * maxE⟩
  let bufB : DTPrecompBufB := ⟨b + 5 * maxE, b + 5 * maxE + maxD, b + 5 * maxE + 2 * maxD,
    b + 5 * maxE + 2 * maxD + maxLeaves, b + 5 * maxE + 2 * maxD + 2 * maxLeaves,
    b + 6 * maxE + 2 * maxD + 2 * maxLeaves⟩
  let bufC : DTPrecompBufC := ⟨b + 7 * maxE + 2 * maxD + 2 * maxLeaves,
    b + 8 * maxE + 2 * maxD + 2 * maxLeaves, b + 8 * maxE + 2 * maxD + 2 * maxLeaves + r0,
    b + 9 * maxE + 2 * maxD + 2 * maxLeaves + r0 + 1⟩
  let env : DTPrecompEnv := ⟨r0, maxE, numMasks, maxD, bufA, bufB, bufC⟩
  have hlay : DTEnvLayout env (s.frontier + numMasks + wsSz) := by
    refine ⟨hr2, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, rfl,
      ?_, ?_⟩ <;> (dsimp only [env, bufA, bufB, bufC, wsSz, maxLeaves]; omega)
  let S : Set ℕ := {a | s.frontier ≤ a}
  have hfr_add : s.frontier + numMasks + wsSz + numMasks * 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) ≤
      s.frontier + dtPrecompCost r0 := by
    dsimp only [wsSz, numMasks, maxLeaves, maxD, maxE] at har_tot_fr ⊢; omega
  have hfit_nm : Fits w numMasks := hfit_alloc.of_le (by dsimp only [wsSz]; omega)
  have h2mul : ∀ n, n * (n - 1) = 2 * (n * (n - 1) / 2) := fun n => by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← Nat.two_mul, mul_assoc]; simp
    · rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_left_comm]; simp
  have hfit_ws : Fits w wsSz := hfit_alloc.of_le (Nat.le_add_left _ _)
  let s2 : Memory.State := ⟨s.mem, s.frontier + numMasks + wsSz⟩
  have hap_safe : dtFillAllPairsProgSafe w ⟨bufA.r0PairA, bufA.r0PairB, r0⟩ s2 :=
    (dtFillAllPairsProgSafe_iff _ _ _).mpr ⟨h2, hfit_ws.of_le (by dsimp only [wsSz]; omega),
      hfit_ws.of_le (by dsimp only [wsSz]; omega), fun _ => by dsimp only [bufA, s2]; omega, by
        dsimp only [bufA, s2]; omega, by dsimp only [bufA, s2]; omega, .inl (by
          dsimp only [bufA]; omega)⟩
  have hap_tri := dtFillAllPairsProg_spec (s := s2) ⟨hfit_alloc, hwf.mem_fits⟩ hap_safe
  let s3 := (Memory.spec 0).clientState s2 (dtFillAllPairsProg ⟨bufA.r0PairA, bufA.r0PairB, r0⟩)
  obtain ⟨_, _, _, _, hfp_fr, hfp_wf, hfp_arr⟩ := framedTriple_iff_realization.mp hap_tri
  obtain ⟨hloop_safe, hloop_tri⟩ := dtPrecompMain_loop_spec (s := s) (s0 := s3) h2 hfit hlay rfl
    hfp_fr (by dsimp only [env]; rw [hfp_fr]; exact hfr_add) hfit_nm hfp_wf hfp_arr
  have hshift_eq : ∀ n, 1 <<< n = 2 ^ n := fun n => by rw [Nat.shiftLeft_eq, Nat.one_mul]
  refine ⟨by dsimp only [dtPrecompMainSafe]; simp only [← Nat.choose_two_right, hshift_eq]; exact
      ⟨h2, hr2, (by rw [h2mul r0, hmaxE_eq]; exact hfit_ws.of_le (by dsimp only [wsSz]; omega)),
        hfit_nm, (by rw [h2mul (r0.choose 2), ← Nat.choose_two_right]; exact hfit_ws.of_le (by
          dsimp only [wsSz, maxLeaves, maxD, maxE]; omega)), hfit_ws.of_le (by
          dsimp only [wsSz, maxLeaves, maxD, maxE]; omega), hfit_alloc, hap_safe, hloop_safe⟩,
    framedTriple_above_frontier_to_empty (by
      have hcost_le : r0 * (1 + 2 * r0) + (env.numMasks * 2 ^ (2 ^ (2 * env.r0 ^ 4 + 11)) + 0) +
          1 + 1 ≤ dtPrecompCost r0 := by dsimp only [env, numMasks, maxE] at har_tot_cost ⊢; omega
      dsimp only [dtPrecompMain, dtRunPrecompLoop]; simp only [← Nat.choose_two_right, hshift_eq]
      refine Memory.FramedTriple.mono (Memory.FramedTriple.allocBlockDirty_bind
        (hfit_alloc.of_le (Nat.le_add_right _ _)) (Memory.FramedTriple.allocBlockDirty_bind
          hfit_alloc (framedTriple_bind_client hap_tri (fun a ha => by
            dsimp only [bufA, b] at ha; simp only [Set.mem_union, Set.mem_Ico] at ha
            rcases ha with ⟨hlo, _⟩ | ⟨hlo, _⟩ <;> [exact (Nat.le_add_right _ _).trans hlo;
              exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans hlo])
            Set.Subset.rfl le_rfl fun _ _ => framedTriple_bind_client hloop_tri Set.Subset.rfl
              Set.Subset.rfl le_rfl fun h _ => Memory.FramedTriple.pure h)))
        hcost_le fun _ _ h => h)⟩

/-! ## Section 4: Public `precomputeDTProg` Entry Point and Specifications -/

/-- Builds the optimal MSF decision-tree lookup table covering all simple graphs on `v ≤ r0`
vertices in `O(dtPrecompCost r0)` time and frontier space. -/
def precomputeDTProg (r0 : ℕ) : Memory.Prog ℕ :=
  if r0 ≤ 1 then dtPrecompTrivial () else dtPrecompMain r0

/-- Safe Word-RAM precondition for `precomputeDTProg`: the allocated table and scratch workspace
fit inside `w`-bit addresses (`Fits w (s.frontier + dtPrecompCost r0)`). -/
def precomputeDTProgSafe (w r0 : ℕ) (s : Memory.State) : Prop :=
  Fits w (s.frontier + dtPrecompCost r0)

/-- Equivalence exposing the definition of `precomputeDTProgSafe`. -/
theorem precomputeDTProgSafe_iff (w r0 : ℕ) (s : Memory.State) :
    precomputeDTProgSafe w r0 s ↔ Fits w (s.frontier + dtPrecompCost r0) := Iff.rfl

private theorem realizes_precomputeDTProg_raw : Realizes .exact
    precomputeDTProg WordEncoding.encode WordEncoding.encode
    (fun w r0 s => if r0 ≤ 1 then dtPrecompTrivialSafe w () s else dtPrecompMainSafe w r0 s)
    (fun _ _ => 0) := by
  unfold precomputeDTProg; realize [realizes_dtPrecompTrivial, realizes_dtPrecompMain]
  all_goals split_ifs at h <;> first | exact h | omega | (obtain ⟨h2, _⟩ := h; fits)

/-- Framed specification for `precomputeDTProg`: computes a `HoldsDTTable` and `DTTableInBounds`
table in `dtPrecompCost r0` time and frontier space without modifying existing memory below
`s.frontier`. -/
theorem precomputeDTProg_spec {w r0 : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : precomputeDTProgSafe w r0 s) :
    Memory.FramedTriple w s (precomputeDTProg r0) (dtPrecompCost r0) ∅ fun res s' =>
      Memory.WellFormed w s' ∧ s'.frontier ≤ s.frontier + dtPrecompCost r0 ∧
      HoldsDTTable r0 res s'.mem ∧ DTTableInBounds r0 res s'.frontier s'.mem := by
  by_cases hr1 : r0 ≤ 1 <;> dsimp only [precomputeDTProg] <;> simp only [hr1, ↓reduceIte]
  · exact dtPrecompTrivial_spec hwf hr1 hsafe
  · exact (dtPrecompMain_spec hwf (by omega) hsafe).2

/-- `precomputeDTProg` is uniformly realized in `O(dtPrecompCost r0)` time with `work = 0`. -/
theorem realizes_precomputeDTProg : Realizes .exact
    precomputeDTProg WordEncoding.encode WordEncoding.encode
    precomputeDTProgSafe (fun _ _ => 0) := by
  refine realizes_precomputeDTProg_raw.consequence (fun w r0 s _ hwf hs => ?_) (fun _ _ => le_rfl)
  by_cases hr1 : r0 ≤ 1 <;> simp only [hr1, ↓reduceIte]
  · have hfit4 : Fits w (s.frontier + 4) :=
      hs.of_le (by simp only [dtPrecompCost, hr1, ↓reduceIte]; omega)
    exact ⟨hfit4.of_le (by omega), hfit4⟩
  · exact (dtPrecompMain_spec hwf (by omega) hs).1

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

end
