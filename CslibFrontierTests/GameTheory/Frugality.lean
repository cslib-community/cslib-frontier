/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.Frugality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Frugality in procurement auctions tests

Non-vacuous client checks and boundary witnesses for
`CslibFrontier.GameTheory.Mechanism.Frugality`:

* two parallel `3`-edge paths on costs `(0, 0, 0; 1, 1, 1)`: VCG pays `9 = 3 * cheapestNash`
  ([HartlineKarlin2007], p. 351), while `sqrtWeightedPathMechanism 3 3` is DSIC, IR, pays losers
  zero, and has frugality ratio at most `3`;
* asymmetric two disjoint paths `(n = 4, n' = 1)`: VCG pays `4` against `cheapestNash = 1`
  (failing frugality ratio `3`), whereas `sqrtWeightedPathMechanism 4 1` has frugality ratio at
  most `√4 = 2` (matching the Theorem 13.54 lower bound `1` within factor `2`) and pays `2` on the
  `0`/`1` profile;
* `K₃` triangle spanning-tree auction ([HartlineKarlin2007], Exercise 13.12, p. 361):
  `IsMatroidBaseFamily`, `VCG` frugality ratio `1`, and exact `vcgTotalPay = cheapestNash = 2` on
  edge costs `(0, 0, 1)`; boundary witness showing the single-edge graph `K₂` has a bridge and is
  not monopoly-free;
* non-matroid equicardinal family `{{0, 1}, {2, 3}}` on `Fin 4`: fails `IsMatroidBaseFamily` and
  VCG pays `4 > 2 = cheapestNash` on `(0, 0, 1, 1)`;
* non-antichain boundary witness `{{0}, {1}, {0, 2}}` on `Fin 3`: fails `IsMatroidBaseFamily`,
  yet VCG still satisfies `HasFrugalityRatioLe _ _ 1`, showing why `IsAntichain` is required in
  the converse of Theorem 13.53.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.Frugality

open Finset
open Cslib.GameTheory.Mechanism.Frugality

/-! ### Two parallel `n`-edge paths (`n = 3` and asymmetric `n = 4, n' = 1`) -/

/-- On two vertex-disjoint `3`-edge paths with costs `0` vs `1`, VCG pays `9` while
`cheapestNash = 3`, and `sqrtWeightedPathMechanism 3 3` pays `≤ 3 * cheapestNash`. -/
private theorem twoDisjointPaths_three_three :
    let c : Fin 3 ⊕ Fin 3 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
    (vcgMechanism (twoDisjointPaths 3 3) (twoDisjointPaths_nonempty 3 3)
        (twoDisjointPaths_isMonopolyFree 3 3)).totalPay c = 9 ∧
      cheapestNash (twoDisjointPaths 3 3) c = 3 ∧
      (sqrtWeightedPathMechanism 3 3).totalPay c ≤ 3 * cheapestNash (twoDisjointPaths 3 3) c := by
  intro c
  obtain ⟨hvcg, hcn⟩ :=
    vcgTotalPay_twoDisjointPaths_zero_one (n := 3) (n' := 3) (by omega) (by omega)
  have hsqrt :=
    sqrtWeightedPathMechanism_hasFrugalityRatioLe (n := 3) (n' := 3) (by omega) (by omega)
  have hc0 : 0 ≤ c := fun x => by cases x <;> norm_num [c]
  have h3 : Real.sqrt ((3 : ℝ) * (3 : ℝ)) = 3 := by
    rw [show (3 : ℝ) * (3 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨by norm_num at hvcg; exact hvcg, by norm_num at hcn; exact hcn, ?_⟩
  have hle := hsqrt.2 c hc0
  rw [show ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) = (3 : ℝ) * (3 : ℝ) by norm_num, h3] at hle
  exact hle

/-- On asymmetric two disjoint paths `(n = 4, n' = 1)`:
1. VCG pays `4` against `cheapestNash = 1` on the `0`/`1` profile (so VCG fails frugality `3`);
2. `sqrtWeightedPathMechanism 4 1` is DSIC, IR, pays losers zero, and achieves frugality ratio at
   most `√4 = 2`, paying `2` on the `0`/`1` profile;
3. By Theorem 13.54, every DSIC, IR, losers-paid-zero mechanism has frugality ratio at least `1`. -/
private theorem twoDisjointPaths_four_one :
    let c : Fin 4 ⊕ Fin 1 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
    (vcgMechanism (twoDisjointPaths 4 1) (twoDisjointPaths_nonempty 4 1)
        (twoDisjointPaths_isMonopolyFree 4 1)).totalPay c = 4 ∧
      ¬ HasFrugalityRatioLe (twoDisjointPaths 4 1)
          (vcgMechanism (twoDisjointPaths 4 1) (twoDisjointPaths_nonempty 4 1)
            (twoDisjointPaths_isMonopolyFree 4 1)) 3 ∧
      HasFrugalityRatioLe (twoDisjointPaths 4 1) (sqrtWeightedPathMechanism 4 1) 2 ∧
      (sqrtWeightedPathMechanism 4 1).totalPay c = 2 ∧
      ∀ (M : ProcurementMechanism (Fin 4 ⊕ Fin 1) (twoDisjointPaths 4 1)) (ρ : ℝ),
        M.IsDSIC → M.IsIR → M.LosersPaidZero →
        HasFrugalityRatioLe (twoDisjointPaths 4 1) M ρ → 1 ≤ ρ := by
  intro c
  obtain ⟨hvcg, hcn⟩ :=
    vcgTotalPay_twoDisjointPaths_zero_one (n := 4) (n' := 1) (by omega) (by omega)
  have hc0 : 0 ≤ c := fun x => by cases x <;> norm_num [c]
  have h41 : Real.sqrt ((4 : ℝ) * (1 : ℝ)) = 2 := by
    rw [show (4 : ℝ) * (1 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
  have hvcg4 : (vcgMechanism (twoDisjointPaths 4 1) (twoDisjointPaths_nonempty 4 1)
      (twoDisjointPaths_isMonopolyFree 4 1)).totalPay c = 4 := by
    norm_num at hvcg; exact hvcg
  have hcn1 : cheapestNash (twoDisjointPaths 4 1) c = 1 := by
    norm_num at hcn; exact hcn
  have hnot3 : ¬ HasFrugalityRatioLe (twoDisjointPaths 4 1)
      (vcgMechanism (twoDisjointPaths 4 1) (twoDisjointPaths_nonempty 4 1)
        (twoDisjointPaths_isMonopolyFree 4 1)) 3 := by
    intro h3
    have hle := h3.2 c hc0
    rw [hvcg4, hcn1] at hle
    linarith
  have hsw2 : HasFrugalityRatioLe (twoDisjointPaths 4 1) (sqrtWeightedPathMechanism 4 1) 2 := by
    have h := sqrtWeightedPathMechanism_hasFrugalityRatioLe (n := 4) (n' := 1) (by omega) (by omega)
    simpa only [Nat.cast_ofNat, Nat.cast_one, h41] using h
  have hsw_val : (sqrtWeightedPathMechanism 4 1).totalPay c = 2 := by
    rw [(sqrtWeightedPathMechanism 4 1).totalPay_eq_sum_alloc
      (sqrtWeightedPathMechanism_losersPaidZero 4 1) hc0]
    simp only [sqrtWeightedPathMechanism, c, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.cast_ofNat, Nat.cast_one, hsqrt4, hsqrt1, mul_zero, one_mul]
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    simp only [h01, ↓reduceIte, sum_leftPath, sub_zero]
    norm_num
  refine ⟨hvcg4, hnot3, hsw2, hsw_val, fun M ρ hD hI hZ hρ => ?_⟩
  have hlb := le_of_hasFrugalityRatioLe_twoDisjointPaths (n := 4) (n' := 1)
    (by omega) (by omega) hD hI hZ hρ
  simp only [Nat.cast_ofNat, Nat.cast_one, h41] at hlb
  linarith

/-! ### `K₃` triangle spanning-tree auction (Exercise 13.12) and `K₂` bridge boundary -/

private theorem completeGraph_fin3_connected : (⊤ : SimpleGraph (Fin 3)).Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl u
  · exact SimpleGraph.Adj.reachable huv

private theorem completeGraph_fin3_not_isBridge (e : Sym2 (Fin 3)) :
    ¬ (⊤ : SimpleGraph (Fin 3)).IsBridge e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.isBridge_iff, not_not]
    fin_cases u <;> fin_cases v
    · exact SimpleGraph.Reachable.refl 0
    · exact (SimpleGraph.Adj.reachable (G := (⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)})
        (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).Adj 0 2)).trans
        (SimpleGraph.Adj.reachable
          (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).Adj 2 1))
    · exact (SimpleGraph.Adj.reachable (G := (⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 2)})
        (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 2)}).Adj 0 1)).trans
        (SimpleGraph.Adj.reachable
          (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 2)}).Adj 1 2))
    · exact (SimpleGraph.Adj.reachable (G := (⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 0)})
        (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 0)}).Adj 1 2)).trans
        (SimpleGraph.Adj.reachable
          (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 0)}).Adj 2 0))
    · exact SimpleGraph.Reachable.refl 1
    · exact (SimpleGraph.Adj.reachable (G := (⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 2)})
        (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 2)}).Adj 1 0)).trans
        (SimpleGraph.Adj.reachable
          (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(1, 2)}).Adj 0 2))
    · exact (SimpleGraph.Adj.reachable (G := (⊤ : SimpleGraph (Fin 3)).deleteEdges {s(2, 0)})
        (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(2, 0)}).Adj 2 1)).trans
        (SimpleGraph.Adj.reachable
          (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(2, 0)}).Adj 1 0))
    · exact (SimpleGraph.Adj.reachable (G := (⊤ : SimpleGraph (Fin 3)).deleteEdges {s(2, 1)})
        (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(2, 1)}).Adj 2 0)).trans
        (SimpleGraph.Adj.reachable
          (by simp : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(2, 1)}).Adj 0 1))
    · exact SimpleGraph.Reachable.refl 2

/-- On the triangle `K₃`, the spanning trees form a monopoly-free matroid base family, VCG has
frugality ratio `1`, and on edge costs `c(s(0, 1)) = 0`, `c(s(1, 2)) = 0`, `c(s(0, 2)) = 1` both
`vcgTotalPay` and `cheapestNash` equal `2`. -/
private theorem triangle_spanningTree_vcg_eq_two :
    let G : SimpleGraph (Fin 3) := ⊤
    let hconn := completeGraph_fin3_connected
    let hbr := completeGraph_fin3_not_isBridge
    let c : G.edgeSet → ℝ := fun e => if e.val = s((0 : Fin 3), 2) then 1 else 0
    IsMatroidBaseFamily (spanningTreeFamily G) ∧
      HasFrugalityRatioLe (spanningTreeFamily G)
        (vcgMechanism (spanningTreeFamily G) (spanningTreeFamily_nonempty hconn)
          ((isMonopolyFree_spanningTreeFamily_iff hconn).2 hbr)) 1 ∧
      (vcgMechanism (spanningTreeFamily G) (spanningTreeFamily_nonempty hconn)
        ((isMonopolyFree_spanningTreeFamily_iff hconn).2 hbr)).totalPay c = 2 ∧
      cheapestNash (spanningTreeFamily G) c = 2 := by
  intro G hconn hbr c
  have hmat := spanningTreeFamily_isMatroidBaseFamily hconn
  have hmono := (isMonopolyFree_spanningTreeFamily_iff hconn).2 hbr
  have h1 := vcg_spanningTree_hasFrugalityRatioLe_one hconn hbr
  have heq := vcg_spanningTree_totalPay_eq_cheapestNash hconn hbr c
  let e01 : G.edgeSet := ⟨s(0, 1), by simp [G]⟩
  let e12 : G.edgeSet := ⟨s(1, 2), by simp [G]⟩
  let e02 : G.edgeSet := ⟨s(0, 2), by simp [G]⟩
  let S0 : Finset G.edgeSet := {e01, e12}
  let S1 : Finset G.edgeSet := {e01, e02}
  let S2 : Finset G.edgeSet := {e12, e02}
  have htree_of_pair : ∀ (a b d : Fin 3) (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d),
      ({⟨s(a, b), (G.mem_edgeSet).2 hab⟩, ⟨s(b, d), (G.mem_edgeSet).2 hbd⟩} : Finset G.edgeSet) ∈
        spanningTreeFamily G := by
    classical
    intro a b d hab hbd had
    rw [mem_spanningTreeFamily_iff]
    set S : Finset G.edgeSet :=
      {⟨s(a, b), (G.mem_edgeSet).2 hab⟩, ⟨s(b, d), (G.mem_edgeSet).2 hbd⟩}
    refine ⟨fun _ _ h => by rw [spanningTreeSubgraph, SimpleGraph.fromEdgeSet_adj] at h; exact h.2,
      ?_⟩
    rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    have hab_adj : (spanningTreeSubgraph S).Adj a b := by
      rw [spanningTreeSubgraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨⟨s(a, b), (G.mem_edgeSet).2 hab⟩, by simp [S], rfl⟩, hab⟩
    have hbd_adj : (spanningTreeSubgraph S).Adj b d := by
      rw [spanningTreeSubgraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨⟨s(b, d), (G.mem_edgeSet).2 hbd⟩, by simp [S], rfl⟩, hbd⟩
    have hconnS : (spanningTreeSubgraph S).Connected := by
      refine ⟨fun x y => ?_⟩
      have hreach_b : ∀ z : Fin 3, (spanningTreeSubgraph S).Reachable b z := fun z => by
        have htri : z = a ∨ z = b ∨ z = d := by omega
        rcases htri with hz | hz | hz
        · rw [hz]; exact hab_adj.symm.reachable
        · rw [hz]
        · rw [hz]; exact hbd_adj.reachable
      exact (hreach_b x).symm.trans (hreach_b y)
    have hcardS : (spanningTreeSubgraph S).edgeFinset.card + 1 = Fintype.card (Fin 3) := by
      have hEq : (spanningTreeSubgraph S).edgeFinset = {s(a, b), s(b, d)} := by
        rw [← Finset.coe_inj, SimpleGraph.coe_edgeFinset, spanningTreeSubgraph,
          SimpleGraph.edgeSet_fromEdgeSet]
        ext z
        simp only [Set.mem_sdiff, Set.mem_image, Finset.mem_coe, S, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨w, rfl | rfl, rfl⟩, _⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨⟨⟨s(a, b), (G.mem_edgeSet).2 hab⟩, Or.inl rfl, rfl⟩, by simpa using hab⟩
          · exact ⟨⟨⟨s(b, d), (G.mem_edgeSet).2 hbd⟩, Or.inr rfl, rfl⟩, by simpa using hbd⟩
      have hne_ab_bd : s(a, b) ≠ s(b, d) := by
        intro hEq'
        rcases Sym2.eq_iff.1 hEq' with ⟨rfl, _⟩ | ⟨h1, _⟩
        · exact hab rfl
        · exact had h1
      rw [hEq, Finset.card_pair hne_ab_bd, Fintype.card_fin]
    exact ⟨hconnS, hcardS⟩
  have hS0 : S0 ∈ spanningTreeFamily G := htree_of_pair 0 1 2 (by decide) (by decide) (by decide)
  have hS1 : S1 ∈ spanningTreeFamily G := by
    have h := htree_of_pair 1 0 2 (by decide) (by decide) (by decide)
    convert h using 1
    ext ⟨z, hz⟩
    simp only [S1, e01, e02, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
    rw [Sym2.eq_swap (a := (1 : Fin 3)) (b := 0)]
  have hS2 : S2 ∈ spanningTreeFamily G := by
    have h := htree_of_pair 1 2 0 (by decide) (by decide) (by decide)
    convert h using 1
    ext ⟨z, hz⟩
    simp only [S2, e12, e02, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
    rw [Sym2.eq_swap (a := (2 : Fin 3)) (b := 0)]
  have he01_ne_e12 : e01 ≠ e12 := by intro h; have := congrArg Subtype.val h; revert this; decide
  have he01_ne_e02 : e01 ≠ e02 := by intro h; have := congrArg Subtype.val h; revert this; decide
  have he12_ne_e02 : e12 ≠ e02 := by intro h; have := congrArg Subtype.val h; revert this; decide
  let b : G.edgeSet → ℝ := fun _ => 1
  have hnash : IsPayYourBidNash (spanningTreeFamily G) c b S0 := by
    have hcard2 : ∀ T ∈ spanningTreeFamily G, T.card = 2 := fun T hT => by
      have h := hmat.card_eq hT hS0
      simpa only [S0, Finset.card_pair he01_ne_e12] using h
    refine ⟨hS0, fun T hT => ?_, fun e _ => ?_, fun e he => ?_, fun e he => ?_⟩
    · simp only [b, Finset.sum_const, nsmul_eq_mul, mul_one, hcard2 T hT, S0,
        Finset.card_pair he01_ne_e12, le_rfl]
    · simp only [b, c]; split_ifs <;> norm_num
    · have he_eq : e = e02 := by
        rcases e with ⟨z, hz⟩
        induction z using Sym2.ind with
        | _ u v =>
          fin_cases u <;> fin_cases v
          · simp [G] at hz
          · exact absurd (Finset.mem_insert_self e01 {e12}) he
          · rfl
          · have : (⟨s(1, 0), hz⟩ : G.edgeSet) = e01 := Subtype.ext Sym2.eq_swap
            exact absurd (this ▸ Finset.mem_insert_self e01 {e12}) he
          · simp [G] at hz
          · exact absurd (Finset.mem_insert_of_mem (Finset.mem_singleton_self e12)) he
          · exact Subtype.ext Sym2.eq_swap
          · have : (⟨s(2, 1), hz⟩ : G.edgeSet) = e12 := Subtype.ext Sym2.eq_swap
            exact absurd (this ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self e12)) he
          · simp [G] at hz
      subst he_eq
      simp [b, c, e02]
    · simp only [S0, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · refine ⟨S2, hS2, ?_, ?_⟩
        · simp [S2, he01_ne_e12, he01_ne_e02]
        · simp [b, S0, S2, Finset.card_pair he01_ne_e12, Finset.card_pair he12_ne_e02]
      · refine ⟨S1, hS1, ?_, ?_⟩
        · simp [S1, he01_ne_e12.symm, he12_ne_e02]
        · simp [b, S0, S1, Finset.card_pair he01_ne_e12, Finset.card_pair he01_ne_e02]
  have htot2 :
      (vcgMechanism (spanningTreeFamily G) (spanningTreeFamily_nonempty hconn) hmono).totalPay c =
        2 := by
    have hsum := sum_eq_vcgTotalPay_of_isPayYourBidNash hmat hmono hnash
    rw [← hsum]
    simp only [b, S0, Finset.sum_const, Finset.card_pair he01_ne_e12, nsmul_eq_mul, mul_one]
    norm_num
  exact ⟨hmat, h1, htot2, heq ▸ htot2⟩

/-- Boundary witness: `K₂` (`⊤ : SimpleGraph (Fin 2)`) has a bridge, so its spanning-tree family
is not monopoly-free. -/
private theorem completeGraph_fin2_not_monopolyFree :
    ¬ IsMonopolyFree (spanningTreeFamily (⊤ : SimpleGraph (Fin 2))) := by
  have hconn : (⊤ : SimpleGraph (Fin 2)).Connected := ⟨fun u v => by
    by_cases huv : u = v
    · subst huv; exact SimpleGraph.Reachable.refl u
    · exact SimpleGraph.Adj.reachable huv⟩
  rw [isMonopolyFree_spanningTreeFamily_iff hconn]
  push Not
  refine ⟨s(0, 1), ?_⟩
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  have hadj : ∀ x y : Fin 2, ¬ ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(0, 1)}).Adj x y := by
    intro x y h
    rw [SimpleGraph.deleteEdges_adj] at h
    fin_cases x <;> fin_cases y
    · exact h.1 rfl
    · exact h.2 rfl
    · exact h.2 Sym2.eq_swap
    · exact h.1 rfl
  cases p with
  | cons h _ => exact hadj _ _ h

/-! ### Non-matroid equicardinal example (Case 2 of Theorem 13.53) -/

/-- On `E = Fin 4`, `F = {{0, 1}, {2, 3}}` is a nonempty, monopoly-free, equicardinal antichain
that fails basis exchange (`¬ IsMatroidBaseFamily F`), and VCG pays `4 > 2 = cheapestNash` on
`c = (0, 0, 1, 1)` so VCG does not have frugality ratio `1`. -/
private theorem disjoint_pairs_fin4_not_matroid :
    let F : Finset (Finset (Fin 4)) := {{0, 1}, {2, 3}}
    let hF : F.Nonempty := ⟨{0, 1}, by simp [F]⟩
    let hmono : IsMonopolyFree F := fun e => by
      fin_cases e
      · exact ⟨{2, 3}, by simp [F], by decide⟩
      · exact ⟨{2, 3}, by simp [F], by decide⟩
      · exact ⟨{0, 1}, by simp [F], by decide⟩
      · exact ⟨{0, 1}, by simp [F], by decide⟩
    ¬ IsMatroidBaseFamily F ∧ ¬ HasFrugalityRatioLe F (vcgMechanism F hF hmono) 1 := by
  intro F hF hmono
  have hanti : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin 4))) := by
    intro S hS T hT hne hsub
    simp only [Finset.mem_coe, F, Finset.mem_insert, Finset.mem_singleton] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · exact hne rfl
    · exact absurd (hsub (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))) (by decide)
    · exact absurd (hsub (by decide : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))) (by decide)
    · exact hne rfl
  have hnot_mat : ¬ IsMatroidBaseFamily F := by
    intro hmat
    obtain ⟨f, hf, hmem⟩ := hmat.exchange {0, 1} (by simp [F]) {2, 3} (by simp [F]) 0 (by decide)
    fin_cases f <;> revert hf hmem <;> decide
  exact ⟨hnot_mat, fun h1 => hnot_mat ((vcg_hasFrugalityRatioLe_one_iff_isMatroidBaseFamily hF hmono
    hanti).1 h1)⟩

/-! ### Non-antichain boundary witness for Theorem 13.53 -/

/-- Boundary witness showing why `IsAntichain` is needed for the converse of Theorem 13.53:
on `E = Fin 3`, `F = {{0}, {1}, {0, 2}}` is nonempty and monopoly-free and is NOT a matroid base
family (since `{0} ⊂ {0, 2}`), yet VCG still satisfies `HasFrugalityRatioLe F (vcgMechanism ...) 1`
for every nonnegative cost profile `c` (because `{0, 2}` is strictly dominated unless `c 2 = 0`, in
which case `2` receives VCG payment `0`). -/
private theorem nonAntichain_vcg_frugality_one :
    let F : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 2}}
    let hF : F.Nonempty := ⟨{0}, by simp [F]⟩
    let hmono : IsMonopolyFree F := fun e => by
      fin_cases e
      · exact ⟨{1}, by simp [F], by decide⟩
      · exact ⟨{0}, by simp [F], by decide⟩
      · exact ⟨{0}, by simp [F], by decide⟩
    ¬ IsMatroidBaseFamily F ∧ HasFrugalityRatioLe F (vcgMechanism F hF hmono) 1 := by
  intro F hF hmono
  have hnot_mat : ¬ IsMatroidBaseFamily F := fun hmat =>
    hmat.isAntichain (by simp [F] : ({0} : Finset (Fin 3)) ∈ F)
      (by simp [F] : ({0, 2} : Finset (Fin 3)) ∈ F) (by decide) (by decide)
  refine ⟨hnot_mat, zero_le_one, fun c hc0 => ?_⟩
  rw [one_mul]
  have hc0' : 0 ≤ c 0 := hc0 0
  have hc1' : 0 ≤ c 1 := hc0 1
  have hc2' : 0 ≤ c 2 := hc0 2
  have hcn_ge : max (c 0) (c 1) ≤ cheapestNash F c := by
    refine le_cheapestNash hF hmono fun b S h => ?_
    have hmem := h.mem
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · obtain ⟨T, hTF, h0T, hTeq⟩ := h.winner_tight 0 (by decide)
      have hT1 : T = {1} := by
        simp only [F, Finset.mem_insert, Finset.mem_singleton] at hTF
        rcases hTF with rfl | rfl | rfl
        · exact absurd (by decide) h0T
        · rfl
        · exact absurd (by decide) h0T
      subst hT1
      have hb1 : b 1 = c 1 := h.loser_truthful 1 (by decide)
      have hge0 : c 0 ≤ b 0 := h.winner_ge 0 (by decide)
      simp only [Finset.sum_singleton] at hTeq ⊢
      rw [max_le_iff]
      exact ⟨hge0, by linarith⟩
    · obtain ⟨T, hTF, h1T, hTeq⟩ := h.winner_tight 1 (by decide)
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hTF
      rcases hTF with rfl | rfl | rfl
      · have hb0 : b 0 = c 0 := h.loser_truthful 0 (by decide)
        have hge1 : c 1 ≤ b 1 := h.winner_ge 1 (by decide)
        simp only [Finset.sum_singleton] at hTeq ⊢
        rw [max_le_iff]
        exact ⟨by linarith, hge1⟩
      · exact absurd (by decide) h1T
      · have hb0 : b 0 = c 0 := h.loser_truthful 0 (by decide)
        have hb2 : b 2 = c 2 := h.loser_truthful 2 (by decide)
        have hge1 : c 1 ≤ b 1 := h.winner_ge 1 (by decide)
        simp only [Finset.sum_singleton, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)] at hTeq ⊢
        rw [max_le_iff]
        exact ⟨by linarith, hge1⟩
    · obtain ⟨T, hTF, h0T, hTeq⟩ := h.winner_tight 0 (by decide)
      have hT1 : T = {1} := by
        simp only [F, Finset.mem_insert, Finset.mem_singleton] at hTF
        rcases hTF with rfl | rfl | rfl
        · exact absurd (by decide) h0T
        · rfl
        · exact absurd (by decide) h0T
      subst hT1
      have hb1 : b 1 = c 1 := h.loser_truthful 1 (by decide)
      have hge0 : c 0 ≤ b 0 := h.winner_ge 0 (by decide)
      have hge2 : c 2 ≤ b 2 := h.winner_ge 2 (by decide)
      simp only [Finset.sum_singleton, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)] at hTeq ⊢
      rw [max_le_iff]
      exact ⟨by linarith, by linarith⟩
  refine le_trans ?_ hcn_ge
  rw [(vcgMechanism F hF hmono).totalPay_eq_sum_alloc (vcgMechanism_losersPaidZero F hF hmono) hc0]
  simp only [vcgMechanism]
  set A := vcgAlloc F hF c
  have hA : IsMinCostSet F c A := vcgAlloc_isMinCostSet F hF c
  have hAmem := hA.1
  simp only [F, Finset.mem_insert, Finset.mem_singleton] at hAmem
  rcases hAmem with hA0 | hA1 | hA02
  · rw [hA0, Finset.sum_singleton]
    have hle := vcgPayOfSet_le hmono c {0} (e := 0) (T := {1}) (by simp [F]) (by decide)
    have her : ({0} : Finset (Fin 3)).erase 0 = ∅ := by decide
    rw [her, Finset.sum_empty, sub_zero, Finset.sum_singleton] at hle
    exact hle.trans (le_max_right _ _)
  · rw [hA1, Finset.sum_singleton]
    have hle := vcgPayOfSet_le hmono c {1} (e := 1) (T := {0}) (by simp [F]) (by decide)
    have her : ({1} : Finset (Fin 3)).erase 1 = ∅ := by decide
    rw [her, Finset.sum_empty, sub_zero, Finset.sum_singleton] at hle
    exact hle.trans (le_max_left _ _)
  · rw [hA02, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]
    have hc2_zero : c 2 = 0 := by
      have hle := hA.2 {0} (by simp [F])
      rw [hA02, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2), Finset.sum_singleton] at hle
      linarith
    have hp0 := vcgPayOfSet_le hmono c {0, 2} (e := 0) (T := {1}) (by simp [F]) (by decide)
    have hp2 := vcgPayOfSet_le hmono c {0, 2} (e := 2) (T := {0}) (by simp [F]) (by decide)
    have her0 : ({0, 2} : Finset (Fin 3)).erase 0 = {2} := by decide
    have her2 : ({0, 2} : Finset (Fin 3)).erase 2 = {0} := by decide
    rw [her0, Finset.sum_singleton, Finset.sum_singleton, hc2_zero, sub_zero] at hp0
    rw [her2, Finset.sum_singleton] at hp2
    have hmax := le_max_right (c 0) (c 1)
    linarith

end CslibFrontierTests.GameTheory.Frugality
