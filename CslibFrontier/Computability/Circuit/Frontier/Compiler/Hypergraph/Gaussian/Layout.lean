/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Compiler
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.DualCert
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.WalkKernel
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.CorrelationBounds
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.ParamSelection
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Scores
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric

/-!
# Grid Control, Local Concentration, and Dual-Certificate Layout Existence

Establishes deterministic grid-threshold control, second-moment local concentration for the
adaptive bipartite Gaussian kernel, and the unconditional dual-certificate layout theorem
`exists_layout_hyperWidth_le`.

## Main results

* `Cslib.Circuits.Frontier.Hypergraph.exists_layout_hyperWidth_le`: unconditional layout existence
  for every circuit of fan-in at most `r` from a `HyperDualCert r K₀ a b`.
-/

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open MeasureTheory ProbabilityTheory Real Set Filter Cslib.Circuits
open scoped RealInnerProductSpace Interval

/-! ### Grid control, local concentration, and unconditional layout existence -/

section GridAndLayout

variable {σ : Signature} {n : ℕ}

/-- Every circuit of fan-in at most `r` has at most `(r + 1) |HyperNode c|` live signals. -/
private theorem card_liveSignal_le {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r) :
    Fintype.card (LiveSignal c) ≤ (r + 1) * Nat.card (HyperNode c) := by
  have h1 : Fintype.card (LiveSignal c) ≤ ∑ w : LiveSignal c, (hyperEdge c w).card := by
    calc Fintype.card (LiveSignal c) = ∑ _w : LiveSignal c, 1 := by simp
      _ ≤ ∑ w : LiveSignal c, (hyperEdge c w).card :=
          Finset.sum_le_sum fun w _ => card_hyperEdge_pos c w
  have h2 := sum_card_hyperEdge_le hfan
  have hnode : Nat.card (HyperNode c) = Fintype.card (LiveGate c) + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unique (α := Unit)]
  rw [hnode]
  calc Fintype.card (LiveSignal c) ≤ (r + 1) * Fintype.card (LiveGate c) + 1 := h1.trans h2
    _ ≤ (r + 1) * Fintype.card (LiveGate c) + (r + 1) := Nat.add_le_add_left (Nat.le_add_left 1 r) _
    _ = (r + 1) * (Fintype.card (LiveGate c) + 1) := by ring

/-- Any finset `F` of live signals each meeting `S : Set (HyperNode c)` has cardinality at most
`(r + 1) |S|`. -/
private theorem card_touching_signals_le_of_subset {c : Circuit σ n 1} {r : ℕ}
    (hfan : c.FanInAtMost r) (S : Set (HyperNode c)) (F : Finset (LiveSignal c))
    (hF : ∀ w ∈ F, ∃ u ∈ hyperEdge c w, u ∈ S) :
    F.card ≤ (r + 1) * S.ncard := by
  have : DecidablePred (· ∈ S) := Classical.decPred _
  have hsub : F ⊆ S.toFinset.biUnion fun u => Finset.univ.filter fun w => u ∈ hyperEdge c w := by
    intro w hw
    obtain ⟨u, huw, huS⟩ := hF w hw
    exact Finset.mem_biUnion.mpr
      ⟨u, mem_toFinset.mpr huS, Finset.mem_filter.mpr ⟨Finset.mem_univ w, huw⟩⟩
  calc F.card
      ≤ (S.toFinset.biUnion fun u => Finset.univ.filter fun w => u ∈ hyperEdge c w).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S.toFinset, (Finset.univ.filter fun w => u ∈ hyperEdge c w).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S.toFinset, (r + 1) := Finset.sum_le_sum fun u _ => card_signals_at_node_le hfan u
    _ = (r + 1) * S.ncard := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm, ncard_eq_toFinset_card' S]

/-- **Grid control for hypergraphs.** Sorting `HyperNode c` by `score` yields a layout of
`hyperWidth c lay ≤ B` whenever the lower tail, upper tail, and each grid threshold plus window
count are bounded by `B`. -/
private theorem exists_hyperWidth_le_of_vertexScore {c : Circuit σ n 1} {r : ℕ}
    (hfan : c.FanInAtMost r) (score : HyperNode c → ℝ) {a₀ δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : ((r + 1 : ℕ) : ℝ) * ({v | score v < a₀}.ncard : ℝ) ≤ B)
    (high : ((r + 1 : ℕ) : ℝ) * ({v | a₀ + M * δ ≤ score v}.ncard : ℝ) ≤ B)
    (mid : ∀ i < M, ((hyperCut c {v | score v < a₀ + i * δ}).card : ℝ) +
      ((r + 1 : ℕ) : ℝ) * ({v | a₀ + i * δ ≤ score v ∧ score v < a₀ + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ lay : Layout (HyperNode c), (hyperWidth c lay : ℝ) ≤ B := by
  obtain ⟨lay, hlay⟩ := Layout.exists_threshold score
  have hB0 : 0 ≤ B := le_trans (by positivity) low
  refine ⟨lay, ?_⟩
  have hsup : hyperWidth c lay ≤ ⌊B⌋₊ := by
    unfold hyperWidth
    refine Finset.sup_le fun t ht => Nat.le_floor ?_
    have ht_lt : t < Nat.card (HyperNode c) := Finset.mem_range.mp ht
    obtain ⟨m, hP, hPc⟩ := hlay t ht_lt
    set P := lay.initial t
    have count_touch (S : Set (HyperNode c))
        (hsub : ∀ w ∈ hyperCut c P, ∃ u ∈ hyperEdge c w, u ∈ S) :
        ((hyperCut c P).card : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * S.ncard := by
      exact_mod_cast card_touching_signals_le_of_subset hfan S (hyperCut c P) hsub
    by_cases hlo : m < a₀
    · refine (count_touch {v | score v < a₀} fun w hw => ?_).trans low
      obtain ⟨⟨u, huw, huP⟩, -⟩ := mem_hyperCut_iff.mp hw
      exact ⟨u, huw, (hP u huP).trans_lt hlo⟩
    by_cases hhi : a₀ + M * δ ≤ m
    · refine (count_touch {v | a₀ + M * δ ≤ score v} fun w hw => ?_).trans high
      obtain ⟨-, ⟨v, hvw, hvP⟩⟩ := mem_hyperCut_iff.mp hw
      exact ⟨v, hvw, hhi.trans (hPc v hvP)⟩
    obtain ⟨i, hi, ht_lo, ht_hi⟩ := exists_grid_index hδ (M := M) (not_lt.mp hlo) (not_le.mp hhi)
    let W := {v : HyperNode c | a₀ + i * δ ≤ score v ∧ score v < a₀ + (i + 1) * δ}
    have : DecidablePred (fun w : LiveSignal c => ∃ u ∈ hyperEdge c w, u ∈ W) :=
      Classical.decPred _
    let FW := (Finset.univ : Finset (LiveSignal c)).filter fun w => ∃ u ∈ hyperEdge c w, u ∈ W
    have hsplit : hyperCut c P ⊆ hyperCut c {v | score v < a₀ + i * δ} ∪ FW := by
      intro w hw
      obtain ⟨⟨u, huw, huP⟩, ⟨v, hvw, hvP⟩⟩ := mem_hyperCut_iff.mp hw
      by_cases hut : score u < a₀ + i * δ
      · exact Finset.mem_union_left _ (mem_hyperCut_iff.mpr
          ⟨⟨u, huw, hut⟩, ⟨v, hvw, not_lt.mpr (ht_lo.trans (hPc v hvP))⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w,
          u, huw, not_lt.mp hut, (hP u huP).trans_lt ht_hi⟩)
    have hFW : FW.card ≤ (r + 1) * W.ncard :=
      card_touching_signals_le_of_subset hfan W FW fun w hw => (Finset.mem_filter.mp hw).2
    have hnat : (hyperCut c P).card ≤
        (hyperCut c {v | score v < a₀ + i * δ}).card + (r + 1) * W.ncard :=
      (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left hFW _))
    have hreal : ((hyperCut c P).card : ℝ) ≤
        (hyperCut c {v | score v < a₀ + i * δ}).card + ((r + 1 : ℕ) : ℝ) * W.ncard := by
      exact_mod_cast hnat
    exact hreal.trans (mid i hi)
  exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le hB0)

/-- Support ball of `x : BipNode c K₀` on `HyperNode c` at bipartite distance `L`. -/
private def bipSupportBall (c : Circuit σ n 1) (K₀ : ℕ) (x : BipNode c K₀) (L : ℕ) :
    Set (HyperNode c) :=
  {z | (bipSimpleGraph c K₀).edist x (.inl z) ≤ L}

private theorem hyperScore_congr {c : Circuit σ n 1} {K₀ r : ℕ} {θ : ℝ} {S : ℕ} {v : HyperNode c}
    {ω ω' : HyperNode c → ℝ} (h : ∀ z ∈ bipSupportBall c K₀ (.inl v) (2 * S), ω z = ω' z) :
    hyperScore c K₀ r θ S ω v = hyperScore c K₀ r θ S ω' v := by
  refine Gaussian.inner_toLp_congr (fun z hz => ?_) h
  have hw0 : walkMax c K₀ r θ (2 * S) (.inl v) z = 0 := by
    by_contra hne
    exact hz (edist_le_of_walkMax_ne_zero c K₀ hne)
  simp [hyperUnitRow, hw0]

private theorem card_overlap_bipSupportBall_le {c : Circuit σ n 1} {K₀ r : ℕ}
    (hfan : c.FanInAtMost r) {κ : Type*} {emb : κ → BipNode c K₀} (hemb : Function.Injective emb)
    (L : ℕ) (i : κ) [Fintype κ] :
    open Classical in
    (Finset.univ.filter fun j : κ =>
      ¬Disjoint (bipSupportBall c K₀ (emb i) L) (bipSupportBall c K₀ (emb j) L)).card ≤
      (max (r + 1) K₀ + 1) ^ (2 * L) := by
  classical
  let ball := Finset.univ.filter fun y : BipNode c K₀ =>
    (bipSimpleGraph c K₀).edist (emb i) y ≤ ((2 * L : ℕ) : ℕ∞)
  have hmaps : ∀ j ∈ Finset.univ.filter (fun j : κ =>
      ¬Disjoint (bipSupportBall c K₀ (emb i) L) (bipSupportBall c K₀ (emb j) L)),
      emb j ∈ ball := by
    intro j hj
    obtain ⟨z, hzi, hzj⟩ := Set.not_disjoint_iff.mp (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    calc (bipSimpleGraph c K₀).edist (emb i) (emb j)
        ≤ (bipSimpleGraph c K₀).edist (emb i) (.inl z) +
          (bipSimpleGraph c K₀).edist (.inl z) (emb j) := SimpleGraph.edist_triangle
      _ = (bipSimpleGraph c K₀).edist (emb i) (.inl z) +
          (bipSimpleGraph c K₀).edist (emb j) (.inl z) := by
            rw [SimpleGraph.edist_comm (G := bipSimpleGraph c K₀)
              (u := (Sum.inl z : BipNode c K₀))]
      _ ≤ (L : ℕ∞) + L := add_le_add hzi hzj
      _ = ((2 * L : ℕ) : ℕ∞) := by push_cast; ring
  have hinj_card : (Finset.univ.filter fun j : κ =>
      ¬Disjoint (bipSupportBall c K₀ (emb i) L) (bipSupportBall c K₀ (emb j) L)).card ≤
      ball.card :=
    Finset.card_le_card_of_injOn emb hmaps fun _ _ _ _ h => hemb h
  exact hinj_card.trans
    (SimpleGraph.card_edist_le_le (degree_bipSimpleGraph_le c K₀ hfan) (emb i) (2 * L))

/-- Dual-LP pin-counting bound on `LiveSignal c`: the deterministic supply
`((r + 1) a + b) |LiveGate c| + max b (-a) |LiveInput c| + a` is nonnegative and dominates the sum
of pruned expected straddling probabilities plus the cardinality of large signals (`|e| > K₀`). -/
private theorem dualSupply_nonneg_and_sum_le {c : Circuit σ n 1} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hfan : c.FanInAtMost r) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (P_cross : PrunedEdge c K₀ → ℝ)
    (hP : ∀ e : PrunedEdge c K₀, P_cross e ≤ (a : ℝ) * (hyperEdge c e.1).card + b + η₀) :
    let B_main := (((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
      max (b : ℝ) (-a) * Fintype.card (LiveInput c) + a
    0 ≤ B_main ∧
      (∑ e : PrunedEdge c K₀, P_cross e) +
        (((Finset.univ : Finset (LiveSignal c)).filter
          fun w => K₀ < (hyperEdge c w).card).card : ℝ) ≤
        B_main + (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) := by
  intro B_main
  have ha_pos : (0 : ℝ) < a := Rat.cast_pos.mpr hcert.ha
  have h2_nn : (0 : ℝ) ≤ 2 * a + b := by exact_mod_cast hcert.h2
  have hpin : (∑ x : LiveInput c, ((hyperEdge c (.inl x)).card : ℝ)) +
      (∑ x : LiveGate c, ((hyperEdge c (.inr x)).card : ℝ)) ≤
      ((r + 1 : ℕ) : ℝ) * Fintype.card (LiveGate c) + 1 := by
    have h := sum_card_hyperEdge_le hfan
    rw [Fintype.sum_sum_type] at h
    exact_mod_cast h
  have hB_nn : 0 ≤ B_main := by
    have hgate_nn (g : LiveGate c) : (0 : ℝ) ≤ (a : ℝ) * (hyperEdge c (.inr g)).card + b := by
      have hk2 : (2 : ℝ) ≤ (hyperEdge c (.inr g)).card :=
        Nat.ofNat_le_cast.mpr (two_le_card_hyperEdge_gate c g)
      nlinarith
    have hinp_nn (i : LiveInput c) :
        (0 : ℝ) ≤ (a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a) := by
      have hk1 : (1 : ℝ) ≤ (hyperEdge c (.inl i)).card :=
        Nat.one_le_cast.mpr (card_hyperEdge_pos c (.inl i))
      nlinarith [le_max_right (b : ℝ) (-a)]
    have hsum_nn : 0 ≤ (∑ g : LiveGate c, ((a : ℝ) * (hyperEdge c (.inr g)).card + b)) +
        ∑ i : LiveInput c, ((a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a)) :=
      add_nonneg (Finset.sum_nonneg fun g _ => hgate_nn g)
        (Finset.sum_nonneg fun i _ => hinp_nn i)
    have hsum_le : (∑ g : LiveGate c, ((a : ℝ) * (hyperEdge c (.inr g)).card + b)) +
        (∑ i : LiveInput c, ((a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a))) ≤
        B_main := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        Finset.card_univ, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, ← Finset.mul_sum,
        ← Finset.mul_sum]
      dsimp only [B_main]
      nlinarith [hpin]
    exact hsum_nn.trans hsum_le
  refine ⟨hB_nn, ?_⟩
  let wt : LiveSignal c → ℝ := fun w => match w with
    | .inr g => (a : ℝ) * (hyperEdge c (.inr g)).card + b + η₀
    | .inl i => (a : ℝ) * (hyperEdge c (.inl i)).card + max (b : ℝ) (-a) + η₀
  have hwt_nn (w : LiveSignal c) : 0 ≤ wt w := by
    rcases w with i | g
    · have hk1 : (1 : ℝ) ≤ (hyperEdge c (.inl i)).card :=
        Nat.one_le_cast.mpr (card_hyperEdge_pos c (.inl i))
      dsimp only [wt]
      nlinarith [le_max_right (b : ℝ) (-a)]
    · have hk2 : (2 : ℝ) ≤ (hyperEdge c (.inr g)).card :=
        Nat.ofNat_le_cast.mpr (two_le_card_hyperEdge_gate c g)
      dsimp only [wt]
      nlinarith
  have hwt_ge (w : LiveSignal c) : (a : ℝ) * (hyperEdge c w).card + b + η₀ ≤ wt w := by
    rcases w with i | g
    · dsimp only [wt]; linarith [le_max_left (b : ℝ) (-a)]
    · exact le_rfl
  let F_mid := (Finset.univ : Finset (LiveSignal c)).filter fun w =>
    2 ≤ (hyperEdge c w).card ∧ (hyperEdge c w).card ≤ K₀
  let S_big := (Finset.univ : Finset (LiveSignal c)).filter fun w => K₀ < (hyperEdge c w).card
  have hdisj : Disjoint F_mid S_big := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have := (Finset.mem_filter.mp h1).2.2
    have := (Finset.mem_filter.mp h2).2
    omega
  have hsum_pruned : ∑ e : PrunedEdge c K₀, P_cross e ≤ ∑ w ∈ F_mid, wt w := by
    calc ∑ e : PrunedEdge c K₀, P_cross e
        ≤ ∑ e : PrunedEdge c K₀, wt e.1 := Finset.sum_le_sum fun e _ => (hP e).trans (hwt_ge e.1)
      _ = ∑ w ∈ F_mid, wt w :=
          Finset.sum_bij (fun e _ => e.1)
            (fun e _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun w hw => ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩)
            (fun _ _ => rfl)
  have hsum_big : (S_big.card : ℝ) ≤ ∑ w ∈ S_big, wt w := by
    calc (S_big.card : ℝ) = ∑ _w ∈ S_big, (1 : ℝ) := by simp
      _ ≤ ∑ w ∈ S_big, wt w := Finset.sum_le_sum fun w hw => by
          have hk_gt : (K₀ + 1 : ℝ) ≤ (hyperEdge c w).card := by
            have : K₀ + 1 ≤ (hyperEdge c w).card := (Finset.mem_filter.mp hw).2
            exact_mod_cast this
          have htailR : (1 : ℝ) ≤ (a : ℝ) * (K₀ + 1) + b := by exact_mod_cast hcert.htail
          have h1 : (1 : ℝ) ≤ (a : ℝ) * (hyperEdge c w).card + b + η₀ := by nlinarith
          exact h1.trans (hwt_ge w)
  have hsig : (Fintype.card (LiveInput c) : ℝ) + Fintype.card (LiveGate c) ≤
      ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) := by
    have hs := card_liveSignal_le hfan
    rw [Fintype.card_sum] at hs
    exact_mod_cast hs
  have htot_wt : ∑ w : LiveSignal c, wt w ≤
      B_main + (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) := by
    rw [Fintype.sum_sum_type]
    dsimp only [wt, B_main]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    nlinarith [hpin, hsig]
  calc (∑ e : PrunedEdge c K₀, P_cross e) + (S_big.card : ℝ)
      ≤ (∑ w ∈ F_mid, wt w) + ∑ w ∈ S_big, wt w := add_le_add hsum_pruned hsum_big
    _ = ∑ w ∈ F_mid ∪ S_big, wt w := (Finset.sum_union hdisj).symm
    _ ≤ ∑ w : LiveSignal c, wt w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun w _ _ => hwt_nn w
    _ ≤ B_main + (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) := htot_wt

private def hyperCrossEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ) (t : ℝ)
    (e : PrunedEdge c K₀) : Set (HyperNode c → ℝ) :=
  {ω | HyperedgeStraddles (hyperEdge c e.1) {v | hyperScore c K₀ r θ S ω v < t}}

private def hyperVertEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ) (f : ℝ → Prop)
    (v : HyperNode c) : Set (HyperNode c → ℝ) :=
  {ω | f (hyperScore c K₀ r θ S ω v)}

/-- Grid-threshold bound on `(hyperCut c {v | hyperScore ... < t}).card` from concentration of
pruned hyperedges. -/
private theorem card_hyperCut_threshold_le {c : Circuit σ n 1} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hfan : c.FanInAtMost r) {η₀ c_dev : ℝ} (hη₀ : 0 ≤ η₀)
    (θ : ℝ) (S : ℕ) (ω : HyperNode c → ℝ) (t : ℝ)
    (hprob : ∀ e : PrunedEdge c K₀,
      (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real (hyperCrossEvent c K₀ r θ S t e) ≤
        (a : ℝ) * (hyperEdge c e.1).card + b + η₀)
    (hdev : ω ∉ Gaussian.deviation (hyperCrossEvent c K₀ r θ S t) c_dev) :
    ((hyperCut c {v | hyperScore c K₀ r θ S ω v < t}).card : ℝ) ≤
      ((((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
        max (b : ℝ) (-a) * Fintype.card (LiveInput c) + a) +
        (Nat.card (HyperNode c) : ℝ) * (η₀ * ((r + 1 : ℕ) : ℝ)) + c_dev := by
  let S_cut := hyperCut c {v | hyperScore c K₀ r θ S ω v < t}
  let S_mid := S_cut.filter fun w => 2 ≤ (hyperEdge c w).card ∧ (hyperEdge c w).card ≤ K₀
  let S_big := (Finset.univ : Finset (LiveSignal c)).filter fun w => K₀ < (hyperEdge c w).card
  have hcut_sub : S_cut ⊆ S_mid ∪ S_big := by
    intro w hw
    by_cases hle : (hyperEdge c w).card ≤ K₀
    · have hk2 : 2 ≤ (hyperEdge c w).card := by
        obtain ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ := mem_hyperCut_iff.mp hw
        have huv : u ≠ v := fun h => by subst h; exact h2 h1
        exact Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hk2, hle⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w, not_le.mp hle⟩)
  have hmid_card : S_mid.card =
      {e : PrunedEdge c K₀ | ω ∈ hyperCrossEvent c K₀ r θ S t e}.ncard := by
    have : DecidablePred (fun e : PrunedEdge c K₀ => ω ∈ hyperCrossEvent c K₀ r θ S t e) :=
      Classical.decPred _
    rw [ncard_eq_toFinset_card']
    refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2⟩)
      (fun w hw => mem_toFinset.mpr (mem_hyperCut_iff.mp (Finset.mem_filter.mp hw).1))
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun e he => ⟨e.1, Finset.mem_filter.mpr ⟨mem_hyperCut_iff.mpr (mem_toFinset.mp he), e.2⟩,
        Subtype.ext rfl⟩)
  have hcard_cut : (S_cut.card : ℝ) ≤ (S_mid.card : ℝ) + (S_big.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcut_sub).trans (Finset.card_union_le _ _)
  have hmid_lt : (S_mid.card : ℝ) <
      (∑ e : PrunedEdge c K₀,
        (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
          (hyperCrossEvent c K₀ r θ S t e)) + c_dev := by
    rw [hmid_card]
    exact Gaussian.ncard_lt_of_notMem_deviation hdev
  have hsum := (dualSupply_nonneg_and_sum_le hcert hfan hη₀
    (fun e => (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
      (hyperCrossEvent c K₀ r θ S t e)) hprob).2
  linarith [hcard_cut, hmid_lt, hsum]

private theorem ncard_hyperWindow_le {c : Circuit σ n 1} {K₀ r : ℕ} {θ : ℝ} {S : ℕ}
    {ω : HyperNode c → ℝ} {a₀ δ c_dev : ℝ} (hδ : 0 ≤ δ)
    (hdev : ω ∉ Gaussian.deviation
      (hyperVertEvent c K₀ r θ S fun x => a₀ ≤ x ∧ x < a₀ + δ) c_dev) :
    ({v : HyperNode c |
      a₀ ≤ hyperScore c K₀ r θ S ω v ∧ hyperScore c K₀ r θ S ω v < a₀ + δ}.ncard : ℝ) ≤
      (Nat.card (HyperNode c) : ℝ) * (δ / √(2 * π)) + c_dev := by
  have hW := Gaussian.ncard_lt_of_notMem_deviation hdev
  have hWm : ∑ v : HyperNode c,
      (Measure.pi fun _ : HyperNode c => gaussianReal 0 1).real
        (hyperVertEvent c K₀ r θ S (fun x => a₀ ≤ x ∧ x < a₀ + δ) v) ≤
      (Nat.card (HyperNode c) : ℝ) * (δ / √(2 * π)) := by
    refine (Finset.sum_le_sum fun v _ =>
      Gaussian.measureReal_window_le (norm_hyperUnitRow c K₀ r θ S v) a₀ hδ).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hset : {v : HyperNode c |
      a₀ ≤ hyperScore c K₀ r θ S ω v ∧ hyperScore c K₀ r θ S ω v < a₀ + δ} =
      {v : HyperNode c | ω ∈ hyperVertEvent c K₀ r θ S (fun x => a₀ ≤ x ∧ x < a₀ + δ) v} := rfl
  rw [hset]
  linarith [hW, hWm]

private theorem measurable_hyperScore (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ)
    (v : HyperNode c) : Measurable fun ω : HyperNode c → ℝ => hyperScore c K₀ r θ S ω v := by
  unfold hyperScore
  fun_prop

private theorem measurableSet_hyperCrossEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ)
    (t : ℝ) (e : PrunedEdge c K₀) : MeasurableSet (hyperCrossEvent c K₀ r θ S t e) := by
  have heq : hyperCrossEvent c K₀ r θ S t e =
      (⋃ v ∈ hyperEdge c e.1, {ω | hyperScore c K₀ r θ S ω v < t}) ∩
      (⋃ v ∈ hyperEdge c e.1, {ω | ¬ hyperScore c K₀ r θ S ω v < t}) := by
    ext ω
    simp only [hyperCrossEvent, HyperedgeStraddles, mem_ofPred_eq, mem_inter_iff, mem_iUnion,
      exists_prop]
  rw [heq]
  exact ((hyperEdge c e.1).measurableSet_biUnion fun v _ =>
    measurableSet_lt (measurable_hyperScore c K₀ r θ S v) measurable_const).inter
    ((hyperEdge c e.1).measurableSet_biUnion fun v _ =>
      (measurableSet_lt (measurable_hyperScore c K₀ r θ S v) measurable_const).compl)

private theorem dependsOn_hyperCrossEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ) (t : ℝ)
    (e : PrunedEdge c K₀) :
    DependsOn (· ∈ hyperCrossEvent c K₀ r θ S t e)
      (bipSupportBall c K₀ (.inr e) (2 * S + 1)) := by
  intro ω ω' hω
  have hsc (v : HyperNode c) (hv : v ∈ hyperEdge c e.1) :
      hyperScore c K₀ r θ S ω v = hyperScore c K₀ r θ S ω' v := by
    refine hyperScore_congr fun z (hz : (bipSimpleGraph c K₀).edist (.inl v) (.inl z) ≤ 2 * S) =>
      hω z ?_
    have hadj : (bipSimpleGraph c K₀).Adj (.inr e) (.inl v) := hv
    calc (bipSimpleGraph c K₀).edist (.inr e) (.inl z)
        ≤ (bipSimpleGraph c K₀).edist (.inr e) (.inl v) +
          (bipSimpleGraph c K₀).edist (.inl v) (.inl z) := SimpleGraph.edist_triangle
      _ = 1 + (bipSimpleGraph c K₀).edist (.inl v) (.inl z) := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
      _ ≤ 1 + (2 * S : ℕ∞) := add_le_add_right hz 1
      _ = ((2 * S + 1 : ℕ) : ℕ∞) := by push_cast; ring
  simp only [hyperCrossEvent, mem_ofPred_eq, HyperedgeStraddles]
  exact propext ⟨fun ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ =>
    ⟨⟨u, hu, by rwa [← hsc u hu]⟩, ⟨v, hv, by rwa [← hsc v hv]⟩⟩,
    fun ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ =>
    ⟨⟨u, hu, by rwa [hsc u hu]⟩, ⟨v, hv, by rwa [hsc v hv]⟩⟩⟩

private theorem dependsOn_hyperVertEvent (c : Circuit σ n 1) (K₀ r : ℕ) (θ : ℝ) (S : ℕ)
    (f : ℝ → Prop) (v : HyperNode c) :
    DependsOn (· ∈ hyperVertEvent c K₀ r θ S f v)
      (bipSupportBall c K₀ (.inl v) (2 * S + 1)) := by
  intro ω ω' hω
  simp only [hyperVertEvent, mem_ofPred_eq]
  rw [hyperScore_congr fun z (hz : _ ≤ (2 * S : ℕ∞)) =>
    hω z (hz.trans (by exact_mod_cast Nat.le_succ (2 * S)))]

/-- Concentration of pruned hyperedge straddling counts, grid windows, and tails on `HyperNode c`.
-/
private theorem exists_concentrated_hyperSample {c : Circuit σ n 1} {r K₀ D_ov : ℕ}
    (hfan : c.FanInAtMost r) (θ : ℝ) (S : ℕ)
    (hD_ov : (max (r + 1) K₀ + 1) ^ (2 * (2 * S + 1)) ≤ D_ov) (T δ : ℝ) {ε c_dev : ℝ}
    (hε : 0 < ε) (hc_eq : c_dev = ε * Nat.card (HyperNode c)) (M : ℕ)
    (hlarge : ((M : ℝ) * (((r + 1 : ℕ) : ℝ) + 1) + 2) * (D_ov : ℝ) / ε ^ 2 <
      Nat.card (HyperNode c)) :
    ∃ ω : HyperNode c → ℝ,
      (∀ i < M,
        ω ∉ Gaussian.deviation (hyperCrossEvent c K₀ r θ S (-T + i * δ)) c_dev ∧
        ω ∉ Gaussian.deviation
          (hyperVertEvent c K₀ r θ S fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ) c_dev) ∧
      ω ∉ Gaussian.deviation (hyperVertEvent c K₀ r θ S (· < -T)) c_dev ∧
      ω ∉ Gaussian.deviation (hyperVertEvent c K₀ r θ S (T ≤ ·)) c_dev := by
  set P := Measure.pi fun _ : HyperNode c => gaussianReal 0 1
  set h : ℝ := (Nat.card (HyperNode c) : ℝ) with hh
  set dr : ℝ := ((r + 1 : ℕ) : ℝ)
  have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) hlarge
  have hc_pos : 0 < c_dev := hc_eq ▸ mul_pos hε hh_pos
  have hcardV : (Fintype.card (HyperNode c) : ℝ) = h := by
    rw [hh, Nat.card_eq_fintype_card]
  have hcard_pruned : (Fintype.card (PrunedEdge c K₀) : ℝ) ≤ dr * h := by
    have hle : Fintype.card (PrunedEdge c K₀) ≤ (r + 1) * Nat.card (HyperNode c) :=
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
        (card_liveSignal_le hfan)
    have hR : (Fintype.card (PrunedEdge c K₀) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) :=
      by exact_mod_cast hle
    exact hR
  have crossDev (t : ℝ) : P.real (Gaussian.deviation (hyperCrossEvent c K₀ r θ S t) c_dev) ≤
      (dr * h) * (D_ov : ℝ) / c_dev ^ 2 := by
    have hd := Gaussian.measureReal_deviation_le (measurableSet_hyperCrossEvent c K₀ r θ S t)
      (fun e => bipSupportBall c K₀ (.inr e) (2 * S + 1))
      (dependsOn_hyperCrossEvent c K₀ r θ S t)
      (fun e => (card_overlap_bipSupportBall_le hfan Sum.inr_injective (2 * S + 1) e).trans hD_ov)
      hc_pos
    exact hd.trans (by gcongr)
  have vertDev {f : ℝ → Prop} (hf : MeasurableSet {x | f x}) :
      P.real (Gaussian.deviation (hyperVertEvent c K₀ r θ S f) c_dev) ≤
        h * (D_ov : ℝ) / c_dev ^ 2 := by
    have hd := Gaussian.measureReal_deviation_le
      (fun v => measurable_hyperScore c K₀ r θ S v hf)
      (fun v => bipSupportBall c K₀ (.inl v) (2 * S + 1))
      (dependsOn_hyperVertEvent c K₀ r θ S f)
      (fun v => (card_overlap_bipSupportBall_le hfan Sum.inl_injective (2 * S + 1) v).trans hD_ov)
      hc_pos
    rwa [hcardV] at hd
  have hsmall : M * ((dr * h) * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2) +
      h * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2 < 1 := by
    have hcalc : M * ((dr * h) * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2) +
        h * (D_ov : ℝ) / c_dev ^ 2 + h * (D_ov : ℝ) / c_dev ^ 2 =
        ((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2 / h := by
      rw [hc_eq]
      field_simp
      ring
    rw [hcalc, div_lt_one hh_pos]
    exact hlarge
  exact Gaussian.exists_sample_of_grid_bounds
    (fun i _ => crossDev (-T + i * δ))
    (fun i _ => vertDev ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)))
    (vertDev (measurableSet_lt measurable_id measurable_const))
    (vertDev (measurableSet_le measurable_const measurable_id)) hsmall

private theorem exists_hyperGrid_parameters (r : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    let dr : ℝ := ((r + 1 : ℕ) : ℝ)
    ∃ (η₀ T ε : ℝ) (M : ℕ), 0 < η₀ ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      η₀ * dr + dr / T ^ 2 + dr * (2 * T / M) / √(2 * π) + (dr + 1) * ε ≤ ξ := by
  intro dr
  have hdr_pos : 0 < dr := by positivity
  set η₀ := ξ / (4 * dr) with hη₀_def
  set T := 1 + 4 * dr / ξ with hT_def
  set ε := ξ / (4 * (dr + 1)) with hε_def
  set M : ℕ := ⌈8 * dr * T / ξ⌉₊ + 1 with hM_def
  have hT : 0 < T := by positivity
  have hM : 0 < M := Nat.succ_pos _
  have hMR : 8 * dr * T / ξ ≤ (M : ℝ) := by
    rw [hM_def]
    push_cast
    linarith [Nat.le_ceil (8 * dr * T / ξ)]
  have htail_err : dr / T ^ 2 ≤ ξ / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    have hsq : 4 * dr / ξ ≤ T ^ 2 := by
      rw [hT_def]
      nlinarith [sq_nonneg (4 * dr / ξ)]
    have H := mul_le_mul_of_nonneg_left hsq hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at H
    linarith [H]
  have hgrid_err : dr * (2 * T / M) / √(2 * π) ≤ ξ / 4 := by
    have hsqrt : 1 ≤ √(2 * π) :=
      (le_sqrt zero_le_one (by positivity)).mpr (by linarith [two_le_pi])
    have hfrac : dr * (2 * T / M) ≤ ξ / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_pos.mpr hM)]
      have H := (div_le_iff₀ hξ).mp hMR
      linarith [H]
    exact (div_le_self (by positivity) hsqrt).trans hfrac
  refine ⟨η₀, T, ε, M, by positivity, hT, by positivity, hM, ?_⟩
  have h1 : η₀ * dr = ξ / 4 := by rw [hη₀_def]; field_simp
  have h2 : (dr + 1) * ε = ξ / 4 := by rw [hε_def]; field_simp
  linarith [h1, h2, htail_err, hgrid_err]

/-- **Unconditional dual-certificate hypergraph layout theorem.** Given a `HyperDualCert r K₀ a b`
and any slack `ξ > 0`, there is a constant `C : ℝ` (depending only on `r, K₀, a, b, ξ`) such that
every single-output circuit `c : Circuit σ n 1` of fan-in at most `r` admits a vertex layout
`lay : Layout (HyperNode c)` with
`hyperWidth c lay ≤ ((r + 1) a + b) |LiveGate c| + max b (-a) |LiveInput c| + ξ |HyperNode c| + C`.
-/
theorem exists_layout_hyperWidth_le {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C : ℝ, ∀ {σ : Signature} {n : ℕ} (c : Circuit σ n 1), c.FanInAtMost r →
      ∃ lay : Layout (HyperNode c), (hyperWidth c lay : ℝ) ≤
        (((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
          max (b : ℝ) (-a) * Fintype.card (LiveInput c) +
          ξ * Nat.card (HyperNode c) + C := by
  let dr : ℝ := ((r + 1 : ℕ) : ℝ)
  have hdr_pos : 0 < dr := by positivity
  obtain ⟨η₀, T, ε, M, hη₀, hT, hε, hM, herr_sum⟩ := exists_hyperGrid_parameters r hξ
  obtain ⟨θ, hθ_mem, S, hS1, hprob_unif⟩ := exists_uniform_theta_radius hcert hη₀
  obtain ⟨D_ov, hD_ov⟩ : ∃ D_ov : ℕ, (max (r + 1) K₀ + 1) ^ (2 * (2 * S + 1)) ≤ D_ov :=
    ⟨_, le_rfl⟩
  obtain ⟨N₀, hN₀_ge⟩ : ∃ N₀ : ℕ, ((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2 ≤ N₀ :=
    ⟨⌈((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2⌉₊, Nat.le_ceil _⟩
  obtain ⟨C, ha_le_C, hC_small⟩ :
      ∃ C : ℝ, (a : ℝ) ≤ C ∧ dr * (N₀ : ℝ) ≤ C - |max (b : ℝ) (-a)| * (dr * (N₀ : ℝ)) := by
    refine ⟨|(a : ℝ)| + (dr + |max (b : ℝ) (-a)| * dr) * (N₀ : ℝ) + 1, ?_, ?_⟩
    · have hnn : 0 ≤ (dr + |max (b : ℝ) (-a)| * dr) * (N₀ : ℝ) := by positivity
      linarith [le_abs_self (a : ℝ), hnn]
    · have h0 : 0 ≤ |(a : ℝ)| := abs_nonneg _
      linarith [h0]
  refine ⟨C, fun {σ n} c hfan => ?_⟩
  by_cases hbig : N₀ < Nat.card (HyperNode c)
  · have hN₀_lt : (N₀ : ℝ) < Nat.card (HyperNode c) := Nat.cast_lt.mpr hbig
    have hlarge : ((M : ℝ) * (dr + 1) + 2) * (D_ov : ℝ) / ε ^ 2 < Nat.card (HyperNode c) :=
      hN₀_ge.trans_lt hN₀_lt
    set P := Measure.pi fun _ : HyperNode c => gaussianReal 0 1
    set h : ℝ := (Nat.card (HyperNode c) : ℝ) with hh
    set δ : ℝ := 2 * T / M
    set c_dev : ℝ := ε * h with hc_dev
    obtain ⟨ω, hmid, hlow, hhigh⟩ :=
      exists_concentrated_hyperSample hfan θ S hD_ov T δ hε hc_dev M hlarge
    have hh_pos : 0 < h := lt_of_le_of_lt (by positivity) hlarge
    have hδ_pos : 0 < δ := by positivity
    have hcardV_eq : (Fintype.card (HyperNode c) : ℝ) = h := by
      rw [hh, Nat.card_eq_fintype_card]
    set B_main := (dr * a + b) * Fintype.card (LiveGate c) +
      max (b : ℝ) (-a) * Fintype.card (LiveInput c) + a
    have hB_main_nn : 0 ≤ B_main :=
      (dualSupply_nonneg_and_sum_le hcert hfan hη₀.le
        (fun e => P.real (hyperCrossEvent c K₀ r θ S 0 e))
        (fun e => hprob_unif c hfan e 0)).1
    set B := B_main + h * (η₀ * dr + dr / T ^ 2 + dr * δ / √(2 * π) + (dr + 1) * ε) with hB_def
    have hunit (v : HyperNode c) : ‖hyperUnitRow c K₀ r θ S v‖ = 1 :=
      norm_hyperUnitRow c K₀ r θ S v
    have tail (f : ℝ → Prop) (hf : ∀ x, f x → T ≤ |x|)
        (hdev : ω ∉ Gaussian.deviation (hyperVertEvent c K₀ r θ S f) c_dev) :
        dr * ({v | f (hyperScore c K₀ r θ S ω v)}.ncard : ℝ) ≤ B := by
      have hcount := Gaussian.ncard_lt_of_notMem_deviation hdev
      have hmean : ∑ v, P.real (hyperVertEvent c K₀ r θ S f v) ≤ h * (1 / T ^ 2) := by
        refine (Finset.sum_le_sum fun v _ =>
          (measureReal_mono (μ := P) fun ω' hω' => hf _ hω').trans
            (Gaussian.measureReal_le_abs_le (hunit v) hT)).trans_eq ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardV_eq]
      have hset : {v | f (hyperScore c K₀ r θ S ω v)} =
          {v | ω ∈ hyperVertEvent c K₀ r θ S f v} := rfl
      have hbound : ({v | f (hyperScore c K₀ r θ S ω v)}.ncard : ℝ) ≤ h * (1 / T ^ 2) + c_dev := by
        rw [hset]
        linarith [hcount, hmean]
      have hmult := mul_le_mul_of_nonneg_left hbound hdr_pos.le
      have hextra : 0 ≤ B_main + h * (η₀ * dr + dr * δ / √(2 * π) + ε) := by positivity
      have hid : B = dr * (h * (1 / T ^ 2) + c_dev) +
          (B_main + h * (η₀ * dr + dr * δ / √(2 * π) + ε)) := by
        rw [hB_def, hc_dev]
        ring
      rw [hid]
      linarith [hmult, hextra]
    have htop : -T + M * δ = T := by
      have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
      dsimp only [δ]
      field_simp [hM_ne]
      ring
    obtain ⟨lay, hlay⟩ := exists_hyperWidth_le_of_vertexScore hfan (hyperScore c K₀ r θ S ω)
      hδ_pos M (a₀ := -T) (B := B)
      (tail (· < -T) (fun x hx => by rw [abs_of_neg (by linarith)]; linarith) hlow)
      (by
        rw [htop]
        exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhigh)
      (fun i hi => by
        have hthr : -T + ((i : ℝ) + 1) * δ = -T + i * δ + δ := by ring
        rw [hthr]
        have hC_le : ((hyperCut c {v | hyperScore c K₀ r θ S ω v < -T + i * δ}).card : ℝ) ≤
            B_main + h * (η₀ * dr) + c_dev :=
          card_hyperCut_threshold_le hcert hfan hη₀.le θ S ω (-T + i * δ)
            (fun e => hprob_unif c hfan e (-T + i * δ)) (hmid i hi).1
        have hW_le := ncard_hyperWindow_le hδ_pos.le (hmid i hi).2
        have hmult := mul_le_mul_of_nonneg_left hW_le hdr_pos.le
        have htail_nn : 0 ≤ h * (dr / T ^ 2) := by positivity
        have hid : B = (B_main + h * (η₀ * dr) + c_dev) + dr * (h * (δ / √(2 * π)) + c_dev) +
            h * (dr / T ^ 2) := by
          rw [hB_def, hc_dev]
          ring
        rw [hid]
        linarith [hC_le, hmult, htail_nn])
    refine ⟨lay, hlay.trans ?_⟩
    have hh_err := mul_le_mul_of_nonneg_left herr_sum hh_pos.le
    rw [hB_def]
    dsimp only [B_main, δ] at hh_err ⊢
    linarith [hh_err, ha_le_C]
  · -- Small circuit (`Nat.card (HyperNode c) ≤ N₀`): any layout works deterministically.
    have hle_N₀ : (Nat.card (HyperNode c) : ℝ) ≤ (N₀ : ℝ) := Nat.cast_le.mpr (not_lt.mp hbig)
    let lay : Layout (HyperNode c) := Finite.equivFin (HyperNode c)
    have hw_le : (hyperWidth c lay : ℝ) ≤ dr * (N₀ : ℝ) := by
      have hsup : hyperWidth c lay ≤ (r + 1) * Nat.card (HyperNode c) := by
        unfold hyperWidth
        refine Finset.sup_le fun t _ => ?_
        exact (Finset.card_le_univ _).trans (card_liveSignal_le hfan)
      have hsupR : (hyperWidth c lay : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) := by
        exact_mod_cast hsup
      exact hsupR.trans (mul_le_mul_of_nonneg_left hle_N₀ hdr_pos.le)
    have hinp_le : (Fintype.card (LiveInput c) : ℝ) ≤ dr * (N₀ : ℝ) := by
      have hinp_nat : Fintype.card (LiveInput c) ≤ (r + 1) * Nat.card (HyperNode c) := by
        have hs := card_liveSignal_le hfan
        rw [Fintype.card_sum] at hs
        omega
      have hinpR : (Fintype.card (LiveInput c) : ℝ) ≤
          ((r + 1 : ℕ) : ℝ) * Nat.card (HyperNode c) := by
        exact_mod_cast hinp_nat
      exact hinpR.trans (mul_le_mul_of_nonneg_left hle_N₀ hdr_pos.le)
    have hgate_nn : 0 ≤ (dr * a + b) * Fintype.card (LiveGate c) := by
      have hd_pos : (0 : ℝ) < dr * a + b := by
        have hq := Rat.cast_pos (K := ℝ).mpr hcert.hdenom
        push_cast at hq
        dsimp only [dr]
        push_cast
        linarith [hq]
      positivity
    have hinp_abs : -(|max (b : ℝ) (-a)| * (dr * (N₀ : ℝ))) ≤
        max (b : ℝ) (-a) * Fintype.card (LiveInput c) := by
      have h1 := neg_abs_le (max (b : ℝ) (-a))
      have h2 := mul_le_mul_of_nonneg_right h1
        (Nat.cast_nonneg (α := ℝ) (Fintype.card (LiveInput c)))
      have h3 := mul_le_mul_of_nonneg_left hinp_le (abs_nonneg (max (b : ℝ) (-a)))
      linarith [h2, h3]
    have hξh_nn : 0 ≤ ξ * Nat.card (HyperNode c) := mul_nonneg hξ.le (Nat.cast_nonneg _)
    exact ⟨lay, by linarith [hw_le, hgate_nn, hinp_abs, hξh_nn, hC_small]⟩

end GridAndLayout

end Cslib.Circuits.Frontier.Hypergraph
