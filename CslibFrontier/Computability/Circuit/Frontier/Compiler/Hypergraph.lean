/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Certificates
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb

/-!
# Unconditional bounded-fan-in frontier lower bounds via signal hypergraphs

Combining the post-layout Steiner hypergraph compiler
(`CslibFrontier/Computability/Circuit/Frontier/Compiler/Hypergraph/Compiler.lean`), the adaptive
bipartite Gaussian layout theorem
(`CslibFrontier/Computability/Circuit/Frontier/Compiler/Hypergraph/Gaussian.lean`), and the six
verified rational dual-LP certificates
(`CslibFrontier/Computability/Circuit/Frontier/Compiler/Hypergraph/Certificates.lean`) yields
strictly stronger unconditional circuit lower bounds across bounded fan-in `r ≥ 3`:

* For any `HyperDualCert r K₀ a b` with coefficient
  `L = hyperCoeff r a b = (r - 1) (1 - max b (-a)) / ((r + 1) a + b)`:
  - **Worst-case (`eventually_lt_mul_multiarySize_of_cert`,
    `eventually_lt_mul_innerSize_of_cert`):**
    every circuit of fan-in at most `r` deciding a dense rectangle-free family `S_n ⊆ U^n` has
    `(r - 1) * c.multiarySize > (L - ε) * n` (nullary and unary gates are completely free).
  - **Average-case (`eventually_agreement_le_multiarySize_of_cert`,
    `eventually_agreement_le_innerSize_of_cert`):** below `(L - ε) * n`, agreement with a
    `(K_n, b_n)`-rectangle-biased family is at most `1/2 + b_n + exp (-γ * n)` with `γ > 0` uniform
    over `U`, `S`, `K`, `b`, `σ`, `I`, and `Acc`.
  - **Nondeterministic (`eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert`,
    `eventually_lt_mul_innerSize_of_nondeterministicDecides_of_cert`):** when `b ≤ 0` (so
    `max b (-a) ≤ 0`), hiding arbitrary witness inputs preserves the input-supply inequality
    uniformly in the witness length `k`, giving `(r - 1) * c.multiarySize > (L - ε) * n` against
    nondeterministic circuits as well.

Instantiating the verified certificates yields unconditional lower bounds at:
* `r = 3` (Slepian + star-cone): `2 s > (4.4199 - ε) n`, worst-case, average-case, and
  nondeterministic (improving `4n` in
  `CslibFrontier/Computability/Circuit/Frontier/BoundedFanIn.lean`; `cert_r3_sheppard` in
  `Certificates.lean` also gives a Slepian-free `4.4011n` certificate via the parametric theorems);
* `r = 4` (Sheppard + star-cone): `3 s > (4.4792 - ε) n`, worst-case, average-case, and
  nondeterministic;
* `r = 8` (Slepian + star-cone): `7 s > (4.6666 - ε) n`, worst-case, average-case, and
  nondeterministic;
* `r = 16` (Slepian + star-cone): `15 s > (4.9798 - ε) n`, worst-case and average-case;
* `r = 64` (Slepian): `63 s > (6.0012 - ε) n`, worst-case and average-case.

## Main results

* `Cslib.Circuits.Frontier.Hypergraph.eventually_lt_mul_multiarySize_of_cert`,
  `Cslib.Circuits.Frontier.Hypergraph.eventually_lt_mul_innerSize_of_cert`: worst-case lower bounds
  from any `HyperDualCert`.
* `Cslib.Circuits.Frontier.Hypergraph.eventually_agreement_le_multiarySize_of_cert`,
  `Cslib.Circuits.Frontier.Hypergraph.eventually_agreement_le_innerSize_of_cert`: average-case
  correlation bounds from any `HyperDualCert`.
* `eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert`,
  `eventually_lt_mul_innerSize_of_nondeterministicDecides_of_cert`:
  nondeterministic lower bounds from any `HyperDualCert` with `b ≤ 0`.
-/

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open Filter Asymptotics Real Set Cslib.Circuits Cslib.Circuits.Frontier

universe u v

/-! ### Rescaled demand-and-supply algebra for `HyperDualCert` -/

private noncomputable def supplyRate (r : ℕ) (a b : ℚ) : ℝ :=
  (((r + 1 : ℕ) : ℝ) * a + b) / (((r : ℝ) - 1) * (1 - max (b : ℝ) (-a)))

private theorem supplyRate_pos_and_inv {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b) :
    0 < supplyRate r a b ∧ 1 / supplyRate r a b = (hyperCoeff r a b : ℝ) ∧
      0 < (((r + 1 : ℕ) : ℝ) * a + b) ∧ 0 < 1 - max (b : ℝ) (-a) := by
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  have hc_s : 0 < (((r + 1 : ℕ) : ℝ) * a + b) := by
    have h := (Rat.cast_pos (K := ℝ)).mpr hcert.hdenom
    push_cast at h ⊢
    linarith
  have hc_n : max (b : ℝ) (-a) < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hcert.hnum
    simpa only [Rat.cast_max, Rat.cast_neg, Rat.cast_one] using h
  have h1c_n : 0 < 1 - max (b : ℝ) (-a) := sub_pos.mpr hc_n
  have hA : 0 < supplyRate r a b := by
    unfold supplyRate
    exact div_pos hc_s (mul_pos (by linarith) h1c_n)
  have hinv : 1 / supplyRate r a b = (hyperCoeff r a b : ℝ) := by
    unfold supplyRate hyperCoeff
    rw [one_div_div]
    push_cast
    ring
  exact ⟨hA, hinv, hc_s, h1c_n⟩

/-- Deterministic input-count bound: when the unread inputs carry fewer than `K` assignments,
`c_n * |LiveInput c| ≤ c_n * n + |c_n| * log_q K` regardless of the sign of `c_n`. -/
private theorem input_supply_le_of_unread_lt {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n K : ℕ} (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Set U)
    (lay : Layout (HyperNode c)) (c_n : ℝ)
    (hu : Nat.card U ^ (hyperNetwork c I Acc lay).readᶜ.ncard < K) :
    c_n * (Fintype.card (LiveInput c) : ℝ) ≤ c_n * n + |c_n| * Real.logb (Nat.card U) K := by
  set q := Nat.card U
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  set u := (hyperNetwork c I Acc lay).readᶜ.ncard
  have hread_card : (hyperNetwork c I Acc lay).read.ncard = Fintype.card (LiveInput c) := by
    rw [read_hyperNetwork, ncard_coe_finset, Fintype.card_coe]
  have hsum : Fintype.card (LiveInput c) + u = n := by
    have h := ncard_add_ncard_compl (hyperNetwork c I Acc lay).read
    rwa [hread_card, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hu_le : (u : ℝ) ≤ Real.logb q K := by
    have hpow : (q : ℝ) ^ u ≤ K := by exact_mod_cast hu.le
    calc (u : ℝ) = Real.logb q ((q : ℝ) ^ u) :=
          (Real.logb_self_pow (zero_lt_one.trans hq1) hq1.ne' u).symm
      _ ≤ Real.logb q K := Real.logb_le_logb_of_le hq1 (pow_pos (zero_lt_one.trans hq1) u) hpow
  have hdiff : |(Fintype.card (LiveInput c) : ℝ) - n| = (u : ℝ) := by
    have heq : (Fintype.card (LiveInput c) : ℝ) - n = -(u : ℝ) := by
      have hR : (Fintype.card (LiveInput c) : ℝ) + u = n := by exact_mod_cast hsum
      linarith
    rw [heq, abs_neg, abs_of_nonneg (Nat.cast_nonneg u)]
  have hprod : c_n * ((Fintype.card (LiveInput c) : ℝ) - n) ≤ |c_n| * Real.logb q K := by
    calc c_n * ((Fintype.card (LiveInput c) : ℝ) - n)
        ≤ |c_n * ((Fintype.card (LiveInput c) : ℝ) - n)| := le_abs_self _
      _ = |c_n| * (u : ℝ) := by rw [abs_mul, hdiff]
      _ ≤ |c_n| * Real.logb q K := mul_le_mul_of_nonneg_left hu_le (abs_nonneg c_n)
  linarith

/-- Hidden post-layout Steiner network for a nondeterministic circuit `c : Circuit σ (n + k) 1`. -/
private noncomputable def hiddenHyperNetwork {U : Type u} {σ : Signature.{v}} {n k : ℕ}
    (c : Circuit σ (n + k) 1) (I : Interpretation σ U) (Acc : Set U)
    (lay : Layout (HyperNode c)) : Network U (Fin n) (HyperNode c) (SteinerEdge c) :=
  ((hyperNetwork c I Acc lay).reindex finSumFinEquiv.symm).hide

private theorem accepted_hiddenHyperNetwork {U : Type u} [Nonempty U] {σ : Signature.{v}}
    {n k : ℕ} (c : Circuit σ (n + k) 1) (I : Interpretation σ U) (Acc : Set U)
    (lay : Layout (HyperNode c)) :
    (hiddenHyperNetwork c I Acc lay).accepted =
      {x | ∃ y : Fin k → U, c.eval I (Fin.append x y) 0 ∈ Acc} := by
  ext x
  simp only [hiddenHyperNetwork, Network.accepted_hide, Network.accepted_reindex,
    accepted_hyperNetwork, mem_ofPred_eq]
  refine exists_congr fun y => ?_
  have happend : Sum.elim x y ∘ finSumFinEquiv.symm = Fin.append x y := by
    rw [← Fin.append_comp_sumElim, Function.comp_assoc]
    exact congrArg (Fin.append x y ∘ ·) finSumFinEquiv.self_comp_symm
  rw [happend]

/-- Nondeterministic input-count bound when `c_n ≤ 0`: hiding the `k` witness inputs can only
decrease the number of read inputs below `|LiveInput c|`, so `n - log_q K ≤ |LiveInput c|`
multiplied by `c_n ≤ 0` yields `c_n * |LiveInput c| ≤ c_n * n + |c_n| * log_q K`. -/
private theorem input_supply_le_of_hidden_unread_lt {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n k K : ℕ} (c : Circuit σ (n + k) 1) (I : Interpretation σ U)
    (Acc : Set U) (lay : Layout (HyperNode c)) {c_n : ℝ} (hc_n : c_n ≤ 0)
    (hu : Nat.card U ^ (hiddenHyperNetwork c I Acc lay).readᶜ.ncard < K) :
    c_n * (Fintype.card (LiveInput c) : ℝ) ≤ c_n * n + |c_n| * Real.logb (Nat.card U) K := by
  set q := Nat.card U
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  set H := hiddenHyperNetwork c I Acc lay
  have hsum : H.read.ncard + H.readᶜ.ncard = n := by
    have h := ncard_add_ncard_compl H.read
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hread_le : H.read.ncard ≤ Fintype.card (LiveInput c) := by
    have h1 := (Network.ncard_read_hide_le
      ((hyperNetwork c I Acc lay).reindex finSumFinEquiv.symm)).trans
      (Network.ncard_read_reindex (hyperNetwork c I Acc lay) finSumFinEquiv.symm).le
    rwa [read_hyperNetwork, ncard_coe_finset, ← Fintype.card_coe] at h1
  have hu_le : (H.readᶜ.ncard : ℝ) ≤ Real.logb q K := by
    have hpow : (q : ℝ) ^ H.readᶜ.ncard ≤ K := by exact_mod_cast hu.le
    calc (H.readᶜ.ncard : ℝ) = Real.logb q ((q : ℝ) ^ H.readᶜ.ncard) :=
          (Real.logb_self_pow (zero_lt_one.trans hq1) hq1.ne' _).symm
      _ ≤ Real.logb q K := Real.logb_le_logb_of_le hq1 (pow_pos (zero_lt_one.trans hq1) _) hpow
  have hinp_ge : (n : ℝ) - Fintype.card (LiveInput c) ≤ Real.logb q K := by
    have hsumR : (H.read.ncard : ℝ) + H.readᶜ.ncard = n := by exact_mod_cast hsum
    have hleR : (H.read.ncard : ℝ) ≤ Fintype.card (LiveInput c) := Nat.cast_le.mpr hread_le
    linarith
  have hmul := mul_le_mul_of_nonneg_left hinp_ge (neg_nonneg.mpr hc_n)
  rw [abs_of_nonpos hc_n]
  linarith

/-- Rescaled supply inequality turning a hypergraph width bound into the `Demand` supply shape on
`w̃ = (w - c_n * n) / (1 - c_n)` and `s̃ = (r - 1) * g + n`. -/
private theorem rescaled_hyperSupply_le {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b)
    {η : ℝ} (hη : 0 < η) (C : ℝ) (n : ℕ) {g l : ℕ} (v : ℕ) (w : ℝ) {e_val logK : ℝ} (hg : l ≤ g)
    (he_nn : 0 ≤ e_val)
    (he_in : (|max (b : ℝ) (-a)| / (1 - max (b : ℝ) (-a))) * logK ≤ supplyRate r a b * e_val)
    (hw : w ≤ (((r + 1 : ℕ) : ℝ) * a + b) * l +
      (max (b : ℝ) (-a) * n + |max (b : ℝ) (-a)| * logK) +
      (η * (1 - max (b : ℝ) (-a))) * v + C) :
    let c_n := max (b : ℝ) (-a)
    let A := supplyRate r a b
    let s_tilde := ((r : ℝ) - 1) * g + n
    (w - c_n * n) / (1 - c_n) ≤ (A + η) * (s_tilde - n + e_val) + η * v + C / (1 - c_n) := by
  obtain ⟨hA, -, hc_s, h1c_n⟩ := supplyRate_pos_and_inv hcert
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  have hr1_pos : 0 < (r : ℝ) - 1 := by linarith
  intro c_n A s_tilde
  have hgate : (((r + 1 : ℕ) : ℝ) * a + b) * (l : ℝ) ≤ A * (1 - c_n) * (s_tilde - n) := by
    have hlR : (l : ℝ) ≤ g := Nat.cast_le.mpr hg
    have h1 : (((r + 1 : ℕ) : ℝ) * a + b) * (l : ℝ) ≤ (((r + 1 : ℕ) : ℝ) * a + b) * g :=
      mul_le_mul_of_nonneg_left hlR hc_s.le
    have h2 : A * (1 - c_n) * (s_tilde - n) = (((r + 1 : ℕ) : ℝ) * a + b) * g := by
      dsimp only [A, supplyRate, c_n, s_tilde]
      have hne1 : (r : ℝ) - 1 ≠ 0 := hr1_pos.ne'
      have hne2 : 1 - max (b : ℝ) (-a) ≠ 0 := h1c_n.ne'
      field_simp [hne1, hne2]
      ring
    linarith
  have hw_div : (w - c_n * n) / (1 - c_n) ≤
      A * (s_tilde - n) + (|c_n| / (1 - c_n)) * logK + η * v + C / (1 - c_n) := by
    rw [div_le_iff₀ h1c_n]
    have hrhs : (A * (s_tilde - n) + (|c_n| / (1 - c_n)) * logK + η * v + C / (1 - c_n)) *
        (1 - c_n) =
        A * (1 - c_n) * (s_tilde - n) + |c_n| * logK + (η * (1 - c_n)) * v + C := by
      have hne : 1 - c_n ≠ 0 := h1c_n.ne'
      field_simp [hne]
    rw [hrhs]
    dsimp only [c_n] at hw ⊢
    linarith [hw, hgate]
  have hs_nn : 0 ≤ s_tilde - n := by
    dsimp only [s_tilde]
    have : 0 ≤ ((r : ℝ) - 1) * g := mul_nonneg hr1_pos.le (Nat.cast_nonneg g)
    linarith
  have hAe : (|c_n| / (1 - c_n)) * logK ≤ (A + η) * e_val :=
    he_in.trans (mul_le_mul_of_nonneg_right (by linarith) he_nn)
  have hAs : A * (s_tilde - n) ≤ (A + η) * (s_tilde - n) :=
    mul_le_mul_of_nonneg_right (by linarith) hs_nn
  linarith

/-- Shared asymptotic demand-vs-supply engine for both deterministic and nondeterministic
hypergraph lower bounds. -/
private theorem eventually_lt_of_hyperSupply {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ > 0, ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ (g l inp v w : ℕ),
      l ≤ g → v ≤ g + 1 →
      (w : ℝ) ≤ (((r + 1 : ℕ) : ℝ) * a + b) * l +
        max (b : ℝ) (-a) * inp + ξ * v + C →
      max (b : ℝ) (-a) * (inp : ℝ) ≤
        max (b : ℝ) (-a) * n + |max (b : ℝ) (-a)| * Real.logb (Nat.card U) (K n) →
      Real.logb (Nat.card U) (S n).ncard ≤
        (w : ℝ) + (3 * (r : ℝ) + 2) + 3 * Real.logb (Nat.card U) (K n) +
          Real.logb (Nat.card U) ((v : ℝ) + 1) →
      ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * g := by
  obtain ⟨hA, hA_inv, hc_s, h1c_n⟩ := supplyRate_pos_and_inv hcert
  set c_n := max (b : ℝ) (-a)
  set A := supplyRate r a b
  set q := Nat.card U
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card (α := U))
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  set κ : ℝ := max 1 ((4 + 1 / Real.log 2) / (1 - c_n))
  have hκ0 : 0 ≤ κ := le_trans zero_le_one (le_max_left _ _)
  set M_K : ℝ := max (3 / (1 - c_n)) ((|c_n| / (1 - c_n)) / A)
  set e : ℕ → ℝ := fun n =>
    ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) +
      (3 * (r : ℝ) + 2) / (1 - c_n) + M_K * Real.logb q (K n)
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have h1 : (fun n : ℕ => ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n)) =o[atTop]
        fun n => (n : ℝ) :=
      ((isLittleO_sub_logb_ncard hSK.isLittleO_deficit).const_mul_left (1 / (1 - c_n))).congr_left
        fun n => by ring
    have h2 : (fun _ : ℕ => (3 * (r : ℝ) + 2) / (1 - c_n)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr
        (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    have h3 : (fun n : ℕ => M_K * Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hSK.isLittleO_log.const_mul_left (M_K / Real.log q)).congr_left fun n => by
        simp only [Real.logb]
        ring
    exact (h1.add h2).add h3
  obtain ⟨η₀, hη₀, H⟩ := eventually_lt_of_demand hA hκ0 hε
  refine ⟨η₀ * (1 - c_n), mul_pos hη₀ h1c_n, fun C => ?_⟩
  filter_upwards [H η₀ hη₀ le_rfl (C / (1 - c_n)) e he, hSK.eventually_rectangleFree,
    eventually_card_mul_sq_le_ncard hSK] with n hn hfreen hbign
  intro g l inp v w hlg hvg hw hinp hdemand
  have hSne : (S n).Nonempty := by
    rw [← ncard_pos (toFinite _)]
    exact lt_of_lt_of_le (Nat.mul_pos Nat.card_pos (pow_pos hfreen.pos 2)) hbign
  have hlogS := logb_ncard_le_self hSne
  have hlogK_nn : 0 ≤ Real.logb q (K n) :=
    Real.logb_nonneg hq1 (by exact_mod_cast hfreen.pos)
  have hMK_nn : 0 ≤ M_K := le_trans (by positivity) (le_max_left _ _)
  have he_nn : 0 ≤ e n := by
    dsimp only [e]
    have hterm1 : 0 ≤ ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) :=
      div_nonneg (by linarith) h1c_n.le
    have hterm2 : 0 ≤ (3 * (r : ℝ) + 2) / (1 - c_n) := by positivity
    have hterm3 : 0 ≤ M_K * Real.logb q (K n) := mul_nonneg hMK_nn hlogK_nn
    linarith
  have he_in : (|c_n| / (1 - c_n)) * Real.logb q (K n) ≤ A * e n := by
    have hM2 : (|c_n| / (1 - c_n)) / A ≤ M_K := le_max_right _ _
    have h1 : |c_n| / (1 - c_n) ≤ A * M_K := by
      have := mul_le_mul_of_nonneg_left hM2 hA.le
      rwa [mul_div_cancel₀ _ hA.ne'] at this
    have h2 : (|c_n| / (1 - c_n)) * Real.logb q (K n) ≤ A * (M_K * Real.logb q (K n)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 hlogK_nn
    dsimp only [e]
    have hterm1 : 0 ≤ ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) :=
      div_nonneg (by linarith) h1c_n.le
    have hterm2 : 0 ≤ (3 * (r : ℝ) + 2) / (1 - c_n) := by positivity
    nlinarith
  set s_tilde : ℝ := ((r : ℝ) - 1) * g + n
  set w_tilde : ℝ := ((w : ℝ) - c_n * n) / (1 - c_n)
  have hsupply := rescaled_hyperSupply_le hcert hη₀ C n v w hlg he_nn he_in (by linarith [hw, hinp])
  have hv_le : (v : ℝ) ≤ κ * (n + s_tilde + 1) := by
    have hv1 : (v : ℝ) ≤ (g : ℝ) + 1 := by exact_mod_cast hvg
    have hg_le : (g : ℝ) ≤ ((r : ℝ) - 1) * g :=
      le_mul_of_one_le_left (Nat.cast_nonneg g) (by linarith)
    have hsum_ge : (g : ℝ) + 1 ≤ n + s_tilde + 1 := by
      dsimp only [s_tilde]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hκ1 : 1 ≤ κ := le_max_left _ _
    nlinarith [Nat.cast_nonneg (α := ℝ) v]
  have hdem_tilde : (n : ℝ) ≤ w_tilde + e n + κ * Real.log ((v : ℝ) + 1) := by
    have hid : (n : ℝ) - w_tilde = ((n : ℝ) - w) / (1 - c_n) := by
      dsimp only [w_tilde]
      have hne : 1 - c_n ≠ 0 := h1c_n.ne'
      field_simp [hne]
      ring
    have hnw : ((n : ℝ) - w) / (1 - c_n) ≤
        ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) +
          (3 * (r : ℝ) + 2) / (1 - c_n) + (3 / (1 - c_n)) * Real.logb q (K n) +
          Real.logb q ((v : ℝ) + 1) / (1 - c_n) := by
      rw [div_le_iff₀ h1c_n]
      have hrhs : (((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) +
          (3 * (r : ℝ) + 2) / (1 - c_n) + (3 / (1 - c_n)) * Real.logb q (K n) +
          Real.logb q ((v : ℝ) + 1) / (1 - c_n)) * (1 - c_n) =
          ((n : ℝ) - Real.logb q (S n).ncard) + (3 * (r : ℝ) + 2) +
            3 * Real.logb q (K n) + Real.logb q ((v : ℝ) + 1) := by
        have hne : 1 - c_n ≠ 0 := h1c_n.ne'
        field_simp [hne]
      rw [hrhs]
      linarith
    have hMK1 : (3 / (1 - c_n)) * Real.logb q (K n) ≤ M_K * Real.logb q (K n) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogK_nn
    have hlogV : Real.logb q ((v : ℝ) + 1) / (1 - c_n) ≤ κ * Real.log ((v : ℝ) + 1) := by
      have h1 : Real.logb q ((v : ℝ) + 1) ≤ (4 + 1 / Real.log 2) * Real.log ((v : ℝ) + 1) :=
        logb_le_mul_log hq2 (by linarith [Nat.cast_nonneg (α := ℝ) v])
      have h2 := div_le_div_of_nonneg_right h1 h1c_n.le
      rw [mul_div_right_comm] at h2
      refine h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
      exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) v])
    dsimp only [e]
    linarith [hid, hnw, hMK1, hlogV]
  have hs_nn : 0 ≤ s_tilde := by
    dsimp only [s_tilde]
    have : 0 ≤ ((r : ℝ) - 1) * g := mul_nonneg (by linarith) (Nat.cast_nonneg g)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hres := hn s_tilde v w_tilde hs_nn (Nat.cast_nonneg v) hv_le hdem_tilde hsupply
  rw [hA_inv] at hres
  dsimp only [s_tilde] at hres
  linarith

/-! ### General worst-case, average-case, and nondeterministic meta-theorems -/

/-- **Worst-case hypergraph frontier lower bound (charging only multiary gates).** From any
verified `HyperDualCert r K₀ a b`, every circuit of fan-in at most `r` deciding a dense
rectangle-free family `S_n ⊆ U^n` has `(r - 1) * c.multiarySize > (hyperCoeff r a b - ε) * n`
for all large `n` (constant and unary gates are completely free). -/
theorem eventually_lt_mul_multiarySize_of_cert {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * c.multiarySize := by
  obtain ⟨ξ, hξ, H⟩ := eventually_lt_of_hyperSupply hcert hSK hε
  obtain ⟨C, hC⟩ := exists_layout_hyperWidth_le hcert hξ
  filter_upwards [H C, hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK] with
    n hn hfreen hbign
  intro σ I Acc c hfan hS
  obtain ⟨lay, hlay⟩ := hC c hfan
  set N := hyperNetwork c I Acc lay
  have hacc : N.accepted = S n := by
    rw [accepted_hyperNetwork]
    ext x
    exact (hS x).symm
  have hfreeN : RectangleFree N.accepted (K n) := hacc ▸ hfreen
  have hbigN : Nat.card U * K n ^ 2 ≤ N.accepted.ncard := hacc ▸ hbign
  have hu : Nat.card U ^ N.readᶜ.ncard < K n :=
    hfreeN.pow_ncard_compl_lt N.dependsOn_read hbigN
  have hinp := input_supply_le_of_unread_lt c I Acc lay (max (b : ℝ) (-a)) hu
  have hmr : max r 1 = r := max_eq_left (by have := hcert.hr; omega)
  have hdem := N.logb_ncard_accepted_le hfreeN hbigN lay (w := hyperWidth c lay)
    (d := 2 * (r + 1)) (m := r) (width_hyperNetwork c I Acc lay).le
    (maxDegreeLE_hyperNetwork hfan I Acc lay)
    (fun u => hmr ▸ ncard_readAt_hyperNetwork_le hfan I Acc lay u)
  rw [hacc] at hdem
  have hdem' : Real.logb (Nat.card U) (S n).ncard ≤
      (hyperWidth c lay : ℝ) + (3 * (r : ℝ) + 2) + 3 * Real.logb (Nat.card U) (K n) +
        Real.logb (Nat.card U) ((Nat.card (HyperNode c) : ℝ) + 1) := by
    refine hdem.trans_eq ?_
    push_cast
    ring
  exact hn c.multiarySize (Fintype.card (LiveGate c)) (Fintype.card (LiveInput c))
    (Nat.card (HyperNode c)) (hyperWidth c lay) (card_liveGate_le_multiarySize c)
    (card_hyperNode_le c) hlay hinp hdem'

/-- **Worst-case hypergraph frontier lower bound (`innerSize`).** -/
theorem eventually_lt_mul_innerSize_of_cert {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * c.innerSize := by
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  filter_upwards [eventually_lt_mul_multiarySize_of_cert.{u, v} hcert hSK hε] with n hn
  intro σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize) (by linarith))

/-- **Nondeterministic hypergraph frontier lower bound (charging only multiary gates).** Whenever
`b ≤ 0` (so `max b (-a) ≤ 0`), every nondeterministic circuit `c : Circuit σ (n + k) 1` of fan-in
at most `r` with any number `k` of witness inputs deciding `S_n` satisfies
`(r - 1) * c.multiarySize > (hyperCoeff r a b - ε) * n` for all large `n`. -/
theorem eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert
    {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * c.multiarySize := by
  obtain ⟨ξ, hξ, H⟩ := eventually_lt_of_hyperSupply hcert hSK hε
  obtain ⟨C, hC⟩ := exists_layout_hyperWidth_le hcert hξ
  have hc_n_le : max (b : ℝ) (-a) ≤ 0 :=
    max_le (Rat.cast_nonpos.mpr hb) (neg_nonpos.mpr (Rat.cast_nonneg.mpr hcert.ha.le))
  filter_upwards [H C, hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK] with
    n hn hfreen hbign
  intro k σ I Acc c hfan hS
  obtain ⟨lay, hlay⟩ := hC c hfan
  set N := hiddenHyperNetwork c I Acc lay
  have hacc : N.accepted = S n := by
    rw [accepted_hiddenHyperNetwork]
    ext x
    exact (hS x).symm
  have hfreeN : RectangleFree N.accepted (K n) := hacc ▸ hfreen
  have hbigN : Nat.card U * K n ^ 2 ≤ N.accepted.ncard := hacc ▸ hbign
  have hu : Nat.card U ^ N.readᶜ.ncard < K n :=
    hfreeN.pow_ncard_compl_lt N.dependsOn_read hbigN
  have hinp := input_supply_le_of_hidden_unread_lt c I Acc lay hc_n_le hu
  have hmr : max r 1 = r := max_eq_left (by have := hcert.hr; omega)
  have hreadAt (u : HyperNode c) : (N.readAt u).ncard ≤ r :=
    (Network.ncard_readAt_hide_le _ u).trans
      ((Network.ncard_readAt_reindex _ _ u).trans_le
        (hmr ▸ ncard_readAt_hyperNetwork_le hfan I Acc lay u))
  have hdem := N.logb_ncard_accepted_le hfreeN hbigN lay (w := hyperWidth c lay)
    (d := 2 * (r + 1)) (m := r) (width_hyperNetwork c I Acc lay).le
    (maxDegreeLE_hyperNetwork hfan I Acc lay) hreadAt
  rw [hacc] at hdem
  have hdem' : Real.logb (Nat.card U) (S n).ncard ≤
      (hyperWidth c lay : ℝ) + (3 * (r : ℝ) + 2) + 3 * Real.logb (Nat.card U) (K n) +
        Real.logb (Nat.card U) ((Nat.card (HyperNode c) : ℝ) + 1) := by
    refine hdem.trans_eq ?_
    push_cast
    ring
  exact hn c.multiarySize (Fintype.card (LiveGate c)) (Fintype.card (LiveInput c))
    (Nat.card (HyperNode c)) (hyperWidth c lay) (card_liveGate_le_multiarySize c)
    (card_hyperNode_le c) hlay hinp hdem'

/-- **Nondeterministic hypergraph frontier lower bound (`innerSize`).** -/
theorem eventually_lt_mul_innerSize_of_nondeterministicDecides_of_cert
    {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * c.innerSize := by
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  filter_upwards [eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert.{u, v}
    hcert hb hSK hε] with n hn
  intro k σ I Acc c hfan hS
  exact (hn k σ I Acc c hfan hS).trans_le
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize) (by linarith))

/-- Single-circuit agreement bound for a narrow hypergraph layout. -/
private theorem agreement_le_of_hyperLayout {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n K r : ℕ} (hr : 2 ≤ r) (c : Circuit σ n 1) (hfan : c.FanInAtMost r)
    (I : Interpretation σ U) (Acc : Set U) {S : Set (Fin n → U)} {b_bias : ℝ}
    (hS : RectangleBias S K b_bias) (hb : 0 ≤ b_bias) (lay : Layout (HyperNode c))
    (hu : Nat.card U ^ (hyperNetwork c I Acc lay).readᶜ.ncard < K) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias +
      ((K ^ 3 * (Nat.card (HyperNode c) + 1) *
        Nat.card U ^ (hyperWidth c lay + (3 * r + 2)) : ℕ) : ℝ) / (Nat.card U : ℝ) ^ n := by
  set q := Nat.card U
  set V := Nat.card (HyperNode c)
  set w := hyperWidth c lay
  have hmr : max r 1 = r := max_eq_left (by omega)
  have bound (A : Set U) :
      |signedCount S {x | c.eval I x 0 ∈ A}| ≤
        2 * b_bias * {x | c.eval I x 0 ∈ A}.ncard +
          (((K - 1) ^ 2 * (V * q ^ (w + (3 * r + 2)) +
            q ^ (hyperNetwork c I Acc lay).readᶜ.ncard) : ℕ) : ℝ) := by
    have h := (hyperNetwork c I A lay).abs_signedCount_accepted_le lay
      (fun _ _ _ => satisfies_unique c I A lay) hb hS (w := w) (d := 2 * (r + 1)) (m := r)
      (width_hyperNetwork c I A lay).le (maxDegreeLE_hyperNetwork hfan I A lay)
      (fun u => hmr ▸ ncard_readAt_hyperNetwork_le hfan I A lay u)
    have hread : (hyperNetwork c I A lay).read = (hyperNetwork c I Acc lay).read := by
      rw [read_hyperNetwork, read_hyperNetwork]
    have hexp : w + 2 * (r + 1) + r = w + (3 * r + 2) := by omega
    rw [accepted_hyperNetwork, hread, hexp] at h
    exact h
  have hcomb := agreement_le (bound Acc) (bound Accᶜ)
  have hcard : (Nat.card (Fin n → U) : ℝ) = (q : ℝ) ^ n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    push_cast
    rfl
  rw [hcard] at hcomb
  have hres : (K - 1) ^ 2 * (V * q ^ (w + (3 * r + 2)) +
      q ^ (hyperNetwork c I Acc lay).readᶜ.ncard) ≤ K ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) := by
    have hq1 : 1 ≤ q ^ (w + (3 * r + 2)) := Nat.one_le_pow _ _ Nat.card_pos
    calc _ ≤ K ^ 2 * (V * K * q ^ (w + (3 * r + 2)) + K * q ^ (w + (3 * r + 2))) := by
          gcongr
          · omega
          · exact Nat.le_mul_of_pos_right _ (lt_of_le_of_lt (Nat.zero_le _) hu)
          · exact hu.le.trans (Nat.le_mul_of_pos_right _ hq1)
      _ = K ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) := by ring
  have hresR : (((K - 1) ^ 2 * (V * q ^ (w + (3 * r + 2)) +
      q ^ (hyperNetwork c I Acc lay).readᶜ.ncard) : ℕ) : ℝ) ≤
      ((K ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) : ℕ) : ℝ) := by exact_mod_cast hres
  have hN_pos : (0 : ℝ) < (q : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr Nat.card_pos) n
  refine hcomb.trans ?_
  have h1 : (1 + 2 * b_bias) / 2 = 1 / 2 + b_bias := by ring
  have h2 (R : ℝ) : (R + R) / (2 * (q : ℝ) ^ n) = R / (q : ℝ) ^ n := by
    field_simp [hN_pos.ne']
    ring
  rw [h1, h2]
  linarith [div_le_div_of_nonneg_right hresR hN_pos.le]

/-- Narrow-unread branch of the average-case hypergraph bound at a fixed input length `n`. -/
private theorem agreement_le_of_unread_lt_step {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n K' r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b)
    {ε η C b_bias γ : ℝ} (hη : 0 < η) (hγ : 0 < γ) (hK'2 : 2 ≤ K')
    (c : Circuit σ n 1) (hfan : c.FanInAtMost r) (I : Interpretation σ U) (Acc : Set U)
    {S : Set (Fin n → U)} (hS : RectangleBias S K' b_bias) (hb_nn : 0 ≤ b_bias)
    (lay : Layout (HyperNode c))
    (hlay : (hyperWidth c lay : ℝ) ≤
      (((r + 1 : ℕ) : ℝ) * a + b) * Fintype.card (LiveGate c) +
        max (b : ℝ) (-a) * Fintype.card (LiveInput c) +
        (η * (1 - max (b : ℝ) (-a))) * Nat.card (HyperNode c) + C)
    (hu : Nat.card U ^ (hyperNetwork c I Acc lay).readᶜ.ncard < K')
    (hsize : ((r : ℝ) - 1) * c.multiarySize ≤ ((hyperCoeff r a b : ℝ) - ε) * n)
    (hγ_le : γ / Real.log 2 ≤ (1 - max (b : ℝ) (-a)) * supplyRate r a b * ε / 2)
    (hn : ∀ s v w : ℝ, 0 ≤ s → 0 ≤ v →
      v ≤ max 1 ((4 + 1 / Real.log 2) / (1 - max (b : ℝ) (-a))) * (n + s + 1) →
      s ≤ (1 + 1 / supplyRate r a b - ε) * n →
      w ≤ (supplyRate r a b + η) * (s - n +
        ((3 * (r : ℝ) + 2) / (1 - max (b : ℝ) (-a)) +
          max (3 / (1 - max (b : ℝ) (-a)))
            ((|max (b : ℝ) (-a)| / (1 - max (b : ℝ) (-a))) / supplyRate r a b) *
            Real.logb (Nat.card U) K')) +
        η * v + C / (1 - max (b : ℝ) (-a)) →
      w + ((3 * (r : ℝ) + 2) / (1 - max (b : ℝ) (-a)) +
        max (3 / (1 - max (b : ℝ) (-a)))
          ((|max (b : ℝ) (-a)| / (1 - max (b : ℝ) (-a))) / supplyRate r a b) *
          Real.logb (Nat.card U) K') +
        max 1 ((4 + 1 / Real.log 2) / (1 - max (b : ℝ) (-a))) * Real.log (v + 1) <
        (1 - supplyRate r a b * ε / 2) * n) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias + Real.exp (-(γ * n)) := by
  obtain ⟨hA, hA_inv, _, h1c_n⟩ := supplyRate_pos_and_inv hcert
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  set c_n := max (b : ℝ) (-a)
  set A := supplyRate r a b
  set κ : ℝ := max 1 ((4 + 1 / Real.log 2) / (1 - c_n))
  set q := Nat.card U
  have hq1_nat : 1 < q := Finite.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq1_nat
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1_nat
  set M_K : ℝ := max (3 / (1 - c_n)) ((|c_n| / (1 - c_n)) / A)
  set e : ℝ := (3 * (r : ℝ) + 2) / (1 - c_n) + M_K * Real.logb q K'
  have hinp := input_supply_le_of_unread_lt c I Acc lay c_n hu
  have hlogK_nn : 0 ≤ Real.logb q K' :=
    Real.logb_nonneg hq1 (by exact_mod_cast (show 1 ≤ K' by omega))
  have hMK_nn : 0 ≤ M_K := le_trans (by positivity) (le_max_left _ _)
  have hterm_nn : 0 ≤ (3 * (r : ℝ) + 2) / (1 - c_n) := by positivity
  have he_nn : 0 ≤ e := add_nonneg hterm_nn (mul_nonneg hMK_nn hlogK_nn)
  have he_in : (|c_n| / (1 - c_n)) * Real.logb q K' ≤ A * e := by
    have hM2 : (|c_n| / (1 - c_n)) / A ≤ M_K := le_max_right _ _
    have h1 : |c_n| / (1 - c_n) ≤ A * M_K := by
      have := mul_le_mul_of_nonneg_left hM2 hA.le
      rwa [mul_div_cancel₀ _ hA.ne'] at this
    have h2 : (|c_n| / (1 - c_n)) * Real.logb q K' ≤ A * (M_K * Real.logb q K') := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 hlogK_nn
    have hAe : A * e = A * ((3 * (r : ℝ) + 2) / (1 - c_n)) + A * (M_K * Real.logb q K') := by
      dsimp only [e]
      ring
    linarith [mul_nonneg hA.le hterm_nn]
  set V := Nat.card (HyperNode c)
  set w := hyperWidth c lay
  set s_tilde : ℝ := ((r : ℝ) - 1) * c.multiarySize + n
  set w_tilde : ℝ := ((w : ℝ) - c_n * n) / (1 - c_n)
  have hsupply := rescaled_hyperSupply_le hcert hη C n V w (card_liveGate_le_multiarySize c)
    he_nn he_in (by linarith [hlay, hinp])
  have hs_nn : 0 ≤ s_tilde := by
    dsimp only [s_tilde]
    have : 0 ≤ ((r : ℝ) - 1) * c.multiarySize := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hv_le : (V : ℝ) ≤ κ * (n + s_tilde + 1) := by
    have hv1 : (V : ℝ) ≤ (c.multiarySize : ℝ) + 1 := by exact_mod_cast card_hyperNode_le c
    have hg_le : (c.multiarySize : ℝ) ≤ ((r : ℝ) - 1) * c.multiarySize :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
    have hκ1 : 1 ≤ κ := le_max_left _ _
    have h1 : (n : ℝ) + s_tilde + 1 ≤ κ * (n + s_tilde + 1) :=
      le_mul_of_one_le_left (by linarith [Nat.cast_nonneg (α := ℝ) n]) hκ1
    dsimp only [s_tilde] at h1 ⊢
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs_le : s_tilde ≤ (1 + 1 / A - ε) * n := by
    rw [hA_inv]
    dsimp only [s_tilde]
    linarith
  have hmargin := hn s_tilde V w_tilde hs_nn (Nat.cast_nonneg V) hv_le hs_le hsupply
  have hmul_margin := mul_lt_mul_of_pos_left hmargin h1c_n
  have hlhs : (1 - c_n) * (w_tilde + e + κ * Real.log ((V : ℝ) + 1)) =
      ((w : ℝ) - c_n * n) + (1 - c_n) * e + (1 - c_n) * (κ * Real.log ((V : ℝ) + 1)) := by
    dsimp only [w_tilde]
    have hne : 1 - c_n ≠ 0 := h1c_n.ne'
    field_simp [hne]
  have hrhs : (1 - c_n) * ((1 - A * ε / 2) * n) =
      ((n : ℝ) - c_n * n) - ((1 - c_n) * A * ε / 2) * n := by
    ring
  have he_ge : (3 * (r : ℝ) + 2) + 3 * Real.logb q K' ≤ (1 - c_n) * e := by
    have hMK1 : 3 / (1 - c_n) ≤ M_K := le_max_left _ _
    have h3 : 3 ≤ (1 - c_n) * M_K := by
      have := mul_le_mul_of_nonneg_left hMK1 h1c_n.le
      rwa [mul_div_cancel₀ _ h1c_n.ne'] at this
    have h1 : (1 - c_n) * ((3 * (r : ℝ) + 2) / (1 - c_n)) = 3 * (r : ℝ) + 2 :=
      mul_div_cancel₀ _ h1c_n.ne'
    have hmul_e : (1 - c_n) * e =
        (1 - c_n) * ((3 * (r : ℝ) + 2) / (1 - c_n)) + ((1 - c_n) * M_K) * Real.logb q K' := by
      dsimp only [e]
      ring
    linarith [mul_le_mul_of_nonneg_right h3 hlogK_nn]
  have hlogV_ge : Real.logb q ((V : ℝ) + 1) ≤ (1 - c_n) * (κ * Real.log ((V : ℝ) + 1)) := by
    have h1 : Real.logb q ((V : ℝ) + 1) ≤ (4 + 1 / Real.log 2) * Real.log ((V : ℝ) + 1) :=
      logb_le_mul_log hq2 (by linarith [Nat.cast_nonneg (α := ℝ) V])
    have hκ2 : (4 + 1 / Real.log 2) / (1 - c_n) ≤ κ := le_max_right _ _
    have h2 : 4 + 1 / Real.log 2 ≤ (1 - c_n) * κ := by
      have := mul_le_mul_of_nonneg_left hκ2 h1c_n.le
      rwa [mul_div_cancel₀ _ h1c_n.ne'] at this
    rw [← mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) V])))
  have hlogR : Real.logb q ((K' ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) : ℕ) : ℝ) ≤
      (1 - γ / Real.log 2) * n := by
    have hK_pos : (0 : ℝ) < K' := by exact_mod_cast (show 0 < K' by omega)
    have hV_pos : (0 : ℝ) < (V : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) V]
    have hq_pos : (0 : ℝ) < q := zero_lt_one.trans hq1
    push_cast
    rw [Real.logb_mul (mul_pos (pow_pos hK_pos 3) hV_pos).ne' (pow_pos hq_pos _).ne',
      Real.logb_mul (pow_pos hK_pos 3).ne' hV_pos.ne',
      Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq1]
    push_cast
    have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hγn : γ / Real.log 2 * n ≤ ((1 - c_n) * A * ε / 2) * n :=
      mul_le_mul_of_nonneg_right hγ_le hn_nn
    linarith [hmul_margin, hlhs, hrhs, he_ge, hlogV_ge, hγn]
  have hagr := agreement_le_of_hyperLayout hcert.hr c hfan I Acc hS hb_nn lay hu
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp := div_pow_le_exp hq2 (by positivity) (div_nonneg hγ.le hl2.le) hlogR
  rw [div_mul_cancel₀ _ hl2.ne'] at hexp
  linarith

/-- **Average-case hypergraph frontier lower bound (charging only multiary gates).** From any
verified `HyperDualCert r K₀ a b` and `ε > 0`, there is an exponent `γ > 0` (uniform over the
alphabet `U`, target family `S`, rectangle threshold `K`, bias `b_bias`, basis `σ`,
interpretation `I`, and accepting set `Acc`) such that every circuit of fan-in at most `r` with
`(r - 1) * c.multiarySize ≤ (hyperCoeff r a b - ε) * n` agrees with `S_n` on at most
`1 / 2 + b_bias n + exp (-γ * n)` of all inputs in `U^n`. -/
theorem eventually_agreement_le_multiarySize_of_cert {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r : ℝ) - 1) * c.multiarySize ≤ ((hyperCoeff r a b : ℝ) - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) := by
  obtain ⟨hA, _, _, h1c_n⟩ := supplyRate_pos_and_inv hcert
  set c_n := max (b : ℝ) (-a)
  set A := supplyRate r a b
  set α := (1 - c_n) * A
  have hα : 0 < α := mul_pos h1c_n hA
  set κ : ℝ := max 1 ((4 + 1 / Real.log 2) / (1 - c_n))
  have hκ0 : 0 ≤ κ := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨η, hη, H⟩ := eventually_add_lt_of_le hA hκ0 hε
  obtain ⟨C, hC⟩ := exists_layout_hyperWidth_le hcert (ξ := η * (1 - c_n)) (mul_pos hη h1c_n)
  set μ := min (α * ε / 2) (1 / 2)
  have hμ : 0 < μ := lt_min (by positivity) (by norm_num)
  set γ := μ * Real.log 2
  have hγ : 0 < γ := mul_pos hμ (Real.log_pos one_lt_two)
  refine ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => ?_⟩
  set q := Nat.card U
  have hq1_nat : 1 < q := Finite.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq1_nat
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1_nat
  set K' : ℕ → ℕ := fun n => max (K n) 2
  have hlogbK : (fun n => Real.logb q (K' n)) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_logb_max_two hK q
  set M_K : ℝ := max (3 / (1 - c_n)) ((|c_n| / (1 - c_n)) / A)
  set e : ℕ → ℝ := fun n => (3 * (r : ℝ) + 2) / (1 - c_n) + M_K * Real.logb q (K' n)
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have hconst : (fun _ : ℕ => (3 * (r : ℝ) + 2) / (1 - c_n)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr
        (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    exact hconst.add (hlogbK.const_mul_left M_K)
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 + 2 * Real.logb q (K' n) ≤ (1 - 1 / 2) * n := by
    have ho : (fun n : ℕ => 1 + 2 * Real.logb q (K' n)) =o[atTop] fun n => (n : ℝ) :=
      (isLittleO_const_left.mpr
        (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))).add
        (hlogbK.const_mul_left 2)
    filter_upwards [ho.bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    linarith [le_abs_self (1 + 2 * Real.logb q (K' n))]
  filter_upwards [H (C / (1 - c_n)) e he, hbias, hsmall] with n hn hbiasn hsmalln
  intro σ I Acc c hfan hsize
  obtain ⟨lay, hlay⟩ := hC c hfan
  have hS : RectangleBias (S n) (K' n) (b_bias n) := hbiasn.mono (le_max_left _ _)
  have hK'2 : 2 ≤ K' n := le_max_right _ _
  have hb_nn : 0 ≤ b_bias n := hS.nonneg (by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact le_pow_half_of_logb hq1_nat (by omega) hsmalln)
  by_cases hu : K' n ≤ q ^ (hyperNetwork c I Acc lay).readᶜ.ncard
  · have hbound (A_set : Set U) :
        |signedCount (S n) {x | c.eval I x 0 ∈ A_set}| ≤
          2 * b_bias n * {x | c.eval I x 0 ∈ A_set}.ncard + ((q * K' n ^ 2 : ℕ) : ℝ) := by
      have hread : (hyperNetwork c I A_set lay).read = (hyperNetwork c I Acc lay).read := by
        rw [read_hyperNetwork, read_hyperNetwork]
      have h := hS.abs_signedCount_le_of_dependsOn hb_nn
        (hyperNetwork c I A_set lay).dependsOn_read (by omega) (hread.symm ▸ hu)
      rwa [accepted_hyperNetwork] at h
    have hcomb := agreement_le (hbound Acc) (hbound Accᶜ)
    have hcard : (Nat.card (Fin n → U) : ℝ) = (q : ℝ) ^ n := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
      push_cast
      rfl
    rw [hcard] at hcomb
    have hN_pos : (0 : ℝ) < (q : ℝ) ^ n := pow_pos (by linarith) n
    have h1 : (1 + 2 * b_bias n) / 2 = 1 / 2 + b_bias n := by ring
    have h2 (R : ℝ) : (R + R) / (2 * (q : ℝ) ^ n) = R / (q : ℝ) ^ n := by
      field_simp [hN_pos.ne']
      ring
    rw [h1, h2] at hcomb
    have hlogR : Real.logb q ((q * K' n ^ 2 : ℕ) : ℝ) ≤ (1 - μ) * n := by
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one hq1]
      push_cast
      have hμ_le : μ ≤ 1 / 2 := min_le_right _ _
      have hμn : μ * n ≤ 1 / 2 * n := mul_le_mul_of_nonneg_right hμ_le (Nat.cast_nonneg n)
      linarith
    have hexp := div_pow_le_exp hq2 (by positivity) hμ.le hlogR
    dsimp only [γ]
    linarith
  · push Not at hu
    have hγ_le : γ / Real.log 2 ≤ (1 - c_n) * A * ε / 2 := by
      have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      dsimp only [γ]
      rw [mul_div_cancel_right₀ _ hl2]
      exact min_le_left _ _
    exact agreement_le_of_unread_lt_step hcert hη hγ hK'2 c hfan I Acc hS hb_nn lay
      hlay hu hsize hγ_le hn

/-- **Average-case hypergraph frontier lower bound (`innerSize`).** -/
theorem eventually_agreement_le_innerSize_of_cert {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r : ℝ) - 1) * c.innerSize ≤ ((hyperCoeff r a b : ℝ) - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) := by
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_multiarySize_of_cert.{u, v} hcert hε
  refine ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => ?_⟩
  filter_upwards [H U S K b_bias hbias hK] with n hn σ I Acc c hfan hs
  exact hn σ I Acc c hfan
    ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize) (by linarith)).trans
      hs)

/-! ### Monotonicity wrappers for rational certificate constants -/

private theorem eventually_lt_multiary_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (L - ε) * n < m_r * c.multiarySize := by
  filter_upwards [eventually_lt_mul_multiarySize_of_cert.{u, v} hcert hSK hε] with n hn
  intro σ I Acc c hfan hS
  have h1 := hn σ I Acc c hfan hS
  rw [hm_r] at h1
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)).trans_lt h1

private theorem eventually_lt_inner_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (L - ε) * n < m_r * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_cert.{u, v} hcert hSK hε] with n hn
  intro σ I Acc c hfan hS
  have h1 := hn σ I Acc c hfan hS
  rw [hm_r] at h1
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)).trans_lt h1

private theorem eventually_lt_nondet_multiary_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (L - ε) * n < m_r * c.multiarySize := by
  filter_upwards [eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert.{u, v}
    hcert hb hSK hε] with n hn
  intro k σ I Acc c hfan hS
  have h1 := hn k σ I Acc c hfan hS
  rw [hm_r] at h1
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)).trans_lt h1

private theorem eventually_lt_nondet_inner_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (L - ε) * n < m_r * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_nondeterministicDecides_of_cert.{u, v}
    hcert hb hSK hε] with n hn
  intro k σ I Acc c hfan hS
  have h1 := hn k σ I Acc c hfan hS
  rw [hm_r] at h1
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)).trans_lt h1

private theorem eventually_agreement_multiary_of_le_coeff {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost r → m_r * c.multiarySize ≤ (L - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_multiarySize_of_cert.{u, v} hcert hε
  refine ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => ?_⟩
  filter_upwards [H U S K b_bias hbias hK] with n hn σ I Acc c hfan hs
  rw [← hm_r] at hs
  exact hn σ I Acc c hfan
    (hs.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)))

/-! ### Unconditional bounded-fan-in lower bounds (`r ∈ {3, 4, 8, 16, 64}`) -/

section ConcreteBounds

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-! #### Fan-in `r = 3` (Slepian + star-cone: `4.4199n`) -/

/-- **Strongest unconditional worst-case lower bound for fan-in at most `3`:**
`2 * c.multiarySize > (44199 / 10000 - ε) * n` (improving `4n` in `BoundedFanIn`). -/
theorem eventually_44199_lt_two_mul_multiarySize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (44199 / 10000 - ε) * n < 2 * c.multiarySize :=
  eventually_lt_multiary_of_le_coeff cert_r3_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Strongest unconditional `innerSize` lower bound for fan-in at most `3`:**
`2 * c.innerSize > (44199 / 10000 - ε) * n`. -/
theorem eventually_44199_lt_two_mul_innerSize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (44199 / 10000 - ε) * n < 2 * c.innerSize :=
  eventually_lt_inner_of_le_coeff cert_r3_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Strongest unconditional nondeterministic lower bound for fan-in at most `3`:**
`2 * c.multiarySize > (44199 / 10000 - ε) * n`. -/
theorem eventually_44199_lt_two_mul_multiarySize_nondeterministic
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 3 → c.NondeterministicDecides I Acc (S n) →
        (44199 / 10000 - ε) * n < 2 * c.multiarySize :=
  eventually_lt_nondet_multiary_of_le_coeff cert_r3_slepian (by norm_num)
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Strongest unconditional nondeterministic `innerSize` lower bound for fan-in at most `3`:**
`2 * c.innerSize > (44199 / 10000 - ε) * n`. -/
theorem eventually_44199_lt_two_mul_innerSize_nondeterministic
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 3 → c.NondeterministicDecides I Acc (S n) →
        (44199 / 10000 - ε) * n < 2 * c.innerSize :=
  eventually_lt_nondet_inner_of_le_coeff cert_r3_slepian (by norm_num)
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Strongest unconditional average-case bound for fan-in at most `3` (`44199 / 10000`).** -/
theorem eventually_agreement_le_44199_two_mul_multiarySize {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 3 → 2 * (c.multiarySize : ℝ) ≤ (44199 / 10000 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) :=
  eventually_agreement_multiary_of_le_coeff cert_r3_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hε

/-- Average-case `innerSize` bound (`44199 / 10000`) for fan-in at most `3`. -/
theorem eventually_agreement_le_44199_two_mul_innerSize {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 3 → 2 * (c.innerSize : ℝ) ≤ (44199 / 10000 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_innerSize_of_cert.{u, v} cert_r3_slepian hε
  refine ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => ?_⟩
  have hL : (44199 / 10000 : ℝ) ≤
      (hyperCoeff 3 (17970677 / 100000000) (-18502061 / 100000000) : ℝ) := by
    norm_num [hyperCoeff]
  filter_upwards [H U S K b_bias hbias hK] with n hn σ I Acc c hfan hs
  rw [show (2 : ℝ) = (3 : ℝ) - 1 by norm_num] at hs
  exact hn σ I Acc c hfan
    (hs.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n)))

/-! #### Fan-in `r = 4` (Sheppard + star-cone: `4.4792n`) -/

/-- **Unconditional worst-case lower bound for fan-in at most `4`:**
`3 * c.multiarySize > (44792 / 10000 - ε) * n`. -/
theorem eventually_44792_lt_three_mul_multiarySize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (44792 / 10000 - ε) * n < 3 * c.multiarySize :=
  eventually_lt_multiary_of_le_coeff cert_r4_sheppard
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional `innerSize` lower bound for fan-in at most `4`:**
`3 * c.innerSize > (44792 / 10000 - ε) * n`. -/
theorem eventually_44792_lt_three_mul_innerSize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (44792 / 10000 - ε) * n < 3 * c.innerSize :=
  eventually_lt_inner_of_le_coeff cert_r4_sheppard
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional nondeterministic lower bound for fan-in at most `4`:**
`3 * c.multiarySize > (44792 / 10000 - ε) * n`. -/
theorem eventually_44792_lt_three_mul_multiarySize_nondeterministic
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 4 → c.NondeterministicDecides I Acc (S n) →
        (44792 / 10000 - ε) * n < 3 * c.multiarySize :=
  eventually_lt_nondet_multiary_of_le_coeff cert_r4_sheppard (by norm_num)
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional nondeterministic `innerSize` lower bound for fan-in at most `4`:**
`3 * c.innerSize > (44792 / 10000 - ε) * n`. -/
theorem eventually_44792_lt_three_mul_innerSize_nondeterministic
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 4 → c.NondeterministicDecides I Acc (S n) →
        (44792 / 10000 - ε) * n < 3 * c.innerSize :=
  eventually_lt_nondet_inner_of_le_coeff cert_r4_sheppard (by norm_num)
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional average-case bound for fan-in at most `4` (`44792 / 10000`).** -/
theorem eventually_agreement_le_44792_three_mul_multiarySize {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 4 → 3 * (c.multiarySize : ℝ) ≤ (44792 / 10000 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) :=
  eventually_agreement_multiary_of_le_coeff cert_r4_sheppard
    (by norm_num [hyperCoeff]) (by norm_num) hε

/-! #### Fan-in `r = 8` (Slepian + star-cone: `4.6666n`) -/

/-- **Unconditional worst-case lower bound for fan-in at most `8`:**
`7 * c.multiarySize > (46666 / 10000 - ε) * n`. -/
theorem eventually_46666_lt_seven_mul_multiarySize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 8 → c.Decides I Acc (S n) →
        (46666 / 10000 - ε) * n < 7 * c.multiarySize :=
  eventually_lt_multiary_of_le_coeff cert_r8_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional `innerSize` lower bound for fan-in at most `8`:**
`7 * c.innerSize > (46666 / 10000 - ε) * n`. -/
theorem eventually_46666_lt_seven_mul_innerSize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 8 → c.Decides I Acc (S n) →
        (46666 / 10000 - ε) * n < 7 * c.innerSize :=
  eventually_lt_inner_of_le_coeff cert_r8_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional nondeterministic lower bound for fan-in at most `8` (`b = 0`):**
`7 * c.multiarySize > (46666 / 10000 - ε) * n`. -/
theorem eventually_46666_lt_seven_mul_multiarySize_nondeterministic
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 8 → c.NondeterministicDecides I Acc (S n) →
        (46666 / 10000 - ε) * n < 7 * c.multiarySize :=
  eventually_lt_nondet_multiary_of_le_coeff cert_r8_slepian le_rfl
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional nondeterministic `innerSize` lower bound for fan-in at most `8`:**
`7 * c.innerSize > (46666 / 10000 - ε) * n`. -/
theorem eventually_46666_lt_seven_mul_innerSize_nondeterministic
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 8 → c.NondeterministicDecides I Acc (S n) →
        (46666 / 10000 - ε) * n < 7 * c.innerSize :=
  eventually_lt_nondet_inner_of_le_coeff cert_r8_slepian le_rfl
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional average-case bound for fan-in at most `8` (`46666 / 10000`).** -/
theorem eventually_agreement_le_46666_seven_mul_multiarySize {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 8 → 7 * (c.multiarySize : ℝ) ≤ (46666 / 10000 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) :=
  eventually_agreement_multiary_of_le_coeff cert_r8_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hε

/-! #### Fan-in `r = 16` (Slepian + star-cone: `4.9798n`) -/

/-- **Unconditional worst-case lower bound for fan-in at most `16`:**
`15 * c.multiarySize > (49798 / 10000 - ε) * n`. -/
theorem eventually_49798_lt_fifteen_mul_multiarySize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 16 → c.Decides I Acc (S n) →
        (49798 / 10000 - ε) * n < 15 * c.multiarySize :=
  eventually_lt_multiary_of_le_coeff cert_r16_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional `innerSize` lower bound for fan-in at most `16`:**
`15 * c.innerSize > (49798 / 10000 - ε) * n`. -/
theorem eventually_49798_lt_fifteen_mul_innerSize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 16 → c.Decides I Acc (S n) →
        (49798 / 10000 - ε) * n < 15 * c.innerSize :=
  eventually_lt_inner_of_le_coeff cert_r16_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional average-case bound for fan-in at most `16` (`49798 / 10000`).** -/
theorem eventually_agreement_le_49798_fifteen_mul_multiarySize {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 16 →
          15 * (c.multiarySize : ℝ) ≤ (49798 / 10000 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) :=
  eventually_agreement_multiary_of_le_coeff cert_r16_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hε

/-! #### Fan-in `r = 64` (Slepian: `6.0012n`) -/

/-- **Unconditional worst-case lower bound for fan-in at most `64`:**
`63 * c.multiarySize > (60012 / 10000 - ε) * n` (breaking `6n`!). -/
theorem eventually_60012_lt_sixtyThree_mul_multiarySize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 64 → c.Decides I Acc (S n) →
        (60012 / 10000 - ε) * n < 63 * c.multiarySize :=
  eventually_lt_multiary_of_le_coeff cert_r64_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional `innerSize` lower bound for fan-in at most `64`:**
`63 * c.innerSize > (60012 / 10000 - ε) * n`. -/
theorem eventually_60012_lt_sixtyThree_mul_innerSize (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 64 → c.Decides I Acc (S n) →
        (60012 / 10000 - ε) * n < 63 * c.innerSize :=
  eventually_lt_inner_of_le_coeff cert_r64_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hSK hε

/-- **Unconditional average-case bound for fan-in at most `64` (`60012 / 10000`).** -/
theorem eventually_agreement_le_60012_sixtyThree_mul_multiarySize {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b_bias : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b_bias n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 64 →
          63 * (c.multiarySize : ℝ) ≤ (60012 / 10000 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias n + Real.exp (-(γ * n)) :=
  eventually_agreement_multiary_of_le_coeff cert_r64_slepian
    (by norm_num [hyperCoeff]) (by norm_num) hε

end ConcreteBounds

end Cslib.Circuits.Frontier.Hypergraph
