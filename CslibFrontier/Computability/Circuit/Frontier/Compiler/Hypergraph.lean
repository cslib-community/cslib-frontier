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

/-- The rescaled error `(3 r + 2) / (1 - c_n) + M_K L` charged for a `log_q K` budget `L`. -/
private noncomputable def errTerm (r : ℕ) (a b : ℚ) (L : ℝ) : ℝ :=
  (3 * (r : ℝ) + 2) / (1 - max (b : ℝ) (-a)) +
    max (3 / (1 - max (b : ℝ) (-a)))
      ((|max (b : ℝ) (-a)| / (1 - max (b : ℝ) (-a))) / supplyRate r a b) * L

/-- The coefficient `κ` of `log (v + 1)` in the rescaled demand. -/
private noncomputable def kappa (c : ℝ) : ℝ := max 1 ((4 + 1 / Real.log 2) / (1 - c))

private theorem supplyRate_pos_and_inv {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b) :
    0 < supplyRate r a b ∧ 1 / supplyRate r a b = (hyperCoeff r a b : ℝ) ∧
      0 < (((r + 1 : ℕ) : ℝ) * a + b) ∧ 0 < 1 - max (b : ℝ) (-a) := by
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  have hc_s : 0 < (((r + 1 : ℕ) : ℝ) * a + b) := by exact_mod_cast hcert.hdenom
  have hc_n : max (b : ℝ) (-a) < 1 := by exact_mod_cast hcert.hnum
  refine ⟨div_pos hc_s (mul_pos (by linarith) (sub_pos.mpr hc_n)), ?_, hc_s, sub_pos.mpr hc_n⟩
  unfold supplyRate hyperCoeff
  rw [one_div_div]
  push_cast; ring

/-- The error term is nonnegative and dominates both the input-supply loss
`|c_n| / (1 - c_n) * L` and the constant demand terms `3 r + 2 + 3 L`. -/
private theorem errTerm_bounds {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b) {L : ℝ}
    (hL : 0 ≤ L) :
    0 ≤ errTerm r a b L ∧
      |max (b : ℝ) (-a)| / (1 - max (b : ℝ) (-a)) * L ≤ supplyRate r a b * errTerm r a b L ∧
      3 * (r : ℝ) + 2 + 3 * L ≤ (1 - max (b : ℝ) (-a)) * errTerm r a b L := by
  obtain ⟨hA, -, -, h1c⟩ := supplyRate_pos_and_inv hcert
  unfold errTerm
  set c := max (b : ℝ) (-a)
  set M := max (3 / (1 - c)) (|c| / (1 - c) / supplyRate r a b)
  have h3 : 3 ≤ (1 - c) * M := (div_le_iff₀' h1c).mp (le_max_left _ _)
  have hc : |c| / (1 - c) ≤ supplyRate r a b * M := (div_le_iff₀' hA).mp (le_max_right _ _)
  have hM : 0 ≤ M := (div_nonneg (by norm_num) h1c.le).trans (le_max_left _ _)
  have hr : 0 ≤ (3 * (r : ℝ) + 2) / (1 - c) := div_nonneg (by positivity) h1c.le
  have hrc : (1 - c) * ((3 * (r : ℝ) + 2) / (1 - c)) = 3 * r + 2 := mul_div_cancel₀ _ h1c.ne'
  refine ⟨add_nonneg hr (mul_nonneg hM hL), ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_right hc hL, mul_nonneg hA.le hr]
  · linarith [mul_le_mul_of_nonneg_right h3 hL]

private theorem isLittleO_errTerm (r : ℕ) (a b : ℚ) {f : ℕ → ℝ}
    (hf : f =o[atTop] fun n => (n : ℝ)) :
    (fun n => errTerm r a b (f n)) =o[atTop] fun n => (n : ℝ) :=
  (isLittleO_const_id_atTop _).natCast_atTop.add (hf.const_mul_left _)

private theorem logb_le_kappa_mul_log {c q v : ℝ} (hc : 0 < 1 - c) (hq : 2 ≤ q) (hv : 0 ≤ v) :
    Real.logb q (v + 1) ≤ (1 - c) * (kappa c * Real.log (v + 1)) := by
  have h : 4 + 1 / Real.log 2 ≤ (1 - c) * kappa c := (div_le_iff₀' hc).mp (le_max_right _ _)
  rw [← mul_assoc]
  exact (logb_le_mul_log hq (by linarith)).trans
    (mul_le_mul_of_nonneg_right h (Real.log_nonneg (by linarith)))

/-- A graph with at most `g + 1` vertices fits the budget `κ (n + s + 1)` for `s = m g + n`. -/
private theorem le_kappa_mul {c m g v n : ℝ} (hm : 1 ≤ m) (hg : 0 ≤ g) (hn : 0 ≤ n)
    (hv : v ≤ g + 1) : v ≤ kappa c * (n + (m * g + n) + 1) := by
  have hκ : 1 ≤ kappa c := le_max_left _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hκ) (by positivity : 0 ≤ n + (m * g + n) + 1),
    mul_nonneg (sub_nonneg.mpr hm) hg]

private theorem natCast_le_logb_of_pow_lt {q u K : ℕ} (hq : 1 < q) (h : q ^ u < K) :
    (u : ℝ) ≤ Real.logb q K := by
  rw [Real.le_logb_iff_rpow_le (by exact_mod_cast hq)
    (by exact_mod_cast (Nat.zero_le _).trans_lt h), Real.rpow_natCast]
  exact_mod_cast h.le

/-- Deterministic input-count bound: when the unread inputs carry fewer than `K` assignments,
`c_n * |LiveInput c| ≤ c_n * n + |c_n| * log_q K` regardless of the sign of `c_n`. -/
private theorem input_supply_le_of_unread_lt {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n K : ℕ} (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Set U)
    (lay : Layout (HyperNode c)) (c_n : ℝ)
    (hu : Nat.card U ^ (hyperNetwork c I Acc lay).readᶜ.ncard < K) :
    c_n * (Fintype.card (LiveInput c) : ℝ) ≤ c_n * n + |c_n| * Real.logb (Nat.card U) K := by
  set u := (hyperNetwork c I Acc lay).readᶜ.ncard
  have hsum : (hyperNetwork c I Acc lay).read.ncard + u = Nat.card (Fin n) :=
    ncard_add_ncard_compl _
  rw [read_hyperNetwork, ncard_coe_finset, ← Fintype.card_coe, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hsum
  have hsumR : (Fintype.card (LiveInput c) : ℝ) + u = n := by exact_mod_cast hsum
  have hR : c_n * (Fintype.card (LiveInput c) : ℝ) = c_n * n - c_n * u := by rw [← hsumR]; ring
  linarith [mul_nonneg (neg_le_iff_add_nonneg.mp (neg_abs_le c_n)) (Nat.cast_nonneg (α := ℝ) u),
    mul_le_mul_of_nonneg_left (natCast_le_logb_of_pow_lt Finite.one_lt_card hu) (abs_nonneg c_n)]

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
  refine exists_congr fun y => Eq.to_iff <| congrArg (c.eval I · 0 ∈ Acc) ?_
  rw [← Fin.append_comp_sumElim, Function.comp_assoc]
  exact congrArg (Fin.append x y ∘ ·) finSumFinEquiv.self_comp_symm


/-- Nondeterministic input-count bound when `c_n ≤ 0`: hiding the `k` witness inputs can only
decrease the number of read inputs below `|LiveInput c|`, so `n - log_q K ≤ |LiveInput c|`
multiplied by `c_n ≤ 0` yields `c_n * |LiveInput c| ≤ c_n * n + |c_n| * log_q K`. -/
private theorem input_supply_le_of_hidden_unread_lt {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n k K : ℕ} (c : Circuit σ (n + k) 1) (I : Interpretation σ U)
    (Acc : Set U) (lay : Layout (HyperNode c)) {c_n : ℝ} (hc_n : c_n ≤ 0)
    (hu : Nat.card U ^ (hiddenHyperNetwork c I Acc lay).readᶜ.ncard < K) :
    c_n * (Fintype.card (LiveInput c) : ℝ) ≤ c_n * n + |c_n| * Real.logb (Nat.card U) K := by
  set H := hiddenHyperNetwork c I Acc lay
  have hsum := ncard_add_ncard_compl H.read
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  have hread_le : H.read.ncard ≤ Fintype.card (LiveInput c) := by
    have h1 := (Network.ncard_read_hide_le
      ((hyperNetwork c I Acc lay).reindex finSumFinEquiv.symm)).trans
      (Network.ncard_read_reindex (hyperNetwork c I Acc lay) finSumFinEquiv.symm).le
    rwa [read_hyperNetwork, ncard_coe_finset, ← Fintype.card_coe] at h1
  have hinp : (n : ℝ) - H.readᶜ.ncard ≤ Fintype.card (LiveInput c) :=
    sub_le_iff_le_add.mpr (mod_cast show n ≤ Fintype.card (LiveInput c) + H.readᶜ.ncard by omega)
  rw [abs_of_nonpos hc_n]
  linarith [mul_le_mul_of_nonpos_left hinp hc_n,
    mul_le_mul_of_nonpos_left (natCast_le_logb_of_pow_lt Finite.one_lt_card hu) hc_n]

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
  obtain ⟨hA, -, hc_s, h1c⟩ := supplyRate_pos_and_inv hcert
  have hr1 : (0 : ℝ) < r - 1 := by linarith [(Nat.ofNat_le_cast.mpr hcert.hr : (2 : ℝ) ≤ r)]
  dsimp only
  set c_n := max (b : ℝ) (-a) with hc
  have hgate : supplyRate r a b * (1 - c_n) * (((r : ℝ) - 1) * g) =
      (((r + 1 : ℕ) : ℝ) * a + b) * g := by
    rw [supplyRate, ← hc]
    field_simp
  have hl : (((r + 1 : ℕ) : ℝ) * a + b) * l ≤ (((r + 1 : ℕ) : ℝ) * a + b) * g := by gcongr
  have hlog : |c_n| * logK ≤ (1 - c_n) * (supplyRate r a b * e_val) :=
    calc |c_n| * logK = (1 - c_n) * (|c_n| / (1 - c_n) * logK) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left he_in h1c.le
  have hC : C / (1 - c_n) * (1 - c_n) = C := div_mul_cancel₀ C h1c.ne'
  rw [div_le_iff₀ h1c]
  linarith [mul_nonneg (mul_nonneg h1c.le hη.le)
    (add_nonneg (mul_nonneg hr1.le (Nat.cast_nonneg (α := ℝ) g)) he_nn)]

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
        (w : ℝ) + ((2 * (r + 1) : ℕ) : ℝ) + r + 3 * Real.logb (Nat.card U) (K n) +
          Real.logb (Nat.card U) ((v : ℝ) + 1) →
      ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * g := by
  obtain ⟨hA, hA_inv, -, h1c_n⟩ := supplyRate_pos_and_inv hcert
  set c_n := max (b : ℝ) (-a)
  set q := Nat.card U
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card (α := U))
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  set e : ℕ → ℝ := fun n =>
    ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) + errTerm r a b (Real.logb q (K n))
  have he : e =o[atTop] fun n => (n : ℝ) :=
    (((isLittleO_sub_logb_ncard hSK.isLittleO_deficit).const_mul_left (1 / (1 - c_n))).congr_left
      fun n => by ring).add (isLittleO_errTerm r a b
        ((hSK.isLittleO_log.const_mul_left (1 / Real.log q)).congr_left fun n => by
          simp only [Real.logb]; ring))
  obtain ⟨η₀, hη₀, H⟩ :=
    eventually_lt_of_demand hA (zero_le_one.trans (le_max_left _ _) : 0 ≤ kappa c_n) hε
  refine ⟨η₀ * (1 - c_n), mul_pos hη₀ h1c_n, fun C => ?_⟩
  filter_upwards [H η₀ hη₀ le_rfl (C / (1 - c_n)) e he, hSK.eventually_rectangleFree,
    eventually_card_mul_sq_le_ncard hSK] with n hn hfreen hbign
  intro g l inp v w hlg hvg hw hinp hdemand
  have hSne : (S n).Nonempty := (ncard_pos (toFinite _)).mp
    ((Nat.mul_pos Nat.card_pos (pow_pos hfreen.pos 2)).trans_le hbign)
  have hX : 0 ≤ ((n : ℝ) - Real.logb q (S n).ncard) / (1 - c_n) :=
    div_nonneg (by linarith [logb_ncard_le_self hSne]) h1c_n.le
  obtain ⟨hE_nn, hE_in, hE_ge⟩ :=
    errTerm_bounds hcert (Real.logb_nonneg (b := q) (x := K n) hq1 (Nat.one_le_cast.mpr hfreen.pos))
  have hsupply := rescaled_hyperSupply_le hcert hη₀ C n v w hlg (add_nonneg hX hE_nn)
    (hE_in.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hX) hA.le))
    (by linarith [hw, hinp])
  have hdem : (n : ℝ) ≤ ((w : ℝ) - c_n * n) / (1 - c_n) + e n + kappa c_n * Real.log (v + 1) := by
    refine le_of_mul_le_mul_left ?_ h1c_n
    have hW := mul_div_cancel₀ ((w : ℝ) - c_n * n) h1c_n.ne'
    have hX' := mul_div_cancel₀ ((n : ℝ) - Real.logb q (S n).ncard) h1c_n.ne'
    push_cast at hdemand
    linarith [logb_le_kappa_mul_log h1c_n hq2 (Nat.cast_nonneg (α := ℝ) v)]
  have hres := hn _ v _ (add_nonneg (mul_nonneg (by linarith) g.cast_nonneg) n.cast_nonneg)
    v.cast_nonneg (le_kappa_mul (by linarith) g.cast_nonneg n.cast_nonneg (by exact_mod_cast hvg))
    hdem hsupply
  rw [hA_inv] at hres; linarith

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
    n hn hfreen hbign σ I Acc c hfan hS
  obtain ⟨lay, hlay⟩ := hC c hfan
  set N := hyperNetwork c I Acc lay
  have hacc : N.accepted = S n :=
    Set.ext fun x => by simpa only [N, accepted_hyperNetwork, mem_ofPred_eq] using (hS x).symm
  rw [← hacc] at hfreen hbign
  have hmr : max r 1 = r := max_eq_left (by have := hcert.hr; omega)
  have hdem := N.logb_ncard_accepted_le hfreen hbign lay (w := hyperWidth c lay)
    (d := 2 * (r + 1)) (m := r) (width_hyperNetwork c I Acc lay).le
    (maxDegreeLE_hyperNetwork hfan I Acc lay)
    (fun u => hmr ▸ ncard_readAt_hyperNetwork_le hfan I Acc lay u)
  rw [hacc] at hdem
  exact hn c.multiarySize (Fintype.card (LiveGate c)) (Fintype.card (LiveInput c))
    (Nat.card (HyperNode c)) (hyperWidth c lay) (card_liveGate_le_multiarySize c)
    (card_hyperNode_le c) hlay (input_supply_le_of_unread_lt c I Acc lay _
      (hfreen.pow_ncard_compl_lt N.dependsOn_read hbign)) hdem

/-- **Worst-case hypergraph frontier lower bound (`innerSize`).** -/
theorem eventually_lt_mul_innerSize_of_cert {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * c.innerSize :=
  (eventually_lt_mul_multiarySize_of_cert.{u, v} hcert hSK hε).mono fun _ hn σ I Acc c hfan hS =>
    (hn σ I Acc c hfan hS).trans_le (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr c.multiarySize_le_innerSize)
      (sub_nonneg.mpr (Nat.one_le_cast.mpr (Nat.one_le_of_lt hcert.hr))))

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
    n hn hfreen hbign k σ I Acc c hfan hS
  obtain ⟨lay, hlay⟩ := hC c hfan
  set N := hiddenHyperNetwork c I Acc lay
  have hacc : N.accepted = S n :=
    Set.ext fun x => by
      simpa only [N, accepted_hiddenHyperNetwork, mem_ofPred_eq] using (hS x).symm
  rw [← hacc] at hfreen hbign
  have hmr : max r 1 = r := max_eq_left (by have := hcert.hr; omega)
  have hreadAt (u : HyperNode c) : (N.readAt u).ncard ≤ r :=
    (Network.ncard_readAt_hide_le _ u).trans
      ((Network.ncard_readAt_reindex _ _ u).trans_le
        (hmr ▸ ncard_readAt_hyperNetwork_le hfan I Acc lay u))
  have hdem := N.logb_ncard_accepted_le hfreen hbign lay (w := hyperWidth c lay)
    (d := 2 * (r + 1)) (m := r) (width_hyperNetwork c I Acc lay).le
    (maxDegreeLE_hyperNetwork hfan I Acc lay) hreadAt
  rw [hacc] at hdem
  exact hn c.multiarySize (Fintype.card (LiveGate c)) (Fintype.card (LiveInput c))
    (Nat.card (HyperNode c)) (hyperWidth c lay) (card_liveGate_le_multiarySize c)
    (card_hyperNode_le c) hlay (input_supply_le_of_hidden_unread_lt c I Acc lay hc_n_le
      (hfreen.pow_ncard_compl_lt N.dependsOn_read hbign)) hdem

/-- **Nondeterministic hypergraph frontier lower bound (`innerSize`).** -/
theorem eventually_lt_mul_innerSize_of_nondeterministicDecides_of_cert
    {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    {r K₀ : ℕ} {a b : ℚ} (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        ((hyperCoeff r a b : ℝ) - ε) * n < ((r : ℝ) - 1) * c.innerSize :=
  (eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert.{u, v} hcert hb hSK hε).mono
    fun _ hn k σ I Acc c hfan hS => (hn k σ I Acc c hfan hS).trans_le
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr (Nat.one_le_of_lt hcert.hr))))

/-- Agreement bound from a residual `R` bounding the bias of every accepting set. -/
private theorem agreement_le_of_forall_bias {U : Type u} [Finite U] [Nonempty U] {n : ℕ}
    {S : Set (Fin n → U)} {f : (Fin n → U) → U} {β R : ℝ}
    (h : ∀ A : Set U, |signedCount S {x | f x ∈ A}| ≤ 2 * β * {x | f x ∈ A}.ncard + R)
    (Acc : Set U) : agreement S {x | f x ∈ Acc} ≤ 1 / 2 + β + R / (Nat.card U : ℝ) ^ n := by
  have h' := agreement_le (h Acc) (h Accᶜ)
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, Nat.cast_pow] at h'
  have hq : (0 : ℝ) < (Nat.card U : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr Nat.card_pos) n
  exact h'.trans_eq (by field_simp; ring)

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
    have hw_eq : w + 2 * (r + 1) + r = w + (3 * r + 2) := by omega
    rwa [accepted_hyperNetwork, read_hyperNetwork, ← read_hyperNetwork (Acc := Acc), hw_eq] at h
  have hres : (K - 1) ^ 2 * (V * q ^ (w + (3 * r + 2)) +
      q ^ (hyperNetwork c I Acc lay).readᶜ.ncard) ≤ K ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) := by
    have hq1 : 1 ≤ q ^ (w + (3 * r + 2)) := Nat.one_le_pow _ _ Nat.card_pos
    calc _ ≤ K ^ 2 * (V * K * q ^ (w + (3 * r + 2)) + K * q ^ (w + (3 * r + 2))) := by
          gcongr
          · omega
          · exact Nat.le_mul_of_pos_right _ (lt_of_le_of_lt (Nat.zero_le _) hu)
          · exact hu.le.trans (Nat.le_mul_of_pos_right _ hq1)
      _ = K ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) := by ring
  refine (agreement_le_of_forall_bias bound Acc).trans
    (add_le_add le_rfl
      (div_le_div_of_nonneg_right ?_ (pow_pos (Nat.cast_pos.mpr Nat.card_pos) n).le))
  exact_mod_cast hres

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
    (hn : ∀ s v w : ℝ, 0 ≤ s → 0 ≤ v → v ≤ kappa (max (b : ℝ) (-a)) * (n + s + 1) →
      s ≤ (1 + 1 / supplyRate r a b - ε) * n →
      w ≤ (supplyRate r a b + η) * (s - n + errTerm r a b (Real.logb (Nat.card U) K')) +
        η * v + C / (1 - max (b : ℝ) (-a)) →
      w + errTerm r a b (Real.logb (Nat.card U) K') +
        kappa (max (b : ℝ) (-a)) * Real.log (v + 1) < (1 - supplyRate r a b * ε / 2) * n) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b_bias + Real.exp (-(γ * n)) := by
  obtain ⟨hA, hA_inv, _, h1c_n⟩ := supplyRate_pos_and_inv hcert
  have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hcert.hr
  set c_n := max (b : ℝ) (-a)
  set q := Nat.card U
  have hq1 : (1 : ℝ) < q := mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := mod_cast (Finite.one_lt_card (α := U))
  have hq0 : 0 < q := Nat.card_pos
  have hK_pos : (0 : ℝ) < K' := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hK'2)
  obtain ⟨he_nn, he_in, he_ge⟩ := errTerm_bounds hcert
    (Real.logb_nonneg hq1 (Nat.one_le_cast.mpr (Nat.one_le_of_lt hK'2)))
  set V := Nat.card (HyperNode c)
  set w := hyperWidth c lay
  have hsupply := rescaled_hyperSupply_le hcert hη C n V w (card_liveGate_le_multiarySize c)
    he_nn he_in (by linarith [hlay, input_supply_le_of_unread_lt c I Acc lay c_n hu])
  have hmargin := hn _ V _ (add_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    n.cast_nonneg) V.cast_nonneg (le_kappa_mul (by linarith) (Nat.cast_nonneg _) n.cast_nonneg
      (by exact_mod_cast card_hyperNode_le c)) (by rw [hA_inv]; linarith) hsupply
  have hlogR : Real.logb q ((K' ^ 3 * (V + 1) * q ^ (w + (3 * r + 2)) : ℕ) : ℝ) ≤
      (1 - γ / Real.log 2) * n := by
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one hq1]
    push_cast
    have hW := mul_div_cancel₀ ((w : ℝ) - c_n * n) h1c_n.ne'
    linarith [mul_lt_mul_of_pos_left hmargin h1c_n, mul_le_mul_of_nonneg_right hγ_le n.cast_nonneg,
      logb_le_kappa_mul_log h1c_n hq2 (Nat.cast_nonneg (α := ℝ) V)]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp := div_pow_le_exp hq2 (by positivity) (div_nonneg hγ.le hl2.le) hlogR
  rw [div_mul_cancel₀ _ hl2.ne'] at hexp
  linarith [agreement_le_of_hyperLayout hcert.hr c hfan I Acc hS hb_nn lay hu]

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
  obtain ⟨η, hη, H⟩ :=
    eventually_add_lt_of_le hA (zero_le_one.trans (le_max_left _ _) : 0 ≤ kappa c_n) hε
  obtain ⟨C, hC⟩ := exists_layout_hyperWidth_le hcert (ξ := η * (1 - c_n)) (mul_pos hη h1c_n)
  set μ := min ((1 - c_n) * A * ε / 2) (1 / 2)
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
  set e : ℕ → ℝ := fun n => errTerm r a b (Real.logb q (K' n))
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 + 2 * Real.logb q (K' n) ≤ (1 - 1 / 2) * n := by
    filter_upwards [((isLittleO_const_id_atTop 1).natCast_atTop.add
      (hlogbK.const_mul_left 2)).bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    linarith [le_abs_self (1 + 2 * Real.logb q (K' n))]
  filter_upwards [H (C / (1 - c_n)) e (isLittleO_errTerm r a b hlogbK), hbias, hsmall] with
    n hn hbiasn hsmalln σ I Acc c hfan hsize
  obtain ⟨lay, hlay⟩ := hC c hfan
  have hK'2 : 2 ≤ K' n := le_max_right _ _
  have hS : RectangleBias (S n) (K' n) (b_bias n) := hbiasn.mono (le_max_left _ _)
  have hb_nn : 0 ≤ b_bias n := hS.nonneg <| by
    simpa [Nat.card_eq_fintype_card] using le_pow_half_of_logb hq1_nat (by omega) hsmalln
  by_cases hu : K' n ≤ q ^ (hyperNetwork c I Acc lay).readᶜ.ncard
  · have hbound (A_set : Set U) :
        |signedCount (S n) {x | c.eval I x 0 ∈ A_set}| ≤
          2 * b_bias n * {x | c.eval I x 0 ∈ A_set}.ncard + ((q * K' n ^ 2 : ℕ) : ℝ) := by
      simpa only [accepted_hyperNetwork] using hS.abs_signedCount_le_of_dependsOn hb_nn
        (hyperNetwork c I A_set lay).dependsOn_read (by omega)
        (by simpa only [read_hyperNetwork] using hu)
    have hlogR : Real.logb q ((q * K' n ^ 2 : ℕ) : ℝ) ≤ (1 - μ) * n := by
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one hq1]
      push_cast
      linarith [mul_le_mul_of_nonneg_right (min_le_right ((1 - c_n) * A * ε / 2) (1 / 2))
        n.cast_nonneg]
    have hexp := div_pow_le_exp hq2 (by positivity) hμ.le hlogR
    exact (agreement_le_of_forall_bias hbound Acc).trans (by linarith)
  · exact agreement_le_of_unread_lt_step hcert hη hγ hK'2 c hfan I Acc hS hb_nn lay hlay
      (not_le.mp hu) hsize
      ((mul_div_cancel_right₀ _ (Real.log_pos one_lt_two).ne').trans_le (min_le_left _ _)) hn

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
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_multiarySize_of_cert.{u, v} hcert hε
  exact ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => (H U S K b_bias hbias hK).mono
    fun n hn σ I Acc c hfan hs => hn σ I Acc c hfan
      ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr (Nat.one_le_of_lt hcert.hr)))).trans hs)⟩

/-! ### Monotonicity wrappers for rational certificate constants -/

private theorem lt_of_le_coeff {L H m_r ε x : ℝ} {r n : ℕ} (hL : L ≤ H)
    (hm_r : (r : ℝ) - 1 = m_r) (h : (H - ε) * n < ((r : ℝ) - 1) * x) : (L - ε) * n < m_r * x :=
  hm_r ▸ (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) n.cast_nonneg).trans_lt h

private theorem eventually_lt_multiary_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (L - ε) * n < m_r * c.multiarySize :=
  (eventually_lt_mul_multiarySize_of_cert.{u, v} hcert hSK hε).mono
    fun _ hn σ I Acc c hfan hS => lt_of_le_coeff hL hm_r (hn σ I Acc c hfan hS)

private theorem eventually_lt_inner_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (L - ε) * n < m_r * c.innerSize :=
  (eventually_lt_mul_innerSize_of_cert.{u, v} hcert hSK hε).mono
    fun _ hn σ I Acc c hfan hS => lt_of_le_coeff hL hm_r (hn σ I Acc c hfan hS)

private theorem eventually_lt_nondet_multiary_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (L - ε) * n < m_r * c.multiarySize :=
  (eventually_lt_mul_multiarySize_of_nondeterministicDecides_of_cert.{u, v} hcert hb hSK hε).mono
    fun _ hn k σ I Acc c hfan hS => lt_of_le_coeff hL hm_r (hn k σ I Acc c hfan hS)

private theorem eventually_lt_nondet_inner_of_le_coeff {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {r K₀ : ℕ} {a b : ℚ}
    (hcert : HyperDualCert r K₀ a b) (hb : b ≤ 0) {L m_r : ℝ} (hL : L ≤ (hyperCoeff r a b : ℝ))
    (hm_r : (r : ℝ) - 1 = m_r) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (L - ε) * n < m_r * c.innerSize :=
  (eventually_lt_mul_innerSize_of_nondeterministicDecides_of_cert.{u, v} hcert hb hSK hε).mono
    fun _ hn k σ I Acc c hfan hS => lt_of_le_coeff hL hm_r (hn k σ I Acc c hfan hS)

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
  exact ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => (H U S K b_bias hbias hK).mono
    fun n hn σ I Acc c hfan hs => hn σ I Acc c hfan
      ((hm_r ▸ hs).trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) n.cast_nonneg))⟩

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
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_44199_two_mul_multiarySize.{u, v} hε
  exact ⟨γ, hγ, fun U _ _ S K b_bias hbias hK => (H U S K b_bias hbias hK).mono
    fun _ hn σ I Acc c hfan hs => hn σ I Acc c hfan ((mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr c.multiarySize_le_innerSize) zero_le_two).trans hs)⟩

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
