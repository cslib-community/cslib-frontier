/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.VertexGaussian
public import CslibFrontier.Computability.Circuit.Frontier.Linear.LowerBound
public import CslibFrontier.Foundations.Probability.Gaussian.QuadrantMono
public import Mathlib.Algebra.CharZero.Infinite
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.Nat.IntermediateValue
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.SecondMoment
import CslibFrontier.Foundations.Probability.UnionBound
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Directed divergence shifts for linear-map frontier lower bounds

For a circuit computing `x ↦ M x` for a totally regular `N × N` matrix `M`, the entering directed
edge cut `inCut` of *any* vertex set `P` satisfies `|inCut P| ≥ min (N - |X(P)|) |Y(P)|`
(`Compiler.min_le_ncard_inCut`). Unlike layout width, this one-way bound needs only a *single*
oriented cut, and it survives arbitrary multigraph compressions (`Compression.quotient`) even when
contracting blocks introduces **directed cycles** in the quotient `Q`: topological wire induction
runs on the uncompressed acyclic circuit graph `Compiler.graph c`, while external entering edges
biject onto `Q.inCut` (`Compression.ncard_inCut_preimage`, `Compiler.min_le_ncard_inCut_quotient`).

In a cubic loopless quotient `Q`, every block `B` has odd total degree `deg⁺(B) + deg⁻(B) = 3`, so
its net divergence `σ(B) = deg⁺(B) - deg⁻(B) ∈ {-3, -1, 1, 3}` is never zero! Shifting vertex
thresholds by the sign of `σ(B)`,

`P_d := {B ∈ V(Q) | M_B ≤ d · sgn(σ(B))}`,

biases `∑_{B ∈ P_d} σ(B)` positively, reducing `inCut P_d = (|edgeCut P_d| - ∑_{B ∈ P_d} σ(B)) / 2`:

* **Atom-free shift theorem** (`exists_pos_shifted_inCut_ratio_lt`): when adjacent scores have no
  diagonal tie atom (`P(M_u = M_v) = 0`) and smooth symmetric crossing rate `c'(0) = 0` with
  `c(0) < 1 / 2`, the normalized backward-cut ratio `g(d) = (E[|inCut P_d|] / h) / F(-d)` falls
  strictly below `c(0)` for small `d > 0` (its smooth upper envelope has derivative
  `-f(0) (1 - 2 c(0)) < 0` at `d = 0`). Conversely, any positive tie atom splits along cross-sign
  edges for `M_u = M_v ∈ (-d, d]` (`tie_mem_edgeCut_shiftedCut`), producing a linear cusp that can
  cancel the shift gain.
* **Unconditional shifted `VertexGaussian` bound (`4.2170 N`)**: Gaussian vertex scores `Z_B` have
  zero tie mass, adjacent correlation approaching `2√2 / 3`, and satisfy bivariate quadrant
  correlation antitonicity (`measureReal_correlatedGaussian_gt_and_le_anti`). Maximizing over the
  4-type cubic degree-balance polytope (`x₃⁺, x₁⁺, x₁⁻, x₃⁻`) attains its exact global maximum
  `p_{+-} + p_{-+} / 2` on balanced `(1, 2)` / `(2, 1)` bipartite graphs. Evaluating at `d = 1 / 20`
  lifts the pure `VertexGaussian` linear-map bound from `≈ 4.0815 N` to
  **`(4217 / 1000 - ε) N = (4.217 - ε) N`**
  (`eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular`), uniformly over fields and
  for explicit Cauchy matrices over characteristic zero and prime fields `ZMod q`.

These results are original to this library. They improve the *vertex-Gaussian* linear-map bound
(`≈ 4.0815 N` to `4.217 N`) via one-way `inCut` demands and odd-parity threshold shifts, whereas
`CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional` already reaches `≈ 4.57597 N`
via undirected median-switched layouts (whose discrete tie atoms incur the linear cusp of
`tie_mem_edgeCut_shiftedCut`).

## Main results

* `Cslib.Circuits.Frontier.Multigraph.Compression.ncard_inCut_preimage`,
  `Cslib.Circuits.Frontier.Compiler.min_le_ncard_inCut_quotient`: `inCut` demand through cyclic
  quotient compressions.
* `Cslib.Circuits.Frontier.Compiler.ncard_readIn_block_le_outCut`,
  `Cslib.Circuits.Frontier.Compiler.ncard_outputs_block_le_inCut`: sharpened directed terminal caps
  `|X(B)| ≤ deg⁺(B) ≤ 3` and `|Y(B)| ≤ deg⁻(B) ≤ 3`.
* `Cslib.Circuits.Frontier.Multigraph.two_mul_ncard_inCut_add_sum_divergence`,
  `Cslib.Circuits.Frontier.Multigraph.sum_divergence`: discrete divergence identity
  `2 |inCut P| + ∑_{v ∈ P} σ(v) = |edgeCut P|` and zero total divergence `∑_v σ(v) = 0`.
* `Cslib.Circuits.Frontier.DirectedShift.exists_pos_shifted_inCut_ratio_lt`: smooth divergence shift
  theorem.
* `Cslib.Circuits.Frontier.DirectedShift.sum_measureReal_inCut_vertexScore_le`: 4-type cubic
  degree-balance LP bound on expected `inCut` under shifted `VertexGaussian` scores.
* `Cslib.Circuits.Frontier.eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular`:
  unconditional `(4.217 - ε) N` shifted `VertexGaussian` lower bound for totally regular linear
  maps (with `_finite`, `_affine`, `_isPolynomial`, `_arith_cauchyNat`, `_cauchyNat_zmod`).
-/

public section

open Set Filter Asymptotics Matrix MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Interval NNReal ENNReal

universe u v

/-! ### Part 1: Entering and leaving cuts through multigraph compressions -/

namespace Cslib.Circuits.Frontier.Multigraph

section Divergence

variable {V E : Type*} (G : Multigraph V E)

/-- The out-degree of `v`: the number of non-loop edges with source `v`. -/
@[expose] noncomputable def outDeg (v : V) : ℕ :=
  (G.outCut {v}).ncard

/-- The in-degree of `v`: the number of non-loop edges with target `v`. -/
@[expose] noncomputable def inDeg (v : V) : ℕ :=
  (G.inCut {v}).ncard

/-- The net *divergence* `σ(v) = deg⁺(v) - deg⁻(v)` of a vertex. -/
@[expose] noncomputable def divergence (v : V) : ℤ :=
  (G.outDeg v : ℤ) - (G.inDeg v : ℤ)

/-- In a loopless finite-edge multigraph, `outDeg v + inDeg v` is the incident degree of `v`. -/
theorem outDeg_add_inDeg [Finite E] (hloop : G.Loopless) (v : V) :
    G.outDeg v + G.inDeg v = (G.incidenceSet v).ncard := by
  rw [outDeg, inDeg, add_comm, ← G.ncard_edgeCut_eq_add {v}, G.edgeCut_singleton hloop v]

/-- **Odd-parity non-vanishing divergence.** In a loopless multigraph where every vertex has degree
three, `outDeg v + inDeg v = 3`, so `1 ≤ |divergence v|` (in particular `divergence v ≠ 0`). -/
theorem one_le_abs_divergence_of_cubic [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (v : V) :
    (1 : ℤ) ≤ |G.divergence v| := by
  have hdeg : G.outDeg v + G.inDeg v = 3 := (G.outDeg_add_inDeg hloop v).trans (h3 v)
  rcases le_or_gt (G.inDeg v) (G.outDeg v) with h | h
  · rw [divergence, abs_of_nonneg (by omega)]
    omega
  · rw [divergence, abs_of_neg (by omega)]
    omega

/-- `|V| ≤ ∑ v, |σ(v)|` when no divergence vanishes. -/
private theorem card_le_sum_abs_divergence [Fintype V]
    (hodd : ∀ v : V, (1 : ℤ) ≤ |G.divergence v|) :
    (Fintype.card V : ℝ) ≤ ∑ v : V, |(G.divergence v : ℝ)| := by
  simpa using Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
    (by exact_mod_cast hodd v : (1 : ℝ) ≤ |(G.divergence v : ℝ)|)

/-- **Discrete divergence identity.** In any finite loopless multigraph,
`2 |inCut P| + ∑_{v ∈ P} σ(v) = |edgeCut P|`. -/
theorem two_mul_ncard_inCut_add_sum_divergence [Fintype V] [Finite E] (hloop : G.Loopless)
    (P : Set V) [DecidablePred (· ∈ P)] :
    (2 * (G.inCut P).ncard : ℤ) + ∑ v : V, (if v ∈ P then G.divergence v else 0) =
      ((G.edgeCut P).ncard : ℤ) := by
  classical
  have := Fintype.ofFinite E
  have hcard (S : Set E) : (S.ncard : ℤ) = ∑ e : E, if e ∈ S then 1 else 0 := by
    rw [ncard_eq_toFinset_card', Finset.sum_boole]
    congr 2
    ext e
    simp
  -- Count `σ(v)` edge by edge, then swap the order of summation.
  have hdiv (v : V) : G.divergence v =
      ∑ e : E, ((if G.src e = v then 1 else 0) - if G.tgt e = v then 1 else 0) := by
    rw [divergence, outDeg, inDeg, hcard, hcard, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := hloop e
    by_cases hs : G.src e = v <;> by_cases ht : G.tgt e = v <;> simp_all [mem_outCut, mem_inCut]
  simp only [hdiv, ← Finset.sum_filter]
  rw [Finset.sum_comm, G.ncard_edgeCut_eq_add, Nat.cast_add, hcard (G.inCut P),
    hcard (G.outCut P), Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hs : G.src e ∈ P <;> by_cases ht : G.tgt e ∈ P <;>
    simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, hs, ht, mem_outCut, mem_inCut]

/-- In any finite loopless multigraph, the vertex divergences sum to zero: `∑ v, σ(v) = 0`. -/
theorem sum_divergence [Fintype V] [Finite E] (hloop : G.Loopless) :
    ∑ v : V, G.divergence v = 0 := by
  have hz := G.two_mul_ncard_inCut_add_sum_divergence hloop (univ : Set V)
  have hin0 : G.inCut (univ : Set V) = ∅ := by ext e; simp
  have hed0 : G.edgeCut (univ : Set V) = ∅ := by ext e; simp
  simp only [hin0, hed0, ncard_empty, mul_zero, CharP.cast_eq_zero, zero_add, mem_univ,
    ↓reduceIte] at hz
  exact hz

end Divergence

namespace Compression

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} (c : Compression G d)

/-- The entering cut of a union of whole blocks consists of the edges of the entering cut of the
quotient, regardless of whether the quotient contains directed cycles. -/
theorem inCut_preimage (T : Set c.blocks) :
    G.inCut (c.blockOf ⁻¹' T) = Subtype.val '' c.quotient.inCut T := by
  ext e
  constructor
  · intro h
    have h1 : c.blockOf (G.src e) ∉ T := h.1
    have h2 : c.blockOf (G.tgt e) ∈ T := h.2
    have hne : e ∈ c.external := fun heq => h1 (heq ▸ h2)
    exact ⟨⟨e, hne⟩, h, rfl⟩
  · rintro ⟨⟨e, _⟩, h, rfl⟩
    exact h

/-- **Entering cuts of unions of whole blocks** are entering cuts of the quotient. -/
theorem ncard_inCut_preimage (T : Set c.blocks) :
    (G.inCut (c.blockOf ⁻¹' T)).ncard = (c.quotient.inCut T).ncard := by
  rw [c.inCut_preimage, ncard_image_of_injective _ Subtype.val_injective]

/-- **Leaving cuts of unions of whole blocks** are leaving cuts of the quotient. -/
theorem ncard_outCut_preimage (T : Set c.blocks) :
    (G.outCut (c.blockOf ⁻¹' T)).ncard = (c.quotient.outCut T).ncard := by
  rw [← G.inCut_compl, ← c.quotient.inCut_compl]
  exact c.ncard_inCut_preimage Tᶜ

end Compression

end Cslib.Circuits.Frontier.Multigraph

/-! ### Part 2: Quotient cut demands and sharpened block terminal bounds -/

namespace Cslib.Circuits.Frontier.Compiler

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- **Entering cut demand on the compression quotient (cycles permitted).** Even when contracting
connected blocks introduces directed cycles in `cmp.quotient`, every block subset `T` satisfies
`min (N - |X(T)|) |Y(T)| ≤ |cmp.quotient.inCut T|`, because wire induction runs on the uncompressed
acyclic circuit graph `Compiler.graph c`. -/
theorem min_le_ncard_inCut_quotient {d : ℕ} (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (cmp : Multigraph.Compression (graph c) d) (T : Set cmp.blocks) :
    min (N - ((network c I fun _ => univ).readIn (cmp.blockOf ⁻¹' T)).ncard)
      {o : Fin N | Vertex.output o ∈ cmp.blockOf ⁻¹' T}.ncard ≤
      (cmp.quotient.inCut T).ncard := by
  rw [← cmp.ncard_inCut_preimage]
  exact min_le_ncard_inCut hM hc hcap (cmp.blockOf ⁻¹' T)

/-- **Leaving cut demand on the compression quotient (cycles permitted).** -/
theorem min_le_ncard_outCut_quotient {d : ℕ} (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (cmp : Multigraph.Compression (graph c) d) (T : Set cmp.blocks) :
    min ((network c I fun _ => univ).readIn (cmp.blockOf ⁻¹' T)).ncard
      (N - {o : Fin N | Vertex.output o ∈ cmp.blockOf ⁻¹' T}.ncard) ≤
      (cmp.quotient.outCut T).ncard := by
  rw [← cmp.ncard_outCut_preimage]
  exact min_le_ncard_outCut hM hc hcap (cmp.blockOf ⁻¹' T)

/-- When `d log₂ |Vertex c| < N`, every block `B` of a compression holds at most `N` inputs and
outputs combined: otherwise a proper prefix of `B` would hit `|X| + |Y| = N` with cut at most
`d log₂ |B| < N`, contradicting `min_le_ncard_edgeCut`. -/
theorem add_ncard_block_le {d : ℕ} (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (cmp : Multigraph.Compression (graph c) d)
    (hsmall : d * Nat.log 2 (Nat.card (Vertex c)) < N) (B : cmp.blocks) :
    ((network c I fun _ => univ).readIn {v | v ∈ B.1}).ncard +
      {o : Fin N | Vertex.output o ∈ B.1}.ncard ≤ N := by
  by_contra! hgt
  set Gnet := network c I fun _ => univ
  let P : ℕ → Set (Vertex c) := fun k => {v | v ∈ B.1.take k}
  let outs : Set (Vertex c) → Set (Fin N) := fun S => {o | Vertex.output o ∈ S}
  let a : ℕ → ℕ := fun k => (Gnet.readIn (P k)).ncard + (outs (P k)).ncard
  have h0 : a 0 ≤ N := by
    simp [a, P, outs]
  have htake : a B.1.length =
      (Gnet.readIn {v | v ∈ B.1}).ncard + {o : Fin N | Vertex.output o ∈ B.1}.ncard := by
    simp [a, P, outs]
  have hT : N ≤ a B.1.length := by omega
  have hstep : ∀ k < B.1.length, a (k + 1) ≤ a k + 1 := by
    intro k hk
    set w := B.1[k]
    have hsucc : P (k + 1) = insert w (P k) := by
      ext v
      simp only [P, mem_ofPred_eq, List.take_succ_eq_append_getElem hk, List.mem_append,
        List.mem_singleton, mem_insert_iff]
      exact or_comm
    have hread : Gnet.readIn (P (k + 1)) ⊆ Gnet.readIn (P k) ∪ Gnet.readAt w := by
      rw [hsucc]
      exact Gnet.readIn_insert_subset _ _
    have houts : outs (P (k + 1)) ⊆ outs (P k) ∪ {o | Vertex.output o = w} := by
      intro o ho
      dsimp only [outs] at ho
      rw [mem_ofPred_eq, hsucc, mem_insert_iff] at ho
      exact ho.symm
    have := ncard_le_ncard hread (toFinite _)
    have := ncard_le_ncard houts (toFinite _)
    have := ncard_union_le (Gnet.readIn (P k)) (Gnet.readAt w)
    have := ncard_union_le (outs (P k)) {o | Vertex.output o = w}
    have h1w : (Gnet.readAt w).ncard + {o | Vertex.output o = w}.ncard ≤ 1 :=
      ncard_readAt_add_ncard_le (I := I) w
    dsimp only [a]
    omega
  obtain ⟨k₀, hk₀_le, hk₀_eq⟩ := Nat.exists_eq_of_forall_le_add_one h0 hT hstep
  have hk₀_lt : k₀ < B.1.length := hk₀_le.lt_of_ne (by rintro rfl; omega)
  have hdem := min_le_ncard_edgeCut hM hc hcap (P k₀)
  change min (a k₀) (2 * N - a k₀) ≤ ((graph c).edgeCut {v | v ∈ B.1.take k₀}).ncard at hdem
  rw [hk₀_eq, show 2 * N - N = N by omega, min_self] at hdem
  have hsup := cmp.ncard_edgeCut_take_le B.1 B.2 k₀ hk₀_lt
  have hlen : B.1.length ≤ Nat.card (Vertex c) := by
    have := Fintype.ofFinite (Vertex c)
    rw [Nat.card_eq_fintype_card]
    exact (cmp.nodup B.1 B.2).length_le_card
  have hlog : d * Nat.log 2 B.1.length ≤ d * Nat.log 2 (Nat.card (Vertex c)) :=
    Nat.mul_le_mul_left d (Nat.log_mono_right hlen)
  omega

/-- When `0 < N` and `d log₂ |Vertex c| < N`, any compression has at least two blocks. -/
theorem one_lt_card_blocks_of_lt {d : ℕ} (hN : 0 < N) (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (cmp : Multigraph.Compression (graph c) d)
    (hsmall : d * Nat.log 2 (Nat.card (Vertex c)) < N) :
    1 < Nat.card cmp.blocks := by
  by_contra! hle
  let B₀ := cmp.blockOf (.output ⟨0, hN⟩)
  have hall : {v : Vertex c | v ∈ B₀.1} = univ := by
    ext v
    simp only [mem_ofPred_eq, mem_univ, iff_true, cmp.mem_iff_blockOf_eq]
    have hsub : Subsingleton cmp.blocks := Finite.card_le_one_iff_subsingleton.mp hle
    exact Subsingleton.elim _ _
  have hsum := add_ncard_block_le hM hc hcap cmp hsmall B₀
  have hread : (network c I fun _ => univ).readIn {v | v ∈ B₀.1} = univ := by
    rw [hall]
    exact read_eq_univ_of_isTotallyRegular hM hc _
  have houts : {o : Fin N | Vertex.output o ∈ B₀.1} = univ := by
    ext o
    have : Vertex.output o ∈ ({v : Vertex c | v ∈ B₀.1} : Set (Vertex c)) := by simp [hall]
    simpa using this
  rw [hread, houts, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  omega

/-- **Sharpened input cap per block (`|X(B)| ≤ deg⁺_Q(B)`).** In particular, sink blocks
(`deg⁺ = 0`) read zero inputs, and in budget `3` every block reads at most `3` inputs. -/
theorem ncard_readIn_block_le_outCut {d : ℕ} (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (cmp : Multigraph.Compression (graph c) d)
    (hsmall : d * Nat.log 2 (Nat.card (Vertex c)) < N) (B : cmp.blocks) :
    ((network c I fun _ => univ).readIn {v | v ∈ B.1}).ncard ≤
      (cmp.quotient.outCut {B}).ncard := by
  have hpre : cmp.blockOf ⁻¹' ({B} : Set cmp.blocks) = {v | v ∈ B.1} := by
    ext v
    simp [cmp.mem_iff_blockOf_eq]
  have hout := min_le_ncard_outCut_quotient hM hc hcap cmp {B}
  rw [hpre] at hout
  change min ((network c I fun _ => univ).readIn {v | v ∈ B.1}).ncard
    (N - {o : Fin N | Vertex.output o ∈ B.1}.ncard) ≤ _ at hout
  have hsum := add_ncard_block_le hM hc hcap cmp hsmall B
  omega

/-- **Sharpened output cap per block (`|Y(B)| ≤ deg⁻_Q(B)`).** In particular, source blocks
(`deg⁻ = 0`) hold zero outputs, and in budget `3` every block holds at most `3` outputs. -/
theorem ncard_outputs_block_le_inCut {d : ℕ} (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I)
    (cmp : Multigraph.Compression (graph c) d)
    (hsmall : d * Nat.log 2 (Nat.card (Vertex c)) < N) (B : cmp.blocks) :
    {o : Fin N | Vertex.output o ∈ B.1}.ncard ≤ (cmp.quotient.inCut {B}).ncard := by
  have hpre : cmp.blockOf ⁻¹' ({B} : Set cmp.blocks) = {v | v ∈ B.1} := by
    ext v
    simp [cmp.mem_iff_blockOf_eq]
  have hin := min_le_ncard_inCut_quotient hM hc hcap cmp {B}
  rw [hpre] at hin
  change min (N - ((network c I fun _ => univ).readIn {v | v ∈ B.1}).ncard)
    {o : Fin N | Vertex.output o ∈ B.1}.ncard ≤ _ at hin
  have hsum := add_ncard_block_le hM hc hcap cmp hsmall B
  omega

/-- **Explicit threshold `28 ≤ N` for `3 log₂ (23 N) < N`** (the exact `s ≤ 5 N` vertex bound). -/
private theorem three_mul_log_twenty_three_mul_lt {N : ℕ} (hN : 28 ≤ N) :
    3 * Nat.log 2 (23 * N) < N := by
  suffices hpow : ∀ m, 28 ≤ m → 23 * m < 2 ^ ((m - 1) / 3 + 1) by
    have hlt := (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr (hpow N hN)
    omega
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases le_or_gt m 30 with hm30 | hm30
    · interval_cases m <;> norm_num
    · have hprev := ih (m - 3) (by omega) (by omega)
      have hexp : (m - 1) / 3 + 1 = ((m - 3 - 1) / 3 + 1) + 1 := by omega
      rw [hexp, pow_succ]
      omega

/-- For fan-in-two circuits with `c.innerSize ≤ 5 * N` and `28 ≤ N`,
`3 * log₂ |Vertex c| < N`. -/
private theorem three_mul_log_card_vertex_lt (hfan : c.FanInAtMost 2) (hs : c.innerSize ≤ 5 * N)
    (hN : 28 ≤ N) : 3 * Nat.log 2 (Nat.card (Vertex c)) < N := by
  have hV : Nat.card (Vertex c) ≤ 23 * N := (card_vertex_le hfan).trans (by omega)
  exact (Nat.mul_le_mul_left 3 (Nat.log_mono_right hV)).trans_lt
    (three_mul_log_twenty_three_mul_lt hN)

end Cslib.Circuits.Frontier.Compiler

/-! ### Part 3: Atom-free divergence shift theorem and tie-cusp obstruction -/

namespace Cslib.Circuits.Frontier.DirectedShift

open _root_.Cslib.Circuits.Frontier.Multigraph

/-- The divergence-shifted vertex cut `{v | M v ≤ d · sgn(σ(v))}` (using `+d` on `0 < σ(v)` and
`-d` otherwise). -/
@[expose] def shiftedCut {V E : Type*} (G : Multigraph V E) (M : V → ℝ) (d : ℝ) : Set V :=
  {v | M v ≤ if 0 < G.divergence v then d else -d}

/-- **Diagonal tie-atom cusp obstruction.** On any edge `e` from `V_+` (`0 < σ(src e)`) to `V_-`
(`¬ 0 < σ(tgt e)`), a shared tie `M (src e) = M (tgt e) ∈ (-d, d]` always lands in `edgeCut` of
`shiftedCut G M d`: `src e ∈ shiftedCut` while `tgt e ∉ shiftedCut`. Thus a positive tie atom
`P(M_u = M_v) > 0` creates a linear `+2 f_tie(0) |d|` cusp in `E[|edgeCut|]`. -/
theorem tie_mem_edgeCut_shiftedCut {V E : Type*} (G : Multigraph V E) (M : V → ℝ) {d : ℝ}
    {e : E} (hsrc : 0 < G.divergence (G.src e)) (htgt : ¬ 0 < G.divergence (G.tgt e))
    (htie : M (G.src e) = M (G.tgt e)) (hlo : -d < M (G.src e)) (hhi : M (G.src e) ≤ d) :
    e ∈ G.edgeCut (shiftedCut G M d) := by
  simp only [mem_edgeCut, shiftedCut, mem_ofPred_eq, hsrc, htgt, ↓reduceIte, ← htie]
  exact fun h => (not_le.mpr hlo) (h.mp hhi)

/-- **Expected backward-cut identity under symmetric marginals.** On a finite loopless multigraph
`G`, if every vertex score `M · v` has marginal `P(M v ≤ d) = 1 - F (-d)` and
`P(M v ≤ -d) = F (-d)`, then `2 E[|inCut(P_d)|] = E[|edgeCut(P_d)|] - (1 / 2 - F(-d)) ∑_v |σ(v)|`,
and when `∀ v, 1 ≤ |σ(v)|` and `F (-d) ≤ 1 / 2`,
`∑_e P(e ∈ inCut(P_d)) ≤ (∑_e P(e ∈ edgeCut(P_d))) / 2 - (1 / 4 - F (-d) / 2) * |V|`. -/
theorem sum_measureReal_inCut_shiftedCut_le {Ω V E : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype V] [Fintype E] (G : Multigraph V E)
    (hloop : G.Loopless) (hodd : ∀ v : V, (1 : ℤ) ≤ |G.divergence v|)
    (M : Ω → V → ℝ) (hM : ∀ v, Measurable fun ω => M ω v) {d q : ℝ} (hq : q ≤ 1 / 2)
    (hpos : ∀ v, 0 < G.divergence v → P.real {ω | M ω v ≤ d} = 1 - q)
    (hneg : ∀ v, ¬ 0 < G.divergence v → P.real {ω | M ω v ≤ -d} = q) :
    (∑ e : E, P.real {ω | e ∈ G.inCut (shiftedCut G (M ω) d)}) ≤
      (∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) d)}) / 2 -
        (1 / 4 - q / 2) * Fintype.card V := by
  classical
  have hmeas_v (v : V) : MeasurableSet {ω | v ∈ shiftedCut G (M ω) d} :=
    hM v measurableSet_Iic
  have hmeas_in (e : E) : MeasurableSet {ω | e ∈ G.inCut (shiftedCut G (M ω) d)} :=
    (hmeas_v (G.src e)).compl.inter (hmeas_v (G.tgt e))
  have hmeas_ed (e : E) : MeasurableSet {ω | e ∈ G.edgeCut (shiftedCut G (M ω) d)} := by
    simp only [G.edgeCut_eq_inCut_union_outCut, mem_union, ofPred_or]
    exact (hmeas_in e).union ((hmeas_v (G.src e)).inter (hmeas_v (G.tgt e)).compl)
  -- Integrate the pointwise identity `2 * inCut + sum_div = edgeCut` over `ω ~ P`.
  have hpt (ω : Ω) :
      2 * (∑ e : E, ({ω' | e ∈ G.inCut (shiftedCut G (M ω') d)}).indicator (1 : Ω → ℝ) ω) +
        (∑ v : V, (G.divergence v : ℝ) *
          ({ω' | v ∈ shiftedCut G (M ω') d}).indicator (1 : Ω → ℝ) ω) =
        ∑ e : E, ({ω' | e ∈ G.edgeCut (shiftedCut G (M ω') d)}).indicator (1 : Ω → ℝ) ω := by
    have hin_ind : (∑ e : E, ({ω' | e ∈ G.inCut (shiftedCut G (M ω') d)}).indicator (1 : Ω → ℝ) ω) =
        ((G.inCut (shiftedCut G (M ω) d)).ncard : ℝ) :=
      (ncard_eq_sum_indicator (fun e : E => {ω' | e ∈ G.inCut (shiftedCut G (M ω') d)}) ω).symm
    have hed_ind :
        (∑ e : E, ({ω' | e ∈ G.edgeCut (shiftedCut G (M ω') d)}).indicator (1 : Ω → ℝ) ω) =
          ((G.edgeCut (shiftedCut G (M ω) d)).ncard : ℝ) :=
      (ncard_eq_sum_indicator (fun e : E => {ω' | e ∈ G.edgeCut (shiftedCut G (M ω') d)}) ω).symm
    have hdiv_ind : (∑ v : V, (G.divergence v : ℝ) *
        ({ω' | v ∈ shiftedCut G (M ω') d}).indicator (1 : Ω → ℝ) ω) =
        ((∑ v : V, if v ∈ shiftedCut G (M ω) d then G.divergence v else 0 : ℤ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ shiftedCut G (M ω) d <;> simp [Set.indicator, hv]
    rw [hin_ind, hed_ind, hdiv_ind]
    exact_mod_cast G.two_mul_ncard_inCut_add_sum_divergence hloop (shiftedCut G (M ω) d)
  have hint_in : Integrable
      (fun ω => ∑ e : E, ({ω' | e ∈ G.inCut (shiftedCut G (M ω') d)}).indicator (1 : Ω → ℝ) ω) P :=
    integrable_finsetSum _ fun e _ => (integrable_const (1 : ℝ)).indicator (hmeas_in e)
  have hint_v (v : V) : Integrable (fun ω => (G.divergence v : ℝ) *
      ({ω' | v ∈ shiftedCut G (M ω') d}).indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1 : ℝ)).indicator (hmeas_v v)).const_mul _
  have hint_div : Integrable (fun ω => ∑ v : V, (G.divergence v : ℝ) *
      ({ω' | v ∈ shiftedCut G (M ω') d}).indicator (1 : Ω → ℝ) ω) P :=
    integrable_finsetSum _ fun v _ => hint_v v
  have hmean_eq :
      2 * (∑ e : E, P.real {ω | e ∈ G.inCut (shiftedCut G (M ω) d)}) +
        (∑ v : V, (G.divergence v : ℝ) * P.real {ω | v ∈ shiftedCut G (M ω) d}) =
        ∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) d)} := by
    have hI := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂P) (funext hpt)
    rw [integral_add (hint_in.const_mul 2) hint_div, integral_const_mul,
      integral_sum_indicator_one Finset.univ (fun e _ => hmeas_in e),
      integral_sum_indicator_one Finset.univ (fun e _ => hmeas_ed e)] at hI
    have hsum_v : (∫ ω, ∑ v : V, (G.divergence v : ℝ) *
        ({ω' | v ∈ shiftedCut G (M ω') d}).indicator (1 : Ω → ℝ) ω ∂P) =
        ∑ v : V, (G.divergence v : ℝ) * P.real {ω | v ∈ shiftedCut G (M ω) d} := by
      rw [integral_finsetSum Finset.univ fun v _ => hint_v v]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul, integral_indicator_one (hmeas_v v)]
    rwa [hsum_v] at hI
  -- Evaluate `∑_v σ(v) P(v ∈ P_d) = (1 / 2 - q) ∑_v |σ(v)| + (1 / 2) ∑_v σ(v)`.
  have hsum_zero : (∑ v : V, (G.divergence v : ℝ)) = 0 := mod_cast G.sum_divergence hloop
  have hdiv_eval :
      (∑ v : V, (G.divergence v : ℝ) * P.real {ω | v ∈ shiftedCut G (M ω) d}) =
        (1 - 2 * q) / 2 * (∑ v : V, |(G.divergence v : ℝ)|) := by
    have hv_eq (v : V) : (G.divergence v : ℝ) * P.real {ω | v ∈ shiftedCut G (M ω) d} =
        (G.divergence v : ℝ) / 2 + (1 / 2 - q) * |(G.divergence v : ℝ)| := by
      by_cases hv : 0 < G.divergence v
      · have hP : P.real {ω | v ∈ shiftedCut G (M ω) d} = 1 - q := by
          simpa [shiftedCut, hv] using hpos v hv
        rw [hP, abs_of_pos (by exact_mod_cast hv)]
        ring
      · have hP : P.real {ω | v ∈ shiftedCut G (M ω) d} = q := by
          simpa [shiftedCut, hv] using hneg v hv
        rw [hP, abs_of_nonpos (by exact_mod_cast le_of_not_gt hv)]
        ring
    simp_rw [hv_eq]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, hsum_zero, zero_div, zero_add,
      ← Finset.mul_sum]
    ring
  have hprod := mul_le_mul_of_nonneg_left (card_le_sum_abs_divergence G hodd)
    (by linarith : 0 ≤ (1 - 2 * q) / 2)
  linarith [hmean_eq, hdiv_eval, hprod]

/-- **Smooth divergence shift theorem.** On a nonempty finite loopless cubic
multigraph `G`, let `M : Ω → V → ℝ` have symmetric marginal cdf `F` (`F 0 = 1 / 2`,
`F t + F (-t) = 1`, `HasDerivAt F f₀ 0` with `0 < f₀`) and smooth symmetric crossing rate `c(d)` at
`d = 0` (`HasDerivAt c 0 0` with `c 0 < 1 / 2` — which holds for atom-free adjacent scores
`P(M_{src e} = M_{tgt e}) = 0`, whereas positive tie mass produces the linear cusp of
`tie_mem_edgeCut_shiftedCut`). Then there exists `d > 0` with `0 < F (-d)` such that
`((E[|inCut(P_d)|] / |V|) / F (-d)) < c 0`. -/
theorem exists_pos_shifted_inCut_ratio_lt {Ω V E : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype V] [Nonempty V] [Fintype E]
    (G : Multigraph V E) (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (M : Ω → V → ℝ) (hM : ∀ v, Measurable fun ω => M ω v)
    {F : ℝ → ℝ} {f₀ : ℝ} (hF0 : F 0 = 1 / 2) (hFsymm : ∀ t, F t + F (-t) = 1)
    (hFm : ∀ v t, P.real {ω | M ω v ≤ t} = F t) (hFderiv : HasDerivAt F f₀ 0) (hf₀ : 0 < f₀)
    (hc0 : (∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) 0)}) / Fintype.card V < 1 / 2)
    (hcderiv : HasDerivAt
      (fun d => (∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) d)}) / Fintype.card V)
      0 0) :
    ∃ d > 0, 0 < F (-d) ∧
      ((∑ e : E, P.real {ω | e ∈ G.inCut (shiftedCut G (M ω) d)}) / Fintype.card V) / F (-d) <
        (∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) 0)}) / Fintype.card V := by
  set h : ℝ := (Fintype.card V : ℝ)
  have hhpos : 0 < h := Nat.cast_pos.mpr Fintype.card_pos
  set c : ℝ → ℝ := fun d =>
    (∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) d)}) / h
  set q : ℝ → ℝ := fun d => F (-d)
  have hq0 : q 0 = 1 / 2 := by simp [q, hF0]
  have hq_deriv : HasDerivAt q (-f₀) 0 := by
    have hF0' : HasDerivAt F f₀ (-(0 : ℝ)) := by rwa [neg_zero]
    have hc := hF0'.comp (0 : ℝ) (hasDerivAt_neg 0)
    rwa [mul_neg_one] at hc
  -- Consider the smooth upper envelope `u(d) := (c(d) / 2 - (1 / 4 - q(d) / 2)) / q(d)`.
  let u : ℝ → ℝ := fun d => (c d / 2 - (1 / 4 - q d / 2)) / q d
  have hu0 : u 0 = c 0 := by
    simp only [u, hq0]
    ring
  have hnum_deriv : HasDerivAt (fun d => c d / 2 - (1 / 4 - q d / 2))
      (0 / 2 - (0 - -f₀ / 2)) 0 :=
    (hcderiv.div_const 2).sub ((hasDerivAt_const 0 (1 / 4 : ℝ)).sub (hq_deriv.div_const 2))
  have hu_deriv : HasDerivAt u (-f₀ * (1 - 2 * c 0)) 0 := by
    have hd := hnum_deriv.div hq_deriv (by linarith [hq0])
    convert hd using 1
    rw [hq0]
    ring
  have hslope_neg : -f₀ * (1 - 2 * c 0) < 0 := by nlinarith [hc0, hf₀]
  -- By `HasDerivAt` at `0`, for small `d > 0`, `(u d - u 0) / d < 0` and `0 < q d ≤ 1 / 2`.
  have hlim := (hasDerivAt_iff_tendsto_slope.mp hu_deriv).eventually (Iio_mem_nhds hslope_neg)
  rw [eventually_nhdsWithin_iff] at hlim
  have hq_cont : ContinuousAt q 0 := hq_deriv.continuousAt
  have hq_pos_ev : ∀ᶠ d in nhds (0 : ℝ), 0 < q d :=
    hq_cont.eventually (Ioi_mem_nhds (by linarith [hq0]))
  have hq_lt_ev : ∀ᶠ d in nhds (0 : ℝ), d > 0 → q d ≤ 1 / 2 := by
    have hlim_q := (hasDerivAt_iff_tendsto_slope.mp hq_deriv).eventually
      (Iio_mem_nhds (by linarith : -f₀ < 0))
    rw [eventually_nhdsWithin_iff] at hlim_q
    filter_upwards [hlim_q] with d hd hdpos
    have hsl := hd (Set.mem_compl_singleton_iff.mpr hdpos.ne')
    rw [slope_def_field, sub_zero, hq0, div_lt_iff₀ hdpos, zero_mul] at hsl
    linarith
  obtain ⟨δ, hδpos, hball⟩ := Metric.eventually_nhds_iff.mp
    (hlim.and (hq_pos_ev.and hq_lt_ev))
  set d := δ / 2 with hd_def
  have hdpos : 0 < d := half_pos hδpos
  have hdist : dist d 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdpos]
    linarith [hd_def, hδpos]
  obtain ⟨hu_sl, hqd_pos, hqd_le⟩ := hball hdist
  have hu_lt : u d < c 0 := by
    have hsl := hu_sl (Set.mem_compl_singleton_iff.mpr hdpos.ne')
    rw [slope_def_field, sub_zero, hu0, div_lt_iff₀ hdpos, zero_mul] at hsl
    linarith
  refine ⟨d, hdpos, hqd_pos, ?_⟩
  have hodd : ∀ v : V, (1 : ℤ) ≤ |G.divergence v| :=
    G.one_le_abs_divergence_of_cubic hloop h3
  have hin_le := sum_measureReal_inCut_shiftedCut_le G hloop hodd M hM (hqd_le hdpos)
    (fun v _ => by rw [hFm]; linarith [hFsymm d])
    (fun v _ => hFm v (-d))
  have hdiv_h : (∑ e : E, P.real {ω | e ∈ G.inCut (shiftedCut G (M ω) d)}) / h ≤
      c d / 2 - (1 / 4 - q d / 2) := by
    rw [div_le_iff₀ hhpos]
    have hc_def : c d * h = ∑ e : E, P.real {ω | e ∈ G.edgeCut (shiftedCut G (M ω) d)} :=
      div_mul_cancel₀ _ hhpos.ne'
    linarith [hin_le, hc_def]
  exact (div_le_div_of_nonneg_right hdiv_h hqd_pos.le).trans_lt hu_lt

end Cslib.Circuits.Frontier.DirectedShift

/-! ### Part 4: 4-type cubic degree-balance LP and shifted `VertexGaussian` (`4.2170 N`) -/

namespace Cslib.Circuits.Frontier

namespace DirectedShift

open _root_.Cslib.Circuits.Frontier.Multigraph ProbabilityTheory Gaussian

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-- Worst-case expected entering edges per vertex `p_{+-} + p_{-+} / 2` for shifted `VertexGaussian`
at correlation `ρ` and shift `d`. -/
noncomputable def shiftedSupply (ρ d : ℝ) : ℝ :=
  (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ -d} +
    1 / 2 * (correlatedGaussian ρ).real {p | -d < p.1 ∧ p.2 ≤ d}

private theorem shiftedSupply_nonneg (ρ d : ℝ) : 0 ≤ shiftedSupply ρ d := by
  unfold shiftedSupply
  positivity

private theorem card_edges_eq_of_cubic {V E : Type*} [Fintype V] [Fintype E]
    {Q : Multigraph V E} (hloop : Q.Loopless) (h3 : ∀ v, (Q.incidenceSet v).ncard = 3) :
    (Fintype.card E : ℝ) = 3 / 2 * Fintype.card V := by
  have hsum := Q.sum_ncard_incidenceSet hloop
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have : ((Fintype.card V * 3 : ℕ) : ℝ) = ((2 * Nat.card E : ℕ) : ℝ) := by exact_mod_cast hsum
  rw [← Nat.card_eq_fintype_card (α := E)]
  push_cast at this
  linarith

/-- **Exact 4-type cubic degree-balance LP.** On any finite loopless 3-regular multigraph `Q`, if
every adjacent pair has inner product at least `ρ ∈ [0, 1]` and `0 ≤ d`, then the expected size of
`Q.inCut (shiftedCut Q (vertexScore Q q R ω) d)` is at most `shiftedSupply ρ d * |V(Q)|`. -/
theorem sum_measureReal_inCut_vertexScore_le {V E : Type*} [Fintype V] [Fintype E]
    (Q : Multigraph V E) (hloop : Q.Loopless) (h3 : ∀ v, (Q.incidenceSet v).ncard = 3)
    {q ρ d : ℝ} (hq : 0 ≤ q) (R : ℕ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (hd : 0 ≤ d) :
    (∑ e : E, (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | e ∈ Q.inCut (shiftedCut Q (vertexScore Q q R ω) d)}) ≤
      shiftedSupply ρ d * Fintype.card V := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  have hdeg : Q.MaxDegreeLE 3 := fun v => (h3 v).le
  set p_dd := (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ d}
  set p_pm := (correlatedGaussian ρ).real {p | d < p.1 ∧ p.2 ≤ -d}
  set p_mp := (correlatedGaussian ρ).real {p | -d < p.1 ∧ p.2 ≤ d}
  have hρ_abs : |ρ| ≤ 1 := abs_le.mpr ⟨by linarith, hρ1⟩
  -- Bound each edge by its endpoint sign pattern `(0 < σ(src e), 0 < σ(tgt e))`.
  let wt : E → ℝ := fun e =>
    if 0 < Q.divergence (Q.src e) then
      if 0 < Q.divergence (Q.tgt e) then p_dd else p_pm
    else
      if 0 < Q.divergence (Q.tgt e) then p_mp else p_dd
  have hedge_le (e : E) :
      P.real {ω | e ∈ Q.inCut (shiftedCut Q (vertexScore Q q R ω) d)} ≤ wt e := by
    set u := unitKernelRow Q.toSimpleGraph q R (Q.src e)
    set v := unitKernelRow Q.toSimpleGraph q R (Q.tgt e)
    have hu : ‖u‖ = 1 := norm_unitKernelRow q R (Q.src e)
    have hv : ‖v‖ = 1 := norm_unitKernelRow q R (Q.tgt e)
    set ρ_e := ⟪u, v⟫
    have hρe_lo : ρ ≤ ρ_e := hρ.trans <| by
      convert le_inner_unitKernelRow_src_tgt hloop (d := 3) (by norm_num) hdeg hq R e using 2
      norm_num
    have hρe_hi : ρ_e ≤ 1 := (real_inner_le_norm u v).trans_eq (by rw [hu, hv, mul_one])
    set tu : ℝ := if 0 < Q.divergence (Q.src e) then d else -d
    set tv : ℝ := if 0 < Q.divergence (Q.tgt e) then d else -d
    have hev : {ω | e ∈ Q.inCut (shiftedCut Q (vertexScore Q q R ω) d)} =
        {ω | (⟪u, WithLp.toLp 2 ω⟫, ⟪v, WithLp.toLp 2 ω⟫) ∈ {p : ℝ × ℝ | tu < p.1 ∧ p.2 ≤ tv}} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inCut, shiftedCut, not_le, vertexScore, u, v, tu, tv]
    have hmS : MeasurableSet {p : ℝ × ℝ | tu < p.1 ∧ p.2 ≤ tv} :=
      (measurableSet_Ioi.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
    rw [hev, measureReal_pi_inner_prod_eq_correlatedGaussian hu hv hmS]
    have hanti := measureReal_correlatedGaussian_gt_and_le_anti (by linarith) hρe_lo hρe_hi tu tv
    refine hanti.trans_eq ?_
    by_cases hs : 0 < Q.divergence (Q.src e) <;> by_cases ht : 0 < Q.divergence (Q.tgt e) <;>
      simp only [tu, tv, wt, p_dd, p_pm, p_mp, hs, ht, ↓reduceIte]
    exact measureReal_correlatedGaussian_gt_neg_le_neg hρ_abs d
  -- Partition `V` into the 4 cubic divergence classes `(+3, +1, -1, -3)` and bound `∑ e, wt e`.
  set h : ℝ := (Fintype.card V : ℝ)
  have hE_card : (Fintype.card E : ℝ) = 3 / 2 * h := card_edges_eq_of_cubic hloop h3
  set Vpos : Set V := {v | 0 < Q.divergence v}
  set e_pm : ℝ := ((Q.outCut Vpos).ncard : ℝ)
  set e_mp : ℝ := ((Q.inCut Vpos).ncard : ℝ)
  -- Express `∑ e, wt e` in terms of `|E|`, `e_pm`, and `e_mp`:
  have hwt_sum : (∑ e : E, wt e) =
      (Fintype.card E : ℝ) * p_dd + e_pm * (p_pm - p_dd) + e_mp * (p_mp - p_dd) := by
    have h1 (e : E) : wt e = p_dd +
        (if e ∈ Q.outCut Vpos then (1 : ℝ) else 0) * (p_pm - p_dd) +
        (if e ∈ Q.inCut Vpos then (1 : ℝ) else 0) * (p_mp - p_dd) := by
      by_cases hs : 0 < Q.divergence (Q.src e) <;> by_cases ht : 0 < Q.divergence (Q.tgt e) <;>
        simp only [wt, Vpos, mem_outCut, mem_inCut, mem_ofPred_eq, hs, ht, ↓reduceIte,
          not_true_eq_false, not_false_eq_true, and_self, and_false, false_and] <;> ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_boole]
    have hcnt (S : Set E) : ((Finset.univ.filter (· ∈ S)).card : ℝ) = (S.ncard : ℝ) := by
      rw [Set.filter_mem_univ_eq_toFinset, ncard_eq_toFinset_card']
    rw [hcnt, hcnt]
  -- Divergence identity on `Vpos`: `e_pm - e_mp = ∑_{v ∈ Vpos} σ(v)`.
  have hflux : e_pm - e_mp = ∑ v : V, if 0 < Q.divergence v then (Q.divergence v : ℝ) else 0 := by
    have hdiv := Q.two_mul_ncard_inCut_add_sum_divergence hloop Vpos
    have htot := Q.ncard_edgeCut_eq_add Vpos
    have hcast : ((∑ v : V, if v ∈ Vpos then Q.divergence v else 0 : ℤ) : ℝ) =
        ∑ v : V, if 0 < Q.divergence v then (Q.divergence v : ℝ) else 0 := by
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [Vpos]
    have hlin : (∑ v : V, if v ∈ Vpos then Q.divergence v else 0) =
        ((Q.outCut Vpos).ncard : ℤ) - ((Q.inCut Vpos).ncard : ℤ) := by omega
    have hlinR : ((∑ v : V, if v ∈ Vpos then Q.divergence v else 0 : ℤ) : ℝ) = e_pm - e_mp := by
      rw [hlin]
      push_cast
      rfl
    linarith [hcast, hlinR]
  -- Total divergence is `0`, so `2 * (e_pm - e_mp) = ∑_v |σ(v)| ≥ |V|`:
  have hsum_zero : (∑ v : V, (Q.divergence v : ℝ)) = 0 := mod_cast Q.sum_divergence hloop
  have hflux_ge : h / 2 ≤ e_pm - e_mp := by
    have hpt (v : V) : |(Q.divergence v : ℝ)| =
        2 * (if 0 < Q.divergence v then (Q.divergence v : ℝ) else 0) - Q.divergence v := by
      split_ifs with hv
      · rw [abs_of_pos (by exact_mod_cast hv)]
        ring
      · rw [abs_of_nonpos (by exact_mod_cast le_of_not_gt hv)]
        ring
    have habs_sum : 2 * (e_pm - e_mp) = ∑ v : V, |(Q.divergence v : ℝ)| := by
      rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_sub_distrib, hsum_zero, sub_zero,
        ← Finset.mul_sum, hflux]
    have hge : h ≤ ∑ v : V, |(Q.divergence v : ℝ)| :=
      card_le_sum_abs_divergence Q (Q.one_le_abs_divergence_of_cubic hloop h3)
    linarith
  -- Also `e_pm + e_mp = |edgeCut Vpos| ≤ |E| = 3 / 2 * h`:
  have hcross_le : e_pm + e_mp ≤ 3 / 2 * h := by
    have hleR : ((Q.edgeCut Vpos).ncard : ℝ) ≤ (Fintype.card E : ℝ) :=
      mod_cast (ncard_le_card _).trans_eq Nat.card_eq_fintype_card
    have haddR : ((Q.edgeCut Vpos).ncard : ℝ) = e_mp + e_pm := by
      dsimp only [e_mp, e_pm]
      exact_mod_cast Q.ncard_edgeCut_eq_add Vpos
    linarith [hE_card]
  -- Nonnegativity of `p_mp - p_pm = Φ d - Φ (-d)` and `p_pm + p_mp - 2 * p_dd`:
  have hdiff_nonneg : 0 ≤ p_mp - p_pm := by
    dsimp only [p_mp, p_pm]
    rw [measureReal_correlatedGaussian_gt_and_le hρ_abs (-d) d,
      measureReal_correlatedGaussian_gt_and_le hρ_abs d (-d),
      ← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, gaussianQuadrant_comm hρ_abs]
    have hmono : Φ (-d) ≤ Φ d := (monotone_cdf _ (by linarith : -d ≤ d))
    linarith
  have hdelta_nonneg : 0 ≤ p_pm + p_mp - 2 * p_dd := by
    linarith [two_mul_correlatedGaussian_gt_le_diag_le hρ_abs hd]
  -- Combine `∑ P ≤ ∑ wt` with the exact algebraic identity:
  have hsum_le : (∑ e : E, P.real {ω | e ∈ Q.inCut (shiftedCut Q (vertexScore Q q R ω) d)}) ≤
      ∑ e : E, wt e := Finset.sum_le_sum fun e _ => hedge_le e
  set esame := 3 / 2 * h - (e_pm + e_mp) with hesame_def
  have hesame_nonneg : 0 ≤ esame := by linarith [hcross_le, hesame_def]
  have hid : (Fintype.card E : ℝ) * p_dd + e_pm * (p_pm - p_dd) + e_mp * (p_mp - p_dd) =
      (p_pm + 1 / 2 * p_mp) * h - (e_pm - e_mp - h / 2) / 2 * (p_mp - p_pm) -
        esame / 2 * (p_pm + p_mp - 2 * p_dd) := by
    rw [hE_card]
    dsimp only [esame]
    ring
  have ht1 : 0 ≤ (e_pm - e_mp - h / 2) / 2 * (p_mp - p_pm) :=
    mul_nonneg (by linarith [hflux_ge]) hdiff_nonneg
  have ht2 : 0 ≤ esame / 2 * (p_pm + p_mp - 2 * p_dd) :=
    mul_nonneg (by linarith [hesame_nonneg]) hdelta_nonneg
  unfold shiftedSupply
  linarith [hsum_le, hwt_sum, hid, ht1, ht2]

/-! ### Part 5: Exact numerical certificate at `d = 1 / 20`, `ρ* = 2√2 / 3` (`4.2170 N`) -/

/-- Upper bound `arccos (2√2 / 3) ≤ 3398371 / 10000000` by `cos_bound` and six angle doublings. -/
private theorem arccos_two_sqrt_two_div_three_le :
    arccos (2 * √2 / 3) ≤ 3398371 / 10000000 := by
  have hsqrt : (141421356 : ℝ) / 100000000 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hcos : cos (3398371 / 10000000) ≤ 2 * √2 / 3 := by
    have hb := cos_bound (x := 3398371 / 640000000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3398371 / 640000000)] at hb
    have h0 : cos (3398371 / 640000000) ≤ 199997180446403 / 200000000000000 := by
      linarith [(abs_le.mp hb).2]
    have h1 := Gaussian.cos_two_mul_le (by norm_num) h0
      (v := 199988721865111 / 200000000000000) (by norm_num)
    have h2 := Gaussian.cos_two_mul_le (by norm_num) h1
      (v := 999774443662037 / 1000000000000000) (by norm_num)
    have h3 := Gaussian.cos_two_mul_le (by norm_num) h2
      (v := 62443617274967 / 62500000000000) (by norm_num)
    have h4 := Gaussian.cos_two_mul_le (by norm_num) h3
      (v := 99639313325187 / 100000000000000) (by norm_num)
    have h5 := Gaussian.cos_two_mul_le (by norm_num) h4
      (v := 492799275991479 / 500000000000000) (by norm_num)
    have h6 := Gaussian.cos_two_mul_le (by norm_num) h5
      (v := 58925563208863 / 62500000000000) (by norm_num)
    have hval : (3398371 / 10000000 : ℝ) =
        2 * (2 * (2 * (2 * (2 * (2 * (3398371 / 640000000)))))) := by norm_num
    rw [hval]
    linarith [h6, hsqrt]
  exact (arccos_le_arccos hcos).trans_eq (arccos_cos (by norm_num) (by linarith [pi_gt_d20]))

private theorem gaussianPDFReal_even (u : ℝ) : φ (-u) = φ u := by
  simp [gaussianPDFReal_def]

private theorem gaussianPDFReal_eq_inv_sqrt (t : ℝ) :
    φ t = (√(2 * π))⁻¹ * exp (-(t ^ 2 / 2)) := by
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
  congr 2
  ring

private theorem integral_inv_sqrt_mul_one_sub_mul_sq (k a b : ℝ) :
    ∫ u in a..b, (√(2 * π))⁻¹ * (1 - k * u ^ 2) =
      (√(2 * π))⁻¹ * ((b - a) - k / 3 * (b ^ 3 - a ^ 3)) := by
  have hc : Continuous fun u : ℝ => k * u ^ 2 := by fun_prop
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const
      (hc.intervalIntegrable (μ := volume) a b), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_pow]
  simp only [smul_eq_mul]
  ring

/-- Tight rational upper bound on `Φ (-1 / 20)` via `1 - x ^ 2 / 2 ≤ exp (-x ^ 2 / 2)`. -/
private theorem cdf_neg_one_div_twenty_le :
    Φ (-1 / 20) ≤ 240030599 / 500000000 := by
  set d : ℝ := 1 / 20
  have hd_nonneg : (0 : ℝ) ≤ d := by dsimp [d]; norm_num
  have hrt_pos : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
  have hrt_hi : √(2 * π) < 250662828 / 100000000 := by
    have hpi_hi : π < 31415926536 / 10000000000 := by linarith [pi_lt_d20]
    exact (sqrt_lt' (by norm_num)).mpr (by linarith [hpi_hi])
  have hcdf_neg : Φ (-d) = 1 / 2 - ∫ x in (0 : ℝ)..d, φ x := by
    have h1 : Φ d - Φ 0 = ∫ x in (0 : ℝ)..d, φ x :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hasDerivAt_cdf_gaussianReal 0 one_ne_zero u)
        ((continuous_gaussianPDFReal 0 1).intervalIntegrable 0 d)).symm
    have h0 : Φ 0 = 1 / 2 := by rw [cdf_gaussianReal_zero_zero one_ne_zero]; norm_num
    have hn : Φ (-d) = 1 - Φ d := cdf_gaussianReal_neg one_ne_zero d
    linarith
  have hint_lo : (√(2 * π))⁻¹ * (d - d ^ 3 / 6) ≤ ∫ x in (0 : ℝ)..d, φ x := by
    have hc : Continuous fun x : ℝ => (√(2 * π))⁻¹ * (1 - 1 / 2 * x ^ 2) := by fun_prop
    have hm := intervalIntegral.integral_mono_on hd_nonneg
      (hc.intervalIntegrable (μ := volume) 0 d)
      ((continuous_gaussianPDFReal 0 1).intervalIntegrable 0 d) fun x _ => by
        rw [gaussianPDFReal_eq_inv_sqrt]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [add_one_le_exp (-(x ^ 2 / 2))]
    rw [integral_inv_sqrt_mul_one_sub_mul_sq] at hm
    exact le_of_eq_of_le (by ring) hm
  have hnum_pos : 0 < d - d ^ 3 / 6 := by dsimp [d]; norm_num
  have hdiv_ge : (d - d ^ 3 / 6) / (250662828 / 100000000) ≤ (√(2 * π))⁻¹ * (d - d ^ 3 / 6) := by
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hnum_pos.le hrt_pos hrt_hi.le
  have hrat : 1 / 2 - (d - d ^ 3 / 6) / (250662828 / 100000000) ≤ 240030599 / 500000000 := by
    dsimp [d]; norm_num
  rw [show (-1 / 20 : ℝ) = -d by dsimp [d]; norm_num]
  linarith

/-- Polynomial upper-bound helper for the 2-step FTC quadrant shift integral at `d = 1 / 20`. -/
private noncomputable def shiftPoly (x : ℝ) : ℝ :=
  (1 - 1599 / 3200 * x ^ 2) *
    ((3 / 20 + 4 * √2 * x) - 391 / 2400 * ((3 / 20 + 2 * √2 * x) ^ 3 - (-(2 * √2 * x)) ^ 3))

private noncomputable def shiftAntideriv (x : ℝ) : ℝ :=
  (3 / 20 - 391 / 800 * (9 / 8000)) * x +
  (6 - 391 / 800 * (27 / 400)) * (2 * √2 / 3) * (x ^ 2 / 2) +
  (-(391 / 800 * (6 / 5)) - 1599 / 3200 * (3 / 20 - 391 / 800 * (9 / 8000))) * (x ^ 3 / 3) +
  (-(391 / 800 * 16) - 1599 / 3200 * (6 - 391 / 800 * (27 / 400))) * (2 * √2 / 3) * (x ^ 4 / 4) +
  (1599 / 3200 * (391 / 800 * (6 / 5))) * (x ^ 5 / 5) +
  (1599 / 3200 * (391 / 800 * 16)) * (2 * √2 / 3) * (x ^ 6 / 6)

private theorem hasDerivAt_shiftAntideriv (x : ℝ) :
    HasDerivAt shiftAntideriv (shiftPoly x) x := by
  have hsq2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hP_eq : shiftPoly x =
      (3 / 20 - 391 / 800 * (9 / 8000)) +
      (6 - 391 / 800 * (27 / 400)) * (2 * √2 / 3) * x +
      (-(391 / 800 * (6 / 5)) - 1599 / 3200 * (3 / 20 - 391 / 800 * (9 / 8000))) * x ^ 2 +
      (-(391 / 800 * 16) - 1599 / 3200 * (6 - 391 / 800 * (27 / 400))) * (2 * √2 / 3) * x ^ 3 +
      (1599 / 3200 * (391 / 800 * (6 / 5))) * x ^ 4 +
      (1599 / 3200 * (391 / 800 * 16)) * (2 * √2 / 3) * x ^ 5 := by
    unfold shiftPoly
    linear_combination (-(391 / 2400) * (1 - 1599 / 3200 * x ^ 2) *
      (36 / 20 * x ^ 2 + 16 * √2 * x ^ 3)) * hsq2
  rw [hP_eq]
  unfold shiftAntideriv
  have h1 := (hasDerivAt_id x).const_mul (3 / 20 - 391 / 800 * (9 / 8000))
  have h2 := ((hasDerivAt_pow 2 x).div_const 2).const_mul
    ((6 - 391 / 800 * (27 / 400)) * (2 * √2 / 3))
  have h3 := ((hasDerivAt_pow 3 x).div_const 3).const_mul
    (-(391 / 800 * (6 / 5)) - 1599 / 3200 * (3 / 20 - 391 / 800 * (9 / 8000)))
  have h4 := ((hasDerivAt_pow 4 x).div_const 4).const_mul
    ((-(391 / 800 * 16) - 1599 / 3200 * (6 - 391 / 800 * (27 / 400))) * (2 * √2 / 3))
  have h5 := ((hasDerivAt_pow 5 x).div_const 5).const_mul
    (1599 / 3200 * (391 / 800 * (6 / 5)))
  have h6 := ((hasDerivAt_pow 6 x).div_const 6).const_mul
    ((1599 / 3200 * (391 / 800 * 16)) * (2 * √2 / 3))
  convert (((((h1.add h2).add h3).add h4).add h5).add h6) using 1
  · ext y
    simp only [Pi.add_apply, id_eq]
  · push_cast
    ring

private theorem shiftAntideriv_diff_le :
    shiftAntideriv (1 / 20) - shiftAntideriv 0 ≤ 14461263 / 1000000000 := by
  have hs2_hi : √2 < (141421357 : ℝ) / 100000000 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hval : shiftAntideriv (1 / 20) - shiftAntideriv 0 =
      6098925183151 / 819200000000000 + 4877119869539 / 983040000000000 * √2 := by
    unfold shiftAntideriv
    ring
  rw [hval]
  linarith [hs2_hi]

/-- Tight rational lower bound on `P_{2√2/3}[z ≤ 1/20 ∧ z' ≤ -1/20]` via two 1D FTC steps. -/
private theorem two_seven_seven_le_correlatedGaussian_shift :
    (27725729 / 62500000 : ℝ) ≤
      (correlatedGaussian (2 * √2 / 3)).real {p | p.1 ≤ 1 / 20 ∧ p.2 ≤ -1 / 20} := by
  set ρ : ℝ := 2 * √2 / 3
  set d : ℝ := 1 / 20
  have hsq2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs2_hi : √2 < (141421357 : ℝ) / 100000000 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hρ_pos : 0 < ρ := by dsimp [ρ]; positivity
  have hρ_lt : ρ < 1 := by dsimp [ρ]; linarith [hs2_hi]
  have hρ_abs : |ρ| < 1 := abs_lt.mpr ⟨by linarith, hρ_lt⟩
  have hρ_sq : ρ ^ 2 = 8 / 9 := by dsimp [ρ]; linear_combination (4 / 9 : ℝ) * hsq2
  have hs_eq : √(1 - ρ ^ 2) = 1 / 3 := by
    rw [hρ_sq, show (1 : ℝ) - 8 / 9 = (1 / 3) ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have hpi_lo : (3141592653 : ℝ) / 1000000000 < π := by linarith [pi_gt_d20]
  have hd_nonneg : (0 : ℝ) ≤ d := by dsimp [d]; norm_num
  have hf00 : (correlatedGaussian ρ).real {p | p.1 ≤ 0 ∧ p.2 ≤ 0} =
      1 / 2 - arccos ρ / (2 * π) := by
    rw [← gaussianQuadrant_cdf_cdf, cdf_gaussianReal_zero_zero one_ne_zero, one_div,
      ← one_div, gaussianQuadrant_half_half hρ_abs.le]
  have hci (f : ℝ → ℝ) (hf : Continuous f) :
      IntervalIntegrable (fun x => φ x * Φ (f x)) volume 0 d :=
    ((continuous_gaussianPDFReal 0 1).mul
      ((continuous_cdf_gaussianReal 0 one_ne_zero).comp hf)).intervalIntegrable 0 d
  have hftc1 : (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ 0} -
      (correlatedGaussian ρ).real {p | p.1 ≤ 0 ∧ p.2 ≤ 0} =
      ∫ x in (0 : ℝ)..d, φ x * Φ (-3 * ρ * x) := by
    have hd1 : ∀ x ∈ uIcc (0 : ℝ) d, HasDerivAt
        (fun t => (correlatedGaussian ρ).real {p | p.1 ≤ t ∧ p.2 ≤ 0})
        (φ x * Φ (-3 * ρ * x)) x := by
      intro x _
      have h := hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_left hρ_abs x 0
      rwa [hs_eq, show (0 - ρ * x) / (1 / 3) = -3 * ρ * x by ring] at h
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hd1
      (hci (fun x => -3 * ρ * x) (by fun_prop))).symm
  have hftc2 : (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} -
      (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ 0} =
      ∫ x in (0 : ℝ)..d, -(φ x * Φ (3 * d + 3 * ρ * x)) := by
    have hd2 : ∀ x ∈ uIcc (0 : ℝ) d, HasDerivAt
        (fun t => (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -t})
        (-(φ x * Φ (3 * d + 3 * ρ * x))) x := by
      intro x _
      have h := (hasDerivAt_measureReal_correlatedGaussian_setOf_le_and_le_right hρ_abs d (-x)).comp
        x (hasDerivAt_neg x)
      rwa [hs_eq, gaussianPDFReal_even,
        show (d - ρ * -x) / (1 / 3) = 3 * d + 3 * ρ * x by ring, mul_neg_one] at h
    simpa only [neg_zero] using (intervalIntegral.integral_eq_sub_of_hasDerivAt hd2
      (hci (fun x => 3 * d + 3 * ρ * x) (by fun_prop)).neg).symm
  have hdiff_eq : (correlatedGaussian ρ).real {p | p.1 ≤ 0 ∧ p.2 ≤ 0} -
      (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} =
      ∫ x in (0 : ℝ)..d, φ x * (Φ (3 * d + 3 * ρ * x) - Φ (-3 * ρ * x)) := by
    rw [intervalIntegral.integral_neg] at hftc2
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hci (fun x => 3 * d + 3 * ρ * x) (by fun_prop))
      (hci (fun x => -3 * ρ * x) (by fun_prop))]
    linarith
  -- Quadratic Taylor bound `φ u ≤ (1 - k u²) / √(2π)` for `u² ≤ 8 (1 / 2 - k)`:
  have hphi {u k : ℝ} (hu : u ^ 2 ≤ 8 * (1 / 2 - k)) :
      φ u ≤ (√(2 * π))⁻¹ * (1 - k * u ^ 2) := by
    rw [gaussianPDFReal_eq_inv_sqrt]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [sq_nonneg u, Real.exp_neg_le_one_sub_add_sq_div_two (x := u ^ 2 / 2) (by positivity)]
  have hpt_le : ∀ x ∈ Icc (0 : ℝ) d,
      φ x * (Φ (3 * d + 3 * ρ * x) - Φ (-3 * ρ * x)) ≤ (2 * π)⁻¹ * shiftPoly x := by
    rintro x ⟨hx0, hxd⟩
    set a := -3 * ρ * x
    set b := 3 * d + 3 * ρ * x
    have hab : a ≤ b := by dsimp [a, b, d]; nlinarith
    have hcdf_sub : Φ b - Φ a = ∫ u in a..b, φ u :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hasDerivAt_cdf_gaussianReal 0 one_ne_zero u)
        ((continuous_gaussianPDFReal 0 1).intervalIntegrable a b)).symm
    have hinner_le : ∫ u in a..b, φ u ≤
        (√(2 * π))⁻¹ * ((b - a) - 391 / 2400 * (b ^ 3 - a ^ 3)) := by
      have hcu : Continuous fun u : ℝ => (√(2 * π))⁻¹ * (1 - 391 / 800 * u ^ 2) := by fun_prop
      have hmono := intervalIntegral.integral_mono_on hab
        ((continuous_gaussianPDFReal 0 1).intervalIntegrable a b)
        (hcu.intervalIntegrable (μ := volume) a b) fun u hu => hphi (by
          rcases hu with ⟨hua, hub⟩
          have ha_lo : -3 / 20 ≤ a := by dsimp [a, d] at hxd ⊢; nlinarith [hρ_lt]
          have hb_hi : b ≤ 3 / 10 := by dsimp [b, d] at hxd ⊢; nlinarith [hρ_lt]
          have habs : |u| ≤ 3 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
          nlinarith [sq_abs u, abs_nonneg u])
      exact hmono.trans_eq ((integral_inv_sqrt_mul_one_sub_mul_sq _ a b).trans (by ring))
    have hcdf_nonneg : 0 ≤ Φ b - Φ a := sub_nonneg.mpr (monotone_cdf _ hab)
    have hpx_le := hphi (u := x) (k := 1599 / 3200) (by dsimp [d] at hxd; nlinarith)
    have hpx_pos : 0 ≤ (√(2 * π))⁻¹ * (1 - 1599 / 3200 * x ^ 2) :=
      (gaussianPDFReal_nonneg 0 1 x).trans hpx_le
    calc φ x * (Φ b - Φ a)
        ≤ ((√(2 * π))⁻¹ * (1 - 1599 / 3200 * x ^ 2)) *
            ((√(2 * π))⁻¹ * ((b - a) - 391 / 2400 * (b ^ 3 - a ^ 3))) :=
          mul_le_mul hpx_le (hcdf_sub ▸ hinner_le) hcdf_nonneg hpx_pos
      _ = (2 * π)⁻¹ * shiftPoly x := by
          have hsq_pi : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
            rw [← mul_inv, mul_self_sqrt (by positivity)]
          have hb_sub_a : b - a = 3 / 20 + 4 * √2 * x := by dsimp [a, b, d, ρ]; ring
          have hb_eq : b = 3 / 20 + 2 * √2 * x := by dsimp [b, d, ρ]; ring
          have ha_eq : a = -(2 * √2 * x) := by dsimp [a, ρ]; ring
          rw [hb_sub_a, hb_eq, ha_eq]
          unfold shiftPoly
          linear_combination ((1 - 1599 / 3200 * x ^ 2) *
            ((3 / 20 + 4 * √2 * x) -
              391 / 2400 * ((3 / 20 + 2 * √2 * x) ^ 3 - (-(2 * √2 * x)) ^ 3))) * hsq_pi
  have hint_le : (correlatedGaussian ρ).real {p | p.1 ≤ 0 ∧ p.2 ≤ 0} -
      (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} ≤
      (2 * π)⁻¹ * (14461263 / 1000000000) := by
    rw [hdiff_eq]
    have hcP : Continuous fun x => (2 * π)⁻¹ * shiftPoly x := by unfold shiftPoly; fun_prop
    have hcP0 : Continuous shiftPoly := by unfold shiftPoly; fun_prop
    have hm := intervalIntegral.integral_mono_on hd_nonneg
      (((continuous_gaussianPDFReal 0 1).mul
        ((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop) |>.sub
          ((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)))).intervalIntegrable
            (μ := volume) 0 d)
      (hcP.intervalIntegrable (μ := volume) 0 d) hpt_le
    have hint_P : ∫ x in (0 : ℝ)..d, (2 * π)⁻¹ * shiftPoly x =
        (2 * π)⁻¹ * (shiftAntideriv d - shiftAntideriv 0) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_shiftAntideriv x)
          (hcP0.intervalIntegrable (μ := volume) 0 d)]
    have hmul : (2 * π)⁻¹ * (shiftAntideriv d - shiftAntideriv 0) ≤
        (2 * π)⁻¹ * (14461263 / 1000000000) :=
      mul_le_mul_of_nonneg_left (by simpa [d] using shiftAntideriv_diff_le) (by positivity)
    exact hm.trans (hint_P ▸ hmul)
  have hdiv_le : arccos ρ / (2 * π) + (2 * π)⁻¹ * (14461263 / 1000000000) ≤
      (3398371 / 10000000 + 14461263 / 1000000000) / (2 * (3141592653 / 1000000000)) := by
    rw [← div_eq_inv_mul, ← add_div]
    exact (div_le_div_of_nonneg_right (by linarith [arccos_two_sqrt_two_div_three_le])
      (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [hpi_lo]))
  rw [show (-1 / 20 : ℝ) = -d by dsimp [d]; norm_num]
  linarith [hf00, hint_le, hdiv_le, show (27725729 / 62500000 : ℝ) ≤
    1 / 2 - (3398371 / 10000000 + 14461263 / 1000000000) / (2 * (3141592653 / 1000000000)) by
      norm_num]

/-- **Strict rational certificate**
`4217 / 1000 < 1 + Φ(-1/20) / (2 · shiftedSupply (2√2/3) (1/20))`.
Proved via two 1D applications of the fundamental theorem of calculus on `QuadrantDeriv` and
quadratic Taylor bounds on `φ` (`Real.exp_neg_le_one_sub_add_sq_div_two`). -/
theorem four_two_one_seven_lt_shifted_coeff :
    (4217 / 1000 : ℝ) <
      1 + Φ (-1 / 20) / (2 * shiftedSupply (2 * √2 / 3) (1 / 20)) := by
  set ρ : ℝ := 2 * √2 / 3
  set d : ℝ := 1 / 20
  have hs2_hi : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hρ_abs : |ρ| < 1 :=
    abs_lt.mpr ⟨by dsimp [ρ]; linarith [sqrt_nonneg 2], by dsimp [ρ]; linarith⟩
  have hsup_eq : shiftedSupply ρ d =
      1 / 2 + 1 / 2 * Φ (-d) -
        3 / 2 * (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
    unfold shiftedSupply
    rw [measureReal_correlatedGaussian_gt_and_le hρ_abs.le d (-d),
      measureReal_correlatedGaussian_gt_and_le hρ_abs.le (-d) d]
    have hsymm : (correlatedGaussian ρ).real {p | p.1 ≤ -d ∧ p.2 ≤ d} =
        (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
      rw [← gaussianQuadrant_cdf_cdf, ← gaussianQuadrant_cdf_cdf, gaussianQuadrant_comm hρ_abs.le]
    have hcdf : Φ d = 1 - Φ (-d) := by linarith [cdf_gaussianReal_neg (v := 1) one_ne_zero d]
    rw [hsymm, hcdf]
    ring
  have hPhi_hi : Φ (-d) ≤ 240030599 / 500000000 := by
    rw [show -d = (-1 / 20 : ℝ) by dsimp [d]; norm_num]
    exact cdf_neg_one_div_twenty_le
  have hf_lo : (27725729 / 62500000 : ℝ) ≤
      (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} := by
    rw [show -d = (-1 / 20 : ℝ) by dsimp [d]; norm_num]
    exact two_seven_seven_le_correlatedGaussian_shift
  have hsup_pos : 0 < shiftedSupply ρ d := by
    have hfle : (correlatedGaussian ρ).real {p | p.1 ≤ d ∧ p.2 ≤ -d} ≤ Φ (-d) := by
      have hsnd : (correlatedGaussian ρ).real {p | p.2 ≤ -d} = Φ (-d) := by
        have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_snd
          (measurableSet_Iic (a := -d))
        rw [correlatedGaussian_map_snd hρ_abs.le, ← cdf_eq_real] at h
        exact h.symm
      exact (measureReal_mono fun _ hp => And.right hp).trans_eq hsnd
    linarith [hsup_eq, hPhi_hi]
  have hneg_eq : Φ (-1 / 20) = Φ (-d) := by congr 1; dsimp [d]; norm_num
  rw [hneg_eq, show (4217 / 1000 : ℝ) = 1 + 3217 / 1000 by norm_num, add_lt_add_iff_left,
    lt_div_iff₀ (mul_pos two_pos hsup_pos)]
  linarith [hsup_eq, hPhi_hi, hf_lo]

/-- Continuity of `ρ ↦ shiftedSupply ρ d` at every `ρ₀ ∈ (-1, 1)`. -/
private theorem continuousAt_shiftedSupply {ρ₀ : ℝ} (hρ₀ : |ρ₀| < 1) (d : ℝ) :
    ContinuousAt (fun ρ => shiftedSupply ρ d) ρ₀ := by
  have hquad (a b : ℝ) : ContinuousAt
      (fun ρ => (correlatedGaussian ρ).real {p | a < p.1 ∧ p.2 ≤ b}) ρ₀ := by
    have hev : (fun ρ => (correlatedGaussian ρ).real {p | a < p.1 ∧ p.2 ≤ b}) =ᶠ[nhds ρ₀]
        fun ρ => Φ b - ∫ x in Iic a, φ x * Φ ((b - ρ * x) / √(1 - ρ ^ 2)) := by
      have hopen : IsOpen {ρ : ℝ | |ρ| < 1} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hρ₀] with ρ hρ
      have hlt : |ρ| < 1 := hρ
      rw [measureReal_correlatedGaussian_gt_and_le hlt.le,
        measureReal_correlatedGaussian_setOf_le_and_le hlt]
    refine ContinuousAt.congr ?_ hev.symm
    refine continuousAt_const.sub ?_
    have hs0 : 1 - ρ₀ ^ 2 ≠ 0 := (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ρ₀).mpr hρ₀)).ne'
    refine MeasureTheory.continuousAt_of_dominated (bound := fun x => φ x) ?_ ?_
      (integrable_gaussianPDFReal 0 1).integrableOn ?_
    · filter_upwards with ρ
      exact ((continuous_gaussianPDFReal 0 1).mul
        ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
          ((continuous_const.sub (continuous_const.mul continuous_id)).div_const _))
        ).aestronglyMeasurable
    · filter_upwards with ρ
      refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x),
        abs_of_nonneg (cdf_nonneg _ _)]
      exact mul_le_of_le_one_right (gaussianPDFReal_nonneg 0 1 x) (cdf_le_one _ _)
    · refine ae_of_all _ fun x => ?_
      refine ContinuousAt.mul continuousAt_const ?_
      refine (continuous_cdf_gaussianReal 0 one_ne_zero).continuousAt.comp ?_
      exact (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).div
        ((continuousAt_const.sub (continuousAt_id.pow 2)).sqrt)
        (sqrt_ne_zero'.mpr (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ρ₀).mpr hρ₀)))
  unfold shiftedSupply
  exact (hquad d (-d)).add ((hquad (-d) d).const_mul (1 / 2))

end DirectedShift

/-! ### Part 6: Unconditional `(4217 / 1000 - ε) N` lower bounds for linear maps -/

/-- **Unconditional shifted `VertexGaussian` lower bound (`4.2170 N`) for totally regular linear
maps.** For every `ε > 0` and all large `N`, every fan-in-two circuit with linear capacity over any
field and any basis that computes `x ↦ M x` for a totally regular `N × N` matrix `M` has `s` inner
gates with `s > (4217 / 1000 - ε) N`. Constants are free. -/
theorem eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (4217 / 1000 - ε) * N < c.innerSize := by
  set d₀ : ℝ := 1 / 20
  set ρStar : ℝ := 2 * √2 / 3
  set q₀ : ℝ := cdf (gaussianReal 0 1) (-d₀)
  have hq₀_pos : 0 < q₀ :=
    cdf_pos (gaussianReal_absolutelyContinuous' 0 one_ne_zero) (-d₀)
  have hρStar_lt : |ρStar| < 1 := by
    have hs2 : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
    rw [abs_of_pos (by dsimp [ρStar]; positivity)]
    dsimp [ρStar]; linarith
  have hstrict := DirectedShift.four_two_one_seven_lt_shifted_coeff
  -- Choose `ρ ∈ (0, ρStar)` and `δ > 0` by continuity of `(q₀ - 2 * δ) / (2 * shiftedSupply ρ d₀)`:
  set fStar := DirectedShift.shiftedSupply ρStar d₀
  have hfStar_pos : 0 < fStar := (DirectedShift.shiftedSupply_nonneg _ _).lt_of_ne fun h0 => by
    rw [show fStar = 0 from h0.symm, mul_zero, div_zero, add_zero] at hstrict
    norm_num at hstrict
  -- Continuous function `(ρ, δ) ↦ 1 + (q₀ - 2 * δ) / (2 * DirectedShift.shiftedSupply ρ d₀)`:
  have hcont_L : ContinuousAt
      (fun p : ℝ × ℝ => 1 + (q₀ - 2 * p.2) / (2 * DirectedShift.shiftedSupply p.1 d₀))
      (ρStar, 0) := by
    refine continuousAt_const.add (ContinuousAt.div ?_ ?_ (by positivity))
    · exact continuousAt_const.sub (continuousAt_const.mul continuousAt_snd)
    · exact continuousAt_const.mul (ContinuousAt.comp
        (g := fun ρ => DirectedShift.shiftedSupply ρ d₀) (f := Prod.fst)
        (DirectedShift.continuousAt_shiftedSupply hρStar_lt d₀) continuousAt_fst)
  have hval_0 : 1 + (q₀ - 2 * (0 : ℝ)) / (2 * fStar) = 1 + q₀ / (2 * fStar) := by ring
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.mp hcont_L
    (min (ε / 2) ((1 + q₀ / (2 * fStar) - 4217 / 1000) / 2))
    (lt_min (half_pos hε) (by linarith [hstrict]))
  have hρStar_pos : 0 < ρStar := by dsimp [ρStar]; positivity
  set ρ := ρStar - min η ρStar / 2
  set δ := min (η / 2) (q₀ / 4)
  have hδ_pos : 0 < δ := lt_min (half_pos hη) (by positivity)
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith [min_le_right η ρStar]
  have hρ_lt_star : ρ < ρStar := by dsimp [ρ]; linarith [lt_min hη hρStar_pos]
  have hρ1 : ρ ≤ 1 := hρ_lt_star.le.trans (abs_lt.mp hρStar_lt).2.le
  have hdist : dist (ρ, δ) (ρStar, (0 : ℝ)) < η := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq, show ρ - ρStar = -(min η ρStar / 2) by dsimp [ρ]; ring, abs_neg,
        abs_of_pos (half_pos (lt_min hη hρStar_pos))]
      linarith [min_le_left η ρStar]
    · rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
      linarith [min_le_left (η / 2) (q₀ / 4)]
  have hL_close := hball hdist
  rw [Real.dist_eq, hval_0] at hL_close
  have hL_gt : 4217 / 1000 < 1 + (q₀ - 2 * δ) / (2 * DirectedShift.shiftedSupply ρ d₀) := by
    linarith [(abs_sub_lt_iff.mp hL_close).2,
      min_le_right (ε / 2) ((1 + q₀ / (2 * fStar) - 4217 / 1000) / 2)]
  have hfρ_pos : 0 < DirectedShift.shiftedSupply ρ d₀ :=
    (DirectedShift.shiftedSupply_nonneg _ _).lt_of_ne fun h0 => by
      rw [← h0, mul_zero, div_zero, add_zero] at hL_gt
      norm_num at hL_gt
  -- Obtain kernel decay `q_k ≥ 0` and radius `R` for `ρ < vertexCorrelation 3 = 2√2 / 3`:
  have hvcorr : Gaussian.vertexCorrelation 3 = ρStar := by
    unfold Gaussian.vertexCorrelation ρStar
    norm_num
  obtain ⟨qk, R, hqk0, hρ_kern⟩ :=
    Gaussian.exists_decay_radius_degree (d := 3) (by norm_num) (hvcorr.symm ▸ hρ_lt_star)
  norm_num at hρ_kern
  set D_ov : ℕ := Gaussian.vertexOverlap 3 R
  -- Choose `N` large enough for `28 ≤ N`, `20 * D_ov / δ ^ 2 < N`, and `2 < ε * N`:
  filter_upwards [eventually_ge_atTop 28,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (20 * (D_ov : ℝ) / δ ^ 2),
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε).eventually_gt_atTop (2 : ℝ)]
    with N hN28 hN_ov hN_eps
  intro F _ σ I M c hM hfan hc hcap
  -- If `5 * N < c.innerSize`, we win immediately since `4.217 - ε < 5`:
  rcases lt_or_ge (5 * N) c.innerSize with hs_big | hs_le
  · have : ((5 * N : ℕ) : ℝ) < c.innerSize := by exact_mod_cast hs_big
    push_cast at this
    linarith [mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) N), Nat.cast_nonneg (α := ℝ) N]
  -- Otherwise `c.innerSize ≤ 5 * N` and `28 ≤ N`: take a saturated budget-3 compression!
  classical
  have hNpos : 0 < N := by omega
  have hconn := Compiler.connected_of_isTotallyRegular hNpos hM hc
  have hdegG := Compiler.maxDegreeLE (by norm_num : 2 ≤ 2) hfan
  obtain ⟨cmp, hsat⟩ := Multigraph.Compression.exists_saturated hdegG
  have hsmall := Compiler.three_mul_log_card_vertex_lt hfan hs_le hN28
  have htwo := Compiler.one_lt_card_blocks_of_lt hNpos hM hc hcap cmp hsmall
  set Q := cmp.quotient
  have := Fintype.ofFinite cmp.blocks
  have := Fintype.ofFinite cmp.external
  have hQloop : Q.Loopless := cmp.quotient_loopless
  have hQ3 : ∀ B, (Q.incidenceSet B).ncard = 3 := hsat.ncard_incidenceSet_quotient hconn htwo
  have hQdeg : Q.MaxDegreeLE 3 := fun B => (hQ3 B).le
  -- Bound `h = |cmp.blocks| ≤ 2 * (c.innerSize - N + 1)`:
  have hrank := Compiler.cycleRank_add_ncard_read_le I (fun _ => univ) hfan hconn
  rw [Compiler.read_eq_univ_of_isTotallyRegular hM hc, ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hrank
  have hh_le_rank := hsat.card_blocks_le hconn htwo
  set h : ℝ := (Fintype.card cmp.blocks : ℝ)
  have hh_le_N : h ≤ 9 * N := by
    have : Fintype.card cmp.blocks ≤ 9 * N := by rw [← Nat.card_eq_fintype_card]; omega
    change (Fintype.card cmp.blocks : ℝ) ≤ 9 * N
    exact_mod_cast this
  have hE_card : (Fintype.card cmp.external : ℝ) = 3 / 2 * h :=
    DirectedShift.card_edges_eq_of_cubic hQloop hQ3
  -- Apply second-moment concentration simultaneously to `inCut`, unread inputs, and held outputs!
  set P := Measure.pi fun _ : cmp.blocks => gaussianReal 0 1
  set c_dev : ℝ := δ * N
  have hc_dev_pos : 0 < c_dev := mul_pos hδ_pos (by exact_mod_cast hNpos)
  let thr : cmp.blocks → ℝ := fun B => if 0 < Q.divergence B then d₀ else -d₀
  let A_in : cmp.external → Set (cmp.blocks → ℝ) := fun e =>
    {ω | e ∈ Q.inCut (DirectedShift.shiftedCut Q (Gaussian.vertexScore Q qk R ω) d₀)}
  -- Input site block map and output block map:
  let bin : Fin N → cmp.blocks := fun i =>
    cmp.blockOf (.signal ⟨.input i, (Compiler.exists_reachable_of_isTotallyRegular hM hc i i).1⟩)
  let bout : Fin N → cmp.blocks := fun o => cmp.blockOf (.output o)
  let B_unread : Fin N → Set (cmp.blocks → ℝ) := fun i =>
    Gaussian.vertexEvent Q qk R (fun x => thr (bin i) < x) (bin i)
  let C_out : Fin N → Set (cmp.blocks → ℝ) := fun o =>
    Gaussian.vertexEvent Q qk R (fun x => x ≤ thr (bout o)) (bout o)
  -- Measurability and locality of `A_in`:
  have hm_Ain (e : cmp.external) : MeasurableSet (A_in e) :=
    (Gaussian.measurableSet_vertexEvent qk R measurableSet_Iic (Q.src e)).compl.inter
      (Gaussian.measurableSet_vertexEvent qk R measurableSet_Iic (Q.tgt e))
  have hdep_Ain (e : cmp.external) :
      DependsOn (· ∈ A_in e) (Gaussian.closedBall Q.toSimpleGraph (Q.src e) (R + 1)) := by
    intro ω ω' hω
    have hsub : Gaussian.closedBall Q.toSimpleGraph (Q.src e) R ⊆
        Gaussian.closedBall Q.toSimpleGraph (Q.src e) (R + 1) :=
      fun _ (hz : Q.toSimpleGraph.edist _ _ ≤ R) =>
        (show Q.toSimpleGraph.edist _ _ ≤ ((R + 1 : ℕ) : ℕ∞) from
          hz.trans (by exact_mod_cast Nat.le_succ R))
    simp only [A_in, DirectedShift.shiftedCut, Multigraph.mem_inCut, mem_ofPred_eq,
      Gaussian.vertexScore_congr fun z hz => hω z (hsub hz),
      Gaussian.vertexScore_congr fun z hz => hω z (Gaussian.closedBall_tgt_subset e R hz)]
  have hdev_A : P.real (Gaussian.deviation A_in c_dev) ≤
      (3 / 2 * h) * D_ov / c_dev ^ 2 := by
    have hd := Gaussian.measureReal_deviation_le hm_Ain
      (fun e => Gaussian.closedBall Q.toSimpleGraph (Q.src e) (R + 1)) hdep_Ain
      (fun e => Gaussian.card_not_disjoint_closedBall_src_le hQdeg R e) hc_dev_pos
    rwa [hE_card] at hd
  -- Multiplicity `≤ 3` of `bin` and `bout` in every block `B`:
  have hmult (B : cmp.blocks) (S : Finset (Fin N)) (T : Set (Fin N))
      (hT : T.ncard ≤ (Q.edgeCut {B}).ncard) (hST : ↑S ⊆ T) : S.card ≤ 3 := by
    rw [← ncard_coe_finset]
    exact (ncard_le_ncard hST (toFinite _)).trans
      (hT.trans ((Q.edgeCut_singleton hQloop B).symm ▸ (hQ3 B).le))
  have hbin_mult (B : cmp.blocks) : (Finset.univ.filter fun i : Fin N => bin i = B).card ≤ 3 :=
    hmult B _ _ ((Compiler.ncard_readIn_block_le_outCut hM hc hcap cmp hsmall B).trans
        (ncard_le_ncard fun e he => (Q.edgeCut_eq_inCut_union_outCut {B}) ▸ Or.inr he))
      fun i hi => ⟨_, cmp.mem_iff_blockOf_eq.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2,
        Compiler.site_of_reach _⟩
  have hbout_mult (B : cmp.blocks) : (Finset.univ.filter fun o : Fin N => bout o = B).card ≤ 3 :=
    hmult B _ _ ((Compiler.ncard_outputs_block_le_inCut hM hc hcap cmp hsmall B).trans
        (ncard_le_ncard fun e he => (Q.edgeCut_eq_inCut_union_outCut {B}) ▸ Or.inl he))
      fun o ho => cmp.mem_iff_blockOf_eq.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ho)).2
  have hdev_term (blk : Fin N → cmp.blocks)
      (hmult : ∀ B : cmp.blocks, (Finset.univ.filter fun i : Fin N => blk i = B).card ≤ 3)
      (pred : cmp.blocks → ℝ → Prop) (hmp : ∀ B, MeasurableSet {x | pred B x}) :
      P.real (Gaussian.deviation (fun i => Gaussian.vertexEvent Q qk R (pred (blk i)) (blk i))
          c_dev) ≤
        (N : ℝ) * ((3 * D_ov : ℕ) : ℝ) / c_dev ^ 2 := by
    have hov (i : Fin N) :
        (Finset.univ.filter fun j : Fin N =>
          ¬Disjoint (Gaussian.closedBall Q.toSimpleGraph (blk i) (R + 1))
            (Gaussian.closedBall Q.toSimpleGraph (blk j) (R + 1))).card ≤ 3 * D_ov := by
      refine (Finset.card_le_mul_card_image_of_maps_to (f := blk)
        (t := Finset.univ.filter fun w : cmp.blocks =>
          ¬Disjoint (Gaussian.closedBall Q.toSimpleGraph (blk i) (R + 1))
            (Gaussian.closedBall Q.toSimpleGraph w (R + 1)))
        (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
        3 fun B _ => ?_).trans
        (Nat.mul_le_mul_left 3 (Gaussian.card_not_disjoint_closedBall_le hQdeg (by norm_num) R _))
      exact (Finset.card_le_card fun j hj =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩).trans (hmult B)
    have hd := Gaussian.measureReal_deviation_le
      (fun i => Gaussian.measurableSet_vertexEvent qk R (hmp (blk i)) (blk i))
      (fun i => Gaussian.closedBall Q.toSimpleGraph (blk i) (R + 1))
      (fun i => Gaussian.dependsOn_vertexEvent qk R (pred (blk i)) (blk i))
      hov hc_dev_pos
    rwa [Fintype.card_fin] at hd
  have hdev_B : P.real (Gaussian.deviation B_unread c_dev) ≤
      (N : ℝ) * ((3 * D_ov : ℕ) : ℝ) / c_dev ^ 2 :=
    hdev_term bin hbin_mult (fun B x => thr B < x) fun _ => measurableSet_Ioi
  have hdev_C : P.real (Gaussian.deviation C_out c_dev) ≤
      (N : ℝ) * ((3 * D_ov : ℕ) : ℝ) / c_dev ^ 2 :=
    hdev_term bout hbout_mult (fun B x => x ≤ thr B) fun _ => measurableSet_Iic
  -- Union bound `< 1` gives a good sample `ω₀`:
  obtain ⟨ω₀, hω⟩ := exists_notMem_of_measureReal_lt_one (((measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add hdev_A hdev_B)) hdev_C)).trans_lt
    (by
      calc _ ≤ 20 * (D_ov : ℝ) * N / c_dev ^ 2 := by
            rw [← add_div, ← add_div]
            gcongr
            push_cast
            nlinarith only [hh_le_N, (Nat.cast_nonneg D_ov : (0 : ℝ) ≤ D_ov)]
        _ < 1 := Gaussian.mul_div_mul_sq_lt_one hδ_pos.ne' (Nat.cast_pos.mpr hNpos) hN_ov))
  simp only [mem_union, not_or] at hω
  obtain ⟨⟨hωA, hωB⟩, hωC⟩ := hω
  set T₀ := DirectedShift.shiftedCut Q (Gaussian.vertexScore Q qk R ω₀) d₀
  -- Upper bound on `|Q.inCut T₀|` from `hωA` and the 4-type cubic LP:
  have hin_upper : ((Q.inCut T₀).ncard : ℝ) <
      DirectedShift.shiftedSupply ρ d₀ * h + c_dev := by
    have h1 := Gaussian.ncard_lt_of_notMem_deviation hωA
    have hmean := DirectedShift.sum_measureReal_inCut_vertexScore_le (d := d₀) Q hQloop hQ3 hqk0 R
      hρ0.le hρ1 hρ_kern (by dsimp [d₀]; norm_num)
    have heq_set : {e | ω₀ ∈ A_in e} = Q.inCut T₀ := rfl
    rw [heq_set] at h1
    linarith
  -- Lower bounds on `N - |X(T₀)|` and `|Y(T₀)|` from `hωB` and `hωC`:
  have hmarginal_cdf (B : cmp.blocks) (t : ℝ) :
      P.real (Gaussian.vertexEvent Q qk R (· ≤ t) B) = cdf (gaussianReal 0 1) t := by
    have hu : ‖Gaussian.unitKernelRow Q.toSimpleGraph qk R B‖ = 1 :=
      Gaussian.norm_unitKernelRow qk R B
    have hu0 : (fun z => Gaussian.unitKernelRow Q.toSimpleGraph qk R B z) ≠ 0 := fun h0 => by
      have : Gaussian.unitKernelRow Q.toSimpleGraph qk R B = 0 := by ext z; exact congrFun h0 z
      simp [this] at hu
    have hdot : Gaussian.vertexEvent Q qk R (· ≤ t) B =
        {ω | (fun z => Gaussian.unitKernelRow Q.toSimpleGraph qk R B z) ⬝ᵥ ω ≤ t} := by
      ext ω
      simp only [Gaussian.vertexEvent, Gaussian.vertexScore, mem_ofPred_eq, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, dotProduct, mul_comm]
    have hnorm1 : √((fun z => Gaussian.unitKernelRow Q.toSimpleGraph qk R B z) ⬝ᵥ
        (fun z => Gaussian.unitKernelRow Q.toSimpleGraph qk R B z)) = 1 := by
      rw [sqrt_dotProduct_self_eq_norm]; exact hu
    rw [hdot, measureReal_pi_gaussianReal_setOf_dotProduct_le hu0, hnorm1, div_one]
  have hmono : cdf (gaussianReal 0 1) (-d₀) ≤ cdf (gaussianReal 0 1) d₀ :=
    monotone_cdf _ (by norm_num [d₀])
  have hB_mean : (N : ℝ) * q₀ ≤ ∑ i : Fin N, P.real (B_unread i) := by
    refine le_of_eq_of_le (by simp) (Finset.sum_le_sum (f := fun _ => q₀) fun i _ => ?_)
    have hcompl : B_unread i = (Gaussian.vertexEvent Q qk R (· ≤ thr (bin i)) (bin i))ᶜ := by
      ext ω; simp [B_unread, Gaussian.vertexEvent]
    rw [hcompl, probReal_compl_eq_one_sub
        (Gaussian.measurableSet_vertexEvent qk R measurableSet_Iic _), hmarginal_cdf]
    dsimp [thr, q₀]
    split_ifs <;> linarith [cdf_gaussianReal_neg (v := 1) one_ne_zero d₀]
  have hC_mean : (N : ℝ) * q₀ ≤ ∑ o : Fin N, P.real (C_out o) := by
    refine le_of_eq_of_le (by simp) (Finset.sum_le_sum (f := fun _ => q₀) fun o _ => ?_)
    rw [hmarginal_cdf]
    dsimp [thr, q₀]
    split_ifs <;> linarith
  have hB_lower : (N : ℝ) * q₀ - c_dev <
      ((N - ((Compiler.network c I fun _ => univ).readIn (cmp.blockOf ⁻¹' T₀)).ncard : ℕ) : ℝ) := by
    have hnot : ¬c_dev ≤ |∑ i, (B_unread i).indicator 1 ω₀ - ∑ i, P.real (B_unread i)| := hωB
    have hlt := neg_lt_of_abs_lt (not_le.mp hnot)
    rw [← ncard_eq_sum_indicator] at hlt
    -- Every `i` with `ω₀ ∈ B_unread i` lies outside `readIn (cmp.blockOf ⁻¹' T₀)`:
    have hsub : {i : Fin N | ω₀ ∈ B_unread i} ⊆
        ((Compiler.network c I fun _ => univ).readIn (cmp.blockOf ⁻¹' T₀))ᶜ := by
      rintro i hi ⟨v, hvT, hsite⟩
      obtain ⟨hi', rfl⟩ := Compiler.site_eq_some hsite
      have hgt : thr (bin i) < Gaussian.vertexScore Q qk R ω₀ (bin i) := hi
      exact not_le.mpr hgt (hvT : bin i ∈ T₀)
    have hc2 := ncard_add_ncard_compl
      ((Compiler.network c I fun _ => univ).readIn (cmp.blockOf ⁻¹' T₀))
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hc2
    have hleR : ({i : Fin N | ω₀ ∈ B_unread i}.ncard : ℝ) ≤
        ((N - ((Compiler.network c I fun _ => univ).readIn (cmp.blockOf ⁻¹' T₀)).ncard : ℕ) : ℝ) :=
      Nat.cast_le.mpr (by have := ncard_le_ncard hsub (toFinite _); omega)
    linarith [hlt, hB_mean, hleR]
  have hC_lower : (N : ℝ) * q₀ - c_dev <
      ({o : Fin N | Compiler.Vertex.output o ∈ cmp.blockOf ⁻¹' T₀}.ncard : ℝ) := by
    have hnot : ¬c_dev ≤ |∑ o, (C_out o).indicator 1 ω₀ - ∑ o, P.real (C_out o)| := hωC
    have hlt := neg_lt_of_abs_lt (not_le.mp hnot)
    rw [← ncard_eq_sum_indicator] at hlt
    change _ < ({o : Fin N | ω₀ ∈ C_out o}.ncard : ℝ)
    linarith [hlt, hC_mean]
  -- Combine demand and supply on `T₀`:
  have hdem_nat := Compiler.min_le_ncard_inCut_quotient hM hc hcap cmp T₀
  have hdem_real : (N : ℝ) * q₀ - c_dev < ((Q.inCut T₀).ncard : ℝ) :=
    (lt_min hB_lower hC_lower).trans_le (by exact_mod_cast hdem_nat)
  have hineq : (N : ℝ) * (q₀ - 2 * δ) < DirectedShift.shiftedSupply ρ d₀ * h := by
    dsimp [c_dev] at hdem_real hin_upper
    linarith [hdem_real, hin_upper]
  have hh_bound : h ≤ 2 * ((c.innerSize : ℝ) - N + 1) := by
    have : Fintype.card cmp.blocks + 2 * N ≤ 2 * c.innerSize + 2 := by
      rw [← Nat.card_eq_fintype_card]; omega
    have hR : (Fintype.card cmp.blocks : ℝ) + 2 * N ≤ 2 * c.innerSize + 2 := by exact_mod_cast this
    linarith
  have hs_lower : (q₀ - 2 * δ) / (2 * DirectedShift.shiftedSupply ρ d₀) * N <
      c.innerSize - N + 1 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (mul_pos two_pos hfρ_pos)]
    linarith [mul_le_mul_of_nonneg_left hh_bound hfρ_pos.le]
  have hstep1 : (4217 / 1000 : ℝ) * N ≤
      (1 + (q₀ - 2 * δ) / (2 * DirectedShift.shiftedSupply ρ d₀)) * N := by gcongr
  linarith [hstep1, hs_lower, hN_eps]

/-- **Shifted `VertexGaussian` lower bound (`4.2170 N`) over finite fields**, for every fan-in-two
basis. -/
theorem eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular_finite {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (4217 / 1000 - ε) * N < c.innerSize := by
  filter_upwards [eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular.{u, v} hε]
    with N hN F _ _ σ I M c hM hfan hc
  exact hN F σ I M c hM hfan hc (c.linearCapacity_of_finite I)

/-- **Shifted `VertexGaussian` lower bound (`4.2170 N`) over the affine basis**, over every
field. -/
theorem eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular_affine {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin N) (Fin N) F)
      (c : Circuit (affineSignature F) N N), M.IsTotallyRegular → c.FanInAtMost 2 →
        c.Computes (affineInterpretation F) (fun x => M *ᵥ x) →
          (4217 / 1000 - ε) * N < c.innerSize := by
  filter_upwards [eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular.{u, u} hε]
    with N hN F _ M c hM hfan hc
  exact hN F _ _ M c hM hfan hc c.linearCapacity_affine

/-- **Shifted `VertexGaussian` lower bound (`4.2170 N`) over infinite fields**, for every basis of
polynomial operations. -/
theorem eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular_isPolynomial {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), I.IsPolynomial → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), M.IsTotallyRegular → c.FanInAtMost 2 →
          c.Computes I (fun x => M *ᵥ x) → (4217 / 1000 - ε) * N < c.innerSize := by
  filter_upwards [eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular_affine.{u} hε]
    with N hN F _ _ σ I hI M c hM hfan hc
  obtain ⟨c', -, hinner, hfan', -, hc'⟩ := hc.exists_affine hI
  rw [← hinner]
  exact hN F M c' hM ((hfan' 2).mpr hfan) hc'

/-- **Arithmetic circuits for Cauchy maps (`4.2170 N` via shifted `VertexGaussian`).** Over every
field of characteristic zero, every arithmetic circuit computing `x ↦ cauchyNat F N *ᵥ x` uses
more than `(4217 / 1000 - ε) N` additions and multiplications, for all large `N`. -/
theorem eventually_4217_div_1000_sub_mul_lt_innerSize_arith_cauchyNat {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [CharZero F] (c : Circuit (arithSignature F) N N),
      c.Computes (arithInterpretation F) (fun x => cauchyNat F N *ᵥ x) →
        (4217 / 1000 - ε) * N < c.innerSize := by
  filter_upwards
    [eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular_isPolynomial.{u, u} hε]
    with N hN F _ _ c hc
  exact hN F _ _ isPolynomial_arithInterpretation _ c (isTotallyRegular_cauchyNat N)
    c.fanInAtMost_two_arith hc

/-- **Prime-field Cauchy maps (`4.2170 N` via shifted `VertexGaussian`).** For all large `N` and
every prime `q ≥ 2 N`, every fan-in-two circuit over `ZMod q` computing
`x ↦ cauchyNat (ZMod q) N *ᵥ x` has more than `(4217 / 1000 - ε) N` inner gates. -/
theorem eventually_4217_div_1000_sub_mul_lt_innerSize_cauchyNat_zmod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q → ∀ (σ : Signature.{v})
      (I : Interpretation σ (ZMod q)) (c : Circuit σ N N), c.FanInAtMost 2 →
        c.Computes I (fun x => cauchyNat (ZMod q) N *ᵥ x) →
          (4217 / 1000 - ε) * N < c.innerSize := by
  filter_upwards
    [eventually_4217_div_1000_sub_mul_lt_innerSize_of_isTotallyRegular_finite.{0, v} hε]
    with N hN q _ hq σ I c hfan hc
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  exact hN (ZMod q) σ I _ c (isTotallyRegular_cauchyNat_zmod hq) hfan hc

end Cslib.Circuits.Frontier

