/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.ReplaceRow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# Gap amplification for inaccessible entropy via parallel repetition

Given a deterministic function $f_0 : \alpha \to \beta$ on a finite uniform domain $\alpha$, its
$t$-fold direct product $f_0^t : (\mathrm{Fin}\;t \to \alpha) \to (\mathrm{Fin}\;t \to \beta)$
(`repHashFin t f₀`) multiplies preimage fiber sizes across coordinates, turning `realSampleEntropy`
and $\log_2 |L_0^t(z)|$ (`repAccessibleSet t L₀`) into sums of $t$ independent bounded coordinate
scores. Following `[HHRVW2020]`, Section 5.1.1, Lemma 5.3 (pp. 26–27):

1. **Real-entropy concentration** (`repHashFin_realSampleEntropy_le_prob`, Lemma 5.3(i), p. 26):
   by Hoeffding's lower-tail bound (`PMF.pi_sum_le_mean_sub`), `realSampleEntropy (repHashFin t f₀)`
   falls below $t \cdot H(X \mid f_0(X)) - \Delta$ with probability at most
   $\exp(-2 \Delta^2 / (t B^2))$ whenever $\log_2 |\alpha| \le B$.
2. **Accessible-set concentration** (`repAccessibleSet_logb_card_ge_prob`, Lemma 5.3(ii),
   Equation (5.1), p. 27): by Hoeffding's upper-tail bound (`PMF.pi_sum_ge_mean_add`),
   $\log_2 |L_0^t(z)|$ exceeds $t \cdot \mathbb{E}[\log_2 |L_0(X)|] + \Delta$ with probability at
   most $\exp(-2 \Delta^2 / (t B^2))$.
3. **Planted-coordinate escape reduction** (`repEscapeInverter`, `isPPT_repEscapeInverter`,
   `repEscape_le_dyadicSize_mul_escape`, Lemma 5.3(ii), pp. 26–27): planting a single challenge
   input at a uniformly sampled dyadic index (`ProbComp.sampleDyadicIndex`) via
   `BitString.replaceRow` (`BitString.uniformList_replaceRow`) reduces escaping $L_0^t$ to escaping
   $L_0$ with concrete multiplicative loss `dyadicSize (t n) ≤ 2 * (t n + 1)`.

## Main definitions

* `Cslib.Crypto.repHashFin`, `Cslib.Crypto.repAccessibleSet`: finite $t$-fold direct product and
  product accessible preimage sets.
* `Cslib.Crypto.repEvalWord`, `Cslib.Crypto.repBitAccessibleSet`: word-level evaluator and flat
  `BitString (t * inLen₀)` accessible sets via `BitString.blocksEquiv`.
* `Cslib.Crypto.repEscapeInverter`: uniform strict-PPT planted-coordinate escape reduction.

## Main results

* `Cslib.Crypto.realSampleEntropy_repHashFin`, `Cslib.Crypto.logb_card_repAccessibleSet`:
  additivity of real sample entropy and accessible log-cardinality across coordinates.
* `Cslib.Crypto.repHashFin_realSampleEntropy_le_prob`,
  `Cslib.Crypto.repAccessibleSet_logb_card_ge_prob`: Hoeffding concentration bounds for Lemma 5.3.
* `Cslib.Crypto.computableInPolyTime_repEvalWord`: plain polynomial-time certificate for
  `repEvalWord`.
* `Cslib.Crypto.isPPT_repEscapeInverter`: plain uniform strict-PPT certificate for
  `repEscapeInverter`.
* `Cslib.Crypto.repEscape_le_dyadicSize_mul_escape`: concrete finite-$n$ reduction from $t$-fold
  accessible escape to single-coordinate accessible escape.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 5.1.1, Lemma 5.3, pp. 26–27][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Finite $t$-fold direct product and product accessible sets -/

/-- Finite $t$-fold direct product $f_0^t(z)_i = f_0(z_i)$ (`[HHRVW2020]`, Section 5.1.1,
Lemma 5.3, p. 26). -/
@[expose] def repHashFin (t : ℕ) {α β : Type*} (f₀ : α → β) (z : Fin t → α) : Fin t → β :=
  fun i => f₀ (z i)

/-- Product accessible set $L_0^t(z) = \prod_{i < t} L_0(z_i)$ (`[HHRVW2020]`, Section 5.1.1,
p. 27). -/
@[expose] def repAccessibleSet (t : ℕ) {α : Type*} (L₀ : α → Finset α)
    (z : Fin t → α) : Finset (Fin t → α) :=
  Fintype.piFinset fun i => L₀ (z i)

@[simp] theorem mem_repAccessibleSet {t : ℕ} {α : Type*}
    (L₀ : α → Finset α) (z z' : Fin t → α) :
    z' ∈ repAccessibleSet t L₀ z ↔ ∀ i, z' i ∈ L₀ (z i) :=
  Fintype.mem_piFinset

theorem self_mem_repAccessibleSet {t : ℕ} {α : Type*} {L₀ : α → Finset α}
    (hself : ∀ x, x ∈ L₀ x) (z : Fin t → α) :
    z ∈ repAccessibleSet t L₀ z :=
  Fintype.mem_piFinset.mpr fun i => hself (z i)

theorem fiberSet_repHashFin (t : ℕ) {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ : α → β) (y : Fin t → β) :
    fiberSet (repHashFin t f₀) y = Fintype.piFinset fun i => fiberSet f₀ (y i) := by
  ext x
  simp only [mem_fiberSet, repHashFin, Fintype.mem_piFinset, funext_iff]

theorem repAccessibleSet_subset_fiber {t : ℕ} {α β : Type*} [Fintype α]
    [DecidableEq β] {f₀ : α → β} {L₀ : α → Finset α}
    (hsub : ∀ x, L₀ x ⊆ fiberSet f₀ (f₀ x)) (z : Fin t → α) :
    repAccessibleSet t L₀ z ⊆ fiberSet (repHashFin t f₀) (repHashFin t f₀ z) := fun _ hz' => by
  simpa only [fiberSet_repHashFin, Fintype.mem_piFinset, repHashFin] using
    fun i => hsub (z i) ((mem_repAccessibleSet L₀ z _).mp hz' i)

theorem card_fiberSet_repHashFin (t : ℕ) {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ : α → β) (y : Fin t → β) :
    #(fiberSet (repHashFin t f₀) y) = ∏ i : Fin t, #(fiberSet f₀ (y i)) := by
  classical
  rw [fiberSet_repHashFin, Fintype.card_piFinset]

theorem card_repAccessibleSet (t : ℕ) {α : Type*} (L₀ : α → Finset α)
    (z : Fin t → α) :
    #(repAccessibleSet t L₀ z) = ∏ i : Fin t, #(L₀ (z i)) :=
  Fintype.card_piFinset _

/-- Real sample entropy is additive across independent coordinates of `repHashFin`. -/
theorem realSampleEntropy_repHashFin (t : ℕ) {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ : α → β) (z : Fin t → α) :
    realSampleEntropy (repHashFin t f₀) z = ∑ i : Fin t, realSampleEntropy f₀ (z i) := by
  simp only [realSampleEntropy, card_fiberSet_repHashFin, repHashFin, Nat.cast_prod, Real.logb]
  rw [Real.log_prod (fun i _ => by exact_mod_cast (card_fiberSet_pos f₀ (z i)).ne'), sum_div]

/-- Accessible log-cardinality is additive across coordinates when every $L_0(x)$ is nonempty. -/
theorem logb_card_repAccessibleSet (t : ℕ) {α : Type*} {L₀ : α → Finset α}
    (hne : ∀ x, (L₀ x).Nonempty) (z : Fin t → α) :
    Real.logb 2 #(repAccessibleSet t L₀ z) = ∑ i : Fin t, Real.logb 2 #(L₀ (z i)) := by
  simp only [card_repAccessibleSet, Nat.cast_prod, Real.logb]
  rw [Real.log_prod (fun i _ => by exact_mod_cast (card_pos.mpr (hne (z i))).ne'), sum_div]

/-! ### Hoeffding concentration bounds (Lemma 5.3(i)–(ii)) -/

/-- **`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(i) (p. 26)**: under uniform sampling on
$\mathrm{Fin}\;t \to \alpha$, `realSampleEntropy (repHashFin t f₀)` falls below
$t \cdot H(X \mid f_0(X)) - \Delta$ with probability at most $\exp(-2 \Delta^2 / (t B^2))$. -/
theorem repHashFin_realSampleEntropy_le_prob (t : ℕ) {α β : Type*}
    [Fintype α] [Nonempty α] [Finite β] [DecidableEq β] (f₀ : α → β)
    {B Δ : ℝ} (hB_nonneg : 0 ≤ B) (hB : Real.logb 2 (Fintype.card α) ≤ B) (hΔ : 0 ≤ Δ) :
    ((PMF.uniformOfFintype (Fin t → α)).toOuterMeasure
      {z | realSampleEntropy (repHashFin t f₀) z ≤
        t * PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (f₀ x, x)) - Δ}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * B ^ 2)) := by
  have hconc := PMF.pi_sum_le_mean_sub (fun _ : Fin t => PMF.uniformOfFintype α)
    (fun _ (x : α) => realSampleEntropy f₀ x) hB_nonneg
    (fun _ x _ => ⟨realSampleEntropy_nonneg f₀ x, (realSampleEntropy_le_log_card f₀ x).trans hB⟩) hΔ
  simpa only [PMF.pi_uniformOfFintype, Fintype.card_fin, realSampleEntropy_repHashFin,
    expected_realSampleEntropy_eq_conditionalEntropy f₀, sum_const, card_univ, nsmul_eq_mul]
    using hconc

/-- **`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(ii), Equation (5.1) (p. 27)**: when
$x \in L_0(x) \subseteq \alpha$ for all $x$, $\log_2 |L_0^t(z)|$ exceeds
$t \cdot \mathbb{E}[\log_2 |L_0(X)|] + \Delta$ with probability at most
$\exp(-2 \Delta^2 / (t B^2))$. -/
theorem repAccessibleSet_logb_card_ge_prob (t : ℕ) {α : Type*}
    [Fintype α] [Nonempty α] (L₀ : α → Finset α)
    (hself : ∀ x, x ∈ L₀ x)
    {B Δ : ℝ} (hB_nonneg : 0 ≤ B) (hB : Real.logb 2 (Fintype.card α) ≤ B) (hΔ : 0 ≤ Δ) :
    ((PMF.uniformOfFintype (Fin t → α)).toOuterMeasure
      {z | t * accessibleSetExpectation L₀ + Δ ≤ Real.logb 2 #(repAccessibleSet t L₀ z)}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * B ^ 2)) := by
  have hne (x : α) : (L₀ x).Nonempty := ⟨x, hself x⟩
  have hconc := PMF.pi_sum_ge_mean_add (fun _ : Fin t => PMF.uniformOfFintype α)
    (fun _ (x : α) => Real.logb 2 #(L₀ x)) hB_nonneg
    (fun _ x _ => ⟨Real.logb_nonneg (by norm_num) (by exact_mod_cast card_pos.mpr (hne x)),
      (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast card_pos.mpr (hne x))
        (by exact_mod_cast card_le_univ (L₀ x))).trans hB⟩) hΔ
  simpa only [PMF.pi_uniformOfFintype, Fintype.card_fin, logb_card_repAccessibleSet t hne,
    accessibleSetExpectation, sum_const, card_univ, nsmul_eq_mul] using hconc

/-! ### Word-level evaluator and flat `BitString` bridge -/

/-- Word-level evaluator of the $t$-fold parallel repetition: slice `w` into `t` rows of width
`inLen₀`, evaluate `evalWord₀` on each row, and concatenate the outputs. -/
@[expose] def repEvalWord (t inLen₀ : ℕ) (evalWord₀ : List Bool → List Bool)
    (w : List Bool) : List Bool :=
  (List.range t).flatMap fun i => evalWord₀ (Cslib.BitString.listRow inLen₀ i w)

/-- Plain polynomial-time certificate for `repEvalWord` when `t`, `inLen₀`, and `n` are supplied in
unary. -/
@[fun_prop]
theorem computableInPolyTime_repEvalWord {α : Type} {encode : α ↪ List Bool}
    {t inLen₀ n : α → ℕ} {evalWord₀ : ℕ → List Bool → List Bool} {w : α → List Bool}
    (ht : ComputableInPolyTime t encode encUnary)
    (hin₀ : ComputableInPolyTime inLen₀ encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (heval₀ : ComputableInPolyTime (fun p : ℕ × List Bool => evalWord₀ p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hw : ComputableInPolyTime w encode encBits) :
    ComputableInPolyTime
      (fun a => repEvalWord (t a) (inLen₀ a) (evalWord₀ (n a)) (w a))
      encode encBits := by
  unfold repEvalWord
  have hfst := ComputableInPolyTime.fst encode encUnary
  exact ComputableInPolyTime.flatMapToBitsWithInput (ComputableInPolyTime.unary_range' ht)
    (heval₀.comp ((hn.comp hfst).prod (ComputableInPolyTime.bitsRowWithInput (hin₀.comp hfst)
      (ComputableInPolyTime.snd encode encUnary) (hw.comp hfst))))

theorem length_repEvalWord {t inLen₀ outLen₀ : ℕ} {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀) (w : List Bool) :
    (repEvalWord t inLen₀ evalWord₀ w).length = t * outLen₀ := by
  have hrow (i : ℕ) : (evalWord₀ (Cslib.BitString.listRow inLen₀ i w)).length = outLen₀ :=
    hlen _ (Cslib.BitString.length_listRow inLen₀ i w)
  simp [repEvalWord, List.length_flatMap, hrow]

theorem listRow_repEvalWord {t inLen₀ outLen₀ : ℕ} {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀) (w : List Bool)
    {j : ℕ} (hj : j < t) :
    Cslib.BitString.listRow outLen₀ j (repEvalWord t inLen₀ evalWord₀ w) =
      evalWord₀ (Cslib.BitString.listRow inLen₀ j w) := by
  have h := Cslib.BitString.listRow_flatMap_append (width := outLen₀)
    (fun i => evalWord₀ (Cslib.BitString.listRow inLen₀ i w)) (List.range t)
    (fun i _ => hlen _ (Cslib.BitString.length_listRow inLen₀ i w)) [] j (by simpa using hj)
  simpa [repEvalWord] using h

private theorem blocksEquiv_ofList {t w : ℕ} (u : List Bool) (i : Fin t) :
    Cslib.BitString.blocksEquiv (Cslib.BitString.ofList (t * w) u) i =
      Cslib.BitString.ofList w (Cslib.BitString.listRow w i.val u) := by
  rw [Cslib.BitString.listRow_eq_ofFn w i u, Cslib.BitString.ofList_ofFn,
    Cslib.BitString.blocksEquiv_apply]

/-- Exact agreement between `wordToFinMap` of `repEvalWord` and `repHashFin` conjugated by
`BitString.blocksEquiv`. -/
theorem wordToFinMap_repEvalWord {t inLen₀ outLen₀ : ℕ} {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    (z : BitString (t * inLen₀)) :
    wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀) z =
      Cslib.BitString.blocksEquiv.symm
        (repHashFin t (wordToFinMap inLen₀ outLen₀ evalWord₀)
          (Cslib.BitString.blocksEquiv z)) := by
  apply Cslib.BitString.blocksEquiv.injective
  ext i : 1
  rw [Equiv.apply_symm_apply, wordToFinMap, blocksEquiv_ofList,
    listRow_repEvalWord hlen _ i.isLt, Cslib.BitString.listRow_eq_ofFn inLen₀ i (List.ofFn z),
    Cslib.BitString.ofList_ofFn, ← Cslib.BitString.blocksEquiv_apply]
  rfl

/-- Flat `BitString (t * inLen₀)` view of `repAccessibleSet t L₀`. -/
@[expose] def repBitAccessibleSet (t inLen₀ : ℕ)
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (z : BitString (t * inLen₀)) : Finset (BitString (t * inLen₀)) :=
  (repAccessibleSet t L₀ (Cslib.BitString.blocksEquiv z)).map
    Cslib.BitString.blocksEquiv.symm.toEmbedding

@[simp] theorem mem_repBitAccessibleSet {t inLen₀ : ℕ}
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (z z' : BitString (t * inLen₀)) :
    z' ∈ repBitAccessibleSet t inLen₀ L₀ z ↔
      ∀ i : Fin t, Cslib.BitString.blocksEquiv z' i ∈ L₀ (Cslib.BitString.blocksEquiv z i) := by
  rw [repBitAccessibleSet, mem_map_equiv]
  simp only [Equiv.symm_symm, mem_repAccessibleSet]

@[simp] theorem card_repBitAccessibleSet (t inLen₀ : ℕ)
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (z : BitString (t * inLen₀)) :
    #(repBitAccessibleSet t inLen₀ L₀ z) =
      #(repAccessibleSet t L₀ (Cslib.BitString.blocksEquiv z)) :=
  card_map _

theorem self_mem_repBitAccessibleSet {t inLen₀ : ℕ}
    {L₀ : BitString inLen₀ → Finset (BitString inLen₀)}
    (hself : ∀ x, x ∈ L₀ x) (z : BitString (t * inLen₀)) :
    z ∈ repBitAccessibleSet t inLen₀ L₀ z :=
  (mem_repBitAccessibleSet L₀ z z).mpr fun _ => hself _

theorem repBitAccessibleSet_subset_fiber {t inLen₀ outLen₀ : ℕ}
    {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    {L₀ : BitString inLen₀ → Finset (BitString inLen₀)}
    (hsub : ∀ x, L₀ x ⊆ fiberSet (wordToFinMap inLen₀ outLen₀ evalWord₀)
      (wordToFinMap inLen₀ outLen₀ evalWord₀ x))
    (z : BitString (t * inLen₀)) :
    repBitAccessibleSet t inLen₀ L₀ z ⊆
      fiberSet (wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀))
        (wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀) z) := by
  intro z' hz'
  rw [mem_fiberSet, wordToFinMap_repEvalWord hlen, wordToFinMap_repEvalWord hlen]
  congr 1 with i : 1
  dsimp only [repHashFin]
  exact (mem_fiberSet _ _ _).mp (hsub _ ((mem_repBitAccessibleSet L₀ z z').mp hz' i))

theorem realSampleEntropy_wordToFinMap_repEvalWord {t inLen₀ outLen₀ : ℕ}
    {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    (z : BitString (t * inLen₀)) :
    realSampleEntropy
        (wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀)) z =
      realSampleEntropy
        (repHashFin t (wordToFinMap inLen₀ outLen₀ evalWord₀))
        (Cslib.BitString.blocksEquiv z) := by
  let f₀ := wordToFinMap inLen₀ outLen₀ evalWord₀
  let f₁ := wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀)
  have hfib : fiberSet f₁ (f₁ z) =
      (fiberSet (repHashFin t f₀) (repHashFin t f₀ (Cslib.BitString.blocksEquiv z))).map
        Cslib.BitString.blocksEquiv.symm.toEmbedding := by
    ext z'
    simp only [mem_fiberSet, mem_map_equiv, Equiv.symm_symm, f₁, f₀,
      wordToFinMap_repEvalWord hlen, EmbeddingLike.apply_eq_iff_eq]
  simp only [realSampleEntropy, f₁, f₀, hfib, card_map]

/-- Flat `BitString` lower-tail Hoeffding bound for `repEvalWord` (`[HHRVW2020]`, Lemma 5.3(i),
p. 26). -/
theorem repEvalWord_realSampleEntropy_le_prob {t inLen₀ outLen₀ : ℕ}
    {evalWord₀ : List Bool → List Bool}
    (hlen : ∀ u, u.length = inLen₀ → (evalWord₀ u).length = outLen₀)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    let f₀ := wordToFinMap inLen₀ outLen₀ evalWord₀
    let f₁ := wordToFinMap (t * inLen₀) (t * outLen₀) (repEvalWord t inLen₀ evalWord₀)
    ((PMF.uniformOfFintype (BitString (t * inLen₀))).toOuterMeasure
      {z | realSampleEntropy f₁ z ≤
        t * PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString inLen₀)).map fun x =>
          (f₀ x, x)) - Δ}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * (inLen₀ : ℝ) ^ 2)) := by
  intro f₀ f₁
  simpa only [← PMF.uniformOfFintype_map_equiv Cslib.BitString.blocksEquiv,
    PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, f₁, f₀,
    realSampleEntropy_wordToFinMap_repEvalWord hlen] using
    repHashFin_realSampleEntropy_le_prob t f₀ (Nat.cast_nonneg inLen₀) (by simp [Real.logb_pow]) hΔ

/-- Flat `BitString` upper-tail Hoeffding bound for `repBitAccessibleSet` (`[HHRVW2020]`,
Lemma 5.3(ii), Equation (5.1), p. 27). -/
theorem repBitAccessibleSet_logb_card_ge_prob (t inLen₀ : ℕ)
    (L₀ : BitString inLen₀ → Finset (BitString inLen₀))
    (hself : ∀ x, x ∈ L₀ x) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ((PMF.uniformOfFintype (BitString (t * inLen₀))).toOuterMeasure
      {z | t * accessibleSetExpectation L₀ + Δ ≤
        Real.logb 2 #(repBitAccessibleSet t inLen₀ L₀ z)}).toReal ≤
      Real.exp (-2 * Δ ^ 2 / (t * (inLen₀ : ℝ) ^ 2)) := by
  simpa only [← PMF.uniformOfFintype_map_equiv Cslib.BitString.blocksEquiv,
    PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, card_repBitAccessibleSet] using
    repAccessibleSet_logb_card_ge_prob t L₀ hself (Nat.cast_nonneg _) (by simp [Real.logb_pow]) hΔ

/-! ### Planted-coordinate escape reduction (Lemma 5.3(ii)) -/

/-- Planted-coordinate escape reduction (`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(ii), pp. 26–27):
sample an exact dyadic index `idx < dyadicSize (t n)`, plant the single-coordinate challenge
`xWord.take (inLen₀ n)` into row `idx` of a uniform `(t n * inLen₀ n)`-bit dummy word, run `A`,
and extract row `idx` of `A`'s output. -/
@[expose] noncomputable def repEscapeInverter (t inLen₀ : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (xWord : List Bool) :
    ProbComp (List Bool) := do
  let idx ← ProbComp.sampleDyadicIndex (t n)
  let dummy ← Cslib.BitString.sampleList (t n * inLen₀ n)
  let zWord := Cslib.BitString.replaceRow (inLen₀ n) (t n) idx (xWord.take (inLen₀ n)) dummy
  let raw ← A n zWord
  return Cslib.BitString.listRow (inLen₀ n) idx raw

/-- Plain uniform strict-PPT certificate for `repEscapeInverter`. -/
theorem isPPT_repEscapeInverter {t inLen₀ : ℕ → ℕ}
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hin₀ : ComputableInPolyTime inLen₀ encUnary encUnary)
    (hA : IsPPT encBits A) :
    IsPPT encBits (repEscapeInverter t inLen₀ A) := by
  apply IsPPTOn.isPPT
  refine (isPPTOn_sampleDyadicIndex (by fun_prop)).bind_with ?_
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  have hp := ComputableInPolyTime.id'
    (encIn := encPair (encPair (encPair encUnary encBits) encUnary) encBits)
  have hn := hp.fst'.fst'.fst'
  have hidx := hp.fst'.snd'
  have hin := hin₀.comp hn
  have hzWord := ComputableInPolyTime.bitsReplaceRowWithInput hin (ht.comp hn) hidx
    (ComputableInPolyTime.bitsTakeWithInput hp.fst'.fst'.snd' hin) hp.snd'
  simpa only [bind_pure_comp, Function.comp_def] using
    (hA.preprocess hn hzWord).map_with
      (ComputableInPolyTime.bitsRowWithInput (hin.comp (.fst _ encBits))
        (hidx.comp (.fst _ encBits)) (ComputableInPolyTime.snd _ encBits))

/-- **`[HHRVW2020]`, Section 5.1.1, Lemma 5.3(ii) (pp. 26–27)**: for any adversary `A`, escaping
`repBitAccessibleSet (t n)` in `accessibleEscapeGame` occurs with probability at most
`dyadicSize (t n)` times the single-coordinate escape probability of
`repEscapeInverter t inLen₀ A`. -/
theorem repEscape_le_dyadicSize_mul_escape (t inLen₀ outLen₀ : ℕ → ℕ)
    (evalWord₀ : ℕ → List Bool → List Bool)
    (L₀ : (n : ℕ) → BitString (inLen₀ n) → Finset (BitString (inLen₀ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ u : List Bool, u.length = inLen₀ n → (evalWord₀ n u).length = outLen₀ n) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame
        (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
        (fun k => t k * inLen₀ k)
        (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)) : ℝ) ≤
      (dyadicSize (t n) : ℝ) *
        (Game.succProbability (ProbComp.eval
          (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)) : ℝ) := by
  classical
  let w₀ := inLen₀ n
  let rCount := t n
  let repPred (zWord raw : List Bool) : Prop :=
    raw.length = rCount * w₀ ∧
      repEvalWord rCount w₀ (evalWord₀ n) raw = repEvalWord rCount w₀ (evalWord₀ n) zWord ∧
      Cslib.BitString.ofList (rCount * w₀) raw ∉
        repBitAccessibleSet rCount w₀ (L₀ n) (Cslib.BitString.ofList (rCount * w₀) zWord)
  let cellPred (xWord xRaw : List Bool) : Prop :=
    xRaw.length = w₀ ∧ evalWord₀ n xRaw = evalWord₀ n xWord ∧
      Cslib.BitString.ofList w₀ xRaw ∉ L₀ n (Cslib.BitString.ofList w₀ xWord)
  let rowPred (idx : ℕ) (zWord raw : List Bool) : Prop :=
    cellPred (Cslib.BitString.listRow w₀ idx zWord) (Cslib.BitString.listRow w₀ idx raw)
  let idxGame (idx : ℕ) : PMF Bool :=
    (Cslib.BitString.uniformList w₀).bind fun xWord =>
      (Cslib.BitString.uniformList (rCount * w₀)).bind fun dummy =>
        let zWord := Cslib.BitString.replaceRow w₀ rCount idx (xWord.take w₀) dummy
        (ProbComp.eval (A n zWord)).map fun raw =>
          decide (cellPred xWord (Cslib.BitString.listRow w₀ idx raw))
  have hrow_witness (zWord raw : List Bool) (hesc : repPred zWord raw) :
      ∃ j : Fin rCount, rowPred j.val zWord raw := by
    rcases hesc with ⟨_, heval_raw, hnot_acc⟩
    obtain ⟨j, hj_not⟩ := not_forall.mp (mt (mem_repBitAccessibleSet _ _ _).mpr hnot_acc)
    refine ⟨j, Cslib.BitString.length_listRow w₀ j.val raw, ?_, ?_⟩
    · rw [← listRow_repEvalWord hlen raw j.isLt, ← listRow_repEvalWord hlen zWord j.isLt,
        heval_raw]
    · rwa [blocksEquiv_ofList, blocksEquiv_ofList] at hj_not
  let μ : PMF (List Bool × List Bool) :=
    (Cslib.BitString.uniformList (rCount * w₀)).bind fun zWord =>
      (ProbComp.eval (A n zWord)).map fun raw => (zWord, raw)
  have hj_eq (j : Fin rCount) :
      μ.map (fun p => decide (rowPred j.val p.1 p.2)) = idxGame j.val := by
    simp only [μ, idxGame, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    conv_lhs => rw [← Cslib.BitString.uniformList_replaceRow w₀ rCount j, PMF.bind_bind]
    refine PMF.bind_congr_on_support _ _ _ fun xWord hx => ?_
    have hx_len := Cslib.BitString.length_of_mem_support_uniformList hx
    rw [PMF.bind_map, List.take_of_length_le hx_len.le]
    refine PMF.bind_congr_on_support _ _ _ fun dummy _ => ?_
    simp only [Function.comp_def, rowPred,
      Cslib.BitString.listRow_replaceRow hx_len dummy j.isLt, ↓reduceIte]
  let lhsGame := ProbComp.eval
    (accessibleEscapeGame
      (fun k => repEvalWord (t k) (inLen₀ k) (evalWord₀ k))
      (fun k => t k * inLen₀ k)
      (fun k => repBitAccessibleSet (t k) (inLen₀ k) (L₀ k)) A n)
  let rhsGame := ProbComp.eval
    (accessibleEscapeGame evalWord₀ inLen₀ L₀ (repEscapeInverter t inLen₀ A) n)
  have hlhs_eq : lhsGame = μ.map (fun p => decide (repPred p.1 p.2)) := by
    simp only [lhsGame, accessibleEscapeGame, μ, repPred, rCount, w₀, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_pure, PMF.map,
      PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  have hrhs_eq : rhsGame =
      (PMF.uniformOfFintype (Fin (dyadicSize rCount))).bind fun k => idxGame k.val := by
    simp only [rhsGame, accessibleEscapeGame, repEscapeInverter, idxGame, cellPred, rCount, w₀,
      ProbComp.eval_bind, Cslib.BitString.eval_sampleList, ProbComp.eval_sampleDyadicIndex,
      ProbComp.eval_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    rw [PMF.bind_comm]
  have hle_ennreal : lhsGame true ≤ (dyadicSize rCount : ℝ≥0∞) * rhsGame true := calc
    lhsGame true
      ≤ ∑ j ∈ range rCount, (μ.map (fun p => decide (rowPred j p.1 p.2))) true := by
        rw [hlhs_eq]
        refine (PMF.map_true_mono μ (F := fun p => (List.range rCount).any
          (fun j => decide (rowPred j p.1 p.2))) fun p _ h => ?_).trans
          (PMF.map_any_range_true_le_sum μ rCount fun j p => decide (rowPred j p.1 p.2))
        obtain ⟨j, hj⟩ := hrow_witness p.1 p.2 (of_decide_eq_true h)
        exact List.any_eq_true.mpr ⟨j.val, List.mem_range.mpr j.isLt, decide_eq_true hj⟩
    _ = ∑ j ∈ range rCount, idxGame j true := by
        simp_rw [← Fin.sum_univ_eq_sum_range, hj_eq]
    _ ≤ ∑ k ∈ range (dyadicSize rCount), idxGame k true :=
        sum_le_sum_of_subset (range_mono (lt_dyadicSize rCount).le)
    _ = (dyadicSize rCount : ℝ≥0∞) * rhsGame true := by
        rw [hrhs_eq, PMF.bind_apply, tsum_fintype]
        simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
        rw [← mul_sum, ← mul_assoc,
          ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (dyadicSize_pos rCount).ne')
            (ENNReal.natCast_ne_top _),
          one_mul, Fin.sum_univ_eq_sum_range (fun k => idxGame k true)]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_mul,
    ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (PMF.apply_ne_top _ _))
      hle_ennreal

end Cslib.Crypto
