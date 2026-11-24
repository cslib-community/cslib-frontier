/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Errors
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Accounting of the certificate procedure (Lemma 3.1)

The accounting of §3.6 of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (pp. 22–24) for
the program `Cslib.Query.Certificate.certificate`: the comparisons it makes outside its exact
minimum spanning forest calls, and the total size of those calls. With the correctness results
of `Cslib.Query.Certificate.card_unsupported_add_sum_absorbed_le` (Lemma 3.7), this proves their
Lemma 3.1 (§3.1, p. 12) for any schedule and estimator satisfying two hypotheses, which M7b's
`Cslib.Query.Certificate.card_errors_le` and `Cslib.Query.Certificate.sum_countQueries_estimator_le`
discharge for the paper's schedule (Lemma 3.11) and estimator (§3.5),
`Cslib.Query.Certificate.Config.derandomized`:

* (i) `Cslib.Query.Certificate.ErrorBound`: every call `c` has at most
  `A t_c² √(m_c n_c) + 4 m_c / t_c` edges with an error (§3.6, p. 23);
* (ii) `Cslib.Query.Certificate.EstCostBound`: the estimator of every call `c` with an edge makes
  at most `B (t_c² n_c + t_c² √(m_c n_c))` comparisons (§3.5, p. 22).

Here `n_c`, `m_c`, `d_c` are the vertices, edges and level of the call and `t_c = γ d_c³`. All
results are steps in the proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325).

## Comparisons (pp. 23–24)

`Cslib.Query.Certificate.countQueries_certificate` and
`Cslib.Query.Certificate.countQueries_roundStep` decompose the comparisons of a call into those
of its rounds: the estimator (`Cslib.Query.Certificate.estCost`), the child call, the exact call
of line 19 and, at the end of a block, the batch of M6 and the recomputation of the first invalid
levels of the rejected edges.
M6's `Cslib.Query.Certificate.countQueries_batch_le` bounds the batch by `468 |B| + n`, at most
`2 (d - 1)` comparisons for each of at most `r² √(8 n |B|)` successful tests, and `2 (k + 1)` for
the failed test of an edge whose first invalid index is `k`; the recomputation costs another
`2 (k + 1)`.

**Failed tests.** The paper charges the failed test of a rejected edge, `O(ℓ)` for its first
invalid level `ℓ`, to the error the edge has at level `ℓ` (Lemma 3.7). The formal proof does this
by a potential: a call holds `4 (k + 1)` for each edge it rejects, with first invalid index `k`.
An edge rejected by a child and not absorbed keeps its index, so the potential passes up
unchanged; an absorbed edge (an edge of `R''`) has `k + 1 = d`, the level of the call, and is paid
there, `4 d` per edge, against the errors of the call
(`Cslib.Query.Certificate.sum_card_absorbed_le_card_errors`). The root rejects nothing.

## Sums over the recursion (Claim 3.13, p. 23)

Sums over the calls (`Cslib.Query.Certificate.calls`) are bounded by level potentials rather than
by levels: `Cslib.Query.Certificate.sum_calls_le_of_potential` pays a quantity of every call from a
potential `Φ(d) μ` of the root, when the potential of a call pays for the call and for the
potentials of its children. Two masses decay along the recursion:

* the edges, `∑ m_child ≤ m` (`Cslib.Query.Certificate.sum_card_child_edges_le`); with
  `Φ(d) = 2a / (γ d)` this sums `a m_c / t_c` and `a d_c m_c / t_c` to at most `2 a m / γ`
  (`Cslib.Query.Certificate.sum_calls_mul_card_edges_le`). So the error terms `4 m_c / t_c` sum
  to at most `8 m / γ` (the paper's `∑ 4 m_d / (γ d³) ≤ 8 m / γ`), and the failed tests
  `16 d_c m_c / t_c` to `32 m / γ`;
* the mass `n + √(m n)`, which halves (`Cslib.Query.Certificate.sum_mass_child_le`: children
  have at most `n / 4` vertices, and Cauchy–Schwarz); with `Φ(d) = 4 K (3/2)^d` this sums
  `p(d_c) (n_c + √(m_c n_c))` for any `p(d) ≤ K (3/2)^d`, in particular any polynomial in `d`
  (`Cslib.Query.Certificate.sum_calls_mul_mass_le_of_le_three_halves_pow`). This is Claim 3.13.

Each edge enters at most one batch in the whole recursion
(`Cslib.Query.Certificate.sum_calls_sum_card_finds_le`), so the `468 |B|` terms sum to `468 m`.

## Exact calls (p. 24)

`Cslib.Query.Certificate.msfInputs` lists the inputs of the exact calls of a call: `F ∪ F' ∪ R''`
in each round and `F ∪ D` at the end of each block. They are root edges
(`Cslib.Query.Certificate.subset_edges_of_mem_msfInputs`), and by M7a's `card_roundInput_le` and
`card_blockInput_le` a call's inputs have at most `t² (3 + r²) n` edges besides the absorbed
ones.

## Main results

* `Cslib.Query.Certificate.certificate_derandomized_accounting`: **Lemma 3.1** for the
  derandomized configuration, and
  `Cslib.Query.Certificate.countQueries_certificate_derandomized_le`, the form used for
  Theorem 4.1 (§4, pp. 25–26).
* `Cslib.Query.Certificate.certificate_root_accounting`: Lemma 3.1 under (i) and (ii): on a
  root instance with `n ≤ 2 m`, `|F| + |U(F)| + ∑ |E_i| ≤ 8 m / γ + C √(m n)`, the comparisons
  are at most `C' m` plus those of the exact calls, and the exact calls work on root edges.
* `Cslib.Query.Certificate.countQueries_certificate_root_le`: the form used for Theorem 4.1: each
  exact input has at most `8 m / γ + C √(m n)` root edges, and if each exact call costs at most
  `κ` per input edge, the procedure costs at most `C' m + κ (8 m / γ + C √(m n))`.

## Deviations from §3.6

* The bound has `8 m / γ` where the paper has `16 m / γ`: the paper bounds `|U(F)|` and the
  rejected edges by the errors separately, while M7a's counting bounds them together.
* A block costs `n` comparisons and its exact call `(n - 1) + r² n` edges; the formal sums
  charge these to every round rather than to the `t` block ends, which changes only the
  polynomial in `d` of Claim 3.13. Likewise the successful tests are bounded per block by
  `r² √(8 n m)` rather than by Cauchy–Schwarz over the blocks.
* The level polynomials are bounded by `d^25` and then by `K (3/2)^d`, rather than summed level by
  level with `n_d ≤ 4^{-(d-1)} n`.

No step of §3.6 needed repair.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.1, p. 12, and §3.5–3.6, pp. 22–24.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E W : Type} [DecidableEq V] [DecidableEq E]

/-! ### Sums over the calls of the recursion -/

section Sums

variable (cfg : Config V E) (o : {ι : Type} → LEQuery E ι → ι)

/-- A call without vertices has no child call. -/
private theorem calls_eq_singleton_of_vertices_eq_empty {inst : Instance V E}
    (h : inst.vertices = ∅) : calls cfg o inst = [inst] := by
  rw [calls_eq]
  split
  · rfl
  · simp [h]

/-- **Sums over calls by a level potential.** Let `g` be a quantity of a call and `μ` a mass, and
let the potential `Φ d · μ` of a call at level `d` pay for `g` and for the potential
`Φ (d + 1) · μ` of its children. Then it pays for `g` over all the calls of the recursion. -/
theorem sum_calls_le_of_potential {g μ : Instance V E → ℝ} {Φ : ℕ → ℝ}
    (hpos : ∀ c, 0 ≤ Φ c.level * μ c)
    (hleaf : ∀ c, c.edges = ∅ → g c ≤ Φ c.level * μ c)
    (hstep : ∀ c, c.edges ≠ ∅ → g c + Φ (c.level + 1) *
      ∑ i ∈ range (levelT cfg.γ c.level ^ 2), μ (child cfg o c i) ≤ Φ c.level * μ c)
    (inst : Instance V E) :
    ((calls cfg o inst).map g).sum ≤ Φ inst.level * μ inst := by
  induction h : #inst.vertices using Nat.strong_induction_on generalizing inst with
  | _ n ih =>
    subst h
    by_cases hS : inst.edges = ∅
    · rw [calls_eq]
      simpa [hS] using hleaf inst hS
    rcases inst.vertices.eq_empty_or_nonempty with hX | hX
    · rw [calls_eq_singleton_of_vertices_eq_empty cfg o hX]
      have h1 := hstep inst hS
      have h2 : 0 ≤ Φ (inst.level + 1) *
          ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), μ (child cfg o inst i) := by
        rw [mul_sum]
        exact sum_nonneg fun i _ => by simpa using hpos (child cfg o inst i)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      linarith
    · rw [sum_map_calls cfg o g inst hX hS]
      have hch : ∀ i ∈ range (levelT cfg.γ inst.level ^ 2),
          ((calls cfg o (child cfg o inst i)).map g).sum ≤
            Φ (inst.level + 1) * μ (child cfg o inst i) := fun i hi => by
        have := ih _ (card_child_vertices_lt cfg o inst hX (mem_range.1 hi)) _ rfl
        simpa using this
      have := sum_le_sum hch
      rw [← mul_sum] at this
      linarith [hstep inst hS]

/-- Each edge enters at most one child (§3.6, p. 23). -/
theorem sum_card_child_edges_le (inst : Instance V E) :
    ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), #(child cfg o inst i).edges ≤ #inst.edges := by
  rw [← sum_card_finds_add_card_child_edges cfg o inst]
  exact sum_le_sum fun i _ => Nat.le_add_left _ _

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the mass `n + √(m n)`
halves from a call to its children (Claim 3.13, §3.6, p. 23). The children have at most `n / 4`
vertices in total, at most `m` edges in total, and `∑ √(mᵢ nᵢ) ≤ √(∑ mᵢ · ∑ nᵢ)` by Cauchy–Schwarz.
-/
theorem sum_mass_child_le (inst : Instance V E) :
    ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), ((#(child cfg o inst i).vertices : ℝ) +
      √(#(child cfg o inst i).edges * #(child cfg o inst i).vertices)) ≤
    (#inst.vertices + √(#inst.edges * #inst.vertices)) / 2 := by
  set T := range (levelT cfg.γ inst.level ^ 2)
  have hn : 4 * ∑ i ∈ T, (#(child cfg o inst i).vertices : ℝ) ≤ #inst.vertices := by
    exact_mod_cast four_mul_sum_card_child_vertices_le cfg o inst
  have hm : ∑ i ∈ T, (#(child cfg o inst i).edges : ℝ) ≤ #inst.edges := by
    exact_mod_cast sum_card_child_edges_le cfg o inst
  have hcs : ∑ i ∈ T, √((#(child cfg o inst i).edges : ℝ) * #(child cfg o inst i).vertices) ≤
      √(∑ i ∈ T, (#(child cfg o inst i).edges : ℝ)) *
        √(∑ i ∈ T, (#(child cfg o inst i).vertices : ℝ)) := by
    simp_rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sum_sqrt_mul_sqrt_le T (fun _ => Nat.cast_nonneg _) fun _ => Nat.cast_nonneg _
  have hsq : √(∑ i ∈ T, (#(child cfg o inst i).edges : ℝ)) *
      √(∑ i ∈ T, (#(child cfg o inst i).vertices : ℝ)) ≤
      √(#inst.edges * #inst.vertices) / 2 := by
    rw [← Real.sqrt_mul (sum_nonneg fun _ _ => Nat.cast_nonneg _)]
    have h4 : √((#inst.edges : ℝ) * #inst.vertices) / 2 =
        √((#inst.edges : ℝ) * (#inst.vertices / 4)) := by
      rw [mul_div_assoc', Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
    exact Real.sqrt_le_sqrt (mul_le_mul hm (by linarith) (sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Nat.cast_nonneg _))
  rw [sum_add_distrib]
  linarith

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): sums over calls of the
edges against a level weight (Claim 3.13 and "Bounding the number of errors", §3.6, p. 23). If
`q d + Φ (d + 1) ≤ Φ d` at every level, then `∑_c q(d_c) m_c ≤ Φ(d) m`, since each edge enters at
most one child. -/
theorem sum_calls_mul_card_edges_le {q Φ : ℕ → ℝ} (hΦ : ∀ d, 0 ≤ Φ d)
    (hq : ∀ d, 1 ≤ d → q d + Φ (d + 1) ≤ Φ d) (inst : Instance V E) :
    ((calls cfg o inst).map fun c => q c.level * #c.edges).sum ≤ Φ inst.level * #inst.edges := by
  refine sum_calls_le_of_potential cfg o (μ := fun c => (#c.edges : ℝ))
    (fun c => mul_nonneg (hΦ _) (Nat.cast_nonneg _)) (fun c hc => by simp [hc])
    (fun c _ => ?_) inst
  have hm : ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(child cfg o c i).edges : ℝ) ≤ #c.edges := by
    exact_mod_cast sum_card_child_edges_le cfg o c
  have := mul_le_mul_of_nonneg_right (hq c.level c.level.pos) (Nat.cast_nonneg (#c.edges))
  have := mul_le_mul_of_nonneg_left hm (hΦ (c.level + 1))
  linarith

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): sums over calls of the
mass against a level weight (Claim 3.13, §3.6, p. 23). If `p d + Φ (d + 1) / 2 ≤ Φ d` at every
level, then `∑_c p(d_c) (n_c + √(m_c n_c)) ≤ Φ(d) (n + √(m n))`, since the mass halves from a call
to its children (`Cslib.Query.Certificate.sum_mass_child_le`). -/
theorem sum_calls_mul_mass_le {p Φ : ℕ → ℝ} (hΦ : ∀ d, 0 ≤ Φ d)
    (hp : ∀ d, 1 ≤ d → p d + Φ (d + 1) / 2 ≤ Φ d) (inst : Instance V E) :
    ((calls cfg o inst).map fun c =>
        p c.level * (#c.vertices + √(#c.edges * #c.vertices))).sum ≤
      Φ inst.level * (#inst.vertices + √(#inst.edges * #inst.vertices)) := by
  have hμ : ∀ c : Instance V E, (0 : ℝ) ≤ #c.vertices + √(#c.edges * #c.vertices) :=
    fun c => add_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  refine sum_calls_le_of_potential cfg o (μ := fun c => (#c.vertices : ℝ) +
      √(#c.edges * #c.vertices)) (fun c => mul_nonneg (hΦ _) (hμ c)) (fun c _ => ?_)
    (fun c _ => ?_) inst
  · have h1 := hp c.level c.level.pos
    have h2 := hΦ (c.level + 1)
    exact mul_le_mul_of_nonneg_right (by linarith) (hμ c)
  · have hm := mul_le_mul_of_nonneg_left (sum_mass_child_le cfg o c) (hΦ (c.level + 1))
    have := mul_le_mul_of_nonneg_right (hp c.level c.level.pos) (hμ c)
    linarith

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the paper's Claim 3.13
(§3.6, p. 23), in potential form. A level weight `p d ≤ K (3/2)^d` (for instance a polynomial in
`d`) summed against the mass `n_c + √(m_c n_c)` over all calls is at most
`4 K (3/2)^d (n + √(m n))`, for a call at level `d`. -/
theorem sum_calls_mul_mass_le_of_le_three_halves_pow {p : ℕ → ℝ} {K : ℝ}
    (hp : ∀ d, 1 ≤ d → p d ≤ K * (3 / 2) ^ d) (hK : 0 ≤ K) (inst : Instance V E) :
    ((calls cfg o inst).map fun c =>
        p c.level * (#c.vertices + √(#c.edges * #c.vertices))).sum ≤
      4 * K * (3 / 2) ^ (inst.level : ℕ) *
        (#inst.vertices + √(#inst.edges * #inst.vertices)) := by
  refine sum_calls_mul_mass_le cfg o (Φ := fun d => 4 * K * (3 / 2) ^ d) (fun d => by positivity)
    (fun d hd => ?_) inst
  have := hp d hd
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) d]

end Sums

/-- A power of `d` grows slower than `(3/2)^d`. -/
private theorem exists_pow_le_mul_three_halves_pow (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℕ, (d : ℝ) ^ N ≤ K * (3 / 2) ^ d := by
  obtain ⟨K, hK⟩ := (tendsto_pow_const_div_const_pow_of_one_lt N
    (by norm_num : (1 : ℝ) < 3 / 2)).bddAbove_range
  refine ⟨K, le_trans (by positivity) (hK ⟨0, rfl⟩), fun d => ?_⟩
  have := hK ⟨d, rfl⟩
  rwa [div_le_iff₀ (by positivity)] at this

/-! ### The comparisons of a call -/

section Cost

variable (cfg : Config V E) (o : {ι : Type} → LEQuery E ι → ι)

/-- The comparisons of the preference estimator over the rounds of the call on `inst` (line 10;
§3.5, p. 22). -/
noncomputable def estCost (inst : Instance V E) : ℕ :=
  ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
    (cfg.est inst (snapshot cfg o inst i).state (acting cfg inst i)).countQueries o

/-- The inputs of the exact minimum spanning forest calls made by the call on `inst` itself, in
order: in round `i`, the input `F ∪ F' ∪ R''` of line 19 and, when `i` ends a block, the input
`F ∪ D` of line 21. A call without edges makes none (lines 1–2). -/
noncomputable def msfInputs (inst : Instance V E) : List (Finset E) :=
  if inst.edges = ∅ then [] else
    (List.range (levelT cfg.γ inst.level ^ 2)).flatMap fun i =>
      roundInput cfg o inst i :: if (i + 1) % levelT cfg.γ inst.level = 0 then
        [(afterRound cfg o inst i).state.forest ∪ (batchResult cfg o inst i).declared] else []

/-- The comparisons of round `i`: the estimator, the child call, the exact call of line 19 and,
when `i` ends a block, the batch and the recomputation of the first invalid levels. -/
theorem countQueries_roundStep (inst : Instance V E) (i : ℕ) :
    (roundStep cfg (childCall cfg inst) inst i (snapshot cfg o inst i)).countQueries o =
      (cfg.est inst (snapshot cfg o inst i).state (acting cfg inst i)).countQueries o +
      (childCall cfg inst (child cfg o inst i)).countQueries o +
      (cfg.msfSub inst.ends (roundInput cfg o inst i)).countQueries o +
      if (i + 1) % levelT cfg.γ inst.level = 0 then
        (batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
          (levelR cfg.γ inst.level) (afterRound cfg o inst i).state
          (afterRound cfg o inst i).batch).countQueries o +
        (invalidIndices inst (batchResult cfg o inst i).rejected.toList).countQueries o
      else 0 := by
  simp only [roundStep, FreeM.countQueries_bind, FreeM.countQueries_ite, FreeM.countQueries_pure,
    blockEnd, add_assoc]
  rfl

private theorem countQueries_runRounds (inst : Instance V E) (j : ℕ) :
    (runRounds cfg (childCall cfg inst) inst j).countQueries o =
      ∑ i ∈ range j,
        (roundStep cfg (childCall cfg inst) inst i (snapshot cfg o inst i)).countQueries o := by
  induction j with
  | zero => simp [runRounds]
  | succ j ih =>
    rw [sum_range_succ, ← ih]
    simp only [runRounds, FreeM.countQueries_bind]
    rfl

/-- The comparisons of a call with an edge are those of its `t²` rounds. -/
theorem countQueries_certificate (inst : Instance V E) (hS : inst.edges ≠ ∅) :
    (certificate cfg inst).countQueries o = ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
      (roundStep cfg (childCall cfg inst) inst i (snapshot cfg o inst i)).countQueries o := by
  rw [certificate_eq]
  simp only [hS, ↓reduceIte, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero,
    countQueries_runRounds]

/-- A property of instances inherited by the children holds at every call of the recursion. -/
theorem forall_mem_calls {P : Instance V E → Prop}
    (hP : ∀ c, P c → c.edges ≠ ∅ → ∀ i, P (child cfg o c i)) {inst : Instance V E}
    (h : P inst) : ∀ c ∈ calls cfg o inst, P c := by
  induction hn : #inst.vertices using Nat.strong_induction_on generalizing inst with
  | _ n ih =>
    subst hn
    intro c hc
    rw [calls_eq] at hc
    split at hc
    · rw [List.mem_singleton.1 hc]; exact h
    rename_i hS
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hc
    split at hi
    · exact ih _ ‹_› (hP inst h hS i) rfl c hi
    · cases hi

/-- The edges of every call are edges of the root call. -/
theorem edges_subset_of_mem_calls {inst c : Instance V E} (hc : c ∈ calls cfg o inst) :
    c.edges ⊆ inst.edges := by
  refine forall_mem_calls cfg o (P := fun c => c.edges ⊆ inst.edges) (fun c hc _ i => ?_)
    subset_rfl c hc
  refine subset_trans (fun e he => ?_) hc
  rw [edges_child, mem_filter, acting, mem_filter] at he
  exact he.1.1

/-- Every record has one entry of at most two spokes per preceding level, for every edge (not
only the edges of the call, as in `Cslib.Query.Certificate.Instance.WellFormed`): the bound of
M6 on the test cost quantifies over all edges. -/
private def RecordShape (inst : Instance V E) : Prop :=
  ∀ e, (inst.record e).length + 1 = inst.level ∧ ∀ P ∈ inst.record e, #P ≤ 2

omit [DecidableEq V] [DecidableEq E] in
private theorem recordShape_root (X : Finset V) (ends : E → Sym2 V) (S : Finset E) :
    RecordShape (Instance.root X ends S) := fun e => by simp

private theorem recordShape_child {inst : Instance V E} (h : RecordShape inst) (i : ℕ) :
    RecordShape (child cfg o inst i) := fun e => by
  refine ⟨?_, fun P hP => ?_⟩
  · simp only [record_child, List.length_append, List.length_singleton, level_child,
      PNat.add_coe, PNat.one_coe]
    rw [← (h e).1]
  · rw [record_child, List.mem_append, List.mem_singleton] at hP
    rcases hP with hP | rfl
    · exact (h e).2 P hP
    · exact card_spokes_le _ e

end Cost

/-! ### Failed tests -/

section Failed

variable {W : Type} [LinearOrder W] (cfg : Config V E) (w : E → W)

/-- The comparisons charged to an edge rejected in a call: its failed test and the recomputation
of its first invalid level, at most `2 (k + 1)` each when its first invalid index is `k` (p. 24).
-/
private def failCost (inst : Instance V E) (e : E) : ℕ :=
  4 * ((firstInvalid w (inst.record e) e).getD 0 + 1)

variable {cfg w}

/-- An edge absorbed in round `i` (an edge of `R''`) is charged `4 d` in the child, for the level
`d` of the call. -/
private theorem failCost_child_of_mem_absorbed (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) {inst : Instance V E} (hwf : inst.WellFormed) {i : ℕ} {e : E}
    (he : e ∈ absorbed cfg (LEQuery.keyOracle w) inst i) :
    failCost w (child cfg (LEQuery.keyOracle w) inst i) e = 4 * inst.level := by
  have hc := sound_childResult hw hmsf hwf i
  have hr := (mem_filter.1 he).1
  have hinv := hc.firstInvalid_rejected e hr
  have hei := child_edges_subset cfg w inst i (hc.rejected_subset hr)
  rw [(mem_filter.1 he).2, hwf.length_record e hei] at hinv
  rw [failCost, hinv, Option.getD_some, Nat.sub_add_cancel inst.level.pos]

/-- A rejected edge of the child that is not absorbed is charged the same in the call. -/
private theorem failCost_child_of_notMem_absorbed (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) {inst : Instance V E} (hwf : inst.WellFormed) {i : ℕ} {e : E}
    (hr : e ∈ (childResult cfg (LEQuery.keyOracle w) inst i).rejected)
    (he : e ∉ absorbed cfg (LEQuery.keyOracle w) inst i) :
    failCost w (child cfg (LEQuery.keyOracle w) inst i) e = failCost w inst e := by
  have hc := sound_childResult hw hmsf hwf i
  have hinv := hc.firstInvalid_rejected e hr
  rw [record_child] at hinv
  have hk : (childResult cfg (LEQuery.keyOracle w) inst i).invalidAt e ≠ (inst.record e).length :=
    fun h => he (mem_filter.2 ⟨hr, h⟩)
  have := firstInvalid_of_append_eq_some hinv hk
  rw [failCost, failCost, record_child, hinv, this]

/-- **The comparisons at the end of a block** (lines 20–21), by M6's batch accounting with the
test costs of the record scans: `468 |B| + n` comparisons, at most `2 (d - 1)` per successful
test, `failCost` per rejected edge for its failed test and the recomputation of its first invalid
level, and the exact call. -/
private theorem countQueries_blockEnd_le (hw : Function.Injective w) {inst : Instance V E}
    (hrs : RecordShape inst) (i : ℕ) :
    (((batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
          (levelR cfg.γ inst.level) (afterRound cfg (LEQuery.keyOracle w) inst i).state
          (afterRound cfg (LEQuery.keyOracle w) inst i).batch).countQueries
            (LEQuery.keyOracle w) +
        (invalidIndices inst (batchResult cfg (LEQuery.keyOracle w) inst i).rejected.toList
          ).countQueries (LEQuery.keyOracle w) : ℕ) : ℝ) ≤
      468 * #(afterRound cfg (LEQuery.keyOracle w) inst i).batch + #inst.vertices +
        ((2 * ((inst.level : ℕ) - 1) : ℕ) : ℝ) * ((levelR cfg.γ inst.level : ℝ) ^ 2 *
          √(8 * #inst.vertices * #(afterRound cfg (LEQuery.keyOracle w) inst i).batch)) +
        (cfg.msfSub inst.ends ((afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∪
          (batchResult cfg (LEQuery.keyOracle w) inst i).declared)).countQueries
            (LEQuery.keyOracle w) +
        ∑ e ∈ (batchResult cfg (LEQuery.keyOracle w) inst i).rejected, (failCost w inst e : ℝ) := by
  have htest : ∀ e, (admissibilityTest (inst.record e) e).eval (LEQuery.keyOracle w) =
      decide (Admissible w (inst.record e) e) := fun e => eval_admissibilityTest w _ e
  have hcs : ∀ e, Admissible w (inst.record e) e →
      (admissibilityTest (inst.record e) e).countQueries (LEQuery.keyOracle w) ≤
        2 * ((inst.level : ℕ) - 1) :=
    fun e _ => by
      rw [countQueries_admissibilityTest]
      refine (countQueries_findInvalid_le (LEQuery.keyOracle w) e (hrs e).2).trans ?_
      have := (hrs e).1
      omega
  have hfi : ∀ e, ¬Admissible w (inst.record e) e →
      firstInvalid w (inst.record e) e =
        some ((firstInvalid w (inst.record e) e).getD 0) := fun e he => by
    rcases h : firstInvalid w (inst.record e) e with _ | k
    · exact absurd (firstInvalid_eq_none_iff.1 h) he
    · rfl
  have hcf : ∀ e, ¬Admissible w (inst.record e) e →
      (admissibilityTest (inst.record e) e).countQueries (LEQuery.keyOracle w) ≤
        2 * ((firstInvalid w (inst.record e) e).getD 0 + 1) := fun e he => by
    rw [countQueries_admissibilityTest]
    exact countQueries_findInvalid_le_of_eq_some w e (hrs e).2 (hfi e he)
  have hv : (afterRound cfg (LEQuery.keyOracle w) inst i).state.vertices = inst.vertices := by
    simp [afterRound]
  have hb := countQueries_batch_le (msfSub := cfg.msfSub inst.ends) (r := levelR cfg.γ inst.level)
    (st := (afterRound cfg (LEQuery.keyOracle w) inst i).state)
    (B := (afterRound cfg (LEQuery.keyOracle w) inst i).batch) hw htest hcs hcf
  rw [hv] at hb
  set R := (batchResult cfg (LEQuery.keyOracle w) inst i).rejected
  have hinv : ((invalidIndices inst R.toList).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      ∑ e ∈ R, ((2 * ((firstInvalid w (inst.record e) e).getD 0 + 1) : ℕ) : ℝ) := by
    rw [countQueries_invalidIndices, Finset.sum_map_toList]
    push_cast
    refine sum_le_sum fun e he => ?_
    have := countQueries_findInvalid_le_of_eq_some w e (hrs e).2
      (hfi e (not_adm_of_mem_rejected_batch hw htest he))
    exact_mod_cast this
  have hsum : ∑ e ∈ R, ((2 * ((firstInvalid w (inst.record e) e).getD 0 + 1) : ℕ) : ℝ) +
      ∑ e ∈ R, ((2 * ((firstInvalid w (inst.record e) e).getD 0 + 1) : ℕ) : ℝ) =
      ∑ e ∈ R, (failCost w inst e : ℝ) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun e _ => ?_
    simp only [failCost]
    push_cast
    ring
  change _ ≤ _ + _ + _ + ∑ e ∈ R, _ + _ at hb
  push_cast at hb hinv hsum ⊢
  simp only [batchResult] at hb ⊢
  linarith

omit [DecidableEq V] [DecidableEq E] in
private theorem acting_subset_sched_lt (inst : Instance V E) (j : ℕ) :
    acting cfg inst j ⊆ {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j + 1} := fun e he => by
  rw [acting, mem_filter] at he
  rw [mem_filter]
  exact ⟨he.1, by omega⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem disjoint_acting_sched_lt (inst : Instance V E) (j : ℕ) :
    Disjoint (acting cfg inst j) {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j} :=
  disjoint_left.2 fun e he he' => by
    rw [acting, mem_filter] at he
    rw [mem_filter] at he'
    omega

/-- **The failed tests of a call, by a potential on its rejected edges.** Over the first `j`
rounds, the failure costs of the edges rejected by the children and by the batches are the cost
`4 d` of each absorbed edge plus the failure costs of the rejected edges of the call so far:
an edge rejected below and not absorbed keeps its first invalid index. Along the way, the batch
and the rejected edges are disjoint edges that acted before round `j`. -/
private theorem failCost_snapshot (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (j : ℕ) :
    ∑ i ∈ range j, (∑ e ∈ (childResult cfg (LEQuery.keyOracle w) inst i).rejected,
        failCost w (child cfg (LEQuery.keyOracle w) inst i) e +
      if (i + 1) % levelT cfg.γ inst.level = 0 then
        ∑ e ∈ (batchResult cfg (LEQuery.keyOracle w) inst i).rejected, failCost w inst e
      else 0) =
      ∑ i ∈ range j, 4 * inst.level * #(absorbed cfg (LEQuery.keyOracle w) inst i) +
        ∑ e ∈ (snapshot cfg (LEQuery.keyOracle w) inst j).rejected, failCost w inst e ∧
    Disjoint (snapshot cfg (LEQuery.keyOracle w) inst j).batch
      (snapshot cfg (LEQuery.keyOracle w) inst j).rejected ∧
    (snapshot cfg (LEQuery.keyOracle w) inst j).batch ⊆
      {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j} ∧
    (snapshot cfg (LEQuery.keyOracle w) inst j).rejected ⊆
      {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j} := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hEq, hD, hB, hR⟩ := ih
    have hc := sound_childResult hw hmsf hwf j
    have hce : (child cfg (LEQuery.keyOracle w) inst j).edges ⊆ acting cfg inst j := by
      rw [edges_child]; exact filter_subset _ _
    have hRc := hc.rejected_subset.trans hce
    have hfa : finds cfg (LEQuery.keyOracle w) inst j ⊆ acting cfg inst j := filter_subset _ _
    have hfc : Disjoint (finds cfg (LEQuery.keyOracle w) inst j)
        (childResult cfg (LEQuery.keyOracle w) inst j).rejected := by
      refine disjoint_left.2 fun e hf hr => ?_
      have := hc.rejected_subset hr
      rw [edges_child, mem_filter] at this
      rw [finds, mem_filter, this.2] at hf
      cases hf.2
    have hab : absorbed cfg (LEQuery.keyOracle w) inst j ⊆
        (childResult cfg (LEQuery.keyOracle w) inst j).rejected := filter_subset _ _
    have hact := acting_subset_sched_lt (cfg := cfg) inst j
    have hdis := disjoint_acting_sched_lt (cfg := cfg) inst j
    have hmono : {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j} ⊆
        {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j + 1} :=
      fun e he => by
        rw [mem_filter] at he ⊢
        exact ⟨he.1, by omega⟩
    -- the round
    set a := afterRound cfg (LEQuery.keyOracle w) inst j
    set Rc := (childResult cfg (LEQuery.keyOracle w) inst j).rejected
    set A := absorbed cfg (LEQuery.keyOracle w) inst j
    have haB : a.batch = (snapshot cfg (LEQuery.keyOracle w) inst j).batch ∪
        finds cfg (LEQuery.keyOracle w) inst j := rfl
    have haR : a.rejected = (snapshot cfg (LEQuery.keyOracle w) inst j).rejected ∪ (Rc \ A) :=
      rfl
    have hsplit : ∑ e ∈ Rc, failCost w (child cfg (LEQuery.keyOracle w) inst j) e =
        4 * inst.level * #A + ∑ e ∈ Rc \ A, failCost w inst e := by
      rw [← sum_sdiff hab, add_comm]
      congr 1
      · rw [sum_congr rfl fun e he => failCost_child_of_mem_absorbed hw hmsf hwf he, sum_const,
          smul_eq_mul, mul_comm]
      · exact sum_congr rfl fun e he =>
          failCost_child_of_notMem_absorbed hw hmsf hwf (mem_sdiff.1 he).1 (mem_sdiff.1 he).2
    have hdR : Disjoint (snapshot cfg (LEQuery.keyOracle w) inst j).rejected (Rc \ A) :=
      (hdis.mono_left (sdiff_subset.trans hRc)).symm.mono_left hR
    have haRsum : ∑ e ∈ a.rejected, failCost w inst e =
        ∑ e ∈ (snapshot cfg (LEQuery.keyOracle w) inst j).rejected, failCost w inst e +
          ∑ e ∈ Rc \ A, failCost w inst e := by
      rw [haR, sum_union hdR]
    have haD : Disjoint a.batch a.rejected := by
      rw [haB, haR]
      refine disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨hD, ?_⟩,
        disjoint_union_right.2 ⟨?_, hfc.mono_right sdiff_subset⟩⟩
      · exact (hdis.mono_left (sdiff_subset.trans hRc)).symm.mono_left hB
      · exact (hdis.mono_left hfa).mono_right hR
    have haBs : a.batch ⊆ {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j + 1} := by
      rw [haB]; exact union_subset (hB.trans hmono) (hfa.trans hact)
    have haRs : a.rejected ⊆ {e ∈ inst.edges | (cfg.sched inst e : ℕ) < j + 1} := by
      rw [haR]; exact union_subset (hR.trans hmono) ((sdiff_subset.trans hRc).trans hact)
    rw [sum_range_succ, sum_range_succ, hEq, hsplit]
    by_cases hbe : (j + 1) % levelT cfg.γ inst.level = 0
    · have hs1 : (snapshot cfg (LEQuery.keyOracle w) inst (j + 1)).rejected =
          a.rejected ∪ (batchResult cfg (LEQuery.keyOracle w) inst j).rejected ∧
          (snapshot cfg (LEQuery.keyOracle w) inst (j + 1)).batch = ∅ := by
        rw [snapshot_succ]
        simp only [hbe, ↓reduceIte, eval_blockEnd, and_true]
        rfl
      have hrej : (batchResult cfg (LEQuery.keyOracle w) inst j).rejected ⊆ a.batch :=
        rejected_subset_batch hw (fun e => eval_admissibilityTest w _ e)
      simp only [hbe, ↓reduceIte]
      rw [hs1.1, hs1.2, sum_union (haD.mono_left hrej).symm, haRsum]
      refine ⟨by ring, disjoint_empty_left _, empty_subset _, union_subset haRs (hrej.trans haBs)⟩
    · have hs1 : snapshot cfg (LEQuery.keyOracle w) inst (j + 1) = a := by
        rw [snapshot_succ]
        simp only [hbe, ↓reduceIte]
        rfl
      simp only [hbe, ↓reduceIte]
      rw [hs1, haRsum]
      exact ⟨by ring, haD, haBs, haRs⟩

end Failed

/-- **Each edge enters at most one batch** of a call: the batches processed at the ends of the
blocks of the first `j` rounds, and the current batch, have at most as many edges as the rounds
sent to them. -/
private theorem sum_card_batch_le (cfg : Config V E) (o : {ι : Type} → LEQuery E ι → ι)
    (inst : Instance V E) (j : ℕ) :
    ∑ i ∈ range j, (if (i + 1) % levelT cfg.γ inst.level = 0 then
        #(afterRound cfg o inst i).batch else 0) + #(snapshot cfg o inst j).batch ≤
      ∑ i ∈ range j, #(finds cfg o inst i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ha : #(afterRound cfg o inst j).batch ≤
        #(snapshot cfg o inst j).batch + #(finds cfg o inst j) := card_union_le _ _
    rw [sum_range_succ, sum_range_succ]
    by_cases hbe : (j + 1) % levelT cfg.γ inst.level = 0
    · have : (snapshot cfg o inst (j + 1)).batch = ∅ := by
        rw [snapshot_succ]
        simp only [hbe, ↓reduceIte, eval_blockEnd]
      simp only [hbe, ↓reduceIte, this, card_empty]
      omega
    · rw [snapshot_succ]
      simp only [hbe, ↓reduceIte]
      omega

/-! ### The comparisons of the recursion -/

section Recursion

variable (cfg : Config V E) (o : {ι : Type} → LEQuery E ι → ι)

/-- The bound of §3.6 (p. 24) on the comparisons of a call outside its child calls and its exact
minimum spanning forest calls: the estimator; `4 d` for each edge absorbed in a round (its failed
test and the recomputation of its first invalid level, charged to the level where its first
invalid projection was made); and at the end of each block, `468 |B| + n` comparisons and at most
`2 (d - 1)` comparisons for each of at most `r² √(8 n |B|)` successful tests. -/
private noncomputable def outsideBound (c : Instance V E) : ℝ :=
  if c.edges = ∅ then 0 else
    estCost cfg o c + ∑ i ∈ range (levelT cfg.γ c.level ^ 2),
      (((4 * c.level * #(absorbed cfg o c i) : ℕ) : ℝ) +
        if (i + 1) % levelT cfg.γ c.level = 0 then
          468 * #(afterRound cfg o c i).batch + #c.vertices +
            ((2 * ((c.level : ℕ) - 1) : ℕ) : ℝ) * ((levelR cfg.γ c.level : ℝ) ^ 2 *
              √(8 * #c.vertices * #(afterRound cfg o c i).batch))
        else 0)

/-- The comparisons of the exact minimum spanning forest calls made by a call itself. -/
private noncomputable def msfCost (c : Instance V E) : ℝ :=
  ((msfInputs cfg o c).map fun S => ((cfg.msfSub c.ends S).countQueries o : ℝ)).sum

/-- A sum over the exact calls of a call with an edge is a sum over its rounds. -/
theorem sum_map_msfInputs {M : Type*} [AddCommMonoid M] (f : Finset E → M) (c : Instance V E)
    (hS : c.edges ≠ ∅) :
    ((msfInputs cfg o c).map f).sum = ∑ i ∈ range (levelT cfg.γ c.level ^ 2),
      (f (roundInput cfg o c i) +
        if (i + 1) % levelT cfg.γ c.level = 0 then
          f ((afterRound cfg o c i).state.forest ∪ (batchResult cfg o c i).declared)
        else 0) := by
  rw [msfInputs]
  simp only [hS, ↓reduceIte, sum_map_flatMap_range]
  refine sum_congr rfl fun i _ => ?_
  split <;> simp

omit [DecidableEq V] [DecidableEq E] in
private theorem vertices_nonempty_of_mem {inst : Instance V E} (hwf : inst.WellFormed) {e : E}
    (he : e ∈ inst.edges) : inst.vertices.Nonempty := by
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (inst.ends e)
  exact ⟨u, hwf.ends_mem e he u (by rw [← huv]; exact Sym2.mem_mk_left u v)⟩

variable {W : Type} [LinearOrder W] {cfg} {w : E → W}

/-- **The comparisons of a call**, by induction on the recursion: at most the bound outside the
calls and the exact calls, summed over all the calls of the recursion, plus the failure costs of
the edges the call rejects (paid by the call that absorbs them). -/
private theorem countQueries_certificate_le_aux (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) (inst : Instance V E) (hwf : inst.WellFormed)
    (hrs : RecordShape inst) :
    ((certificate cfg inst).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      ((calls cfg (LEQuery.keyOracle w) inst).map fun c =>
        outsideBound cfg (LEQuery.keyOracle w) c + msfCost cfg (LEQuery.keyOracle w) c).sum +
      ∑ e ∈ ((certificate cfg inst).eval (LEQuery.keyOracle w)).rejected,
        (failCost w inst e : ℝ) := by
  induction hn : #inst.vertices using Nat.strong_induction_on generalizing inst with
  | _ n ih =>
    subst hn
    by_cases hS : inst.edges = ∅
    · rw [certificate_eq, calls_eq]
      simp [hS, outsideBound, msfCost, msfInputs]
    obtain ⟨e₀, he₀⟩ := nonempty_iff_ne_empty.2 hS
    have hX := vertices_nonempty_of_mem hwf he₀
    set F : Instance V E → ℝ := fun c =>
      outsideBound cfg (LEQuery.keyOracle w) c + msfCost cfg (LEQuery.keyOracle w) c
    -- one round
    have hround : ∀ i ∈ range (levelT cfg.γ inst.level ^ 2),
        ((roundStep cfg (childCall cfg inst) inst i
            (snapshot cfg (LEQuery.keyOracle w) inst i)).countQueries (LEQuery.keyOracle w) : ℝ) ≤
          (cfg.est inst (snapshot cfg (LEQuery.keyOracle w) inst i).state
            (acting cfg inst i)).countQueries (LEQuery.keyOracle w) +
          (((calls cfg (LEQuery.keyOracle w) (child cfg (LEQuery.keyOracle w) inst i)).map F).sum +
            (((cfg.msfSub inst.ends (roundInput cfg (LEQuery.keyOracle w) inst i)).countQueries
              (LEQuery.keyOracle w) : ℝ) +
            if (i + 1) % levelT cfg.γ inst.level = 0 then
              ((cfg.msfSub inst.ends ((afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∪
                (batchResult cfg (LEQuery.keyOracle w) inst i).declared)).countQueries
                  (LEQuery.keyOracle w) : ℝ) else 0)) +
          (if (i + 1) % levelT cfg.γ inst.level = 0 then
            468 * #(afterRound cfg (LEQuery.keyOracle w) inst i).batch + #inst.vertices +
              ((2 * ((inst.level : ℕ) - 1) : ℕ) : ℝ) * ((levelR cfg.γ inst.level : ℝ) ^ 2 *
                √(8 * #inst.vertices * #(afterRound cfg (LEQuery.keyOracle w) inst i).batch))
            else 0) +
          (((∑ e ∈ (childResult cfg (LEQuery.keyOracle w) inst i).rejected,
              failCost w (child cfg (LEQuery.keyOracle w) inst i) e +
            if (i + 1) % levelT cfg.γ inst.level = 0 then
              ∑ e ∈ (batchResult cfg (LEQuery.keyOracle w) inst i).rejected, failCost w inst e
            else 0 : ℕ) : ℝ)) := fun i hi => by
      have hiT := mem_range.1 hi
      have hlt := card_child_vertices_lt cfg (LEQuery.keyOracle w) inst hX hiT
      have hih := ih _ hlt _ (wellFormed_child hw hmsf hwf i)
        (recordShape_child cfg (LEQuery.keyOracle w) hrs i) rfl
      have hcr : (certificate cfg (child cfg (LEQuery.keyOracle w) inst i)).eval
          (LEQuery.keyOracle w) = childResult cfg (LEQuery.keyOracle w) inst i := by
        rw [childResult, childCall_child cfg (LEQuery.keyOracle w) inst hX hiT]
      rw [hcr] at hih
      rw [countQueries_roundStep, childCall_child cfg (LEQuery.keyOracle w) inst hX hiT]
      have hb := countQueries_blockEnd_le (cfg := cfg) hw hrs i
      push_cast
      by_cases hbe : (i + 1) % levelT cfg.γ inst.level = 0
      · simp only [hbe, ↓reduceIte]
        push_cast at hb
        linarith
      · simp only [hbe, ↓reduceIte]
        linarith
    have hsum := sum_le_sum hround
    have hcost : ((certificate cfg inst).countQueries (LEQuery.keyOracle w) : ℝ) =
        ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), ((roundStep cfg (childCall cfg inst) inst i
          (snapshot cfg (LEQuery.keyOracle w) inst i)).countQueries (LEQuery.keyOracle w) : ℝ) := by
      rw [countQueries_certificate cfg (LEQuery.keyOracle w) inst hS]
      push_cast
      rfl
    rw [← hcost] at hsum
    simp only [sum_add_distrib] at hsum
    have hpot := (failCost_snapshot hw hmsf hwf (levelT cfg.γ inst.level ^ 2)).1
    have hpot' : ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
        (((∑ e ∈ (childResult cfg (LEQuery.keyOracle w) inst i).rejected,
          failCost w (child cfg (LEQuery.keyOracle w) inst i) e +
        if (i + 1) % levelT cfg.γ inst.level = 0 then
          ∑ e ∈ (batchResult cfg (LEQuery.keyOracle w) inst i).rejected, failCost w inst e
        else 0 : ℕ) : ℝ)) =
        ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
          ((4 * inst.level * #(absorbed cfg (LEQuery.keyOracle w) inst i) : ℕ) : ℝ) +
          ∑ e ∈ ((certificate cfg inst).eval (LEQuery.keyOracle w)).rejected,
            (failCost w inst e : ℝ) := by
      rw [eval_certificate]
      simp only [hS, ↓reduceIte]
      exact_mod_cast hpot
    rw [sum_map_calls cfg (LEQuery.keyOracle w) F inst hX hS]
    have hF : F inst = estCost cfg (LEQuery.keyOracle w) inst +
        ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
        (((4 * inst.level * #(absorbed cfg (LEQuery.keyOracle w) inst i) : ℕ) : ℝ) +
          if (i + 1) % levelT cfg.γ inst.level = 0 then
            468 * #(afterRound cfg (LEQuery.keyOracle w) inst i).batch + #inst.vertices +
              ((2 * ((inst.level : ℕ) - 1) : ℕ) : ℝ) * ((levelR cfg.γ inst.level : ℝ) ^ 2 *
                √(8 * #inst.vertices * #(afterRound cfg (LEQuery.keyOracle w) inst i).batch))
          else 0) + msfCost cfg (LEQuery.keyOracle w) inst := by
      simp only [F, outsideBound, hS, ↓reduceIte]
    rw [hF, msfCost, sum_map_msfInputs cfg (LEQuery.keyOracle w) _ inst hS, estCost]
    push_cast
    push_cast at hsum hpot' ⊢
    simp only [sum_add_distrib] at hsum hpot' ⊢
    linarith

/-- Every call of the recursion rooted at a well-formed instance is well formed. -/
theorem wellFormed_of_mem_calls (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    ∀ c ∈ calls cfg (LEQuery.keyOracle w) inst, c.WellFormed :=
  forall_mem_calls cfg _ (fun _ hc _ i => wellFormed_child hw hmsf hc i) hwf

/-- **The absorbed edges of a call have errors in it** (Lemma 3.7, second claim, p. 18), and the
sets `R''` of its rounds are disjoint: `∑_i |R''_i| ≤ |errors|`. -/
theorem sum_card_absorbed_le_card_errors (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), #(absorbed cfg (LEQuery.keyOracle w) inst i) ≤
      #(errors cfg w inst) := by
  rw [← card_biUnion ((pairwiseDisjoint_acting inst _).mono fun i =>
    absorbed_subset_acting hw hmsf hwf i)]
  refine card_le_card fun e he => ?_
  obtain ⟨i, -, hei⟩ := mem_biUnion.1 he
  exact mem_errors.2 ⟨(mem_filter.1 (absorbed_subset_acting hw hmsf hwf i hei)).1,
    hasError_of_mem_absorbed hw hmsf hwf hei⟩

/-- The bound outside the calls, per call (§3.6, p. 24): the estimator, `4 d` per error, `468`
per edge sent to a batch, and per round at most `n` comparisons and `2 d r² √(8 n m)` for the
successful tests. -/
private theorem outsideBound_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {c : Instance V E} (hwf : c.WellFormed) (hS : c.edges ≠ ∅) :
    outsideBound cfg (LEQuery.keyOracle w) c ≤ estCost cfg (LEQuery.keyOracle w) c +
      4 * (c.level : ℕ) * #(errors cfg w c) +
      468 * ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(finds cfg (LEQuery.keyOracle w) c i) : ℝ) +
      ((levelT cfg.γ c.level ^ 2 : ℕ) : ℝ) * (#c.vertices + 2 * (c.level : ℕ) *
        ((levelR cfg.γ c.level : ℝ) ^ 2 * √(8 * #c.vertices * #c.edges))) := by
  have habs : (∑ i ∈ range (levelT cfg.γ c.level ^ 2),
      (#(absorbed cfg (LEQuery.keyOracle w) c i) : ℝ)) ≤ #(errors cfg w c) := by
    exact_mod_cast sum_card_absorbed_le_card_errors hw hmsf hwf
  have hB := sum_card_batch_le cfg (LEQuery.keyOracle w) c (levelT cfg.γ c.level ^ 2)
  have hB' : ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (if (i + 1) % levelT cfg.γ c.level = 0 then
      (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ) else 0) ≤
      ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(finds cfg (LEQuery.keyOracle w) c i) : ℝ) := by
    have : ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (if (i + 1) % levelT cfg.γ c.level = 0 then
        #(afterRound cfg (LEQuery.keyOracle w) c i).batch else 0) ≤
        ∑ i ∈ range (levelT cfg.γ c.level ^ 2), #(finds cfg (LEQuery.keyOracle w) c i) := by
      omega
    exact_mod_cast (by simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using this)
  have hd : ((2 * ((c.level : ℕ) - 1) : ℕ) : ℝ) ≤ 2 * (c.level : ℕ) := by
    have : 2 * ((c.level : ℕ) - 1) ≤ 2 * (c.level : ℕ) := by omega
    exact_mod_cast this
  have hround : ∀ i ∈ range (levelT cfg.γ c.level ^ 2),
      (if (i + 1) % levelT cfg.γ c.level = 0 then
          468 * (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ) + #c.vertices +
            ((2 * ((c.level : ℕ) - 1) : ℕ) : ℝ) * ((levelR cfg.γ c.level : ℝ) ^ 2 *
              √(8 * #c.vertices * #(afterRound cfg (LEQuery.keyOracle w) c i).batch))
          else 0) ≤
        468 * (if (i + 1) % levelT cfg.γ c.level = 0 then
          (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ) else 0) +
        (#c.vertices + 2 * (c.level : ℕ) *
          ((levelR cfg.γ c.level : ℝ) ^ 2 * √(8 * #c.vertices * #c.edges))) := fun i _ => by
    have hBm : (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ) ≤ #c.edges := by
      exact_mod_cast card_le_card (invariant_afterRound_of_wellFormed hw hmsf hwf i).batch_subset
    have hsq : √(8 * #c.vertices * (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ)) ≤
        √(8 * #c.vertices * #c.edges) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBm (by positivity))
    have h2 : (levelR cfg.γ c.level : ℝ) ^ 2 *
        √(8 * #c.vertices * (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ)) ≤
        (levelR cfg.γ c.level : ℝ) ^ 2 * √(8 * #c.vertices * #c.edges) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h1 : ((2 * ((c.level : ℕ) - 1) : ℕ) : ℝ) * ((levelR cfg.γ c.level : ℝ) ^ 2 *
        √(8 * #c.vertices * (#(afterRound cfg (LEQuery.keyOracle w) c i).batch : ℝ))) ≤
        2 * (c.level : ℕ) * ((levelR cfg.γ c.level : ℝ) ^ 2 * √(8 * #c.vertices * #c.edges)) :=
      mul_le_mul hd h2 (by positivity) (by positivity)
    split
    · linarith
    · have : 0 ≤ (2 * (c.level : ℕ) : ℝ) *
          ((levelR cfg.γ c.level : ℝ) ^ 2 * √(8 * #c.vertices * #c.edges)) := by positivity
      simp only [mul_zero, zero_add]
      linarith [(Nat.cast_nonneg (#c.vertices) : (0 : ℝ) ≤ _)]
  have hr := sum_le_sum hround
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hr
  rw [outsideBound]
  simp only [hS, ↓reduceIte, sum_add_distrib]
  push_cast at hr ⊢
  rw [← mul_sum]
  have h4 := mul_le_mul_of_nonneg_left habs
    (by positivity : (0 : ℝ) ≤ 4 * ((c.level : ℕ) : ℝ))
  have h5 := mul_le_mul_of_nonneg_left hB' (by norm_num : (0 : ℝ) ≤ 468)
  linarith

/-- **The inputs of a call's exact calls** (§3.6, p. 24): over its rounds, at most `2 (n - 1)`
forest edges and the absorbed edges per round, and `(n - 1) + r² n` per block. -/
private theorem sum_card_msfInputs_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {c : Instance V E} (hwf : c.WellFormed) :
    ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S => (#S : ℝ)).sum ≤
      ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(absorbed cfg (LEQuery.keyOracle w) c i) : ℝ) +
      ((levelT cfg.γ c.level ^ 2 : ℕ) : ℝ) * ((3 + (levelR cfg.γ c.level : ℝ) ^ 2) *
        #c.vertices) := by
  by_cases hS : c.edges = ∅
  · rw [msfInputs]
    simp only [hS, ↓reduceIte, List.map_nil, List.sum_nil]
    have : ∀ i, absorbed cfg (LEQuery.keyOracle w) c i = ∅ := fun i =>
      eq_empty_of_forall_notMem fun e he => by
        have := (mem_filter.1 (absorbed_subset_acting hw hmsf hwf i he)).1
        rw [hS] at this; simp at this
    simp only [this, card_empty, Nat.cast_zero, sum_const_zero, zero_add]
    positivity
  rw [sum_map_msfInputs cfg _ _ c hS]
  have hround : ∀ i ∈ range (levelT cfg.γ c.level ^ 2),
      ((#(roundInput cfg (LEQuery.keyOracle w) c i) : ℝ) +
        if (i + 1) % levelT cfg.γ c.level = 0 then
          (#((afterRound cfg (LEQuery.keyOracle w) c i).state.forest ∪
            (batchResult cfg (LEQuery.keyOracle w) c i).declared) : ℝ)
        else 0) ≤ (#(absorbed cfg (LEQuery.keyOracle w) c i) : ℝ) +
          (3 + (levelR cfg.γ c.level : ℝ) ^ 2) * #c.vertices := fun i _ => by
    have h1 := card_roundInput_le hw hmsf hwf i
    have h2 := card_blockInput_le hw hmsf hwf i
    have h1' : (#(roundInput cfg (LEQuery.keyOracle w) c i) : ℝ) ≤
        2 * #c.vertices + #(absorbed cfg (LEQuery.keyOracle w) c i) := by
      have : #(roundInput cfg (LEQuery.keyOracle w) c i) ≤
          2 * #c.vertices + #(absorbed cfg (LEQuery.keyOracle w) c i) := by omega
      exact_mod_cast this
    have h2' : (#((afterRound cfg (LEQuery.keyOracle w) c i).state.forest ∪
        (batchResult cfg (LEQuery.keyOracle w) c i).declared) : ℝ) ≤
        #c.vertices + (levelR cfg.γ c.level : ℝ) ^ 2 * #c.vertices := by
      have : #((afterRound cfg (LEQuery.keyOracle w) c i).state.forest ∪
          (batchResult cfg (LEQuery.keyOracle w) c i).declared) ≤
          #c.vertices + levelR cfg.γ c.level ^ 2 * #c.vertices := by omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ #c.vertices := Nat.cast_nonneg _
    split
    · linarith
    · nlinarith
  refine (sum_le_sum hround).trans_eq ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]

/-- **Every exact call works on edges of the call**, hence of the root. -/
theorem subset_edges_of_mem_msfInputs (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {c : Instance V E} (hwf : c.WellFormed) {S : Finset E}
    (hS : S ∈ msfInputs cfg (LEQuery.keyOracle w) c) : S ⊆ c.edges := by
  rw [msfInputs] at hS
  split at hS
  · cases hS
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hS
  have hce := child_edges_subset cfg w c i
  have hc := sound_childResult hw hmsf hwf i
  rcases List.mem_cons.1 hi with rfl | hi
  · refine union_subset (union_subset (invariant_snapshot hw hmsf hwf i).forest_subset
      (hc.forest_subset.trans hce)) ?_
    exact (filter_subset _ _).trans (hc.rejected_subset.trans hce)
  · split at hi
    · rw [List.mem_singleton.1 hi]
      have ha := invariant_afterRound_of_wellFormed hw hmsf hwf i
      refine union_subset ha.forest_subset ((declared_subset_batch hw
        (fun e => eval_admissibilityTest w _ e)).trans ha.batch_subset)
    · cases hi

end Recursion

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): each edge enters at
most one batch in the whole recursion ("Bounding the number of comparisons", §3.6, p. 24). The edges
sent to batches, over all calls, number at most the edges of the root call. -/
theorem sum_calls_sum_card_finds_le (cfg : Config V E) (o : {ι : Type} → LEQuery E ι → ι)
    (inst : Instance V E) :
    ((calls cfg o inst).map fun c =>
      ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(finds cfg o c i) : ℝ)).sum ≤ #inst.edges := by
  have := sum_calls_le_of_potential cfg o (Φ := fun _ => 1) (μ := fun c => (#c.edges : ℝ))
    (g := fun c => ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(finds cfg o c i) : ℝ))
    (fun c => by simp) (fun c hc => ?_) (fun c _ => ?_) inst
  · simpa using this
  · have : ∀ i, finds cfg o c i = ∅ := fun i => eq_empty_of_forall_notMem fun e he => by
      have := (mem_filter.1 (mem_filter.1 he).1).1
      rw [hc] at this; simp at this
    simp [this, hc]
  · have := sum_card_finds_add_card_child_edges cfg o c
    simp only [one_mul]
    rw [← sum_add_distrib]
    exact_mod_cast this.le

/-! ### The level polynomials -/

/-- The polynomials in the level of §3.6 grow at most like `d ^ 25`: with `t = γ d³` and
`r = 8 t³`, `t² (a + b d + c d r²) ≤ ((a + b) γ² + 64 c γ⁸) d²⁵`. -/
private theorem levelT_sq_mul_le (γ : ℕ) {d : ℕ} (hd : 1 ≤ d) {a b c : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (levelT γ d : ℝ) ^ 2 * (a + b * d + c * d * (levelR γ d : ℝ) ^ 2) ≤
      ((a + b) * γ ^ 2 + 64 * c * γ ^ 8) * (d : ℝ) ^ 25 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h6 : (d : ℝ) ^ 6 ≤ (d : ℝ) ^ 25 := pow_le_pow_right₀ hd' (by norm_num)
  have h7 : (d : ℝ) ^ 7 ≤ (d : ℝ) ^ 25 := pow_le_pow_right₀ hd' (by norm_num)
  have e : (levelT γ d : ℝ) ^ 2 * (a + b * d + c * d * (levelR γ d : ℝ) ^ 2) =
      a * γ ^ 2 * (d : ℝ) ^ 6 + b * γ ^ 2 * (d : ℝ) ^ 7 + 64 * c * γ ^ 8 * (d : ℝ) ^ 25 := by
    simp only [levelR, levelT]
    push_cast
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ a * γ ^ 2)
  have := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ b * γ ^ 2)
  nlinarith

/-- `q d + Φ (d + 1) ≤ Φ d` for `q d = a d^k / t` and `Φ d = 2 a / (γ d)`, when `k ≤ 1` (here
`d^k ≤ d`): the level weights of the error terms `4 m / t` (`k = 0`, §3.6, p. 23) and of their
failed tests `16 d m / t` (`k = 1`, p. 24), summed with `∑ 1/d³ ≤ 2` and `∑ 1/d² ≤ 2`. -/
private theorem div_levelT_add_le (γ : ℕ) {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : k ≤ 1) {d : ℕ}
    (hd : 1 ≤ d) :
    a * (d : ℝ) ^ k / levelT γ d + 2 * a / (γ * ((d + 1 : ℕ) : ℝ)) ≤ 2 * a / (γ * (d : ℝ)) := by
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · simp [levelT]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hdk : (d : ℝ) ^ k ≤ d := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl <;> simp [hd']
  have ht : (levelT γ d : ℝ) = γ * d ^ 3 := by simp [levelT]
  rw [ht, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  push_cast
  have h1 : a * (d : ℝ) ^ k ≤ a * d := mul_le_mul_of_nonneg_left hdk ha
  have key : (a * d * (γ * (d + 1)) + γ * d ^ 3 * (2 * a)) * (γ * d) ≤
      2 * a * (γ * d ^ 3 * (γ * (d + 1))) := by
    have : a * d * (γ * (d + 1)) * (γ * d) + γ * d ^ 3 * (2 * a) * (γ * d) ≤
        2 * a * (γ * d ^ 3 * (γ * (d + 1))) := by
      have e : 2 * a * (γ * d ^ 3 * (γ * (d + 1))) - (a * d * (γ * (d + 1)) * (γ * d) +
          γ * d ^ 3 * (2 * a) * (γ * d)) = a * γ ^ 2 * d ^ 2 * (d - 1) := by ring
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha (sq_nonneg (γ : ℝ))) (sq_nonneg (d : ℝ)))
        (by linarith : (0 : ℝ) ≤ d - 1)]
    linarith
  calc (a * (d : ℝ) ^ k * (γ * (d + 1)) + γ * d ^ 3 * (2 * a)) * (γ * d)
      ≤ (a * d * (γ * (d + 1)) + γ * d ^ 3 * (2 * a)) * (γ * d) := by
        gcongr
    _ ≤ _ := key

/-! ### Lemma 3.1 -/

section Lemma31

variable {W : Type} [LinearOrder W]

/-- **Hypothesis (i)**, the error bound of each call (§3.6, p. 23, from Lemmas 3.10 and 3.11 and
§3.5): every call `c` of the recursion rooted at `inst` has at most
`A t_c² √(m_c n_c) + 4 m_c / t_c` edges with an error (`Cslib.Query.Certificate.errors`), where
`t_c = γ d_c³`. It is a property of the schedule and the estimator of `cfg`; it holds with
`A = 11` for the schedule of Lemma 3.11 and the estimator of §3.5
(`Cslib.Query.Certificate.errorBound_derandomized`). -/
def ErrorBound (cfg : Config V E) (w : E → W) (inst : Instance V E) (A : ℝ) : Prop :=
  ∀ c ∈ calls cfg (LEQuery.keyOracle w) inst,
    (#(errors cfg w c) : ℝ) ≤ A * (levelT cfg.γ c.level : ℝ) ^ 2 * √(#c.edges * #c.vertices) +
      4 * #c.edges / levelT cfg.γ c.level

/-- **Hypothesis (ii)**, the cost of the estimator (§3.5, p. 22): every call `c` with an edge of
the recursion rooted at `inst` spends at most `B (t_c² n_c + t_c² √(m_c n_c))` comparisons in its
estimator (`Cslib.Query.Certificate.estCost`). It is a property of the estimator of `cfg`; it
holds with `B = 49` for the estimator of §3.5 (`Cslib.Query.Certificate.estCostBound_derandomized`).
-/
def EstCostBound (cfg : Config V E) (w : E → W) (inst : Instance V E) (B : ℝ) : Prop :=
  ∀ c ∈ calls cfg (LEQuery.keyOracle w) inst, c.edges ≠ ∅ →
    (estCost cfg (LEQuery.keyOracle w) c : ℝ) ≤
      B * ((levelT cfg.γ c.level : ℝ) ^ 2 * #c.vertices +
        (levelT cfg.γ c.level : ℝ) ^ 2 * √(#c.edges * #c.vertices))

/-- `√(8 n m) ≤ 3 √(m n)`. -/
private theorem sqrt_eight_mul_le (n m : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    √(8 * n * m) ≤ 3 * √(m * n) := by
  calc √(8 * n * m) ≤ √(9 * (m * n)) := Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hn hm])
    _ = 3 * √(m * n) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

variable {cfg : Config V E} {w : E → W}

/-- The comparisons of a call outside its child calls and exact calls, under hypotheses (i) and
(ii) for the call: a level polynomial times the mass `n + √(m n)`, `468` per edge sent to a
batch, and `16 d m / t` for the failed tests of the edges with an error. -/
private theorem outsideBound_le_of_bounds (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {c : Instance V E} (hwf : c.WellFormed)
    (hi : (#(errors cfg w c) : ℝ) ≤ A * (levelT cfg.γ c.level : ℝ) ^ 2 *
      √(#c.edges * #c.vertices) + 4 * #c.edges / levelT cfg.γ c.level)
    (hii : c.edges ≠ ∅ → (estCost cfg (LEQuery.keyOracle w) c : ℝ) ≤
      B * ((levelT cfg.γ c.level : ℝ) ^ 2 * #c.vertices +
        (levelT cfg.γ c.level : ℝ) ^ 2 * √(#c.edges * #c.vertices))) :
    outsideBound cfg (LEQuery.keyOracle w) c ≤
      (levelT cfg.γ c.level : ℝ) ^ 2 * ((B + 1) + 4 * A * (c.level : ℕ) +
        6 * (c.level : ℕ) * (levelR cfg.γ c.level : ℝ) ^ 2) *
          (#c.vertices + √(#c.edges * #c.vertices)) +
      468 * ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(finds cfg (LEQuery.keyOracle w) c i) : ℝ) +
      16 * ((c.level : ℕ) : ℝ) ^ 1 / levelT cfg.γ c.level * #c.edges := by
  set t : ℝ := (levelT cfg.γ c.level : ℝ)
  set r : ℝ := (levelR cfg.γ c.level : ℝ)
  set d : ℝ := ((c.level : ℕ) : ℝ)
  set n : ℝ := (#c.vertices : ℝ)
  set m : ℝ := (#c.edges : ℝ)
  set F : ℝ := ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(finds cfg (LEQuery.keyOracle w) c i) : ℝ)
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hd : 1 ≤ d := by simp only [d]; exact_mod_cast c.level.pos
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hF : 0 ≤ F := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsq : 0 ≤ √(m * n) := Real.sqrt_nonneg _
  have hq : 0 ≤ 16 * d ^ 1 / t * m := by positivity
  by_cases hS : c.edges = ∅
  · simp only [outsideBound, hS, ↓reduceIte]
    positivity
  have ho := outsideBound_le hw hmsf hwf hS
  have hes := hii hS
  have h8 := sqrt_eight_mul_le n m hn hm
  have p1 := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ 4 * d)
  have p2 : 2 * d * (r ^ 2 * √(8 * n * m)) ≤ 2 * d * (r ^ 2 * (3 * √(m * n))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 (by positivity)) (by positivity)
  have p3 := mul_le_mul_of_nonneg_left p2 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have hT : (((levelT cfg.γ c.level ^ 2 : ℕ) : ℝ)) = t ^ 2 := by push_cast; rfl
  rw [hT] at ho
  have e1 : 4 * d * (4 * m / t) = 16 * d ^ 1 / t * m := by ring
  have n1 : 0 ≤ t ^ 2 * √(m * n) := by positivity
  have n2 : 0 ≤ 4 * A * d * t ^ 2 * n := by positivity
  have n3 : 0 ≤ 6 * d * r ^ 2 * t ^ 2 * n := by positivity
  nlinarith

/-- The inputs of the exact calls of a call and its errors, under hypothesis (i) for the call:
a level polynomial times the mass `n + √(m n)`, `4 m / t`, and the absorbed edges. -/
private theorem sum_card_msfInputs_add_card_errors_le (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) {A : ℝ} (hA : 0 ≤ A) {c : Instance V E} (hwf : c.WellFormed)
    (hi : (#(errors cfg w c) : ℝ) ≤ A * (levelT cfg.γ c.level : ℝ) ^ 2 *
      √(#c.edges * #c.vertices) + 4 * #c.edges / levelT cfg.γ c.level) :
    ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S => (#S : ℝ)).sum + #(errors cfg w c) ≤
      ∑ i ∈ range (levelT cfg.γ c.level ^ 2), (#(absorbed cfg (LEQuery.keyOracle w) c i) : ℝ) +
      ((levelT cfg.γ c.level : ℝ) ^ 2 * ((A + 3) + 0 * (c.level : ℕ) +
        1 * (c.level : ℕ) * (levelR cfg.γ c.level : ℝ) ^ 2) *
          (#c.vertices + √(#c.edges * #c.vertices)) +
      4 * ((c.level : ℕ) : ℝ) ^ 0 / levelT cfg.γ c.level * #c.edges) := by
  have h := sum_card_msfInputs_le hw hmsf hwf
  set t : ℝ := (levelT cfg.γ c.level : ℝ)
  set r : ℝ := (levelR cfg.γ c.level : ℝ)
  set d : ℝ := ((c.level : ℕ) : ℝ)
  set n : ℝ := (#c.vertices : ℝ)
  set m : ℝ := (#c.edges : ℝ)
  have hd : 1 ≤ d := by simp only [d]; exact_mod_cast c.level.pos
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hsq : 0 ≤ √(m * n) := Real.sqrt_nonneg _
  have hT : (((levelT cfg.γ c.level ^ 2 : ℕ) : ℝ)) = t ^ 2 := by push_cast; rfl
  rw [hT] at h
  have p1 : t ^ 2 * (r ^ 2 * n) ≤ t ^ 2 * (d * r ^ 2 * n) := by
    have : r ^ 2 * n ≤ d * r ^ 2 * n := by nlinarith [mul_nonneg (sq_nonneg r) hn]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg t)
  have n1 : 0 ≤ t ^ 2 * (A + 3) * √(m * n) := by positivity
  have n2 : 0 ≤ t ^ 2 * d * r ^ 2 * √(m * n) := by positivity
  have n3 : 0 ≤ t ^ 2 * A * n := by positivity
  have e1 : 4 * m / t = 4 * d ^ 0 / t * m := by ring
  nlinarith

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the paper's Lemma 3.1
(§3.1, p. 12, proved in §3.6, pp. 22–24) for the certificate procedure with any schedule and
estimator satisfying hypotheses (i) (`Cslib.Query.Certificate.ErrorBound`) and (ii)
(`Cslib.Query.Certificate.EstCostBound`). The paper's schedule and estimator are
`Cslib.Query.Certificate.certificate_derandomized_accounting`.

For every `γ` and constants `A, B ≥ 0` there are `C, C'` such that on a root instance with `n`
vertices, `m` edges and `n ≤ 2 m` (no isolated vertices), with injective weights and exact
minimum spanning forest calls:

* `|F| + |U(F)| + ∑ |E_i| ≤ 8 m / γ + C √(m n)`, where `F` is the returned forest, `U(F)` the
  root edges it does not support, and `E_i` ranges over the inputs of the exact calls of all the
  calls of the recursion (`Cslib.Query.Certificate.msfInputs`). The paper has `16 m / γ`; the
  unsupported and the rejected edges are counted together here (M7a's
  `Cslib.Query.Certificate.card_unsupported_add_sum_absorbed_le`), which saves a factor `2`.
  Taking `γ ≥ 8 / ε` gives the paper's `ε m + C_ε √(m n)`.
* The comparisons are at most `C' m` plus those of the exact calls.
* Every exact call works on root edges. -/
theorem certificate_root_accounting (γ : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C C' : ℝ, ∀ {V E W : Type} [DecidableEq V] [DecidableEq E] [LinearOrder W]
      (cfg : Config V E) (w : E → W) (X : Finset V) (ends : E → Sym2 V) (S : Finset E),
      cfg.γ = γ → Function.Injective w → cfg.ExactMsf w → (∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) →
      #X ≤ 2 * #S → ErrorBound cfg w (Instance.root X ends S) A →
      EstCostBound cfg w (Instance.root X ends S) B →
      (#((certificate cfg (Instance.root X ends S)).eval (LEQuery.keyOracle w)).forest +
          #(unsupported ends w
            ↑((certificate cfg (Instance.root X ends S)).eval (LEQuery.keyOracle w)).forest S) +
          ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map fun c =>
            ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' => (#S' : ℝ)).sum).sum ≤
        8 * #S / γ + C * √(#S * #X)) ∧
      ((certificate cfg (Instance.root X ends S)).countQueries (LEQuery.keyOracle w) : ℝ) ≤
        C' * #S + ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map fun c =>
          ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' =>
            ((cfg.msfSub c.ends S').countQueries (LEQuery.keyOracle w) : ℝ)).sum).sum ∧
      ∀ c ∈ calls cfg (LEQuery.keyOracle w) (Instance.root X ends S),
        ∀ S' ∈ msfInputs cfg (LEQuery.keyOracle w) c, S' ⊆ S := by
  obtain ⟨K, hK0, hK⟩ := exists_pow_le_mul_three_halves_pow 25
  set Ko : ℝ := (B + 1 + 4 * A) * γ ^ 2 + 64 * 6 * γ ^ 8
  set Ks : ℝ := (A + 3 + 0) * γ ^ 2 + 64 * 1 * γ ^ 8
  refine ⟨2 + 18 * (Ks * K), 24 * (Ko * K) + 468 + 32 / γ, ?_⟩
  intro V E W _ _ _ cfg w X ends S hγ hw hmsf hS hn hi hii
  subst hγ
  have hwf := Instance.wellFormed_root hS
  have hwfc := wellFormed_of_mem_calls hw hmsf hwf
  -- the root quantities
  have hm0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ #X := Nat.cast_nonneg _
  have hn2 : (#X : ℝ) ≤ 2 * #S := by exact_mod_cast hn
  have hsq0 : 0 ≤ √((#S : ℝ) * #X) := Real.sqrt_nonneg _
  have hsqm : √((#S : ℝ) * #X) ≤ 2 * #S :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  have hnsq : (#X : ℝ) ≤ 2 * √((#S : ℝ) * #X) := by
    have h : (#X : ℝ) / 2 ≤ √((#S : ℝ) * #X) :=
      (Real.le_sqrt (by positivity) (by positivity)).2 (by nlinarith)
    linarith
  have hKo : 0 ≤ Ko := by positivity
  have hKs : 0 ≤ Ks := by positivity
  -- Claim 3.13 for the two level polynomials
  have hpo : ∀ d, 1 ≤ d → (levelT cfg.γ d : ℝ) ^ 2 * ((B + 1) + 4 * A * d +
      6 * d * (levelR cfg.γ d : ℝ) ^ 2) ≤ Ko * K * (3 / 2) ^ d := fun d hd => by
    have := levelT_sq_mul_le cfg.γ hd (a := B + 1) (b := 4 * A) (c := 6) (by positivity)
      (by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hK d) hKo
    nlinarith
  have hps : ∀ d, 1 ≤ d → (levelT cfg.γ d : ℝ) ^ 2 * ((A + 3) + 0 * d +
      1 * d * (levelR cfg.γ d : ℝ) ^ 2) ≤ Ks * K * (3 / 2) ^ d := fun d hd => by
    have := levelT_sq_mul_le cfg.γ hd (a := A + 3) (b := 0) (c := 1) (by positivity) le_rfl
    have h2 := mul_le_mul_of_nonneg_left (hK d) hKs
    nlinarith
  have so := sum_calls_mul_mass_le_of_le_three_halves_pow cfg (LEQuery.keyOracle w) hpo
    (by positivity) (Instance.root X ends S)
  have ss := sum_calls_mul_mass_le_of_le_three_halves_pow cfg (LEQuery.keyOracle w) hps
    (by positivity) (Instance.root X ends S)
  have qo := sum_calls_mul_card_edges_le cfg (LEQuery.keyOracle w)
    (q := fun d => 16 * (d : ℝ) ^ 1 / levelT cfg.γ d) (Φ := fun d => 2 * 16 / (cfg.γ * (d : ℝ)))
    (fun d => by positivity) (fun d hd => div_levelT_add_le cfg.γ (by norm_num) le_rfl hd)
    (Instance.root X ends S)
  have qs := sum_calls_mul_card_edges_le cfg (LEQuery.keyOracle w)
    (q := fun d => 4 * (d : ℝ) ^ 0 / levelT cfg.γ d) (Φ := fun d => 2 * 4 / (cfg.γ * (d : ℝ)))
    (fun d => by positivity) (fun d hd => div_levelT_add_le cfg.γ (by norm_num) (by norm_num) hd)
    (Instance.root X ends S)
  have hfi := sum_calls_sum_card_finds_le cfg (LEQuery.keyOracle w) (Instance.root X ends S)
  simp only [Instance.root_level, PNat.one_coe, Nat.cast_one, pow_one, mul_one,
    Instance.root_edges, Instance.root_vertices] at so ss qo qs hfi
  refine ⟨?_, ?_, fun c hc S' hS' => (subset_edges_of_mem_msfInputs hw hmsf (hwfc c hc)
    hS').trans (edges_subset_of_mem_calls cfg _ hc)⟩
  · -- the sizes
    have hs := sound_certificate hw hmsf _ hwf
    have hF : (#((certificate cfg (Instance.root X ends S)).eval
        (LEQuery.keyOracle w)).forest : ℝ) ≤ #X := by
      have := hs.forest_acyclic.card_le (X := X) fun f hf v hv => hS f (hs.forest_subset hf) v hv
      have : #((certificate cfg (Instance.root X ends S)).eval
          (LEQuery.keyOracle w)).forest ≤ #X := by omega
      exact_mod_cast this
    have hU := card_unsupported_add_sum_absorbed_le hw hmsf hS
    have hcast : ∀ f : Instance V E → ℕ,
        ((((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map f).sum : ℕ) : ℝ) =
          ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map
            fun c => (f c : ℝ)).sum := fun f => by
      rw [Nat.cast_list_sum, List.map_map]; rfl
    have hU' := (Nat.cast_le (α := ℝ)).2 hU
    rw [Nat.cast_add, hcast, hcast] at hU'
    push_cast at hU'
    have hper := List.sum_le_sum fun c hc =>
      sum_card_msfInputs_add_card_errors_le hw hmsf hA (hwfc c hc) (hi c hc)
    rw [List.sum_map_add, List.sum_map_add, List.sum_map_add] at hper
    have e8 : 2 * 4 / (cfg.γ : ℝ) * #S = 8 * #S / cfg.γ := by ring
    have h1 := mul_le_mul_of_nonneg_left hnsq (by positivity : 0 ≤ Ks * K)
    linarith
  · -- the comparisons
    have hmain := countQueries_certificate_le_aux hw hmsf _ hwf (recordShape_root X ends S)
    rw [rejected_certificate_root hw hmsf hS, sum_empty, add_zero] at hmain
    simp only [msfCost] at hmain
    rw [List.sum_map_add] at hmain
    have hper := List.sum_le_sum fun c hc =>
      outsideBound_le_of_bounds hw hmsf hA hB (hwfc c hc) (hi c hc) (hii c hc)
    rw [List.sum_map_add, List.sum_map_add, List.sum_map_mul_left] at hper
    have e32 : 2 * 16 / (cfg.γ : ℝ) * #S = 32 / cfg.γ * #S := by ring
    have hμ : (#X : ℝ) + √((#S : ℝ) * #X) ≤ 4 * #S := by linarith
    have := mul_le_mul_of_nonneg_left hμ (by positivity : 0 ≤ Ko * K)
    simp only [pow_one] at hper
    have h2 := hmain.trans (add_le_add hper le_rfl)
    linarith

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the cost of the
certificate procedure with a linear exact subroutine, the form of the paper's Lemma 3.1 (§3.1, p.
12) used in the proof of Theorem 4.1 (§4, pp. 25–26) by strong induction on the number of edges.

Under the hypotheses of `Cslib.Query.Certificate.certificate_root_accounting`, every exact call
works on root edges and has at most `8 m / γ + C √(m n)` of them; and if each exact call costs at
most `κ` comparisons per input edge, the certificate procedure makes at most
`C' m + κ (8 m / γ + C √(m n))` comparisons in all. -/
theorem countQueries_certificate_root_le (γ : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C C' : ℝ, ∀ {V E W : Type} [DecidableEq V] [DecidableEq E] [LinearOrder W]
      (cfg : Config V E) (w : E → W) (X : Finset V) (ends : E → Sym2 V) (S : Finset E),
      cfg.γ = γ → Function.Injective w → cfg.ExactMsf w → (∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) →
      #X ≤ 2 * #S → ErrorBound cfg w (Instance.root X ends S) A →
      EstCostBound cfg w (Instance.root X ends S) B →
      (∀ c ∈ calls cfg (LEQuery.keyOracle w) (Instance.root X ends S),
        ∀ S' ∈ msfInputs cfg (LEQuery.keyOracle w) c,
          S' ⊆ S ∧ (#S' : ℝ) ≤ 8 * #S / γ + C * √(#S * #X)) ∧
      ∀ κ : ℝ, 0 ≤ κ →
        (∀ c ∈ calls cfg (LEQuery.keyOracle w) (Instance.root X ends S),
          ∀ S' ∈ msfInputs cfg (LEQuery.keyOracle w) c,
            ((cfg.msfSub c.ends S').countQueries (LEQuery.keyOracle w) : ℝ) ≤ κ * #S') →
        ((certificate cfg (Instance.root X ends S)).countQueries (LEQuery.keyOracle w) : ℝ) ≤
          C' * #S + κ * (8 * #S / γ + C * √(#S * #X)) := by
  obtain ⟨C, C', h⟩ := certificate_root_accounting γ hA hB
  refine ⟨C, C', ?_⟩
  intro V E W _ _ _ cfg w X ends S hγ hw hmsf hS hn hi hii
  obtain ⟨h1, h2, h3⟩ := h cfg w X ends S hγ hw hmsf hS hn hi hii
  have hsum : ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map fun c =>
      ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' => (#S' : ℝ)).sum).sum ≤
      8 * #S / γ + C * √(#S * #X) := by
    have : (0 : ℝ) ≤ #((certificate cfg (Instance.root X ends S)).eval
        (LEQuery.keyOracle w)).forest + #(unsupported ends w
          ↑((certificate cfg (Instance.root X ends S)).eval (LEQuery.keyOracle w)).forest S) := by
      positivity
    linarith
  refine ⟨fun c hc S' hS' => ⟨h3 c hc S' hS', ?_⟩, fun κ hκ hK => ?_⟩
  · refine le_trans ?_ hsum
    refine (List.single_le_sum (fun x hx => ?_) _
      (List.mem_map_of_mem (f := fun S' => (#S' : ℝ)) hS')).trans
      (List.single_le_sum (fun x hx => ?_) _ (List.mem_map_of_mem
        (f := fun c => ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' => (#S' : ℝ)).sum) hc))
    · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx; positivity
    · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
      exact List.sum_nonneg fun y hy => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy; positivity
  · have hmsfK : ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map fun c =>
        ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' =>
          ((cfg.msfSub c.ends S').countQueries (LEQuery.keyOracle w) : ℝ)).sum).sum ≤
        κ * ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map fun c =>
          ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' => (#S' : ℝ)).sum).sum := by
      rw [← List.sum_map_mul_left]
      refine List.sum_le_sum fun c hc => ?_
      rw [← List.sum_map_mul_left]
      exact List.sum_le_sum fun S' hS' => hK c hc S' hS'
    have := mul_le_mul_of_nonneg_left hsum hκ
    linarith

/-- **Hypothesis (i) holds for the derandomized configuration** (Lemma 3.11, Claim 3.12, §3.6,
p. 23), with `A = 11`, by `Cslib.Query.Certificate.card_errors_le` at every call. -/
theorem errorBound_derandomized (γ : ℕ) (hγ : 0 < γ)
    (msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)) {w : E → W}
    (hw : Function.Injective w) (hmsf : (Config.derandomized γ hγ msfSub).ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    ErrorBound (Config.derandomized γ hγ msfSub) w inst 11 := fun c hc =>
  card_errors_le γ hγ msfSub hw hmsf (wellFormed_of_mem_calls hw hmsf hwf c hc)

/-- **Hypothesis (ii) holds for the derandomized configuration** (§3.5, p. 22), with `B = 49`, by
`Cslib.Query.Certificate.sum_countQueries_estimator_le` at every call. -/
theorem estCostBound_derandomized (γ : ℕ) (hγ : 0 < γ)
    (msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)) {w : E → W}
    (hw : Function.Injective w) (hmsf : (Config.derandomized γ hγ msfSub).ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    EstCostBound (Config.derandomized γ hγ msfSub) w inst 49 := fun c hc _ => by
  have h := sum_countQueries_estimator_le _ w hw hmsf (wellFormed_of_mem_calls hw hmsf hwf c hc)
  have h0 : (0 : ℝ) ≤ (levelT (Config.derandomized γ hγ msfSub).γ c.level : ℝ) ^ 2 *
      #c.vertices := by positivity
  rw [estCost]
  push_cast
  exact h.trans (by linarith)

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the paper's Lemma 3.1
(§3.1, p. 12, proved in §3.6, pp. 22–24) for the certificate procedure with the schedule of Lemma
3.11 and the estimator of §3.5 (`Cslib.Query.Certificate.Config.derandomized`). For every `γ > 0`
there are `C, C'` such that on a root instance with `n` vertices, `m` edges and `n ≤ 2 m` (no
isolated vertices), with injective weights and exact minimum spanning forest calls,

* `|F| + |U(F)| + ∑ |E_i| ≤ 8 m / γ + C √(m n)` (the paper has `16 m / γ`; taking `γ ≥ 8 / ε`
  gives the paper's `ε m + C_ε √(m n)`),
* the comparisons are at most `C' m` plus those of the exact calls,
* every exact call works on root edges.

The paper's lemma assumes no isolated vertices, which gives `n ≤ 2 m`; only `n ≤ 2 m` is used. -/
theorem certificate_derandomized_accounting (γ : ℕ) (hγ : 0 < γ) :
    ∃ C C' : ℝ, ∀ {V E W : Type} [DecidableEq V] [DecidableEq E] [LinearOrder W]
      (msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)) (w : E → W)
      (X : Finset V) (ends : E → Sym2 V) (S : Finset E),
      Function.Injective w → (Config.derandomized γ hγ msfSub).ExactMsf w →
      (∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) → #X ≤ 2 * #S →
      (#((certificate (Config.derandomized γ hγ msfSub) (Instance.root X ends S)).eval
            (LEQuery.keyOracle w)).forest +
          #(unsupported ends w ↑((certificate (Config.derandomized γ hγ msfSub)
            (Instance.root X ends S)).eval (LEQuery.keyOracle w)).forest S) +
          ((calls (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w)
            (Instance.root X ends S)).map fun c =>
            ((msfInputs (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w) c).map
              fun S' => (#S' : ℝ)).sum).sum ≤
        8 * #S / γ + C * √(#S * #X)) ∧
      ((certificate (Config.derandomized γ hγ msfSub) (Instance.root X ends S)).countQueries
          (LEQuery.keyOracle w) : ℝ) ≤
        C' * #S + ((calls (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w)
          (Instance.root X ends S)).map fun c =>
          ((msfInputs (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w) c).map fun S' =>
            ((msfSub c.ends S').countQueries (LEQuery.keyOracle w) : ℝ)).sum).sum ∧
      ∀ c ∈ calls (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w)
          (Instance.root X ends S),
        ∀ S' ∈ msfInputs (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w) c, S' ⊆ S := by
  obtain ⟨C, C', h⟩ := certificate_root_accounting γ (A := 11) (B := 49) (by norm_num)
    (by norm_num)
  refine ⟨C, C', fun msfSub w X ends S hw hmsf hS hn => ?_⟩
  have hwf := Instance.wellFormed_root hS
  exact h _ w X ends S rfl hw hmsf hS hn (errorBound_derandomized γ hγ msfSub hw hmsf hwf)
    (estCostBound_derandomized γ hγ msfSub hw hmsf hwf)

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the cost of the
certificate procedure with a linear exact subroutine, for the derandomized configuration: the form
of the paper's Lemma 3.1 (§3.1, p. 12) used in the proof of Theorem 4.1 (§4, pp. 25–26) by strong
induction on the number of edges. Every exact call works on at most `8 m / γ + C √(m n)` root edges,
and if each costs at most `κ` comparisons per input edge, the procedure makes at most
`C' m + κ (8 m / γ + C √(m n))` comparisons. -/
theorem countQueries_certificate_derandomized_le (γ : ℕ) (hγ : 0 < γ) :
    ∃ C C' : ℝ, ∀ {V E W : Type} [DecidableEq V] [DecidableEq E] [LinearOrder W]
      (msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)) (w : E → W)
      (X : Finset V) (ends : E → Sym2 V) (S : Finset E),
      Function.Injective w → (Config.derandomized γ hγ msfSub).ExactMsf w →
      (∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) → #X ≤ 2 * #S →
      (∀ c ∈ calls (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w)
          (Instance.root X ends S),
        ∀ S' ∈ msfInputs (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w) c,
          S' ⊆ S ∧ (#S' : ℝ) ≤ 8 * #S / γ + C * √(#S * #X)) ∧
      ∀ κ : ℝ, 0 ≤ κ →
        (∀ c ∈ calls (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w)
            (Instance.root X ends S),
          ∀ S' ∈ msfInputs (Config.derandomized γ hγ msfSub) (LEQuery.keyOracle w) c,
            ((msfSub c.ends S').countQueries (LEQuery.keyOracle w) : ℝ) ≤ κ * #S') →
        ((certificate (Config.derandomized γ hγ msfSub) (Instance.root X ends S)).countQueries
            (LEQuery.keyOracle w) : ℝ) ≤
          C' * #S + κ * (8 * #S / γ + C * √(#S * #X)) := by
  obtain ⟨C, C', h⟩ := countQueries_certificate_root_le γ (A := 11) (B := 49) (by norm_num)
    (by norm_num)
  refine ⟨C, C', fun msfSub w X ends S hw hmsf hS hn => ?_⟩
  have hwf := Instance.wellFormed_root hS
  exact h _ w X ends S rfl hw hmsf hS hn (errorBound_derandomized γ hγ msfSub hw hmsf hwf)
    (estCostBound_derandomized γ hγ msfSub hw hmsf hwf)

end Lemma31

end Cslib.Query.Certificate
