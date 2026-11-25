/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Symmetric.Preprocessing
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.FinIndex
import CslibFrontier.Tactic.UniformRelabel

/-!
# Random-permutation toy SPIR scheme with client preprocessing

This file formalizes the first toy construction of single-server symmetric private information
retrieval (SPIR) with client preprocessing from
[Hoover, Persiano and Yeo, Section 6.3, pp. 54–55][HooverPersianoYeo2026]
("*`n`-bit client storage, `O(k log n)`-bit communication*"):

* **Shared server randomness**: an `n`-bit string `R : Fin n → Bool` sampled uniformly from
  `ProbComp.uniform (Fin n → Bool)`.
* **Setup** (`toyScheme.setup`, modeling the ideal 2PC setup functionality of Section 6.3 with
  trivial offline transcript `Toff = Unit`): the client samples a uniform random permutation
  `π : Equiv.Perm (Fin n)` and receives the masked database `fun i => xor (D i) (R (π i))` together
  with `π`.
* **Online query** (`toyScheme.query`, `toyScheme.answer`, `toyScheme.reconstruct`):
  on batch query tuple `Q : Fin k → Fin n`, the client uploads `τu = π ∘ Q : Fin k → Fin n`,
  the server answers with `τd = R ∘ τu : Fin k → Bool`, and the client reconstructs
  `fun j => xor (st.maskedDB (Q j)) (τd j)`.

## Scope and nuances

* **Client state size (`2 ^ n * n!`).** Although the paper's paragraph heading on p. 54 refers to
  "`n`-bit client storage", the online query `τu = π ∘ Q` uses the client's permutation `π`. In the
  syntax of Definition 6.1, all offline client state used by `Query` is part of `st : St`, so
  `ToyState n` (fields `maskedDB` and `perm`) has cardinality `2 ^ n * n!` (`card_toyState`).
* **Injective vs. repeated queries in a batch.** For every `n, k`, `toyScheme n k` is perfectly
  correct (`toyScheme_isCorrect`, `toyScheme_isCorrectWith_one`) and perfectly data private
  (`toyScheme_isPerfectlyDataPrivate`). For query privacy against the server, applying a uniform
  permutation `π` to `Q` hides the queried indices when `Q` is injective
  (`toyScheme_isPerfectlyPrivateOn_injective`), and hence for all queries when `k ≤ 1`
  (`toyScheme_isPerfectlyPrivate_of_le_one`). When `2 ≤ k` and `2 ≤ n`, however, `τu = π ∘ Q`
  leaks equality patterns among the coordinates of `Q` (`π (Q 0) = π (Q 1) ↔ Q 0 = Q 1`), so
  `toyScheme n k` is **not** perfectly private over all tuples `Q : Fin k → Fin n` with repeats
  allowed (`toyScheme_not_isPerfectlyPrivate`).
* **Coordinate-wise variant (not from the source).** `parallelToyScheme n k` runs `k` independent
  copies of the one-query case, each with its own permutation and its own block of server
  randomness. Its upload is uniform for every batch tuple, so it is perfectly correct, perfectly
  private and perfectly data private for all `n` and `k`
  (`parallelToyScheme_isCorrect`, `parallelToyScheme_isPerfectlyPrivate`,
  `parallelToyScheme_isPerfectlyDataPrivate`). It shows that the hypotheses of
  `Scheme.correct_le_card_div_two_pow` hold together for genuine batches `k ≥ 2`. Its state has
  `(2 ^ n) ^ k * (n!) ^ k` elements (`card_parallelToyState`).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.ToyState`: client state with fields
  `maskedDB` and `perm`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme`: the random-permutation toy
  `k`-batch SPIR scheme.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.ParallelToyState`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.parallelToyScheme`: the coordinate-wise
  variant.

## Main results

* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.card_toyState`:
  `Fintype.card (ToyState n) = 2 ^ n * n.factorial`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme_isCorrect`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme_isCorrectWith_one`:
  perfect correctness.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme_isPerfectlyDataPrivate`:
  perfect data privacy.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme_isPerfectlyPrivateOn_injective`:
  perfect server privacy restricted to injective batch tuples `{Q | Function.Injective Q}`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme_isPerfectlyPrivate_of_le_one`:
  unconditional perfect server privacy when `k ≤ 1`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.toyScheme_not_isPerfectlyPrivate`:
  counterexample to unrestricted perfect privacy when `2 ≤ k` and `2 ≤ n`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.parallelToyScheme_isPerfectlyPrivate`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.parallelToyScheme_isPerfectlyDataPrivate`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.parallelToyScheme_isCorrect`:
  the coordinate-wise variant meets all three hypotheses of the core bound for every `n` and `k`.

## References

* [A. Hoover, G. Persiano, K. Yeo, *Lower Bounds for PIR with Preprocessing from Blackbox
  Cryptography*][HooverPersianoYeo2026], Section 6.3, pp. 54–55. FOCS 2026; page numbers from
  arXiv:2607.06451v3.
-/

public section

namespace Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing

open Cslib.Probability
open scoped ENNReal

/-- Client preprocessing state for the random-permutation toy SPIR scheme. -/
structure ToyState (n : ℕ) where
  /-- The masked database `i ↦ D i ⊕ R (π i)`. -/
  maskedDB : Fin n → Bool
  /-- The client's permutation `π`, used to hide the queried indices. -/
  perm : Equiv.Perm (Fin n)

/-- `ToyState n` is equivalent to the pair of its fields. -/
def ToyState.equivProd (n : ℕ) : ToyState n ≃ (Fin n → Bool) × Equiv.Perm (Fin n) where
  toFun st := (st.maskedDB, st.perm)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : ℕ) : Fintype (ToyState n) := Fintype.ofEquiv _ (ToyState.equivProd n).symm

/-- The client state of `toyScheme n k` has cardinality `2 ^ n * n!` (storing both the `n`-bit
masked database and the permutation `π : Equiv.Perm (Fin n)`). -/
theorem card_toyState (n : ℕ) : Fintype.card (ToyState n) = 2 ^ n * n.factorial := by
  simp [Fintype.card_congr (ToyState.equivProd n), Fintype.card_perm]

/-- The random-permutation toy `k`-batch SPIR scheme with ideal setup functionality
[Hoover, Persiano and Yeo, Section 6.3, pp. 54–55][HooverPersianoYeo2026]. -/
@[expose] noncomputable def toyScheme (n k : ℕ) :
    Scheme n k (Fin n → Bool) (ToyState n) Unit (Fin k → Fin n) (Fin k → Bool) where
  rLaw := ProbComp.uniform (Fin n → Bool)
  setup D r := do
    let π ← ProbComp.uniform (Equiv.Perm (Fin n))
    pure (⟨fun i => xor (D i) (r (π i)), π⟩, ())
  query st Q := st.perm ∘ Q
  answer _D r τu := r ∘ τu
  reconstruct st Q τd := fun j => xor (st.maskedDB (Q j)) (τd j)

/-! ### Correctness -/

private theorem xor_cancel_query {n k : ℕ} (D : Fin n → Bool) (Q : Fin k → Fin n)
    (r : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (fun j => xor (xor (D (Q j)) (r (π (Q j)))) (r (π (Q j)))) = D ∘ Q := by
  funext j
  simp

/-- `toyScheme n k` is perfectly correct (`IsCorrect`). -/
theorem toyScheme_isCorrect (n k : ℕ) : (toyScheme n k).IsCorrect := by
  intro D Q
  simp only [Scheme.run, Scheme.runAt, toyScheme, bind_assoc, pure_bind, Function.comp_def,
    xor_cancel_query, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

/-- `toyScheme n k` is `1`-correct (`IsCorrectWith 1`). -/
theorem toyScheme_isCorrectWith_one (n k : ℕ) : (toyScheme n k).IsCorrectWith 1 :=
  (toyScheme_isCorrect n k).isCorrectWith_one

/-! ### Perfect data privacy -/

/-- `toyScheme n k` is perfectly data private (`IsPerfectlyDataPrivate`). -/
theorem toyScheme_isPerfectlyDataPrivate (n k : ℕ) : (toyScheme n k).IsPerfectlyDataPrivate := by
  intro D₀ D₁ Q hD
  simp only [Scheme.clientView, Scheme.clientViewAt, toyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext π
  relabel_uniform
    (fun (r : Fin n → Bool) m => xor (r m) (xor (D₀ (π.symm m)) (D₁ (π.symm m)))) with r
  have hq :
      ((fun m => xor (r m) (xor (D₀ (π.symm m)) (D₁ (π.symm m)))) ∘ (π ∘ Q)) = r ∘ (π ∘ Q) := by
    funext j
    have hDj : D₀ (Q j) = D₁ (Q j) := congrFun hD j
    simp [Function.comp_apply, hDj]
  rw [hq]
  congr 1; congr 1; congr 1
  funext i
  simp only [Equiv.symm_apply_apply]
  cases D₀ i <;> cases D₁ i <;> cases r (π i) <;> rfl

/-! ### Server privacy on injective query tuples and repeated-query counterexample -/

/-- Any two injective query tuples `Q₀, Q₁ : Fin k → Fin n` are related by a permutation
`σ : Equiv.Perm (Fin n)` with `σ ∘ Q₀ = Q₁`. -/
private theorem exists_perm_comp_eq {n k : ℕ} {Q₀ Q₁ : Fin k → Fin n}
    (hQ₀ : Function.Injective Q₀) (hQ₁ : Function.Injective Q₁) :
    ∃ σ : Equiv.Perm (Fin n), σ ∘ Q₀ = Q₁ := by
  classical
  let eRange : Set.range Q₀ ≃ Set.range Q₁ :=
    (Equiv.ofInjective Q₀ hQ₀).symm.trans (Equiv.ofInjective Q₁ hQ₁)
  refine ⟨(Equiv.Set.sumCompl _).symm.trans
    ((Equiv.sumCongr eRange (Fintype.equivOfCardEq ?_)).trans (Equiv.Set.sumCompl _)),
    funext fun j => ?_⟩
  · rw [Fintype.card_compl_set, Fintype.card_compl_set, Fintype.card_congr eRange]
  · have hmem : Q₀ j ∈ Set.range Q₀ := ⟨j, rfl⟩
    simp [eRange, Equiv.Set.sumCompl_symm_apply_of_mem hmem]

/-- `toyScheme n k` is perfectly private on the set of injective query tuples
`{Q | Function.Injective Q}`. -/
theorem toyScheme_isPerfectlyPrivateOn_injective (n k : ℕ) :
    (toyScheme n k).IsPerfectlyPrivateOn {Q | Function.Injective Q} := by
  intro D Q₀ hQ₀ Q₁ hQ₁
  obtain ⟨σ, rfl⟩ := exists_perm_comp_eq hQ₀ hQ₁
  simp only [Scheme.serverView, Scheme.serverViewAt, toyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  congr 1
  funext r
  relabel_uniform (Equiv.mulRight σ⁻¹) with π
  have hcomp : (Equiv.mulRight σ⁻¹ π) ∘ (σ ∘ Q₀) = π ∘ Q₀ := by
    ext j
    simp [Equiv.mulRight]
  rw [hcomp]

/-- When `k ≤ 1`, every query tuple `Q : Fin k → Fin n` is injective, so `toyScheme n k` is
unconditionally perfectly private (`IsPerfectlyPrivate`). -/
theorem toyScheme_isPerfectlyPrivate_of_le_one {n k : ℕ} (hk : k ≤ 1) :
    (toyScheme n k).IsPerfectlyPrivate := by
  have hinj (Q : Fin k → Fin n) : Function.Injective Q := fun _ _ _ => by
    ext
    omega
  exact fun D Q₀ Q₁ => toyScheme_isPerfectlyPrivateOn_injective n k D Q₀ (hinj Q₀) Q₁ (hinj Q₁)

/-- When `2 ≤ k` and `2 ≤ n`, `toyScheme n k` is **not** perfectly private over all batch tuples
(with repeats allowed): the upload `τu = π ∘ Q` reveals whether the first two queried indices
are equal. -/
theorem toyScheme_not_isPerfectlyPrivate {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) :
    ¬ (toyScheme n k).IsPerfectlyPrivate := by
  intro hpriv
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let j₀ : Fin k := ⟨0, by omega⟩
  let j₁ : Fin k := ⟨1, by omega⟩
  let obs : (Fin n → Bool) × Unit × (Fin k → Fin n) × (Fin k → Bool) → Bool :=
    fun (_, _, τu, _) => decide (τu j₀ = τu j₁)
  have hmap (Q : Fin k → Fin n) (b : Bool)
      (hb : ∀ π : Equiv.Perm (Fin n), decide (π (Q j₀) = π (Q j₁)) = b) :
      (ProbComp.eval ((toyScheme n k).serverView (fun _ => false) Q)).map obs = PMF.pure b := by
    rw [Cslib.Probability.PMF.map_eq_pure_iff]
    intro v hv
    simp only [Scheme.serverView, Scheme.serverViewAt, toyScheme, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hv
    rcases hv with ⟨_, _, π, _, rfl⟩
    exact hb π
  have hj : j₁ ≠ j₀ := by fin_index [j₀, j₁]
  have hi : i₀ ≠ i₁ := by omega
  exact Cslib.Probability.PMF.ne_of_map_eq_pure
    (hmap (fun _ => i₀) true fun _ => by simp)
    (hmap (fun j => if j = j₀ then i₀ else i₁) false fun π => by simp [hj, π.injective.eq_iff, hi])
    (by decide) (hpriv _ _ _)

/-! ### Coordinate-wise toy scheme: privacy for every batch tuple (not from the source) -/

/-- Client state of `parallelToyScheme n k`: one masked database and one permutation per batch
coordinate. -/
structure ParallelToyState (n k : ℕ) where
  /-- The masked databases `j ↦ (i ↦ D i ⊕ r j (π j i))`. -/
  maskedDBs : Fin k → Fin n → Bool
  /-- The client's permutations `π j`, one per batch coordinate. -/
  perms : Fin k → Equiv.Perm (Fin n)

/-- `ParallelToyState n k` is equivalent to the pair of its fields. -/
def ParallelToyState.equivProd (n k : ℕ) :
    ParallelToyState n k ≃ (Fin k → Fin n → Bool) × (Fin k → Equiv.Perm (Fin n)) where
  toFun st := (st.maskedDBs, st.perms)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (n k : ℕ) : Fintype (ParallelToyState n k) :=
  Fintype.ofEquiv _ (ParallelToyState.equivProd n k).symm

/-- The client state of `parallelToyScheme n k` has cardinality `(2 ^ n) ^ k * (n!) ^ k`. -/
theorem card_parallelToyState (n k : ℕ) :
    Fintype.card (ParallelToyState n k) = (2 ^ n) ^ k * n.factorial ^ k := by
  simp [Fintype.card_congr (ParallelToyState.equivProd n k), Fintype.card_perm]

/-- The coordinate-wise toy `k`-batch SPIR scheme: `k` independent copies of the one-query case
of `toyScheme`, one per batch coordinate. The server randomness is a uniform family
`r : Fin k → Fin n → Bool`; the ideal setup gives the client independent uniform permutations
`π j` and the masked databases `fun i => xor (D i) (r j (π j i))`; on `Q` the client uploads
`fun j => π j (Q j)`, the server answers `fun j => r j (τu j)`, and the client unmasks coordinate
`j` with its `j`-th masked database. Because each coordinate uses a fresh permutation, the upload
is uniform for every batch tuple, repeated indices included. This construction is not in the
source; it witnesses that the hypotheses of `Scheme.correct_le_card_div_two_pow` hold together
for every `n` and `k`. -/
@[expose] noncomputable def parallelToyScheme (n k : ℕ) :
    Scheme n k (Fin k → Fin n → Bool) (ParallelToyState n k) Unit (Fin k → Fin n)
      (Fin k → Bool) where
  rLaw := ProbComp.uniform (Fin k → Fin n → Bool)
  setup D r := do
    let π ← ProbComp.uniform (Fin k → Equiv.Perm (Fin n))
    pure (⟨fun j i => xor (D i) (r j (π j i)), π⟩, ())
  query st Q := fun j => st.perms j (Q j)
  answer _D r τu := fun j => r j (τu j)
  reconstruct st Q τd := fun j => xor (st.maskedDBs j (Q j)) (τd j)

private theorem parallel_xor_cancel_query {n k : ℕ} (D : Fin n → Bool) (Q : Fin k → Fin n)
    (r : Fin k → Fin n → Bool) (π : Fin k → Equiv.Perm (Fin n)) :
    (fun j => xor (xor (D (Q j)) (r j (π j (Q j)))) (r j (π j (Q j)))) = D ∘ Q := by
  funext j
  simp

/-- `parallelToyScheme n k` is perfectly correct (`IsCorrect`). -/
theorem parallelToyScheme_isCorrect (n k : ℕ) : (parallelToyScheme n k).IsCorrect := by
  intro D Q
  simp only [Scheme.run, Scheme.runAt, parallelToyScheme, bind_assoc, pure_bind,
    parallel_xor_cancel_query, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

/-- `parallelToyScheme n k` is perfectly data private (`IsPerfectlyDataPrivate`). -/
theorem parallelToyScheme_isPerfectlyDataPrivate (n k : ℕ) :
    (parallelToyScheme n k).IsPerfectlyDataPrivate := by
  intro D₀ D₁ Q hD
  simp only [Scheme.clientView, Scheme.clientViewAt, parallelToyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1
  funext π
  relabel_uniform (fun (r : Fin k → Fin n → Bool) j m =>
    xor (r j m) (xor (D₀ ((π j).symm m)) (D₁ ((π j).symm m)))) with r
  have hq : (fun j => xor (r j (π j (Q j)))
      (xor (D₀ ((π j).symm (π j (Q j)))) (D₁ ((π j).symm (π j (Q j)))))) =
      fun j => r j (π j (Q j)) := by
    funext j
    have hDj : D₀ (Q j) = D₁ (Q j) := congrFun hD j
    simp [hDj]
  simp only [hq]
  congr 1; congr 1; congr 1
  funext j i
  simp only [Equiv.symm_apply_apply]
  cases D₀ i <;> cases D₁ i <;> cases r j (π j i) <;> rfl

/-- `parallelToyScheme n k` is perfectly private (`IsPerfectlyPrivate`) for every pair of batch
tuples, repeated indices included: composing each `π j` with the transposition of `Q₀ j` and
`Q₁ j` is a bijection on the permutation families that maps one upload to the other. -/
theorem parallelToyScheme_isPerfectlyPrivate (n k : ℕ) :
    (parallelToyScheme n k).IsPerfectlyPrivate := by
  intro D Q₀ Q₁
  simp only [Scheme.serverView, Scheme.serverViewAt, parallelToyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  congr 1
  funext r
  relabel_uniform (Equiv.piCongrRight fun j => Equiv.mulRight (Equiv.swap (Q₀ j) (Q₁ j))) with π
  simp

end Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing
