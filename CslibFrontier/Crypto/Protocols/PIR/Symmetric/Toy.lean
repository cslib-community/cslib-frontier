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
  rw [Fintype.card_congr (ToyState.equivProd n)]
  simp [Fintype.card_perm]

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

/-- Involution on server randomness `r : Fin n → Bool` that shifts `r m` by
`xor (D₀ (π.symm m)) (D₁ (π.symm m))`. -/
private def maskEquiv {n : ℕ} (D₀ D₁ : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun r m := xor (r m) (xor (D₀ (π.symm m)) (D₁ (π.symm m)))
  invFun r m := xor (r m) (xor (D₀ (π.symm m)) (D₁ (π.symm m)))
  left_inv r := by
    funext m
    simp
  right_inv r := by
    funext m
    simp

private theorem maskEquiv_maskedDB {n : ℕ} (D₀ D₁ : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (r : Fin n → Bool) :
    (fun i => xor (D₀ i) (maskEquiv D₀ D₁ π r (π i))) = fun i => xor (D₁ i) (r (π i)) := by
  funext i
  simp only [maskEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  cases D₀ i <;> cases D₁ i <;> cases r (π i) <;> rfl

private theorem maskEquiv_comp_query {n k : ℕ} {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}
    (hD : D₀ ∘ Q = D₁ ∘ Q) (π : Equiv.Perm (Fin n)) (r : Fin n → Bool) :
    maskEquiv D₀ D₁ π r ∘ (π ∘ Q) = r ∘ (π ∘ Q) := by
  funext j
  have hDj : D₀ (Q j) = D₁ (Q j) := congrFun hD j
  simp [maskEquiv, Function.comp_apply, hDj]

/-- `toyScheme n k` is perfectly data private (`IsPerfectlyDataPrivate`). -/
theorem toyScheme_isPerfectlyDataPrivate (n k : ℕ) : (toyScheme n k).IsPerfectlyDataPrivate := by
  intro D₀ D₁ Q hD
  simp only [Scheme.clientView, Scheme.clientViewAt, toyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  symm
  rw [PMF.bind_comm]
  symm
  congr 1
  funext π
  rw [← Cslib.Probability.PMF.uniformOfFintype_bind_equiv (maskEquiv D₀ D₁ π)]
  congr 1
  funext r
  rw [maskEquiv_maskedDB D₀ D₁ π r, maskEquiv_comp_query hD π r]

/-! ### Server privacy on injective query tuples and repeated-query counterexample -/

/-- Any two injective query tuples `Q₀, Q₁ : Fin k → Fin n` are related by a permutation
`σ : Equiv.Perm (Fin n)` with `σ ∘ Q₀ = Q₁`. -/
private theorem exists_perm_comp_eq {n k : ℕ} {Q₀ Q₁ : Fin k → Fin n}
    (hQ₀ : Function.Injective Q₀) (hQ₁ : Function.Injective Q₁) :
    ∃ σ : Equiv.Perm (Fin n), σ ∘ Q₀ = Q₁ := by
  classical
  let s₀ : Set (Fin n) := Set.range Q₀
  let s₁ : Set (Fin n) := Set.range Q₁
  let e₀ : Fin k ≃ s₀ := Equiv.ofInjective Q₀ hQ₀
  let e₁ : Fin k ≃ s₁ := Equiv.ofInjective Q₁ hQ₁
  let eRange : s₀ ≃ s₁ := e₀.symm.trans e₁
  have hcard : Fintype.card (s₀ᶜ : Set (Fin n)) = Fintype.card (s₁ᶜ : Set (Fin n)) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, Fintype.card_congr eRange]
  let eCompl : (s₀ᶜ : Set (Fin n)) ≃ (s₁ᶜ : Set (Fin n)) := Fintype.equivOfCardEq hcard
  refine ⟨(Equiv.Set.sumCompl s₀).symm.trans ((Equiv.sumCongr eRange eCompl).trans
    (Equiv.Set.sumCompl s₁)), ?_⟩
  funext j
  have hmem : Q₀ j ∈ s₀ := ⟨j, rfl⟩
  have h₀ : (⟨Q₀ j, hmem⟩ : s₀) = e₀ j := rfl
  have h₁ : (e₁ j : Fin n) = Q₁ j := rfl
  simp [eRange, Equiv.Set.sumCompl_symm_apply_of_mem hmem, h₀, h₁]

/-- `toyScheme n k` is perfectly private on the set of injective query tuples
`{Q | Function.Injective Q}`. -/
theorem toyScheme_isPerfectlyPrivateOn_injective (n k : ℕ) :
    (toyScheme n k).IsPerfectlyPrivateOn {Q | Function.Injective Q} := by
  intro D Q₀ hQ₀ Q₁ hQ₁
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq hQ₀ hQ₁
  simp only [Scheme.serverView, Scheme.serverViewAt, toyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  congr 1
  funext r
  rw [← Cslib.Probability.PMF.uniformOfFintype_bind_equiv (Equiv.mulRight σ)]
  congr 1
  funext π
  have hcomp : ((Equiv.mulRight σ) π) ∘ Q₀ = π ∘ Q₁ := by
    rw [← hσ]
    rfl
  rw [hcomp]

/-- When `k ≤ 1`, every query tuple `Q : Fin k → Fin n` is injective, so `toyScheme n k` is
unconditionally perfectly private (`IsPerfectlyPrivate`). -/
theorem toyScheme_isPerfectlyPrivate_of_le_one {n k : ℕ} (hk : k ≤ 1) :
    (toyScheme n k).IsPerfectlyPrivate := by
  intro D Q₀ Q₁
  have hinj : ∀ Q : Fin k → Fin n, Function.Injective Q := by
    intro Q i j _
    ext
    omega
  exact toyScheme_isPerfectlyPrivateOn_injective n k D Q₀ (hinj Q₀) Q₁ (hinj Q₁)

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
  let D : Fin n → Bool := fun _ => false
  let Q₀ : Fin k → Fin n := fun _ => i₀
  let Q₁ : Fin k → Fin n := fun j => if j = j₀ then i₀ else i₁
  let obs : (Fin n → Bool) × Unit × (Fin k → Fin n) × (Fin k → Bool) → Bool :=
    fun (_, _, τu, _) => decide (τu j₀ = τu j₁)
  have hmap₀ : (ProbComp.eval ((toyScheme n k).serverView D Q₀)).map obs = PMF.pure true := by
    rw [Cslib.Probability.PMF.map_eq_pure_iff]
    intro v hv
    simp only [Scheme.serverView, Scheme.serverViewAt, toyScheme, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hv
    rcases hv with ⟨r, _, π, _, rfl⟩
    simp [obs, Q₀]
  have hmap₁ : (ProbComp.eval ((toyScheme n k).serverView D Q₁)).map obs = PMF.pure false := by
    rw [Cslib.Probability.PMF.map_eq_pure_iff]
    intro v hv
    simp only [Scheme.serverView, Scheme.serverViewAt, toyScheme, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hv
    rcases hv with ⟨r, _, π, _, rfl⟩
    have hj : j₁ ≠ j₀ := by
      fin_index [j₀, j₁]
    have hi : i₀ ≠ i₁ := by
      omega
    simp [obs, Q₁, hj, π.injective.eq_iff, hi]
  exact Cslib.Probability.PMF.ne_of_map_eq_pure hmap₀ hmap₁ (by decide) (hpriv D Q₀ Q₁)

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
  rw [Fintype.card_congr (ParallelToyState.equivProd n k)]
  simp [Fintype.card_perm]

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

/-- Involution on the server randomness family that shifts `r j m` by
`xor (D₀ ((π j).symm m)) (D₁ ((π j).symm m))`. -/
private def parallelMaskEquiv {n k : ℕ} (D₀ D₁ : Fin n → Bool)
    (π : Fin k → Equiv.Perm (Fin n)) : (Fin k → Fin n → Bool) ≃ (Fin k → Fin n → Bool) where
  toFun r j m := xor (r j m) (xor (D₀ ((π j).symm m)) (D₁ ((π j).symm m)))
  invFun r j m := xor (r j m) (xor (D₀ ((π j).symm m)) (D₁ ((π j).symm m)))
  left_inv r := by
    funext j m
    simp
  right_inv r := by
    funext j m
    simp

private theorem parallelMaskEquiv_maskedDB {n k : ℕ} (D₀ D₁ : Fin n → Bool)
    (π : Fin k → Equiv.Perm (Fin n)) (r : Fin k → Fin n → Bool) :
    (fun j i => xor (D₀ i) (parallelMaskEquiv D₀ D₁ π r j (π j i))) =
      fun j i => xor (D₁ i) (r j (π j i)) := by
  funext j i
  simp only [parallelMaskEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  cases D₀ i <;> cases D₁ i <;> cases r j (π j i) <;> rfl

private theorem parallelMaskEquiv_query {n k : ℕ} {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}
    (hD : D₀ ∘ Q = D₁ ∘ Q) (π : Fin k → Equiv.Perm (Fin n)) (r : Fin k → Fin n → Bool)
    (j : Fin k) :
    parallelMaskEquiv D₀ D₁ π r j (π j (Q j)) = r j (π j (Q j)) := by
  have hDj : D₀ (Q j) = D₁ (Q j) := congrFun hD j
  simp [parallelMaskEquiv, hDj]

/-- `parallelToyScheme n k` is perfectly data private (`IsPerfectlyDataPrivate`). -/
theorem parallelToyScheme_isPerfectlyDataPrivate (n k : ℕ) :
    (parallelToyScheme n k).IsPerfectlyDataPrivate := by
  intro D₀ D₁ Q hD
  simp only [Scheme.clientView, Scheme.clientViewAt, parallelToyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  symm
  rw [PMF.bind_comm]
  symm
  congr 1
  funext π
  rw [← Cslib.Probability.PMF.uniformOfFintype_bind_equiv (parallelMaskEquiv D₀ D₁ π)]
  congr 1
  funext r
  simp only [parallelMaskEquiv_maskedDB D₀ D₁ π r, parallelMaskEquiv_query hD π r]

/-- `parallelToyScheme n k` is perfectly private (`IsPerfectlyPrivate`) for every pair of batch
tuples, repeated indices included: composing each `π j` with the transposition of `Q₀ j` and
`Q₁ j` is a bijection on the permutation families that maps one upload to the other. -/
theorem parallelToyScheme_isPerfectlyPrivate (n k : ℕ) :
    (parallelToyScheme n k).IsPerfectlyPrivate := by
  intro D Q₀ Q₁
  obtain ⟨e, he⟩ : ∃ e : (Fin k → Equiv.Perm (Fin n)) ≃ (Fin k → Equiv.Perm (Fin n)),
      ∀ π j, e π j (Q₀ j) = π j (Q₁ j) :=
    ⟨Equiv.piCongrRight fun j => Equiv.mulRight (Equiv.swap (Q₀ j) (Q₁ j)),
      fun π j => by simp⟩
  simp only [Scheme.serverView, Scheme.serverViewAt, parallelToyScheme, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  congr 1
  funext r
  rw [← Cslib.Probability.PMF.uniformOfFintype_bind_equiv e]
  congr 1
  funext π
  simp only [he]

end Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing
