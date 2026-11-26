/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Block
public import CslibFrontier.Crypto.Protocols.PIR.CoveringCode
public import CslibFrontier.Crypto.Protocols.PIR.LinearSummation
public import CslibFrontier.Crypto.Protocols.PIR.Shamir
public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
public import CslibFrontier.Crypto.Protocols.SelectiveFailure
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support

/-!
# Selective failure attacks and immunity in private information retrieval

Standard multi-server private information retrieval (`PIR.Scheme`) guarantees passive query privacy
(`Scheme.IsPrivate`, `Scheme.IsTPrivate`): no server or unauthorized coalition learns the queried
index `i` from the queries it receives. When a malicious server `s₀ : S` actively deviates from
`P.answer s₀ x` by applying a modified answer strategy `malAns : Q → A` (`Scheme.runWithServer`), it
may induce a *selective failure attack* (`Cslib.Crypto.Protocols.SelectiveFailure`): the user's
reconstructed output differs from the true database entry `x i` with a probability that depends on
`i`, leaking `i` through whether the user experiences a reconstruction failure.

Instantiating `SelectiveFailure.Model` on `PIR.Scheme` (`Scheme.selectiveFailureModel`), this module
classifies single-server query-only selective failure immunity and vulnerability across the PIR
constructions of [Chor, Goldreich, Kushilevitz and Sudan][ChorGoldreichKushilevitzSudan1998] under
the explicit non-degeneracy hypotheses required for each family (a singleton index domain cannot
yield positive advantage, and a `RadiusOneCover` with no emulated neighbours reduces to `PIR.cube`):

1. **Immunity of Unbalanced 1-Bit XOR-Sum PIR (`Scheme.HasXorReconstruct`):**
   - In any perfectly correct (`Scheme.IsCorrect`), 1-private (`Scheme.IsPrivate`) one-bit-answer
     scheme satisfying `Scheme.HasXorReconstruct` (`reconstruct i r a = ∑ s, a s` over `Bool`),
     when a single server `s₀` deviates via `malAns : Q → Bool`, the failure indicator
     `decide (out ≠ x i)` on query draw `(r, q)` equals `malAns (q s₀) + P.answer s₀ x (q s₀)`,
     which depends only on `s₀`'s own query `q s₀`. By 1-privacy and
     `SelectiveFailure.Model.isSelectiveFailureFree_of_map_eq`, the scheme is selective-failure free
     (`Scheme.isSelectiveFailureFree_of_hasXorReconstruct`).
   - Consequently, the basic 2-server scheme `PIR.twoServer`, the even-set scheme
     `PIR.evenTwoServer`, the `2 ^ d`-server subcube scheme `PIR.cube`, and Proposition 5's
     answer-compressing scheme `Scheme.sumChunks` are all selective-failure free
     (`isSelectiveFailureFree_twoServer`, `isSelectiveFailureFree_evenTwoServer`,
     `isSelectiveFailureFree_cube`, `Scheme.IsSelectiveFailureFree.sumChunks`).

2. **Vulnerability of Matrix-Balanced `Scheme.rows` PIR (CGKS Section 3.4, Corollary 3) and
   Block-Lifted PIR (`Scheme.toBlock`, Proposition 4):**
   - For any perfectly correct (`P.IsCorrect`) 1-bit XOR-sum scheme (`P.HasXorReconstruct`),
     applying the matrix-balancing transformation `Scheme.rows ρ` multiplies each server's reply by
     `|ρ|` so the user projects onto row `ji.1 : ρ`. A single server `s₀` flipping entry `j₀ : ρ`
     of its reply vector (`Scheme.rowsFlipAttack`) causes a deterministic selective failure for the
     predicate `fun ji => decide (ji.1 = j₀)` on **every** database `x`
     (`Scheme.isDeterministicAttack_rows`), achieving `selectiveFailureAdvantage = 1` between any
     `(j₀, i₀)` and `(j₁, i₁)` with `j₁ ≠ j₀` (`Scheme.selectiveFailureAdvantage_rows_eq_one`).
     Assuming `[Nonempty S]`, `[Nonempty ι]`, and `[Nontrivial ρ]` (so a deviating server, base
     index, and two distinct rows exist), this refutes `IsSelectiveFailureFree`
     (`Scheme.not_isSelectiveFailureFree_rows`, and for `[Nonempty ι]` and `[Nontrivial ρ]`,
     `not_isSelectiveFailureFree_twoServer_rows`, `not_isSelectiveFailureFree_cube_rows`).
   - Dually, for any correct 1-bit XOR-sum scheme `P`, when `P.toBlock κ` is used to retrieve a
     single bit on `ι × κ` via `Scheme.toBitScheme`, flipping block coordinate `b₀ : κ` at server
     `s₀` causes a deterministic selective failure iff the target coordinate within the block is
     `b₀` (`Scheme.isDeterministicAttack_toBlock_toBitScheme`), refuting `IsSelectiveFailureFree`
     whenever `[Nonempty S]`, `[Nonempty ι]`, and `[Nontrivial κ]`
     (`Scheme.not_isSelectiveFailureFree_toBlock_toBitScheme`).

3. **Vulnerability of Covering-Code Subcube Emulation PIR (`RadiusOneCover.scheme`,
   CGKS Section 3.3, Theorem 1 & Corollary 2):**
   - In `K.scheme ι`, each server `s` returns its own subcube bit together with `|M| · |ι|` emulated
     neighbour bits. Whenever `K` has an actually used emulated-neighbour slot
     `K.cover w₀ = (s₀, some r₀)`, injectivity of `K.cover` ensures that `w₀` is the unique vertex
     of the `d`-cube read from direction `r₀` of server `s₀`. Flipping entry `(r₀, k₀)` of `s₀`'s
     emulated table (`RadiusOneCover.coverFlipAttack`) causes a deterministic selective failure for
     `fun i => decide (i (K.dir s₀ r₀) = k₀)` on **every** database `x`
     (`RadiusOneCover.isDeterministicAttack_scheme`), achieving advantage `1` for queries differing
     at coordinate `K.dir s₀ r₀` and refuting `IsSelectiveFailureFree` whenever `[Nontrivial ι]`
     (`RadiusOneCover.not_isSelectiveFailureFree_scheme`). Both Corollary 2 covers have such an
     emulated slot, so `cubeThree.scheme` and `cubeFour.scheme` fail `IsSelectiveFailureFree`
     whenever `[Nontrivial ι]` (`not_isSelectiveFailureFree_cubeThree`,
     `not_isSelectiveFailureFree_cubeFour`).

4. **Vulnerability of Polynomial Shamir `t`-Private PIR (`PIR.shamir` and `PIR.shamirCube`,
   from `PIR.Shamir`, motivated by [ChorGoldreichKushilevitzSudan1998] Sections 1.1 and 2.2):**
   - Even when a polynomial PIR scheme sends only a single field element `F` per server and is
     `t`-private against coalitions of up to `t` servers, reconstruction tests `= 1` in `F`
     (`decide (Shamir.Polynomial.reconstruct params.point ans = 1)`). For any field offset `Δ : F`
     with `Δ ≠ 0` and `Δ ≠ 1`, a single server `s₀` adding
     `Δ * (lagrangeWeightAtZero params.point s₀)⁻¹` to its honest answer
     (`Scheme.lagrangeShiftAttack`) shifts the reconstructed constant term from
     `if x i then 1 else 0` to `(if x i then 1 else 0) + Δ ≠ 1`. The user therefore always outputs
     `false`, suffering a reconstruction failure **if and only if `x i = true`**
     (`isDeterministicAttack_shamir`, and under
     `Fintype.card D * params.threshold < Fintype.card S`, `isDeterministicAttack_shamirCube`),
     yielding `selectiveFailureAdvantage = 1` on any non-constant database pair `x i₀ ≠ x i₁`.
     Whenever `0 < params.threshold` (which yields `|F| > |S| ≥ 2` and hence `Δ ≠ 0, 1`) and
     `[Nontrivial ι]` (plus `[Nonempty D]` and `Fintype.card D * params.threshold < Fintype.card S`
     for `PIR.shamirCube`), this refutes `IsSelectiveFailureFree`
     (`not_isSelectiveFailureFree_shamir`, `not_isSelectiveFailureFree_shamirCube`).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme.runWithServer`: execution of a PIR scheme when server `s₀`
  applies a modified answer function `malAns : Q → A`.
* `Cslib.Crypto.Protocols.PIR.Scheme.selectiveFailureModel`,
  `Cslib.Crypto.Protocols.PIR.Scheme.failureGame`,
  `Cslib.Crypto.Protocols.PIR.Scheme.failureProb`,
  `Cslib.Crypto.Protocols.PIR.Scheme.selectiveFailureAdvantage`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsSelectiveFailureFree`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsDeterministicAttack`: instantiation of
  `SelectiveFailure.Model` for `PIR.Scheme`.
* `Cslib.Crypto.Protocols.PIR.Scheme.rowsFlipAttack`,
  `Cslib.Crypto.Protocols.PIR.Scheme.toBlockBitFlipAttack`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.coverFlipAttack`,
  `Cslib.Crypto.Protocols.PIR.Scheme.lagrangeShiftAttack`: explicit single-server selective failure
  attacks on `Scheme.rows`, `Scheme.toBlock`, `RadiusOneCover.scheme`, and Lagrange-interpolated
  polynomial PIR (`PIR.shamir`, `PIR.shamirCube`).

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.isSelectiveFailureFree_of_hasXorReconstruct`,
  `Cslib.Crypto.Protocols.PIR.isSelectiveFailureFree_twoServer`,
  `Cslib.Crypto.Protocols.PIR.isSelectiveFailureFree_evenTwoServer`,
  `Cslib.Crypto.Protocols.PIR.isSelectiveFailureFree_cube`,
  `Cslib.Crypto.Protocols.PIR.Scheme.IsSelectiveFailureFree.sumChunks`: selective failure immunity
  of 1-bit XOR-sum PIR schemes.
* `Cslib.Crypto.Protocols.PIR.Scheme.isDeterministicAttack_rows`,
  `Cslib.Crypto.Protocols.PIR.Scheme.selectiveFailureAdvantage_rows_eq_one`,
  `Cslib.Crypto.Protocols.PIR.Scheme.not_isSelectiveFailureFree_rows`,
  `Cslib.Crypto.Protocols.PIR.not_isSelectiveFailureFree_twoServer_rows`,
  `Cslib.Crypto.Protocols.PIR.not_isSelectiveFailureFree_cube_rows`: selective failure vulnerability
  of matrix-balanced `Scheme.rows` PIR.
* `Cslib.Crypto.Protocols.PIR.RadiusOneCover.isDeterministicAttack_scheme`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.selectiveFailureAdvantage_scheme_eq_one`,
  `Cslib.Crypto.Protocols.PIR.RadiusOneCover.not_isSelectiveFailureFree_scheme`,
  `Cslib.Crypto.Protocols.PIR.not_isSelectiveFailureFree_cubeThree`,
  `Cslib.Crypto.Protocols.PIR.not_isSelectiveFailureFree_cubeFour`: selective failure vulnerability
  of covering-code subcube emulation PIR.
* `Cslib.Crypto.Protocols.PIR.isDeterministicAttack_shamir`,
  `Cslib.Crypto.Protocols.PIR.not_isSelectiveFailureFree_shamir`,
  `Cslib.Crypto.Protocols.PIR.isDeterministicAttack_shamirCube`,
  `Cslib.Crypto.Protocols.PIR.not_isSelectiveFailureFree_shamirCube`: selective failure
  vulnerability of `t`-private polynomial Shamir PIR.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998]
* [A. Shamir, *How to Share a Secret*][Shamir1979]
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability
open scoped NNReal
open Cslib.Crypto.Protocols.SecretSharing

namespace Scheme

variable {ι S R Q A β : Type}

/-! ### 1. Single-server active deviation model for `PIR.Scheme` -/

section Model

variable [DecidableEq S] (P : Scheme ι S R Q A β)

/-- Execution of the PIR scheme `P` on database `x` and index `i` when server `s₀` deviates from
`P.answer s₀ x` by answering with `malAns : Q → A` while all other servers `s ≠ s₀` answer honestly.
-/
@[expose] def runWithServer (x : ι → β) (s₀ : S) (malAns : Q → A) (i : ι) : ProbComp β :=
  (fun rq =>
    P.reconstruct i rq.1
      (Function.update (fun s => P.answer s x (rq.2 s)) s₀ (malAns (rq.2 s₀)))) <$> P.query i

theorem eval_runWithServer (x : ι → β) (s₀ : S) (malAns : Q → A) (i : ι) :
    ProbComp.eval (P.runWithServer x s₀ malAns i) =
      (ProbComp.eval (P.query i)).map (fun rq =>
        P.reconstruct i rq.1
          (Function.update (fun s => P.answer s x (rq.2 s)) s₀ (malAns (rq.2 s₀)))) :=
  ProbComp.eval_map _ _

/-- When server `s₀` uses its honest answer function `P.answer s₀ x`, `runWithServer` has the same
output distribution as the honest execution `P.run x i`. -/
@[simp] theorem eval_runWithServer_answer (x : ι → β) (s₀ : S) (i : ι) :
    ProbComp.eval (P.runWithServer x s₀ (P.answer s₀ x) i) = ProbComp.eval (P.run x i) := by
  simp only [eval_runWithServer, eval_run, Function.update_eq_self]

/-- Protocol-agnostic `SelectiveFailure.Model` instantiated for single-server active deviations in
`P` on a fixed database `x : ι → β`:
* the secret is the queried index `i : ι`;
* an active deviation `(s₀, malAns) : S × (Q → A)` specifies the deviating server `s₀` and its
  modified answer function `malAns`;
* the ideal output on `i` is `x i`. -/
@[expose] def selectiveFailureModel (x : ι → β) :
    SelectiveFailure.Model ι (S × (Q → A)) β where
  target := x
  exec dev i := P.runWithServer x dev.1 dev.2 i

variable [DecidableEq β]

/-- The Boolean selective-failure experiment (`Game`) when server `s₀` answers with `malAns` on
database `x` and user query `i`. -/
@[expose] noncomputable def failureGame (x : ι → β) (s₀ : S) (malAns : Q → A) (i : ι) : Game :=
  (P.selectiveFailureModel x).failureGame (s₀, malAns) i

/-- The probability (`ℝ≥0`) that the user reconstructs an output `out ≠ x i` when server `s₀`
answers with `malAns`. -/
@[expose] noncomputable def failureProb (x : ι → β) (s₀ : S) (malAns : Q → A) (i : ι) : ℝ≥0 :=
  (P.selectiveFailureModel x).failureProb (s₀, malAns) i

/-- The selective-failure distinguishing advantage (`ℝ≥0`) between indices `i₀` and `i₁` on database
`x` when server `s₀` answers with `malAns`. -/
@[expose] noncomputable def selectiveFailureAdvantage (x : ι → β) (s₀ : S) (malAns : Q → A)
    (i₀ i₁ : ι) : ℝ≥0 :=
  (P.selectiveFailureModel x).advantage (s₀, malAns) i₀ i₁

/-- A PIR scheme `P` is *selective-failure free* if for every database `x : ι → β`, every server
`s₀ : S`, and every modified answer function `malAns : Q → A`, the selective-failure distinguishing
advantage between any two indices `i₀, i₁ : ι` is zero. -/
@[expose] def IsSelectiveFailureFree : Prop :=
  ∀ x : ι → β, (P.selectiveFailureModel x).IsSelectiveFailureFree

/-- Server `s₀`'s answer strategy `malAns` is a *deterministic selective failure attack* on database
`x` for predicate `pred : ι → Bool` if the user suffers a reconstruction failure (`out ≠ x i`) on
query `i` with probability `1` when `pred i = true` and `0` when `pred i = false`. -/
@[expose] def IsDeterministicAttack (x : ι → β) (s₀ : S) (malAns : Q → A)
    (pred : ι → Bool) : Prop :=
  (P.selectiveFailureModel x).IsDeterministicAttack (s₀, malAns) pred

theorem isSelectiveFailureFree_iff :
    P.IsSelectiveFailureFree ↔
      ∀ (x : ι → β) (s₀ : S) (malAns : Q → A) (i₀ i₁ : ι),
        P.failureGame x s₀ malAns i₀ = P.failureGame x s₀ malAns i₁ := by
  refine forall_congr' fun x => ?_
  rw [(P.selectiveFailureModel x).isSelectiveFailureFree_iff, Prod.forall]
  rfl

variable {P}

theorem IsDeterministicAttack.selectiveFailureAdvantage_eq_one {x : ι → β} {s₀ : S}
    {malAns : Q → A} {pred : ι → Bool} (h : P.IsDeterministicAttack x s₀ malAns pred)
    {i₀ i₁ : ι} (hne : pred i₀ ≠ pred i₁) :
    P.selectiveFailureAdvantage x s₀ malAns i₀ i₁ = 1 :=
  SelectiveFailure.Model.IsDeterministicAttack.advantage_eq_one h hne

theorem IsDeterministicAttack.not_isSelectiveFailureFree {x : ι → β} {s₀ : S}
    {malAns : Q → A} {pred : ι → Bool} (h : P.IsDeterministicAttack x s₀ malAns pred)
    {i₀ i₁ : ι} (hne : pred i₀ ≠ pred i₁) :
    ¬ P.IsSelectiveFailureFree := fun hfree =>
  SelectiveFailure.Model.IsDeterministicAttack.not_isSelectiveFailureFree h hne (hfree x)

end Model

/-! ### 2. Selective failure immunity of unbalanced 1-bit XOR-sum PIR -/

section XorImmunity

variable [Fintype S] [DecidableEq S] {P : Scheme ι S R Q Bool}

/-- Updating a `Bool`-valued function `f : S → Bool` at `s₀` to `b` shifts its `Finset.univ` XOR sum
by `b + f s₀`. -/
private theorem sum_update_bool (f : S → Bool) (s₀ : S) (b : Bool) :
    (∑ s : S, Function.update f s₀ b s) = (∑ s : S, f s) + (b + f s₀) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀),
    ← Finset.add_sum_erase _ f (Finset.mem_univ s₀), Function.update_self,
    Finset.sum_congr rfl fun s hs => Function.update_of_ne (Finset.ne_of_mem_erase hs) b f]
  nth_rw 1 [show b = f s₀ + (b + f s₀) by cases b <;> cases f s₀ <;> decide]
  abel

/-- In `Bool` (`BooleanRing`), `decide (a + δ ≠ a) = δ`. -/
private theorem decide_add_ne_self_bool (a δ : Bool) : decide (a + δ ≠ a) = δ := by
  cases a <;> cases δ <;> decide

/-- Under XOR-sum reconstruction (`HasXorReconstruct`) and `IsCorrect`, the failure game when server
`s₀` answers with `malAns` factors through `s₀`'s marginal query distribution `P.serverQuery s₀ i`
via the local answer-flip indicator `fun q₀ => malAns q₀ + P.answer s₀ x q₀`. -/
theorem failureGame_eq_map_serverQuery (hcorrect : P.IsCorrect) (hxor : P.HasXorReconstruct)
    (x : ι → Bool) (s₀ : S) (malAns : Q → Bool) (i : ι) :
    P.failureGame x s₀ malAns i =
      (ProbComp.eval (P.serverQuery s₀ i)).map (fun q₀ => malAns q₀ + P.answer s₀ x q₀) := by
  have hxor' := (P.hasXorReconstruct_iff).mp hxor
  rw [failureGame, SelectiveFailure.Model.failureGame, SelectiveFailure.Model.eval_failureRun,
    selectiveFailureModel, eval_runWithServer, eval_serverQuery, PMF.map_comp, PMF.map_comp]
  refine Probability.PMF.map_congr_on_support _ _ _ fun rq hrq => ?_
  dsimp only [Function.comp_apply]
  rw [hxor', sum_update_bool, ← hxor' i rq.1 (fun s => P.answer s x (rq.2 s)),
    hcorrect.reconstruct_eq x i hrq, decide_add_ne_self_bool]

/-- **Immunity of 1-bit XOR-sum PIR to selective failure attacks.** Every perfectly correct,
1-private one-bit-answer scheme with XOR-sum reconstruction (`HasXorReconstruct`) is
selective-failure free: a single deviating server can flip the user's output bit only with a
probability determined by its own query marginal, which is independent of `i` by `IsPrivate`. -/
theorem isSelectiveFailureFree_of_hasXorReconstruct (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) (hxor : P.HasXorReconstruct) :
    P.IsSelectiveFailureFree := fun x =>
  (P.selectiveFailureModel x).isSelectiveFailureFree_of_map_eq
    (view := fun dev i => P.serverQuery dev.1 i)
    (err := fun dev q₀ => dev.2 q₀ + P.answer dev.1 x q₀)
    (fun dev i₀ i₁ => hprivate.eval_serverQuery_eq dev.1 i₀ i₁)
    (fun dev i => failureGame_eq_map_serverQuery hcorrect hxor x dev.1 dev.2 i)

/-- Proposition 5's answer-compressing transformation `Scheme.sumChunks` produces a
selective-failure-free scheme from any correct, private XOR-sum scheme. -/
theorem IsSelectiveFailureFree.sumChunks (m : ℕ) {P : Scheme (Option ι) S R Q Bool}
    (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) (hxor : P.HasXorReconstruct) :
    (P.sumChunks m).IsSelectiveFailureFree :=
  isSelectiveFailureFree_of_hasXorReconstruct (hcorrect.sumChunks m hxor) (hprivate.sumChunks m)
    (hasXorReconstruct_sumChunks m P)

end XorImmunity

/-! ### 3. Selective failure attacks on `Scheme.rows` and `Scheme.toBlock` -/

section RowsAndBlockAttack

variable {ρ κ : Type} [Fintype S] [DecidableEq S] {P : Scheme ι S R Q Bool}

/-- Single-row bit-flip attack on `P.rows ρ`
([CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998]): server `s₀` computes its honest reply
vector `(P.rows ρ).answer s₀ x q` and flips the single entry at row `j₀ : ρ`. -/
@[expose] def rowsFlipAttack [DecidableEq ρ] (P : Scheme ι S R Q Bool) (x : ρ × ι → Bool)
    (s₀ : S) (j₀ : ρ) (q : Q) : ρ → Bool :=
  Function.update ((P.rows ρ).answer s₀ x q) j₀ (!((P.rows ρ).answer s₀ x q j₀))

/-- **Deterministic selective failure on `P.rows ρ`.** If `P` is a correct one-bit scheme with
XOR-sum reconstruction (`HasXorReconstruct`), then for **every** database `x : ρ × ι → Bool`,
server `s₀` flipping row `j₀` via `rowsFlipAttack P x s₀ j₀` causes the user's reconstruction of
`x ji` to fail with probability `1` when `ji.1 = j₀` and `0` when `ji.1 ≠ j₀`. -/
theorem isDeterministicAttack_rows [DecidableEq ρ] (hcorrect : P.IsCorrect)
    (hxor : P.HasXorReconstruct) (x : ρ × ι → Bool) (s₀ : S) (j₀ : ρ) :
    (P.rows ρ).IsDeterministicAttack x s₀ (P.rowsFlipAttack x s₀ j₀)
      (fun ji => decide (ji.1 = j₀)) := by
  have hxor' := (P.hasXorReconstruct_iff).mp hxor
  simp only [IsDeterministicAttack, SelectiveFailure.Model.isDeterministicAttack_iff,
    selectiveFailureModel, eval_runWithServer]
  rintro ⟨j, i⟩ _ hout
  obtain ⟨⟨r, q⟩, hrq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hout
  rw [query_rows] at hrq
  rw [reconstruct_rows,
    funext fun s => Function.apply_update (fun _ (r : ρ → Bool) => r j) _ s₀ _ s]
  simp only [answer_rows]
  rw [hxor', sum_update_bool,
    ← hxor' i r (fun s => P.answer s (fun i' => x (j, i')) (q s)),
    hcorrect.reconstruct_eq (fun i' => x (j, i')) i hrq, decide_add_ne_self_bool]
  rcases eq_or_ne j j₀ with rfl | hj
  · simp only [rowsFlipAttack, Function.update_self, answer_rows, decide_true]
    cases P.answer s₀ (fun i' => x (j, i')) (q s₀) <;> decide
  · simp only [rowsFlipAttack, Function.update_of_ne hj, answer_rows, hj, decide_false]
    cases P.answer s₀ (fun i' => x (j, i')) (q s₀) <;> decide

/-- Flipping row `j₀` in `P.rows ρ` distinguishes any query `(j₀, i₀)` in row `j₀` from any query
`(j₁, i₁)` in row `j₁ ≠ j₀` with selective-failure advantage `1`. -/
theorem selectiveFailureAdvantage_rows_eq_one [DecidableEq ρ] (hcorrect : P.IsCorrect)
    (hxor : P.HasXorReconstruct) (x : ρ × ι → Bool) (s₀ : S) {j₀ j₁ : ρ} (hj : j₀ ≠ j₁)
    (i₀ i₁ : ι) :
    (P.rows ρ).selectiveFailureAdvantage x s₀ (P.rowsFlipAttack x s₀ j₀)
      (j₀, i₀) (j₁, i₁) = 1 :=
  (isDeterministicAttack_rows hcorrect hxor x s₀ j₀).selectiveFailureAdvantage_eq_one
    (by simp [hj.symm])

/-- **Matrix-balanced `Scheme.rows` PIR is not selective-failure free** whenever there is at least
one server, one column index, and two distinct rows (`[Nontrivial ρ]`). -/
theorem not_isSelectiveFailureFree_rows [Nonempty S] [Nonempty ι] [Nontrivial ρ]
    (hcorrect : P.IsCorrect) (hxor : P.HasXorReconstruct) :
    ¬ (P.rows ρ).IsSelectiveFailureFree := by
  classical
  rcases ‹Nonempty S›, ‹Nonempty ι›, exists_pair_ne ρ with ⟨⟨s₀⟩, ⟨i₀⟩, j₀, j₁, hj⟩
  exact (isDeterministicAttack_rows hcorrect hxor (fun _ => false) s₀ j₀).not_isSelectiveFailureFree
    (i₀ := (j₀, i₀)) (i₁ := (j₁, i₀)) (by simp [hj.symm])

/-- Single-coordinate bit-flip attack on `(P.toBlock κ).toBitScheme` (Proposition 4,
[CGKS, Section 4.1][ChorGoldreichKushilevitzSudan1998]): server `s₀` flips coordinate `b₀ : κ` of
its block reply. -/
@[expose] def toBlockBitFlipAttack [DecidableEq κ] (P : Scheme ι S R Q Bool) (x : ι × κ → Bool)
    (s₀ : S) (b₀ : κ) (q : Q) : κ → Bool :=
  Function.update ((P.toBlock κ).toBitScheme.answer s₀ x q) b₀
    (!((P.toBlock κ).toBitScheme.answer s₀ x q b₀))

/-- **Deterministic selective failure on `(P.toBlock κ).toBitScheme`.** Flipping block coordinate
`b₀ : κ` at server `s₀` causes the user's bit retrieval on `ib : ι × κ` to fail iff `ib.2 = b₀`. -/
theorem isDeterministicAttack_toBlock_toBitScheme [DecidableEq κ] (hcorrect : P.IsCorrect)
    (hxor : P.HasXorReconstruct) (x : ι × κ → Bool) (s₀ : S) (b₀ : κ) :
    (P.toBlock κ).toBitScheme.IsDeterministicAttack x s₀ (P.toBlockBitFlipAttack x s₀ b₀)
      (fun ib => decide (ib.2 = b₀)) := by
  have hxor' := (P.hasXorReconstruct_iff).mp hxor
  simp only [IsDeterministicAttack, SelectiveFailure.Model.isDeterministicAttack_iff,
    selectiveFailureModel, eval_runWithServer]
  rintro ⟨i, b⟩ _ hout
  obtain ⟨⟨r, q⟩, hrq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hout
  rw [query_toBitScheme, query_toBlock] at hrq
  rw [reconstruct_toBitScheme, reconstruct_toBlock,
    funext fun s => Function.apply_update (fun _ (r : κ → Bool) => r b) _ s₀ _ s]
  simp only [answer_toBitScheme, answer_toBlock]
  rw [hxor', sum_update_bool,
    ← hxor' i r (fun s => P.answer s (fun i' => x (i', b)) (q s)),
    hcorrect.reconstruct_eq (fun i' => x (i', b)) i hrq, decide_add_ne_self_bool]
  rcases eq_or_ne b b₀ with rfl | hb
  · simp only [toBlockBitFlipAttack, Function.update_self, answer_toBitScheme, answer_toBlock,
      decide_true]
    cases P.answer s₀ (fun i' => x (i', b)) (q s₀) <;> decide
  · simp only [toBlockBitFlipAttack, Function.update_of_ne hb, answer_toBitScheme, answer_toBlock,
      hb, decide_false]
    cases P.answer s₀ (fun i' => x (i', b)) (q s₀) <;> decide

/-- Block-lifted bit retrieval `(P.toBlock κ).toBitScheme` is not selective-failure free whenever
`S` and `ι` are nonempty and the block coordinate type `κ` has at least two coordinates. -/
theorem not_isSelectiveFailureFree_toBlock_toBitScheme [Nonempty S] [Nonempty ι] [Nontrivial κ]
    (hcorrect : P.IsCorrect) (hxor : P.HasXorReconstruct) :
    ¬ (P.toBlock κ).toBitScheme.IsSelectiveFailureFree := by
  classical
  rcases ‹Nonempty S›, ‹Nonempty ι›, exists_pair_ne κ with ⟨⟨s₀⟩, ⟨i₀⟩, b₀, b₁, hb⟩
  exact (isDeterministicAttack_toBlock_toBitScheme hcorrect hxor (fun _ => false) s₀
    b₀).not_isSelectiveFailureFree (i₀ := (i₀, b₀)) (i₁ := (i₀, b₁)) (by simp [hb.symm])

end RowsAndBlockAttack

end Scheme

/-! ### Concrete corollaries for `PIR.twoServer`, `PIR.evenTwoServer`, and `PIR.cube` -/

section BasicAndCubeCorollaries

variable {ι D ρ : Type} [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]

/-- **The basic 2-server PIR scheme (`PIR.twoServer`) is selective-failure free.** -/
theorem isSelectiveFailureFree_twoServer : (twoServer ι).IsSelectiveFailureFree :=
  Scheme.isSelectiveFailureFree_of_hasXorReconstruct isCorrect_twoServer isPrivate_twoServer
    (Scheme.hasXorReconstruct_twoServer ι)

/-- **The even-set 2-server PIR scheme (`PIR.evenTwoServer`) is selective-failure free.** -/
theorem isSelectiveFailureFree_evenTwoServer (h₀ : ι) :
    (evenTwoServer h₀).IsSelectiveFailureFree :=
  Scheme.isSelectiveFailureFree_of_hasXorReconstruct (isCorrect_evenTwoServer h₀)
    (isPrivate_evenTwoServer h₀) ((Scheme.hasXorReconstruct_iff (evenTwoServer h₀)).mpr
      fun i r a => by
        rw [(isLinearSummation_evenTwoServer h₀).reconstruct_eq i r a, Fintype.sum_bool, add_comm])

/-- **The `2 ^ d`-server subcube PIR scheme (`PIR.cube`) is selective-failure free.** -/
theorem isSelectiveFailureFree_cube : (cube D ι).IsSelectiveFailureFree :=
  Scheme.isSelectiveFailureFree_of_hasXorReconstruct isCorrect_cube isPrivate_cube
    (Scheme.hasXorReconstruct_cube D ι)

/-- **Matrix-balanced 2-server PIR (`(twoServer ι).rows ρ`) is vulnerable to selective failure
attacks** whenever `ι` is nonempty and `ρ` has at least two rows. -/
theorem not_isSelectiveFailureFree_twoServer_rows [Nonempty ι] [Nontrivial ρ] :
    ¬ ((twoServer ι).rows ρ).IsSelectiveFailureFree :=
  Scheme.not_isSelectiveFailureFree_rows isCorrect_twoServer
    (Scheme.hasXorReconstruct_twoServer ι)

/-- **Matrix-balanced `2 ^ d`-server subcube PIR (`(cube D ι).rows ρ`, CGKS Section 3.4,
Corollary 3) is vulnerable to selective failure attacks** whenever `ι` is nonempty and `ρ` has at
least two rows. -/
theorem not_isSelectiveFailureFree_cube_rows [Nonempty ι] [Nontrivial ρ] :
    ¬ ((cube D ι).rows ρ).IsSelectiveFailureFree :=
  Scheme.not_isSelectiveFailureFree_rows isCorrect_cube (Scheme.hasXorReconstruct_cube D ι)

end BasicAndCubeCorollaries

/-! ### 4. Selective failure attacks on covering-code PIR (`RadiusOneCover.scheme`) -/

namespace RadiusOneCover

variable {S D M ι : Type} [DecidableEq S] [Fintype D] [DecidableEq D] [DecidableEq M]
  [Fintype ι] [DecidableEq ι] (K : RadiusOneCover S D M)

/-- Single-entry emulated-neighbour bit-flip attack on `K.scheme ι`
([CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998]): server `s₀` computes its honest answer
`(b, f) = (K.scheme ι).answer s₀ x q` and flips entry `(r₀, k₀)` of its emulated neighbour answer
table `f : M → ι → Bool`. -/
@[expose] noncomputable def coverFlipAttack (x : (D → ι) → Bool) (s₀ : S) (r₀ : M) (k₀ : ι)
    (q : D → ι → Bool) : Bool × (M → ι → Bool) :=
  let ans := (K.scheme ι).answer s₀ x q
  (ans.1, Function.update ans.2 r₀ (Function.update (ans.2 r₀) k₀ (!(ans.2 r₀ k₀))))

/-- On every cube vertex `w ≠ w₀` where `K.cover w₀ = (s₀, some r₀)`, `K.readAnswer` on the
perturbed answer profile agrees with `K.readAnswer` on the honest answer profile. -/
private theorem readAnswer_update_coverFlipAttack_of_ne (x : (D → ι) → Bool) (s₀ : S) (r₀ : M)
    (k₀ : ι) (i : D → ι) (q : S → D → ι → Bool) {w w₀ : D → Bool}
    (hw₀ : K.cover w₀ = (s₀, some r₀)) (hne : w ≠ w₀) :
    K.readAnswer i (K.cover w)
        (Function.update (fun s => (K.scheme ι).answer s x (q s)) s₀
          (K.coverFlipAttack x s₀ r₀ k₀ (q s₀))) =
      K.readAnswer i (K.cover w) (fun s => (K.scheme ι).answer s x (q s)) := by
  have hcov_ne : K.cover w ≠ (s₀, some r₀) := fun h => hne (K.cover_injective (h.trans hw₀.symm))
  rcases hcov : K.cover w with ⟨s, _ | r⟩ <;> by_cases hs : s = s₀ <;>
    simp_all [readAnswer, coverFlipAttack]

/-- At the unique vertex `w₀` with `K.cover w₀ = (s₀, some r₀)`, `K.readAnswer` on the perturbed
answer profile equals `!(honest)` when `i (K.dir s₀ r₀) = k₀` and `honest` otherwise. -/
private theorem readAnswer_update_coverFlipAttack_self (x : (D → ι) → Bool) (s₀ : S) (r₀ : M)
    (k₀ : ι) (i : D → ι) (q : S → D → ι → Bool) {w₀ : D → Bool}
    (hw₀ : K.cover w₀ = (s₀, some r₀)) :
    K.readAnswer i (K.cover w₀)
        (Function.update (fun s => (K.scheme ι).answer s x (q s)) s₀
          (K.coverFlipAttack x s₀ r₀ k₀ (q s₀))) =
      K.readAnswer i (K.cover w₀) (fun s => (K.scheme ι).answer s x (q s)) +
        decide (i (K.dir s₀ r₀) = k₀) := by
  rw [hw₀]
  by_cases hik : i (K.dir s₀ r₀) = k₀
  · simp only [readAnswer, Function.update_self, coverFlipAttack, hik, decide_true]
    cases ((K.scheme ι).answer s₀ x (q s₀)).2 r₀ k₀ <;> rfl
  · simp only [readAnswer, Function.update_self, coverFlipAttack, hik, decide_false,
      Function.update_of_ne hik]
    exact (add_zero _).symm

/-- **Deterministic selective failure on `RadiusOneCover.scheme` (CGKS Section 3.3, Theorem 1).**
Whenever server `s₀` emulates cube vertex `w₀` along direction `r₀` (`K.cover w₀ = (s₀, some r₀)`),
flipping entry `(r₀, k₀)` via `K.coverFlipAttack x s₀ r₀ k₀` causes a reconstruction failure on
query `i : D → ι` with probability `1` if `i (K.dir s₀ r₀) = k₀` and `0` if
`i (K.dir s₀ r₀) ≠ k₀`, on **every** database `x`. -/
theorem isDeterministicAttack_scheme (x : (D → ι) → Bool) {w₀ : D → Bool} {s₀ : S} {r₀ : M}
    (hw₀ : K.cover w₀ = (s₀, some r₀)) (k₀ : ι) :
    (K.scheme ι).IsDeterministicAttack x s₀ (K.coverFlipAttack x s₀ r₀ k₀)
      (fun i => decide (i (K.dir s₀ r₀) = k₀)) := by
  simp only [Scheme.IsDeterministicAttack, SelectiveFailure.Model.isDeterministicAttack_iff,
    Scheme.selectiveFailureModel, Scheme.eval_runWithServer]
  intro i _ hout
  obtain ⟨⟨r, q⟩, hrq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hout
  have hsum :
      (K.scheme ι).reconstruct i r
        (Function.update (fun s => (K.scheme ι).answer s x (q s)) s₀
          (K.coverFlipAttack x s₀ r₀ k₀ (q s₀))) =
        (K.scheme ι).reconstruct i r (fun s => (K.scheme ι).answer s x (q s)) +
          decide (i (K.dir s₀ r₀) = k₀) := by
    rw [K.reconstruct_scheme, K.reconstruct_scheme,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w₀),
      K.readAnswer_update_coverFlipAttack_self x s₀ r₀ k₀ i q hw₀,
      Finset.sum_congr rfl fun w hw =>
        K.readAnswer_update_coverFlipAttack_of_ne x s₀ r₀ k₀ i q hw₀ (Finset.ne_of_mem_erase hw)]
    abel
  rw [hsum, K.isCorrect_scheme.reconstruct_eq x i hrq, Scheme.decide_add_ne_self_bool]

/-- Flipping entry `(r₀, k₀)` in `K.scheme ι` distinguishes any cube query `i₀` with
`i₀ (K.dir s₀ r₀) = k₀` from any `i₁` with `i₁ (K.dir s₀ r₀) ≠ k₀` with advantage `1`. -/
theorem selectiveFailureAdvantage_scheme_eq_one (x : (D → ι) → Bool) {w₀ : D → Bool} {s₀ : S}
    {r₀ : M} (hw₀ : K.cover w₀ = (s₀, some r₀)) (k₀ : ι) {i₀ i₁ : D → ι}
    (hi₀ : i₀ (K.dir s₀ r₀) = k₀) (hi₁ : i₁ (K.dir s₀ r₀) ≠ k₀) :
    (K.scheme ι).selectiveFailureAdvantage x s₀ (K.coverFlipAttack x s₀ r₀ k₀) i₀ i₁ = 1 :=
  (K.isDeterministicAttack_scheme x hw₀ k₀).selectiveFailureAdvantage_eq_one (by simp [hi₀, hi₁])

omit [DecidableEq M] in
/-- **Covering-code PIR is not selective-failure free** whenever `[Nontrivial ι]` and at least one
cube vertex `w₀` is covered via an emulated neighbour direction `K.cover w₀ = (s₀, some r₀)`. -/
theorem not_isSelectiveFailureFree_scheme [Nontrivial ι]
    {w₀ : D → Bool} {s₀ : S} {r₀ : M} (hw₀ : K.cover w₀ = (s₀, some r₀)) :
    ¬ (K.scheme ι).IsSelectiveFailureFree := by
  classical
  obtain ⟨k₀, k₁, hk⟩ := exists_pair_ne ι
  exact (K.isDeterministicAttack_scheme (fun _ => false) hw₀ k₀).not_isSelectiveFailureFree
    (i₀ := fun _ => k₀) (i₁ := fun _ => k₁) (by simp [hk.symm])

end RadiusOneCover

section CorollaryTwoVulnerability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- **CGKS Corollary 2's 2-server `O(n ^ (1 / 3))` covering-code scheme
(`RadiusOneCover.cubeThree.scheme`) is vulnerable to selective failure attacks.** -/
theorem not_isSelectiveFailureFree_cubeThree :
    ¬ (RadiusOneCover.cubeThree.scheme ι).IsSelectiveFailureFree :=
  RadiusOneCover.cubeThree.not_isSelectiveFailureFree_scheme
    (w₀ := ![true, false, false]) (s₀ := false) (r₀ := 0) rfl

/-- **CGKS Corollary 2's 4-server `O(n ^ (1 / 4))` covering-code scheme
(`RadiusOneCover.cubeFour.scheme`) is vulnerable to selective failure attacks.** -/
theorem not_isSelectiveFailureFree_cubeFour :
    ¬ (RadiusOneCover.cubeFour.scheme ι).IsSelectiveFailureFree :=
  RadiusOneCover.cubeFour.not_isSelectiveFailureFree_scheme
    (w₀ := ![false, true, false, false]) (s₀ := (false, false)) (r₀ := 0) rfl

end CorollaryTwoVulnerability

/-! ### 5. Selective failure attacks on polynomial Shamir `t`-private PIR -/

section ShamirSelectiveFailure

variable {F S ι R Q : Type} [Field F] [Fintype S] [DecidableEq S]

namespace Scheme

/-- A field-valued PIR scheme `P : Scheme ι S R Q F` has *Lagrange indicator reconstruction* with
respect to `params : Shamir.Params F S` when the user reconstructs by testing
`Shamir.Polynomial.reconstruct params.point ans = 1` and honest server answers interpolate at `0` to
`if x i then 1 else 0`. Both `PIR.shamir` and `PIR.shamirCube` satisfy this interface. -/
structure HasLagrangeReconstruct (params : Shamir.Params F S) (P : Scheme ι S R Q F) : Prop where
  /-- The user outputs `true` iff Lagrange interpolation at `0` equals `1 : F`. -/
  reconstruct_eq : ∀ i r ans,
    P.reconstruct i r ans =
      open scoped Classical in decide (Shamir.Polynomial.reconstruct params.point ans = 1)
  /-- On every supported query draw, Lagrange interpolation at `0` of the honest answers equals `1`
  when `x i = true` and `0` when `x i = false`. -/
  reconstruct_answer_eq : ∀ x i r q, (r, q) ∈ (ProbComp.eval (P.query i)).support →
    Shamir.Polynomial.reconstruct params.point (fun s => P.answer s x (q s)) =
      if x i then 1 else 0

/-- Additive constant-shift attack on a Lagrange-reconstructed PIR scheme: server `s₀` adds
`Δ * (lagrangeWeightAtZero params.point s₀)⁻¹` to its honest answer, shifting the interpolated
constant term at `0` by `Δ : F`. -/
@[expose] noncomputable def lagrangeShiftAttack (P : Scheme ι S R Q F) (params : Shamir.Params F S)
    (x : ι → Bool) (s₀ : S) (Δ : F) (q : Q) : F :=
  P.answer s₀ x q + Δ * (Shamir.Polynomial.lagrangeWeightAtZero params.point s₀)⁻¹

namespace HasLagrangeReconstruct

variable {params : Shamir.Params F S} {P : Scheme ι S R Q F}
  (hP : P.HasLagrangeReconstruct params)

include hP in
/-- Under `lagrangeShiftAttack P params x s₀ Δ`, Lagrange interpolation at `0` evaluates to
`(if x i then 1 else 0) + Δ` on every supported query draw. -/
theorem reconstruct_update_lagrangeShiftAttack (x : ι → Bool) (s₀ : S) (Δ : F) (i : ι)
    {r : R} {q : S → Q} (hrq : (r, q) ∈ (ProbComp.eval (P.query i)).support) :
    Shamir.Polynomial.reconstruct params.point
        (Function.update (fun s => P.answer s x (q s)) s₀
          (P.lagrangeShiftAttack params x s₀ Δ (q s₀))) =
      (if x i then 1 else 0) + Δ := by
  have hupd : Function.update (fun s => P.answer s x (q s)) s₀
      (P.lagrangeShiftAttack params x s₀ Δ (q s₀)) = (fun s => P.answer s x (q s)) +
        Pi.single s₀ (Δ * (Shamir.Polynomial.lagrangeWeightAtZero params.point s₀)⁻¹) :=
    funext fun s => by by_cases hs : s = s₀ <;> simp [hs, lagrangeShiftAttack]
  have hw_ne : Shamir.Polynomial.lagrangeWeightAtZero params.point s₀ ≠ 0 :=
    Shamir.Polynomial.lagrangeWeightAtZero_ne_zero params.point_injective params.point_nonzero s₀
  rw [hupd, Shamir.Polynomial.reconstruct_add, hP.reconstruct_answer_eq x i r q hrq,
    Shamir.Polynomial.reconstruct_single, mul_assoc, inv_mul_cancel₀ hw_ne, mul_one]

include hP in
/-- **Deterministic selective failure on Lagrange-reconstructed PIR.** For any field offset `Δ : F`
with `Δ ≠ 0` and `Δ ≠ 1`, `P.lagrangeShiftAttack params x s₀ Δ` shifts `1` to `1 + Δ ≠ 1` and `0`
to `Δ ≠ 1`, so the user always outputs `false` and suffers a reconstruction failure **if and only if
`x i = true`**. -/
theorem isDeterministicAttack (x : ι → Bool) (s₀ : S) {Δ : F} (hΔ0 : Δ ≠ 0) (hΔ1 : Δ ≠ 1) :
    P.IsDeterministicAttack x s₀ (P.lagrangeShiftAttack params x s₀ Δ) x := by
  classical
  refine (P.selectiveFailureModel x).isDeterministicAttack_of_decide_eq_one
    (fun i => P.query i)
    (fun i rq => Shamir.Polynomial.reconstruct params.point
      (Function.update (fun s => P.answer s x (rq.2 s)) s₀
        (P.lagrangeShiftAttack params x s₀ Δ (rq.2 s₀))))
    (s₀, P.lagrangeShiftAttack params x s₀ Δ)
    (fun i => congrArg (· <$> P.query i) (funext fun _ => hP.reconstruct_eq _ _ _))
    fun i ⟨r, q⟩ hrq => ?_
  rw [hP.reconstruct_update_lagrangeShiftAttack x s₀ Δ i hrq]
  cases x i <;> simp [hΔ1, hΔ0]

include hP in
/-- Under `lagrangeShiftAttack` with `Δ ≠ 0` and `Δ ≠ 1`, a single server `s₀` distinguishes any two
indices `i₀, i₁` with `x i₀ ≠ x i₁` with selective-failure advantage `1`. -/
theorem selectiveFailureAdvantage_eq_one (x : ι → Bool) (s₀ : S) {Δ : F} (hΔ0 : Δ ≠ 0)
    (hΔ1 : Δ ≠ 1) {i₀ i₁ : ι} (hx : x i₀ ≠ x i₁) :
    P.selectiveFailureAdvantage x s₀ (P.lagrangeShiftAttack params x s₀ Δ) i₀ i₁ = 1 :=
  (hP.isDeterministicAttack x s₀ hΔ0 hΔ1).selectiveFailureAdvantage_eq_one hx

omit [DecidableEq S] in
/-- Whenever `0 < params.threshold` (`t ≥ 1`), the evaluation points of `params : Shamir.Params F S`
supply at least two distinct nonzero field elements, so there exists `Δ : F` with `Δ ≠ 0` and
`Δ ≠ 1`. -/
private theorem exists_ne_zero_ne_one (params : Shamir.Params F S) (ht : 0 < params.threshold) :
    ∃ Δ : F, Δ ≠ 0 ∧ Δ ≠ 1 := by
  have : Nontrivial S :=
    Fintype.one_lt_card_iff_nontrivial.mp (Nat.lt_of_le_of_lt ht params.threshold_lt_card)
  obtain ⟨s₁, s₂, hs⟩ := exists_pair_ne S
  by_cases h1 : params.point s₁ = 1
  · exact ⟨params.point s₂, params.point_nonzero s₂,
      fun h2 => hs (params.point_injective (h1.trans h2.symm))⟩
  · exact ⟨params.point s₁, params.point_nonzero s₁, h1⟩

include hP in
/-- **Every `t`-private (`t ≥ 1`) Lagrange-reconstructed PIR scheme is vulnerable to single-server
selective failure attacks** on any nontrivial index type `[Nontrivial ι]`. -/
theorem not_isSelectiveFailureFree [Nontrivial ι] (ht : 0 < params.threshold) :
    ¬ P.IsSelectiveFailureFree := by
  classical
  obtain ⟨s₀⟩ := Fintype.card_pos_iff.mp (lt_trans ht params.threshold_lt_card)
  obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne ι
  obtain ⟨Δ, hΔ0, hΔ1⟩ := exists_ne_zero_ne_one params ht
  exact (hP.isDeterministicAttack (fun i => decide (i = i₀)) s₀ hΔ0
    hΔ1).not_isSelectiveFailureFree (i₀ := i₀) (i₁ := i₁) (by simp [hi.symm])

end HasLagrangeReconstruct

end Scheme

variable [Fintype F] {D : Type} [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]

omit [DecidableEq S] in
/-- `PIR.shamir` satisfies `Scheme.HasLagrangeReconstruct`. -/
theorem hasLagrangeReconstruct_shamir (params : Shamir.Params F S) :
    (shamir ι params).HasLagrangeReconstruct params where
  reconstruct_eq := reconstruct_shamir params
  reconstruct_answer_eq x i _ _ hrq := reconstruct_answer_shamir params x i hrq

omit [DecidableEq S] in
/-- `PIR.shamirCube` satisfies `Scheme.HasLagrangeReconstruct` whenever
`|D| * params.threshold < |S|`. -/
theorem hasLagrangeReconstruct_shamirCube (params : Shamir.Params F S)
    (hdeg : Fintype.card D * params.threshold < Fintype.card S) :
    (shamirCube D ι params).HasLagrangeReconstruct params where
  reconstruct_eq := reconstruct_shamirCube params
  reconstruct_answer_eq x i _ _ hrq := reconstruct_answer_shamirCube params hdeg x i hrq

/-- **Deterministic selective failure on linear Shamir `t`-private PIR (`PIR.shamir`).** For any
`Δ : F` with `Δ ≠ 0` and `Δ ≠ 1`, server `s₀`'s additive shift attack causes a reconstruction
failure on query `i` iff `x i = true`. -/
theorem isDeterministicAttack_shamir (params : Shamir.Params F S) (x : ι → Bool) (s₀ : S)
    {Δ : F} (hΔ0 : Δ ≠ 0) (hΔ1 : Δ ≠ 1) :
    (shamir ι params).IsDeterministicAttack x s₀
      ((shamir ι params).lagrangeShiftAttack params x s₀ Δ) x :=
  (hasLagrangeReconstruct_shamir params).isDeterministicAttack x s₀ hΔ0 hΔ1

/-- Single-server selective-failure advantage `1` on `PIR.shamir` between any `i₀, i₁` with
`x i₀ ≠ x i₁`. -/
theorem selectiveFailureAdvantage_shamir_eq_one (params : Shamir.Params F S) (x : ι → Bool)
    (s₀ : S) {Δ : F} (hΔ0 : Δ ≠ 0) (hΔ1 : Δ ≠ 1) {i₀ i₁ : ι} (hx : x i₀ ≠ x i₁) :
    (shamir ι params).selectiveFailureAdvantage x s₀
      ((shamir ι params).lagrangeShiftAttack params x s₀ Δ) i₀ i₁ = 1 :=
  (hasLagrangeReconstruct_shamir params).selectiveFailureAdvantage_eq_one x s₀ hΔ0 hΔ1 hx

/-- **Linear Shamir `t`-private PIR (`PIR.shamir`) is not selective-failure free** whenever
`0 < params.threshold` (`t ≥ 1`) and `[Nontrivial ι]`, even though it is `t`-private against
passive server coalitions (`isTPrivate_shamir`). -/
theorem not_isSelectiveFailureFree_shamir [Nontrivial ι] (params : Shamir.Params F S)
    (ht : 0 < params.threshold) :
    ¬ (shamir ι params).IsSelectiveFailureFree :=
  (hasLagrangeReconstruct_shamir params).not_isSelectiveFailureFree ht

/-- **Deterministic selective failure on degree-`d` polynomial `t`-private PIR (`PIR.shamirCube`).**
When `|D| * params.threshold < |S|` and `Δ ≠ 0`, `Δ ≠ 1`, server `s₀`'s additive shift attack causes
a reconstruction failure on query `i` iff `x i = true`. -/
theorem isDeterministicAttack_shamirCube (params : Shamir.Params F S)
    (hdeg : Fintype.card D * params.threshold < Fintype.card S) (x : (D → ι) → Bool) (s₀ : S)
    {Δ : F} (hΔ0 : Δ ≠ 0) (hΔ1 : Δ ≠ 1) :
    (shamirCube D ι params).IsDeterministicAttack x s₀
      ((shamirCube D ι params).lagrangeShiftAttack params x s₀ Δ) x :=
  (hasLagrangeReconstruct_shamirCube params hdeg).isDeterministicAttack x s₀ hΔ0 hΔ1

/-- Single-server selective-failure advantage `1` on `PIR.shamirCube` between any `i₀, i₁` with
`x i₀ ≠ x i₁`. -/
theorem selectiveFailureAdvantage_shamirCube_eq_one (params : Shamir.Params F S)
    (hdeg : Fintype.card D * params.threshold < Fintype.card S) (x : (D → ι) → Bool) (s₀ : S)
    {Δ : F} (hΔ0 : Δ ≠ 0) (hΔ1 : Δ ≠ 1) {i₀ i₁ : D → ι} (hx : x i₀ ≠ x i₁) :
    (shamirCube D ι params).selectiveFailureAdvantage x s₀
      ((shamirCube D ι params).lagrangeShiftAttack params x s₀ Δ) i₀ i₁ = 1 :=
  (hasLagrangeReconstruct_shamirCube params hdeg).selectiveFailureAdvantage_eq_one x s₀ hΔ0 hΔ1 hx

/-- **Degree-`d` polynomial `t`-private PIR (`PIR.shamirCube`) is not selective-failure free**
whenever `|D| * params.threshold < |S|`, `0 < params.threshold` (`t ≥ 1`), `[Nonempty D]`, and
`[Nontrivial ι]`, even though it is `t`-private against passive coalitions
(`isTPrivate_shamirCube`). -/
theorem not_isSelectiveFailureFree_shamirCube [Nonempty D] [Nontrivial ι]
    (params : Shamir.Params F S) (hdeg : Fintype.card D * params.threshold < Fintype.card S)
    (ht : 0 < params.threshold) :
    ¬ (shamirCube D ι params).IsSelectiveFailureFree :=
  (hasLagrangeReconstruct_shamirCube params hdeg).not_isSelectiveFailureFree ht

end ShamirSelectiveFailure

end Cslib.Crypto.Protocols.PIR
