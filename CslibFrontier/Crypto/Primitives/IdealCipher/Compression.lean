/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.IdealCipher
public import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
public import CslibFrontier.Crypto.Primitives.Hash.BlockCipherCompression
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collision Resistance in the Ideal Cipher Model

We define the collision-resistance game (`collisionGame`) for a compression function built from an
ideal block cipher over `Key` and `Block`, played by a `CollisionFinder`, record the inverse-query
break of `cipherOutput` ([KatzLindell2020], Exercise 7.23(a)), and prove the Ideal-Cipher
collision-resistance upper bound for the Davies–Meyer construction `daviesMeyer`
([KatzLindell2020], Section 7.3.1, Figure 7.11, Theorem 7.5). The bound proved is that of
[BonehShoup2023], Section 8.5.3, Theorem 8.4, p. 302.

Specifically, for every randomized adaptive finder `A` (`CollisionFinder`, a `ProbOracleComp` with
private coins) making at most `Q` forward and inverse ideal-cipher queries (`A.IsQueryBounded Q`),
`daviesMeyer_collisionGame_le` fixes private coins via `ProbOracleComp.coinLaw`, reduces each
coin-fixed run to the forgetful ideal-cipher oracle via `abs_sub_uniformPerm_forgetful_le`, and
bounds the forgetful collision probability via `OracleComp.toOuterMeasure_bad_choose_two_le`,
yielding `Pr[collisionGame daviesMeyer A] ≤ 2 * ((Q + 2).choose 2 : ℝ) * (Fintype.card Block)⁻¹`
(equivalently `((Q + 2) * (Q + 1) : ℝ) * (Fintype.card Block)⁻¹`), Boneh–Shoup's
`(q + 1)(q + 2)/|X|` with `q = Q`. The `+ 2` counts the two forward queries on the finder's
output pair that `daviesMeyerCollisionProgram` appends. `daviesMeyer F (k, x) = F k x + x` is
Boneh–Shoup's `h_DM(x, y) = E(y, x) ⊕ x` (Section 8.5.2, p. 300) with its arguments swapped, over
any finite additive group of blocks in place of `{0, 1}ⁿ` under XOR.

## Main definitions

* `Cslib.IdealCipher.CollisionFinder`: A randomized ideal-cipher adversary (`ProbOracleComp`) that
  outputs a candidate collision.
* `Cslib.IdealCipher.collides`: The winning test, shared by the game and the Davies–Meyer program.
* `Cslib.IdealCipher.collisionGame`: The collision-resistance game in the Ideal Cipher Model.
* `Cslib.IdealCipher.cipherOutputAdversary`: An explicit inverse-query collision finder for
  `cipherOutput`.
* `Cslib.IdealCipher.daviesMeyerCollisionProgram`: An ideal-cipher oracle program checking whether
  `A` outputs a valid collision under `daviesMeyer`.

## Main results

* `Cslib.IdealCipher.cipherOutputAdversary_wins`: `cipherOutputAdversary` breaks `cipherOutput`
  with probability `1`.
* `Cslib.IdealCipher.collisionGame_daviesMeyer_eq`: Equivalence between `collisionGame daviesMeyer`
  and `daviesMeyerCollisionProgram`.
* `Cslib.IdealCipher.daviesMeyer_collision_difference_bound`: Switching bound between the real
  ideal cipher and the forgetful sampler on `daviesMeyerCollisionProgram`.
* `Cslib.IdealCipher.daviesMeyer_collisionGame_le`,
  `Cslib.IdealCipher.daviesMeyer_collisionGame_mul_le`: Davies–Meyer collision-resistance upper
  bounds in the Ideal Cipher Model ([KatzLindell2020], Theorem 7.5), with the bound of
  [BonehShoup2023], Theorem 8.4.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1,
  Figure 7.11, Theorem 7.5, Exercises 7.23 and 7.24.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 8.5.2 (p. 300) and Section 8.5.3, Theorem 8.4 (p. 302).
-/

public section

namespace Cslib.IdealCipher

open OracleComp Cslib.Crypto.BlockCipherCompression Cslib.Probability
open scoped ENNReal BigOperators

/-- A collision finder against a compression function `Key × Block → Block` built from an ideal
cipher: an adaptive oracle program with private coins (`ProbOracleComp`) and forward and inverse
ideal-cipher queries that outputs two candidate inputs. -/
abbrev CollisionFinder (Key Block : Type) :=
  ProbOracleComp (Spec Key Block) ((Key × Block) × (Key × Block))

/-- The winning test: the inputs `x₁` and `x₂` differ and their digests `h₁` and `h₂` agree. -/
@[expose]
def collides {α β : Type} [DecidableEq α] [DecidableEq β] (x₁ x₂ : α) (h₁ h₂ : β) : Bool :=
  decide (x₁ ≠ x₂ ∧ h₁ = h₂)

section Programs

variable {Key Block : Type}

/-- Wrap a coin-fixed adversary `A` with two final forward queries on its candidate pair and test
the Davies–Meyer digests `E_k(x) + x` with `collides`. -/
@[expose]
noncomputable def daviesMeyerCollisionProgram [DecidableEq Key] [DecidableEq Block] [Add Block]
    (A : OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))) :
    OracleComp (Spec Key Block) Bool := do
  let ((k₁, x₁), (k₂, x₂)) ← A
  let y₁ ← query (k₁, Cslib.RandomPermutation.PermQuery.forward x₁)
  let y₂ ← query (k₂, Cslib.RandomPermutation.PermQuery.forward x₂)
  return collides (k₁, x₁) (k₂, x₂) (y₁ + x₁) (y₂ + x₂)

/-- Appending two forward queries adds `2` to a coin-fixed adversary's query bound. -/
theorem isQueryBounded_daviesMeyerCollisionProgram [DecidableEq Key] [DecidableEq Block] [Add Block]
    {A : OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))} {Q : ℕ}
    (hQ : IsQueryBounded A Q) :
    IsQueryBounded (daviesMeyerCollisionProgram A) (Q + 2) :=
  IsCostBounded.bind hQ fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ =>
    IsCostBounded.bind (IsCostBounded.query _) fun _ =>
      IsCostBounded.bind (IsCostBounded.query _) fun _ =>
        IsCostBounded.pure _ 0

end Programs

section Games

variable {Key Block : Type} [DecidableEq Key] [Fintype Key] [DecidableEq Block]
  [Fintype Block] [Nonempty Block]

/-- The collision-resistance game for a compression function `H` built from a block cipher.
The randomized adversary `A` has private coins and oracle access to the ideal cipher `E` and its
inverse, and wins when its candidates `x₁` and `x₂` `collide` under `H E`. -/
@[expose]
noncomputable def collisionGame
    (H : (Key → Equiv.Perm Block) → Key × Block → Block) (A : CollisionFinder Key Block) :
    PMF Bool :=
  (complete fun _ => []).bind fun E =>
    (interpret
      (sumHandler ProbComp.unifOracle fun (q : Query Key Block) =>
        PMF.pure (Cslib.RandomPermutation.evalPerm (E q.1) q.2)) A).map
      fun (x₁, x₂) => collides x₁ x₂ (H E x₁) (H E x₂)

/-- An adversary that finds a collision in `cipherOutput` using two inverse queries. -/
@[expose]
def cipherOutputAdversary (k1 k2 : Key) (y : Block) :
    ProbOracleComp (Spec Key Block) ((Key × Block) × (Key × Block)) := do
  let x1 ← ProbOracleComp.query (spec := Spec Key Block)
    (k1, Cslib.RandomPermutation.PermQuery.inverse y)
  let x2 ← ProbOracleComp.query (spec := Spec Key Block)
    (k2, Cslib.RandomPermutation.PermQuery.inverse y)
  return ((k1, x1), (k2, x2))

omit [Nonempty Block] in
/-- **Exercise 7.23(a)** ([KatzLindell2020], Section 7.3.1): `cipherOutputAdversary` finds a
collision for `cipherOutput` with probability `1`. -/
theorem cipherOutputAdversary_wins {k1 k2 : Key} (hk : k1 ≠ k2) (y : Block) :
    collisionGame (cipherOutput (B := Block)) (cipherOutputAdversary k1 k2 y) = PMF.pure true := by
  unfold collisionGame cipherOutputAdversary
  simp only [complete_nil, interp_norm, pmf_norm]
  simp [Cslib.RandomPermutation.evalPerm, collides, cipherOutput_symm, hk]

omit [DecidableEq Key] [DecidableEq Block] [Nonempty Block] in
/-- For `daviesMeyer`, `collisionGame` averages over `A`'s private coins (`ProbOracleComp.coinLaw`)
the execution of `daviesMeyerCollisionProgram (ProbOracleComp.fixCoins A ω)` against uniformly
chosen independent permutations `E : Key → Equiv.Perm Block`. -/
theorem collisionGame_daviesMeyer_eq [DecidableEq Key] [DecidableEq Block] [Add Block]
    (A : CollisionFinder Key Block) :
    collisionGame (daviesMeyer (K := Key) (B := Block)) A =
      (ProbOracleComp.coinLaw A).bind fun ω =>
        (PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))).bind fun E =>
          interpret (fun (q : Query Key Block) =>
            PMF.pure (Cslib.RandomPermutation.evalPerm (E q.1) q.2))
            (daviesMeyerCollisionProgram (ProbOracleComp.fixCoins A ω)) := by
  unfold collisionGame daviesMeyerCollisionProgram
  rw [complete_nil]
  simp_rw [← fun E : Key → Equiv.Perm Block =>
    ProbOracleComp.bind_interpret_fixCoins A fun (q : Query Key Block) =>
      Cslib.RandomPermutation.evalPerm (E q.1) q.2,
    PMF.map_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ω => congrArg _ (funext fun E => ?_))
  rw [interpret_bind, Probability.PMF.monad_bind_eq_bind, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun p => ?_)
  simp only [Cslib.RandomPermutation.evalPerm_forward, interp_norm, pmf_norm, daviesMeyer]

/-- Switching bound between the real ideal cipher and the forgetful sampler on
`daviesMeyerCollisionProgram A` for a coin-fixed finder `A`. -/
theorem daviesMeyer_collision_difference_bound [AddGroup Block]
    {A : OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))} {Q : ℕ}
    (hQ : IsQueryBounded A Q) :
    |Pr[(PMF.pi fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block)).bind fun P =>
        interpret (fun (q : Query Key Block) =>
          PMF.pure (Cslib.RandomPermutation.evalPerm (P q.1) q.2))
          (daviesMeyerCollisionProgram A)] -
      Pr[((interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run fun _ => []).map
        Prod.fst]| ≤
      ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  simpa only [PMF.bind_pure, Probability.PMF.monad_bind_eq_bind] using
    abs_sub_uniformPerm_forgetful_le (isQueryBounded_daviesMeyerCollisionProgram hQ)
      (PMF.pure (α := Bool)) true

end Games

section Helpers

private def HasDMCollision {Key Block : Type} [Add Block]
    (st : Key → Cslib.RandomPermutation.Cache Block) : Prop :=
  ∃ (k1 : Key) (i1 : Fin (st k1).length) (k2 : Key) (i2 : Fin (st k2).length),
    (k1, i1.1) ≠ (k2, i2.1) ∧
      (st k1)[i1].2 + (st k1)[i1].1 = (st k2)[i2].2 + (st k2)[i2].1

private theorem not_hasDMCollision_nil {Key Block : Type} [Add Block] :
    ¬ HasDMCollision (fun _ : Key => ([] : Cslib.RandomPermutation.Cache Block)) := by
  rintro ⟨_, i1, _⟩
  exact i1.elim0

private theorem hasDMCollision_of_mem {Key Block : Type} [Add Block]
    {st : Key → Cslib.RandomPermutation.Cache Block}
    {k1 k2 : Key} {x1 x2 y1 y2 : Block}
    (hne : (k1, x1) ≠ (k2, x2)) (heq : y1 + x1 = y2 + x2)
    (h1 : (x1, y1) ∈ st k1) (h2 : (x2, y2) ∈ st k2) :
    HasDMCollision st := by
  obtain ⟨i1, hi1, hget1⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨i2, hi2, hget2⟩ := List.mem_iff_getElem.mp h2
  refine ⟨k1, ⟨i1, hi1⟩, k2, ⟨i2, hi2⟩, ?_, ?_⟩
  · intro h
    obtain ⟨hk, hi⟩ := Prod.mk.inj h
    subst hk
    subst hi
    apply hne
    have hpair : (x1, y1) = (x2, y2) := hget1.symm.trans hget2
    exact congrArg (k1, ·) (Prod.mk.inj hpair).1
  · simp [hget1, hget2, heq]

private theorem mem_of_mem_support_forgetfulAnswer {Key Block : Type}
    [DecidableEq Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    {q : Query Key Block} {st st' : Key → Cslib.RandomPermutation.Cache Block} {a : Block}
    (hmem : (a, st') ∈ (forgetfulAnswer q st).support) :
    ∀ k e, e ∈ st k → e ∈ st' k := by
  simp only [forgetfulAnswer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c⟩, hbc, h_eq⟩ := hmem
  cases h_eq
  intro k e he
  by_cases hk : k = q.1
  · subst hk
    simp only [Function.update_self]
    rcases Cslib.RandomPermutation.mem_support_forgetfulAnswer hbc with ⟨-, hc⟩ | ⟨-, hc⟩ <;>
      dsimp only at hc <;> rw [hc]
    · exact he
    · exact List.mem_cons_of_mem _ he
  · simp [Function.update_of_ne hk, he]

private theorem mem_of_mem_support_forgetfulAnswer_forward {Key Block : Type}
    [DecidableEq Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    {k : Key} {x y : Block} {st st' : Key → Cslib.RandomPermutation.Cache Block}
    (hmem : (y, st') ∈ (forgetfulAnswer (k, .forward x) st).support) :
    (x, y) ∈ st' k := by
  simp only [forgetfulAnswer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c⟩, hbc, h_eq⟩ := hmem
  cases h_eq
  simp only [Function.update_self]
  rcases Cslib.RandomPermutation.mem_support_forgetfulAnswer hbc with ⟨hhit, hc⟩ | ⟨-, hc⟩ <;>
    dsimp only at hc <;> rw [hc]
  · exact Cslib.RandomPermutation.toCacheEntry_mem_of_cachedAnswer_eq_some hhit
  · exact List.mem_cons_self

private theorem hasDMCollision_of_mem_support_daviesMeyerCollisionProgram {Key Block : Type}
    [DecidableEq Key] [DecidableEq Block] [Fintype Block] [Nonempty Block] [Add Block]
    {A : OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))}
    {st₀ st : Key → Cslib.RandomPermutation.Cache Block}
    (hmem : (true, st) ∈
      ((interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run st₀).support) :
    HasDMCollision st := by
  unfold daviesMeyerCollisionProgram at hmem
  simp only [interp_norm, pmf_norm, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  obtain ⟨⟨⟨⟨k1, x1⟩, ⟨k2, x2⟩⟩, stA⟩, -, ⟨y1, st1⟩, hy1, ⟨y2, st2⟩, hy2, hres⟩ := hmem
  obtain ⟨hbool, hst⟩ := Prod.mk.inj hres
  subst hst
  have hcond : (k1, x1) ≠ (k2, x2) ∧ y1 + x1 = y2 + x2 := of_decide_eq_true hbool.symm
  exact hasDMCollision_of_mem hcond.1 hcond.2
    (mem_of_mem_support_forgetfulAnswer hy2 k1 (x1, y1)
      (mem_of_mem_support_forgetfulAnswer_forward hy1))
    (mem_of_mem_support_forgetfulAnswer_forward hy2)

private def dmTargets {Key Block : Type} [Fintype Key] [DecidableEq Block] [Add Block]
    (st : Key → Cslib.RandomPermutation.Cache Block) : Finset Block :=
  Finset.univ.biUnion fun k => (st k).toFinset.image fun e => e.2 + e.1

private theorem card_dmTargets_le {Key Block : Type} [Fintype Key] [DecidableEq Block] [Add Block]
    (st : Key → Cslib.RandomPermutation.Cache Block) :
    (dmTargets st).card ≤ ∑ k : Key, (st k).length :=
  calc (dmTargets st).card
      ≤ ∑ k : Key, ((st k).toFinset.image fun e : Block × Block => e.2 + e.1).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k : Key, (st k).toFinset.card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ ≤ ∑ k : Key, (st k).length :=
        Finset.sum_le_sum fun k _ => List.toFinset_card_le (st k)

private theorem mem_dmTargets_of_getElem {Key Block : Type} [Fintype Key] [DecidableEq Block]
    [Add Block] {st : Key → Cslib.RandomPermutation.Cache Block}
    (k : Key) (i : Fin (st k).length) :
    (st k)[i].2 + (st k)[i].1 ∈ dmTargets st := by
  refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, Finset.mem_image.mpr ?_⟩
  exact ⟨(st k)[i], List.mem_toFinset.mpr (List.getElem_mem i.2), rfl⟩

private theorem classify_update_idx {Key Block : Type} [DecidableEq Key]
    {st : Key → Cslib.RandomPermutation.Cache Block} (qk : Key) (e : Block × Block)
    (k : Key) (i : Fin (Function.update st qk (e :: st qk) k).length) :
    (k = qk ∧ i.1 = 0 ∧ (Function.update st qk (e :: st qk) k)[i] = e) ∨
      ∃ j : Fin (st k).length,
        (Function.update st qk (e :: st qk) k)[i] = (st k)[j] ∧
        (k = qk → j.1 + 1 = i.1) ∧ (k ≠ qk → j.1 = i.1) := by
  by_cases hk : k = qk
  · subst hk
    rcases i with ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl ⟨rfl, rfl, by simp⟩
    | succ m =>
      right
      have hm : m < (st k).length := by simpa using hn
      refine ⟨⟨m, hm⟩, ?_, fun _ => rfl, fun hne => (hne rfl).elim⟩
      simp
  · right
    have hi : i.1 < (st k).length := by simpa [Function.update_of_ne hk] using i.2
    refine ⟨⟨i.1, hi⟩, ?_, fun h => (hk h).elim, fun _ => rfl⟩
    simp [Function.update_of_ne hk]

private theorem dmTargets_of_hasDMCollision_update {Key Block : Type}
    [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Add Block]
    {st : Key → Cslib.RandomPermutation.Cache Block} (hst : ¬ HasDMCollision st)
    (qk : Key) (e : Block × Block)
    (hcol : HasDMCollision (Function.update st qk (e :: st qk))) :
    e.2 + e.1 ∈ dmTargets st := by
  obtain ⟨k1, i1, k2, i2, hne, heq⟩ := hcol
  rcases classify_update_idx qk e k1 i1 with
    ⟨hk1, hi1, hget1⟩ | ⟨j1, hget1, h1_eq, h1_ne⟩
  · rcases classify_update_idx qk e k2 i2 with
      ⟨hk2, hi2, _⟩ | ⟨j2, hget2, _, _⟩
    · exact (hne (Prod.ext (hk1.trans hk2.symm) (hi1.trans hi2.symm))).elim
    · rw [hget1, hget2] at heq
      rw [heq]
      exact mem_dmTargets_of_getElem k2 j2
  · rcases classify_update_idx qk e k2 i2 with
      ⟨_, _, hget2⟩ | ⟨j2, hget2, h2_eq, h2_ne⟩
    · rw [hget1, hget2] at heq
      rw [← heq]
      exact mem_dmTargets_of_getElem k1 j1
    · refine (hst ⟨k1, j1, k2, j2, ?_, ?_⟩).elim
      · intro hkj
        obtain ⟨hk, hj⟩ := Prod.mk.inj hkj
        apply hne
        apply Prod.ext hk
        by_cases hkq : k1 = qk
        · have hk2q : k2 = qk := hk.symm.trans hkq
          have := h1_eq hkq
          have := h2_eq hk2q
          omega
        · have hk2q : k2 ≠ qk := fun h => hkq (hk.trans h)
          have := h1_ne hkq
          have := h2_ne hk2q
          omega
      · rw [← hget1, ← hget2, heq]

private theorem toOuterMeasure_bad_forgetfulAnswer_step {Key Block : Type}
    [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    [AddGroup Block] (q : Query Key Block) (st : Key → Cslib.RandomPermutation.Cache Block)
    (hst : ¬ HasDMCollision st) :
    (forgetfulAnswer q st).toOuterMeasure {x | HasDMCollision x.2} ≤
      (∑ k : Key, (st k).length : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ := by
  have hle_sum :
      ∀ (f : Block → Block) (e : Block → Block × Block),
        Function.Injective f →
        (∀ a, (e a).2 + (e a).1 = f a) →
        ((PMF.uniformOfFintype Block).map fun a =>
          (a, Function.update st q.1 (e a :: st q.1))).toOuterMeasure
            {x | HasDMCollision x.2} ≤
          (∑ k : Key, (st k).length : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ := by
    intro f e hinj hfe
    rw [PMF.toOuterMeasure_map_apply]
    have hsub : (fun a : Block => (a, Function.update st q.1 (e a :: st q.1))) ⁻¹'
        {x | HasDMCollision x.2} ⊆ {a : Block | f a ∈ dmTargets st} := by
      intro a ha
      rw [Set.mem_ofPred_eq, ← hfe a]
      exact dmTargets_of_hasDMCollision_update hst q.1 (e a) ha
    refine (MeasureTheory.measure_mono hsub).trans ?_
    rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype]
    gcongr
    have hcard_inj : (Finset.univ.filter fun a : Block => f a ∈ dmTargets st).card ≤
        (dmTargets st).card := by
      refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a _ b _ hab => hinj hab)
      simpa using (Finset.mem_filter.mp ha).2
    exact Nat.cast_le.mpr (hcard_inj.trans (card_dmTargets_le st))
  simp only [forgetfulAnswer]
  have hmap_comp : ∀ (p : PMF (Block × Cslib.RandomPermutation.Cache Block)),
      (p.map fun bc => (bc.1, Function.update st q.1 bc.2)).toOuterMeasure
        {x | HasDMCollision x.2} =
      (p.map fun bc => (bc.1, Function.update st q.1 bc.2)).toOuterMeasure
        {x | HasDMCollision x.2} := fun _ => rfl
  cases hq2 : q.2 with
  | forward x =>
    cases hlook : (st q.1).lookup x with
    | some y =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_some hlook, PMF.pure_map]
      simp [hst, PMF.toOuterMeasure_pure_apply]
    | none =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_none hlook, PMF.map_comp]
      exact hle_sum (fun y => y + x) (fun y => (x, y)) (add_left_injective x) (fun _ => rfl)
  | inverse y =>
    cases hlook : Cslib.RandomPermutation.invLookup (st q.1) y with
    | some x =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_some hlook, PMF.pure_map]
      simp [hst, PMF.toOuterMeasure_pure_apply]
    | none =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_none hlook, PMF.map_comp]
      exact hle_sum (fun x => y + x) (fun x => (x, y)) (add_right_injective y) (fun _ => rfl)

private theorem forgetfulAnswer_size_grow {Key Block : Type}
    [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    (q : Query Key Block) (st : Key → Cslib.RandomPermutation.Cache Block)
    (x : Block × (Key → Cslib.RandomPermutation.Cache Block))
    (hmem : x ∈ (forgetfulAnswer q st).support) :
    ∑ k : Key, (x.2 k).length ≤ (∑ k : Key, (st k).length) + 1 := by
  rcases x with ⟨a, st'⟩
  simp only [forgetfulAnswer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c⟩, hbc, h_eq⟩ := hmem
  cases h_eq
  have hc_len : c.length ≤ (st q.1).length + 1 := by
    rcases Cslib.RandomPermutation.mem_support_forgetfulAnswer hbc with ⟨-, hc⟩ | ⟨-, hc⟩ <;>
      dsimp only at hc <;> simp [hc]
  have hsum1 : ∑ k : Key, (Function.update st q.1 c k).length =
      c.length + ∑ k ∈ Finset.univ.erase q.1, (st k).length := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun k => (Function.update st q.1 c k).length) (Finset.mem_univ q.1)]
    simp only [Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  have hsum2 : ∑ k : Key, (st k).length =
      (st q.1).length + ∑ k ∈ Finset.univ.erase q.1, (st k).length :=
    (Finset.add_sum_erase Finset.univ (fun k => (st k).length) (Finset.mem_univ q.1)).symm
  dsimp only
  omega

private theorem forgetful_daviesMeyer_collision_le {Key Block : Type}
    [DecidableEq Key] [Finite Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    [AddGroup Block] {A : OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))} {Q : ℕ}
    (hQ : IsQueryBounded A Q) :
    Pr[((interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run fun _ => []).map
      Prod.fst] ≤
      ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  let _ := Fintype.ofFinite Key
  have hQ_prog := isQueryBounded_daviesMeyerCollisionProgram hQ
  have hbad := OracleComp.toOuterMeasure_bad_choose_two_le
    (handler := forgetfulAnswer (Key := Key) (Block := Block))
    (bad := HasDMCollision)
    (fun st : Key → Cslib.RandomPermutation.Cache Block => ∑ k : Key, (st k).length)
    (Fintype.card Block : ℝ≥0∞)⁻¹
    (fun q st hst => toOuterMeasure_bad_forgetfulAnswer_step q st hst)
    (fun q st _ x hmem _ => forgetfulAnswer_size_grow q st x hmem)
    hQ_prog not_hasDMCollision_nil
  have h_len0 : ∑ _k : Key, ([] : Cslib.RandomPermutation.Cache Block).length = 0 := by simp
  rw [h_len0, mul_zero, zero_add] at hbad
  set p := (interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run (fun _ => [])
  have h_apply : (p.map Prod.fst) true ≤ p.toOuterMeasure {x | HasDMCollision x.2} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    refine p.toOuterMeasure_mono ?_
    rintro ⟨b, st⟩ ⟨hb, hmem⟩
    change b = true at hb
    subst b
    exact hasDMCollision_of_mem_support_daviesMeyerCollisionProgram hmem
  have h_enn : (p.map Prod.fst) true ≤
      ((Q + 2).choose 2 : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ :=
    h_apply.trans hbad
  ennreal_to_real using h_enn

end Helpers

section MainTheorems

variable {Key Block : Type} [DecidableEq Key] [Fintype Key] [DecidableEq Block]
  [Fintype Block] [Nonempty Block]

/-- **Davies–Meyer Ideal-Cipher Collision Resistance** ([KatzLindell2020], Section 7.3.1,
Theorem 7.5): every randomized adaptive collision finder `A` (`CollisionFinder`, with private
coins) making at most `Q` forward and inverse ideal-cipher queries on every path
(`A.IsQueryBounded Q`) finds a collision in `daviesMeyer` with probability at most
`2 * ((Q + 2).choose 2) * (Fintype.card Block)⁻¹`. This is the bound `(q + 1)(q + 2)/|X|` of
[BonehShoup2023], Section 8.5.3, Theorem 8.4, p. 302, with `q = Q`, written as
`2 · C(Q + 2, 2)/|X|`; `daviesMeyer_collisionGame_mul_le` writes it as a product.

`collisionGame` evaluates the two digests itself, without charging them to `A`. The `Q + 2` is
the query count of the proof's `daviesMeyerCollisionProgram`, which appends two forward queries on
each coin-fixed execution's outputs: Boneh–Shoup's "reasonable" adversary, with `q' = q + 2`
queries. No bound on local running time is required. -/
theorem daviesMeyer_collisionGame_le [AddGroup Block]
    {A : CollisionFinder Key Block} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    Pr[collisionGame (daviesMeyer (K := Key) (B := Block)) A] ≤
      2 * ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  rw [collisionGame_daviesMeyer_eq]
  obtain ⟨ω, -, hω⟩ := Cslib.Probability.PMF.exists_bind_apply_le
    (ProbOracleComp.coinLaw A) _ true
  have hle : Pr[(PMF.pi fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block)).bind fun E =>
      interpret (fun (q : Query Key Block) =>
        PMF.pure (Cslib.RandomPermutation.evalPerm (E q.1) q.2))
        (daviesMeyerCollisionProgram (ProbOracleComp.fixCoins A ω))] ≤
      2 * ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
    have hQω := ProbOracleComp.isQueryBounded_fixCoins hQ ω
    have h_diff := (abs_sub_le_iff.mp (daviesMeyer_collision_difference_bound hQω)).1
    have h_forg := forgetful_daviesMeyer_collision_le hQω
    linarith
  exact (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hω).trans hle

/-- Equivalent product form `((Q + 2) * (Q + 1) : ℝ) * (Fintype.card Block)⁻¹` of
`daviesMeyer_collisionGame_le` ([KatzLindell2020], Theorem 7.5), for randomized adaptive finders
making at most `Q` queries. It is the bound `(q + 1)(q + 2)/|X|` of [BonehShoup2023],
Section 8.5.3, Theorem 8.4, p. 302, with `q = Q`. -/
theorem daviesMeyer_collisionGame_mul_le [AddGroup Block]
    {A : CollisionFinder Key Block} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    Pr[collisionGame (daviesMeyer (K := Key) (B := Block)) A] ≤
      ((Q + 2) * (Q + 1) : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  have hchoose : 2 * ((Q + 2).choose 2 : ℝ) = (Q + 2) * (Q + 1) := by
    rw [Nat.cast_choose_two ℝ (Q + 2)]
    push_cast
    ring
  simpa only [hchoose] using daviesMeyer_collisionGame_le hQ

end MainTheorems

end Cslib.IdealCipher
