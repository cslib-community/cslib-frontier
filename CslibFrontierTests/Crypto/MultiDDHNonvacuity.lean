/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

-- `import all`: `MultiDDH.lean` leaves `singleSecretMultiDDHRealGame`,
-- `singleSecretMultiDDHRandomGame`, `SingleSecretMultiDDH`, `multiDDHRealGame`,
-- `multiDDHRandomGame`, and `MultiDDH` without `@[expose]`, so unfolding them to check
-- non-vacuity requires `import all`.
import all CslibFrontier.Crypto.Computational.DiffieHellman.MultiDDH
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

set_option linter.privateModule false

/-!
# Checked non-vacuity witnesses for `SingleSecretMultiDDH` and `MultiDDH`

Proves that every prime-order group family `F` and fixed description `d : F.Desc` fails both
`F.SingleSecretMultiDDH (fun _ => PMF.pure d) (fun _ => 1)` and
`F.MultiDDH (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1)` with acceptance probabilities `1 / q`
(real) vs `1 / q²` (random).
-/

namespace CslibFrontierTests.Crypto.MultiDDHNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc)

/-- Distinguish fixed-group single-secret Multi-DDH by testing `u = 0` and the first pair's second
coordinate `w₀ = 0`. -/
noncomputable def singleSecretIdentityTest : F.SingleSecretMultiDDHDistinguisher :=
  fun _ _ u pairs =>
    pure (decide (u = 0) && match pairs with | [] => false | p :: _ => decide (p.2 = 0))

theorem isPPT_singleSecretIdentityTest : (singleSecretIdentityTest F).IsPPT := by
  rw [SingleSecretMultiDDHDistinguisher.isPPT_iff]
  let encodedPairs (x : F.SingleSecretMultiDDHInput) : List (List Bool × List Bool) :=
    x.pairs.map fun p => (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2)
  have hpairs : ComputableInPolyTime encodedPairs F.encSingleSecretMultiDDHInput
      (encList (encPair encBits encBits)) := by
    have hraw : ComputableInPolyTime
        (fun x : F.SingleSecretMultiDDHInput =>
          encList (F.encCarrierPair x.groupParameters) x.pairs)
        F.encSingleSecretMultiDDHInput encBits := by
      fun_prop
    refine hraw.of_enc_eq fun x => ?_
    exact (F.encList_encCarrierPair x.groupParameters x.pairs).symm
  have hhead : ComputableInPolyTime (fun x : F.SingleSecretMultiDDHInput =>
      (encodedPairs x).head?) F.encSingleSecretMultiDDHInput
      (encOption (encPair encBits encBits)) := by
    fun_prop
  have hisEmpty : ComputableInPolyTime (fun x : F.SingleSecretMultiDDHInput =>
      (encodedPairs x).isEmpty) F.encSingleSecretMultiDDHInput encBool := by
    fun_prop
  have hgetD : ComputableInPolyTime (fun x : F.SingleSecretMultiDDHInput =>
      ((encodedPairs x).head?).getD ([], [])) F.encSingleSecretMultiDDHInput
      (encPair encBits encBits) :=
    ComputableInPolyTime.optionGetDWithInput hhead (ComputableInPolyTime.const ([], []))
  have hsnd : ComputableInPolyTime (fun x : F.SingleSecretMultiDDHInput =>
      (((encodedPairs x).head?).getD ([], [])).2) F.encSingleSecretMultiDDHInput encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp hgetD
  have hfun : ComputableInPolyTime (fun x : F.SingleSecretMultiDDHInput =>
      decide (F.encode x.groupParameters x.leftPublic = F.encode x.groupParameters 0) &&
        (!(encodedPairs x).isEmpty &&
          decide ((((encodedPairs x).head?).getD ([], [])).2 =
            F.encode x.groupParameters 0)))
      F.encSingleSecretMultiDDHInput encBool := by
    fun_prop
  refine hfun.isPPTOn.congr fun x => ?_
  rcases x with ⟨n, d0, u, pairs⟩
  dsimp only [singleSecretIdentityTest, encodedPairs]
  cases pairs with
  | nil => simp
  | cons p ps =>
    simp only [List.map_cons, List.isEmpty_cons, Bool.not_false, Bool.true_and,
      List.head?_cons, Option.getD_some, (F.encode_injective _).eq_iff]

private theorem succProbability_singleSecretReal_identityTest (n : ℕ) :
    Game.succProbability (F.singleSecretMultiDDHRealGame (fun _ => PMF.pure d) (fun _ => 1)
      (singleSecretIdentityTest F) n) = (F.order d : ℝ≥0)⁻¹ := by
  simp only [singleSecretMultiDDHRealGame, multiDDHRealTupleLaw, List.ofFn_succ,
    List.ofFn_zero, singleSecretIdentityTest, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.pure_bind, PMF.bind_map, Function.comp_def]
  have hdec (α : ZMod (F.order d)) (B : Fin 1 → ZMod (F.order d)) :
      (decide (α • F.generator d = 0) && decide (((α * B 0) • F.generator d) = 0)) =
        decide (α = 0) := by
    by_cases hα : α = 0 <;> simp [hα, smul_eq_zero, F.generator_ne_zero]
  simp only [hdec, PMF.bind_const]
  rw [Game.succProbability, PMF.bind_pure_decide_eq_apply_true', PMF.uniformOfFintype_apply,
    ZMod.card, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

private theorem succProbability_singleSecretRandom_identityTest (n : ℕ) :
    Game.succProbability (F.singleSecretMultiDDHRandomGame (fun _ => PMF.pure d) (fun _ => 1)
      (singleSecretIdentityTest F) n) = (F.order d : ℝ≥0)⁻¹ ^ 2 := by
  have : NeZero (F.order d) := ⟨(F.prime_order d).ne_zero⟩
  have hlaw :
      F.multiDDHRandomTupleLaw d (Fin 1) =
        (PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map fun p _ =>
          (p.1 • F.generator d, p.2 • F.generator d) := by
    unfold multiDDHRandomTupleLaw
    rw [← PMF.uniformOfFintype_map_equiv (Equiv.funUnique (Fin 1) _).symm, PMF.map_comp]
    congr 1 with p
  simp only [singleSecretMultiDDHRandomGame, hlaw, List.ofFn_succ, List.ofFn_zero,
    singleSecretIdentityTest, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.pure_bind,
    PMF.bind_map]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  simp only [PMF.bind_apply, tsum_fintype, Fintype.sum_prod_type, PMF.uniformOfFintype_apply,
    ZMod.card, Fintype.card_prod, Nat.cast_mul, Function.comp_apply, PMF.pure_apply, smul_eq_zero,
    F.generator_ne_zero, or_false, Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq, ite_and,
    mul_ite, mul_one, mul_zero]
  have hne : (F.order d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero
  have htop : (F.order d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl hne) (Or.inl htop), Finset.sum_eq_single (0 : ZMod (F.order d))]
  · simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hne htop, one_mul, sq]
  · intro a _ ha
    simp only [ha, ↓reduceIte, Finset.sum_const_zero, mul_zero]
  · intro h0
    exact absurd (Finset.mem_univ 0) h0

/-- Fixed-group refutation of `SingleSecretMultiDDH` for every prime-order group family `F` and
fixed description `d : F.Desc`. -/
theorem not_singleSecretMultiDDH_pure :
    ¬ F.SingleSecretMultiDDH (fun _ => PMF.pure d) (fun _ => 1) := by
  intro h
  have hneg := h (singleSecretIdentityTest F) (isPPT_singleSecretIdentityTest F)
  simp only [Game.advantage, succProbability_singleSecretReal_identityTest,
    succProbability_singleSecretRandom_identityTest] at hneg
  refine not_negligible_const ?_ hneg
  rw [ne_eq, nndist_eq_zero]
  intro heq
  have hq : (2 : ℝ) ≤ F.order d := by exact_mod_cast (F.prime_order d).two_le
  have hr : ((F.order d : ℝ))⁻¹ = ((F.order d : ℝ))⁻¹ ^ 2 := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast] using
      congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  field_simp at hr
  nlinarith

/-- Distinguish fixed-group two-parameter Multi-DDH by running `singleSecretIdentityTest` on the
first secret block `(u₀, pairs₀)`. -/
noncomputable def multiDDHIdentityTest : F.MultiDDHDistinguisher :=
  fun _ d blocks => match blocks with
    | [] => pure false
    | b :: _ => singleSecretIdentityTest F 0 d b.1 b.2

theorem isPPT_multiDDHIdentityTest : (multiDDHIdentityTest F).IsPPT := by
  rw [MultiDDHDistinguisher.isPPT_iff]
  let encodedBlocks (x : F.MultiDDHInput) :
      List (List Bool × List (List Bool × List Bool)) :=
    x.blocks.map fun b =>
      (F.encode x.groupParameters b.1,
        b.2.map fun p => (F.encode x.groupParameters p.1, F.encode x.groupParameters p.2))
  let EBlk := encPair encBits (encList (encPair encBits encBits))
  have hblocks : ComputableInPolyTime encodedBlocks F.encMultiDDHInput (encList EBlk) := by
    have hraw : ComputableInPolyTime
        (fun x : F.MultiDDHInput =>
          encList (F.encMultiDDHBlock x.groupParameters) x.blocks)
        F.encMultiDDHInput encBits := by
      fun_prop
    refine hraw.of_enc_eq fun x => ?_
    exact (F.encList_encMultiDDHBlock x.groupParameters x.blocks).symm
  have hheadB : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      (encodedBlocks x).head?) F.encMultiDDHInput (encOption EBlk) := by
    fun_prop
  have hisEmptyB : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      (encodedBlocks x).isEmpty) F.encMultiDDHInput encBool := by
    fun_prop
  have hblk0 : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      ((encodedBlocks x).head?).getD ([], [])) F.encMultiDDHInput EBlk :=
    ComputableInPolyTime.optionGetDWithInput hheadB (ComputableInPolyTime.const ([], []))
  have hu0 : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      (((encodedBlocks x).head?).getD ([], [])).1) F.encMultiDDHInput encBits :=
    (ComputableInPolyTime.fst encBits (encList (encPair encBits encBits))).comp hblk0
  have hpairs0 : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      (((encodedBlocks x).head?).getD ([], [])).2)
      F.encMultiDDHInput (encList (encPair encBits encBits)) :=
    (ComputableInPolyTime.snd encBits (encList (encPair encBits encBits))).comp hblk0
  have hheadP : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      ((((encodedBlocks x).head?).getD ([], [])).2).head?)
      F.encMultiDDHInput (encOption (encPair encBits encBits)) := by
    fun_prop
  have hisEmptyP : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      ((((encodedBlocks x).head?).getD ([], [])).2).isEmpty)
      F.encMultiDDHInput encBool := by
    fun_prop
  have hp0 : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      (((((encodedBlocks x).head?).getD ([], [])).2).head?).getD ([], []))
      F.encMultiDDHInput (encPair encBits encBits) :=
    ComputableInPolyTime.optionGetDWithInput hheadP (ComputableInPolyTime.const ([], []))
  have hw0 : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      ((((((encodedBlocks x).head?).getD ([], [])).2).head?).getD ([], [])).2)
      F.encMultiDDHInput encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp hp0
  have hfun : ComputableInPolyTime (fun x : F.MultiDDHInput =>
      !(encodedBlocks x).isEmpty &&
        (decide (((((encodedBlocks x).head?).getD ([], [])).1) =
            F.encode x.groupParameters 0) &&
          (!((((encodedBlocks x).head?).getD ([], [])).2).isEmpty &&
            decide (((((((encodedBlocks x).head?).getD ([], [])).2).head?).getD ([], [])).2 =
              F.encode x.groupParameters 0))))
      F.encMultiDDHInput encBool := by
    fun_prop
  refine hfun.isPPTOn.congr fun x => ?_
  rcases x with ⟨n, d0, blocks⟩
  dsimp only [multiDDHIdentityTest, singleSecretIdentityTest, encodedBlocks]
  cases blocks with
  | nil => simp
  | cons b bs =>
    rcases b with ⟨u, pairs⟩
    cases pairs with
    | nil => simp [(F.encode_injective _).eq_iff]
    | cons p ps => simp [(F.encode_injective _).eq_iff]

private theorem eval_multiDDHRealGame_one (n : ℕ) :
    F.multiDDHRealGame (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1)
      (multiDDHIdentityTest F) n =
    F.singleSecretMultiDDHRealGame (fun _ => PMF.pure d) (fun _ => 1)
      (singleSecretIdentityTest F) n := by
  simp only [multiDDHRealGame, singleSecretMultiDDHRealGame, multiDDHRealBlockLaw,
    Probability.PMF.iid, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.pure_map, List.ofFn_succ, List.ofFn_zero, Fin.cons_zero,
    multiDDHIdentityTest, singleSecretIdentityTest]

private theorem eval_multiDDHRandomGame_one (n : ℕ) :
    F.multiDDHRandomGame (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1)
      (multiDDHIdentityTest F) n =
    F.singleSecretMultiDDHRandomGame (fun _ => PMF.pure d) (fun _ => 1)
      (singleSecretIdentityTest F) n := by
  simp only [multiDDHRandomGame, singleSecretMultiDDHRandomGame, multiDDHRandomBlockLaw,
    Probability.PMF.iid, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.pure_map, List.ofFn_succ, List.ofFn_zero, Fin.cons_zero,
    multiDDHIdentityTest, singleSecretIdentityTest]

/-- Fixed-group refutation of two-parameter `MultiDDH` for every prime-order group family `F` and
fixed description `d : F.Desc`. -/
theorem not_multiDDH_pure :
    ¬ F.MultiDDH (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1) := by
  intro h
  have hneg := h (multiDDHIdentityTest F) (isPPT_multiDDHIdentityTest F)
  simp only [eval_multiDDHRealGame_one, eval_multiDDHRandomGame_one, Game.advantage,
    succProbability_singleSecretReal_identityTest,
    succProbability_singleSecretRandom_identityTest] at hneg
  refine not_negligible_const ?_ hneg
  rw [ne_eq, nndist_eq_zero]
  intro heq
  have hq : (2 : ℝ) ≤ F.order d := by exact_mod_cast (F.prime_order d).two_le
  have hr : ((F.order d : ℝ))⁻¹ = ((F.order d : ℝ))⁻¹ ^ 2 := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast] using
      congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  field_simp at hr
  nlinarith

end CslibFrontierTests.Crypto.MultiDDHNonvacuity
