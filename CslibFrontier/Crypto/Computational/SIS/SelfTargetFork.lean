/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Module
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ForkingReduction
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map

/-!
# Classical random-oracle reduction from self-target solutions to Module-SIS

[BaiEtAl2021Dilithium], §6.1, “Classical Hardness of SelfTargetMSIS”, forks the solver
at the oracle query for its output. Two accepting runs at that point give short vectors
with the same module product and different last coordinates. Their integer difference
is a nonzero kernel vector with twice the coefficient bound.

The statement works for a given matrix, including the systematic matrix `[I | A]`.
The ideal challenge game draws uniform challenges embedded in the ring. The digest game
draws uniform digests instead, and its deterministic partial challenge expansion may
reject a digest or map different digests to the same polynomial. The verifier can make one last
oracle query, so the bound covers solvers that never queried their output point. The
experiment counts oracle queries and uses an explicit distribution of saved coins.
-/

public section

namespace Cslib.Crypto.ModuleSIS.SelfTarget

open Probability OracleComp Protocols Protocols.SigmaProtocol
open scoped ENNReal

variable {d k n q : ℕ} {C Coins : Type} [Fintype C] [Nonempty C]

/-- The oracle receives a message representative and the full module product. -/
abbrev Point (d n q : ℕ) := List Bool × (Fin d → Fin n → ZMod q)

/-- A classical self-target solver with saved coins. It receives the public matrix and returns
a message and an integer vector whose last polynomial must encode the challenge. -/
abbrev Adversary (d k n q : ℕ) (C Coins : Type) :=
  Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q) → Coins →
    OracleComp (fun _ : Point d n q => C) (List Bool × (Fin (k + 1) → Fin n → ℤ))

private abbrev Vec (k n : ℕ) := Fin (k + 1) → Fin n → ℤ

/-- Ring product of the matrix and an integer witness reduced coefficientwise. -/
@[expose] def product (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (y : Fin (k + 1) → Fin n → ℤ) :=
  moduleSISMap A (fun i j => (y i j : ZMod q))

/-- A short witness with last coordinate equal to a successful expansion of the reply. -/
@[expose] def accepts (expand : C → Option (Fin n → ZMod q)) (radius : ℕ)
    (y : Fin (k + 1) → Fin n → ℤ) (c : C) : Bool :=
  decide ((∀ i j, |y i j| ≤ radius) ∧ expand c = some (fun j => (y (Fin.last k) j : ZMod q)))

/-- Run the solver with a shared, lazy uniform random oracle and verify its candidate with
the same oracle, including candidates whose point it did not query. -/
@[expose] noncomputable def game (expand : C → Option (Fin n → ZMod q)) (radius : ℕ)
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) : PMF Bool := do
  let s ← coins
  let ((msg, y), cache) ← (interpret (ROMSignature.oracle C) (adv A s)).run []
  let (c, _) ← ROMSignature.oracle C (msg, product A y) cache
  return accepts expand radius y c

private def noSigner : ForkingReduction.Signer Empty Unit (Point d n q) C Unit Unit :=
  ⟨(), fun _ => Empty.elim⟩

private def check (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (expand : C → Option (Fin n → ZMod q)) (radius : ℕ) :
    ForkingReduction.Check (List Bool) (Vec k n) C Unit (Point d n q) Unit where
  point msg y := (msg, product A y)
  accepts _ y c _ := accepts expand radius y c
  fresh _ _ _ := true

private def liftSolver {α : Type} (B : OracleComp (fun _ : Point d n q => C) α) :
    OracleComp (ROMSignature.ForgerSpec Empty (Point d n q) Unit C) α :=
  interpret (fun p => query (Sum.inr p)) B

private def forger (B : OracleComp (fun _ : Point d n q => C) (List Bool × Vec k n)) :=
  (fun r => (r.1, r.2, ())) <$> liftSolver B

omit [Fintype C] [Nonempty C] in
private theorem bounded {B : OracleComp (fun _ : Point d n q => C) (List Bool × Vec k n)}
    {Q : ℕ} (hB : B.IsQueryBounded Q) :
    IsCostBounded ROMSignature.hashCost (forger B) Q :=
  (isCostBounded_map_iff _ _ _).mpr
    (hB.interpret (fun p => IsCostBounded.query (Sum.inr p)))

omit [Fintype C] [Nonempty C] in
private theorem noProgrammed (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (expand : C → Option (Fin n → ZMod q)) (radius : ℕ) :
    ForkingReduction.RejectsProgrammed noSigner (check A expand radius) :=
  fun _ e => e.elim

variable [DecidableEq C]

private def replay (fallback : C) (expand : C → Option (Fin n → ZMod q)) (radius Q : ℕ)
    (adv : Adversary d k n q C Coins) (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :=
  forkingAlgorithm fallback (Q + 1) fun s =>
    ForkingReduction.program noSigner (check A expand radius) (forger (adv A s)) []

private def difference {i β : Type} (result : Option (i ×
    ((β × ForkingReduction.Outcome (List Bool) (Vec k n) C Unit) × List (Point d n q)) ×
    ((β × ForkingReduction.Outcome (List Bool) (Vec k n) C Unit) × List (Point d n q)))) :
    Vec k n :=
  match result with
  | some (_, ((_, out), _), ((_, out'), _)) => out.commitment - out'.commitment
  | none => 0

/-- The program draws its private coins once and two independent reply tapes, then returns
the difference of the two accepted integer witnesses. A failed fork returns the zero vector. -/
def reduction (fallback : C) (expand : C → Option (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : ProbComp Coins) (tape : ProbComp (Fin (Q + 1) → C)) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) : ProbComp (Fin (k + 1) → Fin n → ℤ) := do
  let s ← coins
  let h ← tape
  let h' ← tape
  return difference (Forking.onTapes (replay fallback expand radius Q adv A) s h h')

private noncomputable def fork (fallback : C) (expand : C → Option (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :=
  Forking.fork coins (replay fallback expand radius Q adv A)

/-- Distribution of the extracted vector for an arbitrary saved-coin law and two uniform
reply tapes. `eval_reduction` realizes it whenever a program supplies the coins and tapes. -/
noncomputable def reductionLaw (fallback : C) (expand : C → Option (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) : PMF (Fin (k + 1) → Fin n → ℤ) :=
  (fork fallback expand radius Q coins adv A).map difference

/-- The concrete two-run program realizes the full distribution of the forking reduction. -/
theorem eval_reduction (fallback : C) (expand : C → Option (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : ProbComp Coins) (tape : ProbComp (Fin (Q + 1) → C))
    (uniform : tape.eval = PMF.uniformOfFintype _) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :
    (reduction fallback expand radius Q coins tape adv A).eval =
      reductionLaw fallback expand radius Q coins.eval adv A := by
  simp only [reduction, reductionLaw, fork, Forking.fork, uniform, pmf_norm,
    ProbComp.eval_bind, ProbComp.eval_pure]

omit [Fintype C] [Nonempty C] [DecidableEq C] in
private theorem solution_of_fork (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (expand : C → Option (Fin n → ZMod q)) {radius : ℕ} {y y' : Vec k n} {c c' : C}
    (hc : expand c ≠ expand c') (hprod : product A y = product A y')
    (hy : accepts expand radius y c) (hy' : accepts expand radius y' c') :
    IsSolution A (2 * radius) (y - y') := by
  simp only [accepts, decide_eq_true_eq] at hy hy'
  refine ⟨fun hz => hc (by rw [hy.2, hy'.2, sub_eq_zero.mp hz]), fun i j => ?_, ?_⟩
  · change |y i j - y' i j| ≤ _
    calc
      _ ≤ |y i j| + |y' i j| := abs_sub _ _
      _ ≤ (radius : ℤ) + radius := add_le_add (hy.1 i j) (hy'.1 i j)
      _ = _ := by push_cast; ring
  · have hcast : (fun i j => ((y - y') i j : ZMod q)) =
        (fun i j => (y i j : ZMod q)) - fun i j => (y' i j : ZMod q) :=
      funext₂ fun _ _ => Int.cast_sub _ _
    rw [hcast]
    exact add_right_cancel (b := product A y')
      (by simpa only [product, ← moduleSISMap_add, sub_add_cancel, zero_add] using hprod)

omit [DecidableEq C] in
private theorem oneRun (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (expand : C → Option (Fin n → ZMod q)) (radius : ℕ)
    (B : OracleComp (fun _ : Point d n q => C) (List Bool × Vec k n)) :
    ((interpret countingUniform (ForkingReduction.program noSigner (check A expand radius)
      (forger B) [])).run 0).map (fun ((_, out), _) => out.won) =
    ((interpret (ROMSignature.oracle C) B).run []).bind fun ((msg, y), cache) =>
      (ROMSignature.oracle C (msg, product A y) cache).map
        fun r => accepts expand radius y r.1 := by
  rw [ForkingReduction.map_run_program]
  let aux := withSampleList () (ForkingReduction.gameHandler
    (noSigner (d := d) (n := n) (q := q) (C := C)))
  have hrun := run_interpret_map_state (ROMSignature.oracle C) (fun p => aux (Sum.inr p))
    (fun t => ((t, []), [])) (fun p t => by
      simp only [aux, withSampleList, ForkingReduction.gameHandler, List.tail_nil,
        PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]) B []
  simp only [forger, liftSolver, interpret_map, interpret_interpret, interpret_query,
    StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map]
  change (((interpret (fun p => aux (Sum.inr p)) B).run (([], []), [])).bind _) = _
  rw [← hrun, PMF.bind_map]
  congr 1 with ⟨⟨msg, y⟩, cache⟩
  simp [ForkingReduction.finishGame, check]

private def collides (expand : C → Option (Fin n → ZMod q)) (c c' : C) : Bool :=
  decide (c ≠ c' ∧ (expand c).isSome ∧ expand c = expand c')

/-- Largest probability that a fresh uniform digest differs from a fixed digest and expands
to the same successfully decoded polynomial. Failed expansions contribute zero. -/
noncomputable def collisionMass (expand : C → Option (Fin n → ZMod q)) : ℝ≥0∞ :=
  Finset.univ.sup fun c => (PMF.uniformOfFintype C).map (collides expand c) true

/-- Count successful colliding digests directly. The first digest and all failure outputs are
excluded from each fiber. -/
theorem collisionMass_eq_card (expand : C → Option (Fin n → ZMod q)) :
    collisionMass expand = Finset.univ.sup fun c : C =>
      (Nat.card {c' : C // c ≠ c' ∧ (expand c).isSome ∧ expand c = expand c'} : ℝ≥0∞) /
        Fintype.card C := by
  simp only [collisionMass, Probability.PMF.uniformOfFintype_map_apply, collides,
    decide_eq_true_eq]

private theorem fork_collision_le (fallback : C) (expand : C → Option (Fin n → ZMod q))
    (radius Q : ℕ) (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :
    ((fork fallback expand radius Q coins adv A).map (fun r => r.any
      fun (_, ((_, a), _), ((_, b), _)) => collides expand a.challenge b.challenge)) true ≤
      collisionMass expand := by
  refine Forking.bad_reply_le coins (forkingAlgorithm fallback (Q + 1)
    fun s => ForkingReduction.program noSigner (check A expand radius) (forger (adv A s)) [])
      (fun r => r.1.2.challenge) (fun s h j hj => ?_) (collides expand)
  unfold forkingAlgorithm at hj ⊢
  generalize hrun : runWithAnswers _ _ (List.ofFn h) = run at hj ⊢
  obtain ⟨⟨pos, outcome⟩, queries⟩ := run
  obtain ⟨_, hnamed⟩ := ForkingReduction.runWithAnswers_program _ noSigner (check A expand radius)
    (noProgrammed A expand radius) (forger (adv A s)) [] _ hrun
  simpa only [List.getD_ofFn] using (hnamed j (validIndex_eq_some hj).1).2.1.symm

/-- Classical self-target success with a uniform digest oracle and deterministic partial
challenge expansion. A fork extracting two distinct polynomials gives a Module-SIS solution
at twice the radius. The additional probability inside the square root counts fresh distinct
digests that could expand to the same accepted polynomial. For fixed SHAKE256 in FIPS 204,
this quantity is a property of the concrete function and the bound here is only at most one. -/
theorem success_le_fork_digest (expand : C → Option (Fin n → ZMod q)) (radius Q : ℕ)
    (matrices : PMF (Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)))
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (hQ : ∀ A s, (adv A s).IsQueryBounded Q) (fallback : C := Classical.arbitrary C) :
    ((matrices.bind (game expand radius coins adv)) true).toReal ≤
      (Q + 1 : ℕ) / (Fintype.card C : ℝ) + Real.sqrt ((Q + 1 : ℕ) *
        ((matrices.bind fun A => (reductionLaw fallback expand radius Q coins adv A).map
          fun w => decide (IsSolution A (2 * radius) w)) true + collisionMass expand).toReal) := by
  let first := matrices.bind fun A => coins.map (A, ·)
  let succ := (matrices.bind fun A => (reductionLaw fallback expand radius Q coins adv A).map
    fun w => decide (IsSolution A (2 * radius) w)) true
  have h := ForkingReduction.toReal_le_add_sqrt_fork_of_le first noSigner
    (fun s => check s.1 expand radius) (fun s => noProgrammed s.1 expand radius)
    (fun s => forger (adv s.1 s.2)) (fun _ => []) (fun s => bounded (hQ s.1 s.2))
    (fallback := fallback) (ε := 0) (succ := succ + collisionMass expand) (by simp)
    (p := (matrices.bind (game expand radius coins adv)) true)
    (by simp [first, game, oneRun, pmf_norm])
  have hf : (Forking.fork first (forkingAlgorithm fallback (Q + 1)
      fun s => ForkingReduction.program noSigner (check s.1 expand radius)
        (forger (adv s.1 s.2)) [])).map Option.isSome true ≤ succ + collisionMass expand := by
    have hfork : Forking.fork first (forkingAlgorithm fallback (Q + 1)
          fun s => ForkingReduction.program noSigner (check s.1 expand radius)
            (forger (adv s.1 s.2)) []) =
        matrices.bind (fun A => fork fallback expand radius Q coins adv A) := by
      simp only [first, fork, replay, Forking.fork, pmf_norm, Function.comp_def]
      rfl
    rw [hfork, PMF.map_bind]
    refine Probability.PMF.bind_apply_le_add_const_on_support _ _ fun A _ =>
      le_trans ?_ (add_le_add le_rfl (fork_collision_le fallback expand radius Q coins adv A))
    simp only [reductionLaw, PMF.map_comp]
    simp only [← PMF.bind_pure_comp]
    refine Probability.PMF.bind_apply_le_add_on_support _ _ fun result hr => ?_
    rcases result with _ | ⟨j, ⟨⟨_, a⟩, _⟩, ⟨⟨_, b⟩, _⟩⟩
    · simp [difference]
    · obtain ⟨_, _, he, hc, ha, hb⟩ := ForkingReduction.exists_of_mem_support_fork
        (first := coins) noSigner (fun _ => check A expand radius)
        (fun _ => noProgrammed A expand radius) (fun s => forger (adv A s)) (fun _ => []) hr
      by_cases hsame : expand a.challenge = expand b.challenge
      · have hbad : collides expand a.challenge b.challenge = true :=
          decide_eq_true ⟨hc, by rw [(of_decide_eq_true ha).2]; rfl, hsame⟩
        simp [hbad]
      · simp [Function.comp_def, difference,
          solution_of_fork A expand hsame (congrArg Prod.snd he) ha hb]
  simpa [succ] using h hf (ENNReal.add_ne_top.mpr
    ⟨PMF.apply_ne_top _ _, ne_top_of_le_ne_top ENNReal.one_ne_top
      (Finset.sup_le fun _ _ => PMF.coe_le_one _ _)⟩)

/-- For ideal challenges embedded in the ring, different replies always produce different
last coordinates. The bound recovers the classical Dilithium §6.1 fork with zero collision loss. -/
theorem success_le_fork (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (matrices : PMF (Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)))
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (hQ : ∀ A s, (adv A s).IsQueryBounded Q) (fallback : C := Classical.arbitrary C) :
    ((matrices.bind (game (some ∘ encode) radius coins adv)) true).toReal ≤
      (Q + 1 : ℕ) / (Fintype.card C : ℝ) + Real.sqrt ((Q + 1 : ℕ) *
        ((matrices.bind fun A => (reductionLaw fallback (some ∘ encode) radius Q coins adv A).map
          fun w => decide (IsSolution A (2 * radius) w)) true).toReal) := by
  have hm : collisionMass (some ∘ encode) = 0 := le_antisymm
    (Finset.sup_le fun c _ => by simp [collides, Function.comp_def, encode.injective.eq_iff]) bot_le
  simpa only [hm, add_zero] using
    success_le_fork_digest (some ∘ encode) radius Q matrices coins adv hQ fallback

end Cslib.Crypto.ModuleSIS.SelfTarget
