/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Module
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ForkingReduction
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Classical random-oracle reduction from self-target solutions to Module-SIS

[BaiEtAl2021Dilithium], §6.1, “Classical Hardness of SelfTargetMSIS”, forks the solver
at the oracle query for its output. Two accepting runs at that point give short vectors
with the same module product and different last coordinates. Their integer difference
is a nonzero kernel vector with twice the coefficient bound.

The statement works for a given matrix, including the specification's systematic matrix
`[I | A]`. Its oracle answers are uniform in a finite challenge set embedded in the ring
polynomials. Use the sparse signed challenges for Dilithium. The verifier can make one last
oracle query, so the bound covers solvers that never queried their output point. The
experiment counts oracle queries and admits any saved-coin law. The two-run solver is a
`ProbComp` program with a supplied coin sampler, reply-tape sampler and fallback. Its
evaluation agrees with the analytical law whenever the two tapes are sampled uniformly.
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

private def product (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) (y : Vec k n) :=
  moduleSISMap A (fun i j => (y i j : ZMod q))

private def accepts (encode : C ↪ (Fin n → ZMod q)) (radius : ℕ) (y : Vec k n) (c : C) : Bool :=
  decide ((∀ i j, |y i j| ≤ radius) ∧ (fun j => (y (Fin.last k) j : ZMod q)) = encode c)

/-- Run the solver with a shared, lazy uniform random oracle and verify its candidate with
the same oracle, including candidates whose point it did not query. -/
noncomputable def game (encode : C ↪ (Fin n → ZMod q)) (radius : ℕ)
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) : PMF Bool := do
  let s ← coins
  let ((msg, y), cache) ← (interpret (ROMSignature.oracle C) (adv A s)).run []
  let (c, _) ← ROMSignature.oracle C (msg, product A y) cache
  return accepts encode radius y c

private def noSigner : ForkingReduction.Signer Empty Unit (Point d n q) C Unit Unit :=
  ⟨(), fun _ => Empty.elim⟩

private def check (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (encode : C ↪ (Fin n → ZMod q)) (radius : ℕ) :
    ForkingReduction.Check (List Bool) (Vec k n) C Unit (Point d n q) Unit where
  point msg y := (msg, product A y)
  accepts _ y c _ := accepts encode radius y c
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
    (encode : C ↪ (Fin n → ZMod q)) (radius : ℕ) :
    ForkingReduction.RejectsProgrammed noSigner (check A encode radius) :=
  fun _ e => e.elim

variable [DecidableEq C]

private def replay (fallback : C) (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (adv : Adversary d k n q C Coins) (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :=
  forkingAlgorithm fallback (Q + 1) fun s =>
    ForkingReduction.program noSigner (check A encode radius) (forger (adv A s)) []

private def difference {i β : Type} (result : Option (i ×
    ((β × ForkingReduction.Outcome (List Bool) (Vec k n) C Unit) × List (Point d n q)) ×
    ((β × ForkingReduction.Outcome (List Bool) (Vec k n) C Unit) × List (Point d n q)))) :
    Vec k n :=
  match result with
  | some (_, ((_, out), _), ((_, out'), _)) => out.commitment - out'.commitment
  | none => 0

/-- The program draws its private coins once and two independent reply tapes, then returns
the difference of the two accepted integer witnesses. A failed fork returns the zero vector. -/
def reduction (fallback : C) (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : ProbComp Coins) (tape : ProbComp (Fin (Q + 1) → C)) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) : ProbComp (Fin (k + 1) → Fin n → ℤ) := do
  let s ← coins
  let h ← tape
  let h' ← tape
  return difference (Forking.onTapes (replay fallback encode radius Q adv A) s h h')

private noncomputable def fork (fallback : C) (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :=
  Forking.fork coins (replay fallback encode radius Q adv A)

/-- Distribution of the extracted vector for an arbitrary saved-coin law and two uniform
reply tapes. `eval_reduction` realizes it whenever a program supplies the coins and tapes. -/
noncomputable def reductionLaw (fallback : C) (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) : PMF (Fin (k + 1) → Fin n → ℤ) :=
  (fork fallback encode radius Q coins adv A).map difference

/-- The concrete two-run program realizes the full distribution of the forking reduction. -/
theorem eval_reduction (fallback : C) (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (coins : ProbComp Coins) (tape : ProbComp (Fin (Q + 1) → C))
    (uniform : tape.eval = PMF.uniformOfFintype _) (adv : Adversary d k n q C Coins)
    (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)) :
    (reduction fallback encode radius Q coins tape adv A).eval =
      reductionLaw fallback encode radius Q coins.eval adv A := by
  simp only [reduction, reductionLaw, fork, Forking.fork, uniform, pmf_norm,
    ProbComp.eval_bind, ProbComp.eval_pure]

omit [Fintype C] [Nonempty C] [DecidableEq C] in
private theorem solution_of_fork (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (encode : C ↪ (Fin n → ZMod q)) {radius : ℕ} {y y' : Vec k n} {c c' : C}
    (hc : c ≠ c') (hprod : product A y = product A y')
    (hy : accepts encode radius y c) (hy' : accepts encode radius y' c') :
    IsSolution A (2 * radius) (y - y') := by
  simp only [accepts, decide_eq_true_eq] at hy hy'
  refine ⟨fun hz => hc (encode.injective ?_), ?_, ?_⟩
  · rw [← hy.2, ← hy'.2, sub_eq_zero.mp hz]
  · intro i j
    change |y i j - y' i j| ≤ _
    calc
      _ ≤ |y i j| + |y' i j| := abs_sub _ _
      _ ≤ (radius : ℤ) + radius := add_le_add (hy.1 i j) (hy'.1 i j)
      _ = _ := by push_cast; ring
  · let w := fun i j => (y i j : ZMod q)
    let w' := fun i j => (y' i j : ZMod q)
    have hsub : (fun i j => ((y - y') i j : ZMod q)) = w - w' := by
      funext i j
      exact Int.cast_sub _ _
    rw [hsub]
    apply add_right_cancel (b := moduleSISMap A w')
    simpa only [← moduleSISMap_add, sub_add_cancel, zero_add]
      using (show moduleSISMap A w = moduleSISMap A w' from hprod)

omit [DecidableEq C] in
private theorem oneRun (A : Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q))
    (encode : C ↪ (Fin n → ZMod q)) (radius : ℕ)
    (B : OracleComp (fun _ : Point d n q => C) (List Bool × Vec k n)) :
    ((interpret countingUniform (ForkingReduction.program noSigner (check A encode radius)
      (forger B) [])).run 0).map (fun ((_, out), _) => out.won) =
    ((interpret (ROMSignature.oracle C) B).run []).bind fun ((msg, y), cache) =>
      (ROMSignature.oracle C (msg, product A y) cache).map
        fun r => accepts encode radius y r.1 := by
  rw [ForkingReduction.map_run_program]
  let aux := withSampleList () (ForkingReduction.gameHandler
    (noSigner (d := d) (n := n) (q := q) (C := C)))
  have step (p : Point d n q) (t : List (Point d n q × C)) :
      (ROMSignature.oracle C p t).map
          (fun (a, t') => (a, (t', ([] : List Unit)), ([] : List Unit))) =
        aux (Sum.inr p) ((t, []), []) := by
    simp only [aux, withSampleList, ForkingReduction.gameHandler, List.tail_nil,
      PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  have hrun := run_interpret_map_state (ROMSignature.oracle C) (fun p => aux (Sum.inr p))
    (fun t => ((t, []), [])) step B []
  simp only [forger, liftSolver, interpret_map, interpret_interpret, interpret_query,
    StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map]
  change (((interpret (fun p => aux (Sum.inr p)) B).run (([], []), [])).bind _) = _
  rw [← hrun, PMF.bind_map]
  congr 1 with r
  rcases r with ⟨⟨msg, y⟩, cache⟩
  simp [ForkingReduction.finishGame, check]

/-- Classical random-oracle self-target success is bounded by the success of the explicit
two-run Module-SIS solver at twice the radius (Dilithium v3.1, §6.1). The additive and
square-root losses count the solver's hash queries and one final verifier query. The matrix
distribution may in particular sample a uniform right block and attach the identity. -/
theorem success_le_fork (encode : C ↪ (Fin n → ZMod q)) (radius Q : ℕ)
    (matrices : PMF (Matrix (Fin d) (Fin (k + 1)) (Fin n → ZMod q)))
    (coins : PMF Coins) (adv : Adversary d k n q C Coins)
    (hQ : ∀ A s, (adv A s).IsQueryBounded Q) (fallback : C := Classical.arbitrary C) :
    ((matrices.bind (game encode radius coins adv)) true).toReal ≤
      (Q + 1 : ℕ) / (Fintype.card C : ℝ) + Real.sqrt ((Q + 1 : ℕ) *
        ((matrices.bind fun A => (reductionLaw fallback encode radius Q coins adv A).map
          fun w => decide (IsSolution A (2 * radius) w)) true).toReal) := by
  let first := matrices.bind fun A => coins.map (A, ·)
  let succ := (matrices.bind fun A => (reductionLaw fallback encode radius Q coins adv A).map
    fun w => decide (IsSolution A (2 * radius) w)) true
  have h := ForkingReduction.toReal_le_add_sqrt_fork_of_le first noSigner
    (fun s => check s.1 encode radius) (fun s => noProgrammed s.1 encode radius)
    (fun s => forger (adv s.1 s.2)) (fun _ => []) (fun s => bounded (hQ s.1 s.2))
    (ε := 0) (succ := succ) (fallback := fallback) (by simp)
    (p := (matrices.bind (game encode radius coins adv)) true)
  have hwin : (matrices.bind (game encode radius coins adv)) true ≤
      first.bind (fun s => ((interpret countingUniform (ForkingReduction.program noSigner
        (check s.1 encode radius) (forger (adv s.1 s.2)) [])).run 0).map
          fun ((_, out), _) => out.won) true + 0 := by
    simp [first, game, oneRun, pmf_norm]
  have hf : (Forking.fork first (forkingAlgorithm fallback (Q + 1)
      fun s => ForkingReduction.program noSigner (check s.1 encode radius)
        (forger (adv s.1 s.2)) [])).map Option.isSome true ≤ succ := by
    have hmix : Forking.fork first (forkingAlgorithm fallback (Q + 1)
        fun s => ForkingReduction.program noSigner (check s.1 encode radius)
          (forger (adv s.1 s.2)) []) =
        matrices.bind (fun A => fork fallback encode radius Q coins adv A) := by
      simp only [first, fork, replay, Forking.fork, pmf_norm, Function.comp_def]
      rfl
    rw [hmix, PMF.map_bind]
    apply Probability.PMF.bind_apply_mono_on_support
    intro A _
    simp only [reductionLaw, PMF.map_comp]
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    apply Probability.PMF.bind_apply_mono_on_support
    intro result hr
    rcases result with _ | ⟨j, ⟨⟨_, a⟩, _⟩, ⟨⟨_, b⟩, _⟩⟩
    · simp [difference]
    · obtain ⟨s, _, he, hc, ha, hb⟩ := ForkingReduction.exists_of_mem_support_fork
        (first := coins) noSigner (fun _ => check A encode radius)
        (fun _ => noProgrammed A encode radius) (fun s => forger (adv A s)) (fun _ => []) hr
      have hw := solution_of_fork A encode hc (congrArg Prod.snd he) ha hb
      simp [Function.comp_def, difference, hw]
  simpa [succ] using h hwin hf (PMF.apply_ne_top _ _)

end Cslib.Crypto.ModuleSIS.SelfTarget
