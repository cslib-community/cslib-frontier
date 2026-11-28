/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Tactic.SuppCases

/-!
# Running and counting queries of `OracleComp.pi` and `OracleComp.replicate`

Execution (`ProbOracleComp.run`), simulation (`ProbOracleComp.simulate`), syntactic query bounds
(`ProbOracleComp.IsQueryBounded`), and exact stateful transcript lengths
(`OracleComp.withTranscript`) for finite tuples (`OracleComp.pi`) and independent repetitions
(`OracleComp.replicate`) of probabilistic oracle computations.

## Main results

* `Cslib.OracleComp.isCostBounded_pi`: cost budgets add along `OracleComp.pi`.
* `Cslib.ProbOracleComp.run_pi`, `Cslib.ProbOracleComp.run_pi_query`: running `OracleComp.pi`
  against a probabilistic or deterministic oracle.
* `Cslib.ProbOracleComp.simulate_pi`, `Cslib.ProbOracleComp.simulate_mapM`: simulating
  `OracleComp.pi` or a list traversal `List.mapM` distributes over its steps.
* `Cslib.ProbOracleComp.isQueryBounded_pi_query`,
  `Cslib.ProbOracleComp.length_transcript_pi_query`: a tuple of `m` external queries makes at most
  `m` (and on every supported transcript, exactly `m`) external queries.
* `Cslib.ProbOracleComp.run_replicate`: running `OracleComp.replicate k program` against an oracle
  repeats `ProbOracleComp.run program O`.
* `Cslib.ProbOracleComp.isQueryBounded_replicate`,
  `Cslib.ProbOracleComp.length_transcript_replicate`: repeating a `q`-query computation `k` times
  makes at most `k * q` (and on every supported transcript, exactly `k * q`) external queries.
-/

public section

namespace Cslib.OracleComp

/-- Budgets add along `OracleComp.pi`: if each of `m` coordinate programs costs at most `c`, the
tuple costs at most `m * c`. -/
theorem isCostBounded_pi {ι : Type} {spec : ι → Type} {cost : ι → ℕ} {m : ℕ}
    {β : Fin m → Type} {programs : (i : Fin m) → OracleComp spec (β i)} {c : ℕ}
    (h : ∀ i, OracleComp.IsCostBounded cost (programs i) c) :
    OracleComp.IsCostBounded cost (OracleComp.pi programs) (m * c) := by
  induction m with
  | zero => exact .pure _ _
  | succ m ih =>
    rw [OracleComp.pi_succ]
    exact ((h 0).bind fun _ => (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (ih fun i => h i.succ)).mono (by rw [Nat.succ_mul, Nat.add_comm])

end Cslib.OracleComp

namespace Cslib.ProbOracleComp

variable {Query α : Type} {spec : Query → Type}

/-- Running `OracleComp.pi` against an oracle runs each coordinate program in order. -/
theorem run_pi {m : ℕ} {β : Fin m → Type}
    (programs : (i : Fin m) → ProbOracleComp spec (β i))
    (O : (q : Query) → ProbComp (spec q)) :
    ProbOracleComp.run (OracleComp.pi programs) O =
      OracleComp.pi (fun i => ProbOracleComp.run (programs i) O) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.run_bind, ProbOracleComp.run_map,
      ih (fun i => programs i.succ)]

/-- Simulating `OracleComp.pi` under an oracle simulation `h` simulates each coordinate program
in order. -/
theorem simulate_pi {Query₁ Query₂ : Type} {spec₁ : Query₁ → Type} {spec₂ : Query₂ → Type}
    (h : (q : Query₁) → ProbOracleComp spec₂ (spec₁ q)) :
    {k : ℕ} → {α : Fin k → Type} → (p : (i : Fin k) → ProbOracleComp spec₁ (α i)) →
      ProbOracleComp.simulate h (OracleComp.pi p) =
        OracleComp.pi fun i => ProbOracleComp.simulate h (p i)
  | 0, _, _ => by simp [OracleComp.pi_zero]
  | k + 1, _, p => by
    rw [OracleComp.pi_succ, OracleComp.pi_succ, ProbOracleComp.simulate_bind]
    congr 1
    funext first
    rw [ProbOracleComp.simulate_map, simulate_pi h (fun i => p i.succ)]

/-- Simulating a list traversal under an oracle simulation `h` simulates each step in order. -/
theorem simulate_mapM {Query₁ Query₂ β γ : Type} {spec₁ : Query₁ → Type}
    {spec₂ : Query₂ → Type} (h : (q : Query₁) → ProbOracleComp spec₂ (spec₁ q))
    (f : β → ProbOracleComp spec₁ γ) (l : List β) :
    ProbOracleComp.simulate h (l.mapM f) = l.mapM fun b => ProbOracleComp.simulate h (f b) := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.mapM_cons, ih]

/-- Running a tuple of external queries against a deterministic oracle returns the tuple of
answers. -/
theorem run_pi_query {m : ℕ} (q : Fin m → Query) (O : (x : Query) → spec x) :
    ProbOracleComp.run
      (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i)))
      (fun x => pure (O x)) = pure (fun i => O (q i)) := by
  induction m with
  | zero =>
    exact congrArg pure (funext fun i => i.elim0)
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.run_bind, ProbOracleComp.run_query,
      ProbOracleComp.run_map, ih (fun i => q i.succ), pure_bind, map_pure]
    exact congrArg pure (funext (Fin.cases rfl fun _ => rfl))

/-- A tuple of `m` external queries makes at most `m` external queries. -/
theorem isQueryBounded_pi_query {m : ℕ} (q : Fin m → Query) :
    ProbOracleComp.IsQueryBounded
      (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i))) m := by
  simpa using OracleComp.isCostBounded_pi (c := 1) fun i => IsQueryBounded.query (q i)

/-- Every supported stateful execution of a tuple of `m` external queries logs a transcript of
exact length `m`. -/
theorem length_transcript_pi_query {m : ℕ} {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) (q : Fin m → Query)
    {s s' : State} {result : (i : Fin m) → spec (q i)}
    {transcript : OracleComp.Transcript spec}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i)))
        (s, [])).support) :
    transcript.length = m := by
  induction m generalizing s s' transcript with
  | zero =>
    supp_cases hmem [OracleComp.pi_zero, runWith_norm]
    rfl
  | succ m ih =>
    supp_cases hmem [OracleComp.pi_succ, runWith_norm, OracleComp.withTranscript] with
      ⟨_, ⟨⟨ans, next⟩, -, rfl⟩, ⟨rest, s₂, total⟩, hrest, -, rfl, rfl⟩
    rw [ProbOracleComp.run_interpret_withTranscript_append] at hrest
    supp_cases hrest with ⟨⟨rest', final, fresh⟩, hfresh, rfl, rfl, rfl⟩
    simp [ih (fun i => q i.succ) hfresh]

/-- Running `OracleComp.replicate` against an oracle repeats the run of the underlying program. -/
@[simp]
theorem run_replicate (k : ℕ) (program : ProbOracleComp spec α)
    (O : (q : Query) → ProbComp (spec q)) :
    ProbOracleComp.run (OracleComp.replicate k program) O =
      OracleComp.replicate k (ProbOracleComp.run program O) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [OracleComp.replicate_succ, ih]

/-- Repeating a `q`-query-bounded program `k` times makes at most `k * q` queries. -/
theorem isQueryBounded_replicate (k : ℕ) {program : ProbOracleComp spec α} {q : ℕ}
    (hq : program.IsQueryBounded q) :
    ProbOracleComp.IsQueryBounded (OracleComp.replicate k program) (k * q) := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    exact .pure _ 0
  | succ k ih =>
    rw [OracleComp.replicate_succ, Nat.succ_mul, Nat.add_comm]
    exact hq.bind fun _ => (OracleComp.isCostBounded_map_iff _ _ _).mpr ih

/-- If every supported execution of `program` makes exactly `q` external queries, then every
supported execution of `OracleComp.replicate k program` makes exactly `k * q` external queries. -/
theorem length_transcript_replicate {State : Type}
    (oracle : (x : Query) → StateT State PMF (spec x)) (k : ℕ)
    {program : ProbOracleComp spec α} {q : ℕ}
    (hq : ∀ {s s' : State} {result : α} {tr : OracleComp.Transcript spec},
      (result, s', tr) ∈
        (ProbOracleComp.runWith (OracleComp.withTranscript oracle) program (s, [])).support →
        tr.length = q)
    {s s' : State} {results : List α} {transcript : OracleComp.Transcript spec}
    (hmem : (results, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (OracleComp.replicate k program) (s, [])).support) :
    transcript.length = k * q := by
  induction k generalizing s s' results transcript with
  | zero =>
    supp_cases hmem [OracleComp.replicate_zero, runWith_norm]
    simp
  | succ k ih =>
    supp_cases hmem [OracleComp.replicate_succ, runWith_norm] with
      ⟨⟨first, s₁, seen⟩, hfirst, ⟨rest, s₂, total⟩, hrest, -, rfl, rfl⟩
    rw [ProbOracleComp.run_interpret_withTranscript_append] at hrest
    supp_cases hrest with ⟨⟨rest', final, fresh⟩, hfresh, rfl, rfl, rfl⟩
    simp [hq hfirst, ih hfresh, Nat.succ_mul, Nat.add_comm]

end Cslib.ProbOracleComp
