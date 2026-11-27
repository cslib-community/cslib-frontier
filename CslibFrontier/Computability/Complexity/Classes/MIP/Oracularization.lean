/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Repetition
public import CslibFrontier.Computability.Complexity.Classes.PCP.Oracle
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.QueryBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# Oracularization: `PCPPoly ⊆ MIP₂`

Step 1 of the combined proof of Theorems 2.3 and 2.4 in
[Babai, Fortnow and Lund, §2, pp. 5–6][BabaiFortnowLund1991] converts a proof oracle into
two independent provers. Those theorems credit Fortnow–Rompel–Sipser and
Ben-Or–Goldwasser–Kilian–Wigderson. Here the strict uniform verifier has perfect completeness
and soundness
at most one half. Our adaptation selects a padded query index before the run, checks it online,
and derives an explicit rejection probability for amplification. In
one round (`Cslib.Complexity.Oracularize.round`) the verifier draws an index `j`, runs the proof
verifier with every query answered by the first bit of prover `0`'s reply, and also sends the
`j`-th query to prover `1`, rejecting when the two first bits disagree
(`Cslib.Complexity.Oracularize.handler`).

* **Completeness.** Two copies of a proof are accepted as the proof is
  (`Cslib.Complexity.Oracularize.acceptProb_round_honest`).
* **Soundness.** Prover `1` sees one query, so its answer law `ν_q` can be sampled after the run of
  the proof verifier against prover `0` (`Cslib.Complexity.Oracularize.tsum_composite_before`).
  Runs agreeing with the most likely answers of prover `1` are runs against a fixed proof
  (`Cslib.Complexity.Oracularize.tsum_logged_consistent_le`); on the others some checked index is
  rejected with probability at least `1 / 2`. With at most `T` queries the round accepts with
  probability at most `1 - 1 / (4 (T + 1))` (`Cslib.Complexity.Oracularize.acceptProb_round_le`).

Fair coins sample a uniform index exactly only from a power of two, so the verifier reads `j`
from `m` fair bits (`Cslib.Complexity.Oracularize.roundBits`), with the acceptance probability of
the round for `T = 2 ^ m - 1` (`Cslib.Complexity.Oracularize.acceptProb_roundBits`). Sequential
repetition against non-communicating provers
(`Cslib.Complexity.acceptProb_sequentialRepeat_independent_le`)
then gives `PCPPoly ⊆ MIP₂`
(`Cslib.Complexity.PCPPoly_subset_MIP₂`).

## Main definitions

* `Cslib.Complexity.Oracularize.round`, `Cslib.Complexity.Oracularize.roundBits`: the
  oracularized round, with a uniform and a coin-sampled check index.

## Main results

* `Cslib.Complexity.Oracularize.acceptProb_round_honest`,
  `Cslib.Complexity.Oracularize.acceptProb_round_le`: completeness and soundness of a round.
* `Cslib.Complexity.Oracularize.isOraclePPTOn_roundBits`: efficiency of a round.
* `Cslib.Complexity.PCPPoly_subset_MIP₂`.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### Oracularization -/

namespace Oracularize

/-- Bookkeeping for the random consistency check in an oracularized round. -/
structure CheckState where
  /-- Number of queries already answered by the first prover. -/
  count : ℕ
  /-- Whether the provers disagreed on the selected query. -/
  disagreed : Bool

/-- The framed binary query count followed by the disagreement bit. -/
enc_structure encCheckState : CheckState where
  count : encNat, disagreed : encBool

/-- The checker's state and the private states of the noncommunicating provers. -/
structure CompositeState (σ : Type) where
  /-- The checker's query count and recorded disagreement. -/
  check : CheckState
  /-- The two private prover states. -/
  provers : σ

/-- A prover's private state together with the query-answer history observed by the verifier. -/
structure LoggedState (σ : Type) where
  /-- The private state of the prover supplying the answers. -/
  prover : σ
  /-- Query words and first answer bits in reverse chronological order. -/
  history : List (List Bool × Bool)

/-- The handler of the oracularized round: every query of the proof verifier is answered by the
first bit of prover `0`'s reply; the `j`-th query is also sent to prover `1`, and a disagreement
of its first bit is recorded. The state counts the queries and records a disagreement. -/
noncomputable def handler (j : ℕ) (q : Unit × List Bool) (st : CheckState) :
    WordOracleComp (Fin 2) (List Bool × CheckState) := do
  let r₀ ← ProbOracleComp.query ((0 : Fin 2), q.2)
  if st.count = j then do
    let r₁ ← ProbOracleComp.query ((1 : Fin 2), q.2)
    pure ([r₀.headD false], ⟨st.count + 1, st.disagreed || (r₁.headD false != r₀.headD false)⟩)
  else pure ([r₀.headD false], ⟨st.count + 1, st.disagreed⟩)

/-- The proof verifier run through `handler j`, from no queries and no disagreement. -/
noncomputable def checked (V : WordOracleComp Unit Bool) (j : ℕ) :
    WordOracleComp (Fin 2) (Bool × CheckState) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (handler j)) V).run ⟨0, false⟩

/-- **The oracularized round**: draw `j ≤ T` uniformly, run the proof verifier against prover `0`
with its `j`-th query checked against prover `1`, and accept when the verifier accepts and no
disagreement was found. -/
noncomputable def round (V : WordOracleComp Unit Bool) (T : ℕ) : WordOracleComp (Fin 2) Bool := do
  let j ← ProbOracleComp.sample (ProbComp.unifFin T)
  let r ← checked V j
  pure (r.1 && !r.2.disagreed)

/-- The single prover seen by the proof verifier in the oracularized round: the handler's state
together with the joint state of the two provers. -/
noncomputable abbrev composite (j : ℕ) (P : Fin 2 → Prover Unit) : Prover Unit where
  State := CompositeState (Prover.independent P).State
  init := ⟨⟨0, false⟩, (Prover.independent P).init⟩
  respond q := StateT.mk fun st =>
    ((Prover.independent P).run (handler j q st.check) st.provers).map fun x =>
      (x.1.1, CompositeState.mk x.1.2 x.2)

/-- **The checked run is a run against the composite prover.** -/
private theorem run_checked (V : WordOracleComp Unit Bool) (j : ℕ) (P : Fin 2 → Prover Unit)
    (s : (Prover.independent P).State) :
    (Prover.independent P).run (checked V j) s =
      ((composite j P).run V ⟨⟨0, false⟩, s⟩).map fun x => ((x.1, x.2.check), x.2.provers) := by
  let pack : CompositeState (Prover.independent P).State →
      CheckState × (Prover.independent P).State := fun st => (st.check, st.provers)
  let oracle (q : Unit × List Bool) (st : CheckState × (Prover.independent P).State) :=
    ((Prover.independent P).run (handler j q st.1) st.2).map fun x => (x.1.1, x.1.2, x.2)
  have sim := ProbOracleComp.runWith_map_state (composite j P).respond oracle pack
    (fun q st => by exact PMF.map_comp ..) V ⟨⟨0, false⟩, s⟩
  rw [show (Prover.independent P).run (checked V j) s =
      (ProbOracleComp.runWith oracle V (⟨0, false⟩, s)).map
        (fun x => ((x.1, x.2.1), x.2.2)) from
    ProbOracleComp.runWith_run_interpret _ _ _ _ _]
  change _ = PMF.map _ (ProbOracleComp.runWith _ _ _)
  rw [← sim, PMF.map_comp]
  rfl

/-- Against two honest proof oracles, the handler answers with the proof's bit, counts the query
and records no disagreement. -/
private theorem run_handler_honest (π : List Bool → Bool) (j : ℕ) (q : Unit × List Bool)
    (st : CheckState)
    (s : (Prover.independent fun _ : Fin 2 => Prover.ofProof π).State) :
    (Prover.independent fun _ : Fin 2 => Prover.ofProof π).run (handler j q st) s =
      PMF.pure (([π q.2], ⟨st.count + 1, st.disagreed⟩), s) := by
  have h0 (i : Fin 2) (msg : List Bool)
      (t : (Prover.independent fun _ : Fin 2 => Prover.ofProof π).State) :
      (Prover.independent fun _ : Fin 2 => Prover.ofProof π).run
        (ProbOracleComp.query (i, msg)) t = PMF.pure ([π msg], t) := by
    rw [Prover.run_query]
    change PMF.map _ (PMF.pure _) = _
    erw [PMF.pure_map]
    congr 2
  simp only [handler, Prover.run_bind, h0, PMF.pure_bind, List.headD_cons]
  split_ifs
  · simp only [Prover.run_bind, h0, PMF.pure_bind, List.headD_cons, Prover.run_pure,
      bne_self_eq_false,
      Bool.or_false]
  · simp only [Prover.run_pure]

/-- The prover with a disagreement flag that answers every query by the proof's bit. -/
private noncomputable def flagged (π : List Bool → Bool) : Prover Unit where
  State := Bool
  init := false
  respond q b := PMF.pure ([π q.2], b)

/-- The composite of the honest provers simulates the flagged proof oracle, through the flag. -/
private theorem run_composite_honest (π : List Bool → Bool) (j : ℕ) (V : WordOracleComp Unit Bool) :
    ((composite j fun _ => Prover.ofProof π).run V
        (composite j fun _ => Prover.ofProof π).init).map
        (Prod.map id fun st => st.check.disagreed) =
      ((Prover.ofProof π).run V ()).map (Prod.map id fun _ => false) := by
  have hsim₁ : ∀ q (st : (composite j fun _ => Prover.ofProof π).State),
      (((composite j fun _ => Prover.ofProof π).respond q).run st).map
        (Prod.map id fun st => st.check.disagreed) =
        ((flagged π).respond q).run st.check.disagreed := by
    intro q st
    change PMF.map _ (PMF.map _ ((Prover.independent _).run (handler j q st.check) st.provers)) = _
    rw [run_handler_honest]
    erw [PMF.map_comp, PMF.pure_map]
    rfl
  have hsim₂ : ∀ q (st : (Prover.ofProof π : Prover Unit).State),
      (((Prover.ofProof π : Prover Unit).respond q).run st).map (Prod.map id fun _ => false) =
        ((flagged π).respond q).run false := by
    intro q st
    change PMF.map _ (PMF.pure _) = PMF.pure _
    erw [PMF.pure_map]
    rfl
  exact (ProbOracleComp.runWith_map_state (composite j fun _ => Prover.ofProof π).respond
    (flagged π).respond
    (fun st : (composite j fun _ => Prover.ofProof π).State => st.check.disagreed) hsim₁ V _).trans
    (ProbOracleComp.runWith_map_state (Prover.ofProof π).respond (flagged π).respond
      (fun _ => false) hsim₂ V ()).symm

/-- **Completeness of the oracularized round**: two copies of a proof are accepted with the
probability that the proof verifier accepts the proof. -/
theorem acceptProb_round_honest (V : WordOracleComp Unit Bool) (T : ℕ) (π : List Bool → Bool) :
    acceptProb (round V T) (Prover.independent fun _ : Fin 2 => Prover.ofProof π) =
      acceptProb V (Prover.ofProof π) := by
  rw [round, acceptProb_sample_bind]
  have hj (j : Fin (T + 1)) : acceptProb (do let r ← checked V j; pure (r.1 && !r.2.disagreed))
      (Prover.independent fun _ : Fin 2 => Prover.ofProof π) = acceptProb V (Prover.ofProof π) := by
    rw [acceptProb, acceptProb, Prover.run_bind, run_checked]
    have key := congrArg (PMF.map (fun y : Bool × Bool => y.1 && !y.2)) (run_composite_honest π j V)
    simp only [PMF.map_comp] at key
    simp only [Prover.run_pure]
    erw [PMF.bind_pure_comp]
    simp only [PMF.map_comp]
    have hf : (Prod.fst ∘ (fun x : (Bool × CheckState) ×
          (Prover.independent fun _ : Fin 2 => Prover.ofProof π).State =>
          (x.1.1 && !x.1.2.disagreed, x.2)) ∘
        fun x : Bool × (composite j fun _ => Prover.ofProof π).State =>
          ((x.1, x.2.check), x.2.provers)) =
        ((fun y : Bool × Bool => y.1 && !y.2) ∘ Prod.map id fun st => st.check.disagreed) := rfl
    have hg : ((fun y : Bool × Bool => y.1 && !y.2) ∘ Prod.map id fun _ : Unit => false) =
        Prod.fst := by
      funext x
      simp
    erw [hf, key, hg]
  simp only [hj, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! #### Soundness -/

/-- The prover answering by the first bit of `P`'s reply and logging every query with its bit,
most recent first. -/
noncomputable abbrev logged (P : Prover Unit) : Prover Unit where
  State := LoggedState P.State
  init := ⟨P.init, []⟩
  respond q := StateT.mk fun st =>
    ((P.respond q).run st.prover).map fun x =>
      ([x.1.headD false], LoggedState.mk x.2 ((q.2, x.1.headD false) :: st.history))

private theorem run_uniform_query {ι : Type} (P : Prover ι) (n : ℕ) (s : P.State) :
    P.run (OracleComp.query (Sum.inl n)) s = (ProbComp.unifOracle n).map (·, s) := by
  rw [← ProbOracleComp.sample_unifFin, Prover.run_sample, ProbComp.eval_unifFin]
  rfl

private theorem run_logged_query (P : Prover Unit) (q : Unit × List Bool) (s : (logged P).State) :
    (logged P).run (OracleComp.query (Sum.inr q)) s =
      ((P.respond q).run s.prover).map fun x =>
        ([x.1.headD false], LoggedState.mk x.2 ((q.2, x.1.headD false) :: s.history)) :=
  (logged P).run_query q s

/-- A log is consistent with the proof `π` when every logged bit is the proof's bit. -/
def Consistent (π : List Bool → Bool) (log : List (List Bool × Bool)) : Prop :=
  ∀ e ∈ log, e.2 = π e.1

instance (π : List Bool → Bool) (log : List (List Bool × Bool)) :
    Decidable (Consistent π log) := by
  unfold Consistent
  infer_instance

/-- **Coupling with a proof**: the runs of a program against the logged prover that end with a
log consistent with `π` and result `true` have at most the probability that the program accepts
the proof `π`. -/
theorem tsum_logged_consistent_le (π : List Bool → Bool) (P : Prover Unit)
    (W : WordOracleComp Unit Bool) (s : (logged P).State) :
    ∑' x, (logged P).run W s x * (if x.1 = true ∧ Consistent π x.2.history then 1 else 0) ≤
      if Consistent π s.history then ((Prover.ofProof π).run W ()).map Prod.fst true else 0 := by
  induction W using PFunctor.FreeM.induction generalizing s with
  | pure a =>
    rw [Prover.run_pure, Prover.run_pure]
    rw [tsum_eq_single (a, s) fun x hx => by simp [PMF.pure_apply, hx]]
    simp only [PMF.pure_apply, ite_true, one_mul, PMF.pure_map]
    split_ifs <;> simp_all
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      Prover.run_bind, Prover.run_bind]
    set g : Bool × (logged P).State → ENNReal :=
      fun x => if x.1 = true ∧ Consistent π x.2.history then 1 else 0
    rw [Probability.PMF.tsum_bind_mul]
    refine (tsum_le_tsum fun (y : _ × (logged P).State) =>
      mul_le_mul' le_rfl (ih y.1 y.2)).trans ?_
    cases q with
    | inl n =>
      have h1 := run_uniform_query (logged P) n s
      have h2 := run_uniform_query (Prover.ofProof (Operation := Unit) π) n ()
      rw [h1, h2, Probability.PMF.tsum_map_mul, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
      split_ifs with hc
      · exact le_of_eq (tsum_congr fun b => by simp)
      · simp
    | inr q =>
      have h1 := run_logged_query P q s
      have h2 : (Prover.ofProof (Operation := Unit) π).run (OracleComp.query (Sum.inr q)) () =
          PMF.pure ([π q.2], ()) := by
        exact Prover.run_query _ _ _
      rw [h1, h2, Probability.PMF.tsum_map_mul, PMF.pure_bind]
      calc ∑' b, ((P.respond q).run s.prover) b *
          (if Consistent π ((q.2, b.1.headD false) :: s.history)
              then (PMF.map Prod.fst ((Prover.ofProof π).run (cont [b.1.headD false]) ())) true
              else 0)
          ≤ ∑' b, ((P.respond q).run s.prover) b * (if Consistent π s.history
              then (PMF.map Prod.fst ((Prover.ofProof π).run (cont [π q.2]) ())) true else 0) :=
            tsum_le_tsum fun (b : List Bool × P.State) => mul_le_mul' le_rfl (by
              by_cases hb : Consistent π ((q.2, b.1.headD false) :: s.history)
              · have h1 : b.1.headD false = π q.2 := hb _ (List.mem_cons_self ..)
                have h2 : Consistent π s.history := fun e he => hb e (List.mem_cons_of_mem _ he)
                rw [ite_eq_left hb, ite_eq_left h2, h1]
              · rw [ite_eq_right hb]
                exact zero_le)
        _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Logs only grow**: every final log of a run against the logged prover extends the initial
log by the queries of the run. -/
private theorem exists_log_eq_append (P : Prover Unit) {β : Type} (W : WordOracleComp Unit β)
    (s : (logged P).State) (x : β × (logged P).State) (hx : x ∈ ((logged P).run W s).support) :
    ∃ ext, x.2.history = ext ++ s.history := by
  induction W using PFunctor.FreeM.induction generalizing s with
  | pure a =>
    rw [Prover.run_pure, PMF.mem_support_pure_iff] at hx
    exact ⟨[], by simp [hx]⟩
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      Prover.run_bind, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨ext, hext⟩ := ih y.1 y.2 hxy
    cases q with
    | inl n =>
      have h1 := run_uniform_query (logged P) n s
      rw [h1, PMF.mem_support_map_iff] at hy
      obtain ⟨b, -, rfl⟩ := hy
      exact ⟨ext, hext⟩
    | inr q =>
      have h1 := run_logged_query P q s
      rw [h1, PMF.mem_support_map_iff] at hy
      obtain ⟨r, -, rfl⟩ := hy
      exact ⟨ext ++ [(q.2, r.1.headD false)], by simp [hext]⟩

/-- **Query budgets bound the log**: a run of a program making at most `T` external queries adds
at most `T` entries to the log. -/
private theorem length_log_le (P : Prover Unit) {β : Type} {W : WordOracleComp Unit β} {T : ℕ}
    (hW : W.IsQueryBounded T) (s : (logged P).State) (x : β × (logged P).State)
    (hx : x ∈ ((logged P).run W s).support) : x.2.history.length ≤ s.history.length + T := by
  induction hW generalizing s with
  | pure a n =>
    rw [Prover.run_pure, PMF.mem_support_pure_iff] at hx
    simp [hx]
  | liftBind q cont n hcont ih =>
    rw [Prover.run_bind, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have := ih y.1 y.2 hxy
    cases q with
    | inl m =>
      have h1 := run_uniform_query (logged P) m s
      rw [h1, PMF.mem_support_map_iff] at hy
      obtain ⟨b, -, rfl⟩ := hy
      simpa using this
    | inr q =>
      have h1 := run_logged_query P q s
      rw [h1, PMF.mem_support_map_iff] at hy
      obtain ⟨r, -, rfl⟩ := hy
      simp only [List.length_cons, Sum.elim_inr] at this ⊢
      omega

/-- One handler step that does not check: only prover `0` is asked. -/
private theorem run_handler_of_ne (P : Fin 2 → Prover Unit) {j : ℕ} (q : Unit × List Bool)
    (st : CheckState) (hst : st.count ≠ j) (ps : (Prover.independent P).State) :
    (Prover.independent P).run (handler j q st) ps =
      (((P 0).respond ((), q.2)).run (ps 0)).map fun x =>
        (([x.1.headD false], ⟨st.count + 1, st.disagreed⟩), Function.update ps 0 x.2) := by
  simp only [handler, Prover.run_bind, Prover.run_query, ite_eq_right hst, Prover.run_pure]
  change (PMF.map _ _).bind _ = _
  rw [PMF.bind_map]
  rfl

/-- The checking handler step: prover `0` and then prover `1` are asked. -/
private theorem run_handler_self (P : Fin 2 → Prover Unit) (q : Unit × List Bool) (st : CheckState)
    (ps : (Prover.independent P).State) :
    (Prover.independent P).run (handler st.count q st) ps =
      (((P 0).respond ((), q.2)).run (ps 0)).bind fun x =>
        (((P 1).respond ((), q.2)).run (ps 1)).map fun y =>
          (([x.1.headD false],
            ⟨st.count + 1, st.disagreed || (y.1.headD false != x.1.headD false)⟩),
            Function.update (Function.update ps 0 x.2) 1 y.2) := by
  simp only [handler, Prover.run_bind, Prover.run_query]
  change (PMF.map _ _).bind _ = _
  rw [PMF.bind_map]
  congr 1
  funext x
  change (PMF.map _ _).bind _ = _
  rw [PMF.bind_map]
  simp only [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  rw [← PMF.bind_pure_comp]
  rfl

/-- **After the check**: once the checked query has passed, the composite prover is the logged
prover `0`, with the disagreement flag fixed. -/
private theorem run_composite_after (j : ℕ) (P : Fin 2 → Prover Unit) (bad : Bool)
    (ps : (Prover.independent P).State) (W : WordOracleComp Unit Bool) (s : (logged (P 0)).State)
    (hs : j < s.history.length) :
    ((logged (P 0)).run W s).map (Prod.map id fun st : (logged (P 0)).State =>
        (⟨⟨st.history.length, bad⟩, Function.update ps 0 st.prover⟩ : (composite j P).State)) =
      (composite j P).run W ⟨⟨s.history.length, bad⟩, Function.update ps 0 s.prover⟩ := by
  refine ProbOracleComp.runWith_map_state_of_invariant (logged (P 0)).respond
    (composite j P).respond
    (fun st => ⟨⟨st.history.length, bad⟩, Function.update ps 0 st.prover⟩)
    (fun st => j < st.history.length) (fun q st hst a st' hx => ?_) (fun q st hst => ?_) W s hs
  · have h1 : ((logged (P 0)).respond q).run st = (((P 0).respond q).run st.prover).map fun x =>
        ([x.1.headD false], (LoggedState.mk x.2 ((q.2, x.1.headD false) :: st.history))) := rfl
    change (a, st') ∈ (((logged (P 0)).respond q).run st).support at hx
    rw [h1, PMF.mem_support_map_iff] at hx
    obtain ⟨y, -, heq⟩ := hx
    cases heq
    simp only [List.length_cons]
    omega
  · change PMF.map _ (PMF.map _ _) = PMF.map _ ((Prover.independent P).run (handler j q _) _)
    rw [run_handler_of_ne P q _ (by simp only; omega), PMF.map_comp]
    erw [PMF.map_comp]
    simp only [Function.update_self, Function.update_idem]
    rfl

/-- The probability that prover `P`, from its initial state, answers `q` with first bit `b`. -/
noncomputable def answerProb (P : Prover Unit) (q : List Bool) (b : Bool) : ENNReal :=
  (((P.respond ((), q)).run P.init).map fun x => x.1.headD false) b

/-- The weight of a log at the checked index `j`: the probability that prover `P` agrees with the
logged bit of the `j`-th query, or `1` when there are at most `j` queries. -/
noncomputable def weight (P : Prover Unit) (j : ℕ) (log : List (List Bool × Bool)) : ENNReal :=
  match log.reverse[j]? with
  | some e => answerProb P e.1 e.2
  | none => 1

/-- The weight is `1` while the log has at most `j` entries. -/
private theorem weight_of_length_le (P : Prover Unit) {j : ℕ} {log : List (List Bool × Bool)}
    (h : log.length ≤ j) : weight P j log = 1 := by
  rw [weight, List.getElem?_eq_none (by simpa using h)]

/-- The weight of an extension of a log of length `j` ending with the entry `e` is the agreement
probability of `e`. -/
private theorem weight_append_cons (P : Prover Unit) (ext log : List (List Bool × Bool))
    (e : List Bool × Bool) : weight P log.length (ext ++ e :: log) = answerProb P e.1 e.2 := by
  rw [weight, List.reverse_append, List.reverse_cons, List.append_assoc,
    List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self]
  simp

/-- **Deferred sampling**: before the checked query, the probability that the composite prover is
accepted without a disagreement is the expected weight of the final log of the logged prover `0`
on its accepting runs. -/
theorem tsum_composite_before (j : ℕ) (P : Fin 2 → Prover Unit) (ps : (Prover.independent P).State)
    (hps : ps 1 = (P 1).init) (W : WordOracleComp Unit Bool) (s : (logged (P 0)).State)
    (hs : s.history.length ≤ j) :
    ∑' x, (composite j P).run W
        (CompositeState.mk ⟨s.history.length, false⟩ (Function.update ps 0 s.prover)) x *
        (if x.1 = true ∧ x.2.check.disagreed = false then 1 else 0) =
      ∑' y, (logged (P 0)).run W s y *
        ((if y.1 = true then 1 else 0) * weight (P 1) j y.2.history) := by
  induction W using PFunctor.FreeM.induction generalizing s ps with
  | pure a =>
    rw [Prover.run_pure, Prover.run_pure,
      tsum_eq_single (a, (CompositeState.mk ⟨s.history.length, false⟩
        (Function.update ps 0 s.prover)))
        fun x hx => by simp [PMF.pure_apply, hx],
      tsum_eq_single (a, s) fun x hx => by simp [PMF.pure_apply, hx]]
    simp [PMF.pure_apply, weight_of_length_le _ hs]
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      Prover.run_bind, Prover.run_bind, Probability.PMF.tsum_bind_mul,
      Probability.PMF.tsum_bind_mul]
    cases q with
    | inl n =>
      have h1 := run_uniform_query (composite j P) n
        (CompositeState.mk ⟨s.history.length, false⟩ (Function.update ps 0 s.prover))
      have h2 := run_uniform_query (logged (P 0)) n s
      rw [h1, h2, Probability.PMF.tsum_map_mul, Probability.PMF.tsum_map_mul]
      exact tsum_congr fun b => congrArg _ (ih b ps hps s hs)
    | inr q =>
      have h2 := run_logged_query (P 0) q s
      have hcomp : (composite j P).run (OracleComp.query (Sum.inr q))
          (CompositeState.mk ⟨s.history.length, false⟩ (Function.update ps 0 s.prover)) =
          ((Prover.independent P).run (handler j q (CheckState.mk s.history.length false))
            (Function.update ps 0 s.prover)).map fun x => (x.1.1, CompositeState.mk x.1.2 x.2) := by
        exact Prover.run_query _ _ _
      rw [h2, hcomp, Probability.PMF.tsum_map_mul]
      by_cases hlt : s.history.length < j
      · rw [run_handler_of_ne P q _ (by simp only; omega),
          Probability.PMF.tsum_map_mul, Probability.PMF.tsum_map_mul]
        simp only [Function.update_self, Function.update_idem]
        refine tsum_congr fun x => congrArg _ ?_
        have := ih [x.1.headD false] ps hps
          (LoggedState.mk x.2 ((q.2, x.1.headD false) :: s.history))
          (by simp only [List.length_cons]; omega)
        simpa only [List.length_cons] using this
      · obtain rfl : s.history.length = j := by omega
        rw [run_handler_self P q (CheckState.mk s.history.length false)
          (Function.update ps 0 s.prover), Probability.PMF.tsum_bind_mul,
          Probability.PMF.tsum_map_mul]
        simp only [Function.update_self,
          Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), hps]
        refine tsum_congr fun x => congrArg _ ?_
        set b₀ := x.1.headD false
        set L := (logged (P 0)).run (cont [b₀]) (LoggedState.mk x.2 ((q.2, b₀) :: s.history))
        -- the composite continuation is the logged one with the disagreement flag fixed
        have hafter (y : List Bool × (P 1).State) :
            ∑' z, (composite s.history.length P).run (cont [b₀])
                ⟨⟨s.history.length + 1, false || y.1.headD false != b₀⟩,
                  Function.update (Function.update (Function.update ps 0 s.prover) 0 x.2) 1 y.2⟩ z *
              (if z.1 = true ∧ z.2.check.disagreed = false then 1 else 0) =
            (if (y.1.headD false != b₀) = false then 1 else 0) *
              ∑' z, L z * (if z.1 = true then 1 else 0) := by
          have h := run_composite_after s.history.length P (false || y.1.headD false != b₀)
            (Function.update (Function.update (Function.update ps 0 s.prover) 0 x.2) 1 y.2)
            (cont [b₀]) (LoggedState.mk x.2 ((q.2, b₀) :: s.history)) (by simp)
          have hupd : Function.update (Function.update (Function.update
              (Function.update ps 0 s.prover)
              0 x.2) 1 y.2) 0 x.2 =
              Function.update (Function.update (Function.update ps 0 s.prover) 0 x.2) 1 y.2 := by
            refine Function.update_eq_self_iff.mpr ?_
            rw [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Function.update_self]
          simp only [List.length_cons, hupd] at h
          rw [← h, Probability.PMF.tsum_map_mul, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          simp only [Bool.false_or]
          split_ifs <;> simp_all [L]
        rw [Probability.PMF.tsum_map_mul]
        simp only [hafter]
        -- the agreement probability of prover `1`
        have hagree : ∑' y, ((P 1).respond ((), q.2)).run (P 1).init y *
            (if (y.1.headD false != b₀) = false then 1 else 0) = answerProb (P 1) q.2 b₀ := by
          rw [answerProb, PMF.map_apply]
          refine tsum_congr fun y => ?_
          rw [mul_ite, mul_one, mul_zero]
          split_ifs with h₁ h₂ h₂
          · rfl
          · exact absurd (by cases hb : y.1.headD false <;> cases hc : b₀ <;> simp_all) h₂
          · exact absurd (by cases hb : y.1.headD false <;> cases hc : b₀ <;> simp_all) h₁
          · rfl
        -- the weight of every reachable final log is that agreement probability
        have hweight : ∀ z, L z * ((if z.1 = true then 1 else 0) *
              weight (P 1) s.history.length z.2.history) =
            answerProb (P 1) q.2 b₀ * (L z * (if z.1 = true then 1 else 0)) := by
          intro z
          by_cases hz : z ∈ L.support
          · obtain ⟨ext, hext⟩ := exists_log_eq_append (P 0) (cont [b₀]) _ z hz
            rw [hext, weight_append_cons]
            ring
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hz]
            simp
        simp only [hweight, ← mul_assoc, ENNReal.tsum_mul_right, hagree]
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun z => (mul_assoc _ _ _).symm

/-- The two answer bits of a prover have total probability one. -/
private theorem answerProb_add (P : Prover Unit) (q : List Bool) :
    answerProb P q true + answerProb P q false = 1 :=
  Probability.PMF.apply_true_add_apply_false
    (((P.respond ((), q)).run P.init).map fun x : List Bool × P.State => x.1.headD false)

/-- The most likely answer bit of prover `P` to `q`. -/
noncomputable def likely (P : Prover Unit) (q : List Bool) : Bool :=
  decide (answerProb P q false ≤ answerProb P q true)

private theorem answerProb_le_one (P : Prover Unit) (q : List Bool) (b : Bool)
    : answerProb P q b ≤ 1 :=
  PMF.coe_le_one _ _

/-- An answer other than the most likely one has probability at most one half. -/
private theorem answerProb_le_half (P : Prover Unit) {q : List Bool} {b : Bool}
    (hb : b ≠ likely P q) :
    answerProb P q b ≤ 1 / 2 := by
  have hsum := answerProb_add P q
  have hle : answerProb P q b ≤ answerProb P q (!b) := by
    unfold likely at hb
    by_cases h : answerProb P q false ≤ answerProb P q true
    · rw [decide_eq_true h] at hb
      obtain rfl : b = false := by simpa using hb
      exact h
    · rw [decide_eq_false h] at hb
      obtain rfl : b = true := by simpa using hb
      exact (not_le.mp h).le
  have h2 : 2 * answerProb P q b ≤ 1 := by
    calc 2 * answerProb P q b = answerProb P q b + answerProb P q b := two_mul _
      _ ≤ answerProb P q b + answerProb P q (!b) := add_le_add_right hle _
      _ = 1 := by cases b <;> simpa [add_comm] using hsum
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm]
  exact h2

private theorem weight_le_one (P : Prover Unit) (j : ℕ) (log : List (List Bool × Bool)) :
    weight P j log ≤ 1 := by
  unfold weight
  split
  · exact answerProb_le_one _ _ _
  · exact le_rfl

/-- **The averaged weight**: over the checked indices `j ≤ T`, the weights of a log with at most
`T` entries sum to at most `T + 1`, and to at most `T + 1 / 2` when some logged bit is not the most
likely answer. -/
private theorem sum_weight_le (P : Prover Unit) {T : ℕ} {log : List (List Bool × Bool)}
    (hlen : log.length ≤ T) :
    (∑ j : Fin (T + 1), weight P j log) +
        (if Consistent (likely P) log then 0 else 1 / 2) ≤ T + 1 := by
  split_ifs with hc
  · rw [add_zero]
    calc ∑ j : Fin (T + 1), weight P j log ≤ ∑ _j : Fin (T + 1), (1 : ENNReal) :=
          Finset.sum_le_sum fun j _ => weight_le_one P j log
      _ = T + 1 := by simp
  · obtain ⟨e, he, hbad⟩ : ∃ e ∈ log, e.2 ≠ likely P e.1 := by
      by_contra h
      push Not at h
      exact hc h
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem (List.mem_reverse.mpr he)
    have hiT : i < T + 1 := by simp at hi; omega
    have hwi : weight P i log ≤ 1 / 2 := by
      rw [weight, List.getElem?_eq_getElem hi, hie]
      exact answerProb_le_half P hbad
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i, hiT⟩ : Fin (T + 1)))]
    calc weight P (⟨i, hiT⟩ : Fin (T + 1)) log +
          ∑ j ∈ Finset.univ.erase (⟨i, hiT⟩ : Fin (T + 1)), weight P j log + 1 / 2
        ≤ 1 / 2 + ∑ _j ∈ Finset.univ.erase (⟨i, hiT⟩ : Fin (T + 1)), (1 : ENNReal) + 1 / 2 := by
          gcongr with j
          · exact weight_le_one P _ log
      _ = T + 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.add_sub_cancel, add_comm (1 / 2 : ENNReal),
            add_assoc, ENNReal.add_halves]

/-- **The checked run, through deferred sampling**: the probability that the checked run accepts
without a disagreement is the expected weight, at index `j`, of the final log of the logged prover
`0` on its accepting runs. -/
theorem acceptProb_checked (V : WordOracleComp Unit Bool) (j : ℕ) (P : Fin 2 → Prover Unit) :
    acceptProb (do let r ← checked V j; pure (r.1 && !r.2.disagreed)) (Prover.independent P) =
      ∑' y, (logged (P 0)).run V ⟨(P 0).init, []⟩ y *
        ((if y.1 = true then 1 else 0) * weight (P 1) j y.2.history) := by
  have h := tsum_composite_before j P (Prover.independent P).init rfl V ⟨(P 0).init, []⟩
    (by simp)
  have hupd : Function.update (Prover.independent P).init 0 (P 0).init =
      (Prover.independent P).init := Function.update_eq_self _ _
  simp only [List.length_nil, hupd] at h
  rw [← h, acceptProb, Prover.run_bind, run_checked]
  simp only [Prover.run_pure]
  erw [PMF.bind_pure_comp]
  simp only [PMF.map_comp, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases h1 : x.1 = true <;> by_cases h2 : x.2.check.disagreed = false <;> simp [h1, h2]

/-- **Soundness of the oracularized round**: if the proof verifier makes at most `T` queries and
accepts every proof with probability at most `1 / 2`, every pair of non-communicating provers is
accepted by the round with probability at most `1 - 1 / (4 (T + 1))`. -/
theorem acceptProb_round_le (V : WordOracleComp Unit Bool) (T : ℕ) (hT : V.IsQueryBounded T)
    (hs : ∀ π, acceptProb V (Prover.ofProof π) ≤ 1 / 2) (P : Fin 2 → Prover Unit) :
    acceptProb (round V T) (Prover.independent P) ≤
      ENNReal.ofReal (1 - 1 / (4 * ((T : ℝ) + 1))) := by
  set L := (logged (P 0)).run V ⟨(P 0).init, []⟩
  set ι : Bool × (logged (P 0)).State → ENNReal := fun y => if y.1 = true then 1 else 0
  set c : Bool × (logged (P 0)).State → ENNReal :=
    fun y => if Consistent (likely (P 1)) y.2.history then 0 else 1
  -- the round as an average over the checked index
  have hround : acceptProb (round V T) (Prover.independent P) =
      ((T : ENNReal) + 1)⁻¹ * ∑' y,
        L y * (ι y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history) := by
    rw [round, acceptProb_sample_bind]
    simp only [ProbComp.eval_unifFin, PMF.uniformOfFintype_apply, Fintype.card_fin,
      acceptProb_checked, Nat.cast_add, Nat.cast_one]
    rw [ENNReal.tsum_mul_left, tsum_comm]
    congr 1
    refine tsum_congr fun y => ?_
    rw [tsum_fintype, Finset.mul_sum, Finset.mul_sum]
  -- consistent and inconsistent accepting mass
  set a := ∑' y, L y * (ι y * (1 - c y))
  set b := ∑' y, L y * (ι y * c y)
  have ha : a ≤ 1 / 2 := by
    have h := tsum_logged_consistent_le (likely (P 1)) (P 0) V ⟨(P 0).init, []⟩
    have hnil : Consistent (likely (P 1)) ([] : List (List Bool × Bool)) := fun e he =>
      by simp at he
    rw [ite_eq_left hnil] at h
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) (h.trans (hs (likely (P 1))))
    congr 1
    simp only [ι, c]
    split_ifs <;> simp_all
  have hab : a + b ≤ 1 := by
    rw [← tsum_add]
    refine le_trans (tsum_le_tsum fun y => ?_) (le_of_eq (PMF.tsum_coe L))
    rw [← mul_add, ← mul_add]
    refine mul_le_of_le_one_right' ?_
    simp only [ι, c]
    split_ifs <;> simp
  have hS : ∑' y, L y * (ι y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history) + b * 2⁻¹ ≤
      ((T : ENNReal) + 1) * (a + b) := by
    have hpt (y : Bool × (logged (P 0)).State) :
        L y * (ι y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history) + L y * (ι y * c y) * 2⁻¹ ≤
          ((T : ENNReal) + 1) * (L y * (ι y * (1 - c y)) + L y * (ι y * c y)) := by
      by_cases hy : y ∈ L.support
      · have hlen := length_log_le (P 0) hT ⟨(P 0).init, []⟩ y hy
        have hw := sum_weight_le (P 1) (log := y.2.history) (by simpa using hlen)
        by_cases h1 : y.1 = true
        · by_cases h2 : Consistent (likely (P 1)) y.2.history
          · simp only [ι, c, ite_eq_left h1, ite_eq_left h2, add_zero] at hw ⊢
            simp only [one_mul, mul_zero, zero_mul, add_zero, tsub_zero, mul_one]
            calc L y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history ≤ L y * ((T : ENNReal) + 1) :=
                mul_le_mul' le_rfl hw
              _ = _ := mul_comm _ _
          · simp only [ι, c, ite_eq_left h1, ite_eq_right h2] at hw ⊢
            simp only [one_mul, mul_one, tsub_self, mul_zero, zero_add]
            calc L y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history + L y * 2⁻¹ =
                L y * (∑ j : Fin (T + 1), weight (P 1) j y.2.history + 1 / 2) := by
                  rw [mul_add, one_div]
              _ ≤ L y * ((T : ENNReal) + 1) := mul_le_mul' le_rfl hw
              _ = _ := mul_comm _ _
        · simp [ι, h1]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hy]
        simp
    calc ∑' y, L y * (ι y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history) + b * 2⁻¹
        = ∑' y, (L y * (ι y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history) +
            L y * (ι y * c y) * 2⁻¹) := by
          rw [tsum_add, ENNReal.tsum_mul_right]
      _ ≤ ∑' y, ((T : ENNReal) + 1) * (L y * (ι y * (1 - c y)) + L y * (ι y * c y)) :=
          tsum_le_tsum hpt
      _ = ((T : ENNReal) + 1) * (a + b) := by
          rw [ENNReal.tsum_mul_left, tsum_add]
  set S := ∑' y, L y * (ι y * ∑ j : Fin (T + 1), weight (P 1) j y.2.history)
  -- everything is finite; conclude over the reals
  have hT1 : ((T : ENNReal) + 1) ≠ ⊤ := by simp
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans hab)
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans hab)
  have hab' : a + b ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha', hb'⟩
  have hS' : S ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hT1 hab') (le_self_add.trans hS)
  have hTr : ((T : ENNReal) + 1).toReal = (T : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  have hSr : S.toReal + b.toReal / 2 ≤ ((T : ℝ) + 1) * (a.toReal + b.toReal) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hT1 hab') hS
    rw [ENNReal.toReal_add hS' (ENNReal.mul_ne_top hb' (by simp)), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_add ha' hb', ENNReal.toReal_inv, hTr] at this
    simpa [div_eq_mul_inv] using this
  have har : a.toReal ≤ 1 / 2 := by
    have := ENNReal.toReal_mono (by simp) ha
    simpa using this
  have habr : a.toReal + b.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hab
    rwa [ENNReal.toReal_add ha' hb', ENNReal.toReal_one] at this
  have ha0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  rw [hround, ENNReal.le_ofReal_iff_toReal_le (ENNReal.mul_ne_top (by simp) hS') (by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith), ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  rw [hTr, inv_mul_le_iff₀ hpos]
  have hT0 : (1 : ℝ) ≤ (T : ℝ) + 1 := by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  rw [mul_sub, mul_one, mul_one_div, div_mul_eq_div_div_swap, div_self hpos.ne']
  nlinarith

/-- **The repetition count suffices**: `8 (T + 1)` rounds of error `1 - 1 / (4 (T + 1))` have error
at most `1 / 3`. -/
private theorem pow_round_le (T : ℕ) :
    ENNReal.ofReal (1 - 1 / (4 * ((T : ℝ) + 1))) ^ (8 * (T + 1)) ≤ 1 / 3 := by
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hy : 1 / (4 * ((T : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  rw [← ENNReal.ofReal_pow (by linarith)]
  have hreal : (1 - 1 / (4 * ((T : ℝ) + 1))) ^ (8 * (T + 1)) ≤ 1 / 3 := by
    calc (1 - 1 / (4 * ((T : ℝ) + 1))) ^ (8 * (T + 1))
        ≤ Real.exp (-(1 / (4 * ((T : ℝ) + 1)))) ^ (8 * (T + 1)) :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _
      _ = Real.exp (-2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
          ring
      _ ≤ 1 / 3 := by
          rw [Real.exp_neg, one_div]
          refine inv_anti₀ (by norm_num) ?_
          have := Real.add_one_le_exp 2
          linarith
  calc ENNReal.ofReal ((1 - 1 / (4 * ((T : ℝ) + 1))) ^ (8 * (T + 1)))
      ≤ ENNReal.ofReal (1 / 3) := ENNReal.ofReal_le_ofReal hreal
    _ = 1 / 3 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
        norm_num

/-- **The oracularized round with a coin-sampled check index**: the index is the value of `m`
fair bits. -/
noncomputable def roundBits (V : WordOracleComp Unit Bool) (m : ℕ) :
    WordOracleComp (Fin 2) Bool := do
  let l ← ProbOracleComp.sample (BitString.sampleList m)
  let r ← checked V (ofBits l)
  pure (r.1 && !r.2.disagreed)

/-- The coin-sampled round accepts every prover family with the probability of the round with
`T = 2 ^ m - 1`. -/
theorem acceptProb_roundBits (V : WordOracleComp Unit Bool) (m : ℕ) (P : Prover (Fin 2)) :
    acceptProb (roundBits V m) P = acceptProb (round V (2 ^ m - 1)) P := by
  have hm : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel Nat.one_le_two_pow
  rw [roundBits, round, acceptProb_sample_bind, acceptProb_sample_bind, BitString.eval_sampleList,
    BitString.uniformList, ProbComp.eval_unifFin, Probability.PMF.tsum_map_mul]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    ofBits_ofFn, hm, ENNReal.tsum_mul_left]
  congr 1
  let e : (Fin m → Bool) ≃ Fin (2 ^ m - 1 + 1) := (BitString.equivFin m).trans (finCongr hm.symm)
  rw [tsum_fintype, tsum_fintype]
  exact Fintype.sum_equiv e _ _ fun x => rfl

/-- The handler reading only the first bit of every reply. -/
private noncomputable def handlerT (j : ℕ) (q : Unit × List Bool) (st : CheckState) :
    WordOracleComp (Fin 2) (List Bool × CheckState) := do
  let r₀ ← List.take 1 <$> ProbOracleComp.query ((0 : Fin 2), q.2)
  if decide (st.count = j) then do
    let r₁ ← List.take 1 <$> ProbOracleComp.query ((1 : Fin 2), q.2)
    pure ([r₀.headD false], ⟨st.count + 1, st.disagreed || (r₁.headD false != r₀.headD false)⟩)
  else pure ([r₀.headD false], ⟨st.count + 1, st.disagreed⟩)

private theorem headD_take_one (r : List Bool) : (List.take 1 r).headD false = r.headD false := by
  cases r <;> rfl

/-- The handler reads only the first bit of every reply. -/
private theorem handler_eq_handlerT : handler = handlerT := by
  funext j q st
  simp only [handler, handlerT, bind_map_left, headD_take_one]
  simp

private theorem checkedReply_polyTime :
    ComputableInPolyTime
      (fun y : List Bool × CheckState × List Bool =>
        ([y.1.headD false], CheckState.mk (y.2.1.count + 1)
          (y.2.1.disagreed || (y.2.2.headD false != y.1.headD false))))
      (encPair encBits (encPair encCheckState encBits)) (encPair encBits encCheckState) := by
  have singleton : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits :=
    ComputableInPolyTime.of_finite _
  have flag : ComputableInPolyTime (fun t : Bool × Bool × Bool => t.1 || (t.2.1 != t.2.2))
      (encPair encBool (encPair encBool encBool)) encBool := ComputableInPolyTime.of_finite _
  apply ComputableInPolyTime.prod
  · exact singleton.comp (by fun_prop)
  · apply encCheckState_mk_polyTime
    · fun_prop
    · exact flag.comp (g := fun y : List Bool × CheckState × List Bool =>
        (y.2.1.disagreed, y.2.2.headD false, y.1.headD false)) (by fun_prop)

/-- The truncated handler is strict oracle PPT, with the checked index given as a binary natural.
-/
private theorem isOraclePPTOn_handlerT :
    IsOraclePPTOn
      (encHandlerCall (encPair enc encNat) (encFinEnum Unit) encCheckState)
      (encPair encBits encCheckState)
      (fun x : (α × ℕ) × ((Unit × List Bool) × CheckState) =>
        handlerT x.1.2 x.2.1 x.2.2) := by
  -- the reply of prover `0`
  have h₀ : IsOraclePPTOn (encHandlerCall (encPair enc encNat) (encFinEnum Unit) encCheckState)
      encBits (fun x : (α × ℕ) × ((Unit × List Bool) × CheckState) =>
      List.take 1 <$> ProbOracleComp.query
        (spec := fun _ : Fin 2 × List Bool => List Bool) ((0 : Fin 2), x.2.1.2)) :=
    IsOraclePPTOn.query_take (0 : Fin 2) (by fun_prop) (by fun_prop)
  -- the checked branch: prover `1` is asked too
  have h₁ : IsOraclePPTOn
      (encPair (encHandlerCall (encPair enc encNat) (encFinEnum Unit) encCheckState)
        encBits) (encPair encBits encCheckState)
      (fun p : ((α × ℕ) × ((Unit × List Bool) × CheckState)) × List Bool => do
        let r₁ ← List.take 1 <$> ProbOracleComp.query
          (spec := fun _ : Fin 2 × List Bool => List Bool) ((1 : Fin 2), p.1.2.1.2)
        pure ([p.2.headD false], ⟨p.1.2.2.count + 1,
          p.1.2.2.disagreed || (r₁.headD false != p.2.headD false)⟩)) :=
    (IsOraclePPTOn.query_take (1 : Fin 2) (by fun_prop) (by fun_prop)).bind_with
      (ComputableInPolyTime.isOraclePPTOn (checkedReply_polyTime.comp
        (g := fun x : (((α × ℕ) × (Unit × List Bool) × CheckState) × List Bool) × List Bool =>
          (x.1.2, x.1.1.2.2, x.2)) (by fun_prop)))
  have h₂ : IsOraclePPTOn
      (encPair (encHandlerCall (encPair enc encNat) (encFinEnum Unit) encCheckState)
        encBits) (encPair encBits encCheckState)
      (fun p : ((α × ℕ) × ((Unit × List Bool) × CheckState)) × List Bool =>
        (pure ([p.2.headD false], ⟨p.1.2.2.count + 1, p.1.2.2.disagreed⟩) :
          WordOracleComp (Fin 2) (List Bool × CheckState))) :=
    ComputableInPolyTime.isOraclePPTOn (by fun_prop)
  have hc : ComputableInPolyTime
      (fun p : ((α × ℕ) × (Unit × List Bool) × CheckState) × List Bool =>
        decide (p.1.2.2.count = p.1.1.2))
      (encPair (encHandlerCall (encPair enc encNat) (encFinEnum Unit) encCheckState) encBits)
      encBool := ComputableInPolyTime.decide_eq' (encB := encNat) (by fun_prop) (by fun_prop)
  exact IsOraclePPTOn.bind_with
    (second := fun (x : (α × ℕ) × ((Unit × List Bool) × CheckState)) (r₀ : List Bool) =>
      if decide (x.2.2.count = x.1.2) = true then do
        let r₁ ← List.take 1 <$> ProbOracleComp.query
          (spec := fun _ : Fin 2 × List Bool => List Bool) ((1 : Fin 2), x.2.1.2)
        pure ([r₀.headD false], CheckState.mk (x.2.2.count + 1)
          (x.2.2.disagreed || (r₁.headD false != r₀.headD false)))
      else pure ([r₀.headD false], CheckState.mk (x.2.2.count + 1) x.2.2.disagreed))
        h₀ (IsOraclePPTOn.cond hc h₁ h₂)

/-- **The coin-sampled oracularized round is strict oracle PPT** when the proof verifier is and
the number of index bits is computed in polynomial time. -/
theorem isOraclePPTOn_roundBits {V : α → WordOracleComp Unit Bool}
    (hV : IsOraclePPTOn enc encBool V) {m : α → ℕ} (hm : ComputableInPolyTime m enc encUnary) :
    IsOraclePPTOn enc encBool (fun a => roundBits (V a) (m a)) := by
  -- the checked run, with the index given as a binary natural
  have hrun : IsOraclePPTOn (encPair enc encNat) (encPair encBool encCheckState)
      (fun caller : α × ℕ => checked (V caller.1) caller.2) := by
    simp only [checked, handler_eq_handlerT]
    refine IsOraclePPTOn.run_interpret_preprocess_open hV (prepare := Prod.fst)
      (initial := fun _ => (⟨0, false⟩ : CheckState)) (resources := fun _ _ => 4)
      (by fun_prop) isOraclePPTOn_handlerT (ComputableInPolyTime.const _) (fun _ _ => True)
      (fun _ => trivial) (ComputableInPolyTime.const _) ?_
    intro caller request st _ result hresult
    unfold handlerT at hresult
    simp only [Fin.isValue, decide_eq_true_eq, List.headD_eq_head?_getD,
      bind_pure_comp, Functor.map_map, bind_map_left, OracleComp.mem_supportWith_bind_iff,
      ProbOracleComp.supportWith_query, Set.mem_univ, true_and] at hresult
    obtain ⟨r, hr⟩ := hresult
    have key : ∃ x b, result = ([x], ⟨st.count + 1, b⟩) := by
      split_ifs at hr
      · obtain ⟨r₁, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hr
        exact ⟨_, _, rfl⟩
      · exact ⟨_, _, by simpa using hr⟩
    obtain ⟨x, b, rfl⟩ := key
    refine ⟨trivial, by simp, ?_⟩
    simp only [encCheckState_apply, encCheckStateFields, length_encPair, encNat_apply]
    have h2 : (st.count + 1).size ≤ st.count.size + 2 := by
      have := Nat.size_add_le st.count 1
      simpa using this
    rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len] at h2
    have h3 : (encBool b).length = (encBool st.disagreed).length := by
      cases b <;> cases st.disagreed <;> rfl
    omega
  have hsample : IsOraclePPTOn (Operation := Fin 2) enc encBits
      (fun a => ProbOracleComp.sample (BitString.sampleList (m a))) :=
    IsPPTOn.isOraclePPTOn (IsPPTOn.preprocess isPPTOn_sampleList hm)
  have hcont : IsOraclePPTOn (encPair enc encBits) encBool
      (fun p : α × List Bool => (fun r : Bool × CheckState => r.1 && !r.2.disagreed) <$>
        checked (V p.1) (ofBits p.2)) :=
    (IsOraclePPTOn.preprocess hrun (prepare := fun p : α × List Bool => (p.1, ofBits p.2))
      (by fun_prop)).map (by fun_prop)
  unfold roundBits
  exact IsOraclePPTOn.bind_with hsample (by simpa only [bind_pure_comp] using hcont)

end Oracularize

/-- **`PCPPoly ⊆ MIP₂`**: the oracularized round, which checks one random query of the proof
verifier against the second prover, repeated sequentially `16 (T + 1)` times for a polynomial
bound `T` on the verifier's queries. This is the oracle-to-two-prover direction of
[Babai, Fortnow and Lund, §2, combined proof of Theorems 2.3–2.4, step 1][BabaiFortnowLund1991]. -/
theorem PCPPoly_subset_MIP₂ : PCPPoly enc ⊆ MIP₂ enc := by
  rintro A ⟨V, hV, hc, hs⟩
  obtain ⟨c, d, hq⟩ := IsOraclePPTOn.query_bounds hV
  set T₀ : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  set m : α → ℕ := fun a => Nat.clog 2 (T₀ a + 1)
  have hm : ComputableInPolyTime m enc encUnary := by
    simp only [m, T₀]
    fun_prop
  have hk : ComputableInPolyTime (fun a => 16 * (T₀ a + 1)) enc encUnary := by
    simp only [T₀]
    fun_prop
  -- `2 ^ m` is at least `T₀ + 1` and at most twice that
  have hpow (a : α) : T₀ a + 1 ≤ 2 ^ m a := Nat.le_pow_clog one_lt_two _
  have hpow' (a : α) : 8 * (2 ^ m a - 1 + 1) ≤ 16 * (T₀ a + 1) := by
    rw [Nat.sub_add_cancel Nat.one_le_two_pow]
    have h : 2 ^ m a ≤ 2 * (T₀ a + 1) := Nat.pow_clog_le_mul one_lt_two (by omega)
    omega
  refine ⟨fun a => sequentialRepeat (16 * (T₀ a + 1)) (Oracularize.roundBits (V a) (m a)),
    IsOraclePPTOn.sequentialRepeat_count (Oracularize.isOraclePPTOn_roundBits hV hm) hk,
    ⟨fun a ha => ?_, fun a ha P => ?_⟩⟩
  · obtain ⟨π, hπ⟩ := hc a ha
    refine ⟨fun _ => Prover.ofProof π, ?_⟩
    have h := le_acceptProb_sequentialRepeat (c := 1)
      (round := Oracularize.roundBits (V a) (m a))
      (Prover.independent fun _ : Fin 2 => Prover.ofProof π) (fun s => by
        have hs : s = (Prover.independent fun _ : Fin 2 => Prover.ofProof π).init := rfl
        subst hs
        rw [show ({ Prover.independent fun _ : Fin 2 => Prover.ofProof π with
          init := (Prover.independent fun _ : Fin 2 => Prover.ofProof π).init } : Prover (Fin 2)) =
          Prover.independent fun _ : Fin 2 => Prover.ofProof π from rfl,
          Oracularize.acceptProb_roundBits, Oracularize.acceptProb_round_honest, hπ])
      (16 * (T₀ a + 1))
    rw [one_pow] at h
    refine le_trans ?_ h
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num), one_mul]
    norm_num
  · have hround (P : Fin 2 → Prover Unit) :=
      (Oracularize.acceptProb_roundBits (V a) (m a) (Prover.independent P)).trans_le
        (Oracularize.acceptProb_round_le (V a) (2 ^ m a - 1)
          ((hq a).1.mono (by
            have := hpow a
            have hT : T₀ a = c * ((enc a).length + 1) ^ d := rfl
            omega)) (hs a ha) P)
    refine (acceptProb_sequentialRepeat_independent_le hround _ P).trans ?_
    refine le_trans (pow_le_pow_right_of_le_one' ?_ (hpow' a)) (Oracularize.pow_round_le _)
    exact ENNReal.ofReal_le_one.mpr (by
      have : (0 : ℝ) ≤ 1 / (4 * (((2 ^ m a - 1 : ℕ) : ℝ) + 1)) := by positivity
      linarith)

end Cslib.Complexity
