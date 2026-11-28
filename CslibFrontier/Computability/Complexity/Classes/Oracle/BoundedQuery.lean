/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BooleanHierarchy
public import CslibFrontier.Computability.Complexity.Classes.Oracle.QueryBit
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Languages.Probabilistic.Iteration
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Bounded-query oracle classes and `P^{NP[O(log n)]}`

`f` is computable in polynomial time relative to `A` with `r` requests
(`Cslib.Complexity.ComputableInPolyTimeWithOracleQueries`) when it has the certificate of
`Cslib.Complexity.ComputableInPolyTimeWithOracle` and the program, run against the oracle
language `A`, makes at most `r n` requests on instances of encoded length `n`
(`Cslib.OracleComp.queriesWith`). The requests are counted against `A` itself, as in the usual
definition of a machine with oracle `A` making a bounded number of queries; the certificate's
clock bounds the requests against every oracle in any case
(`Cslib.Probability.IsOraclePPTOn.query_bounds`).

`P^{NP[O(log n)]}` (`Cslib.Complexity.PNPLog`) is the class of problems decided in polynomial time
with at most `c log₂ n + c` requests to some oracle language in `NP`, for a constant `c`
[Hemaspaandra and Ogihara, p. 1][HemaspaandraOgihara2002] [Kadin][Kadin1989]. It contains
`NP` and `coNP` with one request to the encodings of the satisfiable formulas
(`Cslib.Complexity.NP_subset_PWithOracleQueries_image_SAT`), through the Cook–Levin reduction, and
is closed under complement. Running two deciders in sequence adds their requests
(`Cslib.Complexity.inter_mem_PWithOracleQueries`), so the `n`th level of the Boolean hierarchy is
decided with `n` requests to `SAT` and the whole Boolean hierarchy lies in `P^{NP[O(log n)]}`
[Köbler, Schöning and Wagner][KoeblerSchoeningWagner1987]; in particular `DP` and `coDP`
(`Cslib.Complexity.BH_two`, `Cslib.Complexity.coBH_two`) are decided with two requests.

## Main definitions

* `Cslib.Complexity.ComputableInPolyTimeWithOracleQueries`: polynomial time relative to an oracle
  with a bounded number of requests.
* `Cslib.Complexity.PWithOracleQueries`: the problems so decided.
* `Cslib.Complexity.PNPLog`: `P^{NP[O(log n)]}`.

## Main results

* `Cslib.OracleComp.length_queriesWith_iterate_le`: a bounded loop of rounds with boundedly many
  requests makes boundedly many requests.
* `Cslib.Complexity.ComputableInPolyTimeWithOracleQueries.computableInPolyTimeWithOracle`,
  `.mono`, `.map`, `.prod`: forgetting and weakening the bound, postprocessing, and sequential
  composition.
* `Turing.MultiTapeTM.ComputableInPolyTime.computableInPolyTimeWithOracleQueries`: polynomial time
  makes no request.
* `Cslib.Complexity.computableInPolyTimeWithOracleQueries_query`: one request
  (`Cslib.Complexity.queryBit`) decides membership of a polynomial-time request word.
* `Cslib.Complexity.compl_mem_PWithOracleQueries`, `Cslib.Complexity.compl_mem_PNPLog`: closure
  under complement.
* `Cslib.Complexity.inter_mem_PWithOracleQueries`: closure under intersection, adding the bounds.
* `Cslib.Complexity.NP_subset_PWithOracleQueries_image_SAT`: one request to `SAT` decides a
  problem in `NP`.
* `Cslib.Complexity.BH_subset_PWithOracleQueries_image_SAT`: `n` requests to `SAT` decide a
  problem in the `n`th level of the Boolean hierarchy.
* `Cslib.Complexity.P_subset_PNPLog`, `Cslib.Complexity.NP_subset_PNPLog`,
  `Cslib.Complexity.coNP_subset_PNPLog`, `Cslib.Complexity.BooleanHierarchy_subset_PNPLog`,
  `Cslib.Complexity.PNPLog_subset_PWithOracle`.

## References

* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
* [J. Kadin, *P^{NP[O(log n)]} and sparse Turing-complete sets for NP*][Kadin1989]
* [J. Köbler, U. Schöning, K. W. Wagner, *The difference and truth-table hierarchies for
  NP*][KoeblerSchoeningWagner1987]
-/

@[expose] public section

namespace Cslib

/-- **A bounded loop makes a bounded number of requests**: if every round makes at most `r`
requests, `n` rounds make at most `n * r`. -/
theorem OracleComp.length_queriesWith_iterate_le {ι State : Type} {spec : OracleSpec.{0, 0} ι}
    (answer : (q : ι) → spec q) {step : State → OracleComp spec State} {r : ℕ}
    (h : ∀ st, (queriesWith answer (step st)).length ≤ r) (n : ℕ) (st : State) :
    (queriesWith answer (iterate n step st)).length ≤ n * r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ, queriesWith_bind, List.length_append, Nat.succ_mul]
    exact Nat.add_le_add ih (h _)

namespace Complexity

open Probability Turing.MultiTapeTM Cslib.Logic.PL

variable {α β γ : Type}

/-- `f` is computable in polynomial time relative to the oracle language `A` with at most `r n`
requests on instances of encoded length `n`: one deterministic word-query program has the
certificate of `ComputableInPolyTimeWithOracle`, computes `f` against `A`, and makes at most
`r (input a).length` requests on `a` against `A`. -/
def ComputableInPolyTimeWithOracleQueries (A : Set (List Bool)) (r : ℕ → ℕ) (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOraclePPTOn input output (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle A) (program a) = f a ∧
        (OracleComp.queriesWith (languageOracle A) (program a)).length ≤ r (input a).length

namespace ComputableInPolyTimeWithOracleQueries

variable {A : Set (List Bool)} {r r' : ℕ → ℕ} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool}

/-- A bounded number of requests is in particular polynomial time relative to the oracle. -/
theorem computableInPolyTimeWithOracle {f : α → β}
    (h : ComputableInPolyTimeWithOracleQueries A r f input middle) :
    ComputableInPolyTimeWithOracle A f input middle :=
  let ⟨program, hprogram, heq⟩ := h
  ⟨program, hprogram, fun a => (heq a).1⟩

/-- Weakening the bound on the requests. -/
theorem mono {f : α → β} (h : ComputableInPolyTimeWithOracleQueries A r f input middle)
    (hr : ∀ n, r n ≤ r' n) : ComputableInPolyTimeWithOracleQueries A r' f input middle :=
  let ⟨program, hprogram, heq⟩ := h
  ⟨program, hprogram, fun a => ⟨(heq a).1, (heq a).2.trans (hr _)⟩⟩

/-- Polynomial-time postprocessing of the result makes no further request. -/
theorem map {f : α → β} {g : β → γ} (h : ComputableInPolyTimeWithOracleQueries A r f input middle)
    (hg : ComputableInPolyTime g middle output) :
    ComputableInPolyTimeWithOracleQueries A r (fun a => g (f a)) input output := by
  obtain ⟨program, hprogram, heq⟩ := h
  refine ⟨fun a => g <$> program a, ?_, fun a => ⟨?_, ?_⟩⟩
  · simpa only [OracleComp.interpret_map] using hprogram.map hg
  · rw [OracleComp.interpret_map, (heq a).1]
    rfl
  · rw [OracleComp.queriesWith_map]
    exact (heq a).2

/-- **Sequential composition**: running two programs against the same oracle one after the other,
retaining both results, makes the requests of both. -/
theorem prod {f : α → β} {g : α → γ} (hf : ComputableInPolyTimeWithOracleQueries A r f input middle)
    (hg : ComputableInPolyTimeWithOracleQueries A r' g input output) :
    ComputableInPolyTimeWithOracleQueries A (fun n => r n + r' n) (fun a => (f a, g a)) input
      (encPair middle output) := by
  obtain ⟨first, hfirst, hfirst_eq⟩ := hf
  obtain ⟨second, hsecond, hsecond_eq⟩ := hg
  refine ⟨fun a => do
    let b ← first a
    (fun c => (b, c)) <$> second a, ?_, fun a => ⟨?_, ?_⟩⟩
  · simp only [OracleComp.interpret_bind, OracleComp.interpret_map]
    exact hfirst.bind_with ((hsecond.preprocess
      (ComputableInPolyTime.fst input middle)).map_with
      (((ComputableInPolyTime.snd input middle).comp (.fst _ _)).prod (.snd _ _)))
  · simp only [OracleComp.interpret_bind, OracleComp.interpret_map, (hfirst_eq a).1,
      (hsecond_eq a).1]
    rfl
  · rw [OracleComp.queriesWith_bind, List.length_append, OracleComp.queriesWith_map]
    exact Nat.add_le_add (hfirst_eq a).2 (hsecond_eq a).2

end ComputableInPolyTimeWithOracleQueries

/-- A polynomial-time computation makes no request. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.computableInPolyTimeWithOracleQueries
    {f : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : ComputableInPolyTime f input output) (A : Set (List Bool)) (r : ℕ → ℕ) :
    ComputableInPolyTimeWithOracleQueries A r f input output :=
  ⟨fun a => pure (f a), h.isOraclePPTOn, fun _ => ⟨rfl, by simp⟩⟩

open Classical in
/-- **One request** to `A` for the polynomial-time word `req a` decides whether `req a ∈ A`. -/
theorem computableInPolyTimeWithOracleQueries_query {req : α → List Bool}
    {input : α ↪ List Bool} (hreq : ComputableInPolyTime req input encBits)
    (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracleQueries A (fun _ => 1) (fun a => decide (req a ∈ A)) input
      encBool :=
  ⟨fun a => queryBit (req a), isOraclePPTOn_queryBit hreq,
    fun a => ⟨interpret_queryBit A (req a), by simp⟩⟩

/-- The problems decided in polynomial time relative to the oracle language `A` with at most
`r n` requests on instances of encoded length `n`. -/
def PWithOracleQueries (A : Set (List Bool)) (r : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f : α → Bool, ComputableInPolyTimeWithOracleQueries A r f enc encBool ∧
    ∀ a, a ∈ L ↔ f a = true}

theorem mem_PWithOracleQueries {A : Set (List Bool)} {r : ℕ → ℕ} {enc : α ↪ List Bool}
    {L : Set α} :
    L ∈ PWithOracleQueries A r enc ↔ ∃ f : α → Bool,
      ComputableInPolyTimeWithOracleQueries A r f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  Iff.rfl

/-- **`P^{NP[O(log n)]}`**: the problems decided in polynomial time with at most `c log₂ n + c`
requests, on instances of encoded length `n`, to some oracle language in `NP`
[Hemaspaandra and Ogihara, p. 1][HemaspaandraOgihara2002] [Kadin][Kadin1989]. -/
def PNPLog (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NP encBits, ⋃ c : ℕ, PWithOracleQueries A (fun n => c * Nat.log 2 n + c) enc

theorem mem_PNPLog {enc : α ↪ List Bool} {L : Set α} :
    L ∈ PNPLog enc ↔ ∃ A ∈ NP encBits, ∃ c : ℕ,
      L ∈ PWithOracleQueries A (fun n => c * Nat.log 2 n + c) enc := by
  simp only [PNPLog, Set.mem_iUnion, exists_prop]

section

variable {A : Set (List Bool)} {r r' : ℕ → ℕ} {enc : α ↪ List Bool} {L : Set α}

theorem PWithOracleQueries_subset_PWithOracle :
    PWithOracleQueries A r enc ⊆ PWithOracle A enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.computableInPolyTimeWithOracle, hL⟩

theorem PWithOracleQueries_mono (hr : ∀ n, r n ≤ r' n) :
    PWithOracleQueries A r enc ⊆ PWithOracleQueries A r' enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.mono hr, hL⟩

/-- A problem in `P` is decided with no request. -/
theorem P_subset_PWithOracleQueries (A : Set (List Bool)) (r : ℕ → ℕ) (enc : α ↪ List Bool) :
    P enc ⊆ PWithOracleQueries A r enc := fun _ ⟨f, hf, hL⟩ =>
  ⟨f, hf.computableInPolyTimeWithOracleQueries A r, hL⟩

/-- **Closure under complement**: negate the decider, with the same requests. -/
theorem compl_mem_PWithOracleQueries (hL : L ∈ PWithOracleQueries A r enc) :
    Lᶜ ∈ PWithOracleQueries A r enc := by
  obtain ⟨f, hf, hL⟩ := hL
  refine ⟨fun a => !f a, hf.map (by fun_prop), fun a => ?_⟩
  rw [Set.mem_compl_iff, hL a]
  simp

/-- **Closure under intersection**: run both deciders, adding their requests. -/
theorem inter_mem_PWithOracleQueries {L' : Set α} (hL : L ∈ PWithOracleQueries A r enc)
    (hL' : L' ∈ PWithOracleQueries A r' enc) :
    L ∩ L' ∈ PWithOracleQueries A (fun n => r n + r' n) enc := by
  obtain ⟨f, hf, hL⟩ := hL
  obtain ⟨g, hg, hL'⟩ := hL'
  exact ⟨fun a => f a && g a, (hf.prod hg).map (g := fun p => p.1 && p.2) (by fun_prop),
    fun a => by simp [hL a, hL' a]⟩

open Classical in
/-- A problem that reduces in polynomial time to the oracle language is decided with one
request. -/
theorem mem_PWithOracleQueries_of_reduction {req : α → List Bool}
    (hreq : ComputableInPolyTime req enc encBits) (h : ∀ a, a ∈ L ↔ req a ∈ A) :
    L ∈ PWithOracleQueries A (fun _ => 1) enc :=
  ⟨_, computableInPolyTimeWithOracleQueries_query hreq A, fun a => by
    rw [h a, decide_eq_true_iff]⟩

/-- **One request to `SAT` decides a problem in `NP`**: the request is the encoding of the
Cook–Levin reduction of the instance. -/
theorem NP_subset_PWithOracleQueries_image_SAT (enc : α ↪ List Bool) :
    NP enc ⊆ PWithOracleQueries (encCNF '' SAT) (fun _ => 1) enc := by
  intro L hL
  obtain ⟨f, hf, hfL⟩ := CookLevin.SAT_npHard enc L hL
  have henc : ComputableInPolyTime (fun φ : CNF ℕ => encCNF φ) encCNF encBits :=
    .of_eq fun _ => rfl
  refine mem_PWithOracleQueries_of_reduction (req := fun a => encCNF (f a)) (henc.comp hf)
    fun a => ?_
  rw [hfL a]
  exact ⟨fun h => ⟨f a, h, rfl⟩, fun ⟨_, h, he⟩ => encCNF.injective he ▸ h⟩

/-- A problem decided with `c log₂ n + c` requests to an oracle language in `NP` is in
`P^{NP[O(log n)]}`. -/
theorem mem_PNPLog_of_mem_PWithOracleQueries (hA : A ∈ NP encBits) {c : ℕ}
    (hL : L ∈ PWithOracleQueries A (fun n => c * Nat.log 2 n + c) enc) : L ∈ PNPLog enc :=
  mem_PNPLog.mpr ⟨A, hA, c, hL⟩

/-- **`P^{NP[O(log n)]}` is closed under complement.** -/
theorem compl_mem_PNPLog (hL : L ∈ PNPLog enc) : Lᶜ ∈ PNPLog enc := by
  obtain ⟨A, hA, c, hL⟩ := mem_PNPLog.mp hL
  exact mem_PNPLog_of_mem_PWithOracleQueries hA (compl_mem_PWithOracleQueries hL)

/-- `P ⊆ P^{NP[O(log n)]}`. -/
theorem P_subset_PNPLog (enc : α ↪ List Bool) : P enc ⊆ PNPLog enc := fun _ hL =>
  mem_PNPLog_of_mem_PWithOracleQueries image_SAT_mem_NP
    (P_subset_PWithOracleQueries _ (fun n => 0 * Nat.log 2 n + 0) enc hL)

/-- **`NP ⊆ P^{NP[O(log n)]}`**, with one request to `SAT`. -/
theorem NP_subset_PNPLog (enc : α ↪ List Bool) : NP enc ⊆ PNPLog enc := fun _ hL =>
  mem_PNPLog_of_mem_PWithOracleQueries (c := 1) image_SAT_mem_NP
    (PWithOracleQueries_mono (fun n => by omega) (NP_subset_PWithOracleQueries_image_SAT enc hL))

/-- **`coNP ⊆ P^{NP[O(log n)]}`**. -/
theorem coNP_subset_PNPLog (enc : α ↪ List Bool) : coNP enc ⊆ PNPLog enc := fun _ hL => by
  simpa only [compl_compl] using compl_mem_PNPLog (NP_subset_PNPLog enc hL)

/-- **A level of the Boolean hierarchy needs a constant number of requests**: a problem in
`BH enc n` is decided with `n` requests to `SAT`, one for each `NP` language of its nested
difference; by `compl_mem_PWithOracleQueries`, so is a problem in `coBH enc n`.
[Köbler, Schöning and Wagner, Corollary 4.6 (i)][KoeblerSchoeningWagner1987] prove the stronger
nonadaptive form: the `n`th level (their `DIFF_n`) and its complements are `n`-truth-table
reducible to `NP`. `PWithOracleQueries` counts requests that may depend on earlier answers. -/
theorem BH_subset_PWithOracleQueries_image_SAT (enc : α ↪ List Bool) (n : ℕ) :
    BH enc n ⊆ PWithOracleQueries (encCNF '' SAT) (fun _ => n) enc := by
  induction n with
  | zero =>
    rintro L rfl
    exact P_subset_PWithOracleQueries _ _ enc empty_mem_P
  | succ n ih =>
    rintro _ ⟨B, hB, D, hD, rfl⟩
    exact PWithOracleQueries_mono (fun _ => by omega) (inter_mem_PWithOracleQueries
      (NP_subset_PWithOracleQueries_image_SAT enc hB) (compl_mem_PWithOracleQueries (ih hD)))

/-- **`BooleanHierarchy ⊆ P^{NP[O(log n)]}`**: a problem in the `n`th level is decided with `n`
requests to `SAT`, a constant number. The Boolean hierarchy is in fact the class of problems
bounded-truth-table reducible to `NP` [Köbler, Schöning and Wagner, Corollaries 3.9 (iii) and
4.6 (ii)][KoeblerSchoeningWagner1987]. -/
theorem BooleanHierarchy_subset_PNPLog (enc : α ↪ List Bool) :
    BooleanHierarchy enc ⊆ PNPLog enc :=
  Set.iUnion_subset fun n _ hL => mem_PNPLog_of_mem_PWithOracleQueries (c := n) image_SAT_mem_NP
    (PWithOracleQueries_mono (fun _ => by omega) (BH_subset_PWithOracleQueries_image_SAT enc n hL))

/-- `P^{NP[O(log n)]} ⊆ P^{NP}`. -/
theorem PNPLog_subset_PWithOracle (enc : α ↪ List Bool) :
    PNPLog enc ⊆ ⋃ A ∈ NP encBits, PWithOracle A enc := by
  intro L hL
  obtain ⟨A, hA, c, hL⟩ := mem_PNPLog.mp hL
  exact Set.mem_biUnion hA (PWithOracleQueries_subset_PWithOracle hL)

end

end Complexity

end Cslib
