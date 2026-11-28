/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian.Soundness
public import CslibFrontier.Crypto.Computational.Kilian.Succinct
public import CslibFrontier.Computability.Complexity.Classes.NP.Relation
import CslibFrontier.Computability.PCP.Completeness

/-!
# Kilian's arguments for NP

With the PCP theorem and its witness compiler (`exists_pcpVerifier_of_npRelation`), every NP
relation `R : NPRelation enc` has a polynomial-time PCP verifier `V` with `O(log n)` random bits
and constantly many queries together with a polynomial-time compiler `compile` sending every
relation witness `(x, w)` to an accepted compact PCP table `V.tableVerifier (x, compile (x, w))`
(`exists_kilianArgument_of_npRelation`):

* `compile` itself and the composed honest prover maps
  `(key, (x, w)) ↦ kilianCommit H V key x (compile (x, w))` and
  `((key, (x, w)), ρs) ↦ kilianRespond H V key x (compile (x, w)) ρs` run in polynomial time
  (`computableInPolyTime_kilianCommit`, `computableInPolyTime_kilianRespond`), giving a uniform
  polynomial-time honest prover on arbitrary NP relations ([BarakGoldreich2001],
  Definition 3.2);
* on every witness `R.IsWitness x w`, `kilianHonestGame` accepts `compile (x, w)` with
  probability one (`eval_kilianHonestGame`);
* the protocol is computationally sound (`HashFamily.kilianSound`);
* the honest transcript after the statement has `O(n² · (log₂ |enc x| + 1))` payload bits at
  security parameter `n` (`kilianCommunication_honest_le_log`);
* a single binary multi-tape Turing machine computes `kilianVerify` on every `KilianView α` in
  polynomial time and space in its received input, and in time and space polynomial in
  `n + |enc x|` on every honest transcript (`computableInTimeAndSpace_kilianVerify_honest_le`).
  The verifier does not truncate oversized raw tapes from malformed provers before decoding.

`exists_kilianSound_of_mem_NP` states the corresponding language-level consequence for every
`L ∈ NP enc`.

## Main results

* `Cslib.Crypto.exists_kilianArgument_of_npRelation`: Kilian's succinct interactive argument for
  arbitrary NP relations, including polynomial-time witness compilation and honest verifier
  runtime accounting.
* `Cslib.Crypto.exists_kilianSound_of_mem_NP`: every language in NP has a Kilian argument.

## References

* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001]
-/

public section

namespace Cslib.Crypto

open Complexity Turing.MultiTapeTM

variable {α : Type} {H : List Bool → List Bool → List Bool}

/-- **Kilian's interactive arguments for arbitrary NP relations**: for a collision-resistant
`HashFamily H` and any NP relation `R : NPRelation enc`, there exist a polynomial-time PCP
verifier `V` with `O(log n)` random bits and constantly many queries `d` and a polynomial-time
witness compiler `compile : α × List Bool → List Bool` such that the composed honest commitment
and opening maps on `(key, x, w)` run in polynomial time, `compile` produces tables accepted by
`V.tableVerifier` with perfect completeness on `R.IsWitness x w`, the protocol is computationally
sound (`KilianSound H V enc R.language`), honest transcripts use `O(n² · (log₂ |enc x| + 1))`
payload bits, and a fixed binary machine computes `kilianVerify` in time and space polynomial in
`n + |enc x|` on every honest transcript. -/
theorem exists_kilianArgument_of_npRelation (hH : HashFamily H) {enc : α ↪ List Bool}
    (R : NPRelation enc) :
    ∃ (V : PCPVerifier α) (compile : α × List Bool → List Bool) (c d : ℕ),
      V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d) ∧
      ComputableInPolyTime compile (encPair enc encBits) encBits ∧
      ComputableInPolyTime
        (fun p : List Bool × α × List Bool =>
          let (key, state) := p
          let (x, w) := state
          kilianCommit H V key x (compile (x, w)))
        (encPair encBits (encPair enc encBits)) encBits ∧
      ComputableInPolyTime
        (fun p : (List Bool × α × List Bool) × List (List Bool) =>
          let (proverIn, ρs) := p
          let (key, state) := proverIn
          let (x, w) := state
          kilianRespond H V key x (compile (x, w)) ρs)
        (encPair (encPair encBits (encPair enc encBits)) (encList encBits))
        encKilianResponse ∧
      (∀ x, x ∈ R.language ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x w, R.IsWitness x w → V.tableVerifier (x, compile (x, w)) = true) ∧
      (∀ x w, R.IsWitness x w →
        ∀ n, ProbComp.eval (kilianHonestGame H V x (compile (x, w)) n) = PMF.pure true) ∧
      KilianSound H V enc R.language ∧
      (∃ C : ℕ, ∀ (n : ℕ) (k : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)),
        k.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins x) →
          kilianCommunication k (kilianCommit H V k x table) ρs
            (kilianRespond H V k x table ρs) ≤
          C * (n + 1) ^ 2 * (Nat.log 2 (enc x).length + 1)) ∧
      (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
        (t s tHonest sHonest : ℕ → ℕ),
        PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
        PolynomiallyBounded tHonest ∧ PolynomiallyBounded sHonest ∧
        tm.ComputesFunInTimeAndSpace (encKilianView enc) encBool
          (fun v => kilianVerify H V v.key v.stmt v.root v.challenges v.response)
          (fun v => t (encKilianView enc v).length)
          (fun v => s (encKilianView enc v).length) ∧
        (∀ (n : ℕ) (key : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)),
          key.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins x) →
            let view : KilianView α :=
              { key := key, stmt := x, root := kilianCommit H V key x table,
                challenges := ρs, response := kilianRespond H V key x table ρs }
            t (encKilianView enc view).length ≤ tHonest (n + (enc x).length) ∧
            s (encKilianView enc view).length ≤ sHonest (n + (enc x).length) ∧
            tm.ComputesInTimeAndSpace (encKilianView enc view)
              (encBool (kilianVerify H V key x view.root ρs view.response))
              (tHonest (n + (enc x).length)) (sHonest (n + (enc x).length)))) := by
  obtain ⟨V, compile, c, d, hV, hpcp, hcompile, hacc⟩ := exists_pcpVerifier_of_npRelation enc R
  have hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d := fun x ρ hρ => by
    simpa using hpcp.length_queries_le x ρ hρ
  have hk : ComputableInPolyTime (fun p : List Bool × α × List Bool => p.1)
      (encPair encBits (encPair enc encBits)) encBits := ComputableInPolyTime.fst _ _
  have hsnd : ComputableInPolyTime (fun p : List Bool × α × List Bool => p.2)
      (encPair encBits (encPair enc encBits)) (encPair enc encBits) :=
    ComputableInPolyTime.snd _ _
  have hx : ComputableInPolyTime (fun p : List Bool × α × List Bool => p.2.1)
      (encPair encBits (encPair enc encBits)) enc := (ComputableInPolyTime.fst _ _).comp hsnd
  have hin : ComputableInPolyTime
      (fun p : List Bool × α × List Bool =>
        ({ key := p.1, stmt := p.2.1, table := compile p.2 } : KilianProverInput α))
      (encPair encBits (encPair enc encBits)) (encKilianProverInput enc) :=
    encKilianProverInput_mk_polyTime enc hk hx (hcompile.comp hsnd)
  have hcommit : ComputableInPolyTime
      (fun p : List Bool × α × List Bool =>
        let (key, state) := p
        let (x, w) := state
        kilianCommit H V key x (compile (x, w)))
      (encPair encBits (encPair enc encBits)) encBits := by
    simpa only [Function.comp_def] using
      (computableInPolyTime_kilianCommit hH.polyTime hH.length_eq hV hpcp.coins_le).comp hin
  have hrespond : ComputableInPolyTime
      (fun p : (List Bool × α × List Bool) × List (List Bool) =>
        let (proverIn, ρs) := p
        let (key, state) := proverIn
        let (x, w) := state
        kilianRespond H V key x (compile (x, w)) ρs)
      (encPair (encPair encBits (encPair enc encBits)) (encList encBits))
      encKilianResponse := by
    simpa only [Function.comp_def] using
      (computableInPolyTime_kilianRespond hH.polyTime hH.length_eq hV hpcp.coins_le).comp
        ((hin.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  refine ⟨V, compile, c, d, hV, hpcp.coins_le, hq, hcompile, hcommit, hrespond,
    hpcp.mem_iff_exists_tableVerifier, hacc,
    fun x w hw n => eval_kilianHonestGame H V hH.length_eq (hacc x w hw) n,
    hH.kilianSound hV hpcp,
    ⟨_, fun n k x table ρs hk hn hρs =>
      kilianCommunication_honest_le_log hH.length_eq hk hn hρs (fun ρ hρ => hq x ρ hρ)
        (hpcp.coins_le x)⟩,
    computableInTimeAndSpace_kilianVerify_honest_le hH.polyTime hH.length_eq hV
      hpcp.coins_le hq⟩

/-- **Kilian's arguments for NP**: for a collision-resistant `HashFamily H`, every language `L` in
NP has a polynomial-time PCP verifier `V` with `O(log n)` random bits whose accepted compact tables
characterize `L`, such that Kilian's protocol over `V` and `H` accepts the honest prover on every
accepted table with probability one, is computationally sound for `L`, and has honest transcripts
of `O(n² · (log₂ |enc x| + 1))` payload bits at security parameter `n`. -/
theorem exists_kilianSound_of_mem_NP (hH : HashFamily H) {enc : α ↪ List Bool} {L : Set α}
    (hL : L ∈ NP enc) :
    ∃ (V : PCPVerifier α) (c : ℕ), V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x, x ∈ L ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x table, V.tableVerifier (x, table) = true →
        ∀ n, ProbComp.eval (kilianHonestGame H V x table n) = PMF.pure true) ∧
      KilianSound H V enc L ∧
      ∃ C : ℕ, ∀ (n : ℕ) (k : List Bool) (x : α) (table : List Bool) (ρs : List (List Bool)),
        k.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins x) →
          kilianCommunication k (kilianCommit H V k x table) ρs
            (kilianRespond H V k x table ρs) ≤
          C * (n + 1) ^ 2 * (Nat.log 2 (enc x).length + 1) := by
  obtain ⟨R, rfl⟩ := (mem_NP_iff_exists_npRelation (enc := enc)).mp hL
  obtain ⟨V, _, c, _, hV, hcoins, -, -, -, -, hmem, -, -, hsound, hcomm, -⟩ :=
    exists_kilianArgument_of_npRelation hH R
  exact ⟨V, c, hV, hcoins, hmem,
    fun x table htable n => eval_kilianHonestGame H V hH.length_eq htable n, hsound, hcomm⟩

end Cslib.Crypto
