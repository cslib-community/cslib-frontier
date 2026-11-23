/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

/-!
# Prefix-free word-oracle distinguishers

This module records word-oracle queries and expresses prefix-free admissibility against
deterministic oracles of the declared reply width. Invalid queries are ignored by the prefix
condition, and repeated identical valid queries are allowed.

To apply [BonehShoup2023], Definition 4.5 (printed p. 152), one must also show that every query
is nonempty and belongs to the PRF input domain.

## Main definitions

* `Cslib.Crypto.wordQueryRunDist`: the law of the output and chronological query log.
* `Cslib.Crypto.IsPrefixFreeOraclePPT`: strict oracle-PPT distinguishers with prefix-free queries.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Definition 4.5, printed p. 152.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- A query list is prefix-free on `valid` when no valid query is a prefix of a distinct valid query
([BonehShoup2023], Section 4.6.1, Definition 4.5, printed p. 152). Repeated identical queries are
allowed. -/
@[expose]
def WordPrefixFree (valid : List Bool → Bool) (queries : List (List Bool)) : Prop :=
  ∀ x ∈ queries, valid x = true → ∀ y ∈ queries, valid y = true → x ≠ y → ¬ x.IsPrefix y

/-- Distribution of `(output, query_log)` pairs when `program` interacts with a deterministic word
oracle `oracle`, recording word requests in chronological order. -/
@[expose]
noncomputable def wordQueryRunDist {α : Type} (oracle : List Bool → List Bool) :
    WordOracleComp Unit α → PMF (α × List (List Bool))
  | .pure a => PMF.pure (a, [])
  | .liftBind (.inl k) cont =>
    (ProbComp.unifOracle k).bind fun c => wordQueryRunDist oracle (cont c)
  | .liftBind (.inr request) cont =>
    (wordQueryRunDist oracle (cont (oracle request.2))).map fun (a, log) =>
      (a, request.2 :: log)

/-- Returning a value records no external queries. -/
@[simp] theorem wordQueryRunDist_pure {α : Type} (oracle : List Bool → List Bool) (a : α) :
    wordQueryRunDist oracle (pure a) = PMF.pure (a, []) :=
  rfl

/-- A private sample affects the continuation but contributes no external query to the log. -/
theorem wordQueryRunDist_sample_bind {α β : Type} (oracle : List Bool → List Bool)
    (sampler : ProbComp α) (next : α → WordOracleComp Unit β) :
    wordQueryRunDist oracle (do
      let a ← ProbOracleComp.sample sampler
      next a) =
      (ProbComp.eval sampler).bind (fun a => wordQueryRunDist oracle (next a)) := by
  induction sampler with
  | pure a => simp [ProbOracleComp.sample_pure, ProbComp.eval_pure]
  | liftBind k cont ih =>
    change (ProbComp.unifOracle k).bind
      (fun c => wordQueryRunDist oracle (ProbOracleComp.sample (cont c) >>= next)) =
      ((ProbComp.unifOracle k).bind (fun c => ProbComp.eval (cont c))).bind
        (fun a => wordQueryRunDist oracle (next a))
    simp only [PMF.bind_bind, ih]

/-- An external word query adds its request to the front of the continuation's log. -/
theorem wordQueryRunDist_query_bind {α : Type} (oracle : List Bool → List Bool)
    (word : List Bool) (next : List Bool → WordOracleComp Unit α) :
    wordQueryRunDist oracle (do
      let reply ← ProbOracleComp.query ((), word)
      next reply) =
      (wordQueryRunDist oracle (next (oracle word))).map
        (fun (a, log) => (a, word :: log)) :=
  rfl

/-- `IsPrefixFreeOn valid outLen program` holds when, against every deterministic word oracle that
maps valid words to `outLen`-bit replies and invalid words to `[]`, every supported query log of
`program` satisfies `WordPrefixFree valid`. This is the domain-relative prefix condition from
[BonehShoup2023], Definition 4.5 (printed p. 152), which additionally requires every query to be
nonempty and in the input domain. -/
@[expose]
def IsPrefixFreeOn {α : Type} (valid : List Bool → Bool) (outLen : ℕ)
    (program : WordOracleComp Unit α) : Prop :=
  ∀ oracle : List Bool → List Bool,
    (∀ w, valid w = false → oracle w = []) →
    (∀ w, valid w = true → (oracle w).length = outLen) →
    ∀ result ∈ (wordQueryRunDist oracle program).support,
      WordPrefixFree valid result.2

/-- Uniform strict oracle-PPT distinguishers whose queries are prefix-free on `valid n` with
`outLen n`-bit valid replies at every security parameter `n`, in the sense of `IsPrefixFreeOn`. -/
@[expose]
def IsPrefixFreeOraclePPT (valid : ℕ → List Bool → Bool) (outLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) : Prop :=
  IsOraclePPT encBool adversary ∧ ∀ n, IsPrefixFreeOn (valid n) (outLen n) (adversary n [])

/-- Every program is prefix-free on a fixed-length domain, since equal-length prefixes are equal. -/
theorem isPrefixFreeOn_of_fixedLength {α : Type} {valid : List Bool → Bool} {outLen : ℕ}
    (heqLen : ∀ x y, valid x = true → valid y = true → x.length = y.length)
    (program : WordOracleComp Unit α) :
    IsPrefixFreeOn valid outLen program := by
  intro _ _ _ _ _ x _ hx y _ hy hxy hpre
  exact hxy (hpre.eq_of_length (heqLen x y hx hy))

private theorem length_snd_le_of_mem_support_wordQueryRunDist {α : Type}
    (oracle : List Bool → List Bool) {program : WordOracleComp Unit α} {q : ℕ}
    (hq : program.IsQueryBounded q) {result : α × List (List Bool)}
    (hmem : result ∈ (wordQueryRunDist oracle program).support) :
    result.2.length ≤ q := by
  induction program generalizing q result with
  | pure a =>
    simp only [wordQueryRunDist, PMF.mem_support_pure_iff] at hmem
    subst hmem
    exact Nat.zero_le q
  | liftBind op cont ih =>
    obtain ⟨hle, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp hq
    cases op with
    | inl m =>
      simp only [wordQueryRunDist, PMF.mem_support_bind_iff] at hmem
      obtain ⟨c, _, hc⟩ := hmem
      simpa only [Sum.elim_inl, Nat.sub_zero] using ih c (hcont c) hc
    | inr req =>
      simp only [wordQueryRunDist, PMF.mem_support_map_iff] at hmem
      obtain ⟨⟨a, log⟩, hc, rfl⟩ := hmem
      have hlen := ih (oracle req.2) (hcont (oracle req.2)) hc
      simp only [Sum.elim_inr] at hle hlen
      simp only [List.length_cons]
      omega

/-- Every program making at most one query is prefix-free on every domain. -/
theorem isPrefixFreeOn_of_isQueryBounded_one {α : Type} (valid : List Bool → Bool) (outLen : ℕ)
    {program : WordOracleComp Unit α} (hq : program.IsQueryBounded 1) :
    IsPrefixFreeOn valid outLen program := by
  intro oracle _ _ result hmem x hx _ y hy _ hxy
  have hlen := length_snd_le_of_mem_support_wordQueryRunDist oracle hq hmem
  rcases result with ⟨_, _ | ⟨w, _ | ⟨w', _⟩⟩⟩
  · cases hx
  · simp only [List.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · simp only [List.length_cons] at hlen
    omega

end Cslib.Crypto
