/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MAC
public import CslibFrontier.Crypto.Computational.MAC.Counter
public import CslibFrontier.Crypto.Protocols.MAC.CarterWegman
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.HashFamily.UniformOffset
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases

/-!
# Stateful nonce-based Carter–Wegman message authentication codes

This module formalizes Boneh–Shoup Attack Game 7.4 ([BonehShoup2023], Section 7.5.1, p. 274) and
the information-theoretic and statistical-DUF computational steps toward Theorem 7.10 (p. 274).

Under a truly random pad function `rf ← PMF.uniformOfFintype (N → Y)`, an adaptive `NonceForger`
querying distinct signing nonces achieves SUF-CMA / EUF-CMA forgery probability at most
`max ε (1 / |Y|) ≤ ε + 1 / |Y|`. Replacing `rf` with a uniform `PseudorandomFunction` via
`prfNonceToPrfDistinguisher` yields the quantitative bound `ε.toReal + (2 ^ n)⁻¹ + prfAdvantage`
on `carterWegmanNonceMAC` and asymptotic `SUFCMA`, `EUFCMA`, and stateful counter-nonce
`CounterSUFCMA` steps under a statistical DUF (`Negligible ε`, [BonehShoup2023], Definition 7.5,
p. 269). Theorem 7.10 assumes only a computational DUF (Attack Game 7.3, p. 268); that step is open
(#5293). Concrete hash instantiations (including `linearHashNonceMAC`, realizing Theorem 7.10 for
Boolean-matrix linear hashing) live in
`CslibFrontier.Crypto.Protocols.MAC.CarterWegman.Instantiations`.

## Main definitions

* `Cslib.Crypto.Protocols.CarterWegman.NonceForger`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceFnHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceSimHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.reconstructPadFn`,
  `Cslib.Crypto.Protocols.CarterWegman.checkNonceSUF`,
  `Cslib.Crypto.Protocols.CarterWegman.checkNonceEUF`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedNonceStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedNonceGame`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceGame`: nonce-based Carter–Wegman handlers, pad
  reconstruction, verification predicates, and experiments (Boneh–Shoup Attack Game 7.4).
* `Cslib.Crypto.Protocols.CarterWegman.carterWegmanNonceMAC`,
  `Cslib.Crypto.Protocols.CarterWegman.prfNonceToPrfDistinguisher`: word-level `NonceMACScheme`
  packaging and `OracleDistinguisher` PRF reduction.

## Main results

* `Cslib.Crypto.Protocols.CarterWegman.probOracleComp_uniform_bind_run_interpret_nonceFnHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.uniform_bind_run_interpret_nonceFnHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.seed_uniform_checkNonceSUF_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame_le_max`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceGame_le_max`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceGame_le`: ideal random-function simulation and bounds
  (Boneh–Shoup Attack Game 7.4, after Theorem 7.10).
* `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfNonceToPrfDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfRealGame_prfNonceToPrfDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfIdealGame_prfNonceToPrfDistinguisher_le`,
  `Cslib.Crypto.Protocols.CarterWegman.sufCmaGame_carterWegmanNonceMAC_toReal_le`: `IsOraclePPT`
  admissibility and quantitative SUF-CMA reduction bounds for `carterWegmanNonceMAC`.
* `Cslib.Crypto.PseudorandomFunction.sufCma_carterWegmanNonceMAC_of_statisticalDUF`,
  `Cslib.Crypto.PseudorandomFunction.eufCma_carterWegmanNonceMAC_of_statisticalDUF`,
  `Cslib.Crypto.PseudorandomFunction.counterSufCma_carterWegmanNonceMAC_of_statisticalDUF`:
  statistical-DUF steps toward Boneh–Shoup Theorem 7.10 (p. 274) and its counter-nonce stateful
  use; the computational-DUF theorem is open (#5293).

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.4–7.5.
-/

public section

namespace Cslib.Crypto.Protocols.CarterWegman

open Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Full nonce-based Carter–Wegman MAC (Boneh–Shoup Attack Game 7.4 and Theorem 7.10) -/

section Nonce

variable {K M N Y : Type} [AddGroup Y]

/-- An adaptive multi-query forger in the nonce-based MAC game ([BonehShoup2023], Section 7.5.1,
Attack Game 7.4, p. 274): it draws private coins `s ← coins`, makes adaptive signing queries
`(m, x) : M × N` (receiving tag `t : Y`), and outputs a candidate forgery
`((m', x'), t') : (M × N) × Y`. -/
structure NonceForger (M N Y : Type) where
  /-- Type of the forger's private coins. -/
  Coins : Type
  /-- Distribution of the forger's private coins. -/
  coins : PMF Coins
  /-- Adaptive oracle program making signing queries `(m, x) : M × N` and outputting a candidate
  forgery `((m', x'), t') : (M × N) × Y`. -/
  forge : Coins → OracleComp (fun _ : M × N => Y) ((M × N) × Y)

/-- Nonce-based Carter–Wegman signing handler driven by a pad function `padFn : N → Y`:
on signing query `q = (m, x)`, compute `t = sign hash k (padFn x) m`, append `(q, t)` to the
query–tag transcript `tr`, and return `t`. -/
@[expose]
noncomputable def nonceFnHandler (hash : K → M → Y) (k : K) (padFn : N → Y) (q : M × N) :
    StateT (List ((M × N) × Y)) PMF Y := fun tr =>
  let t := sign hash k (padFn q.2) q.1
  PMF.pure (t, tr ++ [(q, t)])

/-- Simulated key-independent nonce signing handler: on query `q = (m, x)`, sample a uniform tag
`t ← PMF.uniformOfFintype Y`, append `(q, t)` to the query–tag transcript `tr`, and return `t`. -/
@[expose]
noncomputable def nonceSimHandler [Fintype Y] [Nonempty Y] (q : M × N) :
    StateT (List ((M × N) × Y)) PMF Y := fun tr => do
  let t ← PMF.uniformOfFintype Y
  return (t, tr ++ [(q, t)])

/-- Reconstruct a pad function `N → Y` from a query–tag transcript `tr : List ((M × N) × Y)` and a
background table `table : N → Y`, setting the pad at each queried nonce `x_i` to
`-hash k m_i + t_i` while retaining `table x` at all unqueried nonces `x`. -/
def reconstructPadFn [DecidableEq N] (hash : K → M → Y) (k : K)
    (tr : List ((M × N) × Y)) (table : N → Y) : N → Y :=
  tr.foldl (fun fn ((m, x), t) => Function.update fn x (-hash k m + t)) table

@[simp]
theorem reconstructPadFn_nil [DecidableEq N] (hash : K → M → Y) (k : K) (table : N → Y) :
    reconstructPadFn hash k [] table = table := by
  rfl

@[simp]
theorem reconstructPadFn_cons [DecidableEq N] (hash : K → M → Y) (k : K)
    (m : M) (x : N) (t : Y) (tr : List ((M × N) × Y)) (table : N → Y) :
    reconstructPadFn hash k (((m, x), t) :: tr) table =
      reconstructPadFn hash k tr (Function.update table x (-hash k m + t)) := by
  rfl

@[simp]
theorem reconstructPadFn_append_singleton [DecidableEq N] (hash : K → M → Y) (k : K)
    (tr : List ((M × N) × Y)) (m : M) (x : N) (t : Y) (table : N → Y) :
    reconstructPadFn hash k (tr ++ [((m, x), t)]) table =
      Function.update (reconstructPadFn hash k tr table) x (-hash k m + t) := by
  simp [reconstructPadFn]

/-- At any nonce `x` not appearing in `tr`, `reconstructPadFn hash k tr table x = table x`. -/
theorem reconstructPadFn_apply_of_not_mem [DecidableEq N] (hash : K → M → Y) (k : K)
    {tr : List ((M × N) × Y)} {x : N} (hx : x ∉ tr.map (fun ((_, x'), _) => x'))
    (table : N → Y) :
    reconstructPadFn hash k tr table x = table x := by
  induction tr generalizing table with
  | nil => rfl
  | cons e tr ih =>
    rcases e with ⟨⟨m', x'⟩, t'⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [reconstructPadFn_cons, ih hx.2, Function.update_of_ne hx.1]

private theorem reconstructPadFn_congr_of_forall_ne [DecidableEq N] (hash : K → M → Y) (k : K)
    {tr : List ((M × N) × Y)} {x : N} {table₁ table₂ : N → Y}
    (h : ∀ z ≠ x, table₁ z = table₂ z) :
    ∀ z ≠ x, reconstructPadFn hash k tr table₁ z = reconstructPadFn hash k tr table₂ z := by
  induction tr generalizing table₁ table₂ with
  | nil => exact h
  | cons e tr ih =>
    rcases e with ⟨⟨m', x'⟩, t'⟩
    refine ih fun z hz => ?_
    by_cases he : z = x' <;> simp [he, h z hz]

private theorem reconstructPadFn_append_update_self [DecidableEq N] (hash : K → M → Y) (k : K)
    (tr : List ((M × N) × Y)) (m : M) (x : N) (t r : Y) (table : N → Y) :
    reconstructPadFn hash k (tr ++ [((m, x), t)]) (Function.update table x r) =
      reconstructPadFn hash k (tr ++ [((m, x), t)]) table := by
  rw [reconstructPadFn_append_singleton, reconstructPadFn_append_singleton]
  funext z
  by_cases hz : z = x
  · subst hz; simp
  · simp only [Function.update_of_ne hz]
    exact reconstructPadFn_congr_of_forall_ne hash k
      (fun w hw => Function.update_of_ne hw r table) z hz

private theorem reconstructPadFn_append_sign_of_not_mem [DecidableEq N] (hash : K → M → Y) (k : K)
    {tr : List ((M × N) × Y)} (m : M) {x : N} (hx : x ∉ tr.map (fun ((_, x'), _) => x'))
    (table : N → Y) :
    reconstructPadFn hash k (tr ++ [((m, x), sign hash k (table x) m)]) table =
      reconstructPadFn hash k tr table := by
  rw [reconstructPadFn_append_singleton, sign, neg_add_cancel_left,
    ← reconstructPadFn_apply_of_not_mem hash k hx table, Function.update_eq_self]

/-- For any entry `((m, x), t) ∈ tr` in a transcript with distinct nonces
`(tr.map (fun ((_, x), _) => x)).Nodup`, `reconstructPadFn` evaluates at `x` to
`-hash k m + t`. -/
theorem reconstructPadFn_apply_of_mem_of_nodup [DecidableEq N] (hash : K → M → Y) (k : K)
    {tr : List ((M × N) × Y)} {m : M} {x : N} {t : Y} (he : ((m, x), t) ∈ tr)
    (hnodup : (tr.map (fun ((_, x), _) => x)).Nodup) (table : N → Y) :
    reconstructPadFn hash k tr table x = -hash k m + t := by
  induction tr generalizing table with
  | nil => contradiction
  | cons hd tl ih =>
    rcases hd with ⟨⟨m', x'⟩, t'⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rw [reconstructPadFn_cons]
    rcases List.mem_cons.mp he with hhd | htl
    · cases hhd
      rw [reconstructPadFn_apply_of_not_mem hash k hnodup.1, Function.update_self]
    · exact ih htl hnodup.2 _

private theorem uniform_reconstructPadFn_step {β : Type} [Fintype N] [DecidableEq N]
    [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K)
    {tr : List ((M × N) × Y)} (m : M) {x : N} (hx : x ∉ tr.map (fun ((_, x'), _) => x'))
    (F : Y → List ((M × N) × Y) → (N → Y) → PMF β) :
    ((PMF.uniformOfFintype (N → Y)).bind fun table =>
      let t := sign hash k (reconstructPadFn hash k tr table x) m
      F t (tr ++ [((m, x), t)]) (reconstructPadFn hash k tr table)) =
    ((PMF.uniformOfFintype Y).bind fun t =>
      (PMF.uniformOfFintype (N → Y)).bind fun table =>
        F t (tr ++ [((m, x), t)]) (reconstructPadFn hash k (tr ++ [((m, x), t)]) table)) := by
  conv_lhs =>
    enter [2, table]
    dsimp only
    rw [reconstructPadFn_apply_of_not_mem hash k hx table,
      ← reconstructPadFn_append_sign_of_not_mem hash k m hx table]
  rw [PMF.bind_uniformOfFintype_update x]
  simp only [Function.update_self, reconstructPadFn_append_update_self]
  conv_rhs =>
    rw [← map_sign_eq_uniform hash k m, PMF.bind_map]
  rfl

omit [AddGroup Y] in
private theorem not_nodup_map_append_of_mem {tr : List ((M × N) × Y)} (m : M) {x : N} (t : Y)
    (hx : x ∈ tr.map (fun e => e.1.2)) :
    ¬ ((tr ++ [((m, x), t)]).map (fun e => e.1.2)).Nodup := by
  rw [List.map_append, List.map_singleton, List.nodup_append]
  rintro ⟨-, -, hdisj⟩
  exact hdisj x hx x (List.mem_singleton.mpr rfl) rfl

omit [AddGroup Y] in
private theorem runWith_bind_of_not_nodup {Query : Type} {spec : Query → Type} {α β : Type}
    {oracle : (q : Query) → StateT (List ((M × N) × Y)) PMF (spec q)}
    (happ : ∀ q tr res, res ∈ (oracle q tr).support → ∃ s, res.2 = tr ++ s)
    (prog : ProbOracleComp spec α) {tr : List ((M × N) × Y)}
    (hnot : ¬ (tr.map (fun e => e.1.2)).Nodup)
    (g : α → List ((M × N) × Y) → PMF β) (c : PMF β)
    (hg : ∀ a tr', ¬ (tr'.map (fun e => e.1.2)).Nodup → g a tr' = c) :
    (ProbOracleComp.runWith oracle prog tr).bind (fun res => g res.1 res.2) = c := by
  have hcongr : ∀ res ∈ (ProbOracleComp.runWith oracle prog tr).support,
      g res.1 res.2 = c := fun res hres =>
    hg res.1 res.2 (ProbOracleComp.runWith_invariant oracle
      (fun s => ¬ (s.map (fun e => e.1.2)).Nodup)
      (fun q s hs a s' ha => by
        obtain ⟨u, he⟩ := happ q s (a, s') ha
        dsimp only at he
        rw [he, List.map_append]
        exact fun h => hs (h.sublist (List.sublist_append_left _ _)))
      prog tr hnot res.1 res.2 hres)
  rw [PMF.bind_congr_on_support _ _ _ hcongr, PMF.bind_const]

/-- **Multi-query simulation equivalence for `nonceFnHandler` on `ProbOracleComp`**:
for any post-processing `post` that collapses to a constant distribution `c` whenever the transcript
has a repeated nonce (`¬ (tr'.map (fun ((_, x), _) => x)).Nodup`), running `prog` with private coin
flips against `nonceFnHandler hash k (reconstructPadFn hash k tr table)` over
`table ← PMF.uniformOfFintype (N → Y)` has the exact same distribution as running `prog` against the
key-independent `nonceSimHandler` and reconstructing `reconstructPadFn hash k res.2 table` at the
end. -/
theorem probOracleComp_uniform_bind_run_interpret_nonceFnHandler {α β : Type}
    [Fintype N] [DecidableEq N] [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K)
    (prog : ProbOracleComp (fun _ : M × N => Y) α) (tr : List ((M × N) × Y))
    (post : α → List ((M × N) × Y) → (N → Y) → PMF β) (c : PMF β)
    (hpost : ∀ a tr' padFn, ¬ (tr'.map (fun ((_, x), _) => x)).Nodup → post a tr' padFn = c) :
    ((PMF.uniformOfFintype (N → Y)).bind fun table =>
      (ProbOracleComp.runWith (nonceFnHandler hash k (reconstructPadFn hash k tr table))
          prog tr).bind
        fun res => post res.1 res.2 (reconstructPadFn hash k tr table)) =
    ((ProbOracleComp.runWith nonceSimHandler prog tr).bind fun res =>
      (PMF.uniformOfFintype (N → Y)).bind fun table =>
        post res.1 res.2 (reconstructPadFn hash k res.2 table)) := by
  have happ_fn (padFn : N → Y) (q : M × N) (tr₁ : List ((M × N) × Y)) res
      (hres : res ∈ (nonceFnHandler hash k padFn q tr₁).support) :
      ∃ s, res.2 = tr₁ ++ s := by
    supp_cases hres [nonceFnHandler]
    exact ⟨[(q, _)], rfl⟩
  have happ_sim (q : M × N) (tr₁ : List ((M × N) × Y)) res
      (hres : res ∈ (nonceSimHandler q tr₁).support) :
      ∃ s, res.2 = tr₁ ++ s := by
    supp_cases hres [nonceSimHandler] with ⟨t, rfl⟩
    exact ⟨[(q, t)], rfl⟩
  have hpost_sim (a : α) (tr' : List ((M × N) × Y))
      (hnot : ¬ (tr'.map (fun e => e.1.2)).Nodup) :
      ((PMF.uniformOfFintype (N → Y)).bind fun table =>
        post a tr' (reconstructPadFn hash k tr' table)) = c := by
    simp only [hpost a tr' _ hnot, PMF.bind_const]
  have hlhs (p : ProbOracleComp (fun _ : M × N => Y) α) {tr₁ : List ((M × N) × Y)}
      (hnot : ¬ (tr₁.map (fun e => e.1.2)).Nodup) (padFn : N → Y) :=
    runWith_bind_of_not_nodup (happ_fn padFn) p hnot (fun a tr' => post a tr' padFn) c
      fun a tr' => hpost a tr' padFn
  have hrhs (p : ProbOracleComp (fun _ : M × N => Y) α) {tr₁ : List ((M × N) × Y)}
      (hnot : ¬ (tr₁.map (fun e => e.1.2)).Nodup) :=
    runWith_bind_of_not_nodup happ_sim p hnot
      (fun a tr' => (PMF.uniformOfFintype (N → Y)).bind fun table =>
        post a tr' (reconstructPadFn hash k tr' table))
      c hpost_sim
  induction prog using ProbOracleComp.induction generalizing tr with
  | pure a => simp
  | sample_bind m cont ih =>
    simp only [ProbOracleComp.runWith_sample_bind, PMF.bind_bind]
    pmf_swap with i
    exact ih i tr
  | query_bind q cont ih =>
    by_cases hnodup : (tr.map (fun e => e.1.2)).Nodup
    · simp only [pmf_norm, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        nonceFnHandler, nonceSimHandler]
      by_cases hx : q.2 ∈ tr.map (fun e => e.1.2)
      · have hnot (t : Y) := not_nodup_map_append_of_mem q.1 t hx
        simp only [fun t => hlhs (cont t) (hnot t), fun t => hrhs (cont t) (hnot t), PMF.bind_const]
      · rw [uniform_reconstructPadFn_step hash k q.1 hx
          (fun t tr' fn => (ProbOracleComp.runWith (nonceFnHandler hash k fn) (cont t) tr').bind
            fun res => post res.1 res.2 fn)]
        congr 1 with t : 1
        exact ih t (tr ++ [(q, t)])
    · simp only [hlhs (ProbOracleComp.query q >>= cont) hnodup,
        hrhs (ProbOracleComp.query q >>= cont) hnodup, PMF.bind_const]

/-- **Multi-query simulation equivalence for `nonceFnHandler` under a random function**:
specialization of `probOracleComp_uniform_bind_run_interpret_nonceFnHandler` to deterministic
`OracleComp` programs. -/
theorem uniform_bind_run_interpret_nonceFnHandler {α β : Type} [Fintype N] [DecidableEq N]
    [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K)
    (prog : OracleComp (fun _ : M × N => Y) α) (tr : List ((M × N) × Y))
    (post : α → List ((M × N) × Y) → (N → Y) → PMF β) (c : PMF β)
    (hpost : ∀ a tr' padFn, ¬ (tr'.map (fun ((_, x), _) => x)).Nodup → post a tr' padFn = c) :
    ((PMF.uniformOfFintype (N → Y)).bind fun table =>
      ((OracleComp.interpret
        (nonceFnHandler hash k (reconstructPadFn hash k tr table)) prog).run tr).bind
        fun res => post res.1 res.2 (reconstructPadFn hash k tr table)) =
    (((OracleComp.interpret nonceSimHandler prog).run tr).bind fun res =>
      (PMF.uniformOfFintype (N → Y)).bind fun table =>
        post res.1 res.2 (reconstructPadFn hash k res.2 table)) := by
  simpa only [ProbOracleComp.runWith_liftRight, OracleComp.runWith_eq_run_interpret] using
    probOracleComp_uniform_bind_run_interpret_nonceFnHandler hash k (OracleComp.liftRight prog)
      tr post c hpost

variable [DecidableEq M] [DecidableEq N] [DecidableEq Y]

/-- Nonce-based SUF-CMA verification predicate on a query–tag transcript `tr` and pad function
`padFn` ([BonehShoup2023], Section 7.5.1, Attack Game 7.4, p. 274): all signing queries in `tr` used
distinct nonces (`(tr.map (fun ((_, x), _) => x)).Nodup`), the candidate `out = ((m', x'), t')` was
not returned by any signing query (`!tr.contains out`), and
`verify hash k (padFn x') m' t' = true`. -/
@[expose]
def checkNonceSUF (hash : K → M → Y) (k : K) (padFn : N → Y) (tr : List ((M × N) × Y))
    (out : (M × N) × Y) : Bool :=
  let cand := out.1
  let m' := cand.1
  let x' := cand.2
  let t' := out.2
  decide (tr.map (fun ((_, x), _) => x)).Nodup &&
    !tr.contains out &&
    verify hash k (padFn x') m' t'

/-- Nonce-based EUF-CMA (message-freshness) verification predicate on a query–tag transcript `tr`
and pad function `padFn`: all signing queries in `tr` used distinct nonces, the message
`m'` was never queried (`!(tr.map (fun ((m, _), _) => m)).contains m'`), and
`verify hash k (padFn x') m' t' = true`. -/
def checkNonceEUF (hash : K → M → Y) (k : K) (padFn : N → Y) (tr : List ((M × N) × Y))
    (out : (M × N) × Y) : Bool :=
  let cand := out.1
  let m' := cand.1
  let x' := cand.2
  let t' := out.2
  decide (tr.map (fun ((_, x), _) => x)).Nodup &&
    !(tr.map (fun ((m, _), _) => m)).contains m' &&
    verify hash k (padFn x') m' t'

/-- Global message freshness (`checkNonceEUF`) implies pair freshness (`checkNonceSUF`). -/
theorem checkNonceEUF_imp_checkNonceSUF (hash : K → M → Y) (k : K) (padFn : N → Y)
    (tr : List ((M × N) × Y)) (out : (M × N) × Y) :
    checkNonceEUF hash k padFn tr out = true → checkNonceSUF hash k padFn tr out = true := by
  simp only [checkNonceEUF, checkNonceSUF, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
  rintro ⟨⟨hnodup, hnotm⟩, hv⟩
  refine ⟨⟨hnodup, fun hout => hnotm ⟨out, hout, rfl⟩⟩, hv⟩

/-- The nonce-based Carter–Wegman SUF-CMA experiment under an arbitrary pad-function distribution
`rfDist : PMF (N → Y)`. -/
noncomputable def maskedNonceStrongGame (seed : PMF K) (rfDist : PMF (N → Y))
    (hash : K → M → Y) (forger : NonceForger M N Y) : PMF Bool := do
  let k ← seed
  let rf ← rfDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (nonceFnHandler hash k rf) (forger.forge s)).run []
  return checkNonceSUF hash k rf res.2 res.1

/-- The nonce-based Carter–Wegman EUF-CMA (message-freshness) experiment under an arbitrary
pad-function distribution `rfDist : PMF (N → Y)`. -/
noncomputable def maskedNonceGame (seed : PMF K) (rfDist : PMF (N → Y))
    (hash : K → M → Y) (forger : NonceForger M N Y) : PMF Bool := do
  let k ← seed
  let rf ← rfDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (nonceFnHandler hash k rf) (forger.forge s)).run []
  return checkNonceEUF hash k rf res.2 res.1

/-- Monotonicity from message-freshness (`maskedNonceGame`) to triple-freshness
(`maskedNonceStrongGame`). -/
theorem maskedNonceGame_le_maskedNonceStrongGame (seed : PMF K) (rfDist : PMF (N → Y))
    (hash : K → M → Y) (forger : NonceForger M N Y) :
    maskedNonceGame seed rfDist hash forger true ≤
      maskedNonceStrongGame seed rfDist hash forger true :=
  bind_apply_mono_on_support seed true fun k _ =>
    bind_apply_mono_on_support rfDist true fun rf _ =>
      bind_apply_mono_on_support forger.coins true fun s _ =>
        map_true_mono ((OracleComp.interpret (nonceFnHandler hash k rf) (forger.forge s)).run [])
          fun res _ => checkNonceEUF_imp_checkNonceSUF hash k rf res.2 res.1

variable [Fintype N] [Fintype Y] [Nonempty Y]

/-- Under `IsDeltaUniversalHash seed hash ε`, for any fixed transcript `tr` and candidate forgery
`out = ((m', x'), t')`, the probability over `k ← seed` and `table ← PMF.uniformOfFintype (N → Y)`
that `checkNonceSUF hash k (reconstructPadFn hash k tr table) tr out = true` is at most
`max ε (Fintype.card Y : ℝ≥0∞)⁻¹`: at most `ε` when `x'` is an issued nonce in `tr`, and at most
`(Fintype.card Y : ℝ≥0∞)⁻¹` when `x'` is an unissued nonce. -/
theorem seed_uniform_checkNonceSUF_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε)
    (tr : List ((M × N) × Y)) (out : (M × N) × Y) :
    (seed.bind fun k =>
      (PMF.uniformOfFintype (N → Y)).bind fun table =>
        PMF.pure (checkNonceSUF hash k (reconstructPadFn hash k tr table) tr out)) true ≤
      max ε (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  by_cases hnodup : (tr.map (fun e => e.1.2)).Nodup
  · by_cases hx : out.1.2 ∈ tr.map (fun e => e.1.2)
    · rcases List.mem_map.mp hx with ⟨⟨⟨m, x⟩, t⟩, he, rfl⟩
      have hbind (k : K) :
          ((PMF.uniformOfFintype (N → Y)).bind fun table =>
            PMF.pure (checkNonceSUF hash k (reconstructPadFn hash k tr table) tr out)) =
          PMF.pure (checkNonceSUF hash k (fun _ => -hash k m + t) tr out) := by
        simp only [checkNonceSUF, reconstructPadFn_apply_of_mem_of_nodup hash k he hnodup,
          PMF.bind_const]
      simp only [hbind]
      refine ((map_true_mono seed fun k _ hcheck => ?_).trans
        (hh.bind_recovered_offset_le m out.1.1 t out.2)).trans (le_max_left _ _)
      simp only [checkNonceSUF, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, decide_eq_true_iff] at hcheck
      rcases hcheck with ⟨⟨-, hnotmem⟩, hv⟩
      have valid := (verify_eq_true_iff _ _ _ _ _).mp hv
      have hne : out.1.1 ≠ m := by
        rintro rfl
        have hv' := (add_recovered_offset_eq_iff _ _ t out.2).mp valid
        obtain rfl : out.2 = t := sub_eq_zero.mp (by simpa only [sub_self] using hv'.symm)
        exact hnotmem he
      simp [hne, valid]
    · rw [PMF.bind_apply]
      refine (tsum_mul_le_of_forall_le seed fun k => ?_).trans (le_max_right _ _)
      refine (bind_apply_mono_on_support (PMF.uniformOfFintype (N → Y))
        (g := fun table => PMF.pure (verify hash k (table out.1.2) out.1.1 out.2)) true
        fun table _ => ?_).trans (le_of_eq ?_)
      · simp only [checkNonceSUF, reconstructPadFn_apply_of_not_mem hash k hx]
        cases decide (tr.map (fun e => e.1.2)).Nodup && !tr.contains out <;> simp
      rw [PMF.bind_uniformOfFintype_update out.1.2]
      simp only [Function.update_self, PMF.bind_const]
      exact uniform_bind_verify_apply_true hash k out.1.1 out.2
  · simp [checkNonceSUF, hnodup]

/-- The ideal nonce-based Carter–Wegman SUF-CMA experiment ([BonehShoup2023], Section 7.5.1,
Attack Game 7.4 and Theorem 7.10, p. 274) under a truly random function
`rf ← PMF.uniformOfFintype (N → Y)`. -/
noncomputable def nonceStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : NonceForger M N Y) : PMF Bool :=
  maskedNonceStrongGame seed (PMF.uniformOfFintype (N → Y)) hash forger

/-- The ideal nonce-based Carter–Wegman EUF-CMA (message-freshness) experiment implied by the SUF
game (`nonceStrongGame`) under a truly random function `rf ← PMF.uniformOfFintype (N → Y)`. -/
noncomputable def nonceGame (seed : PMF K) (hash : K → M → Y)
    (forger : NonceForger M N Y) : PMF Bool :=
  maskedNonceGame seed (PMF.uniformOfFintype (N → Y)) hash forger

/-- Monotonicity from the message-freshness variant (`nonceGame`) to `nonceStrongGame`. -/
theorem nonceGame_le_nonceStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : NonceForger M N Y) :
    nonceGame seed hash forger true ≤ nonceStrongGame seed hash forger true :=
  maskedNonceGame_le_maskedNonceStrongGame seed (PMF.uniformOfFintype (N → Y)) hash forger

/-- **Ideal nonce-based Carter–Wegman SUF-CMA security (`max` bound)**, a step of the proof of
[BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), with a truly random function in place of
the PRF: under `IsDeltaUniversalHash seed hash ε`, every adaptive `NonceForger` wins
`nonceStrongGame` with probability at most `max ε (Fintype.card Y : ℝ≥0∞)⁻¹`. -/
theorem nonceStrongGame_le_max {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : NonceForger M N Y) :
    nonceStrongGame seed hash forger true ≤ max ε (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  simp only [pmf_norm, nonceStrongGame, maskedNonceStrongGame]
  pmf_hoist forger.coins
  refine bind_apply_le_on_support forger.coins fun s _ => ?_
  have hsim (k : K) :
      ((PMF.uniformOfFintype (N → Y)).bind fun rf =>
        ((OracleComp.interpret (nonceFnHandler hash k rf) (forger.forge s)).run []).bind fun res =>
          PMF.pure (checkNonceSUF hash k rf res.2 res.1)) =
      (((OracleComp.interpret nonceSimHandler (forger.forge s)).run []).bind fun res =>
        (PMF.uniformOfFintype (N → Y)).bind fun table =>
          PMF.pure (checkNonceSUF hash k (reconstructPadFn hash k res.2 table) res.2 res.1)) := by
    simpa only [reconstructPadFn_nil] using
      uniform_bind_run_interpret_nonceFnHandler hash k (forger.forge s) []
        (fun out tr' padFn => PMF.pure (checkNonceSUF hash k padFn tr' out))
        (PMF.pure false)
        (fun out tr' padFn hnot => by simp [checkNonceSUF, hnot])
  simp only [hsim]
  pmf_hoist ((OracleComp.interpret nonceSimHandler (forger.forge s)).run [])
  exact bind_apply_le_on_support _ fun ⟨out, tr⟩ _ => seed_uniform_checkNonceSUF_le hh tr out

/-- **Ideal nonce-based Carter–Wegman SUF-CMA security (`+` bound)**, a step of the proof of
[BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), with a truly random function in place of
the PRF: winning probability is at most `ε + (Fintype.card Y : ℝ≥0∞)⁻¹`. -/
theorem nonceStrongGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : NonceForger M N Y) :
    nonceStrongGame seed hash forger true ≤ ε + (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  (nonceStrongGame_le_max hh forger).trans (max_le_add_of_nonneg zero_le zero_le)

/-- **Ideal nonce-based Carter–Wegman EUF-CMA (message-freshness) security (`max` bound)**. -/
theorem nonceGame_le_max {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : NonceForger M N Y) :
    nonceGame seed hash forger true ≤ max ε (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  (nonceGame_le_nonceStrongGame seed hash forger).trans (nonceStrongGame_le_max hh forger)

/-- **Ideal nonce-based Carter–Wegman EUF-CMA (message-freshness) security (`+` bound)**. -/
theorem nonceGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : NonceForger M N Y) :
    nonceGame seed hash forger true ≤ ε + (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  (nonceGame_le_nonceStrongGame seed hash forger).trans (nonceStrongGame_le hh forger)

/-- **Computational nonce-based Carter–Wegman MAC (`NonceMACScheme`)**
([BonehShoup2023], Section 7.5.1, Attack Game 7.4 and Theorem 7.10, p. 274):
given a polynomial-time message-length schedule `msgLen : ℕ → ℕ`, a strict-PPT hash-key sampler
`seed : ℕ → ProbComp (List Bool)`, a polynomial-time hash evaluator
`hash : ℕ → List Bool → List Bool → List Bool`, and a polynomial-time PRF family
`family : List Bool → List Bool → List Bool`:
* `keyGen n` samples `k ← seed n` and `prfKey ← BitString.sampleList n`, returning the framed pair
  `encPair encBits encBits (k, prfKey)`.
* `sign sk msg nonce` recovers `k := unframe sk`, `prfKey := dropFrame sk`, and
  `n := prfKey.length`; if `msg.length == msgLen n` and `nonce.length == n`, it returns the `n`-bit
  Carter–Wegman tag `BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n]`,
  and otherwise `[]`.
* `verify sk msg nonce tag` checks `msg.length == msgLen n`, `nonce.length == n`, and
  `BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n] == tag`. -/
noncomputable def carterWegmanNonceMAC (msgLen : ℕ → ℕ)
    (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool)
    (family : List Bool → List Bool → List Bool)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) : NonceMACScheme where
  msgLen := msgLen
  nonceLen n := n
  msgLen_polyTime := hmsgLen
  nonceLen_polyTime := by fun_prop
  keyGen := carterWegmanKeyGen seed
  sign sk msg nonce :=
    let k := unframe sk
    let prfKey := dropFrame sk
    let n := prfKey.length
    pure (if (msg.length == msgLen n) && (nonce.length == n) then
      BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n]
    else
      [])
  verify sk msg nonce tag :=
    let k := unframe sk
    let prfKey := dropFrame sk
    let n := prfKey.length
    (msg.length == msgLen n) && (nonce.length == n) &&
      (BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n] == tag)
  keyGen_ppt := isPPTOn_carterWegmanKeyGen hseed
  sign_ppt := by
    have hh : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool =>
          hash (dropFrame p.1).length (unframe p.1) p.2.1)
        (encPair encBits (encPair encBits encBits)) encBits :=
      hhash.comp (ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.prod (by fun_prop) (by fun_prop)))
    apply ComputableInPolyTime.isPPTOn
    fun_prop
  verify_polyTime := by
    have hh : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool × List Bool =>
          hash (dropFrame p.1).length (unframe p.1) p.2.1)
        (encPair encBits (encPair encBits (encPair encBits encBits))) encBits :=
      hhash.comp (ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.prod (by fun_prop) (by fun_prop)))
    dsimp only
    fun_prop
  verify_sign := by
    intro n sk hsk msg hmsg nonce hnonce tag htag
    simp only [carterWegmanKeyGen, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsk
    rcases hsk with ⟨k, -, prfKey, hprfKey, rfl⟩
    have hprfLen : prfKey.length = n := BitString.length_of_mem_support_uniformList hprfKey
    simp only [encPair_apply, encBits_apply, dropFrame_frame_append,
      hprfLen, hmsg, hnonce, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag ⊢
    subst htag
    simp

private def cwNonceLogHandler (msgLen : ℕ → ℕ) (hash : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k : List Bool) (request : Unit × List Bool) :
    StateT (List ((List Bool × List Bool) × List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun queriedTriples =>
    let msg := unframe request.2
    let nonce := dropFrame request.2
    if (msg.length == msgLen n) && (nonce.length == n) then
      (fun pad =>
        let tag := BitString.listXor n [hash n k msg, pad]
        (tag, ((msg, nonce), tag) :: queriedTriples)) <$>
        (List.take n <$> ProbOracleComp.query ((), nonce))
    else
      pure ([], queriedTriples)

/-- Oracle reduction turning an adaptive word-level `NonceMACForger` into an `OracleDistinguisher`
for the PRF security game ([BonehShoup2023], Section 7.5.1, Theorem 7.10, p. 274) via
`prfLogDistinguisher`. -/
def prfNonceToPrfDistinguisher (msgLen : ℕ → ℕ) (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool) (adversary : NonceMACForger) :
    OracleDistinguisher :=
  prfLogDistinguisher seed (cwNonceLogHandler msgLen hash) adversary
    (fun (((_, nonce), _), _) => nonce)
    (fun n k (((msg, nonce), tag), tr) pad =>
      (msg.length == msgLen n) && (nonce.length == n) &&
        decide (tr.map (fun ((_, x), _) => x)).Nodup && !tr.contains ((msg, nonce), tag) &&
        (BitString.listXor n [hash n k msg, pad] == tag))

/-- `prfNonceToPrfDistinguisher` is uniformly strict oracle-PPT (`IsOraclePPT encBool`) whenever
`msgLen`, `seed`, `hash`, and `adversary` are uniformly polynomial-time / strict PPT. -/
theorem isOraclePPT_prfNonceToPrfDistinguisher
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool} {adversary : NonceMACForger}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    IsOraclePPT encBool (prfNonceToPrfDistinguisher msgLen seed hash adversary) := by
  have hhandler : IsOraclePPTOn
      (encHandlerCall encLogCaller (encFinite Unit)
        (encList (encPair (encPair encBits encBits) encBits)))
      (encPair encBits (encList (encPair (encPair encBits encBits) encBits)))
      (fun ⟨((n, _), k), request, log⟩ => cwNonceLogHandler msgLen hash n k request log) := by
    dsimp only [cwNonceLogHandler]
    exact IsOraclePPTOn.cond (by fun_prop)
      ((IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop)).map_with (by fun_prop))
      ((ComputableInPolyTime.isOraclePPTOn (Operation := Unit)) (by fun_prop))
  refine isOraclePPT_prfLogDistinguisher hseed hadversary hhandler
    (fun caller query => 2 * caller.1.1 + 4 * query.length + 14) (by fun_prop) ?_
    (by dsimp only; fun_prop)
    (by dsimp only; simp only [List.contains_eq_mem]; fun_prop)
  intro np k request queriedTriples result hresult
  dsimp only [cwNonceLogHandler] at hresult
  have hsplit := length_unframe_add_dropFrame_le request.2
  split at hresult
  · supp_cases hresult with ⟨pad, -, rfl⟩
    exact ⟨by dsimp only; rw [BitString.length_listXor]; omega,
      by enc_len [BitString.length_listXor]⟩
  · supp_cases hresult
    exact ⟨by simp, by enc_len⟩

/-- Running `prfNonceToPrfDistinguisher msgLen seed hash adversary` in `prfRealGame id family`
produces the exact same Boolean distribution as `(carterWegmanNonceMAC ...).sufCmaGame adversary n`.
-/
theorem eval_prfRealGame_prfNonceToPrfDistinguisher
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (adversary : NonceMACForger) (n : ℕ) :
    ProbComp.eval
        (prfRealGame id family (prfNonceToPrfDistinguisher msgLen seed hash adversary) n) =
      ProbComp.eval
        ((carterWegmanNonceMAC msgLen seed hash family hmsgLen hseed hhash hfamily).sufCmaGame
          adversary n) := by
  let M := carterWegmanNonceMAC msgLen seed hash family hmsgLen hseed hhash hfamily
  unfold prfNonceToPrfDistinguisher NonceMACScheme.sufCmaGame
  refine eval_prfRealGame_prfLogDistinguisher family seed (cwNonceLogHandler msgLen hash)
    adversary _ _ (M.signingPairOracle n)
    (fun sk out =>
      let ((msg, nonce), tag) := out.1
      (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
        decide (out.2.map (fun ⟨⟨_, qnonce⟩, _⟩ => qnonce)).Nodup && !out.2.contains out.1 &&
        M.verify sk msg nonce tag) n ?_ ?_
  · intro k prfKey hprfLen request state
    simp only [cwNonceLogHandler, NonceMACScheme.signingPairOracle, M, carterWegmanNonceMAC,
      encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append, hprfLen]
    split <;>
      simp [OracleComp.interpret_map, ProbOracleComp.interpret_query, pmf_norm, Functor.map_map]
  · intro k prfKey hprfLen ⟨⟨⟨msg, nonce⟩, tag⟩, tr⟩
    simp only [M, carterWegmanNonceMAC, encPair_apply, encBits_apply, unframe_frame_append,
      dropFrame_frame_append, hprfLen]
    cases msg.length == msgLen n <;> cases nonce.length == n <;> simp

open scoped List

private def toBitTriple (m n : ℕ)
    (e : (List Bool × List Bool) × List Bool) :
    (BitString m × BitString n) × BitString n :=
  ((BitString.ofList m e.1.1, BitString.ofList n e.1.2), BitString.ofList n e.2)

private def ofBitTriple {m n : ℕ}
    (e : (BitString m × BitString n) × BitString n) :
    (List Bool × List Bool) × List Bool :=
  ((List.ofFn e.1.1, List.ofFn e.1.2), List.ofFn e.2)

private theorem ofBitTriple_toBitTriple {m n : ℕ}
    {e : (List Bool × List Bool) × List Bool}
    (hmsg : e.1.1.length = m) (hnonce : e.1.2.length = n) (htag : e.2.length = n) :
    ofBitTriple (toBitTriple m n e) = e := by
  rcases e with ⟨⟨msg, nonce⟩, tag⟩
  dsimp only [ofBitTriple, toBitTriple]
  rw [BitString.ofFn_ofList hmsg, BitString.ofFn_ofList hnonce, BitString.ofFn_ofList htag]

private def adaptNonceStep (msgLen : ℕ → ℕ) (n : ℕ) (request : Unit × List Bool) :
    StateT (List ((List Bool × List Bool) × List Bool))
      (ProbOracleComp (fun _ : BitString (msgLen n) × BitString n => BitString n)) (List Bool) :=
  fun queriedTriples =>
    let msg := unframe request.2
    let nonce := dropFrame request.2
    if (msg.length == msgLen n) && (nonce.length == n) then
      (fun t =>
        let tag := List.ofFn t
        (tag, ((msg, nonce), tag) :: queriedTriples)) <$>
        ProbOracleComp.query (BitString.ofList (msgLen n) msg, BitString.ofList n nonce)
    else
      pure ([], queriedTriples)

private theorem cwNonceAccept_imp_checkNonceSUF (msgLen : ℕ → ℕ)
    (hash : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k : List Bool) (table : BitString n → BitString n)
    (cand : (List Bool × List Bool) × List Bool)
    (init : List ((List Bool × List Bool) × List Bool))
    (tr : List ((BitString (msgLen n) × BitString n) × BitString n))
    (hsub : tr.map ofBitTriple <+ init.reverse)
    (hcheck : ((cand.1.1.length == msgLen n) && (cand.1.2.length == n) &&
      decide (init.map (fun ((_, x), _) => x)).Nodup && !init.contains cand &&
      (BitString.listXor n
        [hash n k cand.1.1, (randomFunctionOracle n table cand.1.2).take n] == cand.2)) = true) :
    checkNonceSUF
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m)))
      k table tr (toBitTriple (msgLen n) n cand) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    beq_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hmsg, hnonce⟩, hnodup⟩, hnotmem⟩, htag_eq⟩
  have hround : ofBitTriple (toBitTriple (msgLen n) n cand) = cand :=
    ofBitTriple_toBitTriple hmsg hnonce (by rw [← htag_eq, BitString.length_listXor])
  have htr_nodup : (tr.map (fun e => e.1.2)).Nodup := by
    have hsub_map : (tr.map (fun e => e.1.2)).map List.ofFn <+
        (init.map (fun e => e.1.2)).reverse := by
      simpa only [List.map_map, Function.comp_def, ofBitTriple, List.map_reverse] using
        hsub.map (fun e => e.1.2)
    exact .of_map List.ofFn ((List.nodup_reverse.mpr hnodup).sublist hsub_map)
  have htr_notmem : toBitTriple (msgLen n) n cand ∉ tr := fun hmem =>
    hnotmem (List.mem_reverse.mp (hsub.subset (hround ▸ List.mem_map_of_mem hmem)))
  have hverify :
      verify (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m)))
        k (table (toBitTriple (msgLen n) n cand).1.2)
        (toBitTriple (msgLen n) n cand).1.1
        (toBitTriple (msgLen n) n cand).2 = true := by
    simpa only [verify, toBitTriple, BitString.ofFn_ofList hmsg, decide_eq_true_eq,
      randomFunctionOracle, hnonce, ↓reduceIte, BitString.listXor_pair,
      BitString.ofList_take, BitString.ofList_ofFn] using congrArg (BitString.ofList n) htag_eq
  simp only [checkNonceSUF, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨⟨htr_nodup, htr_notmem⟩, hverify⟩

private theorem step_cwNonceLogHandler_randomFunctionOracle
    (msgLen : ℕ → ℕ) (hash : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k : List Bool) (table : BitString n → BitString n)
    (request : Unit × List Bool)
    (init : List ((List Bool × List Bool) × List Bool))
    (tr : List ((BitString (msgLen n) × BitString n) × BitString n))
    (hsub : tr.map ofBitTriple <+ init.reverse) :
    let hashBit := fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))
    let rhs := ProbOracleComp.runWith (nonceFnHandler hashBit k table)
      (adaptNonceStep msgLen n request init) tr
    rhs.map Prod.fst =
      ProbComp.eval
        (OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifFin (fun req =>
            pure (randomFunctionOracle n table req.2)))
          (cwNonceLogHandler msgLen hash n k request init)) ∧
      ∀ reply wstate' tstate', ((reply, wstate'), tstate') ∈ rhs.support →
        tstate'.map ofBitTriple <+ wstate'.reverse := by
  dsimp only [cwNonceLogHandler, adaptNonceStep]
  set msg := unframe request.2
  set nonce := dropFrame request.2
  by_cases hcond : (msg.length == msgLen n && nonce.length == n) = true
  · simp only [hcond, ↓reduceIte, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      nonceFnHandler, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨hmsg, hnonce⟩
    let t := sign
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m)))
      k (table (BitString.ofList n nonce)) (BitString.ofList (msgLen n) msg)
    have htag : List.ofFn t =
        BitString.listXor n [hash n k msg, (randomFunctionOracle n table nonce).take n] := by
      simp only [t, sign, BitString.ofFn_ofList hmsg, randomFunctionOracle, hnonce,
        ↓reduceIte, BitString.listXor_pair, BitString.ofList_take, BitString.ofList_ofFn]
    refine ⟨by simp [pmf_norm, Functor.map_map, OracleComp.interpret_map,
        ProbOracleComp.interpret_query, ← htag, t], ?_⟩
    rintro _ _ _ ⟨⟩
    rw [id_eq, List.map_append, List.map_singleton, List.reverse_cons]
    exact hsub.append
      (by simp [ofBitTriple, BitString.ofFn_ofList hmsg, BitString.ofFn_ofList hnonce])
  · simp only [Bool.eq_false_iff.2 hcond, Bool.false_eq_true, ↓reduceIte,
      ProbOracleComp.runWith_pure, OracleComp.interpret_pure, ProbComp.eval_pure, PMF.pure_map,
      PMF.support_pure, Set.mem_singleton_iff, true_and]
    rintro _ _ _ ⟨⟩
    exact hsub

/-- **Ideal-game bound for `prfNonceToPrfDistinguisher`**, a step of the proof of
[BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274): under
`IsDeltaUniversalHash (ProbComp.eval (seed n)) ... ε`, the ideal-game acceptance probability of
`prfNonceToPrfDistinguisher msgLen seed hash adversary` at parameter `n` is at most
`max ε ((2 : ℝ≥0∞) ^ n)⁻¹`. -/
theorem eval_prfIdealGame_prfNonceToPrfDistinguisher_le
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool} {n : ℕ} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) ε)
    (adversary : NonceMACForger) :
    ProbComp.eval
        (prfIdealGame id id (prfNonceToPrfDistinguisher msgLen seed hash adversary) n) true ≤
      max ε ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  let hashBit : List Bool → BitString (msgLen n) → BitString n :=
    fun k m => BitString.ofList n (hash n k (List.ofFn m))
  unfold prfNonceToPrfDistinguisher
  refine (eval_prfIdealGame_prfLogDistinguisher_le seed (cwNonceLogHandler msgLen hash)
    adversary _ _ n (nonceFnHandler hashBit) (adaptNonceStep msgLen n) []
    (fun tr init => tr.map ofBitTriple <+ init.reverse)
    (fun k table res => checkNonceSUF hashBit k table res.2 (toBitTriple (msgLen n) n res.1.1))
    (List.Sublist.refl [])
    (step_cwNonceLogHandler_randomFunctionOracle msgLen hash n)
    (cwNonceAccept_imp_checkNonceSUF msgLen hash n)).trans ?_
  set adaptProg : ProbOracleComp (fun _ : BitString (msgLen n) × BitString n => BitString n)
      (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) :=
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (adaptNonceStep msgLen n))
      (adversary n [])).run []
  have hsim (k : List Bool) :
      ((PMF.uniformOfFintype (BitString n → BitString n)).bind fun table =>
        (ProbOracleComp.runWith (nonceFnHandler hashBit k table) adaptProg []).bind fun res =>
          PMF.pure
            (checkNonceSUF hashBit k table res.2 (toBitTriple (msgLen n) n res.1.1))) =
      ((ProbOracleComp.runWith nonceSimHandler adaptProg []).bind fun res =>
        (PMF.uniformOfFintype (BitString n → BitString n)).bind fun table =>
          PMF.pure (checkNonceSUF hashBit k (reconstructPadFn hashBit k res.2 table)
            res.2 (toBitTriple (msgLen n) n res.1.1))) := by
    simpa only [reconstructPadFn_nil] using
      probOracleComp_uniform_bind_run_interpret_nonceFnHandler hashBit k adaptProg []
        (fun out tr' padFn =>
          PMF.pure (checkNonceSUF hashBit k padFn tr' (toBitTriple (msgLen n) n out.1)))
        (PMF.pure false)
        (fun out tr' padFn hnot => by simp [checkNonceSUF, hnot])
  simp only [hsim]
  pmf_hoist (ProbOracleComp.runWith nonceSimHandler adaptProg [])
  refine bind_apply_le_on_support _ fun ⟨out, tr⟩ _ => ?_
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    seed_uniform_checkNonceSUF_le hh tr (toBitTriple (msgLen n) n out.1)

/-- **Quantitative SUF-CMA bound for `carterWegmanNonceMAC`** (after [BonehShoup2023],
Theorem 7.10, Section 7.5.1, p. 274, for a hash that is an `ε`-DUF at parameter `n`, with `ε` in
place of the theorem's DUF advantage): at security parameter `n`, the SUF-CMA forgery probability of
any `NonceMACForger` against `carterWegmanNonceMAC` is at most `ε.toReal + (2 ^ n)⁻¹` plus the PRF
distinguishing advantage of `prfNonceToPrfDistinguisher msgLen seed hash adversary`. -/
theorem sufCmaGame_carterWegmanNonceMAC_toReal_le
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    {n : ℕ} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) ε)
    (hε : ε ≠ ⊤) (adversary : NonceMACForger) :
    (ProbComp.eval
      ((carterWegmanNonceMAC msgLen seed hash family hmsgLen hseed hhash hfamily).sufCmaGame
        adversary n) true).toReal ≤
      ε.toReal + ((2 : ℝ) ^ n)⁻¹ +
        (Game.advantage
          (ProbComp.eval
            (prfRealGame id family (prfNonceToPrfDistinguisher msgLen seed hash adversary) n))
          (ProbComp.eval (prfIdealGame id id
            (prfNonceToPrfDistinguisher msgLen seed hash adversary) n)) : ℝ) := by
  rw [← eval_prfRealGame_prfNonceToPrfDistinguisher hmsgLen hseed hhash hfamily adversary n,
    ← Game.coe_succProbability]
  refine (Game.coe_succProbability_le_add_of_advantage_le le_rfl).trans (add_le_add ?_ le_rfl)
  rw [Game.coe_succProbability]
  have hle := (eval_prfIdealGame_prfNonceToPrfDistinguisher_le hh adversary).trans
    (max_le_add_of_nonneg zero_le zero_le)
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using
    ENNReal.toReal_le_add hle hε (by simp)

/-- Statistical-DUF step toward [BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), not the
cited result: if `family` is a `PseudorandomFunction` and `(seed n, hash n)` is an
`(ε n)`-almost-Δ-universal hash family on `BitString (msgLen n)` into `BitString n` with
`Negligible ε`, then `carterWegmanNonceMAC` satisfies `NonceMACScheme.SUFCMA`.

The hash is assumed to be an `ε n`-DUF with negligible `ε`, that is, a statistical DUF
([BonehShoup2023], Definition 7.5, p. 269), whose bound holds against every adversary, efficient or
not. Theorem 7.10 is stated with the notation of Theorem 7.9 (p. 270) and assumes only a
computational DUF: negligible advantage in Attack Game 7.3 (p. 268) for every efficient adversary.
Every statistical DUF is a computational DUF, so this premise is the stronger one and the theorem
does not follow from this step. The computational-DUF theorem is open (#5293). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.sufCma_carterWegmanNonceMAC_of_statisticalDUF
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) (ε n))
    (hε : Negligible ε) :
    (carterWegmanNonceMAC msgLen seed hash family hmsgLen hseed hhash hprf.polyTime).SUFCMA := by
  refine NonceMACScheme.SUFCMA.of_negligible fun adversary hadversary => ?_
  have hdist := hprf.secure (prfNonceToPrfDistinguisher msgLen seed hash adversary)
    (isOraclePPT_prfNonceToPrfDistinguisher hmsgLen hseed hhash hadversary)
  negligible using fun n =>
    sufCmaGame_carterWegmanNonceMAC_toReal_le hmsgLen hseed hhash hprf.polyTime
      (hh n) ENNReal.coe_ne_top adversary

/-- Statistical-DUF step toward [BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), not the
cited result: `NonceMACScheme.EUFCMA` security of `carterWegmanNonceMAC` under the premises of
`PseudorandomFunction.sufCma_carterWegmanNonceMAC_of_statisticalDUF`. The hash is assumed to be an
`ε n`-DUF with negligible `ε`, a statistical DUF ([BonehShoup2023], Definition 7.5, p. 269), where
the theorem assumes only a computational DUF (Attack Game 7.3, p. 268). The computational-DUF
theorem is open (#5293). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.eufCma_carterWegmanNonceMAC_of_statisticalDUF
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) (ε n))
    (hε : Negligible ε) :
    (carterWegmanNonceMAC msgLen seed hash family hmsgLen hseed hhash hprf.polyTime).EUFCMA :=
  (hprf.sufCma_carterWegmanNonceMAC_of_statisticalDUF hmsgLen hseed hhash hh hε).eufCma

/-- Statistical-DUF step toward [BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), not the
cited result: with the nonce implemented as a counter (Section 7.5 and the remark after
Theorem 7.10, p. 274), under the premises of
`PseudorandomFunction.sufCma_carterWegmanNonceMAC_of_statisticalDUF`, a stateful signer that tags
its `j`-th message under the `n`-bit counter nonce `BitString.lowBits n j`, for at most `2 ^ n`
messages, is strongly unforgeable against every oracle-PPT forger
(`NonceMACScheme.CounterSUFCMA`). The reduction is the explicit `NonceMACScheme.counterForger`,
certified by `NonceMACScheme.isOraclePPT_counterForger`. The first counter nonce is `0ⁿ`, the fixed
nonce of `prfOneTimeGame`, so a forgery against that one-time MAC is a counter forgery after one
signing query. The hash is assumed to be an `ε n`-DUF with negligible `ε`, a statistical DUF
([BonehShoup2023], Definition 7.5, p. 269), where the theorem assumes only a computational DUF
(Attack Game 7.3, p. 268). The computational-DUF theorem is open (#5293). -/
theorem
    _root_.Cslib.Crypto.PseudorandomFunction.counterSufCma_carterWegmanNonceMAC_of_statisticalDUF
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) (ε n))
    (hε : Negligible ε) :
    (carterWegmanNonceMAC msgLen seed hash family hmsgLen hseed hhash
      hprf.polyTime).CounterSUFCMA :=
  (hprf.sufCma_carterWegmanNonceMAC_of_statisticalDUF hmsgLen hseed hhash hh hε).counterSufCma

end Nonce

end Cslib.Crypto.Protocols.CarterWegman
