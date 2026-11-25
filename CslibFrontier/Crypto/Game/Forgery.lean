/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind

/-!
# Forgery experiments

A forgery experiment draws a key pair, runs a forger with access to a signing oracle and accepts
when the forger's candidate `(m, σ)` verifies and is fresh. Signatures and MACs differ only in
the parameters: a MAC has no public key (`PK = Unit`) and verifies with the secret key.

The signing oracle is a *policy* over the history of answered queries (`Signer`). Each policy either
signs the next query or refuses it; a refused query is answered with `default` and is not recorded,
as in `ProbOracleComp.runLogWith`. Full, one-time, indexed and counter signing oracles are policies,
so the experiment is written once (`forgeExperiment`). `Signer.restrict` refuses the queries outside
a message space, which is how a word-level game keeps signing queries in the source's message
space. Freshness is a parameter too: `freshMessage`
asks for a message that was never signed (existential unforgeability) and `freshPair` for a pair
that was never answered (strong unforgeability). The evaluation law `eval_forgeExperiment_eq`
writes the experiment's law as an event of the logged run.

## Main definitions

* `Cslib.Crypto.Signer`: a signing policy over the log of answered queries, with
  `Signer.ofSign`, `Signer.restrict`, `Signer.oneTime`, `Signer.indexed` and `Signer.counter`.
* `Cslib.Crypto.forgeExperiment`: the forgery experiment for a key generator, signing policy,
  verifier and freshness test.
* `Cslib.Crypto.oneTimeForgeExperiment`: the fresh-pair game with one signing response.
* `Cslib.Crypto.freshMessage`, `Cslib.Crypto.freshPair`: the existential and strong freshness
  tests.

## Main results

* `Cslib.Crypto.succProbability_forgeExperiment_mono`: a weaker freshness test does not decrease
  the success probability. In particular a forger succeeds at least as often in the strong
  experiment as in the existential one (`succProbability_forgeExperiment_freshMessage_le`), so
  strong unforgeability implies existential unforgeability.
* `Cslib.Crypto.forgeExperiment_freshPair_eq_freshMessage_of_unique`,
  `Cslib.Crypto.forgeExperiment_freshPair_eq_freshMessage`: when every valid pair `(m, σ)` agrees
  with every answer the policy can produce on `m` (in particular, when every policy signature
  verifies and valid signatures are unique), strong and existential forgery are the same experiment.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Attack
  Games 6.1 and 13.1, and Section 13.1.1 (strong unforgeability).
-/

@[expose] public section

namespace Cslib

namespace Crypto

/-- A signing policy: given the secret key, the log of answered queries (in the order answered)
and the next query, either the program that signs it or `none` to refuse it. -/
abbrev Signer (SK M Sig : Type) := SK → List (M × Sig) → M → Option (ProbComp Sig)

namespace Signer

variable {SK M Sig : Type}

/-- The policy that signs every query with `sign`. -/
def ofSign (sign : SK → M → ProbComp Sig) : Signer SK M Sig := fun sk _ m => some (sign sk m)

/-- The restriction of `s` to the queries accepted by `adm`: answer an admissible query as `s`
does and refuse every other one. A refused query is answered with `default` and is not logged, so
under `oneTime` or `counter` it uses up no answer and no counter value. -/
def restrict (s : Signer SK M Sig) (adm : M → Bool) : Signer SK M Sig := fun sk log m =>
  if adm m then s sk log m else none

/-- The one-time restriction of `s`: answer the first query as `s` does, refuse every later
one. -/
def oneTime (s : Signer SK M Sig) : Signer SK M Sig := fun sk log m =>
  if log.isEmpty then s sk log m else none

/-- The indexed policy with capacity `cap`: a query `(u, m)` is signed with `sign sk u m` when
`u < cap` and the index `u` has not been used. -/
def indexed (cap : ℕ) (sign : SK → ℕ → M → ProbComp Sig) : Signer SK (ℕ × M) Sig :=
  fun sk log (u, m) =>
    if u < cap ∧ u ∉ log.map (fun ((v, _), _) => v) then some (sign sk u m) else none

/-- The counter policy with capacity `cap`: the `i`-th answered query is signed with index `i`
and the signature carries `i`; queries after the first `cap` are refused. -/
def counter (cap : ℕ) (sign : SK → ℕ → M → ProbComp Sig) : Signer SK M (ℕ × Sig) :=
  fun sk log m => if log.length < cap then some ((log.length, ·) <$> sign sk log.length m)
    else none

@[simp] theorem ofSign_apply (sign : SK → M → ProbComp Sig) (sk : SK) (log : List (M × Sig))
    (m : M) : ofSign sign sk log m = some (sign sk m) := rfl

@[simp] theorem restrict_apply (s : Signer SK M Sig) (adm : M → Bool) (sk : SK)
    (log : List (M × Sig)) (m : M) :
    s.restrict adm sk log m = if adm m then s sk log m else none := rfl

@[simp] theorem oneTime_nil (s : Signer SK M Sig) (sk : SK) (m : M) :
    s.oneTime sk [] m = s sk [] m := rfl

@[simp] theorem oneTime_cons (s : Signer SK M Sig) (sk : SK) (p : M × Sig)
    (log : List (M × Sig)) (m : M) : s.oneTime sk (p :: log) m = none := rfl

end Signer

open Probability

variable {PK SK M Sig : Type}

/-- The forgery experiment ([BonehShoup2023], Attack Games 6.1 and 13.1): draw `(pk, sk)` from
`keyGen`, run the forger on `pk` against the signing oracle of the policy `signer` at `sk`, and
accept its candidate `(m, σ)` when `verify pk sk m σ` holds and `fresh m σ log` holds for the log
of answered queries. -/
def forgeExperiment [Inhabited Sig] (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool) (fresh : M → Sig → List (M × Sig) → Bool)
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) : Experiment := do
  let (pk, sk) ← keyGen
  let ((m, σ), log) ← (A pk).runLogWith (signer sk)
  return verify pk sk m σ && fresh m σ log

/-- Existential freshness: the message `m` was never signed. -/
def freshMessage [DecidableEq M] (m : M) (_ : Sig) (log : List (M × Sig)) : Bool :=
  decide (m ∉ log.map Prod.fst)

/-- Strong freshness: the pair `(m, σ)` was never an answer of the signing oracle. -/
def freshPair [DecidableEq M] [DecidableEq Sig] (m : M) (σ : Sig) (log : List (M × Sig)) :
    Bool :=
  decide ((m, σ) ∉ log)

/-- The fresh-pair MAC experiment with one signing response ([BonehShoup2023], Attack Game
6.1 restricted as in Section 7.6). The forger chooses its query and saves private state, then
receives the tag before producing its candidate. This works for probabilistic programs and their
distribution semantics. -/
def oneTimeForgeExperiment {P : Type → Type} [Monad P] [DecidableEq M] [DecidableEq Sig]
    {σ : Type} (keyGen : P SK) (sign : SK → M → P Sig) (verify : SK → M → Sig → Bool)
    (choose : P (M × σ)) (guess : σ → Sig → P (M × Sig)) : P Bool := do
  let sk ← keyGen
  let (m, state) ← choose
  let t ← sign sk m
  let (m', t') ← guess state t
  return freshPair m' t' [(m, t)] && verify sk m' t'

/-- A message that was never signed is not part of any answered pair. -/
theorem freshPair_of_freshMessage [DecidableEq M] [DecidableEq Sig] {m : M} {σ : Sig}
    {log : List (M × Sig)} (h : freshMessage m σ log = true) : freshPair m σ log = true := by
  simp only [freshMessage, freshPair, decide_eq_true_eq] at h ⊢
  exact fun hmem => h (List.mem_map_of_mem hmem)

/-- The law of the forgery experiment, as an event of the logged run. -/
theorem eval_forgeExperiment_eq {PK SK M Sig : Type} [Inhabited Sig]
    (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool) (fresh : M → Sig → List (M × Sig) → Bool)
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) :
    ProbComp.eval (forgeExperiment keyGen signer verify fresh A) =
      (ProbComp.eval keyGen).bind fun ⟨pk, sk⟩ =>
        (ProbComp.eval ((A pk).runLogWith (signer sk))).map fun ⟨⟨m, σ⟩, log⟩ =>
          verify pk sk m σ && fresh m σ log := by
  simp only [forgeExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  congr 1

variable [Inhabited Sig] {keyGen : ProbComp (PK × SK)} {signer : Signer SK M Sig}
  {verify : PK → SK → M → Sig → Bool}

/-- **Freshness is monotone**: replacing the freshness test by a weaker one does not decrease the
success probability of any forger. -/
theorem succProbability_forgeExperiment_mono {fresh fresh' : M → Sig → List (M × Sig) → Bool}
    (h : ∀ m σ log, fresh m σ log = true → fresh' m σ log = true)
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) :
    Experiment.succProbability (forgeExperiment keyGen signer verify fresh A) ≤
      Experiment.succProbability (forgeExperiment keyGen signer verify fresh' A) := by
  apply Game.succProbability_mono
  simp only [forgeExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨pk, sk⟩ _ =>
    PMF.bind_apply_mono_on_support _ _ fun ⟨⟨m, σ⟩, log⟩ _ => ?_
  cases hfresh : fresh m σ log <;> simp [hfresh, @h m σ log]

/-- **Strong unforgeability implies existential unforgeability**: a forger succeeds at least as
often in the strong experiment as in the existential one. -/
theorem succProbability_forgeExperiment_freshMessage_le [DecidableEq M] [DecidableEq Sig]
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) :
    Experiment.succProbability (forgeExperiment keyGen signer verify freshMessage A) ≤
      Experiment.succProbability (forgeExperiment keyGen signer verify freshPair A) :=
  succProbability_forgeExperiment_mono (fun _ _ _ => freshPair_of_freshMessage) A

/-- **Unique oracle answers on valid messages**: when every valid pair `(m, σ)` under a supported
key pair agrees with every answer `σ'` that `signer` can produce on `m`, strong and existential
forgery are the same experiment (even when `signer` also answers queries outside the domain of
`verify`). -/
theorem forgeExperiment_freshPair_eq_freshMessage_of_unique [DecidableEq M] [DecidableEq Sig]
    (hunique : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ m σ,
      verify keys.1 keys.2 m σ = true →
      ∀ log program, signer keys.2 log m = some program →
      ∀ σ' ∈ (ProbComp.eval program).support, σ' = σ)
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) :
    ProbComp.eval (forgeExperiment keyGen signer verify freshPair A) =
      ProbComp.eval (forgeExperiment keyGen signer verify freshMessage A) := by
  simp only [forgeExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ hkeys =>
    PMF.bind_congr_on_support _ _ _ fun ⟨⟨m, σ⟩, log⟩ hout => ?_
  have hlog := ProbOracleComp.forall_mem_runLogWith
    (P := fun p => ∀ τ, verify pk sk p.1 τ = true → p.2 = τ)
    (fun log q program h r hr τ hv => hunique _ hkeys q τ hv log program h r hr) (A pk) hout
  cases hv : verify pk sk m σ
  · rfl
  · congr 1
    simp only [Bool.true_and, freshPair, freshMessage, decide_eq_decide]
    refine ⟨fun hpair hmsg => ?_, fun hmsg hpair => hmsg (List.mem_map_of_mem hpair)⟩
    obtain ⟨⟨m', σ'⟩, hmem, rfl⟩ := List.mem_map.mp hmsg
    exact hpair (hlog _ hmem σ hv ▸ hmem)

/-- **Unique signatures**: when every signature that the policy produces verifies and each
message has at most one valid signature, a strong forgery is an existential one, so the two
experiments coincide. -/
theorem forgeExperiment_freshPair_eq_freshMessage [DecidableEq M] [DecidableEq Sig]
    (hsign : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m program,
      signer keys.2 log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify keys.1 keys.2 m σ = true)
    (hunique : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ m σ σ',
      verify keys.1 keys.2 m σ = true → verify keys.1 keys.2 m σ' = true → σ = σ')
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) :
    ProbComp.eval (forgeExperiment keyGen signer verify freshPair A) =
      ProbComp.eval (forgeExperiment keyGen signer verify freshMessage A) :=
  forgeExperiment_freshPair_eq_freshMessage_of_unique
    (fun keys hkeys m _ hv log program hprog _ hσ' =>
      hunique keys hkeys m _ _ (hsign keys hkeys log m program hprog _ hσ') hv) A

end Crypto

end Cslib
