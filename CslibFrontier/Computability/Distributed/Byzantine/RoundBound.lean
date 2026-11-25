/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.Basic
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Fintype.EquivFin

/-!
# The `t + 1` round lower bound for interactive consistency and Byzantine agreement

[Fischer and Lynch][FischerLynch1982] (§§1–3, pp. 183–184; §6, Theorem 5, p. 185) prove that no
deterministic synchronous protocol on `n ≥ t + 2` processes solves *interactive consistency*—where
each correct process outputs a common vector recording every correct process's private input—against
`t` Byzantine faults in `R ≤ t` rounds
(`InteractiveProtocol.not_solvesInteractiveConsistency_of_rounds_le`).

Adapting the same backward crash-peeling argument (`Protocol.not_agreement_and_zero_unanimity`) to
single-bit consensus (`Cslib.Distributed.Byzantine.Protocol`) and combining it with the `n ≤ 3t`
node bound (`CslibFrontier.Computability.Distributed.Byzantine.NodeBound`) rules out Boolean
Byzantine agreement for all `n ≥ 2` and `R ≤ t`
(`Protocol.not_solvesByzantineAgreement_of_rounds_le`). Conversely,
`InteractiveProtocol.toByzantineAgreement` runs an `R`-round Boolean interactive consistency
protocol and takes the strict majority of its output vector to produce an `R`-round Boolean
consensus protocol whenever `2 * t < Fintype.card P`
(`InteractiveProtocol.solvesByzantineAgreement_toByzantineAgreement`). Together with the
`(t + 1)`-round oral messages protocol
(`CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages`), this determines the
exact two-parameter solvability region for Boolean Byzantine agreement: a protocol on `P` solves
Byzantine agreement against `t` faults in `R` rounds if and only if `Fintype.card P ≤ 1` or
`3 * t < Fintype.card P ∧ t + 1 ≤ R` (`exists_solvesByzantineAgreement_iff_full`).

## Proof outline

The shared backward-peeling core (`Protocol.not_agreement_and_zero_unanimity`) shows that on at
least `R + 2` processes, no `R`-round protocol can simultaneously achieve `R`-fault agreement and
distinguish all-`false` from all-`true` in the fault-free (`F = ∅`) run:

* For interactive consistency (`t + 2 ≤ Fintype.card P`, `R ≤ t`, `[Nontrivial V]`), encoding
  `Bool` into two distinct values `v₀ ≠ v₁ : V` and reading a fixed coordinate `p₀ : P` yields a
  Boolean protocol satisfying both hypotheses (`R + 2 ≤ t + 2 ≤ Fintype.card P`), proving Theorem 5
  of [Fischer and Lynch][FischerLynch1982]. (The bound `t + 2 ≤ Fintype.card P` cannot be dropped to
  `2 ≤ Fintype.card P`: on `Fin 2` with `t = 1`, interactive consistency is solvable in `R = 1`
  round because any non-empty fault set leaves at most one nonfaulty process. By contrast, for
  `3 ≤ n ≤ 3t` and `t ≥ 1`, Theorem 3 of [Fischer and Lynch][FischerLynch1982] (§5, p. 185) rules
  out tolerating `t` faults in any number of rounds—at `n = 3`, such as `n = 3, t = 2`, even one
  fault is already impossible, whereas at `n = 4, t = 2` Theorem 4 permits tolerating one fault
  while Theorem 3 rules out tolerating `t = 2` faults.)
* For Boolean Byzantine agreement (`2 ≤ Fintype.card P`, `R ≤ t`), fault-threshold monotonicity
  (`Protocol.SolvesByzantineAgreement.mono`) handles `R + 2 ≤ Fintype.card P`, while
  `Protocol.not_solvesByzantineAgreement` (`NodeBound`) covers `2 ≤ Fintype.card P < R + 2 ≤ 3 * t`.

Even crash-like (silent-omission) schedules suffice. Fix a default message `m₀ : M`. A partial
schedule `(C, alive)` up to round `k` designates at most `k` faulty processes `C` and specifies
which messages faulty processes drop (replacing them by `m₀`) in rounds `< k`; its canonical
extension `extAlive k C alive` silences `C` in all rounds `≥ k` while keeping processes outside `C`
honest. Backward induction on the remaining rounds `d = R - k` proves simultaneously:

1. **Silencing (`P_silence`):** silencing one additional process `p` from round `k` onward does not
   change the round-`R` decision of the remaining correct processes. First silence `p` from round
   `k + 1` onward (`d` remaining rounds), then silence `p`'s round-`(k + 1)` messages one recipient
   `q*` at a time; each single-recipient change alters the state after round `k + 1` only at `q*`,
   which is masked in the remaining `d` rounds by the induction hypothesis with fault set
   `insert p C` of size at most `k + 1`.
2. **Single-process masking (`P_agree`):** two `C`-honest prefixes of length `k` whose states at
   round `k` agree outside `insert p C` reach the same round-`R` decision, obtained by silencing
   `p` from round `k` onward in both runs. Since `(insert p C).card ≤ R + 1 < Fintype.card P`, at
   least one process outside `insert p C` remains correct in both runs.

At `k = 0` (`C = ∅`, `d = R`), flipping the input vector from all-`false` to all-`true` one process
at a time preserves the round-`R` decision of fault-free runs, contradicting fault-free unanimity.

## Main definitions

* `Cslib.Distributed.Byzantine.InteractiveProtocol`: deterministic synchronous protocols for
  interactive consistency over value domain `V`.
* `Cslib.Distributed.Byzantine.InteractiveProtocol.SolvesInteractiveConsistency`: vector agreement
  and per-coordinate validity against at most `t` faults after `R` rounds.
* `Cslib.Distributed.Byzantine.InteractiveProtocol.toByzantineAgreement`: same-round majority
  adapter running an `InteractiveProtocol` over `Bool` to produce a Boolean consensus `Protocol`.

## Main results

* `Cslib.Distributed.Byzantine.InteractiveProtocol.not_solvesInteractiveConsistency_of_rounds_le`:
  no protocol on `n ≥ t + 2` processes over `[Nontrivial V]` solves interactive consistency against
  `t` faults in `R ≤ t` rounds ([Fischer and Lynch][FischerLynch1982], Theorem 5).
* `Cslib.Distributed.Byzantine.InteractiveProtocol.solvesByzantineAgreement_toByzantineAgreement`:
  when `2 * t < Fintype.card P`, an `R`-round interactive consistency protocol over `Bool` yields an
  `R`-round Byzantine agreement protocol.
* `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement_of_rounds_le`: Boolean
  consensus adaptation ruling out `R ≤ t` rounds for all `n ≥ 2`.
* `Cslib.Distributed.Byzantine.exists_solvesByzantineAgreement_iff_full`: complete characterization
  of `(t, R)`-solvability of synchronous Byzantine agreement on finite process sets.

## References

* [M. J. Fischer, N. A. Lynch, *A lower bound for the time to assure interactive
  consistency*][FischerLynch1982]
* [L. Lamport, R. Shostak, M. Pease, *The Byzantine generals problem*][LamportShostakPease1982]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
-/

public section

namespace Cslib.Distributed.Byzantine

namespace Protocol

section CrashPeeling

variable {P S M : Type*} [DecidableEq P] (π : Protocol P S M)

/-- Run of `π` under a binary delivery mask `alive`: when `alive r j i` is `false`, `j` sends the
fixed silent fallback message `m₀` to `i` in round `r + 1`. -/
private def crashState (m₀ : M) (alive : ℕ → P → P → Bool) (x : P → Bool) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (crashState m₀ alive x r i)
      (fun j => if alive r j i then π.send r j (crashState m₀ alive x r j) i else m₀)

/-- Adversary message table realizing `crashState` for any fault set containing all processes that
ever drop a message. -/
private def crashAdv (m₀ : M) (alive : ℕ → P → P → Bool) (x : P → Bool)
    (r : ℕ) (j i : P) : M :=
  if alive r j i then π.send r j (π.crashState m₀ alive x r j) i else m₀

private theorem state_crashAdv_eq (m₀ : M) (F : Finset P) (alive : ℕ → P → P → Bool)
    (x : P → Bool) {R : ℕ} (hF : ∀ r < R, ∀ j ∉ F, ∀ i, alive r j i = true) :
    ∀ r ≤ R, π.state F (π.crashAdv m₀ alive x) x r = π.crashState m₀ alive x r
  | 0, _ => rfl
  | r + 1, hr => by
    have ih := state_crashAdv_eq m₀ F alive x hF r (by omega)
    funext i
    simp only [state, crashState, ih]
    congr 1
    funext j
    by_cases hj : j ∈ F
    · simp only [hj, ↓reduceIte, crashAdv]
    · simp only [hj, ↓reduceIte, hF r (by omega) j hj i]

private theorem crashDecision_agree {R : ℕ}
    (hagr : ∀ F : Finset P, F.card ≤ R → ∀ (adv : ℕ → P → P → M) (x : P → Bool),
      ∀ i ∉ F, ∀ j ∉ F, π.decision F adv x R i = π.decision F adv x R j)
    (m₀ : M) {C : Finset P} (hC : C.card ≤ R) {alive : ℕ → P → P → Bool}
    (halive : ∀ r < R, ∀ j ∉ C, ∀ i, alive r j i = true) (x : P → Bool)
    {i j : P} (hi : i ∉ C) (hj : j ∉ C) :
    π.output i (π.crashState m₀ alive x R i) = π.output j (π.crashState m₀ alive x R j) := by
  have heq := π.state_crashAdv_eq m₀ C alive x halive R le_rfl
  simpa only [decision, heq] using hagr C hC (π.crashAdv m₀ alive x) x i hi j hj

omit [DecidableEq P] in
private theorem crashState_congr_lt (m₀ : M) {alive₁ alive₂ : ℕ → P → P → Bool} (x : P → Bool)
    {k : ℕ} (h : ∀ r < k, alive₁ r = alive₂ r) :
    ∀ r ≤ k, π.crashState m₀ alive₁ x r = π.crashState m₀ alive₂ x r
  | 0, _ => rfl
  | r + 1, hr => by
    have ih := crashState_congr_lt m₀ x h r (by omega)
    simp only [crashState, ih, h r (by omega)]

/-- Canonical continuation from round `k`: keep `alive` before round `k`, and for rounds `≥ k` let
processes outside `C` send honestly while processes in `C` send `m₀`. -/
private def extAlive (k : ℕ) (C : Finset P) (alive : ℕ → P → P → Bool)
    (r : ℕ) (j i : P) : Bool :=
  if r < k then alive r j i else decide (j ∉ C)

/-- Intermediate schedule silencing `p` in round `k + 1` (step `k`) to the recipients in `U` and to
everyone in later rounds, while processes in `C` stay silent from step `k` onward. -/
private def silenceAt (k : ℕ) (C : Finset P) (p : P) (U : Finset P) (alive : ℕ → P → P → Bool)
    (r : ℕ) (j i : P) : Bool :=
  if r < k then alive r j i
  else if r = k then decide (j ∉ C ∧ ¬(j = p ∧ i ∈ U))
  else decide (j ∉ insert p C)

private theorem extAlive_honest {k : ℕ} {C : Finset P} {alive : ℕ → P → P → Bool}
    (h : ∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) :
    ∀ r, ∀ j ∉ C, ∀ i, extAlive k C alive r j i = true := by
  intro r j hj i
  unfold extAlive
  split_ifs with hr
  · exact h r hr j hj i
  · exact decide_eq_true hj

private theorem extAlive_succ_extAlive (k : ℕ) (C : Finset P) (alive : ℕ → P → P → Bool) :
    extAlive (k + 1) C (extAlive k C alive) = extAlive k C alive := by
  funext r j i
  unfold extAlive
  split_ifs with h₁ h₂ <;> first | rfl | omega

private theorem silenceAt_empty (k : ℕ) (C : Finset P) (p : P) (alive : ℕ → P → P → Bool) :
    silenceAt k C p ∅ alive = extAlive (k + 1) (insert p C) (extAlive k C alive) := by
  funext r j i
  unfold silenceAt extAlive
  rcases lt_trichotomy r k with hlt | rfl | hgt
  · simp [hlt, Nat.lt_succ_of_lt hlt]
  · simp
  · simp [Nat.not_lt.mpr hgt.le, hgt.ne', Nat.not_lt.mpr hgt]

private theorem silenceAt_univ [Fintype P] (k : ℕ) (C : Finset P) (p : P)
    (alive : ℕ → P → P → Bool) :
    silenceAt k C p Finset.univ alive = extAlive k (insert p C) alive := by
  funext r j i
  unfold silenceAt extAlive
  split_ifs <;> simp [Finset.mem_insert, not_or, and_comm]

private theorem extAlive_succ_silenceAt (k : ℕ) (C : Finset P) (p : P) (U : Finset P)
    (alive : ℕ → P → P → Bool) :
    extAlive (k + 1) (insert p C) (silenceAt k C p U alive) = silenceAt k C p U alive := by
  funext r j i
  unfold extAlive silenceAt
  split_ifs <;> first | rfl | omega

private theorem silenceAt_honest {k : ℕ} {C : Finset P} {p : P} {U : Finset P}
    {alive : ℕ → P → P → Bool} (h : ∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) :
    ∀ r < k + 1, ∀ j ∉ insert p C, ∀ i, silenceAt k C p U alive r j i = true := by
  intro r hr j hj i
  simp only [Finset.mem_insert, not_or] at hj
  obtain ⟨hjp, hjC⟩ := hj
  unfold silenceAt
  split_ifs with h₁ h₂
  · exact h r h₁ j hjC i
  · exact decide_eq_true ⟨hjC, fun h' => hjp h'.1⟩
  · omega

private theorem crashState_silenceAt_insert_eq_of_ne (m₀ : M) (k : ℕ) (C : Finset P)
    (p qstar : P) (U : Finset P) (alive : ℕ → P → P → Bool) (x : P → Bool)
    {q : P} (hq : q ≠ qstar) :
    π.crashState m₀ (silenceAt k C p (insert qstar U) alive) x (k + 1) q =
      π.crashState m₀ (silenceAt k C p U alive) x (k + 1) q := by
  have hk : π.crashState m₀ (silenceAt k C p (insert qstar U) alive) x k =
      π.crashState m₀ (silenceAt k C p U alive) x k :=
    π.crashState_congr_lt m₀ x (fun r hr => by
      funext j i
      unfold silenceAt
      simp only [hr, ↓reduceIte]) k le_rfl
  simp only [crashState, hk]
  congr 1
  funext j
  have hmem : silenceAt k C p (insert qstar U) alive k j q = silenceAt k C p U alive k j q := by
    unfold silenceAt
    simp only [lt_irrefl, ↓reduceIte, Finset.mem_insert, hq, false_or]
  rw [hmem]

private theorem crashState_extAlive_eq (m₀ : M) (k : ℕ) (C : Finset P)
    (alive : ℕ → P → P → Bool) (x : P → Bool) :
    π.crashState m₀ (extAlive k C alive) x k = π.crashState m₀ alive x k :=
  π.crashState_congr_lt m₀ x (fun r hr => by
    funext j i
    unfold extAlive
    simp only [hr, ↓reduceIte]) k le_rfl

private theorem crashState_extAlive_eq_of_agree (m₀ : M) {k : ℕ} {C : Finset P}
    {alive₁ alive₂ : ℕ → P → P → Bool} {x₁ x₂ : P → Bool}
    (hagree : ∀ q ∉ C, π.crashState m₀ alive₁ x₁ k q = π.crashState m₀ alive₂ x₂ k q) :
    ∀ (d : ℕ), ∀ q ∉ C,
      π.crashState m₀ (extAlive k C alive₁) x₁ (k + d) q =
        π.crashState m₀ (extAlive k C alive₂) x₂ (k + d) q
  | 0, q, hq => by
    rw [Nat.add_zero, π.crashState_extAlive_eq, π.crashState_extAlive_eq, hagree q hq]
  | d + 1, q, hq => by
    rw [← Nat.add_assoc, crashState, crashState]
    congr 1
    · exact crashState_extAlive_eq_of_agree m₀ hagree d q hq
    · funext j
      simp only [extAlive, show ¬(k + d < k) by omega, ↓reduceIte]
      by_cases hj : j ∈ C
      · simp only [hj, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      · simp only [hj, not_false_eq_true, decide_true, ↓reduceIte,
          crashState_extAlive_eq_of_agree m₀ hagree d j hj]

/-- Shared backward-peeling core: on at least `R + 2` processes, no protocol simultaneously achieves
`R`-fault agreement at round `R` and distinguishes all-`false` from all-`true` in the fault-free
(`F = ∅`) run at some process `p₀`. -/
private theorem not_agreement_and_zero_unanimity [Fintype P] {R : ℕ}
    (hn : R + 2 ≤ Fintype.card P)
    (hagr : ∀ F : Finset P, F.card ≤ R → ∀ (adv : ℕ → P → P → M) (x : P → Bool),
      ∀ i ∉ F, ∀ j ∉ F, π.decision F adv x R i = π.decision F adv x R j)
    {p₀ : P} (hval : ∀ adv : ℕ → P → P → M,
      π.decision ∅ adv (fun _ => false) R p₀ = false ∧
        π.decision ∅ adv (fun _ => true) R p₀ = true) : False := by
  let m₀ : M := π.send 0 p₀ (π.init p₀ false) p₀
  -- Single-process silencing (`Sil d`) and single-process state masking (`Agr d`) at `k + d = R`.
  let Sil (d : ℕ) : Prop := ∀ (k : ℕ), k + d = R → ∀ (C : Finset P), C.card ≤ k → ∀ (p : P)
    (alive : ℕ → P → P → Bool) (x : P → Bool),
    (∀ r < k, ∀ j ∉ C, ∀ i, alive r j i = true) →
    ∀ i₁ ∉ C, ∀ i₂ ∉ insert p C,
      π.output i₁ (π.crashState m₀ (extAlive k C alive) x R i₁) =
        π.output i₂ (π.crashState m₀ (extAlive k (insert p C) alive) x R i₂)
  let Agr (d : ℕ) : Prop := ∀ (k : ℕ), k + d = R → ∀ (C : Finset P), C.card ≤ k → ∀ (p : P)
    (alive₁ alive₂ : ℕ → P → P → Bool) (x₁ x₂ : P → Bool),
    (∀ r < k, ∀ j ∉ C, ∀ i, alive₁ r j i = true) →
    (∀ r < k, ∀ j ∉ C, ∀ i, alive₂ r j i = true) →
    (∀ q ∉ insert p C, π.crashState m₀ alive₁ x₁ k q = π.crashState m₀ alive₂ x₂ k q) →
    ∀ i₁ ∉ C, ∀ i₂ ∉ C,
      π.output i₁ (π.crashState m₀ (extAlive k C alive₁) x₁ R i₁) =
        π.output i₂ (π.crashState m₀ (extAlive k C alive₂) x₂ R i₂)
  -- Silencing gives masking: both runs agree with the masked run at some `q₀ ∉ insert p C`.
  have agr_of_sil (d : ℕ) (hsil : Sil d) : Agr d := by
    intro k hk C hC p alive₁ alive₂ x₁ x₂ halive₁ halive₂ hagree i₁ hi₁ i₂ hi₂
    obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ ∉ insert p C := by finset_card
    have hmid := π.crashState_extAlive_eq_of_agree m₀ hagree d q₀ hq₀
    rw [hk] at hmid
    exact (hsil k hk C hC p alive₁ x₁ halive₁ i₁ hi₁ q₀ hq₀).trans
      ((congrArg (π.output q₀) hmid).trans (hsil k hk C hC p alive₂ x₂ halive₂ i₂ hi₂ q₀ hq₀).symm)
  -- Backward induction on `d`.
  have sil (d : ℕ) : Sil d := by
    induction d with
    | zero =>
      intro k hk C hC p alive x halive i₁ hi₁ i₂ hi₂
      rw [Nat.add_zero] at hk
      subst hk
      rw [π.crashState_extAlive_eq m₀ k (insert p C) alive x,
        ← π.crashState_extAlive_eq m₀ k C alive x]
      exact π.crashDecision_agree hagr m₀ hC
        (fun r _ j hj i => extAlive_honest halive r j hj i) x hi₁
        (fun hmem => hi₂ (Finset.mem_insert_of_mem hmem))
    | succ d ih =>
      have ih_agr := agr_of_sil d ih
      intro k hk C hC p alive x halive i₁ hi₁ i₂ hi₂
      have hk' : (k + 1) + d = R := by omega
      -- Step 1: silence `p` from round `k + 1` onward (`silenceAt k C p ∅ alive`).
      have hstep1 := ih (k + 1) hk' C (by omega) p (extAlive k C alive) x
        (fun r _ j hj i => extAlive_honest halive r j hj i) i₁ hi₁ i₂ hi₂
      rw [extAlive_succ_extAlive, ← silenceAt_empty] at hstep1
      -- Step 2: silence `p` in round `k` one recipient at a time across `U : Finset P`.
      have hC' : (insert p C).card ≤ k + 1 := by finset_card
      have hstep2 : ∀ U : Finset P,
          π.output i₂ (π.crashState m₀ (silenceAt k C p ∅ alive) x R i₂) =
            π.output i₂ (π.crashState m₀ (silenceAt k C p U alive) x R i₂) := by
        intro U
        induction U using Finset.induction with
        | empty => rfl
        | insert qstar U hqU ihU =>
          refine ihU.trans ?_
          have hstep := ih_agr (k + 1) hk' (insert p C) hC' qstar
            (silenceAt k C p U alive) (silenceAt k C p (insert qstar U) alive) x x
            (silenceAt_honest halive) (silenceAt_honest halive)
            (fun q hq => (π.crashState_silenceAt_insert_eq_of_ne m₀ k C p qstar U alive x
              (fun heq => hq (by simp [heq]))).symm)
            i₂ hi₂ i₂ hi₂
          simpa only [extAlive_succ_silenceAt] using hstep
      have huniv := hstep2 Finset.univ
      rw [silenceAt_univ] at huniv
      exact hstep1.trans huniv
  -- Apply `Agr R` at `k = 0, C = ∅`, flipping inputs from `false` to `true` one process at a time.
  let aliveTrue : ℕ → P → P → Bool := fun _ _ _ => true
  have hext : extAlive 0 ∅ aliveTrue = aliveTrue := by
    funext r j i
    simp [extAlive, aliveTrue]
  have hall_eq : ∀ U : Finset P,
      π.output p₀ (π.crashState m₀ aliveTrue (fun _ => false) R p₀) =
        π.output p₀ (π.crashState m₀ aliveTrue (fun i => decide (i ∈ U)) R p₀) := by
    intro U
    induction U using Finset.induction with
    | empty =>
      simp only [Finset.notMem_empty, decide_false]
    | insert p U hpU ihU =>
      refine ihU.trans ?_
      have hstep := agr_of_sil R (sil R) 0 (Nat.zero_add R) ∅ (by simp) p aliveTrue aliveTrue
        (fun i => decide (i ∈ U)) (fun i => decide (i ∈ insert p U))
        (fun _ hr => absurd hr (Nat.not_lt_zero _))
        (fun _ hr => absurd hr (Nat.not_lt_zero _))
        (fun q hq => by
          have hqp : q ≠ p := fun heq => hq (by simp [heq])
          simp only [crashState, Finset.mem_insert, hqp, false_or])
        p₀ (Finset.notMem_empty p₀) p₀ (Finset.notMem_empty p₀)
      simpa only [hext] using hstep
  have hstate_eq : ∀ x, π.crashState m₀ aliveTrue x R p₀ =
      π.state ∅ (π.crashAdv m₀ aliveTrue x) x R p₀ := fun x =>
    congrFun (π.state_crashAdv_eq m₀ ∅ aliveTrue x (fun _ _ _ _ _ => rfl) R le_rfl).symm p₀
  have h := hall_eq Finset.univ
  simp only [Finset.mem_univ, decide_true, hstate_eq] at h
  exact Bool.false_ne_true (((hval _).1.symm.trans h).trans (hval _).2)

private theorem not_solvesByzantineAgreement_self [Fintype P] {R : ℕ}
    (hn : R + 2 ≤ Fintype.card P) : ¬ π.SolvesByzantineAgreement R R := by
  intro h
  obtain ⟨p₀, -⟩ : ∃ p₀ : P, p₀ ∈ Finset.univ := by finset_card
  exact π.not_agreement_and_zero_unanimity hn h.agreement (p₀ := p₀) fun adv =>
    ⟨h.validity ∅ (Nat.zero_le R) adv (fun _ => false) false (fun _ _ => rfl) p₀
      (Finset.notMem_empty p₀),
     h.validity ∅ (Nat.zero_le R) adv (fun _ => true) true (fun _ _ => rfl) p₀
      (Finset.notMem_empty p₀)⟩

/-- **The `t + 1` round lower bound for Boolean Byzantine agreement** (Boolean consensus adaptation
of [Fischer and Lynch][FischerLynch1982], §6, Theorem 5, p. 185): no deterministic synchronous
protocol on `n ≥ 2` processes solves Boolean Byzantine agreement against `t` faults in `R ≤ t`
rounds. For the source's interactive consistency formulation, see
`InteractiveProtocol.not_solvesInteractiveConsistency_of_rounds_le`. -/
theorem not_solvesByzantineAgreement_of_rounds_le [Fintype P] {t R : ℕ}
    (h2 : 2 ≤ Fintype.card P) (hR : R ≤ t) :
    ¬ π.SolvesByzantineAgreement t R := by
  intro h
  by_cases hcard : R + 2 ≤ Fintype.card P
  · exact π.not_solvesByzantineAgreement_self hcard (h.mono hR)
  · exact π.not_solvesByzantineAgreement h2 (by omega) h

end CrashPeeling

/-- Reindex a protocol along equivalences of the process, state and message types. -/
private def reindex {P Q S S' M M' : Type*} (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M)
    (π : Protocol Q S M) : Protocol P S' M' where
  init i b := eS.symm (π.init (eP i) b)
  send r i s j := eM.symm (π.send r (eP i) (eS s) (eP j))
  update r i s m := eS.symm (π.update r (eP i) (eS s) (fun j => eM (m (eP.symm j))))
  output i s := π.output (eP i) (eS s)

private theorem reindex_state {P Q S S' M M' : Type*} [DecidableEq P] [DecidableEq Q]
    (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M) (π : Protocol Q S M)
    (F : Finset P) (adv : ℕ → P → P → M') (x : P → Bool) :
    ∀ (r : ℕ) (i : P),
      (reindex eP eS eM π).state F adv x r i =
        eS.symm (π.state (F.map eP.toEmbedding)
          (fun r j i => eM (adv r (eP.symm j) (eP.symm i))) (fun j => x (eP.symm j)) r (eP i))
  | 0, i => by simp only [state, reindex, Equiv.symm_apply_apply]
  | r + 1, i => by
    have ih := reindex_state eP eS eM π F adv x r
    rw [state]
    simp only [ih, state]
    change eS.symm (π.update r (eP i) _ _) = _
    congr 1
    rw [Equiv.apply_symm_apply]
    congr 1
    funext j
    by_cases hj : eP.symm j ∈ F <;> simp [hj, reindex]

private theorem reindex_decision {P Q S S' M M' : Type*} [DecidableEq P] [DecidableEq Q]
    (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M) (π : Protocol Q S M)
    (F : Finset P) (adv : ℕ → P → P → M') (x : P → Bool) (R : ℕ) (i : P) :
    (reindex eP eS eM π).decision F adv x R i =
      π.decision (F.map eP.toEmbedding)
        (fun r j i => eM (adv r (eP.symm j) (eP.symm i))) (fun j => x (eP.symm j)) R (eP i) := by
  rw [decision, reindex_state]
  simp only [reindex, decision, Equiv.apply_symm_apply]

private theorem solvesByzantineAgreement_reindex {P Q S S' M M' : Type*}
    [DecidableEq P] [DecidableEq Q] (eP : P ≃ Q) (eS : S' ≃ S) (eM : M' ≃ M)
    {π : Protocol Q S M} {t R : ℕ} (h : π.SolvesByzantineAgreement t R) :
    (reindex eP eS eM π).SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    have hF' : (F.map eP.toEmbedding).card ≤ t := by simpa only [Finset.card_map] using hF
    have hi' : eP i ∉ F.map eP.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hi
    have hj' : eP j ∉ F.map eP.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hj
    rw [reindex_decision, reindex_decision]
    exact h.agreement _ hF' _ _ (eP i) hi' (eP j) hj'
  validity F hF adv x v hv i hi := by
    have hF' : (F.map eP.toEmbedding).card ≤ t := by simpa only [Finset.card_map] using hF
    have hi' : eP i ∉ F.map eP.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hi
    rw [reindex_decision]
    refine h.validity _ hF' _ _ v (fun j hj => ?_) (eP i) hi'
    exact hv (eP.symm j) (by simpa only [Finset.mem_map_equiv] using hj)

/-- Protocols sharing `send` and `update` whose initial states agree at every process visit
identical states at every round. -/
private theorem state_eq_of_init_eq {P S M : Type*} [DecidableEq P]
    (π₁ π₂ : Protocol P S M) (x₁ x₂ : P → Bool)
    (hsend : π₁.send = π₂.send) (hupd : π₁.update = π₂.update)
    (hinit : ∀ i, π₁.init i (x₁ i) = π₂.init i (x₂ i))
    (F : Finset P) (adv : ℕ → P → P → M) :
    ∀ r, π₁.state F adv x₁ r = π₂.state F adv x₂ r
  | 0 => funext hinit
  | r + 1 => by
    have ih := state_eq_of_init_eq π₁ π₂ x₁ x₂ hsend hupd hinit F adv r
    funext i
    simp only [Protocol.state, ih, hsend, hupd]

end Protocol

/-! ### Interactive consistency and Fischer–Lynch Theorem 5 -/

/-- A deterministic synchronous protocol for *interactive consistency* on the complete graph of
processes `P` over value domain `V` ([Fischer and Lynch][FischerLynch1982], §§1–3, pp. 183–184).

Process `i` starts with private value `inp i : V` in state `init i (inp i)`, exchanges
point-to-point messages via `send` and `update` in synchronous rounds, and outputs a vector
`output i s : P → V` estimating each process's private input. -/
structure InteractiveProtocol (P V State Msg : Type*) where
  /-- Initial state of process `i` with private input value `v : V`. -/
  init : P → V → State
  /-- `send r i s j`: message sent by `i` in state `s` to `j` in round `r + 1`. -/
  send : ℕ → P → State → P → Msg
  /-- `update r i s m`: state of `i` after round `r + 1`, where `m j` came from `j`. -/
  update : ℕ → P → State → (P → Msg) → State
  /-- Output vector `output i s : P → V` computed by process `i`, one coordinate per process. -/
  output : P → State → P → V

namespace InteractiveProtocol

section Model

variable {P V S M : Type*} [DecidableEq P] (π : InteractiveProtocol P V S M)

/-- Local state of process `i` after `r` rounds on private inputs `inp : P → V`, inherited directly
from `Protocol.state` on `π`'s underlying synchronous message-passing transitions. -/
@[expose] def state (F : Finset P) (adv : ℕ → P → P → M) (inp : P → V) : ℕ → P → S :=
  Protocol.state
    { init := fun i _ => π.init i (inp i), send := π.send,
      update := π.update, output := fun _ _ => false }
    F adv (fun _ => false)

/-- Any Boolean `Protocol` sharing `π.send` and `π.update` whose per-process initial state on `x`
matches `π.init · (inp ·)` visits the exact same state `π.state F adv inp r` at every round `r`. -/
private theorem protocol_state_eq (πB : Protocol P S M) (x : P → Bool) (inp : P → V)
    (hsend : πB.send = π.send) (hupd : πB.update = π.update)
    (hinit : ∀ i, πB.init i (x i) = π.init i (inp i))
    (F : Finset P) (adv : ℕ → P → P → M) (r : ℕ) :
    πB.state F adv x r = π.state F adv inp r :=
  Protocol.state_eq_of_init_eq πB
    { init := fun i _ => π.init i (inp i), send := π.send,
      update := π.update, output := fun _ _ => false }
    x (fun _ => false) hsend hupd hinit F adv r

/-- Output vector computed by process `i` after `R` rounds. -/
@[expose] def decision (F : Finset P) (adv : ℕ → P → P → M) (inp : P → V) (R : ℕ) (i : P) :
    P → V :=
  π.output i (π.state F adv inp R i)

/-- `π` assures interactive consistency against at most `t` Byzantine faults in `R` rounds
([Fischer and Lynch][FischerLynch1982], §3, p. 184): whenever at most `t` processes are faulty,
all nonfaulty processes output the same vector (`agreement`), and every nonfaulty process's vector
records every nonfaulty process `r`'s private input `inp r` at coordinate `r` (`validity`). -/
structure SolvesInteractiveConsistency (t R : ℕ) : Prop where
  /-- Agreement: all correct processes output the same vector across all coordinates `r : P`. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (inp : P → V),
    ∀ i ∉ F, ∀ j ∉ F, π.decision F adv inp R i = π.decision F adv inp R j
  /-- Validity: for correct `i` and correct `r`, coordinate `r` of `i`'s output equals `inp r`. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (inp : P → V),
    ∀ i ∉ F, ∀ r ∉ F, π.decision F adv inp R i r = inp r

/-- Tolerating `t` faults implies tolerating `t' ≤ t` faults. -/
theorem SolvesInteractiveConsistency.mono {π : InteractiveProtocol P V S M} {t t' R : ℕ}
    (h : π.SolvesInteractiveConsistency t R) (ht : t' ≤ t) :
    π.SolvesInteractiveConsistency t' R where
  agreement F hF := h.agreement F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)

/-- **Fischer–Lynch `t + 1` round lower bound for interactive consistency**
([Fischer and Lynch][FischerLynch1982], §6, Theorem 5, p. 185): over any nontrivial value domain `V`
(`{0, 1} ⊆ V`), no deterministic synchronous protocol on `n ≥ t + 2` processes assures interactive
consistency against `t` faults in `R ≤ t` rounds.

The bound `t + 2 ≤ Fintype.card P` ensures at least two nonfaulty processes remain outside a
`t`-fault set (Fischer and Lynch invoke the `n ≥ 3t + 1` bound of Pease, Shostak and Lamport for
`t ≥ 1`, §5 Theorem 3, which implies `n ≥ t + 2`, and treat `t = 0` implicitly assuming `n ≥ 2`).
On `Fin 2` with `t = 1` (`n = 2 < t + 2`), interactive consistency is solvable in `R = 1` round;
for `3 ≤ n ≤ 3t` and `t ≥ 1`, §5 Theorem 3 instead rules out tolerating `t` faults in any number of
rounds (at `n = 3`, such as `n = 3, t = 2`, even one fault is impossible, whereas at `n = 4, t = 2`
§5 Theorem 4 permits one fault while §5 Theorem 3 rules out `t = 2` faults). -/
theorem not_solvesInteractiveConsistency_of_rounds_le [Fintype P] [Nontrivial V] {t R : ℕ}
    (hn : t + 2 ≤ Fintype.card P) (hR : R ≤ t) :
    ¬ π.SolvesInteractiveConsistency t R := by
  classical
  intro h
  obtain ⟨v₀, v₁, hv⟩ := exists_pair_ne V
  obtain ⟨p₀, -⟩ : ∃ p₀ : P, p₀ ∈ Finset.univ := by finset_card
  let π₀ : Protocol P S M := {
    init := fun i b => π.init i (if b then v₁ else v₀)
    send := π.send
    update := π.update
    output := fun i s => decide (π.output i s p₀ = v₁)
  }
  have hstate (F : Finset P) (adv : ℕ → P → P → M) (x : P → Bool) :
      π₀.state F adv x R = π.state F adv (fun j => if x j then v₁ else v₀) R :=
    π.protocol_state_eq π₀ x (fun j => if x j then v₁ else v₀) rfl rfl (fun _ => rfl) F adv R
  have hR_solves := h.mono hR
  refine π₀.not_agreement_and_zero_unanimity (R := R) (by omega) ?_ (p₀ := p₀) ?_
  · intro F hF adv x i hi j hj
    simp only [Protocol.decision, hstate, π₀]
    have hvec := hR_solves.agreement F hF adv (fun q => if x q then v₁ else v₀) i hi j hj
    exact congrArg (fun vec => decide (vec p₀ = v₁)) hvec
  · intro adv
    have h₀ := hR_solves.validity ∅ (Nat.zero_le R) adv (fun _ => v₀) p₀
      (Finset.notMem_empty p₀) p₀ (Finset.notMem_empty p₀)
    have h₁ := hR_solves.validity ∅ (Nat.zero_le R) adv (fun _ => v₁) p₀
      (Finset.notMem_empty p₀) p₀ (Finset.notMem_empty p₀)
    simp only [InteractiveProtocol.decision] at h₀ h₁
    simp only [Protocol.decision, hstate, π₀, ↓reduceIte, Bool.false_eq_true, h₀, h₁,
      decide_eq_false hv, decide_true, and_self]

end Model

section Bridge

variable {P S M : Type*} [DecidableEq P] [Fintype P] (π : InteractiveProtocol P Bool S M)

/-- Same-round adapter from Boolean interactive consistency to Boolean Byzantine agreement: runs
the interactive consistency protocol `π` unchanged and outputs `true` iff a strict majority of
coordinates in `π`'s output vector are `true`, producing a Boolean consensus `Protocol`. -/
@[expose] def toByzantineAgreement : Protocol P S M where
  init := π.init
  send := π.send
  update := π.update
  output i s := decide (Fintype.card P < 2 * (Finset.univ.filter fun q => π.output i s q).card)

private theorem toByzantineAgreement_decision (F : Finset P) (adv : ℕ → P → P → M)
    (x : P → Bool) (R : ℕ) (i : P) :
    π.toByzantineAgreement.decision F adv x R i =
      decide (Fintype.card P <
        2 * (Finset.univ.filter fun q => π.decision F adv x R i q).card) := by
  rw [Protocol.decision,
    π.protocol_state_eq π.toByzantineAgreement x x rfl rfl (fun _ => rfl) F adv R]
  rfl

/-- When `2 * t < Fintype.card P`, strict majority over an `R`-round interactive consistency
protocol's output vector solves Boolean Byzantine agreement in the same `R` rounds. -/
theorem solvesByzantineAgreement_toByzantineAgreement {t R : ℕ}
    (ht : 2 * t < Fintype.card P) (h : π.SolvesInteractiveConsistency t R) :
    π.toByzantineAgreement.SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    rw [π.toByzantineAgreement_decision, π.toByzantineAgreement_decision]
    exact congrArg
      (fun vec => decide (Fintype.card P < 2 * (Finset.univ.filter fun q => vec q).card))
      (h.agreement F hF adv x i hi j hj)
  validity F hF adv x v hv i hi := by
    rw [π.toByzantineAgreement_decision]
    set ones := Finset.univ.filter fun q => π.decision F adv x R i q
    cases v with
    | false =>
      have hsub : ones ⊆ F := fun q hq => by
        by_contra hqF
        have htrue : π.decision F adv x R i q = true := (Finset.mem_filter.1 hq).2
        rw [h.validity F hF adv x i hi q hqF, hv q hqF] at htrue
        exact Bool.false_ne_true htrue
      exact decide_eq_false (by finset_card)
    | true =>
      have hsub : Finset.univ \ F ⊆ ones := fun q hq => by
        have hqF : q ∉ F := (Finset.mem_sdiff.1 hq).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ q,
          (h.validity F hF adv x i hi q hqF).trans (hv q hqF)⟩
      exact decide_eq_true (by finset_card)

end Bridge

end InteractiveProtocol

/-- **Complete two-parameter characterization of synchronous Byzantine agreement.**
For a finite process type `P`, fault bound `t`, and fixed decision round `R`, some deterministic
synchronous protocol solves Byzantine agreement on `P` against `t` faults in `R` rounds if and only
if `Fintype.card P ≤ 1` or both `3 * t < Fintype.card P` and `t + 1 ≤ R`:

* `Fintype.card P ≤ 1`: solved in `0` rounds by `Protocol.ownInput`
  (`Protocol.solvesByzantineAgreement_ownInput`).
* `3 * t < Fintype.card P` and `t + 1 ≤ R`: solved by recursive oral messages `om`
  (`solvesByzantineAgreement_om`, [Lamport, Shostak and Pease][LamportShostakPease1982]).
* `2 ≤ Fintype.card P ≤ 3 * t`: excluded by the node bound `Protocol.not_solvesByzantineAgreement`
  ([Fischer, Lynch and Merritt][FischerLynchMerritt1985]).
* `2 ≤ Fintype.card P` and `R ≤ t`: excluded by the Boolean consensus round bound
  `Protocol.not_solvesByzantineAgreement_of_rounds_le` (adapted from
  [Fischer and Lynch][FischerLynch1982], §6, Theorem 5, p. 185). -/
theorem exists_solvesByzantineAgreement_iff_full.{u, v, w} (P : Type u) [Fintype P] [DecidableEq P]
    (t R : ℕ) :
    (∃ (S : Type v) (M : Type w) (π : Protocol P S M), π.SolvesByzantineAgreement t R) ↔
      Fintype.card P ≤ 1 ∨ (3 * t < Fintype.card P ∧ t + 1 ≤ R) := by
  constructor
  · rintro ⟨S, M, π, h⟩
    by_cases h1 : Fintype.card P ≤ 1
    · exact Or.inl h1
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra h3
        exact π.not_solvesByzantineAgreement (by omega) (by omega) h
      · by_contra hR
        exact π.not_solvesByzantineAgreement_of_rounds_le (by omega) (by omega) h
  · rintro (h1 | ⟨h3, hR⟩)
    · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.1 h1
      exact ⟨ULift.{v} Bool, ULift.{w} Unit,
        Protocol.reindex (Equiv.refl P) Equiv.ulift Equiv.ulift (Protocol.ownInput P),
        Protocol.solvesByzantineAgreement_reindex (Equiv.refl P) Equiv.ulift Equiv.ulift
          (Protocol.solvesByzantineAgreement_ownInput t R)⟩
    · let eP := Fintype.equivFin P
      have hcard : 3 * t < Fintype.card (Fin (Fintype.card P)) := by
        simpa only [Fintype.card_fin] using h3
      exact ⟨ULift.{v} (List (Fin (Fintype.card P)) → Bool),
        ULift.{w} (List (Fin (Fintype.card P)) → Bool),
        Protocol.reindex eP Equiv.ulift Equiv.ulift (om (Fin (Fintype.card P)) t),
        Protocol.solvesByzantineAgreement_reindex eP Equiv.ulift Equiv.ulift
          (solvesByzantineAgreement_om hcard hR)⟩

end Cslib.Distributed.Byzantine
