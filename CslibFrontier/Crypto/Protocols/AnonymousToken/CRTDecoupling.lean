/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment.Scheme
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.AnonymousToken.CRTHazard
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Unlinkability
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
public import CslibFrontier.Languages.Probabilistic.UntilBad
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Algebra.CharP.Two

/-!
# Non-black-box `G8 → G8.5` CRT witness-reuse decoupling for VOLE-ACT

This module formalizes the non-black-box CRT witness-reuse decoupling hop (`G8 → G8.5`, where `G8`
follows `[BaumEtAl2026FAEST]` §10.10 Theorem 10.42 and `G8.5` is this library's intermediate hop)
as a standalone concrete finite query-bounded step (`#7068`). Given `qTok` non-adaptive `ck`-fixed
token bundles (`r j` as witness prefix in `r`-first layout, raw-`H5` output `cmult`), `g8Game`
is coupled to `g85Game` via `OracleComp.IdenticalUntilBad` (`crtDecouple_identicalUntilBad`), and
`crtDecouple_advantage_le` bounds their distinguishing advantage by
`qTok * (Adv^hide + Pr[binding]) + g85IvCollisionProb` through `badH5HidingReduction` and
`badH5BindingReduction`. Asymptotic PPT certificates, lazy `H5` simulation, and end-to-end
composition from `G1–G8` remain open under `#7068`.

## Main definitions

* `CRTProofToken`, `G85Setup`, `samplePi`.
* `badH5Key`, `isBadH5Query`, `g8Game`, `g8Handler`, `g85Handler`, `g85HandlerP`, `g85FullRun`,
  `g85Game`, `g85IvCollisionProb`.
* `BadH5HidingState`, `badH5HidingReduction`, `badH5BindingReduction`.

## Main results

* `crtDecouple_identicalUntilBad`: pointwise `IdenticalUntilBad` coupling between `g8Handler` and
  `g85Handler`.
* `crtDecouple_advantage_le`: concrete finite query-bounded `G8 → G8.5` decoupling bound via
  hiding, binding, and `g85IvCollisionProb`.

## References

* [C. Baum et al., *FAEST v3: Algorithm Specifications*][BaumEtAl2026FAEST], §§3.1–3.3 (pp. 13–18),
  §6 (pp. 35–43, Figs. 6.1–6.3), and §10.10 Theorem 10.42 (`G6`–`G11`, pp. 115–121).
* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Initial Issuance (`#issuance`), Spending
  (`#spending`), and Proof status (`#proof-status`).
-/

public section

namespace Cslib.Crypto.AnonymousToken.CRTDecoupling

open Probability
open Probability.PMF (uniformOfFintype uniformOfFintype_apply uniformOfFintype_map_equiv
  uniformOfFintype_prod)
open Cslib.Crypto.AnonymousToken.Unlinkability
open Cslib.Crypto.AnonymousToken.CRTHazard
open scoped ENNReal NNReal

/-- Transcript token bundle exposed to an `H5`-querying distinguisher in the CRT witness-reuse
model (`G8` coupled vs `G8.5` decoupled). -/
structure CRTProofToken (C IV : Type) (nMult lam nMask : ℕ) where
  /-- Note commitment `c = Com.eval ck m r`. -/
  com : C
  /-- Per-proof initialization vector `iv`. -/
  iv : IV
  /-- Verifier mask delta `d`. -/
  d : Fin lam → ZMod 2
  /-- Garbled gate multiplier table `cmult`. -/
  cmult : Fin nMult → Fin nMask → ZMod 2

/-- Configuration for non-black-box CRT witness-reuse decoupling (`G8 → G8.5`, where `G8` follows
[BaumEtAl2026FAEST] §10.10 Theorem 10.42 and `G8.5` is this library's intermediate hop): `qTok`
token events (`0 < qTok`) with non-adaptive `ck`-fixed messages, openings `r j` in `r`-first
layout (`Fin lam → ZMod 2`), IV generator `ivGen`, gate labels `baseLabel`, and `adv` making
adaptive `H5` queries over all `qTok` token bundles delivered together. -/
structure G85Setup
    (CommitKey C Nullifier Context IV : Type) (nMult lam nMask qTok : ℕ) where
  /-- Deterministic-evaluation opening commitment with openings in `Fin lam → ZMod 2`. -/
  Com : OpeningCommitment CommitKey (CommitMsg Nullifier Context) C (Fin lam → ZMod 2)
  /-- Non-adaptive real note message per token event `j : Fin qTok`, fixed by `ck`. -/
  msgs : CommitKey → Fin qTok → CommitMsg Nullifier Context
  /-- Per-token IV distribution. -/
  ivGen : CommitKey → Fin qTok → ProbComp IV
  /-- Base garbled-circuit wire labels `(j, e) ↦ L₀(j, e)`. -/
  baseLabel : CommitKey → Fin qTok → Fin nMult → Fin lam → ZMod 2
  /-- `H5`-adaptive distinguisher receiving all `qTok` token bundles together. -/
  adv : CommitKey → (Fin qTok → CRTProofToken C IV nMult lam nMask) →
    ProbOracleComp (H5Spec IV nMult lam nMask) Bool

variable {CommitKey C Nullifier Context IV : Type} {nMult lam nMask qTok : ℕ}
variable [DecidableEq IV]

/-- Sample a tuple over `Fin n` from independent component distributions. -/
@[expose] def samplePi : (n : ℕ) → {α : Type} → (Fin n → ProbComp α) → ProbComp (Fin n → α)
  | 0, _, _ => pure Fin.elim0
  | n + 1, _, f => do
    let x ← f 0
    let rest ← samplePi n (fun i => f i.succ)
    return Fin.cases x rest

/-- Replacing component `j` of `samplePi` with an independent draw `y ← f j` preserves the
product distribution. -/
private lemma samplePi_replace {n : ℕ} {α : Type}
    (f : Fin n → ProbComp α) (default : Fin n → α) (j : Fin n) :
    ((ProbComp.eval (samplePi n (fun i => if i = j then pure (default i) else f i))).bind
      fun rest => (ProbComp.eval (f j)).map fun y => Function.update rest j y) =
      ProbComp.eval (samplePi n f) := by
  induction n generalizing α with
  | zero => exact Fin.elim0 j
  | succ n' ih =>
    refine Fin.cases ?_ ?_ j
    · simp only [samplePi, Fin.succ_ne_zero, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun x _ =>
        Probability.PMF.bind_congr_on_support _ _ _ fun rest _ => congrArg PMF.pure ?_
      funext i
      exact Fin.cases rfl (fun k => by simp [Function.update, Fin.succ_ne_zero]) i
    · intro j'
      simp only [samplePi, (Fin.succ_ne_zero j').symm, Fin.succ_inj, ↓reduceIte, ProbComp.eval_bind,
        ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun x0 _ => ?_
      rw [← ih (fun i => f i.succ) (fun i => default i.succ) j']
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun rest _ =>
        Probability.PMF.bind_congr_on_support _ _ _ fun y _ => congrArg PMF.pure ?_
      funext i
      refine Fin.cases (by simp [Function.update, (Fin.succ_ne_zero j').symm]) (fun k => ?_) i
      by_cases hk : k = j' <;> simp [Function.update, hk]

/-- Complementary `H5` query key `(iv j, e, baseLabel ck j e + d j + r j)` for token `j` and
gate `e`. -/
@[expose] def badH5Key (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (j : Fin qTok) (e : Fin nMult) : H5Query IV nMult lam :=
  ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩

/-- Boolean check testing whether an `H5` query hits `badH5Key` for some token `j` and gate `e`. -/
@[expose] def isBadH5Query (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (q : H5Query IV nMult lam) : Bool :=
  decide (∃ j : Fin qTok, ∃ e : Fin nMult, q = badH5Key setup ck iv d r j e)

/-- Coupled `G8` game ([BaumEtAl2026FAEST] §10.10, Theorem 10.42) under the witness-reuse CRT mask
option reusing commitment opening `r j` (`r`-first layout, rather than a flag named in
[BaumEtAl2026FAEST] or [VOLEACT2026]): draws `u j`, sets `d j := r j + u j`, and sets `cmult j e`
directly to the raw `H5` value at `badH5Key`. -/
@[expose] noncomputable def g8Game [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) : Game :=
  ProbComp.eval do
    let ck ← setup.Com.keyGen
    let h5 ← ProbComp.uniform (H5Query IV nMult lam → Fin nMask → ZMod 2)
    let r ← samplePi qTok (fun _ => setup.Com.openSample)
    let u ← ProbComp.uniform (Fin qTok → Fin lam → ZMod 2)
    let iv ← samplePi qTok (setup.ivGen ck)
    let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
      let d := r j + u j
      let cmult : Fin nMult → Fin nMask → ZMod 2 :=
        fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + u j⟩
      ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d, cmult⟩
    (setup.adv ck tok).run (fun q => pure (h5 q))

/-- Coupled `G8` `StateT Bool` oracle returning `cmult` on `badH5Key` and `h5` otherwise. -/
noncomputable def g8Handler
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) (bad : Bool) : PMF ((Fin nMask → ZMod 2) × Bool) := by
  classical
  exact if h : ∃ p : Fin qTok × Fin nMult, q = badH5Key setup ck iv d r p.1 p.2 then
    pure (cmult (Classical.choose h).1 (Classical.choose h).2, true)
  else
    pure (h5 q, bad)

/-- Decoupled `G8.5` (this library's intermediate hop between FAEST's `G8` and `G9`) `StateT Bool`
oracle returning `h5 q` uniformly while latching `bad := true` if `isBadH5Query` triggers. -/
noncomputable def g85Handler
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) (bad : Bool) : PMF ((Fin nMask → ZMod 2) × Bool) :=
  pure (h5 q, bad || isBadH5Query setup ck iv d r q)

/-- `ProbComp`-valued variant of `g85Handler` for `ProbOracleComp.runState`. -/
@[expose] def g85HandlerP (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) : StateT Bool ProbComp (Fin nMask → ZMod 2) :=
  fun bad => pure (h5 q, bad || isBadH5Query setup ck iv d r q)

/-- Full decoupled `G8.5` (library intermediate hop) joint execution over
`(output, badH5, ivCollision)`. -/
@[expose] noncomputable def g85FullRun [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) :
    ProbComp (Bool × Bool × Bool) := do
  let ck ← setup.Com.keyGen
  let h5 ← ProbComp.uniform (H5Query IV nMult lam → Fin nMask → ZMod 2)
  let r ← samplePi qTok (fun _ => setup.Com.openSample)
  let d ← ProbComp.uniform (Fin qTok → Fin lam → ZMod 2)
  let iv ← samplePi qTok (setup.ivGen ck)
  let cmult ← ProbComp.uniform (Fin qTok → Fin nMult → Fin nMask → ZMod 2)
  let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
    ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
  let res ← ((setup.adv ck tok).runState (g85HandlerP setup ck iv d r h5)).run false
  let ivColl : Bool := decide (¬ Function.Injective iv)
  return (res.1, res.2, ivColl)

/-- Decoupled `G8.5` (library intermediate hop) distinguishing game: `d j` and `cmult j` are
uniform and independent of `r j` and `h5`. -/
@[expose] noncomputable def g85Game [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) : Game :=
  (ProbComp.eval (g85FullRun setup)).map fun (out, _, _) => out

/-- Probability `Pr[¬ Function.Injective iv]` of an IV collision across the `qTok` proofs in
`g85FullRun` (`0` for counter IVs; replaces a fixed `2 ^ (-λ)` constant bound). -/
noncomputable def g85IvCollisionProb [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok) : ℝ :=
  (((ProbComp.eval (g85FullRun setup)).map fun (_, _, ivColl) => ivColl) true).toReal

/-- `IdenticalUntilBad` connecting `g8Handler` and `g85Handler` lifted to `ProbOracleComp`:
both agree identically while `bad = false` and preserve `bad = true` once triggered. -/
theorem crtDecouple_identicalUntilBad
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (iv : Fin qTok → IV) (d r : Fin qTok → Fin lam → ZMod 2)
    (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) :
    OracleComp.IdenticalUntilBad
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (g8Handler setup ck iv d r cmult h5))
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (g85Handler setup ck iv d r h5))
      (fun bad : Bool => bad = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl n => rfl
    | inr q =>
      simp only [OracleComp.sumHandler, g8Handler, g85Handler, Bool.not_eq_true] at hs hs' ⊢
      have hiff : (∃ j e, q = badH5Key setup ck iv d r j e) ↔
          ∃ p : Fin qTok × Fin nMult, q = badH5Key setup ck iv d r p.1 p.2 :=
        ⟨fun ⟨j, e, hq⟩ => ⟨(j, e), hq⟩, fun ⟨p, hq⟩ => ⟨p.1, p.2, hq⟩⟩
      by_cases hex : ∃ p : Fin qTok × Fin nMult, q = badH5Key setup ck iv d r p.1 p.2 <;>
        simp [isBadH5Query, hiff, hex, hs, hs']
  absorb_first q s hs x hx := by
    cases q with
    | inl n =>
      obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact (Prod.mk.inj heq).2 ▸ hs
    | inr q =>
      simp only [OracleComp.sumHandler, g8Handler] at hx
      split_ifs at hx <;> obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      · rfl
      · exact hs
  absorb_second q s hs x hx := by
    cases q with
    | inl n =>
      obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact (Prod.mk.inj heq).2 ▸ hs
    | inr q =>
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      simp only [hs, Bool.true_or]

/-- Query-logging `StateT` handler answering all `H5` queries from `h5` while recording queries. -/
private noncomputable def h5LogHandler {IV : Type} {nMult lam nMask : ℕ}
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) (qs : List (H5Query IV nMult lam)) :
    PMF ((Fin nMask → ZMod 2) × List (H5Query IV nMult lam)) :=
  pure (h5 q, q :: qs)

/-- `ProbComp`-valued variant of `h5LogHandler` for `ProbOracleComp.runState`. -/
private def h5LogHandlerP {IV : Type} {nMult lam nMask : ℕ}
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (q : H5Query IV nMult lam) :
    StateT (List (H5Query IV nMult lam)) ProbComp (Fin nMask → ZMod 2) :=
  fun qs => pure (h5 q, q :: qs)

/-- State passed across the two stages of `badH5HidingReduction`. -/
structure BadH5HidingState (CommitKey : Type) (qTok : ℕ) where
  /-- Commitment key `ck`. -/
  ck : CommitKey
  /-- Uniformly sampled target token index `j* : Fin qTok`. -/
  jStar : Fin qTok

/-- Shared `BadH5` log-running helper executing `setup.adv` with challenge commitment `cStar` at
target token index `jStar` and logging all `H5` queries. -/
private noncomputable def runBadH5WithChallenge [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    (ck : CommitKey) (jStar : Fin qTok) (cStar : C) :
    ProbComp (IV × (Fin lam → ZMod 2) × List (H5Query IV nMult lam)) := do
  let h5 ← ProbComp.uniform (H5Query IV nMult lam → Fin nMask → ZMod 2)
  let rOthers ← samplePi qTok (fun j => if j = jStar then pure 0 else setup.Com.openSample)
  let d ← ProbComp.uniform (Fin qTok → Fin lam → ZMod 2)
  let iv ← samplePi qTok (setup.ivGen ck)
  let cmult ← ProbComp.uniform (Fin qTok → Fin nMult → Fin nMask → ZMod 2)
  let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
    let c := if j = jStar then cStar else setup.Com.eval ck (setup.msgs ck j) (rOthers j)
    ⟨c, iv j, d j, cmult j⟩
  let res ← ((setup.adv ck tok).runState (h5LogHandlerP h5)).run []
  return (iv jStar, d jStar, res.2)

/-- Explicit `TwoStage` hiding reduction for `BadH5` (concrete query-bounded step, `#7068`,
sampling the full `H5` table rather than lazy oracle simulation): chooses a uniform target token
`j*`, submits `(msgs ck j*, (msgs ck j*).bumpBal)` (`bumpBal ≠ msgs ck j*`) to `Com.toScheme`,
plugs challenge `c*` into token `j*`, and tests whether any logged `H5` query recovers an opening
`r*` satisfying `Com.eval ck (msgs ck j*) r* = c*`. -/
noncomputable def badH5HidingReduction [DecidableEq C] [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    [NeZero qTok] :
    TwoStage CommitKey (MessagePair (CommitMsg Nullifier Context)) C Bool
      (BadH5HidingState CommitKey qTok) where
  choose ck := do
    let jStar ← ProbComp.uniform (Fin qTok)
    let m0 := setup.msgs ck jStar
    return (⟨m0, m0.bumpBal⟩, ⟨ck, jStar⟩)
  guess st cStar := do
    let (ivStar, dStar, qs) ← runBadH5WithChallenge setup st.ck st.jStar cStar
    let m0 := setup.msgs st.ck st.jStar
    return qs.any fun q =>
      decide (q.iv = ivStar) &&
        decide (setup.Com.eval st.ck m0 (q.label + setup.baseLabel st.ck st.jStar q.gate +
          dStar) = cStar)

/-- Explicit commitment-binding reduction (concrete step, `#7068`, sampling the full `H5` table)
extracting a `BindingCollision` between `msgs ck j*` and `(msgs ck j*).bumpBal` whenever
`badH5HidingReduction` hits under `b_hide = true`. -/
noncomputable def badH5BindingReduction [DecidableEq C] [Fintype IV]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    [NeZero qTok] (ck : CommitKey) :
    ProbComp (Commitment.BindingCollision (CommitMsg Nullifier Context) C (Fin lam → ZMod 2)) := do
  let jStar ← ProbComp.uniform (Fin qTok)
  let rDummy ← setup.Com.openSample
  let m0 := setup.msgs ck jStar
  let cStar := setup.Com.eval ck m0.bumpBal rDummy
  let (ivStar, dStar, qs) ← runBadH5WithChallenge setup ck jStar cStar
  let found? := qs.find? fun q =>
    decide (q.iv = ivStar) &&
      decide (setup.Com.eval ck m0 (q.label + setup.baseLabel ck jStar q.gate + dStar) = cStar)
  match found? with
  | some q =>
    return {
      commitment := cStar
      msg₀ := m0
      opening₀ := q.label + setup.baseLabel ck jStar q.gate + dStar
      msg₁ := m0.bumpBal
      opening₁ := rDummy
    }
  | none =>
    return {
      commitment := cStar
      msg₀ := m0
      opening₀ := 0
      msg₁ := m0
      opening₁ := 0
    }

/-- Non-black-box CRT witness-reuse decoupling step (`G8 → G8.5`), original to this library as a
concrete finite query-bounded bound (`#7068`, where `G8` follows `[BaumEtAl2026FAEST]` §10.10
Theorem 10.42 and `G8.5` is this library's intermediate hop): assuming `0 < qTok` (`NeZero qTok`),
any `H5`-adaptive distinguisher over the `qTok` non-adaptive `ck`-fixed token bundles (`r j` as
witness prefix in `r`-first layout, raw-`H5` `cmult`) has advantage between coupled `g8Game` and
decoupled `g85Game` at most `qTok * (Adv^hide + Pr[binding]) + g85IvCollisionProb` via
`badH5HidingReduction` and `badH5BindingReduction` (`g85IvCollisionProb` tracks IV injectivity
instead of a fixed `2 ^ (-λ)` term; asymptotic certificates and composition with `G1–G8` remain
open under `#7068`). -/
theorem crtDecouple_advantage_le [DecidableEq C] [Fintype IV]
    [DecidableEq Nullifier] [DecidableEq Context]
    (setup : G85Setup CommitKey C Nullifier Context IV nMult lam nMask qTok)
    [NeZero qTok] :
    (Game.advantage (g8Game setup) (g85Game setup) : ℝ) ≤
      (qTok : ℝ) *
        ((Experiment.advantage
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false)
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) : ℝ) +
          (Experiment.succProbability
            (setup.Com.toScheme.bindingExperiment (badH5BindingReduction setup)) : ℝ)) +
        g85IvCollisionProb setup := by
  let logRun : CommitKey → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
      (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → IV) →
      (Fin qTok → Fin nMult → Fin nMask → ZMod 2) →
      PMF (Bool × List (H5Query IV nMult lam)) := fun ck h5 r d iv cmult =>
    let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
      ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
    ProbOracleComp.runWith (h5LogHandler h5) (setup.adv ck tok) []
  let badRun : CommitKey → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
      (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → IV) →
      (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF (Bool × Bool) :=
    fun ck h5 r d iv cmult =>
      let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
        ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
      ProbOracleComp.runWith (g85Handler setup ck iv d r h5) (setup.adv ck tok) false
  have hlog_to_bad (ck : CommitKey) (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
      (r d : Fin qTok → Fin lam → ZMod 2) (iv : Fin qTok → IV)
      (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2) :
      (logRun ck h5 r d iv cmult).map (fun (a, qs) => (a, qs.any (isBadH5Query setup ck iv d r))) =
        badRun ck h5 r d iv cmult := by
    refine ProbOracleComp.runWith_map_state (h5LogHandler h5) (g85Handler setup ck iv d r h5)
      (fun qs => qs.any (isBadH5Query setup ck iv d r))
      (fun q qs => by simp [h5LogHandler, g85Handler, Bool.or_comm]) _ []
  let outerSetup {α : Type} :
      (CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → PMF α) → PMF α := fun f =>
    (ProbComp.eval setup.Com.keyGen).bind fun ck =>
    (ProbComp.eval (samplePi qTok (fun _ => setup.Com.openSample))).bind fun r =>
    (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
    (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv => f ck r d iv
  let fullSetup {α : Type} :
      (CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
        (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF α) → PMF α := fun f =>
    outerSetup fun ck r d iv =>
      (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
      (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
        f ck r d iv h5 cmult
  have hbindSum : ∀ {α : Type} (p : PMF α) (f g h : α → ℝ≥0∞),
      (∀ x, f x ≤ g x + h x) →
      (∑' x, p x * f x) ≤ (∑' x, p x * g x) + (∑' x, p x * h x) := by
    intro α p f g h hle
    rw [← tsum_add]
    exact tsum_le_tsum fun x => (mul_add (p x) (g x) (h x)).symm ▸
      mul_le_mul_of_nonneg_left (hle x) zero_le
  have hfullCongr : ∀ {α : Type} (f g :
      CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
        (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF α),
      (∀ ck r d iv h5 cmult, f ck r d iv h5 cmult = g ck r d iv h5 cmult) →
      fullSetup f = fullSetup g := fun f g h =>
    Probability.PMF.bind_congr_on_support _ _ _ fun ck _ =>
      Probability.PMF.bind_congr_on_support _ _ _ fun r _ =>
        Probability.PMF.bind_congr_on_support _ _ _ fun d _ =>
          Probability.PMF.bind_congr_on_support _ _ _ fun iv _ =>
            Probability.PMF.bind_congr_on_support _ _ _ fun h5 _ =>
              Probability.PMF.bind_congr_on_support _ _ _ fun cmult _ => h ck r d iv h5 cmult
  have hfullMap : ∀ {α β : Type} (f :
      CommitKey → (Fin qTok → Fin lam → ZMod 2) → (Fin qTok → Fin lam → ZMod 2) →
        (Fin qTok → IV) → (H5Query IV nMult lam → Fin nMask → ZMod 2) →
        (Fin qTok → Fin nMult → Fin nMask → ZMod 2) → PMF α) (g : α → β),
      (fullSetup f).map g =
        fullSetup fun ck r d iv h5 cmult => (f ck r d iv h5 cmult).map g := by
    intro α β f g
    simp only [fullSetup, outerSetup, PMF.map_bind]
  have hvec (v : Fin lam → ZMod 2) : v + v = 0 :=
    funext fun k => CharTwo.add_self_eq_zero (v k)
  have hg8_eq :
      g8Game setup =
        fullSetup fun ck r d iv h5 _ =>
          let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
            ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
              fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩⟩
          ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q))) := by
    simp only [fullSetup, outerSetup, g8Game, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun ck _ => ?_
    rw [PMF.bind_comm]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun r _ => ?_
    let eAdd : (Fin qTok → Fin lam → ZMod 2) ≃ (Fin qTok → Fin lam → ZMod 2) :=
      { toFun := fun u j => r j + u j
        invFun := fun d j => d j + r j
        left_inv := fun u => funext fun j => by
          dsimp only
          rw [add_comm (r j) (u j), add_assoc, hvec, add_zero]
        right_inv := fun d => funext fun j => by
          dsimp only
          rw [add_comm (d j) (r j), ← add_assoc, hvec, zero_add] }
    have hshift :
        (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind (fun u =>
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, r j + u j,
                  fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + u j⟩⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q)))) =
        (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind (fun d =>
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q)))) := by
      conv_rhs => rw [← uniformOfFintype_map_equiv eAdd, PMF.bind_map]
      simp only [Function.comp_def, eAdd, Equiv.coe_fn_mk]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun u _ =>
        Probability.PMF.bind_congr_on_support _ _ _ fun h5 _ =>
          Probability.PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
      have hlab : ∀ j e,
          setup.baseLabel ck j e + (r j + u j) + r j = setup.baseLabel ck j e + u j :=
        fun j e => by
          rw [add_assoc (setup.baseLabel ck j e), add_comm (r j) (u j), add_assoc,
            hvec, add_zero]
      simp_rw [hlab]
    rw [PMF.bind_comm]
    rw [hshift]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun d _ => ?_
    rw [PMF.bind_comm]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun iv _ =>
      Probability.PMF.bind_congr_on_support _ _ _ fun h5 _ => ?_
    exact (PMF.bind_const _ _).symm
  have hdec_point :
      ∀ ck r d iv,
        let P : Game :=
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j,
                  fun e => h5 ⟨iv j, e, setup.baseLabel ck j e + d j + r j⟩⟩
              ProbComp.eval ((setup.adv ck tok).run (fun q => pure (h5 q)))
        let Q : Game :=
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (badRun ck h5 r d iv cmult).map Prod.fst
        let B : ℝ≥0∞ :=
          if Function.Injective iv then
            ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
              (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
                (badRun ck h5 r d iv cmult).map Prod.snd) true
          else 1
        P true ≤ Q true + B ∧ Q true ≤ P true + B := by
    intro ck r d iv P Q B
    by_cases hInj : Function.Injective iv
    · simp only [B, hInj, ↓reduceIte]
      have hphiInj :
          Function.Injective (fun p : Fin qTok × Fin nMult =>
            badH5Key setup ck iv d r p.1 p.2) := by
        intro p₁ p₂ hp
        have hiv : iv p₁.1 = iv p₂.1 := congrArg H5Query.iv hp
        have hgate : p₁.2 = p₂.2 := congrArg H5Query.gate hp
        exact Prod.ext (hInj hiv) hgate
      let φ : Fin qTok × Fin nMult → H5Query IV nMult lam :=
        fun p => badH5Key setup ck iv d r p.1 p.2
      classical
      have hcm (cmult : Fin qTok → Fin nMult → Fin nMask → ZMod 2)
          (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) :
          (fun j e =>
            if h : ∃ p, φ p = φ (j, e) then cmult (Classical.choose h).1 (Classical.choose h).2
              else h5 (φ (j, e))) = cmult := by
        funext j e
        have hex : ∃ p, φ p = φ (j, e) := ⟨(j, e), rfl⟩
        simp [hex, hphiInj (Classical.choose_spec hex)]
      let eSwap :
          ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2)) ≃
            ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2)) :=
        let swapFn : (Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
            (H5Query IV nMult lam → Fin nMask → ZMod 2) →
            (Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2) :=
          fun ⟨cmult, h5⟩ =>
            (fun j e => h5 (φ (j, e)),
              fun q => if h : ∃ p, φ p = q then
                cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q)
        have hinv : Function.Involutive swapFn := fun ⟨cmult, h5⟩ => by
          refine Prod.ext (hcm cmult h5) (funext fun q => ?_)
          by_cases hq : ∃ p, φ p = q
          · rcases hq with ⟨p, rfl⟩
            have hex : ∃ p', φ p' = φ p := ⟨p, rfl⟩
            simp only [swapFn, hex, ↓reduceDIte, hphiInj (Classical.choose_spec hex)]
          · simp [swapFn, hq]
        ⟨swapFn, swapFn, hinv, hinv⟩
      have hP_eq :
          P = (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
              (ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5) (setup.adv ck tok)
                false).map Prod.fst := by
        have hprod (f : (Fin qTok → Fin nMult → Fin nMask → ZMod 2) →
            (H5Query IV nMult lam → Fin nMask → ZMod 2) → PMF Bool) :
            (uniformOfFintype ((Fin qTok → Fin nMult → Fin nMask → ZMod 2) ×
              (H5Query IV nMult lam → Fin nMask → ZMod 2))).bind (fun ⟨c, h⟩ => f c h) =
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun c =>
              (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind (f c) := by
          rw [← uniformOfFintype_prod, PMF.bind_bind]
          simp only [PMF.bind_map, Function.comp_def]
        dsimp only [P]
        rw [PMF.bind_comm, ← hprod]
        conv_lhs => rw [← uniformOfFintype_map_equiv eSwap, PMF.bind_map]
        conv_rhs => rw [PMF.bind_comm, ← hprod]
        simp only [Function.comp_def, eSwap, Equiv.coe_fn_mk]
        refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨cmult, h5⟩ _ => ?_
        let ans (q : H5Query IV nMult lam) : Fin nMask → ZMod 2 :=
          if h : ∃ p, φ p = q then cmult (Classical.choose h).1 (Classical.choose h).2 else h5 q
        have hg8_ans (q : H5Query IV nMult lam) (s : Bool) :
            ((g8Handler setup ck iv d r cmult h5 q s).map fun (a, _) => (a, ())) =
            (PMF.pure (ans q)).map (·, ()) := by
          simp only [g8Handler, ans, PMF.pure_map]
          by_cases h2 : ∃ p, φ p = q
          · rcases h2 with ⟨p, rfl⟩
            have h1 : ∃ p', φ p = φ p' := ⟨p, rfl⟩
            have h2' : ∃ p', φ p' = φ p := ⟨p, rfl⟩
            have hc1 : Classical.choose h1 = p := hphiInj (Classical.choose_spec h1).symm
            have hc2 : Classical.choose h2' = p := hphiInj (Classical.choose_spec h2')
            dsimp only [φ] at h1 h2' hc1 hc2 ⊢
            simp [h1, h2', hc1, hc2]
          · have h1 : ¬ ∃ p, q = φ p := fun ⟨p, hp⟩ => h2 ⟨p, hp.symm⟩
            dsimp only [φ] at h1 h2 ⊢
            simp [h1, h2]
        have hunit := congrArg (PMF.map Prod.fst) (ProbOracleComp.runWith_map_state
          (g8Handler setup ck iv d r cmult h5)
          (fun q (state : Unit) => (PMF.pure (ans q)).map (·, state))
          (fun _ => ()) hg8_ans
          (setup.adv ck fun j => ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩)
          false)
        simp only [PMF.map_comp, Function.comp_def] at hunit
        rw [hunit, ProbOracleComp.runWith_readOnly (fun q (_ : Unit) => PMF.pure (ans q)),
          PMF.map_comp, show (Prod.fst ∘ fun x : Bool => (x, ())) = id from rfl, PMF.map_id,
          OracleComp.evalWith_eq_interpret, ProbOracleComp.eval_run]
        dsimp only [ans]
        congr 2
        funext j
        congr 1
        exact congrFun (hcm cmult h5) j
      have hstep_le : ∀ h5 cmult,
          let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
            ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩
          let firstRun := ProbOracleComp.runWith (g8Handler setup ck iv d r cmult h5)
            (setup.adv ck tok) false
          let secondRun := ProbOracleComp.runWith (g85Handler setup ck iv d r h5)
            (setup.adv ck tok) false
          (firstRun.map Prod.fst) true ≤
            (secondRun.map Prod.fst) true + (secondRun.map Prod.snd) true ∧
          (secondRun.map Prod.fst) true ≤
            (firstRun.map Prod.fst) true + (secondRun.map Prod.snd) true := by
        intro h5 cmult tok firstRun secondRun
        have hub := crtDecouple_identicalUntilBad setup ck iv d r cmult h5
        have h1 := hub.bind_apply_le (setup.adv ck tok) false
          (fun x => PMF.pure x.1) true
        have h2 := hub.symm.bind_apply_le (setup.adv ck tok) false
          (fun x => PMF.pure x.1) true
        rw [hub.bad_eq (setup.adv ck tok) false] at h1
        simp_rw [← ProbOracleComp.runWith_eq_run_interpret] at h1 h2
        have hbadSet :
            (ProbOracleComp.runWith (g85Handler setup ck iv d r h5)
              (setup.adv ck tok) false).toOuterMeasure {x | x.2 = true} =
              (secondRun.map Prod.snd) true := by
          rw [PMF.toOuterMeasure_apply, PMF.map_apply]
          refine tsum_congr fun x => ?_
          cases hx : x.2 <;> simp [hx, secondRun]
        rw [hbadSet] at h1 h2
        exact ⟨by simpa [firstRun, secondRun, PMF.map, Function.comp_def] using h1,
          by simpa [firstRun, secondRun, PMF.map, Function.comp_def] using h2⟩
      rw [hP_eq]
      constructor
      · simp only [Q, badRun, PMF.bind_apply]
        exact hbindSum _ _ _ _ fun h5 => hbindSum _ _ _ _ fun cmult => (hstep_le h5 cmult).1
      · simp only [Q, badRun, PMF.bind_apply]
        exact hbindSum _ _ _ _ fun h5 => hbindSum _ _ _ _ fun cmult => (hstep_le h5 cmult).2
    · simp only [B, hInj, ↓reduceIte]
      exact ⟨le_trans (PMF.coe_le_one _ _) le_add_self,
        le_trans (PMF.coe_le_one _ _) le_add_self⟩
  let badFullProb : ℝ≥0∞ := ((ProbComp.eval (g85FullRun setup)).map fun (_, bad, _) => bad) true
  let ivFullProb : ℝ≥0∞ :=
    ((ProbComp.eval (g85FullRun setup)).map fun (_, _, ivColl) => ivColl) true
  have hg85_reorder :
      ProbComp.eval (g85FullRun setup) =
        fullSetup fun ck r d iv h5 cmult =>
          (badRun ck h5 r d iv cmult).map fun res =>
            (res.1, res.2, decide (¬ Function.Injective iv)) := by
    simp only [fullSetup, outerSetup, g85FullRun, badRun, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun ck _ => ?_
    rw [PMF.bind_comm]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun r _ => ?_
    rw [PMF.bind_comm]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun d _ => ?_
    rw [PMF.bind_comm]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
    refine Probability.PMF.bind_congr_on_support _ _ _ fun h5 _ =>
      Probability.PMF.bind_congr_on_support _ _ _ fun cmult _ => ?_
    rw [ProbOracleComp.eval_runState]
    have hg85 : (fun q state => ProbComp.eval (g85HandlerP setup ck iv d r h5 q state)) =
        g85Handler setup ck iv d r h5 :=
      funext fun q => funext fun s => by simp [g85HandlerP, g85Handler]
    rw [hg85]
    simp only [PMF.map, Function.comp_def]
  have hdec_global :
      g8Game setup true ≤ g85Game setup true + (badFullProb + ivFullProb) ∧
      g85Game setup true ≤ g8Game setup true + (badFullProb + ivFullProb) := by
    have hbad_le : ∀ ck r d iv,
        (if Function.Injective iv then
          ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (badRun ck h5 r d iv cmult).map Prod.snd) true
        else (1 : ℝ≥0∞)) ≤
          ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (badRun ck h5 r d iv cmult).map Prod.snd) true +
            (PMF.pure (decide (¬ Function.Injective iv))) true := by
      intro ck r d iv
      by_cases hInj : Function.Injective iv
      · simp [hInj]
      · simp [hInj, self_le_add_left]
    have hg85_fst :
        g85Game setup true =
          (fullSetup fun ck r d iv h5 cmult => (badRun ck h5 r d iv cmult).map Prod.fst) true := by
      rw [g85Game, hg85_reorder, hfullMap]
      refine congrArg (fun p : PMF Bool => p true) (hfullCongr _ _ fun ck r d iv h5 cmult => ?_)
      rw [PMF.map_comp]; rfl
    have hsum_bad :
        badFullProb + ivFullProb =
          (fullSetup fun ck r d iv h5 cmult => (badRun ck h5 r d iv cmult).map Prod.snd) true +
          (outerSetup fun _ _ _ iv => PMF.pure (decide (¬ Function.Injective iv))) true := by
      simp only [badFullProb, ivFullProb, hg85_reorder]
      congr 1
      · rw [hfullMap]
        refine congrArg (fun p : PMF Bool => p true) (hfullCongr _ _ fun _ _ _ _ _ _ => ?_)
        rw [PMF.map_comp]; rfl
      · simp only [fullSetup, outerSetup, PMF.map_bind]
        refine congrArg (fun p : PMF Bool => p true) ?_
        refine Probability.PMF.bind_congr_on_support _ _ _ fun ck _ =>
          Probability.PMF.bind_congr_on_support _ _ _ fun r _ =>
            Probability.PMF.bind_congr_on_support _ _ _ fun d _ =>
              Probability.PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
        simp [PMF.map, Function.comp_def, PMF.bind_const]
    rw [hg8_eq, hg85_fst, hsum_bad]
    constructor
    · simp only [fullSetup, outerSetup, PMF.bind_apply]
      refine le_trans (hbindSum _ _ _ _ fun ck =>
        hbindSum _ _ _ _ fun r =>
        hbindSum _ _ _ _ fun d =>
        hbindSum _ _ _ _ fun iv =>
          le_trans (hdec_point ck r d iv).1 (add_le_add (le_refl _) (hbad_le ck r d iv))) ?_
      simp only [mul_add, tsum_add, PMF.bind_apply]
      exact le_refl _
    · simp only [fullSetup, outerSetup, PMF.bind_apply]
      refine le_trans (hbindSum _ _ _ _ fun ck =>
        hbindSum _ _ _ _ fun r =>
        hbindSum _ _ _ _ fun d =>
        hbindSum _ _ _ _ fun iv =>
          le_trans (hdec_point ck r d iv).2 (add_le_add (le_refl _) (hbad_le ck r d iv))) ?_
      simp only [mul_add, tsum_add, PMF.bind_apply]
      exact le_refl _
  have hbad_hide :
      badFullProb ≤ (qTok : ℝ≥0∞) *
        (ProbComp.eval
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) true) := by
    have hq_pos : (qTok : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast NeZero.ne qTok
    have hq_ne_top : (qTok : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top qTok
    let hitAt (ck : CommitKey) (r d : Fin qTok → Fin lam → ZMod 2) (iv : Fin qTok → IV)
        (qs : List (H5Query IV nMult lam)) (jStar : Fin qTok) : Bool :=
      qs.any fun q =>
        decide (q.iv = iv jStar) &&
          decide (setup.Com.eval ck (setup.msgs ck jStar)
            (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
            setup.Com.eval ck (setup.msgs ck jStar) (r jStar))
    have hhide_re :
        ProbComp.eval (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) =
          fullSetup fun ck r d iv h5 cmult =>
            (logRun ck h5 r d iv cmult).bind fun res =>
              (uniformOfFintype (Fin qTok)).map (hitAt ck r d iv res.2) := by
      simp only [fullSetup, outerSetup, Commitment.Scheme.eval_hidingExperiment, Game.withSetup,
        eval_lrExperiment, badH5HidingReduction, runBadH5WithChallenge,
        OpeningCommitment.toScheme, Commitment.Scheme.commitment, MessagePair.select_false,
        ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_pure,
        PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, ite_true, logRun]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun ck _ => ?_
      have hcomm1 (jStar : Fin qTok) :
          ((ProbComp.eval setup.Com.openSample).bind fun rStar =>
            (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (ProbComp.eval (samplePi qTok (fun j => if j = jStar then pure (0 : Fin lam → ZMod 2)
              else setup.Com.openSample))).bind fun rOthers =>
            (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              let tok : Fin qTok → CRTProofToken C IV nMult lam nMask := fun j =>
                ⟨if j = jStar then setup.Com.eval ck (setup.msgs ck jStar) rStar
                  else setup.Com.eval ck (setup.msgs ck j) (rOthers j), iv j, d j, cmult j⟩
              (ProbComp.eval (((setup.adv ck tok).runState (h5LogHandlerP h5)).run [])).bind
                fun res =>
                  PMF.pure (res.2.any fun q =>
                    decide (q.iv = iv jStar) &&
                      decide (setup.Com.eval ck (setup.msgs ck jStar)
                        (q.label + setup.baseLabel ck jStar q.gate + d jStar) =
                        setup.Com.eval ck (setup.msgs ck jStar) rStar))) =
          ((ProbComp.eval (samplePi qTok (fun _ => setup.Com.openSample))).bind fun r =>
            (uniformOfFintype (Fin qTok → Fin lam → ZMod 2)).bind fun d =>
            (ProbComp.eval (samplePi qTok (setup.ivGen ck))).bind fun iv =>
            (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin qTok → Fin nMult → Fin nMask → ZMod 2)).bind fun cmult =>
              (ProbOracleComp.runWith (h5LogHandler h5) (setup.adv ck fun j =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (r j), iv j, d j, cmult j⟩) []).bind
                fun res => PMF.pure (hitAt ck r d iv res.2 jStar)) := by
        have hrep := samplePi_replace (fun _ : Fin qTok => setup.Com.openSample)
          (fun _ : Fin qTok => (0 : Fin lam → ZMod 2)) jStar
        rw [← hrep]
        simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        conv_lhs => enter [2, rStar]; rw [PMF.bind_comm]
        rw [PMF.bind_comm]
        refine Probability.PMF.bind_congr_on_support _ _ _ fun rOthers _ =>
          Probability.PMF.bind_congr_on_support _ _ _ fun rStar _ => ?_
        conv_rhs => enter [2, d]; rw [PMF.bind_comm]
        conv_rhs => rw [PMF.bind_comm]
        refine Probability.PMF.bind_congr_on_support _ _ _ fun h5 _ =>
          Probability.PMF.bind_congr_on_support _ _ _ fun d _ =>
            Probability.PMF.bind_congr_on_support _ _ _ fun iv _ =>
              Probability.PMF.bind_congr_on_support _ _ _ fun cmult _ => ?_
        have heq_tok :
            (fun j : Fin qTok =>
              (⟨if j = jStar then setup.Com.eval ck (setup.msgs ck jStar) rStar
                else setup.Com.eval ck (setup.msgs ck j) (rOthers j), iv j, d j, cmult j⟩ :
                  CRTProofToken C IV nMult lam nMask)) =
              (fun j : Fin qTok =>
                ⟨setup.Com.eval ck (setup.msgs ck j) (Function.update rOthers jStar rStar j),
                  iv j, d j, cmult j⟩) := by
          funext j
          by_cases hj : j = jStar <;> simp [hj, Function.update]
        have hup : Function.update rOthers jStar rStar jStar = rStar := by simp
        simp only [hitAt, heq_tok, hup]
        rw [ProbOracleComp.eval_runState]
        have hh5 : (fun q state => ProbComp.eval (h5LogHandlerP h5 q state)) =
            h5LogHandler h5 :=
          funext fun q => funext fun s => by simp [h5LogHandlerP, h5LogHandler]
        rw [hh5]
      simp_rw [hcomm1]
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun r _ => ?_
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun d _ => ?_
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun h5 _ => ?_
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun cmult _ => ?_
      rw [PMF.bind_comm]
      simp [PMF.map, Function.comp_def]
    rw [hhide_re]
    have hbad_eq :
        badFullProb =
          (fullSetup fun ck r d iv h5 cmult =>
            (logRun ck h5 r d iv cmult).bind fun res =>
              PMF.pure (res.2.any (isBadH5Query setup ck iv d r))) true := by
      simp only [badFullProb, hg85_reorder]
      rw [hfullMap]
      refine congrArg (fun p : PMF Bool => p true) (hfullCongr _ _ fun ck r d iv h5 cmult => ?_)
      rw [← hlog_to_bad ck h5 r d iv cmult]
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    rw [hbad_eq]
    have hpoint_hit (ck : CommitKey) (r d : Fin qTok → Fin lam → ZMod 2)
        (iv : Fin qTok → IV) (qs : List (H5Query IV nMult lam)) :
        (PMF.pure (qs.any (isBadH5Query setup ck iv d r))) true ≤
          (qTok : ℝ≥0∞) * ((uniformOfFintype (Fin qTok)).map (hitAt ck r d iv qs)) true := by
      by_cases hhit : qs.any (isBadH5Query setup ck iv d r) = true
      · simp only [hhit, PMF.pure_apply, ↓reduceIte]
        rcases List.any_eq_true.mp hhit with ⟨q, hqmem, hqbad⟩
        simp only [isBadH5Query, decide_eq_true_eq] at hqbad
        rcases hqbad with ⟨j₀, e₀, rfl⟩
        have hpred0 : hitAt ck r d iv qs j₀ = true := by
          refine List.any_eq_true.mpr ⟨badH5Key setup ck iv d r j₀ e₀, hqmem, ?_⟩
          have hlab : (setup.baseLabel ck j₀ e₀ + d j₀ + r j₀) +
              setup.baseLabel ck j₀ e₀ + d j₀ = r j₀ := by
            rw [add_assoc _ _ (d j₀), add_comm _ (r j₀), add_assoc,
              hvec, add_zero]
          simp [badH5Key, hlab]
        have hle1 : (qTok : ℝ≥0∞)⁻¹ ≤
            ((uniformOfFintype (Fin qTok)).map (hitAt ck r d iv qs)) true := by
          rw [PMF.map_apply]
          have hj0 : (qTok : ℝ≥0∞)⁻¹ =
              if true = hitAt ck r d iv qs j₀ then (uniformOfFintype (Fin qTok)) j₀ else 0 := by
            simp [uniformOfFintype_apply, hpred0]
          simpa using hj0.trans_le (le_tsum (fun jStar =>
            if true = hitAt ck r d iv qs jStar then (uniformOfFintype (Fin qTok)) jStar
            else 0) j₀)
        calc (1 : ℝ≥0∞) = (qTok : ℝ≥0∞) * (qTok : ℝ≥0∞)⁻¹ :=
              (ENNReal.mul_inv_cancel hq_pos hq_ne_top).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hle1 zero_le
      · simp [Bool.eq_false_iff.mpr hhit]
    have hmul_bind : ∀ {α : Type} (p : PMF α) (f g : α → ℝ≥0∞),
        (∀ x, f x ≤ (qTok : ℝ≥0∞) * g x) →
        (∑' x, p x * f x) ≤ (qTok : ℝ≥0∞) * (∑' x, p x * g x) := by
      intro α p f g hle
      rw [← ENNReal.tsum_mul_left]
      refine tsum_le_tsum fun x => ?_
      calc p x * f x ≤ p x * ((qTok : ℝ≥0∞) * g x) := mul_le_mul_of_nonneg_left (hle x) zero_le
        _ = (qTok : ℝ≥0∞) * (p x * g x) := by ring
    simp only [fullSetup, outerSetup, PMF.bind_apply]
    exact hmul_bind _ _ _ fun ck => hmul_bind _ _ _ fun r => hmul_bind _ _ _ fun d =>
      hmul_bind _ _ _ fun iv => hmul_bind _ _ _ fun h5 => hmul_bind _ _ _ fun cmult =>
      hmul_bind _ _ _ fun res => hpoint_hit ck r d iv res.2
  have hhide_true_le_bind :
      ProbComp.eval (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) true ≤
        ProbComp.eval
          (setup.Com.toScheme.bindingExperiment (badH5BindingReduction setup)) true := by
    simp only [Commitment.Scheme.eval_hidingExperiment, Commitment.Scheme.bindingExperiment,
      Game.withSetup, eval_lrExperiment, badH5HidingReduction, badH5BindingReduction,
      OpeningCommitment.toScheme, Commitment.Scheme.commitment, MessagePair.select_true,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    refine Probability.PMF.bind_apply_mono_on_support _ true fun ck _ =>
      Probability.PMF.bind_apply_mono_on_support _ true fun jStar _ =>
        Probability.PMF.bind_apply_mono_on_support _ true fun rDummy _ =>
          Probability.PMF.bind_apply_mono_on_support _ true fun ⟨ivStar, dStar, qs⟩ _ => ?_
    dsimp only
    cases hq : (qs.find? fun q =>
        decide (q.iv = ivStar) &&
          decide (setup.Com.eval ck (setup.msgs ck jStar)
            (q.label + setup.baseLabel ck jStar q.gate + dStar) =
            setup.Com.eval ck (setup.msgs ck jStar).bumpBal rDummy)) with
    | none =>
      have hany := List.any_eq_false.mpr (List.find?_eq_none.mp hq)
      simp [hany]
    | some q =>
      have hqp := List.find?_some hq
      have hqev : setup.Com.eval ck (setup.msgs ck jStar)
          (q.label + setup.baseLabel ck jStar q.gate + dStar) =
          setup.Com.eval ck (setup.msgs ck jStar).bumpBal rDummy :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hqp).2
      refine (PMF.coe_le_one _ true).trans_eq ?_
      simp [Commitment.Scheme.isBindingCollision, hqev, (CommitMsg.bumpBal_ne _).symm]
  have hbad_real :
      badFullProb.toReal ≤
        (qTok : ℝ) *
          ((Experiment.advantage
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false)
            (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) : ℝ) +
            (Experiment.succProbability
              (setup.Com.toScheme.bindingExperiment (badH5BindingReduction setup)) : ℝ)) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top qTok)
      (PMF.apply_ne_top _ _)) hbad_hide
    have h2 := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hhide_true_le_bind
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h1
    have hle := le_abs_self
      ((ProbComp.eval
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) false) true).toReal -
        (ProbComp.eval
          (setup.Com.toScheme.hidingExperiment (badH5HidingReduction setup) true) true).toReal)
    rw [Experiment.coe_advantage, Experiment.coe_succProbability]
    nlinarith [Nat.cast_nonneg (α := ℝ) qTok]
  have hadv_le := Game.advantage_le_of_apply_le
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)
    hdec_global.1 hdec_global.2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at hadv_le
  exact hadv_le.trans (add_le_add hbad_real (le_refl _))


end Cslib.Crypto.AnonymousToken.CRTDecoupling
