/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Correctness
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindCompare
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Tactic.ENNRealToReal
import CslibFrontier.Tactic.SuppCases

/-!
# The challenge hops of the FO IND-CCA proofs

The last hop of the ROM IND-CCA proofs for `FO-notbot` and `FO^⊥` ([HofheinzHoevelmannsKiltz2017],
proofs of the §3.1 theorems for `T` combined with the proofs of the §3.2 IND-CCA theorems for `U`)
bounds the distinguishing advantage between the real and the random challenge key by the success
probability of the one-wayness experiment `Scheme.simFilterOwExperiment`, which
`Scheme.succProbability_simFilterOwExperiment_le` bounds by the IND-CPA advantage of
`Scheme.romCpaReduction`.

In the challenge games the handler starts with `G(m*) = r*` and `Hq(c*) = kq` already cached, and
the adversary receives `kq` (`b = false`) or an independent `kRand` (`b = true`). Both games are
compared with the run of the same handler from empty caches:

1. A preset cache entry is the same as a lazily programmed sampler point: the run from the preset
   caches has the output law of the run from empty caches whose `G` sampler returns `r*` at `m*`
   and whose `Hq` sampler returns `kq` at `c*`.
2. The programmed and the unprogrammed handlers are identical until `G(m*)` or `Hq(c*)` is
   cached, for either input key.
3. It remains to bound the probability that the unprogrammed run caches `Hq(c*)` without `G(m*)`.

For `FO-notbot` the handler is the coupled one, whose key-derivation oracle reads `Hq(c)` for
`H(false, m, c)` only when `c = Enc(pk, m; G(m))` and `Dec(sk, c) = some m`. If the challenge
decrypts to `m*`, this forces `m = m*`, so step 3 costs nothing beyond the challenge's own
decryption failure, as in game G3 of the proof of Theorem 3.4 of [HofheinzHoevelmannsKiltz2017].
The decryption test is then removed inside the run from empty caches, at cost `(qG + qH) δ`, which
leaves the one-wayness experiment of the keyless simulator. No spreadness is needed
(`advantage_coupledGame_le`).

For the keyless simulator of the `FO^⊥` proof, `H(false, m, c*)` reads `Hq(c*)` whenever a cached
coin `G(m)` re-encrypts `m` to `c*`, also for `m ≠ m*`; `γ`-spreadness bounds this collision by
`(qG + qH) · 2^(-γ)` (`advantage_simFilterGame_le`).

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_coupledGame_le`: for a `δ`-correct PKE,
  the advantage between `coupledGame A false` and `coupledGame A true` is at most
  `2 Pr[OW] + 2 (qG + qH + 1) δ`, where `OW` is the one-wayness experiment `simFilterOwExperiment`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_simFilterGame_le`: for a `γ`-spread PKE,
  the advantage between `simFilterGame d A false` and `simFilterGame d A true` is at most
  `2 Pr[OW] + 2 (qG + qH) 2^(-γ)`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/
public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

/-! ### Association lists with one programmed entry -/

section Ens

variable {α β : Type} [DecidableEq α]

/-- Drop every entry for `x` and append `(x, v)`: the list that a memoized cache would hold if
`(x, v)` had been stored before every other entry. -/
@[expose] def ens (x : α) (v : β) (L : List (α × β)) : List (α × β) :=
  L.filter (fun e => e.1 != x) ++ [(x, v)]

private theorem lookup_filter_ne (x y : α) (L : List (α × β)) (hy : y ≠ x) :
    (L.filter (fun e => e.1 != x)).lookup y = L.lookup y := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨a, b⟩ := e; simp only [List.filter_cons]; split_ifs with ha
    · by_cases hya : y = a <;> simp [List.lookup_cons, hya, ih]
    · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr ((by simpa using ha : a = x).symm ▸ hy), ih]

private theorem lookup_filter_self (x : α) (L : List (α × β)) :
    (L.filter (fun e => e.1 != x)).lookup x = none := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨a, b⟩ := e; simp only [List.filter_cons]; split_ifs with ha
    · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr (by simpa [ne_comm] using ha), ih]
    · exact ih

theorem lookup_ens (x : α) (v : β) (L : List (α × β)) (y : α) :
    (ens x v L).lookup y = if y = x then some v else L.lookup y := by
  by_cases hy : y = x
  · subst hy; simp [ens, List.lookup_append, lookup_filter_self]
  · simp only [ens, List.lookup_append, lookup_filter_ne x y L hy, hy, ↓reduceIte]
    cases L.lookup y <;> simp [hy]

private theorem ens_cons_ne (x : α) (v : β) (L : List (α × β)) (y : α) (w : β) (hy : y ≠ x) :
    ens x v ((y, w) :: L) = (y, w) :: ens x v L := by
  simp [ens, hy]

private theorem ens_cons_self (x : α) (v w : β) (L : List (α × β)) :
    ens x v ((x, w) :: L) = ens x v L := by
  simp [ens]

/-- Memoizing with `x` programmed to `v`, then moving `(x, v)` to the end, is memoizing on the list
in which `(x, v)` is already stored. -/
private theorem memoize_ens (d : PMF β) (x : α) (v : β) (y : α) (L : List (α × β))
    (hL : L.lookup x = none ∨ L.lookup x = some v) :
    (memoize (fun _ => if y = x then PMF.pure v else d) y L).map
        (fun p => (p.1, ens x v p.2)) =
      memoize (fun _ => d) y (ens x v L) := by
  by_cases hy : y = x
  · subst hy
    rw [memoize_of_some (fun _ => d) y (ens y v L) v (by simp [lookup_ens])]
    rcases hL with hL | hL
    · rw [memoize_of_none _ _ _ hL]
      simp [ens_cons_self, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    · rw [memoize_of_some _ _ _ v hL]; simp [PMF.monad_pure_eq_pure]
  · have hlook : (ens x v L).lookup y = L.lookup y := by simp [lookup_ens, hy]
    cases h : L.lookup y with
    | some w =>
      rw [memoize_of_some _ _ _ w h, memoize_of_some _ _ _ w (hlook.trans h)]
      simp [PMF.monad_pure_eq_pure]
    | none =>
      rw [memoize_of_none _ _ _ h, memoize_of_none _ _ _ (hlook.trans h)]
      simp [hy, ens_cons_ne _ _ _ _ _ hy, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.map_bind]

private theorem isSome_lookup_of_suffix {L₁ L₂ : List (α × β)} (h : L₁ <:+ L₂) (x : α)
    (hx : (L₁.lookup x).isSome) : (L₂.lookup x).isSome := by
  by_contra hnone
  exact Option.not_isSome_iff_eq_none.mpr
    (h.lookup_eq_none (Option.not_isSome_iff_eq_none.mp hnone)) hx

end Ens

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- The keyless simulator `simFilterHandler d pk cStar`, evaluated to `PMF`, run on
`A ⟨pk, cStar, k⟩` from the state `st`. -/
private noncomputable def simRun (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K)
    (pk : PK) (cStar : CT) (k : K) (st : SimState M R CT K) : PMF (Bool × SimState M R CT K) :=
  (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
    (fun q s => ProbComp.eval (S.simFilterHandler d pk cStar q s)) (A ⟨pk, cStar, k⟩)).run st

omit [DecidableEq CT] in
/-- A supported transition of `simHashG` records its answer, keeps the old `gCache` entries and
does not touch `hqCache`. -/
private theorem simHashG_support {sc : ProbComp R} {m : M} {st : SimState M R CT K}
    {z : R × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashG sc m st)).support) :
    (m, z.1) ∈ z.2.gCache ∧ st.gCache ⊆ z.2.gCache ∧ z.2.hqCache = st.hqCache := by
  supp_cases hz [simHashG, RandomOracle.eval_zoomStateT_memoize] with ⟨⟨r, c'⟩, hc', rfl⟩
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨hl, hnext⟩ | ⟨-, -, hnext⟩
  · dsimp only at hl hnext ⊢; subst hnext
    obtain ⟨l₁, l₂, hlist, -⟩ := List.lookup_eq_some_iff.mp hl
    exact ⟨by simp [hlist], List.Subset.refl _, rfl⟩
  · dsimp only at hnext ⊢; subst hnext; exact ⟨by simp, List.subset_cons_self _ _, rfl⟩

omit [DecidableEq M] in
/-- A supported transition of `simHashHq c` keeps `gCache` and only adds the key `c` to
`hqCache`. -/
private theorem simHashHq_support {sk : ProbComp K} {c cStar : CT} {st : SimState M R CT K}
    {z : K × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashHq sk c st)).support) :
    z.2.gCache = st.gCache ∧
      ((z.2.hqCache.lookup cStar).isSome → c = cStar ∨ (st.hqCache.lookup cStar).isSome) := by
  supp_cases hz [simHashHq, RandomOracle.eval_zoomStateT_memoize] with ⟨⟨r, c'⟩, hc', rfl⟩
  refine ⟨rfl, fun h => ?_⟩
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨-, hnext⟩ | ⟨-, -, hnext⟩
  · dsimp only at hnext h; exact Or.inr (hnext ▸ h)
  · dsimp only at hnext h
    obtain ⟨p, hp, hpk⟩ := List.lookup_isSome_iff.mp (hnext ▸ h)
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl (eq_of_beq hpk).symm
    · exact Or.inr (List.lookup_isSome_iff.mpr ⟨p, hp, hpk⟩)

/-- A supported transition of `simHashHRaw` keeps `gCache` and `hqCache`. -/
private theorem simHashHRaw_support {sk : ProbComp K} {x : Bool × M × CT}
    {st : SimState M R CT K} {z : K × SimState M R CT K}
    (hz : z ∈ (ProbComp.eval (simHashHRaw sk x st)).support) :
    z.2.gCache = st.gCache ∧ z.2.hqCache = st.hqCache := by
  supp_cases hz [simHashHRaw, RandomOracle.eval_zoomStateT_memoize] with ⟨_, -, rfl⟩
  exact ⟨rfl, rfl⟩

omit [DecidableEq M] [DecidableEq CT] in
/-- A distribution whose supported states all keep the `gCache` of a state `st` outside a
`gCache` event reaches that event with probability zero. -/
private theorem toOuterMeasure_gCache_eq_zero {α : Type} (p : PMF (α × SimState M R CT K))
    (st : SimState M R CT K) (P : List (M × R) → Prop) (hst : ¬P st.gCache)
    (h : ∀ x ∈ p.support, x.2.gCache = st.gCache) : p.toOuterMeasure {x | P x.2.gCache} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  exact fun x hx hP => hst (h x hx ▸ hP)

omit [DecidableEq CT] in
/-- From a state where no `gCache` entry re-encrypts to `cStar`, one `simHashG` call creates such
an entry with probability at most `2^(-γ)`. -/
private theorem simHashG_reEnc_le (S : Scheme PK SK M R CT K) {γ : ℝ} (hγ : S.pke.GammaSpread γ)
    {pk : PK} {sk : SK} (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (m : M)
    (cStar : CT) (st : SimState M R CT K)
    (hst : ¬∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar) :
    (ProbComp.eval (simHashG S.pke.sampleCoins m st)).toOuterMeasure
        {z | ∃ p ∈ z.2.gCache, S.pke.encDet pk p.1 p.2 = cStar} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-γ)) := by
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, PMF.toOuterMeasure_map_apply]
  cases h : st.gCache.lookup m with
  | some v =>
    simp only [memoize, h, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
    split_ifs with hmem; exacts [absurd hmem (by simpa using hst), bot_le]
  | none =>
    simp only [memoize, h, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind]
    change ((ProbComp.eval S.pke.sampleCoins).map
      fun v => (v, (m, v) :: st.gCache)).toOuterMeasure _ ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans
      ((ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) (by positivity)).mpr
        (hγ pk sk hpk m cStar))
    rintro r ⟨⟨p, hp, he⟩, -⟩
    rcases List.mem_cons.mp hp with rfl | hp
    exacts [he, absurd ⟨p, hp, he⟩ hst]

/-- From a state where no `gCache` entry re-encrypts to `cStar`, one `simFilterHandler` call
creates such an entry with probability at most `2^(-γ)` for each `G` or `H` query it makes. -/
private theorem simHandler_reEnc_le (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    {γ : ℝ} (hγ : S.pke.GammaSpread γ) {pk : PK} {sk : SK}
    (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (cStar : CT) (q : ROQuery M CT)
    (st : SimState M R CT K) (hst : ¬∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar) :
    (ProbComp.eval (S.simFilterHandler d pk cStar q st)).toOuterMeasure
        {x | ∃ p ∈ x.2.gCache, S.pke.encDet pk p.1 p.2 = cStar} ≤
      (q.gCost : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) +
        (q.hCost : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) := by
  let P := fun g : List (M × R) => ∃ p ∈ g, S.pke.encDet pk p.1 p.2 = cStar
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · change (ProbComp.eval (simHashG S.pke.sampleCoins m st)).toOuterMeasure _ ≤ _
    simpa only [ROQuery.gCost, ROQuery.hCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
      add_zero] using S.simHashG_reEnc_le hγ hpk m cStar st hst
  · simp only [ROQuery.gCost, ROQuery.hCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
      zero_add]
    change (ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun z =>
      (if S.pke.encDet pk m z.fst = c then simHashHq S.sampleKey c
        else simHashHRaw S.sampleKey (false, m, c)) z.snd)).toOuterMeasure _ ≤ _
    rw [ProbComp.eval_bind]
    refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
      {z | P z.2.gCache} _ 0 fun z _ hz => ?_).trans
      (by simpa only [add_zero] using S.simHashG_reEnc_le hγ hpk m cStar st hst)
    refine (toOuterMeasure_gCache_eq_zero _ z.2 P hz fun y hy => ?_).le
    split_ifs at hy; exacts [(simHashHq_support (cStar := cStar) hy).1, (simHashHRaw_support hy).1]
  · simp only [ROQuery.gCost, ROQuery.hCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
      zero_add]
    exact (toOuterMeasure_gCache_eq_zero _ st P hst fun _ hy =>
      (simHashHRaw_support hy).1).trans_le zero_le
  · simp only [ROQuery.gCost, ROQuery.hCost, Nat.cast_zero, zero_mul, add_zero]
    exact (toOuterMeasure_gCache_eq_zero _ st P hst fun _ hy =>
      gCache_eq_of_mem_support_filterDecaps _ _ _ _ _ _ hy).le

/-- The outer four-tuple randomness: key pair, challenge message, coins, and one key. -/
private noncomputable def chalOuter4 (S : Scheme PK SK M R CT K) :
    PMF ((PK × SK) × M × R × K) :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
  (ProbComp.eval S.sampleMsg).bind fun mStar =>
  (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
  (ProbComp.eval S.sampleKey).bind fun k => PMF.pure (keys, mStar, rStar, k)

/-- The one-wayness experiment `simFilterOwExperiment` as the probability that the simulator run
from empty caches on an encryption of a fresh message `m` records `m` in `gCache`. -/
private theorem eval_simFilterOwExperiment (S : Scheme PK SK M R CT K)
    (d : PK → List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K) :
    ProbComp.eval (S.simFilterOwExperiment d A) =
      S.chalOuter4.bind fun u =>
        (S.simRun (d u.1.1) A u.1.1 (S.pke.encDet u.1.1 u.2.1 u.2.2.1) u.2.2.2 {}).map
          fun x => (x.2.gCache.lookup u.2.1).isSome := by
  simp only [simFilterOwExperiment, simFilterHit, simRun, ExplicitCoinPKE.encrypt, chalOuter4,
    OracleComp.map_run_interpret ProbComp.isMonadHom_eval, pmf_norm]
  rfl

/-! ### Simulators with lazily programmed points -/

/-- Lazy `G` on `gCache`, sampling `gs m` at a fresh query `m`. -/
private def genHashG (gs : M → ProbComp R) (m : M) : StateT (SimState M R CT K) ProbComp R :=
  RandomOracle.zoomStateT (fun st => st.gCache) (fun st c => { st with gCache := c })
    (memoize (fun _ => gs m) m)

/-- Lazy `Hq` on `hqCache`, sampling `hs c` at a fresh query `c`. -/
private def genHashHq (hs : CT → ProbComp K) (c : CT) : StateT (SimState M R CT K) ProbComp K :=
  RandomOracle.zoomStateT SimState.hqCache (fun st c' => { st with hqCache := c' })
    (memoize (fun _ => hs c) c)

/-- The simulator with decapsulation filter `d`, per-point samplers `gs` for `G` and `hs` for `Hq`,
and coin test `t`: a key-derivation query `H(false, m, c)` reads `Hq(c)` when the coin `r = G(m)`
satisfies `t m c r`. The keyless simulator tests `Enc(pk, m; r) = c`
(`simFilterHandler_eq_genHandler`); the coupled handler also tests `Dec(sk, c) = some m`
(`coupledFilterHandler_eq_genHandler`). -/
private def genHandler (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (gs : M → ProbComp R) (hs : CT → ProbComp K) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  ROQuery.dispatch (genHashG gs)
    (fun
      | (false, m, c) => do
        let r ← genHashG gs m
        if t m c r then genHashHq hs c else simHashHRaw S.sampleKey (false, m, c)
      | (true, m, c) => simHashHRaw S.sampleKey (true, m, c))
    (filterDecaps (genHashHq hs) d) cStar q

private theorem simFilterHandler_eq_genHandler (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK) (cStar : CT) :
    S.simFilterHandler d pk cStar =
      S.genHandler d (fun m c r => S.pke.encDet pk m r = c) (fun _ => S.pke.sampleCoins)
        (fun _ => S.sampleKey) cStar := by
  funext q
  rcases q with m | ⟨_ | _, m, c⟩ | c <;> rfl

private theorem coupledFilterHandler_eq_genHandler (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK) (sk : SK) (cStar : CT) :
    S.coupledFilterHandler d pk sk cStar =
      S.genHandler d (fun m c r => S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m)
        (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) cStar := by
  funext q
  rcases q with m | ⟨_ | _, m, c⟩ | c <;> rfl

/-- The handler `genHandler d t gs hs cStar`, evaluated to `PMF`, run on `A ⟨pk, cStar, k⟩` from the
state `st`. -/
private noncomputable def genRun (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (gs : M → ProbComp R) (hs : CT → ProbComp K) (A : ROAdversary PK M R CT K)
    (pk : PK) (cStar : CT) (k : K) (st : SimState M R CT K) : PMF (Bool × SimState M R CT K) :=
  (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
    (fun q s => ProbComp.eval (S.genHandler d t gs hs cStar q s)) (A ⟨pk, cStar, k⟩)).run st

omit [DecidableEq CT] in
private theorem eval_genHashG (gs : M → ProbComp R) (m : M) (s : SimState M R CT K) :
    ProbComp.eval (genHashG gs m s) =
      (memoize (fun _ => ProbComp.eval (gs m)) m s.gCache).map
        (fun p => (p.1, { s with gCache := p.2 })) :=
  RandomOracle.eval_zoomStateT_memoize _ _ _ _ _

omit [DecidableEq M] in
private theorem eval_genHashHq (hs : CT → ProbComp K) (c : CT) (s : SimState M R CT K) :
    ProbComp.eval (genHashHq hs c s) =
      (memoize (fun _ => ProbComp.eval (hs c)) c s.hqCache).map
        (fun p => (p.1, { s with hqCache := p.2 })) :=
  RandomOracle.eval_zoomStateT_memoize _ _ _ _ _

private theorem eval_simHashHRaw (sampleKey : ProbComp K) (x : Bool × M × CT)
    (s : SimState M R CT K) :
    ProbComp.eval (simHashHRaw sampleKey x s) =
      (memoize (fun _ => ProbComp.eval sampleKey) x s.hCache).map
        (fun p => (p.1, { s with hCache := p.2 })) :=
  RandomOracle.eval_zoomStateT_memoize _ _ _ _ _

private theorem eval_genHandler_H_false (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (gs : M → ProbComp R) (hs : CT → ProbComp K) (cStar : CT) (m : M) (c : CT)
    (s : SimState M R CT K) :
    ProbComp.eval (S.genHandler d t gs hs cStar (.H (false, m, c)) s) =
      (ProbComp.eval (genHashG gs m s)).bind fun z =>
        if t m c z.1 then ProbComp.eval (genHashHq hs c z.2)
        else ProbComp.eval (simHashHRaw S.sampleKey (false, m, c) z.2) := by
  change ProbComp.eval (genHashG gs m s >>= fun z =>
    (if t m c z.1 then genHashHq hs c else simHashHRaw S.sampleKey (false, m, c)) z.2) = _
  rw [ProbComp.eval_bind]; congr 1 with z : 1; split_ifs <;> rfl

private theorem eval_genHandler_decaps (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (gs : M → ProbComp R) (hs : CT → ProbComp K) (cStar c : CT) (hc : c ≠ cStar)
    (s : SimState M R CT K) :
    ProbComp.eval (S.genHandler d t gs hs cStar (.decaps c) s) =
      if d s.gCache c = true then
        (ProbComp.eval (genHashHq hs c s)).map fun z => (some z.1, z.2)
      else
        PMF.pure (none, s) := by
  change ProbComp.eval ((if c = cStar then (return none : StateT (SimState M R CT K) ProbComp
    (Option K)) else filterDecaps (genHashHq hs) d c) s) = _
  simp only [hc, ↓reduceIte, filterDecaps]
  cases d s.gCache c
  · exact ProbComp.eval_pure _
  · change ProbComp.eval (genHashHq hs c s >>= fun z => pure (some z.1, z.2)) = _
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map]; rfl

private theorem eval_genHandler_decaps_self (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (gs : M → ProbComp R) (hs : CT → ProbComp K) (cStar : CT) (s : SimState M R CT K) :
    ProbComp.eval (S.genHandler d t gs hs cStar (.decaps cStar) s) = PMF.pure (none, s) := by
  change ProbComp.eval ((if cStar = cStar then (return none : StateT (SimState M R CT K)
    ProbComp (Option K)) else filterDecaps (genHashHq hs) d cStar) s) = _
  simp only [↓reduceIte]; exact ProbComp.eval_pure _

/-! ### Cache growth -/

private theorem suffix_of_mem_support_memoize {α β : Type} [BEq α] (d : α → PMF β) (y : α)
    (L : List (α × β)) (p : β × List (α × β)) (hp : p ∈ (memoize d y L).support) : L <:+ p.2 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hp with ⟨-, h⟩ | ⟨-, -, h⟩ <;>
    simp [h, List.suffix_cons]

omit [DecidableEq CT] in
private theorem genHashG_mono (gs : M → ProbComp R) (m : M) (s : SimState M R CT K)
    (x : R × SimState M R CT K) (hx : x ∈ (ProbComp.eval (genHashG gs m s)).support) :
    s.gCache <:+ x.2.gCache ∧ x.2.hqCache = s.hqCache := by
  supp_cases hx [eval_genHashG] with ⟨p, hp, rfl⟩
  exact ⟨suffix_of_mem_support_memoize _ _ _ p hp, rfl⟩

omit [DecidableEq M] in
private theorem genHashHq_mono (hs : CT → ProbComp K) (c : CT) (s : SimState M R CT K)
    (x : K × SimState M R CT K) (hx : x ∈ (ProbComp.eval (genHashHq hs c s)).support) :
    x.2.gCache = s.gCache ∧ s.hqCache <:+ x.2.hqCache := by
  supp_cases hx [eval_genHashHq] with ⟨p, hp, rfl⟩
  exact ⟨rfl, suffix_of_mem_support_memoize _ _ _ p hp⟩

/-- Transfer any state predicate `P` closed under unchanged `(gCache, hqCache)`, `genHashG`,
coin-tested `genHashG >>= genHashHq`, and non-challenge `genHashHq` across one `genHandler`
step. -/
private theorem genHandler_invariant (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (gs : M → ProbComp R)
    (hs : CT → ProbComp K) (cStar : CT) (P : SimState M R CT K → Prop)
    (hraw : ∀ {s s' : SimState M R CT K}, P s →
      s'.gCache = s.gCache → s'.hqCache = s.hqCache → P s')
    (hG : ∀ m s z, P s → z ∈ (ProbComp.eval (genHashG gs m s)).support → P z.2)
    (hGHq : ∀ m c s z y, P s → z ∈ (ProbComp.eval (genHashG gs m s)).support →
      t m c z.1 → y ∈ (ProbComp.eval (genHashHq hs c z.2)).support → P y.2)
    (hHq_ne : ∀ c s z, c ≠ cStar → P s →
      z ∈ (ProbComp.eval (genHashHq hs c s)).support → P z.2)
    (q : ROQuery M CT) (s : SimState M R CT K) (hs₀ : P s)
    (x : ROResp R K q × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (S.genHandler d t gs hs cStar q s)).support) : P x.2 := by
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · exact hG m s x hs₀ hx
  · rw [S.eval_genHandler_H_false] at hx
    supp_cases hx with ⟨z, hz, ⟨ht, hx⟩ | ⟨-, hx⟩⟩
    · exact hGHq m c s z x hs₀ hz ht hx
    · exact hraw (hG m s z hs₀ hz) (simHashHRaw_support hx).1 (simHashHRaw_support hx).2
  · exact hraw hs₀ (simHashHRaw_support hx).1 (simHashHRaw_support hx).2
  · by_cases hc : c = cStar
    · subst hc; rw [S.eval_genHandler_decaps_self] at hx; supp_cases hx; exact hs₀
    · rw [S.eval_genHandler_decaps d t gs hs cStar c hc] at hx
      supp_cases hx with ⟨-, z, hz, rfl⟩ | ⟨-, rfl⟩; exacts [hHq_ne c s z hc hs₀ hz, hs₀]

/-- Every supported step of `genHandler` only prepends to `gCache` and `hqCache`. -/
private theorem genHandler_mono (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (gs : M → ProbComp R)
    (hs : CT → ProbComp K) (cStar : CT) (q : ROQuery M CT) (s : SimState M R CT K)
    (x : ROResp R K q × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (S.genHandler d t gs hs cStar q s)).support) :
    s.gCache <:+ x.2.gCache ∧ s.hqCache <:+ x.2.hqCache :=
  S.genHandler_invariant d t gs hs cStar
    (fun s' => s.gCache <:+ s'.gCache ∧ s.hqCache <:+ s'.hqCache)
    (fun h hg hq => ⟨hg ▸ h.1, hq ▸ h.2⟩)
    (fun m _ _ h hz =>
      ⟨h.1.trans (genHashG_mono gs m _ _ hz).1, (genHashG_mono gs m _ _ hz).2 ▸ h.2⟩)
    (fun m c _ _ _ h hz _ hy =>
      ⟨(genHashHq_mono hs c _ _ hy).1 ▸ h.1.trans (genHashG_mono gs m _ _ hz).1,
        ((genHashG_mono gs m _ _ hz).2 ▸ h.2).trans (genHashHq_mono hs c _ _ hy).2⟩)
    (fun c _ _ _ h hz =>
      ⟨(genHashHq_mono hs c _ _ hz).1 ▸ h.1, h.2.trans (genHashHq_mono hs c _ _ hz).2⟩)
    q s ⟨List.suffix_refl _, List.suffix_refl _⟩ x hx

/-- A supported transition of the unprogrammed handler `genHandler d t` keeps the old `gCache`
entries, and records `cStar` in `hqCache` only if `cStar` already was there or some entry `(m, r)`
of the new `gCache` passes the coin test `t m cStar r`. -/
private theorem genHandler_step (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (cStar : CT)
    (q : ROQuery M CT) (st : SimState M R CT K) (res : ROResp R K q) (st' : SimState M R CT K)
    (hmem : (res, st') ∈ (ProbComp.eval (S.genHandler d t (fun _ => S.pke.sampleCoins)
      (fun _ => S.sampleKey) cStar q st)).support) :
    st.gCache ⊆ st'.gCache ∧
      ((st'.hqCache.lookup cStar).isSome → (st.hqCache.lookup cStar).isSome ∨
        ∃ p ∈ st'.gCache, t p.1 cStar p.2) :=
  S.genHandler_invariant d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) cStar
    (fun s' => st.gCache ⊆ s'.gCache ∧
      ((s'.hqCache.lookup cStar).isSome → (st.hqCache.lookup cStar).isSome ∨
        ∃ p ∈ s'.gCache, t p.1 cStar p.2))
    (fun h hg hq => ⟨hg ▸ h.1, fun h' => (h.2 (hq ▸ h')).imp id fun ⟨p, hp, ht⟩ =>
      ⟨p, hg ▸ hp, ht⟩⟩)
    (fun _ _ _ h hz =>
      let ⟨_, hsub, hhq⟩ := simHashG_support (sc := S.pke.sampleCoins) hz
      ⟨List.Subset.trans h.1 hsub,
        fun h' => (h.2 (hhq ▸ h')).imp id fun ⟨p, hp, ht⟩ => ⟨p, hsub hp, ht⟩⟩)
    (fun m c _ z _ h hz ht hy =>
      let ⟨hmz, hsub, hhq⟩ := simHashG_support (sc := S.pke.sampleCoins) hz
      let ⟨hg, hq'⟩ := simHashHq_support (sk := S.sampleKey) (cStar := cStar) hy
      ⟨hg ▸ List.Subset.trans h.1 hsub, fun h' => by
        rcases hq' h' with rfl | h''
        · exact Or.inr ⟨(m, z.1), hg ▸ hmz, ht⟩
        · exact (h.2 (hhq ▸ h'')).imp id fun ⟨p, hp, htp⟩ => ⟨p, hg ▸ hsub hp, htp⟩⟩)
    (fun c _ _ hc h hz =>
      let ⟨hg, hq'⟩ := simHashHq_support (sk := S.sampleKey) (cStar := cStar) hz
      ⟨hg ▸ h.1, fun h' =>
        (h.2 ((hq' h').resolve_left hc)).imp id fun ⟨p, hp, htp⟩ => ⟨p, hg ▸ hp, htp⟩⟩)
    q st ⟨List.Subset.refl _, Or.inl⟩ (res, st') hmem

/-! ### Programmed and unprogrammed simulators agree until a programmed point is cached -/

/-- The simulator state has cached `G(mStar)` or `Hq(cStar)`. -/
private def progBad (mStar : M) (cStar : CT) (s : SimState M R CT K) : Prop :=
  (s.gCache.lookup mStar).isSome ∨ (s.hqCache.lookup cStar).isSome

/-- A fresh memoized query for `x` caches `x`. -/
private theorem lookup_isSome_of_mem_support_memoize {α β : Type} [BEq α] [LawfulBEq α]
    (d : α → PMF β) (x : α) (L : List (α × β)) (hL : L.lookup x = none)
    (p : β × List (α × β)) (hp : p ∈ (memoize d x L).support) : (p.2.lookup x).isSome := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hp with ⟨h, -⟩ | ⟨-, -, h⟩
  · rw [hL] at h; cases h
  · rw [h]; simp

omit [DecidableEq M] [DecidableEq CT] in
private theorem zoomMemoize_agree {α β σ : Type} [BEq α] [LawfulBEq α]
    (get : σ → List (α × β)) (set : σ → List (α × β) → σ) (hget : ∀ s p, get (set s p) = p)
    {d₁ d₂ : α → ProbComp β} {xStar : α} (hd : ∀ x, x ≠ xStar → d₁ x = d₂ x)
    (x : α) (s : σ) (hs : (get s).lookup xStar = none) (z : β × σ)
    (hz : (get z.2).lookup xStar = none) :
    ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d₁ x) x) s) z =
      ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d₂ x) x) s) z := by
  rw [RandomOracle.eval_zoomStateT_memoize, RandomOracle.eval_zoomStateT_memoize]
  by_cases hx : x = xStar
  · subst hx
    have hzero (d : α → ProbComp β) :
        ((memoize (fun _ => ProbComp.eval (d x)) x (get s)).map
          fun p => (p.1, set s p.2)) z = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      supp_cases hmem with ⟨p, hp, rfl⟩
      have h := lookup_isSome_of_mem_support_memoize _ x (get s) hs p hp
      dsimp only at hz; rw [hget] at hz; simp [hz] at h
    rw [hzero, hzero]
  · cases (get s).lookup x <;> simp [memoize, hd x hx]

private theorem not_progBad {mStar : M} {cStar : CT} {s : SimState M R CT K} :
    ¬progBad mStar cStar s ↔ s.gCache.lookup mStar = none ∧ s.hqCache.lookup cStar = none := by
  simp only [progBad, not_or, Option.not_isSome_iff_eq_none]

private theorem progBad_of_suffix {mStar : M} {cStar : CT} {s s' : SimState M R CT K}
    (hg : s.gCache <:+ s'.gCache) (hq : s.hqCache <:+ s'.hqCache) (hs : progBad mStar cStar s) :
    progBad mStar cStar s' :=
  hs.imp (isSome_lookup_of_suffix hg mStar) (isSome_lookup_of_suffix hq cStar)

/-- Simulators whose samplers differ only at `G(mStar)` and `Hq(cStar)` agree until one of these
points is cached. -/
private theorem identicalUntilBad_genHandler (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    {gs₁ gs₂ : M → ProbComp R} {hs₁ hs₂ : CT → ProbComp K} {mStar : M} (cStar : CT)
    (hgs : ∀ m, m ≠ mStar → gs₁ m = gs₂ m) (hhs : ∀ c, c ≠ cStar → hs₁ c = hs₂ c) :
    OracleComp.IdenticalUntilBad
      (fun q s => ProbComp.eval (S.genHandler d t gs₁ hs₁ cStar q s))
      (fun q s => ProbComp.eval (S.genHandler d t gs₂ hs₂ cStar q s)) (progBad mStar cStar) where
  agree q s hs a s' hs' := by
    obtain ⟨hsg, hsq⟩ := not_progBad.mp hs
    obtain ⟨hsg', hsq'⟩ := not_progBad.mp hs'
    rcases q with m | ⟨_ | _, m, c⟩ | c
    · exact zoomMemoize_agree (fun s : SimState M R CT K => s.gCache)
        (fun s c => { s with gCache := c }) (fun _ _ => rfl) hgs m s hsg (a, s') hsg'
    · rw [eval_genHandler_H_false, eval_genHandler_H_false]
      refine bind_apply_eq_of_good (bad := progBad mStar cStar)
        (fun z hz => zoomMemoize_agree (fun s : SimState M R CT K => s.gCache)
          (fun s c => { s with gCache := c }) (fun _ _ => rfl) hgs m s hsg z
          (not_progBad.mp hz).1)
        (fun z hz y hy => by
          split_ifs
          · exact zoomMemoize_agree SimState.hqCache (fun s c => { s with hqCache := c })
              (fun _ _ => rfl) hhs c z.2 (not_progBad.mp hz).2 y (not_progBad.mp hy).2
          · rfl) ?_ ?_ (a, s') hs'
      all_goals
        intro z hz y hy
        supp_cases hy with ⟨-, hy⟩ | ⟨-, hy⟩
        · exact progBad_of_suffix ((genHashHq_mono _ c z.2 y hy).1 ▸ List.suffix_refl _)
            (genHashHq_mono _ c z.2 y hy).2 hz
        · exact progBad_of_suffix ((simHashHRaw_support hy).1 ▸ List.suffix_refl _)
            ((simHashHRaw_support hy).2 ▸ List.suffix_refl _) hz
    · rfl
    · by_cases hc : c = cStar
      · subst hc
        rw [eval_genHandler_decaps_self, eval_genHandler_decaps_self]
      · rw [eval_genHandler_decaps _ _ _ _ _ _ _ hc, eval_genHandler_decaps _ _ _ _ _ _ _ hc]
        cases d s.gCache c <;> simp only [↓reduceIte, Bool.false_eq_true]
        · simp only [PMF.map_apply]
          refine tsum_congr fun z => ?_
          split_ifs with hz
          · rw [(Prod.mk.inj hz).2] at hsq'
            exact zoomMemoize_agree SimState.hqCache (fun s c => { s with hqCache := c })
              (fun _ _ => rfl) hhs c s hsq z hsq'
          · rfl
  absorb_first _ _ hs _ hx :=
    have h := S.genHandler_mono d t gs₁ hs₁ cStar _ _ _ hx; progBad_of_suffix h.1 h.2 hs
  absorb_second _ _ hs _ hx :=
    have h := S.genHandler_mono d t gs₂ hs₂ cStar _ _ _ hx; progBad_of_suffix h.1 h.2 hs

/-! ### Preset cache entries as lazily programmed points -/

/-- Coin sampler for `G` with `G(mStar)` programmed to `rStar`. -/
private def progG (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R) (m : M) : ProbComp R :=
  if m = mStar then pure rStar else S.pke.sampleCoins

/-- Key sampler for `Hq` with `Hq(cStar)` programmed to `kq`. -/
private def progHq (S : Scheme PK SK M R CT K) (cStar : CT) (kq : K) (c : CT) : ProbComp K :=
  if c = cStar then pure kq else S.sampleKey

/-- A lookup at `x` is either missing or equal to `v`. -/
@[expose] def LookupNoneOr {α β : Type} [BEq α] (x : α) (v : β) (L : List (α × β)) : Prop :=
  L.lookup x = none ∨ L.lookup x = some v

private theorem lookupNoneOr_memoize {α β : Type} [DecidableEq α] (d : PMF β) (x : α) (v : β)
    (y : α) (L : List (α × β)) (hL : LookupNoneOr x v L) (p : β × List (α × β))
    (hp : p ∈ (memoize (fun _ => if y = x then PMF.pure v else d) y L).support) :
    LookupNoneOr x v p.2 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hp with ⟨-, h⟩ | ⟨-, hw, h⟩
  · exact h ▸ hL
  · rw [h]
    by_cases hy : y = x
    · subst hy; simp only [↓reduceIte, PMF.mem_support_pure_iff] at hw; exact Or.inr (by simp [hw])
    · simpa [LookupNoneOr, List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm hy)] using hL

/-- Moving the programmed entries to the end of their caches. -/
private def presetState (mStar : M) (rStar : R) (cStar : CT) (kq : K)
    (s : SimState M R CT K) : SimState M R CT K :=
  { s with gCache := ens mStar rStar s.gCache, hqCache := ens cStar kq s.hqCache }

/-- The programmed caches agree with the programmed values wherever they are defined. -/
private def PresetInv (mStar : M) (rStar : R) (cStar : CT) (kq : K)
    (s : SimState M R CT K) : Prop :=
  LookupNoneOr mStar rStar s.gCache ∧ LookupNoneOr cStar kq s.hqCache

omit [DecidableEq CT] in
private theorem eval_progG (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R) (m : M) :
    ProbComp.eval (S.progG mStar rStar m) =
      if m = mStar then PMF.pure rStar else ProbComp.eval S.pke.sampleCoins := by
  unfold progG; split_ifs <;> simp [ProbComp.eval_pure]

omit [DecidableEq M] in
private theorem eval_progHq (S : Scheme PK SK M R CT K) (cStar : CT) (kq : K) (c : CT) :
    ProbComp.eval (S.progHq cStar kq c) =
      if c = cStar then PMF.pure kq else ProbComp.eval S.sampleKey := by
  unfold progHq; split_ifs <;> simp [ProbComp.eval_pure]

private theorem presetInv_genHashG (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (m : M) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) (x : R × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (genHashG (S.progG mStar rStar) m s)).support) :
    PresetInv mStar rStar cStar kq x.2 := by
  supp_cases hx [eval_genHashG, eval_progG] with ⟨p, hp, rfl⟩
  exact ⟨lookupNoneOr_memoize _ _ _ _ _ hs.1 p hp, hs.2⟩

private theorem presetInv_genHashHq (S : Scheme PK SK M R CT K) (mStar : M) (rStar : R)
    (cStar : CT) (kq : K) (c : CT) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) (x : K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (genHashHq (S.progHq cStar kq) c s)).support) :
    PresetInv mStar rStar cStar kq x.2 := by
  supp_cases hx [eval_genHashHq, eval_progHq] with ⟨p, hp, rfl⟩
  exact ⟨hs.1, lookupNoneOr_memoize _ _ _ _ _ hs.2 p hp⟩

private theorem presetInv_genHandler (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (mStar : M)
    (rStar : R) (cStar : CT) (kq : K) (q : ROQuery M CT) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) (a : ROResp R K q) (s' : SimState M R CT K)
    (hx : (a, s') ∈ (ProbComp.eval
      (S.genHandler d t (S.progG mStar rStar) (S.progHq cStar kq) cStar q s)).support) :
    PresetInv mStar rStar cStar kq s' :=
  S.genHandler_invariant d t (S.progG mStar rStar) (S.progHq cStar kq) cStar
    (PresetInv mStar rStar cStar kq)
    (fun h hg hq => ⟨hg ▸ h.1, hq ▸ h.2⟩)
    (fun m s₁ z h hz => S.presetInv_genHashG mStar rStar cStar kq m s₁ h z hz)
    (fun m c s₁ z y h hz _ hy =>
      S.presetInv_genHashHq mStar rStar cStar kq c z.2
        (S.presetInv_genHashG mStar rStar cStar kq m s₁ h z hz) y hy)
    (fun c s₁ z _ h hz => S.presetInv_genHashHq mStar rStar cStar kq c s₁ h z hz)
    q s hs (a, s') hx

omit [DecidableEq M] [DecidableEq CT] in
private theorem zoomMemoize_presetState {α β σ : Type} [DecidableEq α]
    (get : σ → List (α × β)) (set : σ → List (α × β) → σ) (f : σ → σ)
    (x : α) (v : β) (y : α) (d₁ d₂ : ProbComp β) (s : σ)
    (hd : ProbComp.eval d₁ = if y = x then PMF.pure v else ProbComp.eval d₂)
    (hs : LookupNoneOr x v (get s)) (hget : get (f s) = ens x v (get s))
    (hset : ∀ p, f (set s p) = set (f s) (ens x v p)) :
    (ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d₁) y) s)).map
        (fun z => (z.1, f z.2)) =
      ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d₂) y) (f s)) := by
  rw [RandomOracle.eval_zoomStateT_memoize, RandomOracle.eval_zoomStateT_memoize, hd, hget,
    ← memoize_ens (ProbComp.eval d₂) x v y (get s) hs, PMF.map_comp, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun p => ?_)
  exact Prod.ext rfl (hset p.2)

private theorem genHandler_presetState (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (mStar : M) (rStar : R) (cStar : CT) (kq : K)
    (hd : ∀ L c, c ≠ cStar → LookupNoneOr mStar rStar L → d (ens mStar rStar L) c = d L c)
    (q : ROQuery M CT) (s : SimState M R CT K)
    (hs : PresetInv mStar rStar cStar kq s) :
    (ProbComp.eval
        (S.genHandler d t (S.progG mStar rStar) (S.progHq cStar kq) cStar q s)).map
        (fun x => (x.1, presetState mStar rStar cStar kq x.2)) =
      ProbComp.eval (S.genHandler d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) cStar q
        (presetState mStar rStar cStar kq s)) := by
  have presetRaw (y s₁) :
      (ProbComp.eval (simHashHRaw S.sampleKey y s₁)).map
          (fun x => (x.1, presetState mStar rStar cStar kq x.2)) =
        ProbComp.eval (simHashHRaw S.sampleKey y (presetState mStar rStar cStar kq s₁)) := by
    rw [eval_simHashHRaw, eval_simHashHRaw, PMF.map_comp]; rfl
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · exact zoomMemoize_presetState (fun s : SimState M R CT K => s.gCache)
      (fun s c => { s with gCache := c }) (presetState mStar rStar cStar kq) mStar rStar m _ _ s
      (S.eval_progG mStar rStar m) hs.1 rfl fun _ => rfl
  · rw [eval_genHandler_H_false, eval_genHandler_H_false, PMF.map_bind]
    dsimp only [genHashG]
    rw [← zoomMemoize_presetState (fun s : SimState M R CT K => s.gCache)
        (fun s c => { s with gCache := c }) (presetState mStar rStar cStar kq) mStar rStar m _ _ s
        (S.eval_progG mStar rStar m) hs.1 rfl fun _ => rfl,
      PMF.bind_map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun z hz => ?_
    have hz' := S.presetInv_genHashG mStar rStar cStar kq m s hs z hz
    dsimp only [Function.comp_apply]
    split_ifs
    · exact zoomMemoize_presetState SimState.hqCache (fun s c => { s with hqCache := c })
        (presetState mStar rStar cStar kq) cStar kq c _ _ z.2 (S.eval_progHq cStar kq c)
        hz'.2 rfl fun _ => rfl
    · exact presetRaw _ z.2
  · exact presetRaw _ s
  · by_cases hc : c = cStar
    · subst hc
      rw [eval_genHandler_decaps_self, eval_genHandler_decaps_self, PMF.pure_map]
    · rw [eval_genHandler_decaps _ _ _ _ _ _ _ hc, eval_genHandler_decaps _ _ _ _ _ _ _ hc,
        show (presetState mStar rStar cStar kq s).gCache = ens mStar rStar s.gCache from rfl,
        hd s.gCache c hc hs.1]
      cases d s.gCache c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact PMF.pure_map _ _
      · dsimp only [genHashHq]
        simp only [↓reduceIte, PMF.map_comp]
        rw [← zoomMemoize_presetState SimState.hqCache (fun s c => { s with hqCache := c })
          (presetState mStar rStar cStar kq) cStar kq c _ _ s (S.eval_progHq cStar kq c)
          hs.2 rfl fun _ => rfl, PMF.map_comp]
        rfl

/-- Running the unprogrammed handler `genHandler d t` from caches preset with `G(mStar) = rStar`
and `Hq(cStar) = kq` has the same output law as running it from empty caches with these points
lazily programmed. -/
private theorem genRun_preset_eq (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (A : ROAdversary PK M R CT K)
    (pk : PK) (mStar : M) (rStar : R) (cStar : CT) (kq k : K)
    (hd : ∀ L c, c ≠ cStar → LookupNoneOr mStar rStar L → d (ens mStar rStar L) c = d L c) :
    (S.genRun d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) A pk cStar k
        { gCache := [(mStar, rStar)], hqCache := [(cStar, kq)] }).map Prod.fst =
      (S.genRun d t (S.progG mStar rStar) (S.progHq cStar kq) A pk cStar k {}).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) <| OracleComp.run_interpret_map_state_of_invariant
    (fun q s => ProbComp.eval
      (S.genHandler d t (S.progG mStar rStar) (S.progHq cStar kq) cStar q s))
    (fun q s => ProbComp.eval
      (S.genHandler d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) cStar q s))
    (presetState mStar rStar cStar kq) (PresetInv mStar rStar cStar kq)
    (S.presetInv_genHandler d t mStar rStar cStar kq)
    (fun q s hs => S.genHandler_presetState d t mStar rStar cStar kq hd q s hs)
    (A ⟨pk, cStar, k⟩) {} ⟨Or.inl rfl, Or.inl rfl⟩
  rwa [PMF.map_comp, eq_comm] at h

/-! ### Unfolding `simFilterGame` -/

omit [DecidableEq CT] in
private theorem eval_simHashG_singleton (sc : ProbComp R) (mStar : M) (rStar : R) :
    ProbComp.eval (simHashG sc mStar ({ gCache := [(mStar, rStar)] } : SimState M R CT K)) =
      PMF.pure (rStar, ({ gCache := [(mStar, rStar)] } : SimState M R CT K)) := by
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, memoize_of_some _ _ _ rStar (by simp)]
  simp [Probability.PMF.monad_pure_eq_pure]

/-- The real-key computation of `simFilterGame` stores fresh `kq` at `Hq(c*)` and returns it. -/
private theorem eval_simHashH_init (S : Scheme PK SK M R CT K) (pk : PK) (mStar : M)
    (rStar : R) :
    ProbComp.eval ((S.simHashH pk (false, mStar, S.pke.encDet pk mStar rStar)).run
        { gCache := [(mStar, rStar)] }) =
      (ProbComp.eval S.sampleKey).map fun kq =>
        (kq, ({ gCache := [(mStar, rStar)], hqCache := [(S.pke.encDet pk mStar rStar, kq)] } :
          SimState M R CT K)) := by
  change ProbComp.eval (simHashG S.pke.sampleCoins mStar { gCache := [(mStar, rStar)] } >>=
    fun z => (if S.pke.encDet pk mStar z.1 = S.pke.encDet pk mStar rStar then
      simHashHq S.sampleKey (S.pke.encDet pk mStar rStar)
      else simHashHRaw S.sampleKey (false, mStar, S.pke.encDet pk mStar rStar)) z.2) = _
  rw [ProbComp.eval_bind, eval_simHashG_singleton, PMF.pure_bind]
  simp only [↓reduceIte, simHashHq, RandomOracle.eval_zoomStateT_memoize, memoize, List.lookup_nil,
    pmf_norm]
  rfl

/-- The outer randomness of `simFilterGame`: key pair, challenge message and coins, real and random
keys. -/
private noncomputable def chalOuter (S : Scheme PK SK M R CT K) :
    PMF ((PK × SK) × M × R × K × K) :=
  (ProbComp.eval S.pke.keyGen).bind fun keys =>
  (ProbComp.eval S.sampleMsg).bind fun mStar =>
  (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
  (ProbComp.eval S.sampleKey).bind fun kq =>
  (ProbComp.eval S.sampleKey).bind fun kRand => PMF.pure (keys, mStar, rStar, kq, kRand)

omit [DecidableEq M] [DecidableEq CT] in
private theorem eval_chalGame_aux (S : Scheme PK SK M R CT K)
    (init : PK → SK → M → R → StateT (SimState M R CT K) ProbComp K)
    (initSt : PK → SK → M → R → K → SimState M R CT K)
    (hinit : ∀ pk sk mStar rStar,
      ProbComp.eval ((init pk sk mStar rStar).run { gCache := [(mStar, rStar)] }) =
        (ProbComp.eval S.sampleKey).map fun kq => (kq, initSt pk sk mStar rStar kq))
    (handler : PK → SK → CT → (q : ROQuery M CT) →
      StateT (SimState M R CT K) ProbComp (ROResp R K q))
    (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (do
      let (pk, sk) ← S.pke.keyGen
      let mStar ← S.sampleMsg
      let rStar ← S.pke.sampleCoins
      let cStar := S.pke.encDet pk mStar rStar
      let (kReal, st₀) ← (init pk sk mStar rStar).run { gCache := [(mStar, rStar)] }
      let kRand ← S.sampleKey
      let (guess, _) ← (OracleComp.interpret (handler pk sk cStar)
        (A ⟨pk, cStar, if b then kRand else kReal⟩)).run st₀
      return guess) =
      S.chalOuter.bind fun t =>
        ((OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
          (fun q s => ProbComp.eval (handler t.1.1 t.1.2 (S.pke.encDet t.1.1 t.2.1 t.2.2.1) q s))
          (A ⟨t.1.1, S.pke.encDet t.1.1 t.2.1 t.2.2.1,
            if b then t.2.2.2.2 else t.2.2.2.1⟩)).run
          (initSt t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2.1)).map Prod.fst := by
  simp only [chalOuter, pmf_norm]
  congr 1 with keys : 1; congr 1 with mStar : 1; congr 1 with rStar : 1
  rw [hinit keys.1 keys.2 mStar rStar, PMF.bind_map]
  congr 1 with kq : 1; dsimp only [Function.comp_apply]; congr 1 with kRand : 1
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  rfl

private theorem eval_simFilterGame (S : Scheme PK SK M R CT K)
    (d : PK → List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K)
    (b : Bool) :
    ProbComp.eval (S.simFilterGame d A b) =
      S.chalOuter.bind fun t =>
        (S.simRun (d t.1.1) A t.1.1 (S.pke.encDet t.1.1 t.2.1 t.2.2.1)
          (if b then t.2.2.2.2 else t.2.2.2.1)
          { gCache := [(t.2.1, t.2.2.1)],
            hqCache := [(S.pke.encDet t.1.1 t.2.1 t.2.2.1, t.2.2.2.1)] }).map Prod.fst :=
  S.eval_chalGame_aux (fun pk _ m r => S.simHashH pk (false, m, S.pke.encDet pk m r))
    (fun pk _ m r kq => { gCache := [(m, r)], hqCache := [(S.pke.encDet pk m r, kq)] })
    (fun pk _ m r => S.eval_simHashH_init pk m r)
    (fun pk _ c => S.simFilterHandler (d pk) pk c) A b

private def chalPick (b : Bool) (t : (PK × SK) × M × R × K × K) : (PK × SK) × M × R × K :=
  (t.1, t.2.1, t.2.2.1, if b then t.2.2.2.2 else t.2.2.2.1)

omit [DecidableEq M] [DecidableEq CT] in
private theorem map_chalPick (S : Scheme PK SK M R CT K) (b : Bool) :
    S.chalOuter.map (chalPick b) = S.chalOuter4 := by
  cases b <;> simp only [chalOuter, chalOuter4, chalPick, PMF.map_bind, PMF.pure_map,
    Bool.false_eq_true, ↓reduceIte, PMF.bind_const]

omit [DecidableEq M] [DecidableEq CT] in
private theorem chalOuter4_bind_eq (S : Scheme PK SK M R CT K) (b : Bool) {α : Type}
    (g : (PK × SK) × M × R × K → PMF α) :
    S.chalOuter4.bind g = S.chalOuter.bind fun t => g (chalPick b t) := by
  rw [← S.map_chalPick b, PMF.bind_map]
  rfl

omit [DecidableEq M] [DecidableEq CT] in
private theorem advantage_chalOuter_le (S : Scheme PK SK M R CT K)
    (g : Bool → Game) {G : Bool → ((PK × SK) × M × R × K × K) → Game}
    (W : ((PK × SK) × M × R × K) → Game)
    {err : Bool → ((PK × SK) × M × R × K × K) → ℝ≥0∞} {B : ℝ≥0∞}
    (hg : ∀ b, g b = S.chalOuter.bind (G b))
    (hpt : ∀ b t, t ∈ S.chalOuter.support → CloseTo (G b t) (W (chalPick b t)) (err b t))
    (herr : ∀ b, (∑' t, S.chalOuter t * err b t) ≤ B) :
    (Game.advantage (g false) (g true) : ℝ≥0∞) ≤ 2 * B := by
  rw [two_mul]
  refine Game.closeTo_iff_coe_advantage_le.mp ?_
  have hclose (b : Bool) : CloseTo (g b) (S.chalOuter4.bind W) B := by
    rw [hg b, S.chalOuter4_bind_eq b W]
    exact (CloseTo.bind_right_tsum S.chalOuter (hpt b)).mono (herr b)
  exact (hclose false).trans (hclose true).symm

omit [DecidableEq M] [DecidableEq CT] in
private theorem mem_support_chalOuter (S : Scheme PK SK M R CT K)
    (t : (PK × SK) × M × R × K × K) (ht : t ∈ S.chalOuter.support) :
    t.1 ∈ (ProbComp.eval S.pke.keyGen).support := by
  supp_cases ht [chalOuter] with ⟨keys, hk, -, -, -, -, -, -, -, -, rfl⟩
  exact hk

private theorem genRun_hqCache_isSome (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (A : ROAdversary PK M R CT K) (pk : PK) (cStar : CT) (k : K)
    {x : Bool × SimState M R CT K}
    (hx : x ∈ (S.genRun d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) A pk cStar k
      {}).support)
    (hq : (x.2.hqCache.lookup cStar).isSome) : ∃ p ∈ x.2.gCache, t p.1 cStar p.2 := by
  refine OracleComp.run_interpret_invariant _ (fun st : SimState M R CT K =>
      (st.hqCache.lookup cStar).isSome → ∃ p ∈ st.gCache, t p.1 cStar p.2)
    (fun q s hs a s' h hq' => ?_) _ _ (by simp) x.1 x.2 hx hq
  obtain ⟨hsub, hhq⟩ := S.genHandler_step d t cStar q s a s' h
  exact (hhq hq').elim (fun h₁ => let ⟨p, hp, ht⟩ := hs h₁; ⟨p, hsub hp, ht⟩) id

private theorem simRun_eq_genRun (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K)
    (pk : PK) (cStar : CT) (k : K) (st : SimState M R CT K) :
    S.simRun d A pk cStar k st =
      S.genRun d (fun m c r => S.pke.encDet pk m r = c) (fun _ => S.pke.sampleCoins)
        (fun _ => S.sampleKey) A pk cStar k st := by
  simp only [simRun, genRun, simFilterHandler_eq_genHandler]

/-- For one draw of the outer randomness, the unprogrammed handler `genHandler d t` run from caches
preset with `G(mStar) = rStar` and `Hq(cStar) = kq` is close to its run from empty caches, within
the probability that the latter caches `G(mStar)` or `Hq(cStar)`. -/
private theorem closeTo_genRun_preset (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (A : ROAdversary PK M R CT K) (pk : PK) (mStar : M) (rStar : R) (cStar : CT) (kq k : K)
    (hd : ∀ L c, c ≠ cStar → LookupNoneOr mStar rStar L → d (ens mStar rStar L) c = d L c) :
    CloseTo
      ((S.genRun d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) A pk cStar k
        { gCache := [(mStar, rStar)], hqCache := [(cStar, kq)] }).map Prod.fst)
      ((S.genRun d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) A pk cStar k {}).map
        Prod.fst)
      ((S.genRun d t (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) A pk cStar k
        {}).toOuterMeasure {x | progBad mStar cStar x.2}) := by
  rw [genRun_preset_eq S d t A pk mStar rStar cStar kq k hd]
  have hiub := S.identicalUntilBad_genHandler d t (gs₁ := S.progG mStar rStar)
    (gs₂ := fun _ => S.pke.sampleCoins) (hs₁ := S.progHq cStar kq)
    (hs₂ := fun _ => S.sampleKey) (mStar := mStar) cStar (fun m hm => by simp [progG, hm])
    (fun c hc => by simp [progHq, hc])
  have h := (hiub.closeTo_run (A ⟨pk, cStar, k⟩) {}).map Prod.fst
  rw [hiub.bad_eq] at h; exact h

/-! ### The challenge hop of the keyless simulator

In the keyless simulator, `H(false, m, cStar)` reads `Hq(cStar)` whenever the cached coin `G(m)`
re-encrypts `m` to `cStar`, also for `m ≠ mStar`. `simRun_bad_le` bounds this collision by
`γ`-spreadness. The resulting hop `advantage_simFilterGame_le` is the challenge hop of the `FO^⊥`
proof; the `FO-notbot` proof takes its challenge hop with the decryption test instead (next
section) and needs no spreadness. -/

/-- **Bad-event split**: from the empty state, the simulator records `mStar` in
`gCache` or `cStar` in `hqCache` with probability at most that of recording `mStar`, plus
`(qG + qH) · 2^(-γ)` for a fresh coin re-encrypting to `cStar`. -/
private theorem simRun_bad_le (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH) {γ : ℝ} (hγ : S.pke.GammaSpread γ)
    {pk : PK} {sk : SK} (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support)
    (mStar : M) (cStar : CT) (k : K) :
    (S.simRun d A pk cStar k {}).toOuterMeasure
        {x | (x.2.gCache.lookup mStar).isSome ∨ (x.2.hqCache.lookup cStar).isSome} ≤
      (S.simRun d A pk cStar k {}).toOuterMeasure {x | (x.2.gCache.lookup mStar).isSome} +
        ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) := by
  set ε := ENNReal.ofReal ((2 : ℝ) ^ (-γ))
  set P := S.simRun d A pk cStar k {}
  refine (PMF.toOuterMeasure_mono P (fun x ⟨hx, hsupp⟩ => hx.imp id fun hx' =>
    S.genRun_hqCache_isSome d _ A pk cStar k (by rwa [← simRun_eq_genRun]) hx') :
      P.toOuterMeasure _ ≤ P.toOuterMeasure ({x | (x.2.gCache.lookup mStar).isSome} ∪
        {x | ∃ p ∈ x.2.gCache, S.pke.encDet pk p.1 p.2 = cStar})).trans
    ((MeasureTheory.measure_union_le _ _).trans ?_)
  gcongr
  refine (Cslib.OracleComp.toOuterMeasure_bad_le_two
    (bad := fun st : SimState M R CT K => ∃ p ∈ st.gCache, S.pke.encDet pk p.1 p.2 = cStar)
    ROQuery.gCost ROQuery.hCost (fun _ => ε) 0 0 ε
    (fun q s hs => S.simHandler_reEnc_le d hγ hpk cStar q s hs) (fun _ _ _ _ _ _ => by simp)
    (hq ⟨pk, cStar, k⟩).1 (hq ⟨pk, cStar, k⟩).2 (s := {}) (by simp)).trans_eq ?_
  push_cast; ring

/-- For one draw of the outer randomness, the simulator run from the preset `simFilterGame` caches
is close to the run from empty caches, within the probability of caching `G(mStar)` plus the
`γ`-spreadness term. -/
private theorem closeTo_simRun_preset (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH) {γ : ℝ} (hγ : S.pke.GammaSpread γ)
    {pk : PK} {sk : SK} (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support)
    (mStar : M) (rStar : R) (cStar : CT) (kq k : K)
    (hd : ∀ L c, c ≠ cStar → LookupNoneOr mStar rStar L → d (ens mStar rStar L) c = d L c) :
    CloseTo
      ((S.simRun d A pk cStar k { gCache := [(mStar, rStar)], hqCache := [(cStar, kq)] }).map
        Prod.fst)
      ((S.simRun d A pk cStar k {}).map Prod.fst)
      (((S.simRun d A pk cStar k {}).map fun x => (x.2.gCache.lookup mStar).isSome) true +
        ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  have h := S.closeTo_genRun_preset d (fun m c r => S.pke.encDet pk m r = c) A pk mStar rStar
    cStar kq k hd
  rw [← simRun_eq_genRun, ← simRun_eq_genRun] at h
  refine h.mono ((S.simRun_bad_le d A hq hγ hpk mStar cStar k).trans (le_of_eq ?_))
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]; rfl

/-- **Filtered challenge hop**: if the PKE is `γ`-spread and the decapsulation filter `d` is
invariant under programming `(mStar, rStar)` at ciphertexts `c ≠ Enc(pk, mStar; rStar)`, then for
every adversary making at most `qG` queries to `G` and `qH` queries to `H`, the advantage between
`simFilterGame d A false` and `simFilterGame d A true` is at most
`2 Pr[simFilterOwExperiment d A] + 2 (qG + qH) 2^(-γ)`. -/
theorem advantage_simFilterGame_le (S : Scheme PK SK M R CT K)
    (d : PK → List (M × R) → CT → Bool)
    (hd : ∀ pk mStar rStar L c, c ≠ S.pke.encDet pk mStar rStar →
      LookupNoneOr mStar rStar L → d pk (ens mStar rStar L) c = d pk L c)
    (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {γ : ℝ} (hγ : S.pke.GammaSpread γ) :
    (Game.advantage (ProbComp.eval (S.simFilterGame d A false))
        (ProbComp.eval (S.simFilterGame d A true)) : ℝ) ≤
      2 * Pr[S.simFilterOwExperiment d A] + 2 * (((qG : ℝ) + qH) * (2 : ℝ) ^ (-γ)) := by
  classical
  set ε : ℝ≥0∞ := ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) with hε
  set OW : ((PK × SK) × M × R × K) → PMF Bool := fun u =>
    (S.simRun (d u.1.1) A u.1.1 (S.pke.encDet u.1.1 u.2.1 u.2.2.1) u.2.2.2 {}).map
      fun x => (x.2.gCache.lookup u.2.1).isSome
  set H : ℝ≥0∞ := (S.chalOuter4.bind OW) true with hH
  have hle : (Game.advantage (ProbComp.eval (S.simFilterGame d A false))
      (ProbComp.eval (S.simFilterGame d A true)) : ℝ≥0∞) ≤ 2 * (H + ε) :=
    S.advantage_chalOuter_le (fun b => ProbComp.eval (S.simFilterGame d A b))
      (fun u => (S.simRun (d u.1.1) A u.1.1 (S.pke.encDet u.1.1 u.2.1 u.2.2.1)
        u.2.2.2 {}).map Prod.fst)
      (err := fun b t => OW (chalPick b t) true + ε) (S.eval_simFilterGame d A)
      (fun b t ht => S.closeTo_simRun_preset (d t.1.1) A hq hγ (S.mem_support_chalOuter t ht)
        _ _ _ _ _ (hd t.1.1 t.2.1 t.2.2.1))
      fun b => by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        rw [← PMF.bind_apply, hH, ← S.chalOuter4_bind_eq b OW]
  have hHtop : H ≠ ⊤ := PMF.apply_ne_top _ _
  rw [hε] at hle; ennreal_to_real at hle
  rw [show H = ProbComp.eval (S.simFilterOwExperiment d A) true by
    rw [hH, eval_simFilterOwExperiment], Nat.cast_add] at hle
  linarith

/-! ### The challenge hop with the decryption test

The coupled handler tests `Dec(sk, c) = some m` besides re-encryption. When the challenge
`cStar = Enc(pk, mStar; rStar)` decrypts to `mStar`, a query `H(false, m, cStar)` therefore reads
`Hq(cStar)` only for `m = mStar`, so the coupled run caches `Hq(cStar)` only after `G(mStar)`
(`coupledRun_progBad_le`). The decryption test is removed afterwards, inside the run from empty
caches (`coupledRun_hit_le`), at the cost of the decryption failures of the cached coins. -/

/-- The coupled handler `coupledFilterHandler d pk sk cStar`, evaluated to `PMF`, run on
`A ⟨pk, cStar, k⟩` from the state `st`. -/
private noncomputable def coupledRun (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (A : ROAdversary PK M R CT K) (pk : PK) (sk : SK) (cStar : CT) (k : K)
    (st : SimState M R CT K) : PMF (Bool × SimState M R CT K) :=
  (OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
    (fun q s => ProbComp.eval (S.coupledFilterHandler d pk sk cStar q s)) (A ⟨pk, cStar, k⟩)).run st

private theorem coupledRun_eq_genRun (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K)
    (pk : PK) (sk : SK) (cStar : CT) (k : K) (st : SimState M R CT K) :
    S.coupledRun d A pk sk cStar k st =
      S.genRun d (fun m c r => S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m)
        (fun _ => S.pke.sampleCoins) (fun _ => S.sampleKey) A pk cStar k st := by
  simp only [coupledRun, genRun, coupledFilterHandler_eq_genHandler]

/-- When the challenge `Enc(pk, mStar; rStar)` decrypts to `mStar`, every supported final state of
the coupled run from empty caches that caches `G(mStar)` or `Hq(Enc(pk, mStar; rStar))` caches
`G(mStar)`. -/
private theorem coupledRun_progBad_le (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K) (pk : PK) (sk : SK)
    (mStar : M) (rStar : R) (k : K)
    (hr : S.pke.dec sk (S.pke.encDet pk mStar rStar) = some mStar) :
    (S.coupledRun d A pk sk (S.pke.encDet pk mStar rStar) k {}).toOuterMeasure
        {x | progBad mStar (S.pke.encDet pk mStar rStar) x.2} ≤
      (S.coupledRun d A pk sk (S.pke.encDet pk mStar rStar) k {}).toOuterMeasure
        {x | (x.2.gCache.lookup mStar).isSome} := by
  rw [coupledRun_eq_genRun]
  refine PMF.toOuterMeasure_mono _ fun x ⟨hx, hsupp⟩ => hx.elim id fun hx => ?_
  obtain ⟨p, hp, -, hdec⟩ := S.genRun_hqCache_isSome d _ A pk _ k hsupp hx
  exact List.lookup_isSome_iff.mpr
    ⟨p, hp, Option.some.inj (hr.symm.trans hdec) ▸ beq_self_eq_true mStar⟩

/-- **Removing the decryption test from the run from empty caches** (the correctness step of
[HofheinzHoevelmannsKiltz2017], proof of Theorem 3.1, games G1–G2): the coupled run caches
`G(mStar)` with probability at most that of the keyless run plus `qG + qH` times the worst-message
decryption failure probability of the key pair. -/
private theorem coupledRun_hit_le [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) (pk : PK) (sk : SK) (mStar : M) (cStar : CT) (k : K) :
    (S.coupledRun d A pk sk cStar k {}).toOuterMeasure {x | (x.2.gCache.lookup mStar).isSome} ≤
      (S.simRun d A pk cStar k {}).toOuterMeasure {x | (x.2.gCache.lookup mStar).isSome} +
        ((qG + qH : ℕ) : ℝ≥0∞) * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  have h := S.closeTo_run_coupledFilterHandler_simFilterHandler pk sk cStar d d
    (fun _ _ _ => rfl) (A ⟨pk, cStar, k⟩) (hq.ghCost _) (st := {}) (fun _ he => by simp at he)
    PMF.pure
  simp only [PMF.bind_pure] at h
  exact h _

/-- The state of `coupledGame` after the real key `kq` is computed: `Hq(cStar) = kq` when the
challenge `cStar = Enc(pk, mStar; rStar)` decrypts to `mStar`, and `H(false, mStar, cStar) = kq`
otherwise. -/
private def coupledInit (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (mStar : M) (rStar : R)
    (kq : K) : SimState M R CT K :=
  if S.pke.dec sk (S.pke.encDet pk mStar rStar) = some mStar then
    { gCache := [(mStar, rStar)], hqCache := [(S.pke.encDet pk mStar rStar, kq)] }
  else
    { gCache := [(mStar, rStar)], hCache := [((false, mStar, S.pke.encDet pk mStar rStar), kq)] }

/-- The real-key computation of `coupledGame` stores a fresh key `kq` and returns it. -/
private theorem eval_coupledHashH_run_init (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (mStar : M) (rStar : R) :
    ProbComp.eval ((S.coupledHashH pk sk (false, mStar, S.pke.encDet pk mStar rStar)).run
        { gCache := [(mStar, rStar)] }) =
      (ProbComp.eval S.sampleKey).map fun kq => (kq, S.coupledInit pk sk mStar rStar kq) := by
  change ProbComp.eval (simHashG S.pke.sampleCoins mStar { gCache := [(mStar, rStar)] } >>=
    fun z => (if S.pke.encDet pk mStar z.1 = S.pke.encDet pk mStar rStar ∧
        S.pke.dec sk (S.pke.encDet pk mStar rStar) = some mStar then
      simHashHq S.sampleKey (S.pke.encDet pk mStar rStar)
      else simHashHRaw S.sampleKey (false, mStar, S.pke.encDet pk mStar rStar)) z.2) = _
  rw [ProbComp.eval_bind, eval_simHashG_singleton, PMF.pure_bind]
  by_cases hr : S.pke.dec sk (S.pke.encDet pk mStar rStar) = some mStar <;>
    simp only [hr, true_and, ↓reduceIte, coupledInit, simHashHq, simHashHRaw,
      RandomOracle.eval_zoomStateT_memoize, memoize, List.lookup_nil, pmf_norm] <;> rfl

private theorem eval_coupledGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) :
    ProbComp.eval (S.coupledGame A b) = S.chalOuter.bind fun t =>
      (S.coupledRun (fun _ _ => true) A t.1.1 t.1.2 (S.pke.encDet t.1.1 t.2.1 t.2.2.1)
        (if b then t.2.2.2.2 else t.2.2.2.1)
        (S.coupledInit t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2.1)).map Prod.fst :=
  S.eval_chalGame_aux (fun pk sk m r => S.coupledHashH pk sk (false, m, S.pke.encDet pk m r))
    (fun pk sk m r kq => S.coupledInit pk sk m r kq)
    (fun pk sk m r => S.eval_coupledHashH_run_init pk sk m r)
    (fun pk sk c => S.coupledFilterHandler (fun _ _ => true) pk sk c) A b

omit [DecidableEq CT] in
/-- The challenge decryption failures average to at most the expected worst-message failure
probability of key generation. -/
private theorem tsum_chalOuter_fail_le [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K) :
    ∑' t, S.chalOuter t *
        (if S.pke.dec t.1.2 (S.pke.encDet t.1.1 t.2.1 t.2.2.1) = some t.2.1 then 0 else 1) ≤
      S.pke.keyGen.expect fun x => ENNReal.ofReal (S.pke.keyPairMaxFailProb x.1 x.2) := by
  have hproj : S.chalOuter.map (fun t => (t.1, t.2.1, t.2.2.1)) =
      (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun mStar =>
      (ProbComp.eval S.pke.sampleCoins).bind fun rStar => PMF.pure (keys, mStar, rStar) := by
    simp only [chalOuter, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  rw [← Cslib.Probability.PMF.tsum_map_mul S.chalOuter (fun t => (t.1, t.2.1, t.2.2.1))
      (fun u => if S.pke.dec u.1.2 (S.pke.encDet u.1.1 u.2.1 u.2.2) = some u.2.1 then 0 else 1),
    hproj, Cslib.Probability.PMF.tsum_bind_mul, ProbComp.expect]
  refine tsum_le_tsum fun keys => mul_le_mul_right ?_ _
  rw [Cslib.Probability.PMF.tsum_bind_mul]
  refine Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ fun mStar => ?_
  rw [Cslib.Probability.PMF.tsum_bind_mul]
  refine (le_of_eq ?_).trans (ENNReal.ofReal_le_ofReal
    (S.pke.msgFailProb_le_keyPairMaxFailProb keys.1 keys.2 mStar))
  rw [ExplicitCoinPKE.msgFailProb,
    ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _), PMF.toOuterMeasure_apply]
  refine tsum_congr fun r => ?_
  simp only [PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  by_cases h : S.pke.dec keys.2 (S.pke.encDet keys.1 mStar r) = some mStar <;>
    simp [h, Set.indicator]

/-- **Challenge hop of the `FO-notbot` IND-CCA proof** ([HofheinzHoevelmannsKiltz2017], game G3 of
the proof of Theorem 3.4, with the plaintext-checking oracle removed from the one-wayness run as in
games G1–G2 of the proof of Theorem 3.1): for a `δ`-correct PKE and every adversary making at most
`qG` queries to `G` and `qH` queries to `H`, the advantage between the coupled games
`coupledGame A false` and `coupledGame A true` is at most
`2 Pr[simFilterOwExperiment A] + 2 (qG + qH + 1) δ`. No spreadness is needed: the coupled
key-derivation oracle reads the challenge key only after `G(m*)` is queried, unless the challenge
itself fails to decrypt. -/
theorem advantage_coupledGame_le [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) {qG qH : ℕ} (hq : ROQueryBounds A qG qH) {δ : ℝ}
    (hδ : S.pke.DeltaCorrect δ) :
    (Game.advantage (ProbComp.eval (S.coupledGame A false))
        (ProbComp.eval (S.coupledGame A true)) : ℝ) ≤
      2 * Pr[S.simFilterOwExperiment (fun _ _ _ => true) A] +
        2 * ((qG + qH + 1 : ℕ) : ℝ) * δ := by
  classical
  set fF : ((PK × SK) × M × R × K × K) → ℝ≥0∞ := fun t =>
    if S.pke.dec t.1.2 (S.pke.encDet t.1.1 t.2.1 t.2.2.1) = some t.2.1 then 0 else 1
  set OW : ((PK × SK) × M × R × K) → PMF Bool := fun u =>
    (S.simRun (fun _ _ => true) A u.1.1 (S.pke.encDet u.1.1 u.2.1 u.2.2.1) u.2.2.2 {}).map
      fun x => (x.2.gCache.lookup u.2.1).isSome
  set fE : (PK × SK) → ℝ≥0∞ := fun x => ENNReal.ofReal (S.pke.keyPairMaxFailProb x.1 x.2)
  set E : ℝ≥0∞ := S.pke.keyGen.expect fE with hE
  set H : ℝ≥0∞ := (S.chalOuter4.bind OW) true with hH
  have hEtop : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top <| hE ▸
    Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ fun x =>
      ENNReal.ofReal_le_one.mpr (S.pke.keyPairMaxFailProb_le_one x.1 x.2)
  have hHtop : H ≠ ⊤ := PMF.apply_ne_top _ _
  have hle : (Game.advantage (ProbComp.eval (S.coupledGame A false))
      (ProbComp.eval (S.coupledGame A true)) : ℝ≥0∞) ≤
      2 * (H + ((qG + qH + 1 : ℕ) : ℝ≥0∞) * E) := by
    refine S.advantage_chalOuter_le (fun b => ProbComp.eval (S.coupledGame A b))
      (fun u => (S.coupledRun (fun _ _ => true) A u.1.1 u.1.2
        (S.pke.encDet u.1.1 u.2.1 u.2.2.1) u.2.2.2 {}).map Prod.fst)
      (err := fun b t => fF t + OW (chalPick b t) true + ((qG + qH : ℕ) : ℝ≥0∞) * fE t.1)
      (S.eval_coupledGame A) (fun b ⟨⟨pk, sk⟩, mStar, rStar, kq, kRand⟩ _ => ?_) fun b => ?_
    · dsimp only [fF, OW, chalPick]
      by_cases hr : S.pke.dec sk (S.pke.encDet pk mStar rStar) = some mStar
      · simp only [coupledInit, hr, ↓reduceIte, zero_add]
        have h := S.closeTo_genRun_preset (fun _ _ => true)
          (fun m c r => S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m) A pk mStar rStar
          (S.pke.encDet pk mStar rStar) kq (if b then kRand else kq) fun _ _ _ _ => rfl
        rw [← coupledRun_eq_genRun, ← coupledRun_eq_genRun] at h
        refine h.mono ((S.coupledRun_progBad_le _ A pk sk mStar rStar _ hr).trans
          ((S.coupledRun_hit_le _ A hq pk sk mStar _ _).trans (le_of_eq ?_)))
        rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]; rfl
      · simp only [hr, ↓reduceIte]
        exact fun e => (Probability.PMF.toOuterMeasure_le_one _ e).trans
          (le_add_left (le_add_right (le_add_right le_rfl)))
    · have hH_eq : (∑' t, S.chalOuter t * OW (chalPick b t) true) = H := by
        rw [hH, S.chalOuter4_bind_eq b, PMF.bind_apply]
      have hE_eq : (∑' t, S.chalOuter t * fE t.1) = E := by
        rw [hE, ProbComp.expect,
          show ProbComp.eval S.pke.keyGen = S.chalOuter.map Prod.fst by
            simp only [chalOuter, PMF.map_bind, PMF.pure_map, PMF.bind_const, PMF.bind_pure],
          Cslib.Probability.PMF.tsum_map_mul S.chalOuter Prod.fst fE]
      simp only [mul_add, tsum_add, mul_left_comm _ ((qG + qH : ℕ) : ℝ≥0∞), ENNReal.tsum_mul_left,
        hH_eq, hE_eq]
      calc (∑' t, S.chalOuter t * fF t) + H + ((qG + qH : ℕ) : ℝ≥0∞) * E
        _ ≤ E + H + ((qG + qH : ℕ) : ℝ≥0∞) * E := by gcongr; exact S.tsum_chalOuter_fail_le
        _ = H + ((qG + qH + 1 : ℕ) : ℝ≥0∞) * E := by push_cast; ring
  rw [mul_add] at hle; ennreal_to_real at hle
  rw [show H = ProbComp.eval (S.simFilterOwExperiment (fun _ _ _ => true) A) true by
    rw [hH, eval_simFilterOwExperiment]] at hle
  have := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg (qG + qH + 1))
  linarith

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
