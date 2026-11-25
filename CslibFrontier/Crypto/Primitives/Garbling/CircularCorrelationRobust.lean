/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.OneHot
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Probability.PMF.Uniform

/-!
# Circular correlation robustness

A tweakable hash `H : L → T → M` is *circular correlation robust* when, for a secret offset drawn
from a key, the oracle that answers a query `(x, t, b)` with `H (x + Δ) t`, plus the output offset
`Δ'` when `b` is set, looks like a uniform random function. Choi, Katz, Kumaresan and Zhou
[ChoiKatzKumaresanZhou2012] introduced circular correlation robustness to prove the Free-XOR
technique of Kolesnikov and Schneider [KolesnikovSchneider2008] secure; Guo, Katz, Wang and Yu
[GuoKatzWangYu2020] gave the tweakable form, and Zahur, Rosulek and Evans [ZahurRosulekEvans2015]
and Heath, Kolesnikov and Ng [HeathKolesnikovNg2024], Definition 1, use it for half gates and
one-hot garbling.

`CCR.oracle H Δ Δ' q` is that oracle, with the input offset `Δ : L` and the output offset
`Δ' : M` given separately, and `CCR.advantage H δ δ' A` is the advantage of `A` in telling
`CCR.oracle H (δ k) (δ' k)` under a uniform key `k` from a uniform random function, in the finite
PRF game `Cslib.Crypto.PRF.advantage`. Three Boolean garbling schemes of this library rest on it
(the point-and-permute scheme of `Cslib.Crypto.Garbling.Privacy` rests on PRF security instead):

* Free-XOR (`Cslib.Crypto.Garbling.FreeXOR`): the hash reads only a key `x : K`, labels are
  `K × Bool`, and the offsets are `δ` and `(δ, true)`.
* half gates (`Cslib.Crypto.Garbling.HalfGates`): the hash reads the whole label, colour bit
  included, and both offsets are `CCR.offset δ = (δ, true)`.
* one-hot garbling (`Cslib.Crypto.Garbling.BinaryToOneHot`): labels form a `ZMod 2`-module, both
  offsets are `δ k` for a key map `δ`, which can fix the colour bit of the offset.

The input and output offsets live in different groups only for Free-XOR, whose hash ignores the
colour bit. Reading that hash on whole labels instead would make the assumption false: the distinct
queries `((x, false), t, b)` and `((x, true), t, b)` would get equal answers, which a uniform random
function rarely gives.

Heath's arithmetic garbling [Heath2024] uses an arithmetic variant (`CCR.Arithmetic`): labels lie
in an `R`-module, the shift is a scalar, and the ideal oracle answers every query with a fresh
uniform label. It is a different assumption, and no implication between it and `CCR.advantage` is
formalized. The mixed-modulus assumption of Ball, Malkin and Rosulek [BallMalkinRosulek2016],
Definition 1, has its own dependent query type and lives in
`Cslib.Crypto.Garbling.MixedModulus`.

## Main definitions

* `Cslib.Crypto.Garbling.CCR.Query`: a query of a label, a tweak and a bit.
* `Cslib.Crypto.Garbling.CCR.offset`: the half-gates offset `(R, true)`.
* `Cslib.Crypto.Garbling.CCR.oracle`: the circular oracle under an input and an output offset.
* `Cslib.Crypto.Garbling.CCR.advantage`: the circular correlation robustness advantage.
* `Cslib.Crypto.Garbling.CCR.IsTweakUnique`: tweak uniqueness for Boolean CCR adversaries (at most
  one query per tweak on every execution path).
* `Cslib.Crypto.Garbling.CCR.idealFreshGame`: the fresh-uniform-per-query ideal game, equivalent to
  `PRF.idealExperiment` on tweak-unique adversaries
  (`idealFreshGame_eq_prfIdealGame_of_isTweakUnique`).
* `Cslib.Crypto.Garbling.CCR.keyOnlyEmbed`, `Cslib.Crypto.Garbling.CCR.keyOnlyHandler`: lifting
  key-only CCR queries `(x, t, b)` into full-label queries `((x, true), t, b)`.
* `Cslib.Crypto.Garbling.CCR.Arithmetic.advantage`: the arithmetic variant, with
  `Cslib.Crypto.Garbling.CCR.Arithmetic.IsTweakUnique`.

## Main results

* `Cslib.ProbOracleComp.runWith_memoize_map_fst_eq_eval_run`: lazily memoizing an oracle agrees
  with fresh-per-query execution whenever each tweak is queried at most once on every path.
* `Cslib.Crypto.Garbling.CCR.idealFreshGame_eq_prfIdealGame_of_isTweakUnique`,
  `Cslib.Crypto.Garbling.CCR.Arithmetic.idealGame_eq_runWith_memoize_of_isTweakUnique`:
  fresh-uniform ideal games equal random-function (`PRF` / `memoize`) ideal games on tweak-unique
  adversaries.
* `Cslib.Crypto.Garbling.CCR.advantage_keyOnly`: key-only CCR advantage transfers to full-label
  CCR advantage.

## Implementation notes

The definition of [GuoKatzWangYu2020] only allows adversaries that never ask both `(x, t, false)`
and `(x, t, true)`, whose answers reveal the offset (`CCR.oracle_true_sub_oracle_false`). Here
`advantage` is defined for every adversary, and the restriction `IsTweakUnique` is stated as a
property of the adversary at hand: the Free-XOR (`FreeXOR.isTweakUnique_reduction`), half-gates
(`HalfGates.isTweakUnique_reduction`) and one-hot (`BinaryToOneHot.isTweakUnique_reduction`)
reductions ask every tweak at most once. The same holds for the arithmetic variant, whose
restriction `Arithmetic.IsTweakUnique` is likewise formalized.

## References

* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [D. Heath, V. Kolesnikov, L. K. L. Ng, *Garbled Circuit Lookup Tables with Logarithmic Number of
  Ciphertexts*][HeathKolesnikovNg2024]
* [D. Heath, *Efficient Arithmetic in Garbled Circuits*][Heath2024]
* [M. Ball, T. Malkin, M. Rosulek, *Garbling Gadgets for Boolean and Arithmetic
  Circuits*][BallMalkinRosulek2016]
-/

public section

namespace Cslib.ProbOracleComp

private theorem runWith_memoize_map_fst_eq_eval_run_aux {D R α : Type} [DecidableEq D]
    (O : D → ProbComp R) (A : ProbOracleComp (fun _ : D => R) α) (cache : List (D × R))
    (h1 : ∀ d : D, OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) fun q : D => if q = d then 1 else 0) A 1)
    (h0 : ∀ d : D, (cache.lookup d).isSome = true → OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) fun q : D => if q = d then 1 else 0) A 0) :
    (ProbOracleComp.runWith (memoize fun q => ProbComp.eval (O q)) A cache).map Prod.fst =
      ProbComp.eval (A.run O) := by
  induction A using ProbOracleComp.induction generalizing cache with
  | pure a =>
    rw [ProbOracleComp.runWith_pure, PMF.pure_map, ProbOracleComp.run_pure, ProbComp.eval_pure]
  | sample_bind n cont ih =>
    rw [ProbOracleComp.runWith_sample_bind, PMF.map_bind, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbComp.eval_bind]
    refine congrArg _ (funext fun i => ih i cache (fun d => ?_) (fun d hd => ?_))
    · have hd1 := h1 d
      rw [ProbOracleComp.sample_unifFin] at hd1
      exact (OracleComp.IsCostBounded.liftBind_iff.mp hd1).2 i
    · have hd0 := h0 d hd
      rw [ProbOracleComp.sample_unifFin] at hd0
      exact (OracleComp.IsCostBounded.liftBind_iff.mp hd0).2 i
  | query_bind q cont ih =>
    have hnone : cache.lookup q = none := by
      cases hlook : cache.lookup q with
      | none => rfl
      | some v =>
        simpa using (OracleComp.IsCostBounded.liftBind_iff.mp (h0 q (by simp [hlook]))).1
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      memoize_of_none _ _ _ hnone, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
      ProbOracleComp.run_bind, ProbOracleComp.run_query, ProbComp.eval_bind]
    refine congrArg _ (funext fun v => ih v ((q, v) :: cache)
      (fun d => ((OracleComp.IsCostBounded.liftBind_iff.mp (h1 d)).2 v).mono (Nat.sub_le _ _))
      fun d hd => ?_)
    by_cases hdq : d = q
    · subst hdq
      simpa using (OracleComp.IsCostBounded.liftBind_iff.mp (h1 d)).2 v
    · rw [List.lookup_cons, beq_eq_false_iff_ne.mpr hdq] at hd
      exact ((OracleComp.IsCostBounded.liftBind_iff.mp (h0 d hd)).2 v).mono (Nat.sub_le _ _)

/-- If an oracle computation queries each tweak `tweak q` at most once on every path, lazily
memoizing `fun q => ProbComp.eval (O q)` produces the same output distribution as running `A`
against fresh calls to `O`. -/
theorem runWith_memoize_map_fst_eq_eval_run {D T R α : Type} [DecidableEq D] [DecidableEq T]
    (tweak : D → T) (O : D → ProbComp R) {A : ProbOracleComp (fun _ : D => R) α}
    (h : ∀ t : T, OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) fun q : D => if tweak q = t then 1 else 0) A 1) :
    (ProbOracleComp.runWith (memoize fun q => ProbComp.eval (O q)) A []).map Prod.fst =
      ProbComp.eval (A.run O) := by
  refine runWith_memoize_map_fst_eq_eval_run_aux O A [] (fun d => (h (tweak d)).of_le ?_)
    fun _ hd => by simp at hd
  rintro (_ | q)
  · exact le_rfl
  · by_cases hqd : q = d <;> simp [hqd]

end Cslib.ProbOracleComp

namespace Cslib.Crypto.Garbling.CCR

/-- A query to the circular oracle: a label, a tweak and a bit. -/
structure Query (L T : Type) where
  /-- The label, shifted by the input offset before hashing. -/
  label : L
  /-- The tweak passed to the hash. -/
  tweak : T
  /-- Whether the answer also gets the output offset. -/
  bit : Bool
  deriving DecidableEq, Fintype

/-- Adversaries against circular correlation robustness: oracle algorithms with private coins
that ask queries of a label, a tweak and a bit, get answers in `M`, and output a guess. -/
abbrev Adversary (L T M : Type) : Type := PRF.Adversary (Query L T) M

/-- The global offset `Δ = (R, true)` of the half-gates instance, of colour `true`: the colour
plays the role of the least significant bit, which [ZahurRosulekEvans2015] fixes to `1`
(`R ∈ {0, 1}^(k - 1) 1` in Definition 1). -/
@[expose] def offset {K : Type} (R : K) : K × Bool := (R, true)

variable {L T M Key : Type} [AddCommGroup L] [AddCommGroup M]

/-- The circular oracle under the input offset `Δ` and the output offset `Δ'`: the query
`(x, t, b)` gets `H (x + Δ) t`, plus `Δ'` when `b` is set. -/
@[expose] def oracle (H : L → T → M) (Δ : L) (Δ' : M) (q : Query L T) : M :=
  H (q.label + Δ) q.tweak + bitOffset Δ' q.bit

@[simp] theorem oracle_apply (H : L → T → M) (Δ : L) (Δ' : M) (x : L) (t : T) (b : Bool) :
    oracle H Δ Δ' ⟨x, t, b⟩ = H (x + Δ) t + bitOffset Δ' b :=
  rfl

/-- The answers to `(x, t, true)` and `(x, t, false)` differ by the output offset, so an
adversary that asks both learns it. -/
theorem oracle_true_sub_oracle_false (H : L → T → M) (Δ : L) (Δ' : M) (x : L) (t : T) :
    oracle H Δ Δ' ⟨x, t, true⟩ - oracle H Δ Δ' ⟨x, t, false⟩ = Δ' := by
  rw [oracle_apply, oracle_apply, bitOffset_true, bitOffset_false, add_zero, add_sub_cancel_left]

/-- The keyed circular oracle: the key `k` selects the input offset `δ k` and the output offset
`δ' k`. -/
@[expose] def keyed (H : L → T → M) (δ : Key → L) (δ' : Key → M) (k : Key) : Query L T → M :=
  oracle H (δ k) (δ' k)

/-- The circular correlation robustness advantage of `A` against `H` with offsets `δ` and `δ'`:
its advantage in telling the keyed circular oracle under a uniform key from a uniform random
function. -/
@[expose] noncomputable def advantage [Fintype Key] [Nonempty Key] [Fintype L] [DecidableEq L]
    [Fintype T] [DecidableEq T] [Fintype M] [Nonempty M] (H : L → T → M) (δ : Key → L)
    (δ' : Key → M) (A : Adversary L T M) : NNReal :=
  PRF.advantage (keyed H δ δ') A

/-- The adversary never repeats a tweak: on every path it makes at most one query with each
tweak `t`. In particular, it never queries both `(x, t, false)` and `(x, t, true)`. -/
@[expose] def IsTweakUnique [DecidableEq T] (A : Adversary L T M) : Prop :=
  ∀ t : T, OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) fun q : Query L T => if q.tweak = t then 1 else 0) A 1

omit [AddCommGroup L] [AddCommGroup M] in
/-- Against every stateful oracle, a tweak-unique adversary records at most one query with each
tweak `t` on every supported execution. -/
theorem IsTweakUnique.transcript_tweak_le_one [DecidableEq T] {A : Adversary L T M}
    (h : IsTweakUnique A) {State : Type}
    (oracle : (q : Query L T) → StateT State PMF M) {s s' : State} {result : Bool}
    {transcript : OracleComp.Transcript fun _ : Query L T => M}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle) A (s, [])).support)
    (t : T) :
    (transcript.map fun entry => if entry.1.tweak = t then 1 else 0).sum ≤ 1 :=
  ProbOracleComp.transcript_cost_le (h t) oracle hmem

omit [AddCommGroup L] [AddCommGroup M] in
/-- The fresh-uniform ideal experiment: answer every query with an independent uniform draw from
`M`. -/
@[expose] noncomputable def idealFreshGame [Fintype M] [Nonempty M] (A : Adversary L T M) : Game :=
  ProbComp.eval (A.run fun _ => ProbComp.uniform M)

omit [AddCommGroup L] [AddCommGroup M] in
/-- For a tweak-unique adversary, answering every query with a fresh uniform draw from `M`
(`idealFreshGame`) has the same output law as a uniform random function (`PRF.idealExperiment`). -/
theorem idealFreshGame_eq_prfIdealGame_of_isTweakUnique [Fintype L] [DecidableEq L] [Fintype T]
    [DecidableEq T] [Fintype M] [Nonempty M] {A : Adversary L T M} (h : IsTweakUnique A) :
    idealFreshGame A = ProbComp.eval (PRF.idealExperiment A) := by
  rw [PRF.eval_idealExperiment_eq_runWith_memoize, idealFreshGame]
  simpa only [ProbComp.eval_uniform] using
    (ProbOracleComp.runWith_memoize_map_fst_eq_eval_run Query.tweak
      (fun _ => ProbComp.uniform M) h).symm

omit [AddCommGroup L] [AddCommGroup M] in
/-- Library construction (no cited definition): embedding of key-only queries into full-label
queries via colour bit `true`. -/
@[expose] def keyOnlyEmbed (L T : Type) : Query L T ↪ Query (L × Bool) T where
  toFun q := ⟨(q.label, true), q.tweak, q.bit⟩
  inj' := by
    rintro ⟨x, t, b⟩ ⟨x', t', b'⟩ h
    simp only [Query.mk.injEq, Prod.mk.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl

omit [AddCommGroup L] [AddCommGroup M] in
/-- Library construction (no cited definition): lift a key-only CCR query to a full-label CCR
query via `keyOnlyEmbed`, so that adding the offset `(R, true)` cancels the colour bit to
`false`. -/
@[expose] def keyOnlyHandler {L T M : Type} (q : Query L T) :
    ProbOracleComp (fun _ : Query (L × Bool) T => M) M :=
  ProbOracleComp.query (keyOnlyEmbed L T q)

private theorem oracle_keyOnly (H : L × Bool → T → M) (R : L) (Δ' : M) (q : Query L T) :
    oracle H (R, true) Δ' (keyOnlyEmbed L T q) =
      oracle (fun x t => H (x, false) t) R Δ' q := by
  change H (q.label + R, true + true) q.tweak + bitOffset Δ' q.bit = _
  rw [show (true + true : Bool) = false by decide]; rfl

/-- Library infrastructure (no cited result): **Key-only CCR advantage transfer.** For any key-only
adversary `A` against `fun x t => H (x, false) t` with input offset `δ` and output offset `δ'`,
lifting its queries via `keyOnlyHandler` preserves its CCR advantage against `H` with input offset
`fun r => (δ r, true)` and output offset `δ'`. -/
theorem advantage_keyOnly [Fintype Key] [Nonempty Key] [Fintype L] [DecidableEq L]
    [Fintype T] [DecidableEq T] [Fintype M] [Nonempty M]
    (H : L × Bool → T → M) (δ : Key → L) (δ' : Key → M) (A : Adversary L T M) :
    advantage (fun x t => H (x, false) t) δ δ' A =
      advantage H (fun r => (δ r, true)) δ' (ProbOracleComp.simulate keyOnlyHandler A) := by
  have hreal : ProbComp.eval (PRF.realExperiment (keyed H (fun r => (δ r, true)) δ')
      (ProbOracleComp.simulate keyOnlyHandler A)) =
      ProbComp.eval (PRF.realExperiment (keyed (fun x t => H (x, false) t) δ δ') A) := by
    simp only [PRF.realExperiment, ProbOracleComp.run_simulate, ProbComp.eval_bind,
      ProbComp.eval_uniform, keyOnlyHandler, ProbOracleComp.run_query, keyed, oracle_keyOnly]
  have hideal : ProbComp.eval (PRF.idealExperiment (ProbOracleComp.simulate keyOnlyHandler A)) =
      ProbComp.eval (PRF.idealExperiment A) := by
    simp only [PRF.idealExperiment, ProbOracleComp.run_simulate, ProbComp.eval_bind,
      ProbComp.eval_uniform]
    rw [show (fun f : Query (L × Bool) T → M =>
        ProbComp.eval (A.run fun q => (keyOnlyHandler q).run fun q' => pure (f q'))) =
        (fun g : Query L T → M => ProbComp.eval (A.run fun q => pure (g q))) ∘
          fun f q => f (keyOnlyEmbed L T q) from rfl,
      ← PMF.bind_map, Probability.PMF.uniformOfFintype_pi_map_comp_embedding]
  simp only [advantage, PRF.advantage, hreal, hideal]

/-! ### The arithmetic variant -/

namespace Arithmetic

variable {R : Type} [CommRing R] [Module R L]

/-- A query to the arithmetic circular oracle: a label, a tweak and a scalar shift. -/
structure Query (L R : Type) where
  /-- The label, shifted by minus the offset before hashing. -/
  label : L
  /-- The tweak passed to the hash. -/
  tweak : ℕ
  /-- The multiple of the offset added to the answer. -/
  shift : R
  deriving DecidableEq

/-- The oracle keyed by the offset `Δ`: the query `(k, t, s)` gets `H (k - Δ) t + s • Δ`. -/
@[expose] def oracle (H : L → ℕ → L) (Δ : L) (q : Query L R) : L :=
  H (q.label - Δ) q.tweak + q.shift • Δ

@[simp] theorem oracle_apply (H : L → ℕ → L) (Δ k : L) (t : ℕ) (s : R) :
    oracle H Δ ⟨k, t, s⟩ = H (k - Δ) t + s • Δ :=
  rfl

/-- An arithmetic CCR adversary: a test with private coins and oracle access to queries
`(k, t, s)`. -/
abbrev Adversary (R L : Type) := PRF.Adversary (Query L R) L

/-- The keyed experiment: the law of the PRF real experiment keyed by a uniform offset of colour
`1`, answering with `oracle`. -/
@[expose] noncomputable def realGame (H : L → ℕ → L) (col : L →+ ZMod 2) [Fintype L]
    [Nonempty {Δ : L // col Δ = 1}] (adversary : Adversary R L) : Game :=
  ProbComp.eval (PRF.realExperiment (fun Δ : {Δ : L // col Δ = 1} => oracle H Δ.1) adversary)

/-- The ideal experiment: answer every query with a fresh uniform label. -/
@[expose] noncomputable def idealGame [Fintype L] (adversary : Adversary R L) : Game :=
  ProbComp.eval (adversary.run fun _ => ProbComp.uniform L)

/-- The arithmetic CCR advantage of `adversary` against `H`. The assumption that it is small is
meant only for adversaries that never repeat a tweak (`IsTweakUnique`): repeating a query
distinguishes the fresh oracle from the keyed one. -/
noncomputable abbrev advantage (H : L → ℕ → L) (col : L →+ ZMod 2) [Fintype L]
    [Nonempty {Δ : L // col Δ = 1}] (adversary : Adversary R L) : NNReal :=
  Game.advantage (realGame H col adversary) (idealGame adversary)

/-- The adversary never repeats a tweak: on every path it makes at most one query with each
tweak `t`. -/
@[expose] def IsTweakUnique (adversary : Adversary R L) : Prop :=
  ∀ t : ℕ, OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) fun q : Query L R => if q.tweak = t then 1 else 0) adversary 1

omit [AddCommGroup M] [CommRing R] [Module R L] in
/-- For a tweak-unique adversary, answering every query with a fresh uniform label (`idealGame`)
has the same output law as lazily memoizing a uniform random function on `Query L R`. -/
theorem idealGame_eq_runWith_memoize_of_isTweakUnique [Fintype L] [DecidableEq L] [DecidableEq R]
    {adversary : Adversary R L} (h : IsTweakUnique adversary) :
    idealGame adversary =
      (ProbOracleComp.runWith (memoize fun _ : Query L R => Probability.PMF.uniformOfFintype L)
        adversary []).map Prod.fst := by
  rw [idealGame]
  simpa only [ProbComp.eval_uniform] using
    (ProbOracleComp.runWith_memoize_map_fst_eq_eval_run Query.tweak
      (fun _ => ProbComp.uniform L) h).symm

end Arithmetic

end Cslib.Crypto.Garbling.CCR
