/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.Counting
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.CurveGap
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.UniformBound

/-!
# Smooth FRI Final-Round Counting, Round-by-Round Invariant, and Query/Commit Escape Bounds

Proves the final-round acceptance counting bound (`card_filter_friSmoothFinalPasses_le`),
unconditional smooth round-by-round soundness (`friSmoothIOP_rbrSound`), unconditional query-round
escape (`friSmoothQueryRound_escape_le`), and conditional commit-round escape bounds under
`WeightedCurveEscapePerRound` / `WeightedCurveGapPerRound`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section SmoothEscapeBounds

variable {F : Type} [Field F]

/-- Equivalence between `Fin (params.arity i * params.domainSize (i.val + 1))` and
`Fin (params.domainSize i.val)` for a smooth folding round `i : Fin params.m`. -/
private abbrev FRISmoothParams.fiberDomainEquiv (params : FRISmoothParams F) (i : Fin params.m) :
    Fin (params.arity i * params.domainSize (i.val + 1)) ≃ Fin (params.domainSize i.val) :=
  finCongr (params.domainSize_eq_arity_mul_succ i).symm

omit [Field F] in
private theorem prefQueryIdxs_append_self {m d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q))
    (hlen : pref.length = m) (π : OracleTable d F) (c : FRIChal F d q) :
    prefQueryIdxs (pref ++ [(π, c)]) m = c.queryIdxs := by
  simp only [prefQueryIdxs, ← hlen, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]

omit [Field F] in
private theorem prefQueryIdxs_ofFn {m d q : ℕ}
    (oracles : Fin (m + 1) → OracleTable d F) (chals : Fin (m + 1) → FRIChal F d q) :
    prefQueryIdxs (List.ofFn fun j : Fin (m + 1) => (oracles j, chals j)) m =
      (chals (Fin.last m)).queryIdxs := by
  simp only [prefQueryIdxs, List.getElem?_ofFn, Nat.lt_succ_self, ↓reduceDIte, Fin.last]

private theorem friSmoothTargetWord_append (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friSmoothTargetWord params stmt (pref ++ extra) i hi =
      friSmoothTargetWord params stmt pref i hi := by
  cases i with
  | zero => rfl
  | succ k =>
    simp only [friSmoothTargetWord, prefOracle_append_left pref extra (Nat.lt_of_succ_le hlen),
      prefFoldScalar_append_left pref extra (Nat.lt_of_succ_le hlen)]

private theorem friSmoothPreWeight_append [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friSmoothPreWeight params stmt (pref ++ extra) i hi =
      friSmoothPreWeight params stmt pref i hi := by
  induction i with
  | zero => rfl
  | succ k ih =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    ext j
    simp only [friSmoothPreWeight, friSmoothTargetWord_append params stmt pref extra
      (Nat.le_of_succ_le hi) hk.le, ih (Nat.le_of_succ_le hi) hk.le,
      prefOracle_append_left pref extra hk]

private theorem friSmoothTargetWord_append_step (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friSmoothTargetWord params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      foldWord (params.g ^ (2 ^ params.cumLog pref.length))
        (params.ω ^ (2 ^ params.cumLog pref.length))
        (fun idx : Fin (params.arity ⟨pref.length, hpm⟩ * params.domainSize (pref.length + 1)) =>
          restrictOracle (i := params.cumLog pref.length) π
            (params.fiberDomainEquiv ⟨pref.length, hpm⟩ idx))
        c.foldScalar := by
  simp only [friSmoothTargetWord, prefOracle_append_self, prefFoldScalar_append_self]

private theorem friSmoothPreWeight_append_step [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friSmoothPreWeight params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      friSmoothNextWeight params stmt pref pref.length hpm π := by
  ext j
  simp only [friSmoothPreWeight, friSmoothNextWeight, friSmoothOracleFilterWeight,
    friSmoothTargetWord_append params stmt pref [(π, c)] hpm.le le_rfl,
    friSmoothPreWeight_append params stmt pref [(π, c)] hpm.le le_rfl, prefOracle_append_self]

private theorem friSmoothTranscriptSingleAccepts_append_iff (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F)
    (c : FRIChal F params.d params.q) (s : Fin (2 ^ params.d)) :
    friSmoothTranscriptSingleAccepts params stmt (pref ++ [(πFinal, c)]) s ↔
      friSmoothFinalPasses params stmt pref πFinal s := by
  have hpref (j : ℕ) (hj : j ≤ params.m) :
      prefOracle (pref ++ [(πFinal, c)]) j =
        if j = params.m then πFinal else prefOracle pref j := by
    split_ifs with h <;> [simp only [h, ← hlen, prefOracle_append_self];
      exact prefOracle_append_left pref [(πFinal, c)] (by omega)]
  simp only [friSmoothTranscriptSingleAccepts, friSmoothPrefixPasses, friSmoothFinalPasses,
    hpref params.m le_rfl, ↓reduceIte, hpref 0 (Nat.zero_le _), eq_comm (a := 0),
    apply_ite (fun f : OracleTable params.d F => f s), and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun k => ?_
  have hk_lt : k.val < pref.length := by omega
  simp only [k.isLt, true_implies, prefOracle_append_left pref [(πFinal, c)] hk_lt,
    prefFoldScalar_append_left pref [(πFinal, c)] hk_lt, hpref (k.val + 1) k.isLt]

private theorem friSmoothTranscriptSingleAccepts_ofFn_iff (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) :
    friSmoothTranscriptSingleAccepts params stmt
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) s ↔
      friSmoothSingleAccepts params stmt chals oracles s := by
  simp only [friSmoothTranscriptSingleAccepts, friSmoothPrefixPasses, friSmoothSingleAccepts,
    prefOracle_ofFn oracles chals (Nat.zero_lt_succ params.m),
    prefOracle_ofFn oracles chals (Nat.lt_succ_self params.m), and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun k => ?_
  simp only [k.isLt, true_implies,
    prefOracle_ofFn oracles chals (Nat.lt_succ_of_lt k.isLt),
    prefFoldScalar_ofFn oracles chals (Nat.lt_succ_of_lt k.isLt),
    prefOracle_ofFn oracles chals (Nat.succ_lt_succ k.isLt)]
  rfl

/-- **Smooth final query-acceptance counting bound**: for a length-`m` prefix `pref` and any final
oracle `πFinal`, the number of starting indices `s : Fin (2 ^ d)` satisfying `friSmoothFinalPasses`
is at most the pre-filter weighted agreement of `friSmoothTargetWord ... m` with
`friSmoothFinalCodeword params πFinal`. -/
theorem card_filter_friSmoothFinalPasses_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      friSmoothFinalPasses params stmt pref πFinal s).card ≤
    ∑ j ∈ Finset.univ.filter (fun j =>
      friSmoothTargetWord params stmt pref params.m le_rfl j =
        friSmoothFinalCodeword params πFinal j),
      friSmoothPreWeight params stmt pref params.m le_rfl j := by
  let c₀ : FRIChal F params.d params.q := ⟨0, fun _ => ⟨0, Nat.pow_pos (by omega)⟩⟩
  let pref' := pref ++ [(πFinal, c₀)]
  have hπm : prefOracle pref' params.m = πFinal := by
    simp only [pref', ← hlen, prefOracle_append_self]
  have hfw (j : Fin (params.domainSize params.m)) :
      friSmoothOracleFilterWeight params stmt pref' params.m le_rfl (prefOracle pref' params.m) j =
        friSmoothOracleFilterWeight params stmt pref params.m le_rfl πFinal j := by
    simp only [friSmoothOracleFilterWeight, pref', hπm,
      friSmoothTargetWord_append params stmt pref [(πFinal, c₀)] le_rfl hlen.symm.le,
      friSmoothPreWeight_append params stmt pref [(πFinal, c₀)] le_rfl hlen.symm.le]
  rw [Finset.card_eq_sum_card_fiberwise (f := friSmoothFinalFin params)
    (t := Finset.univ) fun _ _ => Finset.mem_univ _]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans_le
    ((Finset.sum_filter _ _).symm.trans_le
      (sum_agree_friSmoothOracleFilterWeight_le params stmt pref params.m le_rfl πFinal _))
  change (Finset.filter (fun s => friSmoothFinalFin params s = j) _).card =
    if restrictOracle (i := params.cumLog params.m) πFinal j =
        friSmoothFinalCodeword params πFinal j then
      friSmoothOracleFilterWeight params stmt pref params.m le_rfl πFinal j
    else 0
  have hidx {s : Fin (2 ^ params.d)} (hfin : friSmoothFinalFin params s = j) :
      friSmoothFinalIdx params s =
        ⟨j.val, j.isLt.trans_le (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ :=
    Fin.ext (congrArg (Fin.val (n := params.domainSize params.m)) hfin)
  split_ifs with hok
  · rw [← hfw j, ← card_filter_friSmoothPrefixPasses_eq params stmt pref' params.m le_rfl j]
    refine congrArg Finset.card (Finset.ext fun s => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← friSmoothTranscriptSingleAccepts_append_iff params stmt pref hlen πFinal c₀ s,
      friSmoothTranscriptSingleAccepts]
    refine ⟨fun ⟨⟨hp, _⟩, hfin⟩ => ⟨congrArg Fin.val hfin, hp⟩, fun ⟨hmod, hp⟩ => ?_⟩
    have hfin : friSmoothFinalFin params s = j := Fin.ext hmod
    exact ⟨⟨hp, by rwa [hfin, hidx hfin, hπm]⟩, hfin⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro s hs hfin
    have heq := (Finset.mem_filter.mp hs).2.2.2
    exact hok (by rwa [hfin, hidx hfin] at heq)


private theorem friSmoothCommitDoomed_congr_round [DecidableEq F] (params : FRISmoothParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i₁ i₂ : ℕ} (h : i₁ = i₂) (hi₁ : i₁ ≤ params.m) (hi₂ : i₂ ≤ params.m) :
    friSmoothCommitDoomed params B stmt pref i₁ hi₁ ↔
      friSmoothCommitDoomed params B stmt pref i₂ hi₂ :=
  h ▸ Iff.rfl

/-- **Unconditional round-by-round soundness invariant for smooth `friSmoothIOP`**: for every
distance threshold `e : ℕ`, `friSmoothIOP params` satisfies `IOPRoundByRoundSoundness` with respect
to `params.proximityLang e`, `friSmoothDoomed params (2 ^ params.d - e - 1)`, and
`friSmoothGoodStep params (2 ^ params.d - e - 1)`. -/
theorem friSmoothIOP_rbrSound [DecidableEq F] (params : FRISmoothParams F) (e : ℕ) :
    IOPRoundByRoundSoundness (friSmoothIOP params) (params.proximityLang e)
      (friSmoothDoomed params (2 ^ params.d - e - 1))
      (friSmoothGoodStep params (2 ^ params.d - e - 1)) where
  init_doomed stmt hnot := by
    simp only [friSmoothDoomed, List.length_nil, Nat.zero_le, ↓reduceDIte, friSmoothCommitDoomed,
      friSmoothTargetWord, friSmoothPreWeight, restrictOracle, FRISmoothParams.domainSize,
      friCumLog_zero, Nat.sub_zero, Fin.eta, Finset.sum_const, smul_eq_mul, mul_one]
    intro c hc
    have he_lt : e < hammingDist stmt c := Nat.lt_of_not_ge fun h => hnot ⟨c, hc, h⟩
    have hpart := Fintype.card_fin (2 ^ params.d) ▸ card_filter_eq_add_hammingDist stmt c
    change (Finset.univ.filter fun j => stmt j = c j).card ≤ 2 ^ params.d - e - 1
    omega
  step_doomed stmt pref π c _ hgood := by
    by_cases h : pref.length ≤ params.m
    · simpa only [friSmoothGoodStep, h, ↓reduceIte] using hgood
    · simp only [friSmoothDoomed, List.length_append, List.length_singleton]
      split_ifs <;> omega
  reject_of_doomed stmt oracles chals hdoomed := by
    simp only [friSmoothDoomed, List.length_ofFn, Nat.not_succ_le_self, ↓reduceDIte, ↓reduceIte,
      prefQueryIdxs_ofFn] at hdoomed
    obtain ⟨a, ha⟩ := hdoomed
    exact Bool.eq_false_iff.mpr fun hacc => ha <|
      (friSmoothTranscriptSingleAccepts_ofFn_iff params stmt oracles chals _).mpr
        ((iopVerify_friSmoothIOP_eq_true_iff params stmt chals oracles).mp hacc a)

omit [Field F] in
/-- Projecting a uniform `FRIChal F d q` onto its folding scalar `foldScalar` yields the uniform
distribution on `F`. -/
theorem uniformOfFintype_friChal_map_foldScalar [Fintype F] [Nonempty F] (d q : ℕ) :
    (PMF.uniformOfFintype (FRIChal F d q)).map FRIChal.foldScalar =
      PMF.uniformOfFintype F := by
  have : Nonempty (Fin q → Fin (2 ^ d)) := ⟨fun _ => ⟨0, Nat.two_pow_pos d⟩⟩
  rw [show FRIChal.foldScalar = Prod.fst ∘ FRIChal.equivProd F d q from rfl, ← PMF.map_comp,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv (FRIChal.equivProd F d q),
    Cslib.Probability.PMF.uniformOfFintype_prod_map_fst]

omit [Field F] in
/-- Cardinality of `FRIChal` elements whose `q` query starting indices all lie in `S`. -/
private theorem card_filter_queryIdxs_mem [Fintype F] {d q : ℕ}
    (S : Finset (Fin (2 ^ d))) :
    (Finset.univ.filter fun c : FRIChal F d q => ∀ a : Fin q, c.queryIdxs a ∈ S).card =
      Fintype.card F * S.card ^ q := by
  rw [← Fintype.card_subtype, Fintype.card_congr
    { toFun := fun ⟨c, hc⟩ => (c.foldScalar, fun a : Fin q => (⟨c.queryIdxs a, hc a⟩ : S))
      invFun := fun ⟨z, f⟩ => ⟨⟨z, fun a => (f a).val⟩, fun a => (f a).property⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }]
  simp [Fintype.card_prod, Fintype.card_coe]

/-- When `pref.length = m` and `pref` is doomed at threshold `B`, at most `B` starting points in
`Fin (2 ^ d)` pass `friSmoothFinalPasses` against any final oracle `π`. -/
theorem card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {stmt : OracleTable params.d F}
    {pref : List (OracleTable params.d F × FRIChal F params.d params.q)}
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref π s).card ≤ B := by
  simp only [friSmoothDoomed, hlen.le, ↓reduceDIte] at hdoomed
  exact (card_filter_friSmoothFinalPasses_le params stmt pref hlen π).trans
    (((friSmoothCommitDoomed_congr_round params B stmt pref hlen hlen.le le_rfl).mp hdoomed)
      (friSmoothFinalCodeword params π) (friSmoothFinalCodeword_mem_rsCode params π))

/-- **Unconditional smooth query-round escape bound**: when `pref.length = m` and `pref` is doomed
at threshold `B`, the probability over a uniform `FRIChal` that all `q` query repetitions pass is
at most `(B / 2 ^ d) ^ q`. -/
theorem friSmoothQueryRound_escape_le [Fintype F] [DecidableEq F] (params : FRISmoothParams F)
    (B : ℕ) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      ((B : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  classical
  let goodS := Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref π s
  have hbad_eq : {c : FRIChal F params.d params.q | ¬ friSmoothGoodStep params B stmt pref π c} =
      {c | ∀ a : Fin params.q, c.queryIdxs a ∈ goodS} := by
    ext c
    simp only [Set.mem_ofPred_eq, friSmoothGoodStep, le_rfl, ↓reduceIte, friSmoothDoomed,
      List.length_append, List.length_cons, List.length_nil, hlen, Nat.not_succ_le_self,
      ↓reduceDIte, prefQueryIdxs_append_self pref hlen π c, not_exists, not_not,
      friSmoothTranscriptSingleAccepts_append_iff params stmt pref hlen π c,
      goodS, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcard := card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params hlen π hdoomed
  rw [hbad_eq]
  refine (Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div
    (α := FRIChal F params.d params.q) (P := fun c => ∀ a : Fin params.q, c.queryIdxs a ∈ goodS)
    (A := B ^ params.q) (B := (2 ^ params.d) ^ params.q)
    (Nat.pow_pos (Nat.pow_pos (by omega))) ?_).trans_eq ?_
  · rw [card_filter_queryIdxs_mem goodS, card_friChal]
    calc (2 ^ params.d) ^ params.q * (Fintype.card F * goodS.card ^ params.q)
        = goodS.card ^ params.q * (Fintype.card F * (2 ^ params.d) ^ params.q) := by ring
      _ ≤ B ^ params.q * (Fintype.card F * (2 ^ params.d) ^ params.q) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard _)
  · simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]


private theorem sum_agree_foldComp_le_of_commitDoomed [DecidableEq F] (params : FRISmoothParams F)
    {B : ℕ} (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (ir : Fin params.m) (π : OracleTable params.d F)
    (hcommit : friSmoothCommitDoomed params B stmt pref ir.val ir.isLt.le)
    (v : Fin (params.arity ir) → Fin (params.domainSize (ir.val + 1)) → F)
    (hv : ∀ r, v r ∈ params.rsCode (ir.val + 1)) :
    (∑ j ∈ Finset.univ.filter (fun j => ∀ r : Fin (params.arity ir),
        foldComp (params.g ^ (2 ^ params.cumLog ir.val)) (params.ω ^ (2 ^ params.cumLog ir.val))
          (fun idx => restrictOracle (i := params.cumLog ir.val) π
            (params.fiberDomainEquiv ir idx)) r j = v r j),
      friSmoothNextWeight params stmt pref ir.val ir.isLt π j) ≤ B := by
  have hpow (x : F) : (x ^ (2 ^ params.cumLog ir.val)) ^ params.arity ir =
      x ^ (2 ^ params.cumLog (ir.val + 1)) := by
    rw [params.cumLog_succ ir, FRISmoothParams.arity, ← pow_mul, ← pow_add]
  have hωi : IsPrimitiveRoot (params.ω ^ (2 ^ params.cumLog ir.val))
      (params.arity ir * params.domainSize (ir.val + 1)) :=
    params.domainSize_eq_arity_mul_succ ir ▸
      isPrimitiveRoot_pow_two_pow params.hω (params.cumLog_le_d ir.isLt.le)
  have hv' (r : Fin (params.arity ir)) : v r ∈ reedSolomon
      (cosetPoint ((params.g ^ (2 ^ params.cumLog ir.val)) ^ params.arity ir)
        ((params.ω ^ (2 ^ params.cumLog ir.val)) ^ params.arity ir)
        (params.domainSize (ir.val + 1))) (params.dim (ir.val + 1)) := by
    simpa only [FRISmoothParams.rsCode, FRISmoothParams.eval, cosetEval, hpow] using hv r
  let eqv := params.fiberDomainEquiv ir
  obtain ⟨c, hc_rs, -, hc_sum⟩ := exists_mem_reedSolomon_weighted_agree_lift
    (pow_ne_zero _ params.hg) (params.arity_cast_ne_zero ir) (Nat.pow_pos (by omega)) hωi
    (fun idx => restrictOracle (i := params.cumLog ir.val) π (eqv idx)) v hv'
    (fun idx => friSmoothOracleFilterWeight params stmt pref ir.val ir.isLt.le π (eqv idx))
  obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp hc_rs
  have hc'_rs : (c ∘ eqv.symm) ∈ params.rsCode ir.val := mem_reedSolomon.mpr
    ⟨p, (params.dim_eq_arity_mul_succ ir).symm ▸ hp, funext fun y => congrFun hpeq (eqv.symm y)⟩
  have heqv :
      (∑ idx ∈ Finset.univ.filter
          (fun idx => restrictOracle (i := params.cumLog ir.val) π (eqv idx) = c idx),
        friSmoothOracleFilterWeight params stmt pref ir.val ir.isLt.le π (eqv idx)) =
      ∑ y ∈ Finset.univ.filter
          (fun y => restrictOracle (i := params.cumLog ir.val) π y = (c ∘ eqv.symm) y),
        friSmoothOracleFilterWeight params stmt pref ir.val ir.isLt.le π y := by
    simp only [Finset.sum_filter, Function.comp_apply]
    exact (Finset.sum_congr rfl fun idx _ => by simp).trans (Equiv.sum_comp eqv _)
  refine hc_sum.trans_eq heqv |>.trans
    ((sum_agree_friSmoothOracleFilterWeight_le params stmt pref ir.val ir.isLt.le π _).trans
      (hcommit _ hc'_rs))

/-- **Conditional step (smooth commit-round escape bound assuming `WeightedCurveEscapePerRound`)**:
when `pref.length < m` and `pref` is doomed at threshold `B`, the probability over a uniform
`FRIChal` that the `l⁽ⁱ⁾`-to-1 folded target escapes to `> B` weighted agreement with
`params.rsCode (pref.length + 1)` is at most `ε_commit ⟨pref.length, hpm⟩`. Reuses
`Folding.lean`'s `exists_mem_reedSolomon_weighted_agree_lift` and `foldWord_eq_sum_smul`. -/
theorem friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params B ε_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      ε_commit ⟨pref.length, hpm⟩ := by
  let ir : Fin params.m := ⟨pref.length, hpm⟩
  have hcommit : friSmoothCommitDoomed params B stmt pref pref.length hpm.le := by
    simpa only [friSmoothDoomed, hpm.le, ↓reduceDIte] using hdoomed
  let u := foldComp (params.g ^ (2 ^ params.cumLog pref.length))
    (params.ω ^ (2 ^ params.cumLog pref.length))
    (fun idx => restrictOracle (i := params.cumLog pref.length) π (params.fiberDomainEquiv ir idx))
  let W_next := friSmoothNextWeight params stmt pref pref.length hpm π
  have hbad_eq : {c : FRIChal F params.d params.q | ¬ friSmoothGoodStep params B stmt pref π c} =
      FRIChal.foldScalar ⁻¹' {z : F | ∃ v ∈ params.rsCode (pref.length + 1),
        B < ∑ j ∈ Finset.univ.filter
          (fun j => (∑ r : Fin (params.arity ir), z ^ r.val • u r) j = v j), W_next j} := by
    ext c
    have hle' : (pref ++ [(π, c)]).length ≤ params.m := by simp [Nat.succ_le_of_lt hpm]
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, friSmoothGoodStep, hpm.le, ↓reduceIte,
      friSmoothDoomed, hle', ↓reduceDIte]
    rw [friSmoothCommitDoomed_congr_round params B stmt (pref ++ [(π, c)]) (by simp) hle' hpm]
    simp only [friSmoothCommitDoomed, friSmoothTargetWord_append_step params stmt pref hpm π c,
      friSmoothPreWeight_append_step params stmt pref hpm π c, foldWord_eq_sum_smul, not_forall,
      not_le, exists_prop, W_next, u, ir]
  rw [hbad_eq, ← PMF.toOuterMeasure_map_apply,
    uniformOfFintype_friChal_map_foldScalar params.d params.q]
  exact hesc ir W_next (friSmoothNextWeight_le params stmt pref _ hpm π)
    (sum_friSmoothNextWeight_le params stmt pref _ hpm π) u
    (sum_agree_foldComp_le_of_commitDoomed params stmt pref ir π hcommit)

/-- **Conditional step (smooth commit-round escape bound assuming `WeightedCurveGapPerRound`)**:
discharging `WeightedCurveGapPerRound` is left to the caller. -/
theorem friSmoothCommitRound_escape_le_of_weightedCurveGapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      (B_commit ⟨pref.length, hpm⟩ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params
    (weightedCurveEscapePerRound_of_gapPerRound params hgap) stmt pref hpm π hdoomed

/-- **Conditional step (smooth commit-round escape bound assuming `WeightedCurveGapBound`)**:
discharging `WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothCommitRound_escape_le_of_weightedCurveGap [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B B_commit : ℕ}
    (hgap : WeightedCurveGapBound params B B_commit)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤
      (B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friSmoothCommitRound_escape_le_of_weightedCurveGapPerRound params hgap stmt pref hpm π hdoomed


end SmoothEscapeBounds

end Cslib.Crypto.Protocols.FRI
