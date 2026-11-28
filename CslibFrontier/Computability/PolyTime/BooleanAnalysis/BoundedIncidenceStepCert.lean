/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native Step and Measurement-Payload Certificates for Bounded-Incidence Branch Evaluation

This file establishes polynomial-time stage certificates and uniform `ComputableInO` /
`PolyBounded`-workspace bounds for the inner group-cube and two-pass measurement-fiber payload
evaluators of the bounded-incidence $\mathbb{F}_2$ polynomial-system branch algorithm of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (§3.3, Lemma 3.2, p. 23;
§§5.3–5.4, Proposition 5.3, pp. 37–38; Appendix B.2–B.3, pp. 48–50).

Specifically, we define explicit bit-list encodings for the closed stage contexts `GroupEvalCtx`,
`MeasStepCtx`, and `SubsetStepCtx`, certify `validBranchEvalParams`, `validDesignShape`, and
`evalGroupFactorJet` in polynomial time, and compose `BooleanMeasurements.searchCertificate`
(Pass 1) with `CommonCountingAccum.computableInO_streamGroupJetSum` and
`CommonCountingAccum.computableInPolyTime_prodJet` (Pass 2) across the $r_u$ variable groups to
certify the per-measurement-word payload `evalMeasPayload` in
$O\bigl((r_u (2^{d_{\max}} + 1) + 1) \cdot \operatorname{poly}(|\mathrm{input}|)\bigr)$ time and
globally polynomial workspace.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.encGroupEvalCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.encMeasStepCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.encSubsetStepCtx`: bit-list encodings for
  the closed step contexts of `CommonCountingAccum.streamGroupJetSum`, `MeasurementFold.run`, and
  `SubsetPairFold.run`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.maxGroupDim`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.maxAllGroupDim`: unary-clamped maximum
  variable-group dimensions at a single interpolation node and across all $Q_u$ nodes.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.evalMeasPayload`: standalone two-pass
  measurement-word payload returning `some prodJet` when all $r_u$ group fibers are nonempty and
  `none` otherwise.

## Main results

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.computableInPolyTime_validBranchEvalParams`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.computableInPolyTime_validDesignShape`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.computableInPolyTime_evalGroupFactorJet`:
  polynomial-time certificates for the entry guard, design-shape guard, and restricted local-cube
  group factor-jet summand.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.measurementStepBody_eq`: decomposition of
  `measurementStepBody` through `evalMeasPayload` and `Option.elim`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.exists_computableInO_measPayload`: uniform
  `ComputableInO` time and `PolyBounded` workspace bound for `evalMeasPayload`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §3.3 (Lemma 3.2, p. 23),
  §§5.3–5.4 (Proposition 5.3, pp. 37–38), and Appendix B.2–B.3 (pp. 48–50).
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.CommonCountingAccum Cslib.Complexity Cslib.GenericRAM
open Cslib.LinearAlgebra Turing.MultiTapeTM

/-! ### 1. Stage Encodings and Polynomial-Time Step Helpers -/

section StageHelpers

open ComputableInPolyTime

private abbrev encJet : JetRows ↪ List Bool := encList (encList encIntBin)
private abbrev encGroupEqEntry : (List (List ℕ) × List (List (List ℤ))) ↪ List Bool :=
  encPair (encList (encList encNat)) (encList (encList (encList encIntBin)))

/-- Bit-list encoding for `GroupEvalCtx`, encoding `(n', J, ℓ, k')` in unary, `(node, dDen)` and
measurement vectors in signed binary, bit masks via `encBits`, and precollected group equations with
replacement-row tables as nested lists. -/
def encGroupEvalCtx : GroupEvalCtx ↪ List Bool :=
  encPair
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
    (encPair
      (encPair encIntBin encIntBin)
      (encPair
        (encPair (encList encNat) (encPair (encList (encList encIntBin)) (encList encIntBin)))
        (encPair
          (encPair encBits (encPair encBits encBits))
          (encList (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))))))

/-- Bit-list encoding for `MeasStepCtx`, encoding `(n', r_u, m_rows)` and `(J, ℓ, k')` in unary
together with node parameters, per-group variable/measurement slices, subset bit masks, and
precollected group equations. -/
def encMeasStepCtx : MeasStepCtx ↪ List Bool :=
  encPair
    (encPair encUnary (encPair encUnary encUnary))
    (encPair
      (encPair encUnary (encPair encUnary encUnary))
      (encPair
        (encPair encIntBin encIntBin)
        (encPair
          (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))
          (encPair
            (encPair encBits encBits)
            (encList (encList
              (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))))))))

/-- Bit-list encoding for `SubsetStepCtx`, encoding `(n', r_u, m_rows)` and `(J, ℓ, k')` in unary,
`(c_meas, D_cap)` as `(encUnary, encNat)`, and the fixed per-node group and equation tables. -/
def encSubsetStepCtx : SubsetStepCtx ↪ List Bool :=
  encPair
    (encPair encUnary (encPair encUnary encUnary))
    (encPair
      (encPair encUnary encNat)
      (encPair
        (encPair encUnary (encPair encUnary encUnary))
        (encPair
          (encPair encIntBin encIntBin)
          (encPair
            (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))
            (encList (encList
              (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))))))))

private theorem bi_bool_not_or {α : Type} {encIn : α ↪ List Bool} {a b : α → Bool}
    (ha : ComputableInPolyTime a encIn encBool)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => !(a x) || b x) encIn encBool :=
  (of_finite (fun p : Bool × Bool => !p.1 || p.2)).comp (ha.prod hb)

private theorem bi_allWith {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {xs : α → List β} {test : α × β → Bool}
    (hxs : ComputableInPolyTime xs encA (encList encB))
    (htest : ComputableInPolyTime test (encPair encA encB) encBool) :
    ComputableInPolyTime (fun x => (xs x).all fun b => test (x, b)) encA encBool :=
  allWithEncoding htest id' hxs

private theorem bi_filterWithId {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {test : γ × α → Bool} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encIn encA) encBool)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).filter fun a => test (x, a))
      encIn (encList encA) :=
  filterWithInput (test := fun x a => test (x, a)) hlist htest

private theorem bi_mapWithId {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {f : γ × α → β} {list : γ → List α}
    (hf : ComputableInPolyTime f (encPair encIn encA) encB)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).map fun a => f (x, a)) encIn (encList encB) :=
  mapWithInput (f := fun x a => f (x, a)) hlist hf

private theorem bi_listGetD_nat_dyn {α : Type} {encIn : α ↪ List Bool}
    {xs : α → List ℕ} {idx fallback : α → ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hidx : ComputableInPolyTime idx encIn encUnary)
    (hfb : ComputableInPolyTime fallback encIn encNat) :
    ComputableInPolyTime (fun x => (xs x).getD (idx x) (fallback x)) encIn encNat := by
  have hlt := binary_lt' (unary_to_binary.comp hidx)
    (unary_to_binary.comp ((length_list encNat).comp hxs))
  have h0 := (listGetD (encA := encNat) 0).comp (hxs.prod hidx)
  refine (hlt.ite' h0 hfb).of_enc_eq fun x => ?_
  congr 1; dsimp only [Function.comp_apply]
  by_cases h : idx x < (xs x).length
  · simp only [h, decide_true, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
      List.getD_eq_default _ _ (Nat.le_of_not_lt h)]

/-- `validBranchEvalParams` is computable in polynomial time on `encBranchEvalInput`. -/
theorem computableInPolyTime_validBranchEvalParams :
    ComputableInPolyTime validBranchEvalParams encBranchEvalInput encBool := by
  unfold validBranchEvalParams
  have hn' := BranchEvalInput.computableInPolyTime_numVars
  have hk' := BranchEvalInput.computableInPolyTime_maxDegree
  have heqs := BranchEvalInput.computableInPolyTime_equations
  have hr := BranchEvalInput.computableInPolyTime_numGroups
  have hQ := BranchEvalInput.computableInPolyTime_numNodes
  have hR := BranchEvalInput.computableInPolyTime_rowBound
  have hA₀ := BranchEvalInput.computableInPolyTime_intervalStart
  have hn_b := unary_to_binary.comp hn'; have hk_b := unary_to_binary.comp hk'
  have hQu := binary_min_unary' hn' hQ
  have hru := binary_min_unary' hn' hr
  have h2Qu := unary_add.comp (hQu.prod hQu)
  have hpow : ComputableInPolyTime
      (fun inp : BranchEvalInput => (min inp.numVars inp.numGroups) ^
        (2 * min inp.numVars inp.numNodes)) encBranchEvalInput encNat := by fun_prop
  have hc1 := binary_le' (const 1) hn_b; have hc2 := binary_le' (const 2) hr
  have hc3 := binary_le' (const 1) hR; have hc4 := binary_lt' hR hQ
  have hc5 := binary_le' hQ hn_b; have hc6 := binary_le' hr hn_b
  have hc7 := binary_le' (binary_add' hA₀ hR) (binary_add' hQ (const 1))
  have hc8 := binary_le' hpow hn_b
  have hc9 := computableInPolyTime_checkVarsLt.comp (hn'.prod heqs)
  have hc10 := computableInPolyTime_checkCanonicalSystem.comp heqs
  have hc11 := binary_le'
    (unary_to_binary.comp (computableInPolyTime_sysMaxDegree.comp heqs)) hk_b
  exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
    (bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
      hc1 hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9) hc10) hc11

/-- `validDesignShape` is computable in polynomial time when `(n', r_u, m_eq)` are given in unary
and `data` is encoded via `encReplacementDesignData`. -/
theorem computableInPolyTime_validDesignShape {α : Type} {encIn : α ↪ List Bool}
    {n' r_u m_eq : α → ℕ} {data : α → ReplacementDesignData}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hru : ComputableInPolyTime r_u encIn encUnary)
    (hmeq : ComputableInPolyTime m_eq encIn encUnary)
    (hdata : ComputableInPolyTime data encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => validDesignShape (n' x) (r_u x) (m_eq x) (data x))
      encIn encBool := by
  unfold validDesignShape
  have hmrows : ComputableInPolyTime (fun x => (data x).measurementMatrix.length) encIn encUnary :=
    (length_list (encList encIntBin)).comp (computableInPolyTime_measurementMatrix hdata)
  have hlhs := unary_mul.comp (hru.prod hmrows)
  have hrhs := unary_mul.comp ((unary_mul.comp ((const 4).prod
      (unary_add.comp (hn'.prod (const 1))))).prod
    (unary_add.comp ((unary_add.comp ((unary_mul.comp (hmeq.prod hn')).prod hn')).prod
      (const 1))))
  have h1 := unary_le' hlhs hrhs
  have hvgs := computableInPolyTime_varGroups hdata
  let e1 := encPair encIn (encList (encList encNat))
  let e2 := encPair e1 (encList encNat)
  have hn_q := hn'.comp ((fst encIn (encList (encList encNat))).comp (fst e1 (encList encNat)))
  have h2n_b := unary_to_binary.comp (unary_add.comp (hn_q.prod hn_q))
  have hlen_b := unary_to_binary.comp ((length_list encNat).comp (snd e1 (encList encNat)))
  have hcmp : ComputableInPolyTime
      (fun q : (α × List (List ℕ)) × List ℕ => decide (q.2.length ≤ 2 * n' q.1.1)) e2 encBool := by
    fun_prop
  have hall := bi_allWith hvgs (bi_allWith (snd encIn (encList (encList encNat))) hcmp)
  exact bool_and' h1 hall

private theorem length_applyGroupBits (n' : ℕ) (Vg : List ℕ) (ug base : List Bool) :
    (applyGroupBits n' Vg ug base).length = n' := by
  simp only [applyGroupBits, List.length_map, List.length_range]

private theorem computableInPolyTime_applyGroupBits {α : Type} {encIn : α ↪ List Bool}
    {n' : α → ℕ} {Vg : α → List ℕ} {ug base : α → List Bool}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hVg : ComputableInPolyTime Vg encIn (encList encNat))
    (hug : ComputableInPolyTime ug encIn encBits)
    (hbase : ComputableInPolyTime base encIn encBits) :
    ComputableInPolyTime (fun x => applyGroupBits (n' x) (Vg x) (ug x) (base x))
      encIn encBits := by
  let e1 := encPair encIn encUnary
  let hx1 := fst encIn encUnary; let hv_un := snd encIn encUnary
  let ePar := encPair encNat (encPair encNat (encPair (encList encNat) encBits))
  have hpar : ComputableInPolyTime
      (fun p : α × ℕ => (n' p.1, (p.2, (Vg p.1, ug p.1)))) e1 ePar :=
    (unary_to_binary.comp (hn'.comp hx1)).prod
      ((unary_to_binary.comp hv_un).prod ((hVg.comp hx1).prod (hug.comp hx1)))
  have hlist := range.comp ((length_list encNat).comp (hVg.comp hx1))
  have hinit := bitsGetDWithInput (hbase.comp hx1) hv_un false
  let stepFn (par : ℕ × ℕ × List ℕ × List Bool) (cur : Bool) (j : ℕ) : Bool :=
    if par.2.2.1.getD j par.1 == par.2.1 then par.2.2.2.getD j false else cur
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × List ℕ × List Bool) × Bool) × ℕ => stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair ePar encBool) encUnary) encBool := by
    let ePB := encPair ePar encBool
    have hp := (fst ePar encBool).comp (fst ePB encUnary)
    have hcur := (snd ePar encBool).comp (fst ePB encUnary); have hj := snd ePB encUnary
    have hn_s := hp.fst'; have hv_s := hp.snd'.fst'
    have hVg_s := hp.snd'.snd'.fst'; have hug_s := hp.snd'.snd'.snd'
    have hgetV := bi_listGetD_nat_dyn hVg_s hj hn_s
    have hgetU := bitsGetDWithInput hug_s hj false
    exact (beq hgetV hv_s).ite' hgetU hcur
  have hfold := foldlWith hpar hlist hinit hstep (.const 1)
    (fun _ _ _ => by simp only [encBool_apply, List.length_singleton, le_rfl])
  exact (bits_encList_polyTime encBool).2.comp (mapWithInput (range.comp hn') hfold)

private theorem computableInPolyTime_buildBaseAssignment {α : Type} {encIn : α ↪ List Bool}
    {n' r_u : α → ℕ} {vGroups_t : α → List (List ℕ)} {reps : α → List (List Bool)}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hru : ComputableInPolyTime r_u encIn encUnary)
    (hvgs : ComputableInPolyTime vGroups_t encIn (encList (encList encNat)))
    (hreps : ComputableInPolyTime reps encIn (encList encBits)) :
    ComputableInPolyTime (fun x => buildBaseAssignment (n' x) (r_u x) (vGroups_t x) (reps x))
      encIn encBits := by
  let ePar := encPair encUnary (encPair (encList (encList encNat)) (encList encBits))
  have hpar : ComputableInPolyTime (fun x => (n' x, (vGroups_t x, reps x))) encIn ePar :=
    hn'.prod (hvgs.prod hreps)
  have hlist := range.comp hru
  have hinit := (bits_encList_polyTime encBool).2.comp (replicate hn' (const false))
  let stepFn (par : ℕ × List (List ℕ) × List (List Bool)) (acc : List Bool) (g : ℕ) : List Bool :=
    applyGroupBits par.1 (par.2.1.getD g []) (par.2.2.getD g []) acc
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × List (List ℕ) × List (List Bool)) × List Bool) × ℕ =>
        stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair ePar encBits) encUnary) encBits := by
    let ePB := encPair ePar encBits
    have hp := (fst ePar encBits).comp (fst ePB encUnary)
    have hacc := (snd ePar encBits).comp (fst ePB encUnary)
    have hg := snd ePB encUnary
    have hVg := (listGetD (encA := encList encNat) []).comp (hp.snd'.fst'.prod hg)
    have hug := (listGetD (encA := encBits) []).comp (hp.snd'.snd'.prod hg)
    exact computableInPolyTime_applyGroupBits hp.fst' hVg hug hacc
  have hlen_fold (n : ℕ) (vgs : List (List ℕ)) (rps : List (List Bool)) :
      ∀ (xs : List ℕ) (acc : List Bool), acc.length = n →
        (xs.foldl (stepFn (n, vgs, rps)) acc).length = n := by
    intro xs; induction xs with
    | nil => exact fun _ h => h
    | cons _ _ ih => intro _ _; exact ih _ (length_applyGroupBits _ _ _ _)
  exact foldlWith hpar hlist hinit hstep hn'.polyBounded fun x _ _ => by
    simp only [encBits_apply]
    exact (hlen_fold (n' x) (vGroups_t x) (reps x) _ _ List.length_replicate).le

private theorem computableInPolyTime_checkRestrictedGroup {α : Type} {encIn : α ↪ List Bool}
    {n' : α → ℕ} {indE : α → List Bool} {Vg : α → List ℕ} {ug : α → List Bool}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hindE : ComputableInPolyTime indE encIn encBits)
    (hVg : ComputableInPolyTime Vg encIn (encList encNat))
    (hug : ComputableInPolyTime ug encIn encBits) :
    ComputableInPolyTime (fun x => checkRestrictedGroup (n' x) (indE x) (Vg x) (ug x))
      encIn encBool := by
  unfold checkRestrictedGroup
  have hrange := range.comp ((length_list encNat).comp hVg)
  have hx := fst encIn encUnary
  have hj := snd encIn encUnary
  have hgetV := bi_listGetD_nat_dyn (hVg.comp hx) hj (unary_to_binary.comp (hn'.comp hx))
  have hindE_x := hindE.comp hx
  have hlenE : ComputableInPolyTime (fun p : α × ℕ => (indE p.1).length)
      (encPair encIn encUnary) encUnary := by fun_prop
  have hv_cap := binary_min_unary' hlenE hgetV
  have hgetE : ComputableInPolyTime
      (fun p : α × ℕ => (indE p.1).getD ((Vg p.1).getD p.2 (n' p.1)) false)
      (encPair encIn encUnary) encBool := by
    refine (bitsGetDWithInput hindE_x hv_cap false).of_enc_eq fun p => ?_
    congr 1; dsimp only [Function.comp_apply]
    by_cases h : (Vg p.1).getD p.2 (n' p.1) < (indE p.1).length
    · rw [Nat.min_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_left (Nat.le_of_not_lt h), List.getD_eq_default _ _ le_rfl,
        List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
  have hgetU := bitsGetDWithInput (hug.comp hx) hj false
  exact bi_allWith hrange (bi_bool_not_or hgetE hgetU)

private theorem computableInPolyTime_buildEqRowTables {α : Type} {encIn : α ↪ List Bool}
    {n' : α → ℕ} {eqs' : α → List (List (List ℕ))} {data : α → ReplacementDesignData}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (heqs : ComputableInPolyTime eqs' encIn encSparseSystem)
    (hdata : ComputableInPolyTime data encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => buildEqRowTables (n' x) (eqs' x) (data x))
      encIn (encList (encList (encList (encList encIntBin)))) := by
  unfold buildEqRowTables
  have hrf := range.comp ((length_list (encList (encList encNat))).comp heqs)
  let e1 := encPair encIn encUnary
  have hrn := range.comp (hn'.comp (fst encIn encUnary))
  have hq1 := fst e1 encUnary
  have hd2 := hdata.comp ((fst encIn encUnary).comp hq1)
  have hf2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => q.1.2) (encPair e1 encUnary) encNat :=
    unary_to_binary.comp ((snd encIn encUnary).comp hq1)
  have hv2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => q.2) (encPair e1 encUnary) encNat :=
    unary_to_binary.comp (snd e1 encUnary)
  exact mapWithInput hrf (mapWithInput hrn (computableInPolyTime_lookupReplacementRow hd2 hf2 hv2))

private theorem computableInPolyTime_groupEquationsAt {α : Type} {encIn : α ↪ List Bool}
    {eqs' : α → List (List (List ℕ))} {factorGroups : α → List (List ℕ)}
    {eqRowTables : α → List (List (List (List ℤ)))} {t g : α → ℕ}
    (heqs : ComputableInPolyTime eqs' encIn encSparseSystem)
    (hfg : ComputableInPolyTime factorGroups encIn (encList (encList encNat)))
    (htab : ComputableInPolyTime eqRowTables encIn
      (encList (encList (encList (encList encIntBin)))))
    (ht : ComputableInPolyTime t encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) :
    ComputableInPolyTime
      (fun x => groupEquationsAt (eqs' x) (factorGroups x) (eqRowTables x) (t x) (g x))
      encIn (encList encGroupEqEntry) := by
  unfold groupEquationsAt
  have hrf := range.comp ((length_list (encList (encList encNat))).comp heqs)
  have hx := fst encIn encUnary
  have hf_u := snd encIn encUnary
  have hrow := (listGetD (encA := encList encNat) []).comp ((hfg.comp hx).prod hf_u)
  have hval := (listGetD (encA := encNat) 0).comp (hrow.prod (ht.comp hx))
  have hfilt := bi_filterWithId (decide_eq' hval (unary_to_binary.comp (hg.comp hx))) hrf
  have hpair := ((listGetD (encA := encList (encList encNat)) []).comp
      ((heqs.comp hx).prod hf_u)).prod
    ((listGetD (encA := encList (encList (encList encIntBin))) []).comp
      ((htab.comp hx).prod hf_u))
  exact bi_mapWithId hpair hfilt

/-- `evalGroupFactorJet` is computable in polynomial time on
`encPair encGroupEvalCtx (encPair encUnary encBits)`, matching the body-certificate obligation of
`CommonCountingAccum.computableInO_streamGroupJetSum`. -/
theorem computableInPolyTime_evalGroupFactorJet :
    ComputableInPolyTime evalGroupFactorJet
      (encPair encGroupEvalCtx (encPair encUnary encBits)) (encList (encList encIntBin)) := by
  unfold evalGroupFactorJet encGroupEvalCtx
  let eC1 := encPair encUnary (encPair encUnary (encPair encUnary encUnary))
  let eC2 := encPair (encPair encIntBin encIntBin)
    (encPair (encPair (encList encNat) (encPair (encList (encList encIntBin)) (encList encIntBin)))
      (encPair (encPair encBits (encPair encBits encBits)) (encList encGroupEqEntry)))
  let eCtx := encPair eC1 eC2; let eIn := encPair eCtx (encPair encUnary encBits)
  have hctx := fst eCtx (encPair encUnary encBits)
  have hug := (snd eCtx (encPair encUnary encBits)).snd'
  have hc1 := hctx.fst'; have hc2 := hctx.snd'
  have hn' : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.1)
      eIn encUnary := hc1.fst'
  have hJ : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.2.1)
      eIn encUnary := hc1.snd'.fst'
  have hℓ : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.2.2.1)
      eIn encUnary := hc1.snd'.snd'.fst'
  have hVg : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.1.1)
      eIn (encList encNat) := hc2.snd'.fst'.fst'
  have hchk1 := computableInPolyTime_checkRestrictedGroup hn' hc2.snd'.snd'.fst'.fst' hVg hug
  have hchk2 := (BooleanMeasurements.test_polyTime
    (fst (encList (encList encIntBin)) (encList encIntBin))
    (snd (encList (encList encIntBin)) (encList encIntBin))).comp
    ((hc2.snd'.fst'.snd'.fst'.prod hc2.snd'.fst'.snd'.snd').prod hug)
  have hx := computableInPolyTime_applyGroupBits hn' hVg hug hc2.snd'.snd'.fst'.snd'.snd'
  have hp0 := fst eIn encGroupEqEntry
  have heq := snd eIn encGroupEqEntry
  have hvarJ := computableInPolyTime_evalAffineInputZJetTable (hJ.comp hp0)
    (hc2.fst'.fst'.comp hp0) heq.snd'
    ((bits_encList_polyTime encBool).1.comp (hc2.snd'.snd'.fst'.snd'.fst'.comp hp0))
    ((bits_encList_polyTime encBool).1.comp (hx.comp hp0))
  have hfac := computableInPolyTime_evalEquationParityFactorJet (hJ.comp hp0)
    (hℓ.comp hp0) (hc1.snd'.snd'.snd'.comp hp0) (hc2.fst'.snd'.comp hp0) hvarJ heq.fst'
  exact (bool_and' hchk1 hchk2).ite'
    (CommonCountingAccum.computableInPolyTime_prodJet hJ hℓ (bi_mapWithId hfac hc2.snd'.snd'.snd'))
    (computableInPolyTime_zeroJet hJ hℓ)

end StageHelpers

/-! ### 2. Bounded-Range Loop Combinators and Measurement-Payload Certificate -/

section LoopCertificates

open ComputableInPolyTime

/-- Maximum unary-clamped variable-group dimension `min (2 * n') |V_{t,g}|` across `g < r_u` at a
fixed interpolation node `t`. -/
def maxGroupDim (n' r_u : ℕ) (vGroups_t : List (List ℕ)) : ℕ :=
  ((List.range r_u).map fun g => min (2 * n') (vGroups_t.getD g []).length).foldl max 0

/-- Maximum unary-clamped variable-group dimension across all nodes `t < Q_u` and groups
`g < r_u`. -/
def maxAllGroupDim (n' Q_u r_u : ℕ) (varGroups : List (List (List ℕ))) : ℕ :=
  ((List.range Q_u).map fun t => maxGroupDim n' r_u (varGroups.getD t [])).foldl max 0

private theorem min_length_le_maxGroupDim {n' r_u g : ℕ} {vGroups_t : List (List ℕ)}
    (hg : g < r_u) :
    min (2 * n') (vGroups_t.getD g []).length ≤ maxGroupDim n' r_u vGroups_t :=
  List.le_max_of_mem
    (l := 0 :: (List.range r_u).map (fun g => min (2 * n') (vGroups_t.getD g []).length))
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩))

private theorem maxGroupDim_le_maxAllGroupDim {n' Q_u r_u t : ℕ}
    {varGroups : List (List (List ℕ))} (ht : t < Q_u) :
    maxGroupDim n' r_u (varGroups.getD t []) ≤ maxAllGroupDim n' Q_u r_u varGroups :=
  List.le_max_of_mem
    (l := 0 :: (List.range Q_u).map (fun t => maxGroupDim n' r_u (varGroups.getD t [])))
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))

private theorem foldl_optAddJet_spec (J ℓ j M : ℕ) (f : ℕ → Option JetRows)
    (hf : ∀ i < j, ∀ y, f i = some y → ∀ j' < J, ∀ u' < ℓ, (rowEntry y j' u').natAbs ≤ M) :
    let res := (List.range j).foldl
      (fun acc i => (f i).elim acc (fun y => addJet J ℓ acc y)) (zeroJet J ℓ)
    IsTableShape J ℓ res ∧ ∀ j' < J, ∀ u' < ℓ, (rowEntry res j' u').natAbs ≤ j * M := by
  induction j with
  | zero =>
    exact ⟨isTableShape_zeroJet J ℓ, fun _ _ _ _ => by
      simp only [List.range_zero, List.foldl_nil, rowEntry_zeroJet, Int.natAbs_zero, Nat.zero_mul,
        le_rfl]⟩
  | succ k ih =>
    obtain ⟨hsh, hbd⟩ := ih fun i hi => hf i (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    cases hfk : f k with
    | none =>
      exact ⟨hsh, fun j' hj' u' hu' =>
        (hbd j' hj' u' hu').trans (Nat.mul_le_mul_right M (Nat.le_succ k))⟩
    | some y =>
      refine ⟨isTableShape_addJet J ℓ _ y, fun j' hj' u' hu' => ?_⟩
      rw [Option.elim_some, rowEntry_addJet _ _ hj' hu']
      exact (Int.natAbs_add_le _ _).trans
        ((Nat.add_le_add (hbd j' hj' u' hu') (hf k (by omega) y hfk j' hj' u' hu')).trans_eq
          (by ring))

private theorem length_encJetRows_foldl_optAddJet_le {J ℓ j N M : ℕ} {f : ℕ → Option JetRows}
    (hj : j ≤ N)
    (hf : ∀ i < j, ∀ y, f i = some y → ∀ j' < J, ∀ u' < ℓ, (rowEntry y j' u').natAbs ≤ M) :
    (encJet ((List.range j).foldl
      (fun acc i => (f i).elim acc (fun y => addJet J ℓ acc y)) (zeroJet J ℓ))).length ≤
      J * (2 * (ℓ * (2 * (N.size + M.size) + 3)) + 1) := by
  obtain ⟨hsh, hbd⟩ := foldl_optAddJet_spec J ℓ j M f hf
  exact CommonCountingAccum.length_encJetRows_le_of_size_le hsh fun j' hj' u' hu' =>
    (Nat.size_le_size ((hbd j' hj' u' hu').trans (Nat.mul_le_mul_right M hj))).trans
      (Nat.size_mul_le N M)

private theorem exists_computableInO_mapRange {ι γ δ : Type} {encIn : ι ↪ List Bool}
    {encC : γ ↪ List Bool} {encB : δ ↪ List Bool} {m : ι → ℕ} {ctx : ι → γ} {f : γ × ℕ → δ}
    (hm : ComputableInPolyTime m encIn encUnary) (hctx : ComputableInPolyTime ctx encIn encC)
    {Tf Sf : γ × ℕ → ℕ} (hSf : PolyBounded (fun p => (encPair encC encUnary p).length) Sf)
    (hcf : ComputableInO f (encPair encC encUnary) encB Tf Sf)
    (R : ι → ℕ) (hR : ∀ x, ∀ i < m x, Tf (ctx x, i) ≤ R x) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => (List.range (m x)).map fun i => f (ctx x, i))
        encIn (encList encB) (fun x => (m x + 1) * (R x + P x)) P := by
  have hrange : ComputableInPolyTime (fun x => List.range (m x)) encIn (encList encUnary) :=
    ComputableInPolyTime.range.comp hm
  let cPar := NativeCertificate.ofPolyTime hctx
  let cLst := NativeCertificate.ofPolyTime hrange
  have hcPar := NativeCertificate.ofPolyTime_isPolynomial hctx
  have hcLst := NativeCertificate.ofPolyTime_isPolynomial hrange
  obtain ⟨cs, ds, hSf_le⟩ := hSf.exists_le
  obtain ⟨ce, hce⟩ := hcf.length_le
  let L_el : ι → ℕ := fun x => 2 * (encC (ctx x)).length + 2 * m x + 1
  let E_sf : ι → ℕ := fun x => cs * (L_el x + 1) ^ ds
  let B_out : ι → ℕ := fun x => m x * (2 * (ce * (E_sf x + 1)) + 1)
  have hSf_mem : ∀ x i, i ∈ List.range (m x) → Sf (ctx x, i) ≤ E_sf x := fun x i hi => by
    have hi_lt := List.mem_range.mp hi
    have hlen : (encPair encC encUnary (ctx x, i)).length ≤ L_el x := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, L_el]; omega
    exact (hSf_le (ctx x, i)).trans
      (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) ds))
  let P : ι → ℕ := fun x =>
    (encIn x).length + cPar.time x + cLst.time x + cPar.space x + cLst.space x +
      (encC (ctx x)).length + (encList encUnary (List.range (m x))).length + B_out x + E_sf x
  have hP_pb : PolyBounded (fun x => (encIn x).length) P := by growth_poly
  have hlst (x : ι) :
      (encList encB ((List.range (m x)).map fun i => f (ctx x, i))).length ≤ B_out x := by
    have h := length_encList_le encB ((List.range (m x)).map fun i => f (ctx x, i))
      (b := ce * (E_sf x + 1)) fun y hy => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
        exact (hce (ctx x, i)).trans
          (Nat.mul_le_mul_left ce (Nat.add_le_add_right (hSf_mem x i hi) 1))
    simp only [List.length_map, List.length_range] at h
    exact h
  refine ⟨P, hP_pb, (hcf.mapWith cPar.computes cLst.computes).mono_le (fun x => ?_) fun x => ?_⟩
  · have hmaxT : listMax (fun i => Tf (ctx x, i)) (List.range (m x)) ≤ R x :=
      listMax_le fun i hi => hR x i (List.mem_range.mp hi)
    have hm_len : (List.range (m x)).length = m x := List.length_range
    have hpre := Nat.le_mul_of_pos_left
      ((encIn x).length + cPar.time x + cLst.time x) (Nat.succ_pos (m x))
    have hlst_x := hlst x
    rw [hm_len]
    calc (encIn x).length + cPar.time x + cLst.time x + (m x + 1) *
          ((encC (ctx x)).length + (encList encUnary (List.range (m x))).length +
            (encList encB ((List.range (m x)).map fun a => f (ctx x, a))).length +
            listMax (fun a => Tf (ctx x, a)) (List.range (m x)))
        ≤ (m x + 1) * ((encIn x).length + cPar.time x + cLst.time x) +
            (m x + 1) * ((encC (ctx x)).length + (encList encUnary (List.range (m x))).length +
              B_out x + R x) := by
          gcongr
      _ = (m x + 1) * (R x + ((encIn x).length + cPar.time x + cLst.time x +
            (encC (ctx x)).length + (encList encUnary (List.range (m x))).length + B_out x)) := by
          ring
      _ ≤ (m x + 1) * (R x + P x) := by gcongr; dsimp only [P]; omega
  · have hmaxS : listMax (fun i => Sf (ctx x, i)) (List.range (m x)) ≤ E_sf x :=
      listMax_le (hSf_mem x)
    have hlst_x := hlst x
    dsimp only [P]; omega

private theorem absorb_step_add (K P₀ P₁ : ℕ) (hK : 1 ≤ K) :
    K * P₀ + P₁ ≤ K * (P₀ + P₁) := by
  calc K * P₀ + P₁ ≤ K * P₀ + K * P₁ := Nat.add_le_add_left (Nat.le_mul_of_pos_left P₁ hK) _
    _ = K * (P₀ + P₁) := (Nat.mul_add K P₀ P₁).symm

private theorem mapRange_group_bound (r_u G P₀ P₁ : ℕ) :
    (r_u + 1) * ((if r_u = 0 then 0 else (G + 1) * P₀) + P₁) ≤
      (r_u * (G + 1) + 1) * (2 * (P₀ + P₁)) := by
  by_cases hr0 : r_u = 0
  · subst hr0; simp only [↓reduceIte, zero_add, one_mul, Nat.zero_mul]; omega
  · simp only [hr0, ↓reduceIte]
    calc (r_u + 1) * ((G + 1) * P₀ + P₁)
        ≤ (2 * r_u) * ((G + 1) * (P₀ + P₁)) :=
          Nat.mul_le_mul (by omega) (absorb_step_add (G + 1) P₀ P₁ (Nat.succ_pos G))
      _ = (r_u * (G + 1)) * (2 * (P₀ + P₁)) := by ring
      _ ≤ (r_u * (G + 1) + 1) * (2 * (P₀ + P₁)) := Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- **Mapping a per-group computation over the groups.** If the computation at group `g < m x`
runs in `FactorTimePolySpace` with factor bounded by `2 ^ D x + 1`, the map over all `m x` groups
runs in `FactorTimePolySpace` with factor `m x * (2 ^ D x + 1) + 1`. -/
private theorem exists_factorTimePolySpace_groupMap {ι δ : Type} {encIn : ι ↪ List Bool}
    {encB : δ ↪ List Bool} {m D : ι → ℕ} {f : ι × ℕ → δ} {K : ι × ℕ → ℕ}
    {cf : NativeCertificate f (encPair encIn encUnary) encB}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hcf : cf.FactorTimePolySpace K)
    (hK : ∀ x, ∀ g < m x, K (x, g) ≤ 2 ^ D x + 1) :
    ∃ c : NativeCertificate (fun x => (List.range (m x)).map fun g => f (x, g))
        encIn (encList encB),
      c.FactorTimePolySpace (fun x => m x * (2 ^ D x + 1) + 1) := by
  obtain ⟨ov, hov, ht⟩ := hcf.exists_time_polyBounded
  obtain ⟨c, d, hc⟩ := hov.exists_le
  let P (x : ι) : ℕ := c * (2 * (encIn x).length + 2 * m x + 1 + 1) ^ d
  obtain ⟨S, hS, hcomp⟩ := exists_computableInO_mapRange hm id' hcf.space_polyBounded cf.computes
    (fun x => if m x = 0 then 0 else (2 ^ D x + 1) * P x) fun x g hg => by
      simp only [show m x ≠ 0 by omega, ↓reduceIte]
      have hlen : (encPair encIn encUnary (x, g)).length ≤
          2 * (encIn x).length + 2 * m x + 1 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
      exact (ht (x, g)).trans (Nat.mul_le_mul (hK x g hg) ((hc (x, g)).trans
        (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) d))))
  exact ⟨⟨_, S, hcomp⟩, .of_polyBounded
    (by growth_poly : PolyBounded (fun x => (encIn x).length) fun x => 2 * (P x + S x)) hS
    fun x => mapRange_group_bound _ _ _ _⟩

/-- Standalone per-measurement-word two-pass payload: slices `word` across the `r_u` variable
groups, searches each unrestricted group fiber via `BooleanMeasurements.search` (Pass 1), and when
every fiber is nonempty streams restricted local-cube factor-jet sums via
`CommonCountingAccum.streamGroupJetSum` and returns `some (prodJet J ℓ groupJets)` (Pass 2). -/
def evalMeasPayload (wc : List ℤ × MeasStepCtx) : Option JetRows :=
  let (word, ((n', r_u, m_rows), (J, ℓ, k'), (node, dDen), (vGroups_t, grpMeas_t),
    (indE, indU), grpEqLists)) := wc
  let repOpts := (List.range r_u).map fun g =>
    BooleanMeasurements.search Prod.fst Prod.snd
      ((grpMeas_t.getD g [], (word.drop (g * m_rows)).take m_rows),
        min (2 * n') (vGroups_t.getD g []).length)
  if repOpts.all Option.isSome then
    let xStar := buildBaseAssignment n' r_u vGroups_t (repOpts.map fun o => o.getD [])
    let groupJets := (List.range r_u).map fun g =>
      CommonCountingAccum.streamGroupJetSum evalGroupFactorJet J ℓ
        (min (2 * n') (vGroups_t.getD g []).length)
        ((n', J, ℓ, k'), (node, dDen),
          (vGroups_t.getD g [], grpMeas_t.getD g [], (word.drop (g * m_rows)).take m_rows),
          (indE, indU, xStar), grpEqLists.getD g [])
    some (CommonCountingAccum.prodJet J ℓ groupJets)
  else none

/-- Variable count `n'` in `MeasStepCtx`. -/
abbrev MeasStepCtx.numVars (ctx : MeasStepCtx) : ℕ :=
  let ((n', _, _), _) := ctx
  n'

/-- Group count `r_u` in `MeasStepCtx`. -/
abbrev MeasStepCtx.numGroups (ctx : MeasStepCtx) : ℕ :=
  let ((_, r_u, _), _) := ctx
  r_u

/-- Jet order `J` in `MeasStepCtx`. -/
abbrev MeasStepCtx.jetOrder (ctx : MeasStepCtx) : ℕ :=
  let (_, (J, _, _), _) := ctx
  J

/-- Jet precision `ℓ` in `MeasStepCtx`. -/
abbrev MeasStepCtx.precision (ctx : MeasStepCtx) : ℕ :=
  let (_, (_, ℓ, _), _) := ctx
  ℓ

/-- Variable-group partition `vGroups_t` in `MeasStepCtx`. -/
abbrev MeasStepCtx.varGroups (ctx : MeasStepCtx) : List (List ℕ) :=
  let (_, _, _, (vGroups_t, _), _) := ctx
  vGroups_t

/-- Variable count `n'` in `SubsetStepCtx`. -/
abbrev SubsetStepCtx.numVars (ctx : SubsetStepCtx) : ℕ :=
  let ((n', _, _), _) := ctx
  n'

/-- Group count `r_u` in `SubsetStepCtx`. -/
abbrev SubsetStepCtx.numGroups (ctx : SubsetStepCtx) : ℕ :=
  let ((_, r_u, _), _) := ctx
  r_u

/-- Jet order `J` in `SubsetStepCtx`. -/
abbrev SubsetStepCtx.jetOrder (ctx : SubsetStepCtx) : ℕ :=
  let (_, _, (J, _, _), _) := ctx
  J

/-- Jet precision `ℓ` in `SubsetStepCtx`. -/
abbrev SubsetStepCtx.precision (ctx : SubsetStepCtx) : ℕ :=
  let (_, _, (_, ℓ, _), _) := ctx
  ℓ

/-- Variable-group partition `vGroups_t` in `SubsetStepCtx`. -/
abbrev SubsetStepCtx.varGroups (ctx : SubsetStepCtx) : List (List ℕ) :=
  let (_, _, _, _, (vGroups_t, _), _) := ctx
  vGroups_t

/-- `measurementStepBody` factors into `evalMeasPayload` followed by optional `addJet`
accumulation. -/
theorem measurementStepBody_eq (inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) :
    measurementStepBody inp =
      let ((_, word), (ctx, acc)) := inp
      (evalMeasPayload (word, ctx)).elim (ctx, acc)
        (fun y => (ctx, addJet ctx.jetOrder ctx.precision acc y)) := by
  unfold measurementStepBody evalMeasPayload; dsimp only; split_ifs <;> rfl

/-- Uniform `ComputableInO` runtime and global `PolyBounded` workspace bound for `evalMeasPayload`,
running in `(r_u * (2 ^ maxGroupDim + 1) + 1) * P` steps and `P` workspace. -/
theorem exists_computableInO_measPayload :
    ∃ P : List ℤ × MeasStepCtx → ℕ,
      PolyBounded (fun wc => (encPair (encList encIntBin) encMeasStepCtx wc).length) P ∧
      ComputableInO evalMeasPayload (encPair (encList encIntBin) encMeasStepCtx)
        (encOption (encList (encList encIntBin)))
        (fun wc =>
          let ctx := wc.2
          (ctx.numGroups * (2 ^ maxGroupDim ctx.numVars ctx.numGroups ctx.varGroups + 1) + 1) *
            P wc)
        P := by
  let eWC := encPair (encList encIntBin) encMeasStepCtx
  have hru_wc : ComputableInPolyTime (fun wc : List ℤ × MeasStepCtx => wc.2.numGroups)
      eWC encUnary := by fun_prop
  have hprepS : ComputableInPolyTime
      (fun p : (List ℤ × MeasStepCtx) × ℕ =>
        ((p.1.2.2.2.2.1.2.getD p.2 [], (p.1.1.drop (p.2 * p.1.2.1.2.2)).take p.1.2.1.2.2),
          min (2 * p.1.2.numVars) (p.1.2.varGroups.getD p.2 []).length))
      (encPair eWC encUnary)
      (encPair (encPair (encList (encList encIntBin)) (encList encIntBin)) encUnary) := by fun_prop
  have hM_pr := fst (encList (encList encIntBin)) (encList encIntBin)
  have ht_pr := snd (encList (encList encIntBin)) (encList encIntBin)
  obtain ⟨ovS, hovS_pb, hovS_eq⟩ :=
    BooleanMeasurements.exists_polyBounded_searchCertificate_time hM_pr ht_pr
  have hSBase : (BooleanMeasurements.searchCertificate hM_pr ht_pr).FactorTimePolySpace
      (fun p => 2 ^ p.2 + 1) :=
    .of_polyBounded hovS_pb (BooleanMeasurements.polyBounded_searchCertificate_space hM_pr ht_pr)
      fun p => (hovS_eq p).le
  obtain ⟨_, hPass1⟩ := exists_factorTimePolySpace_groupMap
    (D := fun wc => maxGroupDim wc.2.numVars wc.2.numGroups wc.2.varGroups) hru_wc
    (hSBase.comp_polyPre hprepS fun _ => Nat.succ_pos _) fun wc g hg => Nat.succ_le_succ
      (Nat.pow_le_pow_right Nat.zero_lt_two
        (min_length_le_maxGroupDim (n' := wc.2.numVars) (vGroups_t := wc.2.varGroups) hg))
  let eWR := encPair eWC (encList (encOption encBits))
  let eWX := encPair eWC encBits
  have hcond : ComputableInPolyTime
      (fun wr : (List ℤ × MeasStepCtx) × List (Option (List Bool)) => wr.2.all Option.isSome)
      eWR encBool := by fun_prop
  have hxStar : ComputableInPolyTime
      (fun wr : (List ℤ × MeasStepCtx) × List (Option (List Bool)) =>
        (wr.1, buildBaseAssignment wr.1.2.numVars wr.1.2.numGroups wr.1.2.varGroups
          (wr.2.map fun o => o.getD []))) eWR eWX := by
    have hwc := fst eWC (encList (encOption encBits))
    have hro := snd eWC (encList (encOption encBits))
    have hctx := hwc.snd'
    unfold encMeasStepCtx at hctx
    have hreps := bi_mapWithId (optionGetDWithInput (snd eWR (encOption encBits)) (const [])) hro
    have hb := computableInPolyTime_buildBaseAssignment hctx.fst'.fst'
      hctx.fst'.snd'.fst' hctx.snd'.snd'.snd'.fst'.fst' hreps
    exact hwc.prod hb
  have hru_wx : ComputableInPolyTime
      (fun wx : (List ℤ × MeasStepCtx) × List Bool => wx.1.2.numGroups) eWX encUnary := by fun_prop
  let eWXG := encPair eWX encUnary
  have hJ_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      p.1.1.2.jetOrder) eWXG encUnary := by fun_prop
  have hℓ_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      p.1.1.2.precision) eWXG encUnary := by fun_prop
  have hd_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      min (2 * p.1.1.2.numVars) (p.1.1.2.varGroups.getD p.2 []).length) eWXG encUnary := by
    have hp1 := fst eWX encUnary; have hg := snd eWX encUnary
    unfold eWX eWC encMeasStepCtx at hp1
    have hctx := hp1.fst'.snd'
    have hVg := (listGetD (encA := encList encNat) []).comp
      (hctx.snd'.snd'.snd'.fst'.fst'.prod hg)
    exact unary_min' (unary_mul' (const 2) hctx.fst'.fst') ((length_list encNat).comp hVg)
  have hctx_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      ((p.1.1.2.numVars, p.1.1.2.jetOrder, p.1.1.2.precision, p.1.1.2.2.1.2.2),
        (p.1.1.2.2.2.1.1, p.1.1.2.2.2.1.2),
        (p.1.1.2.varGroups.getD p.2 [], p.1.1.2.2.2.2.1.2.getD p.2 [],
          (p.1.1.1.drop (p.2 * p.1.1.2.1.2.2)).take p.1.1.2.1.2.2),
        (p.1.1.2.2.2.2.2.1.1, p.1.1.2.2.2.2.2.1.2, p.1.2),
        p.1.1.2.2.2.2.2.2.getD p.2 [])) eWXG encGroupEvalCtx := by fun_prop
  obtain ⟨Pg0, hPg0_pb, hstreamOne⟩ := CommonCountingAccum.computableInO_streamGroupJetSum
    hJ_g hℓ_g hd_g hctx_g computableInPolyTime_evalGroupFactorJet
  obtain ⟨_, hGrpJets⟩ := exists_factorTimePolySpace_groupMap
    (D := fun wx => maxGroupDim wx.1.2.numVars wx.1.2.numGroups wx.1.2.varGroups)
    (cf := ⟨_, Pg0, hstreamOne⟩) hru_wx (.of_polyBounded hPg0_pb hPg0_pb fun _ => le_rfl)
    fun wx g hg => Nat.succ_le_succ (Nat.pow_le_pow_right Nat.zero_lt_two
      (min_length_le_maxGroupDim (n' := wx.1.2.numVars) (vGroups_t := wx.1.2.varGroups) hg))
  have hprodSome : ComputableInPolyTime
      (fun wj : ((List ℤ × MeasStepCtx) × List Bool) × List JetRows =>
        some (CommonCountingAccum.prodJet wj.1.1.2.jetOrder wj.1.1.2.precision wj.2))
      (encPair eWX (encList encJet)) (encOption encJet) := by fun_prop
  let K (wc : List ℤ × MeasStepCtx) : ℕ :=
    wc.2.numGroups * (2 ^ maxGroupDim wc.2.numVars wc.2.numGroups wc.2.varGroups + 1) + 1
  have hIdWX : (NativeCertificate.linear (ei := eWX)
      (ComputableInO.of_eq fun _ => rfl)).FactorTimePolySpace (fun wx => K wx.1) :=
    (NativeCertificate.FactorTimePolySpace.ofIsPolynomial
      (NativeCertificate.linear_isPolynomial (ei := eWX) (ComputableInO.of_eq fun _ => rfl))).mono
      fun _ => Nat.succ_pos _
  have hYesWR := ((hIdWX.prod_same hGrpJets).comp_ofPolyTime
    (fun _ => Nat.succ_pos _) hprodSome).comp_polyPre hxStar fun _ => Nat.succ_pos _
  have hBrWR := NativeCertificate.FactorTimePolySpace.branch (K := fun wr => K wr.1)
    ((NativeCertificate.FactorTimePolySpace.ofPolyTime hcond).mono fun _ => Nat.succ_pos _)
    hYesWR (fun _ _ => le_rfl)
    ((NativeCertificate.FactorTimePolySpace.ofPolyTime
      (const (encIn := eWR) (encOut := encOption encJet) none)).mono fun _ => Nat.succ_pos _)
  have hIdWC : (NativeCertificate.linear (ei := eWC)
      (ComputableInO.of_eq fun _ => rfl)).FactorTimePolySpace K :=
    (NativeCertificate.FactorTimePolySpace.ofIsPolynomial
      (NativeCertificate.linear_isPolynomial (ei := eWC) (ComputableInO.of_eq fun _ => rfl))).mono
      fun _ => Nat.succ_pos _
  have hFull := (((hIdWC.prod_same hPass1).comp hBrWR).mono_const (K' := K) 2
    fun _ => by dsimp only [K]; omega).congr (f' := evalMeasPayload) fun _ => rfl
  obtain ⟨e, hc⟩ := hFull.computableInO
  exact ⟨_, (PolyBounded.self.add (.const 1)).pow e, hc⟩

end LoopCertificates

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
