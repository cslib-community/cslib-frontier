/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time.ZeroError
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Phase
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.ExpectedTime
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# ZPP is zero-error expected polynomial time

The Arora–Barak draft defines `ZPP` as `⋃_c ZTIME(n ^ c)`, through machines that never err and run
in expected polynomial time [Arora and Barak, Definition 7.7][AroraBarak07], and states
`ZPP = RP ∩ coRP` as Theorem 7.8, leaving the proof to Exercise 7 §4. The library's `ZPP` is the
bounded-time class of zero-error verifiers that answer on at least half of the random strings, for
which `Cslib.Complexity.ZPP_eq_RP_inter_coRP` holds. `Cslib.Complexity.ZTIME_pow_subset_ZPP` shows
that the draft's class is contained in it. This file proves the converse, so the two definitions
agree and Theorem 7.8 holds for the draft's `ZPP`.

A zero-error verifier `V` is turned into a Las Vegas machine. Its words are pairs `(a, o)` of the
instance and an optional answer. A round on `(a, none)` draws a fresh random string `r` and moves
to `(a, V (a, r))`; a round on an answer word `(a, some b)` ends the loop. The machine prepares
`(a, none)`, iterates rounds with `Turing.MultiTapePTM.iterateWhile`, and outputs `[b]` from the
last word. Every answer is right, and each round answers with probability at least `1 / 2`, so the
expected running time is a geometric series over rounds of polynomial length
(`Turing.MultiTapePTM.tsum_toOuterMeasure_compl_iterateWhile_le`), and the phases before and after
the loop only add their clocks (`Turing.MultiTapePTM.toOuterMeasure_compl_comp_le_of_halted`,
`Turing.MultiTapePTM.toOuterMeasure_compl_comp_le_of_good`).

## Main results

* `Cslib.Complexity.exists_mem_ZTIME_pow_of_mem_ZPP`: `ZPP ⊆ ⋃_d ZTIME(n ^ d)`.
* `Cslib.Complexity.iUnion_ZTIME_pow_eq_ZPP`: the draft's `ZPP` is the library's `ZPP`.
* `Cslib.Complexity.iUnion_ZTIME_pow_eq_RP_inter_coRP`: Arora and Barak, Theorem 7.8, for the
  draft's `ZPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM
open _root_.Turing.MultiTapePTM.Internal.Oracle Cslib.Probability
open scoped ENNReal

variable {α : Type} {enc : α ↪ List Bool}

/-- A tidy computation of a constant word halts within its clock with that word as output. -/
private theorem eval_runClosedConfigFrom_of_computesTidily_pure {k : ℕ} {State : Type}
    {machine : MultiTapePTM k Bool State} {x w : List Bool} {t : ℕ}
    (h : machine.ComputesTidily x t (pure w)) :
    ProbComp.eval (machine.runClosedConfigFrom t (machine.initialConfig x)) =
      PMF.pure { tapes := wordsCfg x none (fun _ => []) w, channels := Empty.elim } := by
  rw [RunsWords.eval_runClosedConfigFrom (p := pure w) (h []) _ (Cfg.init_eq_wordsCfg _ _),
    ProbComp.eval_pure, PMF.pure_map]
  rfl

/-- A zero-error verifier gives no answer on at most half of the random strings. -/
private theorem toOuterMeasure_none_le {p : Polynomial ℕ} {V : α × List Bool → Option Bool}
    {A : Set α} (h : DecidesWithZeroError enc p V A) (a : α) :
    ProbComp.eval ((fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length)) none ≤
      2⁻¹ := by
  have hhalf := (h a).2
  set n := p.eval (enc a).length
  rw [ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList_map_apply]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    fun r : Fin n → Bool => (V (a, List.ofFn r)).isSome
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsplit
  have hnone : (Finset.univ.filter fun r : Fin n → Bool => V (a, List.ofFn r) = none) =
      Finset.univ.filter fun r : Fin n → Bool => ¬(V (a, List.ofFn r)).isSome = true := by
    simp only [Option.isSome_iff_ne_none, not_not]
  rw [hnone, ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  have hcard : (Finset.univ.filter fun r : Fin n → Bool =>
      ¬(V (a, List.ofFn r)).isSome = true).card * 2 ≤ 2 ^ n := by
    simp only [acceptCount] at hhalf
    omega
  exact_mod_cast hcard

/-- **`ZPP ⊆ ⋃_d ZTIME(n ^ d)`**: repeating a zero-error verifier on fresh random strings until it
answers decides with zero error in expected polynomial time. -/
theorem exists_mem_ZTIME_pow_of_mem_ZPP {A : Set α} (hA : A ∈ ZPP enc) :
    ∃ d, A ∈ ZTIME enc (· ^ d) := by
  classical
  obtain ⟨p, V, hV, hA⟩ := hA
  -- the words `(a, o)` of the iteration
  let encode : α × Option Bool ↪ List Bool := encPair enc (encOption encBool)
  let sv (a : α) : ProbComp (Option Bool) :=
    (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length)
  have hsv : IsPPTOn enc (encOption encBool) sv := IsPPTOn.of_seeded
    ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length enc)) hV
  let body (pair : α × Option Bool) : WordOracleComp Empty (List Bool) :=
    if decide (pair.2 = none) then
      (fun v => encode (pair.1, v)) <$> ProbOracleComp.sample (sv pair.1)
    else pure []
  have hencW : ComputableInPolyTime encode encode encBits := .of_eq fun _ => rfl
  have hencode : ComputableInPolyTime (fun x : (α × Option Bool) × Option Bool =>
      encode (x.1.1, x.2)) (encPair encode (encOption encBool)) encBits :=
    hencW.comp (by fun_prop)
  have hbody : IsTidyOraclePPTOn encode encBits body :=
    IsTidyOraclePPTOn.cond (ComputableInPolyTime.decide_eq'
        (ComputableInPolyTime.snd enc (encOption encBool)) (.const none))
      (((hsv.isOraclePPTOn (Operation := Empty)).oraclePhase.preprocess
        (ComputableInPolyTime.fst enc (encOption encBool))).map_with hencode)
      (IsTidyOraclePPTOn.of_computableInPolyTime (.const []))
  obtain ⟨_, kB, Body, _, bodyM, cB, dB, hbodyM⟩ := hbody
  -- preparing the first word and extracting the answer
  obtain ⟨_, kp, Prep, _, prepM, cp, dp, hprepM⟩ :=
    IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Empty) (input := enc)
      (output := encBits) (f := fun a => encode (a, none))
      (hencW.comp ((ComputableInPolyTime.id' (encIn := enc)).prod (.const none)))
  obtain ⟨_, ke, Ext, _, extM, ce, de, hextM⟩ :=
    IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Empty) (input := encode)
      (output := encBits) (f := fun pair => [pair.2.getD false])
      ((ComputableInPolyTime.of_finite (encIn := encOption encBool) (encOut := encBits)
        fun v : Option Bool => [v.getD false]).comp
        (ComputableInPolyTime.snd enc (encOption encBool)))
  -- the machine: prepare `(a, none)`, iterate rounds, extract the answer
  let IW := bodyM.iterateWhile true
  let mid := IW.comp prepM true
  let Z := extM.comp mid true
  -- the clocks, as functions of the input length
  let L (a : α) : ℕ := 2 * (enc a).length + 3
  let D (a : α) : ℕ := cB * (L a + 1) ^ dB + 10 * L a + 23
  let tp (a : α) : ℕ := cp * ((enc a).length + 1) ^ dp
  let te (a : α) : ℕ := ce * (L a + 1) ^ de
  let B (a : α) : ℕ :=
    (L a + 4 + te a) + ((tp a + (tp a + 4)) + ((8 * L a + 17) + (D a + D a * 2)))
  have hlen (a : α) (v : Option Bool) : encode (a, v) ≠ [] ∧ (encode (a, v)).length ≤ L a := by
    refine ⟨by simp [encode, encPair, frame], ?_⟩
    cases v <;> simp [encode, encPair, frame, encOption, L] <;> omega
  -- for every instance, the miss probabilities of the answer `[indicator A a]` sum to at most `B a`
  have hsum (a : α) : ∑' s, (ProbComp.eval (Z.runClosedConfigFrom s
      (Z.initialConfig (enc a)))).toOuterMeasure
        {final | final.tapes.state = none ∧
          final.tapes.output = [MultiTapeTM.indicator A a]}ᶜ ≤ B a := by
    set w₀ := encode (a, none)
    set ans := encode (a, some (MultiTapeTM.indicator A a))
    -- the loop
    have hbodyAt (v : Option Bool) := (hbodyM (a, v)).mono
      (Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen a v).2 1) dB))
    have hretry : ∀ w ∈ ({w₀} : Set (List Bool)), bodyM.ComputesTidily w (cB * (L a + 1) ^ dB)
        (ProbOracleComp.sample ((fun v => encode (a, v)) <$> sv a)) := fun _ hw =>
      hw ▸ (hbodyAt none).congr fun _ _ _ => by simp [body, encBits, ProbOracleComp.sample_map]
    have hanswer : ∀ w ∈ ({ans} : Set (List Bool)),
        bodyM.ComputesTidily w (cB * (L a + 1) ^ dB) (pure []) := fun _ hw =>
      hw ▸ (hbodyAt (some _)).congr fun _ _ _ => by simp [body, encBits]
    have hsupport : ∀ w ∈ ({w₀} : Set (List Bool)),
        ∀ w' ∈ (ProbComp.eval ((fun v => encode (a, v)) <$> sv a)).support,
          w' ∈ ({w₀} : Set (List Bool)) ∨ w' ∈ ({ans} : Set (List Bool)) := by
      rintro w - w' hw'
      rw [ProbComp.eval_map, ProbComp.eval_map, BitString.eval_sampleList, PMF.map_comp,
        PMF.mem_support_map_iff] at hw'
      obtain ⟨word, hword, rfl⟩ := hw'
      have hwlen := BitString.mem_support_uniformList_iff.mp hword
      cases hv : V (a, word) with
      | none => exact Or.inl (by simp [hv, w₀])
      | some b =>
        have hfn : List.ofFn (fun i => word.get (i.cast hwlen.symm)) = word := by
          apply List.ext_getElem <;> simp [hwlen]
        have hb := (hA a).1 (fun i => word.get (i.cast hwlen.symm)) b (hfn.symm ▸ hv)
        refine Or.inr ?_
        by_cases ha : a ∈ A <;> simp_all [ans, MultiTapeTM.indicator]
    have hq : ∀ w ∈ ({w₀} : Set (List Bool)),
        (ProbComp.eval ((fun v => encode (a, v)) <$> sv a)).toOuterMeasure {w₀} ≤ 2⁻¹ := by
      rintro w -
      rw [PMF.toOuterMeasure_apply_singleton, ProbComp.eval_map,
        Probability.PMF.map_apply_of_injective _ fun v₁ v₂ h => by simpa using encode.injective h]
      exact toOuterMeasure_none_le hA a
    have hloop := tsum_toOuterMeasure_compl_iterateWhile_le true (Set.mem_singleton w₀) hretry
      hanswer hsupport hq (by rintro w (rfl | rfl) <;> exact hlen a _)
    rw [ENNReal.one_sub_inv_two, inv_inv] at hloop
    -- preparing the first word only shifts the clock
    let good₁ : Set (MultiTapeMachine.Config (kB + 1 + 2 + kp + 2) Bool
        (Prep ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ IterateWhile.MachineState Body) Empty
        (enc a)) :=
      {r | r.tapes.state = none ∧ r.tapes.output = ans}
    have hprep : ProbComp.eval (prepM.runClosedConfigFrom (tp a) (prepM.initialConfig (enc a))) =
        PMF.pure { tapes := wordsCfg (enc a) none (fun _ => []) w₀, channels := Empty.elim } :=
      eval_runClosedConfigFrom_of_computesTidily_pure (by simpa [encBits] using hprepM a)
    have hmid (s : ℕ) :
        (ProbComp.eval (mid.runClosedConfigFrom ((tp a + (tp a + 4)) + s)
          (mid.initialConfig (enc a)))).toOuterMeasure good₁ᶜ ≤
        (ProbComp.eval (IW.runClosedConfigFrom s (IW.initialConfig w₀))).toOuterMeasure
          {final | final.tapes.state = none ∧ final.tapes.output ∈ ({ans} : Set (List Bool))}ᶜ := by
      rw [Nat.add_assoc (tp a) (tp a + 4) s]
      refine (toOuterMeasure_compl_comp_le_of_halted prepM IW true (good := good₁)
        (fun c hc => hc.1) (tp a) s fun r hr => ?_).trans_eq ?_
      · rw [hprep, PMF.mem_support_pure_iff] at hr
        exact hr ▸ rfl
      · rw [hprep, PMF.pure_bind, PMF.toOuterMeasure_map_apply]
        refine congrArg _ (Set.ext fun c => ?_)
        change ¬(((c.tapes.state.map Sum.inr).map Sum.inr = none) ∧ c.tapes.output = ans) ↔
          ¬(c.tapes.state = none ∧ c.tapes.output ∈ ({ans} : Set (List Bool)))
        rcases c.tapes.state with _ | _ <;> simp
    -- extracting the answer only shifts the clock
    have hZ (s : ℕ) :
        (ProbComp.eval (Z.runClosedConfigFrom ((L a + 4 + te a) + s)
          (Z.initialConfig (enc a)))).toOuterMeasure
          {final | final.tapes.state = none ∧
            final.tapes.output = [MultiTapeTM.indicator A a]}ᶜ ≤
        (ProbComp.eval (mid.runClosedConfigFrom s (mid.initialConfig (enc a)))).toOuterMeasure
          good₁ᶜ := by
      rw [Nat.add_comm (L a + 4 + te a) s]
      refine toOuterMeasure_compl_comp_le_of_good mid extM true
        (good := {final | final.tapes.state = none ∧
          final.tapes.output = [MultiTapeTM.indicator A a]}) (fun c hc => hc.1)
        (good₁ := good₁) (fun r hr => ⟨hr.1, hr.2 ▸ (hlen a _).2⟩) (te a)
        (fun r hr final hfinal => ?_) s
      have hspec : extM.ComputesTidily r.tapes.output (te a)
          (pure [MultiTapeTM.indicator A a]) := by
        rw [hr.2]
        exact ((hextM (a, some _)).mono (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left
          (Nat.add_le_add_right (hlen a _).2 1) de))).congr fun _ _ _ => by simp [encBits]
      rw [eval_runClosedConfigFrom_of_computesTidily_pure hspec, PMF.mem_support_pure_iff] at hfinal
      exact hfinal ▸ ⟨rfl, rfl⟩
    -- the sums
    have hsumMid := tsum_le_add_of_shift (tp a + (tp a + 4))
      (fun s => PMF.toOuterMeasure_le_one
        (ProbComp.eval (mid.runClosedConfigFrom s (mid.initialConfig (enc a)))) good₁ᶜ) hmid
    have hsumZ := tsum_le_add_of_shift (L a + 4 + te a)
      (fun s => PMF.toOuterMeasure_le_one
        (ProbComp.eval (Z.runClosedConfigFrom s (Z.initialConfig (enc a)))) _) hZ
    refine hsumZ.trans ((add_le_add le_rfl (hsumMid.trans (add_le_add le_rfl hloop))).trans_eq ?_)
    simp only [B, D]
    push_cast
    ring
  -- the bound is polynomial
  have hB : PolyBounded (fun a => (enc a).length) B := by growth_poly
  obtain ⟨c, d, hc⟩ := hB.exists_le
  refine ⟨d, c * 2 ^ d, c, _, _, inferInstance, Z, fun a => ⟨?_, ?_⟩⟩
  · calc Z.expectedTime (enc a)
        ≤ ∑' s, (ProbComp.eval (Z.runClosedConfigFrom s (Z.initialConfig (enc a)))).toOuterMeasure
          {final | final.tapes.state = none ∧
            final.tapes.output = [MultiTapeTM.indicator A a]}ᶜ :=
          expectedTime_le_tsum_toOuterMeasure_compl Z fun _ hc => hc.1
      _ ≤ B a := hsum a
      _ ≤ ((c * 2 ^ d * (enc a).length ^ d + c : ℕ) : ℝ≥0∞) := by
          exact_mod_cast (hc a).trans (Nat.mul_add_one_pow_le_two_pow c d _)
  · -- the probability of having answered tends to one, since the misses are summable
    set G : Set (MultiTapeMachine.Config _ Bool _ Empty (enc a)) :=
      {final | final.tapes.state = none ∧ final.tapes.output = [MultiTapeTM.indicator A a]}
    have hP (s : ℕ) : (ProbComp.eval (Z.runClosedConfigFrom s
        (Z.initialConfig (enc a)))).toOuterMeasure G = 1 - (ProbComp.eval (Z.runClosedConfigFrom s
          (Z.initialConfig (enc a)))).toOuterMeasure Gᶜ :=
      ENNReal.eq_sub_of_add_eq (PMF.toOuterMeasure_ne_top _ _)
        (PMF.toOuterMeasure_add_compl_ennreal _ G)
    simp only [hP, ← ENNReal.sub_iInf]
    rw [le_antisymm (ge_of_tendsto' (ENNReal.tendsto_atTop_zero_of_tsum_ne_top
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top (B a)) (hsum a))) fun s => iInf_le _ s)
      zero_le, tsub_zero]

/-- **The draft's `ZPP` is the library's `ZPP`**: a problem is decided by zero-error verifiers in
polynomial time if and only if it is decided with zero error in expected time `O(n ^ d)` for some
`d` [Arora and Barak, Definition 7.7][AroraBarak07]. -/
theorem mem_ZPP_iff_exists_mem_ZTIME_pow {A : Set α} :
    A ∈ ZPP enc ↔ ∃ d, A ∈ ZTIME enc (· ^ d) :=
  ⟨exists_mem_ZTIME_pow_of_mem_ZPP, fun ⟨d, hA⟩ => ZTIME_pow_subset_ZPP d hA⟩

/-- `⋃_d ZTIME(n ^ d) = ZPP`. -/
theorem iUnion_ZTIME_pow_eq_ZPP : ⋃ d, ZTIME enc (· ^ d) = ZPP enc :=
  Set.ext fun _ => Set.mem_iUnion.trans mem_ZPP_iff_exists_mem_ZTIME_pow.symm

/-- **Arora and Barak, Theorem 7.8**: `ZPP = RP ∩ coRP`, for the draft's `ZPP = ⋃_c ZTIME(n ^ c)`
of zero-error expected polynomial time [Arora and Barak, Definition 7.7, Theorem 7.8,
Exercise 7 §4][AroraBarak07]. -/
theorem iUnion_ZTIME_pow_eq_RP_inter_coRP : ⋃ d, ZTIME enc (· ^ d) = RP enc ∩ coRP enc := by
  rw [iUnion_ZTIME_pow_eq_ZPP, ZPP_eq_RP_inter_coRP]

end Cslib.Complexity
