/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.CNF.GreedyParitySearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen

/-!
# Greedy parity search with an encoded context

The selector and greedy program are those of `GreedyParitySearch`; this module supplies one
native machine for a counter on `(context, rows)`. The context is part of every live state and
counter input. Its encoding is charged even when candidate enumeration or the outer loop is empty.
This closes the fixed-counter interface gap without constructing the common-zero counter or the
initial Tanner matrix of [OpenAI2026ETH], §§6.2–6.3 (pp. 42–43). A counter fixed before the runtime
inputs is the unit context, which gives the fixed-counter bounds for `GreedyParitySearch`.

## Main definitions

* `GreedyContext.encContextRows`: the encoding of a counter input `(context, rows)`.
* `GreedyContext.selectCertificate`: uniform context-dependent candidate selection.
* `GreedyContext.greedyCertificate`: the existing `greedyParityRows` on a runtime context.

## Main results

* `GreedyContext.computableInO_greedy`: independent time and polynomial-workspace bounds.
* `GreedyContext.count_greedy_eq_card_sat`: the fixed-counter correctness theorem pointwise.
* `computableInO_selectBestTestRow`, `computableInO_greedyParityRows`,
  `computableInPolySpace_greedyParityRows`: fixed-counter time and workspace bounds, from the unit
  context.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§6.2–6.3.

The certificate construction extends Anton Kovsharov's `GreedyParitySearch` implementation.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.GreedyContext

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM

variable {C : Type} (encC : C ↪ List Bool)

/-- Counter input: the pair `(c, rows)` of the framed context `c`, then the concatenation of the
framed rows, each row a bit string written as is (`encBits`). -/
abbrev encContextRows : C × List (List Bool) ↪ List Bool :=
  encPair encC (encList encBits)

/-- Full selector input: context, unary width and tuple length, and retained rows. -/
def encInput : (C × ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encC encSelectBestIn

/-- Full greedy input: context, unary round parameter, width and tuple length, and rows. -/
def encGreedyInput : (C × ℕ × ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encC encGreedyIn

/-- The original selector accumulator with the counter's runtime context retained. -/
private def encAcc : (C × SelectBestAcc) ↪ List Bool := encPair encC encSelectBestAcc

variable {encC}

end Cslib.Logic.PL.CNF.GreedyContext
end

public section
namespace Cslib.Logic.PL.CNF.GreedyContext

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM
variable {C : Type} {encC : C ↪ List Bool}

private def augment (s : ℕ × C × SelectBestAcc) : C × List (List Bool) :=
  (s.2.1, augCandidateRows (s.1, s.2.2))

private theorem augment_polyTime : ComputableInPolyTime (augment (C := C))
    (encPair encNat (encAcc encC)) (encPair encC (encList encBits)) := by
  have := computableInPolyTime_augCandidateRows
  fun_prop [augment, encAcc]

private def finish (p : (ℕ × C × SelectBestAcc) × ℕ) : C × SelectBestAcc :=
  (p.1.2.1, finishSelectBestStep ((p.1.1, p.1.2.2), p.2))

private theorem finish_polyTime : ComputableInPolyTime (finish (C := C))
    (encPair (encPair encNat (encAcc encC)) encNat) (encAcc encC) := by
  have := computableInPolyTime_finishSelectBestStep
  fun_prop [finish, encAcc]

private def step (count : C × List (List Bool) → ℕ)
    (s : ℕ × C × SelectBestAcc) : C × SelectBestAcc :=
  (s.2.1, selectBestStep (fun rows => count (s.2.1, rows)) (s.1, s.2.2))

private noncomputable def stepCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat) :
    NativeCertificate (step count) (encPair encNat (encAcc encC)) (encAcc encC) :=
  let cId := NativeCertificate.linear (ComputableInO.of_linear
    (.of_eq fun _ : ℕ × C × SelectBestAcc => rfl))
  ((NativeCertificate.ofPolyTime finish_polyTime).comp
    (cId.prod (cCount.comp (NativeCertificate.ofPolyTime augment_polyTime)))).congr fun _ => rfl

private theorem run_eq (count : C × List (List Bool) → ℕ) (c : C)
    (acc : SelectBestAcc) (j : ℕ) :
    IndexFold.run (step count) j (c, acc) =
      (j, c, (IndexFold.run (selectBestStep (fun rows => count (c, rows))) j acc).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [IndexFold.run_succ, ih, IndexFold.run_succ]
    simp only [IndexFold.step, step, IndexFold.run_index]
    congr 3
    exact Prod.ext (IndexFold.run_index _ _ _).symm rfl

private theorem run_params (count : C × List (List Bool) → ℕ) (c : C)
    (m P j : ℕ) (rows : List (List Bool)) :
    let s := IndexFold.run (step count) j (c, (m, P), rows, none)
    s.2.1 = c ∧ s.2.2.1 = (m, P) ∧ s.2.2.2.1 = rows := by
  induction j with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ j ih =>
    simp only [IndexFold.run_succ, IndexFold.step, step, selectBestStep,
      ih.1, ih.2.1, ih.2.2, and_self]

private def countIn (a : C × ℕ × ℕ × List (List Bool)) : ℕ :=
  candidateTupleCount a.2.1 a.2.2.1

private theorem countIn_polyTime :
    ComputableInPolyTime (countIn (C := C)) (encInput encC) encNat := by
  unfold countIn encInput encSelectBestIn
  exact computableInPolyTime_candidateTupleCount' (by fun_prop) (by fun_prop)

private def initIn (a : C × ℕ × ℕ × List (List Bool)) : C × SelectBestAcc :=
  (a.1, (a.2.1, a.2.2.1), a.2.2.2, none)

private theorem initIn_polyTime :
    ComputableInPolyTime (initIn (C := C)) (encInput encC) (encAcc encC) := by
  fun_prop [initIn, encInput, encSelectBestIn, encAcc, encSelectBestAcc]

private def extract (r : ℕ × C × SelectBestAcc) : List Bool :=
  r.2.2.2.2.elim (List.replicate r.2.2.1.1 false) Prod.fst

private theorem extract_polyTime :
    ComputableInPolyTime (extract (C := C)) (encPair encNat (encAcc encC)) encBits := by
  fun_prop [extract]

private theorem selectCertificate_eq (count : C × List (List Bool) → ℕ)
    (a : C × ℕ × ℕ × List (List Bool)) :
    (extract ∘ IndexFold.run (step count) (countIn a) ∘ initIn) a =
      selectBestTestRow (fun rows => count (a.1, rows)) a.2.1 a.2.2.1 a.2.2.2 := by
  have hp := (run_params count a.1 a.2.1 a.2.2.1
    (candidateTupleCount a.2.1 a.2.2.1) a.2.2.2).2.1
  rw [run_eq] at hp
  simp only [Function.comp_apply, countIn, initIn, run_eq, extract, selectBestTestRow]
  rw [congrArg Prod.fst hp]

/-- One fixed native selector for all encoded contexts. Empty candidate spaces return the zero
row, exactly as `selectBestTestRow`; otherwise its first-minimum semantics are unchanged. -/
noncomputable def selectCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encContextRows encC) encNat) :
    NativeCertificate
      (fun ((c, m, P, rows) : C × ℕ × ℕ × List (List Bool)) =>
        selectBestTestRow (fun rows => count (c, rows)) m P rows)
      (encInput encC) encBits :=
  ((NativeCertificate.ofPolyTime extract_polyTime).comp
    (IndexFold.certificate (NativeCertificate.ofPolyTime countIn_polyTime)
      (NativeCertificate.ofPolyTime initIn_polyTime) (stepCertificate cCount))).congr
    (selectCertificate_eq count)

private def appendRow (p : (C × ℕ × ℕ × List (List Bool)) × List Bool) :
    C × ℕ × ℕ × List (List Bool) :=
  (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2 ++ [p.2])

private theorem appendRow_polyTime : ComputableInPolyTime (appendRow (C := C))
    (encPair (encInput encC) encBits) (encInput encC) := by
  fun_prop [appendRow, encInput, encSelectBestIn]

private def outerStep (count : C × List (List Bool) → ℕ)
    (s : C × ℕ × ℕ × List (List Bool)) : C × ℕ × ℕ × List (List Bool) :=
  (s.1, s.2.1, s.2.2.1, s.2.2.2 ++
    [selectBestTestRow (fun rows => count (s.1, rows)) s.2.1 s.2.2.1 s.2.2.2])

private theorem outerStep_iterate (count : C × List (List Bool) → ℕ) (c : C)
    (m P i : ℕ) (rows : List (List Bool)) :
    (outerStep count)^[i] (c, m, P, rows) =
      (c, m, P, greedyParityRowsAt (fun rows => count (c, rows)) m P rows i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, outerStep, greedyParityRowsAt_succ]

private noncomputable def outerCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat) :
    NativeCertificate (outerStep count) (encInput encC) (encInput encC) :=
  let cId := NativeCertificate.linear (ComputableInO.of_linear
    (.of_eq fun _ : C × ℕ × ℕ × List (List Bool) => rfl))
  ((NativeCertificate.ofPolyTime appendRow_polyTime).comp
    (cId.prod (selectCertificate cCount))).congr fun _ => rfl

private def roundCount (a : C × ℕ × ℕ × ℕ × List (List Bool)) : ℕ := 3 * a.2.1

private theorem roundCount_polyTime :
    ComputableInPolyTime (roundCount (C := C)) (encGreedyInput encC) encNat := by
  unfold roundCount encGreedyInput encGreedyIn
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

private def outerInit (a : C × ℕ × ℕ × ℕ × List (List Bool)) :
    C × ℕ × ℕ × List (List Bool) := (a.1, a.2.2)

private theorem outerInit_polyTime :
    ComputableInPolyTime (outerInit (C := C)) (encGreedyInput encC) (encInput encC) := by
  fun_prop [outerInit, encGreedyInput, encGreedyIn, encInput]

/-- One fixed machine runs `3n` greedy rounds for the runtime context. The context survives every
candidate and round; the returned rows are the original `greedyParityRows` specialization. -/
noncomputable def greedyCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encContextRows encC) encNat) :
    NativeCertificate
      (fun ((c, n, m, P, rows) : C × ℕ × ℕ × ℕ × List (List Bool)) =>
        greedyParityRows (fun rows => count (c, rows)) n m P rows)
      (encGreedyInput encC) (encList encBits) :=
  (NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.snd
    (NativeCertificate.iterate (NativeCertificate.ofPolyTime roundCount_polyTime)
      (NativeCertificate.ofPolyTime outerInit_polyTime) (outerCertificate cCount))))).congr
    fun ⟨_, _, _, _, _⟩ => by simp only [roundCount, outerInit, outerStep_iterate]; rfl

/-- The existing Lemma 6.2 correctness theorem, specialized at a runtime context. Positivity,
initial support, and counter agreement on the stated bounded candidate systems are essential.
This statement constructs neither that counter nor the initial rows. -/
theorem count_greedy_eq_card_sat {V : Type*} [Fintype V] [DecidableEq V]
    (count : C × List (List Bool) → ℕ) (c : C) (φ : CNF V) {P : ℕ}
    (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P) {initRows : List (List Bool)}
    (hinit_len : ∀ r ∈ initRows, r.length = φ.length)
    (hcount : ∀ rows, (∀ r ∈ rows, r.length = φ.length) →
      rows.length ≤ initRows.length + 3 * Fintype.card V →
      (∀ r ∈ rows, r ∈ initRows ∨ r.count true ≤ P) →
      count (c, rows) = numPassing φ.violations (rows.map (ofList φ.length)))
    (hinit : ∀ σ : V → Bool,
      PassesTests φ.violations (initRows.map (ofList φ.length)) σ →
        φ.eval σ = false → φ.length ≤ P * weight (φ.violations σ)) :
    count (c, greedyParityRows (fun rows => count (c, rows))
      (Fintype.card V) φ.length P initRows) =
      #{σ : V → Bool | φ.eval σ = true} :=
  countSys_greedyParityRows_eq_card_sat φ hn hP hinit_len hcount hinit

private theorem input_le (c : C) (m P : ℕ) (rows : List (List Bool)) :
    (encC c).length ≤ (encInput encC (c, m, P, rows)).length ∧
    m ≤ (encInput encC (c, m, P, rows)).length ∧
    P ≤ (encInput encC (c, m, P, rows)).length ∧
    (encList encBits rows).length ≤ (encInput encC (c, m, P, rows)).length := by
  simp only [encInput, encSelectBestIn, length_encPair, encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega⟩

section
variable {α β γ : Type} {ei : α ↪ List Bool} {eb : β ↪ List Bool} {eg : γ ↪ List Bool}

private def AdditiveBounds {f : α → β} (c : NativeCertificate f ei eb)
    (M : α → ℕ) (Pred : α → ℕ → Prop) : Prop :=
  ∃ P : α → ℕ, PolyBounded (fun a => (ei a).length) P ∧
    ∀ a, c.space a ≤ P a ∧ (∀ R, Pred a R → c.time a ≤ M a * (P a + R))

private theorem AdditiveBounds.mono {f : α → β} {c : NativeCertificate f ei eb}
    {M₁ M₂ : α → ℕ} {P₁ P₂ : α → ℕ → Prop} (h : AdditiveBounds c M₁ P₁)
    (hM : ∀ a, M₁ a ≤ M₂ a) (hP : ∀ a R, P₂ a R → P₁ a R) : AdditiveBounds c M₂ P₂ :=
  let ⟨P, hPoly, hB⟩ := h
  ⟨P, hPoly, fun a => ⟨(hB a).1, fun R hR =>
    ((hB a).2 R (hP a R hR)).trans (Nat.mul_le_mul_right _ (hM a))⟩⟩

private theorem AdditiveBounds.id_prod {f : α → β} {c : NativeCertificate f ei eb}
    {M : α → ℕ} {Pred : α → ℕ → Prop} (h : AdditiveBounds c M Pred) (hM : ∀ a, 1 ≤ M a) :
    let cId : NativeCertificate id ei ei :=
      NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl))
    AdditiveBounds (cId.prod c) M Pred := by
  obtain ⟨P, hP, hB⟩ := h
  refine ⟨_, PolyBounded.self.add hP, fun a => ⟨?_, fun R hR => ?_⟩⟩
  · have := (hB a).1
    simp only [NativeCertificate.prod_space, NativeCertificate.linear_space]; omega
  · have := (hB a).2 R hR; have := hM a
    simp only [NativeCertificate.prod_time, NativeCertificate.linear_time]; nlinarith

private theorem AdditiveBounds.comp_ofPolyTime {f : α → β} {r : β → γ}
    {c : NativeCertificate f ei eb} {M : α → ℕ} {Pred : α → ℕ → Prop}
    (h : AdditiveBounds c M Pred) (hM : ∀ a, 1 ≤ M a) (hr : ComputableInPolyTime r eb eg) :
    AdditiveBounds ((NativeCertificate.ofPolyTime hr).comp c) M Pred := by
  obtain ⟨P, hP, hB⟩ := h
  have hlen := NativeCertificate.polyBounded_length_of_space (hP.mono fun a => (hB a).1)
  have hcr := NativeCertificate.ofPolyTime_isPolynomial hr
  refine ⟨_, (hP.add (hcr.1.comp hlen)).add (hcr.2.comp hlen), fun a => ⟨?_, fun R hR => ?_⟩⟩
  · have := (hB a).1; simp only [NativeCertificate.comp_space]; omega
  · have := (hB a).2 R hR; have := hM a; simp only [NativeCertificate.comp_time]; nlinarith

private theorem AdditiveBounds.iterate {n : α → ℕ} {init : α → β} {stepF : β → β}
    (cn : NativeCertificate n ei encNat) (ci : NativeCertificate init ei eb)
    {cs : NativeCertificate stepF eb eb} {Ms : β → ℕ} {M B : α → ℕ} {Pred : β → ℕ → Prop}
    (hcn : cn.IsPolynomial) (hci : ci.IsPolynomial) (hcs : AdditiveBounds cs Ms Pred)
    (hM : ∀ a, 1 ≤ M a) (hB : PolyBounded (fun a => (ei a).length) B)
    (hMs : ∀ a j, j ≤ n a → Ms (stepF^[j] (init a)) ≤ M a)
    (hb : ∀ a j, j ≤ n a → (eb (stepF^[j] (init a))).length ≤ B a) :
    AdditiveBounds (NativeCertificate.iterate cn ci cs) (fun a => (n a + 1) * M a)
      (fun a R => ∀ j ≤ n a, Pred (stepF^[j] (init a)) R) := by
  obtain ⟨Ps, hPs, hBs⟩ := hcs; obtain ⟨cp, dp, hp_le⟩ := hPs.exists_le
  have hclock := (cn.polyTime hcn).polyBounded_length
  let pMax a := cp * (B a + 1) ^ dp
  let P a := cn.time a + ci.time a + cn.space a + ci.space a +
    pMax a + B a + ((encNat (n a)).length + 1) ^ 2
  refine ⟨P, ((((((hcn.1.add hci.1).add hcn.2).add hci.2).add
    (NativeCertificate.polyBounded_pow_of_polyBounded hB cp dp)).add hB).add
    ((hclock.add (.const 1)).pow 2)), fun a => ?_⟩
  have hmaxB := NativeCertificate.maxStateLength_le eb stepF (n a) (init a) (hb a)
  have hPs_le (j : ℕ) (hj : j ≤ n a) : Ps (stepF^[j] (init a)) ≤ pMax a :=
    (hp_le _).trans (Nat.mul_le_mul_left cp
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hb a j hj) 1) dp))
  refine ⟨?_, fun R hR => ?_⟩
  · have hmaxS := NativeCertificate.maxRoundSpace_le cs (n a) (init a) fun j hj =>
      ((hBs _).1).trans (hPs_le j hj)
    have : (encNat (n a)).length ≤ ((encNat (n a)).length + 1) ^ 2 := by rw [sq]; nlinarith
    rw [NativeCertificate.iterate_space]; dsimp only [P]; omega
  · have hmaxT : NativeCertificate.maxRoundTime cs (n a) (init a) ≤ M a * (pMax a + R) :=
      NativeCertificate.maxRoundTime_le cs (n a) (init a) fun j hj =>
        ((hBs _).2 R (hR j hj)).trans
          (Nat.mul_le_mul (hMs a j hj) (Nat.add_le_add_right (hPs_le j hj) R))
    have hMa := hM a; have hpos : 1 ≤ (n a + 1) * M a := Nat.mul_pos (Nat.succ_pos _) hMa
    have hround : NativeCertificate.maxRoundTime cs (n a) (init a) +
        NativeCertificate.maxStateLength eb stepF (n a) (init a) +
        ((encNat (n a)).length + 1) ^ 2 ≤
        M a * (pMax a + B a + ((encNat (n a)).length + 1) ^ 2 + R) := by nlinarith
    rw [NativeCertificate.iterate_time]
    exact (Nat.add_le_add (Nat.le_mul_of_pos_left _ hpos) (Nat.mul_le_mul_left _ hround)).trans
      ((by ring : _ = (n a + 1) * M a *
        (cn.time a + ci.time a + pMax a + B a + ((encNat (n a)).length + 1) ^ 2 + R)).le.trans
        (Nat.mul_le_mul_left _ (by dsimp only [P]; omega)))

private theorem AdditiveBounds.computableInO {f : α → β} {c : NativeCertificate f ei eb}
    {M : α → ℕ} {Pred : α → ℕ → Prop}
    (h : AdditiveBounds c M Pred) (R : α → ℕ) (hR : ∀ a, Pred a (R a)) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO f ei eb (fun a => M a * (poly (ei a).length + R a))
        (fun a => poly (ei a).length) := by
  obtain ⟨P, ⟨poly, hpoly, hle⟩, hB⟩ := h
  exact ⟨poly, hpoly, c.computes.mono_le
    (fun a => ((hB a).2 (R a) (hR a)).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hle a) _)))
    (fun a => ((hB a).1).trans (hle a))⟩

end

private theorem select_bounds {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat)
    (hSpace : PolyBounded (fun r => (encPair encC (encList encBits) r).length) cCount.space) :
    AdditiveBounds (selectCertificate cCount)
      (fun a => candidateTupleCount a.2.1 a.2.2.1 + 1)
      (fun a R => ∀ j ≤ candidateTupleCount a.2.1 a.2.2.1,
        cCount.time (a.1, a.2.2.2 ++
          [materializeTestRow a.2.1 (decodeTestTuple a.2.1 a.2.2.1 j)]) ≤ R) := by
  obtain ⟨cOut, -, hOutLen⟩ := cCount.computes
  obtain ⟨pSp, hpSp, hmSp, hSp⟩ := exists_mono_poly hSpace
  have hAug := NativeCertificate.ofPolyTime_isPolynomial (augment_polyTime (encC := encC))
  obtain ⟨Ps, hPs, hBs⟩ : AdditiveBounds (stepCertificate cCount)
      (fun _ => 1) (fun s R => cCount.time (augment s) ≤ R) :=
    (AdditiveBounds.id_prod
      (c := cCount.comp (NativeCertificate.ofPolyTime (augment_polyTime (encC := encC))))
      ⟨_, (hAug.1.add hAug.2).add
        (hSpace.comp (augment_polyTime (encC := encC)).polyBounded_length),
        fun _ => ⟨by simp only [NativeCertificate.comp_space]; omega,
          fun _ _ => by simp only [NativeCertificate.comp_time, one_mul]; omega⟩⟩
      (fun _ => le_rfl)).comp_ofPolyTime (fun _ => le_rfl) finish_polyTime
  have hRound : AdditiveBounds (IndexFold.roundCertificate (stepCertificate cCount))
      (fun _ => 1) (fun s R => cCount.time (augment s) ≤ R) :=
    ⟨fun p => (encPair encNat (encAcc encC) p).length + ((encNat p.1).length + 1) ^ 2 + Ps p,
      by growth_poly, fun p => ⟨by
      have := (hBs p).1; have : (encNat p.1).length + 1 ≤ ((encNat p.1).length + 1) ^ 2 := by
        rw [sq]; nlinarith
      change (encPair encNat (encAcc encC) p).length + ((encNat p.1).length + 1) +
        (stepCertificate cCount).space p ≤ _; dsimp only; omega,
      fun R hR => by
        have h := (hBs p).2 R hR; rw [one_mul] at h ⊢
        change (encPair encNat (encAcc encC) p).length + ((encNat p.1).length + 1) ^ 2 +
          (stepCertificate cCount).time p ≤ _; dsimp only; omega⟩⟩
  let qSys (L : ℕ) := pSp (5 * L + 2); let vBound (L : ℕ) := cOut * (qSys L + 1)
  let bAcc (L : ℕ) := 12 * L + vBound L + 7; let lIdx (L : ℕ) := 2 * L * L + 1
  let bFull (L : ℕ) := 2 * lIdx L + 1 + bAcc L
  have hbFullP : PolyBounded (fun a => (encInput encC a).length)
      (fun a => bFull (encInput encC a).length) :=
    .of_polynomiallyBounded _ (by dsimp only [bFull, lIdx, bAcc, vBound, qSys]; fun_prop)
  have hbFull : ∀ a : C × ℕ × ℕ × List (List Bool), ∀ j ≤ countIn a,
      (encPair encNat (encAcc encC) ((IndexFold.step (step count))^[j] (0, initIn a))).length ≤
        bFull (encInput encC a).length := by
    rintro ⟨c, m, P, rows⟩ j hj
    obtain ⟨hc_le, hm_le, hP_le, hrows_le⟩ := input_le (encC := encC) c m P rows
    set L := (encInput encC (c, m, P, rows)).length
    let candRow (i : ℕ) := materializeTestRow m (decodeTestTuple m P i)
    have hq_i (i : ℕ) : cCount.space (c, rows ++ [candRow i]) ≤ qSys L := (hSp _).trans (hmSp (by
      enc_len [candRow, encList_append, List.append_nil, length_materializeTestRow]))
    have hv_i (i : ℕ) : (encNat (count (c, rows ++ [candRow i]))).length ≤ vBound L :=
      (hOutLen _).trans (Nat.mul_le_mul_left cOut (Nat.add_le_add_right (hq_i i) 1))
    have hlIdx : (encNat (countIn (c, m, P, rows))).length ≤ lIdx L :=
      (length_encNat_candidateTupleCount_le m P).trans (by
        have := Nat.mul_le_mul hP_le (show 2 * m ≤ 2 * L by omega); dsimp only [lIdx]; nlinarith)
    have hbAcc : (encAcc encC (IndexFold.run (step count) j (c, (m, P), rows, none)).2).length ≤
        bAcc L := by
      have hb := length_encSelectBestAcc_run_le (fun r => count (c, r)) m P j rows
        (fun i _ => hv_i i)
      simp only [run_eq, encAcc, length_encPair]; dsimp only [bAcc]; omega
    exact (IndexFold.length_run_le (step count) (c, (m, P), rows, none) hj hbAcc).trans
      (by dsimp only [bFull]; omega)
  have hLoop := AdditiveBounds.iterate
    (NativeCertificate.ofPolyTime (countIn_polyTime (encC := encC)))
    ((NativeCertificate.const (em := encNat) 0).prod
      (NativeCertificate.ofPolyTime (initIn_polyTime (encC := encC))))
    (NativeCertificate.ofPolyTime_isPolynomial (countIn_polyTime (encC := encC)))
    (NativeCertificate.prod_isPolynomial _ _ (NativeCertificate.const_isPolynomial 0)
      (NativeCertificate.ofPolyTime_isPolynomial (initIn_polyTime (encC := encC))))
    hRound (M := fun _ => 1) (fun _ => le_rfl) hbFullP (fun _ _ _ => le_rfl) hbFull
  refine AdditiveBounds.mono (c := selectCertificate cCount)
    (hLoop.comp_ofPolyTime (fun _ => by omega) (extract_polyTime (encC := encC)))
    (fun _ => by dsimp only [countIn]; omega) fun ⟨c, m, P, rows⟩ R hR j hj => ?_
  let st := IndexFold.run (step count) j (c, (m, P), rows, none)
  have hparams := run_params count c m P j rows
  have haug_st : augment st = (c, rows ++ [materializeTestRow m (decodeTestTuple m P j)]) := by
    simp only [augment, augCandidateRows, candRowOfState]
    rw [hparams.1, hparams.2.2, IndexFold.run_index (step count) j (c, (m, P), rows, none),
      congrArg Prod.fst hparams.2.1, congrArg Prod.snd hparams.2.1]
  exact haug_st ▸ hR j hj

/-- Uniform selector time and polynomial workspace, measured in the full context/input encoding.
The counter-time premise includes `j = (2m)^P`: the native iterator uses inclusive prefix maxima,
so this endpoint is charged even though that candidate is not executed. -/
theorem computableInO_select {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encContextRows encC) encNat)
    (hSpace : PolyBounded (fun r => (encContextRows encC r).length) cCount.space)
    (R : C × ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a,
      let (c, m, P, rows) := a
      ∀ j ≤ candidateTupleCount m P,
        cCount.time
          (c, rows ++ [materializeTestRow m (decodeTestTuple m P j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun ((c, m, P, rows) : C × ℕ × ℕ × List (List Bool)) =>
          selectBestTestRow (fun r => count (c, r)) m P rows)
        (encInput encC) encBits
        (fun a =>
          let (_, m, P, _) := a
          (candidateTupleCount m P + 1) * (poly (encInput encC a).length + R a))
        (fun a => poly (encInput encC a).length) :=
  (select_bounds cCount hSpace).computableInO R hR

private theorem greedy_input_le (c : C) (n m P : ℕ) (rows : List (List Bool)) :
    (encC c).length ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    n ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    m ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    P ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    (encList encBits rows).length ≤ (encGreedyInput encC (c, n, m, P, rows)).length := by
  simp only [encGreedyInput, encGreedyIn, encSelectBestIn, length_encPair,
    encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

private theorem greedy_bounds {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encContextRows encC) encNat)
    (hSpace : PolyBounded (fun r => (encContextRows encC r).length) cCount.space) :
    AdditiveBounds (greedyCertificate cCount)
      (fun a => (3 * a.2.1 + 1) * (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1))
      (fun a R => ∀ i ≤ 3 * a.2.1, ∀ j ≤ candidateTupleCount a.2.2.1 a.2.2.2.1,
        cCount.time (a.1,
          greedyParityRowsAt (fun r => count (a.1, r)) a.2.2.1 a.2.2.2.1 a.2.2.2.2 i ++
            [materializeTestRow a.2.2.1 (decodeTestTuple a.2.2.1 a.2.2.2.1 j)]) ≤ R) := by
  have hOuter : AdditiveBounds (outerCertificate cCount)
      (fun s => candidateTupleCount s.2.1 s.2.2.1 + 1)
      (fun s R => ∀ j ≤ candidateTupleCount s.2.1 s.2.2.1,
        cCount.time (s.1, s.2.2.2 ++
          [materializeTestRow s.2.1 (decodeTestTuple s.2.1 s.2.2.1 j)]) ≤ R) :=
    ((select_bounds cCount hSpace).id_prod (fun _ => Nat.succ_pos _)).comp_ofPolyTime
      (fun _ => Nat.succ_pos _) appendRow_polyTime
  let bOuter (L : ℕ) := 6 * L * L + 10 * L + 3
  have hbOuterP : PolyBounded (fun a => (encGreedyInput encC a).length)
      (fun a => bOuter (encGreedyInput encC a).length) :=
    .of_polynomiallyBounded _ (by dsimp only [bOuter]; fun_prop)
  have hbOuter : ∀ a : C × ℕ × ℕ × ℕ × List (List Bool), ∀ i ≤ roundCount a,
      (encInput encC ((outerStep count)^[i] (outerInit a))).length ≤
        bOuter (encGreedyInput encC a).length := by
    rintro ⟨c, n, m, P, rows₀⟩ i hi
    obtain ⟨hc_le, hn_le, hm_le, hP_le, hrows0_le⟩ := greedy_input_le (encC := encC) c n m P rows₀
    set L := (encGreedyInput encC (c, n, m, P, rows₀)).length
    dsimp only [roundCount, outerInit] at hi ⊢
    simp only [outerStep_iterate, encInput, encSelectBestIn, length_encPair,
      encUnary_apply, List.length_replicate, length_encList_greedyParityRowsAt]
    have hgrow : i * (2 * m + 1) ≤ (3 * L) * (2 * L + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hxp : (3 * L) * (2 * L + 1) = 6 * L * L + 3 * L := by ring
    dsimp only [bOuter]; omega
  refine AdditiveBounds.mono (c := greedyCertificate cCount) (AdditiveBounds.iterate
    (NativeCertificate.ofPolyTime (roundCount_polyTime (encC := encC)))
    (NativeCertificate.ofPolyTime (outerInit_polyTime (encC := encC)))
    (NativeCertificate.ofPolyTime_isPolynomial (roundCount_polyTime (encC := encC)))
    (NativeCertificate.ofPolyTime_isPolynomial (outerInit_polyTime (encC := encC)))
    hOuter (M := fun a => candidateTupleCount a.2.2.1 a.2.2.2.1 + 1)
    (fun _ => Nat.succ_pos _) hbOuterP
    (fun ⟨c, _, m, P, rows₀⟩ i _ => by simp only [outerInit, outerStep_iterate, le_rfl])
    hbOuter) (fun _ => le_rfl) fun ⟨c, n, m, P, rows₀⟩ R hR i hi => ?_
  simpa only [outerInit, outerStep_iterate] using hR i hi

/-- One uniform machine and polynomial for all encoded contexts, with independent native time
`O((3n + 1) ((2m)^P + 1) (poly(L) + R))` and workspace `O(poly(L))`, where `L` is the full
context/input encoding length. The binary clock, retained rows/context, incumbent count, and final
output are charged; workspace is not multiplied by either loop length.

The inclusive resource maxima require `hR` also at `i = 3n` and `j = (2m)^P`. These are resource
obligations on extra endpoint candidates, not extra calls in the executable program. In particular,
their row-length bound can exceed the correctness theorem's candidate bound by one. Polynomial
counter workspace is a separate, global joint-input assumption; counter time need not be polynomial.
This supplies the context interface for [OpenAI2026ETH], §6.3, not its common-zero counter. -/
theorem computableInO_greedy {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encContextRows encC) encNat)
    (hSpace : PolyBounded (fun r => (encContextRows encC r).length) cCount.space)
    (R : C × ℕ × ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a,
      let (c, n, m, P, rows) := a
      ∀ i ≤ 3 * n, ∀ j ≤ candidateTupleCount m P,
        cCount.time (c,
          greedyParityRowsAt (fun r => count (c, r)) m P rows i ++
            [materializeTestRow m (decodeTestTuple m P j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun ((c, n, m, P, rows) : C × ℕ × ℕ × ℕ × List (List Bool)) =>
          greedyParityRows (fun r => count (c, r)) n m P rows)
        (encGreedyInput encC) (encList encBits)
        (fun a =>
          let (_, n, m, P, _) := a
          (3 * n + 1) * (candidateTupleCount m P + 1) *
            (poly (encGreedyInput encC a).length + R a))
        (fun a => poly (encGreedyInput encC a).length) :=
  (greedy_bounds cCount hSpace).computableInO R hR

/-- Whenever `cCount` uses polynomial workspace, `greedyParityRows` runs in polynomial space. -/
theorem computableInPolySpace_greedy {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encContextRows encC) encNat)
    (hSpace : PolyBounded (fun r => (encContextRows encC r).length) cCount.space) :
    ComputableInPolySpace
      (fun ((c, n, m, P, rows) : C × ℕ × ℕ × ℕ × List (List Bool)) =>
        greedyParityRows (fun r => count (c, r)) n m P rows)
      (encGreedyInput encC) (encList encBits) :=
  let ⟨_, hP, hB⟩ := greedy_bounds cCount hSpace
  (greedyCertificate cCount).computableInPolySpace (hP.mono fun a => (hB a).1)

end Cslib.Logic.PL.CNF.GreedyContext

/-! ### Fixed counters as the unit context

A counter fixed before the runtime inputs is the case `C := Unit` of the context interface. The
fixed-counter bounds below transfer `GreedyContext.computableInO_select` and
`GreedyContext.computableInO_greedy` along the linear re-encoding `a ↦ ((), a)`. -/

namespace Cslib.Logic.PL.CNF

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM GreedyContext

/-- A fixed counter, read as a counter on `(Unit, rows)` after dropping the unit frame. -/
private noncomputable def unitCounter {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat) :
    NativeCertificate (fun p : Unit × List (List Bool) => countSys p.2)
      (encContextRows encUnit) encNat :=
  cCount.comp (NativeCertificate.linear (ComputableInO.snd encUnit (encList encBits)))

private theorem unitCounter_space {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space) :
    PolyBounded (fun p => (encContextRows encUnit p).length) (unitCounter cCount).space := by
  growth_poly

/-- Re-encode a fixed-counter input as a unit-context input. -/
private theorem unitInput {α : Type} (enc : α ↪ List Bool) :
    ComputableInO (fun a : α => ((), a)) enc (encPair encUnit enc)
      (fun a => (enc a).length + (enc a).length) (fun a => (enc a).length + (enc a).length) :=
  (ComputableInO.const ()).prod ComputableInO.id'

private theorem length_unitInput {α : Type} (enc : α ↪ List Bool) (a : α) :
    (encPair encUnit enc ((), a)).length = (enc a).length + 1 := by
  simp only [length_encPair, encUnit_apply, List.length_nil]; omega

/-- **Fixed-counter per-round `ComputableInO` time and polynomial-workspace bound for
`selectBestTestRow`** (with `countSys` and `cCount` fixed before runtime inputs `(m, P, rows)`). -/
theorem computableInO_selectBestTestRow {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space)
    (R : ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a : ℕ × ℕ × List (List Bool),
      let (m, P, rows) := a
      ∀ j ≤ candidateTupleCount m P,
        cCount.time (rows ++ [materializeTestRow m (decodeTestTuple m P j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun (m, P, rows) => selectBestTestRow countSys m P rows)
        encSelectBestIn encBits
        (fun a =>
          let (m, P, _) := a
          (candidateTupleCount m P + 1) * (poly (encSelectBestIn a).length + R a))
        (fun a => poly (encSelectBestIn a).length) := by
  obtain ⟨poly, hpoly, h⟩ := computableInO_select (unitCounter cCount)
    (unitCounter_space cCount hSpace) (fun a => R a.2 + (encInput encUnit a).length)
    fun ⟨_, m, P, rows⟩ j hj => by
      have := hR (m, P, rows) j hj
      dsimp only [unitCounter, NativeCertificate.comp_time, NativeCertificate.linear_time]
      enc_len [encContextRows, encInput, encSelectBestIn, encUnit_apply, encList_append,
        List.append_nil, length_materializeTestRow]
  refine ⟨fun L => poly (L + 1) + 3 * L + 1, by fun_prop, ?_⟩
  refine (h.comp' (unitInput encSelectBestIn)).mono_le (fun ⟨m, P, rows⟩ => ?_)
    fun ⟨m, P, rows⟩ => ?_
  all_goals
    dsimp only [encInput]
    rw [length_unitInput]
  · nlinarith [Nat.zero_le (candidateTupleCount m P * (encSelectBestIn (m, P, rows)).length)]
  · omega

/-- **Fixed-counter `3n`-round `ComputableInO` time and polynomial-workspace bound for
`greedyParityRows`.** For fixed `countSys` and `cCount` (supplied before runtime inputs
`(n, m, P, rows)`), runs in time `O((3 * n + 1) * ((2 * m) ^ P + 1) * (poly(|input|) + R))` and
polynomial workspace `O(poly(|input|))`, never storing `(2 * m) ^ P` lists or counts
([OpenAI2026ETH], §6.3, p. 43). -/
theorem computableInO_greedyParityRows {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space)
    (R : ℕ × ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a : ℕ × ℕ × ℕ × List (List Bool),
      let (n, m, P, rows) := a
      ∀ i ≤ 3 * n, ∀ j ≤ candidateTupleCount m P,
        cCount.time (greedyParityRowsAt countSys m P rows i ++
          [materializeTestRow m (decodeTestTuple m P j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun (n, m, P, rows) => greedyParityRows countSys n m P rows)
        encGreedyIn (encList encBits)
        (fun a =>
          let (n, m, P, _) := a
          (3 * n + 1) * (candidateTupleCount m P + 1) *
            (poly (encGreedyIn a).length + R a))
        (fun a => poly (encGreedyIn a).length) := by
  let E (L : ℕ) := 6 * L * L + 6 * L + 2
  obtain ⟨poly, hpoly, h⟩ := computableInO_greedy (unitCounter cCount)
    (unitCounter_space cCount hSpace) (fun a => R a.2 + E (encGreedyInput encUnit a).length)
    fun ⟨_, n, m, P, rows⟩ i hi j hj => by
      have := hR (n, m, P, rows) i hi j hj
      dsimp only at hi
      dsimp only [unitCounter, NativeCertificate.comp_time, NativeCertificate.linear_time, E]
      eta_reduce
      set L := (encGreedyInput encUnit ((), n, m, P, rows)).length
      have hL : n ≤ L ∧ m ≤ L ∧ (encList encBits rows).length ≤ L := by
        enc_len [L, encGreedyInput, encGreedyIn, encSelectBestIn]
      have hg : i * (2 * m + 1) ≤ 3 * L * (2 * L + 1) := Nat.mul_le_mul (by omega) (by omega)
      have hx : 3 * L * (2 * L + 1) = 6 * L * L + 3 * L := by ring
      enc_len [encContextRows, encUnit_apply, encList_append, List.append_nil,
        length_materializeTestRow, length_encList_greedyParityRowsAt]
  refine ⟨fun N => poly (N + 1) + E (N + 1) + 2 * N, by fun_prop, ?_⟩
  refine (h.comp' (unitInput encGreedyIn)).mono_le (fun ⟨n, m, P, rows⟩ => ?_)
    fun ⟨n, m, P, rows⟩ => ?_
  all_goals
    dsimp only [encGreedyInput]
    rw [length_unitInput]
  · have hM : 1 ≤ (3 * n + 1) * (candidateTupleCount m P + 1) := Nat.mul_pos (by omega) (by omega)
    generalize (3 * n + 1) * (candidateTupleCount m P + 1) = M at hM ⊢
    nlinarith [Nat.mul_le_mul_right (encGreedyIn (n, m, P, rows)).length hM]
  · omega

/-- For a fixed counter `(countSys, cCount)` using polynomial workspace, `greedyParityRows` runs in
polynomial space on runtime inputs `(n, m, P, rows)`. -/
theorem computableInPolySpace_greedyParityRows {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space) :
    ComputableInPolySpace
      (fun (n, m, P, rows) => greedyParityRows countSys n m P rows)
      encGreedyIn (encList encBits) := by
  obtain ⟨_, hP, hB⟩ := greedy_bounds (unitCounter cCount) (unitCounter_space cCount hSpace)
  have hu : PolyBounded (fun a => (encGreedyIn a).length)
      (fun a => (encGreedyInput encUnit ((), a)).length) :=
    (PolyBounded.self.add (.const 1)).mono fun a => (length_unitInput encGreedyIn a).le
  exact (((greedyCertificate (unitCounter cCount)).comp ⟨_, _, unitInput encGreedyIn⟩).congr
    fun ⟨_, _, _, _⟩ => rfl).computableInPolySpace
    (((PolyBounded.self.add .self).add (hP.comp hu)).mono fun a =>
      Nat.add_le_add_left (hB ((), a)).1 _)

end Cslib.Logic.PL.CNF

end
