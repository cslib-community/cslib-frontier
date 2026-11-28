/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo.UntilBad
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm

/-!
# Erasing writes at rejected random-oracle programming trials

Each trial samples fresh coins, writes its digest at a point determined by those coins, and
returns an optional response. A second oracle hides rejected writes. Adaptive direct hash
queries use the resulting table. If every trial address has point mass at most `δ`, the visible
laws for `T` trials and `H` direct queries differ by at most `T H δ`.

The hidden-point argument retains the original coins in the joint law. This permits rejection
to depend on both the point and digest, while charging only the unconditional guessing
probability of the point. This is an original game lemma for classical signing with aborts.
-/

public section

namespace Cslib.RandomOracle

open OracleComp Probability
open scoped ENNReal

variable {Q Key Ω S α : Type} {spec : Q → Type} {Coins : Q → Type}

private noncomputable def runJoint (dist : (q : Q) → PMF (Coins q))
    (step : (q : Q) → Coins q → S → spec q × S)
    (μ : PMF Ω) (init : Ω → S) (program : OracleComp spec α) : PMF (Ω × α) :=
  μ.bind fun x => ((interpret (m := StateT S PMF)
    (fun q st => (dist q).map fun r => step q r st) program).run (init x)).map (fun p => (x, p.1))

private theorem runJoint_query (dist : (q : Q) → PMF (Coins q))
    (step : (q : Q) → Coins q → S → spec q × S)
    (μ : PMF Ω) (init : Ω → S) (q : Q) (cont : spec q → OracleComp spec α) :
    runJoint dist step μ init (query q >>= cont) =
      (dist q).bind fun r => μ.bind fun x =>
        ((interpret (m := StateT S PMF) (fun q st => (dist q).map fun r => step q r st)
          (cont (step q r (init x)).1)).run (step q r (init x)).2).map (fun p => (x, p.1)) := by
  simp only [runJoint, interp_norm, PMF.monad_bind_eq_bind, PMF.map_bind]
  simp only [StateT.run, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm μ]

private theorem runJoint_perturb (dist : (q : Q) → PMF (Coins q))
    (step : (q : Q) → Coins q → S → spec q × S) (readAt : Q → Option Key)
    (R : Key → S → S → Prop) (hrefl : ∀ k s, R k s s)
    (hstep : ∀ k q r s t, readAt q ≠ some k → R k s t →
      (step q r s).1 = (step q r t).1 ∧ R k (step q r s).2 (step q r t).2)
    (μ : PMF Ω) (addr : Ω → Key) {δ : ℝ≥0∞} (hδ : ∀ k, (μ.map addr) k ≤ δ)
    {program : OracleComp spec α} {H : ℕ}
    (h : IsCostBounded (fun q => (readAt q).isSome.toNat) program H)
    (alt : Ω → S) (base : S) (hrel : ∀ x, R (addr x) (alt x) base) :
    CloseTo (runJoint dist step μ alt program) (runJoint dist step μ (fun _ => base) program)
      (H * δ) := by
  classical
  induction h generalizing alt base with
  | pure a n =>
    simp only [runJoint, interp_norm, PMF.monad_pure_eq_pure, PMF.pure_map]
    exact (CloseTo.refl _).mono zero_le
  | liftBind q cont n hcont ih =>
    rw [runJoint_query, runJoint_query]
    refine CloseTo.bind_right (dist q) fun r _ => ?_
    let bad : Set Ω := {x | readAt q = some (addr x)}
    let changeState := fun x => if x ∈ bad then (step q r base).2 else (step q r (alt x)).2
    have hrel' (x) : R (addr x) (changeState x) (step q r base).2 := by
      by_cases hx : x ∈ bad <;> simp only [changeState, hx, ↓reduceIte]
      · exact hrefl _ _
      · exact (hstep (addr x) q r _ _ hx (hrel x)).2
    refine (CloseTo.trans (ε := μ.toOuterMeasure bad) ?_
      (ih (step q r base).1 changeState (step q r base).2 hrel')).mono ?_
    · exact Interactive.CloseTo.bind_of_eq_on μ _ _ bad fun x _ hx => by
        simp only [changeState, hx, ↓reduceIte, (hstep (addr x) q r _ _ hx (hrel x)).1]
    · have hbad : μ.toOuterMeasure bad ≤ ((readAt q).isSome.toNat : ℕ) * δ := by
        cases he : readAt q with
        | none =>
          simp [bad, he]
        | some k =>
          have hb : bad = addr ⁻¹' {k} := Set.ext fun _ => by simp [bad, he, eq_comm]
          rw [hb, ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
          simpa using hδ k
      simpa only [Nat.cast_add, add_mul, add_comm] using add_le_add_right hbad (n * δ)


section
variable {Msg Value Out : Type} [BEq Key] [LawfulBEq Key]
private abbrev TrialSpec (Msg Key Value Out : Type) :=
  (fun _ : Msg => Option Out) ⊕ₒ (fun _ : Key => Value)

/-- A single trial draws its external coins, returns an optional reply and writes its digest
at its sampled point on success. The all-write mode also writes the digest on rejection.
Direct requests perform lazy lookup, using the supplied fresh digest on a miss. -/
@[expose] def programmedTrialStep (writeAborts : Bool) (point : Msg → Ω → Key)
    (digest : Ω → Value)
    (reply : Msg → Ω → Option Out) :
    (q : Msg ⊕ Key) → Ω → List (Key × Value) →
      ((fun _ : Msg => Option Out) ⊕ₒ (fun _ : Key => Value)) q × List (Key × Value)
  | .inl m, x, st => (reply m x, if writeAborts || (reply m x).isSome
      then (point m x, digest x) :: st else st)
  | .inr k, x, st => match st.lookup k with
    | some c => (c, st)
    | none => (digest x, (k, digest x) :: st)

private noncomputable def output (μ : PMF Ω) (step : (q : Q) → Ω → S → spec q × S)
    (program : OracleComp spec α) (s : S) :=
  ((interpret (m := StateT S PMF) (fun q st => μ.map fun r => step q r st) program).run s).map
    Prod.fst

private theorem output_query (μ : PMF Ω) (step : (q : Q) → Ω → S → spec q × S)
    (q : Q) (cont : spec q → OracleComp spec α) (s : S) :
    output μ step (query q >>= cont) s =
      μ.bind fun r => output μ step (cont (step q r s).1) (step q r s).2 := by
  simp only [output, interp_norm, PMF.monad_bind_eq_bind, PMF.map_bind]
  simp only [StateT.run, PMF.bind_map, Function.comp_def]

private def off (k : Key) (s t : List (Key × Value)) : Prop :=
  ∀ j, j ≠ k → s.lookup j = t.lookup j

omit [LawfulBEq Key] in
private theorem off_cons {k : Key} {s t : List (Key × Value)} (h : off k s t)
    (q : Key × Value) : off k (q :: s) (q :: t) := by
  rcases q with ⟨_, _⟩
  intro j hj
  simp only [List.lookup_cons, h j hj]

private theorem erase_here (μ : PMF Ω) (point : Msg → Ω → Key) (digest : Ω → Value)
    (reply : Msg → Ω → Option Out) (m : Msg) (cont : Option Out → OracleComp
      (TrialSpec Msg Key Value Out) α) (st : List (Key × Value))
    {H : ℕ} (hc : IsCostBounded (fun q => ((Sum.elim (fun _ => none) some q).isSome).toNat)
      (cont none) H) {δ : ℝ≥0∞} (hδ : ∀ k, (μ.map (point m)) k ≤ δ) :
    let sim := programmedTrialStep false point digest reply
    CloseTo
      (μ.bind fun x => output μ sim (cont (reply m x)) ((point m x, digest x) :: st))
      (μ.bind fun x => output μ sim (cont (reply m x))
        (if (reply m x).isSome then (point m x, digest x) :: st else st)) (H * δ) := by
  classical
  let sim := programmedTrialStep false point digest reply
  let readAt : Msg ⊕ Key → Option Key := Sum.elim (fun _ => none) some
  have hs (k q r s t) (h : readAt q ≠ some k) (ha : off k s t) :
      (sim q r s).1 = (sim q r t).1 ∧ off k (sim q r s).2 (sim q r t).2 := by
    cases q with
    | inl _ =>
      simp only [sim, programmedTrialStep, Bool.false_or, true_and]
      split <;> first | exact off_cons ha _ | exact ha
    | inr j =>
      simp only [sim, programmedTrialStep, ha j fun hj => h (hj ▸ rfl)]
      cases t.lookup j <;> simp only [true_and] <;> first | exact off_cons ha _ | exact ha
  have hd := runJoint_perturb (fun _ => μ) sim readAt off (fun _ _ _ _ => rfl) hs μ (point m)
    hδ hc (fun x => (point m x, digest x) :: st) st fun x j h => by
      simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr h]
  let after : Ω × α → PMF α := fun (x, a) => if (reply m x).isSome then
    output μ sim (cont (reply m x)) ((point m x, digest x) :: st) else PMF.pure a
  have hpost := hd.bind_left after
  have he (s : Ω → List (Key × Value)) :
      (runJoint (fun _ => μ) sim μ s (cont none)).bind after =
        μ.bind fun x => if (reply m x).isSome then
          output μ sim (cont (reply m x)) ((point m x, digest x) :: st)
        else output μ sim (cont none) (s x) := by
    simp only [runJoint, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    congr 1 with x : 1
    cases e : reply m x <;> simp [after, e, output, PMF.map, Function.comp_def]
  rw [he, he] at hpost
  convert hpost using 1 <;> congr 1 with x : 1 <;> cases reply m x <;> simp [sim]

/-- Erasing the writes of rejected trials changes the visible result of a program with at most
`T` trials and `H` direct reads by at most `T H δ`. Here `δ` bounds the largest atom of each
unconditioned trial address. Rejection can depend on the address and digest. Both executions
sample fresh coins at each operation, and share one table across all operations. -/
theorem closeTo_eraseRejectedTrialWrites (μ : PMF Ω) (point : Msg → Ω → Key) (digest : Ω → Value)
    (reply : Msg → Ω → Option Out)
    {program : OracleComp ((fun _ : Msg => Option Out) ⊕ₒ (fun _ : Key => Value)) α} {T H : ℕ}
    (hs : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program T)
    (hh : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program H)
    {δ : ℝ≥0∞} (hδ : ∀ m k, (μ.map (point m)) k ≤ δ) (st : List (Key × Value)) :
    CloseTo
      (((interpret (m := StateT (List (Key × Value)) PMF) (fun q s =>
        μ.map fun x => programmedTrialStep true point digest reply q x s) program).run st).map
        Prod.fst)
      (((interpret (m := StateT (List (Key × Value)) PMF) (fun q s =>
        μ.map fun x => programmedTrialStep false point digest reply q x s) program).run st).map
        Prod.fst)
      (T * (H * δ)) := by
  change CloseTo (output μ (programmedTrialStep true point digest reply) program st)
    (output μ (programmedTrialStep false point digest reply) program st) _
  classical
  induction hs generalizing st with
  | pure a n =>
    simp only [output, interp_norm, PMF.monad_pure_eq_pure, PMF.pure_map]
    exact (CloseTo.refl _).mono zero_le
  | liftBind q cont n _ ih =>
    have ht (a) := ((IsCostBounded.liftBind_iff.mp hh).2 a).mono (Nat.sub_le _ _)
    rw [output_query, output_query]
    have ha := CloseTo.bind_right μ fun r _ =>
      ih (programmedTrialStep true point digest reply q r st).1
        (ht _) (programmedTrialStep true point digest reply q r st).2
    cases q with
    | inr k => simpa only [programmedTrialStep, Sum.elim_inr, Nat.add_zero] using ha
    | inl m =>
      have hc := (ht none).of_le (cost' := fun q =>
        ((Sum.elim (fun _ => none) some q).isSome).toNat) (fun q => by cases q <;> exact le_rfl)
      have he := erase_here μ point digest reply m cont st hc (hδ m)
      simpa only [programmedTrialStep, Bool.true_or, Bool.false_or, ↓reduceIte, Sum.elim_inl,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ha.trans he

end
end Cslib.RandomOracle
