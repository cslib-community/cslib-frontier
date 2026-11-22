/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.Choice
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.Simulation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Simulating a choice run with universal steps

For a nondeterministic oracle machine `M`, the state `(xs, cur, s, o)` holds the input as numbers
`xs`, the remaining choices `cur`, a universal configuration with the query tape `s`, and a summary
`o` of the output (empty, exactly `[true]`, or other). A step (`OracleNTM.istep`) takes a step of
the simulation (`OracleTM.simNextX`, the step of
`Cslib.Complexity.NtimeDspace.Oracle.OracleTM.simNext` with the
input read from `xs`) of the choice machine `choiceTM (cur mod B)`, and continues with `cur / B`.
It follows the choice run of `M` (`OracleNTM.istep_rel`), and its states have size linear in the
input, the choice number and the number of steps (`OracleNTM.length_encZ_le`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### The step with the input in the state -/

namespace OracleTM

variable {k : ℕ} {State : Type} [Fintype State] (D : OracleTM k State) (eS : State ↪ ℕ)
  (A : Set (List Bool))

open scoped Classical in
/-- The step of the simulation, reading the input symbol from the numbered input `xs`. -/
noncomputable def simNextX (xs : List ℕ) (p : SCfg × List Bool) : SCfg × List Bool :=
  if (Universal.step (desc eS eBit (D.outTM flagSym)) xs p.1).2.isSome then
    (if p.2 ∈ A then (Universal.step (desc eS eBit (D.answerTM true)) xs p.1).1
      else (Universal.step (desc eS eBit (D.answerTM false)) xs p.1).1, [])
  else ((Universal.step (desc eS eBit D.plainTM) xs p.1).1,
    p.2 ++ bitOf (Universal.step (desc eS eBit (D.outTM (querySym true))) xs p.1).2.isSome
      (Universal.step (desc eS eBit (D.outTM (querySym false))) xs p.1).2.isSome)

/-- Whether the step queries, and the flags of the symbol it writes on the output tape. -/
noncomputable def emitFlags (xs : List ℕ) (p : SCfg × List Bool) : Bool × Bool × Bool :=
  ((Universal.step (desc eS eBit (D.outTM flagSym)) xs p.1).2.isSome,
    (Universal.step (desc eS eBit (D.outTM (outSym true))) xs p.1).2.isSome,
    (Universal.step (desc eS eBit (D.outTM (outSym false))) xs p.1).2.isSome)

omit [Fintype State] in
lemma symOf_eq (x : List Bool) (s : SCfg) :
    symOf s (x[s.inputPos - 1]?) = inputSymbol (x.map eBit) s.inputPos := by
  rw [symOf, inputSymbol_map_eBit]

lemma simNextX_eq (x : List Bool) (p : SCfg × List Bool) :
    D.simNextX eS A (x.map eBit) p = D.simNext eS A (p, x[p.1.inputPos - 1]?) := by
  simp only [simNextX, simNext, step_eq_stepWith, symOf_eq]

lemma simEmit_eq (x : List Bool) (p : SCfg × List Bool) :
    D.simEmit eS (p, x[p.1.inputPos - 1]?) =
      if (D.emitFlags eS (x.map eBit) p).1 then []
      else bitOf (D.emitFlags eS (x.map eBit) p).2.1 (D.emitFlags eS (x.map eBit) p).2.2 := by
  simp only [simEmit, emitFlags, step_eq_stepWith, symOf_eq]

lemma simNextX_fst (xs : List ℕ) (p : SCfg × List Bool) : ∃ tm : MultiTapeTM k Bool State,
    (D.simNextX eS A xs p).1 = (Universal.step (desc eS eBit tm) xs p.1).1 := by
  unfold simNextX
  split_ifs <;> exact ⟨_, rfl⟩

lemma length_simNextX_snd (xs : List ℕ) (p : SCfg × List Bool) :
    (D.simNextX eS A xs p).2.length ≤ p.2.length + 1 := by
  unfold simNextX
  split_ifs
  · simp
  · simp
  · simp only [List.length_append, bitOf]
    split_ifs <;> simp

end OracleTM

/-! ### Output summaries -/

/-- A summary of an output: empty, exactly `[true]`, or other. -/
def summ (l : List Bool) : Fin 3 := if l = [] then 0 else if l = [true] then 1 else 2

/-- The summary after a step with flags `f`. -/
def supd (o : Fin 3) (f : Bool × Bool × Bool) : Fin 3 :=
  if f.1 then o else if f.2.1 then (if o = 0 then 1 else 2) else if f.2.2 then 2 else o

lemma summ_append (l : List Bool) (f : Bool × Bool × Bool) :
    summ (l ++ if f.1 then [] else OracleTM.bitOf f.2.1 f.2.2) = supd (summ l) f := by
  rcases f with ⟨_ | _, _ | _, _ | _⟩ <;>
    rcases l with _ | ⟨_ | _, _ | ⟨_, _⟩⟩ <;> simp [summ, supd, OracleTM.bitOf]

lemma summ_eq_one {l : List Bool} : summ l = 1 ↔ l = [true] := by
  unfold summ
  split_ifs with h1 h2 <;> simp_all

/-! ### Universal steps of descriptions of binary machines -/

section Shape

variable {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)

lemma head_apply_le (t : Universal.Tape) (a : TapeAct) :
    ((t.apply a).head - t.head).natAbs ≤ 1 := by
  obtain ⟨w, m⟩ := a
  have hw : (w.elim t t.write).head = t.head := by cases w <;> rfl
  simp only [Universal.Tape.apply]
  rcases m with _ | _ | _ <;> simp [Universal.Tape.move, hw]

/-- The shape of a universal step of the description of a binary machine: the work tapes take
actions writing bits, the input head stays within the input and its boundaries, and the new state,
if any, is a numbered state. -/
lemma stepWith_desc_shape (tm : MultiTapeTM k Bool State) (s : SCfg) (xs : List ℕ)
    (hpos : s.inputPos ≤ xs.length + 1) :
    (∃ as : List TapeAct, (∀ a ∈ as, ∀ o, a.1 = some o → o.getD 0 ≤ 1) ∧
      (stepWith (desc eS eBit tm) s (inputSymbol xs s.inputPos)).1.workTapes =
        applyTapes s.workTapes as) ∧
    (stepWith (desc eS eBit tm) s (inputSymbol xs s.inputPos)).1.inputPos ≤ xs.length + 1 ∧
    ((∀ n, s.state = some n → ∃ q, n = eS q) →
      ∀ n, (stepWith (desc eS eBit tm) s (inputSymbol xs s.inputPos)).1.state = some n →
        ∃ q, n = eS q) := by
  refine ⟨stepWith_desc_tapes eS tm s _, ?_, ?_⟩
  · obtain ⟨_ | q, ip, ts⟩ := s
    · exact hpos
    · simp only [stepWith]
      split
      · exact hpos
      · exact moveInput_le hpos _
  · intro hs n hn
    obtain ⟨_ | q, ip, ts⟩ := s
    · exact hs n hn
    · simp only [stepWith] at hn
      split at hn
      · cases hn
      · next e he =>
        obtain ⟨⟨q', i', w'⟩, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some he)
        simp only [Act.ofAction, Action.map_state, Option.map_eq_some_iff] at hn
        obtain ⟨q'', -, rfl⟩ := hn
        exact ⟨q'', rfl⟩

end Shape

/-! ### The choice run, simulated -/

namespace OracleNTM

variable {k : ℕ} {State : Type} [Fintype State] (M : OracleNTM k State) (eS : State ↪ ℕ)
  (A : Set (List Bool))

/-- The states of the simulated choice run. -/
abbrev Z := List ℕ × ℕ × (SCfg × List Bool) × Fin 3

/-- A step of the simulated choice run. -/
noncomputable def istep (z : Z) : Z :=
  if z.2.2.1.1.state.isNone then z else
    (z.1, z.2.1 / nActs (k := k) (State := State),
      (M.choiceTM (z.2.1 % nActs (k := k) (State := State))).simNextX eS A z.1 z.2.2.1,
      supd z.2.2.2
        ((M.choiceTM (z.2.1 % nActs (k := k) (State := State))).emitFlags eS z.1 z.2.2.1))

/-- The initial universal configuration. -/
noncomputable def sInit : SCfg := init (desc eS eBit (M.choiceTM 0).plainTM)

/-- The initial state of the simulated choice run for the choice number `r`. -/
noncomputable def z0 (xs : List ℕ) (r : ℕ) : Z := (xs, r, (M.sInit eS, []), 0)

variable {M eS A}

lemma rel_sInit (x : List Bool) : OracleTM.Rel eS (M.sInit eS, []) (M.initCfg x) := by
  have h := toCfg_init (k := k) (d := desc eS eBit (M.choiceTM 0).plainTM) (x := x.map eBit) rfl
  refine ⟨h.2, ?_, rfl⟩
  change (init (desc eS eBit (M.choiceTM 0).plainTM)).toCfg k (x.map eBit) [] =
    (Cfg.init M.q₀ x).map eS eBit
  rw [h.1, Cfg.map_init]
  rfl

/-- **The simulated choice run follows the choice run.** -/
theorem istep_rel (x : List Bool) (r j : ℕ) :
    OracleTM.Rel eS ((M.istep eS A)^[j] (M.z0 eS (x.map eBit) r)).2.2.1
        ((M.cstep A)^[j] (r, M.initCfg x)).2 ∧
      ((M.istep eS A)^[j] (M.z0 eS (x.map eBit) r)).2.1 = ((M.cstep A)^[j] (r, M.initCfg x)).1 ∧
      ((M.istep eS A)^[j] (M.z0 eS (x.map eBit) r)).1 = x.map eBit ∧
      ((M.istep eS A)^[j] (M.z0 eS (x.map eBit) r)).2.2.2 =
        summ ((M.cstep A)^[j] (r, M.initCfg x)).2.tapes.output := by
  induction j with
  | zero => exact ⟨rel_sInit x, rfl, rfl, rfl⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    generalize (M.istep eS A)^[j] (M.z0 eS (x.map eBit) r) = z at ih ⊢
    generalize (M.cstep A)^[j] (r, M.initCfg x) = p at ih ⊢
    obtain ⟨hrel, hcur, hxs, hsum⟩ := ih
    cases hq : p.2.tapes.state with
    | none =>
      have hz : z.2.2.1.1.state.isNone = true := by rw [hrel.state, hq]; rfl
      rw [cstep_halted hq]
      simp only [istep, hz, ite_true]
      exact ⟨hrel, hcur, hxs, hsum⟩
    | some q =>
      have hz : z.2.2.1.1.state.isNone = false := by rw [hrel.state, hq]; rfl
      simp only [istep, hz, Bool.false_eq_true, ite_false, cstep, hq, reduceCtorEq]
      rw [hcur, hxs]
      set D := M.choiceTM (p.1 % nActs (k := k) (State := State))
      have hrel' := hrel
      obtain ⟨h1, h2⟩ := OracleTM.rel_simNext (M := D) (A := A) hrel hq
      refine ⟨?_, rfl, rfl, ?_⟩
      · rw [OracleTM.simNextX_eq]; exact h1
      · rw [List.append_nil, OracleTM.simEmit_eq] at h2
        rw [← (List.prefix_iff_eq_append.mp (OracleTM.output_step_prefix (M := D) (A := A) p.2)),
          ← h2, summ_append, hsum]

/-! ### The size of the states -/

/-- The encoding of the states of the simulated choice run. -/
noncomputable abbrev encZ : Z ↪ List Bool :=
  encPair (encList encUnary) (encPair encNat (encPair encSim (encFinite (Fin 3))))

/-- The window of positions within `j` of the origin. -/
def win (j : ℕ) : Finset ℤ := Finset.Icc (-(j : ℤ)) j

lemma card_win (j : ℕ) : (win j).card = 2 * j + 1 := by
  simp only [win, Int.card_Icc]
  omega

lemma win_mono {i j : ℕ} (h : i ≤ j) : win i ⊆ win j := by
  intro z hz
  simp only [win, Finset.mem_Icc] at hz ⊢
  omega

/-- The invariants of the simulated choice run, for any numbered input. -/
theorem istep_shape (xs : List ℕ) (r j : ℕ) :
    ((M.istep eS A)^[j] (M.z0 eS xs r)).1 = xs ∧ ((M.istep eS A)^[j] (M.z0 eS xs r)).2.1 ≤ r ∧
      ((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.1.workTapes.length = k ∧
      ((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.1.inputPos ≤ xs.length + 1 ∧
      (∀ n, ((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.1.state = some n → ∃ q, n = eS q) ∧
      ((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.2.length ≤ j ∧
      ∀ i : Fin k,
        TapeCovered (((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.1.workTapes.getD i
          Universal.Tape.blank) (win j) ∧
        TapeBits (((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.1.workTapes.getD i
          Universal.Tape.blank) ∧
        (((M.istep eS A)^[j] (M.z0 eS xs r)).2.2.1.1.workTapes.getD i
          Universal.Tape.blank).head.natAbs ≤ j := by
  induction j with
  | zero =>
    refine
        ⟨rfl, le_rfl, by simp [z0, sInit, init, desc], by simp [z0, sInit, init], ?_, by simp [z0],
      fun i => ?_⟩
    · intro n hn
      have hs : (M.sInit eS).state = some (eS M.q₀) := rfl
      simp only [Function.iterate_zero, id_eq, z0, hs, Option.some.injEq] at hn
      exact ⟨M.q₀, hn.symm⟩
    · have : ((M.istep eS A)^[0] (M.z0 eS xs r)).2.2.1.1.workTapes.getD i Universal.Tape.blank =
          Universal.Tape.blank := by
        simp [z0, sInit, init, desc, List.getD_eq_getElem?_getD, Universal.Tape.blank]
      rw [this]
      exact ⟨TapeCovered.blank _, tapeBits_blank, by simp [Universal.Tape.blank]⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    generalize (M.istep eS A)^[j] (M.z0 eS xs r) = z at ih ⊢
    obtain ⟨hxs, hcur, hlen, hpos, hst, hbuf, htapes⟩ := ih
    unfold istep
    split_ifs with hh
    · exact ⟨hxs, hcur, hlen, hpos, hst, by omega, fun i => ⟨(htapes i).1.mono
        (by exact_mod_cast win_mono (Nat.le_succ j)),
            (htapes i).2.1, by have := (htapes i).2.2; omega⟩⟩
    · set D := M.choiceTM (z.2.1 % nActs (k := k) (State := State))
      obtain ⟨tm, htm⟩ := D.simNextX_fst eS A z.1 z.2.2.1
      have hshape := stepWith_desc_shape eS tm z.2.2.1.1 z.1 (hxs ▸ hpos)
      rw [step_eq_stepWith] at htm
      obtain ⟨⟨as, has, hws⟩, hpos', hst'⟩ := hshape
      refine ⟨hxs, (Nat.div_le_self _ _).trans hcur, ?_, ?_, ?_, ?_, fun i => ?_⟩
      · rw [htm, hws, length_applyTapes', hlen]
      · rw [htm, ← hxs]; exact hpos'
      · rw [htm]; exact hst' hst
      · have := D.length_simNextX_snd eS A z.1 z.2.2.1
        change (D.simNextX eS A z.1 z.2.2.1).2.length ≤ j + 1
        omega
      · have hi : (i : ℕ) < z.2.2.1.1.workTapes.length := by rw [hlen]; exact i.isLt
        rw [htm, hws, getD_applyTapes' _ _ hi]
        obtain ⟨hc, hb, hh'⟩ := htapes i
        have hmv := head_apply_le (z.2.2.1.1.workTapes.getD i Universal.Tape.blank)
          (as.getD i (none, 0))
        refine ⟨(hc.mono (by exact_mod_cast win_mono (Nat.le_succ j))).apply ?_ _ ?_,
          hb.apply _ (OracleTM.getD_bits as has i), by omega⟩
        · simp only [win, Finset.coe_Icc, Set.mem_Icc]; omega
        · simp only [win, Finset.coe_Icc, Set.mem_Icc]; omega

lemma length_le_encList {α : Type} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList enc l).length := by
  induction l with
  | nil => simp
  | cons a l ih => rw [encList_cons, List.length_append, length_frame]; simp; omega

/-- **The size of the states of the simulated choice run**: linear in the numbered input, the
choice number and the number of steps. -/
theorem length_encZ_le (xs : List ℕ) (r j : ℕ) :
    (encZ ((M.istep eS A)^[j] (M.z0 eS xs r))).length ≤
      (400 * k + 10 * OracleTM.stateBound eS + 100) *
        ((encList encUnary xs).length + (encNat r).length + j + 1) := by
  obtain ⟨hxs, hcur, hlen, hpos, hst, hbuf, htapes⟩ := istep_shape (M := M) (eS := eS) (A := A)
    xs r j
  generalize (M.istep eS A)^[j] (M.z0 eS xs r) = z at *
  obtain ⟨xs', cur, ⟨s, buf⟩, o⟩ := z
  simp only at hxs hcur hlen hpos hst hbuf htapes
  subst xs'
  have hcfg := length_eCfg_le s (fun _ => win j) hlen (fun i => (htapes i).1)
    (fun i => by rw [card_win]; have := (htapes i).2.2; omega) (fun i => (htapes i).2.1)
  simp only [card_win, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hcfg
  have hstb : (eSym s.state).length ≤ OracleTM.stateBound eS := by
    cases hs : s.state with
    | none => simp
    | some n =>
      obtain ⟨q, rfl⟩ := hst n hs
      exact OracleTM.length_eSym_le (eS := eS) (some q)
  have hp : (encNat s.inputPos).length ≤ xs.length + 1 :=
    (Universal.length_encNat_le _).trans hpos
  have hxl := length_le_encList encUnary xs
  have hc : (encNat cur).length ≤ (encNat r).length := length_encNat_mono hcur
  have hf : (encFinite (Fin 3) o).length < 3 := by
    have := length_encFinite_lt o; simpa using this
  simp only [encZ, encSim, length_encPair, encBits_apply]
  generalize (encList encUnary xs).length = L at *
  generalize (encNat r).length = R at *
  generalize OracleTM.stateBound eS = D at *
  have e : (400 * k + 10 * D + 100) * (L + R + j + 1) =
      400 * (k * (L + R + j + 1)) + 10 * (D * (L + R + j + 1)) + 100 * (L + R + j + 1) := by ring
  have h1 : k * (j + 1) ≤ k * (L + R + j + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : D ≤ D * (L + R + j + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : k * (2 * j + 1) ≤ 2 * (k * (j + 1)) := by nlinarith
  have h4 : k ≤ k * (j + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

end OracleNTM

end Cslib.Complexity.NtimeDspace.Oracle
