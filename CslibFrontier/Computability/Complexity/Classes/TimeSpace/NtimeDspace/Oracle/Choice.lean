/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.Machine
import Mathlib.Data.List.GetD

/-!
# Nondeterministic oracle machines as deterministic machines with choices

A nondeterministic oracle machine with finitely many states has finitely many instructions; list
them (`OracleNTM.acts`, `B` of them). For `c < B`, the deterministic machine `choiceTM c` takes the
`c`-th instruction when it is permitted, and otherwise halts after appending `false` to the output
(so it does not accept). A number `r` gives a sequence of choices by its digits in base `B`: the
*choice run* (`OracleNTM.cstep`) takes, at each running step, the choice `r mod B` and continues
with `r / B`.

Under a time bound `T`, the machine accepts `x` exactly when some `r < B^T` leads the choice run to
a halted configuration with output `[true]` after `T` steps (`accepts_iff_exists_choice`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing

variable {k : ℕ} {State : Type}

/-! ### Finitely many instructions -/

/-- The fields of an action. -/
def actionCode (a : Turing.Action k Bool State) :
    SignType × (Fin k → Option (Option Bool) × SignType) × Option Bool × Option State :=
  (a.inputTape, a.workTapes, a.output, a.state)

lemma actionCode_injective : Function.Injective (actionCode (k := k) (State := State)) := by
  rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
  simp only [actionCode, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The fields of an instruction. -/
def oactionCode : OAction k State → (Turing.Action k Bool State × Option Bool) ⊕ (State × State)
  | .step a s => .inl (a, s)
  | .ask y n => .inr (y, n)

lemma oactionCode_injective : Function.Injective (oactionCode (k := k) (State := State)) := by
  rintro (⟨a, s⟩ | ⟨y, n⟩) (⟨a', s'⟩ | ⟨y', n'⟩) h <;> simp_all [oactionCode]

instance [Finite State] : Finite (Turing.Action k Bool State) :=
  Finite.of_injective _ actionCode_injective

instance [Finite State] : Finite (OAction k State) :=
  Finite.of_injective _ oactionCode_injective

/-- The rejecting instruction: halt after appending `false` to the output. -/
def rejectAct : OAction k State := .step ⟨0, fun _ => (none, 0), some false, none⟩ none

namespace OracleNTM

variable [Finite State] (M : OracleNTM k State) (A : Set (List Bool))

/-- All instructions, in a fixed order. -/
noncomputable def acts : List (OAction k State) :=
  (@Finset.univ _ (Fintype.ofFinite (OAction k State))).toList

lemma mem_acts (a : OAction k State) : a ∈ (acts : List (OAction k State)) :=
  @Finset.mem_toList _ a (@Finset.univ _ (Fintype.ofFinite _)) |>.mpr
    (@Finset.mem_univ _ (Fintype.ofFinite _) a)

/-- The number of instructions. -/
noncomputable def nActs : ℕ := (acts : List (OAction k State)).length

lemma two_le_nActs : 2 ≤ nActs (k := k) (State := State) := by
  classical
  have h1 := mem_acts (k := k) (State := State) rejectAct
  have h2 := mem_acts (k := k) (State := State) (.step ⟨0, fun _ => (none, 0), none, none⟩ none)
  have hne : (rejectAct : OAction k State) ≠ .step ⟨0, fun _ => (none, 0), none, none⟩ none := by
    simp [rejectAct]
  unfold nActs
  by_contra h
  push Not at h
  rcases hl : (acts : List (OAction k State)) with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp [hl] at h1
  · simp only [hl, List.mem_singleton] at h1 h2
    exact hne (h1.trans h2.symm)
  · simp [hl] at h

open scoped Classical in
/-- The deterministic machine taking the `c`-th instruction when permitted, and rejecting
otherwise. -/
noncomputable def choiceTM (c : ℕ) : OracleTM k State where
  q₀ := M.q₀
  tr q i w := if M.Tr q i w ((acts : List (OAction k State)).getD c rejectAct) then
    (acts : List (OAction k State)).getD c rejectAct else rejectAct

variable {x : List Bool}

open scoped Classical in
/-- A step of the choice run: a running configuration takes the choice `r mod B` and continues
with `r / B`; a halted configuration stays. -/
noncomputable def cstep (p : ℕ × OCfg k State x) : ℕ × OCfg k State x :=
  if p.2.tapes.state = none then p else
    (p.1 / nActs (k := k) (State := State),
        (M.choiceTM (p.1 % nActs (k := k) (State := State))).step A p.2)

variable {M A}

omit [Finite State] in
lemma step_halted_eq {c c' : OCfg k State x} (hc : c.tapes.state = none) (h : M.Step A c c') :
    c' = c := by
  unfold Step at h
  rw [hc] at h
  exact h

omit [Finite State] in
/-- A run path stays at a halted configuration. -/
lemma runPath_eq_of_halted (p : M.RunPath A x) {i : ℕ} (hi : i < p.length + 1)
    (hh : (p ⟨i, hi⟩).tapes.state = none) :
    ∀ m (hm : i + m < p.length + 1), p ⟨i + m, hm⟩ = p ⟨i, hi⟩ := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hs := p.step ⟨i + m, by omega⟩
    change M.Step A _ _ at hs
    have := ih (by omega)
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hs
    rw [this] at hs
    rw [show (⟨i + (m + 1), hm⟩ : Fin (p.length + 1)) = ⟨i + m + 1, by omega⟩ from Fin.ext rfl,
      step_halted_eq hh hs]

lemma cstep_halted {p : ℕ × OCfg k State x} (h : p.2.tapes.state = none) : M.cstep A p = p := by
  simp [cstep, h]

lemma cstep_iterate_halted {p : ℕ × OCfg k State x} (h : p.2.tapes.state = none) (m : ℕ) :
    (M.cstep A)^[m] p = p := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, cstep_halted h]

/-- **Soundness of choices.** A choice run ending halted with output `[true]` follows a computation
path. -/
lemma accepts_of_choice {r T : ℕ}
    (hT : ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.state = none)
    (ho : ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.output = [true]) : M.Accepts A x := by
  classical
  have key : ∀ j, (∃ p : M.ComputationPath A x, p.last = ((M.cstep A)^[j] (r, M.initCfg x)).2) ∨
      (((M.cstep A)^[j] (r, M.initCfg x)).2.tapes.state = none ∧
        ((M.cstep A)^[j] (r, M.initCfg x)).2.tapes.output.getLast? = some false) := by
    intro j
    induction j with
    | zero => exact .inl ⟨ComputationPath.init (M := M) (A := A) x, rfl⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      generalize (M.cstep A)^[j] (r, M.initCfg x) = p at ih ⊢
      by_cases hh : p.2.tapes.state = none
      · rw [cstep_halted hh]; exact ih
      · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hh
        rcases ih with ⟨pa, hpa⟩ | ⟨h, -⟩
        · simp only [cstep, hh, ite_false]
          rw [OracleTM.step_of_state _ _ hq]
          simp only [choiceTM]
          split_ifs with htr
          · left
            have hstep : (pa.last, ((acts : List (OAction k State)).getD
                (p.1 % nActs (k := k) (State := State)) rejectAct).apply A p.2) ∈
                M.stepRel A x := by
              change M.Step A pa.last _
              rw [hpa]
              unfold Step
              rw [hq]
              exact ⟨_, htr, rfl⟩
            exact ⟨⟨pa.toRunPath.snoc _ hstep, by rw [RelSeries.head_snoc]; exact pa.head_eq⟩,
              RelSeries.last_snoc _ _ hstep⟩
          · right
            simp [rejectAct, OAction.apply]
        · exact absurd h hh
  rcases key T with ⟨p, hp⟩ | ⟨-, h⟩
  · exact ⟨p, hp ▸ hT, hp ▸ ho⟩
  · rw [ho] at h
    cases h

/-- **Completeness of choices.** Under a time bound `T`, an accepting computation is the choice run
of some `r < B^T`. -/
lemma exists_choice_of_accepts {T : ℕ} (hT : M.RunsInTime A x T) (h : M.Accepts A x) :
    ∃ r < nActs (k := k) (State := State) ^ T,
      ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.state = none ∧
      ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.output = [true] := by
  classical
  obtain ⟨p, hph, hpo⟩ := h
  -- an accepting path of length at most `T`
  obtain ⟨q, hqT, hql⟩ : ∃ q : M.ComputationPath A x, q.length ≤ T ∧ q.last = p.last := by
    rcases le_or_gt p.length T with hle | hlt
    · exact ⟨p, hle, rfl⟩
    · let q : M.ComputationPath A x :=
        ⟨p.toRunPath.take ⟨T, by omega⟩, by simpa [RelSeries.head_take] using p.head_eq⟩
      have hqh : q.last.tapes.state = none := hT q (by simp [q])
      refine ⟨q, by simp [q], ?_⟩
      have hqlast : q.last = p.toRunPath ⟨T, by omega⟩ := by simp [q, RelSeries.last_take]
      rw [hqlast] at hqh ⊢
      have := runPath_eq_of_halted p.toRunPath (by omega) hqh (p.length - T) (by omega)
      rw [← this]
      simp only [show T + (p.length - T) = p.length by omega]
      rfl
  -- the choices along `q`
  have hact : ∀ j : Fin q.length, ∃ d : ℕ, d < nActs (k := k) (State := State) ∧
      (∀ st, (q.toRunPath j.castSucc).tapes.state = some st →
        M.Tr st (q.toRunPath j.castSucc).tapes.inputSymbol
          (q.toRunPath j.castSucc).tapes.workTapeSymbols
          ((acts : List (OAction k State)).getD d rejectAct) ∧
        q.toRunPath j.succ = ((acts : List (OAction k State)).getD d rejectAct).apply A
          (q.toRunPath j.castSucc)) := by
    intro j
    have hs := q.step j
    change M.Step A _ _ at hs
    cases hst : (q.toRunPath j.castSucc).tapes.state with
    | none => exact ⟨0, by have := two_le_nActs (k := k) (State := State); omega,
        fun st h => by cases h⟩
    | some st =>
      unfold Step at hs
      rw [hst] at hs
      obtain ⟨a, ha, he⟩ := hs
      have hmem := mem_acts a
      refine ⟨(acts : List (OAction k State)).idxOf a, List.idxOf_lt_length_iff.mpr hmem,
        fun st' hst' => ?_⟩
      cases hst'
      rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hmem), List.getElem_idxOf]
      exact ⟨ha, he⟩
  choose d hdB hd using hact
  set B := nActs (k := k) (State := State) with hBdef
  set ds : List ℕ := List.ofFn d with hds
  have hdsB : ∀ y ∈ ds, y < B := by
    intro y hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact hdB j
  have hB : 2 ≤ B := two_le_nActs
  refine ⟨Nat.ofDigits B ds, ?_, ?_⟩
  · calc Nat.ofDigits B ds < B ^ ds.length := Nat.ofDigits_lt_base_pow_length hB hdsB
      _ ≤ B ^ T := Nat.pow_le_pow_right (by omega) (by simp [hds]; exact hqT)
  -- the choice run follows `q`
  have hrun : ∀ j (hj : j ≤ q.length),
      ((M.cstep A)^[j] (Nat.ofDigits B ds, M.initCfg x)).2 = q.toRunPath ⟨j, by omega⟩ ∧
      ((q.toRunPath ⟨j, by omega⟩).tapes.state ≠ none →
        ((M.cstep A)^[j] (Nat.ofDigits B ds, M.initCfg x)).1 =
          Nat.ofDigits B (ds.drop j)) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨q.head_eq.symm, fun _ => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      by_cases hh : (q.toRunPath ⟨j, by omega⟩).tapes.state = none
      · have hq' := runPath_eq_of_halted q.toRunPath (by omega) hh 1 (by omega)
        rw [cstep_halted (by rw [ih1]; exact hh), ih1]
        refine ⟨hq'.symm, fun h => absurd (hq' ▸ hh) h⟩
      · obtain ⟨st, hst⟩ := Option.ne_none_iff_exists'.mp hh
        have hdj := hd ⟨j, by omega⟩ st (by simpa using hst)
        simp only [Fin.castSucc_mk, Fin.succ_mk] at hdj
        have hdrop : ds.drop j = d ⟨j, by omega⟩ :: ds.drop (j + 1) := by
          rw [List.drop_eq_getElem_cons (by simp [hds]; omega)]
          simp [hds]
        have hcur := ih2 hh
        rw [hdrop, Nat.ofDigits_cons] at hcur
        have hlt := hdB ⟨j, by omega⟩
        have hmod : ((M.cstep A)^[j] (Nat.ofDigits B ds, M.initCfg x)).1 % B =
            d ⟨j, by omega⟩ := by
          rw [hcur, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        have hdiv : ((M.cstep A)^[j] (Nat.ofDigits B ds, M.initCfg x)).1 / B =
            Nat.ofDigits B (ds.drop (j + 1)) := by
          rw [hcur, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
        simp only [cstep, ih1, hh, ite_false]
        rw [← hBdef, hmod, hdiv]
        refine ⟨?_, fun _ => rfl⟩
        rw [OracleTM.step_of_state _ _ hst]
        simp only [choiceTM, hdj.1, ite_true]
        exact hdj.2.symm
  obtain ⟨h1, -⟩ := hrun q.length le_rfl
  have hlast : q.toRunPath ⟨q.length, by omega⟩ = q.last := rfl
  rw [hlast, hql] at h1
  have hfix : (M.cstep A)^[T] (Nat.ofDigits B ds, M.initCfg x) =
      (M.cstep A)^[q.length] (Nat.ofDigits B ds, M.initCfg x) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hqT
    rw [hm, Nat.add_comm, Function.iterate_add_apply,
      cstep_iterate_halted (by rw [h1]; exact hph)]
  rw [hfix, h1]
  exact ⟨hph, hpo⟩

/-- **Acceptance as a search over choices.** -/
theorem accepts_iff_exists_choice {T : ℕ} (hT : M.RunsInTime A x T) :
    M.Accepts A x ↔ ∃ r < nActs (k := k) (State := State) ^ T,
      ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.state = none ∧
      ((M.cstep A)^[T] (r, M.initCfg x)).2.tapes.output = [true] :=
  ⟨exists_choice_of_accepts hT, fun ⟨_, _, h1, h2⟩ => accepts_of_choice h1 h2⟩

end OracleNTM

end Cslib.Complexity.NtimeDspace.Oracle
