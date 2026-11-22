/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.BSA
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.Classes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit

/-!
# One query to `BSA` decides linear space in linear time

Remark 8.3: *one query decides any language in `SPACE[n]` in linear time*. A language in
`DSPACE[n]` is decided by a machine `tm` within space `c₁ n + c₂`. The oracle machine
`OneQuery.machine`, without work tapes, writes the query `⟨tm⟩ # x # 1^{R (n + 1)}`
(`bsaQuery`) on its query tape while reading its input twice (forwards to copy `x`, backwards
to write the budget, `R` ones per cell), submits it, and outputs the answer. It halts after
`(R + 2) n + |frame ⟨tm⟩| + R + 4` steps. For a constant `R` above the configuration bound of
the simulation of `tm` and above `2^|⟨tm⟩|`, the answer is `x ∈ L`
(`Cslib.Complexity.NtimeDspace.Oracle.acceptsWithin_desc_iff`).

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.OneQuery.run_machine`: the run of the one-query machine.
* `Cslib.Complexity.NtimeDspace.Oracle.DSPACE_subset_TIMEO_BSA`: `SPACE[n] ⊆ TIME^BSA[n]`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-- The control states of the one-query machine: writing the fixed prefix, copying the input,
turning back, writing the budget, querying and answering. -/
inductive QSt (m R : ℕ) where
  | pre (i : Fin m)
  | xa
  | xb
  | back
  | ones (j : Fin R)
  | ask
  | yes
  | no
  deriving DecidableEq, Fintype

namespace OneQuery

variable (f : List Bool) (R : ℕ)

/-- An action without work tapes. -/
def act {St : Type} (m : SignType) (o : Option Bool) (s : Option St) : Turing.Action 0 Bool St :=
  ⟨m, Fin.elim0, o, s⟩

/-- The state after writing the `i`-th symbol of the prefix. -/
def nextPre (i : Fin f.length) : QSt f.length R :=
  if h : i.1 + 1 < f.length then .pre ⟨i.1 + 1, h⟩ else .xa

/-- Writing the `j`-th of the `R` ones of a cell of the budget. -/
def nextOnes (hR : 0 < R) (j : Fin R) (sym : Option Bool) : OAction 0 (QSt f.length R) :=
  if h : j.1 + 1 < R then .step (act 0 none (some (.ones ⟨j.1 + 1, h⟩))) (some true)
  else match sym with
    | some _ => .step (act (-1) none (some (.ones ⟨0, hR⟩))) (some true)
    | none => .step (act 0 none (some .ask)) (some true)

/-- The transitions of the one-query machine. -/
def tr (hR : 0 < R) :
    QSt f.length R → Option Bool → (Fin 0 → Option Bool) → OAction 0 (QSt f.length R)
  | .pre i, _, _ => .step (act 0 none (some (nextPre f R i))) (some (f.get i))
  | .xa, some _, _ => .step (act 0 none (some .xb)) (some true)
  | .xa, none, _ => .step (act 0 none (some .back)) (some false)
  | .xb, some b, _ => .step (act 1 none (some .xa)) (some b)
  | .xb, none, _ => .step (act 0 none (some .back)) (some false)
  | .back, _, _ => .step (act (-1) none (some (.ones ⟨0, hR⟩))) none
  | .ones j, s, _ => nextOnes f R hR j s
  | .ask, _, _ => .ask .yes .no
  | .yes, _, _ => .step (act 0 (some true) none) none
  | .no, _, _ => .step (act 0 (some false) none) none

/-- **The one-query machine**: write `f`, then `frame x`, then `R (|x| + 1)` ones, query, and
output the answer. -/
def machine (hf : 0 < f.length) (hR : 0 < R) : OracleTM 0 (QSt f.length R) :=
  ⟨.pre ⟨0, hf⟩, tr f R hR⟩

variable {x : List Bool}

/-- A running configuration with empty output. -/
def C (s : QSt f.length R) (p : Fin (x.length + 2)) (Q : List Bool) :
    OCfg 0 (QSt f.length R) x :=
  ⟨⟨some s, p, fun _ _ => none, fun _ => 0, []⟩, Q⟩

variable {f R} (hf : 0 < f.length) (hR : 0 < R) (A : Set (List Bool))

lemma step_C {s s' : QSt f.length R} {p : Fin (x.length + 2)} {Q : List Bool} {sym : Option Bool}
    {m : SignType} {o : Option Bool} (hsym : (C f R s p Q).tapes.inputSymbol = sym)
    (h : ∀ w, tr f R hR s sym w = .step (act m none (some s')) o) :
    (machine f R hf hR).step A (C f R s p Q) = C f R s' (moveInputPos p m) (Q ++ o.toList) := by
  rw [OracleTM.step_of_state _ _ (show (C f R s p Q).tapes.state = some s from rfl)]
  change (tr f R hR s _ _).apply A _ = _
  rw [hsym, h]
  simp only [OAction.apply_step, C, act]
  congr 1
  exact Cfg.ext_zero_tapes rfl rfl rfl

lemma inputSymbol_inner {s : QSt f.length R} {Q : List Bool} (p : ℕ) (hp : p < x.length) :
    (C f R s (⟨p + 1, by omega⟩ : Fin (x.length + 2)) Q).tapes.inputSymbol = some x[p] :=
  inputSymbolInner p (by simp [C]; omega) hp

lemma inputSymbol_right {s : QSt f.length R} {Q : List Bool} :
    (C f R s (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) Q).tapes.inputSymbol = none :=
  inputSymbol_eq_none_of_boundary (Or.inr rfl)

lemma inputSymbol_zero {s : QSt f.length R} {Q : List Bool} :
    (C f R s (0 : Fin (x.length + 2)) Q).tapes.inputSymbol = none :=
  inputSymbol_eq_none_of_boundary (Or.inl rfl)

lemma tr_ones_succ {j : Fin R} (h : j.1 + 1 < R) (sym : Option Bool) (w : Fin 0 → Option Bool) :
    tr f R hR (.ones j) sym w = .step (act 0 none (some (.ones ⟨j.1 + 1, h⟩))) (some true) := by
  simp [tr, nextOnes, h]

lemma tr_ones_last_some {j : Fin R} (h : ¬ j.1 + 1 < R) (b : Bool) (w : Fin 0 → Option Bool) :
    tr f R hR (.ones j) (some b) w = .step (act (-1) none (some (.ones ⟨0, hR⟩))) (some true) := by
  simp [tr, nextOnes, h]

lemma tr_ones_last_none {j : Fin R} (h : ¬ j.1 + 1 < R) (w : Fin 0 → Option Bool) :
    tr f R hR (.ones j) none w = .step (act 0 none (some .ask)) (some true) := by
  simp [tr, nextOnes, h]

/-- Writing the prefix `f`. -/
lemma run_pre (r : ℕ) : ∀ (i : ℕ) (hi : i + r + 1 = f.length) (Q : List Bool),
    (machine f R hf hR).runFrom A (C f R (.pre ⟨i, by omega⟩) (1 : Fin (x.length + 2)) Q) (r + 1) =
      C f R .xa 1 (Q ++ f.drop i) := by
  induction r with
  | zero =>
    intro i hi Q
    rw [OracleTM.runFrom_succ', step_C hf hR A rfl fun _ => rfl, moveInputPos_zero]
    have hn : nextPre f R ⟨i, by omega⟩ = .xa := by rw [nextPre, dite_eq_right (by simp; omega)]
    rw [hn]
    simp only [Option.toList_some, OracleTM.runFrom, Function.iterate_zero, id_eq]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
    rfl
  | succ r ih =>
    intro i hi Q
    rw [OracleTM.runFrom_succ', step_C hf hR A rfl fun _ => rfl, moveInputPos_zero]
    have hn : nextPre f R ⟨i, by omega⟩ = .pre ⟨i + 1, by omega⟩ := by
      rw [nextPre, dite_eq_left (by simp; omega)]
    rw [hn, ih (i + 1) (by omega)]
    congr 1
    rw [List.drop_eq_getElem_cons (show i < f.length by omega)]
    simp

/-- Copying the input, framed. -/
lemma run_copy : ∀ (rest : List Bool) (p : ℕ) (hp : p + 1 < x.length + 2) (Q : List Bool),
    x.drop p = rest →
    (machine f R hf hR).runFrom A (C f R .xa ⟨p + 1, hp⟩ Q) (2 * rest.length + 1) =
      C f R .back ⟨x.length + 1, by omega⟩ (Q ++ frame rest) := by
  intro rest
  induction rest with
  | nil =>
    intro p hp Q hd
    have hpx : p = x.length := by
      have := List.drop_eq_nil_iff.mp hd
      omega
    subst hpx
    rw [OracleTM.runFrom_succ', step_C hf hR A inputSymbol_right fun _ => rfl, moveInputPos_zero]
    rfl
  | cons b rest ih =>
    intro p hp Q hd
    have hpl : p < x.length := by
      by_contra h
      rw [List.drop_of_length_le (by omega)] at hd
      cases hd
    rw [List.drop_eq_getElem_cons hpl] at hd
    obtain ⟨hb, hd⟩ := List.cons_eq_cons.mp hd
    rw [show 2 * (b :: rest).length + 1 = (2 * rest.length + 1) + 1 + 1 by simp; ring,
      OracleTM.runFrom_succ', step_C hf hR A (inputSymbol_inner p hpl) fun _ => rfl,
      moveInputPos_zero, OracleTM.runFrom_succ',
      step_C hf hR A (inputSymbol_inner p hpl) fun _ => rfl,
      show (1 : SignType) = .pos from rfl, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    simp only [Option.toList_some]
    rw [ih (p + 1) (by omega) _ hd, hb]
    simp

/-- Turning back at the right end of the input. -/
lemma step_back (Q : List Bool) :
    (machine f R hf hR).step A (C f R .back (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) Q) =
      C f R (.ones ⟨0, hR⟩) (⟨x.length, by omega⟩ : Fin (x.length + 2)) Q := by
  rw
      [step_C hf hR A
      inputSymbol_right fun _ => rfl, show (-1 : SignType) = .neg from rfl, moveInputPos_neg_of_ne_left _ (by simp)]
  simp

/-- The ones of one cell inside the input. -/
lemma run_ones_inner (p : ℕ) (hp1 : 1 ≤ p) (hpl : p ≤ x.length) (r : ℕ) :
    ∀ (j : ℕ) (hj : j + r + 1 = R) (Q : List Bool),
    (machine f R hf hR).runFrom A
      (C f R (.ones ⟨j, by omega⟩) (⟨p, by omega⟩ : Fin (x.length + 2)) Q) (r + 1) =
      C f R (.ones ⟨0, hR⟩) (⟨p - 1, by omega⟩ : Fin (x.length + 2))
        (Q ++ List.replicate (r + 1) true) := by
  have hsym : ∀ (s : QSt f.length R) (Q : List Bool),
      (C f R s (⟨p, by omega⟩ : Fin (x.length + 2)) Q).tapes.inputSymbol = some x[p - 1] := by
    intro s Q
    have := inputSymbol_inner (x := x) (f := f) (R := R) (s := s) (Q := Q) (p - 1) (by omega)
    simp only [show p - 1 + 1 = p by omega] at this
    exact this
  induction r with
  | zero =>
    intro j hj Q
    rw [OracleTM.runFrom_succ', step_C hf hR A (hsym _ _)
      (tr_ones_last_some hR (j := ⟨j, by omega⟩) (by simp; omega) _),
      show (-1 : SignType) = .neg from rfl, moveInputPos_neg_of_ne_left _
          (by simp [Fin.ext_iff]; omega)]
    rfl
  | succ r ih =>
    intro j hj Q
    rw [OracleTM.runFrom_succ', step_C hf hR A (hsym _ _)
      (tr_ones_succ hR (j := ⟨j, by omega⟩) (by simp; omega) _),
      moveInputPos_zero, ih (j + 1) (by omega)]
    simp only [Option.toList_some, List.append_assoc, List.singleton_append, ← List.replicate_succ]

/-- The ones of the cell left of the input, then the query state. -/
lemma run_ones_zero (r : ℕ) : ∀ (j : ℕ) (hj : j + r + 1 = R) (Q : List Bool),
    (machine f R hf hR).runFrom A (C f R (.ones ⟨j, by omega⟩) (0 : Fin (x.length + 2)) Q)
      (r + 1) = C f R .ask 0 (Q ++ List.replicate (r + 1) true) := by
  induction r with
  | zero =>
    intro j hj Q
    rw [OracleTM.runFrom_succ', step_C hf hR A inputSymbol_zero
      (tr_ones_last_none hR (j := ⟨j, by omega⟩) (by simp; omega)),
      moveInputPos_zero]
    rfl
  | succ r ih =>
    intro j hj Q
    rw [OracleTM.runFrom_succ', step_C hf hR A inputSymbol_zero
      (tr_ones_succ hR (j := ⟨j, by omega⟩) (by simp; omega) _), moveInputPos_zero,
      ih (j + 1) (by omega)]
    simp only [Option.toList_some, List.append_assoc, List.singleton_append, ← List.replicate_succ]

/-- The ones of the cells from `p` down to `1`. -/
lemma run_ones (p : ℕ) (hp : p ≤ x.length) (Q : List Bool) :
    (machine f R hf hR).runFrom A
      (C f R (.ones ⟨0, hR⟩) (⟨p, by omega⟩ : Fin (x.length + 2)) Q) (R * p) =
      C f R (.ones ⟨0, hR⟩) (0 : Fin (x.length + 2)) (Q ++ List.replicate (R * p) true) := by
  induction p generalizing Q with
  | zero => simp [OracleTM.runFrom]
  | succ p ih =>
    obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
    rw [show (r + 1) * (p + 1) = (r + 1) + (r + 1) * p by ring, OracleTM.runFrom_add,
      run_ones_inner hf hR A (p + 1) (by omega) hp r 0 (by omega)]
    simp only [show p + 1 - 1 = p by omega]
    rw [ih (by omega), List.append_assoc, ← List.replicate_add]

/-- The query. -/
lemma step_ask (Q : List Bool) :
    (machine f R hf hR).step A (C f R .ask (0 : Fin (x.length + 2)) Q) =
      C f R (open scoped Classical in if Q ∈ A then .yes else .no) 0 [] := by
  rw [OracleTM.step_of_state _ _ (show (C f R .ask (0 : Fin (x.length + 2)) Q).tapes.state =
    some .ask from rfl)]
  rfl

lemma step_yes (Q : List Bool) :
    (machine f R hf hR).step A (C f R .yes (0 : Fin (x.length + 2)) Q) =
      ⟨⟨none, 0, fun _ _ => none, fun _ => 0, [true]⟩, Q⟩ := by
  rw [OracleTM.step_of_state _ _ (show (C f R .yes (0 : Fin (x.length + 2)) Q).tapes.state =
    some .yes from rfl)]
  simp only [C, machine, tr, OAction.apply_step, act, Option.toList_none, List.append_nil]
  congr 1
  exact Cfg.ext_zero_tapes rfl (by simp) rfl

lemma step_no (Q : List Bool) :
    (machine f R hf hR).step A (C f R .no (0 : Fin (x.length + 2)) Q) =
      ⟨⟨none, 0, fun _ _ => none, fun _ => 0, [false]⟩, Q⟩ := by
  rw [OracleTM.step_of_state _ _ (show (C f R .no (0 : Fin (x.length + 2)) Q).tapes.state =
    some .no from rfl)]
  simp only [C, machine, tr, OAction.apply_step, act, Option.toList_none, List.append_nil]
  congr 1
  exact Cfg.ext_zero_tapes rfl (by simp) rfl

/-- The time of the one-query machine on inputs of length `n`. -/
def time (f : List Bool) (R n : ℕ) : ℕ := f.length + (2 * n + 1) + 1 + R * n + R + 1 + 1

open scoped Classical in
/-- **The run of the one-query machine**: after `time f R |x|` steps it has halted with output
`[true]` if `f ++ frame x ++ 1^{R (|x| + 1)} ∈ A` and `[false]` otherwise, with an empty query
tape. -/
theorem run_machine (x : List Bool) :
    (machine f R hf hR).run A x (time f R x.length) =
      ⟨⟨none, 0, fun _ _ => none, fun _ => 0,
        [if f ++ frame x ++ List.replicate (R * (x.length + 1)) true ∈ A then true else false]⟩,
        []⟩ := by
  obtain ⟨m, hm⟩ : ∃ m, f.length = m + 1 := ⟨f.length - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  set M := machine f (r + 1) hf hR
  have hinit : M.toNTM.initCfg x = C f (r + 1) (.pre ⟨0, hf⟩) (1 : Fin (x.length + 2)) [] := rfl
  have ht : time f (r + 1) x.length =
      (m + 1) + ((2 * x.length + 1) + (1 + ((r + 1) * x.length + ((r + 1) + (1 + 1))))) := by
    simp only [time]; omega
  have h1 : M.runFrom A (C f (r + 1) (.pre ⟨0, hf⟩) (1 : Fin (x.length + 2)) []) (m + 1) =
      C f (r + 1) .xa (⟨0 + 1, by omega⟩ : Fin (x.length + 2)) f := by
    have := run_pre hf hR A (x := x) m 0 (by omega) []
    simp only [List.drop_zero, List.nil_append] at this
    rw [this]
    exact congrArg (fun p => C f (r + 1) .xa p f) (Fin.ext (by simp))
  have h2 := run_copy hf hR A (x := x) x 0 (by omega) f (by simp)
  have h3 := step_back hf hR A (x := x) (f ++ frame x)
  have h4 := run_ones hf hR A x.length le_rfl (f ++ frame x)
  have h5 := run_ones_zero hf hR A (x := x) r 0 (by omega)
    (f ++ frame x ++ List.replicate ((r + 1) * x.length) true)
  have h6 := step_ask hf hR A (x := x)
    (f ++ frame x ++ List.replicate ((r + 1) * x.length) true ++ List.replicate (r + 1) true)
  have hq : f ++ frame x ++ List.replicate ((r + 1) * x.length) true ++
      List.replicate (r + 1) true =
      f ++ frame x ++ List.replicate ((r + 1) * (x.length + 1)) true := by
    rw [List.append_assoc, ← List.replicate_add]; ring_nf
  rw [OracleTM.run, ht, hinit, OracleTM.runFrom_add _ _ _ (m + 1), h1,
    OracleTM.runFrom_add _ _ _ (2 * x.length + 1), h2, OracleTM.runFrom_add _ _ _ 1,
    OracleTM.runFrom_succ', OracleTM.runFrom_zero, h3,
    OracleTM.runFrom_add _ _ _ ((r + 1) * x.length), h4, OracleTM.runFrom_add _ _ _ (r + 1), h5,
    OracleTM.runFrom_succ' _ _ _ 1, h6, OracleTM.runFrom_succ', OracleTM.runFrom_zero, hq]
  split_ifs with h
  · exact step_yes hf hR A _
  · exact step_no hf hR A _

open scoped Classical in
/-- The one-query machine decides `{x | f ++ frame x ++ 1^{R (|x| + 1)} ∈ A}` relative to `A`
within time and space `time f R n`. -/
theorem decidesIn_machine {L : Set (List Bool)}
    (hL : ∀ x, x ∈ L ↔ f ++ frame x ++ List.replicate (R * (x.length + 1)) true ∈ A) :
    (machine f R hf hR).DecidesIn A L (fun x => time f R x.length)
      (fun x => time f R x.length) := by
  intro x
  have hrun := run_machine hf hR A x
  have hhalt : ((machine f R hf hR).run A x (time f R x.length)).tapes.Halted := by
    rw [hrun]
  refine ⟨OracleTM.runsInTime_of_halted _ _ hhalt le_rfl, fun p => ?_, time f R x.length, hhalt,
    ?_⟩
  · simp only [OracleNTM.pathSpace, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    refine Finset.sup_le fun n _ => ?_
    have hq : ∀ t, ((machine f R hf hR).run A x t).query.length ≤ time f R x.length := by
      intro t
      rcases le_total t (time f R x.length) with h | h
      · exact ((machine f R hf hR).length_query_runFrom_le A _ t).trans
          (by simp [OracleNTM.initCfg]; omega)
      · rw [(machine f R hf hR).run_eq_of_halted A hhalt h, hrun]; simp
    rw [OracleTM.runPath_apply, p.head_eq]
    exact hq _
  · rw [hrun]
    simp only [indicator, hL x]

end OneQuery

open Cslib.Complexity in
/-- **Remark 8.3: one query to `BSA` decides any language in linear space, in linear time.**
`SPACE[n] ⊆ TIME^BSA[n]`, with Complexitylib's `DSPACE` and the oracle classes of
`Cslib.Complexity.NtimeDspace.Oracle.Classes`. -/
theorem DSPACE_subset_TIMEO_BSA : DSPACE encBits (fun n => n) ⊆ TIMEO BSA (fun n => n) := by
  rintro L ⟨c₁, c₂, t, k, State, hfin, tm, htm⟩
  have := Fintype.ofFinite State
  set eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set d := desc eS eBit tm
  set w := eDesc d
  set D := descLen d
  -- the number of ones per cell
  set R := 2 ^ w.length + 2 * D + 6 + 2 + 6 * (2 * D + 5) * (c₁ + c₂) + d.tapes with hRdef
  have hR : 0 < R := by positivity
  have hf : 0 < (frame w).length := by simp
  have hL : ∀ x, x ∈ L ↔ frame w ++ frame x ++ List.replicate (R * (x.length + 1)) true ∈ BSA := by
    intro x
    change _ ↔ bsaQuery w x _ ∈ BSA
    rw [bsaQuery_mem_BSA_iff, decodeDesc_eDesc]
    have htmx : tm.ComputesInTimeAndSpace x [indicator L x] (t x.length)
        (c₁ * x.length + c₂) := htm x
    have hb : cfgBudget d x.length (c₁ * x.length + c₂) ≤ R * (x.length + 1) := by
      have h₁ : (encNat (x.length + 1)).length ≤ x.length + 1 := length_encNat_le _
      have h₂ : 6 * (2 * D + 5) * (c₁ * x.length + c₂) ≤
          6 * (2 * D + 5) * (c₁ + c₂) * (x.length + 1) := by
        have hle : c₁ * x.length + c₂ ≤ (c₁ + c₂) * (x.length + 1) := by nlinarith
        calc 6 * (2 * D + 5) * (c₁ * x.length + c₂)
            ≤ 6 * (2 * D + 5) * ((c₁ + c₂) * (x.length + 1)) := Nat.mul_le_mul_left _ hle
          _ = _ := by ring
      simp only [cfgBudget]
      have : R * (x.length + 1) = (2 ^ w.length + 2 * D + 6 + 2 + d.tapes) * (x.length + 1) +
          6 * (2 * D + 5) * (c₁ + c₂) * (x.length + 1) := by rw [hRdef]; ring
      have h₃ : 2 * D + 6 + d.tapes + 2 * (x.length + 1) ≤
          (2 ^ w.length + 2 * D + 6 + 2 + d.tapes) * (x.length + 1) := by
        generalize 2 ^ w.length = P
        nlinarith [Nat.zero_le (P * x.length), Nat.zero_le (D * x.length),
          Nat.zero_le (d.tapes * x.length)]
      have e : 3 * (2 * D + 5) * 2 = 6 * (2 * D + 5) := by ring
      rw [e]
      linarith
    have hiff := acceptsWithin_desc_iff eS tm htmx hb
    constructor
    · intro hx
      exact ⟨le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)), hiff.mpr hx⟩
    · exact fun h => hiff.mp h.2
  refine ⟨R + 2, (frame w).length + R + 4, 0, QSt (frame w).length R, inferInstance,
    OneQuery.machine (frame w) R hf hR,
    fun n => (R + 2) * n + ((frame w).length + R + 4), ?_⟩
  refine (OneQuery.decidesIn_machine hf hR BSA hL).mono (fun x => ?_) fun x => ?_ <;>
  · simp only [OneQuery.time]
    ring_nf
    omega

end Cslib.Complexity.NtimeDspace.Oracle
