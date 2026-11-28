/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic

/-!
# Exact reachability of the compact configuration graph

The invariant is an actual finite view whose radix registers equal the current ID. Arithmetic
steps preserve this invariant, so malformed IDs cannot create spurious accepting paths.
The forward implication only requires that source-reachable views fit the selected radix.

The overflow test (`Turing.MultiTapeNTM.ConfigurationGraph.overflow`) detects the represented
views with a step leaving the radix. When no reachable vertex overflows, every source-reachable
view fits the radix, so the graph is exact without any space bound on the source.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad`: exact native acceptance.
* `Turing.MultiTapeNTM.ConfigurationGraph.overflow_vertexID`: overflow means a step leaving the
  radix.
* `Turing.MultiTapeNTM.ConfigurationGraph.fits_of_not_overflow`: a graph without reachable
  overflow represents every reachable view.
* `Turing.MultiTapeNTM.ConfigurationGraph.not_overflow_of_fits`: conversely.
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k B : ℕ} {State : Type} [Fintype State]
  {ntm : MultiTapeNTM k Bool State} {w : List Bool}

theorem radix_pos (D n : ℕ) : 0 < radix D n := pow_pos (by omega) _

/-- A radix that fits some registers is positive. -/
theorem pos_of_fits {r : Register k → ℕ} (hf : Fits B r) : 0 < B :=
  (Nat.zero_le _).trans_lt (hf .inputPos)

theorem stateCode_injective : Function.Injective (stateCode (State := State)) :=
  fun _ _ h => (Fintype.equivFin (Option State)).injective (Fin.ext h)

theorem outputCode_lt (w : List Bool) : outputCode w < 3 := by
  unfold outputCode
  split_ifs <;> decide

theorem outputCode_summary (w : List Bool) : outputCode (outputClass w) = outputCode w := by
  unfold outputClass outputCode
  split_ifs <;> simp_all

theorem outputCode_append (w : List Bool) (b : Option Bool) :
    outputCode (outputClass (w ++ b.toList)) = outputStep (outputCode w) b := by
  rw [outputCode_summary]
  rcases b with _ | b
  · simp [outputStep]
  · rcases w with _ | ⟨_ | _, _ | _⟩ <;> cases b <;> simp [outputCode, outputStep]

theorem outputCode_eq_one_iff {w : List Bool} : outputCode w = 1 ↔ w = [true] := by
  unfold outputCode
  split_ifs <;> simp_all

omit [Fintype State] in
/-- The arithmetic input move agrees with native clamping. -/
theorem inputMove_eq (v : FiniteCfg k Bool State) (d : SignType) :
    inputMove v.input.length v.inputPos.val d = (moveInputPos v.inputPos d).val := by
  have h := val_moveInputPos_eq v.inputPos d
  have hb := v.inputPos.isLt
  cases d <;> simp only [inputMove, SignType.cast] at * <;> omega

/-- The arithmetic tuple update agrees with the summarized finite view step. -/
theorem registers_step (v : FiniteCfg k Bool State) (a : Action k Bool State) :
    registers (v.step a).summarizeOutput = nextRegisters v.input.length (registers v) a := by
  funext i
  cases i with
  | inputPos => exact (inputMove_eq v a.inputTape).symm
  | control => rfl
  | output => exact outputCode_append v.output a.output
  | head i => exact congrArg Prod.fst (tapeCode_step (v.workTapes i) (a.workTapes i))
  | left i => exact congrArg (fun t => t.2.1) (tapeCode_step (v.workTapes i) (a.workTapes i))
  | right i => exact congrArg (fun t => t.2.2) (tapeCode_step (v.workTapes i) (a.workTapes i))

theorem readRegisters_vertexID {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    readRegisters B (vertexID B v) = registers v := by
  exact funext fun i => Cslib.Radix.component_pack (pos_of_fits hf) hf i

theorem vertexID_lt {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    vertexID B v < vertexBound (k := k) B := Cslib.Radix.pack_lt (pos_of_fits hf) hf

theorem valid_vertexID {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    valid (k := k) (State := State) B v.input.length (vertexID B v) = true := by
  have hc : stateCode v.state < Fintype.card (Option State) :=
    (Fintype.equivFin (Option State) v.state).isLt
  simp only [valid, readRegisters_vertexID hf, registers, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨vertexID_lt hf, v.inputPos.isLt⟩, hc⟩, outputCode_lt _⟩, by simp [symbolCode_lt]⟩

theorem fitsB_eq_true {B : ℕ} {r : Register k → ℕ} : fitsB B r = true ↔ Fits B r := by
  simp [fitsB, Fits, List.all_eq_true]

/-- The sole queried symbol agrees with the native input head, including both blank boundaries. -/
theorem inputSymbol_query {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    inputSymbol v.input.length v.inputPos.val
      v.input[queryIndex (k := k) B (vertexID B v)]? = v.inputSymbol := by
  rw [queryIndex, readRegisters_vertexID hf, FiniteCfg.inputSymbol_eq_getD]
  rcases eq_or_ne v.inputPos.val 0 with hz | hz
  · simp [inputSymbol, hz]
  · by_cases he : v.inputPos.val = v.input.length + 1
    · simp [inputSymbol, he]
    · simp only [registers, inputSymbol, hz, he, or_self, ↓reduceIte]
      conv_rhs => rw [show v.inputPos.val = (v.inputPos.val - 1) + 1 by omega]
      simp only [List.getElem?_cons_succ, List.getElem?_map]
      cases v.input[v.inputPos.val - 1]? <;> rfl

theorem matchesEntry_iff (v : FiniteCfg k Bool State) (symbol : Option Bool)
    (t : Instruction k State) :
    matchesEntry v.input.length (registers v) symbol t = true ↔
      v.state = some t.1 ∧ inputSymbol v.input.length v.inputPos.val symbol = t.2.1 ∧
        v.workTapeSymbols = t.2.2.1 := by
  simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_ofFn,
    id_eq, forall_exists_index, forall_apply_eq_imp_iff]
  simp only [registers, stateCode_injective.eq_iff, symbolCode_injective.eq_iff, ← funext_iff,
    and_assoc]
  rfl

/-- Validity rejects every ID outside the ambient vertex range. -/
theorem lt_vertexBound_of_valid {B n u : ℕ}
    (h : valid (k := k) (State := State) B n u = true) :
    u < vertexBound (k := k) B := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

/-- Every successful local edge query stays inside the finite ambient graph. -/
theorem lt_vertexBound_of_edgeWithSymbol {B n u v : ℕ} {symbol : Option Bool}
    (h : edgeWithSymbol ntm B n u v symbol = true) :
    u < vertexBound (k := k) B ∧ v < vertexBound (k := k) B := by
  simp only [edgeWithSymbol, Bool.and_eq_true] at h
  exact ⟨lt_vertexBound_of_valid h.1.1, lt_vertexBound_of_valid h.1.2⟩

/-- An edge out of a represented vertex has an actual native view successor. -/
theorem edge_sound {v : FiniteCfg k Bool State} {u : ℕ}
    (hf : Fits B (registers v))
    (he : Edge ntm B v.input (vertexID B v) u) :
    ∃ v', ntm.ViewStep v v' ∧ v'.input = v.input ∧ u = vertexID B v' ∧
      Fits B (registers v') := by
  simp only [Edge, edgeWithSymbol, readRegisters_vertexID hf, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true] at he
  rcases he.2 with hh | ⟨t, ht, ⟨⟨hm, hfit⟩, hu⟩⟩
  · exact ⟨v, by simp [ViewStep, stateCode_injective hh.1], rfl, hh.2, hf⟩
  · obtain ⟨hs, hi, hw⟩ := (matchesEntry_iff _ _ _).mp hm
    rw [inputSymbol_query hf] at hi
    refine ⟨(v.step t.2.2.2).summarizeOutput, ?_, rfl, ?_, ?_⟩
    · simp only [ViewStep, hs]
      exact ⟨t.2.2.2, by rwa [hi, hw, ← mem_instructions], rfl⟩
    · simpa only [vertexID, registers_step] using hu
    · rwa [registers_step, ← fitsB_eq_true]

/-- Every fitting native view edge is an edge of the compact graph. -/
theorem edge_complete {v v' : FiniteCfg k Bool State}
    (hf : Fits B (registers v))
    (hf' : Fits B (registers v')) (he : ntm.ViewStep v v') :
    Edge ntm B v.input (vertexID B v) (vertexID B v') := by
  cases hs : v.state with
  | none =>
    obtain rfl : v' = v := by simpa [ViewStep, hs] using he
    simp [Edge, edgeWithSymbol, readRegisters_vertexID hf, valid_vertexID hf, registers, hs]
  | some q =>
    obtain ⟨a, ha, rfl⟩ : ∃ a, ntm.Tr q v.inputSymbol v.workTapeSymbols a ∧
        v' = (v.step a).summarizeOutput := by simpa [ViewStep, hs] using he
    simp only [Edge, edgeWithSymbol, readRegisters_vertexID hf, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    refine ⟨⟨valid_vertexID hf, valid_vertexID hf'⟩,
      .inr ⟨(q, v.inputSymbol, v.workTapeSymbols, a), (mem_instructions ntm _).mpr ha,
        ⟨⟨?_, ?_⟩, congrArg (Cslib.Radix.pack B) (registers_step v a)⟩⟩⟩
    · exact (matchesEntry_iff _ _ _).mpr ⟨hs, inputSymbol_query hf, rfl⟩
    · exact fitsB_eq_true.mpr (by rwa [← registers_step])

/-- Initial storage has an input-length-only ID. -/
theorem vertexID_init (ntm : MultiTapeNTM k Bool State) (B : ℕ) (w : List Bool) :
    vertexID B (ntm.initView w) = startID ntm B := by
  exact congrArg (Cslib.Radix.pack B) (funext fun i => by cases i <;> rfl)

omit [Fintype State] in
/-- Views reachable on one input retain precisely that input. -/
theorem input_of_reachable {v : FiniteCfg k Bool State}
    (h : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) : v.input = w := by
  obtain ⟨p, hp⟩ := exists_computationPath_of_viewStep h
  exact hp.input

/-- **Graph reachability is sound once the initial view fits the radix**: every vertex reachable
in the compact graph is the identifier of a source-reachable view that fits. Edges lead only to
fitting views, so nothing is assumed about the other source-reachable views. -/
theorem exists_view_of_reachable (hstart : Fits B (registers (ntm.initView w))) {u : ℕ}
    (h : Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u) :
    ∃ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v ∧ u = vertexID B v ∧
      Fits B (registers v) := by
  induction h with
  | refl => exact ⟨_, .refl, (vertexID_init _ _ _).symm, hstart⟩
  | @tail _ _ _ he ih =>
    obtain ⟨v, hv, rfl, hf⟩ := ih
    obtain ⟨v', hstep, _, hid, hf'⟩ := edge_sound hf (input_of_reachable hv ▸ he)
    exact ⟨v', hv.tail hstep, hid, hf'⟩

/-- Exact graph reachability, provided all source-reachable views fit the radix. -/
theorem reachable_iff (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) (u : ℕ) :
    Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ↔
      ∃ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v ∧ u = vertexID B v := by
  refine ⟨fun h =>
    (exists_view_of_reachable (hfit _ .refl) h).imp fun _ ⟨hv, hid, _⟩ => ⟨hv, hid⟩, ?_⟩
  · rintro ⟨v, hv, rfl⟩
    induction hv with
    | refl => rw [vertexID_init]
    | @tail a b h he ih =>
      exact ih.tail (input_of_reachable h ▸ edge_complete (hfit a h) (hfit b (h.tail he)) he)

/-- `bad` has exactly the native accepting-halt meaning on represented vertices. -/
theorem bad_vertexID {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    bad (k := k) (State := State) B v.input.length (vertexID B v) = true ↔
      v.state = none ∧ v.output = [true] := by
  simp [bad, readRegisters_vertexID hf, valid_vertexID hf, registers, outputCode_eq_one_iff,
    stateCode_injective.eq_iff]

/-- **A reachable bad vertex is an accepting computation**, once the initial view fits the radix.
Unlike `accepts_iff_reachable_bad`, this direction assumes nothing about the other
source-reachable views: a radix too small for the machine can hide accepting computations but
cannot create them. -/
theorem accepts_of_reachable_bad (hstart : Fits B (registers (ntm.initView w))) {u : ℕ}
    (hu : Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u)
    (hb : bad (k := k) (State := State) B w.length u = true) : ntm.Accepts w := by
  obtain ⟨v, hv, rfl, hf⟩ := exists_view_of_reachable hstart hu
  rw [← input_of_reachable hv] at hb
  exact accepts_iff_reflTransGen_viewStep.mpr ⟨v, hv, (bad_vertexID hf).mp hb⟩

/-- Native acceptance is exactly reachability of a bad vertex. No totality or time bound on the
source machine is used; the only assumption is that its reachable registers fit the radix. -/
theorem accepts_iff_reachable_bad
    (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) :
    ntm.Accepts w ↔ ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
      bad (k := k) (State := State) B w.length u = true := by
  refine ⟨fun h => ?_, fun ⟨_, hu, hb⟩ => accepts_of_reachable_bad (hfit _ .refl) hu hb⟩
  obtain ⟨v, hv, hs, ho⟩ := accepts_iff_reflTransGen_viewStep.mp h
  exact ⟨vertexID B v, (reachable_iff hfit _).mpr ⟨v, hv, rfl⟩,
    input_of_reachable hv ▸ (bad_vertexID (hfit v hv)).mpr ⟨hs, ho⟩⟩

/-- **Overflow means a step leaving the radix**: a represented view overflows exactly when one of
its source steps reaches a view that does not fit. -/
theorem overflow_vertexID {v : FiniteCfg k Bool State} (hf : Fits B (registers v)) :
    Overflow ntm B v.input (vertexID B v) ↔
      ∃ v', ntm.ViewStep v v' ∧ ¬ Fits B (registers v') := by
  simp only [Overflow, overflow, readRegisters_vertexID hf, valid_vertexID hf, Bool.true_and,
    List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, fitsB_eq_true]
  constructor
  · rintro ⟨t, ht, hm, hfit⟩
    obtain ⟨hs, hi, hw⟩ := (matchesEntry_iff _ _ _).mp hm
    rw [inputSymbol_query hf] at hi
    refine ⟨(v.step t.2.2.2).summarizeOutput, ?_, fun h => hfit (by rwa [← registers_step])⟩
    simp only [ViewStep, hs]
    exact ⟨t.2.2.2, by rwa [hi, hw, ← mem_instructions], rfl⟩
  · rintro ⟨v', he, hn⟩
    cases hs : v.state with
    | none =>
      obtain rfl : v' = v := by simpa [ViewStep, hs] using he
      exact absurd hf hn
    | some q =>
      obtain ⟨a, ha, rfl⟩ : ∃ a, ntm.Tr q v.inputSymbol v.workTapeSymbols a ∧
          v' = (v.step a).summarizeOutput := by simpa [ViewStep, hs] using he
      exact ⟨(q, v.inputSymbol, v.workTapeSymbols, a), (mem_instructions ntm _).mpr ha,
        (matchesEntry_iff _ _ _).mpr ⟨hs, inputSymbol_query hf, rfl⟩,
        fun h => hn (by rwa [registers_step])⟩

/-- **A graph without reachable overflow is exact**: if the start view fits and no vertex
reachable in the graph overflows, then every source-reachable view fits the radix. -/
theorem fits_of_not_overflow (hstart : Fits B (registers (ntm.initView w)))
    (hno : ∀ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u → ¬ Overflow ntm B w u)
    (v : FiniteCfg k Bool State) (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    Fits B (registers v) := by
  suffices h : Fits B (registers v) ∧
      Relation.ReflTransGen (Edge ntm B w) (startID ntm B) (vertexID B v) from h.1
  induction hv with
  | refl => exact ⟨hstart, by rw [vertexID_init]⟩
  | @tail a b h he ih =>
    have hi := input_of_reachable h
    have hfb : Fits B (registers b) :=
      by_contra fun hn => hno _ ih.2 (hi ▸ (overflow_vertexID ih.1).mpr ⟨b, he, hn⟩)
    exact ⟨hfb, ih.2.tail (hi ▸ edge_complete ih.1 hfb he)⟩

/-- Conversely, when every source-reachable view fits the radix, no reachable vertex overflows. -/
theorem not_overflow_of_fits (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) (u : ℕ)
    (hu : Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u) : ¬ Overflow ntm B w u := by
  obtain ⟨v, hv, rfl⟩ := (reachable_iff hfit u).mp hu
  rw [← input_of_reachable hv, overflow_vertexID (hfit v hv)]
  rintro ⟨v', he, hn⟩
  exact hn (hfit v' (hv.tail he))

end Turing.MultiTapeNTM.ConfigurationGraph
