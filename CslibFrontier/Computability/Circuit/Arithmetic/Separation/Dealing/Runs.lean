/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Choices
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Templates
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Picks

/-!
# The runs of the dealing program

After its choices (`Codes.choiceSteps`), the dealing program of [AnthropicVPVNP2026] computes
deterministically: it checks the row data of every row against the row before
(`Codes.rowCheckSteps`), runs the straight-line program on the numbers of units and the outcomes
(`Codes.gateSteps`), and reads off as trees the numbers of units of the moves, the conditions and
whether the units are cut (`Codes.readOutSteps`). It then rejects unless the row data are valid,
the numbers of units valid and the outcomes good (`Codes.checkSteps`); these are the steps of
`Codes.dealSteps`. The sum over the states after them is the sum over the choices that pass the
checks, at states with the values of the end (`Final`, with no contents yet) that the templates
of the scripts read (`sum_execAll_dealSteps`).

## Main definitions

* `RowValidAfter`: row data that are valid after a given last party of the row before.
* `inputName`: the names that the inputs of the straight-line program read.
* `Codes.rowCheckStep`, `Codes.gateStep`, `Codes.readOutStep`: the deterministic steps.
* `Codes.rowCheckSteps`, `Codes.gateSteps`, `Codes.readOutSteps`, `Codes.checkSteps`,
  `Codes.dealSteps`: the phases of the dealing program up to its checks.

## Main results

* `sum_execAll_dealSteps`: the sum over the runs of the steps up to the checks.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: it rejects unless `ρ` is valid, the numbers give every node at most `N`
packets, and all outcomes are good; it computes by the binary operations). Ported from the source
modules `Nc.Dl.Run`, `Nc.Dl.Run2` and `Nc.Dl.Total`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- The row data `d` are those of a row of a staircase after a row whose last party is `h`, as
in `ValidRow`. -/
@[expose] def RowValidAfter {A : ℕ} (h : ℕ) (d : RowData A) : Prop :=
  if d.empty then (d.first : ℕ) = h ∧ (d.last : ℕ) = h else h ≤ d.first ∧ d.first ≤ d.last

instance {A : ℕ} (h : ℕ) (d : RowData A) : Decidable (RowValidAfter h d) :=
  inferInstanceAs (Decidable (if d.empty then _ else _))

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D nI pS mm : ℕ} {M : Moves F (K + K + A') E}
  {S : Type} [Fintype S] [DecidableEq S] (C : Codes S M U0 U1 D pS) {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (tab : SlpTab P grp D nI pS) {m : ℕ}

/-- The name that an input of the straight-line program reads: a number of units or an outcome,
as a digit. -/
@[expose] def inputName : (Fin (K + K) × Fin (K + K)) ⊕ M.Channel → PlanName S M U0 U1 pS
  | .inl ab => .countDigit ab.1 ab.2
  | .inr ν => .outcomeDigit ν

/-- The names that the read-outs write: the numbers of units of the moves, the conditions, and
whether the units are cut. -/
private def readOutName :
    Fin E ⊕ Option (Fin E) ⊕ UnitId (K + K) U0 M.Channel U1 → PlanName S M U0 U1 pS
  | .inl x => .count x
  | .inr (.inl c) => .condition c
  | .inr (.inr u) => .isCut u

namespace Codes

/-- The check of the row data of the party `p` on the tape `s` against the last party of the row
before (`0` for the first row). -/
@[expose] noncomputable def rowCheckStep (s : Option S) (p : Fin (K + K)) : DStep :=
  if h : (p : ℕ) = 0 then
    .op (C.name .empty) (C.name (.rowData s p)) (C.name (.rowValid s p))
      (.cons (trieOf C.rowData fun d => bit (decide (RowValidAfter 0 d))) .nil)
  else
    .op (C.name (.rowData s ⟨p - 1, by omega⟩)) (C.name (.rowData s p)) (C.name (.rowValid s p))
      (trieOf C.rowData fun d' => trieOf C.rowData fun d => bit (decide (RowValidAfter d'.last d)))

/-- Phase 5: the checks of all rows. -/
@[expose] noncomputable def rowCheckSteps : List DStep :=
  (univ : Finset (Option S × Fin (K + K))).toList.map (uncurry C.rowCheckStep)

open Classical in
/-- Step `k` of the straight-line program: it reads an input, writes a constant, or applies an
operation to two earlier steps (and writes the empty value in no other case, since `tab` is a
straight-line program). -/
@[expose] noncomputable def gateStep (k : Fin pS) : DStep :=
  if h : ∃ i, tab.fn k = tab.inp i then
    C.unaryStep (inputName (tab.input h.choose)) (.gate k) C.digitTree
  else if h : ∃ c, tab.fn k = fun _ => c then C.constStep (.gate k) (C.digitTree h.choose)
  else if h : ∃ (i j : Fin pS) (φ : Fin D → Fin D → Fin D), i < k ∧ j < k ∧
      ∀ x, tab.fn k x = φ (tab.fn i x) (tab.fn j x) then
    C.binaryStep (.gate h.choose) (.gate h.choose_spec.choose) (.gate k)
      h.choose_spec.choose_spec.choose
  else C.constStep (.gate k) .nil

/-- Phase 6: the straight-line program. -/
@[expose] noncomputable def gateSteps : List DStep := (List.finRange pS).map (C.gateStep tab)

/-- A read-out: the number of units of the move `x` as a number, and a condition or whether the
unit `u` is cut as a bit. -/
@[expose] noncomputable def readOutStep :
    Fin E ⊕ Option (Fin E) ⊕ UnitId (K + K) U0 M.Channel U1 → DStep
  | .inl x => C.unaryStep (.gate (tab.countGate x)) (.count x) fun d => num d
  | .inr (.inl c) => C.unaryStep (.gate (tab.conditionGate c)) (.condition c) fun d =>
      bit (decide ((d : ℕ) = 1))
  | .inr (.inr u) => C.unaryStep (.gate (tab.cutGate u)) (.isCut u) fun d =>
      bit (decide ((d : ℕ) = 1))

/-- Phase 7: the read-outs. -/
@[expose] noncomputable def readOutSteps : List DStep :=
  (univ : Finset (Fin E ⊕ Option (Fin E) ⊕ UnitId (K + K) U0 M.Channel U1)).toList.map
    (C.readOutStep tab)

/-- Phase 8: reject unless all rows are valid and all conditions hold. -/
@[expose] noncomputable def checkSteps : List DStep :=
  (((univ : Finset (Option S × Fin (K + K))).toList.map fun a => C.name (.rowValid a.1 a.2)) ++
    (univ : Finset (Option (Fin E))).toList.map fun c => C.name (.condition c)).map DStep.check

/-- The steps of the dealing program up to its checks: the choices, the checks of the rows, the
straight-line program, the read-outs and the checks. -/
@[expose] noncomputable def dealSteps {Q : Type} [Fintype Q] (qn : Q → ℕ) (i e : Q)
    (hU0 : U0 < D) (hU1 : U1 ≤ D) : List DStep :=
  C.choiceSteps qn i e hU0 hU1 ++
    (C.rowCheckSteps ++ (C.gateSteps tab ++ (C.readOutSteps tab ++ C.checkSteps)))

end Codes

/-! ### The deterministic phases -/

section Deterministic

omit [Fintype S] [DecidableEq S] in
private theorem rowValid_injective :
    Injective (uncurry Name.rowValid : Option S × Fin (K + K) → PlanName S M U0 U1 pS) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ ⟨⟩
  rfl

omit [DecidableEq S] in
private theorem execAll_rowCheckSteps {st : PlanName S M U0 U1 pS → Tree}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} (hz : st .empty = .nil)
    (hρ : ∀ s p, st (.rowData s p) = ofBits (C.rowData (ρ s p))) :
    execAll m C.rowCheckSteps (extend C.name st fun _ => .nil) =
      [extend C.name (extend (uncurry Name.rowValid) (fun a => bit (decide (ValidRow (ρ a.1) a.2)))
        st) fun _ => .nil] := by
  classical
  refine execAll_writeSteps C (fun a => mem_toList.2 (mem_univ a)) rowValid_injective
    (fun _ st => st .empty = .nil ∧ ∀ s p, st (.rowData s p) = ofBits (C.rowData (ρ s p)))
    ⟨hz, hρ⟩ fun ⟨s, p⟩ _ st ⟨hz, hρ⟩ => ⟨?_, by simp [hz], fun s' p' => by simp [hρ]⟩
  simp only [uncurry_apply_pair, Codes.rowCheckStep]
  split_ifs with h
  · rw [exec_op C.name_injective, hz, hρ, path_ofBits]
    simp [path, tget, hd_cons, tget_trieOf C.rowData_injective, ValidRow, RowValidAfter, prevLast,
      h]
  · rw [exec_op C.name_injective, hρ, hρ, path_ofBits, path_ofBits]
    simp [tget_trieOf C.rowData_injective, ValidRow, RowValidAfter, prevLast, h]

omit [Fintype S] in
private theorem exec_gateStep (x : PlanInput M U0 U1) (k : Fin pS)
    {st : PlanName S M U0 U1 pS → Tree} (hz : st .empty = .nil)
    (hin : ∀ i, st (inputName (tab.input i)) = C.digitTree (tab.inp i x))
    (hprev : ∀ j < k, st (.gate j) = C.digitTree (tab.fn j x)) :
    (C.gateStep tab k).exec m (extend C.name st fun _ => .nil) =
      [extend C.name (update st (.gate k) (C.digitTree (tab.fn k x))) fun _ => .nil] := by
  classical
  unfold Codes.gateStep
  split_ifs with h1 h2 h3
  · rw [Codes.exec_unaryStep hz (hin _), congrFun h1.choose_spec x]
  · rw [Codes.exec_constStep hz, congrFun h2.choose_spec x]
  · obtain ⟨hi, hj, hφ⟩ := h3.choose_spec.choose_spec.choose_spec
    rw [Codes.exec_binaryStep (hprev _ hi) (hprev _ hj), ← hφ x]
  · rcases tab.isSlpStep k k.isLt with h | h | ⟨i, hi, j, hj, φ, hφ⟩
    exacts [(h1 h).elim, (h2 h).elim,
      (h3 ⟨⟨i, hi.trans k.isLt⟩, ⟨j, hj.trans k.isLt⟩, φ, hi, hj, hφ⟩).elim]

omit [Fintype S] [DecidableEq S] in
private theorem execAll_gateSteps (x : PlanInput M U0 U1) {st : PlanName S M U0 U1 pS → Tree}
    (hz : st .empty = .nil) (hin : ∀ i, st (inputName (tab.input i)) = C.digitTree (tab.inp i x)) :
    execAll m (C.gateSteps tab) (extend C.name st fun _ => .nil) =
      [extend C.name (extend Name.gate (fun k => C.digitTree (tab.fn k x)) st) fun _ => .nil] := by
  classical
  refine execAll_writeSteps C List.mem_finRange (fun a b h => Name.gate.inj h)
    (fun rest st => rest.Pairwise (· < ·) ∧ st .empty = .nil ∧
      (∀ i, st (inputName (tab.input i)) = C.digitTree (tab.inp i x)) ∧
      ∀ j, j ∉ rest → st (.gate j) = C.digitTree (tab.fn j x))
    ⟨List.pairwise_lt_finRange pS, hz, hin, fun j hj => absurd (List.mem_finRange j) hj⟩
    fun k rest st ⟨h1, h2, h3, h4⟩ => ⟨exec_gateStep C tab x k h2 h3 fun j hj => h4 j ?_,
      (List.pairwise_cons.1 h1).2, by simp [h2], fun i => ?_, fun j hj => ?_⟩
  · rintro (_ | ⟨_, hj'⟩)
    exacts [lt_irrefl _ hj, lt_asymm hj ((List.pairwise_cons.1 h1).1 j hj')]
  · rw [update_of_ne (by rcases tab.input i <;> simp [inputName]), h3]
  · by_cases hjk : j = k
    · simp [hjk]
    · rw [update_of_ne (by simpa using hjk), h4 j (by simp [hjk, hj])]

/-- The value of a read-out. -/
private def readOutValue (x : PlanInput M U0 U1) :
    Fin E ⊕ Option (Fin E) ⊕ UnitId (K + K) U0 M.Channel U1 → Tree
  | .inl y => num (tab.fn (tab.countGate y) x)
  | .inr (.inl c) => bit (decide ((tab.fn (tab.conditionGate c) x : ℕ) = 1))
  | .inr (.inr u) => bit (decide ((tab.fn (tab.cutGate u) x : ℕ) = 1))

omit [Fintype S] [DecidableEq S] in
private theorem gate_injective : Injective (Name.gate : Fin pS → PlanName S M U0 U1 pS) :=
  fun _ _ h => Name.gate.inj h

omit [Fintype S] [DecidableEq S] in
private theorem readOutName_injective :
    Injective (readOutName : _ → PlanName S M U0 U1 pS) := by
  rintro (_ | _ | _) (_ | _ | _) h <;> simp_all [readOutName]

omit [Fintype S] [DecidableEq S] in
private theorem execAll_readOutSteps (x : PlanInput M U0 U1) {st : PlanName S M U0 U1 pS → Tree}
    (hz : st .empty = .nil) (hg : ∀ k, st (.gate k) = C.digitTree (tab.fn k x)) :
    execAll m (C.readOutSteps tab) (extend C.name st fun _ => .nil) =
      [extend C.name (extend readOutName (readOutValue tab x) st) fun _ => .nil] := by
  classical
  refine execAll_writeSteps C (fun a => mem_toList.2 (mem_univ a)) readOutName_injective
    (fun _ st => st .empty = .nil ∧ ∀ k, st (.gate k) = C.digitTree (tab.fn k x)) ⟨hz, hg⟩
    fun a _ st ⟨hz, hg⟩ => ⟨?_, ?_⟩
  · rcases a with y | c | u <;> exact Codes.exec_unaryStep hz (hg _)
  · rcases a with y | c | u <;> simp [readOutName, hz, hg]

omit [DecidableEq S] in
private theorem execAll_checkSteps (st : PlanName S M U0 U1 pS → Tree) :
    execAll m C.checkSteps (extend C.name st fun _ => .nil) =
      if (∀ s p, st (.rowValid s p) ≠ .nil) ∧ ∀ c, st (.condition c) ≠ .nil then
        [extend C.name st fun _ => .nil] else [] := by
  classical
  split_ifs with h
  · refine execAll_checks_pos fun p hp => ?_
    simp only [List.mem_append, List.mem_map, mem_toList, mem_univ, true_and] at hp
    rcases hp with ⟨a, rfl⟩ | ⟨c, rfl⟩ <;> simp [C.name_injective.extend_apply, h.1, h.2]
  · refine execAll_checks_neg ?_
    simp only [not_and_or, not_forall, not_not] at h
    rcases h with ⟨s, p, h⟩ | ⟨c, h⟩
    · exact ⟨C.name (.rowValid s p), by simp, by rw [C.name_injective.extend_apply, h]⟩
    · exact ⟨C.name (.condition c), by simp, by rw [C.name_injective.extend_apply, h]⟩

end Deterministic

/-! ### All runs -/

section Total

variable {Q : Type} [Fintype Q] [DecidableEq Q] (pt : Fin K → Tree) (qn : Q → ℕ)
  (hU0 : U0 < D) (hU1 : U1 ≤ D) (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K))
  (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)

/-- The state after the deterministic phases. -/
private noncomputable def dealtState : PlanName S M U0 U1 pS → Tree :=
  extend readOutName (readOutValue tab ⟨n, o⟩) (extend Name.gate
    (fun k => C.digitTree (tab.fn k ⟨n, o⟩)) (extend (uncurry Name.rowValid)
      (fun a => bit (decide (ValidRow (ρ a.1) a.2))) (C.chosenState pt qn hU0 hU1 q ρ n o)))

omit [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] in
private theorem dealtState_of_ne {y : PlanName S M U0 U1 pS} (h1 : ∀ a, readOutName a ≠ y)
    (h2 : ∀ k, Name.gate k ≠ y) (h3 : ∀ s p, Name.rowValid s p ≠ y) :
    dealtState C tab pt qn hU0 hU1 q ρ n o y = C.chosenState pt qn hU0 hU1 q ρ n o y := by
  rw [dealtState, extend_apply' _ _ _ fun ⟨a, ha⟩ => h1 a ha,
    extend_apply' _ _ _ fun ⟨k, hk⟩ => h2 k hk, extend_apply' _ _ _ fun ⟨a, ha⟩ => h3 a.1 a.2 ha]

omit [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] in
private theorem dealtState_readOut (a : Fin E ⊕ Option (Fin E) ⊕ UnitId (K + K) U0 M.Channel U1) :
    dealtState C tab pt qn hU0 hU1 q ρ n o (readOutName a) = readOutValue tab ⟨n, o⟩ a :=
  readOutName_injective.extend_apply _ _ a

omit [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] in
private theorem dealtState_gate (k : Fin pS) :
    dealtState C tab pt qn hU0 hU1 q ρ n o (.gate k) = C.digitTree (tab.fn k ⟨n, o⟩) := by
  rw [dealtState, extend_apply' _ _ _ (by rintro ⟨(_ | _ | _), h⟩ <;> simp [readOutName] at h)]
  exact gate_injective.extend_apply _ _ k

omit [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] in
private theorem dealtState_rowValid (s : Option S) (p : Fin (K + K)) :
    dealtState C tab pt qn hU0 hU1 q ρ n o (.rowValid s p) = bit (decide (ValidRow (ρ s) p)) := by
  rw [dealtState, extend_apply' _ _ _ (by rintro ⟨(_ | _ | _), h⟩ <;> simp [readOutName] at h),
    extend_apply' _ _ _ (by simp)]
  exact rowValid_injective.extend_apply _ _ (s, p)

omit [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] in
/-- The states after the deterministic phases have the values of the end, with empty
contents. -/
private theorem final_dealtState :
    Final C tab qn pt q ρ n o (fun _ => (none : UnitContent 0))
      (dealtState C tab pt qn hU0 hU1 q ρ n o) := by
  refine ⟨fun κ => ?_, fun a => ?_, fun s p => ?_, fun p p' => ?_, fun p p' => ?_, fun p => ?_,
    fun ν d => ?_, dealtState_gate C tab pt qn hU0 hU1 q ρ n o, fun x => ?_, fun u => ?_⟩
  pick_goal 8
  · exact (dealtState_readOut C tab pt qn hU0 hU1 q ρ n o (.inl x)).trans
      (by simp [readOutValue, tab.fn_countGate])
  all_goals
    exact dealtState_of_ne C tab pt qn hU0 hU1 q ρ n o
      (by rintro (_ | _ | _) <;> simp [readOutName]) (by simp) (by simp)

omit [DecidableEq S] [Fintype Q] [DecidableEq Q] in
private theorem execAll_computeSteps [DecidablePred tab.Valid] [∀ n o x, Decidable (P.Good n o x)] :
    execAll m (C.rowCheckSteps ++ (C.gateSteps tab ++ (C.readOutSteps tab ++ C.checkSteps)))
      (extend C.name (C.chosenState pt qn hU0 hU1 q ρ n o) fun _ => .nil) =
        if ValidRows ρ ∧ tab.Valid n ∧ ∀ x, P.Good n o x then
          [extend C.name (dealtState C tab pt qn hU0 hU1 q ρ n o) fun _ => .nil] else [] := by
  classical
  rw [execAll_append, execAll_rowCheckSteps C rfl fun s p => rfl, List.flatMap_singleton,
    execAll_append, execAll_gateSteps C tab ⟨n, o⟩ (by simp [extend_apply', Codes.chosenState])
      fun j => ?_, List.flatMap_singleton, execAll_append, execAll_readOutSteps C tab ⟨n, o⟩
      (by simp [extend_apply', Codes.chosenState]) fun k => gate_injective.extend_apply _ _ k,
    List.flatMap_singleton, execAll_checkSteps, ← dealtState]
  · refine if_congr ?_ rfl rfl
    have hc (c : Option (Fin E)) : dealtState C tab pt qn hU0 hU1 q ρ n o (.condition c) =
        readOutValue tab ⟨n, o⟩ (.inr (.inl c)) :=
      dealtState_readOut C tab pt qn hU0 hU1 q ρ n o (.inr (.inl c))
    simp [dealtState_rowValid, hc, bit_ne_nil, readOutValue, SlpTab.conditionGate, Option.forall,
      tab.fn_validGate, tab.fn_goodGate, ValidRows]
  · have hv := tab.inp_val j ⟨n, o⟩
    rcases h : tab.input j with ⟨a, b⟩ | ν <;> rw [h] at hv <;>
      simp only [inputName, extend_apply', Prod.exists, uncurry_apply_pair, reduceCtorEq,
        exists_false, not_false_eq_true, Codes.chosenState] <;>
      exact congrArg C.digitTree (Fin.ext (by simp [hv]))

variable [DecidablePred tab.Valid] [∀ n o x, Decidable (P.Good n o x)]

/-- **The runs of the dealing program up to its checks.** There are states `st q ρ n o` with the
values of the end (`Final`, with empty contents) and the bits that say which units are cut, such
that the sum over the states after `Codes.dealSteps`, from the parts `pt` of the input, is the sum
over the states `q` between the blocks from `i` to `e`, the row data `ρ`, the numbers of units `n`
and the outcomes `o` that pass the checks, at the states `st q ρ n o`. -/
theorem sum_execAll_dealSteps (hK : 0 < K) (i e : Q) :
    ∃ st : (Fin (K + 1) → Q) → (Option S → Fin (K + K) → RowData (K + K)) →
      (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) → (M.Channel → Fin U1) →
        PlanName S M U0 U1 pS → Tree,
      (∀ q ρ n o, Final C tab qn pt q ρ n o (fun _ => (none : UnitContent 0)) (st q ρ n o) ∧
        ∀ u, st q ρ n o (.isCut u) = bit (decide (u ∈ Play.cutUnits
          (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)))) ∧
      ∀ (B : Type) [CommRing B] (Φ : (List Bool → Tree) → B),
        ((execAll m (C.dealSteps tab qn i e hU0 hU1)
          (extend C.name (initialState pt) fun _ => .nil)).map Φ).sum =
        ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
          ∑ ρ : Option S → Fin (K + K) → RowData (K + K),
            ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), ∑ o : M.Channel → Fin U1,
              if ValidRows ρ ∧ tab.Valid n ∧ ∀ x, P.Good n o x then
                Φ (extend C.name (st q ρ n o) fun _ => .nil) else 0
          else 0 := by
  refine ⟨dealtState C tab pt qn hU0 hU1, fun q ρ n o => ⟨final_dealtState C tab pt qn hU0 hU1
    q ρ n o, fun u => ?_⟩, fun B _ Φ => ?_⟩
  · rw [show Name.isCut u = readOutName (.inr (.inr u)) from rfl, dealtState_readOut]
    simp only [readOutValue, tab.fn_cutGate]
    split_ifs <;> simp [*]
  · rw [Codes.dealSteps, sum_execAll_append, sum_execAll_choiceSteps C hK]
    refine sum_congr rfl fun q _ => if_congr Iff.rfl (sum_congr rfl fun ρ _ =>
      sum_congr rfl fun n _ => sum_congr rfl fun o _ => ?_) rfl
    rw [execAll_computeSteps]
    split_ifs <;> simp

end Total

end Cslib.Circuits.Arithmetic.Separation.Dealing
