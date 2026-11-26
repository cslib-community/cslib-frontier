/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Phases

/-!
# The choices of the dealing program

The dealing program of [AnthropicVPVNP2026] begins with four phases of picks. It guesses the
states between the blocks, the first one `i` and the last one `e` (`Codes.stateSteps`); the row
data of every party on every tape (`Codes.rowDataSteps`); the number of units of every string
between two base parties (`Codes.countSteps`); and the outcome of every channel
(`Codes.outcomeSteps`). With each choice it writes what the scripts of the groups will read: the
flags of the rows, the keys of the units, the comparisons of the units from a base party to itself
and the keys of the new units, and the numbers and outcomes as digits for the straight-line
program. The sum over the states after these phases is the sum over all choices
(`sum_execAll_choiceSteps`), at the state `Codes.chosenState`.

## Main definitions

* `initialState`: the state at the beginning, with the parts of the input.
* `stateOptions`, `Codes.countOption`: the options of a state between the blocks and of a number
  of units.
* `Codes.stateSteps`, `Codes.rowDataSteps`, `Codes.countSteps`, `Codes.outcomeSteps`,
  `Codes.choiceSteps`: the phases of picks.
* `Codes.chosenState`: the state after the picks.

## Main results

* `sum_execAll_choiceSteps`: the sum over the states after the picks.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54: it guesses `q`, `ρ`, the numbers of packets and the outcomes). Ported from
the source module `Nc.Dl.Run` (its phases of picks) and `Nc.Dl.Total`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D pS : ℕ} {M : Moves F (K + K + A') E}
  {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  (C : Codes S M U0 U1 D pS) {m : ℕ}

/-- The state at the beginning: the parts `pt` of the input, and empty values. -/
@[expose] def initialState (pt : Fin K → Tree) : PlanName S M U0 U1 pS → Tree
  | .part κ => pt κ
  | _ => .nil

/-- The options of the state `a` between the blocks: `i` first, `e` last, and any state
between. -/
@[expose] noncomputable def stateOptions (i e : Q) (a : Fin (K + 1)) : List Q :=
  if a = 0 then [i] else if a = Fin.last K then [e] else (univ : Finset Q).toList

namespace Codes

/-- Phase 1: pick the states between the blocks, and write their numbers `qn`. -/
@[expose] noncomputable def stateSteps (qn : Q → ℕ) (i e : Q) : List DStep :=
  (univ : Finset (Fin (K + 1))).toList.map fun a =>
    C.pickStep (stateOptions i e a) fun q => [(.state a, num (qn q))]

/-- Phase 2: pick the row data of every party on every tape, and write their flags and codes. -/
@[expose] noncomputable def rowDataSteps : List DStep :=
  (univ : Finset (Option S × Fin (K + K))).toList.map fun a =>
    C.pickStep (univ : Finset (RowData (K + K))).toList fun d =>
      [(.flags a.1 a.2, flagsTree d), (.rowData a.1 a.2, ofBits (C.rowData d))]

/-- The assignments of phase 3 for `n` units of the string from `a.1` to `a.2`: the keys of their
copies at both ends, the number as a digit, and for `a.1 = a.2` the comparisons of the two
copies. -/
@[expose] def countOption (hU0 : U0 < D) (a : Fin (K + K) × Fin (K + K)) (n : Fin (U0 + 1)) :
    List (PlanName S M U0 U1 pS × Tree) :=
  (.writeKeys a.1 a.2, C.writeKeysTree a.1 a.2 n) ::
    (.readKeys a.1 a.2, C.readKeysTree a.1 a.2 n) ::
      (.countDigit a.1 a.2, C.digitTree (Fin.castLE hU0 n)) ::
        if a.1 = a.2 then [(.selfAgree a.1, C.selfAgreeTree a.1 n)] else []

/-- Phase 3: pick the number of units of the string between every two base parties. -/
@[expose] noncomputable def countSteps (hU0 : U0 < D) : List DStep :=
  (univ : Finset (Fin (K + K) × Fin (K + K))).toList.map fun a =>
    C.pickStep (univ : Finset (Fin (U0 + 1))).toList (C.countOption hU0 a)

/-- Phase 4: pick the outcome of every channel, and write it as a digit and the keys of the new
units at both ends. -/
@[expose] noncomputable def outcomeSteps (hU1 : U1 ≤ D) : List DStep :=
  (univ : Finset M.Channel).toList.map fun ν => C.pickStep (univ : Finset (Fin U1)).toList fun j =>
    [(.outcomeDigit ν, C.digitTree (Fin.castLE hU1 j)), (.newKeys ν false, C.newKeysTree ν false j),
      (.newKeys ν true, C.newKeysTree ν true j)]

/-- The phases of picks. -/
@[expose] noncomputable def choiceSteps (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    List DStep :=
  C.stateSteps qn i e ++ (C.rowDataSteps ++ (C.countSteps hU0 ++ C.outcomeSteps hU1))

/-- The state after the picks of the states `q` between the blocks, the row data `ρ`, the
numbers of units `n` and the outcomes `o`, from the parts `pt` of the input. -/
@[expose] def chosenState (pt : Fin K → Tree) (qn : Q → ℕ) (hU0 : U0 < D) (hU1 : U1 ≤ D)
    (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1) :
    PlanName S M U0 U1 pS → Tree
  | .part κ => pt κ
  | .state a => num (qn (q a))
  | .flags s p => flagsTree (ρ s p)
  | .rowData s p => ofBits (C.rowData (ρ s p))
  | .writeKeys a b => C.writeKeysTree a b (n a b)
  | .readKeys a b => C.readKeysTree a b (n a b)
  | .selfAgree a => C.selfAgreeTree a (n a a)
  | .countDigit a b => C.digitTree (Fin.castLE hU0 (n a b))
  | .outcomeDigit ν => C.digitTree (Fin.castLE hU1 (o ν))
  | .newKeys ν d => C.newKeysTree ν d (o ν)
  | _ => .nil

end Codes

/-! ### The four phases -/

section Phases

variable {B : Type} [CommRing B]

private def own1 : PlanName S M U0 U1 pS → Option (Fin (K + 1))
  | .state a => some a
  | _ => none

private def val1 (qn : Q → ℕ) (q : Fin (K + 1) → Q) : PlanName S M U0 U1 pS → Tree
  | .state a => num (qn (q a))
  | _ => .nil

omit [DecidableEq Q] in
private theorem stateOptions_iff (hK : 0 < K) {i e : Q} {q : Fin (K + 1) → Q} :
    (∀ a, q a ∈ stateOptions i e a) ↔ q 0 = i ∧ q (Fin.last K) = e := by
  have h0 : Fin.last K ≠ 0 := fun h => by simp [Fin.ext_iff] at h; omega
  constructor
  · intro h
    have h1 := h 0
    have h2 := h (Fin.last K)
    simp only [stateOptions, h0, ↓reduceIte, List.mem_singleton] at h1 h2
    exact ⟨h1, h2⟩
  rintro ⟨h1, h2⟩ a
  unfold stateOptions
  split_ifs with ha ha' <;> simp [*]

omit [Fintype S] [DecidableEq S] in
private theorem sum_stateSteps (hK : 0 < K) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m (C.stateSteps qn i e) (extend C.name (initialState pt) fun _ => .nil)).map Φ).sum =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        Φ (extend C.name (fun x => if (own1 x).isSome then val1 qn q x else initialState pt x)
          fun _ => .nil) else 0 := by
  classical
  rw [Codes.stateSteps, sum_execAll_pickSteps C rfl _ (fun a => ?_) _ own1 (val1 qn)
    (fun f a b hb => ?_) (fun f a x hx => ?_) rfl]
  · exact sum_congr rfl fun q _ => by simp only [stateOptions_iff hK]
  · unfold stateOptions
    split_ifs <;> simp [nodup_toList]
  · simp only [List.mem_singleton] at hb
    simp [hb, own1, val1]
  · cases x <;> simp_all [own1]

private def own2 : PlanName S M U0 U1 pS → Option (Option S × Fin (K + K))
  | .flags s p => some (s, p)
  | .rowData s p => some (s, p)
  | _ => none

private def val2 (ρ : Option S × Fin (K + K) → RowData (K + K)) :
    PlanName S M U0 U1 pS → Tree
  | .flags s p => flagsTree (ρ (s, p))
  | .rowData s p => ofBits (C.rowData (ρ (s, p)))
  | _ => .nil

private theorem sum_rowDataSteps {st : PlanName S M U0 U1 pS → Tree} (hz : st .empty = .nil)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m C.rowDataSteps (extend C.name st fun _ => .nil)).map Φ).sum =
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K),
        Φ (extend C.name (fun x => if (own2 x).isSome then val2 C (uncurry ρ) x else st x)
          fun _ => .nil) := by
  rw [Codes.rowDataSteps, sum_execAll_pickSteps C hz _ (fun _ => nodup_toList _) _ own2 (val2 C)
    (fun f a b hb => ?_) (fun f a x hx => ?_) rfl, ← (Equiv.curry _ _ _).symm.sum_comp]
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [own2, val2]
  · cases x <;> simp_all [own2] <;> subst hx <;> simp

private def own3 : PlanName S M U0 U1 pS → Option (Fin (K + K) × Fin (K + K))
  | .writeKeys a b => some (a, b)
  | .readKeys a b => some (a, b)
  | .countDigit a b => some (a, b)
  | .selfAgree a => some (a, a)
  | _ => none

private def val3 (hU0 : U0 < D) (n : Fin (K + K) × Fin (K + K) → Fin (U0 + 1)) :
    PlanName S M U0 U1 pS → Tree
  | .writeKeys a b => C.writeKeysTree a b (n (a, b))
  | .readKeys a b => C.readKeysTree a b (n (a, b))
  | .countDigit a b => C.digitTree (Fin.castLE hU0 (n (a, b)))
  | .selfAgree a => C.selfAgreeTree a (n (a, a))
  | _ => .nil

omit [Fintype S] [DecidableEq S] in
private theorem sum_countSteps (hU0 : U0 < D) {st : PlanName S M U0 U1 pS → Tree}
    (hz : st .empty = .nil) (Φ : (List Bool → Tree) → B) :
    ((execAll m (C.countSteps hU0) (extend C.name st fun _ => .nil)).map Φ).sum =
      ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
        Φ (extend C.name (fun x => if (own3 x).isSome then val3 C hU0 (uncurry n) x else st x)
          fun _ => .nil) := by
  classical
  rw [Codes.countSteps, sum_execAll_pickSteps C hz _ (fun _ => nodup_toList _) _ own3
    (val3 C hU0) (fun f a b hb => ?_) (fun f a x hx => ?_) rfl,
    ← (Equiv.curry _ _ _).symm.sum_comp]
  · simp
  · obtain ⟨a1, a2⟩ := a
    simp only [Codes.countOption, List.mem_cons] at hb
    rcases hb with rfl | rfl | rfl | hb
    · simp [own3, val3]
    · simp [own3, val3]
    · simp [own3, val3]
    · split_ifs at hb with h
      · simp only [List.mem_singleton] at hb
        subst hb h
        simp [own3, val3]
      · simp at hb
  · cases x <;> simp_all [own3, Codes.countOption] <;> subst hx <;> simp

private def own4 : PlanName S M U0 U1 pS → Option M.Channel
  | .outcomeDigit ν => some ν
  | .newKeys ν _ => some ν
  | _ => none

private def val4 (hU1 : U1 ≤ D) (o : M.Channel → Fin U1) : PlanName S M U0 U1 pS → Tree
  | .outcomeDigit ν => C.digitTree (Fin.castLE hU1 (o ν))
  | .newKeys ν d => C.newKeysTree ν d (o ν)
  | _ => .nil

omit [Fintype S] [DecidableEq S] in
private theorem sum_outcomeSteps (hU1 : U1 ≤ D) {st : PlanName S M U0 U1 pS → Tree}
    (hz : st .empty = .nil) (Φ : (List Bool → Tree) → B) :
    ((execAll m (C.outcomeSteps hU1) (extend C.name st fun _ => .nil)).map Φ).sum =
      ∑ o : M.Channel → Fin U1,
        Φ (extend C.name (fun x => if (own4 x).isSome then val4 C hU1 o x else st x)
          fun _ => .nil) := by
  classical
  rw [Codes.outcomeSteps, sum_execAll_pickSteps C hz _ (fun _ => nodup_toList _) _ own4
    (val4 C hU1) (fun f a b hb => ?_) (fun f a x hx => ?_) rfl]
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [own4, val4]
  · cases x with
    | outcomeDigit ν => simp_all [own4]
    | newKeys ν d => cases d <;> simp_all [own4]
    | _ => simp [own4] at hx

/-- **The choices.** The sum over the states after the phases of picks, from the parts `pt` of the
input, is the sum over the states `q` between the blocks from `i` to `e`, the row data `ρ`, the
numbers of units `n` and the outcomes `o`, at the states `Codes.chosenState`. -/
theorem sum_execAll_choiceSteps (hK : 0 < K) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q)
    (hU0 : U0 < D) (hU1 : U1 ≤ D) (Φ : (List Bool → Tree) → B) :
    ((execAll m (C.choiceSteps qn i e hU0 hU1) (extend C.name (initialState pt) fun _ => .nil)).map
      Φ).sum = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K),
          ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), ∑ o : M.Channel → Fin U1,
            Φ (extend C.name (C.chosenState pt qn hU0 hU1 q ρ n o) fun _ => .nil) else 0 := by
  rw [Codes.choiceSteps, sum_execAll_append, sum_stateSteps C hK]
  refine sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
  rw [sum_execAll_append, sum_rowDataSteps C rfl]
  refine sum_congr rfl fun ρ _ => ?_
  rw [sum_execAll_append, sum_countSteps C hU0 rfl]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_outcomeSteps C hU1 rfl]
  refine sum_congr rfl fun o _ => ?_
  congr 2
  funext x
  cases x <;> rfl

end Phases

end Cslib.Circuits.Arithmetic.Separation.Dealing
