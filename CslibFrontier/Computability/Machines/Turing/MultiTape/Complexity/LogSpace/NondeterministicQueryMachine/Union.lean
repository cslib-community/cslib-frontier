/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# The union of two nondeterministic query machines

`Turing.NondeterministicQueryMachine.union M N` spends its first choice on selecting one of `M`
and `N`, and then runs the selected machine, keeping the state of the other one unchanged. It
accepts exactly when `M` or `N` accepts
(`Turing.NondeterministicQueryMachine.union_accepts_iff`). Its state is the pair of states and the
selection, so its parts are computable in linear space when those of `M` and `N` are
(`Turing.NondeterministicQueryMachine.union_next_inSpace` and its siblings).

## Main definitions

* `Turing.NondeterministicQueryMachine.UnionState`: both states and the selection.
* `Turing.NondeterministicQueryMachine.union`: the union of two machines.

## Main results

* `Turing.NondeterministicQueryMachine.union_accepts_iff`: the union accepts exactly when one of
  the machines accepts.
* `Turing.NondeterministicQueryMachine.union_query_inSpace`,
  `Turing.NondeterministicQueryMachine.union_next_inSpace`,
  `Turing.NondeterministicQueryMachine.union_halted_inSpace`,
  `Turing.NondeterministicQueryMachine.union_accept_inSpace`: its parts in linear space.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine

open MultiTapeTM ComputableInSpace

/-- The state of the union of two machines: the states of both, and which one runs (`none` before
the first choice, `some false` for the first machine and `some true` for the second). -/
structure UnionState (σ τ : Type) where
  /-- The state of the first machine. -/
  left : σ
  /-- The state of the second machine. -/
  right : τ
  /-- The selected machine, once chosen. -/
  side : Option Bool

/-- States of the union, as their fields. -/
enc_structure eUnion (σ : Type) (τ : Type) (eS : σ ↪ List Bool) (eT : τ ↪ List Bool) :
    UnionState σ τ where
  left : eS, right : eT, side : (encOption encBool)

variable {σ τ : Type} (M : NondeterministicQueryMachine σ) (N : NondeterministicQueryMachine τ)

/-- **The union of two machines**: the first choice selects one of them, which then runs. -/
def union : NondeterministicQueryMachine (UnionState σ τ) where
  init := ⟨M.init, N.init, none⟩
  query s := if s.side.getD false then N.query s.right else M.query s.left
  next p :=
    let ⟨s, ⟨read, choice⟩⟩ := p
    if s.side.isSome then
      if s.side.getD false then ⟨s.left, N.next (s.right, read, choice), s.side⟩
      else ⟨M.next (s.left, read, choice), s.right, s.side⟩
    else ⟨s.left, s.right, some choice⟩
  halted s := s.side.isSome && if s.side.getD false then N.halted s.right else M.halted s.left
  accept s := if s.side.getD false then N.accept s.right else M.accept s.left

variable {M N} (x : List Bool)

theorem replay_union_left (cs : List Bool) (s : σ) (t : τ) :
    (union M N).replay x cs ⟨s, t, some false⟩ = ⟨M.replay x cs s, t, some false⟩ := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [replay_cons, replay_cons, ← ih]
    congr 1
    cases h : M.halted s
    · simp [step, union, h, read]
    · simp [step, union, h]

theorem replay_union_right (cs : List Bool) (s : σ) (t : τ) :
    (union M N).replay x cs ⟨s, t, some true⟩ = ⟨s, N.replay x cs t, some true⟩ := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih =>
    rw [replay_cons, replay_cons, ← ih]
    congr 1
    cases h : N.halted t
    · simp [step, union, h, read]
    · simp [step, union, h]

theorem step_union_none (s : σ) (t : τ) (c : Bool) :
    (union M N).step x ⟨s, t, none⟩ c = ⟨s, t, some c⟩ := by
  simp [step, union]

/-- **The union accepts exactly when one of the machines accepts.** -/
theorem union_accepts_iff (s : σ) (t : τ) :
    ((union M N).withInit ⟨s, t, none⟩).Accepts x ↔
      (M.withInit s).Accepts x ∨ (N.withInit t).Accepts x := by
  constructor
  · rintro ⟨_ | ⟨c, cs⟩, hh, ha⟩
    · change (union M N).halted ⟨s, t, none⟩ = true at hh
      simp [union] at hh
    · change (union M N).halted ((union M N).replay x (c :: cs) ⟨s, t, none⟩) = true at hh
      change (union M N).accept ((union M N).replay x (c :: cs) ⟨s, t, none⟩) = true at ha
      rw [replay_cons, step_union_none] at hh ha
      cases c
      · rw [replay_union_left] at hh ha
        have hh' : M.halted (M.replay x cs s) = true := by simpa [union] using hh
        have ha' : M.accept (M.replay x cs s) = true := by simpa [union] using ha
        exact .inl ⟨cs, hh', ha'⟩
      · rw [replay_union_right] at hh ha
        have hh' : N.halted (N.replay x cs t) = true := by simpa [union] using hh
        have ha' : N.accept (N.replay x cs t) = true := by simpa [union] using ha
        exact .inr ⟨cs, hh', ha'⟩
  · rintro (⟨cs, hh, ha⟩ | ⟨cs, hh, ha⟩)
    · refine ⟨false :: cs, ?_, ?_⟩
      · change (union M N).halted ((union M N).replay x (false :: cs) ⟨s, t, none⟩) = true
        rw [replay_cons, step_union_none, replay_union_left]
        rw [run_withInit] at hh
        simp only [union, Option.isSome_some, Option.getD_some, Bool.true_and, Bool.false_eq_true,
          ↓reduceIte]
        exact hh
      · change (union M N).accept ((union M N).replay x (false :: cs) ⟨s, t, none⟩) = true
        rw [replay_cons, step_union_none, replay_union_left]
        rw [run_withInit] at ha
        simp only [union, Option.getD_some, Bool.false_eq_true, ↓reduceIte]
        exact ha
    · refine ⟨true :: cs, ?_, ?_⟩
      · change (union M N).halted ((union M N).replay x (true :: cs) ⟨s, t, none⟩) = true
        rw [replay_cons, step_union_none, replay_union_right]
        rw [run_withInit] at hh
        simp only [union, Option.isSome_some, Option.getD_some, Bool.true_and, ↓reduceIte]
        exact hh
      · change (union M N).accept ((union M N).replay x (true :: cs) ⟨s, t, none⟩) = true
        rw [replay_cons, step_union_none, replay_union_right]
        rw [run_withInit] at ha
        simp only [union, Option.getD_some, ↓reduceIte]
        exact ha

/-! ### The parts, in linear space -/

section Certificates

variable {encS : σ ↪ List Bool} {encT : τ ↪ List Bool}

private theorem union_id : ComputableInSpace (fun s : UnionState σ τ => s) (eUnion σ τ encS encT)
    (eUnion σ τ encS encT) fun s => (eUnion σ τ encS encT s).length :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

theorem union_query_inSpace
    (hM : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hN : ComputableInSpace N.query encT encNat fun s => (encT s).length) :
    ComputableInSpace (union M N).query (eUnion σ τ encS encT) encNat
      fun s => (eUnion σ τ encS encT s).length :=
  budget_ite (budget_optionGetD (encB := encBool) false (eUnion_side_budget σ τ encS encT union_id))
    (budget_comp_linear (f := fun s : UnionState σ τ => s.right) hN
      (eUnion_right_budget σ τ encS encT union_id))
    (budget_comp_linear (f := fun s : UnionState σ τ => s.left) hM
      (eUnion_left_budget σ τ encS encT union_id))

theorem union_halted_inSpace
    (hM : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (hN : ComputableInSpace N.halted encT encBool fun s => (encT s).length) :
    ComputableInSpace (union M N).halted (eUnion σ τ encS encT) encBool
      fun s => (eUnion σ τ encS encT s).length :=
  have hside := eUnion_side_budget σ τ encS encT union_id
  budget_boolAnd (budget_optionIsSome (encB := encBool) hside)
    (budget_ite (budget_optionGetD (encB := encBool) false hside)
    (budget_comp_linear (f := fun s : UnionState σ τ => s.right) hN
      (eUnion_right_budget σ τ encS encT union_id))
    (budget_comp_linear (f := fun s : UnionState σ τ => s.left) hM
      (eUnion_left_budget σ τ encS encT union_id)))

theorem union_accept_inSpace
    (hM : ComputableInSpace M.accept encS encBool fun s => (encS s).length)
    (hN : ComputableInSpace N.accept encT encBool fun s => (encT s).length) :
    ComputableInSpace (union M N).accept (eUnion σ τ encS encT) encBool
      fun s => (eUnion σ τ encS encT s).length :=
  budget_ite (budget_optionGetD (encB := encBool) false (eUnion_side_budget σ τ encS encT union_id))
    (budget_comp_linear (f := fun s : UnionState σ τ => s.right) hN
      (eUnion_right_budget σ τ encS encT union_id))
    (budget_comp_linear (f := fun s : UnionState σ τ => s.left) hM
      (eUnion_left_budget σ τ encS encT union_id))

theorem union_next_inSpace
    (hM : ComputableInSpace M.next (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hN : ComputableInSpace N.next (encPair encT (encPair (encOption encBool) encBool)) encT
      fun p => (encPair encT (encPair (encOption encBool) encBool) p).length) :
    ComputableInSpace (union M N).next
      (encPair (eUnion σ τ encS encT) (encPair (encOption encBool) encBool)) (eUnion σ τ encS encT)
      fun p => (encPair (eUnion σ τ encS encT) (encPair (encOption encBool) encBool) p).length := by
  have hp := fst (eUnion σ τ encS encT) (encPair (encOption encBool) encBool)
  have hq := snd (eUnion σ τ encS encT) (encPair (encOption encBool) encBool)
  have hl := eUnion_left_budget σ τ encS encT hp
  have hr := eUnion_right_budget σ τ encS encT hp
  have hside := eUnion_side_budget σ τ encS encT hp
  have hnN := budget_comp_linear hN (budget_prod hr hq)
  have hnM := budget_comp_linear hM (budget_prod hl hq)
  exact budget_ite (budget_optionIsSome (encB := encBool) hside)
    (budget_ite (budget_optionGetD (encB := encBool) false hside)
      (eUnion_mk_budget σ τ encS encT hl hnN hside)
      (eUnion_mk_budget σ τ encS encT hnM hr hside))
    (eUnion_mk_budget σ τ encS encT hl hr (budget_optionSome (encO := encOption encBool) hq.snd'))

end Certificates

/-- The size of a state of the union, in the sizes of the states of the machines. -/
theorem length_eUnion_le {encS : σ ↪ List Bool} {encT : τ ↪ List Bool} (s : UnionState σ τ) :
    (eUnion σ τ encS encT s).length ≤ 2 * (encS s.left).length + 2 * (encT s.right).length + 8 := by
  obtain ⟨l, r, o⟩ := s
  have : (encOption encBool o).length ≤ 2 := by cases o <;> simp
  simp only [eUnion_apply, length_encPair]
  omega

end Turing.NondeterministicQueryMachine
