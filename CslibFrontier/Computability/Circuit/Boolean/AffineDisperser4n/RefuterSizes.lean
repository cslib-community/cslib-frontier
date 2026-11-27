/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs

/-!
# Step count and size invariants of the 4n − 9d refuter's run

`refute` runs `refuterLoop (initialState C) (refuterMeasure (initialState C))`. This file counts
the loop's steps and bounds the sizes of every state the loop visits, in terms of `n` and
`C.size`. These are statements about the refuter's own states; no cost model or running time is
claimed here.

`refuterRun` runs the loop and counts its steps; `refuterLoop` is its first component. The loop's
result is `loopStep^[m] S` with `m` the count (`refuterLoop_eq_iterate`), so every state
it visits is `loopStep^[k] (initialState C)` for some `k ≤ 5 n + 7 C.size` (`refute_steps`). Along
the run:

* no step creates a parameter, auxiliary variable or gate name: these only move between roles or
  are deleted, so every such name stays below `n + C.size` (`nameSet_iterate`). Equation names are
  not bounded here (`moveAffine` takes the fresh name `freshEqn`); only the number of equations is;
* the state stays valid and the measure does not increase (`valid_iterate`, from
  `applyStep_valid`), which bounds the numbers of parameters, gates, equations and pairs, and the
  terms per equation (`sizes_iterate`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.loopStep`: one iteration of the loop body.
* `Cslib.Circuits.Boolean.AffineDisperser4n.nameSet`: the parameters, auxiliary variables and gates
  of a state.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.refuterRun_eq_iterate`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.refuterLoop_eq_iterate`: the loop is an iterate of
  `loopStep`, as many times as `refuterRun` counts.
* `Cslib.Circuits.Boolean.AffineDisperser4n.refuterMeasure_initialState`: the initial measure is
  exactly `5 n + 7 · C.program.cost binaryB2Cost`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.refute_steps`: at most `5 n + 7 C.size` steps.
* `Cslib.Circuits.Boolean.AffineDisperser4n.nameSet_iterate`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.sizes_iterate`: names, counts and `varBound` of every
  state along the run, bounded in `n` and `C.size`.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperserCore.State Cslib.Circuits.Boolean.SemiCircuit

variable {n : ℕ}

/-! ### Step count -/

/-- One iteration of the loop body: `applyStep` with the chosen step, or `S` when none applies. -/
@[expose]
def loopStep (S : State n) : State n :=
  match chooseStep? S with
  | some choice => applyStep S choice
  | none => S

/-- `refuterRun S fuel steps` applies `m ≤ fuel` iterations of `loopStep` and adds `m` to
`steps`. -/
theorem refuterRun_eq_iterate : ∀ (fuel : ℕ) (S : State n) (steps : ℕ),
    ∃ m ≤ fuel, refuterRun S fuel steps = (loopStep^[m] S, steps + m)
  | 0, S, steps => ⟨0, le_rfl, rfl⟩
  | fuel + 1, S, steps => by
    unfold refuterRun
    cases h : chooseStep? S with
    | none => exact ⟨0, Nat.zero_le _, rfl⟩
    | some choice =>
      obtain ⟨m, hm, he⟩ := refuterRun_eq_iterate fuel (applyStep S choice) (steps + 1)
      refine ⟨m + 1, by omega, ?_⟩
      simp only [he, Function.iterate_succ, Function.comp_apply, loopStep, h]
      congr 1
      omega

/-- The step count of `refuterRun` is at most the fuel. -/
theorem refuterRun_snd_le (S : State n) (fuel : ℕ) : (refuterRun S fuel 0).2 ≤ fuel := by
  obtain ⟨m, hm, he⟩ := refuterRun_eq_iterate fuel S 0
  rw [he]
  simpa using hm

/-- `refuterLoop S fuel` is `(refuterRun S fuel 0).2` iterations of `loopStep`. -/
theorem refuterLoop_eq_iterate (S : State n) (fuel : ℕ) :
    refuterLoop S fuel = loopStep^[(refuterRun S fuel 0).2] S := by
  obtain ⟨m, -, he⟩ := refuterRun_eq_iterate fuel S 0
  simp [refuterLoop, he]

/-- The initial measure, exactly: `n` parameters, `C.program.cost binaryB2Cost` gates, no
equations and no auxiliary variables. -/
theorem refuterMeasure_initialState (C : Circuit (fullSignature 2 Bool) n 1) :
    refuterMeasure (initialState C) = 5 * n + 7 * C.program.cost binaryB2Cost := by
  have hcost := size_ofCircuitBinary C
  have hm : (initialState C).m = n := by
    change (ofCircuitBinary C).params.card = n
    simp
  have hs : (initialState C).s = C.program.cost binaryB2Cost := hcost
  have hg : (initialState C).gates.card = C.program.cost binaryB2Cost := by
    have : (ofCircuitBinary C).size =
        (ofCircuitBinary C).gates.card + (ofCircuitBinary C).eqns.card := rfl
    rw [ofCircuitBinary_eqns, Finset.card_empty, add_zero, hcost] at this
    exact this.symm
  have ha := initialState_a C
  have haux0 : (initialState C).aux = ∅ := ofCircuitBinary_aux C
  have harg : ∀ t, State.auxArg (initialState C) t = 0 := by
    intro t
    cases t with
    | const b => rfl
    | node x => simp [State.auxArg, haux0]
  have haux : ∀ G, State.auxIn (initialState C) G = 0 := by
    intro G
    simp [State.auxIn, harg]
  unfold refuterMeasure
  rw [hm, hs, hg, ha]
  split
  · rw [haux]; ring
  · ring

theorem refuterMeasure_initialState_le (C : Circuit (fullSignature 2 Bool) n 1) :
    refuterMeasure (initialState C) ≤ 5 * n + 7 * C.size := by
  rw [refuterMeasure_initialState]
  have h2 := cost_binaryB2Cost_le_size C
  omega

/-- The loop of `refute` makes at most `5 n + 7 C.size` steps. -/
theorem refute_steps (C : Circuit (fullSignature 2 Bool) n 1) :
    (refuterRun (initialState C) (refuterMeasure (initialState C)) 0).2 ≤ 5 * n + 7 * C.size :=
  (refuterRun_snd_le _ _).trans (refuterMeasure_initialState_le C)

/-! ### No step creates a parameter, auxiliary variable or gate name -/

/-- The parameters, auxiliary variables and gates of a state (equation names are not included). -/
@[expose]
def nameSet (S : State n) : Finset ℕ :=
  S.params ∪ S.aux ∪ S.gates

/-- `S'` has no parameter, auxiliary variable or gate that `S` lacks, role by role. -/
private def Shrinks (S' S : State n) : Prop :=
  S'.params ⊆ S.params ∧ S'.aux ⊆ S.aux ∧ S'.gates ⊆ S.gates

private theorem Shrinks.trans {S₁ S₂ S₃ : State n} (h₁ : Shrinks S₁ S₂) (h₂ : Shrinks S₂ S₃) :
    Shrinks S₁ S₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

private theorem Shrinks.nameSet {S' S : State n} (h : Shrinks S' S) : nameSet S' ⊆ nameSet S :=
  Finset.union_subset_union (Finset.union_subset_union h.1 h.2.1) h.2.2

private theorem shrinks_restrict (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) :
    Shrinks (S.restrict x ℓ P) S :=
  ⟨Finset.erase_subset _ _, subset_rfl, subset_rfl⟩

private theorem shrinks_fixConst (S : State n) (w : ℕ) (b : Bool) : Shrinks (S.fixConst w b) S :=
  shrinks_restrict _ _ _ _

private theorem shrinks_addPair (S : State n) (pr : ZeroPair) : Shrinks (S.addPair pr) S :=
  ⟨subset_rfl, subset_rfl, subset_rfl⟩

private theorem shrinks_deleteGate (S : State n) (J : ℕ) (ℓ : Lit) :
    Shrinks (S.deleteGate J ℓ) S :=
  ⟨subset_rfl, subset_rfl, Finset.erase_subset _ _⟩

private theorem shrinks_deleteEqn (S : State n) (e v : ℕ) (ℓ : Lit) :
    Shrinks (S.deleteEqn e v ℓ) S :=
  ⟨subset_rfl, Finset.erase_subset _ _, subset_rfl⟩

private theorem shrinks_dropTrivialEqn (S : State n) (e : ℕ) : Shrinks (S.dropTrivialEqn e) S :=
  ⟨subset_rfl, subset_rfl, subset_rfl⟩

private theorem shrinks_deleteConstraint (S : State n) (N : ℕ ⊕ ℕ) :
    Shrinks (S.deleteConstraint N) S := by
  rcases N with J | e
  · exact shrinks_deleteGate _ _ _
  · dsimp only [AffineDisperserCore.State.deleteConstraint]
    split_ifs
    · exact shrinks_deleteEqn _ _ _ _
    · exact shrinks_deleteEqn _ _ _ _
    · exact shrinks_dropTrivialEqn _ _

private theorem shrinks_partnersShareChildStep (S : State n) (pr : ZeroPair) (H : ℕ ⊕ ℕ) :
    Shrinks (S.partnersShareChildStep pr H) S := by
  rcases H with G | e
  · dsimp only [State.partnersShareChildStep]
    split_ifs <;> first
      | exact (shrinks_deleteGate _ _ _).trans (shrinks_fixConst _ _ _)
      | exact (shrinks_deleteGate _ _ _).trans (shrinks_restrict _ _ _ _)
  · exact (shrinks_deleteConstraint _ _).trans (shrinks_restrict _ _ _ _)

private theorem shrinks_andOnPairStep (S : State n) (G : ℕ) (pr : ZeroPair) (p w : ℕ)
    (prw : Option ZeroPair) (b c : Bool) (Hr : ℕ ⊕ ℕ) (K : ℕ) (Hw' : ℕ ⊕ ℕ) :
    Shrinks (S.andOnPairStep G pr p w prw b c Hr K Hw') S := by
  have h₁ := shrinks_fixConst S (pr.partner p) (pr.partnerBias p)
  dsimp only [State.andOnPairStep]
  rcases prw with _ | q
  · exact ((shrinks_deleteConstraint _ _).trans ((shrinks_deleteGate _ _ _).trans
      (shrinks_fixConst _ _ _))).trans h₁
  · dsimp only
    split_ifs
    · exact ((shrinks_deleteConstraint _ _).trans ((shrinks_deleteGate _ _ _).trans
        (shrinks_fixConst _ _ _))).trans h₁
    all_goals exact ((shrinks_deleteConstraint _ _).trans ((shrinks_deleteConstraint _ _).trans
        ((shrinks_deleteGate _ _ _).trans ((shrinks_fixConst _ _ _).trans
        (shrinks_fixConst _ _ _))))).trans h₁

/-- `swap` keeps the names when both swapped names are already names. -/
private theorem nameSet_swap {S : State n} {x Q : ℕ} (c : Bool) (T : Finset ℕ)
    (hx : x ∈ nameSet S) (hQ : Q ∈ nameSet S) : nameSet (S.swap x Q c T) ⊆ nameSet S := by
  intro i hi
  change i ∈ insert Q (S.params.erase x) ∪ insert x (S.aux.erase Q) ∪ S.gates at hi
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hi
  unfold nameSet at hx hQ ⊢
  simp only [Finset.mem_union] at hx hQ ⊢
  rcases hi with ((rfl | ⟨-, h⟩) | (rfl | ⟨-, h⟩)) | h
  · exact hQ
  · exact Or.inl (Or.inl h)
  · exact hx
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- `unitDelete` keeps the names: `Q` is an auxiliary variable, and `x` is dropped again. -/
private theorem nameSet_unitDelete (S : State n) (x e : ℕ) :
    nameSet (unitDelete S x e) ⊆ nameSet S := by
  unfold unitDelete
  split
  · rename_i Q hQ
    have hQa : Q ∈ S.aux := (Finset.mem_sort _).1 (List.mem_of_find?_eq_some hQ)
    intro i hi
    change i ∈ insert Q (S.params.erase x) ∪ (insert x (S.aux.erase Q)).erase x ∪ S.gates at hi
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hi
    unfold nameSet
    simp only [Finset.mem_union]
    rcases hi with ((rfl | ⟨-, h⟩) | ⟨hix, rfl | ⟨-, h⟩⟩) | h
    · exact Or.inl (Or.inr hQa)
    · exact Or.inl (Or.inl h)
    · exact absurd rfl hix
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · exact subset_rfl

/-- A step chosen by the refuter creates no parameter, auxiliary variable or gate name. -/
theorem nameSet_applyStep {S : State n} {c : StepChoice} (hc : chooseStep? S = some c) :
    nameSet (applyStep S c) ⊆ nameSet S := by
  cases c with
  | deleteConstantGate J => exact (shrinks_deleteConstraint _ _).nameSet
  | deleteDeadGate J => exact (shrinks_deleteGate _ _ _).nameSet
  | deleteShortEqn e => exact (shrinks_deleteConstraint _ _).nameSet
  | deleteUnitParam x e => exact nameSet_unitDelete _ _ _
  | moveAffine J =>
    have hJ : J ∈ S.gates := mem_gates_of_chooseStep?_moveAffine hc
    intro i hi
    change i ∈ S.params ∪ insert J S.aux ∪ S.gates.erase J at hi
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hi
    unfold nameSet
    simp only [Finset.mem_union]
    rcases hi with (h | (rfl | h)) | ⟨-, h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr hJ
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  | degeneratePair p =>
    simp only [applyStep]
    split
    · split_ifs
      · exact (shrinks_fixConst _ _ _).nameSet
      · split
        · exact ((shrinks_deleteConstraint _ _).trans ((shrinks_deleteConstraint _ _).trans
            (shrinks_fixConst _ _ _))).nameSet
        · exact subset_rfl
    · exact subset_rfl
  | partnersShareChild p =>
    simp only [applyStep]
    split
    · exact (shrinks_partnersShareChildStep _ _ _).nameSet
    · exact subset_rfl
  | pairInSystem p =>
    simp only [applyStep]
    split
    · split
      · split_ifs
        · exact ((shrinks_deleteConstraint _ _).trans (shrinks_fixConst _ _ _)).nameSet
        · exact (nameSet_unitDelete _ _ _).trans
            ((shrinks_deleteConstraint _ _).trans (shrinks_fixConst _ _ _)).nameSet
      · exact subset_rfl
    · exact subset_rfl
  | andOnPair G p =>
    simp only [applyStep]
    split
    · split
      · exact (shrinks_andOnPairStep _ _ _ _ _ _ _ _ _ _ _).nameSet
      · exact subset_rfl
    · exact subset_rfl
  | swapAuxIn G =>
    simp only [applyStep]
    split
    · rename_i a b hab
      have ha : a ∈ S.aux := by
        unfold auxArgs at hab
        split at hab
        · split_ifs at hab with h₁ h₂
          · cases hab; exact h₁
          · cases hab; exact h₂
        · cases hab
      split_ifs
      · exact (shrinks_deleteGate _ _ _).nameSet
      · exact (shrinks_deleteGate _ _ _).nameSet
      · split
        · rename_i y hy
          have hy' : y ∈ (findAffineRep S a).2 :=
            (Finset.mem_sort _).1 (List.mem_of_find?_eq_some hy)
          have hyp : y ∈ S.params := (Finset.mem_filter.1 hy').1
          exact nameSet_swap _ _ (by unfold nameSet; simp [hyp]) (by unfold nameSet; simp [ha])
        · exact subset_rfl
    · exact subset_rfl
  | pairCreation G =>
    simp only [applyStep]
    split
    · split
      · exact ((shrinks_deleteConstraint _ _).trans ((shrinks_deleteGate _ _ _).trans
          (shrinks_addPair _ _))).nameSet
      · exact subset_rfl
    · exact subset_rfl

theorem nameSet_loopStep (S : State n) : nameSet (loopStep S) ⊆ nameSet S := by
  unfold loopStep
  split
  · rename_i c hc
    exact nameSet_applyStep hc
  · exact subset_rfl

/-- The initial names are below `n + C.size`. -/
theorem nameSet_initialState (C : Circuit (fullSignature 2 Bool) n 1) :
    nameSet (initialState C) ⊆ Finset.range (n + C.size) := by
  intro i hi
  change i ∈ (ofCircuitBinary C).params ∪ (ofCircuitBinary C).aux ∪
    (ofCircuitBinary C).gates at hi
  simp only [ofCircuitBinary_params, ofCircuitBinary_aux, Finset.union_empty,
    Finset.mem_union, Finset.mem_range] at hi
  rw [Finset.mem_range]
  rcases hi with h | h
  · omega
  · exact (mem_gates_ofCircuitBinary h).2

/-- Along the run, every parameter, auxiliary variable and gate name stays below `n + C.size`. -/
theorem nameSet_iterate (C : Circuit (fullSignature 2 Bool) n 1) (k : ℕ) :
    nameSet (loopStep^[k] (initialState C)) ⊆ Finset.range (n + C.size) := by
  induction k with
  | zero => exact nameSet_initialState C
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (nameSet_loopStep _).trans ih

/-! ### Validity and counts along the run -/

/-- Every state of the run is valid for the function `C` computes, and its measure is at most the
initial one. -/
theorem valid_iterate (C : Circuit (fullSignature 2 Bool) n 1) (k : ℕ) :
    (loopStep^[k] (initialState C)).Valid (fun x => C.eval fullInterpretation x 0) ∧
      refuterMeasure (loopStep^[k] (initialState C)) ≤ refuterMeasure (initialState C) := by
  induction k with
  | zero =>
    refine ⟨initialState_valid fun x => ?_, le_rfl⟩
    ext i
    rw [Fin.eq_zero i]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    unfold loopStep
    split
    · rename_i c hc
      obtain ⟨hlt, hv, -, -⟩ := applyStep_valid ih.1 c hc
      exact ⟨hv, hlt.le.trans ih.2⟩
    · exact ih

private theorem pairs_card_le {S : State n} {f : BooleanFunction n} (hS : S.Valid f) :
    S.pairs.card ≤ S.params.card := by
  apply Finset.card_le_card_of_injOn (fun pr : ZeroPair => pr.fst)
  · intro pr hpr
    exact (hS.pair_mem pr hpr).1
  · intro a ha b hb hab
    by_contra hne
    exact (hS.pairs_disjoint a ha b hb hne).1 hab

private theorem card_le_measure (S : State n) :
    S.params.card + S.gates.card + S.eqns.card ≤ refuterMeasure S := by
  have h : refuterMeasure S = 4 * (S.params.card + (S.gates.card + S.eqns.card)) +
      3 * S.gates.card + S.a +
      (if h : S.gates.Nonempty then S.auxIn (S.gates.min' h) else 0) := rfl
  omega

private theorem varBound_le_of_nameSet {S : State n} {N : ℕ}
    (h : nameSet S ⊆ Finset.range N) : varBound S ≤ N + 1 := by
  unfold varBound
  have : (S.params ∪ S.aux).sup id ≤ N := by
    apply Finset.sup_le
    intro i hi
    have : i ∈ nameSet S := by
      unfold nameSet
      exact Finset.mem_union_left _ hi
    exact (Finset.mem_range.1 (h this)).le
  omega

/-- Size invariants of every state of the run, in `n` and `C.size`. -/
theorem sizes_iterate (C : Circuit (fullSignature 2 Bool) n 1) (k : ℕ) :
    let S := loopStep^[k] (initialState C)
    S.params.card + S.gates.card + S.eqns.card ≤ 5 * n + 7 * C.size ∧
    S.pairs.card ≤ S.params.card ∧
    (∀ e ∈ S.eqns, (S.eqn e).terms.card ≤ 3) ∧
    nameSet S ⊆ Finset.range (n + C.size) ∧
    S.aux.card ≤ n + C.size ∧
    varBound S ≤ n + C.size + 1 := by
  intro S
  obtain ⟨hv, hm⟩ := valid_iterate C k
  have hN := nameSet_iterate C k
  refine ⟨(card_le_measure S).trans (hm.trans (refuterMeasure_initialState_le C)),
    pairs_card_le hv, hv.wf.card_terms_le, hN, ?_, varBound_le_of_nameSet hN⟩
  have : S.aux ⊆ Finset.range (n + C.size) := by
    intro i hi
    apply hN
    unfold nameSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  simpa using Finset.card_le_card this

end Cslib.Circuits.Boolean.AffineDisperser4n
