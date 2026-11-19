/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.TensorStrategy
import CslibFrontier.Foundations.Quantum.POVM.Postprocessing
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map

/-!
# Entangled parallel repetition

To play the last `n` coordinates of an `n + 1`-fold strategy, fix the two first questions
in advance. Each player prepends their own fixed question, then drops the first outcome
coordinate. The state and local dimensions are unchanged. Averaging these restricted
strategies over a fresh first question pair recovers the probability of winning the last
`n` coordinates. Thus the entangled value is nonincreasing in the repetition count, and every
nonempty repetition has entangled value at most that of the base game.

## Main results

* `Cslib.PCP.TwoProverGame.quantumValue_pow_antitone` gives monotonicity under additional rounds
  of parallel repetition.
* `Cslib.PCP.TwoProverGame.quantumValue_pow_le_of_pos` bounds any nonempty repetition by the
  original game.
* `Cslib.PCP.TwoProverGame.pow_quantumValue_le_quantumValue_pow` gives the independent-play lower
  bound.
-/

public section

namespace Cslib.PCP

variable {X Y A B ι κ : Type*} [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}

namespace QuantumStrategy

variable [DecidableEq A] [DecidableEq B]

/-- Fix the first question pair and retain only the tail of each player's answer. -/
noncomputable def restrictTail
    (S : QuantumStrategy (Fin (n + 1) → X) (Fin (n + 1) → Y)
      (Fin (n + 1) → A) (Fin (n + 1) → B) ι κ)
    (x₀ : X) (y₀ : Y) :
    QuantumStrategy (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) ι κ where
  state := S.state
  norm_state := S.norm_state
  alice x := (S.alice (Fin.cons x₀ x)).map Fin.tail
  bob y := (S.bob (Fin.cons y₀ y)).map Fin.tail

/-- The extracted strategy draws exactly the tail of the original answers. -/
theorem answers_restrictTail
    (S : QuantumStrategy (Fin (n + 1) → X) (Fin (n + 1) → Y)
      (Fin (n + 1) → A) (Fin (n + 1) → B) ι κ)
    (x₀ : X) (y₀ : Y) (x : Fin n → X) (y : Fin n → Y) :
    (S.restrictTail x₀ y₀).answers x y =
      (S.answers (Fin.cons x₀ x) (Fin.cons y₀ y)).map (Prod.map Fin.tail Fin.tail) := by
  simp only [answers, restrictTail, Quantum.POVM.kronecker_map, Quantum.POVM.measure_map]

variable {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

/-- Play one strategy on the first coordinate and an independent strategy on the remaining
coordinates. The two states occupy distinct registers on each side. -/
noncomputable def cons (S : QuantumStrategy X Y A B ι κ)
    (T : QuantumStrategy (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) ι' κ') :
    QuantumStrategy (Fin (n + 1) → X) (Fin (n + 1) → Y)
      (Fin (n + 1) → A) (Fin (n + 1) → B) (ι × ι') (κ × κ') where
  state := (S.tensor T).state
  norm_state := (S.tensor T).norm_state
  alice x := ((S.tensor T).alice (x 0, Fin.tail x)).map fun p => Fin.cons p.1 p.2
  bob y := ((S.tensor T).bob (y 0, Fin.tail y)).map fun p => Fin.cons p.1 p.2

/-- Independent answer pairs are concatenated in coordinate order. -/
theorem answers_cons (S : QuantumStrategy X Y A B ι κ)
    (T : QuantumStrategy (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) ι' κ')
    (x : Fin (n + 1) → X) (y : Fin (n + 1) → Y) :
    (S.cons T).answers x y =
      ((S.answers (x 0) (y 0)).bind fun ab => (T.answers (Fin.tail x) (Fin.tail y)).map (ab, ·)).map
        (fun ⟨⟨a, b⟩, ⟨aTail, bTail⟩⟩ => (Fin.cons a aTail, Fin.cons b bTail)) := by
  calc
    _ = ((S.tensor T).answers (x 0, Fin.tail x) (y 0, Fin.tail y)).map
            (Prod.map (fun p => Fin.cons p.1 p.2) (fun p => Fin.cons p.1 p.2)) := by
      simp only [answers, cons, Quantum.POVM.kronecker_map, Quantum.POVM.measure_map]
    _ = _ := by rw [answers_tensor, PMF.map_comp]; rfl

end QuantumStrategy

namespace TwoProverGame

variable [Finite X] [Finite Y] (G : TwoProverGame X Y A B)

omit [Fintype A] [Fintype B] in
private theorem questions_pow_succ (n : ℕ) :
    (G.pow (n + 1)).questions = G.questions.bind fun q₀ =>
      (G.pow n).questions.map fun q => (Fin.cons q₀.1 q.1, Fin.cons q₀.2 q.2) := by
  simp only [pow, Probability.PMF.pi_fin_succ, PMF.map_bind, PMF.map_comp]
  congr 1 with q₀ : 1
  congr 1
  funext q
  exact Prod.ext (Fin.comp_cons Prod.fst q₀ q) (Fin.comp_cons Prod.snd q₀ q)

/-- A strategy winning every coordinate also wins after the verifier ignores the first
coordinate. Fixing the ignored questions gives a valid strategy for the shorter game. -/
theorem quantumWinProb_pow_succ_le
    (S : QuantumStrategy (Fin (n + 1) → X) (Fin (n + 1) → Y)
      (Fin (n + 1) → A) (Fin (n + 1) → B) ι κ) :
    (G.pow (n + 1)).quantumWinProb S ≤ (G.pow n).quantumValue := by
  classical
  let T := fun q₀ : X × Y => S.restrictTail q₀.1 q₀.2
  let rounds (q₀ : X × Y) :
      PMF (((Fin (n + 1) → X) × (Fin (n + 1) → Y)) ×
        (Fin (n + 1) → A) × (Fin (n + 1) → B)) :=
    (G.pow n).questions.bind fun q =>
      (S.answers (Fin.cons q₀.1 q.1) (Fin.cons q₀.2 q.2)).map fun ab =>
        ((Fin.cons q₀.1 q.1, Fin.cons q₀.2 q.2), ab)
  let drop := fun z : ((Fin (n + 1) → X) × (Fin (n + 1) → Y)) ×
      (Fin (n + 1) → A) × (Fin (n + 1) → B) =>
    (Prod.map Fin.tail Fin.tail z.1, Prod.map Fin.tail Fin.tail z.2)
  have hrounds (q₀ : X × Y) :
      (rounds q₀).map drop = (G.pow n).questions.bind fun q =>
        ((T q₀).answers q.1 q.2).map (q, ·) := by
    simp only [rounds, T, PMF.map_bind, PMF.map_comp, QuantumStrategy.answers_restrictTail]
    congr 1 with q : 1
  have hbound (q₀ : X × Y) :
      ((rounds q₀).map drop).toOuterMeasure {z | (G.pow n).AcceptsRound z} ≤
        ENNReal.ofReal (G.pow n).quantumValue := by
    rw [hrounds, ← ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal ((G.pow n).quantumWinProb_le_quantumValue (T q₀))
  unfold quantumWinProb answersWinProb
  refine ENNReal.toReal_le_of_le_ofReal (G.pow n).quantumValue_nonneg ?_
  rw [questions_pow_succ, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  change (G.questions.bind rounds).toOuterMeasure _ ≤ _
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' q₀, G.questions q₀ * ENNReal.ofReal (G.pow n).quantumValue := by
      refine tsum_le_tsum fun q₀ => by
        gcongr
        refine le_trans ?_ (hbound q₀)
        rw [PMF.toOuterMeasure_map_apply]
        exact PMF.toOuterMeasure_mono _ fun _ hz i => hz.1 i.succ
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Adding a repetition coordinate cannot increase the entangled value. -/
theorem quantumValue_pow_succ_le (n : ℕ) :
    (G.pow (n + 1)).quantumValue ≤ (G.pow n).quantumValue :=
  (G.pow (n + 1)).quantumValue_le (G.pow n).quantumValue_nonneg
    fun S => G.quantumWinProb_pow_succ_le S

/-- Entangled value is nonincreasing under parallel repetition. -/
theorem quantumValue_pow_antitone : Antitone (fun n => (G.pow n).quantumValue) :=
  antitone_nat_of_succ_le G.quantumValue_pow_succ_le

omit [Finite X] [Finite Y] in
private theorem quantumValue_le_of_relabel
    {X' Y' A' B' : Type*} [Fintype A'] [Fintype B'] (H : TwoProverGame X' Y' A' B')
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (hq : H.questions = G.questions.map (eX.prodCongr eY))
    (ha : ∀ x y a b, H.accepts (eX x) (eY y) (eA a) (eB b) ↔ G.accepts x y a b) :
    G.quantumValue ≤ H.quantumValue := by
  classical
  refine G.quantumValue_le H.quantumValue_nonneg ?_
  intro ι κ _ _ _ _ S
  let T : QuantumStrategy X' Y' A' B' ι κ :=
    { state := S.state
      norm_state := S.norm_state
      alice := fun x => (S.alice (eX.symm x)).map eA
      bob := fun y => (S.bob (eY.symm y)).map eB }
  have hab (x : X) (y : Y) :
      T.answers (eX x) (eY y) = (S.answers x y).map (Prod.map eA eB) := by
    simp only [QuantumStrategy.answers, T, Equiv.symm_apply_apply,
      Quantum.POVM.kronecker_map, Quantum.POVM.measure_map]
  have hscore : H.quantumWinProb T = G.quantumWinProb S := by
    let f := fun z : (X × Y) × A × B => (eX.prodCongr eY z.1, Prod.map eA eB z.2)
    have hrounds : (H.questions.bind fun q => (T.answers q.1 q.2).map (q, ·)) =
        (G.questions.bind fun q => (S.answers q.1 q.2).map (q, ·)).map f := by
      rw [hq, PMF.bind_map, PMF.map_bind]
      congr 1
      funext q
      rcases q with ⟨x, y⟩
      simp only [Function.comp_def, Equiv.prodCongr_apply, Prod.map_apply, hab, PMF.map_comp]
      rfl
    rw [quantumWinProb, quantumWinProb, answersWinProb, answersWinProb, hrounds,
      PMF.toOuterMeasure_map_apply]
    have hpreimage : f ⁻¹' {z | H.AcceptsRound z} = {z | G.AcceptsRound z} := by
      ext ⟨⟨x, y⟩, a, b⟩
      exact ha x y a b
    rw [hpreimage]
  rw [← hscore]
  exact H.quantumWinProb_le_quantumValue T

private abbrev singleTupleEquiv (U : Type*) : U ≃ (Fin 1 → U) :=
  (Equiv.funUnique (Fin 1) U).symm

/-- A one-coordinate repetition has exactly the original entangled value. -/
theorem quantumValue_pow_one : (G.pow 1).quantumValue = G.quantumValue := by
  let eX := singleTupleEquiv X
  let eY := singleTupleEquiv Y
  let eA := singleTupleEquiv A
  let eB := singleTupleEquiv B
  let eQ := eX.prodCongr eY
  have hq : (G.pow 1).questions = G.questions.map eQ := by
    have h : (Probability.PMF.pi fun _ : Fin 1 => G.questions) =
        G.questions.map (singleTupleEquiv (X × Y)) := by
      ext q
      rw [Probability.PMF.pi_apply, Probability.PMF.map_equiv_apply, Fin.prod_univ_one]
      rfl
    rw [pow, h, PMF.map_comp]
    rfl
  refine le_antisymm ?_ (G.quantumValue_le_of_relabel (G.pow 1) eX eY eA eB
    hq (fun x y a b => ⟨fun h => h 0, fun h _ => h⟩))
  refine (G.pow 1).quantumValue_le_of_relabel G eX.symm eY.symm eA.symm eB.symm ?_ ?_
  · change G.questions = (G.pow 1).questions.map eQ.symm
    rw [hq, PMF.map_comp, show (⇑eQ.symm ∘ ⇑eQ) = id from eQ.symm_comp_self, PMF.map_id]
  · intro x y a b
    change G.accepts (x 0) (y 0) (a 0) (b 0) ↔ ∀ i, G.accepts (x i) (y i) (a i) (b i)
    exact ⟨fun h i => by simpa only [Subsingleton.elim i 0] using h, fun h => h 0⟩

/-- Every nonempty parallel repetition has entangled value at most the original game's value. -/
theorem quantumValue_pow_le_of_pos {n : ℕ} (hn : 0 < n) :
    (G.pow n).quantumValue ≤ G.quantumValue :=
  (G.quantumValue_pow_antitone hn).trans_eq G.quantumValue_pow_one

/-- A first-coordinate strategy and an independent tail strategy win with the product of
their winning probabilities. -/
theorem quantumWinProb_pow_cons {ι' κ' : Type*}
    [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ'] [DecidableEq A] [DecidableEq B]
    (S : QuantumStrategy X Y A B ι κ)
    (T : QuantumStrategy (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) ι' κ') :
    (G.pow (n + 1)).quantumWinProb (S.cons T) =
      G.quantumWinProb S * (G.pow n).quantumWinProb T := by
  let firstRound := G.questions.bind fun q => (S.answers q.1 q.2).map (q, ·)
  let tailRound := (G.pow n).questions.bind fun q => (T.answers q.1 q.2).map (q, ·)
  let consRound (z : ((X × Y) × A × B) ×
      ((Fin n → X) × (Fin n → Y)) × (Fin n → A) × (Fin n → B)) :
      ((Fin (n + 1) → X) × (Fin (n + 1) → Y)) × (Fin (n + 1) → A) × (Fin (n + 1) → B) :=
    ((Fin.cons z.1.1.1 z.2.1.1, Fin.cons z.1.1.2 z.2.1.2),
      Fin.cons z.1.2.1 z.2.2.1, Fin.cons z.1.2.2 z.2.2.2)
  have hrounds : ((G.pow (n + 1)).questions.bind fun q =>
      ((S.cons T).answers q.1 q.2).map (q, ·)) =
      (firstRound.bind fun z => tailRound.map (z, ·)).map consRound := by
    simp only [questions_pow_succ, firstRound, tailRound, PMF.bind_bind, PMF.map_bind,
      PMF.bind_map, Function.comp_def, QuantumStrategy.answers_cons, Fin.cons_zero, Fin.tail_cons,
      PMF.map_comp]
    congr 1 with q : 1
    exact PMF.bind_comm _ _ _
  have haccept : consRound ⁻¹' {z | (G.pow (n + 1)).AcceptsRound z} =
      {z | G.AcceptsRound z} ×ˢ {z | (G.pow n).AcceptsRound z} := by
    ext ⟨⟨⟨x, y⟩, a, b⟩, ⟨x', y'⟩, a', b'⟩
    change (∀ i : Fin (n + 1), G.accepts
      (Fin.cons (α := fun _ => X) x x' i) (Fin.cons (α := fun _ => Y) y y' i)
      (Fin.cons (α := fun _ => A) a a' i) (Fin.cons (α := fun _ => B) b b' i)) ↔
      G.accepts x y a b ∧ ∀ i, G.accepts (x' i) (y' i) (a' i) (b' i)
    rw [Fin.forall_fin_succ]
    rfl
  simp only [quantumWinProb, answersWinProb]
  rw [hrounds, PMF.toOuterMeasure_map_apply, haccept,
    Probability.PMF.toOuterMeasure_bind_pair_prod, ENNReal.toReal_mul]

omit [Finite X] [Finite Y] in
private theorem quantumValue_mul_le {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c)
    (h : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (S : QuantumStrategy X Y A B ι κ), G.quantumWinProb S * v ≤ c) :
    G.quantumValue * v ≤ c := by
  rcases hv.eq_or_lt with rfl | hp
  · simpa using hc
  · refine (le_div_iff₀ hp).mp (G.quantumValue_le (div_nonneg hc hv) ?_)
    intro ι κ _ _ _ _ S
    exact (le_div_iff₀ hp).mpr (h S)

/-- Appending an independent coordinate gives a product lower bound for entangled value. -/
theorem mul_quantumValue_pow_le_quantumValue_pow_succ (n : ℕ) :
    G.quantumValue * (G.pow n).quantumValue ≤ (G.pow (n + 1)).quantumValue := by
  classical
  have h₀ := (G.pow (n + 1)).quantumValue_nonneg
  refine G.quantumValue_mul_le (G.pow n).quantumValue_nonneg h₀ ?_
  intro ι κ _ _ _ _ S
  rw [mul_comm]
  refine (G.pow n).quantumValue_mul_le (G.quantumWinProb_nonneg S) h₀ ?_
  intro ι' κ' _ _ _ _ T
  rw [mul_comm, ← G.quantumWinProb_pow_cons S T]
  exact (G.pow (n + 1)).quantumWinProb_le_quantumValue (S.cons T)

/-- The zero-coordinate game accepts vacuously and has entangled value one. -/
@[simp] theorem quantumValue_pow_zero : (G.pow 0).quantumValue = 1 := by
  classical
  let a (_ : Fin 0 → X) := (Fin.elim0 : Fin 0 → A)
  let b (_ : Fin 0 → Y) := (Fin.elim0 : Fin 0 → B)
  have h : (G.pow 0).quantumWinProb (QuantumStrategy.ofDeterministic a b) = 1 := by
    rw [quantumWinProb_ofDeterministic, ← G.winProbOn_univ, Finset.univ_eq_empty,
      G.winProbOn_empty]
  exact le_antisymm (G.pow 0).quantumValue_le_one
    (h ▸ (G.pow 0).quantumWinProb_le_quantumValue (QuantumStrategy.ofDeterministic a b))

/-- Independent play of all coordinates gives the usual product lower bound. -/
theorem pow_quantumValue_le_quantumValue_pow (n : ℕ) :
    G.quantumValue ^ n ≤ (G.pow n).quantumValue := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    exact (mul_le_mul_of_nonneg_left ih G.quantumValue_nonneg).trans
      (G.mul_quantumValue_pow_le_quantumValue_pow_succ n)

end TwoProverGame

end Cslib.PCP
