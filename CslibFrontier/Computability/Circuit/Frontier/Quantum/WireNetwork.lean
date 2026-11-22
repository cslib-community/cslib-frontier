/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Circuit.Quantum.PhaseGates
public import CslibFrontier.Computability.Communication.QuadFormSignRank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Wire-segment tensor-network compilation for quantum circuits

This module compiles active wires of a quantum circuit `C : Cslib.Quantum.Circuit N` into a finite
loopless degree-`d` wire-segment multigraph (`CompiledQuantumNet`) in which zero-qubit and
single-qubit `U(2)` gates (`g.arity ≤ 1`), as well as idle or one-qubit-only ancillas, contribute
**zero** vertices and **zero** edges:

1. **Gate locality and bond-rank-two predicates** (`twoQubitCount`, `TwoLocal`, `HasBondRankTwo`,
   `AllBondRankTwo`). Every `Quantum.Gate.cnot` (`cnot_hasBondRankTwo`) and every controlled
   single-qubit gate `Quantum.Gate.controlled V` (`controlled_hasBondRankTwo`) has Schmidt / bond
   rank at most two, splitting into two degree-`3` vertices (`d = 3`), whereas an arbitrary
   two-qubit `U(4)` gate forms one degree-`4` vertex (`d = 4`).
2. **Active-qubit decoupling and degree-capped tensor networks** (`exists_compiledQuantumNet`).
   Decoupling qubits touched only by `≤ 1`-qubit gates leaves an active wire network on `Aset` of
   size `|V| ≤ 2 n + 6 · twoQubitCount C + 2` whose closed components `Comp` satisfy
   `cycleRankOn Comp + |leafIn ∩ Comp| ≤ twoQubitCount C + 1` (and analogously for `leafOut` and
   the joint `2 n` input/output leaves `leaf2n`).
3. **Single-cut rank, correlation, and fidelity bounds** (`CompiledQuantumNet`). Cutting `P ⊆ V`
   factors transition amplitudes into `2 ^ |G.edgeCut P|` rank-`1` complex terms and single-qubit
   acceptance probabilities into `2 · 4 ^ |G.edgeCut P|` real bilinear terms, yielding single-cut
   bounds for `BQP` correlation, `UQP` sign-rank, quadratic phase-state fidelity, and coherent
   `𝔽₂` linear synthesis (`linBlockMatrix`).

## Main definitions

* `Cslib.Circuits.Frontier.twoQubitCount`: number of two-qubit gates (`g.arity = 2`) in a circuit.
* `Cslib.Circuits.Frontier.TwoLocal`, `Cslib.Circuits.Frontier.HasBondRankTwo`,
  `Cslib.Circuits.Frontier.AllBondRankTwo`: two-qubit locality and bond-rank-two predicates
  (defined via `Cslib.Quantum.Circuit.IsOver`).
* `Cslib.Circuits.Frontier.quantumAcceptProb`, `Cslib.Circuits.Frontier.quantumCorrelation`,
  `Cslib.Circuits.Frontier.phaseState`, `Cslib.Circuits.Frontier.boolMulVec`,
  `Cslib.Circuits.Frontier.linBlockMatrix`: quantum acceptance probability (via
  `Cslib.Quantum.glue`), correlation, quadratic phase states (via `Cslib.Quantum.embedState`), and
  bipartite linear polar block matrices.
* `Cslib.Circuits.Frontier.CompiledQuantumNet`: packaged finite degree-`d` wire network compiled
  from `C : Quantum.Circuit N` together with its component cycle-rank and single-cut bounds.

## Main results

* `Cslib.Circuits.Frontier.cnot_hasBondRankTwo`,
  `Cslib.Circuits.Frontier.controlled_hasBondRankTwo`: `Gate.cnot` and `Gate.controlled V` have
  bond rank at most two.
* `Cslib.Circuits.Frontier.quantumAcceptProb_nonneg`,
  `Cslib.Circuits.Frontier.quantumAcceptProb_le_one`,
  `Cslib.Circuits.Frontier.norm_phaseState`: range and unit-norm properties of quantum observables.
* `Cslib.Circuits.Frontier.half_le_cutRank_linBlockMatrix`: bisection cut-rank lower bound for
  `linBlockMatrix n R` of a submatrix-robust matrix `R`.
* `Cslib.Circuits.Frontier.exists_compiledQuantumNet`: compiles any `AllBondRankTwo` (`d = 3`) or
  `TwoLocal` (`d = 4`) quantum circuit into a `CompiledQuantumNet`.
-/

public section

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

/-! ### Quantum gate predicates and bond-rank-two gates -/

/-- Number of two-qubit gates (`g.arity = 2`) in a quantum circuit `C`; zero-qubit and single-qubit
`U(2)` gates contribute `0`. -/
@[expose]
def twoQubitCount {N : ℕ} (C : Quantum.Circuit N) : ℕ :=
  (C.filter fun g => decide (g.arity = 2)).length

@[simp]
theorem twoQubitCount_nil {N : ℕ} : twoQubitCount ([] : Quantum.Circuit N) = 0 := rfl

@[simp]
theorem twoQubitCount_cons {N : ℕ} (g : Quantum.PlacedGate N) (C : Quantum.Circuit N) :
    twoQubitCount (g :: C) = (if g.arity = 2 then 1 else 0) + twoQubitCount C := by
  simp only [twoQubitCount, List.filter_cons, decide_eq_true_eq]
  split_ifs <;> simp only [List.length_cons, zero_add, add_comm]

@[simp]
theorem twoQubitCount_append {N : ℕ} (C D : Quantum.Circuit N) :
    twoQubitCount (C ++ D) = twoQubitCount C + twoQubitCount D := by
  simp only [twoQubitCount, List.filter_append, List.length_append]

/-- A quantum circuit is *two-local* when every gate acts on at most two qubits (`g.arity ≤ 2`),
expressed via `Quantum.Circuit.IsOver`. -/
@[expose]
def TwoLocal {N : ℕ} (C : Quantum.Circuit N) : Prop :=
  C.IsOver {g | g.1 ≤ 2}

/-- A two-qubit gate `U : Quantum.Gate 2` has *Schmidt / bond rank at most two* across wire `0` and
wire `1` when its unitary matrix factors as a sum over a single Boolean bond index `b : Bool`. -/
@[expose]
def HasBondRankTwo (U : Quantum.Gate 2) : Prop :=
  ∃ L R : Bool → Bool → Bool → ℂ,
    ∀ y x : Fin 2 → Bool,
      (U : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) y x =
        ∑ b : Bool, L (x 0) (y 0) b * R (x 1) (y 1) b

/-- A quantum circuit `C` is two-local with every two-qubit gate having bond rank at most two
(for instance arbitrary `U(2)` single-qubit gates together with `CNOT`, `CZ`, and controlled-`V`
gates), expressed via `Quantum.Circuit.IsOver`. -/
@[expose]
def AllBondRankTwo {N : ℕ} (C : Quantum.Circuit N) : Prop :=
  C.IsOver {g | g.1 ≤ 2 ∧ ∀ h : g.1 = 2, HasBondRankTwo (h ▸ g.2)}

/-- `Quantum.Gate.cnot` has bond rank two across its control and target wires. -/
theorem cnot_hasBondRankTwo : HasBondRankTwo Quantum.Gate.cnot := by
  refine ⟨fun x₀ y₀ b => if x₀ = b ∧ y₀ = b then 1 else 0,
    fun x₁ y₁ b => if y₁ = xor x₁ b then 1 else 0, fun y x => ?_⟩
  rw [Fintype.sum_bool]
  simp only [Quantum.Gate.cnot, Quantum.Gate.ofInvolutive, Quantum.Gate.ofPerm_apply]
  change (if y = Function.update x 1 (xor (x 1) (x 0)) then (1 : ℂ) else 0) = _
  have hiff : (y = Function.update x 1 (xor (x 1) (x 0))) ↔
      (y 0 = x 0 ∧ y 1 = xor (x 1) (x 0)) := by
    simp only [funext_iff, Fin.forall_fin_two, Fin.isValue, Function.update_self, ne_eq,
      zero_ne_one, not_false_eq_true, Function.update_of_ne]
  rw [if_congr hiff rfl rfl]
  cases hx0 : x 0 <;> cases hy0 : y 0 <;> cases hx1 : x 1 <;> cases hy1 : y 1 <;> simp

/-- Every controlled single-qubit gate `Quantum.Gate.controlled V` has bond rank at most two. -/
theorem controlled_hasBondRankTwo (V : Quantum.Gate 1) :
    HasBondRankTwo (Quantum.Gate.controlled V) := by
  refine ⟨fun x₀ y₀ b => if x₀ = b ∧ y₀ = b then 1 else 0,
    fun x₁ y₁ b =>
      if b then (V : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (fun _ => y₁) (fun _ => x₁)
      else if y₁ = x₁ then 1 else 0,
    fun y x => ?_⟩
  rw [Quantum.Gate.controlled_apply, Fintype.sum_bool]
  by_cases hx0 : x 0 = true <;> by_cases hy0 : y 0 = true
  · simp [hx0, hy0]
  · simp [hx0, hy0]
  · simp [hx0, hy0]
  · simp only [Bool.not_eq_true] at hx0 hy0
    simp [hx0, hy0]

/-! ### Active-qubit decoupling on `Quantum.Circuit N` -/

section ActiveSplit

/-- Every gate of arity at least `2` in `C` acts only on qubits in `A`. -/
private def TouchingIn {N : ℕ} (A : Set (Fin N)) (C : Quantum.Circuit N) : Prop :=
  ∀ g ∈ C, 2 ≤ g.arity → ∀ i, g.wires i ∈ A

/-- Active gate of arity `0`, `1`, or `2` on a finite wire type `W`. -/
private abbrev ActiveGate (W : Type) :=
  Sigma fun k : Fin 3 => Quantum.Gate k.val × (Fin k.val ↪ W)

/-- Unitary matrix of an `ActiveGate W` on `W → Bool`. -/
private noncomputable def placeAct {W : Type} [Fintype W] [DecidableEq W]
    (g : ActiveGate W) : unitaryGroup (W → Bool) ℂ :=
  ⟨((g.2.1 : Matrix _ _ ℂ) ⊗ₖ
      (1 : Matrix ({q : W // q ∉ Set.range g.2.2} → Bool) _ ℂ)).submatrix
      ((Equiv.piEquivPiSubtypeProd (· ∈ Set.range g.2.2) fun _ => Bool).trans
        (Equiv.prodCongr
          (Equiv.arrowCongr (Equiv.ofInjective g.2.2 g.2.2.injective).symm (Equiv.refl _))
          (Equiv.refl _)))
      ((Equiv.piEquivPiSubtypeProd (· ∈ Set.range g.2.2) fun _ => Bool).trans
        (Equiv.prodCongr
          (Equiv.arrowCongr (Equiv.ofInjective g.2.2 g.2.2.injective).symm (Equiv.refl _))
          (Equiv.refl _))),
    Matrix.submatrix_equiv_mem_unitary.mpr (Matrix.kronecker_mem_unitary g.2.1.2 (one_mem _))⟩

private theorem placeAct_apply {W : Type} [Fintype W] [DecidableEq W]
    (g : ActiveGate W) (y x : W → Bool) :
    (placeAct g : Matrix (W → Bool) (W → Bool) ℂ) y x =
      if ∀ q : W, (¬∃ i, g.2.2 i = q) → y q = x q then
        (g.2.1 : Matrix _ _ ℂ) (y ∘ g.2.2) (x ∘ g.2.2)
      else 0 := by
  have hcomp (z : W → Bool) :
      Equiv.arrowCongr (Equiv.ofInjective g.2.2 g.2.2.injective).symm (Equiv.refl Bool)
        (fun q : Set.range g.2.2 => z q.1) = z ∘ g.2.2 := by
    ext i
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm,
      Equiv.ofInjective_apply, Function.comp_apply]
  change (placeAct g).1 y x = _
  simp only [placeAct, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Equiv.trans_apply,
    Equiv.piEquivPiSubtypeProd_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    Matrix.one_apply]
  rw [hcomp y, hcomp x]
  have hiff : ((fun a : {q // q ∉ Set.range g.2.2} => y a.1) =
      (fun a : {q // q ∉ Set.range g.2.2} => x a.1)) ↔
      ∀ q : W, (¬∃ i, g.2.2 i = q) → y q = x q := by
    simp only [funext_iff, Subtype.forall, Set.mem_range]
  rw [if_congr hiff rfl rfl]
  split_ifs <;> simp

/-- Sequential unitary matrix of a list of active gates, applied first to last. -/
private noncomputable def evalAct {W : Type} [Fintype W] [DecidableEq W] :
    List (ActiveGate W) → unitaryGroup (W → Bool) ℂ
  | [] => 1
  | g :: L => evalAct L * placeAct g

private theorem evalAct_append {W : Type} [Fintype W] [DecidableEq W]
    (L₁ L₂ : List (ActiveGate W)) :
    evalAct (L₁ ++ L₂) = evalAct L₂ * evalAct L₁ := by
  induction L₁ with
  | nil => simp only [List.nil_append, evalAct, mul_one]
  | cons g L₁ ih => simp only [List.cons_append, evalAct, ih, mul_assoc]

open Classical in
/-- **Active-wire decoupling.** Every two-local circuit `C` whose two-qubit gates lie in `A`
tensors into an active unitary `evalAct L` on `↥A → Bool` (with the same two-qubit gate count and
bond-rank-two property) times single-qubit unitaries on `{q // q ∉ A}`. -/
private theorem exists_active_split {N : ℕ} (A : Set (Fin N)) (C : Quantum.Circuit N)
    (htwo : TwoLocal C) (htouch : TouchingIn A C) :
    ∃ (L : List (ActiveGate ↥A)) (inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ),
      (L.filter fun g => decide (g.1.val = 2)).length = twoQubitCount C ∧
      (AllBondRankTwo C → ∀ g ∈ L, ∀ h : g.1.val = 2, HasBondRankTwo (h ▸ g.2.1)) ∧
      ∀ y x : Fin N → Bool,
        (C.matrix : Matrix (Fin N → Bool) (Fin N → Bool) ℂ) y x =
          (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
            ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1) := by
  induction C with
  | nil =>
    refine ⟨[], fun _ => 1, rfl, fun _ g hg => absurd hg (List.not_mem_nil), fun y x => ?_⟩
    simp only [Quantum.Circuit.matrix_nil, evalAct, Submonoid.coe_one, Matrix.one_apply]
    have hsplit : (y = x) ↔
        (A.domRestrict y = A.domRestrict x ∧ ∀ q : {q : Fin N // q ∉ A}, y q.1 = x q.1) := by
      constructor
      · rintro rfl
        exact ⟨rfl, fun _ => rfl⟩
      · rintro ⟨hA, hAc⟩
        ext j
        by_cases hj : j ∈ A
        · exact congrFun hA ⟨j, hj⟩
        · exact hAc ⟨j, hj⟩
    rw [if_congr hsplit rfl rfl]
    by_cases hA : A.domRestrict y = A.domRestrict x
    · simp only [hA, true_and, ↓reduceIte, one_mul]
      by_cases hAc : ∀ q : {q : Fin N // q ∉ A}, y q.1 = x q.1
      · rw [ite_eq_left hAc]
        exact (Finset.prod_eq_one fun q _ => by simp only [hAc q, ↓reduceIte]).symm
      · rw [ite_eq_right hAc]
        push Not at hAc
        obtain ⟨q₀, hq₀⟩ := hAc
        exact (Finset.prod_eq_zero (Finset.mem_univ q₀) (by simp only [hq₀, ↓reduceIte])).symm
    · simp only [hA, false_and, ↓reduceIte, zero_mul]
  | cons g C ih =>
    have htwo_g : g.arity ≤ 2 := htwo g List.mem_cons_self
    have htwo_C : TwoLocal C := fun g' hg' => htwo g' (List.mem_cons_of_mem _ hg')
    have htouch_C : TouchingIn A C := fun g' hg' => htouch g' (List.mem_cons_of_mem _ hg')
    obtain ⟨L, inactU, hlen, hbondL, hmatC⟩ := ih htwo_C htouch_C
    -- Express the single gate `g` as `(L_g, inact_g)` and compose with `(L, inactU)`.
    suffices hstep : ∃ (Lg : List (ActiveGate ↥A))
        (inactG : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ),
        (Lg.filter fun a => decide (a.1.val = 2)).length = (if g.arity = 2 then 1 else 0) ∧
        (AllBondRankTwo (g :: C) → ∀ a ∈ Lg, ∀ h : a.1.val = 2, HasBondRankTwo (h ▸ a.2.1)) ∧
        ∀ z x : Fin N → Bool,
          (g.matrix : Matrix (Fin N → Bool) (Fin N → Bool) ℂ) z x =
            (evalAct Lg : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict z) (A.domRestrict x) *
              ∏ q : {q : Fin N // q ∉ A}, (inactG q : Matrix Bool Bool ℂ) (z q.1) (x q.1) by
      obtain ⟨Lg, inactG, hlenG, hbondG, hmatG⟩ := hstep
      refine ⟨Lg ++ L, fun q => inactU q * inactG q, ?_, ?_, fun y x => ?_⟩
      · rw [List.filter_append, List.length_append, hlenG, hlen, twoQubitCount_cons]
      · intro hbond a ha h2
        rcases List.mem_append.mp ha with haG | haL
        · exact hbondG hbond a haG h2
        · exact hbondL (fun g' hg' => hbond g' (List.mem_cons_of_mem _ hg')) a haL h2
      · rw [Quantum.Circuit.matrix_cons, Submonoid.coe_mul, Matrix.mul_apply]
        simp_rw [hmatC, hmatG]
        have hsum_eq : (∑ z : Fin N → Bool,
            ((evalAct L : Matrix _ _ ℂ) (A.domRestrict y) (A.domRestrict z) *
              ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix _ _ ℂ) (y q.1) (z q.1)) *
            ((evalAct Lg : Matrix _ _ ℂ) (A.domRestrict z) (A.domRestrict x) *
              ∏ q : {q : Fin N // q ∉ A}, (inactG q : Matrix _ _ ℂ) (z q.1) (x q.1))) =
            (∑ zA : ↥A → Bool,
              (evalAct L : Matrix _ _ ℂ) (A.domRestrict y) zA *
                (evalAct Lg : Matrix _ _ ℂ) zA (A.domRestrict x)) *
            ∑ zAc : ↥Aᶜ → Bool,
              ∏ q : {q : Fin N // q ∉ A},
                (inactU q : Matrix _ _ ℂ) (y q.1) (zAc ⟨q.1, q.2⟩) *
                  (inactG q : Matrix _ _ ℂ) (zAc ⟨q.1, q.2⟩) (x q.1) := by
          rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
          refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Bool) _ _
            fun z => ?_
          rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
          rfl
        rw [hsum_eq, evalAct_append, Submonoid.coe_mul, Matrix.mul_apply]
        congr 1
        let eqvAc : (↥Aᶜ → Bool) ≃ ({q : Fin N // q ∉ A} → Bool) :=
          Equiv.arrowCongr
            { toFun := fun q => ⟨q.1, q.2⟩
              invFun := fun q => ⟨q.1, q.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl } (Equiv.refl Bool)
        let fProd (q : {q : Fin N // q ∉ A}) (b : Bool) : ℂ :=
          (inactU q : Matrix Bool Bool ℂ) (y q.1) b * (inactG q : Matrix Bool Bool ℂ) b (x q.1)
        refine (Fintype.sum_equiv eqvAc _ (fun w => ∏ q, fProd q (w q)) fun _ => rfl).trans ?_
        refine (Fintype.prod_sum fProd).symm.trans (Finset.prod_congr rfl fun q _ => ?_)
        simp only [fProd, Submonoid.coe_mul, Matrix.mul_apply]
    -- Case split on whether all wires of `g` lie in `A`.
    by_cases hallA : ∀ i, g.wires i ∈ A
    · let k3 : Fin 3 := ⟨g.arity, by omega⟩
      let wA : Fin k3.val ↪ ↥A :=
        ⟨fun i => ⟨g.wires i, hallA i⟩, fun i j hij => g.wires.injective (congrArg Subtype.val hij)⟩
      let actG : ActiveGate ↥A := ⟨k3, (g.gate, wA)⟩
      refine ⟨[actG], fun _ => 1, ?_, ?_, fun z x => ?_⟩
      · simp only [actG, k3, List.filter_cons, List.filter_nil, decide_eq_true_eq]
        split_ifs <;> rfl
      · intro hbond a ha h2
        rcases List.mem_singleton.mp ha with rfl
        exact (hbond g List.mem_cons_self).2 h2
      · rw [Quantum.PlacedGate.matrix_apply]
        simp only [evalAct, one_mul, placeAct_apply]
        dsimp only [actG]
        have hoff : (∀ j : Fin N, (¬∃ i, g.wires i = j) → z j = x j) ↔
            ((∀ q : ↥A, (¬∃ i, wA i = q) → A.domRestrict z q = A.domRestrict x q) ∧
              ∀ q : {q : Fin N // q ∉ A}, z q.1 = x q.1) := by
          constructor
          · intro h
            refine ⟨fun q hq => h q.1 fun ⟨i, hi⟩ => hq ⟨i, Subtype.ext hi⟩,
              fun q => h q.1 fun ⟨i, hi⟩ => q.2 (hi ▸ hallA i)⟩
          · rintro ⟨hA, hAc⟩ j hj
            by_cases hjA : j ∈ A
            · exact hA ⟨j, hjA⟩ fun ⟨i, hi⟩ => hj ⟨i, congrArg Subtype.val hi⟩
            · exact hAc ⟨j, hjA⟩
        rw [if_congr hoff rfl rfl]
        by_cases hA_cond : ∀ q : ↥A, (¬∃ i, wA i = q) → A.domRestrict z q = A.domRestrict x q
        · rw [ite_eq_left hA_cond]
          by_cases hAc : ∀ q : {q : Fin N // q ∉ A}, z q.1 = x q.1
          · rw [ite_eq_left ⟨hA_cond, hAc⟩]
            have hprod1 : (∏ q : {q : Fin N // q ∉ A},
                ((1 : unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) (z q.1) (x q.1)) = 1 :=
              Finset.prod_eq_one fun q _ => by
                simp only [Submonoid.coe_one, Matrix.one_apply, hAc q, ↓reduceIte]
            rw [hprod1, mul_one]
            rfl
          · rw [ite_eq_right (fun h => hAc h.2)]
            push Not at hAc
            obtain ⟨q₀, hq₀⟩ := hAc
            have hprod0 : (∏ q : {q : Fin N // q ∉ A},
                ((1 : unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) (z q.1) (x q.1)) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ q₀)
                (by simp only [Submonoid.coe_one, Matrix.one_apply, hq₀, ↓reduceIte])
            rw [hprod0, mul_zero]
        · rw [ite_eq_right (fun h => hA_cond h.1), ite_eq_right hA_cond, zero_mul]
    · -- Not all wires of `g` lie in `A`: since `TouchingIn A (g :: C)` and `g.arity ≤ 2`,
      -- we must have `g.arity = 1` and its single wire `q₀ ∉ A`!
      have har1 : g.arity = 1 := by
        rcases (by omega : g.arity = 0 ∨ g.arity = 1 ∨ g.arity = 2) with h0 | h1 | h2
        · exfalso; apply hallA; intro i; exact absurd i.isLt (by omega)
        · exact h1
        · exfalso; exact hallA (htouch g List.mem_cons_self (by omega))
      rcases g with ⟨arity, gate, wires⟩
      dsimp only at har1 hallA
      subst har1
      have hq₀_notA : wires 0 ∉ A := fun h => hallA fun i => by rw [Fin.eq_zero i]; exact h
      let q₀ : {q : Fin N // q ∉ A} := ⟨wires 0, hq₀_notA⟩
      let u1 : unitaryGroup Bool ℂ :=
        ⟨(gate : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ).submatrix
            (Equiv.funUnique (Fin 1) Bool).symm (Equiv.funUnique (Fin 1) Bool).symm,
          Matrix.submatrix_equiv_mem_unitary.mpr gate.2⟩
      refine ⟨[], fun q => if q = q₀ then u1 else 1, by simp,
        fun _ a ha => absurd ha List.not_mem_nil, fun z x => ?_⟩
      rw [Quantum.PlacedGate.matrix_apply]
      simp only [evalAct, Submonoid.coe_one, Matrix.one_apply]
      have hoff : (∀ j : Fin N, (¬∃ i : Fin 1, wires i = j) → z j = x j) ↔
          (A.domRestrict z = A.domRestrict x ∧
            ∀ q : {q : Fin N // q ∉ A}, q ≠ q₀ → z q.1 = x q.1) := by
        constructor
        · intro h
          refine ⟨funext fun q => h q.1 fun ⟨i, hi⟩ =>
            hq₀_notA (by rw [← Fin.eq_zero i, hi]; exact q.2),
            fun q hq => h q.1 fun ⟨i, hi⟩ =>
              hq (Subtype.ext (by rw [← hi, Fin.eq_zero i]))⟩
        · rintro ⟨hA, hAc⟩ j hj
          by_cases hjA : j ∈ A
          · exact congrFun hA ⟨j, hjA⟩
          · exact hAc ⟨j, hjA⟩ fun h => hj ⟨0, congrArg Subtype.val h.symm⟩
      rw [if_congr hoff rfl rfl]
      by_cases hA_eq : A.domRestrict z = A.domRestrict x
      · rw [ite_eq_left hA_eq, one_mul]
        by_cases hAc_eq : ∀ q : {q : Fin N // q ∉ A}, q ≠ q₀ → z q.1 = x q.1
        · rw [ite_eq_left ⟨hA_eq, hAc_eq⟩]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
          have hrest : (∏ q ∈ Finset.univ.erase q₀,
              ((if q = q₀ then u1 else 1 : unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ)
                (z q.1) (x q.1)) = 1 := by
            refine Finset.prod_eq_one fun q hq => ?_
            have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
            simp only [hne, ↓reduceIte, Submonoid.coe_one, Matrix.one_apply, hAc_eq q hne]
          rw [hrest, mul_one]
          simp only [↓reduceIte, u1]
          change (gate : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (z ∘ wires) (x ∘ wires) =
            (gate : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ)
              (fun _ => z (wires 0)) (fun _ => x (wires 0))
          have hz0 : z ∘ wires = fun _ => z (wires 0) :=
            funext fun i => by rw [Function.comp_apply, Fin.eq_zero i]
          have hx0 : x ∘ wires = fun _ => x (wires 0) :=
            funext fun i => by rw [Function.comp_apply, Fin.eq_zero i]
          exact congrArg₂ _ hz0 hx0
        · rw [ite_eq_right (fun h => hAc_eq h.2)]
          push Not at hAc_eq
          obtain ⟨q₁, hq₁_ne, hq₁_diff⟩ := hAc_eq
          symm
          refine Finset.prod_eq_zero (Finset.mem_univ q₁) ?_
          simp only [hq₁_ne, ↓reduceIte, Submonoid.coe_one, Matrix.one_apply, hq₁_diff]
      · simp only [hA_eq, false_and, ↓reduceIte, zero_mul]

/-- The active qubit set of `C` together with embedded data qubits `e : Fin n ↪ Fin N` and an
optional output qubit `q_extra : Fin N`. -/
private def activeSet {n N : ℕ} (e : Fin n ↪ Fin N) (q_extra : Fin N) (C : Quantum.Circuit N) :
    Set (Fin N) :=
  insert q_extra (Set.range e ∪ {q | ∃ g ∈ C, 2 ≤ g.arity ∧ ∃ i, g.wires i = q})

private theorem range_subset_activeSet {n N : ℕ} (e : Fin n ↪ Fin N) (q_extra : Fin N)
    (C : Quantum.Circuit N) : Set.range e ⊆ activeSet e q_extra C :=
  fun _ hx => Set.mem_insert_of_mem _ (Or.inl hx)

private theorem mem_activeSet_extra {n N : ℕ} (e : Fin n ↪ Fin N) (q_extra : Fin N)
    (C : Quantum.Circuit N) : q_extra ∈ activeSet e q_extra C :=
  Set.mem_insert _ _

private theorem touchingIn_activeSet {n N : ℕ} (e : Fin n ↪ Fin N) (q_extra : Fin N)
    (C : Quantum.Circuit N) : TouchingIn (activeSet e q_extra C) C :=
  fun g hg h2 i => Set.mem_insert_of_mem _ (Or.inr ⟨g, hg, h2, i, rfl⟩)

private theorem ncard_activeSet_le {n N : ℕ} (e : Fin n ↪ Fin N) (q_extra : Fin N)
    {C : Quantum.Circuit N} (htwo : TwoLocal C) :
    (activeSet e q_extra C).ncard ≤ n + 2 * twoQubitCount C + 1 := by
  have hgate : {q : Fin N | ∃ g ∈ C, 2 ≤ g.arity ∧ ∃ i, g.wires i = q}.ncard ≤
      2 * twoQubitCount C := by
    induction C with
    | nil => simp
    | cons g C ih =>
      have hg_le : g.arity ≤ 2 := htwo g List.mem_cons_self
      have hC_two : TwoLocal C := fun g' hg' => htwo g' (List.mem_cons_of_mem _ hg')
      have hsub : {q : Fin N | ∃ g' ∈ g :: C, 2 ≤ g'.arity ∧ ∃ i, g'.wires i = q} ⊆
          {q : Fin N | 2 ≤ g.arity ∧ ∃ i, g.wires i = q} ∪
            {q : Fin N | ∃ g' ∈ C, 2 ≤ g'.arity ∧ ∃ i, g'.wires i = q} := by
        rintro q ⟨g', hg', h2, i, rfl⟩
        rcases List.mem_cons.mp hg' with rfl | hmem
        · exact Or.inl ⟨h2, i, rfl⟩
        · exact Or.inr ⟨g', hmem, h2, i, rfl⟩
      have hhead : {q : Fin N | 2 ≤ g.arity ∧ ∃ i, g.wires i = q}.ncard ≤
          2 * (if g.arity = 2 then 1 else 0) := by
        by_cases h2 : g.arity = 2
        · simp only [h2, le_refl, true_and, ↓reduceIte, mul_one]
          change (Set.range g.wires).ncard ≤ 2
          rw [ncard_range_of_injective g.wires.injective, Nat.card_eq_fintype_card,
            Fintype.card_fin, h2]
        · have hnot2 : ¬(2 ≤ g.arity) := by omega
          have hempty : {q : Fin N | 2 ≤ g.arity ∧ ∃ i, g.wires i = q} = ∅ := by
            ext q; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
            exact fun h => absurd h hnot2
          simp only [hempty, ncard_empty, h2, ↓reduceIte, mul_zero, le_refl]
      calc {q : Fin N | ∃ g' ∈ g :: C, 2 ≤ g'.arity ∧ ∃ i, g'.wires i = q}.ncard
          ≤ ({q : Fin N | 2 ≤ g.arity ∧ ∃ i, g.wires i = q} ∪
              {q : Fin N | ∃ g' ∈ C, 2 ≤ g'.arity ∧ ∃ i, g'.wires i = q}).ncard :=
            ncard_le_ncard hsub (toFinite _)
        _ ≤ {q : Fin N | 2 ≤ g.arity ∧ ∃ i, g.wires i = q}.ncard +
              {q : Fin N | ∃ g' ∈ C, 2 ≤ g'.arity ∧ ∃ i, g'.wires i = q}.ncard :=
            ncard_union_le _ _
        _ ≤ 2 * (if g.arity = 2 then 1 else 0) + 2 * twoQubitCount C :=
            Nat.add_le_add hhead (ih hC_two)
        _ = 2 * twoQubitCount (g :: C) := by rw [twoQubitCount_cons, mul_add]
  have hrange : (Set.range e).ncard = n := by
    rw [ncard_range_of_injective e.injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  calc (activeSet e q_extra C).ncard
      ≤ (Set.range e ∪ {q | ∃ g ∈ C, 2 ≤ g.arity ∧ ∃ i, g.wires i = q}).ncard + 1 :=
        ncard_insert_le _ _
    _ ≤ ((Set.range e).ncard + {q | ∃ g ∈ C, 2 ≤ g.arity ∧ ∃ i, g.wires i = q}.ncard) + 1 :=
        Nat.add_le_add_right (ncard_union_le _ _) 1
    _ ≤ n + 2 * twoQubitCount C + 1 := by omega

end ActiveSplit

/-! ### Wire-segment tensor network compilation (`d = 3` and `d = 4`) -/

section WireNetwork

private theorem reachable_map_inl {V V' E E' : Type} {G : Multigraph V E}
    {G' : Multigraph V' E'} (f : V ↪ V')
    (hedges : ∀ e : E, ∃ e' : E', G'.ends e' = Sym2.map f (G.ends e))
    {u w : V} (hr : G.toSimpleGraph.Reachable u w) :
    G'.toSimpleGraph.Reachable (f u) (f w) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab _ ih =>
    obtain ⟨hab_ne, e₀, he₀⟩ := Multigraph.toSimpleGraph_adj.mp hab
    obtain ⟨e', he'⟩ := hedges e₀
    refine (Multigraph.toSimpleGraph_adj.mpr
      ⟨fun h => hab_ne (f.injective h), e', ?_⟩).reachable.trans ih
    rw [he', he₀]
    rfl

private theorem mem_closed_iff_of_reachable {V E : Type} {G : Multigraph V E}
    {Comp : Set V} (hcut : G.edgeCut Comp = ∅) {u w : V}
    (hr : G.toSimpleGraph.Reachable u w) : u ∈ Comp ↔ w ∈ Comp := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Iff.rfl
  | @cons a b c hab _ ih =>
    obtain ⟨_, e, hends⟩ := Multigraph.toSimpleGraph_adj.mp hab
    have hce := G.edgeCut_eq_empty_iff.mp hcut e
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (h1 ▸ h2 ▸ hce).trans ih
    · exact (h1 ▸ h2 ▸ hce.symm).trans ih

/-- Capped multigraph obtained by joining each wire `q : W`'s current `tip q : V` to a degree-one
output leaf `.inr q : V ⊕ W` via edge `.inr q : E ⊕ W`. -/
private def capGraph {V E W : Type} (G : Multigraph V E) (tip : W → V) :
    Multigraph (V ⊕ W) (E ⊕ W) where
  src
    | .inl e => .inl (G.src e)
    | .inr q => .inl (tip q)
  tgt
    | .inl e => .inl (G.tgt e)
    | .inr q => .inr q

private theorem capGraph_loopless {V E W : Type} {G : Multigraph V E} (hG : G.Loopless)
    (tip : W → V) : (capGraph G tip).Loopless := by
  rintro (e | q)
  · exact fun h => hG e (Sum.inl.inj h)
  · exact Sum.inl_ne_inr

private theorem capGraph_incidence_inr {V E W : Type} (G : Multigraph V E) (tip : W → V)
    (q : W) : (capGraph G tip).incidenceSet (.inr q) = {.inr q} := by
  ext (e | q')
  · simp [Multigraph.mem_incidenceSet, capGraph]
  · simp [Multigraph.mem_incidenceSet, capGraph, eq_comm]

/-- Compiled capped wire-segment tensor network for an active unitary `M : Matrix (W → Bool) _ ℂ`
using `s` two-qubit gates and maximum degree `d` (`d = 3` or `d = 4`). -/
private structure CappedWireNet (d : ℕ) (W : Type) [Fintype W]
    (M : Matrix (W → Bool) (W → Bool) ℂ) (s : ℕ) : Prop where
  exists_net :
    ∃ (V_fin E_fin : Type) (_ : Fintype V_fin) (_ : DecidableEq V_fin)
      (_ : Fintype E_fin) (_ : DecidableEq E_fin)
      (G : Multigraph V_fin E_fin) (inVert outVert : W ↪ V_fin)
      (F : V_fin → (W → Bool) → (W → Bool) → (E_fin → Bool) → ℂ),
      G.Loopless ∧
      G.MaxDegreeLE d ∧
      Disjoint (Set.range inVert) (Set.range outVert) ∧
      (∀ q : W, (G.incidenceSet (inVert q)).ncard = 1 ∧ (G.incidenceSet (outVert q)).ncard = 1) ∧
      (∀ q : W, G.toSimpleGraph.Reachable (inVert q) (outVert q)) ∧
      Fintype.card V_fin ≤ 2 * Fintype.card W + 2 * s ∧
      (∀ Comp : Set V_fin, G.edgeCut Comp = ∅ → Comp.ncard ≤ (G.touching Comp).ncard + 1 →
        G.cycleRankOn Comp + {q : W | inVert q ∈ Comp}.ncard ≤ s + 1) ∧
      (∀ y x : W → Bool, M y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ) ∧
      (∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ) ∧
      (∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ) ∧
      (∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)

/-- Inductive open state before capping output leaves. -/
private structure OpenState (d : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (M : Matrix (W → Bool) (W → Bool) ℂ) (s : ℕ) where
  V : Type
  E : Type
  instFV : Fintype V
  instDV : DecidableEq V
  instFE : Fintype E
  instDE : DecidableEq E
  G : Multigraph V E
  inVert : W ↪ V
  tip : W → V
  scalar : ℂ
  tipMat : W → Matrix Bool Bool ℂ
  openF : V → (W → Bool) → (E ⊕ W → Bool) → ℂ
  loopless : G.Loopless
  deg_inVert : ∀ q : W, ((capGraph G tip).incidenceSet (.inl (inVert q))).ncard = 1
  deg_gate : ∀ v : V, v ∉ Set.range inVert → ((capGraph G tip).incidenceSet (.inl v)).ncard = d
  reach_tip : ∀ q : W, G.toSimpleGraph.Reachable (inVert q) (tip q)
  card_V : (d - 2) * (Fintype.card V - Fintype.card W) = 2 * s ∧ Fintype.card W ≤ Fintype.card V
  contract : ∀ y x : W → Bool,
    M y x = scalar * ∑ γ : E ⊕ W → Bool,
      (∏ v : V, openF v x γ) * ∏ q : W, tipMat q (y q) (γ (.inr q))
  loc_in : ∀ v x₁ x₂ γ, (∀ q, inVert q = v → x₁ q = x₂ q) → openF v x₁ γ = openF v x₂ γ
  loc_edge : ∀ v x γ₁ γ₂, Set.EqOn γ₁ γ₂ ((capGraph G tip).incidenceSet (.inl v)) →
    openF v x γ₁ = openF v x γ₂

attribute [instance] OpenState.instFV OpenState.instDV OpenState.instFE OpenState.instDE

/-- Helper: reindexing incident edges at `.inl u` along an injection `emb : E ⊕ W ↪ E' ⊕ W` that
bijects `(capGraph G tip).incidenceSet (.inl u)` onto
`(capGraph G' tip').incidenceSet (.inl (fV u))` preserves `.ncard`. -/
private theorem ncard_incidence_eq_of_bij {V V' E E' W : Type}
    (G : Multigraph V E) (tip : W → V) (G' : Multigraph V' E') (tip' : W → V')
    (fV : V → V') (emb : E ⊕ W ↪ E' ⊕ W) (u : V)
    (hmap : ∀ e, e ∈ (capGraph G tip).incidenceSet (.inl u) ↔
      emb e ∈ (capGraph G' tip').incidenceSet (.inl (fV u)))
    (hsurj : ∀ e' ∈ (capGraph G' tip').incidenceSet (.inl (fV u)), ∃ e, emb e = e') :
    ((capGraph G' tip').incidenceSet (.inl (fV u))).ncard =
      ((capGraph G tip).incidenceSet (.inl u)).ncard := by
  have himg : (capGraph G' tip').incidenceSet (.inl (fV u)) =
      emb '' (capGraph G tip).incidenceSet (.inl u) := by
    ext e'
    constructor
    · intro he'
      obtain ⟨e, rfl⟩ := hsurj e' he'
      exact ⟨e, (hmap e).mpr he', rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact (hmap e).mp he
  rw [himg, ncard_image_of_injective _ emb.injective]

/-- Base open state for `[] : List (ActiveGate W)`. -/
private noncomputable def openStateNil (d : ℕ) (W : Type) [Fintype W] [DecidableEq W] :
    OpenState d W (1 : Matrix (W → Bool) (W → Bool) ℂ) 0 where
  V := W
  E := Empty
  instFV := inferInstance
  instDV := inferInstance
  instFE := inferInstance
  instDE := inferInstance
  G := { src := Empty.elim, tgt := Empty.elim }
  inVert := Function.Embedding.refl W
  tip := id
  scalar := 1
  tipMat := fun _ => 1
  openF := fun v x γ => if γ (.inr v) = x v then 1 else 0
  loopless := fun e => Empty.elim e
  deg_inVert := fun q => by
    have hset : (capGraph { src := Empty.elim, tgt := Empty.elim } id).incidenceSet (.inl q) =
        {(.inr q : Empty ⊕ W)} := by
      ext (e | q')
      · exact Empty.elim e
      · simp [Multigraph.mem_incidenceSet, capGraph, eq_comm]
    change ((capGraph { src := Empty.elim, tgt := Empty.elim } id).incidenceSet (.inl q)).ncard = 1
    rw [hset, ncard_singleton]
  deg_gate := fun v hv => absurd ⟨v, rfl⟩ hv
  reach_tip := fun _ => SimpleGraph.Reachable.refl _
  card_V := ⟨by simp, le_rfl⟩
  contract := fun y x => by
    rw [one_mul, Matrix.one_apply]
    let eqv : (Empty ⊕ W → Bool) ≃ (W → Bool) :=
      { toFun := fun γ q => γ (.inr q)
        invFun := fun z s => match s with | .inl e => Empty.elim e | .inr q => z q
        left_inv := fun γ => by
          ext (e | q)
          · exact Empty.elim e
          · rfl
        right_inv := fun z => rfl }
    have hsum : (∑ γ : Empty ⊕ W → Bool,
        (∏ v : W, if γ (.inr v) = x v then (1 : ℂ) else 0) *
          ∏ q : W, (1 : Matrix Bool Bool ℂ) (y q) (γ (.inr q))) =
        ∑ z : W → Bool,
          (∏ v : W, if z v = x v then (1 : ℂ) else 0) *
            ∏ q : W, (1 : Matrix Bool Bool ℂ) (y q) (z q) :=
      Fintype.sum_equiv eqv _ _ fun _ => rfl
    rw [hsum]
    have hterm (z : W → Bool) :
        (∏ v : W, if z v = x v then (1 : ℂ) else 0) *
          (∏ q : W, (1 : Matrix Bool Bool ℂ) (y q) (z q)) =
          if z = x then (if y = x then 1 else 0) else 0 := by
      by_cases hzx : z = x
      · subst hzx
        simp only [↓reduceIte, Finset.prod_const_one, one_mul, Matrix.one_apply]
        by_cases hyz : y = z
        · subst hyz
          simp only [↓reduceIte, Finset.prod_const_one]
        · simp only [hyz, ↓reduceIte]
          have ⟨q₀, hq₀⟩ : ∃ q, y q ≠ z q := Function.ne_iff.mp hyz
          exact Finset.prod_eq_zero (Finset.mem_univ q₀) (by simp only [hq₀, ↓reduceIte])
      · simp only [hzx, ↓reduceIte]
        have ⟨v₀, hv₀⟩ : ∃ v, z v ≠ x v := Function.ne_iff.mp hzx
        rw [Finset.prod_eq_zero (Finset.mem_univ v₀) (by simp only [hv₀, ↓reduceIte]), zero_mul]
    simp_rw [hterm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  loc_in := fun v x₁ x₂ γ h => by rw [h v rfl]
  loc_edge := fun v x γ₁ γ₂ h => by
    have hmem : (.inr v : Empty ⊕ W) ∈
        (capGraph { src := Empty.elim, tgt := Empty.elim } id).incidenceSet (.inl v) :=
      Or.inl rfl
    rw [h hmem]

/-- Step for a `0`-qubit global phase gate. -/
private noncomputable def openStateZero {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    (g : ActiveGate W) (h0 : g.1.val = 0) :
    OpenState d W ((placeAct g : Matrix _ _ ℂ) * M) s :=
  let c₀ : ℂ :=
    (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
      (fun i => absurd i.isLt (by omega)) (fun i => absurd i.isLt (by omega))
  { S with
    scalar := c₀ * S.scalar
    contract := fun y x => by
      rw [Matrix.mul_apply]
      have hplace (z : W → Bool) :
          (placeAct g : Matrix _ _ ℂ) y z = if y = z then c₀ else 0 := by
        rw [placeAct_apply]
        have hno : ∀ q : W, ¬∃ i : Fin g.1.val, g.2.2 i = q :=
          fun _ ⟨i, _⟩ => absurd i.isLt (by omega)
        have hiff : (∀ q : W, (¬∃ i, g.2.2 i = q) → y q = z q) ↔ y = z :=
          ⟨fun h => funext fun q => h q (hno q), fun h q _ => congrFun h q⟩
        rw [if_congr hiff rfl rfl]
        by_cases hyz : y = z
        · subst hyz
          simp only [↓reduceIte]
          have harg : (y ∘ g.2.2) = fun i : Fin g.1.val => absurd i.isLt (by omega) :=
            funext fun i => absurd i.isLt (by omega)
          rw [harg]
        · simp only [hyz, ↓reduceIte]
      simp_rw [hplace, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [S.contract y x, mul_assoc] }

/-- Step for a `1`-qubit gate on `W` (graph unchanged, absorbed into `tipMat`). -/
private noncomputable def openStateOne {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    (g : ActiveGate W) (h1 : g.1.val = 1) :
    OpenState d W ((placeAct g : Matrix _ _ ℂ) * M) s :=
  let i₀ : Fin g.1.val := ⟨0, by omega⟩
  let q₀ : W := g.2.2 i₀
  let gMat : Matrix Bool Bool ℂ :=
    Matrix.of fun b c =>
      (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ) (fun _ => b) (fun _ => c)
  { S with
    tipMat := fun q => if q = q₀ then gMat * S.tipMat q₀ else S.tipMat q
    contract := fun y x => by
      rw [Matrix.mul_apply]
      have hplace (z : W → Bool) :
          (placeAct g : Matrix _ _ ℂ) y z =
            if ∀ q ≠ q₀, y q = z q then gMat (y q₀) (z q₀) else 0 := by
        rw [placeAct_apply]
        have hiff : (∀ q : W, (¬∃ i, g.2.2 i = q) → y q = z q) ↔ ∀ q ≠ q₀, y q = z q := by
          refine forall_congr' fun q => imp_congr_left
            ⟨fun h hq => h ⟨i₀, hq.symm⟩, fun h ⟨i, hi⟩ => h ?_⟩
          rw [← hi]; congr 1; ext; omega
        rw [if_congr hiff rfl rfl]
        split_ifs with h
        · have hy_eq : (y ∘ g.2.2) = fun _ : Fin g.1.val => y q₀ :=
            funext fun i => (show i = i₀ by ext; omega) ▸ rfl
          have hz_eq : (z ∘ g.2.2) = fun _ : Fin g.1.val => z q₀ :=
            funext fun i => (show i = i₀ by ext; omega) ▸ rfl
          rw [hy_eq, hz_eq]
          rfl
        · rfl
      have hsum_z : (∑ z : W → Bool, (placeAct g : Matrix _ _ ℂ) y z * M z x) =
          ∑ b : Bool, gMat (y q₀) b * M (Function.update y q₀ b) x := by
        simp_rw [hplace, ite_mul, zero_mul]
        have hfib (z : W → Bool) :
            (∀ q ≠ q₀, y q = z q) ↔ ∃ b : Bool, z = Function.update y q₀ b := by
          constructor
          · intro hz
            refine ⟨z q₀, funext fun q => ?_⟩
            by_cases hq : q = q₀
            · subst hq; simp only [Function.update_self]
            · simp only [ne_eq, hq, not_false_eq_true, Function.update_of_ne, (hz q hq).symm]
          · rintro ⟨b, rfl⟩ q hq
            simp only [ne_eq, hq, not_false_eq_true, Function.update_of_ne]
        let fupd (b : Bool) : W → Bool := Function.update y q₀ b
        have hfupd_inj : Function.Injective fupd := fun b₁ b₂ h => by
          simpa [fupd] using congrFun h q₀
        have hfilt : (Finset.univ.filter fun z : W → Bool => ∀ q ≠ q₀, y q = z q) =
            Finset.univ.image fupd := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfib, Finset.mem_image]
          exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
        rw [← Finset.sum_filter, hfilt, Finset.sum_image (fun _ _ _ _ h => hfupd_inj h)]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [fupd, Function.update_self]
      rw [hsum_z]
      have hstep1 : (∑ b : Bool, gMat (y q₀) b * M (Function.update y q₀ b) x) =
          S.scalar * ∑ b : Bool, ∑ γ : S.E ⊕ W → Bool,
            gMat (y q₀) b *
              ((∏ v : S.V, S.openF v x γ) *
                ∏ q : W, S.tipMat q (Function.update y q₀ b q) (γ (.inr q))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [S.contract (Function.update y q₀ b) x, ← mul_assoc, mul_comm (gMat (y q₀) b) S.scalar,
          mul_assoc, Finset.mul_sum]
      rw [hstep1, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun γ _ => ?_
      have hprod_upd (b : Bool) :
          (∏ q : W, S.tipMat q (Function.update y q₀ b q) (γ (.inr q))) =
            S.tipMat q₀ b (γ (.inr q₀)) *
              ∏ q ∈ Finset.univ.erase q₀, S.tipMat q (y q) (γ (.inr q)) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [Function.update_of_ne (Finset.mem_erase.mp hq).1]
      have hprod_new :
          (∏ q : W, (if q = q₀ then gMat * S.tipMat q₀ else S.tipMat q) (y q) (γ (.inr q))) =
            (gMat * S.tipMat q₀) (y q₀) (γ (.inr q₀)) *
              ∏ q ∈ Finset.univ.erase q₀, S.tipMat q (y q) (γ (.inr q)) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
        simp only [↓reduceIte]
        congr 1
        refine Finset.prod_congr rfl fun q hq => ?_
        simp only [(Finset.mem_erase.mp hq).1, ↓reduceIte]
      rw [hprod_new, Matrix.mul_apply, Fintype.sum_bool]
      simp_rw [hprod_upd]
      rw [Fintype.sum_bool]
      ring }

/-- Step for a general `2`-qubit gate in degree `d = 4` (adds `Unit` vertex and `Bool` edges). -/
private noncomputable def openStateTwoDegFour {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState 4 W M s)
    (g : ActiveGate W) (h2 : g.1.val = 2) :
    OpenState 4 W ((placeAct g : Matrix _ _ ℂ) * M) (s + 1) := by
  let i₀ : Fin g.1.val := ⟨0, by omega⟩
  let i₁ : Fin g.1.val := ⟨1, by omega⟩
  have hi_ne : i₀ ≠ i₁ := fun h => by
    have hv := congrArg Fin.val h
    dsimp only [i₀, i₁] at hv
    omega
  let q₀ : W := g.2.2 i₀
  let q₁ : W := g.2.2 i₁
  have hq_ne : q₀ ≠ q₁ := fun h => hi_ne (g.2.2.injective h)
  let G' : Multigraph (S.V ⊕ Unit) (S.E ⊕ Bool) :=
    { src := fun e => match e with
        | .inl e₀ => .inl (S.G.src e₀)
        | .inr false => .inl (S.tip q₀)
        | .inr true => .inl (S.tip q₁)
      tgt := fun e => match e with
        | .inl e₀ => .inl (S.G.tgt e₀)
        | .inr _ => .inr () }
  let tip' : W → S.V ⊕ Unit := fun q => if q = q₀ ∨ q = q₁ then .inr () else .inl (S.tip q)
  let oldEdgeFun : S.E ⊕ W → (S.E ⊕ Bool) ⊕ W := fun e => match e with
    | .inl e₀ => .inl (.inl e₀)
    | .inr q =>
      if q = q₀ then .inl (.inr false)
      else if q = q₁ then .inl (.inr true)
      else .inr q
  have hold_inj : Function.Injective oldEdgeFun := fun a b hab => by
    cases a with
    | inl ea =>
      cases b with
      | inl eb => exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj hab))
      | inr qb => dsimp only [oldEdgeFun] at hab; split_ifs at hab <;> simp at hab
    | inr qa =>
      cases b with
      | inl eb => dsimp only [oldEdgeFun] at hab; split_ifs at hab <;> simp at hab
      | inr qb => dsimp only [oldEdgeFun] at hab; split_ifs at hab <;> simp_all
  let oldEdge : S.E ⊕ W ↪ (S.E ⊕ Bool) ⊕ W := ⟨oldEdgeFun, hold_inj⟩
  have hmap_u (u : S.V) (e : S.E ⊕ W) :
      e ∈ (capGraph S.G S.tip).incidenceSet (.inl u) ↔
        oldEdge e ∈ (capGraph G' tip').incidenceSet (.inl (.inl u)) := by
    change _ ↔ oldEdgeFun e ∈ _
    cases e with
    | inl e₀ =>
      simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, G']
    | inr q =>
      by_cases hq0 : q = q₀
      · subst hq0; simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, G']
      · by_cases hq1 : q = q₁
        · subst hq1; simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, hq0, G']
        · simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, hq0, hq1, tip']
  have hsurj_u (u : S.V) (e' : (S.E ⊕ Bool) ⊕ W)
      (he' : e' ∈ (capGraph G' tip').incidenceSet (.inl (.inl u))) :
      ∃ e, oldEdge e = e' := by
    change ∃ e, oldEdgeFun e = e'
    rcases e' with (e₀ | b) | q
    · exact ⟨.inl e₀, rfl⟩
    · cases b
      · exact ⟨.inr q₀, by simp [oldEdgeFun]⟩
      · exact ⟨.inr q₁, by simp [oldEdgeFun, hq_ne.symm]⟩
    · by_cases hq : q = q₀ ∨ q = q₁
      · simp [Multigraph.mem_incidenceSet, capGraph, tip', hq] at he'
      · push Not at hq
        exact ⟨.inr q, by simp [oldEdgeFun, hq.1, hq.2]⟩
  let g2Mat (a₀ a₁ b₀ b₁ : Bool) : ℂ :=
    (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
      (fun i => if i = i₀ then a₀ else a₁)
      (fun i => if i = i₀ then b₀ else b₁)
  let gateTensor (γ' : (S.E ⊕ Bool) ⊕ W → Bool) : ℂ :=
    ∑ z₀ : Bool, ∑ z₁ : Bool,
      g2Mat (γ' (.inr q₀)) (γ' (.inr q₁)) z₀ z₁ *
        S.tipMat q₀ z₀ (γ' (.inl (.inr false))) *
        S.tipMat q₁ z₁ (γ' (.inl (.inr true)))
  exact
    { V := S.V ⊕ Unit
      E := S.E ⊕ Bool
      instFV := inferInstance
      instDV := inferInstance
      instFE := inferInstance
      instDE := inferInstance
      G := G'
      inVert := S.inVert.trans ⟨Sum.inl, Sum.inl_injective⟩
      tip := tip'
      scalar := S.scalar
      tipMat := fun q => if q = q₀ ∨ q = q₁ then 1 else S.tipMat q
      openF := fun v x γ' => match v with
        | .inl u => S.openF u x (γ' ∘ oldEdge)
        | .inr () => gateTensor γ'
      loopless := by
        rintro (e₀ | b)
        · exact fun h => S.loopless e₀ (Sum.inl.inj h)
        · cases b <;> exact Sum.inl_ne_inr
      deg_inVert := fun q =>
        (ncard_incidence_eq_of_bij S.G S.tip G' tip' Sum.inl oldEdge (S.inVert q)
          (hmap_u _) (hsurj_u _)).trans (S.deg_inVert q)
      deg_gate := by
        rintro (u | ⟨⟩) hv
        · have hu : u ∉ Set.range S.inVert := fun ⟨q, hq⟩ => hv ⟨q, congrArg Sum.inl hq⟩
          exact (ncard_incidence_eq_of_bij S.G S.tip G' tip' Sum.inl oldEdge u
            (hmap_u u) (hsurj_u u)).trans (S.deg_gate u hu)
        · have hset : (capGraph G' tip').incidenceSet (.inl (.inr ())) =
              {.inl (.inr false), .inl (.inr true), .inr q₀, .inr q₁} := by
            ext ((e₀ | b) | q)
            · simp [Multigraph.mem_incidenceSet, capGraph, G']
            · cases b <;> simp [Multigraph.mem_incidenceSet, capGraph, G']
            · by_cases hq : q = q₀ ∨ q = q₁ <;>
                simp [Multigraph.mem_incidenceSet, capGraph, tip', hq]
          rw [hset, ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_insert_of_notMem,
            ncard_singleton]
          · simp only [mem_singleton_iff, Sum.inr.injEq]; exact hq_ne
          · simp [mem_insert_iff, mem_singleton_iff]
          · simp [mem_insert_iff, mem_singleton_iff]
      reach_tip := fun q => by
        have hprev : G'.toSimpleGraph.Reachable (.inl (S.inVert q)) (.inl (S.tip q)) :=
          reachable_map_inl ⟨Sum.inl, Sum.inl_injective⟩
            (fun e₀ => ⟨.inl e₀, by simp [Multigraph.ends, G']⟩) (S.reach_tip q)
        by_cases hq : q = q₀ ∨ q = q₁
        · simp only [tip', hq, ↓reduceIte]
          rcases hq with rfl | rfl
          · exact hprev.trans (G'.reachable_src_tgt (.inr false))
          · exact hprev.trans (G'.reachable_src_tgt (.inr true))
        · simp only [tip', hq, ↓reduceIte]
          exact hprev
      card_V := by
        rw [Fintype.card_sum, Fintype.card_unit]
        obtain ⟨hc1, hc2⟩ := S.card_V
        exact ⟨by omega, by omega⟩
      contract := fun y x => by
        let eqvFun : ((S.E ⊕ Bool) ⊕ W → Bool) ≃ (S.E ⊕ W → Bool) × (Bool × Bool) :=
          { toFun := fun γ' => (γ' ∘ oldEdgeFun, (γ' (.inr q₀), γ' (.inr q₁)))
            invFun := fun p s => match s with
              | .inl (.inl e₀) => p.1 (.inl e₀)
              | .inl (.inr false) => p.1 (.inr q₀)
              | .inl (.inr true) => p.1 (.inr q₁)
              | .inr q => if q = q₀ then p.2.1 else if q = q₁ then p.2.2 else p.1 (.inr q)
            left_inv := fun γ' => by
              ext ((e₀ | b) | q)
              · rfl
              · cases b <;> simp [oldEdgeFun, hq_ne.symm]
              · by_cases hq0 : q = q₀
                · subst hq0; simp
                · by_cases hq1 : q = q₁
                  · subst hq1; simp [hq0]
                  · simp [hq0, hq1, oldEdgeFun]
            right_inv := fun ⟨γ, a₀, a₁⟩ => by
              refine Prod.ext (funext fun s => ?_) ?_
              · cases s with
                | inl e₀ => rfl
                | inr q =>
                  by_cases hq0 : q = q₀
                  · subst hq0; simp [oldEdgeFun]
                  · by_cases hq1 : q = q₁
                    · subst hq1; simp [oldEdgeFun, hq0]
                    · simp [oldEdgeFun, hq0, hq1]
              · simp [hq_ne.symm] }
        rw [Matrix.mul_apply]
        have hplace (z : W → Bool) :
            (placeAct g : Matrix _ _ ℂ) y z =
              if ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q then g2Mat (y q₀) (y q₁) (z q₀) (z q₁)
              else 0 := by
          rw [placeAct_apply]
          have hiff : (∀ q : W, (¬∃ i, g.2.2 i = q) → y q = z q) ↔
              ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q := by
            refine forall_congr' fun q => imp_congr_left
              ⟨fun h => ⟨fun h0 => h ⟨i₀, h0.symm⟩, fun h1 => h ⟨i₁, h1.symm⟩⟩,
               fun ⟨h0, h1⟩ ⟨i, hi⟩ => ?_⟩
            rcases (by omega : i.val = 0 ∨ i.val = 1) with hi0 | hi1
            · have hii : i = i₀ := Fin.ext hi0
              exact h0 (hi.symm.trans (congrArg g.2.2 hii))
            · have hii : i = i₁ := Fin.ext hi1
              exact h1 (hi.symm.trans (congrArg g.2.2 hii))
          rw [if_congr hiff rfl rfl]
          split_ifs with h
          · have hy_eq : (y ∘ g.2.2) = fun i => if i = i₀ then y q₀ else y q₁ :=
              funext fun i => by
                by_cases hi0 : i = i₀
                · subst hi0; simp [q₀]
                · have hi1 : i = i₁ := by ext; omega
                  subst hi1; simp [hi0, q₁]
            have hz_eq : (z ∘ g.2.2) = fun i => if i = i₀ then z q₀ else z q₁ :=
              funext fun i => by
                by_cases hi0 : i = i₀
                · subst hi0; simp [q₀]
                · have hi1 : i = i₁ := by ext; omega
                  subst hi1; simp [hi0, q₁]
            rw [hy_eq, hz_eq]
          · rfl
        have hsum_z : (∑ z : W → Bool, (placeAct g : Matrix _ _ ℂ) y z * M z x) =
            ∑ z₀ : Bool, ∑ z₁ : Bool,
              g2Mat (y q₀) (y q₁) z₀ z₁ *
                M (Function.update (Function.update y q₁ z₁) q₀ z₀) x := by
          simp_rw [hplace, ite_mul, zero_mul]
          let fupd (p : Bool × Bool) : W → Bool :=
            Function.update (Function.update y q₁ p.2) q₀ p.1
          have hfupd_inj : Function.Injective fupd := fun p₁ p₂ h => by
            have h0 : p₁.1 = p₂.1 := by simpa [fupd] using congrFun h q₀
            have h1 : p₁.2 = p₂.2 := by simpa [fupd, hq_ne.symm] using congrFun h q₁
            exact Prod.ext h0 h1
          have hfilt : (Finset.univ.filter fun z : W → Bool =>
              ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q) = Finset.univ.image fupd := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hz
              refine ⟨(z q₀, z q₁), funext fun q => ?_⟩
              by_cases h0 : q = q₀
              · subst h0; simp only [fupd, Function.update_self]
              · by_cases h1 : q = q₁
                · subst h1; simp only [fupd, ne_eq, h0, not_false_eq_true, Function.update_of_ne,
                    Function.update_self]
                · simp only [fupd, ne_eq, h0, h1, not_false_eq_true, Function.update_of_ne,
                    hz q ⟨h0, h1⟩]
            · rintro ⟨⟨z₀, z₁⟩, rfl⟩ q ⟨h0, h1⟩
              simp only [fupd, ne_eq, h0, h1, not_false_eq_true, Function.update_of_ne]
          rw [← Finset.sum_filter, hfilt, Finset.sum_image (fun _ _ _ _ h => hfupd_inj h),
            Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun z₀ _ => Finset.sum_congr rfl fun z₁ _ => ?_
          simp only [fupd, Function.update_self, ne_eq, hq_ne.symm, not_false_eq_true,
            Function.update_of_ne]
        rw [hsum_z]
        have hrhs : (∑ γ' : (S.E ⊕ Bool) ⊕ W → Bool,
            (∏ v : S.V ⊕ Unit, (match v with
              | .inl u => S.openF u x (γ' ∘ oldEdge)
              | .inr () => gateTensor γ')) *
              ∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                (y q) (γ' (.inr q))) =
            ∑ γ : S.E ⊕ W → Bool,
              (∏ u : S.V, S.openF u x γ) *
                (∑ z₀ : Bool, ∑ z₁ : Bool,
                  g2Mat (y q₀) (y q₁) z₀ z₁ *
                    S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁))) *
                ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
          rw [← Fintype.sum_equiv eqvFun.symm
            (fun p =>
              (∏ v : S.V ⊕ Unit, (match v with
                | .inl u => S.openF u x ((eqvFun.symm p) ∘ oldEdge)
                | .inr () => gateTensor (eqvFun.symm p))) *
                ∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                  (y q) (eqvFun.symm p (.inr q))) _ (fun _ => rfl)]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [Fintype.sum_prod_type]
          set body : ℂ :=
            (∏ u : S.V, S.openF u x γ) *
              (∑ z₀ : Bool, ∑ z₁ : Bool,
                g2Mat (y q₀) (y q₁) z₀ z₁ *
                  S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁))) *
              ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q))
          have hterm_ab (a₀ a₁ : Bool) :
              (∏ v : S.V ⊕ Unit, (match v with
                | .inl u => S.openF u x ((eqvFun.symm (γ, a₀, a₁)) ∘ oldEdge)
                | .inr () => gateTensor (eqvFun.symm (γ, a₀, a₁)))) *
              (∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                (y q) (eqvFun.symm (γ, a₀, a₁) (.inr q))) =
              if a₀ = y q₀ ∧ a₁ = y q₁ then body else 0 := by
            have hcomp_γ : (eqvFun.symm (γ, a₀, a₁)) ∘ oldEdge = γ :=
              congrArg Prod.fst (eqvFun.apply_symm_apply (γ, a₀, a₁))
            have ha₀_val : eqvFun.symm (γ, a₀, a₁) (.inr q₀) = a₀ :=
              congrArg (Prod.fst ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁))
            have ha₁_val : eqvFun.symm (γ, a₀, a₁) (.inr q₁) = a₁ :=
              congrArg (Prod.snd ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁))
            have hf0 : eqvFun.symm (γ, a₀, a₁) (.inl (.inr false)) = γ (.inr q₀) := rfl
            have hf1 : eqvFun.symm (γ, a₀, a₁) (.inl (.inr true)) = γ (.inr q₁) := rfl
            rw [Fintype.prod_sum_type]
            simp only [Fintype.prod_unique, hcomp_γ, gateTensor, ha₀_val, ha₁_val, hf0, hf1]
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
              ← Finset.mul_prod_erase (Finset.univ.erase q₀) _
                (Finset.mem_erase.mpr ⟨hq_ne.symm, Finset.mem_univ q₁⟩)]
            simp only [true_or, or_true, ↓reduceIte, ha₀_val, ha₁_val, Matrix.one_apply]
            have hrest : (∏ q ∈ (Finset.univ.erase q₀).erase q₁,
                (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q) (y q)
                  (eqvFun.symm (γ, a₀, a₁) (.inr q))) =
                ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
              refine Finset.prod_congr rfl fun q hq => ?_
              have hq1 : q ≠ q₁ := (Finset.mem_erase.mp hq).1
              have hq0 : q ≠ q₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
              have hnot : ¬(q = q₀ ∨ q = q₁) := not_or.mpr ⟨hq0, hq1⟩
              simp only [hnot, ↓reduceIte]
              have hval : eqvFun.symm (γ, a₀, a₁) (.inr q) = γ (.inr q) := by
                simp only [eqvFun, Equiv.coe_fn_symm_mk, hq0, hq1, ↓reduceIte]
              rw [hval]
            rw [hrest]
            by_cases h0 : y q₀ = a₀ <;> by_cases h1 : y q₁ = a₁
            · subst h0; subst h1
              simp only [and_self, ↓reduceIte, body]
              ring
            · have hna : ¬(a₀ = y q₀ ∧ a₁ = y q₁) := fun h => h1 h.2.symm
              simp only [h1, hna, ↓reduceIte, mul_zero, zero_mul]
            · have hna : ¬(a₀ = y q₀ ∧ a₁ = y q₁) := fun h => h0 h.1.symm
              simp only [h0, hna, ↓reduceIte, zero_mul, mul_zero]
            · have hna : ¬(a₀ = y q₀ ∧ a₁ = y q₁) := fun h => h0 h.1.symm
              simp only [h0, hna, ↓reduceIte, zero_mul, mul_zero]
          simp_rw [hterm_ab]
          simp only [Fintype.sum_bool]
          cases y q₀ <;> cases y q₁ <;> simp
        rw [hrhs]
        have hstep1 : (∑ z₀ : Bool, ∑ z₁ : Bool,
            g2Mat (y q₀) (y q₁) z₀ z₁ *
              M (Function.update (Function.update y q₁ z₁) q₀ z₀) x) =
            S.scalar * ∑ z₀ : Bool, ∑ z₁ : Bool, ∑ γ : S.E ⊕ W → Bool,
              g2Mat (y q₀) (y q₁) z₀ z₁ *
                ((∏ u : S.V, S.openF u x γ) *
                  ∏ q : W, S.tipMat q (Function.update (Function.update y q₁ z₁) q₀ z₀ q)
                    (γ (.inr q))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z₀ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z₁ _ => ?_
          rw [S.contract _ x, ← mul_assoc, mul_comm (g2Mat _ _ _ _) S.scalar, mul_assoc,
            Finset.mul_sum]
        rw [hstep1, Finset.sum_comm]
        simp_rw [Finset.sum_comm (s := Finset.univ (α := Bool))
          (t := Finset.univ (α := S.E ⊕ W → Bool))]
        congr 1
        refine Finset.sum_congr rfl fun γ _ => ?_
        have hupd_prod (z₀ z₁ : Bool) :
            (∏ q : W, S.tipMat q (Function.update (Function.update y q₁ z₁) q₀ z₀ q)
              (γ (.inr q))) =
            S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁)) *
              ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
            ← Finset.mul_prod_erase (Finset.univ.erase q₀) _
              (Finset.mem_erase.mpr ⟨hq_ne.symm, Finset.mem_univ q₁⟩)]
          have hupd0 : Function.update (Function.update y q₁ z₁) q₀ z₀ q₀ = z₀ :=
            Function.update_self _ _ _
          have hupd1 : Function.update (Function.update y q₁ z₁) q₀ z₀ q₁ = z₁ := by
            rw [Function.update_of_ne hq_ne.symm, Function.update_self]
          rw [hupd0, hupd1, mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun q hq => ?_
          have hq1 : q ≠ q₁ := (Finset.mem_erase.mp hq).1
          have hq0 : q ≠ q₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
          have hupdq : Function.update (Function.update y q₁ z₁) q₀ z₀ q = y q := by
            rw [Function.update_of_ne hq0, Function.update_of_ne hq1]
          rw [hupdq]
        simp_rw [hupd_prod]
        rw [Finset.sum_comm]
        symm
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z₀ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun z₁ _ => by ring
      loc_in := by
        rintro (u | ⟨⟩) x₁ x₂ γ' h
        · exact S.loc_in u x₁ x₂ (γ' ∘ oldEdge) fun q hq => h q (congrArg Sum.inl hq)
        · rfl
      loc_edge := by
        rintro (u | ⟨⟩) x γ₁ γ₂ h
        · exact S.loc_edge u x (γ₁ ∘ oldEdge) (γ₂ ∘ oldEdge) fun e he => h ((hmap_u u e).mp he)
        · simp only [gateTensor]
          have h0 : γ₁ (.inr q₀) = γ₂ (.inr q₀) :=
            h (Or.inl (by simp only [capGraph, tip', true_or, ↓reduceIte]))
          have h1 : γ₁ (.inr q₁) = γ₂ (.inr q₁) :=
            h (Or.inl (by simp only [capGraph, tip', or_true, ↓reduceIte]))
          have hf0 : γ₁ (.inl (.inr false)) = γ₂ (.inl (.inr false)) := h (Or.inr rfl)
          have hf1 : γ₁ (.inl (.inr true)) = γ₂ (.inl (.inr true)) := h (Or.inr rfl)
          rw [h0, h1, hf0, hf1] }

/-- Step for a bond-rank-two `2`-qubit gate in degree `d = 3` (adds `Bool` vertices and `Fin 3`
edges). -/
private noncomputable def openStateTwoDegThree {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState 3 W M s)
    (g : ActiveGate W) (h2 : g.1.val = 2) (hbond : HasBondRankTwo (h2 ▸ g.2.1)) :
    OpenState 3 W ((placeAct g : Matrix _ _ ℂ) * M) (s + 1) := by
  let i₀ : Fin g.1.val := ⟨0, by omega⟩
  let i₁ : Fin g.1.val := ⟨1, by omega⟩
  have hi_ne : i₀ ≠ i₁ := fun h => by
    have hv := congrArg Fin.val h
    dsimp only [i₀, i₁] at hv
    omega
  let q₀ : W := g.2.2 i₀
  let q₁ : W := g.2.2 i₁
  have hq_ne : q₀ ≠ q₁ := fun h => hi_ne (g.2.2.injective h)
  let L_ten : Bool → Bool → Bool → ℂ := Classical.choose hbond
  let R_ten : Bool → Bool → Bool → ℂ := Classical.choose (Classical.choose_spec hbond)
  have hLR : ∀ y' x' : Fin 2 → Bool,
      ((h2 ▸ g.2.1 : Quantum.Gate 2) : Matrix _ _ ℂ) y' x' =
        ∑ b : Bool, L_ten (x' 0) (y' 0) b * R_ten (x' 1) (y' 1) b :=
    Classical.choose_spec (Classical.choose_spec hbond)
  let G' : Multigraph (S.V ⊕ Bool) (S.E ⊕ Fin 3) :=
    { src := fun e => match e with
        | .inl e₀ => .inl (S.G.src e₀)
        | .inr 0 => .inl (S.tip q₀)
        | .inr 1 => .inl (S.tip q₁)
        | .inr 2 => .inr false
      tgt := fun e => match e with
        | .inl e₀ => .inl (S.G.tgt e₀)
        | .inr 0 => .inr false
        | .inr 1 => .inr true
        | .inr 2 => .inr true }
  let tip' : W → S.V ⊕ Bool :=
    fun q => if q = q₀ then .inr false else if q = q₁ then .inr true else .inl (S.tip q)
  let oldEdgeFun : S.E ⊕ W → (S.E ⊕ Fin 3) ⊕ W := fun e => match e with
    | .inl e₀ => .inl (.inl e₀)
    | .inr q =>
      if q = q₀ then .inl (.inr 0)
      else if q = q₁ then .inl (.inr 1)
      else .inr q
  have hold_inj : Function.Injective oldEdgeFun := fun a b hab => by
    cases a with
    | inl ea =>
      cases b with
      | inl eb => exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj hab))
      | inr qb => dsimp only [oldEdgeFun] at hab; split_ifs at hab <;> simp at hab
    | inr qa =>
      cases b with
      | inl eb => dsimp only [oldEdgeFun] at hab; split_ifs at hab <;> simp at hab
      | inr qb => dsimp only [oldEdgeFun] at hab; split_ifs at hab <;> simp_all
  let oldEdge : S.E ⊕ W ↪ (S.E ⊕ Fin 3) ⊕ W := ⟨oldEdgeFun, hold_inj⟩
  have hmap_u (u : S.V) (e : S.E ⊕ W) :
      e ∈ (capGraph S.G S.tip).incidenceSet (.inl u) ↔
        oldEdge e ∈ (capGraph G' tip').incidenceSet (.inl (.inl u)) := by
    change _ ↔ oldEdgeFun e ∈ _
    cases e with
    | inl e₀ =>
      simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, G']
    | inr q =>
      by_cases hq0 : q = q₀
      · subst hq0; simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, G']
      · by_cases hq1 : q = q₁
        · subst hq1; simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, hq0, G']
        · simp [Multigraph.mem_incidenceSet, capGraph, oldEdgeFun, hq0, hq1, tip']
  have hsurj_u (u : S.V) (e' : (S.E ⊕ Fin 3) ⊕ W)
      (he' : e' ∈ (capGraph G' tip').incidenceSet (.inl (.inl u))) :
      ∃ e, oldEdge e = e' := by
    change ∃ e, oldEdgeFun e = e'
    rcases e' with (e₀ | r) | q
    · exact ⟨.inl e₀, rfl⟩
    · fin_cases r
      · exact ⟨.inr q₀, by simp [oldEdgeFun]⟩
      · exact ⟨.inr q₁, by simp [oldEdgeFun, hq_ne.symm]⟩
      · simp [Multigraph.mem_incidenceSet, capGraph, G'] at he'
    · by_cases hq0 : q = q₀
      · subst hq0; simp [Multigraph.mem_incidenceSet, capGraph, tip'] at he'
      · by_cases hq1 : q = q₁
        · subst hq1; simp [Multigraph.mem_incidenceSet, capGraph, tip', hq0] at he'
        · exact ⟨.inr q, by simp [oldEdgeFun, hq0, hq1]⟩
  let leftT (γ' : (S.E ⊕ Fin 3) ⊕ W → Bool) : ℂ :=
    ∑ z₀ : Bool, L_ten z₀ (γ' (.inr q₀)) (γ' (.inl (.inr 2))) *
      S.tipMat q₀ z₀ (γ' (.inl (.inr 0)))
  let rightT (γ' : (S.E ⊕ Fin 3) ⊕ W → Bool) : ℂ :=
    ∑ z₁ : Bool, R_ten z₁ (γ' (.inr q₁)) (γ' (.inl (.inr 2))) *
      S.tipMat q₁ z₁ (γ' (.inl (.inr 1)))
  exact
    { V := S.V ⊕ Bool
      E := S.E ⊕ Fin 3
      instFV := inferInstance
      instDV := inferInstance
      instFE := inferInstance
      instDE := inferInstance
      G := G'
      inVert := S.inVert.trans ⟨Sum.inl, Sum.inl_injective⟩
      tip := tip'
      scalar := S.scalar
      tipMat := fun q => if q = q₀ ∨ q = q₁ then 1 else S.tipMat q
      openF := fun v x γ' => match v with
        | .inl u => S.openF u x (γ' ∘ oldEdge)
        | .inr false => leftT γ'
        | .inr true => rightT γ'
      loopless := by
        rintro (e₀ | r)
        · exact fun h => S.loopless e₀ (Sum.inl.inj h)
        · fin_cases r
          · exact Sum.inl_ne_inr
          · exact Sum.inl_ne_inr
          · simp [G']
      deg_inVert := fun q =>
        (ncard_incidence_eq_of_bij S.G S.tip G' tip' Sum.inl oldEdge (S.inVert q)
          (hmap_u _) (hsurj_u _)).trans (S.deg_inVert q)
      deg_gate := by
        rintro (u | b) hv
        · have hu : u ∉ Set.range S.inVert := fun ⟨q, hq⟩ => hv ⟨q, congrArg Sum.inl hq⟩
          exact (ncard_incidence_eq_of_bij S.G S.tip G' tip' Sum.inl oldEdge u
            (hmap_u u) (hsurj_u u)).trans (S.deg_gate u hu)
        · cases b
          · have hset : (capGraph G' tip').incidenceSet (.inl (.inr false)) =
                {.inl (.inr 0), .inl (.inr 2), .inr q₀} := by
              ext ((e₀ | r) | q)
              · simp [Multigraph.mem_incidenceSet, capGraph, G']
              · fin_cases r <;> simp [Multigraph.mem_incidenceSet, capGraph, G']
              · by_cases hq0 : q = q₀
                · subst hq0; simp [Multigraph.mem_incidenceSet, capGraph, tip']
                · by_cases hq1 : q = q₁ <;>
                    simp [Multigraph.mem_incidenceSet, capGraph, tip', hq0, hq1]
            rw [hset, ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_singleton]
            · simp
            · simp [mem_insert_iff, mem_singleton_iff]
          · have hset : (capGraph G' tip').incidenceSet (.inl (.inr true)) =
                {.inl (.inr 1), .inl (.inr 2), .inr q₁} := by
              ext ((e₀ | r) | q)
              · simp [Multigraph.mem_incidenceSet, capGraph, G']
              · fin_cases r <;> simp [Multigraph.mem_incidenceSet, capGraph, G']
              · by_cases hq0 : q = q₀
                · subst hq0; simp [Multigraph.mem_incidenceSet, capGraph, tip', hq_ne]
                · by_cases hq1 : q = q₁ <;>
                    simp [Multigraph.mem_incidenceSet, capGraph, tip', hq0, hq1, hq_ne.symm]
            rw [hset, ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_singleton]
            · simp
            · simp [mem_insert_iff, mem_singleton_iff]
      reach_tip := fun q => by
        have hprev : G'.toSimpleGraph.Reachable (.inl (S.inVert q)) (.inl (S.tip q)) :=
          reachable_map_inl ⟨Sum.inl, Sum.inl_injective⟩
            (fun e₀ => ⟨.inl e₀, by simp [Multigraph.ends, G']⟩) (S.reach_tip q)
        by_cases hq0 : q = q₀
        · subst hq0; simp only [tip', ↓reduceIte]
          exact hprev.trans (G'.reachable_src_tgt (.inr 0))
        · by_cases hq1 : q = q₁
          · subst hq1; simp only [tip', hq0, ↓reduceIte]
            exact hprev.trans (G'.reachable_src_tgt (.inr 1))
          · simp only [tip', hq0, hq1, ↓reduceIte]; exact hprev
      card_V := by
        rw [Fintype.card_sum, Fintype.card_bool]
        obtain ⟨hc1, hc2⟩ := S.card_V
        exact ⟨by omega, by omega⟩
      contract := fun y x => by
        let eqvFun : ((S.E ⊕ Fin 3) ⊕ W → Bool) ≃
            (S.E ⊕ W → Bool) × (Bool × Bool × Bool) :=
          { toFun := fun γ' =>
              (γ' ∘ oldEdgeFun, (γ' (.inr q₀), γ' (.inr q₁), γ' (.inl (.inr 2))))
            invFun := fun p s => match s with
              | .inl (.inl e₀) => p.1 (.inl e₀)
              | .inl (.inr r) =>
                if r = 0 then p.1 (.inr q₀) else if r = 1 then p.1 (.inr q₁) else p.2.2.2
              | .inr q =>
                if q = q₀ then p.2.1 else if q = q₁ then p.2.2.1 else p.1 (.inr q)
            left_inv := fun γ' => by
              ext ((e₀ | r) | q)
              · rfl
              · fin_cases r
                · simp [oldEdgeFun]
                · simp [oldEdgeFun, hq_ne.symm]
                · simp
              · by_cases hq0 : q = q₀
                · subst hq0; simp
                · by_cases hq1 : q = q₁
                  · subst hq1; simp [hq0]
                  · simp [hq0, hq1, oldEdgeFun]
            right_inv := fun ⟨γ, a₀, a₁, b_bond⟩ => by
              refine Prod.ext (funext fun s => ?_) ?_
              · cases s with
                | inl e₀ => rfl
                | inr q =>
                  by_cases hq0 : q = q₀
                  · subst hq0; simp [oldEdgeFun]
                  · by_cases hq1 : q = q₁
                    · subst hq1; simp [oldEdgeFun, hq0]
                    · simp [oldEdgeFun, hq0, hq1]
              · simp [hq_ne.symm] }
        have hg_eq (a₀ a₁ z₀ z₁ : Bool) :
            (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
              (fun i => if i = i₀ then a₀ else a₁)
              (fun i => if i = i₀ then z₀ else z₁) =
              ∑ b : Bool, L_ten z₀ a₀ b * R_ten z₁ a₁ b := by
          rcases g with ⟨⟨arity, har_lt⟩, gate, wires⟩
          dsimp only [i₀, i₁] at h2 hLR ⊢
          subst h2
          exact hLR (fun i => if i = 0 then a₀ else a₁) (fun i => if i = 0 then z₀ else z₁)
        rw [Matrix.mul_apply]
        have hplace (z : W → Bool) :
            (placeAct g : Matrix _ _ ℂ) y z =
              if ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q then
                ∑ b : Bool, L_ten (z q₀) (y q₀) b * R_ten (z q₁) (y q₁) b
              else 0 := by
          rw [placeAct_apply]
          have hiff : (∀ q : W, (¬∃ i, g.2.2 i = q) → y q = z q) ↔
              ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q := by
            refine forall_congr' fun q => imp_congr_left
              ⟨fun h => ⟨fun h0 => h ⟨i₀, h0.symm⟩, fun h1 => h ⟨i₁, h1.symm⟩⟩,
               fun ⟨h0, h1⟩ ⟨i, hi⟩ => ?_⟩
            rcases (by omega : i.val = 0 ∨ i.val = 1) with hi0 | hi1
            · have hii : i = i₀ := Fin.ext hi0
              exact h0 (hi.symm.trans (congrArg g.2.2 hii))
            · have hii : i = i₁ := Fin.ext hi1
              exact h1 (hi.symm.trans (congrArg g.2.2 hii))
          rw [if_congr hiff rfl rfl]
          split_ifs with h
          · rw [← hg_eq (y q₀) (y q₁) (z q₀) (z q₁)]
            have hy_eq : (y ∘ g.2.2) = fun i => if i = i₀ then y q₀ else y q₁ :=
              funext fun i => by
                by_cases hi0 : i = i₀
                · subst hi0; simp [q₀]
                · have hi1 : i = i₁ := by ext; omega
                  subst hi1; simp [hi0, q₁]
            have hz_eq : (z ∘ g.2.2) = fun i => if i = i₀ then z q₀ else z q₁ :=
              funext fun i => by
                by_cases hi0 : i = i₀
                · subst hi0; simp [q₀]
                · have hi1 : i = i₁ := by ext; omega
                  subst hi1; simp [hi0, q₁]
            rw [hy_eq, hz_eq]
          · rfl
        have hsum_z : (∑ z : W → Bool, (placeAct g : Matrix _ _ ℂ) y z * M z x) =
            ∑ z₀ : Bool, ∑ z₁ : Bool,
              (∑ b : Bool, L_ten z₀ (y q₀) b * R_ten z₁ (y q₁) b) *
                M (Function.update (Function.update y q₁ z₁) q₀ z₀) x := by
          simp_rw [hplace, ite_mul, zero_mul]
          let fupd (p : Bool × Bool) : W → Bool :=
            Function.update (Function.update y q₁ p.2) q₀ p.1
          have hfupd_inj : Function.Injective fupd := fun p₁ p₂ h => by
            have h0 : p₁.1 = p₂.1 := by simpa [fupd] using congrFun h q₀
            have h1 : p₁.2 = p₂.2 := by simpa [fupd, hq_ne.symm] using congrFun h q₁
            exact Prod.ext h0 h1
          have hfilt : (Finset.univ.filter fun z : W → Bool =>
              ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q) = Finset.univ.image fupd := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hz
              refine ⟨(z q₀, z q₁), funext fun q => ?_⟩
              by_cases h0 : q = q₀
              · subst h0; simp only [fupd, Function.update_self]
              · by_cases h1 : q = q₁
                · subst h1; simp only [fupd, ne_eq, h0, not_false_eq_true, Function.update_of_ne,
                    Function.update_self]
                · simp only [fupd, ne_eq, h0, h1, not_false_eq_true, Function.update_of_ne,
                    hz q ⟨h0, h1⟩]
            · rintro ⟨⟨z₀, z₁⟩, rfl⟩ q ⟨h0, h1⟩
              simp only [fupd, ne_eq, h0, h1, not_false_eq_true, Function.update_of_ne]
          rw [← Finset.sum_filter, hfilt, Finset.sum_image (fun _ _ _ _ h => hfupd_inj h),
            Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun z₀ _ => Finset.sum_congr rfl fun z₁ _ => ?_
          simp only [fupd, Function.update_self, ne_eq, hq_ne.symm, not_false_eq_true,
            Function.update_of_ne]
        rw [hsum_z]
        have hrhs : (∑ γ' : (S.E ⊕ Fin 3) ⊕ W → Bool,
            (∏ v : S.V ⊕ Bool, (match v with
              | .inl u => S.openF u x (γ' ∘ oldEdge)
              | .inr false => leftT γ'
              | .inr true => rightT γ')) *
              ∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                (y q) (γ' (.inr q))) =
            ∑ γ : S.E ⊕ W → Bool,
              (∏ u : S.V, S.openF u x γ) *
                (∑ z₀ : Bool, ∑ z₁ : Bool,
                  (∑ b : Bool, L_ten z₀ (y q₀) b * R_ten z₁ (y q₁) b) *
                    S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁))) *
                ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
          rw [← Fintype.sum_equiv eqvFun.symm
            (fun p =>
              (∏ v : S.V ⊕ Bool, (match v with
                | .inl u => S.openF u x ((eqvFun.symm p) ∘ oldEdge)
                | .inr false => leftT (eqvFun.symm p)
                | .inr true => rightT (eqvFun.symm p))) *
                ∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                  (y q) (eqvFun.symm p (.inr q))) _ (fun _ => rfl)]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
          let body (b : Bool) : ℂ :=
            (∏ u : S.V, S.openF u x γ) *
              ((∑ z₀ : Bool, L_ten z₀ (y q₀) b * S.tipMat q₀ z₀ (γ (.inr q₀))) *
                (∑ z₁ : Bool, R_ten z₁ (y q₁) b * S.tipMat q₁ z₁ (γ (.inr q₁)))) *
              ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q))
          have hterm_ab (a₀ a₁ b : Bool) :
              (∏ v : S.V ⊕ Bool, (match v with
                | .inl u => S.openF u x ((eqvFun.symm (γ, a₀, a₁, b)) ∘ oldEdge)
                | .inr false => leftT (eqvFun.symm (γ, a₀, a₁, b))
                | .inr true => rightT (eqvFun.symm (γ, a₀, a₁, b)))) *
              (∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                (y q) (eqvFun.symm (γ, a₀, a₁, b) (.inr q))) =
              if a₀ = y q₀ ∧ a₁ = y q₁ then body b else 0 := by
            have hcomp_γ : (eqvFun.symm (γ, a₀, a₁, b)) ∘ oldEdge = γ :=
              congrArg Prod.fst (eqvFun.apply_symm_apply (γ, a₀, a₁, b))
            have ha₀_val : eqvFun.symm (γ, a₀, a₁, b) (.inr q₀) = a₀ :=
              congrArg (Prod.fst ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁, b))
            have ha₁_val : eqvFun.symm (γ, a₀, a₁, b) (.inr q₁) = a₁ :=
              congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁, b))
            have hb_val : eqvFun.symm (γ, a₀, a₁, b) (.inl (.inr 2)) = b :=
              congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁, b))
            have hf0 : eqvFun.symm (γ, a₀, a₁, b) (.inl (.inr 0)) = γ (.inr q₀) := rfl
            have hf1 : eqvFun.symm (γ, a₀, a₁, b) (.inl (.inr 1)) = γ (.inr q₁) := rfl
            rw [Fintype.prod_sum_type, Fintype.prod_bool]
            simp only [hcomp_γ, leftT, rightT, ha₀_val, ha₁_val, hb_val, hf0, hf1]
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
              ← Finset.mul_prod_erase (Finset.univ.erase q₀) _
                (Finset.mem_erase.mpr ⟨hq_ne.symm, Finset.mem_univ q₁⟩)]
            simp only [true_or, or_true, ↓reduceIte, ha₀_val, ha₁_val, Matrix.one_apply]
            have hrest : (∏ q ∈ (Finset.univ.erase q₀).erase q₁,
                (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q) (y q)
                  (eqvFun.symm (γ, a₀, a₁, b) (.inr q))) =
                ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
              refine Finset.prod_congr rfl fun q hq => ?_
              have hq1 : q ≠ q₁ := (Finset.mem_erase.mp hq).1
              have hq0 : q ≠ q₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
              have hnot : ¬(q = q₀ ∨ q = q₁) := not_or.mpr ⟨hq0, hq1⟩
              simp only [hnot, ↓reduceIte]
              have hval : eqvFun.symm (γ, a₀, a₁, b) (.inr q) = γ (.inr q) := by
                simp only [eqvFun, Equiv.coe_fn_symm_mk, hq0, hq1, ↓reduceIte]
              rw [hval]
            rw [hrest]
            by_cases h0 : y q₀ = a₀ <;> by_cases h1 : y q₁ = a₁
            · subst h0; subst h1
              simp only [and_self, ↓reduceIte, body]
              ring
            · have hna : ¬(a₀ = y q₀ ∧ a₁ = y q₁) := fun h => h1 h.2.symm
              simp only [h1, hna, ↓reduceIte, mul_zero, zero_mul]
            · have hna : ¬(a₀ = y q₀ ∧ a₁ = y q₁) := fun h => h0 h.1.symm
              simp only [h0, hna, ↓reduceIte, zero_mul, mul_zero]
            · have hna : ¬(a₀ = y q₀ ∧ a₁ = y q₁) := fun h => h0 h.1.symm
              simp only [h0, hna, ↓reduceIte, zero_mul, mul_zero]
          simp_rw [hterm_ab]
          have collapse_a : (∑ a₀ : Bool, ∑ a₁ : Bool, ∑ b : Bool,
              if a₀ = y q₀ ∧ a₁ = y q₁ then body b else 0) = ∑ b : Bool, body b := by
            rw [Fintype.sum_bool]
            simp_rw [Fintype.sum_bool]
            cases y q₀ <;> cases y q₁ <;> simp
          rw [collapse_a]
          dsimp only [body]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          congr 2
          simp only [Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z₀ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z₁ _ => ?_
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hrhs]
        have hstep1 : (∑ z₀ : Bool, ∑ z₁ : Bool,
            (∑ b : Bool, L_ten z₀ (y q₀) b * R_ten z₁ (y q₁) b) *
              M (Function.update (Function.update y q₁ z₁) q₀ z₀) x) =
            S.scalar * ∑ z₀ : Bool, ∑ z₁ : Bool, ∑ γ : S.E ⊕ W → Bool,
              (∑ b : Bool, L_ten z₀ (y q₀) b * R_ten z₁ (y q₁) b) *
                ((∏ u : S.V, S.openF u x γ) *
                  ∏ q : W, S.tipMat q (Function.update (Function.update y q₁ z₁) q₀ z₀ q)
                    (γ (.inr q))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z₀ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z₁ _ => ?_
          rw [S.contract _ x, ← mul_assoc, mul_comm _ S.scalar, mul_assoc, Finset.mul_sum]
        rw [hstep1, Finset.sum_comm]
        simp_rw [Finset.sum_comm (s := Finset.univ (α := Bool))
          (t := Finset.univ (α := S.E ⊕ W → Bool))]
        congr 1
        refine Finset.sum_congr rfl fun γ _ => ?_
        have hupd_prod (z₀ z₁ : Bool) :
            (∏ q : W, S.tipMat q (Function.update (Function.update y q₁ z₁) q₀ z₀ q)
              (γ (.inr q))) =
            S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁)) *
              ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
            ← Finset.mul_prod_erase (Finset.univ.erase q₀) _
              (Finset.mem_erase.mpr ⟨hq_ne.symm, Finset.mem_univ q₁⟩)]
          have hupd0 : Function.update (Function.update y q₁ z₁) q₀ z₀ q₀ = z₀ :=
            Function.update_self _ _ _
          have hupd1 : Function.update (Function.update y q₁ z₁) q₀ z₀ q₁ = z₁ := by
            rw [Function.update_of_ne hq_ne.symm, Function.update_self]
          rw [hupd0, hupd1, mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun q hq => ?_
          have hq1 : q ≠ q₁ := (Finset.mem_erase.mp hq).1
          have hq0 : q ≠ q₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
          have hupdq : Function.update (Function.update y q₁ z₁) q₀ z₀ q = y q := by
            rw [Function.update_of_ne hq0, Function.update_of_ne hq1]
          rw [hupdq]
        simp_rw [hupd_prod]
        rw [Finset.sum_comm]
        symm
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z₀ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun z₁ _ => by ring
      loc_in := by
        rintro (u | b) x₁ x₂ γ' h
        · exact S.loc_in u x₁ x₂ (γ' ∘ oldEdge) fun q hq => h q (congrArg Sum.inl hq)
        · cases b <;> rfl
      loc_edge := by
        rintro (u | b) x γ₁ γ₂ h
        · exact S.loc_edge u x (γ₁ ∘ oldEdge) (γ₂ ∘ oldEdge) fun e he => h ((hmap_u u e).mp he)
        · cases b
          · simp only [leftT]
            have h0 : γ₁ (.inr q₀) = γ₂ (.inr q₀) :=
              h (Or.inl (by simp only [capGraph, tip', ↓reduceIte]))
            have hb : γ₁ (.inl (.inr 2)) = γ₂ (.inl (.inr 2)) := h (Or.inl rfl)
            have hf0 : γ₁ (.inl (.inr 0)) = γ₂ (.inl (.inr 0)) := h (Or.inr rfl)
            rw [h0, hb, hf0]
          · simp only [rightT]
            have h1 : γ₁ (.inr q₁) = γ₂ (.inr q₁) :=
              h (Or.inl (by simp only [capGraph, tip', hq_ne.symm, ↓reduceIte]))
            have hb : γ₁ (.inl (.inr 2)) = γ₂ (.inl (.inr 2)) := h (Or.inr rfl)
            have hf1 : γ₁ (.inl (.inr 1)) = γ₂ (.inl (.inr 1)) := h (Or.inr rfl)
            rw [h1, hb, hf1] }

open Classical in
/-- Close an `OpenState d W M s` (`d ∈ {3, 4}`, `Nonempty W`) into a `CappedWireNet d W M s`. -/
private theorem OpenState.toCappedWireNet {d : ℕ} (hd : d = 3 ∨ d = 4) {W : Type}
    [Fintype W] [DecidableEq W] [Nonempty W] {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ}
    (S : OpenState d W M s) : CappedWireNet d W M s := by
  let q_star : W := Classical.arbitrary W
  let G_fin := capGraph S.G S.tip
  let inV : W ↪ S.V ⊕ W := S.inVert.trans ⟨Sum.inl, Sum.inl_injective⟩
  let outV : W ↪ S.V ⊕ W := ⟨Sum.inr, Sum.inr_injective⟩
  let F_fin (v : S.V ⊕ W) (x y : W → Bool) (γ : S.E ⊕ W → Bool) : ℂ :=
    match v with
    | .inl u => S.openF u x γ
    | .inr q => (if q = q_star then S.scalar else 1) * S.tipMat q (y q) (γ (.inr q))
  have hreach_q (q : W) : G_fin.toSimpleGraph.Reachable (inV q) (outV q) :=
    (reachable_map_inl ⟨Sum.inl, Sum.inl_injective⟩
      (fun e₀ => ⟨.inl e₀, by simp [Multigraph.ends, G_fin, capGraph]⟩)
      (S.reach_tip q)).trans (G_fin.reachable_src_tgt (.inr q))
  refine ⟨⟨S.V ⊕ W, S.E ⊕ W, inferInstance, inferInstance, inferInstance, inferInstance,
    G_fin, inV, outV, F_fin, capGraph_loopless S.loopless S.tip, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · -- `G_fin.MaxDegreeLE d`
    rintro (u | q)
    · by_cases hu : u ∈ Set.range S.inVert
      · obtain ⟨q', rfl⟩ := hu
        rw [S.deg_inVert q']
        rcases hd with rfl | rfl <;> omega
      · rw [S.deg_gate u hu]
    · dsimp only [G_fin]
      rw [capGraph_incidence_inr, ncard_singleton]
      rcases hd with rfl | rfl <;> omega
  · -- `Disjoint (range inV) (range outV)`
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨q₁, rfl⟩ ⟨q₂, h⟩
    exact Sum.inl_ne_inr h.symm
  · -- Degree-one input and output leaves
    intro q
    exact ⟨S.deg_inVert q, by
      change ((capGraph S.G S.tip).incidenceSet (.inr q)).ncard = 1
      rw [capGraph_incidence_inr, ncard_singleton]⟩
  · exact hreach_q
  · -- `Fintype.card (S.V ⊕ W) ≤ 2 * Fintype.card W + 2 * s`
    rw [Fintype.card_sum]
    obtain ⟨hc1, hc2⟩ := S.card_V
    rcases hd with rfl | rfl <;> omega
  · -- Component cycle-rank bound: `G_fin.cycleRankOn Comp + {q | inV q ∈ Comp}.ncard ≤ s + 1`
    intro Comp hComp_cut hComp_conn
    have hloopless_ind : (G_fin.induce Comp).Loopless :=
      (capGraph_loopless S.loopless S.tip).induce Comp
    have hinc_eq (w : Comp) :
        ((G_fin.induce Comp).incidenceSet w).ncard = (G_fin.incidenceSet w.1).ncard := by
      have himg : G_fin.incidenceSet w.1 = Subtype.val '' (G_fin.induce Comp).incidenceSet w := by
        ext e
        constructor
        · intro he
          have hboth : G_fin.src e ∈ Comp ∧ G_fin.tgt e ∈ Comp := by
            have hce := G_fin.edgeCut_eq_empty_iff.mp hComp_cut e
            rcases he with hs | ht
            · exact ⟨hs ▸ w.2, hce.mp (hs ▸ w.2)⟩
            · exact ⟨hce.mpr (ht ▸ w.2), ht ▸ w.2⟩
          refine ⟨⟨e, hboth⟩, ?_, rfl⟩
          exact he.imp Subtype.ext Subtype.ext
        · rintro ⟨e', he', rfl⟩
          exact he'.imp (congrArg Subtype.val) (congrArg Subtype.val)
      rw [himg, ncard_image_of_injective _ Subtype.val_injective]
    have hhand := (G_fin.induce Comp).sum_ncard_incidenceSet hloopless_ind
    change _ = 2 * Nat.card ↥{e | G_fin.src e ∈ Comp ∧ G_fin.tgt e ∈ Comp} at hhand
    rw [Nat.card_coe_set_eq, ← G_fin.touching_eq_of_edgeCut_eq_empty hComp_cut] at hhand
    simp_rw [hinc_eq] at hhand
    have hreach_mem (q : W) : inV q ∈ Comp ↔ outV q ∈ Comp :=
      mem_closed_iff_of_reachable hComp_cut (hreach_q q)
    set W_in : Set W := {q : W | inV q ∈ Comp}
    set I_gate : Set S.V := {u : S.V | (.inl u : S.V ⊕ W) ∈ Comp ∧ u ∉ Set.range S.inVert}
    have hI_le : I_gate.ncard ≤ Fintype.card S.V - Fintype.card W := by
      have hsub : I_gate ⊆ (Set.range S.inVert)ᶜ := fun u hu => hu.2
      have hcompl := ncard_add_ncard_compl (Set.range S.inVert)
      rw [ncard_range_of_injective S.inVert.injective, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card] at hcompl
      have hle := ncard_le_ncard hsub (toFinite _)
      omega
    -- Rewrite `∑_{w : Comp} deg(w)` and `Comp.ncard` via Finset filtering on `S.V ⊕ W`.
    have hsum_deg : (∑ w : Comp, (G_fin.incidenceSet w.1).ncard) =
        2 * W_in.ncard + d * I_gate.ncard := by
      have hrew : (∑ w : Comp, (G_fin.incidenceSet w.1).ncard) =
          ∑ v ∈ Finset.univ.filter (· ∈ Comp), (G_fin.incidenceSet v).ncard :=
        (Finset.sum_subtype (Finset.univ.filter (· ∈ Comp))
          (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
          fun v => (G_fin.incidenceSet v).ncard).symm
      rw [hrew]
      have hpart : (Finset.univ.filter (· ∈ Comp) : Finset (S.V ⊕ W)) =
          Finset.univ.image (fun q : W => inV q) ∩ Finset.univ.filter (· ∈ Comp) ∪
            (Finset.univ.image (fun q : W => outV q) ∩ Finset.univ.filter (· ∈ Comp) ∪
              Finset.univ.image (fun u : S.V => (.inl u : S.V ⊕ W)) ∩
                Finset.univ.filter (fun v => v ∈ Comp ∧ v ∉ Set.range inV)) := by
        ext (u | q)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_inter, Finset.mem_image, inV, outV, Function.Embedding.trans_apply,
            Function.Embedding.coeFn_mk, Sum.inl.injEq, reduceCtorEq, false_and, exists_false,
            false_or, Set.mem_range]
          by_cases hu : ∃ y, S.inVert y = u <;> tauto
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_inter, Finset.mem_image, inV, outV, Function.Embedding.trans_apply,
            Function.Embedding.coeFn_mk, reduceCtorEq, Sum.inr.injEq, exists_eq, true_and,
            false_and, exists_false, or_false, false_or]
      have hdisj1 : Disjoint
          (Finset.univ.image (fun q : W => inV q) ∩ Finset.univ.filter (· ∈ Comp))
          (Finset.univ.image (fun q : W => outV q) ∩ Finset.univ.filter (· ∈ Comp) ∪
            Finset.univ.image (fun u : S.V => (.inl u : S.V ⊕ W)) ∩
              Finset.univ.filter (fun v => v ∈ Comp ∧ v ∉ Set.range inV)) := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv1).1
        rcases Finset.mem_union.mp hv2 with hv_out | hv_gate
        · obtain ⟨q', -, hqq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv_out).1
          exact Sum.inl_ne_inr hqq.symm
        · exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv_gate).2).2.2 ⟨q, rfl⟩
      have hdisj2 : Disjoint
          (Finset.univ.image (fun q : W => outV q) ∩ Finset.univ.filter (· ∈ Comp))
          (Finset.univ.image (fun u : S.V => (.inl u : S.V ⊕ W)) ∩
            Finset.univ.filter (fun v => v ∈ Comp ∧ v ∉ Set.range inV)) := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv1).1
        obtain ⟨u, -, hu⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv2).1
        exact Sum.inl_ne_inr hu
      rw [hpart, Finset.sum_union hdisj1, Finset.sum_union hdisj2]
      have hs1 : (Finset.univ.image (fun q : W => inV q) ∩ Finset.univ.filter (· ∈ Comp)) =
          (Finset.univ.filter (· ∈ W_in)).image inV := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_filter, W_in, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨q, rfl⟩, hq⟩; exact ⟨q, hq, rfl⟩
        · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q, rfl⟩, hq⟩
      have hs2 : (Finset.univ.image (fun q : W => outV q) ∩ Finset.univ.filter (· ∈ Comp)) =
          (Finset.univ.filter (· ∈ W_in)).image outV := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_filter, W_in, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨q, rfl⟩, hq⟩; exact ⟨q, (hreach_mem q).mpr hq, rfl⟩
        · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q, rfl⟩, (hreach_mem q).mp hq⟩
      have hs3 : (Finset.univ.image (fun u : S.V => (.inl u : S.V ⊕ W)) ∩
            Finset.univ.filter (fun v => v ∈ Comp ∧ v ∉ Set.range inV)) =
          (Finset.univ.filter (· ∈ I_gate)).image Sum.inl := by
        ext (u | q)
        · simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, Sum.inl.injEq,
            exists_eq, exists_eq_right, Finset.mem_filter, Set.mem_range, inV,
            Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, I_gate, mem_ofPred_eq]
        · simp
      have hcardW : (Finset.univ.filter (· ∈ W_in)).card = W_in.ncard := by
        rw [← ncard_coe_finset]; congr 1; ext q; simp
      have hcardI : (Finset.univ.filter (· ∈ I_gate)).card = I_gate.ncard := by
        rw [← ncard_coe_finset]; congr 1; ext u; simp
      rw [hs1, hs2, hs3, Finset.sum_image (fun _ _ _ _ h => inV.injective h),
        Finset.sum_image (fun _ _ _ _ h => outV.injective h),
        Finset.sum_image (fun _ _ _ _ h => Sum.inl_injective h)]
      have hsum1 : ∑ q ∈ Finset.univ.filter (· ∈ W_in), (G_fin.incidenceSet (inV q)).ncard =
          W_in.ncard := by
        trans ∑ _q ∈ Finset.univ.filter (· ∈ W_in), 1
        · exact Finset.sum_congr rfl fun q _ => S.deg_inVert q
        · rw [Finset.sum_const, smul_eq_mul, mul_one, hcardW]
      have hsum2 : ∑ q ∈ Finset.univ.filter (· ∈ W_in), (G_fin.incidenceSet (outV q)).ncard =
          W_in.ncard := by
        trans ∑ _q ∈ Finset.univ.filter (· ∈ W_in), 1
        · exact Finset.sum_congr rfl fun q _ => by
            change ((capGraph S.G S.tip).incidenceSet (.inr q)).ncard = 1
            rw [capGraph_incidence_inr, ncard_singleton]
        · rw [Finset.sum_const, smul_eq_mul, mul_one, hcardW]
      have hsum3 : ∑ u ∈ Finset.univ.filter (· ∈ I_gate), (G_fin.incidenceSet (.inl u)).ncard =
          d * I_gate.ncard := by
        trans ∑ _u ∈ Finset.univ.filter (· ∈ I_gate), d
        · exact Finset.sum_congr rfl fun u hu => S.deg_gate u (Finset.mem_filter.mp hu).2.2
        · rw [Finset.sum_const, smul_eq_mul, mul_comm, hcardI]
      rw [hsum1, hsum2, hsum3]
      omega
    have hcard_Comp : Comp.ncard = 2 * W_in.ncard + I_gate.ncard := by
      have h1 : Comp.ncard = ∑ _w : Comp, 1 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
          Nat.card_coe_set_eq]
      -- Same partition!
      have hrew : (∑ _w : Comp, 1) = ∑ _v ∈ Finset.univ.filter (· ∈ Comp), 1 :=
        (Finset.sum_subtype (Finset.univ.filter (· ∈ Comp))
          (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
          fun _ => 1).symm
      rw [h1, hrew, Finset.sum_const, smul_eq_mul, mul_one]
      have hbij : (Finset.univ.filter (· ∈ Comp)).card =
          (Finset.univ.filter (· ∈ W_in)).card +
            (Finset.univ.filter (· ∈ W_in)).card +
            (Finset.univ.filter (· ∈ I_gate)).card := by
        have hpart : (Finset.univ.filter (· ∈ Comp) : Finset (S.V ⊕ W)) =
            (Finset.univ.filter (· ∈ W_in)).image inV ∪
              ((Finset.univ.filter (· ∈ W_in)).image outV ∪
                (Finset.univ.filter (· ∈ I_gate)).image Sum.inl) := by
          ext (u | q)
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_image, inV, outV, Function.Embedding.trans_apply,
              Function.Embedding.coeFn_mk, Sum.inl.injEq, reduceCtorEq, and_false, exists_false,
              exists_eq_right, false_or, W_in, I_gate, mem_ofPred_eq, Set.mem_range]
            by_cases hu : ∃ y, S.inVert y = u
            · obtain ⟨y, rfl⟩ := hu
              exact ⟨fun h => Or.inl ⟨y, h, rfl⟩,
                fun h => h.elim (fun ⟨y', hy', hyy⟩ => S.inVert.injective hyy ▸ hy')
                  fun h' => absurd ⟨y, rfl⟩ h'.2⟩
            · exact ⟨fun h => Or.inr ⟨h, hu⟩,
                fun h => h.elim (fun ⟨y, _, hy⟩ => absurd ⟨y, hy⟩ hu) And.left⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_image, inV, outV, Function.Embedding.trans_apply,
              Function.Embedding.coeFn_mk, reduceCtorEq, Sum.inr.injEq, and_false, exists_false,
              exists_eq_right, false_or, or_false, W_in, mem_ofPred_eq]
            exact (hreach_mem q).symm
        have hd1 : Disjoint ((Finset.univ.filter (· ∈ W_in)).image inV)
            ((Finset.univ.filter (· ∈ W_in)).image outV ∪
              (Finset.univ.filter (· ∈ I_gate)).image Sum.inl) := by
          rw [Finset.disjoint_left]
          rintro _ hv1 hv2
          obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv1
          rcases Finset.mem_union.mp hv2 with hv_out | hv_gate
          · obtain ⟨q', -, hqq⟩ := Finset.mem_image.mp hv_out
            exact Sum.inl_ne_inr hqq.symm
          · obtain ⟨u, hu, huq⟩ := Finset.mem_image.mp hv_gate
            exact (Finset.mem_filter.mp hu).2.2 ⟨q, Sum.inl.inj huq.symm⟩
        have hd2 : Disjoint ((Finset.univ.filter (· ∈ W_in)).image outV)
            ((Finset.univ.filter (· ∈ I_gate)).image Sum.inl) := by
          rw [Finset.disjoint_left]
          rintro _ hv1 hv2
          obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv1
          obtain ⟨u, -, huq⟩ := Finset.mem_image.mp hv2
          exact Sum.inl_ne_inr huq
        rw [hpart, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
          Finset.card_image_of_injective _ inV.injective,
          Finset.card_image_of_injective _ outV.injective,
          Finset.card_image_of_injective _ Sum.inl_injective, add_assoc]
      have hcardW : (Finset.univ.filter (· ∈ W_in)).card = W_in.ncard := by
        rw [← ncard_coe_finset]; congr 1; ext q; simp
      have hcardI : (Finset.univ.filter (· ∈ I_gate)).card = I_gate.ncard := by
        rw [← ncard_coe_finset]; congr 1; ext u; simp
      rw [hbij, hcardW, hcardI]
      omega
    obtain ⟨hc1, hc2⟩ := S.card_V
    rw [Multigraph.cycleRankOn]
    rcases hd with rfl | rfl <;> omega
  · -- Contraction identity
    intro y x
    rw [S.contract y x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Fintype.prod_sum_type]
    have hprod_inr : (∏ q : W, F_fin (.inr q) x y γ) =
        S.scalar * ∏ q : W, S.tipMat q (y q) (γ (.inr q)) := by
      simp only [F_fin]
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q_star)]
      simp only [↓reduceIte]
      have h1 : (∏ x_1 ∈ Finset.univ.erase q_star,
          if x_1 = q_star then S.scalar else 1) = 1 :=
        Finset.prod_eq_one fun q hq => by simp only [(Finset.mem_erase.mp hq).1, ↓reduceIte]
      rw [h1, mul_one]
    rw [hprod_inr]
    ring
  · -- Input locality
    rintro (u | q) x₁ x₂ y γ h
    · exact S.loc_in u x₁ x₂ γ fun q' hq' => h q' (congrArg Sum.inl hq')
    · rfl
  · -- Output locality
    rintro (u | q) x y₁ y₂ γ h
    · rfl
    · simp only [F_fin, h q rfl]
  · -- Edge locality
    rintro (u | q) x y γ₁ γ₂ h
    · exact S.loc_edge u x γ₁ γ₂ h
    · simp only [F_fin, h (by rw [capGraph_incidence_inr]; exact mem_singleton _)]

/-- Every list of active gates compiles into a `CappedWireNet 4 W` (`d = 4`), and into a
`CappedWireNet 3 W` (`d = 3`) when all arity-two gates satisfy `HasBondRankTwo`. -/
private theorem exists_cappedWireNet {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (L : List (ActiveGate W)) :
    CappedWireNet 4 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length ∧
      ((∀ g ∈ L, ∀ h : g.1.val = 2, HasBondRankTwo (h ▸ g.2.1)) →
        CappedWireNet 3 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length) := by
  suffices hopen :
      Nonempty (OpenState 4 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length) ∧
        ((∀ g ∈ L, ∀ h : g.1.val = 2, HasBondRankTwo (h ▸ g.2.1)) →
          Nonempty (OpenState 3 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length)) by
    exact ⟨let ⟨S₄⟩ := hopen.1; S₄.toCappedWireNet (Or.inr rfl),
      fun hb => let ⟨S₃⟩ := hopen.2 hb; S₃.toCappedWireNet (Or.inl rfl)⟩
  induction L using List.reverseRecOn with
  | nil =>
    exact ⟨⟨openStateNil 4 W⟩, fun _ => ⟨openStateNil 3 W⟩⟩
  | append_singleton L g ih =>
    have hlen_app : ((L ++ [g]).filter fun a => decide (a.1.val = 2)).length =
        (L.filter fun a => decide (a.1.val = 2)).length + (if g.1.val = 2 then 1 else 0) := by
      simp only [List.filter_append, List.filter_cons, List.filter_nil, List.length_append,
        decide_eq_true_eq]
      split_ifs <;> rfl
    have heval_app : (evalAct (L ++ [g]) : Matrix (W → Bool) (W → Bool) ℂ) =
        (placeAct g : Matrix _ _ ℂ) * (evalAct L : Matrix _ _ ℂ) := by
      rw [evalAct_append]
      simp only [evalAct, one_mul, Submonoid.coe_mul]
    rw [hlen_app, heval_app]
    obtain ⟨⟨S₄⟩, h₃⟩ := ih
    rcases (by omega : g.1.val = 0 ∨ g.1.val = 1 ∨ g.1.val = 2) with h0 | h1 | h2
    · simp only [h0, (by decide : (0 : ℕ) ≠ 2), ↓reduceIte, add_zero]
      exact ⟨⟨openStateZero S₄ g h0⟩, fun hb =>
        let ⟨S₃⟩ := h₃ fun a ha => hb a (List.mem_append_left _ ha)
        ⟨openStateZero S₃ g h0⟩⟩
    · simp only [h1, (by decide : (1 : ℕ) ≠ 2), ↓reduceIte, add_zero]
      exact ⟨⟨openStateOne S₄ g h1⟩, fun hb =>
        let ⟨S₃⟩ := h₃ fun a ha => hb a (List.mem_append_left _ ha)
        ⟨openStateOne S₃ g h1⟩⟩
    · simp only [h2, ↓reduceIte]
      refine ⟨⟨openStateTwoDegFour S₄ g h2⟩, fun hb => ?_⟩
      obtain ⟨S₃⟩ := h₃ fun a ha => hb a (List.mem_append_left _ ha)
      exact ⟨openStateTwoDegThree S₃ g h2
        (hb g (List.mem_append_right _ (List.mem_singleton.mpr rfl)) h2)⟩

/-! ### Amplitude and probability factorizations across an arbitrary vertex cut -/

open Classical in
/-- **Amplitude cut factorization.** In any `CappedWireNet`, across any vertex cut `P ⊆ V_fin`,
`M y x` factors as a sum over `τ : G.edgeCut P → Bool` of
`Φ_P(x_P, y_P, τ) * Ψ_{Pᶜ}(x_{Pᶜ}, y_{Pᶜ}, τ)`. -/
private theorem amplitude_cut_factorization {V_fin E_fin W : Type}
    [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : W ↪ V_fin)
    (F : V_fin → (W → Bool) → (W → Bool) → (E_fin → Bool) → ℂ)
    {M : Matrix (W → Bool) (W → Bool) ℂ}
    (hcontract : ∀ y x : W → Bool, M y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (P : Set V_fin) :
    let XP : Set W := {q | inVert q ∈ P}
    let YP : Set W := {q | outVert q ∈ P}
    let Ecut : Set E_fin := G.edgeCut P
    ∃ (Φ : (XP → Bool) → (YP → Bool) → (Ecut → Bool) → ℂ)
      (Ψ : (↥XPᶜ → Bool) → (↥YPᶜ → Bool) → (Ecut → Bool) → ℂ),
      ∀ (x : W → Bool) (y : W → Bool),
        M y x = ∑ τ : Ecut → Bool,
          Φ (XP.domRestrict x) (YP.domRestrict y) τ *
            Ψ (XPᶜ.domRestrict x) (YPᶜ.domRestrict y) τ := by
  classical
  intro XP YP Ecut
  let Ein : Set E_fin := {e | G.src e ∈ P ∧ G.tgt e ∈ P}
  let Eout : Set E_fin := {e | G.src e ∉ P ∧ G.tgt e ∉ P}
  -- Equivalence `(E_fin → Bool) ≃ (Ecut → Bool) × ((Ein → Bool) × (Eout → Bool))`.
  have hpart_e (e : E_fin) :
      (e ∈ Ecut ∧ e ∉ Ein ∧ e ∉ Eout) ∨
        (e ∉ Ecut ∧ e ∈ Ein ∧ e ∉ Eout) ∨
        (e ∉ Ecut ∧ e ∉ Ein ∧ e ∈ Eout) := by
    simp only [Ecut, Ein, Eout, Multigraph.mem_edgeCut, mem_ofPred_eq]
    by_cases hs : G.src e ∈ P <;> by_cases ht : G.tgt e ∈ P <;> tauto
  let glueE (τ : Ecut → Bool) (γ_in : Ein → Bool) (γ_out : Eout → Bool) (e : E_fin) : Bool :=
    if hc : e ∈ Ecut then τ ⟨e, hc⟩
    else if hi : e ∈ Ein then γ_in ⟨e, hi⟩
    else if ho : e ∈ Eout then γ_out ⟨e, ho⟩
    else false
  let eqvE : (E_fin → Bool) ≃ (Ecut → Bool) × ((Ein → Bool) × (Eout → Bool)) :=
    { toFun := fun γ => (Ecut.domRestrict γ, (Ein.domRestrict γ, Eout.domRestrict γ))
      invFun := fun p => glueE p.1 p.2.1 p.2.2
      left_inv := fun γ => by
        ext e
        rcases hpart_e e with ⟨hc, _, _⟩ | ⟨hc, hi, _⟩ | ⟨hc, hi, ho⟩
        · simp only [glueE, hc, ↓reduceDIte, Set.domRestrict_apply]
        · simp only [glueE, hc, hi, ↓reduceDIte, Set.domRestrict_apply]
        · simp only [glueE, hc, hi, ho, ↓reduceDIte, Set.domRestrict_apply]
      right_inv := fun ⟨τ, γ_in, γ_out⟩ => by
        refine Prod.ext (funext fun ⟨e, hc⟩ => ?_) (Prod.ext (funext fun ⟨e, hi⟩ => ?_)
          (funext fun ⟨e, ho⟩ => ?_))
        · simp only [Set.domRestrict_apply, glueE, hc, ↓reduceDIte]
        · rcases hpart_e e with ⟨hc, hni, _⟩ | ⟨hc, _, _⟩ | ⟨_, hni, _⟩
          · exact absurd hi hni
          · simp only [Set.domRestrict_apply, glueE, hc, hi, ↓reduceDIte]
          · exact absurd hi hni
        · rcases hpart_e e with ⟨_, _, hno⟩ | ⟨_, _, hno⟩ | ⟨hc, hi, _⟩
          · exact absurd ho hno
          · exact absurd ho hno
          · simp only [Set.domRestrict_apply, glueE, hc, hi, ho, ↓reduceDIte] }
  let x0P (xP : XP → Bool) : W → Bool := fun q => if hq : q ∈ XP then xP ⟨q, hq⟩ else false
  let y0P (yP : YP → Bool) : W → Bool := fun q => if hq : q ∈ YP then yP ⟨q, hq⟩ else false
  let x0Pc (xPc : ↥XPᶜ → Bool) : W → Bool := fun q => if hq : q ∈ XPᶜ then xPc ⟨q, hq⟩ else false
  let y0Pc (yPc : ↥YPᶜ → Bool) : W → Bool := fun q => if hq : q ∈ YPᶜ then yPc ⟨q, hq⟩ else false
  let Φ (xP : XP → Bool) (yP : YP → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ γ_in : Ein → Bool, ∏ v ∈ Finset.univ.filter (· ∈ P),
      F v (x0P xP) (y0P yP) (glueE τ γ_in fun _ => false)
  let Ψ (xPc : ↥XPᶜ → Bool) (yPc : ↥YPᶜ → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ γ_out : Eout → Bool, ∏ v ∈ Finset.univ.filter (· ∉ P),
      F v (x0Pc xPc) (y0Pc yPc) (glueE τ (fun _ => false) γ_out)
  refine ⟨Φ, Ψ, fun x y => ?_⟩
  rw [hcontract y x,
    ← Fintype.sum_equiv eqvE.symm (fun p => ∏ v : V_fin, F v x y (eqvE.symm p)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  dsimp only [Φ, Ψ]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun γ_in _ => Finset.sum_congr rfl fun γ_out _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ P)]
  congr 1
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvP : v ∈ P := (Finset.mem_filter.mp hv).2
    have h1 := hloc_in v x (x0P (XP.domRestrict x)) y (glueE τ γ_in γ_out) fun q hq => by
      have hqP : q ∈ XP := by change inVert q ∈ P; rwa [hq]
      simp only [x0P, hqP, ↓reduceDIte, Set.domRestrict_apply]
    have h2 := hloc_out v (x0P (XP.domRestrict x)) y (y0P (YP.domRestrict y))
        (glueE τ γ_in γ_out) fun q hq => by
      have hqP : q ∈ YP := by change outVert q ∈ P; rwa [hq]
      simp only [y0P, hqP, ↓reduceDIte, Set.domRestrict_apply]
    have h3 := hloc_edge v (x0P (XP.domRestrict x)) (y0P (YP.domRestrict y))
        (glueE τ γ_in γ_out) (glueE τ γ_in fun _ => false) fun e he => by
      have hnot_out : e ∉ Eout := by
        rcases he with hs | ht
        · exact fun h => h.1 (hs.symm ▸ hvP)
        · exact fun h => h.2 (ht.symm ▸ hvP)
      simp only [glueE, hnot_out, ↓reduceDIte]
    exact (h1.trans h2).trans h3
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvPc : v ∉ P := (Finset.mem_filter.mp hv).2
    have h1 := hloc_in v x (x0Pc (XPᶜ.domRestrict x)) y (glueE τ γ_in γ_out) fun q hq => by
      have hqPc : q ∈ XPᶜ := by change inVert q ∉ P; rwa [hq]
      simp only [x0Pc, hqPc, ↓reduceDIte, Set.domRestrict_apply]
    have h2 := hloc_out v (x0Pc (XPᶜ.domRestrict x)) y (y0Pc (YPᶜ.domRestrict y))
        (glueE τ γ_in γ_out) fun q hq => by
      have hqPc : q ∈ YPᶜ := by change outVert q ∉ P; rwa [hq]
      simp only [y0Pc, hqPc, ↓reduceDIte, Set.domRestrict_apply]
    have h3 := hloc_edge v (x0Pc (XPᶜ.domRestrict x)) (y0Pc (YPᶜ.domRestrict y))
        (glueE τ γ_in γ_out) (glueE τ (fun _ => false) γ_out) fun e he => by
      have hnot_in : e ∉ Ein := by
        rcases he with hs | ht
        · exact fun h => hvPc (hs ▸ h.1)
        · exact fun h => hvPc (ht ▸ h.2)
      simp only [glueE, hnot_in, ↓reduceDIte]
    exact (h1.trans h2).trans h3

end WireNetwork

/-! ### Quantum circuit observables: acceptance, correlation, state fidelity, and linear maps -/

private theorem glue_left_injective {n N : ℕ} (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) :
    Function.Injective (fun x : Fin n → Bool => Quantum.glue e x x₀) := fun x₁ x₂ h =>
  funext fun i => by
    have hi : Quantum.glue e x₁ x₀ (e i) = Quantum.glue e x₂ x₀ (e i) := congrFun h (e i)
    rwa [Quantum.glue_apply_emb, Quantum.glue_apply_emb] at hi

/-- Acceptance probability of measuring qubit `q_out` in `|1⟩` (`true`) after running `C` on
`|Quantum.glue e x x₀⟩`. -/
@[expose]
noncomputable def quantumAcceptProb {n N : ℕ} (C : Quantum.Circuit N) (q_out : Fin N)
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (x : Fin n → Bool) : ℝ :=
  Quantum.measureProb (C.run (Quantum.glue e x x₀)) (Finset.univ.filter fun y => y q_out = true)

theorem quantumAcceptProb_nonneg {n N : ℕ} (C : Quantum.Circuit N) (q_out : Fin N)
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (x : Fin n → Bool) :
    0 ≤ quantumAcceptProb C q_out e x₀ x :=
  Quantum.measureProb_nonneg _ _

theorem quantumAcceptProb_le_one {n N : ℕ} (C : Quantum.Circuit N) (q_out : Fin N)
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (x : Fin n → Bool) :
    quantumAcceptProb C q_out e x₀ x ≤ 1 := by
  calc quantumAcceptProb C q_out e x₀ x
      ≤ Quantum.measureProb (C.run (Quantum.glue e x x₀)) Finset.univ :=
        Quantum.measureProb_le_measureProb_univ _ _
    _ = ‖C.run (Quantum.glue e x x₀)‖ ^ 2 := Quantum.measureProb_univ _
    _ = 1 := by rw [Quantum.Circuit.norm_run, one_pow]

/-- Correlation `𝔼_x [±1_{x ∈ S} · (2 p(x) - 1)]` between a target set `S ⊆ Bool^n` and an
acceptance-probability function `p : (Fin n → Bool) → ℝ`. -/
@[expose]
noncomputable def quantumCorrelation {n : ℕ} (S : Set (Fin n → Bool))
    (p : (Fin n → Bool) → ℝ) : ℝ :=
  open Classical in
  (∑ x : Fin n → Bool, (if x ∈ S then (1 : ℝ) else -1) * (2 * p x - 1)) / (2 : ℝ) ^ n

/-- The `n`-qubit computational-basis phase state
`2^{-n/2} ∑_{z : Bool^n} (-1)^{BitString.quadForm Q z} |Quantum.glue e z x₀⟩`, embedded via
`Quantum.embedState`. -/
noncomputable def phaseState {n N : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) : Quantum.Qubits N :=
  Quantum.embedState e x₀
    (WithLp.toLp 2 fun z : Fin n → Bool =>
      (((1 / √2) ^ n : ℝ) : ℂ) * (if BitString.quadForm Q z then -1 else 1))

theorem norm_phaseState {n N : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) : ‖phaseState Q e x₀‖ = 1 := by
  rw [phaseState, LinearIsometry.norm_map]
  set ψ : Quantum.Qubits n := WithLp.toLp 2 fun z : Fin n → Bool =>
    (((1 / √2) ^ n : ℝ) : ℂ) * (if BitString.quadForm Q z then -1 else 1)
  have hsq : ‖ψ‖ ^ 2 = 1 := by
    rw [← Quantum.measureProb_univ, Quantum.measureProb]
    have hterm (z : Fin n → Bool) : ‖ψ.ofLp z‖ ^ 2 = (1 / 2 : ℝ) ^ n := by
      have hsign_norm : ‖(if BitString.quadForm Q z then (-1 : ℂ) else 1)‖ = 1 := by
        split_ifs <;> simp
      simp only [ψ, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / √2) ^ n), hsign_norm, mul_one]
      rw [← pow_mul, mul_comm n 2, pow_mul, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow, mul_one_div_cancel (by norm_num),
      one_pow]
  nlinarith [norm_nonneg ψ]

/-- Given `Q_sub ⊆ ↥A` inducing `S = {i : Fin n | ⟨e i, _⟩ ∈ Q_sub}`, restricting
`Quantum.glue e (glueS (a, b)) x₀` to `Q_sub` depends only on `a : S → Bool` and restricting to
`Q_subᶜ` depends only on `b : ↥Sᶜ → Bool`. -/
private theorem exists_lift_domRestrict_glue {n N : ℕ}
    (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    (Q_sub : Set ↥A)
    [DecidablePred (· ∈ ({i : Fin n | (⟨e i, heA ⟨i, rfl⟩⟩ : ↥A) ∈ Q_sub} : Set (Fin n)))] :
    let S : Set (Fin n) := {i | (⟨e i, heA ⟨i, rfl⟩⟩ : ↥A) ∈ Q_sub}
    let glueS := (Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).symm
    ∃ (liftP : (S → Bool) → (Q_sub → Bool)) (liftPc : (↥Sᶜ → Bool) → (↥Q_subᶜ → Bool)),
      (∀ (a : S → Bool) (b : ↥Sᶜ → Bool),
        Q_sub.domRestrict (A.domRestrict (Quantum.glue e (glueS (a, b)) x₀)) = liftP a) ∧
      (∀ (a : S → Bool) (b : ↥Sᶜ → Bool),
        Q_subᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueS (a, b)) x₀)) = liftPc b) := by
  intro S glueS
  let liftP (a : S → Bool) : Q_sub → Bool := fun q =>
    open Classical in
    if hq : ∃ i : Fin n, e i = q.1 then
      a ⟨Classical.choose hq, by
        have hspec : (⟨e (Classical.choose hq), heA ⟨_, rfl⟩⟩ : ↥A) = q.1 :=
          Subtype.ext (Classical.choose_spec hq)
        change (⟨e (Classical.choose hq), _⟩ : ↥A) ∈ Q_sub
        rw [hspec]; exact q.2⟩
    else x₀ q.1.1
  let liftPc (b : ↥Sᶜ → Bool) : ↥Q_subᶜ → Bool := fun q =>
    open Classical in
    if hq : ∃ i : Fin n, e i = q.1 then
      b ⟨Classical.choose hq, by
        have hspec : (⟨e (Classical.choose hq), heA ⟨_, rfl⟩⟩ : ↥A) = q.1 :=
          Subtype.ext (Classical.choose_spec hq)
        change (⟨e (Classical.choose hq), _⟩ : ↥A) ∉ Q_sub
        rw [hspec]; exact q.2⟩
    else x₀ q.1.1
  refine ⟨liftP, liftPc, fun a b => ?_, fun a b => ?_⟩
  · ext q
    simp only [Set.domRestrict_apply, liftP]
    by_cases hq : ∃ i, e i = q.1.1
    · simp only [hq, ↓reduceDIte]
      have hg : Quantum.glue e (glueS (a, b)) x₀ q.1.1 = glueS (a, b) (Classical.choose hq) :=
        (congrArg (Quantum.glue e (glueS (a, b)) x₀) (Classical.choose_spec hq)).symm.trans
          (Quantum.glue_apply_emb e (glueS (a, b)) x₀ (Classical.choose hq))
      rw [hg]
      have hm : Classical.choose hq ∈ S := by
        have hs : (⟨e (Classical.choose hq), heA ⟨_, rfl⟩⟩ : ↥A) = q.1 :=
          Subtype.ext (Classical.choose_spec hq)
        change (⟨e (Classical.choose hq), _⟩ : ↥A) ∈ Q_sub
        rw [hs]; exact q.2
      exact congrFun (congrArg Prod.fst
        ((Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).apply_symm_apply (a, b)))
        ⟨Classical.choose hq, hm⟩
    · simp only [hq, ↓reduceDIte]
      exact Quantum.glue_of_not e _ x₀ fun i hi => hq ⟨i, hi⟩
  · ext q
    simp only [Set.domRestrict_apply, liftPc]
    by_cases hq : ∃ i, e i = q.1.1
    · simp only [hq, ↓reduceDIte]
      have hg : Quantum.glue e (glueS (a, b)) x₀ q.1.1 = glueS (a, b) (Classical.choose hq) :=
        (congrArg (Quantum.glue e (glueS (a, b)) x₀) (Classical.choose_spec hq)).symm.trans
          (Quantum.glue_apply_emb e (glueS (a, b)) x₀ (Classical.choose hq))
      rw [hg]
      have hm : Classical.choose hq ∈ Sᶜ := by
        have hs : (⟨e (Classical.choose hq), heA ⟨_, rfl⟩⟩ : ↥A) = q.1 :=
          Subtype.ext (Classical.choose_spec hq)
        change (⟨e (Classical.choose hq), _⟩ : ↥A) ∉ Q_sub
        rw [hs]; exact q.2
      exact congrFun (congrArg Prod.snd
        ((Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).apply_symm_apply (a, b)))
        ⟨Classical.choose hq, hm⟩
    · simp only [hq, ↓reduceDIte]
      exact Quantum.glue_of_not e _ x₀ fun i hi => hq ⟨i, hi⟩

/-! ### Core single-cut bounds from `CappedWireNet` -/

section CoreCutBounds

open Classical in
/-- Across any vertex cut `P` of a `CappedWireNet` `G` inducing `X = {i | inVert ⟨e i, _⟩ ∈ P}`,
the acceptance probability `quantumAcceptProb C q_out e x₀` factors as the real part of a bilinear
sum indexed by pairs `(γ₁, γ₂) : (G.edgeCut P → Bool) × (G.edgeCut P → Bool)` of crossing bond
configurations. -/
private theorem exists_quantumAcceptProb_pair_sum {n N : ℕ}
    {C : Quantum.Circuit N} {q_out : Fin N} {e : Fin n ↪ Fin N} (x₀ : Fin N → Bool)
    {A : Set (Fin N)} (heA : Set.range e ⊆ A) (hqA : q_out ∈ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (P : Set V_fin) :
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    let Ecut : Set E_fin := G.edgeCut P
    ∃ (A_pair : (X → Bool) → (Ecut → Bool) × (Ecut → Bool) → ℂ)
      (B_pair : (↥Xᶜ → Bool) → (Ecut → Bool) × (Ecut → Bool) → ℂ),
      ∀ (a : X → Bool) (b : ↥Xᶜ → Bool),
        quantumAcceptProb C q_out e x₀
            ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a, b)) =
          ∑ p : (Ecut → Bool) × (Ecut → Bool),
            ((A_pair a p).re * (B_pair b p).re - (A_pair a p).im * (B_pair b p).im) := by
  classical
  intro X Ecut
  -- Express `quantumAcceptProb C q_out e x₀ x` purely on `↥A → Bool` (inactive wires sum to `1`).
  let q_act : ↥A := ⟨q_out, hqA⟩
  have hprob_act (x : Fin n → Bool) :
      quantumAcceptProb C q_out e x₀ x =
        ∑ yA : ↥A → Bool, (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2 := by
    rw [quantumAcceptProb, Quantum.measureProb]
    have hrun (y : Fin N → Bool) :
        (C.run (Quantum.glue e x x₀)).ofLp y =
          (C.matrix : Matrix _ _ ℂ) y (Quantum.glue e x x₀) := by
      simp only [Quantum.Circuit.run, Quantum.Circuit.eval, Quantum.unitaryEquiv_apply,
        Matrix.mulVec, dotProduct, Quantum.ket_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hfilt_sum : (∑ y ∈ Finset.univ.filter (fun y : Fin N → Bool => y q_out = true),
        ‖(C.run (Quantum.glue e x x₀)).ofLp y‖ ^ 2) =
        ∑ y : Fin N → Bool, (if y q_out = true then (1 : ℝ) else 0) *
          ‖(C.matrix : Matrix _ _ ℂ) y (Quantum.glue e x x₀)‖ ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hrun y]
      split_ifs <;> ring
    rw [hfilt_sum]
    simp_rw [hsplit _ (Quantum.glue e x x₀), norm_mul, mul_pow]
    have hsum_split : (∑ y : Fin N → Bool,
        (if y q_out = true then (1 : ℝ) else 0) *
          (‖(evalAct L : Matrix _ _ ℂ) (A.domRestrict y)
              (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2 *
            ‖∏ q : {q : Fin N // q ∉ A},
              (inactU q : Matrix Bool Bool ℂ) (y q.1) (Quantum.glue e x x₀ q.1)‖ ^ 2)) =
        (∑ yA : ↥A → Bool, (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2) *
        ∑ yAc : {q : Fin N // q ∉ A} → Bool,
          ∏ q : {q : Fin N // q ∉ A},
            ‖(inactU q : Matrix Bool Bool ℂ) (yAc q) (x₀ q.1)‖ ^ 2 := by
      let fA (yA : ↥A → Bool) : ℝ :=
        (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e x x₀))‖ ^ 2
      let fAc (yAc : {q : Fin N // q ∉ A} → Bool) : ℝ :=
        ∏ q : {q : Fin N // q ∉ A}, ‖(inactU q : Matrix Bool Bool ℂ) (yAc q) (x₀ q.1)‖ ^ 2
      let eqvN : (Fin N → Bool) ≃ (↥A → Bool) × ({q : Fin N // q ∉ A} → Bool) :=
        (Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Bool).trans
          (Equiv.prodCongr (Equiv.refl _)
            (Equiv.arrowCongr
              { toFun := fun q => ⟨q.1, q.2⟩
                invFun := fun q => ⟨q.1, q.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl } (Equiv.refl Bool)))
      refine (Fintype.sum_equiv eqvN _ (fun p => fA p.1 * fAc p.2) fun y => ?_).trans ?_
      · have heqv1 : (eqvN y).1 = A.domRestrict y := rfl
        have heqv2 : (eqvN y).2 = fun q => y q.1 := rfl
        have hyq : y q_out = (A.domRestrict y) q_act := rfl
        have hprod_norm :
            ‖∏ q : {q : Fin N // q ∉ A},
              (inactU q : Matrix Bool Bool ℂ) (y q.1) (Quantum.glue e x x₀ q.1)‖ ^ 2 =
            ∏ q : {q : Fin N // q ∉ A},
              ‖(inactU q : Matrix Bool Bool ℂ) (y q.1) (x₀ q.1)‖ ^ 2 := by
          have heq_p : (∏ q : {q : Fin N // q ∉ A},
                (inactU q : Matrix Bool Bool ℂ) (y q.1) (Quantum.glue e x x₀ q.1)) =
              ∏ q : {q : Fin N // q ∉ A},
                (inactU q : Matrix Bool Bool ℂ) (y q.1) (x₀ q.1) :=
            Finset.prod_congr (M := ℂ) rfl fun q _ =>
              congrArg _ (Quantum.glue_of_not e x x₀ fun i hi => q.2 (heA ⟨i, hi⟩))
          rw [heq_p, norm_prod, Finset.prod_pow]
        dsimp only [fA, fAc]
        rw [heqv1, heqv2, hyq, hprod_norm]
        ring
      · rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]
    have hinact_one : (∑ yAc : {q : Fin N // q ∉ A} → Bool,
        ∏ q : {q : Fin N // q ∉ A},
          ‖(inactU q : Matrix Bool Bool ℂ) (yAc q) (x₀ q.1)‖ ^ 2) = 1 := by
      let fQ (q : {q : Fin N // q ∉ A}) (b : Bool) : ℝ :=
        ‖(inactU q : Matrix Bool Bool ℂ) b (x₀ q.1)‖ ^ 2
      refine (Fintype.prod_sum fQ).symm.trans (Finset.prod_eq_one fun q _ => ?_)
      dsimp only [fQ]
      have hu := Matrix.mem_unitaryGroup_iff'.mp (inactU q).2
      have hcol := congrArg Complex.re (congrFun (congrFun hu (x₀ q.1)) (x₀ q.1))
      rw [Matrix.mul_apply, Matrix.one_apply] at hcol
      simp only [↓reduceIte, Complex.one_re, Fintype.sum_bool] at hcol
      rw [Fintype.sum_bool]
      have hnorm_re (b : Bool) :
          ‖(inactU q : Matrix Bool Bool ℂ) b (x₀ q.1)‖ ^ 2 =
            (star ((inactU q : Matrix Bool Bool ℂ)) (x₀ q.1) b *
              (inactU q : Matrix Bool Bool ℂ) b (x₀ q.1)).re := by
        simp only [Matrix.star_apply, RCLike.star_def]
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [hnorm_re false, hnorm_re true, ← Complex.add_re, hcol]
    rw [hsum_split, hinact_one, mul_one]
  -- Factor `quantumAcceptProb` across `(X, Xᶜ)` using `amplitude_cut_factorization`.
  obtain ⟨Φ, Ψ, hamp⟩ := amplitude_cut_factorization G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  let XP : Set ↥A := {q | inVert q ∈ P}
  let YP : Set ↥A := {q | outVert q ∈ P}
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  obtain ⟨liftXP, liftXPc, hdom_XP', hdom_XPc'⟩ :=
    exists_lift_domRestrict_glue e x₀ heA XP
  have hdom_XP (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXP a :=
    hdom_XP' a b
  have hdom_XPc (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXPc b := hdom_XPc' a b
  -- Product indicator on `YP` and `YPᶜ` for `yA q_act = true`:
  let wYP (yP : YP → Bool) : ℝ :=
    if hq : q_act ∈ YP then (if yP ⟨q_act, hq⟩ = true then 1 else 0) else 1
  let wYPc (yPc : ↥YPᶜ → Bool) : ℝ :=
    if hq : q_act ∈ YPᶜ then (if yPc ⟨q_act, hq⟩ = true then 1 else 0) else 1
  have hw_prod (yA : ↥A → Bool) :
      (if yA q_act = true then (1 : ℝ) else 0) =
        wYP (YP.domRestrict yA) * wYPc (YPᶜ.domRestrict yA) := by
    by_cases hqP : q_act ∈ YP
    · have hnotPc : q_act ∉ YPᶜ := fun h => h hqP
      simp only [wYP, wYPc, hqP, hnotPc, ↓reduceDIte, Set.domRestrict_apply, mul_one]
      by_cases hy : yA q_act = true <;> simp only [hy, Bool.false_eq_true, ↓reduceIte]
    · have hPc : q_act ∈ YPᶜ := hqP
      simp only [wYP, wYPc, hqP, hPc, ↓reduceDIte, Set.domRestrict_apply, one_mul]
      by_cases hy : yA q_act = true <;> simp only [hy, Bool.false_eq_true, ↓reduceIte]
  let A_pair (a : X → Bool) (p : (Ecut → Bool) × (Ecut → Bool)) : ℂ :=
    ∑ yP : YP → Bool, (wYP yP : ℂ) * Φ (liftXP a) yP p.1 * star (Φ (liftXP a) yP p.2)
  let B_pair (b : ↥Xᶜ → Bool) (p : (Ecut → Bool) × (Ecut → Bool)) : ℂ :=
    ∑ yPc : ↥YPᶜ → Bool, (wYPc yPc : ℂ) * Ψ (liftXPc b) yPc p.1 * star (Ψ (liftXPc b) yPc p.2)
  have hprob_pair (a : X → Bool) (b : ↥Xᶜ → Bool) :
      quantumAcceptProb C q_out e x₀ (glueX (a, b)) =
        ∑ p : (Ecut → Bool) × (Ecut → Bool),
          ((A_pair a p).re * (B_pair b p).re - (A_pair a p).im * (B_pair b p).im) := by
    rw [hprob_act]
    have hstep1 : (∑ yA : ↥A → Bool,
        (if yA q_act = true then (1 : ℝ) else 0) *
          ‖(evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀))‖ ^ 2) =
        ∑ yA : ↥A → Bool,
          (∑ p : (Ecut → Bool) × (Ecut → Bool),
            ((wYP (YP.domRestrict yA) : ℂ) * Φ (liftXP a) (YP.domRestrict yA) p.1 *
                star (Φ (liftXP a) (YP.domRestrict yA) p.2)) *
            ((wYPc (YPᶜ.domRestrict yA) : ℂ) * Ψ (liftXPc b) (YPᶜ.domRestrict yA) p.1 *
                star (Ψ (liftXPc b) (YPᶜ.domRestrict yA) p.2))).re := by
      refine Finset.sum_congr rfl fun yA _ => ?_
      have h1 := hamp (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) yA
      rw [hdom_XP, hdom_XPc] at h1
      set z_amp : ℂ :=
        (evalAct L : Matrix _ _ ℂ) yA (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀))
      have hnorm_sq : ‖z_amp‖ ^ 2 = (z_amp * star z_amp).re := by
        rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [hw_prod yA, hnorm_sq, h1, ← Complex.re_ofReal_mul]
      congr 1
      dsimp only [YP, Ecut]
      rw [star_sum, Finset.sum_mul_sum, ← Fintype.sum_prod_type', Complex.ofReal_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [star_mul']
      ring
    rw [hstep1]
    simp_rw [← Complex.re_sum]
    rw [Finset.sum_comm, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hsplit_y : (∑ yA : ↥A → Bool,
        ((wYP (YP.domRestrict yA) : ℂ) * Φ (liftXP a) (YP.domRestrict yA) p.1 *
            star (Φ (liftXP a) (YP.domRestrict yA) p.2)) *
        ((wYPc (YPᶜ.domRestrict yA) : ℂ) * Ψ (liftXPc b) (YPᶜ.domRestrict yA) p.1 *
            star (Ψ (liftXPc b) (YPᶜ.domRestrict yA) p.2))) = A_pair a p * B_pair b p := by
      dsimp only [A_pair, B_pair]
      rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      exact Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ YP) fun _ => Bool) _ _ fun _ => rfl
    rw [hsplit_y, Complex.mul_re]
  exact ⟨A_pair, B_pair, hprob_pair⟩

open Classical in
/-- Single-cut `BQP` correlation inequality for a `CappedWireNet`: across any vertex cut `P` of `G`
inducing `X = {i | inVert ⟨e i, _⟩ ∈ P}`,
`quantumCorrelation {x | BitString.quadForm Q x} prob ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
  4 * 4 ^ |G.edgeCut P|`. -/
private theorem sq_quantumCorrelation_mul_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {q_out : Fin N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A) (hqA : q_out ∈ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (P : Set V_fin) :
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    quantumCorrelation {x | BitString.quadForm Q x} (quantumAcceptProb C q_out e x₀) ^ 2 *
        (2 : ℝ) ^ (Q + Qᵀ).cutRank X ≤
      4 * (4 : ℝ) ^ (G.edgeCut P).ncard := by
  classical
  intro X
  let Ecut : Set E_fin := G.edgeCut P
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  obtain ⟨A_pair, B_pair, hprob_pair⟩ := exists_quantumAcceptProb_pair_sum x₀ heA hqA hsplit
    G inVert outVert F hcontract hloc_in hloc_out hloc_edge P
  let κ := (((Ecut → Bool) × (Ecut → Bool)) × Bool) ⊕ Unit
  let U_mat : Matrix (X → Bool) κ ℝ := fun a idx => match idx with
    | .inl (p, false) => 2 * (A_pair a p).re
    | .inl (p, true) => -2 * (A_pair a p).im
    | .inr () => -1
  let V_mat : Matrix κ (↥Xᶜ → Bool) ℝ := fun idx b => match idx with
    | .inl (p, false) => (B_pair b p).re
    | .inl (p, true) => (B_pair b p).im
    | .inr () => 1
  have hUV (a : X → Bool) (b : ↥Xᶜ → Bool) :
      (U_mat * V_mat) a b = 2 * quantumAcceptProb C q_out e x₀ (glueX (a, b)) - 1 := by
    rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_bool]
    simp only [Fintype.sum_unique, U_mat, V_mat, mul_one]
    dsimp only [glueX]
    rw [hprob_pair, Finset.mul_sum, sub_eq_add_neg]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hUV_sq : (∑ a : X → Bool, ∑ b : ↥Xᶜ → Bool, (U_mat * V_mat) a b ^ 2) ≤ (2 : ℝ) ^ n := by
    have hle1 (a : X → Bool) (b : ↥Xᶜ → Bool) : (U_mat * V_mat) a b ^ 2 ≤ 1 := by
      rw [hUV]
      have h0 := quantumAcceptProb_nonneg C q_out e x₀ (glueX (a, b))
      have h1 := quantumAcceptProb_le_one C q_out e x₀ (glueX (a, b))
      nlinarith
    calc ∑ a : X → Bool, ∑ b : ↥Xᶜ → Bool, (U_mat * V_mat) a b ^ 2
        ≤ ∑ _a : X → Bool, ∑ _b : ↥Xᶜ → Bool, (1 : ℝ) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hle1 a b
      _ = (Fintype.card (X → Bool) : ℝ) * Fintype.card (↥Xᶜ → Bool) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ = (2 : ℝ) ^ n := by
          have hn : Fintype.card X + Fintype.card ↥Xᶜ = n := by
            rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
              Nat.card_coe_set_eq]
            have hc := ncard_add_ncard_compl X
            rwa [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hc
          simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
          rw [← pow_add, hn]
  have hcorr_sum : quantumCorrelation {x | BitString.quadForm Q x}
        (quantumAcceptProb C q_out e x₀) * (2 : ℝ) ^ n =
      -(∑ a : X → Bool, ∑ b : ↥Xᶜ → Bool,
        Communication.signMatrix ℝ (fun a' b' => BitString.quadForm Q (glueX (a', b'))) a b *
          (U_mat * V_mat) a b) := by
    rw [quantumCorrelation, div_mul_cancel₀ _ (by positivity)]
    rw [← Finset.sum_neg_distrib]
    simp_rw [← Finset.sum_neg_distrib]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool) _ _ fun x => ?_
    have hgx : glueX ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool) x) = x :=
      (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm_apply_apply x
    simp only [Communication.signMatrix_apply, hUV, hgx, mem_ofPred_eq]
    by_cases hqx : BitString.quadForm Q x = true
    · simp only [hqx, ↓reduceIte]; ring
    · simp only [Bool.not_eq_true] at hqx
      simp only [hqx, Bool.false_eq_true, ↓reduceIte]; ring
  have hfrob := Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul Q X U_mat V_mat
  rw [Fintype.card_fin] at hfrob
  have hcard_κ : (Fintype.card κ : ℝ) ≤ 4 * (4 : ℝ) ^ Ecut.ncard := by
    have hE : Fintype.card Ecut = Ecut.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hc : Fintype.card κ = 2 * 4 ^ Ecut.ncard + 1 := by
      simp only [κ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_unit, hE]
      rw [← pow_add, ← two_mul, pow_mul]
      ring
    rw [hc]
    push_cast
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ Ecut.ncard := one_le_pow₀ (by norm_num)
    linarith
  have hsq_corr : (quantumCorrelation {x | BitString.quadForm Q x}
        (quantumAcceptProb C q_out e x₀) * (2 : ℝ) ^ n) ^ 2 =
      (∑ a, ∑ b, Communication.signMatrix ℝ (fun a' b' => BitString.quadForm Q (glueX (a', b')))
        a b * (U_mat * V_mat) a b) ^ 2 := by
    rw [hcorr_sum, neg_sq]
    rfl
  have hmult : (quantumCorrelation {x | BitString.quadForm Q x}
        (quantumAcceptProb C q_out e x₀)) ^ 2 *
        (2 : ℝ) ^ (Q + Qᵀ).cutRank X * ((2 : ℝ) ^ n) ^ 2 ≤
      4 * (4 : ℝ) ^ Ecut.ncard * ((2 : ℝ) ^ n) ^ 2 := by
    calc (quantumCorrelation {x | BitString.quadForm Q x}
            (quantumAcceptProb C q_out e x₀)) ^ 2 *
            (2 : ℝ) ^ (Q + Qᵀ).cutRank X * ((2 : ℝ) ^ n) ^ 2
        = (quantumCorrelation {x | BitString.quadForm Q x}
            (quantumAcceptProb C q_out e x₀) * (2 : ℝ) ^ n) ^ 2 *
            (2 : ℝ) ^ (Q + Qᵀ).cutRank X := by ring
      _ ≤ (Fintype.card κ : ℝ) * (2 : ℝ) ^ n * ∑ a, ∑ b, (U_mat * V_mat) a b ^ 2 := by
          rw [hsq_corr]; exact hfrob
      _ ≤ (4 * (4 : ℝ) ^ Ecut.ncard) * (2 : ℝ) ^ n * (2 : ℝ) ^ n :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcard_κ (by positivity)) hUV_sq
            (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = 4 * (4 : ℝ) ^ Ecut.ncard * ((2 : ℝ) ^ n) ^ 2 := by ring
  exact le_of_mul_le_mul_right hmult (by positivity)

open Classical in
/-- Single-cut `UQP` sign-rank bound: if `quantumAcceptProb C q_out e x₀ x > θ ↔ f x = true`, then
across any cut `P`, `signRank` across `(X, Xᶜ)` is at most `3 * 4 ^ |G.edgeCut P|`. -/
private theorem signRank_uqp_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {q_out : Fin N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A) (hqA : q_out ∈ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    {f : (Fin n → Bool) → Bool} {θ : ℝ}
    (huqp : ∀ x, (if f x then θ < quantumAcceptProb C q_out e x₀ x
      else quantumAcceptProb C q_out e x₀ x < θ))
    (P : Set V_fin) :
    let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    Communication.signRank (fun (a : X → Bool) (b : ↥Xᶜ → Bool) =>
        f ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a, b))) ≤
      3 * 4 ^ (G.edgeCut P).ncard := by
  classical
  intro X
  let Ecut : Set E_fin := G.edgeCut P
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  obtain ⟨A_pair, B_pair, hprob_pair⟩ := exists_quantumAcceptProb_pair_sum x₀ heA hqA hsplit
    G inVert outVert F hcontract hloc_in hloc_out hloc_edge P
  -- `θ - quantumAcceptProb` strictly sign-represents `f (glueX (a, b))`!
  let κ := (((Ecut → Bool) × (Ecut → Bool)) × Bool) ⊕ Unit
  let U_sr : Matrix (X → Bool) κ ℝ := fun a idx => match idx with
    | .inl (p, false) => -(A_pair a p).re
    | .inl (p, true) => (A_pair a p).im
    | .inr () => θ
  let V_sr : Matrix κ (↥Xᶜ → Bool) ℝ := fun idx b => match idx with
    | .inl (p, false) => (B_pair b p).re
    | .inl (p, true) => (B_pair b p).im
    | .inr () => 1
  have hrep : Communication.SignRepresents (U_sr * V_sr) (fun a b => f (glueX (a, b))) := by
    refine Communication.SignRepresents.iff_lt.mpr fun a b => ?_
    have hmul : (U_sr * V_sr) a b = θ - quantumAcceptProb C q_out e x₀ (glueX (a, b)) := by
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_bool]
      simp only [Fintype.sum_unique, U_sr, V_sr, mul_one]
      dsimp only [glueX]
      rw [hprob_pair, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hmul]
    have hu := huqp (glueX (a, b))
    cases hf_ab : f (glueX (a, b))
    · simp only [hf_ab, Bool.false_eq_true, ↓reduceIte] at hu ⊢
      linarith
    · simp only [hf_ab, ↓reduceIte] at hu ⊢
      linarith
  have hcard_κ : Fintype.card κ ≤ 3 * 4 ^ Ecut.ncard := by
    have hE : Fintype.card Ecut = Ecut.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hc : Fintype.card κ = 2 * 4 ^ Ecut.ncard + 1 := by
      simp only [κ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_unit, hE]
      rw [← pow_add, ← two_mul, pow_mul]
      ring
    have h1 : 1 ≤ 4 ^ Ecut.ncard := Nat.one_le_pow _ 4 (by norm_num)
    omega
  exact (Communication.signRank_le_card_of_mul hrep).trans hcard_κ

open Classical in
/-- Single-cut state-preparation fidelity inequality for `phaseState Q e x₀`: across any cut `P`
inducing `Y = {i | outVert ⟨e i, _⟩ ∈ P}`,
`‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 * 2 ^ (Q + Qᵀ).cutRank Y ≤ 4 * 2 ^ |G.edgeCut P|`. -/
private theorem sq_fidelity_phaseState_mul_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (P : Set V_fin) :
    let Y : Set (Fin n) := {i | outVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
    ‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
      4 * (2 : ℝ) ^ (G.edgeCut P).ncard := by
  classical
  intro Y
  obtain ⟨Φ, Ψ, hamp⟩ := amplitude_cut_factorization G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  let XP : Set ↥A := {q | inVert q ∈ P}
  let YP : Set ↥A := {q | outVert q ∈ P}
  let Ecut : Set E_fin := G.edgeCut P
  let glueY := (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm
  let c_inact : ℂ := ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (x₀ q.1) (x₀ q.1)
  obtain ⟨liftYP, liftYPc, hdom_YP', hdom_YPc'⟩ :=
    exists_lift_domRestrict_glue e x₀ heA YP
  have hdom_YP (a : Y → Bool) (b : ↥Yᶜ → Bool) :
      {q | outVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueY (a, b)) x₀)) =
        liftYP a := hdom_YP' a b
  have hdom_YPc (a : Y → Bool) (b : ↥Yᶜ → Bool) :
      {q | outVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueY (a, b)) x₀)) =
        liftYPc b := hdom_YPc' a b
  let amp (z : Fin n → Bool) : ℂ := (C.run x₀).ofLp (Quantum.glue e z x₀)
  have hamp_z (a : Y → Bool) (b : ↥Yᶜ → Bool) :
      amp (glueY (a, b)) =
        ∑ τ : Ecut → Bool,
          (c_inact * Φ (XP.domRestrict (A.domRestrict x₀)) (liftYP a) τ) *
            Ψ (XPᶜ.domRestrict (A.domRestrict x₀)) (liftYPc b) τ := by
    have hrun : amp (glueY (a, b)) =
        (C.matrix : Matrix _ _ ℂ) (Quantum.glue e (glueY (a, b)) x₀) x₀ := by
      simp only [amp, Quantum.Circuit.run, Quantum.Circuit.eval, Quantum.unitaryEquiv_apply,
        Matrix.mulVec, dotProduct, Quantum.ket_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hamp1 := hamp (A.domRestrict x₀) (A.domRestrict (Quantum.glue e (glueY (a, b)) x₀))
    rw [hdom_YP, hdom_YPc] at hamp1
    rw [hrun, hsplit, hamp1]
    have hcin : (∏ q : {q : Fin N // q ∉ A},
        (inactU q : Matrix Bool Bool ℂ)
          (Quantum.glue e (glueY (a, b)) x₀ q.1) (x₀ q.1)) = c_inact := by
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [Quantum.glue_of_not e _ x₀ (fun i hi => q.2 (heA ⟨i, hi⟩))]
    rw [hcin, mul_comm _ c_inact, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  -- Real and imaginary parts of `amp (glueY (a, b))` each factor through `(Ecut → Bool) × Bool`.
  let κ := (Ecut → Bool) × Bool
  let U_re : Matrix (Y → Bool) κ ℝ := fun a p =>
    if p.2 then -(c_inact * Φ (XP.domRestrict (A.domRestrict x₀)) (liftYP a) p.1).im
    else (c_inact * Φ (XP.domRestrict (A.domRestrict x₀)) (liftYP a) p.1).re
  let V_re : Matrix κ (↥Yᶜ → Bool) ℝ := fun p b =>
    if p.2 then (Ψ (XPᶜ.domRestrict (A.domRestrict x₀)) (liftYPc b) p.1).im
    else (Ψ (XPᶜ.domRestrict (A.domRestrict x₀)) (liftYPc b) p.1).re
  let U_im : Matrix (Y → Bool) κ ℝ := fun a p =>
    if p.2 then (c_inact * Φ (XP.domRestrict (A.domRestrict x₀)) (liftYP a) p.1).im
    else (c_inact * Φ (XP.domRestrict (A.domRestrict x₀)) (liftYP a) p.1).re
  let V_im : Matrix κ (↥Yᶜ → Bool) ℝ := fun p b =>
    if p.2 then (Ψ (XPᶜ.domRestrict (A.domRestrict x₀)) (liftYPc b) p.1).re
    else (Ψ (XPᶜ.domRestrict (A.domRestrict x₀)) (liftYPc b) p.1).im
  have hUV_re (a : Y → Bool) (b : ↥Yᶜ → Bool) : (U_re * V_re) a b = (amp (glueY (a, b))).re := by
    rw [hamp_z, Complex.re_sum, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_bool, Complex.mul_re]
    simp only [U_re, V_re, Bool.false_eq_true, ↓reduceIte, neg_mul]
    ring
  have hUV_im (a : Y → Bool) (b : ↥Yᶜ → Bool) : (U_im * V_im) a b = (amp (glueY (a, b))).im := by
    rw [hamp_z, Complex.im_sum, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_bool, Complex.mul_im]
    simp only [U_im, V_im, Bool.false_eq_true, ↓reduceIte]
    ring
  have hnorm_sum_le : (∑ a : Y → Bool, ∑ b : ↥Yᶜ → Bool,
      ((U_re * V_re) a b ^ 2 + (U_im * V_im) a b ^ 2)) ≤ 1 := by
    have h1 (a : Y → Bool) (b : ↥Yᶜ → Bool) :
        (U_re * V_re) a b ^ 2 + (U_im * V_im) a b ^ 2 = ‖amp (glueY (a, b))‖ ^ 2 := by
      rw [hUV_re, hUV_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    simp_rw [h1]
    rw [← Fintype.sum_prod_type']
    have hbij : (∑ p : (Y → Bool) × (↥Yᶜ → Bool), ‖amp (glueY (p.1, p.2))‖ ^ 2) =
        ∑ z : Fin n → Bool, ‖(C.run x₀).ofLp (Quantum.glue e z x₀)‖ ^ 2 :=
      Fintype.sum_equiv glueY _ _ fun p => by simp only [Prod.mk.eta, amp]
    rw [hbij, ← Finset.sum_image (f := fun y => ‖(C.run x₀).ofLp y‖ ^ 2)
      (fun _ _ _ _ h => glue_left_injective e x₀ h)]
    calc ∑ y ∈ Finset.univ.image (fun z => Quantum.glue e z x₀), ‖(C.run x₀).ofLp y‖ ^ 2
        ≤ Quantum.measureProb (C.run x₀) Finset.univ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ = ‖C.run x₀‖ ^ 2 := Quantum.measureProb_univ _
      _ = 1 := by rw [Quantum.Circuit.norm_run, one_pow]
  -- Express `inner ℂ (phaseState Q e x₀) (C.run x₀)` via `U_re * V_re` and `U_im * V_im`.
  set S_mat := Communication.signMatrix ℝ (fun a' b' => BitString.quadForm Q (glueY (a', b')))
  have hinner_eq : inner ℂ (phaseState Q e x₀) (C.run x₀) =
      (((1 / √2) ^ n : ℝ) : ℂ) *
        (((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b : ℝ) : ℂ) +
          Complex.I * ((∑ a, ∑ b, S_mat a b * (U_im * V_im) a b : ℝ) : ℂ)) := by
    rw [PiLp.inner_apply]
    have hsum_z : (∑ y : Fin N → Bool, inner ℂ ((phaseState Q e x₀).ofLp y) ((C.run x₀).ofLp y)) =
        ∑ z : Fin n → Bool,
          (((1 / √2) ^ n : ℝ) : ℂ) *
            ((if BitString.quadForm Q z then -1 else 1) * amp z) := by
      have hite (y : Fin N → Bool) :
          inner ℂ ((phaseState Q e x₀).ofLp y) ((C.run x₀).ofLp y) =
            if Quantum.AgreeOff e y x₀ then
              inner ℂ ((((1 / √2) ^ n : ℝ) : ℂ) * (if BitString.quadForm Q (y ∘ e) then -1 else 1))
                ((C.run x₀).ofLp y)
            else 0 := by
        rw [phaseState, Quantum.embedState_apply]
        split_ifs <;> simp_all
      simp_rw [hite]
      rw [Quantum.sum_agreeOff e x₀]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Quantum.glue_comp, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      have hconj_sign : (starRingEnd ℂ) (if BitString.quadForm Q z then (-1 : ℂ) else 1) =
          if BitString.quadForm Q z then -1 else 1 := by
        cases BitString.quadForm Q z <;> simp
      rw [hconj_sign]
      dsimp only [amp]
      ring
    rw [hsum_z, ← Finset.mul_sum]
    congr 1
    refine (Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool) _
      (fun p => (if BitString.quadForm Q (glueY p) then (-1 : ℂ) else 1) * amp (glueY p))
      (fun z => congrArg (fun w => (if BitString.quadForm Q w then (-1 : ℂ) else 1) * amp w)
        ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm_apply_apply z).symm)).trans ?_
    rw [Fintype.sum_prod_type]
    push_cast
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hsign_eq : (if BitString.quadForm Q (glueY (a, b)) then (-1 : ℂ) else 1) =
        ((S_mat a b : ℝ) : ℂ) := by
      simp only [S_mat, Communication.signMatrix_apply]
      cases BitString.quadForm Q (glueY (a, b)) <;> simp
    rw [← Complex.re_add_im (amp (glueY (a, b))), hUV_re, hUV_im, hsign_eq]
    ring
  have hnorm_inner : ‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 =
      (1 / (2 : ℝ) ^ n) *
        ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
          (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) := by
    rw [hinner_eq, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / √2) ^ n)]
    have h12 : ((1 / √2) ^ n) ^ 2 = 1 / (2 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, div_pow, one_pow, Real.sq_sqrt (by norm_num),
        div_pow, one_pow]
    have hre_im (x_r y_r : ℝ) : ‖(x_r : ℂ) + Complex.I * (y_r : ℂ)‖ ^ 2 = x_r ^ 2 + y_r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, one_mul, zero_add]
      ring
    rw [h12, hre_im]
  have hf_re : (∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
      (Fintype.card κ : ℝ) * (2 : ℝ) ^ Fintype.card (Fin n) * ∑ a, ∑ b, (U_re * V_re) a b ^ 2 :=
    Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul Q Y U_re V_re
  have hf_im : (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
      (Fintype.card κ : ℝ) * (2 : ℝ) ^ Fintype.card (Fin n) * ∑ a, ∑ b, (U_im * V_im) a b ^ 2 :=
    Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul Q Y U_im V_im
  rw [Fintype.card_fin] at hf_re hf_im
  have hcard_κ : (Fintype.card κ : ℝ) = 2 * (2 : ℝ) ^ Ecut.ncard := by
    have hE : Fintype.card Ecut = Ecut.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simp only [κ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hE, mul_comm]
    push_cast; rfl
  rw [hcard_κ] at hf_re hf_im
  rw [hnorm_inner]
  have hsum_frob : ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
        (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y ≤
      2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n := by
    calc ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
            (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y
        ≤ 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n *
            (∑ a, ∑ b, (U_re * V_re) a b ^ 2 + ∑ a, ∑ b, (U_im * V_im) a b ^ 2) := by
          rw [add_mul, mul_add]
          exact add_le_add hf_re hf_im
      _ = 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n *
            ∑ a, ∑ b, ((U_re * V_re) a b ^ 2 + (U_im * V_im) a b ^ 2) := by
          simp_rw [Finset.sum_add_distrib]
      _ ≤ 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n * 1 :=
          mul_le_mul_of_nonneg_left hnorm_sum_le (by positivity)
      _ = 2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n := mul_one _
  calc 1 / (2 : ℝ) ^ n *
        ((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
          (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) *
        (2 : ℝ) ^ (Q + Qᵀ).cutRank Y
      = 1 / (2 : ℝ) ^ n * (((∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 +
          (∑ a, ∑ b, S_mat a b * (U_im * V_im) a b) ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank Y) := by ring
    _ ≤ 1 / (2 : ℝ) ^ n * (2 * (2 : ℝ) ^ Ecut.ncard * (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hsum_frob (by positivity)
    _ = 2 * (2 : ℝ) ^ Ecut.ncard := by field_simp
    _ ≤ 4 * (2 : ℝ) ^ Ecut.ncard := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) Ecut.ncard]

end CoreCutBounds

/-- Boolean matrix-vector multiplication `(x ↦ M *ᵥ x)` viewed on `Fin n → Bool`. -/
@[expose]
def boolMulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → Bool) (i : Fin n) :
    Bool :=
  decide ((M *ᵥ fun j => BitString.bitVal (ZMod 2) (x j)) i = 1)

private def inl2n (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨i.1, by omega⟩

private def inr2n (n : ℕ) (j : Fin n) : Fin (2 * n) :=
  ⟨n + j.1, by omega⟩

private theorem inl2n_injective (n : ℕ) : Function.Injective (inl2n n) :=
  fun _ _ h => Fin.ext (Fin.mk.inj h)

private theorem inr2n_injective (n : ℕ) : Function.Injective (inr2n n) :=
  fun _ _ h => Fin.ext (Nat.add_left_cancel (Fin.mk.inj h))

private theorem disjoint_range_inl2n_inr2n (n : ℕ) :
    Disjoint (Set.range (inl2n n)) (Set.range (inr2n n)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  simp only [inl2n, inr2n] at hval
  omega

/-- Bipartite `(2 n) × (2 n)` block matrix placing `R` on output rows `inr2n n` and input columns
`inl2n n`. -/
noncomputable def linBlockMatrix (n : ℕ) (R : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Matrix.extendBlock (inr2n n) (inl2n n) R

/-- Bisection cut-rank lower bound for `linBlockMatrix n R` when `R` is `t`-submatrix-robust. -/
theorem half_le_cutRank_linBlockMatrix (n : ℕ) {t : ℕ}
    {R : Matrix (Fin n) (Fin n) (ZMod 2)} (hR : R.SubmatrixRobust t)
    {U : Set (Fin (2 * n))} (hU : U.ncard = (2 * n) / 2) :
    (2 * n) / 2 ≤ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U + (2 * t + 1) := by
  have hdiv : (2 * n) / 2 = n := by omega
  rw [hdiv] at hU ⊢
  exact hR.le_cutRank_add (inr2n_injective n) (inl2n_injective n)
    (disjoint_range_inl2n_inr2n n).symm
    (Matrix.submatrix_extendBlock (inr2n_injective n) (inl2n_injective n) R)
    (fun _ _ h => Matrix.extendBlock_eq_zero R h)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hU

private theorem sign_dotProduct_eq_prod {α : Type*} (s : Finset α)
    (y : α → Bool) (v : α → ZMod 2) :
    (if decide (∑ j ∈ s, BitString.bitVal (ZMod 2) (y j) * v j = 1) then (-1 : ℂ) else 1) =
      ∏ j ∈ s, if y j && decide (v j = 1) then (-1 : ℂ) else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
    have hbool : ∀ (b : Bool) (va u : ZMod 2),
        decide (BitString.bitVal (ZMod 2) b * va + u = 1) =
          bne (b && decide (va = 1)) (decide (u = 1)) := by decide
    rw [hbool]
    cases (y a && decide (v a = 1)) <;>
      cases decide (∑ j ∈ s, BitString.bitVal (ZMod 2) (y j) * v j = 1) <;> norm_num

open Classical in
/-- Single-cut linear synthesis bound via Walsh-Hadamard duality on `CappedWireNet`: if `C`
coherently computes `|Quantum.glue e x x₀⟩ ↦ |Quantum.glue e (boolMulVec R x) x₀⟩`, then across any
cut `P`, the joint input/output cut `U ⊆ Fin (2 * n)` satisfies
`(linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤ |G.edgeCut P| + 1`. -/
private theorem cutRank_linBlockMatrix_le_of_capped {n N : ℕ}
    {C : Quantum.Circuit N} {e : Fin n ↪ Fin N} {x₀ : Fin N → Bool}
    {A : Set (Fin N)} (heA : Set.range e ⊆ A)
    {L : List (ActiveGate ↥A)} {inactU : {q : Fin N // q ∉ A} → unitaryGroup Bool ℂ}
    (hsplit : ∀ y x : Fin N → Bool,
      (C.matrix : Matrix _ _ ℂ) y x =
        (evalAct L : Matrix (↥A → Bool) (↥A → Bool) ℂ) (A.domRestrict y) (A.domRestrict x) *
          ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (y q.1) (x q.1))
    {V_fin E_fin : Type} [Fintype V_fin] [Fintype E_fin] [DecidableEq E_fin]
    (G : Multigraph V_fin E_fin) (inVert outVert : ↥A ↪ V_fin)
    (F : V_fin → (↥A → Bool) → (↥A → Bool) → (E_fin → Bool) → ℂ)
    (hcontract : ∀ y x : ↥A → Bool, evalAct L y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ)
    (hloc_in : ∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ)
    (hloc_out : ∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ)
    (hloc_edge : ∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)
    (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (hlin : ∀ x : Fin n → Bool,
      C.run (Quantum.glue e x x₀) = Quantum.ket (Quantum.glue e (boolMulVec R x) x₀))
    (leaf2n : Fin (2 * n) ↪ V_fin)
    (hleaf_in : ∀ i : Fin n, leaf2n (inl2n n i) = inVert ⟨e i, heA ⟨i, rfl⟩⟩)
    (hleaf_out : ∀ j : Fin n, leaf2n (inr2n n j) = outVert ⟨e j, heA ⟨j, rfl⟩⟩)
    (P : Set V_fin) :
    (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank {k | leaf2n k ∈ P} ≤
      (G.edgeCut P).ncard + 1 := by
  classical
  obtain ⟨Φ, Ψ, hamp⟩ := amplitude_cut_factorization G inVert outVert F
    hcontract hloc_in hloc_out hloc_edge P
  let XP : Set ↥A := {q | inVert q ∈ P}
  let YP : Set ↥A := {q | outVert q ∈ P}
  let Ecut : Set E_fin := G.edgeCut P
  let U : Set (Fin (2 * n)) := {k | leaf2n k ∈ P}
  let X : Set (Fin n) := {i | inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P}
  let Y : Set (Fin n) := {j | outVert ⟨e j, heA ⟨j, rfl⟩⟩ ∈ P}
  let glueU := (Equiv.piEquivPiSubtypeProd (· ∈ U) fun _ => Bool).symm
  let glueX := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  let glueY := (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm
  let c_inact : ℂ := ∏ q : {q : Fin N // q ∉ A}, (inactU q : Matrix Bool Bool ℂ) (x₀ q.1) (x₀ q.1)
  obtain ⟨liftXP, liftXPc, hdom_XP', hdom_XPc'⟩ :=
    exists_lift_domRestrict_glue e x₀ heA XP
  have hdom_XP (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXP a :=
    hdom_XP' a b
  have hdom_XPc (a : X → Bool) (b : ↥Xᶜ → Bool) :
      {q | inVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueX (a, b)) x₀)) =
        liftXPc b := hdom_XPc' a b
  obtain ⟨liftYP, liftYPc, hdom_YP', hdom_YPc'⟩ :=
    exists_lift_domRestrict_glue e x₀ heA YP
  have hdom_YP (wP : Y → Bool) (wPc : ↥Yᶜ → Bool) :
      {q | outVert q ∈ P}.domRestrict (A.domRestrict (Quantum.glue e (glueY (wP, wPc)) x₀)) =
        liftYP wP := hdom_YP' wP wPc
  have hdom_YPc (wP : Y → Bool) (wPc : ↥Yᶜ → Bool) :
      {q | outVert q ∈ P}ᶜ.domRestrict (A.domRestrict (Quantum.glue e (glueY (wP, wPc)) x₀)) =
        liftYPc wPc := hdom_YPc' wP wPc
  have hamp_wx (xP : X → Bool) (xPc : ↥Xᶜ → Bool) (wP : Y → Bool) (wPc : ↥Yᶜ → Bool) :
      (if glueY (wP, wPc) = boolMulVec R (glueX (xP, xPc)) then (1 : ℂ) else 0) =
        ∑ τ : Ecut → Bool,
          (c_inact * Φ (liftXP xP) (liftYP wP) τ) * Ψ (liftXPc xPc) (liftYPc wPc) τ := by
    have hket : (if glueY (wP, wPc) = boolMulVec R (glueX (xP, xPc)) then (1 : ℂ) else 0) =
        (C.run (Quantum.glue e (glueX (xP, xPc)) x₀)).ofLp
          (Quantum.glue e (glueY (wP, wPc)) x₀) := by
      rw [hlin, Quantum.ket_apply]
      have hinj : (Quantum.glue e (glueY (wP, wPc)) x₀ =
          Quantum.glue e (boolMulVec R (glueX (xP, xPc))) x₀) ↔
          glueY (wP, wPc) = boolMulVec R (glueX (xP, xPc)) :=
        ⟨fun h => glue_left_injective e x₀ h, fun h => congrArg (Quantum.glue e · x₀) h⟩
      exact (if_congr hinj rfl rfl).symm
    have hrun : (C.run (Quantum.glue e (glueX (xP, xPc)) x₀)).ofLp
          (Quantum.glue e (glueY (wP, wPc)) x₀) =
        (C.matrix : Matrix _ _ ℂ)
          (Quantum.glue e (glueY (wP, wPc)) x₀) (Quantum.glue e (glueX (xP, xPc)) x₀) := by
      simp only [Quantum.Circuit.run, Quantum.Circuit.eval, Quantum.unitaryEquiv_apply,
        Matrix.mulVec, dotProduct, Quantum.ket_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hamp1 :=
      hamp (A.domRestrict (Quantum.glue e (glueX (xP, xPc)) x₀))
        (A.domRestrict (Quantum.glue e (glueY (wP, wPc)) x₀))
    rw [hdom_XP, hdom_XPc, hdom_YP, hdom_YPc] at hamp1
    rw [hket, hrun, hsplit, hamp1]
    have hcin : (∏ q : {q : Fin N // q ∉ A},
        (inactU q : Matrix Bool Bool ℂ) (Quantum.glue e (glueY (wP, wPc)) x₀ q.1)
          (Quantum.glue e (glueX (xP, xPc)) x₀ q.1)) = c_inact := by
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [Quantum.glue_of_not e _ x₀ (fun i hi => q.2 (heA ⟨i, hi⟩)),
        Quantum.glue_of_not e _ x₀ (fun i hi => q.2 (heA ⟨i, hi⟩))]
    rw [hcin, mul_comm _ c_inact, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  -- Extract `(xP, yP)` from `a : U → Bool` and `(xPc, yPc)` from `b : ↥Uᶜ → Bool`.
  have hglue_emb (emb : Fin n → Fin (2 * n)) (S : Set (Fin n)) (hemb : ∀ i, emb i ∈ U ↔ i ∈ S)
      (a : U → Bool) (b : ↥Uᶜ → Bool) (i : Fin n) :
      glueU (a, b) (emb i) =
        (Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).symm
          ((fun k => a ⟨emb k.1, (hemb k.1).mpr k.2⟩),
           (fun k => b ⟨emb k.1, fun h => k.2 ((hemb k.1).mp h)⟩)) i := by
    by_cases hi : i ∈ S
    · have hiU : emb i ∈ U := (hemb i).mpr hi
      have h1 : glueU (a, b) (emb i) = a ⟨emb i, hiU⟩ :=
        congrFun (congrArg Prod.fst
          ((Equiv.piEquivPiSubtypeProd (· ∈ U) fun _ => Bool).apply_symm_apply (a, b))) ⟨emb i, hiU⟩
      have h2 : (Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).symm
          ((fun k => a ⟨emb k.1, (hemb k.1).mpr k.2⟩),
           (fun k => b ⟨emb k.1, fun h => k.2 ((hemb k.1).mp h)⟩)) i = a ⟨emb i, hiU⟩ :=
        congrFun (congrArg Prod.fst
          ((Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).apply_symm_apply _)) ⟨i, hi⟩
      exact h1.trans h2.symm
    · have hiUc : emb i ∈ Uᶜ := fun h => hi ((hemb i).mp h)
      have h1 : glueU (a, b) (emb i) = b ⟨emb i, hiUc⟩ :=
        congrFun (congrArg Prod.snd
          ((Equiv.piEquivPiSubtypeProd (· ∈ U) fun _ => Bool).apply_symm_apply (a, b)))
          ⟨emb i, hiUc⟩
      have h2 : (Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).symm
          ((fun k => a ⟨emb k.1, (hemb k.1).mpr k.2⟩),
           (fun k => b ⟨emb k.1, fun h => k.2 ((hemb k.1).mp h)⟩)) i = b ⟨emb i, hiUc⟩ :=
        congrFun (congrArg Prod.snd
          ((Equiv.piEquivPiSubtypeProd (· ∈ S) fun _ => Bool).apply_symm_apply _)) ⟨i, hi⟩
      exact h1.trans h2.symm
  have hinl_mem (i : Fin n) : inl2n n i ∈ U ↔ i ∈ X := by
    change leaf2n (inl2n n i) ∈ P ↔ inVert ⟨e i, heA ⟨i, rfl⟩⟩ ∈ P
    rw [hleaf_in]
  have hinr_mem (j : Fin n) : inr2n n j ∈ U ↔ j ∈ Y := by
    change leaf2n (inr2n n j) ∈ P ↔ outVert ⟨e j, heA ⟨j, rfl⟩⟩ ∈ P
    rw [hleaf_out]
  let x_of_a (a : U → Bool) : X → Bool := fun i => a ⟨inl2n n i.1, (hinl_mem i.1).mpr i.2⟩
  let y_of_a (a : U → Bool) : Y → Bool := fun j => a ⟨inr2n n j.1, (hinr_mem j.1).mpr j.2⟩
  let x_of_b (b : ↥Uᶜ → Bool) : ↥Xᶜ → Bool :=
    fun i => b ⟨inl2n n i.1, fun h => i.2 ((hinl_mem i.1).mp h)⟩
  let y_of_b (b : ↥Uᶜ → Bool) : ↥Yᶜ → Bool :=
    fun j => b ⟨inr2n n j.1, fun h => j.2 ((hinr_mem j.1).mp h)⟩
  have hglue_inl (a : U → Bool) (b : ↥Uᶜ → Bool) :
      (fun i => glueU (a, b) (inl2n n i)) = glueX (x_of_a a, x_of_b b) :=
    funext (hglue_emb (inl2n n) X hinl_mem a b)
  have hglue_inr (a : U → Bool) (b : ↥Uᶜ → Bool) (j : Fin n) :
      glueU (a, b) (inr2n n j) = glueY (y_of_a a, y_of_b b) j :=
    hglue_emb (inr2n n) Y hinr_mem a b j
  -- Walsh-transform `Φ` over `wP : Y → Bool` and `Ψ` over `wPc : ↥Yᶜ → Bool`.
  let Φ_lin (a : U → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ wP : Y → Bool,
      (∏ j : Y, if y_of_a a j && wP j then (-1 : ℂ) else 1) *
        (c_inact * Φ (liftXP (x_of_a a)) (liftYP wP) τ)
  let Ψ_lin (b : ↥Uᶜ → Bool) (τ : Ecut → Bool) : ℂ :=
    ∑ wPc : ↥Yᶜ → Bool,
      (∏ j : ↥Yᶜ, if y_of_b b j && wPc j then (-1 : ℂ) else 1) *
        Ψ (liftXPc (x_of_b b)) (liftYPc wPc) τ
  set S_mat := Communication.signMatrix ℝ
    (fun a' b' => BitString.quadForm (linBlockMatrix n R) (glueU (a', b')))
  have hsum_τ (a : U → Bool) (b : ↥Uᶜ → Bool) :
      (∑ τ : Ecut → Bool, Φ_lin a τ * Ψ_lin b τ) = ((S_mat a b : ℝ) : ℂ) := by
    have hswap : (∑ τ : Ecut → Bool, Φ_lin a τ * Ψ_lin b τ) =
        ∑ wP : Y → Bool, ∑ wPc : ↥Yᶜ → Bool,
          ((∏ j : Y, if y_of_a a j && wP j then (-1 : ℂ) else 1) *
            (∏ j : ↥Yᶜ, if y_of_b b j && wPc j then (-1 : ℂ) else 1)) *
          ∑ τ : Ecut → Bool,
            (c_inact * Φ (liftXP (x_of_a a)) (liftYP wP) τ) *
              Ψ (liftXPc (x_of_b b)) (liftYPc wPc) τ := by
      dsimp only [Φ_lin, Ψ_lin]
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun wP _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun wPc _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [hswap]
    simp_rw [← hamp_wx (x_of_a a) (x_of_b b)]
    have hprod_y (wP : Y → Bool) (wPc : ↥Yᶜ → Bool) :
        (∏ j : Y, if y_of_a a j && wP j then (-1 : ℂ) else 1) *
          (∏ j : ↥Yᶜ, if y_of_b b j && wPc j then (-1 : ℂ) else 1) =
        ∏ j : Fin n, if glueU (a, b) (inr2n n j) && glueY (wP, wPc) j then (-1 : ℂ) else 1 := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ Y)
        (fun j => if glueU (a, b) (inr2n n j) && glueY (wP, wPc) j then (-1 : ℂ) else 1)]
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        have hy : glueU (a, b) (inr2n n j.1) = y_of_a a j := by
          rw [hglue_inr]
          exact congrFun (congrArg Prod.fst
            ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).apply_symm_apply
              (y_of_a a, y_of_b b))) j
        have hw : glueY (wP, wPc) j.1 = wP j :=
          congrFun (congrArg Prod.fst
            ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).apply_symm_apply (wP, wPc))) j
        rw [hy, hw]
      · refine Finset.prod_congr rfl fun j _ => ?_
        have hy : glueU (a, b) (inr2n n j.1) = y_of_b b j := by
          rw [hglue_inr]
          exact congrFun (congrArg Prod.snd
            ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).apply_symm_apply
              (y_of_a a, y_of_b b))) j
        have hw : glueY (wP, wPc) j.1 = wPc j :=
          congrFun (congrArg Prod.snd
            ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).apply_symm_apply (wP, wPc))) j
        rw [hy, hw]
    simp_rw [hprod_y, ← Fintype.sum_prod_type']
    refine (Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool)
      (fun w =>
        (∏ j : Fin n, if glueU (a, b) (inr2n n j) && w j then (-1 : ℂ) else 1) *
          if w = boolMulVec R (glueX (x_of_a a, x_of_b b)) then 1 else 0)
      (fun p =>
        (∏ j : Fin n, if glueU (a, b) (inr2n n j) && glueY (p.1, p.2) j then (-1 : ℂ) else 1) *
          if glueY (p.1, p.2) = boolMulVec R (glueX (x_of_a a, x_of_b b)) then 1 else 0)
      (fun w => congrArg
        (fun z => (∏ j : Fin n, if glueU (a, b) (inr2n n j) && z j then (-1 : ℂ) else 1) *
          if z = boolMulVec R (glueX (x_of_a a, x_of_b b)) then 1 else 0)
        ((Equiv.piEquivPiSubtypeProd (· ∈ Y) fun _ => Bool).symm_apply_apply w).symm)).symm.trans
      ?_
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      ← hglue_inl a b]
    -- Identify the remaining product with `S_mat a b`.
    have hquad := BitString.quadForm_eq_of_submatrix (inr2n_injective n) (inl2n_injective n)
      (Matrix.submatrix_extendBlock (inr2n_injective n) (inl2n_injective n) R)
      (fun _ _ h => Matrix.extendBlock_eq_zero R h) (glueU (a, b))
    change BitString.quadForm (linBlockMatrix n R) (glueU (a, b)) = _ at hquad
    have hsgn := sign_dotProduct_eq_prod Finset.univ (fun j => glueU (a, b) (inr2n n j))
      (R *ᵥ fun i => BitString.bitVal (ZMod 2) (glueU (a, b) (inl2n n i)))
    simp only [dotProduct] at hquad
    refine hsgn.symm.trans ?_
    rw [← hquad]
    simp only [S_mat, Communication.signMatrix_apply]
    cases BitString.quadForm (linBlockMatrix n R) (glueU (a, b)) <;> simp
  -- Extract real factorization `U_re * V_re = S_mat` of inner dimension `2 * 2 ^ |Ecut|`.
  let κ := (Ecut → Bool) × Bool
  let U_re : Matrix (U → Bool) κ ℝ := fun a p =>
    if p.2 then -(Φ_lin a p.1).im else (Φ_lin a p.1).re
  let V_re : Matrix κ (↥Uᶜ → Bool) ℝ := fun p b =>
    if p.2 then (Ψ_lin b p.1).im else (Ψ_lin b p.1).re
  have hUV (a : U → Bool) (b : ↥Uᶜ → Bool) : (U_re * V_re) a b = S_mat a b := by
    have hre := congrArg Complex.re (hsum_τ a b)
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [← hre, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_bool, Complex.mul_re]
    simp only [U_re, V_re, Bool.false_eq_true, ↓reduceIte, neg_mul]
    ring
  have hfrob :
      (∑ a, ∑ b, S_mat a b * (U_re * V_re) a b) ^ 2 *
        (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      (Fintype.card κ : ℝ) * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) *
        ∑ a, ∑ b, (U_re * V_re) a b ^ 2 :=
    Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul (linBlockMatrix n R) U U_re V_re
  rw [Fintype.card_fin] at hfrob
  have hS_sq (a : U → Bool) (b : ↥Uᶜ → Bool) : S_mat a b ^ 2 = 1 := by
    simp only [S_mat, Communication.signMatrix_apply]
    cases BitString.quadForm (linBlockMatrix n R) (glueU (a, b)) <;> norm_num
  have hcard_ab : (∑ _a : U → Bool, ∑ _b : ↥Uᶜ → Bool, (1 : ℝ)) = (2 : ℝ) ^ (2 * n) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
      Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_add]
    congr 1
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    have hc := ncard_add_ncard_compl U
    rwa [Nat.card_eq_fintype_card (α := Fin (2 * n)), Fintype.card_fin] at hc
  have hsum1 : (∑ a : U → Bool, ∑ b : ↥Uᶜ → Bool, S_mat a b * (U_re * V_re) a b) =
      (2 : ℝ) ^ (2 * n) := by
    simp_rw [hUV, ← sq, hS_sq]
    exact hcard_ab
  have hsum2 : (∑ a : U → Bool, ∑ b : ↥Uᶜ → Bool, (U_re * V_re) a b ^ 2) =
      (2 : ℝ) ^ (2 * n) := by
    simp_rw [hUV, hS_sq]
    exact hcard_ab
  have hcard_κ : (Fintype.card κ : ℝ) = 2 * (2 : ℝ) ^ Ecut.ncard := by
    have hE : Fintype.card Ecut = Ecut.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simp only [κ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hE, mul_comm]
    push_cast; rfl
  have hfrob' :
      ((2 : ℝ) ^ (2 * n)) ^ 2 * (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      (2 * (2 : ℝ) ^ Ecut.ncard) * (2 : ℝ) ^ (2 * n) * (2 : ℝ) ^ (2 * n) :=
    (congrArg (fun x => x ^ 2 * _) hsum1.symm).trans_le
      (hfrob.trans_eq (congrArg₂ (fun x y => x * (2 : ℝ) ^ (2 * n) * y) hcard_κ hsum2))
  have h2pos : (0 : ℝ) < ((2 : ℝ) ^ (2 * n)) ^ 2 := by positivity
  have hpow_r : (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      (2 : ℝ) ^ (Ecut.ncard + 1) := by
    have hmul : (2 : ℝ) ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U *
        ((2 : ℝ) ^ (2 * n)) ^ 2 ≤ (2 : ℝ) ^ (Ecut.ncard + 1) * ((2 : ℝ) ^ (2 * n)) ^ 2 := by
      have hp1 : (2 : ℝ) ^ (Ecut.ncard + 1) = 2 * (2 : ℝ) ^ Ecut.ncard := by rw [pow_succ']
      rw [hp1]
      linarith
    exact le_of_mul_le_mul_right hmul h2pos
  have hpow_nat : 2 ^ (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank U ≤
      2 ^ (Ecut.ncard + 1) := by exact_mod_cast hpow_r
  dsimp only [U, Ecut] at hpow_nat
  by_contra! hgt
  have := Nat.pow_lt_pow_right one_lt_two hgt
  omega

/-! ### Packaged compiled wire network for quantum circuits -/

open Classical in
/-- Packaged finite degree-`d` wire-segment multigraph compiled from `C : Quantum.Circuit N`
with data qubits `e : Fin n ↪ Fin N` and extra tracked qubit `q_extra : Fin N`, bundling the
vertex bound, component cycle-rank inequalities, and single-cut rank/correlation/fidelity bounds. -/
structure CompiledQuantumNet {n N : ℕ} (d : ℕ) (e : Fin n ↪ Fin N) (q_extra : Fin N)
    (C : Quantum.Circuit N) where
  /-- Vertex type of the compiled wire network. -/
  V : Type
  /-- Edge type of the compiled wire network. -/
  E : Type
  instFV : Fintype V
  instFE : Fintype E
  instDE : DecidableEq E
  /-- Underlying loopless degree-`d` multigraph. -/
  G : Multigraph V E
  loopless : G.Loopless
  maxDeg : G.MaxDegreeLE d
  card_V_le : (Nat.card V : ℝ) ≤ 2 * n + 6 * (twoQubitCount C : ℝ) + 2
  /-- Input leaf vertices of the `n` data qubits. -/
  leafIn : Fin n ↪ V
  /-- Output leaf vertices of the `n` data qubits. -/
  leafOut : Fin n ↪ V
  /-- Joint `2 * n` input/output leaf vertices (`inl2n` = inputs, `inr2n` = outputs). -/
  leaf2n : Fin (2 * n) ↪ V
  cycleRank_leafIn_le : ∀ Comp : Set V, G.edgeCut Comp = ∅ →
    Comp.ncard ≤ (G.touching Comp).ncard + 1 →
    G.cycleRankOn Comp + {i : Fin n | leafIn i ∈ Comp}.ncard ≤ twoQubitCount C + 1
  cycleRank_leafOut_le : ∀ Comp : Set V, G.edgeCut Comp = ∅ →
    Comp.ncard ≤ (G.touching Comp).ncard + 1 →
    G.cycleRankOn Comp + {i : Fin n | leafOut i ∈ Comp}.ncard ≤ twoQubitCount C + 1
  cycleRank_leaf2n_le : ∀ Comp : Set V, G.edgeCut Comp = ∅ →
    Comp.ncard ≤ (G.touching Comp).ncard + 1 →
    2 * G.cycleRankOn Comp + {k : Fin (2 * n) | leaf2n k ∈ Comp}.ncard ≤
      2 * (twoQubitCount C + 1)
  sq_quantumCorrelation_mul_le : ∀ (x₀ : Fin N → Bool) (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Set V),
    quantumCorrelation {x | BitString.quadForm Q x} (quantumAcceptProb C q_extra e x₀) ^ 2 *
      (2 : ℝ) ^ (Q + Qᵀ).cutRank {i | leafIn i ∈ P} ≤
      4 * (4 : ℝ) ^ (G.edgeCut P).ncard
  signRank_uqp_le : ∀ (x₀ : Fin N → Bool) {f : (Fin n → Bool) → Bool} {θ : ℝ},
    (∀ x, if f x then θ < quantumAcceptProb C q_extra e x₀ x
      else quantumAcceptProb C q_extra e x₀ x < θ) →
    ∀ P : Set V,
    Communication.signRank (fun (a : {i | leafIn i ∈ P} → Bool)
        (b : ↥{i | leafIn i ∈ P}ᶜ → Bool) =>
      f ((Equiv.piEquivPiSubtypeProd (· ∈ {i | leafIn i ∈ P}) fun _ => Bool).symm (a, b))) ≤
      3 * 4 ^ (G.edgeCut P).ncard
  sq_fidelity_phaseState_mul_le : ∀ (x₀ : Fin N → Bool) (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Set V),
    ‖inner ℂ (phaseState Q e x₀) (C.run x₀)‖ ^ 2 *
      (2 : ℝ) ^ (Q + Qᵀ).cutRank {i | leafOut i ∈ P} ≤
      4 * (2 : ℝ) ^ (G.edgeCut P).ncard
  cutRank_linBlockMatrix_le : ∀ (x₀ : Fin N → Bool) {R : Matrix (Fin n) (Fin n) (ZMod 2)},
    (∀ x, C.run (Quantum.glue e x x₀) = Quantum.ket (Quantum.glue e (boolMulVec R x) x₀)) →
    ∀ P : Set V,
    (linBlockMatrix n R + (linBlockMatrix n R)ᵀ).cutRank {k | leaf2n k ∈ P} ≤
      (G.edgeCut P).ncard + 1

attribute [instance] CompiledQuantumNet.instFV CompiledQuantumNet.instFE CompiledQuantumNet.instDE

/-- **Compile a two-local quantum circuit into a `CompiledQuantumNet`.** Under `AllBondRankTwo C`
(`d = 3`) or `TwoLocal C` (`d = 4`), decoupling inactive qubits and splitting active two-qubit
gates produces a `CompiledQuantumNet d e q_extra C`. -/
theorem exists_compiledQuantumNet {n N d : ℕ} (hd : d = 3 ∨ d = 4)
    (e : Fin n ↪ Fin N) (q_extra : Fin N) {C : Quantum.Circuit N}
    (hmodel : if d = 3 then AllBondRankTwo C else TwoLocal C) :
    Nonempty (CompiledQuantumNet d e q_extra C) := by
  have htwo : TwoLocal C := by
    rcases hd with rfl | rfl
    · simp only [↓reduceIte] at hmodel; exact fun g hg => (hmodel g hg).1
    · simp only [(by decide : 4 ≠ 3), ↓reduceIte] at hmodel; exact hmodel
  classical
  set Aset := activeSet e q_extra C
  have heA : Set.range e ⊆ Aset := range_subset_activeSet e q_extra C
  have hqA : q_extra ∈ Aset := mem_activeSet_extra e q_extra C
  have hneA : Nonempty ↥Aset := ⟨⟨q_extra, hqA⟩⟩
  obtain ⟨L, inactU, hlenL, hbondL, hsplit⟩ :=
    exists_active_split Aset C htwo (touchingIn_activeSet e q_extra C)
  have hcap : CappedWireNet d ↥Aset (evalAct L) (twoQubitCount C) := by
    rw [← hlenL]
    rcases hd with rfl | rfl
    · simp only [↓reduceIte] at hmodel
      exact (exists_cappedWireNet L).2 (hbondL hmodel)
    · exact (exists_cappedWireNet L).1
  obtain ⟨V_fin, E_fin, instFV, _, instFE, instDE, G, inVert, outVert, F,
    hG_loop, hG_deg, hdisj_io, _, hreach, hV_card, hG_ρ, hcontract, hloc_in, hloc_out, hloc_edge⟩ :=
    hcap.exists_net
  let leafIn : Fin n ↪ V_fin :=
    ⟨fun i => inVert ⟨e i, heA ⟨i, rfl⟩⟩,
      fun i j h => e.injective (congrArg Subtype.val (inVert.injective h))⟩
  let leafOut : Fin n ↪ V_fin :=
    ⟨fun i => outVert ⟨e i, heA ⟨i, rfl⟩⟩,
      fun i j h => e.injective (congrArg Subtype.val (outVert.injective h))⟩
  let leaf2n : Fin (2 * n) ↪ V_fin :=
    ⟨fun k => if hk : k.1 < n then inVert ⟨e ⟨k.1, hk⟩, heA ⟨⟨k.1, hk⟩, rfl⟩⟩
        else outVert ⟨e ⟨k.1 - n, by omega⟩, heA ⟨⟨k.1 - n, by omega⟩, rfl⟩⟩,
      fun k₁ k₂ hk => by
        dsimp only at hk
        by_cases h1 : k₁.1 < n <;> by_cases h2 : k₂.1 < n
        · simp only [h1, h2, ↓reduceDIte] at hk
          exact Fin.ext (Fin.mk.inj (e.injective (congrArg Subtype.val (inVert.injective hk))))
        · simp only [h1, h2, ↓reduceDIte] at hk
          exact False.elim (Set.disjoint_left.mp hdisj_io ⟨_, rfl⟩ ⟨_, hk.symm⟩)
        · simp only [h1, h2, ↓reduceDIte] at hk
          exact False.elim (Set.disjoint_left.mp hdisj_io ⟨_, rfl⟩ ⟨_, hk⟩)
        · simp only [h1, h2, ↓reduceDIte] at hk
          have heq := Fin.mk.inj (e.injective (congrArg Subtype.val (outVert.injective hk)))
          ext; omega⟩
  have hleaf_in (i : Fin n) : leaf2n (inl2n n i) = inVert ⟨e i, heA ⟨i, rfl⟩⟩ := by
    change (if hk : (inl2n n i).1 < n then
      inVert ⟨e ⟨(inl2n n i).1, hk⟩, _⟩ else _) = _
    simp only [inl2n, i.isLt, ↓reduceDIte]
  have hleaf_out (j : Fin n) : leaf2n (inr2n n j) = outVert ⟨e j, heA ⟨j, rfl⟩⟩ := by
    have hnot : ¬(n + j.1 < n) := by omega
    change (if hk : (inr2n n j).1 < n then _
      else outVert ⟨e ⟨(inr2n n j).1 - n, _⟩, _⟩) = _
    simp only [inr2n, hnot, ↓reduceDIte]
    congr 1; apply Subtype.ext; dsimp only; congr 1; apply Fin.ext; dsimp only; omega
  have hV_ub : (Nat.card V_fin : ℝ) ≤ 2 * n + 6 * (twoQubitCount C : ℝ) + 2 := by
    rw [Nat.card_eq_fintype_card]
    have hA_card : Fintype.card ↥Aset ≤ n + 2 * twoQubitCount C + 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact ncard_activeSet_le e q_extra htwo
    have hV_nat : Fintype.card V_fin ≤ 2 * n + 6 * twoQubitCount C + 2 := by omega
    exact_mod_cast hV_nat
  have hin_le_act (Comp : Set V_fin) :
      {i : Fin n | leafIn i ∈ Comp}.ncard ≤ {q : ↥Aset | inVert q ∈ Comp}.ncard := by
    let emb : Fin n ↪ ↥Aset :=
      ⟨fun i => ⟨e i, heA ⟨i, rfl⟩⟩, fun i j h => e.injective (congrArg Subtype.val h)⟩
    rw [← ncard_image_of_injective _ emb.injective]
    exact ncard_le_ncard (by rintro _ ⟨i, hi, rfl⟩; exact hi) (toFinite _)
  have hreach_closed (Comp : Set V_fin) (hcut : G.edgeCut Comp = ∅) (q : ↥Aset) :
      inVert q ∈ Comp ↔ outVert q ∈ Comp :=
    mem_closed_iff_of_reachable hcut (hreach q)
  refine ⟨{
    V := V_fin
    E := E_fin
    instFV := instFV
    instFE := instFE
    instDE := instDE
    G := G
    loopless := hG_loop
    maxDeg := hG_deg
    card_V_le := hV_ub
    leafIn := leafIn
    leafOut := leafOut
    leaf2n := leaf2n
    cycleRank_leafIn_le := fun Comp hcut hconn => by
      have := hin_le_act Comp
      have := hG_ρ Comp hcut hconn
      omega
    cycleRank_leafOut_le := fun Comp hcut hconn => by
      have hout_le_in : {i : Fin n | leafOut i ∈ Comp}.ncard ≤
          {q : ↥Aset | inVert q ∈ Comp}.ncard := by
        let emb : Fin n ↪ ↥Aset :=
          ⟨fun i => ⟨e i, heA ⟨i, rfl⟩⟩, fun i j h => e.injective (congrArg Subtype.val h)⟩
        rw [← ncard_image_of_injective _ emb.injective]
        refine ncard_le_ncard ?_ (toFinite _)
        rintro _ ⟨i, hi, rfl⟩
        exact (hreach_closed Comp hcut ⟨e i, heA ⟨i, rfl⟩⟩).mpr hi
      have := hG_ρ Comp hcut hconn
      omega
    cycleRank_leaf2n_le := fun Comp hcut hconn => by
      have hsub2n : {k : Fin (2 * n) | leaf2n k ∈ Comp} ⊆
          inl2n n '' {i | leafIn i ∈ Comp} ∪ inr2n n '' {j | leafIn j ∈ Comp} := by
        intro k hk
        by_cases hk_lt : k.1 < n
        · refine Or.inl ⟨⟨k.1, hk_lt⟩, ?_, Fin.ext rfl⟩
          have heq := hleaf_in ⟨k.1, hk_lt⟩
          change leaf2n k ∈ Comp at hk
          have hk_eq : inl2n n ⟨k.1, hk_lt⟩ = k := Fin.ext rfl
          rwa [← hk_eq, heq] at hk
        · refine Or.inr ⟨⟨k.1 - n, by omega⟩, ?_, Fin.ext (by simp [inr2n]; omega)⟩
          have heq := hleaf_out ⟨k.1 - n, by omega⟩
          change leaf2n k ∈ Comp at hk
          have hk_eq : inr2n n ⟨k.1 - n, by omega⟩ = k := Fin.ext (by simp [inr2n]; omega)
          rw [← hk_eq, heq] at hk
          exact (hreach_closed Comp hcut ⟨e ⟨k.1 - n, by omega⟩, _⟩).mpr hk
      have hcard2n : {k : Fin (2 * n) | leaf2n k ∈ Comp}.ncard ≤
          2 * {q : ↥Aset | inVert q ∈ Comp}.ncard := by
        calc {k : Fin (2 * n) | leaf2n k ∈ Comp}.ncard
            ≤ (inl2n n '' {i | leafIn i ∈ Comp}).ncard +
                (inr2n n '' {j | leafIn j ∈ Comp}).ncard :=
              (ncard_le_ncard hsub2n (toFinite _)).trans (ncard_union_le _ _)
          _ = 2 * {i : Fin n | leafIn i ∈ Comp}.ncard := by
              rw [ncard_image_of_injective _ (inl2n_injective n),
                ncard_image_of_injective _ (inr2n_injective n), two_mul]
          _ ≤ 2 * {q : ↥Aset | inVert q ∈ Comp}.ncard :=
              Nat.mul_le_mul_left 2 (hin_le_act Comp)
      have := hG_ρ Comp hcut hconn
      omega
    sq_quantumCorrelation_mul_le := fun x₀ Q P =>
      sq_quantumCorrelation_mul_le_of_capped (x₀ := x₀) heA hqA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge Q P
    signRank_uqp_le := fun x₀ {_ _} huqp P =>
      signRank_uqp_le_of_capped (x₀ := x₀) heA hqA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge huqp P
    sq_fidelity_phaseState_mul_le := fun x₀ Q P =>
      sq_fidelity_phaseState_mul_le_of_capped (x₀ := x₀) heA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge Q P
    cutRank_linBlockMatrix_le := fun x₀ {_} hlin P =>
      cutRank_linBlockMatrix_le_of_capped (x₀ := x₀) heA hsplit G inVert outVert F
        hcontract hloc_in hloc_out hloc_edge _ hlin leaf2n hleaf_in hleaf_out P
  }⟩

end Cslib.Circuits.Frontier
