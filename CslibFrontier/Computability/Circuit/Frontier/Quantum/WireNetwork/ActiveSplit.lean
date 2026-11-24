/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.PhaseGates
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Fintype.Sum

/-!
# Two-local quantum gate predicates and active-qubit decoupling

Defines the two-qubit gate counter `twoQubitCount`, two-locality `TwoLocal`, and the Schmidt /
bond-rank-two predicates `HasBondRankTwo` and `AllBondRankTwo` (proving `cnot_hasBondRankTwo` and
`controlled_hasBondRankTwo`), together with the internal active-qubit decoupling decomposition for
two-local quantum circuits.

## Main definitions

* `Cslib.Circuits.Frontier.twoQubitCount`: number of two-qubit gates (`g.arity = 2`) in a circuit.
* `Cslib.Circuits.Frontier.TwoLocal`, `Cslib.Circuits.Frontier.HasBondRankTwo`,
  `Cslib.Circuits.Frontier.AllBondRankTwo`: two-qubit locality and bond-rank-two predicates.

## Main results

* `Cslib.Circuits.Frontier.cnot_hasBondRankTwo`,
  `Cslib.Circuits.Frontier.controlled_hasBondRankTwo`: `Gate.cnot` and `Gate.controlled V` have
  bond rank at most two.
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
    simp only [Quantum.Circuit.matrix_nil, evalAct, Submonoid.coe_one, Matrix.one_apply,
      Fintype.prod_boole]
    have hsplit : (y = x) ↔
        (A.domRestrict y = A.domRestrict x ∧ ∀ q : {q : Fin N // q ∉ A}, y q.1 = x q.1) := by
      refine ⟨fun h => h ▸ ⟨rfl, fun _ => rfl⟩, fun ⟨hA, hAc⟩ => funext fun j => ?_⟩
      by_cases hj : j ∈ A
      · exact congrFun hA ⟨j, hj⟩
      · exact hAc ⟨j, hj⟩
    rw [if_congr hsplit rfl rfl]
    by_cases hA : A.domRestrict y = A.domRestrict x
    · by_cases hAc : ∀ q : {q : Fin N // q ∉ A}, y q.1 = x q.1
      · rw [ite_eq_left ⟨hA, hAc⟩, ite_eq_left hA, ite_eq_left hAc, mul_one]
      · rw [ite_eq_right (fun h => hAc h.2), ite_eq_right hAc, mul_zero]
    · rw [ite_eq_right (fun h => hA h.1), ite_eq_right hA, zero_mul]
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
        simp only [Submonoid.coe_one, Matrix.one_apply, Fintype.prod_boole]
        rw [if_congr hoff rfl rfl]
        by_cases hA_cond : ∀ q : ↥A, (¬∃ i, wA i = q) → A.domRestrict z q = A.domRestrict x q
        · by_cases hAc : ∀ q : {q : Fin N // q ∉ A}, z q.1 = x q.1
          · rw [ite_eq_left ⟨hA_cond, hAc⟩, ite_eq_left hA_cond, ite_eq_left hAc, mul_one]; rfl
          · rw [ite_eq_right (fun h => hAc h.2), ite_eq_right hAc, mul_zero]
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

end Cslib.Circuits.Frontier
