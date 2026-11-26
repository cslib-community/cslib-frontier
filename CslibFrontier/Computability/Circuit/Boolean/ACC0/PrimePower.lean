/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
import CslibFrontier.Computability.Circuit.Boolean.Multiplicity
import CslibFrontier.Computability.Circuit.SimulationDepth
import CslibFrontier.Foundations.Data.Nat.Choose.PrimePowerDvd
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset

/-!
# Prime-power modular gates

For a prime `p`, [BeigelTarui1994, Fact 2.2] tests divisibility by `p ^ k`
using the binomial coefficients at `p ^ j` for `j < k`. One conjunction per
subset computes each coefficient as a Hamming weight. This gives a depth-three
gate simulation and the nonuniform class equality `AC0Mod_prime_power_eq`.
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Unbounded

private noncomputable def enumSubsets (m r : Nat) :
    Fin ((Finset.univ : Finset (Fin m)).powersetCard r).card ≃
      ↑((Finset.univ : Finset (Fin m)).powersetCard r) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

private noncomputable def subsetAnd {m : Nat} (s : Finset (Fin m)) : Circuit extSignature m 1 :=
  Circuit.oneGate (σ := extSignature) (.ac (.and s.card)) fun i =>
    (Fintype.equivFinOfCardEq (by simp : Fintype.card ↑s = s.card)).symm i |>.val

private theorem eval_subsetAnd {m p : Nat} (s : Finset (Fin m)) (x : Fin m → Bool) :
    (subsetAnd s).eval (extInterpretation (modGate p)) x 0 = true ↔ ∀ j ∈ s, x j = true := by
  classical
  simp only [subsetAnd, Circuit.eval_oneGate, extInterpretation_ac, interpretation_and,
    decide_eq_true_eq]
  let e := Fintype.equivFinOfCardEq (by simp : Fintype.card ↑s = s.card)
  exact ⟨fun h j hj => by simpa [e] using h (e ⟨j,hj⟩), fun h i => h _ (e.symm i).property⟩

private theorem subset_count {m : Nat} (r : Nat) (x : Fin m → Bool) :
    (Finset.univ.filter (fun i => ∀ j ∈ (enumSubsets m r i).val, x j = true)).card =
      ((Finset.univ.filter fun j => x j = true).card).choose r := by
  classical
  let e := enumSubsets m r
  let yes := Finset.univ.filter (fun i => ∀ j ∈ (e i).val, x j = true)
  let emb : Fin ((Finset.univ : Finset (Fin m)).powersetCard r).card ↪ Finset (Fin m) :=
    ⟨fun i => (e i).val, fun _ _ h => e.injective (Subtype.ext h)⟩
  have hmap : yes.map emb =
      (Finset.univ.filter fun j => x j = true).powersetCard r := by
    ext s
    constructor
    · intro hs
      obtain ⟨i, hi, e'⟩ := Finset.mem_map.mp hs
      change (e i).val = s at e'
      subst s
      have hall := (Finset.mem_filter.mp hi).2
      have hc := (Finset.mem_powersetCard.mp (e i).property).2
      exact Finset.mem_powersetCard.mpr
        ⟨fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ j, hall j hj⟩, hc⟩
    · intro hs
      obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hs
      have he : s ∈ (Finset.univ : Finset (Fin m)).powersetCard r :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩
      refine Finset.mem_map.mpr ⟨e.symm ⟨s, he⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj =>
          (Finset.mem_filter.mp (hsub (by simpa using hj))).2⟩
      · change (e (e.symm ⟨s, he⟩)).val = s
        rw [e.apply_symm_apply]
  rw [← Finset.card_powersetCard, ← hmap, Finset.card_map]

private noncomputable def digitCircuit (m r : Nat) : Circuit extSignature m 1 :=
  let e := enumSubsets m r
  (Circuit.oneGate (σ := extSignature) (.gate _) id).comp
    (Circuit.pi fun i => subsetAnd (e i).val)

private theorem eval_digitCircuit (m r p : Nat) (x : Fin m → Bool) :
    (digitCircuit m r).eval (extInterpretation (modGate p)) x 0 =
      decide ((((Finset.univ.filter fun j => x j = true).card).choose r) % p ≠ 0) := by
  classical
  simp only [digitCircuit, Circuit.eval_comp, Circuit.eval_oneGate, extInterpretation_gate, id_eq,
    Circuit.eval_pi, modGate]
  have e : (Finset.univ.filter
      (fun i => (subsetAnd (enumSubsets m r i).val).eval
        (extInterpretation (modGate p)) x 0 = true)) =
      (Finset.univ.filter (fun i => ∀ j ∈ (enumSubsets m r i).val, x j = true)) := by
    ext i
    simp [eval_subsetAnd]
  erw [e, subset_count]

/-- Three layers suffice for a single prime-power gate. Each middle-layer MOD gate reads all
conjunctions of a fixed subset size, and the final OR detects a nonzero digit. -/
noncomputable def primePowerGateCircuit (p k m : Nat) : Circuit extSignature m 1 :=
  (Circuit.oneGate (σ := extSignature) (.ac (.or k)) id).comp
    (Circuit.pi fun j : Fin k => digitCircuit m (p ^ j.val))

/-- The depth-three circuit computes one prime-power MOD gate using prime MOD gates. -/
theorem primePowerGateCircuit_correct (p : Nat) [Fact p.Prime] (k m : Nat) :
    (primePowerGateCircuit p k m).Computes (extInterpretation (modGate p))
      (single (modGate (p ^ k) m)) := by
  intro x
  funext j
  rw [Subsingleton.elim j 0]
  simp only [primePowerGateCircuit, Circuit.eval_comp, Circuit.eval_oneGate,
    extInterpretation_ac, interpretation_or, id_eq, Circuit.eval_pi, eval_digitCircuit,
    single, modGate]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  have hd := (Nat.pow_dvd_iff_forall_dvd_choose (Fact.out : p.Prime) k
    (Finset.univ.filter fun j => x j = true).card).not
  simp only [Nat.dvd_iff_mod_eq_zero, not_forall] at hd
  constructor
  · rintro ⟨j, hj⟩
    exact hd.mpr ⟨j.val, j.isLt, hj⟩
  · intro h
    obtain ⟨j, hj, hn⟩ := hd.mp h
    exact ⟨⟨j, hj⟩, hn⟩

/-- The simulation uses conjunctions, MOD gates, and a final disjunction. -/
theorem primePowerGateCircuit_depth (p k m : Nat) : (primePowerGateCircuit p k m).depth ≤ 3 := by
  unfold primePowerGateCircuit
  apply (Circuit.depth_comp_le _ _).trans
  have h (j : Fin k) : (digitCircuit m (p ^ j.val)).depth ≤ 2 := by
    unfold digitCircuit
    apply (Circuit.depth_comp_le _ _).trans
    have hb := Circuit.depth_pi_le (fun i => subsetAnd (enumSubsets m (p ^ j.val) i).val)
      (D := 1) (fun i => by simp [subsetAnd, Circuit.depth_oneGate])
    rw [Circuit.depth_oneGate]
    exact Nat.add_le_add_left hb 1
  have hb := Circuit.depth_pi_le _ h
  simp only [Circuit.depth_oneGate]
  omega

theorem primePowerGateCircuit_size (p k m : Nat) (hp : 0 < p) :
    (primePowerGateCircuit p k m).size ≤ k * ((m + 1) ^ (p ^ k) + 1) + 1 := by
  have h (j : Fin k) : (digitCircuit m (p ^ j.val)).size ≤ (m + 1) ^ (p ^ k) + 1 := by
    simp only [digitCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, subsetAnd,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ]
    apply Nat.add_le_add_right _ 1
    change ((Finset.univ : Finset (Fin m)).powersetCard (p ^ j.val)).card ≤ _
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    refine (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans ?_)
    exact Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.pow_le_pow_right hp j.isLt.le)
  simp only [primePowerGateCircuit, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
  apply Nat.add_le_add_right _ 1
  simpa using (Finset.sum_le_sum (s := Finset.univ) fun j _ => h j)

private abbrev repeats {m : Nat} (q : Nat) (mult : Fin m → Nat) := Σ i, Fin (mult i % q)

private noncomputable def repeatWiring {m : Nat} (q : Nat) (mult : Fin m → Nat) :
    Fin (Fintype.card (repeats q mult)) → Fin m :=
  fun j => ((Fintype.equivFin (repeats q mult)).symm j).1

private theorem repeat_arity {m : Nat} (q : Nat) (hq : 0 < q) (mult : Fin m → Nat) :
    Fintype.card (repeats q mult) ≤ m * q := by
  simp only [repeats, Fintype.card_sigma, Fintype.card_fin]
  simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ : Fin m => q)
    (fun i _ => (Nat.mod_lt (mult i) hq).le)

private theorem repeat_modGate {m : Nat} (q : Nat) (mult : Fin m → Nat) (x : Fin m → Bool) :
    modGate q (Fintype.card (repeats q mult)) (x ∘ repeatWiring q mult) =
      decide (multWeight mult x % q ≠ 0) := by
  have mulCount : BitString.weight (x ∘ repeatWiring q mult) =
      ∑ i, (mult i % q) * (x i).toNat := by
    rw [BitString.weight_eq_sum_toNat]
    change (∑ j, (x ((Fintype.equivFin (repeats q mult)).symm j).1).toNat) = _
    rw [Equiv.sum_comp (Fintype.equivFin (repeats q mult)).symm (fun j => (x j.1).toNat)]
    simp [repeats, Fintype.sum_sigma]
  have hmod : (∑ i, (mult i % q) * (x i).toNat) ≡ multWeight mult x [MOD q] := by
    unfold multWeight
    exact Nat.ModEq.sum fun i _ => (Nat.mod_modEq (mult i) q).mul_right _
  change (∑ i, (mult i % q) * (x i).toNat) % q = multWeight mult x % q at hmod
  change decide (BitString.weight (x ∘ repeatWiring q mult) % q ≠ 0) = _
  rw [mulCount, hmod]

private noncomputable def implPrimePower (p k : Nat) :
    (op : MultOp) → Circuit extSignature (multSignature.Arity op) 1
  | .ac op => Circuit.oneGate (.ac op) id
  | .gate _ mult =>
    (primePowerGateCircuit p k (Fintype.card (repeats (p ^ k) mult))).comp
      (Circuit.wiring _ (repeatWiring (p ^ k) mult))

private theorem implPrimePower_correct (p : Nat) [Fact p.Prime] (k : Nat) (op : MultOp) :
    (implPrimePower p k op).Computes (extInterpretation (modGate p))
      (single (multInterpretation (fun _ t => decide (t % p ^ k ≠ 0)) op)) := by
  cases op with
  | ac op => intro x; funext i; rfl
  | gate m mult =>
    intro x
    funext i
    rw [Subsingleton.elim i 0]
    simp only [implPrimePower, Circuit.eval_comp, Circuit.eval_wiring, multInterpretation_gate,
      single]
    have e := congrFun (primePowerGateCircuit_correct p k _ (x ∘ repeatWiring (p ^ k) mult))
      (0 : Fin 1)
    exact e.trans (repeat_modGate _ _ _)

private def simCost (p k m : Nat) : Nat := k * ((m * p ^ k + 1) ^ (p ^ k) + 1) + 1

private theorem implPrimePower_size (p k : Nat) (hp : 0 < p) (op : MultOp) :
    (implPrimePower p k op).size ≤ simCost p k (multSignature.Arity op) := by
  cases op with
  | ac op => simp [implPrimePower, simCost]
  | gate m mult =>
    simp only [implPrimePower, Circuit.size_comp, Circuit.size_wiring, zero_add]
    apply (primePowerGateCircuit_size p k _ hp).trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.pow_le_pow_left (Nat.succ_le_succ (repeat_arity _ (Nat.pow_pos hp) mult)) _) 1)) 1

private theorem implPrimePower_depth (p k : Nat) (op : MultOp) :
    (implPrimePower p k op).depth ≤ 3 := by
  cases op with
  | ac op => simp [implPrimePower, Circuit.depth_oneGate]
  | gate m mult =>
    unfold implPrimePower
    exact (Circuit.depth_comp_le _ _).trans (by simpa using primePowerGateCircuit_depth p k _)

theorem AC0Mod_prime_power_subset (p : Nat) [Fact p.Prime] (k : Nat) :
    AC0Mod (p ^ k) ⊆ AC0Mod p := by
  intro L h
  obtain ⟨d, size, hb, hs⟩ := ConstDepth.mem_iff.mp h
  have hpoly : PolynomiallyBounded (fun n => simCost p k (n + size n) * size n) := by
    unfold simCost
    fun_prop
  refine ConstDepth.mem_iff.mpr ⟨3 * d, _, hpoly, fun n => ?_⟩
  obtain ⟨C, hC, hdepth, hsize⟩ := hs n
  let D := multCircuit C
  have he := eval_multCircuit (G := fun _ t => decide (t % p ^ k ≠ 0))
    (f := modGate (p ^ k)) (fun _ _ => rfl) C
  obtain ⟨E, hE, hEs, hEd⟩ := D.exists_simulation_depth_le
    (fun op => simCost p k (multSignature.Arity op)) (fun _ => 3)
    (fun op => ⟨implPrimePower p k op, implPrimePower_correct p k op,
      implPrimePower_size p k (Fact.out : p.Prime).pos op, implPrimePower_depth p k op⟩)
  refine ⟨E, fun x => congrFun (hE.trans he) x |>.trans (hC x), ?_, ?_⟩
  · exact hEd.trans ((D.depthWith_le_mul_depth (fun _ => le_rfl)).trans
      (Nat.mul_le_mul_left _ ((depth_multCircuit_le C).trans hdepth)))
  · apply hEs.trans
    rw [Program.cost_eq_sum]
    have bounds (i : Fin C.size) :
        simCost p k (multSignature.Arity (D.program.lines i).op) ≤ simCost p k (n + size n) := by
      have hh := (arity_lines_multCircuit_le C i).trans (Nat.add_le_add_left hsize _)
      unfold simCost
      gcongr
    exact (by
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bounds i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      exact hsum.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hsize))

/-- A fixed positive power of a prime gives the same nonuniform class as that prime. -/
theorem AC0Mod_prime_power_eq (p : Nat) [Fact p.Prime] {k : Nat} (hk : 0 < k) :
    AC0Mod (p ^ k) = AC0Mod p := by
  apply (AC0Mod_prime_power_subset p k).antisymm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ']
  exact AC0Mod_subset_AC0Mod_mul_right p (Nat.pow_pos (Fact.out : p.Prime).pos)

end Cslib.Circuits.Boolean
