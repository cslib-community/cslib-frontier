/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
public import CslibFrontier.Computability.Circuit.Boolean.SymmetricNC1
public import CslibFrontier.Computability.Circuit.Boolean.ThresholdNC1
import CslibFrontier.Computability.Circuit.Boolean.PPolyHard
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Simulation of `MOD_q` circuits in `AC¹`, `NC¹`, and `P/poly`

A `MOD_q` gate reading `k` wires is a symmetric function of them, so it has a De Morgan circuit of
fan-in two with `O(k²)` gates and depth `O(log k)` (`symmetricDeMorganCircuit`). A gate may read a
wire many times, but only the multiplicity modulo `q` matters, so after aggregating multiplicities
(`Unbounded.multCircuit`) a gate of a circuit with `n` inputs and `s` gates is a `MOD_q` function of
at most `max q 1 · (n + s)` bits. Replacing every `MOD_q` gate by the symmetric circuit and every
conjunction and disjunction by a balanced tree (`Unbounded.modMultDeMorganCircuit`) turns a
circuit of depth `d` into a De Morgan circuit of polynomial size and depth
`O(log (max q 1 · (n + s))) · d` (`Unbounded.exists_deMorgan_simulation_modGate`). For
polynomial-size circuits this gives **ACⁱ[q] ⊆ NCⁱ⁺¹** (`ACMod_subset_NC_succ`), and so
**ACC⁰ ⊆ NC¹** (`ACC0_subset_NC_one`) [Arora and Barak, Chapter 13, Exercise §4][AroraBarak07].
All classes are nonuniform.

Replacing the majority gate in `modCircuitOfMajority` by the logarithmic-depth De Morgan majority
circuit (`majorityDeMorganCircuit`) simulates each operation of the `MOD_q` multiplicity basis over
`Unbounded.signature` in polynomial size and logarithmic depth (`Unbounded.modMultUnboundedCircuit`,
`Unbounded.exists_unbounded_simulation_modGate`): **ACⁱ[q] ⊆ ACⁱ⁺¹** (`ACMod_subset_AC_succ`) and
`ACC0 ⊆ AC 1 ⊆ PPoly` (`ACC0_subset_AC_one`, `ACC0_subset_PPoly`). The De Morgan simulation also
bounds unbounded-depth `MOD_q` circuits by De Morgan circuits (`SIZEMod_subset_SIZE`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.modMultDeMorganCircuit`: logarithmic-depth fan-in-two
  simulation of a single `MOD_q` multiplicity operation.
* `Cslib.Circuits.Boolean.Unbounded.modMultUnboundedCircuit`: logarithmic-depth unbounded-fan-in
  simulation of a single `MOD_q` multiplicity operation.
* `Cslib.Circuits.Boolean.SIZEMod`: languages decided by `MOD_q` circuits of size at most `s n`.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_modGate`,
  `Cslib.Circuits.Boolean.Unbounded.exists_unbounded_simulation_modGate`: gate-by-gate simulations
  of `MOD_q` circuits with fan-in two and with unbounded fan-in.
* `Cslib.Circuits.Boolean.ACMod_subset_NC_succ`, `Cslib.Circuits.Boolean.AC0Mod_subset_NC_one`,
  `Cslib.Circuits.Boolean.ACC0_subset_NC_one`: **ACⁱ[q] ⊆ NCⁱ⁺¹** and **ACC⁰ ⊆ NC¹**.
* `Cslib.Circuits.Boolean.ACMod_subset_AC_succ`, `Cslib.Circuits.Boolean.ACC0_subset_AC_one`,
  `Cslib.Circuits.Boolean.ACC0_subset_PPoly`.
* `Cslib.Circuits.Boolean.SIZEMod_subset_SIZE`: simulating `SIZEMod q` in De Morgan `SIZE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft)][AroraBarak07]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/
@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded

namespace Unbounded

/-- A circuit over the unbounded fan-in basis simulating each operation of the `MOD_q` multiplicity
basis, using `majorityDeMorganCircuit` mapped into `Unbounded.signature` inside
`modCircuitOfMajority`. -/
def modMultUnboundedCircuit (q : ℕ) :
    (op : MultOp) → Circuit Unbounded.signature (multSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate _ mult =>
    let K := ∑ i, modMult q (mult i)
    (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).comp
      (Circuit.wiring Unbounded.signature (expandIndex fun i => modMult q (mult i)))

/-- `modMultUnboundedCircuit q op` computes `op` under `Unbounded.interpretation`. -/
theorem computes_modMultUnboundedCircuit (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).Computes Unbounded.interpretation
      (single (multInterpretation (modCount q) op)) := by
  cases op with
  | ac op =>
    intro x
    funext o
    rw [Subsingleton.elim o 0]
    rfl
  | gate N mult =>
    intro x
    set K := ∑ i, modMult q (mult i)
    have hM : ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).Computes
        Unbounded.interpretation (single (majority (K + (K + 2)))) :=
      (computes_majorityDeMorganCircuit (K + (K + 2))).mapOp
    rw [modMultUnboundedCircuit, Circuit.eval_comp, Circuit.eval_wiring,
      computes_modCircuitOfMajority hM q]
    funext o
    simp only [single, multInterpretation_gate, modGate_eq_modCount, modCount]
    rw [weight_comp_expandIndex, decide_eq_decide]
    exact multWeight_modMult_mod_ne_zero_iff q mult x

/-- Polynomial size bound for `modMultUnboundedCircuit q op`. -/
theorem size_modMultUnboundedCircuit_le (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).size ≤
      2100 * (max q 1 * multSignature.Arity op + 1) ^ 3 := by
  cases op with
  | ac op =>
    simp only [modMultUnboundedCircuit, Circuit.size_oneGate]
    have : 1 ≤ (max q 1 * multSignature.Arity (.ac op) + 1) ^ 3 :=
      Nat.one_le_pow _ _ (by omega)
    linarith
  | gate N mult =>
    rw [modMultUnboundedCircuit, Circuit.size_comp, Circuit.size_wiring, zero_add]
    set K := ∑ i : Fin N, modMult q (mult i)
    have hK : K ≤ max q 1 * N := by
      simpa [K, mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    have hM : (((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).size) ≤
        65 * (2 * K + 3) ^ 2 := by
      rw [Circuit.size_mapOp, show 2 * K + 3 = K + (K + 2) + 1 by omega]
      exact size_majorityDeMorganCircuit_le_sq (K + (K + 2))
    change (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).size ≤
      2100 * (max q 1 * N + 1) ^ 3
    have hcube : (K + 1) ^ 3 ≤ (max q 1 * N + 1) ^ 3 := by gcongr
    calc (modCircuitOfMajority (Signature.Hom.id _) q
          ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).size
        ≤ 1 + (K + 1) * (2 * (2 +
            ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).size) + 2) :=
          size_modCircuitOfMajority_le q
      _ ≤ 1 + (K + 1) * (2 * (2 + 65 * (2 * K + 3) ^ 2) + 2) := by gcongr
      _ ≤ 2100 * (K + 1) ^ 3 := by
        have hring : 2100 * (K + 1) ^ 3 =
            1 + (K + 1) * (2 * (2 + 65 * (2 * K + 3) ^ 2) + 2) +
              (1580 * K ^ 3 + 4220 * K ^ 2 + 3564 * K + 923) := by ring
        omega
      _ ≤ 2100 * (max q 1 * N + 1) ^ 3 := Nat.mul_le_mul_left 2100 hcube

/-- Logarithmic depth bound for `modMultUnboundedCircuit q op`. -/
theorem depth_modMultUnboundedCircuit_le (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).depth ≤
      6 + 23 * Nat.clog 2 (2 * max q 1 * multSignature.Arity op + 3) := by
  cases op with
  | ac op =>
    simp only [modMultUnboundedCircuit, Circuit.depth_oneGate]
    omega
  | gate N mult =>
    refine (Circuit.depth_comp_le _ _).trans ?_
    rw [Circuit.depth_wiring, add_zero]
    set K := ∑ i : Fin N, modMult q (mult i)
    have hK : K ≤ max q 1 * N := by
      simpa [K, mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    have h2K : 2 * K ≤ 2 * max q 1 * N := by linarith
    have hM : (((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).depth) ≤
        2 + 23 * Nat.clog 2 (2 * max q 1 * N + 3) := by
      rw [Circuit.depth_mapOp]
      refine (depth_majorityDeMorganCircuit_le (K + (K + 2))).trans ?_
      have hclog : Nat.clog 2 (K + (K + 2) + 1) ≤ Nat.clog 2 (2 * max q 1 * N + 3) :=
        Nat.clog_mono_right 2 (by omega)
      omega
    have hd := depth_modCircuitOfMajority_le (φ := Signature.Hom.id _)
      (M := (majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded) q
    change (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).depth ≤
      6 + 23 * Nat.clog 2 (2 * max q 1 * N + 3)
    omega

/-- **Unbounded fan-in circuits simulate `MOD_q` gates in logarithmic depth**: a circuit with
`MOD_q` gates of `n` inputs, `s` gates and depth `d` has an equivalent circuit over the unbounded
fan-in basis of at most `2100 * s * (max q 1 * (n + s) + 1) ^ 3` gates and depth at most
`(6 + 23 * ⌈log₂ (2 * max q 1 * (n + s) + 3)⌉) * d`. -/
theorem exists_unbounded_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit Unbounded.signature n m,
      D.eval Unbounded.interpretation = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) ∧
      D.depth ≤ (6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3)) * C.depth :=
  exists_simulation_modGate q (modMultUnboundedCircuit q) (computes_modMultUnboundedCircuit q)
    (S := fun a => 2100 * (max q 1 * a + 1) ^ 3)
    (D := fun a => 6 + 23 * Nat.clog 2 (2 * max q 1 * a + 3))
    (fun _ _ h => by dsimp only; gcongr) (fun _ _ h => by dsimp only; gcongr)
    (size_modMultUnboundedCircuit_le q) (depth_modMultUnboundedCircuit_le q) C

/-- A De Morgan circuit of fan-in two simulating each operation of the `MOD_q` multiplicity basis:
a balanced tree for a conjunction or a disjunction, and for a `MOD_q` gate the symmetric circuit
`symmetricDeMorganCircuit` on its arguments repeated with their multiplicities reduced by
`modMult`. -/
def modMultDeMorganCircuit (q : ℕ) :
    (op : MultOp) → Circuit Boolean.signature (multSignature.Arity op) 1
  | .ac op => op.deMorganFormula.toCircuit
  | .gate _ mult =>
    let K := ∑ i, modMult q (mult i)
    (symmetricDeMorganCircuit K (modCount q K)).comp
      (Circuit.wiring Boolean.signature (expandIndex fun i => modMult q (mult i)))

/-- `modMultDeMorganCircuit q op` computes `op`. -/
theorem computes_modMultDeMorganCircuit (q : ℕ) (op : MultOp) :
    (modMultDeMorganCircuit q op).Computes Boolean.interpretation
      (single (multInterpretation (modCount q) op)) := by
  cases op with
  | ac op => exact (Op.computes_deMorganFormula op).toCircuit
  | gate N mult =>
    intro x
    funext o
    rw [modMultDeMorganCircuit, Circuit.eval_comp, Circuit.eval_wiring,
      computes_symmetricDeMorganCircuit]
    simp only [single, multInterpretation_gate, modCount]
    rw [weight_comp_expandIndex, decide_eq_decide]
    exact multWeight_modMult_mod_ne_zero_iff q mult x

/-- The number of wires that the `MOD_q` simulation reads, `∑ i, modMult q (mult i)`, is at most
`max q 1` times the number of arguments. -/
private theorem sum_modMult_le (q : ℕ) {N : ℕ} (mult : Fin N → ℕ) :
    ∑ i, modMult q (mult i) ≤ max q 1 * N := by
  simpa [mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
    (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _

/-- An operation reading `a` wires has a De Morgan circuit of at most
`70 (max q 1 · a + 1) ^ 2` gates. -/
theorem size_modMultDeMorganCircuit_le (q : ℕ) (op : MultOp) :
    (modMultDeMorganCircuit q op).size ≤ 70 * (max q 1 * multSignature.Arity op + 1) ^ 2 := by
  have hq : 1 ≤ max q 1 := le_max_right q 1
  cases op with
  | ac op =>
    refine (Formula.size_toCircuit _).trans_le ((Op.size_deMorganFormula_le op).trans ?_)
    have : op.arity ≤ max q 1 * op.arity := Nat.le_mul_of_pos_left _ hq
    have : max 1 op.arity ≤ max q 1 * op.arity + 1 := max_le (by omega) (by omega)
    change max 1 op.arity ≤ 70 * (max q 1 * op.arity + 1) ^ 2
    nlinarith
  | gate N mult =>
    rw [modMultDeMorganCircuit, Circuit.size_comp, Circuit.size_wiring, zero_add]
    refine (size_symmetricDeMorganCircuit_le _ _).trans ?_
    have := sum_modMult_le q mult
    change 70 * (∑ i, modMult q (mult i) + 1) ^ 2 ≤ 70 * (max q 1 * N + 1) ^ 2
    gcongr

/-- An operation reading `a` wires has a De Morgan circuit of depth at most
`2 + 21 ⌈log₂ (max q 1 · a + 1)⌉`. -/
theorem depth_modMultDeMorganCircuit_le (q : ℕ) (op : MultOp) :
    (modMultDeMorganCircuit q op).depth ≤
      2 + 21 * Nat.clog 2 (max q 1 * multSignature.Arity op + 1) := by
  have hq : 1 ≤ max q 1 := le_max_right q 1
  cases op with
  | ac op =>
    refine (Formula.depth_toCircuit_le _).trans ((Op.depth_deMorganFormula_le op).trans ?_)
    have : Nat.clog 2 op.arity ≤ Nat.clog 2 (max q 1 * op.arity + 1) :=
      Nat.clog_mono_right 2 (by nlinarith)
    change max 1 (Nat.clog 2 op.arity) ≤ 2 + 21 * Nat.clog 2 (max q 1 * op.arity + 1)
    omega
  | gate N mult =>
    refine (Circuit.depth_comp_le _ _).trans ?_
    rw [Circuit.depth_wiring, add_zero]
    refine (depth_symmetricDeMorganCircuit_le _ _).trans ?_
    have := Nat.clog_mono_right 2 (Nat.add_le_add_right (sum_modMult_le q mult) 1)
    change 2 + 21 * Nat.clog 2 (∑ i, modMult q (mult i) + 1) ≤
      2 + 21 * Nat.clog 2 (max q 1 * N + 1)
    omega

/-- **Fan-in two simulates `MOD_q` gates in logarithmic depth**: a circuit with `MOD_q` gates of
`n` inputs, `s` gates and depth `d` has an equivalent De Morgan circuit of fan-in two with at most
`70 s (max q 1 · (n + s) + 1) ^ 2` gates and depth at most
`(2 + 21 ⌈log₂ (max q 1 · (n + s) + 1)⌉) d`. -/
theorem exists_deMorgan_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ C.size * (70 * (max q 1 * (n + C.size) + 1) ^ 2) ∧
      D.depth ≤ (2 + 21 * Nat.clog 2 (max q 1 * (n + C.size) + 1)) * C.depth :=
  exists_simulation_modGate q (modMultDeMorganCircuit q) (computes_modMultDeMorganCircuit q)
    (S := fun a => 70 * (max q 1 * a + 1) ^ 2) (D := fun a => 2 + 21 * Nat.clog 2 (max q 1 * a + 1))
    (fun _ _ h => by dsimp only; gcongr) (fun _ _ h => by dsimp only; gcongr)
    (size_modMultDeMorganCircuit_le q) (depth_modMultDeMorganCircuit_le q) C

end Unbounded

/-- **`ACⁱ[q] ⊆ ACⁱ⁺¹`**: polynomial-size circuits with `MOD_q` gates of depth `O((log n) ^ i)` are
simulated by polynomial-size circuits over the unbounded fan-in basis of depth
`O((log n) ^ (i + 1))`. -/
theorem ACMod_subset_AC_succ (q i : ℕ) : ACMod q i ⊆ AC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => 2 * max q 1 * (n + s n) + 3) (by fun_prop)
  refine ⟨(23 * e + 6) * c, fun n => s n * (2100 * (max q 1 * (n + s n) + 1) ^ 3),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_unbounded_simulation_modGate q C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hmono := Nat.add_le_add_right
      (Nat.mul_le_mul_left (2 * max q 1) (Nat.add_le_add_left hCs n)) 3
    have hclog : Nat.clog 2 (2 * max q 1 * (n + C.size) + 3) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 hmono).trans (he n)
    have hlog : 6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3) ≤
        (23 * e + 6) * (Nat.log 2 n + 1) := by nlinarith
    calc D.depth ≤ (6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3)) * C.depth := hDd
      _ ≤ ((23 * e + 6) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) := by gcongr
      _ = (23 * e + 6) * c * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **`AC⁰[q] ⊆ AC¹`.** -/
theorem AC0Mod_subset_AC_one (q : ℕ) : AC0Mod q ⊆ AC 1 := by
  rw [← ACMod_zero]
  exact ACMod_subset_AC_succ q 0

/-- **`ACC⁰ ⊆ AC¹`.** -/
theorem ACC0_subset_AC_one : ACC0 ⊆ AC 1 :=
  iUnion₂_subset fun q _ => AC0Mod_subset_AC_one q

/-- **ACⁱ[q] ⊆ NCⁱ⁺¹**: polynomial-size circuits with `MOD_q` gates of depth `O((log n) ^ i)` are
simulated by polynomial-size De Morgan circuits of fan-in two and depth `O((log n) ^ (i + 1))`. -/
theorem ACMod_subset_NC_succ (q i : ℕ) : ACMod q i ⊆ NC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => max q 1 * (n + s n) + 1) (by fun_prop)
  refine ⟨(21 * e + 2) * c, fun n => s n * (70 * (max q 1 * (n + s n) + 1) ^ 2),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_deMorgan_simulation_modGate q C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hclog : Nat.clog 2 (max q 1 * (n + C.size) + 1) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 (by gcongr)).trans (he n)
    have hlog : 2 + 21 * Nat.clog 2 (max q 1 * (n + C.size) + 1) ≤
        (21 * e + 2) * (Nat.log 2 n + 1) := by nlinarith
    calc D.depth ≤ (2 + 21 * Nat.clog 2 (max q 1 * (n + C.size) + 1)) * C.depth := hDd
      _ ≤ ((21 * e + 2) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) := by gcongr
      _ = (21 * e + 2) * c * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **`AC⁰[q] ⊆ NC¹`.** -/
theorem AC0Mod_subset_NC_one (q : ℕ) : AC0Mod q ⊆ NC 1 := by
  rw [← ACMod_zero]
  exact ACMod_subset_NC_succ q 0

/-- **`ACC⁰ ⊆ NC¹`** [Arora and Barak, web draft 2007-01-08, Chapter 13, Exercise §4, printed
p. 252 / PDF p. 268][AroraBarak07]: every language decided by polynomial-size, constant-depth
circuits with negations and unbounded fan-in `AND`, `OR` and `MOD_q` gates, for a fixed modulus
`q`, is decided by polynomial-size De Morgan circuits of fan-in two and depth `O(log n)`. Both
classes are nonuniform. A circuit with gates for several moduli is one with the single modulus
their product, since a `MOD_m` gate is a `MOD_{m k}` gate reading each wire `k` times
(`modGate_mul_right`). -/
theorem ACC0_subset_NC_one : ACC0 ⊆ NC 1 :=
  iUnion₂_subset fun q _ => AC0Mod_subset_NC_one q

/-- **`AC⁰[q] ⊆ P/poly`** for every modulus `q`. -/
theorem AC0Mod_subset_PPoly (q : ℕ) : AC0Mod q ⊆ PPoly :=
  (AC0Mod_subset_AC_one q).trans (AC_subset_PPoly 1)

/-- **`ACC⁰ ⊆ P/poly`.** -/
theorem ACC0_subset_PPoly : ACC0 ⊆ PPoly :=
  ACC0_subset_AC_one.trans (AC_subset_PPoly 1)

/-- **Some language over `Bool` is not in `ACC⁰`** (by Shannon's counting argument and
`ACC0 ⊆ PPoly`). -/
theorem exists_notMem_ACC0 : ∃ L : Language Bool, L ∉ ACC0 := by
  obtain ⟨L, hL⟩ := PPoly.exists_not_mem
  exact ⟨L, fun h => hL (ACC0_subset_PPoly h)⟩

/-! ### Unbounded-depth `MOD_q` circuit size classes (`SIZEMod`) -/

/-- The class of languages over `Bool` decided at every input length `n` by circuits over the
`AC⁰[q]` basis (`Unbounded.extInterpretation (modGate q)`) of size at most `s n` (of arbitrary
depth). -/
def SIZEMod (q : ℕ) (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit extSignature n 1,
    C.Computes (extInterpretation (modGate q)) (single (L.slice n)) ∧ C.size ≤ s n}

/-- `SIZEMod q` is monotone in the size bound. -/
theorem SIZEMod_mono (q : ℕ) : Monotone (SIZEMod q) := by
  intro s₁ s₂ hs L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  exact ⟨C, hCc, hCs.trans (hs n)⟩

/-- **Simulating `SIZEMod q` in De Morgan `SIZE`**: a circuit with `MOD_q` gates of size at most
`c * (n + 1) ^ k` is simulated by a fan-in-two De Morgan circuit of size at most
`70 * (max q 1) ^ 2 * (c + 1) ^ 3 * (n + 1) ^ (3 * (k + 1))`. -/
theorem SIZEMod_subset_SIZE (q c k : ℕ) :
    SIZEMod q (fun n => c * (n + 1) ^ k) ⊆
      SIZE (fun n => 70 * (max q 1) ^ 2 * (c + 1) ^ 3 * (n + 1) ^ (3 * (k + 1))) := by
  intro L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  obtain ⟨D, hDe, hDs, -⟩ := Unbounded.exists_deMorgan_simulation_modGate q C
  have hDc : D.Computes Boolean.interpretation (single (L.slice n)) :=
    fun x => (congrFun hDe x).trans (hCc x)
  refine (complexity_le_of_computes D hDc).trans (hDs.trans ?_)
  have hq : 1 ≤ max q 1 := le_max_right q 1
  have hn1 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)
  have hk1 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  set P := (c + 1) * (n + 1) ^ (k + 1)
  have hsum : n + C.size + 1 ≤ P := by
    dsimp only at hCs
    calc n + C.size + 1 ≤ (n + 1) + c * (n + 1) ^ k := by omega
      _ ≤ 1 * (n + 1) ^ (k + 1) + c * (n + 1) ^ (k + 1) := by
        rw [one_mul]
        exact Nat.add_le_add hn1 (Nat.mul_le_mul_left c hk1)
      _ = P := by ring
  have hQ : max q 1 * (n + C.size) + 1 ≤ max q 1 * P := by nlinarith
  calc C.size * (70 * (max q 1 * (n + C.size) + 1) ^ 2)
      ≤ P * (70 * (max q 1 * P) ^ 2) := by gcongr; omega
    _ = 70 * (max q 1) ^ 2 * (c + 1) ^ 3 * (n + 1) ^ (3 * (k + 1)) := by
        simp only [P]
        ring

end Cslib.Circuits.Boolean
