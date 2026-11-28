/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ConstDepth
public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Foundations.Data.BitString.Parity
import CslibFrontier.Computability.Circuit.Boolean.Hastad
import CslibFrontier.Computability.Languages.Slice
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Computability.Circuit.Boolean.Simps

/-!
# AC⁰ and parity

**AC⁰** is the class of languages decided, at every input length, by circuits of negations and
conjunctions and disjunctions of unbounded fan-in, of polynomial size and constant depth
[Arora and Barak, Section 6.7.1][AroraBarak09]. By Håstad's theorem
(`Unbounded.two_pow_le_size_of_computes_parity`), **parity is not in AC⁰**
[Arora and Barak, Theorem 14.1][AroraBarak09], [FurstSaxeSipser1984], [Ajtai1983], [Hastad1986].

Over any basis containing the unbounded fan-in basis through a meaning-preserving map `φ`, the
small circuits `constCircuit φ`, `notCircuit φ` and `binCircuit φ` show that polynomial-size
constant-depth circuits decide the constant languages and are closed under the Boolean operations
(`ConstDepth.bot_mem`, `ConstDepth.top_mem`, `ConstDepth.compl`, `ConstDepth.inf`,
`ConstDepth.sup`); for AC⁰ take `φ` the identity. The two constants `constsCircuit φ` feed any
fixed bits, so `substituteCircuit φ` feeds a projection (`Cslib.Circuits.Boolean.substitute`) with
two gates and one layer of depth, and polynomial-size constant-depth circuits are closed under
projections to polynomially many inputs (`ConstDepth.of_substitute`).

## Main definitions

* `Cslib.Circuits.Boolean.AC0`: the class AC⁰.
* `Cslib.Circuits.Boolean.Unbounded.constCircuit`, `notCircuit`, `binCircuit`: a constant, a
  negation, and a gate of two arguments on top of circuits.
* `Cslib.Circuits.Boolean.Unbounded.constsCircuit`: the bits of a fixed string, from two constant
  gates.
* `Cslib.Circuits.Boolean.Unbounded.substituteCircuit`: a projection of the inputs, from two
  constant gates.

## Main results

* `Cslib.Circuits.Boolean.parity_notMem_AC0`: parity is not in AC⁰.
* `Cslib.Circuits.Boolean.ConstDepth.compl`, `ConstDepth.inf`, `ConstDepth.sup`: closure under the
  Boolean operations.
* `Cslib.Circuits.Boolean.ConstDepth.of_substitute`: closure under projections to polynomially many
  inputs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace Unbounded

/-! ### Small circuits over a basis containing the unbounded fan-in basis -/

variable {n : ℕ} {σ : Signature} (φ : signature.Hom σ) {I : Interpretation σ Bool}

/-- The constant `b`, as one gate: the conjunction or the disjunction of no arguments. -/
def constCircuit : Bool → Circuit σ n 1
  | true => (Circuit.oneGate (Op.and 0 : signature.Op) Fin.elim0).mapOp φ
  | false => (Circuit.oneGate (Op.or 0 : signature.Op) Fin.elim0).mapOp φ

/-- The circuit `C` followed by a negation. -/
def notCircuit (C : Circuit σ n 1) : Circuit σ n 1 :=
  ((Circuit.oneGate (σ := signature) Op.not fun _ => 0).mapOp φ).comp C

/-- The circuits `C` and `D` side by side, followed by a gate `op` of two arguments. -/
def binCircuit (op : Op) (h : op.arity = 2) (C D : Circuit σ n 1) : Circuit σ n 1 :=
  ((Circuit.oneGate (σ := signature) op fun a => Fin.cast h a).mapOp φ).comp (C.append D)

/-- The bits of `z`, each wired from one of two constant gates (`Unbounded.constCircuit`), over
any basis containing the unbounded fan-in basis along `φ`. -/
def constsCircuit {m : ℕ} (z : BitString m) : Circuit σ n m :=
  (Circuit.wiring σ fun i => if z i then Fin.castAdd 1 0 else Fin.natAdd 1 0).comp
    ((constCircuit φ true).append (constCircuit φ false))

/-- **A projection as a circuit**, over a basis containing the unbounded fan-in basis through `φ`:
wiring from the inputs and from the constants `constsCircuit φ`. -/
def substituteCircuit {N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) : Circuit σ n N :=
  (Circuit.wiring σ fun j => (ρ j).elim (Fin.castAdd N) fun _ => Fin.natAdd n j).comp
    ((Circuit.wiring σ id).append (constsCircuit φ fun j => (ρ j).elim (fun _ => false) id))

variable {φ} [φ.Preserves interpretation I]

/-- Evaluating `constCircuit φ b` returns the constant `b`. -/
@[simp] theorem eval_constCircuit (b : Bool) (x : BitString n) (j : Fin 1) :
    (constCircuit φ b).eval I x j = b := by
  cases b <;> simp [constCircuit, Circuit.eval_mapOp (I := interpretation)]

/-- A constant circuit has size `1`. -/
@[simp] theorem size_constCircuit (b : Bool) : (constCircuit (n := n) φ b).size = 1 := by
  cases b <;> rfl

/-- A constant has depth at most one. -/
@[circuit_bound]
theorem depth_constCircuit_le (b : Bool) : (constCircuit (n := n) φ b).depth ≤ 1 := by
  cases b <;> simp [constCircuit]

/-- Evaluating `notCircuit φ C` negates the output of `C`. -/
@[simp] theorem eval_notCircuit (C : Circuit σ n 1) (x : BitString n) (j : Fin 1) :
    (notCircuit φ C).eval I x j = !C.eval I x 0 := by
  rw [notCircuit, Circuit.eval_comp, Circuit.eval_mapOp (I := interpretation), Circuit.eval_oneGate,
    interpretation_not]

/-- Appending a negation gate adds `1` to the size of `C`. -/
@[simp] theorem size_notCircuit (C : Circuit σ n 1) : (notCircuit φ C).size = C.size + 1 := by
  simp only [circuit_simps, notCircuit]

/-- A negation adds one to the depth. -/
@[circuit_bound]
theorem depth_notCircuit_le (C : Circuit σ n 1) : (notCircuit φ C).depth ≤ C.depth + 1 := by
  circuit_bound [notCircuit]

/-- The gate of `binCircuit φ op h C D` applied to the outputs of `C` and `D`. -/
theorem eval_binCircuit (op : Op) (h : op.arity = 2) (C D : Circuit σ n 1) (x : BitString n)
    (j : Fin 1) :
    (binCircuit φ op h C D).eval I x j =
      interpretation op fun a => ![C.eval I x 0, D.eval I x 0] (Fin.cast h a) := by
  simp only [circuit_simps, binCircuit, Circuit.eval_mapOp (I := interpretation)]
  congr 1 with a : 1
  refine Fin.cases (Fin.append_left _ _ 0) (fun b => ?_) (Fin.cast h a)
  rw [Subsingleton.elim b 0]
  exact Fin.append_right _ _ 0

/-- Evaluating `binCircuit` with a binary conjunction gate computes the conjunction of the outputs
of `C` and `D`. -/
@[simp] theorem eval_binCircuit_and (C D : Circuit σ n 1) (x : BitString n) (j : Fin 1) :
    (binCircuit φ (.and 2) rfl C D).eval I x j = (C.eval I x 0 && D.eval I x 0) := by
  rw [eval_binCircuit, interpretation_and]
  simp [Fin.forall_fin_two]

/-- Evaluating `binCircuit` with a binary disjunction gate computes the disjunction of the outputs
of `C` and `D`. -/
@[simp] theorem eval_binCircuit_or (C D : Circuit σ n 1) (x : BitString n) (j : Fin 1) :
    (binCircuit φ (.or 2) rfl C D).eval I x j = (C.eval I x 0 || D.eval I x 0) := by
  rw [eval_binCircuit, interpretation_or]
  simp [Fin.exists_fin_two]

/-- Combining `C` and `D` with a binary gate has size `C.size + D.size + 1`. -/
@[simp] theorem size_binCircuit (op : Op) (h : op.arity = 2) (C D : Circuit σ n 1) :
    (binCircuit φ op h C D).size = C.size + D.size + 1 := by
  simp only [circuit_simps, binCircuit]

/-- A gate of two arguments adds one to the larger depth. -/
@[circuit_bound]
theorem depth_binCircuit_le (op : Op) (h : op.arity = 2) (C D : Circuit σ n 1) :
    (binCircuit φ op h C D).depth ≤ max C.depth D.depth + 1 := by
  circuit_bound [binCircuit]

/-- `constsCircuit φ z` outputs `z` on every input. -/
@[simp] theorem eval_constsCircuit {m : ℕ} (z : BitString m) (x : BitString n) :
    (constsCircuit φ z).eval I x = z := by
  funext i
  simp only [circuit_simps, constsCircuit]
  cases z i
  · exact (Fin.append_right _ _ (0 : Fin 1)).trans (eval_constCircuit _ _ _)
  · exact (Fin.append_left _ _ (0 : Fin 1)).trans (eval_constCircuit _ _ _)

/-- `constsCircuit φ z` has two gates. -/
@[simp] theorem size_constsCircuit {m : ℕ} (z : BitString m) :
    (constsCircuit (n := n) φ z).size = 2 := by
  simp [constsCircuit]

/-- `constsCircuit φ z` has depth at most one. -/
@[circuit_bound]
theorem depth_constsCircuit_le {m : ℕ} (z : BitString m) :
    (constsCircuit (n := n) φ z).depth ≤ 1 := by
  circuit_bound [constsCircuit]

/-- The projection circuit evaluates `substitute ρ`. -/
theorem eval_substituteCircuit {N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) (x : BitString n) :
    (substituteCircuit φ ρ).eval I x = substitute ρ x := by
  funext j
  rcases h : ρ j with i | b <;>
    simp [substituteCircuit, substitute, h, Circuit.eval_comp, Circuit.eval_append]

/-- A projection circuit has two gates. -/
@[simp] theorem size_substituteCircuit {N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) :
    (substituteCircuit φ ρ).size = 2 := by
  simp [substituteCircuit]

/-- A projection circuit has depth at most one. -/
@[circuit_bound]
theorem depth_substituteCircuit_le {N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) :
    (substituteCircuit φ ρ).depth ≤ 1 := by
  circuit_bound [substituteCircuit]

end Unbounded

/-! ### AC⁰ -/

/-- **AC⁰**: the languages over `Bool` decided, at every input length, by circuits of negations and
unbounded fan-in conjunctions and disjunctions of polynomially bounded size and constant depth. -/
def AC0 : Set (Language Bool) :=
  ConstDepth Unbounded.interpretation

/-- **Parity is not in AC⁰.** -/
theorem parity_notMem_AC0 : Language.ofSlices parity ∉ AC0 := by
  intro h
  obtain ⟨d, size, hsize, hC⟩ := ConstDepth.mem_iff.1 h
  -- the size bound at the lengths `s (16 s + 1) ^ d` is a polynomial in `s`
  have hpoly : PolynomiallyBounded fun s => size (s * (16 * s + 1) ^ d) :=
    hsize.comp (by fun_prop)
  obtain ⟨s, hlt, hs⟩ := (hpoly.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 2)).exists
  obtain ⟨C, hCcomp, hCdepth, hCsize⟩ := hC (s * (16 * s + 1) ^ d)
  rw [Language.slice_ofSlices] at hCcomp
  have := Unbounded.two_pow_le_size_of_computes_parity hCcomp hs
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hCdepth))
  omega

/-! ### Closure under the Boolean operations -/

namespace ConstDepth

open Unbounded

variable {σ : Signature} {I : Interpretation σ Bool} {L M : Language Bool}

/-- The empty language has constant-depth circuits over a basis containing the unbounded fan-in
basis. -/
theorem bot_mem (φ : Unbounded.signature.Hom σ) [φ.Preserves Unbounded.interpretation I] :
    (⊥ : Language Bool) ∈ ConstDepth I :=
  mem_iff.2 ⟨1, fun _ => 1, by fun_prop, fun _ => ⟨constCircuit φ false,
    fun _ => funext fun _ => by simp [single], depth_constCircuit_le _, (size_constCircuit _).le⟩⟩

/-- The full language has constant-depth circuits over a basis containing the unbounded fan-in
basis. -/
theorem top_mem (φ : Unbounded.signature.Hom σ) [φ.Preserves Unbounded.interpretation I] :
    (⊤ : Language Bool) ∈ ConstDepth I :=
  mem_iff.2 ⟨1, fun _ => 1, by fun_prop, fun _ => ⟨constCircuit φ true,
    fun _ => funext fun _ => by simp [single], depth_constCircuit_le _, (size_constCircuit _).le⟩⟩

/-- Over a basis containing the unbounded fan-in basis, constant-depth circuits are closed under
complement. -/
theorem compl (φ : Unbounded.signature.Hom σ) [φ.Preserves Unbounded.interpretation I]
    (hL : L ∈ ConstDepth I) : Lᶜ ∈ ConstDepth I := by
  obtain ⟨d, size, hsize, hC⟩ := mem_iff.1 hL
  refine mem_iff.2 ⟨d + 1, fun n => size n + 1, by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  exact ⟨notCircuit φ C, fun x => funext fun _ => by simp [single, hCc x],
    (depth_notCircuit_le C).trans (by omega), by simpa using hCs⟩

/-- Two languages with constant-depth circuits, combined by a binary gate. -/
private theorem binCircuit_mem (φ : Unbounded.signature.Hom σ)
    [φ.Preserves Unbounded.interpretation I] (op : Unbounded.Op) (h : op.arity = 2)
    {N : Language Bool} (hN : ∀ n x, N.slice n x = Unbounded.interpretation op fun a =>
      ![L.slice n x, M.slice n x] (Fin.cast h a))
    (hL : L ∈ ConstDepth I) (hM : M ∈ ConstDepth I) : N ∈ ConstDepth I := by
  obtain ⟨d, size, hsize, hC⟩ := mem_iff.1 hL
  obtain ⟨d', size', hsize', hC'⟩ := mem_iff.1 hM
  refine mem_iff.2 ⟨max d d' + 1, fun n => size n + size' n + 1, by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDc, hDd, hDs⟩ := hC' n
  refine ⟨binCircuit φ op h C D, fun x => ?_,
    (depth_binCircuit_le _ _ C D).trans (by omega),
    by simp only [size_binCircuit]; omega⟩
  funext j
  rw [eval_binCircuit, hCc x, hDc x]
  exact (hN n x).symm

/-- Over a basis containing the unbounded fan-in basis, constant-depth circuits are closed under
intersection. -/
theorem inf (φ : Unbounded.signature.Hom σ) [φ.Preserves Unbounded.interpretation I]
    (hL : L ∈ ConstDepth I) (hM : M ∈ ConstDepth I) : L ⊓ M ∈ ConstDepth I :=
  binCircuit_mem φ (.and 2) rfl (fun n x => by
    rw [Language.slice_inf]
    cases L.slice n x <;> cases M.slice n x <;> decide) hL hM

/-- Over a basis containing the unbounded fan-in basis, constant-depth circuits are closed under
union. -/
theorem sup (φ : Unbounded.signature.Hom σ) [φ.Preserves Unbounded.interpretation I]
    (hL : L ∈ ConstDepth I) (hM : M ∈ ConstDepth I) : L ⊔ M ∈ ConstDepth I :=
  binCircuit_mem φ (.or 2) rfl (fun n x => by
    rw [Language.slice_sup]
    cases L.slice n x <;> cases M.slice n x <;> decide) hL hM

/-- **Constant-depth classes are closed under projections to polynomially many inputs.** If
`L.slice n x = M.slice (N n) (substitute (ρ n) x)` for a polynomially bounded `N`, and `M` has
polynomial-size constant-depth circuits over a basis containing the unbounded fan-in basis, so
does `L`: feed the circuit of `M` with `Unbounded.substituteCircuit`. -/
theorem of_substitute (φ : Unbounded.signature.Hom σ) [φ.Preserves Unbounded.interpretation I]
    {N : ℕ → ℕ} (hN : PolynomiallyBounded N) (ρ : ∀ n, Fin (N n) → Fin n ⊕ Bool)
    (h : ∀ n x, L.slice n x = M.slice (N n) (substitute (ρ n) x)) (hM : M ∈ ConstDepth I) :
    L ∈ ConstDepth I := by
  obtain ⟨d, s, hs, hC⟩ := mem_iff.1 hM
  refine mem_iff.2 ⟨d + 1, fun n => s (N n) + 2, by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC (N n)
  refine ⟨C.comp (Unbounded.substituteCircuit φ (ρ n)), fun x => ?_, ?_, ?_⟩
  · funext o
    rw [Circuit.eval_comp, Unbounded.eval_substituteCircuit, hCc]
    simp only [single, h]
  · have := Unbounded.depth_substituteCircuit_le (φ := φ) (ρ n)
    have := Circuit.depth_comp_le C (Unbounded.substituteCircuit φ (ρ n))
    omega
  · rw [Circuit.size_comp, Unbounded.size_substituteCircuit]
    change 2 + C.size ≤ s (N n) + 2
    omega

end ConstDepth

end Cslib.Circuits.Boolean
