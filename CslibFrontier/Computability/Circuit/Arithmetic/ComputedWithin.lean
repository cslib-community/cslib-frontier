/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import CslibFrontier.Computability.Circuit.MapOp
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Polynomials computed within a number of nodes

`ComputedWithin P s` says that the polynomial `P`, in variables of any type `σ`, is computed by an
arithmetic circuit with at most `s` nodes: some `n` of its variables feed a circuit
`c : Circuit (arithSignature K) n 1` whose output is `P` as a formal polynomial, and
`n + c.size ≤ s`. Inputs count one node each, like constants, additions and multiplications. This
is the node count of [Arora and Barak, Section 6.1][AroraBarak09] and of the circuits of
[Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], which are lists of `s` polynomials,
each a variable, a constant, or the sum or product of two earlier ones. For polynomial families
the convention does not matter: `Cslib.Circuits.Arithmetic.mem_VP_iff` characterizes `VP` by
`ComputedWithin`.

A polynomial is *affine* (`IsAffine`) when it is a constant or `a * X i + b`, and `P` is an *affine
projection* of `Q` (`IsAffineProjection`) when `P` arises from `Q` by substituting an affine
polynomial for every variable. Affine polynomials have total degree at most `1`
(`IsAffine.totalDegree_le`), and substituting affine polynomials into one gives an affine
polynomial (`IsAffine.aeval`). Substituting affine polynomials into a circuit costs at most four
gates for each input, hence at most a factor five (`ComputedWithin.of_isAffineProjection`).

## Main definitions

* `Cslib.Circuits.ArithOp.map`: the map of arithmetic signatures along a map of constants.
* `Cslib.Circuits.Arithmetic.ComputedWithin`: `P` is computed by a circuit with at most `s` nodes.
* `Cslib.Circuits.Arithmetic.IsAffine`, `Cslib.Circuits.Arithmetic.IsAffineProjection`: affine
  polynomials and affine projections.

## Main results

* `Cslib.Circuits.Circuit.map_eval_arith`: ring homomorphisms commute with evaluation.
* `Cslib.Circuits.Circuit.polynomial_mapOp_ringHom`: mapping the constants of a circuit maps the
  coefficients of its polynomials.
* `Cslib.Circuits.Arithmetic.ComputedWithin.add`, `Cslib.Circuits.Arithmetic.ComputedWithin.mul`,
  `Cslib.Circuits.Arithmetic.ComputedWithin.sum`, `Cslib.Circuits.Arithmetic.ComputedWithin.prod`,
  `Cslib.Circuits.Arithmetic.ComputedWithin.rename`, `Cslib.Circuits.Arithmetic.ComputedWithin.map`:
  closure properties.
* `Cslib.Circuits.Arithmetic.IsAffine.totalDegree_le`, `Cslib.Circuits.Arithmetic.IsAffine.aeval`:
  affine polynomials have degree at most `1` and are closed under affine substitutions.
* `Cslib.Circuits.Arithmetic.ComputedWithin.of_isAffineProjection`: affine projections cost at
  most a factor five.
* `Cslib.Circuits.Arithmetic.ComputedWithin.exists_steps`: the gate list of a circuit, each entry a
  variable, a constant, or the sum or product of two earlier entries.
* `Cslib.Circuits.Arithmetic.mem_VP_iff`: `VP` in terms of `ComputedWithin`.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Section 6.1
* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]
-/

public section

namespace Cslib.Circuits

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {n m k p : ℕ}

/-! ### Polynomials of combined circuits -/

/-- The polynomial at output `j` is the circuit evaluated at the variables. -/
private theorem Circuit.polynomial_def (c : Circuit (arithSignature K) n m) (j : Fin m) :
    c.polynomial j = c.eval (arithInterpretationWith K C) X j :=
  rfl

/-- Renaming the variables of the polynomial computed by a circuit is evaluating the circuit at
the renamed variables. -/
theorem Circuit.rename_polynomial {σ : Type*} (c : Circuit (arithSignature K) n m) (x : Fin n → σ)
    (j : Fin m) : rename x (c.polynomial j) = c.eval (arithInterpretationWith K C) (X ∘ x) j := by
  rw [← Circuit.aeval_polynomial_mvPolynomial, ← aeval_X_left_apply (rename x _), aeval_rename]

/-- The arithmetic operation with its constant mapped along `f`. -/
@[expose] def ArithOp.map {L : Type*} (f : K → L) : (arithSignature K).Hom (arithSignature L) where
  toFun
    | .add => .add
    | .mul => .mul
    | .const a => .const (f a)
  arity_eq op := by cases op <;> rfl

omit [CommSemiring K] in
/-- Mapping constants twice is mapping them along the composite. -/
theorem ArithOp.map_comp {L M : Type*} (f : K → L) (f' : L → M) :
    (ArithOp.map f').comp (ArithOp.map f) = ArithOp.map (f' ∘ f) :=
  Signature.Hom.ext fun op => by cases op <;> rfl

/-- Mapping constants along `f` and interpreting them by `constant` means interpreting them by
`constant ∘ f`. -/
instance ArithOp.map_preserves {L R : Type*} [Add R] [Mul R] (f : K → L) (constant : L → R) :
    (ArithOp.map f).Preserves (arithInterpretationWith K (constant ∘ f))
      (arithInterpretationWith L constant) :=
  ⟨fun op x => by cases op <;> rfl⟩

omit [CommSemiring K] in
/-- A ring homomorphism commutes with evaluating an arithmetic circuit. -/
theorem Circuit.map_eval_arith {A B : Type*} [NonAssocSemiring A] [NonAssocSemiring B]
    (h : A →+* B) (c : Circuit (arithSignature K) n m) (constant : K → A) (x : Fin n → A)
    (j : Fin m) :
    h (c.eval (arithInterpretationWith K constant) x j) =
      c.eval (arithInterpretationWith K (h ∘ constant)) (h ∘ x) j :=
  congrFun (c.map_eval ⟨h, fun op args => by cases op <;> simp [arithInterpretationWith]⟩ x) j

omit [CommSemiring K] in
/-- The polynomial computed by a circuit with constants mapped along `f` is the circuit evaluated
with the constants `C (f a)`. -/
theorem Circuit.polynomial_mapOp {L : Type*} [CommSemiring L] (f : K → L)
    (c : Circuit (arithSignature K) n m) (j : Fin m) :
    (c.mapOp (ArithOp.map f)).polynomial j = c.eval (arithInterpretationWith K (C ∘ f)) X j := by
  rw [Circuit.polynomial_def, Circuit.eval_mapOp (I := arithInterpretationWith K (C ∘ f))]

/-- Mapping the constants of a circuit along a ring homomorphism maps the coefficients of its
polynomials. -/
theorem Circuit.polynomial_mapOp_ringHom {L : Type*} [CommSemiring L] (φ : K →+* L)
    (c : Circuit (arithSignature K) n m) (j : Fin m) :
    (c.mapOp (ArithOp.map φ)).polynomial j = MvPolynomial.map φ (c.polynomial j) := by
  rw [Circuit.polynomial_mapOp, Circuit.polynomial_def, Circuit.map_eval_arith]
  congr 2 with i : 1
  · exact (map_C φ i).symm
  · exact (map_X φ i).symm

namespace Arithmetic

variable {σ τ : Type*}

/-! ### Computation within a number of nodes -/

/-- `P` is computed by an arithmetic circuit with at most `s` nodes, counting its inputs: for some
`n`, a circuit with `n` inputs, fed with the variables `x`, computes `P` as a formal polynomial,
and `n` plus the number of its gates is at most `s`. Constants count as gates. -/
@[expose] def ComputedWithin (P : MvPolynomial σ K) (s : ℕ) : Prop :=
  ∃ (n : ℕ) (x : Fin n → σ) (c : Circuit (arithSignature K) n 1),
    n + c.size ≤ s ∧ rename x (c.polynomial 0) = P

namespace ComputedWithin

variable {P Q : MvPolynomial σ K} {s t : ℕ}

/-- A bound on the number of nodes may be raised. -/
theorem mono (h : ComputedWithin P s) (hst : s ≤ t) : ComputedWithin P t :=
  let ⟨n, x, c, hs, hc⟩ := h
  ⟨n, x, c, hs.trans hst, hc⟩

/-- A circuit has at least one node: its output is an input or a gate. -/
theorem pos (h : ComputedWithin P s) : 0 < s := by
  obtain ⟨n, x, c, hs, -⟩ := h
  rcases c.outputs 0 with i | i
  · exact lt_of_lt_of_le (i.pos) (Nat.le_of_add_right_le hs)
  · exact lt_of_lt_of_le (i.pos) (le_trans (Nat.le_add_left _ _) hs)

/-- Renaming the variables keeps the number of nodes. -/
theorem rename (f : σ → τ) (h : ComputedWithin P s) :
    ComputedWithin (MvPolynomial.rename f P) s := by
  obtain ⟨n, x, c, hs, rfl⟩ := h
  exact ⟨n, f ∘ x, c, hs, by rw [rename_rename]⟩

/-- Mapping the coefficients along a ring homomorphism keeps the number of nodes. -/
theorem map {L : Type*} [CommSemiring L] (φ : K →+* L) (h : ComputedWithin P s) :
    ComputedWithin (MvPolynomial.map φ P) s := by
  obtain ⟨n, x, c, hs, rfl⟩ := h
  exact ⟨n, x, c.mapOp (ArithOp.map φ), hs, by rw [Circuit.polynomial_mapOp_ringHom, map_rename]⟩

end ComputedWithin

/-- A variable is computed by one node, an input. -/
theorem computedWithin_X (i : σ) : ComputedWithin (X i : MvPolynomial σ K) 1 :=
  ⟨1, fun _ => i, Circuit.wiring _ id, le_rfl, by
    rw [Circuit.rename_polynomial]
    rfl⟩

/-- A constant is computed by one node, a constant gate. -/
theorem computedWithin_C (a : K) : ComputedWithin (C a : MvPolynomial σ K) 1 :=
  ⟨0, Fin.elim0, Circuit.oneGate (σ := arithSignature K) (.const a) Fin.elim0, le_rfl, by
    rw [Circuit.rename_polynomial]
    rfl⟩

/-- Two circuits side by side on disjoint inputs compute two polynomials within the sum of their
numbers of nodes. -/
private theorem exists_pair {P Q : MvPolynomial σ K} {s t : ℕ} (hP : ComputedWithin P s)
    (hQ : ComputedWithin Q t) :
    ∃ (n : ℕ) (x : Fin n → σ) (c : Circuit (arithSignature K) n 2), n + c.size ≤ s + t ∧
      c.eval (arithInterpretationWith K C) (X ∘ x) = ![P, Q] := by
  obtain ⟨n₁, x₁, c₁, hs, rfl⟩ := hP
  obtain ⟨n₂, x₂, c₂, ht, rfl⟩ := hQ
  refine ⟨n₁ + n₂, Fin.append x₁ x₂,
    (c₁.mapInputs (Fin.castAdd n₂)).append (c₂.mapInputs (Fin.natAdd n₁)), ?_, ?_⟩
  · simp only [Circuit.size_append, Circuit.mapInputs_size]
    omega
  · funext j
    rw [Circuit.eval_append, Circuit.eval_mapInputs, Circuit.eval_mapInputs,
      Circuit.rename_polynomial, Circuit.rename_polynomial]
    fin_cases j
    · exact congrArg (c₁.eval _ · 0) (funext fun i => by simp)
    · exact congrArg (c₂.eval _ · 0) (funext fun i => by simp)

/-- A gate applied to two polynomials computed within `s` and `t` nodes is computed within
`s + t + 1` nodes. -/
private theorem computedWithin_gate {P Q : MvPolynomial σ K} {s t : ℕ} (hP : ComputedWithin P s)
    (hQ : ComputedWithin Q t) (op : ArithOp K) (hop : ArithOp.arity K op = 2) :
    ComputedWithin (arithInterpretationWith K C op fun a => ![P, Q] (Fin.cast hop a))
      (s + t + 1) := by
  obtain ⟨n, x, c, hs, hc⟩ := exists_pair hP hQ
  refine ⟨n, x, (Circuit.oneGate (σ := arithSignature K) op (Fin.cast hop)).comp c, ?_, ?_⟩
  · rw [Circuit.size_comp, Circuit.size_oneGate]
    omega
  · rw [Circuit.rename_polynomial, Circuit.eval_comp, hc, Circuit.eval_oneGate]

namespace ComputedWithin

variable {P Q : MvPolynomial σ K} {s t : ℕ}

/-- A sum costs the nodes of both summands and one addition. -/
theorem add (hP : ComputedWithin P s) (hQ : ComputedWithin Q t) :
    ComputedWithin (P + Q) (s + t + 1) :=
  computedWithin_gate hP hQ .add rfl

/-- A product costs the nodes of both factors and one multiplication. -/
theorem mul (hP : ComputedWithin P s) (hQ : ComputedWithin Q t) :
    ComputedWithin (P * Q) (s + t + 1) :=
  computedWithin_gate hP hQ .mul rfl

/-- A sum of polynomials computed within `s` nodes each. -/
theorem sum {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial σ K}
    (h : ∀ i ∈ A, ComputedWithin (f i) s) :
    ComputedWithin (∑ i ∈ A, f i) (A.card * (s + 1) + 1) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using computedWithin_C (σ := σ) (0 : K)
  | insert i A hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono (le_of_eq ?_)
    ring

/-- A product of polynomials computed within `s` nodes each. -/
theorem prod {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial σ K}
    (h : ∀ i ∈ A, ComputedWithin (f i) s) :
    ComputedWithin (∏ i ∈ A, f i) (A.card * (s + 1) + 1) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using computedWithin_C (σ := σ) (1 : K)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono (le_of_eq ?_)
    ring

/-- A polynomial computed within `s` nodes is entry `k < s` of a list in which every entry below
`s` is a variable, a constant, or the sum or product of two earlier entries. The list holds the
values of the wires of the circuit in program order, inputs first, and `0` after them. -/
theorem exists_steps (h : ComputedWithin P s) :
    ∃ l : ℕ → MvPolynomial σ K, (∀ k < s, (∃ i, l k = X i) ∨ (∃ a, l k = C a) ∨
      (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)) ∧
      ∃ k < s, l k = P := by
  classical
  obtain ⟨n, x, c, hs, rfl⟩ := h
  set v := c.program.trace (arithInterpretationWith K C) (X : Fin n → MvPolynomial (Fin n) K)
    with hv
  let pos : Wire n c.size → ℕ := fun
    | .input i => i
    | .gate j => n + j
  let l : ℕ → MvPolynomial σ K := fun k =>
    if h : k < n then MvPolynomial.rename x (v (.input ⟨k, h⟩))
    else if h' : k - n < c.size then MvPolynomial.rename x (v (.gate ⟨k - n, h'⟩)) else 0
  have hl : ∀ w, l (pos w) = MvPolynomial.rename x (v w) := by
    intro w
    cases w with
    | input i => simp [l, pos, i.isLt]
    | gate j =>
      have h1 : ¬ n + (j : ℕ) < n := by omega
      have h2 : n + (j : ℕ) - n = j := by omega
      simp only [l, pos, dite_eq_right h1, h2, j.isLt, dite_true]
  have hpos : ∀ w, pos w < n + c.size := by
    intro w
    cases w with
    | input i => exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
    | gate j => exact Nat.add_lt_add_left j.isLt n
  refine ⟨l, fun k hk => ?_, pos (c.outputs 0), (hpos _).trans_le hs, ?_⟩
  · by_cases hkn : k < n
    · left
      exact ⟨x ⟨k, hkn⟩, by simp [l, hkn, v]⟩
    by_cases hkg : k - n < c.size
    swap
    · exact Or.inr (Or.inl ⟨0, by simp [l, hkn, hkg]⟩)
    set j : Fin c.size := ⟨k - n, hkg⟩
    have hk : k = pos (.gate j) := by simp only [pos, j]; omega
    have hlt : ∀ a, pos ((c.program.lines j).wires a) < k := by
      intro a
      rw [hk]
      cases hw : (c.program.lines j).wires a with
      | input i => simp only [pos]; omega
      | gate j' =>
        have := c.program.lt_of_lines_wires_eq_gate j a j' hw
        simp only [pos]
        omega
    have hg : l k = MvPolynomial.rename x (arithInterpretationWith K C (c.program.lines j).op
        fun a => v ((c.program.lines j).wires a)) := by
      rw [hk]
      refine (hl (.gate j)).trans ?_
      rw [hv, Program.trace_gate]
    have hval : ∀ a, MvPolynomial.rename x (v ((c.program.lines j).wires a)) =
        l (pos ((c.program.lines j).wires a)) := fun a => (hl _).symm
    generalize c.program.lines j = L at hg hval hlt
    obtain ⟨op, ws⟩ := L
    cases op with
    | add =>
      refine Or.inr (Or.inr (Or.inl ⟨_, hlt 0, _, hlt 1, ?_⟩))
      rw [hg, ← hval 0, ← hval 1]
      simp [arithInterpretationWith]
    | mul =>
      refine Or.inr (Or.inr (Or.inr ⟨_, hlt 0, _, hlt 1, ?_⟩))
      rw [hg, ← hval 0, ← hval 1]
      simp [arithInterpretationWith]
    | const a =>
      exact Or.inr (Or.inl ⟨a, by rw [hg]; simp [arithInterpretationWith]⟩)
  · rw [hl, Circuit.polynomial_def]
    rfl

/-- A polynomial computed within `s` nodes has a finite set of constants: along any ring
homomorphism whose range contains them, it is the image of a polynomial computed within `s` nodes.
The set holds the constants of the gates of a circuit for `P`, with `0` for the gates
that are not constants. -/
theorem exists_finset_lift (h : ComputedWithin P s) :
    ∃ S : Finset K, ∀ {B : Type*} [CommSemiring B] (ι : B →+* K), (S : Set K) ⊆ Set.range ι →
      ∃ Q : MvPolynomial σ B, ComputedWithin Q s ∧ MvPolynomial.map ι Q = P := by
  classical
  obtain ⟨n, x, c, hs, rfl⟩ := h
  let cst : ArithOp K → K := fun
    | .const a => a
    | _ => 0
  refine ⟨Finset.univ.image fun k : Fin c.size => cst (c.program.lines k).op, fun {B} _ ι hS => ?_⟩
  let g : K → B := fun t => if h : t ∈ Set.range ι then h.choose else 0
  have hg : ∀ k : Fin c.size, ∀ a, (c.program.lines k).op = .const a → ι (g a) = a := by
    intro k a hk
    have ha : a ∈ Set.range ι := hS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_univ _,
      by rw [hk]⟩))
    simp only [g, ha, ↓reduceDIte]
    exact ha.choose_spec
  refine ⟨MvPolynomial.rename x ((c.mapOp (ArithOp.map g)).polynomial 0), ⟨n, x, _, hs, rfl⟩, ?_⟩
  rw [MvPolynomial.map_rename, ← Circuit.polynomial_mapOp_ringHom, ← Circuit.mapOp_comp,
    ArithOp.map_comp, Circuit.polynomial_mapOp, Circuit.polynomial_def]
  congr 1
  -- the two circuits agree gate by gate, since `ι ∘ g` fixes the constants of `c`
  have htr : c.program.trace (arithInterpretationWith K (C ∘ (ι ∘ g)))
      (X : Fin n → MvPolynomial (Fin n) K) = c.program.trace (arithInterpretationWith K C) X := by
    refine Program.eq_trace_of_forall_gate (fun i => by simp) fun k => ?_
    rw [Program.trace_gate]
    generalize hL : c.program.lines k = L
    obtain ⟨op, ws⟩ := L
    cases op with
    | add => rfl
    | mul => rfl
    | const a =>
      have := hg k a (by rw [hL])
      simp [arithInterpretationWith, this]
  simp only [Circuit.eval, Function.comp_apply, htr]

end ComputedWithin

/-! ### Affine projections -/

/-- `P` is *affine*: a constant, or a constant multiple of a variable plus a constant. -/
@[expose] def IsAffine (P : MvPolynomial σ K) : Prop :=
  (∃ b, P = C b) ∨ ∃ i a b, P = C a * X i + C b

/-- An affine polynomial has total degree at most `1`. -/
theorem IsAffine.totalDegree_le {P : MvPolynomial σ K} (hP : IsAffine P) : P.totalDegree ≤ 1 := by
  rcases hP with ⟨b, rfl⟩ | ⟨i, a, b, rfl⟩
  · simp
  · refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
    rw [C_mul_X_eq_monomial]
    exact (totalDegree_monomial_le _ _).trans (by simp)

/-- Substituting affine polynomials into an affine polynomial gives an affine polynomial. -/
theorem IsAffine.aeval {P : MvPolynomial τ K} (hP : IsAffine P) {ρ : τ → MvPolynomial σ K}
    (hρ : ∀ i, IsAffine (ρ i)) : IsAffine (aeval ρ P) := by
  rcases hP with ⟨b, rfl⟩ | ⟨i, a, b, rfl⟩
  · exact .inl ⟨b, aeval_C _ _⟩
  have h : MvPolynomial.aeval ρ (C a * X i + C b) = C a * ρ i + C b := by
    simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_eq]
  rcases hρ i with ⟨b', hb'⟩ | ⟨j, a', b', hb'⟩
  · exact .inl ⟨a * b' + b, by rw [h, hb', C_add, C_mul]⟩
  · exact .inr ⟨j, a * a', a * b' + b, by rw [h, hb', C_add, C_mul, C_mul]; ring⟩

/-- `P` is an *affine projection* of `Q`: substituting an affine polynomial for every variable of
`Q` gives `P`. -/
@[expose] def IsAffineProjection (P : MvPolynomial σ K) (Q : MvPolynomial τ K) : Prop :=
  ∃ ρ : τ → MvPolynomial σ K, (∀ i, IsAffine (ρ i)) ∧ aeval ρ Q = P

/-- An affine polynomial, with its variable read from input `i`, costs at most four gates. -/
private theorem synthesis_affine {P : MvPolynomial σ K} (hP : IsAffine P) (y₀ : σ) (i : Fin n) :
    ∃ (y : σ) (g : (Fin n → MvPolynomial σ K) → MvPolynomial σ K),
      Synthesis (arithInterpretationWith K C) (inputs n) {g} 4 ∧
        ∀ z : Fin n → MvPolynomial σ K, z i = X y → g z = P := by
  rcases hP with ⟨b, rfl⟩ | ⟨j, a, b, rfl⟩
  · exact ⟨y₀, fun _ => C b, (Synthesis.arith_const b).mono le_rfl le_rfl (by norm_num),
      fun _ _ => rfl⟩
  · have hmul := Synthesis.combine (result := fun z => C a * z i)
      (Synthesis.arith_const (R := MvPolynomial σ K) (constant := C) a)
      (Synthesis.of_mem (I := arithInterpretationWith K C)
        (Set.mem_range_self i : (fun z => z i) ∈ inputs n))
      (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hadd := Synthesis.combine (result := fun z => C a * z i + C b) hmul
      (Synthesis.arith_const (R := MvPolynomial σ K) (constant := C) b)
      (Synthesis.arith_add (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact ⟨j, _, hadd, fun z hz => by simp only [hz]⟩

/-- **Affine projections cost at most a factor five.** Each input of a circuit for `Q` is replaced
by its own input and at most four gates computing the substituted affine polynomial. -/
theorem ComputedWithin.of_isAffineProjection {P : MvPolynomial σ K} {Q : MvPolynomial τ K}
    {s : ℕ} (hQ : ComputedWithin Q s) (h : IsAffineProjection P Q) : ComputedWithin P (5 * s) := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  obtain ⟨n, x, c, hs, rfl⟩ := hQ
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨y₀⟩⟩
  · rw [eq_C_of_isEmpty (aeval ρ _)]
    have hpos : 0 < s := ComputedWithin.pos ⟨n, x, c, hs, rfl⟩
    exact (computedWithin_C _).mono (by omega)
  choose y g hg hgy using fun i => synthesis_affine (hρ (x i)) y₀ i
  obtain ⟨d, hd, hdsize⟩ := (Synthesis.family g (fun _ => 4) hg).exists_circuit_outputs
  refine ⟨n, y, c.comp d, ?_, ?_⟩
  · rw [Circuit.size_comp]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hdsize
    omega
  · rw [Circuit.rename_polynomial, Circuit.eval_comp, hd, aeval_rename,
      Circuit.aeval_polynomial_mvPolynomial]
    congr 1 with i : 1
    exact hgy i _ rfl

/-! ### VP -/

/-- **`VP` by circuit sizes.** A family is in `VP` exactly when it is a p-family whose members are
computed within a polynomially bounded number of nodes. -/
theorem mem_VP_iff {f : PolynomialFamily K} :
    f ∈ VP K ↔ f.IsPFamily ∧ ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧
      ∀ n, ComputedWithin (f.poly n) (b n) := by
  constructor
  · rintro ⟨hf, c, hc, hcf⟩
    refine ⟨hf, fun n => f.vars n + (c n).size, hf.1.add hc,
      fun n => ⟨f.vars n, id, c n, le_rfl, by rw [rename_id, AlgHom.id_apply, hcf]⟩⟩
  · rintro ⟨hf, b, hb, h⟩
    choose k x c hs hc using h
    refine ⟨hf, fun n => (c n).mapInputs (x n), hb.mono_of_le fun n => ?_, fun n => ?_⟩
    · exact (Nat.le_add_left _ _).trans (hs n)
    · rw [Circuit.polynomial_def, Circuit.eval_mapInputs, ← Circuit.rename_polynomial, hc]

end Arithmetic

end Cslib.Circuits
