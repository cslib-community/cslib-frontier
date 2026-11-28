/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.SyntacticMultilinear
import CslibFrontier.Foundations.Data.Finset.BiUnionFinTwo

/-!
# Balanced products in a syntactically multilinear circuit

A syntactically multilinear arithmetic circuit with `g` gates computes, under every specialization
of its inputs, a sum of at most `2 g + 1` products `A * B` in which `A` involves only the variables
of a set `U` and `B` only the others, with `a ≤ |U| ≤ b`. The list of sets `U` depends only on the
circuit, not on the specialization. This is the cut lemma of #8623
[Anonymous, Lemma 4][Anonymous2026MultilinearCircuits], in the form of a forward induction over the
gates.

**Scopes.** The inputs are specialized to polynomials `ρ i` in pairwise disjoint sets `V i` of
variables. The *scope* of a wire is the union of the sets `V i` of the inputs reaching it; the
polynomial at a wire involves only its scope
(`Cslib.Circuits.Program.vars_trace_subset_and_mem_restrictDegree`). A wire is *large* when its
scope has more than `b` variables.

**Exits.** An *exit* is an argument of a large gate that is a small wire: either argument of an
addition, or the argument of larger scope of a multiplication. Its *cut* contains the scope of the
small wire: for a multiplication it is that scope, which has at least `(b + 1) / 2` variables since
the larger argument has at least half of the scope of the gate; for an addition it is padded to `a`
variables inside the scope of the gate. Each gate has at most two exits.

**The invariant.** The polynomial at every large wire is a sum over the exits of a coefficient times
the polynomial at the exit. The coefficient of an exit avoids its cut, and vanishes unless the cut
lies in the scope of the wire. Additions add the coefficients of their arguments. A multiplication
multiplies the coefficients of its larger argument by the smaller one, whose scope is disjoint from
every cut below the larger argument by syntactic multilinearity. Exits start with coefficient `1`,
or the smaller argument of their multiplication.

## Main results

* `Cslib.Circuits.Circuit.exists_balanced_cuts`: the cut lemma.

## References

* [Anonymous, *A Stretched-Exponential Lower Bound for Syntactically Multilinear Circuits*,
  Lemma 4][Anonymous2026MultilinearCircuits]
-/

public section

namespace Cslib.Circuits

open MvPolynomial

universe u

variable {F : Type u} {τ K : Type*} [CommSemiring K] [DecidableEq τ] {n g : ℕ}

/-! ### Scopes and padded cuts -/

/-- The *scope* of a wire: the variables `V i` of the inputs `i` reaching it. -/
private def Program.scope (V : Fin n → Finset τ) (p : Program (arithSignature F) n g)
    (w : Wire n g) : Finset τ :=
  (p.wireSupport w).biUnion V

/-- Scopes are kept when a gate is appended. -/
@[simp] private theorem Program.scope_gate_castSucc (V : Fin n → Finset τ)
    (p : Program (arithSignature F) n g) (line : Line (arithSignature F) n g) (w : Wire n g) :
    (p.gate line).scope V w.castSucc = p.scope V w := by
  simp [scope]

/-- The scope of the last gate is the union of the scopes of its arguments. -/
private theorem Program.scope_gate_last (V : Fin n → Finset τ) (p : Program (arithSignature F) n g)
    (line : Line (arithSignature F) n g) :
    (p.gate line).scope V (Wire.gate (Fin.last g)) =
      Finset.univ.biUnion fun a => p.scope V (line.wires a) := by
  ext j
  simp [scope, Line.inputSupport]
  tauto

/-- The scope of an input is its set of variables. -/
@[simp] private theorem Program.scope_input (V : Fin n → Finset τ)
    (p : Program (arithSignature F) n g) (i : Fin n) : p.scope V (Wire.input i) = V i := by
  simp [scope]

variable (a : ℕ)

/-- A set of at least `a` variables between `s` and `t`: `s` padded to `max |s| a` variables of
`t`, when there are enough. -/
private noncomputable def padCut (s t : Finset τ) : Finset τ :=
  open Classical in
  if h : s ⊆ t ∧ max s.card a ≤ t.card then
    Classical.choose (Finset.exists_subsuperset_card_eq h.1 (le_max_left _ _) h.2)
  else s

variable {a}

/-- The padded cut lies between `s` and `t` and has `max |s| a` elements. -/
private theorem padCut_spec {s t : Finset τ} (h : s ⊆ t) (ht : max s.card a ≤ t.card) :
    s ⊆ padCut a s t ∧ padCut a s t ⊆ t ∧ (padCut a s t).card = max s.card a := by
  unfold padCut
  split_ifs with hc
  · exact Classical.choose_spec (Finset.exists_subsuperset_card_eq h (le_max_left _ _) ht)
  · exact absurd ⟨h, ht⟩ hc

/-! ### Exits -/

variable (V : Fin n → Finset τ) (a b : ℕ)

/-- The argument of larger scope of a multiplication, the first one in case of a tie. -/
private def Program.bigArg (p : Program (arithSignature F) n g) (w : Fin 2 → Wire n g) : Fin 2 :=
  if (p.scope V (w 1)).card ≤ (p.scope V (w 0)).card then 0 else 1

/-- The arguments of the line `line`, appended to `p`, that are exits: the small arguments of a
large addition, and the larger argument of a large multiplication when it is small. -/
private noncomputable def Program.lineExits (p : Program (arithSignature F) n g) :
    Line (arithSignature F) n g → Finset (Fin 2)
  | ⟨.add, w⟩ => open Classical in
    if b < (p.scope V (w 0) ∪ p.scope V (w 1)).card then
      Finset.univ.filter fun c => (p.scope V (w c)).card ≤ b
    else ∅
  | ⟨.mul, w⟩ => open Classical in
    if b < (p.scope V (w 0) ∪ p.scope V (w 1)).card ∧
        (p.scope V (w (p.bigArg V w))).card ≤ b then {p.bigArg V w}
    else ∅
  | ⟨.const _, _⟩ => ∅

/-- The cut of an exit of the line `line`: the scope of the argument, padded to `a` variables of
the scope of the gate for an addition. -/
private noncomputable def Program.lineCut (p : Program (arithSignature F) n g) :
    Line (arithSignature F) n g → Fin 2 → Finset τ
  | ⟨.add, w⟩, c => padCut a (p.scope V (w c)) (p.scope V (w 0) ∪ p.scope V (w 1))
  | ⟨.mul, w⟩, c => p.scope V (w c)
  | ⟨.const _, _⟩, _ => ∅

/-- The polynomial carried by an argument of the line `line`. -/
private noncomputable def Program.linePoly (φ : F → K) (ρ : Fin n → MvPolynomial τ K)
    (p : Program (arithSignature F) n g) : Line (arithSignature F) n g → Fin 2 → MvPolynomial τ K
  | ⟨.add, w⟩, c => p.trace (arithInterpretationWith F (C ∘ φ)) ρ (w c)
  | ⟨.mul, w⟩, c => p.trace (arithInterpretationWith F (C ∘ φ)) ρ (w c)
  | ⟨.const _, _⟩, _ => 0

/-- The *exits* of a program: pairs of a gate number and an argument. -/
private noncomputable def Program.exits :
    {g : ℕ} → Program (arithSignature F) n g → Finset (ℕ × Fin 2)
  | _, .empty => ∅
  | _, @Program.gate _ _ g p line => p.exits ∪ (p.lineExits V b line).image fun c => (g, c)

/-- The cut of each exit. -/
private noncomputable def Program.exitCut : {g : ℕ} → Program (arithSignature F) n g → ℕ × Fin 2 →
    Finset τ
  | _, .empty, _ => ∅
  | _, @Program.gate _ _ g p line, e => if e.1 = g then p.lineCut V a line e.2 else p.exitCut e

/-- The polynomial at each exit. -/
private noncomputable def Program.exitPoly (φ : F → K) (ρ : Fin n → MvPolynomial τ K) :
    {g : ℕ} → Program (arithSignature F) n g → ℕ × Fin 2 → MvPolynomial τ K
  | _, .empty, _ => 0
  | _, @Program.gate _ _ g p line, e =>
    if e.1 = g then p.linePoly φ ρ line e.2 else p.exitPoly φ ρ e

variable {V a b}

/-- The exits of a program are at its gates. -/
private theorem Program.lt_of_mem_exits :
    ∀ {g : ℕ} (p : Program (arithSignature F) n g) {e : ℕ × Fin 2}, e ∈ p.exits V b → e.1 < g
  | _, .empty, _, h => absurd h (Finset.notMem_empty _)
  | _, .gate p line, e, h => by
    rcases Finset.mem_union.mp h with h | h
    · exact Nat.lt_succ_of_lt (p.lt_of_mem_exits h)
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp h
      exact Nat.lt_succ_self _

/-- A program has at most two exits for each gate. -/
private theorem Program.card_exits_le : ∀ {g : ℕ} (p : Program (arithSignature F) n g),
    (p.exits V b).card ≤ 2 * g
  | _, .empty => by simp [exits]
  | _, @Program.gate _ _ g p line => by
    have hp := p.card_exits_le
    have hl : ((p.lineExits V b line).image fun c => ((g, c) : ℕ × Fin 2)).card ≤ 2 :=
      Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
    rw [exits]
    exact (Finset.card_union_le _ _).trans (by omega)

/-! ### Exits of a program with one more gate -/

private theorem Program.mem_exits_gate_iff (p : Program (arithSignature F) n g)
    (line : Line (arithSignature F) n g) (e : ℕ × Fin 2) :
    e ∈ (p.gate line).exits V b ↔ e ∈ p.exits V b ∨ (e.1 = g ∧ e.2 ∈ p.lineExits V b line) := by
  rw [exits, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨c, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hc⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e.2, h2, by ext <;> simp [h1]⟩

private theorem Program.exitCut_gate_of_mem (p : Program (arithSignature F) n g)
    (line : Line (arithSignature F) n g) {e : ℕ × Fin 2} (he : e ∈ p.exits V b) :
    (p.gate line).exitCut V a e = p.exitCut V a e := by
  simp [exitCut, (p.lt_of_mem_exits he).ne]

private theorem Program.exitPoly_gate_of_mem (φ : F → K) (ρ : Fin n → MvPolynomial τ K)
    (p : Program (arithSignature F) n g) (line : Line (arithSignature F) n g) {e : ℕ × Fin 2}
    (he : e ∈ p.exits V b) : (p.gate line).exitPoly φ ρ e = p.exitPoly φ ρ e := by
  simp [exitPoly, (p.lt_of_mem_exits he).ne]

@[simp] private theorem Program.exitCut_gate_self (p : Program (arithSignature F) n g)
    (line : Line (arithSignature F) n g) (c : Fin 2) :
    (p.gate line).exitCut V a (g, c) = p.lineCut V a line c := by
  simp [exitCut]

omit [DecidableEq τ] in
@[simp] private theorem Program.exitPoly_gate_self (φ : F → K) (ρ : Fin n → MvPolynomial τ K)
    (p : Program (arithSignature F) n g) (line : Line (arithSignature F) n g) (c : Fin 2) :
    (p.gate line).exitPoly φ ρ (g, c) = p.linePoly φ ρ line c := by
  simp [exitPoly]

/-- A sum over the exits of `p`, seen in the program with one more gate. -/
private theorem Program.sum_exits_gate (φ : F → K) (ρ : Fin n → MvPolynomial τ K)
    (p : Program (arithSignature F) n g) (line : Line (arithSignature F) n g)
    (M : ℕ × Fin 2 → MvPolynomial τ K) :
    ∑ e ∈ (p.gate line).exits V b, (open Classical in if e ∈ p.exits V b then M e else 0) *
        (p.gate line).exitPoly φ ρ e = ∑ e ∈ p.exits V b, M e * p.exitPoly φ ρ e := by
  classical
  rw [← Finset.sum_subset (s₁ := p.exits V b) (fun e he => (p.mem_exits_gate_iff line e).2
    (Or.inl he)) fun e _ he => by simp [he]]
  exact Finset.sum_congr rfl fun e he => by
    simp only [he, ↓reduceIte, p.exitPoly_gate_of_mem φ ρ line he]

/-- A sum over the exits of a program with one more gate, with a single nonzero coefficient at an
exit of the new gate. -/
private theorem Program.sum_exits_gate_single (φ : F → K) (ρ : Fin n → MvPolynomial τ K)
    (p : Program (arithSignature F) n g) (line : Line (arithSignature F) n g) {c : Fin 2}
    (hc : c ∈ p.lineExits V b line) (m : MvPolynomial τ K) :
    ∑ e ∈ (p.gate line).exits V b, (open Classical in if e = (g, c) then m else 0) *
        (p.gate line).exitPoly φ ρ e = m * p.linePoly φ ρ line c := by
  classical
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', (p.mem_exits_gate_iff line (g, c)).2
    (Or.inr ⟨rfl, hc⟩), ↓reduceIte, exitPoly_gate_self]

/-! ### Sizes of the cuts and polynomials at the exits -/

/-- The cuts have between `a` and `b` variables. -/
private theorem Program.card_exitCut (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) :
    ∀ {g : ℕ} (p : Program (arithSignature F) n g) {e : ℕ × Fin 2}, e ∈ p.exits V b →
      a ≤ (p.exitCut V a e).card ∧ (p.exitCut V a e).card ≤ b
  | _, .empty, _, h => absurd h (Finset.notMem_empty _)
  | _, .gate p line, e, he => by
    rcases (p.mem_exits_gate_iff line e).1 he with he | ⟨h1, h2⟩
    · rw [p.exitCut_gate_of_mem line he]
      exact p.card_exitCut hab ha he
    · obtain ⟨e1, c⟩ := e
      simp only at h1 h2
      subst h1
      rw [exitCut_gate_self]
      obtain ⟨op, w⟩ := line
      cases op with
      | add =>
        simp only [lineExits] at h2
        split_ifs at h2 with hl
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
          have hsub : p.scope V (w c) ⊆ p.scope V (w 0) ∪ p.scope V (w 1) := by
            fin_cases c
            · exact Finset.subset_union_left
            · exact Finset.subset_union_right
          have hle := Finset.card_le_card hsub
          rw [lineCut, (padCut_spec hsub (max_le hle (by omega))).2.2]
          omega
        · simp at h2
      | mul =>
        simp only [lineExits] at h2
        split_ifs at h2 with hl
        · rw [Finset.mem_singleton.mp h2, lineCut]
          have hu := Finset.card_union_le (p.scope V (w 0)) (p.scope V (w 1))
          unfold bigArg at hl ⊢
          split_ifs at hl ⊢ <;> omega
        · simp at h2
      | const c' => simp [lineExits] at h2

/-! ### The invariant -/

section Invariant

variable {φ : F → K} {ρ : Fin n → MvPolynomial τ K}
  (hV : Pairwise fun i j => Disjoint (V i) (V j)) (hvars : ∀ i, (ρ i).vars ⊆ V i)
  (hdeg : ∀ i, ρ i ∈ restrictDegree τ K 1)
include hV hvars hdeg

/-- The polynomial at a wire involves only its scope. -/
private theorem Program.vars_trace_subset_scope {p : Program (arithSignature F) n g}
    (hp : p.IsDecomposableAt (· = .mul)) (w : Wire n g) :
    (p.trace (arithInterpretationWith F (C ∘ φ)) ρ w).vars ⊆ p.scope V w :=
  (p.vars_trace_subset_and_mem_restrictDegree hp φ ρ V hV hvars hdeg w).1

/-- The polynomial at each exit involves only its cut. -/
private theorem Program.vars_exitPoly_subset (hab : a ≤ b) :
    ∀ {g : ℕ} (p : Program (arithSignature F) n g),
    p.IsDecomposableAt (· = .mul) → ∀ e ∈ p.exits V b,
      (p.exitPoly φ ρ e).vars ⊆ p.exitCut V a e
  | _, .empty, _, _, h => absurd h (Finset.notMem_empty _)
  | _, .gate p line, hp, e, he => by
    rw [isDecomposableAt_gate_iff] at hp
    rcases (p.mem_exits_gate_iff line e).1 he with he | ⟨h1, h2⟩
    · rw [p.exitCut_gate_of_mem line he, p.exitPoly_gate_of_mem φ ρ line he]
      exact p.vars_exitPoly_subset hab hp.1 e he
    · obtain ⟨e1, c⟩ := e
      simp only at h1 h2
      subst h1
      rw [exitCut_gate_self, exitPoly_gate_self]
      obtain ⟨op, w⟩ := line
      cases op with
      | add =>
        have hw := p.vars_trace_subset_scope hV hvars hdeg (φ := φ) hp.1 (w c)
        simp only [lineExits] at h2
        split_ifs at h2 with hl
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
          have hsub : p.scope V (w c) ⊆ p.scope V (w 0) ∪ p.scope V (w 1) := by
            fin_cases c
            · exact Finset.subset_union_left
            · exact Finset.subset_union_right
          exact hw.trans (padCut_spec hsub (max_le (Finset.card_le_card hsub) (by omega))).1
        · simp at h2
      | mul => exact p.vars_trace_subset_scope hV hvars hdeg (φ := φ) hp.1 (w c)
      | const c' => simp [lineExits] at h2

/-- **The invariant.** The polynomial at a large wire is a sum over the exits of a coefficient times
the polynomial at the exit. The coefficient of an exit involves no variable of its cut and vanishes
unless the cut lies in the scope of the wire. -/
private theorem Program.exists_coeff_large (hVb : ∀ i, (V i).card ≤ b) (hab : a ≤ b) :
    ∀ {g : ℕ} (p : Program (arithSignature F) n g), p.IsDecomposableAt (· = .mul) →
      ∀ w, b < (p.scope V w).card → ∃ M : ℕ × Fin 2 → MvPolynomial τ K,
        (∀ e ∈ p.exits V b, Disjoint (M e).vars (p.exitCut V a e) ∧
          (M e ≠ 0 → p.exitCut V a e ⊆ p.scope V w)) ∧
        p.trace (arithInterpretationWith F (C ∘ φ)) ρ w =
          ∑ e ∈ p.exits V b, M e * p.exitPoly φ ρ e
  | _, .empty, _, w, hw => by
    cases w with
    | input i => exact absurd (hVb i) (by simpa using hw.not_ge)
    | gate k => exact k.elim0
  | _, @Program.gate _ _ g p line, hp, w, hw => by
    classical
    rw [isDecomposableAt_gate_iff] at hp
    have ih := p.exists_coeff_large hVb hab hp.1
    -- An argument of the new gate, large or an exit, as a sum over the exits.
    have hold (u : Wire n g) (hu : b < (p.scope V u).card) : ∃ M : ℕ × Fin 2 → MvPolynomial τ K,
        (∀ e ∈ (p.gate line).exits V b, Disjoint (M e).vars ((p.gate line).exitCut V a e) ∧
          (M e ≠ 0 → (p.gate line).exitCut V a e ⊆ p.scope V u)) ∧
        p.trace (arithInterpretationWith F (C ∘ φ)) ρ u =
          ∑ e ∈ (p.gate line).exits V b, M e * (p.gate line).exitPoly φ ρ e := by
      obtain ⟨M, hM, hsum⟩ := ih u hu
      refine ⟨fun e => if e ∈ p.exits V b then M e else 0, fun e he => ?_, ?_⟩
      · by_cases he' : e ∈ p.exits V b
        · simp only [he', ↓reduceIte, p.exitCut_gate_of_mem line he']
          exact hM e he'
        · simp [he']
      · rw [hsum, p.sum_exits_gate φ ρ line M]
    revert hw
    refine Wire.lastCases (fun hw => ?_) (fun w hw => ?_) w
    · rw [scope_gate_last] at hw
      change ∃ M, _ ∧ (p.gate line).eval _ ρ (Fin.last g) = _
      rw [eval_gate_last]
      obtain ⟨op, args⟩ := line
      cases op with
      | const c => simp at hw
      | add =>
        rw [Finset.biUnion_univ_fin_two] at hw
        change b < (p.scope V (args 0) ∪ p.scope V (args 1)).card at hw
        have hS (c : Fin 2) : p.scope V (args c) ⊆
            (p.gate ⟨.add, args⟩).scope V (Wire.gate (Fin.last g)) := by
          rw [scope_gate_last, Finset.biUnion_univ_fin_two]
          fin_cases c
          · exact Finset.subset_union_left
          · exact Finset.subset_union_right
        have harg (c : Fin 2) : ∃ M : ℕ × Fin 2 → MvPolynomial τ K,
            (∀ e ∈ (p.gate ⟨.add, args⟩).exits V b,
              Disjoint (M e).vars ((p.gate ⟨.add, args⟩).exitCut V a e) ∧
              (M e ≠ 0 → (p.gate ⟨.add, args⟩).exitCut V a e ⊆
                (p.gate ⟨.add, args⟩).scope V (Wire.gate (Fin.last g)))) ∧
            p.trace (arithInterpretationWith F (C ∘ φ)) ρ (args c) =
              ∑ e ∈ (p.gate ⟨.add, args⟩).exits V b,
                M e * (p.gate ⟨.add, args⟩).exitPoly φ ρ e := by
          by_cases hc : b < (p.scope V (args c)).card
          · obtain ⟨M, hM, hsum⟩ := hold (args c) hc
            exact ⟨M, fun e he => ⟨(hM e he).1, fun h => ((hM e he).2 h).trans (hS c)⟩, hsum⟩
          · have hcx : c ∈ p.lineExits V b ⟨.add, args⟩ := by
              simp only [lineExits, hw, ↓reduceIte]
              simpa using hc
            refine ⟨fun e => if e = (g, c) then 1 else 0, fun e he => ?_, ?_⟩
            · by_cases hec : e = (g, c)
              · subst hec
                refine ⟨by simp, fun _ => ?_⟩
                rw [exitCut_gate_self, scope_gate_last, Finset.biUnion_univ_fin_two]
                have hsub : p.scope V (args c) ⊆ p.scope V (args 0) ∪ p.scope V (args 1) := by
                  fin_cases c
                  · exact Finset.subset_union_left
                  · exact Finset.subset_union_right
                exact (padCut_spec hsub (max_le (Finset.card_le_card hsub) (by omega))).2.1
              · simp [hec]
            · rw [p.sum_exits_gate_single φ ρ _ hcx, one_mul]
              rfl
        obtain ⟨M₀, hM₀, h₀⟩ := harg 0
        obtain ⟨M₁, hM₁, h₁⟩ := harg 1
        refine ⟨M₀ + M₁, fun e he => ⟨?_, fun h => ?_⟩, ?_⟩
        · exact Finset.disjoint_of_subset_left (vars_add_subset _ _)
            (Finset.disjoint_union_left.mpr ⟨(hM₀ e he).1, (hM₁ e he).1⟩)
        · by_cases h0 : M₀ e = 0
          · exact (hM₁ e he).2 fun h1 => h (by simp [h0, h1])
          · exact (hM₀ e he).2 h0
        · change p.trace _ ρ (args 0) + p.trace _ ρ (args 1) = _
          rw [h₀, h₁, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun e _ => (add_mul _ _ _).symm
      | mul =>
        rw [Finset.biUnion_univ_fin_two] at hw
        change b < (p.scope V (args 0) ∪ p.scope V (args 1)).card at hw
        have hdisj : Disjoint (p.scope V (args 0)) (p.scope V (args 1)) := by
          have h : Disjoint (p.wireSupport (args 0)) (p.wireSupport (args 1)) :=
            hp.2 rfl (show (0 : Fin 2) ≠ 1 by decide)
          rw [Finset.disjoint_left]
          intro t ht0 ht1
          simp only [scope, Finset.mem_biUnion] at ht0 ht1
          obtain ⟨i, hi, hti⟩ := ht0
          obtain ⟨j, hj, htj⟩ := ht1
          by_cases hij : i = j
          · subst hij
            exact Finset.disjoint_left.mp h hi hj
          · exact Finset.disjoint_left.mp (hV hij) hti htj
        set big := p.bigArg V args with hbig
        have hother : ∃ o : Fin 2, o ≠ big ∧
            Disjoint (p.scope V (args big)) (p.scope V (args o)) ∧
            p.trace (arithInterpretationWith F (C ∘ φ)) ρ (args 0) *
              p.trace (arithInterpretationWith F (C ∘ φ)) ρ (args 1) =
            p.trace (arithInterpretationWith F (C ∘ φ)) ρ (args big) *
              p.trace (arithInterpretationWith F (C ∘ φ)) ρ (args o) := by
          rcases (show big = 0 ∨ big = 1 by rw [hbig, bigArg]; split_ifs <;> simp) with h | h <;>
            rw [h]
          · exact ⟨1, by decide, hdisj, rfl⟩
          · exact ⟨0, by decide, hdisj.symm, mul_comm _ _⟩
        obtain ⟨o, -, hdo, hprod⟩ := hother
        have hS : p.scope V (args big) ⊆
            (p.gate ⟨.mul, args⟩).scope V (Wire.gate (Fin.last g)) := by
          rw [scope_gate_last]
          exact Finset.subset_biUnion_of_mem (fun c => p.scope V (args c)) (Finset.mem_univ big)
        have ho := p.vars_trace_subset_scope hV hvars hdeg (φ := φ) hp.1 (args o)
        change ∃ M, _ ∧ p.trace _ ρ (args 0) * p.trace _ ρ (args 1) = _
        rw [hprod]
        by_cases hb : b < (p.scope V (args big)).card
        · obtain ⟨M, hM, hsum⟩ := hold (args big) hb
          refine ⟨fun e => M e * p.trace (arithInterpretationWith F (C ∘ φ)) ρ (args o),
            fun e he => ⟨?_, fun h => ((hM e he).2 (left_ne_zero_of_mul h)).trans hS⟩, ?_⟩
          · by_cases h0 : M e = 0
            · simp [h0]
            · refine Finset.disjoint_of_subset_left (vars_mul _ _)
                (Finset.disjoint_union_left.mpr ⟨(hM e he).1, ?_⟩)
              exact Finset.disjoint_of_subset_left ho
                (Finset.disjoint_of_subset_right ((hM e he).2 h0) hdo.symm)
          · rw [hsum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun e _ => by ring
        · have hcx : big ∈ p.lineExits V b ⟨.mul, args⟩ := by
            have hcond : b < (p.scope V (args 0) ∪ p.scope V (args 1)).card ∧
                (p.scope V (args big)).card ≤ b := ⟨hw, not_lt.mp hb⟩
            simp only [lineExits, ← hbig]
            simp only [hcond, and_self, ↓reduceIte, Finset.mem_singleton]
          refine ⟨fun e => if e = (g, big) then p.trace (arithInterpretationWith F (C ∘ φ)) ρ
            (args o) else 0, fun e he => ?_, ?_⟩
          · by_cases hec : e = (g, big)
            · subst hec
              simp only [↓reduceIte, exitCut_gate_self, lineCut]
              exact ⟨Finset.disjoint_of_subset_left ho hdo.symm, fun _ => hS⟩
            · simp [hec]
          · rw [p.sum_exits_gate_single φ ρ _ hcx]
            exact mul_comm _ _
    · rw [scope_gate_castSucc] at hw
      obtain ⟨M, hM, hsum⟩ := hold w hw
      refine ⟨M, fun e he => ⟨(hM e he).1, fun h => by
        rw [scope_gate_castSucc]
        exact (hM e he).2 h⟩, ?_⟩
      rw [trace_gate_castSucc]
      exact hsum

end Invariant

/-! ### The cut lemma -/

omit [DecidableEq τ] in
/-- **Balanced products in a syntactically multilinear circuit.** Let the inputs of a syntactically
multilinear arithmetic circuit with `s` gates carry pairwise disjoint sets `V i` of at most `b`
variables. There are at most `2 s + 1` sets `U` of variables, with `a ≤ |U| ≤ b`, such that under
every specialization of the inputs to multilinear polynomials `ρ i` in the variables `V i`, the
circuit computes a sum of products `A * B` over these sets, `A` in the variables of `U` and `B` in
the others. The sets depend only on the circuit and on the sets `V i`. Here `a ≤ b`,
`2 a ≤ b + 2` and the variables are at least `a`. -/
theorem Circuit.exists_balanced_cuts [Fintype τ] (c : Circuit (arithSignature F) n 1)
    (hc : c.program.IsDecomposableAt (· = .mul)) (V : Fin n → Finset τ)
    (hV : Pairwise fun i j => Disjoint (V i) (V j)) {a b : ℕ} (hVb : ∀ i, (V i).card ≤ b)
    (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (haτ : a ≤ Fintype.card τ) :
    ∃ (L : ℕ) (cut : Fin L → Finset τ), L ≤ 2 * c.size + 1 ∧
      (∀ j, a ≤ (cut j).card ∧ (cut j).card ≤ b) ∧
      ∀ (φ : F → K) (ρ : Fin n → MvPolynomial τ K), (∀ i, (ρ i).vars ⊆ V i) →
        (∀ i, ρ i ∈ restrictDegree τ K 1) →
        ∃ A B : Fin L → MvPolynomial τ K, (∀ j, (A j).vars ⊆ cut j) ∧
          (∀ j, Disjoint (B j).vars (cut j)) ∧
          c.eval (arithInterpretationWith F (C ∘ φ)) ρ 0 = ∑ j, A j * B j := by
  classical
  set p := c.program
  set E := p.exits V b
  set S := p.scope V (c.outputs 0)
  set S' := if S.card ≤ b then S else ∅ with hS'
  have hS'card : S'.card ≤ b := by
    rw [hS']
    split_ifs with h
    · exact h
    · simp
  have hU0 := padCut_spec (a := a) (Finset.subset_univ S')
    (max_le (Finset.card_le_univ _) haτ)
  set e := E.equivFin.symm
  refine ⟨E.card + 1, Fin.lastCases (padCut a S' Finset.univ) fun j => p.exitCut V a (e j),
    by have : E.card ≤ 2 * c.size := p.card_exits_le; omega, fun j => ?_,
    fun φ ρ hvars hdeg => ?_⟩
  · induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last, hU0.2.2]
      exact ⟨le_max_right _ _, max_le hS'card hab⟩
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact p.card_exitCut hab ha (e j).2
  · have hsumE (f : ℕ × Fin 2 → MvPolynomial τ K) :
        ∑ x ∈ E, f x = ∑ j : Fin E.card, f (e j) := by
      rw [← Finset.sum_coe_sort E]
      exact (Equiv.sum_comp e fun x => f x).symm
    by_cases hlarge : b < S.card
    · obtain ⟨M, hM, hsum⟩ := p.exists_coeff_large hV hvars hdeg hVb hab hc _ hlarge
      refine ⟨Fin.lastCases 0 fun j => p.exitPoly φ ρ (e j),
        Fin.lastCases 0 fun j => M (e j), fun j => ?_, fun j => ?_, ?_⟩
      · induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact p.vars_exitPoly_subset hV hvars hdeg hab hc _ (e j).2
      · induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact (hM _ (e j).2).1
      · change p.trace _ ρ (c.outputs 0) = _
        rw [hsum, Fin.sum_univ_castSucc, hsumE]
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · have hS'eq : S' = S := by simp [hS', not_lt.mp hlarge]
      refine ⟨Fin.lastCases (p.trace (arithInterpretationWith F (C ∘ φ)) ρ (c.outputs 0)) 0,
        Fin.lastCases 1 0, fun j => ?_, fun j => ?_, ?_⟩
      · induction j using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last]
          exact (p.vars_trace_subset_scope hV hvars hdeg hc _).trans (hS'eq ▸ hU0.1)
        | cast j => simp
      · induction j using Fin.lastCases with
        | last => simp
        | cast j => simp
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Pi.zero_apply, zero_mul,
          Finset.sum_const_zero, zero_add, mul_one]
        rfl

end Cslib.Circuits
