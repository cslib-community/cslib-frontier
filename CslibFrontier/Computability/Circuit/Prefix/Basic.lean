/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.CriticalPath
public import Mathlib.Algebra.Free
import CslibFrontier.Computability.Circuit.Basic
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Program
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Universal fanout-bounded prefix circuits and the Snir–Fich trade-off

Following Sergeev [Sergeev2025PrefixDepth], we formalize universal prefix circuits over the basis
`{mul, id}` (`Cslib.Circuits.Prefix.prefixSignature`) that compute all prefix products
`s_j = x_0 * x_1 * ⋯ * x_j` in every semigroup `(S, *)`. Here the *complexity* `binaryComplexity c`
counts binary `mul` gates, *depth* `c.depth` counts both `mul` and `id` gates along the longest
input-to-output path, and *fanout* `wireFanout c w` counts both internal gate input slots reading
`w` and external output designations equal to `w`.

We prove that universal correctness across all semigroups is equivalent to correctness over the
single free semigroup `FreeSemigroup (Fin N)` (`isUniversalPrefixCircuit_iff_freeSemigroup`), giving
decidability (`instDecidableIsUniversalPrefixCircuit`), and follows from contiguous-interval gate
labeling (`IsIntervalPrefixCircuit.isUniversalPrefixCircuit`). Decomposing the DAG into its
framework tree of `mul` ancestors of output `N - 1` and its output-defining `mul` gates yields the
Snir–Fich lower bound `2 * N - 2 ≤ binaryComplexity c + c.depth`
(`two_mul_sub_two_le_binaryComplexity_add_depth`), motivating *optimal* (zero-deficiency) prefix
circuits (`IsOptimalPrefixCircuit`).

## Main definitions

* `Cslib.Circuits.Prefix.PrefixOp`, `Cslib.Circuits.Prefix.prefixSignature`,
  `Cslib.Circuits.Prefix.PrefixCircuit`: prefix circuit signature `{mul, id}` and `N`-input,
  `N`-output circuits over it.
* `Cslib.Circuits.Prefix.semigroupInterp`, `Cslib.Circuits.Prefix.prefixProd`,
  `Cslib.Circuits.Prefix.IsUniversalPrefixCircuit`,
  `Cslib.Circuits.Prefix.IsIntervalPrefixCircuit`: evaluation in arbitrary semigroups, universal
  prefix correctness, and contiguous-interval circuit labeling.
* `Cslib.Circuits.Prefix.binaryComplexity`, `Cslib.Circuits.Prefix.wireFanout`,
  `Cslib.Circuits.Prefix.FanoutAtMost`, `Cslib.Circuits.Prefix.IsOptimalPrefixCircuit`: binary gate
  complexity, wire fanout (including external output poles), fanout bound, and zero-deficiency
  optimality.

## Main results

* `Cslib.Circuits.Prefix.isUniversalPrefixCircuit_iff_freeSemigroup`,
  `Cslib.Circuits.Prefix.IsIntervalPrefixCircuit.isUniversalPrefixCircuit`: universal correctness
  across all semigroups is equivalent to correctness on `FreeSemigroup (Fin N)` and follows from
  contiguous interval labeling.
* `Cslib.Circuits.Prefix.two_mul_sub_two_le_binaryComplexity_add_depth`: Snir–Fich lower bound
  `2 * N - 2 ≤ binaryComplexity c + c.depth` for `N ≥ 1`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

/-! ### Part 1: Universal fanout-bounded prefix circuits and zero-deficiency optimality -/

/-- Operations of a fanout-bounded prefix circuit: binary semigroup multiplication `mul` (`x ◦ y`)
and unary identity buffer `id` (`x`) used to replicate values under bounded fanout. -/
inductive PrefixOp : Type
  | mul : PrefixOp
  | id : PrefixOp
  deriving DecidableEq, Repr

/-- Arity of each prefix circuit operation: `2` for `mul` and `1` for `id`. -/
abbrev PrefixOp.arity : PrefixOp → ℕ
  | .mul => 2
  | .id => 1

/-- The circuit signature `{mul, id}` for fanout-bounded prefix circuits. -/
abbrev prefixSignature : Signature where
  Op := PrefixOp
  Arity := PrefixOp.arity

/-- An `N`-input, `N`-output prefix circuit over `{mul, id}`. -/
abbrev PrefixCircuit (N : ℕ) : Type :=
  Circuit prefixSignature N N

/-- Interpretation of `prefixSignature` in any semigroup `(S, *)`. -/
@[expose] def semigroupInterp (S : Type*) [Semigroup S] : Interpretation prefixSignature S
  | .mul, args => args 0 * args 1
  | .id, args => args 0

/-- The `j`-th prefix product `x 0 * x 1 * ⋯ * x j` of `x : Fin N → S` in a semigroup `S`. -/
@[expose] def prefixProd {S : Type*} [Semigroup S] {N : ℕ} (x : Fin N → S) (j : Fin N) : S :=
  Nat.recOn j.val (fun h0 => x ⟨0, h0⟩)
    (fun m ih hm => ih (Nat.lt_of_succ_lt hm) * x ⟨m + 1, hm⟩) j.isLt

@[simp] theorem prefixProd_zero {S : Type*} [Semigroup S] {N : ℕ} (h0 : 0 < N) (x : Fin N → S) :
    prefixProd x ⟨0, h0⟩ = x ⟨0, h0⟩ := rfl

@[simp] theorem prefixProd_succ {S : Type*} [Semigroup S] {N : ℕ} {m : ℕ} (hm : m + 1 < N)
    (x : Fin N → S) :
    prefixProd x ⟨m + 1, hm⟩ = prefixProd x ⟨m, Nat.lt_of_succ_lt hm⟩ * x ⟨m + 1, hm⟩ := rfl

private theorem map_prefixProd {S T : Type*} [Semigroup S] [Semigroup T] (f : S →ₙ* T)
    {N : ℕ} (x : Fin N → S) (j : Fin N) :
    f (prefixProd x j) = prefixProd (f ∘ x) j := by
  rcases j with ⟨m, hm⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [prefixProd_succ, map_mul, ih (Nat.lt_of_succ_lt hm), Function.comp_apply]

private def mulHomToInterpHom {S T : Type*} [Semigroup S] [Semigroup T] (f : S →ₙ* T) :
    Homomorphism (semigroupInterp S) (semigroupInterp T) where
  map := f
  homomorphic
    | .mul, args => by simp only [semigroupInterp, map_mul, Function.comp_apply]
    | .id, args => rfl

/-- A prefix circuit `c` is *universal* if it computes `prefixProd` in every semigroup `(S, *)`
([Sergeev2025PrefixDepth], p. 1, Eq. (1)). -/
@[expose] def IsUniversalPrefixCircuit {N : ℕ} (c : PrefixCircuit N) : Prop :=
  ∀ (S : Type) [Semigroup S], c.Computes (semigroupInterp S) prefixProd

private theorem computes_of_eval_freeSemigroup {N : ℕ} {c : PrefixCircuit N}
    (hfree : c.eval (semigroupInterp (FreeSemigroup (Fin N))) FreeSemigroup.of =
      prefixProd FreeSemigroup.of)
    (S : Type*) [Semigroup S] :
    c.Computes (semigroupInterp S) prefixProd := by
  intro x
  have hmap := c.map_eval (mulHomToInterpHom (FreeSemigroup.lift x)) FreeSemigroup.of
  have hlift : (FreeSemigroup.lift x : FreeSemigroup (Fin N) → S) ∘ FreeSemigroup.of = x :=
    funext (FreeSemigroup.lift_of x)
  change (FreeSemigroup.lift x : FreeSemigroup (Fin N) → S) ∘
      c.eval (semigroupInterp (FreeSemigroup (Fin N))) FreeSemigroup.of =
    c.eval (semigroupInterp S) ((FreeSemigroup.lift x : FreeSemigroup (Fin N) → S) ∘
      FreeSemigroup.of) at hmap
  rw [hlift, hfree] at hmap
  funext j
  exact (congrFun hmap j).symm.trans
    ((map_prefixProd (FreeSemigroup.lift x) FreeSemigroup.of j).trans
      (congrArg (fun f => prefixProd f j) hlift))

/-- Universal correctness over `Type` is equivalent to evaluating correctly on the canonical
generators `FreeSemigroup.of` of `FreeSemigroup (Fin N)`. -/
theorem isUniversalPrefixCircuit_iff_freeSemigroup {N : ℕ} (c : PrefixCircuit N) :
    IsUniversalPrefixCircuit c ↔
      c.eval (semigroupInterp (FreeSemigroup (Fin N))) FreeSemigroup.of =
        prefixProd FreeSemigroup.of :=
  ⟨fun hc => hc (FreeSemigroup (Fin N)) FreeSemigroup.of,
    fun hfree S _ => computes_of_eval_freeSemigroup hfree S⟩

/-- A universal prefix circuit computes `prefixProd` in every semigroup in any universe. -/
theorem IsUniversalPrefixCircuit.computes {N : ℕ} {c : PrefixCircuit N}
    (hc : IsUniversalPrefixCircuit c) (S : Type*) [Semigroup S] :
    c.Computes (semigroupInterp S) prefixProd :=
  computes_of_eval_freeSemigroup ((isUniversalPrefixCircuit_iff_freeSemigroup c).mp hc) S

instance instDecidableIsUniversalPrefixCircuit {N : ℕ} (c : PrefixCircuit N) :
    Decidable (IsUniversalPrefixCircuit c) :=
  decidable_of_iff' _ (isUniversalPrefixCircuit_iff_freeSemigroup c)

/-- A prefix circuit is *interval-labeled* if every wire carries a nonempty contiguous input
interval `[lo w, hi w)` with inputs carrying `[i, i + 1)`, `id` preserving the interval, `mul`
concatenating adjacent intervals `[a, m)` and `[m, b)`, and output `j` carrying `[0, j + 1)`
([Sergeev2025PrefixDepth], p. 1). -/
@[expose] def IsIntervalPrefixCircuit {N : ℕ} (c : PrefixCircuit N) : Prop :=
  ∃ lo hi : Wire N c.size → ℕ,
    (∀ i : Fin N, lo (.input i) = i.val ∧ hi (.input i) = i.val + 1) ∧
    (∀ g : Fin c.size,
      match c.program.lines g with
      | ⟨.id, wires⟩ => lo (.gate g) = lo (wires 0) ∧ hi (.gate g) = hi (wires 0)
      | ⟨.mul, wires⟩ =>
          lo (wires 0) < hi (wires 0) ∧ hi (wires 0) = lo (wires 1) ∧
          lo (wires 1) < hi (wires 1) ∧
          lo (.gate g) = lo (wires 0) ∧ hi (.gate g) = hi (wires 1)) ∧
    (∀ j : Fin N, lo (c.outputs j) = 0 ∧ hi (c.outputs j) = j.val + 1)

private def freeToList {α : Type*} (s : FreeSemigroup α) : List α :=
  s.head :: s.tail

private theorem freeToList_injective {α : Type*} :
    Function.Injective (freeToList (α := α)) := by
  intro s₁ s₂ h
  exact FreeSemigroup.ext (List.cons.inj h).1 (List.cons.inj h).2

private def freeFinWord {N : ℕ} (s : FreeSemigroup (Fin N)) : List ℕ :=
  (freeToList s).map Fin.val

private theorem freeFinWord_injective {N : ℕ} :
    Function.Injective (freeFinWord (N := N)) :=
  (List.map_injective_iff.mpr Fin.val_injective).comp freeToList_injective

private theorem freeFinWord_of {N : ℕ} (i : Fin N) :
    freeFinWord (FreeSemigroup.of i) = [i.val] := rfl

private theorem freeFinWord_mul {N : ℕ} (s₁ s₂ : FreeSemigroup (Fin N)) :
    freeFinWord (s₁ * s₂) = freeFinWord s₁ ++ freeFinWord s₂ := by
  simp only [freeFinWord, freeToList, FreeSemigroup.head_mul, FreeSemigroup.tail_mul,
    List.cons_append, List.map_cons, List.map_append]

private theorem freeFinWord_ne_nil {N : ℕ} (s : FreeSemigroup (Fin N)) :
    freeFinWord s ≠ [] := by
  simp only [freeFinWord, freeToList, List.map_cons, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem freeFinWord_prefixProd {N : ℕ} (j : Fin N) :
    freeFinWord (prefixProd (FreeSemigroup.of : Fin N → FreeSemigroup (Fin N)) j) =
      List.range' 0 (j.val + 1) := by
  rcases j with ⟨m, hm⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    have ihm : freeFinWord (prefixProd FreeSemigroup.of ⟨m, Nat.lt_of_succ_lt hm⟩) =
        List.range' 0 (m + 1) := ih (Nat.lt_of_succ_lt hm)
    change freeFinWord (prefixProd FreeSemigroup.of ⟨m, Nat.lt_of_succ_lt hm⟩ *
        FreeSemigroup.of ⟨m + 1, hm⟩) = List.range' 0 (m + 1 + 1)
    rw [freeFinWord_mul, ihm, freeFinWord_of, List.range'_1_concat (s := 0) (n := m + 1),
      Nat.zero_add]

private def programWord {N g : ℕ} (p : Program prefixSignature N g) (w : Wire N g) : List ℕ :=
  freeFinWord (p.trace (semigroupInterp (FreeSemigroup (Fin N))) FreeSemigroup.of w)

private theorem programWord_input {N g : ℕ} (p : Program prefixSignature N g) (i : Fin N) :
    programWord p (.input i) = [i.val] := rfl

private theorem programWord_ne_nil {N g : ℕ} (p : Program prefixSignature N g) (w : Wire N g) :
    programWord p w ≠ [] :=
  freeFinWord_ne_nil _

private theorem programWord_gate_id {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 1 → Wire N g) (h : p.lines k = ⟨.id, wires⟩) :
    programWord p (.gate k) = programWord p (wires 0) := by
  rw [programWord, p.trace_gate, h]
  rfl

private theorem programWord_gate_mul {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 2 → Wire N g) (h : p.lines k = ⟨.mul, wires⟩) :
    programWord p (.gate k) = programWord p (wires 0) ++ programWord p (wires 1) := by
  rw [programWord, p.trace_gate, h]
  exact freeFinWord_mul _ _

private theorem depths_eq_line_depth {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g) :
    p.depths k = (p.lines k).depth p.wireDepths := by
  induction p with
  | empty => exact k.elim0
  | @gate g' q line ih =>
    have hmap (l : Line prefixSignature N g') :
        (l.mapWires Wire.Renaming.castSucc).depth (q.gate line).wireDepths =
          l.depth q.wireDepths := by
      simp only [Line.depth, Line.mapWires_op, Line.mapWires_wires,
        Wire.Renaming.castSucc_apply, Program.wireDepths_gate_castSucc]
    refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [Program.depths_gate_last, Program.lines_gate_last, hmap]
    · rw [Program.depths_gate_castSucc, Program.lines_gate_castSucc, hmap, ih j]

private theorem wireDepths_gate_id {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 1 → Wire N g) (h : p.lines k = ⟨.id, wires⟩) :
    p.wireDepths (.gate k) = p.wireDepths (wires 0) + 1 := by
  rw [Program.wireDepths_gateWire, depths_eq_line_depth, h]
  simp only [Line.depth, prefixSignature, PrefixOp.arity, Fin.foldl_succ_last, Fin.foldl_zero,
    Nat.zero_max]
  rfl

private theorem wireDepths_gate_mul {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 2 → Wire N g) (h : p.lines k = ⟨.mul, wires⟩) :
    p.wireDepths (.gate k) = max (p.wireDepths (wires 0)) (p.wireDepths (wires 1)) + 1 := by
  rw [Program.wireDepths_gateWire, depths_eq_line_depth, h]
  simp only [Line.depth, prefixSignature, PrefixOp.arity, Fin.foldl_succ_last, Fin.foldl_zero,
    Nat.zero_max]
  rfl

private theorem rank_lt_of_lines_eq {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    {op : PrefixOp} {wires : Fin op.arity → Wire N g} (h : p.lines k = ⟨op, wires⟩)
    (a : Fin op.arity) : (wires a).rank < k.val + 1 := by
  cases hw : wires a with
  | input _ => exact Nat.zero_lt_succ _
  | gate j =>
    obtain ⟨s, hs⟩ : ∃ s, (p.lines k).wires s = .gate j := h ▸ ⟨a, hw⟩
    exact Nat.succ_lt_succ (p.lt_of_lines_wires_eq_gate k s j hs)

@[elab_as_elim]
private theorem prefix_wire_induction {N g : ℕ} (p : Program prefixSignature N g)
    {P : Wire N g → Prop}
    (input : ∀ i, P (.input i))
    (gate_id : ∀ k (wires : Fin 1 → Wire N g),
      p.lines k = ⟨.id, wires⟩ → P (wires 0) → P (.gate k))
    (gate_mul : ∀ k (wires : Fin 2 → Wire N g),
      p.lines k = ⟨.mul, wires⟩ → P (wires 0) → P (wires 1) → P (.gate k))
    (w : Wire N g) : P w := by
  have haux : ∀ r, ∀ w : Wire N g, w.rank = r → P w := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro w hr
      cases w with
      | input i => exact input i
      | gate k =>
        subst hr
        match hline : p.lines k with
        | ⟨.id, wires⟩ =>
          exact gate_id k wires hline
            (ih _ (rank_lt_of_lines_eq p k hline 0) (wires 0) rfl)
        | ⟨.mul, wires⟩ =>
          exact gate_mul k wires hline
            (ih _ (rank_lt_of_lines_eq p k hline 0) (wires 0) rfl)
            (ih _ (rank_lt_of_lines_eq p k hline 1) (wires 1) rfl)
  exact haux w.rank w rfl

/-- Every interval-labeled prefix circuit is a universal prefix circuit. -/
theorem IsIntervalPrefixCircuit.isUniversalPrefixCircuit {N : ℕ} {c : PrefixCircuit N}
    (hc : IsIntervalPrefixCircuit c) : IsUniversalPrefixCircuit c := by
  rcases hc with ⟨lo, hi, hin, hgate, hout⟩
  rw [isUniversalPrefixCircuit_iff_freeSemigroup]
  have hword : ∀ w : Wire N c.size,
      lo w < hi w ∧ programWord c.program w = List.range' (lo w) (hi w - lo w) := by
    intro w
    refine prefix_wire_induction c.program
      (fun i => ?_) (fun g wires hline ih0 => ?_) (fun g wires hline ih0 ih1 => ?_) w
    · obtain ⟨hlo, hhi⟩ := hin i
      rw [hlo, hhi, Nat.add_sub_cancel_left]
      exact ⟨Nat.lt_succ_self _, rfl⟩
    · obtain ⟨hglo, hghi⟩ := hline ▸ hgate g
      rwa [programWord_gate_id c.program g wires hline, hglo, hghi]
    · obtain ⟨h0, h01, h1, hglo, hghi⟩ := hline ▸ hgate g
      refine ⟨by omega, ?_⟩
      rw [programWord_gate_mul c.program g wires hline, ih0.2, ih1.2, hglo, hghi]
      have hsum : lo (wires 0) + (hi (wires 0) - lo (wires 0)) = lo (wires 1) := by omega
      rw [← hsum, List.range'_append_1]
      exact congrArg (List.range' (lo (wires 0))) (by omega)
  funext j
  apply freeFinWord_injective
  simpa [programWord, Circuit.eval, (hout j).1, (hout j).2, freeFinWord_prefixProd] using
    (hword (c.outputs j)).2

/-- Binary gate complexity of a prefix circuit: the total number of binary `mul` gates
([Sergeev2025PrefixDepth], p. 1). -/
@[expose] def binaryComplexity {N m : ℕ} (c : Circuit prefixSignature N m) : ℕ :=
  c.program.cost fun
    | .mul => 1
    | .id => 0

/-- Total fanout of wire `w` in `c`, counting both internal gate input slots reading `w` and
external output poles equal to `w` ([Sergeev2025PrefixDepth], pp. 1–3). -/
@[expose] def wireFanout {N m : ℕ} (c : Circuit prefixSignature N m) (w : Wire N c.size) : ℕ :=
  c.outDeg w + (Finset.univ.filter fun j : Fin m => c.outputs j = w).card

/-- A circuit has *fanout bounded by `k`* if every input and internal gate wire has total fanout
at most `k`. -/
@[expose] def FanoutAtMost {N m : ℕ} (c : Circuit prefixSignature N m) (k : ℕ) : Prop :=
  ∀ w : Wire N c.size, wireFanout c w ≤ k

instance instDecidableFanoutAtMost {N m : ℕ} (c : Circuit prefixSignature N m) (k : ℕ) :
    Decidable (FanoutAtMost c k) :=
  inferInstanceAs (Decidable (∀ _ : Wire N c.size, _))

/-- A universal prefix circuit on `N` inputs is *optimal* (has *zero deficiency*) if
`binaryComplexity c + c.depth = 2 * N - 2` ([Sergeev2025PrefixDepth], p. 1). -/
@[expose] def IsOptimalPrefixCircuit {N : ℕ} (c : PrefixCircuit N) : Prop :=
  IsUniversalPrefixCircuit c ∧ binaryComplexity c + c.depth = 2 * N - 2

/-! #### Internal DAG decomposition for Snir–Fich and zero-deficiency circuits -/

private theorem range_split_of_append {a len : ℕ} {L₁ L₂ : List ℕ}
    (h1 : L₁ ≠ []) (h2 : L₂ ≠ []) (happ : L₁ ++ L₂ = List.range' a len) :
    a < a + L₁.length ∧ a + L₁.length < a + len ∧
      L₁ = List.range' a L₁.length ∧ L₂ = List.range' (a + L₁.length) (len - L₁.length) := by
  have hlen : L₁.length + L₂.length = len := by
    have := congrArg List.length happ
    simpa only [List.length_append, List.length_range'] using this
  have hl1 : 0 < L₁.length := List.length_pos_iff.mpr h1
  have hl2 : 0 < L₂.length := List.length_pos_iff.mpr h2
  have hdecomp : List.range' a len =
      List.range' a L₁.length ++ List.range' (a + L₁.length) (len - L₁.length) := by
    rw [List.range'_append_1, show L₁.length + (len - L₁.length) = len by omega]
  rw [hdecomp] at happ
  obtain ⟨e1, e2⟩ := List.append_inj happ (by rw [List.length_range'])
  exact ⟨by omega, by omega, e1, e2⟩

private theorem card_mulGates_eq_cost {N g : ℕ} (p : Program prefixSignature N g) :
    (Finset.univ.filter fun k : Fin g => (p.lines k).op = .mul).card =
      p.cost (fun | .mul => 1 | .id => 0) := by
  induction p with
  | empty => rfl
  | @gate g' q line ih =>
    rw [Program.cost_gate, ← ih]
    have hbij : (Finset.univ.filter fun k : Fin (g' + 1) => ((q.gate line).lines k).op = .mul) =
        (Finset.univ.filter fun j : Fin g' => (q.lines j).op = .mul).map
          ⟨Fin.castSucc, Fin.castSucc_injective g'⟩ ∪
        (if line.op = .mul then {Fin.last g'} else ∅) := by
      ext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Program.lines_gate_last,
          Line.mapWires_op, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
          Fin.castSucc_ne_last, and_false, exists_false, false_or]
        split_ifs with h <;> simp only [h, Finset.mem_singleton, Finset.notMem_empty]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Program.lines_gate_castSucc,
          Line.mapWires_op, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
          Fin.castSucc_inj, exists_eq_right]
        split_ifs <;> simp only [Finset.mem_singleton, Fin.castSucc_ne_last, Finset.notMem_empty,
          or_false]
    rw [hbij, Finset.card_union_of_disjoint]
    · rw [Finset.card_map]
      cases line.op <;> simp only [reduceCtorEq, ↓reduceIte, Finset.card_singleton,
        Finset.card_empty]
    · split_ifs
      · simp [Finset.disjoint_singleton_right, Fin.castSucc_ne_last]
      · exact Finset.disjoint_empty_right _

private def ancMul {N g : ℕ} (p : Program prefixSignature N g) : Wire N g → Finset (Fin g)
  | .input _ => ∅
  | .gate k =>
      match _h : p.lines k with
      | ⟨.id, wires⟩ => ancMul p (wires 0)
      | ⟨.mul, wires⟩ => insert k (ancMul p (wires 0) ∪ ancMul p (wires 1))
termination_by w => w.rank
decreasing_by
  all_goals exact rank_lt_of_lines_eq p k _h _

private theorem ancMul_input {N g : ℕ} (p : Program prefixSignature N g) (i : Fin N) :
    ancMul p (.input i) = ∅ := by
  unfold ancMul
  rfl

private theorem ancMul_gate_id {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 1 → Wire N g) (h : p.lines k = ⟨.id, wires⟩) :
    ancMul p (.gate k) = ancMul p (wires 0) := by
  conv_lhs => unfold ancMul
  split <;> rename_i w' hw' <;> cases h.symm.trans hw'
  rfl

private theorem ancMul_gate_mul {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 2 → Wire N g) (h : p.lines k = ⟨.mul, wires⟩) :
    ancMul p (.gate k) = insert k (ancMul p (wires 0) ∪ ancMul p (wires 1)) := by
  conv_lhs => unfold ancMul
  split <;> rename_i w' hw' <;> cases h.symm.trans hw'
  rfl

private theorem ancMul_op_eq_mul_and_rank_le {N g : ℕ} (p : Program prefixSignature N g)
    (w : Wire N g) :
    ∀ j ∈ ancMul p w, (p.lines j).op = .mul ∧ j.val + 1 ≤ w.rank := by
  refine prefix_wire_induction p
    (fun i j hj => by rw [ancMul_input] at hj; exact absurd hj (Finset.notMem_empty j))
    (fun k wires hline ih0 j hj => ?_)
    (fun k wires hline ih0 ih1 j hj => ?_) w
  · rw [ancMul_gate_id p k wires hline] at hj
    exact ⟨(ih0 j hj).1, (ih0 j hj).2.trans (rank_lt_of_lines_eq p k hline 0).le⟩
  · rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
    rcases hj with rfl | hj0 | hj1
    · exact ⟨by rw [hline], le_rfl⟩
    · exact ⟨(ih0 j hj0).1, (ih0 j hj0).2.trans (rank_lt_of_lines_eq p k hline 0).le⟩
    · exact ⟨(ih1 j hj1).1, (ih1 j hj1).2.trans (rank_lt_of_lines_eq p k hline 1).le⟩

/-- A gate is not a multiplication ancestor of its own arguments. -/
private theorem notMem_ancMul_wires {N g : ℕ} (p : Program prefixSignature N g) {k : Fin g}
    {op : PrefixOp} {wires : Fin op.arity → Wire N g} (h : p.lines k = ⟨op, wires⟩)
    (a : Fin op.arity) : k ∉ ancMul p (wires a) := fun hk => by
  have := (ancMul_op_eq_mul_and_rank_le p _ k hk).2
  have := rank_lt_of_lines_eq p k h a
  omega

private theorem ancMul_range_and_card {N g : ℕ} (p : Program prefixSignature N g) :
    ∀ (w : Wire N g) (a len : ℕ), 1 ≤ len → programWord p w = List.range' a len →
      (∀ j ∈ ancMul p w, ∃ p₀ q₀, a ≤ p₀ ∧ p₀ < q₀ ∧ q₀ ≤ a + len ∧
        programWord p (.gate j) = List.range' p₀ (q₀ - p₀)) ∧
      (ancMul p w).card = len - 1 := by
  intro w
  refine prefix_wire_induction p
    (fun i a len _ hw => ?_)
    (fun k wires hline ih0 a len hlen hw => ?_)
    (fun k wires hline ih0 ih1 a len _ hw => ?_) w
  · rw [programWord_input] at hw
    obtain rfl : len = 1 := by simpa using (congrArg List.length hw).symm
    rw [ancMul_input]
    exact ⟨fun j hj => absurd hj (Finset.notMem_empty j), rfl⟩
  · rw [ancMul_gate_id p k wires hline]
    exact ih0 a len hlen (programWord_gate_id p k wires hline ▸ hw)
  · rw [programWord_gate_mul p k wires hline] at hw
    obtain ⟨hm1, hm2, hw0, hw1⟩ := range_split_of_append
      (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
    set len0 := (programWord p (wires 0)).length
    obtain ⟨hsub0, hcard0⟩ := ih0 a len0 (by omega) hw0
    obtain ⟨hsub1, hcard1⟩ := ih1 (a + len0) (len - len0) (by omega) hw1
    rw [ancMul_gate_mul p k wires hline]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [Finset.mem_insert, Finset.mem_union] at hj
      rcases hj with rfl | hj0 | hj1
      · refine ⟨a, a + len, le_rfl, by omega, le_rfl, ?_⟩
        rw [programWord_gate_mul p j wires hline, hw, Nat.add_sub_cancel_left]
      · obtain ⟨p₀, q₀, hp₀, hpq, hq₀, hjw⟩ := hsub0 j hj0
        exact ⟨p₀, q₀, hp₀, hpq, by omega, hjw⟩
      · obtain ⟨p₀, q₀, hp₀, hpq, hq₀, hjw⟩ := hsub1 j hj1
        exact ⟨p₀, q₀, by omega, hpq, by omega, hjw⟩
    · have hk_not : k ∉ ancMul p (wires 0) ∪ ancMul p (wires 1) :=
        Finset.notMem_union.mpr ⟨notMem_ancMul_wires p hline 0, notMem_ancMul_wires p hline 1⟩
      have hdisj : Disjoint (ancMul p (wires 0)) (ancMul p (wires 1)) := by
        rw [Finset.disjoint_left]
        intro j hj0 hj1
        obtain ⟨p₀, q₀, _, hpq₀, hq₀, hjw0⟩ := hsub0 j hj0
        obtain ⟨p₁, q₁, hp₁, hpq₁, _, hjw1⟩ := hsub1 j hj1
        have hmem0 : p₁ ∈ List.range' p₀ (q₀ - p₀) := by
          rw [← hjw0, hjw1, List.mem_range'_1]
          omega
        rw [List.mem_range'_1] at hmem0
        omega
      rw [Finset.card_insert_of_notMem hk_not, Finset.card_union_of_disjoint hdisj, hcard0,
        hcard1]
      omega

private def stripId {N g : ℕ} (p : Program prefixSignature N g) : Wire N g → Wire N g
  | .input i => .input i
  | .gate k =>
      match _h : p.lines k with
      | ⟨.id, wires⟩ => stripId p (wires 0)
      | ⟨.mul, _⟩ => .gate k
termination_by w => w.rank
decreasing_by
  exact rank_lt_of_lines_eq p k _h 0

private theorem stripId_spec {N g : ℕ} (p : Program prefixSignature N g) (w : Wire N g) :
    programWord p (stripId p w) = programWord p w ∧
      (stripId p w).rank ≤ w.rank ∧
      (∀ k, stripId p w = .gate k → (p.lines k).op = .mul) := by
  refine prefix_wire_induction p
    (fun i => by
      have : stripId p (.input i) = .input i := by unfold stripId; rfl
      rw [this]
      exact ⟨rfl, le_rfl, fun k hk => by cases hk⟩)
    (fun k wires hline ih0 => ?_)
    (fun k wires hline _ _ => ?_) w
  · have heq : stripId p (.gate k) = stripId p (wires 0) := by
      conv_lhs => unfold stripId
      split <;> rename_i w' hw' <;> cases hline.symm.trans hw'
      rfl
    obtain ⟨hw, hrk, hop⟩ := ih0
    have hlt := rank_lt_of_lines_eq p k hline 0
    rw [heq, programWord_gate_id p k wires hline]
    exact ⟨hw, by simp only [Wire.rank_gate]; omega, hop⟩
  · have heq : stripId p (.gate k) = .gate k := by
      conv_lhs => unfold stripId
      split <;> rename_i w' hw' <;> cases hline.symm.trans hw'
      rfl
    rw [heq]
    exact ⟨rfl, le_rfl, fun j hj => by cases hj; rw [hline]⟩

private def leftSpine {N g : ℕ} (p : Program prefixSignature N g) : Wire N g → List (Fin g)
  | .input _ => []
  | .gate k =>
      match _h : p.lines k with
      | ⟨.id, wires⟩ => leftSpine p (wires 0)
      | ⟨.mul, wires⟩ => leftSpine p (wires 0) ++ [k]
termination_by w => w.rank
decreasing_by
  all_goals exact rank_lt_of_lines_eq p k _h 0

private theorem leftSpine_input {N g : ℕ} (p : Program prefixSignature N g) (i : Fin N) :
    leftSpine p (.input i) = [] := by
  unfold leftSpine
  rfl

private theorem leftSpine_gate_id {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 1 → Wire N g) (h : p.lines k = ⟨.id, wires⟩) :
    leftSpine p (.gate k) = leftSpine p (wires 0) := by
  conv_lhs => unfold leftSpine
  split <;> rename_i w' hw' <;> cases h.symm.trans hw'
  rfl

private theorem leftSpine_gate_mul {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g)
    (wires : Fin 2 → Wire N g) (h : p.lines k = ⟨.mul, wires⟩) :
    leftSpine p (.gate k) = leftSpine p (wires 0) ++ [k] := by
  conv_lhs => unfold leftSpine
  split <;> rename_i w' hw' <;> cases h.symm.trans hw'
  rfl

private theorem leftSpine_subset_ancMul {N g : ℕ} (p : Program prefixSignature N g)
    (w : Wire N g) : ∀ j ∈ leftSpine p w, j ∈ ancMul p w := by
  refine prefix_wire_induction p
    (fun i j hj => by rw [leftSpine_input] at hj; cases hj)
    (fun k wires hline ih0 j hj => ?_)
    (fun k wires hline ih0 _ j hj => ?_) w
  · rw [leftSpine_gate_id p k wires hline] at hj
    simpa only [ancMul_gate_id p k wires hline] using ih0 j hj
  · rw [leftSpine_gate_mul p k wires hline, List.mem_append, List.mem_singleton] at hj
    rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union]
    exact hj.elim (Or.inr ∘ Or.inl ∘ ih0 j) Or.inl

private theorem leftSpine_length_le_wireDepths {N g : ℕ} (p : Program prefixSignature N g)
    (w : Wire N g) : (leftSpine p w).length ≤ p.wireDepths w := by
  refine prefix_wire_induction p
    (fun i => by rw [leftSpine_input]; exact Nat.zero_le _)
    (fun k wires hline ih0 => ?_)
    (fun k wires hline ih0 _ => ?_) w
  · rw [leftSpine_gate_id p k wires hline, wireDepths_gate_id p k wires hline]
    omega
  · rw [leftSpine_gate_mul p k wires hline, List.length_append, List.length_singleton,
      wireDepths_gate_mul p k wires hline]
    omega

private theorem zero_mem_ancMul_iff_mem_leftSpine {N g : ℕ} (p : Program prefixSignature N g) :
    ∀ (w : Wire N g) (len : ℕ), 1 ≤ len → programWord p w = List.range' 0 len →
      ∀ j ∈ ancMul p w, 0 ∈ programWord p (.gate j) ↔ j ∈ leftSpine p w := by
  intro w
  refine prefix_wire_induction p
    (fun i _ _ _ j hj => absurd (ancMul_input p i ▸ hj) (Finset.notMem_empty j))
    (fun k wires hline ih0 len hlen hw j hj => ?_)
    (fun k wires hline ih0 _ len _ hw j hj => ?_) w
  · rw [ancMul_gate_id p k wires hline] at hj
    rw [leftSpine_gate_id p k wires hline]
    exact ih0 len hlen (programWord_gate_id p k wires hline ▸ hw) j hj
  · rw [programWord_gate_mul p k wires hline] at hw
    obtain ⟨hm1, hm2, hw0, hw1⟩ := range_split_of_append
      (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
    rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
    rw [leftSpine_gate_mul p k wires hline, List.mem_append, List.mem_singleton]
    rcases hj with rfl | hj0 | hj1
    · refine ⟨fun _ => Or.inr rfl, fun _ => ?_⟩
      rw [programWord_gate_mul p j wires hline, hw, List.mem_range'_1]
      omega
    · have hjne : j ≠ k := fun h => notMem_ancMul_wires p hline 0 (h ▸ hj0)
      simp only [ih0 _ (by omega) hw0 j hj0, hjne, or_false]
    · obtain ⟨hsub1, _⟩ := ancMul_range_and_card p (wires 1) _ _ (by omega) hw1
      obtain ⟨p₁, q₁, hp₁, hpq₁, _, hjw1⟩ := hsub1 j hj1
      have hnot0 : 0 ∉ programWord p (.gate j) := by
        simp only [hjw1, List.mem_range'_1]; omega
      have hnot_spine : j ∉ leftSpine p (wires 0) := fun hmem =>
        hnot0 ((ih0 _ (by omega) hw0 j (leftSpine_subset_ancMul p (wires 0) j hmem)).mpr hmem)
      have hne : j ≠ k := by rintro rfl; exact notMem_ancMul_wires p hline 1 hj1
      simp only [hnot0, hnot_spine, hne, or_self]

private theorem universal_mul_sets {N : ℕ} (hN : 1 ≤ N) {c : PrefixCircuit N}
    (hc : IsUniversalPrefixCircuit c) :
    let wLast : Wire N c.size := c.outputs ⟨N - 1, by omega⟩
    let B : Finset (Fin c.size) := Finset.univ.filter fun g => (c.program.lines g).op = .mul
    let F : Finset (Fin c.size) := ancMul c.program wLast
    (∀ j : Fin N, programWord c.program (c.outputs j) = List.range' 0 (j.val + 1)) ∧
    programWord c.program wLast = List.range' 0 N ∧
    B.card = binaryComplexity c ∧
    F ⊆ B ∧ F.card = N - 1 ∧
    ∃ lastMul : Fin (N - 1) → Fin c.size,
      (∀ r : Fin (N - 1),
        stripId c.program (c.outputs ⟨r.val + 1, by omega⟩) = .gate (lastMul r) ∧
        (c.program.lines (lastMul r)).op = .mul ∧
        programWord c.program (.gate (lastMul r)) = List.range' 0 (r.val + 2)) ∧
      (Finset.univ.image lastMul) ⊆ B ∧
      (Finset.univ.image lastMul).card = N - 1 ∧
      F ∩ Finset.univ.image lastMul ⊆ (leftSpine c.program wLast).toFinset := by
  intro wLast B F
  have hfree := (isUniversalPrefixCircuit_iff_freeSemigroup c).mp hc
  have houtWord (j : Fin N) : programWord c.program (c.outputs j) = List.range' 0 (j.val + 1) := by
    change freeFinWord (c.eval (semigroupInterp (FreeSemigroup (Fin N))) FreeSemigroup.of j) = _
    rw [hfree, freeFinWord_prefixProd]
  have hB : B.card = binaryComplexity c := card_mulGates_eq_cost c.program
  have hwLast : programWord c.program wLast = List.range' 0 N := by
    simpa only [show N - 1 + 1 = N by omega] using houtWord ⟨N - 1, by omega⟩
  have hF_sub : F ⊆ B := fun g hg =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, (ancMul_op_eq_mul_and_rank_le c.program wLast g hg).1⟩
  have hF_card : F.card = N - 1 := (ancMul_range_and_card c.program wLast 0 N hN hwLast).2
  have hlastMul : ∀ r : Fin (N - 1),
      ∃ g : Fin c.size, stripId c.program (c.outputs ⟨r.val + 1, by omega⟩) = .gate g ∧
        (c.program.lines g).op = .mul ∧
        programWord c.program (.gate g) = List.range' 0 (r.val + 2) := by
    intro r
    obtain ⟨hword, _, hop⟩ := stripId_spec c.program (c.outputs ⟨r.val + 1, by omega⟩)
    rw [houtWord ⟨r.val + 1, by omega⟩] at hword
    cases hs : stripId c.program (c.outputs ⟨r.val + 1, by omega⟩) with
    | input i =>
      have := congrArg List.length (programWord_input c.program i ▸ hs ▸ hword)
      simp only [List.length_singleton, List.length_range'] at this
      omega
    | gate g =>
      exact ⟨g, rfl, hop g hs, hs ▸ hword⟩
  choose lastMul hlastStrip hlastOp hlastWord using hlastMul
  have hlastInj : Function.Injective lastMul := fun r₁ r₂ heq => by
    have hlen := congrArg List.length ((hlastWord r₁).symm.trans (heq ▸ hlastWord r₂))
    simp only [List.length_range'] at hlen
    exact Fin.ext (by omega)
  have hOut_sub : Finset.univ.image lastMul ⊆ B :=
    Finset.image_subset_iff.mpr fun r _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlastOp r⟩
  have hOut_card : (Finset.univ.image lastMul).card = N - 1 := by
    rw [Finset.card_image_of_injective _ hlastInj, Finset.card_univ, Fintype.card_fin]
  have hinter_sub : F ∩ Finset.univ.image lastMul ⊆ (leftSpine c.program wLast).toFinset := by
    intro g hg
    rcases Finset.mem_image.mp (Finset.mem_inter.mp hg).2 with ⟨r, _, rfl⟩
    refine List.mem_toFinset.mpr ((zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast
      _ (Finset.mem_inter.mp hg).1).mp ?_)
    simp only [hlastWord r, List.mem_range'_1]; omega
  exact ⟨houtWord, hwLast, hB, hF_sub, hF_card, lastMul,
    fun r => ⟨hlastStrip r, hlastOp r, hlastWord r⟩, hOut_sub, hOut_card, hinter_sub⟩

/-- **Snir–Fich trade-off** ([Sergeev2025PrefixDepth], p. 1, citing Fich 1983 and Snir 1986):
every universal prefix circuit on `N ≥ 1` inputs satisfies
`2 * N - 2 ≤ binaryComplexity c + c.depth`. -/
theorem two_mul_sub_two_le_binaryComplexity_add_depth {N : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hc : IsUniversalPrefixCircuit c) :
    2 * N - 2 ≤ binaryComplexity c + c.depth := by
  obtain ⟨_, _, hB, hF_sub, hF_card, lastMul, _, hOut_sub, hOut_card, hinter_sub⟩ :=
    universal_mul_sets hN hc
  let wLast : Wire N c.size := c.outputs ⟨N - 1, by omega⟩
  let OutMul : Finset (Fin c.size) := Finset.univ.image lastMul
  let F : Finset (Fin c.size) := ancMul c.program wLast
  have hinter_card : (F ∩ OutMul).card ≤ c.depth := by
    calc
      (F ∩ OutMul).card
        ≤ (leftSpine c.program wLast).toFinset.card := Finset.card_le_card hinter_sub
      _ ≤ (leftSpine c.program wLast).length := List.toFinset_card_le _
      _ ≤ c.program.wireDepths wLast := leftSpine_length_le_wireDepths c.program wLast
      _ ≤ c.depth := c.outputDepths_le_depth ⟨N - 1, by omega⟩
  have hunion_le := Finset.card_le_card (Finset.union_subset hF_sub hOut_sub)
  have hie := Finset.card_union_add_card_inter F OutMul
  dsimp only [wLast, F, OutMul] at *
  omega

end Cslib.Circuits.Prefix
