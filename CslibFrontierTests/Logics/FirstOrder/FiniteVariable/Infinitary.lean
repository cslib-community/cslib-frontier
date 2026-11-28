/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Infinitary
public import Mathlib.ModelTheory.Order
import Mathlib.Tactic.FinCases

/-!
# Tests for Infinitary Finite-Variable Logics (`L^k_{∞ω}` and `C^k_{∞ω}`)

Covers:
1. Infinite graph reachability and connectivity (`walkFormula`, `reachableInfinitary`,
   `connectedInfinitary` in `L^3_{∞ω}`) on the infinite ray `(ℕ, natRay)` versus two disjoint
   infinite rays `ℕ ⊕ ℕ` (plus the `SimpleGraph Empty` `Preconnected` vs `Connected` boundary),
   witnessing `¬PebbleWinsForever` directly on infinite structures.
2. An explicit closed `L^2_{∞ω}` formula of **unbounded** quantifier depth (`infiniteAscChain`)
   over `Language.order` that holds on `(ℕ, ≤)` and fails on every finite linear order `(Fin n, ≤)`,
   plus verification that it has no finite quantifier-rank bound (`¬QuantifierRankLE n`).
3. `EVEN` cardinality (`evenCardInfinitary` in `C^1_{∞ω}`) evaluated positively on `Fin 2`,
   `Fin 4` and negatively on `Fin 1`, `Fin 3`, contrasted with non-definability in `L^k_{∞ω}` and
   `PebbleWinsForever` between `Fin (k + 1)` and `Fin (k + 2)`.
4. Embeddings (`GenFormula.toInfinitary`, `InfinitaryFormula.toCounting`), `k = 0` edge cases,
   and finite-model collapse instances (`L^k_{∞ω} ≡ FO^k`, `C^k_{∞ω} ≡ C^k`).
-/

public section

open FirstOrder Language Structure Cslib.Logic.FO Cslib.Logic.FO.FiniteVariable

namespace CslibFrontierTests.Logics.FirstOrder.FiniteVariable.Infinitary

/-! ### 1. Infinite graph reachability and connectivity in `L^3_{∞ω}` -/

/-- The infinite ray `0 - 1 - 2 - ⋯` on `ℕ`. -/
def natRay : SimpleGraph ℕ where
  Adj u v := u + 1 = v ∨ v + 1 = u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by omega⟩

/-- Two disjoint infinite rays on `ℕ ⊕ ℕ`. -/
def twoRays : SimpleGraph (ℕ ⊕ ℕ) where
  Adj x y :=
    match x, y with
    | .inl u, .inl v => natRay.Adj u v
    | .inr u, .inr v => natRay.Adj u v
    | .inl _, .inr _ => False
    | .inr _, .inl _ => False
  symm := ⟨fun x y h => by
    cases x <;> cases y
    · exact h.symm
    · exact False.elim h
    · exact False.elim h
    · exact h.symm⟩
  loopless := ⟨fun x => by cases x <;> exact natRay.loopless.irrefl _⟩

theorem natRay_reachable_zero : ∀ m : ℕ, natRay.Reachable 0 m
  | 0 => SimpleGraph.Reachable.refl 0
  | m + 1 => (natRay_reachable_zero m).trans (SimpleGraph.Adj.reachable (Or.inl rfl))

theorem natRay_connected : natRay.Connected :=
  ⟨fun u v => (natRay_reachable_zero u).symm.trans (natRay_reachable_zero v)⟩

theorem twoRays_not_reachable_inl_inr (u v : ℕ) : ¬twoRays.Reachable (.inl u) (.inr v) := by
  rintro ⟨w⟩
  have hleft : ∀ {x y : ℕ ⊕ ℕ}, twoRays.Walk x y → ∀ u', x = .inl u' → ∃ v', y = .inl v' := by
    intro x y p
    induction p with
    | nil => exact fun u' hx => ⟨u', hx⟩
    | @cons a b c hab rest ih =>
      intro u' ha
      subst ha
      cases b with
      | inl b' => exact ih b' rfl
      | inr _ => exact False.elim hab
  obtain ⟨_, hv'⟩ := hleft w u rfl
  cases hv'

theorem twoRays_not_connected : ¬twoRays.Connected := fun h =>
  twoRays_not_reachable_inl_inr 0 0 (h.preconnected (.inl 0) (.inr 0))

/-- Positive check: `connectedInfinitary` (`L^3_{∞ω}`) holds on the infinite ray `natRay`. -/
example :
    (letI := natRay.structure;
      (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).Realize
        (fun _ => (0 : ℕ))) :=
  (realize_connectedInfinitary_iff_connected natRay (fun _ => 0)).2 natRay_connected

/-- Negative control: `connectedInfinitary` fails on the disconnected infinite graph `twoRays`. -/
example :
    ¬(letI := twoRays.structure;
      (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).Realize
        (fun _ => (Sum.inl 0 : ℕ ⊕ ℕ))) :=
  mt (realize_connectedInfinitary_iff_connected twoRays (fun _ => Sum.inl 0)).1
    twoRays_not_connected

/-- Positive/negative reachability checks on `twoRays`: `.inl 0` reaches `.inl 4` (via a walk of
length `≤ 4`) and does not reach `.inr 0`. -/
example :
    (letI := twoRays.structure;
      (reachableInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).Realize
        (![Sum.inl 0, Sum.inl 4, Sum.inl 0] : Fin 3 → ℕ ⊕ ℕ)) := by
  rw [realize_reachableInfinitary]
  have hstep : ∀ m : ℕ, twoRays.Adj (Sum.inl m) (Sum.inl (m + 1)) := fun _ => Or.inl rfl
  exact (hstep 0).reachable.trans <| (hstep 1).reachable.trans <|
    (hstep 2).reachable.trans (hstep 3).reachable

example :
    ¬(letI := twoRays.structure;
      (reachableInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).Realize
        (![Sum.inl 0, Sum.inr 0, Sum.inl 0] : Fin 3 → ℕ ⊕ ℕ)) := by
  rw [realize_reachableInfinitary]
  exact twoRays_not_reachable_inl_inr 0 0

/-- Duplicator does not win the infinite `3`-pebble game between the infinite structures `natRay`
and `twoRays` from `∅`, directly exercising `pebbleWinsForever_iff_forall_infinitaryFormula` without
any `[Finite]` assumption. -/
example :
    ¬(letI := natRay.structure; letI := twoRays.structure;
      PebbleWinsForever Language.graph ∅ (fun _ : Fin 3 => (0 : ℕ))
        (fun _ : Fin 3 => (Sum.inl 0 : ℕ ⊕ ℕ))) := by
  let _ := natRay.structure
  let _ := twoRays.structure
  rw [pebbleWinsForever_iff_forall_infinitaryFormula]
  intro hall
  have hiff := hall connectedInfinitary (by rw [freeVars_connectedInfinitary])
  have htrue : (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).Realize
      (fun _ => (0 : ℕ)) :=
    (realize_connectedInfinitary_iff_connected natRay (fun _ => 0)).2 natRay_connected
  have hfalse : ¬(connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).Realize
      (fun _ => (Sum.inl 0 : ℕ ⊕ ℕ)) :=
    mt (realize_connectedInfinitary_iff_connected twoRays (fun _ => Sum.inl 0)).1
      twoRays_not_connected
  exact hfalse (hiff.1 htrue)

/-- Empty-graph control: `(⊥ : SimpleGraph Empty)` is vacuously `Preconnected` (matching
`realize_connectedInfinitary_iff_preconnected`), whereas `SimpleGraph.Connected` additionally
requires `Nonempty`. -/
example : (⊥ : SimpleGraph Empty).Preconnected ∧ ¬(⊥ : SimpleGraph Empty).Connected :=
  ⟨fun u => u.elim, fun h => h.nonempty.elim fun u => u.elim⟩

/-! ### 2. Unbounded-rank `L^2_{∞ω}` sentence separating `(ℕ, ≤)` from all `(Fin n, ≤)` -/

/-- Strict order `v_i < v_j` in `L^2_{∞ω}` over `Language.order`. -/
def ltAtom (i j : Fin 2) : InfinitaryFormula.{0, 0, 0} Language.order 2 :=
  (.rel leSymb ![i, j] : InfinitaryFormula.{0, 0, 0} Language.order 2) ⊓
    (.equal i j : InfinitaryFormula.{0, 0, 0} Language.order 2).not

/-- Two-pebble alternating formula asserting a strictly increasing chain of `d` steps starting
from pebble `i`, alternating between `i` and `1 - i`. -/
def ascFrom (i : Fin 2) : ℕ → InfinitaryFormula.{0, 0, 0} Language.order 2
  | 0 => ⊤
  | d + 1 => .ex (1 - i) (ltAtom i (1 - i) ⊓ ascFrom (1 - i) d)

/-- Closed `L^2_{∞ω}` sentence asserting an element with arbitrarily long finite ascending chains
above it, of **unbounded** quantifier depth (`¬QuantifierRankLE n` for all `n`). -/
def infiniteAscChain : InfinitaryFormula.{0, 0, 0} Language.order 2 :=
  .ex 0 (.iInf fun d : ℕ => ascFrom 0 d)

theorem freeVars_ascFrom (d : ℕ) (i : Fin 2) : (ascFrom i d).freeVars ⊆ ({i} : Set (Fin 2)) := by
  induction d generalizing i with
  | zero => simp only [ascFrom, InfinitaryGenFormula.freeVars_top, Set.empty_subset]
  | succ d _ =>
    simp only [ascFrom, InfinitaryGenFormula.freeVars_ex, InfinitaryGenFormula.freeVars_min,
      ltAtom, InfinitaryGenFormula.freeVars_not, InfinitaryGenFormula.freeVars_equal,
      InfinitaryGenFormula.freeVars_rel, Set.sdiff_subset_iff]
    intro x _
    fin_cases i <;> fin_cases x <;> simp

theorem freeVars_infiniteAscChain : infiniteAscChain.freeVars = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [infiniteAscChain, InfinitaryGenFormula.freeVars_ex,
    InfinitaryGenFormula.freeVars_iInf, Set.mem_sdiff, Set.mem_iUnion, Set.mem_singleton_iff] at hx
  obtain ⟨⟨d, hd⟩, hx0⟩ := hx
  exact hx0 (Set.mem_singleton_iff.1 (freeVars_ascFrom d 0 hd))

theorem not_quantifierRankLE_ascFrom (n : ℕ) (i : Fin 2) :
    ¬(ascFrom i (n + 1)).QuantifierRankLE n := by
  induction n generalizing i with
  | zero =>
    simp only [ascFrom, InfinitaryGenFormula.quantifierRankLE_ex_zero, not_false_eq_true]
  | succ n ih =>
    simp only [ascFrom, InfinitaryGenFormula.quantifierRankLE_ex_succ,
      InfinitaryGenFormula.quantifierRankLE_min]
    exact fun ⟨_, h⟩ => ih (1 - i) h

/-- `infiniteAscChain` genuinely has unbounded quantifier depth: no `n : ℕ` bounds its rank. -/
theorem not_quantifierRankLE_infiniteAscChain (n : ℕ) : ¬infiniteAscChain.QuantifierRankLE n := by
  cases n with
  | zero =>
    simp only [infiniteAscChain, InfinitaryGenFormula.quantifierRankLE_ex_zero, not_false_eq_true]
  | succ m =>
    simp only [infiniteAscChain, InfinitaryGenFormula.quantifierRankLE_ex_succ,
      InfinitaryGenFormula.quantifierRankLE_iInf]
    exact fun hall => not_quantifierRankLE_ascFrom m 0 (hall (m + 1))

theorem realize_ltAtom {M : Type*} [LinearOrder M] [Language.order.Structure M]
    [Language.order.OrderedStructure M] (i j : Fin 2) (a : Fin 2 → M) :
    (ltAtom i j).Realize a ↔ a i < a j := by
  simp only [ltAtom, InfinitaryGenFormula.realize_min, InfinitaryGenFormula.realize_rel,
    InfinitaryGenFormula.realize_not, InfinitaryGenFormula.realize_equal]
  have hle : RelMap (leSymb : Language.order.Relations 2) (a ∘ ![i, j]) ↔ a i ≤ a j :=
    (relMap_leSymb (L := Language.order) _).trans ⟨fun h => h, fun h => h⟩
  rw [hle, lt_iff_le_and_ne]

theorem realize_ascFrom_nat (d : ℕ) (i : Fin 2) (a : Fin 2 → ℕ) :
    letI : Language.order.Structure ℕ := orderStructure ℕ
    (ascFrom i d).Realize a := by
  let _ : Language.order.Structure ℕ := orderStructure ℕ
  have _ : Language.order.OrderedStructure ℕ := ⟨fun _ => Iff.rfl⟩
  induction d generalizing i a with
  | zero => simp only [ascFrom, InfinitaryGenFormula.realize_top]
  | succ d ih =>
    simp only [ascFrom, InfinitaryGenFormula.realize_ex, InfinitaryGenFormula.realize_min]
    refine ⟨a i + 1, ?_, ih (1 - i) _⟩
    rw [realize_ltAtom]
    have hne : i ≠ 1 - i := by fin_cases i <;> decide
    simp only [Function.update_self, Function.update_of_ne hne]
    omega

theorem bound_of_realize_ascFrom {n : ℕ} (d : ℕ) (i : Fin 2) (a : Fin 2 → Fin n) :
    (letI : Language.order.Structure (Fin n) := orderStructure (Fin n);
      (ascFrom i d).Realize a) → (a i).val + d < n := by
  let _ : Language.order.Structure (Fin n) := orderStructure (Fin n)
  have _ : Language.order.OrderedStructure (Fin n) := ⟨fun _ => Iff.rfl⟩
  induction d generalizing i a with
  | zero => exact fun _ => (a i).isLt
  | succ d ih =>
    simp only [ascFrom, InfinitaryGenFormula.realize_ex, InfinitaryGenFormula.realize_min]
    rintro ⟨c, hlt, hd⟩
    rw [realize_ltAtom] at hlt
    have hne : i ≠ 1 - i := by fin_cases i <;> decide
    simp only [Function.update_self, Function.update_of_ne hne] at hlt
    have hrec := ih (1 - i) (Function.update a (1 - i) c) hd
    simp only [Function.update_self] at hrec
    have hlt_val : (a i).val < c.val := hlt
    omega

/-- `infiniteAscChain` holds on `(ℕ, ≤)`. -/
example :
    (letI : Language.order.Structure ℕ := orderStructure ℕ;
      infiniteAscChain.Realize (fun _ => (0 : ℕ))) := by
  let _ : Language.order.Structure ℕ := orderStructure ℕ
  simp only [infiniteAscChain, InfinitaryGenFormula.realize_ex, InfinitaryGenFormula.realize_iInf]
  exact ⟨0, fun d => realize_ascFrom_nat d 0 _⟩

/-- `infiniteAscChain` fails on every finite linear order `(Fin n, ≤)`. -/
example (n : ℕ) (a : Fin 2 → Fin n) :
    ¬(letI : Language.order.Structure (Fin n) := orderStructure (Fin n);
      infiniteAscChain.Realize a) := by
  let _ : Language.order.Structure (Fin n) := orderStructure (Fin n)
  simp only [infiniteAscChain, InfinitaryGenFormula.realize_ex, InfinitaryGenFormula.realize_iInf]
  rintro ⟨c, hall⟩
  have h := bound_of_realize_ascFrom n 0 (Function.update a 0 c) (hall n)
  omega

/-! ### 3. `EVEN` cardinality in `C^1_{∞ω}` vs non-definability in `L^k_{∞ω}` -/

example :
    (letI : Language.empty.Structure (Fin 2) := Language.emptyStructure;
      (evenCardInfinitary Language.empty : InfinitaryCountingFormula.{0, 0, 0} Language.empty 1)
        |>.Realize (fun _ => (0 : Fin 2))) := by
  let _ : Language.empty.Structure (Fin 2) := Language.emptyStructure
  rw [realize_evenCardInfinitary, Nat.card_fin]
  exact ⟨1, rfl⟩

example :
    (letI : Language.empty.Structure (Fin 4) := Language.emptyStructure;
      (evenCardInfinitary Language.empty : InfinitaryCountingFormula.{0, 0, 0} Language.empty 1)
        |>.Realize (fun _ => (0 : Fin 4))) := by
  let _ : Language.empty.Structure (Fin 4) := Language.emptyStructure
  rw [realize_evenCardInfinitary, Nat.card_fin]
  exact ⟨2, rfl⟩

example :
    ¬(letI : Language.empty.Structure (Fin 3) := Language.emptyStructure;
      (evenCardInfinitary Language.empty : InfinitaryCountingFormula.{0, 0, 0} Language.empty 1)
        |>.Realize (fun _ => (0 : Fin 3))) := by
  let _ : Language.empty.Structure (Fin 3) := Language.emptyStructure
  rw [realize_evenCardInfinitary, Nat.card_fin]
  decide

example :
    ¬(letI : Language.empty.Structure (Fin 1) := Language.emptyStructure;
      (evenCardInfinitary Language.empty : InfinitaryCountingFormula.{0, 0, 0} Language.empty 1)
        |>.Realize (fun _ => (0 : Fin 1))) := by
  let _ : Language.empty.Structure (Fin 1) := Language.emptyStructure
  rw [realize_evenCardInfinitary, Nat.card_fin]
  decide

/-- Non-definability of `EVEN` in `L^k_{∞ω}` at `k = 0` and `k = 3`, and `PebbleWinsForever`
between `Fin 4` and `Fin 5` for `3` pebbles. -/
example :
    ¬∃ φ : InfinitaryFormula.{0, 0, 0} Language.empty 0, φ.freeVars = ∅ ∧
      ∀ (n : ℕ) (a : Fin 0 → Fin (n + 1)),
        (letI : Language.empty.Structure (Fin (n + 1)) := Language.emptyStructure;
          φ.Realize a) ↔ Even (n + 1) :=
  not_exists_infinitaryFormula_even_card 0

example :
    ¬∃ φ : InfinitaryFormula.{0, 0, 0} Language.empty 3, φ.freeVars = ∅ ∧
      ∀ (n : ℕ) (a : Fin 3 → Fin (n + 1)),
        (letI : Language.empty.Structure (Fin (n + 1)) := Language.emptyStructure;
          φ.Realize a) ↔ Even (n + 1) :=
  not_exists_infinitaryFormula_even_card 3

example :
    (letI : Language.empty.Structure (Fin 4) := Language.emptyStructure;
      letI : Language.empty.Structure (Fin 5) := Language.emptyStructure;
      PebbleWinsForever Language.empty ∅ (fun _ : Fin 3 => (0 : Fin 4))
        (fun _ : Fin 3 => (0 : Fin 5))) :=
  pebbleWinsForever_fin_succ 3 _ _

/-! ### 4. Embeddings, `k = 0` edge cases, and finite-model collapse -/

/-- At `k = 0`, every `InfinitaryFormula` has empty `freeVars`. -/
example (φ : InfinitaryFormula.{0, 0, 0} Language.graph 0) : φ.freeVars = ∅ :=
  Set.eq_empty_of_isEmpty _

/-- Embedding `GenFormula.toInfinitary` composes with `InfinitaryFormula.toCounting` and preserves
realization and quantifier rank (and likewise for `CountingFormula`). -/
example (G : SimpleGraph (Fin 4)) (φ : FiniteVariable.Formula Language.graph 2)
    (ψ : FiniteVariable.CountingFormula Language.graph 2) (a : Fin 2 → Fin 4) :
    (letI := G.structure;
      ((show InfinitaryFormula.{0, 0, 0} Language.graph 2 from φ.toInfinitary).toCounting.Realize
          a ↔ φ.Realize a)) ∧
      ((show InfinitaryFormula.{0, 0, 0} Language.graph 2 from
          φ.toInfinitary).toCounting.QuantifierRankLE φ.quantifierRank) ∧
      (letI := G.structure;
        ((ψ.toInfinitary : InfinitaryCountingFormula.{0, 0, 0} Language.graph 2).Realize a ↔
          ψ.Realize a)) := by
  let _ := G.structure
  refine ⟨by rw [InfinitaryFormula.realize_toCounting, GenFormula.realize_toInfinitary], ?_,
    GenFormula.realize_toInfinitary ψ a⟩
  rw [InfinitaryFormula.quantifierRankLE_toCounting]
  exact (GenFormula.quantifierRankLE_toInfinitary φ φ.quantifierRank).2 le_rfl

/-- Finite-model collapse (`L^k_{∞ω} ≡ FO^k` and `C^k_{∞ω} ≡ C^k`) instantiated on finite graphs:
two finite graphs agree on all `C^2_{∞ω}` sentences iff they agree on finitary `C^2`. -/
example (G H : SimpleGraph (Fin 6)) (a b : Fin 2 → Fin 6) :
    (letI := G.structure; letI := H.structure;
      (∀ φ : InfinitaryCountingFormula.{0, 0, 0} Language.graph 2, φ.freeVars ⊆ ∅ →
        (φ.Realize a ↔ φ.Realize b)) ↔
      (∀ φ : CountingFormula Language.graph 2, ↑φ.freeVars ⊆ (∅ : Set (Fin 2)) →
        (φ.Realize a ↔ φ.Realize b))) := by
  let _ := G.structure
  let _ := H.structure
  exact forall_realize_infinitaryCountingFormula_iff_forall_realize

end CslibFrontierTests.Logics.FirstOrder.FiniteVariable.Infinitary
