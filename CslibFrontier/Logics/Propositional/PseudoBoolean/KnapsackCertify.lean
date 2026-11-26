/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
-- `import all`: the acceptance proof unfolds `stepTop`, `runTop`, `State.improve` and `certify`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP

/-!
# The certified knapsack's proof is accepted

The proof that `Cslib.Logic.PL.VeriPB.Knapsack.certify` writes is accepted by the checker on
every instance (`Cslib.Logic.PL.VeriPB.Knapsack.checkRed_certify`), so its answer is always the
optimum (`Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_certify`), with no per-run check left.

The proof logs the selection of `Cslib.Algorithms.Lean.Knapsack.profitDP`, which fits
(`Cslib.Algorithms.Lean.Knapsack.sum_map_profitDP_le`), with `soli`; the shared state-graph
emitter of `CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP`, with dominance merging
and pruning, then runs from the state after the solution (`Cslib.Logic.PL.VeriPB.Knapsack.Inst.
forward_spec`). Every state of the last layer is reached by a selection that fits, so its profit
is at most that of `profitDP`'s selection (`Cslib.Algorithms.Lean.Knapsack.sum_map_le_profitDP`):
the forward half of its `P` plus the improving constraint refutes it, and the at-least-one
constraint of the last layer is refuted by RUP.

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.checkRed_certify`: the checker accepts every proof of the
  dynamic program.
* `Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_certify`: its answer is the optimum.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Knapsack

open PBConstr Inst

variable {n : ℕ}

/-! ### Reachable states -/

namespace Inst

variable (I : Inst)

/-- **The states of a layer are reached**: by an assignment allowed by the domains, and, with
pruning, within the capacity. -/
private theorem exists_of_mem_layM {m : Mode} : ∀ {i : ℕ} {st : St}, st ∈ I.layM m i →
    ∃ σ, I.stOf σ i = st ∧ (m.prune = true → st.1 ≤ I.C)
  | 0, st, h => by
    simp only [layM, List.mem_singleton] at h
    subst h
    exact ⟨fun _ => false, by simp [stOf, part], fun _ => Nat.zero_le _⟩
  | i + 1, st, h => by
    obtain ⟨st₀, h₀, b, -, hk, rfl⟩ := I.mem_nextL h
    obtain ⟨σ, hσ, -⟩ := exists_of_mem_layM h₀
    refine ⟨Function.update σ i b, ?_, fun hp => ?_⟩
    · rw [stOf_succ, Function.update_self]
      congr 1
      rw [← hσ]
      simp only [stOf]
      rw [part_congr (σ := Function.update σ i b) (τ := σ) (fun (j : ℕ) (hj : j < i) =>
          Function.update_of_ne (Nat.ne_of_lt hj) _ _),
        part_congr (σ := Function.update σ i b) (τ := σ) (fun (j : ℕ) (hj : j < i) =>
          Function.update_of_ne (Nat.ne_of_lt hj) _ _)]
    · simp only [keep, hp, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hk
      simpa [succSt] using hk

end Inst

/-! ### Sums over `Fin n` -/

private theorem map_finRange {α : Type*} (g : ℕ → α) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl

private theorem sum_filter_map {α : Type*} (l : List α) (q : α → Bool) (a : α → ℕ) :
    ((l.filter q).map a).sum = (l.map fun i => if q i then a i else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : q x <;> simp [h, ih]

/-- The weight of the items an assignment takes, as the dynamic program counts it. -/
private theorem part_ofFin (σ : ℕ → Bool) (a : Fin n → ℕ) :
    Inst.part σ (fun j => if h : j < n then a ⟨j, h⟩ else 0) true n =
      (((List.finRange n).filter fun i => σ i.val).map a).sum := by
  rw [sum_filter_map, Inst.part, ← map_finRange
    (fun j => Inst.bit (σ j) true (if h : j < n then a ⟨j, h⟩ else 0))]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  cases σ i.val <;> simp [Inst.bit]

/-! ### The logged solution -/

/-- A list of literals assigning `σ` to the variables below `m` solves the constraints over those
variables that `σ` satisfies. -/
private theorem solves_range {σ : ℕ → Bool} {m : ℕ} {cs : List PBConstr}
    (hc : ∀ c ∈ cs, c.Holds σ) (hv : ∀ c ∈ cs, ∀ v ∈ c.vars, v < m) :
    solves ((List.range m).map fun v => (v, σ v)) cs = true := by
  have hmem : ∀ v b, (v, b) ∈ (List.range m).map (fun v => (v, σ v)) ↔ v < m ∧ b = σ v := by
    intro v b
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨v', h, rfl, rfl⟩; exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩; exact ⟨v, h, rfl, rfl⟩
  have hcon : ∀ l, ((List.range m).map fun v => (v, σ v)).contains l =
      decide (l ∈ (List.range m).map fun v => (v, σ v)) := fun l =>
    Bool.eq_iff_iff.2 (by simp only [List.contains_iff_mem, decide_eq_true_eq])
  simp only [solves, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    hcon]
  refine ⟨fun l hl => ?_, fun c hc' => ?_⟩
  · obtain ⟨v, b⟩ := l
    have := (hmem v b).1 hl
    simp only [Std.Sat.Literal.negate, hmem, decide_eq_false_iff_not, not_and]
    intro _ h
    cases b <;> simp_all
  · have hf : (c.terms.filter fun t => decide (t.2 ∈ (List.range m).map fun v => (v, σ v))) =
        c.terms.filter fun t => Literal.eval σ t.2 := by
      refine List.filter_congr fun t ht => ?_
      obtain ⟨a, v, b⟩ := t
      have hvm : v < m := hv c hc' v (List.mem_map_of_mem (f := termVar) ht)
      simp only [hmem, hvm, true_and, Literal.eval_mk]
      cases b <;> cases σ v <;> simp
    rw [hf, ← lhs_eq_coeffSum_filter]
    exact hc c hc'

section

variable (w p : Fin n → ℕ) (B : ℕ)

/-- The selection of `profitDP`. -/
private def sel : List (Fin n) := Cslib.Algorithms.Lean.Knapsack.profitDP w p B (List.finRange n)

/-- The assignment of the selection. -/
private def σsel (v : ℕ) : Bool := if h : v < n then decide (⟨v, h⟩ ∈ sel w p B) else false

private theorem nodup_sel : (sel w p B).Nodup :=
  (Cslib.Algorithms.Lean.Knapsack.profitDP_sublist B _).nodup (List.nodup_finRange n)

private theorem rho_eq : ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B))) =
    (List.range n).map fun v => (v, σsel w p B v) := by
  rw [← map_finRange (fun v => (v, σsel w p B v))]
  refine List.map_congr_left fun i _ => ?_
  simp [σsel, i.isLt]

private theorem chosen_σsel : chosen n (σsel w p B) = (sel w p B).toFinset := by
  ext i; simp [σsel, i.isLt]

private theorem assignOf_rho :
    assignOf ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B))) = σsel w p B := by
  funext v
  rw [rho_eq]
  simp only [assignOf]
  rw [Bool.eq_iff_iff, List.contains_iff_mem]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  by_cases hv : v < n
  · cases h : σsel w p B v <;> simp [h, hv]
  · simp [σsel, hv]

private theorem eval_σsel : (objective p).eval (σsel w p B) = -((sel w p B).map p).sum := by
  rw [eval_objective, chosen_σsel, List.sum_toFinset _ (nodup_sel w p B)]
  simp only [Nat.cast_list_sum, List.map_map]
  rfl

end

/-! ### The constraint numbered `2` and the last layer -/

private theorem vars_fromLinear {L : List (ℕ × ℤ)} {D : ℤ} {x : ℕ}
    (h : x ∈ (fromLinear L D).vars) : x ∈ L.map Prod.fst := by
  simp only [PBConstr.vars, fromLinear, List.mem_map, List.mem_filterMap] at h
  obtain ⟨t, ⟨e, he, ht⟩, rfl⟩ := h
  refine List.mem_map.2 ⟨e, he, ?_⟩
  unfold entryTerm at ht
  split_ifs at ht <;> cases ht <;> rfl

private theorem nodup_fromLinear {L : List (ℕ × ℤ)} (hL : (L.map Prod.fst).Nodup) (D : ℤ) :
    ((fromLinear L D).terms.map termVar).Nodup := by
  simp only [fromLinear]
  refine List.Nodup.sublist ?_ hL
  clear hL
  induction L with
  | nil => simp
  | cons e L ih =>
    obtain ⟨v, a⟩ := e
    rw [List.filterMap_cons]
    rcases h : entryTerm (v, a) with _ | t
    · exact ih.cons _
    · have hv : termVar t = v := by
        unfold entryTerm at h; split_ifs at h <;> cases h <;> rfl
      simpa [hv] using ih.cons_cons v

section

variable (w p : Fin n → ℕ) (B : ℕ)

/-- The improving constraint of the logged solution. -/
private def impr : PBConstr := (objective p).improving (-((sel w p B).map p).sum)

private theorem impr_eq : impr w p B =
    fromLinear ((List.finRange n).map fun i => (i.val, (p i : ℤ)))
      (((sel w p B).map p).sum + 1) := by
  simp only [impr, Objective.improving, objective, List.map_map]
  congr 1
  · refine List.map_congr_left fun i _ => ?_; simp
  · ring

private theorem vars_impr {x : ℕ} (h : x ∈ (impr w p B).normalize.vars) : x < n := by
  have := vars_fromLinear (impr_eq w p B ▸ mem_vars_of_mem_vars_normalize h)
  simp only [List.map_map, List.mem_map, List.mem_finRange, true_and] at this
  obtain ⟨i, rfl⟩ := this
  exact i.isLt

/-- **The slack of the improving constraint**: `∑ pᵢ xᵢ - (k + 1)`. -/
private theorem slack_impr (σ : ℕ → Bool) :
    (lhs σ (impr w p B).normalize.terms : ℤ) - (impr w p B).normalize.degree =
      Inst.part σ (optInst w p B).p true n - (((sel w p B).map p).sum + 1) := by
  have hnd : ((impr w p B).terms.map termVar).Nodup := by
    rw [impr_eq]
    refine nodup_fromLinear ?_ _
    simpa [List.map_map, Function.comp_def] using List.nodup_finRange n |>.map Fin.val_injective
  rw [slack_normalize hnd, impr_eq, lhs_fromLinear]
  have hneg : negMass ((List.finRange n).map fun i => (i.val, (p i : ℤ))) = 0 := by
    simp only [negMass, List.map_map]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      simp
  have hlin : linVal σ ((List.finRange n).map fun i => (i.val, (p i : ℤ))) =
      Inst.part σ (optInst w p B).p true n := by
    rw [linVal, List.map_map, Inst.part, Nat.cast_list_sum, List.map_map, ← map_finRange
      (Nat.cast ∘ fun j => Inst.bit (σ j) true ((optInst w p B).p j))]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, optInst, Inst.ofFin, i.isLt, ↓reduceDIte, Fin.eta]
    cases σ i.val <;> simp [Inst.bit]
  simp only [fromLinear, hneg, hlin, Nat.cast_zero, add_zero]
  rw [Int.toNat_of_nonneg (by positivity)]

/-- **A state of the last layer has profit at most the optimum**, so the forward half of its `P`
and the improving constraint refute it. -/
private theorem refute_last {u : Node} (hu : u.st ∈ (optInst w p B).layM optMode n)
    (hP : n ≤ u.P) {σ : ℕ → Bool}
    (hA : ((impl [(u.P, true)] ((optInst w p B).cP n u.st)).normalize.add
      (impr w p B).normalize).Holds σ) (hσ : σ u.P = true) : False := by
  obtain ⟨τ, hτ, hfit⟩ := (optInst w p B).exists_of_mem_layM hu
  have h1 := slack_fwd (c := (optInst w p B).cP n u.st) (z := u.P)
    (fun h => by have := vars_sumTerms h; omega)
    (nodup_sumTerms _ _ _) σ
  have h2 := slack_impr w p B σ
  have h3 := Inst.part_add_part σ (optInst w p B).p false n
  have h4 := Inst.part_add_part τ (optInst w p B).p false n
  rw [holds_add_iff] at hA
  simp only [Inst.cP, dimC, lhs_sumTerms, hσ, ite_true] at h1 hA
  simp only [Bool.not_false] at h3 h4
  -- The selection of `τ` fits, so its profit is at most the optimum.
  have hw : (((List.finRange n).filter fun i => τ i.val).map w).sum ≤ B := by
    rw [← part_ofFin]; have := hfit rfl; simp only [← hτ, Inst.stOf] at this; exact this
  have hle := Cslib.Algorithms.Lean.Knapsack.sum_map_le_profitDP (w := w) (p := p)
    List.filter_sublist hw
  rw [← part_ofFin] at hle
  have hq : Inst.part τ (optInst w p B).p false n = u.st.2 := by rw [← hτ]; rfl
  have htot : Inst.tot (optInst w p B).p n = Inst.tot (optInst w p B).p (optInst w p B).n := rfl
  change Inst.part τ (fun j => if h : j < n then p ⟨j, h⟩ else 0) true n ≤ _ at hle
  simp only [optInst, Inst.ofFin] at h1 h2 h3 h4 hq hA hle ⊢
  change _ ≤ ((sel w p B).map p).sum at hle
  omega

end

/-! ### The additions of the last layer -/

namespace Inst

variable (I : Inst) {X : Ctx}

/-- **The additions of the last layer run**: for each node, its forward half of `P` plus the
constraint `2`, numbered from `e.next` on. -/
private theorem run_pols : ∀ (L : List Node) (e : Acc) (db : List (ℕ × PBConstr)),
    I.Run X e db → (∀ u ∈ L, lookup db u.pf = some (impl [(u.P, true)] (I.cP I.n u.st)).normalize) →
    ∃ db', I.Run X (e.push (L.map fun u => .step (.pol [.id u.pf, .id 2, .add])) L.length 0) db' ∧
      Sub db db' ∧ ∀ x ∈ L.zip ((List.range L.length).map (e.next + ·)),
        lookup db' x.2 = some ((impl [(x.1.P, true)] (I.cP I.n x.1.st)).normalize.add
          X.c₂.normalize)
  | [], e, db, h, _ => ⟨db, by simpa [Acc.push] using h, Sub.refl _, by simp⟩
  | u :: L, e, db, h, hL => by
    obtain ⟨h₁, s₁⟩ := Run.add I h (hL u List.mem_cons_self) h.2.2.2.2.2
    obtain ⟨db', h', s', hall⟩ := run_pols L _ _ h₁
      (fun v hv => s₁ _ _ (hL v (List.mem_cons_of_mem _ hv)))
    refine ⟨db', ?_, s₁.trans s', ?_⟩
    · rw [push_push] at h'
      simpa [Nat.add_comm] using h'
    · simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero,
        List.zip_cons_cons, List.mem_cons, List.map_map]
      rintro x (rfl | hx)
      · exact s' _ _ (lookup_cons_self _ _ _)
      · refine hall x ?_
        convert hx using 3
        funext j
        simp [Acc.push, Nat.add_assoc, Nat.add_comm 1]

end Inst

/-! ### The whole proof -/

section

variable (w p : Fin n → ℕ) (B : ℕ)

private theorem capacity_eq : capacity w B = (optInst w p B).capC := by
  have h1 : (List.finRange n).map (fun i => (w i, (i.val, false))) =
      (List.range n).map fun j => ((optInst w p B).w j, (j, false)) := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [optInst, Inst.ofFin]
  have h3 : (List.finRange n).map w = (List.range n).map (optInst w p B).w := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [optInst, Inst.ofFin]
  simp only [capacity, Inst.capC, Inst.tot, h1, h3]
  rfl

private theorem fixedLits_opt : (optInst w p B).fixedLits = [] := by
  simp [Inst.fixedLits, optInst, Inst.ofFin]

private theorem vars_capacity {x : ℕ} (h : x ∈ (capacity w B).normalize.vars) : x < n := by
  have := mem_vars_of_mem_vars_normalize h
  simp only [PBConstr.vars, capacity, List.map_map, List.mem_map, List.mem_finRange,
    true_and] at this
  obtain ⟨i, rfl⟩ := this
  exact i.isLt

/-- The state after the logged solution. -/
private def s₀ : State :=
  ((State.init (formula w B) (some (objective p)) none).log (formula w B) (some (objective p))
    ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B)))).improve (objective p)
    (-((sel w p B).map p).sum)

/-- Where the dynamic program of the optimization starts. -/
private def X₁ : Ctx := ⟨formula w B, some (objective p), s₀ w p B, impr w p B⟩

private theorem soli_step : stepTop (formula w B) (some (objective p))
    (State.init (formula w B) (some (objective p)) none)
    (.soli ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B)))) =
      some (s₀ w p B) := by
  have hfit : (capacity w B).Holds (σsel w p B) := by
    rw [holds_capacity_iff, chosen_σsel, List.sum_toFinset _ (nodup_sel w p B)]
    exact Cslib.Algorithms.Lean.Knapsack.sum_map_profitDP_le B _
  have hsol : solves ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B)))
      ((initDb (formula w B)).map (·.2)) = true := by
    rw [rho_eq]
    refine solves_range (m := n) (fun c hc => ?_) (fun c hc v hv => ?_) <;>
      simp only [initDb, formula, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
        List.map_nil, List.mem_singleton] at hc <;> subst hc
    · exact (holds_normalize _ _).2 hfit
    · exact vars_capacity w B hv
  have hasg : assigns ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B)))
      (objective p) = true := by
    rw [rho_eq]
    simp only [assigns, assignsAll, List.all_eq_true, Bool.or_eq_true]
    intro x hx
    simp only [objective, List.map_map, List.mem_map, List.mem_finRange, true_and,
      Function.comp_apply] at hx
    obtain ⟨i, rfl⟩ := hx
    have hmem : ((i.val, σsel w p B i.val) : Literal ℕ) ∈
        (List.range n).map fun v => (v, σsel w p B v) :=
      List.mem_map.2 ⟨i.val, List.mem_range.2 i.isLt, rfl⟩
    cases h : σsel w p B i.val <;> rw [h] at hmem <;> simp [hmem]
  have hev : (objective p).eval (assignOf
      ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B)))) =
      -((sel w p B).map p).sum := by
    rw [assignOf_rho, eval_σsel]
  simp only [stepTop, State.init, hsol, hasg, Bool.and_self, ↓reduceIte, hev]
  rfl

private theorem ctxOk_opt : (optInst w p B).CtxOk (X₁ w p B) where
  tcb := rfl
  order := rfl
  core := fun x hx v hv => by
    simp only [X₁, s₀, State.improve, State.addCore, State.log, State.init, initDb, formula,
      List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    simp only [optInst, Inst.ofFin]
    rcases hx with rfl | rfl
    · exact vars_impr w p B hv
    · exact vars_capacity w B hv
  avoid := fun v hv => by
    have : ∀ i : Fin n, i.val ≠ v := fun i h => by
      have := i.isLt; simp only [optInst, Inst.ofFin] at hv; omega
    simpa [State.avoidsVar, X₁, s₀, State.improve, State.addCore, State.log, State.init,
      objective, List.contains_iff_mem] using this

/-- **The final refutation**: the additions refute the `P` of every node of the last layer, its
`S` follows, and the at-least-one constraint is violated. -/
private theorem final_rup {db : List (ℕ × PBConstr)} {V : ℕ} {rn : LayerRec}
    (hrn : (optInst w p B).LayOk optMode n db V rn) {ks : List ℕ}
    (hlen : ks.length = rn.nodes.length)
    (hpols : ∀ x ∈ rn.nodes.zip ks, lookup db x.2 = some ((impl [(x.1.P, true)]
      ((optInst w p B).cP n x.1.st)).normalize.add (impr w p B).normalize)) :
    rup db ⟨[], 1⟩ (ks.map .id ++ rn.nodes.map (.id ·.sf) ++ [.id rn.alo]) = true := by
  refine rup_of_rupOk ?_
  rw [List.append_assoc]
  have e₁ : ks.map Hint.id = ((rn.nodes.zip ks).map fun x => (Hint.id x.2, (x.1.P, false))).map
      (·.1) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_snd_zip (l₁ := rn.nodes) (l₂ := ks) (by omega), List.map_map]
    rfl
  have e₂ : ((rn.nodes.zip ks).map fun x => (Hint.id x.2, (x.1.P, false))).map (·.2) =
      rn.nodes.map fun u => (u.P, false) := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_fst_zip (l₁ := rn.nodes) (l₂ := ks) (by omega), List.map_map]
    rfl
  rw [e₁]
  refine RupOk.imps (K₀ := []) _ _ (fun l hl => by simp at hl) ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hyn := (List.of_mem_zip hy).1
    refine ⟨_, hpols y hy, nodup_vars_normalize _, fun σ _ hc => ?_⟩
    simp only [Literal.eval_mk, beq_iff_eq]
    by_contra hP
    exact refute_last w p B (hrn.lay ▸ List.mem_map_of_mem hyn) (hrn.nodes y.1 hyn).nP hc
      (by simpa using hP)
  rw [e₂, List.append_nil]
  have e₃ : rn.nodes.map (Hint.id ·.sf) =
      (rn.nodes.map fun u => (Hint.id u.sf, (u.S, false))).map (·.1) := by simp
  rw [e₃]
  refine RupOk.imps (K₀ := rn.nodes.map fun u => (u.P, false)) _ _ (fun l hl => hl) ?_ ?_
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    refine ⟨_, (hrn.nodes u hu).sf, nodup_vars_normalize _, fun σ hσ hc => ?_⟩
    rw [holds_normalize, holds_impl] at hc
    have hP := lit_of hσ (v := u.P) (b := false) (List.mem_map_of_mem hu)
    cases hS : σ u.S
    · simp [hS]
    · have := ((holds_cS σ _ _).1 (hc (by simpa using hS))).2
      simp [hP] at this
  · refine RupOk.id_conflict hrn.alo (nodup_vars_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, Inst.aloClause, Inst.negD, fixedLits_opt, holds_clause] at hc
    obtain ⟨l, hl, hev⟩ := hc
    simp only [List.map_nil, List.nil_append, List.mem_map] at hl
    obtain ⟨u, hu, rfl⟩ := hl
    have := lit_of hσ (v := u.S) (b := false)
      (List.mem_append_left _ (List.mem_map.2 ⟨(Hint.id u.sf, (u.S, false)),
        List.mem_map.2 ⟨u, hu, rfl⟩, rfl⟩))
    simp [this] at hev

/-- **The checker accepts the proof of the certified knapsack**, on every instance. -/
theorem checkRed_certify :
    checkRed (formula w B) (some (objective p)) (certify w p B).proof = true := by
  set I := optInst w p B with hI
  have hn : I.n = n := rfl
  have h₀ : I.Run (X₁ w p B) ⟨[], 3, I.n⟩ (s₀ w p B).db := by
    refine I.run_start (X := X₁ w p B) rfl (fun x hx => ?_) (fun x hx v hv => ?_) ?_ ?_
    · simp only [X₁, s₀, State.improve, State.addCore, State.log, State.init, initDb, formula,
        List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    · simp only [X₁, s₀, State.improve, State.addCore, State.log, State.init, initDb, formula,
        List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact vars_impr w p B hv
      · exact vars_capacity w B hv
    · simp [X₁, s₀, State.improve, State.addCore, State.log, State.init, initDb, formula, lookup,
        capacity_eq w p B, hI]
    · simp [X₁, s₀, State.improve, State.addCore, State.log, State.init, initDb, formula, lookup,
        impr]
  obtain ⟨db₂, h₂, -, rn, rs, hf, hrn, -, -⟩ := I.forward_spec optMode (ctxOk_opt w p B) h₀
  obtain ⟨db₃, h₃, s₃, hpols⟩ := I.run_pols rn.nodes _ db₂ h₂ (fun u hu => (hrn.nodes u hu).pf)
  have hr := final_rup w p B (hrn.mono I s₃ le_rfl) (ks := (List.range rn.nodes.length).map
    ((I.forward optMode).1.next + ·)) (by simp) hpols
  obtain ⟨h₄, -⟩ := Run.rup I h₃ hr (fun v hv => by simp [PBConstr.vars] at hv)
  have hopt : optSteps I = ((((I.forward optMode).1.push
      (rn.nodes.map fun u => .step (.pol [.id u.pf, .id 2, .add])) rn.nodes.length 0).push
        [.step (.rup ⟨[], 1⟩
          (((List.range rn.nodes.length).map ((I.forward optMode).1.next + ·)).map .id ++
            rn.nodes.map (.id ·.sf) ++ [.id rn.alo]))] 1 0),
      ((I.forward optMode).1.push (rn.nodes.map fun u => .step (.pol [.id u.pf, .id 2, .add]))
        rn.nodes.length 0).next) := by
    simp only [optSteps, hf, List.headD_cons]
  have hev : (objective p).eval (assignOf
      ((List.finRange n).map fun i => (i.val, decide (i ∈ sel w p B)))) =
      -((sel w p B).map p).sum := by
    rw [assignOf_rho, eval_σsel]
  have hrun := h₄.1
  simp only [X₁] at hrun
  have hs := soli_step w p B
  simp only [sel] at hs
  simp only [certify, ← hI, hopt, checkRed, runTop_cons]
  erw [hs]
  rw [Option.bind_some]
  erw [hrun]
  simp only [sel] at hev
  have hnc : namesContra ((((I.forward optMode).1.push
      (List.map (fun u => TopStep.step (Step.pol [PolOp.id u.pf, PolOp.id 2, PolOp.add])) rn.nodes)
      rn.nodes.length 0).next, (⟨[], 1⟩ : PBConstr).normalize) :: db₃) ((I.forward optMode).1.push
      (List.map (fun u => TopStep.step (Step.pol [PolOp.id u.pf, PolOp.id 2, PolOp.add])) rn.nodes)
      rn.nodes.length 0).next = true := by
    simp only [namesContra, lookup_cons_self, Option.any_some]; decide
  simp only [Nat.cast_list_sum, List.map_map] at hev
  simp [checkConclusion, boundsOk, state, s₀, State.improve, State.addCore, State.log,
    State.init, lowerTo, objValue, hnc, sel, hev]

/-- **The answer of the certified knapsack is the optimum**: the largest profit of a set of items
that fits, on every instance. -/
theorem isGreatest_certify :
    IsGreatest ((fun S : Finset (Fin n) => ∑ i ∈ S, p i) '' {S | ∑ i ∈ S, w i ≤ B})
      (certify w p B).optimum :=
  isGreatest_of_checkRed_certify (checkRed_certify w p B)

end

end Cslib.Logic.PL.VeriPB.Knapsack

end
