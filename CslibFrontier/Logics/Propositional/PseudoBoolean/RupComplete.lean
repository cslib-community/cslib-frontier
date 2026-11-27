/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
import CslibFrontier.Logics.Propositional.PseudoBoolean.CuttingPlanes
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast

/-!
# Unit propagation is complete on constraints over distinct variables

A trail `ρ` of literals is *consistent* when it holds no literal together with its negation
(`Cslib.Logic.PL.VeriPB.TrailConsistent`). For a constraint `C` whose terms are on distinct
variables, as every normalized constraint's are
(`Cslib.Logic.PL.PBConstr.nodup_termVar_normalize`), unit propagation on a consistent trail
decides the two questions a proof by reverse unit propagation asks of `C`:

* it reports a conflict exactly when no assignment extending `ρ` satisfies `C`
  (`Cslib.Logic.PL.VeriPB.propagate_eq_none_of_forall`), because some assignment extending `ρ`
  makes every term not falsified by `ρ` true;
* otherwise it puts on the trail every literal `ℓ` that `C` implies under `ρ`
  (`Cslib.Logic.PL.VeriPB.mem_of_propagate`): if `ℓ` is not on the trail, the assignment making
  `ℓ` false and every other unfalsified term true violates `C`, so a term of `C` carries `ℓ`, and
  its coefficient exceeds the slack.

The trail stays consistent (`Cslib.Logic.PL.VeriPB.trailConsistent_of_propagate`). So a `rup` step
succeeds when, along its hints, each constraint is either violated by every assignment satisfying
the literals derived so far, or implies new literals (`Cslib.Logic.PL.VeriPB.RupOk`): acceptance
of a `rup` step reduces to implications between constraints, checked on assignments, with no
reasoning about the propagation's term lists. The proof logging of
`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackPropagator` proves its `rup` steps
accepted this way.

Cutting-planes addition is described the same way: the sum of two constraints holds at `σ`
exactly when their slacks at `σ` add up to a nonnegative number
(`Cslib.Logic.PL.VeriPB.holds_add_iff`), and normalizing a constraint over distinct variables keeps
its slack at every assignment (`Cslib.Logic.PL.VeriPB.slack_normalize`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.TrailConsistent`: a trail without complementary literals.
* `Cslib.Logic.PL.VeriPB.RupOk`: every consistent trail containing the given literals leads the
  hints to a conflict.
* `Cslib.Logic.PL.VeriPB.Forces`: a constraint forces a literal on a trail.

## Main results

* `Cslib.Logic.PL.VeriPB.propagate_eq_none_of_forall`, `Cslib.Logic.PL.VeriPB.mem_of_propagate`:
  unit propagation is complete for conflicts and for implied literals.
* `Cslib.Logic.PL.VeriPB.RupOk.conflict`, `Cslib.Logic.PL.VeriPB.RupOk.imp`,
  `Cslib.Logic.PL.VeriPB.RupOk.imps`, `Cslib.Logic.PL.VeriPB.rup_of_rupOk`: a `rup` step is
  accepted when its hints are justified by implications.
* `Cslib.Logic.PL.VeriPB.slack_normalize`, `Cslib.Logic.PL.VeriPB.holds_add_iff`: the slack of a
  normalized constraint and of a sum.
* `Cslib.Logic.PL.VeriPB.Forces.propagate`, `Cslib.Logic.PL.VeriPB.rupHints_of_forces`: a literal
  that a constraint forces on a trail is propagated from every larger trail, so a chain of forced
  literals ending in a constraint of negative slack is a run of hints that reaches a conflict.
  Unlike `Cslib.Logic.PL.VeriPB.RupOk`, this needs no distinct variables: it is stated with the
  slack, which only falls as the trail grows (`Cslib.Logic.PL.VeriPB.slack_anti`).
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB

open PBConstr

/-- A trail is *consistent* when it holds no literal together with its negation. -/
def TrailConsistent (ρ : List (Literal ℕ)) : Prop :=
  ∀ l ∈ ρ, Std.Sat.Literal.negate l ∉ ρ

/-- A literal whose negation is not on a consistent trail extends it consistently. -/
theorem TrailConsistent.cons {t : List (Literal ℕ)} (ht : TrailConsistent t) {l : Literal ℕ}
    (hl : Std.Sat.Literal.negate l ∉ t) : TrailConsistent (l :: t) := by
  intro m hm hnm
  simp only [List.mem_cons] at hm hnm
  rcases hm with rfl | hm
  · rcases hnm with h | h
    · exact absurd h (by cases m; simp [Std.Sat.Literal.negate])
    · exact hl h
  · rcases hnm with h | h
    · exact hl (h ▸ by simpa using hm)
    · exact ht m hm h

private theorem negate_ne_self (l : Literal ℕ) : Std.Sat.Literal.negate l ≠ l := by
  obtain ⟨v, b⟩ := l; cases b <;> simp [Std.Sat.Literal.negate]

private theorem negate_inj {l m : Literal ℕ}
    (h : Std.Sat.Literal.negate l = Std.Sat.Literal.negate m) : l = m := by
  rw [← negate_negate l, h, negate_negate]

/-- Two terms on the same variable of a list of terms on distinct variables are equal. -/
private theorem eq_of_termVar_eq {ts : List (ℕ × Literal ℕ)} (hd : (ts.map termVar).Nodup)
    {t t' : ℕ × Literal ℕ} (ht : t ∈ ts) (ht' : t' ∈ ts) (h : termVar t = termVar t') : t = t' :=
  List.inj_on_of_nodup_map hd ht ht' h

/-- **The best assignment of a trail**: on a consistent trail, some assignment extending the trail
makes every term not falsified by the trail true. -/
theorem exists_lhs_eq {ts : List (ℕ × Literal ℕ)} (hd : (ts.map termVar).Nodup)
    {ρ : List (Literal ℕ)} (hρ : TrailConsistent ρ) :
    ∃ σ, Consistent σ ρ ∧ lhs σ ts = coeffSum (ts.filter fun t => !falsified ρ t) := by
  let σ : ℕ → Bool := fun v =>
    if (v, true) ∈ ρ then true else if (v, false) ∈ ρ then false
    else ((ts.find? fun t => termVar t == v).map termPos).getD false
  have hcons : Consistent σ ρ := by
    rintro ⟨v, b⟩ hl
    cases b
    · have : (v, true) ∉ ρ := hρ _ hl
      simp [σ, this, hl]
    · simp [σ, hl]
  refine ⟨σ, hcons, ?_⟩
  rw [lhs_eq_coeffSum_filter]
  congr 1
  refine List.filter_congr fun t ht => ?_
  obtain ⟨a, v, b⟩ := t
  have hf : falsified ρ (a, v, b) = decide ((v, !b) ∈ ρ) := by
    simp [falsified, Std.Sat.Literal.negate]
  rw [hf]
  by_cases hn : (v, !b) ∈ ρ
  · have := hcons _ hn
    simp only [Literal.eval_eq_true_iff] at this
    simp [hn, Literal.eval, this]
  · simp only [hn, decide_false, Bool.not_false]
    by_cases hp : (v, b) ∈ ρ
    · have := hcons _ hp
      simpa using this
    · have hfind : ∃ t', ts.find? (fun t => termVar t == v) = some t' := by
        rcases h : ts.find? (fun t => termVar t == v) with _ | t'
        · exact absurd (List.find?_eq_none.1 h _ ht) (by simp)
        · exact ⟨t', rfl⟩
      obtain ⟨t', ht'⟩ := hfind
      have hv' : termVar t' = v := by simpa using List.find?_some ht'
      have heq := eq_of_termVar_eq hd ht (List.mem_of_find?_eq_some ht') hv'.symm
      subst heq
      cases b <;> simp_all [σ, Literal.eval]

/-- **Conflicts are found**: if no assignment extending a consistent trail satisfies a constraint
over distinct variables, propagation reports a conflict. -/
theorem propagate_eq_none_of_forall {c : PBConstr} (hd : (c.terms.map termVar).Nodup)
    {ρ : List (Literal ℕ)} (hρ : TrailConsistent ρ) (h : ∀ σ, Consistent σ ρ → ¬ c.Holds σ) :
    propagate ρ c = none := by
  obtain ⟨σ, hσ, hl⟩ := exists_lhs_eq hd hρ
  have := h σ hσ
  unfold Holds at this
  have hs : slack ρ c < 0 := by unfold slack; omega
  simp [propagate, hs]

/-- **Implied literals are propagated**: if propagation of a constraint over distinct variables on
a consistent trail finds no conflict, every literal that the constraint implies under the trail is
on the new trail. -/
theorem mem_of_propagate {c : PBConstr} (hd : (c.terms.map termVar).Nodup) {ρ ρ' : List (Literal ℕ)}
    (hρ : TrailConsistent ρ) (hp : propagate ρ c = some ρ') {l : Literal ℕ}
    (hl : ∀ σ, Consistent σ ρ → c.Holds σ → Literal.eval σ l = true) : l ∈ ρ' := by
  have hsub : ∀ m ∈ ρ, m ∈ ρ' := by
    unfold propagate at hp
    split at hp
    · cases hp
    · cases hp; exact fun m hm => List.mem_append_right _ hm
  by_cases hin : l ∈ ρ
  · exact hsub l hin
  have hnn : Std.Sat.Literal.negate l ∉ ρ := by
    intro hn
    have := propagate_eq_none_of_forall hd hρ fun σ hσ hc => by
      have h1 := hl σ hσ hc
      have h2 := hσ _ hn
      simp [Literal.eval_negate, h1] at h2
    simp [this] at hp
  obtain ⟨σ, hσ, hlhs⟩ := exists_lhs_eq hd
    (hρ.cons (l := Std.Sat.Literal.negate l) (by rwa [negate_negate]))
  have hσρ : Consistent σ ρ := fun m hm => hσ m (List.mem_cons_of_mem _ hm)
  have hlf : Literal.eval σ l = false := by
    have := hσ _ List.mem_cons_self
    simpa [Literal.eval_negate] using this
  have hnc : ¬ c.Holds σ := fun hc => by simp [hl σ hσρ hc] at hlf
  unfold Holds at hnc
  -- Split the unfalsified terms by whether their literal is `l`.
  have hsplit := coeffSum_filter_add c.terms (fun t => !falsified ρ t) (fun t => t.2 == l)
  have hrest : (c.terms.filter fun t => !falsified ρ t && !(t.2 == l)) =
      c.terms.filter fun t => !falsified (Std.Sat.Literal.negate l :: ρ) t := by
    refine List.filter_congr fun t _ => ?_
    simp only [falsified, List.contains_cons, Bool.not_or]
    by_cases h : t.2 = l
    · simp [h]
    · have : (Std.Sat.Literal.negate t.2 == Std.Sat.Literal.negate l) = false := by
        simpa using fun he => h (negate_inj he)
      simp [h, this, Bool.and_comm]
  rw [hrest, ← hlhs] at hsplit
  have hslack : 0 ≤ slack ρ c := by
    unfold propagate at hp
    split at hp
    · cases hp
    · omega
  -- Some unfalsified term carries `l`.
  obtain ⟨t, ht⟩ : ∃ t, t ∈ c.terms.filter fun t => !falsified ρ t && (t.2 == l) := by
    by_contra hne
    push Not at hne
    have : (c.terms.filter fun t => !falsified ρ t && (t.2 == l)) = [] :=
      List.eq_nil_iff_forall_not_mem.2 hne
    rw [this, coeffSum_nil, Nat.zero_add] at hsplit
    unfold slack at hslack
    omega
  obtain ⟨htm, htp⟩ := List.mem_filter.1 ht
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at htp
  obtain ⟨hft, htl⟩ := htp
  -- It is the only one, the variables being distinct.
  have hone : (c.terms.filter fun t => !falsified ρ t && (t.2 == l)) = [t] := by
    have hall : ∀ t' ∈ c.terms.filter (fun t => !falsified ρ t && (t.2 == l)), t' = t := by
      intro t' ht'
      obtain ⟨ht'm, ht'p⟩ := List.mem_filter.1 ht'
      simp only [Bool.and_eq_true, beq_iff_eq] at ht'p
      refine eq_of_termVar_eq hd ht'm htm ?_
      obtain ⟨a, v, b⟩ := t; obtain ⟨a', v', b'⟩ := t'
      simp only at htl ht'p
      simp [← htl, ht'p.2] at *
    have hnd : (c.terms.filter fun t => !falsified ρ t && (t.2 == l)).Nodup :=
      (List.Nodup.of_map _ hd).filter _
    rcases hlist : (c.terms.filter fun t => !falsified ρ t && (t.2 == l)) with _ | ⟨a, L⟩
    · simp [hlist] at ht
    · rw [hlist] at hall hnd
      have ha := hall a List.mem_cons_self
      cases L with
      | nil => rw [ha]
      | cons b L =>
        have hb := hall b (by simp)
        simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
        exact absurd (ha.trans hb.symm) hnd.1.1
  rw [hone] at hsplit
  simp only [coeffSum_cons, coeffSum_nil, Nat.add_zero] at hsplit
  unfold propagate at hp
  split at hp
  · cases hp
  · cases hp
    refine List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_filter.2 ⟨htm, ?_⟩, htl⟩)
    have hc : ρ.contains l = false := by simpa using hin
    simp only [hft, htl, hc, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    unfold slack
    omega

/-- **Propagation keeps the trail consistent** on a constraint over distinct variables. -/
theorem trailConsistent_of_propagate {c : PBConstr} (hd : (c.terms.map termVar).Nodup)
    {ρ ρ' : List (Literal ℕ)} (hρ : TrailConsistent ρ) (hp : propagate ρ c = some ρ') :
    TrailConsistent ρ' := by
  unfold propagate at hp
  split at hp
  · cases hp
  cases hp
  -- The literal of an unfalsified term, not already on the trail.
  have hnew : ∀ l ∈ (c.terms.filter fun t => !falsified ρ t && !ρ.contains t.2 &&
      decide (slack ρ c < t.1)).map (·.2), (∃ t ∈ c.terms, t.2 = l) ∧
        Std.Sat.Literal.negate l ∉ ρ ∧ l ∉ ρ := by
    intro l hl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
    obtain ⟨htm, hp⟩ := List.mem_filter.1 ht
    simp only [Bool.and_eq_true, Bool.not_eq_true', falsified] at hp
    exact ⟨⟨t, htm, rfl⟩, by simpa using hp.1.1, by simpa using hp.1.2⟩
  intro l hl hn
  rcases List.mem_append.1 hl with hl | hl <;> rcases List.mem_append.1 hn with hn | hn
  · obtain ⟨⟨t, ht, rfl⟩, -⟩ := hnew _ hl
    obtain ⟨⟨t', ht', he⟩, -⟩ := hnew _ hn
    have := eq_of_termVar_eq hd ht' ht (by
      obtain ⟨a, v, b⟩ := t; obtain ⟨a', v', b'⟩ := t'
      simp only [Std.Sat.Literal.negate, Prod.mk.injEq] at he
      simp [he.1])
    rw [this] at he
    exact negate_ne_self _ he.symm
  · exact (hnew _ hl).2.1 hn
  · have := (hnew _ hn).2.1
    rw [negate_negate] at this
    exact this hl
  · exact hρ l hl hn

/-! ### Reverse unit propagation -/

/-- **A justified run of hints**: from every consistent trail containing the literals `K`, the hints
`hs` reach a conflict. -/
def RupOk (db : List (ℕ × PBConstr)) (neg : PBConstr) (hs : List Hint) (K : List (Literal ℕ)) :
    Prop :=
  ∀ ρ, TrailConsistent ρ → (∀ l ∈ K, l ∈ ρ) → rupHints db neg hs ρ = true

/-- **A hint in conflict**: a constraint over distinct variables violated by every assignment
satisfying `K` closes the run. -/
theorem RupOk.conflict {db : List (ℕ × PBConstr)} {neg c : PBConstr} {h : Hint} {hs : List Hint}
    {K : List (Literal ℕ)} (hc : resolve db neg h = some c) (hd : (c.terms.map termVar).Nodup)
    (hk : ∀ σ, Consistent σ K → ¬ c.Holds σ) : RupOk db neg (h :: hs) K := by
  intro ρ hρ hK
  have : propagate ρ c = none := propagate_eq_none_of_forall hd hρ fun σ hσ =>
    hk σ fun l hl => hσ l (hK l hl)
  simp [rupHints, hc, this]

/-- **A propagating hint**: a constraint over distinct variables that, with `K`, implies the
literals `L` lets the run continue from `L ++ K`. -/
theorem RupOk.imp {db : List (ℕ × PBConstr)} {neg c : PBConstr} {h : Hint} {hs : List Hint}
    {K L : List (Literal ℕ)} (hc : resolve db neg h = some c) (hd : (c.terms.map termVar).Nodup)
    (hk : ∀ σ, Consistent σ K → c.Holds σ → Consistent σ L) (hrest : RupOk db neg hs (L ++ K)) :
    RupOk db neg (h :: hs) K := by
  intro ρ hρ hK
  simp only [rupHints, hc]
  split
  · rfl
  · rename_i ρ' hp
    refine hrest ρ' (trailConsistent_of_propagate hd hρ hp) fun l hl => ?_
    have hsub : ∀ m ∈ ρ, m ∈ ρ' := by
      unfold propagate at hp
      split at hp
      · cases hp
      · cases hp; exact fun m hm => List.mem_append_right _ hm
    rcases List.mem_append.1 hl with hl | hl
    · exact mem_of_propagate hd hρ hp fun σ hσ hcσ =>
        hk σ (fun m hm => hσ m (hK m hm)) hcσ l hl
    · exact hsub l (hK l hl)

/-- **More literals justify the same run.** -/
theorem RupOk.mono {db : List (ℕ × PBConstr)} {neg : PBConstr} {hs : List Hint}
    {K K' : List (Literal ℕ)} (h : RupOk db neg hs K) (hK : ∀ l ∈ K, l ∈ K') :
    RupOk db neg hs K' :=
  fun ρ hρ hK' => h ρ hρ fun l hl => hK' l (hK l hl)

/-- A run of hints each of which implies one literal from `K`. -/
theorem RupOk.imps {db : List (ℕ × PBConstr)} {neg : PBConstr} {K₀ : List (Literal ℕ)}
    {rest : List Hint} :
    ∀ (xs : List (Hint × Literal ℕ)) (K : List (Literal ℕ)), (∀ l ∈ K₀, l ∈ K) →
      (∀ x ∈ xs, ∃ c, resolve db neg x.1 = some c ∧ (c.terms.map termVar).Nodup ∧
        ∀ σ, Consistent σ K₀ → c.Holds σ → Literal.eval σ x.2 = true) →
      RupOk db neg rest (xs.map (·.2) ++ K) → RupOk db neg (xs.map (·.1) ++ rest) K
  | [], K, _, _, h => by simpa using h
  | x :: xs, K, hK, hx, h => by
    obtain ⟨c, hc, hd, hi⟩ := hx x List.mem_cons_self
    refine RupOk.imp (L := [x.2]) hc hd
      (fun σ hσ hcσ => by
        have := hi σ (fun l hl => hσ l (hK l hl)) hcσ
        intro l hl; simp only [List.mem_singleton] at hl; subst hl; exact this) ?_
    refine RupOk.imps xs ([x.2] ++ K) (fun l hl => List.mem_append_right _ (hK l hl))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (RupOk.mono h ?_)
    intro l hl
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hl ⊢
    tauto

/-- **A `rup` step is accepted** when its hints are justified from the empty trail. -/
theorem rup_of_rupOk {db : List (ℕ × PBConstr)} {c : PBConstr} {hs : List Hint}
    (h : RupOk db c.negate hs []) : rup db c hs = true :=
  h [] (fun _ h => by cases h) (fun _ h => by cases h)

/-! ### Normalized constraints -/

/-- The terms of a negation are on distinct variables. -/
theorem nodup_vars_negate (c : PBConstr) : (c.negate.terms.map termVar).Nodup := by
  have := nodup_termVar_normalize c
  simp only [negate, List.map_map]
  convert this using 2
  ext t
  obtain ⟨a, v, b⟩ := t
  simp [Std.Sat.Literal.negate]

private theorem negMass_toLinear_of_nodup {ts : List (ℕ × Literal ℕ)}
    (hd : (ts.map termVar).Nodup) : negMass (toLinear ts) = negSum ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.nodup_cons] at hd
    have hn : termVar t ∉ (toLinear ts).map Prod.fst := fun h => hd.1 (by
      obtain ⟨e, he, hev⟩ := List.mem_map.1 h
      exact hev ▸ fst_mem_of_mem_toLinear he)
    rw [show toLinear (t :: ts) = insertCoeff (termVar t) (termCoeff t) (toLinear ts) from rfl,
      insertCoeff_of_not_mem hn, negSum_cons, ← ih hd.2]
    obtain ⟨a, v, b⟩ := t
    cases b <;> simp [negMass, termCoeff, termPos, Nat.add_comm]

/-- **Normalization keeps the slack** of a constraint over distinct variables: `∑ aᵢ ℓᵢ - d` is
the same at every assignment. -/
theorem slack_normalize {c : PBConstr} (hd : (c.terms.map termVar).Nodup) (σ : ℕ → Bool) :
    (lhs σ c.normalize.terms : ℤ) - c.normalize.degree = lhs σ c.terms - c.degree := by
  have hm := negMass_toLinear_of_nodup hd
  have h1 := lhs_fromLinear σ (toLinear c.terms) ((c.degree : ℤ) - negSum c.terms)
  have h2 := lhs_eq_linVal σ c.terms
  simp only [normalize, fromLinear] at h1 ⊢
  rw [h1, hm]
  omega

/-- **The sum of two constraints holds exactly when their slacks add up to a nonnegative
number.** -/
theorem holds_add_iff (σ : ℕ → Bool) (c d : PBConstr) :
    (c.add d).Holds σ ↔ (c.degree : ℤ) + d.degree ≤ lhs σ c.terms + lhs σ d.terms := by
  rw [PBConstr.add, holds_normalize, Holds, lhs_append]
  simp only
  omega

/-! ### Forced literals -/

/-- The constraint `c` **forces** the literal `l` on the trail `ρ`: `ρ` does not falsify `l`, and
a term of `c` on `l` has a coefficient above the slack of `c`. Unit propagation of `c` then makes
`l` true (`Cslib.Logic.PL.VeriPB.Forces.propagate`). -/
def Forces (ρ : List (Literal ℕ)) (c : PBConstr) (l : Literal ℕ) : Prop :=
  Std.Sat.Literal.negate l ∉ ρ ∧ ∃ a, (a, l) ∈ c.terms ∧ slack ρ c < a

private theorem coeffSum_filter_mono {ts : List (ℕ × Literal ℕ)} {p q : ℕ × Literal ℕ → Bool}
    (h : ∀ t ∈ ts, p t = true → q t = true) :
    coeffSum (ts.filter p) ≤ coeffSum (ts.filter q) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ih := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
    have ht := h t List.mem_cons_self
    by_cases hp : p t = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (ht hp), coeffSum_cons,
        coeffSum_cons]
      omega
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q t = true
      · rw [List.filter_cons_of_pos hq, coeffSum_cons]; omega
      · rw [List.filter_cons_of_neg hq]; exact ih

private theorem not_falsified_of_sub {ρ ρ' : List (Literal ℕ)} (h : ∀ l ∈ ρ, l ∈ ρ')
    {t : ℕ × Literal ℕ} (ht : (!falsified ρ' t) = true) : (!falsified ρ t) = true := by
  unfold falsified at *
  cases h1 : ρ.contains (Std.Sat.Literal.negate t.2)
  · rfl
  · exact absurd (h _ (List.contains_iff_mem.1 h1)) (by simpa using ht)

/-- **The slack only falls as the trail grows.** -/
theorem slack_anti {ρ ρ' : List (Literal ℕ)} (h : ∀ l ∈ ρ, l ∈ ρ') (c : PBConstr) :
    slack ρ' c ≤ slack ρ c := by
  unfold slack
  have := coeffSum_filter_mono (ts := c.terms) fun t _ => not_falsified_of_sub h (t := t)
  omega

/-- A term the larger trail falsifies, and the smaller does not, lowers the slack by its
coefficient. -/
private theorem slack_add_le {ρ ρ' : List (Literal ℕ)} (h : ∀ l ∈ ρ, l ∈ ρ') {c : PBConstr}
    {a : ℕ} {l : Literal ℕ} (hl : (a, l) ∈ c.terms) (hn : Std.Sat.Literal.negate l ∉ ρ)
    (hn' : Std.Sat.Literal.negate l ∈ ρ') : slack ρ' c + a ≤ slack ρ c := by
  unfold slack
  have hsplit := coeffSum_filter_add c.terms (fun t => !falsified ρ t) (fun t => !falsified ρ' t)
  have h1 : (c.terms.filter fun t => !falsified ρ t && !falsified ρ' t) =
      c.terms.filter fun t => !falsified ρ' t :=
    List.filter_congr fun t _ => by
      cases h' : falsified ρ' t
      · simp [not_falsified_of_sub h (t := t) (by simp [h'])]
      · simp
  have h2 : a ≤ coeffSum (c.terms.filter fun t => !falsified ρ t && !!falsified ρ' t) :=
    le_coeffSum_of_mem (t := (a, l)) (List.mem_filter.2 ⟨hl, by simp [falsified, hn, hn']⟩)
  rw [h1] at hsplit
  omega

/-- **A forced literal is propagated**: on any larger trail, propagating `c` finds a conflict or
makes `l` true. -/
theorem Forces.propagate {ρ ρ' : List (Literal ℕ)} {c : PBConstr} {l : Literal ℕ}
    (hF : Forces ρ c l) (h : ∀ m ∈ ρ, m ∈ ρ') :
    VeriPB.propagate ρ' c = none ∨
      ∃ ρ'', VeriPB.propagate ρ' c = some ρ'' ∧ l ∈ ρ'' ∧ ∀ m ∈ ρ', m ∈ ρ'' := by
  obtain ⟨hn, a, hl, hs⟩ := hF
  unfold VeriPB.propagate
  by_cases h0 : slack ρ' c < 0
  · left; simp [h0]
  right
  simp only [h0, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun m hm => List.mem_append_right _ hm⟩
  by_cases hl' : l ∈ ρ'
  · exact List.mem_append_right _ hl'
  have hn' : Std.Sat.Literal.negate l ∉ ρ' := fun hn' => by
    have := slack_add_le h hl hn hn'
    omega
  have := slack_anti h c
  refine List.mem_append_left _ (List.mem_map.2 ⟨(a, l), List.mem_filter.2 ⟨hl, ?_⟩, rfl⟩)
  simp [falsified, hn', hl']
  omega

/-- **A chain of forced literals closes a RUP run**: if each hint of `xs` names a constraint
forcing its literal on the literals before it (after those of `B`), and the hint `h` names a
constraint whose slack on all of them is negative, then the hints `xs` and then `h` reach a
conflict from every trail containing `B`. -/
theorem rupHints_of_forces {db : List (ℕ × PBConstr)} {neg : PBConstr} {h : Hint} :
    ∀ (xs : List (Hint × Literal ℕ)) (B ρ : List (Literal ℕ)), (∀ l ∈ B, l ∈ ρ) →
      (∀ (k : ℕ) (hk : k < xs.length), ∃ c, resolve db neg xs[k].1 = some c ∧
        Forces (B ++ (xs.take k).map (·.2)) c xs[k].2) →
      (∃ c, resolve db neg h = some c ∧ slack (B ++ xs.map (·.2)) c < 0) →
      rupHints db neg (xs.map (·.1) ++ [h]) ρ = true
  | [], B, ρ, hB, _, ⟨c, hc, hs⟩ => by
    have : VeriPB.propagate ρ c = none := by
      have := slack_anti hB c
      simp only [List.map_nil, List.append_nil] at hs
      simp [VeriPB.propagate]
      omega
    simp [rupHints, hc, this]
  | x :: xs, B, ρ, hB, hx, hc => by
    obtain ⟨c, hcx, hF⟩ := hx 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, List.map_nil, List.append_nil] at hcx hF
    simp only [List.map_cons, List.cons_append, rupHints, hcx]
    rcases hF.propagate hB with hp | ⟨ρ'', hp, hl, hsub⟩
    · simp [hp]
    · simp only [hp]
      refine rupHints_of_forces xs (B ++ [x.2]) ρ'' (fun m hm => ?_) (fun k hk => ?_) ?_
      · rcases List.mem_append.1 hm with hm | hm
        · exact hsub m (hB m hm)
        · simp only [List.mem_singleton] at hm; exact hm ▸ hl
      · obtain ⟨c, h1, h2⟩ := hx (k + 1) (by simp; omega)
        exact ⟨c, by simpa using h1, by simpa using h2⟩
      · simpa using hc

/-- **Adding a literal to the trail** lowers the slack by the coefficients of the terms on its
negation. -/
theorem slack_append_singleton {ρ : List (Literal ℕ)} {m : Literal ℕ} (hm : m ∉ ρ) (c : PBConstr) :
    slack (ρ ++ [m]) c = slack ρ c -
      (((c.terms.filter fun t => t.2 == Std.Sat.Literal.negate m).map (·.1)).sum : ℕ) := by
  unfold slack
  have key : ∀ ts : List (ℕ × Literal ℕ), (∀ t ∈ ts, True) →
      (coeffSum (ts.filter fun t => !falsified (ρ ++ [m]) t) : ℤ) =
        coeffSum (ts.filter fun t => !falsified ρ t) -
          (((ts.filter fun t => t.2 == Std.Sat.Literal.negate m).map (·.1)).sum : ℕ) := by
    intro ts _
    induction ts with
    | nil => simp
    | cons t ts ih =>
      simp only [forall_const] at ih
      have hneg : Std.Sat.Literal.negate t.2 = m ↔ t.2 = Std.Sat.Literal.negate m := by
        constructor
        · rintro rfl; simp
        · rintro h; rw [h]; simp
      by_cases ht : t.2 = Std.Sat.Literal.negate m
      · have h1 : falsified (ρ ++ [m]) t = true := by
          simp [falsified, hneg.2 ht]
        have h2 : falsified ρ t = false := by
          simp only [falsified, Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
          rw [hneg.2 ht]; exact hm
        simp [h1, h2, ht, ih]
      · have h1 : falsified (ρ ++ [m]) t = falsified ρ t := by
          simp only [falsified, List.contains_append, List.contains_cons, List.contains_nil,
            Bool.or_false]
          have : (Std.Sat.Literal.negate t.2 == m) = false := by
            simpa [beq_iff_eq] using fun h => ht (hneg.1 h)
          simp [this]
        cases hf : falsified ρ t
        · simp [h1, hf, ht, ih]; omega
        · simp [h1, hf, ht, ih]
  rw [key c.terms (fun _ _ => trivial)]
  omega

end Cslib.Logic.PL.VeriPB

end
