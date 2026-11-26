/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Algorithms.Lean.DPLL
import CslibFrontier.Logics.Propositional.CNF.Tautology
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast

/-! # LRAT certificates are VeriPB proofs

An LRAT certificate [Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017] accepted by
`Cslib.Logic.PL.CNF.checkLRAT` translates step by step into a VeriPB kernel proof
[Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023] that
`Cslib.Logic.PL.VeriPB.check` accepts for the same formula, its clauses read as the
pseudo-Boolean constraints `Cslib.Logic.PL.Clause.toPB` (`Cslib.Logic.PL.CNF.check_toVeriPB`).
The translation `Cslib.Logic.PL.CNF.toVeriPB` maps

* a RUP step `addRup i c hints` to `rup c.toPB : ~ hints'`, which starts from the negated
  constraint;
* the empty-clause step to `rup 0 ≥ 1 : hints'`, the conclusion of the proof;
* a deletion to `del` of the kernel numbers of the clauses it deletes.

**Numbering.** LRAT names each added clause with a number chosen by the certificate, and the
checker reads the first clause of a number, so a reused number shadows the earlier clause. The
kernel numbers constraints consecutively. The translation keeps a renaming from certificate numbers
to kernel numbers, the latest first, and `hints'` are the hints renumbered along it. A deletion in
LRAT ignores numbers that name no clause and deletes every clause of a number it names, shadowed
ones too; the kernel's `del` requires its numbers to be present, so the translation deletes
exactly the kernel numbers of those clauses.

**Normalization.** The kernel stores `c.toPB` normalized. `Cslib.Logic.PL.Clause.toPB` keeps the
distinct literals of a clause, each with coefficient `1`, so a repeated literal counts once, as in
LRAT. A clause without complementary literals normalizes to itself, with its terms reversed
(`Cslib.Logic.PL.Clause.normalize_toPB_of_not_isTautology`). A clause with complementary literals
is a tautology, and normalizes to a constraint of degree `0`
(`Cslib.Logic.PL.Clause.degree_normalize_toPB_of_isTautology`), which propagates nothing. On a
consistent trail LRAT also gains nothing from it: its residual is never empty, and is unit only on
a literal already on the trail. So on consistent trails, pseudo-Boolean propagation of every
clause is unit propagation (`Cslib.Logic.PL.VeriPB.propagate_toPB`): the slack of a clause is its
number of literals not false minus one, so it conflicts exactly when it is falsified and forces a
literal exactly when it is unit. The trails of the LRAT checker stay consistent, except from the
negation of a tautological RUP clause; the kernel refutes that negation at once, from the `~`
hint alone.

**Why only one direction.** The theorem is an implication, not an equivalence. The kernel's
`Cslib.Logic.PL.VeriPB.rupHints` skips a hinted constraint that neither conflicts nor propagates,
while the LRAT checker's `Cslib.Logic.PL.CNF.propagateWith` rejects a hinted clause with two
literals left. So an LRAT step with a superfluous non-unit hint is rejected by `checkLRAT`, while
its translation is accepted; the test client checks such a certificate. An equivalence between
`checkLRAT` and the acceptance of some translation would say nothing, since a translation could
itself run `checkLRAT`. The faithful converse is the back-translation of the clausal `rup`/`del`
fragment of the kernel format into LRAT.

## Main definitions

* `Cslib.Logic.PL.Clause.unitStep`: unit propagation of one clause, skipping a clause with two
  literals left.
* `Cslib.Logic.PL.VeriPB.hintCount`: the number of hints of kernel steps.
* `Cslib.Logic.PL.CNF.toVeriPB`: the translation.

## Main results

* `Cslib.Logic.PL.VeriPB.propagate_eq_unitStep`, `Cslib.Logic.PL.VeriPB.propagate_toPB`: on a
  constraint of degree `1` on distinct variables, and on every clause on a consistent trail,
  pseudo-Boolean propagation is unit propagation.
* `Cslib.Logic.PL.CNF.check_toVeriPB`: an accepted LRAT certificate translates into an accepted
  kernel proof.
* `Cslib.Logic.PL.CNF.length_toVeriPB_le`, `Cslib.Logic.PL.CNF.hintCount_toVeriPB_le`,
  `Cslib.Logic.PL.CNF.toVeriPB_fragment`: a certificate of `S` steps with `H` hints translates
  into at most `S` steps with at most `H + S` hints, all `rup` steps for clauses or `del` steps.
* `Cslib.Logic.PL.CNF.checkRed_toVeriPB`: the checker with redundance accepts the translation.
* `Cslib.Logic.PL.CNF.exists_check_iff`, `Cslib.Logic.PL.CNF.exists_checkRed_iff`: a CNF formula
  has an accepted kernel proof of `UNSAT` exactly when it is unsatisfiable.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)
open PBConstr

/-! ### Unit propagation on one clause -/

/-- **Unit propagation of one clause** on the trail `ρ` of literals taken to be true, read through
its residual (`Cslib.Logic.PL.Clause.residual`): `none` when every literal is false, the trail
extended by the remaining literal when one is left, and the trail unchanged otherwise. Unlike
`Cslib.Logic.PL.CNF.propagateWith`, which rejects a clause with two literals left, this step
skips it, as pseudo-Boolean propagation does. -/
def Clause.unitStep (c : Clause ℕ) (ρ : List (Literal ℕ)) : Option (List (Literal ℕ)) :=
  match c.residual ρ with
  | .empty => none
  | .unit l => some (if ρ.contains l then ρ else l :: ρ)
  | .other => some ρ

/-- The residual of a clause reads the clause only through membership. -/
theorem Clause.residual_congr_left {c c' : Clause ℕ} (h : ∀ l, l ∈ c ↔ l ∈ c')
    (t : List (Literal ℕ)) : c.residual t = c'.residual t := by
  have he : c.residual t = .empty ↔ c'.residual t = .empty := by
    simp only [residual_eq_empty_iff, h]
  have hu : ∀ l, c.residual t = .unit l ↔ c'.residual t = .unit l := by
    intro l
    simp only [residual_eq_unit_iff, h]
  cases hc : c.residual t <;> cases hc' : c'.residual t <;> simp_all

namespace VeriPB

/-- A trail is *consistent* when it holds no literal together with its negation. -/
def TrailConsistent (ρ : List (Literal ℕ)) : Prop :=
  ∀ l ∈ ρ, Std.Sat.Literal.negate l ∉ ρ

mutual

/-- The number of hints of a step: those of a `rup` step, and those of the steps of a `pbc`
subproof. -/
def Step.hintCount : Step → ℕ
  | .rup _ hs => hs.length
  | .pbc _ sub _ => VeriPB.hintCount sub
  | _ => 0

/-- The number of hints of a list of steps (`Cslib.Logic.PL.VeriPB.Step.hintCount`). -/
def hintCount : List Step → ℕ
  | [] => 0
  | s :: ss => s.hintCount + VeriPB.hintCount ss

end

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

/-- **A constraint of degree `0` propagates nothing**: it never conflicts, and a term it could
force has a coefficient within the slack. -/
theorem propagate_of_degree_eq_zero {c : PBConstr} (h : c.degree = 0) (ρ : List (Literal ℕ)) :
    propagate ρ c = some ρ := by
  have hnil : (c.terms.filter fun t => !falsified ρ t && !ρ.contains t.2 &&
      decide (slack ρ c < t.1)) = [] := by
    refine List.filter_eq_nil_iff.2 fun t ht hp => ?_
    have hf : (!falsified ρ t) = true := by revert hp; cases falsified ρ t <;> simp
    have hlt : slack ρ c < t.1 := by revert hp; simp
    have := le_coeffSum_of_mem ((List.mem_filter (p := fun t => !falsified ρ t)).2 ⟨ht, hf⟩)
    simp only [slack, h, Nat.cast_zero, sub_zero] at hlt
    omega
  have hs : ¬ slack ρ c < 0 := by simp [slack, h]
  unfold propagate
  rw [hnil, ite_eq_right hs]
  rfl

/-- The literals of the terms of `c` that the trail does not falsify. -/
private theorem filter_map_snd (ρ : List (Literal ℕ)) (ts : List (ℕ × Literal ℕ)) :
    (ts.map (·.2)).filter (fun l => !ρ.contains (Std.Sat.Literal.negate l)) =
      (ts.filter fun t => !falsified ρ t).map (·.2) := by
  rw [List.filter_map]
  rfl

/-- **On a constraint of degree `1`, pseudo-Boolean propagation is unit propagation** of the
clause of its literals: if its terms are on distinct variables and have positive coefficients,
the slack is the sum of the coefficients of the literals not falsified, minus `1`. So it
conflicts exactly when every literal is false, forces a literal exactly when that literal alone
is not false, and otherwise forces nothing. -/
theorem propagate_eq_unitStep {c : PBConstr} (hv : (c.terms.map termVar).Nodup)
    (hpos : ∀ t ∈ c.terms, 0 < t.1) (hd : c.degree = 1) (ρ : List (Literal ℕ)) :
    propagate ρ c = Clause.unitStep (c.terms.map (·.2)) ρ := by
  -- the terms not falsified, on distinct variables
  set F := c.terms.filter fun t => !falsified ρ t with hF
  have hFv : (F.map termVar).Nodup := hv.sublist (List.filter_sublist.map _)
  have hFpos : ∀ t ∈ F, 0 < t.1 := fun t ht => hpos t (List.mem_of_mem_filter ht)
  have hslack : slack ρ c = (coeffSum F : ℤ) - 1 := by simp [slack, hd, hF]
  -- the terms the step forces are the terms of `F` that pass the test
  have hforce : (c.terms.filter fun t => !falsified ρ t && !ρ.contains t.2 &&
      decide (slack ρ c < t.1)) =
      F.filter fun t => !ρ.contains t.2 && decide (slack ρ c < t.1) := by
    rw [hF, List.filter_filter]
    exact List.filter_congr fun t _ => by cases falsified ρ t <;> simp
  unfold propagate Clause.unitStep Clause.residual
  rw [filter_map_snd, ← hF, hforce]
  match hFm : F with
  | [] => simp [hslack, hFm]
  | [t] =>
    have h1 := hFpos t (by simp [hFm])
    by_cases hc : t.2 ∈ ρ <;> simp [hslack, hFm, h1.ne', hc]
  | t₁ :: t₂ :: ts =>
    have h1 := hFpos t₁ (by simp [hFm])
    have h2 := hFpos t₂ (by simp [hFm])
    have hs : ¬ slack ρ c < 0 := by rw [hslack, hFm]; simp; omega
    have hnil : ((t₁ :: t₂ :: ts).filter fun t => !ρ.contains t.2 &&
        decide (slack ρ c < t.1)) = [] := by
      refine List.filter_eq_nil_iff.2 fun t ht hp => ?_
      simp only [Bool.and_eq_true, decide_eq_true_eq, hslack, hFm, coeffSum_cons] at hp
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · omega
      · omega
      have := le_coeffSum_of_mem ht
      omega
    have hb : (t₂.2 == t₁.2) = false := by
      have := hFm ▸ hFv
      simp only [List.map_cons, List.nodup_cons, List.mem_cons] at this
      exact beq_eq_false_iff_ne.2 fun heq => this.1 (.inl (congrArg Prod.fst heq).symm)
    simp only [List.contains_eq_mem] at hnil
    simp [hs, hb, hnil]

end VeriPB

/-- The terms of a normalized constraint have positive coefficients. -/
theorem PBConstr.pos_of_mem_normalize {c : PBConstr}
    {t : ℕ × Literal ℕ} (ht : t ∈ c.normalize.terms) : 0 < t.1 := by
  obtain ⟨e, -, he⟩ := List.mem_filterMap.1 ht
  unfold entryTerm at he
  split_ifs at he <;> cases he <;> omega

/-! ### Clauses as constraints -/

private theorem nodup_termVar_toPB {d : Clause ℕ} (hd : ¬ ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d) :
    ((Clause.toPB d).terms.map termVar).Nodup := by
  simp only [Clause.toPB, List.map_map]
  exact CNF.nodup_map_fst_dedup_of_not_isTautClause (by simpa [CNF.isTautClause] using hd)

/-- **A clause without complementary literals normalizes to itself**: its distinct literals, in
reverse order, with coefficient `1` and degree `1`. -/
theorem Clause.normalize_toPB_of_not_isTautology {d : Clause ℕ}
    (hd : ¬ ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d) :
    d.toPB.normalize = ⟨(d.dedup.map fun l => (1, l)).reverse, 1⟩ :=
  normalize_of_nodup (nodup_termVar_toPB hd) fun t ht => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
    exact Nat.one_pos

/-- **A tautological clause normalizes to a constraint of degree `0`**: it holds everywhere, and
the assignment falsifying every term of the normal form, whose variables are distinct, gives the
left side `0`. -/
theorem Clause.degree_normalize_toPB_of_isTautology {d : Clause ℕ}
    (hd : ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d) :
    d.toPB.normalize.degree = 0 := by
  set N := d.toPB.normalize
  have hv := nodup_termVar_normalize d.toPB
  let σ : ℕ → Bool := fun v => match N.terms.find? (termVar · == v) with
    | some t => !termPos t
    | none => false
  have hfalse : ∀ t ∈ N.terms, Literal.eval σ t.2 = false := by
    rintro ⟨a, v, b⟩ ht
    have hf : (N.terms.find? (termVar · == v)).isSome :=
      List.find?_isSome.2 ⟨(a, v, b), ht, by simp [termVar]⟩
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hf
    obtain rfl : t' = (a, v, b) := List.inj_on_of_nodup_map hv (List.mem_of_find?_eq_some ht') ht
      (by simpa [termVar] using List.find?_some ht')
    simp [Literal.eval, σ, ht', termPos_mk]
  have hholds : N.Holds σ := by
    rw [holds_normalize, Clause.holds_toPB_iff]
    exact CNF.eval_eq_true_of_isTautClause (by simpa [CNF.isTautClause] using hd) σ
  have hlhs : lhs σ N.terms = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    simp [termVal, hfalse t ht]
  unfold Holds at hholds
  omega

/-- A clause normalizes to a constraint of degree at most `1`. -/
theorem Clause.degree_normalize_toPB_le (d : Clause ℕ) : d.toPB.normalize.degree ≤ 1 := by
  by_cases hd : ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d
  · simp [Clause.degree_normalize_toPB_of_isTautology hd]
  · simp [Clause.normalize_toPB_of_not_isTautology hd]

namespace VeriPB

private theorem coeffSum_map_negate (ts : List (ℕ × Literal ℕ)) :
    coeffSum (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) = coeffSum ts := by
  simp [coeffSum, List.map_map, Function.comp_def]

private theorem filter_falsified_nil (ts : List (ℕ × Literal ℕ)) :
    ts.filter (fun t => !falsified [] t) = ts :=
  List.filter_eq_self.2 fun _ _ => by simp [falsified]

/-- The negation of a tautological clause conflicts at once. -/
private theorem propagate_nil_negate_toPB_of_isTautology {d : Clause ℕ}
    (hd : ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d) :
    propagate [] d.toPB.negate = none := by
  have h0 := Clause.degree_normalize_toPB_of_isTautology hd
  simp only [propagate, slack, negate, filter_falsified_nil, coeffSum_map_negate, h0]
  simp

/-- **The negation of a clause without complementary literals** forces the negation of each of
its literals, starting from the empty trail. -/
private theorem propagate_nil_negate_toPB {d : Clause ℕ}
    (hd : ¬ ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d) :
    ∃ ρ, propagate [] d.toPB.negate = some ρ ∧
      ∀ l, l ∈ ρ ↔ l ∈ d.map Std.Sat.Literal.negate := by
  have hN := Clause.normalize_toPB_of_not_isTautology hd
  have hc : coeffSum ((d.dedup.map fun l => (1, l)).reverse) = d.dedup.length := by
    simp [coeffSum, List.map_map, Function.comp_def]
  have hc' : coeffSum ((d.dedup.map fun l => (1, Std.Sat.Literal.negate l)).reverse) =
      d.dedup.length := by
    simp [coeffSum, List.map_map, Function.comp_def]
  refine ⟨(d.dedup.map Std.Sat.Literal.negate).reverse, ?_, fun l => ?_⟩
  · simp [hc', propagate, slack, negate, hN, hc, falsified, List.map_reverse, List.map_map,
      Function.comp_def, List.filter_map]
  · simp [List.mem_dedup]

/-- **On a clause, pseudo-Boolean propagation is unit propagation.** For every clause `d` and
every consistent trail, propagating the constraint `d.toPB`, normalized as the checker stores it,
conflicts exactly when every literal of `d` is false, forces `l` exactly when `l` is the only
literal of `d` not false, and otherwise leaves the trail unchanged
(`Cslib.Logic.PL.Clause.unitStep`). For a clause without complementary literals the normal form
is the clause with coefficient `1` and degree `1`, whose slack is its number of literals not
false minus one (`Cslib.Logic.PL.VeriPB.propagate_eq_unitStep`). A tautological clause
normalizes to degree `0` and propagates nothing; on a consistent trail its residual is never
empty, and a literal it is unit on is already on the trail. -/
theorem propagate_toPB (d : Clause ℕ) {ρ : List (Literal ℕ)} (hρ : TrailConsistent ρ) :
    propagate ρ d.toPB.normalize = d.unitStep ρ := by
  by_cases hd : ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d
  · rw [propagate_of_degree_eq_zero (Clause.degree_normalize_toPB_of_isTautology hd)]
    obtain ⟨x, hx, hnx⟩ := hd
    unfold Clause.unitStep
    rcases h : d.residual ρ with _ | l | _
    · have hall := Clause.residual_eq_empty_iff.1 h
      exact absurd (by simpa using hall _ hnx) (hρ _ (hall x hx))
    · obtain ⟨-, -, hall⟩ := Clause.residual_eq_unit_iff.1 h
      have hl : l ∈ ρ := by
        by_cases hxl : x = l
        · subst hxl
          simpa using hall _ hnx (by cases x; simp [Std.Sat.Literal.negate])
        · by_cases hnl : Std.Sat.Literal.negate x = l
          · exact hnl ▸ hall x hx hxl
          · exact absurd (by simpa using hall _ hnx hnl) (hρ _ (hall x hx hxl))
      simp [hl]
    · rfl
  · have hN := Clause.normalize_toPB_of_not_isTautology hd
    rw [propagate_eq_unitStep (nodup_termVar_normalize d.toPB)
      (fun _ ht => pos_of_mem_normalize ht) (by rw [hN])]
    unfold Clause.unitStep
    rw [Clause.residual_congr_left (c' := d) (by simp [hN, List.mem_dedup])]

end VeriPB

/-! ### The translation -/

namespace CNF

/-- The hints of an LRAT step as kernel hints, renumbered along `ren`, which maps certificate
numbers to kernel numbers, the first match counting. A hint without a number is dropped; the LRAT
checker rejects it. -/
def renameHints (ren : List (ℕ × ℕ)) (hs : List ℕ) : List VeriPB.Hint :=
  hs.filterMap fun h => (ren.lookup h).map VeriPB.Hint.id

/-- **The translation of the steps of an LRAT certificate**, from the renaming `ren` of
certificate numbers to kernel numbers and the next kernel number `n`:
* a RUP step `addRup i c hints` becomes `rup c.toPB : ~ hints'`, with `hints'` the renumbered
  hints, and `i` is renamed to `n`, shadowing an earlier clause numbered `i`;
* the empty-clause step becomes `rup 0 ≥ 1 : hints'`, and the translation stops there, with that
  step as the conclusion, as the LRAT checker stops;
* a deletion becomes `del` of the kernel numbers of the clauses it deletes, which are all present;
* a RAT step, which the LRAT checker rejects, ends the translation. -/
def toVeriPBAux : List (ℕ × ℕ) → ℕ → List LRAT.IntAction → VeriPB.Proof
  | _, _, [] => ⟨[], 0⟩
  | ren, n, .addEmpty _ hints :: _ =>
    ⟨[.rup (Clause.toPB []) (renameHints ren hints.toList)], n⟩
  | ren, n, .addRup i c hints :: rest =>
    let P := toVeriPBAux ((i, n) :: ren) (n + 1) rest
    ⟨.rup (Clause.ofDIMACS c.toList).toPB (.neg :: renameHints ren hints.toList) :: P.steps,
      P.conclusion⟩
  | _, _, .addRat .. :: _ => ⟨[], 0⟩
  | ren, n, .del ids :: rest =>
    let P := toVeriPBAux (ren.filter fun e => !ids.toList.contains e.1) n rest
    ⟨.del ((ren.filter fun e => ids.toList.contains e.1).map (·.2)) :: P.steps, P.conclusion⟩

/-- **An LRAT certificate as a VeriPB kernel proof** for the formula `φ.map Clause.toPB`. The
clauses of `φ` keep their numbers `1, 2, …`, and the steps translate one by one
(`Cslib.Logic.PL.CNF.toVeriPBAux`). -/
def toVeriPB (φ : CNF ℕ) (cert : Array LRAT.IntAction) : VeriPB.Proof :=
  toVeriPBAux (φ.lratDB.map fun e => (e.1, e.1)) (φ.length + 1) cert.toList

end CNF

/-! ### Correctness -/

namespace VeriPB

/-- A clause of the LRAT database with its kernel number, during the translation. -/
private structure Entry where
  /-- The certificate number. -/
  key : ℕ
  /-- The kernel number. -/
  num : ℕ
  /-- The clause. -/
  clause : Clause ℕ

private def lratPart (J : List Entry) : List (ℕ × Clause ℕ) := J.map fun e => (e.key, e.clause)

private def renPart (J : List Entry) : List (ℕ × ℕ) := J.map fun e => (e.key, e.num)

private def pbPart (J : List Entry) : List (ℕ × PBConstr) :=
  J.map fun e => (e.num, e.clause.toPB.normalize)

private theorem pbPart_map_fst (J : List Entry) : (pbPart J).map (·.1) = J.map Entry.num := by
  simp [pbPart, Function.comp_def]

private theorem mem_num_of_lookup {J : List Entry} {p : ℕ} {c : PBConstr}
    (h : lookup (pbPart J) p = some c) : p ∈ J.map Entry.num := by
  obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.1 h
  have hk := List.find?_some he
  simp only [beq_iff_eq] at hk
  rw [← pbPart_map_fst, ← hk]
  exact List.mem_map_of_mem (List.mem_of_find?_eq_some he)

/-- A clause the LRAT database finds has a kernel number, under which the kernel database holds
its constraint. -/
private theorem lookup_parts {J : List Entry} (hJ : (J.map Entry.num).Nodup) {h : ℕ}
    {d : Clause ℕ} (hl : (lratPart J).lookup h = some d) :
    ∃ p, (renPart J).lookup h = some p ∧ lookup (pbPart J) p = some d.toPB.normalize := by
  induction J with
  | nil => simp [lratPart] at hl
  | cons e J ih =>
    simp only [List.map_cons, List.nodup_cons] at hJ
    by_cases he : h = e.key
    · subst he
      simp only [lratPart, List.map_cons, List.lookup_cons, BEq.rfl, Option.some.injEq] at hl
      subst hl
      simp [renPart, pbPart, lookup]
    · have hne : (h == e.key) = false := by simpa using he
      have hl' : (lratPart J).lookup h = some d := by
        simpa [lratPart, List.lookup_cons, hne] using hl
      obtain ⟨p, hp, hq⟩ := ih hJ.2 hl'
      have hpe : p ≠ e.num := fun hpe => hJ.1 (hpe ▸ mem_num_of_lookup hq)
      refine ⟨p, by simpa [renPart, List.lookup_cons, hne] using hp, ?_⟩
      simpa [lookup, pbPart, List.find?_cons, Ne.symm hpe] using hq

/-- **The renumbered hints propagate in the kernel as the hints do in the LRAT checker**, from a
trail with the same literals. -/
private theorem rupHints_renameHints {J : List Entry} (hJ : (J.map Entry.num).Nodup)
    (neg : PBConstr) : ∀ (hs : List ℕ) (t ρ : List (Literal ℕ)), TrailConsistent t →
      (∀ l, l ∈ ρ ↔ l ∈ t) → CNF.propagateHints (lratPart J) t hs = true →
      rupHints (pbPart J) neg (CNF.renameHints (renPart J) hs) ρ = true
  | [], _, _, _, _, h => by simp [CNF.propagateHints_nil] at h
  | x :: hs, t, ρ, ht, hρ, h => by
    simp only [CNF.propagateHints, CNF.propagateWith] at h
    rcases hl : (lratPart J).lookup x with _ | d
    · simp [hl] at h
    obtain ⟨p, hp, hq⟩ := lookup_parts hJ hl
    have hcons : CNF.renameHints (renPart J) (x :: hs) =
        .id p :: CNF.renameHints (renPart J) hs := by
      simp [CNF.renameHints, hp]
    have hρc : TrailConsistent ρ := fun l hl hn => ht l ((hρ l).1 hl) ((hρ _).1 hn)
    rw [hcons]
    simp only [rupHints, resolve, hq, propagate_toPB d hρc]
    simp only [hl] at h
    unfold Clause.unitStep
    rw [Clause.residual_congr _ hρ]
    rcases hr : d.residual t with _ | l | _ <;> simp only [hr] at h
    · rfl
    · obtain ⟨-, hlt, -⟩ := Clause.residual_eq_unit_iff.1 hr
      refine rupHints_renameHints hJ neg hs (l :: t) _ (ht.cons hlt) ?_ h
      intro m
      split
      · rename_i hc
        have : l ∈ t := (hρ l).1 (by simpa using hc)
        simp only [List.mem_cons, hρ]
        exact ⟨fun h => .inr h, fun h => h.elim (· ▸ this) id⟩
      · simp [hρ]
    · simp at h

private theorem consistent_map_negate {d : Clause ℕ}
    (hd : ¬ ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d) :
    TrailConsistent (d.map Std.Sat.Literal.negate) := by
  intro x hx hnx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨m, hm, hml⟩ := List.mem_map.1 hnx
  simp only [negate_negate] at hml
  exact hd ⟨m, hm, hml ▸ hl⟩

/-- **A RUP step translates into an accepted `rup` step**: from the negation of a tautology the
kernel conflicts at once, and otherwise it propagates the negated literals, the trail the LRAT
checker starts from. -/
private theorem rup_toPB {J : List Entry} (hJ : (J.map Entry.num).Nodup) (d : Clause ℕ)
    (hs : List ℕ) (h : CNF.propagateHints (lratPart J) (d.map Std.Sat.Literal.negate) hs = true) :
    rup (pbPart J) d.toPB (.neg :: CNF.renameHints (renPart J) hs) = true := by
  unfold rup
  simp only [rupHints, resolve]
  by_cases hd : ∃ l ∈ d, Std.Sat.Literal.negate l ∈ d
  · rw [propagate_nil_negate_toPB_of_isTautology hd]
  · obtain ⟨ρ, hρ, hset⟩ := propagate_nil_negate_toPB hd
    rw [hρ]
    exact rupHints_renameHints hJ _ _ _ _ (consistent_map_negate hd) hset h

/-- **The invariant of the translation**: from LRAT and kernel databases that hold the same
clauses under the renaming, an accepted certificate translates into steps that the kernel runs
to a database naming a contradiction at the translated conclusion. -/
private theorem check_aux : ∀ (cert : List LRAT.IntAction) (J : List Entry) (n : ℕ),
    IdOk (pbPart J) n → CNF.checkLRATAux (lratPart J) cert = true →
    ∃ D m, runSteps (pbPart J) n (CNF.toVeriPBAux (renPart J) n cert).steps = some (D, m) ∧
      namesContra D (CNF.toVeriPBAux (renPart J) n cert).conclusion = true
  | [], _, _, _, h => by simp [CNF.checkLRATAux] at h
  | .addEmpty _ hints :: _, J, n, hid, h => by
    have hJ : (J.map Entry.num).Nodup := pbPart_map_fst J ▸ hid.nodup
    simp only [CNF.checkLRATAux] at h
    have hr := rupHints_renameHints hJ (Clause.toPB []).negate hints.toList [] []
      (by simp [TrailConsistent]) (by simp) h
    refine ⟨(n, (Clause.toPB []).normalize) :: pbPart J, n + 1, ?_, ?_⟩
    · simp [CNF.toVeriPBAux, runSteps, runStep, rup, hr]
    · change namesContra ((n, (Clause.toPB []).normalize) :: pbPart J) n = true
      simp only [namesContra, lookup, List.find?, BEq.rfl, Option.map_some, Option.any_some]
      decide
  | .addRup i c hints :: rest, J, n, hid, h => by
    have hJ : (J.map Entry.num).Nodup := pbPart_map_fst J ▸ hid.nodup
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    obtain ⟨D, m, hrun, hc⟩ :=
      check_aux rest (⟨i, n, Clause.ofDIMACS c.toList⟩ :: J) (n + 1) (hid.cons le_rfl _) h2
    refine ⟨D, m, ?_, hc⟩
    simp only [CNF.toVeriPBAux, runSteps, runStep, rup_toPB hJ _ _ h1, ↓reduceIte]
    exact hrun
  | .addRat .. :: _, _, _, _, h => by simp [CNF.checkLRATAux] at h
  | .del ids :: rest, J, n, hid, h => by
    have hJ : (J.map Entry.num).Nodup := pbPart_map_fst J ▸ hid.nodup
    simp only [CNF.checkLRATAux] at h
    set J' := J.filter fun e => !ids.toList.contains e.key
    have hl : lratPart J' = (lratPart J).filter fun e => !ids.toList.contains e.1 := by
      simp [J', lratPart, List.filter_map, Function.comp_def]
    have hr : renPart J' = (renPart J).filter fun e => !ids.toList.contains e.1 := by
      simp [J', renPart, List.filter_map, Function.comp_def]
    have hdel : ((renPart J).filter fun e => ids.toList.contains e.1).map (·.2) =
        (J.filter fun e => ids.toList.contains e.key).map Entry.num := by
      simp [renPart, List.filter_map, Function.comp_def]
    have hnd : ((J.filter fun e => ids.toList.contains e.key).map Entry.num).Nodup :=
      hJ.sublist (List.filter_sublist.map _)
    have hall : ((J.filter fun e => ids.toList.contains e.key).map Entry.num).all
        (fun i => (lookup (pbPart J) i).isSome) = true := by
      refine List.all_eq_true.2 fun p hp => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      simp only [lookup, Option.isSome_map, List.find?_isSome]
      exact ⟨(e.num, e.clause.toPB.normalize),
        List.mem_map_of_mem (List.mem_of_mem_filter he), by simp⟩
    have hp : (pbPart J).filter (fun e =>
        !((J.filter fun e => ids.toList.contains e.key).map Entry.num).contains e.1) =
        pbPart J' := by
      simp only [pbPart, J', List.filter_map]
      congr 1
      refine List.filter_congr fun e he => ?_
      simp only [Function.comp_apply, List.contains_eq_mem]
      congr 1
      refine decide_eq_decide.2 ⟨fun hm => ?_, fun hk => ?_⟩
      · obtain ⟨e', he', hn⟩ := List.mem_map.1 hm
        obtain ⟨he', hk⟩ := List.mem_filter.1 he'
        obtain rfl : e' = e := List.inj_on_of_nodup_map hJ he' he hn
        simpa using hk
      · exact List.mem_map_of_mem (List.mem_filter.2 ⟨he, by simpa using hk⟩)
    have hstep : runStep (pbPart J) n
        (.del (((renPart J).filter fun e => ids.toList.contains e.1).map (·.2))) =
        some (pbPart J', n) := by
      simp only [runStep]
      rw [hdel, ite_eq_left (by simp only [hnd, hall, decide_true, Bool.and_self]), hp]
    obtain ⟨D, m, hrun, hc⟩ := check_aux rest J' n (hp ▸ hid.filter _) (hl ▸ h)
    simp only [CNF.toVeriPBAux, ← hr, runSteps, hstep]
    exact ⟨D, m, hrun, hc⟩

end VeriPB

namespace CNF

open VeriPB

/-- **LRAT certificates are VeriPB proofs**: if the LRAT checker accepts a certificate for `φ`,
the kernel checker accepts its translation for the clauses of `φ` read as pseudo-Boolean
constraints. The converse fails (see the module documentation). -/
theorem check_toVeriPB {φ : CNF ℕ} {cert : Array LRAT.IntAction} (h : φ.checkLRAT cert = true) :
    check (φ.map Clause.toPB) (φ.toVeriPB cert) = true := by
  let J : List Entry := φ.lratDB.map fun e => ⟨e.1, e.1, e.2⟩
  have hl : lratPart J = φ.lratDB := by simp [J, lratPart, Function.comp_def]
  have hr : renPart J = φ.lratDB.map fun e => (e.1, e.1) := by
    simp [J, renPart, Function.comp_def]
  have hp : pbPart J = initDb (φ.map Clause.toPB) := by
    simp [J, pbPart, initDb, lratDB, List.zipIdx_map, Function.comp_def]
  have hn : (φ.map Clause.toPB).length + 1 = φ.length + 1 := by simp
  obtain ⟨D, m, hrun, hc⟩ := check_aux cert.toList J (φ.length + 1)
    (hp ▸ hn ▸ idOk_initDb _) (hl ▸ h)
  unfold check
  rw [hn, ← hp]
  simp only [toVeriPB, ← hr, hrun, hc]

/-! ### Size and fragment -/

/-- The translation of the steps has at most one step per certificate step, and at most one hint
more than the certificate step: the `~` hint of a RUP step. -/
private theorem toVeriPBAux_size : ∀ (ren : List (ℕ × ℕ)) (n : ℕ) (cert : List LRAT.IntAction),
    (toVeriPBAux ren n cert).steps.length ≤ cert.length ∧
      VeriPB.hintCount (toVeriPBAux ren n cert).steps ≤ lratHintCount cert + cert.length
  | _, _, [] => by simp [toVeriPBAux, VeriPB.hintCount]
  | ren, n, .addEmpty _ hints :: rest => by
    have : (renameHints ren hints.toList).length ≤ hints.size :=
      (List.length_filterMap_le _ _).trans (by simp)
    simp only [toVeriPBAux, List.length_cons, List.length_nil, VeriPB.hintCount,
      VeriPB.Step.hintCount, lratHintCount]
    omega
  | ren, n, .addRup i c hints :: rest => by
    have ih := toVeriPBAux_size ((i, n) :: ren) (n + 1) rest
    have : (renameHints ren hints.toList).length ≤ hints.size :=
      (List.length_filterMap_le _ _).trans (by simp)
    simp only [toVeriPBAux, List.length_cons, VeriPB.hintCount, VeriPB.Step.hintCount,
      lratHintCount]
    omega
  | _, _, .addRat .. :: _ => by simp [toVeriPBAux, VeriPB.hintCount]
  | ren, n, .del ids :: rest => by
    have ih := toVeriPBAux_size (ren.filter fun e => !ids.toList.contains e.1) n rest
    simp only [toVeriPBAux, List.length_cons, VeriPB.hintCount, VeriPB.Step.hintCount,
      lratHintCount]
    omega

/-- **The translation has at most one step per certificate step.** -/
theorem length_toVeriPB_le (φ : CNF ℕ) (cert : Array LRAT.IntAction) :
    (φ.toVeriPB cert).steps.length ≤ cert.size := by
  simpa [toVeriPB] using (toVeriPBAux_size _ _ cert.toList).1

/-- **The translation has at most `H + S` hints**, for a certificate of `S` steps with `H` hints
(`Cslib.Logic.PL.CNF.lratHintCount`): the hints of each step, renumbered, and the `~` hint of each
RUP step. -/
theorem hintCount_toVeriPB_le (φ : CNF ℕ) (cert : Array LRAT.IntAction) :
    VeriPB.hintCount (φ.toVeriPB cert).steps ≤ lratHintCount cert.toList + cert.size := by
  simpa [toVeriPB] using (toVeriPBAux_size _ _ cert.toList).2

private theorem toVeriPBAux_fragment : ∀ (ren : List (ℕ × ℕ)) (n : ℕ)
    (cert : List LRAT.IntAction), ∀ s ∈ (toVeriPBAux ren n cert).steps,
      (∃ (d : Clause ℕ) (hs : List VeriPB.Hint), s = .rup d.toPB hs) ∨ ∃ ids, s = .del ids
  | _, _, [] => by simp [toVeriPBAux]
  | ren, n, .addEmpty _ hints :: rest => by simp [toVeriPBAux]
  | ren, n, .addRup i c hints :: rest => by
    simp only [toVeriPBAux, List.mem_cons, forall_eq_or_imp]
    exact ⟨.inl ⟨_, _, rfl⟩, toVeriPBAux_fragment _ _ rest⟩
  | _, _, .addRat .. :: _ => by simp [toVeriPBAux]
  | ren, n, .del ids :: rest => by
    simp only [toVeriPBAux, List.mem_cons, forall_eq_or_imp]
    exact ⟨.inr ⟨_, rfl⟩, toVeriPBAux_fragment _ _ rest⟩

/-- **The translation uses only `rup` steps for clauses and `del` steps**: no `pol`, `rupSearch`
or `pbc`. -/
theorem toVeriPB_fragment (φ : CNF ℕ) (cert : Array LRAT.IntAction) :
    ∀ s ∈ (φ.toVeriPB cert).steps,
      (∃ (d : Clause ℕ) (hs : List VeriPB.Hint), s = .rup d.toPB hs) ∨ ∃ ids, s = .del ids :=
  toVeriPBAux_fragment _ _ _

/-! ### Corollaries -/

/-- **The checker with redundance accepts the translation** with the conclusion `UNSAT`, for
every objective. -/
theorem checkRed_toVeriPB {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) (obj : Option VeriPB.Objective) :
    VeriPB.checkRed (φ.map Clause.toPB) obj
      ⟨(φ.toVeriPB cert).steps.map .step, .unsat (φ.toVeriPB cert).conclusion⟩ = true := by
  rw [VeriPB.checkRed_map_step]
  exact check_toVeriPB h

/-- **The kernel checker is complete for CNF**: a CNF formula has a kernel proof of `UNSAT` for
its clauses read as pseudo-Boolean constraints exactly when it is unsatisfiable. The proof is the
translation of the certificate of `Cslib.Algorithms.Lean.DPLL.solve`. -/
theorem exists_check_iff (φ : CNF ℕ) :
    (∃ P, VeriPB.check (φ.map Clause.toPB) P = true) ↔ ¬ φ.Satisfiable := by
  refine ⟨fun ⟨_, h⟩ => VeriPB.not_satisfiable_cnf_of_check h, fun h => ?_⟩
  obtain ⟨cert, hc⟩ := (Cslib.Algorithms.Lean.DPLL.exists_checkLRAT_iff φ).2 h
  exact ⟨_, check_toVeriPB hc⟩

/-- **The checker with redundance is complete for CNF**: for every objective, a CNF formula has
a proof of `UNSAT` that `Cslib.Logic.PL.VeriPB.checkRed` accepts exactly when it is
unsatisfiable. -/
theorem exists_checkRed_iff (φ : CNF ℕ) (obj : Option VeriPB.Objective) :
    (∃ (P : VeriPB.RedProof) (q : ℕ), P.conclusion = .unsat q ∧
      VeriPB.checkRed (φ.map Clause.toPB) obj P = true) ↔ ¬ φ.Satisfiable := by
  refine ⟨fun ⟨_, _, hq, h⟩ => VeriPB.not_satisfiable_cnf_of_checkRed h hq, fun h => ?_⟩
  obtain ⟨cert, hc⟩ := (Cslib.Algorithms.Lean.DPLL.exists_checkLRAT_iff φ).2 h
  exact ⟨_, _, rfl, checkRed_toVeriPB hc obj⟩

end CNF

end Cslib.Logic.PL
