/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.OfLRAT
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast

/-! # Clausal VeriPB proofs are LRAT certificates

A VeriPB kernel proof [Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023]
for a CNF formula, read as the pseudo-Boolean constraints `Cslib.Logic.PL.Clause.toPB` of its
clauses, whose steps are *clausal* (`Cslib.Logic.PL.VeriPB.Step.isClausal`), translates back into
an LRAT certificate [Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017] that
`Cslib.Logic.PL.CNF.checkLRAT` accepts (`Cslib.Logic.PL.VeriPB.checkLRAT_toLRAT`). A step is
clausal when it is a deletion or a `rup` step whose constraint normalizes to degree at most `1`.
That is how clauses are recognized up to `Cslib.Logic.PL.PBConstr.normalize`: a normalized
constraint has positive coefficients on distinct variables, so of degree `1` it is the clause of
its literals, whatever its coefficients, and of degree `0` it holds everywhere. Every clause
normalizes to degree at most `1` (`Cslib.Logic.PL.Clause.degree_normalize_toPB_le`), so the
translation of LRAT into VeriPB lands in this fragment.

The back-translation `Cslib.Logic.PL.VeriPB.toLRAT` keeps the kernel numbers as certificate
numbers, so it renumbers nothing. A `rup` step of degree `1` becomes a RUP step for its clause; a
`rup` step of degree `0` is dropped, since its constraint propagates nothing; a deletion stays a
deletion, which LRAT reads the same way. The proof ends with an empty-clause step whose single hint
is the conclusion: a contradiction among clauses is the empty clause. The hints of a RUP step are
read along the LRAT database from the negated clause (`Cslib.Logic.PL.VeriPB.lratHints`): the `~`
hint is dropped, hints that leave two literals of their clause on the current LRAT trail are
dropped, unit hints are kept, and the hints stop at the first falsified clause.

**Why this is correct.** On a clause, pseudo-Boolean propagation is unit propagation
(`Cslib.Logic.PL.VeriPB.propagate_eq_unitStep`, `Cslib.Logic.PL.VeriPB.propagate_toPB`). The LRAT
trail contains the negated clause from the start, while the kernel's trail gains it only at the
`~` hint, so the LRAT trail always contains the kernel's. More literals assumed true keep a
falsified clause falsified and a unit clause unit or falsified
(`Cslib.Logic.PL.Clause.residual_mono`), so the LRAT propagation conflicts no later than the
kernel's. The LRAT trail stays consistent, since the clause of a normalized constraint has no
complementary literals, so the `~` hint never conflicts in the kernel.

**Size.** The certificate has at most one step and one hint more than the proof
(`Cslib.Logic.PL.VeriPB.size_toLRAT_le`, `Cslib.Logic.PL.VeriPB.lratHintCount_toLRAT_le`), for
the final empty-clause step. With the embedding `Cslib.Logic.PL.CNF.toVeriPB`, LRAT and the
clausal `rup`/`del` fragment of the kernel format simulate each other with linear overhead in
steps and hints (`Cslib.Logic.PL.VeriPB.exists_clausal_check_of_checkLRAT`,
`Cslib.Logic.PL.VeriPB.exists_checkLRAT_of_clausal_check`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Step.isClausal`: the clausal fragment.
* `Cslib.Logic.PL.VeriPB.lratHints`: the LRAT hints of a kernel RUP step.
* `Cslib.Logic.PL.VeriPB.toLRAT`: the back-translation.

## Main results

* `Cslib.Logic.PL.Clause.residual_mono`: the residual of a clause is monotone in the trail.
* `Cslib.Logic.PL.VeriPB.checkLRAT_toLRAT`: an accepted clausal kernel proof translates into an
  accepted LRAT certificate.
* `Cslib.Logic.PL.VeriPB.size_toLRAT_le`, `Cslib.Logic.PL.VeriPB.lratHintCount_toLRAT_le`: the
  size bounds.
* `Cslib.Logic.PL.VeriPB.exists_clausal_check_of_checkLRAT`,
  `Cslib.Logic.PL.VeriPB.exists_checkLRAT_of_clausal_check`: the polynomial equivalence.

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

/-- **More literals assumed true keep a residual empty, and keep a unit residual unit or make it
empty.** -/
theorem Clause.residual_mono {c : Clause ℕ} {t t' : List (Literal ℕ)} (h : ∀ l ∈ t, l ∈ t') :
    (c.residual t = .empty → c.residual t' = .empty) ∧
      ∀ l, c.residual t = .unit l → c.residual t' = .empty ∨ c.residual t' = .unit l := by
  refine ⟨fun he => ?_, fun l hu => ?_⟩
  · exact residual_eq_empty_iff.2 fun m hm => h _ (residual_eq_empty_iff.1 he m hm)
  · obtain ⟨-, -, hall⟩ := residual_eq_unit_iff.1 hu
    exact residual_of_forall_ne fun m hm hne => h _ (hall m hm hne)

namespace VeriPB

/-- **A clausal step**: a `rup` step whose constraint normalizes to degree at most `1`, or a
deletion. A normalized constraint has positive coefficients on distinct variables, so one of
degree `1` is the clause of its literals, and one of degree `0` holds everywhere. -/
def Step.isClausal : Step → Bool
  | .rup c _ => decide (c.normalize.degree ≤ 1)
  | .del _ => true
  | _ => false

/-- The clause of a constraint: the literals of its normal form. -/
def clauseOf (c : PBConstr) : Clause ℕ := c.normalize.terms.map (·.2)

/-- **The LRAT hints of a kernel RUP step**, read along the LRAT database `L` from the trail `t`:
the `~` hint is dropped, since the LRAT checker starts from the negated clause; a hint naming no
clause of `L` is dropped, as is a hint whose clause has two literals left; a unit hint is kept,
and its literal joins the trail; and the hints stop at the first falsified clause. -/
def lratHints (L : List (ℕ × Clause ℕ)) : List (Literal ℕ) → List Hint → List ℕ
  | _, [] => []
  | t, .neg :: hs => lratHints L t hs
  | t, .id p :: hs =>
    match L.lookup p with
    | none => lratHints L t hs
    | some d =>
      match d.residual t with
      | .empty => [p]
      | .unit l => p :: lratHints L (l :: t) hs
      | .other => lratHints L t hs

/-- **The back-translation of kernel steps** into LRAT steps, from the LRAT database `L` and the
next kernel number `n`, with the contradiction `q` named by the conclusion. Certificate numbers are
kernel numbers, so no renaming is needed.
* A `rup` step for a constraint of degree `1` becomes a RUP step for its clause, numbered `n`, with
  the hints `Cslib.Logic.PL.VeriPB.lratHints`. A `rup` step for a constraint of degree `0` derives
  a constraint that holds everywhere and propagates nothing; it is dropped, and so are hints
  naming it.
* A deletion is the same deletion: LRAT ignores numbers that name no clause.
* At the end, an empty-clause step with the single hint `q`. -/
def toLRATAux (q : ℕ) : List (ℕ × Clause ℕ) → ℕ → List Step → List LRAT.IntAction
  | _, n, [] => [.addEmpty n #[q]]
  | L, n, .rup c hs :: ss =>
    if c.normalize.degree = 1 then
      .addRup n (clauseOf c).toDIMACS
          (lratHints L ((clauseOf c).map Std.Sat.Literal.negate) hs).toArray ::
        toLRATAux q ((n, clauseOf c) :: L) (n + 1) ss
    else toLRATAux q L (n + 1) ss
  | L, n, .del ids :: ss =>
    .del ids.toArray :: toLRATAux q (L.filter fun e => !ids.contains e.1) n ss
  | _, _, _ :: _ => []

/-- **A clausal kernel proof as an LRAT certificate** for `φ`, whose clauses keep their numbers
`1, 2, …` (`Cslib.Logic.PL.VeriPB.toLRATAux`). -/
def toLRAT (φ : CNF ℕ) (P : Proof) : Array LRAT.IntAction :=
  (toLRATAux P.conclusion φ.lratDB (φ.length + 1) P.steps).toArray

/-! ### Correctness -/

/-- A constraint of the kernel database with its clause in the LRAT database, if any. -/
private structure Ent where
  /-- The kernel number, also the certificate number. -/
  num : ℕ
  /-- The constraint. -/
  constr : PBConstr
  /-- The clause, or none for a constraint that propagates nothing. -/
  clause : Option (Clause ℕ)

private def pbPart (J : List Ent) : List (ℕ × PBConstr) := J.map fun e => (e.num, e.constr)

private def lratPart (J : List Ent) : List (ℕ × Clause ℕ) :=
  J.filterMap fun e => e.clause.map (e.num, ·)

/-- **The constraint agrees with its clause**: on every consistent trail, propagating the
constraint is unit propagation of the clause, or does nothing when there is no clause. -/
private def Agrees (e : Ent) : Prop :=
  ∀ ρ, TrailConsistent ρ → propagate ρ e.constr = e.clause.elim (some ρ) (·.unitStep ρ)

private theorem pbPart_map_fst (J : List Ent) : (pbPart J).map (·.1) = J.map Ent.num := by
  simp [pbPart, Function.comp_def]

private theorem lookup_lratPart_eq_none {J : List Ent} {p : ℕ} (h : p ∉ J.map Ent.num) :
    (lratPart J).lookup p = none := by
  induction J with
  | nil => rfl
  | cons e J ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (p == e.num) = false := by simpa using h.1
    cases hc : e.clause with
    | none => simpa [lratPart, hc] using ih h.2
    | some d =>
      simp only [lratPart, hc, List.filterMap_cons, Option.map_some, List.lookup_cons, hne]
      exact ih h.2

private theorem lookup_lratPart_cons {e : Ent} {J : List Ent} {p : ℕ} (hp : p ≠ e.num) :
    (lratPart (e :: J)).lookup p = (lratPart J).lookup p := by
  have hne : (p == e.num) = false := by simpa using hp
  cases hc : e.clause with
  | none => simp [lratPart, hc]
  | some d => simp only [lratPart, hc, List.filterMap_cons, Option.map_some, List.lookup_cons, hne]

private theorem lookup_pbPart {J : List Ent} (hJ : (J.map Ent.num).Nodup) {p : ℕ}
    {N : PBConstr} (h : lookup (pbPart J) p = some N) :
    ∃ e ∈ J, e.constr = N ∧ (lratPart J).lookup p = e.clause := by
  induction J with
  | nil => simp [lookup, pbPart] at h
  | cons e J ih =>
    simp only [List.map_cons, List.nodup_cons] at hJ
    by_cases hp : e.num = p
    · subst hp
      simp only [lookup, pbPart, List.map_cons, List.find?_cons, BEq.rfl, Option.map_some,
        Option.some.injEq] at h
      refine ⟨e, List.mem_cons_self, h, ?_⟩
      cases hc : e.clause with
      | none => simpa [lratPart, hc] using lookup_lratPart_eq_none hJ.1
      | some d => simp [lratPart, hc]
    · have hne : (e.num == p) = false := by simpa using hp
      have h' : lookup (pbPart J) p = some N := by
        simpa [lookup, pbPart, List.find?_cons, hne] using h
      obtain ⟨e', he', hc, hl⟩ := ih hJ.2 h'
      exact ⟨e', List.mem_cons_of_mem _ he', hc, (lookup_lratPart_cons (Ne.symm hp)).trans hl⟩

/-- What a propagation adds to the trail comes from the constraint. -/
private theorem mem_of_propagate {ρ ρ' : List (Literal ℕ)} {c : PBConstr}
    (h : propagate ρ c = some ρ') {l : Literal ℕ} (hl : l ∈ ρ') :
    l ∈ ρ ∨ l ∈ c.terms.map (·.2) := by
  unfold propagate at h
  split at h
  · cases h
  · cases h
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
      exact .inr (List.mem_map_of_mem (List.mem_of_mem_filter ht))
    · exact .inl hl

/-- **The kernel hints propagate as their LRAT hints do**, from an LRAT trail `t` that contains
the kernel trail and the negated clause `t₀`; the negation `neg` of the clause never conflicts on
such a trail and adds only literals of `t`. -/
private theorem propagateHints_lratHints {J : List Ent} (hJ : (J.map Ent.num).Nodup)
    (hA : ∀ e ∈ J, Agrees e) {neg : PBConstr} {t₀ : List (Literal ℕ)}
    (hneg : ∀ ρ t, TrailConsistent t → (∀ l ∈ t₀, l ∈ t) → (∀ l ∈ ρ, l ∈ t) →
      ∃ ρ', propagate ρ neg = some ρ' ∧ ∀ l ∈ ρ', l ∈ t) :
    ∀ (hs : List Hint) (t ρ : List (Literal ℕ)), TrailConsistent t → (∀ l ∈ t₀, l ∈ t) →
      (∀ l ∈ ρ, l ∈ t) → rupHints (pbPart J) neg hs ρ = true →
      CNF.propagateHints (lratPart J) t (lratHints (lratPart J) t hs) = true
  | [], _, _, _, _, _, h => by simp [rupHints] at h
  | .neg :: hs, t, ρ, ht, h₀, hρ, h => by
    obtain ⟨ρ', hp, hρ'⟩ := hneg ρ t ht h₀ hρ
    simp only [rupHints, resolve, hp] at h
    exact propagateHints_lratHints hJ hA hneg hs t ρ' ht h₀ hρ' h
  | .id p :: hs, t, ρ, ht, h₀, hρ, h => by
    have hρc : TrailConsistent ρ := fun l hl hn => ht l (hρ l hl) (hρ _ hn)
    simp only [rupHints, resolve] at h
    rcases hN : lookup (pbPart J) p with _ | N
    · simp [hN] at h
    obtain ⟨e, he, rfl, hl⟩ := lookup_pbPart hJ hN
    simp only [hN, hA e he ρ hρc] at h
    rcases hc : e.clause with _ | d
    · -- no clause: the kernel propagates nothing, and the hint is dropped
      simp only [hc, Option.elim_none] at h
      simp only [lratHints, hl, hc]
      exact propagateHints_lratHints hJ hA hneg hs t ρ ht h₀ hρ h
    simp only [hc, Option.elim_some] at h
    rw [hc] at hl
    have hmono := Clause.residual_mono (c := d) hρ
    -- the LRAT step decides; the kernel step is used only to continue
    rcases hr : d.residual t with _ | l | _
    · simp only [lratHints, hl, hr]
      simp [CNF.propagateHints, CNF.propagateWith, hl, hr]
    · obtain ⟨-, hlt, -⟩ := Clause.residual_eq_unit_iff.1 hr
      have hcont : CNF.propagateHints (lratPart J) (l :: t)
          (lratHints (lratPart J) (l :: t) hs) = true := by
        unfold Clause.unitStep at h
        rcases hρr : d.residual ρ with _ | l' | _ <;> simp only [hρr] at h
        · simp [hmono.1 hρr] at hr
        · have hl' : l' = l := by
            rcases hmono.2 l' hρr with h' | h' <;> rw [hr] at h'
            · cases h'
            · exact (Clause.Residual.unit.inj h').symm
          subst hl'
          refine propagateHints_lratHints hJ hA hneg hs (l' :: t) _ (ht.cons hlt)
            (fun m hm => List.mem_cons_of_mem _ (h₀ m hm)) (fun m hm => ?_) h
          split at hm
          · exact List.mem_cons_of_mem _ (hρ m hm)
          · rcases List.mem_cons.1 hm with rfl | hm
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hρ m hm)
        · exact propagateHints_lratHints hJ hA hneg hs (l :: t) ρ (ht.cons hlt)
            (fun m hm => List.mem_cons_of_mem _ (h₀ m hm))
            (fun m hm => List.mem_cons_of_mem _ (hρ m hm)) h
      simpa [lratHints, hl, hr, CNF.propagateHints, CNF.propagateWith] using hcont
    · have hcont : CNF.propagateHints (lratPart J) t (lratHints (lratPart J) t hs) = true := by
        unfold Clause.unitStep at h
        rcases hρr : d.residual ρ with _ | l' | _ <;> simp only [hρr] at h
        · simp [hmono.1 hρr] at hr
        · rcases hmono.2 l' hρr with h' | h' <;> rw [hr] at h' <;> cases h'
        · exact propagateHints_lratHints hJ hA hneg hs t ρ ht h₀ hρ h
      simpa [lratHints, hl, hr] using hcont

/-- **The negation of a constraint of degree `1`** never conflicts on a consistent trail that
contains the negation of its clause, and adds only literals of that trail. -/
private theorem negate_ok {c : PBConstr} (hd : c.normalize.degree = 1) (ρ t : List (Literal ℕ))
    (ht : TrailConsistent t) (h₀ : ∀ l ∈ (clauseOf c).map Std.Sat.Literal.negate, l ∈ t)
    (hρ : ∀ l ∈ ρ, l ∈ t) : ∃ ρ', propagate ρ c.negate = some ρ' ∧ ∀ l ∈ ρ', l ∈ t := by
  have hmem : ∀ y ∈ c.normalize.terms, Std.Sat.Literal.negate y.2 ∈ t := fun y hy =>
    h₀ _ (List.mem_map_of_mem (List.mem_map_of_mem hy))
  have hnf : (c.negate.terms.filter fun x => !falsified ρ x) = c.negate.terms := by
    refine List.filter_eq_self.2 fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [falsified, negate_negate, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun hyρ => ht _ (hρ _ hyρ) (hmem y hy)
  have hs : ¬ slack ρ c.negate < 0 := by
    unfold slack
    rw [hnf]
    simp only [negate, hd, coeffSum, List.map_map, Function.comp_def]
    omega
  obtain ⟨ρ', hp⟩ : ∃ ρ', propagate ρ c.negate = some ρ' :=
    ⟨_, by unfold propagate; rw [ite_eq_right hs]⟩
  refine ⟨ρ', hp, fun l hl => ?_⟩
  rcases mem_of_propagate hp hl with hl | hl
  · exact hρ l hl
  · simp only [negate, List.map_map, Function.comp_def, List.mem_map] at hl
    obtain ⟨y, hy, rfl⟩ := hl
    exact hmem y hy

/-- The negated clause of a normalized constraint is a consistent trail: its variables are
distinct. -/
private theorem consistent_clauseOf (c : PBConstr) :
    TrailConsistent ((clauseOf c).map Std.Sat.Literal.negate) := by
  intro x hx hnx
  simp only [clauseOf, List.map_map, Function.comp_def, List.mem_map] at hx hnx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, hzy⟩ := hnx
  simp only [negate_negate] at hzy
  have hvar : termVar z = termVar y := by
    obtain ⟨a, v, b⟩ := y
    obtain ⟨a', v', b'⟩ := z
    simp only [Std.Sat.Literal.negate, Prod.mk.injEq] at hzy
    simp [hzy.1]
  obtain rfl := List.inj_on_of_nodup_map (nodup_termVar_normalize c) hz hy hvar
  obtain ⟨a, v, b⟩ := z
  cases b <;> simp [Std.Sat.Literal.negate] at hzy

private theorem lratPart_filter (J : List Ent) (p : ℕ → Bool) :
    lratPart (J.filter fun e => p e.num) = (lratPart J).filter fun e => p e.1 := by
  induction J with
  | nil => rfl
  | cons e J ih =>
    simp only [lratPart] at ih ⊢
    cases hc : e.clause <;> by_cases hp : p e.num = true <;> simp [hp, hc, ih]

/-- **The invariant of the back-translation**: from kernel and LRAT databases that agree, a
clausal run of kernel steps ending at a database that names the contradiction `q` translates into
LRAT steps that the LRAT checker accepts. -/
private theorem checkLRAT_aux (q : ℕ) : ∀ (ss : List Step) (J : List Ent) (n : ℕ)
    (D : List (ℕ × PBConstr)) (m : ℕ), IdOk (pbPart J) n → (∀ e ∈ J, Agrees e) →
    ss.all Step.isClausal = true → runSteps (pbPart J) n ss = some (D, m) →
    namesContra D q = true → CNF.checkLRATAux (lratPart J) (toLRATAux q (lratPart J) n ss) = true
  | [], J, n, D, m, hid, hA, _, hrun, hq => by
    have hJ : (J.map Ent.num).Nodup := pbPart_map_fst J ▸ hid.nodup
    simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, -⟩ := hrun
    obtain ⟨N, hN, hcon⟩ := (Option.any_eq_true _ _).1 hq
    obtain ⟨e, he, rfl, hl⟩ := lookup_pbPart hJ hN
    have hagree := hA e he [] (by simp [TrailConsistent])
    have hnone : propagate [] e.constr = none := by
      have : slack [] e.constr < 0 := by
        have := of_decide_eq_true hcon
        unfold IsContradiction at this
        simp only [slack, falsified, List.contains_nil, Bool.not_false, List.filter_true]
        omega
      simp [propagate, this]
    rw [hnone] at hagree
    cases hc : e.clause with
    | none => simp [hc] at hagree
    | some d =>
      simp only [hc, Option.elim_some, Clause.unitStep] at hagree
      have hr : d.residual [] = .empty := by revert hagree; cases d.residual [] <;> simp
      rw [hc] at hl
      simp [toLRATAux, CNF.checkLRATAux, CNF.propagateHints, CNF.propagateWith, hl, hr]
  | .rup c hs :: ss, J, n, D, m, hid, hA, hcl, hrun, hq => by
    have hJ : (J.map Ent.num).Nodup := pbPart_map_fst J ▸ hid.nodup
    simp only [List.all_cons, Bool.and_eq_true, Step.isClausal, decide_eq_true_eq] at hcl
    obtain ⟨hdeg, hcl⟩ := hcl
    simp only [runSteps, runStep] at hrun
    by_cases hr : rup (pbPart J) c hs = true
    swap
    · simp [hr] at hrun
    simp only [hr, ↓reduceIte] at hrun
    by_cases h1 : c.normalize.degree = 1
    · have hA' : ∀ e ∈ (⟨n, c.normalize, some (clauseOf c)⟩ :: J : List Ent), Agrees e := by
        refine List.forall_mem_cons.2 ⟨fun ρ _ => ?_, hA⟩
        exact propagate_eq_unitStep (nodup_termVar_normalize c)
          (fun _ ht => pos_of_mem_normalize ht) h1 ρ
      have hprop := propagateHints_lratHints hJ hA (negate_ok h1) hs _ [] (consistent_clauseOf c)
        (fun _ h => h) (by simp) hr
      simp only [toLRATAux, h1, ↓reduceIte, CNF.checkLRATAux, Clause.ofDIMACS_toDIMACS,
        hprop, Bool.true_and]
      exact checkLRAT_aux q ss (⟨n, c.normalize, some (clauseOf c)⟩ :: J) (n + 1) D m
        (hid.cons le_rfl _) hA' hcl hrun hq
    · have h0 : c.normalize.degree = 0 := by omega
      have hA' : ∀ e ∈ (⟨n, c.normalize, none⟩ :: J : List Ent), Agrees e :=
        List.forall_mem_cons.2 ⟨fun ρ _ => propagate_of_degree_eq_zero h0 ρ, hA⟩
      simp only [toLRATAux, h1, ↓reduceIte]
      exact checkLRAT_aux q ss (⟨n, c.normalize, none⟩ :: J) (n + 1) D m
        (hid.cons le_rfl _) hA' hcl hrun hq
  | .del ids :: ss, J, n, D, m, hid, hA, hcl, hrun, hq => by
    simp only [List.all_cons, Bool.and_eq_true, Step.isClausal, true_and] at hcl
    simp only [runSteps, runStep] at hrun
    by_cases hc : (decide ids.Nodup && ids.all fun i => (lookup (pbPart J) i).isSome) = true
    swap
    · simp [hc] at hrun
    simp only [hc, ↓reduceIte] at hrun
    have hp : pbPart (J.filter fun e => !ids.contains e.num) =
        (pbPart J).filter fun e => !ids.contains e.1 := by
      simp [pbPart, List.filter_map, Function.comp_def]
    have ih := checkLRAT_aux q ss _ n D m (hp ▸ hid.filter _)
      (fun e he => hA e (List.mem_of_mem_filter he)) hcl (hp ▸ hrun) hq
    simp only [toLRATAux, CNF.checkLRATAux]
    rw [← lratPart_filter J (fun i => !ids.contains i)]
    exact ih
  | .pol _ :: _, _, _, _, _, _, _, hcl, _, _ => by simp [Step.isClausal] at hcl
  | .rupSearch _ :: _, _, _, _, _, _, _, hcl, _, _ => by simp [Step.isClausal] at hcl
  | .pbc .. :: _, _, _, _, _, _, _, hcl, _, _ => by simp [Step.isClausal] at hcl

/-- **Clausal VeriPB proofs are LRAT certificates**: if the kernel checker accepts a proof for the
clauses of `φ` read as pseudo-Boolean constraints, and its steps are clausal `rup` steps and
deletions, the LRAT checker accepts its back-translation. -/
theorem checkLRAT_toLRAT {φ : CNF ℕ} {P : Proof} (hP : P.steps.all Step.isClausal = true)
    (h : check (φ.map Clause.toPB) P = true) : φ.checkLRAT (toLRAT φ P) = true := by
  let J : List Ent := φ.lratDB.map fun e => ⟨e.1, e.2.toPB.normalize, some e.2⟩
  have hl : lratPart J = φ.lratDB := by simp [J, lratPart, List.filterMap_map]
  have hp : pbPart J = initDb (φ.map Clause.toPB) := by
    simp [J, pbPart, initDb, CNF.lratDB, List.zipIdx_map, Function.comp_def]
  have hA : ∀ e ∈ J, Agrees e := fun _ he => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
    exact fun ρ hρ => propagate_toPB x.2 hρ
  have hn : (φ.map Clause.toPB).length + 1 = φ.length + 1 := by simp
  unfold check at h
  rw [hn] at h
  split at h
  · rename_i D m hrun
    unfold CNF.checkLRAT toLRAT
    rw [List.toList_toArray, ← hl]
    exact checkLRAT_aux _ _ J _ D m (hp ▸ hn ▸ idOk_initDb _) hA hP (hp ▸ hrun) h
  · cases h

/-! ### Size -/

private theorem length_lratHints_le (L : List (ℕ × Clause ℕ)) :
    ∀ (t : List (Literal ℕ)) (hs : List Hint), (lratHints L t hs).length ≤ hs.length
  | _, [] => le_rfl
  | t, .neg :: hs => (length_lratHints_le L t hs).trans (Nat.le_succ _)
  | t, .id p :: hs => by
    simp only [lratHints]
    split
    · exact (length_lratHints_le L t hs).trans (Nat.le_succ _)
    · split
      · simp
      · simpa using length_lratHints_le L _ hs
      · exact (length_lratHints_le L t hs).trans (Nat.le_succ _)

private theorem toLRATAux_size (q : ℕ) : ∀ (L : List (ℕ × Clause ℕ)) (n : ℕ) (ss : List Step),
    (toLRATAux q L n ss).length ≤ ss.length + 1 ∧
      CNF.lratHintCount (toLRATAux q L n ss) ≤ hintCount ss + 1
  | _, _, [] => by simp [toLRATAux, CNF.lratHintCount]
  | L, n, .rup c hs :: ss => by
    simp only [toLRATAux]
    split
    · have ih := toLRATAux_size q ((n, clauseOf c) :: L) (n + 1) ss
      have := length_lratHints_le L ((clauseOf c).map Std.Sat.Literal.negate) hs
      simp only [List.length_cons, CNF.lratHintCount, List.size_toArray, hintCount,
        Step.hintCount]
      omega
    · have ih := toLRATAux_size q L (n + 1) ss
      simp only [List.length_cons, hintCount, Step.hintCount]
      omega
  | L, n, .del ids :: ss => by
    have ih := toLRATAux_size q (L.filter fun e => !ids.contains e.1) n ss
    simp only [toLRATAux, List.length_cons, CNF.lratHintCount, hintCount, Step.hintCount]
    omega
  | _, _, .pol _ :: _ => by simp [toLRATAux, CNF.lratHintCount]
  | _, _, .rupSearch _ :: _ => by simp [toLRATAux, CNF.lratHintCount]
  | _, _, .pbc .. :: _ => by simp [toLRATAux, CNF.lratHintCount]

/-- **The back-translation has at most one step more than the proof**: the empty-clause step for
the conclusion. -/
theorem size_toLRAT_le (φ : CNF ℕ) (P : Proof) : (toLRAT φ P).size ≤ P.steps.length + 1 := by
  simpa [toLRAT] using (toLRATAux_size P.conclusion φ.lratDB (φ.length + 1) P.steps).1

/-- **The back-translation has at most one hint more than the proof**: the hint of the
empty-clause step. -/
theorem lratHintCount_toLRAT_le (φ : CNF ℕ) (P : Proof) :
    CNF.lratHintCount (toLRAT φ P).toList ≤ hintCount P.steps + 1 := by
  simpa [toLRAT] using (toLRATAux_size P.conclusion φ.lratDB (φ.length + 1) P.steps).2

/-! ### Polynomial equivalence -/

/-- **Clausal kernel proofs simulate LRAT**: an accepted LRAT certificate of `S` steps and `H`
hints gives an accepted clausal kernel proof of at most `S` steps and `H + S` hints
(`Cslib.Logic.PL.CNF.toVeriPB`). -/
theorem exists_clausal_check_of_checkLRAT {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) :
    ∃ P : Proof, check (φ.map Clause.toPB) P = true ∧ P.steps.all Step.isClausal = true ∧
      P.steps.length ≤ cert.size ∧
        hintCount P.steps ≤ CNF.lratHintCount cert.toList + cert.size := by
  refine ⟨φ.toVeriPB cert, CNF.check_toVeriPB h, List.all_eq_true.2 fun s hs => ?_,
    CNF.length_toVeriPB_le φ cert, CNF.hintCount_toVeriPB_le φ cert⟩
  rcases CNF.toVeriPB_fragment φ cert s hs with ⟨d, hs, rfl⟩ | ⟨ids, rfl⟩
  · simpa [Step.isClausal] using Clause.degree_normalize_toPB_le d
  · rfl

/-- **LRAT simulates clausal kernel proofs**: an accepted clausal kernel proof of `S` steps and
`H` hints gives an accepted LRAT certificate of at most `S + 1` steps and `H + 1` hints
(`Cslib.Logic.PL.VeriPB.toLRAT`). With
`Cslib.Logic.PL.VeriPB.exists_clausal_check_of_checkLRAT`, LRAT and the clausal `rup`/`del`
fragment of the kernel format polynomially, indeed linearly, simulate each other, size counting
steps and hints. -/
theorem exists_checkLRAT_of_clausal_check {φ : CNF ℕ} {P : Proof}
    (hP : P.steps.all Step.isClausal = true) (h : check (φ.map Clause.toPB) P = true) :
    ∃ cert : Array LRAT.IntAction, φ.checkLRAT cert = true ∧ cert.size ≤ P.steps.length + 1 ∧
      CNF.lratHintCount cert.toList ≤ hintCount P.steps + 1 :=
  ⟨toLRAT φ P, checkLRAT_toLRAT hP h, size_toLRAT_le φ P, lratHintCount_toLRAT_le φ P⟩

end VeriPB

end Cslib.Logic.PL
