/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-!
# A VeriPB kernel-proof checker: output sections

The output section of a VeriPB proof [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023] states a relation between the input instance and
an *output formula*, which must be the core set at the end of the proof (§4.2 of the
VeriPB/CakePB documentation, 22 June 2026 edition). It certifies preprocessing and
reformulation: the output formula can be handed on to the next stage of the solving process.
The section is `output g FILE;`, the output formula being a separate OPB file, or
`output g IMPLICIT;`, the output being the core set itself (`Cslib.Logic.PL.VeriPB.OutputSection`).
The guarantees `g` (`Cslib.Logic.PL.VeriPB.Guarantee`) are:
* `DERIVABLE`: if the input is satisfiable, so is the output;
* `EQUISATISFIABLE`: the input is satisfiable exactly when the output is;
* `EQUIOPTIMAL`: below the bound `b` of the best certifying logged solution, the input has a
  solution of value at most `v` exactly when the output does, so the two have the same optimum
  unless the proof logged an optimal solution;
* `EQUIENUMERABLE`: below that bound, the solutions of value at most `v` of the input and of the
  output have the same projections to the preserved set.

**The check** (`Cslib.Logic.PL.VeriPB.checkOutput`) is CakePB's `check_output`
(`npbc_checkScript.sml`, CakeML commit `14856fcf`). The output formula and the core set must be
the same set of constraints, up to normalization and the order of terms (for `DERIVABLE`, the
output must only lie in the core set). `DERIVABLE` and `EQUISATISFIABLE` need no logged solution
and no `obji` step, that is, `dbound` unset; `EQUISATISFIABLE`, `EQUIOPTIMAL` and
`EQUIENUMERABLE` need no unchecked deletion (`chk`), and the last two need `bound` at most
`dbound`. `EQUIOPTIMAL` needs the output objective to agree with the final objective on every
assignment (CakePB's `eq_obj`); `EQUIENUMERABLE` needs the same, or no objective on either side,
and the same preserved set, as a set of variables. CakePB supports only `FILE`. VeriPB 3.0.2
differs from CakePB and from this checker: it rejects `EQUISATISFIABLE` under an objective, a
`DERIVABLE` output that omits a core constraint, and `EQUIENUMERABLE` after any logged solution,
and it accepts `DERIVABLE` and `EQUISATISFIABLE` after a logged solution. Without a `preserved:`
line, VeriPB 3.0.2 treats every variable as preserved, so it rejects `EQUIENUMERABLE` after a
witness on any variable; CakePB and this checker reject `EQUIENUMERABLE` without a preserved set
in any case.

**Soundness** (`Cslib.Logic.PL.VeriPB.semOutput_of_checkRedOutput`) is CakePB's
`check_csteps_check_output` against its semantics `sem_output` (`npbcScript.sml`), with the
injections of its invariant `bimp_pres_obj` the identity on projections, because the preserved
set does not change and witnesses leave it alone. So `EQUIENUMERABLE` gives an equality of the
projected solution sets, a stronger form of the bijection of `sem_output`. The proof combines the
invariants of the checker (`Cslib.Logic.PL.VeriPB.invariants_of_runTop`):
* forward, the projected lower-bound invariant (`Cslib.Logic.PL.VeriPB.ReachesOn`): below
  `dbound`, every solution of the input has the projection of a solution of the database, hence
  of the core set, with no larger value;
* backward, the core invariant (`Cslib.Logic.PL.VeriPB.Inv`): while `chk` holds, every solution of
  the core set has the projection of a solution of the input with no larger value.

The bound `b` returned with the output is that of CakePB, and it is at least the value of some
solution of the input (`Cslib.Logic.PL.VeriPB.exists_le_of_checkRedOutput`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Instance`: instances, the input and the output formula.
* `Cslib.Logic.PL.VeriPB.Guarantee`, `Cslib.Logic.PL.VeriPB.semOutput`: the output guarantees and
  their meaning.
* `Cslib.Logic.PL.VeriPB.checkOutput`, `Cslib.Logic.PL.VeriPB.checkRedOutput`: the check of an
  output section, and the checker of proofs with one.

## Main results

* `Cslib.Logic.PL.VeriPB.semOutput_of_checkRedOutput`: soundness of the output section.
* `Cslib.Logic.PL.VeriPB.projections_eq_of_semOutput`,
  `Cslib.Logic.PL.VeriPB.projections_eq_of_checkRedOutput`: with an infinite bound (no logged
  solution), `EQUIENUMERABLE` preserves the projected solutions, hence their number.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB

open PBConstr

/-- An instance: its constraints, its objective to minimize, if any, and its preserved set, if
any (§3 and §5.8.3 of the documentation). It is the input of a proof, and the formula of an
output section (§4.2). -/
structure Instance where
  /-- The constraints. -/
  constraints : List PBConstr
  /-- The objective to minimize. -/
  objective : Option Objective
  /-- The preserved set of a projected enumeration. -/
  preserved : Option (List ℕ) := none
  deriving DecidableEq, Repr

namespace Instance

/-- The instance has a solution. -/
def Satisfiable (I : Instance) : Prop := ∃ σ, ∀ c ∈ I.constraints, c.Holds σ

/-- The solutions of the instance with objective value at most `v`. -/
def solsLE (I : Instance) (v : ℤ) : Set (ℕ → Bool) :=
  {σ | (∀ c ∈ I.constraints, c.Holds σ) ∧ objValue I.objective σ ≤ v}

end Instance

/-- An output guarantee (§4.2), other than `NONE`. CakePB calls `EQUIENUMERABLE`
`Equisolvable`. -/
inductive Guarantee where
  /-- `DERIVABLE`. -/
  | derivable
  /-- `EQUISATISFIABLE`. -/
  | equisatisfiable
  /-- `EQUIOPTIMAL`. -/
  | equioptimal
  /-- `EQUIENUMERABLE`. -/
  | equienumerable
  deriving DecidableEq, Repr

/-- **The meaning of an output guarantee** between the input `I` and the output `O`, for the
bound `b` (`none` for infinite), as CakePB's `sem_output` (`npbcScript.sml`, CakeML commit
`14856fcf`). For `EQUIENUMERABLE` the two instances have the same preserved set, as a set of
variables, and the projections to it of their solutions of value at most `v` are the same set; in
`sem_output` they are in bijection. -/
def semOutput (I : Instance) (b : Option ℤ) (O : Instance) : Guarantee → Prop
  | .derivable => I.Satisfiable → O.Satisfiable
  | .equisatisfiable => I.Satisfiable ↔ O.Satisfiable
  | .equioptimal => ∀ v, (∀ u ∈ b, v < u) → ((I.solsLE v).Nonempty ↔ (O.solsLE v).Nonempty)
  | .equienumerable => ∃ P Q, I.preserved = some P ∧ O.preserved = some Q ∧ (∀ x, x ∈ P ↔ x ∈ Q) ∧
      ∀ v, (∀ u ∈ b, v < u) → proj P '' I.solsLE v = proj P '' O.solsLE v

/-- Every constraint of `ds` is one of `cs`, up to normalization and the order of terms. -/
def includes (cs ds : List PBConstr) : Bool :=
  ds.all fun d => cs.any fun c => sameUpToOrder c.normalize d.normalize

/-- `cs` and `ds` are the same set of constraints, up to normalization and the order of terms. -/
def sameConstrs (cs ds : List PBConstr) : Bool := includes cs ds && includes ds cs

/-- The constraints of the core set. -/
def State.coreConstrs (s : State) : List PBConstr := s.core.map (·.2)

/-- The bound `bound` is at most `dbound`, if `dbound` is set. -/
def State.boundLe (s : State) : Bool := s.dbound.all fun d => s.bound.any (· ≤ d)

/-- Two objectives agree on every assignment: each bounds the other trivially after
normalization (CakePB's `eq_obj`). -/
def Objective.equiv (f g : Objective) : Bool :=
  (f.geGoal g).normalize.degree == 0 && (g.geGoal f).normalize.degree == 0

/-- Two optional objectives agree on every assignment, or neither is given. -/
def objEquiv : Option Objective → Option Objective → Bool
  | some f, some g => f.equiv g
  | none, none => true
  | _, _ => false

/-- **The check of an output section** with guarantee `g` and output formula `O` in the final
state `s` (§4.2), as CakePB's `check_output` (`npbc_checkScript.sml`, CakeML commit `14856fcf`).
* `DERIVABLE`: `dbound` is unset and every constraint of `O` is in the core set.
* `EQUISATISFIABLE`: `dbound` and `bound` are unset, `chk` holds, and `O` and the core set are
  the same set of constraints.
* `EQUIOPTIMAL`: `chk` holds, `bound` is at most `dbound`, `O` and the core set are the same set,
  and the objective of `O` agrees with the final objective.
* `EQUIENUMERABLE`: as `EQUIOPTIMAL`, or with no objective on either side, and the preserved set
  of `O` is that of the state, as a set of variables.

Constraints are compared up to normalization and the order of terms. -/
def checkOutput (s : State) (O : Instance) : Guarantee → Bool
  | .derivable => s.dbound.isNone && includes s.coreConstrs O.constraints
  | .equisatisfiable =>
    s.dbound.isNone && s.bound.isNone && s.chk && sameConstrs s.coreConstrs O.constraints
  | .equioptimal =>
    s.chk && s.boundLe && sameConstrs s.coreConstrs O.constraints && s.obj.isSome &&
      objEquiv s.obj O.objective
  | .equienumerable =>
    s.chk && s.boundLe && sameConstrs s.coreConstrs O.constraints &&
      objEquiv s.obj O.objective &&
      match s.pres, O.preserved with
      | some P, some Q => P.all Q.contains && Q.all P.contains
      | _, _ => false

/-- An output section `output g FILE;` with the output formula `file`, or `output g IMPLICIT;`
with `file = none` (§4.2). -/
structure OutputSection where
  /-- The guarantee. -/
  guarantee : Guarantee
  /-- The output formula of `FILE`; `none` for `IMPLICIT`, whose output is the core set. -/
  file : Option Instance
  deriving DecidableEq, Repr

/-- The output of an accepted proof: its guarantee, the output formula and the bound `bound`
(CakePB's `bound`, `none` for infinite) below which `EQUIOPTIMAL` and `EQUIENUMERABLE` hold. -/
structure Output where
  /-- The guarantee. -/
  guarantee : Guarantee
  /-- The output formula. -/
  formula : Instance
  /-- The bound. -/
  bound : Option ℤ
  deriving DecidableEq, Repr

/-- **The checker of a proof with an output section** for the formula `F`, the objective `obj`
and the preserved set `pres`: run the steps, check the conclusion and the output section, and
return the output. For `IMPLICIT`, the output formula is the core set, with the final objective
and the preserved set. -/
def checkRedOutput (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ)) (sec : OutputSection) : Option Output :=
  match runTop F obj (State.init F obj pres) P.steps with
  | some s =>
    let O := sec.file.getD ⟨s.coreConstrs, s.obj, s.pres⟩
    if checkConclusion F obj s P.conclusion && checkOutput s O sec.guarantee then
      some ⟨sec.guarantee, O, s.bound⟩
    else none
  | none => none

/-! ### Soundness -/

theorem holds_of_includes {σ : ℕ → Bool} {cs ds : List PBConstr} (h : includes cs ds = true)
    (hc : ∀ c ∈ cs, c.Holds σ) : ∀ d ∈ ds, d.Holds σ := by
  intro d hd
  simp only [includes, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨c, hcs, heq⟩ := h d hd
  rw [← holds_normalize]
  exact Holds.of_sameUpToOrder ((holds_normalize σ c).2 (hc c hcs)) heq

theorem Objective.eval_eq_of_equiv {f g : Objective} (h : f.equiv g = true) (σ : ℕ → Bool) :
    f.eval σ = g.eval σ := by
  simp only [Objective.equiv, Bool.and_eq_true, beq_iff_eq] at h
  have h1 := (Objective.holds_geGoal σ f g).1 (holds_of_normalize_degree_eq_zero h.1)
  have h2 := (Objective.holds_geGoal σ g f).1 (holds_of_normalize_degree_eq_zero h.2)
  omega

theorem objValue_eq_of_objEquiv {f g : Option Objective} (h : objEquiv f g = true)
    (σ : ℕ → Bool) : objValue g σ = objValue f σ := by
  cases f <;> cases g <;> simp only [objEquiv, Bool.false_eq_true] at h
  · rfl
  · exact (Objective.eval_eq_of_equiv h σ).symm

/-- A value below the bound `b` is below `d` when `b` is at most `d`. -/
private theorem lt_of_le_bound {b d : Option ℤ} (hle : (d.all fun d => b.any (· ≤ d)) = true)
    {v w : ℤ} (hv : ∀ u ∈ b, v < u) (hw : w ≤ v) : ∀ x ∈ d, w < x := by
  intro x hx
  simp only [Option.all_eq_true, Option.any_eq_true, decide_eq_true_eq] at hle
  obtain ⟨u, hu, hux⟩ := hle x hx
  exact (hw.trans_lt (hv u hu)).trans_le hux

/-- What an accepted proof with an output section gives: the final state, its invariants, the
accepted conclusion and output section, and the output it returns. -/
private theorem of_checkRedOutput {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {pres : Option (List ℕ)} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P pres sec = some o) :
    ∃ s, runTop F obj (State.init F obj pres) P.steps = some s ∧
      checkConclusion F obj s P.conclusion = true ∧ checkOutput s o.formula o.guarantee = true ∧
      o.guarantee = sec.guarantee ∧ o.formula = sec.file.getD ⟨s.coreConstrs, s.obj, s.pres⟩ ∧
      o.bound = s.bound := by
  unfold checkRedOutput at h
  split at h
  · rename_i s hrun
    dsimp only at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hok
      exact ⟨s, hrun, hok.1, hok.2, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- **A proof with an accepted output section is accepted**, with its conclusion. -/
theorem checkRed_of_checkRedOutput {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {pres : Option (List ℕ)} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P pres sec = some o) : checkRed F obj P pres = true := by
  obtain ⟨s, hrun, hc, -⟩ := of_checkRedOutput h
  simp [checkRed, hrun, hc]

/-- The output of an accepted proof has the guarantee of its section, and for `FILE` its formula
is the one given. -/
theorem output_of_checkRedOutput {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {pres : Option (List ℕ)} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P pres sec = some o) :
    o.guarantee = sec.guarantee ∧ ∀ O ∈ sec.file, o.formula = O := by
  obtain ⟨s, -, -, -, hg, hO, -⟩ := of_checkRedOutput h
  refine ⟨hg, fun O hO' => ?_⟩
  rw [hO, Option.mem_def.1 hO']
  rfl

/-- **The bound of an output is reached**: it is at least the value of some solution of the
input. -/
theorem exists_le_of_checkRedOutput {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {pres : Option (List ℕ)} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P pres sec = some o) :
    ∀ u ∈ o.bound, ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ objValue obj σ ≤ u := by
  obtain ⟨s, hrun, -, -, -, -, hb⟩ := of_checkRedOutput h
  rw [hb]
  exact (invariants_of_runTop hrun).1.wit

/-- **Soundness of the output section**: if the checker accepts a proof with an output section
for the formula `F`, the objective `obj` and the preserved set `pres`, the guarantee of the
section holds between the input instance and the output formula, for the returned bound, as in
CakePB's `check_csteps_check_output`. -/
theorem semOutput_of_checkRedOutput {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {pres : Option (List ℕ)} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P pres sec = some o) :
    semOutput ⟨F, obj, pres⟩ o.bound o.formula o.guarantee := by
  obtain ⟨s, hrun, -, hout, -, -, hb⟩ := of_checkRedOutput h
  obtain ⟨hinv, he, hσ⟩ := invariants_of_runTop hrun
  rcases o with ⟨g, O, b⟩
  simp only at hout hb ⊢
  subst hb
  have hcore : ∀ τ, AllHold τ s.core ↔ ∀ c ∈ s.coreConstrs, c.Holds τ := fun τ => by
    rw [State.coreConstrs, List.forall_mem_map]
    rfl
  -- Forward: below `dbound`, a solution of the input gives one of the core set with the same
  -- projection to the preserved set and no larger value.
  have fwd : ∀ σ, (∀ c ∈ F, c.Holds σ) → (∀ d ∈ s.dbound, objValue obj σ < d) →
      ∃ τ, AllHold τ s.core ∧ objValue s.obj τ ≤ objValue obj σ ∧
        proj (pres.getD []) τ = proj (pres.getD []) σ :=
    fun σ hF hd => by
      rcases (hσ σ hF).2 with ⟨τ, hτ, hw, hp⟩ | ⟨d, hd', hw⟩
      · exact ⟨τ, fun e he => hτ e (hinv.sub e he), hw, hp⟩
      · exact absurd (hd d hd') (not_lt.2 hw)
  cases g with
  | derivable =>
    simp only [checkOutput, Bool.and_eq_true, Option.isNone_iff_eq_none] at hout
    rintro ⟨σ, hF⟩
    obtain ⟨τ, hτ, -⟩ := fwd σ hF (by simp [hout.1])
    exact ⟨τ, holds_of_includes hout.2 ((hcore τ).1 hτ)⟩
  | equisatisfiable =>
    simp only [checkOutput, sameConstrs, Bool.and_eq_true, Option.isNone_iff_eq_none] at hout
    obtain ⟨⟨⟨hd, -⟩, hchk⟩, hsub, hsup⟩ := hout
    constructor
    · rintro ⟨σ, hF⟩
      obtain ⟨τ, hτ, -⟩ := fwd σ hF (by simp [hd])
      exact ⟨τ, holds_of_includes hsub ((hcore τ).1 hτ)⟩
    · rintro ⟨τ, hO⟩
      obtain ⟨σ, hF, -⟩ := hinv.chk hchk τ ((hcore τ).2 (holds_of_includes hsup hO))
      exact ⟨σ, hF⟩
  | equioptimal =>
    simp only [checkOutput, sameConstrs, State.boundLe, Bool.and_eq_true] at hout
    obtain ⟨⟨⟨⟨hchk, hle⟩, hsub, hsup⟩, -⟩, hobj⟩ := hout
    intro v hv
    constructor
    · rintro ⟨σ, hF, hσv⟩
      obtain ⟨τ, hτ, hw, -⟩ := fwd σ hF (lt_of_le_bound hle hv hσv)
      exact ⟨τ, holds_of_includes hsub ((hcore τ).1 hτ),
        by rw [objValue_eq_of_objEquiv hobj]; exact hw.trans hσv⟩
    · rintro ⟨τ, hO, hτv⟩
      obtain ⟨σ, hF, hw, -⟩ := hinv.chk hchk τ ((hcore τ).2 (holds_of_includes hsup hO))
      exact ⟨σ, hF, hw.trans (by rw [← objValue_eq_of_objEquiv hobj]; exact hτv)⟩
  | equienumerable =>
    simp only [checkOutput, sameConstrs, State.boundLe, Bool.and_eq_true] at hout
    obtain ⟨⟨⟨⟨hchk, hle⟩, hsub, hsup⟩, hobj⟩, hpres⟩ := hout
    obtain ⟨Pr, hPr⟩ : ∃ Pr, s.pres = some Pr := by
      cases hp : s.pres with
      | none => simp [hp] at hpres
      | some Pr => exact ⟨Pr, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, O.preserved = some Q := by
      cases hq : O.preserved with
      | none => simp [hq] at hpres
      | some Q => exact ⟨Q, rfl⟩
    rw [hPr, hQ] at hpres
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hpres
    have hpres0 : pres = some Pr := he.pres_eq ▸ hPr
    refine ⟨Pr, Q, hpres0, hQ, fun x => ⟨hpres.1 x, hpres.2 x⟩, fun v hv => ?_⟩
    ext l
    constructor
    · rintro ⟨σ, ⟨hF, hσv⟩, rfl⟩
      obtain ⟨τ, hτ, hw, hp⟩ := fwd σ hF (lt_of_le_bound hle hv hσv)
      rw [hpres0] at hp
      exact ⟨τ, ⟨holds_of_includes hsub ((hcore τ).1 hτ),
        by rw [objValue_eq_of_objEquiv hobj]; exact hw.trans hσv⟩, hp⟩
    · rintro ⟨τ, ⟨hO, hτv⟩, rfl⟩
      obtain ⟨σ, hF, hw, hp⟩ := hinv.chk hchk τ ((hcore τ).2 (holds_of_includes hsup hO))
      exact ⟨σ, ⟨hF, hw.trans (by rw [← objValue_eq_of_objEquiv hobj]; exact hτv)⟩, hp Pr hPr⟩

/-- The solutions of an instance, of every value, project onto all its projected solutions. -/
private theorem iUnion_image_solsLE (I : Instance) (P : List ℕ) :
    ⋃ v : ℤ, proj P '' I.solsLE v = projections I.constraints P := by
  ext l
  simp only [Set.mem_iUnion, Set.mem_image, Instance.solsLE, Set.mem_ofPred_eq, projections]
  constructor
  · rintro ⟨v, σ, ⟨hσ, -⟩, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨objValue I.objective σ, σ, ⟨hσ, le_rfl⟩, rfl⟩

/-- **`EQUIENUMERABLE` with an infinite bound** preserves the projected solutions: if it holds
between the instances `I` and `O` for the bound `none`, and `I` has the preserved set `Pres`,
then the solutions of `I` and of `O` have the same projections to `Pres`, hence equally many,
whatever their objectives. -/
theorem projections_eq_of_semOutput {I O : Instance} {Pres : List ℕ}
    (hI : I.preserved = some Pres) (h : semOutput I none O .equienumerable) :
    projections I.constraints Pres = projections O.constraints Pres := by
  obtain ⟨P', -, hP', -, -, heq⟩ := h
  cases (Option.some.inj (hI.symm.trans hP') : Pres = P')
  rw [← iUnion_image_solsLE, ← iUnion_image_solsLE]
  exact Set.iUnion_congr fun v => heq v (by simp)

/-- **`EQUIENUMERABLE` from the checker**: if the checker accepts a proof with an `EQUIENUMERABLE`
output section for the formula `F` with the preserved set `Pres`, and the bound is infinite (no
solution was logged), then the solutions of `F` and of the output formula have the same
projections to `Pres`, hence equally many. -/
theorem projections_eq_of_checkRedOutput {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} {Pres : List ℕ} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P (some Pres) sec = some o) (hg : o.guarantee = .equienumerable)
    (hb : o.bound = none) : projections F Pres = projections o.formula.constraints Pres := by
  have hsem := semOutput_of_checkRedOutput h
  rw [hg, hb] at hsem
  exact projections_eq_of_semOutput (I := ⟨F, obj, some Pres⟩) rfl hsem

end Cslib.Logic.PL.VeriPB

end
