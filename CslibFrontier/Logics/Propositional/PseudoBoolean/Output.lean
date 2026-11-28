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
* `EQUIENUMERABLE`: below that bound, the projections of the solutions of value at most `v` of
  the input, to its preserved set, are in bijection with those of the output, to the output's
  preserved set.

**The check** (`Cslib.Logic.PL.VeriPB.checkOutput`) is CakePB's `check_output`
(`npbc_checkScript.sml`, CakeML commit `14856fcf`). The output formula and the core set must be
the same set of constraints, up to normalization and the order of terms (for `DERIVABLE`, the
output must only lie in the core set). `DERIVABLE` and `EQUISATISFIABLE` need no logged solution
and no `obji` step, that is, `dbound` unset; `EQUISATISFIABLE`, `EQUIOPTIMAL` and
`EQUIENUMERABLE` need no unchecked deletion (`chk`), and the last two need `bound` at most
`dbound`. `EQUIOPTIMAL` needs the output objective to agree with the final objective on every
assignment (CakePB's `eq_obj`); `EQUIENUMERABLE` needs the same, or no objective on either side,
and the output's preserved set to be the final one, as a set of variables, also after
`preserved_add` and `preserved_rm` (§5.10), as in VeriPB 3.0.2 and CakePB. CakePB supports only
`FILE`. VeriPB 3.0.2 differs from CakePB and from this checker: it rejects `EQUISATISFIABLE`
under an objective, a `DERIVABLE` output that omits a core constraint, and `EQUIENUMERABLE` after
any logged solution, and it accepts `DERIVABLE` and `EQUISATISFIABLE` after a logged solution.
Without a `preserved:` line, VeriPB 3.0.2 treats every variable as preserved, so it rejects
`EQUIENUMERABLE` after a witness on any variable; CakePB and this checker reject
`EQUIENUMERABLE` without a preserved set in any case.

**Soundness** (`Cslib.Logic.PL.VeriPB.semOutput_of_checkRedOutput`) is CakePB's
`check_csteps_check_output` against its semantics `sem_output` (`npbcScript.sml`). It rests on
the counting injections of the checker (`Cslib.Logic.PL.VeriPB.InjInv`, CakePB's
`bimp_pres_obj`), after every run (`Cslib.Logic.PL.VeriPB.invariants_of_runTop`):
* forward, below `dbound`, the projections of the solutions of the input inject into those of the
  solutions of the database, hence of the core set, of no larger value;
* backward, while `chk` holds, the projections of the solutions of the core set inject into
  those of the input, of no larger value.

The existence halves give `DERIVABLE`, `EQUISATISFIABLE` and `EQUIOPTIMAL`. For `EQUIENUMERABLE`
the output is the core set, and its preserved set the final one, so the two injections give a
bijection by Schröder–Bernstein, as CakePB's `BIJ_INJ_INJ` does. The injections map projections
to the input's preserved set to projections to the final one, which may differ after
`preserved_add` and `preserved_rm`, so the guarantee is a bijection, as in `sem_output`, and not
an equality: removing a variable, redefining it and adding it back keeps the preserved set but
may permute the projections. Without a change of the preserved set the injections are the
identity on projections, and the projected solution sets are equal
(`Cslib.Logic.PL.VeriPB.projections_eq_of_checkRedOutput`).

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
* `Cslib.Logic.PL.VeriPB.exists_bijOn_projections_of_semOutput`,
  `Cslib.Logic.PL.VeriPB.exists_bijOn_projections_of_checkRedOutput`: with an infinite bound (no
  logged solution), `EQUIENUMERABLE` puts the projected solutions in bijection, hence keeps their
  number.
* `Cslib.Logic.PL.VeriPB.projections_eq_of_checkRedOutput`: without a change of the preserved
  set, it preserves the projected solutions.

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
`14856fcf`). For `EQUIENUMERABLE` both instances have a preserved set, `P` and `Q`, and below the
bound the projections to `P` of the solutions of `I` of value at most `v` are in bijection with
the projections to `Q` of those of `O`. The two sets of variables may differ, after
`preserved_add` and `preserved_rm` (§5.10), and even when they agree the bijection need not be
the identity, since a variable removed and added back may be redefined in between. -/
def semOutput (I : Instance) (b : Option ℤ) (O : Instance) : Guarantee → Prop
  | .derivable => I.Satisfiable → O.Satisfiable
  | .equisatisfiable => I.Satisfiable ↔ O.Satisfiable
  | .equioptimal => ∀ v, (∀ u ∈ b, v < u) → ((I.solsLE v).Nonempty ↔ (O.solsLE v).Nonempty)
  | .equienumerable => ∃ P Q, I.preserved = some P ∧ O.preserved = some Q ∧
      ∀ v, (∀ u ∈ b, v < u) → ∃ f, Set.BijOn f (proj P '' I.solsLE v) (proj Q '' O.solsLE v)

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
  of `O` is that of the state, as a set of variables (`Cslib.Logic.PL.VeriPB.sameVars`), whether
  or not `preserved_add` and `preserved_rm` (§5.10) have changed it, as in CakePB and VeriPB.

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
      | some P, some Q => sameVars P Q
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
    split at h <;> cases h
    rename_i hok
    simp only [Bool.and_eq_true] at hok
    exact ⟨s, hrun, hok.1, hok.2, rfl, rfl, rfl⟩
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

/-- **Schröder–Bernstein for sets**: injections of `A` into `B` and of `B` into `A` give a
bijection between them. -/
private theorem exists_bijOn_of_injOn {α β : Type*} [Nonempty β] {A : Set α} {B : Set β}
    {f : α → β} {g : β → α} (hf : Set.InjOn f A) (hfm : Set.MapsTo f A B) (hg : Set.InjOn g B)
    (hgm : Set.MapsTo g B A) : ∃ h, Set.BijOn h A B := by
  classical
  obtain ⟨h, hh⟩ := Function.Embedding.schroeder_bernstein
    (f := fun a : A => (⟨f a, hfm a.property⟩ : B)) (g := fun b : B => (⟨g b, hgm b.property⟩ : A))
    (fun a b hab => Subtype.ext (hf a.property b.property (congrArg Subtype.val hab)))
    (fun a b hab => Subtype.ext (hg a.property b.property (congrArg Subtype.val hab)))
  refine ⟨fun a => if ha : a ∈ A then (h ⟨a, ha⟩ : β) else Classical.arbitrary β,
    fun a ha => by simp only [ha, ↓reduceDIte]; exact (h ⟨a, ha⟩).property,
    fun a ha b hb hab => congrArg Subtype.val (hh.1 (Subtype.ext (by
      simpa only [ha, hb, ↓reduceDIte] using hab))),
    fun b hb => ?_⟩
  obtain ⟨⟨a, ha⟩, hab⟩ := hh.2 ⟨b, hb⟩
  exact ⟨a, ha, by simp only [ha, ↓reduceDIte, hab]⟩

/-- **The injections behind `EQUIENUMERABLE`**: if the final state `s` of a run from the formula
`F`, the objective `obj` and the preserved set `pres` accepts an `EQUIENUMERABLE` output `O`,
then `pres`, the preserved set `Q` of `O` and the final preserved set are set, the last two being
the same set of variables, and below the bound `bound` the counting injections
(`Cslib.Logic.PL.VeriPB.InjInv`) give injections both ways between the projections to `pres` of
the solutions of the input and those to `Q` of the solutions of `O`, of value at most `v`.
While the preserved set is unchanged, the two sets of projections, to `pres`, are equal. -/
private theorem equienumerable_injections {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {s : State} {O : Instance} (hinv : Inv F obj s)
    (he : InjInv F obj pres s) (hout : checkOutput s O .equienumerable = true) :
    ∃ P Q, pres = some P ∧ O.preserved = some Q ∧ ∀ v, (∀ u ∈ s.bound, v < u) →
      (∃ f, Set.InjOn f (proj P '' Instance.solsLE ⟨F, obj, pres⟩ v) ∧
        Set.MapsTo f (proj P '' Instance.solsLE ⟨F, obj, pres⟩ v) (proj Q '' O.solsLE v)) ∧
      (∃ g, Set.InjOn g (proj Q '' O.solsLE v) ∧
        Set.MapsTo g (proj Q '' O.solsLE v) (proj P '' Instance.solsLE ⟨F, obj, pres⟩ v)) ∧
      (s.presChanged = false →
        proj P '' Instance.solsLE ⟨F, obj, pres⟩ v = proj P '' O.solsLE v) := by
  simp only [checkOutput, sameConstrs, State.boundLe, Bool.and_eq_true] at hout
  obtain ⟨⟨⟨⟨hchk, hle⟩, hsub, hsup⟩, hobj⟩, hpres⟩ := hout
  obtain ⟨Pr, Q, hPr, hQ, hpres⟩ : ∃ Pr Q, s.pres = some Pr ∧ O.preserved = some Q ∧
      sameVars Pr Q = true := by
    cases hp : s.pres <;> cases hq : O.preserved <;>
      simp only [hp, hq, Bool.false_eq_true] at hpres
    exact ⟨_, _, rfl, rfl, hpres⟩
  replace hpres := sameVars_iff.1 hpres
  obtain ⟨P, hP⟩ : ∃ P, pres = some P :=
    Option.isSome_iff_exists.1 (he.pres_some ▸ by simp [hPr])
  have hPr' : s.pres.getD [] = Pr := by rw [hPr]; rfl
  have hP' : pres.getD [] = P := by rw [hP]; rfl
  have hcore : ∀ τ, AllHold τ s.core ↔ ∀ c ∈ s.coreConstrs, c.Holds τ :=
    fun _ => List.forall_mem_map.symm
  -- The projections to `Pr` and to `Q` determine each other everywhere.
  obtain ⟨φ, -, -, hφ⟩ := exists_proj_injOn (A := Set.univ) (P := Pr) (Q := Q) fun a _ b _ => by
    simp only [proj_eq_iff]
    exact ⟨fun h x hx => h x ((hpres x).2 hx), fun h x hx => h x ((hpres x).1 hx)⟩
  obtain ⟨ψ, -, -, hψ⟩ := exists_proj_injOn (A := Set.univ) (P := Q) (Q := Pr) fun a _ b _ => by
    simp only [proj_eq_iff]
    exact ⟨fun h x hx => h x ((hpres x).1 hx), fun h x hx => h x ((hpres x).2 hx)⟩
  -- The solutions of the database are solutions of `O`, and those of `O` of the core set.
  have hdbO : ∀ v τ, AllHold τ s.db ∧ objValue s.obj τ ≤ v → τ ∈ O.solsLE v :=
    fun v τ ⟨hτ, hv⟩ => ⟨holds_of_includes hsub ((hcore τ).1 fun e he => hτ e (hinv.sub e he)),
      by rw [objValue_eq_of_objEquiv hobj]; exact hv⟩
  have hOcore : ∀ v τ, τ ∈ O.solsLE v →
      τ ∈ {τ | s.chk = true ∧ AllHold τ s.core ∧ objValue s.obj τ ≤ v} :=
    fun v τ ⟨hτ, hv⟩ => ⟨hchk, (hcore τ).2 (holds_of_includes hsup hτ),
      by rw [← objValue_eq_of_objEquiv hobj]; exact hv⟩
  refine ⟨P, Q, hP, hQ, fun v hv => ?_⟩
  obtain ⟨f, hfi, hfm, hfid⟩ := he.fwd v (.inl (lt_of_le_bound hle hv le_rfl))
  obtain ⟨g, hgi, hgm, hgid⟩ := he.bwd v
  rw [hP'] at hfi hfm hfid hgm
  -- Below the bound, the forward injection lands in the solutions of the database.
  have hf : ∀ l ∈ proj P '' Instance.solsLE ⟨F, obj, pres⟩ v, ∃ τ, (AllHold τ s.db ∧
      objValue s.obj τ ≤ v) ∧ f l = .inl (proj Pr τ) := by
    intro l hl
    rcases hfm hl with ⟨_, ⟨τ, hτ, rfl⟩, hfl⟩ | ⟨k, ⟨-, d, hd, hdv⟩, -⟩
    · exact ⟨τ, hτ, by rw [← hfl, hPr']⟩
    · exact absurd (lt_of_le_bound hle hv le_rfl d hd) (not_lt.2 hdv)
  have hO : ∀ m ∈ proj Q '' O.solsLE v, ∃ τ, τ ∈ O.solsLE v ∧ m = proj Q τ ∧
      Sum.inl (proj Pr τ) ∈ s.bwdSource v := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact ⟨τ, hτ, rfl, .inl ⟨_, ⟨τ, hOcore v τ hτ, by rw [hPr']⟩, rfl⟩⟩
  refine ⟨⟨fun l => φ (Sum.elim id (fun _ => []) (f l)), ?_, ?_⟩,
    ⟨fun m => g (.inl (ψ m)), ?_, ?_⟩, fun hpc => ?_⟩
  · intro l₁ h₁ l₂ h₂ h12
    obtain ⟨τ₁, -, hf₁⟩ := hf l₁ h₁
    obtain ⟨τ₂, -, hf₂⟩ := hf l₂ h₂
    simp only [hf₁, hf₂, Sum.elim_inl, id, hφ _ (Set.mem_univ _), proj_eq_iff] at h12
    refine hfi h₁ h₂ ?_
    rw [hf₁, hf₂, Sum.inl.injEq, proj_eq_iff]
    exact fun x hx => h12 x ((hpres x).1 hx)
  · intro l hl
    obtain ⟨τ, hτ, hfl⟩ := hf l hl
    simp only [hfl, Sum.elim_inl, id, hφ τ trivial]
    exact ⟨τ, hdbO v τ hτ, rfl⟩
  · rintro _ h₁ _ h₂ h12
    obtain ⟨τ₁, -, rfl, hs₁⟩ := hO _ h₁
    obtain ⟨τ₂, -, rfl, hs₂⟩ := hO _ h₂
    simp only [hψ _ trivial] at h12
    have := hgi hs₁ hs₂ h12
    simp only [Sum.inl.injEq, proj_eq_iff] at this ⊢
    exact fun x hx => this x ((hpres x).2 hx)
  · intro m hm
    obtain ⟨τ, -, rfl, hs⟩ := hO m hm
    simp only [hψ _ trivial]
    exact hgm hs
  · have hPP : Pr = P := Option.some.inj (hPr.symm.trans ((he.pres_eq hpc).trans hP))
    subst hPP
    ext l
    refine ⟨fun hl => ?_, ?_⟩
    · obtain ⟨τ, hτ, hfl⟩ := hf l hl
      rw [← hfid hpc l hl _ hfl]
      exact ⟨τ, hdbO v τ hτ, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      have hs : Sum.inl (proj Pr τ) ∈ s.bwdSource v :=
        .inl ⟨_, ⟨τ, hOcore v τ hτ, by rw [hPr']⟩, rfl⟩
      rw [← hgid hpc _ hs]
      exact hgm hs

/-- **Soundness of the output section**: if the checker accepts a proof with an output section
for the formula `F`, the objective `obj` and the preserved set `pres`, the guarantee of the
section holds between the input instance and the output formula, for the returned bound, as in
CakePB's `check_csteps_check_output`. Everything follows from the counting injections
(`Cslib.Logic.PL.VeriPB.InjInv`): their existence halves for `DERIVABLE`, `EQUISATISFIABLE` and
`EQUIOPTIMAL`, and for `EQUIENUMERABLE` the injections themselves, which give a bijection by
Schröder–Bernstein, as CakePB's `BIJ_INJ_INJ`. -/
theorem semOutput_of_checkRedOutput {F : List PBConstr} {obj : Option Objective} {P : RedProof}
    {pres : Option (List ℕ)} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P pres sec = some o) :
    semOutput ⟨F, obj, pres⟩ o.bound o.formula o.guarantee := by
  obtain ⟨s, hrun, -, hout, -, -, hb⟩ := of_checkRedOutput h
  obtain ⟨hinv, he⟩ := invariants_of_runTop hrun
  rcases o with ⟨g, O, b⟩
  simp only at hout hb ⊢
  subst hb
  have hcore : ∀ τ, AllHold τ s.core ↔ ∀ c ∈ s.coreConstrs, c.Holds τ :=
    fun _ => List.forall_mem_map.symm
  -- Forward: below `dbound`, a solution of the input gives one of the core set with no larger
  -- value.
  have fwd : ∀ σ, (∀ c ∈ F, c.Holds σ) → (∀ d ∈ s.dbound, objValue obj σ < d) →
      ∃ τ, AllHold τ s.core ∧ objValue s.obj τ ≤ objValue obj σ :=
    fun σ hF hd => by
      rcases he.reaches hF with ⟨τ, hτ, hw⟩ | ⟨d, hd', hw⟩
      · exact ⟨τ, fun e he => hτ e (hinv.sub e he), hw⟩
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
      exact (he.exists_of_core hchk ((hcore τ).2 (holds_of_includes hsup hO))).imp fun _ h => h.1
  | equioptimal =>
    simp only [checkOutput, sameConstrs, State.boundLe, Bool.and_eq_true] at hout
    obtain ⟨⟨⟨⟨hchk, hle⟩, hsub, hsup⟩, -⟩, hobj⟩ := hout
    intro v hv
    constructor
    · rintro ⟨σ, hF, hσv⟩
      obtain ⟨τ, hτ, hw⟩ := fwd σ hF (lt_of_le_bound hle hv hσv)
      exact ⟨τ, holds_of_includes hsub ((hcore τ).1 hτ),
        by rw [objValue_eq_of_objEquiv hobj]; exact hw.trans hσv⟩
    · rintro ⟨τ, hO, hτv⟩
      obtain ⟨σ, hF, hw⟩ := he.exists_of_core hchk ((hcore τ).2 (holds_of_includes hsup hO))
      exact ⟨σ, hF, hw.trans (by rw [← objValue_eq_of_objEquiv hobj]; exact hτv)⟩
  | equienumerable =>
    obtain ⟨P, Q, hP, hQ, hinj⟩ := equienumerable_injections hinv he hout
    refine ⟨P, Q, hP, hQ, fun v hv => ?_⟩
    obtain ⟨⟨f, hfi, hfm⟩, ⟨g, hgi, hgm⟩, -⟩ := hinj v hv
    exact exists_bijOn_of_injOn hfi hfm hgi hgm

/-- Every solution has value at most the sum of the positive weights of the objective and its
constant. -/
private theorem objValue_le (obj : Option Objective) (σ : ℕ → Bool) :
    objValue obj σ ≤ obj.elim 0 fun f => (posMass f.lin : ℤ) + f.const := by
  cases obj with
  | none => exact le_rfl
  | some f =>
    simp only [objValue, Objective.eval, Option.elim]
    have := linVal_le_posMass σ f.lin
    omega

/-- With a bound above every value, the projected solutions of value at most it are all of
them. -/
private theorem image_solsLE_eq (I : Instance) (P : List ℕ) {v : ℤ}
    (hv : (I.objective.elim 0 fun f => (posMass f.lin : ℤ) + f.const) ≤ v) :
    proj P '' I.solsLE v = projections I.constraints P := by
  ext l
  simp only [Set.mem_image, Instance.solsLE, Set.mem_ofPred_eq, projections]
  exact ⟨fun ⟨σ, ⟨hσ, _⟩, h⟩ => ⟨σ, hσ, h⟩,
    fun ⟨σ, hσ, h⟩ => ⟨σ, ⟨hσ, (objValue_le _ σ).trans hv⟩, h⟩⟩

/-- **`EQUIENUMERABLE` with an infinite bound** puts the projected solutions in bijection: if it
holds between the instances `I` and `O` for the bound `none`, with the preserved sets `P` and `Q`,
then the projections to `P` of the solutions of `I` are in bijection with those to `Q` of the
solutions of `O`, whatever their objectives, so there are equally many. -/
theorem exists_bijOn_projections_of_semOutput {I O : Instance} {P Q : List ℕ}
    (hI : I.preserved = some P) (hO : O.preserved = some Q)
    (h : semOutput I none O .equienumerable) :
    ∃ f, Set.BijOn f (projections I.constraints P) (projections O.constraints Q) := by
  obtain ⟨P', Q', hP', hQ', hbij⟩ := h
  cases (Option.some.inj (hI.symm.trans hP') : P = P')
  cases (Option.some.inj (hO.symm.trans hQ') : Q = Q')
  obtain ⟨f, hf⟩ := hbij (max (I.objective.elim 0 fun f => (posMass f.lin : ℤ) + f.const)
    (O.objective.elim 0 fun f => (posMass f.lin : ℤ) + f.const)) (by simp)
  rw [image_solsLE_eq I P (le_max_left _ _), image_solsLE_eq O Q (le_max_right _ _)] at hf
  exact ⟨f, hf⟩

/-- **`EQUIENUMERABLE` from the checker**: if the checker accepts a proof with an `EQUIENUMERABLE`
output section for the formula `F` with the preserved set `Pres`, and the bound is infinite (no
solution was logged), then the output formula has a preserved set `Q`, and the projections to
`Pres` of the solutions of `F` are in bijection with those to `Q` of the solutions of the output
formula, hence equally many, even after changes of the preserved set. -/
theorem exists_bijOn_projections_of_checkRedOutput {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} {Pres : List ℕ} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P (some Pres) sec = some o) (hg : o.guarantee = .equienumerable)
    (hb : o.bound = none) : ∃ Q, o.formula.preserved = some Q ∧
      ∃ f, Set.BijOn f (projections F Pres) (projections o.formula.constraints Q) := by
  have hsem := semOutput_of_checkRedOutput h
  rw [hg, hb] at hsem
  obtain ⟨P', Q, -, hQ, -⟩ := id hsem
  exact ⟨Q, hQ, exists_bijOn_projections_of_semOutput (I := ⟨F, obj, some Pres⟩) rfl hQ hsem⟩

/-- **`EQUIENUMERABLE` without a change of the preserved set**: if, moreover, no step of the proof
is `preserved_add` or `preserved_rm`, then the solutions of `F` and of the output formula have
the same projections to `Pres`. -/
theorem projections_eq_of_checkRedOutput {F : List PBConstr} {obj : Option Objective}
    {P : RedProof} {Pres : List ℕ} {sec : OutputSection} {o : Output}
    (h : checkRedOutput F obj P (some Pres) sec = some o) (hg : o.guarantee = .equienumerable)
    (hb : o.bound = none) (hP : ∀ t ∈ P.steps, ∀ add x c sub, t ≠ .presChange add x c sub) :
    projections F Pres = projections o.formula.constraints Pres := by
  obtain ⟨s, hrun, -, hout, -, -, hsb⟩ := of_checkRedOutput h
  obtain ⟨hinv, he⟩ := invariants_of_runTop hrun
  rw [hg] at hout
  obtain ⟨P', Q, hP', -, hinj⟩ := equienumerable_injections hinv he hout
  cases (Option.some.inj hP' : Pres = P')
  have hpc := presChanged_of_runTop hP rfl hrun
  obtain ⟨-, -, heq⟩ := hinj _ (by rw [← hsb, hb]; simp)
  rw [image_solsLE_eq ⟨F, obj, some Pres⟩ Pres (le_max_left _ _),
    image_solsLE_eq o.formula Pres (le_max_right _ _)] at heq
  exact heq hpc

end Cslib.Logic.PL.VeriPB

end
