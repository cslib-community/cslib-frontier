/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Output

/-! # Renaming the variables of an instance

What the conclusions of the VeriPB checker say about an instance does not depend on how its
variables are numbered. This file states that once, for every conclusion and every output
guarantee.

**The values of an instance.** Every conclusion speaks about the solutions of an instance through
their objective values and their projections to a list of variables: `UNSAT` and `SAT` say whether
there is a solution, `BOUNDS` bounds the values, an enumeration counts the projections, and the
output guarantees compare such sets between two instances (`Cslib.Logic.PL.VeriPB.semOutput`).
`Cslib.Logic.PL.VeriPB.Instance.valuesVia e I P` collects these pairs over the assignments `τ` of
a type `α` of names, the variable `v` read as `τ (e v)`, and
`Cslib.Logic.PL.VeriPB.Instance.values I P` is the case `e = id`.

**Transfer.** When `e` is injective on the variables of the instance and of `P`, reading through
`e` gives the same values (`Cslib.Logic.PL.VeriPB.Instance.valuesVia_eq`): every assignment of the
variables is `τ ∘ e` on them for some `τ`. With `α = String` and `e` the name of each variable,
this says that the conclusions hold for the named instance, under any assignment of the names.
With `α = ℕ`, it says that an injective renumbering `π` changes nothing, because the renamed
instance `Cslib.Logic.PL.VeriPB.Instance.rename π I` has the values of `I` read through `π`
(`Cslib.Logic.PL.VeriPB.Instance.values_rename`). The conclusions are read off the values by
`Cslib.Logic.PL.VeriPB.Instance.satisfiable_iff`, `Cslib.Logic.PL.VeriPB.Instance.exists_iff`,
`Cslib.Logic.PL.VeriPB.Instance.image_solsLE` and
`Cslib.Logic.PL.VeriPB.Instance.projections_eq`, and the output guarantees transfer as a whole
(`Cslib.Logic.PL.VeriPB.Instance.semOutput_rename_iff`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Instance.rename`: an instance with its variables renamed.
* `Cslib.Logic.PL.VeriPB.Instance.valuesVia`, `Cslib.Logic.PL.VeriPB.Instance.values`: the values
  and projections of the solutions.

## Main results

* `Cslib.Logic.PL.VeriPB.Instance.valuesVia_eq`: the transfer.
* `Cslib.Logic.PL.VeriPB.Instance.values_rename`: renaming is reading through the renaming.
* `Cslib.Logic.PL.VeriPB.Instance.semOutput_rename_iff`: the output guarantees are invariant under
  injective renaming.
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB

open PBConstr

namespace Instance

/-! ### Renaming -/

/-- A term with its variable `v` renamed `π v`. -/
def renameTerm (π : ℕ → ℕ) : ℕ × Literal ℕ → ℕ × Literal ℕ
  | (a, v, b) => (a, π v, b)

/-- A constraint with each variable `v` renamed `π v`. -/
def renameConstr (π : ℕ → ℕ) (c : PBConstr) : PBConstr :=
  ⟨c.terms.map (renameTerm π), c.degree⟩

/-- An objective with each variable `v` renamed `π v`. -/
def renameObj (π : ℕ → ℕ) (f : Objective) : Objective :=
  ⟨f.lin.map fun e => (π e.1, e.2), f.const⟩

/-- **An instance with each variable `v` renamed `π v`**, in its constraints, its objective and
its preserved set. -/
def rename (π : ℕ → ℕ) (I : Instance) : Instance :=
  ⟨I.constraints.map (renameConstr π), I.objective.map (renameObj π), I.preserved.map (·.map π)⟩

@[simp] theorem rename_id (I : Instance) : I.rename id = I := by
  obtain ⟨cs, obj, pres⟩ := I
  have hc (c : PBConstr) : renameConstr id c = c := by
    rcases c with ⟨ts, d⟩
    simp only [renameConstr, PBConstr.mk.injEq, and_true]
    exact (List.map_congr_left fun ⟨_, _, _⟩ _ => rfl).trans (List.map_id ts)
  have hcs : cs.map (renameConstr id) = cs :=
    (List.map_congr_left fun c _ => hc c).trans (List.map_id cs)
  cases obj <;> cases pres <;> simp [rename, renameObj, hcs]

/-- The variables of the constraints and of the objective. -/
def vars (I : Instance) : Set ℕ :=
  {v | (∃ c ∈ I.constraints, ∃ t ∈ c.terms, termVar t = v) ∨
    ∃ f ∈ I.objective, ∃ e ∈ f.lin, e.1 = v}

/-- The variables of the constraints, of the objective and of the preserved set, in this order,
with repetitions. -/
def varList (I : Instance) : List ℕ :=
  (I.constraints.flatMap fun c => c.terms.map termVar) ++
    (I.objective.map fun f => f.lin.map Prod.fst).getD [] ++ I.preserved.getD []

/-- The variables of the constraints, of the objective and of the preserved set. -/
def allVars (I : Instance) : Set ℕ := {v | v ∈ I.varList}

theorem vars_subset_allVars (I : Instance) : I.vars ⊆ I.allVars := by
  rintro v (⟨c, hc, t, ht, rfl⟩ | ⟨f, hf, e, he, rfl⟩)
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨c, hc, List.mem_map_of_mem ht⟩))
  · exact List.mem_append_left _ (List.mem_append_right _
      (by rw [Option.mem_def.1 hf]; exact List.mem_map_of_mem he))

theorem mem_allVars_of_preserved {I : Instance} {P : List ℕ} (hP : I.preserved = some P)
    {v : ℕ} (hv : v ∈ P) : v ∈ I.allVars :=
  List.mem_append_right _ (by rw [hP]; exact hv)

theorem holds_renameConstr (π : ℕ → ℕ) (c : PBConstr) (σ : ℕ → Bool) :
    (renameConstr π c).Holds σ ↔ c.Holds (σ ∘ π) := by
  simp only [Holds, renameConstr, lhs, List.map_map]
  rfl

theorem eval_renameObj (π : ℕ → ℕ) (f : Objective) (σ : ℕ → Bool) :
    (renameObj π f).eval σ = f.eval (σ ∘ π) := by
  simp only [Objective.eval, renameObj, linVal, List.map_map]
  rfl

theorem objValue_rename (π : ℕ → ℕ) (I : Instance) (σ : ℕ → Bool) :
    objValue (I.rename π).objective σ = objValue I.objective (σ ∘ π) := by
  cases h : I.objective <;> simp [rename, h, objValue, eval_renameObj]

theorem proj_map (π : ℕ → ℕ) (P : List ℕ) (σ : ℕ → Bool) :
    proj (P.map π) σ = proj P (σ ∘ π) := by
  simp [proj]

/-! ### Values -/

/-- **The values of the solutions read through `e`**: for each assignment `τ` of the names `α`
under which the constraints hold, the variable `v` read as `τ (e v)`, the objective value and the
projection to `P`. -/
def valuesVia {α : Type*} (e : ℕ → α) (I : Instance) (P : List ℕ) : Set (ℤ × List Bool) :=
  {x | ∃ τ : α → Bool, (∀ c ∈ I.constraints, c.Holds (τ ∘ e)) ∧
    x = (objValue I.objective (τ ∘ e), proj P (τ ∘ e))}

/-- **The values of the solutions**: for each solution, its objective value and its projection to
`P`. -/
def values (I : Instance) (P : List ℕ) : Set (ℤ × List Bool) := I.valuesVia id P

theorem mem_values {I : Instance} {P : List ℕ} {x : ℤ × List Bool} :
    x ∈ I.values P ↔ ∃ σ, (∀ c ∈ I.constraints, c.Holds σ) ∧
      x = (objValue I.objective σ, proj P σ) := Iff.rfl

/-- **Renaming is reading through the renaming.** -/
theorem values_rename (π : ℕ → ℕ) (I : Instance) (P : List ℕ) :
    (I.rename π).values (P.map π) = I.valuesVia π P := by
  ext x
  simp only [mem_values, valuesVia, Set.mem_ofPred_eq, objValue_rename, proj_map]
  refine exists_congr fun σ => and_congr ?_ Iff.rfl
  simp [rename, holds_renameConstr]

private theorem linVal_congr {σ σ' : ℕ → Bool} {L : List (ℕ × ℤ)}
    (h : ∀ e ∈ L, σ e.1 = σ' e.1) : linVal σ L = linVal σ' L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [linVal_cons, h e List.mem_cons_self, ih fun e he => h e (List.mem_cons_of_mem _ he)]

/-- The solutions, their values and their projections depend only on the variables of the
instance and of `P`. -/
private theorem values_congr {I : Instance} {P : List ℕ} {σ σ' : ℕ → Bool}
    (h : ∀ v ∈ I.vars ∪ {v | v ∈ P}, σ v = σ' v) :
    ((∀ c ∈ I.constraints, c.Holds σ) ↔ ∀ c ∈ I.constraints, c.Holds σ') ∧
      objValue I.objective σ = objValue I.objective σ' ∧ proj P σ = proj P σ' := by
  refine ⟨forall₂_congr fun c hc => holds_congr fun t ht => h _ (.inl (.inl ⟨c, hc, t, ht, rfl⟩)),
    ?_, List.map_congr_left fun v hv => h v (.inr hv)⟩
  cases hf : I.objective with
  | none => rfl
  | some f =>
    simp only [objValue, Objective.eval]
    rw [linVal_congr fun e he => h _ (.inl (.inr ⟨f, hf, e, he, rfl⟩))]

/-- **Transfer**: read through a map `e` injective on the variables of the instance and of `P`,
the solutions have the same values and projections. Every assignment `σ` of the variables is
`τ ∘ e` on them, for `τ` the assignment of the names `e v` that gives `e v` the value of `v`. -/
theorem valuesVia_eq {α : Type*} {e : ℕ → α} {I : Instance} {P : List ℕ}
    (he : Set.InjOn e (I.vars ∪ {v | v ∈ P})) : I.valuesVia e P = I.values P := by
  ext x
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ ∘ e, hτ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    let τ (a : α) := σ (Function.invFunOn e (I.vars ∪ {v | v ∈ P}) a)
    obtain ⟨h1, h2, h3⟩ := values_congr (P := P) (I := I)
      (σ := τ ∘ e) fun v hv => congrArg σ (he.leftInvOn_invFunOn hv)
    exact ⟨τ, h1.2 hσ, Prod.ext h2.symm h3.symm⟩

/-- An injective renaming keeps the values and projections. -/
theorem values_rename_eq {π : ℕ → ℕ} {I : Instance} {P : List ℕ}
    (hπ : Set.InjOn π (I.vars ∪ {v | v ∈ P})) : (I.rename π).values (P.map π) = I.values P := by
  rw [values_rename, valuesVia_eq hπ]

/-! ### The conclusions in terms of the values -/

theorem satisfiable_iff (I : Instance) : I.Satisfiable ↔ (I.values []).Nonempty :=
  ⟨fun ⟨σ, h⟩ => ⟨_, σ, h, rfl⟩, fun ⟨_, σ, h, _⟩ => ⟨σ, h⟩⟩

/-- A property of the value and projection of some solution. -/
theorem exists_iff (I : Instance) (P : List ℕ) (p : ℤ → List Bool → Prop) :
    (∃ σ, (∀ c ∈ I.constraints, c.Holds σ) ∧ p (objValue I.objective σ) (proj P σ)) ↔
      ∃ x ∈ I.values P, p x.1 x.2 :=
  ⟨fun ⟨σ, hσ, h⟩ => ⟨_, ⟨σ, hσ, rfl⟩, h⟩, fun ⟨_, ⟨σ, hσ, rfl⟩, h⟩ => ⟨σ, hσ, h⟩⟩

/-- The projections of the solutions. -/
theorem projections_eq (I : Instance) (P : List ℕ) :
    projections I.constraints P = Prod.snd '' I.values P :=
  Set.ext fun _ => ⟨fun ⟨σ, hσ, hl⟩ => ⟨_, ⟨σ, hσ, rfl⟩, hl⟩,
    fun ⟨_, ⟨σ, hσ, rfl⟩, hl⟩ => ⟨σ, hσ, hl⟩⟩

/-- The projections of the solutions of value at most `v`. -/
theorem image_solsLE (I : Instance) (P : List ℕ) (v : ℤ) :
    proj P '' I.solsLE v = Prod.snd '' {x ∈ I.values P | x.1 ≤ v} :=
  Set.ext fun _ =>
    ⟨fun ⟨σ, ⟨hσ, hv⟩, hl⟩ => ⟨_, ⟨⟨σ, hσ, rfl⟩, hv⟩, hl⟩,
      fun ⟨_, ⟨⟨σ, hσ, rfl⟩, hv⟩, hl⟩ => ⟨σ, ⟨hσ, hv⟩, hl⟩⟩

/-! ### Output guarantees -/

private theorem injOn_vars {π : ℕ → ℕ} {I : Instance} {P : List ℕ} {S : Set ℕ}
    (hπ : Set.InjOn π S) (hI : I.vars ⊆ S) (hP : ∀ v ∈ P, v ∈ S) :
    Set.InjOn π (I.vars ∪ {v | v ∈ P}) :=
  hπ.mono (Set.union_subset hI fun v hv => hP v hv)

private theorem nonempty_solsLE_rename {π : ℕ → ℕ} {I : Instance} (hπ : Set.InjOn π I.vars)
    (v : ℤ) : ((I.rename π).solsLE v).Nonempty ↔ (I.solsLE v).Nonempty := by
  have key (J : Instance) : (J.solsLE v).Nonempty ↔ ∃ x ∈ J.values [], x.1 ≤ v :=
    exists_iff J [] fun o _ => o ≤ v
  simpa only [key, List.map_nil] using
    (congrArg (∃ x ∈ ·, x.1 ≤ v) (values_rename_eq (P := []) (I := I) (hπ.mono (by simp)))).to_iff

private theorem image_solsLE_rename {π : ℕ → ℕ} {J : Instance} {P : List ℕ}
    (hπ : Set.InjOn π (J.vars ∪ {v | v ∈ P})) (v : ℤ) :
    proj (P.map π) '' (J.rename π).solsLE v = proj P '' J.solsLE v := by
  rw [image_solsLE, image_solsLE, values_rename_eq hπ]

/-- **The output guarantees are invariant under injective renaming**: renaming the input and the
output formula alike, injectively on their variables and preserved sets, keeps each guarantee. -/
theorem semOutput_rename_iff {π : ℕ → ℕ} {I O : Instance} {b : Option ℤ} {g : Guarantee}
    (hπ : Set.InjOn π (I.allVars ∪ O.allVars)) :
    semOutput (I.rename π) b (O.rename π) g ↔ semOutput I b O g := by
  have hI : I.vars ⊆ I.allVars ∪ O.allVars := fun v hv => .inl (vars_subset_allVars I hv)
  have hO : O.vars ⊆ I.allVars ∪ O.allVars := fun v hv => .inr (vars_subset_allVars O hv)
  have hsat (J : Instance) (hJ : Set.InjOn π J.vars) :
      (J.rename π).Satisfiable ↔ J.Satisfiable := by
    simpa only [satisfiable_iff, List.map_nil] using
      (congrArg Set.Nonempty (values_rename_eq (P := []) (I := J) (hJ.mono (by simp)))).to_iff
  cases g with
  | derivable =>
    exact imp_congr (hsat I (hπ.mono hI)) (hsat O (hπ.mono hO))
  | equisatisfiable =>
    exact iff_congr (hsat I (hπ.mono hI)) (hsat O (hπ.mono hO))
  | equioptimal =>
    exact forall_congr' fun v => imp_congr_right fun _ =>
      iff_congr (nonempty_solsLE_rename (hπ.mono hI) v) (nonempty_solsLE_rename (hπ.mono hO) v)
  | equienumerable =>
    have hp {J : Instance} {R : List ℕ} :
        (J.rename π).preserved = some R ↔ ∃ P, J.preserved = some P ∧ P.map π = R :=
      Option.map_eq_some_iff
    have himg {P Q : List ℕ} (hP : I.preserved = some P) (hQ : O.preserved = some Q) (v : ℤ) :
        (∃ f, Set.BijOn f (proj (P.map π) '' (I.rename π).solsLE v)
          (proj (Q.map π) '' (O.rename π).solsLE v)) ↔
            ∃ f, Set.BijOn f (proj P '' I.solsLE v) (proj Q '' O.solsLE v) := by
      rw [image_solsLE_rename (injOn_vars hπ hI fun _ hv => .inl (mem_allVars_of_preserved hP hv)),
        image_solsLE_rename (injOn_vars hπ hO fun _ hv => .inr (mem_allVars_of_preserved hQ hv))]
    simp only [semOutput, hp]
    exact ⟨fun ⟨_, _, ⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, h⟩ =>
        ⟨P, Q, hP, hQ, fun v hv => (himg hP hQ v).1 (h v hv)⟩,
      fun ⟨P, Q, hP, hQ, h⟩ =>
        ⟨_, _, ⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, fun v hv => (himg hP hQ v).2 (h v hv)⟩⟩

end Instance

end Cslib.Logic.PL.VeriPB

end
