/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Machine
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Laws of linking and composing interactive machines

Running a program against a composed machine `A.comp P` is running it against `A` and running the
result against `P` (`Machine.runFrom_comp`). Since `A.comp P` initializes `P` first, linking is
associative as an equation of programs, without any appeal to probabilities
(`Machine.link_comp`): `(A.comp P).link Z = P.link (A.link Z)`. The forwarding machine is a unit
for linking (`Machine.link_id`). These are the package-algebra laws of state-separating proofs,
which turn reductions into a regrouping of the same program.

Call budgets compose: a machine making at most `u` calls per activation, on top of a machine making
at most `t`, makes at most `u * (t + 1) + t` (`Machine.IsBounded.comp`), and a program making at
most `m` calls, linked against a machine making at most `t` per activation, makes at most
`t + m * (t + 1)` (`Machine.isQueryBounded_link`).

## Main results

* `Cslib.Crypto.Protocols.UC.Machine.runFrom_map_state`,
  `Cslib.Crypto.Protocols.UC.Machine.comp_handle_map_state`: state representations that commute
  with every activation commute with runs and compositions.
* `Cslib.Crypto.Protocols.UC.Machine.runFrom_comp`: running against a composition.
* `Cslib.Crypto.Protocols.UC.Machine.link_comp`, `Cslib.Crypto.Protocols.UC.Machine.run_comp`:
  linking is associative.
* `Cslib.Crypto.Protocols.UC.Machine.runFrom_id`, `Cslib.Crypto.Protocols.UC.Machine.link_id`: the
  forwarding machine is a unit.
* `Cslib.Crypto.Protocols.UC.Machine.IsBounded.comp`,
  `Cslib.Crypto.Protocols.UC.Machine.isQueryBounded_link`: budgets of compositions and links.
* `Cslib.Crypto.Protocols.UC.Machine.liftRightProgram`,
  `Cslib.Crypto.Protocols.UC.Machine.liftRight`,
  `Cslib.Crypto.Protocols.UC.Machine.runFrom_liftRight_liftRightProgram`,
  `Cslib.Crypto.Protocols.UC.Machine.liftRight_id`,
  `Cslib.Crypto.Protocols.UC.Machine.liftRight_comp`,
  `Cslib.Crypto.Protocols.UC.Machine.isQueryBounded_liftRightProgram`,
  `Cslib.Crypto.Protocols.UC.Machine.isBounded_liftRight`: lifting a right-port program or machine
  past an arbitrary left-port interface.

## References

* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]: linking and its associativity.
-/

public section

namespace Cslib.Crypto.Protocols.UC.Machine

open OracleComp (sumHandler)

variable {ιI ιJ ιE : Type} {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type} {α : Type}

/-- A single call of the combined interface is answered by the machine's handler. -/
theorem runFrom_call (M : Machine I E) (q : ℕ ⊕ ιE) (s : M.State) :
    M.runFrom (OracleComp.query q) s = (M.handler q).run s :=
  OracleComp.run_interpret_query _ _ _

/-- A state representation `f` that commutes with every activation commutes with every run. -/
theorem runFrom_map_state (M₁ M₂ : Machine I E) (f : M₂.State → M₁.State)
    (h : ∀ q s, (M₁.handle q).run (f s) = Prod.map _root_.id f <$> (M₂.handle q).run s)
    (program : ProbOracleComp E α) (s : M₂.State) :
    M₁.runFrom program (f s) = Prod.map _root_.id f <$> M₂.runFrom program s := by
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    have hq : (M₁.handler q).run (f s) = Prod.map _root_.id f <$> (M₂.handler q).run s := by
      cases q with
      | inl k =>
        change (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run (f s) =
          Prod.map _root_.id f <$> (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run s
        simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]
        rfl
      | inr e => exact h e s
    rw [PFunctor.FreeM.bind_eq_bind, runFrom_bind, runFrom_bind, runFrom_call, runFrom_call,
      hq, bind_map_left, map_bind]
    exact bind_congr fun x => ih x.1 x.2

/-- Intertwining the inner machines of a composition intertwines the composed machines on the
product state. -/
theorem comp_handle_map_state (A : Machine J E) (P₁ P₂ : Machine I J) (f : P₂.State → P₁.State)
    (h : ∀ q s, (P₁.handle q).run (f s) = Prod.map _root_.id f <$> (P₂.handle q).run s)
    (q : ιE) (s : A.State × P₂.State) :
    ((A.comp P₁).handle q).run (Prod.map _root_.id f s) =
      Prod.map _root_.id (Prod.map _root_.id f) <$> ((A.comp P₂).handle q).run s := by
  rcases s with ⟨sA, sP⟩
  change Equiv.prodAssoc _ _ _ <$> P₁.runFrom ((A.handle q).run sA) (f sP) =
    Prod.map _root_.id (Prod.map _root_.id f) <$>
      (Equiv.prodAssoc _ _ _ <$> P₂.runFrom ((A.handle q).run sA) sP)
  rw [runFrom_map_state P₁ P₂ f h, Functor.map_map, Functor.map_map]
  rfl

/-- Running against a composition runs against the outer machine, and runs the result against the
inner machine. -/
theorem runFrom_comp (A : Machine J E) (P : Machine I J) (program : ProbOracleComp E α)
    (sA : A.State) (sP : P.State) :
    (A.comp P).runFrom program (sA, sP) =
      Equiv.prodAssoc _ _ _ <$> P.runFrom (A.runFrom program sA) sP := by
  simp only [runFrom]
  rw [OracleComp.run_interpret_run_interpret, Functor.map_map]
  have hhandler : (fun q (state : A.State × P.State) =>
      (fun x : (probOracleSpec E q × A.State) × P.State => (x.1.1, x.1.2, x.2)) <$>
        (OracleComp.interpret P.handler ((A.handler q).run state.1)).run state.2) =
      (A.comp P).handler := by
    funext q state
    cases q with
    | inl n =>
      change (fun x : (Fin (n + 1) × A.State) × P.State => (x.1.1, x.1.2, x.2)) <$>
          P.runFrom ((StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))).run state.1)
            state.2 =
        (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))).run state
      simp only [StateT.run_lift, bind_pure_comp, runFrom_map, runFrom_sample, Functor.map_map]
      rfl
    | inr e => rfl
  rw [hhandler]
  refine (id_map _).symm.trans ?_
  congr 1

/-- The composition samples the inner machine's state first. -/
theorem comp_init (A : Machine J E) (P : Machine I J) :
    (A.comp P).init = (do
      let sP ← P.init
      let sA ← A.init
      return (sA, sP)) := rfl

/-- Sampling the composition's initial state inside a program samples the inner machine's state,
then the outer one's. -/
theorem sample_comp_init {ιK : Type} {K : ιK → Type} (A : Machine J E) (P : Machine I J) :
    ProbOracleComp.sample (spec := K) (α := A.State × P.State) (A.comp P).init = (do
      let sP ← ProbOracleComp.sample P.init
      let sA ← ProbOracleComp.sample A.init
      return (sA, sP)) := by
  rw [comp_init, ProbOracleComp.sample_bind]
  simp only [ProbOracleComp.sample_bind, ProbOracleComp.sample_pure]

/-- Linking is associative: a program linked against a composition is the program linked against
the outer machine and then against the inner one. -/
theorem link_comp (A : Machine J E) (P : Machine I J) (program : ProbOracleComp E α) :
    (A.comp P).link program = P.link (A.link program) := by
  simp only [link, runFrom_bind, runFrom_sample, bind_map_left, map_bind]
  erw [sample_comp_init, bind_assoc]
  refine congrArg _ (funext fun sP => ?_)
  erw [bind_assoc]
  refine congrArg _ (funext fun sA => ?_)
  erw [pure_bind]
  rw [runFrom_comp]
  change (Prod.fst : α × A.State × P.State → α) <$>
    (Equiv.prodAssoc α A.State P.State <$> P.runFrom (A.runFrom program sA) sP) = _
  rw [Functor.map_map, runFrom_map, Functor.map_map]
  rfl

/-- Running a program against a closed composition is running its link against the inner machine. -/
theorem run_comp (A : Machine J E) (P : Machine OracleSpec.empty J) (program : ProbOracleComp E α) :
    (A.comp P).run program = P.run (A.link program) := by
  rw [run, run, link_comp]

/-- The forwarding machine passes every call through and never changes its state. -/
theorem runFrom_id (program : ProbOracleComp E α) (s : (Machine.id E).State) :
    (Machine.id E).runFrom program s = (fun a => (a, s)) <$> program := by
  have hhandler : (Machine.id E).handler = fun q => StateT.lift (OracleComp.query q) := by
    funext q
    cases q with
    | inl n => simp only [handler, Machine.id, ProbOracleComp.sample, ProbComp.unifFin,
        OracleComp.substitute_query]
    | inr e => rfl
  rw [runFrom, hhandler, OracleComp.run_interpret_lift, OracleComp.interpret_query_eq_self]

/-- Linking against the forwarding machine leaves a program unchanged. -/
@[simp] theorem link_id (program : ProbOracleComp E α) : (Machine.id E).link program = program := by
  simp only [link, runFrom_id, Functor.map_map, id_map']
  exact pure_bind _ _

/-! ### Budgets of compositions and links -/

/-- Embedded sampling makes as many calls as the closed program. -/
theorem isQueryBounded_sample {program : ProbComp α} {n : ℕ} (h : program.IsQueryBounded n) :
    (ProbOracleComp.sample (spec := I) program).IsQueryBounded n := by
  rw [ProbOracleComp.sample, OracleComp.substitute_eq_interpret]
  exact OracleComp.IsCostBounded.interpret (fun _ => OracleComp.IsCostBounded.query _) h

/-- Every call of a program run against `P` costs at most `t + 1` calls of `P`'s imports. -/
private theorem isQueryBounded_handler {P : Machine I J} {t : ℕ} (hP : P.IsBounded t)
    (q : ℕ ⊕ ιJ) (s : P.State) : ((P.handler q).run s).IsQueryBounded (t + 1) := by
  cases q with
  | inl n =>
    change ((StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))).run s).IsQueryBounded _
    rw [StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((isQueryBounded_sample (OracleComp.IsCostBounded.query n)).mono (by omega))
  | inr j => exact (hP.2 j s).mono (Nat.le_succ t)

/-- A program with at most `m` calls, run against a machine with at most `t` calls per activation,
makes at most `m * (t + 1)` calls. -/
theorem isQueryBounded_runFrom {P : Machine I J} {t m : ℕ} (hP : P.IsBounded t)
    {program : ProbOracleComp J α} (h : program.IsQueryBounded m) (s : P.State) :
    (P.runFrom program s).IsQueryBounded (m * (t + 1)) :=
  OracleComp.IsCostBounded.run_interpret (isQueryBounded_handler hP)
    (h.isCostBounded_mul_of_forall_le fun _ => le_rfl) s

/-- A program with at most `m` calls, linked against a machine with at most `t` calls per
activation and at initialization, makes at most `t + m * (t + 1)` calls. -/
theorem isQueryBounded_link {M : Machine I J} {t m : ℕ} (hM : M.IsBounded t)
    {program : ProbOracleComp J α} (h : program.IsQueryBounded m) :
    (M.link program).IsQueryBounded (t + m * (t + 1)) :=
  (isQueryBounded_sample hM.1).bind fun s =>
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_runFrom hM h s)

/-- A machine with at most `u` calls per activation on top of a machine with at most `t` makes at
most `u * (t + 1) + t` calls per activation. -/
theorem IsBounded.comp {A : Machine J E} {P : Machine I J} {u t : ℕ} (hA : A.IsBounded u)
    (hP : P.IsBounded t) : (A.comp P).IsBounded (u * (t + 1) + t) := by
  refine ⟨?_, fun q s => ?_⟩
  · refine (hP.1.bind fun _ => hA.1.bind fun _ => .pure _ 0).mono ?_
    rw [Nat.mul_succ]
    omega
  · refine ((OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_runFrom hP (hA.2 q s.1) s.2)).mono (Nat.le_add_right _ _)

/-! ### Lifting right-port programs and machines over an arbitrary left port -/

section LiftRight

variable {ιL ιR ιR₁ ιR₂ : Type} (L : ιL → Type)
  {R : ιR → Type} {R₁ : ιR₁ → Type} {R₂ : ιR₂ → Type} {β : Type}

/-- Lift a program on `R` to a program on `L ⊕ₒ R`, preserving private samples. -/
@[expose] def liftRightProgram (program : ProbOracleComp R α) : ProbOracleComp (L ⊕ₒ R) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec (L ⊕ₒ R)) (Sum.inl k))
      fun q => ProbOracleComp.query (Sum.inr q))
    program

@[simp] theorem liftRightProgram_pure (a : α) :
    liftRightProgram L (pure a : ProbOracleComp R α) = pure a := rfl

@[simp] theorem liftRightProgram_bind (program : ProbOracleComp R α)
    (next : α → ProbOracleComp R β) :
    liftRightProgram L (program >>= next) =
      liftRightProgram L program >>= fun a => liftRightProgram L (next a) :=
  OracleComp.interpret_bind _ _ _

@[simp] theorem liftRightProgram_map (f : α → β) (program : ProbOracleComp R α) :
    liftRightProgram L (f <$> program) = f <$> liftRightProgram L program :=
  OracleComp.interpret_map _ _ _

/-- A right-port query becomes a query on the right branch of `L ⊕ₒ R`. -/
@[simp] theorem liftRightProgram_query (q : ιR) :
    liftRightProgram L (ProbOracleComp.query (spec := R) q) =
      ProbOracleComp.query (spec := L ⊕ₒ R) (.inr q) :=
  OracleComp.interpret_query _ _

/-- Private samples are unchanged by lifting. -/
@[simp] theorem liftRightProgram_sample (program : ProbComp α) :
    liftRightProgram L (ProbOracleComp.sample (spec := R) program) =
      ProbOracleComp.sample program := by
  simp only [liftRightProgram, ProbOracleComp.interpret_sample]
  exact (OracleComp.substitute_eq_interpret _ _).symm

/-- Lifting past `L` preserves the call budget of a program. -/
theorem isQueryBounded_liftRightProgram {program : ProbOracleComp R α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftRightProgram L program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr q => exact OracleComp.IsCostBounded.query _

/-- Lift a machine `M` from `R → E` to `L ⊕ₒ R → L ⊕ₒ E`, forwarding left-port queries
unchanged and running right-port activations through `liftRightProgram`. -/
@[expose] def liftRight (M : Machine R E) : Machine (L ⊕ₒ R) (L ⊕ₒ E) where
  State := M.State
  init := M.init
  handle
    | .inl p => StateT.lift (ProbOracleComp.query (spec := L ⊕ₒ R) (Sum.inl p))
    | .inr q => fun s => liftRightProgram L ((M.handle q).run s)

/-- Running a lifted program against a lifted machine equals lifting the run against the inner
machine. -/
theorem runFrom_liftRight_liftRightProgram (S : Machine R₂ R₁)
    (program : ProbOracleComp R₁ α) (s : S.State) :
    (liftRight L S).runFrom (liftRightProgram L program) s =
      liftRightProgram L (S.runFrom program s) := by
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    cases q with
    | inl k =>
      have h₁ : liftRightProgram L
          (OracleComp.query (spec := probOracleSpec R₁) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← liftRightProgram_sample L (R := R₁)]
        rfl
      have h₂ : S.runFrom (OracleComp.query (spec := probOracleSpec R₁) (Sum.inl k)) s =
          (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        S.runFrom_sample (ProbComp.unifFin k) s
      rw [liftRightProgram_bind, h₁, Machine.runFrom_bind, h₂, liftRightProgram_bind,
        liftRightProgram_map, liftRightProgram_sample, bind_map_left]
      erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
      exact bind_congr fun a => ih a s
    | inr e =>
      rw [liftRightProgram_bind, Machine.runFrom_bind, liftRightProgram_bind]
      erw [Machine.runFrom_bind]
      have h₁ : (liftRight L S).runFrom
          (liftRightProgram L (OracleComp.query (spec := probOracleSpec R₁) (Sum.inr e))) s =
          liftRightProgram L (S.runFrom
            (OracleComp.query (spec := probOracleSpec R₁) (Sum.inr e)) s) := by
        erw [liftRightProgram_query, Machine.runFrom_query, Machine.runFrom_query]
        rfl
      exact (congrArg (fun m => m >>= _) h₁).trans
        (bind_congr fun (x : R₁ e × S.State) => ih x.1 x.2)

/-- Lifting the forwarding machine yields the forwarding machine on the combined interface. -/
@[simp] theorem liftRight_id :
    liftRight L (Machine.id R) = Machine.id (L ⊕ₒ R) := by
  simp only [liftRight, Machine.id]
  congr 1 with q s : 2
  cases q with
  | inl p => rfl
  | inr q =>
    change liftRightProgram L ((fun a => (a, s)) <$> ProbOracleComp.query q) = _
    rw [liftRightProgram_map, liftRightProgram_query]
    rfl

/-- Lifting a composition is composing the lifted machines. -/
theorem liftRight_comp (A : Machine R₁ E) (S : Machine R₂ R₁) :
    liftRight L (A.comp S) = (liftRight L A).comp (liftRight L S) := by
  simp only [liftRight, Machine.comp]
  congr 1 with q s : 2
  cases q with
  | inl p =>
    change (StateT.lift (ProbOracleComp.query (spec := L ⊕ₒ R₂) (Sum.inl p))) s =
      Equiv.prodAssoc _ _ _ <$> (liftRight L S).runFrom
        ((StateT.lift (ProbOracleComp.query (spec := L ⊕ₒ R₁) (Sum.inl p))).run s.1) s.2
    simp only [StateT.lift, StateT.run, bind_pure_comp]
    erw [Machine.runFrom_map, Machine.runFrom_query]
    simp only [liftRight, StateT.lift, StateT.run, bind_pure_comp, Functor.map_map]
    rfl
  | inr e =>
    change liftRightProgram L (Equiv.prodAssoc _ _ _ <$> S.runFrom ((A.handle e).run s.1) s.2) =
      Equiv.prodAssoc _ _ _ <$> (liftRight L S).runFrom
        (liftRightProgram L ((A.handle e).run s.1)) s.2
    rw [runFrom_liftRight_liftRightProgram, liftRightProgram_map]
    rfl

/-- Lifting a machine with per-activation call budget `t` yields budget `t + 1`: left-port queries
forward with one call. -/
theorem isBounded_liftRight {M : Machine R E} {t : ℕ} (h : M.IsBounded t) :
    (liftRight L M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (Nat.le_succ t), fun q s => ?_⟩
  cases q with
  | inl p =>
    change ((fun a => (a, s)) <$> ProbOracleComp.query _).IsQueryBounded _
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  | inr q => exact (isQueryBounded_liftRightProgram L (h.2 q s)).mono (Nat.le_succ t)

end LiftRight

end Cslib.Crypto.Protocols.UC.Machine
