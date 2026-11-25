/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Interactive machines with private coins

An interactive machine `M : UC.Machine I E` is a stateful probabilistic program that *exports*
the interface `E` and *imports* the interface `I`. It samples an initial private state with
`M.init`, and each *activation* `M.handle q` answers one query `q` of `E`: it may draw private
coins, call `I`, and update its state. Activations are `ProbOracleComp I` programs, so a machine is
a program in the sense of `CslibFrontier/Languages/Probabilistic/Semantics.lean`, not a
distribution.
A machine importing `OracleSpec.empty` is *closed*.

These machines are the parties, protocols, ideal functionalities, adversaries and simulators of
the universal-composability (UC) execution in `CslibFrontier.Crypto.Protocols.UC.Execution`. Their
composition follows the package algebra of state-separating proofs: `Machine.comp A P` answers each
query of `A` by running `A`'s activation with its imported calls answered by `P`, and
`Machine.link M Z` runs a program `Z` over `E` with its calls answered by `M`, which removes the
interface `E`.

A *budget* `M.IsBounded t` says that the initial sampler and every activation make at most `t`
calls on every path, counting private samples and calls to `I` alike
(`OracleComp.IsQueryBounded`). As everywhere in this library, a call budget bounds interaction, not
running time: pure computation between calls, message sizes and state growth are free.

## Main definitions

* `Cslib.Crypto.Protocols.UC.Machine`: a stateful interactive machine with private coins.
* `Cslib.Crypto.Protocols.UC.Machine.handler`, `Cslib.Crypto.Protocols.UC.Machine.runFrom`: the
  handler answering the private samples and exported calls of a program, and the stateful run from a
  given state.
* `Cslib.Crypto.Protocols.UC.Machine.link`: run a program against a machine, sampling its initial
  state.
* `Cslib.Crypto.Protocols.UC.Machine.comp`: sequential composition of machines.
* `Cslib.Crypto.Protocols.UC.Machine.id`: the machine forwarding every query unchanged.
* `Cslib.Crypto.Protocols.UC.Machine.run`: the closed probabilistic program of a program run against
  a closed machine.
* `Cslib.Crypto.Protocols.UC.Machine.IsBounded`: a per-activation call budget.

## Main results

* `Cslib.Crypto.Protocols.UC.Machine.IsBounded.mono`: budgets are monotone.
* `Cslib.Crypto.Protocols.UC.Machine.isBounded_id`: the forwarding machine makes one call per
  activation.
* `Cslib.Crypto.Protocols.UC.Machine.isQueryBounded_closeProgram`: closing a program with no
  imports preserves its call budget.
* `Cslib.Crypto.Protocols.UC.Machine.runFrom_interpret_intertwine`,
  `Cslib.Crypto.Protocols.UC.Machine.runFrom_intertwine`,
  `Cslib.Crypto.Protocols.UC.Machine.closeEval_runFrom_interpret_le_intertwine`,
  `Cslib.Crypto.Protocols.UC.Machine.closeEval_runFrom_le_intertwine`: exact and sub-probability
  state-intertwining laws for `Machine.runFrom`.
* `Cslib.Crypto.Protocols.UC.Machine.runFrom_interpret_stripNoop`,
  `Cslib.Crypto.Protocols.UC.Machine.run_interpret_stripNoop`: replacing state-preserving no-op
  queries by `pure` leaves `Machine.runFrom` and `Machine.run` invariant.

## References

* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]: the package algebra.
* [R. Canetti, *Universally Composable Security*][Canetti2020]: the machines play the role of the
  interactive Turing machines of the UC framework.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)

/-- An interactive machine exporting the interface `E` and importing the interface `I`: a private
state sampled by `init`, and for each query `q` of `E` an activation that answers it with private
coins, calls to `I` and an updated state. -/
structure Machine {ιI ιE : Type} (I : ιI → Type) (E : ιE → Type) : Type 1 where
  /-- The private state. -/
  State : Type
  /-- The initial state sampler. -/
  init : ProbComp State
  /-- The activation answering a query of the exported interface. -/
  handle : (q : ιE) → StateT State (ProbOracleComp I) (E q)

namespace Machine

variable {ιI ιJ ιE : Type} {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type} {α : Type}

/-- The stateful handler for programs calling `M`: private samples of the program stay private
samples, and calls to the exported interface run `M`'s activations. -/
@[expose] def handler (M : Machine I E) :
    (q : ℕ ⊕ ιE) → StateT M.State (ProbOracleComp I) (probOracleSpec E q) :=
  sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) M.handle

/-- Run a program over `E` against `M` from the state `s`, returning its result and `M`'s final
state. -/
@[expose] def runFrom (M : Machine I E) (program : ProbOracleComp E α) (s : M.State) :
    ProbOracleComp I (α × M.State) :=
  (OracleComp.interpret M.handler program).run s

/-- Run a program over `E` against `M`, starting from a fresh initial state. The exported interface
disappears; what remains calls `M`'s imported interface. -/
@[expose] def link (M : Machine I E) (program : ProbOracleComp E α) : ProbOracleComp I α := do
  let s ← ProbOracleComp.sample M.init
  Prod.fst <$> M.runFrom program s

/-- Sequential composition: `A.comp P` answers a query of `A`'s exported interface by running `A`'s
activation, whose calls to the interface `J` are answered by `P`. The imported machine `P` is
initialized first, as when a program is linked against `A` and the result against `P`. -/
@[expose] def comp (A : Machine J E) (P : Machine I J) : Machine I E where
  State := A.State × P.State
  init := do
    let sP ← P.init
    let sA ← A.init
    return (sA, sP)
  handle q s := Equiv.prodAssoc _ _ _ <$> P.runFrom ((A.handle q).run s.1) s.2

/-- The stateless machine forwarding every query of `E` to its imported copy of `E`. -/
@[expose] def id (E : ιE → Type) : Machine E E where
  State := PUnit
  init := pure PUnit.unit
  handle q := StateT.lift (ProbOracleComp.query q)

/-- A program with private coins and no external calls, as a closed probabilistic program. -/
@[expose] def closeProgram (program : ProbOracleComp OracleSpec.empty α) : ProbComp α :=
  OracleComp.interpret (sumHandler ProbComp.unifFin fun q => q.elim) program

/-- The closed probabilistic program of a program over `E` run against the closed machine `M`. -/
@[expose] def run (M : Machine OracleSpec.empty E) (program : ProbOracleComp E α) : ProbComp α :=
  closeProgram (M.link program)

/-! ### Running programs against machines -/

section RunFrom

variable {β : Type}

/-- A returned value makes no call and leaves the machine's state unchanged. -/
@[simp] theorem runFrom_pure (M : Machine I E) (a : α) (s : M.State) :
    M.runFrom (pure a) s = pure (a, s) := rfl

/-- Sequencing runs the second program from the state the first one reached. -/
@[simp] theorem runFrom_bind (M : Machine I E) (program : ProbOracleComp E α)
    (next : α → ProbOracleComp E β) (s : M.State) :
    M.runFrom (program >>= next) s = M.runFrom program s >>= fun x => M.runFrom (next x.1) x.2 :=
  OracleComp.run_interpret_bind _ _ _ _

/-- Postprocessing the result keeps the machine's final state. -/
@[simp] theorem runFrom_map (M : Machine I E) (f : α → β) (program : ProbOracleComp E α)
    (s : M.State) : M.runFrom (f <$> program) s = Prod.map f _root_.id <$> M.runFrom program s :=
  OracleComp.run_interpret_map _ _ _ _

/-- An exported call is one activation of the machine. -/
@[simp] theorem runFrom_query (M : Machine I E) (q : ιE) (s : M.State) :
    M.runFrom (ProbOracleComp.query q) s = (M.handle q).run s :=
  OracleComp.run_interpret_query _ _ _

/-- A private sample of the program stays a private sample and leaves the machine untouched. -/
@[simp] theorem runFrom_sample (M : Machine I E) (program : ProbComp α) (s : M.State) :
    M.runFrom (ProbOracleComp.sample program) s =
      (fun a => (a, s)) <$> ProbOracleComp.sample program :=
  ProbOracleComp.run_interpret_lift_sample M.handle program s

/-- Closing a returned value returns it. -/
@[simp] theorem closeProgram_pure (a : α) : closeProgram (pure a) = pure a := rfl

/-- Closing commutes with sequencing. -/
@[simp] theorem closeProgram_bind (program : ProbOracleComp OracleSpec.empty α)
    (next : α → ProbOracleComp OracleSpec.empty β) :
    closeProgram (program >>= next) = closeProgram program >>= fun a => closeProgram (next a) :=
  OracleComp.interpret_bind _ _ _

/-- Closing commutes with postprocessing. -/
@[simp] theorem closeProgram_map (f : α → β) (program : ProbOracleComp OracleSpec.empty α) :
    closeProgram (f <$> program) = f <$> closeProgram program :=
  OracleComp.interpret_map _ _ _

/-- An embedded closed program is unchanged by closing. -/
@[simp] theorem closeProgram_sample (program : ProbComp α) :
    closeProgram (ProbOracleComp.sample program) = program := by
  rw [closeProgram, ProbOracleComp.interpret_sample, ProbComp.interpret_unifFin]

/-- Close an empty-spec probabilistic computation and return its `PMF`. -/
@[expose] noncomputable def closeEval (program : ProbOracleComp OracleSpec.empty α) : PMF α :=
  ProbComp.eval (closeProgram program)

/-- Closing a `pure` program yields `PMF.pure`. -/
@[simp] theorem closeEval_pure (a : α) : closeEval (pure a) = PMF.pure a := rfl

/-- Closing a bind distributes over `PMF.bind`. -/
@[simp] theorem closeEval_bind (p : ProbOracleComp OracleSpec.empty α)
    (next : α → ProbOracleComp OracleSpec.empty β) :
    closeEval (p >>= next) = (closeEval p).bind fun a => closeEval (next a) := by
  simp only [closeEval, closeProgram_bind, ProbComp.eval_bind]

/-- Closing a mapped program maps the `PMF`. -/
@[simp] theorem closeEval_map (f : α → β) (p : ProbOracleComp OracleSpec.empty α) :
    closeEval (f <$> p) = (closeEval p).map f := by
  simp only [closeEval, closeProgram_map, ProbComp.eval_map]

/-- Closing a sampled `ProbComp` evaluates it directly. -/
@[simp] theorem closeEval_sample (p : ProbComp α) :
    closeEval (ProbOracleComp.sample p) = p.eval := by
  simp only [closeEval, closeProgram_sample]

/-- Support of `closeEval (pure a)`. -/
theorem mem_support_closeEval_pure {a x : α} :
    x ∈ (closeEval (pure a)).support ↔ x = a := by erw [closeEval_pure, PMF.mem_support_pure_iff]

/-- Support of `closeEval (p >>= next)`. -/
theorem mem_support_closeEval_bind {p : ProbOracleComp OracleSpec.empty α}
    {next : α → ProbOracleComp OracleSpec.empty β} {y : β} :
    y ∈ (closeEval (p >>= next)).support ↔
      ∃ a ∈ (closeEval p).support, y ∈ (closeEval (next a)).support := by
  erw [closeEval_bind, PMF.mem_support_bind_iff]

/-- Support of `closeEval (f <$> p)`. -/
theorem mem_support_closeEval_map {f : α → β} {p : ProbOracleComp OracleSpec.empty α} {y : β} :
    y ∈ (closeEval (f <$> p)).support ↔ ∃ a ∈ (closeEval p).support, f a = y := by
  erw [closeEval_map, PMF.mem_support_map_iff]

/-- Pointwise monotonicity of `closeEval` across a shared prefix `p`. -/
theorem closeEval_bind_le (p : ProbOracleComp OracleSpec.empty α)
    (f g : α → ProbOracleComp OracleSpec.empty β) (y : β)
    (h : ∀ a, closeEval (f a) y ≤ closeEval (g a) y) :
    closeEval (p >>= f) y ≤ closeEval (p >>= g) y := by
  rw [closeEval_bind, closeEval_bind, PMF.bind_apply, PMF.bind_apply]
  exact tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h a) zero_le

private theorem closeEval_bind_eq_zero {p : ProbOracleComp OracleSpec.empty α}
    {f : α → ProbOracleComp OracleSpec.empty β} {y : β}
    (h : ∀ a ∈ (closeEval p).support, closeEval (f a) y = 0) : closeEval (p >>= f) y = 0 := by
  rw [closeEval_bind, PMF.bind_apply, tsum_eq_zero_iff]
  intro a
  by_cases ha : a ∈ (closeEval p).support
  · exact mul_eq_zero_of_right _ (h a ha)
  · rw [PMF.mem_support_iff, not_not] at ha
    exact mul_eq_zero_of_left ha _

private theorem runFrom_query_inl (M : Machine I E) (k : ℕ) (s : M.State) :
    M.runFrom (OracleComp.query (.inl k)) s =
      (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
  (OracleComp.run_interpret_query M.handler (.inl k) s).trans
    ((StateT.run_lift _ s).trans (bind_pure_comp _ _))

private theorem sumHandler_query_eq (E : ιE → Type) :
    sumHandler (fun k => OracleComp.query (spec := probOracleSpec E) (.inl k))
      (fun q => ProbOracleComp.query (spec := E) q) = OracleComp.query :=
  funext fun q => by cases q <;> rfl

/-- Support invariant for `closeEval (M.runFrom prog s)` under a reflexive, transitive state
relation preserved by every allowed machine query. -/
theorem mem_support_closeEval_runFrom_invariant
    (M : Machine OracleSpec.empty E) (Inv : ιE → Prop) (R : M.State → M.State → Prop)
    (hR_refl : ∀ s, R s s) (hR_trans : ∀ {a b c}, R a b → R b c → R a c)
    (prog : ProbOracleComp E α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s : M.State) {x : α × M.State} (hx : x ∈ (closeEval (M.runFrom prog s)).support)
    (hstep : ∀ (q : ιE) (s' : M.State) {y : E q × M.State},
      Inv q → y ∈ (closeEval ((M.handle q).run s')).support → R s' y.2) :
    R s x.2 := by
  induction prog using OracleComp.induction generalizing s with
  | pure a => exact mem_support_closeEval_pure.mp hx ▸ hR_refl s
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind] at hinv hx
    have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hinv
    rcases q with k | q
    · erw [runFrom_bind, runFrom_query_inl, bind_map_left] at hx
      obtain ⟨a, _, hx'⟩ := mem_support_closeEval_bind.mp hx
      exact ih a (hq.2 a) s hx'
    · erw [runFrom_bind, runFrom_query] at hx
      obtain ⟨y, hy, hx'⟩ := mem_support_closeEval_bind.mp hx
      exact hR_trans (hstep q s hq.1 hy) (ih y.1 (hq.2 y.1) y.2 hx')

end RunFrom

/-! ### State-intertwining for `runFrom` -/

section Intertwining

variable {ι₁ ι₂ ι β : Type} {E₁ : ι₁ → Type} {E₂ : ι₂ → Type} {O : ι → Type}

/-- Two machines `M₁` and `M₂` sharing an imported interface `I`, a state invariant `R`, and a
query invariant `Inv` produce related post-run continuations when translating an `O`-program via
`h₁` and `h₂` preserves `R` at each `Inv`-satisfying query. -/
theorem runFrom_interpret_intertwine (M₁ : Machine I E₁) (M₂ : Machine I E₂)
    (h₁ : (q : ι) → ProbOracleComp E₁ (O q)) (h₂ : (q : ι) → ProbOracleComp E₂ (O q))
    (Inv : ι → Prop) (R : M₁.State → M₂.State → Prop) (prog : ProbOracleComp O α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s₁ : M₁.State) (s₂ : M₂.State) (hR : R s₁ s₂)
    (f : α × M₁.State → ProbOracleComp I β) (g : α × M₂.State → ProbOracleComp I β)
    (hfg : ∀ a s₁' s₂', R s₁' s₂' → f (a, s₁') = g (a, s₂'))
    (hstep : ∀ (q : ι) (s₁' : M₁.State) (s₂' : M₂.State)
      (k₁ : O q × M₁.State → ProbOracleComp I β) (k₂ : O q × M₂.State → ProbOracleComp I β),
      Inv q → R s₁' s₂' → (∀ r s₁'' s₂'', R s₁'' s₂'' → k₁ (r, s₁'') = k₂ (r, s₂'')) →
      (M₁.runFrom (h₁ q) s₁' >>= k₁) = (M₂.runFrom (h₂ q) s₂' >>= k₂)) :
    (M₁.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₁) (.inl k)) h₁) prog)
        s₁ >>= f) =
      (M₂.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₂) (.inl k)) h₂) prog)
        s₂ >>= g) := by
  induction prog using OracleComp.induction generalizing s₁ s₂ with
  | pure a => exact hfg a s₁ s₂ hR
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind] at hinv ⊢
    have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hinv
    rcases q with k | q
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler]
      erw [runFrom_bind, runFrom_bind, runFrom_query_inl M₁, runFrom_query_inl M₂,
        bind_map_left, bind_map_left, bind_assoc, bind_assoc]
      exact bind_congr fun a => ih a (hq.2 a) s₁ s₂ hR
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler]
      erw [runFrom_bind, runFrom_bind, bind_assoc, bind_assoc]
      exact hstep q s₁ s₂ _ _ hq.1 hR fun r s₁'' s₂'' hR' => ih r (hq.2 r) s₁'' s₂'' hR'

/-- Direct (uninterpreted) state-intertwining specialization of
`Machine.runFrom_interpret_intertwine` for two machines sharing an exported interface `E`. -/
theorem runFrom_intertwine (M₁ M₂ : Machine I E) (Inv : ιE → Prop)
    (R : M₁.State → M₂.State → Prop) (prog : ProbOracleComp E α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s₁ : M₁.State) (s₂ : M₂.State) (hR : R s₁ s₂)
    (f : α × M₁.State → ProbOracleComp I β) (g : α × M₂.State → ProbOracleComp I β)
    (hfg : ∀ a s₁' s₂', R s₁' s₂' → f (a, s₁') = g (a, s₂'))
    (hstep : ∀ (q : ιE) (s₁' : M₁.State) (s₂' : M₂.State)
      (k₁ : E q × M₁.State → ProbOracleComp I β) (k₂ : E q × M₂.State → ProbOracleComp I β),
      Inv q → R s₁' s₂' → (∀ r s₁'' s₂'', R s₁'' s₂'' → k₁ (r, s₁'') = k₂ (r, s₂'')) →
      ((M₁.handle q).run s₁' >>= k₁) = ((M₂.handle q).run s₂' >>= k₂)) :
    (M₁.runFrom prog s₁ >>= f) = (M₂.runFrom prog s₂ >>= g) := by
  simpa only [sumHandler_query_eq, OracleComp.interpret_query_eq_self] using
    runFrom_interpret_intertwine M₁ M₂ ProbOracleComp.query ProbOracleComp.query
      Inv R prog hinv s₁ s₂ hR f g hfg fun q s₁' s₂' k₁ k₂ hq hR' hcont => by
        erw [runFrom_query, runFrom_query]; exact hstep q s₁' s₂' k₁ k₂ hq hR' hcont

/-- Interpreting a program through a handler `strip` whose runs from every state agree with
`M.handle` leaves `M.runFrom` unchanged. -/
theorem runFrom_interpret_stripNoop (M : Machine I E)
    (strip : (q : ιE) → ProbOracleComp E (E q))
    (hstrip : ∀ q s, M.runFrom (strip q) s = (M.handle q).run s)
    (prog : ProbOracleComp E α) (s : M.State) :
    M.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E) (.inl k)) strip) prog) s =
      M.runFrom prog s := by
  simpa only [sumHandler_query_eq, OracleComp.interpret_query_eq_self, bind_pure] using
    runFrom_interpret_intertwine M M strip ProbOracleComp.query (fun _ => True) Eq prog
      (.of_forall (fun q => by cases q <;> trivial) _) s s rfl pure pure (fun _ _ _ hR => hR ▸ rfl)
      fun q s₁ _ k₁ k₂ _ hR hcont => by
        subst hR
        erw [hstrip q s₁, runFrom_query]
        exact bind_congr fun ⟨r, s'⟩ => hcont r s' s' rfl

/-- Interpreting a program through a handler `strip` whose runs from every state agree with
`M.handle` (for instance, replacing state-preserving `pure` no-op queries with `pure`) leaves
`M.run` unchanged. -/
theorem run_interpret_stripNoop (M : Machine OracleSpec.empty E)
    (strip : (q : ιE) → ProbOracleComp E (E q))
    (hstrip : ∀ q s, M.runFrom (strip q) s = (M.handle q).run s) (prog : ProbOracleComp E α) :
    M.run (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E) (.inl k)) strip) prog) =
      M.run prog := by
  simp only [run, link, runFrom_interpret_stripNoop M strip hstrip]

private theorem closeEval_runFrom_interpret_trap_eq_zero (M : Machine OracleSpec.empty E₁)
    (h : (q : ι) → ProbOracleComp E₁ (O q)) (Inv : ι → Prop) (Trap : M.State → Prop)
    (prog : ProbOracleComp O α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s : M.State) (hs : Trap s) (f : α × M.State → ProbOracleComp OracleSpec.empty β) (y : β)
    (htrap_f : ∀ a s', Trap s' → closeEval (f (a, s')) y = 0)
    (htrap_step : ∀ (q : ι) (s' : M.State) {z : O q × M.State},
      Inv q → Trap s' → z ∈ (closeEval (M.runFrom (h q) s')).support → Trap z.2) :
    closeEval (M.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₁) (.inl k)) h) prog)
        s >>= f) y = 0 := by
  induction prog using OracleComp.induction generalizing s with
  | pure a => exact htrap_f a s hs
  | query_bind q _ ih =>
    simp only [PFunctor.FreeM.bind_eq_bind] at hinv ⊢
    have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hinv
    rcases q with k | q
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler]
      erw [runFrom_bind, runFrom_query_inl, bind_map_left, bind_assoc]
      exact closeEval_bind_eq_zero fun a _ => ih a (hq.2 a) s hs
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler]
      erw [runFrom_bind, bind_assoc]
      exact closeEval_bind_eq_zero fun z hz => ih z.1 (hq.2 z.1) z.2 (htrap_step q s hq.1 hs hz)

/-- Sub-probability (clamped) state-intertwining for `closeEval`: two closed machines `M₁` and
`M₂` sharing a state relation `R`, an absorbing trap predicate `Trap` on `M₁` where `f` assigns
zero mass to `y`, and a query invariant `Inv` satisfy the pointwise `PMF` bound at `y` whenever
each `Inv`-satisfying query preserves the bound across `R` or lands in `Trap`. -/
theorem closeEval_runFrom_interpret_le_intertwine
    (M₁ : Machine OracleSpec.empty E₁) (M₂ : Machine OracleSpec.empty E₂)
    (h₁ : (q : ι) → ProbOracleComp E₁ (O q)) (h₂ : (q : ι) → ProbOracleComp E₂ (O q))
    (Inv : ι → Prop) (R : M₁.State → M₂.State → Prop) (Trap : M₁.State → Prop)
    (prog : ProbOracleComp O α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s₁ : M₁.State) (s₂ : M₂.State) (hR : R s₁ s₂)
    (f : α × M₁.State → ProbOracleComp OracleSpec.empty β)
    (g : α × M₂.State → ProbOracleComp OracleSpec.empty β) (y : β)
    (hfg : ∀ a s₁' s₂', R s₁' s₂' → closeEval (f (a, s₁')) y ≤ closeEval (g (a, s₂')) y)
    (htrap_f : ∀ a s₁', Trap s₁' → closeEval (f (a, s₁')) y = 0)
    (htrap_step : ∀ (q : ι) (s₁' : M₁.State) {z : O q × M₁.State},
      Inv q → Trap s₁' → z ∈ (closeEval (M₁.runFrom (h₁ q) s₁')).support → Trap z.2)
    (hstep : ∀ (q : ι) (s₁' : M₁.State) (s₂' : M₂.State)
      (k₁ : O q × M₁.State → ProbOracleComp OracleSpec.empty β)
      (k₂ : O q × M₂.State → ProbOracleComp OracleSpec.empty β),
      Inv q → R s₁' s₂' →
      (∀ r s₁'' s₂'', R s₁'' s₂'' → closeEval (k₁ (r, s₁'')) y ≤ closeEval (k₂ (r, s₂'')) y) →
      (∀ r s₁'', Trap s₁'' → closeEval (k₁ (r, s₁'')) y = 0) →
      closeEval (M₁.runFrom (h₁ q) s₁' >>= k₁) y ≤ closeEval (M₂.runFrom (h₂ q) s₂' >>= k₂) y) :
    closeEval (M₁.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₁) (.inl k)) h₁) prog)
        s₁ >>= f) y ≤
      closeEval (M₂.runFrom (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E₂) (.inl k)) h₂) prog)
        s₂ >>= g) y := by
  induction prog using OracleComp.induction generalizing s₁ s₂ with
  | pure a => exact hfg a s₁ s₂ hR
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind] at hinv ⊢
    have hq := OracleComp.QueriesSatisfy.liftBind_iff.mp hinv
    rcases q with k | q
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler]
      erw [runFrom_bind, runFrom_bind, runFrom_query_inl M₁, runFrom_query_inl M₂,
        bind_map_left, bind_map_left, bind_assoc, bind_assoc]
      exact closeEval_bind_le _ _ _ y fun a => ih a (hq.2 a) s₁ s₂ hR
    · simp only [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler]
      erw [runFrom_bind, runFrom_bind, bind_assoc, bind_assoc]
      exact hstep q s₁ s₂ _ _ hq.1 hR (fun r s₁'' s₂'' hR' => ih r (hq.2 r) s₁'' s₂'' hR')
        fun r s₁'' hT => closeEval_runFrom_interpret_trap_eq_zero M₁ h₁ Inv Trap (cont r)
          (hq.2 r) s₁'' hT f y htrap_f htrap_step

/-- Direct (uninterpreted) specialization of
`Machine.closeEval_runFrom_interpret_le_intertwine` for two closed machines sharing an exported
interface `E`. -/
theorem closeEval_runFrom_le_intertwine (M₁ M₂ : Machine OracleSpec.empty E)
    (Inv : ιE → Prop) (R : M₁.State → M₂.State → Prop) (Trap : M₁.State → Prop)
    (prog : ProbOracleComp E α)
    (hinv : OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) Inv) prog)
    (s₁ : M₁.State) (s₂ : M₂.State) (hR : R s₁ s₂)
    (f : α × M₁.State → ProbOracleComp OracleSpec.empty β)
    (g : α × M₂.State → ProbOracleComp OracleSpec.empty β) (y : β)
    (hfg : ∀ a s₁' s₂', R s₁' s₂' → closeEval (f (a, s₁')) y ≤ closeEval (g (a, s₂')) y)
    (htrap_f : ∀ a s₁', Trap s₁' → closeEval (f (a, s₁')) y = 0)
    (htrap_step : ∀ (q : ιE) (s₁' : M₁.State) {z : E q × M₁.State},
      Inv q → Trap s₁' → z ∈ (closeEval ((M₁.handle q).run s₁')).support → Trap z.2)
    (hstep : ∀ (q : ιE) (s₁' : M₁.State) (s₂' : M₂.State)
      (k₁ : E q × M₁.State → ProbOracleComp OracleSpec.empty β)
      (k₂ : E q × M₂.State → ProbOracleComp OracleSpec.empty β),
      Inv q → R s₁' s₂' →
      (∀ r s₁'' s₂'', R s₁'' s₂'' → closeEval (k₁ (r, s₁'')) y ≤ closeEval (k₂ (r, s₂'')) y) →
      (∀ r s₁'', Trap s₁'' → closeEval (k₁ (r, s₁'')) y = 0) →
      closeEval ((M₁.handle q).run s₁' >>= k₁) y ≤ closeEval ((M₂.handle q).run s₂' >>= k₂) y) :
    closeEval (M₁.runFrom prog s₁ >>= f) y ≤ closeEval (M₂.runFrom prog s₂ >>= g) y := by
  simpa only [sumHandler_query_eq, OracleComp.interpret_query_eq_self] using
    closeEval_runFrom_interpret_le_intertwine M₁ M₂ ProbOracleComp.query ProbOracleComp.query
      Inv R Trap prog hinv s₁ s₂ hR f g y hfg htrap_f
      (fun q s₁' _ hq hT hz => htrap_step q s₁' hq hT (by erw [runFrom_query] at hz; exact hz))
      fun q s₁' s₂' k₁ k₂ hq hR' hcont htrap_k => by
        erw [runFrom_query, runFrom_query]; exact hstep q s₁' s₂' k₁ k₂ hq hR' hcont htrap_k

end Intertwining

/-- The per-activation call budget `t`: the initial sampler and every activation, from every state,
make at most `t` calls on every path. Private samples and imported calls both count. -/
@[expose] def IsBounded (M : Machine I E) (t : ℕ) : Prop :=
  M.init.IsQueryBounded t ∧ ∀ q s, ((M.handle q).run s).IsQueryBounded t

/-- A larger budget is still a budget. -/
theorem IsBounded.mono {M : Machine I E} {t t' : ℕ} (h : M.IsBounded t) (htt' : t ≤ t') :
    M.IsBounded t' :=
  ⟨h.1.mono htt', fun q s => (h.2 q s).mono htt'⟩

/-- The forwarding machine makes one call per activation and none at initialization. -/
theorem isBounded_id (E : ιE → Type) : (Machine.id E).IsBounded 1 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 1, fun q s => ?_⟩
  change ((fun a => (a, s)) <$> ProbOracleComp.query (spec := E) q).IsQueryBounded 1
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Closing a program with no external imports preserves its query budget. -/
theorem isQueryBounded_closeProgram {program : ProbOracleComp OracleSpec.empty α} {n : ℕ}
    (h : program.IsQueryBounded n) : (closeProgram program).IsQueryBounded n :=
  OracleComp.IsCostBounded.interpret
    (fun q => q.casesOn (fun k => OracleComp.IsCostBounded.query k) fun e => e.elim) h

end Machine

end Cslib.Crypto.Protocols.UC
