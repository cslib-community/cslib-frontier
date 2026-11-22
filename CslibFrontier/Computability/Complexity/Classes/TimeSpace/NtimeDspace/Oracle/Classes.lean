/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.Machine

/-!
# Relativized time and space classes

For an oracle `A : Set (List Bool)`, the classes `TIMEO A t`, `NTIMEO A t` and `SPACEO A s` of
languages over `{0,1}` decided by deterministic or nondeterministic oracle machines
(`Cslib.Complexity.NtimeDspace.Oracle.OracleTM`, `Cslib.Complexity.NtimeDspace.Oracle.OracleNTM`)
with finitely many states, within
time `O(t n)` or space `O(s n)`, the query tape counting toward space. They copy Complexitylib's
`Cslib.Complexity.DTIME`, `Cslib.Complexity.NTIME` and `Cslib.Complexity.DSPACE` (instances
encoded by `Turing.MultiTapeTM.encBits`) clause for clause: bounds `c₁ * t n + c₂`, binary
alphabet, finite control, output `[true]` or `[false]`, and for `SPACEO` some time bound in the
length of the input.

## Sanity checks

An oracle machine that never queries and never writes its query tape (`IsOracleFree`) is a CSLib
machine (`OracleNTM.plain`, `OracleTM.plainTM`), step for step, and every CSLib machine is such
an oracle machine (`MultiTapeNTM.toOracle`, `MultiTapeTM.toOracle`). The time bounds, the space
bounds and acceptance agree. So, for every oracle `A`, restricting the relativized classes to
oracle-free machines gives exactly Complexitylib's classes
(`DTIME_eq_oracleFree`, `NTIME_eq_oracleFree`, `DSPACE_eq_oracleFree`), and the unrelativized
classes are contained in the relativized ones (`DTIME_subset_TIMEO`, `NTIME_subset_NTIMEO`,
`DSPACE_subset_SPACEO`). Deterministic oracle time is contained in nondeterministic oracle time
(`TIMEO_subset_NTIMEO`) and in oracle space (`TIMEO_subset_SPACEO`).

## Main definitions

* `Cslib.Complexity.NtimeDspace.Oracle.TIMEO`, `Cslib.Complexity.NtimeDspace.Oracle.NTIMEO`,
`Cslib.Complexity.NtimeDspace.Oracle.SPACEO`.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleNTM.IsOracleFree`,
`Cslib.Complexity.NtimeDspace.Oracle.OracleTM.IsOracleFree`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing

variable {k : ℕ} {State : Type*} {x : List Bool}

/-! ### Oracle-free machines -/

namespace OracleNTM

variable (M : OracleNTM k State) (A : Set (List Bool))

/-- `M` never uses its oracle: every permitted instruction is an ordinary action writing nothing on
the query tape. -/
def IsOracleFree : Prop := ∀ q i w a, M.Tr q i w a → ∃ b, a = .step b none

/-- The CSLib machine of the ordinary actions of `M` that write nothing on the query tape. -/
def plain : MultiTapeNTM k Bool State := ⟨M.q₀, fun q i w a => M.Tr q i w (.step a none)⟩

variable {M A}

/-- An oracle-free step does not change the query tape. -/
lemma query_of_step (hM : M.IsOracleFree) {c c' : OCfg k State x} (h : M.Step A c c') :
    c'.query = c.query := by
  unfold Step at h
  split at h
  · rw [h]
  · obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨b, rfl⟩ := hM _ _ _ _ ha
    simp

/-- Along an oracle-free path the query tape does not change. -/
lemma query_runPath (hM : M.IsOracleFree) (p : M.RunPath A x) (n : Fin (p.length + 1)) :
    (p n).query = p.head.query := by
  obtain ⟨n, hn⟩ := n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih (by omega)]
    exact query_of_step hM (p.step ⟨n, by omega⟩)

/-- Forgetting the query tape maps oracle-free steps to steps of the plain machine. -/
def forgetHom (hM : M.IsOracleFree) : (M.stepRel A x).Hom (M.plain.stepRel x) where
  toFun c := c.tapes
  map_rel' {c c'} h := by
    change M.Step A c c' at h
    change M.plain.Step c.tapes c'.tapes
    unfold Step at h
    unfold MultiTapeNTM.Step
    split at h
    · next hq => rw [hq, h]
    · next q hq =>
      rw [hq]
      obtain ⟨a, ha, rfl⟩ := h
      obtain ⟨b, rfl⟩ := hM _ _ _ _ ha
      exact ⟨b, ha, rfl⟩

/-- An empty query tape maps steps of the plain machine to steps of `M`. -/
def liftHom : (M.plain.stepRel x).Hom (M.stepRel A x) where
  toFun c := ⟨c, []⟩
  map_rel' {c c'} h := by
    change M.plain.Step c c' at h
    change M.Step A ⟨c, []⟩ ⟨c', []⟩
    unfold MultiTapeNTM.Step at h
    unfold Step
    split at h
    · next hq => simp only [hq]; rw [h]
    · next q hq =>
      simp only [hq]
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨.step a none, ha, by simp⟩

/-- The plain path of an oracle-free computation path. -/
def ComputationPath.forget (hM : M.IsOracleFree) (p : M.ComputationPath A x) :
    M.plain.ComputationPath x :=
  ⟨p.toRunPath.map (forgetHom hM), by simp [p.head_eq, initCfg, forgetHom]; rfl⟩

/-- The oracle path of a plain computation path. -/
def liftPath (q : M.plain.ComputationPath x) : M.ComputationPath A x :=
  ⟨q.toRunPath.map liftHom, by simp [q.head_eq, initCfg, liftHom]; rfl⟩

lemma pathSpace_eq (hM : M.IsOracleFree) (p : M.ComputationPath A x) :
    pathSpace p.toRunPath = (p.forget hM).space := by
  have hq : ∀ n, (p.toRunPath n).query = [] := fun n => by
    rw [query_runPath hM, p.head_eq]; rfl
  have h0 : (Finset.univ.sup fun n => (p.toRunPath n).query.length) = 0 := by simp [hq]
  rw [pathSpace, h0, add_zero]
  rfl

lemma runsInTime_iff (hM : M.IsOracleFree) {t : ℕ} :
    M.RunsInTime A x t ↔ M.plain.RunsInTime x t := by
  constructor
  · intro h q hq
    exact h (liftPath q) hq
  · intro h p hp
    exact h (p.forget hM) hp

lemma runsInSpace_iff (hM : M.IsOracleFree) {s : ℕ} :
    M.RunsInSpace A x s ↔ M.plain.RunsInSpace x s := by
  constructor
  · intro h q
    have := h (liftPath q)
    rw [pathSpace_eq hM] at this
    exact this
  · intro h p
    rw [pathSpace_eq hM]
    exact h _

lemma accepts_iff (hM : M.IsOracleFree) : M.Accepts A x ↔ M.plain.Accepts x := by
  constructor
  · rintro ⟨p, hh, ho⟩
    exact ⟨p.forget hM, hh, ho⟩
  · rintro ⟨q, hh, ho⟩
    exact ⟨liftPath q, hh, ho⟩

end OracleNTM

/-- A CSLib nondeterministic machine as an oracle machine that never uses its oracle. -/
def _root_.Turing.MultiTapeNTM.toOracle (N : MultiTapeNTM k Bool State) : OracleNTM k State :=
  ⟨N.q₀, fun q i w a => ∃ b, a = .step b none ∧ N.Tr q i w b⟩

lemma isOracleFree_toOracle (N : MultiTapeNTM k Bool State) : N.toOracle.IsOracleFree :=
  fun _ _ _ _ ⟨b, hb, _⟩ => ⟨b, hb⟩

lemma plain_toOracle (N : MultiTapeNTM k Bool State) : N.toOracle.plain = N := by
  obtain ⟨q₀, Tr⟩ := N
  simp only [OracleNTM.plain, MultiTapeNTM.toOracle, MultiTapeNTM.mk.injEq, true_and]
  funext q i w a
  apply propext
  constructor
  · rintro ⟨b, hb, h⟩
    cases hb
    exact h
  · exact fun h => ⟨a, rfl, h⟩

namespace OracleTM

variable (M : OracleTM k State) (A : Set (List Bool))

/-- `M` never uses its oracle. -/
def IsOracleFree : Prop := ∀ q i w, ∃ b, M.tr q i w = .step b none

/-- The ordinary action of an instruction; a query is replaced by halting. -/
def _root_.Cslib.Complexity.NtimeDspace.Oracle.OAction.action : OAction k State →
    Turing.Action k Bool State
  | .step a _ => a
  | .ask _ _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- The CSLib machine of the ordinary actions of `M`. -/
noncomputable def plainTM : MultiTapeTM k Bool State :=
  MultiTapeTM.ofTr M.q₀ fun q i w => (M.tr q i w).action

variable {M A}

lemma toNTM_isOracleFree (hM : M.IsOracleFree) : M.toNTM.IsOracleFree := by
  rintro q i w a rfl
  exact hM q i w

lemma plainTM_eq (hM : M.IsOracleFree) : M.plainTM.toMultiTapeNTM = M.toNTM.plain := by
  simp only [plainTM, MultiTapeTM.ofTr, OracleNTM.plain, toNTM, MultiTapeNTM.mk.injEq, true_and]
  funext q i w a
  obtain ⟨b, hb⟩ := hM q i w
  simp only [hb, OAction.action, eq_iff_iff]
  constructor
  · rintro rfl; rfl
  · intro h; cases h; rfl

/-- An oracle-free step is a step of the plain machine. -/
lemma tapes_step (hM : M.IsOracleFree) (c : OCfg k State x) :
    (M.step A c).tapes = M.plainTM.step c.tapes := by
  cases hq : c.tapes.state with
  | none => rw [step_of_halted _ _ hq, MultiTapeTM.step_of_halt hq]
  | some q =>
    rw [step_of_state _ _ hq, MultiTapeTM.step_of_state hq]
    obtain ⟨b, hb⟩ := hM q c.tapes.inputSymbol c.tapes.workTapeSymbols
    simp [hb, plainTM, OAction.action]

lemma tapes_run (hM : M.IsOracleFree) (t : ℕ) :
    (M.run A x t).tapes = M.plainTM.runFrom (M.plainTM.initCfg x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run, runFrom_succ, tapes_step hM, ← run, ih, MultiTapeTM.runFrom_succ]

/-- **An oracle-free deterministic oracle machine decides exactly as its plain machine computes
the indicator**, within the same time and space bounds, whatever the oracle. -/
theorem decidesIn_iff (hM : M.IsOracleFree) {L : Set (List Bool)} {T S : List Bool → ℕ} :
    M.DecidesIn A L T S ↔ ∀ x, M.plainTM.ComputesInTimeAndSpace x [MultiTapeTM.indicator L x]
      (T x) (S x) := by
  refine forall_congr' fun x => ?_
  unfold MultiTapeTM.ComputesInTimeAndSpace MultiTapeTM.Computes
  rw [OracleNTM.runsInTime_iff (toNTM_isOracleFree hM),
    OracleNTM.runsInSpace_iff (toNTM_isOracleFree hM), ← plainTM_eq hM]
  simp only [tapes_run hM]
  tauto

end OracleTM

/-- A CSLib deterministic machine as an oracle machine that never uses its oracle. -/
noncomputable def _root_.Turing.MultiTapeTM.toOracle (tm : MultiTapeTM k Bool State) :
    OracleTM k State :=
  ⟨tm.q₀, fun q i w => .step (tm.tr q i w) none⟩

lemma isOracleFree_toOracleTM (tm : MultiTapeTM k Bool State) : tm.toOracle.IsOracleFree :=
  fun q i w => ⟨tm.tr q i w, rfl⟩

lemma plainTM_toOracle (tm : MultiTapeTM k Bool State) :
    tm.toOracle.plainTM.toMultiTapeNTM = tm.toMultiTapeNTM := by
  rw [OracleTM.plainTM_eq (isOracleFree_toOracleTM tm)]
  obtain ⟨⟨q₀, Tr⟩, hdet⟩ := tm
  simp only [OracleNTM.plain, OracleTM.toNTM, MultiTapeTM.toOracle, MultiTapeNTM.mk.injEq,
    true_and]
  funext q i w a
  apply propext
  constructor
  · intro h
    cases h
    exact (MultiTapeTM.tr_iff (tm := ⟨⟨q₀, Tr⟩, hdet⟩)).mpr rfl
  · intro h
    rw [MultiTapeTM.tr_iff.mp h]

/-- The CSLib computation of a machine is the computation of its oracle-free oracle form. -/
lemma computesInTimeAndSpace_toOracle (tm : MultiTapeTM k Bool State) {x y : List Bool}
    {t s : ℕ} : tm.toOracle.plainTM.ComputesInTimeAndSpace x y t s ↔
      tm.ComputesInTimeAndSpace x y t s := by
  have hrun : ∀ u, tm.toOracle.plainTM.runFrom (tm.toOracle.plainTM.initCfg x) u =
      tm.runFrom (tm.initCfg x) u := by
    intro u
    induction u with
    | zero => rfl
    | succ u ih =>
      rw [MultiTapeTM.runFrom_succ, MultiTapeTM.runFrom_succ, ih]
      apply MultiTapeTM.step_iff.mp
      rw [plainTM_toOracle]
      exact MultiTapeTM.step_iff.mpr rfl
  unfold MultiTapeTM.ComputesInTimeAndSpace MultiTapeTM.Computes
  simp only [hrun]
  change _ ∧ MultiTapeNTM.RunsInTime tm.toOracle.plainTM.toMultiTapeNTM x t ∧
      MultiTapeNTM.RunsInSpace tm.toOracle.plainTM.toMultiTapeNTM x s ↔ _
  rw [plainTM_toOracle]

/-! ### The relativized classes -/

/-- **Deterministic time relative to `A`**: the languages decided within time `c₁ * t n + c₂` by a
deterministic oracle machine with finitely many states, within some space bound in `n`, as
`Cslib.Complexity.DTIME`. -/
def TIMEO (A : Set (List Bool)) (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State) (M : OracleTM k State) (s : ℕ → ℕ),
    M.DecidesIn A L (fun x => c₁ * t x.length + c₂) fun x => s x.length}

/-- **Nondeterministic time relative to `A`**: the languages decided within time `c₁ * t n + c₂`
by a nondeterministic oracle machine with finitely many states (every computation path of that
many steps has halted, and `x ∈ L` exactly when some computation path halts with output `[true]`),
as `Cslib.Complexity.NTIME`. -/
def NTIMEO (A : Set (List Bool)) (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State) (M : OracleNTM k State),
    ∀ x, M.RunsInTime A x (c₁ * t x.length + c₂) ∧ (x ∈ L ↔ M.Accepts A x)}

/-- **Deterministic space relative to `A`**: the languages decided within space `c₁ * s n + c₂`,
counting the work tapes and the query tape, by a deterministic oracle machine with finitely many
states, within some time bound in `n`, as `Cslib.Complexity.DSPACE`. -/
def SPACEO (A : Set (List Bool)) (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State) (M : OracleTM k State) (t : ℕ → ℕ),
    M.DecidesIn A L (fun x => t x.length) fun x => c₁ * s x.length + c₂}

/-! ### Agreement with the unrelativized classes -/

open Cslib.Complexity MultiTapeTM

/-- **Sanity check (deterministic time).** For every oracle `A`, the languages that oracle-free
deterministic oracle machines decide within time `O(t)` are exactly `DTIME[t]`. -/
theorem DTIME_eq_oracleFree (A : Set (List Bool)) (t : ℕ → ℕ) :
    DTIME encBits t = {L | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (M : OracleTM k State) (s : ℕ → ℕ), M.IsOracleFree ∧
        M.DecidesIn A L (fun x => c₁ * t x.length + c₂) fun x => s x.length} := by
  ext L
  constructor
  · rintro ⟨c₁, c₂, s, k, State, hfin, tm, htm⟩
    refine ⟨c₁, c₂, k, State, hfin, tm.toOracle, s, isOracleFree_toOracleTM tm,
      (OracleTM.decidesIn_iff (isOracleFree_toOracleTM tm)).mpr fun x => ?_⟩
    rw [computesInTimeAndSpace_toOracle]
    exact htm x
  · rintro ⟨c₁, c₂, k, State, hfin, M, s, hM, h⟩
    exact ⟨c₁, c₂, s, k, State, hfin, M.plainTM, (OracleTM.decidesIn_iff hM).mp h⟩

/-- **Sanity check (deterministic space).** For every oracle `A`, the languages that oracle-free
deterministic oracle machines decide within space `O(s)` are exactly `DSPACE[s]`. -/
theorem DSPACE_eq_oracleFree (A : Set (List Bool)) (s : ℕ → ℕ) :
    DSPACE encBits s = {L | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (M : OracleTM k State) (t : ℕ → ℕ), M.IsOracleFree ∧
        M.DecidesIn A L (fun x => t x.length) fun x => c₁ * s x.length + c₂} := by
  ext L
  constructor
  · rintro ⟨c₁, c₂, t, k, State, hfin, tm, htm⟩
    refine ⟨c₁, c₂, k, State, hfin, tm.toOracle, t, isOracleFree_toOracleTM tm,
      (OracleTM.decidesIn_iff (isOracleFree_toOracleTM tm)).mpr fun x => ?_⟩
    rw [computesInTimeAndSpace_toOracle]
    exact htm x
  · rintro ⟨c₁, c₂, k, State, hfin, M, t, hM, h⟩
    exact ⟨c₁, c₂, t, k, State, hfin, M.plainTM, (OracleTM.decidesIn_iff hM).mp h⟩

/-- **Sanity check (nondeterministic time).** For every oracle `A`, the languages that oracle-free
nondeterministic oracle machines decide within time `O(t)` are exactly `NTIME[t]`. -/
theorem NTIME_eq_oracleFree (A : Set (List Bool)) (t : ℕ → ℕ) :
    NTIME encBits t = {L | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (M : OracleNTM k State), M.IsOracleFree ∧
        ∀ x, M.RunsInTime A x (c₁ * t x.length + c₂) ∧ (x ∈ L ↔ M.Accepts A x)} := by
  ext L
  constructor
  · rintro ⟨c₁, c₂, k, State, hfin, N, hN⟩
    refine ⟨c₁, c₂, k, State, hfin, N.toOracle, isOracleFree_toOracle N, fun x => ?_⟩
    rw [OracleNTM.runsInTime_iff (isOracleFree_toOracle N),
      OracleNTM.accepts_iff (isOracleFree_toOracle N), plain_toOracle]
    exact hN x
  · rintro ⟨c₁, c₂, k, State, hfin, M, hM, h⟩
    refine ⟨c₁, c₂, k, State, hfin, M.plain, fun x => ?_⟩
    rw [← OracleNTM.runsInTime_iff hM, ← OracleNTM.accepts_iff hM]
    exact h x

theorem DTIME_subset_TIMEO (A : Set (List Bool)) (t : ℕ → ℕ) : DTIME encBits t ⊆ TIMEO A t := by
  rw [DTIME_eq_oracleFree A]
  rintro L ⟨c₁, c₂, k, State, hfin, M, s, -, h⟩
  exact ⟨c₁, c₂, k, State, hfin, M, s, h⟩

theorem NTIME_subset_NTIMEO (A : Set (List Bool)) (t : ℕ → ℕ) :
    NTIME encBits t ⊆ NTIMEO A t := by
  rw [NTIME_eq_oracleFree A]
  rintro L ⟨c₁, c₂, k, State, hfin, M, -, h⟩
  exact ⟨c₁, c₂, k, State, hfin, M, h⟩

theorem DSPACE_subset_SPACEO (A : Set (List Bool)) (s : ℕ → ℕ) :
    DSPACE encBits s ⊆ SPACEO A s := by
  rw [DSPACE_eq_oracleFree A]
  rintro L ⟨c₁, c₂, k, State, hfin, M, t, -, h⟩
  exact ⟨c₁, c₂, k, State, hfin, M, t, h⟩

/-! ### Deterministic oracle time within nondeterministic oracle time -/

theorem TIMEO_subset_NTIMEO (A : Set (List Bool)) (t : ℕ → ℕ) : TIMEO A t ⊆ NTIMEO A t := by
  rintro L ⟨c₁, c₂, k, State, hfin, M, s, h⟩
  refine ⟨c₁, c₂, k, State, hfin, M.toNTM, fun x => ⟨(h x).1, ?_⟩⟩
  obtain ⟨-, -, u, hu, hout⟩ := h x
  constructor
  · intro hx
    refine ⟨OracleTM.ComputationPath.ofRun M A x u, hu, ?_⟩
    rw [OracleTM.last_ofRun, hout]
    simp [indicator, hx]
  · rintro ⟨p, hp, hpo⟩
    rw [OracleTM.last_eq_run] at hp hpo
    have e : M.run A x (max u p.length) = M.run A x u := M.run_eq_of_halted A hu (by omega)
    have e' : M.run A x (max u p.length) = M.run A x p.length :=
      M.run_eq_of_halted A hp (by omega)
    rw [← e', e, hout] at hpo
    by_contra hx
    simp [indicator, hx] at hpo

/-! ### Deterministic oracle time within oracle space -/

namespace OracleTM

variable {M : OracleTM k State} {A : Set (List Bool)}

/-- **Time bounds space**: a deterministic oracle machine halting within `T` steps uses at most
`T + 1` cells of each work tape and holds queries of length at most `T`. -/
theorem runsInSpace_of_runsInTime {T : ℕ} (h : M.toNTM.RunsInTime A x T) :
    M.toNTM.RunsInSpace A x (k * (T + 1) + T) := by
  have hT : (M.run A x T).tapes.Halted := by
    have := h (ComputationPath.ofRun M A x T) le_rfl
    rwa [last_ofRun] at this
  have hrun : ∀ n, M.run A x n = M.run A x (min n T) := by
    intro n
    rcases le_total n T with hn | hn
    · rw [min_eq_left hn]
    · rw [min_eq_right hn, M.run_eq_of_halted A hT hn]
  intro p
  have hp : ∀ n : Fin (p.length + 1), p.toRunPath n = M.run A x (min n T) := by
    intro n
    rw [runPath_apply, p.head_eq, ← hrun]
    rfl
  unfold OracleNTM.pathSpace
  have hw : ∀ i : Fin k, (Finset.univ.image fun n : Fin (p.length + 1) =>
      (p.toRunPath n).tapes.workTapePos i).card ≤ T + 1 := by
    intro i
    refine (Finset.card_le_card (t := Finset.univ.image fun n : Fin (T + 1) =>
      (M.run A x n).tapes.workTapePos i) fun z hz => ?_).trans
      (Finset.card_image_le.trans (by simp))
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨⟨min n T, by omega⟩, Finset.mem_univ _, by rw [hp]⟩
  have hq : (Finset.univ.sup fun n : Fin (p.length + 1) => (p.toRunPath n).query.length) ≤ T :=
    Finset.sup_le fun n _ => by
      rw [hp]
      have := M.length_query_runFrom_le A (M.toNTM.initCfg x) (min n T)
      simp only [OracleNTM.initCfg, List.length_nil, zero_add] at this
      exact this.trans (min_le_right _ _)
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hw i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

end OracleTM

/-- `TIME^A[t] ⊆ SPACE^A[t]` for every oracle `A`. -/
theorem TIMEO_subset_SPACEO (A : Set (List Bool)) (t : ℕ → ℕ) : TIMEO A t ⊆ SPACEO A t := by
  rintro L ⟨c₁, c₂, k, State, hfin, M, s, h⟩
  refine ⟨(k + 1) * c₁, (k + 1) * c₂ + k, k, State, hfin, M, fun n => c₁ * t n + c₂, fun x => ?_⟩
  obtain ⟨ht, -, hout⟩ := h x
  refine ⟨ht, (OracleTM.runsInSpace_of_runsInTime ht).mono ?_, hout⟩
  simp only
  ring_nf
  omega

end Cslib.Complexity.NtimeDspace.Oracle
