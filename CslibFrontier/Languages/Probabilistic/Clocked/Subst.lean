/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Clocked
public import CslibFrontier.Languages.Probabilistic.Sum

/-!
# Reductions between oracle interfaces as handlers

A *handler* `h : (q : ι) → ClockedComp spec' (spec q)` answers each query of the interface `spec`
by a clocked program over another interface `spec'`. Substituting it into a clocked program `P`
over `spec` gives a clocked program `P.subst h` over `spec'`. Against a partial handler `o` for
`spec'` it computes what `P` computes against the handler `fun q => eval o (h q)`
(`ClockedComp.eval_subst`), and it is stable when `P` and the handler programs are
(`ClockedComp.Stable.subst`).

`ClockedComp.Implements h o o'` says that `h` computes the partial handler `o'` from `o` by stable
programs. Queries implement every handler (`Implements.query`), substitution composes
implementations (`Implements.trans`), and implementations of two interfaces combine on their sum
(`Implements.sumHandler`).

## Main definitions

* `Cslib.ClockedComp.subst`: substitute a handler into a clocked program.
* `Cslib.ClockedComp.Implements`: a handler computes one partial handler from another.

## Main results

* `Cslib.ClockedComp.eval_subst`: `eval o (P.subst h) = eval (fun q => eval o (h q)) P`.
* `Cslib.ClockedComp.Stable.subst`: substitution preserves stability.
* `Cslib.ClockedComp.Implements.query`, `.trans`, `.sumHandler`, `.eval_subst`.

## Implementation notes

The run of `P.subst h` with fuel `j` cannot simply run `P` and the handler programs with the same
fuel `j`: a stable program may make more queries as its fuel grows, each needing more fuel from
the handler, so that no single fuel suffices. Instead, the run with fuel `j` tries `P` with fuel
`0, …, j - 1` in turn, answering its queries by the handler programs run with fuel `j`
(`ClockedComp.substRun`), and returns the first result. Each try is the ordinary interpretation
`OracleComp.interpret` of the fuel-`k` program in `OptionT (OracleComp spec')`, so a handler that
runs out of fuel ends the try.

`Implements` asks for nothing beyond stability: every partial handler is implemented by constant
and diverging programs, so it is a reducibility only together with a restriction on the programs,
such as a computable dialogue over `natOracleSpec` (`Cslib.ClockedComp.dialogue`), under which it
is transitive through codes (`Nat.RecursiveIn.Code.exists_clockedComp_trans`).
-/

@[expose] public section

namespace Cslib

universe u u' u''

namespace ClockedComp

variable {ι : Type u} {κ : Type u'} {spec : OracleSpec.{u, 0} ι} {spec' : OracleSpec.{u', 0} κ}
  {α β : Type}

/-- The run of `P` with fuel `k`, its queries answered by the handler programs run with fuel `j`.
It runs out of fuel if `P` or one of the handler programs does. -/
def substRun (P : ClockedComp spec α) (h : (q : ι) → ClockedComp spec' (spec q)) (k j : ℕ) :
    OptionT (OracleComp spec') α :=
  OracleComp.interpret (fun q => h q j) (P k).run >>= fun r => OptionT.mk (pure r)

/-- The tries `substRun P h i j` for `i = k, …, k + r - 1`, returning the first result. -/
def substFrom (P : ClockedComp spec α) (h : (q : ι) → ClockedComp spec' (spec q)) (j : ℕ) :
    ℕ → ℕ → OptionT (OracleComp spec') α
  | 0, _ => failure
  | r + 1, k => OptionT.mk do
    match ← (substRun P h k j).run with
    | some a => pure (some a)
    | none => (substFrom P h j r (k + 1)).run

/-- Substitute the handler `h` into `P`: answer each query `q` of `P` by the program `h q`. With
fuel `j` it tries `P` with fuel `0, …, j - 1`, each with the handler programs run with fuel `j`,
and returns the first result. -/
def subst (P : ClockedComp spec α) (h : (q : ι) → ClockedComp spec' (spec q)) :
    ClockedComp spec' α :=
  fun j => substFrom P h j j 0

/-- The handler `h` implements the partial handler `o'` for `spec` against the partial handler
`o` for `spec'`: each `h q` is stable against `o` and computes `o' q`. -/
def Implements (h : (q : ι) → ClockedComp spec' (spec q)) (o : (q : κ) → Part (spec' q))
    (o' : (q : ι) → Part (spec q)) : Prop :=
  ∀ q, Stable o (h q) ∧ eval o (h q) = o' q

/-! ### Runs answered by partial runs -/

section Runs

/-- A program run in `OptionT Part`, each query `q` answered by `R q`, where `none` means that
the answer ran out of fuel. -/
private abbrev runWith (R : (q : ι) → Part (Option (spec q))) (T : OracleComp spec β) :
    Part (Option β) :=
  (OracleComp.interpret (m := OptionT Part) (fun q => OptionT.mk (R q)) T).run

private theorem runWith_liftBind (R : (q : ι) → Part (Option (spec q))) (q : ι)
    (cont : spec q → OracleComp spec β) :
    runWith R (PFunctor.FreeM.liftBind q cont) = (R q).bind fun r =>
      match r with
      | some v => runWith R (cont v)
      | none => Part.some none := by
  change (OptionT.mk (R q) >>= fun v =>
    OracleComp.interpret (m := OptionT Part) (fun q => OptionT.mk (R q)) (cont v)).run = _
  rw [OptionT.run_bind, Option.elimM, OptionT.run_mk]
  exact congrArg _ (funext fun r => by cases r <;> rfl)

private theorem interpret_liftBind (o : (q : ι) → Part (spec q)) (q : ι)
    (cont : spec q → OracleComp spec β) :
    OracleComp.interpret o (PFunctor.FreeM.liftBind q cont) =
      (o q).bind fun v => OracleComp.interpret o (cont v) := rfl

variable {o : (q : ι) → Part (spec q)}

/-- A finished run answered by sound partial answers is a run against `o`. -/
private theorem mem_interpret_of_runWith {R : (q : ι) → Part (Option (spec q))}
    (hR : ∀ q v, some v ∈ R q → v ∈ o q) {T : OracleComp spec β} {b : β}
    (h : some b ∈ runWith R T) : b ∈ OracleComp.interpret o T := by
  induction T with
  | pure b' => simpa using Option.some.inj (Part.mem_some_iff.1 h)
  | liftBind q cont ih =>
    rw [runWith_liftBind] at h
    rw [interpret_liftBind]
    obtain ⟨_ | v, hr, h⟩ := Part.mem_bind_iff.1 h
    · simp at h
    · exact Part.mem_bind_iff.2 ⟨v, hR q v hr, ih v h⟩

/-- A finished run stays finished when every finished answer stays the same. -/
private theorem runWith_eq_of_mono {R R' : (q : ι) → Part (Option (spec q))}
    (hR : ∀ q v, some v ∈ R q → R' q = Part.some (some v)) {T : OracleComp spec β} {b : β}
    (h : some b ∈ runWith R T) : runWith R' T = Part.some (some b) := by
  induction T with
  | pure b' => exact congrArg Part.some (Part.mem_some_iff.1 h).symm
  | liftBind q cont ih =>
    rw [runWith_liftBind] at h ⊢
    obtain ⟨_ | v, hr, h⟩ := Part.mem_bind_iff.1 h
    · simp at h
    · rw [hR q v hr, Part.bind_some]; exact ih v h

/-- If the run against `o` returns `b` and every answer of `R` to a defined query of `o` is that
answer or runs out of fuel, then the run answered by `R` returns `b` or runs out of fuel. -/
private theorem runWith_eq_or {R : (q : ι) → Part (Option (spec q))}
    (hR : ∀ q v, v ∈ o q → R q = Part.some (some v) ∨ R q = Part.some none)
    {T : OracleComp spec β} {b : β} (h : b ∈ OracleComp.interpret o T) :
    runWith R T = Part.some (some b) ∨ runWith R T = Part.some none := by
  induction T with
  | pure b' => exact Or.inl (by rw [Part.mem_some_iff.1 h]; rfl)
  | liftBind q cont ih =>
    rw [interpret_liftBind] at h
    obtain ⟨v, hv, h⟩ := Part.mem_bind_iff.1 h
    rw [runWith_liftBind]
    rcases hR q v hv with hq | hq <;> rw [hq, Part.bind_some]
    exacts [ih v h, Or.inr rfl]

/-- If the run against `o` returns `b` and the answers `R j` approximate `o` from below as `j`
grows, then the run answered by `R j` returns `b` for some `j`. -/
private theorem exists_mem_runWith {R : ℕ → (q : ι) → Part (Option (spec q))}
    (hex : ∀ q v, v ∈ o q → ∃ j, some v ∈ R j q)
    (hmono : ∀ q v j j', j ≤ j' → some v ∈ R j q → R j' q = Part.some (some v))
    {T : OracleComp spec β} {b : β} (h : b ∈ OracleComp.interpret o T) :
    ∃ j, some b ∈ runWith (R j) T := by
  induction T with
  | pure b' => exact ⟨0, by rw [Part.mem_some_iff.1 h]; exact Part.mem_some _⟩
  | liftBind q cont ih =>
    rw [interpret_liftBind] at h
    obtain ⟨v, hv, h⟩ := Part.mem_bind_iff.1 h
    obtain ⟨j₁, h₁⟩ := ih v h
    obtain ⟨j₀, h₀⟩ := hex q v hv
    refine ⟨max j₀ j₁, ?_⟩
    rw [runWith_liftBind, hmono q v j₀ _ (le_max_left _ _) h₀, Part.bind_some]
    change some b ∈ runWith (R (max j₀ j₁)) (cont v)
    rw [runWith_eq_of_mono (fun q' v' => hmono q' v' j₁ _ (le_max_right _ _)) h₁]
    exact Part.mem_some _

end Runs

/-! ### The runs of a substituted program -/

section Subst

variable (o : (q : κ) → Part (spec' q)) (P : ClockedComp spec α)
  (h : (q : ι) → ClockedComp spec' (spec q))

/-- The try of `P` with fuel `k` and handler fuel `j`, against `o`. -/
private abbrev tryWith (k j : ℕ) : Part (Option α) :=
  (runWith (fun q => attempt o (h q) j) (P k).run).map Option.join

private theorem attempt_substFrom_succ (j r k : ℕ) :
    OracleComp.interpret o (substFrom P h j (r + 1) k).run = (tryWith o P h k j).bind fun x =>
      match x with
      | some a => Part.some (some a)
      | none => OracleComp.interpret o (substFrom P h j r (k + 1)).run := by
  have hint (T : OracleComp spec (Option α)) :
      OracleComp.interpret o (OracleComp.interpret (fun q => h q j) T).run =
        runWith (fun q => attempt o (h q) j) T := by
    induction T with
    | pure _ => rfl
    | liftBind q cont ih =>
      rw [runWith_liftBind]
      change OracleComp.interpret o (h q j >>= fun v => OracleComp.interpret _ (cont v)).run = _
      rw [OptionT.run_bind, Option.elimM, OracleComp.interpret_bind]
      exact congrArg _ (funext fun | none => rfl | some v => ih v)
  have hrun : OracleComp.interpret o (substRun P h k j).run = tryWith o P h k j := by
    rw [substRun, OptionT.run_bind, Option.elimM, OracleComp.interpret_bind, hint]
    change Part.bind _ _ = Part.map _ _
    rw [← Part.bind_some_eq_map]
    exact congrArg _ (funext fun r => by rcases r with _ | _ | _ <;> rfl)
  change OracleComp.interpret o ((substRun P h k j).run >>= _) = _
  rw [OracleComp.interpret_bind, hrun]
  exact congrArg _ (funext fun x => by cases x <;> rfl)

variable {o P h}

private theorem mem_substFrom {j : ℕ} {a : α} :
    ∀ {r k}, some a ∈ OracleComp.interpret o (substFrom P h j r k).run →
      ∃ i < k + r, some a ∈ tryWith o P h i j
  | 0, k, hm => by simp [substFrom] at hm
  | r + 1, k, hm => by
    rw [attempt_substFrom_succ] at hm
    obtain ⟨_ | b, hx, hm⟩ := Part.mem_bind_iff.1 hm
    · obtain ⟨i, hi, h⟩ := mem_substFrom hm; exact ⟨i, by omega, h⟩
    · obtain rfl : b = a := by simpa [eq_comm] using hm
      exact ⟨k, by omega, hx⟩

private theorem substFrom_eq_or {j : ℕ} {a : α}
    (ht : ∀ i, tryWith o P h i j = Part.some (some a) ∨ tryWith o P h i j = Part.some none) :
    ∀ r k, OracleComp.interpret o (substFrom P h j r k).run = Part.some (some a) ∨
      OracleComp.interpret o (substFrom P h j r k).run = Part.some none
  | 0, _ => Or.inr rfl
  | r + 1, k => by
    rw [attempt_substFrom_succ]
    rcases ht k with hk | hk <;> rw [hk, Part.bind_some]
    exacts [Or.inl rfl, substFrom_eq_or ht r (k + 1)]

private theorem substFrom_eq_some {j i : ℕ} {a : α}
    (ht : ∀ i, tryWith o P h i j = Part.some (some a) ∨ tryWith o P h i j = Part.some none)
    (hi : tryWith o P h i j = Part.some (some a)) :
    ∀ {r k}, k ≤ i → i < k + r →
      OracleComp.interpret o (substFrom P h j r k).run = Part.some (some a)
  | 0, _, _, _ => by omega
  | r + 1, k, hki, hir => by
    rw [attempt_substFrom_succ]
    rcases Nat.eq_or_lt_of_le hki with rfl | hki
    · rw [hi, Part.bind_some]
    · rcases ht k with hk | hk <;> rw [hk, Part.bind_some]
      exact substFrom_eq_some ht hi hki (by omega)

variable (hh : ∀ q, Stable o (h q))
include hh

/-- A finished try is a run of `P` against the composed handler. -/
private theorem mem_attempt_of_mem_tryWith {i j : ℕ} {a : α} (ht : some a ∈ tryWith o P h i j) :
    some a ∈ attempt (fun q => eval o (h q)) P i := by
  obtain ⟨_ | _ | b, hr, ⟨⟩⟩ := (Part.mem_map_iff _).1 ht
  exact mem_interpret_of_runWith (fun q v hv => (mem_eval_iff (hh q)).2 ⟨j, hv⟩) hr

/-- A finished try stays finished with more handler fuel. -/
private theorem tryWith_mono {i j j' : ℕ} {a : α} (ht : some a ∈ tryWith o P h i j)
    (hj : j ≤ j') : tryWith o P h i j' = Part.some (some a) := by
  obtain ⟨_ | _ | b, hr, ⟨⟩⟩ := (Part.mem_map_iff _).1 ht
  rw [tryWith, runWith_eq_of_mono (fun q v hv => (hh q).mono hv hj) hr, Part.map_some]
  rfl

/-- Once `P` finishes with `a` against the composed handler, every try finishes with `a` or runs
out of fuel. -/
private theorem tryWith_eq_or_of_mem (hP : Stable (fun q => eval o (h q)) P) {i₀ : ℕ} {a : α}
    (ha : some a ∈ attempt (fun q => eval o (h q)) P i₀) (i j : ℕ) :
    tryWith o P h i j = Part.some (some a) ∨ tryWith o P h i j = Part.some none := by
  have hR (q v) (hv : v ∈ eval o (h q)) :=
    let ⟨k, hk⟩ := (mem_eval_iff (hh q)).1 hv; (hh q k v hk j).imp_right And.right
  rcases (hP i₀ a ha i).imp_right And.right with e | e <;>
    rcases runWith_eq_or hR (e ▸ Part.mem_some _) with e' | e' <;>
    simp [tryWith, e']

/-- Substitution preserves stability: if `P` is stable against the composed handler and every
handler program is stable against `o`, then `P.subst h` is stable against `o`. -/
theorem Stable.subst (hP : Stable (fun q => eval o (h q)) P) : Stable o (P.subst h) := by
  intro j a ha j'
  obtain ⟨i, hij, hi⟩ := mem_substFrom ha
  have ht := tryWith_eq_or_of_mem hh hP (mem_attempt_of_mem_tryWith hh hi)
  rcases le_or_gt j j' with hjj | hjj
  · exact Or.inl (substFrom_eq_some (ht · j') (tryWith_mono hh hi hjj) (Nat.zero_le i) (by omega))
  · exact (substFrom_eq_or (ht · j') j' 0).imp_right fun e => ⟨hjj, e⟩

/-- **Substitution of a handler.** If `P` is stable against the composed handler and every
handler program is stable against `o`, then `P.subst h` computes against `o` what `P` computes
when each query `q` is answered by `eval o (h q)`. -/
theorem eval_subst (hP : Stable (fun q => eval o (h q)) P) :
    eval o (P.subst h) = eval (fun q => eval o (h q)) P := by
  ext a
  rw [mem_eval_iff (hP.subst hh), mem_eval_iff hP]
  refine ⟨fun ⟨j, hj⟩ => let ⟨i, _, hi⟩ := mem_substFrom hj; ⟨i, mem_attempt_of_mem_tryWith hh hi⟩,
    fun ⟨i, hi⟩ => ?_⟩
  obtain ⟨j, hj⟩ := exists_mem_runWith (R := fun j q => attempt o (h q) j)
    (fun q v hv => (mem_eval_iff (hh q)).1 hv) (fun q _ _ _ hjj' hv => (hh q).mono hv hjj') hi
  refine ⟨max j (i + 1), ?_⟩
  rw [attempt, subst, substFrom_eq_some (tryWith_eq_or_of_mem hh hP hi · _)
    (tryWith_mono hh ((Part.mem_map_iff _).2 ⟨_, hj, rfl⟩) (le_max_left _ _)) (Nat.zero_le i)
    (by omega)]
  exact Part.mem_some _

end Subst

/-! ### Implementations -/

namespace Implements

variable {o : (q : κ) → Part (spec' q)} {o' : (q : ι) → Part (spec q)}
  {h : (q : ι) → ClockedComp spec' (spec q)}

/-- Run against an implementation, the substituted program computes what the program computes
against the implemented handler. -/
theorem eval_subst (hh : Implements h o o') {P : ClockedComp spec α} (hP : Stable o' P) :
    eval o (P.subst h) = eval o' P := by
  cases funext fun q => (hh q).2
  exact ClockedComp.eval_subst (fun q => (hh q).1) hP

theorem stable_subst (hh : Implements h o o') {P : ClockedComp spec α} (hP : Stable o' P) :
    Stable o (P.subst h) := by
  cases funext fun q => (hh q).2
  exact Stable.subst (fun q => (hh q).1) hP

/-- Each handler implements itself by its queries. -/
theorem query (o : (q : ι) → Part (spec q)) :
    Implements (fun q => (ClockedComp.query q : ClockedComp spec (spec q))) o o :=
  fun q => ⟨.query q, eval_query o q⟩

/-- Implementations compose by substitution. -/
theorem trans {ι'' : Type u''} {spec'' : OracleSpec.{u'', 0} ι''}
    {o'' : (q : ι'') → Part (spec'' q)} {h' : (q : ι'') → ClockedComp spec (spec'' q)}
    (hh' : Implements h' o' o'') (hh : Implements h o o') :
    Implements (fun q => (h' q).subst h) o o'' :=
  fun q => ⟨hh.stable_subst (hh' q).1, (hh.eval_subst (hh' q).1).trans (hh' q).2⟩

/-- Implementations of two interfaces over the same interface implement their sum. -/
theorem sumHandler {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
    {o₁ : (q : ι₁) → Part (spec₁ q)} {o₂ : (q : ι₂) → Part (spec₂ q)}
    {h₁ : (q : ι₁) → ClockedComp spec' (spec₁ q)} {h₂ : (q : ι₂) → ClockedComp spec' (spec₂ q)}
    (hh₁ : Implements h₁ o o₁) (hh₂ : Implements h₂ o o₂) :
    Implements (OracleComp.sumHandler h₁ h₂) o (OracleComp.sumHandler o₁ o₂)
  | .inl q => hh₁ q
  | .inr q => hh₂ q

end Implements

end ClockedComp

end Cslib
