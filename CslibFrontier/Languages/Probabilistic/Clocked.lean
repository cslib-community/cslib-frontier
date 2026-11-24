/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Computability.Partrec

/-!
# Clocked oracle programs with unbounded search

An `OracleComp` always halts, so it cannot express unbounded search. A *clocked* oracle program
`ClockedComp spec α` is an `OracleComp` indexed by a fuel bound: run with fuel `k`, it either
finishes with `some a` or gives up with `none`. It is the transformer stack
`ReaderT ℕ (OptionT (OracleComp spec))`, so `pure`, `bind`, `do` notation and the monad laws come
from the transformers. `ClockedComp.query` makes an oracle call and `ClockedComp.rfind` is
unbounded search: with fuel `k` it tries the first `k` arguments, each with fuel `k`.

The partial semantics `ClockedComp.eval o P` answers queries with a partial handler
`o : (q : ι) → Part (spec q)` and returns the result of the least fuel for which the run finishes;
it diverges when an oracle answer on the way is undefined or when no fuel suffices. A run with
fuel `k` is `ClockedComp.attempt o P k`, the ordinary interpretation `OracleComp.interpret` of
the fuel-`k` program in Mathlib's `Part` monad.

The semantics is compositional for *stable* programs (`ClockedComp.Stable`): once a run with some
fuel finishes, every run with more fuel finishes with the same result, and every run with less
fuel is defined and either finishes with that result or runs out. Pure values, queries, bind,
map and `rfind` preserve stability, and on stable programs `eval` sends them to `Part.some`, the
handler, `Part` bind and map, and `Nat.rfind`.

## Main definitions

* `Cslib.ClockedComp`: oracle programs indexed by fuel.
* `Cslib.ClockedComp.query`, `Cslib.ClockedComp.rfind`: an oracle call and unbounded search.
* `Cslib.ClockedComp.attempt`: the run with a given fuel under a partial handler.
* `Cslib.ClockedComp.eval`: the partial result.
* `Cslib.ClockedComp.Stable`: runs with different fuel agree.

## Main results

* `Cslib.ClockedComp.mem_eval_iff`: a stable program returns `a` iff some run finishes with `a`.
* `Cslib.ClockedComp.eval_pure`, `.eval_bind`, `.eval_map`, `.eval_query`, `.eval_rfind`: the
  semantics of the program constructors.
* `Cslib.ClockedComp.Stable.pure`, `.bind`, `.map`, `.query`, `.rfind`: they are stable.
-/

@[expose] public section

namespace Cslib

universe u

/-- Oracle programs indexed by a fuel bound. Run with fuel `k`, a program is a terminating
`OracleComp` that returns `some a` when it finishes and `none` when it runs out of fuel. -/
abbrev ClockedComp {ι : Type u} (spec : OracleSpec.{u, 0} ι) : Type → Type u :=
  ReaderT ℕ (OptionT (OracleComp spec))

namespace ClockedComp

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {α β : Type}

/-- Make one oracle call, whatever the fuel. -/
def query (q : ι) : ClockedComp spec (spec q) := fun _ => OptionT.lift (OracleComp.query q)

/-- The trials `i, i + 1, …, i + r - 1` of an unbounded search, each with fuel `k`. -/
def rfindFrom (p : ℕ → ClockedComp spec Bool) (k : ℕ) : ℕ → ℕ → OptionT (OracleComp spec) ℕ
  | 0, _ => failure
  | r + 1, i => do if ← p i k then pure i else rfindFrom p k r (i + 1)

/-- Unbounded search: the least `n` for which `p n` returns `true`, provided `p m` returns `false`
for every `m < n`. With fuel `k` it tries `p 0, …, p (k - 1)`, each with fuel `k`. -/
def rfind (p : ℕ → ClockedComp spec Bool) : ClockedComp spec ℕ := fun k => rfindFrom p k k 0

/-- The run of `P` with fuel `k`, answering each query with the partial handler `o`. -/
def attempt (o : (q : ι) → Part (spec q)) (P : ClockedComp spec α) (k : ℕ) : Part (Option α) :=
  OracleComp.interpret o (P k).run

/-- The partial result of `P`, answering each query with the partial handler `o`: the result of
the run with the least fuel that finishes. It diverges if no run finishes, or if a run with less
fuel diverges because the handler is undefined on one of its queries. -/
def eval (o : (q : ι) → Part (spec q)) (P : ClockedComp spec α) : Part α :=
  Nat.rfind (fun k => Option.isSome <$> attempt o P k : ℕ →. Bool) >>= fun k =>
    attempt o P k >>= fun r => (r : Part α)

/-- Runs of `P` against the handler `o` with different fuel agree: once the run with fuel `k`
finishes with `a`, the run with any fuel `j` is defined, and finishes with `a` unless `j < k` and
it runs out of fuel. -/
def Stable (o : (q : ι) → Part (spec q)) (P : ClockedComp spec α) : Prop :=
  ∀ k a, some a ∈ attempt o P k →
    ∀ j, attempt o P j = Part.some (some a) ∨ (j < k ∧ attempt o P j = Part.some none)

section Attempt

variable (o : (q : ι) → Part (spec q))

@[simp] theorem attempt_pure (a : α) (k : ℕ) :
    attempt o (pure a : ClockedComp spec α) k = Part.some (some a) := rfl

theorem attempt_bind (P : ClockedComp spec α) (f : α → ClockedComp spec β) (k : ℕ) :
    attempt o (P >>= f) k = (attempt o P k).bind fun r =>
      match r with
      | some a => attempt o (f a) k
      | none => Part.some none := by
  change OracleComp.interpret o (P k >>= fun a => f a k).run = _
  rw [OptionT.run_bind, Option.elimM, OracleComp.interpret_bind]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> rfl

@[simp] theorem attempt_query (q : ι) (k : ℕ) :
    attempt o (query q : ClockedComp spec (spec q)) k = (o q).map some := by
  simp [attempt, query]

theorem attempt_rfindFrom_succ (p : ℕ → ClockedComp spec Bool) (k r i : ℕ) :
    OracleComp.interpret o (rfindFrom p k (r + 1) i).run = (attempt o (p i) k).bind fun x =>
      match x with
      | some true => Part.some (some i)
      | some false => OracleComp.interpret o (rfindFrom p k r (i + 1)).run
      | none => Part.some none := by
  change OracleComp.interpret o
    (p i k >>= fun b => if b then pure i else rfindFrom p k r (i + 1)).run = _
  rw [OptionT.run_bind, Option.elimM, OracleComp.interpret_bind]
  refine congrArg _ (funext fun x => ?_)
  rcases x with _ | _ | _ <;> rfl

theorem attempt_rfind (p : ℕ → ClockedComp spec Bool) (k : ℕ) :
    attempt o (rfind p) k = OracleComp.interpret o (rfindFrom p k k 0).run := rfl

end Attempt

section Stable

variable {o : (q : ι) → Part (spec q)}

/-- A finished run of a stable program stays finished with more fuel. -/
theorem Stable.mono {P : ClockedComp spec α} (hP : Stable o P) {k : ℕ} {a : α}
    (h : some a ∈ attempt o P k) {j : ℕ} (hj : k ≤ j) : attempt o P j = Part.some (some a) :=
  (hP k a h j).resolve_right fun h' => absurd h'.1 (not_lt.2 hj)

/-- A stable program returns `a` exactly when one of its runs finishes with `a`. -/
theorem mem_eval_iff {P : ClockedComp spec α} (hP : Stable o P) {a : α} :
    a ∈ eval o P ↔ ∃ k, some a ∈ attempt o P k := by
  constructor
  · intro h
    obtain ⟨k, -, h⟩ := Part.mem_bind_iff.1 h
    obtain ⟨r, hr, ha⟩ := Part.mem_bind_iff.1 h
    cases r with
    | none => simp at ha
    | some b =>
      obtain rfl : b = a := by simpa [eq_comm] using ha
      exact ⟨k, hr⟩
  · rintro ⟨k, hk⟩
    have hex : ∃ j, attempt o P j = Part.some (some a) := ⟨k, hP.mono hk le_rfl⟩
    classical
    have hm : Nat.find hex ∈ Nat.rfind (fun k => Option.isSome <$> attempt o P k : ℕ →. Bool) := by
      refine Nat.mem_rfind.2 ⟨by simp [Nat.find_spec hex], fun {j} hj => ?_⟩
      rcases hP k a hk j with h | ⟨-, h⟩
      · exact absurd h (Nat.find_min hex hj)
      · simp [h]
    refine Part.mem_bind_iff.2 ⟨_, hm, Part.mem_bind_iff.2 ⟨some a, ?_, by simp⟩⟩
    rw [Nat.find_spec hex]
    exact Part.mem_some _

theorem Stable.pure (a : α) : Stable o (pure a : ClockedComp spec α) := by
  intro k b h j
  obtain rfl := Option.some.inj (Part.mem_some_iff.1 h)
  exact Or.inl rfl

theorem Stable.bind {P : ClockedComp spec α} {f : α → ClockedComp spec β} (hP : Stable o P)
    (hf : ∀ a, Stable o (f a)) : Stable o (P >>= f) := by
  intro k b h j
  rw [attempt_bind] at h ⊢
  obtain ⟨r, hr, hb⟩ := Part.mem_bind_iff.1 h
  cases r with
  | none => simp at hb
  | some a =>
    rcases hP k a hr j with h₁ | ⟨hjk, h₁⟩
    · rw [h₁, Part.bind_some]
      exact hf a k b hb j
    · rw [h₁, Part.bind_some]
      exact Or.inr ⟨hjk, rfl⟩

theorem Stable.map {P : ClockedComp spec α} (hP : Stable o P) (f : α → β) :
    Stable o (f <$> P) := by
  rw [map_eq_bind_pure_comp]
  exact hP.bind fun a => .pure (f a)

theorem Stable.query (q : ι) : Stable o (query q : ClockedComp spec (spec q)) := by
  intro k a h j
  rw [attempt_query, Part.mem_map_iff] at h
  obtain ⟨a', ha, h'⟩ := h
  obtain rfl := Option.some.inj h'
  rw [attempt_query, Part.eq_some_iff.2 ha, Part.map_some]
  exact Or.inl rfl

section Rfind

variable {p : ℕ → ClockedComp spec Bool} {k : ℕ}

private theorem mem_rfindFrom {n : ℕ} :
    ∀ {r i}, some n ∈ OracleComp.interpret o (rfindFrom p k r i).run →
      i ≤ n ∧ n < i + r ∧ (∀ m, i ≤ m → m < n → some false ∈ attempt o (p m) k) ∧
        some true ∈ attempt o (p n) k
  | 0, i, h => by simp [rfindFrom] at h
  | r + 1, i, h => by
    rw [attempt_rfindFrom_succ] at h
    obtain ⟨x, hx, h⟩ := Part.mem_bind_iff.1 h
    rcases x with _ | _ | _
    · simp at h
    · obtain ⟨hin, hnr, hlt, hn⟩ := mem_rfindFrom h
      refine ⟨by omega, by omega, fun m him hmn => ?_, hn⟩
      rcases Nat.eq_or_lt_of_le him with rfl | him
      · exact hx
      · exact hlt m him hmn
    · obtain rfl : i = n := by simpa [eq_comm] using h
      exact ⟨le_rfl, by omega, fun m him hmn => absurd hmn (not_lt.2 him), hx⟩

private theorem rfindFrom_eq_some {n : ℕ}
    (hlt : ∀ m < n, attempt o (p m) k = Part.some (some false))
    (hn : attempt o (p n) k = Part.some (some true)) :
    ∀ {r i}, i ≤ n → n < i + r →
      OracleComp.interpret o (rfindFrom p k r i).run = Part.some (some n)
  | 0, i, hin, hnr => by omega
  | r + 1, i, hin, hnr => by
    rw [attempt_rfindFrom_succ]
    rcases Nat.eq_or_lt_of_le hin with rfl | hin
    · rw [hn, Part.bind_some]
    · rw [hlt i hin, Part.bind_some]
      exact rfindFrom_eq_some hlt hn (by omega) (by omega)

private theorem rfindFrom_eq_some_or_none {n : ℕ}
    (h : ∀ m ≤ n, attempt o (p m) k = Part.some (some (decide (m = n))) ∨
      attempt o (p m) k = Part.some none) :
    ∀ {r i}, i ≤ n → OracleComp.interpret o (rfindFrom p k r i).run = Part.some (some n) ∨
      OracleComp.interpret o (rfindFrom p k r i).run = Part.some none
  | 0, i, _ => Or.inr rfl
  | r + 1, i, hin => by
    rw [attempt_rfindFrom_succ]
    rcases h i hin with hi | hi <;> rw [hi, Part.bind_some]
    · by_cases hin' : i = n
      · subst hin'
        simp
      · simp only [hin', decide_false]
        exact rfindFrom_eq_some_or_none h (by omega)
    · exact Or.inr rfl

theorem Stable.rfind (hp : ∀ i, Stable o (p i)) : Stable o (rfind p) := by
  intro k n h j
  rw [attempt_rfind] at h
  obtain ⟨-, hnk, hlt, hn⟩ := mem_rfindFrom (n := n) h
  have hval : ∀ m ≤ n, some (decide (m = n)) ∈ attempt o (p m) k := fun m hm => by
    rcases Nat.eq_or_lt_of_le hm with rfl | hm
    · simpa using hn
    · simpa [hm.ne] using hlt m (Nat.zero_le _) hm
  rcases lt_or_ge j k with hjk | hjk
  · rw [attempt_rfind]
    rcases rfindFrom_eq_some_or_none (n := n) (k := j)
        (fun m hm => (hp m k _ (hval m hm) j).imp_right And.right) (Nat.zero_le n) with
      h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨hjk, h'⟩
  · refine Or.inl ?_
    rw [attempt_rfind]
    refine rfindFrom_eq_some (fun m hm => ?_) ?_ (Nat.zero_le n) (by omega)
    · simpa [hm.ne] using (hp m).mono (hval m hm.le) hjk
    · simpa using (hp n).mono (hval n le_rfl) hjk

end Rfind

end Stable

section Eval

variable (o : (q : ι) → Part (spec q))

@[simp] theorem eval_pure (a : α) : eval o (pure a : ClockedComp spec α) = Part.some a := by
  ext b
  rw [mem_eval_iff (.pure a)]
  simp [eq_comm]

theorem eval_bind {P : ClockedComp spec α} {f : α → ClockedComp spec β} (hP : Stable o P)
    (hf : ∀ a, Stable o (f a)) : eval o (P >>= f) = (eval o P).bind fun a => eval o (f a) := by
  ext b
  rw [mem_eval_iff (hP.bind hf), Part.mem_bind_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [attempt_bind] at hk
    obtain ⟨r, hr, hb⟩ := Part.mem_bind_iff.1 hk
    cases r with
    | none => simp at hb
    | some a => exact ⟨a, (mem_eval_iff hP).2 ⟨k, hr⟩, (mem_eval_iff (hf a)).2 ⟨k, hb⟩⟩
  · rintro ⟨a, ha, hb⟩
    obtain ⟨k₁, h₁⟩ := (mem_eval_iff hP).1 ha
    obtain ⟨k₂, h₂⟩ := (mem_eval_iff (hf a)).1 hb
    refine ⟨max k₁ k₂, ?_⟩
    rw [attempt_bind, hP.mono h₁ (le_max_left _ _), Part.bind_some]
    change some b ∈ attempt o (f a) (max k₁ k₂)
    rw [(hf a).mono h₂ (le_max_right _ _)]
    exact Part.mem_some _

theorem eval_map {P : ClockedComp spec α} (hP : Stable o P) (f : α → β) :
    eval o (f <$> P) = (eval o P).map f := by
  rw [map_eq_bind_pure_comp, eval_bind o (f := pure ∘ f) hP fun a => .pure (f a)]
  simp [Part.bind_some_eq_map]

@[simp] theorem eval_query (q : ι) : eval o (query q : ClockedComp spec (spec q)) = o q := by
  ext a
  rw [mem_eval_iff (.query q)]
  simp

theorem eval_rfind {p : ℕ → ClockedComp spec Bool} (hp : ∀ i, Stable o (p i)) :
    eval o (rfind p) = Nat.rfind (fun i => eval o (p i) : ℕ →. Bool) := by
  ext n
  rw [mem_eval_iff (.rfind hp)]
  refine Iff.trans ?_ Nat.mem_rfind.symm
  constructor
  · rintro ⟨k, hk⟩
    rw [attempt_rfind] at hk
    obtain ⟨-, -, hlt, hn⟩ := mem_rfindFrom hk
    exact ⟨(mem_eval_iff (hp n)).2 ⟨k, hn⟩, fun {m} hm =>
      (mem_eval_iff (hp m)).2 ⟨k, hlt m (Nat.zero_le _) hm⟩⟩
  · rintro ⟨hn, hlt⟩
    obtain ⟨kn, hkn⟩ := (mem_eval_iff (hp n)).1 hn
    choose kf hkf using fun m : Fin n => (mem_eval_iff (hp m)).1 (hlt m.2)
    let K := max (max (Finset.univ.sup kf) kn) (n + 1)
    refine ⟨K, ?_⟩
    have hlt' : ∀ m < n, attempt o (p m) K = Part.some (some false) := fun m hm =>
      (hp m).mono (hkf ⟨m, hm⟩) (le_trans
        (Finset.le_sup (f := kf) (Finset.mem_univ (⟨m, hm⟩ : Fin n)))
        (le_trans (le_max_left _ _) (le_max_left _ _)))
    have hn' : attempt o (p n) K = Part.some (some true) :=
      (hp n).mono hkn (le_trans (le_max_right _ _) (le_max_left _ _))
    rw [attempt_rfind, rfindFrom_eq_some hlt' hn' (Nat.zero_le n) (by omega)]
    exact Part.mem_some _

end Eval

end ClockedComp

end Cslib
