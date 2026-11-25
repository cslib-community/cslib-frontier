/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Control.Monad.Memoize
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Map

/-!
# Lawful state lenses for composite stateful oracle handlers

Cryptographic games and reductions often combine several stateful components—an association-list
cache, a ciphertext log, a query countdown, a sticky Boolean bad flag—inside a single documented
`structure` rather than nested anonymous tuples (`((j, (false, [])), queried)`). A
`StateLens S Part` packages a lawful getter/setter pair (`get_set`, `set_get`, `set_set`) focusing
on one field or sub-record `Part` inside `S`.

`StateLens.zoom` lifts any `StateT Part m` action or oracle handler onto `S` while leaving the
unfocused fields invariant:

* `StateLens.run_interpret_zoom` and `StateLens.runWith_zoom` commute adaptive execution with
  zooming, using all three lens laws to preserve the unfocused frame of the initial state.
* `StateLens.identicalUntilBad_zoom` and `StateLens.probIdenticalUntilBad_zoom` transport
  `IdenticalUntilBad` from `Part` to `S`.
* `StateLens.zoom_memoize_of_some`, `StateLens.zoom_memoize_of_none`, and
  `StateLens.length_get_of_mem_support_zoom_memoize` lift `memoize` and its cache-growth bound onto
  a `structure` state.
* `StateLens.latch` turns any Boolean field `flag : StateLens S Bool` into a monotone sticky bad
  flag directly on `S`, transporting `IdenticalUntilBad`, marginal projection (`runWith_latch_map`),
  and linear/triangular union bounds (`toOuterMeasure_latch_le`,
  `toOuterMeasure_latch_choose_two_le`) without packing `S` into `Base × Bool`.

## Main definitions

* `Cslib.StateLens`: lawful lens (`get`, `set`, `get_set`, `set_get`, `set_set`).
* `Cslib.StateLens.zoom`: lift a `StateT Part m` computation onto `S`.
* `Cslib.StateLens.Bad`, `Cslib.StateLens.latch`: monotone Boolean bad-flag latching along a
  `StateLens S Bool`.

## Main results

* `Cslib.StateLens.run_interpret_zoom`, `Cslib.StateLens.runWith_zoom`: adaptive execution of a
  zoomed handler preserves the outer state frame.
* `Cslib.StateLens.identicalUntilBad_zoom`, `Cslib.StateLens.probIdenticalUntilBad_zoom`:
  `IdenticalUntilBad` lifts across `zoom`.
* `Cslib.StateLens.zoom_memoize_of_some`, `Cslib.StateLens.zoom_memoize_of_none`,
  `Cslib.StateLens.length_get_of_mem_support_zoom_memoize`: zoomed `memoize` characterization and
  cache-size growth.
* `Cslib.StateLens.latch_of_false`, `Cslib.StateLens.identicalUntilBad_latch`,
  `Cslib.StateLens.probIdenticalUntilBad_latch`, `Cslib.StateLens.runWith_latch_map`,
  `Cslib.StateLens.toOuterMeasure_latch_le`,
  `Cslib.StateLens.toOuterMeasure_latch_choose_two_le`: named-structure bad-flag hops and union
  bounds.
-/

public section

namespace Cslib

open Probability
open scoped ENNReal

universe u v

/-- A lawful lens focusing on a `Part` component inside a composite state `S`. -/
structure StateLens (S Part : Type*) where
  /-- Read the focused component from `S`. -/
  get : S → Part
  /-- Replace the focused component in `S`. -/
  set : S → Part → S
  /-- Reading immediately after writing recovers the written component. -/
  get_set (s : S) (p : Part) : get (set s p) = p
  /-- Writing back the current component leaves the composite state unchanged. -/
  set_get (s : S) : set s (get s) = s
  /-- Writing twice overwrites the first write. -/
  set_set (s : S) (p₁ p₂ : Part) : set (set s p₁) p₂ = set s p₂

attribute [simp] StateLens.get_set StateLens.set_get StateLens.set_set

namespace StateLens

section Combinators

/-- Identity lens on `S`. -/
@[expose] protected def id (S : Type*) : StateLens S S where
  get s := s
  set _ p := p
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Compose an outer lens `S → Mid` with an inner lens `Mid → Part`. -/
@[expose] def comp {S Mid Part : Type*} (outer : StateLens S Mid) (inner : StateLens Mid Part) :
    StateLens S Part where
  get s := inner.get (outer.get s)
  set s p := outer.set s (inner.set (outer.get s) p)
  get_set s p := by simp
  set_get s := by simp
  set_set s p₁ p₂ := by simp

/-- Lens focusing on the first component of a pair `A × B`. -/
@[expose] def fst (A B : Type*) : StateLens (A × B) A where
  get p := p.1
  set p a := (a, p.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens focusing on the second component of a pair `A × B`. -/
@[expose] def snd (A B : Type*) : StateLens (A × B) B where
  get p := p.2
  set p b := (p.1, b)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Fixing the surrounding composite state `s`, `l.set s` is injective. -/
theorem set_injective {S Part : Type*} (l : StateLens S Part) (s : S) :
    Function.Injective (l.set s) := fun _ _ h => by simpa only [l.get_set] using congrArg l.get h

/-- Lift a `StateT Part m` action onto the composite state `S`, leaving everything outside `l`
unchanged. -/
@[expose] def zoom {S Part : Type u} {m : Type u → Type v} [Functor m]
    (l : StateLens S Part) {α : Type u} (act : StateT Part m α) : StateT S m α :=
  fun s => (fun x => (x.1, l.set s x.2)) <$> act (l.get s)

end Combinators

/-! ### Zooming oracle executions and `IdenticalUntilBad` -/

section ZoomOracle

variable {ι Query S Part α : Type} {spec : ι → Type} {qspec : Query → Type}

/-- Running an `OracleComp` against a zoomed `PMF` handler executes against the inner handler from
`l.get s` and writes the final inner state back into the initial frame `s`. -/
theorem run_interpret_zoom (l : StateLens S Part)
    (handler : (q : ι) → StateT Part PMF (spec q)) (program : OracleComp spec α) (s : S) :
    (OracleComp.interpret (fun q => l.zoom (handler q)) program).run s =
      ((OracleComp.interpret handler program).run (l.get s)).map
        (fun x => (x.1, l.set s x.2)) := by
  simpa only [l.set_get] using (OracleComp.run_interpret_map_state handler
    (fun q => l.zoom (handler q)) (l.set s)
    (fun q p => by simp [zoom, PMF.monad_map_eq_map]) program (l.get s)).symm

/-- Running a `ProbOracleComp` with `runWith` against a zoomed `PMF` handler executes against the
inner handler from `l.get s` and writes the final inner state back into `s`. -/
theorem runWith_zoom (l : StateLens S Part)
    (handler : (q : Query) → StateT Part PMF (qspec q)) (program : ProbOracleComp qspec α)
    (s : S) :
    ProbOracleComp.runWith (fun q => l.zoom (handler q)) program s =
      (ProbOracleComp.runWith handler program (l.get s)).map (fun x => (x.1, l.set s x.2)) := by
  simpa only [l.set_get] using (ProbOracleComp.runWith_map_state handler
    (fun q => l.zoom (handler q)) (l.set s)
    (fun q p => by simp [zoom, PMF.monad_map_eq_map]) program (l.get s)).symm

/-- `OracleComp.IdenticalUntilBad` lifts along a lawful `StateLens`. -/
theorem identicalUntilBad_zoom {first second : (q : ι) → StateT Part PMF (spec q)}
    {bad : Part → Prop} (l : StateLens S Part)
    (h : OracleComp.IdenticalUntilBad first second bad) :
    OracleComp.IdenticalUntilBad
      (fun q => l.zoom (first q)) (fun q => l.zoom (second q)) (fun s => bad (l.get s)) where
  agree q s hs a s' hs' := by
    let emb : spec q × Part → spec q × S := fun x => (x.1, l.set s x.2)
    have hemb : Function.Injective emb := fun _ _ hxy =>
      Prod.ext (Prod.mk.inj hxy).1 (l.set_injective s (Prod.mk.inj hxy).2)
    change ((first q (l.get s)).map emb) (a, s') = ((second q (l.get s)).map emb) (a, s')
    by_cases hex : ∃ p', s' = l.set s p'
    · obtain ⟨p', rfl⟩ := hex
      change ((first q (l.get s)).map emb) (emb (a, p')) =
        ((second q (l.get s)).map emb) (emb (a, p'))
      rw [PMF.map_apply_of_injective _ hemb, PMF.map_apply_of_injective _ hemb]
      exact h.agree q (l.get s) hs a p' (by rwa [l.get_set] at hs')
    · have hzero (μ : PMF (spec q × Part)) : (μ.map emb) (a, s') = 0 :=
        (PMF.apply_eq_zero_iff ..).mpr fun hmem =>
          let ⟨x, _, hx⟩ := (PMF.mem_support_map_iff ..).mp hmem
          hex ⟨x.2, (Prod.mk.inj hx).2.symm⟩
      rw [hzero, hzero]
  absorb_first q s hs x hx := by
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff ..).mp hx
    simpa only [l.get_set] using h.absorb_first q (l.get s) hs y hy
  absorb_second q s hs x hx := by
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff ..).mp hx
    simpa only [l.get_set] using h.absorb_second q (l.get s) hs y hy

/-- `ProbOracleComp.IdenticalUntilBad` lifts along a lawful `StateLens`. -/
theorem probIdenticalUntilBad_zoom {first second : (q : Query) → StateT Part PMF (qspec q)}
    {bad : Part → Prop} (l : StateLens S Part)
    (h : ProbOracleComp.IdenticalUntilBad first second bad) :
    ProbOracleComp.IdenticalUntilBad
      (fun q => l.zoom (first q)) (fun q => l.zoom (second q)) (fun s => bad (l.get s)) :=
  (l.identicalUntilBad_zoom h.toOracleComp).probOracleComp

end ZoomOracle

/-! ### Zooming `memoize` onto a composite state -/

section ZoomMemoize

variable {S Key Value : Type u} {m : Type u → Type v}

/-- On a cache hit, `l.zoom (memoize compute key)` returns the cached value and leaves the entire
composite state `s` unchanged. -/
theorem zoom_memoize_of_some [Monad m] [LawfulMonad m] [BEq Key]
    (l : StateLens S (List (Key × Value)))
    (compute : Key → m Value) (key : Key) (s : S) (value : Value)
    (h : (l.get s).lookup key = some value) :
    l.zoom (memoize compute key) s = pure (value, s) := by
  simp [zoom, memoize_of_some compute key (l.get s) value h]

/-- On a cache miss, `l.zoom (memoize compute key)` runs `compute key` and prepends `(key, value)`
to `l.get s` inside `s`. -/
theorem zoom_memoize_of_none [Monad m] [LawfulMonad m] [BEq Key]
    (l : StateLens S (List (Key × Value)))
    (compute : Key → m Value) (key : Key) (s : S)
    (h : (l.get s).lookup key = none) :
    l.zoom (memoize compute key) s =
      (fun value => (value, l.set s ((key, value) :: l.get s))) <$> compute key := by
  simp [zoom, memoize_of_none compute key (l.get s) h]

/-- Every supported transition of `l.zoom (memoize compute key)` in `PMF` grows the focused cache by
at most one entry. -/
theorem length_get_of_mem_support_zoom_memoize {S Key Value : Type} [BEq Key]
    (l : StateLens S (List (Key × Value)))
    (compute : Key → PMF Value) (key : Key) (s : S) {out : Value × S}
    (hout : out ∈ ((l.zoom (memoize compute key) s : PMF (Value × S))).support) :
    (l.get out.2).length ≤ (l.get s).length + 1 := by
  cases h : (l.get s).lookup key with
  | some value =>
    rw [l.zoom_memoize_of_some compute key s value h, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hout
    subst hout
    exact Nat.le_succ _
  | none =>
    rw [l.zoom_memoize_of_none compute key s h, PMF.monad_map_eq_map,
      PMF.mem_support_map_iff] at hout
    obtain ⟨value, -, rfl⟩ := hout
    simp

end ZoomMemoize

/-! ### Sticky Boolean bad-flag latching on a named structure state -/

section Latch

variable {ι Query S Base α : Type} {spec : ι → Type} {qspec : Query → Type}

/-- Bad-state predicate testing whether a focused Boolean field `flag : StateLens S Bool` is
`true`. -/
abbrev Bad (flag : StateLens S Bool) (s : S) : Prop := flag.get s = true

/-- Latch a Boolean bad-flag field `flag : StateLens S Bool` across oracle calls: evaluate `step` on
the unflagged state `flag.set s false` and combine the prior flag `flag.get s` with the per-call
indicator `flag.get s'` via `||`. -/
@[expose] noncomputable def latch (flag : StateLens S Bool)
    (step : (q : ι) → S → PMF (spec q × S)) (q : ι) : StateT S PMF (spec q) :=
  fun s => (step q (flag.set s false)).map fun x => (x.1, flag.set x.2 (flag.get s || flag.get x.2))

/-- From an unflagged state (`flag.get s = false`), one call of `flag.latch step` has the exact law
`step q s`. -/
@[simp] theorem latch_of_false (flag : StateLens S Bool)
    (step : (q : ι) → S → PMF (spec q × S)) (q : ι) {s : S} (hs : flag.get s = false) :
    flag.latch step q s = step q s := by
  have hs_set : flag.set s false = s := by rw [← hs, flag.set_get]
  have hid : (fun x : spec q × S => (x.1, flag.set x.2 (false || flag.get x.2))) = _root_.id := by
    funext ⟨a, s'⟩
    simp
  simp only [latch, hs, hs_set, hid, PMF.map_id]

/-- `flag.Bad` is absorbing for every handler built with `flag.latch`. -/
theorem absorb_latch (flag : StateLens S Bool) (step : (q : ι) → S → PMF (spec q × S)) :
    ∀ q s, flag.Bad s → ∀ x ∈ (flag.latch step q s).support, flag.Bad x.2 := by
  intro q s hs x hx
  simp only [latch, hs, Bool.true_or, PMF.mem_support_map_iff] at hx
  obtain ⟨_, -, rfl⟩ := hx
  simp [Bad]

/-- Two `flag.latch` handlers satisfy `OracleComp.IdenticalUntilBad` whenever their underlying
step kernels assign equal mass to unflagged transitions from unflagged states. -/
theorem identicalUntilBad_latch (flag : StateLens S Bool)
    (step₁ step₂ : (q : ι) → S → PMF (spec q × S))
    (hagree : ∀ q s, flag.get s = false → ∀ a s', flag.get s' = false →
      step₁ q s (a, s') = step₂ q s (a, s')) :
    OracleComp.IdenticalUntilBad (flag.latch step₁) (flag.latch step₂) flag.Bad where
  agree q s hs a s' hs' := by
    have hbs := Bool.eq_false_iff.mpr hs
    have hbs' := Bool.eq_false_iff.mpr hs'
    rw [flag.latch_of_false step₁ q hbs, flag.latch_of_false step₂ q hbs]
    exact hagree q s hbs a s' hbs'
  absorb_first := flag.absorb_latch step₁
  absorb_second := flag.absorb_latch step₂

/-- Two `flag.latch` handlers satisfy `ProbOracleComp.IdenticalUntilBad` whenever their underlying
step kernels assign equal mass to unflagged transitions from unflagged states. -/
theorem probIdenticalUntilBad_latch (flag : StateLens S Bool)
    (step₁ step₂ : (q : Query) → S → PMF (qspec q × S))
    (hagree : ∀ q s, flag.get s = false → ∀ a s', flag.get s' = false →
      step₁ q s (a, s') = step₂ q s (a, s')) :
    ProbOracleComp.IdenticalUntilBad (flag.latch step₁) (flag.latch step₂) flag.Bad :=
  (flag.identicalUntilBad_latch step₁ step₂ hagree).probOracleComp

/-- Projecting a `flag.latch step` execution along `proj : S → Base` that ignores `flag` recovers
`ProbOracleComp.runWith unflagged` whenever each unflagged step projects to `unflagged`. -/
theorem runWith_latch_map (flag : StateLens S Bool)
    (step : (q : Query) → S → PMF (qspec q × S))
    (unflagged : (q : Query) → StateT Base PMF (qspec q))
    (proj : S → Base) (hproj : ∀ s b, proj (flag.set s b) = proj s)
    (hstep : ∀ q s, flag.get s = false → (step q s).map (Prod.map _root_.id proj) =
      unflagged q (proj s))
    (program : ProbOracleComp qspec α) (s : S) :
    (ProbOracleComp.runWith (flag.latch step) program s).map (Prod.map _root_.id proj) =
      ProbOracleComp.runWith unflagged program (proj s) := by
  refine ProbOracleComp.runWith_map_state (flag.latch step) unflagged proj (fun q st => ?_)
    program s
  have hmap : (flag.latch step q st).map (fun (a, s') => (a, proj s')) =
      (step q (flag.set st false)).map (Prod.map _root_.id proj) := by
    simp only [latch, PMF.map_comp]
    congr 1 with ⟨a, s'⟩ : 1
    simp [hproj]
  rw [hmap, hstep q (flag.set st false) (flag.get_set st false), hproj st false]

/-- Linear bad-event union bound for `ProbOracleComp.runWith (flag.latch step)`, stated directly in
terms of unflagged `step` transitions (`flag.get s = false`). -/
theorem toOuterMeasure_latch_le (flag : StateLens S Bool)
    {step : (q : Query) → S → PMF (qspec q × S)}
    (cost : Query → ℕ) (budget : S → ℝ≥0∞) (δ : ℝ≥0∞)
    (hstep : ∀ q s, flag.get s = false →
      (step q s).toOuterMeasure {x | flag.Bad x.2} ≤ cost q * budget s)
    (hgrow : ∀ q s, flag.get s = false → ∀ x ∈ (step q s).support, flag.get x.2 = false →
      budget x.2 ≤ budget s + δ)
    {program : ProbOracleComp qspec α} {n k : ℕ} (hn : program.IsQueryBounded n)
    (hk : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) program k)
    {s : S} (hs : flag.get s = false) :
    (ProbOracleComp.runWith (flag.latch step) program s).toOuterMeasure {x | flag.Bad x.2} ≤
      k * (budget s + n * δ) :=
  ProbOracleComp.toOuterMeasure_bad_le cost budget δ
    (fun q st hst => by
      simpa [flag.latch_of_false step q (Bool.eq_false_iff.mpr hst)] using
        hstep q st (Bool.eq_false_iff.mpr hst))
    (fun q st hst x hx hgood => hgrow q st (Bool.eq_false_iff.mpr hst) x
      (by rwa [flag.latch_of_false step q (Bool.eq_false_iff.mpr hst)] at hx)
      (Bool.eq_false_iff.mpr hgood)) hn hk (Bool.eq_false_iff.mp hs)

/-- Triangular (`n * size s + n.choose 2`) bad-event union bound for
`ProbOracleComp.runWith (flag.latch step)`, stated directly in terms of unflagged `step`
transitions (`flag.get s = false`). -/
theorem toOuterMeasure_latch_choose_two_le (flag : StateLens S Bool)
    {step : (q : Query) → S → PMF (qspec q × S)}
    (size : S → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, flag.get s = false →
      (step q s).toOuterMeasure {x | flag.Bad x.2} ≤ size s * δ)
    (hgrow : ∀ q s, flag.get s = false → ∀ x ∈ (step q s).support, flag.get x.2 = false →
      size x.2 ≤ size s + 1)
    {program : ProbOracleComp qspec α} {n : ℕ} (hn : program.IsQueryBounded n)
    {s : S} (hs : flag.get s = false) :
    (ProbOracleComp.runWith (flag.latch step) program s).toOuterMeasure {x | flag.Bad x.2} ≤
      (n * size s + n.choose 2 : ℕ) * δ :=
  ProbOracleComp.toOuterMeasure_bad_choose_two_le size δ
    (fun q st hst => by
      simpa [flag.latch_of_false step q (Bool.eq_false_iff.mpr hst)] using
        hstep q st (Bool.eq_false_iff.mpr hst))
    (fun q st hst x hx hgood => hgrow q st (Bool.eq_false_iff.mpr hst) x
      (by rwa [flag.latch_of_false step q (Bool.eq_false_iff.mpr hst)] at hx)
      (Bool.eq_false_iff.mpr hgood)) hn (Bool.eq_false_iff.mp hs)

end Latch

end StateLens

end Cslib
