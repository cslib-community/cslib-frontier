/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind

/-!
# Revealing a hidden sample along an experiment

A real experiment runs on states `a`. An ideal experiment first draws a hidden sample `k` and then
runs on smaller states that depend on it. The two are linked by a law `exp a` of the hidden sample
given the real state and by a representation `rep a`: the real state together with the explained
sample, `(exp a).map (·, rep a)`, has the law of the ideal pair. Lazy and eager sampling of a
random function are an example, where `exp` completes the table that a lazy state has not yet
sampled.

Such a link is preserved by a step that keeps it on reachable real states. The lemmas carry an
invariant of those states, so the local link need only hold where the invariant does. A trivial
hidden sample turns the link into a plain state representation, `(d.map rep)`.

## Main definitions

* `Cslib.Probability.PMF.HiddenCoupling`: link `(exp a).map (·, rep a)` between a concrete
  distribution and an ideal hidden-sample experiment, bundled with a support invariant.
* `Cslib.Probability.PMF.RepInv`: deterministic state representation `d₁.map rep = d₂`, bundled
  with a support invariant.

## Main results

* `Cslib.Probability.PMF.HiddenCoupling.pure`, `.congr`, `.bind`, `.bind_pure`, `.map`, `.iterate`:
  dot-notation combinators inferring intermediate distributions and continuations.
* `Cslib.Probability.PMF.RepInv.pure`, `.of_eq`, `.map_eq`, `.bind`, `.map`, `.iterate`:
  dot-notation combinators for deterministic state representations with invariants.
* `Cslib.Probability.PMF.iterate_bind_invariant`: invariant preservation across `m` monadic steps.
-/

public section

namespace Cslib.Probability.PMF

universe u v w x y

variable {α₁ : Type u} {β₁ : Type v} {α : Type w} {β : Type x} {γ : Type y}

/-- Couple a concrete distribution `d₁` with an ideal two-stage distribution drawing `k ← exp₀` and
running `d₂ k`, linked by the conditional law `exp a` of the hidden sample and representation
`rep a`, carrying `inv` on `d₁.support`. -/
structure HiddenCoupling (d₁ : PMF α) (exp₀ : PMF γ) (exp : α → PMF γ)
    (rep : α → β) (d₂ : γ → PMF β) (inv : α → Prop) : Prop where
  /-- Joint law of the concrete outcome with its explained sample matches the ideal pair. -/
  bind_eq : (d₁.bind fun a => (exp a).map (·, rep a)) =
    (exp₀.bind fun k => (d₂ k).map (k, ·))
  /-- Every reachable concrete outcome satisfies `inv`. -/
  support_inv : ∀ a ∈ d₁.support, inv a

/-- Pointwise hidden-sample coupling on `PMF.pure`. -/
theorem HiddenCoupling.pure {a : α} {exp₀ : PMF γ} {exp : α → PMF γ} {rep : α → β} {b : γ → β}
    {inv : α → Prop} (hexp : exp a = exp₀) (hrep : ∀ k ∈ exp₀.support, rep a = b k)
    (hinv : inv a) : HiddenCoupling (PMF.pure a) exp₀ exp rep (fun k => PMF.pure (b k)) inv := by
  refine ⟨?_, fun _ h => (PMF.mem_support_pure_iff _ _).mp h ▸ hinv⟩
  simp only [PMF.pure_bind, hexp, PMF.map]
  exact bind_congr_on_support _ _ _ fun k hk => by simp only [Function.comp_def, hrep k hk]

/-- Transport `HiddenCoupling` along distribution equalities on support and invariant weakening. -/
theorem HiddenCoupling.congr {d₁ d₁' : PMF α} {exp₀ : PMF γ} {exp : α → PMF γ} {rep : α → β}
    {d₂ d₂' : γ → PMF β} {inv₁ inv₂ : α → Prop} (h : HiddenCoupling d₁ exp₀ exp rep d₂ inv₁)
    (hd₁ : d₁ = d₁') (hd₂ : ∀ k ∈ exp₀.support, d₂ k = d₂' k)
    (hinv : ∀ a ∈ d₁.support, inv₁ a → inv₂ a) : HiddenCoupling d₁' exp₀ exp rep d₂' inv₂ := by
  subst hd₁
  exact ⟨h.bind_eq.trans (bind_congr_on_support _ _ _ fun k hk => by rw [hd₂ k hk]),
    fun a ha => hinv a ha (h.support_inv a ha)⟩

/-- Sequence two `HiddenCoupling` stages with distributions and continuations inferred. -/
theorem HiddenCoupling.bind {d₁ : PMF α₁} {exp₀ : PMF γ} {exp₁ : α₁ → PMF γ} {rep₁ : α₁ → β₁}
    {d₂ : γ → PMF β₁} {inv₁ : α₁ → Prop} {f₁ : α₁ → PMF α} {exp : α → PMF γ} {rep : α → β}
    {f₂ : γ → β₁ → PMF β} {inv : α → Prop} (hd : HiddenCoupling d₁ exp₀ exp₁ rep₁ d₂ inv₁)
    (hf : ∀ a ∈ d₁.support, inv₁ a →
      HiddenCoupling (f₁ a) (exp₁ a) exp rep (fun k => f₂ k (rep₁ a)) inv) :
    HiddenCoupling (d₁.bind f₁) exp₀ exp rep (fun k => (d₂ k).bind (f₂ k)) inv := by
  refine ⟨?_, fun b hb => ?_⟩
  · rw [PMF.bind_bind,
      bind_congr_on_support _ _ _ fun a ha => (hf a ha (hd.support_inv a ha)).bind_eq]
    have h2 := congrArg (fun d => d.bind fun (k, b₁) => (f₂ k b₁).map (k, ·)) hd.bind_eq
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h2 ⊢
    exact h2.trans (bind_congr_on_support _ _ _ fun _ _ => by simp only [PMF.map_bind])
  · obtain ⟨a, ha, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
    exact (hf a ha (hd.support_inv a ha)).support_inv b hmem

/-- Sequence a `HiddenCoupling` whose ideal first stage is `PMF.pure (b k)` with a continuation
`fun k => f₂ k (b k)`. -/
theorem HiddenCoupling.bind_pure {d₁ : PMF α₁} {exp₀ : PMF γ} {exp₁ : α₁ → PMF γ}
    {rep₁ : α₁ → β₁} {b : γ → β₁} {inv₁ : α₁ → Prop} {f₁ : α₁ → PMF α} {exp : α → PMF γ}
    {rep : α → β} {f₂ : γ → β₁ → PMF β} {inv : α → Prop}
    (hd : HiddenCoupling d₁ exp₀ exp₁ rep₁ (fun k => PMF.pure (b k)) inv₁)
    (hf : ∀ a ∈ d₁.support, inv₁ a →
      HiddenCoupling (f₁ a) (exp₁ a) exp rep (fun k => f₂ k (rep₁ a)) inv) :
    HiddenCoupling (d₁.bind f₁) exp₀ exp rep (fun k => f₂ k (b k)) inv :=
  (hd.bind hf).congr rfl (fun _ _ => PMF.pure_bind _ _) fun _ _ h => h

/-- Postprocess both sides of a `HiddenCoupling` on `d₁.support` and `(exp₁ a).support`. -/
theorem HiddenCoupling.map {d₁ : PMF α₁} {exp₀ : PMF γ} {exp₁ : α₁ → PMF γ} {rep₁ : α₁ → β₁}
    {d₂ : γ → PMF β₁} {inv₁ : α₁ → Prop} {g₁ : α₁ → α} {exp : α → PMF γ} {rep : α → β}
    {g₂ : γ → β₁ → β} {inv : α → Prop} (hd : HiddenCoupling d₁ exp₀ exp₁ rep₁ d₂ inv₁)
    (hg : ∀ a ∈ d₁.support, inv₁ a →
      exp (g₁ a) = exp₁ a ∧ (∀ k ∈ (exp₁ a).support, rep (g₁ a) = g₂ k (rep₁ a)) ∧ inv (g₁ a)) :
    HiddenCoupling (d₁.map g₁) exp₀ exp rep (fun k => (d₂ k).map (g₂ k)) inv :=
  hd.bind fun a ha hia => let ⟨hexp, hrep, hinv⟩ := hg a ha hia; .pure hexp hrep hinv

/-- Lift a step-wise `HiddenCoupling` across `m` monadic iterations. -/
theorem HiddenCoupling.iterate {step₁ : α → PMF α} {step₂ : γ → β → PMF β} {exp₀ : PMF γ}
    {exp : α → PMF γ} {rep : α → β} (inv : ℕ → α → Prop) {m : ℕ} {init : α} {init₂ : γ → β}
    (hexp₀ : exp init = exp₀) (hrep₀ : ∀ k ∈ exp₀.support, rep init = init₂ k) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a →
      HiddenCoupling (step₁ a) (exp a) exp rep (fun k => step₂ k (rep a)) (inv (i + 1))) :
    HiddenCoupling (Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)) exp₀ exp rep
      (fun k => Nat.iterate (fun d => d.bind (step₂ k)) m (PMF.pure (init₂ k))) (inv m) := by
  induction m with
  | zero => exact .pure hexp₀ hrep₀ hinit
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact (ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)).bind
      fun a _ ha => hstep m (Nat.lt_succ_self m) a ha

/-- Couple a concrete distribution `d₁` with an abstract distribution `d₂` via `d₁.map rep = d₂`,
carrying `inv` on `d₁.support`. -/
structure RepInv (d₁ : PMF α) (d₂ : PMF β) (rep : α → β) (inv : α → Prop) : Prop where
  /-- Pushforward of `d₁` along `rep` equals `d₂`. -/
  map_eq : d₁.map rep = d₂
  /-- Every reachable concrete outcome satisfies `inv`. -/
  support_inv : ∀ a ∈ d₁.support, inv a

/-- Pointwise representation and invariant on `PMF.pure`. -/
theorem RepInv.pure {a : α} {b : β} {rep : α → β} {inv : α → Prop}
    (hrep : rep a = b) (hinv : inv a) : RepInv (PMF.pure a) (PMF.pure b) rep inv :=
  ⟨by rw [PMF.pure_map, hrep], fun _ h => (PMF.mem_support_pure_iff _ _).mp h ▸ hinv⟩

/-- Package an unconditional equality `d₁.map rep = d₂` with the trivial invariant. -/
theorem RepInv.of_eq {d₁ : PMF α} {d₂ : PMF β} {rep : α → β} (h : d₁.map rep = d₂) :
    RepInv d₁ d₂ rep (fun _ => True) :=
  ⟨h, fun _ _ => trivial⟩

/-- Sequence two `RepInv` stages with distributions and continuations inferred. -/
theorem RepInv.bind {d₁ : PMF α₁} {d₂ : PMF β₁} {rep₁ : α₁ → β₁} {inv₁ : α₁ → Prop}
    {f₁ : α₁ → PMF α} {f₂ : β₁ → PMF β} {rep : α → β} {inv : α → Prop}
    (hd : RepInv d₁ d₂ rep₁ inv₁)
    (hf : ∀ a ∈ d₁.support, inv₁ a → RepInv (f₁ a) (f₂ (rep₁ a)) rep inv) :
    RepInv (d₁.bind f₁) (d₂.bind f₂) rep inv := by
  refine ⟨?_, fun b hb => ?_⟩
  · rw [PMF.map_bind, ← hd.map_eq, PMF.bind_map]
    exact bind_congr_on_support _ _ _ fun a ha => (hf a ha (hd.support_inv a ha)).map_eq
  · obtain ⟨a, ha, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
    exact (hf a ha (hd.support_inv a ha)).support_inv b hmem

/-- Postprocess both sides of a `RepInv` coupling on `d₁.support`. -/
theorem RepInv.map {d₁ : PMF α₁} {d₂ : PMF β₁} {rep₁ : α₁ → β₁} {inv₁ : α₁ → Prop}
    {g₁ : α₁ → α} {g₂ : β₁ → β} {rep : α → β} {inv : α → Prop} (hd : RepInv d₁ d₂ rep₁ inv₁)
    (hg : ∀ a ∈ d₁.support, inv₁ a → rep (g₁ a) = g₂ (rep₁ a) ∧ inv (g₁ a)) :
    RepInv (d₁.map g₁) (d₂.map g₂) rep inv :=
  hd.bind fun a ha hia => .pure (hg a ha hia).1 (hg a ha hia).2

/-- Lift a step-wise `RepInv` coupling across `m` monadic iterations. -/
theorem RepInv.iterate {step₁ : α → PMF α} {step₂ : β → PMF β} {rep : α → β}
    (inv : ℕ → α → Prop) {m : ℕ} {init : α} {init₂ : β} (hrep₀ : rep init = init₂)
    (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a → RepInv (step₁ a) (step₂ (rep a)) rep (inv (i + 1))) :
    RepInv (Nat.iterate (fun d => d.bind step₁) m (PMF.pure init))
      (Nat.iterate (fun d => d.bind step₂) m (PMF.pure init₂)) rep (inv m) := by
  induction m with
  | zero => exact .pure hrep₀ hinit
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact (ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)).bind
      fun a _ ha => hstep m (Nat.lt_succ_self m) a ha

/-- Every reachable state of a chain of `m` steps satisfies an invariant indexed by the round,
when every possible step from a state satisfying the invariant of its round preserves it. -/
theorem iterate_bind_invariant
    (step : α → PMF α) (inv : ℕ → α → Prop) (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a → ∀ a' ∈ (step a).support, inv (i + 1) a') :
    ∀ a ∈ (Nat.iterate (fun d => d.bind step) m (PMF.pure init)).support, inv m a :=
  (RepInv.iterate (step₂ := fun _ => PMF.pure ()) (rep := fun _ => ()) inv rfl hinit
    fun i hi a ha => ⟨PMF.map_const _ _, hstep i hi a ha⟩).support_inv

end Cslib.Probability.PMF
