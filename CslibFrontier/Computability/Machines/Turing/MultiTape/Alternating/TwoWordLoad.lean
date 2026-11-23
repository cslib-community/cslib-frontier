/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunctionLayout

/-!
# Loading terminal parameters from a completed choice tape

The last move leaves its tape head on the blank after the completed input. The loader rewinds
that tape and computes two protected words. The time bound retains the original computation's
input-dependent clock, including the native copies of its outputs.

## Main results

* `Turing.MultiTapeATM.TwoWordLoad.runs_rewind`: rewind one stored word while preserving all
  ambient tape contents, heads, input position, and output.
* `Turing.MultiTapeATM.TwoWordLoad.exists_load_from`: prepare two native words from one stored
  source and transfer to a supplied alternating continuation, charging both computations.
-/

public section
namespace Turing.MultiTapeATM.TwoWordLoad
open MultiTapeTM WordFunctionLayout

/-- All work tapes start blank and the input head is on its left blank. -/
@[expose] def blank (K : ℕ) (input : List Bool) : Cfg K Bool Unit input :=
  { tapesCfg input (fun _ => []) 0 0 [] with inputPos := 0 }

/-- Rewind a selected completed word without changing any ambient tape, cursor or output. -/
noncomputable def rewind {K : ℕ} (src : Fin K) :=
  (rewindWork Bool).extendTapes (tapeEmb src)

/-- The native rewind works over arbitrary ambient storage and preserves its input head. -/
theorem runs_rewind {K : ℕ} (src : Fin K) (w : List Bool) {input : List Bool}
    (storage : Cfg K Bool Unit input) (pos : ℕ) (hp : pos ≤ w.length) :
    RunsBetween (rewind src) (WordGameLeaf.config src none w pos storage)
      (WordGameLeaf.config src none w 0 storage) (pos + 2) (K * (pos + 3)) := by
  apply RunsBetween.of_runFrom
  simp only [rewind, runFrom_tapeEmb, oneTapeCfg, WordGameLeaf.config, Cfg.withState,
    extendTapes_q₀, Function.update_self]
  rw [runFrom_rewindWork_none _ _ _ rfl hp, embed_tapeEmb]
  apply Cfg.ext <;> try rfl
  all_goals
    funext j
    by_cases hj : j = src <;> simp [hj]

private theorem rewind_run {K : ℕ} (src : Fin K) (w input : List Bool) (pos : ℕ)
    (hp : pos ≤ w.length) :
    let ws := Function.update (fun _ : Fin K => []) src w
    RunsBetween (rewind src).fromLeftBlank
      (WordGameLeaf.config src none w pos (blank K input))
      { tapesCfg input ws 0 0 [] with inputPos := 0 } (pos + 2 + 2)
      (K * (pos + 3) + 4 * K) := by
  have hr := runs_rewind src w (tapesCfg input (fun _ => []) 0 0 []) pos hp
  have hs := hr.fromLeftBlank rfl rfl
  convert hs using 1 <;> apply Cfg.ext <;> try rfl
  all_goals
    funext j
    by_cases hj : j = src <;> simp [WordGameLeaf.config, tapesCfg, hj]

/-- Run two clocked functions on the completed input and transfer to a continuation seeing only
its two requested words. The choice tape may hold a long framed prefix. Its rewind is charged. -/
theorem exists_load_from {K : ℕ} {S α β γ : Type} {encIn : α ↪ List Bool}
    {encX : β ↪ List Bool} {encY : γ ↪ List Bool} {f : α → β} {g : α → γ} {T : α → ℕ}
    (hf : ComputableInO f encIn encX T T) (hg : ComputableInO g encIn encY T T)
    (i j : Fin K) (hne : i ≠ j) (leaf : MultiTapeATM K Bool S) [Finite S] :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (c : ℕ),
      ∀ (input : List Bool) (a : α) (pos : ℕ), pos ≤ (encIn a).length → ∀ (t : ℕ),
        let cfg := (TwoWordInput.ready i j input (encX (f a)) (encY (g a))).withState
          (some leaf.toPTM.initial)
        let start := WordGameLeaf.config src (some atm.toPTM.initial) (encIn a) pos
          (blank U input)
        let time := pos + c * (T a + 1) + 8 + t
        leaf.HaltsWithin t cfg → atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ leaf.AcceptsWithin t cfg) := by
  obtain ⟨k₁, Q₁, hQ₁, tm₁, c₁, h₁⟩ := WordFunctionLayout.exists_of_inO hf
  obtain ⟨k₂, Q₂, hQ₂, tm₂, c₂, h₂⟩ := WordFunctionLayout.exists_of_inO hg
  let s := max k₁ k₂
  let src : Fin (s + K + 2) := Fin.natAdd (s + K) 0
  let emb : Fin K ↪ Fin (s + K + 2) := (Fin.natAddEmb s).trans (Fin.castAddEmb 2)
  let prep₁ := (tm₁.extendTapes (outputTapes (Nat.le_max_left k₁ k₂) i)).fromLeftBlank
  let prep₂ := (tm₂.extendTapes (outputTapes (Nat.le_max_right k₁ k₂) j)).fromLeftBlank
  let prep := ((rewind src).fromLeftBlank.seq prep₁).seq prep₂
  let cont := leaf.extendTapes emb
  let atm := prependTM prep cont
  refine ⟨_, src, _, inferInstance, atm, c₁ + c₂, ?_⟩
  intro input a pos hpos t
  dsimp only
  intro hh
  let ws₀ : Fin (s + K + 2) → List Bool := Function.update (fun _ => []) src (encIn a)
  let ws₁ := Function.update ws₀ (emb i) (encX (f a))
  let ws₂ := Function.update ws₁ (emb j) (encY (g a))
  let finish : Cfg (s + K + 2) Bool Unit input := { tapesCfg input ws₂ 0 0 [] with inputPos := 0 }
  have hr := rewind_run src (encIn a) input pos hpos
  have hl₁ := h₁ s K (Nat.le_max_left ..) i input a ws₀ []
    (by intro l; simp [ws₀, src, Fin.castAdd_ne_natAdd])
    (by simp [ws₀, src, Fin.castAdd_ne_natAdd]) (by simp [ws₀, src]) (by simp [ws₀, src])
  have hsrc (l : Fin 2) : Fin.natAdd (s + K) l ≠ emb i :=
    (Fin.castAdd_ne_natAdd _ _).symm
  have hl₂ := h₂ s K (Nat.le_max_right ..) j input a ws₁ []
    (by intro l; simp [ws₁, emb, ws₀, src, Fin.castAdd_ne_natAdd])
    (by simp [ws₁, emb, ws₀, src, hne.symm, Fin.castAdd_ne_natAdd])
    (by simp [ws₁, hsrc, ws₀, src])
    (by simp [ws₁, hsrc, ws₀, src])
  have hv : viewCfg emb (finish.withState (some leaf.toPTM.initial)) =
      (TwoWordInput.ready i j input (encX (f a)) (encY (g a))).withState
        (some leaf.toPTM.initial) := by
    apply Cfg.ext <;> try rfl
    funext l z
    by_cases hi : l = i <;> by_cases hj : l = j <;>
      simp_all [finish, ws₂, ws₁, ws₀, emb, src, viewCfg, Cfg.withState, tapesCfg,
        TwoWordInput.ready, TwoWordInput.words, wordsCfg, Fin.castAdd_ne_natAdd]
  have hhalt := (leaf.haltsWithin_extendTapes_iff emb t _).2 (hv ▸ hh)
  have hm := prependTM_spec prep cont _ finish _ t ((hr.seq hl₁).seq hl₂).1 hhalt
  have hc : pos + 2 + 2 + (c₁ * (T a + 1) + 2) + (c₂ * (T a + 1) + 2) + t =
      pos + (c₁ + c₂) * (T a + 1) + 8 + t := by rw [Nat.add_mul]; omega
  rw [hc] at hm
  refine ⟨hm.1, hm.2.trans ?_⟩
  change (leaf.extendTapes emb).AcceptsWithin t (finish.withState (some leaf.toPTM.initial)) ↔ _
  rw [leaf.acceptsWithin_extendTapes_iff emb, hv]

/-- Starting at the right blank of a completed word charges the entire head rewind. -/
theorem exists_load {K : ℕ} {S α β γ : Type} {encIn : α ↪ List Bool}
    {encX : β ↪ List Bool} {encY : γ ↪ List Bool} {f : α → β} {g : α → γ} {T : α → ℕ}
    (hf : ComputableInO f encIn encX T T) (hg : ComputableInO g encIn encY T T)
    (i j : Fin K) (hne : i ≠ j) (leaf : MultiTapeATM K Bool S) [Finite S] :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (c : ℕ),
      ∀ (input : List Bool) (a : α) (t : ℕ),
        let cfg := (TwoWordInput.ready i j input (encX (f a)) (encY (g a))).withState
          (some leaf.toPTM.initial)
        let start := WordGameLeaf.config src (some atm.toPTM.initial) (encIn a) (encIn a).length
          (blank U input)
        let time := (encIn a).length + c * (T a + 1) + 8 + t
        leaf.HaltsWithin t cfg → atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ leaf.AcceptsWithin t cfg) := by
  obtain ⟨U, src, Q, hQ, atm, c, h⟩ := exists_load_from hf hg i j hne leaf
  exact ⟨U, src, Q, hQ, atm, c, fun input a => h input a _ le_rfl⟩

end Turing.MultiTapeATM.TwoWordLoad
