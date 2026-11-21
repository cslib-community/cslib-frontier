/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PreparePair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Starting a two-word alternating computation from an ordinary input tape

The input is a framed pair. A finite deterministic prefix places its components on two
distinct selected work tapes, clears its scratch space and moves the input head to the
left blank. It then passes control to the original alternating machine. The preparation
is linear in the encoded input length and the continuation time is added once.
-/

public section

namespace Turing.MultiTapeATM.TwoWordInput

open MultiTapeTM

/-- Two words on selected work tapes, with all other tapes blank. -/
@[expose] def words {K : ℕ} (i j : Fin K) (x y : List Bool) (l : Fin K) : List Bool :=
  if l = i then x else if l = j then y else []

/-- Stored words begin at their tape origins and the physical input head is on its left blank. -/
@[expose] def ready {K : ℕ} (i j : Fin K) (input x y : List Bool) : Cfg K Bool Unit input :=
  { wordsCfg input none (words i j x y) [] with inputPos := 0 }

private def first (r : ℕ) {K : ℕ} (i : Fin K) : Fin (r + 1) ↪ Fin (r + K) :=
  Fin.Embedding.snoc (Fin.castAddEmb K) (a := Fin.natAdd r i) (by
    rintro ⟨l, h⟩
    exact Fin.castAdd_ne_natAdd _ _ h)

private def tapes (r : ℕ) {K : ℕ} (i j : Fin K) (hij : i ≠ j) : Fin (r + 2) ↪ Fin (r + K) :=
  Fin.Embedding.snoc (first r i) (a := Fin.natAdd r j) (by
    rintro ⟨l, h⟩
    cases l using Fin.lastCases with
    | last => simp [first, hij] at h
    | cast l => simp [first, Fin.castAdd_ne_natAdd] at h)

private theorem selected {r K : ℕ} {i j : Fin K} (hij : i ≠ j) {x y : List Bool}
    {ws : Fin (r + K) → List Bool}
    (h : (fun l => ws (tapes r i j hij l)) = Fin.append (fun _ : Fin r => []) ![x, y])
    (hblank : ∀ l ∉ Set.range (tapes r i j hij), ws l = []) (l : Fin K) :
    ws (Fin.natAdd r l) = words i j x y l := by
  by_cases hi : l = i
  · subst l
    have hn : tapes r i j hij (Fin.natAdd r 0) = Fin.natAdd r i := by
      change tapes r i j hij (Fin.last r).castSucc = _
      simp [tapes, first]
    simpa [hn, words] using congrFun h (Fin.natAdd r 0)
  by_cases hj : l = j
  · subst l
    have hn : tapes r i j hij (Fin.natAdd r 1) = Fin.natAdd r j := by
      change tapes r i j hij (Fin.last (r + 1)) = _
      simp [tapes]
    simpa [hn, words, hi] using congrFun h (Fin.natAdd r 1)
  rw [words, ite_eq_right hi, ite_eq_right hj]
  apply hblank
  rintro ⟨m, hm⟩
  cases m using Fin.lastCases with
  | last => simp [tapes, Ne.symm hj] at hm
  | cast m =>
    cases m using Fin.lastCases with
    | last => simp [tapes, first, Ne.symm hi] at hm
    | cast m => simp [tapes, first, Fin.castAdd_ne_natAdd] at hm

/-- Pay for the external input layout and run the same alternating computation from a
standard blank-work-tape start. Both projections and both rewinds are included. -/
theorem exists_prepend {K : ℕ} {S α β : Type} (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool)
    (i j : Fin K) (hij : i ≠ j) (leaf : MultiTapeATM K Bool S) [Finite S] :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (c : ℕ),
      ∀ (p : α × β) (t : ℕ),
        let input := encPair enc₁ enc₂ p
        let cfg := (ready i j input (enc₁ p.1) (enc₂ p.2)).withState (some leaf.toPTM.initial)
        leaf.HaltsWithin t cfg →
          let time := c * (input.length + 1) + 1 + t
          atm.HaltsWithin time (atm.toPTM.toNTM.initCfg input) ∧
            (atm.AcceptsWithin time (atm.toPTM.toNTM.initCfg input) ↔
              leaf.AcceptsWithin t cfg) := by
  obtain ⟨r, P, hP, prep, c, hp⟩ := PairEncoding.exists_prepare enc₁ enc₂ (encPair enc₁ enc₂)
  let E := tapes r i j hij
  let load := prep.extendTapes E
  let cont := leaf.extendTapes (Fin.natAddEmb r)
  let atm := prependTM (load.seq (inputStep (-1))) cont
  refine ⟨_, _, inferInstance, atm, c, ?_⟩
  intro p t
  let input := encPair enc₁ enc₂ p
  let t₀ := c * (input.length + 1)
  let blank := fun _ : Fin (r + K) => ([] : List Bool)
  dsimp only
  intro hhalt
  obtain ⟨ws, emitted, hr, ⟨⟨hws, hem⟩, hrest⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp ((hp p).extendTapes E) input blank [] ⟨rfl, rfl⟩
  subst emitted
  let start : Cfg (r + K) Bool Unit input := wordsCfg input none blank []
  let finish : Cfg (r + K) Bool Unit input := { wordsCfg input none ws [] with inputPos := 0 }
  have h₁ : (inputStep (k := r + K) (-1)).runFrom (wordsCfg input (some ()) ws []) 1 =
      finish.withState none := by
    apply Cfg.ext <;> simp [finish, wordsCfg, runFrom, step_of_state, inputStep,
      Cfg.withState, Action.apply, moveInputPos]
  have hrun : (load.seq (inputStep (-1))).runFrom
      (start.withState (some (load.seq (inputStep (-1))).q₀)) (t₀ + 1) = finish.withState none :=
    runFrom_seq hr rfl h₁ rfl
  have hv : viewCfg (Fin.natAddEmb r) (finish.withState (some cont.toPTM.initial)) =
      (ready i j input (enc₁ p.1) (enc₂ p.2)).withState (some leaf.toPTM.initial) := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext l z
    change tapeOfList (ws (Fin.natAdd r l)) z = _
    rw [selected hij hws hrest l]
    rfl
  have hc : cont.HaltsWithin t (finish.withState (some cont.toPTM.initial)) := by
    rw [MultiTapeATM.haltsWithin_extendTapes_iff, hv]
    exact hhalt
  have ht := prependTM_spec (load.seq (inputStep (-1))) cont start finish (t₀ + 1) t hrun hc
  have hinit : atm.toPTM.toNTM.initCfg input = start.withState (some atm.toPTM.initial) :=
    Cfg.init_eq_wordsCfg _ _
  rw [hinit]
  refine ⟨ht.1, ht.2.trans ?_⟩
  rw [MultiTapeATM.acceptsWithin_extendTapes_iff]
  exact iff_of_eq (congrArg (leaf.AcceptsWithin t) hv)

end Turing.MultiTapeATM.TwoWordInput
