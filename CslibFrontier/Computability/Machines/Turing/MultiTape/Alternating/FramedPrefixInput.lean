/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.SkipFrame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Starting an alternating machine at the suffix of a stored framed input

A deterministic machine computes the encoded pair of the public data and its suffix word.
Output redirection places the pair on one chosen work tape. After restoring the external input
head to its left blank, a two-state machine skips the frame. The continuation then owns exactly
its chosen work tape, initially positioned at the suffix. The stored-input version preserves
an arbitrary host input and charges its source rewind separately.
-/

public section

namespace Turing.MultiTapeATM.FramedPrefixInput

open MultiTapeTM

private def outputTapes (r : ℕ) {K : ℕ} (i : Fin K) : Fin (r + 1) ↪ Fin (r + K) :=
  Fin.Embedding.snoc (Fin.castAddEmb K) (a := Fin.natAdd r i) (by
    rintro ⟨l, h⟩
    exact Fin.castAdd_ne_natAdd _ _ h)

/-- Place the framed input and computed suffix on the designated tape and move to the first
suffix bit. The external input head is on the left blank, with every other work tape blank. -/
@[expose] def ready {K : ℕ} (i : Fin K) (input suffix : List Bool) : Cfg K Bool Unit input :=
  WordGameLeaf.config i none (frame input ++ suffix) (frame input).length
    { wordsCfg input none (fun _ => []) [] with inputPos := 0 }

/-- A clocked computation from the framed configuration lifts to the ordinary initial
configuration. The cost of producing, storing and seeking past the frame is additive. -/
theorem exists_prepend {α : Type} {enc : α ↪ List Bool} {suffix : α → List Bool} {T : α → ℕ}
    (hf : ComputableInO (fun a => (a, suffix a)) enc (encPair enc encBits) T T)
    {K : ℕ} {L : Type} [Finite L] (i : Fin K) (leaf : MultiTapeATM K Bool L) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C : ℕ),
      ∀ (a : α) (t : ℕ),
        let input := enc a
        let cfg := (ready i input (suffix a)).withState (some leaf.toPTM.initial)
        leaf.HaltsWithin t cfg →
          let time := C * (T a + 1) + t
          atm.HaltsWithin time (atm.toPTM.toNTM.initCfg input) ∧
            (atm.AcceptsWithin time (atm.toPTM.toNTM.initCfg input) ↔
              leaf.AcceptsWithin t cfg) := by
  obtain ⟨c, ⟨r, P, hP, M, hM⟩, hlen⟩ := Internal.NormalForm.inO hf
  let E := outputTapes r i
  let d := Fin.natAdd r i
  let load := M.outputToWord.extendTapes E
  let skip := SkipFrame.machine d
  let prep := (load.seq (inputStep (-1))).seq skip
  let cont := leaf.extendTapes (Fin.natAddEmb r)
  let atm := prependTM prep cont
  refine ⟨_, _, inferInstance, atm, 3 * c + 3, ?_⟩
  intro a t
  let input := enc a
  let header := frame input
  let data := header ++ suffix a
  let blank := fun _ : Fin (r + K) => ([] : List Bool)
  let ws := Function.update blank d data
  let start : Cfg (r + K) Bool Unit input := wordsCfg input none blank []
  let loaded : Cfg (r + K) Bool Unit input := wordsCfg input none ws []
  let left : Cfg (r + K) Bool Unit input := { loaded with inputPos := 0 }
  let finish : Cfg (r + K) Bool Unit input := { left with
    workTapePos := Function.update left.workTapePos d (header.length : ℤ) }
  let budget := c * (T a + 1)
  let τ := (budget + data.length + 2 + 1) + header.length
  dsimp only
  intro hhalt
  obtain ⟨ws', emitted, hr, ⟨hws, hem⟩, _⟩ := transformsTapes_iff_runFrom.mp
    ((hM a).outputToWord_extendTapes E) input blank [] ⟨rfl, fun _ => rfl⟩
  have he : E (Fin.last r) = d := by simp [E, outputTapes, d]
  rw [he] at hws
  subst ws' emitted
  have hl : load.runFrom (start.withState (some load.q₀))
      (budget + data.length + 2) = loaded.withState none := hr
  have hleft : (inputStep (k := r + K) (-1)).runFrom (loaded.withState (some ())) 1 =
      left.withState none := by
    apply Cfg.ext <;> simp [left, loaded, wordsCfg, runFrom, step_of_state, inputStep,
      Cfg.withState, Action.apply, moveInputPos]
  have hskip : skip.runFrom (left.withState (some skip.q₀)) header.length = finish.withState none :=
    SkipFrame.runFrom d input (suffix a) left
      (by simp [left, loaded, ws, wordsCfg, data, header]) rfl
  have hrun : prep.runFrom (start.withState (some prep.q₀)) τ = finish.withState none :=
    runFrom_seq (runFrom_seq hl rfl hleft rfl) rfl hskip rfl
  have hv : viewCfg (Fin.natAddEmb r) (finish.withState (some cont.toPTM.initial)) =
      (ready i input (suffix a)).withState (some leaf.toPTM.initial) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l z
      by_cases hi : l = i
      · subst l
        simp [finish, left, loaded, ws, d, ready, WordGameLeaf.config, wordsCfg, viewCfg,
          Cfg.withState, data, header]
      · simp [finish, left, loaded, ws, d, ready, WordGameLeaf.config, wordsCfg, viewCfg,
          Cfg.withState, hi, blank]
    · funext l
      by_cases hi : l = i <;>
        simp [finish, left, loaded, d, ready, WordGameLeaf.config, wordsCfg, viewCfg,
          Cfg.withState, hi, header]
  have hc : cont.HaltsWithin t (finish.withState (some cont.toPTM.initial)) := by
    rw [MultiTapeATM.haltsWithin_extendTapes_iff, hv]
    exact hhalt
  have h := prependTM_spec prep cont start finish τ t hrun hc
  have hinit : atm.toPTM.toNTM.initCfg input = start.withState (some atm.toPTM.initial) :=
    Cfg.init_eq_wordsCfg _ _
  rw [hinit]
  have hdlen : data.length ≤ budget := hlen a
  have hhead : header.length ≤ data.length := by simp [data]
  have hb : τ + t ≤ (3 * c + 3) * (T a + 1) + t := by
    dsimp only [τ, budget] at *
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  have hv' : viewCfg (Fin.natAddEmb r) (finish.withState (some cont.toPTM.toNTM.q₀)) =
      (ready i input (suffix a)).withState (some leaf.toPTM.initial) := hv
  refine ⟨h.1.mono hb, ⟨fun hacc => ?_, fun hacc => ?_⟩⟩
  · have ha := h.2.mp (hacc.of_halted_stepCoins h.1)
    rwa [MultiTapeATM.acceptsWithin_extendTapes_iff, hv'] at ha
  · apply (h.2.mpr ?_).mono hb
    rwa [MultiTapeATM.acceptsWithin_extendTapes_iff, hv']

/-- Compute a framed context and suffix from one stored word, then start a continuation at
its first suffix cell. The native preparation clock is retained, and the original cursor's
rewind and the new frame's scan are charged explicitly. The host input is preserved. -/
theorem exists_prepend_work {α : Type} {enc : α ↪ List Bool} {suffix : α → List Bool}
    {T : α → ℕ}
    (hd : ComputableInO (fun a => (a, suffix a)) enc (encPair enc encBits) T T)
    {K : ℕ} {L : Type} [Finite L] (tape : Fin K) (leaf : MultiTapeATM K Bool L) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (c : ℕ),
      ∀ (host : List Bool) (p : α) (pos : ℕ), pos ≤ (enc p).length → ∀ (t : ℕ),
        let pre := frame (enc p)
        let target := WordGameLeaf.config tape (some leaf.toPTM.initial)
          (pre ++ suffix p) pre.length (TwoWordLoad.blank K host)
        let start := SharedWordFork.start src atm host (enc p) pos
        leaf.HaltsWithin t target →
          let time := pos + c * (T p + 1) + 8 + (pre.length + t)
          atm.HaltsWithin time start ∧
            (atm.AcceptsWithin time start ↔ leaf.AcceptsWithin t target) := by
  let emb : Fin K ↪ Fin (K + 1) := Fin.castSuccEmb
  let i := emb tape
  let j := Fin.last K
  have hij : i ≠ j := Fin.castSucc_ne_last _
  let skip := SkipFrame.machine i
  let child := leaf.extendTapes emb
  let stage := prependTM skip child
  have hnil := (ComputableInDegree.const (encIn := (encPair enc encBits))
    (encMid := encBits) ([] : List Bool)).inO_one.comp_linear hd
  obtain ⟨U, src, Q, hQ, atm, c, h⟩ := TwoWordLoad.exists_load_from hd hnil i j hij stage
  refine ⟨U, src, Q, hQ, atm, c, ?_⟩
  intro host p pos hpos t
  dsimp only
  intro hh
  let pre := frame (enc p)
  let word := pre ++ suffix p
  let start := TwoWordInput.ready i j host word []
  let finish : Cfg (K + 1) Bool Unit host := {start with
    workTapePos := Function.update start.workTapePos i (pre.length : ℤ)}
  have hs : skip.runFrom (start.withState (some skip.q₀)) pre.length = finish.withState none :=
    SkipFrame.runFrom i (enc p) (suffix p) start
      (by simp [start, TwoWordInput.ready, TwoWordInput.words, wordsCfg, word, pre]) rfl
  have hv : viewCfg emb (finish.withState (some child.toPTM.initial)) =
      WordGameLeaf.config tape (some leaf.toPTM.initial) word pre.length
        (TwoWordLoad.blank K host) := by
    apply Cfg.ext <;> try rfl
    · funext l z
      by_cases hl : l = tape
      · subst l
        simp [finish, start, TwoWordInput.ready, TwoWordInput.words, wordsCfg, viewCfg,
          Cfg.withState, WordGameLeaf.config, i]
      · simp [finish, start, TwoWordInput.ready, TwoWordInput.words, wordsCfg, viewCfg,
          Cfg.withState, WordGameLeaf.config, i, hl, TwoWordLoad.blank,
          tapesCfg]
    · funext l
      by_cases hl : l = tape <;>
        simp [finish, start, TwoWordInput.ready, wordsCfg, viewCfg, Cfg.withState,
          WordGameLeaf.config, i, hl, TwoWordLoad.blank, tapesCfg]
  have ht : child.HaltsWithin t (finish.withState (some child.toPTM.initial)) :=
    (leaf.haltsWithin_extendTapes_iff emb t _).2 (hv ▸ hh)
  obtain ⟨hs', ha⟩ := prependTM_spec skip child start finish pre.length t hs ht
  obtain ⟨hh', hacc⟩ := h host p pos hpos _ hs'
  have hac : child.AcceptsWithin t (finish.withState (some child.toPTM.initial)) ↔
      leaf.AcceptsWithin t (WordGameLeaf.config tape (some leaf.toPTM.initial)
        word pre.length (TwoWordLoad.blank K host)) := by
    exact (leaf.acceptsWithin_extendTapes_iff emb t _).trans (by rw [hv])
  have hiff := hacc.trans (ha.trans hac)
  exact ⟨hh', hiff⟩

end Turing.MultiTapeATM.FramedPrefixInput
