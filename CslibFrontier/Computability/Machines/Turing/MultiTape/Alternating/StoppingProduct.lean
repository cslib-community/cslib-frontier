/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGameLeaf
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameRoundTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunctionLayout
public import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteBounds
import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView

/-!
# Native navigation through a stopping product

The short Boolean position is updated by native routing rounds on a separate tape block. The
assignment is retained on a protected terminal tape and is never copied by a routing round.
-/

public section

namespace Turing.MultiTapeATM.StoppingProduct

open MultiTapeTM Cslib GaloisRingArith Cslib.Circuits.Frontier.FastContraction
open StoppingQuery.ProductRouting

private abbrev control (N q : ℕ) : Fin (N + (q + 4)) :=
  Fin.natAdd N (Fin.natAdd q 0)

private abbrev metadata (N q : ℕ) : Fin (N + (q + 4)) :=
  Fin.natAdd N (Fin.natAdd q 1)

private def terminalEmbedding {N : ℕ} (q : ℕ) (query : Fin N) :
    Fin N ↪ Fin (N + (q + 4)) :=
  (Fin.castAddEmb (q + 4)).trans
    (Equiv.swap (query.castAdd (q + 4)) (metadata N q)).toEmbedding

private theorem terminalEmbedding_query {N : ℕ} (q : ℕ) (query : Fin N) :
    terminalEmbedding q query query = metadata N q := by
  simp [terminalEmbedding]

private theorem terminalEmbedding_other {N : ℕ} (q : ℕ) (query i : Fin N) (hi : i ≠ query) :
    terminalEmbedding q query i = i.castAdd (q + 4) := by
  simp [terminalEmbedding, Equiv.swap_apply_of_ne_of_ne, hi, metadata,
    Fin.castAdd_ne_natAdd]

private def storage {N : ℕ} (q : ℕ) (assignment : Fin N)
    (input word data : List Bool) : Cfg (N + (q + 4)) Bool Unit input :=
  TwoWordInput.ready (assignment.castAdd (q + 4)) (metadata N q) input word data

private def config {N : ℕ} (q : ℕ) (assignment : Fin N)
    (input word data : List Bool) {S : Type} (state : Option S) (header : List Bool) :
    Cfg (N + (q + 4)) Bool S input :=
  WordGameLeaf.config (control N q) state header 0 (storage q assignment input word data)

private theorem view_round {N : ℕ} (q : ℕ) (assignment : Fin N)
    (input word data : List Bool) {S : Type} (state : Option S) (header : List Bool) :
    viewCfg (Fin.natAddEmb N) (config q assignment input word data state header) =
      (WordGameRound.config q input header data []).withState state := by
  have hleft (i : Fin (q + 4)) : Fin.natAdd N i ≠ assignment.castAdd (q + 4) :=
    (Fin.castAdd_ne_natAdd _ _).symm
  apply Cfg.ext <;> try rfl
  · funext i z
    cases i using Fin.addCases with
    | left i =>
      simp [viewCfg, config, storage, WordGameLeaf.config, control,
        WordGameRound.config, WordGameRound.queryConfig, WordGameRound.tapeWords, tapesCfg,
        TwoWordInput.ready, TwoWordInput.words, metadata, wordsCfg, Cfg.withState,
        hleft, Fin.castAdd_ne_natAdd]
    | right i =>
      fin_cases i <;>
        simp [viewCfg, config, storage, WordGameLeaf.config, control,
          WordGameRound.config, WordGameRound.queryConfig, WordGameRound.tapeWords, tapesCfg,
          TwoWordInput.ready, TwoWordInput.words, metadata, wordsCfg, Cfg.withState, hleft]
  · funext i
    simp [viewCfg, config, storage, WordGameLeaf.config, Cfg.withState,
      WordGameRound.config, WordGameRound.queryConfig, tapesCfg,
      TwoWordInput.ready, wordsCfg]

private theorem view_terminal {N : ℕ} (q : ℕ) (assignment query : Fin N)
    (hne : assignment ≠ query) (input word data : List Bool) {S : Type}
    (state : Option S) (header : List Bool) :
    viewCfg (terminalEmbedding q query) (config q assignment input word data state header) =
      (TwoWordInput.ready assignment query input word data).withState state := by
  have hleft : metadata N q ≠ assignment.castAdd (q + 4) :=
    (Fin.castAdd_ne_natAdd _ _).symm
  apply Cfg.ext <;> try rfl
  · funext i z
    by_cases hi : i = query
    · subst i
      simp [viewCfg, terminalEmbedding_query, config, storage, WordGameLeaf.config,
        control, TwoWordInput.ready, TwoWordInput.words,
        wordsCfg, Cfg.withState, hne.symm, hleft, metadata]
    · rw [show (viewCfg (terminalEmbedding q query)
        (config q assignment input word data state header)).workTapes i z =
          (config q assignment input word data state header).workTapes
            (terminalEmbedding q query i) z from rfl, terminalEmbedding_other q query i hi]
      by_cases ha : i = assignment <;>
        simp [config, storage, WordGameLeaf.config, control,
          TwoWordInput.ready,
          TwoWordInput.words, wordsCfg, Cfg.withState, hi, ha, metadata,
          Fin.castAdd_ne_natAdd]
  · funext i
    simp [viewCfg, config, storage, WordGameLeaf.config, Cfg.withState,
      TwoWordInput.ready, wordsCfg]

private theorem run_round {N q : ℕ} {S : Type} (round : MultiTapeTM (q + 4) Bool S)
    (assignment : Fin N) (input word data data' header header' : List Bool) (t : ℕ)
    (h : round.runFrom ((WordGameRound.config q input header data []).withState
      (some round.q₀)) t = (WordGameRound.config q input header' data' []).withState none) :
    (round.extendTapes (Fin.natAddEmb N)).runFrom
      (config q assignment input word data (some round.q₀) header) t =
      config q assignment input word data' none header' := by
  rw [runFrom_extendTapes, view_round, h, embed_natAdd]
  apply Cfg.ext <;> try rfl
  · funext i z
    cases i using Fin.addCases with
    | left i =>
      simp [config, storage, WordGameLeaf.config, control, Cfg.withState,
        TwoWordInput.ready, TwoWordInput.words, wordsCfg, metadata, Fin.castAdd_ne_natAdd]
    | right i =>
      have hv := congrArg (fun c => c.workTapes i z)
        (view_round q assignment input word data' (none : Option S) header')
      simpa [viewCfg] using hv.symm
  · funext i
    cases i using Fin.addCases <;>
      simp [config, storage, WordGameLeaf.config, Cfg.withState,
        WordGameRound.config, WordGameRound.queryConfig, tapesCfg,
        TwoWordInput.ready, wordsCfg]

private abbrev protectedTapes (s N q : ℕ) :
    Fin (N + (q + 4)) ↪ Fin (s + (N + (q + 4)) + 2) :=
  (Fin.natAddEmb s).trans (Fin.castAddEmb 2)

private abbrev loadSource (s N q : ℕ) : Fin (s + (N + (q + 4)) + 2) :=
  Fin.natAdd (s + (N + (q + 4))) 0

private def loadedEmbedding (s N q : ℕ) :
    Fin (N + (q + 4)) ↪ Fin (s + (N + (q + 4)) + 2) :=
  (protectedTapes s N q).trans
    (Equiv.swap (protectedTapes s N q (metadata N q)) (loadSource s N q)).toEmbedding

private theorem loadedEmbedding_metadata (s N q : ℕ) :
    loadedEmbedding s N q (metadata N q) = loadSource s N q := by
  simp [loadedEmbedding]

private theorem loadedEmbedding_other (s N q : ℕ) (i : Fin (N + (q + 4)))
    (hi : i ≠ metadata N q) :
    loadedEmbedding s N q i = protectedTapes s N q i := by
  simp [loadedEmbedding, Equiv.swap_apply_of_ne_of_ne, hi, protectedTapes, loadSource,
    Fin.castAdd_ne_natAdd]

private theorem view_loaded {N : ℕ} (s q : ℕ) (assignment : Fin N)
    (input word data header : List Bool) {S : Type} (state : Option S) :
    let emb := protectedTapes s N q
    let source := loadSource s N q
    let ws := TwoWordInput.words (emb (assignment.castAdd (q + 4))) source word data
    let finish : Cfg (s + (N + (q + 4)) + 2) Bool Unit input :=
      { tapesCfg input (Function.update ws (emb (control N q)) header) 0 0 [] with inputPos := 0 }
    viewCfg (loadedEmbedding s N q) (finish.withState state) =
      config q assignment input word data state header := by
  intro emb source ws finish
  have hsource (i : Fin (N + (q + 4))) : emb i ≠ source := Fin.castAdd_ne_natAdd _ _
  have hassign : assignment.castAdd (q + 4) ≠ metadata N q := Fin.castAdd_ne_natAdd _ _
  have hcontrol : control N q ≠ metadata N q := by simp [control, metadata]
  apply Cfg.ext <;> try rfl
  · funext i z
    by_cases hm : i = metadata N q
    · subst i
      rw [show (viewCfg (loadedEmbedding s N q) (finish.withState state)).workTapes
          (metadata N q) z = (finish.withState state).workTapes
            (loadedEmbedding s N q (metadata N q)) z from rfl, loadedEmbedding_metadata]
      simp only [finish, Cfg.withState, tapesCfg, Pi.zero_apply, sub_zero]
      change tapeOfList (Function.update ws (emb (control N q)) header source) z = _
      simp [ws, Function.update_of_ne (hsource (control N q)).symm,
        (hsource (assignment.castAdd (q + 4))).symm, config, storage,
        WordGameLeaf.config, TwoWordInput.ready, TwoWordInput.words, wordsCfg,
        hassign.symm, hcontrol.symm]
    · rw [show (viewCfg (loadedEmbedding s N q) (finish.withState state)).workTapes i z =
        (finish.withState state).workTapes (loadedEmbedding s N q i) z from rfl,
        loadedEmbedding_other s N q i hm]
      simp only [finish, Cfg.withState, tapesCfg, Pi.zero_apply, sub_zero]
      change tapeOfList (Function.update ws (emb (control N q)) header (emb i)) z = _
      by_cases hc : i = control N q <;> by_cases ha : i = assignment.castAdd (q + 4) <;>
        simp_all [ws, config, storage, WordGameLeaf.config, TwoWordInput.ready,
          TwoWordInput.words, wordsCfg, emb.injective.eq_iff]
  · funext i
    simp [finish, viewCfg, config, storage, WordGameLeaf.config, TwoWordInput.ready,
      wordsCfg, tapesCfg, Cfg.withState]

/-- All native routing rounds and the initial header computation, plus one terminal evaluation.
The polynomial is applied only to short metadata; the retained assignment is not in this clock. -/
@[expose] noncomputable def clock (C D : ℕ) (parameters : StoppingQuery.Product.Parameters)
    (terminalTime : ℕ) : ℕ :=
  let levels := Nat.clog 2 parameters.vertices
  let moves := 13 * (levels *
    (SignedValueGame.height (3 ^ modulusExp parameters.scale) parameters.precision +
      2 * SignedValueGame.rounds parameters.precision + 11) + 1) + 12
  (moves + 1) * (C * (metadataBound parameters (2 ^ levels) levels + 1) ^ D + 2) +
    terminalTime + 1

/-- Compile the balanced stopping product into one fixed finite alternating machine. The raw
entry consists of an opaque assignment word and the short encoded root position on two distinct
work tapes. Native header preparation and every Boolean routing round are included in the clock.

The supplied terminal is invoked only on a terminal gate and receives the retained assignment
and the terminal position. Its time is added once per branch. Arithmetic routing is constructed
from the concrete product compiler and requires no caller-supplied decoder or update certificate. -/
theorem exists_evaluator {N : ℕ} {S : Type} [Finite S]
    (assignment query : Fin N) (hne : assignment ≠ query) (terminal : MultiTapeATM N Bool S) :
    ∃ (U : ℕ) (assignmentSource querySource : Fin U) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM U Bool Q) (C D : ℕ), assignmentSource ≠ querySource ∧
      ∀ (input word : List Bool) (parameters : StoppingQuery.Product.Parameters)
        (entry : ℕ → ℕ → GaloisRingArith.Ring parameters.precision (modulus parameters.scale))
        (terminalTime : ℕ),
        (∀ p, Valid parameters (2 ^ Nat.clog 2 parameters.vertices)
            (Nat.clog 2 parameters.vertices) p → player p = none →
          let start := (TwoWordInput.ready assignment query input word (encPosition p)).withState
            (some terminal.toPTM.initial)
          terminal.HaltsWithin terminalTime start ∧
            (terminal.AcceptsWithin terminalTime start ↔
              StoppingQuery.value parameters.scale parameters.precision 0 parameters.vertices
                entry (address p) = p.claim)) →
        ∀ (coefficient : Fin (modulus parameters.scale).length)
          (bit : Fin parameters.precision) (claim : Bool),
          let position := root parameters coefficient.val bit.val claim
          let start := (TwoWordInput.ready assignmentSource querySource input word
            (encPosition position)).withState (some atm.toPTM.initial)
          atm.HaltsWithin (clock C D parameters terminalTime) start ∧
            (atm.AcceptsWithin (clock C D parameters terminalTime) start ↔
              ((representative parameters.scale parameters.precision
                (∏ vertex ∈ Finset.range parameters.vertices, entry 0 vertex)).coeff
                  coefficient.val).val.testBit bit.val = claim) := by
  obtain ⟨q, R, hR, round, cR, dR, hr⟩ :=
    WordGameRound.exists_round encPosition StoppingQuery.ProductRouting.step step_polyTime
  have hheader : ComputableInPolyTime (fun p => wordGameHeader (player p)) encPosition encBits :=
    (ComputableInPolyTime.of_finite (encIn := encOption encBool) (encOut := encBits)
      wordGameHeader).comp player_polyTime
  obtain ⟨s, H, hH, header, cH, dH, hh⟩ := WordFunctionLayout.exists_of_polyTime hheader
  let round' := round.extendTapes (Fin.natAddEmb N)
  let terminal' := terminal.extendTapes (terminalEmbedding q query)
  let body := WordGameLeaf.machine round' terminal' (control N q)
  let prepare := (header.extendTapes (WordFunctionLayout.outputTapes (Nat.le_refl s)
    (control N q))).fromLeftBlank
  let continuation := body.extendTapes (loadedEmbedding s N q)
  let atm := prependTM prepare continuation
  let ass := protectedTapes s N q (assignment.castAdd (q + 4))
  let src := loadSource s N q
  have hpoly : Cslib.PolynomiallyBounded
      (fun n => cR * (n + 1) ^ dR + cH * (n + 1) ^ dH) := by fun_prop
  obtain ⟨C, D, hc⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  refine ⟨_, ass, src, _, inferInstance, atm, C, D, Fin.castAdd_ne_natAdd _ _, ?_⟩
  intro input word parameters entry terminalTime hterminal coefficient bit claim position start
  let levels := Nat.clog 2 parameters.vertices
  let bound := metadataBound parameters (2 ^ levels) levels
  let overhead := C * (bound + 1) ^ D
  let valid := Valid parameters (2 ^ levels) levels
  let value := fun p : Position => StoppingQuery.value parameters.scale parameters.precision 0
    parameters.vertices entry (address p) = p.claim
  let rank := fun p : Position => StoppingQuery.rank parameters.scale parameters.precision 0
    parameters.vertices (address p)
  let potential := fun p => rank p * (overhead + 2) + terminalTime + 1
  let store := fun p : Position => storage q assignment input word (encPosition p)
  have hlength (p : Position) (hp : valid p) : (encPosition p).length ≤ bound :=
    hp.length_encPosition_le
  have hroundCost (p : Position) (hp : valid p) :
      cR * ((encPosition p).length + 1) ^ dR ≤ overhead := by
    have hm := Nat.mul_le_mul_left cR (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hlength p hp) 1) dR)
    have hb := hc bound
    dsimp only [overhead]
    omega
  have hprepared : ∀ p, valid p → body.HaltsWithin (potential p)
        (config q assignment input word (encPosition p) (some body.toPTM.initial)
          (wordGameHeader (player p))) ∧
      (body.AcceptsWithin (potential p)
        (config q assignment input word (encPosition p) (some body.toPTM.initial)
          (wordGameHeader (player p))) ↔ value p) := by
    intro p hp
    have hs := WordGameLeaf.spec_of_potential round' terminal' (control N q)
      player StoppingQuery.ProductRouting.next store valid value potential ?_ ?_ ?_ hp le_rfl
    · simpa only [body, WordGameLeaf.machine_initial, config, store] using hs
    · intro a ha hplayer
      obtain ⟨ht, hv⟩ := hterminal a ha hplayer
      have hview := view_terminal q assignment query hne input word (encPosition a)
        (some terminal.toPTM.initial) []
      refine ⟨terminalTime, ?_, ?_, ?_⟩
      · exact (terminal.haltsWithin_extendTapes_iff (terminalEmbedding q query) _ _).mpr
          (hview ▸ ht)
      · exact ((terminal.acceptsWithin_extendTapes_iff (terminalEmbedding q query) _ _).trans
          (hview ▸ Iff.rfl)).trans hv
      · dsimp only [potential]
        omega
    · intro a ha owner hplayer move
      let t := cR * ((encPosition a).length + 1) ^ dR
      have hrun := run_round round assignment input word (encPosition a)
        (encPosition (StoppingQuery.ProductRouting.next a move)) [owner, move]
        (wordGameHeader (player (StoppingQuery.ProductRouting.next a move))) t
        (hr input [] owner move a)
      refine ⟨t, hrun, ha.next move, ?_⟩
      have hdecrease := rank_next_lt a hplayer move
      rw [ha.parameters] at hdecrease
      have hm := Nat.mul_le_mul_right (overhead + 2) (Nat.succ_le_of_lt hdecrease)
      simp only [Nat.succ_mul] at hm
      have ht := hroundCost a ha
      dsimp only [potential, rank, t]
      omega
    · intro a ha owner hplayer
      have hgame := @value_iff_next a
      rw [ha.parameters] at hgame
      exact hgame entry hplayer
  have hvalid : valid position := valid_root parameters coefficient.isLt bit.isLt claim
  have hs := hprepared position hvalid
  let ws := TwoWordInput.words ass src word (encPosition position)
  let finish : Cfg (s + (N + (q + 4)) + 2) Bool Unit input :=
    { tapesCfg input
        (Function.update ws (protectedTapes s N q (control N q))
          (wordGameHeader (player position))) 0 0 [] with inputPos := 0 }
  have hcontrol : control N q ≠ assignment.castAdd (q + 4) :=
    (Fin.castAdd_ne_natAdd _ _).symm
  have hprefix := hh s (N + (q + 4)) (Nat.le_refl s) (control N q) input position ws []
    (by intro i; simp [ws, ass, src, loadSource, TwoWordInput.words,
      Fin.castAdd_ne_natAdd])
    (by simp [ws, ass, src, loadSource, TwoWordInput.words,
      hcontrol, Fin.castAdd_ne_natAdd])
    (by simp [ws, ass, src, loadSource, TwoWordInput.words,
      (Fin.castAdd_ne_natAdd _ _).symm])
    (by simp [ws, ass, src, loadSource, TwoWordInput.words,
      (Fin.castAdd_ne_natAdd _ _).symm])
  let raw := TwoWordInput.ready ass src input word (encPosition position)
  have hrunning : prepare.runFrom (raw.withState (some prepare.q₀))
      (cH * ((encPosition position).length + 1) ^ dH + 2) = finish.withState none := by
    convert hprefix.1 using 1 <;>
      simp only [prepare, raw, TwoWordInput.ready, wordsCfg, tapesCfg, Cfg.withState,
        Pi.zero_apply, sub_zero, ws, finish, protectedTapes, encBits_apply,
        Function.Embedding.trans_apply, Fin.coe_castAddEmb, Fin.natAddEmb_apply]
    · congr 1
    · apply Cfg.ext <;> rfl
  have hview := view_loaded s q assignment input word (encPosition position)
    (wordGameHeader (player position)) (some body.toPTM.initial)
  have hcont := (body.haltsWithin_extendTapes_iff (loadedEmbedding s N q) _ _).mpr
    (hview ▸ hs.1)
  have hrun := prependTM_spec prepare continuation raw finish _ (potential position)
    hrunning hcont
  have haccept := hrun.2.trans
    (((body.acceptsWithin_extendTapes_iff (loadedEmbedding s N q) _ _).trans
      (hview ▸ Iff.rfl)).trans hs.2)
  have hheaderCost : cH * ((encPosition position).length + 1) ^ dH ≤ overhead := by
    have hm := Nat.mul_le_mul_left cH (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hlength position hvalid) 1) dH)
    have hb := hc bound
    dsimp only [overhead]
    omega
  have hrootRank := StoppingQuery.rank_block_root_le parameters.scale parameters.precision 0
    parameters.vertices 0 0 levels coefficient.val bit.val
  rw [← root_address parameters coefficient.val bit.val claim] at hrootRank
  have htime : cH * ((encPosition position).length + 1) ^ dH + 2 + potential position ≤
      clock C D parameters terminalTime := by
    have hm := Nat.mul_le_mul_right (overhead + 2) hrootRank
    change rank position * (overhead + 2) ≤
      (13 * (levels * (SignedValueGame.height (3 ^ modulusExp parameters.scale)
        parameters.precision + 2 * SignedValueGame.rounds parameters.precision + 11) + 1) + 12) *
          (overhead + 2) at hm
    change cH * ((encPosition position).length + 1) ^ dH + 2 +
        (rank position * (overhead + 2) + terminalTime + 1) ≤
      (13 * (levels * (SignedValueGame.height (3 ^ modulusExp parameters.scale)
        parameters.precision + 2 * SignedValueGame.rounds parameters.precision + 11) + 1) +
          12 + 1) * (overhead + 2) + terminalTime + 1
    simp only [Nat.add_mul, Nat.one_mul] at hm ⊢
    omega
  have hvalue : value position ↔
      ((representative parameters.scale parameters.precision
        (∏ vertex ∈ Finset.range parameters.vertices, entry 0 vertex)).coeff
          coefficient.val).val.testBit bit.val = claim := by
    dsimp only [value, position]
    rw [root_address, StoppingQuery.value_product_root]
    rfl
  refine ⟨hrun.1.mono htime, ?_⟩
  exact ⟨fun h => hvalue.mp (haccept.mp (h.of_halted_stepCoins hrun.1)),
    fun h => (haccept.mpr (hvalue.mpr h)).mono htime⟩

end Turing.MultiTapeATM.StoppingProduct
