/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.WordTransducers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ScheduleHeightWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRoot
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafLayout
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Preparing native depth and count words

The source count remains on tape seven. Two native word computations write its ceiling logarithm
in binary on tape zero and in unary on tape four. Their scratch lies beyond the twelve protected
controller tapes, so context, width, bit index and every other protected word survive. All work,
including the host input head movements, is charged in the binary count's length. When a binary
height is already known, the same protected writer constructs its unary frontier and power-of-two
count in time linear in the height, without recomputing its logarithm.
-/

public noncomputable section

namespace Turing.MultiTapeATM.CarrySaveDepthPrepare

open MultiTapeTM

/-- Work-tape words and heads at their origins, with the host input parked at its left blank. -/
@[expose] def config {k : ℕ} (input : List Bool) (words : Fin (k + 12) → List Bool)
    (out : List Bool) : Cfg (k + 12) Bool Unit input :=
  { tapesCfg input words 0 0 out with inputPos := 0 }

private def scratchEmbedding (m k : ℕ) (h : m ≤ k) : Fin m ↪ Fin (k + 12) :=
  (Fin.natAddEmb 12).trans (Fin.castLEEmb (by omega))

private theorem scratchEmbedding_val (m k : ℕ) (h : m ≤ k) (i : Fin m) :
    (scratchEmbedding m k h i).val = 12 + i.val := rfl

private def outputEmbedding (m k : ℕ) (h : m ≤ k) (target : Fin 12) :
    Fin (m + 1) ↪ Fin (k + 12) :=
  Fin.Embedding.snoc (scratchEmbedding m k h) (a := ⟨target.val, by omega⟩) (by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have := target.isLt
    simp only [scratchEmbedding_val] at hv
    omega)

private def inputMarker (m k : ℕ) (h : m + 1 ≤ k) (source : Fin 12) :
    Fin 2 ↪ Fin (k + 12) :=
  Function.Embedding.embFinTwo (a := ⟨source.val, by omega⟩) (b := ⟨12 + m, by omega⟩) (by
    intro he
    have hv := congrArg Fin.val he
    have := source.isLt
    change source.val = 12 + m at hv
    omega)

private theorem outputEmbedding_last (m k : ℕ) (h : m ≤ k) (target : Fin 12) :
    outputEmbedding m k h target (Fin.last m) = ⟨target.val, by omega⟩ :=
  Fin.Embedding.snoc_last

private theorem outputEmbedding_cast (m k : ℕ) (h : m ≤ k) (target : Fin 12) (i : Fin m) :
    outputEmbedding m k h target i.castSucc = scratchEmbedding m k h i :=
  Fin.Embedding.snoc_castSucc

private def embedding (m k : ℕ) (h : m + 1 ≤ k) (source target : Fin 12)
    (htarget : target ≠ source) : Fin (m + 1 + 2) ↪ Fin (k + 12) :=
  Fin.Embedding.append (x := outputEmbedding m k (by omega) target)
    (y := inputMarker m k h source) (by
      rw [Set.disjoint_left]
      rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
      have hs := source.isLt
      have ht := target.isLt
      have hne : target.val ≠ source.val := fun he => htarget (Fin.ext he)
      cases i using Fin.lastCases with
      | last =>
        fin_cases j <;>
          have hv := congrArg Fin.val hj <;>
          simp [inputMarker, outputEmbedding_last,
            Function.Embedding.embFinTwo_apply_zero,
            Function.Embedding.embFinTwo_apply_one] at hv <;> omega
      | cast i =>
        fin_cases j <;>
          have hv := congrArg Fin.val hj <;>
          simp [inputMarker, outputEmbedding_cast,
            Function.Embedding.embFinTwo_apply_zero,
            Function.Embedding.embFinTwo_apply_one, scratchEmbedding_val] at hv <;> omega)

private theorem embedding_source (m k : ℕ) (h : m + 1 ≤ k) (source target : Fin 12)
    (htarget : target ≠ source) :
    embedding m k h source target htarget (Fin.natAdd (m + 1) 0) =
      ⟨source.val, by have := source.isLt; omega⟩ := by
  simp [embedding, inputMarker, Function.Embedding.embFinTwo_apply_zero]

private theorem embedding_output (m k : ℕ) (h : m + 1 ≤ k) (source target : Fin 12)
    (htarget : target ≠ source) :
    embedding m k h source target htarget ((Fin.last m).castAdd 2) =
      ⟨target.val, by omega⟩ := by
  simp [embedding, outputEmbedding_last]

private theorem embedding_private (m k : ℕ) (h : m + 1 ≤ k) (source target : Fin 12)
    (htarget : target ≠ source) (j : Fin (m + 1 + 2))
    (hsource : j ≠ Fin.natAdd (m + 1) 0) (houtput : j ≠ (Fin.last m).castAdd 2) :
    12 ≤ (embedding m k h source target htarget j).val := by
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.lastCases with
    | last => exact (houtput rfl).elim
    | cast j => simp [embedding, outputEmbedding_cast, scratchEmbedding_val]
  | right j =>
    fin_cases j
    · exact (hsource rfl).elim
    · simp [embedding, inputMarker, Function.Embedding.embFinTwo_apply_one]

private theorem exists_prepare_pair {β γ : Type} {encB : β ↪ List Bool}
    {encU : γ ↪ List Bool} {f : ℕ → β} {g : ℕ → γ} {T : ℕ → ℕ}
    (hf : ComputableInO f encNat encB T T) (hg : ComputableInO g encNat encU T T)
    (source left right : Fin 12) (hl : left ≠ source) (hr : right ≠ source)
    (hlr : right ≠ left) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c : ℕ),
      ∀ (input : List Bool) (n : ℕ) (words : Fin (k + 12) → List Bool) (out : List Bool),
        words ⟨source.val, by have := source.isLt; omega⟩ = encNat n →
        words ⟨left.val, by have := left.isLt; omega⟩ = [] →
        words ⟨right.val, by have := right.isLt; omega⟩ = [] →
        (∀ i, 12 ≤ i.val → words i = []) →
        tm.runFrom ((config input words out).withState (some tm.q₀)) (c * (T n + 1)) =
          (config input
            (Function.update
              (Function.update words ⟨left.val, by have := left.isLt; omega⟩ (encB (f n)))
              ⟨right.val, by have := right.isLt; omega⟩ (encU (g n))) out).withState none := by
  obtain ⟨mB, SB, hSB, binary, cB, hB⟩ := WordFunction.exists_of_inO hf
  obtain ⟨mU, SU, hSU, unary, cU, hU⟩ := WordFunction.exists_of_inO hg
  let := hSB
  let := hSU
  let k := max mB mU + 1
  let eB := embedding mB k (by simp [k]) source left hl
  let eU := embedding mU k (by simp [k]) source right hr
  let l : Fin (k + 12) := ⟨left.val, by have := left.isLt; omega⟩
  let r : Fin (k + 12) := ⟨right.val, by have := right.isLt; omega⟩
  let s : Fin (k + 12) := ⟨source.val, by have := source.isLt; omega⟩
  refine ⟨k, _, inferInstance, ((binary.extendTapes eB).seq (unary.extendTapes eU)).fromLeftBlank,
    cB + cU + 2, ?_⟩
  intro input n words out hsource hleft hright hblank
  have hoB : eB ((Fin.last mB).castAdd 2) = l := embedding_output ..
  have hoU : eU ((Fin.last mU).castAdd 2) = r := embedding_output ..
  have hsl : s ≠ l := fun he => hl (Fin.ext (congrArg Fin.val he).symm)
  have hrl : r ≠ l := fun he =>
    hlr (Fin.ext (congrArg (fun i : Fin (k + 12) => i.val) he))
  have hb := hB (k + 12) eB input n words out
    (by simpa only [eB, embedding_source] using hsource)
    (by
      intro j hj
      by_cases ho : j = (Fin.last mB).castAdd 2
      · subst j
        simpa only [hoB] using hleft
      · exact hblank _ (embedding_private mB k _ source left hl j hj ho))
  have hu := hU (k + 12) eU input n (Function.update words l (encB (f n))) out
    (by simpa only [eU, embedding_source, ← show s = ⟨source.val, by omega⟩ from rfl,
      Function.update_of_ne hsl] using hsource)
    (by
      intro j hj
      by_cases ho : j = (Fin.last mU).castAdd 2
      · subst j
        simpa only [hoU, Function.update_of_ne hrl] using hright
      · have hprivate := embedding_private mU k (by simp [k]) source right hr j hj ho
        have hne : eU j ≠ l := by
          intro he
          have hv := congrArg Fin.val he
          have := left.isLt
          change (embedding mU k _ source right _ j).val = left.val at hv
          omega
        rw [Function.update_of_ne hne]
        exact hblank _ hprivate)
  rw [hoB] at hb
  rw [hoU] at hu
  have hrun := (hb.seq hu).fromLeftBlank rfl rfl
  have hclock : cB * (T n + 1) + cU * (T n + 1) + 2 ≤
      (cB + cU + 2) * (T n + 1) := by nlinarith
  unfold config
  rw [runFrom_eq_of_halt _ _ hclock (by rw [hrun.1]; rfl), hrun.1]

/-- One finite native preparation constructs both depth counters from the binary count.
All twelve protected words except height and unary frontier survive. The bound depends only on
the count's binary length; the source count, width and potentially long predicate context are
never copied into the function's input. -/
theorem exists_prepare :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c d : ℕ),
      ∀ (input : List Bool) (n : ℕ) (words : Fin (k + 12) → List Bool) (out : List Bool),
        words 7 = encNat n → words 0 = [] → words 4 = [] →
        (∀ i, 12 ≤ i.val → words i = []) →
        tm.runFrom
          ((config input words out).withState (some tm.q₀))
          (c * ((encNat n).length + 1) ^ d) =
          (config input
              (Function.update (Function.update words 0 (encNat (Nat.clog 2 n))) 4
                (encUnary (Nat.clog 2 n))) out).withState none := by
  obtain ⟨dB, eB, hB⟩ := ComputableInPolyTime.binary_clog_two_nat.exists_degree
  obtain ⟨dU, eU, hU⟩ := ComputableInPolyTime.binary_clog_two.exists_degree
  let d := max dB dU
  have hb := (hB.mono (d' := d) (e' := eB) (le_max_left ..) le_rfl).inO
  have hu := (hU.mono (d' := d) (e' := eU) (le_max_right ..) le_rfl).inO
  obtain ⟨k, S, hS, tm, c, h⟩ :=
    exists_prepare_pair hb hu ⟨7, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩
    (by decide) (by decide) (by decide)
  refine ⟨k, S, hS, tm, 2 * c, d, ?_⟩
  intro input n words out hcount hheight hfront hblank
  have hr := h input n words out
  dsimp only at hr
  have h7 : (⟨7, by omega⟩ : Fin (k + 12)) = 7 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 7 < k + 12 by omega)]
  have h4 : (⟨4, by omega⟩ : Fin (k + 12)) = 4 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 4 < k + 12 by omega)]
  rw [h7, h4] at hr
  have hrun := hr hcount hheight hfront hblank
  have hclock : c * (((encNat n).length + 1) ^ d + 1) ≤
      2 * c * ((encNat n).length + 1) ^ d := by
    have : 1 ≤ ((encNat n).length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  rw [runFrom_eq_of_halt _ _ hclock (by rw [hrun]; rfl), hrun]
  rfl

private theorem two_pow_inO :
    ComputableInO (fun n : ℕ => 2 ^ n) encNat encNat (fun n => n) (fun n => n) := by
  have hmap : ComputableInO (List.map (fun _ : Bool => false)) encBits encBits
      List.length List.length :=
    .of_bounds (ComputableInTimeAndSpace.map_bits _) 8
      (fun l => by omega) (fun _ => by omega) (fun l => by simp; omega)
  have hword : ComputableInO (fun l : List Bool => l.map (fun _ => false) ++ [true])
      encBits encBits List.length List.length :=
    (hmap.append (ComputableInO.const (encMid := encBits) [true]) (fun _ => rfl)).mono
      2 (fun _ => by simp only [encBits_apply]; omega)
        (fun _ => by simp only [encBits_apply]; omega)
  have hu := ComputableInO.natToUnary.of_enc_eq
    (g := fun n => encUnary n) (encC := encBits) (fun _ => rfl)
  exact (hword.comp_linear hu).of_enc_eq fun n => by
    change encNat (2 ^ n) = (encUnary n).map (fun _ => false) ++ [true]
    rw [encNat_apply, ScheduleHeightWord.bits_pow]
    simp [encUnary_apply]

/-- A supplied binary height is expanded only linearly. The source height on tape zero survives;
tape seven receives the binary count `2 ^ height` and tape four the unary frontier. Every other
protected word, including an arbitrarily long context, is untouched. -/
theorem exists_prepare_height :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c : ℕ),
      ∀ (input : List Bool) (height : ℕ) (words : Fin (k + 12) → List Bool) (out : List Bool),
        words 0 = encNat height → words 7 = [] → words 4 = [] →
        (∀ i, 12 ≤ i.val → words i = []) →
        tm.runFrom ((config input words out).withState (some tm.q₀)) (c * (height + 1)) =
          (config input
            (Function.update (Function.update words 7 (encNat (2 ^ height))) 4
              (encUnary height)) out).withState none := by
  obtain ⟨k, S, hS, tm, c, h⟩ := exists_prepare_pair two_pow_inO
    ComputableInO.natToUnary ⟨0, by decide⟩ ⟨7, by decide⟩ ⟨4, by decide⟩
    (by decide) (by decide) (by decide)
  refine ⟨k, S, hS, tm, c, ?_⟩
  intro input height words out hh hn hf hb
  have hr := h input height words out
  dsimp only at hr
  have h7 : (⟨7, by omega⟩ : Fin (k + 12)) = 7 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 7 < k + 12 by omega)]
  have h4 : (⟨4, by omega⟩ : Fin (k + 12)) = 4 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 4 < k + 12 by omega)]
  rw [h7, h4] at hr
  exact hr hh hn hf hb

/-- Root storage before depth preparation: count, width, context and index are already present,
while height, unary frontier, path and private scratch are blank. -/
@[expose] def initial (k : ℕ) (input context : List Bool) (n w bit : ℕ) :
    Cfg (k + 12) Bool Unit input :=
  CarrySaveLeaf.initial k input context (encNat n) (encNat w) [] (encNat bit) [] [] 0 false

/-- Actual initialization of both depth words reaches the canonical counting-root configuration.
The same finite machine works for every count, precision and queried bit. -/
theorem exists_root :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (n w bit : ℕ),
        tm.runFrom ((initial k input context n w bit).withState (some tm.q₀))
          (c * ((encNat n).length + 1) ^ d) =
          (CarrySaveCountingRoot.initial k input context n w bit).withState none := by
  obtain ⟨k, S, hS, tm, c, d, h⟩ := exists_prepare
  refine ⟨k, S, hS, tm, c, d, ?_⟩
  intro input context n w bit
  have hr := h input n
    (CarrySaveLeafLayout.words k context (encNat n) (encNat w) [] (encNat bit) [] [] false) []
    (by simp [CarrySaveLeafLayout.words, Nat.mod_eq_of_lt (show 7 < k + 12 by omega)])
    (by simp [CarrySaveLeafLayout.words])
    (by simp [CarrySaveLeafLayout.words, Nat.mod_eq_of_lt (show 4 < k + 12 by omega)])
    (by
      intro i hi
      exact CarrySaveLeafLayout.words_scratch _ _ _ _ _ _ _ _ _ i (by omega))
  rw [CarrySaveLeafLayout.words_update_height, CarrySaveLeafLayout.words_update_unary] at hr
  simpa only [initial, CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_nil_eq_tapesCfg,
    config, Pi.zero_def] using hr

end Turing.MultiTapeATM.CarrySaveDepthPrepare
