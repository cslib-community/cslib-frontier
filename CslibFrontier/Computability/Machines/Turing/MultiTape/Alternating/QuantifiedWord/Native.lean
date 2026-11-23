/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordPredicate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.FramedPrefixInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds

/-!
# Native quantified programs from one stored input

A native polynomial-time flag function and a native polynomial-time terminal checker give one
finite alternating machine. The shared loader computes the flags before play. The existing
quantified-word machine overwrites them with choices, and a charged rewind prepares those choices
for the two-word checker. Its input context is preserved throughout all quantified moves.

## Main results

* `Turing.MultiTapeATM.QuantifiedWord.exists_on_words`: evaluate a native checker after an
  arbitrary runtime flag word, with the input context on a separate protected tape.
* `Turing.MultiTapeATM.QuantifiedWord.exists_evaluator`: construct the flags and evaluate the
  quantified program from one stored encoded input, with a complete polynomial clock.
* `Turing.MultiTapeATM.QuantifiedWord.exists_of_terminal`: prepare flags from a stored input and
  invoke a supplied alternating terminal once per branch, preserving both clock components.
* `Turing.MultiTapeATM.QuantifiedWord.exists_of_inO`: native deterministic terminal checks with
  separate preparation and terminal clocks, including a charged rewind.
* `Turing.MultiTapeATM.QuantifiedWord.exists_linear_evaluator`: retain linear dependence on a
  long input component when all remaining work has polynomial short-data bounds.
-/

public section

namespace Turing.MultiTapeATM.QuantifiedWord

open MultiTapeTM

private theorem config_ready {K : ℕ} {S : Type} (i j : Fin K) (hne : i ≠ j)
    (input x y : List Bool) (state : Option S) :
    WordGameLeaf.config j state y 0 (TwoWordInput.ready i j input x []) =
      (TwoWordInput.ready i j input x y).withState state := by
  apply Cfg.ext <;> try rfl
  · funext l z
    by_cases hi : l = i <;> by_cases hj : l = j <;>
      simp_all [WordGameLeaf.config, TwoWordInput.ready, TwoWordInput.words, wordsCfg,
        Cfg.withState]
  · funext l
    by_cases hj : l = j <;>
      simp [WordGameLeaf.config, TwoWordInput.ready, wordsCfg, Cfg.withState, hj]

/-- A finite machine plays any stored flag word and evaluates a native terminal checker.
The common bound is polynomial in the context and flag lengths; neither the machine nor its
constants depend on the context or the quantifier pattern. -/
theorem exists_on_words {α : Type} (enc : α ↪ List Bool) (check : α × List Bool → Bool)
    (hcheck : ComputableInPolyTime check (encPair enc encBits) encBool) :
    ∃ (K : ℕ) (context choices : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ), context ≠ choices ∧
      ∀ (input : List Bool) (a : α) (players : List Bool),
        let start := (TwoWordInput.ready context choices input (enc a) players).withState
          (some atm.toPTM.initial)
        let time := C * ((enc a).length + players.length + 1) ^ D
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ plays (fun xs => check (a, xs) = true) [] players) := by
  obtain ⟨d, e, hdeg⟩ := hcheck.exists_degree
  obtain ⟨K, i, j, S, hS, terminal, c, hne, hterminal⟩ :=
    TwoWordPredicate.exists_of_inO hdeg.inO
  let leaf := prependTM (TwoWordLoad.rewind j) terminal
  let atm := machine leaf j
  have hpoly : Cslib.PolynomiallyBounded
      (fun n => n + 2 + c * (2 * n + 1 + (2 * n + 2) ^ d + 1) + 2 * n + 1) := by
    fun_prop
  obtain ⟨C, D, hbound⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  refine ⟨K, i, j, _, inferInstance, atm, C, D, hne, ?_⟩
  intro input a players start time
  let storage := TwoWordInput.ready i j input (enc a) []
  let pairLength := 2 * (enc a).length + 1 + players.length
  let terminalTime := c * (pairLength + (pairLength + 1) ^ d + 1)
  let leafTime := players.length + 2 + terminalTime
  have hleaf (xs : List Bool) (hx : xs.length = players.length) :
      leaf.HaltsWithin leafTime (WordGameLeaf.config j (some leaf.toPTM.initial)
        xs xs.length storage) ∧
      (leaf.AcceptsWithin leafTime (WordGameLeaf.config j (some leaf.toPTM.initial)
        xs xs.length storage) ↔ check (a, xs) = true) := by
    have ht := hterminal input a xs
    have hlen : (encPair enc encBits (a, xs)).length = pairLength := by
      simp [encBits_apply, pairLength, hx]
    change terminal.HaltsWithin
        (c * ((encPair enc encBits (a, xs)).length +
          ((encPair enc encBits (a, xs)).length + 1) ^ d + 1)) _ ∧ _ at ht
    rw [hlen] at ht
    have hr := TwoWordLoad.runs_rewind j xs storage xs.length le_rfl
    have hfinish : WordGameLeaf.config j none xs 0 storage =
        TwoWordInput.ready i j input (enc a) xs := config_ready i j hne input (enc a) xs none
    rw [hfinish] at hr
    have h := prependTM_spec (TwoWordLoad.rewind j) terminal
      (WordGameLeaf.config j none xs xs.length storage)
      (TwoWordInput.ready i j input (enc a) xs) (xs.length + 2) terminalTime hr.1 ht.1
    refine ⟨?_, ?_⟩
    · simpa only [leaf, leafTime, hx, WordGameLeaf.config, Cfg.withState,
        MultiTapePTM.toNTM, MultiTapePTM.branches, MultiTapeMachine.toNTM] using h.1
    · simpa only [leaf, leafTime, hx, WordGameLeaf.config, Cfg.withState,
        MultiTapePTM.toNTM, MultiTapePTM.branches, MultiTapeMachine.toNTM] using h.2.trans ht.2
  have hgame := spec leaf j leafTime storage (fun xs => check (a, xs) = true) [] players (by
    intro xs hx
    simpa only [List.nil_append] using hleaf xs hx)
  simp only [List.nil_append, List.length_nil] at hgame
  rw [config_ready i j hne, ← machine_initial leaf j] at hgame
  have htime : leafTime + 2 * players.length + 1 ≤ time := by
    calc
      _ ≤ ((enc a).length + players.length) + 2 +
          c * (2 * ((enc a).length + players.length) + 1 +
            (2 * ((enc a).length + players.length) + 2) ^ d + 1) +
          2 * ((enc a).length + players.length) + 1 := by
        have hl : pairLength ≤ 2 * ((enc a).length + players.length) + 1 := by
          dsimp only [pairLength]
          omega
        have hp : (pairLength + 1) ^ d ≤
            (2 * ((enc a).length + players.length) + 2) ^ d :=
          Nat.pow_le_pow_left (by omega) d
        have hm := Nat.mul_le_mul_left c (show
          pairLength + (pairLength + 1) ^ d + 1 ≤
            2 * ((enc a).length + players.length) + 1 +
              (2 * ((enc a).length + players.length) + 2) ^ d + 1 by omega)
        dsimp only [leafTime, terminalTime]
        omega
      _ ≤ time := hbound ((enc a).length + players.length)
  exact ⟨hgame.1.mono htime, ⟨fun h => hgame.2.mp (h.of_halted_stepCoins hgame.1),
    fun h => (hgame.2.mpr h).mono htime⟩⟩

/-- Prepare all flags from one encoded context and run its quantified program. All physical
copying, flag computation, choices, rewinding and terminal evaluation are included in the
polynomial bound. Only the single encoded context is supplied at runtime. -/
theorem exists_evaluator {α : Type} (enc : α ↪ List Bool) (players : α → List Bool)
    (check : α × List Bool → Bool)
    (hplayers : ComputableInPolyTime players enc encBits)
    (hcheck : ComputableInPolyTime check (encPair enc encBits) encBool) :
    ∃ (K : ℕ) (source : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ),
      ∀ (input : List Bool) (a : α),
        let start := WordGameLeaf.config source (some atm.toPTM.initial) (enc a) 0
          (TwoWordLoad.blank K input)
        let time := C * ((enc a).length + 1) ^ D
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔
            plays (fun xs => check (a, xs) = true) [] (players a)) := by
  obtain ⟨K, i, j, S, hS, leaf, c, d, hne, hleaf⟩ := exists_on_words enc check hcheck
  obtain ⟨dF, eF, hF⟩ := hplayers.exists_degree
  have hid : ComputableInPolyTime (fun a : α => a) enc enc := .id'
  obtain ⟨dI, eI, hI⟩ := hid.exists_degree
  let dL := max dI dF
  let T := fun a : α => ((enc a).length + 1) ^ dL
  have hId : ComputableInO (fun a : α => a) enc enc T T :=
    hI.inO.mono_le
      (fun a => Nat.pow_le_pow_right (by omega) (Nat.le_max_left dI dF))
      (fun a => Nat.pow_le_pow_right (by omega) (Nat.le_max_left dI dF))
  have hFlags : ComputableInO players enc encBits T T :=
    hF.inO.mono_le
      (fun a => Nat.pow_le_pow_right (by omega) (Nat.le_max_right dI dF))
      (fun a => Nat.pow_le_pow_right (by omega) (Nat.le_max_right dI dF))
  obtain ⟨U, src, Q, hQ, atm, cL, hload⟩ :=
    TwoWordLoad.exists_load_from hId hFlags i j hne leaf
  have hlength : PolyBounded (fun a => (enc a).length) (fun a => (players a).length) :=
    hplayers.polyBounded_length
  have ht : PolyBounded (fun a => (enc a).length)
      (fun a => cL * (T a + 1) + 8 + c * ((enc a).length + (players a).length + 1) ^ d) := by
    have hinput : PolyBounded (fun a => (enc a).length) (fun a => (enc a).length) := .self
    exact (((PolyBounded.const cL).mul
      (((hinput.add (.const 1)).pow dL).add (.const 1))).add (.const 8)).add
        ((PolyBounded.const c).mul (((hinput.add hlength).add (.const 1)).pow d))
  obtain ⟨C, D, hbound⟩ := ht.exists_le
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro input a start time
  have he := hleaf input a (players a)
  have h := hload input a 0 (Nat.zero_le _) _ he.1
  simp only [Nat.zero_add] at h
  have htime := hbound a
  exact ⟨h.1.mono htime, ⟨fun hacc => he.2.mp (h.2.mp (hacc.of_halted_stepCoins h.1)),
    fun hacc => (h.2.mpr (he.2.mpr hacc)).mono htime⟩⟩

/-- Prepare a flag word from one stored input and run any finite alternating terminal on the
completed encoded pair. The terminal budget is charged once, independently of the quantifier
pattern. This version preserves a sharp native preparation clock instead of replacing it by a
polynomial in the full context length. -/
theorem exists_of_terminal {α : Type} {enc : α ↪ List Bool} {flags : α → List Bool}
    {T : α → ℕ}
    (hflags : ComputableInO (fun a => (a, flags a)) enc (encPair enc encBits) T T)
    {K : ℕ} {S : Type} [Finite S] (source : Fin K) (terminal : MultiTapeATM K Bool S) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (c : ℕ),
      ∀ (host : List Bool) (a : α) (pos : ℕ), pos ≤ (enc a).length →
        ∀ (t : ℕ) (P : List Bool → Prop),
        (∀ xs, xs.length = (flags a).length →
          let word := encPair enc encBits (a, xs)
          let cfg := SharedWordFork.start source terminal host word word.length
          terminal.HaltsWithin t cfg ∧ (terminal.AcceptsWithin t cfg ↔ P xs)) →
        let start := SharedWordFork.start src atm host (enc a) pos
        let time := pos + c * (T a + 1) + 8 +
          ((frame (enc a)).length + (t + 2 * (flags a).length + 1))
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ plays P [] (flags a)) := by
  let game := machine terminal source
  obtain ⟨U, src, Q, hQ, atm, c, hprepare⟩ :=
    FramedPrefixInput.exists_prepend_work hflags source game
  refine ⟨U, src, Q, hQ, atm, c, ?_⟩
  intro host a pos hpos t P hterminal
  let pre := frame (enc a)
  have hgame := spec terminal source t (TwoWordLoad.blank K host)
    (fun word => P (word.drop pre.length)) pre (flags a) (by
      intro xs hxs
      have ht := hterminal xs hxs
      simpa only [encPair_apply, encBits_apply, List.drop_left, SharedWordFork.start] using ht)
  rw [← machine_initial terminal source] at hgame
  have hp := hprepare host a pos hpos _ hgame.1
  have hplay := plays_append_prefix (fun word => P (word.drop pre.length)) pre [] (flags a)
  simp only [List.append_nil, List.drop_left] at hplay
  exact ⟨hp.1, hp.2.trans (hgame.2.trans hplay)⟩


/-- A finite alternating evaluator from native preparation and deterministic-check certificates.
The common terminal budget includes the completed word's rewind and the check's original clock;
no polynomial envelope is imposed on either input-dependent resource function. -/
theorem exists_of_inO {α : Type} {enc : α ↪ List Bool} {flags : α → List Bool}
    {check : α × List Bool → Bool} {T : α → ℕ} {V W : α × List Bool → ℕ}
    (hflags : ComputableInO (fun a => (a, flags a)) enc (encPair enc encBits) T T)
    (hcheck : ComputableInO check (encPair enc encBits) encBool V W) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q)
      (cPrepare cCheck : ℕ),
      ∀ (host : List Bool) (a : α) (pos : ℕ), pos ≤ (enc a).length →
        ∀ t : ℕ,
        (∀ xs, xs.length = (flags a).length →
          (encPair enc encBits (a, xs)).length + 2 + cCheck * (V (a, xs) + 1) ≤ t) →
        let start := SharedWordFork.start src atm host (enc a) pos
        let time := pos + cPrepare * (T a + 1) + 8 +
          ((frame (enc a)).length + (t + 2 * (flags a).length + 1))
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ plays (fun xs => check (a, xs) = true) [] (flags a)) := by
  obtain ⟨u, S, hS, runner, cCheck, hr⟩ := WorkTapePredicate.exists_of_inO hcheck
  let deterministic := MultiTapeATM.ofTMs (fun _ => runner) (fun _ => false)
  let source : Fin (u + 2) := Fin.natAdd u 0
  let terminal := prependTM (TwoWordLoad.rewind source) deterministic
  obtain ⟨U, src, Q, hQ, atm, cPrepare, hgame⟩ := exists_of_terminal hflags source terminal
  refine ⟨U, src, Q, hQ, atm, cPrepare, cCheck, ?_⟩
  intro host a pos hpos t hbound
  apply hgame host a pos hpos t (fun xs => check (a, xs) = true)
  intro xs hxs
  let word := encPair enc encBits (a, xs)
  have hd : deterministic.HaltsWithin (cCheck * (V (a, xs) + 1))
      ((WorkTapePredicate.config host word).withState (some deterministic.toPTM.initial)) ∧
      (deterministic.AcceptsWithin (cCheck * (V (a, xs) + 1))
        ((WorkTapePredicate.config host word).withState (some deterministic.toPTM.initial)) ↔
          check (a, xs) = true) := by
    rw [MultiTapeATM.haltsWithin_ofTMs_const_iff, MultiTapeATM.acceptsWithin_ofTMs_const_iff]
    rw [show deterministic.toPTM.initial = runner.q₀ from rfl, hr]
    simp [WorkTapePredicate.config, Cfg.withState, tapesCfg]
  rw [← SharedWordFork.start_eq_workTape deterministic host word] at hd
  have h := SharedWordFork.rewind_spec source deterministic host word word.length _ le_rfl hd.1
  have hb := hbound xs hxs
  exact ⟨h.1.mono hb, ⟨fun acc => hd.2.mp (h.2.mp (acc.of_halted_stepCoins h.1)),
    fun v => (h.2.mpr (hd.2.mpr v)).mono hb⟩⟩

/-- A fixed finite evaluator with linear dependence on a long input component and polynomial
short-data cost. The measured bounds `long`, `short`, and `challenge` accompany actual native
preparation/check certificates. The only other premises bound encoding and completed-challenge
lengths; the machine and clock constants are chosen before every runtime input. -/
theorem exists_linear_evaluator {α : Type} {enc : α ↪ List Bool} {flags : α → List Bool}
    {check : α × List Bool → Bool} {long short : α → ℕ} {challenge : α × List Bool → ℕ}
    {dPrepare dCheck : ℕ}
    (hflags : ComputableInO (fun a => (a, flags a)) enc (encPair enc encBits)
      (fun a => long a + short a ^ dPrepare) (fun a => long a + short a ^ dPrepare))
    (hcheck : ComputableInO check (encPair enc encBits) encBool
      (fun x => long x.1 + challenge x ^ dCheck) (fun x => long x.1 + challenge x ^ dCheck))
    (K : ℕ) (hshort : ∀ a, 1 ≤ short a)
    (hinput : ∀ a, (enc a).length ≤ long a + K * short a + K)
    (hflagLength : PolyBounded short (fun a => (flags a).length))
    (hchallenge : ∀ a xs, xs.length = (flags a).length →
      challenge (a, xs) ≤ K * short a + xs.length + K) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (a : α),
        let start := SharedWordFork.start src atm host (enc a) 0
        let time := C * (long a + short a ^ D + 1)
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ plays (fun xs => check (a, xs) = true) [] (flags a)) := by
  obtain ⟨U, src, Q, hQ, atm, cPrepare, cCheck, hgame⟩ := exists_of_inO hflags hcheck
  let size := fun a => K * short a + (flags a).length + K
  have hsize : PolyBounded short size :=
    (((PolyBounded.const K).mul PolyBounded.self).add hflagLength).add (.const K)
  let framing := fun a => 2 * (K * short a) + 2 * K + 1
  have hprefix : PolyBounded short framing :=
    (((PolyBounded.const 2).mul ((PolyBounded.const K).mul PolyBounded.self)).add
      (.const (2 * K))).add (.const 1)
  let tail := fun a => framing a + (flags a).length + 2 + cCheck * (size a ^ dCheck + 1)
  have htail : PolyBounded short tail :=
    ((hprefix.add hflagLength).add (.const 2)).add
      ((PolyBounded.const cCheck).mul ((hsize.pow dCheck).add (.const 1)))
  let minor := fun a => cPrepare * (short a ^ dPrepare + 1) + 8 +
    (framing a + (tail a + 2 * (flags a).length + 1))
  have hminor : PolyBounded short minor :=
    (((PolyBounded.const cPrepare).mul ((PolyBounded.self.pow dPrepare).add (.const 1))).add
      (.const 8)).add
      (hprefix.add ((htail.add ((PolyBounded.const 2).mul hflagLength)).add (.const 1)))
  obtain ⟨C, D, hbound⟩ := hminor.exists_le_linear_add_pow
    long (cPrepare + 4 + cCheck) hshort
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host a start time
  let t := (2 + cCheck) * long a + tail a
  have ht (xs : List Bool) (hxs : xs.length = (flags a).length) :
      (encPair enc encBits (a, xs)).length + 2 +
        cCheck * (long a + challenge (a, xs) ^ dCheck + 1) ≤ t := by
    have hsize' : challenge (a, xs) ≤ size a := by
      simpa only [size, hxs] using hchallenge a xs hxs
    have hlen := hinput a
    have hp := Nat.pow_le_pow_left hsize' dCheck
    have hm := Nat.mul_le_mul_left cCheck hp
    simp only [length_encPair, encBits_apply, hxs]
    dsimp only [t, tail, framing]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega
  have h := hgame host a 0 (Nat.zero_le _) t ht
  simp only [Nat.zero_add] at h
  have hclock : cPrepare * (long a + short a ^ dPrepare + 1) + 8 +
      ((frame (enc a)).length + (t + 2 * (flags a).length + 1)) ≤ time := by
    refine le_trans ?_ (hbound a)
    have hlen := hinput a
    simp only [length_frame]
    dsimp only [minor, t, framing]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega
  exact ⟨h.1.mono hclock, ⟨fun acc => h.2.mp (acc.of_halted_stepCoins h.1),
    fun v => (h.2.mpr v).mono hclock⟩⟩

end Turing.MultiTapeATM.QuantifiedWord
