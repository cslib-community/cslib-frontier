/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation.Game
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Fin.Embedding

/-!
# Games of polynomially many moves are in `AP`

A polynomial-time game verifier (`Cslib.Complexity.IsGameVerifier`) decides a problem through a
game of `2 * p n` alternate single-bit moves, the existential player first. Through the
guess-then-verify alternating machine (`Turing.MultiTapeATM.guessVerify`, in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify`)
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09], acceptance in the guessing phase is the game of `L`
alternate moves (`Turing.MultiTapeATM.GuessVerify.acceptsWithin_lift_tag`), giving the overall time
and acceptance specification (`Turing.MultiTapeATM.guessVerify_spec`).

For a game verifier `V`, `prep` writes the frame of `2 * p (enc a).length` bits followed by
`enc a`, by a polynomial-time machine with its output redirected to tape `B`
(`Turing.MultiTapeTM.outputToWord`), and `verify` runs a polynomial-time machine computing
`V (a, z)` from the word on tape `B`, which is the encoded pair `encPair encBits enc (z, a)` of the
moves `z` and the instance (`Turing.MultiTapeTM.inputFromWord`). The machine therefore runs within
polynomial time, and it accepts `enc a` exactly when the existential player wins the game, proving
that every problem with a polynomial-time game verifier is in `AP`
(`Cslib.Complexity.IsGameVerifier.mem_AP`).

The same machine works at any time bound: a game of `L a` moves whose number of moves is
computable in unary, and whose verifier runs, within time `O(t n)`, with `n + L a = O(t n)`, is in
`ATIME t` (`Cslib.Complexity.mem_ATIME_of_alternation`). The term `n` pays for copying the instance
next to the moves, since the input head is sequential. Both results come from one private bound on
the time of the guess-then-verify machine in terms of the times of its two deterministic phases.

## Main results

* `Turing.MultiTapeATM.GuessVerify.acceptsWithin_lift_tag`: the guessing phase is a game.
* `Turing.MultiTapeATM.guessVerify_spec`: the guess-then-verify machine plays the game within the
  time of `prep`, plus `4 * L + 3`, plus the time of `verify`.
* `Cslib.Complexity.IsGameVerifier.mem_AP`: every problem with a polynomial-time game verifier is
  in `AP`.
* `Cslib.Complexity.mem_ATIME_of_alternation`: a game of `O(t n)` moves with a verifier within time
  `O(t n)` is in `ATIME t`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Turing.MultiTapeATM

namespace GuessVerify

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} {B : Fin k} {prep : MultiTapeTM k Bool S₁}
  {verify : MultiTapeTM k Bool S₂} {input : List Bool}

/-- **The guessing phase.** From the tag of the first of `r` pairs `true, true` that follow the
pairs of the moves `zd`, with the player `u` to move (`true` for universal), acceptance within
`2 * r + 1 + n` moves is the game of `r` alternate moves, the first by the player `u`, after which
the configuration ending the guessing phase accepts within `n` moves. -/
theorem acceptsWithin_lift_tag (r : ℕ) : ∀ (zd : List Bool) (u : Bool) (n : ℕ),
    (guessVerify B prep verify).AcceptsWithin (2 * r + 1 + n)
      (lift S₁ B verify (cfg (input := input) B (some (.tag u))
        (frame (zd ++ List.replicate r true) ++ input) (2 * zd.length))) ↔
    Cslib.Complexity.Alternation (!u) (List.replicate r 1) fun zr =>
      (guessVerify B prep verify).AcceptsWithin n
        (lift S₁ B verify (cfg (input := input) B none (frame (zd ++ zr) ++ input)
          (2 * (zd.length + r)))) := by
  induction r with
  | zero =>
    intro zd u n
    rw [show 2 * 0 + 1 + n = n + 1 by omega, List.replicate_zero, List.replicate_zero,
      List.append_nil, acceptsWithin_succ_of_next_eq (next_lift_halt zd u),
      Cslib.Complexity.alternation_nil, List.append_nil, add_zero]
  | succ r ih =>
    intro zd u n
    simp only [List.replicate_succ]
    have hstate : (lift S₁ B verify (cfg (input := input) B (some (.move u))
        (frame (zd ++ true :: List.replicate r true) ++ input)
        (2 * zd.length + 1))).state = some (.inr (.inl (.move u))) := rfl
    have hgame (b : Bool) := ih (zd ++ [b]) (!u) n
    simp only [Bool.not_not, List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton, show zd.length + 1 + r = zd.length + (r + 1) by ring] at hgame
    rw [show 2 * (r + 1) + 1 + n = 2 * r + 1 + n + 1 + 1 by omega,
      acceptsWithin_succ_of_next_eq (next_lift_tag zd _ true u)]
    cases u
    · rw [(guessVerify B prep verify).acceptsWithin_succ_of_existential hstate rfl,
        Bool.not_false, Cslib.Complexity.alternation_true_one_cons]
      exact exists_congr fun b => by
        rw [next_lift_move]
        exact hgame b
    · rw [(guessVerify B prep verify).acceptsWithin_succ_of_universal hstate rfl,
        Bool.not_true, Cslib.Complexity.alternation_false_one_cons]
      exact forall_congr' fun b => by
        rw [next_lift_move]
        exact hgame b

end GuessVerify

section Spec

open MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type} {B : Fin k} {prep : MultiTapeTM k Bool S₁}
  {verify : MultiTapeTM k Bool S₂} {input : List Bool}

/-- **The guess-then-verify machine plays the game of `L` moves.** Suppose that `prep`, started on
the input with blank work tapes, has halted after `t₁` steps with the frame of `L` bits `true`
followed by the input on tape `B` and every other work tape blank, and that `verify`, started on
the frame of any `L` moves `z` followed by the input on tape `B` and every other work tape blank,
has halted after `t₂` steps with output `[V z]`. Then for some
`T ≤ t₁ + 4 * L + 3 + t₂`, every list of `T` moves reaches a halted configuration, and the
machine accepts within `T` moves exactly when the existential player wins the game of `L`
alternate moves, the existential first, with winning condition `V`. -/
theorem guessVerify_spec {L t₁ t₂ : ℕ} {V : List Bool → Bool}
    (hprep : prep.runFrom (Cfg.init prep.q₀ input) t₁ = wordsCfg input none
      (Function.update (fun _ => []) B (frame (List.replicate L true) ++ input)) [])
    (hverify : ∀ z : List Bool, z.length = L →
      (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ input)) []) t₂).state = none ∧
      (verify.runFrom (wordsCfg input (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ input)) []) t₂).output = [V z]) :
    ∃ T ≤ t₁ + (4 * L + 3 + t₂),
      (guessVerify B prep verify).HaltsWithin T
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input) ∧
      ((guessVerify B prep verify).AcceptsWithin T
        ((guessVerify B prep verify).toPTM.toNTM.initCfg input) ↔
        Cslib.Complexity.Alternation true (List.replicate L 1) fun z => V z = true) := by
  obtain ⟨u, hut, hu⟩ := exists_haltsAt (tm := prep) (cfg := Cfg.init prep.q₀ input)
    (t := t₁) (by rw [hprep]; rfl)
  obtain ⟨hdet, hstart⟩ := GuessVerify.prepare_spec (S₁ := S₁) (verify := verify) hu
    ((hu.runFrom_eq hut).symm.trans hprep)
  have hguess : GuessVerify.cfg (input := input) (State := GuessState) B (some (.tag false))
      (frame (List.replicate L true) ++ input) 0 =
      GuessVerify.cfg B (some (.tag false))
        (frame (([] : List Bool) ++ List.replicate L true) ++ input)
        (2 * ([] : List Bool).length) := rfl
  have hpos (z : List Bool) :
      2 * (([] : List Bool) ++ z).length ≤ (frame z ++ input).length := by
    simpa using two_mul_length_le_length_frame_append z input
  refine ⟨u + (2 * L + 1 + (2 * L + 2 + t₂)), by omega, ?_, ?_⟩
  · rw [haltsWithin_add_iff_of_next_eq hdet, hstart, hguess, GuessVerify.haltsWithin_lift_tag]
    intro z hz
    simpa only [List.nil_append, List.length_nil, zero_add, hz] using
      GuessVerify.haltsWithin_lift_none (S₁ := S₁) (prep := prep) (hpos z) (hverify z hz).1
  · rw [acceptsWithin_add_iff_of_next_eq hdet, hstart, hguess,
      GuessVerify.acceptsWithin_lift_tag, Bool.not_false]
    refine Cslib.Complexity.alternation_congr_of_length fun z hz => ?_
    rw [Cslib.Complexity.sum_replicate_one] at hz
    have hnone := GuessVerify.acceptsWithin_lift_none (S₁ := S₁) (prep := prep) (hpos z)
      (hverify z hz).1
    simp only [List.nil_append, List.length_nil, zero_add, hz] at hnone ⊢
    simp [hnone, (hverify z hz).2]

end Spec

end Turing.MultiTapeATM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **The guess-then-verify machine decides a game within the time of its phases.** Suppose that
`Tg` writes the frame of `L a` bits `true` followed by `enc a` within `tg a` steps, and that `Tv`
computes `W (z, a)` from the frame of any `L a` moves `z` followed by `enc a` within `tv a` steps.
Then the guess-then-verify machine decides, within `tg a + ℓ + 4 * L a + tv a + 9` steps for the
length `ℓ` of the prepared word, the problem won by the existential player in the game of `L a`
alternate moves with winning condition `W`. -/
private theorem decidableInTime_guessVerify {L : α → ℕ} {W : List Bool × α → Bool}
    {k₁ k₂ : ℕ} {S₁ S₂ : Type} [Finite S₁] [Finite S₂] {Tg : MultiTapeTM k₁ Bool S₁}
    {Tv : MultiTapeTM k₂ Bool S₂} {tg tv : α → ℕ}
    (hTg : ∀ a, ∃ s, Tg.ComputesTidilyInTimeAndSpace (enc a)
      (encBits (frame (List.replicate (L a) true) ++ enc a)) (tg a) s)
    (hTv : ∀ a (z : List Bool), z.length = L a →
      ∃ s, Tv.ComputesTidilyInTimeAndSpace (encPair encBits enc (z, a)) (encBool (W (z, a)))
        (tv a) s)
    (hA : ∀ a, a ∈ A ↔ Alternation true (List.replicate (L a) 1) fun z => W (z, a) = true) :
    MultiTapeATM.DecidableInTime A enc fun a =>
      tg a + (frame (List.replicate (L a) true) ++ enc a).length + 2 +
        (4 * L a + 3 + (tv a + 4)) := by
  have hk₁ : k₁ + 1 ≤ k₁ + 1 + (k₂ + 2) := by omega
  have hk₂ : k₂ + 2 ≤ k₁ + 1 + (k₂ + 2) := by omega
  let B : Fin (k₁ + 1 + (k₂ + 2)) := ⟨0, by omega⟩
  let prep := Tg.outputToWord.extendTapes (Fin.embeddingAt hk₁ (Fin.last k₁) B)
  let verify := (Tv.inputFromWord true).extendTapes (Fin.embeddingAt hk₂ (Fin.natAdd k₂ 0) B)
  have hprep (a : α) : prep.runFrom (Cfg.init prep.q₀ (enc a))
      (tg a + (frame (List.replicate (L a) true) ++ enc a).length + 2) =
      wordsCfg (enc a) none (Function.update (fun _ => []) B
        (frame (List.replicate (L a) true) ++ enc a)) [] := by
    obtain ⟨_, hs⟩ := hTg a
    obtain ⟨_, _, hrun, ⟨rfl, rfl⟩, -⟩ := transformsTapes_iff_runFrom.mp
      (hs.outputToWord_onTape (Fin.embeddingAt_source hk₁ (Fin.last k₁) B))
      (enc a) (fun _ => []) [] ⟨rfl, rfl⟩
    exact Cfg.init_eq_wordsCfg .. ▸ hrun
  have hverify (a : α) (z : List Bool) (hz : z.length = L a) :
      (verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (tv a + 4)).state = none ∧
      (verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (tv a + 4)).output =
        [W (z, a)] := by
    obtain ⟨_, hs⟩ := hTv a z hz
    obtain ⟨_, _, hrun, ⟨rfl, rfl⟩, -⟩ := transformsTapes_iff_runFrom.mp
      (hs.inputFromWord_extendTapes true (Fin.embeddingAt_source hk₂ (Fin.natAdd k₂ 0) B))
      (enc a) _ [] rfl
    have hrun' : verify.runFrom (wordsCfg (enc a) (some verify.q₀)
        (Function.update (fun _ => []) B (frame z ++ enc a)) []) (tv a + 4) = _ := hrun
    rw [hrun']
    exact ⟨rfl, rfl⟩
  refine ⟨k₁ + 1 + (k₂ + 2), _, inferInstance, MultiTapeATM.guessVerify B prep verify,
    fun a => ?_⟩
  obtain ⟨T, hT, hhalt, hacc⟩ := MultiTapeATM.guessVerify_spec (hprep a) (hverify a)
  have hrun : (MultiTapeATM.guessVerify B prep verify).toPTM.toNTM.RunsInTime (enc a) T :=
    MultiTapeATM.runsInTime_iff_haltsWithin.mpr hhalt
  refine ⟨hrun.mono hT, ?_⟩
  rw [hA a, MultiTapeATM.accepts_iff_acceptsWithin hrun, hacc]

/-- **Games of polynomially many moves are in `AP`** [Chandra, Kozen and
Stockmeyer][ChandraKozenStockmeyer1981]: a problem with a polynomial-time game verifier is decided
in polynomial time by the guess-then-verify machine, which writes the moves of the two players,
alternately, and then runs the verifier. -/
theorem IsGameVerifier.mem_AP {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : Turing.MultiTapeTM.ComputableInPolyTime V (encPair enc encBits) encBool)
    (h : IsGameVerifier enc p V A) : A ∈ AP enc := by
  -- the number of moves, and the word prepared on tape `B`
  set L : α → ℕ := fun a => 2 * p.eval (enc a).length
  have hL : ComputableInPolyTime L enc encUnary := by fun_prop
  set g : α → List Bool := fun a => frame (List.replicate (L a) true) ++ enc a with hg_def
  have hg : ComputableInPolyTime g enc encBits :=
    (hL.prod ComputableInPolyTime.id').of_enc_eq fun _ => rfl
  have hLb : PolyBounded (fun a => (enc a).length) L := by growth_poly
  have hgl : PolyBounded (fun a => (enc a).length) fun a => (g a).length := by growth_poly
  have hV' : ComputableInPolyTime (fun x : List Bool × α => V (x.2, x.1))
      (encPair encBits enc) encBool :=
    hV.comp ((ComputableInPolyTime.snd encBits enc).prod
      (ComputableInPolyTime.fst encBits enc))
  obtain ⟨cg, dg, k₁, S₁, _, Tg, hTg⟩ := Internal.NormalForm.polyTime hg
  obtain ⟨cv, dv, k₂, S₂, _, Tv, hTv⟩ := Internal.NormalForm.polyTime hV'
  -- the time bounds of the two deterministic phases
  have htg : PolyBounded (fun a => (enc a).length) fun a => cg * ((enc a).length + 1) ^ dg := by
    growth_poly
  have htv : PolyBounded (fun a => (enc a).length) fun a => cv * ((g a).length + 1) ^ dv :=
    (PolyBounded.of_forall_le (size := id) cv dv fun _ => le_rfl).comp hgl
  have hdec := decidableInTime_guessVerify (A := A) (L := L) (W := fun x => V (x.2, x.1))
    (tg := fun a => cg * ((enc a).length + 1) ^ dg) (tv := fun a => cv * ((g a).length + 1) ^ dv)
    (fun a => ⟨_, hTg a⟩)
    (fun a z hz => ⟨_, (hTv (z, a)).mono (le_of_eq (by simp [hg_def, hz])) le_rfl⟩) h
  exact ⟨_, ((htg.add hgl).add (.const 2)).add ((((PolyBounded.const 4).mul hLb).add
    (.const 3)).add (htv.add (.const 4))), hdec⟩

/-- **Games of `O(t n)` moves with an `O(t n)`-time verifier are in `ATIME t`** [Chandra, Kozen
and Stockmeyer][ChandraKozenStockmeyer1981] [Arora and Barak, Section 5.3][AroraBarak09]:
let `a ∈ A` exactly when the existential player wins the game of `L a` alternate single-bit moves,
the existential player first, with winning condition `V`. If `L` is computable in unary within
time `O(TL a)`, the verifier `V` is computable within time `O(TV (a, z))`, and, for a constant `C`,
`n + L a + TL a` and `TV (a, z)` (for every `z` of length `L a`) are at most `C * t n + C`, where
`n` is the length of `enc a`, then the guess-then-verify machine decides `A` within time
`O(t n)`.

This is the time-parametric form of `Cslib.Complexity.IsGameVerifier.mem_AP`; it is not a
Chandra–Kozen–Stockmeyer simulation theorem by itself. The term `n` in the hypothesis pays for
copying the instance next to the moves on a work tape, since the input head is sequential, so
the statement only applies to time bounds `t n ≥ n` up to constants. -/
theorem mem_ATIME_of_alternation {L : α → ℕ} {V : α × List Bool → Bool} {t : ℕ → ℕ}
    {TL SL : α → ℕ} {TV SV : α × List Bool → ℕ} {C : ℕ}
    (hL : ComputableInO L enc encUnary TL SL)
    (hV : ComputableInO V (encPair enc encBits) encBool TV SV)
    (hA : ∀ a, a ∈ A ↔ Alternation true (List.replicate (L a) 1) fun z => V (a, z) = true)
    (hTL : ∀ a, (enc a).length + L a + TL a ≤ C * t (enc a).length + C)
    (hTV : ∀ a z, z.length = L a → TV (a, z) ≤ C * t (enc a).length + C) :
    A ∈ ATIME enc t := by
  have hg : ComputableInO (fun a => (L a, a)) enc (encPair encUnary enc)
      (fun a => TL a + (enc a).length) (fun a => SL a + (enc a).length) :=
    hL.prod ComputableInO.id'
  have hV' : ComputableInO (fun x : List Bool × α => V (x.2, x.1)) (encPair encBits enc) encBool
      (fun x => (encPair encBits enc x).length + (encPair encBits enc x).length + TV (x.2, x.1))
      (fun x => (encPair encBits enc x).length + (encPair encBits enc x).length +
        SV (x.2, x.1)) :=
    hV.comp' ((ComputableInO.snd encBits enc).prod (ComputableInO.fst encBits enc))
  obtain ⟨cg, k₁, S₁, _, Tg, hTg⟩ := Internal.NormalForm.bigO hg.computableInBigO
  obtain ⟨cv, k₂, S₂, _, Tv, hTv⟩ := Internal.NormalForm.bigO hV'.computableInBigO
  obtain ⟨k, State, hfin, atm, hatm⟩ :=
    decidableInTime_guessVerify (A := A) (L := L) (W := fun x => V (x.2, x.1))
      (tg := fun a => cg * (TL a + (enc a).length + 1))
      (tv := fun a => cv * (2 * (2 * L a + 1 + (enc a).length) + (C * t (enc a).length + C) + 1))
      (fun a => ⟨_, hTg a⟩) (fun a z hz => ⟨_, (hTv (z, a)).mono (Nat.mul_le_mul_left cv (by
        have hlen := length_encPair (enc₁ := encBits) (enc₂ := enc) (z, a)
        have hT := hTV a z hz
        simp only [encBits_apply] at hlen
        dsimp only
        omega)) le_rfl⟩) hA
  refine ⟨(cg + 5 * cv + 11) * C, (cg + 5 * cv + 11) * C + (cg + 5 * cv + 11), k, State, hfin,
    atm, hatm.mono fun a => ?_⟩
  have h₁ := hTL a
  have e₁ : cg * (TL a + (enc a).length + 1) ≤ cg * (C * t (enc a).length + C + 1) :=
    Nat.mul_le_mul_left cg (by omega)
  have e₂ : cv * (2 * (2 * L a + 1 + (enc a).length) + (C * t (enc a).length + C) + 1) ≤
      cv * (5 * (C * t (enc a).length + C + 1)) :=
    Nat.mul_le_mul_left cv (by omega)
  rw [show (frame (List.replicate (L a) true) ++ enc a).length =
    2 * L a + 1 + (enc a).length by simp]
  nlinarith [e₁, e₂, Nat.zero_le (C * t (enc a).length)]

end Cslib.Complexity
