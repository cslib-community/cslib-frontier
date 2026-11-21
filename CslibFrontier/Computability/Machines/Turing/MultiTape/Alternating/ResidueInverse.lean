/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueChallenge
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalLayout
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime

/-!
# A native alternating verifier for residue-inverse queries

The prepared short tape holds the contraction scale and output query followed by the
existential and universal flags. A deterministic word computation turns the completed play
into either a local verdict or one bit request. The read-only host input is preserved.
-/

public section
namespace Turing.MultiTapeATM.ResidueInverse

open MultiTapeTM Cslib Cslib.Circuits.Frontier.FastContraction
open Cslib.Circuits.Frontier.FastContraction.ResidueInverse
open RootPackingBalance.TerminalLayout QuantifiedWord

/-- A local verdict or an indexed operand-bit claim. -/
abbrev encResult := encSum encBool (encPair encNat encBool)

/-- The public fields precede every choice bit on the physical tape. -/
@[expose] def header (m i : ℕ) (claim : Bool) := encChallenge ⟨m, i, claim, []⟩

private theorem encoded (m i : ℕ) (claim : Bool) (xs : List Bool) :
    encChallenge ⟨m, i, claim, xs⟩ = header m i claim ++ xs := by
  simp [header, encChallenge_apply, encChallengeFields, encPair_apply, encBits_apply,
    List.append_assoc]

/-- The complete native word has polynomial size in the binary scale and requested index. -/
theorem length_prepared_le (m i : ℕ) (claim : Bool) :
    (header m i claim ++ flags (modulus m).length).length ≤
      4 * m.size + 4 * i.size + 4 * (4 * m.size + 2) ^ 2 + 12 := by
  have hg := degree_le_size m
  have hl : Nat.clog 2 ((modulus m).length + 1) ≤ (modulus m).length + 1 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  simp [header, encChallenge_apply, encChallengeFields, encPair_apply, encBits_apply,
    encBool_apply, encNat_apply, Nat.size_eq_bits_len, flags] at *
  omega

/-- One fixed machine verifies a residue-inverse bit with a single charged call on each path.
A leaf receives the actual routed verdict or operand request and the binary contraction scale.
The clock covers all choices, routing, rewinding, work-word transfer, and the continuation. -/
theorem exists_check {K : ℕ} {S : Type} [Finite S] (j l : Fin K) (hne : j ≠ l)
    (child : MultiTapeATM K Bool S) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (c e : ℕ),
      ∀ (input : List Bool) (m i : ℕ) (claim : Bool) (word : List Bool)
        (_hw : word.length = (modulus m).length) (time : ℕ),
        let pre := header m i claim
        let players := flags (modulus m).length
        let init := WordGameLeaf.config src (some atm.toPTM.initial)
          (pre ++ players) pre.length (blank U input)
        (∀ (s : List Bool) (_ : s.length = players.length),
          let req := route ⟨m, i, claim, s⟩
          let cfg := (TwoWordInput.ready j l input (encResult req) (encNat m)).withState
            (some child.toPTM.initial)
          child.HaltsWithin time cfg ∧ (child.AcceptsWithin time cfg ↔ answer word req)) →
        let n := (pre ++ players).length
        let clock := n + c * ((n + 1) ^ e + 1) + 8 + time + 2 * players.length + 1
        atm.HaltsWithin clock init ∧
          (atm.AcceptsWithin clock init ↔ run ⟨m, i, word⟩ = claim) := by
  classical
  obtain ⟨tr, sr, htr, hsr, hr⟩ := computableInPolyTime_route.exists_computableInO
  obtain ⟨tm, sm, htm, hsm, hm⟩ :=
    encChallenge_scale_deg.computableInPolyTime.exists_computableInO
  obtain ⟨A, e, he⟩ := ((htr.add hsr).add (htm.add hsm)).exists_le
  let T (a : Challenge) := ((encChallenge a).length + 1) ^ e
  have hb (a : Challenge) : tr a + sr a + (tm a + sm a) ≤ A * (T a + 1) :=
    (he a).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have hr' : ComputableInO route encChallenge encResult T T := hr.mono A (fun a => by
    have := hb a; omega) (fun a => by have := hb a; omega)
  have hm' : ComputableInO Challenge.scale encChallenge encNat T T := hm.mono A (fun a => by
    have := hb a; omega) (fun a => by have := hb a; omega)
  obtain ⟨U, src, Q, fin, leaf, c, hleaf⟩ := exists_load hr' hm' j l hne child
  let := Fintype.ofFinite Q
  refine ⟨U, src, State Q, inferInstance, machine leaf src, c, e, ?_⟩
  intro input m i claim word hw time pre players init childSpec n clock
  let v (w : List Bool) := answer word (route ⟨m, i, claim, w.drop pre.length⟩)
  have h := spec leaf src (n + c * ((n + 1) ^ e + 1) + 8 + time) (blank U input) v pre players (by
    intro s hs
    let a : Challenge := ⟨m, i, claim, s⟩
    have henc : encChallenge a = pre ++ s := encoded _ _ _ _
    have hslen : (encChallenge a).length = n := by simp only [n, henc, List.length_append, hs]
    have hc := childSpec s hs
    obtain ⟨hh, ha⟩ := hleaf input a time hc.1
    dsimp only
    have hval : v (pre ++ s) = answer word (route a) := by simp [v, a]
    rw [hval, ← henc]
    simpa only [T, hslen] using And.intro hh (ha.trans hc.2))
  have hp := plays_append_prefix v pre [] players
  refine ⟨?_, ?_⟩
  · simpa only [clock, init, machine_initial] using h.1
  · have hp' : plays v pre players ↔
        plays (fun s => answer word (route ⟨m, i, claim, s⟩)) [] players := by
      simpa only [List.append_nil, v, List.drop_left] using hp
    have heq := hp'.trans (plays_flags m i claim word hw)
    simpa only [clock, init, machine_initial] using h.2.trans heq

end Turing.MultiTapeATM.ResidueInverse
