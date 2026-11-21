/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafATM
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WorkTapeFamily
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterRootLeafRequest

/-!
# The guarded root call from the outer carry-save tapes

Both bit claims use one finite state type and scratch layout. The actual path, carry and counters
are serialized before the dispatcher either returns a constant or runs the root child. Its clock
charges linear preparation on the long fields, a fixed power of the metadata, and one child run.
-/

public section

namespace Turing.MultiTapeATM.OuterRootLeafRunner

open MultiTapeTM OuterRootLeafRequest
open RootBalanceRequest (encPublic)

private theorem setup_le (x : Input) (n a l d D B : ℕ)
    (hn : n ≤ l * (longSize x + shortSize x ^ d + 1)) (hd : d ≤ D) (hb : a + 2 * l + 16 ≤ B) :
    x.path.length + 3 + (2 * (encInput x).length + 5) +
        (a * (longSize x + shortSize x ^ d + 1) + (2 * n + 16)) ≤
      (B + 1) * (x.path.length + 2 * (encInput x).length + 9 + longSize x +
        shortSize x ^ D + 1) := by
  let m := longSize x + shortSize x ^ d + 1
  let N := x.path.length + 2 * (encInput x).length + 9 + longSize x + shortSize x ^ D + 1
  have hp := Nat.pow_le_pow_right (show 0 < shortSize x by simp [shortSize]) hd
  have hm : m ≤ N := by dsimp [m, N]; omega
  have hlocal : a * m + (2 * n + 16) ≤ (a + 2 * l + 16) * m := by
    change n ≤ l * m at hn
    have hm₁ : 1 ≤ m := Nat.succ_pos _
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    omega
  have hu := hlocal.trans (Nat.mul_le_mul hb hm)
  change _ ≤ (B + 1) * N
  rw [Nat.add_mul, Nat.one_mul]
  change _ + (a * m + _) ≤ _
  dsimp only [N] at hu ⊢
  omega

/-- A single finite family accepts exactly the guarded root verdict on the real outer leaf
storage. A disabled request carries no premise about the root child's running time. -/
theorem exists_runner {K : ℕ} {S : Type} [Finite S] (k : ℕ) (src : Fin K)
    (child : MultiTapeATM K Bool S) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q) (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q)
      (C d : ℕ), ∀ (host : List Bool) (x : Input) (height unary : List Bool) (frontier : ℤ)
        (status claim : Bool) (t : ℕ),
        let target := SharedWordFork.start src child host (encPublic (publicRequest k claim x)) 0
        let atm := leaf x.carry claim
        let start := (CarrySaveLeaf.initial a host (encPublic x.template) x.count x.width
          height x.bit x.path unary frontier status).withState (some atm.toPTM.initial)
        let time := C * (x.path.length + 2 * (encInput x).length + 9 + longSize x +
          shortSize x ^ d + 1) + t
        (active (data k x) = true → child.HaltsWithin t target) →
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            if active (data k x) then child.AcceptsWithin t target else (!claim) = true) := by
  classical
  choose d hd using exists_word_inO k
  choose l hl using fun b => (hd b).length_le_time
  let cost (b : Bool) (x : Input) := longSize x + shortSize x ^ d b
  have guarded (b : Bool) := GuardedWord.exists_guarded_runner src child
    (fun x => active (data k x)) (fun _ => !b) (fun x => encPublic (publicRequest k b x))
    (cost b) (hd b)
  choose u R hR runner A hr using guarded
  let : ∀ b, Finite (R b) := hR
  obtain ⟨a, Q, hQ, family, hf⟩ := WorkTapeFamily.exists_family u R runner
  let := hQ
  let D := max (d false) (d true)
  let coeff (b : Bool) := A b + 2 * l b + 16
  let B := max (coeff false) (coeff true)
  refine ⟨a, _, inferInstance, fun carry b => CarrySaveLeafATM.machine (family b) carry,
    B + 1, D, ?_⟩
  intro host x height unary frontier status b t target atm start time hchild
  let w := encPublic (publicRequest k b x)
  let n := A b * (cost b x + 1) + (2 * w.length + 16) + t
  obtain ⟨hh, ha⟩ := hr b host x t hchild
  have hs := hf b host (encInput x) n
  have hq := CarrySaveLeafATM.spec (family b) host (encPublic x.template) x.count x.width
    height x.bit x.path unary frontier status x.carry n (hs.1.mpr hh)
  obtain ⟨hhalt, hacc⟩ := hq
  have hlen := hl b x
  simp only [encBits_apply, word, List.length_append] at hlen
  have hn : w.length ≤ l b * (longSize x + shortSize x ^ d b + 1) := by
    change 3 + w.length ≤ _ at hlen
    omega
  have hD : d b ≤ D := by cases b <;> first | apply Nat.le_max_left | apply Nat.le_max_right
  have hB : coeff b ≤ B := by cases b <;> first | apply Nat.le_max_left | apply Nat.le_max_right
  have hb := setup_le x w.length (A b) (l b) (d b) D B hn hD hB
  have clock : x.path.length + 3 + (2 * (encInput x).length + 5) + n ≤ time := by
    dsimp only [time, n, cost]
    omega
  refine ⟨hhalt.mono clock, ⟨?_, ?_⟩⟩
  · intro acc
    exact ha.mp (hs.2.mp (hacc.mp (acc.of_halted_stepCoins hhalt)))
  · intro h
    exact (hacc.mpr (hs.2.mpr (ha.mpr h))).mono clock

end Turing.MultiTapeATM.OuterRootLeafRunner
