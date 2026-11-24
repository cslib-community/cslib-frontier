/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation.SavitchEndpoints
public import CslibFrontier.Computability.Complexity.Classes.Constructible
import CslibFrontier.Computability.Complexity.Classes.Constructible.UnaryClock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Savitch's midpoint game in alternating time, from its leaf test

A play of Savitch's midpoint game on the views of a nondeterministic machine `ntm` ends with the
edge test of two endpoints, each the midpoint of the last level with a given half or, if there is
none, the code of the initial view or the accepting code
(`Cslib.Reachability.midpointGame_eq_reach_lastMidpoint`). This file names that last test,
`Turing.MultiTapeNTM.midpointLeaf`, on the width, the input and the two endpoints as options, and
assembles the rest of a verifier of the midpoint game within time `O((n + s n) ^ 2)`: the width
and the number of moves in unary
(`Cslib.Complexity.TimeConstructible.computableInO_unary_of_polyTime`) and both endpoints
(`Cslib.Reachability.computableInO_lastMidpoint`).

The result, `Cslib.Complexity.NSPACE_subset_ATIME_sq_of_midpointLeaf`, is a step toward
`NSPACE(S) ⊆ ⋃_{c > 0} ATIME(c * S ^ 2)` for `S(n) ≥ n` [Chandra, Kozen and Stockmeyer, Theorem
3.1][ChandraKozenStockmeyer1981], not that theorem: it assumes that the leaf test of every machine
runs within time quadratic in the length of its encoded input, which is proved neither here nor
elsewhere in the library. The leaf test decodes two views, and compares the second with the results
of the finitely many actions the machine permits on the first; it also writes the code of the
initial view when the left endpoint is missing.

The views record the input, so the codes have width linear in `n + s n`, and the bound is
`O((n + s n) ^ 2)` (Sipser's form) for every `s`; under the hypothesis `s n ≥ n` of Theorem 3.1 it
is `O(s n ^ 2)`. Unlike Theorem 3.1, `s` is assumed time-constructible, to write the number of moves
in unary.

## Main definitions

* `Turing.MultiTapeNTM.midpointLeaf`: the leaf test of the midpoint game on the views of a machine.

## Main results

* `Cslib.Complexity.NSPACE_subset_ATIME_sq_of_midpointLeaf`: if the leaf test of every machine runs
  in quadratic time, then `NSPACE s ⊆ ATIME ((n + s n) ^ 2)` for a time-constructible `s`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State]

/-- **The leaf test of Savitch's midpoint game** on the views of `ntm`, at width `w` on `input`,
given the final endpoints `u` and `v` of a play as options: the edge test
`Cslib.Reachability.reach ntm.codeEdge (2 * w + 2) 0` of the left endpoint, by default the code of
the initial view on `input`, and of the right endpoint, by default the accepting code. -/
noncomputable def midpointLeaf (ntm : MultiTapeNTM k Bool State) (w : ℕ) (input : List Bool)
    (u v : Option (List Bool)) : Bool :=
  Cslib.Reachability.reach ntm.codeEdge (2 * w + 2) 0 (u.getD (viewCode w (ntm.initView input)))
    (v.getD (acceptCode w))

end Turing.MultiTapeNTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Reachability

variable {α : Type} {enc : α ↪ List Bool}

/-- A midpoint chosen in the midpoint game on words of width `w`, as an encoded option, has at most
`w + 1` bits. -/
private theorem length_encOption_lastMidpoint_le (w i : ℕ) (z : List Bool) (d : Bool) :
    (encOption encBits (lastMidpoint w i z d)).length ≤ w + 1 := by
  induction i generalizing z with
  | zero => simp [lastMidpoint]
  | succ i ih =>
    have hi := ih (z.drop (2 * w + 2))
    simp only [lastMidpoint]
    rcases h : lastMidpoint w i (z.drop (2 * w + 2)) d with _ | m
    · split_ifs <;> simp [midpointMoves]
    · rw [h] at hi
      simpa using hi

/-- For a time-constructible `s` and a constant `K`, the number of moves of the midpoint game on
codes of `2 * w + 2` bits, `w = K * (n + s n + 1)`, as in `exists_midpointGame_of_mem_NSPACE`, is
written in unary within time and space `O((n + s n + 1) ^ 2)`. -/
private theorem computableInO_midpointMoveCount {s : ℕ → ℕ} (hs : TimeConstructible s) (K : ℕ) :
    ComputableInO (fun a : α =>
      2 * ((2 * (K * ((enc a).length + s (enc a).length + 1)) + 2 + 1) *
        (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2))) enc encUnary
      (fun a => ((enc a).length + s (enc a).length + 1) ^ 2)
      fun a => ((enc a).length + s (enc a).length + 1) ^ 2 := by
  have hF : ComputableInPolyTime (fun p : ℕ × ℕ =>
      2 * ((2 * (K * (p.1 + p.2 + 1)) + 2 + 1) * (2 * (K * (p.1 + p.2 + 1)) + 2)))
      (encPair encNat encNat) encNat := by
    fun_prop
  have h := (hs.computableInO_unary_of_polyTime hF).comp
    (ComputableInO.of_eq (f := fun a : α => enc a) (encMid := encBits) fun _ => rfl)
  have hbound (a : α) : (enc a).length + ((enc a).length + s (enc a).length +
      2 * ((2 * (K * ((enc a).length + s (enc a).length + 1)) + 2 + 1) *
        (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2))) ≤
      (8 * K ^ 2 + 20 * K + 14) * (((enc a).length + s (enc a).length + 1) ^ 2 + 1) := by
    set m := (enc a).length + s (enc a).length + 1
    have hm : (enc a).length + ((enc a).length + s (enc a).length) ≤ 2 * m := by omega
    have hm2 : m ≤ m ^ 2 := by nlinarith
    have e : 2 * ((2 * (K * m) + 2 + 1) * (2 * (K * m) + 2)) =
        8 * K ^ 2 * m ^ 2 + 20 * (K * m) + 12 := by
      ring
    have hKm : K * m ≤ K * m ^ 2 := Nat.mul_le_mul_left K hm2
    have e2 : (8 * K ^ 2 + 20 * K + 14) * (m ^ 2 + 1) =
        8 * K ^ 2 * m ^ 2 + 20 * (K * m ^ 2) + 14 * m ^ 2 + (8 * K ^ 2 + 20 * K + 14) := by
      ring
    omega
  refine h.mono (8 * K ^ 2 + 20 * K + 14) (fun a => ?_) fun a => ?_ <;>
    simpa only [Function.comp_apply, encBits_apply] using hbound a

/-- This is not `NSPACE(S) ⊆ ⋃_{c > 0} ATIME(c * S ^ 2)` [Chandra, Kozen and Stockmeyer, Theorem
3.1][ChandraKozenStockmeyer1981] but a step toward it, **the reduction of
`NSPACE s ⊆ ATIME ((n + s n) ^ 2)` to the leaf test**: the hypothesis `hleaf`, that the leaf test
`Turing.MultiTapeNTM.midpointLeaf` of every machine runs within time quadratic in the length of its
encoded input, is a step of that simulation that is proved neither here nor elsewhere in the
library.

Given it, every problem in `NSPACE s`, for a time-constructible `s`, is in
`ATIME ((n + s n) ^ 2)`: the alternating machine plays Savitch's midpoint game on the views of a
machine deciding it (`Cslib.Complexity.exists_midpointGame_of_mem_NSPACE`), with the number of moves
and the width written in unary within time `O((n + s n + 1) ^ 2)`, both endpoints of the play
extracted within time linear in the number of moves
(`Cslib.Reachability.computableInO_lastMidpoint`),
and the leaf test on codes of width linear in `n + s n`
(`Cslib.Complexity.mem_ATIME_of_alternation`). The bound is Sipser's form `O((n + s n) ^ 2)`, which
is `O(s n ^ 2)` under the hypothesis `s n ≥ n` of Theorem 3.1; unlike Theorem 3.1, `s` is assumed
time-constructible. -/
theorem NSPACE_subset_ATIME_sq_of_midpointLeaf {s : ℕ → ℕ} (hs : TimeConstructible s)
    (hleaf : ∀ {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State),
      ComputableInO
        (fun ((w, input, u, v) : ℕ × List Bool × Option (List Bool) × Option (List Bool)) =>
          ntm.midpointLeaf w input u v)
        (encPair encUnary (encPair encBits (encPair (encOption encBits) (encOption encBits))))
        encBool
        (fun p => (encPair encUnary (encPair encBits (encPair (encOption encBits)
          (encOption encBits))) p).length ^ 2)
        fun p => (encPair encUnary (encPair encBits (encPair (encOption encBits)
          (encOption encBits))) p).length ^ 2) :
    NSPACE enc s ⊆ ATIME enc fun n => (n + s n) ^ 2 := by
  intro A h
  obtain ⟨k, State, hfin, ntm, K, hA⟩ := exists_midpointGame_of_mem_NSPACE h
  have hF₁ : ComputableInPolyTime (fun p : ℕ × ℕ => K * (p.1 + p.2 + 1))
      (encPair encNat encNat) encNat := by
    fun_prop
  have hF₂ : ComputableInPolyTime (fun p : ℕ × ℕ => 2 * (K * (p.1 + p.2 + 1)) + 2)
      (encPair encNat encNat) encNat := by
    fun_prop
  have henc : ComputableInO (fun x : α × List Bool => enc x.1) (encPair enc encBits) encBits
      (fun x => (encPair enc encBits x).length) (fun x => (encPair enc encBits x).length) :=
    (ComputableInO.of_eq (f := fun a : α => enc a) (encMid := encBits) fun _ => rfl).comp_linear
      (ComputableInO.fst enc encBits)
  have hW₁ := (hs.computableInO_unary_of_polyTime hF₁).comp henc
  have hW₂ := (hs.computableInO_unary_of_polyTime hF₂).comp henc
  have hmid (d : Bool) := (computableInO_lastMidpoint d).comp
    (hW₂.prod (hW₂.prod (ComputableInO.snd enc encBits)))
  have hV := (hleaf ntm).comp (hW₁.prod (henc.prod ((hmid true).prod (hmid false))))
  have hV' := hV.mono (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200)
    (T' := fun x => ((enc x.1).length + s (enc x.1).length + 1) ^ 2 + x.2.length)
    (S' := fun x => ((enc x.1).length + s (enc x.1).length + 1) ^ 2 + x.2.length)
    (fun x => ?_) (fun x => ?_)
  rotate_left
  iterate 2
    obtain ⟨a, z⟩ := x
    have h₁ := length_encOption_lastMidpoint_le
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2)
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2) z true
    have h₂ := length_encOption_lastMidpoint_le
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2)
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2) z false
    simp only [Function.comp_apply, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    generalize (encOption encBits (lastMidpoint
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2)
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2) z true)).length = e₁ at h₁ ⊢
    generalize (encOption encBits (lastMidpoint
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2)
      (2 * (K * ((enc a).length + s (enc a).length + 1)) + 2) z false)).length = e₂ at h₂ ⊢
    generalize (enc a).length = n at h₁ h₂ ⊢
    generalize s n = t at h₁ h₂ ⊢
    generalize z.length = l
    generalize hm : n + t + 1 = m at h₁ h₂ ⊢
    generalize hW : K * m = W at h₁ h₂ ⊢
    have e₀ : (2 * (2 * W + 2) + 2) * (2 * W + 2) = 8 * (W * W) + 20 * W + 12 := by ring
    have hWW : W * W = K ^ 2 * m ^ 2 := by rw [← hW]; ring
    have hX : 2 * W + 1 + (2 * n + 1 + (2 * e₁ + 1 + e₂)) ≤ (8 * K + 15) * m := by
      have : (8 * K + 15) * m = 8 * W + 15 * m := by rw [← hW]; ring
      omega
    have hX2 := Nat.pow_le_pow_left hX 2
    have e₃ : ((8 * K + 15) * m) ^ 2 = 64 * (K ^ 2 * m ^ 2) + 240 * (K * m ^ 2) + 225 * m ^ 2 := by
      ring
    have hm2 : m ≤ m ^ 2 := by nlinarith
    have hWm : W ≤ K * m ^ 2 := by rw [← hW]; exact Nat.mul_le_mul_left K hm2
    have e₄ : (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200) * (m ^ 2 + l + 1) =
        168 * (K ^ 2 * m ^ 2) + 580 * (K * m ^ 2) + 650 * m ^ 2 +
          (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200) * (l + 1) := by
      ring
    have hc : 200 * (l + 1) ≤ (2 * (8 * K + 15) ^ 2 + 40 * K ^ 2 + 100 * K + 200) * (l + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  refine mem_ATIME_of_alternation
    (C := 2 * (8 * K + 15) ^ 2 + 64 * K ^ 2 + 140 * K + 260)
    (computableInO_midpointMoveCount hs K) hV' (fun a => (hA a _ le_rfl).trans ?_) (fun a => ?_)
    fun a z hz => ?_
  · refine Iff.of_eq (congrArg (Alternation true _) (funext fun z => ?_))
    rw [midpointGame_eq_reach_lastMidpoint]
    rfl
  all_goals
    simp only at *
    set p := (enc a).length + s (enc a).length
    have hn : (enc a).length ≤ p := Nat.le_add_right _ _
    have hp : p ≤ p ^ 2 + 1 := by nlinarith
    have hKp : K * p ≤ K * (p ^ 2 + 1) := Nat.mul_le_mul_left K hp
    have hK2p : K ^ 2 * p ≤ K ^ 2 * (p ^ 2 + 1) := Nat.mul_le_mul_left _ hp
    have e : 2 * ((2 * (K * (p + 1)) + 2 + 1) * (2 * (K * (p + 1)) + 2)) + (p + 1) ^ 2 =
        (8 * K ^ 2 + 1) * p ^ 2 + (16 * K ^ 2 + 20 * K + 2) * p + (8 * K ^ 2 + 20 * K + 13) := by
      ring
    nlinarith [Nat.zero_le ((8 * K + 15) ^ 2 * p ^ 2), Nat.zero_le (K * p ^ 2),
      Nat.zero_le (K ^ 2 * p ^ 2)]

end Cslib.Complexity
