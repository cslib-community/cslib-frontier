/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.PrimeTable
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Query
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import CslibFrontier.Computability.GenericRAM.Signed.Fits
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.PreservesMask
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Native least-prime collision searches

The search scans the prime bitmap in increasing order. A candidate runs the complete native
three-set collision query. Its first acceptance is retained while the remaining candidates
are visited without further bitmap reads. If no candidate is accepted, the answer is one, matching
`ChanHe.minOrOne`.

## Main definitions

* `Search.program`: a fixed native prime search using charged collision queries.

## Main results

* `Search.exec`: exact minimum/default selection with native fits, frames and charged cost.
* `Search.preserves_caller`: the upper five caller registers are preserved.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Search

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum.ChanHe

/-- Largest candidate prime. -/
abbrev limit : Fin 64 := 40
/-- Prime bitmap base. -/
abbrev primes : Fin 64 := 41
/-- Factor multiplied by the candidate prime. -/
abbrev factor : Fin 64 := 43
/-- Current candidate. -/
abbrev cursor : Fin 64 := 47
/-- One past the largest candidate. -/
abbrev stop : Fin 64 := 48
/-- Selected prime, or the default one. -/
abbrev answer : Fin 64 := 49
/-- Whether an acceptance has already occurred. -/
abbrev found : Fin 64 := 50
/-- Constant one. -/
abbrev one : Fin 64 := 51
/-- Constant zero. -/
abbrev zero : Fin 64 := 52
/-- Constant two, for positive signed encoding. -/
abbrev two : Fin 64 := 53
/-- Unencoded candidate modulus. -/
abbrev rawModulus : Fin 64 := 54
/-- Bitmap address scratch. -/
abbrev addr : Fin 64 := 55
/-- Loaded primality bit. -/
abbrev bit : Fin 64 := 56
/-- Encoded candidate modulus. -/
abbrev modulus : Fin 64 := CountCall.modulus
/-- Acceptance flag returned by the collision query. -/
abbrev good : Fin 64 := CollisionTest.good

/-- Compute and encode the candidate modulus, then run the full collision query. -/
def query : Code .standard 64 :=
  .seq (ram[ rawModulus ← factor * cursor; modulus ← rawModulus * two ]) Query.program

/-- Record an accepted candidate, or retain the previous answer. -/
def pick : Code .standard 64 := ram[
  if good = one then [ answer ← cursor; found ← one ] else [ answer ← answer ] ]

/-- A charged instruction that retains the answer. -/
def nop : Code .standard 64 := ram[ answer ← answer ]

/-- Load a bitmap entry. -/
def load : Code .standard 64 := ram[ addr ← primes + cursor; bit ← *addr ]

/-- Before the first acceptance, run the query exactly on prime candidates. -/
def inner : Code .standard 64 :=
  .branch (.eq found zero)
    (.seq load (.branch (.eq bit one) (.seq query pick) nop)) nop

/-- One candidate and its charged cursor increment. -/
def body : Code .standard 64 := .seq inner (ram[ cursor ← cursor + one ])

/-- Initialize the selector and scan the entire bounded candidate range. -/
def program : Code .standard 64 :=
  .seq (ram[ one ← #1; zero ← #0; two ← #2; cursor ← #0;
    stop ← limit + one; answer ← one; found ← zero ]) (.loop (.lt cursor stop) body)

/-- The five upper caller registers survive the complete native search. -/
theorem preserves_caller (i : Fin 64) (hi : 59 ≤ i.val) : program.Preserves i :=
  Code.preserves_of_writeEnd (by decide) hi

private abbrev Fixed (i : Fin 64) : Prop := (28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 46)

private abbrev Control (i : Fin 64) : Prop :=
  (28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 53)

private def Stable (x y : Data 64) : Prop :=
  (∀ i, Fixed i → y.regs i = x.regs i) ∧
    ∀ a < x.regs CountCall.scratch, y.mem a = x.mem a

private def Status (A : ℕ → Prop) (k : ℕ) (y : Data 64) : Prop :=
  (y.regs found = 0 ∧ y.regs answer = 1 ∧ ∀ q < k, ¬(q.Prime ∧ A q)) ∨
  (y.regs found = 1 ∧ y.regs answer < k ∧ (y.regs answer).Prime ∧ A (y.regs answer) ∧
    ∀ q < y.regs answer, ¬(q.Prime ∧ A q))

private theorem status_min {A : ℕ → Prop} [DecidablePred A] {m : ℕ} {y : Data 64}
    (h : Status A (m + 1) y) :
    y.regs answer = minOrOne {q ∈ Nat.primesLE m | A q} := by
  let S := {q ∈ Nat.primesLE m | A q}
  rcases h with ⟨hf, ha, hn⟩ | ⟨hf, hk, hp, hA, hn⟩
  · have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun q hq => by
      simp only [S, Finset.mem_filter, Nat.primesLE_eq_filter_range, Finset.mem_range] at hq
      exact hn q hq.1.1 ⟨hq.1.2, hq.2⟩
    rw [ha]
    change 1 = minOrOne S
    simp [hs, minOrOne]
  · have hmem : y.regs answer ∈ S := by
      simp only [S, Finset.mem_filter, Nat.primesLE_eq_filter_range, Finset.mem_range]
      exact ⟨⟨hk, hp⟩, hA⟩
    have hs : S.Nonempty := ⟨_, hmem⟩
    have hmin : S.min' hs = y.regs answer :=
      le_antisymm (Finset.min'_le _ _ hmem) (Finset.le_min' _ _ _ fun q hq =>
        not_lt.mp fun hlt => by
          simp only [S, Finset.mem_filter, Nat.primesLE_eq_filter_range, Finset.mem_range] at hq
          exact hn q hlt ⟨hq.1.2, hq.2⟩)
    change y.regs answer = minOrOne S
    simp only [minOrOne, dite_eq_left hs, hmin]

private theorem exec_driver {w T : ℕ} (x : Data 64) (A : ℕ → Prop) [DecidablePred A]
    (hfit : Fits w (x.regs limit + 3))
    (haddr : Fits w (x.regs primes + (x.regs limit + 1)))
    (hbefore : x.regs primes + (x.regs limit + 1) ≤ x.regs CountCall.scratch)
    (hbitmap : ∀ q ≤ x.regs limit, x.mem (x.regs primes + q) = if q.Prime then 1 else 0)
    (hquery : ∀ y, Stable x y → y.regs cursor ≤ x.regs limit →
      y.regs one = 1 → y.regs zero = 0 → y.regs two = 2 → (y.regs cursor).Prime →
      ∃ z, ExecWithin w query y z T ∧ Stable x z ∧
        z.regs good = (if A (y.regs cursor) then 1 else 0) ∧
        ∀ i, Control i → z.regs i = y.regs i) :
    ∃ y, ExecWithin w program x y ((x.regs limit + 1) * (T + 15) + 9) ∧
      Stable x y ∧ y.regs answer = minOrOne {q ∈ Nat.primesLE (x.regs limit) | A q} := by
  let m := x.regs limit
  let P (j : ℕ) (y : Data 64) : Prop := Stable x y ∧ y.regs stop = m + 1 ∧
    y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs two = 2 ∧ Status A j y
  have hbody (y : Data 64) (hy : P (y.regs cursor) y) (hlt : y.regs cursor < m + 1) :
      ∃ z, ExecWithin w body y z (T + 13) ∧ P (y.regs cursor + 1) z ∧
        z.regs cursor = y.regs cursor + 1 := by
    obtain ⟨hstable, hstop, ho, hz, ht, hstatus⟩ := hy
    have hinc : Fits w (y.regs cursor + 1) := hfit.of_le (by change _ ≤ m + 3; omega)
    unfold body inner load pick nop
    rcases hstatus with ⟨hf, ha, hn⟩ | hsome
    · have hpr : y.regs primes = x.regs primes := hstable.1 _ (by decide)
      have had : Fits w (x.regs primes + y.regs cursor) := haddr.of_le (by omega)
      have hread : y.mem (x.regs primes + y.regs cursor) =
          if (y.regs cursor).Prime then 1 else 0 := by
        rw [hstable.2 (x.regs primes + y.regs cursor) (by omega)]
        exact hbitmap _ (by change y.regs cursor ≤ m; omega)
      by_cases hp : (y.regs cursor).Prime
      · wram_exec [hf, hz, ho, hpr, had, hread, hp]
        refine WP.name fun u hu => ?_
        have hucur : u.regs cursor = y.regs cursor := by subst hu; wram_simp
        have hus : Stable x u :=
          ⟨fun i hF => (by
              subst hu; dsimp only [Fixed] at hF
              update_simp [addr, bit] : u.regs i = y.regs i).trans (hstable.1 i hF),
            by subst hu; exact hstable.2⟩
        wram_call (hquery u hus (by rw [hucur]; change _ ≤ m; omega)
            (by subst hu; regs_frame) (by subst hu; regs_frame) (by subst hu; regs_frame)
            (by rwa [hucur]))
          with v ⟨hvs, hvg, hvr⟩
        have hvy (i : Fin 64) (hc : Control i) : v.regs i = y.regs i := by
          refine (hvr i hc).trans ?_
          subst hu
          dsimp only [Control] at hc
          update_simp [addr, bit]
        have hvcur : v.regs cursor = y.regs cursor := hvy cursor (by decide)
        have hvo : v.regs one = 1 := (hvy one (by decide)).trans ho
        have hvf : v.regs found = 0 := (hvy found (by decide)).trans hf
        have hva : v.regs answer = 1 := (hvy answer (by decide)).trans ha
        have hvsp : v.regs stop = m + 1 := (hvy stop (by decide)).trans hstop
        have hvz : v.regs zero = 0 := (hvy zero (by decide)).trans hz
        have hvt : v.regs two = 2 := (hvy two (by decide)).trans ht
        rw [hucur] at hvg
        by_cases hA : A (y.regs cursor)
        · wram_exec [hvg, hvo, hvcur, hA, hinc]
          refine ⟨⟨⟨fun i hF => ?_, hvs.2⟩,
            by regs_frame, by regs_frame, by regs_frame, by regs_frame,
            Or.inr ⟨by wram_simp, ?_, ?_, ?_, ?_⟩⟩, by wram_simp⟩
          · dsimp only [Fixed] at hF
            exact (by update_simp [answer, found, cursor] : _ = v.regs i).trans (hvs.1 i hF)
          · wram_simp; omega
          · wram_simp; exact hp
          · wram_simp; exact hA
          · wram_simp; exact hn
        · wram_exec [hvg, hvo, hvcur, hA, hinc]
          refine ⟨⟨⟨fun i hF => ?_, hvs.2⟩,
            by regs_frame, by regs_frame, by regs_frame, by regs_frame,
            Or.inl ⟨by wram_simp [hvf], by wram_simp [hva], fun q hq hqA => ?_⟩⟩,
            by wram_simp⟩
          · dsimp only [Fixed] at hF
            exact (by update_simp [answer, cursor] : _ = v.regs i).trans (hvs.1 i hF)
          · by_cases hqk : q < y.regs cursor
            · exact hn q hqk hqA
            · obtain rfl : q = y.regs cursor := by omega
              exact hA hqA.2
      · wram_exec [hf, hz, ho, hpr, had, hread, hp, hinc]
        refine ⟨⟨⟨fun i hF => ?_, hstable.2⟩,
          by regs_frame, by regs_frame, by regs_frame, by regs_frame,
          Or.inl ⟨by regs_frame, by regs_frame, fun q hq hqA => ?_⟩⟩, by wram_simp⟩
        · dsimp only [Fixed] at hF
          exact (by update_simp [addr, bit, answer, cursor] : _ = y.regs i).trans (hstable.1 i hF)
        · by_cases hqk : q < y.regs cursor
          · exact hn q hqk hqA
          · obtain rfl : q = y.regs cursor := by omega
            exact hp hqA.1
    · have hne : y.regs found ≠ y.regs zero := by rw [hsome.1, hz]; decide
      wram_exec [hne, ho, hinc]
      refine ⟨⟨⟨fun i hF => ?_, hstable.2⟩,
        by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        Or.inr ⟨by wram_simp [hsome.1], ?_, ?_, ?_, ?_⟩⟩, by wram_simp⟩
      · dsimp only [Fixed] at hF
        exact (by update_simp [answer, cursor] : _ = y.regs i).trans (hstable.1 i hF)
      · wram_simp; exact lt_trans hsome.2.1 (Nat.lt_succ_self _)
      · wram_simp; exact hsome.2.2.1
      · wram_simp; exact hsome.2.2.2.1
      · wram_simp; exact hsome.2.2.2.2
  have hm1 : Fits w (m + 1) := hfit.of_le (by change m + 1 ≤ m + 3; omega)
  unfold program
  wram_exec [hm1]
  refine WP.name fun x₀ hx₀ => ?_
  have hi : P (x₀.regs cursor) x₀ := by
    subst hx₀
    refine ⟨⟨fun i hF => by
        dsimp only [Fixed] at hF
        update_simp [one, zero, two, cursor, stop, answer, found],
      fun _ _ => rfl⟩,
      by wram_simp [m], by wram_simp, by wram_simp, by wram_simp,
      Or.inl ⟨by wram_simp, by wram_simp, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩⟩
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.2.1) hbody
      (by subst hx₀; wram_simp [m]) hi)
    with y ⟨⟨hs, _, _, _, _, hstat⟩, _⟩
  refine ⟨?_, hs, status_min hstat⟩
  have hcur₀ : x₀.regs cursor = 0 := by subst hx₀; wram_simp
  dsimp only [m] at *
  have hmul : (x.regs limit + 1 - x₀.regs cursor) * (T + 13 + 2) =
      (x.regs limit + 1) * (T + 15) := by
    rw [hcur₀, Nat.sub_zero, show T + 13 + 2 = T + 15 by omega]
  omega

/-- The least prime whose three actual collision counts satisfy the supplied thresholds.
Every candidate query is executed by `Query.program`; the hypotheses only constrain native
input values, layout and word fits. All instructions, including the scan after acceptance,
are charged. The final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hfactor : 0 < x.regs factor)
    (hmod : GenericRAM.Signed.Fits w ((x.regs factor * x.regs limit : ℕ) : ℤ))
    (hfit : Fits (w + 2) (x.regs limit + 3))
    (haddr : Fits (w + 2) (x.regs primes + (x.regs limit + 1)))
    (hbefore : x.regs primes + (x.regs limit + 1) ≤ x.regs CountCall.scratch)
    (hbitmap : ∀ q ≤ x.regs limit, x.mem (x.regs primes + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hs : ∀ j, Fits (w + 2) (x.regs (CountCall.source j) + x.regs (CountCall.length j)))
    (hk : ∀ j, Fits (w + 2) (x.regs CountCall.scratch + x.regs (CountCall.length j)))
    (hd : Fits (w + 2) (x.regs CountCall.histogram + x.regs factor * x.regs limit))
    (ht : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) +
      x.regs (CountCall.length j) + 1))
    (hproduct : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) *
      x.regs CollisionTest.card))
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y
        ((x.regs limit + 1) * (34 * (x.regs (CountCall.length 0) +
          x.regs (CountCall.length 1) + x.regs (CountCall.length 2)) +
          15 * (x.regs factor * x.regs limit) + 102) + 9) ∧
      (∀ i, ((28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 46)) →
        y.regs i = x.regs i) ∧
      (∀ a < x.regs CountCall.scratch, y.mem a = x.mem a) ∧
      y.regs answer = minOrOne {q ∈ Nat.primesLE (x.regs limit) | ∀ j : Fin 3,
        coll ((Finset.range (x.regs (CountCall.length j))).image (values j))
          (x.regs factor * q) * x.regs CollisionTest.card ≤
            x.regs (CollisionTest.threshold j)} := by
  let A (q : ℕ) : Prop := ∀ j : Fin 3,
    coll ((Finset.range (x.regs (CountCall.length j))).image (values j))
      (x.regs factor * q) * x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold j)
  let T := 34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
    x.regs (CountCall.length 2)) + 15 * (x.regs factor * x.regs limit) + 87
  have hquery (y : Data 64) (hy : Stable x y) (hiq : y.regs cursor ≤ x.regs limit)
      (ho : y.regs one = 1) (hz : y.regs zero = 0) (htwo : y.regs two = 2)
      (hp : (y.regs cursor).Prime) :
      ∃ z, ExecWithin (w + 2) query y z T ∧ Stable x z ∧
        z.regs good = (if A (y.regs cursor) then 1 else 0) ∧
        ∀ i, Control i → z.regs i = y.regs i := by
    let M := x.regs factor * y.regs cursor
    have hM : 0 < M := Nat.mul_pos hfactor hp.pos
    have hMle : M ≤ x.regs factor * x.regs limit := Nat.mul_le_mul_left _ hiq
    have hMf : GenericRAM.Signed.Fits w (M : ℤ) := hmod.of_natAbs_le hMle
    have henc : encode (M : ℤ) = 2 * M := by simp [encode]
    have hencoded : Fits (w + 2) (2 * M) := by
      rw [← henc]
      exact (encode_fits hMf).mono (by omega)
    have hraw : Fits (w + 2) M := hencoded.of_le (by omega)
    have hyf : y.regs factor = x.regs factor := hy.1 _ (by decide)
    unfold query
    wram_exec [hyf, htwo, hraw, hencoded, Nat.mul_comm]
    refine WP.name fun u hu => ?_
    have huc (i : Fin 64) (hi : Control i) : u.regs i = y.regs i := by
      subst hu; dsimp only [Control] at hi
      update_simp [rawModulus, modulus, CountCall.modulus]
    have huf (i : Fin 64) (hi : Fixed i) : u.regs i = x.regs i :=
      (huc i (by unfold Control Fixed at *; omega)).trans (hy.1 i hi)
    have hlen (j : Fin 3) : u.regs (CountCall.length j) = x.regs (CountCall.length j) :=
      huf _ (by dsimp [CountCall.length, Fixed]; omega)
    have hsrc (j : Fin 3) : u.regs (CountCall.source j) = x.regs (CountCall.source j) :=
      huf _ (by dsimp [CountCall.source, Fixed]; omega)
    have hscratch : u.regs CountCall.scratch = x.regs CountCall.scratch := huf _ (by decide)
    have hhist : u.regs CountCall.histogram = x.regs CountCall.histogram := huf _ (by decide)
    have hcard : u.regs CollisionTest.card = x.regs CollisionTest.card := huf _ (by decide)
    have hcut (j : Fin 3) : u.regs (CollisionTest.threshold j) =
        x.regs (CollisionTest.threshold j) :=
      huf _ (by dsimp [Fixed, CollisionTest.threshold]; omega)
    have hmodreg : u.regs CountCall.modulus = encode (M : ℤ) := by
      subst hu; wram_simp [henc, M]
    have huinput : ∀ j i, i < u.regs (CountCall.length j) →
        u.mem (u.regs (CountCall.source j) + i) = encode (values j i) := by
      intro j i hi
      rw [hlen] at hi
      have humem : u.mem = y.mem := by subst hu; rfl
      rw [humem, hsrc, hy.2 _ (by have := hsk j; omega)]
      exact hinput j i hi
    wram_call (Query.exec u values hM hMf hmodreg
        (by simpa only [hlen] using hvalues) (by simpa only [hsrc, hlen] using hs)
        (by simpa only [hscratch, hlen] using hk)
        (by rw [hhist]; exact hd.of_le (Nat.add_le_add_left hMle _))
        (by simpa only [hlen] using ht) (by simpa only [hlen, hcard] using hproduct)
        (by subst hu; regs_frame)
        (by simpa only [hsrc, hlen, hscratch] using hsk)
        (by simpa only [hscratch, hlen, hhist] using hkd) huinput
        (by simpa only [hlen] using hinj))
      with z ⟨hgood, hreg, hmem⟩
    have hcontrol (i : Fin 64) (hi : Control i) : z.regs i = y.regs i := by
      have hscl : i ≠ CollisionTest.scaled := by
        intro h; subst i; norm_num [Control, CollisionTest.scaled] at hi
      have hg : i ≠ CollisionTest.good := by
        intro h; subst i; norm_num [Control, CollisionTest.good] at hi
      exact (hreg i (by unfold Control at hi; omega) hscl hg).trans (huc i hi)
    refine ⟨?_, ?_, ?_, hcontrol⟩
    · dsimp only [T]
      rw [hlen 0, hlen 1, hlen 2]
      have := Nat.mul_le_mul_left 15 hMle
      omega
    · refine ⟨fun i hi => (hcontrol i (by unfold Fixed Control at *; omega)).trans
          (hy.1 i hi), ?_⟩
      intro a ha
      have humem : u.mem = y.mem := by subst hu; rfl
      rw [hmem a (by simpa only [hscratch] using ha), humem]
      exact hy.2 a ha
    · have hA : A (y.regs cursor) ↔
          coll ((Finset.range (x.regs (CountCall.length 0))).image (values 0)) M *
            x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 0) ∧
          coll ((Finset.range (x.regs (CountCall.length 1))).image (values 1)) M *
            x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 1) ∧
          coll ((Finset.range (x.regs (CountCall.length 2))).image (values 2)) M *
            x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 2) := by
        simp [A, M, Fin.forall_fin_succ]
      simpa only [hlen, hcard, hcut, ← hA] using hgood
  obtain ⟨y, he, hs, ha⟩ := exec_driver x A hfit haddr hbefore hbitmap hquery
  refine ⟨y, he.mono ?_, hs.1, hs.2, ha⟩
  dsimp only [T]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 9

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Search
