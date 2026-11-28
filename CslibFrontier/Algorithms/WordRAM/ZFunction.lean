/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.ZFunction.Basic
public import CslibFrontier.Algorithms.Lean.ZFunction.Search
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.Sort

/-!
# The Z-Algorithm and Exact Pattern Matching on the Word RAM

This module implements Gusfield's Z-algorithm (`[Gusfield1997]`, Sections 1.4–1.5) as uniform
16-register `Basis.standard` Word-RAM programs over word arrays, proving exact output agreement
with `Cslib.Algorithms.Lean.ZFunction.zFunction` and `Cslib.Algorithms.Lean.ZFunction.zMatches`
(`= KMP.kmpMatchesList`) together with linear `O(|s|)` and `O(|pat| + |txt|)` instruction bounds
that charge every comparison, Z-box copy, arithmetic operation, memory access, and output write.

## Memory layouts and cost bounds

1. **Z-array construction (`zCode`, `zProgram`):**
   * **Input (`State.init s`):** `mem[0] = |s|` and `s` occupies `[1, 1 + |s|)`.
   * **Output:** `zFunction s` written as a length-prefixed array at `y.regs Reg.out = |s| + 1`
     (`mem[|s| + 1] = |s|` and `z[j]` at `|s| + 2 + j`), preserving `s` at `[1, 1 + |s|)`.
   * **Word width and time:** for every word width `w` with `Fits w (2 * |s| + 1)`, `zCode`
     executes within `39 * |s| + 9` instructions (`39 * |s| + 10` for `zProgram`).

2. **Exact pattern matching via the Z-array of `pat ++ txt` (`matchCode`, `matchProgram`):**
   * **Input (`State.init I.encode`):** `MatchInput.encode I = |pat| :: |txt| :: (pat ++ txt)`
     places `|pat|` at `mem[1]`, `|txt|` at `mem[2]`, and `pat ++ txt` contiguously at
     `[3, 3 + |pat| + |txt|)` (`pat` at `[3, 3 + |pat|)` and `txt` at
     `[3 + |pat|, 3 + |pat| + |txt|)`).
   * **Workspace and output:** for `|pat| > 0`, the Z-array of `pat ++ txt` is computed in
     `[3 + |pat| + |txt|, 3 + 2 * (|pat| + |txt|))`, and the matching shifts `zMatches pat txt`
     are written as a length-prefixed array at `y.regs Reg.out = 3 + 2 * (|pat| + |txt|)` (which
     also serves as the output base when `pat = []`). Both input blocks `pat` and `txt` are
     preserved.
   * **Word width and time:** for every word width `w` with
     `Fits w (2 * |pat| + 3 * |txt| + 4)`, `matchCode` executes within
     `39 * |pat| + 50 * |txt| + 22` instructions (`39 * |pat| + 50 * |txt| + 23` for
     `matchProgram`).

## Amortized analysis

During the Z-box scan over `s` (`|s| ≥ 1`), the rightmost Z-box right endpoint `r` never decreases
(`r ≤ r' ≤ |s|`), and each matched character comparison in `extCode` (`10` instructions per match)
advances the new right endpoint `r' = i + k` past `max r i ≥ r` by `1`. Thus the potential
$$\Phi(i, r) = 10 \cdot (|s| - r) + 29 \cdot (|s| - i)$$
pays `10` instructions per matched character comparison from `10 * (|s| - r)` and `29` instructions
per position `i` from `29 * (|s| - i)` to cover the Z-box test, at most one mismatch check, memory
writes, and loop overhead.

## Main definitions

* `Cslib.Algorithms.WordRAM.ZFunction.MatchInput`: pattern-and-text word-array input record.
* `Cslib.Algorithms.WordRAM.ZFunction.MatchInput.encode`: flat word-list encoding
  `[|pat|, |txt|] ++ pat ++ txt`.
* `Cslib.Algorithms.WordRAM.ZFunction.Reg.out`: output base register (`15`).
* `Cslib.Algorithms.WordRAM.ZFunction.zCode`, `zProgram`: Word-RAM Z-array code and program.
* `Cslib.Algorithms.WordRAM.ZFunction.matchCode`, `matchProgram`: Word-RAM Z-algorithm pattern
  matcher code and program.

## Main results

* `Cslib.Algorithms.WordRAM.ZFunction.zCode_exec` and `zProgram_computesListInTime`: linear-time
  Word-RAM Z-array construction (`39 * |s| + 9` / `39 * |s| + 10` instructions).
* `Cslib.Algorithms.WordRAM.ZFunction.matchCode_exec`, `matchProgram_computesListInTime`, and
  `matchProgram_computesKmpMatchesInTime`: linear-time Word-RAM exact pattern matching
  (`39 * |pat| + 50 * |txt| + 22` / `39 * |pat| + 50 * |txt| + 23` instructions).

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*, Sections 1.4–1.5][Gusfield1997]
-/

public section

namespace Cslib.Algorithms.WordRAM.ZFunction

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.ZFunction

/-! ## Input encoding and registers -/

/-- Pattern-matching instance on the word RAM: a pattern `pat` and a text `txt` over `w`-bit
words. -/
structure MatchInput where
  /-- Pattern word sequence. -/
  pat : List ℕ
  /-- Text word sequence. -/
  txt : List ℕ
  deriving DecidableEq, Repr

/-- Word-list layout `[|pat|, |txt|] ++ pat ++ txt` placed into `State.init`: `mem[1] = |pat|`,
`mem[2] = |txt|`, `pat` occupies `[3, 3 + |pat|)`, `txt` occupies `[3 + |pat|, 3 + |pat| + |txt|)`,
and `pat ++ txt` occupies `[3, 3 + |pat| + |txt|)`. -/
@[expose] def MatchInput.encode (I : MatchInput) : List ℕ :=
  I.pat.length :: I.txt.length :: (I.pat ++ I.txt)

namespace Reg

private abbrev zero : Fin 16 := 0
private abbrev one : Fin 16 := 1
private abbrev patLen : Fin 16 := 2
private abbrev txtLen : Fin 16 := 3
private abbrev sBase : Fin 16 := 4
private abbrev sLen : Fin 16 := 5
private abbrev zBase : Fin 16 := 6
private abbrev regi : Fin 16 := 7
private abbrev regl : Fin 16 := 8
private abbrev regr : Fin 16 := 9
private abbrev regk : Fin 16 := 10
private abbrev outCnt : Fin 16 := 11
private abbrev go : Fin 16 := 12
private abbrev t0 : Fin 16 := 13
private abbrev t1 : Fin 16 := 14
/-- Address register `out` of the length-prefixed output array. -/
abbrev out : Fin 16 := 15

end Reg

open Reg

/-! ## Programs -/

/-- One step of common-prefix extension between `s` (at `sBase`) and `s.drop regi`: if
`regi + regk < sLen` and `s[regk] = s[regi + regk]`, increments `regk`; otherwise clears `go`. -/
private def extBody : Code .standard 16 := ram[
  t0 ← regi + regk;
  if t0 < sLen then [
    t1 ← sBase + regk;
    t1 ← *t1;
    t0 ← sBase + t0;
    t0 ← *t0;
    if t1 = t0 then [
      regk ← regk + one
    ] else [
      go ← #0
    ]
  ] else [
    go ← #0
  ] ]

/-- Extend `regk` until `regi + regk = sLen` or `s[regk] ≠ s[regi + regk]`. -/
private def extCode : Code .standard 16 :=
  .seq (ram[ go ← #1 ]) (.loop (.lt zero go) extBody)

/-- Run `extCode`, store `z[regi] = regk`, update Z-box `[regi, regi + regk)`, and increment
`regi`. -/
private def zExtendTail : Code .standard 16 :=
  .seq extCode (ram[
    t0 ← zBase + regi;
    *t0 ← regk;
    regl ← regi;
    regr ← regi + regk;
    regi ← regi + one ])

/-- One position `regi` (`1 ≤ regi < sLen`) of the Z-algorithm loop. -/
private def zBody : Code .standard 16 :=
  .branch (.lt regi regr)
    (.seq (ram[
        t0 ← regi - regl;
        t0 ← zBase + t0;
        t0 ← *t0;
        t1 ← regr - regi ])
      (.branch (.lt t0 t1)
        (ram[
          t1 ← zBase + regi;
          *t1 ← t0;
          regi ← regi + one ])
        (.seq (ram[ regk ← t1 ]) zExtendTail)))
    (.seq (ram[ regk ← zero ]) zExtendTail)

/-- Compute `zFunction s` (`|s| = sLen ≥ 1`) at `[zBase, zBase + sLen)` for `s` at
`[sBase, sBase + sLen)`. -/
private def buildZNonempty : Code .standard 16 :=
  .seq (ram[
      *zBase ← sLen;
      regi ← one;
      regl ← zero;
      regr ← zero ])
    (.loop (.lt regi sLen) zBody)

/-- Standalone Z-array code: reads `s` from `State.init s` and writes `zFunction s` as a
length-prefixed array at `out = |s| + 1`. -/
def zCode : Code .standard 16 :=
  .seq (ram[
      zero ← #0;
      one ← #1;
      sLen ← *zero;
      sBase ← one;
      out ← sLen + one;
      *out ← sLen ])
    (.branch (.lt zero sLen)
      (.seq (ram[ zBase ← out + one ]) buildZNonempty)
      (ram[ regk ← zero ]))

/-- Uniform `Basis.standard` Word-RAM program for Z-array construction. -/
def zProgram : Program .standard 16 := zCode.program out

private def emptyMatchBody : Code .standard 16 := ram[
  t0 ← out + one;
  t0 ← t0 + regi;
  *t0 ← regi;
  regi ← regi + one ]

private def emptyMatchCode : Code .standard 16 :=
  .seq (ram[ t1 ← txtLen + one; *out ← t1; regi ← zero ])
    (.loop (.lt regi t1) emptyMatchBody)

private def filterBody : Code .standard 16 := ram[
  t0 ← patLen + regi;
  t0 ← zBase + t0;
  t0 ← *t0;
  if t0 < patLen then [
    regi ← regi + one
  ] else [
    outCnt ← outCnt + one;
    t1 ← out + outCnt;
    *t1 ← regi;
    regi ← regi + one
  ] ]

private def nonemptyMatchCode : Code .standard 16 :=
  .seq buildZNonempty
    (.seq (ram[ outCnt ← zero; regi ← zero ])
      (.seq (.loop (.lt regi txtLen) filterBody)
        (ram[ *out ← outCnt ])))

private def matchSetup : Code .standard 16 := ram[
  zero ← #0;
  one ← #1;
  t0 ← #2;
  sBase ← #3;
  patLen ← *one;
  txtLen ← *t0;
  sLen ← patLen + txtLen;
  zBase ← sBase + sLen;
  out ← zBase + sLen ]

/-- Word-RAM exact pattern-matching code via the Z-array of `pat ++ txt`. -/
def matchCode : Code .standard 16 :=
  .seq matchSetup (.branch (.lt zero patLen) nonemptyMatchCode emptyMatchCode)

/-- Uniform `Basis.standard` Word-RAM program for Z-algorithm exact pattern matching. -/
def matchProgram : Program .standard 16 := matchCode.program out

/-! ## Bundled register invariants -/

private structure ZBuildRegs (sb zb len : ℕ) (x : Data 16) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  sb_eq : x.regs sBase = sb
  zb_eq : x.regs zBase = zb
  len_eq : x.regs sLen = len

private theorem ZBuildRegs.of_ext_frame {sb zb len : ℕ} {x y : Data 16}
    (hr : ZBuildRegs sb zb len x)
    (hfr : ∀ r : Fin 16, r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 → y.regs r = x.regs r) :
    ZBuildRegs sb zb len y :=
  ⟨(hfr _ (by decide) (by decide) (by decide) (by decide)).trans hr.zero_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide)).trans hr.one_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide)).trans hr.sb_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide)).trans hr.zb_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide)).trans hr.len_eq⟩

private theorem ZBuildRegs.set_scratch {sb zb len : ℕ} {x : Data 16} (hr : ZBuildRegs sb zb len x)
    (d : Fin 16) (v : ℕ) (h0 : zero ≠ d := by decide) (h1 : one ≠ d := by decide)
    (hsb : sBase ≠ d := by decide) (hzb : zBase ≠ d := by decide)
    (hsl : sLen ≠ d := by decide) : ZBuildRegs sb zb len (x.set d v) :=
  ⟨by simp only [Data.set_regs, Function.update_of_ne h0, hr.zero_eq],
   by simp only [Data.set_regs, Function.update_of_ne h1, hr.one_eq],
   by simp only [Data.set_regs, Function.update_of_ne hsb, hr.sb_eq],
   by simp only [Data.set_regs, Function.update_of_ne hzb, hr.zb_eq],
   by simp only [Data.set_regs, Function.update_of_ne hsl, hr.len_eq]⟩

/-! ## Execution of `extCode` -/

private theorem while_ext_stop {w : ℕ} {s : List ℕ} {x x₁ : Data 16} {T : ℕ}
    (hc_go : (Cond.lt zero go).Holds x)
    (hbody : ExecWithin w extBody x x₁ T)
    (hT : T + 4 ≤ 13)
    (hx₁_z : x₁.regs zero = 0)
    (hx₁_go : x₁.regs go = 0)
    (hx₁_k : x₁.regs regk = x.regs regk)
    (hx₁_mem : x₁.mem = x.mem)
    (hx₁_fr : ∀ r : Fin 16, r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 → x₁.regs r = x.regs r)
    (hlcp_zero : List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) = 0) :
    ∃ y T',
      ExecWithin w (.loop (.lt zero go) extBody) x y T' ∧
      y.regs regk = x.regs regk +
        List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) ∧
      T' ≤ 10 * List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) + 13 ∧
      y.mem = x.mem ∧
      ∀ r : Fin 16, r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 → y.regs r = x.regs r := by
  have hc_stop : ¬(Cond.lt zero go).Holds x₁ := by
    simp only [Cond.holds_lt, hx₁_z, hx₁_go]
    exact Nat.lt_irrefl 0
  exact ⟨x₁, T + 4, ExecWithin.loop_once hc_go hbody hc_stop,
    by rw [hx₁_k, hlcp_zero, Nat.add_zero],
    by rw [hlcp_zero]; exact hT, hx₁_mem, hx₁_fr⟩

private theorem while_ext_spec {w : ℕ} (s : List ℕ) (sb zb : ℕ) :
    ∀ (rem : ℕ) (x : Data 16),
      s.length - (x.regs regi + x.regs regk) = rem →
      ZBuildRegs sb zb s.length x →
      x.regs go = 1 →
      0 < x.regs regi →
      x.regs regi + x.regs regk ≤ s.length →
      Fits w s.length →
      Fits w (sb + s.length) →
      Block.HoldsList sb s x.mem →
      ∃ y T,
        ExecWithin w (.loop (.lt zero go) extBody) x y T ∧
        y.regs regk = x.regs regk +
          List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) ∧
        T ≤ 10 * List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) + 13 ∧
        y.mem = x.mem ∧
        ∀ r : Fin 16, r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 → y.regs r = x.regs r := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro x hrem hr hgo hi_pos hik_le hf_len hf_sb hs
    have hc_go : (Cond.lt zero go).Holds x := by
      simp only [Cond.holds_lt, hr.zero_eq, hgo]
      exact Nat.zero_lt_one
    have hf_ik : Fits w (x.regs regi + x.regs regk) := hf_len.of_le hik_le
    by_cases hik_lt : x.regs regi + x.regs regk < s.length
    · have hk_lt : x.regs regk < s.length :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left hi_pos) (Nat.le_of_lt hik_lt)
      have hf_sbk : Fits w (sb + x.regs regk) :=
        hf_sb.of_le (Nat.add_le_add_left (Nat.le_of_lt hk_lt) sb)
      have hf_sbik : Fits w (sb + (x.regs regi + x.regs regk)) :=
        hf_sb.of_le (Nat.add_le_add_left (Nat.le_of_lt hik_lt) sb)
      have hread_k : x.mem (sb + x.regs regk) = s[x.regs regk] := hs.get (x.regs regk) hk_lt
      have hread_ik : x.mem (sb + (x.regs regi + x.regs regk)) = s[x.regs regi + x.regs regk] :=
        hs.get (x.regs regi + x.regs regk) hik_lt
      by_cases heq_ch : s[x.regs regk] = s[x.regs regi + x.regs regk]
      · have hf_k1 : Fits w (x.regs regk + 1) :=
          hf_len.of_le (Nat.succ_le_of_lt hk_lt)
        have hbody_ex : ∃ x₁, ExecWithin w extBody x x₁ 8 ∧
            x₁.regs regk = x.regs regk + 1 ∧
            x₁.regs go = 1 ∧
            x₁.mem = x.mem ∧
            ∀ r : Fin 16, r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 → x₁.regs r = x.regs r := by
          refine WP.exists_execWithin ?_
          unfold extBody
          wram_exec [hr.one_eq, hr.sb_eq, hr.len_eq, hik_lt, hread_k, hread_ik, heq_ch,
            hf_ik, hf_sbk, hf_sbik, hf_k1]
          refine ⟨by wram_simp, by wram_simp [hgo], rfl, fun r hr1 hr2 hr3 hr4 => ?_⟩
          simp only [Data.set_regs, Function.update_of_ne hr1, Function.update_of_ne hr3,
            Function.update_of_ne hr4]
        obtain ⟨x₁, hbody, hx₁_k, hx₁_go, hx₁_mem, hx₁_fr⟩ := hbody_ex
        have hx₁_i : x₁.regs regi = x.regs regi :=
          hx₁_fr regi (by decide) (by decide) (by decide) (by decide)
        have hr₁ : ZBuildRegs sb zb s.length x₁ := hr.of_ext_frame hx₁_fr
        have hrem_lt : s.length - (x₁.regs regi + x₁.regs regk) < rem := by
          rw [← hrem, hx₁_i, hx₁_k]
          omega
        obtain ⟨y, T', hrest, hy_k, hT', hy_mem, hy_fr⟩ :=
          ih _ hrem_lt x₁ rfl hr₁ hx₁_go (hx₁_i ▸ hi_pos)
            (by rw [hx₁_i, hx₁_k]; omega) hf_len hf_sb (hx₁_mem ▸ hs)
        rw [hx₁_i, hx₁_k] at hy_k hT'
        have hlcp_step : List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) =
            List.lcpLen (s.drop (x.regs regk + 1)) (s.drop (x.regs regi + (x.regs regk + 1))) +
              1 := by
          rw [List.drop_eq_getElem_cons hk_lt, List.drop_eq_getElem_cons hik_lt, heq_ch,
            List.lcpLen_cons_cons_self, Nat.add_assoc]
        refine ⟨y, 8 + T' + 2, ExecWithin.loop_iter hc_go hbody hrest, ?_, ?_,
          hy_mem.trans hx₁_mem, fun r hr1 hr2 hr3 hr4 =>
            (hy_fr r hr1 hr2 hr3 hr4).trans (hx₁_fr r hr1 hr2 hr3 hr4)⟩
        · rw [hy_k, hlcp_step]
          omega
        · rw [hlcp_step]
          omega
      · have hf_0 : Fits w 0 := hf_len.of_le (Nat.zero_le _)
        let x₁ := (((((x.set t0 (x.regs regi + x.regs regk)).set t1 (sb + x.regs regk)).set
            t1 s[x.regs regk]).set t0 (sb + (x.regs regi + x.regs regk))).set
              t0 s[x.regs regi + x.regs regk]).set go 0
        have hbody : ExecWithin w extBody x x₁ 9 := by
          unfold extBody
          ram_eval [x₁, hr.sb_eq, hr.len_eq, hik_lt, hread_k, hread_ik, heq_ch,
            hf_ik, hf_sbk, hf_sbik, hf_0]
        refine while_ext_stop hc_go hbody (by decide) (by simp +decide [x₁, hr.zero_eq])
          (by simp +decide [x₁]) (by simp +decide [x₁]) rfl (fun r _ hr2 hr3 hr4 => by
            simp only [x₁, Data.set_regs, Function.update_of_ne hr2, Function.update_of_ne hr3,
              Function.update_of_ne hr4]) ?_
        rw [List.drop_eq_getElem_cons hk_lt, List.drop_eq_getElem_cons hik_lt,
          List.lcpLen_cons_cons]
        simp only [heq_ch, ↓reduceIte]
    · have hik_eq : x.regs regi + x.regs regk = s.length :=
        Nat.le_antisymm hik_le (Nat.not_lt.mp hik_lt)
      have hf_0 : Fits w 0 := hf_len.of_le (Nat.zero_le _)
      let x₁ := (x.set t0 (x.regs regi + x.regs regk)).set go 0
      have hbody : ExecWithin w extBody x x₁ 4 := by
        unfold extBody
        ram_eval [x₁, hr.len_eq, hik_lt, hf_ik, hf_0]
      refine while_ext_stop hc_go hbody (by decide) (by simp +decide [x₁, hr.zero_eq])
        (by simp +decide [x₁]) (by simp +decide [x₁]) rfl (fun r _ hr2 hr3 _ => by
          simp only [x₁, Data.set_regs, Function.update_of_ne hr2, Function.update_of_ne hr3]) ?_
      rw [hik_eq, List.drop_length, List.lcpLen_nil_right]

private theorem extCode_spec {w : ℕ} (s : List ℕ) (sb zb : ℕ) (x : Data 16)
    (hr : ZBuildRegs sb zb s.length x)
    (hi_pos : 0 < x.regs regi)
    (hik_le : x.regs regi + x.regs regk ≤ s.length)
    (hk_lcp : x.regs regk ≤ List.lcpLen s (s.drop (x.regs regi)))
    (hf_len : Fits w s.length)
    (hf_sb : Fits w (sb + s.length))
    (hs : Block.HoldsList sb s x.mem) :
    ∃ y T,
      ExecWithin w extCode x y T ∧
      y.regs regk = List.lcpLen s (s.drop (x.regs regi)) ∧
      T ≤ 10 * (List.lcpLen s (s.drop (x.regs regi)) - x.regs regk) + 14 ∧
      y.mem = x.mem ∧
      ∀ r : Fin 16, r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 → y.regs r = x.regs r := by
  have hf_1 : Fits w 1 := hf_len.of_le (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hi_pos
    (Nat.le_trans (Nat.le_add_right _ _) hik_le)))
  let x₀ := x.set go 1
  have hgo_step : ExecWithin (B := .standard) w (ram[ go ← #1 ]) x x₀ 1 :=
    ExecWithin.const (B := .standard) hf_1
  have hr₀ : ZBuildRegs sb zb s.length x₀ := hr.set_scratch go 1
  have hx₀_i : x₀.regs regi = x.regs regi := by simp +decide [x₀]
  have hx₀_k : x₀.regs regk = x.regs regk := by simp +decide [x₀]
  obtain ⟨y, T', hloop, hy_k, hT', hy_mem, hy_fr⟩ :=
    while_ext_spec s sb zb (s.length - (x₀.regs regi + x₀.regs regk)) x₀ rfl hr₀
      (by simp +decide [x₀]) (hx₀_i ▸ hi_pos) (by rw [hx₀_i, hx₀_k]; exact hik_le)
      hf_len hf_sb hs
  rw [hx₀_i, hx₀_k] at hy_k hT'
  have hlcp_split : List.lcpLen s (s.drop (x.regs regi)) =
      x.regs regk + List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) := by
    rw [List.lcpLen_eq_add_lcpLen_drop hk_lcp, List.drop_drop,
      Nat.add_comm (x.regs regi) (x.regs regk)]
  have hd_eq : List.lcpLen (s.drop (x.regs regk)) (s.drop (x.regs regi + x.regs regk)) =
      List.lcpLen s (s.drop (x.regs regi)) - x.regs regk := by omega
  unfold extCode
  refine ⟨y, 1 + T', hgo_step.seq hloop, hy_k.trans hlcp_split.symm,
    by rw [hd_eq] at hT'; omega, hy_mem, fun r hr1 hr2 hr3 hr4 => ?_⟩
  rw [hy_fr r hr1 hr2 hr3 hr4]
  simp only [x₀, Data.set_regs, Function.update_of_ne hr2]

/-! ## Execution of `buildZNonempty` and `zCode` -/

private def zPotential (len : ℕ) (x : Data 16) : ℕ :=
  10 * (len - x.regs regr) + 29 * (len - x.regs regi)

private structure ZInv (s : List ℕ) (sb zb : ℕ) (x₀ x : Data 16) : Prop where
  regs_ok : ZBuildRegs sb zb s.length x
  i_ge_one : 1 ≤ x.regs regi
  i_le : x.regs regi ≤ s.length
  l_lt_i : x.regs regl < x.regs regi
  r_le : x.regs regr ≤ s.length
  r_zero_or_l_pos : x.regs regr = 0 ∨ 0 < x.regs regl
  box_lcp : x.regs regr ≤ x.regs regl + List.lcpLen s (s.drop (x.regs regl))
  z_holds : ∀ j < x.regs regi, x.mem (zb + j) = List.lcpLen s (s.drop j)
  mem_frame : ∀ a, (a < zb ∨ zb + s.length ≤ a) → x.mem a = x₀.mem a
  reg_frame : ∀ r : Fin 16,
    r ≠ regi → r ≠ regl → r ≠ regr → r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 →
      x.regs r = x₀.regs r

private theorem zExtendTail_spec {w : ℕ} (s : List ℕ) (sb zb : ℕ) (x₀ s₁ : Data 16)
    (hr₁ : ZBuildRegs sb zb s.length s₁)
    (hi_ge : 1 ≤ s₁.regs regi) (hi_lt : s₁.regs regi < s.length)
    (hik_ge_r : s₁.regs regr ≤ s₁.regs regi + s₁.regs regk)
    (hik_le : s₁.regs regi + s₁.regs regk ≤ s.length)
    (hk_lcp : s₁.regs regk ≤ List.lcpLen s (s.drop (s₁.regs regi)))
    (hf_sb : Fits w (sb + s.length))
    (hf_zb : Fits w (zb + (s.length - 1)))
    (hs_holds : Block.HoldsList sb s s₁.mem)
    (hz_prev : ∀ j < s₁.regs regi, s₁.mem (zb + j) = List.lcpLen s (s.drop j))
    (hm_fr : ∀ a, (a < zb ∨ zb + s.length ≤ a) → s₁.mem a = x₀.mem a)
    (hr_fr : ∀ r : Fin 16,
      r ≠ regi → r ≠ regl → r ≠ regr → r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 →
        s₁.regs r = x₀.regs r) :
    ∃ z T,
      ExecWithin w zExtendTail s₁ z T ∧
      ZInv s sb zb x₀ z ∧
      z.regs regi = s₁.regs regi + 1 ∧
      s₁.regs regr ≤ z.regs regr ∧
      T ≤ 10 * (z.regs regr - s₁.regs regr) + 19 := by
  have hf_len : Fits w s.length := hf_sb.of_le (Nat.le_add_left _ _)
  obtain ⟨s₂, T_ext, hext, hs₂_k, hT_ext, hs₂_mem, hs₂_fr⟩ :=
    extCode_spec s sb zb s₁ hr₁ hi_ge hik_le hk_lcp hf_len hf_sb hs_holds
  have hr₂ : ZBuildRegs sb zb s.length s₂ := hr₁.of_ext_frame hs₂_fr
  have hs₂_i : s₂.regs regi = s₁.regs regi :=
    hs₂_fr regi (by decide) (by decide) (by decide) (by decide)
  have hlcp_bound : List.lcpLen s (s.drop (s₁.regs regi)) ≤ s.length - s₁.regs regi := by
    simpa only [List.length_drop] using List.lcpLen_le_length_right s (s.drop (s₁.regs regi))
  have hik_final_le : s₁.regs regi + s₂.regs regk ≤ s.length := by
    rw [hs₂_k]
    omega
  have hf_zbi : Fits w (zb + s₁.regs regi) := hf_zb.of_le (by omega)
  have hf_ik_fin : Fits w (s₁.regs regi + s₂.regs regk) := hf_len.of_le hik_final_le
  have hf_i1 : Fits w (s₁.regs regi + 1) := hf_len.of_le (Nat.succ_le_of_lt hi_lt)
  have hpost_ex : ∃ z, ExecWithin w (ram[
        t0 ← zBase + regi;
        *t0 ← regk;
        regl ← regi;
        regr ← regi + regk;
        regi ← regi + one ]) s₂ z 5 ∧
      ZBuildRegs sb zb s.length z ∧
      z.regs regi = s₁.regs regi + 1 ∧
      z.regs regl = s₁.regs regi ∧
      z.regs regr = s₁.regs regi + s₂.regs regk ∧
      z.mem = Function.update s₁.mem (zb + s₁.regs regi) (s₂.regs regk) ∧
      ∀ r : Fin 16,
        r ≠ regi → r ≠ regl → r ≠ regr → r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 →
          z.regs r = s₂.regs r := by
    refine WP.exists_execWithin ?_
    wram_exec [hr₂.one_eq, hr₂.zb_eq, hs₂_i, hf_zbi, hf_ik_fin, hf_i1]
    refine ⟨⟨by wram_simp [hr₂.zero_eq], by wram_simp [hr₂.one_eq], by wram_simp [hr₂.sb_eq],
      by wram_simp [hr₂.zb_eq], by wram_simp [hr₂.len_eq]⟩,
      by wram_simp [hs₂_i], by wram_simp [hs₂_i], by wram_simp [hs₂_i],
      by wram_simp [hs₂_mem, hs₂_i], fun r hr1 hr2 hr3 _ _ hr6 _ => ?_⟩
    simp only [Data.set_regs, Data.write_regs, Function.update_of_ne hr1,
      Function.update_of_ne hr2, Function.update_of_ne hr3, Function.update_of_ne hr6]
  obtain ⟨z, hpost, hrz, hz_i, hz_l, hz_r, hz_mem, hz_fr⟩ := hpost_ex
  have hk_ge_k0 : s₁.regs regk ≤ s₂.regs regk := by rw [hs₂_k]; exact hk_lcp
  have hr_mono : s₁.regs regr ≤ z.regs regr := by
    rw [hz_r]
    exact Nat.le_trans hik_ge_r (Nat.add_le_add_left hk_ge_k0 _)
  have hdiff_le : List.lcpLen s (s.drop (s₁.regs regi)) - s₁.regs regk ≤
      z.regs regr - s₁.regs regr := by
    rw [hz_r, hs₂_k]
    clear hs₂_k hk_lcp hlcp_bound hz_prev
    omega
  unfold zExtendTail
  refine ⟨z, T_ext + 5, hext.seq hpost, ?_, hz_i, hr_mono,
    by clear hs₂_k hk_lcp hlcp_bound hz_prev; omega⟩
  refine ⟨hrz, by rw [hz_i]; omega, hz_i ▸ Nat.succ_le_of_lt hi_lt,
    by rw [hz_l, hz_i]; exact Nat.lt_succ_self _,
    hz_r ▸ hik_final_le, Or.inr (hz_l ▸ hi_ge),
    by rw [hz_r, hz_l, hs₂_k], ?_, ?_, ?_⟩
  · intro j hj
    rw [hz_i] at hj
    rw [hz_mem]
    by_cases hji : j = s₁.regs regi
    · subst hji
      rw [Function.update_self, hs₂_k]
    · rw [Function.update_of_ne (by omega)]
      exact hz_prev j (by omega)
  · intro a ha
    rw [hz_mem, Function.update_of_ne (by omega)]
    exact hm_fr a ha
  · intro r h1 h2 h3 h4 h5 h6 h7
    exact (hz_fr r h1 h2 h3 h4 h5 h6 h7).trans
      ((hs₂_fr r h4 h5 h6 h7).trans (hr_fr r h1 h2 h3 h4 h5 h6 h7))

private theorem zBody_spec {w : ℕ} (s : List ℕ) (sb zb : ℕ) (x₀ : Data 16)
    (hf_sb : Fits w (sb + s.length))
    (hf_zb : Fits w (zb + (s.length - 1)))
    (hs_init : Block.HoldsList sb s x₀.mem)
    (hdisj : sb + s.length ≤ zb)
    (x : Data 16) (hx : ZInv s sb zb x₀ x) (hc : (Cond.lt regi sLen).Holds x) :
    ∃ z T, ExecWithin w zBody x z T ∧ ZInv s sb zb x₀ z ∧
      T + 2 + zPotential s.length z ≤ zPotential s.length x := by
  obtain ⟨hrx, hi_ge, _, hl_lt, hr_le, hr0_l, hbox_lcp, hz_prev, hm_fr, hr_fr⟩ := hx
  have hi_lt : x.regs regi < s.length := by simpa only [Cond.holds_lt, hrx.len_eq] using hc
  have hf_len : Fits w s.length := hf_sb.of_le (Nat.le_add_left _ _)
  have hs_x : Block.HoldsList sb s x.mem :=
    hs_init.frame fun a _ ha2 => hm_fr a (Or.inl (Nat.lt_of_lt_of_le ha2 hdisj))
  unfold zBody
  by_cases hir : x.regs regi < x.regs regr
  · have hc_ir : (Cond.lt regi regr).Holds x := hir
    have hl_pos : 0 < x.regs regl := by
      rcases hr0_l with hr0 | hpos
      · exact absurd (hr0 ▸ hir) (Nat.not_lt_zero _)
      · exact hpos
    have hil_lt : x.regs regi - x.regs regl < x.regs regi := Nat.sub_lt hi_ge hl_pos
    have hf_il : Fits w (x.regs regi - x.regs regl) :=
      hf_len.of_le (Nat.le_of_lt (Nat.lt_trans hil_lt hi_lt))
    have hf_zbil : Fits w (zb + (x.regs regi - x.regs regl)) :=
      hf_zb.of_le (by have := Nat.lt_trans hil_lt hi_lt; omega)
    have hf_rem : Fits w (x.regs regr - x.regs regi) :=
      hf_len.of_le (Nat.le_trans (Nat.sub_le _ _) hr_le)
    have hread_zil : x.mem (zb + (x.regs regi - x.regs regl)) =
        List.lcpLen s (s.drop (x.regs regi - x.regs regl)) :=
      hz_prev (x.regs regi - x.regs regl) hil_lt
    have hbox_min :
        min (List.lcpLen s (s.drop (x.regs regi - x.regs regl))) (x.regs regr - x.regs regi) =
          min (List.lcpLen s (s.drop (x.regs regi))) (x.regs regr - x.regs regi) :=
      min_lcpLen_zBox s (Nat.le_of_lt hl_lt) (Nat.le_of_lt hir) hbox_lcp
    let zil := List.lcpLen s (s.drop (x.regs regi - x.regs regl))
    let rem := x.regs regr - x.regs regi
    have hprep_ex : ∃ s₁, ExecWithin w (ram[
          t0 ← regi - regl;
          t0 ← zBase + t0;
          t0 ← *t0;
          t1 ← regr - regi ]) x s₁ 4 ∧
        ZBuildRegs sb zb s.length s₁ ∧
        s₁.regs t0 = zil ∧
        s₁.regs t1 = rem ∧
        s₁.mem = x.mem ∧
        ∀ r : Fin 16, r ≠ t0 → r ≠ t1 → s₁.regs r = x.regs r := by
      refine WP.exists_execWithin ?_
      wram_exec [hrx.zb_eq, hread_zil, hf_il, hf_zbil, hf_rem]
      refine ⟨⟨by wram_simp [hrx.zero_eq], by wram_simp [hrx.one_eq], by wram_simp [hrx.sb_eq],
        by wram_simp [hrx.zb_eq], by wram_simp [hrx.len_eq]⟩,
        by wram_simp [zil], by wram_simp [rem], rfl, fun r hr1 hr2 => ?_⟩
      simp only [Data.set_regs, Function.update_of_ne hr1, Function.update_of_ne hr2]
    obtain ⟨s₁, hprep, hrs₁, hs₁_t0, hs₁_t1, hs₁_mem, hs₁_fr⟩ := hprep_ex
    have hs₁_i : s₁.regs regi = x.regs regi := hs₁_fr regi (by decide) (by decide)
    have hs₁_l : s₁.regs regl = x.regs regl := hs₁_fr regl (by decide) (by decide)
    have hs₁_r : s₁.regs regr = x.regs regr := hs₁_fr regr (by decide) (by decide)
    by_cases hcopy : zil < rem
    · have hc_copy : (Cond.lt t0 t1).Holds s₁ := by
        simp only [Cond.holds_lt, hs₁_t0, hs₁_t1]
        exact hcopy
      have hzil_eq : zil = List.lcpLen s (s.drop (x.regs regi)) := by
        have hlt_raw : List.lcpLen s (s.drop (x.regs regi - x.regs regl)) <
            x.regs regr - x.regs regi := hcopy
        change List.lcpLen s (s.drop (x.regs regi - x.regs regl)) = _
        clear hbox_lcp hz_prev hread_zil hs₁_t0 hs₁_t1 hcopy
        omega
      have hf_zbi : Fits w (zb + x.regs regi) := hf_zb.of_le (by omega)
      have hf_i1 : Fits w (x.regs regi + 1) := hf_len.of_le (Nat.succ_le_of_lt hi_lt)
      have hcopy_ex : ∃ z, ExecWithin w (ram[
            t1 ← zBase + regi;
            *t1 ← t0;
            regi ← regi + one ]) s₁ z 3 ∧
          ZBuildRegs sb zb s.length z ∧
          z.regs regi = x.regs regi + 1 ∧
          z.regs regl = x.regs regl ∧
          z.regs regr = x.regs regr ∧
          z.mem = Function.update x.mem (zb + x.regs regi) zil ∧
          ∀ r : Fin 16, r ≠ regi → r ≠ t1 → z.regs r = s₁.regs r := by
        refine WP.exists_execWithin ?_
        wram_exec [hrs₁.one_eq, hrs₁.zb_eq, hs₁_i, hs₁_t0, hf_zbi, hf_i1]
        refine ⟨⟨by wram_simp [hrs₁.zero_eq], by wram_simp [hrs₁.one_eq],
          by wram_simp [hrs₁.sb_eq], by wram_simp [hrs₁.zb_eq], by wram_simp [hrs₁.len_eq]⟩,
          by wram_simp [hs₁_i], by wram_simp [hs₁_l], by wram_simp [hs₁_r],
          by wram_simp [hs₁_mem, hs₁_i, hs₁_t0], fun r hr1 hr2 => ?_⟩
        simp only [Data.set_regs, Data.write_regs, Function.update_of_ne hr1,
          Function.update_of_ne hr2]
      obtain ⟨z, hcopy_step, hrz, hz_i, hz_l, hz_r, hz_mem, hz_fr⟩ := hcopy_ex
      have hstep : ExecWithin w zBody x z 9 := by
        unfold zBody
        exact ExecWithin.branch_pos hc_ir (hprep.seq (ExecWithin.branch_pos hc_copy hcopy_step))
      refine ⟨z, 9, hstep, ?_, ?_⟩
      · refine ⟨hrz, by rw [hz_i]; omega, hz_i ▸ Nat.succ_le_of_lt hi_lt,
          by rw [hz_l, hz_i]; exact Nat.lt_succ_of_lt hl_lt,
          hz_r ▸ hr_le, hz_r ▸ (hz_l ▸ hr0_l), hz_r ▸ (hz_l ▸ hbox_lcp), ?_, ?_, ?_⟩
        · intro j hj
          rw [hz_i] at hj
          rw [hz_mem]
          by_cases hji : j = x.regs regi
          · subst hji
            rw [Function.update_self, hzil_eq]
          · rw [Function.update_of_ne (by omega)]
            exact hz_prev j (by omega)
        · intro a ha
          rw [hz_mem, Function.update_of_ne (by omega)]
          exact hm_fr a ha
        · intro r h1 h2 h3 h4 h5 h6 h7
          exact (hz_fr r h1 h7).trans ((hs₁_fr r h6 h7).trans (hr_fr r h1 h2 h3 h4 h5 h6 h7))
      · unfold zPotential
        rw [hz_r, hz_i]
        clear hbox_lcp hz_prev hread_zil hbox_min hzil_eq hcopy hs₁_t0 hs₁_t1
        omega
    · have hc_ncopy : ¬(Cond.lt t0 t1).Holds s₁ := by
        simp only [Cond.holds_lt, hs₁_t0, hs₁_t1]
        exact hcopy
      have hrem_le_lcp : rem ≤ List.lcpLen s (s.drop (x.regs regi)) := by
        have hge : rem ≤ zil := Nat.le_of_not_lt hcopy
        have h1 : min zil rem = rem := Nat.min_eq_right hge
        have h2 : min (List.lcpLen s (s.drop (x.regs regi))) rem = rem := hbox_min.symm.trans h1
        rw [← h2]
        exact Nat.min_le_left _ _
      let s₂ := s₁.set regk rem
      have hset_k : ExecWithin (B := .standard) w (ram[ regk ← t1 ]) s₁ s₂ 1 := by
        simpa only [s₂, hs₁_t1] using ExecWithin.copy (B := .standard) (d := regk) (s := t1)
          (x := s₁)
      have hrs₂ : ZBuildRegs sb zb s.length s₂ := hrs₁.set_scratch regk rem
      have hs₂_i : s₂.regs regi = x.regs regi := by simp +decide [s₂, hs₁_i]
      have hs₂_r : s₂.regs regr = x.regs regr := by simp +decide [s₂, hs₁_r]
      have hs₂_k : s₂.regs regk = rem := by simp +decide [s₂]
      have hik_eq_r : s₂.regs regi + s₂.regs regk = x.regs regr := by
        rw [hs₂_i, hs₂_k]
        exact Nat.add_sub_of_le (Nat.le_of_lt hir)
      obtain ⟨z, T_tail, htail, hz_inv, hz_i, _, hT_tail⟩ :=
        zExtendTail_spec s sb zb x₀ s₂ hrs₂ (hs₂_i ▸ hi_ge) (hs₂_i ▸ hi_lt)
          (by rw [hs₂_r, hik_eq_r]) (hik_eq_r ▸ hr_le)
          (by rw [hs₂_i, hs₂_k]; exact hrem_le_lcp) hf_sb hf_zb (hs₁_mem ▸ hs_x)
          (by rw [hs₂_i]; intro j hj; rw [show s₂.mem = x.mem from hs₁_mem]; exact hz_prev j hj)
          (fun a ha => by rw [show s₂.mem = x.mem from hs₁_mem]; exact hm_fr a ha)
          (fun r h1 h2 h3 h4 h5 h6 h7 => by
            simp only [s₂, Data.set_regs, Function.update_of_ne h4]
            exact (hs₁_fr r h6 h7).trans (hr_fr r h1 h2 h3 h4 h5 h6 h7))
      rw [hs₂_i] at hz_i
      rw [hs₂_r] at hT_tail
      have hstep : ExecWithin w zBody x z (T_tail + 8) := by
        unfold zBody
        exact (ExecWithin.branch_pos hc_ir
          (hprep.seq (ExecWithin.branch_neg hc_ncopy (hset_k.seq htail)))).mono (by omega)
      have hz_r_le : z.regs regr ≤ s.length := hz_inv.r_le
      refine ⟨z, T_tail + 8, hstep, hz_inv, ?_⟩
      unfold zPotential
      rw [hz_i]
      clear hbox_lcp hz_prev hread_zil hbox_min hrem_le_lcp hcopy hs₁_t0 hs₁_t1 hs₂_k hik_eq_r
      omega
  · have hc_nir : ¬(Cond.lt regi regr).Holds x := hir
    have hr_le_i : x.regs regr ≤ x.regs regi := Nat.not_lt.mp hir
    let s₁ := x.set regk 0
    have hset_k : ExecWithin (B := .standard) w (ram[ regk ← zero ]) x s₁ 1 := by
      simpa only [s₁, hrx.zero_eq] using ExecWithin.copy (B := .standard) (d := regk) (s := zero)
        (x := x)
    have hrs₁ : ZBuildRegs sb zb s.length s₁ := hrx.set_scratch regk 0
    have hs₁_i : s₁.regs regi = x.regs regi := by simp +decide [s₁]
    have hs₁_r : s₁.regs regr = x.regs regr := by simp +decide [s₁]
    have hs₁_k : s₁.regs regk = 0 := by simp +decide [s₁]
    obtain ⟨z, T_tail, htail, hz_inv, hz_i, _, hT_tail⟩ :=
      zExtendTail_spec s sb zb x₀ s₁ hrs₁ (hs₁_i ▸ hi_ge) (hs₁_i ▸ hi_lt)
        (by rw [hs₁_r, hs₁_i, hs₁_k, Nat.add_zero]; exact hr_le_i)
        (by rw [hs₁_i, hs₁_k, Nat.add_zero]; exact Nat.le_of_lt hi_lt)
        (by rw [hs₁_k]; exact Nat.zero_le _) hf_sb hf_zb hs_x
        (by rw [hs₁_i]; exact hz_prev) hm_fr
        (fun r h1 h2 h3 h4 h5 h6 h7 => by
          simp only [s₁, Data.set_regs, Function.update_of_ne h4]
          exact hr_fr r h1 h2 h3 h4 h5 h6 h7)
    rw [hs₁_i] at hz_i
    rw [hs₁_r] at hT_tail
    have hstep : ExecWithin w zBody x z (T_tail + 3) := by
      unfold zBody
      exact (ExecWithin.branch_neg hc_nir (hset_k.seq htail)).mono (by omega)
    have hz_r_le : z.regs regr ≤ s.length := hz_inv.r_le
    refine ⟨z, T_tail + 3, hstep, hz_inv, ?_⟩
    unfold zPotential
    rw [hz_i]
    clear hbox_lcp hz_prev
    omega

private theorem buildZNonempty_spec {w : ℕ} (s : List ℕ) (hs_pos : 0 < s.length)
    (x : Data 16)
    (hrx : ZBuildRegs (x.regs sBase) (x.regs zBase) s.length x)
    (hf_sb : Fits w (x.regs sBase + s.length))
    (hf_zb : Fits w (x.regs zBase + (s.length - 1)))
    (hs_holds : Block.HoldsList (x.regs sBase) s x.mem)
    (hdisj : x.regs sBase + s.length ≤ x.regs zBase) :
    ∃ y, ExecWithin w buildZNonempty x y (39 * s.length) ∧
      Block.HoldsList (x.regs zBase) (zFunction s) y.mem ∧
      (∀ a, (a < x.regs zBase ∨ x.regs zBase + s.length ≤ a) → y.mem a = x.mem a) ∧
      (∀ r : Fin 16,
        r ≠ regi → r ≠ regl → r ≠ regr → r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 →
          y.regs r = x.regs r) := by
  let sb := x.regs sBase
  let zb := x.regs zBase
  have hinit_ex : ∃ x₁ : Data 16,
      ExecWithin (B := .standard) w
        (ram[ *zBase ← sLen; regi ← one; regl ← zero; regr ← zero ]) x x₁ 4 ∧
      ZBuildRegs sb zb s.length x₁ ∧
      x₁.regs regi = 1 ∧ x₁.regs regl = 0 ∧ x₁.regs regr = 0 ∧
      x₁.mem = Function.update x.mem zb s.length ∧
      ∀ r : Fin 16, r ≠ regi → r ≠ regl → r ≠ regr → x₁.regs r = x.regs r := by
    refine WP.exists_execWithin ?_
    wram_exec [hrx.zero_eq, hrx.one_eq, hrx.zb_eq, hrx.len_eq]
    refine ⟨⟨by wram_simp [hrx.zero_eq], by wram_simp [hrx.one_eq], by wram_simp [sb, hrx.sb_eq],
      by wram_simp [zb, hrx.zb_eq], by wram_simp [hrx.len_eq]⟩,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp [zb], fun r h1 h2 h3 => ?_⟩
    simp only [Data.set_regs, Data.write_regs, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3]
  obtain ⟨x₁, hinit, hrx₁, hx₁_i, hx₁_l, hx₁_r, hx₁_mem, hx₁_fr⟩ := hinit_ex
  have hx₁_inv : ZInv s sb zb x x₁ := by
    refine ⟨hrx₁, by rw [hx₁_i], by rw [hx₁_i]; exact hs_pos,
      by rw [hx₁_l, hx₁_i]; exact Nat.zero_lt_one,
      by rw [hx₁_r]; exact Nat.zero_le _,
      Or.inl hx₁_r,
      by rw [hx₁_r]; exact Nat.zero_le _, ?_, ?_, ?_⟩
    · intro j hj
      rw [hx₁_i] at hj
      obtain rfl : j = 0 := by omega
      rw [hx₁_mem, Nat.add_zero, Function.update_self, List.drop_zero, List.lcpLen_self]
    · intro a ha
      rw [hx₁_mem, Function.update_of_ne (by omega)]
    · intro r h1 h2 h3 _ _ _ _
      exact hx₁_fr r h1 h2 h3
  obtain ⟨y, hloop, hy_inv, hstop⟩ := ExecWithin.loop_potential
    (cond := .lt regi sLen) (body := zBody) (ZInv s sb zb x) (zPotential s.length)
    (fun st hst hc => zBody_spec s sb zb x hf_sb hf_zb hs_holds hdisj st hst hc) hx₁_inv
  obtain ⟨hry, _, hy_i_le, _, _, _, _, hy_z, hy_mfr, hy_rfr⟩ := hy_inv
  have hy_i_eq : y.regs regi = s.length := by
    simp only [Cond.holds_lt, hry.len_eq] at hstop
    exact Nat.le_antisymm hy_i_le (Nat.not_lt.mp hstop)
  have hpot₁ : zPotential s.length x₁ = 10 * s.length + 29 * (s.length - 1) := by
    unfold zPotential
    rw [hx₁_r, hx₁_i, Nat.sub_zero]
  unfold buildZNonempty
  refine ⟨y, (hinit.seq hloop).mono (by rw [hpot₁]; omega), ?_, hy_mfr, hy_rfr⟩
  intro ⟨j, hj⟩
  have hj_len : j < s.length := by simpa only [length_zFunction] using hj
  change y.mem (zb + j) = (zFunction s)[j]'hj
  rw [hy_z j (hy_i_eq ▸ hj_len), getElem_zFunction]

/-- **Z-array construction on the word RAM.** Starting from `Data.init s` at any word width `w`
with `Fits w (2 * s.length + 1)`, `zCode` executes within `39 * s.length + 9` instructions and
writes `zFunction s` as the length-prefixed array at `y.regs Reg.out = s.length + 1`, preserving
the input block `[1, 1 + s.length)`. -/
theorem zCode_exec {w : ℕ} (s : List ℕ) (hw : Fits w (2 * s.length + 1)) :
    ∃ y, ExecWithin w zCode (Data.init s) y (39 * s.length + 9) ∧
      outputList y.mem (y.regs out) = zFunction s ∧
      y.regs out = s.length + 1 ∧
      Fits w (y.regs out + (zFunction s).length) ∧
      Block.HoldsList 1 s y.mem := by
  let x : Data 16 := Data.init s
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_m1 : Fits w (s.length + 1) := hw.of_le (by omega)
  have hsetup_ex : ∃ x₁, ExecWithin w (ram[
        zero ← #0;
        one ← #1;
        sLen ← *zero;
        sBase ← one;
        out ← sLen + one;
        *out ← sLen ]) x x₁ 6 ∧
      x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧ x₁.regs sLen = s.length ∧
      x₁.regs sBase = 1 ∧ x₁.regs out = s.length + 1 ∧
      x₁.mem = Function.update x.mem (s.length + 1) s.length := by
    refine WP.exists_execWithin ?_
    wram_exec [x, Data.init_regs, Data.init_mem_zero, hf_1, hf_m1]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₁, hsetup, hz₁, ho₁, hlen₁, hsb₁, hout₁, hmem₁⟩ := hsetup_ex
  have hs_init : Block.HoldsList 1 s x.mem := (outputList_eq_iff.mp (outputList_init s)).2
  have hs₁ : Block.HoldsList 1 s x₁.mem :=
    hs_init.frame fun a _ ha2 => by rw [hmem₁, Function.update_of_ne (by omega)]
  unfold zCode
  by_cases hs_pos : 0 < s.length
  · have hc : (Cond.lt zero sLen).Holds x₁ := by
      simp only [Cond.holds_lt, hz₁, hlen₁]
      exact hs_pos
    have hf_m2 : Fits w (s.length + 2) := hw.of_le (by omega)
    let x₂ := x₁.set zBase (s.length + 2)
    have hzb_step : ExecWithin w (ram[ zBase ← out + one ]) x₁ x₂ 1 := by
      have h := ExecWithin.bin (w := w) (f := .add) (d := zBase) (i := out) (j := one) (x := x₁)
        (by simpa only [BinOp.eval, hout₁, ho₁, Nat.add_assoc] using hf_m2)
      simpa only [x₂, BinOp.eval, hout₁, ho₁, Nat.add_assoc] using h
    have hx₂_sb : x₂.regs sBase = 1 := by simp +decide [x₂, hsb₁]
    have hx₂_zb : x₂.regs zBase = s.length + 2 := by simp +decide [x₂]
    have hrx₂ : ZBuildRegs (x₂.regs sBase) (x₂.regs zBase) s.length x₂ :=
      ⟨by simp +decide [x₂, hz₁], by simp +decide [x₂, ho₁], rfl, rfl,
       by simp +decide [x₂, hlen₁]⟩
    obtain ⟨y, hbuild, hy_z, hy_mfr, hy_rfr⟩ :=
      buildZNonempty_spec s hs_pos x₂ hrx₂
        (by rw [hx₂_sb]; exact hw.of_le (by omega))
        (by rw [hx₂_zb]; exact hw.of_le (by omega))
        (by rw [hx₂_sb]; exact hs₁)
        (by rw [hx₂_sb, hx₂_zb]; omega)
    rw [hx₂_zb] at hy_z hy_mfr
    have hy_out : y.regs out = s.length + 1 :=
      (hy_rfr out (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans (by simp +decide [x₂, hout₁])
    refine ⟨y, (hsetup.seq (ExecWithin.branch_pos hc (hzb_step.seq hbuild))).mono (by omega),
      ?_, hy_out,
      by rw [hy_out, length_zFunction]; exact hw.of_le (by omega),
      hs₁.frame fun a _ ha2 => hy_mfr a (Or.inl (by omega))⟩
    rw [hy_out, outputList_eq_iff]
    refine ⟨?_, hy_z⟩
    rw [hy_mfr (s.length + 1) (Or.inl (by omega))]
    simp only [x₂, Data.set_mem, hmem₁, Function.update_self, length_zFunction]
  · have hs0 : s.length = 0 := Nat.eq_zero_of_not_pos hs_pos
    have hnil : s = [] := List.eq_nil_of_length_eq_zero hs0
    subst hnil
    have hc : ¬(Cond.lt zero sLen).Holds x₁ := by
      simp only [Cond.holds_lt, hz₁, hlen₁, List.length_nil]
      exact Nat.lt_irrefl 0
    let y := x₁.set regk 0
    have hnoop : ExecWithin (B := .standard) w (ram[ regk ← zero ]) x₁ y 1 := by
      simpa only [y, hz₁] using ExecWithin.copy (B := .standard) (d := regk) (s := zero) (x := x₁)
    have hy_out : y.regs out = 1 := by simp +decide [y, hout₁]
    refine ⟨y, hsetup.seq (ExecWithin.branch_neg hc hnoop),
      ?_, hy_out,
      by rw [hy_out, length_zFunction, List.length_nil, Nat.add_zero]; exact hf_1, hs₁⟩
    rw [hy_out, outputList_eq_iff]
    exact ⟨by simp only [y, Data.set_mem, hmem₁, List.length_nil, Function.update_self,
      length_zFunction], Block.holdsList_nil _ _⟩

/-- `zProgram` computes `zFunction s` in `39 * |s| + 10` instructions on every fitting word array at
every word width fitting `2 * |s| + 1`. -/
theorem zProgram_computesListInTime :
    zProgram.ComputesListInTime (fun _ s => s) (fun s _ => 39 * s.length + 10)
      (fun s w => Fits w (2 * s.length + 1)) zFunction :=
  zCode.computesListInTime_program out fun s _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _⟩ := zCode_exec s hw
    exact ⟨y, hexec, hout, hfit⟩

/-! ## Execution of `matchCode` -/

private structure MatchRegs (I : MatchInput) (x : Data 16) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  pl_eq : x.regs patLen = I.pat.length
  tl_eq : x.regs txtLen = I.txt.length
  sb_eq : x.regs sBase = 3
  sl_eq : x.regs sLen = I.pat.length + I.txt.length
  zb_eq : x.regs zBase = 3 + I.pat.length + I.txt.length
  out_eq : x.regs out = 3 + 2 * (I.pat.length + I.txt.length)

private theorem MatchRegs.of_z_frame {I : MatchInput} {x y : Data 16}
    (hr : MatchRegs I x)
    (hfr : ∀ r : Fin 16,
      r ≠ regi → r ≠ regl → r ≠ regr → r ≠ regk → r ≠ go → r ≠ t0 → r ≠ t1 →
        y.regs r = x.regs r) :
    MatchRegs I y :=
  ⟨(hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.zero_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.one_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.pl_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.tl_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.sb_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.sl_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.zb_eq,
   (hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hr.out_eq⟩

private theorem init_matchEncode_blocks (I : MatchInput) :
    let x : Data 16 := Data.init I.encode
    x.mem 1 = I.pat.length ∧
      x.mem 2 = I.txt.length ∧
      Block.HoldsList 3 (I.pat ++ I.txt) x.mem ∧
      Block.HoldsList 3 I.pat x.mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt x.mem := by
  dsimp only
  have hm1 : (Data.init I.encode : Data 16).mem 1 = I.pat.length := by
    simpa only [MatchInput.encode, List.getD_cons_zero] using
      Data.init_mem_succ (r := 16) I.encode 0
  have hm2 : (Data.init I.encode : Data 16).mem 2 = I.txt.length := by
    simpa only [MatchInput.encode, List.getD_cons_succ, List.getD_cons_zero] using
      Data.init_mem_succ (r := 16) I.encode 1
  have hall : Block.HoldsList 3 (I.pat ++ I.txt) (Data.init I.encode : Data 16).mem := by
    have heq : I.encode = [I.pat.length, I.txt.length] ++ ((I.pat ++ I.txt) ++ []) := by
      simp only [MatchInput.encode, List.cons_append, List.nil_append, List.append_nil]
    rw [heq]
    exact Data.init_realizes_append [I.pat.length, I.txt.length] (I.pat ++ I.txt) []
  obtain ⟨hpat, htxt⟩ := Block.holdsList_append_iff.mp hall
  exact ⟨hm1, hm2, hall, hpat, htxt⟩

private theorem emptyMatchCode_spec {w : ℕ} (txt : List ℕ)
    (hw : Fits w (3 * txt.length + 4))
    (x : Data 16)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hn : x.regs txtLen = txt.length)
    (hout : x.regs out = 3 + 2 * txt.length)
    (htxt : Block.HoldsList 3 txt x.mem) :
    ∃ y, ExecWithin w emptyMatchCode x y (6 * txt.length + 11) ∧
      outputList y.mem (y.regs out) = zMatches [] txt ∧
      (zMatches ([] : List ℕ) txt).length = txt.length + 1 ∧
      y.regs out = 3 + 2 * txt.length ∧
      Block.HoldsList 3 txt y.mem := by
  let outAddr := 3 + 2 * txt.length
  have hf_n1 : Fits w (txt.length + 1) := hw.of_le (by omega)
  let x₀ := ((x.set t1 (txt.length + 1)).write outAddr (txt.length + 1)).set regi 0
  have hinit : ExecWithin w (ram[ t1 ← txtLen + one; *out ← t1; regi ← zero ]) x x₀ 3 := by
    have h1 : ExecWithin w (ram[ t1 ← txtLen + one ]) x (x.set t1 (txt.length + 1)) 1 := by
      simpa only [BinOp.eval, hn, ho] using ExecWithin.bin (f := .add) (d := t1) (i := txtLen)
        (j := one) (x := x) (by simpa only [BinOp.eval, hn, ho] using hf_n1)
    have h2 : ExecWithin (B := .standard) w (ram[ *out ← t1 ]) (x.set t1 (txt.length + 1))
        ((x.set t1 (txt.length + 1)).write outAddr (txt.length + 1)) 1 := by
      simpa only [outAddr, Data.set_regs, Function.update_self,
        Function.update_of_ne (show out ≠ t1 by decide), hout] using
        ExecWithin.store (B := .standard) (a := out) (s := t1) (x := x.set t1 (txt.length + 1))
    have h3 : ExecWithin (B := .standard) w (ram[ regi ← zero ])
        ((x.set t1 (txt.length + 1)).write outAddr (txt.length + 1)) x₀ 1 := by
      simpa only [x₀, Data.write_regs, Data.set_regs, hz,
        Function.update_of_ne (show zero ≠ t1 by decide)] using
        ExecWithin.copy (B := .standard) (d := regi) (s := zero)
          (x := (x.set t1 (txt.length + 1)).write outAddr (txt.length + 1))
    exact h1.seq (h2.seq h3)
  let P (j : ℕ) (s : Data 16) : Prop :=
    s.regs one = 1 ∧ s.regs out = outAddr ∧ s.regs t1 = txt.length + 1 ∧
      s.mem outAddr = txt.length + 1 ∧
      (∀ i < j, s.mem (outAddr + 1 + i) = i) ∧
      Block.HoldsList 3 txt s.mem
  have hx₀_P : P (x₀.regs regi) x₀ := by
    refine ⟨by simp +decide [x₀, ho], by simp +decide [x₀, outAddr, hout],
      by simp +decide [x₀],
      by simp only [x₀, Data.set_mem, Data.write_mem, Function.update_self],
      fun i hi => by simp +decide [x₀] at hi, ?_⟩
    exact htxt.frame fun a _ ha2 => by
      simp only [x₀, Data.set_mem, Data.write_mem, outAddr]
      rw [Function.update_of_ne (by omega)]
  have hbody (s : Data 16) (hs : P (s.regs regi) s) (hlt : s.regs regi < txt.length + 1) :
      ∃ z, ExecWithin w emptyMatchBody s z 4 ∧ P (s.regs regi + 1) z ∧
        z.regs regi = s.regs regi + 1 := by
    obtain ⟨so, sout, st1, shdr, svals, stxt⟩ := hs
    let j := s.regs regi
    have hf_o1 : Fits w (outAddr + 1) := hw.of_le (by simp only [outAddr]; omega)
    have hf_addr : Fits w (outAddr + 1 + j) := hw.of_le (by simp only [outAddr]; omega)
    have hf_j1 : Fits w (j + 1) := hw.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold emptyMatchBody
    wram_exec [so, sout, hf_o1, hf_addr, hf_j1]
    refine ⟨⟨by wram_simp [so], by wram_simp [sout], by wram_simp [st1], ?_, ?_, ?_⟩,
      by wram_simp⟩
    · wram_simp [outAddr, shdr]
    · intro i hi
      by_cases hij : i = j
      · subst hij
        wram_simp [outAddr, j]
      · wram_simp [outAddr]
        exact svals i (by omega)
    · exact stxt.frame fun a _ ha2 => by wram_simp [outAddr]
  have hx₀_idx : x₀.regs regi = 0 := by simp +decide [x₀]
  obtain ⟨y, hloop, ⟨_, hy_out, _, hy_hdr, hy_vals, hy_txt⟩, _⟩ :=
    ExecWithin.loop_count P (fun _ hs => hs.2.2.1) hbody (by rw [hx₀_idx]; omega) hx₀_P
  rw [hx₀_idx] at hloop
  have hzmatches_nil : zMatches ([] : List ℕ) txt = List.range (txt.length + 1) := by
    rw [zMatches_eq_filter_range]
    simp only [List.nil_prefix, decide_true, List.filter_true]
  unfold emptyMatchCode
  refine ⟨y, (hinit.seq hloop).mono (by omega), ?_,
    by rw [hzmatches_nil, List.length_range], hy_out, hy_txt⟩
  rw [hy_out, hzmatches_nil, outputList_eq_iff]
  refine ⟨by rw [hy_hdr, List.length_range], fun i => ?_⟩
  have hi : i.val < txt.length + 1 := by simpa only [List.length_range] using i.isLt
  change y.mem (outAddr + 1 + i.val) = (List.range (txt.length + 1))[i.val]
  rw [hy_vals i.val hi, List.getElem_range]

private structure FilterInv (I : MatchInput) (s : Data 16) : Prop where
  regs_ok : MatchRegs I s
  oc_le : s.regs outCnt ≤ s.regs regi
  pat_holds : Block.HoldsList 3 I.pat s.mem
  txt_holds : Block.HoldsList (3 + I.pat.length) I.txt s.mem
  z_holds : Block.HoldsList (3 + I.pat.length + I.txt.length) (zFunction (I.pat ++ I.txt)) s.mem
  matches_ex : ∃ ms : List ℕ, s.regs outCnt = ms.length ∧
    Block.HoldsList (3 + 2 * (I.pat.length + I.txt.length) + 1) ms s.mem ∧
    ms.Pairwise (· < ·) ∧
    (∀ sh, sh ∈ ms ↔ sh < s.regs regi ∧ I.pat <+: I.txt.drop sh)

private theorem filterBody_spec {w : ℕ} (I : MatchInput)
    (hw : Fits w (2 * I.pat.length + 3 * I.txt.length + 4))
    (s : Data 16) (hs : FilterInv I s) (hlt : s.regs regi < I.txt.length) :
    ∃ z, ExecWithin w filterBody s z 9 ∧
      FilterInv I z ∧
      z.regs regi = s.regs regi + 1 := by
  obtain ⟨hrs, hoc_le, spat, stxt, sz, ⟨ms, soc_ms, sms_holds, sms_pw, sms_mem⟩⟩ := hs
  let j := s.regs regi
  have hmj_lt : I.pat.length + j < (zFunction (I.pat ++ I.txt)).length := by
    rw [length_zFunction, List.length_append]
    omega
  have hread_z : s.mem (3 + I.pat.length + I.txt.length + (I.pat.length + j)) =
      List.lcpLen (I.pat ++ I.txt) (I.txt.drop j) := by
    have h1 := sz.get (I.pat.length + j) hmj_lt
    rw [getElem_zFunction, List.drop_append,
      List.drop_eq_nil_of_le (Nat.le_add_right I.pat.length j), List.nil_append,
      Nat.add_sub_cancel_left] at h1
    exact h1
  have hf_mj : Fits w (I.pat.length + j) := hw.of_le (by omega)
  have hf_zbmj : Fits w (3 + I.pat.length + I.txt.length + (I.pat.length + j)) :=
    hw.of_le (by omega)
  have hf_j1 : Fits w (j + 1) := hw.of_le (by omega)
  let zv := List.lcpLen (I.pat ++ I.txt) (I.txt.drop j)
  by_cases hlt_p : zv < I.pat.length
  · have hnot_pref : ¬(I.pat <+: I.txt.drop j) := by
      intro hp_pref
      exact Nat.not_le.mpr hlt_p (List.length_le_lcpLen_append_iff.mpr hp_pref)
    have hstep_ex : ∃ z, ExecWithin w filterBody s z 5 ∧
        MatchRegs I z ∧
        z.regs regi = j + 1 ∧
        z.regs outCnt = s.regs outCnt ∧
        z.mem = s.mem := by
      refine WP.exists_execWithin ?_
      unfold filterBody
      wram_exec [hrs.one_eq, hrs.pl_eq, hrs.zb_eq, hread_z, hlt_p, hf_mj, hf_zbmj, hf_j1]
      exact ⟨⟨by wram_simp [hrs.zero_eq], by wram_simp [hrs.one_eq], by wram_simp [hrs.pl_eq],
        by wram_simp [hrs.tl_eq], by wram_simp [hrs.sb_eq], by wram_simp [hrs.sl_eq],
        by wram_simp [hrs.zb_eq], by wram_simp [hrs.out_eq]⟩,
        by wram_simp [j], by wram_simp, rfl⟩
    obtain ⟨z, hstep, hrz, hz_i, hz_oc, hz_mem⟩ := hstep_ex
    refine ⟨z, hstep.mono (by decide : 5 ≤ 9), ?_, hz_i⟩
    refine ⟨hrz, by rw [hz_oc, hz_i]; exact Nat.le_succ_of_le hoc_le,
      hz_mem ▸ spat, hz_mem ▸ stxt, hz_mem ▸ sz,
      ⟨ms, hz_oc.trans soc_ms, hz_mem ▸ sms_holds, sms_pw, fun sh => ?_⟩⟩
    rw [hz_i, sms_mem]
    constructor
    · rintro ⟨hsh, hp_sh⟩
      exact ⟨Nat.lt_succ_of_lt hsh, hp_sh⟩
    · rintro ⟨hsh, hp_sh⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hsh) with hlt_j | rfl
      · exact ⟨hlt_j, hp_sh⟩
      · exact absurd hp_sh hnot_pref
  · have hpref_here : I.pat <+: I.txt.drop j :=
      List.length_le_lcpLen_append_iff.mp (Nat.not_lt.mp hlt_p)
    have hf_oc1 : Fits w (s.regs outCnt + 1) :=
      hw.of_le (by clear sms_mem hpref_here hread_z; omega)
    have hf_out_oc : Fits w (3 + 2 * (I.pat.length + I.txt.length) + (s.regs outCnt + 1)) :=
      hw.of_le (by clear sms_mem hpref_here hread_z; omega)
    have hstep_ex : ∃ z, ExecWithin w filterBody s z 9 ∧
        MatchRegs I z ∧
        z.regs regi = j + 1 ∧
        z.regs outCnt = s.regs outCnt + 1 ∧
        z.mem = Function.update s.mem
          (3 + 2 * (I.pat.length + I.txt.length) + 1 + ms.length) j := by
      refine WP.exists_execWithin ?_
      unfold filterBody
      wram_exec [hrs.one_eq, hrs.pl_eq, hrs.zb_eq, hrs.out_eq, hread_z, hlt_p,
        hf_mj, hf_zbmj, hf_j1, hf_oc1, hf_out_oc]
      refine ⟨⟨by wram_simp [hrs.zero_eq], by wram_simp [hrs.one_eq], by wram_simp [hrs.pl_eq],
        by wram_simp [hrs.tl_eq], by wram_simp [hrs.sb_eq], by wram_simp [hrs.sl_eq],
        by wram_simp [hrs.zb_eq], by wram_simp [hrs.out_eq]⟩,
        by wram_simp [j], by wram_simp, ?_⟩
      wram_simp [soc_ms, j]
      congr 1
      clear sms_mem hpref_here hread_z hlt_p
      omega
    obtain ⟨z, hstep, hrz, hz_i, hz_oc, hz_mem⟩ := hstep_ex
    refine ⟨z, hstep, ?_, hz_i⟩
    refine ⟨hrz, by rw [hz_oc, hz_i]; exact Nat.add_le_add_right hoc_le 1, ?_, ?_, ?_,
      ⟨ms ++ [j], ?_, ?_, ?_, ?_⟩⟩
    · exact spat.frame fun a _ ha2 => by
        rw [hz_mem, Function.update_of_ne]
        clear sms_mem hpref_here hread_z hlt_p; omega
    · exact stxt.frame fun a _ ha2 => by
        rw [hz_mem, Function.update_of_ne]
        clear sms_mem hpref_here hread_z hlt_p; omega
    · exact sz.frame fun a _ ha2 => by
        rw [length_zFunction, List.length_append] at ha2
        rw [hz_mem, Function.update_of_ne]
        clear sms_mem hpref_here hread_z hlt_p; omega
    · rw [hz_oc, soc_ms, List.length_append, List.length_singleton]
    · rw [hz_mem]
      exact sms_holds.append_one j
    · rw [List.pairwise_append]
      refine ⟨sms_pw, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      exact ((sms_mem a).mp ha).1
    · intro sh
      rw [hz_i, List.mem_append, List.mem_singleton, sms_mem]
      constructor
      · rintro (⟨hlt_j, hp_sh⟩ | rfl)
        · exact ⟨Nat.lt_succ_of_lt hlt_j, hp_sh⟩
        · exact ⟨Nat.lt_succ_self _, hpref_here⟩
      · rintro ⟨hsh, hp_sh⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hsh) with hlt_j | rfl
        · exact Or.inl ⟨hlt_j, hp_sh⟩
        · exact Or.inr rfl

private theorem nonemptyMatchCode_spec {w : ℕ} (I : MatchInput) (hp : 0 < I.pat.length)
    (hw : Fits w (2 * I.pat.length + 3 * I.txt.length + 4))
    (x : Data 16) (hrx : MatchRegs I x)
    (hall : Block.HoldsList 3 (I.pat ++ I.txt) x.mem)
    (hpat : Block.HoldsList 3 I.pat x.mem)
    (htxt : Block.HoldsList (3 + I.pat.length) I.txt x.mem) :
    ∃ y, ExecWithin w nonemptyMatchCode x y (39 * I.pat.length + 50 * I.txt.length + 5) ∧
      outputList y.mem (y.regs out) = zMatches I.pat I.txt ∧
      (zMatches I.pat I.txt).length ≤ I.txt.length ∧
      y.regs out = 3 + 2 * (I.pat.length + I.txt.length) ∧
      Block.HoldsList 3 I.pat y.mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt y.mem := by
  have hs_pos : 0 < (I.pat ++ I.txt).length := by rw [List.length_append]; omega
  have hrz_x : ZBuildRegs (x.regs sBase) (x.regs zBase) (I.pat ++ I.txt).length x :=
    ⟨hrx.zero_eq, hrx.one_eq, rfl, rfl, by rw [hrx.sl_eq, List.length_append]⟩
  obtain ⟨y₁, hbuild, hy₁_z, hy₁_mfr, hy₁_rfr⟩ :=
    buildZNonempty_spec (I.pat ++ I.txt) hs_pos x hrz_x
      (by rw [hrx.sb_eq, List.length_append]; exact hw.of_le (by omega))
      (by rw [hrx.zb_eq, List.length_append]; exact hw.of_le (by omega))
      (by rw [hrx.sb_eq]; exact hall)
      (by rw [hrx.sb_eq, hrx.zb_eq, List.length_append]; omega)
  rw [hrx.zb_eq, List.length_append] at hy₁_mfr
  rw [hrx.zb_eq] at hy₁_z
  rw [List.length_append] at hbuild
  have hry₁ : MatchRegs I y₁ := hrx.of_z_frame hy₁_rfr
  have hpat₁ : Block.HoldsList 3 I.pat y₁.mem :=
    hpat.frame fun a _ ha2 => hy₁_mfr a (Or.inl (by omega))
  have htxt₁ : Block.HoldsList (3 + I.pat.length) I.txt y₁.mem :=
    htxt.frame fun a _ ha2 => hy₁_mfr a (Or.inl (by omega))
  have hprep_ex : ∃ y₂ : Data 16,
      ExecWithin (B := .standard) w (ram[ outCnt ← zero; regi ← zero ]) y₁ y₂ 2 ∧
      MatchRegs I y₂ ∧ y₂.regs outCnt = 0 ∧ y₂.regs regi = 0 ∧ y₂.mem = y₁.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hry₁.zero_eq]
    exact ⟨⟨by wram_simp [hry₁.zero_eq], by wram_simp [hry₁.one_eq], by wram_simp [hry₁.pl_eq],
      by wram_simp [hry₁.tl_eq], by wram_simp [hry₁.sb_eq], by wram_simp [hry₁.sl_eq],
      by wram_simp [hry₁.zb_eq], by wram_simp [hry₁.out_eq]⟩,
      by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₂, hprep, hry₂, hy₂_oc, hy₂_i, hy₂_mem⟩ := hprep_ex
  let P (j : ℕ) (st : Data 16) : Prop := FilterInv I st ∧ st.regs regi = j
  have hy₂_P : P (y₂.regs regi) y₂ := by
    refine ⟨⟨hry₂, by rw [hy₂_oc, hy₂_i], hy₂_mem ▸ hpat₁, hy₂_mem ▸ htxt₁, hy₂_mem ▸ hy₁_z,
      ⟨[], hy₂_oc, Block.holdsList_nil _ _, List.Pairwise.nil, fun sh => ?_⟩⟩, rfl⟩
    rw [hy₂_i]
    simp only [List.not_mem_nil, Nat.not_lt_zero, false_and]
  obtain ⟨y₃, hloop, ⟨⟨hry₃, hy₃_oc_le, hy₃_pat, hy₃_txt, _,
    ⟨ms, hy₃_oc, hy₃_ms_holds, hy₃_ms_pw, hy₃_ms_mem⟩⟩, hy₃_i_eq⟩, _⟩ :=
    ExecWithin.loop_count P (fun _ hst => hst.1.regs_ok.tl_eq)
      (fun st ⟨hst, _⟩ hlt => by
        obtain ⟨z, hz_exec, hz_inv, hz_i⟩ := filterBody_spec I hw st hst hlt
        exact ⟨z, hz_exec, ⟨hz_inv, hz_i⟩, hz_i⟩)
      (by rw [hy₂_i]; exact Nat.zero_le _) hy₂_P
  rw [hy₂_i, Nat.sub_zero] at hloop
  rw [hy₃_i_eq] at hy₃_oc_le hy₃_ms_mem
  have hms_eq : ms = zMatches I.pat I.txt := by
    refine hy₃_ms_pw.eq_of_mem_iff (pairwise_lt_zMatches I.pat I.txt) fun sh => ?_
    rw [hy₃_ms_mem, mem_zMatches_iff]
    refine ⟨fun ⟨hlt, hpr⟩ => ⟨Nat.le_of_lt hlt, hpr⟩, fun ⟨hle, hpr⟩ => ⟨?_, hpr⟩⟩
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · exact hlt
    · exfalso
      rw [List.drop_length, List.prefix_nil] at hpr
      rw [hpr, List.length_nil] at hp
      exact Nat.lt_irrefl 0 hp
  let outAddr := 3 + 2 * (I.pat.length + I.txt.length)
  let y := y₃.write outAddr (y₃.regs outCnt)
  have hfin : ExecWithin (B := .standard) w (ram[ *out ← outCnt ]) y₃ y 1 := by
    simpa only [y, hry₃.out_eq] using ExecWithin.store (B := .standard) (a := out) (s := outCnt)
      (x := y₃)
  have htotal_time : 39 * (I.pat.length + I.txt.length) +
      (2 + (I.txt.length * (9 + 2) + 2 + 1)) ≤ 39 * I.pat.length + 50 * I.txt.length + 5 := by
    clear hy₃_ms_mem hms_eq
    omega
  unfold nonemptyMatchCode
  refine ⟨y, (hbuild.seq (hprep.seq (hloop.seq hfin))).mono htotal_time,
    ?_, by rw [← hms_eq, ← hy₃_oc]; exact hy₃_oc_le, by simp +decide [y, hry₃.out_eq], ?_, ?_⟩
  · simp only [y, Data.write_regs, hry₃.out_eq]
    rw [← hms_eq, outputList_eq_iff]
    refine ⟨by simp only [Data.write_mem, outAddr, Function.update_self, hy₃_oc], ?_⟩
    exact hy₃_ms_holds.frame fun a ha1 _ => by
      simp only [Data.write_mem, outAddr]
      rw [Function.update_of_ne]
      clear hy₃_ms_mem hms_eq; omega
  · exact hy₃_pat.frame fun a _ ha2 => by
      simp only [y, Data.write_mem, outAddr]
      rw [Function.update_of_ne]
      clear hy₃_ms_mem hms_eq; omega
  · exact hy₃_txt.frame fun a _ ha2 => by
      simp only [y, Data.write_mem, outAddr]
      rw [Function.update_of_ne]
      clear hy₃_ms_mem hms_eq; omega

/-- **End-to-end Z-algorithm exact pattern matching on the word RAM.** Starting from
`Data.init I.encode` at any word width `w` with `Fits w (2 * I.pat.length + 3 * I.txt.length + 4)`,
`matchCode` executes within `39 * I.pat.length + 50 * I.txt.length + 22` instructions and writes
`zMatches I.pat I.txt` as the length-prefixed array at
`y.regs Reg.out = 3 + 2 * (I.pat.length + I.txt.length)`, preserving the pattern and text blocks at
`[3, 3 + I.pat.length)` and `[3 + I.pat.length, 3 + I.pat.length + I.txt.length)`. -/
theorem matchCode_exec {w : ℕ} (I : MatchInput)
    (hw : Fits w (2 * I.pat.length + 3 * I.txt.length + 4)) :
    ∃ y, ExecWithin w matchCode (Data.init I.encode) y
        (39 * I.pat.length + 50 * I.txt.length + 22) ∧
      outputList y.mem (y.regs out) = zMatches I.pat I.txt ∧
      y.regs out = 3 + 2 * (I.pat.length + I.txt.length) ∧
      Fits w (y.regs out + (zMatches I.pat I.txt).length) ∧
      Block.HoldsList 3 I.pat y.mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt y.mem := by
  let x : Data 16 := Data.init I.encode
  obtain ⟨hm1, hm2, hall, hpat, htxt⟩ := init_matchEncode_blocks I
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_2 : Fits w 2 := hw.of_le (by omega)
  have hf_3 : Fits w 3 := hw.of_le (by omega)
  have hf_sl : Fits w (I.pat.length + I.txt.length) := hw.of_le (by omega)
  have hf_zb : Fits w (3 + (I.pat.length + I.txt.length)) := hw.of_le (by omega)
  have hf_out : Fits w (3 + (I.pat.length + I.txt.length) + (I.pat.length + I.txt.length)) :=
    hw.of_le (by omega)
  have hsetup_ex : ∃ x₁, ExecWithin w matchSetup x x₁ 9 ∧
      MatchRegs I x₁ ∧ x₁.mem = x.mem := by
    refine WP.exists_execWithin ?_
    unfold matchSetup
    wram_exec [x, Data.init_regs, hm1, hm2, hf_1, hf_2, hf_3, hf_sl, hf_zb, hf_out]
    exact ⟨⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp; omega, by wram_simp; omega⟩, rfl⟩
  obtain ⟨x₁, hsetup, hrx₁, hmem₁⟩ := hsetup_ex
  unfold matchCode
  by_cases hp : 0 < I.pat.length
  · have hc : (Cond.lt zero patLen).Holds x₁ := by
      simp only [Cond.holds_lt, hrx₁.zero_eq, hrx₁.pl_eq]
      exact hp
    obtain ⟨y, hne, hy_out_list, hlen_le, hy_out, hy_pat, hy_txt⟩ :=
      nonemptyMatchCode_spec I hp hw x₁ hrx₁ (hmem₁ ▸ hall) (hmem₁ ▸ hpat) (hmem₁ ▸ htxt)
    have hfit_out : Fits w (y.regs out + (zMatches I.pat I.txt).length) := by
      rw [hy_out]
      refine hw.of_le (Nat.le_trans (Nat.add_le_add_left hlen_le _) ?_)
      clear hlen_le hy_out_list; omega
    refine ⟨y, (hsetup.seq (ExecWithin.branch_pos hc hne)).mono
      (by clear hlen_le hy_out_list hfit_out; omega),
      hy_out_list, hy_out, hfit_out, hy_pat, hy_txt⟩
  · have hp0 : I.pat.length = 0 := Nat.eq_zero_of_not_pos hp
    have hpnil : I.pat = [] := List.eq_nil_of_length_eq_zero hp0
    have hc : ¬(Cond.lt zero patLen).Holds x₁ := by
      simp only [Cond.holds_lt, hrx₁.zero_eq, hrx₁.pl_eq, hp0]
      exact Nat.lt_irrefl 0
    have htxt0 : Block.HoldsList 3 I.txt x₁.mem := by
      rw [hmem₁]
      simpa only [hp0, Nat.add_zero] using htxt
    obtain ⟨y, hemp, hy_out_list, hlen_eq, hy_out, hy_txt⟩ :=
      emptyMatchCode_spec I.txt (hw.of_le (by omega)) x₁ hrx₁.zero_eq hrx₁.one_eq hrx₁.tl_eq
        (by rw [hrx₁.out_eq, hp0, Nat.zero_add]) htxt0
    rw [← hpnil] at hy_out_list hlen_eq
    have hy_out' : y.regs out = 3 + 2 * (I.pat.length + I.txt.length) := by
      rw [hy_out, hp0, Nat.zero_add]
    have hy_pat : Block.HoldsList 3 I.pat y.mem := by
      rw [hpnil]
      exact Block.holdsList_nil _ _
    have hy_txt' : Block.HoldsList (3 + I.pat.length) I.txt y.mem := by
      simpa only [hp0, Nat.add_zero] using hy_txt
    have hfit_out : Fits w (y.regs out + (zMatches I.pat I.txt).length) := by
      rw [hy_out', hlen_eq]
      exact hw.of_le (by clear hlen_eq hy_out_list; omega)
    refine ⟨y, (hsetup.seq (ExecWithin.branch_neg hc hemp)).mono
      (by clear hlen_eq hy_out_list hfit_out; omega),
      hy_out_list, hy_out', hfit_out, hy_pat, hy_txt'⟩

/-- `matchProgram` computes `zMatches I.pat I.txt` in `39 * |I.pat| + 50 * |I.txt| + 23`
instructions on every fitting `MatchInput` at every word width fitting
`2 * |I.pat| + 3 * |I.txt| + 4`. -/
theorem matchProgram_computesListInTime :
    matchProgram.ComputesListInTime (fun _ (I : MatchInput) => I.encode)
      (fun I _ => 39 * I.pat.length + 50 * I.txt.length + 23)
      (fun I w => Fits w (2 * I.pat.length + 3 * I.txt.length + 4))
      (fun I => zMatches I.pat I.txt) :=
  matchCode.computesListInTime_program out fun I _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _, _⟩ := matchCode_exec I hw
    exact ⟨y, hexec, hout, hfit⟩

/-- `matchProgram` computes `KMP.kmpMatchesList I.pat I.txt` in `39 * |I.pat| + 50 * |I.txt| + 23`
instructions on every fitting `MatchInput` at every word width fitting
`2 * |I.pat| + 3 * |I.txt| + 4`. -/
theorem matchProgram_computesKmpMatchesInTime :
    matchProgram.ComputesListInTime (fun _ (I : MatchInput) => I.encode)
      (fun I _ => 39 * I.pat.length + 50 * I.txt.length + 23)
      (fun I w => Fits w (2 * I.pat.length + 3 * I.txt.length + 4))
      (fun I => KMP.kmpMatchesList I.pat I.txt) := by
  simpa only [funext fun I : MatchInput => zMatches_eq_kmpMatchesList I.pat I.txt] using
    matchProgram_computesListInTime

end Cslib.Algorithms.WordRAM.ZFunction
