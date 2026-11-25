/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Create

/-!
# The move of a track

The phases of the move of track `i` of the Hennie–Stearns machine put together: from the scan to
the next state, the machine performs `ZTrack.move` on track `i` (`runFrom_op`), in time
`O(2 ^ j)` for the level `j` of the move (`opTime_le`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}
  (tm : MultiTapeTM k Symbol State) (q : State) (mv : Fin k → SignType) (i : Fin k)
  (p : Fin (input.length + 2)) (out : List (HSym k Symbol))

lemma readA_encA_zero (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) :
    readA (encA Z J tg 0) = some (centerCell Z) := by
  simp [encA, aCell, readA]

lemma center_readA_encA (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) {n : ℕ} (hn : 1 ≤ n)
    (c : ACell k Symbol) (hc : readA (encA Z J tg n) = some c) : c.center = false := by
  rw [readA_encA_nat, aCell] at hc
  simp only [show n ≠ 0 by omega, ↓reduceIte] at hc
  split_ifs at hc
  cases hc
  rfl

/-- **Walking home** on both work tapes. -/
lemma runFrom_return (nx : Next) (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ)
    (src dst : List (Option Symbol)) (m r : ℕ) :
    (hennieStearns tm).runFrom (C q mv i p out (.back nx) (encA Z J tg) (encB src dst) m r)
        (m + 1 + (r + 1)) =
      hcfg (some (nextState q mv i nx)) p (encA Z J tg) (encB src dst) 0 1 out :=
  runFrom_trans tm
    (runFrom_back (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) nx _ _ m r
      ⟨_, readA_encA_zero Z J tg, rfl⟩ fun _ hn _ c hc => center_readA_encA Z J tg hn c hc)
    (runFrom_backB (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) nx _ _ 0 r rfl
      fun u hu _ => by rw [readB_encB_pos _ _ (by omega)]; rfl)

/-- The time of a move at level `j` with gathered lists of lengths `d` and `s`. -/
def moveTime (j d s : ℕ) : ℕ :=
  (zs j + 1) + (zs j - 1 + 1 + (1 + 1)) + (zs (j + 1) + 1) + (zs (j + 1) - 1 + 1 + (d + 1 + 1)) +
    (zs (j + 1) + 1) + (zs (j + 1) - 1 + 1 + (s + 1 + 1)) + (zs (j + 1) + 1) +
    (zs (j + 1) - 1 + 1 + (s + 1 + 1)) + (zs (j + 1) + 1) + (zs (j + 1) - 1 + 1 + (d + 1 + 1))

/-- **A move at a created level.** -/
lemma runFrom_move (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : (Z i).Valid J)
    (hj : (Z i).trig J (srcSide mv i) < J) :
    (hennieStearns tm).runFrom (C q mv i p out .scan (encA Z J none) (encB [] []) 0 1)
        (moveTime ((Z i).trig J (srcSide mv i))
          ((Z i).center :: (List.range ((Z i).trig J (srcSide mv i) + 1)).flatMap
            ((Z i).zone (srcSide mv i).other)).length
          ((Z i).zone (srcSide mv i) ((Z i).trig J (srcSide mv i))).length) =
      hcfg (some (afterOp q mv i)) p
        (encA (Function.update Z i ((Z i).move J (srcSide mv i))) J none) (encB [] []) 0 1
        out := by
  set s := srcSide mv i
  set j := (Z i).trig J s with hjdef
  set D := (Z i).center :: (List.range (j + 1)).flatMap ((Z i).zone s.other)
  set S := (Z i).zone s j
  have h1 := one_le_zs j
  have h2 := one_le_zs (j + 1)
  have hcast : ∀ n : ℕ, 1 ≤ n → (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := fun n hn => by omega
  have hcast' : ∀ n : ℕ, (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := fun n => by push_cast; rfl
  have e1 := runFrom_scan (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) Z hV hj
    (encB [] []) 1
  rw [hcast _ h1] at e1
  have e2 := runFrom_return tm q mv i p out .gatherD Z J (some j) [] [] (zs j - 1) 1
  have e3 := runFrom_gatherD tm q mv i p out Z hV hj
  rw [hcast _ h2, hcast'] at e3
  have e4 := runFrom_return tm q mv i p out .gatherS Z J (some j) [] D (zs (j + 1) - 1)
    (D.length + 1)
  have e5 := runFrom_gatherS tm q mv i p out Z hV hj D
  rw [hcast _ h2, hcast', ZTrack.flatMap_zone_trig hV] at e5
  have e6 := runFrom_return tm q mv i p out .writeS Z J (some j) S D (zs (j + 1) - 1)
    (S.length + 1)
  have e7 := runFrom_writeS tm q mv i p out Z hV hj D
  rw [hcast _ h2, hcast'] at e7
  have e8 := runFrom_return tm q mv i p out .writeD
    (Function.update Z i ((Z i).withSide ((Z i).move J s) s)) J (some j) [] D (zs (j + 1) - 1)
    (S.length + 1)
  have e9 := runFrom_writeD tm q mv i p out Z hV hj
  rw [hcast _ h2, hcast'] at e9
  have e10 := runFrom_return tm q mv i p out .done (Function.update Z i ((Z i).move J s)) J none
    [] [] (zs (j + 1) - 1) (D.length + 1)
  exact runFrom_trans tm (runFrom_trans tm (runFrom_trans tm (runFrom_trans tm (runFrom_trans tm
    (runFrom_trans tm (runFrom_trans tm (runFrom_trans tm (runFrom_trans tm e1 e2) e3) e4) e5)
    e6) e7) e8) e9) e10

/-- The move does not depend on the number of created levels. -/
lemma ZTrack.move_mono {Y : ZTrack Symbol} {J J' : ℕ} (hV : Y.Valid J) (hJ : J ≤ J') (s : Side) :
    Y.move J' s = Y.move J s := by
  simp only [ZTrack.move, ZTrack.trig_mono hV hJ]

/-- The number of created levels after a move to side `s`. -/
def opLevels (Y : ZTrack Symbol) (J : ℕ) (s : Side) : ℕ := if Y.trig J s = J then J + 1 else J

/-- The time of a move to side `s`. -/
def opTime (Y : ZTrack Symbol) (J : ℕ) (s : Side) : ℕ :=
  (if Y.trig J s = J then createTime J else 0) +
    moveTime (Y.trig J s)
      (Y.center :: (List.range (Y.trig J s + 1)).flatMap (Y.zone s.other)).length
      (Y.zone s (Y.trig J s)).length

/-- **The move of track `i`.** From the scan, the machine performs the move of track `i`, creating
a level first if needed, and goes on to the next state. -/
lemma runFrom_op (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : ∀ i', (Z i').Valid J) :
    (hennieStearns tm).runFrom (C q mv i p out .scan (encA Z J none) (encB [] []) 0 1)
        (opTime (Z i) J (srcSide mv i)) =
      hcfg (some (afterOp q mv i)) p
        (encA (Function.update Z i ((Z i).move J (srcSide mv i))) (opLevels (Z i) J (srcSide mv i))
          none) (encB [] []) 0 1 out := by
  set s := srcSide mv i
  rcases Nat.lt_or_ge ((Z i).trig J s) J with hj | hj
  · simp only [opTime, opLevels, show (Z i).trig J s ≠ J by omega, ↓reduceIte, zero_add]
    exact runFrom_move tm q mv i p out Z (hV i) hj
  · have hjJ : (Z i).trig J s = J := le_antisymm (ZTrack.trig_le (hV i) s) hj
    simp only [opTime, opLevels, hjJ, ↓reduceIte]
    have hV' : (Z i).Valid (J + 1) := (hV i).mono (Nat.le_succ J)
    have htr := ZTrack.trig_mono (hV i) (Nat.le_succ J) s
    have e := runFrom_move tm q mv i p out Z hV' (by rw [htr, hjJ]; omega)
    rw [htr, hjJ, ZTrack.move_mono (hV i) (Nat.le_succ J)] at e
    exact runFrom_trans tm (runFrom_create tm q mv i p out Z hV hjJ) e

/-- **A move takes time `O(2 ^ j)`** at level `j`. -/
lemma opTime_le {Y : ZTrack Symbol} {J : ℕ} (hV : Y.Valid J) (s : Side) :
    opTime Y J s ≤ 80 * 2 ^ Y.trig J s := by
  have hD := ZTrack.length_dst hV s
  have hO := ZTrack.length_zone_other_trig hV s
  have hS := hV.length s (Y.trig J s)
  have hle := ZTrack.trig_le hV s
  simp only [opTime, moveTime, createTime, zs]
  rw [hD]
  generalize ht : Y.trig J s = j at *
  have hp : 2 ^ (j + 1 + 1) = 4 * 2 ^ j := by rw [pow_succ, pow_succ]; omega
  have hp' : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
  have hpos := Nat.one_le_two_pow (n := j)
  split_ifs with h
  · subst h
    rcases hO with h | h <;> rcases hS with h' | h' | h' <;> simp only [h, h', hp, hp'] <;> omega
  · rcases hO with h | h <;> rcases hS with h' | h' | h' <;> simp only [h, h', hp, hp'] <;> omega

end Turing.MultiTapeTM.HennieStearns
