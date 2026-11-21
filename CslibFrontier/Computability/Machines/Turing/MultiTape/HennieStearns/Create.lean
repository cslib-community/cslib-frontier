/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Write
import Mathlib.Tactic.Ring

/-!
# Creating a zone

When no created zone holds a symbol on the side of a move, the Hennie–Stearns machine creates
zone `J`, half full of blanks: walking from the end of the created zones to the center, it lays a
ruler of `2 ^ (J + 1)` marks on work tape `1`, with the middle marked (`runFrom_cr₁`); it then
walks to the end of the created zones (`runFrom_crWalk`) and, reading the ruler back, writes the
cells of zone `J` (`runFrom_cr₃`). `runFrom_create` puts the phases together.
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}
  (tm : MultiTapeTM k Symbol State) (q : State) (mv : Fin k → SignType) (i : Fin k)
  (p : Fin (input.length + 2)) (out : List (HSym k Symbol))

/-! ### The ruler -/

/-- A cell of the ruler, `outer` for the first cell of the outer half of the new zone. -/
def rulerCell (outer : Bool) : BCell Symbol := { BCell.empty with mark := true, outer := outer }

/-- Work tape `1` holding the cells `c + 1, …, n` of a ruler whose outer half starts at cell
`w`. -/
def encR (c n w : ℕ) : ℤ → Option (HSym k Symbol) :=
  fun z => if z = 0 then some (.inr (.inr homeCell))
    else if c < z.toNat ∧ z.toNat ≤ n then some (.inr (.inr (rulerCell (decide (z.toNat = w)))))
    else none

lemma encR_of_le {c n : ℕ} (w : ℕ) (h : n ≤ c) : encR (k := k) (Symbol := Symbol) c n w =
    encB [] [] := by
  funext z
  simp only [encR, encB]
  split_ifs with h₀ h₁ h₂ <;> first | rfl | omega

lemma readB_encR_zero (c n w : ℕ) :
    readB (encR (k := k) (Symbol := Symbol) c n w 0) = homeCell := rfl

lemma readB_encR_pos (c n w : ℕ) {z : ℤ} (hz : 0 < z) :
    readB (encR (k := k) (Symbol := Symbol) c n w z) =
      if c < z.toNat ∧ z.toNat ≤ n then rulerCell (decide (z.toNat = w)) else BCell.empty := by
  simp only [encR, show z ≠ 0 by omega, ↓reduceIte]
  split_ifs <;> rfl

lemma home_readB_encR (c n w : ℕ) {z : ℤ} (hz : 0 < z) :
    (readB (encR (k := k) (Symbol := Symbol) c n w z)).home = false := by
  rw [readB_encR_pos _ _ _ hz]
  split_ifs <;> rfl

/-- Laying cell `n + 1` of the ruler. -/
lemma encR_push {c n w : ℕ} (hc : c ≤ n) {b : Bool} (hb : b = decide (n + 1 = w)) :
    Function.update (encR (k := k) (Symbol := Symbol) c n w) ((n : ℤ) + 1)
        (bWrite { BCell.empty with mark := true, outer := b }) = encR c (n + 1) w := by
  funext z
  by_cases hz : z = (n : ℤ) + 1
  · subst hz
    rw [Function.update_self]
    simp only [encR, show (n : ℤ) + 1 ≠ 0 by omega, ↓reduceIte,
      show ((n : ℤ) + 1).toNat = n + 1 by omega, show c < n + 1 by omega, le_refl, and_self, hb]
    rfl
  · rw [Function.update_of_ne hz]
    simp only [encR]
    split_ifs <;> first | rfl | omega

/-- Clearing cell `c + 1` of the ruler. -/
lemma encR_pop (c n w : ℕ) :
    Function.update (encR (k := k) (Symbol := Symbol) c n w) ((c : ℤ) + 1) none =
      encR (c + 1) n w := by
  funext z
  by_cases hz : z = (c : ℤ) + 1
  · subst hz
    rw [Function.update_self]
    simp only [encR, show (c : ℤ) + 1 ≠ 0 by omega, ↓reduceIte,
      show ((c : ℤ) + 1).toNat = c + 1 by omega, lt_irrefl, false_and]
  · rw [Function.update_of_ne hz]
    simp only [encR]
    split_ifs <;> first | rfl | omega

/-! ### Laying the ruler -/

lemma cr_start {J u : ℕ} (hu : u + 1 < zs J) :
    (!decide (2 ^ J < u + 1) && decide (off (zs J - 1 - u) = 0)) = decide (u + 1 = 2 ^ J) := by
  rcases J with _ | J
  · simp [zs] at hu
  rcases Nat.lt_or_ge (2 ^ (J + 1)) (u + 1) with h | h
  · simp [h, show u + 1 ≠ 2 ^ (J + 1) by omega]
  · have h1 : zs J ≤ zs (J + 1) - 1 - u := by rw [zs_succ]; omega
    have h2 : zs (J + 1) - 1 - u < zs (J + 1) := by omega
    rw [off_eq h1 h2]
    simp only [show ¬ 2 ^ (J + 1) < u + 1 by omega, decide_false, Bool.not_false, Bool.true_and,
      decide_eq_decide]
    rw [zs_succ]
    omega

/-- **Laying the ruler.** From the end of the created zones, the machine walks to the center,
laying a ruler of `2 ^ (J + 1)` cells on work tape `1` with the outer half marked. -/
lemma runFrom_cr₁ (Z : Fin k → ZTrack Symbol) (J : ℕ) :
    (hennieStearns tm).runFrom
        (C q mv i p out (.cr₁ false false) (encA Z J none) (encB [] []) (zs J - 1) 1)
        (zs J + 1) =
      C q mv i p out (.backB .crWalk) (encA Z J none) (encR 0 (2 ^ (J + 1)) (2 ^ J + 1)) 0
        ((2 ^ (J + 1) + 1 : ℕ) : ℤ) := by
  set A := encA Z J none
  set w := 2 ^ J + 1
  have h1 := one_le_zs J
  have hrun := runFrom_of_step tm (G := fun u => C q mv i p out
    (.cr₁ (decide (u = 2 ^ J)) (decide (2 ^ J < u))) A (encR 0 u w) ((zs J - 1 - u : ℕ) : ℤ)
      ((u : ℤ) + 1)) (W := zs J - 1) fun u hu => by
      have hn : 1 ≤ zs J - 1 - u := by omega
      rw [step_op, readA_encA_nat, aCell_of_lt hn (lvl_lt_of_lt_zs hn (by omega))]
      simp only [opTr, zoneCell_center, Bool.or_false, Bool.false_eq_true, ↓reduceIte, act_apply,
        Option.elim_none, Option.elim_some]
      rw [encR_push (Nat.zero_le _) (by simp; omega)]
      have hf : (decide (2 ^ J < u) || decide (u = 2 ^ J)) = decide (2 ^ J < u + 1) := by
        by_cases h : 2 ^ J < u <;> by_cases h' : u = 2 ^ J <;> simp [h, h'] <;> omega
      simp only [zoneCell, hf, cr_start (show u + 1 < zs J by omega)]
      congr 1
      simp only [SignType.coe_neg_one]
      omega
  simp only [Nat.not_lt_zero, decide_false, Nat.cast_zero, zero_add, Nat.sub_zero,
    decide_eq_false (Nat.two_pow_pos J).ne, encR_of_le w le_rfl] at hrun
  have hA0 : readA (A 0) = some (centerCell Z) := by simp [A, encA, aCell, readA]
  rw [show (zs J : ℤ) - 1 = ((zs J - 1 : ℕ) : ℤ) by omega,
    show zs J + 1 = zs J - 1 + 1 + 1 by omega, runFrom_add, runFrom_add, hrun, runFrom_one,
    runFrom_one, step_op, show ((zs J - 1 - (zs J - 1) : ℕ) : ℤ) = 0 by simp, hA0]
  simp only [opTr, centerCell_center, ↓reduceIte, act_apply, Option.elim_none, Option.elim_some]
  rw [encR_push (Nat.zero_le _) (by simp; omega), step_op]
  simp only [opTr, act_apply, Option.elim_none, Option.elim_some]
  rw [show ((zs J - 1 : ℕ) : ℤ) + 1 + ((1 : SignType) : ℤ) = ((zs J - 1 + 1 : ℕ) : ℤ) + 1 by
      simp,
    encR_push (Nat.zero_le _) ?_]
  · rw [show zs J - 1 + 1 + 1 = 2 ^ (J + 1) by
      rw [zs]; have := Nat.one_le_two_pow (n := J + 1); omega]
    congr 1
    simp [zs]
  · have hz : zs J + 1 = 2 ^ J + 2 ^ J := by
      have := Nat.one_le_two_pow (n := J + 1)
      simp only [zs, pow_succ]
      omega
    have := Nat.one_le_two_pow (n := J)
    by_cases h : 2 ^ J < zs J - 1 <;> by_cases h' : zs J - 1 = 2 ^ J <;>
      simp [h, h', centerCell, w] <;> omega

/-! ### Writing the new zone -/

/-- **Walking to the end of the created zones.** -/
lemma runFrom_crWalk (Z : Fin k → ZTrack Symbol) (J : ℕ) (B : ℤ → Option (HSym k Symbol))
    (pB : ℤ) :
    (hennieStearns tm).runFrom (C q mv i p out .crWalk (encA Z J none) B 0 pB) (zs J + 1) =
      C q mv i p out (.cr₃ true false) (encA Z J none) B (zs J) pB := by
  rw [runFrom_add, runFrom_walk tm q mv i .crWalk p _ _ 0 pB out 1 0 (zs J) fun u hu => by
    simp only [SignType.coe_one, one_mul, zero_add, SignType.coe_zero, zero_mul, add_zero]
    rw [readA_encA_nat]
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · rfl
    · rw [aCell_of_lt hu0 (lvl_lt_of_lt_zs hu0 hu)]
      rfl]
  simp only [SignType.coe_one, one_mul, zero_add, SignType.coe_zero, zero_mul, add_zero]
  rw [runFrom_one, step_op, readA_encA_nat, aCell_of_le (one_le_zs J) (by rw [lvl_zs])]
  simp only [opTr, act_apply, Option.elim_none]
  congr 1
  simp

lemma mixA_eq_left {A A' : ℤ → Option (HSym k Symbol)} {t : ℕ} (h : ∀ z : ℤ, z < t → A' z = A z) :
    mixA A A' t = A := by
  funext z
  simp only [mixA]
  split_ifs with hz
  · exact h z hz
  · rfl

/-- The cells of a new zone. -/
lemma zoneCell_new (Z : Fin k → ZTrack Symbol) {J u : ℕ}
    (hblank : ∀ i s, (Z i).zone s J = List.replicate (2 ^ J) none) (hu : u < 2 ^ (J + 1)) :
    zoneCell Z none (zs J + u) =
      newZoneCell (decide (u = 0)) (!(decide (2 ^ J < u) || decide (u + 1 = 2 ^ J + 1))) := by
  have hinner : (!(decide (2 ^ J < u) || decide (u + 1 = 2 ^ J + 1))) = decide (u < 2 ^ J) := by
    by_cases h : u < 2 ^ J
    · simp [h, show ¬ 2 ^ J < u by omega, show u ≠ 2 ^ J by omega]
    · simp only [h, decide_false]
      rcases Nat.lt_or_ge (2 ^ J) u with h' | h'
      · simp [h']
      · simp only [show ¬ 2 ^ J < u by omega, decide_false, Bool.false_or, Bool.not_eq_eq_eq_not,
          Bool.not_false, decide_eq_true_eq]
        omega
  rw [hinner]
  simp only [zoneCell, lvl_zs_add hu, off_zs_add hu, hblank, newZoneCell, reduceCtorEq,
    false_and, decide_false, ACell.mk.injEq, true_and]
  constructor <;> funext i <;> by_cases h : u < 2 ^ J <;> simp [h]

/-- **Writing the new zone.** Reading the ruler back, the machine writes zone `J`, half full of
blanks. -/
lemma runFrom_cr₃ (Z : Fin k → ZTrack Symbol) (J : ℕ)
    (hblank : ∀ i s, (Z i).zone s J = List.replicate (2 ^ J) none) :
    (hennieStearns tm).runFrom
        (C q mv i p out (.cr₃ true false) (encA Z J none) (encR 0 (2 ^ (J + 1)) (2 ^ J + 1))
          (zs J) 1) (2 ^ (J + 1) + 1) =
      C q mv i p out (.back .scan) (encA Z (J + 1) none) (encB [] [])
        ((zs (J + 1) - 1 : ℕ) : ℤ) ((2 ^ (J + 1) + 1 : ℕ) : ℤ) := by
  set A := encA Z J none
  set A' := encA Z (J + 1) none
  set w := 2 ^ J + 1
  have hrun := runFrom_of_step tm (G := fun u => C q mv i p out
    (.cr₃ (decide (u = 0)) (decide (2 ^ J < u))) (mixA A A' (zs J + u)) (encR u (2 ^ (J + 1)) w)
      ((zs J + u : ℕ) : ℤ) ((u : ℤ) + 1)) (W := 2 ^ (J + 1)) fun u hu => by
      rw [step_op, readB_encR_pos _ _ _ (by omega), show ((u : ℤ) + 1).toNat = u + 1 by omega,
        ite_eq_left (show u < u + 1 ∧ u + 1 ≤ 2 ^ (J + 1) by omega)]
      simp only [opTr, rulerCell, ↓reduceIte, act_apply, Option.elim_some]
      rw [update_mixA_of_eq ?_, encR_pop]
      · have h1 : decide (u + 1 = 0) = false := by simp
        have h2 : (decide (2 ^ J < u) || decide (u + 1 = w)) = decide (2 ^ J < u + 1) := by
          by_cases h : 2 ^ J < u <;> by_cases h' : u + 1 = w <;> simp [h, h', w] <;> omega
        simp only [h2, h1]
        congr 1
      · have hl : lvl (zs J + u) < J + 1 := by rw [lvl_zs_add hu]; omega
        have h1 : 1 ≤ zs J + u := by have := one_le_zs J; omega
        simp only [A', encA_natCast, aCell_of_lt h1 hl, Option.map_some, zoneCell_new Z hblank hu,
          w]
  have hl : mixA A A' (zs J) = A := mixA_eq_left fun z hz => by
    by_cases hz0 : 0 ≤ z
    · have hn : z.toNat < zs J := by omega
      simp only [A, A', encA, hz0, ↓reduceIte, aCell]
      split_ifs with h₀ h₁ h₂ h₂ <;> try first | rfl | omega
      · exact absurd (lvl_lt_of_lt_zs (by omega) hn) h₂
    · simp only [A, A', encA_neg _ _ _ (show z < 0 by omega)]
  simp only [add_zero, hl, decide_true, Nat.not_lt_zero, decide_false, Nat.cast_zero, zero_add]
    at hrun
  rw [runFrom_add, hrun, runFrom_one, step_op,
    show ((2 ^ (J + 1) : ℕ) : ℤ) + 1 = ((2 ^ (J + 1) + 1 : ℕ) : ℤ) by push_cast; rfl,
    readB_encR_pos _ _ _ (Int.natCast_pos.2 (Nat.succ_pos _)), Int.toNat_natCast,
    ite_eq_right (by omega)]
  have hend : mixA A A' (zs J + 2 ^ (J + 1)) = A' := mixA_eq_of_ge fun z hz => by
    have h0z : 0 ≤ z := le_trans (Int.natCast_nonneg _) hz
    have hz' := (Int.le_toNat h0z).2 hz
    have hn : 1 ≤ z.toNat := le_trans (one_le_zs J) (le_trans (Nat.le_add_right _ _) hz')
    have hl : J + 1 ≤ lvl z.toNat := by
      by_contra h
      have := lt_zs_of_lvl_lt hn (show lvl z.toNat < J + 1 by omega)
      rw [zs_succ] at this
      omega
    simp only [A, A', encA, h0z, ↓reduceIte, aCell, show z.toNat ≠ 0 by omega,
      show ¬ lvl z.toNat < J by omega, show ¬ lvl z.toNat < J + 1 by omega, Option.map_none]
  simp only [opTr, BCell.empty, Bool.false_eq_true, ↓reduceIte, act_apply, Option.elim_none, hend,
    encR_of_le w (le_refl (2 ^ (J + 1)))]
  congr 1
  · rw [zs_succ]; have := one_le_zs J; simp; omega

/-! ### Creating a zone -/

/-- The time to create a zone at level `J`. -/
def createTime (J : ℕ) : ℕ :=
  3 * (zs J + 1) + 3 * 2 ^ (J + 1) + 5 + zs (J + 1)

/-- **Creating a zone.** When no created zone holds a symbol on the side of the move of track
`i`, the machine creates zone `J`, half full of blanks, and starts the move again. -/
lemma runFrom_create (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : ∀ i, (Z i).Valid J)
    (hj : (Z i).trig J (srcSide mv i) = J) :
    (hennieStearns tm).runFrom (C q mv i p out .scan (encA Z J none) (encB [] []) 0 1)
        (createTime J) =
      C q mv i p out .scan (encA Z (J + 1) none) (encB [] []) 0 1 := by
  have hblank : ∀ i s, (Z i).zone s J = List.replicate (2 ^ J) none := fun i s =>
    (hV i).blank s J le_rfl
  have hB : ∀ (c n w : ℕ) (u : ℕ), 1 ≤ u →
      (readB (encR (k := k) (Symbol := Symbol) c n w u)).home = false := fun c n w u hu =>
    home_readB_encR _ _ _ (by omega)
  have hT : createTime J = (zs J + 1) + (zs J + 1) + (2 ^ (J + 1) + 1 + 1) + (zs J + 1) +
      (2 ^ (J + 1) + 1) + (zs (J + 1) - 1 + 1) + (2 ^ (J + 1) + 1 + 1) := by
    have := one_le_zs (J + 1)
    simp only [createTime]
    omega
  have e1 := runFrom_scan_blank (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) Z
    (hV i) hj (encB [] []) 1
  have e2 := runFrom_cr₁ (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) Z J
  have e3 := runFrom_backB (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) .crWalk
    (encA Z J none) (encR 0 (2 ^ (J + 1)) (2 ^ J + 1)) 0 (2 ^ (J + 1) + 1)
    rfl fun u hu _ => hB _ _ _ u hu
  have e4 := runFrom_crWalk (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) Z J
    (encR 0 (2 ^ (J + 1)) (2 ^ J + 1)) 1
  have e5 := runFrom_cr₃ (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) Z J hblank
  have e6 := runFrom_back (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) .scan
    (encA Z (J + 1) none) (encB [] []) (zs (J + 1) - 1) (2 ^ (J + 1) + 1)
    ⟨centerCell Z, by simp [encA, aCell, readA], rfl⟩ fun n hn _ c hc => by
      rw [readA_encA_nat, aCell] at hc
      simp only [show n ≠ 0 by omega, ↓reduceIte] at hc
      split_ifs at hc
      cases hc; rfl
  have e7 := runFrom_backB (tm := tm) (q := q) (mv := mv) (i := i) (p := p) (out := out) .scan
    (encA Z (J + 1) none) (encB [] []) 0 (2 ^ (J + 1) + 1) rfl fun u hu _ => by
      rw [readB_encB_pos _ _ (by omega)]
      rfl
  rw [hT]
  exact runFrom_trans tm (runFrom_trans tm (runFrom_trans tm (runFrom_trans tm
    (runFrom_trans tm (runFrom_trans tm e1 e2) e3) e4) e5) e6) e7

end Turing.MultiTapeTM.HennieStearns
