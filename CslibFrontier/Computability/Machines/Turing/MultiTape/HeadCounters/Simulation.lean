/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HeadCounters
import CslibFrontier.Tactic.FinIndex
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Head counters simulate every machine

Every finite-state binary multitape machine is simulated by a machine whose only nonblank work
cells, at every time and on every input, are fixed origin markers. With `k` work tapes the
simulator is a `HeadCounter.machine` with `k + k + 1` counters stored in head positions. For each
simulated tape, two counters hold the cells left and right of its head as base-three numbers,
least significant digit next to the head and blank as the digit zero; one counter is scratch. The
scanned symbols stay in the finite control. A head move pushes the written symbol onto one stack
(multiply by three and add its digit) and pops the other (divide by three), by zero-tested
transfer loops through the scratch counter. This is the classical simulation of tapes by counters
[Minsky1967]. The input head moves exactly as the simulated one, and the output is copied, so the
simulator halts with the same output as the simulated machine; it runs far longer.

A space measure that counts only work-tape cells that are ever nonblank, the literal measure of
Definition 4.1 in the 2007-01-08 draft of [AroraBarak09] (printed p. 76 / PDF p. 92), therefore
charges every decider a constant. The visited-cell measure `Turing.MultiTapeNTM.RunPath.space`
charges the head excursions and does not collapse in this way.

## Main results

* `Turing.MultiTapeTM.HeadCounter.exists_fixed_support_computes`: every finite-state binary
  machine has a finite-state simulator that computes every output the machine computes and whose
  only ever-nonblank work cells are the origins of its tapes.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Turing.MultiTapeTM.HeadCounter

open Function

variable {k : ℕ} {State : Type}

/-! ### Tape halves as base-three numbers -/

/-- The base-three digit of a tape symbol; the blank is `0`. -/
private def digit : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

private lemma digit_lt (s : Option Bool) : digit s < 3 := by
  rcases s with _ | _ | _ <;> simp [digit]

/-- The tape symbol whose digit is the last base-three digit of `n`. -/
private def symbol (n : ℕ) : Option Bool :=
  if n % 3 = 1 then some false else if n % 3 = 2 then some true else none

private lemma symbol_mod (n : ℕ) : symbol (n % 3) = symbol n := by
  simp [symbol]

private lemma symbol_three_mul_add (L : ℕ) (s : Option Bool) : symbol (3 * L + digit s) = s := by
  rcases s with _ | _ | _ <;> simp [symbol, digit]

private lemma three_mul_add_div (L : ℕ) (s : Option Bool) : (3 * L + digit s) / 3 = L := by
  have := digit_lt s
  omega

/-- The cells right of `p` hold the base-three digits of `R`, and those left of `p` the digits of
`L`, least significant digit next to `p`. -/
private def Encodes (f : ℤ → Option Bool) (p : ℤ) (L R : ℕ) : Prop :=
  ∀ n : ℕ, f (p + (n + 1)) = symbol (R / 3 ^ n) ∧ f (p - (n + 1)) = symbol (L / 3 ^ n)

private lemma encodes_blank : Encodes (fun _ => none) 0 0 0 := fun n => by simp [symbol]

private lemma Encodes.symbol_right {f : ℤ → Option Bool} {p : ℤ} {L R : ℕ}
    (h : Encodes f p L R) : f (p + 1) = symbol R := by
  simpa using (h 0).1

private lemma Encodes.symbol_left {f : ℤ → Option Bool} {p : ℤ} {L R : ℕ}
    (h : Encodes f p L R) : f (p - 1) = symbol L := by
  simpa using (h 0).2

/-- Writing under the head leaves both halves unchanged. -/
private lemma Encodes.write {f : ℤ → Option Bool} {p : ℤ} {L R : ℕ} (h : Encodes f p L R)
    (s : Option Bool) : Encodes (update f p s) p L R := fun n => by
  rw [update_of_ne (by omega), update_of_ne (by omega)]
  exact h n

/-- Writing `s` and moving right pushes `s` onto the left half and pops the right half. -/
private lemma Encodes.move_right {f : ℤ → Option Bool} {p : ℤ} {L R : ℕ}
    (h : Encodes f p L R) (s : Option Bool) :
    Encodes (update f p s) (p + 1) (3 * L + digit s) (R / 3) := fun n => by
  refine ⟨?_, ?_⟩
  · have e : p + 1 + ((n : ℤ) + 1) = p + (((n + 1 : ℕ) : ℤ) + 1) := by omega
    rw [update_of_ne (by omega), e, (h (n + 1)).1, Nat.div_div_eq_div_mul, pow_succ']
  · cases n with
    | zero => simp [symbol_three_mul_add]
    | succ n =>
      have e : p + 1 - (((n + 1 : ℕ) : ℤ) + 1) = p - ((n : ℤ) + 1) := by omega
      rw [update_of_ne (by omega), e, (h n).2, pow_succ', ← Nat.div_div_eq_div_mul,
        three_mul_add_div]

/-- Writing `s` and moving left pushes `s` onto the right half and pops the left half. -/
private lemma Encodes.move_left {f : ℤ → Option Bool} {p : ℤ} {L R : ℕ}
    (h : Encodes f p L R) (s : Option Bool) :
    Encodes (update f p s) (p - 1) (L / 3) (3 * R + digit s) := fun n => by
  refine ⟨?_, ?_⟩
  · cases n with
    | zero => simp [symbol_three_mul_add]
    | succ n =>
      have e : p - 1 + (((n + 1 : ℕ) : ℤ) + 1) = p + ((n : ℤ) + 1) := by omega
      rw [update_of_ne (by omega), e, (h n).1, pow_succ', ← Nat.div_div_eq_div_mul,
        three_mul_add_div]
  · have e : p - 1 - ((n : ℤ) + 1) = p - (((n + 1 : ℕ) : ℤ) + 1) := by omega
    rw [update_of_ne (by omega), e, (h (n + 1)).2, Nat.div_div_eq_div_mul, pow_succ']

/-! ### The controller -/

/-- The stages of simulating one step of the simulated machine. -/
private inductive Phase (k : ℕ) where
  /-- Record the input symbol that, with the state and scanned symbols, fixes the action. -/
  | start
  /-- Begin with work tape `j`. -/
  | tape (j : Fin k)
  /-- Push, first loop: move the target stack into scratch, tripled; `i` scratch increments are
  still owed for the last unit moved. -/
  | triple (j : Fin k) (i : Fin 3)
  /-- Push, second loop: move scratch back onto the target stack. -/
  | back (j : Fin k)
  /-- Push, last stage: `i` more increments of the target stack add the pushed digit. -/
  | addDigit (j : Fin k) (i : Fin 3)
  /-- Pop, first loop: divide the source stack by three into scratch; `r` is the remainder so
  far. -/
  | count (j : Fin k) (r : Fin 3)
  /-- Pop, second loop: move scratch back onto the source stack; `r` is the popped digit. -/
  | restore (j : Fin k) (r : Fin 3)
  /-- Apply the input move, output and next state of the simulated step. -/
  | finish
  deriving Fintype

/-- A control state of the simulator. -/
private structure Control (k : ℕ) (State : Type) where
  /-- The state of the simulated machine. -/
  state : State
  /-- The input symbol scanned when the simulated step began. -/
  input : Option Bool
  /-- The work symbols scanned when the simulated step began. -/
  scanned : Fin k → Option Bool
  /-- The work symbols scanned now. -/
  current : Fin k → Option Bool
  /-- The stage within the simulated step. -/
  phase : Phase k

private instance [Finite State] : Finite (Control k State) :=
  Finite.of_injective (fun c : Control k State => (c.state, c.input, c.scanned, c.current, c.phase))
    fun a b h => by cases a; cases b; simp_all

/-- The counter holding the cells left of the head of tape `j`. -/
private def lo (j : Fin k) : Fin (k + k + 1) := ⟨j, by have := j.isLt; omega⟩

/-- The counter holding the cells right of the head of tape `j`. -/
private def hi (j : Fin k) : Fin (k + k + 1) := ⟨k + j, by have := j.isLt; omega⟩

/-- The scratch counter. -/
private def tmp : Fin (k + k + 1) := Fin.last _

private lemma lo_ne_tmp (j : Fin k) : lo j ≠ tmp := by
  fin_index [lo, tmp]

private lemma hi_ne_tmp (j : Fin k) : hi j ≠ tmp := by
  fin_index [hi, tmp]

private lemma lo_ne_hi (j j' : Fin k) : lo j ≠ hi j' := by
  fin_index [lo, hi]

private lemma lo_inj {j j' : Fin k} : lo j = lo j' ↔ j = j' :=
  ⟨fun _ => by fin_index [lo], congrArg lo⟩

private lemma hi_inj {j j' : Fin k} : hi j = hi j' ↔ j = j' :=
  ⟨fun _ => by fin_index [hi], congrArg hi⟩

/-- The stack that a move in direction `d` pushes onto: the half behind the head. -/
private def target (j : Fin k) (d : SignType) : Fin (k + k + 1) := if d = 1 then lo j else hi j

/-- The stack that a move in direction `d` pops from: the half ahead of the head. -/
private def source (j : Fin k) (d : SignType) : Fin (k + k + 1) := if d = 1 then hi j else lo j

/-- Move one unit from counter `x` to counter `y`. -/
private def transfer {m : ℕ} (x y : Fin m) : Fin m → SignType :=
  fun i => if i = x then -1 else if i = y then 1 else 0

/-- Counters after the moves `mv`, as the compiled machine performs them. -/
private def moveCounters {m : ℕ} (cs : Fin m → ℕ) (mv : Fin m → SignType) : Fin m → ℕ :=
  fun i => ((cs i : ℤ) + (mv i).cast).toNat

private lemma moveCounters_zero {m : ℕ} (cs : Fin m → ℕ) : moveCounters cs (fun _ => 0) = cs := by
  funext i
  simp [moveCounters]

private lemma moveCounters_single_one {m : ℕ} (cs : Fin m → ℕ) (x : Fin m) :
    moveCounters cs (Pi.single x 1) = update cs x (cs x + 1) := by
  funext i
  rcases eq_or_ne i x with rfl | hi <;> simp [moveCounters, *]

private lemma moveCounters_single_neg_one {m : ℕ} (cs : Fin m → ℕ) (x : Fin m) :
    moveCounters cs (Pi.single x (-1)) = update cs x (cs x - 1) := by
  funext i
  rcases eq_or_ne i x with rfl | hi
  · simp [moveCounters]; omega
  · simp [moveCounters, hi]

private lemma moveCounters_transfer {m : ℕ} (cs : Fin m → ℕ) {x y : Fin m} (hxy : x ≠ y) :
    moveCounters cs (transfer x y) = update (update cs x (cs x - 1)) y (cs y + 1) := by
  funext i
  rcases eq_or_ne i x with rfl | hx
  · simp [moveCounters, transfer, hxy]; omega
  · rcases eq_or_ne i y with rfl | hy <;> simp [moveCounters, transfer, *]

/-- The first stage of tape `j`, or `finish` after the last tape. -/
private def phaseAt (k j : ℕ) : Phase k := if h : j < k then .tape ⟨j, h⟩ else .finish

/-- The symbol that action `a` leaves under the head of tape `j`, which scanned `s j`. -/
private def written (a : Action k Bool State) (s : Fin k → Option Bool) (j : Fin k) :
    Option Bool :=
  (a.workTapes j).1.getD (s j)

/-- The direction in which the step of `tm` from state `q`, scanning `inp` and `sc`, moves the
head of tape `j`. -/
private noncomputable def dir (tm : MultiTapeTM k Bool State) (q : State) (inp : Option Bool)
    (sc : Fin k → Option Bool) (j : Fin k) : SignType :=
  ((tm.tr q inp sc).workTapes j).2

/-- The controller simulating `tm`. Apart from `start` and `finish`, its instructions neither read
the input nor move the input head nor emit output. -/
private noncomputable def ctl (tm : MultiTapeTM k Bool State) (c : Control k State)
    (inp : Option Bool) (zero : Fin (k + k + 1) → Bool) :
    Instruction (k + k + 1) (Control k State) :=
  let d := dir tm c.state c.input c.scanned
  let w := written (tm.tr c.state c.input c.scanned) c.scanned
  match c.phase with
  | .start => ⟨0, fun _ => 0, none, some { c with input := inp, phase := phaseAt k 0 }⟩
  | .tape j =>
    if d j = 0 then
      ⟨0, fun _ => 0, none,
        some { c with current := update c.current j (w j), phase := phaseAt k (j + 1) }⟩
    else ⟨0, fun _ => 0, none, some { c with phase := .triple j 0 }⟩
  | .triple j i =>
    if i = 0 then
      if zero (target j (d j)) then ⟨0, fun _ => 0, none, some { c with phase := .back j }⟩
      else ⟨0, transfer (target j (d j)) tmp, none, some { c with phase := .triple j 2 }⟩
    else ⟨0, Pi.single tmp 1, none,
      some { c with phase := .triple j ⟨i - 1, by have := i.isLt; omega⟩ }⟩
  | .back j =>
    if zero tmp then
      ⟨0, fun _ => 0, none, some { c with phase := .addDigit j ⟨digit (w j), digit_lt _⟩ }⟩
    else ⟨0, transfer tmp (target j (d j)), none, some { c with phase := .back j }⟩
  | .addDigit j i =>
    if i = 0 then ⟨0, fun _ => 0, none, some { c with phase := .count j 0 }⟩
    else ⟨0, Pi.single (target j (d j)) 1, none,
      some { c with phase := .addDigit j ⟨i - 1, by have := i.isLt; omega⟩ }⟩
  | .count j r =>
    if zero (source j (d j)) then ⟨0, fun _ => 0, none, some { c with phase := .restore j r }⟩
    else if r = 2 then
      ⟨0, transfer (source j (d j)) tmp, none, some { c with phase := .count j 0 }⟩
    else ⟨0, Pi.single (source j (d j)) (-1), none, some { c with phase := .count j (r + 1) }⟩
  | .restore j r =>
    if zero tmp then
      ⟨0, fun _ => 0, none,
        some { c with current := update c.current j (symbol r), phase := phaseAt k (j + 1) }⟩
    else ⟨0, transfer tmp (source j (d j)), none, some { c with phase := .restore j r }⟩
  | .finish =>
    let a := tm.tr c.state c.input c.scanned
    ⟨a.inputTape, fun _ => 0, a.output,
      a.state.map fun q => ⟨q, none, c.current, c.current, .start⟩⟩

/-- The simulator of `tm`. -/
private noncomputable def simulator (tm : MultiTapeTM k Bool State) :
    MultiTapeTM (k + k + 1) Bool (Option (Control k State)) :=
  machine ⟨tm.q₀, none, fun _ => none, fun _ => none, .start⟩ (ctl tm)

private lemma target_ne_tmp (j : Fin k) (d : SignType) : target j d ≠ tmp := by
  unfold target; split_ifs; exacts [lo_ne_tmp j, hi_ne_tmp j]

private lemma source_ne_tmp (j : Fin k) (d : SignType) : source j d ≠ tmp := by
  unfold source; split_ifs; exacts [hi_ne_tmp j, lo_ne_tmp j]

private lemma source_ne_target (j : Fin k) (d : SignType) : source j d ≠ target j d := by
  unfold source target; split_ifs; exacts [(lo_ne_hi j j).symm, lo_ne_hi j j]

/-- Runs concatenate. -/
private lemma reach_trans {m : ℕ} {S : Type} {M : MultiTapeTM m Bool S} {input : List Bool}
    {C₁ C₂ C₃ : Cfg m Bool S input} (h₁ : ∃ n, M.runFrom C₁ n = C₂)
    (h₂ : ∃ n, M.runFrom C₂ n = C₃) : ∃ n, M.runFrom C₁ n = C₃ :=
  let ⟨n₁, h₁⟩ := h₁
  let ⟨n₂, h₂⟩ := h₂
  ⟨n₁ + n₂, by rw [runFrom_add, h₁, h₂]⟩

/-- Counter vectors agreeing at `a`, at `b` and everywhere else are equal. -/
private lemma funext_two {f g : Fin (k + k + 1) → ℕ} (a b : Fin (k + k + 1)) (ha : f a = g a)
    (hb : f b = g b) (h : ∀ i, i ≠ a → i ≠ b → f i = g i) : f = g :=
  funext fun i => if h1 : i = a then h1 ▸ ha else if h2 : i = b then h2 ▸ hb else h i h1 h2

/-! ### Runs of the stages -/

section Stages

variable (tm : MultiTapeTM k Bool State) {input : List Bool} (pos : Fin (input.length + 2))
  (out : List Bool) (q : State) (inp : Option Bool) (sc cur : Fin k → Option Bool) (j : Fin k)

/-- A step of the simulator that neither moves the input head nor emits output. -/
private lemma runFrom_succ_of_ctl {c c' : Control k State} {cs : Fin (k + k + 1) → ℕ}
    {mv : Fin (k + k + 1) → SignType}
    (h : ∀ inp, ctl tm c inp (fun i => decide (cs i = 0)) = ⟨0, mv, none, some c'⟩) (n : ℕ) :
    (simulator tm).runFrom (cfg (some c) pos cs out) (n + 1) =
      (simulator tm).runFrom (cfg (some c') pos (moveCounters cs mv) out) n := by
  rw [show n + 1 = 1 + n by omega, runFrom_add, runFrom_one, simulator, step_cfg, h]
  simp only [moveInputPos_zero, Option.toList_none, List.append_nil]
  rfl

/-- Move the target stack into scratch, tripled. -/
private lemma run_triple (X : ℕ) (cs : Fin (k + k + 1) → ℕ)
    (hX : cs (target j (dir tm q inp sc j)) = X) :
    (simulator tm).runFrom (cfg (some ⟨q, inp, sc, cur, .triple j 0⟩) pos cs out) (3 * X + 1) =
      cfg (some ⟨q, inp, sc, cur, .back j⟩) pos
        (update (update cs (target j (dir tm q inp sc j)) 0) tmp (cs tmp + 3 * X)) out := by
  have hne := target_ne_tmp j (dir tm q inp sc j)
  induction X generalizing cs with
  | zero =>
    have e : update (update cs (target j (dir tm q inp sc j)) 0) tmp (cs tmp + 3 * 0) = cs :=
      funext_two tmp (target j (dir tm q inp sc j)) (by simp only [update_self]; omega)
        (by simp only [update_of_ne hne, update_self, hX]) fun i h1 h2 => by
          simp only [update_of_ne h1, update_of_ne h2]
    rw [e, runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .back j⟩) (mv := fun _ => 0)
      (fun _ => by simp [ctl, hX]), moveCounters_zero]
    rfl
  | succ X ih =>
    rw [show 3 * (X + 1) + 1 = (3 * X + 1) + 1 + 1 + 1 by omega,
      runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .triple j 2⟩)
        (mv := transfer (target j (dir tm q inp sc j)) tmp) (fun _ => by simp [ctl, hX]),
      moveCounters_transfer _ hne,
      runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .triple j 1⟩)
        (mv := Pi.single tmp 1) (fun _ => by simp [ctl]),
      moveCounters_single_one,
      runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .triple j 0⟩)
        (mv := Pi.single tmp 1) (fun _ => by simp [ctl]),
      moveCounters_single_one, ih _ (by simp [hne, hX])]
    congr 1
    exact funext_two tmp (target j (dir tm q inp sc j)) (by simp only [update_self]; omega)
      (by simp only [update_of_ne hne, update_self]) fun i h1 h2 => by
        simp only [update_of_ne h1, update_of_ne h2]

/-- Drain `tmp` onto `dst`, then advance the control state. -/
private lemma run_drainTmp {p p' : Control k State} (dst : Fin (k + k + 1)) (hne : dst ≠ tmp)
    (hz : ∀ {cs : Fin (k + k + 1) → ℕ}, cs tmp = 0 →
      ∀ inp, ctl tm p inp (fun i => decide (cs i = 0)) = ⟨0, fun _ => 0, none, some p'⟩)
    (hs : ∀ {cs : Fin (k + k + 1) → ℕ} {T : ℕ}, cs tmp = T + 1 →
      ∀ inp, ctl tm p inp (fun i => decide (cs i = 0)) = ⟨0, transfer tmp dst, none, some p⟩)
    (T : ℕ) (cs : Fin (k + k + 1) → ℕ) (hT : cs tmp = T) :
    (simulator tm).runFrom (cfg (some p) pos cs out) (T + 1) =
      cfg (some p') pos (update (update cs tmp 0) dst (cs dst + T)) out := by
  induction T generalizing cs with
  | zero =>
    have e : update (update cs tmp 0) dst (cs dst + 0) = cs := by
      rw [(congrArg (update cs tmp) hT.symm).trans (update_eq_self tmp cs)]
      simp only [Nat.add_zero, update_eq_self]
    rw [e, runFrom_succ_of_ctl tm pos out (hz hT), moveCounters_zero]
    rfl
  | succ T ih =>
    rw [runFrom_succ_of_ctl tm pos out (hs hT), moveCounters_transfer _ hne.symm,
      ih _ (by simp [hne.symm, hT])]
    congr 1
    exact funext_two dst tmp (by simp only [update_self]; omega)
      (by simp only [update_of_ne hne.symm, update_self]) fun i h2 h1 => by
        simp only [update_of_ne h1, update_of_ne h2]

/-- Move scratch back onto the target stack, then start adding the digit. -/
private lemma run_back (T : ℕ) (cs : Fin (k + k + 1) → ℕ) (hT : cs tmp = T) :
    (simulator tm).runFrom (cfg (some ⟨q, inp, sc, cur, .back j⟩) pos cs out) (T + 1) =
      cfg (some ⟨q, inp, sc, cur,
          .addDigit j ⟨digit (written (tm.tr q inp sc) sc j), digit_lt _⟩⟩) pos
        (update (update cs tmp 0) (target j (dir tm q inp sc j))
          (cs (target j (dir tm q inp sc j)) + T)) out :=
  run_drainTmp tm pos out _ (target_ne_tmp j (dir tm q inp sc j))
    (fun h0 _ => by simp [ctl, h0]) (fun hS _ => by simp [ctl, hS]) T cs hT

/-- Add the pushed digit to the target stack. -/
private lemma run_addDigit (δ : ℕ) (hδ : δ < 3) (cs : Fin (k + k + 1) → ℕ) :
    (simulator tm).runFrom (cfg (some ⟨q, inp, sc, cur, .addDigit j ⟨δ, hδ⟩⟩) pos cs out)
        (δ + 1) =
      cfg (some ⟨q, inp, sc, cur, .count j 0⟩) pos
        (update cs (target j (dir tm q inp sc j)) (cs (target j (dir tm q inp sc j)) + δ))
        out := by
  induction δ generalizing cs with
  | zero =>
    rw [runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .count j 0⟩) (mv := fun _ => 0)
      (fun _ => by simp [ctl]), moveCounters_zero]
    simp only [Nat.add_zero, update_eq_self]
    rfl
  | succ δ ih =>
    rw [runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .addDigit j ⟨δ, by omega⟩⟩)
        (mv := Pi.single (target j (dir tm q inp sc j)) 1) (fun _ => by simp [ctl]),
      moveCounters_single_one, ih (by omega)]
    congr 1
    funext i
    rcases eq_or_ne i (target j (dir tm q inp sc j)) with rfl | h2
    · simp only [update_self]; omega
    · simp only [update_of_ne h2]

/-- The residue modulo three. -/
private def rem3 (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

/-- Divide the source stack by three into scratch, tracking the remainder. -/
private lemma run_count (Y r : ℕ) (hr : r < 3) (cs : Fin (k + k + 1) → ℕ)
    (hY : cs (source j (dir tm q inp sc j)) = Y) :
    (simulator tm).runFrom (cfg (some ⟨q, inp, sc, cur, .count j ⟨r, hr⟩⟩) pos cs out) (Y + 1) =
      cfg (some ⟨q, inp, sc, cur, .restore j (rem3 (r + Y))⟩) pos
        (update (update cs (source j (dir tm q inp sc j)) 0) tmp (cs tmp + (r + Y) / 3)) out := by
  have hne := source_ne_tmp j (dir tm q inp sc j)
  induction Y generalizing r cs with
  | zero =>
    have e : update (update cs (source j (dir tm q inp sc j)) 0) tmp (cs tmp + (r + 0) / 3) =
        cs :=
      funext_two tmp (source j (dir tm q inp sc j)) (by simp only [update_self]; omega)
        (by simp only [update_of_ne hne, update_self, hY]) fun i h1 h2 => by
          simp only [update_of_ne h1, update_of_ne h2]
    have hrem : rem3 (r + 0) = ⟨r, hr⟩ := by fin_index [rem3]
    rw [e, hrem, runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .restore j ⟨r, hr⟩⟩)
      (mv := fun _ => 0) (fun _ => by simp [ctl, hY]), moveCounters_zero]
    rfl
  | succ Y ih =>
    by_cases h2 : r = 2
    · subst h2
      have hrem : rem3 (0 + Y) = rem3 (2 + (Y + 1)) := by fin_index [rem3]
      rw [runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .count j ⟨0, by omega⟩⟩)
          (mv := transfer (source j (dir tm q inp sc j)) tmp) (fun _ => by simp [ctl, hY]),
        moveCounters_transfer _ hne, ih 0 (by omega) _ (by simp [hne, hY]), hrem]
      congr 1
      exact funext_two tmp (source j (dir tm q inp sc j)) (by simp only [update_self]; omega)
        (by simp only [update_of_ne hne, update_self]) fun i h1 h3 => by
          simp only [update_of_ne h1, update_of_ne h3]
    · have hsucc : (⟨r, hr⟩ + 1 : Fin 3) = ⟨r + 1, by omega⟩ := by fin_index [Fin.val_add]
      have hrem : rem3 (r + 1 + Y) = rem3 (r + (Y + 1)) := by rw [Nat.add_assoc, Nat.add_comm 1]
      have hne2 : (⟨r, hr⟩ : Fin 3) ≠ 2 := by fin_index
      rw [runFrom_succ_of_ctl tm pos out (c' := ⟨q, inp, sc, cur, .count j ⟨r + 1, by omega⟩⟩)
          (mv := Pi.single (source j (dir tm q inp sc j)) (-1))
          (fun _ => by simp [ctl, hY, hne2, hsucc]),
        moveCounters_single_neg_one, ih (r + 1) (by omega) _ (by simp [hY]), hrem]
      congr 1
      exact funext_two tmp (source j (dir tm q inp sc j))
        (by simp only [update_self, update_of_ne hne.symm]; omega)
        (by simp only [update_of_ne hne, update_self]) fun i h1 h3 => by
          simp only [update_of_ne h1, update_of_ne h3]

/-- Move scratch back onto the source stack, record the popped symbol and go to the next tape. -/
private lemma run_restore (T : ℕ) (r : Fin 3) (cs : Fin (k + k + 1) → ℕ) (hT : cs tmp = T) :
    (simulator tm).runFrom (cfg (some ⟨q, inp, sc, cur, .restore j r⟩) pos cs out) (T + 1) =
      cfg (some ⟨q, inp, sc, update cur j (symbol r), phaseAt k (j + 1)⟩) pos
        (update (update cs tmp 0) (source j (dir tm q inp sc j))
          (cs (source j (dir tm q inp sc j)) + T)) out :=
  run_drainTmp tm pos out _ (source_ne_tmp j (dir tm q inp sc j))
    (fun h0 _ => by simp [ctl, h0]) (fun hS _ => by simp [ctl, hS]) T cs hT

/-- One simulated move of tape `j`: push the written symbol behind the head and pop the cell
ahead of it into the scanned symbol. -/
private lemma run_move (hd : dir tm q inp sc j ≠ 0) (cs : Fin (k + k + 1) → ℕ) (h0 : cs tmp = 0) :
    ∃ n, (simulator tm).runFrom (cfg (some ⟨q, inp, sc, cur, .tape j⟩) pos cs out) n =
      cfg (some ⟨q, inp, sc, update cur j (symbol (cs (source j (dir tm q inp sc j)))),
          phaseAt k (j + 1)⟩) pos
        (update (update cs (target j (dir tm q inp sc j))
            (3 * cs (target j (dir tm q inp sc j)) + digit (written (tm.tr q inp sc) sc j)))
          (source j (dir tm q inp sc j)) (cs (source j (dir tm q inp sc j)) / 3)) out := by
  have hx := target_ne_tmp j (dir tm q inp sc j)
  have hy := source_ne_tmp j (dir tm q inp sc j)
  have hxy := source_ne_target j (dir tm q inp sc j)
  obtain ⟨n, hn⟩ := reach_trans ⟨1, runFrom_succ_of_ctl tm pos out
      (c := ⟨q, inp, sc, cur, .tape j⟩) (c' := ⟨q, inp, sc, cur, .triple j 0⟩) (cs := cs)
      (mv := fun _ => 0) (fun _ => by simp [ctl, hd]) 0⟩ <|
    reach_trans ⟨_, run_triple tm pos out q inp sc cur j _ _ rfl⟩ <|
    reach_trans ⟨_, run_back tm pos out q inp sc cur j (3 * cs (target j (dir tm q inp sc j))) _
      (by simp [moveCounters_zero, h0])⟩ <|
    reach_trans ⟨_, run_addDigit tm pos out q inp sc cur j _ (digit_lt _) _⟩ <|
    reach_trans ⟨_, run_count tm pos out q inp sc cur j (cs (source j (dir tm q inp sc j))) 0
      (by omega) _ (by simp [moveCounters_zero, hxy, hy])⟩ <|
    ⟨_, run_restore tm pos out q inp sc cur j (cs (source j (dir tm q inp sc j)) / 3) _ _
      (by simp [moveCounters_zero, hx.symm, h0])⟩
  refine ⟨n, hn.trans ?_⟩
  simp only [rem3, Nat.zero_add, symbol_mod]
  congr 1
  refine funext_two tmp (target j (dir tm q inp sc j))
    (by simp [moveCounters_zero, hx.symm, hy.symm, h0])
    (by simp [moveCounters_zero, hx, hxy.symm, h0]) fun i h1 h2 => ?_
  by_cases h3 : i = source j (dir tm q inp sc j)
  · subst h3
    simp [moveCounters_zero, h1, h0]
  · simp [moveCounters_zero, h1, h2, h3]

end Stages

/-! ### Simulating steps of the simulated machine -/

section Steps

variable (tm : MultiTapeTM k Bool State) {input : List Bool}

/-- After an action, the written symbol replaces the scanned one. -/
private lemma apply_workTapes (a : Action k Bool State) (c : Cfg k Bool State input) (j : Fin k) :
    (a.apply c).workTapes j =
      update (c.workTapes j) (c.workTapePos j) (written a c.workTapeSymbols j) := by
  rcases h : (a.workTapes j).1 with _ | s <;> simp [Action.apply, written, Cfg.workTapeSymbols, h]

/-- The simulator is at the start of a step of `tm` from `c`: the counters encode the work tapes
of `c`, and the scratch counter is zero. -/
private def Sim (c : Cfg k Bool State input)
    (C : Cfg (k + k + 1) Bool (Option (Control k State)) input) : Prop :=
  ∃ cs : Fin (k + k + 1) → ℕ, cs tmp = 0 ∧
    (∀ j, Encodes (c.workTapes j) (c.workTapePos j) (cs (lo j)) (cs (hi j))) ∧
    C = cfg (c.state.map fun q => ⟨q, none, c.workTapeSymbols, c.workTapeSymbols, .start⟩)
      c.inputPos cs c.output

/-- Partway through simulating the step of action `a` from `c`: the tapes before `j` show the
result of the step, the others still those of `c`. -/
private def StepInv (c : Cfg k Bool State input) (a : Action k Bool State) (j : ℕ)
    (cur : Fin k → Option Bool) (cs : Fin (k + k + 1) → ℕ) : Prop :=
  cs tmp = 0 ∧ ∀ i : Fin k,
    ((i : ℕ) < j → cur i = (a.apply c).workTapeSymbols i ∧
      Encodes ((a.apply c).workTapes i) ((a.apply c).workTapePos i) (cs (lo i)) (cs (hi i))) ∧
    (j ≤ i → cur i = c.workTapeSymbols i ∧
      Encodes (c.workTapes i) (c.workTapePos i) (cs (lo i)) (cs (hi i)))

/-- A step of the simulator. -/
private lemma step_simulator (pos : Fin (input.length + 2)) (out : List Bool) (c : Control k State)
    (cs : Fin (k + k + 1) → ℕ) :
    let a := ctl tm c (cfg (some c) pos cs out).inputSymbol (fun i => decide (cs i = 0))
    (simulator tm).step (cfg (some c) pos cs out) =
      cfg a.state (moveInputPos pos a.inputTape) (moveCounters cs a.counters)
        (out ++ a.output.toList) :=
  step_cfg _ _ _ _ _ _

/-- Simulate the step on tape `j`. -/
private lemma run_tape (pos : Fin (input.length + 2)) (out : List Bool) (q : State)
    (c : Cfg k Bool State input) (j : Fin k) (cur : Fin k → Option Bool)
    (cs : Fin (k + k + 1) → ℕ)
    (h : StepInv c (tm.tr q c.inputSymbol c.workTapeSymbols) j cur cs) :
    ∃ n cur' cs', (simulator tm).runFrom
        (cfg (some ⟨q, c.inputSymbol, c.workTapeSymbols, cur, .tape j⟩) pos cs out) n =
      cfg (some ⟨q, c.inputSymbol, c.workTapeSymbols, cur', phaseAt k (j + 1)⟩) pos cs' out ∧
      StepInv c (tm.tr q c.inputSymbol c.workTapeSymbols) (j + 1) cur' cs' := by
  obtain ⟨h0, hinv⟩ := h
  obtain ⟨hcur, henc⟩ := (hinv j).2 le_rfl
  have hw := apply_workTapes (tm.tr q c.inputSymbol c.workTapeSymbols) c j
  have hdir : dir tm q c.inputSymbol c.workTapeSymbols j =
      ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes j).2 := rfl
  -- the tapes other than `j` keep their state in the invariant
  have hother (cur' : Fin k → Option Bool) (cs' : Fin (k + k + 1) → ℕ) (h0' : cs' tmp = 0)
      (hcur' : ∀ i, i ≠ j → cur' i = cur i) (hlo : ∀ i, i ≠ j → cs' (lo i) = cs (lo i))
      (hhi : ∀ i, i ≠ j → cs' (hi i) = cs (hi i))
      (hj : cur' j = (tm.tr q c.inputSymbol c.workTapeSymbols |>.apply c).workTapeSymbols j ∧
        Encodes ((tm.tr q c.inputSymbol c.workTapeSymbols |>.apply c).workTapes j)
          ((tm.tr q c.inputSymbol c.workTapeSymbols |>.apply c).workTapePos j)
          (cs' (lo j)) (cs' (hi j))) :
      StepInv c (tm.tr q c.inputSymbol c.workTapeSymbols) (j + 1) cur' cs' := by
    refine ⟨h0', fun i => ?_⟩
    by_cases hij : i = j
    · subst hij
      exact ⟨fun _ => hj, fun h => absurd h (by omega)⟩
    · rw [hcur' i hij, hlo i hij, hhi i hij]
      exact ⟨fun h => (hinv i).1 (by omega), fun h => (hinv i).2 (by omega)⟩
  rcases hd : ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes j).2 with _ | _ | _
  · -- no move: only the scanned symbol changes
    rw [SignType.zero_eq_zero] at hd
    refine ⟨0 + 1, _, cs, runFrom_succ_of_ctl tm pos out
      (c' := ⟨q, c.inputSymbol, c.workTapeSymbols,
        update cur j (written (tm.tr q c.inputSymbol c.workTapeSymbols) c.workTapeSymbols j),
        phaseAt k (j + 1)⟩) (mv := fun _ => 0) (fun _ => by simp [ctl, hdir, hd]) 0 |>.trans
        (by rw [moveCounters_zero]; rfl), ?_⟩
    refine hother _ _ h0 (fun i hi => update_of_ne hi _ _) (fun _ _ => rfl) (fun _ _ => rfl) ?_
    simp only [Cfg.workTapeSymbols, hw, Action.apply_workTapePos, hd, SignType.coe_zero,
      add_zero, update_self, true_and]
    exact henc.write _
  · -- move left
    rw [SignType.neg_eq_neg_one] at hd
    have hd' : dir tm q c.inputSymbol c.workTapeSymbols j ≠ 0 := by rw [hdir, hd]; decide
    obtain ⟨n, hn⟩ := run_move tm pos out q c.inputSymbol c.workTapeSymbols cur j hd' cs h0
    have ht : target j (dir tm q c.inputSymbol c.workTapeSymbols j) = hi j := by
      simp [target, hdir, hd]
    have hs : source j (dir tm q c.inputSymbol c.workTapeSymbols j) = lo j := by
      simp [source, hdir, hd]
    rw [ht, hs] at hn
    refine ⟨n, _, _, hn, hother _ _ ?_ (fun i hi => update_of_ne hi _ _) (fun i hi => ?_)
      (fun i hi => ?_) ?_⟩
    · simp [(lo_ne_tmp j).symm, (hi_ne_tmp j).symm, h0]
    · rw [update_of_ne (fun e => hi (lo_inj.mp e)), update_of_ne (lo_ne_hi i j)]
    · rw [update_of_ne (fun e => lo_ne_hi j i e.symm), update_of_ne (fun e => hi (hi_inj.mp e))]
    · have hpos : (tm.tr q c.inputSymbol c.workTapeSymbols |>.apply c).workTapePos j =
          c.workTapePos j - 1 := by
        simp only [Action.apply_workTapePos, hd, SignType.coe_neg_one]; omega
      simp only [Cfg.workTapeSymbols, hw, hpos, update_self, update_of_ne (lo_ne_hi j j).symm,
        update_of_ne (show c.workTapePos j - 1 ≠ c.workTapePos j by omega)]
      exact ⟨henc.symbol_left.symm, henc.move_left _⟩
  · -- move right
    rw [SignType.pos_eq_one] at hd
    have hd' : dir tm q c.inputSymbol c.workTapeSymbols j ≠ 0 := by rw [hdir, hd]; decide
    obtain ⟨n, hn⟩ := run_move tm pos out q c.inputSymbol c.workTapeSymbols cur j hd' cs h0
    have ht : target j (dir tm q c.inputSymbol c.workTapeSymbols j) = lo j := by
      simp [target, hdir, hd]
    have hs : source j (dir tm q c.inputSymbol c.workTapeSymbols j) = hi j := by
      simp [source, hdir, hd]
    rw [ht, hs] at hn
    refine ⟨n, _, _, hn, hother _ _ ?_ (fun i hi => update_of_ne hi _ _) (fun i hi => ?_)
      (fun i hi => ?_) ?_⟩
    · simp [(lo_ne_tmp j).symm, (hi_ne_tmp j).symm, h0]
    · rw [update_of_ne (lo_ne_hi i j), update_of_ne (fun e => hi (lo_inj.mp e))]
    · rw [update_of_ne (fun e => hi (hi_inj.mp e)), update_of_ne (fun e => lo_ne_hi j i e.symm)]
    · simp only [Cfg.workTapeSymbols, hw, Action.apply_workTapePos, hd, SignType.coe_one,
        update_self, update_of_ne (lo_ne_hi j j),
        update_of_ne (show c.workTapePos j + 1 ≠ c.workTapePos j by omega)]
      exact ⟨henc.symbol_right.symm, henc.move_right _⟩

/-- Simulate the step on all tapes from tape `j` on. -/
private lemma run_tapes (pos : Fin (input.length + 2)) (out : List Bool) (q : State)
    (c : Cfg k Bool State input) :
    ∀ (m j : ℕ) (cur : Fin k → Option Bool) (cs : Fin (k + k + 1) → ℕ), j + m = k →
      StepInv c (tm.tr q c.inputSymbol c.workTapeSymbols) j cur cs →
      ∃ n cur' cs', (simulator tm).runFrom
          (cfg (some ⟨q, c.inputSymbol, c.workTapeSymbols, cur, phaseAt k j⟩) pos cs out) n =
        cfg (some ⟨q, c.inputSymbol, c.workTapeSymbols, cur', .finish⟩) pos cs' out ∧
        StepInv c (tm.tr q c.inputSymbol c.workTapeSymbols) k cur' cs'
  | 0, j, cur, cs, hjm, h => by
    obtain rfl : j = k := by omega
    have hp : phaseAt j j = .finish := by simp [phaseAt]
    exact ⟨0, cur, cs, by rw [hp]; rfl, h⟩
  | m + 1, j, cur, cs, hjm, h => by
    have hj : j < k := by omega
    obtain ⟨n₁, cur₁, cs₁, h₁, hinv₁⟩ := run_tape tm pos out q c ⟨j, hj⟩ cur cs h
    obtain ⟨n₂, cur₂, cs₂, h₂, hinv₂⟩ := run_tapes pos out q c m (j + 1) cur₁ cs₁ (by omega) hinv₁
    refine ⟨n₁ + n₂, cur₂, cs₂, ?_, hinv₂⟩
    rw [show phaseAt k j = .tape ⟨j, hj⟩ by simp [phaseAt, hj], runFrom_add, h₁]
    exact h₂

/-- The simulator carries out each step of `tm`. -/
private lemma sim_step {c : Cfg k Bool State input}
    {C : Cfg (k + k + 1) Bool (Option (Control k State)) input} (h : Sim c C) {q : State}
    (hq : c.state = some q) : ∃ n, Sim (tm.step c) ((simulator tm).runFrom C n) := by
  obtain ⟨cs, h0, henc, rfl⟩ := h
  obtain ⟨n, cur, cs', htapes, hinv⟩ := run_tapes tm c.inputPos c.output q c k 0
    c.workTapeSymbols cs (by omega) ⟨h0, fun i => ⟨fun h => absurd h (Nat.not_lt_zero _),
      fun _ => ⟨rfl, henc i⟩⟩⟩
  have hcur : cur = (tm.tr q c.inputSymbol c.workTapeSymbols |>.apply c).workTapeSymbols :=
    funext fun i => ((hinv.2 i).1 i.isLt).1
  have hstart : (simulator tm).runFrom (cfg (some ⟨q, none, c.workTapeSymbols, c.workTapeSymbols,
      .start⟩) c.inputPos cs c.output) 1 = cfg (some ⟨q, c.inputSymbol, c.workTapeSymbols,
        c.workTapeSymbols, phaseAt k 0⟩) c.inputPos cs c.output := by
    rw [runFrom_one, step_simulator]
    simp only [ctl, moveInputPos_zero, moveCounters_zero, Option.toList_none, List.append_nil]
    rfl
  have hfinish : (simulator tm).runFrom (cfg (some ⟨q, c.inputSymbol, c.workTapeSymbols, cur,
      .finish⟩) c.inputPos cs' c.output) 1 =
      cfg ((tm.tr q c.inputSymbol c.workTapeSymbols).state.map
        fun q' => ⟨q', none, cur, cur, .start⟩)
        (moveInputPos c.inputPos (tm.tr q c.inputSymbol c.workTapeSymbols).inputTape) cs'
        (c.output ++ (tm.tr q c.inputSymbol c.workTapeSymbols).output.toList) := by
    rw [runFrom_one, step_simulator]
    simp only [ctl, moveCounters_zero]
  refine ⟨1 + n + 1, cs', hinv.1, fun i => ?_, ?_⟩
  · rw [step_of_state hq]
    exact ((hinv.2 i).1 i.isLt).2
  · simp only [hq, Option.map_some]
    rw [runFrom_add, runFrom_add, hstart, htapes, hfinish, step_of_state hq, ← hcur]
    rfl

/-- Started on `input`, the simulator carries out every run of `tm`. -/
private lemma sim_runFrom (input : List Bool) (t : ℕ) :
    ∃ n, Sim (tm.runFrom (tm.initCfg input) t)
      ((simulator tm).runFrom ((simulator tm).initCfg input) n) := by
  induction t with
  | zero =>
    refine ⟨1, fun _ => 0, rfl, fun _ => encodes_blank, ?_⟩
    rw [runFrom_one, simulator, step_init]
    rfl
  | succ t ih =>
    obtain ⟨n, hn⟩ := ih
    rw [runFrom_succ]
    cases hs : (tm.runFrom (tm.initCfg input) t).state with
    | none =>
      rw [step_of_halt hs]
      exact ⟨n, hn⟩
    | some q =>
      obtain ⟨n', hn'⟩ := sim_step tm hn hs
      exact ⟨n + n', by rwa [runFrom_add]⟩

end Steps

/-- **Head counters simulate every machine.** Every finite-state binary multitape machine with
`k` work tapes has a finite-state simulator with `k + k + 1` work tapes that computes every output
the machine computes, and whose only work cells that are ever nonblank, at every time and on every
input, are the origins of its tapes.

The simulator (`HeadCounter.machine` with a controller) keeps each simulated tape as two
base-three numbers in head counters and runs much longer than the machine it simulates. Under a
space measure that counts only ever-nonblank work cells, as in Definition 4.1 of the 2007-01-08
draft of [AroraBarak09] (printed p. 76 / PDF p. 92), it therefore decides every decidable problem in
constant space. The construction is the classical simulation of tapes by counters
[Minsky1967]. -/
theorem exists_fixed_support_computes [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ (State' : Type) (_ : Finite State') (tm' : MultiTapeTM (k + k + 1) Bool State'),
      (∀ input output, tm.Computes input output → tm'.Computes input output) ∧
      ∀ input t i z, (tm'.runFrom (tm'.initCfg input) t).workTapes i z ≠ none → z = 0 := by
  refine ⟨Option (Control k State), inferInstance, simulator tm, ?_, run_support _ _⟩
  rintro input output ⟨u, hu, hout⟩
  obtain ⟨n, cs, -, -, h⟩ := sim_runFrom tm input u
  have hs : (tm.runFrom (tm.initCfg input) u).state = none := hu
  exact ⟨n, by simp only [Cfg.Halted, h, cfg, hs, Option.map_none], h.symm ▸ hout⟩

end Turing.MultiTapeTM.HeadCounter
