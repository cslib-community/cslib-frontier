/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnce
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationMatrix
public import CslibFrontier.Crypto.Primitives.PRG.Nisan.Bits

/-!
# Nisan's generator fools randomized logarithmic space

A fair-coin machine (`Turing.MultiTapePTM`) reads each coin once, in order, and between coins it
remembers only its view (`Turing.FiniteCfg`). So on a set `V` of views that contains the initial
view and is closed under coin steps, its run on `t` coins is a read-once branching program of
length `t` and width `|V|` over the coins (`Turing.MultiTapePTM.coinProgram`): the states are the
views of `V`, coin `i` is read at time `i` by the coin step `Turing.MultiTapePTM.viewCoinStep`, and
the accepting states are the accepting halted views. The program accepts a coin string exactly when
the machine does (`Turing.MultiTapePTM.eval_coinProgram_iff`). This is the reduction from
space-bounded probabilistic machines to read-once branching programs behind Nisan's generator
[Nisan1992], [Vadhan, Section 8.2.1][Vadhan2012].

Nisan's generator on bit strings (`Cslib.Crypto.PRG.Nisan.bitGenerator`) fools such programs
(`Cslib.Crypto.PRG.Nisan.abs_dens_eval_bitGenerator_sub_le`), hence fair-coin machines: with blocks
of `n` bits and `r` hash seeds, the fraction of the `2 ^ (n + r (3 n - 1))` seeds whose output the
machine accepts (`Turing.MultiTapePTM.acceptNisanSeeds`) is within `(2 ^ r - 1) |V| / (2 √(2 ^ n))`
of the fraction of all `2 ^ (2 ^ r n)` coin strings it accepts
(`Turing.MultiTapePTM.abs_acceptNisanSeeds_div_sub_le`).

For a `Cslib.Complexity.BPL` machine the reachable views are polynomially many and every branch
halts within a polynomial clock, so `r = O(log m)` hash seeds and blocks of `n = O(log m)` bits,
depending only on the input length `m`, suffice: a `BPL` language is decided by the majority of the
machine's answers over the `O(log² m)`-bit seeds of Nisan's generator
(`Cslib.Complexity.exists_acceptNisanSeeds_of_mem_BPL`). This is a step of Nisan's proof that
`BPL ⊆ DSPACE(log² n)` [Nisan1992], [Arora and Barak, Section 16.7][AroraBarak07], not that
inclusion: the deterministic simulation that enumerates the seeds, evaluates the generator and
replays the machine within `O(log² m)` work-tape cells is
`Cslib.Complexity.BPL_subset_DSPACE_log2_sq`.

## Main definitions

* `Turing.MultiTapePTM.coinProgram`: the read-once branching program of a fair-coin machine on a
  closed set of views.
* `Turing.MultiTapePTM.acceptNisanSeeds`: the number of seeds of Nisan's generator whose output the
  machine accepts as its coins.

## Main results

* `Turing.MultiTapePTM.eval_coinProgram_iff`: the program accepts the coin strings the machine
  accepts.
* `Turing.MultiTapePTM.abs_acceptNisanSeeds_div_sub_le`: Nisan's generator fools fair-coin machines,
  with error proportional to the number of views.
* `Cslib.Complexity.exists_acceptNisanSeeds_of_mem_BPL`: a `BPL` language is decided by majority
  over the `O(log² m)`-bit seeds of Nisan's generator.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Section 16.7
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Section 8.2.1
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.BranchingPrograms Cslib.Crypto.PRG

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

open scoped Classical in
/-- **The read-once branching program of a fair-coin machine** on a set `V` of views that contains
the initial view on `input` and is closed under coin steps, reading `t` coins: its states are the
views of `V`, it starts at the initial view, at every time it takes the coin step
(`Turing.MultiTapePTM.viewCoinStep`) on the coin read, and it accepts at the accepting halted views.
Its width is `|V|`. -/
noncomputable def coinProgram {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (t : ℕ) : ReadOnceProgram t V Bool where
  start := ⟨_, hinit⟩
  step _ v bit := ⟨machine.viewCoinStep v bit, hV _ v.property bit⟩
  accept v := decide ((v : FiniteCfg k Bool State).state = none ∧
    (v : FiniteCfg k Bool State).output = [true])

open scoped Classical in
/-- The number of seeds of Nisan's generator on bit strings
(`Cslib.Crypto.PRG.Nisan.bitGenerator n r`, with blocks of `n` bits and `r` hash seeds) whose
output, read as the `2 ^ r n` coins, the machine accepts on `input`: the replay from the initial
configuration ends halted with output `[true]`. This is `Turing.MultiTapePTM.acceptCoins` with the
uniform coin strings replaced by the outputs of the generator. -/
@[expose] noncomputable def acceptNisanSeeds (input : List Bool) (n r : ℕ) : ℕ :=
  (Finset.univ.filter fun z : Nisan.BitSeed n r =>
    (machine.stepCoins (List.ofFn (Nisan.bitGenerator n r z))
        (machine.toNTM.initCfg input)).Halted ∧
      (machine.stepCoins (List.ofFn (Nisan.bitGenerator n r z))
        (machine.toNTM.initCfg input)).output = [true]).card

variable {machine}

/-- **The program of a fair-coin machine accepts the coin strings the machine accepts**: the
program `Turing.MultiTapePTM.coinProgram` accepts a coin string `w` exactly when the replay of `w`
from the initial configuration on `input` ends halted with output `[true]`. -/
theorem eval_coinProgram_iff {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) {t : ℕ} (w : Fin t → Bool) :
    (machine.coinProgram hV hinit t).eval w = true ↔
      (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).Halted ∧
        (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).output = [true] := by
  have hrun : ∀ (l : List Bool) (v : V),
      ((l.foldl (fun v bit => (⟨machine.viewCoinStep v bit, hV _ v.property bit⟩ : V)) v : V) :
        FiniteCfg k Bool State) = l.foldl machine.viewCoinStep v := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons bit l ih => exact fun v => ih _
  rw [stepCoins_accepts_iff_foldl_viewCoinStep, ← hrun (List.ofFn w) ⟨_, hinit⟩]
  simp only [ReadOnceProgram.eval, ReadOnceProgram.finalState, coinProgram,
    Fin.foldl_eq_finRange_foldl, List.ofFn_eq_map, List.foldl_map, decide_eq_true_iff]

/-- **Nisan's generator fools fair-coin machines** [Nisan1992]: for every set `V` of views that
contains the initial view on `input` and is closed under coin steps, the fraction of the seeds of
`Cslib.Crypto.PRG.Nisan.bitGenerator n r` whose output the machine accepts differs from the
fraction of all coin strings of length `2 ^ r n` that it accepts by at most
`(2 ^ r - 1) |V| / (2 √(2 ^ n))`. No halting time is assumed; when every branch halts within
`2 ^ r n` steps, the second fraction is the acceptance probability
(`Turing.MultiTapePTM.acceptCoins_mul_two_pow`). -/
theorem abs_acceptNisanSeeds_div_sub_le {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (n r : ℕ) :
    |(machine.acceptNisanSeeds input n r : ℝ) / 2 ^ (n + r * (3 * n - 1)) -
        (machine.acceptCoins input (2 ^ r * n) : ℝ) / 2 ^ (2 ^ r * n)| ≤
      (2 ^ r - 1) * V.card / (2 * √(2 ^ n)) := by
  classical
  have h := Nisan.abs_dens_eval_bitGenerator_sub_le n r (machine.coinProgram hV hinit (2 ^ r * n))
  rw [Fintype.card_coe, Finset.nnratCast_dens, Finset.nnratCast_dens, Nisan.card_bitSeed,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have hseeds : machine.acceptNisanSeeds input n r =
      (Finset.univ.filter fun z : Nisan.BitSeed n r =>
        (machine.coinProgram hV hinit (2 ^ r * n)).eval (Nisan.bitGenerator n r z) = true).card :=
    congrArg Finset.card (Finset.filter_congr fun _ _ => (eval_coinProgram_iff hV hinit _).symm)
  have hcoins : machine.acceptCoins input (2 ^ r * n) =
      (Finset.univ.filter fun w : Fin (2 ^ r * n) → Bool =>
        (machine.coinProgram hV hinit (2 ^ r * n)).eval w = true).card :=
    congrArg Finset.card (Finset.filter_congr fun w _ => (eval_coinProgram_iff hV hinit w).symm)
  rw [hseeds, hcoins]
  exact_mod_cast h

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- `r = d (log₂ m + 2) + 1` hash seeds cover the polynomial clock `polyClock d m`. -/
private theorem polyClock_le_two_pow (d m : ℕ) :
    polyClock d m ≤ 2 ^ (d * (Nat.log2 m + 2) + 1) := by
  have hm : 2 * (m + 1) ≤ 2 ^ (Nat.log2 m + 2) := by
    have := Nat.lt_log2_self (n := m)
    rw [pow_succ]
    omega
  calc polyClock d m = 2 * (2 * (m + 1)) ^ d := rfl
    _ ≤ 2 * (2 ^ (Nat.log2 m + 2)) ^ d := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hm d)
    _ = 2 ^ (d * (Nat.log2 m + 2) + 1) := by
      rw [← pow_mul, pow_succ, Nat.mul_comm 2, Nat.mul_comm (Nat.log2 m + 2)]

/-- The seed length `n + r (3 n - 1)` for `n = 2 (2 r + 3)` and `r = d (ℓ + 2) + 1` is at most
`39 (2 d + 1) ^ 2 (ℓ + 1) ^ 2`. -/
private theorem seedLength_le (d ℓ : ℕ) :
    2 * (2 * (d * (ℓ + 2) + 1) + 3) +
        (d * (ℓ + 2) + 1) * (3 * (2 * (2 * (d * (ℓ + 2) + 1) + 3)) - 1) ≤
      39 * (2 * d + 1) ^ 2 * (ℓ + 1) ^ 2 := by
  set r := d * (ℓ + 2) + 1 with hr
  have hrR : r ≤ (2 * d + 1) * (ℓ + 1) := by rw [hr]; nlinarith
  rw [show 3 * (2 * (2 * r + 3)) - 1 = 12 * r + 17 by omega]
  nlinarith [Nat.mul_le_mul hrR hrR, show 1 ≤ r by omega]

/-- **A `BPL` language is decided by majority over the seeds of Nisan's generator**: a step of
Nisan's proof of `BPL ⊆ DSPACE(log² n)` [Nisan1992], not that inclusion. A `BPL` language has a
fair-coin machine, within `c (log₂ m + 1)` work cells on every encoded instance of length `m`, and
a constant `d` such that on every such instance, with
`r = d (log₂ m + 2) + 1` hash seeds and blocks of `n = 2 (2 r + 3)` bits, the seeds of
`Cslib.Crypto.PRG.Nisan.bitGenerator n r` have at most `39 (2 d + 1) ^ 2 (log₂ m + 1) ^ 2` bits,
and the machine, reading the generator's output as its coins, accepts members on more than half of
the seeds and non-members on fewer than half. The parameters depend only on `m`. The deterministic
`O(log² m)`-space simulation that enumerates the seeds, evaluates the generator and replays the
machine is `Cslib.Complexity.BPL_subset_DSPACE_log2_sq`. -/
theorem exists_acceptNisanSeeds_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c d : ℕ),
      (∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1))) ∧
      ∀ a r n, r = d * (Nat.log2 (enc a).length + 2) + 1 → n = 2 * (2 * r + 3) →
        n + r * (3 * n - 1) ≤ 39 * (2 * d + 1) ^ 2 * (Nat.log2 (enc a).length + 1) ^ 2 ∧
        (a ∈ A → 2 ^ (n + r * (3 * n - 1)) < 2 * M.acceptNisanSeeds (enc a) n r) ∧
        (a ∉ A → 2 * M.acceptNisanSeeds (enc a) n r < 2 ^ (n + r * (3 * n - 1))) := by
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  set d := MultiTapeNTM.logSpaceClockExponent k State c
  refine ⟨k, State, hfin, M, c, d, fun a => (hM a).1, fun a r n hr hn => ?_⟩
  obtain ⟨hs, t, ht, hmem, hnot⟩ := hM a
  obtain ⟨V, hreach, hV, hcard⟩ := M.exists_finset_reachable hs
  have hinit : M.toNTM.initView (enc a) ∈ V := (hreach _).mpr .refl
  have hpoly := MultiTapeNTM.two_pow_coreLengthBound_log_le k State c (enc a).length
  have hT : polyClock d (enc a).length ≤ 2 ^ r := hr ▸ polyClock_le_two_pow d _
  have hVr : V.card ≤ 2 ^ r := (hcard.trans hpoly).trans hT
  have hL : M.toNTM.RunsInTime (enc a) (2 ^ r * n) :=
    ((MultiTapeNTM.runsInTime_of_runsInSpace hs ht).mono hpoly).mono
      (hT.trans (Nat.le_mul_of_pos_right _ (by omega)))
  have herr := abs_le.mp (M.abs_acceptNisanSeeds_div_sub_le hV hinit n r)
  have hsqrt : √((2 : ℝ) ^ n) = 2 ^ r * 2 ^ r * 8 := by
    rw [show (2 : ℝ) ^ n = (2 ^ r * 2 ^ r * 8) ^ 2 by rw [hn]; ring]
    exact Real.sqrt_sq (by positivity)
  have hVr' : (V.card : ℝ) ≤ 2 ^ r := by exact_mod_cast hVr
  have h1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
  have hsmall : (2 ^ r - 1) * (V.card : ℝ) / (2 * √(2 ^ n)) ≤ 1 / 16 := by
    rw [hsqrt, div_le_iff₀ (by positivity)]
    nlinarith
  have hpos : (0 : ℝ) < 2 ^ (n + r * (3 * n - 1)) := by positivity
  have hposL : (0 : ℝ) < 2 ^ (2 ^ r * n) := by positivity
  refine ⟨by subst hn hr; exact seedLength_le d _, fun ha => ?_, fun ha => ?_⟩
  · have hacc := (M.two_pow_mul_le_iff ht hL 2 3).mp (hmem ha)
    have hacc' : (2 : ℝ) / 3 ≤ (M.acceptCoins (enc a) (2 ^ r * n) : ℝ) / 2 ^ (2 ^ r * n) := by
      rw [div_le_div_iff₀ (by norm_num) hposL]
      exact_mod_cast (by linarith : 2 * 2 ^ (2 ^ r * n) ≤ M.acceptCoins (enc a) (2 ^ r * n) * 3)
    have hgt : (1 : ℝ) / 2 < (M.acceptNisanSeeds (enc a) n r : ℝ) / 2 ^ (n + r * (3 * n - 1)) := by
      linarith [herr.1]
    rw [div_lt_div_iff₀ (by norm_num) hpos] at hgt
    exact_mod_cast (by linarith : (2 : ℝ) ^ (n + r * (3 * n - 1)) <
      2 * M.acceptNisanSeeds (enc a) n r)
  · have hacc := (M.mul_le_two_pow_iff ht hL 1 3).mp (by simpa using hnot ha)
    have hacc' : (M.acceptCoins (enc a) (2 ^ r * n) : ℝ) / 2 ^ (2 ^ r * n) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hposL (by norm_num)]
      exact_mod_cast (by linarith : M.acceptCoins (enc a) (2 ^ r * n) * 3 ≤ 1 * 2 ^ (2 ^ r * n))
    have hlt : (M.acceptNisanSeeds (enc a) n r : ℝ) / 2 ^ (n + r * (3 * n - 1)) < 1 / 2 := by
      linarith [herr.2]
    rw [div_lt_div_iff₀ hpos (by norm_num)] at hlt
    exact_mod_cast (by linarith : 2 * (M.acceptNisanSeeds (enc a) n r : ℝ) <
      2 ^ (n + r * (3 * n - 1)))

end Cslib.Complexity
