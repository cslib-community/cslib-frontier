/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Bounds
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Exist
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The universal automaton is exact

A weighted pointer machine is simulated by a weighted automaton on tapes (M1's tape program
`Uni.emX`, with its series from `Uni.runs_X`). Its value at the input `bits`, counting the
tape contents of total length at most `tU …`, is the sum of the weights of the accepting runs of
the machine, if these are at most `Tm` steps long (`Uni.val_emX_eq_sum_wts`). For the universal
machine on a plain instance `z` of time `τ`, the runs have `O(|z| + τ)` steps, so the series has
the value `pv θ z` on tape contents of length `O((|z| + τ) lg (|z| + τ) ^ 2)`
(`Uni.exists_series_universal`).

## Main results

* `Uni.val_emX_eq_sum_wts`: the value of the tape program of a machine is the sum of the
  weights of its accepting runs.
* `Uni.exists_runs_universalMachine`: the accepting runs of the universal machine.
* `Uni.exists_series_universal`: one series of bounded dimension computes `pv θ z` for every
  plain instance, on contents of quasi-linear length.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition I.1 (its proof: the automaton and the pointer machine are exact); module
  `Paper.UniversalSteps`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Tape Cslib.Automata.Weighted Interpreter

section General

variable {A : Type} [CommRing A] {M K : Type} [Finite M] [Fintype K] [DecidableEq K]
  {P : Mach A M K}

/-- **The tape program of a pointer machine is exact.** If the accepting runs from the input
`bits` are the traces in `R`, each of at most `Tm` steps, then the tape contents of the series
of the program have total length at most `tU … Tm …`, and its value there is the sum of the
weights of the runs. -/
theorem val_emX_eq_sum_wts {S₀ : Series A (Zc K × Sy M K)}
    (h : IsRuns S₀ (emX P) fun x => (x.steps.map fun s => P.wt s.1).prod) {bits : List Bool}
    (R : Finset (List P.Step))
    (hR : ∀ tr, tr ∈ R ↔ Mach.GV (σi P bits) tr) {Tm : ℕ} (hTm : ∀ tr ∈ R, tr.length ≤ Tm) :
    Bdd (tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1))) S₀ (fun _ => bits.map .bit) ∧
      val (tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1))) S₀ (fun _ => bits.map .bit) =
        ∑ tr ∈ R, Mach.wts tr := by
  classical
  have := Fintype.ofFinite M
  have hle (x : XP P) (hx : Mt (emX P) (fun _ => bits.map .bit) x) :
      ∑ s, (emX P x (.tp s true)).length ≤ tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1)) := by
    rw [mt_X] at hx
    have h1 : x.steps.length ≤ Tm := by simpa using hTm _ ((hR _).2 hx.gv)
    rw [hx.total]
    exact tU_mono h1 (hx.size_eq ▸ Nat.size_le_size (by omega))
  refine ⟨h.bdd hle, ?_⟩
  have hex (tr : List P.Step) (htr : tr ∈ R) : ∃ x : XP P, MX x bits ∧ x.steps.map nst = tr := by
    have hgv := (hR tr).1 htr
    have hc := closed_σi P bits
    exact exists_MX hgv fun st hst i => by
      simpa [σi] using ((Mach.gv_iff hc tr).1 hgv).le hc st hst i
  choose f hf using hex
  have hinj : Set.InjOn (fun t : R => f t.1 t.2) (univ : Finset R) := by
    rintro ⟨t, ht⟩ - ⟨t', ht'⟩ - e
    exact Subtype.ext ((hf t ht).2.symm.trans
      ((congrArg (fun x : XP P => x.steps.map nst) e).trans (hf t' ht').2))
  rw [h.val_eq _ _ (univ.image fun t : R => f t.1 t.2), sum_image fun a ha b hb e => hinj ha hb e,
    ← sum_coe_sort R]
  · refine sum_congr rfl fun ⟨tr, htr⟩ _ => ?_
    change _ = (tr.map fun st => P.wt st.1).prod
    conv_rhs => rw [← (hf tr htr).2, List.map_map]
    rfl
  · intro x
    rw [mem_image]
    constructor
    · rintro ⟨⟨tr, htr⟩, -, rfl⟩
      have hx := (mt_X (f tr htr) bits).2 (hf tr htr).1
      exact ⟨hx, hle _ hx⟩
    · rintro ⟨hx, -⟩
      have hx' := (mt_X x bits).1 hx
      have htr : x.steps.map nst ∈ R := (hR _).2 hx'.gv
      exact ⟨⟨_, htr⟩, mem_univ _, MX.unique (hf _ htr).1 hx' (hf _ htr).2⟩

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- **The accepting runs of the universal machine** on a plain instance `z`: a finite set of
traces from the initial state, whose weights sum to `pv θ z`, each of `O(|z| + τ)` steps. -/
theorem exists_runs_universalMachine (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree}
    (h : Plain θ τ z) :
    ∃ R : Finset (List (universalMachine θ supp).Step),
      (∀ tr, tr ∈ R ↔ Mach.GV (initState supp z) tr) ∧ ∑ tr ∈ R, Mach.wts tr = pv θ z ∧
        ∀ tr ∈ R, tr.length ≤ runLength supp τ z.size := by
  obtain ⟨R, h1, h2, h3⟩ := sumTo_universalMachine (supp := supp) hθ h
  have hc : Mach.Closed (initState supp z) := closed_σi (universalMachine θ supp) (tbits z)
  refine ⟨R, fun tr => by rw [h1, Mach.gv_iff hc], h2, fun tr htr => ?_⟩
  have := h3 tr htr
  rw [← natCast_runLength] at this
  exact_mod_cast this

variable (θ supp) in
/-- **The universal automaton is exact, in quasi-linear time.** One series of dimension
`dimX (universalMachine θ supp)` has, at the word of every plain instance `z` of time `τ`, the
value `pv θ z`, counting tape contents of total length `O((|z| + τ) lg (|z| + τ) ^ 2)`. -/
theorem exists_series_universal (hθ : ∀ q, q ∉ supp → θ q = 0) :
    ∃ S₀ : Series A (Zc RecKind × Sy (Mode (Name supp)) RecKind),
      RatLe (dimX (universalMachine θ supp)) S₀ ∧ ∃ C : ℕ, ∀ (τ : ℕ) (z : Tree), Plain θ τ z →
        Bdd (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) S₀
            (fun _ => (tbits z).map .bit) ∧
          val (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) S₀
            (fun _ => (tbits z).map .bit) = pv θ z := by
  obtain ⟨S₀, h1, h2⟩ := runs_X (universalMachine θ supp)
  set c := 41 + 2 * nameLength supp
  set d := Nat.size c + 2
  refine ⟨S₀, h1, (50 + Fintype.card (Bl RecKind)) * (c * d ^ 2), fun τ z hz => ?_⟩
  obtain ⟨R, r1, r2, r3⟩ := exists_runs_universalMachine (supp := supp) hθ hz
  obtain ⟨a1, a2⟩ := val_emX_eq_sum_wts h2 R r1 r3
  set N := z.size + τ + 2
  have hT : runLength supp τ z.size + 1 ≤ c * N := by
    have := Tree.size_pos z
    simp only [runLength, c, N]
    nlinarith [Nat.zero_le (nameLength supp * z.size), Nat.zero_le (nameLength supp)]
  have hL : Nat.size (runLength supp τ z.size + 1) + 1 ≤ d * lg N := by
    have h3 : Nat.size (runLength supp τ z.size + 1) ≤ Nat.size c + lg N :=
      (Nat.size_le_size hT).trans
        ((Nat.size_mul_le c N).trans (Nat.add_le_add_left (Nat.size_le_log_two_add_one N) _))
    have hlg : 1 ≤ lg N := Nat.le_add_left 1 _
    have h4 : Nat.size c ≤ Nat.size c * lg N := Nat.le_mul_of_pos_right _ hlg
    simp only [d]
    nlinarith
  have ht : tU (Fintype.card (Bl RecKind)) (runLength supp τ z.size)
      (Nat.size (runLength supp τ z.size + 1)) ≤
        (50 + Fintype.card (Bl RecKind)) * (c * d ^ 2) * (N * lg N ^ 2) :=
    (tU_le _ _ _).trans (by
      calc _ ≤ (50 + Fintype.card (Bl RecKind)) * (c * N * (d * lg N) ^ 2) := by gcongr
        _ = _ := by ring)
  exact ⟨fun W hW => (a1 W hW).trans ht, by rw [val_eq_of_bdd a1 ht, a2, r2]⟩

end Cslib.Circuits.Arithmetic.Separation.Uni
