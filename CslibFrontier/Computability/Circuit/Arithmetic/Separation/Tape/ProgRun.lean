/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Run
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.ReduceOption

/-!
# From programs to runs

A program (a rational series on the channels) is turned into a finite automaton whose matched runs
emit the letters of the program and then pad with idle (`none`) steps.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.ProgRun`.

## Main results

* `Tape.exists_run`: a rational series gives an automaton whose `runVal` sums `hat P (tup W u)`.
* `Tape.exists_run_val`: a bounded program is realized by an automaton of dimension `≤ n + 3`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset Cslib.Automata.Weighted

theorem sum_length_tup {Γ S J : Type*} [Fintype S] [Fintype J]
    (W : S → List Γ) (u : J → List Γ) :
    ∑ z, (tup W u z).length = 2 * ∑ s, (W s).length + ∑ j, (u j).length := by
  rw [Fintype.sum_equiv (chSumEquiv S J) _
    (Sum.elim (fun x : S × Bool => (W x.1).length) fun j => (u j).length)
    fun z => by cases z <;> rfl,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.mul_sum]
  simp [two_mul]

private theorem ofFn_getElem? {Ω : Type*} (w : List Ω) (t : ℕ) (h : w.length ≤ t) :
    List.ofFn (fun k : Fin t => w[(k : ℕ)]?) =
      w.map some ++ List.replicate (t - w.length) none := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    rw [List.getElem_ofFn]
    by_cases hk : k < w.length
    · rw [List.getElem_append_left (by simpa using hk)]
      simp [hk]
    · rw [List.getElem_append_right (by simpa using hk)]
      simp; omega

theorem emit_idle {Γ S J : Type*} [DecidableEq S] [DecidableEq J]
    (w : List (Ch S J × Γ)) (j : ℕ) :
    emit (w.map some ++ List.replicate j none) = proj w := by
  rw [emit, List.reduceOption_append]
  simp [List.reduceOption]

section Runs

variable {F Γ S J : Type*} [CommRing F] [Fintype Γ] [DecidableEq Γ]
  [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]

/-- **From programs to runs.** A rational series of dimension at most `n` gives an automaton of
dimension at most `n + 3` whose value on runs of length `t ≥ 1` matches `hat P` summed over
tape contents fitting inside `t` steps. -/
theorem exists_run {n : ℕ} {P : Series F (Ch S J × Γ)} (hP : RatLe n P) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S J Γ → Matrix Q Q F)
      (i e : Q), Fintype.card Q ≤ n + 3 ∧ ∀ t, 1 ≤ t → ∀ u : J → List Γ,
        runVal mu i e t u =
          ∑ W ∈ (contents S Γ t).filter
              (fun W => 2 * ∑ s, (W s).length + ∑ j, (u j).length ≤ t),
            hat P (tup W u) := by
  obtain ⟨Q, i1, i2, mu, i, e, hcard, hmu⟩ := hP.idle.normal
  refine ⟨Q, i1, i2, mu, i, e, hcard, fun t ht u => ?_⟩
  have hne (o : Fin t → Letter S J Γ) (h : List.ofFn o = []) : False := by
    have := congrArg List.length h
    simp at this; omega
  rw [runVal, Finset.sum_congr rfl fun o _ => by rw [hmu _ (hne o)]]
  simp only [hat]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_of_injOn (fun x k => x.2[(k : ℕ)]?) ?_ (by simp) ?_ ?_
  · rintro ⟨W, w⟩ hx ⟨W', w'⟩ hx' h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_fib] at hx hx'
    obtain ⟨⟨-, hb⟩, hp⟩ := hx
    obtain ⟨⟨-, hb'⟩, hp'⟩ := hx'
    have l1 : w.length ≤ t := by rwa [← sum_length_proj w, hp, sum_length_tup]
    have l2 : w'.length ≤ t := by rwa [← sum_length_proj w', hp', sum_length_tup]
    obtain rfl : w = w' := List.ext_getElem? fun k => by
      by_cases hk : k < t
      · exact congrFun h ⟨k, hk⟩
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    obtain rfl : W = W' := funext fun s => congrFun (hp.symm.trans hp') (.tp s false)
    rfl
  · intro o _ ho
    by_contra hcon
    have hm : Matched (List.ofFn o) u := of_not_not fun hm => hcon (ite_eq_right hm)
    rw [ite_eq_left hm] at hcon
    obtain ⟨w, j, hw⟩ := idle_ne_zero P _ hcon
    have hlen : w.length + j = t := by simpa using (congrArg List.length hw).symm
    apply ho
    have hproj : proj w = tup (fun s => proj w (.tp s false)) u := by
      rw [Matched, hw, emit_idle] at hm
      funext z
      rcases z with ⟨s, _ | _⟩ | j
      · rfl
      · exact (hm.1 s).symm
      · exact hm.2 j
    have hlen2 := sum_length_proj w
    rw [hproj, sum_length_tup] at hlen2
    refine ⟨⟨fun s => proj w (.tp s false), w⟩, ?_, ?_⟩
    · simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_fib, mem_contents]
      exact ⟨⟨by omega, by omega⟩, hproj⟩
    · apply List.ofFn_injective
      rw [hw, ofFn_getElem? w t (by omega)]
      congr 2
      omega
  · rintro ⟨W, w⟩ hx
    simp only [mem_sigma, mem_filter, mem_fib] at hx
    obtain ⟨⟨-, hb⟩, hp⟩ := hx
    rw [ofFn_getElem? w t (by rwa [← sum_length_proj w, hp, sum_length_tup]), ite_eq_left _,
      idle_apply]
    rw [Matched, emit_idle, hp]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- A bounded rational program is realized by a weighted automaton of dimension at most `n + 3`. -/
theorem exists_run_val {n : ℕ} {P : Series F (Ch S J × Γ)} (hP : RatLe n P) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S J Γ → Matrix Q Q F)
      (i e : Q), Fintype.card Q ≤ n + 3 ∧ ∀ (t₀ t : ℕ) (u : J → List Γ), Bdd t₀ P u →
        2 * t₀ + ∑ j, (u j).length + 1 ≤ t → runVal mu i e t u = val t₀ P u := by
  obtain ⟨Q, i1, i2, mu, i, e, hcard, H⟩ := exists_run hP
  refine ⟨Q, i1, i2, mu, i, e, hcard, fun t₀ t u hb ht => ?_⟩
  rw [H t (by omega) u, val]
  symm
  refine Finset.sum_subset (fun W hW => ?_) fun W _ hW => ?_
  · rw [mem_contents] at hW
    rw [mem_filter, mem_contents]
    omega
  · by_contra hne
    exact hW (mem_contents.2 (hb W hne))

end Runs

end Cslib.Circuits.Arithmetic.Separation.Tape
