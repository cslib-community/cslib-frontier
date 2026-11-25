/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Depth
import CslibFrontier.Tactic.LinarithCast

/-!
# Circuits for first targets and halting

Let `c` compute `f` on `n`-bit states and let a circuit `p` recognize a target set. Stopping at
targets is computed by a circuit of size `c.size + p.size + 4 * n` (`absorbing_circuit`), and
`2 ^ n` steps of it reach the first target of every orbit that has one
(`FunctionalGraph.absorb_iterate_card`). With the fixed-power bound this gives the first target
state (`first_target_state`) and whether a target is ever reached (`target_reachability`). When
the halting states are fixed by `f` itself, `2 ^ n` steps of `f` reach the halting configuration
of every halting computation, and no recognizer is charged (`halting_computation`).

The first visit to a target is the transient depth of the map that stops at targets
(`FunctionalGraph.first_target_depth`), so the depth circuits give a reachability flag and the
exact first target time (`first_target_time`, `first_target_time_optimized`), and the first
halting time (`halting_time`).

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. They exist for each parameter choice; nothing here
bounds the time to construct them. For halting computations the state holds every persistent
bit of the computation, including its input and workspace.

## Main results

* `Cslib.Circuits.Boolean.Iteration.absorbing_circuit`: stopping at recognized targets.
* `Cslib.Circuits.Boolean.Iteration.first_target_state`,
  `Cslib.Circuits.Boolean.Iteration.target_reachability`: first targets and reachability.
* `Cslib.Circuits.Boolean.Iteration.halting_computation`: final configurations.
* `Cslib.Circuits.Boolean.Iteration.first_target_time`,
  `Cslib.Circuits.Boolean.Iteration.first_target_time_optimized`: first target times.
* `Cslib.Circuits.Boolean.Iteration.halting_time`: first halting times.

## References

* Adapted from lean/Proofs/{Targets,TargetTimes}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions], whose
  first-time and halting-time bounds have the constants `3120000` and `3000000`.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n : ℕ}

/-- **Absorbing targets.** The map that stops at states accepted by `p` and otherwise applies
`c` has a circuit of size at most `c.size + p.size + 4 * n`. -/
theorem absorbing_circuit (c : Circuit signature n n) (p : Circuit signature n 1) :
    ∃ g : Circuit signature n n,
      g.Computes interpretation
        (absorb (c.eval interpretation) fun x => p.eval interpretation x 0 = true) ∧
      g.size ≤ c.size + p.size + 4 * n := by
  have hc := Synthesis.circuit (I := interpretation) (s := inputs n) c (fun i x => x i)
    fun i => ⟨i, rfl⟩
  have hp : Synthesis interpretation (inputs n) {fun x => p.eval interpretation x 0} p.size :=
    (Synthesis.circuit (I := interpretation) (s := inputs n) p (fun i x => x i)
      fun i => ⟨i, rfl⟩).mono Set.Subset.rfl (by rintro _ rfl; exact ⟨0, rfl⟩) le_rfl
  have hi : Synthesis interpretation (inputs n) (wires fun x : BitString n => x) 0 :=
    Synthesis.of_subset Set.Subset.rfl
  obtain ⟨g, hg, hs⟩ := (synthesis_ite hi hc hp).exists_circuit_outputs
  refine ⟨g, fun x => ?_, by simpa using hs⟩
  rw [hg x]
  by_cases hx : p.eval interpretation x 0 = true <;> simp [absorb, hx]

/-- **First target states.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`40000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L` returns a state accepted by `p`
exactly when the orbit of its input ever reaches one, and then returns the first such state,
reached before time `2 ^ n`. -/
theorem first_target_state (c : Circuit signature n n) (p : Circuit signature n 1) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      (∀ x, p.eval interpretation (out.eval interpretation x) 0 = true ↔
        ∃ t, p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      (∀ x, (∃ t, p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) →
        ∃ t < 2 ^ n, out.eval interpretation x = (c.eval interpretation)^[t] x ∧
          p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true ∧
          ∀ j < t, p.eval interpretation ((c.eval interpretation)^[j] x) 0 ≠ true) ∧
      out.size ≤ 40000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L := by
  let f := c.eval interpretation
  let P := fun x => p.eval interpretation x 0 = true
  obtain ⟨g, hg, hgs⟩ := absorbing_circuit c p
  obtain ⟨out, hout, hs⟩ := fixed_power n g (2 ^ n) L hL hLN
  have hcard : Fintype.card (BitString n) = 2 ^ n := by simp
  have ho (x) : out.eval interpretation x = (absorb f P)^[Fintype.card (BitString n)] x := by
    rw [hout x, hcard]
    congr 1
    exact funext hg
  refine ⟨out, fun x => ?_, fun x hx => ?_, hs.trans ?_⟩
  · rw [ho x]
    exact absorb_iterate_card_eq_iff f P x
  · obtain ⟨t, ht, hp, hfirst, heq⟩ := absorb_iterate_card f P x hx
    exact ⟨t, hcard ▸ ht, (ho x).trans heq, hp, hfirst⟩
  · unfold powerBudget
    gcongr

/-- **Target reachability.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`40000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size` decides whether the orbit
of its input ever reaches a state accepted by `p`. -/
theorem target_reachability (c : Circuit signature n n) (p : Circuit signature n 1) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n 1,
      (∀ x, out.eval interpretation x 0 = true ↔
        ∃ t, p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      out.size ≤ 40000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size := by
  obtain ⟨state, hp, -, hs⟩ := first_target_state c p L hL hLN
  refine ⟨p.comp state, ?_, ?_⟩
  · simpa only [Circuit.eval_comp] using hp
  · rw [Circuit.size_comp]
    omega

/-- **Halting computations.** If `c` fixes every halting state and the orbit of every initial
state halts, then for every `0 < L ≤ 2 ^ n` some circuit of size at most
`40000 * powerBudget n c.size (2 ^ n) L` returns the halting state of every initial state, first
reached before time `2 ^ n`. No circuit recognizing halting states is needed. -/
theorem halting_computation (c : Circuit signature n n) (H : BitString n → Prop)
    (initial : Set (BitString n)) (hstop : ∀ x, H x → c.eval interpretation x = x)
    (hhalt : ∀ x ∈ initial, ∃ t, H ((c.eval interpretation)^[t] x)) (L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      (∀ x ∈ initial, H (out.eval interpretation x) ∧
        ∃ t < 2 ^ n, out.eval interpretation x = (c.eval interpretation)^[t] x ∧
          ∀ j < t, ¬H ((c.eval interpretation)^[j] x)) ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by
  classical
  let f := c.eval interpretation
  have ha : absorb f H = f := funext fun x => by
    by_cases hx : H x
    · simp only [absorb, hx, ite_true]; exact (hstop x hx).symm
    · simp only [absorb, hx, ite_false]
  obtain ⟨out, hout, hs⟩ := fixed_power n c (2 ^ n) L hL hLN
  refine ⟨out, fun x hx => ?_, hs⟩
  obtain ⟨t, ht, hp, hfirst, he⟩ := absorb_iterate_card f H x (hhalt x hx)
  have hcard : Fintype.card (BitString n) = 2 ^ n := by simp
  rw [ha, hcard] at he
  have ho : out.eval interpretation x = f^[t] x := (hout x).trans he
  exact ⟨ho ▸ hp, t, hcard ▸ ht, ho, hfirst⟩

/-- **First target times.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`90000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size` returns a flag, set exactly
when the orbit of its input reaches a state accepted by `p`, followed by `n + 2` bits. When the
flag is set they are the first time a target is visited, which is below `2 ^ n`; otherwise
nothing is claimed about them. -/
theorem first_target_time (c : Circuit signature n n) (p : Circuit signature n 1) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n (1 + (n + 2)),
      (∀ x, out.eval interpretation x 0 = true ↔
        ∃ t, p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      (∀ x, out.eval interpretation x 0 = true →
        let t := (BitString.equivBitVec fun i : Fin (n + 2) =>
          out.eval interpretation x (Fin.natAdd 1 i)).toNat
        p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true ∧
          (∀ j < t, p.eval interpretation ((c.eval interpretation)^[j] x) 0 ≠ true) ∧ t < 2 ^ n) ∧
      out.size ≤ 90000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size := by
  let f := c.eval interpretation
  let P := fun x => p.eval interpretation x 0 = true
  obtain ⟨g, hg, hgs⟩ := absorbing_circuit c p
  have he : g.eval interpretation = absorb f P := funext hg
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit g L hL hLN
  obtain ⟨flag, hf, hfs⟩ := target_reachability c p L hL hLN
  refine ⟨flag.append depth, ?_, ?_, ?_⟩
  · intro x
    rw [Circuit.eval_append]
    exact hf x
  · intro x hx
    rw [Circuit.eval_append] at hx
    have hex := (hf x).mp hx
    have hb : transientDepth (absorb f P) x < 2 ^ n := by
      simpa using transientDepth_lt_card (absorb f P) x
    have ht : (BitString.equivBitVec fun i : Fin (n + 2) =>
        (flag.append depth).eval interpretation x (Fin.natAdd 1 i)).toNat =
        transientDepth (absorb f P) x := by
      simp only [Circuit.eval_append, Fin.append_right, hd, he, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (hb.trans (Nat.pow_lt_pow_right (by decide) (by omega)))
    dsimp only
    rw [ht]
    exact ⟨(first_target_depth f P x hex).1, (first_target_depth f P x hex).2, hb⟩
  · have hb : powerBudget n g.size (2 ^ n) L ≤
        powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L := by
      unfold powerBudget
      gcongr
    rw [Circuit.size_append]
    omega

/-- **Square-root first target times.** Some circuit of size at most
`180000 * optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) + p.size` returns the
reachability flag and, when it is set, the first target time, as in `first_target_time`. -/
theorem first_target_time_optimized (c : Circuit signature n n) (p : Circuit signature n 1) :
    ∃ out : Circuit signature n (1 + (n + 2)),
      (∀ x, out.eval interpretation x 0 = true ↔
        ∃ t, p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true) ∧
      (∀ x, out.eval interpretation x 0 = true →
        let t := (BitString.equivBitVec fun i : Fin (n + 2) =>
          out.eval interpretation x (Fin.natAdd 1 i)).toNat
        p.eval interpretation ((c.eval interpretation)^[t] x) 0 = true ∧
          (∀ j < t, p.eval interpretation ((c.eval interpretation)^[j] x) 0 ≠ true) ∧ t < 2 ^ n) ∧
      (out.size : ℝ) ≤
        180000 * optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) + p.size := by
  obtain ⟨L, hL, hLN, hopt⟩ :=
    exists_powerBudget_le_optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) le_rfl
  obtain ⟨out, hf, ht, hs⟩ := first_target_time c p L hL hLN
  refine ⟨out, hf, ht, ?_⟩
  cast_linarith [hs]

/-- **Halting times.** If `c` fixes every halting state and the orbit of every initial state
halts, some circuit of size at most `100000 * optimizedBudget n c.size (2 ^ n)` returns, in
`n + 2` bits, the first halting time of every initial state, which is below `2 ^ n`. No circuit
recognizing halting states is needed. -/
theorem halting_time (c : Circuit signature n n) (H : BitString n → Prop)
    (initial : Set (BitString n)) (hstop : ∀ x, H x → c.eval interpretation x = x)
    (hhalt : ∀ x ∈ initial, ∃ t, H ((c.eval interpretation)^[t] x)) :
    ∃ out : Circuit signature n (n + 2),
      (∀ x ∈ initial, let t := (BitString.equivBitVec (out.eval interpretation x)).toNat
        H ((c.eval interpretation)^[t] x) ∧ (∀ j < t, ¬H ((c.eval interpretation)^[j] x)) ∧
          t < 2 ^ n) ∧
      (out.size : ℝ) ≤ 100000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨out, ho, hs⟩ := checkpoint_depth_optimized c
  refine ⟨out, fun x hx => ?_, hs⟩
  have hb : transientDepth (c.eval interpretation) x < 2 ^ n := by
    simpa using transientDepth_lt_card (c.eval interpretation) x
  dsimp only
  rw [ho, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (hb.trans (Nat.pow_lt_pow_right (by decide) (by omega)))]
  exact ⟨(halting_depth _ H hstop x (hhalt x hx)).1, (halting_depth _ H hstop x (hhalt x hx)).2,
    hb⟩

end Cslib.Circuits.Boolean.Iteration
