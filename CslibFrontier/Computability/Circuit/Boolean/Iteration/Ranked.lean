/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Scan
import CslibFrontier.Computability.Circuit.Boolean.Iteration.Decoder
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Fixed powers from ranked checkpoints

A circuit for the rank of a state lets us find the least rank on an orbit prefix of length
`K = 2 * L` by a linear scan. A second scan selects the state at the winning position in the
first half of the prefix or the state `L` steps before it in the second half. When the prefix
is injective, the coverage hypothesis puts this state in the domain of a single circuit for
the pre-shifted power. Reusing the same selection flags chooses the matching correction time
even when several states have the same rank.

If two prefix states coincide, the state at time `K` returns to itself within `K` steps.
For each candidate return time `p`, the exponent and `p` are circuit parameters, so the
corresponding output is wired directly to the suffix at time `K + (T - K) % p`.
The resulting gate count charges the transition, rank and payload circuits.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n w K : ℕ}

/-- Flag every position attaining the lexicographically least rank; ties are retained. -/
noncomputable def leastRankFlag (ranks : Fin K → BitString w) (first : Fin K)
    (i : Fin K) : Bool :=
  decide (ranks i = @scanMin _ (lexOrder w) _ ranks (ranks first) K)

/-- At least one position is flagged and each flagged position attains the least rank. -/
theorem leastRankFlag_spec (ranks : Fin K → BitString w) (first : Fin K) :
    (∃ i, leastRankFlag ranks first i = true) ∧
      ∀ i, leastRankFlag ranks first i = true → ∀ j, toLex (ranks i) ≤ toLex (ranks j) := by
  let := lexOrder w
  obtain ⟨h1, _, hmin⟩ := scanMin_spec ranks (ranks first) K
  exact ⟨h1.elim (fun he => ⟨first, decide_eq_true he.symm⟩) fun ⟨i, _, he⟩ =>
      ⟨i, decide_eq_true he.symm⟩,
    fun i hi j => (of_decide_eq_true (p := ranks i = scanMin ranks (ranks first) K) hi) ▸
      hmin j j.isLt⟩

/-- Evaluate the rank circuit once per supplied state, scan for the minimum and share its
comparison with every rank. The flags can drive any number of subsequent priority scans. -/
theorem synthesis_leastRankFlag {a : ℕ} (s : Set (BooleanFunction a)) (q : Circuit signature n w)
    (states : BitString a → Fin K → BitString n) (first : Fin K)
    (hs : ∀ j bit, (fun x => states x j bit) ∈ s) :
    Synthesis interpretation s
      (Set.range fun j x => leastRankFlag (fun i => q.eval interpretation (states x i)) first j)
      (K * (q.size + 16 * w + 2)) := by
  let ranks := fun x j => q.eval interpretation (states x j)
  let least := fun x => @scanMin _ (lexOrder w) _ (ranks x) (ranks x first) K
  have hr := Synthesis.iUnion (I := interpretation) (fun j => wires fun x => ranks x j)
    (fun _ => q.size) fun j => Synthesis.circuit q (fun i x => states x j i) (hs j)
  let s₁ := s ∪ ⋃ j, wires fun x => ranks x j
  have hwire (j : Fin K) (bit : Fin w) : (fun x => ranks x j bit) ∈ s₁ :=
    Or.inr (Set.mem_iUnion.mpr ⟨j, bit, rfl⟩)
  have hm := synthesis_scanMin s₁ ranks (fun x => ranks x first) hwire (hwire first)
  have he := Synthesis.family (I := interpretation) (s := s₁ ∪ wires least)
    (fun j x => decide (ranks x j = least x)) (fun _ => 6 * w + 1) fun j =>
      synthesis_bits_eq _ (fun x => ranks x j) least
        (by rintro _ ⟨bit, rfl⟩; exact Or.inl (hwire j bit)) (fun _ hb => Or.inr hb)
  refine (hr.trans (hm.trans he)).mono .rfl .rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- Using the same flags for both scans selects the same position even in a tie. -/
private theorem chooseRecord_eq_apply {α : Type*} (flags : Fin K → Bool)
    (rows : Fin K → α) (first : Fin K) :
    chooseRecord flags rows (rows first) K = rows (chooseRecord flags id first K) :=
  (chooseRecord_map rows flags id first K).symm

private def corrected (f payload : BitString n → BitString n) (d : Fin K → ℕ)
    (first : Fin K) (flags : Fin K → Bool) (x : BitString n) : BitString n :=
  let states := fun j => f^[d j] x
  let checkpoint := chooseRecord flags states (states first) K
  let rows := fun j => f^[K - d j] (payload checkpoint)
  chooseRecord flags rows (rows first) K

private theorem corrected_spec (f payload : BitString n → BitString n) (d : Fin K → ℕ)
    (first : Fin K) (flags : Fin K → Bool) (x : BitString n) (T : ℕ) (hT : K ≤ T)
    (hd : ∀ j, d j ≤ K)
    (hp : payload (f^[d (chooseRecord flags id first K)] x) =
      f^[T - K] (f^[d (chooseRecord flags id first K)] x)) :
    corrected f payload d first flags x = f^[T] x := by
  simp only [corrected, chooseRecord_eq_apply, hp, ← Function.iterate_add_apply]
  congr 1
  have := hd (chooseRecord flags id first K)
  lia

private theorem synthesis_corrected (s : Set (BooleanFunction n)) (c p : Circuit signature n n)
    (d : Fin K → ℕ) (first : Fin K) (flags : BitString n → Fin K → Bool)
    (hf : ∀ j, (fun x => flags x j) ∈ s) (hd : ∀ j, d j ≤ K)
    (hs : ∀ j ≤ K, ∀ bit, (fun x => (c.eval interpretation)^[j] x bit) ∈ s) :
    Synthesis interpretation s
      (wires fun x => corrected (c.eval interpretation) (p.eval interpretation) d first (flags x) x)
      (K * (c.size + 8 * n) + p.size) := by
  let f := c.eval interpretation
  let states := fun x j => f^[d j] x
  let checkpoint := fun x => chooseRecord (flags x) (states x) (states x first) K
  let seed := fun x => p.eval interpretation (checkpoint x)
  have hcp := synthesis_chooseRecord s flags states (fun x => states x first) hf
    (fun j => hs _ (hd j)) (hs _ (hd first))
  have hseed := Synthesis.circuit (I := interpretation) (s := s ∪ wires checkpoint) p
    (fun i x => checkpoint x i) fun i => Or.inr ⟨i, rfl⟩
  let s₂ := s ∪ wires checkpoint ∪ wires seed
  let trace := Synthesis.stages (fun j => wires fun x => f^[j] (seed x)) K
  have hw (j : Fin K) (bit : Fin n) : (fun x => f^[K - d j] (seed x) bit) ∈ s₂ ∪ trace :=
    Or.inr (Synthesis.subset_stages _ (Nat.sub_le K (d j)) ⟨bit, rfl⟩)
  have hout := synthesis_chooseRecord (s₂ ∪ trace) flags (fun x j => f^[K - d j] (seed x))
    (fun x => f^[K - d first] (seed x)) (fun j => Or.inl (Or.inl (Or.inl (hf j)))) hw (hw first)
  exact (hcp.trans (hseed.trans ((Synthesis.orbit c seed (fun i => Or.inr ⟨i, rfl⟩) K).trans
    hout))).mono .rfl .rfl (le_of_eq (by ring))

private def returnFlag (f : BitString n → BitString n) (x : BitString n) (j : Fin K) : Bool :=
  decide (f^[j.val + 1 + K] x = f^[K] x)

private def finish (f : BitString n → BitString n) (T K : ℕ) (x fallback : BitString n) :
    BitString n :=
  chooseRecord (returnFlag f x) (fun j : Fin K => f^[(T - K) % (j.val + 1) + K] x) fallback K

private theorem finish_of_return (f : BitString n → BitString n) (x fallback : BitString n)
    {T : ℕ} (hT : K ≤ T) (hret : ∃ j : Fin K, returnFlag f x j = true) :
    finish f T K x fallback = f^[T] x := by
  obtain ⟨j, hj⟩ := hret
  obtain ⟨i, _, hi, he⟩ := chooseRecord_spec (returnFlag f x)
    (fun j : Fin K => f^[(T - K) % (j.val + 1) + K] x) fallback K ⟨j, j.isLt, hj⟩
  have hperiod : Function.IsPeriodicPt f (i.val + 1) (f^[K] x) := by
    simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Function.iterate_add_apply] using
      of_decide_eq_true hi
  rw [finish, he, Function.iterate_add_apply, hperiod.iterate_mod_apply,
    ← Function.iterate_add_apply, Nat.sub_add_cancel hT]

/-- If the state at time `K` has no positive return within `K` further steps, the initial
prefix of `K` states is simple. -/
theorem injective_of_no_return_period (f : BitString n → BitString n) (x : BitString n)
    (hret : ¬ ∃ j : Fin K, f^[j.val + 1] (f^[K] x) = f^[K] x) :
    Function.Injective (fun i : Fin K => f^[i.val] x) := by
  have hlt {i j : Fin K} (hij : i.val < j.val) (he : f^[i.val] x = f^[j.val] x) : False := by
    have hperiod : Function.IsPeriodicPt f (j.val - i.val) (f^[i.val] x) := by
      simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hij.le] using he.symm
    have h := hperiod.apply_iterate (K - i.val)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel i.isLt.le] at h
    have hj := j.isLt
    exact hret ⟨⟨j.val - i.val - 1, by lia⟩,
      by simpa [show j.val - i.val - 1 + 1 = j.val - i.val by lia] using h.eq⟩
  intro i j he
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  exacts [(hlt hij he).elim, Fin.ext hij, (hlt hij he.symm).elim]

private theorem synthesis_finish (s : Set (BooleanFunction n)) (f : BitString n → BitString n)
    (T K : ℕ) (fallback : BitString n → BitString n) (hb : wires fallback ⊆ s)
    (hs : ∀ i ≤ 2 * K, ∀ bit, (fun x => f^[i] x bit) ∈ s) :
    Synthesis interpretation s (wires fun x => finish f T K x (fallback x)) (K * (10 * n + 1)) := by
  have hflag := Synthesis.family (I := interpretation) (s := s)
    (fun j : Fin K => fun x => returnFlag f x j) (fun _ => 6 * n + 1) fun j =>
      synthesis_bits_eq s (fun x => f^[j.val + 1 + K] x) (fun x => f^[K] x)
        (by rintro _ ⟨bit, rfl⟩; exact hs _ (by have := j.isLt; lia) bit)
        (by rintro _ ⟨bit, rfl⟩; exact hs K (by lia) bit)
  have hout := synthesis_chooseRecord (s ∪ Set.range fun j x => returnFlag f x j)
    (fun x (j : Fin K) => returnFlag f x j) (fun x j => f^[(T - K) % (j.val + 1) + K] x)
    fallback (fun j => Or.inr ⟨j, rfl⟩)
    (fun j bit => Or.inl (hs _ (by
      have := Nat.mod_lt (T - K) j.val.succ_pos
      have := j.isLt
      lia) bit))
    fun bit => Or.inl (hb ⟨bit, rfl⟩)
  refine (hflag.trans hout).mono .rfl .rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- A fixed power from a rank circuit and a circuit computing the pre-shifted payload on `H`.
For an injective prefix of length `2 * L`, each least-ranked position must give a checkpoint in
`H` by taking its state in the first half or the state `L` steps earlier in the second half.
The rank circuit is evaluated once per position and the payload circuit once per input. -/
theorem fixed_power_of_ranked_checkpoints (c : Circuit signature n n) (q : Circuit signature n w)
    (p : Circuit signature n n) (X H : Set (BitString n)) (T L : ℕ) (hL : 0 < L)
    (hcover : ∀ x ∈ X, Function.Injective (fun i : Fin (2 * L) =>
        (c.eval interpretation)^[i.val] x) → ∀ i : Fin (2 * L),
      (∀ j : Fin (2 * L),
        toLex (q.eval interpretation ((c.eval interpretation)^[i.val] x)) ≤
          toLex (q.eval interpretation ((c.eval interpretation)^[j.val] x))) →
      (c.eval interpretation)^[if i.val < L then i.val else i.val - L] x ∈ H)
    (hp : p.ComputesOn interpretation H (c.eval interpretation)^[T - 2 * L]) :
    ∃ out : Circuit signature n n, out.ComputesOn interpretation X (c.eval interpretation)^[T] ∧
      out.size ≤ 2 * L * (3 * c.size + q.size + 16 * w + 18 * n + 3) + p.size := by
  let K := 2 * L
  let f := c.eval interpretation
  by_cases hT : K ≤ T
  · let first : Fin K := ⟨0, by dsimp [K]; lia⟩
    let states := fun x (j : Fin K) => f^[j.val] x
    let ranks := fun x j => q.eval interpretation (states x j)
    let d := fun j : Fin K => if j.val < L then j.val else j.val - L
    let flags := fun x => leastRankFlag (ranks x) first
    let fallback := fun x => corrected f (p.eval interpretation) d first (flags x) x
    have hd (j : Fin K) : d j ≤ K := by
      have := j.isLt
      dsimp only [d]
      split <;> lia
    have htrace : Synthesis interpretation (inputs n) (prefixWires f (2 * K))
        (2 * K * c.size) := Synthesis.orbit (s := inputs n) c id (fun i => ⟨i, rfl⟩) (2 * K)
    let s₁ := inputs n ∪ prefixWires f (2 * K)
    have hs (j : ℕ) (hj : j ≤ 2 * K) (bit : Fin n) : (fun x => f^[j] x bit) ∈ s₁ :=
      Or.inr (prefix_mem f hj bit)
    have hr := synthesis_leastRankFlag s₁ q states first fun j => hs _ (by have := j.isLt; lia)
    let s₂ := s₁ ∪ Set.range fun j x => flags x j
    have hc := synthesis_corrected s₂ c p d first flags (fun j => Or.inr ⟨j, rfl⟩) hd
      fun j hj bit => Or.inl (hs _ (by lia) bit)
    have hout := synthesis_finish (s₂ ∪ wires fallback) f T K fallback (fun _ hb => Or.inr hb)
      fun j hj bit => Or.inl (Or.inl (hs j hj bit))
    obtain ⟨out, heval, hsize⟩ :=
      (htrace.trans (hr.trans (hc.trans hout))).exists_circuit_outputs
    refine ⟨out, fun x hx => ?_, hsize.trans (le_of_eq ?_)⟩
    · rw [heval x]
      change finish f T K x (fallback x) = f^[T] x
      by_cases hret : ∃ j : Fin K, returnFlag f x j = true
      · exact finish_of_return f x (fallback x) hT hret
      · rw [finish, chooseRecord_of_forall_eq_false _ _ _ (fun j =>
          Bool.eq_false_iff.mpr fun hj => hret ⟨j, hj⟩)]
        obtain ⟨⟨j, hj⟩, hmin⟩ := leastRankFlag_spec (ranks x) first
        obtain ⟨i, _, hi, hchosen⟩ := chooseRecord_spec (flags x) id first K ⟨j, j.isLt, hj⟩
        apply corrected_spec f _ d first (flags x) x T hT hd
        rw [hchosen]
        have hsimple := injective_of_no_return_period f x (K := K)
          (by simpa only [returnFlag, decide_eq_true_eq, Function.iterate_add_apply] using hret)
        exact hp (hcover x hx hsimple i (hmin i hi))
    · dsimp only [K]
      ring
  · refine ⟨c.iterate T, fun x _ => congrFun (c.eval_iterate interpretation T) x, ?_⟩
    rw [Circuit.size_iterate]
    have h := Nat.mul_le_mul_right c.size (Nat.le_of_not_ge hT)
    change _ ≤ K * _ + _
    exact h.trans ((Nat.mul_le_mul_left K (by lia)).trans (Nat.le_add_right _ _))

end Cslib.Circuits.Boolean.Iteration
