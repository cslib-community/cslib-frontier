/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Pebbling.Basic

/-!
# Path blocking and lower bounds for the black pebble game

A configuration `P` blocks a vertex `v` when every path from a source to `v` meets `P`.
`Unblocked G P v` is the complement: some source path into `v` avoids `P`. The predicate
`ForcesPebbles G R v n` says that every legal run that starts with `v` unblocked and later pebbles
`v` passes, strictly after its start, through a configuration with at least `n` pebbles on the
region `R`. Blocking is Definition 4.9 of [Nordstrom2015Survey]; the invariant `ForcesPebbles`
is this library's own formulation of the path-blocking argument for Cook's pyramid lower bound
([Cook1974]; [Nordstrom2015Survey], Theorem 4.8), whose written proof argues with converging
paths instead.

## Main definitions

* `Cslib.Pebbling.Unblocked G P v`: some path from a source to `v` avoids `P`.
* `Cslib.Pebbling.ForcesPebbles G R v n`: pebbling `v` from an unblocked start forces `n`
  simultaneous pebbles on `R`.

## Main results

* `Cslib.Pebbling.forcesPebbles_one`, `Cslib.Pebbling.forcesPebbles_three`: the base cases.
* `Cslib.Pebbling.ForcesPebbles.step`: the inductive step for a vertex with exactly two
  predecessors, given blocking information about the two predecessor regions.
* `Cslib.Pebbling.ForcesPebbles.le_of_blackPebblable`: forced pebbles bound every successful
  budget from below.

## References

* [S. A. Cook, *An observation on time-storage trade off*][Cook1974].
* [J. Nordström, *New wine into old wineskins*][Nordstrom2015Survey], Definition 4.9 and
  Theorem 4.8.
-/

public section

namespace Cslib.Pebbling

/-! ## Blocking and the lower-bound engine -/

section Blocking

variable {V : Type*} (G : Digraph V)

/-- `Unblocked G P v`: some path from a source of `G` to `v` avoids `P`. -/
inductive Unblocked (P : Finset V) : V → Prop where
  /-- An unpebbled source is unblocked. -/
  | source {v : V} (hsrc : ∀ u, ¬ G.Adj u v) (hv : v ∉ P) : Unblocked P v
  /-- An unpebbled successor of an unblocked vertex is unblocked. -/
  | step {u v : V} (hu : Unblocked P u) (huv : G.Adj u v) (hv : v ∉ P) : Unblocked P v

variable {G}

theorem Unblocked.notMem {P : Finset V} {v : V} (h : Unblocked G P v) : v ∉ P := by
  cases h <;> assumption

theorem Unblocked.exists_adj {P : Finset V} {v u₀ : V} (h : Unblocked G P v) (hu₀ : G.Adj u₀ v) :
    ∃ u, G.Adj u v ∧ Unblocked G P u := by
  cases h with
  | source hsrc _ => exact absurd hu₀ (hsrc u₀)
  | step hu huv _ => exact ⟨_, huv, hu⟩

theorem unblocked_empty (hG : WellFounded G.Adj) (v : V) : Unblocked G ∅ v := by
  induction v using hG.induction with
  | _ v ih =>
    by_cases h : ∃ u, G.Adj u v
    · obtain ⟨u, hu⟩ := h
      exact .step (ih u hu) hu (Finset.notMem_empty v)
    · exact .source (fun u hu => h ⟨u, hu⟩) (Finset.notMem_empty v)

variable [DecidableEq V]

variable (G) in
/-- Every legal pebbling that starts with an unblocked path to `v` and later pebbles `v` passes,
strictly after its start, through a configuration with at least `n` pebbles on `R`. -/
def ForcesPebbles (R : Set V) (v : V) (n : ℕ) : Prop :=
  ∀ (C : ℕ → Finset V) (t₀ t₁ : ℕ), t₀ ≤ t₁ →
    (∀ t, t₀ ≤ t → t < t₁ → ∃ m, BlackStep G (C t) m (C (t + 1))) →
    Unblocked G (C t₀) v → v ∈ C t₁ →
    ∃ t, t₀ < t ∧ t ≤ t₁ ∧ ∃ S : Finset V, S ⊆ C t ∧ ↑S ⊆ R ∧ n ≤ S.card

private theorem exists_flip {p : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : ¬ p a) (hb : p b) :
    ∃ s, a ≤ s ∧ s < b ∧ ¬ p s ∧ p (s + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hb ha
  | succ b hab ih =>
    by_cases hpb : p b
    · obtain ⟨s, h₁, h₂, h₃, h₄⟩ := ih hpb
      exact ⟨s, h₁, by omega, h₃, h₄⟩
    · exact ⟨b, hab, by omega, hpb, hb⟩

private theorem exists_last {p : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : p a) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ p c ∧ ∀ t, c < t → t ≤ b → ¬ p t := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_rfl, le_rfl, ha, by omega⟩
  | succ b hab ih =>
    by_cases hpb : p (b + 1)
    · exact ⟨b + 1, by omega, le_rfl, hpb, by omega⟩
    · obtain ⟨c, h₁, h₂, h₃, h₄⟩ := ih
      exact ⟨c, h₁, by omega, h₃, fun t ht₁ ht₂ =>
        (Nat.lt_or_eq_of_le ht₂).elim (fun ht => h₄ t ht₁ (by omega)) (· ▸ hpb)⟩

/-- Any vertex of `R` forces one pebble on `R`. -/
theorem forcesPebbles_one {R : Set V} {x : V} (hx : x ∈ R) : ForcesPebbles G R x 1 := by
  intro C t₀ t₁ ht _ hu hx₁
  obtain ⟨s, hs₀, hs₁, -, hs⟩ := exists_flip (p := fun t => x ∈ C t) ht hu.notMem hx₁
  exact ⟨s + 1, by omega, by omega, {x}, Finset.singleton_subset_iff.2 hs, by simpa using hx,
    by simp⟩

/-- A vertex with two distinct predecessors in `R` forces three pebbles on `R`. -/
theorem forcesPebbles_three {R : Set V} {x y z : V} (hy : G.Adj y x) (hz : G.Adj z x)
    (hyz : y ≠ z) (hxR : x ∈ R) (hyR : y ∈ R) (hzR : z ∈ R) : ForcesPebbles G R x 3 := by
  intro C t₀ t₁ ht hstep hu hx₁
  obtain ⟨s, hs₀, hs₁, hxs, hxs'⟩ := exists_flip (p := fun t => x ∈ C t) ht hu.notMem hx₁
  obtain ⟨m, hm⟩ := hstep s hs₀ hs₁
  obtain ⟨hpred, hD⟩ := hm.eq_insert_of_mem hxs' hxs
  refine ⟨s + 1, by omega, by omega, {x, y, z}, ?_, by simp [Set.insert_subset_iff, hxR, hyR, hzR],
    (Finset.card_eq_three.2 ⟨x, y, z, fun h => hxs (h ▸ hpred y hy),
      fun h => hxs (h ▸ hpred z hz), hyz, rfl⟩).symm.le⟩
  rw [hD]
  simp [Finset.insert_subset_iff, hpred y hy, hpred z hz]

/-- The inductive step of the path-blocking argument for a vertex `x` whose predecessors are
exactly `y` and `z`. If blocking all paths to `y` puts a pebble on `Rx \ Rz` and blocking all paths
to `z` puts a pebble on `Rx \ Ry`, then `x` forces one more pebble on `Rx` than its predecessors
force on their regions. -/
theorem ForcesPebbles.step {Rx Ry Rz : Set V} {x y z : V} {n : ℕ}
    (hy : G.Adj y x) (hz : G.Adj z x) (hpred : ∀ u, G.Adj u x → u = y ∨ u = z)
    (hRy : Ry ⊆ Rx) (hRz : Rz ⊆ Rx)
    (hby : ∀ P : Finset V, ¬ Unblocked G P y → ∃ w ∈ P, w ∈ Rx ∧ w ∉ Rz)
    (hbz : ∀ P : Finset V, ¬ Unblocked G P z → ∃ w ∈ P, w ∈ Rx ∧ w ∉ Ry)
    (hFy : ForcesPebbles G Ry y n) (hFz : ForcesPebbles G Rz z n) :
    ForcesPebbles G Rx x (n + 1) := by
  intro C t₀ t₁ ht hstep hu hx₁
  obtain ⟨s, hs₀, hs₁, hxs, hxs'⟩ := exists_flip (p := fun t => x ∈ C t) ht hu.notMem hx₁
  obtain ⟨m, hm⟩ := hstep s hs₀ hs₁
  obtain ⟨hpx, -⟩ := hm.eq_insert_of_mem hxs' hxs
  have h₀ : Unblocked G (C t₀) y ∨ Unblocked G (C t₀) z := by
    obtain ⟨u, hux, huU⟩ := hu.exists_adj hy
    exact match hpred u hux with | .inl rfl => .inl huU | .inr rfl => .inr huU
  obtain ⟨c, hc₀, hcs, hc, hlast⟩ :=
    exists_last (p := fun t => Unblocked G (C t) y ∨ Unblocked G (C t) z) hs₀ h₀
  have branch {u v : V} {Ru : Set V} (hRu : Ru ⊆ Rx) (hFu : ForcesPebbles G Ru u n)
      (hcu : Unblocked G (C c) u) (hus : u ∈ C s)
      (hcv : ∀ t, c < t → t ≤ s → ¬ Unblocked G (C t) v)
      (hbv : ∀ P : Finset V, ¬ Unblocked G P v → ∃ w ∈ P, w ∈ Rx ∧ w ∉ Ru) :
      ∃ t, t₀ < t ∧ t ≤ t₁ ∧ ∃ S : Finset V, S ⊆ C t ∧ ↑S ⊆ Rx ∧ n + 1 ≤ S.card := by
    obtain ⟨t, ht₁, ht₂, S, hSC, hSR, hS⟩ :=
      hFu C c s hcs (fun t h₁ h₂ => hstep t (by omega) (by omega)) hcu hus
    obtain ⟨w, hwC, hwx, hwu⟩ := hbv (C t) (hcv t ht₁ ht₂)
    exact ⟨t, by omega, by omega, insert w S, Finset.insert_subset hwC hSC,
      Finset.coe_insert w S ▸ Set.insert_subset hwx (hSR.trans hRu),
      by rw [Finset.card_insert_of_notMem fun h => hwu (hSR h)]; omega⟩
  exact hc.elim
    (fun hcy => branch hRy hFy hcy (hpx y hy) (fun t h₁ h₂ h => hlast t h₁ h₂ (.inr h)) hbz)
    (fun hcz => branch hRz hFz hcz (hpx z hz) (fun t h₁ h₂ h => hlast t h₁ h₂ (.inl h)) hby)

private theorem exists_seq_of_mTr {s : ℕ} {C D : Finset V} {ms : List (Move V)}
    (h : (blackPebbleGame G s).MTr C ms D) :
    ∃ (f : ℕ → Finset V) (N : ℕ), f 0 = C ∧ f N = D ∧
      ∀ t < N, ∃ m, (blackPebbleGame G s).Tr (f t) m (f (t + 1)) := by
  induction h with
  | @refl C => exact ⟨fun _ => C, 0, rfl, rfl, by simp⟩
  | @stepL C₁ m _ _ _ htr _ ih =>
    obtain ⟨f, N, rfl, rfl, hf⟩ := ih
    exact ⟨fun t => Nat.casesOn t C₁ f, N + 1, rfl, rfl,
      fun | 0, _ => ⟨m, htr⟩ | t + 1, ht => hf t (by omega)⟩

/-- Lower bound: if `v` forces `n` pebbles on some region and every path from a source to `v` is
initially open, then every successful budget for `v` is at least `n`. -/
theorem ForcesPebbles.le_of_blackPebblable {R : Set V} {v : V} {n s : ℕ}
    (hF : ForcesPebbles G R v n) (hu : Unblocked G ∅ v) (h : BlackPebblable G s v) : n ≤ s := by
  obtain ⟨ms, D, hD, hvD⟩ := h
  obtain ⟨f, N, hf0, hfN, hf⟩ := exists_seq_of_mTr hD
  obtain ⟨t, ht₀, htN, S, hSf, -, hS⟩ := hF f 0 N (Nat.zero_le N)
    (fun t _ ht => (hf t ht).imp fun _ h => h.1) (hf0 ▸ hu) (hfN ▸ hvD)
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨m, -, hcard⟩ := hf t' (by omega)
  exact hS.trans ((Finset.card_le_card hSf).trans hcard)

end Blocking

end Cslib.Pebbling
