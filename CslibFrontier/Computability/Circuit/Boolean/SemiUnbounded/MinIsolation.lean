/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded
public import CslibFrontier.Foundations.Combinatorics.MinIsolation.BaseSix
public import CslibFrontier.Foundations.Data.Code.JustesenFamily

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Min-isolation of proof trees in layered semi-unbounded circuits

This module formalizes the combinatorial core of work package 1 of cslib-frontier #7920: an
original adaptation of Hoza's base-six min-isolation lemma ([Hoza2026NLUL], §2) from paths in
layered digraphs to proof trees in layered alternating semi-unbounded Boolean circuits with an
AND first layer.

Given a binary code `code : G → Fin ℓ → Bool` and a seed `seed : Fin ℓ → Bool`, each AND gate
`g` at AND-level `k = C.andLevel g` receives the base-six weight
`∑ j, 6 ^ (k + (ℓ - (j + 1))) * (code g j).toNat * (seed j).toNat`, while OR gates and leaves
receive weight `0` (`seededGateWeight`). In normal form:

* A proof tree of an AND gate `u` at level `m` has at most `2 ^ (m - k)` AND-gate copies at each
  lower level `k < m`, so the minimum proof-tree weight `μ_u(seed)` obeys Hoza's two-sided
  seed-update derivative bound (`minProofTreeWeight_update_bounds`).
* For any two satisfied AND gates `u, v` in the same layer, at most
  `2 ^ (ℓ - hammingDist (code u) (code v))` seeds tie `μ_u` and `μ_v` (`card_tyingSeeds_le`).
* A union bound over all same-layer pairs of distinct AND gates bounds the number of non-isolating
  seeds by `Fintype.card G ^ 2 * 2 ^ (ℓ - d)` whenever distinct AND gates in the same layer have
  Hamming distance at least `d` (`card_nonisolatingSeeds_le`), yielding an isolating seed whenever
  this bound is below `2 ^ ℓ` (`exists_minIsolating_seed`).
* Instantiating with `Cslib.Code.JustesenFamily.indexedCodeword` gives an explicit seed family of
  length `O(log N)` that min-isolates every normal-form circuit on `Fin N`
  (`exists_generatedGateWeight_isMinIsolating`), with weights strictly below `6 ^ (K + ℓ)`,
  polynomially bounded in `N` for logarithmic AND-depth
  (`generatedGateWeight_polynomial_of_log_depth`).

This establishes the nonuniform combinatorial isolation step of #7920; uniform logspace weight
evaluation, auxiliary pushdown automata, and the uniform `LogCFL = UAuxPDA(log n, poly)`
endpoint remain open in #7920.

## Main definitions

* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.seededGateWeight`: AND-level base-six
  gate weights (zero on OR gates and leaves).
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.minProofTreeWeight`: minimum seeded
  proof-tree weight of a satisfied gate.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.generatedGateWeight`: executable Justesen
  instantiation on `Fin N`.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.generatedGateWeightBound`: seed-independent
  upper bound `6 ^ (K + codeLength N 0)` for AND-depth at most `K`.

## Main results

* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.minProofTreeWeight_update_bounds`:
  two-sided seed-update derivative bound for satisfied AND gates in normal form.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.card_tyingSeeds_le`: collision bound for
  two satisfied AND gates in the same layer.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.card_nonisolatingSeeds_le`: union bound
  over bad seeds.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.exists_minIsolating_seed`: existence of a
  min-isolating seed from minimum within-layer code distance.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.exists_generatedGateWeight_isMinIsolating`:
  Justesen family existence theorem for every normal-form circuit on `Fin N`.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.generatedGateWeightBound_le_poly`:
  uniform polynomial bound on `6 ^ (K + ℓ)` for logarithmic AND-depth `K = O(log N)`.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.generatedGateWeight_polynomial_of_log_depth`:
  polynomial magnitude bound for logarithmic AND-depth circuits.
-/

public section

namespace Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit

open Finset Function
open Cslib.MinIsolation.BaseSix

variable {G : Type*} {ℓ : ℕ}

/-- Seeded base-six gate weight: AND gates at AND-level `k = C.andLevel g` receive
`levelWeight k (code g) seed`, while OR gates and leaves receive weight `0`. -/
@[expose] def seededGateWeight (C : LayeredSemiUnboundedCircuit G) (code : G → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (g : G) : ℕ :=
  match C.kind g with
  | .and _ => levelWeight (C.andLevel g) (code g) seed
  | .leaf _ | .or => 0

/-- Every gate weight is strictly below `6 ^ (C.andLevel g + ℓ)`. -/
theorem seededGateWeight_lt_pow (C : LayeredSemiUnboundedCircuit G) (code : G → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (g : G) :
    C.seededGateWeight code seed g < 6 ^ (C.andLevel g + ℓ) := by
  unfold seededGateWeight
  cases C.kind g <;> first | positivity | exact levelWeight_lt_pow _ _ _

/-- The seeded weight of a proof tree equals the `multisetWeight` of its AND-gate occurrences. -/
theorem ProofTree.weight_seededGateWeight {C : LayeredSemiUnboundedCircuit G}
    (code : G → Fin ℓ → Bool) (seed : Fin ℓ → Bool) {g : G} (t : ProofTree C g) :
    t.weight (C.seededGateWeight code seed) =
      multisetWeight C.andLevel code seed (t.andNodes : Multiset G) := by
  induction t <;> simp [ProofTree.weight, ProofTree.andNodes, seededGateWeight, *,
    ← Multiset.cons_coe, ← Multiset.coe_add, Nat.add_assoc]

open Classical in
/-- The finite set of all proof trees of a gate in a finite circuit. -/
private noncomputable def proofTreeFinset [Finite G] (C : LayeredSemiUnboundedCircuit G) (g : G) :
    Finset (ProofTree C g) :=
  (Set.toFinite (Set.univ : Set (ProofTree C g))).toFinset

private theorem mem_proofTreeFinset [Finite G] {C : LayeredSemiUnboundedCircuit G} {g : G}
    (t : ProofTree C g) : t ∈ C.proofTreeFinset g := by
  simp [proofTreeFinset]

private theorem proofTreeFinset_nonempty [Finite G] {C : LayeredSemiUnboundedCircuit G} {g : G}
    (hg : C.Eval g) : (C.proofTreeFinset g).Nonempty :=
  let ⟨t⟩ := (C.eval_iff_nonempty_proofTree g).mp hg
  ⟨t, C.mem_proofTreeFinset t⟩

open Classical in
/-- The minimum seeded proof-tree weight of a satisfied gate `g`. -/
noncomputable def minProofTreeWeight [Finite G] (C : LayeredSemiUnboundedCircuit G)
    (code : G → Fin ℓ → Bool) (seed : Fin ℓ → Bool) {g : G} (hg : C.Eval g) : ℕ :=
  ((C.proofTreeFinset g).image fun t => t.weight (C.seededGateWeight code seed)).min'
    ((C.proofTreeFinset_nonempty hg).image _)

/-- The minimum proof-tree weight is at most the weight of any proof tree of `g`. -/
theorem minProofTreeWeight_le [Finite G] (C : LayeredSemiUnboundedCircuit G)
    (code : G → Fin ℓ → Bool) (seed : Fin ℓ → Bool) {g : G} (hg : C.Eval g)
    (t : ProofTree C g) :
    C.minProofTreeWeight code seed hg ≤ t.weight (C.seededGateWeight code seed) := by
  classical
  exact min'_le _ _ (mem_image_of_mem _ (C.mem_proofTreeFinset t))

/-- Every globally minimum proof tree of `g` attains `minProofTreeWeight`. -/
theorem minProofTreeWeight_eq_of_isMinOn [Finite G] (C : LayeredSemiUnboundedCircuit G)
    (code : G → Fin ℓ → Bool) (seed : Fin ℓ → Bool) {g : G} (hg : C.Eval g)
    {t : ProofTree C g}
    (ht : IsMinOn (ProofTree.weight (C.seededGateWeight code seed)) Set.univ t) :
    C.minProofTreeWeight code seed hg = t.weight (C.seededGateWeight code seed) := by
  classical
  obtain ⟨t', -, ht'⟩ := mem_image.mp (min'_mem _
    ((C.proofTreeFinset_nonempty hg).image fun q => q.weight (C.seededGateWeight code seed)))
  exact le_antisymm (C.minProofTreeWeight_le code seed hg t)
    (by rw [minProofTreeWeight, ← ht']; exact isMinOn_univ_iff.mp ht t')

/-- Two-sided seed-update derivative bound for a satisfied AND gate `u` in a normal-form circuit:
flipping seed bit `j` from `false` to `true` increases `minProofTreeWeight` by between
`levelBitCoeff (C.andLevel u) j * (code u j).toNat` and that quantity plus half of
`levelBitCoeff (C.andLevel u) j`. -/
theorem minProofTreeWeight_update_bounds [Finite G] (C : LayeredSemiUnboundedCircuit G)
    (hnorm : C.InNormalForm) (code : G → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    {u : G} {inp : AndInputs G} (hkind : C.kind u = .and inp) (hu : C.Eval u) (j : Fin ℓ) :
    let d₀ := C.minProofTreeWeight code (update seed j false) hu
    let d₁ := C.minProofTreeWeight code (update seed j true) hu
    let B := levelBitCoeff (C.andLevel u) j
    d₀ + B * (code u j).toNat ≤ d₁ ∧
      d₁ ≤ d₀ + B * (code u j).toNat + B / 2 := by
  classical
  refine minWeight_update_bounds (fun t s => t.weight (C.seededGateWeight code s))
    (C.proofTreeFinset_nonempty hu) (m := C.andLevel u) (c := code u) seed j fun t _ => ?_
  obtain ⟨rest, hnodes, hlt, hcard⟩ := t.andNodes_and_profile hnorm hkind
  rw [t.weight_seededGateWeight, t.weight_seededGateWeight, hnodes]
  exact multisetWeight_update_bounds C.andLevel code seed u (rest : Multiset G) rfl
    (fun x hx => hlt x (Multiset.mem_coe.mp hx))
    (fun k hk => by simpa only [Multiset.filter_coe, Multiset.coe_card] using hcard k hk) j

/-- Collision bound: for two satisfied AND gates `u` and `v` in the same layer of a normal-form
circuit, at most `2 ^ (ℓ - hammingDist (code u) (code v))` seeds tie their minimum proof-tree
weights. -/
theorem card_tyingSeeds_le [Finite G] (C : LayeredSemiUnboundedCircuit G)
    (hnorm : C.InNormalForm) (code : G → Fin ℓ → Bool)
    {u v : G} {inpu inpv : AndInputs G}
    (hku : C.kind u = .and inpu) (hkv : C.kind v = .and inpv)
    (hlayer : C.layer u = C.layer v) (hu : C.Eval u) (hv : C.Eval v) :
    (univ.filter fun seed =>
      C.minProofTreeWeight code seed hu = C.minProofTreeWeight code seed hv).card ≤
      2 ^ (ℓ - hammingDist (code u) (code v)) :=
  card_tyingSeeds_le_of_update_bounds
    (fun seed => C.minProofTreeWeight code seed hu)
    (fun seed => C.minProofTreeWeight code seed hv)
    (fun seed j => C.minProofTreeWeight_update_bounds hnorm code seed hku hu j)
    fun seed j => by
      simpa only [andLevel, hlayer] using
        C.minProofTreeWeight_update_bounds hnorm code seed hkv hv j

open Classical in
/-- Union bound over bad seeds: if distinct AND gates in the same layer have Hamming distance
at least `d`, then at most `Fintype.card G ^ 2 * 2 ^ (ℓ - d)` seeds fail to min-isolate `C`. -/
theorem card_nonisolatingSeeds_le [Fintype G] (C : LayeredSemiUnboundedCircuit G)
    (hnorm : C.InNormalForm) (code : G → Fin ℓ → Bool) {d : ℕ}
    (hd : ∀ u v : G, Odd (C.layer u) → C.layer u = C.layer v → u ≠ v →
      d ≤ hammingDist (code u) (code v)) :
    (univ.filter fun seed => ¬C.IsMinIsolating (C.seededGateWeight code seed)).card ≤
      Fintype.card G ^ 2 * 2 ^ (ℓ - d) := by
  classical
  let events : G × G → Finset (Fin ℓ → Bool) := fun (u, v) =>
    if h : Odd (C.layer u) ∧ C.layer u = C.layer v ∧ u ≠ v ∧ C.Eval u ∧ C.Eval v then
      univ.filter fun seed =>
        C.minProofTreeWeight code seed h.2.2.2.1 = C.minProofTreeWeight code seed h.2.2.2.2
    else ∅
  have hevent : ∀ p : G × G, (events p).card ≤ 2 ^ (ℓ - d) := fun ⟨u, v⟩ => by
    dsimp only [events]
    split_ifs with ht
    · obtain ⟨inpu, hku⟩ := hnorm.and_of_odd ht.1
      obtain ⟨inpv, hkv⟩ := hnorm.and_of_odd (ht.2.1 ▸ ht.1)
      exact (C.card_tyingSeeds_le hnorm code hku hkv ht.2.1 ht.2.2.2.1 ht.2.2.2.2).trans
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (hd u v ht.1 ht.2.1 ht.2.2.1) ℓ))
    · simp
  have hcover : (univ.filter fun seed => ¬C.IsMinIsolating (C.seededGateWeight code seed)) ⊆
      univ.biUnion events := fun seed hseed => by
    by_contra hout
    refine (mem_filter.mp hseed).2 (C.isMinIsolating_of_separated _ fun g hgor u v hcu hcv hne
      tu tv htu htv heq => ?_)
    have hlayer : C.layer u = C.layer v := by
      have := C.layer_orChild hgor hcu
      have := C.layer_orChild hgor hcv
      omega
    have heu : C.Eval u := (C.eval_iff_nonempty_proofTree u).mpr ⟨tu⟩
    have hev : C.Eval v := (C.eval_iff_nonempty_proofTree v).mpr ⟨tv⟩
    have ht : Odd (C.layer u) ∧ C.layer u = C.layer v ∧ u ≠ v ∧ C.Eval u ∧ C.Eval v :=
      ⟨(hnorm.and_of_orChild hgor hcu).1, hlayer, hne, heu, hev⟩
    refine hout (mem_biUnion.mpr ⟨(u, v), mem_univ _, ?_⟩)
    simp only [events, dite_eq_left ht, mem_filter, mem_univ, true_and]
    rw [C.minProofTreeWeight_eq_of_isMinOn code seed heu htu,
      C.minProofTreeWeight_eq_of_isMinOn code seed hev htv, heq]
  refine (card_le_card hcover).trans (card_biUnion_le.trans
    ((sum_le_sum fun p _ => hevent p).trans_eq ?_))
  simp only [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
  ring

/-- A seed min-isolates every true gate of a normal-form circuit whenever the union bound is
strictly smaller than the seed space `2 ^ ℓ`. -/
theorem exists_minIsolating_seed [Fintype G] (C : LayeredSemiUnboundedCircuit G)
    (hnorm : C.InNormalForm) (code : G → Fin ℓ → Bool) {d : ℕ}
    (hd : ∀ u v : G, Odd (C.layer u) → C.layer u = C.layer v → u ≠ v →
      d ≤ hammingDist (code u) (code v))
    (hsize : Fintype.card G ^ 2 * 2 ^ (ℓ - d) < 2 ^ ℓ) :
    ∃ seed, C.IsMinIsolating (C.seededGateWeight code seed) := by
  classical
  by_contra! hne
  simpa [hne] using (C.card_nonisolatingSeeds_le hnorm code hd).trans_lt hsize

section Justesen

open Code.JustesenFamily

/-- Executable Justesen-based base-six gate weight on a finite gate set `Fin N`. -/
@[expose] def generatedGateWeight {N : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
    (seed : Fin (codeLength N 0) → Bool) (g : Fin N) : ℕ :=
  C.seededGateWeight (indexedCodeword (n := 0)) seed g

/-- Every normal-form layered semi-unbounded circuit on `Fin N` admits a seed in the Justesen
family (of length `O(log N)`) that gives every true gate a unique minimum-weight proof tree. -/
theorem exists_generatedGateWeight_isMinIsolating {N : ℕ}
    (C : LayeredSemiUnboundedCircuit (Fin N)) (hnorm : C.InNormalForm) :
    ∃ seed, C.IsMinIsolating (C.generatedGateWeight seed) := by
  let d := 4 * (Nat.log 2 N + 1)
  have hd : d ≤ codeLength N 0 :=
    (Nat.mul_le_mul_right _ (by decide : 4 ≤ 512)).trans (by simpa using (codeLength_bounds N 0).1)
  have hbound : N ^ 2 < 2 ^ d := calc
    N ^ 2 < (2 ^ (Nat.log 2 N + 1)) ^ 2 :=
      Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by decide) N) (by decide)
    _ ≤ 2 ^ d := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) (by dsimp [d]; omega)
  refine C.exists_minIsolating_seed hnorm (indexedCodeword (n := 0))
    (fun _ _ _ _ hne => by simpa using log_le_hammingDist_indexedCodeword (n := 0) hne) ?_
  rw [Fintype.card_fin]
  conv_rhs => rw [← Nat.add_sub_of_le hd, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hbound (Nat.two_pow_pos _)

/-- Seed-independent upper bound `6 ^ (maxAndLevel + codeLength gateCount 0)` on generated gate
weights for circuits of size `gateCount` and maximum AND-level `maxAndLevel`. -/
@[expose] def generatedGateWeightBound (gateCount maxAndLevel : ℕ) : ℕ :=
  6 ^ (maxAndLevel + codeLength gateCount 0)

/-- Every Justesen-generated gate weight is strictly below `6 ^ (C.andLevel g + codeLength N 0)`. -/
theorem generatedGateWeight_lt_pow {N : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
    (seed : Fin (codeLength N 0) → Bool) (g : Fin N) :
    C.generatedGateWeight seed g < 6 ^ (C.andLevel g + codeLength N 0) :=
  C.seededGateWeight_lt_pow (indexedCodeword (n := 0)) seed g

/-- Every gate at AND-level at most `maxAndLevel` has generated weight strictly below
`generatedGateWeightBound N maxAndLevel`. -/
theorem generatedGateWeight_lt_bound {N maxAndLevel : ℕ} (C : LayeredSemiUnboundedCircuit (Fin N))
    (seed : Fin (codeLength N 0) → Bool) (g : Fin N) (hdepth : C.andLevel g ≤ maxAndLevel) :
    C.generatedGateWeight seed g < generatedGateWeightBound N maxAndLevel :=
  (C.generatedGateWeight_lt_pow seed g).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hdepth _))

/-- For logarithmic AND-depth (`maxAndLevel ≤ c * (Nat.log 2 N + 1)`), one polynomial in `N`
bounds `generatedGateWeightBound N maxAndLevel = 6 ^ (maxAndLevel + codeLength N 0)` uniformly
across all circuit sizes `N`. -/
theorem generatedGateWeightBound_le_poly (c : ℕ) :
    ∃ D : ℕ, ∀ (N maxAndLevel : ℕ),
      maxAndLevel ≤ c * (Nat.log 2 N + 1) →
      generatedGateWeightBound N maxAndLevel ≤ (2 * (N + 1)) ^ D := by
  refine ⟨3 * (c + 268435456), fun N maxAndLevel hdepth => ?_⟩
  let L := Nat.log 2 N + 1
  have hlen : codeLength N 0 ≤ 268435456 * L := by simpa using (codeLength_bounds N 0).2
  have hexp : maxAndLevel + codeLength N 0 ≤ (c + 268435456) * L := by
    rw [Nat.add_mul]; exact Nat.add_le_add hdepth hlen
  have hpow : 2 ^ L ≤ 2 * (N + 1) := by
    simpa only [L, pow_succ'] using Nat.mul_le_mul_left 2 (Nat.pow_log_le_add_one 2 N)
  calc
    generatedGateWeightBound N maxAndLevel
        ≤ (2 ^ 3) ^ ((c + 268435456) * L) :=
          (Nat.pow_le_pow_right (by decide) hexp).trans (Nat.pow_le_pow_left (by decide) _)
    _ = (2 ^ L) ^ (3 * (c + 268435456)) := by rw [← pow_mul, ← pow_mul]; ring_nf
    _ ≤ (2 * (N + 1)) ^ (3 * (c + 268435456)) := Nat.pow_le_pow_left hpow _

/-- For circuits of logarithmic AND-depth (`C.andLevel g ≤ c * (Nat.log 2 N + 1)`), one
polynomial in `N` bounds every Justesen-generated gate weight uniformly across all circuit sizes
and seeds. -/
theorem generatedGateWeight_polynomial_of_log_depth (c : ℕ) :
    ∃ D : ℕ, ∀ (N : ℕ) (C : LayeredSemiUnboundedCircuit (Fin N))
      (seed : Fin (codeLength N 0) → Bool) (g : Fin N),
      C.andLevel g ≤ c * (Nat.log 2 N + 1) →
      C.generatedGateWeight seed g < (2 * (N + 1)) ^ D := by
  obtain ⟨D, hD⟩ := generatedGateWeightBound_le_poly c
  exact ⟨D, fun N C seed g hdepth =>
    (C.generatedGateWeight_lt_bound seed g le_rfl).trans_le (hD N (C.andLevel g) hdepth)⟩

end Justesen

end Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit
