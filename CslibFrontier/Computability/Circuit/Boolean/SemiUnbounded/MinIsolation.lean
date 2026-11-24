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
  cases C.kind g with
  | leaf _ | or => positivity
  | and _ => exact levelWeight_lt_pow (C.andLevel g) (code g) seed

/-- The seeded weight of a proof tree equals the `multisetWeight` of its AND-gate occurrences. -/
theorem ProofTree.weight_seededGateWeight {C : LayeredSemiUnboundedCircuit G}
    (code : G → Fin ℓ → Bool) (seed : Fin ℓ → Bool) {g : G} (t : ProofTree C g) :
    t.weight (C.seededGateWeight code seed) =
      multisetWeight C.andLevel code seed (t.andNodes : Multiset G) := by
  induction t with
  | leaf hkind =>
    simp [ProofTree.weight, ProofTree.andNodes, seededGateWeight, hkind]
  | andUnary hkind sub ih =>
    simp [ProofTree.weight, ProofTree.andNodes, seededGateWeight, hkind, ih, ← Multiset.cons_coe]
  | andBinary hkind left right ihl ihr =>
    simp [ProofTree.weight, ProofTree.andNodes, seededGateWeight, hkind, ihl, ihr,
      ← Multiset.cons_coe, ← Multiset.coe_add, Nat.add_assoc]
  | orChoice hkind _ sub ih =>
    simp [ProofTree.weight, ProofTree.andNodes, seededGateWeight, hkind, ih]

open Classical in
/-- The finite set of all proof trees of a gate in a finite circuit. -/
private noncomputable def proofTreeFinset [Finite G] (C : LayeredSemiUnboundedCircuit G) (g : G) :
    Finset (ProofTree C g) :=
  (Set.toFinite (Set.univ : Set (ProofTree C g))).toFinset

private theorem mem_proofTreeFinset [Finite G] {C : LayeredSemiUnboundedCircuit G} {g : G}
    (t : ProofTree C g) : t ∈ C.proofTreeFinset g := by
  simp [proofTreeFinset]

private theorem proofTreeFinset_nonempty [Finite G] {C : LayeredSemiUnboundedCircuit G} {g : G}
    (hg : C.Eval g) : (C.proofTreeFinset g).Nonempty := by
  obtain ⟨t⟩ := (C.eval_iff_nonempty_proofTree g).mp hg
  exact ⟨t, C.mem_proofTreeFinset t⟩

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
  obtain ⟨t', -, ht'⟩ := mem_image.mp (min'_mem
    ((C.proofTreeFinset g).image fun q => q.weight (C.seededGateWeight code seed))
    ((C.proofTreeFinset_nonempty hg).image _))
  exact le_antisymm (C.minProofTreeWeight_le code seed hg t) (by
    rw [minProofTreeWeight, ← ht']
    exact isMinOn_univ_iff.mp ht t')

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
  refine multisetWeight_update_bounds C.andLevel code seed u (rest : Multiset G) rfl
    (fun x hx => hlt x (Multiset.mem_coe.mp hx)) (fun k hk => ?_) j
  have hlen : ((rest : Multiset G).filter fun x => C.andLevel x = k).card =
      (rest.filter fun x => decide (C.andLevel x = k)).length := by
    rw [Multiset.filter_coe, Multiset.coe_card]
  rw [hlen]
  exact hcard k hk

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
      2 ^ (ℓ - hammingDist (code u) (code v)) := by
  have hlevel : C.andLevel u = C.andLevel v := by simp only [andLevel, hlayer]
  refine card_tyingSeeds_le_of_update_bounds
    (fun seed => C.minProofTreeWeight code seed hu)
    (fun seed => C.minProofTreeWeight code seed hv)
    (m := C.andLevel u)
    (fun seed j => C.minProofTreeWeight_update_bounds hnorm code seed hku hu j)
    (fun seed j => ?_)
  simpa only [← hlevel] using C.minProofTreeWeight_update_bounds hnorm code seed hkv hv j

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
  have hevent (p : G × G) : (events p).card ≤ 2 ^ (ℓ - d) := by
    obtain ⟨u, v⟩ := p
    by_cases ht : Odd (C.layer u) ∧ C.layer u = C.layer v ∧ u ≠ v ∧ C.Eval u ∧ C.Eval v
    · dsimp only [events]
      rw [dite_eq_left ht]
      obtain ⟨inpu, hku⟩ := hnorm.and_of_odd ht.1
      obtain ⟨inpv, hkv⟩ := hnorm.and_of_odd (ht.2.1 ▸ ht.1)
      refine (C.card_tyingSeeds_le hnorm code hku hkv ht.2.1 ht.2.2.2.1 ht.2.2.2.2).trans ?_
      exact Nat.pow_le_pow_right (by decide)
        (Nat.sub_le_sub_left (hd u v ht.1 ht.2.1 ht.2.2.1) ℓ)
    · simp [events, ht]
  have hcover : (univ.filter fun seed => ¬C.IsMinIsolating (C.seededGateWeight code seed)) ⊆
      univ.biUnion events := by
    intro seed hseed
    by_contra hout
    apply (mem_filter.mp hseed).2
    apply C.isMinIsolating_of_separated (C.seededGateWeight code seed)
    intro g hgor u v hcu hcv hne tu tv htu htv heq
    obtain ⟨hoddu, _⟩ := hnorm.and_of_orChild hgor hcu
    have hlu := C.layer_orChild hgor hcu
    have hlv := C.layer_orChild hgor hcv
    have hlayer : C.layer u = C.layer v := by omega
    have heu : C.Eval u := (C.eval_iff_nonempty_proofTree u).mpr ⟨tu⟩
    have hev : C.Eval v := (C.eval_iff_nonempty_proofTree v).mpr ⟨tv⟩
    have ht : Odd (C.layer u) ∧ C.layer u = C.layer v ∧ u ≠ v ∧ C.Eval u ∧ C.Eval v :=
      ⟨hoddu, hlayer, hne, heu, hev⟩
    have hminEq : C.minProofTreeWeight code seed heu = C.minProofTreeWeight code seed hev := by
      rw [C.minProofTreeWeight_eq_of_isMinOn code seed heu htu,
        C.minProofTreeWeight_eq_of_isMinOn code seed hev htv, heq]
    apply hout
    refine mem_biUnion.mpr ⟨(u, v), mem_univ _, ?_⟩
    simp only [events, dite_eq_left ht]
    exact mem_filter.mpr ⟨mem_univ _, hminEq⟩
  calc
    _ ≤ (univ.biUnion events).card := card_le_card hcover
    _ ≤ ∑ p : G × G, (events p).card := card_biUnion_le
    _ ≤ ∑ _ : G × G, 2 ^ (ℓ - d) := sum_le_sum fun p _ => hevent p
    _ = Fintype.card G ^ 2 * 2 ^ (ℓ - d) := by
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
  by_contra hne
  have h := (C.card_nonisolatingSeeds_le hnorm code hd).trans_lt hsize
  simp only [not_exists] at hne
  simp [hne] at h

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
  have hd : d ≤ codeLength N 0 := by
    have h := (codeLength_bounds N 0).1
    simp only [Nat.zero_add, Nat.mul_one] at h
    dsimp [d]
    omega
  have hbase : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by decide) N
  have hbound : N ^ 2 < 2 ^ d := by
    calc
      N ^ 2 < (2 ^ (Nat.log 2 N + 1)) ^ 2 := Nat.pow_lt_pow_left hbase (by decide)
      _ = 2 ^ (2 * (Nat.log 2 N + 1)) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) (by dsimp [d]; omega)
  have hsize : Fintype.card (Fin N) ^ 2 * 2 ^ (codeLength N 0 - d) < 2 ^ codeLength N 0 := by
    rw [Fintype.card_fin]
    calc
      _ < 2 ^ d * 2 ^ (codeLength N 0 - d) :=
        Nat.mul_lt_mul_of_pos_right hbound (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hd]
  exact C.exists_minIsolating_seed hnorm (indexedCodeword (n := 0))
    (fun _ _ _ _ hne => by
      simpa only [Nat.zero_add, Nat.mul_one] using log_le_hammingDist_indexedCodeword (n := 0) hne)
    hsize

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
  have hdepth' : maxAndLevel ≤ c * L := hdepth
  have hlen : codeLength N 0 ≤ 268435456 * L := by
    have h := (codeLength_bounds N 0).2
    simpa only [Nat.zero_add, Nat.mul_one] using h
  have hexp : maxAndLevel + codeLength N 0 ≤ (c + 268435456) * L := by
    have : (c + 268435456) * L = c * L + 268435456 * L := Nat.add_mul c 268435456 L
    omega
  have hpow : 2 ^ L ≤ 2 * (N + 1) := by
    rw [show L = Nat.log 2 N + 1 from rfl, pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_add_one 2 N)
  calc
    generatedGateWeightBound N maxAndLevel
        ≤ 6 ^ ((c + 268435456) * L) := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ (2 ^ 3) ^ ((c + 268435456) * L) := Nat.pow_le_pow_left (by decide) _
    _ = (2 ^ L) ^ (3 * (c + 268435456)) := by
      have hab : 3 * ((c + 268435456) * L) = L * (3 * (c + 268435456)) := by ac_rfl
      rw [← pow_mul, ← pow_mul, hab]
    _ ≤ (2 * (N + 1)) ^ (3 * (c + 268435456)) :=
      Nat.pow_le_pow_left hpow _

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
