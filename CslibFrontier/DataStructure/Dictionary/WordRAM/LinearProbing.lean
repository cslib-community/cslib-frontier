/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Spec
public import CslibFrontier.DataStructure.HashFamily.WordRAM.KWise
public import CslibFrontier.DataStructure.Dictionary.WordRAM.LinearProbing.FiveWise
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega

/-!
# Open-Addressed Linear Probing on the Randomized Word RAM

This file implements a self-contained open-addressed linear-probing hash table realizing
`Cslib.DataStructure.Dictionary.spec U V n_max` on the randomized Word RAM
(`Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl`), adapting
[Pagh, Pagh and Ružić, *Linear Probing with
Constant Independence*, *SIAM J. Comput.* 39(3):1107–1120, 2009, Section 2.3 (Lemma 2.1,
pp. 1110–1111) and Section 4 (Lemma 4.1, Theorem 4.3, and Theorem 4.5,
pp. 1114–1118)][PaghPaghRuzic2009]; [Cormen, Leiserson, Rivest and Stein, *Introduction to
Algorithms*, Section 11.4][CLRS2009].

## Design

1. **Power-of-$2$ open-addressed layout ($O(n_{\max})$ words, zero tombstones):**
   For capacity bound $n_{\max}$, we set $M = \mathrm{tableLog}(n_{\max}) =
   \lceil \log_2 \max(8 n_{\max}, 8) \rceil$ and table size $m = 2^M$ (`tableSize n_max`), so that
   $8 n_{\max} \le 2^M < 16 \max(n_{\max}, 1)$ (load factor $\alpha \le 1/8$). Memory at `base`
   consists of:
   - `[base, base + KWise.space n_max 5)`: embedded $5$-wise independent trinomial-field hash state
     (`Cslib.DataStructure.HashFamily.WordRAM.KWise`);
   - `[usedBase, usedBase + 2^M)`: occupancy flags `used[0 .. 2^M - 1]` (`0` = empty, `1` =
     occupied, so zero-initialized memory is immediately a valid empty table);
   - `[keyBase, keyBase + 2^M)`: stored keys `key[0 .. 2^M - 1]`;
   - `[valBase, valBase + 2^M)`: stored values `val[0 .. 2^M - 1]`.
   Total footprint is `space n_max = KWise.space n_max 5 + 3 * tableSize n_max = O(n_max)` words.

2. **Self-contained operations (`initSetup`, `query`, `insert`):**
   - `initSetup`: runs `KWise.initCode 5` ($O(n_{\max})$ deterministic Four-Russians carryless
     multiplication table setup plus $5$ `Code.rand` calls, with zero caller-supplied primes).
   - `query u` and `insert u v`: evaluate $b = h_\theta(u) \in \mathrm{Fin}(2^M)$ via
     `KWise.evalCode 5` in $O(L^2 + 1)$ deterministic steps ($L = \mathrm{limbCount}(n_{\max}, U, M)
     = O(1)$ when $U \le n_{\max}^c$), then scan $(b + d) \bmod 2^M$ until reaching the first slot
     `p` where `used[p] = 0` or `key[p] = u`. Because at most $n_{\max} \le 2^M / 8$ slots are
     occupied, at least $7/8$ of all slots are empty and the probe loop terminates deterministically
     in $\le n_{\max} < 2^M$ iterations on every seed.

3. **Expected $O(1)$ probe bound under $5$-wise independence:**
   If probing for $u$ from $b = h_\theta(u)$ steps over $t \ge 1$ slots occupied by keys in
   $S = \mathrm{dom}(s) \setminus \{u\}$, walking backwards from $b$ to the nearest preceding empty
   slot yields a contiguous cyclic interval `cyclicInterval M b a ℓ` of length
   $\ell = a + t \in [t, \#S]$ whose $\ell$ stored keys in $S$ all hash into
   `cyclicInterval M b a ℓ` (`TableInv.hasClusterWitness_probeLen`, adapting the occupied-run
   argument in the proof of Lemma 4.1, p. 1114 of `[PaghPaghRuzic2009]`). Applying
   `tsum_uniform_probe_le_of_cluster_witness` from
   `CslibFrontier.DataStructure.Dictionary.WordRAM.LinearProbing.FiveWise` bounds the expected
   number
   of
   skipped occupied slots `TableInv.probeLen` by $288 = O(1)$ (`tsum_probeLen_le`).

## Source mapping, specialization, and cost scope

In `[PaghPaghRuzic2009]`, Section 4 (Theorems 4.3 and 4.5, pp. 1115–1118, built on Lemma 2.1,
pp. 1110–1111, and Lemma 4.1, p. 1114) proves that for any sequence of insertions, deletions, and
lookups in a linear-probing hash table of size $r$ using a hash function chosen uniformly at random
from a $5$-wise independent family $\mathcal{H} : U \to [r]$ with maximum load $\bar{\alpha} < 1$,
the expected number of probes made during an operation is $O((1 - \bar{\alpha})^{-5/2})$
(Theorem 4.3) and $O((1 - \bar{\alpha})^{-13/6})$ (Theorem 4.5), which is $O(1)$ for bounded load
factor. The declarations in this module and `LinearProbing.FiveWise` map to `[PaghPaghRuzic2009]` as
follows:
- **Hash family (`isKWiseIndependentHash_hashFn`):**
  Uniform $5$-wise independent trinomial-field polynomial family `hashFn U n_max`
  (`trinomialPolyHash` over $\mathbb{F}_{2^q}$ projected to $M$ bits, initialized and evaluated on
  the Word RAM via `KWise.initCode 5` and `KWise.evalCode 5`), realizing exact uniform $5$-wise
  independence (`IsKWiseIndependentHash 5`) with maximum load $\bar{\alpha} = \alpha = \#S / 2^M$.
- **Operation history and oblivious adversary (`ValidHistory`, `seq_expected_amortized`):**
  An admissible operation sequence `ops : List (Dictionary.Op U)` fixed independently of the sampled
  hash seed $\theta \sim \mathrm{seedLaw}\ U\ n_{\max}$, matching the fixed-set / oblivious
  operation model of `[PaghPaghRuzic2009]`, Section 4.
- **Load-factor specialization ($\alpha \le 1/8$):**
  While `[PaghPaghRuzic2009]` Theorems 4.3 and 4.5 apply to any maximum load $\bar{\alpha} < 1$, we
  fix $M = \mathrm{tableLog}(n_{\max}) = \lceil \log_2 \max(8 n_{\max}, 8) \rceil$ so that
  $\alpha = \#\mathrm{dom}(s) / 2^M \le n_{\max} / 2^M \le 1/8$ (`eight_mul_le_tableSize`) and
  `space n_max = O(n_max)` (`space_le`).
- **Probe count (`TableInv.probeLen`) vs. executable Word-RAM body charge (`charge`):**
  Whereas `[PaghPaghRuzic2009]` Section 4 (p. 1114) counts
  $1 + \max\{l \mid h(x) + [l] \subseteq P\}$ table probes, `TableInv.probeLen` counts the number of
  skipped occupied slots before the stopping slot ($\mathbb{E}[\mathrm{probeLen}] \le 288$ via
  `tsum_probeLen_le`). The final stopping-slot inspection, loop/branch overhead ($12 t + 27$
  instructions for $t$ skipped slots), and embedded `KWise.evalCode 5` hash evaluation
  (`KWise.evalSteps n_max U (tableLog n_max) 5`) are all included in the executable Word-RAM
  operation charge
  `charge U n_max = KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * 288 + 27 =
  KWise.evalSteps n_max U (tableLog n_max) 5 + 3483` (`opCode_execWithin`).
- **Original proof adaptation and explicit constants (`288` and `3483`):**
  Rather than formalizing the interval-grid decompositions of Lemmas 4.2 and 4.4 in
  `[PaghPaghRuzic2009]`, `LinearProbing.FiveWise` uses an original simplified proof adaptation at
  load $\le 1/8$ that covers any length-$\ell$ cyclic interval containing $b$ ($2^{j-1} \le \ell <
  2^j$) by a single centered dyadic-scale window `scaleWindow M b j` of size at most $2^{j+1}$
  (`card_scaleWindow_le`), yielding the explicit scale-$j$ overload bound
  $18 / (2^{j-2})^2 = 288 / 4^j$ (`expect_scaleOverload_le`), the probe-step bound $288$, and the
  instruction constant $12 \cdot 288 + 27 = 3483$.
- **Fixed-parameter program specialization and charged-body scope (`initParams = Fin.elim0`):**
  For fixed `(U, V, n_max)` on an admissible external machine word width `w`
  (`2 * trinomialDeg U (tableLog n_max) ≤ w`, `Fits w (base + space n_max)`, `Fits w V`),
  `subroutineCode U n_max` specializes configuration constants as instruction literals. Expected
  instruction bounds (`impl`, `implStandard`, and `seq_expected_amortized`) charge
  fresh initialization (`initFresh`) and subroutine operation bodies
  (`StateTransitionImpl.ExecSteps`),
  excluding caller argument delivery, caller control/dispatch loops, and host-level code
  construction.
- **Insert-only dictionary specification vs. source deletions:**
  Whereas `[PaghPaghRuzic2009]` Section 1 (p. 1107) and Section 4 (Theorems 4.3 and 4.5) include
  deletions via greedy backward-shift rearrangement, `Dictionary.spec U V n_max` specifies an
  insert-only bounded dictionary (`query` and `insert` with at most `n_max` distinct keys and no
  deletion operation), so open-addressed slots use `{0, 1}` occupancy flags (`0` = empty, `1` =
  occupied) with zero tombstones.

## References

* [A. Pagh, R. Pagh and M. Ružić, *Linear Probing with Constant Independence*][PaghPaghRuzic2009]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 11.4][CLRS2009]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.LinearProbing

open Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.WordRAM.ExactLog
open Cslib.DataStructure.HashFamily.WordRAM
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Parameters, memory layout, and cyclic probe geometry -/

/-- Latent seed type for the embedded $5$-wise independent trinomial-field hash family:
$5$ coefficients in $\mathrm{Fin}(2^{\mathrm{trinomialDeg}(U, \mathrm{tableLog}(n_{\max}))})$. -/
abbrev Seed (U n_max : ℕ) : Type :=
  Fin 5 → Fin (2 ^ trinomialDeg U (tableLog n_max))

/-- Uniform reference distribution over `Seed U n_max`. -/
@[expose] noncomputable def seedLaw (U n_max : ℕ) : PMF (Seed U n_max) :=
  PMF.uniformOfFintype (Seed U n_max)

/-- The $5$-wise independent hash function $h_\theta : \mathrm{Fin}\,U \to \mathrm{Fin}(2^M)$
associated with seed $\theta$. -/
@[expose] noncomputable def hashFn (U n_max : ℕ) (θ : Seed U n_max) (u : Fin U) :
    Fin (2 ^ tableLog n_max) :=
  trinomialPolyHash (trinomialStep U (tableLog n_max)) 5 U (tableLog n_max) θ u

/-- `hashFn U n_max` is a $5$-wise independent hash family. -/
theorem isKWiseIndependentHash_hashFn (U n_max : ℕ) :
    IsKWiseIndependentHash 5 (hashFn U n_max) :=
  isKWiseIndependentHash_trinomialPolyHash
    (le_two_pow_trinomialDeg U (tableLog n_max))
    (le_trinomialDeg U (tableLog n_max))

/-- Base address of the occupancy array `used[0 .. 2^M - 1]`. -/
@[expose, wram_arith] def usedBase (base n_max : ℕ) : ℕ :=
  base + KWise.space n_max 5

/-- Base address of the key array `key[0 .. 2^M - 1]`. -/
@[expose, wram_arith] def keyBase (base n_max : ℕ) : ℕ :=
  usedBase base n_max + tableSize n_max

/-- Base address of the value array `val[0 .. 2^M - 1]`. -/
@[expose, wram_arith] def valBase (base n_max : ℕ) : ℕ :=
  keyBase base n_max + tableSize n_max

/-- Total contiguous memory footprint of the linear-probing dictionary (in words):
`KWise.space n_max 5 + 3 * tableSize n_max = O(n_max)`. -/
@[expose, wram_arith] def space (n_max : ℕ) : ℕ :=
  KWise.space n_max 5 + 3 * tableSize n_max

local macro "layout_omega" : tactic => `(tactic| first | omega | wram_omega)

/-- `space n_max` is $O(n_{\max})$: specifically `space n_max ≤ 49 * max n_max 4 + 13`. -/
theorem space_le (n_max : ℕ) : space n_max ≤ 49 * max n_max 4 + 13 := by
  have h1 := KWise.two_pow_two_mul_chunkBits_le n_max
  have h2 := tableSize_le_sixteen_mul n_max
  dsimp only [space, KWise.space, KWise.spaceFromB]; omega

/-! ## Section 2: Open-addressed table invariant, termination, and cluster witness -/

/-- Occupancy flag `used[p]` at slot `p : Fin (2 ^ tableLog n_max)`. -/
@[expose] def usedAt (base n_max : ℕ) (mem : ℕ → ℕ) (p : Fin (2 ^ tableLog n_max)) : ℕ :=
  mem (usedBase base n_max + p.val)

/-- Stored key `key[p]` at slot `p : Fin (2 ^ tableLog n_max)`. -/
@[expose] def keyAt (base n_max : ℕ) (mem : ℕ → ℕ) (p : Fin (2 ^ tableLog n_max)) : ℕ :=
  mem (keyBase base n_max + p.val)

/-- Stored value `val[p]` at slot `p : Fin (2 ^ tableLog n_max)`. -/
@[expose] def valAt (base n_max : ℕ) (mem : ℕ → ℕ) (p : Fin (2 ^ tableLog n_max)) : ℕ :=
  mem (valBase base n_max + p.val)

/-- Linear-probing table invariant at `(base, n_max)` coupling abstract state
`s : Dictionary.State U` and seed `θ : Seed U n_max` with concrete memory `mem`:
1. `(Dictionary.dom s).card ≤ n_max` and `Dictionary.ValuesBounded V s`;
2. every slot `p` has `usedAt p ∈ {0, 1}`;
3. every occupied slot `p` (`usedAt p = 1`) stores a valid key `keyAt p < U` and value
   `valAt p < V` matching `s ⟨keyAt p, _⟩ = some (valAt p)`;
4. occupied slots store pairwise distinct keys;
5. every present key `u` with `s u = some v` resides at some probe offset `k < 2 ^ M` from
   `hashFn U n_max θ u` such that all preceding probe offsets `j < k` are occupied (`usedAt = 1`);
6. conversely, every occupied slot `p` (`usedAt p = 1`) is reachable from its key's home bucket
   `hashFn U n_max θ ⟨keyAt p, _⟩` at some offset `k < 2 ^ M` along an entirely occupied prefix
   (`∀ j < k, usedAt = 1`). -/
structure TableInv (U V n_max base : ℕ) (θ : Seed U n_max) (s : Dictionary.State U)
    (mem : ℕ → ℕ) : Prop where
  /-- Number of stored keys is at most `n_max`. -/
  card_dom_le : (Dictionary.dom s).card ≤ n_max
  /-- Every stored value in `s` is strictly less than `V`. -/
  values_bounded : Dictionary.ValuesBounded V s
  /-- Every occupancy entry is `0` or `1`. -/
  used_bit : ∀ p : Fin (2 ^ tableLog n_max),
    usedAt base n_max mem p = 0 ∨ usedAt base n_max mem p = 1
  /-- Every occupied slot holds a key `< U`. -/
  occupied_key_lt : ∀ p : Fin (2 ^ tableLog n_max),
    usedAt base n_max mem p = 1 → keyAt base n_max mem p < U
  /-- Every occupied slot agrees with the abstract dictionary `s`. -/
  occupied_state : ∀ (p : Fin (2 ^ tableLog n_max)) (u : Fin U),
    usedAt base n_max mem p = 1 → keyAt base n_max mem p = u.val →
    s u = some (valAt base n_max mem p)
  /-- Distinct occupied slots hold distinct keys. -/
  occupied_inj : ∀ p₁ p₂ : Fin (2 ^ tableLog n_max),
    usedAt base n_max mem p₁ = 1 → usedAt base n_max mem p₂ = 1 →
    keyAt base n_max mem p₁ = keyAt base n_max mem p₂ → p₁ = p₂
  /-- Every present key `u` with `s u = some v` is stored at some offset `k < 2 ^ M` from its hash
  bucket with all intermediate probe slots `j < k` occupied. -/
  present_slot : ∀ (u : Fin U) (v : ℕ), s u = some v →
    ∃ k < 2 ^ tableLog n_max,
      let p := probeSlot (tableLog n_max) (hashFn U n_max θ u) k
      usedAt base n_max mem p = 1 ∧
      keyAt base n_max mem p = u.val ∧
      valAt base n_max mem p = v ∧
      ∀ j < k, usedAt base n_max mem (probeSlot (tableLog n_max) (hashFn U n_max θ u) j) = 1
  /-- Every occupied slot `p` has a contiguous occupied probe prefix from its key's hash bucket. -/
  occupied_prefix : ∀ (p : Fin (2 ^ tableLog n_max)) (u : Fin U),
    usedAt base n_max mem p = 1 → keyAt base n_max mem p = u.val →
    ∃ k < 2 ^ tableLog n_max,
      p = probeSlot (tableLog n_max) (hashFn U n_max θ u) k ∧
      ∀ j < k, usedAt base n_max mem (probeSlot (tableLog n_max) (hashFn U n_max θ u) j) = 1

/-- Any finset of occupied slots `A` whose keys belong to `K : Finset (Fin U)` has cardinality
`#A ≤ #K`. -/
theorem TableInv.card_slots_le {U V n_max base : ℕ} {θ : Seed U n_max} {s : Dictionary.State U}
    {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (A : Finset (Fin (2 ^ tableLog n_max))) (K : Finset (Fin U))
    (hused : ∀ p ∈ A, usedAt base n_max mem p = 1)
    (hkey : ∀ p (hp : p ∈ A), ⟨keyAt base n_max mem p, hinv.occupied_key_lt p (hused p hp)⟩ ∈ K) :
    #A ≤ #K := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  · have hU : 0 < U := Nat.lt_of_le_of_lt (Nat.zero_le _) (hinv.occupied_key_lt p₀ (hused p₀ hp₀))
    let f (p : Fin (2 ^ tableLog n_max)) : Fin U :=
      if h : keyAt base n_max mem p < U then ⟨keyAt base n_max mem p, h⟩ else ⟨0, hU⟩
    refine Finset.card_le_card_of_injOn f
      (fun p hp => by simpa [f, hinv.occupied_key_lt p (hused p hp)] using hkey p hp)
      fun p₁ hp₁ p₂ hp₂ heq => hinv.occupied_inj p₁ p₂ (hused p₁ hp₁) (hused p₂ hp₂) ?_
    have h1 := hinv.occupied_key_lt p₁ (hused p₁ hp₁)
    have h2 := hinv.occupied_key_lt p₂ (hused p₂ hp₂)
    simpa [f, h1, h2] using congrArg Fin.val heq

/-- Every occupied slot `p` with `keyAt p ≠ u.val` maps to a key in `(Dictionary.dom s).erase u`. -/
theorem TableInv.key_mem_erase_of_ne {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    {p : Fin (2 ^ tableLog n_max)} (hp : usedAt base n_max mem p = 1) (u : Fin U)
    (hne : keyAt base n_max mem p ≠ u.val) :
    ⟨keyAt base n_max mem p, hinv.occupied_key_lt p hp⟩ ∈ (Dictionary.dom s).erase u :=
  Finset.mem_erase.mpr ⟨fun heq => hne (congrArg Fin.val heq),
    Dictionary.mem_dom_iff.mpr ⟨valAt base n_max mem p,
      hinv.occupied_state p ⟨keyAt base n_max mem p, hinv.occupied_key_lt p hp⟩ hp rfl⟩⟩

/-- Probing for key `u` from bucket `b` continues past offset `d` when slot `probeSlot M b d` is
occupied (`used = 1`) by a key different from `u`. -/
@[expose] def probeContinue (base n_max : ℕ) (mem : ℕ → ℕ) (u : ℕ)
    (b : Fin (2 ^ tableLog n_max)) (d : ℕ) : Prop :=
  usedAt base n_max mem (probeSlot (tableLog n_max) b d) = 1 ∧
  keyAt base n_max mem (probeSlot (tableLog n_max) b d) ≠ u

instance instDecidableProbeContinue (base n_max : ℕ) (mem : ℕ → ℕ) (u : ℕ)
    (b : Fin (2 ^ tableLog n_max)) (d : ℕ) :
    Decidable (probeContinue base n_max mem u b d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- If probing for `u : Fin U` from `b` continues across all `i < d` (`d ≤ 2 ^ M`), then
`d ≤ #((Dictionary.dom s).erase u)`. -/
theorem TableInv.probeContinue_prefix_le {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) {d : ℕ} (hd : d ≤ 2 ^ tableLog n_max)
    (hcont : ∀ i < d, probeContinue base n_max mem u.val b i) :
    d ≤ #((Dictionary.dom s).erase u) := by
  rw [← Finset.card_range d,
    ← Finset.card_image_of_injOn (s := Finset.range d) (probeSlot_injOn_range b hd)]
  refine hinv.card_slots_le _ ((Dictionary.dom s).erase u) (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (hcont i (Finset.mem_range.mp hi)).1
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hinv.key_mem_erase_of_ne (hcont i (Finset.mem_range.mp hi)).1 u
      (hcont i (Finset.mem_range.mp hi)).2

/-- Under `TableInv`, probing for any `u : Fin U` from any `b` stops within
`#((Dictionary.dom s).erase u)` steps. -/
theorem TableInv.exists_not_probeContinue {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    ∃ d ≤ #((Dictionary.dom s).erase u), ¬probeContinue base n_max mem u.val b d := by
  by_contra! h
  have hK_le : #((Dictionary.dom s).erase u) ≤ n_max :=
    Finset.card_erase_le.trans hinv.card_dom_le
  have h8 : 8 * n_max ≤ 2 ^ tableLog n_max := eight_mul_le_tableSize n_max
  have h8' : 8 ≤ 2 ^ tableLog n_max := eight_le_tableSize n_max
  have hle := hinv.probeContinue_prefix_le u b (d := #((Dictionary.dom s).erase u) + 1)
    (by omega) fun i hi => h i (by omega)
  omega

/-- Number of probe steps from `b` before reaching an empty slot or key `u`. -/
@[expose] noncomputable def TableInv.probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) : ℕ :=
  Nat.find (hinv.exists_not_probeContinue u b)

theorem TableInv.probeLen_congr {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem₁ mem₂ : ℕ → ℕ}
    (h₁ : TableInv U V n_max base θ s mem₁) (h₂ : TableInv U V n_max base θ s mem₂)
    (hmem : mem₁ = mem₂) (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    h₁.probeLen u b = h₂.probeLen u b := by
  subst hmem
  rfl

theorem TableInv.probeLen_le_card_erase {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    hinv.probeLen u b ≤ #((Dictionary.dom s).erase u) :=
  (Nat.find_spec (hinv.exists_not_probeContinue u b)).1

theorem TableInv.probeLen_le_n_max {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    hinv.probeLen u b ≤ n_max :=
  (hinv.probeLen_le_card_erase u b).trans (Finset.card_erase_le.trans hinv.card_dom_le)

theorem TableInv.probeLen_lt_tableSize {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    hinv.probeLen u b < 2 ^ tableLog n_max :=
  lt_of_le_of_lt (hinv.probeLen_le_n_max u b) (n_max_lt_tableSize n_max)

theorem TableInv.not_probeContinue_probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) :
    ¬probeContinue base n_max mem u.val b (hinv.probeLen u b) :=
  (Nat.find_spec (hinv.exists_not_probeContinue u b)).2

theorem TableInv.probeContinue_of_lt_probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (b : Fin (2 ^ tableLog n_max)) {d : ℕ} (hd : d < hinv.probeLen u b) :
    probeContinue base n_max mem u.val b d := by
  by_contra hnot
  exact Nat.find_min (hinv.exists_not_probeContinue u b) hd
    ⟨(le_of_lt hd).trans (hinv.probeLen_le_card_erase u b), hnot⟩

/-- Exact characterization of the stopping slot `p = probeSlot M (hashFn U n_max θ u) t` where
`t = hinv.probeLen u (hashFn U n_max θ u)`:
- if `usedAt p = 0`, then `s u = none`;
- if `usedAt p = 1`, then `keyAt p = u.val` and `s u = some (valAt p)`. -/
theorem TableInv.probeStop_spec {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    (usedAt base n_max mem p = 0 ∧ s u = none) ∨
    (usedAt base n_max mem p = 1 ∧ keyAt base n_max mem p = u.val ∧
      s u = some (valAt base n_max mem p)) := by
  rcases hinv.used_bit (probeSlot (tableLog n_max) (hashFn U n_max θ u)
      (hinv.probeLen u (hashFn U n_max θ u))) with hp0 | hp1
  · refine .inl ⟨hp0, ?_⟩
    by_contra! hne
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨k, _, hk_used, hk_key, _, hk_pref⟩ := hinv.present_slot u v hv
    rcases lt_trichotomy k (hinv.probeLen u (hashFn U n_max θ u)) with hlt | rfl | hgt
    · exact (hinv.probeContinue_of_lt_probeLen u _ hlt).2 hk_key
    · exact absurd (hp0.symm.trans hk_used) (by decide)
    · exact absurd (hp0.symm.trans (hk_pref _ hgt)) (by decide)
  · have hkey : keyAt base n_max mem (probeSlot (tableLog n_max) (hashFn U n_max θ u)
        (hinv.probeLen u (hashFn U n_max θ u))) = u.val := by
      have := hinv.not_probeContinue_probeLen u (hashFn U n_max θ u)
      dsimp only [probeContinue] at this; tauto
    exact .inr ⟨hp1, hkey, hinv.occupied_state _ u hp1 hkey⟩

/-- If a slot `p` has `usedAt p = 1` and `keyAt p = u.val`, then `p` is the stopping slot
`probeSlot M (hashFn U n_max θ u) (hinv.probeLen u (hashFn U n_max θ u))`. -/
theorem TableInv.eq_probeStop_of_key_eq {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) {p : Fin (2 ^ tableLog n_max)}
    (hp1 : usedAt base n_max mem p = 1) (hkey : keyAt base n_max mem p = u.val) :
    p = probeSlot (tableLog n_max) (hashFn U n_max θ u)
      (hinv.probeLen u (hashFn U n_max θ u)) := by
  rcases hinv.probeStop_spec u with ⟨_, hnone⟩ | ⟨hstop1, hstop_key, _⟩
  · cases hnone.symm.trans (hinv.occupied_state p u hp1 hkey)
  · exact hinv.occupied_inj p _ hp1 hstop1 (hkey.trans hstop_key.symm)

/-- Zeroed occupancy array `∀ p, usedAt base n_max mem p = 0` satisfies `TableInv` for
`Dictionary.empty U`. -/
theorem tableInv_empty (U V n_max base : ℕ) (θ : Seed U n_max) {mem : ℕ → ℕ}
    (hzero : ∀ p : Fin (2 ^ tableLog n_max), usedAt base n_max mem p = 0) :
    TableInv U V n_max base θ (Dictionary.empty U) mem where
  card_dom_le := by simp [Dictionary.dom_empty]
  values_bounded := Dictionary.valuesBounded_empty U V
  used_bit p := Or.inl (hzero p)
  occupied_key_lt p hp := by rw [hzero p] at hp; cases hp
  occupied_state p _ hp _ := by rw [hzero p] at hp; cases hp
  occupied_inj p₁ _ hp₁ _ _ := by rw [hzero p₁] at hp₁; cases hp₁
  present_slot _ _ h := by simp [Dictionary.empty] at h
  occupied_prefix p _ hp _ := by rw [hzero p] at hp; cases hp

/-- Memory update performed by `insert u v` once the stopping slot `p` has been located:
writes `used[p] ← 1`, `key[p] ← u`, and `val[p] ← v`. -/
@[expose] def insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p : Fin (2 ^ tableLog n_max)) (u v : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update mem (usedBase base n_max + p.val) 1)
      (keyBase base n_max + p.val) u)
    (valBase base n_max + p.val) v

private theorem insertMem_of_outside {base n_max : ℕ} {mem : ℕ → ℕ}
    {p : Fin (2 ^ tableLog n_max)} {u v a : ℕ}
    (ha : a < usedBase base n_max ∨ base + space n_max ≤ a) :
    insertMem base n_max mem p u v a = mem a := by
  have := p.isLt
  dsimp only [usedBase, space, tableSize] at ha
  dsimp only [insertMem, usedBase, keyBase, valBase, tableSize]
  update_simp

theorem usedAt_insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p q : Fin (2 ^ tableLog n_max)) (u v : ℕ) :
    usedAt base n_max (insertMem base n_max mem p u v) q =
      if q = p then 1 else usedAt base n_max mem q := by
  have := p.isLt; have := q.isLt
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, usedAt, insertMem, usedBase, keyBase, valBase, tableSize]
    update_simp
  · have := Fin.val_ne_of_ne hqp
    simp only [hqp, ↓reduceIte, usedAt, insertMem, usedBase, keyBase, valBase, tableSize]
    update_simp

theorem keyAt_insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p q : Fin (2 ^ tableLog n_max)) (u v : ℕ) :
    keyAt base n_max (insertMem base n_max mem p u v) q =
      if q = p then u else keyAt base n_max mem q := by
  have := p.isLt; have := q.isLt
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, keyAt, insertMem, usedBase, keyBase, valBase, tableSize]
    update_simp
  · have := Fin.val_ne_of_ne hqp
    simp only [hqp, ↓reduceIte, keyAt, insertMem, usedBase, keyBase, valBase, tableSize]
    update_simp

theorem valAt_insertMem (base n_max : ℕ) (mem : ℕ → ℕ)
    (p q : Fin (2 ^ tableLog n_max)) (u v : ℕ) :
    valAt base n_max (insertMem base n_max mem p u v) q =
      if q = p then v else valAt base n_max mem q := by
  have := p.isLt; have := q.isLt
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, valAt, insertMem, usedBase, keyBase, valBase, tableSize]
    update_simp
  · have := Fin.val_ne_of_ne hqp
    simp only [hqp, ↓reduceIte, valAt, insertMem, usedBase, keyBase, valBase, tableSize]
    update_simp

/-- Writing `(1, u.val, v)` at the stopping slot `p = probeSlot M (hashFn U n_max θ u) t`
preserves `TableInv` for `Function.update s u (some v)` whenever `.insert u v` is admissible. -/
theorem TableInv.insert_mem {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (v : ℕ) (hvalid : (Dictionary.spec U V n_max).valid s (.insert u v)) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    TableInv U V n_max base θ (Function.update s u (some v))
      (insertMem base n_max mem p u.val v) := by
  let b := hashFn U n_max θ u; let t := hinv.probeLen u b; let p := probeSlot (tableLog n_max) b t
  have hused_ge : ∀ q, usedAt base n_max mem q = 1 →
      usedAt base n_max (insertMem base n_max mem p u.val v) q = 1 := fun q hq => by
    rw [usedAt_insertMem]; split_ifs <;> [rfl; exact hq]
  have hkey_ne : ∀ q, q ≠ p → usedAt base n_max mem q = 1 → keyAt base n_max mem q ≠ u.val :=
    fun q hne hq heq => hne (hinv.eq_probeStop_of_key_eq u hq heq)
  refine
    { card_dom_le := Dictionary.card_dom_step_le_of_valid hinv.card_dom_le (o := .insert u v) hvalid
      values_bounded :=
        Dictionary.valuesBounded_step_of_valid hinv.values_bounded (o := .insert u v) hvalid
      used_bit := fun q => by
        rw [usedAt_insertMem]; split_ifs
        · exact .inr rfl
        · exact hinv.used_bit q
      occupied_key_lt := fun q hq => by
        rw [usedAt_insertMem] at hq; rw [keyAt_insertMem]
        split_ifs at hq ⊢ with hqp
        · exact u.isLt
        · exact hinv.occupied_key_lt q hq
      occupied_state := fun q u' hq hkey => by
        change usedAt base n_max (insertMem base n_max mem p u.val v) q = 1 at hq
        change keyAt base n_max (insertMem base n_max mem p u.val v) q = u'.val at hkey
        change Function.update s u (some v) u' =
          some (valAt base n_max (insertMem base n_max mem p u.val v) q)
        rw [usedAt_insertMem] at hq; rw [keyAt_insertMem] at hkey; rw [valAt_insertMem]
        by_cases hqp : q = p
        · simp only [hqp, ↓reduceIte] at hkey ⊢
          rw [show u' = u from Fin.ext hkey.symm, Function.update_self]
        · simp only [hqp, ↓reduceIte] at hq hkey ⊢
          rw [Function.update_of_ne (fun h => hkey_ne q hqp hq (hkey.trans (congrArg Fin.val h)))]
          exact hinv.occupied_state q u' hq hkey
      occupied_inj := fun q₁ q₂ hq₁ hq₂ hkey => by
        change usedAt base n_max (insertMem base n_max mem p u.val v) q₁ = 1 at hq₁
        change usedAt base n_max (insertMem base n_max mem p u.val v) q₂ = 1 at hq₂
        change keyAt base n_max (insertMem base n_max mem p u.val v) q₁ =
          keyAt base n_max (insertMem base n_max mem p u.val v) q₂ at hkey
        rw [usedAt_insertMem] at hq₁ hq₂; rw [keyAt_insertMem, keyAt_insertMem] at hkey
        by_cases h1 : q₁ = p <;> by_cases h2 : q₂ = p
        · exact h1.trans h2.symm
        · simp only [h1, h2, ↓reduceIte] at hq₂ hkey; exact absurd hkey.symm (hkey_ne q₂ h2 hq₂)
        · simp only [h1, h2, ↓reduceIte] at hq₁ hkey; exact absurd hkey (hkey_ne q₁ h1 hq₁)
        · simp only [h1, h2, ↓reduceIte] at hq₁ hq₂ hkey
          exact hinv.occupied_inj q₁ q₂ hq₁ hq₂ hkey
      present_slot := fun u' v' hst' => by
        by_cases hu' : u' = u
        · subst hu'
          rw [Function.update_self, Option.some.injEq] at hst'; subst hst'
          exact ⟨t, hinv.probeLen_lt_tableSize u' b,
            by rw [usedAt_insertMem, ite_eq_left_iff.mpr fun h => (h rfl).elim],
            by rw [keyAt_insertMem, ite_eq_left_iff.mpr fun h => (h rfl).elim],
            by rw [valAt_insertMem, ite_eq_left_iff.mpr fun h => (h rfl).elim],
            fun j hj => hused_ge _ (hinv.probeContinue_of_lt_probeLen u' b hj).1⟩
        · rw [Function.update_of_ne hu'] at hst'
          obtain ⟨k, hk_lt, hk_used, hk_key, hk_val, hk_pref⟩ := hinv.present_slot u' v' hst'
          have hqp : probeSlot (tableLog n_max) (hashFn U n_max θ u') k ≠ p := fun heq => by
            rcases hinv.probeStop_spec u with ⟨hp0, _⟩ | ⟨_, hp_key, _⟩
            · rw [heq, hp0] at hk_used; cases hk_used
            · exact hu' (Fin.ext (by rw [← hk_key, heq, hp_key]))
          exact ⟨k, hk_lt, hused_ge _ hk_used,
            by rw [keyAt_insertMem, ite_eq_right_iff.mpr fun h => (hqp h).elim, hk_key],
            by rw [valAt_insertMem, ite_eq_right_iff.mpr fun h => (hqp h).elim, hk_val],
            fun j hj => hused_ge _ (hk_pref j hj)⟩
      occupied_prefix := fun q u' hq hkey => by
        change usedAt base n_max (insertMem base n_max mem p u.val v) q = 1 at hq
        change keyAt base n_max (insertMem base n_max mem p u.val v) q = u'.val at hkey
        rw [usedAt_insertMem] at hq; rw [keyAt_insertMem] at hkey
        by_cases hqp : q = p
        · simp only [hqp, ↓reduceIte] at hkey
          obtain rfl : u' = u := Fin.ext hkey.symm
          exact ⟨t, hinv.probeLen_lt_tableSize u' b, hqp,
            fun j hj => hused_ge _ (hinv.probeContinue_of_lt_probeLen u' b hj).1⟩
        · simp only [hqp, ↓reduceIte] at hq hkey
          obtain ⟨k, hk_lt, hk_eq, hk_pref⟩ := hinv.occupied_prefix q u' hq hkey
          exact ⟨k, hk_lt, hk_eq, fun j hj => hused_ge _ (hk_pref j hj)⟩ }

private theorem probeSlot_backSlot_pred {M : ℕ} (b : Fin (2 ^ M)) (a : ℕ) :
    probeSlot M (backSlot M b a) (2 ^ M - 1) = backSlot M b (a + 1) := by
  apply Fin.ext
  simp only [probeSlot, backSlot, cyclicSlotMod]
  have h1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have ha_le : a ≤ 2 ^ M * (a + 1) := by
    calc a ≤ 1 * (a + 1) := by omega
      _ ≤ 2 ^ M * (a + 1) := Nat.mul_le_mul_right (a + 1) h1
  have hmul : 2 ^ M * (a + 1 + 1) = 2 ^ M * (a + 1) + 2 ^ M := by ring
  rw [Nat.mod_add_mod, hmul]
  congr 1
  omega

private theorem probeSlot_sub_mod {M : ℕ} (o b₀ : Fin (2 ^ M)) :
    probeSlot M o ((b₀.val + 2 ^ M - o.val) % 2 ^ M) = b₀ := by
  apply Fin.ext
  simp only [probeSlot, cyclicSlotMod]
  have ho := o.isLt
  have hb := b₀.isLt
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
    show o.val + (b₀.val + 2 ^ M - o.val) = b₀.val + 2 ^ M by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hb]

private theorem TableInv.backSlot_interval_used_ne {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (a : ℕ)
    (hback : ∀ r, 1 ≤ r → r ≤ a →
      usedAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) = 1 ∧
      keyAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) ≠ u.val)
    {idx : ℕ} (hidx : idx < a + hinv.probeLen u (hashFn U n_max θ u)) :
    usedAt base n_max mem
      (probeSlot (tableLog n_max) (backSlot (tableLog n_max) (hashFn U n_max θ u) a) idx) = 1 ∧
    keyAt base n_max mem
      (probeSlot (tableLog n_max) (backSlot (tableLog n_max) (hashFn U n_max θ u) a) idx) ≠
      u.val := by
  by_cases hlt : idx < a
  · rw [probeSlot_backSlot_sub (hashFn U n_max θ u) (by omega)]
    exact hback (a - idx) (by omega) (by omega)
  · have hge : a ≤ idx := le_of_not_gt hlt
    have heq : idx = a + (idx - a) := by omega
    rw [heq, probeSlot_backSlot_add]
    exact hinv.probeContinue_of_lt_probeLen u (hashFn U n_max θ u) (by omega)

private theorem TableInv.cyclicInterval_occ {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (a ℓ : ℕ) (hℓ : ℓ ≤ a + hinv.probeLen u (hashFn U n_max θ u))
    (hback : ∀ r, 1 ≤ r → r ≤ a →
      usedAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) = 1 ∧
      keyAt base n_max mem (backSlot (tableLog n_max) (hashFn U n_max θ u) r) ≠ u.val)
    {q : Fin (2 ^ tableLog n_max)}
    (hq : q ∈ cyclicInterval (tableLog n_max) (hashFn U n_max θ u) a ℓ) :
    usedAt base n_max mem q = 1 ∧ keyAt base n_max mem q ≠ u.val := by
  rw [cyclicInterval_eq_image_probeSlot] at hq
  obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hq
  exact hinv.backSlot_interval_used_ne u a hback (lt_of_lt_of_le (Finset.mem_range.mp hidx) hℓ)

/-- Any occupied slot `q` in a cyclic interval `J` whose immediately preceding slot
`backSlot M b (a + 1)` is empty must contain a key whose home hash bucket lies in `J`. -/
private theorem TableInv.hash_mem_cyclicInterval_of_prev_empty {U V n_max base : ℕ}
    {θ : Seed U n_max} {s : Dictionary.State U} {mem : ℕ → ℕ}
    (hinv : TableInv U V n_max base θ s mem) (b : Fin (2 ^ tableLog n_max)) {a ℓ : ℕ}
    (hℓ_lt : ℓ < 2 ^ tableLog n_max)
    (hprev : usedAt base n_max mem (backSlot (tableLog n_max) b (a + 1)) = 0)
    {q : Fin (2 ^ tableLog n_max)} (hq : q ∈ cyclicInterval (tableLog n_max) b a ℓ)
    (hused : usedAt base n_max mem q = 1) :
    hashFn U n_max θ ⟨keyAt base n_max mem q, hinv.occupied_key_lt q hused⟩ ∈
      cyclicInterval (tableLog n_max) b a ℓ := by
  set x_q : Fin U := ⟨keyAt base n_max mem q, hinv.occupied_key_lt q hused⟩
  obtain ⟨k, hk_lt, hq_eq, hk_pref⟩ := hinv.occupied_prefix q x_q hused rfl
  set o := backSlot (tableLog n_max) b a
  set b₀ := hashFn U n_max θ x_q
  obtain ⟨idx, hidx, hq_idx⟩ := Finset.mem_image.mp (by
    rw [← cyclicInterval_eq_image_probeSlot]; exact hq)
  have hidx_lt : idx < ℓ := Finset.mem_range.mp hidx
  set r := (b₀.val + 2 ^ tableLog n_max - o.val) % 2 ^ tableLog n_max
  have hr_lt : r < 2 ^ tableLog n_max := Nat.mod_lt _ (by positivity)
  have hb₀_eq : probeSlot (tableLog n_max) o r = b₀ := probeSlot_sub_mod o b₀
  by_cases hr_lt_ℓ : r < ℓ
  · rw [cyclicInterval_eq_image_probeSlot]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr_lt_ℓ, hb₀_eq⟩
  · exfalso
    have hq_rk : probeSlot (tableLog n_max) o ((r + k) % 2 ^ tableLog n_max) =
        probeSlot (tableLog n_max) o idx := by
      rw [hq_idx, hq_eq, ← hb₀_eq, probeSlot_add]
      exact Fin.ext (by simp [probeSlot, cyclicSlotMod])
    have hrk_eq := probeSlot_injOn_range o (len := 2 ^ tableLog n_max) le_rfl
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) hq_rk
    have hge : 2 ^ tableLog n_max ≤ r + k := by
      by_contra hlt; rw [Nat.mod_eq_of_lt (not_le.mp hlt)] at hrk_eq; omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hrk_eq
    have hslot : probeSlot (tableLog n_max) b₀ (2 ^ tableLog n_max - 1 - r) =
        backSlot (tableLog n_max) b (a + 1) := by
      rw [← hb₀_eq, probeSlot_add,
        show r + (2 ^ tableLog n_max - 1 - r) = 2 ^ tableLog n_max - 1 by omega]
      exact probeSlot_backSlot_pred b a
    exact absurd (hslot ▸ hk_pref (2 ^ tableLog n_max - 1 - r) (by omega)) (by rw [hprev]; decide)

/-- **Left-anchored cluster witness theorem**: if probing key `u` from `b = hashFn U n_max θ u`
takes `t = hinv.probeLen u b ≥ 1` steps, there is a contiguous cyclic interval
`cyclicInterval M b a ℓ` (`a < ℓ`, `t ≤ ℓ ≤ #((Dictionary.dom s).erase u)`) into which at least
`ℓ` keys of `(Dictionary.dom s).erase u` hash. -/
theorem TableInv.hasClusterWitness_probeLen {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (hinv : TableInv U V n_max base θ s mem)
    (u : Fin U) (ht : 1 ≤ hinv.probeLen u (hashFn U n_max θ u)) :
    ∃ a ℓ, a < ℓ ∧
      hinv.probeLen u (hashFn U n_max θ u) ≤ ℓ ∧
      ℓ ≤ #((Dictionary.dom s).erase u) ∧
      ℓ ≤ #(((Dictionary.dom s).erase u).filter fun x =>
        hashFn U n_max θ x ∈ cyclicInterval (tableLog n_max) (hashFn U n_max θ u) a ℓ) := by
  set b := hashFn U n_max θ u; set t := hinv.probeLen u b; set S := (Dictionary.dom s).erase u
  have ht_le_S : t ≤ #S := hinv.probeLen_le_card_erase u b
  have hS_le_n : #S ≤ n_max := Finset.card_erase_le.trans hinv.card_dom_le
  have h8n : 8 * n_max ≤ 2 ^ tableLog n_max := eight_mul_le_tableSize n_max
  have h8 : 8 ≤ 2 ^ tableLog n_max := eight_le_tableSize n_max
  have hex_empty : ∃ r, 1 ≤ r ∧ r ≤ #S + 1 - t ∧
      ¬(usedAt base n_max mem (backSlot (tableLog n_max) b r) = 1 ∧
        keyAt base n_max mem (backSlot (tableLog n_max) b r) ≠ u.val) := by
    by_contra! hall
    set a_max := #S + 1 - t
    set A := cyclicInterval (tableLog n_max) b a_max (#S + 1)
    have hocc : ∀ q ∈ A, usedAt base n_max mem q = 1 ∧ keyAt base n_max mem q ≠ u.val :=
      fun _ hq => hinv.cyclicInterval_occ u a_max (#S + 1)
        (by dsimp only [a_max, t, b, S]; omega) hall hq
    have hcardA : #A = #S + 1 := card_cyclicInterval b a_max (by omega)
    have hle := hinv.card_slots_le A S (fun q hq => (hocc q hq).1)
      fun q hq => hinv.key_mem_erase_of_ne (hocc q hq).1 u (hocc q hq).2
    omega
  set r₀ := Nat.find hex_empty
  obtain ⟨hr₀_ge, hr₀_le, hr₀_not⟩ := Nat.find_spec hex_empty
  set a := r₀ - 1; set ℓ := a + t; have ha1 : a + 1 = r₀ := by omega
  have hback_occ : ∀ r, 1 ≤ r → r ≤ a →
      usedAt base n_max mem (backSlot (tableLog n_max) b r) = 1 ∧
      keyAt base n_max mem (backSlot (tableLog n_max) b r) ≠ u.val := fun r hr1 hra => by
    have hmin := Nat.find_min hex_empty (show r < r₀ by omega); push Not at hmin
    exact hmin hr1 (by omega)
  have hprev_zero : usedAt base n_max mem (backSlot (tableLog n_max) b (a + 1)) = 0 := by
    rcases hinv.used_bit (backSlot (tableLog n_max) b (a + 1)) with h0 | h1
    · exact h0
    · exfalso
      have heq := hinv.eq_probeStop_of_key_eq u h1 (by rw [ha1] at h1 ⊢; tauto)
      rw [← probeSlot_zero (backSlot (tableLog n_max) b (a + 1)),
        ← probeSlot_backSlot_add b (a + 1) t] at heq
      have hinj := probeSlot_injOn_range (backSlot (tableLog n_max) b (a + 1))
        (len := 2 ^ tableLog n_max) le_rfl
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) heq
      omega
  refine ⟨a, ℓ, by omega, by omega, by omega, ?_⟩
  set J := cyclicInterval (tableLog n_max) b a ℓ
  have hJ_occ : ∀ q ∈ J, usedAt base n_max mem q = 1 ∧ keyAt base n_max mem q ≠ u.val :=
    fun _ hq => hinv.cyclicInterval_occ u a ℓ le_rfl hback_occ hq
  rw [← card_cyclicInterval b a (show ℓ ≤ 2 ^ tableLog n_max by omega)]
  exact hinv.card_slots_le J (S.filter fun x => hashFn U n_max θ x ∈ J)
    (fun q hq => (hJ_occ q hq).1) fun q hq => Finset.mem_filter.mpr
      ⟨hinv.key_mem_erase_of_ne (hJ_occ q hq).1 u (hJ_occ q hq).2,
        hinv.hash_mem_cyclicInterval_of_prev_empty b (by omega) hprev_zero hq (hJ_occ q hq).1⟩

noncomputable instance instDecidablePredHasClusterWitness (U n_max : ℕ) (S : Finset (Fin U))
    (u : Fin U) (θ : Seed U n_max) :
    DecidablePred (HasClusterWitness (hashFn U n_max) S u θ) :=
  Classical.decPred _

/-- Maximum `t ≤ #S` satisfying `HasClusterWitness (hashFn U n_max) S u θ t` (depends only on
`θ`). -/
@[expose] noncomputable def maxWitnessProbe (U n_max : ℕ) (S : Finset (Fin U)) (u : Fin U)
    (θ : Seed U n_max) : ℕ :=
  have h0 : 0 ∈ (Finset.range (#S + 1)).filter (HasClusterWitness (hashFn U n_max) S u θ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), fun h => by omega⟩
  ((Finset.range (#S + 1)).filter (HasClusterWitness (hashFn U n_max) S u θ)).max' ⟨0, h0⟩

theorem le_maxWitnessProbe {U n_max : ℕ} {S : Finset (Fin U)} {u : Fin U}
    {θ : Seed U n_max} {t : ℕ} (ht_le : t ≤ #S)
    (hwit : HasClusterWitness (hashFn U n_max) S u θ t) :
    t ≤ maxWitnessProbe U n_max S u θ := by
  dsimp only [maxWitnessProbe]
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hwit⟩)

theorem hasClusterWitness_maxWitnessProbe (U n_max : ℕ) (S : Finset (Fin U)) (u : Fin U)
    (θ : Seed U n_max) :
    HasClusterWitness (hashFn U n_max) S u θ (maxWitnessProbe U n_max S u θ) := by
  dsimp only [maxWitnessProbe]
  exact (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

/-- For any coupled state distribution `ν : PMF (Seed U n_max × α)` whose seed marginal is bounded
by `seedLaw U n_max`, any step counter `T_probe : Seed U n_max × α → ℕ` bounded by `hinv.probeLen`
on `ν.support` has expected value at most `288`. -/
theorem tsum_probeLen_le {α : Type*} {U V n_max base : ℕ}
    {s : Dictionary.State U}
    (u : Fin U) (ν : PMF (Seed U n_max × α))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ seedLaw U n_max θ)
    (T_probe : Seed U n_max × α → ℕ)
    (hT : ∀ p ∈ ν.support, ∃ (mem : ℕ → ℕ) (hinv : TableInv U V n_max base p.1 s mem),
      T_probe p ≤ hinv.probeLen u (hashFn U n_max p.1 u)) :
    (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ 288 := by
  obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
  obtain ⟨_, hinv₀, _⟩ := hT p₀ hp₀
  set S := (Dictionary.dom s).erase u
  have hpt : ∀ p, ν p * (T_probe p : ℝ≥0∞) ≤
      ν p * (maxWitnessProbe U n_max S u p.1 : ℝ≥0∞) := fun p => by
    by_cases hp : p ∈ ν.support
    · obtain ⟨_, hinv, hle⟩ := hT p hp
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr <| hle.trans <| le_maxWitnessProbe
        (hinv.probeLen_le_card_erase u _) fun ht => hinv.hasClusterWitness_probeLen u ht) zero_le
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hp]
  calc (∑' p, ν p * (T_probe p : ℝ≥0∞))
      ≤ ∑' p, ν p * (maxWitnessProbe U n_max S u p.1 : ℝ≥0∞) := tsum_le_tsum hpt
    _ = ∑' θ, (ν.map Prod.fst) θ * (maxWitnessProbe U n_max S u θ : ℝ≥0∞) :=
        (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
          fun θ => (maxWitnessProbe U n_max S u θ : ℝ≥0∞)).symm
    _ ≤ ∑' θ, seedLaw U n_max θ * (maxWitnessProbe U n_max S u θ : ℝ≥0∞) :=
        tsum_le_tsum fun θ => mul_le_mul_of_nonneg_right (hseed θ) zero_le
    _ ≤ 288 := tsum_uniform_probe_le_of_cluster_witness (isKWiseIndependentHash_hashFn U n_max)
        S (Finset.notMem_erase u _) (Finset.card_erase_le.trans hinv₀.card_dom_le)
        (eight_mul_le_tableSize n_max) _ (hasClusterWitness_maxWitnessProbe U n_max S u)

/-! ## Section 3: Word-RAM register layout, programs, and operational execution -/

open Cslib.DataStructure.HashFamily.WordRAM.Tabulation

/-- Total number of registers used by the linear-probing subroutine (`0 .. 17` for `KWise` and
probe scratch, `18 .. 23` for allocation, zero-fill, and operation arguments). -/
abbrev rLP : ℕ := 24

/-- Register embedding `Fin 18 → Fin 24` mapping `KWise` registers `0 .. 17` to `0 .. 17`. -/
@[expose] def kwiseMap : Fin 18 → Fin 24 :=
  Fin.castLE (by decide)

theorem injective_kwiseMap : Function.Injective kwiseMap :=
  Fin.castLE_injective (by decide)

/-- Allocation span program: copies `frontierReg` (`18`) to `baseReg` (`0`) and advances
`frontierReg` by `space n_max`. -/
@[expose] def allocSpan (n_max : ℕ) : Code .exact 24 :=
  .seq (.op (.copy 0 18))
  (.seq (.op (.const 3 (space n_max)))
        (.op (.exactBin .add 18 0 3)))

/-- `18`-register initialization program setting `(n_max, U, tableLog n_max)` in registers
`1, 2, 3` and invoking `KWise.initCode 5`. -/
@[expose] def initSetup18 (U n_max : ℕ) : Code .exact 18 :=
  .seq (.op (.const 1 n_max))
  (.seq (.op (.const 2 U))
  (.seq (.op (.const 3 (tableLog n_max)))
        (KWise.initCode 5)))

/-- `24`-register initialization program. -/
@[expose] def initSetup (U n_max : ℕ) : Code .exact 24 :=
  (initSetup18 U n_max).rename kwiseMap

/-- Single-slot probe inspection program: given current slot `pos` in `reg 2`, loads
`used[pos]` into `reg 9` (`cellReg`) and sets `reg 7` (`contReg`) to `1` if
`used[pos] = 1 ∧ key[pos] ≠ u.val`, or `0` otherwise. -/
@[expose] def probeCheckCode : Code .exact 24 :=
  .seq (.op (.exactBin .add 8 4 2))
  (.seq (.op (.load 9 8))
        (.branch (.eq 9 10)
          (.seq (.op (.exactBin .add 8 5 2))
          (.seq (.op (.load 8 8))
                (.branch (.eq 8 1)
                  (.op (.const 7 0))
                  (.op (.const 7 1)))))
          (.op (.const 7 0))))

/-- Probe setup program: initializes `maskReg` (`3`), `usedBaseReg` (`4`), `keyBaseReg` (`5`),
`valBaseReg` (`6`), and `cOneReg` (`10`), then inspects the home slot `pos = (h u).val` (`reg 2`).
-/
@[expose] def probeSetupCode (n_max : ℕ) : Code .exact 24 :=
  .seq (.op (.const 3 (tableSize n_max - 1)))
  (.seq (.op (.const 4 (KWise.space n_max 5)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (tableSize n_max)))
  (.seq (.op (.exactBin .add 5 4 5))
  (.seq (.op (.const 6 (tableSize n_max)))
  (.seq (.op (.exactBin .add 6 5 6))
  (.seq (.op (.const 10 1))
        probeCheckCode)))))))

/-- Probe loop body: advances `pos ← (pos + 1) &&& (2 ^ M - 1)` in `reg 2` and inspects the new
slot via `probeCheckCode`. -/
@[expose] def probeBody : Code .exact 24 :=
  .seq (.op (.exactBin .add 2 2 10))
  (.seq (.op (.exactBin .and 2 2 3))
        probeCheckCode)

/-- Linear probe loop `while contReg == 1 do probeBody`. -/
@[expose] def probeLoop : Code .exact 24 :=
  .loop (.eq 7 10) probeBody

/-- Insertion suffix after `probeLoop` halts at slot `pos` (`reg 2`): stores `used[pos] ← 1`,
`key[pos] ← u.val` (`reg 1`), `val[pos] ← v` (`reg 23`), and sets `outReg` (`reg 2`) to `0`. -/
@[expose] def insertFinishCode : Code .exact 24 :=
  .seq (.op (.exactBin .add 8 4 2))
  (.seq (.op (.store 8 10))
  (.seq (.op (.exactBin .add 8 5 2))
  (.seq (.op (.store 8 1))
  (.seq (.op (.exactBin .add 8 6 2))
  (.seq (.op (.store 8 23))
        (.op (.const 2 0)))))))

/-- Lookup suffix after `probeLoop` halts at slot `pos` (`reg 2`) with `used[pos]` in `reg 9`:
if `reg 9 == 1`, loads `val[pos]` and writes `val[pos] + 1` into `reg 2`; otherwise writes `0`
into `reg 2`. -/
@[expose] def queryFinishCode : Code .exact 24 :=
  .branch (.eq 9 10)
    (.seq (.op (.exactBin .add 8 6 2))
    (.seq (.op (.load 2 8))
          (.op (.exactBin .add 2 2 10))))
    (.op (.const 2 0))

/-- Unified operation program for `query u` (`opReg = 0`) and `insert u v` (`opReg = 1`). -/
@[expose] def opCode (n_max : ℕ) : Code .exact 24 :=
  .seq ((KWise.evalCode 5).rename kwiseMap)
  (.seq (probeSetupCode n_max)
  (.seq probeLoop
        (.branch (.eq 22 10) insertFinishCode queryFinishCode)))

/-- `SubroutineCode` bundle for linear probing. -/
@[expose] def subroutineCode (U n_max : ℕ) : SubroutineCode .exact rLP 0 where
  allocSpan := allocSpan n_max
  initSetup := initSetup U n_max
  code := opCode n_max
  baseReg := 0
  frontierReg := 18
  zeroReg := 19
  oneReg := 20
  curReg := 21
  incCur := .exactBin .add 21 21 20
  initParams := Fin.elim0
  input i := decide (i = 1 ∨ i = 22 ∨ i = 23)
  output := 2

/-- Standalone argument encoding for `Dictionary.Op U`. -/
@[expose] def encodeOp {U : ℕ} (o : Dictionary.Op U) (i : Fin rLP) : ℕ :=
  match o with
  | .query u =>
    if i = 1 then u.val else 0
  | .insert u v =>
    if i = 1 then u.val else if i = 22 then 1 else if i = 23 then v else 0

/-- Argument-matching predicate for `Dictionary.Op U`. -/
@[expose] def argMatchOp {U : ℕ} (o : Dictionary.Op U) (regs : Fin rLP → ℕ) : Prop :=
  match o with
  | .query u => regs 1 = u.val ∧ regs 22 = 0
  | .insert u v => regs 1 = u.val ∧ regs 22 = 1 ∧ regs 23 = v

/-- Output decoder for `Dictionary.Op U`: for `query u`, `0` decodes to `none` and `k + 1` decodes
to `some k`; for `insert u v`, decodes to `some ()`. -/
@[expose] def decodeOp {U V n_max : ℕ} (o : (Dictionary.spec U V n_max).Op)
    (regs : Fin rLP → ℕ) : Option ((Dictionary.spec U V n_max).Result o) :=
  match o with
  | .query _ => some (if regs 2 = 0 then none else some (regs 2 - 1))
  | .insert _ _ => some ()

/-- Expected instruction count for `initSetup U n_max`:
`KWise.initTableSteps n_max U (tableLog n_max) + 38 = O(n_max + log U)`. -/
@[expose] def setupTime (U n_max : ℕ) : ℕ :=
  KWise.initTableSteps n_max U (tableLog n_max) + 38

/-- Expected instruction charge per dictionary operation:
`KWise.evalSteps n_max U (tableLog n_max) 5 + 3483 = O(L ^ 2 + 1)`. -/
@[expose] def charge (U n_max : ℕ) : ℕ :=
  KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * 288 + 27

/-- Full seed-coupled representation invariant `Rep U V n_max w base θ s x` for linear probing. -/
structure Rep (U V n_max w base : ℕ) (θ : Seed U n_max) (s : Dictionary.State U)
    (x : Data rLP) : Prop where
  /-- Machine configuration is word-bounded at width `w`. -/
  bounded : x.Bounded w
  /-- Persistent base register `reg 0` holds `base`. -/
  reg_base : x.regs 0 = base
  /-- Embedded `5`-wise independent hash representation at `[base, base + KWise.space n_max 5)`. -/
  kwise_rep : KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ x.mem
  /-- Open-addressed linear-probing table invariant at `[usedBase, valBase + tableSize n_max)`. -/
  table_inv : TableInv U V n_max base θ s x.mem

theorem Rep.unique {U V n_max w base : ℕ} {θ : Seed U n_max}
    {s₁ s₂ : Dictionary.State U} {x : Data rLP}
    (h₁ : Rep U V n_max w base θ s₁ x) (h₂ : Rep U V n_max w base θ s₂ x) :
    s₁ = s₂ := by
  funext u
  rcases h₁.table_inv.probeStop_spec u with ⟨hp0, hnone₁⟩ | ⟨hp1, hkey₁, hsome₁⟩ <;>
    rcases h₂.table_inv.probeStop_spec u with ⟨hp0', hnone₂⟩ | ⟨hp1', hkey₂, hsome₂⟩
  · exact hnone₁.trans hnone₂.symm
  · exact absurd (hp0.symm.trans (h₁.table_inv.eq_probeStop_of_key_eq u hp1' hkey₂ ▸ hp1'))
      (by decide)
  · exact absurd (hp0'.symm.trans (h₂.table_inv.eq_probeStop_of_key_eq u hp1 hkey₁ ▸ hp1))
      (by decide)
  · rw [hsome₁, hsome₂, h₁.table_inv.occupied_inj _ _ hp1 hp1' (hkey₁.trans hkey₂.symm)]

/-- `KWise.Rep` depends only on addresses in `[base, base + KWise.space n_max 5)`. -/
private theorem kwise_rep_congr {U n_max base : ℕ} {θ : Seed U n_max} {mem mem' : ℕ → ℕ}
    (hrep : KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ mem)
    (heq : ∀ a, a < base + KWise.space n_max 5 → base ≤ a → mem' a = mem a) :
    KWise.Rep base (KWise.chunkBits n_max) U (tableLog n_max) 5 θ mem' := by
  have hsp : KWise.space n_max 5 = 8 + 5 + 2 ^ (2 * KWise.chunkBits n_max) := rfl
  have hpow : 0 < 2 ^ (2 * KWise.chunkBits n_max) := Nat.two_pow_pos _
  have hm (k : ℕ) (hk : k < KWise.space n_max 5) : mem' (base + k) = mem (base + k) :=
    heq (base + k) (by omega) (Nat.le_add_right _ _)
  rcases hrep with ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, htab⟩, hseed⟩
  refine ⟨⟨?_, hm 1 (by omega) ▸ h1, hm 2 (by omega) ▸ h2, hm 3 (by omega) ▸ h3,
    hm 4 (by omega) ▸ h4, hm 5 (by omega) ▸ h5, hm 6 (by omega) ▸ h6,
    hm 7 (by omega) ▸ h7, fun idx hi => ?_⟩,
    hseed.congr_of_footprint fun a hlo hhi => heq a (by omega) hlo⟩
  · simpa only [Nat.add_zero] using (hm 0 (by omega)).trans h0
  · simpa only [Nat.add_assoc] using (hm (8 + 5 + idx) (by omega)).trans (by
      simpa only [Nat.add_assoc] using htab idx hi)

/-- `TableInv` depends only on addresses in `[base, base + space n_max)`. -/
private theorem tableInv_congr {U V n_max base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem mem' : ℕ → ℕ}
    (hinv : TableInv U V n_max base θ s mem)
    (heq : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem' a = mem a) :
    TableInv U V n_max base θ s mem' := by
  have hused (p : Fin (2 ^ tableLog n_max)) : usedAt base n_max mem' p = usedAt base n_max mem p :=
    heq _ (Block.mem_footprint.mpr ⟨by wram_omega,
      by have : p.val < tableSize n_max := p.isLt; wram_omega⟩)
  have hkey (p : Fin (2 ^ tableLog n_max)) : keyAt base n_max mem' p = keyAt base n_max mem p :=
    heq _ (Block.mem_footprint.mpr ⟨by wram_omega,
      by have : p.val < tableSize n_max := p.isLt; wram_omega⟩)
  have hval (p : Fin (2 ^ tableLog n_max)) : valAt base n_max mem' p = valAt base n_max mem p :=
    heq _ (Block.mem_footprint.mpr ⟨by wram_omega,
      by have : p.val < tableSize n_max := p.isLt; wram_omega⟩)
  exact
    { card_dom_le := hinv.card_dom_le
      values_bounded := hinv.values_bounded
      used_bit := fun p => by simpa only [hused] using hinv.used_bit p
      occupied_key_lt := fun p hp => by
        rw [hused] at hp; rw [hkey]; exact hinv.occupied_key_lt p hp
      occupied_state := fun p u hp hk => by
        rw [hused] at hp; rw [hkey] at hk; rw [hval]; exact hinv.occupied_state p u hp hk
      occupied_inj := fun p q hp hq hk => by
        rw [hused] at hp hq; rw [hkey, hkey] at hk; exact hinv.occupied_inj p q hp hq hk
      present_slot := fun u v hsu => by
        obtain ⟨k, hk_lt, hp, hk, hv, hpref⟩ := hinv.present_slot u v hsu
        exact ⟨k, hk_lt, by rwa [hused], by rwa [hkey], by rwa [hval],
          fun j hj => by rw [hused]; exact hpref j hj⟩
      occupied_prefix := fun p u hp hk => by
        rw [hused] at hp; rw [hkey] at hk
        obtain ⟨k, hk_lt, hp_eq, hpref⟩ := hinv.occupied_prefix p u hp hk
        exact ⟨k, hk_lt, hp_eq, fun j hj => by rw [hused]; exact hpref j hj⟩ }

theorem Rep.supported {U V n_max w base : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x x' : Data rLP}
    (hregs : ∀ i, (subroutineCode U n_max).input i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w)
    (hrep : Rep U V n_max w base θ s x) :
    Rep U V n_max w base θ s x' :=
  ⟨hbdd, (hregs 0 rfl).trans hrep.reg_base,
    kwise_rep_congr hrep.kwise_rep fun a hlt hge =>
      hmem a (Block.mem_footprint.mpr ⟨hge, by dsimp only [space]; omega⟩),
    tableInv_congr hrep.table_inv hmem⟩

private theorem fits_max_U_add_one_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w (max U 2 + 1) := by
  set q := trinomialDeg U (tableLog n_max)
  have hq : 2 ≤ q := by
    have : 1 ≤ 3 ^ trinomialStep U (tableLog n_max) := Nat.one_le_pow _ 3 (by decide)
    dsimp only [q, trinomialDeg]; omega
  have hU_le : U ≤ 2 ^ q := le_two_pow_trinomialDeg U (tableLog n_max)
  have h4 : 4 ≤ 2 ^ q := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hq
  have h2q : 2 ^ (q + 1) ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by decide) (by omega)
  have hle_w : 2 ^ (2 * q) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  rw [pow_succ] at h2q; change max U 2 + 1 < 2 ^ w; omega

private theorem fits_U_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w U :=
  (fits_max_U_add_one_of_hw hw).of_le (by omega)

private theorem fits_tableLog_of_hw {w U n_max : ℕ}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w) :
    Fits w (tableLog n_max) := by
  have := le_trinomialDeg U (tableLog n_max)
  have := Nat.lt_two_pow_self (n := trinomialDeg U (tableLog n_max))
  exact (KWise.fits_two_pow_trinomialDeg hw).of_le (by omega)

private theorem fits_max_n_max_of_space {w base n_max : ℕ}
    (hfit : Fits w (base + space n_max)) :
    Fits w (max n_max 2) := by
  have := eight_mul_le_tableSize n_max
  have := eight_le_tableSize n_max
  have : tableSize n_max ≤ base + space n_max := by wram_omega
  exact hfit.of_le (by omega)

/-- `allocSpan n_max` executes in `3` steps, copying `frontierReg` (`18`) to `baseReg` (`0`) and
advancing `frontierReg` to `base + space n_max`. -/
theorem allocSpan_execWithin {w base n_max : ℕ} {x : Data rLP}
    (hfr : x.regs 18 = base) (hfit : Fits w (base + space n_max)) :
    ∃ x₁ : Data rLP,
      ExecWithin w (allocSpan n_max) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base ∧
      x₁.regs 18 = base + space n_max := by
  refine WP.exists_execWithin ?_
  unfold allocSpan
  wram_exec [hfr, hfit]
  wram_simp

/-- `initSetup U n_max` initializes the `5`-wise independent hash table and leaves the zeroed
linear-probing arrays representing the empty dictionary in at most `setupTime U n_max` expected
instructions. -/
theorem initSetup_exec {U V n_max w base : ℕ} {x₁ : Data rLP}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs 0 = base)
    (hfr : x₁.regs 18 = base + space n_max)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (Seed U n_max × Data rLP),
      ExecCodeDist w (initSetup U n_max) x₁ (ν₀.map Prod.snd) (setupTime U n_max) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw U n_max θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs 18 = base + space n_max ∧
        Rep U V n_max w base p.1 (Dictionary.empty U) p.2 ∧
        0 ≤ 0 ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem p.2.mem := by
  have hfit_kwise : Fits w (base + KWise.space n_max 5) := hfit_space.of_le (by wram_omega)
  have hfit_n : Fits w (max n_max 2) := fits_max_n_max_of_space hfit_space
  have hfit_U1 : Fits w (max U 2 + 1) := fits_max_U_add_one_of_hw hw
  have hfit_M : Fits w (tableLog n_max) := fits_tableLog_of_hw hw
  have hfit_q := KWise.fits_two_pow_trinomialDeg hw
  have hfit_end : Fits w (base + 8 + 5) := by
    have : KWise.space n_max 5 = 8 + 5 + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    have : 0 < 2 ^ (2 * KWise.chunkBits n_max) := Nat.two_pow_pos _
    exact hfit_kwise.of_le (by omega)
  set x₀ : Data 18 := x₁.comap kwiseMap
  set s3 : Data 18 := ((x₀.set 1 n_max).set 2 U).set 3 (tableLog n_max)
  obtain ⟨dTab, hdTab_exec, htab, hdTab_0, hdTab_out⟩ :=
    KWise.initTableCode_execWithin (x := s3)
      (by wram_simp [s3]; exact hb) (by wram_simp [s3]) (by wram_simp [s3])
      (by wram_simp [s3]) hfit_kwise hfit_n hfit_U1 hfit_q
  set m := KWise.resampleComp base U (tableLog n_max) 5 dTab
  have hsupp := fun z (hz : z ∈ m.support) => KWise.mem_support_resampleComp htab hdTab_0 hz
  have hdist_res : ExecCodeDist w (KWise.resampleCode 5) dTab (m.eval.map Prod.fst) 35 :=
    ExecCodeDist.of_execRand_le (KWise.resampleCode_execRand htab hdTab_0 hfit_end hfit_q)
      fun z hz => (hsupp z hz).2
  have hdist_18 : ExecCodeDist w (initSetup18 U n_max) x₀ (m.eval.map Prod.fst)
      (setupTime U n_max) := by
    unfold initSetup18
    wram_rand_exec [hfit_M]
    wram_rand_call hdTab_exec
    wram_rand_call hdist_res
    refine ⟨rfl, ?_⟩
    dsimp only [setupTime]; norm_cast; omega
  have hdist_24 := hdist_18.rename injective_kwiseMap
  refine ⟨m.eval.map fun z =>
    (KWise.extractSeeds base U (tableLog n_max) 5 z.1.mem, z.1.extend kwiseMap x₁),
    hdist_24.congr_dist (by rw [PMF.map_comp, PMF.map_comp]; rfl) le_rfl,
    fun θ => by
      rw [PMF.map_comp]; dsimp only [Function.comp_def]
      rw [KWise.map_extractSeeds_eval_resampleComp base U (tableLog n_max) 5 dTab, one_mul]
      exact le_rfl,
    fun p hp => ?_⟩
  supp_cases hp with ⟨z, hz_eval, rfl⟩
  have hz_supp : z ∈ m.support := by rwa [← ProbComp.support_eval m]
  obtain ⟨⟨hkrep, hz_0, hz_out⟩, _⟩ := hsupp z hz_supp
  have hp_mem : z.1.extend kwiseMap x₁ ∈
      ((m.eval.map Prod.fst).map (·.extend kwiseMap x₁)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨z.1, (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz_eval, rfl⟩, rfl⟩
  have hmem_out : ∀ a, a < base ∨ base + KWise.space n_max 5 ≤ a → z.1.mem a = x₁.mem a := by
    intro a ha
    have : KWise.space n_max 5 = 8 + 5 + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    have : 0 < 2 ^ (2 * KWise.chunkBits n_max) := Nat.two_pow_pos _
    exact (hz_out a (by omega)).trans (hdTab_out a ha)
  have hempty : ∀ j : Fin (2 ^ tableLog n_max),
      usedAt base n_max (z.1.extend kwiseMap x₁).mem j = 0 := fun j => by
    have : j.val < tableSize n_max := j.isLt
    change z.1.mem (usedBase base n_max + j.val) = 0
    rw [hmem_out _ (.inr (by wram_omega))]
    exact hz _ (Block.mem_footprint.mpr ⟨by wram_omega, by wram_omega⟩)
  refine ⟨by rw [Data.extend_regs_of_notMem _ _ (by decide : (18 : Fin 24) ∉ Set.range kwiseMap),
    hfr], ⟨hdist_24.bounded hx₁ _ hp_mem, ?_, hkrep, tableInv_empty U V n_max base _ hempty⟩,
    le_rfl, Modifies.block_iff.mpr fun a ha => hmem_out a (by wram_omega)⟩
  change ((z.1.extend kwiseMap x₁).comap kwiseMap).regs 0 = base
  rw [Data.comap_extend injective_kwiseMap]; exact hz_0

/-- Single-slot inspection `probeCheckCode` executes in at most `8` deterministic steps, loading
`usedAt base n_max x.mem pos` into `reg 9` and setting `reg 7` to `1` iff
`usedAt base n_max x.mem pos = 1 ∧ keyAt base n_max x.mem pos ≠ u.val`. -/
theorem probeCheckCode_execWithin {U w base n_max : ℕ} (u : Fin U)
    (pos : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = pos.val)
    (h3 : x.regs 3 = tableSize n_max - 1)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max)) :
    ∃ y : Data rLP,
      ExecWithin w probeCheckCode x y 8 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = pos.val ∧
      y.regs 3 = tableSize n_max - 1 ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 7 = (if usedAt base n_max x.mem pos = 1 ∧
        keyAt base n_max x.mem pos ≠ u.val then 1 else 0) ∧
      y.regs 9 = usedAt base n_max x.mem pos ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  have hpos_lt : pos.val < tableSize n_max := pos.isLt
  have hts_pos : 0 < tableSize n_max := tableSize_pos n_max
  have hused : x.mem (usedBase base n_max + pos.val) = usedAt base n_max x.mem pos := rfl
  have hkey : x.mem (keyBase base n_max + pos.val) = keyAt base n_max x.mem pos := rfl
  unfold probeCheckCode
  wram_exec (disch := first | fits | layout_omega) [h1, h2, h4, h5, h10, hused, hkey]
  all_goals wram_simp [h0, h1, h2, h3, h4, h5, h6, h10]
  all_goals split_ifs <;> omega
/-- `probeSetupCode n_max` executes in at most `16` deterministic steps, initializing registers
`3, 4, 5, 6, 10` and running `probeCheckCode` on the initial hash bucket `pos`. -/
theorem probeSetupCode_execWithin {U w base n_max : ℕ} (u : Fin U)
    (pos : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = pos.val)
    (hfit_space : Fits w (base + space n_max)) :
    ∃ y : Data rLP,
      ExecWithin w (probeSetupCode n_max) x y 16 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = pos.val ∧
      y.regs 3 = tableSize n_max - 1 ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 7 = (if usedAt base n_max x.mem pos = 1 ∧
        keyAt base n_max x.mem pos ≠ u.val then 1 else 0) ∧
      y.regs 9 = usedAt base n_max x.mem pos ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  have hts_pos : 0 < tableSize n_max := tableSize_pos n_max
  have hub : base + KWise.space n_max 5 = usedBase base n_max := rfl
  have hkb : usedBase base n_max + tableSize n_max = keyBase base n_max := rfl
  have hvb : keyBase base n_max + tableSize n_max = valBase base n_max := rfl
  unfold probeSetupCode
  wram_exec (disch := first | fits | layout_omega) [h0, hub, hkb, hvb]
  wram_call (probeCheckCode_execWithin u pos (by regs_frame) (by regs_frame)
    (by regs_frame) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
    (by wram_simp) hfit_space) with y hy
  exact ⟨by omega, by wram_simp at hy; exact hy⟩

/-- One iteration of `probeBody` advances `pos` to `probeSlot (tableLog n_max) pos 1` and inspects
the new slot in at most `10` deterministic steps. -/
theorem probeBody_execWithin {U w base n_max : ℕ} (u : Fin U)
    (pos : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = pos.val)
    (h3 : x.regs 3 = tableSize n_max - 1)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max)) :
    let pos' := probeSlot (tableLog n_max) pos 1
    ∃ y : Data rLP,
      ExecWithin w probeBody x y 10 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = pos'.val ∧
      y.regs 3 = tableSize n_max - 1 ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 7 = (if usedAt base n_max x.mem pos' = 1 ∧
        keyAt base n_max x.mem pos' ≠ u.val then 1 else 0) ∧
      y.regs 9 = usedAt base n_max x.mem pos' ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 := by
  set pos' := probeSlot (tableLog n_max) pos 1
  have hpos_lt : pos.val < tableSize n_max := pos.isLt
  have hpos'_lt : pos'.val < tableSize n_max := pos'.isLt
  have hand_eq : (pos.val + 1) &&& (tableSize n_max - 1) = pos'.val :=
    Nat.and_two_pow_sub_one_eq_mod (pos.val + 1) (tableLog n_max)
  unfold probeBody
  wram_exec (disch := first | fits | layout_omega) [h2, h3, h10, hand_eq]
  wram_call (probeCheckCode_execWithin u pos' (by regs_frame) (by regs_frame)
    (by wram_simp) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    (by regs_frame) hfit_space) with y hy
  exact ⟨by omega, by wram_simp at hy; exact hy⟩

private theorem probeLoop_execWithin_aux {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {mem : ℕ → ℕ}
    (hinv : TableInv U V n_max base θ s mem) (u : Fin U)
    (hfit_space : Fits w (base + space n_max)) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    ∀ rem k (d : Data rLP),
      k + rem = t → d.mem = mem →
      d.regs 0 = base → d.regs 1 = u.val →
      d.regs 2 = (probeSlot (tableLog n_max) b k).val →
      d.regs 3 = tableSize n_max - 1 →
      d.regs 4 = usedBase base n_max →
      d.regs 5 = keyBase base n_max →
      d.regs 6 = valBase base n_max →
      d.regs 7 = (if usedAt base n_max mem (probeSlot (tableLog n_max) b k) = 1 ∧
        keyAt base n_max mem (probeSlot (tableLog n_max) b k) ≠ u.val then 1 else 0) →
      d.regs 9 = usedAt base n_max mem (probeSlot (tableLog n_max) b k) →
      d.regs 10 = 1 →
      ∃ y : Data rLP,
        ExecWithin w probeLoop d y (12 * rem + 2) ∧
        y.mem = mem ∧ y.regs 0 = base ∧ y.regs 1 = u.val ∧ y.regs 2 = p.val ∧
        y.regs 4 = usedBase base n_max ∧ y.regs 5 = keyBase base n_max ∧
        y.regs 6 = valBase base n_max ∧ y.regs 9 = usedAt base n_max mem p ∧
        y.regs 10 = 1 ∧ y.regs 22 = d.regs 22 ∧ y.regs 23 = d.regs 23 := by
  intro b t p rem
  induction rem with
  | zero =>
    intro k d hkr hdmem hd0 hd1 hd2 _ hd4 hd5 hd6 hd7 hd9 hd10
    obtain rfl : k = t := by omega
    have hd7_0 : d.regs 7 = 0 :=
      hd7 ▸ ite_eq_right_iff.mpr fun h => absurd h (hinv.not_probeContinue_probeLen u b)
    have hc : ¬(Cond.eq (7 : Fin 24) 10).Holds d := by simp [Cond.Holds, hd7_0, hd10]
    exact ⟨d, (Exec.loop_exit hc).within, hdmem, hd0, hd1, hd2, hd4, hd5, hd6, hd9, hd10, rfl, rfl⟩
  | succ rem ih =>
    intro k d hkr hdmem hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd9 hd10
    have hcont := hinv.probeContinue_of_lt_probeLen u b (show k < t by omega)
    have hc : (Cond.eq (7 : Fin 24) 10).Holds d := by
      simp [Cond.Holds, hd7, hd10, hcont.1, hcont.2]
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    wram_call (probeBody_execWithin u (probeSlot (tableLog n_max) b k) (x := d)
      hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd10 hfit_space) with d'
      ⟨hd'mem, hd'0, hd'1, hd'2, hd'3, hd'4, hd'5, hd'6, hd'7, hd'9, hd'10, hd'22, hd'23⟩
    rw [probeSlot_add] at hd'2 hd'7 hd'9; rw [hdmem] at hd'7 hd'9
    wram_call (ih (k + 1) d' (by omega) (hd'mem.trans hdmem) hd'0 hd'1 hd'2 hd'3 hd'4 hd'5 hd'6
      hd'7 hd'9 hd'10) with y ⟨hm, h0, h1, h2, h4, h5, h6, h9, h10, h22, h23⟩
    exact ⟨by simp only [Nat.mul_add]; omega, hm, h0, h1, h2, h4, h5, h6, h9, h10,
      h22.trans hd'22, h23.trans hd'23⟩

/-- `probeLoop` halts deterministically at the stopping slot
`p = probeSlot (tableLog n_max) b (hinv.probeLen u b)` in at most
`12 * (hinv.probeLen u b) + 2` instructions. -/
theorem probeLoop_execWithin {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data rLP}
    (hinv : TableInv U V n_max base θ s x.mem)
    (u : Fin U)
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = (hashFn U n_max θ u).val)
    (h3 : x.regs 3 = tableSize n_max - 1)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h7 : x.regs 7 = (if usedAt base n_max x.mem (hashFn U n_max θ u) = 1 ∧
      keyAt base n_max x.mem (hashFn U n_max θ u) ≠ u.val then 1 else 0))
    (h9 : x.regs 9 = usedAt base n_max x.mem (hashFn U n_max θ u))
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max)) :
    let b := hashFn U n_max θ u
    let t := hinv.probeLen u b
    let p := probeSlot (tableLog n_max) b t
    ∃ y : Data rLP,
      ExecWithin w probeLoop x y (12 * t + 2) ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = p.val ∧
      y.regs 4 = usedBase base n_max ∧
      y.regs 5 = keyBase base n_max ∧
      y.regs 6 = valBase base n_max ∧
      y.regs 9 = usedAt base n_max x.mem p ∧
      y.regs 10 = 1 ∧
      y.regs 22 = x.regs 22 ∧
      y.regs 23 = x.regs 23 :=
  probeLoop_execWithin_aux hinv u hfit_space _ 0 x (Nat.zero_add _) rfl h0 h1
    (by rw [probeSlot_zero, h2]) h3 h4 h5 h6
    (by rw [probeSlot_zero, h7]) (by rw [probeSlot_zero, h9]) h10

/-- `insertFinishCode` executes in `7` deterministic steps, writing `(1, u.val, v)` at slot `p`
(`insertMem base n_max x.mem p u.val v`) and setting `reg 2` (`outReg`) to `0`. -/
theorem insertFinishCode_execWithin {U w base n_max : ℕ} (u : Fin U) (v : ℕ)
    (p : Fin (2 ^ tableLog n_max)) {x : Data rLP}
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (h2 : x.regs 2 = p.val)
    (h4 : x.regs 4 = usedBase base n_max)
    (h5 : x.regs 5 = keyBase base n_max)
    (h6 : x.regs 6 = valBase base n_max)
    (h10 : x.regs 10 = 1)
    (h23 : x.regs 23 = v)
    (hfit_space : Fits w (base + space n_max)) :
    ∃ y : Data rLP,
      ExecWithin w insertFinishCode x y 7 ∧
      y.mem = insertMem base n_max x.mem p u.val v ∧
      y.regs 0 = base ∧
      y.regs 2 = 0 := by
  have hp_lt : p.val < tableSize n_max := p.isLt
  unfold insertFinishCode
  wram_exec (disch := first | fits | layout_omega) [h1, h2, h4, h5, h6, h10, h23]
  exact ⟨rfl, by wram_simp [h0], by wram_simp⟩

/-- `queryFinishCode` executes in at most `4` deterministic steps, writing `val[p] + 1` into `reg 2`
when `s u = some (val[p])` (`used[p] = 1`) and `0` into `reg 2` when `s u = none` (`used[p] = 0`).
-/
theorem queryFinishCode_execWithin {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data rLP}
    (hinv : TableInv U V n_max base θ s x.mem)
    (u : Fin U)
    (h0 : x.regs 0 = base)
    (h2 : x.regs 2 = (probeSlot (tableLog n_max) (hashFn U n_max θ u)
      (hinv.probeLen u (hashFn U n_max θ u))).val)
    (h6 : x.regs 6 = valBase base n_max)
    (h9 : x.regs 9 = usedAt base n_max x.mem
      (probeSlot (tableLog n_max) (hashFn U n_max θ u)
        (hinv.probeLen u (hashFn U n_max θ u))))
    (h10 : x.regs 10 = 1)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    ∃ y : Data rLP,
      ExecWithin w queryFinishCode x y 4 ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      decodeOp (V := V) (n_max := n_max) (.query u) y.regs = some (s u) := by
  have hstop := hinv.probeStop_spec u
  dsimp only at hstop
  set p := probeSlot (tableLog n_max) (hashFn U n_max θ u) (hinv.probeLen u (hashFn U n_max θ u))
  have hp_lt : p.val < tableSize n_max := p.isLt
  have hval : x.mem (valBase base n_max + p.val) = valAt base n_max x.mem p := rfl
  unfold queryFinishCode
  rcases hstop with ⟨hp0, hnone⟩ | ⟨hp1, -, hsome⟩
  · wram_exec [h9, h10, hp0]
    exact ⟨rfl, by wram_simp [h0], by wram_simp [decodeOp, hnone]⟩
  · have hv_lt : valAt base n_max x.mem p < V := hinv.values_bounded u _ hsome
    wram_exec (disch := first | fits | layout_omega) [h2, h6, h9, h10, hp1, hval]
    exact ⟨rfl, by wram_simp [h0], by wram_simp [decodeOp, hsome]⟩

/-- The key queried or updated by dictionary operation `o`. -/
@[expose] def opKey {U : ℕ} : Dictionary.Op U → Fin U
  | .query u => u
  | .insert u _ => u

/-- `opCode n_max` executes any admissible operation `o` from `Rep U V n_max w base θ s x` and
`argMatchOp o x.regs` in at most
`KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * t + 27` deterministic instructions (where
`t = hrep.table_inv.probeLen (opKey o) (hashFn U n_max θ (opKey o))`), preserving `Rep` for
`((Dictionary.spec U V n_max).step s o).1`, decoding to
`some ((Dictionary.spec U V n_max).step s o).2`, and modifying only
`(Block.mk base (space n_max)).footprint`. -/
theorem opCode_execWithin {U V w base n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data rLP}
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V)
    (hrep : Rep U V n_max w base θ s x)
    (o : (Dictionary.spec U V n_max).Op)
    (hvalid : (Dictionary.spec U V n_max).valid s o)
    (harg : argMatchOp o x.regs) :
    let u := opKey o
    let b := hashFn U n_max θ u
    let t := hrep.table_inv.probeLen u b
    ∃ y : Data rLP,
      ExecWithin w (opCode n_max) x y
        (KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * t + 27) ∧
      decodeOp (V := V) (n_max := n_max) o y.regs =
        some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
      Rep U V n_max w base θ ((Dictionary.spec U V n_max).stepFn s o).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  set u := opKey o; set b := hashFn U n_max θ u
  set t := hrep.table_inv.probeLen u b; set p := probeSlot (tableLog n_max) b t
  have hx1_key : x.regs 1 = u.val := by cases o <;> exact harg.1
  refine WP.exists_execWithin (WP.bounded hrep.bounded ?_)
  unfold opCode
  wram_call (KWise.evalCode_execWithin u (x := x.comap kwiseMap) hrep.kwise_rep
    hrep.reg_base hx1_key hw (hfit_space.of_le (by wram_omega))) renamed injective_kwiseMap with
    x₁ ⟨⟨hx₁_0, hx₁_1, hx₁_2, hx₁_mem⟩, hx₁_frame⟩
  wram_call (probeSetupCode_execWithin u b (x := x₁) hx₁_0 hx₁_1 hx₁_2 hfit_space) with x₂
    ⟨hx₂_mem, hx₂_0, hx₂_1, hx₂_2, hx₂_3, hx₂_4, hx₂_5, hx₂_6, hx₂_7, hx₂_9, hx₂_10,
      hx₂_22, hx₂_23⟩
  have hmem₂ : x₂.mem = x.mem := by mem_frame
  have ht₂ : (hmem₂.symm ▸ hrep.table_inv).probeLen u (hashFn U n_max θ u) = t :=
    TableInv.probeLen_congr (hmem₂.symm ▸ hrep.table_inv) hrep.table_inv hmem₂ u b
  wram_call (probeLoop_execWithin (hinv := hmem₂.symm ▸ hrep.table_inv) u
    hx₂_0 hx₂_1 hx₂_2 hx₂_3 hx₂_4 hx₂_5 hx₂_6
    (by simpa only [hx₁_mem, hmem₂] using hx₂_7)
    (by simpa only [hx₁_mem, hmem₂] using hx₂_9) hx₂_10 hfit_space) with x₃
    ⟨hx₃_mem, hx₃_0, hx₃_1, hx₃_2, hx₃_4, hx₃_5, hx₃_6, hx₃_9, hx₃_10, hx₃_22, hx₃_23⟩
  have hmem₃ : x₃.mem = x.mem := by mem_frame
  have hx₃_22_eq : x₃.regs 22 = x.regs 22 := by regs_frame
  have hx₃_23_eq : x₃.regs 23 = x.regs 23 := by regs_frame
  have hx₃_2' : x₃.regs 2 = p.val := by rwa [ht₂] at hx₃_2
  have hx₃_9' : x₃.regs 9 = usedAt base n_max x.mem p := by rwa [ht₂, hmem₂] at hx₃_9
  cases o with
  | query u₀ =>
    have ht₃ : (hmem₃.symm ▸ hrep.table_inv).probeLen u (hashFn U n_max θ u) = t :=
      TableInv.probeLen_congr (hmem₃.symm ▸ hrep.table_inv) hrep.table_inv hmem₃ u b
    wram_exec [hx₃_22_eq, harg.2, hx₃_10]
    wram_call (queryFinishCode_execWithin (hinv := hmem₃.symm ▸ hrep.table_inv) u hx₃_0
      (by rw [ht₃]; exact hx₃_2') hx₃_6
      (by rw [ht₃, hmem₃]; exact hx₃_9')
      hx₃_10 hfit_space hfit_V) with y ⟨hymem, hy0, hdec⟩
    intro hbdd
    have hmx : y.mem = x.mem := by mem_frame
    refine ⟨?_, hdec, ⟨hbdd, hy0, hmx ▸ hrep.kwise_rep, hmx ▸ hrep.table_inv⟩,
      fun _ _ => hmx ▸ rfl⟩
    rw [TableInv.probeLen_congr (hmem₂.symm ▸ hrep.table_inv) hrep.table_inv hmem₂ u _]; omega
  | insert u₀ v =>
    wram_exec [hx₃_22_eq, harg.2.1, hx₃_10]
    wram_call (insertFinishCode_execWithin u v p hx₃_0 hx₃_1 hx₃_2'
      hx₃_4 hx₃_5 hx₃_6 hx₃_10 (hx₃_23_eq.trans harg.2.2) hfit_space) with
      y ⟨hymem, hy0, _⟩
    intro hbdd
    have hmx : y.mem = insertMem base n_max x.mem p u.val v := hymem.trans (by rw [hmem₃])
    refine ⟨?_, rfl,
      ⟨hbdd, hy0,
        kwise_rep_congr hrep.kwise_rep fun a ha _ => hmx ▸ insertMem_of_outside (.inl ha),
        hmx ▸ hrep.table_inv.insert_mem u₀ v hvalid⟩,
      Modifies.block_iff.mpr fun a ha =>
        hmx ▸ insertMem_of_outside (ha.imp (fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
          id)⟩
    rw [TableInv.probeLen_congr (hmem₂.symm ▸ hrep.table_inv) hrep.table_inv hmem₂ u _]; omega

/-! ## Section 4: `Randomized.StateTransitionImpl` certificate and expected-time sequence theorem -/

/-- **`StateTransitionImpl` certificate for open-addressed linear probing on the randomized Word
RAM**
over `Cslib.WordRAM.Basis.exact`:
- **Space**: `space n_max = KWise.space n_max 5 + 3 * 2 ^ (tableLog n_max) = O(n_max)` words;
- **Initialization time**: `setupTime U n_max = KWise.initTableSteps n_max U (tableLog n_max) + 38
  = O(n_max + log U)` expected instructions;
- **Operation charge**: `charge U n_max = KWise.evalSteps n_max U (tableLog n_max) 5 + 3483
  = O(L ^ 2 + 1)` expected instructions per `query` or `insert`, which is `O(1)` whenever
  `U ≤ n_max ^ c` for any constant `c`;
- **Potential**: `0` (`seedSlack := 1`). -/
@[expose] noncomputable def impl (U V n_max w base : ℕ)
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl (subroutineCode U n_max)
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl.ofFn
    (Seed := Seed U n_max)
    (seedLaw := seedLaw U n_max)
    (seedSlack := 1)
    (space := space n_max)
    (spanTime := 3)
    (setupTime := setupTime U n_max)
    (initPotential := 0)
    (charge := fun _ _ => charge U n_max)
    (rep := fun θ s x => Rep U V n_max w base θ s x)
    (potential := fun _ _ => 0)
    (encode := encodeOp)
    (argMatch := argMatchOp)
    (decode := decodeOp)
    (bounded := fun h => h.bounded)
    (arguments_fit := fun {s} o hvalid i hi => by
      cases o with
      | query u =>
        dsimp only [encodeOp]; split_ifs
        · exact (fits_U_of_hw hw).of_le u.isLt.le
        · exact fits_zero w
      | insert u v =>
        dsimp only [encodeOp]; split_ifs
        · exact (fits_U_of_hw hw).of_le u.isLt.le
        · exact hfit_space.of_le (by have := tableSize_pos n_max; wram_omega)
        · exact hfit_V.of_le hvalid.2.le
        · exact fits_zero w)
    (encode_matches := fun o _ => by
      cases o with
      | query _ => exact ⟨rfl, rfl⟩
      | insert _ _ => exact ⟨rfl, rfl, rfl⟩)
    (rep_supported := fun hregs hmem hbdd hrep => hrep.supported hregs hmem hbdd)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by dsimp only [subroutineCode]; decide)
    (params_not_clear := fun j => j.elim0)
    (incCur_eval := fun {x} h20 hfit => by
      dsimp only [subroutineCode] at h20 hfit ⊢
      simp [Op.exactBin, Op.eval, StandardOp.evalExact, Data.put, h20, hfit])
    (span_exec := fun _ hfr _ => by
      obtain ⟨x₁, hex, hmem, hb, hfr'⟩ := allocSpan_execWithin hfr hfit_space
      exact ⟨x₁, hex, hmem, hb, hfr', fun j => j.elim0⟩)
    (setup_exec := fun hx₁ hb hfr _ hz => initSetup_exec hw hfit_space hx₁ hb hfr hz)
    (step_exec := fun {s} o ν hvalid hseed hsupp => by
      classical
      let u := opKey o
      let y (p : Seed U n_max × Data rLP) : Data rLP :=
        if hp : p ∈ ν.support then
          Classical.choose (opCode_execWithin hw hfit_space hfit_V (hsupp p hp).1 o hvalid
            (hsupp p hp).2)
        else p.2
      let T_probe (p : Seed U n_max × Data rLP) : ℕ :=
        if hp : p ∈ ν.support then (hsupp p hp).1.table_inv.probeLen u (hashFn U n_max p.1 u)
        else 0
      refine ⟨fun p => PMF.pure (p.1, y p),
        fun p => (KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * T_probe p + 27 : ℕ),
        ?_, fun θ' => by
          have : (ν.bind fun p => PMF.pure (p.1, y p)).map Prod.fst = ν.map Prod.fst := by
            rw [PMF.map_bind]; simp only [PMF.pure_map]; rfl
          rw [this]; exact hseed θ', ?_⟩
      · intro p hp
        obtain ⟨hex, hdec, hrep', hmod⟩ := Classical.choose_spec
          (opCode_execWithin hw hfit_space hfit_V (hsupp p hp).1 o hvalid (hsupp p hp).2)
        have hy : y p = Classical.choose
            (opCode_execWithin hw hfit_space hfit_V (hsupp p hp).1 o hvalid (hsupp p hp).2) := by
          simp only [y, hp, ↓reduceDIte]
        have hT : T_probe p = (hsupp p hp).1.table_inv.probeLen u (hashFn U n_max p.1 u) := by
          simp only [T_probe, hp, ↓reduceDIte]
        refine ⟨(ExecCodeDist.of_execWithin hex).congr_dist (by simp [hy])
          (by dsimp only; rw [hT]), fun q hq => ?_⟩
        obtain rfl : q = (p.1, y p) := by simpa using hq
        exact ⟨by simpa only [hy] using hdec, by simpa only [hy] using hrep',
          by simpa only [hy] using hmod⟩
      · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
        have hprobe : (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ 288 :=
          tsum_probeLen_le (V := V) (base := base) (s := s) u ν
            (fun θ => by simpa only [one_mul] using hseed θ) T_probe
            fun p hp => ⟨p.2.mem, (hsupp p hp).1.table_inv,
              by simp only [T_probe, hp, ↓reduceDIte, le_rfl]⟩
        have hterm (p : Seed U n_max × Data rLP) :
            ν p * ((KWise.evalSteps n_max U (tableLog n_max) 5 + 12 * T_probe p + 27 : ℕ) :
              ℝ≥0∞) =
              ν p * (KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞) +
                12 * (ν p * (T_probe p : ℝ≥0∞)) := by push_cast; ring
        simp_rw [hterm]
        rw [tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ν.tsum_coe, one_mul]
        calc (KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞) +
              12 * ∑' p, ν p * (T_probe p : ℝ≥0∞)
            ≤ (KWise.evalSteps n_max U (tableLog n_max) 5 + 27 : ℝ≥0∞) + 12 * 288 := by gcongr
          _ = (charge U n_max : ℝ≥0∞) := by dsimp only [charge]; push_cast; ring)

/-- Standard-basis (`Basis.standard`) `StateTransitionImpl` certificate for linear probing,
transported
from `impl` via `Randomized.StateTransitionImpl.toStandard`. -/
noncomputable def implStandard (U V n_max w base : ℕ)
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl
      (subroutineCode U n_max).toStandard
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (impl U V n_max w base hw hfit_space hfit_V).toStandard

/-- **Expected amortized multi-operation theorem for linear probing**: for any admissible sequence
`ops : List (Dictionary.Op U)` starting from the empty dictionary on fresh zeroed memory and fixed
independently of the sampled hash seed (oblivious adversary), `initFresh` followed by the
subroutine operation bodies (`StateTransitionImpl.ExecSteps`) executes with total expected
instruction
count at most `3 + setupTime U n_max + ops.length * charge U n_max` (excluding caller argument
delivery, caller dispatch loops, and host-level code specialization). -/
theorem seq_expected_amortized (U V n_max w base : ℕ)
    (hw : 2 * trinomialDeg U (tableLog n_max) ≤ w)
    (hfit_space : Fits w (base + space n_max))
    (hfit_V : Fits w V)
    {x₀ : Data rLP}
    (hx₀ : x₀.Bounded w)
    (hfr : x₀.regs 18 = base)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₀.mem a = 0)
    (ops : List (Dictionary.Op U))
    (hvalid : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ∃ (ν₀ ν_f : PMF (Seed U n_max × Data rLP))
      (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U n_max).initFresh x₀
        (ν₀.map Prod.snd) (3 + setupTime U n_max : ℕ) ∧
      (impl U V n_max w base hw hfit_space hfit_V).ExecStepsOfFn
        (Dictionary.empty U) ops ν₀ ν_f T_ops ∧
      (3 + setupTime U n_max : ℕ) + T_ops ≤
        (3 + setupTime U n_max + ops.length * charge U n_max : ℕ) := by
  obtain ⟨ν₀, ν_f, T_ops, hinit, hsteps, _, _, hbound⟩ :=
    (impl U V n_max w base hw hfit_space hfit_V).seq_expected_amortized_ofFn ops hx₀ hfr
      (fun j => j.elim0) hz hvalid
  have htotal :=
    (Dictionary.spec U V n_max).totalCost_const (charge U n_max) (Dictionary.empty U) ops
  refine ⟨ν₀, ν_f, T_ops, ?_, hsteps, ?_⟩
  · dsimp only [StateTransitionImpl.initTime, impl, StateTransitionImpl.ofFn] at hinit
    exact_mod_cast hinit
  · dsimp only [StateTransitionImpl.initTime, impl, StateTransitionImpl.ofFn] at hbound
    rw [htotal] at hbound
    simpa only [Nat.cast_zero, mul_zero, tsum_zero, add_zero, ← Nat.cast_add] using hbound

end Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
