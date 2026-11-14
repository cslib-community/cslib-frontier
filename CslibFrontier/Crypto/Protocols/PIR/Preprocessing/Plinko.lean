/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Invertible
public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Basic
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

/-!
# The Plinko client-preprocessing single-server PIR scheme

This module formalizes the core of the Plinko updateable client-preprocessing single-server PIR
scheme of [Hoover, Patel, Persiano and Yeo][HooverPatelPersianoYeo2025] (Section 5 and Appendix A,
Figure 7).

A database `db : Fin c × Fin w → Bool` of `n = c * w` bits is partitioned into `c` blocks of size
`w`. The client maintains `nReg` regular hint slots and `nBackup` backup/promoted hint slots,
indexed by `Fin (nReg + nBackup)`, together with one invertible PRF key `keys α : Key` per block
`α : Fin c` for an iPRF `iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)`.

* **Hint lookup via iPRF inversion** (`getHint`, `getHintScan`, `getHint_eq_getHintScan`):
  to find an active hint containing `x = (α, β)`, `getHint` inverts `iF` at `(keys α, β)` to obtain
  the candidate slot set `iF.inv (keys α) β` and selects the first matching active slot.
  When `iF.IsCorrectKey (keys α)` holds, `getHint` returns the exact same hint as a full linear scan
  `getHintScan` over all `nReg + nBackup` slots.
* **Offline single-pass entry streaming** (`initPlinkoState`, `streamEntry`, `streamPreprocess`,
  `foldr_streamEntry_univ`, `PlinkoState.valid_streamPreprocess`): streaming each database entry
  `x = (α, β)` once and updating only the slots in `iF.inv (keys α) β` establishes the parity and
  cache validity invariant `PlinkoState.Valid`.
* **Online query, answer, reconstruction, and backup promotion** (`buildQuery`, `plinkoAnswer`,
  `plinkoReconstruct`, `plinkoScheme`, `PlinkoState.eval_step_plinkoScheme`,
  `PlinkoState.isCorrectFrom_plinkoScheme`): on an uncached query `x = (α, β)`, the client removes
  `α` from the matched `(c / 2 + 1)`-block set `P` to obtain `P' = P.erase α`, randomly sends either
  `P'` or `Finset.univ \ P'` according to a fair coin `b : Bool`, replaces `α`'s offset with a
  random offset `r : Fin w`, reconstructs `db x = p + r_b`, consumes the matched hint, promotes the
  next backup hint `T[j']` into `H[j']`, and caches `(db x, j')` in `cache x`. Under `Valid` and
  `CanAnswerSeq`, `plinkoScheme` satisfies `Scheme.IsCorrectFrom` and preserves `Valid` across both
  the promotion and cache paths.
* **Single-query and hybrid multi-query privacy** (`eval_buildQuery_conditioned_eq_plinkoSim`,
  `plinkoHybridScheme`, `isCorrect_plinkoHybridScheme`,
  `isPerfectlyPrivateWith_plinkoHybridScheme`, `eval_snd_plinkoScheme_query_of_getHint`):
  when `Even c`, a regular hint conditioned on containing `x = (α, β)` produces a query message
  whose distribution equals `plinkoSim c w` (a uniform `(c / 2)`-subset of blocks paired with
  independent uniform offsets), independent of `x`. In the idealized random-hint hybrid
  `plinkoHybridScheme` (a proof device that stores `db` to compute exact parities and samples a
  fresh conditioned regular hint at each query), this yields unconditional correctness
  `Scheme.IsCorrect` and multi-query adaptive perfect privacy `Scheme.IsPerfectlyPrivateWith`.
* **Database and hint updates** (`updateDB`, `updateHint`, `updateState`,
  `PlinkoState.valid_updateHint_delta`, `PlinkoState.valid_updateHint`,
  `PlinkoState.valid_updateState`, `PlinkoState.canAnswer_updateHint_iff`):
  updating entry `i = (α, β)` to `d` via summary `δ = (i, db i + d)` touches only the candidate
  slots in `iF.inv (keys α) β` and the cache entry `cache i`, preserving `PlinkoState.Valid`
  against `Function.update db i d` as well as `PlinkoState.CanAnswer`.

## Main definitions

* `blockParity`, `PlinkoQuery`, `buildQuery`, `plinkoAnswer`, `plinkoReconstruct`:
  block-offset parities, online query construction, server answer, and client reconstruction.
* `ActiveHint`, `BackupHint`, `PlinkoState`, `getHint`, `getHintScan`:
  client hint state and hint lookup via iPRF inversion (`iF.inv`) vs. linear scan.
* `initPlinkoState`, `streamEntry`, `streamUpTo`, `streamPreprocess`:
  offline single-pass entry streaming (`HintInit`).
* `refreshPlinkoState`, `PlinkoState.Valid`, `PlinkoState.CanAnswer`, `PlinkoState.CanAnswerSeq`,
  `PlinkoState.nextState`: online backup promotion, state validity invariant, and answerability.
* `plinkoSim`, `plinkoScheme`, `plinkoHybridScheme`: simulator, full Plinko `Scheme`, and idealized
  random-hint hybrid `Scheme`.
* `updateDB`, `updateHint`, `applyUpdates`, `updateState`: database and hint update algorithms
  (Definition 5.2 and Figure 7).

## Main results

* `plinkoReconstruct_plinkoAnswer_eq`: online reconstruction identity.
* `getHint_eq_getHintScan`: equivalence of `getHint` via `iF.inv` and `getHintScan`.
* `foldr_streamEntry_univ`, `PlinkoState.valid_streamPreprocess`: offline streaming correctness.
* `PlinkoState.valid_nextState`, `PlinkoState.eval_step_plinkoScheme`,
  `PlinkoState.isCorrectFrom_plinkoScheme`: online state-validity preservation and conditional
  multi-query correctness of `plinkoScheme`.
* `queryBlocksEquiv`, `queryOffsetsEquiv`, `eval_buildQuery_conditioned_eq_plinkoSim`,
  `eval_snd_plinkoScheme_query_of_getHint`: single-query exact privacy and bridge lemma.
* `isCorrect_plinkoHybridScheme`, `isPerfectlyPrivateWith_plinkoHybridScheme`,
  `privacyAdvantage_plinkoHybridScheme_eq_zero`, `eval_queryTranscript_plinkoHybridScheme`:
  unconditional correctness and multi-query adaptive perfect privacy of `plinkoHybridScheme`.
* `PlinkoState.valid_updateHint_delta`, `PlinkoState.valid_updateHint`,
  `PlinkoState.valid_updateState`, `PlinkoState.canAnswer_updateHint_iff`: hint update correctness.

## What is not proved

* Exact multi-query perfect privacy is proved for the idealized random-hint proof device
  `plinkoHybridScheme`, not for the full `plinkoScheme` (where `getHint` takes the first candidate
  slot, conditioning earlier slots, and the paper argues computational privacy via Ren, Mughees,
  and Sun (2024) and iPRF
  security).
* The Chernoff load bound on `|iF.inv (keys α) β|` (Section 5.2, p. 22), the failure-probability
  bound for `CanAnswerSeq`, amortized re-streaming after `nBackup` queries, the Appendix B
  Plinko–Piano variant (Figure 8), `B`-bit entries, the FHE offline phase, and the asymptotic
  runtime/storage bounds of Theorem 5.3 are not formalized.

## References

* [A. Hoover, S. Patel, G. Persiano, K. Yeo, *Plinko: Single-Server PIR with Efficient Updates via
  Invertible PRFs*][HooverPatelPersianoYeo2025], Section 5 (Definitions 5.1–5.2, Figure 5, and
  Theorem 5.3) and Appendix A (Figure 7; locators follow IACR ePrint 2024/318).
-/

public section

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko

open Probability
open Cslib.Crypto.PRF
open scoped ENNReal NNReal

variable {c w nReg nBackup : ℕ} {Key : Type}

/-! ### Block-offset parities, queries, server answers, and reconstruction -/

/-- The parity `⊕_{a ∈ P} db (a, o a)` of database `db : Fin c × Fin w → Bool` over a subset of
blocks `P : Finset (Fin c)` at offsets `o : Fin c → Fin w`, using `BooleanRing Bool` addition
(XOR). -/
@[expose] def blockParity (db : Fin c × Fin w → Bool) (P : Finset (Fin c))
    (o : Fin c → Fin w) : Bool :=
  ∑ a ∈ P, db (a, o a)

theorem blockParity_erase_add (db : Fin c × Fin w → Bool) {P : Finset (Fin c)} {α : Fin c}
    (hα : α ∈ P) (o : Fin c → Fin w) :
    db (α, o α) + blockParity db (P.erase α) o = blockParity db P o :=
  Finset.add_sum_erase P (fun a => db (a, o a)) hα

theorem blockParity_insert_of_notMem (db : Fin c × Fin w → Bool) {P : Finset (Fin c)} {α : Fin c}
    (hα : α ∉ P) (o : Fin c → Fin w) :
    blockParity db (insert α P) o = db (α, o α) + blockParity db P o :=
  Finset.sum_insert hα

theorem blockParity_update_of_notMem (db : Fin c × Fin w → Bool) {P : Finset (Fin c)} {α : Fin c}
    (hα : α ∉ P) (o : Fin c → Fin w) (β : Fin w) :
    blockParity db P (Function.update o α β) = blockParity db P o := by
  apply Finset.sum_congr rfl
  intro a ha
  have hne : a ≠ α := fun h => hα (h ▸ ha)
  simp [hne]

/-- A Plinko online query message `(P', o)` sent to the server
([Hoover, Patel, Persiano and Yeo, Figure 7, `Query` and `Answer`][HooverPatelPersianoYeo2025]),
consisting of a block subset `blocks : Finset (Fin c)` and one offset per block
`offsets : Fin c → Fin w`. -/
@[ext]
structure PlinkoQuery (c w : ℕ) where
  /-- Subset of blocks `P'` selected by the query. -/
  blocks : Finset (Fin c)
  /-- Offset in `Fin w` for each block `a : Fin c`. -/
  offsets : Fin c → Fin w
  deriving DecidableEq

/-- Equivalence between `PlinkoQuery c w` and `Finset (Fin c) × (Fin c → Fin w)`. -/
@[expose] def plinkoQueryEquiv (c w : ℕ) : PlinkoQuery c w ≃ Finset (Fin c) × (Fin c → Fin w) where
  toFun q := (q.blocks, q.offsets)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance (c w : ℕ) : Fintype (PlinkoQuery c w) :=
  Fintype.ofEquiv (Finset (Fin c) × (Fin c → Fin w)) (plinkoQueryEquiv c w).symm

instance (c w : ℕ) [NeZero w] : Nonempty (PlinkoQuery c w) :=
  ⟨⟨∅, fun _ => 0⟩⟩

/-- Constructs the Plinko query message from a matched hint `(P, o)` for target `x = (α, β)`,
coin `b : Bool`, and replacement offset `r : Fin w`
([Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7, `Query`][HooverPatelPersianoYeo2025]):
removes `x.1` from `P` to form `P' = P.erase x.1`, complements `P'` when `b = true`, and replaces
the offset in block `x.1` with `r`. -/
@[expose] def buildQuery (x : Fin c × Fin w) (P : Finset (Fin c)) (o : Fin c → Fin w) (b : Bool)
    (r : Fin w) : PlinkoQuery c w := by
  let P' := P.erase x.1
  exact ⟨if b then Finset.univ \ P' else P', Function.update o x.1 r⟩

/-- Deterministic server answer algorithm `(r₀, r₁)`
([Hoover, Patel, Persiano and Yeo, Figure 7, `Answer`][HooverPatelPersianoYeo2025]): `r₀` is the
parity of database entries in `q.blocks`, and `r₁` is the parity of database entries in
`Finset.univ \ q.blocks`. -/
@[expose] def plinkoAnswer (db : Fin c × Fin w → Bool) (q : PlinkoQuery c w) : Bool × Bool :=
  (blockParity db q.blocks q.offsets, blockParity db (Finset.univ \ q.blocks) q.offsets)

/-- Client bit reconstruction `a = p ⊕ r_b`
([Hoover, Patel, Persiano and Yeo, Figure 7, `Recon`][HooverPatelPersianoYeo2025]). -/
@[expose] def plinkoReconstruct (p b : Bool) (ans : Bool × Bool) : Bool :=
  p + (if b then ans.2 else ans.1)

private theorem sdiff_univ_sdiff (s : Finset (Fin c)) :
    Finset.univ \ (Finset.univ \ s) = s := by
  ext a
  simp

private theorem bool_add_add_cancel (a b : Bool) : (a + b) + b = a := by
  revert a b
  decide

/-- Selecting component `r_b` from `plinkoAnswer db (buildQuery x P o b r)` always recovers the
punctured parity `blockParity db (P.erase x.1) o`, regardless of the coin `b` and replacement
offset `r`. -/
theorem plinkoAnswer_buildQuery_select (db : Fin c × Fin w → Bool) (x : Fin c × Fin w)
    (P : Finset (Fin c)) (o : Fin c → Fin w) (b : Bool) (r : Fin w) :
    (if b then (plinkoAnswer db (buildQuery x P o b r)).2
     else (plinkoAnswer db (buildQuery x P o b r)).1) =
      blockParity db (P.erase x.1) o := by
  cases b <;>
    simp [plinkoAnswer, buildQuery,
      blockParity_update_of_notMem db (Finset.notMem_erase x.1 P)]

/-- **Online reconstruction identity**
([Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7, `Recon`][HooverPatelPersianoYeo2025]):
if `(P, o)` contains `x` (`x.1 ∈ P` and `o x.1 = x.2`), then XORing the hint parity
`blockParity db P o` with the `b`-th server parity from `plinkoAnswer db (buildQuery x P o b r)`
recovers `db x`. -/
theorem plinkoReconstruct_plinkoAnswer_eq (db : Fin c × Fin w → Bool) (x : Fin c × Fin w)
    (P : Finset (Fin c)) (o : Fin c → Fin w) (b : Bool) (r : Fin w)
    (hP : x.1 ∈ P) (ho : o x.1 = x.2) :
    plinkoReconstruct (blockParity db P o) b (plinkoAnswer db (buildQuery x P o b r)) = db x := by
  rw [plinkoReconstruct, plinkoAnswer_buildQuery_select, ← blockParity_erase_add db hP o, ho,
    Prod.mk.eta, bool_add_add_cancel]

/-! ### Hint state, `getHint` via `iF.inv` vs. linear scan, and single-pass entry streaming -/

/-- An active hint entry in table `H` of
[Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]: either an initial regular
hint `(P, p)` or a promoted backup hint `(P, x, p)` whose effective block set is `insert x.1 P`
with `x.1 ∉ P`. -/
inductive ActiveHint (c w : ℕ) where
  /-- Unconsumed regular hint with block subset `blocks` and parity `parity`. -/
  | regular (blocks : Finset (Fin c)) (parity : Bool)
  /-- Unconsumed promoted backup hint with base block subset `blocks` (`entry.1 ∉ blocks`),
  promoted index `entry`, and parity `parity`. -/
  | promoted (blocks : Finset (Fin c)) (entry : Fin c × Fin w) (parity : Bool)
  deriving DecidableEq

/-- An unconsumed backup hint `(B, p₁, p₂)` in table `T` of
[Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]. -/
@[ext]
structure BackupHint (c : ℕ) where
  /-- Block subset `B` of size `c / 2`. -/
  blocks : Finset (Fin c)
  /-- Parity `p₁` of database entries in blocks `a ∈ B`. -/
  parityIn : Bool
  /-- Parity `p₂` of database entries in blocks `a ∈ Finset.univ \ B`. -/
  parityOut : Bool
  deriving DecidableEq

/-- Persistent client state `(K, H, T, Q)` of Plinko
([Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]). -/
@[ext]
structure PlinkoState (c w nReg nBackup : ℕ) (Key : Type) where
  /-- Per-block iPRF keys `K[α]`. -/
  keys : Fin c → Key
  /-- Active regular and promoted hint table `H`, indexed by `Fin (nReg + nBackup)`. -/
  H : Fin (nReg + nBackup) → Option (ActiveHint c w)
  /-- Unconsumed backup hint table `T`, indexed by `Fin (nReg + nBackup)`. -/
  T : Fin (nReg + nBackup) → Option (BackupHint c)
  /-- Query cache `Q`, mapping each previously queried index `x` to `(db x, promotedSlot)`. -/
  cache : Fin c × Fin w → Option (Bool × Fin (nReg + nBackup))

/-- Checks whether an active hint `h : ActiveHint c w` at slot `j` contains block `x.1` (compatible
with offset `x.2` at `x.1` when `iF.eval (keys x.1) j = x.2`) and returns its effective block set,
parity, and offset vector
([Hoover, Patel, Persiano and Yeo, Figure 7, `GetHint`][HooverPatelPersianoYeo2025]). -/
@[expose] def extractActiveHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (keys : Fin c → Key) (j : Fin (nReg + nBackup)) (h : ActiveHint c w) (x : Fin c × Fin w) :
    Option (Finset (Fin c) × Bool × (Fin c → Fin w)) :=
  let o : Fin c → Fin w := fun a => iF.eval (keys a) j
  match h with
  | .regular P p =>
    if x.1 ∈ P then some (P, p, o) else none
  | .promoted P y p =>
    if (x.1 = y.1 ∧ x.2 = y.2) ∨ (x.1 ≠ y.1 ∧ x.1 ∈ P) then
      some (insert y.1 P, p, Function.update o y.1 y.2)
    else none

/-- Boolean predicate testing whether slot `j` in `st.H` has an active hint matching `x` under
`extractActiveHint`. -/
@[expose] def slotMatchesBlock (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (j : Fin (nReg + nBackup)) : Bool :=
  match st.H j with
  | some h => (extractActiveHint iF st.keys j h x).isSome
  | none => false

/-- Finds the first matching candidate slot in `iF.inv (st.keys x.1) x.2`
([Hoover, Patel, Persiano and Yeo, Figure 7, `GetHint`][HooverPatelPersianoYeo2025]). -/
@[expose] def findHintSlot (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    Option (Fin (nReg + nBackup)) :=
  ((iF.inv (st.keys x.1) x.2).sort (· ≤ ·)).find? (slotMatchesBlock iF st x)

/-- Full linear scan over all `nReg + nBackup` hint slots finding the first slot `j` where
`iF.eval (st.keys x.1) j = x.2` and `slotMatchesBlock iF st x j` holds. -/
@[expose] def findHintSlotScan (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    Option (Fin (nReg + nBackup)) :=
  (List.finRange (nReg + nBackup)).find?
    (fun j => decide (iF.eval (st.keys x.1) j = x.2) && slotMatchesBlock iF st x j)

/-- `GetHint` via `iF.inv`
([Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]): finds the first
candidate slot `j ∈ iF.inv (st.keys x.1) x.2` with a matching active hint and returns
`(j, P_eff, p, o)`. -/
@[expose] def getHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    Option (Fin (nReg + nBackup) × Finset (Fin c) × Bool × (Fin c → Fin w)) :=
  match findHintSlot iF st x with
  | some j =>
    match st.H j with
    | some h => (extractActiveHint iF st.keys j h x).map (fun t => (j, t))
    | none => none
  | none => none

/-- Linear-scan counterpart of `getHint` scanning all `nReg + nBackup` slots via forward
evaluations `iF.eval`. -/
@[expose] def getHintScan (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    Option (Fin (nReg + nBackup) × Finset (Fin c) × Bool × (Fin c → Fin w)) :=
  match findHintSlotScan iF st x with
  | some j =>
    match st.H j with
    | some h => (extractActiveHint iF st.keys j h x).map (fun t => (j, t))
    | none => none
  | none => none

private theorem sort_eq_filter_finRange {N : ℕ} (s : Finset (Fin N)) :
    s.sort (· ≤ ·) = (List.finRange N).filter (· ∈ s) := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ (hab : a ≤ b) (hba : b ≤ a) => le_antisymm hab hba)
  · exact Finset.pairwise_sort s (· ≤ ·)
  · exact ((List.pairwise_lt_finRange N).imp le_of_lt).filter _
  · refine (List.perm_ext_iff_of_nodup (s.sort_nodup _) ((List.nodup_finRange N).filter _)).mpr ?_
    intro j
    simp [Finset.mem_sort, List.mem_filter, List.mem_finRange]

/-- **Algorithmic equivalence of `getHint` and linear scan**
([Hoover, Patel, Persiano and Yeo, Section 5.2, p. 21][HooverPatelPersianoYeo2025]): when
`iF.IsCorrectKey (st.keys x.1)` holds, `findHintSlot` via `iF.inv` returns the exact same slot as
the full linear scan `findHintSlotScan` over `Fin (nReg + nBackup)`. -/
theorem findHintSlot_eq_findHintSlotScan
    {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (hcorr : iF.IsCorrectKey (st.keys x.1)) :
    findHintSlot iF st x = findHintSlotScan iF st x := by
  rw [findHintSlot, findHintSlotScan, sort_eq_filter_finRange, List.find?_filter]
  congr 1
  funext j
  simp [hcorr j x.2]

/-- When `iF.IsCorrectKey (st.keys x.1)` holds, `getHint` via `iF.inv` returns the exact same
hint tuple as `getHintScan`. -/
theorem getHint_eq_getHintScan
    {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (hcorr : iF.IsCorrectKey (st.keys x.1)) :
    getHint iF st x = getHintScan iF st x := by
  rw [getHint, getHintScan, findHintSlot_eq_findHintSlotScan st x hcorr]

/-- Initializes `PlinkoState` prior to streaming the database, with regular hints in slots
`j < nReg`, backup hints in slots `j ≥ nReg`, all parities set to `false`, and an empty cache
([Hoover, Patel, Persiano and Yeo, Figure 7, `HintInit`][HooverPatelPersianoYeo2025]). -/
@[expose] def initPlinkoState (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    PlinkoState c w nReg nBackup Key where
  keys := keys
  H := fun j => if j.val < nReg then some (.regular (regBlocks j) false) else none
  T := fun j => if j.val < nReg then none else some ⟨backupBlocks j, false, false⟩
  cache := fun _ => none

/-- Streams a single database entry `x = (α, β)` with bit `d = db x`, updating only the candidate
slots `j ∈ iF.inv (st.keys x.1) x.2`
([Hoover, Patel, Persiano and Yeo, Figure 7, `HintInit`][HooverPatelPersianoYeo2025]). -/
@[expose] def streamEntry (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (x : Fin c × Fin w) (d : Bool) (st : PlinkoState c w nReg nBackup Key) :
    PlinkoState c w nReg nBackup Key := by
  let cand := iF.inv (st.keys x.1) x.2
  exact
    { keys := st.keys
      H := fun j =>
        if j ∈ cand then
          match st.H j with
          | some (.regular P p) =>
            if x.1 ∈ P then some (.regular P (d + p)) else some (.regular P p)
          | other => other
        else st.H j
      T := fun j =>
        if j ∈ cand then
          match st.T j with
          | some ⟨B, p₁, p₂⟩ =>
            if x.1 ∈ B then some ⟨B, d + p₁, p₂⟩ else some ⟨B, p₁, d + p₂⟩
          | none => none
        else st.T j
      cache := st.cache }

/-- The `PlinkoState` after streaming a subset of database entries `s : Finset (Fin c × Fin w)`. -/
@[expose] def streamUpTo (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (s : Finset (Fin c × Fin w)) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    PlinkoState c w nReg nBackup Key where
  keys := keys
  H := fun j =>
    if j.val < nReg then
      some (.regular (regBlocks j)
        (∑ a ∈ regBlocks j, if (a, iF.eval (keys a) j) ∈ s then db (a, iF.eval (keys a) j)
          else false))
    else none
  T := fun j =>
    if j.val < nReg then none
    else
      some ⟨backupBlocks j,
        ∑ a ∈ backupBlocks j, if (a, iF.eval (keys a) j) ∈ s then db (a, iF.eval (keys a) j)
          else false,
        ∑ a ∈ Finset.univ \ backupBlocks j,
          if (a, iF.eval (keys a) j) ∈ s then db (a, iF.eval (keys a) j) else false⟩
  cache := fun _ => none

/-- Offline preprocessing result (`HintInit`) after streaming all entries `Finset.univ` of `db`. -/
@[expose] def streamPreprocess (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    PlinkoState c w nReg nBackup Key where
  keys := keys
  H := fun j =>
    if j.val < nReg then
      some (.regular (regBlocks j) (blockParity db (regBlocks j) (fun a => iF.eval (keys a) j)))
    else none
  T := fun j =>
    if j.val < nReg then none
    else
      some ⟨backupBlocks j,
        blockParity db (backupBlocks j) (fun a => iF.eval (keys a) j),
        blockParity db (Finset.univ \ backupBlocks j) (fun a => iF.eval (keys a) j)⟩
  cache := fun _ => none

private theorem bool_mul_false (b : Bool) : b * false = false := by
  cases b <;> rfl

private theorem bool_false_add (b : Bool) : false + b = b := by
  cases b <;> rfl

private theorem bool_add_false (b : Bool) : b + false = b := by
  cases b <;> rfl

private theorem bool_zero_eq_false : (0 : Bool) = false := rfl

@[simp]
theorem streamUpTo_empty (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    streamUpTo iF db ∅ keys regBlocks backupBlocks =
      initPlinkoState keys regBlocks backupBlocks := by
  ext <;> simp [streamUpTo, initPlinkoState, bool_mul_false]

theorem streamUpTo_univ (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    streamUpTo iF db Finset.univ keys regBlocks backupBlocks =
      streamPreprocess iF db keys regBlocks backupBlocks := by
  ext <;> simp [streamUpTo, streamPreprocess, blockParity]

private theorem sum_ite_mem_insert (db : Fin c × Fin w → Bool)
    (o : Fin c → Fin w) (P : Finset (Fin c)) {s : Finset (Fin c × Fin w)} {x : Fin c × Fin w}
    (hx : x ∉ s) :
    (∑ a ∈ P, if (a, o a) ∈ insert x s then db (a, o a) else false) =
      (if o x.1 = x.2 ∧ x.1 ∈ P then db x else false) +
        ∑ a ∈ P, if (a, o a) ∈ s then db (a, o a) else false := by
  have hpoint : ∀ a ∈ P,
      (if (a, o a) ∈ insert x s then db (a, o a) else false) =
        (if a = x.1 ∧ o x.1 = x.2 then db x else false) +
          (if (a, o a) ∈ s then db (a, o a) else false) := by
    intro a _
    by_cases hax : (a, o a) = x
    · have ha1 : a = x.1 := congrArg Prod.fst hax
      have ha2 : o x.1 = x.2 := ha1 ▸ congrArg Prod.snd hax
      rw [hax]
      simp [ha1, ha2, hx, bool_add_false]
    · have hne : ¬(a = x.1 ∧ o x.1 = x.2) := fun ⟨h1, h2⟩ => hax (Prod.ext h1 (h1 ▸ h2))
      simp [Finset.mem_insert, hax, hne, bool_false_add]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  congr 1
  by_cases ho : o x.1 = x.2
  · by_cases hP : x.1 ∈ P
    · rw [Finset.sum_eq_single x.1]
      · simp [ho, hP]
      · intro a _ hne; simp [hne, bool_zero_eq_false]
      · intro habs; exact absurd hP habs
    · rw [Finset.sum_eq_zero]
      · simp [hP, bool_zero_eq_false]
      · intro a ha
        have hne : a ≠ x.1 := fun h => hP (h ▸ ha)
        simp [hne, bool_zero_eq_false]
  · rw [Finset.sum_eq_zero]
    · simp [ho, bool_zero_eq_false]
    · intro a _; simp [ho, bool_zero_eq_false]

/-- Streaming a fresh entry `x ∉ s` via `streamEntry` transitions `streamUpTo iF db s` to
`streamUpTo iF db (insert x s)` whenever `iF.IsCorrectKey (keys x.1)` holds. -/
theorem streamEntry_streamUpTo {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (db : Fin c × Fin w → Bool) {s : Finset (Fin c × Fin w)} {x : Fin c × Fin w} (hx : x ∉ s)
    (keys : Fin c → Key) (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (hcorr : iF.IsCorrectKey (keys x.1)) :
    streamEntry iF x (db x) (streamUpTo iF db s keys regBlocks backupBlocks) =
      streamUpTo iF db (insert x s) keys regBlocks backupBlocks := by
  ext j
  · rfl
  · simp only [streamEntry, streamUpTo, hcorr j x.2]
    by_cases hj : j.val < nReg
    · rw [sum_ite_mem_insert db (fun a => iF.eval (keys a) j) (regBlocks j) hx]
      by_cases hev : iF.eval (keys x.1) j = x.2 <;> by_cases hP : x.1 ∈ regBlocks j <;>
        simp [hj, hev, hP, bool_false_add]
    · simp [hj]
  · simp only [streamEntry, streamUpTo, hcorr j x.2]
    by_cases hj : j.val < nReg
    · simp [hj]
    · rw [sum_ite_mem_insert db (fun a => iF.eval (keys a) j) (backupBlocks j) hx,
        sum_ite_mem_insert db (fun a => iF.eval (keys a) j) (Finset.univ \ backupBlocks j) hx]
      by_cases hev : iF.eval (keys x.1) j = x.2 <;> by_cases hB : x.1 ∈ backupBlocks j <;>
        simp [hj, hev, hB, bool_false_add]
  · rfl

/-- Folding `streamEntry` over any duplicate-free list of database entries `xs` starting from
`initPlinkoState` produces `streamUpTo iF db xs.toFinset`. -/
theorem foldr_streamEntry_eq_streamUpTo {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (hcorr : ∀ α : Fin c, iF.IsCorrectKey (keys α))
    {xs : List (Fin c × Fin w)} (hnd : xs.Nodup) :
    xs.foldr (fun x st => streamEntry iF x (db x) st)
      (initPlinkoState keys regBlocks backupBlocks) =
      streamUpTo iF db xs.toFinset keys regBlocks backupBlocks := by
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    have hx : x ∉ xs.toFinset := by simpa using hnd.1
    simp only [List.foldr_cons, ih hnd.2, List.toFinset_cons,
      streamEntry_streamUpTo db hx keys regBlocks backupBlocks (hcorr x.1)]

/-- **Offline single-pass entry streaming correctness**
([Hoover, Patel, Persiano and Yeo, Figure 7, `HintInit`][HooverPatelPersianoYeo2025]): folding
`streamEntry` once over `(Finset.univ : Finset (Fin c × Fin w)).toList` starting from
`initPlinkoState` produces `streamPreprocess`. -/
theorem foldr_streamEntry_univ {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (hcorr : ∀ α : Fin c, iF.IsCorrectKey (keys α)) :
    (Finset.univ : Finset (Fin c × Fin w)).toList.foldr
      (fun x st => streamEntry iF x (db x) st)
      (initPlinkoState keys regBlocks backupBlocks) =
      streamPreprocess iF db keys regBlocks backupBlocks := by
  rw [foldr_streamEntry_eq_streamUpTo db keys regBlocks backupBlocks hcorr
    (Finset.nodup_toList _), Finset.toList_toFinset, streamUpTo_univ]

/-! ### State validity, online execution, and conditional multi-query correctness -/

/-- Finds the first unconsumed backup slot `j' : Fin (nReg + nBackup)` where `T j'` is `some _`
([Hoover, Patel, Persiano and Yeo, Figure 7, `Recon`,
`j' ← arg min_j (T[j] ≠ ⊥)`][HooverPatelPersianoYeo2025]). -/
@[expose] def findBackupSlot (T : Fin (nReg + nBackup) → Option (BackupHint c)) :
    Option (Fin (nReg + nBackup)) :=
  (List.finRange (nReg + nBackup)).find? (fun j => (T j).isSome)

/-- Retained per-query client state between `query`, `reconstruct`, and `refresh` in
`plinkoScheme`. -/
structure PlinkoQueryRecord (nReg nBackup : ℕ) where
  /-- `some a` when the queried index `x` was found in `st.cache`, `none` otherwise. -/
  cachedBit : Option Bool
  /-- Matched active hint slot `j` in `st.H` when `x` was not cached. -/
  matchedSlot : Option (Fin (nReg + nBackup))
  /-- Parity `p` of the matched active hint. -/
  matchedParity : Bool
  /-- Random order bit `b : Bool` indicating whether `P'` was complemented. -/
  coin : Bool

/-- Updates the client hint state after reconstructing bit `a` for query `x`
([Hoover, Patel, Persiano and Yeo, Figure 7, `Recon`][HooverPatelPersianoYeo2025]): on a cache hit,
the state is unchanged; on an uncached query matching slot `j`, slot `j` in `H` is consumed
(`none`), the first available backup slot `j'` in `T` is promoted to `H[j']`, `T[j']` is set to
`none`, and `cache x` records `(a, j')`. -/
@[expose] def refreshPlinkoState (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (rec : PlinkoQueryRecord nReg nBackup) (a : Bool) :
    PlinkoState c w nReg nBackup Key :=
  match rec.cachedBit with
  | some _ => st
  | none =>
    match rec.matchedSlot, findBackupSlot st.T with
    | some j, some j' =>
      match st.T j' with
      | some bk =>
        let P_prom := if x.1 ∈ bk.blocks then Finset.univ \ bk.blocks else bk.blocks
        let p_prom := (if x.1 ∈ bk.blocks then bk.parityOut else bk.parityIn) + a
        { keys := st.keys
          H := Function.update (Function.update st.H j none) j'
            (some (.promoted P_prom x p_prom))
          T := Function.update st.T j' none
          cache := Function.update st.cache x (some (a, j')) }
      | none => st
    | _, _ => st

namespace PlinkoState

/-- Parity and structural validity invariant for `st : PlinkoState c w nReg nBackup Key` against
database `db` and iPRF `iF`:

1. Every active regular hint `st.H j = some (.regular P p)` has
   `p = blockParity db P (fun a => iF.eval (st.keys a) j)`.
2. Every active promoted hint `st.H j = some (.promoted P x p)` has `x.1 ∉ P`,
   `p = db x + blockParity db P (fun a => iF.eval (st.keys a) j)`, and
   `st.cache x = some (db x, j)`.
3. Every unconsumed backup hint `st.T j = some bk` has
   `bk.parityIn = blockParity db bk.blocks (fun a => iF.eval (st.keys a) j)`,
   `bk.parityOut = blockParity db (Finset.univ \ bk.blocks) (fun a => iF.eval (st.keys a) j)`,
   `st.H j = none`, and no cache entry pointing to `j`.
4. Every cache entry `st.cache x = some (a, j)` stores `a = db x` and, if `st.H j = some h`,
   `h` is a promoted hint for `x`. -/
structure Valid (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (st : PlinkoState c w nReg nBackup Key) : Prop where
  /-- Regular hint parity invariant. -/
  valid_regular : ∀ (j : Fin (nReg + nBackup)) (P : Finset (Fin c)) (p : Bool),
    st.H j = some (.regular P p) →
      p = blockParity db P (fun a => iF.eval (st.keys a) j)
  /-- Promoted backup hint parity and cache-link invariant. -/
  valid_promoted : ∀ (j : Fin (nReg + nBackup)) (P : Finset (Fin c)) (x : Fin c × Fin w)
    (p : Bool),
    st.H j = some (.promoted P x p) →
      x.1 ∉ P ∧ p = db x + blockParity db P (fun a => iF.eval (st.keys a) j) ∧
        st.cache x = some (db x, j)
  /-- Unconsumed backup hint parity and slot-disjointness invariant. -/
  valid_backup : ∀ (j : Fin (nReg + nBackup)) (bk : BackupHint c),
    st.T j = some bk →
      bk.parityIn = blockParity db bk.blocks (fun a => iF.eval (st.keys a) j) ∧
        bk.parityOut =
          blockParity db (Finset.univ \ bk.blocks) (fun a => iF.eval (st.keys a) j) ∧
        st.H j = none ∧ ∀ x : Fin c × Fin w, (st.cache x).map Prod.snd ≠ some j
  /-- Query cache bit and slot invariant. -/
  valid_cache : ∀ (x : Fin c × Fin w) (a : Bool) (j : Fin (nReg + nBackup)),
    st.cache x = some (a, j) →
      a = db x ∧ ∀ h : ActiveHint c w, st.H j = some h → ∃ P p, h = .promoted P x p

/-- **Offline preprocessing produces a valid state**
([Hoover, Patel, Persiano and Yeo, Figure 7, `HintInit`][HooverPatelPersianoYeo2025]). -/
theorem valid_streamPreprocess (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    Valid iF db (streamPreprocess iF db keys regBlocks backupBlocks) where
  valid_regular j P p hH := by
    simp only [streamPreprocess] at hH
    split_ifs at hH with hj
    simp only [Option.some.injEq, ActiveHint.regular.injEq] at hH
    obtain ⟨rfl, rfl⟩ := hH
    rfl
  valid_promoted j P x p hH := by
    simp only [streamPreprocess] at hH
    split_ifs at hH
    simp at hH
  valid_backup j bk hT := by
    simp only [streamPreprocess] at hT ⊢
    split_ifs at hT with hj
    simp only [Option.some.injEq] at hT
    subst hT
    refine ⟨rfl, rfl, by simp [hj], fun _ => by simp⟩
  valid_cache x a j hC := by
    simp [streamPreprocess] at hC

/-- If `getHint iF st x = some (j, P, p, o)` on a valid state `st` and
`iF.IsCorrectKey (st.keys x.1)` holds, then `x.1 ∈ P`, `o x.1 = x.2`, and
`p = blockParity db P o`. -/
theorem getHint_valid_props {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key} {x : Fin c × Fin w}
    {j : Fin (nReg + nBackup)} {P : Finset (Fin c)} {p : Bool} {o : Fin c → Fin w}
    (hvalid : st.Valid iF db) (hcorr : iF.IsCorrectKey (st.keys x.1))
    (hget : getHint iF st x = some (j, P, p, o)) :
    st.H j ≠ none ∧ x.1 ∈ P ∧ o x.1 = x.2 ∧ p = blockParity db P o := by
  dsimp only [getHint] at hget
  cases hfind : findHintSlot iF st x with
  | none => simp [hfind] at hget
  | some j₀ =>
    rw [hfind] at hget
    dsimp only at hget
    have hmem_sort : j₀ ∈ (iF.inv (st.keys x.1) x.2).sort (· ≤ ·) :=
      List.mem_of_find?_eq_some hfind
    have hj₀_eval : iF.eval (st.keys x.1) j₀ = x.2 :=
      (hcorr j₀ x.2).mp ((Finset.mem_sort (· ≤ ·)).mp hmem_sort)
    cases hH : st.H j₀ with
    | none => simp [hH] at hget
    | some h =>
      rw [hH] at hget
      dsimp only at hget
      cases h with
      | regular P₀ p₀ =>
        dsimp only [extractActiveHint] at hget
        by_cases hxP₀ : x.1 ∈ P₀
        · simp only [hxP₀, ↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hget
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hget
          exact ⟨by simp [hH], hxP₀, hj₀_eval, hvalid.valid_regular j₀ P₀ p₀ hH⟩
        · simp [hxP₀] at hget
      | promoted P₀ y p₀ =>
        dsimp only [extractActiveHint] at hget
        by_cases hcond : (x.1 = y.1 ∧ x.2 = y.2) ∨ (x.1 ≠ y.1 ∧ x.1 ∈ P₀)
        · simp only [hcond, ↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hget
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hget
          obtain ⟨hyP₀, hp₀, -⟩ := hvalid.valid_promoted j₀ P₀ y p₀ hH
          have hpar : p₀ = blockParity db (insert y.1 P₀)
              (Function.update (fun a => iF.eval (st.keys a) j₀) y.1 y.2) := by
            rw [blockParity_insert_of_notMem db hyP₀, Function.update_self, Prod.mk.eta,
              blockParity_update_of_notMem db hyP₀, hp₀]
          rcases hcond with ⟨hx1, hx2⟩ | ⟨hne, hxP₀⟩
          · refine ⟨by simp [hH], by simp [hx1], ?_, hpar⟩
            rw [hx1, Function.update_self, hx2]
          · refine ⟨by simp [hH], Finset.mem_insert_of_mem hxP₀, ?_, hpar⟩
            rw [Function.update_of_ne hne, hj₀_eval]
        · simp [hcond] at hget

/-- Precondition for answering query `x` from state `st`: either `x` is already in `st.cache`, or
`getHint iF st x` finds a matching active hint and `st.T` has an unconsumed backup hint. -/
@[expose] def CanAnswer (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) : Prop :=
  (st.cache x).isSome ∨ ((getHint iF st x).isSome ∧ (findBackupSlot st.T).isSome)

/-- Deterministic next hint state produced after an honest query-answer-reconstruct-refresh step on
database `db` and index `x`. -/
@[expose] def nextState (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    PlinkoState c w nReg nBackup Key :=
  refreshPlinkoState st x
    ⟨(st.cache x).map Prod.fst,
     if (st.cache x).isSome then none else (getHint iF st x).map Prod.fst,
     false, false⟩
    (db x)

@[simp]
theorem refreshPlinkoState_keys (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (rec : PlinkoQueryRecord nReg nBackup) (a : Bool) :
    (refreshPlinkoState st x rec a).keys = st.keys := by
  dsimp only [refreshPlinkoState]
  cases rec.cachedBit with
  | some _ => rfl
  | none =>
    cases rec.matchedSlot with
    | none => rfl
    | some j =>
      cases h : findBackupSlot st.T with
      | none => rfl
      | some j' =>
        dsimp only
        cases st.T j' <;> rfl

@[simp]
theorem nextState_keys (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    (st.nextState iF db x).keys = st.keys :=
  refreshPlinkoState_keys st x _ (db x)

/-- Sequential availability predicate over a query list `xs : List (Fin c × Fin w)`. -/
@[expose] def CanAnswerSeq (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) : PlinkoState c w nReg nBackup Key → List (Fin c × Fin w) → Prop
  | _, [] => True
  | st, x :: xs => st.CanAnswer iF x ∧ CanAnswerSeq iF db (st.nextState iF db x) xs

/-- **Preservation of `Valid` under `nextState`**
([Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7, `Recon`][HooverPatelPersianoYeo2025]):
if `st.Valid iF db`, `st.CanAnswer iF x`, and `iF.IsCorrectKey (st.keys x.1)` hold, then
`st.nextState iF db x` satisfies `Valid iF db`. -/
theorem valid_nextState {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key} {x : Fin c × Fin w}
    (hvalid : st.Valid iF db) (hcorr : iF.IsCorrectKey (st.keys x.1))
    (hcan : st.CanAnswer iF x) :
    (st.nextState iF db x).Valid iF db := by
  dsimp only [nextState, refreshPlinkoState]
  cases hcache : st.cache x with
  | some cj => simpa [hcache] using hvalid
  | none =>
    rcases hcan with hc | ⟨hget_some, hbak_some⟩
    · simp [hcache] at hc
    · obtain ⟨⟨j, P, p, o⟩, hget⟩ := Option.isSome_iff_exists.mp hget_some
      obtain ⟨j', hbak⟩ := Option.isSome_iff_exists.mp hbak_some
      have hTj' : (st.T j').isSome := by simpa [findBackupSlot] using List.find?_some hbak
      obtain ⟨bk, hbk⟩ := Option.isSome_iff_exists.mp hTj'
      obtain ⟨hHj_ne, -, -, -⟩ := getHint_valid_props hvalid hcorr hget
      obtain ⟨hbk_in, hbk_out, hHj'_none, hcache_j'⟩ := hvalid.valid_backup j' bk hbk
      have hj_ne_j' : j ≠ j' := fun heq => hHj_ne (heq ▸ hHj'_none)
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        hget, Option.map_some, hbak, hbk]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k P_k p_k hHk
        have hne1 : k ≠ j' := by rintro rfl; simp at hHk
        have hne2 : k ≠ j := by rintro rfl; simp [hne1] at hHk
        simp only [Function.update_of_ne hne1, Function.update_of_ne hne2] at hHk
        exact hvalid.valid_regular k P_k p_k hHk
      · intro k P_k y p_k hHk
        by_cases hkj' : k = j'
        · subst hkj'
          simp only [Function.update_self, Option.some.injEq, ActiveHint.promoted.injEq] at hHk
          obtain ⟨rfl, rfl, rfl⟩ := hHk
          refine ⟨by by_cases hxB : x.1 ∈ bk.blocks <;> simp [hxB], ?_,
            by simp [Function.update_self]⟩
          by_cases hxB : x.1 ∈ bk.blocks <;> simp [hxB, hbk_out, hbk_in, add_comm]
        · have hkj : k ≠ j := by rintro rfl; simp [hkj'] at hHk
          simp only [Function.update_of_ne hkj', Function.update_of_ne hkj] at hHk
          obtain ⟨hyP, hp_k, hcy⟩ := hvalid.valid_promoted k P_k y p_k hHk
          have hyx : y ≠ x := fun h => by rw [h, hcache] at hcy; cases hcy
          exact ⟨hyP, hp_k, by simp [Function.update_of_ne hyx, hcy]⟩
      · intro k bk_k hTk
        have hkj' : k ≠ j' := by rintro rfl; simp at hTk
        simp only [Function.update_of_ne hkj'] at hTk
        obtain ⟨hin, hout, hHk_none, hck⟩ := hvalid.valid_backup k bk_k hTk
        have hkj : k ≠ j := fun heq => hHj_ne (heq ▸ hHk_none)
        refine ⟨hin, hout, by simp [Function.update_of_ne hkj', Function.update_of_ne hkj,
          hHk_none], fun y => ?_⟩
        by_cases hyx : y = x
        · subst hyx; simp [Function.update_self, Ne.symm hkj']
        · simp [Function.update_of_ne hyx, hck y]
      · intro y a_y k hcy
        by_cases hyx : y = x
        · subst hyx
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hcy
          obtain ⟨rfl, rfl⟩ := hcy
          refine ⟨rfl, fun h hh => ?_⟩
          simp only [Function.update_self, Option.some.injEq] at hh
          exact ⟨_, _, hh.symm⟩
        · simp only [Function.update_of_ne hyx] at hcy
          obtain ⟨rfl, hprom⟩ := hvalid.valid_cache y a_y k hcy
          have hkj' : k ≠ j' := fun heq => hcache_j' y (by simp [heq, hcy])
          refine ⟨rfl, fun h hh => ?_⟩
          have hkj : k ≠ j := by rintro rfl; simp [hkj'] at hh
          simp only [Function.update_of_ne hkj', Function.update_of_ne hkj] at hh
          exact hprom h hh

end PlinkoState

/-! ### Single-query and hybrid multi-query privacy -/

/-- The subtype of `(c / 2)`-element block subsets of `Fin c`. -/
@[expose] def HalfBlocks (c : ℕ) : Type :=
  { S : Finset (Fin c) // S.card = c / 2 }

instance (c : ℕ) : Fintype (HalfBlocks c) :=
  Subtype.fintype _

instance (c : ℕ) : DecidableEq (HalfBlocks c) :=
  inferInstanceAs (DecidableEq { S : Finset (Fin c) // S.card = c / 2 })

instance (c : ℕ) : Nonempty (HalfBlocks c) := by
  have hle : c / 2 ≤ (Finset.univ : Finset (Fin c)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Nat.div_le_self c 2
  obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hle
  exact ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩⟩

/-- The subtype of `(min (c / 2 + 1) c)`-element regular block subsets of `Fin c`. -/
@[expose] def RegBlocks (c : ℕ) : Type :=
  { P : Finset (Fin c) // P.card = min (c / 2 + 1) c }

instance (c : ℕ) : Fintype (RegBlocks c) :=
  Subtype.fintype _

instance (c : ℕ) : DecidableEq (RegBlocks c) :=
  inferInstanceAs (DecidableEq { P : Finset (Fin c) // P.card = min (c / 2 + 1) c })

instance (c : ℕ) : Nonempty (RegBlocks c) := by
  have hle : min (c / 2 + 1) c ≤ (Finset.univ : Finset (Fin c)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Nat.min_le_right _ _
  obtain ⟨P, hP⟩ := Finset.powersetCard_nonempty.mpr hle
  exact ⟨⟨P, (Finset.mem_powersetCard.mp hP).2⟩⟩

/-- The subtype of `(c / 2 + 1)`-element block subsets of `Fin c` that contain block `α`. -/
@[expose] def RegBlocksContaining (c : ℕ) (α : Fin c) : Type :=
  { P : Finset (Fin c) // P.card = c / 2 + 1 ∧ α ∈ P }

instance (c : ℕ) (α : Fin c) : Fintype (RegBlocksContaining c α) :=
  Subtype.fintype _

instance (c : ℕ) (α : Fin c) : DecidableEq (RegBlocksContaining c α) :=
  inferInstanceAs (DecidableEq { P : Finset (Fin c) // P.card = c / 2 + 1 ∧ α ∈ P })

/-- The subtype of offset vectors `o : Fin c → Fin w` satisfying `o x.1 = x.2`. -/
@[expose] def OffsetsContaining (c w : ℕ) (x : Fin c × Fin w) : Type :=
  { o : Fin c → Fin w // o x.1 = x.2 }

instance (c w : ℕ) (x : Fin c × Fin w) : Fintype (OffsetsContaining c w x) :=
  Subtype.fintype _

instance (c w : ℕ) (x : Fin c × Fin w) : DecidableEq (OffsetsContaining c w x) :=
  inferInstanceAs (DecidableEq { o : Fin c → Fin w // o x.1 = x.2 })

instance (c w : ℕ) (x : Fin c × Fin w) : Nonempty (OffsetsContaining c w x) :=
  ⟨⟨fun _ => x.2, rfl⟩⟩

/-- Index-independent query simulator for Plinko
([Hoover, Patel, Persiano and Yeo, Section 5.2, p. 22][HooverPatelPersianoYeo2025]):
samples a uniform `(c / 2)`-subset of blocks `S : HalfBlocks c` and an independent uniform offset
vector `o : Fin c → Fin w`. -/
@[expose] noncomputable def plinkoSim (c w : ℕ) [NeZero w] : ProbComp (PlinkoQuery c w) := do
  let S ← ProbComp.uniform (HalfBlocks c)
  let o ← ProbComp.uniform (Fin c → Fin w)
  pure ⟨S.1, o⟩

/-- Full `Preprocessing.Scheme` packaging of Plinko
([Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]). -/
@[expose] noncomputable def plinkoScheme (c w nReg nBackup : ℕ) [NeZero w]
    [Fintype Key] [Nonempty Key] (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)) :
    Scheme (Fin c × Fin w) (PlinkoState c w nReg nBackup Key)
      (PlinkoQueryRecord nReg nBackup) (PlinkoQuery c w) (Bool × Bool) where
  preprocess db := do
    let keys ← ProbComp.uniform (Fin c → Key)
    let regB ← ProbComp.uniform (Fin (nReg + nBackup) → RegBlocks c)
    let bakB ← ProbComp.uniform (Fin (nReg + nBackup) → HalfBlocks c)
    pure (streamPreprocess iF db keys (fun j => (regB j).1) (fun j => (bakB j).1))
  query st x := do
    let b ← ProbComp.uniform Bool
    let r ← ProbComp.uniform (Fin w)
    let qDummy ← plinkoSim c w
    match st.cache x with
    | some (cachedBit, _) =>
      pure (⟨some cachedBit, none, false, b⟩, qDummy)
    | none =>
      match getHint iF st x with
      | some (j, P, p, o) =>
        pure (⟨none, some j, p, b⟩, buildQuery x P o b r)
      | none =>
        pure (⟨none, none, false, b⟩, qDummy)
  answer db q := plinkoAnswer db q
  reconstruct rec ans :=
    match rec.cachedBit with
    | some a => a
    | none => plinkoReconstruct rec.matchedParity rec.coin ans
  refresh st x rec a := pure (refreshPlinkoState st x rec a)

namespace PlinkoState

variable [NeZero w] [Fintype Key] [Nonempty Key]

/-- **Single-step exact evaluation of `plinkoScheme`**: when `st.Valid iF db`,
`st.CanAnswer iF x`, and `iF.IsCorrectKey (st.keys x.1)` hold, one honest online step of
`plinkoScheme` outputs `(st.nextState iF db x, db x)` with probability one. -/
theorem eval_step_plinkoScheme {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key} {x : Fin c × Fin w}
    (hvalid : st.Valid iF db) (hcorr : iF.IsCorrectKey (st.keys x.1))
    (hcan : st.CanAnswer iF x) :
    ProbComp.eval ((plinkoScheme c w nReg nBackup iF).step db st x) =
      PMF.pure (st.nextState iF db x, db x) := by
  have hsupp : ∀ p ∈ (ProbComp.eval ((plinkoScheme c w nReg nBackup iF).step db st x)).support,
      p = (st.nextState iF db x, db x) := by
    rintro ⟨st', β⟩ hmem
    simp only [Scheme.step, plinkoScheme, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
    obtain ⟨⟨rec, q⟩, ⟨b, -, r, -, qDummy, -, hq⟩, hstep⟩ := hmem
    cases hcache : st.cache x with
    | some cj =>
      rw [hcache] at hq
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hq hstep
      obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨_, rfl, rfl, rfl⟩ := hstep
      obtain ⟨hadb, -⟩ := hvalid.valid_cache x cj.1 cj.2 hcache
      simp [nextState, refreshPlinkoState, hcache, hadb]
    | none =>
      rcases hcan with hc | ⟨hget_some, _⟩
      · simp [hcache] at hc
      · obtain ⟨⟨j, P, p, o⟩, hget⟩ := Option.isSome_iff_exists.mp hget_some
        obtain ⟨-, hxP, hox, hp⟩ := getHint_valid_props hvalid hcorr hget
        rw [hcache, hget] at hq
        simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hq hstep
        obtain ⟨rfl, rfl⟩ := hq
        have hrec : plinkoReconstruct p b (plinkoAnswer db (buildQuery x P o b r)) = db x := by
          rw [hp, plinkoReconstruct_plinkoAnswer_eq db x P o b r hxP hox]
        obtain ⟨_, rfl, rfl, rfl⟩ := hstep
        simp [nextState, refreshPlinkoState, hcache, hget, hrec]
  have hmap := Cslib.Probability.PMF.map_congr_on_support
    (ProbComp.eval ((plinkoScheme c w nReg nBackup iF).step db st x))
    id (Function.const _ (st.nextState iF db x, db x)) hsupp
  simpa only [PMF.map_id, PMF.map_const] using hmap

/-- **Conditional multi-query correctness of `plinkoScheme`**
([Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7][HooverPatelPersianoYeo2025]):
if `st.Valid iF db`, `∀ α, iF.IsCorrectKey (st.keys α)`, and `st.CanAnswerSeq iF db xs` hold, then
`(plinkoScheme c w nReg nBackup iF).IsCorrectFrom db st xs` holds, and every hint state reached
after `xs` satisfies `Valid iF db`. -/
theorem isCorrectFrom_plinkoScheme {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    {xs : List (Fin c × Fin w)} (hvalid : st.Valid iF db)
    (hcorr : ∀ α : Fin c, iF.IsCorrectKey (st.keys α))
    (hcan : st.CanAnswerSeq iF db xs) :
    (plinkoScheme c w nReg nBackup iF).IsCorrectFrom db st xs ∧
      ∀ st' βs,
        (st', βs) ∈ (ProbComp.eval
          ((plinkoScheme c w nReg nBackup iF).runQueriesFrom db st xs)).support →
        st'.Valid iF db := by
  induction xs generalizing st with
  | nil =>
    refine ⟨Scheme.isCorrectFrom_nil _ _ _, fun st' βs hmem => ?_⟩
    simp only [Scheme.runQueriesFrom, ProbComp.eval_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    exact hmem.1 ▸ hvalid
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hcan
    have hvalid' := valid_nextState hvalid (hcorr x.1) hx
    obtain ⟨hcorr_tail, hvalid_tail⟩ := ih hvalid' (by simpa using hcorr) hxs
    have hstep := eval_step_plinkoScheme hvalid (hcorr x.1) hx
    refine ⟨Scheme.isCorrectFrom_cons fun st₁ β hmem₁ => ?_, fun st'' βs hmem => ?_⟩
    · rw [hstep, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem₁
      obtain ⟨rfl, rfl⟩ := hmem₁
      exact ⟨rfl, hcorr_tail⟩
    · simp only [Scheme.runQueriesFrom, ProbComp.eval_bind, hstep, PMF.pure_bind,
        ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨⟨st₂, βs'⟩, hmem₂, rfl, -⟩ := hmem
      exact hvalid_tail st'' βs' hmem₂

end PlinkoState

/-! ### Bijective query decompositions and single-query / multi-query privacy -/

private theorem card_sdiff_univ_of_even {c : ℕ} (hc : Even c) {s : Finset (Fin c)}
    (hs : s.card = c / 2) : (Finset.univ \ s).card = c / 2 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, Fintype.card_fin, hs]
  obtain ⟨k, rfl⟩ := hc
  omega

/-- Bijection between `(c / 2 + 1)`-subsets of `Fin c` containing `α` paired with the order bit
`b : Bool` and `(c / 2)`-subsets of `Fin c` (`HalfBlocks c`), when `Even c`. -/
@[expose] def queryBlocksEquiv {c : ℕ} (hc : Even c) (α : Fin c) :
    RegBlocksContaining c α × Bool ≃ HalfBlocks c where
  toFun := fun ⟨⟨P, hcard, hα⟩, b⟩ =>
    let P' := P.erase α
    have hP' : P'.card = c / 2 := by
      rw [Finset.card_erase_of_mem hα, hcard, Nat.add_sub_cancel]
    ⟨if b then Finset.univ \ P' else P',
      by cases b
         · exact hP'
         · exact card_sdiff_univ_of_even hc hP'⟩
  invFun S :=
    if hα : α ∈ S.1 then
      (⟨insert α (Finset.univ \ S.1),
        by
          have hnot : α ∉ Finset.univ \ S.1 := by simp [hα]
          rw [Finset.card_insert_of_notMem hnot, card_sdiff_univ_of_even hc S.2],
        Finset.mem_insert_self α _⟩,
       true)
    else
      (⟨insert α S.1,
        by rw [Finset.card_insert_of_notMem hα, S.2],
        Finset.mem_insert_self α _⟩,
       false)
  left_inv := by
    rintro ⟨⟨P, hcard, hαP⟩, b⟩
    cases b
    · have hnot : α ∉ P.erase α := Finset.notMem_erase α P
      simp [hnot, Finset.insert_erase hαP]
    · have hmem : α ∈ Finset.univ \ P.erase α := by simp
      simp [hmem, Finset.insert_erase hαP]
  right_inv := by
    rintro ⟨S, hcard⟩
    apply Subtype.ext
    by_cases hα : α ∈ S
    · have hnot : α ∉ Finset.univ \ S := by simp [hα]
      simp [hα, Finset.erase_insert hnot]
    · simp [hα, Finset.erase_insert hα]

/-- When `Even c`, `RegBlocksContaining c α` is nonempty for every `α : Fin c`. -/
instance {c : ℕ} [Fact (Even c)] (α : Fin c) : Nonempty (RegBlocksContaining c α) :=
  ⟨((queryBlocksEquiv Fact.out α).symm (Classical.arbitrary (HalfBlocks c))).1⟩

/-- Bijection between offset vectors `o : Fin c → Fin w` with `o x.1 = x.2` paired with a
replacement offset `r : Fin w` and arbitrary offset vectors `Fin c → Fin w`. -/
@[expose] def queryOffsetsEquiv (x : Fin c × Fin w) :
    OffsetsContaining c w x × Fin w ≃ (Fin c → Fin w) where
  toFun := fun ⟨⟨o, _⟩, r⟩ => Function.update o x.1 r
  invFun q := (⟨Function.update q x.1 x.2, Function.update_self _ _ _⟩, q x.1)
  left_inv := by
    rintro ⟨⟨o, ho⟩, r⟩
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp only [Function.update_idem]
      rw [← ho, Function.update_eq_self]
    · simp
  right_inv q := by
    ext a
    simp

private theorem uniformOfFintype_bind_bind_equiv_single {α β γ ε : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ]
    (e : α × β ≃ γ) (f : γ → PMF ε) :
    ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind fun b =>
      f (e (a, b))) =
      (PMF.uniformOfFintype γ).bind f := by
  calc _ = (PMF.uniformOfFintype (α × β)).bind (fun ab => f (e ab)) := by
        rw [← PMF.uniformOfFintype_prod, PMF.bind_bind]
        simp only [PMF.bind_map, Function.comp_def]
    _ = ((PMF.uniformOfFintype (α × β)).map e).bind f := by
        rw [PMF.bind_map]; rfl
    _ = (PMF.uniformOfFintype γ).bind f := by
        rw [PMF.uniformOfFintype_map_equiv]

/-- **Continuation-passing exact privacy of `buildQuery`**: when `Even c`, binding any continuation
`k` to `buildQuery x P.1 o.1 b r` over uniform `(P, o, b, r)` equals binding `k` to
`plinkoSim c w`. -/
theorem uniformOfFintype_bind_buildQuery {c w : ℕ} [Fact (Even c)] [NeZero w]
    {ε : Type*} (x : Fin c × Fin w) (k : PlinkoQuery c w → PMF ε) :
    ((PMF.uniformOfFintype (RegBlocksContaining c x.1)).bind fun P =>
      (PMF.uniformOfFintype (OffsetsContaining c w x)).bind fun o =>
        (PMF.uniformOfFintype Bool).bind fun b =>
          (PMF.uniformOfFintype (Fin w)).bind fun r =>
            k (buildQuery x P.1 o.1 b r)) =
      (ProbComp.eval (plinkoSim c w)).bind k := by
  have hcomm : ∀ P : RegBlocksContaining c x.1,
      ((PMF.uniformOfFintype (OffsetsContaining c w x)).bind fun o =>
        (PMF.uniformOfFintype Bool).bind fun b =>
          (PMF.uniformOfFintype (Fin w)).bind fun r =>
            k (buildQuery x P.1 o.1 b r)) =
      (PMF.uniformOfFintype Bool).bind fun b =>
        (PMF.uniformOfFintype (Fin c → Fin w)).bind fun o' =>
          k ⟨(queryBlocksEquiv Fact.out x.1 (P, b)).1, o'⟩ := by
    intro P
    rw [PMF.bind_comm]
    congr 1; funext b
    exact uniformOfFintype_bind_bind_equiv_single (queryOffsetsEquiv x)
      (fun o' => k ⟨(queryBlocksEquiv Fact.out x.1 (P, b)).1, o'⟩)
  simp only [plinkoSim, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  trans ((PMF.uniformOfFintype (RegBlocksContaining c x.1)).bind fun P =>
    (PMF.uniformOfFintype Bool).bind fun b =>
      (PMF.uniformOfFintype (Fin c → Fin w)).bind fun o' =>
        k ⟨(queryBlocksEquiv Fact.out x.1 (P, b)).1, o'⟩)
  · congr 1; funext P; exact hcomm P
  · exact uniformOfFintype_bind_bind_equiv_single (queryBlocksEquiv Fact.out x.1)
      (fun S => (PMF.uniformOfFintype (Fin c → Fin w)).bind fun o' => k ⟨S.1, o'⟩)

/-- **Single-query exact privacy of Plinko**
([Hoover, Patel, Persiano and Yeo, Section 5.2, p. 22][HooverPatelPersianoYeo2025]):
when `Even c`, if the consumed hint `(P, o)` is distributed as a uniform regular hint conditioned
on containing `x = (α, β)` (`P ← ProbComp.uniform (RegBlocksContaining c x.1)` and
`o ← ProbComp.uniform (OffsetsContaining c w x)`), then the query message
`buildQuery x P.1 o.1 b r` has the exact simulator distribution `plinkoSim c w`, independent of
`x`. -/
theorem eval_buildQuery_conditioned_eq_plinkoSim {c w : ℕ} [Fact (Even c)] [NeZero w]
    (x : Fin c × Fin w) :
    ProbComp.eval (do
      let P ← ProbComp.uniform (RegBlocksContaining c x.1)
      let o ← ProbComp.uniform (OffsetsContaining c w x)
      let b ← ProbComp.uniform Bool
      let r ← ProbComp.uniform (Fin w)
      pure (buildQuery x P.1 o.1 b r)) =
      ProbComp.eval (plinkoSim c w) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  exact (uniformOfFintype_bind_buildQuery x PMF.pure).trans (PMF.bind_pure _)

/-- **Idealized random-hint hybrid of Plinko (`plinkoHybridScheme`)**: a proof device for the
ideal-random-set privacy analysis of
[Hoover, Patel, Persiano and Yeo, Section 5.2][HooverPatelPersianoYeo2025]. At each online query
for `x = (α, β)`, it samples a fresh conditioned regular hint
`(P, o) ← RegBlocksContaining c x.1 × OffsetsContaining c w x`, computes the exact hint parity
`p = blockParity db P.1 o.1` from the database stored in its state, sends
`buildQuery x P.1 o.1 b r`, and reconstructs `db x = plinkoReconstruct p b ans`.

Unlike `pianoHybridScheme`, `plinkoHybridScheme` is **both** a correct PIR scheme
(`isCorrect_plinkoHybridScheme`) and adaptively perfectly private
(`isPerfectlyPrivateWith_plinkoHybridScheme`); it is a proof device because it retains `db` in its
state to compute exact hint parities online and draws a fresh conditioned hint at each query rather
than scanning the finite table `PlinkoState`. -/
@[expose] noncomputable def plinkoHybridScheme (c w : ℕ) [Fact (Even c)] [NeZero w] :
    Scheme (Fin c × Fin w) (Fin c × Fin w → Bool) (Bool × Bool) (PlinkoQuery c w)
      (Bool × Bool) where
  preprocess db := pure db
  query db x := do
    let P ← ProbComp.uniform (RegBlocksContaining c x.1)
    let o ← ProbComp.uniform (OffsetsContaining c w x)
    let b ← ProbComp.uniform Bool
    let r ← ProbComp.uniform (Fin w)
    pure ((blockParity db P.1 o.1, b), buildQuery x P.1 o.1 b r)
  answer db q := plinkoAnswer db q
  reconstruct rec ans := plinkoReconstruct rec.1 rec.2 ans
  refresh db _ _ _ := pure db

/-- **Bridge lemma between `plinkoScheme.query` and `plinkoHybridScheme.query`**: on an uncached
query `x` where `getHint iF st x = some (j, P, p, o)`, the server query distribution of
`plinkoScheme` equals the query distribution built from `(P, o)` using the same map
`fun (b, r) => buildQuery x P o b r` as `plinkoHybridScheme`. -/
theorem eval_snd_plinkoScheme_query_of_getHint [NeZero w] [Fintype Key] [Nonempty Key]
    (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    {j : Fin (nReg + nBackup)} {P : Finset (Fin c)} {p : Bool} {o : Fin c → Fin w}
    (hcache : st.cache x = none) (hget : getHint iF st x = some (j, P, p, o)) :
    ProbComp.eval (Prod.snd <$> (plinkoScheme c w nReg nBackup iF).query st x) =
      ProbComp.eval (do
        let b ← ProbComp.uniform Bool
        let r ← ProbComp.uniform (Fin w)
        pure (buildQuery x P o b r)) := by
  simp only [plinkoScheme, hcache, hget, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.map_bind, PMF.bind_const, PMF.pure_map]

section HybridProperties

variable [Fact (Even c)] [NeZero w]

/-- `plinkoHybridScheme c w` is unconditionally multi-query correct (`Scheme.IsCorrect`). -/
theorem isCorrect_plinkoHybridScheme : (plinkoHybridScheme c w).IsCorrect := by
  refine Scheme.isCorrect_of_forall_preprocess fun db xs h₀ hmem => ?_
  simp only [plinkoHybridScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
  subst h₀
  induction xs with
  | nil => exact Scheme.isCorrectFrom_nil _ _ _
  | cons x xs ih =>
    refine Scheme.isCorrectFrom_cons fun h' β hmem => ?_
    simp only [Scheme.step, plinkoHybridScheme, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨⟨rec, q⟩, ⟨P, -, o, -, b, -, r, -, rfl, rfl⟩, _, rfl, rfl, rfl⟩ := hmem
    exact ⟨plinkoReconstruct_plinkoAnswer_eq h' x P.1 o.1 b r P.2.2 o.2, ih⟩

/-- Projected one-step transition of `(Unit, serverState)` in the adaptive privacy experiment for
`plinkoHybridScheme`. -/
private noncomputable def plinkoHybridAdaptiveStep {St : Type}
    (adv : AdaptiveServer (Fin c × Fin w) (PlinkoQuery c w) (Bool × Bool) St)
    (_ : Unit) (st : St) : PMF (Unit × St) :=
  (ProbComp.eval (adv.chooseQuery st)).bind fun p =>
    (ProbComp.eval (do
      let P ← ProbComp.uniform (RegBlocksContaining c p.2.1)
      let o ← ProbComp.uniform (OffsetsContaining c w p.2)
      let b ← ProbComp.uniform Bool
      let r ← ProbComp.uniform (Fin w)
      pure (buildQuery p.2 P.1 o.1 b r))).bind fun q =>
      (ProbComp.eval (adv.onQuery p.1 q)).map fun sa => ((), sa.1)

/-- **Multi-query adaptive perfect privacy of `plinkoHybridScheme`**
([Hoover, Patel, Persiano and Yeo, Section 5.2][HooverPatelPersianoYeo2025]): when `Even c`,
`plinkoHybridScheme c w` is perfectly private with simulator `plinkoSim c w` against any adaptive
malicious server `adv` over any number of queries `k`. -/
theorem isPerfectlyPrivateWith_plinkoHybridScheme :
    (plinkoHybridScheme c w).IsPerfectlyPrivateWith (plinkoSim c w) := by
  apply Scheme.isPerfectlyPrivateWith_of_invariant
    (proj := fun _ => ())
    (inv := PMF.pure ())
    (sim := plinkoSim c w)
    (stepS := fun adv => plinkoHybridAdaptiveStep adv)
  · intro db; simp [plinkoHybridScheme]
  · intro St adv db st
    dsimp only [plinkoHybridAdaptiveStep]
    simp only [Scheme.realAdaptiveStep, plinkoHybridScheme, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map]
    rfl
  · intro St adv st kCont
    dsimp only [plinkoHybridAdaptiveStep]
    simp_rw [eval_buildQuery_conditioned_eq_plinkoSim]
    simp only [idealAdaptiveStep, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem isPerfectlyPrivate_plinkoHybridScheme :
    (plinkoHybridScheme c w).IsPerfectlyPrivate :=
  isPerfectlyPrivateWith_plinkoHybridScheme.isPerfectlyPrivate

/-- Every adaptive malicious server with Boolean finalizer `finalize : St → Bool` has zero
distinguishing advantage against `plinkoHybridScheme c w`. -/
theorem privacyAdvantage_plinkoHybridScheme_eq_zero {St : Type}
    (adv : AdaptiveServer (Fin c × Fin w) (PlinkoQuery c w) (Bool × Bool) St)
    (finalize : St → Bool) (db : Fin c × Fin w → Bool) (k : ℕ) (st₀ : St) :
    (plinkoHybridScheme c w).privacyAdvantage (plinkoSim c w) adv finalize db k st₀ = 0 :=
  isPerfectlyPrivateWith_plinkoHybridScheme.privacyAdvantage_eq_zero adv finalize db k st₀

/-- **Multi-query non-adaptive transcript privacy of `plinkoHybridScheme`**: for every database
`db` and query list `xs : List (Fin c × Fin w)`, the query transcript of `plinkoHybridScheme c w`
has the same distribution as `xs.length` independent draws from `plinkoSim c w`. -/
theorem eval_queryTranscript_plinkoHybridScheme (db : Fin c × Fin w → Bool)
    (xs : List (Fin c × Fin w)) :
    ProbComp.eval ((plinkoHybridScheme c w).queryTranscript db xs) =
      ProbComp.eval (simTranscript (plinkoSim c w) xs.length) := by
  apply Scheme.eval_queryTranscript_eq_of_invariant
    (proj := fun _ => ())
    (inv := PMF.pure ())
    (sim := plinkoSim c w)
    (stepQ := fun _ _ => (ProbComp.eval (plinkoSim c w)).map fun q => ((), q))
  · simp [plinkoHybridScheme]
  · intro h x
    have heq := eval_buildQuery_conditioned_eq_plinkoSim (c := c) (w := w) x
    simp only [Scheme.queryStep, plinkoHybridScheme, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map] at heq ⊢
    rw [← heq]
    simp [PMF.bind_bind]
  · intro x kCont
    simp [PMF.bind_map, Function.comp_def]

end HybridProperties

/-! ### Database and hint updates (`UpdateDB` and `UpdateHint`, Definition 5.2 and Figure 7) -/

/-- Effect of flipping database entry `u : Fin c × Fin w` by XOR delta `d : Bool` on
`blockParity db P o`. -/
theorem blockParity_update_db (db : Fin c × Fin w → Bool) (u : Fin c × Fin w) (d : Bool)
    (P : Finset (Fin c)) (o : Fin c → Fin w) :
    blockParity (Function.update db u (d + db u)) P o =
      (if o u.1 = u.2 ∧ u.1 ∈ P then d else false) + blockParity db P o := by
  have hpoint : ∀ a ∈ P,
      Function.update db u (d + db u) (a, o a) =
        (if a = u.1 ∧ o u.1 = u.2 then d else false) + db (a, o a) := by
    intro a _
    by_cases hau : (a, o a) = u
    · have ha1 : a = u.1 := congrArg Prod.fst hau
      have ha2 : o u.1 = u.2 := ha1 ▸ congrArg Prod.snd hau
      rw [hau]
      simp [ha1, ha2]
    · have hne : ¬(a = u.1 ∧ o u.1 = u.2) := fun ⟨h1, h2⟩ => hau (Prod.ext h1 (h1 ▸ h2))
      simp [Function.update_of_ne hau, hne, bool_false_add]
  unfold blockParity
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  congr 1
  by_cases ho : o u.1 = u.2
  · by_cases hP : u.1 ∈ P
    · rw [Finset.sum_eq_single u.1]
      · simp [ho, hP]
      · intro a _ hne; simp [hne, bool_zero_eq_false]
      · intro habs; exact absurd hP habs
    · rw [Finset.sum_eq_zero]
      · simp [hP, bool_zero_eq_false]
      · intro a ha
        have hne : a ≠ u.1 := fun h => hP (h ▸ ha)
        simp [hne, bool_zero_eq_false]
  · rw [Finset.sum_eq_zero]
    · simp [ho, bool_zero_eq_false]
    · intro a _; simp [ho, bool_zero_eq_false]

/-- Server database update algorithm `UpdateDB(i, d; D)`
([Hoover, Patel, Persiano and Yeo, Definition 5.2 and Figure 7][HooverPatelPersianoYeo2025]):
when entry `i` is updated to new bit `d`, returns the update summary `δ = (i, db i + d)` together
with the updated database `Function.update db i d`. -/
@[expose] def updateDB (db : Fin c × Fin w → Bool) (i : Fin c × Fin w) (d : Bool) :
    ((Fin c × Fin w) × Bool) × (Fin c × Fin w → Bool) :=
  ((i, db i + d), Function.update db i d)

/-- Client hint update algorithm `UpdateHint(δ; st)` for an update summary `δ = (i, u)` where
`u : Bool` is the XOR delta at entry `i : Fin c × Fin w`
([Hoover, Patel, Persiano and Yeo, Definition 5.2 and Figure 7][HooverPatelPersianoYeo2025]):
1. Computes the candidate hint slots `cand := iF.inv (st.keys i.1) i.2` via the iPRF inverse.
2. For each slot `j ∈ cand`, flips the parity of `st.H j` if `i.1` lies in its base block set,
   and flips `parityIn` (if `i.1 ∈ B`) or `parityOut` (if `i.1 ∉ B`) of `st.T j`.
3. If `st.cache i = some (a, j')`, updates `st.cache i` to `some (u + a, j')` and (if `st.H j'` is
   still active as a promoted hint for `i`) flips its parity by `u`. -/
@[expose] def updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (st : PlinkoState c w nReg nBackup Key) :
    PlinkoState c w nReg nBackup Key :=
  let i := δ.1
  let u := δ.2
  let cand := iF.inv (st.keys i.1) i.2
  { keys := st.keys
    H := fun j =>
      match st.H j with
      | some (.regular P p) =>
        some (.regular P (if j ∈ cand ∧ i.1 ∈ P then u + p else p))
      | some (.promoted P y p) =>
        let p₁ := if j ∈ cand ∧ i.1 ∈ P then u + p else p
        let p₂ := if y = i then u + p₁ else p₁
        some (.promoted P y p₂)
      | none => none
    T := fun j =>
      match st.T j with
      | some ⟨B, p₁, p₂⟩ =>
        some ⟨B,
          if j ∈ cand ∧ i.1 ∈ B then u + p₁ else p₁,
          if j ∈ cand ∧ i.1 ∉ B then u + p₂ else p₂⟩
      | none => none
    cache := Function.update st.cache i ((st.cache i).map fun ak => (u + ak.1, ak.2)) }

/-- Applies a list of database XOR update summaries `updates : List ((Fin c × Fin w) × Bool)` to
`db`. -/
@[expose] def applyUpdates (updates : List ((Fin c × Fin w) × Bool))
    (db : Fin c × Fin w → Bool) : Fin c × Fin w → Bool :=
  updates.foldr (fun δ d => Function.update d δ.1 (δ.2 + d δ.1)) db

/-- Updates the client state `st` across a list of database XOR update summaries
`updates : List ((Fin c × Fin w) × Bool)`
([Hoover, Patel, Persiano and Yeo, Figure 7, `UpdateHint`][HooverPatelPersianoYeo2025]). -/
@[expose] def updateState (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (updates : List ((Fin c × Fin w) × Bool)) (st : PlinkoState c w nReg nBackup Key) :
    PlinkoState c w nReg nBackup Key :=
  updates.foldr (fun δ s => updateHint iF δ s) st

@[simp]
theorem applyUpdates_nil (db : Fin c × Fin w → Bool) :
    applyUpdates [] db = db := rfl

@[simp]
theorem applyUpdates_cons (δ : (Fin c × Fin w) × Bool) (updates : List ((Fin c × Fin w) × Bool))
    (db : Fin c × Fin w → Bool) :
    applyUpdates (δ :: updates) db =
      Function.update (applyUpdates updates db) δ.1 (δ.2 + applyUpdates updates db δ.1) := rfl

@[simp]
theorem updateState_nil (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) :
    updateState iF [] st = st := rfl

@[simp]
theorem updateState_cons (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (updates : List ((Fin c × Fin w) × Bool))
    (st : PlinkoState c w nReg nBackup Key) :
    updateState iF (δ :: updates) st = updateHint iF δ (updateState iF updates st) := rfl

namespace PlinkoState

@[simp]
theorem updateHint_keys (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (st : PlinkoState c w nReg nBackup Key) :
    (updateHint iF δ st).keys = st.keys :=
  rfl

@[simp]
theorem updateState_keys (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (updates : List ((Fin c × Fin w) × Bool)) (st : PlinkoState c w nReg nBackup Key) :
    (updateState iF updates st).keys = st.keys := by
  induction updates <;> simp [*]

private theorem bool_promoted_update_eq (d b₁ b₂ c₁ c₂ : Bool) :
    (if c₂ then d + (if c₁ then d + (b₁ + b₂) else b₁ + b₂)
     else if c₁ then d + (b₁ + b₂) else b₁ + b₂) =
      (if c₂ then d + b₁ else b₁) + ((if c₁ then d else false) + b₂) := by
  revert d b₁ b₂ c₁ c₂
  decide

/-- **Single-entry XOR-delta update preserves `PlinkoState.Valid`**
([Hoover, Patel, Persiano and Yeo, Figure 7, `UpdateHint`][HooverPatelPersianoYeo2025]): if
`st.Valid iF db` and `iF.IsCorrectKey (st.keys u.1)` hold, then `updateHint iF (u, d) st` is valid
for the updated database `Function.update db u (d + db u)`. -/
theorem valid_updateHint_delta {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    (u : Fin c × Fin w) (d : Bool) (hvalid : st.Valid iF db)
    (hcorr : iF.IsCorrectKey (st.keys u.1)) :
    (updateHint iF (u, d) st).Valid iF (Function.update db u (d + db u)) where
  valid_regular j P p' hH := by
    dsimp only [updateHint] at hH ⊢
    cases hHj : st.H j with
    | none => simp [hHj] at hH
    | some h =>
      cases h with
      | promoted _ _ _ => simp [hHj] at hH
      | regular P₀ p =>
        rw [hHj] at hH
        simp only [Option.some.injEq, ActiveHint.regular.injEq] at hH
        obtain ⟨rfl, rfl⟩ := hH
        have hp := hvalid.valid_regular j P₀ p hHj
        rw [blockParity_update_db, ← hp]
        simp only [hcorr j u.2]
        by_cases hcond : iF.eval (st.keys u.1) j = u.2 ∧ u.1 ∈ P₀ <;>
          simp [hcond, bool_false_add]
  valid_promoted j P y p' hH := by
    dsimp only [updateHint] at hH ⊢
    cases hHj : st.H j with
    | none => simp [hHj] at hH
    | some h =>
      cases h with
      | regular _ _ => simp [hHj] at hH
      | promoted P₀ y₀ p =>
        rw [hHj] at hH
        simp only [Option.some.injEq, ActiveHint.promoted.injEq] at hH
        obtain ⟨rfl, rfl, rfl⟩ := hH
        obtain ⟨hyP, hp, hcache⟩ := hvalid.valid_promoted j P₀ y₀ p hHj
        refine ⟨hyP, ?_, ?_⟩
        · rw [blockParity_update_db, hp]
          simp only [hcorr j u.2]
          have hyu : Function.update db u (d + db u) y₀ =
              if decide (y₀ = u) then d + db y₀ else db y₀ := by
            by_cases h : y₀ = u <;> simp [h]
          rw [hyu]
          simpa using bool_promoted_update_eq d (db y₀)
            (blockParity db P₀ (fun a => iF.eval (st.keys a) j))
            (decide (iF.eval (st.keys u.1) j = u.2 ∧ u.1 ∈ P₀)) (decide (y₀ = u))
        · by_cases hyu : y₀ = u
          · subst hyu; simp [hcache]
          · simp [Function.update_of_ne hyu, hcache]
  valid_backup j bk' hT := by
    dsimp only [updateHint] at hT ⊢
    cases hTj : st.T j with
    | none => simp [hTj] at hT
    | some bk =>
      rcases bk with ⟨B, p₁, p₂⟩
      rw [hTj] at hT
      simp only [Option.some.injEq] at hT
      subst hT
      obtain ⟨hin, hout, hHnone, hcache⟩ := hvalid.valid_backup j ⟨B, p₁, p₂⟩ hTj
      refine ⟨?_, ?_, by simp [hHnone], ?_⟩
      · dsimp only
        rw [blockParity_update_db, ← hin]
        simp only [hcorr j u.2]
        by_cases hcond : iF.eval (st.keys u.1) j = u.2 ∧ u.1 ∈ B <;>
          simp [hcond, bool_false_add]
      · dsimp only
        rw [blockParity_update_db, ← hout]
        simp only [hcorr j u.2, Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hcond : iF.eval (st.keys u.1) j = u.2 ∧ u.1 ∉ B <;>
          simp [hcond, bool_false_add]
      · intro x
        by_cases hxu : x = u
        · subst hxu
          have hmap : ((updateHint iF (x, d) st).cache x).map Prod.snd =
              (st.cache x).map Prod.snd := by
            dsimp only [updateHint]
            rw [Function.update_self]
            cases st.cache x <;> rfl
          exact hmap ▸ hcache x
        · simpa [Function.update_of_ne hxu] using hcache x
  valid_cache x a' j hC := by
    dsimp only [updateHint] at hC
    by_cases hxu : x = u
    · subst hxu
      simp only [Function.update_self, Option.map_eq_some_iff] at hC
      obtain ⟨⟨a, j₀⟩, hcx, hpair⟩ := hC
      simp only [Prod.mk.injEq] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      obtain ⟨rfl, hprom⟩ := hvalid.valid_cache x a j₀ hcx
      refine ⟨by simp, fun h' hh' => ?_⟩
      dsimp only [updateHint] at hh'
      cases hHj : st.H j₀ with
      | none => simp [hHj] at hh'
      | some h =>
        obtain ⟨P, p, rfl⟩ := hprom h hHj
        rw [hHj] at hh'
        simp only [Option.some.injEq] at hh'
        exact ⟨P, _, hh'.symm⟩
    · simp only [Function.update_of_ne hxu] at hC
      obtain ⟨rfl, hprom⟩ := hvalid.valid_cache x a' j hC
      refine ⟨by simp [Function.update_of_ne hxu], fun h' hh' => ?_⟩
      dsimp only [updateHint] at hh'
      cases hHj : st.H j with
      | none => simp [hHj] at hh'
      | some h =>
        obtain ⟨P, p, rfl⟩ := hprom h hHj
        rw [hHj] at hh'
        simp only [Option.some.injEq] at hh'
        exact ⟨P, _, hh'.symm⟩

/-- **Database and hint update correctness (`UpdateDB` / `UpdateHint`, Figure 7)**
([Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7][HooverPatelPersianoYeo2025]): if
`st.Valid iF db` and `iF.IsCorrectKey (st.keys i.1)` hold, updating entry `i` to new bit `d` via
summary `(i, db i + d) = (updateDB db i d).1` yields a client state valid for
`Function.update db i d = (updateDB db i d).2`. -/
theorem valid_updateHint {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    (i : Fin c × Fin w) (d : Bool) (hvalid : st.Valid iF db)
    (hcorr : iF.IsCorrectKey (st.keys i.1)) :
    (updateHint iF (i, db i + d) st).Valid iF (Function.update db i d) := by
  have hcancel : (db i + d) + db i = d := by
    rw [add_comm (db i) d, bool_add_add_cancel]
  simpa [hcancel] using valid_updateHint_delta i (db i + d) hvalid hcorr

/-- `updateHint` preserves `slotMatchesBlock` at every slot `j` and query `x`. -/
@[simp]
theorem slotMatchesBlock_updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (j : Fin (nReg + nBackup)) :
    slotMatchesBlock iF (updateHint iF δ st) x j = slotMatchesBlock iF st x j := by
  dsimp only [slotMatchesBlock, updateHint]
  cases hHj : st.H j with
  | none => rfl
  | some h =>
    cases h <;> dsimp only [extractActiveHint] <;> split_ifs <;> rfl

/-- `updateHint` preserves `findHintSlot` for every query `x`. -/
@[simp]
theorem findHintSlot_updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    findHintSlot iF (updateHint iF δ st) x = findHintSlot iF st x := by
  simp [findHintSlot]

/-- `updateHint` preserves `findBackupSlot`. -/
@[simp]
theorem findBackupSlot_updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (st : PlinkoState c w nReg nBackup Key) :
    findBackupSlot (updateHint iF δ st).T = findBackupSlot st.T := by
  have hpred : (fun j : Fin (nReg + nBackup) => ((updateHint iF δ st).T j).isSome) =
      (fun j : Fin (nReg + nBackup) => (st.T j).isSome) := by
    funext j
    dsimp only [updateHint]
    cases st.T j <;> rfl
  simp [findBackupSlot, hpred]

/-- `updateHint` preserves `CanAnswer` for every query `x`. -/
@[simp]
theorem canAnswer_updateHint_iff (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : (Fin c × Fin w) × Bool) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    (updateHint iF δ st).CanAnswer iF x ↔ st.CanAnswer iF x := by
  have hcache : ((updateHint iF δ st).cache x).isSome = (st.cache x).isSome := by
    dsimp only [updateHint]
    by_cases hxu : x = δ.1
    · subst hxu
      simp only [Function.update_self]
      cases st.cache δ.1 <;> rfl
    · simp [Function.update_of_ne hxu]
  have hget : (getHint iF (updateHint iF δ st) x).isSome = (getHint iF st x).isSome := by
    dsimp only [getHint]
    rw [findHintSlot_updateHint]
    cases hfind : findHintSlot iF st x with
    | none => rfl
    | some j =>
      dsimp only [updateHint]
      cases hHj : st.H j with
      | none => rfl
      | some h =>
        cases h <;> dsimp only [extractActiveHint] <;> split_ifs <;> rfl
  simp [CanAnswer, hcache, hget, findBackupSlot_updateHint]

/-- **Batch database update (`UpdateHint`, Figure 7) preserves `PlinkoState.Valid`**
([Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]): if `st.Valid iF db`
and `∀ α, iF.IsCorrectKey (st.keys α)` hold, then `updateState iF updates st` is valid for
`applyUpdates updates db`. -/
theorem valid_updateState {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    (updates : List ((Fin c × Fin w) × Bool)) (hvalid : st.Valid iF db)
    (hcorr : ∀ α : Fin c, iF.IsCorrectKey (st.keys α)) :
    (updateState iF updates st).Valid iF (applyUpdates updates db) := by
  induction updates with
  | nil => exact hvalid
  | cons δ updates ih =>
    simp only [updateState_cons, applyUpdates_cons]
    refine valid_updateHint_delta δ.1 δ.2 ih ?_
    rw [updateState_keys]
    exact hcorr δ.1.1

/-- `updateState` preserves `CanAnswer` for every query `x`. -/
@[simp]
theorem canAnswer_updateState_iff (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (updates : List ((Fin c × Fin w) × Bool)) (st : PlinkoState c w nReg nBackup Key)
    (x : Fin c × Fin w) :
    (updateState iF updates st).CanAnswer iF x ↔ st.CanAnswer iF x := by
  induction updates <;> simp [*]

end PlinkoState

end Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko

end
