/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Invertible
public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Basic
public import CslibFrontier.Languages.Probabilistic.Vector
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Finset.Sort
import CslibFrontier.Foundations.Data.Finset.OrderedFilter
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.Finset.Powerset

/-!
# The Plinko client-preprocessing single-server PIR scheme

This module formalizes the deterministic and structural core of the Plinko updateable
client-preprocessing single-server PIR scheme of
[Hoover, Patel, Persiano and Yeo][HooverPatelPersianoYeo2025] (Section 5 and Appendix A, Figure 7).

A database `db : Fin c × Fin w → Bool` of `n = c * w` bits is partitioned into `c` blocks of size
`w`. The client maintains `nReg` regular hint slots and `nBackup` backup/promoted hint slots,
indexed by `Fin (nReg + nBackup)`, together with one invertible PRF key `keys α : Key` per block
`α : Fin c` for an iPRF `iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)`.

* **Hint lookup via iPRF inversion** (`getHint`, `getHintScan`, `getHint_eq_getHintScan`):
  to find an active hint containing `x = (α, β)`, `getHint` inverts `iF` at `(keys α, β)` to obtain
  the candidate slot set `iF.inv (keys α) β` and selects the smallest matching active slot.
  When `iF.IsCorrectKey (keys α)` holds, `getHint` returns the exact same hint as a full linear scan
  `getHintScan` over all `nReg + nBackup` slots.
* **Offline single-pass entry streaming** (`initPlinkoState`, `streamEntry`, `streamPreprocess`,
  `foldr_streamEntry_univ`, `PlinkoState.valid_streamPreprocess`): streaming each database entry
  `x = (α, β)` once and updating only the slots in `iF.inv (keys α) β` establishes the parity and
  cache validity invariant `PlinkoState.Valid`.
* **Online query, answer, reconstruction, and backup promotion** (`buildQuery`, `plinkoAnswer`,
  `plinkoReconstruct`, `plinkoScheme`, `PlinkoState.eval_step_plinkoScheme`,
  `PlinkoState.isCorrectFrom_plinkoScheme_of_canAnswerSeq`): on an uncached query `x = (α, β)`,
  the client removes `α` from the matched `(c / 2 + 1)`-block set `P` to obtain
  `P' = P.erase α`, randomly sends either `P'` or `Finset.univ \ P'` according to a fair coin
  `b : Bool`, replaces `α`'s offset with a random offset `r : Fin w`, reconstructs
  `db x = p + r_b`, consumes the matched hint, promotes the next backup hint `T[j']` into `H[j']`,
  and caches `(db x, j')` in `cache x`. Under `Valid` and `CanAnswerSeq`, `plinkoScheme` satisfies
  `Scheme.IsCorrectFrom` and preserves `Valid` across both the promotion and cache paths.
* **The query map and an idealized stand-in** (`eval_buildQuery_conditioned_eq_plinkoSim`,
  `plinkoHybridScheme`, `isPerfectlyPrivateWith_plinkoHybridScheme`): when `Even c`, `buildQuery`
  sends a uniform regular hint conditioned on containing `x = (α, β)`, together with a uniform coin
  and replacement offset, to the simulator distribution `plinkoSim c w` (a uniform
  `(c / 2)`-subset of blocks with independent uniform offsets). This is a fact about the query map
  under an assumed hint law; the law of the hints that `plinkoScheme` consumes is not analysed.
  The idealized stand-in `plinkoHybridScheme` has no iPRF, no keys and no hint table, keeps `db` in
  its state and draws a fresh conditioned hint for each query; it is perfectly private against
  adaptive servers. Neither result is privacy of `plinkoScheme` or the paper's computational privacy
  claim (#5736).
* **Database and hint updates** (`updateDB`, `updateHint`, `updateState`,
  `PlinkoState.valid_updateHint_delta`, `PlinkoState.valid_updateHint`,
  `PlinkoState.valid_updateState`, `PlinkoState.canAnswer_updateHint_iff`):
  updating entry `i = (α, β)` to `d` via summary `δ = ⟨i, db i + d⟩` touches three things: the
  candidate slots in `iF.inv (keys α) β`, the active promoted hint linked to the cached entry
  (its stored entry is `i`, and its slot need not be a candidate), and the cache entry `cache i`.
  It preserves `PlinkoState.Valid` against `Function.update db i d` as well as
  `PlinkoState.CanAnswer`.

## Main definitions

* `blockParity`, `PlinkoQuery`, `buildQuery`, `plinkoAnswer`, `plinkoReconstruct`:
  block-offset parities, online query construction, server answer, and client reconstruction.
* `ActiveHint`, `BackupHint`, `PlinkoState`, `ExtractedHint`, `MatchedHint`, `getHint`,
  `getHintScan`: client hint state and hint lookup via iPRF inversion (`iF.inv`) vs. linear scan.
* `initPlinkoState`, `streamEntry`, `streamPreprocess`:
  offline single-pass entry streaming (`HintInit`).
* `refreshPlinkoState`, `PlinkoState.Valid`, `PlinkoState.CanAnswer`, `PlinkoState.CanAnswerSeq`,
  `PlinkoState.nextState`: online backup promotion, state validity invariant, and answerability.
* `plinkoSim`, `plinkoScheme`, `plinkoHybridScheme`: simulator, full Plinko `Scheme`, and an
  idealized stand-in `Scheme` with no iPRF, keys or hint table (#5736).
* `queryBlocksEquiv`, `queryOffsetsEquiv`: bijections that decompose a query message.
* `UpdateSummary`, `updateDB`, `updateHint`, `applyUpdates`, `updateState`: update summaries and
  the database and hint update algorithms (Definition 5.2 and Figure 7).

## Main results

* `plinkoReconstruct_plinkoAnswer_eq`: online reconstruction identity.
* `findHintSlot_eq_findHintSlotScan`, `getHint_eq_getHintScan`: equivalence of `getHint` via
  `iF.inv` and `getHintScan`.
* `foldr_streamEntry_univ`, `PlinkoState.valid_streamPreprocess`: offline streaming correctness.
* `PlinkoState.Valid.getHint_spec`, `PlinkoState.valid_nextState`,
  `PlinkoState.eval_step_plinkoScheme`, `PlinkoState.isCorrectFrom_plinkoScheme_of_canAnswerSeq`:
  matched-hint specification, online state-validity preservation, and multi-query correctness of
  `plinkoScheme` under the availability condition `CanAnswerSeq`.
* `PlinkoState.valid_of_mem_support_preprocess`: every preprocessed state is `Valid`, with
  inversion-correct keys when `iF.IsCorrectOnGen` holds.
* `eval_buildQuery_conditioned_eq_plinkoSim`: the query map sends a uniform regular hint
  conditioned on containing `x` to `plinkoSim c w`.
* `isPerfectlyPrivateWith_plinkoHybridScheme`, `eval_queryTranscript_plinkoHybridScheme`: perfect
  privacy and transcript uniformity of the idealized stand-in `plinkoHybridScheme` (not privacy of
  `plinkoScheme`, #5736).
* `PlinkoState.valid_updateHint_delta`, `PlinkoState.valid_updateHint`,
  `PlinkoState.valid_updateState`, `PlinkoState.canAnswer_updateHint_iff`: hint update correctness.

## What is not proved

* Full-client privacy, iPRF/PMNS security, and the asymptotic efficiency and failure bounds of
  Theorem 5.3 are open (#5736). Perfect privacy is proved only for the idealized stand-in
  `plinkoHybridScheme`, which has no iPRF, no keys and no hint table: every query draws a fresh
  regular hint conditioned on containing the queried index. The paper's argument that the hint table
  stays uniform after hints are consumed and backups promoted is not formalized, and nothing about
  privacy is proved for `plinkoScheme` (#5736). Its `getHint` takes the smallest matching candidate
  slot, which conditions the remaining slots, and the paper argues privacy computationally by appeal
  to Ren, Mughees, and Sun (2024) and forward iPRF security (Section 5.2, p. 23). No iPRF security
  notion is defined here.
* The Chernoff load bound on `|iF.inv (keys α) β|` (Section 5.2, p. 23), the failure-probability
  bound for `CanAnswerSeq`, amortized re-streaming after `nBackup` queries, the Appendix B
  Plinko–Piano variant (Figure 8), `B`-bit entries, the FHE offline phase, and the asymptotic
  runtime/storage bounds of Theorem 5.3 are not formalized (#5736).

## Modelling choices

* Figure 7 `GetHint` scans the candidate slots `iF.inv (K[α], β)` in random order, and Section 5.2
  (p. 22) picks a random unused hint. `getHint` instead returns the smallest matching slot. The
  correctness and update results do not depend on this choice (#5736).
* On a repeated (cached) query, Figure 7 `Query` issues a real query for a fresh random index that
  has not been queried before, consuming and promoting a hint for it. `plinkoScheme` instead sends
  a dummy message drawn from `plinkoSim` and leaves the hint state unchanged; the cached bit is
  returned in both cases (#5736).
* If no matching hint or no backup hint is left, the paper's scheme has failed. `plinkoScheme` then
  sends a dummy message and its output is unspecified; correctness is only claimed under
  `PlinkoState.CanAnswerSeq`.
* Regular and backup block sets are sampled for every slot, and `streamPreprocess` uses the regular
  set only in slots `j < nReg` and the backup set only in slots `j ≥ nReg`.

## References

* [A. Hoover, S. Patel, G. Persiano, K. Yeo, *Plinko: Single-Server PIR with Efficient Updates via
  Invertible PRFs*][HooverPatelPersianoYeo2025], Section 5 (Definitions 5.1–5.2, Figure 5, and
  Theorem 5.3) and Appendix A (p. 30; Figure 7, p. 31; locators follow IACR ePrint 2024/318).
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

private theorem blockParity_erase_add (db : Fin c × Fin w → Bool) {P : Finset (Fin c)} {α : Fin c}
    (hα : α ∈ P) (o : Fin c → Fin w) :
    db (α, o α) + blockParity db (P.erase α) o = blockParity db P o :=
  Finset.add_sum_erase P (fun a => db (a, o a)) hα

private theorem blockParity_insert_of_notMem (db : Fin c × Fin w → Bool) {P : Finset (Fin c)}
    {α : Fin c} (hα : α ∉ P) (o : Fin c → Fin w) :
    blockParity db (insert α P) o = db (α, o α) + blockParity db P o :=
  Finset.sum_insert hα

private theorem blockParity_update_of_notMem (db : Fin c × Fin w → Bool) {P : Finset (Fin c)}
    {α : Fin c} (hα : α ∉ P) (o : Fin c → Fin w) (β : Fin w) :
    blockParity db P (Function.update o α β) = blockParity db P o :=
  Finset.sum_congr rfl fun a ha => by simp [show a ≠ α from fun h => hα (h ▸ ha)]

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
    (r : Fin w) : PlinkoQuery c w :=
  ⟨if b then Finset.univ \ P.erase x.1 else P.erase x.1, Function.update o x.1 r⟩

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

/-- Online reconstruction identity
([Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7, `Recon`][HooverPatelPersianoYeo2025]):
if `(P, o)` contains `x` (`x.1 ∈ P` and `o x.1 = x.2`), then XORing the hint parity
`blockParity db P o` with the `b`-th server parity from `plinkoAnswer db (buildQuery x P o b r)`
recovers `db x`. -/
theorem plinkoReconstruct_plinkoAnswer_eq (db : Fin c × Fin w → Bool) (x : Fin c × Fin w)
    (P : Finset (Fin c)) (o : Fin c → Fin w) (b : Bool) (r : Fin w)
    (hP : x.1 ∈ P) (ho : o x.1 = x.2) :
    plinkoReconstruct (blockParity db P o) b (plinkoAnswer db (buildQuery x P o b r)) = db x := by
  have hsel : (if b then (plinkoAnswer db (buildQuery x P o b r)).2
      else (plinkoAnswer db (buildQuery x P o b r)).1) = blockParity db (P.erase x.1) o := by
    cases b <;>
      simp [plinkoAnswer, buildQuery, blockParity_update_of_notMem db (Finset.notMem_erase x.1 P)]
  rw [plinkoReconstruct, hsel, ← blockParity_erase_add db hP o, ho, Prod.mk.eta, add_assoc,
    BooleanRing.add_self, add_zero]

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

/-- The effective block set, parity and offset vector of an active hint that contains a queried
index, as returned by `extractActiveHint`. -/
@[ext]
structure ExtractedHint (c w : ℕ) where
  /-- Effective block set of the hint (for a promoted hint, its base set plus the promoted
  block). -/
  blocks : Finset (Fin c)
  /-- Stored parity of the hint. -/
  parity : Bool
  /-- Offset of the hint in each block. -/
  offsets : Fin c → Fin w
  deriving DecidableEq

/-- A hint found by `getHint` or `getHintScan`: the slot `j` it occupies in the table `H`,
together with its effective block set, parity and offset vector. -/
@[ext]
structure MatchedHint (c w N : ℕ) where
  /-- Slot of the matched hint in the table `H`. -/
  slot : Fin N
  /-- Effective block set of the hint. -/
  blocks : Finset (Fin c)
  /-- Stored parity of the hint. -/
  parity : Bool
  /-- Offset of the hint in each block. -/
  offsets : Fin c → Fin w
  deriving DecidableEq

/-- Checks whether an active hint `h : ActiveHint c w` at slot `j` contains block `x.1` (compatible
with offset `x.2` at `x.1` when `iF.eval (keys x.1) j = x.2`) and returns its effective block set,
parity, and offset vector
([Hoover, Patel, Persiano and Yeo, Figure 7, `GetHint`][HooverPatelPersianoYeo2025]). -/
@[expose] def extractActiveHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (keys : Fin c → Key) (j : Fin (nReg + nBackup)) (h : ActiveHint c w) (x : Fin c × Fin w) :
    Option (ExtractedHint c w) :=
  let o : Fin c → Fin w := fun a => iF.eval (keys a) j
  match h with
  | .regular P p =>
    if x.1 ∈ P then some ⟨P, p, o⟩ else none
  | .promoted P y p =>
    if (x.1 = y.1 ∧ x.2 = y.2) ∨ (x.1 ≠ y.1 ∧ x.1 ∈ P) then
      some ⟨insert y.1 P, p, Function.update o y.1 y.2⟩
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
([Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]): finds the smallest
candidate slot `j ∈ iF.inv (st.keys x.1) x.2` with a matching active hint and returns
the matched hint. Figure 7 scans the candidates in random order instead; see the module
docstring (#5736). -/
@[expose] def getHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    Option (MatchedHint c w (nReg + nBackup)) := do
  let j ← findHintSlot iF st x
  let h ← st.H j
  let t ← extractActiveHint iF st.keys j h x
  pure ⟨j, t.blocks, t.parity, t.offsets⟩

/-- Linear-scan counterpart of `getHint` scanning all `nReg + nBackup` slots via forward
evaluations `iF.eval`. -/
@[expose] def getHintScan (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    Option (MatchedHint c w (nReg + nBackup)) := do
  let j ← findHintSlotScan iF st x
  let h ← st.H j
  let t ← extractActiveHint iF st.keys j h x
  pure ⟨j, t.blocks, t.parity, t.offsets⟩

/-- Algorithmic equivalence of `findHintSlot` and linear scan
([Hoover, Patel, Persiano and Yeo, Section 5.2, p. 21][HooverPatelPersianoYeo2025]): when
`iF.IsCorrectKey (st.keys x.1)` holds, `findHintSlot` via `iF.inv` returns the exact same slot as
the full linear scan `findHintSlotScan` over `Fin (nReg + nBackup)`. -/
theorem findHintSlot_eq_findHintSlotScan
    {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (hcorr : iF.IsCorrectKey (st.keys x.1)) :
    findHintSlot iF st x = findHintSlotScan iF st x := by
  rw [findHintSlot, findHintSlotScan, Finset.sort_eq_filter_finRange, List.find?_filter]
  congr 1; funext j
  simp [hcorr j x.2]

/-- When `iF.IsCorrectKey (st.keys x.1)` holds, `getHint` via `iF.inv` returns the exact same
matched hint as `getHintScan`. -/
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
    PlinkoState c w nReg nBackup Key :=
  let cand := iF.inv (st.keys x.1) x.2
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

private def streamUpTo (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
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

private theorem streamUpTo_empty (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    streamUpTo iF db ∅ keys regBlocks backupBlocks =
      initPlinkoState keys regBlocks backupBlocks := by
  ext <;> simp [streamUpTo, initPlinkoState, ← Bool.zero_eq_false]

private theorem streamUpTo_univ (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    streamUpTo iF db Finset.univ keys regBlocks backupBlocks =
      streamPreprocess iF db keys regBlocks backupBlocks := by
  ext <;> simp [streamUpTo, streamPreprocess, blockParity]

/-- Indicator sum over `a ∈ P` for `(a, o a) = x`. -/
private theorem sum_ite_pair_eq (P : Finset (Fin c)) (o : Fin c → Fin w) (x : Fin c × Fin w)
    (v : Bool) :
    (∑ a ∈ P, if (a, o a) = x then v else false) =
      if o x.1 = x.2 ∧ x.1 ∈ P then v else false := by
  rcases x with ⟨α, β⟩
  have hcongr : ∀ a ∈ P, (if (a, o a) = (α, β) then v else false) =
      if a = α then (if o α = β then v else 0) else 0 := fun a _ => by
    by_cases ha : a = α <;> simp [ha, ← Bool.zero_eq_false]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
  by_cases hP : α ∈ P <;> by_cases ho : o α = β <;> simp [hP, ho, ← Bool.zero_eq_false]

private theorem sum_ite_mem_insert (db : Fin c × Fin w → Bool)
    (o : Fin c → Fin w) (P : Finset (Fin c)) {s : Finset (Fin c × Fin w)} {x : Fin c × Fin w}
    (hx : x ∉ s) :
    (∑ a ∈ P, if (a, o a) ∈ insert x s then db (a, o a) else false) =
      (if o x.1 = x.2 ∧ x.1 ∈ P then db x else false) +
        ∑ a ∈ P, if (a, o a) ∈ s then db (a, o a) else false := by
  have hpoint : ∀ a ∈ P,
      (if (a, o a) ∈ insert x s then db (a, o a) else false) =
        (if (a, o a) = x then db x else false) +
          (if (a, o a) ∈ s then db (a, o a) else false) := fun a _ => by
    by_cases hax : (a, o a) = x
    · simp [hax, hx, ← Bool.zero_eq_false]
    · simp [Finset.mem_insert, hax, ← Bool.zero_eq_false]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, sum_ite_pair_eq]

private theorem streamEntry_streamUpTo {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
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
        simp [hj, hev, hP, ← Bool.zero_eq_false]
    · simp [hj]
  · simp only [streamEntry, streamUpTo, hcorr j x.2]
    by_cases hj : j.val < nReg
    · simp [hj]
    · rw [sum_ite_mem_insert db (fun a => iF.eval (keys a) j) (backupBlocks j) hx,
        sum_ite_mem_insert db (fun a => iF.eval (keys a) j) (Finset.univ \ backupBlocks j) hx]
      by_cases hev : iF.eval (keys x.1) j = x.2 <;> by_cases hB : x.1 ∈ backupBlocks j <;>
        simp [hj, hev, hB, ← Bool.zero_eq_false]
  · rfl

private theorem foldr_streamEntry_eq_streamUpTo
    {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (hcorr : ∀ α : Fin c, iF.IsCorrectKey (keys α))
    {xs : List (Fin c × Fin w)} (hnd : xs.Nodup) :
    xs.foldr (fun x st => streamEntry iF x (db x) st)
      (initPlinkoState keys regBlocks backupBlocks) =
      streamUpTo iF db xs.toFinset keys regBlocks backupBlocks := by
  induction xs with
  | nil => simp [streamUpTo_empty]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    have hx : x ∉ xs.toFinset := by simpa using hnd.1
    simp only [List.foldr_cons, ih hnd.2, List.toFinset_cons,
      streamEntry_streamUpTo db hx keys regBlocks backupBlocks (hcorr x.1)]

/-- Offline single-pass entry streaming correctness
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

/-- Offline preprocessing produces a valid state
([Hoover, Patel, Persiano and Yeo, Figure 7, `HintInit`][HooverPatelPersianoYeo2025]). -/
theorem valid_streamPreprocess (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key)
    (regBlocks : Fin (nReg + nBackup) → Finset (Fin c))
    (backupBlocks : Fin (nReg + nBackup) → Finset (Fin c)) :
    Valid iF db (streamPreprocess iF db keys regBlocks backupBlocks) where
  valid_regular j P p hH := by
    simp only [streamPreprocess] at hH
    split_ifs at hH
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
    exact ⟨rfl, rfl, by simp [hj], fun _ => by simp⟩
  valid_cache _ _ _ hC := by simp [streamPreprocess] at hC

/-- If `getHint iF st x = some ⟨j, P, p, o⟩` on a valid state `st` and
`iF.IsCorrectKey (st.keys x.1)` holds, then `st.H j ≠ none`, `x.1 ∈ P`, `o x.1 = x.2`, and
`p = blockParity db P o`. -/
theorem Valid.getHint_spec {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key} {x : Fin c × Fin w}
    {j : Fin (nReg + nBackup)} {P : Finset (Fin c)} {p : Bool} {o : Fin c → Fin w}
    (hvalid : st.Valid iF db) (hcorr : iF.IsCorrectKey (st.keys x.1))
    (hget : getHint iF st x = some ⟨j, P, p, o⟩) :
    st.H j ≠ none ∧ x.1 ∈ P ∧ o x.1 = x.2 ∧ p = blockParity db P o := by
  simp only [getHint, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, MatchedHint.mk.injEq] at hget
  obtain ⟨j₀, hfind, h, hH, ⟨P_t, p_t, o_t⟩, hext, rfl, rfl, rfl, rfl⟩ := hget
  have hj₀_eval : iF.eval (st.keys x.1) j₀ = x.2 :=
    (hcorr j₀ x.2).mp ((Finset.mem_sort (· ≤ ·)).mp (List.mem_of_find?_eq_some hfind))
  cases h with
  | regular P₀ p₀ =>
    simp only [extractActiveHint] at hext
    split_ifs at hext with hxP₀
    simp only [Option.some.injEq, ExtractedHint.mk.injEq] at hext
    obtain ⟨rfl, rfl, rfl⟩ := hext
    exact ⟨by simp [hH], hxP₀, hj₀_eval, hvalid.valid_regular j₀ P₀ p₀ hH⟩
  | promoted P₀ y p₀ =>
    simp only [extractActiveHint] at hext
    split_ifs at hext with hcond
    simp only [Option.some.injEq, ExtractedHint.mk.injEq] at hext
    obtain ⟨rfl, rfl, rfl⟩ := hext
    obtain ⟨hyP₀, hp₀, -⟩ := hvalid.valid_promoted j₀ P₀ y p₀ hH
    have hpar : p₀ = blockParity db (insert y.1 P₀)
        (Function.update (fun a => iF.eval (st.keys a) j₀) y.1 y.2) := by
      rw [blockParity_insert_of_notMem db hyP₀, Function.update_self, Prod.mk.eta,
        blockParity_update_of_notMem db hyP₀, hp₀]
    rcases hcond with ⟨hx1, hx2⟩ | ⟨hne, hxP₀⟩
    · refine ⟨by simp [hH], by simp [hx1], ?_, hpar⟩
      dsimp only; rw [hx1, Function.update_self, hx2]
    · refine ⟨by simp [hH], Finset.mem_insert_of_mem hxP₀, ?_, hpar⟩
      dsimp only; rw [Function.update_of_ne hne, hj₀_eval]

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
     if (st.cache x).isSome then none else (getHint iF st x).map MatchedHint.slot,
     false, false⟩
    (db x)

@[simp]
theorem refreshPlinkoState_keys (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (rec : PlinkoQueryRecord nReg nBackup) (a : Bool) :
    (refreshPlinkoState st x rec a).keys = st.keys := by
  dsimp only [refreshPlinkoState]
  cases rec.cachedBit
  · cases rec.matchedSlot
    · rfl
    · cases findBackupSlot st.T with
      | none => rfl
      | some j' => dsimp only; cases st.T j' <;> rfl
  · rfl

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

/-- Preservation of `Valid` under `nextState`
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
      obtain ⟨bk, hbk⟩ := Option.isSome_iff_exists.mp
        (by simpa [findBackupSlot] using List.find?_some hbak)
      obtain ⟨hHj_ne, -, -, -⟩ := hvalid.getHint_spec hcorr hget
      obtain ⟨hbk_in, hbk_out, hHj'_none, hcache_j'⟩ := hvalid.valid_backup j' bk hbk
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
        refine ⟨hin, hout,
          by simp [Function.update_of_ne hkj', Function.update_of_ne hkj, hHk_none], fun y => ?_⟩
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

/-! ### Block-set subtypes, simulator, and `plinkoScheme` -/

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

/-- `Preprocessing.Scheme` packaging of Plinko
([Hoover, Patel, Persiano and Yeo, Figure 7][HooverPatelPersianoYeo2025]). `HintInit` samples one
key per block from `iF.gen` (`OracleComp.replicateFin c iF.gen`), a uniform `(c / 2 + 1)`-block
regular set and a uniform `(c / 2)`-block backup set per slot, and computes the parities with
`streamPreprocess`. Two online steps depart from Figure 7 (#5736): `getHint` takes the smallest
matching slot instead of a random one, and a cached query sends a dummy `plinkoSim` message instead
of querying a fresh index. -/
@[expose] noncomputable def plinkoScheme (c w nReg nBackup : ℕ) [NeZero w]
    (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)) :
    Scheme (Fin c × Fin w) (PlinkoState c w nReg nBackup Key)
      (PlinkoQueryRecord nReg nBackup) (PlinkoQuery c w) (Bool × Bool) where
  preprocess db := do
    let keys ← OracleComp.replicateFin c iF.gen
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
      | some ⟨j, P, p, o⟩ =>
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

variable [NeZero w]

/-- Every state in the support of `(plinkoScheme c w nReg nBackup iF).preprocess db` is `Valid` for
`db`, and when `iF.IsCorrectOnGen` holds every block key is inversion-correct. -/
theorem valid_of_mem_support_preprocess
    {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)} {db : Fin c × Fin w → Bool}
    {st : PlinkoState c w nReg nBackup Key}
    (hmem : st ∈ (ProbComp.eval ((plinkoScheme c w nReg nBackup iF).preprocess db)).support) :
    st.Valid iF db ∧ (iF.IsCorrectOnGen → ∀ α : Fin c, iF.IsCorrectKey (st.keys α)) := by
  supp_cases hmem [plinkoScheme] with ⟨keys, hkeys, regB, bakB, rfl⟩
  exact ⟨valid_streamPreprocess iF db keys _ _,
    fun hgen α => hgen (keys α) ((ProbComp.mem_support_replicateFin_iff c iF.gen keys).mp hkeys α)⟩

/-- Single-step exact evaluation of `plinkoScheme`: when `st.Valid iF db`, `st.CanAnswer iF x`, and
`iF.IsCorrectKey (st.keys x.1)` hold, one honest online step of `plinkoScheme` outputs
`(st.nextState iF db x, db x)` with probability one. -/
theorem eval_step_plinkoScheme {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key} {x : Fin c × Fin w}
    (hvalid : st.Valid iF db) (hcorr : iF.IsCorrectKey (st.keys x.1))
    (hcan : st.CanAnswer iF x) :
    ProbComp.eval ((plinkoScheme c w nReg nBackup iF).step db st x) =
      PMF.pure (st.nextState iF db x, db x) := by
  have hsupp : ∀ p ∈ (ProbComp.eval ((plinkoScheme c w nReg nBackup iF).step db st x)).support,
      p = (st.nextState iF db x, db x) := by
    rintro ⟨st', β⟩ hmem
    cases hcache : st.cache x with
    | some cj =>
      supp_cases hmem [Scheme.step, plinkoScheme, hcache]
      obtain ⟨hadb, -⟩ := hvalid.valid_cache x cj.1 cj.2 hcache
      simp [nextState, refreshPlinkoState, hcache, hadb]
    | none =>
      rcases hcan with hc | ⟨hget_some, _⟩
      · simp [hcache] at hc
      · obtain ⟨⟨j, P, p, o⟩, hget⟩ := Option.isSome_iff_exists.mp hget_some
        obtain ⟨-, hxP, hox, hp⟩ := hvalid.getHint_spec hcorr hget
        supp_cases hmem [Scheme.step, plinkoScheme, hcache, hget]
        simp [nextState, refreshPlinkoState, hcache, hget, hp,
          plinkoReconstruct_plinkoAnswer_eq db x P o _ _ hxP hox]
  simpa only [PMF.map_id, PMF.map_const] using
    Cslib.Probability.PMF.map_congr_on_support
      (ProbComp.eval ((plinkoScheme c w nReg nBackup iF).step db st x))
      id (Function.const _ (st.nextState iF db x, db x)) hsupp

/-- Conditional multi-query correctness of `plinkoScheme` under `CanAnswerSeq` (deterministic
availability core of [Hoover, Patel, Persiano and Yeo, Section 5.2 and
Figure 7][HooverPatelPersianoYeo2025]; the `CanAnswerSeq` failure-probability bound is open in
#5736): if `st.Valid iF db`, `∀ α, iF.IsCorrectKey (st.keys α)`, and `st.CanAnswerSeq iF db xs`
hold, then `(plinkoScheme c w nReg nBackup iF).IsCorrectFrom db st xs` holds, and every hint state
reached after `xs` satisfies `Valid iF db`. -/
theorem isCorrectFrom_plinkoScheme_of_canAnswerSeq
    {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
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
    supp_cases hmem [Scheme.runQueriesFrom]
    exact hvalid
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hcan
    obtain ⟨hcorr_tail, hvalid_tail⟩ :=
      ih (valid_nextState hvalid (hcorr x.1) hx) (by simpa using hcorr) hxs
    have hstep := eval_step_plinkoScheme hvalid (hcorr x.1) hx
    refine ⟨Scheme.isCorrectFrom_cons fun st₁ β hmem₁ => ?_, fun st'' βs hmem => ?_⟩
    · supp_cases hmem₁ [hstep]
      exact ⟨rfl, hcorr_tail⟩
    · supp_cases hmem [Scheme.runQueriesFrom, hstep] with ⟨⟨_, βs'⟩, hmem₂, rfl, -⟩
      exact hvalid_tail st'' βs' hmem₂

end PlinkoState

/-! ### Bijective query decompositions and idealized stand-in privacy -/

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
    · simp [Finset.notMem_erase α P, Finset.insert_erase hαP]
    · simp [Finset.insert_erase hαP]
  right_inv := by
    rintro ⟨S, hcard⟩
    apply Subtype.ext
    by_cases hα : α ∈ S
    · simp [hα, Finset.erase_insert (show α ∉ Finset.univ \ S by simp [hα])]
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
    refine Prod.ext (Subtype.ext ?_) (by simp)
    simp only [Function.update_idem, ← ho, Function.update_eq_self]
  right_inv q := by ext a; simp

private theorem uniformOfFintype_bind_buildQuery {c w : ℕ} [Fact (Even c)] [NeZero w]
    {ε : Type*} (x : Fin c × Fin w) (k : PlinkoQuery c w → PMF ε) :
    ((PMF.uniformOfFintype (RegBlocksContaining c x.1)).bind fun P =>
      (PMF.uniformOfFintype (OffsetsContaining c w x)).bind fun o =>
        (PMF.uniformOfFintype Bool).bind fun b =>
          (PMF.uniformOfFintype (Fin w)).bind fun r =>
            k (buildQuery x P.1 o.1 b r)) =
      (ProbComp.eval (plinkoSim c w)).bind k := by
  have hcomm (P : RegBlocksContaining c x.1) :
      ((PMF.uniformOfFintype (OffsetsContaining c w x)).bind fun o =>
        (PMF.uniformOfFintype Bool).bind fun b =>
          (PMF.uniformOfFintype (Fin w)).bind fun r =>
            k (buildQuery x P.1 o.1 b r)) =
      (PMF.uniformOfFintype Bool).bind fun b =>
        (PMF.uniformOfFintype (Fin c → Fin w)).bind fun o' =>
          k ⟨(queryBlocksEquiv Fact.out x.1 (P, b)).1, o'⟩ := by
    rw [PMF.bind_comm]
    congr 1; funext b
    exact Cslib.Probability.PMF.uniformOfFintype_bind_bind_equiv (queryOffsetsEquiv x)
      (fun o' => k ⟨(queryBlocksEquiv Fact.out x.1 (P, b)).1, o'⟩)
  simp only [plinkoSim, ProbComp.eval_uniform, pmf_norm]
  trans ((PMF.uniformOfFintype (RegBlocksContaining c x.1)).bind fun P =>
    (PMF.uniformOfFintype Bool).bind fun b =>
      (PMF.uniformOfFintype (Fin c → Fin w)).bind fun o' =>
        k ⟨(queryBlocksEquiv Fact.out x.1 (P, b)).1, o'⟩)
  · congr 1; funext P; exact hcomm P
  · exact Cslib.Probability.PMF.uniformOfFintype_bind_bind_equiv (queryBlocksEquiv Fact.out x.1)
      (fun S => (PMF.uniformOfFintype (Fin c → Fin w)).bind fun o' => k ⟨S.1, o'⟩)

/-- Single-query distribution step for `buildQuery` under an assumed conditioned-uniform hint law
(after [Hoover, Patel, Persiano and Yeo, Section 5.2, p. 22][HooverPatelPersianoYeo2025]; not
privacy of `plinkoScheme`, #5736): when `Even c`, if `(P, o)` is drawn uniformly from
`RegBlocksContaining c x.1 × OffsetsContaining c w x` and `b` and `r` are a uniform coin and
uniform replacement offset, then `buildQuery x P.1 o.1 b r` has law `plinkoSim c w` for every `x`.
The law of the hints consumed by `plinkoScheme` is not analysed here (#5736). -/
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

/-- Idealized stand-in for Plinko (not an implementation of
[Hoover, Patel, Persiano and Yeo, Section 5.2][HooverPatelPersianoYeo2025]; full-client privacy is
open in #5736): it has no iPRF, no keys and no hint table, keeps `db` in its state, and at each
online query for `x = (α, β)` draws a fresh conditioned regular hint
`(P, o) ← RegBlocksContaining c x.1 × OffsetsContaining c w x`, computes
`p = blockParity db P.1 o.1` online from `db`, sends `buildQuery x P.1 o.1 b r`, and reconstructs
`db x = plinkoReconstruct p b ans`. Because it resamples a fresh conditioned hint on every query,
its privacy skips the hint-table refresh invariant and iPRF reduction of `plinkoScheme` (#5736). -/
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

section HybridProperties

variable [Fact (Even c)] [NeZero w]

/-- Perfect privacy for the idealized stand-in `plinkoHybridScheme`, not for `plinkoScheme` and not
the computational privacy claim of
[Hoover, Patel, Persiano and Yeo, Section 5.2, p. 23][HooverPatelPersianoYeo2025] (#5736): because
`plinkoHybridScheme` keeps `db` in its state and draws a fresh conditioned hint for each query
without an iPRF or hint table, when `Even c` it is perfectly private with simulator `plinkoSim c w`
against every adaptive server. -/
theorem isPerfectlyPrivateWith_plinkoHybridScheme :
    (plinkoHybridScheme c w).IsPerfectlyPrivateWith (plinkoSim c w) := by
  apply Scheme.isPerfectlyPrivateWith_of_invariant
    (proj := fun _ => ())
    (inv := PMF.pure ())
    (sim := plinkoSim c w)
    (stepS := fun adv _ st =>
      (ProbComp.eval (adv.chooseQuery st)).bind fun p =>
        (ProbComp.eval (plinkoSim c w)).bind fun q =>
          (ProbComp.eval (adv.onQuery p.1 q)).map fun sa => ((), sa.1))
  · intro db; simp [plinkoHybridScheme]
  · intro St adv db st
    simp only [Scheme.realAdaptiveStep, plinkoHybridScheme, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map]
    congr 1; funext ⟨st₁, i⟩
    exact uniformOfFintype_bind_buildQuery i
      (fun q => (ProbComp.eval (adv.onQuery st₁ q)).bind fun sa => PMF.pure ((), sa.1))
  · intro St adv st kCont
    simp only [idealAdaptiveStep, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- Existential perfect privacy for the idealized stand-in `plinkoHybridScheme` (which has no iPRF,
keys or hint table; not privacy of `plinkoScheme`, #5736). -/
theorem isPerfectlyPrivate_plinkoHybridScheme :
    (plinkoHybridScheme c w).IsPerfectlyPrivate :=
  isPerfectlyPrivateWith_plinkoHybridScheme.isPerfectlyPrivate

/-- Zero adaptive-server distinguishing advantage for the idealized stand-in `plinkoHybridScheme`
(which has no iPRF, keys or hint table; not privacy of `plinkoScheme`, #5736). -/
theorem privacyAdvantage_plinkoHybridScheme_eq_zero {St : Type}
    (adv : AdaptiveServer (Fin c × Fin w) (PlinkoQuery c w) (Bool × Bool) St)
    (finalize : St → Bool) (db : Fin c × Fin w → Bool) (k : ℕ) (st₀ : St) :
    (plinkoHybridScheme c w).privacyAdvantage (plinkoSim c w) adv finalize db k st₀ = 0 :=
  isPerfectlyPrivateWith_plinkoHybridScheme.privacyAdvantage_eq_zero adv finalize db k st₀

/-- Non-adaptive query-transcript uniformity for the idealized stand-in `plinkoHybridScheme` (not
for `plinkoScheme`, #5736): for every database `db` and query list `xs`, the query transcript of
`plinkoHybridScheme c w` has the same distribution as `xs.length` independent draws from
`plinkoSim c w`. -/
theorem eval_queryTranscript_plinkoHybridScheme (db : Fin c × Fin w → Bool)
    (xs : List (Fin c × Fin w)) :
    ProbComp.eval ((plinkoHybridScheme c w).queryTranscript db xs) =
      ProbComp.eval (simTranscript (plinkoSim c w) xs.length) := by
  apply Scheme.eval_queryTranscript_eq_of_invariant
    (proj := fun _ => ())
    (inv := PMF.pure ())
    (sim := plinkoSim c w)
    (stepQ := fun _ _ => (ProbComp.eval (plinkoSim c w)).map ((), ·))
  · simp [plinkoHybridScheme]
  · intro _ x
    simp only [Scheme.queryStep, plinkoHybridScheme, ProbComp.eval_uniform, pmf_norm]
    exact uniformOfFintype_bind_buildQuery x (fun q => PMF.pure ((), q))
  · intro _ kCont
    simp [pmf_norm]

end HybridProperties

/-! ### Database and hint updates (`UpdateDB` and `UpdateHint`, Definition 5.2 and Figure 7) -/

private theorem blockParity_update_db (db : Fin c × Fin w → Bool) (u : Fin c × Fin w) (d : Bool)
    (P : Finset (Fin c)) (o : Fin c → Fin w) :
    blockParity (Function.update db u (d + db u)) P o =
      (if o u.1 = u.2 ∧ u.1 ∈ P then d else false) + blockParity db P o := by
  have hpoint : ∀ a ∈ P,
      Function.update db u (d + db u) (a, o a) =
        (if (a, o a) = u then d else false) + db (a, o a) := fun a _ => by
    by_cases hau : (a, o a) = u <;> simp [hau, ← Bool.zero_eq_false]
  unfold blockParity
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, sum_ite_pair_eq]

private theorem blockParity_update_db_cand {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    (db : Fin c × Fin w → Bool) (keys : Fin c → Key) (u : Fin c × Fin w) (d : Bool)
    (j : Fin (nReg + nBackup)) (P : Finset (Fin c)) (hcorr : iF.IsCorrectKey (keys u.1)) :
    (if j ∈ iF.inv (keys u.1) u.2 ∧ u.1 ∈ P then
        d + blockParity db P (fun a => iF.eval (keys a) j)
      else blockParity db P (fun a => iF.eval (keys a) j)) =
      blockParity (Function.update db u (d + db u)) P (fun a => iF.eval (keys a) j) := by
  rw [blockParity_update_db]
  simp only [hcorr j u.2]
  by_cases hcond : iF.eval (keys u.1) j = u.2 ∧ u.1 ∈ P <;> simp [hcond, ← Bool.zero_eq_false]

/-- An update summary `δ = (i, u)`
([Hoover, Patel, Persiano and Yeo, Definition 5.2][HooverPatelPersianoYeo2025]): entry `i` of the
database is XORed with `u`. -/
@[ext]
structure UpdateSummary (c w : ℕ) where
  /-- The updated entry `i`. -/
  entry : Fin c × Fin w
  /-- The XOR difference `u` between the new and the old bit. -/
  delta : Bool
  deriving DecidableEq

/-- Server database update algorithm `UpdateDB(i, d; D)`
([Hoover, Patel, Persiano and Yeo, Definition 5.2 and Figure 7][HooverPatelPersianoYeo2025]):
when entry `i` is updated to new bit `d`, returns the update summary `δ = (i, db i + d)` together
with the updated database `Function.update db i d`. -/
@[expose] def updateDB (db : Fin c × Fin w → Bool) (i : Fin c × Fin w) (d : Bool) :
    UpdateSummary c w × (Fin c × Fin w → Bool) :=
  (⟨i, db i + d⟩, Function.update db i d)

/-- Client hint update algorithm `UpdateHint(δ; st)` for an update summary `δ = (i, u)` where
`u : Bool` is the XOR delta at entry `i : Fin c × Fin w`
([Hoover, Patel, Persiano and Yeo, Definition 5.2 and Figure 7][HooverPatelPersianoYeo2025]):
1. Computes the candidate hint slots `cand := iF.inv (st.keys i.1) i.2` via the iPRF inverse.
2. For each slot `j ∈ cand`, flips the parity of `st.H j` if `i.1` lies in its base block set,
   and flips `parityIn` (if `i.1 ∈ B`) or `parityOut` (if `i.1 ∉ B`) of `st.T j`.
3. If `st.cache i = some (a, j')`, updates `st.cache i` to `some (u + a, j')` and (if `st.H j'` is
   still active as a promoted hint for `i`) flips its parity by `u`. -/
@[expose] def updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (st : PlinkoState c w nReg nBackup Key) :
    PlinkoState c w nReg nBackup Key :=
  let i := δ.entry
  let u := δ.delta
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

/-- Applies a list of database XOR update summaries `updates : List (UpdateSummary c w)` to
`db`. -/
@[expose] def applyUpdates (updates : List (UpdateSummary c w))
    (db : Fin c × Fin w → Bool) : Fin c × Fin w → Bool :=
  updates.foldr (fun δ d => Function.update d δ.entry (δ.delta + d δ.entry)) db

/-- Updates the client state `st` across a list of database XOR update summaries
`updates : List (UpdateSummary c w)`
([Hoover, Patel, Persiano and Yeo, Figure 7, `UpdateHint`][HooverPatelPersianoYeo2025]). -/
@[expose] def updateState (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (updates : List (UpdateSummary c w)) (st : PlinkoState c w nReg nBackup Key) :
    PlinkoState c w nReg nBackup Key :=
  updates.foldr (fun δ s => updateHint iF δ s) st

@[simp]
theorem applyUpdates_nil (db : Fin c × Fin w → Bool) :
    applyUpdates [] db = db := rfl

@[simp]
theorem applyUpdates_cons (δ : UpdateSummary c w) (updates : List (UpdateSummary c w))
    (db : Fin c × Fin w → Bool) :
    applyUpdates (δ :: updates) db =
      Function.update (applyUpdates updates db) δ.entry
        (δ.delta + applyUpdates updates db δ.entry) := rfl

@[simp]
theorem updateState_nil (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (st : PlinkoState c w nReg nBackup Key) :
    updateState iF [] st = st := rfl

@[simp]
theorem updateState_cons (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (updates : List (UpdateSummary c w))
    (st : PlinkoState c w nReg nBackup Key) :
    updateState iF (δ :: updates) st = updateHint iF δ (updateState iF updates st) := rfl

namespace PlinkoState

@[simp]
theorem updateHint_keys (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (st : PlinkoState c w nReg nBackup Key) :
    (updateHint iF δ st).keys = st.keys :=
  rfl

@[simp]
theorem updateState_keys (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (updates : List (UpdateSummary c w)) (st : PlinkoState c w nReg nBackup Key) :
    (updateState iF updates st).keys = st.keys := by
  induction updates <;> simp [*]

/-- Single-entry XOR-delta update preserves `PlinkoState.Valid`
([Hoover, Patel, Persiano and Yeo, Figure 7, `UpdateHint`][HooverPatelPersianoYeo2025]): if
`st.Valid iF db` and `iF.IsCorrectKey (st.keys u.1)` hold, then `updateHint iF ⟨u, d⟩ st` is valid
for the updated database `Function.update db u (d + db u)`. -/
theorem valid_updateHint_delta {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    (u : Fin c × Fin w) (d : Bool) (hvalid : st.Valid iF db)
    (hcorr : iF.IsCorrectKey (st.keys u.1)) :
    (updateHint iF ⟨u, d⟩ st).Valid iF (Function.update db u (d + db u)) where
  valid_regular j P p' hH := by
    dsimp only [updateHint] at hH ⊢
    rcases hHj : st.H j with _ | ⟨P₀, p⟩ | _ <;>
      simp only [hHj, reduceCtorEq, Option.some.injEq, ActiveHint.regular.injEq] at hH
    obtain ⟨rfl, rfl⟩ := hH
    rw [hvalid.valid_regular j P₀ p hHj, blockParity_update_db_cand _ _ _ _ _ _ hcorr]
  valid_promoted j P y p' hH := by
    dsimp only [updateHint] at hH ⊢
    rcases hHj : st.H j with _ | _ | ⟨P₀, y₀, p⟩ <;>
      simp only [hHj, reduceCtorEq, Option.some.injEq, ActiveHint.promoted.injEq] at hH
    obtain ⟨rfl, rfl, rfl⟩ := hH
    obtain ⟨hyP, hp, hcache⟩ := hvalid.valid_promoted j P₀ y₀ p hHj
    refine ⟨hyP, ?_, ?_⟩
    · rw [hp, ← blockParity_update_db_cand db st.keys u d j P₀ hcorr]
      by_cases hyu : y₀ = u <;>
        by_cases hc : j ∈ iF.inv (st.keys u.1) u.2 ∧ u.1 ∈ P₀ <;>
        simp [hyu, hc, add_assoc, add_left_comm]
    · by_cases hyu : y₀ = u
      · subst hyu; simp [hcache]
      · simp [Function.update_of_ne hyu, hcache]
  valid_backup j bk' hT := by
    dsimp only [updateHint] at hT ⊢
    rcases hTj : st.T j with _ | ⟨B, p₁, p₂⟩ <;>
      simp only [hTj, reduceCtorEq, Option.some.injEq] at hT
    subst hT
    obtain ⟨hin, hout, hHnone, hcache⟩ := hvalid.valid_backup j ⟨B, p₁, p₂⟩ hTj
    dsimp only at hin hout
    refine ⟨?_, ?_, by simp [hHnone], fun x => ?_⟩
    · dsimp only
      rw [hin, blockParity_update_db_cand _ _ _ _ _ _ hcorr]
    · dsimp only
      have hmem : (j ∈ iF.inv (st.keys u.1) u.2 ∧ u.1 ∈ Finset.univ \ B) ↔
          (j ∈ iF.inv (st.keys u.1) u.2 ∧ u.1 ∉ B) := by simp
      rw [hout, ← blockParity_update_db_cand db st.keys u d j (Finset.univ \ B) hcorr]
      simp only [hmem]
    · by_cases hxu : x = u
      · subst hxu
        have hmap : ((updateHint iF ⟨x, d⟩ st).cache x).map Prod.snd =
            (st.cache x).map Prod.snd := by
          dsimp only [updateHint]; rw [Function.update_self]; cases st.cache x <;> rfl
        exact hmap ▸ hcache x
      · simpa [Function.update_of_ne hxu] using hcache x
  valid_cache x a' j hC := by
    have hprom_upd (hprom : ∀ h, st.H j = some h → ∃ P p, h = .promoted P x p)
        (h' : ActiveHint c w) (hh' : (updateHint iF ⟨u, d⟩ st).H j = some h') :
        ∃ P p, h' = .promoted P x p := by
      dsimp only [updateHint] at hh'
      cases hHj : st.H j with
      | none => simp [hHj] at hh'
      | some h =>
        obtain ⟨P, p, rfl⟩ := hprom h hHj
        rw [hHj] at hh'
        simp only [Option.some.injEq] at hh'
        exact ⟨P, _, hh'.symm⟩
    dsimp only [updateHint] at hC
    by_cases hxu : x = u
    · subst hxu
      simp only [Function.update_self, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at hC
      obtain ⟨a, j₀, hcx, rfl, rfl⟩ := hC
      obtain ⟨rfl, hprom⟩ := hvalid.valid_cache x a j₀ hcx
      exact ⟨by simp, hprom_upd hprom⟩
    · simp only [Function.update_of_ne hxu] at hC
      obtain ⟨rfl, hprom⟩ := hvalid.valid_cache x a' j hC
      exact ⟨by simp [Function.update_of_ne hxu], hprom_upd hprom⟩

/-- Database and hint update correctness (`UpdateDB` / `UpdateHint`, Figure 7 of
[Hoover, Patel, Persiano and Yeo, Section 5.2 and Figure 7][HooverPatelPersianoYeo2025]): if
`st.Valid iF db` and `iF.IsCorrectKey (st.keys i.1)` hold, updating entry `i` to new bit `d` via
summary `⟨i, db i + d⟩ = (updateDB db i d).1` yields a client state valid for
`Function.update db i d = (updateDB db i d).2`. -/
theorem valid_updateHint {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    (i : Fin c × Fin w) (d : Bool) (hvalid : st.Valid iF db)
    (hcorr : iF.IsCorrectKey (st.keys i.1)) :
    (updateHint iF ⟨i, db i + d⟩ st).Valid iF (Function.update db i d) := by
  have hcancel : (db i + d) + db i = d := by
    rw [add_comm (db i) d, add_assoc, BooleanRing.add_self, add_zero]
  simpa [hcancel] using valid_updateHint_delta i (db i + d) hvalid hcorr

private theorem slotMatchesBlock_updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w)
    (j : Fin (nReg + nBackup)) :
    slotMatchesBlock iF (updateHint iF δ st) x j = slotMatchesBlock iF st x j := by
  dsimp only [slotMatchesBlock, updateHint]
  cases st.H j with
  | none => rfl
  | some h => cases h <;> dsimp only [extractActiveHint] <;> split_ifs <;> rfl

private theorem findHintSlot_updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    findHintSlot iF (updateHint iF δ st) x = findHintSlot iF st x := by
  simp [findHintSlot, slotMatchesBlock_updateHint]

private theorem findBackupSlot_updateHint (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (st : PlinkoState c w nReg nBackup Key) :
    findBackupSlot (updateHint iF δ st).T = findBackupSlot st.T := by
  have hpred : (fun j : Fin (nReg + nBackup) => ((updateHint iF δ st).T j).isSome) =
      (fun j : Fin (nReg + nBackup) => (st.T j).isSome) := by
    funext j; dsimp only [updateHint]; cases st.T j <;> rfl
  simp [findBackupSlot, hpred]

/-- `updateHint` preserves `CanAnswer` for every query `x`. -/
@[simp]
theorem canAnswer_updateHint_iff (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (δ : UpdateSummary c w) (st : PlinkoState c w nReg nBackup Key) (x : Fin c × Fin w) :
    (updateHint iF δ st).CanAnswer iF x ↔ st.CanAnswer iF x := by
  have hcache : ((updateHint iF δ st).cache x).isSome = (st.cache x).isSome := by
    dsimp only [updateHint]
    by_cases hxu : x = δ.entry <;> simp [hxu]
  have hget : (getHint iF (updateHint iF δ st) x).isSome = (getHint iF st x).isSome := by
    simp only [getHint, Option.bind_eq_bind, findHintSlot_updateHint]
    cases findHintSlot iF st x with
    | none => rfl
    | some j =>
      dsimp only [Option.bind, updateHint]
      cases st.H j with
      | none => rfl
      | some h =>
        cases h <;> dsimp only [Option.bind, extractActiveHint] <;> split_ifs <;> rfl
  simp [CanAnswer, hcache, hget, findBackupSlot_updateHint]

/-- Batch database update (`UpdateHint`, Figure 7 of
[Hoover, Patel, Persiano and Yeo][HooverPatelPersianoYeo2025]) preserves `PlinkoState.Valid`: if
`st.Valid iF db` and `∀ α, iF.IsCorrectKey (st.keys α)` hold, then `updateState iF updates st` is
valid for `applyUpdates updates db`. -/
theorem valid_updateState {iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w)}
    {db : Fin c × Fin w → Bool} {st : PlinkoState c w nReg nBackup Key}
    (updates : List (UpdateSummary c w)) (hvalid : st.Valid iF db)
    (hcorr : ∀ α : Fin c, iF.IsCorrectKey (st.keys α)) :
    (updateState iF updates st).Valid iF (applyUpdates updates db) := by
  induction updates with
  | nil => exact hvalid
  | cons δ updates ih =>
    simp only [updateState_cons, applyUpdates_cons]
    refine valid_updateHint_delta δ.entry δ.delta ih ?_
    rw [updateState_keys]
    exact hcorr δ.entry.1

/-- `updateState` preserves `CanAnswer` for every query `x`. -/
@[simp]
theorem canAnswer_updateState_iff (iF : InvertiblePRF Key (Fin (nReg + nBackup)) (Fin w))
    (updates : List (UpdateSummary c w)) (st : PlinkoState c w nReg nBackup Key)
    (x : Fin c × Fin w) :
    (updateState iF updates st).CanAnswer iF x ↔ st.CanAnswer iF x := by
  induction updates <;> simp [*]

end PlinkoState

end Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko

end
