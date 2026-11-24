/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Protocol

/-!
# Smooth FRI Transcript Accessors, Target Words, Fiber Weights, and Acceptance Predicates

Defines smooth parameter scaling identities, shared transcript prefix accessors (`prefOracle`,
`prefFoldScalar`, `prefQueryIdxs`, `prefFinalQueryIdxs`), smooth per-round target words and
pushed-forward integer fiber weights (`friSmoothTargetWord`, `friSmoothPreWeight`,
`friSmoothOracleFilterWeight`, `friSmoothNextWeight`), and smooth starting-point acceptance
predicates (`friSmoothPrefixPasses`, `friSmoothTranscriptSingleAccepts`, `friSmoothFinalPasses`).
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

/-! ### Smooth Parameter and Domain Helpers -/

section SmoothParamHelpers

variable {F : Type} [Field F]

/-- Cumulative fiber-size product identity `2 ^ cumLog i * domainSize i = 2 ^ d` for `i ≤ m`. -/
theorem FRISmoothParams.two_pow_cumLog_mul_domainSize (params : FRISmoothParams F)
    {i : ℕ} (hi : i ≤ params.m) :
    2 ^ params.cumLog i * params.domainSize i = 2 ^ params.d := by
  have := params.cumLog_le_d hi
  simp only [FRISmoothParams.domainSize, ← pow_add]
  exact congrArg (2 ^ ·) (by omega)

/-- Cumulative dimension scaling identity `2 ^ cumLog i * dim i = dim 0` for `i ≤ m`. -/
theorem FRISmoothParams.two_pow_cumLog_mul_dim (params : FRISmoothParams F)
    {i : ℕ} (hi : i ≤ params.m) :
    2 ^ params.cumLog i * params.dim i = params.dim 0 := by
  have hle := params.cumLog_le_totalLog hi
  simp only [FRISmoothParams.dim, FRISmoothParams.cumLog, friCumLog_zero, Nat.sub_zero,
    FRISmoothParams.totalLog] at hle ⊢
  rw [mul_left_comm, ← pow_add]
  exact congrArg (params.kFinal * 2 ^ ·) (by omega)

/-- Every round Reed–Solomon dimension `params.dim r` is at least `1`. -/
theorem FRISmoothParams.one_le_dim (params : FRISmoothParams F) (r : ℕ) : 1 ≤ params.dim r :=
  Nat.mul_pos params.hkPos (Nat.pow_pos (by omega))

/-- Each active round dimension fits inside its active coset size (`r ≤ m`). -/
theorem FRISmoothParams.dim_le_domainSize (params : FRISmoothParams F)
    {r : ℕ} (hr : r ≤ params.m) :
    params.dim r ≤ params.domainSize r := by
  have htot : params.totalLog ≤ params.d := params.htotal
  have hle : params.cumLog r ≤ params.totalLog := params.cumLog_le_totalLog hr
  refine (Nat.mul_le_mul_right _ params.hkLe).trans_eq ?_
  rw [FRISmoothParams.domainSize, ← pow_add]
  change 2 ^ ((params.d - params.totalLog) + (params.totalLog - params.cumLog r)) = _
  exact congrArg (2 ^ ·) (by omega)

/-- Transport the initial unique-decoding bound `2 * e + params.dim 0 ≤ 2 ^ params.d` to the
scaled round-`(i + 1)` unique-decoding bound
`2 * (e / 2 ^ cumLog (i + 1)) + params.dim (i + 1) ≤ params.domainSize (i + 1)`. -/
theorem FRISmoothParams.two_mul_div_add_dim_le (params : FRISmoothParams F) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d) (i : Fin params.m) :
    2 * (e / 2 ^ params.cumLog (i.val + 1)) + params.dim (i.val + 1) ≤
      params.domainSize (i.val + 1) := by
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos (a := 2) (n := params.cumLog (i.val + 1))
    (by omega))
  rw [mul_add, mul_left_comm _ 2, params.two_pow_cumLog_mul_dim i.isLt,
    params.two_pow_cumLog_mul_domainSize i.isLt]
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_div_le e _)) _).trans huniq

end SmoothParamHelpers

/-! ### Shared Transcript Accessors (`prefOracle`, `prefFoldScalar`, `prefQueryIdxs`) -/

section SharedTranscriptAccessors

variable {F : Type} [Field F]

/-- Read the `k`-th committed prover oracle from a transcript prefix, defaulting to the zero table
if `k ≥ pref.length`. -/
@[expose] def prefOracle {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (k : ℕ) : OracleTable d F :=
  match pref[k]? with
  | some (π, _) => π
  | none => fun _ => 0

/-- Read the `k`-th folding challenge scalar from a transcript prefix, defaulting to `0` if
`k ≥ pref.length`. -/
@[expose] def prefFoldScalar {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (k : ℕ) : F :=
  match pref[k]? with
  | some (_, c) => c.foldScalar
  | none => 0

/-- Read the `k`-th round's `q` query starting indices from a transcript prefix, defaulting to `0`
if `k ≥ pref.length`. -/
@[expose] def prefQueryIdxs {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (k : ℕ) :
    Fin q → Fin (2 ^ d) :=
  match pref[k]? with
  | some (_, c) => c.queryIdxs
  | none => fun _ => ⟨0, Nat.pow_pos (by omega)⟩

/-- Read the final round's `q` query starting indices from a transcript, defaulting to `0`. -/
abbrev prefFinalQueryIdxs (params : FRIParams F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    Fin params.q → Fin (2 ^ params.d) :=
  prefQueryIdxs pref params.m

/-- Reading oracle `k < pref.length` from `pref ++ extra` matches reading it from `pref`. -/
theorem prefOracle_append_left {d q : ℕ}
    (pref extra : List (OracleTable d F × FRIChal F d q)) {k : ℕ} (hk : k < pref.length) :
    prefOracle (pref ++ extra) k = prefOracle pref k := by
  simp only [prefOracle, List.getElem?_append_left hk]

/-- Reading the newly appended oracle at index `pref.length` returns `π`. -/
theorem prefOracle_append_self {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (π : OracleTable d F) (c : FRIChal F d q) :
    prefOracle (pref ++ [(π, c)]) pref.length = π := by
  simp only [prefOracle, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]

/-- Reading folding scalar `k < pref.length` from `pref ++ extra` matches reading it from `pref`.
-/
theorem prefFoldScalar_append_left {d q : ℕ}
    (pref extra : List (OracleTable d F × FRIChal F d q)) {k : ℕ} (hk : k < pref.length) :
    prefFoldScalar (pref ++ extra) k = prefFoldScalar pref k := by
  simp only [prefFoldScalar, List.getElem?_append_left hk]

/-- Reading the newly appended folding scalar at index `pref.length` returns `c.foldScalar`. -/
theorem prefFoldScalar_append_self {d q : ℕ}
    (pref : List (OracleTable d F × FRIChal F d q)) (π : OracleTable d F) (c : FRIChal F d q) :
    prefFoldScalar (pref ++ [(π, c)]) pref.length = c.foldScalar := by
  simp only [prefFoldScalar, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero]


/-- Reading the final round's query starting indices after appending `(π, c)` at index `m` returns
`c.queryIdxs`. -/
theorem prefFinalQueryIdxs_append_self (params : FRIParams F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    prefFinalQueryIdxs params (pref ++ [(π, c)]) = c.queryIdxs := by
  simp only [prefFinalQueryIdxs, prefQueryIdxs, ← hlen, List.getElem?_append_right le_rfl,
    Nat.sub_self, List.getElem?_cons_zero]

/-- Reading oracle `k < m + 1` from a transcript built with `List.ofFn` yields `oracles ⟨k, hk⟩`.
-/
theorem prefOracle_ofFn {m d q : ℕ}
    (oracles : Fin (m + 1) → OracleTable d F) (chals : Fin (m + 1) → FRIChal F d q)
    {k : ℕ} (hk : k < m + 1) :
    prefOracle (List.ofFn fun j : Fin (m + 1) => (oracles j, chals j)) k = oracles ⟨k, hk⟩ := by
  simp only [prefOracle, List.getElem?_ofFn, hk, ↓reduceDIte]

/-- Reading folding scalar `k < m + 1` from a transcript built with `List.ofFn` yields
`(chals ⟨k, hk⟩).foldScalar`. -/
theorem prefFoldScalar_ofFn {m d q : ℕ}
    (oracles : Fin (m + 1) → OracleTable d F) (chals : Fin (m + 1) → FRIChal F d q)
    {k : ℕ} (hk : k < m + 1) :
    prefFoldScalar (List.ofFn fun j : Fin (m + 1) => (oracles j, chals j)) k =
      (chals ⟨k, hk⟩).foldScalar := by
  simp only [prefFoldScalar, List.getElem?_ofFn, hk, ↓reduceDIte]


/-- Reading the final round's query starting indices from a full `List.ofFn` transcript yields
`(chals (Fin.last params.m)).queryIdxs`. -/
theorem prefFinalQueryIdxs_ofFn (params : FRIParams F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    prefFinalQueryIdxs params
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) =
      (chals (Fin.last params.m)).queryIdxs := by
  simp only [prefFinalQueryIdxs, prefQueryIdxs, List.getElem?_ofFn, Nat.lt_succ_self,
    ↓reduceDIte, Fin.last]

/-- Equivalence between `Fin (2 * 2 ^ (d - (j + 1)))` and `Fin (2 ^ (d - j))` for `j < d`. -/
@[expose] def reindexDoubleEquiv {d j : ℕ} (hj : j < d) :
    Fin (2 * 2 ^ (d - (j + 1))) ≃ Fin (2 ^ (d - j)) where
  toFun := reindexDouble hj
  invFun idx := ⟨idx.val, by
    have hsplit : 2 ^ (d - j) = 2 * 2 ^ (d - (j + 1)) := by
      have hsub : d - j = (d - (j + 1)) + 1 := by omega
      rw [hsub, pow_succ']
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SharedTranscriptAccessors

/-! ### Smooth Transcript State, Target Words, and Weight Filters -/

section SmoothTranscriptState

variable {F : Type} [Field F]

/-- Expected round-`i` word along a smooth transcript prefix `pref`: `stmt` at round `0`, and the
`l⁽ⁱ⁻¹⁾`-to-1 coset folding `foldWord` of `prefOracle pref (i - 1)` at `prefFoldScalar pref (i - 1)`
for round `i ≥ 1`. -/
@[expose] def friSmoothTargetWord (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (params.domainSize i) → F
  | 0, _ => restrictOracle (i := 0) stmt
  | i + 1, hi =>
    let ir : Fin params.m := ⟨i, Nat.lt_of_succ_le hi⟩
    foldWord (params.g ^ (2 ^ params.cumLog i)) (params.ω ^ (2 ^ params.cumLog i))
      (fun idx : Fin (params.arity ir * params.domainSize (i + 1)) =>
        restrictOracle (i := params.cumLog i) (prefOracle pref i)
          (finCongr (params.domainSize_eq_arity_mul_succ ir).symm idx))
      (prefFoldScalar pref i)

/-- Pre-filter integer fiber weight `W̃_i : Fin (params.domainSize i) → ℕ` along a smooth transcript
prefix `pref`, prior to applying the round-`i` oracle consistency check `π_i = friSmoothTargetWord`:
identically `1` at `i = 0`, and for `i ≥ 1` the `pushWeight` fiberwise sum of the round-`(i - 1)`
filtered weight. -/
@[expose] def friSmoothPreWeight [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    (i : ℕ) → i ≤ params.m → Fin (params.domainSize i) → ℕ
  | 0, _ => fun _ => 1
  | i + 1, hi =>
    let ir : Fin params.m := ⟨i, Nat.lt_of_succ_le hi⟩
    let prevTarget := friSmoothTargetWord params stmt pref i (Nat.le_of_succ_le hi)
    let prevWeight := friSmoothPreWeight params stmt pref i (Nat.le_of_succ_le hi)
    let prevOracle := restrictOracle (i := params.cumLog i) (prefOracle pref i)
    let filt : Fin (params.domainSize i) → ℕ :=
      fun y => if prevOracle y = prevTarget y then prevWeight y else 0
    pushWeight (a := params.arity ir)
      (fun idx => filt (finCongr (params.domainSize_eq_arity_mul_succ ir).symm idx))

/-- Filtered smooth round-`i` weight for an explicit prover oracle `π`: retains `friSmoothPreWeight`
on coordinates where `π` agrees with `friSmoothTargetWord`, and zeroes all other coordinates. -/
@[expose] def friSmoothOracleFilterWeight [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (params.domainSize i)) : ℕ :=
  if restrictOracle (i := params.cumLog i) π j = friSmoothTargetWord params stmt pref i hi j then
    friSmoothPreWeight params stmt pref i hi j
  else 0

/-- Pushed smooth round-`(i + 1)` weight induced by an explicit prover oracle `π` at round `i`
(independent of the round-`i` verifier challenge). -/
@[expose] def friSmoothNextWeight [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    Fin (params.domainSize (i + 1)) → ℕ :=
  let ir : Fin params.m := ⟨i, hi⟩
  pushWeight (a := params.arity ir)
    (fun idx => friSmoothOracleFilterWeight params stmt pref i hi.le π
      (finCongr (params.domainSize_eq_arity_mul_succ ir).symm idx))

end SmoothTranscriptState

/-! ### Smooth Starting-Point Acceptance Predicates -/

section SmoothAcceptancePredicates

variable {F : Type} [Field F]

/-- Smooth prefix acceptance predicate for a starting index `s : Fin (2 ^ d)` through folding
rounds `0, ..., i - 1` along a transcript `pref`: round-0 binding `π_0(s) = stmt(s)` plus
`l⁽ᵏ⁾`-to-1 fiber folding checks for every `k < i`. -/
@[expose] def friSmoothPrefixPasses (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) : Prop :=
  prefOracle pref 0 s = stmt s ∧
  ∀ k : Fin params.m, k.val < i →
    foldFiber (params.g ^ (2 ^ params.cumLog k.val)) (params.ω ^ (2 ^ params.cumLog k.val))
      (fun t : Fin (params.arity k) => prefOracle pref k.val (friSmoothFiberIdx params k s t))
      (friSmoothFoldedFin params k s) (prefFoldScalar pref k.val) =
    prefOracle pref (k.val + 1) (friSmoothFoldedIdx params k s)

/-- Full single-query acceptance predicate evaluated on a smooth transcript list `pref` at starting
index `s : Fin (2 ^ d)`. -/
@[expose] def friSmoothTranscriptSingleAccepts (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) : Prop :=
  friSmoothPrefixPasses params stmt pref params.m s ∧
    prefOracle pref params.m (friSmoothFinalIdx params s) =
      friSmoothFinalCodeword params (prefOracle pref params.m) (friSmoothFinalFin params s)

/-- Smooth final-round acceptance predicate for a length-`m` prefix `pref` and final oracle `πFinal`
(manifestly independent of the final round's verifier challenge `c`). -/
@[expose] def friSmoothFinalPasses (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  (if params.m = 0 then πFinal s else prefOracle pref 0 s) = stmt s ∧
  (∀ k : Fin params.m,
    foldFiber (params.g ^ (2 ^ params.cumLog k.val)) (params.ω ^ (2 ^ params.cumLog k.val))
      (fun t : Fin (params.arity k) => prefOracle pref k.val (friSmoothFiberIdx params k s t))
      (friSmoothFoldedFin params k s) (prefFoldScalar pref k.val) =
    (if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1))
      (friSmoothFoldedIdx params k s)) ∧
  πFinal (friSmoothFinalIdx params s) =
    friSmoothFinalCodeword params πFinal (friSmoothFinalFin params s)

/-- Decidability of the smooth prefix-acceptance predicate `friSmoothPrefixPasses`. -/
instance instDecidableFriSmoothPrefixPasses [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) :
    Decidable (friSmoothPrefixPasses params stmt pref i s) := by
  unfold friSmoothPrefixPasses
  infer_instance

/-- Decidability of the final-round smooth acceptance predicate `friSmoothFinalPasses`. -/
instance instDecidableFriSmoothFinalPasses [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    Decidable (friSmoothFinalPasses params stmt pref πFinal s) := by
  unfold friSmoothFinalPasses
  infer_instance


end SmoothAcceptancePredicates

end Cslib.Crypto.Protocols.FRI
