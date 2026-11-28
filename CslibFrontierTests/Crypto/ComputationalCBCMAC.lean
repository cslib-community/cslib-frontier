/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.CBCMAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Tactic.NormNum

/-!
# Ordinary-Import Client Tests for Computational CBC-MAC and Length-Prepended CBC-MAC

Exercises `CslibFrontier.Crypto.Computational.CBCMAC` through an ordinary `module` import (without
`import all`):

1. Concrete kernel-checked (`decide` / `rfl`) evaluations of `cbcMacFamily`, `prependLengthWord`,
   `lengthPrependedCbcMacFamily`, `ofFn_blockCountBlock`, `cbcFixedBlockMAC`, and
   `lengthPrependedBlockMAC`, plus subtle model-boundary witnesses (malformed-length rejection,
   repeated identical oracle queries under `IsPrefixFreeOn`, and `directReplyPrefixFreeAdv`
   relying on `n`-bit valid oracle replies without defensive `List.take n` truncation).
2. Explicit `IsOraclePPT` certificates and concrete non-vacuous numerical advantage bounds at
   `n = 16` for an adaptive 2-query prefix-free distinguisher on `cbcMacFamily` and for
   variable-length PRF and `SUFCMA` MAC security of `lengthPrependedCbcMacFamily`.
3. Asymptotic compositions from an arbitrary `PseudorandomFunction` for
   `PrefixFreePseudorandomFunctionOn`, `PseudorandomFunctionOn`, `PseudorandomFunctionOver`,
   `MACSUFCMAOn`, `MACEUFCMAOn` (via `macSufCmaOn_iff_macEufCmaOn`), and `MACScheme.SUFCMA` /
   `MACScheme.EUFCMA`.
4. Client instantiations of the 1-to-2-block length-extension attack (`cbcExtensionForger`,
   `not_macSufCmaOn_cbcMacFamily`, `not_prfOn_cbcMacFamily`).
-/

public section

namespace CslibFrontierTests.Crypto.ComputationalCBCMAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### 1. Concrete Word-Level Evaluations and Model Boundaries -/

/-- Toy length-preserving block family `F_k(x) = ¬(k ⊕ x)` with `F_k(0^n) = ¬k`. -/
def xnorFamily (key query : List Bool) : List Bool :=
  List.zipWith (fun k q => !(xor k q)) key query

theorem length_xnorFamily (key query : List Bool) (h : query.length = key.length) :
    (xnorFamily key query).length = key.length := by
  simp [xnorFamily, h]

-- Single-block and 2-block evaluations of `cbcMacFamily` at `n = 2`.
example : cbcMacFamily xnorFamily [true, false] [false, false] = [false, true] := by decide

example :
    cbcMacFamily xnorFamily [true, false] [false, false, false, true] = [false, true] := by
  decide

-- A common full block preserves this collision between a one- and a two-block message.
example :
    cbcMacWord xnorFamily 2 [true, false] ([false, false] ++ [true, true]) =
      cbcMacWord xnorFamily 2 [true, false] ([false, false, false, true] ++ [true, true]) := by
  rw [cbcMacWord_append_block xnorFamily (by decide) _ (by decide) (by decide),
    cbcMacWord_append_block xnorFamily (by decide) _ (by decide) (by decide)]
  decide

-- Empty-message (`0`-block) and 1-block evaluations of `prependLengthWord` and
-- `lengthPrependedCbcMacFamily` at `n = 2`: `[]` prepends `0^2 = [false, false]`, while a 1-block
-- message prepends `lowBits 2 1 = [true, false]`.
example : prependLengthWord 2 [] = [false, false] := by decide

example : prependLengthWord 2 [false, true] = [true, false, false, true] := by decide

example : lengthPrependedCbcMacFamily xnorFamily [true, false] [] = [false, true] := by decide

example : lengthPrependedCbcMacFamily xnorFamily [true, false] [false, false] = [true, false] := by
  decide

-- Exact bit-level agreement between `prependLengthWord` and `LengthPrependedCBCMAC`'s typed
-- `blockCountBlock` at `n = 4, L = 7, k = 5` (`5 = 1 + 4`, little-endian
-- `[true, false, true, false]`).
example :
    List.ofFn (blockCountBlock (n := 4) (L := 7) (by decide) ⟨5, by decide⟩) =
      [true, false, true, false] := by
  rw [ofFn_blockCountBlock]
  decide

-- `cbcFixedBlockMAC` and `lengthPrependedBlockMAC` verify honest tags (`k n = 0` authenticates
-- `[]`).
example :
    (cbcFixedBlockMAC (fun _ => 2) (ComputableInPolyTime.const 2) xnorFamily
      (by unfold xnorFamily; polytime)).verify
      [true, false] [false, false, false, true] [false, true] = true := by
  rw [cbcFixedBlockMAC_verify]
  decide

example :
    (lengthPrependedBlockMAC (fun _ => 0) (ComputableInPolyTime.const 0) xnorFamily
      (by unfold xnorFamily; polytime)).verify
      [true, false] [] [false, true] = true := by
  rw [lengthPrependedBlockMAC_verify]
  decide

-- Subtle boundary 1: malformed (non-block-aligned or overlong or empty-for-basic-CBC) oracle
-- queries return `[]` without invoking the keyed family or recording a MAC query.
example : cbcBlockValid (fun _ => 2) 2 [] = false := by decide
example : cbcBlockValid (fun _ => 2) 2 [true] = false := by decide
example : cbcBlockValid (fun _ => 2) 2 [true, false, true, false, true, false] = false := by decide
example : lpBlockValid (fun _ => 2) 2 [] = true := by decide
example : lpBlockValid (fun _ => 2) 2 [true] = false := by decide

example :
    macSigningOracleOn (lpBlockValid (fun _ => 2)) (lengthPrependedCbcMacFamily xnorFamily)
      2 [true, false] ((), [true]) [] = pure ([], []) := by
  simp [macSigningOracleOn, lpBlockValid]

example : cbcMacQuery (fun _ => 2) 2 ((), []) = pure [] := by
  simp [cbcMacQuery, cbcBlockValid]

example : cbcMacQuery (fun _ => 2) 2 ((), [true]) = pure [] := by
  simp [cbcMacQuery, cbcBlockValid]

example : lengthPrependedQuery (fun _ => 2) 2 ((), [true]) = pure [] := by
  simp [lengthPrependedQuery, lpBlockValid]

-- Subtle boundary 2: [BonehShoup2023] Definition 4.5 allows repeated *identical* queries (`x = y`)
-- in a prefix-free distinguisher (`WordPrefixFree` and `IsPrefixFreeOn` only forbid `x ≠ y` with
-- `x <+: y`).
/-- Two-query distinguisher that queries the same valid 1-block message `1^n` twice and checks
consistency of the two returned tags. -/
def repeatSameBlockAdv : OracleDistinguisher := fun n _ => do
  let tag1 ← List.take n <$> ProbOracleComp.query ((), List.replicate n true)
  let tag2 ← List.take n <$> ProbOracleComp.query ((), List.replicate n true)
  return tag1 == tag2

theorem isPrefixFreeOn_repeatSameBlockAdv (n : ℕ) :
    IsPrefixFreeOn (cbcBlockValid (fun _ => 2) n) n (repeatSameBlockAdv n []) := by
  intro oracle _ _ res hres x hx _ y hy _ hxy _
  have hstep : repeatSameBlockAdv n [] =
      .liftBind (.inr ((), List.replicate n true)) (fun raw1 =>
        .liftBind (.inr ((), List.replicate n true)) (fun raw2 =>
          .pure ((raw1.take n) == (raw2.take n)))) := by
    simp only [repeatSameBlockAdv, ProbOracleComp.query, OracleComp.query,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rfl
  rw [hstep] at hres
  simp only [wordQueryRunDist, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hres
  obtain ⟨_, ⟨_, rfl, rfl⟩, rfl⟩ := hres
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> exact hxy rfl

-- Subtle boundary 3: `IsPrefixFreeOn valid outLen` constrains valid oracle replies to have length
-- `outLen`, admitting distinguishers that use a returned `n`-bit block directly (with only a loose
-- `2 * n` PPT cap rather than defensive `List.take n` truncation) to form a 3-block query
-- `tag1 ++ 0^n ++ 1^n` when `tag1 != 0^n`.
/-- Adaptive distinguisher that embeds a valid `n`-bit reply `tag1 ≠ 0^n` directly as the first
block of its second query `tag1 ++ 0^n ++ 1^n` without `List.take n` truncation. -/
def directReplyPrefixFreeAdv : OracleDistinguisher := fun n _ => do
  let tag1 ← List.take (2 * n) <$> ProbOracleComp.query ((), List.replicate n false)
  let tag2 ← List.take n <$>
    ProbOracleComp.query ((),
      if tag1 == List.replicate n false then
        List.replicate n false
      else
        tag1 ++ List.replicate n false ++ List.replicate n true)
  return tag2.headD false

theorem isOraclePPT_directReplyPrefixFreeAdv : IsOraclePPT encBool directReplyPrefixFreeAdv := by
  let EIn := encPair encUnary encBits
  have hq1 : IsOraclePPTOn EIn encBits
      (fun p : ℕ × List Bool =>
        List.take (2 * p.1) <$> ProbOracleComp.query ((), List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take () (by dsimp only [EIn]; polytime) (by dsimp only [EIn]; polytime)
  let EPost := encPair EIn encBits
  have hnPost : ComputableInPolyTime (fun x : (ℕ × List Bool) × List Bool => x.1.1)
      EPost encUnary := by dsimp only [EPost, EIn]; fun_prop
  have hmsg2 : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × List Bool =>
        if x.2 == List.replicate x.1.1 false then
          List.replicate x.1.1 false
        else
          x.2 ++ List.replicate x.1.1 false ++ List.replicate x.1.1 true)
      EPost encBits := by
    dsimp only [EPost, EIn]
    polytime
  have hq2 : IsOraclePPTOn EPost encBool
      (fun x : (ℕ × List Bool) × List Bool =>
        (fun tag2 : List Bool => tag2.headD false) <$>
          (List.take x.1.1 <$>
            ProbOracleComp.query ((),
              if x.2 == List.replicate x.1.1 false then
                List.replicate x.1.1 false
              else
                x.2 ++ List.replicate x.1.1 false ++ List.replicate x.1.1 true))) :=
    (IsOraclePPTOn.query_take () hmsg2 hnPost).map (by polytime)
  exact (hq1.bind_with hq2).isOraclePPT

theorem isPrefixFreeOn_directReplyPrefixFreeAdv (n : ℕ) :
    IsPrefixFreeOn (cbcBlockValid (fun _ => 3) n) n (directReplyPrefixFreeAdv n []) := by
  intro oracle _ horacleLen res hres x hx hxVal y hy _ hxy hpre
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [cbcBlockValid, Nat.mul_zero, Nat.le_zero, Bool.and_eq_true, decide_eq_true_eq,
      List.length_eq_zero_iff] at hxVal
    rcases hxVal with ⟨⟨hpos, -⟩, rfl⟩
    exact absurd hpos (Nat.lt_irrefl 0)
  · have hstep : directReplyPrefixFreeAdv n [] =
        .liftBind (.inr ((), List.replicate n false)) (fun raw1 =>
          let tag1 := raw1.take (2 * n)
          .liftBind (.inr ((),
              if tag1 == List.replicate n false then
                List.replicate n false
              else
                tag1 ++ List.replicate n false ++ List.replicate n true))
            (fun raw2 => .pure ((raw2.take n).headD false))) := by
      simp only [directReplyPrefixFreeAdv, ProbOracleComp.query, OracleComp.query,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      rfl
    rw [hstep] at hres
    simp only [wordQueryRunDist, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hres
    obtain ⟨_, ⟨_, rfl, rfl⟩, rfl⟩ := hres
    have hval0 : cbcBlockValid (fun _ => 3) n (List.replicate n false) = true := by
      simp only [cbcBlockValid, List.length_replicate, hn, decide_true, Nat.mod_self,
        beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      omega
    have hrawLen : (oracle (List.replicate n false)).length = n := horacleLen _ hval0
    let tag1 := (oracle (List.replicate n false)).take (2 * n)
    have htagLen : tag1.length = n := by
      dsimp only [tag1]
      rw [List.take_of_length_le (by omega), hrawLen]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    by_cases hbeq : (tag1 == List.replicate n false) = true
    · simp only [tag1, hbeq, ↓reduceIte] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> exact hxy rfl
    · have hneTag : tag1 ≠ List.replicate n false := fun h => hbeq (beq_iff_eq.mpr h)
      simp only [tag1, Bool.eq_false_iff.mpr hbeq, Bool.false_eq_true, ↓reduceIte] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hxy rfl
      · rw [hy, List.append_assoc] at hpre
        obtain ⟨rest, hEq⟩ := hpre
        have htakeEq := congrArg (List.take n) hEq
        rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
          List.take_append_of_le_length htagLen.ge, List.take_of_length_le htagLen.le] at htakeEq
        exact hneTag htakeEq.symm
      · rw [hx] at hpre
        have hlen := hpre.length_le
        simp only [List.length_append, List.length_replicate] at hlen
        omega
      · exact hxy (hx.trans hy.symm)

theorem isPrefixFreeOraclePPT_directReplyPrefixFreeAdv :
    IsPrefixFreeOraclePPT (cbcBlockValid (fun _ => 3)) id directReplyPrefixFreeAdv :=
  ⟨isOraclePPT_directReplyPrefixFreeAdv, isPrefixFreeOn_directReplyPrefixFreeAdv⟩

-- Against a wrong-length oracle `fun _ => []` at `n = 1`, `directReplyPrefixFreeAdv 1 []` issues
-- `[false]` then `[false, true]`, which is not prefix-free on `cbcBlockValid (fun _ => 3) 1`.
example :
    ∃ res ∈ (wordQueryRunDist (fun _ => []) (directReplyPrefixFreeAdv 1 [])).support,
      ¬ WordPrefixFree (cbcBlockValid (fun _ => 3) 1) res.2 := by
  refine ⟨(false, [[false], [false, true]]), ?_, ?_⟩
  · have hstep : directReplyPrefixFreeAdv 1 [] =
        .liftBind (.inr ((), [false])) (fun raw1 =>
          let tag1 := raw1.take 2
          .liftBind (.inr ((),
              if tag1 == [false] then [false] else tag1 ++ [false] ++ [true]))
            (fun raw2 => .pure ((raw2.take 1).headD false))) := by
      simp only [directReplyPrefixFreeAdv, Nat.mul_one, List.replicate, ProbOracleComp.query,
        OracleComp.query, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      rfl
    rw [hstep]
    simp [wordQueryRunDist]
  · intro hpf
    exact hpf [false] (by simp) (by decide) [false, true] (by simp) (by decide) (by decide)
      ⟨[true], rfl⟩

/-! ### 2. Adaptive Prefix-Free Distinguisher, Certified Reductions, and Concrete Bounds -/

/-- Adaptive 2-query word distinguisher: queries the 1-block message `1^n`, inspects the first tag
bit, and adaptively queries the 2-block message `0^n ++ 1^n` (when `true`) or `0^n ++ 0^n` (when
`false`). At every `n ≥ 1`, the first query starts with `true` while the second starts with
`false`, so neither is a prefix of the other; at `n = 0`, `cbcBlockValid` rejects all queries. -/
def adaptivePrefixFreeAdv : OracleDistinguisher := fun n _ => do
  let tag1 ← List.take n <$> ProbOracleComp.query ((), List.replicate n true)
  let tag2 ← List.take n <$>
    ProbOracleComp.query ((),
      if tag1.headD false then
        List.replicate n false ++ List.replicate n true
      else
        List.replicate (2 * n) false)
  return tag2.headD false

theorem isOraclePPT_adaptivePrefixFreeAdv : IsOraclePPT encBool adaptivePrefixFreeAdv := by
  let EIn := encPair encUnary encBits
  have hq1 : IsOraclePPTOn EIn encBits
      (fun p : ℕ × List Bool =>
        List.take p.1 <$> ProbOracleComp.query ((), List.replicate p.1 true)) :=
    IsOraclePPTOn.query_take () (by dsimp only [EIn]; polytime) (by dsimp only [EIn]; fun_prop)
  let EPost := encPair EIn encBits
  have hnPost : ComputableInPolyTime (fun x : (ℕ × List Bool) × List Bool => x.1.1)
      EPost encUnary := by dsimp only [EPost, EIn]; fun_prop
  have hmsg2 : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × List Bool =>
        if x.2.headD false then
          List.replicate x.1.1 false ++ List.replicate x.1.1 true
        else
          List.replicate (2 * x.1.1) false)
      EPost encBits := by
    dsimp only [EPost, EIn]
    polytime
  have hq2 : IsOraclePPTOn EPost encBool
      (fun x : (ℕ × List Bool) × List Bool =>
        (fun tag2 : List Bool => tag2.headD false) <$>
          (List.take x.1.1 <$>
            ProbOracleComp.query ((),
              if x.2.headD false then
                List.replicate x.1.1 false ++ List.replicate x.1.1 true
              else
                List.replicate (2 * x.1.1) false))) :=
    (IsOraclePPTOn.query_take () hmsg2 hnPost).map (by polytime)
  exact (hq1.bind_with hq2).isOraclePPT

theorem isQueryBounded_adaptivePrefixFreeAdv (n : ℕ) :
    (adaptivePrefixFreeAdv n []).IsQueryBounded 2 := by
  unfold adaptivePrefixFreeAdv
  have h1 : (List.take n <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
        ((), List.replicate n true)).IsQueryBounded 1 := by
    unfold ProbOracleComp.IsQueryBounded
    rw [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.isCostBounded_query _ _
  change OracleComp.IsCostBounded _ _ (1 + 1)
  refine h1.bind fun _ => ?_
  rw [bind_pure_comp, OracleComp.isCostBounded_map_iff, OracleComp.isCostBounded_map_iff]
  exact ProbOracleComp.isCostBounded_query _ _

private theorem head_replicate_true_ne_false {n : ℕ} (hn : 0 < n) (tail : List Bool) :
    ¬ (List.replicate n true).IsPrefix (List.replicate n false ++ tail) := by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
  rintro ⟨rest, hEq⟩
  simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at hEq
  exact Bool.false_ne_true hEq.1.symm

theorem isPrefixFreeOn_adaptivePrefixFreeAdv (n : ℕ) :
    IsPrefixFreeOn (cbcBlockValid (fun _ => 2) n) n (adaptivePrefixFreeAdv n []) := by
  intro oracle _ _ res hres x hx hxVal y hy _ hxy hpre
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [cbcBlockValid, Nat.mul_zero, Nat.le_zero, Bool.and_eq_true, decide_eq_true_eq,
      List.length_eq_zero_iff] at hxVal
    rcases hxVal with ⟨⟨hpos, -⟩, rfl⟩
    exact absurd hpos (Nat.lt_irrefl 0)
  · have hstep1 : adaptivePrefixFreeAdv n [] =
        .liftBind (.inr ((), List.replicate n true)) (fun raw1 =>
          .liftBind (.inr ((),
              if (raw1.take n).headD false then
                List.replicate n false ++ List.replicate n true
              else
                List.replicate (2 * n) false))
            (fun raw2 => .pure ((raw2.take n).headD false))) := by
      simp only [adaptivePrefixFreeAdv, ProbOracleComp.query, OracleComp.query,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      rfl
    rw [hstep1] at hres
    simp only [wordQueryRunDist, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hres
    obtain ⟨_, ⟨_, rfl, rfl⟩, rfl⟩ := hres
    let msg2 := if ((oracle (List.replicate n true)).take n).headD false then
        List.replicate n false ++ List.replicate n true
      else
        List.replicate (2 * n) false
    have hmsg2 : msg2 = List.replicate n false ++
        (if ((oracle (List.replicate n true)).take n).headD false then
          List.replicate n true
        else
          List.replicate n false) := by
      dsimp only [msg2]
      split_ifs
      · rfl
      · rw [Nat.two_mul, List.replicate_add]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · change y = msg2 at hy
      rw [hy, hmsg2] at hpre
      exact head_replicate_true_ne_false hn _ hpre
    · change x = msg2 at hx
      rw [hx, hmsg2] at hpre
      have hlen : (List.replicate n false ++ _).length ≤ (List.replicate n true).length :=
        hpre.length_le
      simp only [List.length_append, List.length_replicate] at hlen
      split_ifs at hlen <;> simp only [List.length_replicate] at hlen <;> omega
    · exact hxy (hx.trans hy.symm)

theorem isPrefixFreeOraclePPT_adaptivePrefixFreeAdv :
    IsPrefixFreeOraclePPT (cbcBlockValid (fun _ => 2)) id adaptivePrefixFreeAdv :=
  ⟨isOraclePPT_adaptivePrefixFreeAdv, isPrefixFreeOn_adaptivePrefixFreeAdv⟩

-- Certified reductions preserve `IsOraclePPT` with no assumptions on constructed objects.
example : IsOraclePPT encBool
    (cbcMacToPrfDistinguisher (fun _ => 2) adaptivePrefixFreeAdv) :=
  isOraclePPT_cbcMacToPrfDistinguisher (ComputableInPolyTime.const 2)
    isOraclePPT_adaptivePrefixFreeAdv

example : IsOraclePPT encBool
    (lengthPrependedToPrfDistinguisher (fun n => n + 1) adaptivePrefixFreeAdv) :=
  isOraclePPT_lengthPrependedToPrfDistinguisher (by polytime)
    isOraclePPT_adaptivePrefixFreeAdv

-- Non-vacuous concrete prefix-free CBC-MAC bound at `n = 16, Q = 2, ℓ = 2` (`16 / 65536 < 1`).
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length) :
    Game.advantage
        (ProbComp.eval
          (prfRealGameOn (cbcBlockValid (fun _ => 2)) (cbcMacFamily family)
            adaptivePrefixFreeAdv 16))
        (ProbComp.eval (prfIdealGameOn (cbcBlockValid (fun _ => 2)) id adaptivePrefixFreeAdv 16)) ≤
      Game.advantage
        (ProbComp.eval
          (prfRealGame id family
            (cbcMacToPrfDistinguisher (fun _ => 2) adaptivePrefixFreeAdv) 16))
        (ProbComp.eval
          (prfIdealGame id id
            (cbcMacToPrfDistinguisher (fun _ => 2) adaptivePrefixFreeAdv) 16)) +
      (2 : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ 2 / (2 * 2 ^ 16) ∧
    (2 : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ 2 / (2 * 2 ^ 16) < 1 :=
  ⟨advantage_cbcMac_le hlen (fun _ => 2) adaptivePrefixFreeAdv
      (isQueryBounded_adaptivePrefixFreeAdv 16)
      (isPrefixFreeOn_adaptivePrefixFreeAdv 16),
    by norm_num⟩

-- Non-vacuous concrete length-prepended CBC-MAC PRF bound at `n = 16, Q = 2, L = 3`
-- (`64 / 65536 < 1`).
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length) :
    Game.advantage
        (ProbComp.eval
          (prfRealGameOn (lpBlockValid (fun _ => 3)) (lengthPrependedCbcMacFamily family)
            adaptivePrefixFreeAdv 16))
        (ProbComp.eval
          (prfIdealGameOn (lpBlockValid (fun _ => 3)) id adaptivePrefixFreeAdv 16)) ≤
      Game.advantage
        (ProbComp.eval
          (prfRealGame id family
            (lengthPrependedToPrfDistinguisher (fun _ => 3) adaptivePrefixFreeAdv) 16))
        (ProbComp.eval
          (prfIdealGame id id
            (lengthPrependedToPrfDistinguisher (fun _ => 3) adaptivePrefixFreeAdv) 16)) +
      (2 : ℝ≥0) ^ 2 * ((3 : ℝ≥0) + 1) ^ 2 / (2 * 2 ^ 16) ∧
    (2 : ℝ≥0) ^ 2 * ((3 : ℝ≥0) + 1) ^ 2 / (2 * 2 ^ 16) < 1 :=
  ⟨advantage_lengthPrependedCbcMac_le hlen (fun _ => 3) adaptivePrefixFreeAdv (by decide)
      (isQueryBounded_adaptivePrefixFreeAdv 16),
    by norm_num⟩

/-! ### 3. Asymptotic PRF and MAC Security Instantiations -/

-- Prefix-free CBC-MAC security specialized to both `adaptivePrefixFreeAdv` and
-- `directReplyPrefixFreeAdv`.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval
        (prfRealGameOn (cbcBlockValid (fun _ => 2)) (cbcMacFamily family)
          adaptivePrefixFreeAdv n))
      (ProbComp.eval
        (prfIdealGameOn (cbcBlockValid (fun _ => 2)) id adaptivePrefixFreeAdv n))) ∧
    Negligible (fun n => Game.advantage
      (ProbComp.eval
        (prfRealGameOn (cbcBlockValid (fun _ => 3)) (cbcMacFamily family)
          directReplyPrefixFreeAdv n))
      (ProbComp.eval
        (prfIdealGameOn (cbcBlockValid (fun _ => 3)) id directReplyPrefixFreeAdv n))) :=
  ⟨(hF.prefixFreePRF_cbcMac (ComputableInPolyTime.const 2)).secure
      adaptivePrefixFreeAdv isPrefixFreeOraclePPT_adaptivePrefixFreeAdv,
    (hF.prefixFreePRF_cbcMac (ComputableInPolyTime.const 3)).secure
      directReplyPrefixFreeAdv isPrefixFreeOraclePPT_directReplyPrefixFreeAdv⟩

-- Variable-length PRF, SUFCMA, and EUFCMA (via `macSufCmaOn_iff_macEufCmaOn`) security for
-- length-prepended CBC-MAC up to `n + 1` blocks.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    PseudorandomFunctionOn (lpBlockValid (fun n => n + 1)) id
      (lengthPrependedCbcMacFamily family) ∧
    MACSUFCMAOn (lpBlockValid (fun n => n + 1)) (lengthPrependedCbcMacFamily family) ∧
    MACEUFCMAOn (lpBlockValid (fun n => n + 1)) (lengthPrependedCbcMacFamily family) := by
  have hL : ComputableInPolyTime (fun n => n + 1) encUnary encUnary := by polytime
  have hsuf := hF.macSufCmaOn_lengthPrependedCbcMac hL
  exact ⟨hF.prfOn_lengthPrependedCbcMac hL, hsuf, (macSufCmaOn_iff_macEufCmaOn _ _).mp hsuf⟩

-- Fixed-block `MACScheme.SUFCMA` and `.eufCma` for positive block counts and for 0-block
-- length-prepended CBC-MAC.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    (hℓ : ComputableInPolyTime (fun n => n + 1) encUnary encUnary) :
    (cbcFixedBlockMAC (fun n => n + 1) hℓ family hF.polyTime).SUFCMA ∧
    (cbcFixedBlockMAC (fun n => n + 1) hℓ family hF.polyTime).EUFCMA ∧
    (lengthPrependedBlockMAC (fun _ => 0) (ComputableInPolyTime.const 0)
      family hF.polyTime).SUFCMA := by
  have hsuf := hF.sufCma_cbcFixedBlockMAC hℓ (fun n => Nat.succ_pos n)
  exact ⟨hsuf, hsuf.eufCma,
    hF.sufCma_lengthPrependedBlockMAC (ComputableInPolyTime.const 0)⟩

/-! ### 4. Necessity of Prefix-Freeness / Length-Prepending: Variable-Length Forgery -/

-- Concrete instantiation on `xnorFamily` at `n = 2`: `cbcExtensionForger` wins with probability `1`
-- and unmodified `cbcMacFamily` fails `MACSUFCMAOn`, `MACEUFCMAOn`, and `PseudorandomFunctionOn`.
example :
    ProbComp.eval
      (macSufCmaGameOn (lpBlockValid (fun _ => 2)) (cbcMacFamily xnorFamily)
        cbcExtensionForger 2) = PMF.pure true :=
  eval_macSufCmaGameOn_cbcMacFamily_cbcExtensionForger length_xnorFamily (by decide)

example :
    ¬ MACSUFCMAOn (lpBlockValid (fun _ => 2)) (cbcMacFamily xnorFamily) ∧
    ¬ MACEUFCMAOn (lpBlockValid (fun _ => 2)) (cbcMacFamily xnorFamily) ∧
    ¬ PseudorandomFunctionOn (lpBlockValid (fun _ => 2)) id (cbcMacFamily xnorFamily) := by
  have hnsuf := not_macSufCmaOn_cbcMacFamily length_xnorFamily
  exact ⟨hnsuf, fun heuf => hnsuf ((macSufCmaOn_iff_macEufCmaOn _ _).mpr heuf),
    not_prfOn_cbcMacFamily length_xnorFamily⟩

end CslibFrontierTests.Crypto.ComputationalCBCMAC
