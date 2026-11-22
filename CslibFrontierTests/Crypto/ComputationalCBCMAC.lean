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
   `lengthPrependedBlockMAC` (including empty-message authentication, malformed-length rejection,
   and repeated identical oracle queries under `IsPrefixFreeOn`).
2. Explicit `IsOraclePPT` certificates and concrete non-vacuous numerical advantage bounds at
   `n = 16` for an adaptive 2-query prefix-free distinguisher on `cbcMacFamily` and for
   variable-length PRF and `SUFCMA` MAC security of `lengthPrependedCbcMacFamily`.
3. Asymptotic compositions from an arbitrary `PseudorandomFunction` for
   `PrefixFreePseudorandomFunctionOn`, `PseudorandomFunctionOn`, `PseudorandomFunctionOver`,
   `MACSUFCMAOn`, `MACEUFCMAOn`, and `MACScheme.SUFCMA`.
4. Computational 1-to-2-block length-extension attack (`extensionForger`, certified `IsOraclePPT`)
   showing that for *every* length-preserving `family` (including any `PseudorandomFunction`),
   unmodified `cbcMacFamily family` fails `MACSUFCMAOn (lpBlockValid (fun _ => 2))` and
   `MACEUFCMAOn (lpBlockValid (fun _ => 2))` with forgery probability `1` at every `n ≥ 1`, while
   `lengthPrependedCbcMacFamily family` is `MACSUFCMAOn`-secure on the exact same domain.
-/

public section

namespace CslibFrontierTests.Crypto.ComputationalCBCMAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### 1. Concrete Word-Level Evaluations and Model Boundaries -/

/-- Toy length-preserving block family `F_k(x) = ¬(k ⊕ x)` with `F_k(0^n) = ¬k`. -/
def xnorFamily (key query : List Bool) : List Bool :=
  List.zipWith (fun k q => !(xor k q)) key query

theorem computableInPolyTime_xnorFamily :
    ComputableInPolyTime (fun p : List Bool × List Bool => xnorFamily p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold xnorFamily
  exact ComputableInPolyTime.bitsZipWithInput (fun k q => !(xor k q))
    (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

theorem length_xnorFamily (key query : List Bool) (h : query.length = key.length) :
    (xnorFamily key query).length = key.length := by
  simp [xnorFamily, h]

-- Two-block basic CBC-MAC under `k = [true, false]` on `[false, true, true, true]`:
-- block 1 `[false, true]` gives `xnor [true, false] [false, true] = [false, false]`;
-- block 2 `[true, true]` gives `xnor [true, false] [true, true] = [true, false]`.
example : cbcMacFamily xnorFamily [true, false] [false, true, true, true] = [true, false] := by
  decide

-- `prependLengthWord` prepends the little-endian block count `2 = [false, true]` (width 2) and
-- encodes the empty message `[]` with zero block `[false, false]`.
example : prependLengthWord 2 [false, true, true, true] =
    [false, true, false, true, true, true] := by
  decide

example : prependLengthWord 2 [] = [false, false] := by
  decide

-- Length-prepended CBC-MAC authenticates the empty message `[]` by evaluating `F_k(0^n)`.
example : lengthPrependedCbcMacFamily xnorFamily [true, false] [] = [false, true] := by
  decide

-- `blockCountBlock` flattens to the exact little-endian bit list `BitString.lowBits`.
example : List.ofFn (blockCountBlock (n := 4) (L := 5) (by decide) ⟨3, by decide⟩) =
    [true, true, false, false] := by
  rw [ofFn_blockCountBlock]
  decide

/-- Concrete 2-block `MACScheme` built from `cbcFixedBlockMAC`. -/
noncomputable abbrev toyFixedMAC : MACScheme :=
  cbcFixedBlockMAC (fun _ => 2) (ComputableInPolyTime.const 2) xnorFamily
    computableInPolyTime_xnorFamily

/-- Concrete empty-message (`0`-block) `MACScheme` built from `lengthPrependedBlockMAC`. -/
noncomputable abbrev toyEmptyMsgMAC : MACScheme :=
  lengthPrependedBlockMAC (fun _ => 0) (ComputableInPolyTime.const 0) xnorFamily
    computableInPolyTime_xnorFamily

example : toyFixedMAC.verify [true, false] [false, true, true, true] [true, false] = true := by
  simp only [toyFixedMAC, cbcFixedBlockMAC_verify, beq_iff_eq]
  decide

example : toyEmptyMsgMAC.verify [true, false] [] [false, true] = true := by
  simp only [toyEmptyMsgMAC, lengthPrependedBlockMAC_verify, beq_iff_eq]
  decide

-- Subtle boundary 1: malformed-length signing requests and empty basic-CBC-MAC requests are
-- rejected without recording a message or making an underlying block query.
example : macSigningOracleOn (cbcBlockValid (fun _ => 2)) (cbcMacFamily xnorFamily) 2
    [true, false] ((), [true]) [] = pure ([], []) := by
  rfl

example : cbcMacQuery (fun _ => 2) 2 ((), []) = pure [] := by
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
    IsPrefixFreeOn (cbcBlockValid (fun _ => 2) n) (repeatSameBlockAdv n []) := by
  intro oracle _ res hres x hx _ y hy _ hxy _
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
    IsPrefixFreeOn (cbcBlockValid (fun _ => 2) n) (adaptivePrefixFreeAdv n []) := by
  intro oracle _ res hres x hx hxVal y hy _ hxy hpre
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
    IsPrefixFreeOraclePPT (cbcBlockValid (fun _ => 2)) adaptivePrefixFreeAdv :=
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
      (2 : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ 2 / 2 ^ 16 ∧
    (2 : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ 2 / 2 ^ 16 < 1 :=
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
      (2 : ℝ≥0) ^ 2 * ((3 : ℝ≥0) + 1) ^ 2 / 2 ^ 16 ∧
    (2 : ℝ≥0) ^ 2 * ((3 : ℝ≥0) + 1) ^ 2 / 2 ^ 16 < 1 :=
  ⟨advantage_lengthPrependedCbcMac_le hlen (fun _ => 3) adaptivePrefixFreeAdv (by decide)
      (isQueryBounded_adaptivePrefixFreeAdv 16),
    by norm_num⟩

/-! ### 3. Asymptotic PRF and MAC Security Instantiations -/

-- Prefix-free CBC-MAC security specialized to our concrete 2-query adaptive distinguisher.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    Negligible fun n => Game.advantage
      (ProbComp.eval
        (prfRealGameOn (cbcBlockValid (fun _ => 2)) (cbcMacFamily family)
          adaptivePrefixFreeAdv n))
      (ProbComp.eval
        (prfIdealGameOn (cbcBlockValid (fun _ => 2)) id adaptivePrefixFreeAdv n)) :=
  (hF.prefixFreePRF_cbcMac (ComputableInPolyTime.const 2)).secure
    adaptivePrefixFreeAdv isPrefixFreeOraclePPT_adaptivePrefixFreeAdv

-- Variable-length PRF, SUFCMA, and EUFCMA security for length-prepended CBC-MAC up to `n + 1`
-- blocks.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    PseudorandomFunctionOn (lpBlockValid (fun n => n + 1)) id
      (lengthPrependedCbcMacFamily family) ∧
    MACSUFCMAOn (lpBlockValid (fun n => n + 1)) (lengthPrependedCbcMacFamily family) ∧
    MACEUFCMAOn (lpBlockValid (fun n => n + 1)) (lengthPrependedCbcMacFamily family) := by
  have hL : ComputableInPolyTime (fun n => n + 1) encUnary encUnary := by polytime
  exact ⟨hF.prfOn_lengthPrependedCbcMac hL,
    hF.macSufCmaOn_lengthPrependedCbcMac hL,
    hF.macEufCmaOn_lengthPrependedCbcMac hL⟩

-- Fixed-block `MACScheme.SUFCMA` for positive block counts and for 0-block length-prepended
-- CBC-MAC.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    (cbcFixedBlockMAC (fun n => n + 1) (by polytime) family hF.polyTime).SUFCMA ∧
    (lengthPrependedBlockMAC (fun _ => 0) (ComputableInPolyTime.const 0)
      family hF.polyTime).SUFCMA :=
  ⟨hF.sufCma_cbcFixedBlockMAC (by polytime) (fun n => Nat.succ_pos n),
    hF.sufCma_lengthPrependedBlockMAC (ComputableInPolyTime.const 0)⟩

/-! ### 4. Necessity of Prefix-Freeness / Length-Prepending: Variable-Length Forgery -/

/-- Classic 1-query length-extension forger against unmodified zero-IV CBC-MAC
([BonehShoup2023], Section 6.4.3, printed pp. 230–231):
sign the 1-block zero message `0^n`, receive `t = F_k(0^n)`, and output the fresh 2-block forgery
`(0^n ++ t, t)`. Since `cbcMac(0^n ++ t) = F_k(F_k(0^n) ⊕ t) = F_k(t ⊕ t) = F_k(0^n) = t`, this
forges with probability `1` at every `n ≥ 1`. -/
def extensionForger : Forger := fun n _ =>
  (fun tag => (List.replicate n false ++ tag, tag)) <$>
    (List.take n <$> ProbOracleComp.query ((), List.replicate n false))

theorem isOraclePPT_extensionForger : IsOraclePPT (encPair encBits encBits) extensionForger := by
  have hq : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take p.1 <$> ProbOracleComp.query ((), List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take () (by polytime) (by fun_prop)
  unfold extensionForger
  exact (hq.map_with (by polytime)).isOraclePPT

private theorem zipWith_xor_self : ∀ l : List Bool,
    List.zipWith xor l l = List.replicate l.length false
  | [] => rfl
  | b :: bs => by
    simp only [List.zipWith_cons_cons, bne_self_eq_false, List.length_cons, List.replicate_succ,
      List.cons.injEq, true_and]
    exact zipWith_xor_self bs

private theorem cbcMacFamily_zero_append_tag {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    {n : ℕ} (hn : 0 < n) {sk : List Bool} (hsk : sk.length = n) :
    let tag := cbcMacFamily family sk (List.replicate n false)
    cbcMacFamily family sk (List.replicate n false ++ tag) = tag := by
  intro tag
  have htagLen : tag.length = n := by
    dsimp only [tag]
    rw [length_cbcMacFamily hlen, hsk]
  have hrows1 : BitString.listRows (n / n) n (List.replicate n false) =
      [List.replicate n false] := by
    rw [Nat.div_self hn]
    have hflat : BitString.listRows 1 n [List.replicate n false].flatten =
        [List.replicate n false] :=
      BitString.listRows_flatten [List.replicate n false] (by simp)
    simpa using hflat
  have hfamLen : (family sk (List.replicate n false)).length = n :=
    hsk ▸ hlen sk _ (by simp [hsk])
  have htag1 : tag = family sk (List.replicate n false) := by
    simp only [tag, cbcMacFamily, hsk, cbcMacWord, List.length_replicate, hrows1,
      List.foldl_cons, List.foldl_nil, zipWith_xor_self,
      List.take_of_length_le hfamLen.le]
  have hrows2 : BitString.listRows ((List.replicate n false ++ tag).length / n) n
      (List.replicate n false ++ tag) = [List.replicate n false, tag] := by
    have hdiv2 : (List.replicate n false ++ tag).length / n = 2 := by
      rw [List.length_append, List.length_replicate, htagLen, ← Nat.two_mul,
        Nat.mul_div_cancel _ hn]
    rw [hdiv2]
    have hflat : BitString.listRows 2 n [List.replicate n false, tag].flatten =
        [List.replicate n false, tag] :=
      BitString.listRows_flatten [List.replicate n false, tag] (by simp [htagLen])
    simpa using hflat
  rw [cbcMacFamily, hsk, cbcMacWord, hrows2]
  simp only [List.foldl_cons, List.foldl_nil, zipWith_xor_self, List.length_replicate,
    ← htag1, List.take_of_length_le htagLen.le, htagLen]

/-- At every `n ≥ 1`, `extensionForger` wins `macEufCmaGameOn` (and `macSufCmaGameOn`) against raw
`cbcMacFamily family` on `lpBlockValid (fun _ => 2)` with probability `1`. -/
theorem eval_macEufCmaGameOn_cbcMacFamily_extensionForger
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    {n : ℕ} (hn : 0 < n) :
    ProbComp.eval
      (macEufCmaGameOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family) extensionForger n) =
    PMF.pure true := by
  have hval1 : lpBlockValid (fun _ => 2) n (List.replicate n false) = true := by
    simp only [lpBlockValid, List.length_replicate, Nat.mod_self, beq_self_eq_true, Bool.true_and,
      decide_eq_true_eq]
    omega
  simp only [macEufCmaGameOn, extensionForger, Functor.map_map, OracleComp.interpret_map,
    StateT.run_map, ProbOracleComp.interpret_query, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_map, Function.comp_def]
  dsimp only [StateT.run, macSigningOracleOn]
  simp only [hval1, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
  trans PMF.bind (BitString.uniformList n) (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
    have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
    have htagLen : (cbcMacFamily family sk (List.replicate n false)).length = n := by
      rw [length_cbcMacFamily hlen, hskLen]
    have htake : (cbcMacFamily family sk (List.replicate n false)).take n =
        cbcMacFamily family sk (List.replicate n false) :=
      List.take_of_length_le htagLen.le
    rw [htake]
    have hval2 : lpBlockValid (fun _ => 2) n
        (List.replicate n false ++ cbcMacFamily family sk (List.replicate n false)) = true := by
      have hlen2 : (List.replicate n false ++
          cbcMacFamily family sk (List.replicate n false)).length = 2 * n := by
        rw [List.length_append, List.length_replicate, htagLen, Nat.two_mul]
      simp [lpBlockValid, hlen2, Nat.mul_mod_left]
    have hne : List.replicate n false ++ cbcMacFamily family sk (List.replicate n false) ≠
        List.replicate n false := by
      intro hEq
      have hlenEq := congrArg List.length hEq
      rw [List.length_append, List.length_replicate, htagLen] at hlenEq
      omega
    have hforge := cbcMacFamily_zero_append_tag hlen hn hskLen
    simp [hval2, hne, hforge]
  · exact PMF.bind_const _ _

/-- For **every** length-preserving family `family` (including any `PseudorandomFunction`), raw
`cbcMacFamily family` without prefix-freeness or length-prepending fails
`MACEUFCMAOn (lpBlockValid (fun _ => 2))`. -/
theorem not_macEufCmaOn_cbcMacFamily {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length) :
    ¬ MACEUFCMAOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family) := by
  intro hsec
  have hneg := hsec extensionForger isOraclePPT_extensionForger
  have hev : ∀ᶠ n in Filter.atTop,
      (1 : ℝ≥0) ≤ Game.advantage
        (ProbComp.eval
          (macEufCmaGameOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family) extensionForger n))
        (PMF.pure false) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [eval_macEufCmaGameOn_cbcMacFamily_extensionForger hlen hn, Game.advantage_pure_false,
      Game.succProbability]
    simp
  have h1 : Negligible (fun _ : ℕ => (1 : ℝ≥0)) := negligible_of_eventually_le hneg hev
  rcases Filter.eventually_atTop.mp ((h1 0).eventually (gt_mem_nhds zero_lt_one)) with ⟨N, hN⟩
  have hlt := hN N le_rfl
  norm_num at hlt

/-- Raw `cbcMacFamily family` likewise fails strong `MACSUFCMAOn (lpBlockValid (fun _ => 2))` for
every length-preserving `family`, whereas `lengthPrependedCbcMacFamily family` satisfies
`MACSUFCMAOn (lpBlockValid (fun _ => 2))` whenever `PseudorandomFunction family`. -/
theorem not_macSufCmaOn_cbcMacFamily {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length) :
    ¬ MACSUFCMAOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family) := by
  intro hsec
  refine not_macEufCmaOn_cbcMacFamily hlen fun adversary hadversary => ?_
  refine (hsec adversary hadversary).congr fun n => ?_
  dsimp only
  rw [← eval_macSufCmaGameOn_eq_macEufCmaGameOn]

end CslibFrontierTests.Crypto.ComputationalCBCMAC
