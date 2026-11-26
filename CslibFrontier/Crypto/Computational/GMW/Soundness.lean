/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GMW.Protocol
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.GetD

/-!
# Completeness and soundness of the 3-copy GMW protocol

This module proves perfect completeness (`acceptProb_gmwVerifier_gmwProver`) and unconditional
soundness (`acceptProb_gmwVerifier_le`) for `Cslib.Crypto.GMW.gmwVerifier`.

* **Completeness.** When `ThreeSAT.verifier (f a, w) = true`, every selectively opened copy of the
  honest prover's committed bits matches `simBits` (`naorMaskBits_realBits`) and passes
  `verifyCopyBits` and `verifyCommitments`, so `gmwVerifier` accepts `gmwProver` with probability
  `1`.
* **Soundness.** Whenever Naor's commitment scheme is statistically binding on the first-round
  receiver string `r` (`NaorBinding generator s (BitString.listRow m 0 r)`), if a prover can produce
  accepting second-round openings for two distinct 3-bit challenges `x₁ ≠ x₂` on the same
  first-round commitment transcript `commitReply`, then those two challenges differ in at least one
  coordinate `j ∈ {0, 1, 2}`: one transcript opens copy `j` under challenge `false` (revealing `m`
  and the full clause truth tables `tableBits φ m`) and the other opens copy `j` under challenge
  `true` (revealing `v` and confirming that the active entry `gmwActiveIdx` of every clause is
  `true`), while binding forces the opened active entries to agree with `tableBits φ m`.
  Consequently `v ⊕ m` satisfies `φ` (`mem_ThreeSAT_of_verifyTranscript_ne`), so when
  `f a ∉ ThreeSAT` at most one of the `8` challenges can be answered after any binding `r`,
  bounding the acceptance probability by `naorBindingProb + 1 / 8 ≤ 1 / 3`
  (`acceptProb_gmwVerifier_le`).

## Main results

* `Cslib.Crypto.GMW.acceptProb_gmwVerifier_gmwProver`: perfect completeness (`acceptProb = 1`) for
  any valid `ThreeSAT` witness.
* `Cslib.Crypto.GMW.mem_ThreeSAT_of_verifyTranscript_ne`: witness extraction from two accepting
  transcripts with distinct 3-bit challenges on a binding receiver string.
* `Cslib.Crypto.GMW.acceptProb_gmwVerifier_le`: soundness bound `acceptProb ≤ 1 / 3` when
  `f a ∉ ThreeSAT` and `∀ k, 3 * k + 1 ≤ length k`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
-/

public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL
open scoped NNReal ENNReal

/-! ### Completeness of `gmwVerifier` with `gmwProver` -/

private theorem length_mem_naorCommitSplit_true {generator : List Bool → List Bool} {m : ℕ}
    {r bits : List Bool} {seeds : List (List Bool)} (hseeds : seeds.length = bits.length)
    (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    ∀ u ∈ naorCommitSplit generator r (List.replicate bits.length true) bits seeds [],
      u.length = m := by
  rw [naorCommitSplit_eq_map]; intro u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu; rw [List.mem_range] at hi
  have hflag : (List.replicate bits.length true).getD i false = true := by simp [List.getD, hi]
  have hi_seeds : i < seeds.length := hseeds ▸ hi
  have hmem : seeds.getD i [] ∈ seeds := by simp [List.getD, List.getElem?_eq_getElem hi_seeds]
  rw [hflag, naorCommitAt_true, length_naorCommit, hgen _ hmem]

private theorem length_flatten_naorCommitSplit_true {generator : List Bool → List Bool} {m : ℕ}
    (r : List Bool) {bits : List Bool} {seeds : List (List Bool)}
    (hseeds : seeds.length = bits.length) (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    (naorCommitSplit generator (BitString.listRow m 0 r)
      (List.replicate bits.length true) bits seeds []).flatten.length = bits.length * m := by
  rw [List.length_flatten, List.map_congr_left
    (length_mem_naorCommitSplit_true (r := BitString.listRow m 0 r) hseeds hgen), List.map_const']
  simp [naorCommitSplit_eq_map]

private theorem proverReply1_true_eq_flatten {generator : List Bool → List Bool} {m : ℕ}
    (r : List Bool) {bits : List Bool} {seeds : List (List Bool)}
    (hseeds : seeds.length = bits.length) (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    proverReply1 generator m r (List.replicate bits.length true) bits seeds [] =
      (naorCommitSplit generator (BitString.listRow m 0 r)
        (List.replicate bits.length true) bits seeds []).flatten := by
  simp [proverReply1,
    List.take_of_length_le (length_flatten_naorCommitSplit_true r hseeds hgen).le]

private theorem length_proverReply1_true {generator : List Bool → List Bool} {m : ℕ}
    {r bits : List Bool} {seeds : List (List Bool)} (hseeds : seeds.length = bits.length)
    (hgen : ∀ seed ∈ seeds, (generator seed).length = m) :
    (proverReply1 generator m r (List.replicate bits.length true) bits seeds []).length =
      bits.length * m := by
  rw [proverReply1_true_eq_flatten r hseeds hgen,
    length_flatten_naorCommitSplit_true r hseeds hgen]

private theorem length_proverReply2 (s : ℕ) (φ : CNF ℕ) {ch bits : List Bool}
    (seeds : List (List Bool)) (hbits : bits.length = totalLen φ) :
    (proverReply2 s φ ch bits seeds).length = totalLen φ * (s + 1) := by
  rw [length_proverReply2_any, hbits]

private theorem verifyTranscript_honest {generator : List Bool → List Bool} {s m : ℕ}
    {φ : CNF ℕ} {w m₀ m₁ m₂ r ch : List Bool} {seeds : List (List Bool)}
    (hw : ThreeSAT.verifier (φ, w) = true) (hseeds : seeds.length = totalLen φ)
    (hseed_len : ∀ seed ∈ seeds, seed.length = s)
    (hgen_len : ∀ seed ∈ seeds, (generator seed).length = m) :
    verifyTranscript generator s m φ r
      (proverReply1 generator m r (List.replicate (totalLen φ) true)
        (realBits φ w m₀ m₁ m₂) seeds []) ch
      (proverReply2 s φ ch (realBits φ w m₀ m₁ m₂) seeds) = true := by
  let K := totalLen φ
  let bits := realBits φ w m₀ m₁ m₂
  have hbits_len : bits.length = K := length_realBits φ w m₀ m₁ m₂
  let flags := allOpenFlags φ ch bits
  have hmask_len : (naorMaskBits flags bits).length = K := by simp [K, bits]
  have htake : (proverReply2 s φ ch bits seeds).take K = naorMaskBits flags bits := by
    simp [proverReply2, K, flags, bits, List.take_left' hmask_len]
  have hdrop : (proverReply2 s φ ch bits seeds).drop K =
      (naorSelectSeeds s flags bits seeds).flatten := by
    simp [proverReply2, K, flags, bits, List.drop_left' hmask_len]
  have hmask_eq := naorMaskBits_realBits (m₀ := m₀) (m₁ := m₁) (m₂ := m₂) ch hw
  have hflags_eq : allOpenFlags φ ch (naorMaskBits flags bits) = flags :=
    hmask_eq ▸ (allOpenFlags_realBits φ ch w m₀ m₁ m₂).symm
  dsimp only [verifyTranscript, K, bits, flags] at htake hdrop hflags_eq ⊢
  rw [htake, hdrop, hflags_eq]
  refine (Bool.and_eq_true _ _).mpr ⟨by
    simp only [((Bool.and_eq_true _ _).mp hw).1, hmask_eq, gmwCopy0_simBits, gmwCopy1_simBits,
      gmwCopy2_simBits, verifyCopyBits_simCopyBits, Bool.and_self], ?_⟩
  simp only [verifyCommitments, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq]
  intro i hi
  by_cases hfi : flags.getD i false = true
  · right
    have hi_bits : i < bits.length := hbits_len ▸ hi
    have hseed_mem : seeds.getD i [] ∈ seeds := by
      simp [List.getD, List.getElem?_eq_getElem (hseeds ▸ hi)]
    have hseed_i : BitString.listRow s i (naorSelectSeeds s flags bits seeds).flatten =
        seeds.getD i [] := by
      rw [BitString.listRow_flatten (fun w hw => length_mem_naorSelectSeeds hw) (by simp [hi_bits]),
        getD_naorSelectSeeds s flags bits seeds i hi_bits, hfi]
      simp only [↓reduceIte, BitString.listRow, Nat.zero_mul, List.drop_zero,
        List.take_left' (hseed_len _ hseed_mem)]
    have hcommit_i : BitString.listRow m i
          (proverReply1 generator m r (List.replicate K true) bits seeds []) =
        naorCommit generator (BitString.listRow m 0 r) (bits.getD i false) (seeds.getD i []) := by
      have hmem := length_mem_naorCommitSplit_true
        (r := BitString.listRow m 0 r) (hseeds.trans hbits_len.symm) hgen_len
      rw [← hbits_len, proverReply1_true_eq_flatten r (hseeds.trans hbits_len.symm) hgen_len,
        BitString.listRow_flatten hmem (by simp [hi_bits]),
        getD_naorCommitSplit _ _ _ _ _ _ i hi_bits]
      simp [List.getD, hi_bits, naorCommitAt_true]
    rw [getD_naorMaskBits, hfi, Bool.true_and, hseed_i, hcommit_i]
  · left; exact Bool.eq_false_iff.mpr hfi

private theorem length_mem_support_replicate_sampleList {K s : ℕ} {seeds : List (List Bool)}
    (hseeds : seeds ∈ (ProbComp.eval (OracleComp.replicate K (BitString.sampleList s))).support) :
    seeds.length = K ∧ ∀ seed ∈ seeds, seed.length = s := by
  induction K generalizing seeds with
  | zero =>
    supp_cases hseeds [OracleComp.replicate_zero]
    simp
  | succ K ih =>
    supp_cases hseeds [OracleComp.replicate_succ, BitString.eval_sampleList] with
      ⟨seed, hseed, rest, hrest, rfl⟩
    obtain ⟨hrest_len, hrest_mem⟩ := ih hrest
    exact ⟨by simp [hrest_len], List.forall_mem_cons.mpr
      ⟨BitString.length_of_mem_support_uniformList hseed, hrest_mem⟩⟩

/-- **Completeness of the GMW protocol.** When `ThreeSAT.verifier (f a, w) = true`, the honest
prover `gmwProver` makes `gmwVerifier` accept with probability `1`. -/
theorem acceptProb_gmwVerifier_gmwProver {α : Type} {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ seed, (generator seed).length = length seed.length)
    (f : α → CNF ℕ) (n : ℕ) (a : α) {w : List Bool}
    (hw : ThreeSAT.verifier (f a, w) = true) :
    acceptProb (gmwVerifier generator length f n a)
      (gmwProver generator (n + 7) (length (n + 7)) (f a) w) = 1 := by
  let φ := f a; let s := n + 7; let m := length s; let K := totalLen φ
  rw [acceptProb, run_gmwProver_fst]
  let prog : ProbComp Bool := do
    let coins ← sampleHonestCoins s φ w
    Prod.fst <$> runTwoRound (honestReply1 generator m φ coins)
      (honestReply2 s φ coins) (gmwVerifier generator length f n a) .init
  change ProbComp.eval prog true = 1
  have hfalse : ProbComp.eval prog false = 0 := by
    rw [PMF.apply_eq_zero_iff]
    intro hmem
    supp_cases hmem [prog] with ⟨coins, hcoins, ⟨_, _⟩, hrun, rfl⟩
    supp_cases hcoins [sampleHonestCoins, BitString.eval_sampleList] with
      ⟨m₀, -, m₁, -, m₂, -, seeds, hseeds, rfl⟩
    supp_cases hrun [gmwVerifier, BitString.eval_sampleList, runTwoRound_bind,
      runTwoRound_sample, runTwoRound_map, runTwoRound_query, runTwoRound_pure, Prod.map_apply]
      with ⟨⟨r, _⟩, ⟨_, -, ⟨⟩⟩, ⟨_, _⟩, ⟨rfl, rfl⟩, ⟨ch, _⟩, ⟨_, hch, ⟨⟩⟩, ⟨_, _⟩, ⟨rfl, rfl⟩,
        hfalse_eq, -⟩
    dsimp only [twoRoundStep, TwoRoundState.init, beq_self_eq_true, Nat.reduceBEq, ↓reduceIte,
      id_eq] at hfalse_eq
    obtain ⟨hseeds_len, hseeds_mem⟩ := length_mem_support_replicate_sampleList hseeds
    have hch_len : ch.length = 3 := BitString.length_of_mem_support_uniformList hch
    have hch_row : BitString.listRow 3 0 ch = ch := by
      simp [BitString.listRow, List.take_left' hch_len]
    have hgen_len : ∀ seed ∈ seeds, (generator seed).length = m := fun seed hseed => by
      rw [hlen, hseeds_mem seed hseed]
    have hr1_len :
        (honestReply1 generator m φ ⟨realBits φ w m₀ m₁ m₂, seeds⟩ r).length = K * m := by
      simpa [honestReply1, K, length_realBits] using length_proverReply1_true (r := r)
        (hseeds_len.trans (length_realBits φ w m₀ m₁ m₂).symm) hgen_len
    have hr2_len :
        (honestReply2 s φ ⟨realBits φ w m₀ m₁ m₂, seeds⟩ ch).length = K * (s + 1) := by
      simpa [honestReply2, K] using length_proverReply2 s φ seeds (length_realBits φ w m₀ m₁ m₂)
    rw [hch_row, List.take_of_length_le hr1_len.le, List.take_of_length_le hr2_len.le] at hfalse_eq
    exact Bool.false_ne_true (hfalse_eq.trans (verifyTranscript_honest (m₀ := m₀) (m₁ := m₁)
      (m₂ := m₂) (r := r) (ch := ch) hw hseeds_len hseeds_mem hgen_len))
  simpa [tsum_bool, hfalse] using PMF.tsum_coe (ProbComp.eval prog)

/-! ### Soundness of `gmwVerifier` against arbitrary provers -/

private theorem satisfiable_of_verifyCopyBits {φ : CNF ℕ} {copy₀ copy₁ : List Bool}
    (hwidth : ∀ c ∈ φ, c.length ≤ 3)
    (h₀ : verifyCopyBits φ false copy₀ = true)
    (h₁ : verifyCopyBits φ true copy₁ = true)
    (hagree : ∀ i < copyLen φ,
      (copyOpenFlags φ false copy₀).getD i false = true →
      (copyOpenFlags φ true copy₁).getD i false = true →
      copy₀.getD i false = copy₁.getD i false) :
    φ.Satisfiable := by
  let m := mPart φ copy₀
  let v := vPart φ copy₁
  have htab₀ : tablePart φ copy₀ = tableBits φ m := by
    simpa [verifyCopyBits, m] using h₀
  have htab₁ : ∀ j < 8 * φ.length,
      (activeTableFlags φ v).getD j false = true → (tablePart φ copy₁).getD j false = true := by
    simp only [verifyCopyBits, ↓reduceIte, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, Bool.not_eq_true'] at h₁
    exact fun j hj hact => (h₁ j hj).resolve_left (Bool.ne_false_iff.mpr hact)
  have htab_eq : ∀ j < 8 * φ.length,
      (activeTableFlags φ v).getD j false = true → (tableBits φ m).getD j false = true := by
    intro j hj hact
    have hj_len : 2 * φ.vars.length + j < copyLen φ := by unfold copyLen; omega
    have hle (b₁ b₂ : Bool) :
        (List.replicate φ.vars.length b₁ ++ List.replicate φ.vars.length b₂).length ≤
          2 * φ.vars.length + j := by simp [Nat.two_mul]
    have hflag₀ : (copyOpenFlags φ false copy₀).getD (2 * φ.vars.length + j) false = true := by
      simp only [copyOpenFlags, Bool.false_eq_true, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (hle _ _)]
      simp [List.getD_eq_getElem?_getD, hj, Nat.two_mul]
    have hflag₁ : (copyOpenFlags φ true copy₁).getD (2 * φ.vars.length + j) false = true := by
      simp only [copyOpenFlags, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (hle _ _)]
      simpa [Nat.two_mul] using hact
    rw [← htab₀, tablePart, List.getD_take_drop copy₀ _ hj,
      hagree _ hj_len hflag₀ hflag₁, ← List.getD_take_drop copy₁ _ hj]
    exact htab₁ j hj hact
  refine ⟨fun x => varBit φ v x ^^ varBit φ m x, CNF.eval_eq_true_iff _ _ |>.mpr ?_⟩
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  let t := gmwActiveIdx
    (varBit φ v (φ[k].getD 0 (0, false)).1)
    (varBit φ v (φ[k].getD 1 (0, false)).1)
    (varBit φ v (φ[k].getD 2 (0, false)).1)
  have ht : t < 8 := gmwActiveIdx_lt_eight _ _ _
  have hkt : k * 8 + t < 8 * φ.length := by omega
  have hrow (f : Clause ℕ → List Bool) (hf : ∀ c, (f c).length = 8) :
      BitString.listRow 8 k (φ.map f).flatten = f φ[k] := by
    rw [BitString.listRow_flatten (by simp [hf]) (by simpa using hk)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hact_true : (activeTableFlags φ v).getD (k * 8 + t) false = true := by
    rw [← BitString.getD_listRow (row := k) ht, activeTableFlags,
      hrow _ (fun _ => by simp), getD_clauseActiveRow φ v φ[k] ht]
    simp [t]
  have htab_true := htab_eq (k * 8 + t) hkt hact_true
  rw [← BitString.getD_listRow (row := k) ht, tableBits,
    hrow _ (fun _ => by simp), getD_clauseTableRow φ m φ[k] ht] at htab_true
  simp only [t, gmwBit0Of8_gmwActiveIdx, gmwBit1Of8_gmwActiveIdx,
    gmwBit2Of8_gmwActiveIdx] at htab_true
  rwa [← clauseEvalBits_eq_eval (hwidth φ[k] hc) (fun x => varBit φ v x ^^ varBit φ m x)]

private theorem getD_allOpenFlags_copy0 (φ : CNF ℕ) (ch bits : List Bool) {i : ℕ}
    (hi : i < copyLen φ) :
    (allOpenFlags φ ch bits).getD i false =
      (copyOpenFlags φ (ch.getD 0 false) (gmwCopy0 φ bits)).getD i false := by
  simp only [allOpenFlags, List.append_assoc]
  exact List.getD_append _ _ _ _ (by simpa using hi)

private theorem getD_allOpenFlags_copy1 (φ : CNF ℕ) (ch bits : List Bool) {i : ℕ}
    (hi : i < copyLen φ) :
    (allOpenFlags φ ch bits).getD (copyLen φ + i) false =
      (copyOpenFlags φ (ch.getD 1 false) (gmwCopy1 φ bits)).getD i false := by
  simp only [allOpenFlags, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ ((length_copyOpenFlags _ _ _).trans_le (Nat.le_add_right _ i)),
    length_copyOpenFlags, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ ((length_copyOpenFlags _ _ _).symm ▸ hi)]

private theorem getD_allOpenFlags_copy2 (φ : CNF ℕ) (ch bits : List Bool) (i : ℕ) :
    (allOpenFlags φ ch bits).getD (2 * copyLen φ + i) false =
      (copyOpenFlags φ (ch.getD 2 false) (gmwCopy2 φ bits)).getD i false := by
  have hlen :
      (copyOpenFlags φ (ch.getD 0 false) (gmwCopy0 φ bits) ++
        copyOpenFlags φ (ch.getD 1 false) (gmwCopy1 φ bits)).length = 2 * copyLen φ := by
    rw [List.length_append, length_copyOpenFlags, length_copyOpenFlags, Nat.two_mul]
  rw [allOpenFlags, List.getD_append_right _ _ _ _ (hlen ▸ Nat.le_add_right _ _), hlen,
    Nat.add_sub_cancel_left]

private theorem verifyCommitments_eq_of_true {generator : List Bool → List Bool} {s m : ℕ}
    {φ : CNF ℕ} {r flags₀ flags₁ commitReply opened₀ opened₁ seeds₀ seeds₁ : List Bool}
    (hbind : NaorBinding generator s (BitString.listRow m 0 r))
    (hc₀ : verifyCommitments generator s m φ r flags₀ commitReply opened₀ seeds₀ = true)
    (hc₁ : verifyCommitments generator s m φ r flags₁ commitReply opened₁ seeds₁ = true)
    {idx : ℕ} (hidx : idx < totalLen φ)
    (hf₀ : flags₀.getD idx false = true) (hf₁ : flags₁.getD idx false = true) :
    opened₀.getD idx false = opened₁.getD idx false := by
  simp only [verifyCommitments, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hc₀ hc₁
  have h₀ := (hc₀ idx hidx).resolve_left (by rw [hf₀]; decide)
  have h₁ := (hc₁ idx hidx).resolve_left (by rw [hf₁]; decide)
  exact hbind.eq_of_naorCommit_eq (BitString.length_listRow s idx seeds₀)
    (BitString.length_listRow s idx seeds₁) (h₀.trans h₁.symm)

private theorem mem_ThreeSAT_of_verifyTranscript_false_true
    {generator : List Bool → List Bool} {s m : ℕ} {φ : CNF ℕ}
    {r commitReply ch₀ ch₁ openReply₀ openReply₁ : List Bool}
    (hbind : NaorBinding generator s (BitString.listRow m 0 r))
    (hv₀ : verifyTranscript generator s m φ r commitReply ch₀ openReply₀ = true)
    (hv₁ : verifyTranscript generator s m φ r commitReply ch₁ openReply₁ = true)
    (hdiff :
      (ch₀.getD 0 false = false ∧ ch₁.getD 0 false = true) ∨
      (ch₀.getD 1 false = false ∧ ch₁.getD 1 false = true) ∨
      (ch₀.getD 2 false = false ∧ ch₁.getD 2 false = true)) :
    φ ∈ ThreeSAT := by
  let K := totalLen φ
  let opened₀ := openReply₀.take K
  let opened₁ := openReply₁.take K
  simp only [verifyTranscript, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv₀ hv₁
  obtain ⟨⟨⟨⟨hwidth, hv₀_0⟩, hv₀_1⟩, hv₀_2⟩, hc₀⟩ := hv₀
  obtain ⟨⟨⟨⟨_, hv₁_0⟩, hv₁_1⟩, hv₁_2⟩, hc₁⟩ := hv₁
  refine ⟨hwidth, ?_⟩
  rcases hdiff with ⟨hb₀, hb₁⟩ | ⟨hb₀, hb₁⟩ | ⟨hb₀, hb₁⟩
  · refine satisfiable_of_verifyCopyBits hwidth (hb₀ ▸ hv₀_0) (hb₁ ▸ hv₁_0) fun i hi hf₀ hf₁ => ?_
    simpa [gmwCopy0, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi] using
      verifyCommitments_eq_of_true hbind hc₀ hc₁ (idx := i)
        (by simp only [totalLen]; omega) (by rwa [getD_allOpenFlags_copy0 φ ch₀ opened₀ hi, hb₀])
        (by rwa [getD_allOpenFlags_copy0 φ ch₁ opened₁ hi, hb₁])
  · refine satisfiable_of_verifyCopyBits hwidth (hb₀ ▸ hv₀_1) (hb₁ ▸ hv₁_1) fun i hi hf₀ hf₁ => ?_
    simpa only [gmwCopy1, List.getD_take_drop _ _ hi] using
      verifyCommitments_eq_of_true hbind hc₀ hc₁ (idx := copyLen φ + i)
        (by simp only [totalLen]; omega) (by rwa [getD_allOpenFlags_copy1 φ ch₀ opened₀ hi, hb₀])
        (by rwa [getD_allOpenFlags_copy1 φ ch₁ opened₁ hi, hb₁])
  · refine satisfiable_of_verifyCopyBits hwidth (hb₀ ▸ hv₀_2) (hb₁ ▸ hv₁_2) fun i hi hf₀ hf₁ => ?_
    simpa only [gmwCopy2, List.getD_take_drop _ _ hi] using
      verifyCommitments_eq_of_true hbind hc₀ hc₁ (idx := 2 * copyLen φ + i)
        (by simp only [totalLen]; omega) (by rwa [getD_allOpenFlags_copy2 φ ch₀ opened₀ i, hb₀])
        (by rwa [getD_allOpenFlags_copy2 φ ch₁ opened₁ i, hb₁])

/-- If a first-round commitment transcript `commitReply` under a binding receiver string `r` admits
accepting second-round openings for two distinct 3-bit challenges `x₁ ≠ x₂`, then `φ ∈ ThreeSAT`. -/
theorem mem_ThreeSAT_of_verifyTranscript_ne
    {generator : List Bool → List Bool} {s m : ℕ} {φ : CNF ℕ}
    {r commitReply openReply₁ openReply₂ : List Bool} {x₁ x₂ : BitString 3}
    (hbind : NaorBinding generator s (BitString.listRow m 0 r))
    (hne : x₁ ≠ x₂)
    (hv₁ : verifyTranscript generator s m φ r commitReply (List.ofFn x₁) openReply₁ = true)
    (hv₂ : verifyTranscript generator s m φ r commitReply (List.ofFn x₂) openReply₂ = true) :
    φ ∈ ThreeSAT := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have key {y₁ y₂ : BitString 3} {o₁ o₂ : List Bool}
      (h₁ : verifyTranscript generator s m φ r commitReply (List.ofFn y₁) o₁ = true)
      (h₂ : verifyTranscript generator s m φ r commitReply (List.ofFn y₂) o₂ = true)
      (hy₁ : y₁ j = false) (hy₂ : y₂ j = true) : φ ∈ ThreeSAT :=
    mem_ThreeSAT_of_verifyTranscript_false_true hbind h₁ h₂ (by fin_cases j <;> simp_all)
  cases h₁ : x₁ j <;> cases h₂ : x₂ j <;>
    first | exact absurd (h₁.trans h₂.symm) hj | exact key hv₁ hv₂ h₁ h₂ | exact key hv₂ hv₁ h₂ h₁

private theorem sum_le_of_subsingleton_support {ι : Type*} [Fintype ι]
    {f : ι → ℝ≥0∞} {c : ℝ≥0∞} (hle : ∀ i, f i ≤ c)
    (hsub : ∀ i₁ i₂, f i₁ ≠ 0 → f i₂ ≠ 0 → i₁ = i₂) :
    ∑ i, f i ≤ c := by
  classical
  by_cases hex : ∃ i₀, f i₀ ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hex
    rw [Finset.sum_eq_single i₀
      (fun i _ hne => Decidable.byContradiction fun hfi => hne (hsub i i₀ hfi hi₀))
      (fun h => False.elim (h (Finset.mem_univ i₀)))]
    exact hle i₀
  · simp_all

/-- **Soundness of the GMW protocol.** When `f a ∉ ThreeSAT` and `3 * k + 1 ≤ length k` for all `k`,
no unbounded stateful prover `P` makes `gmwVerifier` accept with probability greater than
`1 / 3`. -/
theorem acceptProb_gmwVerifier_le {α : Type} {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ seed, (generator seed).length = length seed.length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (f : α → CNF ℕ) (n : ℕ) (a : α) (hnot : f a ∉ ThreeSAT) (P : Prover Unit) :
    acceptProb (gmwVerifier generator length f n a) P ≤ 1 / 3 := by
  let φ := f a
  let s := n + 7
  let m := length s
  let K := totalLen φ
  let step3 (r commitReply ch : List Bool) : WordOracleComp Unit Bool :=
    (List.take (K * (s + 1)) <$> ProbOracleComp.query ((), ch)) >>= fun openReply =>
      pure (verifyTranscript generator s m φ r commitReply ch openReply)
  let step2 (r commitReply : List Bool) : WordOracleComp Unit Bool :=
    ProbOracleComp.sample (BitString.sampleList 3) >>= step3 r commitReply
  let step1 (r : List Bool) : WordOracleComp Unit Bool :=
    (List.take (K * m) <$> ProbOracleComp.query ((), r)) >>= step2 r
  have hstep2_le : ∀ r commitReply state₁,
      NaorBinding generator s (BitString.listRow m 0 r) →
      ProbOracleComp.acceptProbWith P.respond (step2 r commitReply) state₁ ≤ 1 / 8 := by
    intro r commitReply state₁ hbind
    rw [ProbOracleComp.acceptProbWith, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
      BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, PMF.map_bind,
      PMF.bind_map, PMF.bind_apply, tsum_fintype]
    refine sum_le_of_subsingleton_support
      (fun x => by
        simpa [Probability.PMF.uniformOfFintype_apply, ProbOracleComp.acceptProbWith] using
          (mul_le_of_le_one_right'
            (ProbOracleComp.acceptProbWith_le_one P.respond
              (step3 r commitReply (List.ofFn x)) state₁) : (1 / 8 : ℝ≥0∞) * _ ≤ 1 / 8))
      (fun x₁ x₂ hx₁ hx₂ => ?_)
    by_contra hne
    have hv {x : BitString 3}
        (hx : ((ProbOracleComp.runWith P.respond
          (step3 r commitReply (List.ofFn x)) state₁).map Prod.fst) true ≠ 0) :
        ∃ o, verifyTranscript generator s m φ r commitReply (List.ofFn x) o = true := by
      have h := (PMF.mem_support_iff _ _).mpr hx
      supp_cases h [step3, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure]
      exact ⟨_, ‹_›⟩
    exact hnot (mem_ThreeSAT_of_verifyTranscript_ne hbind hne
      (hv (right_ne_zero_of_mul hx₁)).choose_spec (hv (right_ne_zero_of_mul hx₂)).choose_spec)
  have hstep1_le : ∀ r, NaorBinding generator s (BitString.listRow m 0 r) →
      acceptProb (step1 r) P ≤ 1 / 8 := by
    intro r hbind
    rw [acceptProb_eq_acceptProbWith, ProbOracleComp.acceptProbWith_bind]
    calc
      _ ≤ ∑' x, ProbOracleComp.runWith P.respond
            (List.take (K * m) <$> ProbOracleComp.query ((), r)) P.init x * (1 / 8) :=
          tsum_le_tsum fun x => mul_le_mul_right (hstep2_le r x.1 x.2 hbind) _
      _ = 1 / 8 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [gmwVerifier, acceptProb_sample_bind, BitString.eval_sampleList]
  have hterm_le : ∀ r,
      BitString.uniformList m r * acceptProb (step1 r) P ≤
        ({r | ¬ NaorBinding generator s r}.indicator (BitString.uniformList m) r) +
          BitString.uniformList m r * (1 / 8) := by
    intro r
    by_cases hbind : NaorBinding generator s r
    · rw [Set.indicator_of_notMem (by simp [hbind]), zero_add]
      by_cases hr : r ∈ (BitString.uniformList m).support
      · have hr_len : r.length = m := BitString.length_of_mem_support_uniformList hr
        have hrow : BitString.listRow m 0 r = r := by
          simp [BitString.listRow, List.take_left' hr_len]
        exact mul_le_mul_right (hstep1_le r (hrow.symm ▸ hbind)) _
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hr, zero_mul, zero_mul]
    · rw [Set.indicator_of_mem (by simp [hbind])]
      exact le_add_right (mul_le_of_le_one_right' (ProbOracleComp.acceptProbWith_le_one _ _ _))
  calc
    ∑' r, BitString.uniformList m r * acceptProb (step1 r) P
      ≤ ∑' r, (({r | ¬ NaorBinding generator s r}.indicator (BitString.uniformList m) r) +
          BitString.uniformList m r * (1 / 8)) := tsum_le_tsum hterm_le
    _ = (∑' r, {r | ¬ NaorBinding generator s r}.indicator (BitString.uniformList m) r) +
          ∑' r, BitString.uniformList m r * (1 / 8) := tsum_add
    _ = naorBindingProb generator length s + 1 / 8 := by
        rw [← PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        rfl
    _ ≤ (1 / 2 : ℝ≥0∞) ^ (n + 8) + 1 / 8 := by
        gcongr
        exact naorBindingProb_le_of_three_mul_add_one hlen (n + 7) (hstretch (n + 7))
    _ ≤ 1 / 8 + 1 / 8 := by
        gcongr
        rw [one_div, ← ENNReal.inv_pow, one_div]
        exact ENNReal.inv_le_inv.mpr
          ((by norm_num : (8 : ℝ≥0∞) ≤ 2 ^ 3).trans
            (pow_le_pow_right' (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by omega)))
    _ ≤ 1 / 3 := by
        rw [← two_mul,
          ENNReal.le_div_iff_mul_le (Or.inl three_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
          one_div, mul_comm (2 : ℝ≥0∞), mul_assoc]
        calc
          (8 : ℝ≥0∞)⁻¹ * (2 * 3) ≤ (8 : ℝ≥0∞)⁻¹ * 8 := by gcongr; norm_num
          _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

end Cslib.Crypto.GMW
