/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.State
-- `import all` only to read private `bcsChallengesAuxProg` in the round-by-round query-count and
-- support-invariant inductions for `bcsChallengesProg`.
import all CslibFrontier.Crypto.Protocols.BCS.ROM.Protocol
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Verifier query-cost bounds and support invariants for `bcsVerifyROM`

Proves per-channel query-cost bounds (`IsCostBounded`) for `bcsChallengesProg` and `bcsVerifyROM`
together with internal support invariants connecting accepting `bcsVerifyROM` runs under
`bcsMemoize` in a good state to doomed IOP transcripts accepted by `iopVerify`
([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Construction 25.1.1 and Lemma 18.5.7).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsOpeningsMerkleQueries`: total Merkle hash query budget required to
  verify a list of `MerkleOpening`s.

## Main results

* `Cslib.Crypto.Protocols.BCS.isQueryBounded_bcsChallengesProg`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsFSCost_bcsVerifyROM`: Fiat–Shamir query-count bounds
  for `bcsChallengesProg` and `bcsVerifyROM`.
* `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le`: Merkle hash
  query-count bounds for `bcsVerifyROM` in terms of `bcsOpeningsMerkleQueries` or uniform query and
  opening-path bounds.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 18 (Lemma 18.5.7) and Chapter 25 (Construction 25.1.1).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM Cslib.Probability Cslib.OracleComp

section CostBounds

variable {r d : ℕ} {Stmt Wit Sym Chal β : Type}

private theorem isQueryBounded_bcsChallengesAuxProg (x : Stmt) (roots : Fin r → List Bool) :
    ∀ (m : ℕ) (hm : m ≤ r), IsQueryBounded (bcsChallengesAuxProg (Chal := Chal) x roots m hm) m
  | 0, _ => .pure Fin.elim0 0
  | m + 1, hm => by
    unfold bcsChallengesAuxProg
    simpa only [Nat.add_zero, bind_assoc] using
      (isQueryBounded_bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)).bind fun prev =>
        (IsCostBounded.query (cost := fun _ => 1)
          (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev)).bind fun c =>
            IsCostBounded.pure (Fin.snoc prev c : Fin (m + 1) → Chal) 0

/-- `bcsChallengesProg x roots` makes at most `r` Fiat–Shamir queries. -/
theorem isQueryBounded_bcsChallengesProg (x : Stmt) (roots : Fin r → List Bool) :
    IsQueryBounded (bcsChallengesProg (Chal := Chal) x roots) r :=
  isQueryBounded_bcsChallengesAuxProg x roots r le_rfl

/-- `bcsVerifyROM iop encSym x prf` makes at most `r` Fiat–Shamir queries for every statement `x`
and proof `prf`. -/
theorem isCostBounded_bcsFSCost_bcsVerifyROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    IsCostBounded bcsFSCost (bcsVerifyROM iop encSym x prf) r := by
  unfold bcsVerifyROM
  simpa only [Nat.add_zero] using
    ((isQueryBounded_bcsChallengesProg x prf.roots).liftRight fun _ => le_rfl).bind fun chals =>
      IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl)
        (bcsVerifyOpeningsProg iop encSym x prf chals)

/-- Total number of Merkle hash queries needed to verify every opening in `openings` (one leaf hash
plus `path.length` internal-node hashes per opening). -/
@[expose] def bcsOpeningsMerkleQueries {Sym : Type} (openings : List (MerkleOpening Sym)) : ℕ :=
  (openings.map fun o => o.path.length + 1).sum

private theorem isQueryBounded_zip_mapM_merkleVerifyProg (encSym : Sym → List Bool)
    (roots : Fin r → List Bool) (qs : List (Fin r × Fin (2 ^ d)))
    (ops : List (MerkleOpening Sym)) :
    IsQueryBounded
      ((qs.zip ops).mapM fun ((j, idx), ⟨val, path⟩) =>
        merkleVerifyProg d (roots j) idx.val (encSym val) path)
      (((qs.zip ops).map fun (_, o) => o.path.length + 1).sum) := by
  induction qs generalizing ops with
  | nil => exact .pure [] 0
  | cons q qs' ih =>
    cases ops with
    | nil => exact .pure [] 0
    | cons op ops' =>
      simpa only [List.zip_cons_cons, List.mapM_cons, List.map_cons, List.sum_cons,
        Nat.add_zero] using
        (isQueryBounded_merkleVerifyProg d (roots q.1) q.2.val (encSym op.leaf) op.path).bind
          fun c => (ih ops').bind fun cs => IsCostBounded.pure (c :: cs) 0

private theorem isCostBounded_bcsMTCost_bcsVerifyROM_of_le
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) {B : ℕ}
    (hB : ∀ chals,
      (((iop.queries x chals).zip prf.openings).map fun (_, o) => o.path.length + 1).sum ≤ B) :
    IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) B := by
  unfold bcsVerifyROM
  simpa only [Nat.zero_add] using
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl)
      (bcsChallengesProg x prf.roots)).bind fun chals =>
      IsCostBounded.liftLeft (cost₁ := fun _ => 1)
        (program := bcsVerifyOpeningsProg iop encSym x prf chals) (by
          unfold bcsVerifyOpeningsProg
          simpa only [Nat.add_zero] using
            ((isQueryBounded_zip_mapM_merkleVerifyProg encSym prf.roots (iop.queries x chals)
              prf.openings).mono (hB chals)).bind fun _ => IsCostBounded.pure _ 0)
        fun _ => le_rfl

/-- `bcsVerifyROM iop encSym x prf` makes at most `bcsOpeningsMerkleQueries prf.openings` Merkle
hash queries, independently of the random Fiat–Shamir challenges. -/
theorem isCostBounded_bcsMTCost_bcsVerifyROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf)
      (bcsOpeningsMerkleQueries prf.openings) := by
  refine isCostBounded_bcsMTCost_bcsVerifyROM_of_le iop encSym x prf fun chals => ?_
  suffices ∀ (qs : List (Fin r × Fin (2 ^ d))) (ops : List (MerkleOpening Sym)),
      ((qs.zip ops).map fun (_, o) => o.path.length + 1).sum ≤ bcsOpeningsMerkleQueries ops from
    this _ _
  intro qs
  induction qs with
  | nil => exact fun _ => Nat.zero_le _
  | cons _ _ ih => exact fun | [] => le_rfl | _ :: _ => Nat.add_le_add_left (ih _) _

/-- If `iop.queries x chals` makes at most `q_iop` oracle queries for every `chals` and every
authentication path in `prf.openings` has length at most `L_path`, then
`bcsVerifyROM iop encSym x prf` makes at most `q_iop * (L_path + 1)` Merkle hash queries. -/
theorem isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (x : Stmt) (prf : BCSProof r Sym) {q_iop L_path : ℕ}
    (hqs : ∀ chals, (iop.queries x chals).length ≤ q_iop)
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) (q_iop * (L_path + 1)) := by
  refine isCostBounded_bcsMTCost_bcsVerifyROM_of_le iop encSym x prf fun chals => ?_
  calc (((iop.queries x chals).zip prf.openings).map fun (_, o) => o.path.length + 1).sum
      ≤ ((iop.queries x chals).zip prf.openings).length * (L_path + 1) := by
        simpa [List.length_map] using List.sum_le_length_nsmul
          (((iop.queries x chals).zip prf.openings).map fun (_, o) => o.path.length + 1)
          (L_path + 1) fun _ hx => by
            rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
            exact Nat.add_le_add_right (hops p.2 (List.of_mem_zip hp).2) 1
    _ ≤ q_iop * (L_path + 1) := by
        rw [List.length_zip]
        exact Nat.mul_le_mul_right _ ((Nat.min_le_left _ _).trans (hqs _))

end CostBounds

/-! #### Support invariants of `bcsMemoize`, `bcsChallengesProg`, and `bcsVerifyROM` -/

section SupportInvariants

variable {r d : ℕ} {Stmt Wit Sym Chal β : Type}

private theorem validFSChain_of_mem_support_bcsChallengesAuxProg
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (x : Stmt) (roots : Fin r → List Bool) :
    ∀ (m : ℕ) (hm : m ≤ r) {tr_FS tr_FS' : List (BCSFSQuery Stmt Chal × Chal)}
      {chals : Fin m → Chal},
      (tr_FS.map Prod.fst).Nodup →
      (∀ e ∈ tr_FS, e.2 ∈ (PMF.uniformOfFintype Chal).support) →
      (chals, tr_FS') ∈
        ((OracleComp.interpret (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal))
          (bcsChallengesAuxProg x roots m hm)).run tr_FS).support →
      ValidFSChain tr_FS' x ((List.ofFn roots).take m) (List.ofFn chals)
  | 0, _, tr_FS, tr_FS', chals, _, _, hmem => by
    supp_cases hmem [bcsChallengesAuxProg, run_interpret_pure]
    exact ⟨by simp, fun _ hi => by simp at hi⟩
  | m + 1, hm, tr_FS, tr_FS', chals, hnodup, hsupp, hmem => by
    supp_cases hmem [bcsChallengesAuxProg, run_interpret_bind, run_interpret_query,
      run_interpret_pure] with ⟨⟨prev, tr_FS₁⟩, hprev, ⟨c, tr_FS₂⟩, hc, rfl, rfl⟩
    obtain ⟨-, hnodup₁, hsupp₁, -⟩ := mem_support_run_memoize_invariant _
      (bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)) hnodup hsupp hprev
    obtain ⟨_, hsteps_prev⟩ := validFSChain_of_mem_support_bcsChallengesAuxProg x roots m
      (Nat.le_of_succ_le hm) hnodup hsupp hprev
    obtain ⟨hc_mem, hsub₂, -, -⟩ := mem_support_memoize_nodup _
      (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev) hnodup₁ hsupp₁ hc
    refine ⟨by simp [hm], fun i hi => ?_⟩
    rw [List.length_take_of_le (by simpa using hm)] at hi
    by_cases him : i < m
    · simpa only [List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ m + 1),
        Nat.min_eq_left (Nat.succ_le_of_lt him), List.ofFn_succ_last, Fin.snoc_castSucc,
        Fin.snoc_last,
        List.take_append_of_le_length (by simp [him.le] : i ≤ (List.ofFn prev).length),
        List.getElem_append_left (by simpa using him : i < (List.ofFn prev).length)] using
          hsub₂ _ (hsteps_prev i (by simpa [Nat.le_of_succ_le hm] using him))
    · obtain rfl : i = m := by omega
      simpa only [List.take_take, Nat.min_self, rootPrefix_eq_take_ofFn,
        List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last,
        List.take_left' (by simp : (List.ofFn prev).length = i),
        List.getElem_append_right (by simp : (List.ofFn prev).length ≤ i),
        List.length_ofFn, Nat.sub_self, List.getElem_singleton] using hc_mem

private theorem validFSChain_of_mem_support_bcsChallengesProg
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (x : Stmt) (roots : Fin r → List Bool)
    {tr_FS tr_FS' : List (BCSFSQuery Stmt Chal × Chal)} {chals : Fin r → Chal}
    (hnodup : (tr_FS.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr_FS, e.2 ∈ (PMF.uniformOfFintype Chal).support)
    (hmem : (chals, tr_FS') ∈
      ((OracleComp.interpret (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal))
        (bcsChallengesProg x roots)).run tr_FS).support) :
    ValidFSChain tr_FS' x (List.ofFn roots) (List.ofFn chals) := by
  simpa only [List.take_of_length_le (by simp : (List.ofFn roots).length ≤ r)] using
    validFSChain_of_mem_support_bcsChallengesAuxProg x roots r le_rfl hnodup hsupp hmem

/-- Core trace soundness/consistency lemma for `bcsVerifyROM`: when `bcsVerifyROM iop encSym x prf`
runs from a valid trace state `(tr_MT₁, tr_FS₁)` and returns `(true, (tr_MT₃, tr_FS₂))`, if
`TraceCollisionFree tr_MT₃` holds, then there exists a challenge vector `chals : Fin r → Chal` such
that `ValidFSChain tr_FS₂ x (List.ofFn prf.roots) (List.ofFn chals)` holds and `iopVerify` accepts
`bcsExtractOracles decSym defaultSym tr_MT₃ d prf.roots` at `chals`. -/
private theorem exists_validFSChain_and_iopVerify_of_mem_support_bcsVerifyROM
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    (x : Stmt) (prf : BCSProof r Sym)
    {tr_MT₁ tr_MT₃ : List (List Bool × List Bool)}
    {tr_FS₁ tr_FS₂ : List (BCSFSQuery Stmt Chal × Chal)}
    (hnodup_MT₁ : (tr_MT₁.map Prod.fst).Nodup)
    (hsupp_MT₁ : ∀ e ∈ tr_MT₁, e.2 ∈ (BitString.uniformList σ).support)
    (hnodup_FS₁ : (tr_FS₁.map Prod.fst).Nodup)
    (hsupp_FS₁ : ∀ e ∈ tr_FS₁, e.2 ∈ (PMF.uniformOfFintype Chal).support)
    (hmem : (true, (tr_MT₃, tr_FS₂)) ∈
      ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run
        (tr_MT₁, tr_FS₁)).support)
    (hfree : TraceCollisionFree tr_MT₃) :
    ∃ chals : Fin r → Chal,
      ValidFSChain tr_FS₂ x (List.ofFn prf.roots) (List.ofFn chals) ∧
      iopVerify iop x chals (bcsExtractOracles decSym defaultSym tr_MT₃ d prf.roots) = true := by
  supp_cases hmem [bcsVerifyROM, run_interpret_bind,
    RandomOracle.run_interpret_memoizeSum_liftRight] with
    ⟨_, ⟨⟨chals', tr_FS₂'⟩, hch_mem, rfl⟩, hMT_call⟩
  supp_cases hMT_call [RandomOracle.run_interpret_memoizeSum_liftLeft] with
    ⟨⟨_, tr_MT₃'⟩, hmt_mem, rfl, rfl, rfl⟩
  obtain ⟨-, hnodup_FS₂, -, heval_FS⟩ := mem_support_run_memoize_invariant _
    (bcsChallengesProg x prf.roots) hnodup_FS₁ hsupp_FS₁ hch_mem
  obtain ⟨-, hnodup_MT₃, -, heval_MT⟩ := mem_support_run_memoize_invariant _
    (bcsVerifyOpeningsProg iop encSym x prf chals') hnodup_MT₁ hsupp_MT₁ hmt_mem
  have hcons_MT := traceConsistentWith_lookup_of_nodup tr_MT₃' [] hnodup_MT₃
  let dChal : Chal := Classical.choice ‹Nonempty Chal›
  have hchals_eq : chals' =
      bcsChallenge (chainedFS fun q => (tr_FS₂'.lookup q).getD dChal) x prf.roots := by
    simpa only [evalPure_bcsChallengesProg] using
      heval_FS _ (traceConsistentWith_lookup_of_nodup tr_FS₂' dChal hnodup_FS₂)
  refine ⟨chals',
    validFSChain_of_mem_support_bcsChallengesProg x prf.roots hnodup_FS₁ hsupp_FS₁ hch_mem, ?_⟩
  supp_cases hmt_mem [bcsVerifyOpeningsProg, run_interpret_bind, run_interpret_pure] with
    ⟨⟨_, _⟩, hchecks, -, rfl⟩
  rw [hchals_eq]
  refine iopVerify_bcsExtractOracles_of_bcsVerify hdec defaultSym hfree (fun j idx val path hq =>
    pathQueriedInTrace_of_mem_support_mapM_merkleVerifyProg hnodup_MT₁ hsupp_MT₁ hchecks d
      (fun ((j, _), _) => prf.roots j) (fun ((_, idx), _) => idx.val)
      (fun (_, o) => encSym o.leaf) (fun (_, o) => o.path) (fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)
      hcons_MT _ (hchals_eq ▸ hq)) ?_
  simpa only [bcsVerify, evalPure_bcsVerifyOpeningsProg, hchals_eq] using
    (heval_MT _ hcons_MT).symm

/-- An accepting verification that ends in a good state yields a doomed accepted IOP transcript:
if a prover run from `([], [])` reaches `st₁`, `bcsVerifyROM iop encSym x prf` accepts from `st₁`
and ends in `st₃`, `BCSGoodState` on `S` holds at `st₃` and `x ∈ S`, then for some challenges the
transcript extracted from `st₃` is a valid Fiat–Shamir chain, is doomed, and is accepted by
`iopVerify`. -/
private theorem exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {P : OracleComp (BCSROMSpec Stmt Chal) β} {res : β} {x : Stmt} {prf : BCSProof r Sym}
    {st₁ st₃ : BCSTraceState Stmt Chal}
    (hP : (res, st₁) ∈ ((OracleComp.interpret (bcsMemoize σ) P).run ([], [])).support)
    (hV : (true, st₃) ∈
      ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run st₁).support)
    (hgood : BCSGoodState r d S doomed decSym defaultSym st₃) (hx : x ∈ S) :
    ∃ chals : Fin r → Chal,
      ValidFSChain st₃.2 x (List.ofFn prf.roots) (List.ofFn chals) ∧
      doomed x (List.ofFn fun j : Fin r =>
        (bcsExtractOracles decSym defaultSym st₃.1 d prf.roots j, chals j)) ∧
      iopVerify iop x chals (bcsExtractOracles decSym defaultSym st₃.1 d prf.roots) = true := by
  obtain ⟨⟨hnodup_MT, hsupp_MT⟩, hnodup_FS, hsupp_FS⟩ :=
    RandomOracle.mem_support_run_interpret_memoizeSum _ _
      (fun tr => (tr.map Prod.fst).Nodup ∧ ∀ e ∈ tr, e.2 ∈ (BitString.uniformList σ).support)
      (fun tr => (tr.map Prod.fst).Nodup ∧ ∀ e ∈ tr, e.2 ∈ (PMF.uniformOfFintype Chal).support)
      (fun q _ _ _ h hmem => (mem_support_memoize_nodup _ q h.1 h.2 hmem).2.2)
      (fun q _ _ _ h hmem => (mem_support_memoize_nodup _ q h.1 h.2 hmem).2.2) P
      (st := ([], [])) (by simp) hP
  obtain ⟨chals, hchain, hacc⟩ :=
    exists_validFSChain_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ x prf
      hnodup_MT hsupp_MT hnodup_FS hsupp_FS hV hgood.1
  exact ⟨chals, hchain, bcsExtractTranscript_ofFn .. ▸
    hgood.2 x hx _ _ (by simp) hchain, hacc⟩

end SupportInvariants

end Cslib.Crypto.Protocols.BCS
