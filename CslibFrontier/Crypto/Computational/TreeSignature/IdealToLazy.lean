/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TreeSignature.Reduction
import CslibFrontier.Crypto.Computational.TreeSignature.Handlers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Languages.Probabilistic.Iteration.Chain
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.GetD

/-!
# Ideal-to-lazy coin hybrid for stateless tree signatures

Proves the first post-PRF game hop toward [BonehShoup2023], Section 14.6.3, Theorem 14.6, p. 600
(binary case `q = 2`): replacing the uniform random function supplying coins in `treeIdealGame`
with lazy node keys and edge signatures plus leaf-collision aborts (`lazyTreeGame`) loses at most
`(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)` across any `Q`-query adversary, whenever the coin-request
width `N n` covers all padded tree requests (`2 * depth n + 4 ≤ N n`) and seeded key/signature
coin budgets.

## Main results

* `Cslib.Crypto.TreeSignature.succProbability_treeIdealGame_le_lazy`: leaf-collision birthday
  bound between `treeIdealGame` and `lazyTreeGame`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.3, Theorem 14.6, p. 600.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace TreeSignature

private def treeBad {σ : Type} (s : TreeState σ) : Prop := s.2.bad = true

private noncomputable def unguardedTreeHandler {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) (req : Unit × List Bool) : StateT (TreeState σ) PMF (List Bool) :=
  fun (inner, ⟨queried, seenLeaves, bad⟩) =>
    if req.2.length = n then
      (BitString.uniformList (depth n)).bind fun leaf =>
        let bad' := bad || seenLeaves.contains leaf
        let seen' := if bad' then seenLeaves else leaf :: seenLeaves
        (body leaf req.2 inner).map fun (sig, inner') =>
          (sig, (inner', ⟨req.2 :: queried, seen', bad'⟩))
    else PMF.pure ([], (inner, ⟨req.2 :: queried, seenLeaves, bad⟩))

private theorem identicalUntilBad_treeHandler {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) :
    ProbOracleComp.IdenticalUntilBad
      (unguardedTreeHandler depth n body) (guardedTreeHandler depth n body) treeBad := by
  refine OracleComp.IdenticalUntilBad.probOracleComp ⟨?_, ?_, ?_⟩
  · rintro req ⟨inner, ⟨queried, seen, bad⟩⟩ hs a ⟨inner', ⟨queried', seen', bad'⟩⟩ hs'
    obtain rfl : bad = false := Bool.eq_false_iff.mpr hs
    obtain rfl : bad' = false := Bool.eq_false_iff.mpr hs'
    simp only [unguardedTreeHandler, guardedTreeHandler, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte]
    split_ifs with hmsg
    · simp only [PMF.bind_apply]
      refine tsum_congr fun leaf => ?_
      cases hcl : seen.contains leaf
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        congr 1
        exact ((PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm).trans
          ((PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm).symm
    · rfl
  · rintro req ⟨inner, ⟨queried, seen, bad⟩⟩ hbad x hx
    obtain rfl : bad = true := hbad
    simp only [unguardedTreeHandler, Bool.true_or, ↓reduceIte] at hx
    split_ifs at hx <;> (supp_cases hx; rfl)
  · rintro req ⟨inner, ⟨queried, seen, bad⟩⟩ hbad x hx
    obtain rfl : bad = true := hbad
    simp only [guardedTreeHandler, ↓reduceIte] at hx
    split_ifs at hx <;> (supp_cases hx; rfl)

private theorem toOuterMeasure_bad_guardedTreeHandler_le {α σ : Type} (depth : ℕ → ℕ) (n Q : ℕ)
    (body : TreeBody σ) {prog : WordOracleComp Unit α} (hq : prog.IsQueryBounded Q) (inner : σ)
    (queried : List (List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (guardedTreeHandler depth n body)) prog).run (inner, ⟨queried, [], false⟩)).toOuterMeasure
        {x | treeBad x.2} ≤
      (((Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) : ℝ≥0) : ℝ≥0∞) := by
  have hstep : ∀ req (s : TreeState σ), ¬treeBad s →
      (guardedTreeHandler depth n body req s).toOuterMeasure {x | treeBad x.2} ≤
        (s.2.seenLeaves.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ depth n) := by
    rintro req ⟨inner₀, ⟨q₀, seen, bad⟩⟩ hs
    obtain rfl : bad = false := Bool.eq_false_iff.mpr hs
    simp only [guardedTreeHandler, Bool.false_eq_true, ↓reduceIte]
    split_ifs with hmsg
    · classical
      refine (Probability.PMF.toOuterMeasure_bind_le_add (BitString.uniformList (depth n)) _
        (seen.toFinset : Set (List Bool)) {x : List Bool × TreeState σ | treeBad x.2} 0
        fun leaf _ hnot => ?_).trans ?_
      · have hmem : seen.contains leaf = false := Bool.eq_false_iff.mpr fun hc =>
          hnot (Finset.mem_coe.mpr (List.mem_toFinset.mpr (List.contains_iff_mem.mp hc)))
        simp only [hmem, Bool.false_eq_true, ↓reduceIte, le_zero_iff,
          PMF.toOuterMeasure_apply_eq_zero_iff]
        exact Set.disjoint_left.mpr fun x hx hbad => by supp_cases hx; cases hbad
      · rw [add_zero]
        exact (BitString.toOuterMeasure_uniformList_finset_le (depth n) seen.toFinset).trans
          (by gcongr; exact_mod_cast List.toFinset_card_le seen)
    · simp [PMF.toOuterMeasure_pure_apply, treeBad]
  have hgrow : ∀ req (s : TreeState σ), ¬treeBad s → ∀ x ∈
      (guardedTreeHandler depth n body req s).support, ¬treeBad x.2 →
      x.2.2.seenLeaves.length ≤ s.2.seenLeaves.length + 1 := by
    rintro req ⟨inner₀, ⟨q₀, seen, bad⟩⟩ hs x hx hxbad
    obtain rfl : bad = false := Bool.eq_false_iff.mpr hs
    simp only [guardedTreeHandler, Bool.false_eq_true, ↓reduceIte] at hx
    split_ifs at hx
    · obtain ⟨leaf, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      split_ifs at hx <;> (supp_cases hx; first | exact absurd rfl hxbad | exact le_rfl)
    · supp_cases hx; exact Nat.le_succ _
  have hbad := ProbOracleComp.toOuterMeasure_bad_choose_two_le
    (handler := guardedTreeHandler depth n body) (bad := treeBad)
    (fun s => s.2.seenLeaves.length) ((1 : ℝ≥0∞) / 2 ^ depth n) hstep hgrow hq
    (s := (inner, ⟨queried, [], false⟩)) Bool.false_ne_true
  rw [ProbOracleComp.runWith_eq_run_interpret] at hbad
  have htwo : (1 : ℝ≥0∞) / 2 ^ depth n = 2 * ((1 : ℝ≥0∞) / 2 ^ (depth n + 1)) := by
    simp only [one_div, pow_succ']
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hchoose : 2 * Q.choose 2 ≤ Q ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    exact (Nat.mul_div_le _ 2).trans (Nat.mul_le_mul_left Q (Nat.sub_le Q 1))
  refine hbad.trans ?_
  have herr : ((((Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) : ℝ≥0)) : ℝ≥0∞) =
      ((Q ^ 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ (depth n + 1)) := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), div_eq_mul_inv, one_div]; push_cast; ring
  simp only [List.length_nil, mul_zero, zero_add, htwo, ← mul_assoc]
  rw [herr, mul_comm (Q.choose 2 : ℝ≥0∞) 2, ← Nat.cast_ofNat, ← Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hchoose) zero_le

private abbrev CoinCache := List (List Bool × List Bool)

private noncomputable def lazyCoinRequest (M : ℕ) (x : List Bool) (L : ℕ) :
    StateT CoinCache PMF (List Bool) := fun cc =>
  (memoize (fun _ => BitString.uniformList M) (padRequest M x) cc).map
    fun out => (out.1.take L, out.2)

private noncomputable def lazyCoinHandler (M : ℕ) (r : Unit × List Bool) :
    StateT CoinCache PMF (List Bool) :=
  let req := coinRequestDecoder.decode r.2
  lazyCoinRequest M req.1 req.2

private theorem run_interpret_coinRequest (M : ℕ) (x : List Bool) (L : ℕ) (cc : CoinCache) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (coinRequest x L)).run cc = lazyCoinRequest M x L cc := by
  simp only [coinRequest, OracleComp.interpret_map, ProbOracleComp.interpret_query,
    StateT.run_map, PMF.monad_map_eq_map]
  change (lazyCoinHandler M ((), encPair encBits encUnary (x, L)) cc).map
    (fun (v, s) => (v.take L, s)) = _
  simp only [lazyCoinHandler, coinRequestDecoder.decode_enc, lazyCoinRequest, PMF.map_comp,
    Function.comp_def, List.take_take, Nat.min_self]

private theorem eval_treeIdealGame_eq_lazyCoin (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (treeIdealGame S T depth N adversary n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler (N n)))
        (simulateTreeGame S T depth adversary n)).run []).map Prod.fst := by
  set M := N n
  set prog := simulateTreeGame S T depth adversary n
  have hideal : ProbComp.eval (treeIdealGame S T depth N adversary n) =
      (PMF.uniformOfFintype (BitString M → BitString M)).bind fun table =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (fun r : Unit × List Bool => PMF.pure (randomCoinOracle M table r.2)))
          prog := by
    simp only [treeIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
    have hc : ∀ x L, (randomCoinOracle M table (encPair encBits encUnary (x, L))).length ≤ L := by
      simp only [randomCoinOracle, coinRequestDecoder.decode_enc, List.length_take_le, implies_true]
    have hcoins : coinsOf (randomCoinOracle M table) = tableCoins M table := by
      funext _ x L; simp only [coinsOf, randomCoinOracle, coinRequestDecoder.decode_enc, tableCoins]
    rw [← hcoins, ← evalDet_simulateTreeGame hc adversary n [], ← eval_interpret_eq_evalDet,
      ProbOracleComp.eval_interpret]
    simp only [ProbComp.eval_pure]; rfl
  let adapt (r : Unit × List Bool) :
      ProbOracleComp (fun _ : BitString M => List Bool) (List Bool) :=
    let req := coinRequestDecoder.decode r.2
    List.take req.2 <$> ProbOracleComp.query (BitString.ofList M (padRequest M req.1))
  let adapted := OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) adapt) prog
  have hmem := RandomOracle.interpret_prob_eq_memoize_map (encBitString M) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString M)) (fun _ => BitString.uniformList M)
    (fun _ => rfl) adapted
  rw [PMF.pi_uniformOfFintype, Probability.PMF.monad_bind_eq_bind] at hmem
  simp only [encBitString_apply] at hmem
  rw [hideal]
  refine (Eq.symm (PMF.bind_congr_on_support _ _ _ fun table _ => ?_)).trans
    (hmem.trans (congrArg (PMF.map Prod.fst) ?_))
  · simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
    congr 1; funext q; cases q with
    | inl _ => rfl
    | inr r =>
      simp only [adapt, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        pmf_norm, randomCoinOracle, randomFunctionOracle, length_padRequest, ↓reduceIte]
  · simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
    refine congrArg (fun h => (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h) prog).run [])
      (funext fun r => funext fun cc => ?_)
    simp only [adapt, interp_norm, pmf_norm,
      BitString.ofFn_ofList (length_padRequest M _), lazyCoinHandler, lazyCoinRequest]
    rfl

private noncomputable def coinSignBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) : TreeBody CoinCache :=
  fun leaf msg cc =>
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (do
        let (node, (_, sk), certs) ← certifyO S T depth n leaf
        let σ ← signAtO S T node sk (leaf.getLastD false).toNat msg
        return encodeSignature leaf certs σ)).run cc

private abbrev JointInner := CoinCache × (NodeKeyCache × EdgeSigCache)

private noncomputable def jointNodeKey (S : IndexedSignatureScheme) (T : S.Seeded) (M n : ℕ)
    (path : List Bool) (st : CoinCache × NodeKeyCache) :
    PMF ((List Bool × List Bool) × (CoinCache × NodeKeyCache)) :=
  (lazyCoinRequest M (keyInput path) (T.keyGenBudget n) st.1).map fun out =>
    let key := T.keyGenWith n out.1
    let nodes' := match st.2.lookup path with | some _ => st.2 | none => (path, key) :: st.2
    (key, (out.2, nodes'))

private noncomputable def jointSignAt (S : IndexedSignatureScheme) (T : S.Seeded) (M : ℕ)
    (path sk : List Bool) (u : ℕ) (msg : List Bool) (st : CoinCache × EdgeSigCache) :
    PMF (List Bool × (CoinCache × EdgeSigCache)) :=
  (lazyCoinRequest M (signInput path u) (T.signBudget sk u msg) st.1).map fun out =>
    let σ := T.signWith sk u msg out.1
    let edges' := match st.2.lookup (path, u) with
      | some _ => st.2 | none => ((path, u), σ) :: st.2
    (σ, (out.2, edges'))

private noncomputable def jointCertifyStep (S : IndexedSignatureScheme) (T : S.Seeded) (M n : ℕ)
    (leaf : List Bool) (st : CoinCache × LazyCertState) : PMF (CoinCache × LazyCertState) := do
  let (cc, ((node, (_, sk), certs), (nodes, edges))) := st
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (child, (cc', nodes')) ← jointNodeKey S T M n childPath (cc, nodes)
  (jointSignAt S T M node sk bit.toNat child.1 (cc', edges)).map fun (σ, (cc'', edges')) =>
    (cc'', ((childPath, child, certs ++ [(child.1, σ)]), (nodes', edges')))

private noncomputable def jointCertify (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf : List Bool) (st : JointInner) :
    PMF (CoinCache × LazyCertState) := do
  let (root, (cc₀, nodes₀)) ← jointNodeKey S T M n [] (st.1, st.2.1)
  Nat.iterate (fun m => m.bind (jointCertifyStep S T M n leaf)) (depth n - 1)
    (PMF.pure (cc₀, (([], root, []), (nodes₀, st.2.2))))

private noncomputable def jointCoinBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) : TreeBody JointInner :=
  fun leaf msg st =>
    (jointCertify S T depth M n leaf st).bind fun
      (cc', ((node, (_, sk), certs), (nodes', edges'))) =>
        (jointSignAt S T M node sk (leaf.getLastD false).toNat msg (cc', edges')).map
          fun (σ, (cc'', edges'')) => (encodeSignature leaf certs σ, (cc'', (nodes', edges'')))

private theorem map_dropCaches_jointNodeKey (S : IndexedSignatureScheme) (T : S.Seeded)
    (M n : ℕ) (path : List Bool) (cc : CoinCache) (ns : NodeKeyCache) :
    (jointNodeKey S T M n path (cc, ns)).map (fun out => (out.1, out.2.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (nodeKeyO S T n path)).run cc := by
  simp only [jointNodeKey, nodeKeyO, OracleComp.interpret_map, StateT.run_map,
    run_interpret_coinRequest, pmf_norm]

private theorem map_dropCaches_jointSignAt (S : IndexedSignatureScheme) (T : S.Seeded)
    (M : ℕ) (path sk : List Bool) (u : ℕ) (msg : List Bool) (cc : CoinCache)
    (es : EdgeSigCache) :
    (jointSignAt S T M path sk u msg (cc, es)).map (fun out => (out.1, out.2.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (signAtO S T path sk u msg)).run cc := by
  simp only [jointSignAt, signAtO, OracleComp.interpret_map, StateT.run_map,
    run_interpret_coinRequest, pmf_norm]

private theorem map_dropCaches_jointCertify (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf : List Bool) (st : JointInner) :
    (jointCertify S T depth M n leaf st).map (fun out => (out.2.1, out.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (certifyO S T depth n leaf)).run st.1 := by
  apply PMF.RepInv.map_eq (inv := fun _ => True)
  dsimp only [jointCertify, certifyO]
  simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_iterate_pmf, pmf_norm]
  refine (PMF.RepInv.of_eq (map_dropCaches_jointNodeKey S T M n [] st.1 st.2.1)).bind
    fun ⟨root, cc₀, nodes₀⟩ _ _ =>
      PMF.RepInv.iterate (fun _ _ => True) rfl trivial
        fun _ _ ⟨c, ⟨node, ⟨_, sk⟩, certs⟩, ns, es⟩ _ => ?_
  dsimp only [jointCertifyStep, certifyStepO]
  simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_pure, pmf_norm]
  exact (PMF.RepInv.of_eq (map_dropCaches_jointNodeKey S T M n _ c ns)).bind
    fun ⟨child, c', _⟩ _ _ =>
      (PMF.RepInv.of_eq (map_dropCaches_jointSignAt S T M node sk _ child.1 c' es)).map
        fun _ _ _ => ⟨rfl, trivial⟩

private theorem map_dropCaches_jointCoinBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf msg : List Bool) (st : JointInner) :
    (jointCoinBody S T depth M n leaf msg st).map (fun (sig, st') => (sig, st'.1)) =
      coinSignBody S T depth M n leaf msg st.1 := by
  apply PMF.RepInv.map_eq (inv := fun _ => True)
  dsimp only [jointCoinBody, coinSignBody]
  simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_pure, pmf_norm]
  exact (PMF.RepInv.of_eq (map_dropCaches_jointCertify S T depth M n leaf st)).bind
    fun ⟨cc', ⟨node, ⟨_, sk⟩, certs⟩, _, es'⟩ _ _ =>
      (PMF.RepInv.of_eq (map_dropCaches_jointSignAt S T M node sk _ msg cc' es')).map
        fun _ _ _ => ⟨rfl, trivial⟩

private theorem take_sub_one_append_getLastD {l : List Bool} {d : ℕ} (hd : 1 ≤ d)
    (hl : l.length = d) : l.take (d - 1) ++ [l.getLastD false] = l := by
  have hlt : d - 1 < l.length := by omega
  have hlast : l.getLastD false = l[d - 1] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp only [hl, Option.getD_eq_iff, List.getElem?_eq_getElem hlt, true_or]
  rw [hlast, ← List.take_succ_eq_append_getElem hlt, show d - 1 + 1 = l.length by omega,
    List.take_length]

/-- Coupling invariant linking the lazy random-function coin table `cc` to the lazy node-key and
edge-signature caches `(nodes, edges)` for depth-`d` binary tree signing. -/
private structure JointLazyInv (S : IndexedSignatureScheme) (T : S.Seeded) (M d n : ℕ)
    (root : List Bool × List Bool) (s : TreeState JointInner) : Prop where
  root_lookup : s.1.2.1.lookup [] = some root
  nodes_mem : ∀ p k, (p, k) ∈ s.1.2.1 → p.length < d ∧ k ∈ (ProbComp.eval (S.keyGen n)).support
  nodes_eq_coin : ∀ p, p.length < d →
    s.1.2.1.lookup p =
      (s.1.1.lookup (padRequest M (keyInput p))).map
        (fun w => T.keyGenWith n (w.take (T.keyGenBudget n)))
  edges_mem : ∀ q v σ, ((q, v), σ) ∈ s.1.2.2 →
    q.length < d ∧ v ≤ 1 ∧
      (q.length = d - 1 → ∃ l ∈ s.2.seenLeaves, l.length = d ∧ q = l.take (d - 1) ∧
        v = (l.getLastD false).toNat)
  edges_none_coin_none : ∀ p u, p.length < d → u ≤ 1 → s.1.2.2.lookup (p, u) = none →
    s.1.1.lookup (padRequest M (signInput p u)) = none
  edges_some_internal : ∀ p (b : Bool) σ, p.length + 1 < d →
    s.1.2.2.lookup (p, b.toNat) = some σ →
    ∃ kp kc w, s.1.2.1.lookup p = some kp ∧ s.1.2.1.lookup (p ++ [b]) = some kc ∧
      s.1.1.lookup (padRequest M (signInput p b.toNat)) = some w ∧
      σ = T.signWith kp.2 b.toNat kc.1 (w.take (T.signBudget kp.2 b.toNat kc.1))

private theorem jointLazyInv_insert_sign (S : IndexedSignatureScheme) (T : S.Seeded)
    {M d n : ℕ} (hwidth : 2 * d + 4 ≤ M) {root : List Bool × List Bool}
    {cc : CoinCache} {ns : NodeKeyCache} {es : EdgeSigCache}
    {q₀ q₁ sl₀ sl₁ : List (List Bool)} {b₀ b₁ : Bool}
    (hinv : JointLazyInv S T M d n root ((cc, ns, es), ⟨q₀, sl₀, b₀⟩))
    (hsub : ∀ l ∈ sl₀, l ∈ sl₁) {node : List Bool} {u : ℕ} (hnode_lt : node.length < d)
    (hu : u ≤ 1) (w σ : List Bool)
    (hleaf : node.length = d - 1 →
      ∃ l ∈ sl₁, l.length = d ∧ node = l.take (d - 1) ∧ u = (l.getLastD false).toNat)
    (hinternal : ∀ b : Bool, b.toNat = u → node.length + 1 < d →
      ∃ kp kc, ns.lookup node = some kp ∧ ns.lookup (node ++ [b]) = some kc ∧
        σ = T.signWith kp.2 b.toNat kc.1 (w.take (T.signBudget kp.2 b.toNat kc.1))) :
    JointLazyInv S T M d n root
      (((padRequest M (signInput node u), w) :: cc, ns, ((node, u), σ) :: es),
        ⟨q₁, sl₁, b₁⟩) := by
  refine ⟨hinv.root_lookup, hinv.nodes_mem, fun p hp => ?_, fun q v σ' hmem => ?_,
    fun p u' hp hu' he => ?_, fun p b σ' hp he => ?_⟩
  · rw [List.lookup_cons_of_ne (padRequest_keyInput_ne_signInput hwidth hp hnode_lt hu)]
    exact hinv.nodes_eq_coin p hp
  · rcases List.mem_cons.mp hmem with hhead | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj hhead).1; exact ⟨hnode_lt, hu, hleaf⟩
    · obtain ⟨hq, hv, hex⟩ := hinv.edges_mem q v σ' htail
      exact ⟨hq, hv, fun h => let ⟨l, hl, h'⟩ := hex h; ⟨l, hsub l hl, h'⟩⟩
  · have hne : (p, u') ≠ (node, u) := fun h => by simp [h] at he
    rw [List.lookup_cons_of_ne hne] at he
    rw [List.lookup_cons_of_ne fun h => hne (Prod.ext_iff.mpr
      (padRequest_signInput_injective hwidth hp hnode_lt hu' hu h))]
    exact hinv.edges_none_coin_none p u' hp hu' he
  · by_cases hpb : (p, b.toNat) = (node, u)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpb
      rw [List.lookup_cons, beq_self_eq_true] at he
      obtain rfl := Option.some.inj he.symm
      obtain ⟨kp, kc, hkp, hkc, hσ⟩ := hinternal b rfl hp
      exact ⟨kp, kc, w, hkp, hkc, by simp, hσ⟩
    · rw [List.lookup_cons_of_ne hpb] at he
      obtain ⟨kp, kc, w', hkp, hkc, hw', hσ'⟩ := hinv.edges_some_internal p b σ' hp he
      refine ⟨kp, kc, w', hkp, hkc, ?_, hσ'⟩
      rw [List.lookup_cons_of_ne fun h => hpb (Prod.ext_iff.mpr
        (padRequest_signInput_injective hwidth (Nat.lt_of_succ_lt hp) hnode_lt
          (Bool.toNat_le b) hu h))]
      exact hw'

private theorem jointNodeKey_spec (S : IndexedSignatureScheme) (T : S.Seeded) {M d n : ℕ}
    (hwidth : 2 * d + 4 ≤ M) (hkgBudget : T.keyGenBudget n ≤ M)
    {root : List Bool × List Bool} {s : TreeState JointInner}
    (hinv : JointLazyInv S T M d n root s) {path : List Bool} (hpath : path.length < d) :
    PMF.RepInv (jointNodeKey S T M n path (s.1.1, s.1.2.1))
      (ProbComp.eval (memoize (fun _ => S.keyGen n) path s.1.2.1))
      (fun (k, (_, ns')) => (k, ns'))
      (fun (k, (cc', ns')) =>
        JointLazyInv S T M d n root ((cc', ns', s.1.2.2), s.2) ∧
        ns'.lookup path = some k ∧ k ∈ (ProbComp.eval (S.keyGen n)).support ∧
        ∀ q v, s.1.2.1.lookup q = some v → q ≠ path → ns'.lookup q = some v) := by
  obtain ⟨⟨cc, nodes, edges⟩, log⟩ := s
  have hrel := hinv.nodes_eq_coin path hpath
  simp only [jointNodeKey, lazyCoinRequest, memoize]
  cases hcc : cc.lookup (padRequest M (keyInput path)) with
  | some w =>
    rw [hcc, Option.map_some] at hrel
    refine ⟨by simp only [hrel, pmf_norm], fun ⟨k, cc', ns'⟩ hm => ?_⟩
    simp only [hrel] at hm; supp_cases hm
    exact ⟨hinv, hrel, T.keyGenWith_mem_support n _, fun _ _ h _ => h⟩
  | none =>
    rw [hcc, Option.map_none] at hrel
    refine ⟨?_, fun ⟨k, cc', ns'⟩ hm => ?_⟩
    · simp only [hrel, bind_pure_comp, pmf_norm]
      rw [T.eval_keyGen n _ le_rfl, ← BitString.uniformList_take hkgBudget]
      simp only [pmf_norm, PMF.map]
    · simp only [hrel, pmf_norm] at hm
      supp_cases hm with ⟨w, -, rfl, rfl, rfl⟩
      have hstay {q v} (hq : nodes.lookup q = some v) :
          ((path, T.keyGenWith n (w.take (T.keyGenBudget n))) :: nodes).lookup q = some v := by
        rw [List.lookup_cons_of_ne fun h => by subst h; rw [hq] at hrel; cases hrel]; exact hq
      refine ⟨⟨hstay hinv.root_lookup, fun p kp hp => ?_, fun p hp => ?_, hinv.edges_mem,
          fun p u hp hu he => ?_, fun p b σ hp he => ?_⟩,
        by simp, T.keyGenWith_mem_support n _,
        fun q v hqv hne => by rw [List.lookup_cons_of_ne hne]; exact hqv⟩
      · rcases List.mem_cons.mp hp with hhead | htail
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead; exact ⟨hpath, T.keyGenWith_mem_support n _⟩
        · exact hinv.nodes_mem p kp htail
      · by_cases hpeq : p = path
        · subst hpeq; simp
        · rw [List.lookup_cons_of_ne hpeq, List.lookup_cons_of_ne fun h =>
            hpeq (padRequest_keyInput_injective hwidth hp hpath h)]
          exact hinv.nodes_eq_coin p hp
      · rw [List.lookup_cons_of_ne (padRequest_keyInput_ne_signInput hwidth hpath hp hu).symm]
        exact hinv.edges_none_coin_none p u hp hu he
      · obtain ⟨kp, kc, w', hkp, hkc, hw', hσ⟩ := hinv.edges_some_internal p b σ hp he
        refine ⟨kp, kc, w', hstay hkp, hstay hkc, ?_, hσ⟩
        rw [List.lookup_cons_of_ne
          (padRequest_keyInput_ne_signInput hwidth hpath (Nat.lt_of_succ_lt hp)
            (Bool.toNat_le b)).symm]
        exact hw'

private theorem jointSignAt_none_spec (S : IndexedSignatureScheme) (T : S.Seeded)
    {M d n : ℕ} (hwidth : 2 * d + 4 ≤ M)
    {sk msg : List Bool} {u : ℕ} (hbud : T.signBudget sk u msg ≤ M)
    {root : List Bool × List Bool} {cc : CoinCache} {ns : NodeKeyCache} {es : EdgeSigCache}
    {q₀ q₁ sl₀ sl₁ : List (List Bool)} {b₀ b₁ : Bool}
    (hinv : JointLazyInv S T M d n root ((cc, ns, es), ⟨q₀, sl₀, b₀⟩))
    (hsub : ∀ l ∈ sl₀, l ∈ sl₁) {node : List Bool} (hnode_lt : node.length < d)
    (hu : u ≤ 1) (hes : es.lookup (node, u) = none)
    (hleaf : node.length = d - 1 →
      ∃ l ∈ sl₁, l.length = d ∧ node = l.take (d - 1) ∧ u = (l.getLastD false).toNat)
    (hinternal : ∀ b : Bool, b.toNat = u → node.length + 1 < d →
      ∃ kp kc, ns.lookup node = some kp ∧ ns.lookup (node ++ [b]) = some kc ∧
        kp.2 = sk ∧ kc.1 = msg) :
    PMF.RepInv (jointSignAt S T M node sk u msg (cc, es))
      (ProbComp.eval (memoize (fun _ => S.sign sk u msg) (node, u) es))
      (fun (σ, (_, es')) => (σ, es'))
      (fun (_, (cc', es')) =>
        JointLazyInv S T M d n root ((cc', ns, es'), ⟨q₁, sl₁, b₁⟩)) := by
  have hcc := hinv.edges_none_coin_none node u hnode_lt hu hes
  simp only [jointSignAt, lazyCoinRequest, memoize, hes, hcc, bind_pure_comp, pmf_norm]
  refine ⟨?_, fun _ hm => ?_⟩
  · rw [T.eval_sign sk u msg _ le_rfl, ← BitString.uniformList_take hbud]
    simp only [pmf_norm, PMF.map]
  · obtain ⟨w, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    refine jointLazyInv_insert_sign S T hwidth hinv hsub hnode_lt hu w _ hleaf fun b hb hp => ?_
    subst hb
    obtain ⟨kp, kc, hkp, hkc, rfl, rfl⟩ := hinternal b rfl hp
    exact ⟨kp, kc, hkp, hkc, rfl⟩

private theorem jointSignAt_internal_spec (S : IndexedSignatureScheme) (T : S.Seeded)
    {M d n : ℕ} (hwidth : 2 * d + 4 ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    {root kp kc : List Bool × List Bool} {cc : CoinCache} {ns : NodeKeyCache} {es : EdgeSigCache}
    {log : TreeLog} (hinv : JointLazyInv S T M d n root ((cc, ns, es), log))
    {node : List Bool} {bit : Bool} (hnode_lt : node.length + 1 < d)
    (hkp : ns.lookup node = some kp) (hkp_supp : kp ∈ (ProbComp.eval (S.keyGen n)).support)
    (hkc : ns.lookup (node ++ [bit]) = some kc)
    (hkc_supp : kc ∈ (ProbComp.eval (S.keyGen n)).support) :
    PMF.RepInv (jointSignAt S T M node kp.2 bit.toNat kc.1 (cc, es))
      (ProbComp.eval (memoize (fun _ => S.sign kp.2 bit.toNat kc.1) (node, bit.toNat) es))
      (fun (σ, (_, es')) => (σ, es'))
      (fun (_, (cc', es')) => JointLazyInv S T M d n root ((cc', ns, es'), log)) := by
  cases hes : es.lookup (node, bit.toNat) with
  | some σ₀ =>
    obtain ⟨kp', kc', w, hkp', hkc', hw, hσ₀⟩ := hinv.edges_some_internal node bit σ₀ hnode_lt hes
    cases Option.some.inj (hkp.symm.trans hkp')
    cases Option.some.inj (hkc.symm.trans hkc')
    simp only [jointSignAt, lazyCoinRequest, memoize, hes, hw, pmf_norm, ← hσ₀]
    exact PMF.RepInv.pure rfl hinv
  | none =>
    refine jointSignAt_none_spec S T hwidth
      (hsgBudget kp hkp_supp bit.toNat (Bool.toNat_le bit) kc.1 (Or.inr ⟨kc, hkc_supp, rfl⟩))
      hinv (fun _ h => h) (Nat.lt_of_succ_lt hnode_lt) (Bool.toNat_le bit) hes
      (fun _ => by omega) fun b hb _ => ⟨kp, kc, hkp, ?_, rfl, rfl⟩
    exact ((Bool.ofNat_toNat b).symm.trans (hb ▸ Bool.ofNat_toNat bit) : b = bit) ▸ hkc

private theorem jointCertify_spec (S : IndexedSignatureScheme) (T : S.Seeded) (depth : ℕ → ℕ)
    {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    {root : List Bool × List Bool} {s : TreeState JointInner}
    (hinv : JointLazyInv S T M (depth n) n root s) {leaf : List Bool}
    (hleaf : leaf.length = depth n) :
    PMF.RepInv (jointCertify S T depth M n leaf s.1)
      (ProbComp.eval (certifyLazy S depth n root leaf s.1.2)) Prod.snd
      (fun (cc', cert, ns', es') =>
        JointLazyInv S T M (depth n) n root ((cc', ns', es'), s.2) ∧
        cert.1 = leaf.take (depth n - 1) ∧ ns'.lookup cert.1 = some cert.2.1 ∧
        cert.2.1 ∈ (ProbComp.eval (S.keyGen n)).support) := by
  obtain ⟨⟨cc, nodes, edges⟩, log⟩ := s
  have hrootLen : ([] : List Bool).length < depth n := by simp; omega
  have hnk0 : jointNodeKey S T M n [] (cc, nodes) = PMF.pure (root, (cc, nodes)) := by
    have hrel := hinv.root_lookup ▸ hinv.nodes_eq_coin [] hrootLen
    cases hcc : cc.lookup (padRequest M (keyInput [])) with
    | none => simp [hcc] at hrel
    | some w =>
      rw [hcc, Option.map_some] at hrel
      simp only [jointNodeKey, lazyCoinRequest, memoize, hcc, hinv.root_lookup, pmf_norm,
        Option.some.inj hrel.symm]
  simp only [jointCertify, hnk0, certifyLazy, ProbComp.eval_iterate, pmf_norm]
  apply PMF.RepInv.iterate fun m (out : CoinCache × LazyCertState) =>
    JointLazyInv S T M (depth n) n root ((out.1, out.2.2.1, out.2.2.2), log) ∧
    out.2.1.1 = leaf.take m ∧ out.2.2.1.lookup out.2.1.1 = some out.2.1.2.1 ∧
    out.2.1.2.1 ∈ (ProbComp.eval (S.keyGen n)).support
  · rfl
  · exact ⟨hinv, rfl, hinv.root_lookup,
      (hinv.nodes_mem [] root (List.mem_of_lookup_eq_some hinv.root_lookup)).2⟩
  rintro m hm ⟨c, ⟨node, ⟨pk, sk⟩, certs⟩, ns, es⟩ ⟨hinv_c, hnode_eq, hns_node, hkey_supp⟩
  dsimp only at hinv_c hnode_eq hns_node hkey_supp
  have hnode_len : node.length = m := by
    rw [hnode_eq, List.length_take, hleaf, Nat.min_eq_left (by omega)]
  set cPath := node ++ [leaf.getD node.length false]
  have hne : node ≠ cPath := fun h => by have := congrArg List.length h; simp [cPath] at this
  simp only [jointCertifyStep, certifyStepLazy, pmf_norm]
  exact (jointNodeKey_spec S T hwidth hkgBudget hinv_c (by simp; omega)).bind
    fun ⟨child, c', ns'⟩ _ ⟨hinv_c', hns'_child, hchild_supp, hkeep⟩ =>
      (jointSignAt_internal_spec S T hwidth hsgBudget hinv_c' (by omega)
        (hkeep node (pk, sk) hns_node hne) hkey_supp hns'_child hchild_supp).map
        fun _ _ hinv'' => ⟨rfl, hinv'', by
          have hlt : m < leaf.length := by omega
          dsimp only [cPath]
          rw [hnode_len, hnode_eq, List.getD_eq_getElem _ _ hlt,
            List.take_succ_eq_append_getElem hlt], hns'_child, hchild_supp⟩

private theorem jointCoinBody_step_lazy (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    (root : List Bool × List Bool) (req : Unit × List Bool) (s : TreeState JointInner)
    (hinv : JointLazyInv S T M (depth n) n root s) :
    PMF.RepInv (guardedTreeHandler depth n (jointCoinBody S T depth M n) req s)
      (ProbComp.eval (lazySignHandler S depth n root req (s.1.2, s.2)))
      (fun (a, s') => (a, s'.1.2, s'.2))
      (fun (_, s') => JointLazyInv S T M (depth n) n root s') := by
  obtain ⟨inner, ⟨queried, seen, bad⟩⟩ := s
  rw [eval_lazySignHandler_eq]
  apply guardedTreeHandler_map depth n Prod.snd (JointLazyInv S T M (depth n) n root) req
    inner queried seen bad
    (fun _ => ⟨hinv.root_lookup, hinv.nodes_mem, hinv.nodes_eq_coin, hinv.edges_mem,
      hinv.edges_none_coin_none, hinv.edges_some_internal⟩)
  intro hmsg _ leaf hleaf_supp hseen
  have hleaf_len := BitString.length_of_mem_support_uniformList hleaf_supp
  dsimp only [jointCoinBody, lazySignBody]
  exact (jointCertify_spec S T depth hdepth_pos hwidth hkgBudget hsgBudget hinv hleaf_len).bind
    fun ⟨cc', ⟨node, ⟨pk, sk⟩, certs⟩, ns', es'⟩ _ ⟨hinv_c', hnode_eq, _, hkey_supp⟩ => by
      dsimp only at hnode_eq hkey_supp ⊢
      have hnode_len : node.length = depth n - 1 := by
        rw [hnode_eq, List.length_take, hleaf_len, Nat.min_eq_left (by omega)]
      set uLast := (leaf.getLastD false).toNat
      have hes'_none : es'.lookup (node, uLast) = none := by
        cases hlk : es'.lookup (node, uLast) with
        | none => rfl
        | some σ₀ =>
          obtain ⟨l, hl_mem, hl_len, hq_eq, hv_eq⟩ :=
            (hinv_c'.edges_mem node uLast σ₀ (List.mem_of_lookup_eq_some hlk)).2.2 hnode_len
          have hlast_eq : leaf.getLastD false = l.getLastD false := by
            rw [← Bool.ofNat_toNat (leaf.getLastD false), ← Bool.ofNat_toNat (l.getLastD false),
              show (leaf.getLastD false).toNat = (l.getLastD false).toNat from hv_eq]
          have hll : leaf = l := by
            rw [← take_sub_one_append_getLastD hdepth_pos hleaf_len,
              ← take_sub_one_append_getLastD hdepth_pos hl_len, ← hnode_eq, hq_eq, hlast_eq]
          simp only [hll ▸ hl_mem, List.contains_eq_mem, decide_true] at hseen
          cases hseen
      exact (jointSignAt_none_spec S T hwidth
        (hsgBudget (pk, sk) hkey_supp uLast (Bool.toNat_le _) req.2 (Or.inl hmsg))
        hinv_c' (fun _ h => List.mem_cons_of_mem _ h) (by omega) (Bool.toNat_le _) hes'_none
        (fun _ => ⟨leaf, List.mem_cons_self, hleaf_len, hnode_eq, rfl⟩)
        fun _ _ hp => by omega).map fun _ _ hinv'' => ⟨rfl, hinv''⟩

private noncomputable def coinGameWith (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (adversary : Forger)
    (h : Unit × List Bool → StateT (TreeState CoinCache) PMF (List Bool)) (w₀ : List Bool) :
    PMF Bool :=
  let root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
  let pk := encPair encUnary encBits (n, root.1)
  let init : TreeState CoinCache := ([(padRequest M (keyInput []), w₀)], ⟨[], [], false⟩)
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h)
    (adversary n pk)).run init).map fun (msig, (_, log)) =>
      (msig.1.length == n) && !log.queried.contains msig.1 && verify S depth pk msig.1 msig.2

private theorem eval_treeIdealGame_eq_unguarded (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (treeIdealGame S T depth N adversary n) =
      (BitString.uniformList (N n)).bind
        (coinGameWith S T depth (N n) n adversary
          (unguardedTreeHandler depth n (coinSignBody S T depth (N n) n))) := by
  set M := N n
  rw [eval_treeIdealGame_eq_lazyCoin]
  have hroot : (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (nodeKeyO S T n [])).run [] =
      (BitString.uniformList M).map fun w₀ =>
        (T.keyGenWith n (w₀.take (T.keyGenBudget n)), [(padRequest M (keyInput []), w₀)]) := by
    simp only [nodeKeyO, OracleComp.interpret_map, StateT.run_map, run_interpret_coinRequest,
      lazyCoinRequest, memoize, List.lookup_nil, pmf_norm, PMF.map]
  simp only [simulateTreeGame, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
    pmf_norm]
  rw [hroot, PMF.bind_map]
  apply PMF.bind_congr_on_support; intro w₀ _
  set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
  set pk := encPair encUnary encBits (n, root.1)
  set cc₀ : CoinCache := [(padRequest M (keyInput []), w₀)]
  have hstep : ∀ req (s : TreeState CoinCache),
      ((unguardedTreeHandler depth n (coinSignBody S T depth M n) req s).map
        fun (a, s') => (a, (s'.2.queried, s'.1))) =
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (signHandler S T depth n req s.2.queried)).run s.1).map fun ((a, b), c) => (a, b, c)) := by
    rintro req ⟨cc, ⟨queried, seen, bad⟩⟩
    simp only [unguardedTreeHandler, signHandler, signO]
    split_ifs with hmsg
    · rw [bind_assoc, OracleComp.run_interpret_bind, ProbOracleComp.run_interpret_sample,
        BitString.eval_sampleList]
      simp only [pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun leaf _ => ?_
      simp only [coinSignBody, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
        pmf_norm]
    · simp only [pure_bind, OracleComp.run_interpret_pure, pmf_norm]
  have hflat := ProbOracleComp.run_interpret_run_interpret (signHandler S T depth n)
    (lazyCoinHandler M) (adversary n pk) [] cc₀
  have hunguard := ProbOracleComp.run_interpret_map_state _
    (fun q (st : List (List Bool) × CoinCache) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
        (signHandler S T depth n q st.1)).run st.2).map fun ((a, b), c) => (a, b, c))
    (fun s : TreeState CoinCache => (s.2.queried, s.1)) hstep
    (adversary n pk) (cc₀, TreeLog.mk [] [] false)
  have hcomb := congrArg (PMF.map fun ((msig, queried), _) =>
      (msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2)
    (hflat.trans (congrArg (PMF.map fun (a, b, c) => ((a, b), c)) hunguard.symm))
  simpa only [coinGameWith, pmf_norm, PMF.map] using hcomb

private theorem eval_lazyTreeGame_eq_guarded (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    (adversary : Forger) :
    ProbComp.eval (lazyTreeGame S depth adversary n) =
      (BitString.uniformList M).bind
        (coinGameWith S T depth M n adversary
          (guardedTreeHandler depth n (coinSignBody S T depth M n))) := by
  have hrootLaw : ProbComp.eval (S.keyGen n) =
      (BitString.uniformList M).map fun w₀ => T.keyGenWith n (w₀.take (T.keyGenBudget n)) := by
    rw [T.eval_keyGen n _ le_rfl, ← BitString.uniformList_take hkgBudget, PMF.map_comp]; rfl
  simp only [lazyTreeGame, hrootLaw, ProbOracleComp.eval_run_interpret, pmf_norm]
  apply PMF.bind_congr_on_support; intro w₀ _
  set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
  set pk := encPair encUnary encBits (n, root.1)
  set jInit : TreeState JointInner :=
    (([(padRequest M (keyInput []), w₀)], [([], root)], []), ⟨[], [], false⟩)
  have hrootLen : ([] : List Bool).length < depth n := by simp; omega
  have hjInv : JointLazyInv S T M (depth n) n root jInit := by
    refine ⟨by simp [jInit], ?_, ?_, ?_, ?_, ?_⟩
    · intro p k hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hp)
      exact ⟨hrootLen, T.keyGenWith_mem_support n _⟩
    · intro p hp; by_cases hp0 : p = []
      · subst hp0; simp [jInit, root]
      · simp only [jInit, List.lookup_cons_of_ne hp0,
          List.lookup_cons_of_ne fun h => hp0 (padRequest_keyInput_injective hwidth hp hrootLen h),
          List.lookup_nil, Option.map_none]
    · intro _ _ _ h; cases h
    · intro p u hp hu _
      simp only [jInit,
        List.lookup_cons_of_ne (padRequest_keyInput_ne_signInput hwidth hrootLen hp hu).symm,
        List.lookup_nil]
    · intro _ _ _ _ h; cases h
  have hstep := jointCoinBody_step_lazy S T depth hdepth_pos hwidth hkgBudget hsgBudget root
  have hprojLazy := ProbOracleComp.run_interpret_map_state_of_invariant _
    (fun q s => ProbComp.eval (lazySignHandler S depth n root q s))
    (fun s => (s.1.2, s.2)) _
    (fun q s hs a s' hm => (hstep q s hs).2 (a, s') hm)
    (fun q s hs => (hstep q s hs).1) (adversary n pk) jInit hjInv
  have hprojGuard := ProbOracleComp.run_interpret_map_state _
    (guardedTreeHandler depth n (coinSignBody S T depth M n)) (fun s => (s.1.1, s.2))
    (fun q ⟨inner, ⟨queried, seen, bad⟩⟩ => (guardedTreeHandler_map depth n
      (body₂ := coinSignBody S T depth M n) Prod.fst (fun _ => True) q inner queried seen bad
      (fun _ => trivial)
      fun _ _ leaf _ _ => .of_eq (map_dropCaches_jointCoinBody S T depth M n leaf q.2 inner)).1)
    (adversary n pk) jInit
  have hwinL := congrArg (PMF.map fun (msig, (_, log)) =>
    (msig.1.length == n) && !log.queried.contains msig.1 && verify S depth pk msig.1 msig.2)
    hprojLazy.symm
  have hwinG := congrArg (PMF.map fun (msig, (_, log)) =>
    (msig.1.length == n) && !log.queried.contains msig.1 && verify S depth pk msig.1 msig.2)
    hprojGuard
  dsimp only [coinGameWith]
  simp only [pmf_norm] at hwinL hwinG ⊢
  simpa only [PMF.map, Function.comp_def] using hwinL.trans hwinG

/-- **From ideal coins to lazy tree signing**: when `N n` covers all padded tree request widths and
seeded key/signature coin budgets, replacing the uniform random function in `treeIdealGame` with
lazy node keys, lazy edge signatures, and leaf-collision aborts (`lazyTreeGame`) loses at most
`(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)` across any `Q`-query adversary. -/
theorem succProbability_treeIdealGame_le_lazy (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) {n Q : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ N n)
    (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ N n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) ≤
      Game.succProbability (ProbComp.eval (lazyTreeGame S depth adversary n)) +
        (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) := by
  set err : ℝ≥0 := (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)
  have hle_enn : ProbComp.eval (treeIdealGame S T depth N adversary n) true ≤
      ProbComp.eval (lazyTreeGame S depth adversary n) true + (err : ℝ≥0∞) := by
    rw [eval_treeIdealGame_eq_unguarded,
      eval_lazyTreeGame_eq_guarded S T depth hdepth_pos hwidth hkgBudget hsgBudget adversary]
    refine Probability.PMF.bind_apply_le_add_const_on_support _ true fun w₀ _ => ?_
    set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
    set pk := encPair encUnary encBits (n, root.1)
    have hiub := identicalUntilBad_treeHandler depth n (coinSignBody S T depth (N n) n)
    have hdiff := OracleComp.IdenticalUntilBad.bind_apply_le hiub (adversary n pk)
      ([(padRequest (N n) (keyInput []), w₀)], ⟨[], [], false⟩)
      (fun (msig, (_, log)) => PMF.pure
        ((msig.1.length == n) && !log.queried.contains msig.1 &&
          verify S depth pk msig.1 msig.2)) true
    rw [OracleComp.IdenticalUntilBad.bad_eq hiub] at hdiff
    exact hdiff.trans (add_le_add le_rfl (toOuterMeasure_bad_guardedTreeHandler_le depth n Q _
      (hq root (T.keyGenWith_mem_support n _)) _ []))
  have h := ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩) hle_enn
  rwa [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at h

end TreeSignature

end Cslib.Crypto
