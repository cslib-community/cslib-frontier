/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TreeSignature.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.Oracle.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.GetD

/-!
# Efficiency of the planted-node tree-signature reduction

Proves that `TreeSignature.indexedForger` is uniformly strict oracle PPT whenever `depth`,
`slotBound`, and `sigCap` are computable in polynomial time (in unary) and the underlying tree
forger `adversary` is strict oracle PPT. Isolating the polynomial-time machine and growth
certificates here allows them to elaborate in parallel with the probabilistic coupling hops in
`TreeSignature.IdealToLazy` and `TreeSignature.LazyToIndexed`.

## Main results

* `Cslib.Crypto.TreeSignature.isOraclePPT_indexedForger`: uniform strict oracle-PPT certificate
  for `indexedForger`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.3, Theorem 14.6, p. 600.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace TreeSignature

attribute [local fun_prop]
  ComputableInPolyTime.bool_and'
  ComputableInPolyTime.unary_dyadicSize
  IsPPTOn.replicate

@[local fun_prop]
private theorem getLastD_fp {α : Type} {encA : α ↪ List Bool} {l : α → List Bool} (d : Bool)
    (hl : ComputableInPolyTime l encA encBits) :
    ComputableInPolyTime (fun a => (l a).getLastD d) encA encBool := by
  have heq : (fun a => (l a).getLastD d) = fun a => (l a).getD ((l a).length - 1) d := by
    funext a
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  rw [heq]; fun_prop

@[local fun_prop]
private theorem encodeSignature_funProp {α : Type} {encA : α ↪ List Bool}
    {leaf : α → List Bool} {certs : α → List (List Bool × List Bool)} {last : α → List Bool}
    (hl : ComputableInPolyTime leaf encA encBits)
    (hc : ComputableInPolyTime certs encA (encList (encPair encBits encBits)))
    (hs : ComputableInPolyTime last encA encBits) :
    ComputableInPolyTime (fun a => encodeSignature (leaf a) (certs a) (last a)) encA encBits := by
  unfold encodeSignature; fun_prop

@[local fun_prop]
private theorem signatureDecoder_funProp {α : Type} {encA : α ↪ List Bool} {s : α → List Bool}
    (hs : ComputableInPolyTime s encA encBits) :
    ComputableInPolyTime (fun a => signatureDecoder.decode (s a)) encA
      (encPair encBits (encPair (encList (encPair encBits encBits)) encBits)) :=
  signatureDecoder.computableInPolyTime.comp hs

/-- The visited node-to-slot cache, encoded as a list of entries; each entry is a node path in
binary followed by its slot in unary, the path framed. -/
private abbrev encNodeCache : NodeSlotCache ↪ List Bool :=
  encList (encPair encBits encUnary)

/-- The edge-signature cache, encoded as a list of entries; each entry is an edge (a node path in
binary followed by the edge bit in unary, the path framed), framed, followed by its signature in
binary. -/
private abbrev encEdgeCache : EdgeSigCache ↪ List Bool :=
  encList (encPair (encPair encBits encUnary) encBits)

/-- A list of pairs of words, such as the pre-sampled node key pairs or a certificate chain;
each pair is its first word in binary, framed, followed by its second word in binary. -/
private abbrev encKeys : List (List Bool × List Bool) ↪ List Bool :=
  encList (encPair encBits encBits)

/-- Multi-tape encoding of `TreeLog`: queried messages (framed), sampled leaves (framed), and the
leaf-collision abort flag, each list holding its words in binary. Matches
`encPair (encList encBits) (encPair (encList encBits) encBool)`. -/
private enc_structure encTreeLog : TreeLog where
  queried : (encList encBits),
  seenLeaves : (encList encBits),
  bad : encBool

private example (l : TreeLog) :
    encTreeLog l =
      encPair (encList encBits) (encPair (encList encBits) encBool)
        (l.queried, l.seenLeaves, l.bad) := rfl

/-- The state of `plantedTreeHandler`, encoded as a nested pair: the visited node cache (framed)
and the edge-signature cache, framed together, followed by `encTreeLog` (the queried messages,
sampled leaves, and abort flag). -/
private abbrev encPlantedState : PlantedState ↪ List Bool :=
  encPair (encPair encNodeCache encEdgeCache) encTreeLog

/-- The chain state of `certifyPlanted`, encoded as a nested pair: the node path in binary
(framed), the slot in unary (framed) and the certificates (key/signature word pairs, `encKeys`),
framed together, followed by the visited node cache (framed) and the edge-signature cache. -/
private abbrev encPlantedCert : PlantedCertState ↪ List Bool :=
  encPair (encPair encBits (encPair encUnary encKeys)) (encPair encNodeCache encEdgeCache)

private theorem length_fst_getD_keys_le (keys : List (List Bool × List Bool)) (idx : ℕ) :
    (keys.getD idx ([], [])).1.length ≤ (encKeys keys).length := by
  by_cases h : idx < keys.length
  · exact (length_le_encPair_left encBits encBits _).trans
      (length_le_encList_of_mem (encPair encBits encBits) (List.getD_mem _ h))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    exact Nat.zero_le _

@[local fun_prop]
private theorem isPPTOn_plantNodeKeys (S : IndexedSignatureScheme) {slotBound : ℕ → ℕ}
    (hslot : ComputableInPolyTime slotBound encUnary encUnary) :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary) encKeys
      (fun c : (ℕ × List Bool) × ℕ => plantNodeKeys S slotBound c.1.1 c.2 c.1.2) := by
  have _ := S.keyGen_ppt
  dsimp only [plantNodeKeys]
  fun_prop

@[local fun_prop]
private theorem isOraclePPTOn_visitNodeM {γ : Type} {enc : γ ↪ List Bool}
    {cap : γ → ℕ} {path : γ → List Bool} {visited : γ → NodeSlotCache}
    (hcap : ComputableInPolyTime cap enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits)
    (hvisited : ComputableInPolyTime visited enc encNodeCache) :
    IsOraclePPTOn enc (encPair encUnary encNodeCache)
      (fun a => visitNodeM (cap a) (path a) (visited a)) :=
  IsOraclePPTOn.memoize (compute := fun a _ => pure (min (visited a).length (cap a)))
    (ComputableInPolyTime.isOraclePPTOn (by fun_prop)) hpath hvisited

@[local fun_prop]
private theorem isOraclePPTOn_signEdgeM (S : IndexedSignatureScheme) {γ : Type}
    {enc : γ ↪ List Bool} {keys : γ → List (List Bool × List Bool)}
    {target sigCap idx u : γ → ℕ} {path msg : γ → List Bool} {edges : γ → EdgeSigCache}
    (hkeys : ComputableInPolyTime keys enc encKeys)
    (htarget : ComputableInPolyTime target enc encUnary)
    (hsigCap : ComputableInPolyTime sigCap enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits)
    (hidx : ComputableInPolyTime idx enc encUnary)
    (hu : ComputableInPolyTime u enc encUnary)
    (hmsg : ComputableInPolyTime msg enc encBits)
    (hedges : ComputableInPolyTime edges enc encEdgeCache) :
    IsOraclePPTOn enc (encPair encBits encEdgeCache)
      (fun a => signEdgeM S (keys a) (target a) (sigCap a) (path a) (idx a) (u a) (msg a)
        (edges a)) := by
  have _ := S.sign_ppt
  unfold signEdgeM signEdgeRaw
  exact IsOraclePPTOn.memoize
    (compute := fun a _ =>
      if idx a = target a then
        List.take (sigCap a) <$> ProbOracleComp.query ((), encPair encUnary encBits (u a, msg a))
      else
        List.take (sigCap a) <$>
          ProbOracleComp.sample (S.sign ((keys a).getD (idx a) ([], [])).2 (u a) (msg a)))
    (IsOraclePPTOn.ite (by fun_prop)
      (IsOraclePPTOn.query_take () (by fun_prop) hsigCap)
      (((S.sign_ppt.preprocess
        (prepare := fun a => (((keys a).getD (idx a) ([], [])).2, u a, msg a))
        (by fun_prop)).isOraclePPTOn (Operation := Unit)).map_with (by fun_prop)))
    (hpath.prod hu) hedges

private theorem length_le_of_mem_support_signEdgeRaw (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap idx u : ℕ) (msg : List Bool)
    {σ : List Bool} (hσ : σ ∈ OracleComp.support (signEdgeRaw S keys target sigCap idx u msg)) :
    σ.length ≤ sigCap := by
  unfold signEdgeRaw at hσ
  split_ifs at hσ <;>
    (obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hσ; exact List.length_take_le _ _)

/-- Input to `certifyPlanted`: `((keys, (target, sigCap), (n, leaf)), (visited₀, edges₀))`. -/
private abbrev CertLoopIn :=
  (List (List Bool × List Bool) × (ℕ × ℕ) × (ℕ × List Bool)) × (NodeSlotCache × EdgeSigCache)

private abbrev CertLoopIn.keys (a : CertLoopIn) := a.1.1
private abbrev CertLoopIn.target (a : CertLoopIn) := a.1.2.1.1
private abbrev CertLoopIn.sigCap (a : CertLoopIn) := a.1.2.1.2
private abbrev CertLoopIn.parameter (a : CertLoopIn) := a.1.2.2.1
private abbrev CertLoopIn.leaf (a : CertLoopIn) := a.1.2.2.2
private abbrev CertLoopIn.visited (a : CertLoopIn) := a.2.1
private abbrev CertLoopIn.edges (a : CertLoopIn) := a.2.2

private theorem isOraclePPTOn_certifyStepPlanted (S : IndexedSignatureScheme) :
    IsOraclePPTOn
      (encPair (encPair encKeys (encPair (encPair encUnary encUnary) encBits)) encPlantedCert)
      encPlantedCert
      (fun q : (List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState =>
        certifyStepPlanted S q.1.1 q.1.2.1.1 q.1.2.1.2 q.1.2.2 q.2) := by
  let encIn :=
    encPair (encPair encKeys (encPair (encPair encUnary encUnary) encBits)) encPlantedCert
  let encMid := encPair encIn (encPair encUnary encNodeCache)
  let encEnd := encPair encMid (encPair encBits encEdgeCache)
  have hbit : ComputableInPolyTime (fun q => q.1.2.2.getD q.2.1.1.length false) encIn encBool :=
    .bitsGetDWithInput (by fun_prop) (by fun_prop) false
  have hpath : ComputableInPolyTime
      (fun q => q.2.1.1 ++ [q.1.2.2.getD q.2.1.1.length false]) encIn encBits :=
    .bitsAppend (by fun_prop) (.bitsCons hbit (.const []))
  have hchildPk : ComputableInPolyTime
      (fun r => (r.1.1.1.getD r.2.1 ([], [])).1) encMid encBits :=
    (ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) ([], [])).fst'
  have hvisit := isOraclePPTOn_visitNodeM (enc := encIn) (cap := fun q => q.1.1.length)
    (path := fun q => q.2.1.1 ++ [q.1.2.2.getD q.2.1.1.length false])
    (visited := fun q => q.2.2.1) (by fun_prop) hpath (by fun_prop)
  have hsign := isOraclePPTOn_signEdgeM S (enc := encMid)
    (keys := fun r => r.1.1.1) (target := fun r => r.1.1.2.1.1)
    (sigCap := fun r => r.1.1.2.1.2) (path := fun r => r.1.2.1.1) (idx := fun r => r.1.2.1.2.1)
    (u := fun r => (r.1.1.2.2.getD r.1.2.1.1.length false).toNat)
    (msg := fun r => (r.1.1.1.getD r.2.1 ([], [])).1) (edges := fun r => r.1.2.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    ((by fun_prop : ComputableInPolyTime Bool.toNat encBool encUnary).comp
      (hbit.comp (.fst encIn _))) hchildPk (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun s => ((s.1.1.2.1.1 ++ [s.1.1.1.2.2.getD s.1.1.2.1.1.length false], s.1.2.1,
        s.1.1.2.1.2.2 ++ [((s.1.1.1.1.getD s.1.2.1 ([], [])).1, s.2.1)]), (s.1.2.2, s.2.2)))
      encEnd encPlantedCert :=
    ((hpath.comp (by fun_prop)).prod
      ((by fun_prop : ComputableInPolyTime _ encEnd encUnary).prod
        (.listAppend' (by fun_prop)
          (.cons' ((hchildPk.comp (.fst encMid _)).prod (by fun_prop)) (.const []))))).prod
      (by fun_prop)
  exact hvisit.bind_with (hsign.bind_with hpost.isOraclePPTOn)

/-- Size invariant tracked across the `depth n - 1` iterations of `certifyPlanted`. -/
private structure PlantedLoopInv (Mv Me : ℕ) (a : CertLoopIn) (i : ℕ)
    (state : PlantedCertState) : Prop where
  node_len : state.1.1.length = i
  idx_le : state.1.2.1 ≤ Mv
  certs_len : state.1.2.2.length = i
  certs_bound : ∀ c ∈ state.1.2.2, c.1.length ≤ (encKeys a.keys).length ∧ c.2.length ≤ Me
  visited_le : ∀ e ∈ state.2.1, e.2 ≤ Mv
  edges_le : ∀ e ∈ state.2.2, e.2.length ≤ Me
  visited_enc_le : (encNodeCache state.2.1).length ≤
    (encNodeCache a.visited).length + i * (4 * (i + 1) + 2 * Mv + 3)
  edges_enc_le : (encEdgeCache state.2.2).length ≤
    (encEdgeCache a.edges).length + i * (8 * i + 2 * Me + 11)

private theorem plantedLoopInv_step (S : IndexedSignatureScheme) {Mv Me : ℕ} (a : CertLoopIn)
    (hMv : a.keys.length ≤ Mv) (hMe : a.sigCap ≤ Me) (i : ℕ) (state : PlantedCertState)
    (hinv : PlantedLoopInv Mv Me a i state) (next : PlantedCertState)
    (hnext : next ∈ OracleComp.support
      (certifyStepPlanted S a.keys a.target a.sigCap a.leaf state)) :
    PlantedLoopInv Mv Me a (i + 1) next := by
  rcases a with ⟨⟨keys, ⟨target, sigCap⟩, ⟨n, leaf⟩⟩, ⟨visited₀, edges₀⟩⟩
  rcases state with ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩
  supp_cases hnext [certifyStepPlanted, OracleComp.support] with
    ⟨⟨childIdx, visited'⟩, hvisStep, ⟨σ, edges'⟩, hedgStep, rfl⟩
  have hvBound := ProbOracleComp.memoize_call_size_le encBits encUnary
    (fun _ => pure (min visited.length keys.length))
    (node ++ [leaf.getD node.length false]) visited Mv
    (fun e he => by simpa only [encUnary_apply, List.length_replicate] using hinv.visited_le e he)
    (fun val hval => by
      rw [OracleComp.eq_of_mem_supportWith_pure hval]
      simpa only [encUnary_apply, List.length_replicate] using (Nat.min_le_right _ _).trans hMv)
    hvisStep
  have heBound := ProbOracleComp.memoize_call_size_le (encPair encBits encUnary) encBits
    (fun _ => signEdgeRaw S keys target sigCap idx
      (leaf.getD node.length false).toNat (keys.getD childIdx ([], [])).1)
    (node, (leaf.getD node.length false).toNat) edges Me
    (fun e he => by simpa only [encBits_apply] using hinv.edges_le e he)
    (fun val hval => by
      simpa only [encBits_apply] using
        (length_le_of_mem_support_signEdgeRaw S keys target sigCap idx _ _ hval).trans hMe)
    hedgStep
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate,
    List.length_append, List.length_singleton, hinv.node_len] at hvBound heBound
  have hu : (leaf.getD i false).toNat ≤ 1 := Bool.toNat_le _
  refine ⟨by simp [hinv.node_len], hvBound.1, by simp [hinv.certs_len], ?_,
    hvBound.2.1, heBound.2.1, ?_, ?_⟩
  · rintro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hinv.certs_bound c hc
    · rw [List.mem_singleton.mp hc]
      exact ⟨length_fst_getD_keys_le keys childIdx, heBound.1⟩
  · have hvisLen := hinv.visited_enc_le
    dsimp only [encNodeCache, CertLoopIn.visited] at hvisLen ⊢
    have := Nat.mul_le_mul_left i
      (by omega : 4 * (i + 1) + 2 * Mv + 3 ≤ 4 * (i + 1 + 1) + 2 * Mv + 3)
    have := Nat.add_one_mul i (4 * (i + 1 + 1) + 2 * Mv + 3)
    exact hvBound.2.2.trans (by omega)
  · have hedgLen := hinv.edges_enc_le
    dsimp only [encEdgeCache, CertLoopIn.edges] at hedgLen ⊢
    have := Nat.mul_le_mul_left i (by omega : 8 * i + 2 * Me + 11 ≤ 8 * (i + 1) + 2 * Me + 11)
    have := Nat.add_one_mul i (8 * (i + 1) + 2 * Me + 11)
    exact heBound.2.2.trans (by omega)

private theorem plantedLoopInv_enc_bounds {Mv Me d i : ℕ} {a : CertLoopIn}
    {state : PlantedCertState} (hi : i ≤ d)
    (hinv : PlantedLoopInv Mv Me a i state) :
    (encKeys state.1.2.2).length ≤ d * (2 * (2 * (encKeys a.keys).length + 1 + Me) + 1) ∧
    (encNodeCache state.2.1).length ≤
      (encNodeCache a.visited).length + d * (4 * (d + 1) + 2 * Mv + 3) ∧
    (encEdgeCache state.2.2).length ≤
      (encEdgeCache a.edges).length + d * (8 * d + 2 * Me + 11) := by
  have hcertsList : (encKeys state.1.2.2).length ≤
      state.1.2.2.length * (2 * (2 * (encKeys a.keys).length + 1 + Me) + 1) :=
    length_encList_le (encPair encBits encBits) _ fun c hc => by
      obtain ⟨h1, h2⟩ := hinv.certs_bound c hc
      enc_len
  refine ⟨hcertsList.trans (by rw [hinv.certs_len]; gcongr),
    hinv.visited_enc_le.trans (by gcongr), hinv.edges_enc_le.trans (by gcongr)⟩

private theorem isOraclePPTOn_certifyPlanted (S : IndexedSignatureScheme) {depth : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair encKeys (encPair (encPair encUnary encUnary) (encPair encUnary encBits)))
        (encPair encNodeCache encEdgeCache))
      encPlantedCert
      (fun a : CertLoopIn =>
        certifyPlanted S depth a.keys a.target a.sigCap a.parameter a.leaf a.2) := by
  let encLoopIn :=
    encPair (encPair encKeys (encPair (encPair encUnary encUnary) (encPair encUnary encBits)))
      (encPair encNodeCache encEdgeCache)
  obtain ⟨cd, dd, hdd⟩ := hdepth.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hdd
  have hleIn (a : CertLoopIn) :
      a.keys.length ≤ (encLoopIn a).length ∧ (encKeys a.keys).length ≤ (encLoopIn a).length ∧
      a.sigCap ≤ (encLoopIn a).length ∧ a.parameter ≤ (encLoopIn a).length ∧
      (encNodeCache a.visited).length ≤ (encLoopIn a).length ∧
      (encEdgeCache a.edges).length ≤ (encLoopIn a).length := by
    rcases a with ⟨⟨keys, _, ⟨n, leaf⟩⟩, ⟨visited, edges⟩⟩
    have hk := length_le_length_encList (encPair encBits encBits) keys
    enc_len [CertLoopIn.keys, CertLoopIn.sigCap, CertLoopIn.parameter, CertLoopIn.visited,
      CertLoopIn.edges, encLoopIn, encKeys]
  let bound (L : ℕ) : ℕ :=
    let d := cd * (L + 1) ^ dd
    let certB := d * (2 * (3 * L + 1) + 1)
    2 * (2 * d + 1 + (2 * L + 1 + certB)) + 1 +
      (2 * (L + d * (4 * (d + 1) + 2 * L + 3)) + 1 + (L + d * (8 * d + 2 * L + 11)))
  refine (IsOraclePPTOn.iterateWith_spec (input := encLoopIn) (stateEncoding := encPlantedCert)
    (count := fun a : CertLoopIn => depth a.parameter - 1)
    (initial := fun a => ((([], 0, []), a.2) : PlantedCertState))
    (step := fun (a : CertLoopIn) state =>
      certifyStepPlanted S a.keys a.target a.sigCap a.leaf state)
    (by fun_prop) (by fun_prop)
    ((isOraclePPTOn_certifyStepPlanted S).preprocess
      (prepare := fun pair : CertLoopIn × PlantedCertState =>
        ((pair.1.keys, (pair.1.target, pair.1.sigCap), pair.1.leaf), pair.2))
      (by fun_prop))
    (fun a i state => PlantedLoopInv (encLoopIn a).length (encLoopIn a).length a i state)
    (fun a => ⟨rfl, Nat.zero_le _, rfl, by simp,
      fun e he => by
        have h := ((length_le_encPair_right encBits encUnary e).trans
          (length_le_encList_of_mem (encPair encBits encUnary) he)).trans (hleIn a).2.2.2.2.1
        simpa only [encUnary_apply, List.length_replicate] using h,
      fun e he => by
        have h := ((length_le_encPair_right (encPair encBits encUnary) encBits e).trans
          (length_le_encList_of_mem (encPair (encPair encBits encUnary) encBits) he)).trans
          (hleIn a).2.2.2.2.2
        simpa only [encBits_apply] using h,
      by simp, by simp⟩)
    (fun a i state _ hinv next hnext =>
      plantedLoopInv_step S a (hleIn a).1 (hleIn a).2.2.1 i state hinv next hnext)
    (size := fun a => bound (encLoopIn a).length)
    (PolyBounded.of_polynomiallyBounded _ (by dsimp only [bound]; fun_prop))
    (fun (a : CertLoopIn) i ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩ hi hinv => by
      obtain ⟨-, hKE, -, hpar, hVE, hEE⟩ := hleIn a
      have hd : depth a.parameter ≤ cd * ((encLoopIn a).length + 1) ^ dd :=
        (hdd a.parameter).trans (by gcongr)
      obtain ⟨hcB, hvB, heB⟩ := plantedLoopInv_enc_bounds (hi.trans (Nat.sub_le _ _)) hinv
      have hnode : node.length ≤ cd * ((encLoopIn a).length + 1) ^ dd :=
        hinv.node_len ▸ (hi.trans (Nat.sub_le _ _)).trans hd
      have hidx : idx ≤ (encLoopIn a).length := hinv.idx_le
      let dB := cd * ((encLoopIn a).length + 1) ^ dd
      have hcB' := hcB.trans
        (Nat.mul_le_mul hd (by omega : _ ≤ 2 * (3 * (encLoopIn a).length + 1) + 1))
      have hvB' := hvB.trans (Nat.add_le_add hVE
        (Nat.mul_le_mul hd (by omega : _ ≤ 4 * (dB + 1) + 2 * (encLoopIn a).length + 3)))
      have heB' := heB.trans (Nat.add_le_add hEE
        (Nat.mul_le_mul hd (by omega : _ ≤ 8 * dB + 2 * (encLoopIn a).length + 11)))
      dsimp only [dB] at hcB' hvB' heB'
      dsimp only [bound]
      enc_len)).1

/-- Caller tuple for `plantedTreeHandler`: `(((n, vk), target), keys)`. -/
private abbrev ForgerCaller := ((ℕ × List Bool) × ℕ) × List (List Bool × List Bool)

private theorem isOraclePPTOn_plantedTreeHandler (S : IndexedSignatureScheme)
    {depth sigCap : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hsigCap : ComputableInPolyTime sigCap encUnary encUnary) :
    let encCaller := encPair (encPair (encPair encUnary encBits) encUnary) encKeys
    IsOraclePPTOn
      (encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) encPlantedState))
      (encPair encBits encPlantedState)
      (fun pair : ForgerCaller × ((Unit × List Bool) × PlantedState) =>
        plantedTreeHandler S depth pair.1.2 pair.1.1.2 (sigCap pair.1.1.1.1) pair.1.1.1.1
          pair.2.1 pair.2.2) := by
  intro encCaller
  let encH := encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) encPlantedState)
  let encHL := encPair encH encBits
  have hcert := (isOraclePPTOn_certifyPlanted S hdepth).preprocess (input := encHL)
    (prepare := fun q => (((q.1.1.2, (q.1.1.1.2, sigCap q.1.1.1.1.1), (q.1.1.1.1.1, q.2)),
      (q.1.2.2.1.1, q.1.2.2.1.2)) : CertLoopIn)) (by fun_prop)
  have hsignLast := isOraclePPTOn_signEdgeM S (enc := encPair encHL encPlantedCert)
    (keys := fun r => r.1.1.1.2) (target := fun r => r.1.1.1.1.2)
    (sigCap := fun r => sigCap r.1.1.1.1.1.1) (path := fun r => r.2.1.1)
    (idx := fun r => r.2.1.2.1) (u := fun r => (r.1.2.getLastD false).toNat)
    (msg := fun r => r.1.1.2.1.2) (edges := fun r => r.2.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold plantedTreeHandler
  exact IsOraclePPTOn.ite (by fun_prop)
    (IsOraclePPTOn.cond (by fun_prop) (ComputableInPolyTime.isOraclePPTOn (by fun_prop))
      (((by fun_prop : ComputableInPolyTime (fun p => depth p.1.1.1.1)
          encH encUnary).sampleList).isOraclePPTOn.bind_with
        (IsOraclePPTOn.cond (by fun_prop) (ComputableInPolyTime.isOraclePPTOn (by fun_prop))
          (hcert.bind_with
            (hsignLast.bind_with (ComputableInPolyTime.isOraclePPTOn (by fun_prop)))))))
    (ComputableInPolyTime.isOraclePPTOn (by fun_prop))

private def plantedStateGrowth (depth sigCap : ℕ → ℕ) (c : ForgerCaller)
    (w : List Bool) : ℕ :=
  let d := depth c.1.1.1
  4 * (d * (4 * (d + 1) + 2 * c.2.length + 3)) +
    2 * ((d + 1) * (8 * d + 2 * sigCap c.1.1.1 + 11)) +
    2 * (2 * w.length + 2) + 2 * (2 * d + 2)

private theorem plantedState_length_eq (state : PlantedState) :
    (encPlantedState state).length =
      4 * (encNodeCache state.1.1).length +
      2 * (encEdgeCache state.1.2).length +
      2 * (encList encBits state.2.queried).length +
      2 * (encList encBits state.2.seenLeaves).length + 6 := by
  rcases state with ⟨⟨v, e⟩, ⟨q, sl, b⟩⟩
  enc_len [encTreeLog_apply, List.length_singleton]

private theorem plantedTreeHandler_preserve (S : IndexedSignatureScheme) (depth sigCap : ℕ → ℕ)
    (c : ForgerCaller) (request : Unit × List Bool) (state : PlantedState)
    (hinv : (∀ e ∈ state.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ state.1.2, e.2.length ≤ sigCap c.1.1.1))
    (result : List Bool × PlantedState)
    (hresult : result ∈ OracleComp.support
      (plantedTreeHandler S depth c.2 c.1.2 (sigCap c.1.1.1) c.1.1.1 request state)) :
    ((∀ e ∈ result.2.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ result.2.1.2, e.2.length ≤ sigCap c.1.1.1)) ∧
    (encPlantedState result.2).length ≤
      (encPlantedState state).length + plantedStateGrowth depth sigCap c request.2 := by
  rcases state with ⟨⟨visited, edges⟩, ⟨queried, seenLeaves, bad⟩⟩
  obtain ⟨hvis, hedg⟩ := hinv
  have hqCons : (encList encBits (request.2 :: queried)).length ≤
      (encList encBits queried).length + (2 * request.2.length + 2) := by
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]; omega
  have hpure (b' : Bool) :
      ((∀ e ∈ visited, e.2 ≤ c.2.length) ∧ (∀ e ∈ edges, e.2.length ≤ sigCap c.1.1.1)) ∧
      (encPlantedState ((visited, edges), ⟨request.2 :: queried, seenLeaves, b'⟩)).length ≤
        (encPlantedState ((visited, edges), ⟨queried, seenLeaves, bad⟩)).length +
          plantedStateGrowth depth sigCap c request.2 := by
    refine ⟨⟨hvis, hedg⟩, ?_⟩
    rw [plantedState_length_eq, plantedState_length_eq]
    dsimp only [plantedStateGrowth]; omega
  unfold plantedTreeHandler at hresult
  dsimp only at hresult
  split_ifs at hresult with hmsg hbad
  · rw [OracleComp.eq_of_mem_supportWith_pure hresult]; exact hpure true
  · obtain ⟨leaf, hleaf, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
    have hleafLen := BitString.length_of_mem_support_uniformList <| by
      rwa [← BitString.eval_sampleList, ← ProbOracleComp.support_sample]
    split_ifs at hrest with hcoll
    · rw [OracleComp.eq_of_mem_supportWith_pure hrest]; exact hpure true
    · simp only [OracleComp.mem_supportWith_bind_iff] at hrest
      obtain ⟨⟨⟨node, idx, certs⟩, ⟨visited', edges'⟩⟩, hcert, ⟨σ, edges''⟩, hsig, hres⟩ := hrest
      rw [OracleComp.eq_of_mem_supportWith_pure hres]
      let loopIn : CertLoopIn :=
        ((c.2, (c.1.2, sigCap c.1.1.1), (c.1.1.1, leaf)), (visited, edges))
      have hloop := OracleComp.iterate_invariant (PlantedLoopInv c.2.length (sigCap c.1.1.1) loopIn)
        ⟨rfl, Nat.zero_le _, rfl, by simp, hvis, hedg, by simp [loopIn], by simp [loopIn]⟩
        (fun i st _ hi => plantedLoopInv_step S loopIn le_rfl le_rfl i st hi) _ hcert
      obtain ⟨-, hvB, heB⟩ := plantedLoopInv_enc_bounds (Nat.sub_le (depth c.1.1.1) 1) hloop
      have heLast := ProbOracleComp.memoize_call_size_le (encPair encBits encUnary) encBits
        (fun _ => signEdgeRaw S c.2 c.1.2 (sigCap c.1.1.1) idx
          (leaf.getLastD false).toNat request.2)
        (node, (leaf.getLastD false).toNat) edges' (sigCap c.1.1.1)
        (fun e he => by simpa only [encBits_apply] using hloop.edges_le e he)
        (fun val hval => by
          simpa only [encBits_apply] using
            length_le_of_mem_support_signEdgeRaw S c.2 c.1.2 (sigCap c.1.1.1) idx _ _ hval)
        hsig
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate,
        hloop.node_len] at heLast
      have hu : (leaf.getLastD false).toNat ≤ 1 := Bool.toNat_le _
      have hslCons : (encList encBits (leaf :: seenLeaves)).length ≤
          (encList encBits seenLeaves).length + (2 * depth c.1.1.1 + 2) := by
        simp only [encList_cons, List.length_append, length_frame, encBits_apply, hleafLen]; omega
      refine ⟨⟨hloop.visited_le, heLast.2.1⟩, ?_⟩
      rw [plantedState_length_eq, plantedState_length_eq]
      dsimp only [plantedStateGrowth, loopIn, CertLoopIn.visited, CertLoopIn.edges,
        CertLoopIn.parameter, encNodeCache, encEdgeCache] at hvB heB heLast ⊢
      have hsucc : (depth c.1.1.1 + 1) * (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) =
          depth c.1.1.1 * (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) +
            (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) := Nat.succ_mul _ _
      have hsub := Nat.sub_le (depth c.1.1.1) 1
      omega
  · rw [OracleComp.eq_of_mem_supportWith_pure hresult]; exact hpure bad

private theorem computableInPolyTime_extractForgery :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × NodeSlotCache) × (List Bool × List Bool) =>
        extractForgery q.1.1.1 q.1.1.2 q.1.2 q.2.1 q.2.2)
      (encPair (encPair (encPair encUnary encUnary) encNodeCache) (encPair encBits encBits))
      (encPair encUnary (encPair encBits encBits)) := by
  let encIn := encPair (encPair (encPair encUnary encUnary) encNodeCache) (encPair encBits encBits)
  let encMid := encPair encIn (encPair (encPair encBits (encPair encKeys encBits)) encUnary)
  have hmid : ComputableInPolyTime
      (fun q => (q, signatureDecoder.decode q.2.2,
        ((q.1.2.filter fun e => e.2 == q.1.1.2).headD ([], 0)).1.length)) encIn encMid := by
    fun_prop
  have hbit := (by fun_prop : ComputableInPolyTime Bool.toNat encBool encUnary).comp
    (.bitsGetDWithInput (encIn := encMid) (list := fun t => t.2.1.1) (index := fun t => t.2.2)
      (by fun_prop) (by fun_prop) false)
  have hentry := ComputableInPolyTime.listGetDWithInput (encIn := encMid)
    (list := fun t => t.2.1.2.1) (index := fun t => t.2.2) (by fun_prop) (by fun_prop) ([], [])
  have hstep : ComputableInPolyTime
      (fun t => if t.2.2 + 1 < t.1.1.1.1 then
        ((t.2.1.1.getD t.2.2 false).toNat, t.2.1.2.1.getD t.2.2 ([], []))
        else ((t.2.1.1.getD t.2.2 false).toNat, t.1.2.1, t.2.1.2.2))
      encMid (encPair encUnary (encPair encBits encBits)) :=
    .ite_decide (by fun_prop) (hbit.prod hentry) (hbit.prod (by fun_prop))
  exact (hstep.comp hmid).of_enc_eq fun _ => by simp only [Function.comp_apply, extractForgery]

/-- The planted-node reduction `indexedForger` is uniformly strict oracle PPT whenever `depth`,
`slotBound`, and `sigCap` are polynomial-time in unary and `adversary` is strict oracle PPT. -/
theorem isOraclePPT_indexedForger (S : IndexedSignatureScheme) {depth slotBound sigCap : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hslot : ComputableInPolyTime slotBound encUnary encUnary)
    (hsigCap : ComputableInPolyTime sigCap encUnary encUnary)
    {adversary : Forger} (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits))
      (indexedForger S depth slotBound sigCap adversary) := by
  let encCaller := encPair (encPair (encPair encUnary encBits) encUnary) encKeys
  have hgrowth : PolyBounded (fun p => (encPair encCaller encBits p).length)
      (fun p => plantedStateGrowth depth sigCap p.1 p.2) := by
    simpa only [encUnary_apply, List.length_replicate] using
      (by dsimp only [plantedStateGrowth]; fun_prop :
        ComputableInPolyTime (fun p : ForgerCaller × List Bool =>
          plantedStateGrowth depth sigCap p.1 p.2) (encPair encCaller encBits) encUnary
        ).polyBounded_length
  have hrun := hA.run_interpret_preprocess_open_of_bounded_growth (External := Unit)
    (operationEncoding := encFinEnum Unit)
    (handler := fun c : ForgerCaller =>
      plantedTreeHandler S depth c.2 c.1.2 (sigCap c.1.1.1) c.1.1.1)
    (prepare := fun c : ForgerCaller =>
      (c.1.1.1, encPair encUnary encBits (c.1.1.1, (c.2.getD 0 ([], [])).1)))
    (initial := fun _ => initPlantedState)
    (growth := plantedStateGrowth depth sigCap)
    (by fun_prop) (isOraclePPTOn_plantedTreeHandler S hdepth hsigCap)
    (.const initPlantedState)
    (fun c state => (∀ e ∈ state.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ state.1.2, e.2.length ≤ sigCap c.1.1.1))
    (fun _ => by
      simp only [initPlantedState, List.mem_singleton, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      rintro _ rfl; exact Nat.zero_le _)
    hgrowth (plantedTreeHandler_preserve S depth sigCap)
  have hextract := computableInPolyTime_extractForgery.comp
    (by fun_prop : ComputableInPolyTime
      (fun pair : ForgerCaller × ((List Bool × List Bool) × PlantedState) =>
        (((depth pair.1.1.1.1, pair.1.1.2), pair.2.2.1.1), (pair.2.1.1, pair.2.1.2)))
      (encPair encCaller (encPair (encPair encBits encBits) encPlantedState))
      (encPair (encPair (encPair encUnary encUnary) encNodeCache) (encPair encBits encBits)))
  refine IsOraclePPTOn.isOraclePPT ?_
  unfold indexedForger indexedForgerAt
  exact ((isPPTOn_sampleDyadicIndex (by fun_prop)).isOraclePPTOn).bind_with
    ((isPPTOn_plantNodeKeys S hslot).isOraclePPTOn.bind_with
      (hrun.bind_with hextract.isOraclePPTOn))

end TreeSignature

end Cslib.Crypto
