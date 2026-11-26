/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncForge
public import CslibFrontier.Crypto.Computational.Encryption.HalfBlockPRP
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Computational.LubyRackoff
import CslibFrontier.Crypto.Computational.PseudorandomPermutation.StrongSwitching
import CslibFrontier.Crypto.Game.Concrete
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# CCA Security of Half-Block Encryption from a Strong PRP

The half-block scheme `BlockCipher.halfBlockCipher` encrypts an `n`-bit message `m` under a block
cipher `F` on `2 n`-bit blocks as `F_k(r ‖ m)` for a fresh `n`-bit nonce `r`. This module proves
[BonehShoup2023], Exercise 9.12(a) for it: if `F` is a strong pseudorandom permutation, the scheme
is CCA-secure. The scheme has no ciphertext integrity
(`BlockCipher.not_ciphertextIntegrity_halfBlockCipher`) and, as shown here, no plaintext integrity,
so it is the example behind the remark after Theorem 9.1 of [BonehShoup2023] that a CCA-secure
cipher need not provide either. [Katz and Lindell, Exercise 5.8][KatzLindell2020] asks for the
same security proof.

The reduction has one adversary for each challenge bit. `ccaToStrongPRPAdversary bit A` runs the
CCA adversary `A`, turning a valid encryption request into a forward query on `r ‖ m_bit`, an
unlogged `2 n`-bit decryption request into an inverse query, and logged or wrong-length requests
into local replies. Against the block cipher its output has the law of CCA experiment `bit`.
Against a uniform permutation the two adversaries are close: the permutation is replaced by the
forgetful sampler `RandomPermutation.forgetfulAnswer` (`advantage_strongPRPIdealGame_forgetful_le`),
against which the challenge bit affects the run only when a fresh encryption nonce matches the
`n`-bit prefix of an earlier recorded block (from an encryption or inverse query).

## Main definitions

* `Cslib.Crypto.ccaToStrongPRPAdversary`: the reduction from a CCA adversary and a challenge bit to
  a strong-PRP distinguisher.

## Main results

* `Cslib.Crypto.eval_strongPRPRealGame_ccaToStrongPRPAdversary`: the real strong-PRP game of the
  reduction is the CCA experiment of its challenge bit.
* `Cslib.Crypto.isQueryBounded_ccaToStrongPRPAdversary`,
  `Cslib.Crypto.isOraclePPT_ccaToStrongPRPAdversary`: the reduction makes at most as many oracle
  calls as the adversary and is oracle PPT whenever the adversary is.
* `Cslib.Crypto.advantage_strongPRPIdealGame_ccaToStrongPRPAdversary_le`: against a uniform
  permutation, the two reductions of an adversary with at most `Q` oracle calls differ by at most
  `Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / 4 ^ n`.
* `Cslib.Crypto.BlockCipher.advantage_ccaGame_halfBlockCipher_le`: the concrete bound on the CCA
  advantage.
* `Cslib.Crypto.BlockCipher.StrongPRP.indcca_halfBlockCipher`: Exercise 9.12(a), the scheme is
  CCA-secure for a strong pseudorandom permutation.
* `Cslib.Crypto.BlockCipher.eval_encForgeGame_halfBlockCipher_allOnesForger`,
  `Cslib.Crypto.BlockCipher.not_encForge_halfBlockCipher`: the all-ones forger wins with
  probability `1`, so the scheme has no plaintext integrity, whatever the block cipher.
* `Cslib.Crypto.PseudorandomFunction.exists_indcca_not_integrity`: from any pseudorandom function,
  a CCA-secure cipher with neither ciphertext nor plaintext integrity exists.

## Implementation notes

* The book writes the block `(m, r)`; here it is `r ‖ m`. Messages and nonces are the `n`-bit
  strings and blocks have `2 n` bits; other nonce lengths are not covered.
* The book leaves the definition of a strongly secure block cipher to the reader (§4.1.3,
  Exercise 4.9); here it is `BlockCipher.StrongPRP`.
* Attack Game 9.2 forbids a decryption query on a returned ciphertext; here it is answered `[]`,
  as in `SymmetricCipher.ccaGame`.
* The book does not print a bound; the one here is derived and is not claimed tight. Its `Q` counts
  every oracle call of the adversary.
* "(or plaintext) integrity" is read as `SymmetricCipher.EncForge`.
* The proof uses the inverse queries of a strong PRP: every unlogged decryption request of length
  `2 n` becomes one, while logged challenge ciphertexts are answered `[]` and other lengths are
  answered `encOption encBits none` locally without querying the oracle.
* Parts (b) and (c) of Exercise 9.12 are not formalized.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 9.13, Exercise 9.12(a) (p. 394) and Section 9.2.3, remark after Theorem 9.1 (p. 363).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Exercise 5.8
  (p. 165)][KatzLindell2020]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM RandomPermutation

/-! ### The reduction -/

/-- The reduction's answer to one CCA request, with the log of returned ciphertexts as state. It
follows `SymmetricCipher.ccaOracle` case by case. A decryption request for a logged ciphertext is
answered `[]`, and one whose length is not `2 * n` with the code of `none`, both without a query;
any other goes to the inverse channel, and the reply without its first `n` bits is returned. An
encryption request whose two messages have `n` bits each is answered by a forward query on a fresh
`n`-bit nonce followed by the message of the challenge bit `bit`, and the reply is logged; any
other is answered `[]`.

Each reply of the oracle is cut to `2 * n` bits. Both oracles of the strong-PRP game answer a
`2 * n`-bit request with `2 * n` bits, so the cut changes nothing against them; it bounds the reply
of every oracle, which `isOraclePPT_ccaToStrongPRPAdversary` needs. -/
private noncomputable def ccaToStrongPRPHandler (n : ℕ) (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool)) (WordOracleComp Bool) (List Bool) :=
  fun queried =>
    if request.1 then
      if queried.contains request.2 then
        pure ([], queried)
      else if request.2.length == 2 * n then
        (fun block => (encOption encBits (some (block.drop n)), queried)) <$>
          (List.take (2 * n) <$> ProbOracleComp.query (true, request.2))
      else
        pure (encOption encBits none, queried)
    else
      if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then do
        let r ← ProbOracleComp.sample (BitString.sampleList n)
        (fun ct => (ct, ct :: queried)) <$> (List.take (2 * n) <$> ProbOracleComp.query
          (false, r ++ (if bit then dropFrame request.2 else unframe request.2)))
      else
        pure ([], queried)

/-- The strong-PRP distinguisher built from a CCA adversary and a challenge bit: it runs the
adversary on the empty advice word, as `SymmetricCipher.ccaGame` does, logging returned challenge
ciphertexts; encryption requests on pairs of `n`-bit messages query the forward channel `(false, ·)`
on `r ++ m_bit` for a fresh `n`-bit nonce `r` (logging the `2 * n`-bit reply), unlogged `2 * n`-bit
decryption requests query the inverse channel `(true, ·)` and drop the `n`-bit nonce prefix, and
replayed or malformed requests are answered locally without an oracle call. -/
noncomputable def ccaToStrongPRPAdversary (bit : Bool) (adversary : CCAAdversary) :
    StrongPRPDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToStrongPRPHandler n bit))
      (adversary n [])).run []
    return out.1

/-- Interpreting a program against a stateless oracle is its stateful run with the unit
state. -/
private theorem interpret_eq_map_fst_runWith {Query α : Type} {spec : Query → Type}
    (h : (q : Query) → PMF (spec q)) (program : ProbOracleComp spec α) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle h) program =
      (ProbOracleComp.runWith (fun q => StateT.lift (h q)) program ()).map Prod.fst := by
  simp only [ProbOracleComp.runWith_lift, PMF.map_comp, Function.comp_def,
    Probability.PMF.map_id', OracleComp.evalWith_eq_interpret]

/-- **The real game of the reduction is the CCA experiment**: against the block cipher `F`, the
output of `ccaToStrongPRPAdversary bit adversary` has the law of experiment `bit` of the CCA game
of the half-block scheme. -/
theorem eval_strongPRPRealGame_ccaToStrongPRPAdversary (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) (adversary : CCAAdversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (F.strongPRPRealGame (ccaToStrongPRPAdversary bit adversary) n) =
      ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary bit n) := by
  simp only [BlockCipher.strongPRPRealGame, SymmetricCipher.ccaGame, ccaToStrongPRPAdversary,
    ProbOracleComp.eval_run, runWith_norm, pmf_norm]
  change ((BitString.sampleList (F.keyLen n)).eval.bind _) =
    ((BitString.sampleList (F.keyLen n)).eval.bind _)
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hkLen : k.length = F.keyLen n :=
    BitString.length_of_mem_support_uniformList (by simpa [BitString.eval_sampleList] using hk)
  rw [interpret_eq_map_fst_runWith, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_run_interpret]
  have hsim := ProbOracleComp.runWith_map_state
    (fun q (state : List (List Bool) × Unit) =>
      PMF.map (fun x => match x with | ((a, b), c) => (a, b, c))
        (ProbOracleComp.runWith (fun q => StateT.lift (PMF.pure (F.strongPRPOracle n k q)))
          ((ccaToStrongPRPHandler n bit q).run state.1) state.2))
    (fun q state => ProbComp.eval ((F.halfBlockCipher hblock).ccaOracle n k bit q state))
    Prod.fst
    (fun request state => by
      obtain ⟨queried, u⟩ := state
      change PMF.map (fun x : List Bool × List (List Bool) × Unit => (x.1, x.2.1))
          (PMF.map (fun x : (List Bool × List (List Bool)) × Unit => (x.1.1, x.1.2, x.2))
            (ProbOracleComp.runWith (fun q => StateT.lift (PMF.pure (F.strongPRPOracle n k q)))
              (ccaToStrongPRPHandler n bit request queried) u)) =
        ProbComp.eval ((F.halfBlockCipher hblock).ccaOracle n k bit request queried)
      rw [PMF.map_comp]
      have hliftpure (x : List Bool) :
          (StateT.lift (PMF.pure x) u : PMF (List Bool × Unit)) = PMF.pure (x, u) := by
        simp [StateT.lift]
      cases hreq : request.1
      · simp only [SymmetricCipher.ccaOracle, ccaToStrongPRPHandler, hreq, Bool.false_eq_true,
          ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
          have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
            cases bit <;> simp [hlenEq]
          rw [ProbOracleComp.runWith_sample_bind]
          simp only [BlockCipher.halfBlockCipher, ProbComp.eval_bind, ProbComp.eval_pure,
            BitString.eval_sampleList, PMF.map_bind, PMF.bind_bind, PMF.pure_bind]
          refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
          have hrLen := BitString.length_of_mem_support_uniformList hr
          have hlen : (r ++ if bit then dropFrame request.2 else unframe request.2).length =
              F.blockLen n := by
            rw [List.length_append, hrLen, hmbLen, hblock, Nat.two_mul]
          have hct := F.length_encrypt n k _ hkLen hlen
          have htake : List.take (2 * n) (F.encrypt n k
              (r ++ if bit then dropFrame request.2 else unframe request.2)) =
              F.encrypt n k (r ++ if bit then dropFrame request.2 else unframe request.2) :=
            List.take_of_length_le (by rw [hct, hblock])
          simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hliftpure,
            BlockCipher.strongPRPOracle, hlen, ↓reduceIte, Bool.false_eq_true, PMF.pure_map,
            Prod.map_apply, id_eq, htake, Function.comp_def]
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            ProbOracleComp.runWith_pure, PMF.pure_map, Function.comp_def]
      · simp only [SymmetricCipher.ccaOracle, ccaToStrongPRPHandler, hreq, ↓reduceIte]
        by_cases hmem : queried.contains request.2 = true
        · simp only [hmem, ↓reduceIte, ProbComp.eval_pure, ProbOracleComp.runWith_pure,
            PMF.pure_map, Function.comp_def]
        · simp only [hmem, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]
          by_cases hlen : request.2.length = 2 * n
          · have htake : List.take (2 * n) (F.decrypt n k request.2) = F.decrypt n k request.2 :=
              List.take_of_length_le
                (by rw [F.length_decrypt n k _ hkLen (by rw [hlen, hblock]), hblock])
            simp only [hlen, beq_self_eq_true, ↓reduceIte, ProbOracleComp.runWith_map,
              ProbOracleComp.runWith_query, hliftpure, BlockCipher.strongPRPOracle, hblock,
              PMF.pure_map, Prod.map_apply, id_eq, htake, Function.comp_def,
              BlockCipher.halfBlockCipher]
          · simp [hlen, hblock, BlockCipher.halfBlockCipher])
    (adversary n []) ([], ())
  rw [← hsim]
  simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, ProbOracleComp.runWith_pure,
    PMF.pure_map]

/-- The reduction's handler makes at most one oracle call. -/
private theorem isQueryBounded_ccaToStrongPRPHandler (n : ℕ) (bit : Bool)
    (request : Bool × List Bool) (s : List (List Bool)) :
    (ccaToStrongPRPHandler n bit request s).IsQueryBounded 1 := by
  unfold ccaToStrongPRPHandler
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : ((unframe request.2).length == n &&
        (dropFrame request.2).length == n) = true
    · simp only [hlenEq, ↓reduceIte]
      simpa only [Nat.zero_add] using
        (ProbOracleComp.IsQueryBounded.sample (BitString.sampleList n)).bind fun r => by
          simp only [OracleComp.isCostBounded_map_iff]
          exact ProbOracleComp.IsQueryBounded.query _
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte]
      exact OracleComp.IsCostBounded.pure _ 1
  · simp only [↓reduceIte]
    split_ifs
    · exact OracleComp.IsCostBounded.pure _ 1
    · simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.query _
    · exact OracleComp.IsCostBounded.pure _ 1

/-- The reduction makes at most as many oracle calls as the adversary. -/
theorem isQueryBounded_ccaToStrongPRPAdversary (bit : Bool) (adversary : CCAAdversary) (n : ℕ)
    (aux : List Bool) {Q : ℕ} (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToStrongPRPAdversary bit adversary n aux).IsQueryBounded Q := by
  unfold ccaToStrongPRPAdversary
  simp only [bind_pure_comp, ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
  refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_) hq []
  cases q with
  | inl m =>
    simp only [OracleComp.sumHandler, Sum.elim_inl]
    change ((·, s) <$> ProbOracleComp.sample (ProbComp.unifFin m)).IsQueryBounded 0
    simp only [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)
  | inr request =>
    simp only [OracleComp.sumHandler, Sum.elim_inr]
    exact isQueryBounded_ccaToStrongPRPHandler n bit request s

/-- The reduction is uniform strict oracle PPT whenever the adversary is. -/
theorem isOraclePPT_ccaToStrongPRPAdversary {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (ccaToStrongPRPAdversary bit adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) (encList encBits))
  have hhandler : IsOraclePPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        ccaToStrongPRPHandler pair.1.1 bit pair.2.1 pair.2.2) := by
    ppt [ccaToStrongPRPHandler]
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToStrongPRPHandler caller.1 bit))
          (adversary caller.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ([] : List (List Bool)))
      (resources := fun caller _ => 8 * caller.1 + 8)
      (by fun_prop) hhandler (ComputableInPolyTime.const [])
      (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    intro caller request queried _ result hresult
    unfold ccaToStrongPRPHandler at hresult
    cases hreq : request.1
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
      by_cases hlenEq : ((unframe request.2).length == caller.1 &&
          (dropFrame request.2).length == caller.1) = true
      · simp only [hlenEq, ↓reduceIte] at hresult
        obtain ⟨r, hr, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
        obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
        have htake : (List.take (2 * caller.1) raw).length ≤ 2 * caller.1 :=
          List.length_take_le _ _
        refine ⟨trivial, by lia, ?_⟩
        simp only [encList_cons, List.length_append, length_frame, encBits_apply]
        lia
      · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte] at hresult
        cases OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨trivial, by simp, by lia⟩
    · simp only [hreq, ↓reduceIte] at hresult
      split_ifs at hresult with hmem hlen
      · cases OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨trivial, by simp, by lia⟩
      · obtain ⟨block, hblock, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hblock
        have htake : (List.take (2 * caller.1) raw).length ≤ 2 * caller.1 :=
          List.length_take_le _ _
        refine ⟨trivial, ?_, by lia⟩
        simp only [encOption_some, encBits_apply, List.length_cons, List.length_drop]
        lia
      · cases OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨trivial, by simp, by lia⟩
  unfold ccaToStrongPRPAdversary
  simpa only [bind_pure_comp] using (hrun.map (ComputableInPolyTime.fst _ _)).isOraclePPT

/-! ### The coupled ideal run -/

/-- A record of the coupled ideal run: the block a call stands for when the challenge bit is
`false`, the block when it is `true`, and their common image. -/
private abbrev CoupledRecord (n : ℕ) : Type :=
  BitString (2 * n) × BitString (2 * n) × BitString (2 * n)

/-- The state of the coupled ideal run: the returned ciphertexts and the records. -/
private abbrev CoupledState (n : ℕ) : Type := List (List Bool) × List (CoupledRecord n)

/-- The lazy permutation table of the run with challenge bit `bit`. -/
private def coupledCache (n : ℕ) (bit : Bool) (records : List (CoupledRecord n)) :
    Cache (BitString (2 * n)) :=
  records.map fun t => (if bit then t.2.1 else t.1, t.2.2)

/-- One call of the coupled ideal run from fresh randomness `r` (a nonce) and `z` (a block):
the reply, the next state, and whether the nonce repeats the nonce part of a recorded block. -/
private def coupledStep (n : ℕ) (bit : Bool) (request : Bool × List Bool) (s : CoupledState n)
    (r : List Bool) (z : BitString (2 * n)) : List Bool × CoupledState n × Bool :=
  if request.1 then
    if s.1.contains request.2 then ([], s, false)
    else if request.2.length == 2 * n then
      match invLookup (coupledCache n false s.2) (BitString.ofList (2 * n) request.2) with
      | some x => (encOption encBits (some ((List.ofFn x).drop n)), s, false)
      | none => (encOption encBits (some ((List.ofFn z).drop n)),
          (s.1, (z, z, BitString.ofList (2 * n) request.2) :: s.2), false)
    else (encOption encBits none, s, false)
  else
    if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
      if r ∈ s.2.map (fun t => (List.ofFn t.1).take n) then
        match (coupledCache n bit s.2).lookup (BitString.ofList (2 * n)
            (r ++ (if bit then dropFrame request.2 else unframe request.2))) with
        | some y => (List.ofFn y, (List.ofFn y :: s.1, s.2), true)
        | none => (List.ofFn z, (List.ofFn z :: s.1,
            (BitString.ofList (2 * n) (r ++ unframe request.2),
              BitString.ofList (2 * n) (r ++ dropFrame request.2), z) :: s.2), true)
      else (List.ofFn z, (List.ofFn z :: s.1,
        (BitString.ofList (2 * n) (r ++ unframe request.2),
          BitString.ofList (2 * n) (r ++ dropFrame request.2), z) :: s.2), false)
    else ([], s, false)

/-- The coupled ideal handler: `coupledStep` on fresh uniform randomness, with a sticky flag. -/
private noncomputable def coupledHandler (n : ℕ) (bit : Bool) (request : Bool × List Bool) :
    StateT (CoupledState n × Bool) PMF (List Bool) :=
  fun s => (BitString.uniformList n).bind fun r =>
    (PMF.uniformOfFintype (BitString (2 * n))).map fun z =>
      ((coupledStep n bit request s.1 r z).1,
        ((coupledStep n bit request s.1 r z).2.1, s.2 || (coupledStep n bit request s.1 r z).2.2))

/-- The flag of one coupled step is raised exactly by an encryption call whose fresh nonce repeats
the nonce part of a recorded block; it does not depend on the challenge bit. -/
private theorem coupledStep_flag (n : ℕ) (bit : Bool) (request : Bool × List Bool)
    (s : CoupledState n) (r : List Bool) (z : BitString (2 * n)) :
    (coupledStep n bit request s r z).2.2 =
      (!request.1 && (((unframe request.2).length == n) && ((dropFrame request.2).length == n)) &&
        decide (r ∈ s.2.map (fun t => (List.ofFn t.1).take n))) := by
  grind [coupledStep]

/-- One coupled step adds at most one record. -/
private theorem coupledStep_length_le (n : ℕ) (bit : Bool) (request : Bool × List Bool)
    (s : CoupledState n) (r : List Bool) (z : BitString (2 * n)) :
    (coupledStep n bit request s r z).2.1.2.length ≤ s.2.length + 1 := by
  grind [coupledStep]

/-- Unflagged coupled steps do not depend on the challenge bit. -/
private theorem coupledStep_eq_of_flag_eq_false (n : ℕ) (request : Bool × List Bool)
    (s : CoupledState n) (r : List Bool) (z : BitString (2 * n)) (bit : Bool)
    (h : (coupledStep n bit request s r z).2.2 = false) :
    coupledStep n false request s r z = coupledStep n true request s r z := by
  rw [coupledStep_flag] at h
  unfold coupledStep
  by_cases h1 : request.1 = true
  · simp only [h1, ↓reduceIte]
  · by_cases h2 : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
    · have h3 : r ∉ s.2.map (fun t => (List.ofFn t.1).take n) := by simpa [h1, h2] using h
      simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- A raised flag means the fresh nonce repeats the nonce part of a recorded block. -/
private theorem coupledStep_flag_imp (n : ℕ) (bit : Bool) (request : Bool × List Bool)
    (s : CoupledState n) (r : List Bool) (z : BitString (2 * n))
    (h : (coupledStep n bit request s r z).2.2 = true) :
    r ∈ s.2.map (fun t => (List.ofFn t.1).take n) := by
  rw [coupledStep_flag] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The coupled handler keeps a raised flag raised. -/
private theorem isFlagMonotone_coupledHandler (n : ℕ) (bit : Bool) :
    OracleComp.IsFlagMonotone (coupledHandler n bit) := by
  intro request s x hx
  obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
  obtain ⟨z, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  rfl

/-- From an unflagged state, the two coupled handlers give every unflagged outcome the same
probability. -/
private theorem coupledHandler_apply_false (n : ℕ) (request : Bool × List Bool) (s : CoupledState n)
    (a : List Bool) (s' : CoupledState n) :
    coupledHandler n false request (s, false) (a, (s', false)) =
      coupledHandler n true request (s, false) (a, (s', false)) := by
  simp only [coupledHandler, PMF.bind_apply, PMF.map_apply, Bool.false_or]
  refine tsum_congr fun r => congrArg _ (tsum_congr fun z => ?_)
  by_cases hflag : (coupledStep n false request s r z).2.2 = false
  · rw [coupledStep_eq_of_flag_eq_false n request s r z false hflag]
  · have hfalse : (coupledStep n false request s r z).2.2 = true := by simpa using hflag
    have htrue : (coupledStep n true request s r z).2.2 = true := by
      simpa only [coupledStep_flag] using hfalse
    simp [Prod.ext_iff, hfalse, htrue]

/-- The coupled handlers agree until the flag is raised. -/
private theorem identicalUntilBad_coupledHandler (n : ℕ) :
    ProbOracleComp.IdenticalUntilBad (coupledHandler n false) (coupledHandler n true)
      OracleComp.FlagBad :=
  ProbOracleComp.IdenticalUntilBad.of_flag (isFlagMonotone_coupledHandler n false)
    (isFlagMonotone_coupledHandler n true) (coupledHandler_apply_false n)

/-- One call from an unflagged state raises the flag with probability at most the number of
records over `2 ^ n`. -/
private theorem toOuterMeasure_coupledHandler_flag_le (n : ℕ) (bit : Bool)
    (request : Bool × List Bool) (s : CoupledState n) :
    (coupledHandler n bit request (s, false)).toOuterMeasure {x | OracleComp.FlagBad x.2} ≤
      (s.2.length : ENNReal) * ((1 : ENNReal) / 2 ^ n) := by
  unfold coupledHandler
  refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
    {r | r ∈ s.2.map (fun t => (List.ofFn t.1).take n)} _ 0 fun r _ hr => ?_).trans ?_
  · rw [nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff]
    refine Set.disjoint_left.mpr fun x hx hbad => hr ?_
    obtain ⟨z, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact coupledStep_flag_imp n bit request s r z hbad
  · rw [add_zero]
    have hset : {r | r ∈ s.2.map (fun t => (List.ofFn t.1).take n)} =
        ↑(s.2.map (fun t => (List.ofFn t.1).take n)).toFinset := by
      ext r
      simp
    rw [hset]
    refine (BitString.toOuterMeasure_uniformList_finset_le n _).trans ?_
    gcongr
    exact_mod_cast (List.toFinset_card_le _).trans (by simp)

/-- One call of the coupled handler adds at most one record. -/
private theorem length_le_of_mem_support_coupledHandler (n : ℕ) (bit : Bool)
    (request : Bool × List Bool) (s : CoupledState n × Bool)
    {x : List Bool × CoupledState n × Bool} (hx : x ∈ (coupledHandler n bit request s).support) :
    x.2.1.2.length ≤ s.1.2.length + 1 := by
  obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
  obtain ⟨z, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact coupledStep_length_le n bit request s.1 r z

/-- A program making at most `Q` calls raises the flag of the coupled run with probability at
most `Q.choose 2 / 2 ^ n`. -/
private theorem toOuterMeasure_runWith_coupledHandler_flag_le (n : ℕ) (bit : Bool) {α : Type}
    {program : ProbOracleComp (fun _ : Bool × List Bool => List Bool) α} {Q : ℕ}
    (hQ : program.IsQueryBounded Q) :
    (ProbOracleComp.runWith (coupledHandler n bit) program (([], []), false)).toOuterMeasure
        {x | OracleComp.FlagBad x.2} ≤ (Q.choose 2 : ENNReal) * ((1 : ENNReal) / 2 ^ n) := by
  simpa using ProbOracleComp.toOuterMeasure_bad_choose_two_le (handler := coupledHandler n bit)
    (bad := OracleComp.FlagBad) (fun s => s.1.2.length) ((1 : ENNReal) / 2 ^ n)
    (fun q ⟨st, flag⟩ hs => by
      obtain rfl : flag = false := by simpa [OracleComp.FlagBad] using hs
      exact toOuterMeasure_coupledHandler_flag_le n bit q st)
    (fun q s _ x hx _ => length_le_of_mem_support_coupledHandler n bit q s hx)
    hQ (s := (([], []), false)) (by simp [OracleComp.FlagBad])

/-! ### The coupled run presents the two forgetful runs -/

/-- The invariant of the coupled run: a record whose two blocks differ has its image among the
returned ciphertexts, and the two blocks of a record have the same nonce part. -/
private def CoupledInv (n : ℕ) (s : CoupledState n) : Prop :=
  ∀ t ∈ s.2, (t.1 ≠ t.2.1 → List.ofFn t.2.2 ∈ s.1) ∧
    (List.ofFn t.2.1).take n = (List.ofFn t.1).take n

private theorem take_ofFn_ofList_append {n : ℕ} {r m : List Bool} (hr : r.length = n)
    (hm : m.length = n) : (List.ofFn (BitString.ofList (2 * n) (r ++ m))).take n = r := by
  rw [BitString.ofFn_ofList (by rw [List.length_append, hr, hm, Nat.two_mul])]
  exact List.take_left' hr

/-- Every coupled step from a nonce of `n` bits keeps the invariant. -/
private theorem coupledInv_coupledStep {n : ℕ} (bit : Bool) (request : Bool × List Bool)
    {s : CoupledState n} {r : List Bool} (z : BitString (2 * n)) (hr : r.length = n)
    (hs : CoupledInv n s) : CoupledInv n (coupledStep n bit request s r z).2.1 := by
  by_cases h1 : request.1 = true
  · simp only [coupledStep, h1, ↓reduceIte]
    by_cases h2 : s.1.contains request.2 = true
    · simpa only [h2, ↓reduceIte] using hs
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (request.2.length == 2 * n) = true
      · simp only [h3, ↓reduceIte]
        split
        · exact hs
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨fun h => (h rfl).elim, rfl⟩
          · exact hs t ht
      · simpa only [h3, Bool.false_eq_true, ↓reduceIte] using hs
  · simp only [coupledStep, h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
    · simp only [h2, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      have hnew : CoupledInv n (List.ofFn z :: s.1,
          (BitString.ofList (2 * n) (r ++ unframe request.2),
            BitString.ofList (2 * n) (r ++ dropFrame request.2), z) :: s.2) := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨fun _ => List.mem_cons_self, by
            rw [take_ofFn_ofList_append hr h2.2, take_ofFn_ofList_append hr h2.1]⟩
        · exact ⟨fun h => List.mem_cons_of_mem _ ((hs t ht).1 h), (hs t ht).2⟩
      by_cases h3 : r ∈ s.2.map (fun t => (List.ofFn t.1).take n)
      · simp only [h3, ↓reduceIte]
        split
        · intro t ht
          exact ⟨fun h => List.mem_cons_of_mem _ ((hs t ht).1 h), (hs t ht).2⟩
        · exact hnew
      · simpa only [h3, ↓reduceIte] using hnew
    · simpa only [h2, Bool.false_eq_true, ↓reduceIte] using hs

/-- The coupled handler keeps the invariant. -/
private theorem coupledInv_of_mem_support_coupledHandler {n : ℕ} (bit : Bool)
    (request : Bool × List Bool) {s : CoupledState n × Bool} (hs : CoupledInv n s.1)
    {x : List Bool × CoupledState n × Bool} (hx : x ∈ (coupledHandler n bit request s).support) :
    CoupledInv n x.2.1 := by
  obtain ⟨r, hr, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
  obtain ⟨z, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact coupledInv_coupledStep bit request z (BitString.length_of_mem_support_uniformList hr) hs

/-- On an image that is not a returned ciphertext, the two tables have the same preimage. -/
private theorem invLookup_coupledCache_eq {n : ℕ} (bit : Bool) {log : List (List Bool)}
    {records : List (CoupledRecord n)} (hs : CoupledInv n (log, records))
    {y : BitString (2 * n)} (hy : List.ofFn y ∉ log) :
    invLookup (coupledCache n bit records) y = invLookup (coupledCache n false records) y := by
  induction records with
  | nil => rfl
  | cons t rest ih =>
    have hrest : CoupledInv n (log, rest) := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    simp only [coupledCache, List.map_cons, invLookup_cons, Bool.false_eq_true, ↓reduceIte]
    by_cases hyt : y = t.2.2
    · subst hyt
      have ht : t.1 = t.2.1 :=
        Classical.byContradiction fun hne => hy ((hs t List.mem_cons_self).1 hne)
      simp [ht]
    · have hbeq : (y == t.2.2) = false := by simpa using hyt
      simp only [hbeq]
      exact ih hrest

/-- A block whose nonce part is not that of a recorded block is not in the table. -/
private theorem lookup_coupledCache_eq_none {n : ℕ} (bit : Bool) {records : List (CoupledRecord n)}
    {x : BitString (2 * n)}
    (h : ∀ t ∈ records,
      (List.ofFn (if bit then t.2.1 else t.1)).take n ≠ (List.ofFn x).take n) :
    (coupledCache n bit records).lookup x = none := by
  induction records with
  | nil => rfl
  | cons t rest ih =>
    have hne : x ≠ (if bit then t.2.1 else t.1) := fun heq =>
      h t List.mem_cons_self (by rw [heq])
    have hbeq : (x == (if bit then t.2.1 else t.1)) = false := by simpa using hne
    simp only [coupledCache, List.map_cons, List.lookup_cons, hbeq]
    exact ih fun u hu => h u (List.mem_cons_of_mem _ hu)

private theorem stateT_map_apply {σ α β : Type} (f : α → β) (x : StateT σ PMF α) (s : σ) :
    (f <$> x) s = (x s).map (Prod.map f id) := by
  change (x s).bind (fun p => PMF.pure (f p.1, p.2)) = _
  rfl

private theorem coupledCache_cons (n : ℕ) (bit : Bool) (t : CoupledRecord n)
    (records : List (CoupledRecord n)) :
    coupledCache n bit (t :: records) =
      (if bit then t.2.1 else t.1, t.2.2) :: coupledCache n bit records := rfl

/-- **The coupled run presents the forgetful run of either challenge bit**: forgetting the flag
and reading the records as the table of challenge bit `bit`, one call of the coupled handler is
one call of the reduction's handler against the forgetful sampler. -/
private theorem coupledHandler_map_coupledCache (n : ℕ) (bit : Bool) (request : Bool × List Bool)
    (s : CoupledState n × Bool) (hs : CoupledInv n s.1) :
    (coupledHandler n bit request s).map
        (fun x => (x.1, (x.2.1.1, coupledCache n bit x.2.1.2))) =
      (ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
        (ccaToStrongPRPHandler n bit request s.1.1) (coupledCache n bit s.1.2)).map
          (fun x => (x.1.1, x.1.2, x.2)) := by
  obtain ⟨⟨log, records⟩, flag⟩ := s
  have hL : (coupledHandler n bit request ((log, records), flag)).map
      (fun x => (x.1, (x.2.1.1, coupledCache n bit x.2.1.2))) =
      (BitString.uniformList n).bind fun r =>
        (PMF.uniformOfFintype (BitString (2 * n))).map fun z =>
          ((coupledStep n bit request (log, records) r z).1,
            ((coupledStep n bit request (log, records) r z).2.1.1,
              coupledCache n bit (coupledStep n bit request (log, records) r z).2.1.2)) := by
    simp only [coupledHandler, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have htake (x : BitString (2 * n)) : List.take (2 * n) (List.ofFn x) = List.ofFn x :=
    List.take_of_length_le (by simp)
  rw [hL]
  by_cases h1 : request.1 = true
  · by_cases h2 : log.contains request.2 = true
    · simp only [ccaToStrongPRPHandler, coupledStep, PMF.bind_const, h1, h2, ↓reduceIte,
        ProbOracleComp.runWith_pure, PMF.pure_map]
      exact PMF.map_const _ _
    · by_cases h3 : (request.2.length == 2 * n) = true
      · have hlen : request.2.length = 2 * n := by simpa using h3
        have hy : List.ofFn (BitString.ofList (2 * n) request.2) ∉ log := by
          rw [BitString.ofFn_ofList hlen]
          simpa using h2
        have hlookup := invLookup_coupledCache_eq bit hs hy
        have hW := strongBitStringCodec_wordOracle_of_length
          (forgetfulAnswer (α := BitString (2 * n))) true hlen
        cases hinv : invLookup (coupledCache n false records)
            (BitString.ofList (2 * n) request.2) with
        | some x =>
          rw [hinv] at hlookup
          simp only [ccaToStrongPRPHandler, coupledStep, PMF.bind_const, h1, h2, h3, hinv,
            Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_map,
            ProbOracleComp.runWith_query, hW, PermQuery.ofBoolProd, stateT_map_apply,
            forgetfulAnswer_inverse_of_some hlookup, PMF.pure_map, Prod.map_apply, id_eq, htake]
          exact PMF.map_const _ _
        | none =>
          rw [hinv] at hlookup
          simp only [ccaToStrongPRPHandler, coupledStep, PMF.bind_const, h1, h2, h3, hinv,
            Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_map,
            ProbOracleComp.runWith_query, hW, PermQuery.ofBoolProd, stateT_map_apply,
            forgetfulAnswer_inverse_of_none hlookup, PMF.map_comp, Function.comp_def,
            Prod.map_apply, id_eq, htake, coupledCache_cons, ite_self]
      · simp only [ccaToStrongPRPHandler, coupledStep, PMF.bind_const, h1, h2, h3,
          Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_map]
        exact PMF.map_const _ _
  · by_cases h2 : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
    · have hlen := h2
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      simp only [ccaToStrongPRPHandler, h1, h2, Bool.false_eq_true, ↓reduceIte]
      rw [ProbOracleComp.runWith_sample_bind]
      simp only [BitString.eval_sampleList, PMF.map_bind]
      refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
      have hrLen := BitString.length_of_mem_support_uniformList hr
      have hmbLen : (if bit = true then dropFrame request.2 else unframe request.2).length = n := by
        cases bit <;> simp [hlen]
      have hwordLen : (r ++ if bit = true then dropFrame request.2 else unframe request.2).length =
          2 * n := by
        rw [List.length_append, hrLen, hmbLen, Nat.two_mul]
      have hW := strongBitStringCodec_wordOracle_of_length
        (forgetfulAnswer (α := BitString (2 * n))) false hwordLen
      have hxb : (if bit = true then BitString.ofList (2 * n) (r ++ dropFrame request.2)
          else BitString.ofList (2 * n) (r ++ unframe request.2)) =
          BitString.ofList (2 * n)
            (r ++ if bit = true then dropFrame request.2 else unframe request.2) := by
        cases bit <;> rfl
      cases hlk : (coupledCache n bit records).lookup (BitString.ofList (2 * n)
          (r ++ if bit = true then dropFrame request.2 else unframe request.2)) with
      | some y =>
        have hmem : r ∈ records.map (fun t => (List.ofFn t.1).take n) := by
          by_contra hmem
          have hnone := lookup_coupledCache_eq_none bit (records := records)
            (x := BitString.ofList (2 * n)
              (r ++ if bit = true then dropFrame request.2 else unframe request.2))
            (fun t ht heq => hmem (List.mem_map.mpr ⟨t, ht, by
              rw [take_ofFn_ofList_append hrLen hmbLen] at heq
              cases bit
              · simpa using heq
              · rw [← (hs t ht).2]
                simpa using heq⟩))
          simp [hnone] at hlk
        simp only [coupledStep, h1, h2, hmem, hlk, Bool.false_eq_true, ↓reduceIte,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hW, PermQuery.ofBoolProd,
          stateT_map_apply, forgetfulAnswer_forward_of_some hlk, PMF.pure_map, Prod.map_apply,
          id_eq, htake]
        exact PMF.map_const _ _
      | none =>
        have hstep (z : BitString (2 * n)) :
            ((coupledStep n bit request (log, records) r z).1,
              ((coupledStep n bit request (log, records) r z).2.1.1,
                coupledCache n bit (coupledStep n bit request (log, records) r z).2.1.2)) =
              (List.ofFn z, (List.ofFn z :: log,
                (BitString.ofList (2 * n)
                  (r ++ if bit = true then dropFrame request.2 else unframe request.2), z) ::
                    coupledCache n bit records)) := by
          simp only [coupledStep, h1, h2, hlk, Bool.false_eq_true, ↓reduceIte]
          split <;> simp only [coupledCache_cons, hxb]
        simp only [hstep, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
          hW, PermQuery.ofBoolProd, stateT_map_apply, forgetfulAnswer_forward_of_none hlk,
          PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq, htake]
    · simp only [ccaToStrongPRPHandler, coupledStep, PMF.bind_const, h1, h2, Bool.false_eq_true,
        ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_map]
      exact PMF.map_const _ _

/-! ### The ideal bound -/

/-- The reduction's run against the forgetful sampler is the coupled run of its challenge bit. -/
private theorem runWith_forgetful_ccaToStrongPRPAdversary (adversary : CCAAdversary) (bit : Bool)
    (n : ℕ) :
    (ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
        (ccaToStrongPRPAdversary bit adversary n []) []).map Prod.fst =
      (ProbOracleComp.runWith (coupledHandler n bit) (adversary n [])
        (([], []), false)).map Prod.fst := by
  have hsim := ProbOracleComp.runWith_map_state_of_invariant
    (coupledHandler n bit)
    (fun q (state : List (List Bool) × Cache (BitString (2 * n))) =>
      (ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
        ((ccaToStrongPRPHandler n bit q).run state.1) state.2).map
          (fun x => (x.1.1, x.1.2, x.2)))
    (fun s : CoupledState n × Bool => (s.1.1, coupledCache n bit s.1.2))
    (fun s => CoupledInv n s.1)
    (fun q s hs a s' hmem => coupledInv_of_mem_support_coupledHandler bit q hs hmem)
    (fun q s hs => coupledHandler_map_coupledCache n bit q s hs)
    (adversary n []) (([], []), false) (by intro t ht; cases ht)
  unfold ccaToStrongPRPAdversary
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_run_interpret]
  change ((PMF.map _ (ProbOracleComp.runWith _ (adversary n []) ([], coupledCache n bit []))).bind
    _).map Prod.fst = _
  rw [← hsim]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    ProbOracleComp.runWith_pure]

/-- **Against the forgetful sampler the challenge bit is hidden up to a nonce collision**: the
two reductions of a `Q`-call adversary differ by at most `Q.choose 2 / 2 ^ n`. -/
private theorem advantage_forgetful_ccaToStrongPRPAdversary_le (adversary : CCAAdversary) (n Q : ℕ)
    (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      ((ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
        (ccaToStrongPRPAdversary false adversary n []) []).map Prod.fst)
      ((ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
        (ccaToStrongPRPAdversary true adversary n []) []).map Prod.fst) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
  rw [runWith_forgetful_ccaToStrongPRPAdversary, runWith_forgetful_ccaToStrongPRPAdversary,
    Game.coe_advantage]
  have habs := (identicalUntilBad_coupledHandler n).abs_sub_le (adversary n [])
    (([], []), false) (fun x => PMF.pure x.1) true
  have hne : (Q.choose 2 : ENNReal) * ((1 : ENNReal) / 2 ^ n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.div_ne_top ENNReal.one_ne_top (by positivity))
  have hreal := ENNReal.toReal_mono hne
    (toOuterMeasure_runWith_coupledHandler_flag_le n false hQ)
  simpa [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_mul] using
    habs.trans hreal

open scoped NNReal

/-- **Ideal world.** Against a uniform permutation of `2 * n`-bit blocks, the two reductions of
a `Q`-call adversary are within `Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / 4 ^ n` of each other. -/
theorem advantage_strongPRPIdealGame_ccaToStrongPRPAdversary_le (adversary : CCAAdversary)
    (n Q : ℕ) (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
        (ccaToStrongPRPAdversary false adversary) n))
      (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
        (ccaToStrongPRPAdversary true adversary) n)) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ + 2 * (Q.choose 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have h0 := advantage_strongPRPIdealGame_forgetful_le (fun n => 2 * n)
    (ccaToStrongPRPAdversary false adversary) n Q
    (isQueryBounded_ccaToStrongPRPAdversary false adversary n [] hQ)
  have h1 := advantage_strongPRPIdealGame_forgetful_le (fun n => 2 * n)
    (ccaToStrongPRPAdversary true adversary) n Q
    (isQueryBounded_ccaToStrongPRPAdversary true adversary n [] hQ)
  have hmid := advantage_forgetful_ccaToStrongPRPAdversary_le adversary n Q hQ
  have hpow : ((2 : ℝ) ^ (2 * n))⁻¹ = (((2 : ℝ) ^ n)⁻¹) ^ 2 := by rw [pow_mul', inv_pow]
  rw [hpow] at h0 h1
  rw [Game.advantage_comm] at h1
  have htri1 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
      (ccaToStrongPRPAdversary false adversary) n))
    ((ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
      (ccaToStrongPRPAdversary false adversary n []) []).map Prod.fst)
    (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
      (ccaToStrongPRPAdversary true adversary) n)))
  have htri2 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    ((ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
      (ccaToStrongPRPAdversary false adversary n []) []).map Prod.fst)
    ((ProbOracleComp.runWith ((strongBitStringCodec (2 * n)).wordOracle forgetfulAnswer)
      (ccaToStrongPRPAdversary true adversary n []) []).map Prod.fst)
    (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
      (ccaToStrongPRPAdversary true adversary) n)))
  rw [NNReal.coe_add] at htri1 htri2
  linarith

/-! ### Exercise 9.12(a) and the missing integrity -/

/-- **Concrete bound for Exercise 9.12(a).** The CCA advantage against the half-block scheme of an
adversary making at most `Q` oracle calls is at most the strong-PRP advantages of the two
reductions plus `Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / 4 ^ n`. Here `Q` counts every oracle call of
the adversary, encryption and decryption, refused or not. The first error term bounds the
probability that a fresh encryption nonce matches the `n`-bit prefix of a previously recorded
`2 * n`-bit block (from either an earlier encryption query or an earlier inverse query), and the
second is the cost of comparing the two ideal games with the forgetful sampler
(`advantage_strongPRPIdealGame_forgetful_le`). The book does not print a bound; the one here is
derived and is not claimed tight. -/
theorem BlockCipher.advantage_ccaGame_halfBlockCipher_le (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) (adversary : CCAAdversary) (n Q : ℕ)
    (hQ : (adversary n []).IsQueryBounded Q) :
    (Game.advantage
        (ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary false n))
        (ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary true n)) : ℝ) ≤
      Game.advantage
        (ProbComp.eval (F.strongPRPRealGame (ccaToStrongPRPAdversary false adversary) n))
        (ProbComp.eval (strongPRPIdealGame F.blockLen
          (ccaToStrongPRPAdversary false adversary) n)) +
      Game.advantage
        (ProbComp.eval (F.strongPRPRealGame (ccaToStrongPRPAdversary true adversary) n))
        (ProbComp.eval (strongPRPIdealGame F.blockLen
          (ccaToStrongPRPAdversary true adversary) n)) +
      ((Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ + 2 * (Q.choose 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ 2) := by
  have hbl : strongPRPIdealGame F.blockLen = strongPRPIdealGame (fun n => 2 * n) :=
    congrArg strongPRPIdealGame (funext hblock)
  have hideal := advantage_strongPRPIdealGame_ccaToStrongPRPAdversary_le adversary n Q hQ
  rw [hbl, eval_strongPRPRealGame_ccaToStrongPRPAdversary F hblock,
    eval_strongPRPRealGame_ccaToStrongPRPAdversary F hblock]
  have h₁ := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary false n))
    (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
      (ccaToStrongPRPAdversary false adversary) n))
    (ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary true n)))
  have h₂ := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
      (ccaToStrongPRPAdversary false adversary) n))
    (ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
      (ccaToStrongPRPAdversary true adversary) n))
    (ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary true n)))
  rw [NNReal.coe_add] at h₁ h₂
  rw [Game.advantage_comm (ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary true n))]
  linarith

/-- **Boneh–Shoup, Exercise 9.12(a)**, for the half-block scheme: if `F` is a strong pseudorandom
permutation on `2 * n`-bit blocks, then encrypting an `n`-bit message `m` as `F_k(r ‖ m)` for a
fresh `n`-bit nonce `r` is CCA-secure ([BonehShoup2023], Section 9.13, Exercise 9.12(a), p. 394).

The book writes the block `(m, r)`; here it is `r ‖ m`. Messages and nonces are the `n`-bit
strings, so the book's condition that `1/|R|` is negligible holds and is not a hypothesis. The book
leaves the definition of a strongly secure block cipher to the reader (§4.1.3, Exercise 4.9); here
it is `BlockCipher.StrongPRP`. Attack Game 9.2 forbids a decryption query on a returned
ciphertext; here it is answered `[]`. The reduction sends every unlogged `2 * n`-bit decryption
request to the inverse channel of the strong-PRP oracle, answering logged challenge ciphertexts
with `[]` and other lengths with `encOption encBits none` locally. -/
theorem BlockCipher.StrongPRP.indcca_halfBlockCipher {F : BlockCipher} (hF : F.StrongPRP)
    (hblock : ∀ n, F.blockLen n = 2 * n) : (F.halfBlockCipher hblock).INDCCA := by
  have hbl : F.blockLen = fun n => 2 * n := funext hblock
  have hreal (bit : Bool) : Game.Indistinguishable
      (fun (adversary : CCAAdversary) n =>
        ProbComp.eval ((F.halfBlockCipher hblock).ccaGame adversary bit n))
      (fun adversary n => ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
        (ccaToStrongPRPAdversary bit adversary) n))
      (IsOraclePPT encBool) := by
    intro adversary hadversary
    simpa only [← hbl, eval_strongPRPRealGame_ccaToStrongPRPAdversary F hblock] using
      hF (ccaToStrongPRPAdversary bit adversary)
        (isOraclePPT_ccaToStrongPRPAdversary hadversary bit)
  have hideal : Game.Indistinguishable
      (fun (adversary : CCAAdversary) n => ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
        (ccaToStrongPRPAdversary false adversary) n))
      (fun adversary n => ProbComp.eval (strongPRPIdealGame (fun n => 2 * n)
        (ccaToStrongPRPAdversary true adversary) n))
      (IsOraclePPT encBool) := by
    refine Game.Indistinguishable.of_birthday_queryBounded_real
      (base := fun n => ((2 : ℝ≥0) ^ n)⁻¹) 3 (by negligible) fun n Q adversary hQ => ?_
    have hbound := advantage_strongPRPIdealGame_ccaToStrongPRPAdversary_le adversary n Q hQ
    have hsmall : (((2 : ℝ) ^ n)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ := by
      have h₀ : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
      have h₁ : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      nlinarith
    have hchoose : (0 : ℝ) ≤ Q.choose 2 := Nat.cast_nonneg _
    refine hbound.trans ?_
    push_cast
    nlinarith
  exact (hreal false).trans (hideal.trans (hreal true).symm)

/-- The all-ones forger makes no queries and its output decrypts, so it wins `encForgeGame`
against the half-block scheme with probability `1`. -/
theorem BlockCipher.eval_encForgeGame_halfBlockCipher_allOnesForger (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) (n : ℕ) :
    ProbComp.eval ((F.halfBlockCipher hblock).encForgeGame F.allOnesForger n) = PMF.pure true := by
  have h : ProbComp.eval ((F.halfBlockCipher hblock).encForgeGame F.allOnesForger n) =
      (BitString.uniformList (F.keyLen n)).map (fun _ => true) := by
    simp [SymmetricCipher.encForgeGame, BlockCipher.allOnesForger, BlockCipher.halfBlockCipher]
  exact h.trans (PMF.map_const _ true)

/-- The half-block scheme does not have plaintext integrity, whatever the block cipher. -/
theorem BlockCipher.not_encForge_halfBlockCipher (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) : ¬ (F.halfBlockCipher hblock).EncForge := by
  intro h
  have hneg := h.negligible F.allOnesForger F.isOraclePPT_allOnesForger
  simp only [BlockCipher.eval_encForgeGame_halfBlockCipher_allOnesForger, Game.succProbability,
    PMF.pure_apply_self, ENNReal.toNNReal_one] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- **Boneh–Shoup, the remark after the statement of Theorem 9.1 (p. 363)**, from any pseudorandom
function: a CCA-secure cipher with neither ciphertext integrity nor plaintext integrity exists. The
witness is the half-block scheme over four Feistel rounds of the function (`lubyRackoff4Cipher`),
so the hypotheses of `BlockCipher.StrongPRP.indcca_halfBlockCipher` can be met. The book's
"(or plaintext) integrity" is read as `SymmetricCipher.EncForge`. -/
theorem PseudorandomFunction.exists_indcca_not_integrity
    {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family) :
    ∃ E : SymmetricCipher, E.INDCCA ∧ ¬ E.CiphertextIntegrity ∧ ¬ E.EncForge := by
  have hblock : ∀ n, (lubyRackoff4Cipher family hfamily.polyTime hfamily.length_eq).blockLen n =
      2 * n := fun _ => rfl
  exact ⟨_, hfamily.strongPRP_lubyRackoff4Cipher.indcca_halfBlockCipher hblock,
    BlockCipher.not_ciphertextIntegrity_halfBlockCipher _ hblock,
    BlockCipher.not_encForge_halfBlockCipher _ hblock⟩

end Cslib.Crypto
