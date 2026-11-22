/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH.WordKEM
public import CslibFrontier.Computability.Probabilistic.Oracle.ReplayParameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Substitution
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PMFSwap

/-!
# Asymptotic ROM IND-CCA security of the Diffie–Hellman KEM under Gap-CDH

This module bridges the word-level random-oracle DH-KEM (`dhKEMCCAWordGame`) and its certified
word-level reduction (`dhKEMToGapCDHWord`) from
`CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH.WordKEM` to the typed per-group games and
reduction (`PrimeOrderGroupFamily.dhKEMCCAGame`, `PrimeOrderGroupFamily.gapCDHGame`,
`PrimeOrderGroupFamily.dhKEMToGapCDH`) of
`CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH`, and proves the asymptotic security
theorem ([KatzLindell2020], Theorem 12.22, p. 435).

For any uniform strict oracle-PPT adversary `A`, `IsOraclePPTOn.exists_savedCoins` yields a
coin-tape machine whose fixed-coin replays `savedCoinDHKEMAdversary` instantiate typed
`PrimeOrderGroupFamily.DHKEMAdversary` adversaries at each `(n, d)`. Because `F.Carrier d` is
finite, every challenge word at `(n, d)` has bounded length, so padding the coin tape to
`dhKEMCoinBudget` makes the coin draw independent of `(x, y, H, key)`. Query-by-query simulation
through `routeToTypedQuery` and `tableRep` equates:
1. `dhKEMCCAWordGameAt` with the coin-averaged typed `dhKEMCCAGame`, and
2. the execution of `dhKEMToGapCDHWord` on every encoded Gap-CDH instance (and hence
   `gapCDHWordGame`) with the coin-averaged typed `dhKEMToGapCDH` (`eval_run_dhKEMToGapCDHWord_eq`
   and `gapCDHWordGame_dhKEMToGapCDHWord_eq`).

Averaging `PrimeOrderGroupFamily.advantage_dhKEMCCAGame_le` over the coin tape and `setup n` yields
the exact concrete family bound `advantage_dhKEMCCAWordGame_le` (with multiplicative factor `1` and
zero additive loss), from which `GapCDH.dhKEMROMINDCCA` follows directly.

## Main definitions

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.routeToTypedQuery`: translate word-level `DHKEMOp`
  requests to typed `PrimeOrderGroupFamily.DHKEMQuery` calls via `F.decode d`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMCoinBudget`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.savedCoinDHKEMAdversary`: per-`(n, d)` coin budget
  and typed fixed-coin replay KEM adversary.

## Main results

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.eval_run_dhKEMToGapCDHWord_eq`: exact distributional
  equality between `dhKEMToGapCDHWord` and the coin-averaged typed `dhKEMToGapCDH` on every encoded
  Gap-CDH challenge.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.advantage_dhKEMCCAWordGame_le`: concrete family
  bound `Adv_CCA(A) ≤ Succ_GapCDH(dhKEMToGapCDHWord A)` at every `n`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDH.dhKEMROMINDCCA`: **[KatzLindell2020],
  Theorem 12.22** — under `F.GapCDH setup`, Construction 12.19 is ROM IND-CCA secure for any
  polynomial-time `keyLen` (`keyLen = id` gives the `n`-bit keys of Definition 12.13).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], 3rd edition,
  Definition 12.13 (p. 425), Construction 12.19 (p. 431), §12.4.4 (p. 434), and Theorem 12.22
  (p. 435).
-/

@[expose] public section

namespace Cslib.Crypto.DecodablePrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped NNReal

variable (F : DecodablePrimeOrderGroupFamily)

/-- Translate a word-level `DHKEMOp` request at group `d` into a typed `DHKEMQuery` program,
answering out-of-group requests (`F.decode d w = none`) with `[]` without making any oracle call. -/
def routeToTypedQuery (d : F.Desc) {m : ℕ} :
    DHKEMOp → List Bool →
      OracleComp (PrimeOrderGroupFamily.DHKEMSpec (F.Carrier d) (BitString m)) (List Bool)
  | .hash, w =>
    match F.decode d w with
    | some z =>
      List.ofFn <$> OracleComp.query
        (spec := PrimeOrderGroupFamily.DHKEMSpec (F.Carrier d) (BitString m)) (.hash z)
    | none => pure []
  | .decaps, c =>
    match F.decode d c with
    | some C =>
      (fun r => encOption encBits (r.map List.ofFn)) <$> OracleComp.query
        (spec := PrimeOrderGroupFamily.DHKEMSpec (F.Carrier d) (BitString m)) (.decaps C)
    | none => pure []

/-- Maximum encoded bit length among all elements of `F.Carrier d`. -/
noncomputable def maxElemEncLen (d : F.Desc) : ℕ :=
  letI : Fintype (F.Carrier d) := F.fintypeCarrier d
  Finset.univ.sup fun u : F.Carrier d => (F.encode d u).length

theorem length_encode_le_maxElemEncLen (d : F.Desc) (u : F.Carrier d) :
    (F.encode d u).length ≤ F.maxElemEncLen d := by
  let _ : Fintype (F.Carrier d) := F.fintypeCarrier d
  exact Finset.le_sup (f := fun v : F.Carrier d => (F.encode d v).length) (Finset.mem_univ u)

/-- Uniform upper bound on the bit length of every encoded `DHKEMChallenge` at `(n, d)` with a
`keyLen n`-bit key. -/
noncomputable def maxChallengeLen (keyLen : ℕ → ℕ) (n : ℕ) (d : F.Desc) : ℕ :=
  2 * (F.encDesc d).length + 4 * F.maxElemEncLen d + keyLen n + 10

theorem length_encDHKEMChallenge_le (keyLen : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (h cStar : F.Carrier d) (key : BitString (keyLen n)) :
    (encDHKEMChallenge F.toPrimeOrderGroupFamily
      ⟨d, F.encode d h, F.encode d cStar, List.ofFn key⟩).length ≤
        F.maxChallengeLen keyLen n d := by
  have hh := F.length_encode_le_maxElemEncLen d h
  have hc := F.length_encode_le_maxElemEncLen d cStar
  have hk : (List.ofFn key).length = keyLen n := List.length_ofFn
  unfold maxChallengeLen
  enc_len [encDHKEMChallenge_apply, hk]

/-- Uniform coin-tape length for replaying an oracle machine with clock `(c, deg)` on any challenge
at `(n, d)`. -/
noncomputable def dhKEMCoinBudget (keyLen : ℕ → ℕ) (c deg n : ℕ) (d : F.Desc) : ℕ :=
  c * (2 * n + 4 + F.maxChallengeLen keyLen n d) ^ deg

theorem clock_le_dhKEMCoinBudget (keyLen : ℕ → ℕ) (c deg n : ℕ) (d : F.Desc)
    {w : List Bool} (hw : w.length ≤ F.maxChallengeLen keyLen n d) :
    c * ((encPair encUnary encBits (n, w)).length + 1) ^ deg ≤
      F.dhKEMCoinBudget keyLen c deg n d := by
  apply Nat.mul_le_mul_left c
  apply Nat.pow_le_pow_left
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  omega

/-- Fixed-coin typed KEM adversary obtained by replaying `machine` on the encoded challenge word
and routing its queries through `routeToTypedQuery`. -/
noncomputable def savedCoinDHKEMAdversary {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control DHKEMOp)
    (keyLen : ℕ → ℕ) (c deg n : ℕ) (d : F.Desc) (coins : List Bool) :
    F.toPrimeOrderGroupFamily.DHKEMAdversary d (BitString (keyLen n)) :=
  fun ⟨h, cStar, key⟩ =>
    let challenge := encDHKEMChallenge F.toPrimeOrderGroupFamily
      ⟨d, F.encode d h, F.encode d cStar, List.ofFn key⟩
    let input := encPair encUnary encBits (n, challenge)
    Decoder.bool.decode <$>
      machine.runCoins (F.routeToTypedQuery d)
        (coins.take (c * (input.length + 1) ^ deg)) input

/-- Word-level representation of a typed `SimTable`. -/
def tableRep (d : F.Desc) {m : ℕ}
    (table : F.toPrimeOrderGroupFamily.SimTable d (BitString m)) : List DHKEMSimEntry :=
  table.map fun
    | (.inl z, k) => ⟨false, F.encode d z, List.ofFn k⟩
    | (.inr c, k) => ⟨true, F.encode d c, List.ofFn k⟩

/-! ### Query-by-query and table simulation -/

private theorem eval_run_findSomeM?_eq_find? (d : F.Desc) (y : ZMod (F.order d))
    (select : DHKEMSimEntry → WordOracleComp Unit (Option (List Bool)))
    (pred : DHKEMSimEntry → Bool) (extract : DHKEMSimEntry → List Bool)
    (hsel : ∀ e, ProbComp.eval ((select e).run fun req => pure (F.ddhWordOracle d y req.2)) =
      PMF.pure (if pred e then some (extract e) else none))
    (t : List DHKEMSimEntry) :
    ProbComp.eval ((t.findSomeM? select).run fun req => pure (F.ddhWordOracle d y req.2)) =
      PMF.pure ((t.find? pred).map extract) := by
  induction t with
  | nil => simp [List.findSomeM?_nil]
  | cons e rest ih =>
    simp only [List.findSomeM?_cons, ProbOracleComp.run_bind, ProbComp.eval_bind, hsel e,
      PMF.pure_bind]
    cases h : pred e <;> simp [h, ih]

private theorem interpret_routeToTypedQuery_dhKEMAnswer (d : F.Desc) {m : ℕ}
    (H : F.Carrier d → BitString m) (x y : ZMod (F.order d)) (op : DHKEMOp) (w : List Bool) :
    OracleComp.interpret
        (fun q => PMF.pure (F.toPrimeOrderGroupFamily.dhKEMAnswer d H x (y • F.generator d) q))
        (F.routeToTypedQuery d op w) =
      PMF.pure (F.dhKEMCCAWordAnswer d H x (F.encode d (y • F.generator d)) (op, w)) := by
  cases op with
  | hash =>
    simp only [routeToTypedQuery, dhKEMCCAWordAnswer]
    cases F.decode d w <;>
      simp [OracleComp.interpret_map, OracleComp.interpret_query,
        PrimeOrderGroupFamily.dhKEMAnswer]
  | decaps =>
    simp only [routeToTypedQuery, dhKEMCCAWordAnswer]
    cases hdec : F.decode d w with
    | none =>
      have hne : w ≠ F.encode d (y • F.generator d) := by
        rintro rfl; simp [F.decode_encode] at hdec
      simp [hne, dhKEMDecapsWord, hdec, encOption]
    | some C =>
      have hw : w = F.encode d C := F.encode_eq_of_decode_eq_some hdec
      subst hw
      by_cases hc : C = y • F.generator d
      · subst hc
        simp [OracleComp.interpret_map, OracleComp.interpret_query,
          PrimeOrderGroupFamily.dhKEMAnswer, encOption]
      · have hwne : F.encode d C ≠ F.encode d (y • F.generator d) :=
          fun h => hc (F.encode_injective d h)
        simp [hc, hwne, OracleComp.interpret_map, OracleComp.interpret_query,
          PrimeOrderGroupFamily.dhKEMAnswer, dhKEMDecapsWord, PrimeOrderGroupFamily.dhKEMDecaps,
          F.decode_encode]

private theorem run_runCoins_routeToTypedQuery (d : F.Desc) {m : ℕ} {σ σ' : Type}
    (rep : σ' → σ)
    (handler' : (q : PrimeOrderGroupFamily.DHKEMQuery (F.Carrier d)) →
      StateT σ' PMF (PrimeOrderGroupFamily.DHKEMSpec (F.Carrier d) (BitString m) q))
    (handler : DHKEMOp × List Bool → StateT σ PMF (List Bool))
    (hstep : ∀ op w s,
      (((OracleComp.interpret handler' (F.routeToTypedQuery (m := m) d op w)).run s)).map
        (fun p => (p.1, rep p.2)) = (handler (op, w)).run (rep s))
    {k : ℕ} {Control : Type} (machine : _root_.Turing.MultiTapePTM k Bool Control DHKEMOp)
    (tape input : List Bool) (s : σ') :
    (((OracleComp.interpret handler'
        (machine.runCoins (F.routeToTypedQuery (m := m) d) tape input)).run s)).map
        (fun p => (p.1, rep p.2)) =
      ProbOracleComp.runWith handler
        (machine.runCoins (fun op w => ProbOracleComp.query (op, w)) tape input) (rep s) := by
  let W := machine.runCoins
    (fun op w => OracleComp.query (spec := fun _ : DHKEMOp × List Bool => List Bool) (op, w))
    tape input
  have h₁ : machine.runCoins (F.routeToTypedQuery (m := m) d) tape input =
      OracleComp.interpret (fun q => F.routeToTypedQuery (m := m) d q.1 q.2) W := by
    simp only [W, _root_.Turing.MultiTapePTM.interpret_runCoins, OracleComp.interpret_query]
  have h₂ : machine.runCoins (fun op w => ProbOracleComp.query (op, w)) tape input =
      OracleComp.interpret (fun q => ProbOracleComp.query q) W := by
    simp only [W, _root_.Turing.MultiTapePTM.interpret_runCoins, OracleComp.interpret_query]
  rw [h₁, h₂, OracleComp.interpret_interpret, ProbOracleComp.runWith_eq_run_interpret,
    OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  exact OracleComp.run_interpret_map_state _ _ rep (fun q st => hstep q.1 q.2 st) W s

private theorem eval_run_eq_fst_runWith {Query α : Type} {spec : Query → Type}
    (ans : (q : Query) → spec q) (program : ProbOracleComp spec α) :
    ProbComp.eval (program.run fun q => pure (ans q)) =
      (ProbOracleComp.runWith (fun q (st : Unit) => PMF.pure (ans q, st)) program ()).map
        Prod.fst := by
  have hro := ProbOracleComp.runWith_readOnly (fun q (_ : Unit) => PMF.pure (ans q)) program ()
  simp only [PMF.pure_map] at hro
  rw [hro, PMF.map_comp, ProbOracleComp.eval_run, OracleComp.evalWith_eq_interpret]
  have hid : (Prod.fst ∘ fun x : α => (x, ())) = id := rfl
  simp only [hid, PMF.map_id, ProbComp.eval_pure]

private theorem eval_run_run_interpret {Query Query' σ α : Type}
    {spec : Query → Type} {spec' : Query' → Type}
    (inner : (q : Query) → StateT σ (ProbOracleComp spec') (spec q))
    (O : (q : Query') → ProbComp (spec' q)) (program : ProbOracleComp spec α) (s : σ) :
    ProbComp.eval (((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        inner) program).run s).run O) =
      ProbOracleComp.runWith (fun q st => ProbComp.eval (((inner q).run st).run O)) program s := by
  rw [ProbOracleComp.runWith_eq_run_interpret]
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_bind, ProbOracleComp.run_bind, ProbComp.eval_bind,
      OracleComp.run_interpret_query, OracleComp.run_interpret_query]
    cases q with
    | inl k =>
      change ProbComp.eval (((ProbOracleComp.sample (ProbComp.unifFin k) >>= fun x =>
          pure (x, s)).run O)) >>= _ =
        ((ProbComp.unifOracle k).map (·, s)) >>= _
      simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_pure,
        ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_unifFin, ProbComp.unifOracle,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
        Function.comp_def]
      exact congrArg (PMF.bind _) (funext fun x => ih x s)
    | inr q =>
      exact congrArg (PMF.bind _) (funext fun r => ih r.1 r.2)

private theorem find?_tableRep_hash (d : F.Desc) {m : ℕ} (y : ZMod (F.order d))
    (z : F.Carrier d) (table : F.toPrimeOrderGroupFamily.SimTable d (BitString m)) :
    ((F.tableRep d table).find? fun e =>
        if e.isDecaps then F.ddhOraclePred d y e.elem (F.encode d z)
        else e.elem == F.encode d z).map DHKEMSimEntry.key =
      ((table.find? fun e => F.toPrimeOrderGroupFamily.hashMatches d y z e.1).map Prod.snd).map
        List.ofFn := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨l, k⟩ := e
    cases l with
    | inl z' =>
      have hcons : F.tableRep d ((.inl z', k) :: rest) =
          ⟨false, F.encode d z', List.ofFn k⟩ :: F.tableRep d rest := rfl
      have heq : (F.encode d z' == F.encode d z) = decide (z' = z) :=
        Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, (F.encode_injective d).eq_iff, decide_eq_true_eq])
      rw [hcons, List.find?_cons, List.find?_cons]
      by_cases hz : z' = z <;> simp [PrimeOrderGroupFamily.hashMatches, heq, hz, ih]
    | inr c =>
      have hcons : F.tableRep d ((.inr c, k) :: rest) =
          ⟨true, F.encode d c, List.ofFn k⟩ :: F.tableRep d rest := rfl
      rw [hcons, List.find?_cons, List.find?_cons]
      by_cases hz : z = y • c <;>
        simp [PrimeOrderGroupFamily.hashMatches, ddhOraclePred_encode, hz, ih]

private theorem find?_tableRep_decaps (d : F.Desc) {m : ℕ} (y : ZMod (F.order d))
    (c : F.Carrier d) (table : F.toPrimeOrderGroupFamily.SimTable d (BitString m)) :
    ((F.tableRep d table).find? fun e =>
        if e.isDecaps then e.elem == F.encode d c
        else F.ddhOraclePred d y (F.encode d c) e.elem).map DHKEMSimEntry.key =
      ((table.find? fun e => F.toPrimeOrderGroupFamily.decapsMatches d y c e.1).map Prod.snd).map
        List.ofFn := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨l, k⟩ := e
    cases l with
    | inl z =>
      have hcons : F.tableRep d ((.inl z, k) :: rest) =
          ⟨false, F.encode d z, List.ofFn k⟩ :: F.tableRep d rest := rfl
      rw [hcons, List.find?_cons, List.find?_cons]
      by_cases hz : z = y • c <;>
        simp [PrimeOrderGroupFamily.decapsMatches, ddhOraclePred_encode, hz, ih]
    | inr c' =>
      have hcons : F.tableRep d ((.inr c', k) :: rest) =
          ⟨true, F.encode d c', List.ofFn k⟩ :: F.tableRep d rest := rfl
      have heq : (F.encode d c' == F.encode d c) = decide (c' = c) :=
        Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, (F.encode_injective d).eq_iff, decide_eq_true_eq])
      rw [hcons, List.find?_cons, List.find?_cons]
      by_cases hc : c' = c <;> simp [PrimeOrderGroupFamily.decapsMatches, heq, hc, ih]

private theorem simWordHandler_step (keyLen : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (y : ZMod (F.order d)) (cStar : F.Carrier d) (op : DHKEMOp) (w : List Bool)
    (table : F.toPrimeOrderGroupFamily.SimTable d (BitString (keyLen n))) :
    (((OracleComp.interpret
        (F.toPrimeOrderGroupFamily.lowerHandler d y
          (F.toPrimeOrderGroupFamily.simHandler d
            (ProbComp.uniform (BitString (keyLen n))) cStar))
        (F.routeToTypedQuery d op w)).run table)).map (fun p => (p.1, F.tableRep d p.2)) =
      ProbComp.eval (((F.simWordHandler keyLen n d (F.encode d cStar) (op, w)
        (F.tableRep d table))).run fun req => pure (F.ddhWordOracle d y req.2)) := by
  cases op with
  | hash =>
    simp only [routeToTypedQuery, simWordHandler]
    cases hdec : F.decode d w with
    | none =>
      have helem : F.isElem (d, w) = false := by simp [isElem, hdec]
      simp [helem]
    | some z =>
      have hw : w = F.encode d z := F.encode_eq_of_decode_eq_some hdec
      subst hw
      simp only [F.isElem_encode, ↓reduceIte, OracleComp.run_interpret_map,
        OracleComp.run_interpret_query, PMF.monad_map_eq_map, PMF.map_comp,
        PrimeOrderGroupFamily.lowerHandler, F.toPrimeOrderGroupFamily.runDDH_simHandler_hash,
        simLookupWord, ProbOracleComp.run_bind, ProbComp.eval_bind]
      have hsel : ∀ e, ProbComp.eval
          ((hashSelectWord (F.encode d z) e).run fun req => pure (F.ddhWordOracle d y req.2)) =
          PMF.pure (if (if e.isDecaps then F.ddhOraclePred d y e.elem (F.encode d z)
            else e.elem == F.encode d z) then some e.key else none) := by
        intro e; by_cases hd : e.isDecaps <;> simp [hashSelectWord, hd]
      rw [F.eval_run_findSomeM?_eq_find? d y _ _ DHKEMSimEntry.key hsel,
        F.find?_tableRep_hash d y z table, PMF.pure_bind]
      cases hfind : (table.find? fun e =>
          F.toPrimeOrderGroupFamily.hashMatches d y z e.1).map Prod.snd with
      | some key => simp
      | none =>
        simp [ProbOracleComp.run_sample, BitString.eval_sampleList, BitString.uniformList,
          BitString, PMF.map_comp, Function.comp_def, tableRep]
  | decaps =>
    simp only [routeToTypedQuery, simWordHandler]
    cases hdec : F.decode d w with
    | none =>
      have helem : F.isElem (d, w) = false := by simp [isElem, hdec]
      simp [helem]
    | some C =>
      have hw : w = F.encode d C := F.encode_eq_of_decode_eq_some hdec
      subst hw
      have heq : (F.encode d C == F.encode d cStar) = decide (C = cStar) :=
        Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, (F.encode_injective d).eq_iff, decide_eq_true_eq])
      simp only [F.isElem_encode, Bool.not_true, Bool.false_or, heq,
        OracleComp.run_interpret_map, OracleComp.run_interpret_query, PMF.monad_map_eq_map,
        PMF.map_comp, PrimeOrderGroupFamily.lowerHandler,
        F.toPrimeOrderGroupFamily.runDDH_simHandler_decaps]
      by_cases hc : C = cStar
      · subst hc; simp [encOption]
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_map,
          ProbComp.eval_map, simLookupWord, ProbOracleComp.run_bind, ProbComp.eval_bind]
        have hsel : ∀ e, ProbComp.eval
            ((decapsSelectWord (F.encode d C) e).run fun req => pure (F.ddhWordOracle d y req.2)) =
            PMF.pure (if (if e.isDecaps then e.elem == F.encode d C
              else F.ddhOraclePred d y (F.encode d C) e.elem) then some e.key else none) := by
          intro e; by_cases hd : e.isDecaps <;> simp [decapsSelectWord, hd]
        rw [F.eval_run_findSomeM?_eq_find? d y _ _ DHKEMSimEntry.key hsel,
          F.find?_tableRep_decaps d y C table, PMF.pure_bind]
        cases hfind : (table.find? fun e =>
            F.toPrimeOrderGroupFamily.decapsMatches d y C e.1).map Prod.snd with
        | some key => simp
        | none =>
          simp [ProbOracleComp.run_sample, BitString.eval_sampleList, BitString.uniformList,
            BitString, PMF.map_comp, Function.comp_def, tableRep]

private theorem eval_run_extractDHWord (d : F.Desc) {m : ℕ} (y : ZMod (F.order d))
    (cStar : F.Carrier d) (table : F.toPrimeOrderGroupFamily.SimTable d (BitString m)) :
    ProbComp.eval ((F.extractDHWord d (F.encode d cStar) (F.tableRep d table)).run
        fun req => pure (F.ddhWordOracle d y req.2)) =
      (F.toPrimeOrderGroupFamily.runDDH d y
        (F.toPrimeOrderGroupFamily.extractDH d cStar table)).map (F.encode d) := by
  induction table with
  | nil => simp [extractDHWord, List.findSomeM?_nil, tableRep]
  | cons e rest ih =>
    obtain ⟨l, k⟩ := e
    cases l with
    | inl z =>
      by_cases hz : z = y • cStar <;>
        simp [extractDHWord, List.findSomeM?_cons, extractSelectWord, tableRep,
          ddhOraclePred_encode, hz, ProbComp.eval_map, ← ih]
    | inr c =>
      simpa [extractDHWord, List.findSomeM?_cons, extractSelectWord, tableRep] using ih

/-! ### Saved-coin replay equalities and Theorem 12.22 -/

private theorem replay_runWith_eq (keyLen : ℕ → ℕ)
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    {k : ℕ} {Control : Type} (machine : _root_.Turing.MultiTapePTM k Bool Control DHKEMOp)
    (c deg : ℕ)
    (hrun : ∀ (x : ℕ × List Bool) (Store : Type)
      (oracle : DHKEMOp × List Bool → StateT Store PMF (List Bool)) (s : Store),
      ProbOracleComp.runWith oracle (encBool <$> adversary x.1 x.2) s =
        (BitString.uniformList (c * ((encPair encUnary encBits x).length + 1) ^ deg)).bind
          fun coins => ProbOracleComp.runWith oracle
            (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins
              (encPair encUnary encBits x)) s)
    (n : ℕ) (d : F.Desc) (h cStar : F.Carrier d) (key : BitString (keyLen n))
    {σ σ' : Type} (rep : σ' → σ)
    (handler' : (q : PrimeOrderGroupFamily.DHKEMQuery (F.Carrier d)) →
      StateT σ' PMF (PrimeOrderGroupFamily.DHKEMSpec (F.Carrier d) (BitString (keyLen n)) q))
    (handler : DHKEMOp × List Bool → StateT σ PMF (List Bool))
    (hstep : ∀ op w s,
      (((OracleComp.interpret handler' (F.routeToTypedQuery d op w)).run s)).map
        (fun p => (p.1, rep p.2)) = (handler (op, w)).run (rep s))
    (s : σ') :
    ProbOracleComp.runWith handler
        (adversary n (encDHKEMChallenge F.toPrimeOrderGroupFamily
          ⟨d, F.encode d h, F.encode d cStar, List.ofFn key⟩)) (rep s) =
      (BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
        (((OracleComp.interpret handler'
          (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins (h, cStar, key))).run s)).map
          (fun p => (p.1, rep p.2)) := by
  let w := encDHKEMChallenge F.toPrimeOrderGroupFamily
    ⟨d, F.encode d h, F.encode d cStar, List.ofFn key⟩
  have hclock := F.clock_le_dhKEMCoinBudget keyLen c deg n d
    (F.length_encDHKEMChallenge_le keyLen n d h cStar key)
  have hdecode (μ : PMF (Bool × σ)) :
      (μ.map (Prod.map encBool id)).map (Prod.map Decoder.bool.decode id) = μ := by
    rw [PMF.map_comp]
    convert PMF.map_id μ
    funext p
    exact Prod.ext (Decoder.bool.decode_enc _) rfl
  rw [← hdecode (ProbOracleComp.runWith handler (adversary n w) (rep s)),
    ← ProbOracleComp.runWith_map, hrun (n, w) σ handler (rep s),
    ← BitString.uniformList_take hclock, PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun coins => ?_)
  simp only [savedCoinDHKEMAdversary, w, Function.comp_def]
  rw [OracleComp.run_interpret_map, PMF.monad_map_eq_map, PMF.map_comp,
    ← F.run_runCoins_routeToTypedQuery d rep handler' handler hstep machine _ _ s, PMF.map_comp]
  rfl

private theorem dhKEMCCAWordGameAt_eq_savedCoin (keyLen : ℕ → ℕ)
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    {k : ℕ} {Control : Type} (machine : _root_.Turing.MultiTapePTM k Bool Control DHKEMOp)
    (c deg : ℕ)
    (hrun : ∀ (x : ℕ × List Bool) (Store : Type)
      (oracle : DHKEMOp × List Bool → StateT Store PMF (List Bool)) (s : Store),
      ProbOracleComp.runWith oracle (encBool <$> adversary x.1 x.2) s =
        (BitString.uniformList (c * ((encPair encUnary encBits x).length + 1) ^ deg)).bind
          fun coins => ProbOracleComp.runWith oracle
            (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins
              (encPair encUnary encBits x)) s)
    (bit : Bool) (n : ℕ) (d : F.Desc) :
    F.dhKEMCCAWordGameAt keyLen adversary bit n d =
      letI : Fintype (F.Carrier d) := F.fintypeCarrier d
      (BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
        F.toPrimeOrderGroupFamily.dhKEMCCAGame d (ProbComp.uniform (BitString (keyLen n)))
          (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins) bit := by
  let _ : Fintype (F.Carrier d) := F.fintypeCarrier d
  simp only [dhKEMCCAWordGameAt, PrimeOrderGroupFamily.dhKEMCCAGame, dhKEMEncapsWord,
    PrimeOrderGroupFamily.dhKEMEncaps, Probability.PMF.monad_bind_eq_bind]
  have hite (kReal kRand : BitString (keyLen n)) :
      (if bit = true then List.ofFn kReal else List.ofFn kRand) =
        List.ofFn (if bit = true then kReal else kRand) := by
    cases bit <;> rfl
  have hbody (x y : ZMod (F.order d)) (H : F.Carrier d → BitString (keyLen n))
      (random : BitString (keyLen n)) :
      ProbComp.eval ((adversary n (encDHKEMChallenge F.toPrimeOrderGroupFamily
        ⟨d, F.encode d (x • F.generator d), F.encode d (y • F.generator d),
          if bit = true then List.ofFn (H (y • x • F.generator d)) else List.ofFn random⟩)).run
        fun req => pure (F.dhKEMCCAWordAnswer d H x (F.encode d (y • F.generator d)) req)) =
        (BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
          OracleComp.interpret
            (fun q => PMF.pure (F.toPrimeOrderGroupFamily.dhKEMAnswer d H x (y • F.generator d) q))
            (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins
              (x • F.generator d, y • F.generator d,
                if bit = true then H (y • x • F.generator d) else random)) := by
    rw [hite, eval_run_eq_fst_runWith]
    have hrep := F.replay_runWith_eq keyLen machine c deg hrun n d (x • F.generator d)
      (y • F.generator d) (if bit = true then H (y • x • F.generator d) else random) id
      (fun q => StateT.lift
        (PMF.pure (F.toPrimeOrderGroupFamily.dhKEMAnswer d H x (y • F.generator d) q)))
      (fun req st => PMF.pure (F.dhKEMCCAWordAnswer d H x (F.encode d (y • F.generator d)) req, st))
      (fun op w s => by
        rw [OracleComp.run_interpret_lift, PMF.monad_map_eq_map,
          F.interpret_routeToTypedQuery_dhKEMAnswer d H x y op w, PMF.pure_map, PMF.pure_map]
        rfl) ()
    rw [hrep, PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun coins => ?_)
    rw [OracleComp.run_interpret_lift, PMF.monad_map_eq_map, PMF.map_comp, PMF.map_comp]
    have hid : ((Prod.fst ∘ fun p : Bool × Unit => (p.1, id p.2)) ∘ fun b : Bool => (b, ())) =
        id := rfl
    rw [hid, PMF.map_id]
  have hlhs :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun x =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun y =>
        (Probability.PMF.pi fun _ : F.Carrier d =>
          ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))).bind fun H =>
        (ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))).bind fun random =>
        ProbComp.eval ((adversary n (encDHKEMChallenge F.toPrimeOrderGroupFamily
          ⟨d, F.encode d (x • F.generator d), F.encode d (y • F.generator d),
            if bit = true then List.ofFn (H (y • x • F.generator d)) else List.ofFn random⟩)).run
          fun req => pure (F.dhKEMCCAWordAnswer d H x (F.encode d (y • F.generator d)) req))) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun x =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun y =>
        (Probability.PMF.pi fun _ : F.Carrier d =>
          ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))).bind fun H =>
        (ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))).bind fun random =>
        (BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
          OracleComp.interpret
            (fun q => PMF.pure (F.toPrimeOrderGroupFamily.dhKEMAnswer d H x (y • F.generator d) q))
            (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins
              (x • F.generator d, y • F.generator d,
                if bit = true then H (y • x • F.generator d) else random))) := by
    refine congrArg (PMF.bind _) (funext fun x => congrArg (PMF.bind _) (funext fun y => ?_))
    refine congrArg (PMF.bind _) (funext fun H => congrArg (PMF.bind _) (funext fun random => ?_))
    exact hbody x y H random
  rw [hlhs]
  pmf_swap

/-- **Exact reduction equality** on every encoded Gap-CDH challenge `(a • g, b • g)`: running
`dhKEMToGapCDHWord` against `ddhWordOracle d b` has the exact `PMF` law of drawing saved coins from
`BitString.uniformList (dhKEMCoinBudget ...)` and encoding the output of the typed reduction
`PrimeOrderGroupFamily.dhKEMToGapCDH` on `savedCoinDHKEMAdversary`. -/
theorem eval_run_dhKEMToGapCDHWord_eq (keyLen : ℕ → ℕ)
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    {k : ℕ} {Control : Type} (machine : _root_.Turing.MultiTapePTM k Bool Control DHKEMOp)
    (c deg : ℕ)
    (hrun : ∀ (x : ℕ × List Bool) (Store : Type)
      (oracle : DHKEMOp × List Bool → StateT Store PMF (List Bool)) (s : Store),
      ProbOracleComp.runWith oracle (encBool <$> adversary x.1 x.2) s =
        (BitString.uniformList (c * ((encPair encUnary encBits x).length + 1) ^ deg)).bind
          fun coins => ProbOracleComp.runWith oracle
            (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins
              (encPair encUnary encBits x)) s)
    (n : ℕ) (d : F.Desc) (a b : ZMod (F.order d)) :
    ProbComp.eval
        ((F.dhKEMToGapCDHWord keyLen adversary
          ⟨n, d, F.encode d (a • F.generator d), F.encode d (b • F.generator d)⟩).run
          fun req => pure (F.ddhWordOracle d b req.2)) =
      (BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
        (F.toPrimeOrderGroupFamily.runDDH d b
          (F.toPrimeOrderGroupFamily.dhKEMToGapCDH d
            (ProbComp.uniform (BitString (keyLen n)))
            (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins)
            (a • F.generator d, b • F.generator d))).map (F.encode d) := by
  have hz : (F.encode d (b • F.generator d) == F.encode d 0) = decide (b • F.generator d = 0) :=
    Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, (F.encode_injective d).eq_iff, decide_eq_true_eq])
  by_cases hb0 : b • F.generator d = 0
  · rw [hb0]
    simp [dhKEMToGapCDHWord, PrimeOrderGroupFamily.dhKEMToGapCDH]
  · simp only [dhKEMToGapCDHWord, PrimeOrderGroupFamily.dhKEMToGapCDH, hz, hb0, decide_false,
      Bool.false_eq_true, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
      ProbComp.eval_bind, BitString.eval_sampleList, F.toPrimeOrderGroupFamily.runDDH_bind,
      F.toPrimeOrderGroupFamily.runDDH_sample, F.toPrimeOrderGroupFamily.runDDH_run_interpret,
      PMF.map_bind]
    conv_lhs => rw [BitString.uniformList, PMF.bind_map]
    conv_rhs => rw [PMF.bind_comm]
    simp only [ProbComp.eval_uniform, BitString]
    refine congrArg (PMF.bind _) (funext fun key => ?_)
    dsimp only [Function.comp_def]
    rw [eval_run_run_interpret]
    dsimp only [StateT.run]
    have hrep := F.replay_runWith_eq keyLen machine c deg hrun n d (b • F.generator d)
      (a • F.generator d) key (F.tableRep d)
      (F.toPrimeOrderGroupFamily.lowerHandler d b
        (F.toPrimeOrderGroupFamily.simHandler d (ProbComp.uniform (BitString (keyLen n)))
          (a • F.generator d)))
      (fun req st => ProbComp.eval
        (((F.simWordHandler keyLen n d (F.encode d (a • F.generator d)) req st)).run
          fun r => pure (F.ddhWordOracle d b r.2)))
      (F.simWordHandler_step keyLen n d b (a • F.generator d))
      ([] : F.toPrimeOrderGroupFamily.SimTable d (BitString (keyLen n)))
    change (ProbOracleComp.runWith _ _
      (F.tableRep d ([] : F.toPrimeOrderGroupFamily.SimTable d (BitString (keyLen n))))).bind _ = _
    rw [hrep, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun coins => ?_)
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun res => ?_)
    exact F.eval_run_extractDHWord d b (a • F.generator d) res.2

/-- **Game-level reduction equality**: at every security parameter `n`, the word-level Gap-CDH
experiment of `dhKEMToGapCDHWord` equals the `setup n`- and coin-averaged typed `gapCDHGame` of
`PrimeOrderGroupFamily.dhKEMToGapCDH` on `savedCoinDHKEMAdversary`. -/
theorem gapCDHWordGame_dhKEMToGapCDHWord_eq (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    {k : ℕ} {Control : Type} (machine : _root_.Turing.MultiTapePTM k Bool Control DHKEMOp)
    (c deg : ℕ)
    (hrun : ∀ (x : ℕ × List Bool) (Store : Type)
      (oracle : DHKEMOp × List Bool → StateT Store PMF (List Bool)) (s : Store),
      ProbOracleComp.runWith oracle (encBool <$> adversary x.1 x.2) s =
        (BitString.uniformList (c * ((encPair encUnary encBits x).length + 1) ^ deg)).bind
          fun coins => ProbOracleComp.runWith oracle
            (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins
              (encPair encUnary encBits x)) s)
    (n : ℕ) :
    F.gapCDHWordGame setup (F.dhKEMToGapCDHWord keyLen adversary) n =
      (setup n).bind fun d =>
        (BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
          F.toPrimeOrderGroupFamily.gapCDHGame d
            (F.toPrimeOrderGroupFamily.dhKEMToGapCDH d
              (ProbComp.uniform (BitString (keyLen n)))
              (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins)) := by
  simp only [gapCDHWordGame, Game.withSetup]
  refine congrArg (PMF.bind (setup n)) (funext fun d => ?_)
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    F.eval_run_dhKEMToGapCDHWord_eq keyLen machine c deg hrun n d,
    PrimeOrderGroupFamily.gapCDHGame, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    (F.encode_injective d).eq_iff]
  pmf_swap

/-- **Concrete family-level reduction** for [KatzLindell2020], Theorem 12.22 (p. 435): for every
setup distribution, key length, uniform strict oracle-PPT adversary `adversary`, and security
parameter `n`, the word-level ROM IND-CCA advantage is at most the Gap-CDH success probability of
`dhKEMToGapCDHWord`. -/
theorem advantage_dhKEMCCAWordGame_le (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    (hA : IsOraclePPT encBool adversary) (n : ℕ) :
    Game.advantage (F.dhKEMCCAWordGame setup keyLen adversary true n)
        (F.dhKEMCCAWordGame setup keyLen adversary false n) ≤
      Game.succProbability
        (F.gapCDHWordGame setup (F.dhKEMToGapCDHWord keyLen adversary) n) := by
  obtain ⟨k, Control, _, machine, c, deg, _, hrun⟩ := hA.on.exists_savedCoins
  rw [F.gapCDHWordGame_dhKEMToGapCDHWord_eq setup keyLen machine c deg hrun n]
  simp only [dhKEMCCAWordGame]
  refine Game.advantage_bind_le_succProbability_bind (setup n) _ _ _ fun d => ?_
  let _ : Fintype (F.Carrier d) := F.fintypeCarrier d
  have hle_d : Game.advantage (F.dhKEMCCAWordGameAt keyLen adversary true n d)
      (F.dhKEMCCAWordGameAt keyLen adversary false n d) ≤
      Game.succProbability
        ((BitString.uniformList (F.dhKEMCoinBudget keyLen c deg n d)).bind fun coins =>
          F.toPrimeOrderGroupFamily.gapCDHGame d
            (F.toPrimeOrderGroupFamily.dhKEMToGapCDH d
              (ProbComp.uniform (BitString (keyLen n)))
              (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins))) := by
    rw [F.dhKEMCCAWordGameAt_eq_savedCoin keyLen machine c deg hrun true n d,
      F.dhKEMCCAWordGameAt_eq_savedCoin keyLen machine c deg hrun false n d]
    refine Game.advantage_bind_le_succProbability_bind _ _ _ _ fun coins => ?_
    have hadv := Game.apply_true_le_of_advantage_le
      (F.toPrimeOrderGroupFamily.advantage_dhKEMCCAGame_le d
        (ProbComp.uniform (BitString (keyLen n)))
        (F.savedCoinDHKEMAdversary machine keyLen c deg n d coins))
    rwa [ENNReal.coe_toNNReal (PMF.apply_ne_top _ true)] at hadv
  have hadv_d := Game.apply_true_le_of_advantage_le hle_d
  rwa [ENNReal.coe_toNNReal (PMF.apply_ne_top _ true)] at hadv_d

/-- **[KatzLindell2020], Theorem 12.22 (p. 435).** If Gap-CDH is hard relative to `(F, setup)` and
`keyLen` is computable in polynomial time in unary, then the word-level random-oracle Diffie–Hellman
KEM (Construction 12.19) is IND-CCA secure in the random-oracle model; taking `keyLen = id` gives
the `n`-bit keys of Definition 12.13 (p. 425). -/
theorem GapCDH.dhKEMROMINDCCA {F : DecodablePrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {keyLen : ℕ → ℕ}
    (hGap : F.GapCDH setup)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    F.DHKEMROMINDCCA setup keyLen := by
  intro adversary hA
  exact negligible_of_le
    (hGap (F.dhKEMToGapCDHWord keyLen adversary)
      (F.isOraclePPTOn_dhKEMToGapCDHWord hA hkeyLen))
    (F.advantage_dhKEMCCAWordGame_le setup keyLen hA)

end Cslib.Crypto.DecodablePrimeOrderGroupFamily
