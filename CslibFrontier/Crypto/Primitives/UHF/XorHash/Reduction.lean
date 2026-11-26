/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListCollision
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Primitives.UHF.Computational
public import CslibFrontier.Crypto.Primitives.UHF.XorHash.Word
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.HashFamily.Collisions
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Computational security of XOR-hash

The collision adversary sees the unary security parameter, also used as deterministic
public setup so the key and digest types can depend on it.
The wrapper checks the two messages' block counts and block widths before hashing them
through the same word oracle. The ideal random function restricts to a uniform table on
tagged blocks, giving the statistical collision bound. The resulting uniform strict PPT
reduction proves the single-pair guarantee in Boneh–Shoup v0.6, §7.2.3, Theorem 7.6
(printed pp. 261–262), including equation (7.12).
For Exercise 7.28, the direct multi-query wrapper retains at most `Q` messages, uses at most
`Q * ℓ` queries, and incurs an ideal-table loss of at most `Q.choose 2 / |Y|`.

## Main results

* `Cslib.Crypto.UHF.isOraclePPT_xorHashWordCollisionReduction`: certify the explicit wrapper.
* `Cslib.Crypto.UHF.succProbability_xorHashWordFamily_le`: the concrete PRF-plus-collision bound.
* `Cslib.Crypto.UHF.isComputationalUHF_xorHashWordFamily`: the asymptotic security guarantee.
* `Cslib.Crypto.UHF.isOraclePPT_xorHashWordMultiQueryReduction`: the bounded-list wrapper is
  uniform strict oracle PPT.
* `Cslib.Crypto.UHF.isQueryBounded_xorHashWordMultiQueryReduction`: its `Q * ℓ` query budget.
* `Cslib.Crypto.UHF.succProbability_multiQueryGame_xorHashWordFamily_le`: the direct
  multi-query advantage bound with an unordered-pair ideal term.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-- Valid XOR-hash messages contain at most `ℓ` blocks, all of exactly `blockWidth` bits. -/
@[expose] def xorHashWordValid (ℓ blockWidth : ℕ) (m : List (List Bool)) : Bool :=
  decide (m.length ≤ ℓ) && m.all fun block => decide (block.length = blockWidth)

/-- Hash the bounded prefix, interpreting each block at `blockWidth` and encoding the
position as in the word-oracle evaluator. On valid messages no truncation or padding occurs. -/
@[expose] def xorHashWordFromTable {width : ℕ} (ℓ blockWidth : ℕ)
    (table : List Bool → BitString width) (m : List (List Bool)) : BitString width :=
  xorHash (ℓ := ℓ) (Y := BitString width)
    (fun (block, i) => table (xorHashTaggedWord ℓ (List.ofFn block) i.val))
    ⟨(m.take ℓ).map (BitString.ofList blockWidth), by
      simpa only [List.length_map] using List.length_take_le ℓ m⟩

/-- Instantiate XOR-hash with a word PRF whose input width is the block cap plus the block
width. The security parameter fixes the private key width and all other dimensions. -/
@[expose] def xorHashWordFamily (ℓ blockWidth width : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (key : BitString n) :
    List (List Bool) → BitString (width n) :=
  xorHashWordFromTable (ℓ n) (blockWidth n)
    (fun req => BitString.ofList (width n) (family (List.ofFn key) req))

/-- Test a collision by evaluating the two valid messages through the same oracle.
The auxiliary input of the PRF game is unused. -/
@[expose] def xorHashWordCollisionReduction (ℓ blockWidth width : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (CollisionGuess (List (List Bool)))) : OracleDistinguisher :=
  fun n _ => do
    let guess ← ProbOracleComp.sample (A (n, n))
    if xorHashWordValid (ℓ n) (blockWidth n) guess.first &&
        xorHashWordValid (ℓ n) (blockWidth n) guess.second then
      let first ← xorHashWordQueries (ℓ n) (width n) guess.first
      let second ← xorHashWordQueries (ℓ n) (width n) guess.second
      return decide (guess.first ≠ guess.second ∧ first = second)
    else
      return false

/-- Evaluate the valid messages in the first `Q n` entries of the adversary's list,
using one shared word oracle. Accept exactly when distinct retained messages have the
same digest. Repeated messages alone cannot give a collision. -/
@[expose] def xorHashWordMultiQueryReduction (ℓ blockWidth width Q : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (List (List (List Bool)))) : OracleDistinguisher :=
  fun n _ => do
    let guesses ← ProbOracleComp.sample (A (n, n))
    let ms := (guesses.take (Q n)).filter (xorHashWordValid (ℓ n) (blockWidth n))
    let ds ← ms.mapM (xorHashWordQueries (ℓ n) (width n))
    return hasDistinctCollision (ds.zip ms)

/-- Each retained valid message costs at most `ℓ n` oracle calls, even for arbitrary replies. -/
theorem isQueryBounded_xorHashWordMultiQueryReduction (ℓ blockWidth width Q : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (List (List (List Bool)))) (n : ℕ) (aux : List Bool) :
    (xorHashWordMultiQueryReduction ℓ blockWidth width Q A n aux).IsQueryBounded (Q n * ℓ n) := by
  rw [xorHashWordMultiQueryReduction, ← Nat.zero_add (Q n * ℓ n)]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun guesses => ?_
  let ms := (guesses.take (Q n)).filter (xorHashWordValid (ℓ n) (blockWidth n))
  have htraverse := OracleComp.IsCostBounded.mapM (inputs := ms) fun m _ =>
    isQueryBounded_xorHashWordQueries (ℓ n) (width n) m
  refine (htraverse.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
  have hlen : ms.length ≤ Q n :=
    (List.length_filter_le _ _).trans (List.length_take_le _ _)
  simpa only [Nat.add_zero] using Nat.mul_le_mul_right (ℓ n) hlen

private theorem polyTime_xorHashWordValid {α : Type} {input : α ↪ List Bool}
    {ℓ blockWidth : α → ℕ} {m : α → List (List Bool)}
    (hℓ : ComputableInPolyTime ℓ input encUnary)
    (hb : ComputableInPolyTime blockWidth input encUnary)
    (hm : ComputableInPolyTime m input (encList encBits)) :
    ComputableInPolyTime (fun p => xorHashWordValid (ℓ p) (blockWidth p) (m p)) input encBool := by
  unfold xorHashWordValid
  have hlen := (ComputableInPolyTime.length_list encBits).comp hm
  have hcap : ComputableInPolyTime (fun p => decide ((m p).length ≤ ℓ p)) input encBool := by
    fun_prop
  have hblocks : ComputableInPolyTime
      (fun p => (m p).all (fun b => decide (b.length = blockWidth p))) input encBool :=
    hm.allWithInput (ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd input encBits))
      (hb.comp (ComputableInPolyTime.fst input encBits)))
  exact ComputableInPolyTime.bool_and.comp (hcap.prod hblocks)

/-- The multi-query wrapper is strict oracle PPT whenever its adversary is strict PPT and
its dimensions and list cap are polynomial-time computable in unary. -/
theorem isOraclePPT_xorHashWordMultiQueryReduction {ℓ blockWidth width Q : ℕ → ℕ}
    {A : ℕ × ℕ → ProbComp (List (List (List Bool)))}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (hb : ComputableInPolyTime blockWidth encUnary encUnary)
    (hw : ComputableInPolyTime width encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hA : IsPPTOn (encPair encUnary encUnary) (encList (encList encBits)) A) :
    IsOraclePPT encBool (xorHashWordMultiQueryReduction ℓ blockWidth width Q A) := by
  let encM := encList encBits
  let encInput := encPair encUnary encBits
  let encStage := encPair encInput (encList encM)
  let encDigests := encList encBits
  have hn := ComputableInPolyTime.fst encUnary encBits
  have hrun := hA.preprocess (hn.prod hn)
  have hn' := hn.comp (ComputableInPolyTime.fst encInput (encList encM))
  have hguesses := ComputableInPolyTime.snd encInput (encList encM)
  have htake := ComputableInPolyTime.listTakeWithInput hguesses (hQ.comp hn')
  have hparam := hn'.comp (ComputableInPolyTime.fst encStage encM)
  have hvalid := polyTime_xorHashWordValid (hℓ.comp hparam) (hb.comp hparam)
    (ComputableInPolyTime.snd encStage encM)
  have hmessages := ComputableInPolyTime.filterWithInput
    (test := fun p : (ℕ × List Bool) × List (List (List Bool)) =>
      xorHashWordValid (ℓ p.1.1) (blockWidth p.1.1)) htake hvalid
  have hargs := ((hℓ.comp hparam).prod (hw.comp hparam)).prod
    (ComputableInPolyTime.snd encStage encM)
  have hhash := isOraclePPTOn_xorHashWordQueries.preprocess hargs
  have htraverse := IsOraclePPTOn.mapM_with_of_bounded_output []
    (program := fun p : (ℕ × List Bool) × List (List (List Bool)) =>
      xorHashWordQueries (ℓ p.1.1) (width p.1.1))
    hmessages hhash (hw.comp hn')
    (fun _ _ _ hout => length_le_of_mem_support_xorHashWordQueries hout)
  have hzip := (ComputableInPolyTime.zip encBits encM).comp
    ((ComputableInPolyTime.snd encStage encDigests).prod
      (hmessages.comp (ComputableInPolyTime.fst encStage encDigests)))
  have htest := (polyTime_hasDistinctCollision encBits encM).comp hzip
  have htail : IsOraclePPTOn encStage encBool
      (fun p : (ℕ × List Bool) × List (List (List Bool)) => do
        let n := p.1.1
        let ms := (p.2.take (Q n)).filter (xorHashWordValid (ℓ n) (blockWidth n))
        let ds ← ms.mapM (xorHashWordQueries (ℓ n) (width n))
        return hasDistinctCollision (ds.zip ms)) := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using htraverse.map_with
      (f := fun (p : (ℕ × List Bool) × List (List (List Bool))) (ds : List (List Bool)) =>
        hasDistinctCollision
        (ds.zip ((p.2.take (Q p.1.1)).filter (xorHashWordValid (ℓ p.1.1) (blockWidth p.1.1)))))
      htest
  exact hrun.isOraclePPTOn.bind_with htail

/-- A strict PPT collision adversary gives a uniform strict PPT word-oracle
distinguisher. The cap and both widths are computed from the unary parameter. -/
theorem isOraclePPT_xorHashWordCollisionReduction {ℓ blockWidth width : ℕ → ℕ}
    {A : ℕ × ℕ → ProbComp (CollisionGuess (List (List Bool)))}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (hb : ComputableInPolyTime blockWidth encUnary encUnary)
    (hw : ComputableInPolyTime width encUnary encUnary)
    (hA : IsPPTOn (encPair encUnary encUnary) (encCollisionGuess (encList encBits)) A) :
    IsOraclePPT encBool (xorHashWordCollisionReduction ℓ blockWidth width A) := by
  let encGuess := encCollisionGuess (encList encBits)
  let encInput := encPair encUnary encBits
  let encStage := encPair encInput encGuess
  have hn := ComputableInPolyTime.fst encUnary encBits
  have hrun := hA.preprocess (hn.prod hn)
  have hn' := hn.comp (ComputableInPolyTime.fst encInput encGuess)
  have hfirst := encCollisionGuess_first_polyTime (encList encBits)
    (ComputableInPolyTime.snd encInput encGuess)
  have hsecond := encCollisionGuess_second_polyTime (encList encBits)
    (ComputableInPolyTime.snd encInput encGuess)
  have hvalid := ComputableInPolyTime.bool_and.comp
    ((polyTime_xorHashWordValid (hℓ.comp hn') (hb.comp hn') hfirst).prod
      (polyTime_xorHashWordValid (hℓ.comp hn') (hb.comp hn') hsecond))
  have hdimensions := (hℓ.comp hn').prod (hw.comp hn')
  have hfirstRun := isOraclePPTOn_xorHashWordQueries.preprocess (hdimensions.prod hfirst)
  have hsecondRun := isOraclePPTOn_xorHashWordQueries.preprocess (hdimensions.prod hsecond)
  have hfst := ComputableInPolyTime.fst encStage encBits
  have hsnd := ComputableInPolyTime.snd encStage encBits
  have hcompare : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × CollisionGuess (List (List Bool))) × List Bool) × List Bool =>
        decide (p.1.1.2.first ≠ p.1.1.2.second ∧ p.1.2 = p.2))
      (encPair (encPair encStage encBits) encBits) encBool := by
    have hout := ComputableInPolyTime.fst (encPair encStage encBits) encBits
    exact ComputableInPolyTime.decide_and
      ((ComputableInPolyTime.decide_ne hfirst hsecond).comp (hfst.comp hout))
      (ComputableInPolyTime.decide_eq' (hsnd.comp hout)
        (ComputableInPolyTime.snd _ _))
  have hboth : IsOraclePPTOn encStage encBool
      (fun p : (ℕ × List Bool) × CollisionGuess (List (List Bool)) => do
        let first ← xorHashWordQueries (ℓ p.1.1) (width p.1.1) p.2.first
        let second ← xorHashWordQueries (ℓ p.1.1) (width p.1.1) p.2.second
        return decide (p.2.first ≠ p.2.second ∧ first = second)) := by
    apply hfirstRun.bind_with
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      (hsecondRun.preprocess hfst).map_with
        (f := fun p second => decide (p.1.2.first ≠ p.1.2.second ∧ p.2 = second)) hcompare
  exact hrun.isOraclePPTOn.bind_with (IsOraclePPTOn.cond hvalid hboth
    (ComputableInPolyTime.const false).isOraclePPTOn)

private def decodeWordMessage (ℓ blockWidth : ℕ) (m : List (List Bool)) :
    {xs : List (BitString blockWidth) // xs.length ≤ ℓ} :=
  ⟨(m.take ℓ).map (BitString.ofList blockWidth), by
    simpa only [List.length_map] using List.length_take_le ℓ m⟩

private theorem decode_encode_xorHashWord {ℓ blockWidth : ℕ}
    {m : List (List Bool)} (hm : xorHashWordValid ℓ blockWidth m = true) :
    (decodeWordMessage ℓ blockWidth m).val.map List.ofFn = m := by
  have hv : m.length ≤ ℓ ∧ ∀ b ∈ m, b.length = blockWidth := by
    simpa only [xorHashWordValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using hm
  simp only [decodeWordMessage, List.take_of_length_le hv.1, List.map_map]
  calc
    _ = m.map id := List.map_congr_left fun b hb => BitString.ofFn_ofList (hv.2 b hb)
    _ = m := List.map_id m

private theorem eq_of_decodeWordMessage_eq {ℓ blockWidth : ℕ} {m m' : List (List Bool)}
    (hm : xorHashWordValid ℓ blockWidth m = true) (hm' : xorHashWordValid ℓ blockWidth m' = true)
    (heq : decodeWordMessage ℓ blockWidth m = decodeWordMessage ℓ blockWidth m') : m = m' :=
  calc
    m = (decodeWordMessage ℓ blockWidth m).val.map List.ofFn :=
      (decode_encode_xorHashWord hm).symm
    _ = (decodeWordMessage ℓ blockWidth m').val.map List.ofFn :=
      congrArg (fun x => x.val.map List.ofFn) heq
    _ = m' := decode_encode_xorHashWord hm'

private theorem run_xorHashWordQueries_of_valid {ℓ blockWidth width : ℕ}
    {m : List (List Bool)} (hm : xorHashWordValid ℓ blockWidth m = true)
    (table : List Bool → BitString width) (oracle : List Bool → List Bool)
    (h : ∀ (b : BitString blockWidth) (i : Fin ℓ),
      oracle (xorHashTaggedWord ℓ (List.ofFn b) i.val) =
        List.ofFn (table (xorHashTaggedWord ℓ (List.ofFn b) i.val))) :
    (xorHashWordQueries ℓ width m).run (fun q => pure (oracle q.2)) =
      pure (List.ofFn (xorHashWordFromTable ℓ blockWidth table m)) := by
  have hrun := run_xorHashWordQueries (decodeWordMessage ℓ blockWidth m) List.ofFn
    (fun (block, i) => table (xorHashTaggedWord ℓ (List.ofFn block) i.val)) oracle h
  rw [decode_encode_xorHashWord hm] at hrun
  exact hrun

/-- With fixed-width matching replies on valid requests, the word reduction checks the
same event as the bounded-block collision game. -/
theorem run_xorHashWordCollisionReduction (ℓ blockWidth width : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (CollisionGuess (List (List Bool)))) (n : ℕ) (aux : List Bool)
    (table : List Bool → BitString (width n)) (oracle : List Bool → List Bool)
    (h : ∀ (b : BitString (blockWidth n)) (i : Fin (ℓ n)),
      oracle (xorHashTaggedWord (ℓ n) (List.ofFn b) i.val) =
        List.ofFn (table (xorHashTaggedWord (ℓ n) (List.ofFn b) i.val))) :
    (xorHashWordCollisionReduction ℓ blockWidth width A n aux).run (fun q => pure (oracle q.2)) =
      (do
        let guess ← A (n, n)
        return decide (guess.first ≠ guess.second ∧
          xorHashWordValid (ℓ n) (blockWidth n) guess.first = true ∧
          xorHashWordValid (ℓ n) (blockWidth n) guess.second = true ∧
          xorHashWordFromTable (ℓ n) (blockWidth n) table guess.first =
            xorHashWordFromTable (ℓ n) (blockWidth n) table guess.second)) := by
  simp only [xorHashWordCollisionReduction, ProbOracleComp.run_bind, ProbOracleComp.run_sample]
  refine bind_congr fun guess => ?_
  by_cases hfirst : xorHashWordValid (ℓ n) (blockWidth n) guess.first = true
  · by_cases hsecond : xorHashWordValid (ℓ n) (blockWidth n) guess.second = true
    · simp [hfirst, hsecond, run_xorHashWordQueries_of_valid hfirst table oracle h,
        run_xorHashWordQueries_of_valid hsecond table oracle h, List.ofFn_injective.eq_iff]
    · simp [hfirst, hsecond]
  · simp [hfirst]

private theorem run_xorHashWordMultiQueryReduction (ℓ blockWidth width Q : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (List (List (List Bool)))) (n : ℕ)
    (table : List Bool → BitString (width n)) (oracle : List Bool → List Bool)
    (h : ∀ (b : BitString (blockWidth n)) (i : Fin (ℓ n)),
      oracle (xorHashTaggedWord (ℓ n) (List.ofFn b) i.val) =
        List.ofFn (table (xorHashTaggedWord (ℓ n) (List.ofFn b) i.val))) :
    (xorHashWordMultiQueryReduction ℓ blockWidth width Q A n []).run
      (fun q => pure (oracle q.2)) = (do
        let gs ← A (n, n)
        let ms := (gs.take (Q n)).filter (xorHashWordValid (ℓ n) (blockWidth n))
        return decide (∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧
          xorHashWordFromTable (ℓ n) (blockWidth n) table m =
            xorHashWordFromTable (ℓ n) (blockWidth n) table m')) := by
  let digest := xorHashWordFromTable (ℓ n) (blockWidth n) table
  have hmap (ms : List (List (List Bool)))
      (hm : ∀ m ∈ ms, xorHashWordValid (ℓ n) (blockWidth n) m = true) :
      (ms.mapM (xorHashWordQueries (ℓ n) (width n))).run (fun q => pure (oracle q.2)) =
        pure (ms.map (List.ofFn ∘ digest)) := by
    induction ms with
    | nil => rfl
    | cons m ms ih =>
      simp only [List.mapM_cons, ProbOracleComp.run_bind, ProbOracleComp.run_pure,
        run_xorHashWordQueries_of_valid (hm m List.mem_cons_self) table oracle h, pure_bind,
        ih (fun m hm' => hm m (List.mem_cons_of_mem _ hm')), List.map_cons,
        Function.comp_def, digest]
  simp only [xorHashWordMultiQueryReduction, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbOracleComp.run_pure]
  refine bind_congr fun gs => ?_
  let ms := (gs.take (Q n)).filter (xorHashWordValid (ℓ n) (blockWidth n))
  rw [hmap ms (fun m hm => (List.mem_filter.mp hm).2), pure_bind, List.zip_map_left,
    List.zip_eq_zipWith, List.zipWith_self]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [hasDistinctCollision, List.map_map, List.any_map, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, decide_eq_true_eq, Function.comp_def, Prod.map_apply, id_eq,
    List.ofFn_injective.eq_iff, and_comm, ms, digest]

private theorem taggedRequest_length {ℓ blockWidth : ℕ} (p : BitString blockWidth × Fin ℓ) :
    (xorHashTaggedWord ℓ (List.ofFn p.1) p.2.val).length = ℓ + blockWidth := by
  rw [length_xorHashTaggedWord p.2.isLt.le, List.length_ofFn]

private theorem prfOracle_xorHashTaggedWord {ℓ blockWidth width : ℕ}
    (family : List Bool → List Bool → List Bool) (key : List Bool)
    (hlength : ∀ req, req.length = ℓ + blockWidth → (family key req).length = width)
    (block : BitString blockWidth) (i : Fin ℓ) :
    let req := xorHashTaggedWord ℓ (List.ofFn block) i.val
    prfOracle family (ℓ + blockWidth) key req =
      List.ofFn (BitString.ofList width (family key req)) := by
  let req := xorHashTaggedWord ℓ (List.ofFn block) i.val
  have hreq : req.length = ℓ + blockWidth := taggedRequest_length (block, i)
  change prfOracle family (ℓ + blockWidth) key req =
    List.ofFn (BitString.ofList width (family key req))
  simp only [prfOracle, hreq, ite_true, BitString.ofFn_ofList (hlength req hreq)]

/-- With the security parameter as public setup, running the reduction in the real PRF game gives
exactly the computational collision game's law. The length hypothesis is the PRF's
declared output-width condition. -/
theorem eval_prfRealGame_xorHashWordCollisionReduction {ℓ blockWidth width : ℕ → ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key query, query.length = ℓ key.length + blockWidth key.length →
      (family key query).length = width key.length)
    (A : ℕ × ℕ → ProbComp (CollisionGuess (List (List Bool)))) (n : ℕ) :
    ProbComp.eval (prfRealGame (fun k => ℓ k + blockWidth k) family
      (xorHashWordCollisionReduction ℓ blockWidth width A) n) =
      collisionGame (fun k => pure k) (fun _ k => xorHashWordValid (ℓ k) (blockWidth k))
        (fun _ => xorHashWordFamily ℓ blockWidth width family) A n := by
  let table (key : BitString n) (req : List Bool) :=
    BitString.ofList (width n) (family (List.ofFn key) req)
  have hreal (key : BitString n) := run_xorHashWordCollisionReduction ℓ blockWidth width
    A n [] (table key) (prfOracle family (ℓ n + blockWidth n) (List.ofFn key))
    (prfOracle_xorHashTaggedWord family (List.ofFn key)
      (by simpa only [List.length_ofFn] using hlength (List.ofFn key)))
  simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList, BitString.uniformList,
    PMF.bind_map, Function.comp_def, hreal, collisionGame, ProbComp.eval_pure,
    Game.withSetup_pure, ProbComp.eval_uniform, table, xorHashWordFamily]
  rw [PMF.bind_comm]
  rfl

/-- For adversaries whose supported lists fit the cap, the real PRF game has the same
law as the full multi-query collision game. Malformed messages are ignored in both games. -/
theorem eval_prfRealGame_xorHashWordMultiQueryReduction {ℓ blockWidth width Q : ℕ → ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key query, query.length = ℓ key.length + blockWidth key.length →
      (family key query).length = width key.length)
    (A : ℕ × ℕ → ProbComp (List (List (List Bool)))) (n : ℕ)
    (hQ : ∀ ms ∈ (ProbComp.eval (A (n, n))).support, ms.length ≤ Q n) :
    ProbComp.eval (prfRealGame (fun k => ℓ k + blockWidth k) family
      (xorHashWordMultiQueryReduction ℓ blockWidth width Q A) n) =
      multiQueryGame (fun k => pure k) (fun _ k => xorHashWordValid (ℓ k) (blockWidth k))
        (fun _ => xorHashWordFamily ℓ blockWidth width family) A n := by
  let table (key : BitString n) (req : List Bool) :=
    BitString.ofList (width n) (family (List.ofFn key) req)
  have hreal (key : BitString n) := run_xorHashWordMultiQueryReduction ℓ blockWidth width Q
    A n (table key) (prfOracle family (ℓ n + blockWidth n) (List.ofFn key))
    (prfOracle_xorHashTaggedWord family (List.ofFn key)
      (by simpa only [List.length_ofFn] using hlength (List.ofFn key)))
  simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList, BitString.uniformList,
    PMF.bind_map, Function.comp_def, hreal, multiQueryGame, ProbComp.eval_pure,
    Game.withSetup_pure, ProbComp.eval_uniform, table, xorHashWordFamily]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ms hms => ?_
  rw [List.take_of_length_le (hQ ms hms)]
  refine congrArg (fun f => (PMF.uniformOfFintype (BitString n)).bind f)
    (funext fun key => congrArg PMF.pure (decide_eq_decide.mpr ?_))
  simp only [List.mem_filter]
  exact ⟨fun ⟨m, ⟨hm, hv⟩, m', ⟨hm', hv'⟩, hne, heq⟩ => ⟨m, hm, m', hm', hne, hv, hv', heq⟩,
    fun ⟨m, hm, m', hm', hne, hv, hv', heq⟩ => ⟨m, ⟨hm, hv⟩, m', ⟨hm', hv'⟩, hne, heq⟩⟩

private def taggedRequestEmbedding (ℓ blockWidth : ℕ) :
    BitString blockWidth × Fin ℓ ↪ BitString (ℓ + blockWidth) where
  toFun p := BitString.ofList (ℓ + blockWidth) (xorHashTaggedWord ℓ (List.ofFn p.1) p.2.val)
  inj' := by
    intro p q hpq
    have hword := congrArg List.ofFn hpq
    change List.ofFn (BitString.ofList _ _) = List.ofFn (BitString.ofList _ _) at hword
    rw [BitString.ofFn_ofList (taggedRequest_length p),
      BitString.ofFn_ofList (taggedRequest_length q)] at hword
    have hpair : (List.ofFn p.1, p.2) = (List.ofFn q.1, q.2) :=
      xorHashTaggedWord_injective ℓ hword
    exact Prod.ext (List.ofFn_injective (congrArg Prod.fst hpair))
      (congrArg (fun v : List Bool × Fin ℓ => v.2) hpair)

private theorem isUniversalHash_taggedRequest (ℓ blockWidth width : ℕ) :
    IsUniversalHash (PMF.uniformOfFintype (BitString (ℓ + blockWidth) → BitString width))
      (fun f m => xorHash (fun p => f (taggedRequestEmbedding ℓ blockWidth p)) m)
      (Fintype.card (BitString width) : ℝ≥0∞)⁻¹ := by
  let seed := PMF.uniformOfFintype (BitString (ℓ + blockWidth) → BitString width)
  let e := taggedRequestEmbedding ℓ blockWidth
  refine IsUniversalHash.precompose_seed seed (fun f p => f (e p)) ?_
  simp only [seed, Probability.PMF.uniformOfFintype_pi_map_comp_embedding e]
  exact isDeltaUniversalHash_xorHash.isUniversalHash

private theorem eval_prfIdealGame_xorHashWordCollisionReduction_le
    (ℓ blockWidth width : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (CollisionGuess (List (List Bool)))) (n : ℕ) :
    ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
      (xorHashWordCollisionReduction ℓ blockWidth width A) n) true ≤
      (Fintype.card (BitString (width n)) : ℝ≥0∞)⁻¹ := by
  have hU := isUniversalHash_taggedRequest (ℓ n) (blockWidth n) (width n)
  have hrun (f : BitString (ℓ n + blockWidth n) → BitString (width n)) :=
    run_xorHashWordCollisionReduction ℓ blockWidth width A n []
      (fun q => f (BitString.ofList (ℓ n + blockWidth n) q))
      (randomFunctionOracle (ℓ n + blockWidth n) f)
      (fun b i => by simp only [randomFunctionOracle, taggedRequest_length (b, i), ite_true])
  simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, hrun, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_apply_le_on_support _ fun guess _ => ?_
  by_cases h₁ : xorHashWordValid (ℓ n) (blockWidth n) guess.first = true
  · by_cases h₂ : xorHashWordValid (ℓ n) (blockWidth n) guess.second = true
    · by_cases hne : guess.first = guess.second
      · simp [hne]
      · let decode := decodeWordMessage (ℓ n) (blockWidth n)
        rw [Probability.PMF.bind_pure_decide_apply_true]
        simp only [ne_eq, hne, not_false_eq_true, h₁, h₂, true_and]
        exact hU (decode guess.first) (decode guess.second)
          fun heq => hne (eq_of_decodeWordMessage_eq h₁ h₂ heq)
    · simp [h₂]
  · simp [h₁]

private theorem eval_prfIdealGame_xorHashWordMultiQueryReduction_le
    (ℓ blockWidth width Q : ℕ → ℕ)
    (A : ℕ × ℕ → ProbComp (List (List (List Bool)))) (n : ℕ) :
    ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
      (xorHashWordMultiQueryReduction ℓ blockWidth width Q A) n) true ≤
      ((Q n).choose 2 : ℕ) * (Fintype.card (BitString (width n)) : ℝ≥0∞)⁻¹ := by
  classical
  have hU := isUniversalHash_taggedRequest (ℓ n) (blockWidth n) (width n)
  let seed := PMF.uniformOfFintype (BitString (ℓ n + blockWidth n) → BitString (width n))
  have hrun (f : BitString (ℓ n + blockWidth n) → BitString (width n)) :=
    run_xorHashWordMultiQueryReduction ℓ blockWidth width Q A n
      (fun q => f (BitString.ofList (ℓ n + blockWidth n) q))
      (randomFunctionOracle (ℓ n + blockWidth n) f)
      (fun b i => by simp only [randomFunctionOracle, taggedRequest_length (b, i), ite_true])
  simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, hrun, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_apply_le_on_support _ fun gs _ => ?_
  rw [Probability.PMF.bind_pure_decide_apply_true]
  let ms := (gs.take (Q n)).filter (xorHashWordValid (ℓ n) (blockWidth n))
  let decode := decodeWordMessage (ℓ n) (blockWidth n)
  let ds := ms.map decode
  refine (seed.toOuterMeasure.mono ?_).trans
    ((hU.toOuterMeasure_not_injOn_le ds.toFinset).trans ?_)
  · intro f ⟨m, hm, m', hm', hne, heq⟩ hinj
    exact hne (eq_of_decodeWordMessage_eq (List.mem_filter.mp hm).2 (List.mem_filter.mp hm').2
      (hinj (List.mem_toFinset.mpr (List.mem_map_of_mem hm))
        (List.mem_toFinset.mpr (List.mem_map_of_mem hm')) heq))
  · gcongr
    refine ds.toFinset_card_le.trans ?_
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The concrete bound (7.12) of Boneh–Shoup v0.6, §7.2.3, p. 261, for the explicit
word distinguisher. The ideal-table contribution is the reciprocal of the digest cardinality. -/
theorem succProbability_xorHashWordFamily_le {ℓ blockWidth width : ℕ → ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key query, query.length = ℓ key.length + blockWidth key.length →
      (family key query).length = width key.length)
    (A : ℕ × ℕ → ProbComp (CollisionGuess (List (List Bool)))) (n : ℕ) :
    Game.succProbability
        (collisionGame (fun k => pure k) (fun _ k => xorHashWordValid (ℓ k) (blockWidth k))
          (fun _ => xorHashWordFamily ℓ blockWidth width family) A n) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame (fun k => ℓ k + blockWidth k) family
          (xorHashWordCollisionReduction ℓ blockWidth width A) n))
        (ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
          (xorHashWordCollisionReduction ℓ blockWidth width A) n)) +
      ((2 : ℝ≥0) ^ width n)⁻¹ := by
  have hideal : Game.succProbability
      (ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
        (xorHashWordCollisionReduction ℓ blockWidth width A) n)) ≤ ((2 : ℝ≥0) ^ width n)⁻¹ := by
    apply ENNReal.coe_le_coe.mp
    rw [Game.coe_succProbability_ennreal, ENNReal.coe_inv (pow_ne_zero _ two_ne_zero),
      ENNReal.coe_pow, ENNReal.coe_ofNat]
    simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
      eval_prfIdealGame_xorHashWordCollisionReduction_le ℓ blockWidth width A n
  rw [← eval_prfRealGame_xorHashWordCollisionReduction family hlength A n]
  let I := ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
    (xorHashWordCollisionReduction ℓ blockWidth width A) n)
  refine (Game.succProbability_le_add_of_advantage_le (g₁ := I) le_rfl).trans ?_
  rw [add_comm (Game.succProbability I)]
  exact add_le_add le_rfl hideal

/-- Boneh–Shoup v0.6, Exercise 7.28, printed p. 285. A `Q`-message adversary's collision success
is at most the advantage of the direct word PRF wrapper plus `Q² / (2 |Y|)`. The wrapper
uses at most `Q * ℓ` calls and is strict oracle PPT for a strict PPT adversary and
unary polynomial-time schedules. Its ideal-table bound counts unordered pairs. -/
theorem succProbability_multiQueryGame_xorHashWordFamily_le
    {ℓ blockWidth width Q : ℕ → ℕ}
    (family : List Bool → List Bool → List Bool)
    (hlength : ∀ key query, query.length = ℓ key.length + blockWidth key.length →
      (family key query).length = width key.length)
    (A : ℕ × ℕ → ProbComp (List (List (List Bool)))) (n : ℕ)
    (hQ : ∀ ms ∈ (ProbComp.eval (A (n, n))).support, ms.length ≤ Q n) :
    Game.succProbability
        (multiQueryGame (fun k => pure k) (fun _ k => xorHashWordValid (ℓ k) (blockWidth k))
          (fun _ => xorHashWordFamily ℓ blockWidth width family) A n) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame (fun k => ℓ k + blockWidth k) family
          (xorHashWordMultiQueryReduction ℓ blockWidth width Q A) n))
        (ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
          (xorHashWordMultiQueryReduction ℓ blockWidth width Q A) n)) +
      ((Q n : ℝ≥0) ^ 2 / 2) * ((2 : ℝ≥0) ^ width n)⁻¹ := by
  let I : Game := ProbComp.eval (prfIdealGame (fun k => ℓ k + blockWidth k) width
    (xorHashWordMultiQueryReduction ℓ blockWidth width Q A) n)
  have hideal : I.succProbability ≤ ((Q n).choose 2 : ℕ) * ((2 : ℝ≥0) ^ width n)⁻¹ := by
    apply ENNReal.coe_le_coe.mp
    rw [Game.coe_succProbability_ennreal, ENNReal.coe_mul, ENNReal.coe_natCast,
      ENNReal.coe_inv (pow_ne_zero _ two_ne_zero), ENNReal.coe_pow, ENNReal.coe_ofNat]
    simpa only [I, BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
      eval_prfIdealGame_xorHashWordMultiQueryReduction_le ℓ blockWidth width Q A n
  have hchoose : ((Q n).choose 2 : ℝ≥0) ≤ (Q n : ℝ≥0) ^ 2 / 2 := by
    simpa using Nat.choose_le_pow_div (α := ℝ≥0) 2 (Q n)
  rw [← eval_prfRealGame_xorHashWordMultiQueryReduction family hlength A n hQ]
  refine (Game.succProbability_le_add_of_advantage_le (g₁ := I) le_rfl).trans ?_
  rw [add_comm I.succProbability]
  refine add_le_add le_rfl (hideal.trans ?_)
  gcongr

/-- Boneh–Shoup v0.6, Theorem 7.6, §7.2.3, printed pp. 261–262, for word PRFs with
`n`-bit keys, fixed-width bit blocks, and a fixed-width unary position prefix. If
the PRF is secure and the digest space has negligible reciprocal cardinality, XOR-hash
is computationally universal against uniform strict PPT collision adversaries. All
dimensions are polynomial-time computable in unary. -/
theorem isComputationalUHF_xorHashWordFamily {ℓ blockWidth width : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool}
    (hPRF : PseudorandomFunctionOver (fun n => ℓ n + blockWidth n) width family)
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (hb : ComputableInPolyTime blockWidth encUnary encUnary)
    (hout : Negligible (fun n => ((2 : ℝ≥0) ^ width n)⁻¹)) :
    IsComputationalUHF encUnary (encList encBits) (fun n => pure n)
      (fun _ n => xorHashWordValid (ℓ n) (blockWidth n))
      (fun _ => xorHashWordFamily ℓ blockWidth width family) := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro A hA
  have hinput : ComputableInPolyTime (fun n => ℓ n + blockWidth n) encUnary encUnary := by
    fun_prop
  have hw := hPRF.outLen_polyTime hinput
  have hred := isOraclePPT_xorHashWordCollisionReduction hℓ hb hw hA
  apply negligible_of_le ((hPRF.secure _ hred).add hout)
  exact succProbability_xorHashWordFamily_le family hPRF.length_eq A

end Cslib.Crypto.UHF
