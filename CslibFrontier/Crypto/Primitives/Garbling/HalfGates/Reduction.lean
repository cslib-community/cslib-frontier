/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Simulator
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Uniform
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime

/-!
# The CCR reduction for the privacy of half-gates garbling

The `prv.sim` advantage of an adversary `B` against the simulator `simWord` of
`HalfGates.scheme hash`, with the side information `Φ_circ`, is exactly the circular correlation
robustness advantage of an explicit, certified reduction `prvSimReduction hash B`, at every
parameter `k` where every circuit `B` can choose has `2 q ≤ 2 ^ k` (`prvSimAdvantage_simWord_eq`).

The reduction follows the hybrid `G₁^O` of the proof of Theorem 1 of Zahur, Rosulek and Evans
[ZahurRosulekEvans2015] (Fig. 3, p. 13), on words and with this library's tweaks, and hands its
view to `B`. It runs `B`'s choice of a query `(f, x)`. When `x` has `f.n` bits and
`2 q ≤ 2 ^ k`, it samples the labels the evaluator holds on the inputs and walks the gates in
order, knowing the value `v` of every wire from `x`. An XOR gate adds its argument labels `a` and
`b`. An AND gate asks its oracle `(a, t, col(b) ⊕ v_b)` and `(b, t', v_a)`, at the tweaks `t`
and `t'` of its two slots, and adds the parts of the two ciphertexts the evaluator can compute:
`TG = H(a, t) ⊕ O(a, t, col(b) ⊕ v_b)` and `TE = H(b, t') ⊕ a ⊕ O(b, t', v_a)`; its label is
the evaluator's AND gate on them. Each query is asked once the labels it reads are known, so
later queries depend on earlier answers. The reduction then runs `B`'s guess on the view
`(F, X, d)` with these ciphertexts, the input labels and, for each output, the colour of its
label plus its value. Otherwise it runs `B`'s guess on `⊥` without querying: on an invalid query,
as the `prv.sim` game does, and when `2 q > 2 ^ k`, where the `k`-bit tweaks of distinct slots
could coincide.

Against every fixed oracle the reduction runs the typed reduction `HalfGates.reduction` of
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Privacy` on `toCircuit f`, with `B`'s guess on
the words of the view. So, averaged over `B`'s choice, its circular game is the real `prv.sim`
experiment by `HalfGates.realGame_reduction`, and its random-function game is the simulated one
by `HalfGates.simGame_reduction`, since distinct slots have distinct tweaks while `2 q ≤ 2 ^ k`.
The reduction asks every tweak at most once on every run, at every level, which is the legality
condition of `CircularCorrelationRobust` (`isTweakUnique_prvSimReduction`), and it is uniform
strict oracle PPT for every adversary certified by `TwoStage.IsPPT` and every hash computed in
polynomial time (`isOraclePPT_prvSimReduction`).

## Main definitions

* `Cslib.Crypto.Garbling.HalfGates.prvSimReduction`: the CCR reduction.

## Main results

* `Cslib.Crypto.Garbling.HalfGates.isTweakUnique_prvSimReduction`: the reduction is legal.
* `Cslib.Crypto.Garbling.HalfGates.prvSimAdvantage_simWord_eq`: the `prv.sim` advantage is the
  reduction's CCR advantage.
* `Cslib.Crypto.Garbling.HalfGates.isOraclePPT_prvSimReduction`: the reduction is oracle PPT.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.HalfGates

open Cslib.Circuits Probability

/-! ### The reduction -/

section Words

/-- The data that the gate loop of the reduction reads. -/
private structure GateLoopData where
  /-- The parameter `k`: labels have `k + 2` bits and tweaks `k` bits. -/
  param : ℕ
  /-- The number `n` of inputs of the circuit. -/
  inputCount : ℕ
  /-- The data `(A, B, table)` of the gates of the circuit, in order. -/
  gates : List (ℕ × ℕ × List Bool)
  /-- The plaintext values of all wires of the circuit on the chosen input. -/
  wireValues : List Bool

/-- The state of the gate loop of the reduction. -/
private structure GateLoopState where
  /-- The words of the labels that the evaluator holds on the wires so far. -/
  labels : List (List Bool)
  /-- The ciphertext block of each gate so far. -/
  blocks : List (List Bool)

variable (hash : List Bool → List Bool → List Bool)

/-- The data `(A, B, table)` of the next gate after the labels `labels`, gate `|labels| - n`. -/
private def nextGate (d : GateLoopData) (labels : List (List Bool)) : ℕ × ℕ × List Bool :=
  d.gates.getD (labels.length - d.inputCount) (0, 0, [])

/-- The 0-indexed first argument wire of the next gate, capped at the labels so far. -/
private def leftArg (d : GateLoopData) (labels : List (List Bool)) : ℕ :=
  min (labels.length + 1) (nextGate d labels).1 - 1

/-- The 0-indexed second argument wire of the next gate, capped at the labels so far. -/
private def rightArg (d : GateLoopData) (labels : List (List Bool)) : ℕ :=
  min (labels.length + 1) (nextGate d labels).2.1 - 1

/-- The state after AND gate `g` with argument labels `a` and `b`, from the oracle's replies
`rG` and `rE`: the ciphertexts are `TG = H(a, t) ⊕ rG` and `TE = H(b, t') ⊕ a ⊕ rE`, the label is
the evaluator's AND gate on them, and the block is `TG ‖ TE`. -/
private def andState (k g : ℕ) (a b rG rE : List Bool) (st : GateLoopState) : GateLoopState :=
  let tg := List.zipWith xor (hashWord hash k a (tweakWord k g false)) rG
  let te := List.zipWith xor (List.zipWith xor (hashWord hash k b (tweakWord k g true)) a) rE
  ⟨st.labels ++ [andWord hash k g tg te a b], st.blocks ++ [tg ++ te]⟩

/-- One gate of the reduction on the loop data `d`. Gate `g = |labels| - n` reads the labels `a`
and `b` of its argument wires `i` and `j`. An AND gate asks the oracle `(a, t, col(b) ⊕ v_j)` and
`(b, t', v_i)` at the tweaks `t`, `t'` of its two slots, keeps the first `k + 2` bits of each
reply, and continues with `andState`. An XOR gate appends the sum of its argument labels, cut to
`k + 2` bits, and an empty block. -/
private def reductionStep (d : GateLoopData) (st : GateLoopState) :
    WordOracleComp Unit GateLoopState :=
  if (nextGate d st.labels).2.2.getD 3 false then do
    let rG ← List.take (d.param + 2) <$> ProbOracleComp.query
      (spec := fun _ : Unit × List Bool => List Bool)
      ((), st.labels.getD (leftArg d st.labels) [] ++
        (tweakWord d.param (st.labels.length - d.inputCount) false ++
          [colourWord d.param (st.labels.getD (rightArg d st.labels) []) ^^
            d.wireValues.getD (rightArg d st.labels) false]))
    let rE ← List.take (d.param + 2) <$> ProbOracleComp.query
      (spec := fun _ : Unit × List Bool => List Bool)
      ((), st.labels.getD (rightArg d st.labels) [] ++
        (tweakWord d.param (st.labels.length - d.inputCount) true ++
          [d.wireValues.getD (leftArg d st.labels) false]))
    pure (andState hash d.param (st.labels.length - d.inputCount)
      (st.labels.getD (leftArg d st.labels) []) (st.labels.getD (rightArg d st.labels) []) rG rE st)
  else pure ⟨st.labels ++ [(List.zipWith xor (st.labels.getD (leftArg d st.labels) [])
      (st.labels.getD (rightArg d st.labels) [])).take (d.param + 2)], st.blocks ++ [[]]⟩

/-- Row `i` of gate `g` of the reduction's garbled function in the layout of
`PointPermute.bodyWith`: row `0` is the AND bit, row `1` the gate's ciphertext block, and the
other rows are empty. -/
private def ctRow (blocks : List (List Bool)) (isAnd : Bool) (g i : ℕ) : List Bool :=
  if i = 0 then [isAnd] else if i = 1 then blocks.getD g [] else []

/-- The view `(F, X, d)` the reduction writes at parameter `k` for the circuit `f`, from its
plaintext wire values `ws`, the coins of the input labels and the final state of its gate loop:
`F` has the header and gates of `f` with the blocks as ciphertexts, `X` lists the input labels,
and the decoding bit of each output is the colour of its label plus its value. -/
private def reductionView (k : ℕ) (f : ConventionalCircuit) (ws coins : List Bool)
    (st : GateLoopState) : PrvView where
  fn := PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
    PointPermute.bodyWith f.n f.gateList.length 0 (fun g => (f.gateList.getD g (0, 0, [])).1)
      (fun g => (f.gateList.getD g (0, 0, [])).2.1)
      (fun g _ _ i => ctRow st.blocks ((f.gateList.getD g (0, 0, [])).2.2.getD 3 false) g i))
  input := ((List.range f.n).map fun i => BitString.listRow (k + 2) i coins).flatten
  decInfo := (List.range f.m).map fun o =>
    colourWord k (st.labels.getD (f.n + f.gateList.length - f.m + o) []) ^^
      ws.getD (f.n + f.gateList.length - f.m + o) false

/-- **The CCR reduction** for a `prv.sim` adversary `B` against half-gates garbling, at parameter
`k`: run `B`'s choice of a query `(f, x)`. When `x` has `f.n` bits and `2 q ≤ 2 ^ k`, sample the
input labels, build the ciphertexts gate by gate with the oracle and run `B`'s guess on the
resulting view; otherwise run `B`'s guess on `⊥` without querying. -/
noncomputable def prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary XorAndCircuit σ) :
    OracleDistinguisher :=
  fun k _ => do
    let (query, state) ← ProbOracleComp.sample ((B k).choose ())
    if query.input.length = query.fn.circuit.n ∧ 2 * query.fn.circuit.q ≤ 2 ^ k then do
      let coins ← ProbOracleComp.sample (BitString.sampleList (query.fn.circuit.n * (k + 2)))
      let st ← OracleComp.iterate query.fn.circuit.q
        (reductionStep hash ⟨k, query.fn.circuit.n, query.fn.circuit.gateList,
          query.fn.circuit.wires query.input query.fn.circuit.q⟩)
        ⟨BitString.listRows query.fn.circuit.n (k + 2) coins, []⟩
      ProbOracleComp.sample ((B k).guess state (some (reductionView k query.fn.circuit
        (query.fn.circuit.wires query.input query.fn.circuit.q) coins st)))
    else ProbOracleComp.sample ((B k).guess state none)

end Words

/-! ### Legality -/

section Legality

variable (hash : List Bool → List Bool → List Bool)

/-- A request at the tweak of slot `b` of gate `g` costs at most one, and only when that tweak is
`t`. -/
private theorem tweakCost_request_le (k : ℕ) (t : BitString k) (a : List Bool) (g : ℕ)
    (b c : Bool) :
    CCR.tweakCost k t ((), a ++ (tweakWord k g b ++ [c])) ≤
      if tweakWord k g b = List.ofFn t then 1 else 0 := by
  unfold CCR.tweakCost
  split_ifs with h₁ h₂ <;> try omega
  obtain ⟨hlen, htw⟩ := h₁
  have ha : a.length = k + 2 := by
    simp only [List.length_append, length_tweakWord, List.length_singleton] at hlen
    omega
  rw [List.drop_left' ha, List.take_left' (length_tweakWord k g b)] at htw
  exact absurd htw h₂

/-- One gate of the reduction asks at the tweaks of the two slots of gate `|labels| - n`, and
only there. -/
private theorem isCostBounded_reductionStep (k n : ℕ) (gates : List (ℕ × ℕ × List Bool))
    (ws : List Bool) (t : BitString k) (st : GateLoopState) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (CCR.tweakCost k t))
      (reductionStep hash ⟨k, n, gates, ws⟩ st)
      ((if tweakWord k (st.labels.length - n) false = List.ofFn t then 1 else 0) +
        (if tweakWord k (st.labels.length - n) true = List.ofFn t then 1 else 0)) := by
  unfold reductionStep
  dsimp only
  split
  · refine (((OracleComp.isCostBounded_map_iff _ _ _).mpr
      (ProbOracleComp.isCostBounded_query _ _)).bind fun _ =>
        ((OracleComp.isCostBounded_map_iff _ _ _).mpr
          (ProbOracleComp.isCostBounded_query _ _)).bind fun _ =>
            OracleComp.IsCostBounded.pure _ 0).mono ?_
    have h₁ := tweakCost_request_le k t (st.labels.getD (leftArg ⟨k, n, gates, ws⟩ st.labels) [])
      (st.labels.length - n) false
      (colourWord k (st.labels.getD (rightArg ⟨k, n, gates, ws⟩ st.labels) []) ^^
        ws.getD (rightArg ⟨k, n, gates, ws⟩ st.labels) false)
    have h₂ := tweakCost_request_le k t (st.labels.getD (rightArg ⟨k, n, gates, ws⟩ st.labels) [])
      (st.labels.length - n) true (ws.getD (leftArg ⟨k, n, gates, ws⟩ st.labels) false)
    omega
  · exact OracleComp.IsCostBounded.pure _ _

/-- Every possible step appends one label of at most `k + 2` bits and one block of at most
`2 (k + 2)` bits. -/
private theorem exists_of_mem_support_reductionStep {d : GateLoopData} {st next : GateLoopState}
    (hnext : next ∈ (reductionStep hash d st).support) :
    ∃ label block, next = ⟨st.labels ++ [label], st.blocks ++ [block]⟩ ∧
      label.length ≤ d.param + 2 ∧ block.length ≤ 2 * (d.param + 2) := by
  unfold reductionStep at hnext
  split at hnext
  · obtain ⟨rG, -, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
    obtain ⟨rE, -, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
    rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    refine ⟨_, _, rfl, length_andWord_le hash _ _ _ _ _ _, ?_⟩
    simp only [List.length_append, List.length_zipWith, length_hashWord]
    omega
  · rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    exact ⟨_, _, rfl, by simp, by simp⟩

/-- The tweak budget of the first `c` gates, while `2 c ≤ 2 ^ k`: each of the `k`-bit tweaks
`lowBits k j`, `j < 2 c`, is asked at most once. -/
private theorem isCostBounded_iterate_reductionStep (k n : ℕ)
    (gates : List (ℕ × ℕ × List Bool)) (ws : List Bool) (t : BitString k)
    (init : GateLoopState) (hinit : init.labels.length = n) (c : ℕ) (hc : 2 * c ≤ 2 ^ k) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (CCR.tweakCost k t))
      (OracleComp.iterate c (reductionStep hash ⟨k, n, gates, ws⟩) init)
      (if ∃ j < 2 * c, BitString.lowBits k j = List.ofFn t then 1 else 0) ∧
    ∀ st ∈ (OracleComp.iterate c (reductionStep hash ⟨k, n, gates, ws⟩) init).support,
      st.labels.length = n + c := by
  induction c with
  | zero =>
    refine ⟨OracleComp.IsCostBounded.pure _ _, fun st hst => ?_⟩
    rw [OracleComp.iterate_zero] at hst
    rw [OracleComp.eq_of_mem_supportWith_pure hst]
    exact hinit
  | succ c ih =>
    obtain ⟨hcost, hlen⟩ := ih (by omega)
    rw [OracleComp.iterate_succ]
    refine ⟨(hcost.bind_on_support (m := (if tweakWord k c false = List.ofFn t then 1 else 0) +
      (if tweakWord k c true = List.ofFn t then 1 else 0)) fun st hst => ?_).mono ?_,
      fun st hst => ?_⟩
    · have h := isCostBounded_reductionStep hash k n gates ws t st
      rwa [hlen st hst, Nat.add_sub_cancel_left] at h
    · simp only [tweakWord, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
      by_cases hB : ∃ j < 2 * (c + 1), BitString.lowBits k j = List.ofFn t
      · have ⟨j, hj, hjt⟩ := hB
        have huniq {m : ℕ} (hm : m < 2 * (c + 1)) (hmt : BitString.lowBits k m = List.ofFn t) :
            m = j := BitString.lowBits_injective_of_lt (by omega) (by omega) (hmt.trans hjt.symm)
        have hA' : (∃ i < 2 * c, BitString.lowBits k i = List.ofFn t) ↔ j < 2 * c :=
          ⟨fun ⟨i, hi, hit⟩ => huniq (by omega) hit ▸ hi, fun hj' => ⟨j, hj', hjt⟩⟩
        have h₀' : BitString.lowBits k (2 * c) = List.ofFn t ↔ 2 * c = j :=
          ⟨huniq (by omega), fun h => h ▸ hjt⟩
        have h₁' : BitString.lowBits k (2 * c + 1) = List.ofFn t ↔ 2 * c + 1 = j :=
          ⟨huniq (by omega), fun h => h ▸ hjt⟩
        simp only [hB, hA', h₀', h₁', ↓reduceIte]
        split_ifs <;> omega
      · have hA : ¬∃ j < 2 * c, BitString.lowBits k j = List.ofFn t :=
          fun ⟨j, hj, h⟩ => hB ⟨j, by omega, h⟩
        have h₀ : ¬BitString.lowBits k (2 * c) = List.ofFn t := fun h => hB ⟨2 * c, by omega, h⟩
        have h₁ : ¬BitString.lowBits k (2 * c + 1) = List.ofFn t :=
          fun h => hB ⟨2 * c + 1, by omega, h⟩
        simp only [hB, hA, h₀, h₁, ↓reduceIte, le_rfl]
    · obtain ⟨st', hst', hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hst
      obtain ⟨label, block, rfl, -, -⟩ := exists_of_mem_support_reductionStep hash hnext
      simp only [List.length_append, List.length_singleton, hlen st' hst']
      omega

/-- **The reduction is legal at every level.** At every level `k`, the reduction for `B`, read
through `CCR.codec k`, asks each tweak at most once on every run: it asks only when
`2 q ≤ 2 ^ k`, and then at the tweaks `2 g + s` of distinct slots, which are distinct below
`2 ^ k`. -/
theorem isTweakUnique_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary XorAndCircuit σ)
    (k : ℕ) : CCR.IsTweakUnique ((CCR.codec k).adapt (prvSimReduction hash B k [])) := by
  intro t
  refine (CCR.codec k).isCostBounded_adapt (wordCost := CCR.tweakCost k t)
    (CCR.tweakCost_encodeQuery k t) ?_
  refine ((ProbOracleComp.isCostBounded_sample _ _).bind (m := 1) fun ⟨query, state⟩ => ?_).mono
    (by omega)
  dsimp only
  split_ifs with hguard
  · refine ((ProbOracleComp.isCostBounded_sample _ _).bind fun coins =>
      ((isCostBounded_iterate_reductionStep hash k _ _ _ t _ (by simp) _ hguard.2).1.bind
        fun st => ProbOracleComp.isCostBounded_sample _ _)).mono ?_
    split_ifs <;> omega
  · exact (ProbOracleComp.isCostBounded_sample _ _).mono (by omega)

end Legality

/-! ### Against every oracle the reduction runs the typed reduction -/

section Run

variable (hash : List Bool → List Bool → List Bool) (k : ℕ) (f : XorAndCircuit)

/-- The words of the labels of the first `n + s` wires of `toCircuit f` under the labelling
`E`. -/
private noncomputable def labelsUpTo
    (E : Wire f.circuit.n (toCircuit f).size → BitString (k + 1) × Bool) (s : ℕ) :
    List (List Bool) :=
  (List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
    labelBits (E (Wire.ofNat v v.isLt))).take (f.circuit.n + s)

/-- The ciphertext block of gate `g` of the table `T` over `toCircuit f`: the words of its two
ciphertexts for an AND gate, nothing for an XOR gate. -/
private noncomputable def ctBlock (T : Slot (toCircuit f) → BitString (k + 1) × Bool)
    (g : Fin (toCircuit f).size) : List Bool :=
  if h : op (toCircuit f) g = .and then
    labelBits (T (⟨g, h⟩, false)) ++ labelBits (T (⟨g, h⟩, true))
  else []

/-- The ciphertext blocks of the first `s` gates of the table `T`. -/
private noncomputable def blocksUpTo (T : Slot (toCircuit f) → BitString (k + 1) × Bool)
    (s : ℕ) : List (List Bool) :=
  (List.ofFn (ctBlock k f T)).take s

variable {hash k f}

/-- **One gate of the reduction against a fixed oracle.** When the labelling `E` is fixed by one
evaluation round of the table `T`, and `T` is the typed reduction's entry with oracle `O` on the
labels `E`, one step of the word reduction from the words of the first `n + s` labels and `s`
blocks appends the word of the label and the block of gate `s`. -/
private theorem run_reductionStep {x : List Bool} (hx : x.length = f.circuit.n)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool)
    {X : Fin f.circuit.n → BitString (k + 1) × Bool}
    {E : Wire f.circuit.n (toCircuit f).size → BitString (k + 1) × Bool}
    {T : Slot (toCircuit f) → BitString (k + 1) × Bool}
    (hE : evalStep (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) T X E = E)
    (hT : T = entry (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
      (BitString.ofList f.circuit.n x) O E)
    {s : ℕ} (hs : s < f.circuit.q) :
    ProbOracleComp.run (reductionStep hash ⟨k, f.circuit.n, f.circuit.gateList,
        f.circuit.wires x f.circuit.q⟩ ⟨labelsUpTo k f E s, blocksUpTo k f T s⟩)
        ((CCR.codec k).wordOracle fun q => pure (O q)) =
      pure ⟨labelsUpTo k f E (s + 1), blocksUpTo k f T (s + 1)⟩ := by
  have hsize := size_toCircuit f
  set g : Fin (toCircuit f).size := ⟨s, by omega⟩ with hg
  have hgs : (g : ℕ) = s := rfl
  have hgcast : g.cast (size_toCircuit f) = ⟨s, hs⟩ := Fin.ext rfl
  have hA₁ := f.isValid.one_le_A ⟨s, hs⟩
  have hAB := f.isValid.A_lt_B ⟨s, hs⟩
  have hBg := f.isValid.B_lt_gate ⟨s, hs⟩
  simp only [ConventionalCircuit.topo] at hA₁ hAB hBg
  have hl := toNat_left_lt (toCircuit f) g
  have hr := toNat_right_lt (toCircuit f) g
  have hlen : (labelsUpTo k f E s).length = f.circuit.n + s := by
    simp only [labelsUpTo, List.length_take, List.length_ofFn]
    omega
  have hnext : nextGate ⟨k, f.circuit.n, f.circuit.gateList, f.circuit.wires x f.circuit.q⟩
      (labelsUpTo k f E s) =
      (f.circuit.A ⟨s, hs⟩, f.circuit.B ⟨s, hs⟩, [f.circuit.G ⟨s, hs⟩ false false,
        f.circuit.G ⟨s, hs⟩ false true, f.circuit.G ⟨s, hs⟩ true false,
        f.circuit.G ⟨s, hs⟩ true true]) := by
    simp [nextGate, hlen, ConventionalCircuit.gateList, List.getD_eq_getElem?_getD, hs]
  have hleft : leftArg ⟨k, f.circuit.n, f.circuit.gateList, f.circuit.wires x f.circuit.q⟩
      (labelsUpTo k f E s) =
      (left (toCircuit f) g).toNat := by
    rw [leftArg, hnext, hlen, toNat_left_toCircuit, hgcast]
    dsimp only
    omega
  have hright : rightArg ⟨k, f.circuit.n, f.circuit.gateList, f.circuit.wires x f.circuit.q⟩
      (labelsUpTo k f E s) =
      (right (toCircuit f) g).toNat := by
    rw [rightArg, hnext, hlen, toNat_right_toCircuit, hgcast]
    dsimp only
    omega
  have hlabel (w : Wire f.circuit.n (toCircuit f).size) (hw : w.toNat < f.circuit.n + s) :
      (labelsUpTo k f E s).getD w.toNat [] = labelBits (E w) := by
    rw [labelsUpTo, getD_take_labels E hw (by omega), Wire.ofNat_toNat]
  have hv (w : Wire f.circuit.n (toCircuit f).size) :
      (f.circuit.wires x f.circuit.q).getD w.toNat false =
        (toCircuit f).program.trace interpretation (BitString.ofList f.circuit.n x) w := by
    rw [trace_toCircuit, BitString.ofFn_ofList hx]
  have hlabels : labelsUpTo k f E (s + 1) = labelsUpTo k f E s ++ [labelBits (E (.gate g))] := by
    have hgate : (Wire.ofNat (f.circuit.n + s) (by omega) :
        Wire f.circuit.n (toCircuit f).size) = .gate g := Wire.toNat_injective (by simp [hg])
    rw [labelsUpTo, labelsUpTo, ← Nat.add_assoc, List.take_add_one, List.getElem?_ofFn]
    simp only [show f.circuit.n + s < f.circuit.n + (toCircuit f).size by omega, dite_true,
      Option.toList_some, hgate]
  have hblocks : blocksUpTo k f T (s + 1) = blocksUpTo k f T s ++ [ctBlock k f T g] := by
    rw [blocksUpTo, blocksUpTo, List.take_add_one, List.getElem?_ofFn]
    simp only [show s < (toCircuit f).size by omega, dite_true, Option.toList_some]
    rfl
  have hEg := congrFun hE (.gate g)
  have hand : op (toCircuit f) g = .and ↔ f.circuit.G ⟨s, hs⟩ true true = true := by
    rw [op_toCircuit, hgcast, opOf]
    cases f.circuit.G ⟨s, hs⟩ true true <;> simp
  simp only [reductionStep, hnext, hlen, Nat.add_sub_cancel_left, hleft, hright,
    hlabel _ (show (left (toCircuit f) g).toNat < f.circuit.n + s by rw [← hgs]; omega),
    hlabel _ (show (right (toCircuit f) g).toNat < f.circuit.n + s by rw [← hgs]; omega), hv,
    List.getD_cons_succ, List.getD_cons_zero]
  have htake (y : BitString (k + 1) × Bool) : (labelBits y).take (k + 2) = labelBits y :=
    List.take_of_length_le (by simp)
  rw [hlabels, hblocks]
  by_cases hG : f.circuit.G ⟨s, hs⟩ true true = true
  · have hop : op (toCircuit f) g = .and := hand.mpr hG
    have ht₁ : List.ofFn (slotTweak (toCircuit f) k (⟨g, hop⟩, false)) = tweakWord k s false :=
      ofFn_slotTweak _ k g hop false
    have ht₂ : List.ofFn (slotTweak (toCircuit f) k (⟨g, hop⟩, true)) = tweakWord k s true :=
      ofFn_slotTweak _ k g hop true
    have hq₁ : (CCR.codec k).encodeQuery (slotQuery (toCircuit f) (slotTweak _ k)
        (BitString.ofList f.circuit.n x) E (⟨g, hop⟩, false)) =
        ((), labelBits (E (left (toCircuit f) g)) ++ (tweakWord k s false ++
          [colourWord k (labelBits (E (right (toCircuit f) g))) ^^
            (toCircuit f).program.trace interpretation (BitString.ofList f.circuit.n x)
              (right (toCircuit f) g)])) := by
      simp only [slotQuery, Bool.false_eq_true, ↓reduceIte, Bool.add_eq_xor,
        colourWord_labelBits, ← ht₁]
      rfl
    have hq₂ : (CCR.codec k).encodeQuery (slotQuery (toCircuit f) (slotTweak _ k)
        (BitString.ofList f.circuit.n x) E (⟨g, hop⟩, true)) =
        ((), labelBits (E (right (toCircuit f) g)) ++ (tweakWord k s true ++
          [(toCircuit f).program.trace interpretation (BitString.ofList f.circuit.n x)
            (left (toCircuit f) g)])) := by
      simp only [slotQuery, ↓reduceIte, ← ht₂]
      rfl
    have hTG : List.zipWith xor (hashWord hash k (labelBits (E (left (toCircuit f) g)))
        (tweakWord k s false)) (labelBits (O (slotQuery (toCircuit f) (slotTweak _ k)
          (BitString.ofList f.circuit.n x) E (⟨g, hop⟩, false)))) =
        labelBits (T (⟨g, hop⟩, false)) := by
      simp only [hT, entry, slotKnown, Bool.false_eq_true, ↓reduceIte, labelBits_add,
        labelBits_atLevel, ht₁]
    have hTE : List.zipWith xor (List.zipWith xor (hashWord hash k
        (labelBits (E (right (toCircuit f) g))) (tweakWord k s true))
          (labelBits (E (left (toCircuit f) g))))
        (labelBits (O (slotQuery (toCircuit f) (slotTweak _ k)
          (BitString.ofList f.circuit.n x) E (⟨g, hop⟩, true)))) =
        labelBits (T (⟨g, hop⟩, true)) := by
      simp only [hT, entry, slotKnown, ↓reduceIte, labelBits_add, labelBits_atLevel, ht₂]
    rw [ite_eq_left hG, ← hq₁, ← hq₂]
    simp only [ProbOracleComp.run_bind, ProbOracleComp.run_map, ProbOracleComp.run_query,
      CCR.wordOracle_codec_encodeQuery, map_pure, pure_bind, ProbOracleComp.run_pure, htake]
    simp only [andState, hTG, hTE, ctBlock, dite_eq_left hop]
    rw [← labelBits_andEval hash k s ht₁ ht₂, ← hEg]
    simp only [evalStep, dite_eq_left hop]
  · have hop : ¬ op (toCircuit f) g = .and := fun h => hG (hand.mp h)
    rw [ite_eq_right hG]
    simp only [ProbOracleComp.run_pure, ctBlock, dite_eq_right hop]
    rw [← labelBits_add, htake, ← hEg]
    simp only [evalStep, dite_eq_right hop]

/-- **The gate loop against a fixed oracle.** Under the hypotheses of `run_reductionStep`, with
`X` the input labels read from `coins`, the first `s` steps of the word reduction from the input
label words write the words of the first `n + s` labels and the first `s` blocks. -/
private theorem run_iterate_reductionStep {x : List Bool} (hx : x.length = f.circuit.n)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool)
    (coins : List Bool)
    {E : Wire f.circuit.n (toCircuit f).size → BitString (k + 1) × Bool}
    {T : Slot (toCircuit f) → BitString (k + 1) × Bool}
    (hE : evalStep (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) T
      (fun i => labelOfWord k (BitString.listRow (k + 2) i coins)) E = E)
    (hT : T = entry (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
      (BitString.ofList f.circuit.n x) O E)
    {s : ℕ} (hs : s ≤ f.circuit.q) :
    ProbOracleComp.run (OracleComp.iterate s (reductionStep hash ⟨k, f.circuit.n,
        f.circuit.gateList, f.circuit.wires x f.circuit.q⟩)
        ⟨BitString.listRows f.circuit.n (k + 2) coins, []⟩)
        ((CCR.codec k).wordOracle fun q => pure (O q)) =
      pure ⟨labelsUpTo k f E s, blocksUpTo k f T s⟩ := by
  induction s with
  | zero =>
    rw [OracleComp.iterate_zero, ProbOracleComp.run_pure]
    congr 2
    apply List.ext_getElem (by simp [labelsUpTo])
    intro i h₁ h₂
    simp only [BitString.length_listRows] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.circuit.n (toCircuit f).size) =
        .input ⟨i, h₁⟩ := Wire.toNat_injective (by simp)
    have hEi := congrFun hE (.input ⟨i, h₁⟩)
    simp only [evalStep] at hEi
    simp only [labelsUpTo, BitString.listRows, List.getElem_map, List.getElem_range,
      List.getElem_take, List.getElem_ofFn, Nat.add_zero, hin, ← hEi,
      labelBits_labelOfWord (BitString.length_listRow _ _ _)]
  | succ s ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih (by omega), pure_bind,
      run_reductionStep hx O hE hT (by omega)]

/-- Gate `g` of the typed garbled table `T`, as a word, is the gate of the reduction's garbled
function, with the blocks of `T` as ciphertexts. -/
private theorem encodeGate_eq_ctRow (T : Slot (toCircuit f) → BitString (k + 1) × Bool)
    (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size) (toCircuit f) T g =
      BitString.lowBits (PointPermute.wireWidth f.circuit.n f.circuit.q)
          (f.circuit.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (PointPermute.wireWidth f.circuit.n f.circuit.q)
          (f.circuit.B (g.cast (size_toCircuit f))) ++
        (List.ofFn fun i : Fin 4 => ctRow (blocksUpTo k f T f.circuit.q)
          (f.circuit.G (g.cast (size_toCircuit f)) true true) (g.cast (size_toCircuit f))
            i).flatten := by
  have hblock : (blocksUpTo k f T f.circuit.q).getD (g.cast (size_toCircuit f)) [] =
      ctBlock k f T g := by
    rw [blocksUpTo, List.take_of_length_le (by simp [size_toCircuit]),
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  rw [encodeGate_toCircuit]
  simp only [List.ofFn_succ, List.ofFn_zero, ctRow, Fin.val_zero, Fin.val_succ, hblock, ctBlock]
  simp

/-- **The reduction's view is a typed simulated view.** When `E` is the labelling that the table
`T` gives the evaluator holding the input labels `X` read from `coins`, the view the reduction
writes from the words of all labels and blocks is the words of the typed simulated view with
input labels `X`, table `T` and the output of `toCircuit f` on `x`. -/
private theorem reductionView_eq {x : List Bool} (hx : x.length = f.circuit.n)
    (coins : List Bool) {E : Wire f.circuit.n (toCircuit f).size → BitString (k + 1) × Bool}
    {T : Slot (toCircuit f) → BitString (k + 1) × Bool}
    (hE : evalLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) T
      (fun i => labelOfWord k (BitString.listRow (k + 2) i coins)) = E) :
    reductionView k f.circuit (f.circuit.wires x f.circuit.q) coins
        ⟨labelsUpTo k f E f.circuit.q, blocksUpTo k f T f.circuit.q⟩ =
      viewWord k (toCircuit f) (simulateWith (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
        ((toCircuit f).eval interpretation (BitString.ofList f.circuit.n x))
        (fun i => labelOfWord k (BitString.listRow (k + 2) i coins)) T) := by
  have hgate (g : Fin f.circuit.q) : f.circuit.gateList.getD g (0, 0, []) =
      (f.circuit.A g, f.circuit.B g, [f.circuit.G g false false, f.circuit.G g false true,
        f.circuit.G g true false, f.circuit.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  have hm := f.isValid.m_le_q
  have hsize := size_toCircuit f
  simp only [ConventionalCircuit.topo] at hm
  simp only [reductionView, viewWord, simulateWith, PrvView.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [ConventionalCircuit.length_gateList, PointPermute.bodyWith_eq_ofFn f.circuit.A
      f.circuit.B (fun g i => ctRow (blocksUpTo k f T f.circuit.q) (f.circuit.G g true true) g i)
      (fun g => by rw [hgate]) (fun g => by rw [hgate]) (fun g i => by rw [hgate]; rfl)]
    simp only [encodeFn, encodeGate_eq_ctRow]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · rw [List.map_range_eq_ofFn]
    simp only [labelBits_labelOfWord (BitString.length_listRow _ _ _)]
  · rw [List.map_range_eq_ofFn]
    congr 1
    funext o
    have hout : (Wire.ofNat (f.circuit.n + f.circuit.q - f.circuit.m + o) (by omega) :
        Wire f.circuit.n (toCircuit f).size) = (toCircuit f).outputs o :=
      Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_outputs_toCircuit])
    have hlabel : (labelsUpTo k f E f.circuit.q).getD
        (f.circuit.n + f.circuit.q - f.circuit.m + o) [] =
          labelBits (E ((toCircuit f).outputs o)) := by
      rw [labelsUpTo, getD_take_labels E (by omega) (by omega), hout]
    have hval : (f.circuit.wires x f.circuit.q).getD (f.circuit.n + f.circuit.q - f.circuit.m + o)
        false = (toCircuit f).eval interpretation (BitString.ofList f.circuit.n x) o := by
      rw [← toNat_outputs_toCircuit, Circuit.eval, Function.comp_apply, trace_toCircuit,
        BitString.ofFn_ofList hx]
    simp only [ConventionalCircuit.length_gateList, hlabel, hval, colourWord_labelBits, evaluate,
      hE, Bool.add_eq_xor]

/-- Uniform coins give uniform input labels. -/
private theorem uniformList_map_labelOfWord (k n : ℕ) :
    (BitString.uniformList (n * (k + 2))).map
        (fun coins (i : Fin n) => labelOfWord k (BitString.listRow (k + 2) i coins)) =
      PMF.uniformOfFintype (Fin n → BitString (k + 1) × Bool) := by
  have hcomp : (fun coins (i : Fin n) => labelOfWord k (BitString.listRow (k + 2) i coins)) =
      ((Equiv.arrowCongr (Equiv.refl (Fin n)) (labelEquiv k)) : _ → _) ∘
        fun word i => BitString.ofList (k + 2) (BitString.listRow (k + 2) (Equiv.refl (Fin n) i)
          word) := by
    funext coins i
    rfl
  rw [hcomp, ← PMF.map_comp, BitString.uniformList_map_listRow_equiv,
    PMF.uniformOfFintype_map_equiv]

variable (hash) in
/-- **The word reduction runs the typed reduction.** Against every fixed oracle `O`, the
reduction for `B` at parameter `k` runs `B`'s choice of `(f, x)`. When `x` has `f.n` bits and
`2 q ≤ 2 ^ k`, it then runs the typed reduction on `toCircuit f` with `B`'s guess on the words of
the view; otherwise it runs `B`'s guess on `⊥`. -/
private theorem eval_run_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary XorAndCircuit σ)
    (k : ℕ)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool) :
    ProbComp.eval (((CCR.codec k).adapt (prvSimReduction hash B k [])).run
        fun q => pure (O q)) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.circuit.n ∧
            2 * query.fn.circuit.q ≤ 2 ^ k then
          ProbComp.eval ((reduction (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)
            (BitString.ofList query.fn.circuit.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ V)))).run fun q => pure (O q))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [prvSimReduction, OracleCodec.run_adapt, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hguard
  swap
  · simp only [ProbOracleComp.run_sample]
  set f := query.fn
  set x := query.input
  have hx : x.length = f.circuit.n := hguard.1
  rw [eval_run_reduction]
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind,
    BitString.eval_sampleList]
  rw [← uniformList_map_labelOfWord, PMF.bind_map]
  refine congrArg _ (funext fun coins => ?_)
  have hfix := (isLocal_entry (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
    (BitString.ofList f.circuit.n x) O
    (fun i => labelOfWord k (BitString.listRow (k + 2) i coins))).isFixed_iterate 0
  rw [run_iterate_reductionStep hx O coins hfix rfl le_rfl]
  simp only [ProbComp.eval_pure, PMF.pure_bind, Function.comp_apply]
  exact congrArg (fun V => ProbComp.eval ((B k).guess state (some V)))
    (reductionView_eq hx coins (evalLabels_oracleTable _ _ _ _ _ _))

end Run

/-! ### The exact equality -/

section Exact

variable (hash : List Bool → List Bool → List Bool)

/-- **Distinct slots have distinct tweaks** while `2 q ≤ 2 ^ k`: slot `s` of gate `g` has the
tweak `2 g + s`, which is below `2 ^ k`. -/
private theorem slotTweak_injective (k : ℕ) (f : XorAndCircuit) (hk : 2 * f.circuit.q ≤ 2 ^ k) :
    Function.Injective (slotTweak (toCircuit f) k) := by
  have hsize := size_toCircuit f
  have hbound (g : Fin (toCircuit f).size) (b : Bool) : 2 * (g : ℕ) + b.toNat < 2 ^ k := by
    have := g.isLt
    have := Bool.toNat_le b
    omega
  rintro ⟨⟨g, hg⟩, b⟩ ⟨⟨g', hg'⟩, b'⟩ h
  have h' := congrArg List.ofFn h
  rw [ofFn_slotTweak, ofFn_slotTweak] at h'
  have heq := BitString.lowBits_injective_of_lt (hbound g b) (hbound g' b') h'
  obtain rfl : b = b' := by
    cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at heq ⊢ <;> omega
  obtain rfl : g = g' := Fin.ext (by omega)
  rfl

/-- **The garbler's coins are a uniform offset key and uniform input zero labels.** -/
private theorem uniformList_map_offsetKey_inputLabels (k n : ℕ) :
    (BitString.uniformList ((k + 1) + n * (k + 2))).map
        (fun coins => (offsetKey k coins, (inputLabels k coins : Fin n → _))) =
      PMF.uniformOfFintype (BitString (k + 1) × (Fin n → BitString (k + 1) × Bool)) := by
  rw [BitString.uniformList_add, PMF.map_bind]
  calc _ = (BitString.uniformList (k + 1)).bind fun front =>
        ((BitString.uniformList (n * (k + 2))).map fun back (i : Fin n) =>
          labelOfWord k (BitString.listRow (k + 2) i back)).map
            fun Z => (BitString.ofList (k + 1) front, Z) := by
        refine Probability.PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
        have hlen := BitString.length_of_mem_support_uniformList hfront
        rw [PMF.map_comp, PMF.map_comp]
        congr 1
        funext back
        refine Prod.ext (BitString.ofList_append_of_le hlen.ge _) (funext fun i => ?_)
        simp only [Function.comp_apply, inputLabels, inputWord, List.drop_left' hlen]
    _ = _ := by
        rw [uniformList_map_labelOfWord, ← Cslib.Probability.PMF.uniformOfFintype_prod,
          ← BitString.uniformList_ofList, PMF.bind_map]
        rfl

/-- **The real view is the typed real view.** For a query `(f, x)` with `x` of `f.n` bits, the
real view at parameter `k` is the words of the typed view, on `x`, of the typed garbling of
`toCircuit f`. -/
private theorem eval_prvView (k : ℕ) (q : Query XorAndCircuit)
    (hx : q.input.length = q.fn.circuit.n) :
    ProbComp.eval ((scheme hash).prvView k q) =
      (ProbComp.eval (garble (toCircuit q.fn) (CCR.atLevel hash k) (slotTweak _ k))).map
        fun G => viewWord k _ (G.view (BitString.ofList q.fn.circuit.n q.input)) := by
  have hcoins : (scheme hash).coins k q.fn = (k + 1) + q.fn.circuit.n * (k + 2) := rfl
  have hfun : (fun a : Scheme.Garbled =>
      (⟨a.fn, (scheme hash).encode a.encInfo q.input, a.decInfo⟩ : PrvView)) ∘
        (scheme hash).gb k q.fn =
      (fun p : BitString (k + 1) × (Fin q.fn.circuit.n → BitString (k + 1) × Bool) =>
        viewWord k _ ((garbleWith (toCircuit q.fn) (CCR.atLevel hash k) (slotTweak _ k) p.1
          p.2).view (BitString.ofList q.fn.circuit.n q.input))) ∘
        (fun coins => (offsetKey k coins, (inputLabels k coins : Fin q.fn.circuit.n → _))) := by
    funext coins
    simp only [Function.comp_apply]
    rw [gb_eq_encodeGarbled]
    simp only [viewWord, encodeGarbled, Garbled.view, PrvView.mk.injEq, true_and, and_true]
    exact PointPermute.projectiveEncode_labelBits (n := q.fn.circuit.n) _ hx
  simp only [Scheme.prvView, garble, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    Scheme.eval_garble, ProbComp.eval_uniform, hcoins, PMF.map_comp]
  rw [hfun, ← PMF.map_comp, uniformList_map_offsetKey_inputLabels,
    ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The real `prv.sim` experiment, when every valid query `B k` can choose has `2 q ≤ 2 ^ k`, is
`B`'s choice followed by the typed real game of `toCircuit f`. -/
private theorem eval_prvSimExperiment_true {σ : Type} (B : ℕ → PrvSimAdversary XorAndCircuit σ)
    (k : ℕ) (S : PrvSimulator XorAndCircuit)
    (hq : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.circuit.n → 2 * query.fn.circuit.q ≤ 2 ^ k) :
    ProbComp.eval (prvSimExperiment (scheme hash) (SideInfo.circ (scheme hash)) k S (B k) true) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.circuit.n ∧ 2 * query.fn.circuit.q ≤ 2 ^ k then
          realGame (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)
            (BitString.ofList query.fn.circuit.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [realGame, ProbComp.eval_bind]
  exact eval_prvSimExperiment_eq_bind (scheme hash) (SideInfo.circ (scheme hash)) k S (B k) true
    (fun q => 2 * q.fn.circuit.q ≤ 2 ^ k) hq
    (fun query (G : Garbled (toCircuit query.fn) (BitString (k + 1))) =>
      viewWord k _ (G.view (BitString.ofList query.fn.circuit.n query.input)))
    (fun query => ProbComp.eval (garble (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)))
    (fun query _ _ hx => by
      change query.input.length = query.fn.circuit.n at hx
      simp only [ite_true]
      exact eval_prvView hash k query hx)

/-- The simulated `prv.sim` experiment, when every valid query `B k` can choose has
`2 q ≤ 2 ^ k`, is `B`'s choice followed by the typed simulated game of `toCircuit f`. -/
private theorem eval_prvSimExperiment_false {σ : Type} (B : ℕ → PrvSimAdversary XorAndCircuit σ)
    (k : ℕ)
    (hq : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.circuit.n → 2 * query.fn.circuit.q ≤ 2 ^ k) :
    ProbComp.eval (prvSimExperiment (scheme hash) (SideInfo.circ (scheme hash)) k
        (simWord hash k) (B k) false) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.circuit.n ∧ 2 * query.fn.circuit.q ≤ 2 ^ k then
          simGame (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)
            (BitString.ofList query.fn.circuit.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [simGame, ProbComp.eval_bind]
  exact eval_prvSimExperiment_eq_bind (scheme hash) (SideInfo.circ (scheme hash)) k
    (simWord hash k) (B k) false (fun q => 2 * q.fn.circuit.q ≤ 2 ^ k) hq
    (fun query (V : View (toCircuit query.fn) (BitString (k + 1))) => viewWord k _ V)
    (fun query => ProbComp.eval (simulate (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)
      ((toCircuit query.fn).eval interpretation (BitString.ofList query.fn.circuit.n query.input))))
    (fun query _ _ hx => by
      change query.input.length = query.fn.circuit.n at hx
      have hy : BitString.ofList query.fn.circuit.m (query.fn.circuit.evalCirc query.input) =
          (toCircuit query.fn).eval interpretation
            (BitString.ofList query.fn.circuit.n query.input) := by
        have h := eval_toCircuit query.fn (BitString.ofList query.fn.circuit.n query.input)
        rw [BitString.ofFn_ofList hx] at h
        rw [← h, BitString.ofList_ofFn]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (scheme hash).ev query.fn query.input = query.fn.circuit.evalCirc query.input from
        rfl, show (SideInfo.circ (scheme hash)).phi query.fn = query.fn from rfl, eval_simWord, hy])

/-- Against the circular oracle, the reduction plays `B`'s choice followed by the typed real
game. -/
private theorem eval_realExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary XorAndCircuit σ) (k : ℕ) :
    ProbComp.eval (PRF.realExperiment (CCR.keyed (CCR.atLevel hash k) CCR.offset CCR.offset)
        ((CCR.codec k).adapt (prvSimReduction hash B k []))) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.circuit.n ∧ 2 * query.fn.circuit.q ≤ 2 ^ k then
          realGame (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)
            (BitString.ofList query.fn.circuit.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs
  · rw [← realGame_reduction _ _ _ _ BitString.add_self]
    simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  · rw [PMF.bind_const]

/-- Against a uniform random function, the reduction plays `B`'s choice followed by the typed
simulated game: in the branch that queries, distinct slots have distinct tweaks. -/
private theorem eval_idealExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary XorAndCircuit σ) (k : ℕ) :
    ProbComp.eval (PRF.idealExperiment ((CCR.codec k).adapt (prvSimReduction hash B k []))) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.circuit.n ∧ 2 * query.fn.circuit.q ≤ 2 ^ k then
          simGame (toCircuit query.fn) (CCR.atLevel hash k) (slotTweak _ k)
            (BitString.ofList query.fn.circuit.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hguard
  · rw [← simGame_reduction _ _ _ _ (slotTweak_injective k query.fn hguard.2)]
    simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  · rw [PMF.bind_const]

/-- **The `prv.sim` advantage against the simulator is the reduction's CCR advantage.** At
parameter `k`, if every valid query that `B k` can choose has a circuit with `2 q ≤ 2 ^ k`, the
`prv.sim` advantage of `B k` against `simWord hash k`, with the side information `Φ_circ`, equals
the finite circular correlation robustness advantage `CCR.advantage (CCR.atLevel hash k)
CCR.offset CCR.offset` of `prvSimReduction hash B` at level `k`, read through `CCR.codec k`. -/
theorem prvSimAdvantage_simWord_eq {σ : Type} (B : ℕ → PrvSimAdversary XorAndCircuit σ) (k : ℕ)
    (hq : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.circuit.n → 2 * query.fn.circuit.q ≤ 2 ^ k) :
    prvSimAdvantage (scheme hash) (SideInfo.circ (scheme hash)) k (simWord hash k) (B k) =
      CCR.advantage (CCR.atLevel hash k) CCR.offset CCR.offset
        ((CCR.codec k).adapt (prvSimReduction hash B k [])) := by
  rw [prvSimAdvantage, Experiment.advantage, eval_prvSimExperiment_false hash B k hq,
    eval_prvSimExperiment_true hash B k _ hq, Game.advantage_comm, CCR.advantage, PRF.advantage,
    eval_realExperiment_prvSimReduction, eval_idealExperiment_prvSimReduction]

end Exact

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

variable {hash : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => hash p.1 p.2)
    (encPair encBits encBits) encBits)

attribute [local fun_prop] hashWord_polyTime tweakWord_polyTime andWord_polyTime

/-- The data of the gate loop as words: the parameter and the input count in unary, the gate
data, framed, and the wire values; each field but the last is framed. -/
private enc_structure encGateLoopData : GateLoopData where
  param : encUnary, inputCount : encUnary,
  gates : (encList (encPair encNat (encPair encNat encBits))), wireValues : encBits

/-- The state of the gate loop as words: the labels so far, framed, then the blocks so far. -/
private enc_structure encGateLoopState : GateLoopState where
  labels : (encList encBits), blocks : (encList encBits)

/-! The records are written as the right-nested tuples of their fields. -/

example (d : GateLoopData) : encGateLoopData d = encPair encUnary (encPair encUnary
    (encPair (encList (encPair encNat (encPair encNat encBits))) encBits))
    (d.param, d.inputCount, d.gates, d.wireValues) := rfl

example (st : GateLoopState) :
    encGateLoopState st = encPair (encList encBits) (encList encBits) (st.labels, st.blocks) :=
  rfl

include hf in
/-- The state after an AND gate is computed in polynomial time. -/
private theorem andState_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g : γ → ℕ}
    {a b rG rE : γ → List Bool} {st : γ → GateLoopState}
    (hk : ComputableInPolyTime k encIn encUnary) (hg : ComputableInPolyTime g encIn encUnary)
    (ha : ComputableInPolyTime a encIn encBits) (hb : ComputableInPolyTime b encIn encBits)
    (hrG : ComputableInPolyTime rG encIn encBits) (hrE : ComputableInPolyTime rE encIn encBits)
    (hst : ComputableInPolyTime st encIn encGateLoopState) :
    ComputableInPolyTime (fun x => andState hash (k x) (g x) (a x) (b x) (rG x) (rE x) (st x))
      encIn encGateLoopState := by
  have hTG : ComputableInPolyTime (fun x => List.zipWith xor (hashWord hash (k x) (a x)
      (tweakWord (k x) (g x) false)) (rG x)) encIn encBits := by
    polytime
  have hTE : ComputableInPolyTime (fun x => List.zipWith xor (List.zipWith xor
      (hashWord hash (k x) (b x) (tweakWord (k x) (g x) true)) (a x)) (rE x)) encIn encBits := by
    polytime
  have hnil : ComputableInPolyTime (fun _ : γ => ([] : List (List Bool))) encIn
      (encList encBits) := ComputableInPolyTime.const _
  exact encGateLoopState_mk_polyTime
    (ComputableInPolyTime.listAppend' (encGateLoopState_labels_polyTime hst)
      (ComputableInPolyTime.cons' (andWord_polyTime hf hk hg hTG hTE ha hb) hnil))
    (ComputableInPolyTime.listAppend' (encGateLoopState_blocks_polyTime hst)
      (ComputableInPolyTime.cons' (ComputableInPolyTime.bitsAppend hTG hTE) hnil))

include hf in
/-- One gate of the reduction is strict oracle PPT. -/
private theorem isOraclePPTOn_reductionStep :
    IsOraclePPTOn (encPair encGateLoopData encGateLoopState) encGateLoopState
      (fun p : GateLoopData × GateLoopState => reductionStep hash p.1 p.2) := by
  let E := encPair encGateLoopData encGateLoopState
  have hd := ComputableInPolyTime.fst encGateLoopData encGateLoopState
  have hst := ComputableInPolyTime.snd encGateLoopData encGateLoopState
  have hk := encGateLoopData_param_polyTime hd
  have hn := encGateLoopData_inputCount_polyTime hd
  have hgates := encGateLoopData_gates_polyTime hd
  have hws := encGateLoopData_wireValues_polyTime hd
  have hlabels := encGateLoopState_labels_polyTime hst
  have hblocks := encGateLoopState_blocks_polyTime hst
  have hg : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      p.2.labels.length - p.1.inputCount) E encUnary :=
    ComputableInPolyTime.unary_sub.comp
      (((ComputableInPolyTime.length_list _).comp hlabels).prod hn)
  have hnext : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      nextGate p.1 p.2.labels) E (encPair encNat (encPair encNat encBits)) :=
    ComputableInPolyTime.listGetDWithInput hgates hg (0, 0, [])
  have hcap : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      p.2.labels.length + 1) E encUnary :=
    ComputableInPolyTime.unary_add' ((ComputableInPolyTime.length_list _).comp hlabels)
      (ComputableInPolyTime.const 1)
  have hi : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      leftArg p.1 p.2.labels) E encUnary := by
    have hA := hnext.fst'
    unfold leftArg
    polytime
  have hj : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      rightArg p.1 p.2.labels) E encUnary := by
    have hB := hnext.snd'.fst'
    unfold rightArg
    polytime
  have ha := ComputableInPolyTime.listGetDWithInput hlabels hi []
  have hb := ComputableInPolyTime.listGetDWithInput hlabels hj []
  have hva := ComputableInPolyTime.bitsGetDWithInput hws hi false
  have hvb := ComputableInPolyTime.bitsGetDWithInput hws hj false
  have hcond := ComputableInPolyTime.bitsGetDWithInput hnext.snd'.snd'
    (ComputableInPolyTime.const 3) false
  have hlim : ComputableInPolyTime (fun p : GateLoopData × GateLoopState => p.1.param + 2) E
      encUnary := ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2)
  have hcolour : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      colourWord p.1.param (p.2.labels.getD (rightArg p.1 p.2.labels) [])) E encBool :=
    ComputableInPolyTime.bitsGetDWithInput hb
      (ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 1)) false
  have hreqG := ha.bitsAppend ((tweakWord_polyTime hk hg (.const false)).bitsAppend
    ((Eq.ndrec (motive := fun g => ComputableInPolyTime g E encBool)
      (ComputableInPolyTime.bool_xor.comp (hcolour.prod hvb)) rfl).bitsCons (.const [])))
  have hreqE := hb.bitsAppend ((tweakWord_polyTime hk hg (.const true)).bitsAppend
    (hva.bitsCons (.const [])))
  have hnil : ComputableInPolyTime (fun _ : GateLoopData × GateLoopState =>
      ([] : List (List Bool))) E (encList encBits) := ComputableInPolyTime.const _
  have hxorLabel : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      (List.zipWith xor (p.2.labels.getD (leftArg p.1 p.2.labels) [])
        (p.2.labels.getD (rightArg p.1 p.2.labels) [])).take (p.1.param + 2)) E encBits := by
    polytime
  have hxor : ComputableInPolyTime (fun p : GateLoopData × GateLoopState =>
      (⟨p.2.labels ++ [(List.zipWith xor (p.2.labels.getD (leftArg p.1 p.2.labels) [])
        (p.2.labels.getD (rightArg p.1 p.2.labels) [])).take (p.1.param + 2)],
          p.2.blocks ++ [[]]⟩ : GateLoopState)) E encGateLoopState :=
    encGateLoopState_mk_polyTime
      (ComputableInPolyTime.listAppend' hlabels (ComputableInPolyTime.cons' hxorLabel hnil))
      (ComputableInPolyTime.listAppend' hblocks (ComputableInPolyTime.cons'
        (ComputableInPolyTime.const (encIn := E) (encOut := encBits) []) hnil))
  have hfst₁ := ComputableInPolyTime.fst E encBits
  have hfst₂ := (ComputableInPolyTime.fst E encBits).comp
    (ComputableInPolyTime.fst (encPair E encBits) encBits)
  have hrG := (ComputableInPolyTime.snd E encBits).comp
    (ComputableInPolyTime.fst (encPair E encBits) encBits)
  have hrE := ComputableInPolyTime.snd (encPair E encBits) encBits
  have hand := andState_polyTime hf (hk.comp hfst₂) (hg.comp hfst₂) (ha.comp hfst₂)
    (hb.comp hfst₂) hrG hrE (hst.comp hfst₂)
  refine IsOraclePPTOn.cond hcond ?_ hxor.isOraclePPTOn
  refine IsOraclePPTOn.bind_with (IsOraclePPTOn.query_take () hreqG hlim) ?_
  exact IsOraclePPTOn.bind_with (IsOraclePPTOn.query_take () (hreqE.comp hfst₁)
    (hlim.comp hfst₁)) hand.isOraclePPTOn

include hf in
/-- One gate of the reduction is strict oracle PPT on any input from which its loop data is
computed in polynomial time. -/
private theorem isOraclePPTOn_reductionStep_comp {γ : Type} {encIn : γ ↪ List Bool}
    {d : γ → GateLoopData} (hd : ComputableInPolyTime d encIn encGateLoopData) :
    IsOraclePPTOn (encPair encIn encGateLoopState) encGateLoopState
      (fun p : γ × GateLoopState => reductionStep hash (d p.1) p.2) := by
  have h := (isOraclePPTOn_reductionStep hf).preprocess
    ((hd.comp (ComputableInPolyTime.fst encIn encGateLoopState)).prod
      (ComputableInPolyTime.snd encIn encGateLoopState))
  exact Eq.ndrec (motive := IsOraclePPTOn _ _) h rfl

/-- A step of the gate loop grows its encoded state by at most `8 (k + 2) + 8` bits. -/
private theorem length_encGateLoopState_le_of_mem_support {d : GateLoopData}
    {st next : GateLoopState} (hnext : next ∈ (reductionStep hash d st).support) :
    (encGateLoopState next).length ≤ (encGateLoopState st).length + (8 * (d.param + 2) + 8) := by
  obtain ⟨label, block, rfl, hl, hb⟩ := exists_of_mem_support_reductionStep hash hnext
  simp only [encGateLoopState_apply, length_encPair, length_encList, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, encBits_apply]
  omega

/-- A row of the reduction's garbled function is computed in polynomial time. -/
private theorem ctRow_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {blocks : γ → List (List Bool)} {isAnd : γ → Bool} {g i : γ → ℕ}
    (hblocks : ComputableInPolyTime blocks encIn (encList encBits))
    (hisAnd : ComputableInPolyTime isAnd encIn encBool)
    (hg : ComputableInPolyTime g encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => ctRow (blocks x) (isAnd x) (g x) (i x)) encIn encBits := by
  polytime [ctRow]

/-- The reduction's view is computed in polynomial time from the parameter, the data of the
circuit, the wire values, the coins and the state of the gate loop. -/
private theorem reductionView_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k : γ → ℕ}
    {f : γ → ConventionalCircuit} {ws coins : γ → List Bool}
    {st : γ → GateLoopState}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hd : ComputableInPolyTime (fun x => ((f x).n, (f x).m, (f x).gateList)) encIn encCircuitData)
    (hws : ComputableInPolyTime ws encIn encBits)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (hst : ComputableInPolyTime st encIn encGateLoopState) :
    ComputableInPolyTime (fun x => reductionView (k x) (f x) (ws x) (coins x) (st x)) encIn
      encPrvView := by
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hgates := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hgates
  have hx := ComputableInPolyTime.fst encIn (encPair encUnary (encPair encBool encUnary))
  have hrest := ComputableInPolyTime.snd encIn (encPair encUnary (encPair encBool encUnary))
  have hrow : ComputableInPolyTime (fun p : γ × ℕ × Bool × ℕ => ctRow (st p.1).blocks p.2.2.1
      p.2.1 p.2.2.2) (encPair encIn (encPair encUnary (encPair encBool encUnary))) encBits :=
    ctRow_polyTime ((encGateLoopState_blocks_polyTime hst).comp hx) hrest.snd'.fst' hrest.fst'
      hrest.snd'.snd'
  have hbody := bodyWith_gateData_polyTime hn hgates hrow
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn z)
      PointPermute.encFn encBits := .of_eq fun _ => rfl
  have hF := Eq.ndrec (motive := fun g => ComputableInPolyTime g encIn encBits)
    (henc.comp ((hk.prod (hn.prod (hm.prod hq))).prod hbody))
    (funext fun _ => congrArg PointPermute.encFn rfl)
  have hX : ComputableInPolyTime (fun x => ((List.range (f x).n).map fun i =>
      BitString.listRow (k x + 2) i (coins x)).flatten) encIn encBits := by
    polytime [BitString.listRow]
  have hrange : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List (List Bool) × List Bool =>
      (List.range p.2.1).map fun o => colourWord p.1 (p.2.2.2.1.getD (p.2.2.1 + o) []) ^^
        p.2.2.2.2.getD (p.2.2.1 + o) false)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair (encList encBits) encBits))))
      encBits := by
    polytime [colourWord]
  have hs := ComputableInPolyTime.unary_sub.comp ((ComputableInPolyTime.unary_add' hn hq).prod hm)
  exact encPrvView_mk_polyTime hF hX (Eq.ndrec (motive := fun g =>
    ComputableInPolyTime g encIn encBits) (hrange.comp (hk.prod (hm.prod (hs.prod
      ((encGateLoopState_labels_polyTime hst).prod hws))))) rfl)

variable {σ : Type} {encσ : σ ↪ List Bool} {B : ℕ → PrvSimAdversary XorAndCircuit σ}
  (hB : TwoStage.IsPPT encUnit (encQuery XorAndCircuit encXorAndCircuit) (encOption encPrvView)
    encBool encσ B)

include hf hB in
/-- The querying branch of the reduction after the input labels are drawn: run the gate loop and
`B`'s guess on the view. -/
private theorem isOraclePPTOn_prvSimGuess :
    IsOraclePPTOn (encPair (encPrvChosen encXorAndCircuit encσ) encBits) encBool
      (fun p : ((ℕ × List Bool) × (Query XorAndCircuit × σ)) × List Bool => do
        let st ← OracleComp.iterate p.1.2.1.fn.circuit.q
          (reductionStep hash ⟨p.1.1.1, p.1.2.1.fn.circuit.n, p.1.2.1.fn.circuit.gateList,
            p.1.2.1.fn.circuit.wires p.1.2.1.input p.1.2.1.fn.circuit.q⟩)
          ⟨BitString.listRows p.1.2.1.fn.circuit.n (p.1.1.1 + 2) p.2, []⟩
        ProbOracleComp.sample ((B p.1.1.1).guess p.1.2.2 (some (reductionView p.1.1.1
          p.1.2.1.fn.circuit (p.1.2.1.fn.circuit.wires p.1.2.1.input p.1.2.1.fn.circuit.q) p.2
          st)))) := by
  let E := encPair (encPrvChosen encXorAndCircuit encσ) encBits
  have h₁ := ComputableInPolyTime.fst (encPrvChosen encXorAndCircuit encσ) encBits
  have hk := ((ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encQuery XorAndCircuit encXorAndCircuit) encσ)).comp h₁).fst'
  have hqs := (ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encQuery XorAndCircuit encXorAndCircuit) encσ)).comp h₁
  have hquery := hqs.fst'
  have hstate := hqs.snd'
  have hcoins := ComputableInPolyTime.snd (encPrvChosen encXorAndCircuit encσ) encBits
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hd := (circuitData_polyTime.comp XorAndCircuit.val_polyTime).comp hfn
  have hn := hd.fst'
  have hgates := hd.snd'.snd'
  have hq : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query XorAndCircuit × σ)) ×
      List Bool => p.1.2.1.fn.circuit.q) E encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hgates
  have hws := wires_polyTime.comp ((XorAndCircuit.val_polyTime.comp hfn).prod hx)
  have hrows : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool =>
      BitString.listRows p.1 (p.2.1 + 2) p.2.2) (encPair encUnary (encPair encUnary encBits))
      (encList encBits) := by
    polytime [BitString.listRows, BitString.listRow]
  have hinit : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query XorAndCircuit × σ)) ×
      List Bool => (⟨BitString.listRows p.1.2.1.fn.circuit.n (p.1.1.1 + 2) p.2, []⟩ :
        GateLoopState)) E encGateLoopState :=
    encGateLoopState_mk_polyTime (hrows.comp (hn.prod (hk.prod hcoins)))
      (ComputableInPolyTime.const (encIn := E) (encOut := encList encBits) [])
  have hfst := ComputableInPolyTime.fst E encGateLoopState
  have hdata : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query XorAndCircuit × σ)) ×
      List Bool => (⟨p.1.1.1, p.1.2.1.fn.circuit.n, p.1.2.1.fn.circuit.gateList,
        p.1.2.1.fn.circuit.wires p.1.2.1.input p.1.2.1.fn.circuit.q⟩ : GateLoopData)) E
      encGateLoopData :=
    encGateLoopData_mk_polyTime hk hn hgates hws
  have hstep := isOraclePPTOn_reductionStep_comp hf hdata
  have hgrowth : ComputableInPolyTime (fun k : ℕ => 8 * (k + 2) + 8) encUnary encUnary := by
    polytime
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth
    (growth := fun p : ((ℕ × List Bool) × (Query XorAndCircuit × σ)) × List Bool =>
      8 * (p.1.1.1 + 2) + 8) hq hinit hstep
    ((hgrowth.comp hk).polyBounded_length.mono fun p => by simp)
    (fun (p : ((ℕ × List Bool) × (Query XorAndCircuit × σ)) × List Bool) _ _ hnext =>
      length_encGateLoopState_le_of_mem_support (d := ⟨p.1.1.1, p.1.2.1.fn.circuit.n,
        p.1.2.1.fn.circuit.gateList, p.1.2.1.fn.circuit.wires p.1.2.1.input
          p.1.2.1.fn.circuit.q⟩) hnext)
  have hview := reductionView_polyTime (f := fun p => p.1.1.2.1.fn.circuit) (hk.comp hfst)
    (hd.comp hfst) (hws.comp hfst) (hcoins.comp hfst) (ComputableInPolyTime.snd E encGateLoopState)
  have hprep := (hk.comp hfst).prod ((hstate.comp hfst).prod
    ((ComputableInPolyTime.optionSome encPrvView).comp hview))
  have hguess := (hB.guess.preprocess hprep).isOraclePPTOn (Operation := Unit)
  exact hloop.bind_with (Eq.ndrec (motive := IsOraclePPTOn (Operation := Unit)
    (encPair E encGateLoopState) encBool) hguess rfl)

include hf hB in
/-- **Efficiency of the reduction.** For every hash family computed in polynomial time and every
uniform strict PPT `prv.sim` adversary `B`, `prvSimReduction hash B` is uniform strict oracle
PPT. -/
theorem isOraclePPT_prvSimReduction : IsOraclePPT encBool (prvSimReduction hash B) := by
  have hd := circuitData_polyTime.comp XorAndCircuit.val_polyTime
  have hn : ComputableInPolyTime (fun f : XorAndCircuit => f.circuit.n) encXorAndCircuit
      encUnary := hd.fst'
  have hq : ComputableInPolyTime (fun f : XorAndCircuit => f.circuit.q) encXorAndCircuit
      encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have hlen : ComputableInPolyTime (fun p : ℕ × XorAndCircuit => p.2.circuit.n * (p.1 + 2))
      (encPair encUnary encXorAndCircuit) encUnary :=
    ComputableInPolyTime.unary_mul.comp ((hn.comp (ComputableInPolyTime.snd _ _)).prod
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst _ _)
        (ComputableInPolyTime.const 2)))
  exact isOraclePPT_prvSimReduction_of_bounded hB 2 hn hq hlen
    (fun k query state coins => do
      let st ← OracleComp.iterate query.fn.circuit.q
        (reductionStep hash ⟨k, query.fn.circuit.n, query.fn.circuit.gateList,
          query.fn.circuit.wires query.input query.fn.circuit.q⟩)
        ⟨BitString.listRows query.fn.circuit.n (k + 2) coins, []⟩
      ProbOracleComp.sample ((B k).guess state (some (reductionView k query.fn.circuit
        (query.fn.circuit.wires query.input query.fn.circuit.q) coins st))))
    (isOraclePPTOn_prvSimGuess hf hB)

end Efficiency

end Cslib.Crypto.Garbling.HalfGates
