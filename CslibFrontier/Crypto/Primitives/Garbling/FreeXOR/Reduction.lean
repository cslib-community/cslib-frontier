/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Simulator
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
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
import CslibFrontier.Tactic.PolyTime

/-!
# The CCR reduction for the privacy of Free-XOR garbling

Library infrastructure (no cited result): the run equality and exact advantage equality
connecting `FreeXOR.prvSimReduction` to `FreeXOR.scheme`, completing the reduction whose
program, legality, and efficiency were certified in Part 3a.

The `prv.sim` advantage of an adversary `B` against the simulator `simWord` of
`FreeXOR.scheme hash`, with the side information `phiXor`, is exactly the circular correlation
robustness advantage of an explicit, certified non-adaptive reduction `prvSimReduction hash B`, at
every parameter `k` where every valid circuit `B` can choose has `8 q ≤ 2 ^ k`
(`prvSimAdvantage_simWord_eq`).

The reduction runs `B`'s choice of a query `(f, x)`. When `x` has `f.n` bits and `8 q ≤ 2 ^ k`, it
samples one `(k + 2)`-bit active label per input and non-XOR gate, propagates active labels across
XOR gates, evaluates the circuit on `x` to obtain all plaintext wire bits, and issues the 8 oracle
queries of every non-XOR gate (`allReqs`) non-adaptively at level `k` (`(key, true), tweak, bit`),
whose requests all carry distinct `k`-bit tweaks while `8 q ≤ 2 ^ k`. It then builds the garbled
view `(F, X, d)` from the oracle replies and hands it to `B`'s guess. Otherwise (on an invalid input
length or when `8 q > 2 ^ k`), it makes no oracle queries and runs `B`'s guess on `⊥`.

Key-only queries `H'(x, t) = CCR.atLevel hash k (x, false) t` transfer to full-label queries via
`CCR.advantage_keyOnly` in `CslibFrontier.Crypto.Primitives.Garbling.CircularCorrelationRobust`,
since `(x, true) + (R, true) = (x + R, false)`. Against every fixed full-label oracle `O`, the word
reduction runs the typed reduction `FreeXOR.reduction` of
`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR` on `toCircuit f` (`eval_run_prvSimReduction`).
Thus, by `FreeXOR.realGame_reduction` and `FreeXOR.idealGame_reduction`, its CCR advantage equals
the `prv.sim` advantage (`prvSimAdvantage_simWord_eq`). The reduction asks every tweak at most once
on every execution path (`isTweakUnique_prvSimReduction`), issues `8` requests per non-XOR gate on
valid bounded inputs (`exists_of_mem_support_runWith_prvSimReduction`), and is uniform strict oracle
PPT (`isOraclePPT_prvSimReduction`).

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.prvSimReduction`: the non-adaptive CCR reduction.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.isTweakUnique_prvSimReduction`: the reduction is tweak-unique.
* `Cslib.Crypto.Garbling.FreeXOR.exists_of_mem_support_runWith_prvSimReduction`: logged execution
  request count.
* `Cslib.Crypto.Garbling.FreeXOR.prvSimAdvantage_simWord_eq`: the `prv.sim` advantage equals the
  reduction's CCR advantage while `8 q ≤ 2 ^ k`.
* `Cslib.Crypto.Garbling.FreeXOR.isOraclePPT_prvSimReduction`: the reduction is oracle PPT.
-/

public section

namespace Cslib.Crypto.Garbling

open Cslib.Circuits Probability ConventionalCircuit

namespace FreeXOR

/-! ### The word-level reduction -/

section Words

/-- The `2 k + 3`-bit CCR request for slot `(g, i, s)` of a non-XOR gate: the `(k + 1)`-bit key
with colour bit `true` (so `CCR.codec k` reads `(key, true)`), the `k`-bit tweak
`PointPermute.tweak k g i s`, and the circular bit `isFirst (flipped) s && rowBit`. -/
private def slotReq (k n : ℕ) (labels : List (List Bool)) (ws : List Bool)
    (g a b : ℕ) (tt : List Bool) (i s : ℕ) : List Bool :=
  let la := labels.getD a []
  let lb := labels.getD b []
  let f₀ := decide (2 ≤ i) ^^ HalfGates.colourWord k la
  let f₁ := decide (i % 2 = 1) ^^ HalfGates.colourWord k lb
  let rbit := ws.getD (n + g) false ^^
    tt.getD ((if f₀ ^^ ws.getD a false then 2 else 0) +
      (if f₁ ^^ ws.getD b false then 1 else 0)) false
  let lbl := if s = 0 then la else lb
  let bit := (if s = 0 then f₀ else !f₀ && f₁) && rbit
  lbl.take (k + 1) ++ [true] ++ PointPermute.tweak k g i s ++ [bit]

/-- The 8 CCR requests of gate `g`, or `[]` if gate `g` is an XOR gate. -/
private def gateReqs (k n g : ℕ) (labels : List (List Bool)) (ws : List Bool)
    (gate : ℕ × ℕ × List Bool) : List (List Bool) :=
  if isXorTable gate.2.2 then []
  else
    let cap := labels.length + ws.length + 1
    let a := min cap gate.1 - 1
    let b := min cap gate.2.1 - 1
    [slotReq k n labels ws g a b gate.2.2 0 0,
     slotReq k n labels ws g a b gate.2.2 0 1,
     slotReq k n labels ws g a b gate.2.2 1 0,
     slotReq k n labels ws g a b gate.2.2 1 1,
     slotReq k n labels ws g a b gate.2.2 2 0,
     slotReq k n labels ws g a b gate.2.2 2 1,
     slotReq k n labels ws g a b gate.2.2 3 0,
     slotReq k n labels ws g a b gate.2.2 3 1]

/-- All CCR requests of the circuit in gate, row, slot order. -/
private def allReqs (k n : ℕ) (gates : List (ℕ × ℕ × List Bool)) (labels : List (List Bool))
    (ws : List Bool) : List (List Bool) :=
  ((List.range gates.length).map fun g =>
    gateReqs k n g labels ws (gates.getD g (0, 0, []))).flatten

/-- One oracle step collecting the next reply truncated to `k + 2` bits. -/
private noncomputable def replyStep (k : ℕ) (reqs : List (List Bool)) (rs : List (List Bool)) :
    WordOracleComp Unit (List (List Bool)) :=
  replyStepWord (k + 2) (reqs.getD rs.length []) rs

variable (hash : List Bool → List Bool → List Bool)

/-- Row `i` of non-XOR gate `g` built from the propagated active labels `labels` and the oracle
answers `rs` at offset `8 * nonXorRank free g`. -/
private def redRow (k n : ℕ) (free : List Bool) (labels : List (List Bool))
    (rs : List (List Bool)) (g a b i : ℕ) : List Bool :=
  let la := labels.getD a []
  let lb := labels.getD b []
  let lout := labels.getD (n + g) []
  let f₀ := decide (2 ≤ i) ^^ HalfGates.colourWord k la
  let f₁ := decide (i % 2 = 1) ^^ HalfGates.colourWord k lb
  let rank := nonXorRank free g
  let o₀ := if f₀ then rs.getD (8 * rank + 2 * i) []
    else keyHashWord hash k la (PointPermute.tweak k g i 0)
  let o₁ := if f₁ then rs.getD (8 * rank + 2 * i + 1) []
    else keyHashWord hash k lb (PointPermute.tweak k g i 1)
  List.zipWith xor lout (List.zipWith xor o₀ o₁)

/-- One row slot of gate `g` in the layout of `PointPermute.bodyWith`. -/
private def redRowData (k n : ℕ) (free : List Bool) (labels : List (List Bool))
    (rs : List (List Bool)) (g a b i : ℕ) : List Bool :=
  (if i = 0 then [free.getD g false] else []) ++
    if free.getD g false then [] else redRow hash k n free labels rs g a b i

/-- The view `(F, X, d)` built by the reduction from the active wire labels, plaintext wire trace
`ws`, input label coins `coins`, and oracle replies `rs`. -/
private def redView (k : ℕ) (f : ConventionalCircuit) (ws coins : List Bool)
    (rs : List (List Bool)) : PrvView :=
  let free := xorFlags f.gateList
  let labels := simPropWords k f.topo free coins f.q
  ⟨PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
      PointPermute.bodyWith f.n f.gateList.length (labels.length + 1)
        (fun g => (f.gateList.getD g (0, 0, [])).1)
        (fun g => (f.gateList.getD g (0, 0, [])).2.1)
        (fun g a b i => redRowData hash k f.n free labels rs g a b i)),
    ((List.range f.n).map fun i => PointPermute.simLabel k coins i).flatten,
    (List.range f.m).map fun o =>
      HalfGates.colourWord k (labels.getD (f.n + f.gateList.length - f.m + o) []) ^^
        ws.getD (f.n + f.gateList.length - f.m + o) false⟩

/-- The non-adaptive oracle request list constructed by `prvSimReduction` for valid circuit `f`,
plaintext wire trace `ws`, and label coins `coins`. -/
private def prvSimReqs (k : ℕ) (f : ConventionalCircuit) (ws coins : List Bool) :
    List (List Bool) :=
  let free := xorFlags f.gateList
  let labels := simPropWords k f.topo free coins f.q
  allReqs k f.n f.gateList labels ws

/-- Library construction (no cited definition): **The CCR reduction** for a `prv.sim` adversary `B`
against Free-XOR garbling, at parameter `k`. Runs `B`'s choice of `(f, x)`. When `x` has `f.n` bits
and `8 q ≤ 2 ^ k`, it samples `(n + q)` active `(k + 2)`-bit labels, propagates across XOR gates,
issues 8 CCR queries per non-XOR gate non-adaptively, assembles the view `(F, X, d)` from the
replies, and runs `B`'s guess. Otherwise it makes no queries and runs `B`'s guess on `⊥`. -/
noncomputable def prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) : OracleDistinguisher :=
  fun k _ => do
    let (query, state) ← ProbOracleComp.sample ((B k).choose ())
    if query.input.length = query.fn.1.n ∧ 8 * query.fn.1.q ≤ 2 ^ k then do
      let coins ← ProbOracleComp.sample
        (BitString.sampleList ((query.fn.1.n + query.fn.1.q) * (k + 2)))
      let ws := query.fn.1.wires query.input query.fn.1.q
      let reqs := prvSimReqs k query.fn.1 ws coins
      let rs ← OracleComp.iterate reqs.length (replyStep k reqs) []
      ProbOracleComp.sample ((B k).guess state (some (redView hash k query.fn.1 ws coins rs)))
    else ProbOracleComp.sample ((B k).guess state none)

end Words

/-! ### Active label lengths and request structure -/

section Helpers

private theorem length_getD_simPropWords (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    {s : ℕ} (hs : s ≤ f.1.q) :
    ∀ w ∈ simPropWords k f.1.topo (xorFlags f.1.gateList) coins s, w.length = k + 2 := by
  induction s with
  | zero =>
    intro w hw
    simp only [simPropWords, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    exact PointPermute.length_simLabel k coins i
  | succ s ih =>
    have hsq : s < f.1.q := hs
    have hsq' : s < f.1.topo.q := hsq
    rw [simPropWords, dite_eq_left hsq']
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact ih hsq.le w hw
    · rw [List.mem_singleton.mp hw]
      split
      · have hlen : (simPropWords k f.1.topo (xorFlags f.1.gateList) coins s).length =
            f.1.n + s :=
          length_simPropWords k f.1.topo (xorFlags f.1.gateList) coins hsq.le
        have hA₁ := f.2.one_le_A ⟨s, hsq⟩
        have hAB := f.2.A_lt_B ⟨s, hsq⟩
        have hBg := f.2.B_lt_gate ⟨s, hsq⟩
        simp only [ConventionalCircuit.topo] at hA₁ hAB hBg hlen ⊢
        have hwire : ∀ v, v < f.1.n + s →
            ((simPropWords k { n := f.1.n, m := f.1.m, q := f.1.q, A := f.1.A, B := f.1.B }
              (xorFlags f.1.gateList) coins s).getD v []).length = k + 2 := by
          intro v hv
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact ih hsq.le _ (List.getElem_mem _)
        rw [List.length_zipWith, hwire _ (by omega), hwire _ (by omega), min_self]
      · exact PointPermute.length_simLabel k coins _

private theorem length_getD_simPropWords_q (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    {i : ℕ} (hi : i < f.1.n + f.1.q) :
    ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD i []).length =
      k + 2 := by
  have hlen : (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).length =
      f.1.n + f.1.q :=
    length_simPropWords k f.1.topo (xorFlags f.1.gateList) coins le_rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact length_getD_simPropWords k f coins le_rfl _ (List.getElem_mem _)

private theorem length_tweak (k g i s : ℕ) : (PointPermute.tweak k g i s).length = k := by
  simp [PointPermute.tweak]

private theorem length_slotReq {k n : ℕ} {labels : List (List Bool)} {ws : List Bool}
    {g a b : ℕ} {tt : List Bool} {i s : ℕ}
    (ha : (labels.getD a []).length = k + 2) (hb : (labels.getD b []).length = k + 2) :
    (slotReq k n labels ws g a b tt i s).length = 2 * k + 3 := by
  have hlbl : ((if s = 0 then labels.getD a [] else labels.getD b []).take (k + 1)).length =
      k + 1 := by
    rw [List.length_take]
    split_ifs <;> omega
  simp only [slotReq, List.length_append, hlbl, List.length_singleton, length_tweak]
  omega

private theorem tweak_slotReq {k n : ℕ} {labels : List (List Bool)} {ws : List Bool}
    {g a b : ℕ} {tt : List Bool} {i s : ℕ}
    (ha : (labels.getD a []).length = k + 2) (hb : (labels.getD b []).length = k + 2) :
    ((slotReq k n labels ws g a b tt i s).drop (k + 2)).take k = PointPermute.tweak k g i s := by
  have hpref : ((if s = 0 then labels.getD a [] else labels.getD b []).take (k + 1) ++
      [true]).length = k + 2 := by
    simp only [List.length_append, List.length_take, List.length_singleton]
    split_ifs <;> omega
  dsimp only [slotReq]
  rw [List.append_assoc, List.drop_left' hpref, List.take_left' (length_tweak k g i s)]

private theorem getD_min_cap {α : Type*} (l : List α) (d : α) (bound v : ℕ)
    (hb : l.length + 1 ≤ bound) :
    l.getD (min bound v - 1) d = l.getD (v - 1) d := by
  by_cases h : v ≤ l.length + 1
  · rw [Nat.min_eq_right (by omega)]
  · have h₁ : l.length ≤ min bound v - 1 := by omega
    have h₂ : l.length ≤ v - 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h₁, List.getElem?_eq_none h₂,
      Option.getD_none]

private theorem slotReq_min_cap (k n : ℕ) (labels : List (List Bool)) (ws : List Bool)
    (g v₁ v₂ : ℕ) (tt : List Bool) (i s : ℕ) :
    slotReq k n labels ws g (min (labels.length + ws.length + 1) v₁ - 1)
      (min (labels.length + ws.length + 1) v₂ - 1) tt i s =
      slotReq k n labels ws g (v₁ - 1) (v₂ - 1) tt i s := by
  have hl (v : ℕ) := getD_min_cap labels [] (labels.length + ws.length + 1) v (by omega)
  have hw (v : ℕ) := getD_min_cap ws false (labels.length + ws.length + 1) v (by omega)
  simp only [slotReq, hl, hw]

private theorem gateReqs_length (k n g : ℕ) (labels : List (List Bool)) (ws : List Bool)
    (gate : ℕ × ℕ × List Bool) :
    (gateReqs k n g labels ws gate).length = if isXorTable gate.2.2 then 0 else 8 := by
  unfold gateReqs
  split_ifs <;> simp

private def gateReqSlot (k n g : ℕ) (labels : List (List Bool)) (ws : List Bool)
    (gate : ℕ × ℕ × List Bool) (idx : ℕ) : List Bool :=
  slotReq k n labels ws g (gate.1 - 1) (gate.2.1 - 1) gate.2.2 (idx / 2) (idx % 2)

private theorem gateReqs_getElem {k n g : ℕ} {labels : List (List Bool)} {ws : List Bool}
    {gate : ℕ × ℕ × List Bool} (hxor : isXorTable gate.2.2 = false)
    {idx : ℕ} (hidx : idx < 8)
    (hmem : idx < (gateReqs k n g labels ws gate).length) :
    (gateReqs k n g labels ws gate)[idx]'hmem = gateReqSlot k n g labels ws gate idx := by
  simp only [gateReqs, hxor, Bool.false_eq_true, ↓reduceIte, gateReqSlot]
  interval_cases idx <;> exact slotReq_min_cap k n labels ws g gate.1 gate.2.1 gate.2.2 _ _

private theorem allReqs_prefix_length (k n : ℕ) (gates : List (ℕ × ℕ × List Bool))
    (labels : List (List Bool)) (ws : List Bool) {m : ℕ} (hm : m ≤ gates.length) :
    ((List.range m).map fun g =>
        gateReqs k n g labels ws (gates.getD g (0, 0, []))).flatten.length =
      8 * nonXorRank (xorFlags gates) m := by
  induction m with
  | zero => simp [nonXorRank]
  | succ m ih =>
    have hmlt : m < gates.length := hm
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih hmlt.le]
    simp only [List.map_singleton, List.flatten_singleton, gateReqs_length, nonXorRank, xorFlags,
      List.take_add_one, List.count_append]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt, Option.getD_some,
      List.getElem?_map, List.getElem?_eq_getElem hmlt]
    simp only [Option.map_some, Option.toList_some]
    cases isXorTable gates[m].2.2 <;> simp; omega

private theorem allReqs_length (k n : ℕ) (gates : List (ℕ × ℕ × List Bool))
    (labels : List (List Bool)) (ws : List Bool) :
    (allReqs k n gates labels ws).length = 8 * nonXorRank (xorFlags gates) gates.length :=
  allReqs_prefix_length k n gates labels ws le_rfl

private theorem allReqs_getD_slot (k n : ℕ) (gates : List (ℕ × ℕ × List Bool))
    (labels : List (List Bool)) (ws : List Bool) {g : ℕ} (hg : g < gates.length)
    (hxor : isXorTable gates[g].2.2 = false)
    {idx : ℕ} (hidx : idx < 8) :
    (allReqs k n gates labels ws).getD (8 * nonXorRank (xorFlags gates) g + idx) [] =
      gateReqSlot k n g labels ws gates[g] idx := by
  let free := xorFlags gates
  let step := fun j => gateReqs k n j labels ws (gates.getD j (0, 0, []))
  have hsplit : List.range gates.length =
      List.range g ++ g :: (List.range (gates.length - g - 1)).map (g + 1 + ·) := by
    conv_lhs =>
      rw [show gates.length = g + 1 + (gates.length - g - 1) by omega, List.range_add,
        List.range_succ, List.append_assoc, List.singleton_append]
  have hpre : ((List.range g).map step).flatten.length = 8 * nonXorRank free g :=
    allReqs_prefix_length k n gates labels ws hg.le
  have hstep : step g = gateReqs k n g labels ws gates[g] := by
    simp [step, List.getD_eq_getElem?_getD, hg]
  have hlen : (gateReqs k n g labels ws gates[g]).length = 8 := by
    rw [gateReqs_length, hxor]; simp
  change ((List.range gates.length).map step).flatten.getD (8 * nonXorRank free g + idx) [] =
    gateReqSlot k n g labels ws gates[g] idx
  rw [hsplit, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, hstep,
    ← List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [List.length_append, hpre, hlen]; omega),
    List.getElem?_append_right (by omega), hpre, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact gateReqs_getElem hxor hidx (by omega)

private theorem allReqs_lookup (k n : ℕ) (gates : List (ℕ × ℕ × List Bool))
    (labels : List (List Bool)) (ws : List Bool) {p : ℕ}
    (hp : p < (allReqs k n gates labels ws).length) :
    ∃ (g : ℕ) (hg : g < gates.length) (idx : ℕ), idx < 8 ∧
      isXorTable gates[g].2.2 = false ∧
      p = 8 * nonXorRank (xorFlags gates) g + idx ∧
      (allReqs k n gates labels ws)[p]'hp = gateReqSlot k n g labels ws gates[g] idx := by
  let free := xorFlags gates
  let step := fun j => gateReqs k n j labels ws (gates.getD j (0, 0, []))
  suffices h : ∀ m (hm : m ≤ gates.length)
      (hp : p < ((List.range m).map step).flatten.length),
      ∃ (g : ℕ) (hg : g < m) (idx : ℕ), idx < 8 ∧
        isXorTable (gates[g]'(by omega)).2.2 = false ∧
        p = 8 * nonXorRank free g + idx ∧
        ((List.range m).map step).flatten[p]'hp =
          gateReqSlot k n g labels ws (gates[g]'(by omega)) idx from
    h gates.length le_rfl hp
  intro m hm hp
  induction m with
  | zero => simp at hp
  | succ m ih =>
    have hmlt : m < gates.length := hm
    simp only [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton, List.length_append] at hp ⊢
    have hpre : ((List.range m).map step).flatten.length = 8 * nonXorRank free m :=
      allReqs_prefix_length k n gates labels ws hmlt.le
    by_cases hlt : p < ((List.range m).map step).flatten.length
    · obtain ⟨g, hg, idx, hidx, hxor, hp_eq, hval⟩ := ih hmlt.le hlt
      refine ⟨g, Nat.lt_succ_of_lt hg, idx, hidx, hxor, hp_eq, ?_⟩
      rwa [List.getElem_append_left hlt]
    · have hge : ((List.range m).map step).flatten.length ≤ p := Nat.le_of_not_lt hlt
      have hstep_eq : step m = gateReqs k n m labels ws gates[m] := by
        simp [step, List.getD_eq_getElem?_getD, hmlt]
      have hlen_step : (step m).length = if isXorTable gates[m].2.2 then 0 else 8 := by
        rw [hstep_eq, gateReqs_length]
      have hxor : isXorTable gates[m].2.2 = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        rw [hc, ite_eq_left rfl] at hlen_step
        omega
      rw [hxor, ite_eq_right Bool.false_ne_true] at hlen_step
      have hp' : p - 8 * nonXorRank free m < 8 := by
        rw [hpre, hlen_step] at hp
        omega
      refine ⟨m, Nat.lt_succ_self m, p - 8 * nonXorRank free m, hp', hxor,
        by omega, ?_⟩
      rw [List.getElem_append_right hge]
      simp only [hpre, hstep_eq]
      exact gateReqs_getElem hxor hp' _

end Helpers

/-! ### Legality -/

section Legality

variable (hash : List Bool → List Bool → List Bool)

/-- Tweak uniqueness predicate for a flat request list: every request has length `2 k + 3` and
distinct indices carry distinct `k`-bit tweaks. -/
private def HasUniqueTweaks (k : ℕ) (reqs : List (List Bool)) : Prop :=
  ∀ i (hi : i < reqs.length) j (hj : j < reqs.length),
    reqs[i].length = 2 * k + 3 ∧ (i ≠ j →
      (reqs[i].drop (k + 2)).take k ≠ (reqs[j].drop (k + 2)).take k)

private theorem hasUniqueTweaks_allReqs (k : ℕ) (f : ValidCircuit) (ws coins : List Bool)
    (hk : 8 * f.1.q ≤ 2 ^ k) :
    HasUniqueTweaks k (allReqs k f.1.n f.1.gateList
      (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q) ws) := by
  let labels := simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q
  have hlen : ∀ (g : ℕ) (hg : g < f.1.gateList.length),
      (labels.getD (f.1.gateList[g].1 - 1) []).length = k + 2 ∧
      (labels.getD (f.1.gateList[g].2.1 - 1) []).length = k + 2 := by
    intro g hg
    have hgq : g < f.1.q := by simpa [ConventionalCircuit.length_gateList] using hg
    have hA₁ := f.2.one_le_A ⟨g, hgq⟩
    have hAB := f.2.A_lt_B ⟨g, hgq⟩
    have hBg := f.2.B_lt_gate ⟨g, hgq⟩
    simp only [ConventionalCircuit.topo] at hA₁ hAB hBg
    simp only [ConventionalCircuit.gateList, List.getElem_ofFn]
    exact ⟨length_getD_simPropWords_q k f coins (by omega),
      length_getD_simPropWords_q k f coins (by omega)⟩
  intro i hi j hj
  obtain ⟨gi, hgi, idx_i, hidx_i, _, hi_eq, hreq_i⟩ :=
    allReqs_lookup k f.1.n f.1.gateList labels ws hi
  obtain ⟨gj, hgj, idx_j, hidx_j, _, hj_eq, hreq_j⟩ :=
    allReqs_lookup k f.1.n f.1.gateList labels ws hj
  obtain ⟨hai, hbi⟩ := hlen gi hgi
  obtain ⟨haj, hbj⟩ := hlen gj hgj
  refine ⟨?_, fun hne => ?_⟩
  · rw [hreq_i]
    exact length_slotReq hai hbi
  · rw [hreq_i, hreq_j, gateReqSlot, gateReqSlot, tweak_slotReq hai hbi, tweak_slotReq haj hbj]
    intro htw
    have hgi_q : gi < f.1.q := by simpa [ConventionalCircuit.length_gateList] using hgi
    have hgj_q : gj < f.1.q := by simpa [ConventionalCircuit.length_gateList] using hgj
    have hb₁ : 8 * gi + 2 * (idx_i / 2) + idx_i % 2 < 2 ^ k := by omega
    have hb₂ : 8 * gj + 2 * (idx_j / 2) + idx_j % 2 < 2 ^ k := by omega
    have heq_nat := BitString.lowBits_injective_of_lt hb₁ hb₂ htw
    have hgg : gi = gj := by omega
    have hidx_eq : idx_i = idx_j := by omega
    subst hgg hidx_eq
    exact hne (hi_eq.trans hj_eq.symm)

private theorem tweakCost_req_le (k : ℕ) (t : BitString k) (req : List Bool)
    (hlen : req.length = 2 * k + 3) :
    CCR.tweakCost k t ((), req) ≤
      if (req.drop (k + 2)).take k = List.ofFn t then 1 else 0 := by
  unfold CCR.tweakCost
  split_ifs with h₁ h₂ <;> simp_all

private theorem isCostBounded_iterate_replyStep (k : ℕ) (reqs : List (List Bool))
    (htw : HasUniqueTweaks k reqs) (t : BitString k) {m : ℕ} (hm : m ≤ reqs.length) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (CCR.tweakCost k t))
      (OracleComp.iterate m (replyStep k reqs) [])
      (if ∃ i < m, ∃ hi : i < reqs.length, (reqs[i].drop (k + 2)).take k = List.ofFn t
        then 1 else 0) ∧
    ∀ rs ∈ (OracleComp.iterate m (replyStep k reqs) []).support, rs.length = m := by
  induction m with
  | zero =>
    refine ⟨OracleComp.IsCostBounded.pure _ _, fun rs hrs => ?_⟩
    rw [OracleComp.iterate_zero] at hrs
    rw [OracleComp.eq_of_mem_supportWith_pure hrs]
    rfl
  | succ m ih =>
    obtain ⟨hcost, hlen⟩ := ih (Nat.le_of_succ_le hm)
    have hmlt : m < reqs.length := hm
    rw [OracleComp.iterate_succ]
    refine ⟨(hcost.bind_on_support
        (m := if (reqs[m].drop (k + 2)).take k = List.ofFn t then 1 else 0)
        fun rs hrs => ?_).mono ?_, fun rs hrs => ?_⟩
    · have hrs_len : rs.length = m := hlen rs hrs
      have hget : reqs.getD rs.length [] = reqs[m] := by
        rw [hrs_len, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt, Option.getD_some]
      refine (((OracleComp.isCostBounded_map_iff _ _ _).mpr
        ((OracleComp.isCostBounded_map_iff _ _ _).mpr
          (ProbOracleComp.isCostBounded_query _ _)))).mono ?_
      rw [hget]
      have hc := tweakCost_req_le k t reqs[m] (htw m hmlt m hmlt).1
      omega
    · by_cases hprev : ∃ i < m, ∃ hi : i < reqs.length,
          (reqs[i].drop (k + 2)).take k = List.ofFn t
      · obtain ⟨i, hi_m, hi_len, hti⟩ := hprev
        have hm_ne : ¬ (reqs[m].drop (k + 2)).take k = List.ofFn t := fun htm =>
          (htw i hi_len m hmlt).2 (by omega) (hti.trans htm.symm)
        have hnext : ∃ i < m + 1, ∃ hi : i < reqs.length,
            (reqs[i].drop (k + 2)).take k = List.ofFn t := ⟨i, by omega, hi_len, hti⟩
        simp only [show ∃ i < m, ∃ hi : i < reqs.length,
            (reqs[i].drop (k + 2)).take k = List.ofFn t from ⟨i, hi_m, hi_len, hti⟩,
          hm_ne, hnext, ↓reduceIte, le_refl]
      · by_cases hm_eq : (reqs[m].drop (k + 2)).take k = List.ofFn t
        · have hnext : ∃ i < m + 1, ∃ hi : i < reqs.length,
              (reqs[i].drop (k + 2)).take k = List.ofFn t := ⟨m, by omega, hmlt, hm_eq⟩
          simp only [hprev, hm_eq, hnext, ↓reduceIte, le_refl]
        · have hnext : ¬ ∃ i < m + 1, ∃ hi : i < reqs.length,
              (reqs[i].drop (k + 2)).take k = List.ofFn t := by
            rintro ⟨i, hi_succ, hi_len, hti⟩
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi_succ) with hi_m | rfl
            · exact hprev ⟨i, hi_m, hi_len, hti⟩
            · exact hm_eq hti
          simp only [hprev, hm_eq, hnext, ↓reduceIte, le_refl]
    · obtain ⟨st, hst, hstep⟩ := OracleComp.mem_supportWith_bind_iff.mp hrs
      unfold replyStep replyStepWord at hstep
      obtain ⟨reply, -, hstep⟩ := OracleComp.mem_supportWith_map_iff.mp hstep
      rw [← hstep, List.length_append, List.length_singleton, hlen st hst]

/-- Library infrastructure (no cited result): **Legality of the reduction.** At every level `k`
and for every `prv.sim` adversary `B`, the adapted reduction asks each `k`-bit tweak at most once on
every execution path. -/
theorem isTweakUnique_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k : ℕ) :
    CCR.IsTweakUnique ((CCR.codec k).adapt (prvSimReduction hash B k [])) := by
  intro t
  refine (CCR.codec k).isCostBounded_adapt (wordCost := CCR.tweakCost k t)
    (CCR.tweakCost_encodeQuery k t) ?_
  refine ((ProbOracleComp.isCostBounded_sample _ _).bind (m := 1) fun ⟨query, state⟩ => ?_).mono
    (by omega)
  dsimp only
  split_ifs with hguard
  · refine ((ProbOracleComp.isCostBounded_sample (CCR.tweakCost k t) _).bind (m := 1)
        fun coins => ?_).mono (by omega)
    let labels := simPropWords k query.fn.1.topo (xorFlags query.fn.1.gateList) coins query.fn.1.q
    let reqs := allReqs k query.fn.1.n query.fn.1.gateList labels
      (query.fn.1.wires query.input query.fn.1.q)
    have hcost := (isCostBounded_iterate_replyStep k reqs
      (hasUniqueTweaks_allReqs k query.fn _ coins hguard.2) t le_rfl).1
    refine (hcost.bind fun _ => ProbOracleComp.isCostBounded_sample _ _).mono ?_
    split_ifs <;> omega
  · exact (ProbOracleComp.isCostBounded_sample (CCR.tweakCost k t)
      ((B k).guess state none)).mono (by omega)

private theorem length_transcript_iterate_replyStep {State : Type}
    (oracle : Unit × List Bool → StateT State PMF (List Bool))
    (k : ℕ) (reqs : List (List Bool)) (m : ℕ) (init : List (List Bool)) (s : State)
    (tr₀ : OracleComp.Transcript fun _ : Unit × List Bool => List Bool)
    {rs : List (List Bool)} {s' : State}
    {tr : OracleComp.Transcript fun _ : Unit × List Bool => List Bool}
    (h : (rs, s', tr) ∈ (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
      (OracleComp.iterate m (replyStep k reqs) init) (s, tr₀)).support) :
    tr.length = tr₀.length + m := by
  induction m generalizing init s tr₀ rs s' tr with
  | zero =>
    simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure, PMF.support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨-, -, rfl⟩
    rfl
  | succ m ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.runWith_bind] at h
    obtain ⟨⟨st₁, s₁, tr₁⟩, h₁, h₂⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    have htr₁ := ih init s tr₀ h₁
    simp only [replyStep, replyStepWord, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      OracleComp.withTranscript, PMF.map_comp, Function.comp_def] at h₂
    obtain ⟨⟨reply, s₂⟩, _, hmap⟩ := (PMF.mem_support_map_iff _ _ _).mp h₂
    rcases hmap with ⟨-, -, rfl⟩
    simp only [List.length_cons, htr₁]
    omega

/-- Library infrastructure (no cited result): on any logged execution of
`prvSimReduction hash B k []` against a stateful word oracle, the adversary's choice `(q, st)`
determines the request trace length: `8` requests per non-XOR gate of `q.fn` when `q` is valid and
`8 * q.fn.1.q ≤ 2 ^ k`, and `0` otherwise. -/
theorem exists_of_mem_support_runWith_prvSimReduction {σ State : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (k : ℕ)
    (oracle : Unit × List Bool → StateT State PMF (List Bool)) {s s' : State} {result : Bool}
    {transcript : OracleComp.Transcript fun _ : Unit × List Bool => List Bool}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (prvSimReduction hash B k []) (s, [])).support) :
    ∃ q st, (q, st) ∈ (ProbComp.eval ((B k).choose ())).support ∧
      transcript.length =
        if q.input.length = q.fn.1.n ∧ 8 * q.fn.1.q ≤ 2 ^ k then
          8 * (phiXor.phi q.fn).free.count false
        else 0 := by
  unfold prvSimReduction at hmem
  rw [ProbOracleComp.runWith_bind] at hmem
  obtain ⟨⟨⟨q, st⟩, _, _⟩, h₁, h₂⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmem
  rw [ProbOracleComp.runWith_sample] at h₁
  obtain ⟨_, hq', hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp h₁
  rcases Prod.mk.inj hpair with ⟨rfl, rfl, rfl⟩
  refine ⟨q, st, hq', ?_⟩
  dsimp only at h₂
  split_ifs at h₂ ⊢ with hguard
  · rw [ProbOracleComp.runWith_bind] at h₂
    obtain ⟨⟨coins, _, _⟩, hc, h₃⟩ := (PMF.mem_support_bind_iff _ _ _).mp h₂
    rw [ProbOracleComp.runWith_sample] at hc
    obtain ⟨_, -, hc_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
    rcases Prod.mk.inj hc_eq with ⟨-, rfl, rfl⟩
    rw [ProbOracleComp.runWith_bind] at h₃
    obtain ⟨⟨rs, _, _⟩, hrs, h₄⟩ := (PMF.mem_support_bind_iff _ _ _).mp h₃
    rw [ProbOracleComp.runWith_sample] at h₄
    obtain ⟨_, -, hb_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp h₄
    rcases Prod.mk.inj hb_eq with ⟨-, -, rfl⟩
    have hlen : (prvSimReqs k q.fn.1 (q.fn.1.wires q.input q.fn.1.q) coins).length =
        8 * (phiXor.phi q.fn).free.count false := by
      rw [prvSimReqs, allReqs, allReqs_prefix_length _ _ _ _ _ le_rfl, xorFlags_gateList,
        nonXorRank, List.take_of_length_le (by simp [phiXor])]
    simpa [hlen] using length_transcript_iterate_replyStep oracle k _ _ [] s [] hrs
  · rw [ProbOracleComp.runWith_sample] at h₂
    obtain ⟨_, -, hb_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp h₂
    rcases Prod.mk.inj hb_eq with ⟨-, -, rfl⟩
    rfl

end Legality

/-! ### Against a fixed oracle -/

section Run

private theorem uniformList_map_simBaseLabels (k : ℕ) (f : ValidCircuit) :
    (BitString.uniformList ((f.1.n + f.1.q) * (k + 2))).map
        (fun coins => (simBaseLabels k coins :
          Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool)) =
      PMF.uniformOfFintype (Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) := by
  let e : Wire f.1.n (toCircuit f).size ≃ Fin (f.1.n + f.1.q) :=
    (Wire.equivFin f.1.n (toCircuit f).size).trans (finCongr (by rw [size_toCircuit]))
  let E : (Wire f.1.n (toCircuit f).size → BitString (k + 2)) ≃
      (Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) :=
    Equiv.arrowCongr (Equiv.refl _) (labelEquiv k)
  have hcomp : (fun coins => (simBaseLabels k coins :
        Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool)) =
      (E : _ → _) ∘ fun coins w =>
        BitString.ofList (k + 2) (BitString.listRow (k + 2) (e w) coins) := by
    funext coins w
    rfl
  rw [hcomp, ← PMF.map_comp, BitString.uniformList_map_listRow_equiv e (k + 2),
    PMF.uniformOfFintype_map_equiv E]

private theorem testBit_decide_lt_four {i : ℕ} (hi : i < 4) :
    (i.testBit 1 = decide (2 ≤ i)) ∧ (i.testBit 0 = decide (i % 2 = 1)) := by
  interval_cases i <;> decide

private theorem simPropWords_ofFn_labelBits (k : ℕ) (f : ValidCircuit) (coins : List Bool) :
    simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q =
      List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
          (Wire.ofNat v v.isLt)) := by
  rw [xorFlags_gateList]
  exact simPropWords_q k f coins

private theorem validCircuit_gate_bounds (f : ValidCircuit) (g : Fin (toCircuit f).size) :
    (g : ℕ) < f.1.q ∧ 1 ≤ f.1.A (g.cast (size_toCircuit f)) ∧
      f.1.A (g.cast (size_toCircuit f)) < f.1.B (g.cast (size_toCircuit f)) ∧
      f.1.B (g.cast (size_toCircuit f)) < f.1.n + 1 + g.val := by
  have hsize := size_toCircuit f
  have hgq : (g : ℕ) < f.1.q := by have := g.isLt; omega
  have hA₁ := f.2.one_le_A (g.cast (size_toCircuit f))
  have hAB := f.2.A_lt_B (g.cast (size_toCircuit f))
  have hBg := f.2.B_lt_gate (g.cast (size_toCircuit f))
  simp only [ConventionalCircuit.topo, Fin.val_cast] at hA₁ hAB hBg
  exact ⟨hgq, hA₁, hAB, hBg⟩

private theorem wire_toCircuit_input (f : ValidCircuit) (g : Fin (toCircuit f).size)
    (s : Fin 2) :
    (toCircuit f).topology.wires g (Fin.cast (arity_topology_toCircuit f g).symm s) =
      Wire.ofNat ((if s = 0 then f.1.A (g.cast (size_toCircuit f))
        else f.1.B (g.cast (size_toCircuit f))) - 1) (by
          have hsize := size_toCircuit f
          obtain ⟨hgq, hA₁, hAB, hBg⟩ := validCircuit_gate_bounds f g
          fin_cases s <;> simp <;> omega) := by
  have hsize := size_toCircuit f
  obtain ⟨hgq, hA₁, hAB, hBg⟩ := validCircuit_gate_bounds f g
  fin_cases s
  · exact (congrArg ((toCircuit f).topology.wires g) (Fin.ext rfl)).trans
      (wires_toCircuit_zero f g (by omega))
  · exact (congrArg ((toCircuit f).topology.wires g) (Fin.ext rfl)).trans
      (wires_toCircuit_one f g (by omega))

private theorem simPropWords_getD_input (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) (s : Fin 2) :
    (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
        ((if s = 0 then f.1.A (g.cast (size_toCircuit f))
          else f.1.B (g.cast (size_toCircuit f))) - 1) [] =
      labelBits (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
        ((toCircuit f).topology.wires g (Fin.cast (arity_topology_toCircuit f g).symm s))) := by
  rw [simPropWords_ofFn_labelBits]
  fin_cases s
  · exact getD_ofFn_wire_A f _ g
  · exact getD_ofFn_wire_B f _ g

private theorem flipped_garbledRowOf_toCircuit (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) (hg : freeCircuit f g = false) {i : ℕ} (hi : i < 4)
    (s : Fin 2) :
    flipped (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
        (garbledRowOf (toCircuit f).topology g hg i)
        (Fin.cast (arity_topology_toCircuit f g).symm s) =
      ((if s = 0 then decide (2 ≤ i) else decide (i % 2 = 1)) ^^
        HalfGates.colourWord k
          ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
            ((if s = 0 then f.1.A (g.cast (size_toCircuit f))
              else f.1.B (g.cast (size_toCircuit f))) - 1) [])) := by
  have harity := arity_topology_toCircuit f g
  have htb := testBit_decide_lt_four hi
  rw [simPropWords_getD_input k f coins g s, HalfGates.colourWord_labelBits]
  dsimp only [flipped, garbledRowOf]
  rw [Bool.add_eq_xor]
  fin_cases s <;> simp [harity, htb.1, htb.2]

private theorem wires_getD_input {f : ValidCircuit} {x : List Bool} (hx : x.length = f.1.n)
    (g : Fin (toCircuit f).size) (s : Fin 2) :
    (f.1.wires x f.1.q).getD ((if s = 0 then f.1.A (g.cast (size_toCircuit f))
        else f.1.B (g.cast (size_toCircuit f))) - 1) false =
      (toCircuit f).program.trace fullInterpretation (BitString.ofList f.1.n x)
        ((toCircuit f).topology.wires g (Fin.cast (arity_topology_toCircuit f g).symm s)) := by
  rw [wire_toCircuit_input, trace_toCircuit, BitString.ofFn_ofList hx, Wire.toNat_ofNat]

private theorem slotReq_eq_encodeQuery {k : ℕ} {f : ValidCircuit} {x : List Bool}
    (hx : x.length = f.1.n) (coins : List Bool) (g : Fin (toCircuit f).size)
    (hg : freeCircuit f g = false) {i : ℕ} (hi : i < 4) (s : Fin 2) :
    let labels := simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q
    let ws := f.1.wires x f.1.q
    let gc := g.cast (size_toCircuit f)
    let A := propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
    let r := garbledRowOf (toCircuit f).topology g hg i
    let p : GarbledSlot (toCircuit f).topology (freeCircuit f) :=
      ⟨r, Fin.cast (arity_topology_toCircuit f g).symm s⟩
    ((), slotReq k f.1.n labels ws g.val (f.1.A gc - 1) (f.1.B gc - 1)
      [f.1.G gc false false, f.1.G gc false true, f.1.G gc true false, f.1.G gc true true]
      i s.val) =
      (CCR.codec k).encodeQuery (CCR.keyOnlyEmbed _ _ (reductionQuery (toCircuit f)
        fullInterpretation (slotTweak (toCircuit f).topology (freeCircuit f) k)
        (BitString.ofList f.1.n x) A p)) := by
  have hsize := size_toCircuit f
  have harity := arity_topology_toCircuit f g
  have hgq : (g : ℕ) < f.1.q := by have := g.isLt; omega
  set A := propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
  have hla := simPropWords_getD_input k f coins g 0
  have hlb := simPropWords_getD_input k f coins g 1
  have hva := wires_getD_input hx g 0
  have hvb := wires_getD_input hx g 1
  have hf₀ := flipped_garbledRowOf_toCircuit k f coins g hg hi 0
  have hf₁ := flipped_garbledRowOf_toCircuit k f coins g hg hi 1
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide] at hla hlb hva hvb hf₀ hf₁
  have hvg : (f.1.wires x f.1.q).getD (f.1.n + g.val) false =
      (toCircuit f).program.trace fullInterpretation (BitString.ofList f.1.n x) (.gate g) := by
    have hwg : (Wire.ofNat (f.1.n + g.val) (by omega) : Wire f.1.n (toCircuit f).size) =
        .gate g := Wire.toNat_injective (by simp)
    rw [← hwg, trace_toCircuit, BitString.ofFn_ofList hx, Wire.toNat_ofNat]
  have htake_lbl (y : BitString (k + 1) × Bool) : (labelBits y).take (k + 1) = List.ofFn y.1 := by
    rw [labelBits_apply, List.take_left' (List.length_ofFn)]
  have hrowBit : ((f.1.wires x f.1.q).getD (f.1.n + g.val) false ^^
      [f.1.G (g.cast (size_toCircuit f)) false false,
       f.1.G (g.cast (size_toCircuit f)) false true,
       f.1.G (g.cast (size_toCircuit f)) true false,
       f.1.G (g.cast (size_toCircuit f)) true true].getD
        ((if (decide (2 ≤ i) ^^ HalfGates.colourWord k
            ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
              (f.1.A (g.cast (size_toCircuit f)) - 1) [])) ^^
            (f.1.wires x f.1.q).getD (f.1.A (g.cast (size_toCircuit f)) - 1) false then 2 else 0) +
          (if (decide (i % 2 = 1) ^^ HalfGates.colourWord k
            ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
              (f.1.B (g.cast (size_toCircuit f)) - 1) [])) ^^
            (f.1.wires x f.1.q).getD (f.1.B (g.cast (size_toCircuit f)) - 1) false then 1 else 0))
        false) =
      rowBit (toCircuit f) fullInterpretation (BitString.ofList f.1.n x) A
        (garbledRowOf (toCircuit f).topology g hg i) := by
    rw [getD_table, ← hf₀, ← hf₁, hva, hvb, hvg]
    dsimp only [rowBit, GarbledRow.gate, garbledRowOf]
    erw [fullInterpretation_lines_toCircuit f g]
    simp only [Bool.add_eq_xor]
    rfl
  dsimp only [slotReq]
  rw [hrowBit]
  have htw : PointPermute.tweak k g.val i s.val =
      List.ofFn (slotTweak (toCircuit f).topology (freeCircuit f) k
        ⟨garbledRowOf (toCircuit f).topology g hg i, Fin.cast harity.symm s⟩) :=
    (ofFn_slotTweak_garbledRowOf f k g hg hi (Fin.cast harity.symm s)).symm
  have hkey : (if s.val = 0 then
        (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
          (f.1.A (g.cast (size_toCircuit f)) - 1) []
      else (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
        (f.1.B (g.cast (size_toCircuit f)) - 1) []).take (k + 1) ++ [true] =
      labelBits ((reductionQuery (toCircuit f) fullInterpretation
        (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.n x) A
        ⟨garbledRowOf (toCircuit f).topology g hg i,
          Fin.cast harity.symm s⟩).label, true) := by
    fin_cases s
    · simp only [↓reduceIte, hla, htake_lbl, reductionQuery]; rfl
    · simp only [one_ne_zero, ↓reduceIte, hlb, htake_lbl, reductionQuery]; rfl
  have hbit : ((if s.val = 0 then
        decide (2 ≤ i) ^^ HalfGates.colourWord k
          ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
            (f.1.A (g.cast (size_toCircuit f)) - 1) [])
      else !(decide (2 ≤ i) ^^ HalfGates.colourWord k
          ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
            (f.1.A (g.cast (size_toCircuit f)) - 1) [])) &&
        (decide (i % 2 = 1) ^^ HalfGates.colourWord k
          ((simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).getD
            (f.1.B (g.cast (size_toCircuit f)) - 1) []))) &&
        rowBit (toCircuit f) fullInterpretation (BitString.ofList f.1.n x) A
          (garbledRowOf (toCircuit f).topology g hg i)) =
      (reductionQuery (toCircuit f) fullInterpretation
        (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.n x) A
        ⟨garbledRowOf (toCircuit f).topology g hg i,
          Fin.cast harity.symm s⟩).bit := by
    rw [← hf₀, ← hf₁]
    fin_cases s
    · dsimp only [reductionQuery, isFirst]
      rw [ite_eq_left rfl, decide_eq_true fun j hj => by
        have hlt : j.val < 0 := Fin.lt_def.mp hj; omega, Bool.and_true]
      rfl
    · simp only [one_ne_zero, ↓reduceIte, reductionQuery, isFirst]
      change ((!flipped A (garbledRowOf (toCircuit f).topology g hg i) (Fin.cast harity.symm 0) &&
          flipped A (garbledRowOf (toCircuit f).topology g hg i) (Fin.cast harity.symm 1)) && _) =
        ((flipped A (garbledRowOf (toCircuit f).topology g hg i) (Fin.cast harity.symm 1) && _) &&
          _)
      rw [Bool.and_comm (flipped A (garbledRowOf (toCircuit f).topology g hg i)
        (Fin.cast harity.symm 1))]
      congr 2; symm
      cases hb : flipped A (garbledRowOf (toCircuit f).topology g hg i) (Fin.cast harity.symm 0)
      · exact decide_eq_true fun j hj =>
          (Fin.ext (Nat.lt_one_iff.mp (Fin.lt_def.mp hj)) : j = Fin.cast harity.symm 0) ▸ hb
      · exact decide_eq_false fun hp => Bool.noConfusion
          (hb.symm.trans (hp _ (Fin.lt_def.mpr (show (0 : ℕ) < 1 by decide))))
  erw [htw, hkey, hbit]
  simp only [CCR.codec, CCR.keyOnlyEmbed, labelBits_apply, List.append_assoc,
    List.singleton_append]
  rfl

private noncomputable def oracleReplies (k : ℕ) (f : ValidCircuit) (x coins : List Bool)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool) :
    List (List Bool) :=
  (allReqs k f.1.n f.1.gateList (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q)
      (f.1.wires x f.1.q)).map fun req =>
    match (CCR.codec k).decodeQuery ((), req) with
    | some q => labelBits (O q)
    | none => []

private theorem redGate_eq (hash : List Bool → List Bool → List Bool) {k : ℕ} {f : ValidCircuit}
    {x : List Bool} (hx : x.length = f.1.n)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool)
    (coins : List Bool) (g : Fin (toCircuit f).size) :
    let free := xorFlags f.1.gateList
    let labels := simPropWords k f.1.topo free coins f.1.q
    let rs := oracleReplies k f x coins O
    let A := propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
    let O' : GarbledSlot (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool :=
      fun p => O (CCR.keyOnlyEmbed _ _ (reductionQuery (toCircuit f) fullInterpretation
        (slotTweak (toCircuit f).topology (freeCircuit f) k)
        (BitString.ofList f.1.n x) A p))
    encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size) (toCircuit f).topology
        (freeCircuit f) (reductionTable (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k) A O') g =
      BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
          (f.1.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
          (f.1.B (g.cast (size_toCircuit f))) ++
        (List.ofFn fun i : Fin 4 => redRowData hash k f.1.n free labels rs
          (g.cast (size_toCircuit f)) (f.1.A (g.cast (size_toCircuit f)) - 1)
          (f.1.B (g.cast (size_toCircuit f)) - 1) i).flatten := by
  have hsize := size_toCircuit f
  have harity := arity_topology_toCircuit f g
  obtain ⟨hgq, hA₁, hAB, hBg⟩ := validCircuit_gate_bounds f g
  dsimp only
  set free := xorFlags f.1.gateList
  set labels := simPropWords k f.1.topo free coins f.1.q
  set ws := f.1.wires x f.1.q
  set reqs := allReqs k f.1.n f.1.gateList labels ws
  set rs := oracleReplies k f x coins O
  set A := propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
  have hfree_eq : free.getD g.val false = freeCircuit f g := by
    simp only [free, xorFlags_gateList, phiXor, freeCircuit, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hgq, ↓reduceDIte, Option.getD_some]
    rfl
  rw [encodeGate_toCircuit k f _ g]
  dsimp only [redRowData]
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_cons, List.flatten_cons, List.flatten_cons, List.flatten_nil]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_cast, ↓reduceIte, hfree_eq, List.append_nil]
  by_cases hg : freeCircuit f g = true
  · simp [hg, show isXorGate f.1 (g.cast (size_toCircuit f)) = true from hg]
  · have hg' : freeCircuit f g = false := Bool.eq_false_iff.mpr hg
    simp only [hg', Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, List.singleton_append,
      List.append_assoc]
    congr 2
    have hlout : labels.getD (f.1.n + g.val) [] = labelBits (A (.gate g)) := by
      rw [show labels = simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q from rfl,
        simPropWords_ofFn_labelBits, getD_ofFn_wire_gate]
    have hmem_free : free[g.val]'(by
        simp [free, xorFlags, ConventionalCircuit.length_gateList, hgq]) = false := by
      simpa [free, xorFlags_gateList, phiXor, freeCircuit, Fin.cast] using hg'
    have hxor_g : isXorTable (f.1.gateList[g.val]'(by
        simpa [ConventionalCircuit.length_gateList] using hgq)).2.2 = false := by
      simpa [free, xorFlags] using hmem_free
    have hrow_eq (i : ℕ) (hi : i < 4) :
        labelBits (reductionTable (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k) A
          (fun p => O (CCR.keyOnlyEmbed _ _ (reductionQuery (toCircuit f) fullInterpretation
            (slotTweak (toCircuit f).topology (freeCircuit f) k)
            (BitString.ofList f.1.n x) A p))) (garbledRowOf (toCircuit f).topology g hg' i)) =
          redRow hash k f.1.n free labels rs g.val (f.1.A (g.cast (size_toCircuit f)) - 1)
            (f.1.B (g.cast (size_toCircuit f)) - 1) i := by
      have hrs_slot (s : Fin 2) :
          rs.getD (8 * nonXorRank free g.val + 2 * i + s.val) [] =
            labelBits (O (CCR.keyOnlyEmbed _ _ (reductionQuery (toCircuit f) fullInterpretation
              (slotTweak (toCircuit f).topology (freeCircuit f) k)
              (BitString.ofList f.1.n x) A
              ⟨garbledRowOf (toCircuit f).topology g hg' i, Fin.cast harity.symm s⟩))) := by
        have hidx_lt : 2 * i + s.val < 8 := by omega
        have hlt_rank := nonXorRank_lt free
          (by simp [free, xorFlags, ConventionalCircuit.length_gateList, hgq]) hmem_free hgq
        have hlen_reqs : 8 * nonXorRank free g.val + (2 * i + s.val) < reqs.length := by
          rw [allReqs_length, ConventionalCircuit.length_gateList]
          change _ < 8 * nonXorRank free f.1.q; omega
        have hget_req : reqs[8 * nonXorRank free g.val + (2 * i + s.val)]'hlen_reqs =
            slotReq k f.1.n labels ws g.val (f.1.A (g.cast hsize) - 1)
              (f.1.B (g.cast hsize) - 1)
              [f.1.G (g.cast hsize) false false, f.1.G (g.cast hsize) false true,
               f.1.G (g.cast hsize) true false, f.1.G (g.cast hsize) true true] i s.val := by
          have h := allReqs_getD_slot k f.1.n f.1.gateList labels ws
            (by simpa [ConventionalCircuit.length_gateList] using hgq) hxor_g hidx_lt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_reqs,
            Option.getD_some] at h
          rw [h, gateReqSlot, show (2 * i + s.val) / 2 = i by omega,
            show (2 * i + s.val) % 2 = s.val by omega]
          simp only [ConventionalCircuit.gateList, List.getElem_ofFn]; rfl
        have hdec := ((CCR.codec k).decodeQuery_eq_some_iff _ _).mpr
          (slotReq_eq_encodeQuery hx coins g hg' hi s).symm
        dsimp only [rs, oracleReplies]
        rw [show 8 * nonXorRank free g.val + 2 * i + s.val =
            8 * nonXorRank free g.val + (2 * i + s.val) by omega,
          List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simpa [List.length_map] using hlen_reqs),
          Option.getD_some, List.getElem_map, hget_req]
        change (match (CCR.codec k).decodeQuery
            ((), slotReq k f.1.n labels ws g.val _ _ _ i s.val) with
          | some q => labelBits (O q)
          | none => []) = _
        rw [hdec]
      have harity_row : (toCircuit f).topology.arity
          (garbledRowOf (toCircuit f).topology g hg' i).gate = 2 := harity
      have hslot_side (s : Fin 2) :
          labelBits (if flipped A (garbledRowOf (toCircuit f).topology g hg' i)
                (Fin.cast harity_row.symm s) = true then
              O (CCR.keyOnlyEmbed _ _ (reductionQuery (toCircuit f) fullInterpretation
                (slotTweak (toCircuit f).topology (freeCircuit f) k)
                (BitString.ofList f.1.n x) A
                ⟨garbledRowOf (toCircuit f).topology g hg' i, Fin.cast harity_row.symm s⟩))
            else CCR.atLevel hash k ((A ((toCircuit f).topology.wires
                (↑(garbledRowOf (toCircuit f).topology g hg' i).fst)
                (Fin.cast harity_row.symm s))).1, false)
              (slotTweak (toCircuit f).topology (freeCircuit f) k
                ⟨garbledRowOf (toCircuit f).topology g hg' i, Fin.cast harity_row.symm s⟩)) =
            if ((if s = 0 then decide (2 ≤ i) else decide (i % 2 = 1)) ^^
                HalfGates.colourWord k (labels.getD ((if s = 0 then f.1.A (g.cast hsize)
                  else f.1.B (g.cast hsize)) - 1) [])) = true then
              rs.getD (8 * nonXorRank free g.val + 2 * i + s.val) []
            else keyHashWord hash k (labels.getD ((if s = 0 then f.1.A (g.cast hsize)
                else f.1.B (g.cast hsize)) - 1) []) (PointPermute.tweak k g.val i s.val) := by
        rw [apply_ite labelBits]
        refine ite_congr
          (congrArg (· = true) (flipped_garbledRowOf_toCircuit k f coins g hg' hi s))
          (fun _ => (hrs_slot s).symm) (fun _ => ?_)
        rw [labelBits_atLevel_key]
        erw [ofFn_slotTweak_garbledRowOf f k g hg' hi (Fin.cast harity.symm s),
          ← simPropWords_getD_input k f coins g s]
        rfl
      dsimp only [redRow]
      rw [reductionTable]
      dsimp only [GarbledRow.gate]
      change labelBits (A (.gate g) + ∑ x_1 : Fin ((toCircuit f).topology.arity
          (garbledRowOf (toCircuit f).topology g hg' i).gate), _) = _
      rw [labelBits_add, ← Fin.sum_congr' _ harity_row.symm, Fin.sum_univ_two, labelBits_add, hlout]
      exact congrArg (List.zipWith xor (labelBits (A (.gate g))) ·)
        (congrArg₂ (List.zipWith xor)
          (by simpa only [Fin.val_zero, Nat.add_zero, ↓reduceIte, Fin.isValue] using hslot_side 0)
          (by simpa only [Fin.val_one, one_ne_zero, ↓reduceIte, Fin.isValue] using hslot_side 1))
    simp only [show isXorGate f.1 (g.cast (size_toCircuit f)) = false from hg', Nat.reduceAdd,
      Nat.add_one_ne_zero, ↓reduceIte, List.nil_append, List.cons_append]
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
      List.flatten_cons, List.flatten_cons, List.flatten_cons, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    simp only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
    exact congrArg (false :: ·) (congrArg₂ (· ++ ·) (hrow_eq 0 (by omega))
      (congrArg₂ (· ++ ·) (hrow_eq 1 (by omega))
        (congrArg₂ (· ++ ·) (hrow_eq 2 (by omega)) (hrow_eq 3 (by omega)))))

private theorem redView_eq (hash : List Bool → List Bool → List Bool) {k : ℕ} {f : ValidCircuit}
    {x : List Bool} (hx : x.length = f.1.n)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool)
    (coins : List Bool) :
    redView hash k f.1 (f.1.wires x f.1.q) coins (oracleReplies k f x coins O) =
      viewWord k (toCircuit f).topology (freeCircuit f)
        (FreeXOR.reductionView (toCircuit f).topology
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k)
          ((toCircuit f).eval fullInterpretation (BitString.ofList f.1.n x))
          (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
          fun p => O (CCR.keyOnlyEmbed _ _ (reductionQuery (toCircuit f) fullInterpretation
            (slotTweak (toCircuit f).topology (freeCircuit f) k)
            (BitString.ofList f.1.n x)
            (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)) p))) := by
  have hτ := (toCircuit f).isOrdered_topology
  have hgate (g : Fin f.1.q) : f.1.gateList.getD g (0, 0, []) =
      (f.1.A g, f.1.B g, [f.1.G g false false, f.1.G g false true, f.1.G g true false,
        f.1.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  have hlen : (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q).length =
      f.1.n + f.1.q :=
    length_simPropWords k f.1.topo (xorFlags f.1.gateList) coins le_rfl
  have hA₁ (g : Fin f.1.q) : 1 ≤ f.1.A g := f.2.one_le_A g
  have hAB (g : Fin f.1.q) : f.1.A g < f.1.B g := f.2.A_lt_B g
  have hBg (g : Fin f.1.q) : f.1.B g < f.1.n + 1 + g := f.2.B_lt_gate g
  dsimp only [redView, viewWord, FreeXOR.reductionView]
  rw [PrvView.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [ConventionalCircuit.length_gateList,
      PointPermute.bodyWith_eq_ofFn f.1.A f.1.B
        (fun g i => redRowData hash k f.1.n (xorFlags f.1.gateList)
          (simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q)
          (oracleReplies k f x coins O) g (f.1.A g - 1) (f.1.B g - 1) i)
        (fun g => by rw [hgate]) (fun g => by rw [hgate])
        (fun g i => by
          have ha := hA₁ g
          have hab := hAB g
          have hb := hBg g
          have hg := g.isLt
          rw [hlen]
          simp only [
            show min (f.1.n + f.1.q + 1) (f.1.A g) = f.1.A g from Nat.min_eq_right (by omega),
            show min (f.1.n + f.1.q + 1) (f.1.B g) = f.1.B g from Nat.min_eq_right (by omega)])]
    simp only [encodeFn]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      refine congrArg List.flatten (congrArg List.ofFn (funext fun g => ?_))
      rw [redGate_eq hash hx O coins (Fin.cast (size_toCircuit f).symm g)]
      have hcast : Fin.cast (size_toCircuit f) (Fin.cast (size_toCircuit f).symm g) = g :=
        Fin.ext rfl
      simp only [hcast]
  · rw [List.map_range_eq_ofFn]
    simp only [propagate_input hτ, simBaseLabels, Wire.toNat_input,
      labelBits_labelOfWord (PointPermute.length_simLabel k coins _)]
  · rw [List.map_range_eq_ofFn, ConventionalCircuit.length_gateList, simPropWords_ofFn_labelBits]
    refine congrArg List.ofFn (funext fun o => ?_)
    have hval : (f.1.wires x f.1.q).getD (f.1.n + f.1.q - f.1.m + o) false =
        (toCircuit f).eval fullInterpretation (BitString.ofList f.1.n x) o := by
      rw [← toNat_outputs_toCircuit, Circuit.eval, Function.comp_apply,
        ← BitString.ofFn_ofList hx, trace_toCircuit]
      simp [BitString.ofList_ofFn]
    rw [getD_ofFn_wire_output, hval, HalfGates.colourWord_labelBits, Bool.add_eq_xor]
    rfl

variable (hash) in
/-- Library infrastructure (no cited result): **The word reduction runs the typed reduction.**
Against every fixed full-label oracle `O`,
the reduction for `B` at parameter `k` runs `B`'s choice of `(f, x)`. When `x` has `f.n` bits and
`8 q ≤ 2 ^ k`, it runs the typed reduction `FreeXOR.reduction` on `toCircuit f` with key-only
queries lifted via `CCR.keyOnlyEmbed` and `B`'s guess on the view words; otherwise it runs `B`'s
guess on `⊥`. -/
theorem eval_run_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ) (k : ℕ)
    (O : CCR.Query (BitString (k + 1) × Bool) (BitString k) → BitString (k + 1) × Bool) :
    ProbComp.eval (((CCR.codec k).adapt (prvSimReduction hash B k [])).run
        fun q => pure (O q)) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n ∧ 8 * query.fn.1.q ≤ 2 ^ k then
          ProbComp.eval ((FreeXOR.reduction (toCircuit query.fn) fullInterpretation
            (fun key t => CCR.atLevel hash k (key, false) t)
            (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
            (BitString.ofList query.fn.1.n query.input)
            (fun V => (B k).guess state
              (some (viewWord k _ (freeCircuit query.fn) V)))).run
              fun q => pure (O (CCR.keyOnlyEmbed _ _ q)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [prvSimReduction, prvSimReqs, OracleCodec.run_adapt, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hguard
  swap
  · simp only [ProbOracleComp.run_sample]
  set f := query.fn
  set x := query.input
  have hx : x.length = f.1.n := hguard.1
  rw [eval_run_reduction]
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbComp.eval_bind,
    BitString.eval_sampleList]
  rw [← uniformList_map_simBaseLabels k f, PMF.bind_map]
  refine congrArg _ (funext fun coins => ?_)
  let labels := simPropWords k f.1.topo (xorFlags f.1.gateList) coins f.1.q
  let ws := f.1.wires x f.1.q
  let reqs := allReqs k f.1.n f.1.gateList labels ws
  let ans := oracleReplies k f x coins O
  have hO : ∀ i (hi : i < reqs.length),
      ((CCR.codec k).wordOracle fun q => (pure (O q) : ProbComp _)) ((), reqs.getD i []) =
        pure (ans.getD i []) := by
    intro i hi
    obtain ⟨g, hg, idx, hidx, hxor, _, hreq⟩ := allReqs_lookup k f.1.n f.1.gateList labels ws hi
    have hgq : g < f.1.q := by simpa [ConventionalCircuit.length_gateList] using hg
    let gFin : Fin (toCircuit f).size := ⟨g, by rw [size_toCircuit]; exact hgq⟩
    have hcast : gFin.cast (size_toCircuit f) = ⟨g, hgq⟩ := Fin.ext rfl
    have hfree_g : freeCircuit f gFin = false := by
      simpa [ConventionalCircuit.gateList, freeCircuit, isXorGate, hcast, isXorTable_eq] using hxor
    let sFin : Fin 2 := ⟨idx % 2, Nat.mod_lt _ (by decide)⟩
    have henc := slotReq_eq_encodeQuery (k := k) hx coins gFin hfree_g (i := idx / 2)
      (by omega) sFin
    dsimp only at henc
    have hreq_eq : reqs[i]'hi = slotReq k f.1.n labels ws gFin.val
        (f.1.A (gFin.cast (size_toCircuit f)) - 1) (f.1.B (gFin.cast (size_toCircuit f)) - 1)
        [f.1.G (gFin.cast (size_toCircuit f)) false false,
         f.1.G (gFin.cast (size_toCircuit f)) false true,
         f.1.G (gFin.cast (size_toCircuit f)) true false,
         f.1.G (gFin.cast (size_toCircuit f)) true true] (idx / 2) sFin.val := by
      rw [hreq, gateReqSlot]
      simp [ConventionalCircuit.gateList, gFin, sFin]
    have hia : i < ans.length := by simpa [ans, oracleReplies] using hi
    rw [← hreq_eq] at henc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia, Option.getD_some,
      henc, CCR.wordOracle_codec_encodeQuery]
    dsimp only [ans, oracleReplies]
    erw [List.getElem_map]
    have hdec := ((CCR.codec k).decodeQuery_eq_some_iff _ _).mpr henc.symm
    change (pure _ : ProbComp _) = pure (match (CCR.codec k).decodeQuery ((), reqs[i]) with
      | some q => labelBits (O q)
      | none => [])
    rw [hdec]
  unfold replyStep
  rw [run_iterate_replyStepWord (k + 2) reqs.length (fun idx => reqs.getD idx [])
      ((CCR.codec k).wordOracle fun q => (pure (O q) : ProbComp _))
      (fun idx => ans.getD idx []) hO, ProbComp.eval_pure, PMF.pure_bind]
  have htake : ((List.range reqs.length).map fun idx => (ans.getD idx []).take (k + 2)) = ans := by
    apply List.ext_getElem (by simp [ans, oracleReplies]; rfl)
    intro i hi hia
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hia, Option.getD_some]
    dsimp only [ans, oracleReplies]
    erw [List.getElem_map]
    cases (CCR.codec k).decodeQuery ((), reqs[i]'(by simpa [ans, oracleReplies] using hia)) <;>
      simp
  rw [htake]
  exact congrArg (fun V => ProbComp.eval ((B k).guess state (some V))) (redView_eq hash hx O coins)

end Run

/-! ### The exact equality -/

section Exact

variable (hash : List Bool → List Bool → List Bool)

private theorem slotTweak_injective (k : ℕ) (f : ValidCircuit) (hk : 8 * f.1.q ≤ 2 ^ k) :
    Function.Injective (slotTweak (toCircuit f).topology (freeCircuit f) k) := by
  rintro ⟨⟨⟨g, hg⟩, r⟩, s⟩ ⟨⟨⟨g', hg'⟩, r'⟩, s'⟩ h
  have hinj := @PointPermute.slotTweak_injective k f hk ⟨⟨g, r⟩, s⟩ ⟨⟨g', r'⟩, s'⟩ h
  obtain rfl : g = g' := congrArg (·.1.1) hinj
  cases hinj
  rfl

/-- **The real view is the typed real view.** For a query `(f, x)` with `x` of `f.n` bits, the
real view at parameter `k` is the words of the typed view, on `x`, of the typed garbling of
`toCircuit f`. -/
private theorem eval_prvView (k : ℕ) (query : Query ValidCircuit)
    (hx : query.input.length = query.fn.1.n) :
    ProbComp.eval ((scheme hash).prvView k query) =
      (ProbComp.eval (FreeXOR.garble (toCircuit query.fn) fullInterpretation
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k))).map
        fun G => viewWord k _ (freeCircuit query.fn)
          (G.view (BitString.ofList query.fn.1.n query.input)) := by
  have hcoins : (scheme hash).coins k query.fn =
      (k + 1) + (query.fn.1.n + query.fn.1.q) * (k + 2) := rfl
  have hfun : (fun a : Scheme.Garbled =>
      (⟨a.fn, (scheme hash).encode a.encInfo query.input, a.decInfo⟩ : PrvView)) ∘
        (scheme hash).gb k query.fn =
      (fun p : BitString (k + 1) × (Wire query.fn.1.n (toCircuit query.fn).size →
          BitString (k + 1) × Bool) =>
        viewWord k _ (freeCircuit query.fn) ((garbleWith (toCircuit query.fn)
          fullInterpretation (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k) p.1
          p.2).view (BitString.ofList query.fn.1.n query.input))) ∘
        (fun coins => (HalfGates.offsetKey k coins,
          (baseLabels k coins : Wire query.fn.1.n (toCircuit query.fn).size → _))) := by
    funext coins
    simp only [Function.comp_apply]
    rw [gb_eq_encodeGarbled]
    simp only [viewWord, encodeGarbled, Garbled.view, PrvView.mk.injEq, true_and, and_true]
    exact PointPermute.projectiveEncode_labelBits (n := query.fn.1.n) _ hx
  simp only [Scheme.prvView, garble, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    Scheme.eval_garble, ProbComp.eval_uniform, hcoins, PMF.map_comp]
  have hunif : (BitString.uniformList ((k + 1) + (query.fn.1.n + query.fn.1.q) *
      (k + 2))).map (fun coins => (HalfGates.offsetKey k coins,
        (baseLabels k coins : Wire query.fn.1.n (toCircuit query.fn).size → _))) =
      PMF.uniformOfFintype (BitString (k + 1) ×
        (Wire query.fn.1.n (toCircuit query.fn).size → BitString (k + 1) × Bool)) := by
    rw [BitString.uniformList_add, PMF.map_bind]
    calc _ = (BitString.uniformList (k + 1)).bind fun front =>
          ((BitString.uniformList ((query.fn.1.n + query.fn.1.q) * (k + 2))).map
            (fun back => (simBaseLabels k back :
              Wire query.fn.1.n (toCircuit query.fn).size → _))).map
              fun B => (BitString.ofList (k + 1) front, B) := by
          refine Probability.PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
          have hlen := BitString.length_of_mem_support_uniformList hfront
          rw [PMF.map_comp, PMF.map_comp]
          congr 1
          funext back
          refine Prod.ext (BitString.ofList_append_of_le hlen.ge _) (funext fun w => ?_)
          simp [baseLabels, simBaseLabels, baseWord, PointPermute.simLabel, BitString.listRow,
            List.drop_left' hlen]
      _ = _ := by
          rw [uniformList_map_simBaseLabels, ← Cslib.Probability.PMF.uniformOfFintype_prod,
            ← BitString.uniformList_ofList, PMF.bind_map]
          rfl
  rw [hfun, ← PMF.map_comp, hunif, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

private theorem eval_prvSimExperiment_true {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k : ℕ) (S : PrvSimulator XorTopology)
    (hq : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → 8 * query.fn.1.q ≤ 2 ^ k) :
    ProbComp.eval (prvSimExperiment (scheme hash) phiXor k S (B k) true) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n ∧ 8 * query.fn.1.q ≤ 2 ^ k then
          FreeXOR.realGame (toCircuit query.fn) fullInterpretation
            (fun key t => CCR.atLevel hash k (key, false) t)
            (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
            (BitString.ofList query.fn.1.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [FreeXOR.realGame, ProbComp.eval_bind]
  exact eval_prvSimExperiment_eq_bind (scheme hash) phiXor k S (B k) true
    (fun q => 8 * q.fn.1.q ≤ 2 ^ k) hq
    (fun query (G : FreeXOR.Garbled (toCircuit query.fn).topology (freeCircuit query.fn)
        (BitString (k + 1))) =>
      viewWord k _ (freeCircuit query.fn) (G.view (BitString.ofList query.fn.1.n query.input)))
    (fun query => ProbComp.eval (FreeXOR.garble (toCircuit query.fn) fullInterpretation
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)))
    (fun query _ _ hx => by
      change query.input.length = query.fn.1.n at hx
      simp only [ite_true]
      exact eval_prvView hash k query hx)

private theorem eval_prvSimExperiment_false {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k : ℕ)
    (hq : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → 8 * query.fn.1.q ≤ 2 ^ k) :
    ProbComp.eval (prvSimExperiment (scheme hash) phiXor k (simWord hash k) (B k) false) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n ∧ 8 * query.fn.1.q ≤ 2 ^ k then
          FreeXOR.simGame (toCircuit query.fn) fullInterpretation
            (fun key t => CCR.atLevel hash k (key, false) t)
            (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
            (BitString.ofList query.fn.1.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [FreeXOR.simGame, ProbComp.eval_bind]
  exact eval_prvSimExperiment_eq_bind (scheme hash) phiXor k (simWord hash k) (B k) false
    (fun q => 8 * q.fn.1.q ≤ 2 ^ k) hq
    (fun query (V : FreeXOR.View (toCircuit query.fn).topology (freeCircuit query.fn)
        (BitString (k + 1))) =>
      viewWord k _ (freeCircuit query.fn) V)
    (fun query => ProbComp.eval (FreeXOR.simulate (toCircuit query.fn).topology
      (freeCircuit query.fn) (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
      ((toCircuit query.fn).eval fullInterpretation (BitString.ofList query.fn.1.n query.input))))
    (fun query _ _ hx => by
      change query.input.length = query.fn.1.n at hx
      have hy : BitString.ofList query.fn.1.m (query.fn.1.evalCirc query.input) =
          (toCircuit query.fn).eval fullInterpretation
            (BitString.ofList query.fn.1.n query.input) := by
        have h := eval_toCircuit query.fn (BitString.ofList query.fn.1.n query.input)
        rw [BitString.ofFn_ofList hx] at h
        rw [← h, BitString.ofList_ofFn]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (scheme hash).ev query.fn query.input = query.fn.1.evalCirc query.input from rfl,
        eval_simWord, hy])

private theorem eval_realExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (k : ℕ) :
    ProbComp.eval (PRF.realExperiment (CCR.keyed (CCR.atLevel hash k) CCR.offset CCR.offset)
        ((CCR.codec k).adapt (prvSimReduction hash B k []))) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n ∧ 8 * query.fn.1.q ≤ 2 ^ k then
          FreeXOR.realGame (toCircuit query.fn) fullInterpretation
            (fun key t => CCR.atLevel hash k (key, false) t)
            (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
            (BitString.ofList query.fn.1.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs
  · have h := FreeXOR.realGame_reduction (toCircuit query.fn) fullInterpretation
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
      (BitString.ofList query.fn.1.n query.input)
      (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))
      (hfree_toCircuit query.fn) BitString.add_self
    rw [← h]
    simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine congrArg _ (funext fun R => congrArg ProbComp.eval (congrArg _ (funext fun q => ?_)))
    change pure (CCR.atLevel hash k (q.label + R, true + true) q.tweak +
        bitOffset (R, true) q.bit) =
      pure (CCR.atLevel hash k (q.label + R, false) q.tweak + bitOffset (R, true) q.bit)
    rw [show (true + true : Bool) = false by decide]
  · rw [PMF.bind_const]

private theorem eval_idealExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (k : ℕ) :
    ProbComp.eval (PRF.idealExperiment ((CCR.codec k).adapt (prvSimReduction hash B k []))) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n ∧ 8 * query.fn.1.q ≤ 2 ^ k then
          FreeXOR.simGame (toCircuit query.fn) fullInterpretation
            (fun key t => CCR.atLevel hash k (key, false) t)
            (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
            (BitString.ofList query.fn.1.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hguard
  · rw [← FreeXOR.idealGame_reduction (toCircuit query.fn) fullInterpretation
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
        (BitString.ofList query.fn.1.n query.input)
        (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))
        (slotTweak_injective k query.fn hguard.2)]
    simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
    have hcomp : (fun f : CCR.Query (BitString (k + 1) × Bool) (BitString k) →
          BitString (k + 1) × Bool =>
        ProbComp.eval ((FreeXOR.reduction (toCircuit query.fn) fullInterpretation
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
          (BitString.ofList query.fn.1.n query.input)
          (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))).run
            fun q => pure (f (CCR.keyOnlyEmbed _ _ q)))) =
        (fun g : CCR.Query (BitString (k + 1)) (BitString k) → BitString (k + 1) × Bool =>
          ProbComp.eval ((FreeXOR.reduction (toCircuit query.fn) fullInterpretation
            (fun key t => CCR.atLevel hash k (key, false) t)
            (slotTweak (toCircuit query.fn).topology (freeCircuit query.fn) k)
            (BitString.ofList query.fn.1.n query.input)
            (fun V => (B k).guess state (some (viewWord k _ (freeCircuit query.fn) V)))).run
              fun q => pure (g q))) ∘
          (fun f q => f (CCR.keyOnlyEmbed _ _ q)) := by
      funext f
      rfl
    rw [hcomp, ← PMF.bind_map, Probability.PMF.uniformOfFintype_pi_map_comp_embedding]
  · rw [PMF.bind_const]

/-- Library infrastructure (no cited result): **The `prv.sim` advantage against the simulator
is the reduction's CCR advantage.** At
parameter `k`, if every valid query that `B k` can choose has `8 q ≤ 2 ^ k`, the `prv.sim`
advantage of `B k` against `simWord hash k`, with side information `phiXor`, equals the finite CCR
advantage `CCR.advantage (CCR.atLevel hash k) CCR.offset CCR.offset` of `prvSimReduction hash B`
at level `k`, read through `CCR.codec k`. -/
theorem prvSimAdvantage_simWord_eq {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ) (k : ℕ)
    (hq : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → 8 * query.fn.1.q ≤ 2 ^ k) :
    prvSimAdvantage (scheme hash) phiXor k (simWord hash k) (B k) =
      CCR.advantage (CCR.atLevel hash k) CCR.offset CCR.offset
        ((CCR.codec k).adapt (prvSimReduction hash B k [])) := by
  rw [prvSimAdvantage, Experiment.advantage, eval_prvSimExperiment_false hash B k hq,
    eval_prvSimExperiment_true hash B k _ hq, Game.advantage_comm, CCR.advantage, PRF.advantage,
    eval_realExperiment_prvSimReduction, eval_idealExperiment_prvSimReduction]

end Exact

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

private theorem slotReq_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k n g a b i s : γ → ℕ} {labels : γ → List (List Bool)} {ws tt : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hws : ComputableInPolyTime ws encIn encBits)
    (hg : ComputableInPolyTime g encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) (htt : ComputableInPolyTime tt encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary) (hs : ComputableInPolyTime s encIn encUnary) :
    ComputableInPolyTime (fun x => slotReq (k x) (n x) (labels x) (ws x) (g x) (a x) (b x)
      (tt x) (i x) (s x)) encIn encBits := by
  have htw := PointPermute.tweak_polyTime hk hg hi hs
  unfold slotReq
  polytime [HalfGates.colourWord]

private theorem gateReqs_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k n g : γ → ℕ} {labels : γ → List (List Bool)} {ws : γ → List Bool}
    {gate : γ → ℕ × ℕ × List Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hws : ComputableInPolyTime ws encIn encBits)
    (hgate : ComputableInPolyTime gate encIn (encPair encNat (encPair encNat encBits))) :
    ComputableInPolyTime (fun x => gateReqs (k x) (n x) (g x) (labels x) (ws x) (gate x))
      encIn (encList encBits) := by
  have hcap : ComputableInPolyTime (fun x => (labels x).length + (ws x).length + 1) encIn
      encUnary := by polytime
  have ha := ComputableInPolyTime.unary_sub'
    (ComputableInPolyTime.binary_min_unary' hcap hgate.fst') (ComputableInPolyTime.const 1)
  have hb := ComputableInPolyTime.unary_sub'
    (ComputableInPolyTime.binary_min_unary' hcap hgate.snd'.fst') (ComputableInPolyTime.const 1)
  have htt := hgate.snd'.snd'
  let sr (i s : ℕ) := slotReq_polyTime hk hn hlabels hws hg ha hb htt
    (ComputableInPolyTime.const i) (ComputableInPolyTime.const s)
  have hnil : ComputableInPolyTime (fun _ : γ => ([] : List (List Bool))) encIn
      (encList encBits) := ComputableInPolyTime.const _
  exact ComputableInPolyTime.ite' (isXorTable_polyTime.comp htt) hnil
    (.cons' (sr 0 0) (.cons' (sr 0 1) (.cons' (sr 1 0) (.cons' (sr 1 1)
      (.cons' (sr 2 0) (.cons' (sr 2 1) (.cons' (sr 3 0) (.cons' (sr 3 1) hnil))))))))

private theorem allReqs_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k n : γ → ℕ} {gates : γ → List (ℕ × ℕ × List Bool)}
    {labels : γ → List (List Bool)} {ws : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn (encList (encPair encNat (encPair encNat encBits))))
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hws : ComputableInPolyTime ws encIn encBits) :
    ComputableInPolyTime (fun x => allReqs (k x) (n x) (gates x) (labels x) (ws x))
      encIn (encList encBits) := by
  have hfst := ComputableInPolyTime.fst encIn encUnary
  have hg := ComputableInPolyTime.snd encIn encUnary
  have hgate := ComputableInPolyTime.listGetDWithInput (hgates.comp hfst) hg (0, 0, [])
  have hstep := gateReqs_polyTime (hk.comp hfst) (hn.comp hfst) hg (hlabels.comp hfst)
    (hws.comp hfst) hgate
  have hq : ComputableInPolyTime (fun x => (gates x).length) encIn encUnary :=
    (ComputableInPolyTime.length_list _).comp hgates
  have heq : (fun x => allReqs (k x) (n x) (gates x) (labels x) (ws x)) = fun x =>
      (List.range (gates x).length).flatMap fun g =>
        gateReqs (k x) (n x) g (labels x) (ws x) ((gates x).getD g (0, 0, [])) := by
    funext x; exact List.flatMap_def.symm
  rw [heq]
  exact ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hq) hstep

variable {hash : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => hash p.1 p.2)
    (encPair encBits encBits) encBits)

include hf in
private theorem redRow_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k n g a b i : γ → ℕ} {free : γ → List Bool} {labels rs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hfree : ComputableInPolyTime free encIn encBits)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hrs : ComputableInPolyTime rs encIn (encList encBits))
    (hg : ComputableInPolyTime g encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => redRow hash (k x) (n x) (free x) (labels x) (rs x)
      (g x) (a x) (b x) (i x)) encIn encBits := by
  have hrank := nonXorCount_polyTime hfree hg
  have htw₀ := PointPermute.tweak_polyTime hk hg hi (ComputableInPolyTime.const 0)
  have htw₁ := PointPermute.tweak_polyTime hk hg hi (ComputableInPolyTime.const 1)
  have hla := ComputableInPolyTime.listGetDWithInput hlabels ha []
  have hlb := ComputableInPolyTime.listGetDWithInput hlabels hb []
  have hhash₀ := keyHashWord_polyTime hf hk hla htw₀
  have hhash₁ := keyHashWord_polyTime hf hk hlb htw₁
  unfold redRow
  polytime [HalfGates.colourWord]

include hf in
private theorem redRowData_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k n g a b i : γ → ℕ} {free : γ → List Bool} {labels rs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hfree : ComputableInPolyTime free encIn encBits)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hrs : ComputableInPolyTime rs encIn (encList encBits))
    (hg : ComputableInPolyTime g encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => redRowData hash (k x) (n x) (free x) (labels x) (rs x)
      (g x) (a x) (b x) (i x)) encIn encBits :=
  rowData_polyTime hfree hg hi (redRow_polyTime hf hk hn hfree hlabels hrs hg ha hb hi)

private theorem validSimPropWords_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {f : γ → ValidCircuit} {coins : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hfv : ComputableInPolyTime f encIn encValidCircuit)
    (hcoins : ComputableInPolyTime coins encIn encBits) :
    ComputableInPolyTime (fun x => simPropWords (k x) (f x).1.topo (xorFlags (f x).1.gateList)
      (coins x) (f x).1.q) encIn (encList encBits) := by
  have hfree := xorFlags_polyTime.comp (circuitData_polyTime.snd'.snd'.comp hfv)
  have htopo : ComputableInPolyTime (fun x => ((f x).1.topo.n, (f x).1.topo.m,
      (f x).1.topo.gateList)) encIn encTopoData :=
    topoData_polyTime.comp (phiTopo_polyTime.comp hfv)
  exact simPropWords_polyTime_of hk htopo hfree hcoins
    (fun x g => (f x).2.one_le_A g) (fun x g => (f x).2.A_lt_B g)
    (fun x g => (f x).2.B_lt_gate g)

include hf in
private theorem redView_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {f : γ → ValidCircuit} {ws coins : γ → List Bool} {rs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hfv : ComputableInPolyTime f encIn encValidCircuit)
    (hws : ComputableInPolyTime ws encIn encBits)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (hrs : ComputableInPolyTime rs encIn (encList encBits)) :
    ComputableInPolyTime (fun x => redView hash (k x) (f x).1 (ws x) (coins x) (rs x))
      encIn encPrvView := by
  have hd := circuitData_polyTime.comp hfv
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hgates := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hgates
  have hfree := xorFlags_polyTime.comp hgates
  have hlabels := validSimPropWords_polyTime hk hfv hcoins
  have hcap : ComputableInPolyTime (fun x =>
      (simPropWords (k x) (f x).1.topo (xorFlags (f x).1.gateList) (coins x)
        (f x).1.q).length + 1) encIn encUnary :=
    ComputableInPolyTime.unary_add' ((ComputableInPolyTime.length_list _).comp hlabels)
      (ComputableInPolyTime.const 1)
  have hp := ComputableInPolyTime.fst encIn (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have hr := ComputableInPolyTime.snd encIn (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have hrow := redRowData_polyTime hf (hk.comp hp) (hn.comp hp) (hfree.comp hp)
    (hlabels.comp hp) (hrs.comp hp) hr.fst' hr.snd'.fst' hr.snd'.snd'.fst' hr.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hgates.comp (ComputableInPolyTime.fst encIn encUnary)) (ComputableInPolyTime.snd _ _)
    (0, 0, [])
  have hbody := PointPermute.bodyWith_polyTime
    (n := fun x => (f x).1.n) (q := fun x => (f x).1.gateList.length)
    (cap := fun x =>
      (simPropWords (k x) (f x).1.topo (xorFlags (f x).1.gateList) (coins x)
        (f x).1.q).length + 1)
    (A := fun x g => ((f x).1.gateList.getD g (0, 0, [])).1)
    (B := fun x g => ((f x).1.gateList.getD g (0, 0, [])).2.1)
    (row := fun x g a b i => redRowData hash (k x) (f x).1.n (xorFlags (f x).1.gateList)
      (simPropWords (k x) (f x).1.topo (xorFlags (f x).1.gateList) (coins x) (f x).1.q)
      (rs x) g a b i)
    hn hq hcap hgate.fst' hgate.snd'.fst'
    (by convert hrow using 2; rcases ‹_› with ⟨_, _, _, _, _⟩; rfl)
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn z)
      PointPermute.encFn encBits := .of_eq fun _ => rfl
  have hF := henc.comp ((hk.prod (hn.prod (hm.prod hq))).prod hbody)
  have hX : ComputableInPolyTime (fun x =>
      ((List.range (f x).1.n).map fun i => PointPermute.simLabel (k x) (coins x) i).flatten)
      encIn encBits := by
    polytime [PointPermute.simLabel, BitString.listRow]
  have hdecRange : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × ℕ × List (List Bool) =>
      (List.range p.2.2.1).map fun o => HalfGates.colourWord p.1
        (p.2.2.2.2.getD (p.2.2.2.1 + o) []) ^^ p.2.1.getD (p.2.2.2.1 + o) false)
      (encPair encUnary (encPair encBits (encPair encUnary (encPair encUnary (encList encBits)))))
      encBits := by
    polytime [HalfGates.colourWord]
  have hdecOff : ComputableInPolyTime (fun x =>
      (f x).1.n + (f x).1.gateList.length - (f x).1.m) encIn encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' hn hq) hm
  have hdec : ComputableInPolyTime (fun x => (List.range (f x).1.m).map fun o =>
      HalfGates.colourWord (k x) ((simPropWords (k x) (f x).1.topo (xorFlags (f x).1.gateList)
        (coins x) (f x).1.q).getD ((f x).1.n + (f x).1.gateList.length - (f x).1.m + o) []) ^^
        (ws x).getD ((f x).1.n + (f x).1.gateList.length - (f x).1.m + o) false) encIn encBits := by
    simpa only [Function.comp_def, ConventionalCircuit.topo] using
      hdecRange.comp (hk.prod (hws.prod (hm.prod (hdecOff.prod hlabels))))
  exact encPrvView_mk_polyTime hF hX hdec

variable {σ : Type} {encσ : σ ↪ List Bool} {B : ℕ → PrvSimAdversary ValidCircuit σ}
  (hB : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit) (encOption encPrvView)
    encBool encσ B)

private theorem prvSimReqs_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {f : γ → ValidCircuit} {ws coins : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hfv : ComputableInPolyTime f encIn encValidCircuit)
    (hws : ComputableInPolyTime ws encIn encBits)
    (hcoins : ComputableInPolyTime coins encIn encBits) :
    ComputableInPolyTime (fun p => prvSimReqs (k p) (f p).1 (ws p) (coins p))
      encIn (encList encBits) := by
  have hd := circuitData_polyTime.comp hfv
  exact allReqs_polyTime hk hd.fst' hd.snd'.snd' (validSimPropWords_polyTime hk hfv hcoins) hws

include hf hB in
private theorem isOraclePPTOn_prvSimGuess :
    IsOraclePPTOn (encPair (encPrvChosen encValidCircuit encσ) encBits) encBool
      (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) × List Bool => do
        let ws := p.1.2.1.fn.1.wires p.1.2.1.input p.1.2.1.fn.1.q
        let reqs := prvSimReqs p.1.1.1 p.1.2.1.fn.1 ws p.2
        let rs ← OracleComp.iterate reqs.length (replyStep p.1.1.1 reqs) []
        ProbOracleComp.sample ((B p.1.1.1).guess p.1.2.2
          (some (redView hash p.1.1.1 p.1.2.1.fn.1 ws p.2 rs)))) := by
  let E := encPair (encPrvChosen encValidCircuit encσ) encBits
  have hchosen := ComputableInPolyTime.fst (encPrvChosen encValidCircuit encσ) encBits
  have hcoins := ComputableInPolyTime.snd (encPrvChosen encValidCircuit encσ) encBits
  have hk := (ComputableInPolyTime.fst _ _).fst'.comp hchosen
  have hquery := (ComputableInPolyTime.snd _ _).fst'.comp hchosen
  have hstate := (ComputableInPolyTime.snd _ _).snd'.comp hchosen
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hws := wires_polyTime.comp (hfn.prod hx)
  have hreqs := prvSimReqs_polyTime hk hfn hws hcoins
  have hfst := ComputableInPolyTime.fst E (encList encBits)
  have hrs := ComputableInPolyTime.snd E (encList encBits)
  have hloop := isOraclePPTOn_iterate_replyStepWord
    ((ComputableInPolyTime.length_list _).comp hreqs)
    (ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2))
    (ComputableInPolyTime.listGetDWithInput (hreqs.comp hfst)
      ((ComputableInPolyTime.length_list _).comp hrs) [])
  have hview := redView_polyTime hf (hk.comp hfst) (hfn.comp hfst) (hws.comp hfst)
    (hcoins.comp hfst) hrs
  have hprep := (hk.comp hfst).prod ((hstate.comp hfst).prod
    ((ComputableInPolyTime.optionSome encPrvView).comp hview))
  unfold replyStep
  exact hloop.bind_with ((hB.guess.preprocess hprep).isOraclePPTOn (Operation := Unit))

include hf hB in
/-- Library infrastructure (no cited result): **Efficiency of the reduction.** For every hash
family computed in polynomial time and every uniform strict PPT `prv.sim` adversary `B`,
`prvSimReduction hash B` is uniform strict oracle PPT. -/
theorem isOraclePPT_prvSimReduction : IsOraclePPT encBool (prvSimReduction hash B) := by
  have hd := circuitData_polyTime
  have hn : ComputableInPolyTime (fun f : ValidCircuit => f.1.n) encValidCircuit encUnary :=
    hd.fst'
  have hq : ComputableInPolyTime (fun f : ValidCircuit => f.1.q) encValidCircuit encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have hlen : ComputableInPolyTime (fun p : ℕ × ValidCircuit => (p.2.1.n + p.2.1.q) * (p.1 + 2))
      (encPair encUnary encValidCircuit) encUnary :=
    ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.unary_add.comp
      ((hn.comp (ComputableInPolyTime.snd _ _)).prod
        (hq.comp (ComputableInPolyTime.snd _ _)))).prod
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst _ _)
        (ComputableInPolyTime.const 2)))
  exact isOraclePPT_prvSimReduction_of_bounded hB 8 hn hq hlen
    (fun k query state coins => do
      let ws := query.fn.1.wires query.input query.fn.1.q
      let reqs := prvSimReqs k query.fn.1 ws coins
      let rs ← OracleComp.iterate reqs.length (replyStep k reqs) []
      ProbOracleComp.sample ((B k).guess state (some (redView hash k query.fn.1 ws coins rs))))
    (isOraclePPTOn_prvSimGuess hf hB)

end Efficiency

end FreeXOR

end Cslib.Crypto.Garbling
