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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime

/-!
# The CCR reduction program for Free-XOR garbling

Library infrastructure (no cited result): the Free-XOR `prv.sim` reduction as a certified,
tweak-unique strict oracle-PPT CCR adversary; its run equality, advantage equality, and simulation
privacy theorem follow in the next PR.

The reduction `prvSimReduction hash B` runs `B`'s choice of a query `(f, x)`. When `x` has `f.n`
bits and `8 q ≤ 2 ^ k`, it samples `(n + q)` active `(k + 2)`-bit labels, propagates active
labels across XOR gates, evaluates the circuit on `x` to obtain all plaintext wire bits, and issues
the 8 oracle queries of every non-XOR gate (`allReqs`) non-adaptively at level `k`
(`(key, true), tweak, bit`), whose requests all carry distinct `k`-bit tweaks while `8 q ≤ 2 ^ k`.
It then builds the garbled view `(F, X, d)` from the oracle replies and hands it to `B`'s guess.
Otherwise (on an invalid input length or when `8 q > 2 ^ k`), it makes no oracle queries and runs
`B`'s guess on `⊥`.

Key-only queries `H'(x, t) = CCR.atLevel hash k (x, false) t` transfer to full-label queries via
`CCR.advantage_keyOnly` in `CslibFrontier.Crypto.Primitives.Garbling.CircularCorrelationRobust`,
since `(x, true) + (R, true) = (x + R, false)`. The reduction asks every tweak at most once on
every execution path (`isTweakUnique_prvSimReduction`), issues `8` requests per non-XOR gate on
valid bounded inputs (`exists_of_mem_support_runWith_prvSimReduction`), and is uniform strict
oracle PPT (`isOraclePPT_prvSimReduction`).

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.prvSimReduction`: the non-adaptive CCR reduction.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.isTweakUnique_prvSimReduction`: the reduction is tweak-unique.
* `Cslib.Crypto.Garbling.FreeXOR.exists_of_mem_support_runWith_prvSimReduction`: logged execution
  request count.
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
      rw [List.getElem_append_left hlt]
      exact hval
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
      have hsub : p - ((List.range m).map step).flatten.length = p - 8 * nonXorRank free m := by
        rw [hpre]
      rw [List.getElem_append_right hge]
      simp only [hsub, hstep_eq]
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
        have hm_ne : ¬ (reqs[m].drop (k + 2)).take k = List.ofFn t := by
          intro htm
          exact (htw i hi_len m hmlt).2 (by omega) (hti.trans htm.symm)
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
  obtain ⟨⟨⟨q, st⟩, s₁, tr₁⟩, h₁, h₂⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmem
  rw [ProbOracleComp.runWith_sample] at h₁
  obtain ⟨⟨q', st'⟩, hq', hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp h₁
  simp only [Prod.mk.injEq] at hpair
  rcases hpair with ⟨⟨hq_eq, hst_eq⟩, hs₁, htr₁⟩
  subst hq_eq hst_eq hs₁ htr₁
  refine ⟨q', st', hq', ?_⟩
  dsimp only at h₂
  by_cases hguard : q'.input.length = q'.fn.1.n ∧ 8 * q'.fn.1.q ≤ 2 ^ k
  · simp only [hguard, and_self, ↓reduceIte] at h₂ ⊢
    rw [ProbOracleComp.runWith_bind] at h₂
    obtain ⟨⟨coins, s₂, tr₂⟩, hc, h₃⟩ := (PMF.mem_support_bind_iff _ _ _).mp h₂
    rw [ProbOracleComp.runWith_sample] at hc
    obtain ⟨coins', -, hc_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
    simp only [Prod.mk.injEq] at hc_eq
    rcases hc_eq with ⟨-, rfl, rfl⟩
    rw [ProbOracleComp.runWith_bind] at h₃
    obtain ⟨⟨rs, s₃, tr₃⟩, hrs, h₄⟩ := (PMF.mem_support_bind_iff _ _ _).mp h₃
    rw [ProbOracleComp.runWith_sample] at h₄
    obtain ⟨b, -, hb_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp h₄
    simp only [Prod.mk.injEq] at hb_eq
    rcases hb_eq with ⟨-, -, rfl⟩
    have htr := length_transcript_iterate_replyStep oracle k _ _ [] s [] hrs
    have hlen : (prvSimReqs k q'.fn.1 (q'.fn.1.wires q'.input q'.fn.1.q) coins).length =
        8 * (phiXor.phi q'.fn).free.count false := by
      simp only [prvSimReqs, allReqs]
      rw [allReqs_prefix_length _ _ _ _ _ le_rfl, xorFlags_gateList, nonXorRank,
        List.take_of_length_le]
      simp [phiXor]
    simpa [hlen] using htr
  · simp only [hguard, ↓reduceIte] at h₂ ⊢
    rw [ProbOracleComp.runWith_sample] at h₂
    obtain ⟨b, -, hb_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp h₂
    simp only [Prod.mk.injEq] at hb_eq
    rcases hb_eq with ⟨-, -, rfl⟩
    rfl

end Legality

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
  have ha : ComputableInPolyTime
      (fun x => min ((labels x).length + (ws x).length + 1) (gate x).1 - 1) encIn encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.binary_min_unary' hcap hgate.fst')
      (ComputableInPolyTime.const 1)
  have hb : ComputableInPolyTime
      (fun x => min ((labels x).length + (ws x).length + 1) (gate x).2.1 - 1) encIn encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.binary_min_unary' hcap hgate.snd'.fst')
      (ComputableInPolyTime.const 1)
  have htt := hgate.snd'.snd'
  have hcond : ComputableInPolyTime (fun x => isXorTable (gate x).2.2) encIn encBool :=
    isXorTable_polyTime.comp htt
  have hr00 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.const 0)
  have hr01 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.const 1)
  have hr10 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.const 0)
  have hr11 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.const 1)
  have hr20 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.const 0)
  have hr21 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.const 1)
  have hr30 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 3)
    (ComputableInPolyTime.const 0)
  have hr31 := slotReq_polyTime hk hn hlabels hws hg ha hb htt (ComputableInPolyTime.const 3)
    (ComputableInPolyTime.const 1)
  have hnil : ComputableInPolyTime (fun _ : γ => ([] : List (List Bool))) encIn
      (encList encBits) := ComputableInPolyTime.const _
  have hlist := ComputableInPolyTime.cons' hr00 (ComputableInPolyTime.cons' hr01
    (ComputableInPolyTime.cons' hr10 (ComputableInPolyTime.cons' hr11
      (ComputableInPolyTime.cons' hr20 (ComputableInPolyTime.cons' hr21
        (ComputableInPolyTime.cons' hr30 (ComputableInPolyTime.cons' hr31 hnil)))))))
  exact ComputableInPolyTime.ite' hcond hnil hlist

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
  have hfm : ∀ (l : List ℕ) (f : ℕ → List (List Bool)), (l.map f).flatten = l.flatMap f :=
    fun l f => by induction l <;> simp [*]
  have heq : (fun x => allReqs (k x) (n x) (gates x) (labels x) (ws x)) = fun x =>
      (List.range (gates x).length).flatMap fun g =>
        gateReqs (k x) (n x) g (labels x) (ws x) ((gates x).getD g (0, 0, [])) := by
    funext x
    exact hfm _ _
  rw [heq]
  exact ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hq) hstep

private theorem isOraclePPTOn_replyStep {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {reqs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hreqs : ComputableInPolyTime reqs encIn (encList encBits)) :
    IsOraclePPTOn (encPair encIn (encList encBits)) (encList encBits)
      (fun p : γ × List (List Bool) => replyStep (k p.1) (reqs p.1) p.2) := by
  let E := encPair encIn (encList encBits)
  have hfst := ComputableInPolyTime.fst encIn (encList encBits)
  have hrs := ComputableInPolyTime.snd encIn (encList encBits)
  have hidx := (ComputableInPolyTime.length_list _).comp hrs
  have hreq : ComputableInPolyTime (fun p : γ × List (List Bool) =>
      (reqs p.1).getD p.2.length []) E encBits :=
    ComputableInPolyTime.listGetDWithInput (hreqs.comp hfst) hidx []
  have hlim : ComputableInPolyTime (fun p : γ => k p + 2) encIn encUnary :=
    ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2)
  exact isOraclePPTOn_replyStepWord hlim hreq

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

private theorem isOraclePPTOn_prvSimLoop_aux {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {reqs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hreqs : ComputableInPolyTime reqs encIn (encList encBits)) :
    IsOraclePPTOn encIn (encList encBits)
      (fun p : γ => OracleComp.iterate (reqs p).length (replyStep (k p) (reqs p)) []) := by
  have hcount : ComputableInPolyTime (fun p => (reqs p).length) encIn encUnary :=
    (ComputableInPolyTime.length_list _).comp hreqs
  have hgrowth : ComputableInPolyTime (fun p => 2 * (k p + 2) + 2) encIn encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod
        (ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2))))
      (ComputableInPolyTime.const 2)
  exact IsOraclePPTOn.iterateWith_of_bounded_growth (Operation := Unit)
    (input := encIn) (stateEncoding := encList encBits) (initial := fun _ => [])
    (count := fun p => (reqs p).length) (step := fun p => replyStep (k p) (reqs p))
    hcount (ComputableInPolyTime.const (encIn := encIn) []) (isOraclePPTOn_replyStep hk hreqs)
    (growth := fun p => 2 * (k p + 2) + 2)
    (hgrowth.polyBounded_length.mono fun p => by
      simp only [encUnary_apply, List.length_replicate, le_refl])
    (fun _ _ _ hnext => length_le_of_mem_support_replyStepWord hnext)

private theorem isOraclePPTOn_prvSimLoop :
    IsOraclePPTOn (encPair (encPrvChosen encValidCircuit encσ) encBits) (encList encBits)
      (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) × List Bool =>
        let ws := p.1.2.1.fn.1.wires p.1.2.1.input p.1.2.1.fn.1.q
        let reqs := prvSimReqs p.1.1.1 p.1.2.1.fn.1 ws p.2
        OracleComp.iterate reqs.length (replyStep p.1.1.1 reqs) []) := by
  dsimp only
  have hchosen := ComputableInPolyTime.fst (encPrvChosen encValidCircuit encσ) encBits
  have hcoins := ComputableInPolyTime.snd (encPrvChosen encValidCircuit encσ) encBits
  have hk : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      List Bool => p.1.1.1) (encPair (encPrvChosen encValidCircuit encσ) encBits) encUnary :=
    (ComputableInPolyTime.fst _ _).fst'.comp hchosen
  have hquery : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      List Bool => p.1.2.1) (encPair (encPrvChosen encValidCircuit encσ) encBits)
      (encQuery ValidCircuit encValidCircuit) :=
    (ComputableInPolyTime.snd _ _).fst'.comp hchosen
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hws := wires_polyTime.comp (hfn.prod hx)
  have hreqs := prvSimReqs_polyTime hk hfn hws hcoins
  exact isOraclePPTOn_prvSimLoop_aux hk hreqs

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
  have hk : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      List Bool => p.1.1.1) E encUnary := (ComputableInPolyTime.fst _ _).fst'.comp hchosen
  have hquery : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      List Bool => p.1.2.1) E (encQuery ValidCircuit encValidCircuit) :=
    (ComputableInPolyTime.snd _ _).fst'.comp hchosen
  have hstate : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) ×
      List Bool => p.1.2.2) E encσ := (ComputableInPolyTime.snd _ _).snd'.comp hchosen
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hws := wires_polyTime.comp (hfn.prod hx)
  have hfst := ComputableInPolyTime.fst E (encList encBits)
  have hview := redView_polyTime hf (hk.comp hfst) (hfn.comp hfst) (hws.comp hfst)
    (hcoins.comp hfst) (ComputableInPolyTime.snd E (encList encBits))
  have hprep := (hk.comp hfst).prod ((hstate.comp hfst).prod
    ((ComputableInPolyTime.optionSome encPrvView).comp hview))
  have hstep_guess := (hB.guess.preprocess hprep).isOraclePPTOn (Operation := Unit)
  exact (isOraclePPTOn_prvSimLoop (encσ := encσ)).bind_with hstep_guess

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
