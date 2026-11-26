/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.CircuitInverters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Crypto.Primitives.Garbling.Games
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Foundations.Data.List.GetD

/-!
# Efficient garbling schemes

The algorithms of a garbling scheme in the sense of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012] are meant to be efficient. `Scheme.IsEfficient G encFn` states this for
a scheme `G` whose function descriptions are encoded by `encFn`: the length readers `f.n` and
`f.m`, the number of coins, the deterministic core `gb` of the garbling algorithm, encoding,
evaluation, decoding and the semantics `ev` are computed in polynomial time, on the security
parameter in unary and the encoded arguments.

For circuit garbling, `encConventionalCircuit` encodes a conventional circuit by `n` and `m` in
unary followed by its gates, each the binary numbers of its two argument wires and its truth table
as four bits; `encValidCircuit` restricts it to valid circuits. `encValidTopo` encodes the
topology `(n, m, q, A, B)` revealed by `phiTopo` in the same layout without the truth tables, and
`encPrvView` encodes the view `(F, X, d)` of a privacy adversary.

The plaintext wire values and the semantics `evalCirc` of a valid circuit are computed in
polynomial time from its word (`wires_polyTime`, `evalCirc_polyTime`), by a fold over the gates
whose state grows by one bit per gate. This is the `ev` field of `Scheme.IsEfficient` for every
scheme whose semantics is `evalCirc`.

## Main definitions

* `Cslib.Crypto.Garbling.Scheme.encGarbled`: the encoding of a garbled triple `(F, e, d)`.
* `Cslib.Crypto.Garbling.Scheme.IsEfficient`: polynomial-time algorithms.
* `Cslib.Crypto.Garbling.ConventionalCircuit.gateList`,
  `Cslib.Crypto.Garbling.encConventionalCircuit`, `Cslib.Crypto.Garbling.encValidCircuit`:
  conventional circuits as data.
* `Cslib.Crypto.Garbling.Topo.gateList`, `Cslib.Crypto.Garbling.encTopo`,
  `Cslib.Crypto.Garbling.encValidTopo`: topologies, the side information of `phiTopo`, as data.
* `Cslib.Crypto.Garbling.encPrvView`, `Cslib.Crypto.Garbling.encQuery`: the encodings of a
  privacy view `(F, X, d)` and of a query `(f, x)`.

## Main results

* `Cslib.Crypto.Garbling.evalCirc_polyTime`: the semantics of valid circuits is computed in
  polynomial time.
* `Cslib.Crypto.Garbling.phiTopo_polyTime`: so is the side information `Φ_topo`.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM

namespace Scheme

/-- The encoding of a garbled triple `(F, e, d)`: `F` and `e` framed, then `d`
(`encGarbled_apply`). -/
enc_structure encGarbled : Garbled where
  fn : encBits, encInfo : encBits, decInfo : encBits

variable {Fn : Type}

/-- A garbling scheme is **efficient** for the encoding `encFn` of its function descriptions when
its algorithms run in polynomial time: the length readers `f.n` and `f.m` on the encoded function,
the number of coins and the deterministic core `gb` of `Gb` on the parameter in unary and the
encoded function (and coins), and `En`, `Ev`, `De` and `ev` on their encoded arguments.
[BellareHoangRogaway2012], §3.1, fixes linear-time algorithms for `f.n` and `f.m`; here they are
only required to run in polynomial time. -/
structure IsEfficient (G : Scheme Fn) (encFn : Fn ↪ List Bool) : Prop where
  /-- The input length `f.n` is read from `f` in polynomial time, in unary. -/
  inLen : ComputableInPolyTime G.inLen encFn encUnary
  /-- The output length `f.m` is read from `f` in polynomial time, in unary. -/
  outLen : ComputableInPolyTime G.outLen encFn encUnary
  /-- The number of coins is polynomial-time computable in unary. -/
  coins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary
  /-- The deterministic core of garbling is polynomial-time on `(1^k, f, r)`. -/
  gb : ComputableInPolyTime (fun (k, f, coins) => G.gb k f coins)
    (encPair encUnary (encPair encFn encBits)) encGarbled
  /-- Encoding is polynomial-time on `(e, x)`. -/
  encode : ComputableInPolyTime (fun (e, x) => G.encode e x) (encPair encBits encBits) encBits
  /-- Evaluation is polynomial-time on `(F, X)`. -/
  evalGarbled : ComputableInPolyTime (fun (F, X) => G.evalGarbled F X) (encPair encBits encBits)
    encBits
  /-- Decoding is polynomial-time on `(d, Y)`. -/
  decode : ComputableInPolyTime (fun (d, Y) => G.decode d Y) (encPair encBits encBits)
    (encOption encBits)
  /-- The semantics is polynomial-time on `(f, x)`. -/
  ev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits

end Scheme

namespace ConventionalCircuit

/-- The gates of a conventional circuit as data: for each gate its argument wires `A g` and `B g`
and its truth table as the four bits `G g 0 0`, `G g 0 1`, `G g 1 0`, `G g 1 1`. -/
@[expose] def gateList (f : ConventionalCircuit) : List (ℕ × ℕ × List Bool) :=
  List.ofFn fun g => (f.A g, f.B g,
    [f.G g false false, f.G g false true, f.G g true false, f.G g true true])

@[simp] theorem length_gateList (f : ConventionalCircuit) : f.gateList.length = f.q := by
  simp [gateList]

/-- A conventional circuit is determined by `n`, `m` and its gates. -/
theorem gateList_injective {f f' : ConventionalCircuit} (hn : f.n = f'.n) (hm : f.m = f'.m)
    (h : f.gateList = f'.gateList) : f = f' := by
  obtain ⟨n, m, q, A, B, G⟩ := f
  obtain ⟨n', m', q', A', B', G'⟩ := f'
  simp only at hn hm
  subst hn hm
  obtain ⟨rfl, hfun⟩ := Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp h)
  have hfun := eq_of_heq hfun
  have hA : A = A' := funext fun g => congrArg Prod.fst (congrFun hfun g)
  have hB : B = B' := funext fun g => congrArg (fun p => p.2.1) (congrFun hfun g)
  have hG : G = G' := funext fun g => funext fun x => funext fun y => by
    have ht := congrArg (fun p => p.2.2) (congrFun hfun g)
    simp only [List.cons.injEq, and_true] at ht
    obtain ⟨h₀, h₁, h₂, h₃⟩ := ht
    cases x <;> cases y <;> assumption
  subst hA hB hG
  rfl

end ConventionalCircuit

/-- The data of a conventional circuit: `n` and `m` in unary, then its gates, each the binary
numbers of its two argument wires followed by its truth table as four bits. -/
abbrev encCircuitData : (ℕ × ℕ × List (ℕ × ℕ × List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList (encPair encNat (encPair encNat encBits))))

/-- **Conventional circuits as words**: `n` and `m` in unary, then the gates in order, each the
binary numbers of its argument wires `A g` and `B g` and its truth table as four bits
(`encCircuitData` of `(n, m, gateList f)`). -/
def encConventionalCircuit : ConventionalCircuit ↪ List Bool :=
  ⟨fun f => encCircuitData (f.n, f.m, f.gateList), fun f f' h => by
    obtain ⟨hn, hrest⟩ := Prod.ext_iff.mp (encCircuitData.injective h)
    obtain ⟨hm, hg⟩ := Prod.ext_iff.mp hrest
    exact ConventionalCircuit.gateList_injective hn hm hg⟩

/-- Valid conventional circuits as words, by `encConventionalCircuit`. -/
def encValidCircuit : ValidCircuit ↪ List Bool :=
  (Function.Embedding.subtype _).trans encConventionalCircuit

/-- A valid circuit's word has at least `n + q` bits: `n` in unary and at least one bit per
gate. -/
theorem n_add_q_le_length_encValidCircuit (f : ValidCircuit) :
    f.1.n + f.1.q ≤ (encValidCircuit f).length := by
  change f.1.n + f.1.q ≤ (encCircuitData (f.1.n, f.1.m, f.1.gateList)).length
  have h := length_le_length_encList (encPair encNat (encPair encNat encBits)) f.1.gateList
  simp only [ConventionalCircuit.length_gateList] at h
  simp only [encCircuitData, length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- The data of a valid circuit is read from its word in polynomial time. -/
theorem circuitData_polyTime :
    ComputableInPolyTime (fun f : ValidCircuit => (f.1.n, f.1.m, f.1.gateList)) encValidCircuit
      encCircuitData :=
  .of_eq fun _ => rfl

/-! ### Evaluating conventional circuits -/

/-- The truth table of a gate read from its four bits, listed as in
`ConventionalCircuit.gateList`. -/
theorem getD_table (G : Bool → Bool → Bool) (x y : Bool) :
    [G false false, G false true, G true false, G true true].getD
      ((if x then 2 else 0) + (if y then 1 else 0)) false = G x y := by
  cases x <;> cases y <;> rfl

/-- One gate of the plaintext evaluation, from the gate's data. -/
private def wireStep (ws : List Bool) (gate : ℕ × ℕ × List Bool) : List Bool :=
  ws ++ [gate.2.2.getD ((if ws.getD (min (ws.length + 1) gate.1 - 1) false then 2 else 0) +
    (if ws.getD (min (ws.length + 1) gate.2.1 - 1) false then 1 else 0)) false]

private theorem wires_eq_foldl (f : ConventionalCircuit) (x : List Bool) {s : ℕ} (hs : s ≤ f.q) :
    f.wires x s = (f.gateList.take s).foldl wireStep
      (x.take f.n ++ List.replicate (f.n - x.length) false) := by
  induction s with
  | zero => simp [ConventionalCircuit.wires]
  | succ s ih =>
    have hsq : s < f.q := hs
    rw [List.take_add_one, List.foldl_append, ← ih hsq.le, ConventionalCircuit.wires,
      dite_eq_left hsq]
    have hget : f.gateList[s]? = some (f.A ⟨s, hsq⟩, f.B ⟨s, hsq⟩,
        [f.G ⟨s, hsq⟩ false false, f.G ⟨s, hsq⟩ false true, f.G ⟨s, hsq⟩ true false,
          f.G ⟨s, hsq⟩ true true]) := by
      simp [ConventionalCircuit.gateList, hsq]
    rw [hget]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, wireStep,
      List.getD_min_length_succ_sub_one,
      getD_table, ConventionalCircuit.wireVal, ← List.getD_eq_getElem?_getD]

private theorem wireStep_polyTime :
    ComputableInPolyTime (fun p : (Unit × List Bool) × (ℕ × ℕ × List Bool) => wireStep p.1.2 p.2)
      (encPair (encPair encUnit encBits) (encPair encNat (encPair encNat encBits))) encBits := by
  polytime [wireStep]

/-- **The plaintext wire values** `f.wires x f.q` of a valid circuit on an input, the `n` input
bits followed by the `q` gate values, are computed in polynomial time. -/
theorem wires_polyTime :
    ComputableInPolyTime (fun (f, x) => f.1.wires x f.1.q) (encPair encValidCircuit encBits)
      encBits := by
  have hd : ComputableInPolyTime (fun p : ValidCircuit × List Bool =>
      (p.1.1.n, p.1.1.m, p.1.1.gateList)) (encPair encValidCircuit encBits) encCircuitData :=
    circuitData_polyTime.comp (ComputableInPolyTime.fst _ _)
  have hg : ComputableInPolyTime (fun p : ValidCircuit × List Bool => p.1.1.gateList)
      (encPair encValidCircuit encBits) (encList (encPair encNat (encPair encNat encBits))) :=
    hd.snd'.snd'
  have hn : ComputableInPolyTime (fun p : ValidCircuit × List Bool => p.1.1.n)
      (encPair encValidCircuit encBits) encUnary := hd.fst'
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encUnit) (encL := encList (encPair encNat (encPair encNat encBits)))
    (encB := encBits) (encA := encPair encNat (encPair encNat encBits))
    (encIn := encPair encValidCircuit encBits)
    (step := fun (_ : Unit) ws gate => wireStep ws gate) (par := fun _ => ())
    (list := fun p => p.1.1.gateList)
    (init := fun p => p.2.take p.1.1.n ++ List.replicate (p.1.1.n - p.2.length) false)
    (by polytime) hg (by polytime) wireStep_polyTime (growth := fun _ => 1)
    (PolyBounded.const 1) (fun _ ws gate _ => by
      change (wireStep ws gate).length ≤ ws.length + 1
      simp [wireStep])
  have heq : (fun (f, x) => f.1.wires x f.1.q) = fun p : ValidCircuit × List Bool =>
      p.1.1.gateList.foldl wireStep (p.2.take p.1.1.n ++
        List.replicate (p.1.1.n - p.2.length) false) := by
    funext ⟨f, x⟩
    dsimp only
    rw [wires_eq_foldl _ _ le_rfl,
      List.take_of_length_le (show f.1.gateList.length ≤ f.1.q by simp)]
  rw [heq]
  exact hfold

/-- **The semantics** `evalCirc` of a valid circuit on an input, the semantics `ev` of the
garbling schemes over conventional circuits, is computed in polynomial time. -/
theorem evalCirc_polyTime :
    ComputableInPolyTime (fun (f, x) => f.1.evalCirc x) (encPair encValidCircuit encBits)
      encBits := by
  have hd := circuitData_polyTime.comp (ComputableInPolyTime.fst encValidCircuit encBits)
  have hq := (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have hc := ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' hd.fst' hq)
    hd.snd'.fst'
  convert wires_polyTime.bitsDropWithInput hc using 1
  funext ⟨f, x⟩
  simp [ConventionalCircuit.evalCirc]

namespace Topo

/-- The gates of a topology as data: for each gate its argument wires `A g` and `B g`. -/
@[expose] def gateList (t : Topo) : List (ℕ × ℕ) := List.ofFn fun g => (t.A g, t.B g)

@[simp] theorem length_gateList (t : Topo) : t.gateList.length = t.q := by
  simp [gateList]

/-- A topology is determined by `n`, `m` and its gates. -/
theorem gateList_injective {t t' : Topo} (hn : t.n = t'.n) (hm : t.m = t'.m)
    (h : t.gateList = t'.gateList) : t = t' := by
  obtain ⟨n, m, q, A, B⟩ := t
  obtain ⟨n', m', q', A', B'⟩ := t'
  simp only at hn hm
  subst hn hm
  obtain ⟨rfl, hfun⟩ := Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp h)
  have hfun := eq_of_heq hfun
  have hA : A = A' := funext fun g => congrArg Prod.fst (congrFun hfun g)
  have hB : B = B' := funext fun g => congrArg Prod.snd (congrFun hfun g)
  subst hA hB
  rfl

end Topo

/-- The data of a topology: `n` and `m` in unary, then each gate's argument wires in binary. -/
abbrev encTopoData : (ℕ × ℕ × List (ℕ × ℕ)) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList (encPair encNat encNat)))

/-- **Topologies as words**: `n` and `m` in unary, then the gates in order, each the binary numbers
of its argument wires `A g` and `B g` (`encTopoData` of `(n, m, gateList t)`). This is the layout
of `encConventionalCircuit` without the truth tables. -/
def encTopo : Topo ↪ List Bool :=
  ⟨fun t => encTopoData (t.n, t.m, t.gateList), fun t t' h => by
    obtain ⟨hn, hrest⟩ := Prod.ext_iff.mp (encTopoData.injective h)
    obtain ⟨hm, hg⟩ := Prod.ext_iff.mp hrest
    exact Topo.gateList_injective hn hm hg⟩

/-- Valid topologies, the side information of `phiTopo`, as words by `encTopo`. -/
def encValidTopo : ValidTopo ↪ List Bool :=
  (Function.Embedding.subtype _).trans encTopo

/-- The data of a valid topology is read from its word in polynomial time. -/
theorem topoData_polyTime :
    ComputableInPolyTime (fun t : ValidTopo => (t.1.n, t.1.m, t.1.gateList)) encValidTopo
      encTopoData :=
  .of_eq fun _ => rfl

/-- The topology `Φ_topo(f)` of a valid circuit is computed in polynomial time from its word: drop
the truth table of each gate. -/
theorem phiTopo_polyTime : ComputableInPolyTime phiTopo.phi encValidCircuit encValidTopo := by
  have hd := circuitData_polyTime
  have hgates : ComputableInPolyTime (fun f : ValidCircuit =>
      f.1.gateList.map fun t => (t.1, t.2.1)) encValidCircuit (encList (encPair encNat encNat)) :=
    ComputableInPolyTime.mapWithInput hd.snd'.snd' (by fun_prop)
  refine (hd.fst'.prod (hd.snd'.fst'.prod hgates)).of_enc_eq fun f => ?_
  change encTopoData (f.1.n, f.1.m, f.1.topo.gateList) = encTopoData (f.1.n, f.1.m, _)
  simp only [Topo.gateList, ConventionalCircuit.gateList, ConventionalCircuit.topo, List.map_ofFn]
  rfl

/-- The encoding of a privacy view `(F, X, d)`: `F` and `X` framed, then `d`. -/
enc_structure encPrvView : PrvView where
  fn : encBits, input : encBits, decInfo : encBits

/-- The encoding of a query `(f, x)`: `f` by `encFn`, framed, then `x`. -/
enc_structure encQuery (Fn : Type) (encFn : Fn ↪ List Bool) : Query Fn where
  fn : encFn, input : encBits

/-- Library construction (no cited definition): the state after a `prv.sim` adversary's choice
stage: `((1^k, aux), (query, state))`. -/
abbrev encPrvChosen {Fn σ : Type} (encFn : Fn ↪ List Bool) (encσ : σ ↪ List Bool) :
    ((ℕ × List Bool) × (Query Fn × σ)) ↪ List Bool :=
  encPair (encPair encUnary encBits) (encPair (encQuery Fn encFn) encσ)

/-- Library infrastructure (no cited result): uniform strict PPT combinator for a two-stage
`prv.sim` reduction that runs `B.choose ()`, branches on a polynomial-time guard `guard`, delegates
to `cont` when `guard` holds, and runs `B.guess` on `⊥` otherwise. -/
theorem isOraclePPT_prvSimReduction_of_guard
    {Fn σ : Type} {encFn : Fn ↪ List Bool} {encσ : σ ↪ List Bool}
    {B : ℕ → PrvSimAdversary Fn σ}
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B)
    (guard : ℕ → Query Fn → Prop) [∀ k q, Decidable (guard k q)]
    (hguard : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query Fn × σ) =>
      decide (guard p.1.1 p.2.1)) (encPrvChosen encFn encσ) encBool)
    (cont : ℕ → Query Fn → σ → Probability.WordOracleComp Unit Bool)
    (hcont : Probability.IsOraclePPTOn (encPrvChosen encFn encσ) encBool
      (fun p => cont p.1.1 p.2.1 p.2.2)) :
    Probability.IsOraclePPT encBool (fun k _ => do
      let (query, state) ← ProbOracleComp.sample ((B k).choose ())
      if guard k query then cont k query state
      else ProbOracleComp.sample ((B k).guess state none)) := by
  have hnone := (hB.guess.preprocess
    (((ComputableInPolyTime.fst (encPair encUnary encBits)
      (encPair (encQuery Fn encFn) encσ)).fst').prod
      (((ComputableInPolyTime.snd _ _).snd').prod
        (ComputableInPolyTime.const (encIn := encPrvChosen encFn encσ)
          (encOut := encOption encPrvView) none)))).isOraclePPTOn (Operation := Unit)
  have hchoose := (hB.choose.preprocess (prepare := fun a : ℕ × List Bool => (a.1, ()))
    ((ComputableInPolyTime.fst encUnary encBits).prod
      (ComputableInPolyTime.const ()))).isOraclePPTOn (Operation := Unit)
  exact hchoose.bind_with (Probability.IsOraclePPTOn.ite hguard hcont hnone)

/-- Library infrastructure (no cited result): uniform strict PPT combinator for a two-stage
`prv.sim` reduction that checks `query.input.length = n query.fn ∧ mult * q query.fn ≤ 2 ^ k`,
samples `coinLen k query.fn` uniform coin bits and delegates to `cont`, or runs `B.guess` on `⊥`.
-/
theorem isOraclePPT_prvSimReduction_of_bounded
    {Fn σ : Type} {encFn : Fn ↪ List Bool} {encσ : σ ↪ List Bool}
    {B : ℕ → PrvSimAdversary Fn σ}
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B)
    {n q : Fn → ℕ} (mult : ℕ) {coinLen : ℕ × Fn → ℕ}
    (hn : ComputableInPolyTime n encFn encUnary)
    (hq : ComputableInPolyTime q encFn encUnary)
    (hlen : ComputableInPolyTime coinLen (encPair encUnary encFn) encUnary)
    (cont : ℕ → Query Fn → σ → List Bool → Probability.WordOracleComp Unit Bool)
    (hcont : Probability.IsOraclePPTOn (encPair (encPrvChosen encFn encσ) encBits) encBool
      (fun p => cont p.1.1.1 p.1.2.1 p.1.2.2 p.2)) :
    Probability.IsOraclePPT encBool (fun k _ => do
      let (query, state) ← ProbOracleComp.sample ((B k).choose ())
      if query.input.length = n query.fn ∧ mult * q query.fn ≤ 2 ^ k then do
        let coins ← ProbOracleComp.sample (BitString.sampleList (coinLen (k, query.fn)))
        cont k query state coins
      else ProbOracleComp.sample ((B k).guess state none)) := by
  let E := encPrvChosen encFn encσ
  have hk : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query Fn × σ) => p.1.1) E
      encUnary := (ComputableInPolyTime.fst _ _).fst'
  have hquery : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query Fn × σ) => p.2.1) E
      (encQuery Fn encFn) := (ComputableInPolyTime.snd _ _).fst'
  have hfn := encQuery_fn_polyTime Fn encFn hquery
  have hx := encQuery_input_polyTime Fn encFn hquery
  have hcond : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query Fn × σ) =>
      decide (p.2.1.input.length = n p.2.1.fn ∧ mult * q p.2.1.fn ≤ 2 ^ p.1.1)) E encBool :=
    ComputableInPolyTime.decide_and
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits_comp hx) (hn.comp hfn))
      (ComputableInPolyTime.binary_le'
        (ComputableInPolyTime.unary_to_binary.comp
          (ComputableInPolyTime.unary_mul.comp
            ((ComputableInPolyTime.const mult).prod (hq.comp hfn))))
        (ComputableInPolyTime.binary_two_pow.comp hk))
  have hcoins := (Probability.isPPTOn_sampleList.preprocess
    (hlen.comp (hk.prod hfn))).isOraclePPTOn (Operation := Unit)
  exact isOraclePPT_prvSimReduction_of_guard hB
    (fun k query => query.input.length = n query.fn ∧ mult * q query.fn ≤ 2 ^ k)
    hcond (fun k query state => do
      let coins ← ProbOracleComp.sample (BitString.sampleList (coinLen (k, query.fn)))
      cont k query state coins) (hcoins.bind_with hcont)

/-- Library construction (no cited definition): one word-oracle step querying `req` and appending
the reply truncated to `len` bits. -/
@[expose] noncomputable def replyStepWord (len : ℕ) (req : List Bool) (rs : List (List Bool)) :
    Probability.WordOracleComp Unit (List (List Bool)) :=
  (fun reply => rs ++ [reply]) <$> (List.take len <$> ProbOracleComp.query
    (spec := fun _ : Unit × List Bool => List Bool) ((), req))

/-- Library infrastructure (no cited result): one `replyStepWord` step is uniform strict oracle
PPT whenever the request and length bound are computed in polynomial time. -/
theorem isOraclePPTOn_replyStepWord {γ : Type} {encIn : γ ↪ List Bool}
    {len : γ → ℕ} {req : γ × List (List Bool) → List Bool}
    (hlen : ComputableInPolyTime len encIn encUnary)
    (hreq : ComputableInPolyTime req (encPair encIn (encList encBits)) encBits) :
    Probability.IsOraclePPTOn (encPair encIn (encList encBits)) (encList encBits)
      (fun p : γ × List (List Bool) => replyStepWord (len p.1) (req p) p.2) := by
  let E := encPair encIn (encList encBits)
  have hfst := ComputableInPolyTime.fst encIn (encList encBits)
  have hrs := ComputableInPolyTime.snd encIn (encList encBits)
  have hnil : ComputableInPolyTime (fun _ : (γ × List (List Bool)) × List Bool =>
      ([] : List (List Bool))) (encPair E encBits) (encList encBits) := ComputableInPolyTime.const _
  have hpost : ComputableInPolyTime (fun p : (γ × List (List Bool)) × List Bool =>
      p.1.2 ++ [p.2]) (encPair E encBits) (encList encBits) :=
    ComputableInPolyTime.listAppend' (hrs.comp (ComputableInPolyTime.fst E encBits))
      (ComputableInPolyTime.cons' (ComputableInPolyTime.snd E encBits) hnil)
  unfold replyStepWord
  exact Probability.IsOraclePPTOn.map_with
    (Probability.IsOraclePPTOn.query_take () hreq (hlen.comp hfst)) hpost

/-- Library infrastructure (no cited result): a `replyStepWord len` step increases the encoded
reply-list length by at most `2 * len + 2`. -/
theorem length_le_of_mem_support_replyStepWord {len : ℕ} {req : List Bool}
    {rs next : List (List Bool)}
    (hnext : next ∈ OracleComp.support (replyStepWord len req rs)) :
    (encList encBits next).length ≤ (encList encBits rs).length + (2 * len + 2) := by
  unfold replyStepWord at hnext
  obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
  simp only [length_encList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, encBits_apply, List.length_take]
  omega

/-- Library infrastructure (no cited result): iterating `replyStepWord len (req ·.length)` from
`[]` for `c` steps against a pure-answering word oracle collects `(List.range c).map` of the
replies truncated to `len` bits. -/
theorem run_iterate_replyStepWord (len c : ℕ) (req : ℕ → List Bool)
    (O : Unit × List Bool → ProbComp (List Bool)) (ans : ℕ → List Bool)
    (hO : ∀ idx < c, O ((), req idx) = pure (ans idx)) :
    ProbOracleComp.run
        (OracleComp.iterate c (fun rs => replyStepWord len (req rs.length) rs) []) O =
      pure ((List.range c).map fun idx => (ans idx).take len) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih fun idx h => hO idx (by omega),
      pure_bind]
    simp [replyStepWord, ProbOracleComp.run_map, ProbOracleComp.run_query,
      hO c (Nat.lt_succ_self c), List.range_succ]

/-- Library infrastructure (no cited result): iterating `replyStepWord` from `[]` for a
polynomial-time unary count `count` is uniform strict oracle PPT whenever the reply cap `len` and
request function `req` are computed in polynomial time. -/
theorem isOraclePPTOn_iterate_replyStepWord {γ : Type} {encIn : γ ↪ List Bool}
    {count len : γ → ℕ} {req : γ × List (List Bool) → List Bool}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hlen : ComputableInPolyTime len encIn encUnary)
    (hreq : ComputableInPolyTime req (encPair encIn (encList encBits)) encBits) :
    Probability.IsOraclePPTOn encIn (encList encBits)
      (fun p : γ => OracleComp.iterate (count p)
        (fun rs => replyStepWord (len p) (req (p, rs)) rs) []) := by
  have hgrowth : ComputableInPolyTime (fun p => 2 * len p + 2) encIn encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hlen)
      (ComputableInPolyTime.const 2)
  exact Probability.IsOraclePPTOn.iterateWith_of_bounded_growth (Operation := Unit)
    (stateEncoding := encList encBits) hcount (ComputableInPolyTime.const [])
    (isOraclePPTOn_replyStepWord hlen hreq)
    (hgrowth.polyBounded_length.mono fun _ => by simp)
    (fun _ _ _ hnext => length_le_of_mem_support_replyStepWord hnext)

end Cslib.Crypto.Garbling
