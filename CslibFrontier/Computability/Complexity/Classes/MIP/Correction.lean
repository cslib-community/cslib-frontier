/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.AxisTest
public import CslibFrontier.Computability.Complexity.Classes.MIP.LineTest
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Recovering an oracle value by checking a random affine line

The verifier reads the coefficient word of a line through the requested point, then checks the
values of the point table at its first `n + 1` positive nodes. It returns the polynomial value
at zero when all comparisons succeed. Each coordinate of the direction comes from bounded fair
coins. The coefficient word, the point values and the random direction belong to the same
static bit-oracle experiment.
-/

public section

namespace Cslib.Complexity.MIP

open Polynomial (evalCoeffListMod)

open Cslib.Probability Turing.MultiTapeTM QBFProtocol

/-- The coefficient word for an affine line, with tag `111` and the framed unary coordinate
lists of its evaluation point and direction. -/
@[expose] def correctionKey (point direction : List ℕ) : List Bool :=
  true :: true :: true :: encPair (encList encUnary) (encList encUnary) (point, direction)

/-- The bits supplied by a fixed proof for the polynomial on the line through `x` along `v`. -/
@[expose] def correctionReply (π : List Bool → Bool) {p n : ℕ} (x v : Fin n → ZMod p) : List Bool :=
  let key := correctionKey (List.ofFn fun j => (x j).val) (List.ofFn fun j => (v j).val)
  List.ofFn fun i : Fin (replyLimit p n) => π (encPair encBits encNat (key, i.val))

/-- The deterministic line check on the tables of the same proof, evaluated on field elements. -/
@[expose] def correctionAnswer (π : List Bool → Bool) {p n : ℕ} [NeZero p]
    (x v : Fin n → ZMod p) : Option ℕ :=
  let word := correctionReply π x v
  let reads := List.ofFn fun i : Fin (n + 1) =>
    (proofPoint π p (x + ((i.val + 1 : ℕ) : ZMod p) • v)).val
  if checkLineReply p n word reads then some (evalCoeffListMod p 0 (decodeReply p n word)) else none

private def linePoint (p n t : ℕ) (point direction : List ℕ) : List ℕ :=
  (List.range n).map fun j => (point.getD j 0 + t * direction.getD j 0) % p

private def pointKeys (p n : ℕ) (point direction : List ℕ) : List (List Bool) :=
  (List.range (n + 1)).map fun i => pointTableKey (linePoint p n (i + 1) point direction)

private def verdict (p n : ℕ) (word : List Bool) (reads : List ℕ) : Option ℕ :=
  if checkLineReply p n word (reads.map fun r => min p (r % p)) then
    some (evalCoeffListMod p 0 (decodeReply p n word))
  else none

/-- Read the fixed-width coefficient word and all point values for a supplied direction. -/
def correctAt (p n : ℕ) (point direction : List ℕ) : WordOracleComp Unit (Option ℕ) := do
  let word ← ProofWord.readBits (correctionKey point direction) (replyLimit p n)
  let reads ← ProofWord.readValues (pointKeys p n point direction) p.size
  pure (verdict p n word reads)

/-- Sample a direction with bounded fair coins and return the checked value at the given point.
A failed comparison returns `none`. -/
@[expose] noncomputable def correctPoint (p n precision : ℕ) (point : List ℕ) :
    WordOracleComp Unit (Option ℕ) := do
  let v ← ProbOracleComp.sample (OracleComp.replicate n
    (ProbComp.sampleModIndex (n.size + p.size + precision) p))
  correctAt p n point v

private theorem linePoint_vals {p n : ℕ} [NeZero p] (x v : Fin n → ZMod p) (t : ℕ) :
    linePoint p n t (List.ofFn fun j => (x j).val) (List.ofFn fun j => (v j).val) =
      List.ofFn fun j => ((x + (t : ZMod p) • v) j).val := by
  rw [linePoint, List.map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp [ZMod.val_add, ZMod.val_mul, ZMod.val_natCast,
    Nat.mod_mul_mod, Nat.add_mod_mod]

/-- The native bit-oracle verifier returns exactly the deterministic field check against the
same fixed proof, including when a field representative is noncanonical or addresses repeat. -/
theorem run_correctAt (π : List Bool → Bool) {p n : ℕ} [Fact p.Prime] (x v : Fin n → ZMod p) :
    (Prover.ofProof π).run (correctAt p n
      (List.ofFn fun j => (x j).val) (List.ofFn fun j => (v j).val)) () =
      PMF.pure (correctionAnswer π x v, ()) := by
  simp only [correctAt, Prover.run_bind, ProofWord.run_readBits, PMF.pure_bind,
    ProofWord.run_readValues, Prover.run_pure]
  congr 2
  unfold verdict correctionAnswer
  congr 1
  unfold pointKeys
  rw [List.map_map, List.map_map, List.map_range_eq_ofFn]
  apply congrArg (fun reads => checkLineReply p n (correctionReply π x v) reads = true)
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, linePoint_vals, proofPoint, ZMod.val_natCast]
  exact min_eq_right (Nat.mod_lt _ (NeZero.pos p)).le

private theorem linePoint_polyTime {α : Type} {enc : α ↪ List Bool} {p n t : α → ℕ}
    {point direction : α → List ℕ} (hp : ComputableInPolyTime p enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (ht : ComputableInPolyTime t enc encUnary)
    (hx : ComputableInPolyTime point enc (encList encUnary))
    (hv : ComputableInPolyTime direction enc (encList encUnary)) :
    ComputableInPolyTime (fun a => linePoint (p a) (n a) (t a) (point a) (direction a))
      enc (encList encUnary) := by
  unfold linePoint
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have hpar := ComputableInPolyTime.fst enc encUnary
  have hj := ComputableInPolyTime.snd enc encUnary
  have hxj := ComputableInPolyTime.listGetDWithInput (hx.comp hpar) hj 0
  have hvj := ComputableInPolyTime.listGetDWithInput (hv.comp hpar) hj 0
  exact (hxj.unary_add' ((ht.comp hpar).unary_mul' hvj)).unary_mod' (hp.comp hpar)

private theorem verdict_polyTime {α : Type} {enc : α ↪ List Bool} {p n : α → ℕ}
    {word : α → List Bool} {reads : α → List ℕ} (hp : ComputableInPolyTime p enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (hw : ComputableInPolyTime word enc encBits)
    (hr : ComputableInPolyTime reads enc (encList encNat)) :
    ComputableInPolyTime (fun a => verdict (p a) (n a) (word a) (reads a))
      enc (encOption encUnary) := by
  have hnorm : ComputableInPolyTime (fun a => (reads a).map fun r => min (p a) (r % p a))
      enc (encList encUnary) := by
    apply ComputableInPolyTime.mapWithInput hr
    have hpar := hp.comp (ComputableInPolyTime.fst enc encNat)
    exact hpar.binary_min_unary' ((ComputableInPolyTime.snd _ _).binary_mod'
      (ComputableInPolyTime.unary_to_binary.comp hpar))
  exact (computableInPolyTime_checkLineReply hp hn hw hnorm).ite
    ((ComputableInPolyTime.optionSome encUnary).comp
      (ComputableInPolyTime.evalCoeffListMod_unary hp (.const 0)
        (computableInPolyTime_decodeReply hp hn hw)))
    (.const none)

/-- The supplied-direction correction verifier is strict polynomial time for unary field
parameters and coordinate lists, including all its individual bit queries. -/
theorem isOraclePPTOn_correctAt {α : Type} {enc : α ↪ List Bool} {p n : α → ℕ}
    {point direction : α → List ℕ} (hp : ComputableInPolyTime p enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hx : ComputableInPolyTime point enc (encList encUnary))
    (hv : ComputableInPolyTime direction enc (encList encUnary)) :
    IsOraclePPTOn enc (encOption encUnary)
      (fun a => correctAt (p a) (n a) (point a) (direction a)) := by
  have hkey : ComputableInPolyTime (fun a => correctionKey (point a) (direction a)) enc encBits :=
    .bitsCons (.const _) (.bitsCons (.const _) (.bitsCons (.const _) (.encoding_comp (hx.prod hv))))
  have hkeys : ComputableInPolyTime (fun a => pointKeys (p a) (n a) (point a) (direction a))
      enc (encList encBits) := by
    unfold pointKeys
    apply ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp (hn.unary_add' (.const 1)))
    have hpar := ComputableInPolyTime.fst enc encUnary
    exact .bitsCons (.const _) (.encoding_comp (linePoint_polyTime (hp.comp hpar) (hn.comp hpar)
      ((ComputableInPolyTime.snd enc encUnary).unary_add' (.const 1))
      (hx.comp hpar) (hv.comp hpar)))
  have hwidth := ComputableInPolyTime.binary_size.comp
    (ComputableInPolyTime.unary_to_binary.comp hp)
  unfold correctAt
  apply (ProofWord.isOraclePPTOn_readBits hkey (computableInPolyTime_replyLimit hp hn)).bind_with
  let e := encPair enc encBits
  have hpar := ComputableInPolyTime.fst enc encBits
  have hctx := ComputableInPolyTime.fst e (encList encNat)
  have hpost : ComputableInPolyTime (fun z : (α × List Bool) × List ℕ =>
      verdict (p z.1.1) (n z.1.1) z.1.2 z.2) (encPair e (encList encNat)) (encOption encUnary) :=
    verdict_polyTime (hp.comp (hpar.comp hctx)) (hn.comp (hpar.comp hctx))
      ((ComputableInPolyTime.snd enc encBits).comp hctx) (.snd _ _)
  simpa only [bind_pure_comp, Function.comp_apply] using
    (ProofWord.isOraclePPTOn_readValues (hkeys.comp hpar) (hwidth.comp hpar)).map_with
      (f := fun q values => verdict (p q.1) (n q.1) q.2 values)
      hpost

/-- The bounded-coin correction verifier is strict oracle polynomial time on unary moduli,
dimensions, precision parameters and point coordinates. -/
theorem isOraclePPTOn_correctPoint {α : Type} {enc : α ↪ List Bool} {p n precision : α → ℕ}
    {point : α → List ℕ} (hp : ComputableInPolyTime p enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (hq : ComputableInPolyTime precision enc encUnary)
    (hx : ComputableInPolyTime point enc (encList encUnary)) :
    IsOraclePPTOn enc (encOption encUnary)
      (fun a => correctPoint (p a) (n a) (precision a) (point a)) := by
  have hnsize := ComputableInPolyTime.binary_size.comp
    (ComputableInPolyTime.unary_to_binary.comp hn)
  have hpsize := ComputableInPolyTime.binary_size.comp
    (ComputableInPolyTime.unary_to_binary.comp hp)
  have hdir := (isPPTOn_sampleModIndex ((hnsize.unary_add' hpsize).unary_add' hq) hp).replicate hn
  exact hdir.isOraclePPTOn.bind_with (second := fun a v => correctAt (p a) (n a) (point a) v)
    (isOraclePPTOn_correctAt (hp.comp (.fst _ _)) (hn.comp (.fst _ _))
      (hx.comp (.fst _ _)) (.snd _ _))

end Cslib.Complexity.MIP
