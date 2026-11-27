/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Game.RepeatedInversion.SlotBound
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Probability.PMF.Bind

/-!
# Repeated one-way functions

A `RevealInverter` receives the unary security parameter `n` and the framed bit list of `t n`
images of uniform `n`-bit inputs under `f`, may submit reveal requests whose slot indices are read
as request bit lengths (`requestSlot`), and wins `repeatedInversionGameOn f valid` when it outputs,
for a slot it never revealed, a preimage `x` with `valid n x`. With
`valid n w = decide (w.length = n)` this is Attack Game 13.3 on `X = {0,1}ⁿ`.

The word-level reduction `repeatedInverter` samples a dyadic index `g < dyadicSize (t n)` and,
when `g < t n`, runs `slotInverter` with `d = 1` (`isPPT_repeatedInverter`), incurring the
dyadic-range factor `dyadicSize (t n)` in `succProbability_repeatedInversionGameOn_le`. It
forwards the adversary's claimed preimage unchanged, so the domain check of the repeated game
becomes the domain check of `inversionGameOn`. For every function that is one-way on a domain
containing the `n`-bit words and every unary polynomial-time repetition schedule `t`, every
uniform strict oracle PPT adversary succeeds with negligible probability
(`OneWayOn.repeatedInversion_negligible`).

## Main definitions

* `Cslib.Crypto.RevealInverter`: word-level adversary for repeated inversion.
* `Cslib.Crypto.requestSlot`: unary slot index read from a query word's length.
* `Cslib.Crypto.RevealInverter.toTyped`: typed game view of a `RevealInverter`.
* `Cslib.Crypto.repeatedInversionGameOn`: word-level Attack Game 13.3 on `n`-bit inputs, with
  answers checked against a declared domain.
* `Cslib.Crypto.repeatedInverter`: dyadic plug-and-pray inverter reduction.

## Main results

* `Cslib.Crypto.isPPT_repeatedInverter`: `repeatedInverter` is uniform strict PPT.
* `Cslib.Crypto.succProbability_repeatedInversionGameOn_le`: concrete reduction bound with factor
  `dyadicSize (t n)`.
* `Cslib.Crypto.OneWayOn.repeatedInversion_negligible`: **Lemma 13.5** ([BonehShoup2023],
  p. 539), asymptotic repeated one-wayness for polynomial-time `t`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 13.4.1, Attack Game 13.3 and Lemma 13.5, pp. 539–540; Section 8.11.1, Definition 8.6,
  p. 336.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An adversary of the repeated games on words: it receives the unary parameter and the encoded
list of images, sends reveal requests, and returns a request word naming a slot together with a
claimed preimage. The same shape as a signature `Forger`. -/
abbrev RevealInverter := ℕ → List Bool → WordOracleComp Unit (List Bool × List Bool)

/-- A request names the slot given by its length (a unary index; the bits are ignored). -/
abbrev requestSlot (q : Unit × List Bool) : ℕ := q.2.length

/-- The typed adversary played by a word adversary at parameter `n`. -/
@[expose] def RevealInverter.toTyped (adversary : RevealInverter) (n : ℕ)
    (ys : List (List Bool)) :
    ProbOracleComp (fun _ : Unit × List Bool => List Bool) ((Unit × List Bool) × List Bool) :=
  (fun out => (((), out.1), out.2)) <$> adversary n (encList encBits ys)

/-- Attack Game 13.3 ([BonehShoup2023], p. 539) on words, on a declared domain: the challenger
draws `t n` uniform `n`-bit inputs `x_j` and sends their images `y_j = f x_j`; a reveal request
for slot `j` is answered with `x_j`; the adversary wins with a claim `(ν, x)` when it never
revealed slot `ν`, `valid n x`, and `f x = y_ν`. With `valid n w = decide (w.length = n)` the
domain is the book's `X = {0,1}ⁿ`. Slots are 0-based and named by the length of a request word
(`requestSlot`); a reveal outside the range is answered with `[]`, and a claim outside it loses. -/
@[expose] noncomputable def repeatedInversionGameOn (f : List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (t : ℕ → ℕ) (adversary : RevealInverter) (n : ℕ) :
    ProbComp Bool :=
  forgeExperiment
    (do let xs ← OracleComp.replicate (t n) (BitString.sampleList n); return (xs.map f, xs))
    (.ofSign fun xs q => pure (xs.getD (requestSlot q) default))
    (fun ys _ q x => valid n x && ys[requestSlot q]? == some (f x))
    (fun q _ log => decide (requestSlot q ∉ log.map fun r => requestSlot r.1))
    (adversary.toTyped n)

/-- The inverter of Lemma 13.5 on words: plant the challenge at a dyadic-uniform index. -/
@[expose] noncomputable def repeatedInverter (f : List Bool → List Bool) (t : ℕ → ℕ)
    (adversary : RevealInverter) : Inverter := fun n y => do
  let g ← ProbComp.sampleDyadicIndex (t n)
  if g < t n then
    slotInverter requestSlot (BitString.sampleList n) f (t n) 1 g (adversary.toTyped n) y
  else return []

private theorem slotInverter_toTyped_one_eq_interpret {f : List Bool → List Bool} {t n g : ℕ}
    {adversary : RevealInverter} {y : List Bool} :
    ProbComp.eval (slotInverter requestSlot (BitString.sampleList n) f t 1 g
        (adversary.toTyped n) y) =
      ProbComp.eval (do
        let front ← OracleComp.replicate g (BitString.sampleList n)
        let back ← OracleComp.replicate (t - g - 1) (BitString.sampleList n)
        let res ← (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (fun (request : Unit × List Bool) (_ : Unit) =>
              pure (if request.2.length = g then []
                else (front ++ [] :: back).getD request.2.length [], ())))
          (adversary n (encList encBits (front.map f ++ y :: back.map f)))).run ()
        return if res.1.1.length = g then res.1.2 else []) := by
  have hr : ∀ (xs : List (List Bool)) (ys : List (List Bool)),
      ProbComp.eval (do
        let res ← (adversary.toTyped n ys).run fun q : Unit × List Bool =>
          pure (if q.2.length / 1 = g / 1 then
              if g % 1 < q.2.length % 1 then f^[q.2.length % 1 - g % 1 - 1] y else default
            else chainSlot f 1 xs q.2.length)
        return if res.1.2.length = g then res.2 else []) =
      ProbComp.eval (do
        let res ← (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (fun (request : Unit × List Bool) (_ : Unit) =>
              pure (if request.2.length = g then [] else xs.getD request.2.length [], ())))
          (adversary n (encList encBits ys))).run ()
        return if res.1.1.length = g then res.1.2 else []) := by
    intro xs ys
    have ho : (fun q : Unit × List Bool =>
        pure (if q.2.length / 1 = g / 1 then
            if g % 1 < q.2.length % 1 then f^[q.2.length % 1 - g % 1 - 1] y else default
          else chainSlot f 1 xs q.2.length)) =
        fun q : Unit × List Bool =>
          (pure (if q.2.length = g then [] else xs.getD q.2.length []) : ProbComp (List Bool)) := by
      funext q
      simp [chainSlot, Nat.div_one, Nat.mod_one, Function.iterate_zero, default]
    rw [ho, RevealInverter.toTyped, ProbOracleComp.run_map]
    have hl : (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun (request : Unit × List Bool) (_ : Unit) =>
            pure (if request.2.length = g then [] else xs.getD request.2.length [], ())))
        (adversary n (encList encBits ys))).run () =
        (fun x => (x, ())) <$> (adversary n (encList encBits ys)).run
          (fun q => pure (if q.2.length = g then [] else xs.getD q.2.length [])) := by
      have hstate : (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (fun (request : Unit × List Bool) (_ : Unit) =>
              pure (if request.2.length = g then [] else xs.getD request.2.length [], ())))
          (adversary n (encList encBits ys))) =
          ProbOracleComp.runState (adversary n (encList encBits ys))
            (fun q => StateT.lift (pure (if q.2.length = g then [] else xs.getD q.2.length []))) :=
        rfl
      rw [hstate, ProbOracleComp.runState_lift]
    rw [hl]
    simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map,
      Function.comp_def]
  simp only [slotInverter, Nat.div_one, Nat.mod_one, Function.iterate_one, Nat.sub_self,
    Function.iterate_zero, id_eq, Nat.lt_irrefl, ↓reduceIte, Nat.zero_le, and_true, default,
    ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun front _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun back _ => ?_
  simpa only [requestSlot, Nat.div_one, Nat.mod_one, Function.iterate_one, Nat.sub_self,
    Function.iterate_zero, id_eq, Nat.lt_irrefl, ↓reduceIte, default, ProbComp.eval_bind,
    ProbComp.eval_pure] using
    hr (front ++ [] :: back) (front.map f ++ y :: back.map f)

/-- `repeatedInverter` runs in strict uniform PPT whenever `f`, `t`, and `adversary` are
polynomial-time. -/
theorem isPPT_repeatedInverter {f : List Bool → List Bool} {t : ℕ → ℕ}
    (hf : ComputableInPolyTime f encBits encBits) (ht : ComputableInPolyTime t encUnary encUnary)
    {adversary : RevealInverter} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBits (repeatedInverter f t adversary) := by
  let encNY := encPair encUnary encBits
  let encNYG := encPair encNY encUnary
  let encF := encPair encNYG (encList encBits)
  let encAll := encPair encF (encList encBits)
  have ht_ny : ComputableInPolyTime (fun p : ℕ × List Bool => t p.1) encNY encUnary :=
    ht.comp (ComputableInPolyTime.fst encUnary encBits)
  have hg : IsPPTOn encNY encUnary (fun p : ℕ × List Bool => ProbComp.sampleDyadicIndex (t p.1)) :=
    isPPTOn_sampleDyadicIndex ht_ny
  have hfront_count : ComputableInPolyTime (fun p : (ℕ × List Bool) × ℕ => p.2) encNYG encUnary :=
    ComputableInPolyTime.snd encNY encUnary
  have hn_nyg : ComputableInPolyTime (fun p : (ℕ × List Bool) × ℕ => p.1.1) encNYG encUnary :=
    (ComputableInPolyTime.fst encUnary encBits).comp (ComputableInPolyTime.fst encNY encUnary)
  have hfront : IsPPTOn encNYG (encList encBits)
      (fun p => OracleComp.replicate p.2 (BitString.sampleList p.1.1)) :=
    (isPPTOn_sampleList.preprocess hn_nyg).replicate hfront_count
  have hback_count : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × List (List Bool) => t p.1.1.1 - p.1.2 - 1) encF encUnary :=
    ComputableInPolyTime.unary_sub'
      (ComputableInPolyTime.unary_sub'
        (ht.comp ((ComputableInPolyTime.fst encUnary encBits).comp
          ((ComputableInPolyTime.fst encNY encUnary).comp
            (ComputableInPolyTime.fst encNYG (encList encBits)))))
        ((ComputableInPolyTime.snd encNY encUnary).comp
          (ComputableInPolyTime.fst encNYG (encList encBits))))
      (.const 1)
  have hn_f : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × List (List Bool) => p.1.1.1) encF encUnary :=
    hn_nyg.comp (ComputableInPolyTime.fst encNYG (encList encBits))
  have hback : IsPPTOn encF (encList encBits)
      (fun p => OracleComp.replicate (t p.1.1.1 - p.1.2 - 1) (BitString.sampleList p.1.1.1)) :=
    (isPPTOn_sampleList.preprocess hn_f).replicate hback_count
  let prepare (a : (((ℕ × List Bool) × ℕ) × List (List Bool)) × List (List Bool)) :
      ℕ × List Bool :=
    (a.1.1.1.1, encList encBits (a.1.2.map f ++ a.1.1.1.2 :: a.2.map f))
  have ha_nyg := (ComputableInPolyTime.fst encNYG (encList encBits)).comp
    (ComputableInPolyTime.fst encF (encList encBits))
  have ha_n : ComputableInPolyTime (fun a => a.1.1.1.1) encAll encUnary :=
    (ComputableInPolyTime.fst encUnary encBits).comp
      ((ComputableInPolyTime.fst encNY encUnary).comp ha_nyg)
  have ha_y : ComputableInPolyTime (fun a => a.1.1.1.2) encAll encBits :=
    (ComputableInPolyTime.snd encUnary encBits).comp
      ((ComputableInPolyTime.fst encNY encUnary).comp ha_nyg)
  have ha_g : ComputableInPolyTime (fun a => a.1.1.2) encAll encUnary :=
    (ComputableInPolyTime.snd encNY encUnary).comp ha_nyg
  have ha_front : ComputableInPolyTime (fun a => a.1.2) encAll (encList encBits) :=
    (ComputableInPolyTime.snd encNYG (encList encBits)).comp
      (ComputableInPolyTime.fst encF (encList encBits))
  have ha_back : ComputableInPolyTime (fun a => a.2) encAll (encList encBits) :=
    ComputableInPolyTime.snd encF (encList encBits)
  have hmap_f : ∀ {l : _ → List (List Bool)},
      ComputableInPolyTime l encAll (encList encBits) →
      ComputableInPolyTime (fun a => (l a).map f) encAll (encList encBits) := fun hl =>
    ComputableInPolyTime.mapWithInput hl (hf.comp (ComputableInPolyTime.snd encAll encBits))
  have hprepare : ComputableInPolyTime prepare encAll (encPair encUnary encBits) :=
    ha_n.prod (ComputableInPolyTime.encoding_comp (ComputableInPolyTime.listAppend'
      (hmap_f ha_front) (ComputableInPolyTime.cons' ha_y (hmap_f ha_back))))
  let seeds (a : (((ℕ × List Bool) × ℕ) × List (List Bool)) × List (List Bool)) :
      List (List Bool) :=
    a.1.2 ++ [] :: a.2
  have hseeds : ComputableInPolyTime seeds encAll (encList encBits) :=
    ComputableInPolyTime.listAppend' ha_front (ComputableInPolyTime.cons' (.const []) ha_back)
  let handler (a : (((ℕ × List Bool) × ℕ) × List (List Bool)) × List (List Bool))
      (request : Unit × List Bool) (_ : Unit) : ProbComp (List Bool × Unit) :=
    pure (if request.2.length = a.1.1.2 then []
      else (seeds a).getD request.2.length [], ())
  have hhandler : IsPPTOn (encHandlerCall encAll encUnit encUnit) (encPair encBits encUnit)
      (fun ⟨a, request, s⟩ => handler a request s) := by
    let encCall := encHandlerCall encAll encUnit encUnit
    have hca : ComputableInPolyTime (fun q : _ => q.1) encCall encAll :=
      ComputableInPolyTime.fst encAll (encPair (encPair encUnit encBits) encUnit)
    have hcreq : ComputableInPolyTime (fun q : _ => q.2.1.2) encCall encBits :=
      (ComputableInPolyTime.snd encUnit encBits).comp
        ((ComputableInPolyTime.fst (encPair encUnit encBits) encUnit).comp
          (ComputableInPolyTime.snd encAll (encPair (encPair encUnit encBits) encUnit)))
    have hans : ComputableInPolyTime
        (fun q : _ => if q.2.1.2.length = q.1.1.1.2 then []
          else (seeds q.1).getD q.2.1.2.length []) encCall encBits :=
      ComputableInPolyTime.ite_decide
        (ComputableInPolyTime.unary_eq' (ComputableInPolyTime.length_bits_comp hcreq)
          (ha_g.comp hca))
        (.const [])
        (ComputableInPolyTime.listGetDWithInput (hseeds.comp hca)
          (ComputableInPolyTime.length_bits_comp hcreq) [])
    exact (hans.prod (.const ())).isPPTOn
  have hresources : ComputableInPolyTime
      (fun pair : ((((ℕ × List Bool) × ℕ) × List (List Bool)) × List (List Bool)) × List Bool =>
        (encList encBits (seeds pair.1)).length)
      (encPair encAll encBits) encUnary :=
    ComputableInPolyTime.length_bits_comp
      (ComputableInPolyTime.encoding_comp
        (hseeds.comp (ComputableInPolyTime.fst encAll encBits)))
  have hrun := hadversary.run_interpret_preprocess
    (operationEncoding := encUnit) (stateEncoding := encUnit)
    (handler := handler) (resources := fun a _ => (encList encBits (seeds a)).length)
    hprepare hhandler (.const ()) (fun _ _ => True) (fun _ => trivial) hresources
    (fun a request _ _ result hres => by
      dsimp only [handler] at hres
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hres
      subst hres
      refine ⟨trivial, ?_, Nat.le_add_right _ _⟩
      dsimp only
      split_ifs with heq
      · simp
      · rw [List.getD_eq_getElem?_getD]
        cases hget : (seeds a)[request.2.length]? with
        | none => simp
        | some v =>
          simpa using length_le_encList_of_mem encBits (List.mem_of_getElem? hget))
  have hpost : ComputableInPolyTime
      (fun q : ((((ℕ × List Bool) × ℕ) × List (List Bool)) × List (List Bool)) ×
          ((List Bool × List Bool) × Unit) =>
        if q.2.1.1.length = q.1.1.1.2 then q.2.1.2 else [])
      (encPair encAll (encPair (encPair encBits encBits) encUnit)) encBits := by
    have hq_all := ComputableInPolyTime.fst encAll (encPair (encPair encBits encBits) encUnit)
    have hq_out := (ComputableInPolyTime.fst (encPair encBits encBits) encUnit).comp
      (ComputableInPolyTime.snd encAll (encPair (encPair encBits encBits) encUnit))
    exact ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.length_bits_comp
          ((ComputableInPolyTime.fst encBits encBits).comp hq_out))
        (ha_g.comp hq_all))
      ((ComputableInPolyTime.snd encBits encBits).comp hq_out)
      (.const [])
  let body : ℕ → List Bool → ProbComp (List Bool) := fun n y => do
    let g ← ProbComp.sampleDyadicIndex (t n)
    if g < t n then do
      let front ← OracleComp.replicate g (BitString.sampleList n)
      let back ← OracleComp.replicate (t n - g - 1) (BitString.sampleList n)
      let res ← (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (handler ((((n, y), g), front), back)))
        (adversary n (encList encBits (front.map f ++ y :: back.map f)))).run ()
      return if res.1.1.length = g then res.1.2 else []
    else return []
  have hbody : IsPPT encBits body := by
    refine (hg.bind_with (IsPPTOn.ite
      (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.snd encNY encUnary)
        (ht_ny.comp (ComputableInPolyTime.fst encNY encUnary)))
      (hfront.bind_with (hback.bind_with (hrun.bind_with hpost.isPPTOn)))
      (ComputableInPolyTime.const []).isPPTOn)).isPPT
  refine hbody.congr fun n y => ?_
  simp only [body, repeatedInverter, ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun g _ => ?_
  split_ifs with hg
  · exact slotInverter_toTyped_one_eq_interpret.symm
  · rfl

/-- Tag each image with the validity bit of its argument. Two tagged images of words, one of which
is valid, agree exactly when the other word is valid and has the same image. -/
private def tagValid (valid : ℕ → List Bool → Bool) (f : List Bool → List Bool) (n : ℕ)
    (x : List Bool) : List Bool :=
  valid n x :: f x

/-- On a domain containing the `n`-bit words, the domain game is the repeated game of the tagged
function, played by the adversary that reads the untagged images. -/
private theorem eval_repeatedInversionGameOn_eq {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {t : ℕ → ℕ} {adversary : RevealInverter} {n : ℕ}
    (hvalid : ∀ x : List Bool, x.length = n → valid n x = true) :
    ProbComp.eval (repeatedInversionGameOn f valid t adversary n) =
      ProbComp.eval (repeatedInversionExperiment requestSlot (BitString.sampleList n)
        (tagValid valid f n) (t n) fun ys => adversary.toTyped n (ys.map List.tail)) := by
  simp only [repeatedInversionGameOn, repeatedInversionExperiment, eval_forgeExperiment_eq,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun xs hxs => ?_
  have hvxs : ∀ y ∈ xs, valid n y = true := fun y hy => hvalid y
    (BitString.length_of_mem_support_uniformList (by
      simpa using ((ProbComp.mem_support_replicate_iff _ _ _).mp hxs).2 y hy))
  have hmap : (xs.map (tagValid valid f n)).map List.tail = xs.map f := by
    simp [List.map_map, Function.comp_def, tagValid]
  simp only [hmap]
  congr 1
  funext z
  congr 1
  rw [List.getElem?_map, List.getElem?_map]
  cases h : xs[requestSlot z.1.1]? with
  | none => simp
  | some y =>
    have hy := hvxs y (List.mem_of_getElem? h)
    cases hz : valid n z.1.2 <;> simp [tagValid, hy, hz]

/-- With one slot per chain, planting a tagged challenge for the untagging adversary is planting
the untagged challenge for the adversary itself. -/
private theorem slotInverter_tagValid {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {n T g : ℕ} {adversary : RevealInverter} (c : List Bool) :
    slotInverter requestSlot (BitString.sampleList n) (tagValid valid f n) T 1 g
        (fun ys => adversary.toTyped n (ys.map List.tail)) c =
      slotInverter requestSlot (BitString.sampleList n) f T 1 g (adversary.toTyped n) c.tail := by
  simp [slotInverter, chainSlot, tagValid, List.map_map, Function.comp_def, Nat.mod_one,
    Nat.div_one]

/-- The concrete bound behind the asymptotic statement, on a domain containing the `n`-bit words:
`rOWadv[A, f, t] ≤ dyadicSize (t n) · OWadv[B, f]` for the efficient reduction
`B = repeatedInverter f t A`, the inequality (13.6) of [BonehShoup2023], Lemma 13.5, with the
dyadic range `dyadicSize (t n)` in place of `t`. -/
theorem succProbability_repeatedInversionGameOn_le (f : List Bool → List Bool)
    {valid : ℕ → List Bool → Bool} (t : ℕ → ℕ) (adversary : RevealInverter) {n : ℕ}
    (hvalid : ∀ x : List Bool, x.length = n → valid n x = true) :
    Game.succProbability (ProbComp.eval (repeatedInversionGameOn f valid t adversary n)) ≤
      dyadicSize (t n) * Game.succProbability
        (ProbComp.eval (inversionGameOn f valid (repeatedInverter f t adversary) n)) := by
  have hslot := succProbability_repeatedInversionExperiment_le_sum requestSlot
    (BitString.sampleList n) (tagValid valid f n) (t n)
    (fun ys => adversary.toTyped n (ys.map List.tail))
  let trial : ℕ → Game := fun g =>
    ProbComp.eval (inversionGameOn f valid (fun _ =>
      if g < t n then
        slotInverter requestSlot (BitString.sampleList n) f (t n) 1 g (adversary.toTyped n)
      else fun _ => return []) n)
  have hinv : ProbComp.eval (inversionGameOn f valid (repeatedInverter f t adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (t n)))).bind fun g => trial g.val := by
    simp only [inversionGameOn, repeatedInverter, trial, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_sampleDyadicIndex]
    rw [PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
    rw [PMF.bind_map, PMF.bind_bind]
    refine PMF.bind_congr_on_support _ _ _ fun a _ => ?_
    by_cases hlt : (a : ℕ) < t n <;> simp [hlt, ProbComp.eval_pure]
  have hpos : (0 : ℝ≥0) < dyadicSize (t n) := by exact_mod_cast dyadicSize_pos (t n)
  rw [eval_repeatedInversionGameOn_eq hvalid]
  refine hslot.trans ?_
  rw [hinv, Game.succProbability_uniform, Fintype.card_fin, mul_div_cancel₀ _ hpos.ne',
    Fin.sum_univ_eq_sum_range (fun g => Game.succProbability (trial g))]
  refine (Finset.sum_le_sum fun g hg => ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono (lt_dyadicSize (t n)).le))
  have hlt : g < t n := Finset.mem_range.mp hg
  dsimp only [trial]
  simp only [hlt, ↓reduceIte, Experiment.succProbability]
  apply le_of_eq
  congr 1
  simp only [inversionExperiment, inversionGameOn, slotInverter_tagValid, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun x hx => ?_
  have hvx := hvalid x (BitString.length_of_mem_support_uniformList hx)
  refine PMF.bind_congr_on_support _ _ _ fun y _ => ?_
  congr 1
  rw [Bool.eq_iff_iff]
  cases hy : valid n y <;> simp [tagValid, hvx, hy]

/-- **Lemma 13.5** ([BonehShoup2023], p. 539), asymptotic form: a function that is one-way on a
domain containing the `n`-bit words (Definition 8.6, p. 336) is repeatedly one-way on that domain
(Attack Game 13.3) for every number of instances `t n` that is computable in polynomial time from
unary `n`. With `valid n w = decide (w.length = n)` both games are the book's on `X = {0,1}ⁿ`. The
book's `t` is a parameter of the game; its computability is this formal setting's addition, needed
because the uniform reduction `repeatedInverter` computes `t n` to draw its guess. -/
theorem OneWayOn.repeatedInversion_negligible {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (hf : OneWayOn f valid)
    (hvalid : ∀ n (x : List Bool), x.length = n → valid n x = true)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary)
    (adversary : RevealInverter) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible fun n =>
      Game.succProbability (ProbComp.eval (repeatedInversionGameOn f valid t adversary n)) := by
  have hinv_neg := hf.negligible (repeatedInverter f t adversary)
    (isPPT_repeatedInverter hf.polyTime ht hadversary)
  have hpoly : PolynomiallyBounded fun n => dyadicSize (t n) :=
    dyadicSize_polynomiallyBounded.comp ht.polynomiallyBounded
  exact negligible_of_le (hinv_neg.polynomiallyBounded_mul hpoly) fun n =>
    succProbability_repeatedInversionGameOn_le f t adversary (hvalid n)

end Cslib.Crypto
