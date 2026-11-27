/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP
public import CslibFrontier.Computability.Circuit.Quantum.PathSum
public import CslibFrontier.Computability.Complexity.Classes.AWPP
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Complexity.Classes.Counting.Space
import CslibFrontier.Computability.Complexity.Classes.SharpP.Aggregation
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# `BQP ⊆ AWPP ⊆ PP`

The acceptance probability of a uniform family of Hadamard–Toffoli circuits is a gap function
divided by a power of two, `acceptGap / 2^h` (`Cslib.Quantum.acceptProb_eq_acceptGap`). Here both
are computed classically. The path simulation `Cslib.Quantum.pathStep` runs in polynomial time
(`Cslib.Quantum.computableInPolyTime_pathStep`), so the acceptance gap is a sum, over pairs of
polynomially long paths, of a polynomial-time integer, which is a `GapP` function; the number `h`
of Hadamard gates is computed in unary. Fenner's characterization of AWPP
(`Cslib.Complexity.AWPP`) then gives `BQP ⊆ AWPP` (`Cslib.Complexity.BQP_subset_AWPP`), and
`AWPP ⊆ PP` gives `BQP ⊆ PP` (`Cslib.Complexity.BQP_subset_PP`). With `PP ⊆ PSPACE`
(`Cslib.Complexity.PP_subset_PSPACE`) this gives `BQP ⊆ PSPACE`
(`Cslib.Complexity.BQP_subset_PSPACE`).

`BQP ⊆ PP` is due to Adleman, DeMarrais and Huang
[Adleman, DeMarrais, Huang][AdlemanDeMarraisHuang1997]. `BQP ⊆ AWPP` is Theorem 3.1 of
[Fortnow, Rogers][FortnowRogers1999], proved there through Lemma 3.2: the acceptance probability of
a quantum Turing machine running for `t` steps, with amplitudes in `{0, ±3/5, ±4/5, ±1}`, is a GapP
function divided by `5^{2t}`. For circuits over the Hadamard and Toffoli gates the denominator is
`2^h` instead. Fortnow and Rogers work with quantum Turing machines; this file works with the
uniform circuit families of `Cslib.Complexity.BQP`.

## Main results

* `Cslib.Quantum.computableInPolyTime_pathStep`,
  `Cslib.Quantum.computableInPolyTime_foldl_pathStep`: the path simulation runs in polynomial
  time.
* `Cslib.Complexity.onesPairGap_mem_GapP`: acceptance overlaps of polynomial-time gate codes
  and registers are `GapP`.
* `Cslib.Complexity.acceptGap_mem_GapP`: the acceptance gap of a uniform family is `GapP`.
* `Cslib.Complexity.BQP_subset_AWPP`, `Cslib.Complexity.BQP_subset_PP`,
  `Cslib.Complexity.BQP_subset_PSPACE`.

## References

* [L. Adleman, J. DeMarrais, M.-D. Huang, *Quantum computability*][AdlemanDeMarraisHuang1997]
* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 web draft][AroraBarak07]
* [L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*][FortnowRogers1999]
* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- One simulation step, written with polynomial-time list operations. -/
private theorem pathStep_eq (p : (List Bool × List Bool × Bool) × GateCode) :
    pathStep p.1 p.2 =
      if p.2.1 then
        (if p.2.2.1 < p.1.1.length then
            p.1.1.take p.2.2.1 ++ p.1.2.1.headD false :: p.1.1.drop (p.2.2.1 + 1) else p.1.1,
          p.1.2.1.tail, p.1.2.2 ^^ (p.1.1.getD p.2.2.1 false && p.1.2.1.headD false))
      else
        (if p.2.2.1 < p.1.1.length then
            p.1.1.take p.2.2.1 ++
              (p.1.1.getD p.2.2.1 false ^^ p.2.2.2.all fun c => p.1.1.getD c false) ::
                p.1.1.drop (p.2.2.1 + 1) else p.1.1,
          p.1.2.1, p.1.2.2) := by
  obtain ⟨⟨s, π, σ⟩, ⟨_ | _, t, cs⟩⟩ := p <;>
    simp only [pathStep, List.set_eq_take_append_cons_drop] <;> rfl

/-- **The path simulation step runs in polynomial time**, with the register and the unread path
as raw bit strings. -/
theorem computableInPolyTime_pathStep :
    ComputableInPolyTime (fun p : (List Bool × List Bool × Bool) × GateCode => pathStep p.1 p.2)
      (encPair (encPair encBits (encPair encBits encBool)) encGateCode)
      (encPair encBits (encPair encBits encBool)) := by
  let encSt := encPair encBits (encPair encBits encBool)
  have hs := (ComputableInPolyTime.fst encSt encGateCode).fst'
  have hp := (ComputableInPolyTime.fst encSt encGateCode).snd'.fst'
  have hsign := (ComputableInPolyTime.fst encSt encGateCode).snd'.snd'
  have hg := ComputableInPolyTime.snd encSt encGateCode
  have ht := hg.snd'.fst'
  have hbit := ComputableInPolyTime.bitsGetDWithInput hs ht false
  have hhead := (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hp
  have hall : ComputableInPolyTime
      (fun p : (List Bool × List Bool × Bool) × GateCode =>
        p.2.2.2.all fun c => p.1.1.getD c false)
      (encPair encSt encGateCode) encBool :=
    ComputableInPolyTime.allWithInput hg.snd'.snd'
      (ComputableInPolyTime.bitsGetDWithInput
        (hs.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _) false)
  have htake := ComputableInPolyTime.bitsTake.comp (hs.prod ht)
  have hdrop := ComputableInPolyTime.bitsDropWithInput hs
    (ComputableInPolyTime.unary_add.comp (ht.prod (ComputableInPolyTime.const 1)))
  have hin := ComputableInPolyTime.unary_lt.comp
    (ht.prod (ComputableInPolyTime.length_bits.comp hs))
  have htail : ComputableInPolyTime
      (fun p : (List Bool × List Bool × Bool) × GateCode => p.1.2.1.tail)
      (encPair encSt encGateCode) encBits := by fun_prop
  simp only [pathStep_eq]
  refine hg.fst'.ite' ?_ ?_
  · simpa only [Function.comp_def, decide_eq_true_eq] using
      (hin.ite' (ComputableInPolyTime.bitsAppend htake (ComputableInPolyTime.bitsCons hhead hdrop))
        hs).prod (htail.prod (ComputableInPolyTime.bool_xor.comp
          (hsign.prod (ComputableInPolyTime.bool_and' hbit hhead))))
  · simpa only [Function.comp_def, decide_eq_true_eq] using
      (hin.ite' (ComputableInPolyTime.bitsAppend htake (ComputableInPolyTime.bitsCons
        (ComputableInPolyTime.bool_xor.comp (hbit.prod hall)) hdrop)) hs).prod (hp.prod hsign)

/-- A simulation step never lengthens the encoded state. -/
private theorem length_encPair_pathStep (st : List Bool × List Bool × Bool) (g : GateCode) :
    (encPair encBits (encPair encBits encBool) (pathStep st g)).length ≤
      (encPair encBits (encPair encBits encBool) st).length + 0 := by
  obtain ⟨s, π, σ⟩ := st
  obtain ⟨_ | _, t, cs⟩ := g <;> simp [pathStep]

/-- **The path simulation runs in polynomial time** on computed gate codes and initial states. -/
theorem computableInPolyTime_foldl_pathStep {γ : Type} {encIn : γ ↪ List Bool}
    {gs : γ → List GateCode} {init : γ → List Bool × List Bool × Bool}
    (hgs : ComputableInPolyTime gs encIn (encList encGateCode))
    (hinit : ComputableInPolyTime init encIn (encPair encBits (encPair encBits encBool))) :
    ComputableInPolyTime (fun c => (gs c).foldl pathStep (init c)) encIn
      (encPair encBits (encPair encBits encBool)) :=
  ComputableInPolyTime.foldl_of_bounded_growth hgs hinit computableInPolyTime_pathStep
    length_encPair_pathStep

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Acceptance overlaps are `GapP` functions**: for gate codes and two registers computed in
polynomial time from the instance, the projected pair gap on the measured wires `S` is a `GapP`
function of the instance. -/
theorem onesPairGap_mem_GapP (S : List ℕ) {gs : α → List GateCode} {X X' : α → List Bool}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits) (hX' : ComputableInPolyTime X' enc encBits) :
    (fun a => onesPairGap S (gs a) (X a) (X' a)) ∈ GapP enc := by
  let h : α → ℕ := fun a => hadamardCount (gs a)
  have hh : ComputableInPolyTime h enc encUnary := by
    simp only [h, hadamardCount_eq_countP]; fun_prop
  -- the simulations along the two paths of a pair
  let run₁ : (α × List Bool) × List Bool → List Bool × List Bool × Bool := fun p =>
    (gs p.1.1).foldl pathStep (X p.1.1, p.1.2, false)
  let run₂ : (α × List Bool) × List Bool → List Bool × List Bool × Bool := fun p =>
    (gs p.1.1).foldl pathStep (X' p.1.1, p.2, false)
  have hrun₁ : ComputableInPolyTime run₁ (encPair (encPair enc encBits) encBits)
      (encPair encBits (encPair encBits encBool)) :=
    computableInPolyTime_foldl_pathStep (by fun_prop) (by fun_prop)
  have hrun₂ : ComputableInPolyTime run₂ (encPair (encPair enc encBits) encBits)
      (encPair encBits (encPair encBits encBool)) :=
    computableInPolyTime_foldl_pathStep (by fun_prop) (by fun_prop)
  let T : (α × List Bool) × List Bool → ℤ := fun p =>
    if (run₁ p).1 = (run₂ p).1 ∧ (S.all fun i => (run₁ p).1.getD i false) = true then
      (if (run₁ p).2.2 ^^ (run₂ p).2.2 then -1 else 1) else 0
  have hall : ComputableInPolyTime
      (fun p : (α × List Bool) × List Bool => S.all fun i => (run₁ p).1.getD i false)
      (encPair (encPair enc encBits) encBits) encBool :=
    ComputableInPolyTime.allWithInput (encA := encUnary) (.const S)
      (ComputableInPolyTime.bitsGetDWithInput
        (hrun₁.fst'.comp (.fst _ _)) (.snd _ _) false)
  have hT : T ∈ GapP (encPair (encPair enc encBits) encBits) :=
    mem_GapP_of_polyTime (by dsimp only [T]; fun_prop)
  convert GapP.sum_bits_mem (GapP.sum_bits_mem hT (r := fun p : α × List Bool => h p.1)
    (by fun_prop)) hh using 2 with a
  rw [onesPairGap]
  rfl

/-- **The projected gap of a uniform family is a `GapP` function** of the instance. -/
theorem onesGap_mem_GapP (F : UniformCircuitFamily) (S : List ℕ) :
    (fun a => onesGap S (F.gates (enc a).length)
      (List.ofFn (inputState (F.width (enc a).length) (enc a)))) ∈ GapP enc := by
  have := F.computableInPolyTime_gates
  have := F.computableInPolyTime_width
  let X : α → List Bool := fun a =>
    enc a ++ List.replicate (F.width (enc a).length - (enc a).length) false
  have hX : ComputableInPolyTime X enc encBits := by dsimp only [X]; fun_prop
  convert onesPairGap_mem_GapP S (gs := fun a => F.gates (enc a).length) (by fun_prop) hX hX
    using 2 with a
  rw [ofFn_inputState (F.le_width _), onesGap_eq_onesPairGap]

/-- **The acceptance gap of a uniform family is a `GapP` function** of the instance. -/
theorem acceptGap_mem_GapP (F : UniformCircuitFamily) :
    (fun a => acceptGap (F.gates (enc a).length)
      (List.ofFn (inputState (F.width (enc a).length) (enc a)))) ∈ GapP enc :=
  onesGap_mem_GapP F [0]

/-- **`BQP ⊆ AWPP`** [Fortnow, Rogers][FortnowRogers1999]: the acceptance probability of a uniform
family is a `GapP` function divided by `2^h`, with `h` computed in polynomial time. -/
theorem BQP_subset_AWPP : BQP enc ⊆ AWPP enc := by
  rintro A ⟨F, hF⟩
  refine mem_AWPP_of_polyTime_exponent (acceptGap_mem_GapP F)
    (r := fun a => hadamardCount (F.gates (enc a).length))
    (by
      have := F.computableInPolyTime_gates
      simp only [hadamardCount_eq_countP]; fun_prop)
    fun a => ?_
  have hp : F.acceptProb (enc a) = _ :=
    acceptProb_eq_acceptGap _ (F.wellFormed (enc a).length) (enc a)
  set g := acceptGap (F.gates (enc a).length)
    (List.ofFn (inputState (F.width (enc a).length) (enc a)))
  set r := hadamardCount (F.gates (enc a).length)
  have hpos : (0 : ℝ) < 2 ^ r := by positivity
  have h0 := (le_div_iff₀ hpos).mp (hp ▸ F.acceptProb_nonneg (enc a))
  have h1 := (div_le_iff₀ hpos).mp (hp ▸ F.acceptProb_le_one (enc a))
  refine ⟨⟨by exact_mod_cast (by linarith : (0 : ℝ) ≤ g),
      by exact_mod_cast (by linarith : (g : ℝ) ≤ 2 ^ r)⟩, fun ha => ?_, fun ha => ?_⟩
  · have := (le_div_iff₀ hpos).mp (hp ▸ (hF a).1 ha)
    exact_mod_cast (by linarith : (2 : ℝ) * 2 ^ r ≤ 3 * g)
  · have := (div_le_iff₀ hpos).mp (hp ▸ (hF a).2 ha)
    exact_mod_cast (by linarith : (3 : ℝ) * g ≤ 2 ^ r)

/-- **`BQP ⊆ PP`** [Adleman, DeMarrais, Huang][AdlemanDeMarraisHuang1997]. -/
theorem BQP_subset_PP : BQP enc ⊆ PP enc :=
  fun _ hA => AWPP_subset_PP (BQP_subset_AWPP hA)

/-- **`BQP ⊆ PSPACE`** [Bernstein, Vazirani][BernsteinVazirani1997], through `BQP ⊆ PP ⊆ PSPACE`.
[Arora and Barak, Theorem 20.25][AroraBarak07]. This is the library's `BQP`, over the fixed gate
set of `Cslib.Complexity.BQP`; the draft allows arbitrary elementary gates, whose equivalence with
this gate set is not formalized. -/
theorem BQP_subset_PSPACE : BQP enc ⊆ PSPACE enc :=
  fun _ hA => PP_subset_PSPACE (BQP_subset_PP hA)

end Cslib.Complexity
