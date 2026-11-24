/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.AcceptCount
public import CslibFrontier.Computability.Complexity.Problems.TQBF.Closed
public import CslibFrontier.Computability.Complexity.Problems.TQBF.QuantifierFree
public import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Counting the satisfying assignments of a Boolean formula

`QBF.modelCount φ` is the number of satisfying assignments of a formula `φ`: the sets of free
variables of `φ` whose indicator makes `φ` true. For a quantifier-free formula, a Boolean formula
not necessarily in conjunctive normal form, this is the count `#(φ)` of [Arora and Barak, draft
§9.3.2, printed p. 181][AroraBarak07], and `φ` belongs to their `⊕SAT` (Definition 9.14) exactly
when the count is odd. `Cslib.Complexity.SharpSAT` is the count for formulas in conjunctive normal
form.

The counting verifier `Cslib.Complexity.SharpFormula.verifier` reads a certificate as the values
of the free variables of `φ` without repetition, in the order of
`Cslib.Logic.PL.QBF.distinctFreeVars`, and evaluates `φ` from its tokens. On a quantifier-free
formula it accepts exactly one certificate of that length for each satisfying assignment
(`Cslib.Complexity.SharpFormula.acceptCount_verifier`), and it runs in polynomial time
(`Cslib.Complexity.SharpFormula.computableInPolyTime_verifier`).

## Main definitions

* `Cslib.Logic.PL.QBF.modelCount`: the number of satisfying assignments of the free variables.
* `Cslib.Logic.PL.QBF.distinctFreeVars`: the free variables without repetition.
* `Cslib.Complexity.SharpFormula.verifier`: the counting verifier.

## Main results

* `Cslib.Complexity.SharpFormula.acceptCount_verifier`: one certificate for each satisfying
  assignment.
* `Cslib.Complexity.SharpFormula.computableInPolyTime_verifier`: the verifier is polynomial-time.
* `Cslib.Logic.PL.QBF.three_mul_length_distinctFreeVars_le`,
  `Cslib.Complexity.SharpFormula.computableInPolyTime_length_distinctFreeVars`: the certificate
  length is at most a third of the length of the encoding and computable in unary.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07]
-/

public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*} [DecidableEq V]

/-- **The number of satisfying assignments** of `φ`: the sets `S` of free variables of `φ` such
that `φ` is true when exactly the variables of `S` are true. -/
@[expose] def modelCount (φ : QBF V) : ℕ :=
  (φ.freeVars.powerset.filter fun S => φ.eval (fun v => decide (v ∈ S)) = true).card

/-- The free variables of a formula over `ℕ`, without repetition. -/
@[expose] def distinctFreeVars (φ : QBF ℕ) : List ℕ :=
  φ.freeVarList.eraseDupsBy fun a b => decide (a = b)

theorem nodup_distinctFreeVars (φ : QBF ℕ) : φ.distinctFreeVars.Nodup :=
  List.nodup_eraseDupsBy_eq _

theorem mem_distinctFreeVars {φ : QBF ℕ} {v : ℕ} : v ∈ φ.distinctFreeVars ↔ v ∈ φ.freeVars := by
  rw [distinctFreeVars, List.mem_eraseDupsBy_eq, mem_freeVarList]

/-- A formula has at least as many tokens as free variables, counted with multiplicity. -/
theorem length_freeVarList_le_length_tokens (φ : QBF ℕ) :
    φ.freeVarList.length ≤ φ.tokens.length := by
  induction φ with
  | var _ | top | bot => simp [freeVarList, tokens]
  | not _ ih => simp only [freeVarList, tokens, List.length_cons]; omega
  | and _ _ ihφ ihψ | or _ _ ihφ ihψ =>
    simp only [freeVarList, tokens, List.length_cons, List.length_append]; omega
  | ex v φ ih | all v φ ih =>
    simp only [freeVarList, tokens, List.length_cons]
    have := (List.filter_sublist (l := φ.freeVarList) (p := (· != v))).length_le
    omega

/-- Each free variable takes at least three bits of the encoding. -/
theorem three_mul_length_distinctFreeVars_le (φ : QBF ℕ) :
    3 * φ.distinctFreeVars.length ≤ (Cslib.Complexity.encQBF φ).length := by
  have h1 : φ.distinctFreeVars.length ≤ φ.freeVarList.length :=
    (List.eraseDupsBy_sublist _).length_le
  have := length_freeVarList_le_length_tokens φ
  have := Cslib.Complexity.three_mul_length_tokens_le φ
  omega

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SharpFormula

/-- The variables of the list `vs` made true by the certificate `w`: the variable at position `i`
of `vs` takes the value of bit `i` of `w`. -/
@[expose] def trueVars (vs : List ℕ) (w : List Bool) : List ℕ :=
  vs.filter fun v => w.getD (vs.idxOf v) false

/-- **The counting verifier for Boolean formulas**: the certificate gives the values of the free
variables in the order of `distinctFreeVars`, and `φ` is evaluated from its tokens under the
assignment making exactly the variables of `trueVars` true. -/
@[expose] def verifier (x : QBF ℕ × List Bool) : Bool :=
  (x.1.tokens.reverse.foldl
    (QBF.evalStep fun v => (trueVars x.1.distinctFreeVars x.2).contains v) []).headD false

/-- On a quantifier-free formula the verifier evaluates it. -/
theorem verifier_eq {φ : QBF ℕ} (hφ : φ.QuantifierFree) (w : List Bool) :
    verifier (φ, w) = φ.eval fun v => (trueVars φ.distinctFreeVars w).contains v := by
  rw [verifier, QBF.foldl_evalStep hφ, List.headD_cons]

/-- **The counting verifier accepts one certificate for each satisfying assignment** of a
quantifier-free formula: certificates of length `|distinctFreeVars φ|`. -/
theorem acceptCount_verifier {φ : QBF ℕ} (hφ : φ.QuantifierFree) :
    acceptCount verifier φ φ.distinctFreeVars.length = φ.modelCount := by
  classical
  set vs := φ.distinctFreeVars with hvs
  have hnd : vs.Nodup := QBF.nodup_distinctFreeVars φ
  have hidx (i : Fin vs.length) : vs.idxOf vs[(i : ℕ)] = i := hnd.idxOf_getElem _ _
  -- the set of variables made true by a certificate
  let S (w : Fin vs.length → Bool) : Finset ℕ := (trueVars vs (List.ofFn w)).toFinset
  have hmemS (w : Fin vs.length → Bool) (v : ℕ) :
      v ∈ S w ↔ v ∈ vs ∧ (List.ofFn w).getD (vs.idxOf v) false = true := by
    simp [S, trueVars]
  have hS (w : Fin vs.length → Bool) :
      (fun v => (trueVars vs (List.ofFn w)).contains v) = fun v => decide (v ∈ S w) := by
    funext v
    simp [S]
  -- the certificate of a set of free variables
  let W (T : Finset ℕ) : Fin vs.length → Bool := fun i => decide (vs[(i : ℕ)] ∈ T)
  have hSW {T : Finset ℕ} (hT : T ⊆ φ.freeVars) : S (W T) = T := by
    ext v
    rw [hmemS]
    constructor
    · rintro ⟨hv, h⟩
      rw [List.getD_ofFn_of_lt _ (List.idxOf_lt_length_of_mem hv)] at h
      simpa [W, List.getElem_idxOf] using h
    · intro hv
      have hv' : v ∈ vs := QBF.mem_distinctFreeVars.2 (hT hv)
      refine ⟨hv', ?_⟩
      rw [List.getD_ofFn_of_lt _ (List.idxOf_lt_length_of_mem hv')]
      simpa [W, List.getElem_idxOf] using hv
  unfold acceptCount QBF.modelCount
  refine Finset.card_bij' (fun w _ => S w) (fun T _ => W T) (fun w hw => ?_) (fun T hT => ?_)
    (fun w _ => ?_) (fun T hT => hSW (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1))
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun v hv => ?_, ?_⟩
    · exact QBF.mem_distinctFreeVars.1 ((hmemS w v).1 hv).1
    · rw [← hS, ← verifier_eq hφ, hw]
  · simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [verifier_eq hφ, hS, hSW hT.1, hT.2]
  · funext i
    have := hmemS w vs[(i : ℕ)]
    rw [hidx, List.getD_ofFn_of_lt _ i.isLt] at this
    simp [W, this, List.getElem_mem]

/-! ### Polynomial time -/

/-- The free variables without repetition are listed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_distinctFreeVars :
    ComputableInPolyTime QBF.distinctFreeVars encQBF (encList encNat) := by
  unfold QBF.distinctFreeVars
  fun_prop

/-- The length of a certificate is computable in polynomial time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_length_distinctFreeVars :
    ComputableInPolyTime (fun φ : QBF ℕ => φ.distinctFreeVars.length) encQBF encUnary := by
  fun_prop

/-- The counting verifier is polynomial-time, including on certificates of arbitrary length. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encQBF encBits) encBool := by
  have hT : ComputableInPolyTime (fun x : QBF ℕ × List Bool =>
      trueVars x.1.distinctFreeVars x.2) (encPair encQBF encBits) (encList encNat) := by
    have hp := ComputableInPolyTime.id' (encIn := encPair encQBF encBits)
    have hvars := computableInPolyTime_distinctFreeVars.comp hp.fst'
    apply ComputableInPolyTime.filterWithInput (test := fun p v =>
      p.2.getD (p.1.distinctFreeVars.idxOf v) false) hvars
    have hq := ComputableInPolyTime.id'
      (encIn := encPair (encPair encQBF encBits) encNat)
    exact hq.fst'.snd'.bitsGetDWithInput
      ((hvars.comp hq.fst').idxOfWithInput hq.snd') false
  unfold verifier
  exact computableInPolyTime_evalTokens.comp ((ComputableInPolyTime.fst _ _).prod hT)

end SharpFormula

end Cslib.Complexity
