/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Rewinding
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.UniformRelabel
import Mathlib.Algebra.Order.Chebyshev

/-!
# The general forking lemma

An algorithm `A` gets coins `s`, drawn from a distribution, and `q` answers `h : Fin q → H`, drawn
independently and uniformly from a finite set `H`, and outputs an optional index `j : Fin q`
together with a result. The *forking algorithm* runs `A` once; if it outputs an index `j`, it
runs `A` again on the same coins and the same answers before `j`, with fresh answers from `j` on
(`splice`). It succeeds when the second run outputs the same index `j` and the two answers at `j`
differ, and it returns both results.

The general forking lemma of Bellare and Neven ([BellareNeven2006], Lemma 1) bounds the success
probability `frk` of forking by the acceptance probability `acc` of one run:
`acc ^ 2 / q - acc / |H| ≤ frk` (`sq_div_sub_le_fork`), and consequently
`acc ≤ q / |H| + √(q · frk)` (`le_add_sqrt_fork`). For each index `j` this is the rewinding lemma
(`Rewinding.sq_sub_le_twice`), with the coins and the answers before `j` as the first stage, the
answer at `j` as the challenge and the answers after `j` as fresh randomness of the second stage;
summing over `j` loses the factor `q` by the Cauchy–Schwarz inequality. Boneh and Shoup prove the
same bound for `r`-impersonation adversaries ([BonehShoup2023], Lemma 19.8).

The algorithm is deterministic given its coins and answers, which is the form forking needs: the
second run reuses the coins. The statements are exact; no efficiency is involved.

## Main definitions

* `Cslib.Probability.Forking.splice`: answers from one vector before an index, another from it on.
* `Cslib.Probability.Forking.accept`: run once and accept when an index is output.
* `Cslib.Probability.Forking.fork`: the forking algorithm.

## Main results

* `Cslib.Probability.Forking.sq_div_sub_le_fork`: `acc ^ 2 / q - acc / |H| ≤ frk`.
* `Cslib.Probability.Forking.le_add_sqrt_fork`: `acc ≤ q / |H| + √(q · frk)`.
* `Cslib.Probability.Forking.mem_support_fork`: what a successful fork returns.

## References

* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Lemma 19.8.
-/

@[expose] public section

namespace Cslib.Probability.Forking

variable {S H β : Type} {q : ℕ}

/-- The answers of `h` before the index `j` and those of `h'` from `j` on. -/
def splice (j : Fin q) (h h' : Fin q → H) : Fin q → H := fun i => if i < j then h i else h' i

/-- A splice at `j` lists as the first `j` answers of `h` followed by those of `h'` from `j` on. -/
theorem ofFn_splice (j : Fin q) (h h' : Fin q → H) :
    List.ofFn (splice j h h') = (List.ofFn h).take j ++ (List.ofFn h').drop j := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₁
  by_cases hi : i < j
  · rw [List.getElem_append_left (by simp; omega)]
    simp [splice, Fin.lt_def, hi]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [Nat.add_sub_cancel' (not_lt.mp hi), splice, Fin.lt_def, hi]

variable [Fintype H] [Nonempty H]

/-- One run: draw coins and uniform answers, and accept when `A` outputs an index. -/
noncomputable def accept (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    PMF Bool := do
  let s ← first
  let h ← PMF.uniformOfFintype (Fin q → H)
  return (A s h).1.isSome

/-- Replay on two supplied tapes with shared coins and the first tape's prefix. Both the
finite program and its probability law use this deterministic fork. -/
def onTapes [DecidableEq H] (A : S → (Fin q → H) → Option (Fin q) × β)
    (s : S) (h h' : Fin q → H) : Option (Fin q × β × β) :=
  let (index, first) := A s h
  match index with
  | none => none
  | some j =>
    let (index', second) := A s (splice j h h')
    if index' = some j ∧ h j ≠ h' j then some (j, first, second) else none

/-- The forking algorithm ([BellareNeven2006]): run `A` on coins `s` and answers `h`; if it
outputs an index `j`, rerun it on `s` and on `splice j h h'` for fresh answers `h'`, and succeed
with both results when the rerun outputs `j` too and `h j ≠ h' j`. -/
noncomputable def fork [DecidableEq H] (first : PMF S)
    (A : S → (Fin q → H) → Option (Fin q) × β) : PMF (Option (Fin q × β × β)) := do
  let s ← first
  let h ← PMF.uniformOfFintype (Fin q → H)
  let h' ← PMF.uniformOfFintype (Fin q → H)
  return onTapes A s h h'

/-- A predicate of the two replies in a successful fork costs at most its largest probability
against a fresh uniform reply. The first run may choose its index after seeing all its answers.
The output's recorded reply must be the answer at the index it names. -/
theorem bad_reply_le [DecidableEq H] (first : PMF S)
    (A : S → (Fin q → H) → Option (Fin q) × β) (reply : β → H)
    (named : ∀ s h j, (A s h).1 = some j → reply (A s h).2 = h j)
    (bad : H → H → Bool) :
    ((fork first A).map (fun r => r.any fun (_, a, b) => bad (reply a) (reply b)) true) ≤
      Finset.univ.sup (fun c => (PMF.uniformOfFintype H).map (bad c) true) := by
  simp only [fork, onTapes, pmf_norm]
  apply Probability.PMF.bind_apply_le_on_support
  intro s _
  apply Probability.PMF.bind_apply_le_on_support
  intro h _
  cases hj : (A s h).1 with
  | none => simp
  | some j =>
    refine le_trans ?_ (Finset.le_sup (f := fun c => (PMF.uniformOfFintype H).map (bad c) true)
      (Finset.mem_univ (h j)))
    rw [← Probability.PMF.pi_map_eval (fun _ : Fin q => PMF.uniformOfFintype H) j,
      Probability.PMF.pi_uniformOfFintype, PMF.map_comp, ← PMF.bind_pure_comp]
    apply Probability.PMF.bind_apply_mono_on_support
    intro h' _
    by_cases hf : (A s (splice j h h')).1 = some j ∧ h j ≠ h' j
    · simp [hf, named s h j hj, named s (splice j h h') j hf.1, splice, Function.comp_def]
    · simp [hf]

/-! ### Splitting the answers at an index -/

/-- Answers from `b` before `j`, the answer `t` at `j`, and answers from `r` after `j`. -/
private def glue (j : Fin q) (b : Fin q → H) (t : H) (r : Fin q → H) : Fin q → H :=
  fun i => if i < j then b i else if i = j then t else r i

/-- Gluing independent uniform parts gives uniform answers. -/
private theorem bind_glue {γ : Type} (j : Fin q) (k : (Fin q → H) → PMF γ) :
    ((PMF.uniformOfFintype (Fin q → H)).bind fun b => (PMF.uniformOfFintype H).bind fun t =>
      (PMF.uniformOfFintype (Fin q → H)).bind fun r => k (glue j b t r)) =
      (PMF.uniformOfFintype (Fin q → H)).bind k := by
  conv_rhs =>
    rw [← Probability.PMF.uniformOfFintype_prod_map_fst (α := Fin q → H)
      (β := (Fin q → H) × H), PMF.bind_map]
  relabel_uniform (fun (x : (Fin q → H) × H × (Fin q → H)) =>
    (glue j x.1 x.2.1 x.2.2, fun i => if i < j then x.2.2 i else x.1 i, x.2.2 j))
  rintro ⟨b₁, t₁, r₁⟩ ⟨b₂, t₂, r₂⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hg, hbr, hrj⟩
  refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ (funext fun i => ?_))
  · by_cases hi : i < j
    · simpa [glue, hi] using congrFun hg i
    · simpa [hi] using congrFun hbr i
  · simpa [glue] using congrFun hg j
  · by_cases hi : i < j
    · simpa [hi] using congrFun hbr i
    · by_cases heq : i = j
      · exact heq ▸ hrj
      · simpa [glue, hi, heq] using congrFun hg i

omit [Fintype H] [Nonempty H] in
private theorem glue_self (j : Fin q) (b : Fin q → H) (t : H) (r : Fin q → H) :
    glue j b t r j = t := by
  simp [glue]

omit [Fintype H] [Nonempty H] in
private theorem splice_glue (j : Fin q) (b b' : Fin q → H) (t t' : H) (r r' : Fin q → H) :
    splice j (glue j b t r) (glue j b' t' r') = glue j b t' r' := by
  funext i
  by_cases h₁ : i < j <;> simp [splice, glue, h₁]

/-! ### One index -/

/-- The first stage at an index: coins, and answers to use before the index. -/
private noncomputable def firstAt (first : PMF S) : PMF (S × (Fin q → H)) := do
  let s ← first
  let b ← PMF.uniformOfFintype (Fin q → H)
  return (s, b)

/-- Accepting with the index `j` is one run of a rewinding experiment. -/
private theorem acceptAt_eq_once (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β)
    (j : Fin q) :
    (do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j) : PMF Bool) =
      Rewinding.once (firstAt first) (fun _ => PMF.uniformOfFintype H)
        (fun _ _ => PMF.uniformOfFintype (Fin q → H))
        (fun x t r => decide ((A x.1 (glue j x.2 t r)).1 = some j)) := by
  simp only [Rewinding.once, firstAt, pmf_norm]
  pmf_swap with s
  exact (bind_glue j fun h => PMF.pure (decide ((A s h).1 = some j))).symm

variable [DecidableEq H]

/-- Forking with the index `j` is two runs of the rewinding experiment. -/
private theorem forkAt_eq_twice (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β)
    (j : Fin q) :
    (do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      let h' ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j ∧ (A s (splice j h h')).1 = some j ∧ h j ≠ h' j) :
      PMF Bool) =
      Rewinding.twice (firstAt first) (fun _ => PMF.uniformOfFintype H)
        (fun _ _ => PMF.uniformOfFintype (Fin q → H))
        (fun x t r => decide ((A x.1 (glue j x.2 t r)).1 = some j)) := by
  simp only [Rewinding.twice, firstAt, pmf_norm]
  pmf_swap with s
  rw [← bind_glue j]
  pmf_swap with b t
  conv_lhs => enter [2, r]; rw [← bind_glue j]
  simp only [splice_glue, glue_self, PMF.bind_const, Bool.decide_and, ne_eq, decide_not,
    Bool.and_assoc]
  pmf_swap

/-! ### Summing over the indices -/

omit [DecidableEq H] [Fintype H] [Nonempty H] in
/-- An event that names one index has probability equal to the sum over all indices. -/
private theorem toReal_bind_match_apply {X : Type} (μ : PMF X) (index : X → Option (Fin q))
    (event : Fin q → X → Prop) [∀ j x, Decidable (event j x)] :
    ((μ.bind fun x => PMF.pure (match index x with
      | none => false
      | some j => decide (event j x))) true).toReal =
      ∑ j, ((μ.bind fun x => PMF.pure (decide (index x = some j ∧ event j x))) true).toReal := by
  rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
  congr 1
  simp only [PMF.bind_apply, PMF.pure_apply]
  rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
  refine tsum_congr fun x => ?_
  rw [← Finset.mul_sum]
  congr 1
  cases hx : index x with
  | none => simp
  | some j =>
    rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
    simp

omit [DecidableEq H] in
/-- The acceptance probability, as a real number. -/
private theorem toReal_accept (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    (accept first A true).toReal = ∑ j, ((do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j) : PMF Bool) true).toReal := by
  have h := toReal_bind_match_apply (first.bind fun s =>
    (PMF.uniformOfFintype (Fin q → H)).map (s, ·)) (fun x => (A x.1 x.2).1) (fun _ _ => True)
  simp only [accept, pmf_norm, and_true] at h ⊢
  refine Eq.trans (congrArg (fun p : PMF Bool => (p true).toReal) ?_) h
  pmf_swap with s h
  cases (A s h).1 <;> rfl

/-- The success probability of forking, as a real number. -/
private theorem toReal_fork (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    ((fork first A).map Option.isSome true).toReal = ∑ j, ((do
      let s ← first
      let h ← PMF.uniformOfFintype (Fin q → H)
      let h' ← PMF.uniformOfFintype (Fin q → H)
      return decide ((A s h).1 = some j ∧ (A s (splice j h h')).1 = some j ∧ h j ≠ h' j) :
        PMF Bool) true).toReal := by
  have h := toReal_bind_match_apply (first.bind fun s =>
    (PMF.uniformOfFintype (Fin q → H)).bind fun h =>
      (PMF.uniformOfFintype (Fin q → H)).map (s, h, ·))
    (fun x => (A x.1 x.2.1).1)
    (fun j x => (A x.1 (splice j x.2.1 x.2.2)).1 = some j ∧ x.2.1 j ≠ x.2.2 j)
  simp only [fork, onTapes, pmf_norm] at h ⊢
  refine Eq.trans (congrArg (fun p : PMF Bool => (p true).toReal) ?_) h
  pmf_swap with s h h'
  cases (A s h).1 with
  | none => rfl
  | some j => by_cases hc : (A s (splice j h h')).1 = some j ∧ h j ≠ h' j <;> simp [hc]

/-! ### The forking lemma -/

/-- **The general forking lemma** ([BellareNeven2006], Lemma 1): forking succeeds with
probability at least `acc ^ 2 / q - acc / |H|`, where `acc` is the probability that one run
outputs an index. -/
theorem sq_div_sub_le_fork (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    (accept first A true).toReal ^ 2 / q - (accept first A true).toReal / Fintype.card H ≤
      ((fork first A).map Option.isSome true).toReal := by
  rw [toReal_fork, toReal_accept]
  set a : Fin q → ℝ := fun j => ((do
    let s ← first
    let h ← PMF.uniformOfFintype (Fin q → H)
    return decide ((A s h).1 = some j) : PMF Bool) true).toReal
  have hcs : (∑ j, a j) ^ 2 / q ≤ ∑ j, a j ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · rw [div_le_iff₀ (Nat.cast_pos.2 hq), mul_comm]
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  calc (∑ j, a j) ^ 2 / q - (∑ j, a j) / Fintype.card H
      ≤ ∑ j, a j ^ 2 - ∑ j, a j / Fintype.card H := by
        linarith [Finset.sum_div Finset.univ a (Fintype.card H : ℝ)]
    _ = ∑ j, (a j ^ 2 - a j / Fintype.card H) := by rw [Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
        simpa only [a, acceptAt_eq_once, forkAt_eq_twice] using Rewinding.sq_sub_le_twice _ _ _

/-- The forking lemma solved for the acceptance probability: `acc ≤ q / |H| + √(q · frk)`. -/
theorem le_add_sqrt_fork (first : PMF S) (A : S → (Fin q → H) → Option (Fin q) × β) :
    (accept first A true).toReal ≤
      q / Fintype.card H + √(q * ((fork first A).map Option.isSome true).toReal) := by
  set ε := (accept first A true).toReal with hεdef
  set N : ℝ := (Fintype.card H : ℝ)
  by_cases hε : ε ≤ q / N
  · exact hε.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have hq : (0 : ℝ) < q := Nat.cast_pos.2 <| Nat.pos_of_ne_zero fun hq0 =>
      hε (by simp [hq0, hεdef, toReal_accept])
    have hsq : (ε - q / N) ^ 2 ≤ q * ((fork first A).map Option.isSome true).toReal :=
      calc (ε - q / N) ^ 2
          ≤ (ε - q / N) ^ 2 + (ε - q / N) * (q / N) :=
            le_add_of_nonneg_right (mul_nonneg (by linarith) (by positivity))
        _ = q * (ε ^ 2 / q - ε / N) := by
            field_simp
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (sq_div_sub_le_fork first A) hq.le
    linarith [le_abs_self (ε - q / N), Real.abs_le_sqrt hsq]

/-- A successful fork comes from one coin sample and two answer vectors that agree before the
returned index `j` and differ at it, on both of which `A` outputs `j`. -/
theorem mem_support_fork {first : PMF S} {A : S → (Fin q → H) → Option (Fin q) × β}
    {j : Fin q} {out out' : β} (hfork : some (j, out, out') ∈ (fork first A).support) :
    ∃ s ∈ first.support, ∃ h h' : Fin q → H, (∀ i < j, h i = h' i) ∧ h j ≠ h' j ∧
      A s h = (some j, out) ∧ A s h' = (some j, out') := by
  supp_cases hfork [fork, onTapes] with ⟨s, hs, h, h', hres⟩
  cases hA : (A s h).1 with
  | none => simp [hA] at hres
  | some j' =>
    simp only [hA] at hres
    split_ifs at hres with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hres
    obtain ⟨rfl, rfl, rfl⟩ := hres
    exact ⟨s, hs, h, splice j h h', fun i hi => by simp [splice, hi],
      by simpa [splice] using hc.2, Prod.ext hA rfl, Prod.ext hc.1 rfl⟩

end Cslib.Probability.Forking
