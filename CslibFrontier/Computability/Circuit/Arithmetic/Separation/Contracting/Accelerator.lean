/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.GridSum
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Iterate
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.LowDegProg
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.LetterSubst
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunCount
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunRename
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunValue
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Automaton
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution

/-!
# Accelerators from small circuits

Lemma K.3 of [AnthropicVPVNP2026] (p. 56): there are `B₀`, `C`, `v₀` such that for `v ≥ v₀` and
`a` with `(lg v) ^ (C a) ≤ v`, a circuit with at most `v ^ a` nodes for the member `G.poly m`,
`m ≥ v ^ B₀`, of a family `G` complete for grid sums gives an accelerator of size `v ^ (C (a + 1))`
at the scale `v` (`Contracting.exists_hasAcc_of_computedWithin`). The paper states it for the
permanent, which is complete for grid sums when `2 ≠ 0` (`gridComplete_permFamily`); its proof
notes that it holds for every such family.

The proof follows the paper (p. 57). The value of the universal automaton
(`Uni.exists_universal_automaton`) on words of fewer than `n = v ^ (H - 32) + 1` letters is a
clause sum `Φ` of the code of the word (`Tape.runVal_eq_domainClauseSum`), made one-hot
(`domainClauseSum_eq_clauseSumWith`), restricted to codes (`Tape.domainClauseSum_codeLits`) and
with the input bits as variables (`clauseSum_withInputs`). As a monomial extension it has degree
at most `n`, and at the indicator assignment of a word it takes the value of that word, since no
other code lies below the code of a word (`MvPolynomial.eval_indicator_monomialExtension`,
`Tape.eq_wordCode`). It has at most `1600 B ^ 9` literals, so it is an affine projection of
`G.poly m` (`GridComplete.isAffineProjection_clauseSum`, Corollary E.2). The letters other than the
two of the words of instances are set to `0` (`Tape.letterSubst`), and Lemma K.2 (`lem_lowdeg`)
with `d = n` turns the circuit into the accelerator.

## Main results

* `Contracting.exists_hasAcc_of_computedWithin`: Lemma K.3, for every family complete for grid
  sums.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Definition K.1 (p. 55), Lemma K.3 (p. 56) and its proof (p. 57); modules `Paper.CircuitPhi`
  (`lem_circuit_phi`) and `Paper.Circuit`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Contracting

open Finset MvPolynomial Tape Interpreter

section ClauseSum

variable {F : Type} [Field F] {S Γ Q : Type} [Fintype S] [DecidableEq S] [Fintype Γ]
  [DecidableEq Γ] [Fintype Q] [DecidableEq Q] {t N : ℕ}

/-- The clauses of `Φ`: those of the runs and of the codes, made one-hot, and one for every input
bit. -/
private noncomputable abbrev phiLits (i e : Q) :=
  withInputs (oneHotLits (Sum.elim
    (runLits (Γ := Γ) (S := S) (n := 1) (t := t) (M := N + t + 1) (N := N) i e) codeLits))

omit [DecidableEq Γ] [DecidableEq Q] in
/-- Every clause of `Φ` has a literal. -/
private theorem phiLits_ne_nil (i e : Q) (κ) :
    phiLits (Γ := Γ) (S := S) (t := t) (N := N) i e κ ≠ [] := by
  rcases κ with ((((r | r) | r) | d | p) | b)
  · simp [withInputs, oneHotLits, runLits, stepLits]
  · rcases r <;> simp [withInputs, oneHotLits, runLits, ruleLits]
  · rcases r <;> simp [withInputs, oneHotLits, codeLits, univ_eq_empty_iff]
  · have : Nonempty Q := ⟨i⟩
    rcases d <;> simp [withInputs, oneHotLits, univ_eq_empty_iff]
  · simp [withInputs, oneHotLits]
  · simp [withInputs]

omit [DecidableEq Γ] [DecidableEq Q] in
/-- The clauses of `Φ` have at most `1600 B ^ 9` literals. -/
private theorem sum_length_phiLits_le (i e : Q) {B : ℕ}
    (hB : t + N + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 ≤ B) :
    ∑ κ, (phiLits (Γ := Γ) (S := S) (t := t) (N := N) i e κ).length ≤ 1600 * B ^ 9 := by
  have hE := card_sigma_dom_le (Γ := Γ) (S := S) (Q := Q) (n := 1) (t := t) (M := N + t + 1)
    (B := B) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hlen : ∀ κ, (phiLits (Γ := Γ) (S := S) (t := t) (N := N) i e κ).length ≤
      9 * B ^ 3 + B + 3 := by
    rintro ((((r | r) | r) | d | p) | b)
    · simp [withInputs, oneHotLits, runLits, stepLits]
    · rcases r <;> simp only [withInputs, runLits, Sum.elim_inl, oneHotLits, Sum.elim_inr,
        ruleLits] <;> (try split_ifs) <;> simp only [List.length_cons, List.length_nil] <;> omega
    · rcases r with ⟨p, y, y'⟩ | p
      · simp [withInputs, oneHotLits, codeLits]
      · have := card_filter_le (univ : Finset (Fin N)) (· < p)
        simp only [card_univ, Fintype.card_fin] at this
        simp only [withInputs, Sum.elim_inl, oneHotLits, Sum.elim_inr, codeLits,
          List.length_append, List.length_map, length_toList, card_univ, Fintype.card_option]
        omega
    · have := (Fintype.card_le_of_injective (Sigma.mk d) sigma_mk_injective).trans hE
      simp only [withInputs, oneHotLits, Sum.elim_inl, List.length_map, length_toList, card_univ]
      omega
    · simp [withInputs, oneHotLits]
    · simp [withInputs]
  refine (sum_le_card_nsmul _ _ _ fun κ _ => hlen κ).trans ?_
  rw [smul_eq_mul, card_univ]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
    Fintype.card_congr (CodeRule.equivSum Γ N)]
  have h1 := RunStep.card_le (Γ := Γ) (S := S) (Q := Q) (n := 1) (t := t) (B := B)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := RunRule.card_le (Γ := Γ) (S := S) (n := 1) (t := t) (M := N + t + 1) (B := B)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h3 := RunVar.card_le (S := S) (n := 1) (t := t) (M := N + t + 1) (B := B)
    (by omega) (by omega) (by omega) (by omega)
  have h4 : N * ((Fintype.card Γ + 1) * (Fintype.card Γ + 1)) + N ≤ B ^ 3 + B :=
    calc _ ≤ B * (B * B) + B := by gcongr <;> omega
      _ = B ^ 3 + B := by ring
  have h5 : N * (Fintype.card Γ + 1) ≤ B ^ 2 :=
    calc _ ≤ B * B := by gcongr <;> omega
      _ = B ^ 2 := by ring
  have h6 : Fintype.card (Σ d : RunVar S 1 t (N + t + 1), d.Dom Γ Q) *
      Fintype.card (Σ d : RunVar S 1 t (N + t + 1), d.Dom Γ Q) ≤ 81 * B ^ 6 :=
    (Nat.mul_le_mul hE hE).trans_eq (by ring)
  have hB : 1 ≤ B := by omega
  have p : ∀ k ≤ 6, B ^ k ≤ B ^ 6 := fun k hk => Nat.pow_le_pow_right hB hk
  have : B ^ 5 ≤ B ^ 6 ∧ B ^ 3 ≤ B ^ 6 ∧ B ^ 2 ≤ B ^ 6 ∧
      1 ≤ B ^ 3 ∧ B ≤ B ^ 3 ∧ B ≤ B ^ 6 :=
    ⟨p 5 (Nat.le_succ 5), p 3 (Nat.le_add_left 3 3), p 2 (Nat.le_add_left 2 4),
      Nat.one_le_pow 3 B hB, Nat.le_self_pow (Nat.succ_ne_zero 2) B,
      Nat.le_self_pow (Nat.succ_ne_zero 5) B⟩
  refine (Nat.mul_le_mul (n₂ := 119 * B ^ 6) (m₂ := 13 * B ^ 3) (by omega) (by omega)).trans ?_
  ring_nf
  omega

/-- **The clause sum `Φ`** (proof of Lemma K.3, p. 57). Let `mu` be an automaton with one input
over a field, and `G` a family complete for grid sums with blow-up `κ`. For `t` steps, `N` places,
`B ≥ t + N + |Q| + |S| + |Γ| + 2` and `m ≥ κ 1600 B ^ 9` there is an affine projection `Φ` of
`G.poly m` of degree at most `N` whose value at the code of every word `w` with `|w| < N` is the
value of the automaton on `w` in `t` steps. -/
private theorem exists_isAffineProjection_runVal {G : PolynomialFamily F} {κ : ℕ}
    (hG : GridComplete G κ) (mu : Letter S Unit Γ → Matrix Q Q F) (i e : Q) {B m : ℕ}
    (hB : t + N + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 ≤ B)
    (hm : κ * (1600 * B ^ 9) ≤ m) :
    ∃ Φ : MvPolynomial (Fin N × Option Γ) F, IsAffineProjection Φ (G.poly m) ∧
      Φ.totalDegree ≤ N ∧ ∀ w : List Γ, w.length + 1 ≤ N →
        eval (fun b => if wordCode N w b then 1 else 0) Φ = runVal mu i e t fun _ => w := by
  let φ : Fin 1 ≃ Unit := Equiv.ofUnique _ _
  let mu' := fun a => mu (Letter.congr S Γ φ a)
  let R := runLits (Γ := Γ) (S := S) (n := 1) (t := t) (M := N + t + 1) (N := N) i e
  let W₀ := runWeights (t := t) (M := N + t + 1) mu'
  let W := Sum.elim W₀ (codeWeights : CodeRule Γ N → F)
  have hf (x) : clauseSumWith (oneHotLits (Sum.elim R codeLits)) (oneHotWeights W) x =
      if IsWordCode x then domainClauseSum R W₀ x else 0 := by
    rw [← domainClauseSum_eq_clauseSumWith, domainClauseSum_codeLits]
  refine ⟨clauseSum (phiLits i e) (inputWeights (oneHotWeights W)),
    hG.isAffineProjection_clauseSum _ (phiLits_ne_nil i e) ?_ _ ?_
      ((Nat.mul_le_mul_left κ (sum_length_phiLits_le i e hB)).trans hm), ?_, fun w hw => ?_⟩
  · rintro (b | ⟨d, y⟩)
    · exact ⟨.inr b, _, List.mem_singleton_self _, rfl⟩
    · exact ⟨.inl (.inr (.inl d)), (.inr ⟨d, y⟩, false), by simp [withInputs, oneHotLits], rfl⟩
  · rintro (k | b)
    · exact .inr ⟨_, rfl⟩
    · exact .inl ⟨b, rfl⟩
  · rw [clauseSum_withInputs]
    refine totalDegree_monomialExtension_le _ fun x hx => ?_
    rw [hf, ite_ne_right_iff] at hx
    exact card_ones_le hx.1
  · rw [clauseSum_withInputs, eval_indicator_monomialExtension, sum_eq_single (wordCode N w)]
    · have hc : Tape.code N (fun _ : Fin 1 => w) = wordCode N w :=
        funext fun ⟨_, _⟩ => by simp [Tape.code, wordCode, wordOf]
      rw [hf, ite_eq_left (isWordCode_wordCode w), ← hc, runVal_eq_domainClauseSum _ i e _
        (by omega) (by rw [length_wordOf_ofFn]; simpa using hw)]
      exact runVal_congr φ mu i e t fun _ => w
    · intro x hx hne
      rw [hf]
      exact ite_eq_right fun h => hne (eq_wordCode h (mem_filter.1 hx).2)
    · exact fun h => absurd (mem_filter.2 ⟨mem_univ _, fun _ => id⟩) h

end ClauseSum

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- **Accelerators from small circuits** (Lemma K.3 of [AnthropicVPVNP2026], p. 56). Let `θ` have
finite support and `H ≥ 32`. For every `κ` there are `B₀ > 0`, `C` and `v₀` such that for every
field `F` that is an `A`-algebra and every family `G` over `F` complete for grid sums with blow-up
`κ`: if `v ≥ v₀`, `(lg v) ^ (C a) ≤ v`, `m ≥ v ^ B₀` and `G.poly m` is computed within `v ^ a`
nodes, then `F` has an accelerator of size `v ^ (C (a + 1))` at the scale `v`. -/
theorem exists_hasAcc_of_computedWithin (hθ : (Function.support θ).Finite) {H : ℕ}
    (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ C v₀ : ℕ, 0 < B₀ ∧ ∀ (F : Type) [Field F] [Algebra A F] (G : PolynomialFamily F),
      GridComplete G κ → ∀ v, v₀ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ m, v ^ B₀ ≤ m →
        ComputedWithin (G.poly m) (v ^ a) → HasAcc θ F H v (v ^ (C * (a + 1))) := by
  obtain ⟨S, Γ, Q, _, _, _, _, _, _, mu, i, e, bt, Cu, hbt, huni⟩ :=
    Uni.exists_universal_automaton θ hθ
  obtain ⟨c, hc⟩ := lem_lowdeg
  obtain ⟨l₀, hl₀⟩ := poly_lg ((3 * c + 6000) * (H + 2)) 2
  refine ⟨27 * H + 19, 8 * (H + 1), l₀ + 1600 * κ + 8 * Cu + Fintype.card Q + Fintype.card S +
    Fintype.card Γ + 10000, by omega, fun F _ _ G hG v hv a ha m hm hcomp => ?_⟩
  set n := v ^ (H - 32) + 1 with hn
  have hv1 : 1 ≤ v := by omega
  have hY : 1 ≤ v ^ (H - 32) := Nat.one_le_pow _ _ hv1
  have hYH : v ^ (H - 32) ≤ v ^ H := Nat.pow_le_pow_right hv1 (by omega)
  have hvH : v ≤ v ^ H := Nat.le_self_pow (by omega) v
  -- the clause sum `Φ` of the universal automaton, and its letters named by bits
  obtain ⟨Φ, hΦ, hdeg, hval⟩ := exists_isAffineProjection_runVal hG
    (fun a => (mu a).map (algebraMap A F)) i e (t := v ^ (3 * H + 1)) (N := n)
    (B := v ^ (3 * H + 2)) (by
      have : v ^ (H - 32) ≤ v ^ (3 * H + 1) := Nat.pow_le_pow_right hv1 (by omega)
      have : v ≤ v ^ (3 * H + 1) := Nat.le_self_pow (by omega) v
      have : 3 * v ^ (3 * H + 1) ≤ v * v ^ (3 * H + 1) := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ' v (3 * H + 1)]
      omega) (calc
      κ * (1600 * (v ^ (3 * H + 2)) ^ 9) = 1600 * κ * v ^ (27 * H + 18) := by ring
      _ ≤ v * v ^ (27 * H + 18) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (27 * H + 19) := by ring
      _ ≤ m := hm)
  let Ψ := aeval (letterSubst F bt n) Φ
  have hΨ : ComputedWithin Ψ (5 * (5 * v ^ a)) :=
    (hcomp.of_isAffineProjection hΦ).of_isAffineProjection ⟨_, isAffine_letterSubst bt n, rfl⟩
  have hΨdeg : Ψ.totalDegree ≤ n :=
    (totalDegree_aeval_le (fun b => (isAffine_letterSubst bt n b).totalDegree_le) Φ).trans hdeg
  have hΨval (z : Tree) (hz : z.size ≤ v ^ (H - 32)) (hpl : Plain θ (v ^ H) z) :
      eval (codeB F n (tbits z)) Ψ = algebraMap A F (pv θ z) := by
    have hcode : codeB F n (tbits z) = fun b => if wordCode n (tbits z) b then 1 else 0 := by
      funext b
      simp [codeB, wordCode]
    rw [hcode, eval_aeval_letterSubst hbt, hval _ (by rw [List.length_map, length_tbits]; omega),
      runVal_map, huni _ z _ hpl]
    have hlg : lg (z.size + v ^ H) ≤ z.size + v ^ H := Nat.log_lt_self 2 (by omega)
    calc Cu * (z.size + v ^ H) * lg (z.size + v ^ H) ^ 2
        ≤ Cu * (2 * v ^ H) * (2 * v ^ H) ^ 2 := by gcongr <;> omega
      _ = 8 * Cu * v ^ (3 * H) := by ring
      _ ≤ v * v ^ (3 * H) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (3 * H + 1) := by ring
  -- the program of Lemma K.2, with `M = lg X` bits for the nodes and the places
  obtain ⟨X, hX⟩ : ∃ X, v ^ (a + H + 1) = X := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, lg X = M := ⟨_, rfl⟩
  have hL : 2 ≤ lg v := lg_ge_two (by omega)
  have haL : a ≤ lg v := (Nat.le_mul_of_pos_left a (by omega)).trans
    (le_lg_of_lg_pow_le (by omega) ha)
  have hMv : (3 * c + 6000) * M ≤ v :=
    calc (3 * c + 6000) * M ≤ (3 * c + 6000) * ((H + 2) * lg v * lg v) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [← hM, ← hX]
          exact (lg_pow_le (by omega)).trans (Nat.mul_le_mul_right _ (by nlinarith))
      _ = (3 * c + 6000) * (H + 2) * lg v ^ 2 := by ring
      _ ≤ v := hl₀ v (by omega)
  have hMv' : 6000 * M ≤ v := (Nat.mul_le_mul_right _ (by omega)).trans hMv
  have hvX : v ^ (H + 1) ≤ X := hX ▸ Nat.pow_le_pow_right hv1 (by omega)
  have hvX' : v ≤ X := (Nat.le_self_pow (by omega) v).trans hvX
  have hXM : X < 2 ^ M := hM ▸ lt_two_pow_lg X
  have hM5 : 5 ≤ M := hM ▸ le_lg_of_two_pow_le (k := 4) (by omega)
  obtain ⟨K, D, hnds, hht, hsize, hrun⟩ := hc F M M n n (5 * (5 * v ^ a)) Ψ hΨ (by
    have : 25 * v ^ a ≤ X :=
      calc 25 * v ^ a ≤ v * v ^ a := Nat.mul_le_mul_right _ (by omega)
        _ = v ^ (a + 1) := by ring
        _ ≤ X := hX ▸ Nat.pow_le_pow_right hv1 (by omega)
    omega) (by
      have : v ^ (H - 32) < v ^ H := Nat.pow_lt_pow_right (by omega) (by omega)
      have : v ^ H ≤ v ^ (H + 1) := Nat.pow_le_pow_right hv1 (by omega)
      omega)
  -- the bounds of an accelerator of size `X ^ 8 ≤ v ^ (C (a + 1))`
  have hX8 : X ^ 8 ≤ v ^ (8 * (H + 1) * (a + 1)) := by
    rw [← hX, ← pow_mul]
    exact Nat.pow_le_pow_right hv1 (by nlinarith)
  have hsz := le_max_right (v ^ H) (v ^ (8 * (H + 1) * (a + 1)))
  refine ⟨K, 1, D, ⟨fun z hz => ?_, fun z hz hpl => ?_⟩, ?_, ?_, ?_, Nat.one_le_pow _ _ (by
    simp [lg])⟩
  · obtain ⟨h1, h2, -⟩ := hrun A θ z (by omega)
    refine ⟨h1, fun r hr => ⟨(h2 r hr).1.trans ?_, (h2 r hr).2⟩⟩
    calc (n + 1) * (800 * (M + M) + 4000) + (z.size + 2) * (40 * M + 60) + 10 * M + 100
        ≤ (n + 1) * v + (z.size + 2) * v + v := by
          have := Nat.mul_le_mul_left (n + 1) (show 800 * (M + M) + 4000 ≤ v by omega)
          have := Nat.mul_le_mul_left (z.size + 2) (show 40 * M + 60 ≤ v by omega)
          omega
      _ = (n + z.size + 4) * v := by ring
      _ ≤ v * v ^ (H - 32) * v :=
        Nat.mul_le_mul_right _ ((show _ ≤ 7 * v ^ (H - 32) by omega).trans
          (Nat.mul_le_mul_right _ (by omega)))
      _ = v ^ (H - 32 + 2) := by ring
      _ ≤ v ^ (H - 16) := Nat.pow_le_pow_right hv1 (by omega)
  · rw [(hrun A θ z (by omega)).2.2, ← hΨval z hz hpl]
    exact (sum_congr rfl fun i _ => (coeff_line _ Ψ i).symm).trans
      (sum_coeff_line_eq_eval _ _ hΨdeg n.lt_succ_self)
  · have h2M : 2 ^ M ≤ 2 * X := by
      have := hM ▸ two_pow_lg_le (n := X) (by omega)
      rw [← Nat.sub_add_cancel (m := 1) (Nat.one_le_of_lt hM5), pow_succ]
      omega
    have hX : 51 ≤ X := by omega
    calc K.nds ≤ 2 * (2 ^ M) ^ 3 + 8 * (2 ^ M) ^ 2 + 3 := hnds.trans_eq (by ring)
      _ ≤ 2 * (2 * X) ^ 3 + 8 * (2 * X) ^ 2 + 3 := by gcongr
      _ = 16 * X ^ 3 + 32 * X ^ 2 + 3 := by ring
      _ ≤ X * X ^ 3 := by
        have := Nat.pow_le_pow_right (show 1 ≤ X by omega) (show 2 ≤ 3 by norm_num)
        have := Nat.one_le_pow 3 X (by omega)
        have := Nat.mul_le_mul_right (X ^ 3) hX
        omega
      _ ≤ X ^ 8 := by rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ _ := hX8
  · have hcM : c * (M + M + 1) ≤ v :=
      calc c * (M + M + 1) ≤ c * (3 * M) := Nat.mul_le_mul_left c (by omega)
        _ ≤ (3 * c + 6000) * M := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ v := hMv
    calc D.size ≤ c * (M + M + 1) + 2 * (n + 1) := hsize
      _ ≤ 5 * v ^ H := by omega
      _ ≤ v * v ^ H := Nat.mul_le_mul_right _ (by omega)
      _ ≤ X := by rw [← pow_succ']; exact hvX
      _ ≤ X ^ 8 := Nat.le_self_pow (by norm_num) X
      _ ≤ _ := hX8
  · calc K.ht ≤ 8 * (M - 1) + 1 := by omega
      _ ≤ lg (X ^ 8) := hM ▸ le_lg_pow (by omega)
      _ ≤ lg (max (v ^ H) (v ^ (8 * (H + 1) * (a + 1)))) := lg_mono (hX8.trans hsz)
      _ ≤ _ := Nat.le_self_pow (by norm_num) _

end Cslib.Circuits.Arithmetic.Separation.Contracting
