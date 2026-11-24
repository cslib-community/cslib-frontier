/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Scale
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One scale is all scales: from one scale to the next

`Interpreter.prop_next`, Proposition K.5 (Section K.3) of *VP ≠ VNP over every field*
[AnthropicVPVNP2026]. Under Theorem C (`Interpreter.CutHyp`), an accelerator at a scale `u` with few
constants gives one at the scale `u ^ α`, with the same constants and a program larger only by
lower-order terms. Each round of the proof lowers the exponent of the time bound by `8`, using
`Interpreter.round`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Paper.Next`.

## Main results

* `Interpreter.prop_next`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- Powers of a scale `u ≥ 2000`: each power is at least `2000` times the one before, and all are
positive. -/
theorem scale_bounds {u : ℕ} (hu : 2000 ≤ u) :
    (∀ a, 2000 * u ^ a ≤ u ^ (a + 1)) ∧ ∀ a, 1 ≤ u ^ a :=
  ⟨fun a => (Nat.mul_le_mul_right _ hu).trans_eq (pow_succ' u a).symm,
    fun a => Nat.one_le_pow _ _ (by omega)⟩

/-- Powers of a number at least `10`. -/
theorem pow_bounds {X : ℕ} (hX10 : 10 ≤ X) : 10 * X ^ 2 ≤ X ^ 3 ∧ 10 * X ≤ X ^ 2 :=
  ⟨by
    have : X ^ 3 = X * X ^ 2 := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ hX10,
    by rw [pow_two]; exact Nat.mul_le_mul_right _ hX10⟩

/-- A scale above `cst`, with the sizes of the fixed programs named (so that `omega` does not unfold
them). -/
theorem cst_bounds {u : ℕ} (h : cst ≤ u) :
    ∃ sU sW, sU = UF.code.size ∧ sW = WF.code.size ∧ sW + sU + 2000 ≤ u :=
  ⟨_, _, rfl, rfl, h⟩

/-- **Paper: proof of Proposition K.5, one round.** "One round, from f+8 to f, for f ≥ α(H−32)+40":
from values in v^(f+8) steps to values in v^f steps, with exponent bound max(B_p+J, B); the program
grows by v^(h₀α+2) + v^(H+1). Here e is the paper's f. -/
private theorem prop_next_round {h : ℕ} (hh : 17 ≤ h) {u α : ℕ} (hα : 5 ≤ α)
    (hC : CutAt θ (16 * h) u (2 * α)) (hcst : cst ≤ u) {K : KT R} {B' : ℕ} {D : Tree}
    (hD : IsAccT θ (16 * h) u (u ^ (16 * h - 16)) K B' D) (hK : K.nds ≤ u ^ (h * α))
        (hDs : D.size ≤ u ^ (h * α))
    {p : Tree} {B J X e : ℕ} (hp : IsPre θ (16 * h) (u ^ α) (u ^ (e + 8)) K B p)
        (hps : p.size ≤ u ^ (4 * h * α))
    (hJ : u ^ (e + 8) < 2 ^ J) (hX : K.ht + B + J + 1 ≤ X) (hX10 : 10 ≤ X) (hXu : 1000 * X ^ 3 ≤ u)
    (he1 : α * (16 * h - 32) + 40 ≤ e) (he2 : e + 9 ≤ 16 * h * (2 * α)) :
    ∃ p', IsAccT θ (16 * h) (u ^ α) (u ^ e) K (max (B + J) B') p' ∧
      p'.size ≤ p.size + (u ^ (h * α + 2) + u ^ (16 * h + 1)) := by
  -- basic inequalities
  obtain ⟨hX3, hX2⟩ := pow_bounds hX10
  obtain ⟨sU, sW, hsU, hsW, hcst⟩ := cst_bounds hcst
  have hu4 : 2000 ≤ u := by omega
  have hu1 : 1 ≤ u := by omega
  have hh1 : 5 * h ≤ h * α := by rw [Nat.mul_comm h α]; exact Nat.mul_le_mul_right _ hα
  have hα32 : α * (16 * h - 32) = 16 * (h * α) - 32 * α := by
    rw [Nat.mul_sub]
    congr 1
    · ring
    · ring
  have hαh : 17 * α ≤ h * α := Nat.mul_le_mul_right _ hh
  have he3 : h * α + 3 ≤ e := by omega
  have he4 : 16 * h ≤ e := by omega
  have hH : 16 * h ≤ e + 9 := by omega
  -- the trie of powers
  obtain ⟨nB, hnB⟩ : ∃ n, n = (K.expand B).nds := ⟨_, rfl⟩
  have hnB1 : nB ≤ K.nds * (2 * X) :=
      hnB ▸ (KT.nds_expand B K).trans (Nat.mul_le_mul_left _ (by omega))
  have hnBX : ∀ c, c * X ^ 2 ≤ 1000 * X ^ 3 → nB * (c * X) ≤ 2 * u ^ (h * α + 1) := by
    intro c hc
    calc nB * (c * X) ≤ K.nds * (2 * X) * (c * X) := Nat.mul_le_mul_right _ hnB1
      _ = K.nds * (2 * (c * X ^ 2)) := by ring
      _ ≤ u ^ (h * α) * (2 * u) := Nat.mul_le_mul hK (by omega)
      _ = 2 * u ^ (h * α + 1) := by rw [pow_succ]; ring
  have pu : ∀ a, u ^ (a + 1) = u * u ^ a := pow_succ' u
  obtain ⟨pbig, ppos⟩ := scale_bounds hu4
  -- the cut
  obtain ⟨G, hG⟩ := hC (u ^ (e + 9)) (u ^ (α * (16 * h - 32) + 1)) (Nat.pow_le_pow_right hu1 hH)
    (Nat.pow_le_pow_right hu1 he2) (by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hu1 (by omega))
  obtain ⟨f, hf⟩ : ∃ f, e = f + 15 := ⟨e - 15, by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, e + 11 = g + 16 * h := ⟨e + 11 - 16 * h, by omega⟩
  have h1 := hnBX 1 (by omega)
  have hJX : J + 1 ≤ X := by omega
  have hnBJ : ∀ c, c ≤ 40 → c * (nB * (J + 1)) ≤ u ^ (h * α + 1 + 1) := fun c hc => by
    have := hnBX c (by
      have := Nat.mul_le_mul_right (X ^ 2) hc
      omega)
    calc c * (nB * (J + 1)) ≤ c * (nB * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJX)
      _ = nB * (c * X) := by ring
      _ ≤ 2 * u ^ (h * α + 1) := this
      _ ≤ u ^ (h * α + 1 + 1) := by have := pbig (h * α + 1); omega
  refine ⟨_, round hD hp hJ hG (tG := u ^ f) (Ln := u ^ g) (t := u ^ e) ?_ ?_ ?_ ?_ ?_, ?_⟩
  · -- time of the plain instances
    rw [← hnB]
    have m1 : MM (K.ht + B + J + 1) + 2 ≤ u := by
      unfold MM
      omega
    have m2 : 40 * (nB * (J + 1)) ≤ u ^ (e + 8) := by
      exact (hnBJ 40 (by omega)).trans (Nat.pow_le_pow_right hu1 (by omega))
    have m3 : 40 ≤ u ^ (e + 8) := by
      have h7 : 2000 * u ^ (e + 7) ≤ u ^ (e + 8) := pbig (e + 7)
      have := ppos (e + 7)
      omega
    calc MM (K.ht + B + J + 1) * u ^ (e + 8) + 40 * (nB * (J + 1)) + 40
        ≤ (MM (K.ht + B + J + 1) + 2) * u ^ (e + 8) := by rw [add_mul]; omega
      _ ≤ u * u ^ (e + 8) := Nat.mul_le_mul_right _ m1
      _ = u ^ (e + 9) := (pu (e + 8)).symm
  · -- size of the plain instances
    rw [← hnB, ← hsW]
    have m1 : sW + 3 ≤ u ^ (α * (16 * h - 32)) := by
      calc sW + 3 ≤ u ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := Nat.pow_le_pow_right hu1 (by omega)
    have m2 : p.size ≤ u ^ (α * (16 * h - 32)) := hps.trans (Nat.pow_le_pow_right hu1 (by
      have : 4 * h * α = 4 * (h * α) := by ring
      omega))
    have m3 : (u ^ α) ^ (16 * h - 32) = u ^ (α * (16 * h - 32)) := by rw [← pow_mul]
    have m4 : 4 * (nB * (J + 1)) ≤ u ^ (α * (16 * h - 32)) := by
      exact (hnBJ 4 (by omega)).trans (Nat.pow_le_pow_right hu1 (by omega))
    have := pbig (α * (16 * h - 32))
    rw [m3]
    omega
  · intro k hk
    rw [show e + 9 = f + 24 by omega, pow_add] at hk
    exact Nat.le_of_mul_le_mul_right hk (ppos 24)
  · intro k hk
    rw [← pow_add, show e + 9 + 2 = g + 16 * h by omega, pow_add] at hk
    exact Nat.le_of_mul_le_mul_right hk (ppos _)
  · -- time
    rw [← hnB]
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have m1 : (8 * J + 10) * nB ≤ u ^ e' := by
      have := hnBX 9 (by omega)
      calc (8 * J + 10) * nB ≤ 9 * X * nB := Nat.mul_le_mul_right _ (by omega)
        _ = nB * (9 * X) := by ring
        _ ≤ 2 * u ^ (h * α + 1) := this
        _ ≤ u ^ (h * α + 1 + 1) := by have := pbig (h * α + 1); omega
        _ ≤ u ^ e' := Nat.pow_le_pow_right hu1 (by omega)
    have m2 : u ^ f ≤ u ^ e' := Nat.pow_le_pow_right hu1 (by omega)
    have m3 : (u ^ (16 * h - 16) + 30) * u ^ g ≤ u ^ e' := by
      have : 30 ≤ 30 * u ^ (16 * h - 16) := by have := ppos (16 * h - 16); omega
      calc (u ^ (16 * h - 16) + 30) * u ^ g ≤ (31 * u ^ (16 * h - 16)) * u ^ g :=
          Nat.mul_le_mul_right _ (by omega)
        _ = 31 * u ^ (16 * h - 16 + g) := by rw [pow_add]; ring
        _ ≤ u ^ (16 * h - 16 + g + 1) := by have := pbig (16 * h - 16 + g); omega
        _ ≤ u ^ e' := Nat.pow_le_pow_right hu1 (by omega)
    have m4 : 30 ≤ u ^ e' := by
      obtain ⟨e'', he''⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
      have := pbig e''
      have := ppos e''
      rw [he'']
      omega
    have := pbig e'
    rw [he']
    omega
  · -- size
    have s1 := size_stepF D G p (gt id J B K [])
    rw [← hsW] at s1
    have s2 := hG.size
    have s3 := size_gt id J B K [] (B + J) (fun i hi => (show id i ≤ B + J from hi.le))
    rw [← hnB, List.length_nil] at s3
    obtain ⟨sg, hsg⟩ : ∃ n, n = (gt id J B K []).code.size := ⟨_, rfl⟩
    rw [← hsg] at s1 s3
    have s4 : sg ≤ 2 * u ^ (h * α + 1) := by
      have := hnBX (14 * X) (by
        rw [show 14 * X * X ^ 2 = 14 * X ^ 3 by ring]
        omega)
      calc sg ≤ nB * ((J + 1) * (4 * (0 + K.ht + (B + J)) + 100)) := s3
        _ ≤ nB * (X * (14 * X)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hJX (by omega))
        _ = nB * (14 * X * X) := by ring
        _ ≤ 2 * u ^ (h * α + 1) := this
    have s5 : 2 * D.size ≤ 2 * u ^ (h * α) := Nat.mul_le_mul_left _ hDs
    have s6 : sW + 1500 ≤ u ^ (16 * h) := by
      calc sW + 1500 ≤ u ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := Nat.pow_le_pow_right hu1 (by omega)
    have s7 := pbig (16 * h)
    have s8 : 2000 * u ^ (h * α + 1) ≤ u ^ (h * α + 2) := pbig (h * α + 1)
    have s9 : u ^ (h * α) ≤ u ^ (h * α + 1) := Nat.pow_le_pow_right hu1 (Nat.le_succ _)
    omega

/-- **Paper: Proposition K.5.** Let `v` be large, `α ≥ 5` an integer and `(lg v) ^ (C α) ≤ v` for a
suitable constant `C`, which depends on the fixed power below. A program with the two properties of
an accelerator at scale `v`, with `Q ≤ v ^ (h₀ α)`, program size at most `v ^ (h₀ α)` and with `B`
and the height of its trie at most a fixed power of `α lg v` gives a program with the two properties
of an accelerator at scale `v′ = v ^ α` (without the bounds on height and exponents of Definition
K.1), with the same constants, exponent bound `B + O(α² lg v)` and program size at most
`v′ ^ (4 h₀)`. Its accepting runs take at most `v′ ^ (H − 17)` steps. The two properties are the
fields of `IsAccT`, `k` is the fixed power, and `H = 16 h`. This paraphrases the statement of the
paper, which gives the exponent bound as `B + 51 h₀ α² lg v`. -/
theorem prop_next {h : ℕ} (hh : 17 ≤ h) {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * h) C₀ v₀) (k : ℕ) :
    ∃ C v₁ : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R], ∀ v, v₁ ≤ v → ∀ α,
        5 ≤ α → lg v ^ (C * α) ≤ v →
      ∀ (K : KT R) (B : ℕ) (D : Tree),
      IsAccT θ (16 * h) v (v ^ (16 * h - 16)) K B D → K.nds ≤ v ^ (h * α) → D.size ≤ v ^ (h * α) →
      B ≤ (α * lg v) ^ k → K.ht ≤ (α * lg v) ^ k →
      ∃ D', IsAccT θ (16 * h) (v ^ α) ((v ^ α) ^ (16 * h - 17)) K (B + 51 * h * α ^ 2 * lg v) D' ∧
        D'.size ≤ (v ^ α) ^ (4 * h) := by
  refine ⟨2 * C₀ + 6 * (k + 3) + 4, v₀ + cst + 2 ^ (1000 + 100 * h) + 4,
      fun R _ _ v hv α hα hl K B D hD hK hDs hB hht => ?_⟩
  have hp := Nat.one_le_two_pow (n := 1000 + 100 * h)
  have hl2 : 1000 + 100 * h + 1 ≤ lg v := le_lg_of_two_pow_le (by omega)
  obtain ⟨l, hll⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  rw [← hll] at hl hB hht hl2 ⊢
  have pw : ∀ m, m ≤ (2 * C₀ + 6 * (k + 3) + 4) * α → l ^ m ≤ v := fun m hm =>
    (Nat.pow_le_pow_right (by omega) hm).trans hl
  have hC : CutAt θ (16 * h) v (2 * α) := hcut _ (by omega) _ (by
    rw [← hll]
    refine pw _ ?_
    calc C₀ * (2 * α) = (2 * C₀) * α := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega))
  obtain ⟨J, hJ⟩ : ∃ J, J = (16 * h * α + 1) * l := ⟨_, rfl⟩
  have hJ2 : v ^ (16 * h * α + 1) < 2 ^ J := by
    rw [hJ, pow_mul' 2]
    exact Nat.pow_lt_pow_left (hll ▸ lt_two_pow_lg v) (Nat.succ_ne_zero _)
  have hJb : (3 * α) * J ≤ 51 * h * α ^ 2 * l := by
    rw [hJ, ← mul_assoc]
    refine Nat.mul_le_mul_right _ ?_
    calc (3 * α) * (16 * h * α + 1) ≤ (3 * α) * (17 * h * α) := Nat.mul_le_mul le_rfl (by nlinarith)
      _ = 51 * h * α ^ 2 := by ring
  have hX : 1000 * (B + (3 * α + 1) * (J + 1) + K.ht + 10) ^ 3 ≤ v := by
    have ha : α * l ≤ l ^ (α + 1) := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right _
          ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) α))
    have h1 : (α * l) ^ k ≤ (α * l) ^ (k + 3) :=
        Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega)) (by omega)
    have h2 : (3 * α + 1) * (J + 1) ≤ 72 * h * (α * l) ^ (k + 3) := by
      refine le_trans ?_
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega))
        (show 2 ≤ k + 3 by omega)))
      rw [hJ]
      calc (3 * α + 1) * ((16 * h * α + 1) * l + 1) ≤ (4 * α) * (18 * h * α * l) := by
            refine Nat.mul_le_mul (by omega) ?_
            have h5 : 1 ≤ h * α * l := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
            have h6 : l ≤ h * α * l := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
            have h7 : (16 * h * α + 1) * l = 16 * (h * α * l) + l := by ring
            have h8 : 18 * h * α * l = 18 * (h * α * l) := by ring
            omega
        _ = 72 * h * (α ^ 2 * l) := by ring
        _ ≤ 72 * h * (α * l) ^ 2 := Nat.mul_le_mul_left _ (by
            rw [mul_pow]
            exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) l))
    have h3 : 1 ≤ (α * l) ^ (k + 3) := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    have h4 : B + (3 * α + 1) * (J + 1) + K.ht + 10 ≤ l * (α * l) ^ (k + 3) := by
      calc _ ≤ (12 + 72 * h) * (α * l) ^ (k + 3) := by
            refine le_trans (add_le_add (add_le_add (add_le_add (hB.trans h1) h2) (hht.trans h1))
              (Nat.mul_le_mul_left 10 h3)) (le_of_eq ?_)
            ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    calc 1000 * (B + (3 * α + 1) * (J + 1) + K.ht + 10) ^ 3 ≤ l * (l * (α * l) ^ (k + 3)) ^ 3 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h4 3)
      _ ≤ l * (l * (l ^ (α + 1)) ^ (k + 3)) ^ 3 := by gcongr
      _ = l ^ (4 + 3 * ((α + 1) * (k + 3))) := by ring
      _ ≤ v := pw _ (by nlinarith)
  have hcst : cst ≤ v := by omega
  set X := B + (3 * α + 1) * (J + 1) + K.ht + 10 with hXdef
  have hX10 : 10 ≤ X := by omega
  have hX' : X ≤ v := by
    have : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
    omega
  have ⟨hu4, hUF⟩ : 2000 ≤ v ∧ UF.code.size ≤ v := by
    obtain ⟨_, _, rfl, -, h⟩ := cst_bounds hcst
    omega
  have hu1 : 1 ≤ v := by omega
  have pu : ∀ a, v ^ (a + 1) = v * v ^ a := pow_succ' v
  have pbig : ∀ a, 2000 * v ^ a ≤ v ^ (a + 1) := fun a =>
    (Nat.mul_le_mul_right _ hu4).trans_eq (pow_succ' v a).symm
  have hαX : 3 * α + 1 ≤ X := by
    have : (3 * α + 1) * 1 ≤ (3 * α + 1) * (J + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hh1 : 5 * h ≤ h * α := by rw [Nat.mul_comm h α]; exact Nat.mul_le_mul_right _ hα
  have hαh : 17 * α ≤ h * α := Nat.mul_le_mul_right _ hh
  have hα32 : α * (16 * h - 32) = 16 * (h * α) - 32 * α := by
    rw [Nat.mul_sub]
    congr 1
    · ring
    · ring
  have hα16 : α * (16 * h - 17) = 16 * (h * α) - 17 * α := by
    rw [Nat.mul_sub]
    congr 1
    · ring
    · ring
  have e16 : 16 * h * α = 16 * (h * α) := by ring
  have e4 : 4 * h * α = 4 * (h * α) := by ring
  have e17 : 16 * h * (2 * α) = 32 * (h * α) := by ring
  -- sizes stay small
  have hsize : ∀ n ≤ 3 * α, v + n * (v ^ (h * α + 2) + v ^ (16 * h + 1)) ≤ v ^ (4 * h * α) := by
    intro n hn
    obtain ⟨a, ha⟩ : ∃ a, 4 * h * α = a + 1 := ⟨4 * h * α - 1, by omega⟩
    have t1 : n * (v ^ (h * α + 2) + v ^ (16 * h + 1)) ≤ v * (v ^ (h * α + 2) + v ^ (16 * h + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have t2 : v * (v ^ (h * α + 2) + v ^ (16 * h + 1)) = v ^ (h * α + 3) + v ^ (16 * h + 2) := by
      rw [mul_add, ← pu, ← pu]
    have t3 : v ^ (h * α + 3) ≤ v ^ a := Nat.pow_le_pow_right hu1 (by omega)
    have t4 : v ^ (16 * h + 2) ≤ v ^ a := Nat.pow_le_pow_right hu1 (by omega)
    have t5 : v ^ 1 ≤ v ^ a := Nat.pow_le_pow_right hu1 (by omega)
    have t6 := pbig a
    rw [pow_one] at t5
    rw [ha]
    omega
  -- the rounds
  have rounds : ∀ n ≤ 3 * α, ∃ p,
      IsPre θ (16 * h) (v ^ α) (v ^ (16 * h * α + 1 - 8 * n)) K (B + n * J) p ∧
      p.size ≤ v + n * (v ^ (h * α + 2) + v ^ (16 * h + 1)) ∧
      (1 ≤ n → IsAccT θ (16 * h) (v ^ α) (v ^ (16 * h * α + 1 - 8 * n)) K (B + n * J) p) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨UF.code, (UF_pre θ (16 * h) (v ^ α) K (B + 0 * J)).mono ?_ le_rfl, ?_,
          fun h => absurd h (by norm_num)⟩
      · rw [← pow_mul, Nat.mul_comm α (16 * h), Nat.mul_zero, Nat.sub_zero]
        have := pbig (16 * h * α)
        have : 1 ≤ v ^ (16 * h * α) := Nat.one_le_pow _ _ (by omega)
        omega
      · rw [Nat.zero_mul, Nat.add_zero]
        exact hUF
    | succ n ih =>
      intro hn
      obtain ⟨p, hp, hps, -⟩ := ih (by omega)
      have hnJ : n * J ≤ 3 * α * J := Nat.mul_le_mul_right _ (by omega)
      have e1 : (3 * α + 1) * (J + 1) = 3 * α * J + J + 3 * α + 1 := by ring
      have e2 : (n + 1) * J = n * J + J := by ring
      obtain ⟨p', hp', hps'⟩ := prop_next_round hh hα hC hcst hD hK hDs (p := p) (B := B + n * J)
          (J := J) (X := X)
        (e := 16 * h * α + 1 - 8 * (n + 1)) (by
          rw [show 16 * h * α + 1 - 8 * (n + 1) + 8 = 16 * h * α + 1 - 8 * n by omega]
          exact hp) (hps.trans (hsize n (by omega)))
              (lt_of_le_of_lt (Nat.pow_le_pow_right hu1 (by omega)) hJ2) (by omega) hX10
        hX (by omega) (by omega)
      have hB : max (B + n * J + J) B ≤ B + (n + 1) * J := by
        rw [e2]
        omega
      refine ⟨p', (hp'.mono le_rfl hB).pre, ?_, fun _ => hp'.mono le_rfl hB⟩
      have e3 : (n + 1) * (v ^ (h * α + 2) + v ^ (16 * h + 1)) = n *
          (v ^ (h * α + 2) + v ^ (16 * h + 1)) +
          (v ^ (h * α + 2) + v ^ (16 * h + 1)) := by ring
      omega
  obtain ⟨p, -, hps, hp⟩ := rounds (3 * α) le_rfl
  refine ⟨p, (hp (by omega)).mono ?_ (Nat.add_le_add_left hJb B), ?_⟩
  · rw [← pow_mul]
    exact Nat.pow_le_pow_right hu1 (by omega)
  · rw [← pow_mul, show α * (4 * h) = 4 * h * α by ring]
    exact hps.trans (hsize _ le_rfl)

end Cslib.Circuits.Arithmetic.Separation.Interpreter
