/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundBase
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundEnt
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PathsAux

/-!
# The value of the formula (§6.2)

The meaning `Setup.mean` of the states is locally sound (`AGen.Sound`) on the reachable states
(`Setup.Inv`), with a rank `Setup.rank` decreasing along children; so the unfolded tree from the
root has value `Z(G) mod 2^P` (`Setup.formula_value`).

* `Setup.PathOK`: a path of valid choice codes. Along it the clique has `2^(2^(e - length))`
  nodes (`q_path`) and potential at most that of the first clique (`potential_path`, by
  Lemma 6.1).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset MergeProof

/-! ### Potentials along the chain -/

theorem Clique.potential_recast (C : Clique) (n : ℕ) (h : C.q = n) :
    (C.recast n h).potential = C.potential := by
  obtain ⟨q, a, T⟩ := C
  simp only at h
  subst h
  rfl

theorem mem_choices_grade {g : ℕ} {a : Fin (g * g) → Fin (g * g) → ℕ} {ι : Rect g → ℤ × ℤ}
    (h : ι ∈ choices a) (r : Rect g) : Even (ι r).1 ∧ |(ι r).1| ≤ 2 * diagWt a r := by
  simp only [choices, Fintype.mem_piFinset, mem_product, mem_filter, mem_Icc] at h
  obtain ⟨⟨⟨h1, h2⟩, he⟩, -⟩ := h r
  exact ⟨he, abs_le.mpr ⟨h1, h2⟩⟩

theorem mergeStep_q {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) : (mergeStep g a T ι).q =
        g := by
  unfold mergeStep; split_ifs <;> rfl

theorem potential_mergeStep {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (hι : ι ∈ choices a) :
    (mergeStep g a T ι).potential ≤ (⟨g * g, a, T⟩ : Clique).potential := by
  have hk := fun r => mem_choices_grade hι r
  have E := energy_le a (fun r => (ι r).1) hk
  unfold mergeStep
  split_ifs
  · show (g - 1) ^ 2 * ∑ p : Pairs g, rowBudget a (fun r => (ι r).1) p.1.1 p.1.2 ≤
      (g * g - 1) ^ 2 * ∑ p : Pairs (g * g), a p.1.1 p.1.2
    refine le_trans ?_ E
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · show (g - 1) ^ 2 * ∑ p : Pairs g, (colChild g a T ι).a p.1.1 p.1.2 ≤
      (g * g - 1) ^ 2 * ∑ p : Pairs (g * g), a p.1.1 p.1.2
    rw [sum_congr rfl fun p _ => colChild_a a T ι (fun r => (hk r).1) (le_of_lt p.2)]
    refine le_trans ?_ E
    exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

theorem potential_childAt (fw : ℕ) (C : Clique) (i : ℕ)
    (h : C.q = Nat.sqrt C.q * Nat.sqrt C.q) (hv : ValidChoiceCode (C.recast _ h).a fw i) :
    (childAt fw C i).potential ≤ C.potential := by
  have e : childAt fw C i = mergeStep (Nat.sqrt C.q) (C.recast _ h).a (C.recast _ h).T
      (decodeChoice (Nat.sqrt C.q) fw i) := by
    simp only [childAt, dif_pos h]
  rw [e]
  calc _ ≤ (⟨_, (C.recast _ h).a, (C.recast _ h).T⟩ : Clique).potential := potential_mergeStep _ _ _ hv.1
    _ = (C.recast _ h).potential := rfl
    _ = C.potential := Clique.potential_recast C _ h

theorem diag_le_sum {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ) (r : Rect g) :
    diagWt a r ≤ ∑ p : Pairs (g * g), a p.1.1 p.1.2 := by
  classical
  let p1 : Pairs (g * g) := ⟨(node r.1.1.1 r.1.2.1, node r.1.1.2 r.1.2.2), node_lt_node r.2.1 _ _⟩
  let p2 : Pairs (g * g) := ⟨(node r.1.1.1 r.1.2.2, node r.1.1.2 r.1.2.1), node_lt_node r.2.1 _ _⟩
  have hne : p1 ≠ p2 := by
    intro e
    have := congrArg (fun p : Pairs (g * g) => p.1.1) e
    simp only [p1, p2, node_inj] at this
    exact absurd this.2 r.2.2.ne
  have := Finset.sum_le_sum_of_subset (f := fun p : Pairs (g * g) => a p.1.1 p.1.2)
    (subset_univ ({p1, p2} : Finset (Pairs (g * g))))
  rw [sum_pair hne] at this
  exact this

theorem diagWt_le_potential (C : Clique) {g : ℕ} (h : C.q = g * g) (r : Rect g) :
    diagWt (C.recast _ h).a r ≤ C.potential := by
  rw [← Clique.potential_recast C _ h]
  have hg : 2 ≤ g := by have := r.2.1; have := r.1.1.2.isLt; rw [Fin.lt_def] at *; omega
  have h4 : 4 ≤ g * g := by nlinarith
  have h1 : 1 ≤ (g * g - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc diagWt (C.recast _ h).a r ≤ ∑ p : Pairs (g * g), (C.recast _ h).a p.1.1 p.1.2 := diag_le_sum _ r
    _ ≤ (g * g - 1) ^ 2 * ∑ p : Pairs (g * g), (C.recast _ h).a p.1.1 p.1.2 :=
        Nat.le_mul_of_pos_left _ h1
    _ = (C.recast _ h).potential := rfl

theorem sqrt_two_pow (k : ℕ) : Nat.sqrt (2 ^ 2 ^ (k + 1)) = 2 ^ 2 ^ k := by
  rw [pow_succ, pow_mul, sq]
  exact Nat.sqrt_eq _

namespace Setup

variable (S : Setup)

/-- A path of valid choice codes (latest first). -/
def PathOK (S : Setup) : List ℕ → Prop
  | [] => True
  | i :: rest => PathOK S rest ∧ 4 ≤ (S.clique rest).q ∧
      ∃ h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q,
        ValidChoiceCode ((S.clique rest).recast _ h).a S.fw i

theorem clique_cons (rest : List ℕ) (i : ℕ)
    (h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q) :
    S.clique (i :: rest) = mergeStep (Nat.sqrt (S.clique rest).q) ((S.clique rest).recast _ h).a
      ((S.clique rest).recast _ h).T (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i) := by
  show childAt S.fw (S.clique rest) i = _
  simp only [childAt, dif_pos h]

theorem clique_nil : S.clique [] = S.C₀ := rfl

theorem q_path {e₀ : ℕ} (h₀ : 2 * S.K = 2 ^ 2 ^ e₀) :
    ∀ chs, S.PathOK chs → (S.clique chs).q = 2 ^ 2 ^ (e₀ - chs.length) ∧ chs.length ≤ e₀
  | [], _ => ⟨by simp [clique_nil, C₀, firstClique, h₀], by simp⟩
  | i :: rest, ⟨hp, h4, h, _⟩ => by
    obtain ⟨hq, hl⟩ := q_path h₀ rest hp
    have hpos : 1 ≤ e₀ - rest.length := by
      by_contra hc
      rw [show e₀ - rest.length = 0 by omega] at hq
      rw [hq] at h4; norm_num at h4
    have hq' : (S.clique (i :: rest)).q = Nat.sqrt (S.clique rest).q :=
      (congrArg Clique.q (clique_cons S rest i h)).trans (mergeStep_q _ _ _)
    rw [hq', hq,
      show e₀ - rest.length = (e₀ - (i :: rest).length) + 1 by simp; omega, sqrt_two_pow]
    exact ⟨rfl, by simp; omega⟩

theorem potential_path : ∀ chs, S.PathOK chs → (S.clique chs).potential ≤ S.C₀.potential
  | [], _ => le_rfl
  | _ :: rest, ⟨hp, _, h, hv⟩ => (potential_childAt _ _ _ h hv).trans (potential_path rest hp)

/-- The field width holds every grade and split at every clique of a path. -/
theorem hfw_path (hS : S.Good) (chs : List ℕ) (hp : S.PathOK chs)
    (h : (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q) :
    ∀ r : Rect (Nat.sqrt (S.clique chs).q),
      6 * diagWt ((S.clique chs).recast _ h).a r < 2 ^ (S.fw - 1) := by
  intro r
  have h1 := diagWt_le_potential (S.clique chs) h r
  have h2 := S.potential_path chs hp
  have h3 := hS.2.2
  omega

theorem one_le_fw (hS : S.Good) : 1 ≤ S.fw := by
  have h3 := hS.2.2
  by_contra hc
  rw [show S.fw - 1 = 0 by omega, pow_zero] at h3
  omega

/-! ### The invariant and the rank -/

/-- The reachable states. -/
def Inv (S : Setup) (D : ℕ) : St → Prop
  | .zero => True
  | .lit _ => True
  | .cl chs => S.PathOK chs ∧ (S.clique chs).q = 2 ^ 2 ^ (D - chs.length) ∧ chs.length ≤ D
  | .last chs _ => S.PathOK chs ∧ (S.clique chs).q = 2
  | .ent chs v _ => S.PathOK chs ∧ v < (S.clique chs).q
  | .rng [] _ _ _ _ _ => False
  | .rng (i :: rest) v _ _ lo hi => S.PathOK (i :: rest) ∧ v < Nat.sqrt (S.clique rest).q ∧
      lo + 2 ≤ hi ∧ hi ≤ nFac (Nat.sqrt (S.clique rest).q)
  | .rng0 _ _ lo hi => lo + 2 ≤ hi
  | .tr up x y m lo hi T _ => lo ≤ hi ∧ hi ≤ (srcList up x y m).length ∧ ∀ s ∈ T, ValidPl up s.1
  | .trm up x y m lo pos hi _ T₁ T₂ _ _ _ => lo ≤ pos ∧ pos < hi ∧ hi ≤ (srcList up x y m).length ∧
      (∀ s ∈ T₁, ValidPl up s.1) ∧ ∀ s ∈ T₂, ValidPl up s.1
  | .trr up x y m pos hi _ T₂ _ _ => pos < hi ∧ hi ≤ (srcList up x y m).length ∧
      ∀ s ∈ T₂, ValidPl up s.1

/-- The rank of a factor state, given the ranks of the entries one level up. -/
def rkF (re : ℕ → ℕ → ℕ) : St → ℕ
  | .ent _ n x => re n x
  | .tr _ _ _ _ lo hi _ _ => 4 * (hi - lo) + 3
  | _ => 0

/-- The rank of an entry. -/
noncomputable def rankEnt (S : Setup) : List ℕ → ℕ → ℕ → ℕ
  | [] => fun v _ => S.nFac0 v + 1
  | i :: rest => fun v args => 2 + ∑ ξ ∈ range (2 ^ S.xiWidth rest i v),
      (nFac (Nat.sqrt (S.clique rest).q) + 1 + ∑ f ∈ range (nFac (Nat.sqrt (S.clique rest).q)),
        rkF (rankEnt S rest) (S.factorSt rest i v args ξ f))

/-- The rank of a clique state with `n` levels below it. -/
noncomputable def rankCl (S : Setup) : ℕ → List ℕ → ℕ
  | 0,
      chs => 1 + ∑ i ∈ range (2 ^ S.gen.width (.cl chs)), (rankEnt S chs 0 i + rankEnt S chs 1 i + 1)
  | n + 1, chs => 1 + ∑ i ∈ range (2 ^ S.gen.width (.cl chs)),
      (rankEnt S chs 0 i + rankEnt S chs 1 i + 1 + rankCl S n (i :: chs))

/-- **The rank.** -/
noncomputable def rank (S : Setup) (D : ℕ) : St → ℕ
  | .zero => 0
  | .lit _ => 0
  | .cl chs => rankCl S (D - chs.length) chs
  | .last chs i => rankEnt S chs 0 i + rankEnt S chs 1 i + 1
  | .ent chs v args => rankEnt S chs v args
  | .rng [] _ _ _ _ _ => 0
  | .rng (i :: rest) v args ξ lo
      hi => (hi - lo) + 1 + ∑ f ∈ range (nFac (Nat.sqrt (S.clique rest).q)),
      rkF (rankEnt S rest) (S.factorSt rest i v args ξ f)
  | .rng0 _ _ lo hi => hi - lo
  | .tr _ _ _ _ lo hi _ _ => 4 * (hi - lo) + 3
  | .trm _ _ _ _ lo _ hi _ _ _ _ _ _ => 4 * (hi - lo) + 2
  | .trr _ _ _ _ pos hi _ _ _ _ => 4 * (hi - pos) + 1

/-! ### Ranges of factors -/

theorem rangeSt_cases (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi : ℕ) :
    (hi ≤ lo ∧ rangeSt mk mkR lo hi = .lit 1) ∨ (hi = lo + 1 ∧ rangeSt mk mkR lo hi = mk lo) ∨
      (lo + 2 ≤ hi ∧ rangeSt mk mkR lo hi = mkR lo hi) := by
  unfold rangeSt
  by_cases h1 : hi ≤ lo
  · exact Or.inl ⟨h1, if_pos h1⟩
  · rw [if_neg h1]
    by_cases h2 : hi = lo + 1
    · exact Or.inr (Or.inl ⟨h2, if_pos h2⟩)
    · exact Or.inr (Or.inr ⟨by omega, if_neg h2⟩)

theorem mean_rangeSt (mk : ℕ → St) (mkR : ℕ → ℕ → St) (F : ℕ → ℤ) (hmk : ∀ f, S.mean (mk f) = F f)
    (hR : ∀ a b, S.mean (mkR a b) = ∏ f ∈ Ico a b, F f) {lo hi : ℕ} (h : lo ≤ hi) :
    S.mean (rangeSt mk mkR lo hi) = ∏ f ∈ Ico lo hi, F f := by
  rcases rangeSt_cases mk mkR lo hi with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨_, e⟩
  · rw [e, show hi = lo by omega, Ico_self, prod_empty]; rfl
  · rw [e, h1, Nat.Ico_succ_singleton, prod_singleton, hmk]
  · rw [e, hR]

/-- The halves of a range. -/
theorem prod_halves (F : ℕ → ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    ∏ f ∈ Ico lo hi, F f = (∏ f ∈ Ico lo ((lo + hi) / 2), F f) * ∏ f ∈ Ico ((lo + hi) / 2) hi, F
        f :=
  (prod_Ico_consecutive F (by omega) (by omega)).symm

/-! ### Factor states -/

section Factors

variable (rest : List ℕ) (i v args ξ f : ℕ)
  (h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q)
include h

theorem factorSt_shape :
    S.factorSt rest i v args ξ f = .zero ∨ (∃ w, S.factorSt rest i v args ξ f = .lit w) ∨
      (∃ row x, f < Nat.sqrt (S.clique rest).q ∧
        S.factorSt rest i v args ξ f = .ent rest (holders (Nat.sqrt (S.clique rest).q) v row f) x) ∨
      ∃ up x y m e, S.factorSt rest i v args ξ f =
        .tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) e := by
  rw [S.factorSt_eq rest i v args ξ f h]
  rcases factorG_shape rest _ _ _ _ _ _ v args ξ f with e | ⟨w, e⟩ | ⟨hf, e⟩ | ⟨up, x, y, m, c, e⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨w, e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, hf, e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨up, x, y, m, c, e⟩))

theorem mean_factorSt : S.mean (S.factorSt rest i v args ξ f) = S.meanBase
    (S.factorSt rest i v args ξ f) := by
  rcases S.factorSt_shape rest i v args ξ f
      h with e | ⟨w, e⟩ | ⟨row, x, -, e⟩ | ⟨up, x, y, m, c, e⟩ <;>
    rw [e] <;> rfl

theorem meanBase_factorSt : S.meanBase (S.factorSt rest i v args ξ f) =
    fval (S.clique rest) (S.factorSt rest i v args ξ f) := by
  rcases S.factorSt_shape rest i v args ξ f
      h with e | ⟨w, e⟩ | ⟨row, x, -, e⟩ | ⟨up, x, y, m, c, e⟩ <;>
    rw [e] <;> rfl

theorem rank_factorSt (D : ℕ) : S.rank D (S.factorSt rest i v args ξ f) =
    rkF (rankEnt S rest) (S.factorSt rest i v args ξ f) := by
  rcases S.factorSt_shape rest i v args ξ f
      h with e | ⟨w, e⟩ | ⟨row, x, -, e⟩ | ⟨up, x, y, m, c, e⟩ <;>
    rw [e] <;> rfl

theorem inv_factorSt (D : ℕ) (hp : S.PathOK rest) (hv : v < Nat.sqrt (S.clique rest).q) :
    S.Inv D (S.factorSt rest i v args ξ f) := by
  rcases S.factorSt_shape rest i v args ξ f
      h with e | ⟨w, e⟩ | ⟨row, x, hf, e⟩ | ⟨up, x, y, m, c, e⟩ <;>
    rw [e]
  · trivial
  · trivial
  · refine ⟨hp, ?_⟩
    have := holders_lt hv row hf
    rw [← h] at this
    exact this
  · exact ⟨Nat.zero_le _, le_rfl, tgtMs_valid up x y m⟩

end Factors

/-! ### Clique states -/

theorem two_pow_cases (k : ℕ) : 2 ^ 2 ^ k = 2 ∨
    (4 ≤ 2 ^ 2 ^ k ∧ 2 ^ 2 ^ k = Nat.sqrt (2 ^ 2 ^ k) * Nat.sqrt (2 ^ 2 ^ k)) := by
  rcases k with _ | k
  · left; norm_num
  · right
    rw [sqrt_two_pow]
    refine ⟨?_, by rw [pow_succ, pow_mul, sq]⟩
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num)
          (by rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega)

theorem mean_cl (chs : List ℕ) (hc : (S.clique chs).q = 2 ∨ (4 ≤ (S.clique chs).q ∧
    (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q)) :
    S.mean (.cl chs) = (S.clique chs).value := by
  show (if _ then _ else _) = _
  rw [if_pos hc]

theorem rankCl_gt_last (k : ℕ) (chs : List ℕ) (i : ℕ) (hi : i < 2 ^ S.gen.width (.cl chs)) :
    rankEnt S chs 0 i + rankEnt S chs 1 i + 1 < rankCl S k chs := by
  rcases k with _ | k
  · have := Finset.single_le_sum (f := fun i => rankEnt S chs 0 i + rankEnt S chs 1 i + 1)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
    simp only [rankCl]; omega
  · have := Finset.single_le_sum
      (f := fun i => rankEnt S chs 0 i + rankEnt S chs 1 i + 1 + rankCl S k (i :: chs))
      (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
    simp only [rankCl]; omega

theorem rankCl_gt_cl (k : ℕ) (chs : List ℕ) (i : ℕ) (hi : i < 2 ^ S.gen.width (.cl chs)) :
    rankCl S k (i :: chs) < rankCl S (k + 1) chs := by
  have := Finset.single_le_sum
    (f := fun i => rankEnt S chs 0 i + rankEnt S chs 1 i + 1 + rankCl S k (i :: chs))
    (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
  simp only [rankCl]; omega

open Classical in
theorem sound_cl (hS : S.Good) {D : ℕ} (hD : 2 * S.K = 2 ^ 2 ^ D) (chs : List ℕ)
    (hinv : S.Inv D (.cl chs)) :
    S.mean (.cl chs) = ∑ i ∈ range (2 ^ S.gen.width (.cl chs)), S.mean (S.gen.child (.cl chs) i) ∧
      ∀ i < 2 ^ S.gen.width (.cl chs), S.Inv D (S.gen.child (.cl chs) i) ∧
        S.rank D (S.gen.child (.cl chs) i) < S.rank D (.cl chs) := by
  obtain ⟨hp, hq, hl⟩ := hinv
  rcases two_pow_cases (D - chs.length) with h2 | ⟨h4, hsq⟩
  · have hq2 : (S.clique chs).q = 2 := hq.trans h2
    have hw : S.gen.width (.cl chs) = codeWidth ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) := by
      show (if h : _ then _ else _) = _
      rw [dif_pos hq2]
    have hch : ∀ i, S.gen.child (.cl chs) i =
        (decodeLabel ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) i).elim .zero fun l =>
          if labelWt l = (S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩ then .last chs
              i else .zero := by
      intro i
      show (if h : _ then _ else _) = _
      rw [dif_pos hq2]
      cases decodeLabel _ i <;> rfl
    refine ⟨?_, fun i hi => ?_⟩
    · rw [mean_cl S chs (Or.inl hq2), value_two _ hq2, hw]
      refine sum_congr rfl fun i _ => ?_
      rw [hch]
      rcases decodeLabel ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) i with _ | l
      · rfl
      · simp only [Option.elim]
        split_ifs <;> rfl
    · rw [hch]
      rcases decodeLabel ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) i with _ | l
      · exact
          ⟨trivial, by show 0 < rankCl S (D - chs.length) chs; have := rankCl_gt_last S (D - chs.length) chs i hi; omega⟩
      · simp only [Option.elim]
        split_ifs
        · exact ⟨⟨hp, hq2⟩, rankCl_gt_last S (D - chs.length) chs i hi⟩
        · exact
            ⟨trivial, by show 0 < rankCl S (D - chs.length) chs; have := rankCl_gt_last S (D - chs.length) chs i hi; omega⟩
  · rw [← hq] at h4 hsq
    have hq2 : (S.clique chs).q ≠ 2 := by omega
    have hk : 1 ≤ D - chs.length := by
      by_contra hc
      rw [show D - chs.length = 0 by omega] at hq
      omega
    have hw : S.gen.width (.cl chs) = choiceWidth (Nat.sqrt (S.clique chs).q) S.fw := by
      show (if h : _ then _ else _) = _
      rw [dif_neg hq2]
    have hch : ∀ i, S.gen.child (.cl chs) i =
        if ValidChoiceCode ((S.clique chs).recast _ hsq).a S.fw i then .cl
            (i :: chs) else .zero := by
      intro i
      show (if h : _ then _ else _) = _
      rw [dif_neg hq2, dif_pos hsq]
    have hpath : ∀ i, ValidChoiceCode ((S.clique chs).recast _ hsq).a S.fw i → S.PathOK
        (i :: chs) :=
      fun i hv => ⟨hp, h4, hsq, hv⟩
    refine ⟨?_, fun i hi => ?_⟩
    · rw [mean_cl S chs (Or.inr ⟨h4, hsq⟩),
        value_childAt S.fw (S.clique chs) (Nat.le_sqrt.mpr (by omega)) hsq (S.one_le_fw hS)
          (S.hfw_path hS chs hp hsq), hw]
      refine sum_congr rfl fun i _ => ?_
      rw [hch]
      split_ifs with hv
      · obtain ⟨hq', -⟩ := S.q_path hD (i :: chs) (hpath i hv)
        rw [mean_cl S (i :: chs) (by rw [hq']; exact two_pow_cases _)]
        rfl
      · rfl
    · rw [hch]
      split_ifs with hv
      · obtain ⟨hq', hl'⟩ := S.q_path hD (i :: chs) (hpath i hv)
        refine ⟨⟨hpath i hv, hq', hl'⟩, ?_⟩
        show rankCl S (D - (i :: chs).length) (i :: chs) < rankCl S (D - chs.length) chs
        rw [show D - chs.length = (D - (i :: chs).length) + 1 by simp; omega]
        exact rankCl_gt_cl S _ chs i hi
      · exact
          ⟨trivial, by show 0 < rankCl S (D - chs.length) chs; have := rankCl_gt_last S (D - chs.length) chs i hi; omega⟩

/-! ### Product states -/

/-- The conclusion of local soundness at a product state. -/
def ProdOK (D : ℕ) (st : St) : Prop :=
  S.mean st = S.mean (S.gen.child st 0) * S.mean (S.gen.child st 1) ∧
    S.Inv D (S.gen.child st 0) ∧ S.Inv D (S.gen.child st 1) ∧
    S.rank D (S.gen.child st 0) < S.rank D st ∧ S.rank D (S.gen.child st 1) < S.rank D st

theorem inv_rangeSt (D : ℕ) (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi : ℕ)
    (hmk : ∀ f, lo ≤ f → f < hi → S.Inv D (mk f)) (hR : lo + 2 ≤ hi → S.Inv D (mkR lo hi)) :
    S.Inv D (rangeSt mk mkR lo hi) := by
  rcases rangeSt_cases mk mkR lo hi with ⟨_, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ <;> rw [e]
  · trivial
  · exact hmk lo le_rfl (by omega)
  · exact hR h1

theorem rank_rangeSt_lt (D : ℕ) (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi R : ℕ) (h0 : 0 < R)
    (hmk : hi = lo + 1 → S.rank D (mk lo) < R) (hR : lo + 2 ≤ hi → S.rank D (mkR lo hi) < R) :
    S.rank D (rangeSt mk mkR lo hi) < R := by
  rcases rangeSt_cases mk mkR lo hi with ⟨_, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ <;> rw [e]
  · exact h0
  · exact hmk h1
  · exact hR h1

theorem sound_last (D : ℕ) (chs : List ℕ) (i : ℕ) (hinv : S.Inv D (.last chs i)) :
    S.ProdOK D (.last chs i) := by
  obtain ⟨hp, hq⟩ := hinv
  refine ⟨rfl, ⟨hp, by omega⟩, ⟨hp, by omega⟩, ?_, ?_⟩
  · show rankEnt S chs 0 i < rankEnt S chs 0 i + rankEnt S chs 1 i + 1; omega
  · show rankEnt S chs 1 i < rankEnt S chs 0 i + rankEnt S chs 1 i + 1; omega

theorem mean_rangeSt0 (v args lo hi : ℕ) (h : lo ≤ hi) :
    S.mean (rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo hi) =
      ∏ f ∈ Ico lo hi, S.factor0 v args f :=
  S.mean_rangeSt _ _ _ (fun _ => rfl) (fun _ _ => rfl) h

theorem rank_rangeSt0 (D v args lo hi : ℕ) (R : ℕ) (h0 : hi - lo < R) :
    S.rank D (rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo hi) < R :=
  S.rank_rangeSt_lt D _ _ lo hi R (by omega) (fun _ => by show 0 < R; omega)
    (fun _ => by show hi - lo < R; exact h0)

theorem inv_rangeSt0 (D v args lo hi : ℕ) :
    S.Inv D (rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo hi) :=
  S.inv_rangeSt D _ _ lo hi (fun _ _ _ => trivial) (fun h => h)

theorem sound_ent0 (D v args : ℕ) (hinv : S.Inv D (.ent [] v args)) : S.ProdOK D
    (.ent [] v args) := by
  have hv : v < 2 * S.K := hinv.2
  have c0 : S.gen.child (.ent [] v args) 0 =
      rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) 0 (S.nFac0 v / 2) := rfl
  have c1 : S.gen.child (.ent [] v args) 1 =
      rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) (S.nFac0 v / 2) (S.nFac0 v) := rfl
  have hr : S.rank D (.ent [] v args) = S.nFac0 v + 1 := rfl
  rw [ProdOK, c0, c1, hr]
  refine ⟨?_, S.inv_rangeSt0 D v args _ _, S.inv_rangeSt0 D v args _ _,
    S.rank_rangeSt0 D v args _ _ _ (by omega), S.rank_rangeSt0 D v args _ _ _ (by omega)⟩
  show cEntry S.C₀ v args = _
  rw [S.ent0 v args hv, S.mean_rangeSt0 v args _ _ (Nat.zero_le _),
    S.mean_rangeSt0 v args _ _ (Nat.div_le_self _ _),
    prod_Ico_consecutive _ (Nat.zero_le _) (Nat.div_le_self _ _), range_eq_Ico]

theorem sound_rng0 (D v args lo hi : ℕ) (hinv : S.Inv D (.rng0 v args lo hi)) :
    S.ProdOK D (.rng0 v args lo hi) := by
  have h2 : lo + 2 ≤ hi := hinv
  have c0 : S.gen.child (.rng0 v args lo hi) 0 =
      rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo ((lo + hi) / 2) := rfl
  have c1 : S.gen.child (.rng0 v args lo hi) 1 =
      rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) ((lo + hi) / 2) hi := rfl
  have hr : S.rank D (.rng0 v args lo hi) = hi - lo := rfl
  rw [ProdOK, c0, c1, hr]
  refine ⟨?_, S.inv_rangeSt0 D v args _ _, S.inv_rangeSt0 D v args _ _,
    S.rank_rangeSt0 D v args _ _ _ (by omega), S.rank_rangeSt0 D v args _ _ _ (by omega)⟩
  show ∏ f ∈ Ico lo hi, S.factor0 v args f = _
  rw [S.mean_rangeSt0 v args _ _ (by omega), S.mean_rangeSt0 v args _ _ (by omega),
    prod_halves _ (by omega)]

theorem sound_rng (D : ℕ) (i : ℕ) (rest : List ℕ) (v args ξ lo hi : ℕ)
    (hinv : S.Inv D (.rng (i :: rest) v args ξ lo hi)) : S.ProdOK D
        (.rng (i :: rest) v args ξ lo hi) := by
  obtain ⟨hp, hv, h2, hle⟩ := hinv
  have hp' : S.PathOK rest := hp.1
  have h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q := hp.2.2.1
  have c0 : S.gen.child (.rng (i :: rest) v args ξ lo hi) 0 =
      rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) lo ((lo + hi) / 2) := rfl
  have c1 : S.gen.child (.rng (i :: rest) v args ξ lo hi) 1 =
      rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) ((lo + hi) / 2) hi := rfl
  have hr : ∀ a b, S.rank D (.rng (i :: rest) v args ξ a b) = (b - a) + 1 +
      ∑ f ∈ range (nFac (Nat.sqrt (S.clique rest).q)),
        rkF (rankEnt S rest) (S.factorSt rest i v args ξ f) := fun _ _ => rfl
  have hm : ∀ a b, a ≤ b → S.mean (rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ)
      a b) =
      ∏ f ∈ Ico a b, S.meanBase (S.factorSt rest i v args ξ f) := fun a b hab =>
    S.mean_rangeSt _ _ _ (fun f => S.mean_factorSt rest i v args ξ f h) (fun _ _ => rfl) hab
  have hinvR : ∀ a b, b ≤ hi →
      S.Inv D (rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) a b) :=
    fun a b hb => S.inv_rangeSt D _ _ a b
      (fun f _ _ => S.inv_factorSt rest i v args ξ f h D hp' hv)
      (fun hab => ⟨hp, hv, hab, by omega⟩)
  have hrk : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → (a, b) ≠ (lo, hi) →
      S.rank D (rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) a b) <
        S.rank D (.rng (i :: rest) v args ξ lo hi) := by
    intro a b hla hab hb hne
    rw [hr]
    refine S.rank_rangeSt_lt D _ _ a b _ (by omega) (fun hb' => ?_) (fun hab' => ?_)
    · rw [S.rank_factorSt rest i v args ξ a h D]
      have := Finset.single_le_sum
          (f := fun f => rkF (rankEnt S rest) (S.factorSt rest i v args ξ f))
        (fun _ _ => Nat.zero_le _) (mem_range.mpr
            (show a < nFac (Nat.sqrt (S.clique rest).q) by omega))
      omega
    · rw [hr]
      have : b - a < hi - lo := by
        by_contra hc
        exact hne (Prod.ext (by simp; omega) (by simp; omega))
      omega
  rw [ProdOK, c0, c1]
  refine ⟨?_, hinvR _ _ (by omega), hinvR _ _ le_rfl, hrk _ _ le_rfl (by omega) (by omega) ?_,
    hrk _ _ (by omega) (by omega) le_rfl ?_⟩
  · show ∏ f ∈ Ico lo hi, S.meanBase (S.factorSt rest i v args ξ f) = _
    rw [hm _ _ (by omega), hm _ _ (by omega), prod_halves _ (by omega)]
  · intro e; simp at e; omega
  · intro e; simp at e; omega

theorem sound_trm (D : ℕ) (up : Bool) (x y m : Label) (lo pos hi : ℕ) (t : HPlace × ℕ)
    (T₁ T₂ : Multiset (HPlace × ℕ)) (c₁ c₀ c₂ : ℤ)
    (hinv : S.Inv D (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂)) :
    S.ProdOK D (.trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  refine ⟨rfl, ⟨h1, by omega, h4⟩, ⟨h2, h3, h5⟩, ?_, ?_⟩
  · show 4 * (pos - lo) + 3 < 4 * (hi - lo) + 2; omega
  · show 4 * (hi - pos) + 1 < 4 * (hi - lo) + 2; omega

theorem sound_trr (D : ℕ) (up : Bool) (x y m : Label) (pos hi : ℕ) (t : HPlace × ℕ)
    (T₂ : Multiset (HPlace × ℕ)) (c₀ c₂ : ℤ) (hinv : S.Inv D (.trr up x y m pos hi t T₂ c₀ c₂)) :
    S.ProdOK D (.trr up x y m pos hi t T₂ c₀ c₂) := by
  obtain ⟨h1, h2, h3⟩ := hinv
  refine ⟨rfl, trivial, ⟨by omega, h2, h3⟩, ?_, ?_⟩
  · show 0 < 4 * (hi - pos) + 1; omega
  · show 4 * (hi - (pos + 1)) + 3 < 4 * (hi - pos) + 1; omega

/-! ### Sum states -/

/-- The conclusion of local soundness at a sum state. -/
def SumOK (D : ℕ) (st : St) : Prop :=
  S.mean st = ∑ i ∈ range (2 ^ S.gen.width st), S.mean (S.gen.child st i) ∧
    ∀ i < 2 ^ S.gen.width st, S.Inv D (S.gen.child st i) ∧ S.rank D (S.gen.child st i) < S.rank D st

open Classical in
theorem sound_tr (D : ℕ) (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ)) (c : ℤ)
    (hinv : S.Inv D (.tr up x y m lo hi T c)) (hlt : lo < hi) : S.SumOK D
        (.tr up x y m lo hi T c) := by
  obtain ⟨hle, hhi, hT⟩ := hinv
  let trmOf : PivX →
      St := fun d => .trm up x y m lo (lo + d.1) hi d.2.1 d.2.2.1 (T - d.2.2.1 - {d.2.1})
    d.2.2.2.1 d.2.2.2.2 (c - d.2.2.2.1 - d.2.2.2.2)
  have hch : ∀ i, S.gen.child (.tr up x y m lo hi T c) i =
      if PivotValid up x y m lo hi T i then trmOf (decodePivot up (tWt (srcSub up x y m lo hi) T) i)
      else .zero := by
    intro i
    show (if _ then _ else _) = _
    split_ifs
    · generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d
      obtain ⟨ν, t, T₁, c₁, c₀⟩ := d
      rfl
    · rfl
  refine ⟨?_, fun i hi' => ?_⟩
  · show Setup.trMean up x y m lo hi T c = _
    rw [trMean_pivot up x y m T c hlt hhi hT]
    refine sum_congr rfl fun i _ => ?_
    rw [hch]
    split_ifs <;> rfl
  · rw [hch]
    split_ifs with hv
    · rw [pivotValid_iff] at hv
      obtain ⟨-, h1, h2, h3, -⟩ := hv
      have hl := length_srcSub up x y m hhi hle
      generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d at h1 h2 h3 ⊢
      refine
          ⟨⟨by omega, by omega, hhi, fun s hs => hT s (Multiset.mem_of_le (h3.trans tsub_le_self) hs),
        fun s hs => hT s (Multiset.mem_of_le (tsub_le_self.trans tsub_le_self) hs)⟩, ?_⟩
      show 4 * (hi - lo) + 2 < 4 * (hi - lo) + 3
      omega
    · exact ⟨trivial, by show 0 < 4 * (hi - lo) + 3; omega⟩

theorem leaf_tr (D : ℕ) (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ)) (c : ℤ)
    (hinv : S.Inv D (.tr up x y m lo hi T c)) (hlt : ¬ lo < hi) :
    S.mean (.tr up x y m lo hi T c) = S.gen.leafVal (.tr up x y m lo hi T c) := by
  obtain ⟨hle, -, -⟩ := hinv
  show Setup.trMean up x y m lo hi T c = if T = 0 ∧ c = 0 then 1 else 0
  rw [show hi = lo by omega, trMean_empty]

theorem parentGrid_eq (rest : List ℕ) (i : ℕ)
    (h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q) :
    S.parentGrid rest i = some ⟨Nat.sqrt (S.clique rest).q, ((S.clique rest).recast _ h).a,
      ((S.clique rest).recast _ h).T, decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i,
      orientRow ((S.clique rest).recast _ h).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1⟩ := by
  unfold parentGrid
  simp only [dif_pos h]

open Classical in
theorem sound_ent (D : ℕ) (i : ℕ) (rest : List ℕ) (v args : ℕ)
    (hinv : S.Inv D (.ent (i :: rest) v args)) :
    (S.gen.kind (.ent (i :: rest) v args) = .sum → S.SumOK D (.ent (i :: rest) v args)) ∧
      (S.gen.kind (.ent (i :: rest) v args) = .leaf →
        S.mean (.ent (i :: rest) v args) = S.gen.leafVal (.ent (i :: rest) v args)) := by
  obtain ⟨hp, hvq⟩ := hinv
  have hp0 := hp
  obtain ⟨hp', h4, h, hvc⟩ := hp0
  have hpg := S.parentGrid_eq rest i h
  have hqc : (S.clique (i :: rest)).q = Nat.sqrt (S.clique rest).q :=
    (congrArg Clique.q (S.clique_cons rest i h)).trans (mergeStep_q _ _ _)
  have hv : v < Nat.sqrt (S.clique rest).q := hqc ▸ hvq
  have hk : S.gen.kind (.ent (i :: rest) v args) =
      if Setup.ArgsValid (S.clique (i :: rest)) v args (packL (Nat.sqrt (S.clique rest).q))
      then .sum else .leaf := by
    simp only [Setup.gen, hpg]
  have hw : S.gen.width (.ent (i :: rest) v args) = copiesWidth (S.clique rest)
      (holders (Nat.sqrt (S.clique rest).q) v (orientRow ((S.clique rest).recast _ h).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q) := by
    simp only [Setup.gen, Setup.xiWidth, hpg]
  have hch : ∀ ξ, S.gen.child (.ent (i :: rest) v args) ξ =
      if CopiesValid (S.clique rest) (holders (Nat.sqrt (S.clique rest).q) v
        (orientRow ((S.clique rest).recast _ h).a
          fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q) ξ
      then .rng (i :: rest) v args ξ 0 (nFac (Nat.sqrt (S.clique rest).q)) else .zero := by
    intro ξ
    simp only [Setup.gen, hpg]
  have hkk : ∀ r, Even (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1 :=
    fun r => (mem_choices_grade hvc.1 r).1
  have hmean : S.mean (.ent (i :: rest) v args) =
      if Setup.ArgsValid (S.clique (i :: rest)) v args (packL (Nat.sqrt (S.clique rest).q)) then
        ∑ ξ ∈ range (2 ^ copiesWidth (S.clique rest)
          (holders (Nat.sqrt (S.clique rest).q) v (orientRow ((S.clique rest).recast _ h).a
            fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q)),
          if CopiesValid (S.clique rest) (holders (Nat.sqrt (S.clique rest).q) v
            (orientRow ((S.clique rest).recast _ h).a
              fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)) (Nat.sqrt (S.clique rest).q) ξ
          then ∏ f ∈ range (nFac (Nat.sqrt (S.clique rest).q)), S.meanBase
              (S.factorSt rest i v args ξ f)
          else 0
      else 0 := by
    show cEntry (S.clique (i :: rest)) v args = _
    have hC0 := S.clique_cons rest i h
    unfold mergeStep at hC0
    have hf : ∀ ξ f, S.meanBase (S.factorSt rest i v args ξ f) = fval (S.clique rest)
        (factorG rest (S.clique rest) (S.clique (i :: rest)) (Nat.sqrt (S.clique rest).q)
          ((S.clique rest).recast _ h).a (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i)
          (orientRow ((S.clique rest).recast _ h).a
            fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1) v args ξ f) := by
      intro ξ f
      rw [S.meanBase_factorSt rest i v args ξ f h, S.factorSt_eq rest i v args ξ f h]
    simp only [hf]
    revert hC0
    cases orientRow ((S.clique rest).recast _ h).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1 <;>
      intro hC0 <;> simp only [Bool.false_eq_true, if_false, if_true] at hC0 <;> rw [hC0]
    · exact ent_col rest (S.clique rest) h _ hkk ⟨v, hv⟩ args
    · exact ent_row rest (S.clique rest) h _ ⟨v, hv⟩ args
  constructor
  · intro hks
    rw [hk] at hks
    split_ifs at hks with hav
    refine ⟨?_, fun ξ hξ => ?_⟩
    · rw [hmean, if_pos hav, hw]
      refine sum_congr rfl fun ξ _ => ?_
      rw [hch]
      split_ifs
      · show _ = ∏ f ∈ Ico 0 _, _
        rw [range_eq_Ico]
      · rfl
    · have hξ' : ξ < 2 ^ S.xiWidth rest i v := hξ
      rw [hch]
      split_ifs
      · have hg : 1 ≤ Nat.sqrt (S.clique rest).q := by omega
        have hn : 2 ≤ nFac (Nat.sqrt (S.clique rest).q) := by unfold nFac; nlinarith
        refine ⟨⟨hp, hv, by omega, le_rfl⟩, ?_⟩
        show nFac (Nat.sqrt (S.clique rest).q) - 0 + 1 + _ < 2 + ∑ ξ ∈ range
            (2 ^ S.xiWidth rest i v), _
        have := Finset.single_le_sum (f := fun ξ => nFac (Nat.sqrt (S.clique rest).q) + 1 +
            ∑ f ∈ range (nFac (Nat.sqrt (S.clique rest).q)),
              rkF (rankEnt S rest) (S.factorSt rest i v args ξ f))
          (fun _ _ => Nat.zero_le _) (mem_range.mpr hξ')
        omega
      · exact ⟨trivial, by show 0 < 2 + _; omega⟩
  · intro hkl
    rw [hk] at hkl
    split_ifs at hkl with hav
    rw [hmean, if_neg hav]
    rfl

/-! ### Local soundness and the value -/

open Classical in
theorem gen_sound (hS : S.Good) {D : ℕ} (hD : 2 * S.K = 2 ^ 2 ^ D) :
    S.gen.Sound (S.Inv D) S.mean (S.rank D) where
  sum := by
    intro st hinv hk
    cases st with
    | cl chs => exact S.sound_cl hS hD chs hinv
    | ent chs v args =>
      cases chs with
      | nil => cases hk
      | cons i rest => exact (S.sound_ent D i rest v args hinv).1 hk
    | tr up x y m lo hi T c =>
      by_cases hlt : lo < hi
      · exact S.sound_tr D up x y m lo hi T c hinv hlt
      · have : S.gen.kind (.tr up x y m lo hi T c) = .leaf := if_neg hlt
        rw [this] at hk; cases hk
    | rng chs => cases hk
    | _ => cases hk
  prod := by
    intro st hinv hk
    cases st with
    | last chs i => exact S.sound_last D chs i hinv
    | ent chs v args =>
      cases chs with
      | nil => exact S.sound_ent0 D v args hinv
      | cons i rest =>
        obtain ⟨hp, -⟩ := hinv
        have hpg := S.parentGrid_eq rest i hp.2.2.1
        have e : S.gen.kind (.ent (i :: rest) v args) =
            if Setup.ArgsValid (S.clique (i :: rest)) v args (packL (Nat.sqrt (S.clique rest).q))
            then Kind.sum else Kind.leaf := by
          simp only [Setup.gen, hpg]
        rw [e] at hk
        split_ifs at hk
    | rng chs v args ξ lo hi =>
      cases chs with
      | nil => exact hinv.elim
      | cons i rest => exact S.sound_rng D i rest v args ξ lo hi hinv
    | rng0 v args lo hi => exact S.sound_rng0 D v args lo hi hinv
    | trm up x y m lo pos hi t T₁ T₂ c₁ c₀
        c₂ => exact S.sound_trm D up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ hinv
    | trr up x y m pos hi t T₂ c₀ c₂ => exact S.sound_trr D up x y m pos hi t T₂ c₀ c₂ hinv
    | cl chs =>
      have e : S.gen.kind (.cl chs) = (if (S.clique chs).q = 2 then .sum else
          if 4 ≤ (S.clique chs).q ∧ (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt
              (S.clique chs).q
          then .sum else .leaf) := rfl
      rw [e] at hk
      split_ifs at hk
    | tr up x y m lo hi T c =>
      have e : S.gen.kind (.tr up x y m lo hi T c) = if lo < hi then .sum else .leaf := rfl
      rw [e] at hk
      split_ifs at hk
    | _ => cases hk
  leaf := by
    intro st hinv hk
    cases st with
    | zero => rfl
    | lit w => rfl
    | cl chs =>
      have e : S.gen.kind (.cl chs) = (if (S.clique chs).q = 2 then .sum else
          if 4 ≤ (S.clique chs).q ∧ (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt
              (S.clique chs).q
          then .sum else .leaf) := rfl
      rw [e] at hk
      split_ifs at hk with h1 h2
      have hn : ¬ ((S.clique chs).q = 2 ∨ (4 ≤ (S.clique chs).q ∧
          (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q)) := by tauto
      exact if_neg hn
    | ent chs v args =>
      cases chs with
      | nil => cases hk
      | cons i rest => exact (S.sound_ent D i rest v args hinv).2 hk
    | tr up x y m lo hi T c =>
      by_cases hlt : lo < hi
      · have : S.gen.kind (.tr up x y m lo hi T c) = .sum := if_pos hlt
        rw [this] at hk; cases hk
      · exact S.leaf_tr D up x y m lo hi T c hinv hlt
    | _ => cases hk

/-- **The value of the formula** (§6.2): for a good setup and enough fuel, the unfolded tree from
the root has value `Z(G) mod 2^P`. -/
theorem formula_value (hS : S.Good) : ∃ N, ∀ n, N ≤ n →
    (S.gen.tree S.P n (.cl [])).value = AGen.res S.P S.G.value := by
  obtain ⟨hK, ⟨e, he⟩, -⟩ := id hS
  have hq0 : (S.clique []).q = 2 ^ 2 ^ e := by simp [clique_nil, C₀, firstClique, he]
  have hinv0 : S.Inv e (.cl []) := ⟨trivial, by simpa using hq0, by simp⟩
  refine ⟨S.rank e (.cl []) + 1, fun n hn => ?_⟩
  rw [AGen.tree_value _ (S.gen_sound hS he) S.P n _ hinv0 (by omega)]
  congr 1
  rw [mean_cl S [] (by rw [hq0]; exact two_pow_cases e), clique_nil]
  exact firstClique_value S.G S.K hK

end Setup

end Cslib.Complexity.NtimeDspace.Cube
