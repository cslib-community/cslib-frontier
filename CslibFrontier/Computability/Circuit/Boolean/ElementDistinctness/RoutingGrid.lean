/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.PermutationWires
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.RectangleRouting
public import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-!
# A regular graph from joint tagged-permutation tests

The lists supply horizontal and vertical shifts on a rectangle with `r` rows and `2 ^ h`
columns. Split each record address into a pair `(b,c)` with `b < r`. One list in each row
supplies all horizontal shifts. Another list for each `b` supplies the vertical shifts
by interchanging the row and `b`. This construction uses at most four layers of lists.
At each site a terminal is determined by its layer, its bit coordinate and its side of the
network, giving at most `8 * h` terminals per site. For one list the rectangle has one row.

The resulting regular graph gives a two-coordinate alternative to the random permutations in
[OpenAI2026MatrixExponentNineFourths, “Fields without ports”]. Its squared-distance inequality
holds simultaneously in every spectral metric.
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Function Finset Frontier
open scoped BigOperators

universe u

private def switch {A C : Type*} (layer : Fin 4) : Equiv.Perm (A × A × C) :=
  if layer = 1 then
    { toFun := fun (a, b, c) => (b, a, c)
      invFun := fun (a, b, c) => (b, a, c)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  else Equiv.refl _

private def layers {t r : ℕ} (upper : t ≤ 4 * r) : Fin t ↪ Fin 4 × Fin r :=
  (Fin.castLEEmb upper).trans finProdFinEquiv.symm.toEmbedding

private def anchor {t r : ℕ} {m : ℕ} (lower : m * r ≤ t) (a : Fin m) : Fin r ↪ Fin t :=
  { toFun := fun i => (finProdFinEquiv (a, i)).castLE lower
    inj' := fun _ _ he => (Prod.mk_right_inj).mp
      (finProdFinEquiv.injective (Fin.castLE_injective _ he)) }

private theorem layers_anchor {t r m : ℕ} (upper : t ≤ 4 * r) (lower : m * r ≤ t)
    (hm : m ≤ 4) (l : Fin m) (a : Fin r) :
    layers upper (anchor lower l a) = (l.castLE hm, a) := by
  apply finProdFinEquiv.injective
  change finProdFinEquiv (finProdFinEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

private def coded {t h r : ℕ} {C : Type*} (upper : t ≤ 4 * r)
    (addr : Fin (2 ^ h) ≃ Fin r × C) :
    RoutingSlot t h ↪ (Fin r × Fin r × C) × (Fin 4 × Fin h) where
  toFun := fun (j, i, b) =>
    let u := layers upper j
    (switch u.1 (u.2, addr i), u.1, b)
  inj' := by
    rintro ⟨j, i, b⟩ ⟨k, n, d⟩ he
    obtain ⟨hs, hp⟩ := Prod.mk.inj he
    obtain ⟨hd, hb⟩ := Prod.mk.inj hp
    have hh : ((layers upper j).2, addr i) = ((layers upper k).2, addr n) := by
      apply (switch (layers upper j).1).injective
      simpa only [hd] using hs
    have hj := (layers upper).injective (Prod.ext hd (congrArg Prod.fst hh))
    have hi := addr.injective (congrArg Prod.snd hh)
    cases hj
    cases hi
    cases hb
    rfl

private theorem terminal_load {t h r : ℕ} {C : Type*} [Finite C] (upper : t ≤ 4 * r)
    (addr : Fin (2 ^ h) ≃ Fin r × C) (s : Fin r × Fin r × C) :
    let f (l : RoutingSlot t h) := (coded upper addr l).1
    Nat.card {i // Sum.elim f f i = s} ≤ 8 * h := by
  dsimp only
  let e := coded upper addr
  let f (l : RoutingSlot t h) := (e l).1
  have cap : Nat.card {l // f l = s} ≤ 4 * h := calc
    _ ≤ Nat.card (Fin 4 × Fin h) := Nat.card_le_card_of_injective
      (fun l : {l // f l = s} => (e l.val).2) fun x y he =>
        Subtype.ext (e.injective (Prod.ext (x.prop.trans y.prop.symm) he))
    _ = _ := by simp
  rw [Nat.card_subtype_sum]
  exact (Nat.add_le_add cap cap).trans (by lia)

private def select {t h r : ℕ} {C : Type*} (pin : Fin r ↪ Fin t)
    (addr : Fin (2 ^ h) ≃ Fin r × C) (swap : Equiv.Perm (Fin r × Fin r × C)) :
    (Fin r × Fin r × C) × Fin h ↪ RoutingSlot t h :=
  ((swap.prodCongr (Equiv.refl _)).toEmbedding.trans
    (Equiv.prodAssoc (Fin r) (Fin r × C) (Fin h)).toEmbedding).trans
      (pin.prodMap (addr.symm.toEmbedding.prodMap (Embedding.refl _)))

private def onRecords {t h : ℕ} (ρ : Equiv.Perm (Fin (2 ^ h))) : Equiv.Perm (RoutingSlot t h) :=
  (Equiv.refl (Fin t)).prodCongr (ρ.prodCongr (Equiv.refl (Fin h)))

private theorem selected_start {t h r : ℕ} {C : Type*} (upper : t ≤ 4 * r)
    (addr : Fin (2 ^ h) ≃ Fin r × C) (l : Fin 4) (pin : Fin r ↪ Fin t)
    (hpin : ∀ a, layers upper (pin a) = (l, a)) (p : (Fin r × Fin r × C) × Fin h) :
    (coded upper addr (select pin addr (switch l).symm p)).1 = p.1 := by
  change switch (layers upper (pin ((switch l).symm p.1).1)).1
    ((layers upper (pin ((switch l).symm p.1).1)).2, addr (addr.symm ((switch l).symm p.1).2)) = _
  rw [hpin, Equiv.apply_symm_apply]
  exact (switch l).apply_symm_apply _

private theorem selected_end {t h r : ℕ} {C : Type*} (upper : t ≤ 4 * r)
    (addr : Fin (2 ^ h) ≃ Fin r × C) (l : Fin 4) (pin : Fin r ↪ Fin t)
    (hpin : ∀ a, layers upper (pin a) = (l, a)) (ρ : Equiv.Perm (Fin r × C))
    (p : (Fin r × Fin r × C) × Fin h) :
    (coded upper addr (onRecords (addr.trans (ρ.trans addr.symm))
      (select pin addr (switch l).symm p))).1 =
      switch l (((switch l).symm p.1).1, ρ ((switch l).symm p.1).2) := by
  change switch (layers upper (pin ((switch l).symm p.1).1)).1
    ((layers upper (pin ((switch l).symm p.1).1)).2,
      addr (addr.symm (ρ (addr (addr.symm ((switch l).symm p.1).2))))) = _
  rw [hpin, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem exists_grid_width {t h : ℕ} (ht : 0 < t) (hbound : t ≤ 2 * 2 ^ h) :
    ∃ k ≤ h, 2 ^ k ≤ t ∧ t ≤ 4 * 2 ^ k ∧ (2 * 2 ^ k ≤ t ∨ (k = 0 ∧ t = 1)) := by
  by_cases hs : t = 1
  · exact ⟨0, Nat.zero_le _, by simp [hs], by simp [hs], Or.inr ⟨rfl, hs⟩⟩
  let k := Nat.log 2 (t / 2)
  have lo : 2 ^ k ≤ t / 2 := Nat.pow_log_le_self _ (by lia)
  have hi := Nat.lt_pow_succ_log_self one_lt_two (t / 2)
  change t / 2 < 2 ^ (k + 1) at hi
  rw [pow_succ] at hi
  have kh : k ≤ h := (Nat.pow_le_pow_iff_right one_lt_two).mp (show 2 ^ k ≤ 2 ^ h by lia)
  exact ⟨k, kh, by lia, by lia, Or.inl (by lia)⟩

private def splitAddress {k h : ℕ} (hk : k ≤ h) :
    Fin (2 ^ h) ≃ Fin (2 ^ k) × Fin (2 ^ (h - k)) :=
  (finCongr (show 2 ^ h = 2 ^ k * 2 ^ (h - k) by rw [← pow_add, Nat.add_sub_of_le hk])).trans
    finProdFinEquiv.symm

open scoped Classical in
/-- A trivalent network realizing `t` tagged-permutation tests on `2 ^ h` records gives a
regular graph on `2 ^ k * 2 ^ h` sites, where `2 ^ k ≤ t ≤ 4 * 2 ^ k`. Its degree and
squared-distance Poincaré constant are bounded in terms of the number of network vertices
and `h`. The tests may share all their internal wiring. -/
public theorem exists_regular_of_taggedPermutation {K V E : Type} [Field K] [Fintype V] [Fintype E]
    [DecidableEq E] {t h : ℕ} [NeZero h] (ht : 0 < t) (htN : t ≤ 2 * 2 ^ h)
    (N : OpenBitNetwork K (Fin t × RoutingBit h) V E) (htri : N.Trivalent)
    (hT : ∀ z, N.contraction z =
      ∏ a : Fin t, if TaggedPermutation (fun q => z (a, q)) then 1 else 0) :
    ∃ k ≤ h, 2 ^ k ≤ t ∧ t ≤ 4 * 2 ^ k ∧
      let S := Fin (2 ^ k) × Fin (2 ^ k) × Fin (2 ^ (h - k))
      let q := Fintype.card V / (2 ^ k * 2 ^ h) + 1 + 8 * h
      ∃ R : RotationMap S (Fin q × Fin 3), ∀ (X : Type u) [PseudoMetricSpace X],
        PartyTensor.IsPrice K (dist : X → X → ℝ) → ∀ f : S → X,
        (𝔼 s, 𝔼 s', dist (f s) (f s') ^ 2) ≤
          12 * (2 * ((q : ℝ) * 3 / h)) ^ 2 *
            𝔼 p : S × (Fin q × Fin 3), dist (f p.1) (f (R.rot p).1) ^ 2 := by
  classical
  obtain ⟨k, hk, lo, hi, cover⟩ := exists_grid_width ht htN
  refine ⟨k, hk, lo, hi, ?_⟩
  let A := Fin (2 ^ k)
  let C := Fin (2 ^ (h - k))
  let B := A × C
  let S := A × B
  let addr : Fin (2 ^ h) ≃ B := splitAddress hk
  let endSite (s : RoutingSlot t h) := (coded hi addr s).1
  let terminal := Sum.elim endSite endSite
  choose net hgraph htriv hvol hsites hcontract using fun ρ : Equiv.Perm (Fin (2 ^ h)) =>
    exists_permutationWires_of_taggedPermutation N htri hT (fun _ => ρ)
  let G := net (Equiv.refl _)
  have same (ρ : Equiv.Perm (Fin (2 ^ h))) : (net ρ).site = G.site := by
    funext s
    rcases s with ⟨a, i, b⟩ | ⟨a, i, b⟩
    · exact (hsites ρ a i b).1.trans (hsites (Equiv.refl _) a i b).1.symm
    · exact (hsites ρ a i b).2.trans (hsites (Equiv.refl _) a i b).2.symm
  have make {T : Type} (l : Fin 4) (pin : A ↪ Fin t) (hp : ∀ a, layers hi (pin a) = (l, a))
      (move : T → Equiv.Perm B) (shift : T → S → S)
      (he : ∀ δ s,
        switch l (((switch l).symm s).1, move δ ((switch l).symm s).2) = shift δ s) :
      G.ShiftRoutings terminal h shift :=
    { active := select pin addr (switch l).symm
      perm := fun δ => onRecords (addr.trans ((move δ).trans addr.symm))
      tables := fun δ => net (addr.trans ((move δ).trans addr.symm))
      graph_eq := fun δ => (hgraph _).trans (hgraph (Equiv.refl _)).symm
      sites_eq := fun δ => same _
      contraction_eq := fun δ => hcontract _
      input_site := selected_start hi addr l pin hp
      output_site := fun δ p => (selected_end hi addr l pin hp (move δ) p).trans (he δ p.1) }
  let row := anchor (show 1 * 2 ^ k ≤ t by simpa using lo) (0 : Fin 1)
  have hr (a : A) : layers hi (row a) = (0, a) := layers_anchor hi _ (by decide) (0 : Fin 1) a
  let rows := make 0 row hr (fun δ : B => Equiv.addRight δ) (fun δ s => (s.1, s.2 + δ))
    (by intro δ s; simp [switch])
  have cols : G.ShiftRoutings terminal h (fun δ : A => fun s => (s.1 + δ, s.2)) := by
    by_cases hc : 2 * 2 ^ k ≤ t
    · let col := anchor hc (1 : Fin 2)
      have hc' (a : A) : layers hi (col a) = (1, a) := layers_anchor hi hc (by decide) 1 a
      apply make 1 col hc' (fun δ : A => Equiv.addRight (δ, (0 : C)))
      rintro δ ⟨a, b, c⟩
      change (a + δ, b, c + 0) = (a + δ, b, c)
      simp
    · have hk0 := (cover.resolve_left hc).1
      have : Subsingleton A := by
        dsimp [A]
        rw [hk0, pow_zero]
        infer_instance
      apply make 0 row hr (fun _ : A => Equiv.refl B)
      rintro δ ⟨a, b, c⟩
      simp [switch, Subsingleton.elim (a + δ) a]
  have hs : Fintype.card S = 2 ^ k * 2 ^ h := by
    simp only [S, B, A, C, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_add, Nat.add_sub_of_le hk]
  change ∃ R : RotationMap S (Fin (Fintype.card V / (2 ^ k * 2 ^ h) + 1 + 8 * h) × Fin 3), _
  rw [← hs]
  exact G.exists_regular_of_terminal_shifts (htriv _) terminal h (8 * h)
    (terminal_load hi addr) rows cols

end Cslib.Circuits.Boolean.ElementDistinctness
