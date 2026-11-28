/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Operations
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Reparameterisation

/-!
# Reparameterisation of `3.5n` gate-elimination states

Two reparameterisation operations for `3.5n` states:

* `State.Valid.swap`: specialization of the shared affine reparameterisation `(AR)`
  (`AffineDisperserCore.State.swap`) preserving `PairTame` affinity;
* `State.quad`: the quadratic reparameterisation `(QR)` ([MishraSanthanam2026], §2.4 eq. (3),
  §3.2, and §4.3), substituting `z = D + (x + α)(y + β) + γ + c`, moving `D` into the parameters,
  deleting `G` and `D`, and pairing `x` with `y`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.quad`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.QuadOK`: the quadratic reparameterisation and
  its hypotheses.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.swap`: `(AR)` preserves validity.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.quad`: `(QR)` preserves validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

private theorem ne_of_not_paired {S : State n} {z : ℕ} (hz : ¬ S.Paired z) {pr : ℕ × ℕ}
    (hpr : pr ∈ S.pairs) : pr.1 ≠ z ∧ pr.2 ≠ z :=
  ⟨fun he => hz ⟨pr, hpr, Or.inl he⟩, fun he => hz ⟨pr, hpr, Or.inr he⟩⟩

private theorem pairTame_update {k : ℕ} {τ : BitString k → ℕ → Bool} {z : ℕ}
    {g : BitString k → Bool} {pr : ℕ × ℕ} (h1 : pr.1 ≠ z) (h2 : pr.2 ≠ z)
    (ht : PairTame τ pr) :
    PairTame (fun u => Function.update (τ u) z (g u)) pr := by
  rcases ht with ht | ht | ht
  · exact Or.inl fun u v => by simpa only [Function.update_of_ne h1] using ht u v
  · exact Or.inr (Or.inl fun u v => by simpa only [Function.update_of_ne h2] using ht u v)
  · exact Or.inr (Or.inr fun u v => by
      simpa only [Function.update_of_ne h1, Function.update_of_ne h2] using ht u v)

/-! ### Affine reparameterisation (AR) -/

/-- The affine reparameterisation preserves validity. -/
theorem Valid.swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).Valid f :=
  Valid.swap_of hS h fun k τ hτ htame =>
    hS.phi_affine k (fun u => Function.update (τ u) x (τ u Q + c + ∑ j ∈ T.erase x, τ u j))
      (isAffine_update hτ x (isAffine_add_add_sum hτ Q c (T.erase x))) fun pr hpr =>
      let ⟨hx1, hx2⟩ := ne_of_not_paired h.unpaired hpr
      pairTame_update hx1 hx2 (htame pr hpr)

/-! ### Quadratic reparameterisation (QR) -/

/-- Along an affine family on which the pair `(x, y)` is tame, the product
`(u x + α) (u y + β)` is affine. -/
private theorem isAffine_mul_of_pairTame {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ)
    {x y : ℕ} (ht : PairTame τ (x, y)) (α β : Bool) :
    IsAffine fun u => (τ u x + α) * (τ u y + β) := by
  intro u v w
  have hy : τ (u + v + w) y = τ u y + τ v y + τ w y := congrFun (hτ u v w) y
  have hx : τ (u + v + w) x = τ u x + τ v x + τ w x := congrFun (hτ u v w) x
  dsimp only [PairTame] at ht ⊢
  rcases ht with ht | ht | ht
  · rw [ht (u + v + w) 0, ht u 0, ht v 0, ht w 0, hy]
    generalize τ 0 x = a; generalize τ u y = b₁; generalize τ v y = b₂; generalize τ w y = b₃
    revert a b₁ b₂ b₃ α β; decide
  · rw [ht (u + v + w) 0, ht u 0, ht v 0, ht w 0, hx]
    generalize τ 0 y = a; generalize τ u x = b₁; generalize τ v x = b₂; generalize τ w x = b₃
    revert a b₁ b₂ b₃ α β; decide
  · have h0 (u') : τ u' x = τ u' y + (τ 0 x + τ 0 y) := by
      have := ht u' 0
      rw [← this]
      generalize τ u' x = a; generalize τ u' y = b; revert a b; decide
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hy]
    generalize τ 0 x + τ 0 y = a; generalize τ u y = b₁; generalize τ v y = b₂
    generalize τ w y = b₃
    revert a b₁ b₂ b₃ α β; decide

/-- The quadratic reparameterisation: for an AND-type gate `G = (x + α)(y + β) + γ` whose only
child is the XOR-type gate `D = G + z + c`, where `z` is an isolated parameter, substitute
`z = D + G + c` in the parameter map, turn `D` into a parameter (it computes the new parameter
`w` of the source), delete the gates `G` and `D`, and pair `x` with `y`. -/
@[expose] def quad (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : State n where
  toSemiCircuit := S.toSemiCircuit.quad z G D
  pairs := insert (x, y) S.pairs
  phi val := S.phi (Function.update val z (val D + ((val x + α) * (val y + β) + γ) + c))

/-- The hypotheses of the quadratic reparameterisation: the configuration of
`SemiCircuit.QuadOK` on unpaired parameters. -/
structure QuadOK (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : Prop
    extends SemiCircuit.QuadOK S.toSemiCircuit x y z G D α β γ c where
  /-- `x` is not paired. -/
  unpaired_x : ¬ S.Paired x
  /-- `y` is not paired. -/
  unpaired_y : ¬ S.Paired y
  /-- `z` is not paired. -/
  unpaired_z : ¬ S.Paired z

/-- The quadratic reparameterisation replaces `z` with `D` in `S.params`. -/
@[simp] theorem quad_params (S : State n) (x y z G D : ℕ) (α β γ c : Bool) :
    (S.quad x y z G D α β γ c).params = insert D (S.params.erase z) := rfl

/-- The quadratic reparameterisation inserts `(x, y)` into `S.pairs`. -/
@[simp] theorem quad_pairs (S : State n) (x y z G D : ℕ) (α β γ c : Bool) :
    (S.quad x y z G D α β γ c).pairs = insert (x, y) S.pairs := rfl

/-- The quadratic reparameterisation decreases the size of the state by `2`. -/
theorem quad_size {S : State n} {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) : (S.quad x y z G D α β γ c).size + 2 = S.size := by
  have h1 := Finset.card_erase_add_one h.mem_D
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨h.G_ne_D, h.mem_G⟩)
  simp only [SemiCircuit.size] at *
  change ((S.gates.erase D).erase G).card + S.eqns.card + 2 = _
  omega

/-- After the quadratic reparameterisation, the children of `w` are contained in `S.children w`
with `.inl D` and `.inl G` removed. -/
theorem quad_children_subset (S : State n) (x y z G D : ℕ) (α β γ c : Bool) (w : ℕ) :
    (S.quad x y z G D α β γ c).children w ⊆ ((S.children w).erase (.inl D)).erase (.inl G) := by
  rintro (K | e) hv
  · obtain ⟨hK, hr⟩ := (SemiCircuit.inl_mem_children (S.quad x y z G D α β γ c).toSemiCircuit).1 hv
    obtain ⟨hKG, hKD, hK⟩ : K ≠ G ∧ K ≠ D ∧ K ∈ S.gates := by
      simpa [quad, SemiCircuit.quad, and_assoc] using hK
    simp only [Finset.mem_erase, ne_eq, Sum.inl.injEq]
    exact ⟨hKG, hKD, (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩⟩
  · simp only [Finset.mem_erase, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact (SemiCircuit.inr_mem_children _).2
      ((SemiCircuit.inr_mem_children (S.quad x y z G D α β γ c).toSemiCircuit).1 hv)

namespace QuadOK

variable {S : State n} {x y z G D : ℕ} {α β γ c : Bool} (h : S.QuadOK x y z G D α β γ c)
include h

private theorem pair_mem (hS : S.Valid f) : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs,
    pr.1 ∈ (S.quad x y z G D α β γ c).params ∧ pr.2 ∈ (S.quad x y z G D α β γ c).params ∧
      pr.1 ≠ pr.2 := by
  intro pr hpr
  rcases Finset.mem_insert.1 hpr with rfl | hpr
  · exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.x_ne_z, h.mem_x⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.y_ne_z, h.mem_y⟩), h.x_ne_y⟩
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr hpr
    obtain ⟨hz1, hz2⟩ := ne_of_not_paired h.unpaired_z hpr
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz1, h1⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz2, h2⟩), h12⟩

private theorem pairs_disjoint (hS : S.Valid f) : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs,
    ∀ pr' ∈ (S.quad x y z G D α β γ c).pairs, pr ≠ pr' →
      pr.1 ≠ pr'.1 ∧ pr.1 ≠ pr'.2 ∧ pr.2 ≠ pr'.1 ∧ pr.2 ≠ pr'.2 := by
  have hnew (pr) (hpr : pr ∈ S.pairs) : x ≠ pr.1 ∧ x ≠ pr.2 ∧ y ≠ pr.1 ∧ y ≠ pr.2 :=
    let ⟨hx1, hx2⟩ := ne_of_not_paired h.unpaired_x hpr
    let ⟨hy1, hy2⟩ := ne_of_not_paired h.unpaired_y hpr
    ⟨hx1.symm, hx2.symm, hy1.symm, hy2.symm⟩
  intro pr hpr pr' hpr' hne
  rcases Finset.mem_insert.1 hpr with rfl | hpr <;>
    rcases Finset.mem_insert.1 hpr' with rfl | hpr'
  · exact absurd rfl hne
  · exact hnew pr' hpr'
  · obtain ⟨h1, h2, h3, h4⟩ := hnew pr hpr
    exact ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩
  · exact hS.pairs_disjoint pr hpr pr' hpr' hne

private theorem affine (hS : S.Valid f) {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ)
    (htame : ∀ pr ∈ (S.quad x y z G D α β γ c).pairs, PairTame τ pr) :
    ∃ τ' : BitString k → ℕ → Bool, IsAffine τ' ∧ (∀ pr ∈ S.pairs, PairTame τ' pr) ∧
      ∀ u, ∀ j ∈ S.params, τ' u j = quadValue x y z G D α β γ c (τ u) j := by
  refine ⟨fun u => Function.update (τ u) z (τ u D + ((τ u x + α) * (τ u y + β) + γ) + c),
    ?_, fun pr hpr => ?_, fun u j hj => ?_⟩
  · refine isAffine_update hτ z fun u v w => ?_
    have hm := isAffine_mul_of_pairTame hτ (htame (x, y) (Finset.mem_insert_self _ _)) α β u v w
    dsimp only at hm
    have hD : τ (u + v + w) D = τ u D + τ v D + τ w D := congrFun (hτ u v w) D
    have hadd : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : Bool,
        (a₁ + a₂ + a₃) + (b₁ + b₂ + b₃) = (a₁ + b₁) + (a₂ + b₂) + (a₃ + b₃) := by decide
    have hconst : ∀ a₁ a₂ a₃ k : Bool,
        (a₁ + a₂ + a₃) + k = (a₁ + k) + (a₂ + k) + (a₃ + k) := by decide
    rw [hD, hm, hconst _ _ _ γ, hadd, hconst _ _ _ c]
  · obtain ⟨hz1, hz2⟩ := ne_of_not_paired h.unpaired_z hpr
    exact pairTame_update hz1 hz2 (htame pr (Finset.mem_insert_of_mem hpr))
  · have hjG : j ≠ G := fun he => hS.wf.notMem_gates_of_mem_params hj (he ▸ h.mem_G)
    simp only [quadValue, Function.update_of_ne hjG]

end QuadOK

/-- The quadratic reparameterisation preserves validity. -/
theorem Valid.quad {S : State n} (hS : S.Valid f) {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) : (S.quad x y z G D α β γ c).Valid f := by
  have hneG {i} (hi : i ∈ S.params) : i ≠ G := fun he =>
    hS.wf.notMem_params_of_mem_gates h.mem_G (he ▸ hi)
  set σ := quadValue x y z G D α β γ c
  have hσ (val i) (hz : i ≠ z) (hG : i ≠ G) : σ val i = val i := by
    simp only [σ, quadValue, Function.update_of_ne hG, Function.update_of_ne hz]
  have hσz (val) : σ val z = val D + ((val x + α) * (val y + β) + γ) + c := by
    simp only [σ, quadValue, Function.update_of_ne (hneG h.mem_z), Function.update_self]
  refine Valid.of_transport hS (σ := σ) (hS.wf.quad h.toQuadOK)
    { pair_mem := h.pair_mem hS
      pairs_disjoint := h.pairs_disjoint hS
      phi := fun val => hS.phi_congr _ _ fun j hj => by
        simp only [σ, quadValue, Function.update_of_ne (hneG hj)]
      phi_affine := fun k τ hτ htame => by
        obtain ⟨τ', hτ', htame', hagree⟩ := h.affine hS hτ htame
        have heq : (S.quad x y z G D α β γ c).phi ∘ τ = S.phi ∘ τ' := funext fun u =>
          hS.phi_congr _ _ fun j hj => by
            simpa only [σ, quadValue, Function.update_of_ne (hneG hj)] using (hagree u j hj).symm
        rw [heq]
        exact hS.phi_affine k τ' hτ' htame'
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      consistent := fun val hval => (h.toQuadOK.consistent hS.wf hval).1
      locus := fun _ _ => trivial
      out := fun val hval _ => (h.toQuadOK.consistent hS.wf hval).2 }
  · by_cases hjz : j = z
    · subst hjz
      rw [hσz, hσz, hv D (Finset.mem_insert_self _ _),
        hv x (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.x_ne_z, h.mem_x⟩)),
        hv y (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.y_ne_z, h.mem_y⟩))]
    · rw [hσ val j hjz (hneG hj), hσ val' j hjz (hneG hj)]
      exact hv j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjz, hj⟩))
  · rcases Finset.mem_insert.1 hj with rfl | hj
    · have hx : val x = val' x := by simpa only [hσ _ x h.x_ne_z (hneG h.mem_x)] using hv x h.mem_x
      have hy : val y = val' y := by simpa only [hσ _ y h.y_ne_z (hneG h.mem_y)] using hv y h.mem_y
      simpa [hσz, hx, hy] using hv z h.mem_z
    · simpa only [hσ _ j (Finset.ne_of_mem_erase hj) (hneG (Finset.mem_of_mem_erase hj))] using
        hv j (Finset.mem_of_mem_erase hj)

end State

end Cslib.Circuits.Boolean.AffineDisperser
