/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Cipher.LubyRackoff
public import CslibFrontier.Foundations.Data.BitString.HalfSplit
public import CslibFrontier.Languages.Probabilistic.RandomPermutation.ExtPermsCard
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Product
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Block cipher networks: SPNs, unbalanced Feistel networks, periodicity, and Feistel distinguishers

This module complements `CslibFrontier.Crypto.Protocols.Cipher.LubyRackoff` with structural and
concrete-security results on block cipher networks from [KatzLindell2020] and original extensions:

1. **Substitution–permutation networks (SPNs)** ([KatzLindell2020], Section 7.2.1, Proposition 7.3):
   in `Cslib.Crypto.SPN`, key mixing (`spnKeyMixEquiv`), S-box substitution (`spnSubstituteEquiv`),
   sub-block and wire permutations (`spnPermuteEquiv`, `spnBitPermuteEquiv`), single rounds
   (`spnRoundEquiv`), and multi-round SPNs (`spnNetworkEquiv`) are permutations with an explicit
   round-by-round inverse (`spnRoundEquiv_symm`, `spnNetworkEquiv_symm_cons`,
   `bijective_spnNetworkEquiv`).
2. **Unbalanced Feistel networks** (original construction generalizing the balanced Feistel network
   of [KatzLindell2020], Section 7.2.2, Proposition 7.4): alternating rounds on `A × B`
   (`unbalancedFeistelLeftEquiv`, `unbalancedFeistelRightEquiv`), 2- and 4-round networks
   (`unbalancedFeistel2`, `unbalancedFeistel4`), agreement with balanced Feistel (`feistel4`), and
   lifting to `Equiv.Perm (BitString n)` for any block length `n` (`unbalancedFeistel4BitString`,
   through the split `BitString.halfSplitEquiv`).
3. **Degenerate round-function periodicity** ([KatzLindell2020], Exercise 7.10(a),(b)): general
   periodicity reduction (`feistelNetwork_replicate_mod`), period-2 law for `0 : G → G`
   (`feistelNetwork_replicate_zero`), and period-3 law for `id : G → G` when `∀ a : G, -a = a`
   (`feistelNetwork_replicate_id`).
4. **Explicit 1- and 2-round CPA, 3-round repeated-key CPA, and 3-round CCA distinguishers**
   (attacks from [KatzLindell2020], Section 8.6 and Exercises 8.16–8.18; concrete bounds are
   original):
   - **Permutation-fiber counts**: the one-, two- and three-point bounds below specialize the
     `k`-point falling-factorial bound `RandomPermutation.card_extPerms_ofFn_mul_descFactorial_le`
     from `CslibFrontier.Languages.Probabilistic.RandomPermutation.ExtPermsCard`.
   - **1-round CPA** (`feistel1CPAAttack`, [KatzLindell2020], Section 8.6): accepts
     `feistelRoundEquiv f` w.p. `1`, `randomFunctionGame` w.p. `|G|⁻¹`, and `idealPermGame` w.p.
     `≤ |G|⁻¹` (original advantage bound `≥ 1 - |G|⁻¹`).
   - **2-round CPA** (`feistel2CPAAttack`, [KatzLindell2020], Exercise 8.16): accepts
     `feistelNetwork [f₁, f₂]` w.p. `1` and `idealPermGame` (`|G| ≥ 2`) w.p.
     `≤ |G| / (|G| ^ 2 - 1) ≤ 2 / 3` (original bound).
   - **3-round repeated-key (`[f, f, f]`) CPA** (`feistel3RepeatedKeyCPAAttack`, [KatzLindell2020],
     Exercise 8.18): accepts `feistel3 f f f` (`∀ a : G, -a = a`) w.p. `1` and `idealPermGame`
     (`|G| ≥ 2`) w.p. `≤ 2 / |G| ^ 2 ≤ 1 / 2` (original bound).
   - **Sharper permutation-fiber bound for 3-round CCA** (attack from [KatzLindell2020],
     Exercise 8.17; original bound `idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one`,
     `le_advantage_feistel3CCAAttack_idealStrongGame_of_two_le_card`): refines the lazy-sampling
     bound on `feistel3CCAAttack l₀ l₁ r₀` to `(|G| + 1) / (|G| ^ 2 - 1) = (|G| - 1)⁻¹`.

## Implementation notes

In [KatzLindell2020], Section 8.6 and Exercises 8.16–8.18 state the distinguishers against Feistel
networks instantiated with keyed PRFs `F_{k_i}`. Proving acceptance with probability `1` for every
fixed tuple of round functions `f₁, f₂, f₃ : G → G` immediately implies acceptance with probability
`1` under any key distribution (such as the keys of `feistel3Cipher` in `LubyRackoff`).

## References

* [J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Sections 7.2.1–7.2.2, Propositions 7.3–7.4, Exercise 7.10, Section 8.6, and Exercises 8.16–8.18.
* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 4.5 and Exercise 4.15.
-/

@[expose] public section

/-! ### Substitution–permutation networks (SPNs) -/

namespace Cslib.Crypto.SPN

variable {boxes width : ℕ} {G : Type*}

/-- The state of a substitution–permutation network with `boxes` sub-blocks in `G`:
a tuple `Fin boxes → G`. -/
abbrev SPNState (boxes : ℕ) (G : Type*) := Fin boxes → G

/-- Parallel S-box substitution layer of an SPN: apply a family of bijective S-boxes
`sboxes : Fin boxes → Equiv.Perm G` independently to each sub-block (`i ↦ sboxes i (state i)`). -/
def spnSubstituteEquiv (sboxes : Fin boxes → Equiv.Perm G) : Equiv.Perm (SPNState boxes G) :=
  Equiv.piCongrRight sboxes

@[simp] theorem spnSubstituteEquiv_apply (sboxes : Fin boxes → Equiv.Perm G)
    (state : SPNState boxes G) (i : Fin boxes) :
    spnSubstituteEquiv sboxes state i = sboxes i (state i) := rfl

@[simp] theorem spnSubstituteEquiv_symm (sboxes : Fin boxes → Equiv.Perm G) :
    (spnSubstituteEquiv sboxes).symm = spnSubstituteEquiv (fun i => (sboxes i).symm) := rfl

/-- Sub-block permutation layer across `Fin boxes`: reindex sub-blocks along
`σ : Equiv.Perm (Fin boxes)`. -/
def spnPermuteEquiv (σ : Equiv.Perm (Fin boxes)) : Equiv.Perm (SPNState boxes G) where
  toFun state i := state (σ.symm i)
  invFun state i := state (σ i)
  left_inv state := by funext i; simp
  right_inv state := by funext i; simp

@[simp] theorem spnPermuteEquiv_apply (σ : Equiv.Perm (Fin boxes)) (state : SPNState boxes G)
    (i : Fin boxes) :
    spnPermuteEquiv σ state i = state (σ.symm i) := rfl

@[simp] theorem spnPermuteEquiv_symm (σ : Equiv.Perm (Fin boxes)) :
    (spnPermuteEquiv (G := G) σ).symm = spnPermuteEquiv σ.symm := rfl

/-- Wire-level bit-permutation (mixing) layer on `SPNState boxes (BitString width)`:
permute the `boxes × width` individual bit coordinates according to
`mix : Equiv.Perm (Fin boxes × Fin width)`. -/
def spnBitPermuteEquiv (mix : Equiv.Perm (Fin boxes × Fin width)) :
    Equiv.Perm (SPNState boxes (BitString width)) where
  toFun state i j := state (mix.symm (i, j)).1 (mix.symm (i, j)).2
  invFun state i j := state (mix (i, j)).1 (mix (i, j)).2
  left_inv state := by funext i j; simp
  right_inv state := by funext i j; simp

@[simp] theorem spnBitPermuteEquiv_apply (mix : Equiv.Perm (Fin boxes × Fin width))
    (state : SPNState boxes (BitString width)) (i : Fin boxes) (j : Fin width) :
    spnBitPermuteEquiv mix state i j = state (mix.symm (i, j)).1 (mix.symm (i, j)).2 := rfl

@[simp] theorem spnBitPermuteEquiv_symm (mix : Equiv.Perm (Fin boxes × Fin width)) :
    (spnBitPermuteEquiv mix).symm = spnBitPermuteEquiv mix.symm := rfl

variable [AddGroup G]

/-- Subkey mixing layer of an SPN: add `subkey : SPNState boxes G` coordinatewise on the right
(`state ↦ state + subkey`), with inverse `state ↦ state - subkey`. -/
def spnKeyMixEquiv (subkey : SPNState boxes G) : Equiv.Perm (SPNState boxes G) where
  toFun state := state + subkey
  invFun state := state - subkey
  left_inv state := add_sub_cancel_right state subkey
  right_inv state := sub_add_cancel state subkey

@[simp] theorem spnKeyMixEquiv_apply (subkey state : SPNState boxes G) :
    spnKeyMixEquiv subkey state = state + subkey := rfl

@[simp] theorem spnKeyMixEquiv_symm_apply (subkey state : SPNState boxes G) :
    (spnKeyMixEquiv subkey).symm state = state - subkey := rfl

/-- A single round of a substitution–permutation network ([KatzLindell2020], Section 7.2.1):
mix in `subkey`, apply parallel S-boxes `sboxes`, and apply `mixLayer`. -/
def spnRoundEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey : SPNState boxes G) :
    Equiv.Perm (SPNState boxes G) :=
  (spnKeyMixEquiv subkey).trans ((spnSubstituteEquiv sboxes).trans mixLayer)

@[simp] theorem spnRoundEquiv_apply (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey state : SPNState boxes G) :
    spnRoundEquiv sboxes mixLayer subkey state =
      mixLayer (spnSubstituteEquiv sboxes (state + subkey)) := rfl

/-- Explicit inverse of a single SPN round: invert `mixLayer`, apply inverse S-boxes
`(sboxes i).symm`, and subtract `subkey`. -/
theorem spnRoundEquiv_symm (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey : SPNState boxes G) :
    (spnRoundEquiv sboxes mixLayer subkey).symm =
      mixLayer.symm.trans
        ((spnSubstituteEquiv (fun i => (sboxes i).symm)).trans (spnKeyMixEquiv subkey).symm) :=
  rfl

@[simp] theorem spnRoundEquiv_symm_apply (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey state : SPNState boxes G) :
    (spnRoundEquiv sboxes mixLayer subkey).symm state =
      spnSubstituteEquiv (fun i => (sboxes i).symm) (mixLayer.symm state) - subkey := rfl

/-- Multi-round substitution–permutation network without final post-whitening:
fold `spnRoundEquiv sboxes mixLayer k` left-to-right across `roundKeys`. -/
def spnRoundsEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G)) :
    Equiv.Perm (SPNState boxes G) :=
  roundKeys.foldl (fun acc k => acc.trans (spnRoundEquiv sboxes mixLayer k)) (Equiv.refl _)

@[simp] theorem spnRoundsEquiv_nil (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) :
    spnRoundsEquiv sboxes mixLayer [] = Equiv.refl (SPNState boxes G) := rfl

@[simp] theorem spnRoundsEquiv_cons (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (k : SPNState boxes G)
    (ks : List (SPNState boxes G)) :
    spnRoundsEquiv sboxes mixLayer (k :: ks) =
      (spnRoundEquiv sboxes mixLayer k).trans (spnRoundsEquiv sboxes mixLayer ks) := by
  have h (e : Equiv.Perm (SPNState boxes G)) (l : List (SPNState boxes G)) :
      l.foldl (fun acc k => acc.trans (spnRoundEquiv sboxes mixLayer k)) e =
        e.trans (spnRoundsEquiv sboxes mixLayer l) := by
    induction l generalizing e with
    | nil => rfl
    | cons k' rest ih => rw [List.foldl_cons, spnRoundsEquiv, List.foldl_cons, ih, ih]; rfl
  exact h (spnRoundEquiv sboxes mixLayer k) ks

@[simp] theorem spnRoundsEquiv_append (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (ks₁ ks₂ : List (SPNState boxes G)) :
    spnRoundsEquiv sboxes mixLayer (ks₁ ++ ks₂) =
      (spnRoundsEquiv sboxes mixLayer ks₁).trans (spnRoundsEquiv sboxes mixLayer ks₂) := by
  induction ks₁ with
  | nil => rfl
  | cons k ks₁ ih => simp only [List.cons_append, spnRoundsEquiv_cons, ih]; rfl

/-- Full substitution–permutation network ([KatzLindell2020], Section 7.2.1, Proposition 7.3):
execute `spnRoundsEquiv sboxes mixLayer roundKeys` followed by a final post-whitening key-mixing
step `spnKeyMixEquiv finalKey`. -/
def spnNetworkEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G))
    (finalKey : SPNState boxes G) : Equiv.Perm (SPNState boxes G) :=
  (spnRoundsEquiv sboxes mixLayer roundKeys).trans (spnKeyMixEquiv finalKey)

@[simp] theorem spnNetworkEquiv_apply (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G))
    (finalKey state : SPNState boxes G) :
    spnNetworkEquiv sboxes mixLayer roundKeys finalKey state =
      spnRoundsEquiv sboxes mixLayer roundKeys state + finalKey := rfl

@[simp] theorem spnNetworkEquiv_symm_nil (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (finalKey : SPNState boxes G) :
    (spnNetworkEquiv sboxes mixLayer [] finalKey).symm = (spnKeyMixEquiv finalKey).symm := rfl

/-- Decrypting a non-empty SPN (`k :: ks`) undoes the remaining network `(ks, finalKey)` first and
then applies the single-round inverse `(spnRoundEquiv sboxes mixLayer k).symm`. -/
theorem spnNetworkEquiv_symm_cons (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (k : SPNState boxes G)
    (ks : List (SPNState boxes G)) (finalKey : SPNState boxes G) :
    (spnNetworkEquiv sboxes mixLayer (k :: ks) finalKey).symm =
      (spnNetworkEquiv sboxes mixLayer ks finalKey).symm.trans
        (spnRoundEquiv sboxes mixLayer k).symm := by
  ext state; simp [spnNetworkEquiv]

/-- **Proposition 7.3 of [KatzLindell2020]**: for any bijective S-boxes `sboxes`, any bijective
mixing layer `mixLayer`, and any subkey schedule `(roundKeys, finalKey)`, the resulting
substitution–permutation network `spnNetworkEquiv sboxes mixLayer roundKeys finalKey` is a bijection
on `SPNState boxes G`. -/
theorem bijective_spnNetworkEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G))
    (finalKey : SPNState boxes G) :
    Function.Bijective (spnNetworkEquiv sboxes mixLayer roundKeys finalKey) :=
  (spnNetworkEquiv sboxes mixLayer roundKeys finalKey).bijective

end Cslib.Crypto.SPN

namespace Cslib.Crypto.LubyRackoff

open Cslib.Probability
open scoped ENNReal NNReal BigOperators

/-! ### Unbalanced Feistel networks and arbitrary block-length splitting -/

section UnbalancedFeistel

variable {A B G : Type*}

/-- Left-updating unbalanced Feistel round on `A × B` (original):
`(a, b) ↦ (a + f b, b)` for `f : B → A`. -/
def unbalancedFeistelLeft [AddGroup A] (f : B → A) (p : A × B) : A × B :=
  (p.1 + f p.2, p.2)

/-- Explicit inverse of a left-updating unbalanced Feistel round: `(a, b) ↦ (a - f b, b)`. -/
def unbalancedFeistelLeftInv [AddGroup A] (f : B → A) (p : A × B) : A × B :=
  (p.1 - f p.2, p.2)

/-- Left-updating unbalanced Feistel round bundled as a permutation `Equiv.Perm (A × B)`. -/
def unbalancedFeistelLeftEquiv [AddGroup A] (f : B → A) : Equiv.Perm (A × B) where
  toFun := unbalancedFeistelLeft f
  invFun := unbalancedFeistelLeftInv f
  left_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelLeft, unbalancedFeistelLeftInv]
  right_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelLeft, unbalancedFeistelLeftInv]

@[simp] theorem unbalancedFeistelLeftEquiv_apply [AddGroup A] (f : B → A) (p : A × B) :
    unbalancedFeistelLeftEquiv f p = (p.1 + f p.2, p.2) := rfl

@[simp] theorem unbalancedFeistelLeftEquiv_symm_apply [AddGroup A] (f : B → A) (p : A × B) :
    (unbalancedFeistelLeftEquiv f).symm p = (p.1 - f p.2, p.2) := rfl

/-- Right-updating unbalanced Feistel round on `A × B` (original):
`(a, b) ↦ (a, b + g a)` for `g : A → B`. -/
def unbalancedFeistelRight [AddGroup B] (g : A → B) (p : A × B) : A × B :=
  (p.1, p.2 + g p.1)

/-- Explicit inverse of a right-updating unbalanced Feistel round: `(a, b) ↦ (a, b - g a)`. -/
def unbalancedFeistelRightInv [AddGroup B] (g : A → B) (p : A × B) : A × B :=
  (p.1, p.2 - g p.1)

/-- Right-updating unbalanced Feistel round bundled as a permutation `Equiv.Perm (A × B)`. -/
def unbalancedFeistelRightEquiv [AddGroup B] (g : A → B) : Equiv.Perm (A × B) where
  toFun := unbalancedFeistelRight g
  invFun := unbalancedFeistelRightInv g
  left_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelRight, unbalancedFeistelRightInv]
  right_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelRight, unbalancedFeistelRightInv]

@[simp] theorem unbalancedFeistelRightEquiv_apply [AddGroup B] (g : A → B) (p : A × B) :
    unbalancedFeistelRightEquiv g p = (p.1, p.2 + g p.1) := rfl

@[simp] theorem unbalancedFeistelRightEquiv_symm_apply [AddGroup B] (g : A → B) (p : A × B) :
    (unbalancedFeistelRightEquiv g).symm p = (p.1, p.2 - g p.1) := rfl

/-- Swapping the two halves (`Equiv.prodComm`) conjugates a left-updating unbalanced Feistel round
into a right-updating unbalanced Feistel round. -/
theorem prodComm_trans_unbalancedFeistelLeftEquiv_trans_prodComm [AddGroup A] (f : B → A) :
    (Equiv.prodComm B A).trans
      ((unbalancedFeistelLeftEquiv f).trans (Equiv.prodComm A B)) =
      unbalancedFeistelRightEquiv f := by
  ext ⟨b, a⟩ <;> rfl

/-- A balanced Feistel round `feistelRoundEquiv f` ([KatzLindell2020], Section 7.2.2,
Proposition 7.4) is a left-updating unbalanced round followed by swapping halves
`Equiv.prodComm G G`. -/
theorem feistelRoundEquiv_eq_unbalancedFeistelLeftEquiv_trans_prodComm [AddGroup G] (f : G → G) :
    feistelRoundEquiv f = (unbalancedFeistelLeftEquiv f).trans (Equiv.prodComm G G) := by
  ext ⟨l, r⟩ <;> rfl

/-- Two-round alternating unbalanced Feistel network on `A × B` (original): update `A` using
`f₁ : B → A`, then update `B` using `f₂ : A → B`. -/
def unbalancedFeistel2 [AddGroup A] [AddGroup B] (f₁ : B → A) (f₂ : A → B) :
    Equiv.Perm (A × B) :=
  (unbalancedFeistelLeftEquiv f₁).trans (unbalancedFeistelRightEquiv f₂)

@[simp] theorem unbalancedFeistel2_apply [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (p : A × B) :
    unbalancedFeistel2 f₁ f₂ p = (p.1 + f₁ p.2, p.2 + f₂ (p.1 + f₁ p.2)) := rfl

@[simp] theorem unbalancedFeistel2_symm_apply [AddGroup A] [AddGroup B] (f₁ : B → A) (f₂ : A → B)
    (p : A × B) :
    (unbalancedFeistel2 f₁ f₂).symm p = (p.1 - f₁ (p.2 - f₂ p.1), p.2 - f₂ p.1) := rfl

/-- When `A = B = G`, the 2-round alternating unbalanced Feistel network `unbalancedFeistel2 f₁ f₂`
coincides with the 2-round balanced Feistel network `feistelNetwork [f₁, f₂]`. -/
theorem unbalancedFeistel2_eq_feistelNetwork [AddGroup G] (f₁ f₂ : G → G) :
    unbalancedFeistel2 f₁ f₂ = feistelNetwork [f₁, f₂] := rfl

/-- Four-round alternating unbalanced Feistel network on `A × B` (original): alternate `f₁ : B → A`,
`f₂ : A → B`, `f₃ : B → A`, and `f₄ : A → B`. -/
def unbalancedFeistel4 [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (f₃ : B → A) (f₄ : A → B) :
    Equiv.Perm (A × B) :=
  (unbalancedFeistel2 f₁ f₂).trans (unbalancedFeistel2 f₃ f₄)

theorem unbalancedFeistel4_apply [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (f₃ : B → A) (f₄ : A → B) (p : A × B) :
    unbalancedFeistel4 f₁ f₂ f₃ f₄ p =
      let u := p.1 + f₁ p.2
      let v := p.2 + f₂ u
      let w := u + f₃ v
      (w, v + f₄ w) := rfl

theorem unbalancedFeistel4_symm_apply [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (f₃ : B → A) (f₄ : A → B) (wz : A × B) :
    (unbalancedFeistel4 f₁ f₂ f₃ f₄).symm wz =
      let v := wz.2 - f₄ wz.1
      let u := wz.1 - f₃ v
      (u - f₁ (v - f₂ u), v - f₂ u) := rfl

/-- When `A = B = G`, the 4-round alternating unbalanced Feistel network
`unbalancedFeistel4 f₁ f₂ f₃ f₄` coincides with the 4-round balanced Feistel network
`feistel4 f₁ f₂ f₃ f₄`. -/
theorem unbalancedFeistel4_eq_feistel4 [AddGroup G] (f₁ f₂ f₃ f₄ : G → G) :
    unbalancedFeistel4 f₁ f₂ f₃ f₄ = feistel4 f₁ f₂ f₃ f₄ := rfl

/-- Four-round unbalanced Feistel permutation on `BitString n` for any (even or odd) block size `n`,
constructed from half-block round functions `f₁, f₃ : BitString (n - n / 2) → BitString (n / 2)`
and `f₂, f₄ : BitString (n / 2) → BitString (n - n / 2)` (original). -/
def unbalancedFeistel4BitString (n : ℕ)
    (f₁ : BitString (n - n / 2) → BitString (n / 2))
    (f₂ : BitString (n / 2) → BitString (n - n / 2))
    (f₃ : BitString (n - n / 2) → BitString (n / 2))
    (f₄ : BitString (n / 2) → BitString (n - n / 2)) :
    Equiv.Perm (BitString n) :=
  (BitString.halfSplitEquiv n).trans
    ((unbalancedFeistel4 f₁ f₂ f₃ f₄).trans (BitString.halfSplitEquiv n).symm)

end UnbalancedFeistel

/-! ### Degenerate round-function periodicity in Feistel networks -/

section Periodicity

variable {G : Type*} [AddGroup G]

/-- Replicating `a + b` copies of a single round function `f` composes the `a`-round and `b`-round
Feistel networks. -/
theorem feistelNetwork_replicate_add (a b : ℕ) (f : G → G) :
    feistelNetwork (List.replicate (a + b) f) =
      (feistelNetwork (List.replicate a f)).trans (feistelNetwork (List.replicate b f)) := by
  rw [List.replicate_add, feistelNetwork_append]

/-- If `k` identical Feistel rounds of `f` compose to the identity permutation on `G × G`, then
for every `r : ℕ`, `r` rounds of `f` equal `r % k` rounds of `f`. -/
theorem feistelNetwork_replicate_mod {k : ℕ} {f : G → G}
    (hperiod : feistelNetwork (List.replicate k f) = Equiv.refl (G × G)) (r : ℕ) :
    feistelNetwork (List.replicate r f) = feistelNetwork (List.replicate (r % k) f) := by
  have hmul (m : ℕ) : feistelNetwork (List.replicate (k * m) f) = Equiv.refl (G × G) := by
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.mul_succ, feistelNetwork_replicate_add, ih, hperiod]; rfl
  conv_lhs => rw [← Nat.div_add_mod r k]
  rw [feistelNetwork_replicate_add, hmul (r / k)]
  rfl

/-- A single Feistel round with the identically zero function `0 : G → G` is
`Equiv.prodComm G G`. -/
@[simp] theorem feistelRoundEquiv_zero :
    feistelRoundEquiv (0 : G → G) = Equiv.prodComm G G := by ext ⟨l, r⟩ <;> simp

/-- Two Feistel rounds with the zero round function `0 : G → G` compose to the identity. -/
@[simp] theorem feistelNetwork_replicate_two_zero :
    feistelNetwork (List.replicate 2 (0 : G → G)) = Equiv.refl (G × G) := by
  ext ⟨l, r⟩ <;> simp [List.replicate]

/-- **Period-2 law for zero Feistel rounds** ([KatzLindell2020], Exercise 7.10(a)):
running `r` Feistel rounds with the identically zero round function `0 : G → G` acts as the
identity when `r` is even and swaps the two halves `(l, r) ↦ (r, l)` when `r` is odd. -/
theorem feistelNetwork_replicate_zero (r : ℕ) (p : G × G) :
    feistelNetwork (List.replicate r (0 : G → G)) p =
      if r % 2 = 0 then p else p.swap := by
  rw [feistelNetwork_replicate_mod feistelNetwork_replicate_two_zero r]
  rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rcases p with ⟨l, r'⟩; simp [List.replicate]

private theorem add_self_cancel_left_of_neg_eq_self (hneg : ∀ a : G, -a = a) (a b : G) :
    b + (a + b) = a := by
  calc b + (a + b) = -(a + b) + -b := (hneg _).symm.trans (neg_add_rev b (a + b))
    _ = a := by rw [hneg (a + b), add_neg_cancel_right]

/-- Over any group of exponent two (`∀ a : G, -a = a`), three Feistel rounds with the identity
round function `id : G → G` compose to the identity permutation on `G × G`
([KatzLindell2020], Exercise 7.10(b)). -/
theorem feistelNetwork_replicate_three_id (hneg : ∀ a : G, -a = a) :
    feistelNetwork (List.replicate 3 (id : G → G)) = Equiv.refl (G × G) := by
  ext ⟨l, r⟩ <;>
    simp [List.replicate, feistelRound, add_self_cancel_left_of_neg_eq_self hneg, add_assoc]

/-- **Period-3 law for identity Feistel rounds** ([KatzLindell2020], Exercise 7.10(b)):
over any group of exponent two (`∀ a : G, -a = a`, such as `BitString n`), running `r` Feistel
rounds with the identity round function `id : G → G` has period `3`:
- `r % 3 = 0`: `(l, r') ↦ (l, r')`,
- `r % 3 = 1`: `(l, r') ↦ (r', l + r')`,
- `r % 3 = 2`: `(l, r') ↦ (l + r', l)`. -/
theorem feistelNetwork_replicate_id (hneg : ∀ a : G, -a = a) (r : ℕ) (p : G × G) :
    feistelNetwork (List.replicate r (id : G → G)) p =
      if r % 3 = 0 then p
      else if r % 3 = 1 then (p.2, p.1 + p.2)
      else (p.1 + p.2, p.1) := by
  rw [feistelNetwork_replicate_mod (feistelNetwork_replicate_three_id hneg) r]
  have hmod : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases p with ⟨l, r'⟩
  rcases hmod with h | h | h <;>
    simp [h, List.replicate, feistelRound, add_self_cancel_left_of_neg_eq_self hneg]

end Periodicity

/-! ### Extension-cache fiber bounds and explicit Feistel distinguishers -/

section Distinguishers

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private theorem injective_pair {x y : α} (hxy : x ≠ y) : Function.Injective ![x, y] := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

omit [Fintype α] [DecidableEq α] in
private theorem injective_triple {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem cast_descFactorial_three {n : ℕ} (hn : 2 ≤ n) :
    ((n.descFactorial 3 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub hn]
  ring

private theorem card_filter_perm_div_factorial_le {k : ℕ}
    (xs : Fin k → α) (hxs : Function.Injective xs) (ys : Fin k → α) :
    ((Finset.univ.filter fun π : Equiv.Perm α => ∀ i, π (xs i) = ys i).card : ℝ) /
      (Fintype.card α).factorial ≤ ((Fintype.card α).descFactorial k : ℝ)⁻¹ := by
  have hk : k ≤ Fintype.card α := by simpa using Fintype.card_le_of_injective xs hxs
  have hdesc : (0 : ℝ) < (Fintype.card α).descFactorial k :=
    Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hk)
  have hfac : (0 : ℝ) < (Fintype.card α).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ hfac, inv_mul_eq_div, le_div_iff₀ hdesc, ← RandomPermutation.extPerms_ofFn_eq]
  exact_mod_cast RandomPermutation.card_extPerms_ofFn_mul_descFactorial_le ⟨xs, hxs⟩ ys

private abbrev permBiUnion {β : Type*} (S : Finset β) {k : ℕ}
    (xs : β → Fin k → α) (ys : β → Fin k → α) : Finset (Equiv.Perm α) :=
  S.biUnion fun i => Finset.univ.filter fun π : Equiv.Perm α => ∀ j, π (xs i j) = ys i j

private theorem card_biUnion_perm_div_le {β : Type*} (S : Finset β) {k : ℕ}
    (xs : β → Fin k → α) (hxs : ∀ i ∈ S, Function.Injective (xs i)) (ys : β → Fin k → α) :
    ((permBiUnion S xs ys).card : ℝ) / (Fintype.card α).factorial ≤
      (S.card : ℝ) / ((Fintype.card α).descFactorial k : ℝ) := by
  refine (div_le_div_of_nonneg_right (Nat.cast_le.mpr Finset.card_biUnion_le)
    (Nat.cast_nonneg _)).trans ?_
  rw [Nat.cast_sum, Finset.sum_div]
  refine (Finset.sum_le_sum fun i hi =>
    card_filter_perm_div_factorial_le (xs i) (hxs i hi) (ys i)).trans_eq ?_
  simp [div_eq_mul_inv]

private theorem card_erase_erase {x y : α} (hxy : x ≠ y) :
    (((Finset.univ.erase x).erase y).card : ℝ) = (Fintype.card α : ℝ) - 2 := by
  have h2 : 2 ≤ Fintype.card α := Finset.card_pair hxy ▸ Finset.card_le_univ ({x, y} : Finset α)
  rw [Finset.card_erase_of_mem (by simp [Ne.symm hxy]),
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
    Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

private theorem perm_decide_toReal_le_of_subset {P : Equiv.Perm α → Prop} [DecidablePred P]
    {E : Finset (Equiv.Perm α)} (hcover : ∀ π, P π → π ∈ E) {b : ℝ}
    (hb : (E.card : ℝ) / (Fintype.card α).factorial ≤ b) :
    (((PMF.uniformOfFintype (Equiv.Perm α)).bind fun π => PMF.pure (decide (P π))) true).toReal ≤
      b := by
  rw [Cslib.Probability.PMF.bind_pure_decide_apply_true,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_perm]
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr
    (Finset.card_le_card fun π hπ => hcover π (Finset.mem_filter.mp hπ).2))
    (Nat.cast_nonneg _)).trans hb

private theorem perm_decide_toReal_le_biUnion {β : Type*} {P : Equiv.Perm α → Prop}
    [DecidablePred P] (S : Finset β) {k : ℕ}
    (xs : β → Fin k → α) (hxs : ∀ i ∈ S, Function.Injective (xs i)) (ys : β → Fin k → α)
    (hcover : ∀ π, P π → ∃ i ∈ S, ∀ j, π (xs i j) = ys i j) :
    (((PMF.uniformOfFintype (Equiv.Perm α)).bind fun π => PMF.pure (decide (P π))) true).toReal ≤
      (S.card : ℝ) / ((Fintype.card α).descFactorial k : ℝ) :=
  perm_decide_toReal_le_of_subset
    (fun π hπ => by
      simpa only [permBiUnion, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and] using hcover π hπ)
    (card_biUnion_perm_div_le S xs hxs ys)

private theorem perm_decide_toReal_le_biUnion_union {β γ : Type*}
    {P : Equiv.Perm α → Prop} [DecidablePred P]
    (S₁ : Finset β) {k₁ : ℕ} (xs₁ : β → Fin k₁ → α)
    (hxs₁ : ∀ i ∈ S₁, Function.Injective (xs₁ i)) (ys₁ : β → Fin k₁ → α)
    (S₂ : Finset γ) {k₂ : ℕ} (xs₂ : γ → Fin k₂ → α)
    (hxs₂ : ∀ i ∈ S₂, Function.Injective (xs₂ i)) (ys₂ : γ → Fin k₂ → α)
    (hcover : ∀ π, P π →
      (∃ i ∈ S₁, ∀ j, π (xs₁ i j) = ys₁ i j) ∨ (∃ i ∈ S₂, ∀ j, π (xs₂ i j) = ys₂ i j)) :
    (((PMF.uniformOfFintype (Equiv.Perm α)).bind fun π => PMF.pure (decide (P π))) true).toReal ≤
      (S₁.card : ℝ) / ((Fintype.card α).descFactorial k₁ : ℝ) +
        (S₂.card : ℝ) / ((Fintype.card α).descFactorial k₂ : ℝ) := by
  refine perm_decide_toReal_le_of_subset (E := permBiUnion S₁ xs₁ ys₁ ∪ permBiUnion S₂ xs₂ ys₂)
    (fun π hπ => by
      simpa only [permBiUnion, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and] using hcover π hπ) ?_
  refine (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_union_le _ _))
    (Nat.cast_nonneg _)).trans ?_
  rw [Nat.cast_add, add_div]
  exact add_le_add (card_biUnion_perm_div_le S₁ xs₁ hxs₁ ys₁)
    (card_biUnion_perm_div_le S₂ xs₂ hxs₂ ys₂)

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-! #### 1-round Feistel CPA distinguisher -/

/-- **The 1-query chosen-plaintext distinguisher against 1-round Feistel** ([KatzLindell2020],
Section 8.6): query `(l₀, r₀)` to obtain `(v, w)` and accept iff `v = r₀`. -/
def feistel1CPAAttack (l₀ r₀ : G) :
    OracleComp (fun _ : G × G => G × G) Bool := do
  let vw ← OracleComp.query (spec := fun _ : G × G => G × G) (l₀, r₀)
  return decide (vw.1 = r₀)

omit [AddGroup G] [Fintype G] in
/-- `feistel1CPAAttack` makes at most 1 oracle query. -/
theorem isQueryBounded_feistel1CPAAttack (l₀ r₀ : G) :
    OracleComp.IsQueryBounded (feistel1CPAAttack l₀ r₀) 1 := by
  refine ((OracleComp.IsCostBounded.query (l₀, r₀)).bind fun vw =>
    OracleComp.IsCostBounded.pure _ 0).mono (by omega)

omit [Fintype G] in
/-- **Every 1-round Feistel network `feistelRoundEquiv f` is accepted with probability `1` by
`feistel1CPAAttack l₀ r₀`** ([KatzLindell2020], Section 8.6), for any round function
`f : G → G`. -/
theorem eval_feistelRoundEquiv_feistel1CPAAttack (f : G → G) (l₀ r₀ : G) :
    OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
      (feistel1CPAAttack l₀ r₀) = PMF.pure true := by
  simp [feistel1CPAAttack]

omit [AddGroup G] in
/-- Against `randomFunctionGame`, `feistel1CPAAttack l₀ r₀` accepts with probability `|G|⁻¹`
(original bound). -/
theorem randomFunctionGame_feistel1CPAAttack_true [Nonempty G] (l₀ r₀ : G) :
    randomFunctionGame (feistel1CPAAttack l₀ r₀) true = (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hgame :
      randomFunctionGame (feistel1CPAAttack l₀ r₀) =
        (PMF.uniformOfFintype G).map (fun v => decide (v = r₀)) := by
    calc randomFunctionGame (feistel1CPAAttack l₀ r₀)
        = (((PMF.uniformOfFintype (G × G → G × G)).map (fun table => table (l₀, r₀))).map
            Prod.fst).map (fun v => decide (v = r₀)) := by
          simp [randomFunctionGame, feistel1CPAAttack, PMF.map_comp, Function.comp_def]; rfl
      _ = (PMF.uniformOfFintype G).map (fun v => decide (v = r₀)) := by
          rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval,
            Cslib.Probability.PMF.uniformOfFintype_prod_map_fst]
  rw [hgame, Cslib.Probability.PMF.map_decide_eq_apply_true, PMF.uniformOfFintype_apply]

/-- `feistel1CPAAttack l₀ r₀` distinguishes any 1-round Feistel network `feistelRoundEquiv f` from
`randomFunctionGame` with exact advantage `1 - |G|⁻¹` (original bound). -/
theorem advantage_feistel1CPAAttack_randomFunctionGame [Nonempty G] (f : G → G) (l₀ r₀ : G) :
    (Game.advantage
      (OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
        (feistel1CPAAttack l₀ r₀))
      (randomFunctionGame (feistel1CPAAttack l₀ r₀)) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [eval_feistelRoundEquiv_feistel1CPAAttack, Game.coe_advantage_pure_true_left,
    randomFunctionGame_feistel1CPAAttack_true, ENNReal.toReal_inv, ENNReal.toReal_natCast]

omit [AddGroup G] in
/-- Against `idealPermGame`, `feistel1CPAAttack l₀ r₀` accepts with probability at most `|G|⁻¹`
(original bound). -/
theorem idealPermGame_feistel1CPAAttack_true_le [Nonempty G] (l₀ r₀ : G) :
    (idealPermGame (feistel1CPAAttack l₀ r₀) true).toReal ≤ (Fintype.card G : ℝ)⁻¹ := by
  simp only [interp_norm, pmf_norm, idealPermGame, feistel1CPAAttack]
  refine (perm_decide_toReal_le_biUnion (Finset.univ : Finset G) (k := 1)
    (fun _ => ![(l₀, r₀)]) (fun _ _ => Function.injective_of_subsingleton _)
    (fun w => ![(r₀, w)])
    fun π hπ => ⟨(π (l₀, r₀)).2, Finset.mem_univ _,
      Fin.forall_fin_one.mpr (Prod.ext hπ rfl)⟩).trans_eq ?_
  simp [Finset.card_univ, Fintype.card_prod]

/-- `feistel1CPAAttack l₀ r₀` distinguishes any 1-round Feistel network `feistelRoundEquiv f` from
`idealPermGame` with advantage at least `1 - |G|⁻¹` (original bound). -/
theorem le_advantage_feistel1CPAAttack_idealPermGame [Nonempty G] (f : G → G) (l₀ r₀ : G) :
    1 - (Fintype.card G : ℝ)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
          (feistel1CPAAttack l₀ r₀))
        (idealPermGame (feistel1CPAAttack l₀ r₀)) : ℝ) := by
  rw [eval_feistelRoundEquiv_feistel1CPAAttack, Game.coe_advantage_pure_true_left]
  exact sub_le_sub_left (idealPermGame_feistel1CPAAttack_true_le l₀ r₀) 1

/-! #### 2-round Feistel CPA distinguisher -/

/-- **The 2-query chosen-plaintext distinguisher against 2-round Feistel** ([KatzLindell2020],
Exercise 8.16):
query `(l₀, r₀)` to obtain `(v₀, w₀)`, query `(l₁, r₀)` to obtain `(v₁, w₁)`, and accept iff
`v₀ - v₁ = l₀ - l₁`. -/
def feistel2CPAAttack (l₀ l₁ r₀ : G) :
    OracleComp (fun _ : G × G => G × G) Bool := do
  let vw₀ ← OracleComp.query (spec := fun _ : G × G => G × G) (l₀, r₀)
  let vw₁ ← OracleComp.query (spec := fun _ : G × G => G × G) (l₁, r₀)
  return decide (vw₀.1 - vw₁.1 = l₀ - l₁)

omit [Fintype G] in
/-- `feistel2CPAAttack` makes at most 2 oracle queries. -/
theorem isQueryBounded_feistel2CPAAttack (l₀ l₁ r₀ : G) :
    OracleComp.IsQueryBounded (feistel2CPAAttack l₀ l₁ r₀) 2 := by
  refine ((OracleComp.IsCostBounded.query (l₀, r₀)).bind fun vw₀ =>
    ((OracleComp.IsCostBounded.query (l₁, r₀)).bind fun vw₁ =>
      OracleComp.IsCostBounded.pure _ 0)).mono (by omega)

omit [Fintype G] in
/-- **Every 2-round Feistel network `feistelNetwork [f₁, f₂]` is accepted with probability `1` by
`feistel2CPAAttack l₀ l₁ r₀`** ([KatzLindell2020], Exercise 8.16), for any round functions
`f₁, f₂ : G → G` and any `l₀, l₁, r₀ : G`. -/
theorem eval_feistel2_feistel2CPAAttack (f₁ f₂ : G → G) (l₀ l₁ r₀ : G) :
    OracleComp.interpret (fun p => PMF.pure (feistelNetwork [f₁, f₂] p))
      (feistel2CPAAttack l₀ l₁ r₀) = PMF.pure true := by
  simp only [interp_norm, pmf_norm, feistel2CPAAttack, feistelNetwork_cons, feistelNetwork_nil,
    Equiv.trans_apply, feistelRoundEquiv_apply, feistelRound, Equiv.refl_apply,
    add_sub_add_right_eq_sub, decide_true]

/-- Against `idealPermGame`, when `l₀ ≠ l₁` and `2 ≤ Fintype.card G`, `feistel2CPAAttack l₀ l₁ r₀`
accepts with probability at most `|G| / (|G| ^ 2 - 1)` (original bound). -/
theorem idealPermGame_feistel2CPAAttack_true_le [Nonempty G] {l₀ l₁ : G} (r₀ : G)
    (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    (idealPermGame (feistel2CPAAttack l₀ l₁ r₀) true).toReal ≤
      (Fintype.card G : ℝ) / ((Fintype.card G : ℝ) ^ 2 - 1) := by
  simp only [interp_norm, pmf_norm, idealPermGame, feistel2CPAAttack]
  refine (perm_decide_toReal_le_biUnion (Finset.univ : Finset ((G × G) × G)) (k := 2)
    (fun _ => ![(l₀, r₀), (l₁, r₀)]) (fun _ _ => injective_pair fun h => h01 (congrArg Prod.fst h))
    (fun aw => ![aw.1, (-(l₀ - l₁) + aw.1.1, aw.2)]) fun π hπ =>
      ⟨(π (l₀, r₀), (π (l₁, r₀)).2), Finset.mem_univ _, Fin.forall_fin_two.mpr
        ⟨rfl, Prod.ext (by dsimp; rw [← hπ, neg_sub, sub_add_cancel]) rfl⟩⟩).trans_eq ?_
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  have hN0 : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsq1 : (Fintype.card G : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [Finset.card_univ, Nat.cast_descFactorial_two ℝ _]
  simp only [Fintype.card_prod, Nat.cast_mul]; field_simp

/-- When `l₀ ≠ l₁` and `2 ≤ Fintype.card G`, `feistel2CPAAttack l₀ l₁ r₀` distinguishes any
2-round Feistel network `feistelNetwork [f₁, f₂]` from `idealPermGame` with advantage at least
`1 - |G| / (|G| ^ 2 - 1)` (`≥ 1 / 3`; attack from [KatzLindell2020], Exercise 8.16, original
bound). -/
theorem le_advantage_feistel2CPAAttack_idealPermGame [Nonempty G] (f₁ f₂ : G → G)
    {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    1 - (Fintype.card G : ℝ) / ((Fintype.card G : ℝ) ^ 2 - 1) ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistelNetwork [f₁, f₂] p))
          (feistel2CPAAttack l₀ l₁ r₀))
        (idealPermGame (feistel2CPAAttack l₀ l₁ r₀)) : ℝ) := by
  rw [eval_feistel2_feistel2CPAAttack, Game.coe_advantage_pure_true_left]
  exact sub_le_sub_left (idealPermGame_feistel2CPAAttack_true_le r₀ h01 hG) 1

/-! #### 3-round repeated-key (`[f, f, f]`) Feistel CPA distinguisher -/

/-- **The 2-query chosen-plaintext distinguisher against 3-round Feistel with a repeated round
function `[f, f, f]`** ([KatzLindell2020], Exercise 8.18):
query `(x, x)` to obtain `vw`, query `vw.swap = (vw.2, vw.1)` to obtain `lr`, and accept iff
`lr = (x, x)`. -/
def feistel3RepeatedKeyCPAAttack (x : G) :
    OracleComp (fun _ : G × G => G × G) Bool := do
  let vw ← OracleComp.query (spec := fun _ : G × G => G × G) (x, x)
  let lr ← OracleComp.query (spec := fun _ : G × G => G × G) (vw.2, vw.1)
  return decide (lr = (x, x))

omit [AddGroup G] [Fintype G] in
/-- `feistel3RepeatedKeyCPAAttack` makes at most 2 oracle queries. -/
theorem isQueryBounded_feistel3RepeatedKeyCPAAttack (x : G) :
    OracleComp.IsQueryBounded (feistel3RepeatedKeyCPAAttack x) 2 := by
  refine ((OracleComp.IsCostBounded.query (x, x)).bind fun vw =>
    ((OracleComp.IsCostBounded.query (vw.2, vw.1)).bind fun lr =>
      OracleComp.IsCostBounded.pure _ 0)).mono (by omega)

omit [Fintype G] in
/-- **Over any group of exponent two (`∀ a : G, -a = a`), every repeated-key 3-round Feistel
network `feistel3 f f f` is accepted with probability `1` by `feistel3RepeatedKeyCPAAttack x`**
([KatzLindell2020], Exercise 8.18). -/
theorem eval_feistel3_repeated_feistel3RepeatedKeyCPAAttack
    (hneg : ∀ a : G, -a = a) (f : G → G) (x : G) :
    OracleComp.interpret (fun p => PMF.pure (feistel3 f f f p))
      (feistel3RepeatedKeyCPAAttack x) = PMF.pure true := by
  have happ := Equiv.congr_fun
    (prodComm_trans_feistelNetwork_reverse_trans_prodComm hneg [f, f, f]) (feistel3 f f f (x, x))
  have h : feistel3 f f f ((feistel3 f f f (x, x)).2, (feistel3 f f f (x, x)).1) = (x, x) :=
    Prod.swap_injective (happ.trans (Equiv.symm_apply_apply (feistel3 f f f) (x, x)))
  simp [feistel3RepeatedKeyCPAAttack, h]

omit [AddGroup G] in
/-- Against `idealPermGame`, when `2 ≤ Fintype.card G`, `feistel3RepeatedKeyCPAAttack x` accepts
with probability at most `2 / |G| ^ 2` (`≤ 1 / 2`; original bound). -/
theorem idealPermGame_feistel3RepeatedKeyCPAAttack_true_le [Nonempty G] (x : G)
    (hG : 2 ≤ Fintype.card G) :
    (idealPermGame (feistel3RepeatedKeyCPAAttack x) true).toReal ≤
      2 / (Fintype.card G : ℝ) ^ 2 := by
  simp only [interp_norm, pmf_norm, idealPermGame, feistel3RepeatedKeyCPAAttack]
  set p₀ : G × G := (x, x)
  refine (perm_decide_toReal_le_biUnion_union
    ({()} : Finset Unit) (k₁ := 1)
    (fun _ => ![p₀]) (fun _ _ => Function.injective_of_subsingleton _) (fun _ => ![p₀])
    (Finset.univ.erase p₀) (k₂ := 2)
    (fun a => ![p₀, a.swap])
    (fun a ha => injective_pair fun h => (Finset.mem_erase.mp ha).1 (Prod.swap_injective h.symm))
    (fun a => ![a, p₀])
    fun π hπ => by
      by_cases h : π p₀ = p₀
      · exact Or.inl ⟨(), Finset.mem_singleton_self _, Fin.forall_fin_one.mpr h⟩
      · exact Or.inr ⟨π p₀, Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩,
          Fin.forall_fin_two.mpr ⟨rfl, hπ⟩⟩).trans_eq ?_
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  have hN0 : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hM1r : (Fintype.card G : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [Finset.card_singleton, Nat.descFactorial_one, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Nat.cast_descFactorial_two ℝ _, Nat.cast_sub Fintype.card_pos]
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_one]
  field_simp
  ring

/-- Over any group of exponent two (`∀ a : G, -a = a`) with `2 ≤ Fintype.card G`,
`feistel3RepeatedKeyCPAAttack x` distinguishes any repeated-key 3-round Feistel network
`feistel3 f f f` from `idealPermGame` with advantage at least `1 - 2 / |G| ^ 2` (`≥ 1 / 2`; attack
from [KatzLindell2020], Exercise 8.18, original bound). -/
theorem le_advantage_feistel3RepeatedKeyCPAAttack_idealPermGame [Nonempty G]
    (hneg : ∀ a : G, -a = a) (f : G → G) (x : G) (hG : 2 ≤ Fintype.card G) :
    1 - 2 / (Fintype.card G : ℝ) ^ 2 ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistel3 f f f p))
          (feistel3RepeatedKeyCPAAttack x))
        (idealPermGame (feistel3RepeatedKeyCPAAttack x)) : ℝ) := by
  rw [eval_feistel3_repeated_feistel3RepeatedKeyCPAAttack hneg f x,
    Game.coe_advantage_pure_true_left]
  exact sub_le_sub_left (idealPermGame_feistel3RepeatedKeyCPAAttack_true_le x hG) 1

/-! #### Sharper permutation-fiber bound for the 3-round CCA distinguisher -/

/-- **Sharper permutation-fiber bound for `feistel3CCAAttack`** (attack from [KatzLindell2020],
Exercise 8.17; original bound): when `l₀ ≠ l₁` and `2 ≤ Fintype.card G`, the true bidirectional
random-permutation game `idealStrongGame` accepts `feistel3CCAAttack l₀ l₁ r₀` with probability at
most `(|G| + 1) / (|G| ^ 2 - 1) = (|G| - 1)⁻¹` (`≤ 1 / 2` for `|G| ≥ 3`). -/
theorem idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one [Nonempty G]
    {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true).toReal ≤
      ((Fintype.card G : ℝ) - 1)⁻¹ := by
  simp only [interp_norm, pmf_norm, idealStrongGame, feistel3CCAAttack, feistelStrongOracle]
  set x : G × G := (l₀, r₀)
  set y : G × G := (l₁, r₀)
  have hxy : x ≠ y := fun h => h01 (congrArg Prod.fst h)
  let q : G × G → G × G := fun a => (a.1, (l₁ - l₀) + a.2)
  have hq (a) : q a ≠ a := fun h => h01 (sub_eq_zero.mp
    (add_right_cancel ((congrArg Prod.snd h).trans (zero_add a.2).symm))).symm
  let S : Finset ((G × G) × ((G × G) × G)) :=
    ((Finset.univ.erase x).erase y) ×ˢ (Finset.univ ×ˢ Finset.univ)
  refine (perm_decide_toReal_le_biUnion_union
    (Finset.univ : Finset (G × G)) (k₁ := 2)
    (fun _ => ![x, y]) (fun _ _ => injective_pair hxy) (fun a => ![a, q a])
    S (k₂ := 3)
    (fun t => ![x, t.1, y])
    (fun t ht => by
      simp only [S, Finset.mem_product, Finset.mem_erase] at ht
      exact injective_triple (Ne.symm ht.1.2.1) hxy ht.1.1)
    (fun t => ![t.2.1, q t.2.1, (r₀ - (-t.2.1.1 + t.1.2), t.2.2)])
    fun π hπ => by
      set c := π.symm (q (π x))
      have hπc : π c = q (π x) := by simp [c]
      by_cases hcy : c = y
      · exact Or.inl ⟨π x, Finset.mem_univ _, Fin.forall_fin_two.mpr ⟨rfl, hcy ▸ hπc⟩⟩
      · refine Or.inr ⟨(c, π x, (π y).2), ?_, Fin.forall_fin_succ.mpr ⟨rfl,
          Fin.forall_fin_two.mpr ⟨hπc, Prod.ext
            (by simpa [neg_sub] using congrArg Neg.neg (eq_sub_of_add_eq hπ.symm)) rfl⟩⟩⟩
        simp only [S, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨hcy, fun h : c = x => hq (π x) (by rw [← hπc, h])⟩).trans_eq ?_
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  have hN0 : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN1 : (Fintype.card G : ℝ) - 1 ≠ 0 := by linarith
  have hM1 : (Fintype.card G : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hM2r : (Fintype.card G : ℝ) ^ 2 - 2 ≠ 0 := by nlinarith
  rw [Finset.card_univ, Nat.cast_descFactorial_two ℝ _,
    cast_descFactorial_three (by rw [Fintype.card_prod]; nlinarith)]
  simp only [S, Finset.card_product, Finset.card_univ, Nat.cast_mul, card_erase_erase hxy,
    Fintype.card_prod]
  field_simp; ring

/-- **Sharper chosen-ciphertext advantage lower bound for `feistel3CCAAttack`** (attack from
[KatzLindell2020], Exercise 8.17; original bound): when `l₀ ≠ l₁` and `2 ≤ Fintype.card G`,
`feistel3CCAAttack l₀ l₁ r₀` distinguishes any 3-round Feistel network `feistel3 f₁ f₂ f₃` from
`idealStrongGame` with advantage at least `1 - (|G| - 1)⁻¹` (`≥ 1 / 2` for `|G| ≥ 3`). -/
theorem le_advantage_feistel3CCAAttack_idealStrongGame_of_two_le_card [Nonempty G]
    (f₁ f₂ f₃ : G → G) {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    1 - ((Fintype.card G : ℝ) - 1)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack l₀ l₁ r₀))
        (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  rw [eval_feistel3_feistel3CCAAttack, Game.coe_advantage_pure_true_left]
  exact sub_le_sub_left (idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one r₀ h01 hG) 1

end Distinguishers

end Cslib.Crypto.LubyRackoff
