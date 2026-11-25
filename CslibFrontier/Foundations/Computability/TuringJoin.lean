/-
Copyright (c) 2026 Tanner Duve, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Matthew Doty
-/

module
-- upstream: candidate (Mathlib; copy of Mathlib PR 37062 @1bac7307b0, delete when it lands)

public import CslibFrontier.Init
public import Mathlib.Computability.TuringDegree

/-!
# The Turing join and the join semilattice of Turing degrees

The *join* `f ⊕ g` of two partial functions `f g : ℕ →. ℕ` codes their disjoint union by
parity: on `2 * n` it returns `f n` doubled, and on `2 * n + 1` it returns `g n` doubled plus one.
Each of `f` and `g` is Turing reducible to `f ⊕ g`, and `f ⊕ g` is reducible to every `h` to
which both `f` and `g` are reducible. So the join is a least upper bound for `≤ᵀ`, and it makes
`TuringDegree` a join semilattice [KleenePost1954], [Soare1987].

## Main definitions

* `Partrec.join`, notation `f ⊕ g` (scoped in `Partrec`): the join of two partial functions.
* `TuringDegree.sup`: the supremum of Turing degrees, induced by the join.

## Main results

* `left_le_join`, `right_le_join`: `f ≤ᵀ f ⊕ g` and `g ≤ᵀ f ⊕ g`.
* `join_le`: if `f ≤ᵀ h` and `g ≤ᵀ h`, then `f ⊕ g ≤ᵀ h`.
* `TuringDegree.join_mono`, `TuringDegree.join_congr`: the join respects `≤ᵀ` and `≡ᵀ`.
* `TuringDegree.instSemilatticeSup`: Turing degrees form a join semilattice, with `⊔` given on
  representatives by the join (`TuringDegree.sup_def`).

## Implementation notes

This file is a copy of the additions that the open Mathlib PR 37062 by Tanner Duve,
<https://github.com/leanprover-community/mathlib4/pull/37062> ("Turing join and semilattice
structure on Turing degrees", at head `1bac7307b0`), makes to `Mathlib/Computability/Partrec.lean`,
`Mathlib/Computability/RecursiveIn.lean` and `Mathlib/Computability/TuringDegree.lean`. It keeps
that PR's declaration names and statements, so that clients switch to Mathlib by changing their
imports. **Delete this file when Mathlib PR 37062, or a successor providing the join, lands in the
pinned Mathlib**, and point its importers at Mathlib.

The copy differs from the PR in three places, each marked `-- vendored:` below. The PR proves
that `Nat.RecursiveIn` is closed under conditionals through an equality test and unbounded search
(`Partrec.kronecker`, `Nat.RecursiveIn.cond'`); here the join is instead the sum of two guarded
branches, each guarded by the PR's `Nat.RecursiveIn.cond_const`, so the equality test is not
copied. The PR's `Nat.RecursiveIn.of_primrec` and `Nat.RecursiveIn.of_partrec` restate the pinned
`Nat.Primrec.recursiveIn` and `Nat.Partrec.recursiveIn`, which are used instead. On the pinned
Mathlib, `f ≤ᵀ g` unfolds to the encoded `RecursiveIn {g} f` rather than `Nat.RecursiveIn {g} f`,
and `RecursiveIn.iff_nat` converts between them.

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

namespace Partrec

/-- The join of partial functions `f` and `g`, coding a disjoint union by parity. -/
@[expose] def join (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n =>
    cond n.bodd ((g n.div2).map (fun y => 2 * y + 1)) ((f n.div2).map (fun y => 2 * y))

@[inherit_doc]
scoped infix:50 " ⊕ " => Partrec.join

namespace Join

@[simp]
lemma even (f g : ℕ →. ℕ) (n : ℕ) :
    Partrec.join f g (2 * n) = (f n).map (fun y => 2 * y) := by
  simp [Partrec.join]

@[simp]
lemma odd (f g : ℕ →. ℕ) (n : ℕ) :
    Partrec.join f g (2 * n + 1) = (g n).map (fun y => 2 * y + 1) := by
  simp [Partrec.join, Nat.bodd_mul]

end Join

end Partrec

open scoped Partrec

-- vendored: under the module system `ℕ →. ℕ` does not unfold to `ℕ → Part ℕ` for `simp`, so
-- binds into partial functions are eta-expanded before Mathlib's `Part.bind` lemmas apply.
private theorem bind_pfun (x : Part ℕ) (f : ℕ →. ℕ) : x >>= f = x.bind fun y => f y := rfl

namespace Nat.RecursiveIn

variable {O : Set (ℕ →. ℕ)}

/-- Every function is recursive in the singleton oracle set containing it. -/
theorem oracle_self (f : ℕ →. ℕ) : Nat.RecursiveIn {f} f :=
  .oracle f rfl

/-- The first function in a two-element oracle set is recursive in that set. -/
theorem oracle_pair_left (f g : ℕ →. ℕ) : Nat.RecursiveIn ({f, g} : Set _) f :=
  .oracle f <| .inl rfl

/-- The second function in a two-element oracle set is recursive in that set. -/
theorem oracle_pair_right (f g : ℕ →. ℕ) : Nat.RecursiveIn ({f, g} : Set _) g :=
  .oracle g <| .inr rfl

-- vendored: the PR's `of_primrec` is the pinned `Nat.Primrec.recursiveIn`, used here.
theorem div2 :
    Nat.RecursiveIn O (fun n => Nat.div2 n : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn (Primrec.nat_iff.1 Primrec.nat_div2)

theorem double :
    Nat.RecursiveIn O (fun n => 2 * n : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn (Primrec.nat_iff.1 Primrec.nat_double)

theorem double_add_one :
    Nat.RecursiveIn O (fun n => 2 * n + 1 : ℕ → ℕ) :=
  Nat.Primrec.recursiveIn (Primrec.nat_iff.1 Primrec.nat_double_succ)

theorem comp_at_even {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O (fun n => h (2 * n)) :=
  (hh.comp .double).of_eq fun _ => Part.bind_some _ _

theorem comp_at_odd {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O (fun n => h (2 * n + 1)) :=
  (hh.comp .double_add_one).of_eq fun _ => Part.bind_some _ _

theorem encode_even {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O (fun n =>
      (Nat.div2 n : ℕ) >>= h >>= fun y => (2 * y : ℕ)) :=
  (Nat.RecursiveIn.double.comp (hh.comp .div2)).of_eq
    fun _ => by congr

theorem encode_odd {h : ℕ →. ℕ}
    (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O (fun n =>
      (Nat.div2 n : ℕ) >>= h >>= fun y => (2 * y + 1 : ℕ)) :=
  (Nat.RecursiveIn.double_add_one.comp (hh.comp .div2)).of_eq
    fun _ => by congr

/-- Conditional with a computable guard and constant fallback. -/
theorem cond_const {c : ℕ → Bool} {f : ℕ →. ℕ}
    (hc : Computable c) (hf : Nat.RecursiveIn O f) (k : ℕ) :
    Nat.RecursiveIn O
      (fun n => bif c n then f n else Part.some k) := by
  -- vendored: `Nat.Primrec.recursiveIn` and `Nat.Partrec.recursiveIn` for the PR's `of_primrec`
  -- and `of_partrec`
  have hid : Nat.RecursiveIn O (fun n => n : ℕ → ℕ) := Nat.Primrec.recursiveIn .id
  have hcode : Nat.RecursiveIn O (fun n => Encodable.encode (c n) : ℕ → ℕ) :=
    Nat.Partrec.recursiveIn (Partrec.nat_iff.1 (Computable.encode.comp hc).partrec)
  refine (comp (prec (Nat.Primrec.recursiveIn (.const k))
    ((comp hf left).of_eq fun _ => by aesop))
    (pair hid hcode)).of_eq fun n => ?_
  cases h : c n <;> simp [Seq.seq, Nat.unpair_pair, bind_pfun] <;> aesop

-- vendored: the PR derives the join from its general conditional `cond'`; here it is the sum of
-- the two branches, each guarded with fallback `0` by `cond_const`.
/-- The join of two functions recursive in `O` is recursive in `O`. -/
private theorem join {f g : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hg : Nat.RecursiveIn O g) :
    Nat.RecursiveIn O (f ⊕ g) := by
  have hadd : Nat.RecursiveIn O (fun n => n.unpair.1 + n.unpair.2 : ℕ → ℕ) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.1
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
  refine (hadd.comp ((cond_const (Primrec.not.comp Primrec.nat_bodd).to_comp hf.encode_even 0).pair
    (cond_const Primrec.nat_bodd.to_comp hg.encode_odd 0))).of_eq fun n => ?_
  cases h : n.bodd <;>
    simp [Partrec.join, h, Seq.seq, bind_pfun, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def]

end Nat.RecursiveIn

open scoped Computability

/-- `f` is Turing reducible to the join `f ⊕ g`. -/
lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) :=
  -- vendored: on the pinned Mathlib `≤ᵀ` is the encoded `RecursiveIn`, hence `iff_nat`
  RecursiveIn.iff_nat.2 <| (Nat.RecursiveIn.div2.comp
    (Nat.RecursiveIn.oracle_self _).comp_at_even).of_eq fun n => by
    simp [bind_pfun, Part.bind_some_eq_map, Part.map_map, Function.comp_def, Part.map_id']

/-- `g` is Turing reducible to the join `f ⊕ g`. -/
lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) :=
  RecursiveIn.iff_nat.2 <| (Nat.RecursiveIn.div2.comp
    (Nat.RecursiveIn.oracle_self _).comp_at_odd).of_eq fun n => by
    simp [bind_pfun, Part.bind_some_eq_map, Part.map_map, Function.comp_def, Part.map_id']

/-- The join is recursive in the pair of oracles `{f, g}`. -/
lemma join_recursiveIn_pair (f g : ℕ →. ℕ) :
    Nat.RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) :=
  (Nat.RecursiveIn.oracle_pair_left f g).join (Nat.RecursiveIn.oracle_pair_right f g)

/-- If `f` and `g` are both reducible to `h`, then their join
is reducible to `h`. -/
lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) :
    (f ⊕ g) ≤ᵀ h :=
  RecursiveIn.iff_nat.2 <| (join_recursiveIn_pair f g).subst fun k hk => by
    rcases Set.mem_insert_iff.mp hk with rfl | hkg
    · exact RecursiveIn.iff_nat.1 hf
    · rw [Set.mem_singleton_iff.mp hkg]; exact RecursiveIn.iff_nat.1 hg

/-- If `f ≤ᵀ f'`, then `f` is reducible to any join with `f'` on the left. -/
theorem TuringReducible.le_join_of_le_left {f f' : ℕ →. ℕ} (hf : f ≤ᵀ f') (g : ℕ →. ℕ) :
    f ≤ᵀ (f' ⊕ g) :=
  hf.trans (left_le_join f' g)

/-- If `g ≤ᵀ g'`, then `g` is reducible to any join with `g'` on the right. -/
theorem TuringReducible.le_join_of_le_right {g g' : ℕ →. ℕ} (hg : g ≤ᵀ g') (f : ℕ →. ℕ) :
    g ≤ᵀ (f ⊕ g') :=
  hg.trans (right_le_join f g')

namespace TuringDegree

/-- The Turing join respects Turing reducibility: if `f ≤ᵀ f'` and `g ≤ᵀ g'`,
then `f ⊕ g ≤ᵀ f' ⊕ g'`. -/
theorem join_mono {f f' g g' : ℕ →. ℕ} (hf : f ≤ᵀ f') (hg : g ≤ᵀ g') :
    (f ⊕ g) ≤ᵀ (f' ⊕ g') :=
  join_le f g (f' ⊕ g') (hf.le_join_of_le_left g') (hg.le_join_of_le_right f')

/-- The Turing join respects Turing equivalence. -/
theorem join_congr {f f' g g' : ℕ →. ℕ} (hf : f ≡ᵀ f') (hg : g ≡ᵀ g') :
    (f ⊕ g) ≡ᵀ (f' ⊕ g') :=
  ⟨join_mono hf.1 hg.1, join_mono hf.2 hg.2⟩

/-- The supremum operation on Turing degrees, induced by the Turing join. -/
@[expose] def sup : TuringDegree → TuringDegree → TuringDegree :=
  Quotient.lift₂
    (fun f g => toAntisymmetrization TuringReducible (f ⊕ g))
    (fun _ _ _ _ hf hg => Quotient.sound (join_congr hf hg))

/-- `sup` agrees with `⊕` on representatives. -/
lemma sup_mk (f g : ℕ →. ℕ) :
    TuringDegree.sup (toAntisymmetrization TuringReducible f)
    (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

instance instSemilatticeSup : SemilatticeSup TuringDegree where
  sup := sup
  le_sup_left a b := by
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    exact left_le_join _ _
  le_sup_right a b := by
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    exact right_le_join _ _
  sup_le {a b c} ha hb := by
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    induction c using Quotient.inductionOn'
    exact join_le _ _ _ ha hb

/-- The sup on Turing degrees agrees with the Turing join on representatives. -/
@[simp]
lemma sup_def (f g : ℕ →. ℕ) :
    (toAntisymmetrization TuringReducible f) ⊔ (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

end TuringDegree
