/-
Copyright (c) 2018 Mario Carneiro, 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Samuel Schlesinger
-/
module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInCode
public import Mathlib.Computability.Primrec.Basic
import CslibFrontier.Foundations.Computability.FunProp

/-!
# Primitive recursive evaluator for oracle computations

This file proves that structural recursion on `Nat.RecursiveIn.Code` (`Code.primrec_recOn'`,
`Code.primrec_recOn`) and the stage-bounded oracle evaluator `Nat.RecursiveIn.Code.evaln`
(`Code.primrec_evaln`) are primitive recursive.

It adapts the strong-recursion table argument of `Mathlib/Computability/PartrecCode.lean`
(Apache 2.0, by Mario Carneiro) from `Nat.Partrec.Code` to `Nat.RecursiveIn.Code`. Relative to
that proof, `Code.primrec_recOn'` adds the `oracle` constructor at Gödel number `4` (shifting the
composite constructors to `n + 5`), and `G` carries the finite oracle prefix `σ : List ℕ` as an
extra parameter of the strong recursion so that the `oracle` branch looks up `σ[n]?`.

## Main results

* `Nat.RecursiveIn.Code.encodeCode_lt_pair`, `Nat.RecursiveIn.Code.encodeCode_lt_comp`,
  `Nat.RecursiveIn.Code.encodeCode_lt_prec`, `Nat.RecursiveIn.Code.encodeCode_lt_rfind'`: code
  encodings of immediate subcodes are strictly smaller than those of the composite code.
* `Nat.RecursiveIn.Code.primrec_recOn'`, `Nat.RecursiveIn.Code.primrec_recOn`: structural
  recursion on `Nat.RecursiveIn.Code` is primitive recursive.
* `Nat.RecursiveIn.Code.primrec_evaln`: stage-bounded oracle evaluation `Code.evaln` is primitive
  recursive in `(σ, (k, c), n)`.

## References

* Adapted from `Mathlib/Computability/PartrecCode.lean` (Apache 2.0, by Mario Carneiro).
* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

open Encodable Denumerable
open Primrec
open Nat Nat.RecursiveIn Nat.RecursiveIn.Code

public section

namespace Nat.RecursiveIn.Code

/-- The subcodes of `Code.pair cf cg` have strictly smaller Gödel numbers than `pair cf cg`. -/
theorem encodeCode_lt_pair (cf cg : Code) :
    encodeCode cf < encodeCode (pair cf cg) ∧ encodeCode cg < encodeCode (pair cf cg) := by
  simp only [encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

/-- The subcodes of `Code.comp cf cg` have strictly smaller Gödel numbers than `comp cf cg`. -/
theorem encodeCode_lt_comp (cf cg : Code) :
    encodeCode cf < encodeCode (comp cf cg) ∧ encodeCode cg < encodeCode (comp cf cg) := by
  have : encodeCode (pair cf cg) < encodeCode (comp cf cg) := by simp [encodeCode]
  exact (encodeCode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

/-- The subcodes of `Code.prec cf cg` have strictly smaller Gödel numbers than `prec cf cg`. -/
theorem encodeCode_lt_prec (cf cg : Code) :
    encodeCode cf < encodeCode (prec cf cg) ∧ encodeCode cg < encodeCode (prec cf cg) := by
  have : encodeCode (pair cf cg) < encodeCode (prec cf cg) := by simp [encodeCode]
  exact (encodeCode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

/-- The subcode of `Code.rfind' cf` has a strictly smaller Gödel number than `rfind' cf`. -/
theorem encodeCode_lt_rfind' (cf : Code) : encodeCode cf < encodeCode (rfind' cf) := by
  simp only [encodeCode]
  omega

/-- Structural recursion on `Nat.RecursiveIn.Code` with tupled branch functions is primitive
recursive. Adapted from `Nat.Partrec.Code.primrec_recOn'` with an additional `oracle` branch. -/
theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o)
    {pr : α → Code × Code × σ × σ → σ} (hpr : Primrec₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Primrec₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Primrec₂ pc) {rf : α → Code × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Code.recOn c (z a) (s a) (l a) (r a) (o a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI p1 := p.1; letI p2 := p.2; letI a := p1.1; letI IH := p1.2; letI n := p2.1; letI m := p2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    bif n.bodd then
      (bif n.div2.bodd then (rf a (ofNat Code m, s))
        else (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      else (bif n.div2.bodd then (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        else (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ := by
    have hpr : Primrec fun p : α × Code × Code × σ × σ => pr p.1 p.2 := hpr
    have hco : Primrec fun p : α × Code × Code × σ × σ => co p.1 p.2 := hco
    have hpc : Primrec fun p : α × Code × Code × σ × σ => pc p.1 p.2 := hpc
    have hrf : Primrec fun p : α × Code × σ => rf p.1 p.2 := hrf
    fun_prop
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    n.casesOn (some (o a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G := by
    unfold Primrec₂
    fun_prop
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 5 rcases n with - | n; · simp [ofNatCode_eq, Code.ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 5)).map fun n => F a (ofNat Code n)), n, m) =
    some (F a (ofNat Code (n + 5)))
  have hm : m < n + 5 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
  simp only [List.length_map, List.length_range, List.getElem?_eq_getElem, hm, m1, m2,
    List.getElem_map, List.getElem_range, Option.bind_some, Option.map_some, G₁, m]
  rw [show ofNat Code (n + 5) = Code.ofNatCode (n + 5) from rfl]
  simp only [Code.ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl


/-- Structural recursion on `Nat.RecursiveIn.Code` with curried branch functions is primitive
recursive. Adapted from `Nat.Partrec.Code.primrec_recOn` with an additional `oracle` branch. -/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o)
    {pr : α → Code → Code → σ → σ → σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ =>
      let a2 := a.2; let a22 := a2.2; let a222 := a22.2; pr a.1 a2.1 a22.1 a222.1 a222.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Primrec fun a : α × Code × Code × σ × σ =>
      let a2 := a.2; let a22 := a2.2; let a222 := a22.2; co a.1 a2.1 a22.1 a222.1 a222.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Primrec fun a : α × Code × Code × σ × σ =>
      let a2 := a.2; let a22 := a2.2; let a222 := a22.2; pc a.1 a2.1 a22.1 a222.1 a222.2)
    {rf : α → Code → σ → σ} (hrf : Primrec fun a : α × Code × σ =>
      let a2 := a.2; rf a.1 a2.1 a2.2) :
    let F (a : α) (c : Code) : σ :=
      Code.recOn c (z a) (s a) (l a) (r a) (o a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr ho
    (pr := fun a b => let b2 := b.2; let b22 := b2.2; pr a b.1 b2.1 b22.1 b22.2) (.mk hpr)
    (co := fun a b => let b2 := b.2; let b22 := b2.2; co a b.1 b2.1 b22.1 b22.2) (.mk hco)
    (pc := fun a b => let b2 := b.2; let b22 := b2.2; pc a b.1 b2.1 b22.1 b22.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

private def lup (L : List (List (Option ℕ))) (p : ℕ × Code) (n : ℕ) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o

@[local fun_prop]
private theorem lup_primrec {α : Type*} [Primcodable α] {L : α → List (List (Option ℕ))}
    {p : α → ℕ × Code} {n : α → ℕ} (hL : Primrec L) (hp : Primrec p) (hn : Primrec n) :
    Primrec fun a => lup (L a) (p a) (n a) := by
  unfold lup
  fun_prop

private noncomputable def G (σ : List ℕ) (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Code.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (σ[n]?) -- oracle
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (Nat.pair z y)
              lup L (k, cg) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c) (Nat.pair z (m + 1)))


private theorem hG : Primrec₂ G := by
  refine Primrec.option_some.comp (Primrec.list_map (β := ℕ) (σ := Option ℕ) (by fun_prop)
    (?_ : Primrec _))
  refine Primrec.nat_casesOn (by fun_prop) (_root_.Primrec.const Option.none) (?_ : Primrec _)
  apply primrec_recOn (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) <;> fun_prop

private theorem evaln_map (σ k c n) :
    ((List.range k)[n]?.bind fun a ↦ evaln σ k c a) = evaln σ k c n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln σ k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn

/-- The `Nat.RecursiveIn.Code.evaln` function is primitive recursive. -/
theorem primrec_evaln :
    Primrec fun q : List ℕ × (ℕ × Code) × ℕ =>
      let q2 := q.2; let q21 := q2.1; evaln q.1 q21.1 q21.2 q2.2 :=
  have :
    Primrec₂ fun (σ : List ℕ) (n : ℕ) =>
      let a := ofNat (ℕ × Code) n
      (List.range a.1).map (evaln σ a.1 a.2) :=
    Primrec.nat_strong_rec (fun σ n => let a := ofNat (ℕ × Code) n;
        (List.range a.1).map (evaln σ a.1 a.2)) hG
      fun σ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_unpair, Option.some_inj]
      refine List.map_congr_left fun n => ?_
      have : List.range p = List.range (Nat.pair p.unpair.1 (encode (ofNat Code p.unpair.2))) := by
        simp
      rw [this]
      generalize p.unpair.1 = k
      generalize ofNat Code p.unpair.2 = c
      intro nk
      rcases k with - | k'
      · simp [evaln]
      let k := k' + 1
      simp only
      simp only [List.mem_range, Nat.lt_succ_iff] at nk
      have hg :
        ∀ {k' c' n},
          Nat.pair k' (encode c') < Nat.pair k (encode c) →
            lup ((List.range (Nat.pair k (encode c))).map fun n =>
              (List.range n.unpair.1).map (evaln σ n.unpair.1 (ofNat Code n.unpair.2))) (k', c') n =
            evaln σ k' c' n := by
        intro k₁ c₁ n₁ hl
        simp [lup, List.getElem?_range hl, evaln_map, Bind.bind, Option.bind_map]
      obtain - | - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
        simp only [evaln, bind, nk, guard_true, pure, Option.bind_some, unpaired, pair_unpair]
      · obtain ⟨lf, lg⟩ := encodeCode_lt_pair cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln σ k cf n
        · rfl
        cases evaln σ k cg n <;> rfl
      · obtain ⟨lf, lg⟩ := encodeCode_lt_comp cf cg
        rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln σ k cg n
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lf)]
      · obtain ⟨lf, lg⟩ := encodeCode_lt_prec cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases n.unpair.2
        · rfl
        simp only
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evaln σ k' _ _
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lg)]
      · have lf := encodeCode_lt_rfind' cf
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        rcases evaln σ k cf n with - | x
        · rfl
        simp only [Option.bind_some]
        cases x with
        | zero => simp
        | succ _ => simpa using hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)
  (Primrec.option_bind
    (Primrec.list_getElem?.comp (this.comp Primrec.fst
      (Primrec.encode_iff.2 (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
    Primrec.snd.to₂).of_eq
    fun ⟨σ, ⟨k, c⟩, n⟩ => by simp [evaln_map, Option.bind_map]

end Nat.RecursiveIn.Code

