/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.FGLSS
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Computability.PCP.Approximation.AssignmentConsistency
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.List.DropRight

/-!
# Constructing the FGLSS graph on a native multi-tape machine

The construction enumerates the verifier's random strings and the answer strings for each
resulting query list. It retains the accepting self-consistent views and tests pairs for
conflicts, using binary query addresses throughout. The resulting edge-list graph is isomorphic
to `PCPVerifier.fglssGraph`.

This is the running-time step toward [Goldreich, Exercise 9.18][Goldreich2007DraftR5]
(`r5.pdf`, PDF pp. 67–68, printed pp. 449–450). The source permits adaptive queries. Here the
queries depend only on the input and the coins, and each answer string has the length of its
query list. Adding one to the encoded input length accounts for the empty word.

## Main results

* `Cslib.Complexity.PCPVerifier.fglssGraphIso`: the explicit edge list realizes the FGLSS graph.
* `Cslib.Complexity.PCPVerifier.computableInO_fglssEdgeList`: the native machine certificate.
* `Cslib.Complexity.PCPVerifier.computableInPolyTime_fglssEdgeList`: polynomial-time construction
  under logarithmic randomness and a constant query bound.
-/

public section

namespace Cslib.Complexity.PCPVerifier

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} (V : PCPVerifier α)

private abbrev encWords := encList encBits
private abbrev encView := encPair encBits encBits

private def label (word : List Bool × List Bool) : ℕ :=
  ofBits (encView word ++ [true])

private theorem label_injective : Function.Injective label := by
  intro x y h
  have hbits (w) : (label w).bits = encView w ++ [true] := by
    simp [label, bits_ofBits]
  have he := congrArg Nat.bits h
  rw [hbits, hbits] at he
  exact encView.injective (List.append_inj_left' he rfl)

private def assigned (a : α) (word : List Bool × List Bool) : List (ℕ × Bool) :=
  (V.queries (a, word.1)).zip word.2

private def keep (a : α) (word : List Bool × List Bool) : Bool :=
  V.verdict ((a, word.1), word.2) &&
    SAT.consistentLits (V.assigned a word) (V.assigned a word)

-- The cap makes this stage polynomial in its explicit input. The caller chooses a budget
-- whose logarithm bounds the length of every query list.
private def viewsForRandom (a : α) (budget : ℕ) (ρ : List Bool) :
    List (List Bool × List Bool) :=
  ((BitString.enumList (min (V.queries (a, ρ)).length (Nat.log 2 budget))).map
    (fun bits => (ρ, bits))).filter (V.keep a)

private def viewsFrom (a : α) (randoms : List (List Bool)) (budget : ℕ) :
    List (List Bool × List Bool) :=
  randoms.flatMap (V.viewsForRandom a budget)

private def graphFrom (a : α) (views : List (List Bool × List Bool)) : Graph :=
  ⟨views.map label, views.flatMap fun u =>
    (views.filter fun v => !SAT.consistentLits (V.assigned a u) (V.assigned a v)).map
      fun v => (label u, label v)⟩

private def queryWidth (a : α) (randoms : List (List Bool)) : ℕ :=
  (randoms.map fun ρ => (V.queries (a, ρ)).length).foldl max 0

private theorem queryWidth_le (a : α) (randoms : List (List Bool)) {q : ℕ}
    (h : ∀ ρ ∈ randoms, (V.queries (a, ρ)).length ≤ q) :
    V.queryWidth a randoms ≤ q := by
  unfold queryWidth
  cases he : randoms.map (fun ρ => (V.queries (a, ρ)).length) with
  | nil => simp
  | cons n ns =>
    rw [List.foldl_max_eq_max (by simp), zero_max, List.max_le_iff]
    intro m hm
    rw [← he] at hm
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hm
    exact h ρ hρ

private theorem length_queries_le_queryWidth (a : α) {randoms : List (List Bool)}
    {ρ : List Bool} (hρ : ρ ∈ randoms) : (V.queries (a, ρ)).length ≤ V.queryWidth a randoms := by
  have hm : (V.queries (a, ρ)).length ∈
      randoms.map (fun w => (V.queries (a, w)).length) := List.mem_map_of_mem hρ
  simpa [queryWidth, List.foldl_max_eq_max (List.ne_nil_of_mem hm)] using List.le_max_of_mem hm

/-- The edge-list realization of `fglssGraph`. A vertex label is the binary number obtained
by appending a high-order one to the framed pair of random and answer strings.
Each conflict is emitted in both orientations. -/
def fglssEdgeList (a : α) : Graph :=
  let randoms := BitString.enumList (V.coins a)
  V.graphFrom a (V.viewsFrom a randoms (2 ^ V.queryWidth a randoms))

private theorem consistent_assigned_iff {a : α} (u v : V.View a) :
    SAT.consistentLits (V.assigned a (List.ofFn u.random, List.ofFn u.answers))
      (V.assigned a (List.ofFn v.random, List.ofFn v.answers)) = true ↔ u.Consistent v := by
  rw [SAT.consistentLits_eq_true_iff]
  simp only [assigned, List.forall_mem_iff_getElem, List.length_zip, List.length_ofFn,
    min_self, List.getElem_zip, List.getElem_ofFn, View.Consistent]
  exact ⟨fun h i j => h i i.isLt j j.isLt, fun h i hi j hj => h ⟨i, hi⟩ ⟨j, hj⟩⟩

private def viewWords {a : α} (u : V.View a) : List Bool × List Bool :=
  (List.ofFn u.random, List.ofFn u.answers)

private theorem viewWords_injective (a : α) : Function.Injective (V.viewWords (a := a)) := by
  rintro ⟨u, x⟩ ⟨v, y⟩ h
  have huv : u = v := List.ofFn_injective (congrArg Prod.fst h)
  subst v
  have hxy : x = y := List.ofFn_injective (congrArg Prod.snd h)
  subst y
  rfl

private theorem mem_viewsFrom_iff (a : α) (word : List Bool × List Bool) :
    word ∈ V.viewsFrom a (BitString.enumList (V.coins a))
      (2 ^ V.queryWidth a (BitString.enumList (V.coins a))) ↔
      ∃ u : V.View a, V.IsFGLSSVertex a u ∧ V.viewWords u = word := by
  rcases word with ⟨ρ, bits⟩
  have hwidth (hρ : ρ.length = V.coins a) :
      min (V.queries (a, ρ)).length
        (Nat.log 2 (2 ^ V.queryWidth a (BitString.enumList (V.coins a)))) =
        (V.queries (a, ρ)).length := by
    rw [Nat.log_pow (by decide)]
    exact min_eq_left (V.length_queries_le_queryWidth a (BitString.mem_enumList.mpr hρ))
  constructor
  · intro hm
    obtain ⟨w, hw, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hm, hk⟩ := List.mem_filter.mp hm
    obtain ⟨bs, hbs, he⟩ := List.mem_map.mp hm
    cases he
    have hρ := BitString.mem_enumList.mp hw
    have hb := BitString.mem_enumList.mp hbs
    rw [hwidth hρ] at hb
    have hr : List.ofFn (fun i : Fin (V.coins a) => ρ[i.val]'(hρ.symm ▸ i.isLt)) = ρ := by
      apply List.ext_getElem (by simp [hρ])
      simp
    let u : V.View a := ⟨fun i => ρ[i.val]'(hρ.symm ▸ i.isLt),
      fun i => bits[i.val]'(by simpa only [hr, ← hb] using i.isLt)⟩
    have huv : V.viewWords u = (ρ, bits) := by
      refine Prod.ext hr (List.ext_getElem (by simp [viewWords, u, hr, hb]) ?_)
      intros
      simp [viewWords, u]
    have hu : V.keep a (V.viewWords u) = true := huv ▸ hk
    obtain ⟨haccepts, hconsistent⟩ := Bool.and_eq_true_iff.mp hu
    exact ⟨u, ⟨haccepts, (V.consistent_assigned_iff u u).mp hconsistent⟩, huv⟩
  · rintro ⟨u, hu, h⟩
    have hr : List.ofFn u.random = ρ := congrArg Prod.fst h
    have hb : List.ofFn u.answers = bits := congrArg Prod.snd h
    have hρ : ρ.length = V.coins a := by rw [← hr, List.length_ofFn]
    refine List.mem_flatMap.mpr ⟨ρ, BitString.mem_enumList.mpr hρ, List.mem_filter.mpr ⟨?_, ?_⟩⟩
    · refine List.mem_map.mpr ⟨bits, BitString.mem_enumList.mpr ?_, rfl⟩
      rw [hwidth hρ, ← hb, List.length_ofFn, hr]
    · rw [← h]
      exact Bool.and_eq_true_iff.mpr ⟨hu.accepts, (V.consistent_assigned_iff u u).mpr hu.consistent⟩

/-- The edge-list realization has exactly the vertices and edges of the mathematical FGLSS
graph, up to relabeling. -/
noncomputable def fglssGraphIso (a : α) : V.fglssGraph a ≃g (V.fglssEdgeList a).induced := by
  let vertices := V.viewsFrom a (BitString.enumList (V.coins a))
    (2 ^ V.queryWidth a (BitString.enumList (V.coins a)))
  have hl (u : {v : V.View a // V.IsFGLSSVertex a v}) : V.viewWords u.val ∈ vertices :=
    (V.mem_viewsFrom_iff a _).mpr ⟨u.val, u.property, rfl⟩
  let f (u : {v : V.View a // V.IsFGLSSVertex a v}) :
      {n // n ∈ (V.fglssEdgeList a).vertices} :=
    ⟨label (V.viewWords u.val), List.mem_map_of_mem (hl u)⟩
  have he : Function.Bijective f := by
    constructor
    · intro u v h
      exact Subtype.ext (V.viewWords_injective a (label_injective (congrArg Subtype.val h)))
    · intro ⟨n, hn⟩
      obtain ⟨word, hw, rfl⟩ := List.mem_map.mp (show n ∈ vertices.map label from hn)
      obtain ⟨u, hu, rfl⟩ := (V.mem_viewsFrom_iff a _).mp hw
      exact ⟨⟨u, hu⟩, rfl⟩
  refine ⟨Equiv.ofBijective f he, ?_⟩
  intro u v
  change (V.fglssEdgeList a).induced.Adj (f u) (f v) ↔ (V.fglssGraph a).Adj u v
  rw [fglssGraph_adj, Graph.induced_adj, Graph.toSimpleGraph_adj]
  change ((f u).val ≠ (f v).val ∧
    (((f u).val, (f v).val) ∈ (V.graphFrom a vertices).edges ∨
      ((f v).val, (f u).val) ∈ (V.graphFrom a vertices).edges)) ↔ ¬u.val.Consistent v.val
  have edge (x y : {v : V.View a // V.IsFGLSSVertex a v}) :
      ((f x).val, (f y).val) ∈ (V.graphFrom a vertices).edges ↔ ¬x.val.Consistent y.val := by
    change (label (V.viewWords x.val), label (V.viewWords y.val)) ∈ _ ↔ _
    simp only [graphFrom, List.mem_flatMap, List.mem_filter, List.mem_map, Prod.mk.injEq,
      label_injective.eq_iff, exists_eq_right_right, hl, true_and]
    rw [Bool.not_eq_true']
    exact Bool.eq_false_iff.trans (not_congr (V.consistent_assigned_iff x.val y.val))
  rw [edge u v, edge v u]
  refine ⟨fun h => h.2.elim id fun h' h => h' h.symm, fun h => ⟨?_, Or.inl h⟩⟩
  intro heq
  have huv := he.1 (Subtype.ext heq)
  subst v
  exact h u.property.consistent

private theorem nativePostprocess {β γ : Type} {encIn : α ↪ List Bool}
    {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool} {size T S : α → ℕ}
    {f : α → β} {g : β → γ}
    (hf : ComputableInO f encIn encMid T S) (hT : PolyBounded size T) (hS : PolyBounded size S)
    (hg : ComputableInPolyTime g encMid encOut) :
    ∃ T' S', PolyBounded size T' ∧ PolyBounded size S' ∧
      ComputableInO (fun a => g (f a)) encIn encOut T' S' := by
  obtain ⟨c, hc⟩ := hf.length_le
  have hl : PolyBounded size (fun a => (encMid (f a)).length) :=
    ((PolyBounded.const c).mul (hS.add (.const 1))).mono hc
  obtain ⟨Tg, Sg, hTg, hSg, hg⟩ := hg.exists_computableInO
  exact ⟨_, _, hT.add (hTg.comp hl), hS.add (hSg.comp hl), hg.comp hf⟩

private theorem nativeTwoPow {encIn : α ↪ List Bool} {size T S width : α → ℕ}
    (h : ComputableInO width encIn encUnary T S) (hT : PolyBounded size T)
    (hS : PolyBounded size S) (hw : PolyBounded size (fun a => 2 ^ width a)) :
    ∃ T' S', PolyBounded size T' ∧ PolyBounded size S' ∧
      ComputableInO (fun a => 2 ^ width a) encIn encUnary T' S' := by
  refine ⟨_, _, hT.add ?_, hS.add hw, ComputableInO.unary_two_pow.comp h⟩
  exact (hw.mul hw).mono fun a =>
    Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := width a))

private theorem polyEnumFromBudget :
    ComputableInPolyTime (fun n => BitString.enumList (Nat.log 2 n)) encUnary encWords := by
  apply bitsEnumList_of_polyBounded ComputableInPolyTime.unary_log_two
  refine (PolyBounded.self.add (.const 1)).mono fun n => ?_
  simp only [encUnary_apply, List.length_replicate]
  exact Nat.pow_log_le_add_one 2 n

private theorem polyQueryWidth (hV : V.PolyTime enc) :
    ComputableInPolyTime (fun p : α × List (List Bool) => V.queryWidth p.1 p.2)
      (encPair enc encWords) encUnary := by
  apply (unary_foldl_max 0).comp
  exact ComputableInPolyTime.mapWith ((length_list encNat).comp hV.queries)
    (fst enc encWords) (snd enc encWords)

private theorem polyGraphFrom (hV : V.PolyTime enc) :
    ComputableInPolyTime (fun p : (α × List (List Bool)) × ℕ =>
      V.graphFrom p.1.1 (V.viewsFrom p.1.1 p.1.2 p.2))
      (encPair (encPair enc encWords) encUnary) encGraph := by
  have hlabel : ComputableInPolyTime label encView encNat :=
    ComputableInPolyTime.bitsToNat.comp
      (bitsAppend (of_eq fun _ => rfl) (const [true]))
  have hassigned : ComputableInPolyTime (fun p : α × (List Bool × List Bool) =>
      V.assigned p.1 p.2) (encPair enc encView) (encList (encPair encNat encBool)) := by
    unfold assigned
    have h := id' (encIn := encPair enc encView)
    exact (zip encNat encBool).comp ((hV.queries.comp (h.fst'.prod h.snd'.fst')).prod
      ((bits_encList_polyTime encBool).1.comp h.snd'.snd'))
  have hkeep : ComputableInPolyTime (fun p : α × (List Bool × List Bool) => V.keep p.1 p.2)
      (encPair enc encView) encBool := by
    have h := id' (encIn := encPair enc encView)
    exact bool_and' (hV.verdict.comp ((h.fst'.prod h.snd'.fst').prod h.snd'.snd'))
      (SAT.computableInPolyTime_consistentLits.comp (hassigned.prod hassigned))
  have hrow : ComputableInPolyTime (fun p : (α × ℕ) × List Bool =>
      V.viewsForRandom p.1.1 p.1.2 p.2)
      (encPair (encPair enc encUnary) encBits) (encList encView) := by
    unfold viewsForRandom
    have h := id' (encIn := encPair (encPair enc encUnary) encBits)
    have hw := (length_list encNat).comp (hV.queries.comp (h.fst'.fst'.prod h.snd'))
    have hlog := ComputableInPolyTime.unary_log_two.comp h.fst'.snd'
    have henum := bitsEnumList_of_polyBounded (unary_min' hw hlog) (by growth_poly)
    have hmap := ComputableInPolyTime.mapWith
      (ComputableInPolyTime.id' (encIn := encView)) h.snd' henum
    exact ComputableInPolyTime.filterWith hkeep h.fst'.fst' hmap
  have h := id' (encIn := encPair (encPair enc encWords) encUnary)
  have hviews := ComputableInPolyTime.flatMapWith hrow
    (h.fst'.fst'.prod h.snd') h.fst'.snd'
  have hgraph : ComputableInPolyTime (fun p : α × List (List Bool × List Bool) =>
      V.graphFrom p.1 p.2) (encPair enc (encList encView)) encGraph := by
    unfold graphFrom
    fun_prop
  exact hgraph.comp (h.fst'.fst'.prod hviews)

/-- A native multi-tape machine constructs the explicit FGLSS graph. Its time and charged space
are polynomial in `2 ^ (r + q) * (n + 1)`, where `n` is the encoded instance length, `r` is the
verifier's coin count, and `q` bounds the query list lengths on valid random strings. The only
machine hypotheses are the three component certificates of `PCPVerifier.PolyTime`. -/
theorem computableInO_fglssEdgeList (hV : V.PolyTime enc) (q : ℕ → ℕ)
    (hq : ∀ a ρ, ρ.length = V.coins a → (V.queries (a, ρ)).length ≤ q (enc a).length) :
    let size := fun a => 2 ^ (V.coins a + q (enc a).length) * ((enc a).length + 1)
    ∃ T S, PolyBounded size T ∧ PolyBounded size S ∧
      ComputableInO (V.fglssEdgeList) enc encGraph T S := by
  let size := fun a => 2 ^ (V.coins a + q (enc a).length) * ((enc a).length + 1)
  have hi : PolyBounded size (fun a => (enc a).length) := PolyBounded.self.mono fun a => by
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hr : PolyBounded size (fun a => 2 ^ V.coins a) := PolyBounded.self.mono fun a =>
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  obtain ⟨Tc, Sc, hTc, hSc, hc⟩ := hV.coins.exists_computableInO
  have hcoins : PolyBounded size V.coins := hr.mono fun _ => Nat.lt_two_pow_self.le
  obtain ⟨Tp, Sp, hTp, hSp, hp⟩ := nativeTwoPow (ComputableInO.natToUnary.comp hc)
    ((hTc.comp hi).add hcoins) ((hSc.comp hi).add hcoins) hr
  obtain ⟨Tr, Sr, hTr, hSr, hrand⟩ := nativePostprocess hp hTp hSp polyEnumFromBudget
  have hrand' := hrand.of_enc_eq (encC := encWords) (g := fun a => BitString.enumList (V.coins a))
    fun a => by simp [Nat.log_pow (by decide : 1 < 2)]
  have hx := ComputableInO.id' (encMid := enc)
  obtain ⟨Tw, Sw, hTw, hSw, hw⟩ := nativePostprocess (hx.prod hrand')
    (hi.add hTr) (hi.add hSr) (V.polyQueryWidth hV)
  have hwidth : PolyBounded size
      (fun a => 2 ^ V.queryWidth a (BitString.enumList (V.coins a))) :=
    PolyBounded.self.mono fun a =>
      (Nat.pow_le_pow_right (by decide)
        ((V.queryWidth_le a _ (fun ρ hρ => hq a ρ (BitString.mem_enumList.mp hρ))).trans
          (Nat.le_add_left _ _))).trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  obtain ⟨Ta, Sa, hTa, hSa, ha⟩ := nativeTwoPow hw hTw hSw hwidth
  obtain ⟨T, S, hT, hS, h⟩ := nativePostprocess ((hx.prod hrand').prod ha)
    ((hi.add hTr).add hTa) ((hi.add hSr).add hSa) (V.polyGraphFrom hV)
  exact ⟨T, S, hT, hS, h⟩

/-- Under a logarithmic coin bound and a constant query bound on valid random strings, the explicit
FGLSS edge-list graph is computable in polynomial time. -/
theorem computableInPolyTime_fglssEdgeList (hV : V.PolyTime enc) {c d : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hq : ∀ a ρ, ρ.length = V.coins a → (V.queries (a, ρ)).length ≤ d) :
    ComputableInPolyTime V.fglssEdgeList enc encGraph := by
  let size := fun a => 2 ^ (V.coins a + d) * ((enc a).length + 1)
  have hsize : PolyBounded (fun a => (enc a).length) size := by growth_poly
  obtain ⟨T, S, hT, hS, h⟩ := V.computableInO_fglssEdgeList hV (fun _ => d) hq
  exact h.computableInPolyTime (hT.comp hsize) (hS.comp hsize)

end Cslib.Complexity.PCPVerifier
