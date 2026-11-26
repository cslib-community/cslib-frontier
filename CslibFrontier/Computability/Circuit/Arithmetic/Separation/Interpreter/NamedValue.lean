/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Comp
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-!
# Values of formulas with named constants

`Interpreter.KV θ κ S F x w c` says four things:

* all runs of the formula `F` at `x` stop;
* the accepting runs have cost at most `c`;
* they use only names of constants in `S`;
* with the constants `κ`, the sum of their weights is `w`.

The rules follow the formulas, as for `Interpreter.Does` but with named constants.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Acc.CompK`.

## Main definitions

* `Interpreter.KV`.

## Main results

* `Interpreter.KV.of_does`, `Interpreter.KV.mul`, `Interpreter.KV.cons`, `Interpreter.KV.ite_true`,
  `Interpreter.KV.ite_false`, `Interpreter.KV.either`, `Interpreter.KV.app`, `Interpreter.KV.lett`,
  `Interpreter.KV.run`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The value of a formula. -/
@[expose] def KV (θ : List Bool → A) (κ : List Bool → R) (S : Set (List Bool)) (F : Fm) (x : Tree)
    (w : R) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧ val κ l = w

theorem wt_mul (κ : List Bool → R) {r s u : Run A} (h1 : u.th = r.th * s.th)
    (h2 : u.bill = r.bill ++ s.bill) :
    wt κ u = wt κ r * wt κ s := by
  rw [wt, wt, wt, h1, h2, map_mul, List.map_append, List.prod_append]
  ring

namespace KV

variable {κ : List Bool → R} {S : Set (List Bool)} {F G H : Fm} {x : Tree} {w w' : R} {c d : ℕ}

theorem mono (h : KV θ κ S F x w c) (hc : c ≤ d) : KV θ κ S F x w d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1.trans hc, (h2 r hr).2⟩, h3⟩

theorem congr (h : KV θ κ S F x w c) (hw : w = w') : KV θ κ S F x w' c := hw ▸ h

theorem hl (h : KV θ κ S F x w c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : KV θ κ S F x w c) :
    (∀ r ∈ Cslib.Circuits.Arithmetic.Separation.Interpreter.evl θ F x, r.cost ≤ c ∧ ∀ p ∈ r.bill,
        p ∈ S) ∧
    val κ (Cslib.Circuits.Arithmetic.Separation.Interpreter.evl θ F x) = w := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

theorem of_does {Q : List (A × Tree)} (h : Does θ F x Q c) :
    KV θ κ S F x (algebraMap A R (Q.map Prod.fst).sum) c := by
  obtain ⟨l, h1, h2, h3⟩ := h
  refine ⟨l, h1, fun r hr => ⟨(h2 r hr).2.1, ?_⟩, ?_⟩
  · rw [(h2 r hr).1]
    simp
  · rw [val_plain fun r hr => (h2 r hr).1, pval]
    have := h3 fun _ => 1
    simp only [mul_one, wsum] at this
    rw [this]

theorem of_gives {o : Tree} (h : Gives θ F x o c) : KV θ κ S F x 1 c := (of_does h).congr (by simp)

theorem fail (x : Tree) : KV θ κ S .fail x 0 0 := ⟨[], .fail x, by simp, by simp [val]⟩

/-- The runs of a formula with the one value `o` (with weight `1`) have total weight `1` in `R`. -/
private theorem sum_th_eq_one {L : List (Run A)} {o : Tree}
    (hL : ∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum [(1, o)] φ) :
    (L.map fun r => algebraMap A R r.th).sum = 1 := by
  have h2 := hL fun _ => 1
  simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    at h2
  have h4 := congrArg (algebraMap A R) h2
  rw [map_list_sum, List.map_map, map_one] at h4
  exact h4

theorem mul {o : Tree} (h : Gives θ F x o c) (ho : o.path ∈ S) : KV θ κ S (.mul F) x (κ o.path)
    (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout := Does.out_eq e2
  refine ⟨_, Ev.mul e1, ?_, ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨by simpa using a2, fun p hp => ?_⟩
    rw [a1, List.nil_append, List.mem_singleton] at hp
    rw [hp, hout r hr]
    exact ho
  · have h1 :
      (l.map fun r : Run A => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)).map
          (wt κ) =
        l.map fun r => algebraMap A R r.th * κ o.path := by
      rw [List.map_map]
      refine List.map_congr_left fun r hr => ?_
      simp [wt, (e2 r hr).1, hout r hr]
    rw [val, h1, List.sum_map_mul_right]
    rw [sum_th_eq_one e3, one_mul]

theorem cons (hF : KV θ κ S F x w c) (hG : KV θ κ S G x w' d) : KV θ κ S (.cons F G) x (w * w')
    (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    refine ⟨?_, fun p hp => ?_⟩
    · have h1 := (e2 r hr).1
      have h2 := (f2 s hs).1
      simp only [Run.tick, Run.seq]
      omega
    · simp only [Run.tick, Run.seq, List.mem_append] at hp
      exact hp.elim ((e2 r hr).2 p) ((f2 s hs).2 p)
  · rw [val, List.sum_map_flatMap]
    have h1 : ∀ r : Run A,
        ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map (wt κ)).sum = wt κ r * w' := by
      intro r
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun s _ => wt_mul κ rfl rfl
    simp only [h1]
    rw [List.sum_map_mul_right, ← e3]
    rfl

/-- The branch `K` of an `ite` whose condition has the one value `o`: the branch that `o` selects.
-/
private theorem ite_of {K : Fm} {o : Tree} (hF : Gives θ F x o c) (hK : KV θ κ S K x w d)
    (hev : ∀ {l l' : List (Run A)}, Ev θ F x l → (∀ r ∈ l, r.out = o) → Ev θ K x l' →
      Ev θ (.ite F G H) x (l.flatMap fun r => l'.map fun s => (r.seq s).tick s.out)) :
    KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hK
  refine ⟨_, hev e1 (Does.out_eq e2) f1, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.tick, Run.seq, a1, List.nil_append] at hp
      exact b2 p hp
  · rw [val, List.sum_map_flatMap]
    have h1 : ∀ r ∈ l,
        ((l'.map fun s => (r.seq s).tick s.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      rw [Function.comp_apply, wt_mul κ (r := r) (s := s) rfl rfl, wt, (e2 r hr).1]
      simp
    rw [List.map_congr_left h1, List.sum_map_mul_right]
    rw [sum_th_eq_one e3, one_mul]

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : KV θ κ S G x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) :=
  ite_of hF hG fun e1 hout f1 => Ev.ite (L := fun _ => _) e1 (fun _ _ _ => f1)
    (fun r hr h => absurd ((hout r hr).symm.trans h) ho)

theorem ite_false (hF : Gives θ F x .nil c) (hH : KV θ κ S H x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) :=
  ite_of hF hH fun e1 hout f1 => Ev.ite (L := fun _ => _) e1 (fun r hr h => absurd (hout r hr) h)
    (fun _ _ _ => f1)

theorem either (hG : KV θ κ S G x w c) (hH : KV θ κ S H x w' d) :
    KV θ κ S (.ite .guess G H) x (w + w') (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_,
      Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x)
          (fun r _ h => by rw [ite_eq_right h]; exact e1)
    (fun r _ h => by rw [ite_eq_left h]; exact f1), ?_, ?_⟩
  · intro u hu
    simp only
        [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map,
            Run.det, Tree.one,
      _root_.ite_true, reduceCtorEq, _root_.ite_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a1, a2⟩ := f2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
    · obtain ⟨a1, a2⟩ := e2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
  · rw [← e3, ← f3, val, val, val, add_comm]
    simp only
        [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append,
            List.map_map,
      Run.det, Tree.one, _root_.ite_true, reduceCtorEq, _root_.ite_false]
    congr 1
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]

/-- A weighted sum of values of `ω`, grouped by the value: for a list whose values lie in `D`. -/
private theorem sum_split {β : Type*} (D : Finset Tree) (f : β → A) (g : β → Tree)
    (ω : Tree → R) (L : List β) (hL : ∀ b ∈ L, g b ∈ D) :
    (L.map fun b => algebraMap A R (f b) * ω (g b)).sum =
      ∑ o ∈ D, algebraMap A R (L.map fun b => f b * if g b = o then 1 else 0).sum * ω o := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.sum_cons, ih fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')]
    simp only [List.map_cons, List.sum_cons, map_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (g b)]
    · simp
    · intro o _ ho
      rw [ite_eq_right (Ne.symm ho), mul_zero, map_zero, zero_mul]
    · intro h
      exact absurd (hL b List.mem_cons_self) h

/-- A plain computation, then a value. -/
theorem app {p : Tree} {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S (Fm.ofTree p) q.2 (ω q.2) d) :
    KV θ κ S (Cslib.Circuits.Arithmetic.Separation.Interpreter.app p F) x
        (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, KV θ κ S (Fm.ofTree p) s.out (ω s.out) d := by
    intro s hs
    obtain ⟨-, -, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨a1, a2, -⟩ := e2 s hs
    obtain ⟨b1, b2⟩ := (hG' s hs).evl.1 t ht
    refine ⟨by omega, fun p hp => ?_⟩
    rw [h2, a1, List.nil_append] at hp
    exact b2 p hp
  · rw [val, List.sum_map_flatMap]
    have h1 : ∀ s ∈ l,
        (((Cslib.Circuits.Arithmetic.Separation.Interpreter.evl θ (Fm.ofTree p) s.out).map fun t =>
            ((Run.det 1 p).seq s).seq t |>.tick t.out).map
        (wt κ)).sum = algebraMap A R s.th * ω s.out := by
      intro s hs
      rw [← (hG' s hs).evl.2, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick, Run.det, (e2 s hs).1, mul_assoc]
    rw [List.map_congr_left h1]
    -- functions with values in `R`
    have h2 : ∀ (L : List (Run A)) (P : List (A × Tree)),
        (∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum P φ) →
        (L.map fun s => algebraMap A R s.th * ω s.out).sum =
            (P.map fun q => algebraMap A R q.1 * ω q.2).sum := by
      intro L P hLP
      classical
      let D : Finset Tree := (L.map Run.out).toFinset ∪ (P.map Prod.snd).toFinset
      have k1 := sum_split D Run.th Run.out ω L fun s hs =>
        Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map_of_mem hs))
      have k2 := sum_split D Prod.fst Prod.snd ω P fun q hq =>
        Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map_of_mem hq))
      rw [k1, k2]
      refine Finset.sum_congr rfl fun o _ => ?_
      have := hLP fun t => if t = o then 1 else 0
      rw [this]
      rfl
    exact h2 l Q e3

theorem lett {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S G q.2 (ω q.2) d) :
    KV θ κ S (Cslib.Circuits.Arithmetic.Separation.Interpreter.lett F G) x
        (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem app_gives {p o : Tree} (hF : Gives θ F x o c) (hG : KV θ κ S (Fm.ofTree p) o w d) :
    KV θ κ S (Cslib.Circuits.Arithmetic.Separation.Interpreter.app p F) x w (c + d + 2) :=
  (app (Q := [(1, o)]) (ω := fun _ => w) hF (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hG)).congr (by simp)

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : KV θ κ S (Fm.ofTree p) y w e) : KV θ κ S (.run F G) x w (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho := Does.out_eq e2
  have ho' := Does.out_eq f2
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr, ho' s hs]; exact h.hl, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr, ho' s hs] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, -⟩ := f2 s hs
    obtain ⟨c1, c2⟩ := h.evl.1 t ht
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.seq, Run.tick, a1, b1, List.nil_append] at hp
      exact c2 p hp
  · rw [val, List.sum_map_flatMap]
    have h1 : ∀ r ∈ l,
        ((l'.flatMap fun s =>
            (Cslib.Circuits.Arithmetic.Separation.Interpreter.evl θ (Fm.ofTree r.out) s.out).map
                fun t =>
        ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [List.sum_map_flatMap]
      have h2 : ∀ s ∈ l',
          (((Cslib.Circuits.Arithmetic.Separation.Interpreter.evl θ (Fm.ofTree r.out) s.out).map
              fun t =>
          ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R s.th *
              (algebraMap A R r.th * w) := by
        intro s hs
        rw [ho r hr, ho' s hs, List.map_map, ← h.evl.2, val, ← List.sum_map_mul_left,
            ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only
            [Function.comp_apply, wt, Run.seq, Run.tick, (e2 r hr).1, (f2 s hs).1, List.nil_append,
                map_mul]
        ring
      rw [List.map_congr_left h2, List.sum_map_mul_right, sum_th_eq_one f3, one_mul]
    rw [List.map_congr_left h1, List.sum_map_mul_right, sum_th_eq_one e3, one_mul]

end KV

end Cslib.Circuits.Arithmetic.Separation.Interpreter
