/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteProjection
public import CslibFrontier.Foundations.Relation.RelatesWithinSteps

/-!
# Projection of arbitrary H-word moves to source rewriting

Changes of pair coordinates are authorized by the neighboring rule marker. Protected end
markers ensure that the two source positions of this rule lie inside the original word.

## Main results

* `HWord.RewriteGadget.step_readout`: each arbitrary H-word move decodes to at most two
  standard source rewriting steps.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014],
  arXiv:1405.0847v1, Section 3, proof of Theorem 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

open Cslib.PostCorrespondence

variable {n q r : ℕ} (rules : Fin r → Rule q)
  {u v : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}

private theorem first_change_marker {p : Symbol q r} {a a' b b' : Option (Fin q)}
    (h : Compatible rules p (.pair a b)) (h' : Compatible rules p (.pair a' b'))
    (hne : a ≠ a') : ∃ i, p = .marker i := by
  cases p with
  | start => exact False.elim (hne (h.1.trans h'.1.symm))
  | finish => exact False.elim h
  | marker i => exact ⟨i, rfl⟩
  | pair c d =>
    obtain ⟨x, hd, ha⟩ := h
    obtain ⟨y, hd', ha'⟩ := h'
    exact False.elim (hne (ha.trans ((hd.symm.trans hd').trans ha'.symm)))

private theorem second_change_marker {p : Symbol q r} {a a' b b' : Option (Fin q)}
    (h : Compatible rules (.pair a b) p) (h' : Compatible rules (.pair a' b') p)
    (hne : b ≠ b') : ∃ i, p = .marker i := by
  cases p with
  | start => exact False.elim h
  | finish => exact False.elim (hne (h.1.trans h'.1.symm))
  | marker i => exact ⟨i, rfl⟩
  | pair c d =>
    obtain ⟨x, hb, hc⟩ := h
    obtain ⟨y, hb', hc'⟩ := h'
    exact False.elim (hne (hb.trans ((hc.symm.trans hc').trans hb'.symm)))

private theorem before_marker {p : Symbol q r} (i : Fin r)
    (h : Compatible rules p (.marker i)) : ∃ a c, p = .pair a (some c) := by
  rcases p with _ | _ | _ | ⟨a, b⟩ <;> try exact h.elim
  exact h.elim (fun h => ⟨a, _, congrArg (Symbol.pair a) h⟩) fun h =>
    ⟨a, _, congrArg (Symbol.pair a) h⟩

private theorem after_marker {p : Symbol q r} (i : Fin r)
    (h : Compatible rules (.marker i) p) : ∃ c b, p = .pair (some c) b := by
  rcases p with _ | _ | _ | ⟨a, b⟩ <;> try exact h.elim
  exact h.elim (fun h => ⟨_, b, congrArg (Symbol.pair · b) h⟩) fun h =>
    ⟨_, b, congrArg (Symbol.pair · b) h⟩

private theorem pair_interior (k : Fin (n + 3)) (a b : Option (Fin q))
    (hpair : code.symm (u k) = .pair a b)
    (hstart : u 0 = code .start) (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    0 < k.val ∧ k.val < n + 2 := by
  refine ⟨Nat.pos_of_ne_zero fun hk0 => ?_, lt_of_le_of_ne (by omega) fun hkn => ?_⟩
  · simp [(Fin.ext hk0 : k = 0), hstart] at hpair
  · simp [(Fin.ext hkn : k = ⟨n + 2, by omega⟩), hfinish] at hpair

private theorem first_marker_depth (hu : HWord.Legal (compatibility rules) u)
    (k : Fin (n + 3)) (hk : 0 < k.val) (i : Fin r)
    (hm : code.symm (u ⟨k.val - 1, by omega⟩) = .marker i)
    (hstart : u 0 = code .start) : 3 ≤ k.val := by
  by_contra h
  rcases (by omega : k.val = 1 ∨ k.val = 2) with hc | hc
  · have h0 : (⟨k.val - 1, by omega⟩ : Fin (n + 3)) = 0 := Fin.ext (by simp [hc])
    simp [h0, hstart] at hm
  · have hedge := edge_view rules hu 0 ⟨k.val - 1, by omega⟩ (by simp [hc])
    rwa [hstart, Equiv.symm_apply_apply, hm] at hedge

private structure FirstNeighborhood (u : Fin (n + 3) → Fin (Fintype.card (Symbol q r)))
    (k : Fin (n + 3)) (a a' b : Option (Fin q)) where
  rule : Fin r
  lower : 3 ≤ k.val
  upper : k.val < n + 2
  left : Option (Fin q)
  letter : Fin q
  before : code.symm (u ⟨k.val - 2, by omega⟩) = .pair left (some letter)
  compatible : Compatible rules (.pair left (some letter)) (.marker rule)
  source : Compatible rules (.marker rule) (.pair a b)
  target : Compatible rules (.marker rule) (.pair a' b)

private theorem first_neighborhood (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a a' b : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a' b)
    (hne : a ≠ a') (hstart : u 0 = code .start)
    (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Nonempty (FirstNeighborhood rules u k a a' b) := by
  obtain ⟨hk0, hkn⟩ := pair_interior k a b hpu hstart hfinish
  let previous : Fin (n + 3) := ⟨k.val - 1, by omega⟩
  have hprev : previous ≠ k := Fin.ne_of_val_ne (by dsimp only [previous]; omega)
  have hu' := edge_view rules hu previous k (by change k.val - 1 + 1 = k.val; omega)
  have hv' := edge_view rules hv previous k (by change k.val - 1 + 1 = k.val; omega)
  rw [hpu] at hu'
  rw [hpv, ← he previous hprev] at hv'
  obtain ⟨i, hm⟩ := first_change_marker rules hu' hv' hne
  have hk3 := first_marker_depth rules hu k hk0 i hm hstart
  let earlier : Fin (n + 3) := ⟨k.val - 2, by omega⟩
  have hbefore := edge_view rules hu earlier previous
    (by change k.val - 2 + 1 = k.val - 1; omega)
  rw [hm] at hbefore
  obtain ⟨left, c, hc⟩ := before_marker rules i hbefore
  rw [hc] at hbefore
  exact ⟨⟨i, hk3, hkn, left, c, hc, hbefore,
    by simpa only [hm] using hu', by simpa only [hm] using hv'⟩⟩

private theorem first_coordinate_rewrites (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a a' b : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a' b)
    (hne : a ≠ a') (hstart : u 0 = code .start)
    (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Rewrites (RuleSet rules) (List.ofFn (readout rules u hu))
      (List.ofFn (readout rules v hv)) := by
  obtain ⟨C⟩ := first_neighborhood rules hu hv k he a a' b hpu hpv hne hstart hfinish
  have hk3 := C.lower
  have hkn := C.upper
  let context : Fin n := ⟨k.val - 3, by omega⟩
  let changed : Fin n := ⟨k.val - 2, by omega⟩
  have hindex : k.val - 3 + 1 = k.val - 2 := by omega
  have hcontext : C.letter = readout rules u hu context :=
    Option.some.inj (readout_pair_right rules hu context C.left (some C.letter)
      (by simpa only [context, hindex] using C.before))
  have hx := readout_pair_left rules hu changed a b
    (by simpa only [changed, Nat.sub_add_cancel (by omega : 2 ≤ k.val)] using hpu)
  have hy := readout_pair_left rules hv changed a' b
    (by simpa only [changed, Nat.sub_add_cancel (by omega : 2 ≤ k.val)] using hpv)
  have hcontext' : readout rules u hu context = readout rules v hv context :=
    readout_first_off rules hu hv k he a a' b hpu hpv context (by dsimp [context]; omega)
  have hlocal := marker_right_rewrites rules C.rule C.letter (readout rules u hu changed)
    (readout rules v hv changed) C.left b b C.compatible
    (by simpa only [hx] using C.source) (by simpa only [hy] using C.target)
    (by intro h; exact hne (hx.trans ((congrArg some h).trans hy.symm)))
  apply rewrites_of_pair rules context changed hindex
  · intro j _hj hchanged
    exact readout_first_off rules hu hv k he a a' b hpu hpv j fun h =>
      hchanged (Fin.ext (by change j.val = k.val - 2; omega))
  · simpa only [hcontext, ← hcontext'] using hlocal

private theorem second_marker_depth (hu : HWord.Legal (compatibility rules) u)
    (k : Fin (n + 3)) (hk : k.val < n + 2) (i : Fin r)
    (hm : code.symm (u ⟨k.val + 1, by omega⟩) = .marker i)
    (hfinish : u ⟨n + 2, by omega⟩ = code .finish) : k.val < n := by
  by_contra h
  rcases (by omega : k.val = n ∨ k.val = n + 1) with hc | hc
  · have hedge := edge_view rules hu ⟨k.val + 1, by omega⟩ ⟨n + 2, by omega⟩ (by simp [hc])
    rwa [hm, hfinish, Equiv.symm_apply_apply] at hedge
  · have hn2 : (⟨k.val + 1, by omega⟩ : Fin (n + 3)) = ⟨n + 2, by omega⟩ :=
      Fin.ext (by simp [hc])
    simp [hn2, hfinish] at hm

private structure SecondNeighborhood (u : Fin (n + 3) → Fin (Fintype.card (Symbol q r)))
    (k : Fin (n + 3)) (a b b' : Option (Fin q)) where
  rule : Fin r
  lower : 0 < k.val
  upper : k.val < n
  right : Option (Fin q)
  letter : Fin q
  after : code.symm (u ⟨k.val + 2, by omega⟩) = .pair (some letter) right
  compatible : Compatible rules (.marker rule) (.pair (some letter) right)
  source : Compatible rules (.pair a b) (.marker rule)
  target : Compatible rules (.pair a b') (.marker rule)

private theorem second_neighborhood (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a b b' : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a b')
    (hne : b ≠ b') (hstart : u 0 = code .start)
    (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Nonempty (SecondNeighborhood rules u k a b b') := by
  obtain ⟨hk0, hkn⟩ := pair_interior k a b hpu hstart hfinish
  let following : Fin (n + 3) := ⟨k.val + 1, by omega⟩
  have hfollowing : following ≠ k := Fin.ne_of_val_ne (by dsimp only [following]; omega)
  have hu' := edge_view rules hu k following rfl
  have hv' := edge_view rules hv k following rfl
  rw [hpu] at hu'
  rw [hpv, ← he following hfollowing] at hv'
  obtain ⟨i, hm⟩ := second_change_marker rules hu' hv' hne
  have hk' := second_marker_depth rules hu k hkn i hm hfinish
  let later : Fin (n + 3) := ⟨k.val + 2, by omega⟩
  have hafter := edge_view rules hu following later rfl
  rw [hm] at hafter
  obtain ⟨c, right, hc⟩ := after_marker rules i hafter
  rw [hc] at hafter
  exact ⟨⟨i, hk0, hk', right, c, hc, hafter,
    by simpa only [hm] using hu', by simpa only [hm] using hv'⟩⟩

private theorem second_coordinate_rewrites (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a b b' : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a b')
    (hne : b ≠ b') (hstart : u 0 = code .start)
    (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Rewrites (RuleSet rules) (List.ofFn (readout rules u hu))
      (List.ofFn (readout rules v hv)) := by
  obtain ⟨C⟩ := second_neighborhood rules hu hv k he a b b' hpu hpv hne hstart hfinish
  have hk0 := C.lower
  have hk' := C.upper
  let changed : Fin n := ⟨k.val - 1, by omega⟩
  let context : Fin n := ⟨k.val, hk'⟩
  have hcontext : C.letter = readout rules u hu context :=
    Option.some.inj (readout_pair_left rules hu context (some C.letter) C.right C.after)
  have hx := readout_pair_right rules hu changed a b
    (by simpa only [changed, Nat.sub_add_cancel hk0] using hpu)
  have hy := readout_pair_right rules hv changed a b'
    (by simpa only [changed, Nat.sub_add_cancel hk0] using hpv)
  have hcontext' : readout rules u hu context = readout rules v hv context :=
    readout_second_off rules hu hv k he a b b' hpu hpv context (by dsimp [context]; omega)
  have hlocal := marker_left_rewrites rules C.rule C.letter (readout rules u hu changed)
    (readout rules v hv changed) a a C.right C.compatible
    (by simpa only [hx] using C.source) (by simpa only [hy] using C.target)
    (by intro h; exact hne (hx.trans ((congrArg some h).trans hy.symm)))
  apply rewrites_of_pair rules changed context (by change k.val - 1 + 1 = k.val; omega)
  · intro j hchanged _hj
    exact readout_second_off rules hu hv k he a b b' hpu hpv j fun h =>
      hchanged (Fin.ext (by change j.val = k.val - 1; omega))
  · simpa only [hcontext, ← hcontext'] using hlocal

private theorem same_pair_eq (k : Fin (n + 3)) (he : ∀ j, j ≠ k → u j = v j)
    (a b : Option (Fin q)) (hpu : code.symm (u k) = .pair a b)
    (hpv : code.symm (v k) = .pair a b) : u = v := by
  funext j
  rcases eq_or_ne j k with rfl | hj
  · exact code.symm.injective (hpu.trans hpv.symm)
  · exact he j hj

private theorem first_coordinate_reflGen (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a a' b : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a' b)
    (hstart : u 0 = code .start) (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Relation.ReflGen (Rewrites (RuleSet rules)) (List.ofFn (readout rules u hu))
      (List.ofFn (readout rules v hv)) := by
  by_cases h : a = a'
  · subst a'; obtain rfl := same_pair_eq k he a b hpu hpv; exact .refl
  · exact .single (first_coordinate_rewrites rules hu hv k he a a' b hpu hpv h hstart hfinish)

private theorem second_coordinate_reflGen (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a b b' : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a b')
    (hstart : u 0 = code .start) (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Relation.ReflGen (Rewrites (RuleSet rules)) (List.ofFn (readout rules u hu))
      (List.ofFn (readout rules v hv)) := by
  by_cases h : b = b'
  · subst b'; obtain rfl := same_pair_eq k he a b hpu hpv; exact .refl
  · exact .single (second_coordinate_rewrites rules hu hv k he a b b' hpu hpv h hstart hfinish)

private theorem changed_readout (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j)
    (hstart : u 0 = code .start) (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Relation.RelatesWithinSteps (Rewrites (RuleSet rules)) (List.ofFn (readout rules u hu))
      (List.ofFn (readout rules v hv)) 2 := by
  classical
  by_cases hp : ∃ a b, code.symm (u k) = .pair a b
  · obtain ⟨a, b, hpu⟩ := hp
    by_cases hp' : ∃ a' b', code.symm (v k) = .pair a' b'
    · obtain ⟨a', b', hpv⟩ := hp'
      let middle := Function.update u k (code (.pair a' b))
      have hm := mixed_pair_legal rules hu hv k he a a' b b' hpu hpv
      have hmid : code.symm (middle k) = .pair a' b := by
        simp only [middle, Function.update_self, Equiv.symm_apply_apply]
      have hum : ∀ j, j ≠ k → u j = middle j := fun j hj => (Function.update_of_ne hj _ _).symm
      have hmv : ∀ j, j ≠ k → middle j = v j := fun j hj =>
        (Function.update_of_ne hj _ _).trans (he j hj)
      have hmiddle := HWord.reachable_of_eq_off hu hm k hum
      obtain ⟨hm0, hmn⟩ := reachable_boundaries rules hmiddle hstart hfinish
      have hfirst := Relation.RelatesWithinSteps.one_iff.mpr
        (first_coordinate_reflGen rules hu hm k hum a a' b hpu hmid hstart hfinish)
      have hsecond := Relation.RelatesWithinSteps.one_iff.mpr
        (second_coordinate_reflGen rules hm hv k hmv a' b b' hmid hpv hm0 hmn)
      exact hfirst.trans hsecond
    · rw [readout_eq_of_special rules hv hu k (fun j hj => (he j hj).symm) fun a b h =>
        hp' ⟨a, b, h⟩]
      exact (Relation.RelatesWithinSteps.refl _).mono (by decide)
  · rw [readout_eq_of_special rules hu hv k he fun a b h => hp ⟨a, b, h⟩]
    exact (Relation.RelatesWithinSteps.refl _).mono (by decide)

/-- One arbitrary H-word move projects to at most two real source rewriting steps. -/
theorem step_readout (hs : HWord.Step (compatibility rules) u v)
    (hstart : u 0 = code .start) (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Relation.RelatesWithinSteps (Rewrites (RuleSet rules))
      (List.ofFn (readout rules u hs.legal_left))
      (List.ofFn (readout rules v hs.legal_right)) 2 := by
  obtain ⟨hu, hv, k, _, he⟩ := hs
  exact changed_readout rules hu hv k he hstart hfinish

end Cslib.Complexity.NCL.HWord.RewriteGadget
