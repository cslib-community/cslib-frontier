/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PostCorrespondence.Basic

/-!
# From the modified correspondence problem to PCP

Sipser's reduction [Sipser2013, proof of Theorem 5.15] turns an MPCP instance into a PCP instance
over the alphabet `α` extended by markers. Writing `⋆u` for `⋆u₁⋆u₂⋯⋆uₙ` and `u⋆` for
`u₁⋆u₂⋆⋯uₙ⋆`, the domino `t / b` becomes `⋆t / b⋆`, the start domino `t / b` becomes
`⋆t / ⋆b⋆`, and the end domino `⋆◇ / ◇` is added. A match must then begin with the start domino,
whose top and bottom alone begin with the same letter.

As stated, the construction can be unsound when a domino of the instance has an empty bottom,
since `⋆t / ε` may then come first. For the start domino `a / ba` and the single domino `b / ε`, the
MPCP instance has no match (its top begins with `a` and its bottom with `b`), but
`⋆b / ε`, `⋆a / ⋆b⋆a⋆`, `⋆◇ / ◇` is a match of the PCP instance (checked in the test module
`CslibFrontierTests.PostCorrespondence`). The reduction here therefore prefixes the start
domino with a start marker `▷`, which occurs in no other domino. A match then contains the start
domino, the part before its first occurrence matches on its own, and the part after it gives an
MPCP match. The domino `ε / ε`, which would be a PCP match by itself, is dropped.

Sipser's machine instances contain no domino with an empty bottom, so his proof is unaffected. The
instances of `CslibFrontier.Computability.PostCorrespondence.OfTM0` do: the rule `OfTM0.Rule.finish`
erases the final word `⊢ halt ⊣`. So Sipser's argument does not apply to them as written, while
the marked reduction needs no instance-specific argument. Empty tops are harmless.

## Main definitions

* `Cslib.PostCorrespondence.Marked`: the alphabet `α` with the markers `⋆`, `◇` and `▷`.
* `Cslib.PostCorrespondence.toPCP`: the reduction.

## Main results

* `Cslib.PostCorrespondence.solvable_toPCP_iff`: `toPCP I` is solvable iff `I` is.
* `Cslib.PostCorrespondence.mSolvable_manyOneReducible`: MPCP many-one reduces to PCP.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence

variable {α : Type*}

-- Exposed so that `decide` can evaluate the derived `DecidableEq` instance in client modules.
@[expose] public section MarkedDef

/-- The alphabet of Sipser's reduction from MPCP to PCP: the letters of `α` and three markers. -/
inductive Marked (α : Type*) where
  /-- A letter of the original alphabet. -/
  | letter : α → Marked α
  /-- The separator `⋆`. -/
  | sep : Marked α
  /-- The end marker `◇`. -/
  | stop : Marked α
  /-- The start marker `▷`, which forces every match to begin with the start domino. -/
  | start : Marked α
deriving DecidableEq

end MarkedDef

namespace Marked

/-- `Marked α` as `α ⊕ Fin 3`. -/
def equivSum : Marked α ≃ α ⊕ Fin 3 where
  toFun
    | letter a => .inl a
    | sep => .inr 0
    | stop => .inr 1
    | start => .inr 2
  invFun
    | .inl a => letter a
    | .inr 0 => sep
    | .inr 1 => stop
    | .inr 2 => start
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with a | ⟨_ | _ | _ | n, h⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · omega

instance [Primcodable α] : Primcodable (Marked α) := Primcodable.ofEquiv _ equivSum

theorem primrec_letter [Primcodable α] : Primrec (letter : α → Marked α) :=
  (Primrec.of_equiv_symm.comp Primrec.sumInl).of_eq fun _ => rfl

end Marked

open Marked

/-- `⋆a₁⋆a₂⋯⋆aₙ`: a separator before every letter. -/
def starBefore (w : List α) : List (Marked α) := w.flatMap fun a => [sep, letter a]

/-- `a₁⋆a₂⋆⋯aₙ⋆`: a separator after every letter. -/
def starAfter (w : List α) : List (Marked α) := w.flatMap fun a => [letter a, sep]

@[simp] theorem starBefore_nil : starBefore ([] : List α) = [] := List.flatMap_nil
@[simp] theorem starAfter_nil : starAfter ([] : List α) = [] := List.flatMap_nil
@[simp] theorem starBefore_cons (a : α) (w : List α) :
    starBefore (a :: w) = sep :: letter a :: starBefore w := List.flatMap_cons
@[simp] theorem starAfter_cons (a : α) (w : List α) :
    starAfter (a :: w) = letter a :: sep :: starAfter w := List.flatMap_cons
@[simp] theorem starBefore_append (u v : List α) :
    starBefore (u ++ v) = starBefore u ++ starBefore v := List.flatMap_append
@[simp] theorem starAfter_append (u v : List α) :
    starAfter (u ++ v) = starAfter u ++ starAfter v := List.flatMap_append

/-- `⋆ (a₁⋆⋯aₙ⋆) = (⋆a₁⋯⋆aₙ) ⋆`. -/
theorem sep_cons_starAfter (w : List α) : sep :: starAfter w = starBefore w ++ [sep] := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [starAfter_cons, starBefore_cons, ih]; rfl

theorem sep_cons_starAfter_append (w : List α) (l : List (Marked α)) :
    sep :: (starAfter w ++ l) = starBefore w ++ sep :: l := by
  rw [← List.cons_append, sep_cons_starAfter, List.append_assoc, List.singleton_append]

theorem length_starBefore (w : List α) : (starBefore w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [starBefore_cons, List.length_cons, ih]; omega

theorem starBefore_injective : Function.Injective (starBefore : List α → List (Marked α)) := by
  intro u
  induction u with
  | nil => rintro (_ | ⟨b, v⟩) h <;> simp at h ⊢
  | cons a u ih =>
    rintro (_ | ⟨b, v⟩) h <;> simp only [starBefore_cons, starBefore_nil, reduceCtorEq,
      List.cons.injEq, letter.injEq, true_and] at h
    exact congrArg₂ List.cons h.1 (ih h.2)

theorem start_notMem_starBefore (w : List α) : start ∉ starBefore w := by
  simp [starBefore]

theorem start_notMem_starAfter (w : List α) : start ∉ starAfter w := by
  simp [starAfter]

theorem stop_notMem_starBefore (w : List α) : stop ∉ starBefore w := by
  simp [starBefore]

theorem head?_starBefore (w : List α) : ∀ x ∈ (starBefore w).head?, x = sep := by
  cases w <;> simp

theorem head?_starAfter (w : List α) : ∀ x ∈ (starAfter w).head?, x ≠ sep := by
  cases w <;> simp

/-- The start domino of the PCP instance: `▷⋆t₁⋯⋆tₖ` over `▷⋆b₁⋆⋯bₗ⋆`. -/
def startPiece (s : Domino α) : Domino (Marked α) :=
  ⟨start :: starBefore s.top, start :: sep :: starAfter s.bottom⟩

/-- The end domino of the PCP instance: `⋆◇` over `◇`. -/
def stopPiece : Domino (Marked α) := ⟨[sep, stop], [stop]⟩

/-- The domino `⋆t₁⋯⋆tₖ` over `b₁⋆⋯bₗ⋆` of a domino `t` over `b`. -/
def markPiece (d : Domino α) : Domino (Marked α) := ⟨starBefore d.top, starAfter d.bottom⟩

/-- Sipser's reduction from MPCP to PCP [Sipser2013, proof of Theorem 5.15], with a start marker
`▷`: the start domino, the end domino, and the marked dominoes of the instance other than the empty
one. -/
def toPCP (I : MInstance α) : List (Domino (Marked α)) :=
  startPiece I.start :: stopPiece ::
    (I.dominoes.filter fun d => 0 < d.top.length + d.bottom.length).map markPiece

theorem tops_map_markPiece (ds : List (Domino α)) :
    tops (ds.map markPiece) = starBefore (tops ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.map_cons, tops_cons, tops_cons, ih, starBefore_append]; rfl

theorem bottoms_map_markPiece (ds : List (Domino α)) :
    bottoms (ds.map markPiece) = starAfter (bottoms ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.map_cons, bottoms_cons, bottoms_cons, ih, starAfter_append]; rfl

private theorem tops_filter (ds : List (Domino α)) :
    tops (ds.filter fun d => 0 < d.top.length + d.bottom.length) = tops ds ∧
      bottoms (ds.filter fun d => 0 < d.top.length + d.bottom.length) = bottoms ds := by
  induction ds with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    rcases d with ⟨_ | ⟨a, t⟩, _ | ⟨b, u⟩⟩ <;>
      simp only [List.filter_cons, List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add,
        Nat.lt_irrefl, Nat.zero_lt_succ, Nat.add_pos_left, decide_false, decide_true,
        Bool.false_eq_true, ↓reduceIte, tops_cons, bottoms_cons, List.nil_append, ih, and_self]

/-- The marked pieces after the start domino: if their tops follow `⋆T` and their bottoms follow
`⋆B⋆`, then a sequence of dominoes of the instance completes `T` over `B`. -/
private theorem complete_of_marked (I : MInstance α) :
    ∀ (ρ : List (Domino (Marked α))) (T B : List α), (∀ d ∈ ρ, d ∈ toPCP I) →
      starBefore T ++ tops ρ = starBefore B ++ sep :: bottoms ρ →
      ∃ ds : List (Domino α), (∀ d ∈ ds, d ∈ I.dominoes) ∧ T ++ tops ds = B ++ bottoms ds
  | [], T, B, _, h => by
    have := congrArg List.length h
    simp only [tops_nil, List.append_nil, bottoms_nil, List.length_append, length_starBefore,
      List.length_cons, List.length_nil] at this
    omega
  | d :: ρ, T, B, hρ, h => by
    obtain ⟨hd, hρ'⟩ := List.forall_mem_cons.1 hρ
    simp only [toPCP, List.mem_cons, List.mem_map, List.mem_filter] at hd
    rcases hd with rfl | rfl | ⟨e, ⟨he, -⟩, rfl⟩
    · -- the start domino again: impossible, by the parity of the prefix
      have h' : starBefore T ++ start :: (starBefore I.start.top ++ tops ρ) =
          (starBefore B ++ [sep]) ++ start :: (sep :: starAfter I.start.bottom ++ bottoms ρ) := by
        simpa [startPiece] using h
      obtain ⟨h'', -⟩ := (List.append_cons_inj_of_notMem_prefix (start_notMem_starBefore T)
        (by simp [start_notMem_starBefore])).mp h'
      have := congrArg List.length h''
      simp only [List.length_append, length_starBefore, List.length_singleton] at this; omega
    · -- the end domino: then `T = B`
      have h' : (starBefore T ++ [sep]) ++ stop :: tops ρ =
          (starBefore B ++ [sep]) ++ stop :: bottoms ρ := by
        simpa [stopPiece] using h
      obtain ⟨h'', -⟩ := (List.append_cons_inj_of_notMem_prefix (by simp [stop_notMem_starBefore])
        (by simp [stop_notMem_starBefore])).mp h'
      have hTB : T = B := starBefore_injective (List.append_cancel_right h'')
      exact ⟨[], by simp, by simp [hTB]⟩
    · -- a marked domino of the instance
      have key : starBefore B ++ sep :: (starAfter e.bottom ++ bottoms ρ) =
          starBefore (B ++ e.bottom) ++ sep :: bottoms ρ := by
        rw [sep_cons_starAfter_append, starBefore_append, List.append_assoc]
      simp only [tops_cons, bottoms_cons, markPiece] at h
      obtain ⟨ds, hds, heq⟩ := complete_of_marked I ρ (T ++ e.top) (B ++ e.bottom) hρ' (by
        rw [starBefore_append, List.append_assoc, h, key])
      exact ⟨e :: ds, List.forall_mem_cons.2 ⟨he, hds⟩, by simpa using heq⟩

/-- The heads of the concatenation of words whose heads satisfy `p`. -/
private theorem head?_flatMap {β : Type*} {p : α → Prop} {f : β → List α} :
    ∀ {l : List β}, (∀ b ∈ l, ∀ x ∈ (f b).head?, p x) → ∀ x ∈ (l.flatMap f).head?, p x
  | [], _ => by simp
  | b :: l, h => by
    cases hfb : f b with
    | nil => simpa [hfb] using head?_flatMap (fun c hc => h c (List.mem_cons_of_mem b hc))
    | cons y w => simpa [hfb] using h b List.mem_cons_self y

/-- **Sipser's reduction is correct.** An MPCP instance is solvable exactly when the PCP instance
`toPCP I` is. -/
theorem solvable_toPCP_iff (I : MInstance α) : Solvable (toPCP I) ↔ I.Solvable := by
  constructor
  · rintro ⟨ρ, hne, hρ, heq⟩
    by_cases hs : startPiece I.start ∈ ρ
    · obtain ⟨ρ₁, _, ρ₂, rfl, rfl, hρ₁⟩ :=
        List.exists_eq_append_cons_of_exists_mem (p := (· = startPiece I.start)) ⟨_, hs, rfl⟩
      -- no domino before the start domino contains `▷`
      have hnot (d : Domino (Marked α)) (hd : d ∈ ρ₁) : start ∉ d.top ∧ start ∉ d.bottom := by
        have hd' := hρ d (List.mem_append_left _ hd)
        simp only [toPCP, List.mem_cons, List.mem_map, List.mem_filter] at hd'
        rcases hd' with rfl | rfl | ⟨e, -, rfl⟩
        · exact absurd rfl (hρ₁ _ hd)
        · simp [stopPiece]
        · exact ⟨start_notMem_starBefore _, start_notMem_starAfter _⟩
      have ht : start ∉ tops ρ₁ := fun h =>
        (List.mem_flatMap.1 h).elim fun d ⟨hd, h'⟩ => (hnot d hd).1 h'
      have hb : start ∉ bottoms ρ₁ := fun h =>
        (List.mem_flatMap.1 h).elim fun d ⟨hd, h'⟩ => (hnot d hd).2 h'
      simp only [tops_append, tops_cons, startPiece, bottoms_append, bottoms_cons,
        List.cons_append] at heq
      obtain ⟨-, heq⟩ := (List.append_cons_inj_of_notMem_prefix ht hb).mp heq
      have hρ₂ : ∀ d ∈ ρ₂, d ∈ toPCP I := fun d hd =>
        hρ d (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
      exact complete_of_marked I ρ₂ I.start.top I.start.bottom hρ₂ (by
        rw [heq, sep_cons_starAfter_append])
    · -- without the start domino, tops begin with `⋆` and bottoms do not
      exfalso
      have hρ' (d : Domino (Marked α)) (hd : d ∈ ρ) :
          d = stopPiece ∨ ∃ e, (e ∈ I.dominoes ∧ 0 < e.top.length + e.bottom.length) ∧
            markPiece e = d := by
        simpa [toPCP, show d ≠ startPiece I.start from fun h => hs (h ▸ hd)] using hρ d hd
      have htop : ∀ x ∈ (tops ρ).head?, x = sep := head?_flatMap fun d hd => by
        rcases hρ' d hd with rfl | ⟨e, -, rfl⟩
        exacts [by simp [stopPiece], head?_starBefore e.top]
      have hbot : ∀ x ∈ (bottoms ρ).head?, x ≠ sep := head?_flatMap fun d hd => by
        rcases hρ' d hd with rfl | ⟨e, -, rfl⟩
        exacts [by simp [stopPiece], head?_starAfter e.bottom]
      obtain ⟨d, ρ', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hnil : tops (d :: ρ') = [] := by
        rcases h : (tops (d :: ρ')).head? with _ | x
        · exact List.head?_eq_none_iff.mp h
        · exact absurd (htop x h) (hbot x (heq ▸ h))
      rcases hρ' d List.mem_cons_self with rfl | ⟨e, ⟨-, hpos⟩, rfl⟩
      · simp [stopPiece, tops_cons] at hnil
      · rw [hnil] at heq
        cases ht : e.top <;> cases hb : e.bottom <;>
          simp [ht, hb, markPiece, tops_cons, bottoms_cons] at heq hnil hpos
  · rintro ⟨ds, hds, heq⟩
    obtain ⟨ht, hb⟩ := tops_filter ds
    refine ⟨startPiece I.start ::
        ((ds.filter fun d => 0 < d.top.length + d.bottom.length).map markPiece ++ [stopPiece]),
      List.cons_ne_nil _ _, fun d hd => ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_filter,
        List.not_mem_nil, or_false, toPCP] at hd ⊢
      rcases hd with rfl | ⟨e, ⟨he, hpos⟩, rfl⟩ | rfl
      exacts [Or.inl rfl, Or.inr (Or.inr ⟨e, ⟨hds e he, hpos⟩, rfl⟩), Or.inr (Or.inl rfl)]
    · simp only [tops_cons, tops_append, tops_map_markPiece, startPiece, bottoms_cons,
        bottoms_append, bottoms_map_markPiece, stopPiece, ht, hb, tops_nil, bottoms_nil,
        List.append_nil, List.cons_append, List.cons.injEq, true_and]
      rw [← List.append_assoc, ← starBefore_append, heq, ← List.append_assoc (starAfter _),
        ← starAfter_append, sep_cons_starAfter_append]

theorem primrec_starBefore [Primcodable α] : Primrec (starBefore : List α → List (Marked α)) :=
  Primrec.list_flatMap Primrec.id
    (Primrec.list_cons.comp (Primrec.const sep)
      (Primrec.list_cons.comp (Marked.primrec_letter.comp Primrec.snd)
        (Primrec.const []))).to₂

theorem primrec_starAfter [Primcodable α] : Primrec (starAfter : List α → List (Marked α)) :=
  Primrec.list_flatMap Primrec.id
    (Primrec.list_cons.comp (Marked.primrec_letter.comp Primrec.snd)
      (Primrec.const [sep])).to₂

theorem primrec_toPCP [Primcodable α] :
    Primrec (toPCP : MInstance α → List (Domino (Marked α))) := by
  have hstart : Primrec (startPiece : Domino α → Domino (Marked α)) :=
    Domino.primrec₂_mk.comp
      (Primrec.list_cons.comp (Primrec.const start) (primrec_starBefore.comp Domino.primrec_top))
      (Primrec.list_cons.comp (Primrec.const start)
        (Primrec.list_cons.comp (Primrec.const sep)
          (primrec_starAfter.comp Domino.primrec_bottom)))
  have hmark : Primrec (markPiece : Domino α → Domino (Marked α)) :=
    Domino.primrec₂_mk.comp (primrec_starBefore.comp Domino.primrec_top)
      (primrec_starAfter.comp Domino.primrec_bottom)
  have hpos : PrimrecPred fun d : Domino α => 0 < d.top.length + d.bottom.length :=
    Primrec.nat_lt.comp (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.list_length.comp Domino.primrec_top)
        (Primrec.list_length.comp Domino.primrec_bottom))
  have hfilter : Primrec fun I : MInstance α =>
      I.dominoes.filter fun d => 0 < d.top.length + d.bottom.length :=
    (Primrec.listFilter hpos).comp MInstance.primrec_dominoes
  exact Primrec.list_cons.comp (hstart.comp MInstance.primrec_start)
    (Primrec.list_cons.comp (Primrec.const stopPiece)
      (Primrec.list_map hfilter (hmark.comp Primrec.snd).to₂))

/-- MPCP reduces to PCP by a computable many-one reduction. -/
theorem mSolvable_manyOneReducible [Primcodable α] :
    (MInstance.Solvable : MInstance α → Prop) ≤₀ (Solvable : List (Domino (Marked α)) → Prop) :=
  ⟨toPCP, primrec_toPCP.to_comp, fun I => (solvable_toPCP_iff I).symm⟩

end Cslib.PostCorrespondence
