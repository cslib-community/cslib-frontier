/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Gate
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Contract
import CslibFrontier.Foundations.Data.List.Forall2

/-!
# The network of a formula in conjunctive normal form

The network evaluates a formula in conjunctive normal form on a bundle of red literal wires
[HearnDemaine2005, Section 3.1]. Every wire of the network is active when it points down.

Each clause is a row across the bundle. An accumulator starts at the first literal wire of the
clause (`Cslib.Complexity.NCL.QBF.Network.tapFirst`), then sweeps to the right, collecting each
further literal wire of the clause by an OR vertex (`Cslib.Complexity.NCL.QBF.Network.tap`) and
crossing the others. A literal wire is collected by converting it to blue and splitting it, by an
AND vertex, into its continuation and a red copy, which is converted to blue again. The values of
the clauses are joined by blue AND gates (`Cslib.Complexity.NCL.QBF.Network.conj`): two
conversions to red and an AND vertex.

`NCL.QBF.Network.Evaluation` constructs exact legal evaluations and executes them while
keeping the incoming literal and tail directions fixed.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Network.tapFirst`, `Cslib.Complexity.NCL.QBF.Network.tap`,
  `Cslib.Complexity.NCL.QBF.Network.conj`: the gadgets.
* `Cslib.Complexity.NCL.QBF.Network.row`, `Cslib.Complexity.NCL.QBF.Network.clause`,
  `Cslib.Complexity.NCL.QBF.Network.network`: the rows and the network, for `n` literal wires
  and the clauses given by the literal wires they mark, with the wires `r` beside on the right.

## Main results

* `Cslib.Complexity.NCL.QBF.Network.holds_tapFirst`, `Cslib.Complexity.NCL.QBF.Network.holds_tap`,
  `Cslib.Complexity.NCL.QBF.Network.holds_conj`: the contracts of the gadgets, checked on their
  boundaries: an active output needs the inputs it is computed from.
* `Cslib.Complexity.NCL.QBF.Network.holds_network`: the static soundness of the network
  [HearnDemaine2005, Lemma 2], composed from the contracts of the gadgets.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Network

open Diagram Gate

local notation "R" => Color.red
local notation "B" => Color.blue

/-- **The first collection** `[ℓ] → [ℓ', acc]`: the literal wire `ℓ` is converted to blue and
split into its continuation `ℓ'` and a red copy, which is converted to the blue accumulator. -/
@[expose] def tapFirst : Diagram Gate [R] [R, B] :=
  (gen conv).comp <| (pad [] (node [B] [R, R]) [R]).comp <|
    (pad [R] (gen conv) [R]).comp (pad [R, B] (gen cap) [])

/-- **A collection** `[acc, ℓ] → [ℓ', acc']`: the literal wire is collected as by `tapFirst`,
and an OR vertex joins its copy to the accumulator. -/
@[expose] def tap : Diagram Gate [B, R] [R, B] :=
  (pad [B] tapFirst []).comp <| (pad [] (swap B R) [B]).comp (pad [R] (node [B, B] [B]) [])

/-- **The conjunction** `[x, y] → [x ∧ y]`: both blue wires are converted to red, and an AND
vertex joins them. -/
@[expose] def conj : Diagram Gate [B, B] [B] :=
  ((gen vnoc).tensor (gen vnoc)).comp <| (pad [R] (swap R R) [R]).comp
    ((node [R, R] [B]).tensor (gen cap))

/-- The contract of `tapFirst`: the continuation and the copy need the literal. -/
@[expose] def TapFirstSpec : List Bool → List Bool → Prop
  | [l], [l', acc] => l' ≤ l ∧ acc ≤ l
  | _, _ => True

/-- The contract of `tap`: the continuation needs the literal, and the new accumulator needs the
old one or the literal. -/
@[expose] def TapSpec : List Bool → List Bool → Prop
  | [acc, l], [l', acc'] => l' ≤ l ∧ acc' ≤ (acc || l)
  | _, _ => True

/-- The contract of `conj`: the output needs both inputs. -/
@[expose] def ConjSpec : List Bool → List Bool → Prop
  | [x, y], [z] => z ≤ (x && y)
  | _, _ => True

instance : ∀ x y, Decidable (TapFirstSpec x y) := by
  intro x y; unfold TapFirstSpec; split <;> infer_instance

instance : ∀ x y, Decidable (TapSpec x y) := by
  intro x y; unfold TapSpec; split <;> infer_instance

instance : ∀ x y, Decidable (ConjSpec x y) := by
  intro x y; unfold ConjSpec; split <;> infer_instance

theorem holds_tapFirst : Holds Gate.interp tapFirst TapFirstSpec :=
  Holds.of_check 3 (by decide +kernel)

theorem holds_tap : Holds Gate.interp tap TapSpec :=
  Holds.of_check 3 (by decide +kernel)

theorem holds_conj : Holds Gate.interp conj ConjSpec :=
  Holds.of_check 3 (by decide +kernel)

/-! ### The rows and the network -/

/-- `n` red wires. -/
abbrev bundle (n : ℕ) : List Color := List.replicate n R

/-- The accumulator passes a literal wire: it collects it, or crosses it. -/
@[expose] def step (b : Bool) : Diagram Gate [B, R] [R, B] := if b then tap else swap B R

/-- **A row**: the accumulator sweeps across `n` literal wires, collecting those marked by `m`;
the wires `r` run down on the right. -/
@[expose] def row (r : List Color) : (n : ℕ) → List Bool →
    Diagram Gate ([B] ++ (bundle n ++ r)) (bundle n ++ ([B] ++ r))
  | 0, _ => Diagram.id ([B] ++ r)
  | n + 1, m => ((step (m.headD false)).tensor (Diagram.id (bundle n ++ r))).comp
      ((Diagram.id [R]).tensor (row r n m.tail))

/-- **A clause**: its accumulator starts at its first marked literal wire. The empty clause
starts a wire that is never active: a vertex that needs it. -/
@[expose] def clause (r : List Color) :
    (n : ℕ) → List Bool → Diagram Gate (bundle n ++ r) (bundle n ++ ([B] ++ r))
  | 0, _ => (node [] [B]).tensor (Diagram.id r)
  | n + 1, m =>
    if m.headD false then
      (tapFirst.tensor (Diagram.id (bundle n ++ r))).comp ((Diagram.id [R]).tensor (row r n m.tail))
    else (Diagram.id [R]).tensor (clause r n m.tail)

/-- The clauses `ms`, each joined by a conjunction to the value on the wire right of the
bundle. -/
@[expose] def conjoin (r : List Color) (n : ℕ) :
    List (List Bool) → Diagram Gate (bundle n ++ ([B] ++ r)) (bundle n ++ ([B] ++ r))
  | [] => Diagram.id _
  | m :: ms => ((clause ([B] ++ r) n m).comp
      ((Diagram.id (bundle n)).tensor (conj.tensor (Diagram.id r)))).comp (conjoin r n ms)

/-- **The network** of the clauses `ms`: the value of their conjunction appears on a wire right of
the bundle. The empty conjunction is a free wire. -/
@[expose] def network (r : List Color) (n : ℕ) :
    List (List Bool) → Diagram Gate (bundle n ++ r) (bundle n ++ ([B] ++ r))
  | [] => (Diagram.id (bundle n)).tensor ((gen start).tensor (Diagram.id r))
  | m :: ms => (clause r n m).comp (conjoin r n ms)

/-! ### The contracts of the rows and the network -/

/-- Whether a literal wire marked by `m` is active in `ls`. -/
@[expose] def hits : List Bool → List Bool → Bool
  | b :: m, l :: ls => (b && l) || hits m ls
  | _, _ => false

@[simp] theorem hits_nil_right (m : List Bool) : hits m [] = false := by cases m <;> rfl

theorem hits_cons (m : List Bool) (l : Bool) (ls : List Bool) :
    hits m (l :: ls) = (m.headD false && l || hits m.tail ls) := by
  cases m <;> simp [hits]

private theorem and_or_le {b a' a u v : Bool} (h : a' ≤ a) (h' : u ≤ v) :
    (b && a' || u) ≤ (b && a || v) := by
  revert h h'; revert b a' a u v; decide

/-- Fewer active literal wires hit less. -/
theorem hits_mono : ∀ (m : List Bool) {ls' ls : List Bool}, List.Forall₂ (· ≤ ·) ls' ls →
    hits m ls' ≤ hits m ls
  | _, _, _, .nil => by cases ‹List Bool› <;> exact le_rfl
  | [], _, _, .cons _ _ => le_rfl
  | _ :: m, _, _, .cons h hs => and_or_le h (hits_mono m hs)

/-- The contract of a step: the continuation needs the literal, and the new accumulator needs the
old one, or the literal if collected. -/
@[expose] def StepSpec (b : Bool) : List Bool → List Bool → Prop
  | [acc, l], [l', acc'] => l' ≤ l ∧ acc' ≤ (acc || (b && l))
  | _, _ => True

theorem holds_step (b : Bool) : Holds Gate.interp (step b) (StepSpec b) := by
  cases b
  · refine (Holds.swap B R).mono fun x _ hx _ h => ?_
    obtain ⟨acc, l, rfl⟩ := List.length_eq_two.1 hx
    subst h
    simp [StepSpec]
  · refine holds_tap.mono fun x y hx hy h => ?_
    obtain ⟨acc, l, rfl⟩ := List.length_eq_two.1 hx
    obtain ⟨l', acc', rfl⟩ := List.length_eq_two.1 hy
    simpa [StepSpec, TapSpec] using h

/-- The contract of a row: every continuation needs its literal, and the accumulator below needs
the one above or a marked literal. -/
@[expose] def RowSpec (n : ℕ) (m x y : List Bool) : Prop :=
  ∃ acc ls rs ls' acc', x = acc :: (ls ++ rs) ∧ y = ls' ++ (acc' :: rs) ∧ ls.length = n ∧
    List.Forall₂ (· ≤ ·) ls' ls ∧ acc' ≤ (acc || hits m ls)

private theorem le_or_or {acc acc₁ acc' u v : Bool} (h₁ : acc₁ ≤ (acc || u))
    (h₂ : acc' ≤ (acc₁ || v)) : acc' ≤ (acc || (u || v)) := by
  revert h₁ h₂; revert acc acc₁ acc' u v; decide

theorem holds_row (r : List Color) :
    ∀ (n : ℕ) (m : List Bool), Holds Gate.interp (row r n m) (RowSpec n m)
  | 0, _ => (Holds.id _).mono fun x _ hx _ h => by
    obtain ⟨acc, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
    exact ⟨acc, [], rs, [], acc, rfl, h.symm, rfl, .nil, by simp⟩
  | n + 1, m =>
    (((holds_step _).tensor_id _).comp ((holds_row r n m.tail).id_tensor [R])).mono <| by
    rintro _ _ - - ⟨_, ⟨x₁, y₁, _, rfl, rfl, hx₁, hy₁, hs⟩,
      ⟨w, _, _, hmid, rfl, hw, _, ls, rs, ls', acc', rfl, rfl, hls, hf, ha⟩⟩
    obtain ⟨acc, l, rfl⟩ := List.length_eq_two.1 hx₁
    obtain ⟨l', acc₁, rfl⟩ := List.length_eq_two.1 hy₁
    obtain ⟨_, rfl⟩ := List.length_eq_one_iff.1 hw
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hmid
    obtain ⟨rfl, rfl, rfl⟩ := hmid
    exact ⟨acc, l :: ls, rs, _ :: ls', acc', rfl, rfl, by simp [hls], .cons hs.1 hf,
      by rw [hits_cons]; exact le_or_or hs.2 ha⟩

/-- The wire started by the empty clause is never active. -/
theorem holds_dead : Holds Gate.interp (node [] [B]) fun _ y => y = [false] :=
  Holds.of_check 1 (by decide +kernel)

/-- The contract of a clause: every continuation needs its literal, and the value of the clause
needs a marked literal. -/
@[expose] def ClauseSpec (n : ℕ) (m x y : List Bool) : Prop :=
  ∃ ls rs ls' v, x = ls ++ rs ∧ y = ls' ++ (v :: rs) ∧ ls.length = n ∧
    List.Forall₂ (· ≤ ·) ls' ls ∧ v ≤ hits m ls

theorem holds_clause (r : List Color) :
    ∀ (n : ℕ) (m : List Bool), Holds Gate.interp (clause r n m) (ClauseSpec n m)
  | 0, _ => (holds_dead.tensor_id r).mono <| by
    rintro _ _ - - ⟨x', _, z, rfl, rfl, hx', -, rfl⟩
    exact ⟨[], z, [], false, by simp [List.eq_nil_of_length_eq_zero hx'], rfl, rfl, .nil,
      Bool.false_le _⟩
  | n + 1, m => by
    unfold clause
    split_ifs with h
    · refine ((holds_tapFirst.tensor_id _).comp ((holds_row r n m.tail).id_tensor [R])).mono ?_
      rintro _ _ - - ⟨_, ⟨x₁, y₁, _, rfl, rfl, hx₁, hy₁, hs⟩,
        ⟨w, _, _, hmid, rfl, hw, _, ls, rs, ls', acc', rfl, rfl, hls, hf, ha⟩⟩
      obtain ⟨l, rfl⟩ := List.length_eq_one_iff.1 hx₁
      obtain ⟨l', acc₁, rfl⟩ := List.length_eq_two.1 hy₁
      obtain ⟨_, rfl⟩ := List.length_eq_one_iff.1 hw
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hmid
      obtain ⟨rfl, rfl, rfl⟩ := hmid
      refine ⟨l :: ls, rs, _ :: ls', acc', rfl, rfl, by simp [hls], .cons hs.1 hf, ?_⟩
      rw [hits_cons, h]
      simpa using le_or_or (acc := false) (u := l) (by simpa using hs.2) ha
    · refine ((holds_clause r n m.tail).id_tensor [R]).mono ?_
      rintro _ _ - - ⟨w, _, _, rfl, rfl, hw, ls, rs, ls', v, rfl, rfl, hls, hf, hv⟩
      obtain ⟨l, rfl⟩ := List.length_eq_one_iff.1 hw
      refine ⟨l :: ls, rs, l :: ls', v, rfl, rfl, by simp [hls], .cons le_rfl hf, ?_⟩
      rw [hits_cons, Bool.eq_false_iff.2 h]
      simpa using hv

private theorem and_le_and {a a' b b' : Bool} (h : a' ≤ a) (h' : b' ≤ b) :
    (a' && b') ≤ (a && b) := by
  revert h h'; revert a a' b b'; decide

/-- A CNF evaluated on fewer active literal wires has no greater value. -/
theorem all_hits_mono (ms : List (List Bool)) {ls' ls : List Bool}
    (h : List.Forall₂ (· ≤ ·) ls' ls) : ms.all (hits · ls') ≤ ms.all (hits · ls) := by
  induction ms with
  | nil => exact le_rfl
  | cons m ms ih => simpa only [List.all_cons] using and_le_and (hits_mono m h) ih

private theorem conj_le {w' c v b h u' u : Bool} (hw : w' ≤ (c && u')) (hc : c ≤ (v && b))
    (hv : v ≤ h) (hu : u' ≤ u) : w' ≤ (b && (h && u)) := by
  revert hw hc hv hu; revert w' c v b h u' u; decide

private theorem exists_split (n : ℕ) (r : List Color) {x : List Bool}
    (hx : x.length = (bundle n ++ ([B] ++ r)).length) :
    ∃ ls w rs, x = ls ++ w :: rs ∧ ls.length = n := by
  have hn : n < x.length := by simp at hx; omega
  exact ⟨x.take n, x[n], x.drop (n + 1),
    by rw [← List.drop_eq_getElem_cons hn, List.take_append_drop], by simp; omega⟩

/-- The contract of the further clauses: every continuation needs its literal, and the value of
the conjunction needs the value before and every clause. -/
@[expose] def ConjoinSpec (n : ℕ) (ms : List (List Bool)) (x y : List Bool) : Prop :=
  ∃ ls w rs ls' w', x = ls ++ (w :: rs) ∧ y = ls' ++ (w' :: rs) ∧ ls.length = n ∧
    List.Forall₂ (· ≤ ·) ls' ls ∧ w' ≤ (w && ms.all (hits · ls))

theorem holds_conjoin (r : List Color) (n : ℕ) :
    ∀ ms : List (List Bool), Holds Gate.interp (conjoin r n ms) (ConjoinSpec n ms)
  | [] => (Holds.id _).mono fun x _ hx _ h => by
    obtain ⟨ls, w, rs, rfl, hls⟩ := exists_split n r hx
    exact ⟨ls, w, rs, ls, w, rfl, h.symm, hls, List.forall₂_refl ls, by simp⟩
  | m :: ms => (((holds_clause ([B] ++ r) n m).comp
      ((holds_conj.tensor_id r).id_tensor (bundle n))).comp (holds_conjoin r n ms)).mono <| by
    rintro _ _ - - ⟨_, ⟨_, ⟨ls, rs₀, ls', v, rfl, rfl, hls, hf, hv⟩,
      ⟨z, _, _, h₁, rfl, hz, x'', y'', q, rfl, rfl, hx'', hy'', hc⟩⟩,
      ⟨ls₂, w₂, rs₂, ls'', w', h₂, rfl, hls₂, hf', hw'⟩⟩
    obtain ⟨rfl, h₃⟩ := List.append_inj h₁ (by simp [hz, hf.length_eq, hls])
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hx''
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 hy''
    obtain ⟨rfl, rfl⟩ := List.cons.inj h₃
    obtain ⟨rfl, h₄⟩ := List.append_inj h₂ (by simp [hf.length_eq, hls, hls₂])
    obtain ⟨rfl, rfl⟩ := List.cons.inj h₄
    exact ⟨ls, b, q, ls'', w', rfl, rfl, hls, hf'.trans hf,
      by simpa only [List.all_cons] using conj_le hw' hc hv (all_hits_mono ms hf)⟩

/-- The contract of the network: every continuation needs its literal, and the value of the
formula needs every clause to have an active marked literal. -/
@[expose] def NetSpec (n : ℕ) (ms : List (List Bool)) (x y : List Bool) : Prop :=
  ∃ ls rs ls' v, x = ls ++ rs ∧ y = ls' ++ (v :: rs) ∧ ls.length = n ∧
    List.Forall₂ (· ≤ ·) ls' ls ∧ v ≤ ms.all (hits · ls)

/-- **Static soundness of the network** [HearnDemaine2005, Lemma 2]: its value is active only if
every clause has an active marked literal wire. -/
theorem holds_network (r : List Color) (n : ℕ) :
    ∀ ms : List (List Bool), Holds Gate.interp (network r n ms) (NetSpec n ms)
  | [] => ((Holds.tensor_id r (C := fun _ _ => True) fun _ _ => trivial).id_tensor
      (bundle n)).mono <| by
    rintro _ _ - - ⟨z, _, _, rfl, rfl, hz, x', y', q, rfl, rfl, hx', hy', -⟩
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.1 hy'
    exact ⟨z, q, z, v, by simp [List.eq_nil_of_length_eq_zero hx'], rfl, by simpa using hz,
      List.forall₂_refl z, by simp⟩
  | m :: ms => ((holds_clause r n m).comp (holds_conjoin r n ms)).mono <| by
    rintro _ _ - - ⟨_, ⟨ls, rs, ls', v, rfl, rfl, hls, hf, hv⟩,
      ⟨ls₂, w, rs₂, ls'', w', h, rfl, hls₂, hf', hw'⟩⟩
    obtain ⟨rfl, h'⟩ := List.append_inj h (by simp [hf.length_eq, hls, hls₂])
    obtain ⟨rfl, rfl⟩ := List.cons.inj h'
    exact ⟨ls, rs, ls'', w', rfl, rfl, hls, hf'.trans hf,
      by simpa only [List.all_cons] using le_trans hw' (and_le_and hv (all_hits_mono ms hf))⟩

end Cslib.Complexity.NCL.QBF.Network
