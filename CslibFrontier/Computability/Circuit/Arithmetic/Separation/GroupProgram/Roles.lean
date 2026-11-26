/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Law
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Transducer
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Units
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.DSteps
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# The program of a role

A role of a law (`Cut.Law`) is played by the program GROUP of [AnthropicVPVNP2026] on the units
of a trie. The units at the keys of every slot of the role are put together to a stream of bits;
the table of the role, read as a transducer (`roleTable`), runs on the streams for `tt * ub` steps,
guessing an index and the strings on the channels and multiplying by the entries of the table; the
string that it emits on every channel, closed by the bit `1`, is cut into units, which are written
at the keys of the channel (`roleSem`).

## Main definitions

* `termOf`: a term of the interpreter with a given value.
* `slotList`, `channelList`, `slotIndex`: the slots and the channels of a role, as lists.
* `RoleChoice`: what a role guesses in one block: an index and a string on every channel.
* `roleTable`: the table of a role as a transducer.
* `roleSem`: what a role does with a trie.

## Main results

* `val_termOf`: the value of `termOf`.
* `exists_formula_roleSem`: one formula plays a role.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54); this file formalizes programs
of that evaluator, not the theorem. Ported from the source modules `Nc.Grp.Role` and
`Nc.Grp.RoleProg`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A term whose value is `a`, if there is one, and otherwise an arbitrary term. -/
noncomputable def termOf (θ : List Bool → A) (a : A) : WE :=
  @Classical.epsilon WE ⟨.zero⟩ fun e => e.val θ = a

theorem val_termOf {a : A} (h : ∃ e : WE, e.val θ = a) : (termOf θ a).val θ = a :=
  Classical.epsilon_spec h

section Role

variable (L : Cut.Law A) (p : L.Role)

/-- The slots of a role, as a list. -/
@[expose] noncomputable def slotList : List (L.SlotAt p) := Finset.univ.toList

/-- The channels of a role, as a list. -/
@[expose] noncomputable def channelList : List (L.ChannelAt p) := Finset.univ.toList

/-- The position of a slot in `slotList`. -/
@[expose] noncomputable def slotIndex (e : L.SlotAt p) : Fin (slotList L p).length :=
  ⟨(slotList L p).idxOf e, List.idxOf_lt_length_of_mem (Finset.mem_toList.2 (Finset.mem_univ e))⟩

/-- What a role guesses in one block: an index of the law and a string on every channel. -/
abbrev RoleChoice : Type := Σ i : L.Index, ∀ ν : L.ChannelAt p, BitString (L.length i ν)

variable (θ) in
/-- The table of a role as a transducer with one control, an input list for every slot and an
output list for every channel: a choice is a `RoleChoice`, whose weight is a term (`termOf`) for
the entry of the table at the bits read and the guessed strings, and which pushes, on every
channel, the label of the index followed by the string on the channel, reversed. -/
@[expose] noncomputable def roleTable (_ : Fin 1) (v : Fin (slotList L p).length → Bool) :
    List (Transducer.Choice 1 (channelList L p).length Bool) :=
  (Finset.univ : Finset (RoleChoice L p)).toList.map fun z =>
    ⟨termOf θ (L.table p z.1 (fun e => v (slotIndex L p e)) z.2), 0,
      fun j => (List.ofFn (L.label z.1) ++ List.ofFn (z.2 ((channelList L p).get j))).reverse⟩

variable (θ) in
/-- What a role does with a trie whose entry at a key `k` has the bits `ct k`: if no unit at the
keys of the slots is empty, the transducer of the role runs for `tt * ub` steps on the streams of
the slots, and the strings that it emits, reversed and closed by the bit `1`, are written at the
keys of the channels; if a unit is empty, nothing. -/
@[expose] noncomputable def roleSem (ub : ℕ) (ct : List Bool → List Bool) (tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree) : List (A × Tree) :=
  if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then
    (Transducer.run θ (roleTable θ L p) (tt * ub)
      ⟨0, fun i => (slots.map fun es => es.reverse.flatMap ct).getD i [], fun _ => []⟩).weightedBind
      fun s => (putStrings ub keys (List.ofFn fun j => (s.outputs j).reverse ++ [true]) t).map
        ((1 : A), ·)
  else []

end Role

/-! ### Streams -/

/-- Put the unit at a key in front of a stream: the argument is (key, (trie, stream)). -/
private def streamStep : Fm := .ite (getF (.hd .id) (.hd (.tl .id)))
  (.cons (.hd (.tl .id)) (appF (getF (.hd .id) (.hd (.tl .id))) (.tl (.tl .id)))) .fail

/-- The stream of the units at a list of keys: the argument is (trie, keys). -/
private def streamF : Fm :=
  lett (foldF streamStep (.cons (.hd .id) (.quote .nil)) (.tl .id)) (.tl .id)

/-- The stream of the units at the keys of one slot of several: the argument is (keys, (trie,
streams)). -/
private def streamsStep : Fm :=
  .cons (.hd (.tl .id)) (.cons (lett (.cons (.hd (.tl .id)) (.hd .id)) streamF) (.tl (.tl .id)))

/-- The streams of the slots: the argument is (trie, lists of keys). -/
private def streamsF : Fm := lett (foldF streamsStep (.cons (.hd .id) (.quote .nil)) (.tl .id))
  (foldF .id (.quote .nil) (.tl .id))

private theorem foldl_append_flatMap (ct : List Bool → List Bool) (es : List (List Bool)) :
    ∀ acc, es.foldl (fun acc k => ct k ++ acc) acc = es.reverse.flatMap ct ++ acc := by
  induction es with
  | nil => simp
  | cons e es ih => simp [ih]

private theorem streamF_does {ub : ℕ} {t : Tree} (ht : StoreBound ub t) (es : List (List Bool)) :
    Does θ streamF (.cons t (wordsEnc es))
      ((if ∀ k ∈ es, (tget k t).path ≠ [] then
        [((1 : A), es.reverse.flatMap fun k => (tget k t).path)] else []).map (Prod.map id ofBits))
      (400 * (es.map fun k => ub + k.length + 1).sum + 60) := by
  have h1 := foldF_does_enc (θ := θ) (encE := ofBits) (xs := es) (x := .cons t (wordsEnc es))
    (enc := fun acc => .cons t (ofBits acc)) (s₀ := [])
    (f := fun k acc => if (tget k t).path ≠ [] then [((1 : A), (tget k t).path ++ acc)] else [])
    (Inv := fun _ _ => True) (d := fun k => 370 * (ub + k.length + 1)) (step := streamStep)
    ((Gives.id _).hd.cons (Gives.quote _ _)) (Gives.id _).tl (fun k _ acc _ _ => by
      set y := Tree.cons (ofBits k) (.cons t (ofBits acc))
      have g := getF_gives (θ := θ) (p := ofBits k) (t := t) (Gives.id y).hd (Gives.id y).tl.hd
      simp only [path_ofBits, len_ofBits] at g
      rw [(ht.tget k).1] at g
      have hk := (ht.tget k).2
      refine ⟨?_, fun _ _ => trivial⟩
      by_cases h : (tget k t).path = []
      · rw [h] at g
        exact ((Does.ite_false g (Does.fail y)).of_eq (by simp [h])).mono (by omega)
      · exact ((Does.ite_true g (by cases e : (tget k t).path <;> simp_all [ofBits])
          ((Gives.id y).tl.hd.cons (appF_gives_ofBits g (Gives.id y).tl.tl))).of_eq
          (by simp [h, y])).mono (by omega)) trivial
  rw [List.weightedFoldl_ite (fun k => (tget k t).path ≠ []) (fun k acc => (tget k t).path ++ acc),
    foldl_append_flatMap, List.append_nil] at h1
  have h2 := Does.lett_enc_enc (G := .tl .id) (f := fun acc => [((1 : A), acc)]) (enc' := ofBits)
    (d := 2) h1 fun _ _ => (Gives.id _).tl
  refine (h2.of_eq (by split_ifs <;> simp [List.weightedBind])).mono ?_
  have := List.sum_le_sum (l := es) (f := fun k => 370 * (ub + k.length + 1) + 30)
    (g := fun k => 400 * (ub + k.length + 1)) fun k _ => by omega
  rw [List.sum_map_mul_left] at this
  omega

/-- The streams of the slots. -/
private theorem streamsF_does {ub : ℕ} {t : Tree} (ht : StoreBound ub t)
    (slots : List (List (List Bool))) :
    Does θ streamsF (.cons t (keysEnc slots))
      ((if ∀ es ∈ slots, ∀ k ∈ es, (tget k t).path ≠ [] then [((1 : A), slots.map fun es =>
        es.reverse.flatMap fun k => (tget k t).path)] else []).map (Prod.map id wordsEnc))
      (500 * (putCost ub slots + 1)) := by
  set ct := fun k => (tget k t).path
  have h1 := foldF_does_enc (θ := θ) (encE := wordsEnc) (xs := slots)
    (x := .cons t (keysEnc slots)) (enc := fun acc => .cons t (wordsEnc acc)) (s₀ := [])
    (f := fun es acc => if ∀ k ∈ es, ct k ≠ [] then [((1 : A), es.reverse.flatMap ct :: acc)]
      else []) (Inv := fun _ _ => True)
    (d := fun es => 400 * (es.map fun k => ub + k.length + 1).sum + 100) (step := streamsStep)
    ((Gives.id _).hd.cons (Gives.quote _ _)) (Gives.id _).tl (fun es _ acc _ _ => by
      set y := Tree.cons (wordsEnc es) (.cons t (wordsEnc acc))
      refine ⟨((Does.cons (Gives.id y).tl.hd (Does.cons (Does.of_gives ((Gives.id y).tl.hd.cons
        (Gives.id y).hd) (streamF_does ht es)) (Gives.id y).tl.tl)).of_eq ?_).mono (by omega),
        fun _ _ => trivial⟩
      split_ifs <;> simp [y, ct, wordsEnc, listT]) trivial
  rw [List.weightedFoldl_ite] at h1
  have e : ∀ (l : List (List (List Bool))) acc,
      l.foldl (fun acc es => es.reverse.flatMap ct :: acc) acc =
        (l.map fun es => es.reverse.flatMap ct).reverse ++ acc := fun l => by
    induction l <;> simp_all
  rw [e, List.append_nil] at h1
  have h2 := Does.lett_enc_enc (G := foldF .id (.quote .nil) (.tl .id))
    (f := fun acc => [((1 : A), acc.reverse)]) (enc' := wordsEnc) (d := slots.length * 31 + 25) h1
    fun b hb => by
      have hl : b.2.length = slots.length := by split_ifs at hb <;> simp_all
      have := rev_gives (θ := θ) (xs := b.2.map ofBits) (Gives.quote (listT [])
        (.cons t (wordsEnc b.2))) (Gives.id _).tl
      rw [List.append_nil, ← List.map_reverse, List.length_map, hl] at this
      exact this.mono (by omega)
  refine (h2.of_eq (by split_ifs <;> simp [List.weightedBind])).mono ?_
  have h3 := List.sum_le_sum (l := slots)
    (f := fun es => 400 * (es.map fun k => ub + k.length + 1).sum + 100 + 30)
    (g := fun es => 400 * ((es.map fun k => ub + k.length + 1).sum + 1)) fun k _ => by omega
  have h4 := List.length_le_sum_of_one_le (slots.map fun es =>
    (es.map fun k => ub + k.length + 1).sum + 1) (by simp)
  simp only [List.sum_map_mul_left, List.length_map, putCost] at h3 h4 ⊢
  omega

/-! ### The number of steps and the end -/

/-- The number `tt * ub` of steps: the argument is (`num ub`, (trie, (`num tt`, …))). -/
private def yardF : Fm := .tl (foldF (.cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id))))
  (.cons (.hd .id) (.quote .nil)) (.hd (.tl (.tl .id))))

private theorem yardF_gives (ub tt : ℕ) (t y : Tree) :
    Gives θ yardF (.cons (num ub) (.cons t (.cons (num tt) y))) (num (tt * ub))
      (tt * (62 * ub + 100) + 60) := by
  have hy : Gives θ (.hd (.tl (.tl .id))) (.cons (num ub) (.cons t (.cons (num tt) y))) (num tt)
    4 := (Gives.id _).tl.tl.hd
  have h := foldF_gives_enc (θ := θ) (encE := fun _ : Unit => (.nil : Tree))
    (enc := fun k : ℕ => .cons (num ub) (num k)) (s₀ := 0) (g := fun _ k => ub + k)
    (Inv := fun _ _ => True) (d := fun _ => 62 * ub + 60) (xs := List.replicate tt ())
    (step := .cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id))))
    (x := .cons (num ub) (.cons t (.cons (num tt) y))) ((Gives.id _).hd.cons (Gives.quote _ _))
    (by simpa [← num_eq_listT_replicate] using hy) (fun _ _ k _ _ => by
      have ga : Gives θ (.hd (.tl .id)) (.cons .nil (.cons (num ub) (num k)))
          (listT (List.replicate ub .nil)) 3 :=
        num_eq_listT_replicate ub ▸ (Gives.id _).tl.hd
      have gb : Gives θ (.tl (.tl .id)) (.cons .nil (.cons (num ub) (num k)))
          (listT (List.replicate k .nil)) 3 :=
        num_eq_listT_replicate k ▸ (Gives.id _).tl.tl
      have g := appF_gives ga gb
      rw [← List.replicate_add, ← num_eq_listT_replicate, List.length_replicate] at g
      exact ⟨((Gives.id _).tl.hd.cons g).mono (by omega), trivial⟩) trivial
  have e : ∀ tt m, (List.replicate tt ()).foldl (fun k _ => ub + k) m = tt * ub + m := fun tt => by
    induction tt with
    | zero => simp
    | succ tt ih => intro m; rw [List.replicate_succ, List.foldl_cons, ih]; ring
  rw [e, add_zero] at h
  refine h.tl.mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  nlinarith

/-- The arguments of the writing of the strings that a role emits: the argument is ((`num ub`,
(trie, (`num tt`, (slots, keys)))), state of the transducer). -/
private def endF : Fm := .cons (.hd (.hd .id)) (.cons (.tl (.tl (.tl (.tl (.hd .id)))))
  (.cons (mapF (foldF .id (.quote (ofBits [true])) (.tl .id)) (.quote .nil) (.tl (.tl (.tl .id))))
    (.hd (.tl (.hd .id)))))

private theorem endF_gives {nC nI nO m : ℕ} (ub : ℕ) (t y sl ks : Tree)
    (s : Transducer.State nC nI nO Bool) (hm : ∀ j, (s.outputs j).length ≤ m) :
    Gives θ endF (.cons (.cons (num ub) (.cons t (.cons y (.cons sl ks)))) (s.enc bit))
      (.cons (num ub) (.cons ks (.cons (wordsEnc (List.ofFn fun j => (s.outputs j).reverse ++
        [true])) t))) (nO * (31 * m + 70) + 50) := by
  have h := mapF_gives (θ := θ) (step := foldF .id (.quote (ofBits [true])) (.tl .id))
    (g := fun y => ofBits (y.path.reverse ++ [true])) (d := fun _ => 31 * m + 30)
    (Gives.quote .nil (.cons (.cons (num ub) (.cons t (.cons y (.cons sl ks)))) (s.enc bit)))
    (Gives.id _).tl.tl.tl fun z hz => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
      have := rev_gives_ofBits (θ := θ) (Gives.quote (ofBits [true]) _)
        (listT_ofBits (s.outputs j) ▸ (Gives.id (.cons .nil (listT ((s.outputs j).map bit)))).tl)
      rw [listT_ofBits, path_ofBits]
      exact this.mono (by have := hm j; omega)
  simp only [wordsEnc, List.map_ofFn, Function.comp_def, listT_ofBits, path_ofBits] at h ⊢
  refine ((Gives.id _).hd.hd.cons ((Gives.id _).hd.tl.tl.tl.tl.cons (h.cons
    (Gives.id _).hd.tl.hd))).mono ?_
  simp only [List.ofFn_const, List.sum_replicate, smul_eq_mul]
  nlinarith

/-! ### The role -/

/-- **One formula plays a role.** Its argument is (`num ub`, (trie, (`num tt`, (keys of the slots,
keys of the channels)))); the trie holds units of at most `ub` bits. -/
theorem exists_formula_roleSem (L : Cut.Law A) (p : L.Role) : ∃ F κ, ∀ (ub tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree), StoreBound ub t →
      slots.length = (slotList L p).length →
      Does θ F (.cons (num ub) (.cons t (.cons (num tt) (.cons (keysEnc slots) (keysEnc keys)))))
        (roleSem θ L p ub (fun k => (tget k t).path) tt slots keys t)
        (κ * (tt * (ub + 1) + putCost ub slots + putCost ub keys + 1)) := by
  obtain ⟨R, κ, hR⟩ := Transducer.exists_formula_run (θ := θ) bit (roleTable θ L p)
  obtain ⟨κ', hκ'⟩ := Transducer.exists_length_le_of_mem_run (θ := θ) (roleTable θ L p)
  obtain ⟨P, hP⟩ := exists_formula_putStrings (A := A) (θ := θ)
  set nO := (channelList L p).length
  refine ⟨lett (.cons .id (lett (.cons yardF (.cons (.quote (num 0)) (.cons (lett (.cons (.hd
    (.tl .id)) (.hd (.tl (.tl (.tl .id))))) streamsF) (.quote (listT (List.replicate nO .nil))))))
    R)) (lett endF P), κ + nO * (31 * κ' + 100) + 2000, fun ub tt slots keys t ht hsl => ?_⟩
  set x := Tree.cons (num ub) (.cons t (.cons (num tt) (.cons (keysEnc slots) (keysEnc keys))))
  set ct := fun k => (tget k t).path
  set bs := slots.map fun es => es.reverse.flatMap ct
  let s₀ : Transducer.State 1 (slotList L p).length nO Bool :=
    ⟨0, fun i => bs.getD i [], fun _ => []⟩
  have hs₀ : s₀.enc bit = .cons (num 0) (.cons (wordsEnc bs) (listT (List.replicate nO .nil))) := by
    have e : (List.ofFn fun i : Fin (slotList L p).length => ofBits (bs.getD i [])) =
        bs.map ofBits := List.ext_getElem (by simp [bs, hsl]) fun i h1 h2 => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]
    simp only [Transducer.State.enc, s₀, e, List.map_nil, List.ofFn_const]
    rfl
  have h1 := Does.cons (yardF_gives (θ := θ) ub tt t _) (Does.cons (Gives.quote (num 0) x)
    (Does.cons (Does.of_gives ((Gives.id x).tl.hd.cons (Gives.id x).tl.tl.tl.hd)
      (streamsF_does (A := A) ht slots)) (Gives.quote (listT (List.replicate nO .nil)) x)))
  have h2 := Does.lett_enc_enc (G := R) (enc := fun s => .cons (num (tt * ub)) (s.enc bit))
    (l := if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then [((1 : A), s₀)] else [])
    (f := Transducer.run θ (roleTable θ L p) (tt * ub)) (enc' := Transducer.State.enc bit)
    (d := κ * (tt * ub + 1)) (h1.of_eq (by split_ifs <;> simp [hs₀, bs, ct])) fun b _ => hR _ b.2
  have h3 := Does.letk_enc (G := lett endF P) (f := fun s => (putStrings ub keys
    (List.ofFn fun j => (s.outputs j).reverse ++ [true]) t).map ((1 : A), ·))
    (d := nO * (31 * (κ' * (tt * ub)) + 70) + 50 + 600 * (putCost ub keys + 1) + 2) h2
    fun b hb => by
      obtain ⟨a, ha, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 hb
      have ha2 : a.2 = s₀ := by split_ifs at ha <;> simp_all
      rw [ha2] at hr
      exact Does.of_gives
        (endF_gives ub t _ _ _ r.2 (fun j => hκ' (tt * ub) s₀ (fun _ => rfl) r hr j))
        (hP ub keys _ t)
  refine (h3.of_eq ?_).mono ?_
  · simp only [roleSem]
    split_ifs
    · rw [List.weightedBind_singleton_one]
    · rfl
  · have hN1 : tt * ub ≤ tt * (ub + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
    have hN2 : tt * (62 * ub + 100) ≤ 100 * (tt * (ub + 1)) := by nlinarith
    set N := tt * (ub + 1) + putCost ub slots + putCost ub keys + 1 with hN
    have b2 : κ' * (tt * ub) ≤ κ' * N := Nat.mul_le_mul_left _ (by omega)
    have b3 : κ * (tt * ub + 1) ≤ κ * N := Nat.mul_le_mul_left _ (by omega)
    have b4 : nO * (31 * (κ' * (tt * ub)) + 70) ≤ nO * (31 * (κ' * N) + 100 * N) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (κ + nO * (31 * κ' + 100) + 2000) * N =
        κ * N + nO * (31 * (κ' * N) + 100 * N) + 2000 * N := by ring
    rw [e]
    omega

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
