/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Roles
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Segments
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Run
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Guess
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# The program of a base party

A base party of the evaluator of [AnthropicVPVNP2026] is a block of the automaton or a part of the
input. A block simulates `T` steps of the automaton between two given states: the automaton is
read as a transducer (`simTable`) that guesses a letter and a next state in every step and pushes
the code of the letter on the output list of the side of its channel (`simSem`). An input part
puts the codes of its letters on the side `false` of the input (`inputOutputs`). Then the letters
of every tape are cut into segments for the partners, and the strings that the partners get are
written into the trie as units; the same is done with the letters of the other sides for the
strings that the party reads (`packSem`).

## Main definitions

* `channelSide`, `tapes`, `tapeCount`, `outputSide`: the tapes and their sides.
* `Outputs`: the output lists of a simulation.
* `letterCode`, `letterPush`, `separator`: the codes of the letters, and the separator.
* `simTable`, `simSem`: the automaton as a transducer, and a simulation.
* `inputOutputs`: the output lists of an input part.
* `writeItems`, `readItems`, `cutPut`, `packSem`: cutting the letters and writing the units.

## Main results

* `StoreBound.of_mem_packSem`: writing keeps the bound on the units.
* `exists_formula_block`, `exists_formula_input`: one formula makes a block, and one formula an
  input part.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54); this file formalizes programs
of that evaluator, not the theorem. Ported from the source modules `Nc.Grp.Base`, `Nc.Grp.BaseProg`
and `Nc.Grp.Pack`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The tape of a channel and its side; the input channel is the side `true` of `none`. -/
@[expose] def channelSide {S : Type} : Tape.Ch S Unit → Option S × Bool
  | .tp s b => (some s, b)
  | .inp _ => (none, true)

/-- The code of a letter. -/
@[expose] def letterCode {Γ : Type} {c : ℕ} (cb : Option Γ → Fin c → Bool) (a : Γ) : List Bool :=
  List.ofFn (cb (some a))

/-- The separator: the code of `none`. -/
@[expose] def separator {Γ : Type} {c : ℕ} (cb : Option Γ → Fin c → Bool) : List Bool :=
  List.ofFn (cb none)

section Tapes

variable (S : Type) [Fintype S]

/-- The tapes, `none` being the input, in a fixed order. -/
@[expose] noncomputable def tapes : List (Option S) := Finset.univ.toList

/-- The number of tapes, with the input. -/
noncomputable abbrev tapeCount : ℕ := (tapes S).length

/-- Output lists of a simulation: one for every side of every tape, the sides `false` first. -/
abbrev Outputs : Type := Fin (tapeCount S + tapeCount S) → List (List Bool)

variable {S}

/-- Output lists as a tree. -/
private noncomputable def Outputs.enc (o : Outputs S) : Tree :=
  listT (List.ofFn fun j => wordsEnc (o j))

/-- The tape and the side of an output list. -/
@[expose] noncomputable def outputSide (j : Fin (tapeCount S + tapeCount S)) : Option S × Bool :=
  Fin.addCases (fun i => ((tapes S).get i, false)) (fun i => ((tapes S).get i, true)) j

/-- The tapes to cut for the strings that a base party writes: for every tape, the last first, the
flags of its row and the letters on its side `false`. -/
@[expose] noncomputable def writeItems (flags : List (List ℕ)) (o : Outputs S) : List CutItem :=
  List.ofFn fun i : Fin (tapeCount S) => ⟨flags.getD i.rev [], o (Fin.castAdd _ i.rev)⟩

/-- The tapes to cut for the strings that a base party reads: for every tape, the last first, the
flag `2` for each of `m` partners and the letters on its side `true`. -/
@[expose] noncomputable def readItems (m : ℕ) (o : Outputs S) : List CutItem :=
  List.ofFn fun i : Fin (tapeCount S) => ⟨List.replicate m 2, o (Fin.natAdd _ i.rev)⟩

variable (A) in
/-- Cut the letters of the tapes `items` for `m` partners, each starting from the closing bit `1`,
and write the strings that the partners get, in their order, at the lists of keys `kss`. -/
@[expose] def cutPut (sep : List Bool) (ub : ℕ) (items : List CutItem) (m : ℕ)
    (kss : List (List (List Bool))) (t : Tree) : List (A × Tree) :=
  (cutTapes A sep items (List.replicate m [true])).weightedBind fun s =>
    (putStrings ub kss s.reverse t).map ((1 : A), ·)

variable (A) in
/-- What a base party with the output lists `o` does with a trie: it writes the units of the
strings to its partners, then those of the strings from its partners. -/
@[expose] noncomputable def packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outputs S)
    (t : Tree) : List (A × Tree) :=
  (cutPut A sep ub (writeItems B.flags o) B.writeKeys.length B.writeKeys t).weightedBind fun t1 =>
    cutPut A sep ub (readItems B.writeKeys.length o) B.writeKeys.length B.readKeys t1

theorem StoreBound.of_mem_packSem {sep : List Bool} {ub : ℕ} {B : Body} {o : Outputs S}
    {t : Tree} {q : A × Tree} (h : StoreBound ub t) (hq : q ∈ packSem A sep ub B o t) :
    StoreBound ub q.2 := by
  have hcp : ∀ {items m kss t} {q : A × Tree}, StoreBound ub t →
      q ∈ cutPut A sep ub items m kss t → StoreBound ub q.2 := fun ht hq => by
    obtain ⟨a, -, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 hq
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hr
    exact ht.of_mem_putStrings ht'
  obtain ⟨a, ha, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 hq
  exact hcp (q := r) (hcp h ha) hr

variable [DecidableEq S]

/-- The output lists of an input part with the codes `part` of its letters: they are on the side
`false` of the input. -/
@[expose] noncomputable def inputOutputs (part : List (List Bool)) : Outputs S :=
  fun j => if outputSide j = (none, false) then part else []

end Tapes

section Automaton

variable {Γ S Q : Type} [Fintype Γ] [Fintype S] [DecidableEq S] [Fintype Q] {c : ℕ}

/-- What a letter of the automaton pushes on an output list: its code, if the output list is the
side of its channel, and nothing otherwise or for the idle letter. -/
@[expose] noncomputable def letterPush (cb : Option Γ → Fin c → Bool) :
    Tape.Letter S Unit Γ → Fin (tapeCount S + tapeCount S) → List (List Bool)
  | none, _ => []
  | some (ch, a), j => if channelSide ch = outputSide j then [letterCode cb a] else []

variable (θ) in
/-- The automaton `mu` as a transducer whose controls are the numbers of the states: a choice is a
letter and a next state, whose weight is a term (`termOf`) for the entry of the matrix of the
letter, and which pushes what the letter pushes. -/
@[expose] noncomputable def simTable (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (q : Fin (Fintype.card Q)) (_ : Fin 0 → Bool) :
    List (Transducer.Choice (Fintype.card Q) (tapeCount S + tapeCount S) (List Bool)) :=
  (Finset.univ : Finset (Tape.Letter S Unit Γ × Q)).toList.map fun z =>
    ⟨termOf θ (mu z.1 ((Fintype.equivFin Q).symm q) z.2), Fintype.equivFin Q z.2, letterPush cb z.1⟩

variable (θ) in
/-- The simulation of `T` steps of the automaton from the state with number `q`, ending in the
state with number `q'`: the weighted list of the output lists. -/
@[expose] noncomputable def simSem (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (T : ℕ) (q q' : Fin (Fintype.card Q)) :
    List (A × Outputs S) :=
  (Transducer.run θ (simTable θ mu cb) T ⟨q, Fin.elim0, fun _ => []⟩).weightedBind fun s =>
    if s.control = q' then [(1, s.outputs)] else []

/-! ### The programs -/

private theorem exists_formula_simSem (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) : ∃ F κ, ∀ (T : ℕ) (q q' : Fin (Fintype.card Q)),
      Does θ F (.cons (num T) (.cons (num q) (num q')))
        ((simSem θ mu cb T q q').map (Prod.map id Outputs.enc)) (κ * (T + 1)) := by
  obtain ⟨R, κ, hR⟩ := Transducer.exists_formula_run (θ := θ) ofBits (simTable θ mu cb)
  set n := tapeCount S + tapeCount S
  refine ⟨lett (.cons .id (lett (.cons (.hd .id) (.cons (.hd (.tl .id)) (.cons (.quote .nil)
    (.quote (listT (List.replicate n .nil)))))) R))
    (.ite (eqF (.hd (.tl .id)) (.tl (.tl (.hd .id)))) (.tl (.tl (.tl .id))) .fail),
    κ + 120 * Fintype.card Q + 300, fun T q q' => ?_⟩
  set x := Tree.cons (num T) (.cons (num q) (num q'))
  let s₀ : Transducer.State (Fintype.card Q) 0 n (List Bool) := ⟨q, Fin.elim0, fun _ => []⟩
  have hs₀ : s₀.enc ofBits = .cons (num q) (.cons .nil (listT (List.replicate n .nil))) := by
    simp only [Transducer.State.enc, s₀, List.ofFn_zero, List.map_nil, List.ofFn_const]
    rfl
  have h1 : Gives θ (.cons (.hd .id) (.cons (.hd (.tl .id)) (.cons (.quote .nil)
      (.quote (listT (List.replicate n .nil)))))) x (.cons (num T) (s₀.enc ofBits)) 20 := by
    rw [hs₀]
    exact ((Gives.id x).hd.cons ((Gives.id x).tl.hd.cons ((Gives.quote _ x).cons
      (Gives.quote _ x)))).mono (by omega)
  refine ((Does.letk_enc (Does.of_gives h1 (hR T s₀)) (f := fun s =>
    (if s.control = q' then [((1 : A), s.outputs)] else []).map (Prod.map id Outputs.enc))
    (d := 120 * Fintype.card Q + 100) fun b _ => ?_).of_eq
    (List.map_weightedBind _ _ _).symm).mono ?_
  · set y := Tree.cons x (b.2.enc ofBits)
    have e := eqF_gives (θ := θ) (u := num b.2.control) (v := num q') (Gives.id y).tl.hd
      (Gives.id y).hd.tl.tl
    rw [size_num] at e
    have hs := b.2.control.2
    by_cases h : b.2.control = q'
    · refine ((Does.ite_true e (by simp [h, bit, one]) (Gives.id y).tl.tl.tl).of_eq ?_).mono
        (by omega)
      simp only [h, ↓reduceIte, List.map_cons, List.map_nil]
      rfl
    · have hne : num (b.2.control : ℕ) ≠ num q' := fun h' =>
        h (Fin.ext (by simpa using congrArg len h'))
      exact ((Does.ite_false (by simpa [hne, bit] using e) (Does.fail y)).of_eq
        (by simp [h])).mono (by omega)
  · nlinarith

private theorem exists_length_le_simSem (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) : ∃ κ, ∀ (T : ℕ) (q q' : Fin (Fintype.card Q)),
      ∀ r ∈ simSem θ mu cb T q q', ∀ j, (r.2 j).length ≤ κ * T ∧ ∀ a ∈ r.2 j, a.length ≤ c := by
  obtain ⟨κ, hκ⟩ := Transducer.exists_length_le_of_mem_run (θ := θ) (simTable θ mu cb)
  refine ⟨κ, fun T q q' r hr j => ?_⟩
  obtain ⟨s, hs, z, hz, rfl⟩ := List.mem_weightedBind_iff.1 hr
  have h2 := Transducer.mem_run_induction (θ := θ) (tab := simTable θ mu cb) (m := 0) (k := T)
    (Inv := fun _ s => ∀ j, ∀ a ∈ s.outputs j, a.length ≤ c) (s := ⟨q, Fin.elim0, fun _ => []⟩)
    (fun s m hm q hq j a ha => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hq
      obtain ⟨⟨z, q⟩, -, rfl⟩ := List.mem_map.1 ho
      rcases List.mem_append.1 ha with ha | ha
      · rcases z with _ | ⟨ch, x⟩
        · simp [letterPush] at ha
        · simp only [letterPush] at ha
          split_ifs at ha
          · simp [List.mem_singleton.1 ha, letterCode]
          · simp at ha
      · exact hm j a ha) (fun j a ha => by simp at ha) s hs
  split_ifs at hz
  · obtain rfl := List.mem_singleton.1 hz
    exact ⟨hκ T _ (fun _ => rfl) s hs j, h2 j⟩
  · simp at hz

/-- The cut items of a list of items. -/
private theorem listF_items_gives {n c : ℕ} {f g : Fin n → Fm} {x : Tree} (it : Fin n → CutItem)
    (hf : ∀ i, Gives θ (f i) x (listT ((it i).flags.map num)) c)
    (hg : ∀ i, Gives θ (g i) x (wordsEnc (it i).letters) c) :
    Gives θ (listF (List.ofFn fun i => .cons (f i) (g i))) x
      (listT ((List.ofFn it).map CutItem.enc)) (n * (2 * c + 2) + 1) := by
  rw [List.map_ofFn]
  exact listF_gives fun i => ((hf i).cons (hg i)).mono (by omega)

/-- A list of copies of a constant, one for every list of keys. -/
private theorem mapF_const_gives {k : Fm} {x v : Tree} {ck : ℕ} {kss : List (List (List Bool))}
    (hk : Gives θ k x (keysEnc kss) ck) :
    Gives θ (mapF (.quote v) (.quote .nil) k) x (listT (List.replicate kss.length v))
      (ck + 41 * kss.length + 21) := by
  have h := mapF_gives (θ := θ) (g := fun _ => v) (d := fun _ => 1) (Gives.quote .nil x) hk
    fun _ _ => Gives.quote _ _
  simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
    smul_eq_mul] at h
  exact h.mono (by omega)

/-- Cut and write: the argument is (items, (initial strings, (`num ub`, (lists of keys,
trie)))). -/
private theorem exists_formula_cutPut (sep : List Bool) : ∃ F, ∀ (c N m ub : ℕ)
    (items : List CutItem) (kss : List (List (List Bool))) (t : Tree), sep.length ≤ c → m ≤ N →
      (∀ it ∈ items, it.flags.length + it.letters.length ≤ N ∧ ∀ a ∈ it.letters, a.length ≤ c) →
      Does θ F (.cons (listT (items.map CutItem.enc)) (.cons (wordsEnc (List.replicate m [true]))
          (.cons (num ub) (.cons (keysEnc kss) t))))
        (cutPut A sep ub items m kss t) ((62 * c + 800) * (items.length * (N + 1) + 1) + 31 * N +
          600 * (putCost ub kss + 1) + 100) := by
  obtain ⟨CT, hCT⟩ := exists_formula_cutTapes (A := A) (θ := θ) sep
  obtain ⟨P, hP⟩ := exists_formula_putStrings (A := A) (θ := θ)
  refine ⟨lett (.cons .id (lett (.cons (.hd .id) (.hd (.tl .id))) CT))
    (lett (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.hd (.tl (.tl (.tl (.hd .id)))))
      (.cons (foldF .id (.quote .nil) (.tl .id)) (.tl (.tl (.tl (.tl (.hd .id)))))))) P),
    fun c N m ub items kss t hsep hm hc => ?_⟩
  set x := Tree.cons (listT (items.map CutItem.enc)) (.cons (wordsEnc (List.replicate m [true]))
    (.cons (num ub) (.cons (keysEnc kss) t)))
  refine (Does.letk_enc (Does.of_gives ((Gives.id x).hd.cons (Gives.id x).tl.hd)
    (hCT c N items _ hsep hc)) (d := 31 * N + 600 * (putCost ub kss + 1) + 60) fun b hb => ?_).mono
    (by omega)
  have hl := length_le_of_mem_cutTapes (N := N) (fun it hit => by have := (hc it hit).1; omega)
    (by simpa using hm) b hb
  set y := Tree.cons x (wordsEnc b.2)
  have r := rev_gives (θ := θ) (xs := b.2.map ofBits) (Gives.quote (listT []) y) (Gives.id y).tl
  rw [List.append_nil, ← List.map_reverse, List.length_map] at r
  exact (Does.of_gives ((Gives.id y).hd.tl.tl.hd.cons ((Gives.id y).hd.tl.tl.tl.hd.cons
    (r.cons (Gives.id y).hd.tl.tl.tl.tl))) (hP ub kss b.2.reverse t)).mono (by omega)

/-- The flags of a row of a list of rows. -/
private theorem getD_map_flags (l : List (List ℕ)) (k : ℕ) :
    (l.map fun fl => listT (fl.map num)).getD k .nil = listT ((l.getD k []).map num) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

private theorem length_getD_le (l : List (List ℕ)) (k : ℕ) :
    (l.getD k []).length ≤ (l.map List.length).sum := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact Nat.zero_le _
  | some a => exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_of_getElem? h))

/-- The cost bound of `exists_formula_packSem`. -/
private theorem pack_cost {n K m N X PW PR : ℕ} (hX : N + 1 ≤ X) (hm : m ≤ X)
    (hP : PW + PR + 1 ≤ X) : 2 * (K * (n * (N + 1) + 1)) + 62 * N + 600 * (PW + PR + 2) +
      n * (2 * (41 * m + 2 * n + 40) + 2) + n * (2 * (2 * n + 6) + 2) + 82 * m + 400 ≤
      (2 * K * (n + 1) + 200 * (n + 1) * (n + 1) + 3000) * X := by
  have f1 : K * (n * (N + 1) + 1) ≤ K * (n + 1) * X := by
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have := Nat.mul_le_mul_left n hX
    rw [add_mul, one_mul]
    omega
  have g1 : n * m ≤ n * X := Nat.mul_le_mul_left _ hm
  have g2 : n * n ≤ n * n * X := Nat.le_mul_of_pos_right _ (by omega)
  have g3 : n ≤ n * X := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

omit [DecidableEq S] in
/-- **Cutting and writing.** The argument is (output lists, (`num ub`, (trie, body))). -/
private theorem exists_formula_packSem (sep : List Bool) {c : ℕ} (hsep : sep.length ≤ c) :
    ∃ F κ, ∀ (ub O : ℕ) (B : Body) (o : Outputs S) (t : Tree), (∀ j, (o j).length ≤ O) →
      (∀ j, ∀ a ∈ o j, a.length ≤ c) →
      Does θ F (.cons (Outputs.enc o) (.cons (num ub) (.cons t B.enc))) (packSem A sep ub B o t)
        (κ * (O + B.cost ub)) := by
  obtain ⟨CP, hCP⟩ := exists_formula_cutPut (A := A) (θ := θ) sep
  refine ⟨lett (.cons .id (lett (.cons (listF (List.ofFn fun i : Fin (tapeCount S) =>
      .cons (nthF i.rev (.hd (.tl (.tl (.tl .id)))))
        (nthF (Fin.castAdd (tapeCount S) i.rev) (.hd .id))))
      (.cons (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl .id))))))
      (.cons (.hd (.tl .id)) (.cons (.hd (.tl (.tl (.tl (.tl .id))))) (.hd (.tl (.tl .id)))))))
      CP))
    (lett (.cons (listF (List.ofFn fun i : Fin (tapeCount S) =>
      .cons (mapF (.quote (num 2)) (.quote .nil) (.hd (.tl (.tl (.tl (.tl (.hd .id)))))))
        (nthF (Fin.natAdd (tapeCount S) i.rev) (.hd (.hd .id)))))
      (.cons (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl (.hd .id)))))))
      (.cons (.hd (.tl (.hd .id))) (.cons (.tl (.tl (.tl (.tl (.tl (.hd .id)))))) (.tl .id)))))
      CP), 2 * (62 * c + 800) * (tapeCount S + 1) + 200 * (tapeCount S + 1) * (tapeCount S + 1) +
      3000, fun ub O B o t hO hc => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, m = B.writeKeys.length := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = O + (B.flags.map List.length).sum + m := ⟨_, rfl⟩
  set x := Tree.cons (Outputs.enc o) (.cons (num ub) (.cons t B.enc))
  have gO : Gives θ (.hd .id) x (listT (List.ofFn fun j => wordsEnc (o j))) 2 := (Gives.id x).hd
  have gF : Gives θ (.hd (.tl (.tl (.tl .id)))) x
      (listT (B.flags.map fun fl => listT (fl.map num))) 5 := (Gives.id x).tl.tl.tl.hd
  have gW : Gives θ (.hd (.tl (.tl (.tl (.tl .id))))) x (keysEnc B.writeKeys) 6 :=
    (Gives.id x).tl.tl.tl.tl.hd
  have gOnes : Gives θ (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl
      .id)))))) x (wordsEnc (List.replicate m [true])) (6 + 41 * m + 21) := by
    simpa [wordsEnc, hm] using mapF_const_gives (θ := θ) (v := ofBits [true]) gW
  -- what is written
  have iR := listF_items_gives (θ := θ) (c := 2 * tapeCount S + 6) (x := x)
    (f := fun i : Fin (tapeCount S) => nthF i.rev (.hd (.tl (.tl (.tl .id)))))
    (g := fun i => nthF (Fin.castAdd (tapeCount S) i.rev) (.hd .id))
    (fun i => ⟨B.flags.getD i.rev [], o (Fin.castAdd (tapeCount S) i.rev)⟩)
    (fun i => by
      have := nthF_gives (i.rev : ℕ) gF
      rw [getD_map_flags] at this
      exact this.mono (by have := i.rev.2; omega))
    (fun i => (nthF_gives_ofFn (Fin.castAdd (tapeCount S) i.rev) gO).mono (by omega))
  have hR := Does.of_gives (iR.cons (gOnes.cons ((Gives.id x).tl.hd.cons
    (gW.cons (Gives.id x).tl.tl.hd))))
    (hCP c N m ub (writeItems B.flags o) B.writeKeys t hsep (by omega) fun it hit => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hit
      exact ⟨by
        dsimp only
        have := length_getD_le B.flags i.rev
        have := hO (Fin.castAdd (tapeCount S) i.rev)
        omega, hc _⟩)
  rw [show (writeItems B.flags o).length = tapeCount S from List.length_ofFn] at hR
  -- what is read
  have hC : ∀ t1 : Tree, Does θ _ (.cons x t1)
      (cutPut A sep ub (readItems m o) m B.readKeys t1) _ := fun t1 => by
    set y := Tree.cons x t1
    have gW' : Gives θ (.hd (.tl (.tl (.tl (.tl (.hd .id)))))) y (keysEnc B.writeKeys) 7 :=
      (Gives.id y).hd.tl.tl.tl.tl.hd
    have gOnes' : Gives θ (mapF (.quote (ofBits [true])) (.quote .nil) (.hd (.tl (.tl (.tl (.tl
        (.hd .id))))))) y (wordsEnc (List.replicate m [true])) (7 + 41 * m + 21) := by
      simpa [wordsEnc, hm] using mapF_const_gives (θ := θ) (v := ofBits [true]) gW'
    have iC := listF_items_gives (θ := θ) (c := 41 * m + 2 * tapeCount S + 40) (x := y)
      (f := fun _ : Fin (tapeCount S) => mapF (.quote (num 2)) (.quote .nil) (.hd (.tl (.tl (.tl
        (.tl (.hd .id)))))))
      (g := fun i => nthF (Fin.natAdd (tapeCount S) i.rev) (.hd (.hd .id)))
      (fun i => ⟨List.replicate m 2, o (Fin.natAdd (tapeCount S) i.rev)⟩)
      (fun _ => by
        have := mapF_const_gives (θ := θ) (v := num 2) gW'
        simpa [hm] using this.mono (by omega : _ ≤ 41 * m + 2 * tapeCount S + 40))
      (fun i => (nthF_gives_ofFn (Fin.natAdd (tapeCount S) i.rev) (Gives.id y).hd.hd).mono
        (by omega))
    have h := hCP c N m ub (readItems m o) B.readKeys t1 hsep (by omega) fun it hit => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hit
      exact ⟨by
        dsimp only
        have := hO (Fin.natAdd (tapeCount S) i.rev)
        simp only [List.length_replicate]
        omega, hc _⟩
    rw [show (readItems m o).length = tapeCount S from List.length_ofFn] at h
    exact Does.of_gives (iC.cons (gOnes'.cons ((Gives.id y).hd.tl.hd.cons
      ((Gives.id y).hd.tl.tl.tl.tl.tl.cons (Gives.id y).tl)))) h
  have hX : N + 1 ≤ O + B.cost ub := by simp only [Body.cost]; omega
  have hP : putCost ub B.writeKeys + putCost ub B.readKeys + 1 ≤ O + B.cost ub := by
    simp only [Body.cost]; omega
  refine ((Does.letk hR fun q _ => hC q.2).of_eq (by rw [hm]; rfl)).mono
    (le_trans ?_ (pack_cost (m := m) hX (by simp only [Body.cost]; omega) hP))
  omega

/-! ### Blocks and input parts -/

/-- **One formula makes a block.** Its argument is ((`num T`, (`num q`, `num q'`)), (`num ub`,
(trie, body))); the block simulates `T` steps of the automaton from the state with number `q` to
the state with number `q'`, and writes the units of the letters. -/
theorem exists_formula_block (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) : ∃ F κ, ∀ (T ub q q' : ℕ) (hq : q < Fintype.card Q)
      (hq' : q' < Fintype.card Q) (B : Body) (t : Tree),
      Does θ F (.cons (.cons (num T) (.cons (num q) (num q'))) (.cons (num ub) (.cons t B.enc)))
        ((simSem θ mu cb T ⟨q, hq⟩ ⟨q', hq'⟩).weightedBind fun o =>
          packSem A (separator cb) ub B o t) (κ * (T + B.cost ub)) := by
  obtain ⟨FS, κs, hFS⟩ := exists_formula_simSem (θ := θ) mu cb
  obtain ⟨κl, hκl⟩ := exists_length_le_simSem (θ := θ) mu cb
  obtain ⟨FP, κp, hFP⟩ := exists_formula_packSem (A := A) (θ := θ) (S := S) (separator cb)
    (c := c) (by simp [separator])
  refine ⟨lett (.cons .id (lett (.hd .id) FS)) (lett (.cons (.tl .id) (.tl (.hd .id))) FP),
    κs + κp * (κl + 1) + 20, fun T ub q q' hq hq' B t => ?_⟩
  have hB : 1 ≤ B.cost ub := by simp only [Body.cost]; omega
  refine (Does.letk_enc (Does.of_gives (Gives.id _).hd (hFS T ⟨q, hq⟩ ⟨q', hq'⟩))
    (d := κp * (κl * T + B.cost ub) + 10) fun b hb => (Does.of_gives ((Gives.id _).tl.cons
      (Gives.id _).hd.tl) (hFP ub (κl * T) B b.2 t (fun j => (hκl T _ _ b hb j).1)
      fun j => (hκl T _ _ b hb j).2)).mono (by omega)).mono ?_
  have f1 : κs * (T + 1) ≤ κs * (T + B.cost ub) := Nat.mul_le_mul_left _ (by omega)
  have f2 : κp * (κl * T + B.cost ub) ≤ κp * (κl + 1) * (T + B.cost ub) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (by nlinarith)
  have e : (κs + κp * (κl + 1) + 20) * (T + B.cost ub) =
      κs * (T + B.cost ub) + κp * (κl + 1) * (T + B.cost ub) + 20 * (T + B.cost ub) := by ring
  rw [e]
  omega

omit [Fintype Γ] in
/-- **One formula makes an input part.** Its argument is (codes of the letters, (`num ub`, (trie,
body))). -/
theorem exists_formula_input (cb : Option Γ → Fin c → Bool) : ∃ F κ, ∀ (ub : ℕ)
      (part : List (List Bool)) (B : Body) (t : Tree), (∀ a ∈ part, a.length ≤ c) →
      Does θ F (.cons (wordsEnc part) (.cons (num ub) (.cons t B.enc)))
        (packSem A (separator cb) ub B (inputOutputs (S := S) part) t)
        (κ * (part.length + B.cost ub)) := by
  obtain ⟨FP, κp, hFP⟩ := exists_formula_packSem (A := A) (θ := θ) (S := S) (separator cb)
    (c := c) (by simp [separator])
  set n := tapeCount S + tapeCount S
  refine ⟨lett (.cons (listF (List.ofFn fun j : Fin n =>
    if outputSide j = (none, false) then .hd .id else .quote .nil)) (.tl .id)) FP,
    κp + 6 * n + 10, fun ub part B t hc => ?_⟩
  set x := Tree.cons (wordsEnc part) (.cons (num ub) (.cons t B.enc))
  have hIO : Gives θ (listF (List.ofFn fun j : Fin n =>
      if outputSide j = (none, false) then .hd .id else .quote .nil)) x
      (Outputs.enc (inputOutputs (S := S) part)) (n * 3 + 1) := listF_gives fun j => by
    by_cases h : outputSide j = ((none : Option S), false)
    · simp only [inputOutputs, h, ↓reduceIte]
      exact (Gives.id x).hd
    · simp only [inputOutputs, h, ↓reduceIte]
      exact (Gives.quote .nil x).mono (by omega)
  have hB : 1 ≤ B.cost ub := by simp only [Body.cost]; omega
  refine (Does.of_gives (hIO.cons (Gives.id x).tl) (hFP ub part.length B _ t (fun j => by
    simp only [inputOutputs]; split_ifs <;> simp) fun j a ha => by
      simp only [inputOutputs] at ha
      split_ifs at ha
      exacts [hc a ha, absurd ha List.not_mem_nil])).mono ?_
  have e : (κp + 6 * n + 10) * (part.length + B.cost ub) =
      κp * (part.length + B.cost ub) + (6 * n + 10) * (part.length + B.cost ub) := by ring
  rw [e]
  nlinarith

end Automaton

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
