/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Segments
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.GroupScript
import CslibFrontier.Foundations.Algebra.BigOperators.PiFinset
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.List.ReduceOption

/-!
# What a base party writes and reads

A base party of the evaluator of [AnthropicVPVNP2026] cuts the letters of every tape into
segments for its partners. The sum over all ways to cut the letters of a tape is the sum over the
segments whose concatenation is the letters and that obey the flags of the partners, and so is the
sum over the cuts of all tapes and over what a base party writes and reads (`sum_map_packSem`).
In a block, the letters are those of a run of the automaton on the sides of the tapes
(`sideLetters`), and the sum over a simulation of the block is the sum over these runs
(`weightedSum_simSem`).

## Main definitions

* `sideLetters`: the letters that a run of the automaton writes on the sides of the tapes.

## Main results

* `sideLetters_channelSide`, `sideLetters_none_false`: the letters on the sides of the tapes.
* `sum_length_sideLetters_le`, `length_sideLetters_le`: a run writes at most one letter per step.
* `weightedSum_simSem`, `exists_of_mem_simSem`: the sum over a simulation of a block, and what it
  writes.
* `one_of_mem_packSem`, `sum_map_packSem`: the weights of what a base party writes and reads, and
  the sum over it.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source modules
`Nc.Grp.SegSum`, `Nc.Grp.SumSeg`, `Nc.Grp.SumSim` and `Nc.Grp.SumBase`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset Interpreter Interpreter.Tree List.StairRefinement

/-! ### Cutting the letters of the tapes -/

section Cuts

variable {M : Type*} [AddCommMonoid M] {Γ : Type*} [Finite Γ] [DecidableEq Γ] (sep : List Bool)
  (code : Γ → List Bool) (T : ℕ)

/-- The sum over the cuts of the remaining letters `rest` is the sum over the number `j` of letters
that the partner at hand still takes before its segment is closed. -/
private theorem sum_map_cuts (G : List (List Bool) → M) (f : ℕ) (fs : List ℕ)
    (as out : List (List Bool)) :
    ∀ (rest : List (List Bool)) (tk : Bool) (cur : List Bool),
      ((cuts sep f tk cur fs as rest out).map G).sum =
        ∑ j ∈ range (rest.length + 1), if flagAllows f (tk || decide (0 < j)) then
          ((cutsClose sep ((rest.take j).reverse.flatten ++ cur) fs as (rest.drop j) out).map
            G).sum else 0
  | [], tk, cur => by rw [cuts_eq]; split_ifs <;> simp [cutsTake, *]
  | a :: rest, tk, cur => by
    rw [cuts_eq, List.map_append, List.sum_append, sum_range_succ', add_comm, cutsTake,
      sum_map_cuts G f fs as out rest true (a ++ cur)]
    congr 1
    · exact sum_congr rfl fun j _ => by simp
    · split_ifs <;> simp_all

/-- The sum over segments `X` of the letters `l` that obey the flags `fl`, of a function of the
strings of the partners: the segment of every partner `b`, a separator, and the string `acc b`
that it has from the later tapes. -/
private noncomputable abbrev segSum {m : ℕ} (fl : Fin m → ℕ) (acc : Fin m → List Bool) (l : List Γ)
    (G : List (List Bool) → M) : M :=
  ∑ X ∈ Fintype.piFinset fun _ : Fin m => List.wordsLe Γ T,
    if cat X = l ∧ ∀ b, flagAllows (fl b) (decide (X b ≠ [])) then
      G (List.ofFn fun b => (X b).flatMap code ++ (sep ++ acc b)) else 0

/-- One more partner: the cuts of the letters of a tape from a fresh partner, given the sum
over the cuts after a segment is closed. -/
private theorem sum_map_cuts_fresh {m : ℕ} (hP : ∀ (fl : Fin m → ℕ) (acc : Fin m → List Bool)
      (cur : List Bool) (l : List Γ) (out : List (List Bool)) (G : List (List Bool) → M),
      l.length ≤ T → ((cutsClose sep cur (List.ofFn fl).reverse (List.ofFn acc).reverse
        ((l.map code).reverse) out).map G).sum =
        segSum sep code T fl acc l fun r => G (r ++ cur :: out))
    (fl : Fin (m + 1) → ℕ) (acc : Fin (m + 1) → List Bool) (l : List Γ) (out : List (List Bool))
    (G : List (List Bool) → M) (hl : l.length ≤ T) :
    ((cuts sep (fl (Fin.last m)) false (sep ++ acc (Fin.last m))
      (List.ofFn fun b => fl b.castSucc).reverse (List.ofFn fun b => acc b.castSucc).reverse
      ((l.map code).reverse) out).map G).sum =
      segSum sep code T fl acc l fun r => G (r ++ out) := by
  rw [sum_map_cuts, segSum, Fin.sum_piFinset_const_snoc]
  simp only [List.length_reverse, List.length_map, Bool.false_or, List.take_reverse,
    List.drop_reverse, List.reverse_reverse, List.length_map, ← List.map_drop, ← List.map_take,
    ← List.flatMap_def]
  set g : List Γ → M := fun Y => ∑ X ∈ Fintype.piFinset fun _ : Fin m => List.wordsLe Γ T,
    if cat (Fin.snoc X Y : Fin (m + 1) → List Γ) = l ∧ ∀ b, flagAllows (fl b)
      (decide ((Fin.snoc X Y : Fin (m + 1) → List Γ) b ≠ [])) then
      G (List.ofFn (fun b => ((Fin.snoc X Y : Fin (m + 1) → List Γ) b).flatMap code ++
        (sep ++ acc b)) ++ out) else 0
  have hcat (X : Fin m → List Γ) (Y : List Γ) :
      cat (Fin.snoc X Y : Fin (m + 1) → List Γ) = cat X ++ Y := by
    simp only [cat, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      List.flatten_append, List.flatten_singleton]
  have hj (j : ℕ) (hj : j ∈ range (l.length + 1)) :
      (if flagAllows (fl (Fin.last m)) (decide (0 < j))
      then ((cutsClose sep ((l.drop (l.length - j)).flatMap code ++ (sep ++ acc (Fin.last m)))
        (List.ofFn fun b => fl b.castSucc).reverse (List.ofFn fun b => acc b.castSucc).reverse
          (((l.take (l.length - j)).map code).reverse) out).map G).sum else 0) =
      g (l.drop (l.length - j)) := by
    rw [mem_range] at hj
    rw [hP _ _ _ (l.take (l.length - j)) _ _ (by rw [List.length_take]; omega)]
    have e1 : decide (l.drop (l.length - j) ≠ []) = decide (0 < j) := by
      rw [decide_eq_decide, ne_eq, ← List.length_eq_zero_iff, List.length_drop]; omega
    have e2 (X : Fin m → List Γ) : cat X ++ l.drop (l.length - j) = l ↔
        cat X = l.take (l.length - j) := by
      conv_lhs => rhs; rw [← List.take_append_drop (l.length - j) l]
      exact List.append_left_inj _
    simp only [g, segSum, hcat, e2, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last, e1,
      List.ofFn_succ', List.concat_eq_append, List.append_assoc, List.singleton_append]
    split_ifs with hc <;> simp [hc]
  rw [sum_congr rfl hj, ← sum_image (g := fun j => l.drop (l.length - j)) fun j hj j' hj' e => by
    have := congrArg List.length e
    simp only [coe_range, Set.mem_Iio, List.length_drop] at hj hj' this
    omega]
  refine sum_subset (fun Y hY => ?_) fun Y _ hY => sum_eq_zero fun X _ => ite_eq_right_iff.2 ?_
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 hY
    exact List.mem_wordsLe.2 (by rw [List.length_drop]; omega)
  · rintro ⟨h, -⟩
    refine (hY (mem_image.2 ⟨Y.length, mem_range.2 ?_, ?_⟩)).elim
    · have := congrArg List.length h
      simp only [hcat, List.length_append] at this; omega
    · rw [← h, hcat, List.drop_append_of_le_length (by simp), List.length_append,
        Nat.add_sub_cancel, List.drop_length, List.nil_append]

/-- The sum over the cuts after a segment is closed. -/
private theorem sum_map_cutsClose : ∀ (m : ℕ) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (cur : List Bool) (l : List Γ) (out : List (List Bool)) (G : List (List Bool) → M),
    l.length ≤ T → ((cutsClose sep cur (List.ofFn fl).reverse (List.ofFn acc).reverse
      ((l.map code).reverse) out).map G).sum =
        segSum sep code T fl acc l fun r => G (r ++ cur :: out)
  | 0, fl, acc, cur, l, out, G, _ => by
    rw [segSum, Fintype.piFinset_of_isEmpty, Fintype.sum_unique]
    cases l <;> simp [cutsClose, cat]
  | m + 1, fl, acc, cur, l, out, G, hl => by
    simp only [List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, cutsClose, List.headD_cons, List.tail_cons]
    exact sum_map_cuts_fresh sep code T (sum_map_cutsClose m) fl acc l (cur :: out) G hl

/-- **The sum over the cuts of the letters `l` of a tape** for partners with the flags `fl` and
the strings `acc` from the later tapes. -/
private theorem sum_map_tapeCuts {m : ℕ} (hm : 0 < m) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (l : List Γ) (hl : l.length ≤ T) (G : List (List Bool) → M) :
    ((tapeCuts sep (List.ofFn fl).reverse (List.ofFn acc).reverse
      ((l.map code).reverse)).map G).sum = segSum sep code T fl acc l G := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
    List.singleton_append, tapeCuts, List.headD_cons, List.tail_cons]
  simpa using sum_map_cuts_fresh sep code T (sum_map_cutsClose sep code T m) fl acc l [] G hl

/-- **The sum over the cuts of the letters `l i` of the tapes `i`**, the last tape first, for
partners with the flags `fl i` and the strings `acc` from the later tapes. -/
private theorem sum_map_cutTapes {F : Type} [CommRing F] {m : ℕ} (hm : 0 < m) :
    ∀ {N : ℕ} (fl : Fin N → Fin m → ℕ) (l : Fin N → List Γ), (∀ i, (l i).length ≤ T) →
      ∀ (acc : Fin m → List Bool) (G : List (List Bool) → M),
      ((cutTapes F sep (List.ofFn fun i => ⟨(List.ofFn (fl i.rev)).reverse,
        ((l i.rev).map code).reverse⟩) (List.ofFn acc).reverse).map Prod.snd |>.map G).sum =
        ∑ X ∈ Fintype.piFinset fun _ : Fin N => Fintype.piFinset fun _ : Fin m =>
          List.wordsLe Γ T, if ∀ i, cat (X i) = l i ∧ ∀ b, flagAllows (fl i b) (decide (X i b ≠ []))
          then G (List.ofFn fun b =>
            (List.ofFn fun i => (X i b).flatMap code ++ sep).flatten ++ acc b).reverse else 0
  | 0, fl, l, _, acc, G => by
    rw [Fintype.piFinset_of_isEmpty, Fintype.sum_unique]
    simp [cutTapes]
  | N + 1, fl, l, hl, acc, G => by
    have hcons (it items accs) : cutTapes F sep (it :: items) accs =
        (cutTape F sep it accs).weightedBind (cutTapes F sep items) := rfl
    have hcut (it : CutItem) accs (H : List (List Bool) → M) :
        ((cutTape F sep it accs).map Prod.snd).map H =
          (tapeCuts sep it.flags accs it.letters).map (H ·.reverse) := by
      simp [cutTape]
    rw [List.ofFn_succ, hcons, List.map_snd_weightedBind, List.sum_map_flatMap,
      Fin.sum_piFinset_const_snoc, hcut]
    simp only [Fin.rev_zero, Fin.rev_succ]
    rw [sum_map_tapeCuts sep code T hm _ _ _ (hl _)]
    refine sum_congr rfl fun Y _ => ?_
    beta_reduce
    rw [sum_map_cutTapes hm (fun i => fl i.castSucc) (fun i => l i.castSucc)
      (fun i => hl _)]
    simp only [Fin.forall_fin_succ' (n := N), Fin.snoc_castSucc, Fin.snoc_last,
      List.ofFn_succ' (n := N), List.concat_eq_append, List.flatten_append, List.flatten_singleton,
      List.append_assoc]
    split_ifs with h <;>
      simp only [h, implies_true, and_self, and_true, and_false, ite_false, sum_const_zero]

end Cuts

/-! ### Simulating the automaton -/

section Sim

variable {Γ S : Type} [DecidableEq S]

/-- The letters that a run of the automaton writes on the side `d` of the tape `s`, in order. The
input channel is the side `true` of the tape `none`, and the side `false` of `none` gets no
letter. -/
@[expose] def sideLetters (u : List (Tape.Letter S Unit Γ)) (z : Option S × Bool) : List Γ :=
  Automata.Weighted.proj (u.reduceOption.map fun a => (channelSide a.1, a.2)) z

/-- The letters on the side of a channel are the letters that the run emits on the channel. -/
theorem sideLetters_channelSide (u : List (Tape.Letter S Unit Γ)) (ch : Tape.Ch S Unit) :
    sideLetters u (channelSide ch) = Tape.emit u ch := by
  have hinj : Function.Injective (channelSide : Tape.Ch S Unit → _) := by
    rintro (⟨s, d⟩ | ⟨⟨⟩⟩) (⟨s', d'⟩ | ⟨⟨⟩⟩) h <;> simp_all [channelSide]
  simp [sideLetters, Tape.emit, Automata.Weighted.proj, List.filter_map, Function.comp_def,
    hinj.eq_iff]

theorem sideLetters_none_false (u : List (Tape.Letter S Unit Γ)) :
    sideLetters u (none, false) = [] := by
  simp only [sideLetters, Automata.Weighted.proj, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    List.mem_map, decide_eq_true_eq, forall_exists_index, and_imp]
  rintro _ ⟨⟨s, d⟩ | ⟨⟨⟩⟩, a⟩ - rfl <;> simp [channelSide]

/-- A run writes at most as many letters on a side of a tape as it has steps. -/
theorem length_sideLetters_le (u : List (Tape.Letter S Unit Γ)) (z : Option S × Bool) :
    (sideLetters u z).length ≤ u.length :=
  (List.length_map _).trans_le ((List.length_filter_le _ _).trans
    ((List.length_map _).trans_le (List.reduceOption_length_le u)))

variable [Fintype S]

/-- A run writes at most as many letters on the sides `d` of all tapes as it has steps. -/
theorem sum_length_sideLetters_le (u : List (Tape.Letter S Unit Γ)) (d : Bool) :
    ∑ s, (sideLetters u (s, d)).length ≤ u.length := by
  refine le_trans ?_ ((Automata.Weighted.sum_length_proj
    (u.reduceOption.map fun a => (channelSide a.1, a.2))).trans_le
    ((List.length_map _).trans_le (List.reduceOption_length_le u)))
  rw [Fintype.sum_prod_type]
  exact sum_le_sum fun s _ => single_le_sum (f := fun d => (sideLetters u (s, d)).length)
    (fun _ _ => Nat.zero_le _) (mem_univ d)


/-- What the run `u` pushes on an output list are the codes of its letters on the side of the
list, the last first. -/
private theorem flatMap_letterPush {c : ℕ} (cb : Option Γ → Fin c → Bool)
    (u : List (Tape.Letter S Unit Γ)) (j : Fin (tapeCount S + tapeCount S)) :
    u.reverse.flatMap (letterPush cb · j) =
      ((sideLetters u (outputSide j)).map (letterCode cb)).reverse := by
  induction u with
  | nil => simp [sideLetters, Automata.Weighted.proj]
  | cons z u ih =>
    rw [List.reverse_cons, List.flatMap_append, ih, List.flatMap_singleton]
    rcases z with _ | ⟨ch, a⟩
    · simp [letterPush, sideLetters, List.reduceOption_cons_of_none]
    · simp only [letterPush, sideLetters, List.reduceOption_cons_of_some, List.map_cons,
        Automata.Weighted.proj_cons]
      split_ifs <;> simp

variable {F : Type} [CommRing F] {θ : List Bool → F} {Q : Type} [Fintype Γ] [Fintype Q] {c : ℕ}

private theorem exists_of_mem_run_simTable (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (cb : Option Γ → Fin c → Bool) :
    ∀ {k : ℕ} {s : Transducer.State (Fintype.card Q) 0 (tapeCount S + tapeCount S) (List Bool)}
      {r : F × Transducer.State (Fintype.card Q) 0 (tapeCount S + tapeCount S) (List Bool)},
      r ∈ Transducer.run θ (simTable θ mu cb) k s → ∃ u : List (Tape.Letter S Unit Γ),
        u.length = k ∧ ∀ j, r.2.outputs j = u.reverse.flatMap (letterPush cb · j) ++ s.outputs j
  | 0, s, r, h => ⟨[], rfl, fun _ => by simp_all [Transducer.run_zero]⟩
  | k + 1, s, r, h => by
    rw [Transducer.run_succ] at h
    obtain ⟨a, ha, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 h
    obtain ⟨u, hu, hr'⟩ := exists_of_mem_run_simTable mu cb hr
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 ho
    exact ⟨z.1 :: u, by simp [hu], fun j => by simp [hr', Transducer.Choice.apply]⟩

/-- The output lists of a simulation are the codes of the letters of a run of `T` steps on the
sides of the tapes, the last first. -/
theorem exists_of_mem_simSem (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (cb : Option Γ → Fin c → Bool) {T : ℕ} {qa qb : Fin (Fintype.card Q)} {r : F × Outputs S}
    (h : r ∈ simSem θ mu cb T qa qb) : ∃ u : List (Tape.Letter S Unit Γ), u.length = T ∧
      r.2 = fun j => ((sideLetters u (outputSide j)).map (letterCode cb)).reverse := by
  obtain ⟨a, ha, r', hr', rfl⟩ := List.mem_weightedBind_iff.1 h
  obtain ⟨u, hu, hout⟩ := exists_of_mem_run_simTable mu cb ha
  split_ifs at hr'
  · exact ⟨u, hu, by simpa [List.mem_singleton.1 hr', ← flatMap_letterPush] using funext hout⟩
  · simp at hr'

variable [DecidableEq Q]

/-- The runs of the automaton as a transducer, from the state `q`. -/
private theorem weightedSum_run_simTable (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (cb : Option Γ → Fin c → Bool) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') :
    ∀ (k : ℕ) (q : Q) (out : Outputs S)
      (H : Transducer.State (Fintype.card Q) 0 (tapeCount S + tapeCount S) (List Bool) → F),
      (Transducer.run θ (simTable θ mu cb) k ⟨Fintype.equivFin Q q, Fin.elim0, out⟩).weightedSum H =
        ∑ u : Fin k → Tape.Letter S Unit Γ, ∑ q', ((List.ofFn u).map mu).prod q q' *
          H ⟨Fintype.equivFin Q q', Fin.elim0,
            fun j => (List.ofFn u).reverse.flatMap (letterPush cb · j) ++ out j⟩
  | 0, q, out, H => by simp [Transducer.run_zero, Matrix.one_apply]
  | k + 1, q, out, H => by
    rw [Transducer.weightedSum_run_succ _ rfl, Fintype.sum_prod_type,
      ← (Fin.consEquiv fun _ => Tape.Letter S Unit Γ).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    have helim : (fun i : Fin 0 => (Fin.elim0 i : List Bool).tail) = Fin.elim0 := funext (·.elim0)
    simp only [Transducer.Choice.apply, val_termOf (hmu _ _ _), Equiv.symm_apply_apply, helim,
      weightedSum_run_simTable mu cb hmu k, mul_sum, Fin.consEquiv_apply, List.ofFn_succ,
      Fin.cons_zero, Fin.cons_succ, List.map_cons, List.prod_cons, Matrix.mul_apply, sum_mul,
      List.reverse_cons, List.flatMap_append, List.flatMap_singleton, List.append_assoc, mul_assoc]
    rw [sum_comm]
    exact sum_congr rfl fun u _ => sum_comm

/-- **The sum over a simulation**: the sum over the runs `u` of `T` steps of the weight of the
run from `q` to `q'` times `G` at the codes of the letters of `u` on the sides of the tapes. -/
theorem weightedSum_simSem (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (cb : Option Γ → Fin c → Bool) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (T : ℕ)
    (q q' : Q) (G : Outputs S → F) :
    (simSem θ mu cb T (Fintype.equivFin Q q) (Fintype.equivFin Q q')).weightedSum G =
      ∑ u : Fin T → Tape.Letter S Unit Γ, ((List.ofFn u).map mu).prod q q' *
        G fun j => ((sideLetters (List.ofFn u) (outputSide j)).map (letterCode cb)).reverse := by
  rw [simSem, List.weightedSum_weightedBind, weightedSum_run_simTable mu cb hmu]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_eq_single q' (fun q'' _ h => by simp [(Fintype.equivFin Q).injective.ne h]) (by simp)]
  simp [flatMap_letterPush]

end Sim

/-! ### What a base party writes and reads -/

section Pack

variable {F : Type} [CommRing F] {Γ S : Type} [Finite Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] {c T : ℕ} {M' : Type*} [AddCommMonoid M']

omit [Finite Γ] [DecidableEq Γ] [DecidableEq S] in
/-- The bit string of segments on all tapes, as the codes of their letters with separators. -/
private theorem segmentString_eq (cb : Option Γ → Fin c → Bool) (Y : Option S → List Γ) :
    segmentString cb Y =
      (tapes S).flatMap fun s => (Y s).flatMap (letterCode cb) ++ separator cb := by
  simp only [segmentString, bitsOf, joinSegments, List.flatMap_assoc, List.flatMap_append,
    List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil, separator, tapes]
  rfl

/-- **The sum over the cuts of the letters `l s` of all tapes `s`**, the last tape first, for
partners with the flags `fl s`, each partner starting from the closing bit `1`. -/
private theorem sum_map_cutTapes_tapes (cb : Option Γ → Fin c → Bool) {m : ℕ} (hm : 0 < m)
    (fl : Option S → Fin m → ℕ) (l : Option S → List Γ) (hl : ∀ s, (l s).length ≤ T)
    (G : List (List Bool) → M') :
    ((cutTapes F (separator cb) (List.ofFn fun i : Fin (tapeCount S) =>
      ⟨(List.ofFn (fl ((tapes S).get i.rev))).reverse,
        ((l ((tapes S).get i.rev)).map (letterCode cb)).reverse⟩) (List.replicate m [true])).map
      Prod.snd |>.map G).sum =
      ∑ X ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin m => List.wordsLe Γ T,
        if ∀ s, cat (X s) = l s ∧ ∀ b, flagAllows (fl s b) (decide (X s b ≠ [])) then
          G (List.ofFn fun b => segmentString cb (fun s => X s b) ++ [true]).reverse else 0 := by
  let e : Fin (tapeCount S) ≃ Option S := (nodup_toList _).getEquivOfForallMemList _ fun s =>
    mem_toList.2 (mem_univ s)
  have hrep : List.replicate m [true] = (List.ofFn fun _ : Fin m => [true]).reverse := by simp
  rw [hrep, sum_map_cutTapes (separator cb) (letterCode cb) T hm (fun i => fl ((tapes S).get i))
      (fun i => l ((tapes S).get i)) fun i => hl _]
  refine sum_equiv (e.arrowCongr (Equiv.refl _)) (fun X => by simpa [Fintype.mem_piFinset] using
    (e.symm.forall_congr_right (q := fun i => ∀ b, (X i b).length ≤ T)).symm) fun X _ => ?_
  have hs (b : Fin m) :
      (List.ofFn fun i => (X i b).flatMap (letterCode cb) ++ separator cb).flatten =
      (tapes S).flatMap fun s => (X (e.symm s) b).flatMap (letterCode cb) ++ separator cb := by
    rw [List.flatMap_def, ← List.ofFn_getElem_eq_map]
    congr! 3 with i
    exact congrArg (fun j => (X j b).flatMap (letterCode cb) ++ separator cb)
      (e.symm_apply_apply i).symm
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    ← e.forall_congr_right (q := fun s => cat (X (e.symm s)) = l s ∧ _), e.symm_apply_apply,
    segmentString_eq, hs]
  rfl

omit [Finite Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] in
/-- The flags of a row allow the segments of the partners exactly when the segments fit the row
data, if a row that is not empty has its first partner before its last one. -/
private theorem forall_flagAllows_rowFlag {A : ℕ} {d : RowData A}
    (hd : d.empty = false → d.first ≤ d.last) {X : Fin A → List Γ} :
    (∀ b, flagAllows (rowFlag d b) (decide (X b ≠ [])) = true) ↔ d.Ok X := by
  rw [RowData.Ok]
  cases he : d.empty
  · have hfl := hd he
    simp only [rowFlag, he, Bool.false_eq_true, ite_false]
    refine ⟨fun h => ⟨by simpa [flagAllows] using h d.first, by simpa [flagAllows] using h d.last,
      fun b hb => ?_⟩, fun ⟨h1, h2, h3⟩ b => by split_ifs <;> grind [flagAllows]⟩
    have := h b
    split_ifs at this <;> grind [flagAllows]
  · simp [rowFlag, he, flagAllows]

private theorem one_of_mem_cutTapes (sep : List Bool) :
    ∀ (items : List CutItem) (accs : List (List Bool)), ∀ q ∈ cutTapes F sep items accs, q.1 = 1
  | [], accs => by simp [cutTapes]
  | it :: items, accs => List.fst_eq_one_of_mem_weightedBind (by simp [cutTape])
    fun a => one_of_mem_cutTapes sep items a

omit [DecidableEq S] in
/-- All weights of what a base party writes and reads are `1`. -/
theorem one_of_mem_packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outputs S)
    (t : Tree) : ∀ q ∈ packSem F sep ub B o t, q.1 = 1 :=
  List.fst_eq_one_of_mem_weightedBind
    (List.fst_eq_one_of_mem_weightedBind (one_of_mem_cutTapes sep _ _) (by simp))
    fun _ => List.fst_eq_one_of_mem_weightedBind (one_of_mem_cutTapes sep _ _) (by simp)

private theorem map_snd_cutPut (sep : List Bool) (ub : ℕ) (items : List CutItem) (m : ℕ)
    (kss : List (List (List Bool))) (t : Tree) :
    (cutPut F sep ub items m kss t).map Prod.snd =
      ((cutTapes F sep items (List.replicate m [true])).map Prod.snd).flatMap fun s =>
        putStrings ub kss s.reverse t := by
  simp [cutPut, List.map_snd_weightedBind, Function.comp_def]

variable {A' E K U0 U1 ub : ℕ} {M : Moves F (K + K + A') E}

/-- **What a base party writes and reads.** If the base party `p` has the letters `w (s, d)` on
the side `d` of every tape `s`, at most `T` on each, the sum of `G` over the tries after it has cut
the letters and written the units of the strings that it writes and reads is the sum over the
segments `R` that it writes, which fit its row data, and `C` that it reads, of the sum over
writing the units of their strings. -/
theorem sum_map_packSem (cb : Option Γ → Fin c → Bool)
    (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) {p : Fin (K + K)}
    (hρ : ∀ s, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last)
    {w : Option S × Bool → List Γ} (hw : ∀ z, (w z).length ≤ T) {o : Outputs S}
    (ho : ∀ j, o j = ((w (outputSide j)).map (letterCode cb)).reverse) (t : Tree)
    (G : Tree → M') :
    (((packSem F (separator cb) ub (baseBody ρ n key dkey p) o t).map Prod.snd).map G).sum =
      ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) =>
        List.wordsLe Γ T, if (∀ s, cat (R s) = w (s, false)) ∧ ∀ s, (ρ s p).Ok (R s) then
          ((putStrings ub (baseBody ρ n key dkey p).writeKeys
            (List.ofFn fun b => segmentString cb (fun s => R s b) ++ [true]) t).map fun t₁ =>
            ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) =>
              List.wordsLe Γ T, if ∀ s, cat (C s) = w (s, true) then
                ((putStrings ub (baseBody ρ n key dkey p).readKeys
                  (List.ofFn fun b => segmentString cb (fun s => C s b) ++ [true]) t₁).map G).sum
              else 0).sum
        else 0 := by
  have hwi : writeItems (baseBody ρ n key dkey p).flags o = List.ofFn fun i : Fin (tapeCount S) =>
      ⟨(List.ofFn fun b => rowFlag (ρ ((tapes S).get i.rev) p) b).reverse,
        ((w ((tapes S).get i.rev, false)).map (letterCode cb)).reverse⟩ :=
    congrArg List.ofFn (funext fun i => by
      simp [baseBody, ho, outputSide,
        List.getElem?_eq_getElem (Nat.sub_lt ((Nat.zero_le _).trans_lt i.2) (Nat.succ_pos _))])
  have hri : readItems (K + K) o = List.ofFn fun i : Fin (tapeCount S) =>
      ⟨(List.ofFn fun _ : Fin (K + K) => 2).reverse,
        ((w ((tapes S).get i.rev, true)).map (letterCode cb)).reverse⟩ := by
    simp [readItems, ho, outputSide, -Fin.natAdd_eq_addNat]
  have hm : (baseBody ρ n key dkey p).writeKeys.length = K + K := List.length_ofFn
  rw [packSem, List.map_snd_weightedBind, List.sum_map_flatMap, map_snd_cutPut,
    List.sum_map_flatMap, hm, hwi,
    sum_map_cutTapes_tapes cb (Fin.pos p) (fun s b => rowFlag (ρ s p) b)
      (fun s => w (s, false)) fun s => hw _]
  refine sum_congr rfl fun R _ => ?_
  simp only [forall_and, forall_flagAllows_rowFlag (hρ _), List.reverse_reverse]
  congr! 4 with t₁
  rw [map_snd_cutPut, List.sum_map_flatMap, hri,
    sum_map_cutTapes_tapes cb (Fin.pos p) (fun _ _ => 2) (fun s => w (s, true)) fun s => hw _]
  simp [flagAllows]

end Pack

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
