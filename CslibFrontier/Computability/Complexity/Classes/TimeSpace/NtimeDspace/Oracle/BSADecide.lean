/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.BSA

/-!
# Deciding `BSA`

Membership in `BSA` is decided by checking the shape `frame w ++ frame x ++ 1^b` of the query with a
finite automaton (`bsaValid`), testing the padding `2^|w| ≤ b`, and running Complexitylib's
universal machine within the space budget `b` for `2^(b+1)` steps
(`Turing.MultiTapeTM.Universal.budgetedUniversal`). A halting run within the budget repeats no
configuration, and there are fewer than `2^(b+1)` configurations described within `b` bits, so the
clock suffices (`acceptsWithin_iff_budgeted`).

## Main definitions

* `Cslib.Complexity.NtimeDspace.Oracle.bsaDecide`: the decision procedure.

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.acceptsWithin_iff_budgeted`: acceptance within space `b` is
decided by the
  budgeted universal machine with clock `2^(b+1)`.
* `Cslib.Complexity.NtimeDspace.Oracle.bsaDecide_eq`: `bsaDecide q = decide (q ∈ BSA)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### The shape of a query -/

/-- The states of the automaton checking the shape `frame w ++ frame x ++ 1^b`. -/
inductive VSt where
  | f1
  | f1b
  | f2
  | f2b
  | r
  | dead
  deriving DecidableEq

instance : Fintype VSt :=
  ⟨{.f1, .f1b, .f2, .f2b, .r, .dead}, by intro x; cases x <;> simp⟩

/-- A step of the automaton. -/
def vstep : VSt → Bool → VSt
  | .f1, true => .f1b
  | .f1, false => .f2
  | .f1b, _ => .f1
  | .f2, true => .f2b
  | .f2, false => .r
  | .f2b, _ => .f2
  | .r, true => .r
  | .r, false => .dead
  | .dead, _ => .dead

lemma foldl_frame_f1 (w u : List Bool) : (frame w ++ u).foldl vstep .f1 = u.foldl vstep .f2 := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [vstep] using ih

lemma foldl_frame_f2 (w u : List Bool) : (frame w ++ u).foldl vstep .f2 = u.foldl vstep .r := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [vstep] using ih

lemma foldl_dead (u : List Bool) : u.foldl vstep .dead = .dead := by
  induction u with
  | nil => rfl
  | cons b u ih => simpa [vstep] using ih

lemma foldl_r_replicate (n : ℕ) : (List.replicate n true).foldl vstep .r = .r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, vstep] using ih

lemma eq_replicate_of_foldl_r : ∀ u : List Bool, u.foldl vstep .r = .r →
    u = List.replicate u.length true
  | [], _ => rfl
  | true :: u, h => by
    simp only [List.foldl_cons, vstep] at h
    simpa [List.replicate_succ] using eq_replicate_of_foldl_r u h
  | false :: u, h => by
    simp only [List.foldl_cons, vstep, foldl_dead] at h
    cases h

lemma framed_of_f2 : ∀ q : List Bool, q.foldl vstep .f2 = .r →
    frame (unframe q) ++ dropFrame q = q ∧ (dropFrame q).foldl vstep .r = .r
  | [], h => by cases h
  | [true], h => by cases h
  | true :: c :: q, h => by
    simp only [List.foldl_cons, vstep] at h
    obtain ⟨h1, h2⟩ := framed_of_f2 q h
    refine ⟨?_, by simpa [dropFrame] using h2⟩
    simp only [unframe, dropFrame, frame_cons, List.cons_append, h1]
  | false :: q, h => by
    simp only [List.foldl_cons, vstep] at h
    exact ⟨by simp [unframe, dropFrame], by simpa [dropFrame] using h⟩

lemma framed_of_f1 : ∀ q : List Bool, q.foldl vstep .f1 = .r →
    frame (unframe q) ++ dropFrame q = q ∧ (dropFrame q).foldl vstep .f2 = .r
  | [], h => by cases h
  | [true], h => by cases h
  | true :: c :: q, h => by
    simp only [List.foldl_cons, vstep] at h
    obtain ⟨h1, h2⟩ := framed_of_f1 q h
    refine ⟨?_, by simpa [dropFrame] using h2⟩
    simp only [unframe, dropFrame, frame_cons, List.cons_append, h1]
  | false :: q, h => by
    simp only [List.foldl_cons, vstep] at h
    exact ⟨by simp [unframe, dropFrame], by simpa [dropFrame] using h⟩

/-- The shape test. -/
def bsaValid (q : List Bool) : Bool := decide (q.foldl vstep .f1 = .r)

lemma bsaValid_bsaQuery (w x : List Bool) (b : ℕ) : bsaValid (bsaQuery w x b) = true := by
  simp only [bsaValid, bsaQuery, List.append_assoc, foldl_frame_f1, foldl_frame_f2,
    foldl_r_replicate, decide_true]

/-- The parts of a query. -/
lemma parts_bsaQuery (w x : List Bool) (b : ℕ) :
    unframe (bsaQuery w x b) = w ∧ unframe (dropFrame (bsaQuery w x b)) = x ∧
      dropFrame (dropFrame (bsaQuery w x b)) = List.replicate b true := by
  simp [bsaQuery, List.append_assoc]

lemma eq_bsaQuery_of_valid {q : List Bool} (h : bsaValid q = true) :
    q = bsaQuery (unframe q) (unframe (dropFrame q)) (dropFrame (dropFrame q)).length := by
  simp only [bsaValid, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := framed_of_f1 q h
  obtain ⟨h3, h4⟩ := framed_of_f2 _ h2
  have h5 := eq_replicate_of_foldl_r _ h4
  rw [bsaQuery, List.append_assoc, ← h5, h3, h1]

/-! ### The clock of the budgeted universal machine -/

section Budget

variable (d : Desc) (xs : List ℕ) (b : ℕ)

lemma step_of_none {c : SCfg} (h : c.state = none) : step d xs c = (c, none) := by
  obtain ⟨st, ip, ts⟩ := c
  simp only at h
  subst h
  rfl

lemma run_add_of_halted {j : ℕ} (h : (run d xs j).state = none) (m : ℕ) :
    run d xs (j + m) = run d xs j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, run_succ, ih, step_of_none d xs h]

lemma stepOut_add_of_halted {j : ℕ} (h : (run d xs j).state = none) (m : ℕ) :
    (stepOut d xs)^[j + m] (init d, []) = (stepOut d xs)^[j] (init d, []) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih]
    have hj : ((stepOut d xs)^[j] (init d, [])).1 = run d xs j := rfl
    rw [show (stepOut d xs)^[j] (init d, []) = (((stepOut d xs)^[j] (init d, [])).1,
      ((stepOut d xs)^[j] (init d, [])).2) from rfl]
    simp only [stepOut, hj, step_of_none d xs h, Option.toList_none, List.append_nil]

lemma run_add (i m : ℕ) : run d xs (i + m) = (fun c => (step d xs c).1)^[m] (run d xs i) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, run_succ, ih, Function.iterate_succ_apply']

lemma init_state : (run d xs 0).state = some d.q₀ := rfl

/-- The lists of bits of length at most `b`. -/
lemma card_short_lists_lt :
    ((Finset.range (b + 1)).biUnion fun n =>
      (Finset.univ : Finset (Fin n → Bool)).image List.ofFn).card < 2 ^ (b + 1) := by
  refine lt_of_le_of_lt Finset.card_biUnion_le ?_
  have h : ∀ m, ∑ n ∈ Finset.range m, ((Finset.univ : Finset (Fin n → Bool)).image
      List.ofFn).card < 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin m → Bool))) (f := List.ofFn)
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
      omega
  exact h _

lemma mem_short_lists {l : List Bool} (hl : l.length ≤ b) :
    l ∈ (Finset.range (b + 1)).biUnion fun n =>
      (Finset.univ : Finset (Fin n → Bool)).image List.ofFn :=
  Finset.mem_biUnion.mpr ⟨l.length, Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩⟩

/-- **A halting run within the budget halts within the clock**: its configurations after the
first step are pairwise distinct, all described within `b` bits. -/
lemma halt_le_clock {T : ℕ} (hT : (run d xs T).state = none)
    (hmin : ∀ j < T, (run d xs j).state ≠ none)
    (hb : ∀ j < T, (eCfg (run d xs (j + 1))).length ≤ b) : T ≤ 2 ^ (b + 1) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range T) (f := fun j => eCfg (run d xs (j + 1)))
    ((card_short_lists_lt b).trans_le (by simpa using hlt.le))
    (fun j hj => mem_short_lists b (hb j (Finset.mem_range.mp hj)))
  simp only [Finset.mem_range] at hi hj
  have heq'' : run d xs (i + 1) = run d xs (j + 1) := eCfg.injective heq
  clear heq
  obtain ⟨i, j, hi, hj, hlt', heq'⟩ : ∃ i j, i < T ∧ j < T ∧ i < j ∧
      run d xs (i + 1) = run d xs (j + 1) := by
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, hi, hj, h, heq''⟩
    · exact ⟨j, i, hj, hi, h, heq''.symm⟩
  -- the run is periodic from step `i + 1` with period `j - i`
  have hper : ∀ n, run d xs (i + 1 + n * (j - i)) = run d xs (i + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show i + 1 + (n + 1) * (j - i) = (i + 1 + n * (j - i)) + (j - i) by ring, run_add, ih,
        ← run_add, show i + 1 + (j - i) = j + 1 by omega, heq']
  have hrun := hper T
  rw [show i + 1 + T * (j - i) = T + (i + 1 + T * (j - i) - T) by
    have : T ≤ T * (j - i) := Nat.le_mul_of_pos_right _ (by omega)
    omega, run_add_of_halted d xs hT] at hrun
  rcases Nat.lt_or_ge (i + 1) T with h | h
  · exact hmin (i + 1) h (hrun ▸ hT)
  · omega

/-- The run within the budget is the run of the simulation up to a step, all of whose
configurations are within the budget. -/
lemma budgetStep_iterate' (i : ℕ) : ∃ j ≤ i,
    (budgetStep d xs b)^[i] (init d, []) = (run d xs j, ((stepOut d xs)^[j] (init d, [])).2.take 2)
        ∧
      ∀ m < j, (eCfg (run d xs (m + 1))).length ≤ b := by
  induction i with
  | zero => exact ⟨0, le_rfl, rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ i ih =>
    obtain ⟨j, hj, heq, hb⟩ := ih
    rw [Function.iterate_succ_apply', heq, budgetStep]
    dsimp only
    split_ifs with h
    · refine ⟨j + 1, by omega, ?_, fun m hm => ?_⟩
      · rw [run_succ, Function.iterate_succ_apply']
        simp only [stepOut, Prod.mk.injEq, true_and]
        rw [List.take_append, List.take_take, List.take_append, List.length_take]
        congr 2
        omega
      · rcases Nat.lt_or_ge m j with hm' | hm'
        · exact hb m hm'
        · rw [show m = j by omega, run_succ]; exact h
    · exact ⟨j, by omega, rfl, hb⟩

/-- Whether the budgeted universal machine reports acceptance: halted with output `[1]`. -/
def budgetAccepts (r : List ℕ × Bool) : Bool := !Cslib.Complexity.Diagonal.verdict r

/-- **Acceptance within space `b` is decided by the budgeted universal machine** with the clock
`2^(b+1)`. -/
theorem acceptsWithin_iff_budgeted :
    AcceptsWithin d xs b ↔ budgetAccepts (budgetedUniversal (d, xs, 2 ^ (b + 1), b)) = true := by
  constructor
  · rintro ⟨T, hT, hb⟩
    have hhalt : (run d xs T).state = none := by
      have := congrArg Prod.snd hT
      simpa [simulate, run] using this
    obtain ⟨T₀, hT₀s, hT₀m⟩ : ∃ T₀, (run d xs T₀).state = none ∧
        ∀ j < T₀, (run d xs j).state ≠ none :=
      have hex : ∃ j, (run d xs j).state = none := ⟨T, hhalt⟩
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hT₀T : T₀ ≤ T := by
      by_contra h
      exact hT₀m T (by omega) hhalt
    have h0 : 0 < T₀ := by
      rcases Nat.eq_zero_or_pos T₀ with h | h
      · rw [h, init_state] at hT₀s
        cases hT₀s
      · exact h
    have hclock := halt_le_clock d xs b hT₀s hT₀m (fun j hj => hb j (by omega))
    have hsim : ∀ t, T₀ ≤ t → simulate d xs t = simulate d xs T₀ := by
      intro t ht
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
      unfold simulate
      rw [stepOut_add_of_halted d xs hT₀s m]
    rw [budgetedUniversal_eq_of_le d xs b (t := 2 ^ (b + 1)) fun j hj => ?_]
    · simp only [universal, hsim _ hclock, ← hsim T hT₀T, hT]
      rfl
    · rcases Nat.lt_or_ge j T₀ with h | h
      · exact hb j (by omega)
      · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show T₀ ≤ j + 1 by omega)
        rw [hm, run_add_of_halted d xs hT₀s m, show T₀ = (T₀ - 1) + 1 by omega]
        exact hb _ (by omega)
  · intro h
    obtain ⟨j, -, heq, hb⟩ := budgetStep_iterate' d xs b (2 ^ (b + 1))
    simp only [budgetAccepts, Cslib.Complexity.Diagonal.verdict, budgetedUniversal, heq,
      Bool.not_not, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hh, ho⟩ := h
    have hout : ((stepOut d xs)^[j] (init d, [])).2 = [1] := by
      generalize ((stepOut d xs)^[j] (init d, [])).2 = l at ho
      rcases l with _ | ⟨a, _ | ⟨b', l⟩⟩ <;> simp_all
      rfl
    refine ⟨j, ?_, hb⟩
    simp only [simulate, hout]
    simpa [run] using hh

end Budget

end Cslib.Complexity.NtimeDspace.Oracle
