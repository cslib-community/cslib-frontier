/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Output
import CslibFrontier.Foundations.Data.Array.SetGrow
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# A compiled VeriPB kernel checker

The reference checker `Cslib.Logic.PL.VeriPB.checkRed` is written for the kernel: its database
and core set are lists, so looking up a constraint scans the database and every deletion filters
it, and unit propagation keeps its trail as a list. `Cslib.Logic.PL.VeriPB.checkRedFast` checks
the same proofs with compiled data structures, and agrees with it on every input
(`Cslib.Logic.PL.VeriPB.checkRedFast_eq_checkRed`), so every soundness theorem of `checkRed`
applies to it unchanged.

* **The database and the core set** are each a private `DB`: an array indexed by constraint
  number holding the live constraint of each number, and a history list of the constraints in
  database order, deleted ones included. The represented list is the history filtered to the
  live numbers. A lookup reads the array, a
  deletion writes `none` into it, and an addition at a number above all others conses onto the
  history and writes the array. The history is filtered again once the deletions since the last
  filtering outnumber half the array.
* **The steps** `pol`, `rup`, `del`, `deld` and `delc`, which make up the proofs that solvers
  log, run on this representation (the private `stepTopFast`). Every other step
  materializes the represented state, runs the reference step `Cslib.Logic.PL.VeriPB.stepTop`
  and converts back, so its semantics is that of the reference by construction. That costs time
  linear in the database, as the reference step does anyway.
* **The cutting-planes rules** normalize in linear time: the private `toLinearFast` merges the
  terms on a variable through a hash map of positions instead of
  `Cslib.Logic.PL.PBConstr.insertCoeff`'s scan, and produces the same list. Saturation, division
  and weakening renormalize a constraint already in normal form, whose variables are distinct
  (`Cslib.Logic.PL.PBConstr.nodup_termVar_normalize`): there no terms merge, and the hash map
  is skipped.
* **Unit propagation** keeps its trail in a hash set and computes the slack once per
  constraint. Distinct deletion numbers are checked with a hash set.

The proof is by a representation invariant on the compiled state, preserved by each step, as for
`Cslib.Logic.PL.CNF.checkLRATFast_eq_checkLRAT`. The representation and the compiled steps are
private. The structures are updated in place when
uniquely referenced. That speed is measured, not proved.

**Compiled callers run it automatically**: `Cslib.Logic.PL.VeriPB.checkRed_eq_checkRedFast` is a
`@[csimp]` lemma, so the compiler replaces `checkRed` by `checkRedFast` (and `checkRedOutput` by
`checkRedOutputFast`) in compiled code, justified by the equality theorems. The kernel and
`decide` keep reducing the reference definitions, so the text front end, the augmented pipeline
and their `decide +kernel` clients are unchanged.

## Main definitions

* `Cslib.Logic.PL.VeriPB.checkRedFast`, `Cslib.Logic.PL.VeriPB.checkRedOutputFast`: the compiled
  checkers.

## Main results

* `Cslib.Logic.PL.VeriPB.checkRedFast_eq_checkRed`,
  `Cslib.Logic.PL.VeriPB.checkRedOutputFast_eq_checkRedOutput`: they agree with the reference
  checkers.
* `Cslib.Logic.PL.VeriPB.checkRed_eq_checkRedFast`,
  `Cslib.Logic.PL.VeriPB.checkRedOutput_eq_checkRedOutputFast`: the `@[csimp]` lemmas.
-/

public section

namespace Cslib.Logic.PL

namespace PBConstr

/-! ### Normalization in linear time -/

/-- A linear form under construction: its entries, and the position of each variable among
them. -/
private structure LinAcc where
  /-- The position of each variable among the entries. -/
  pos : Std.HashMap ℕ ℕ
  /-- The entries, one per variable, in the order of `Cslib.Logic.PL.PBConstr.toLinear`. -/
  entries : Array (ℕ × ℤ)

/-- Add the term `t` to a linear form under construction, as `Cslib.Logic.PL.PBConstr.insertCoeff`
does: to the entry of its variable if there is one, and as a new last entry otherwise. -/
private def linStep (t : ℕ × Literal ℕ) (acc : LinAcc) : LinAcc :=
  match acc.pos[termVar t]? with
  | some i => ⟨acc.pos, acc.entries.modify i fun e => (e.1, e.2 + termCoeff t)⟩
  | none => ⟨acc.pos.insert (termVar t) acc.entries.size, acc.entries.push (termVar t, termCoeff t)⟩

/-- `Cslib.Logic.PL.PBConstr.toLinear` with the positions of the variables hashed: linear time
instead of quadratic. -/
private def toLinearFast (ts : List (ℕ × Literal ℕ)) : List (ℕ × ℤ) :=
  (ts.foldr linStep
    ⟨Std.HashMap.emptyWithCapacity ts.length, Array.emptyWithCapacity ts.length⟩).entries.toList

private theorem insertCoeff_of_findIdx?_eq_some {v : ℕ} {a : ℤ} :
    ∀ {L : List (ℕ × ℤ)} {i : ℕ}, L.findIdx? (·.1 == v) = some i →
      insertCoeff v a L = L.modify i fun e => (e.1, e.2 + a)
  | [], _, h => by simp at h
  | (u, b) :: L, i, h => by
    rw [List.findIdx?_cons] at h
    by_cases huv : u = v
    · subst huv
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [insertCoeff]
    · simp only [huv, beq_iff_eq, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      simp [insertCoeff, huv, insertCoeff_of_findIdx?_eq_some hj]

private theorem insertCoeff_of_findIdx?_eq_none {v : ℕ} {a : ℤ} :
    ∀ {L : List (ℕ × ℤ)}, L.findIdx? (·.1 == v) = none → insertCoeff v a L = L ++ [(v, a)]
  | [], _ => rfl
  | (u, b) :: L, h => by
    rw [List.findIdx?_cons] at h
    by_cases huv : u = v
    · subst huv; simp at h
    · simp only [huv, beq_iff_eq, ↓reduceIte, Option.map_eq_none_iff] at h
      simp [insertCoeff, huv, insertCoeff_of_findIdx?_eq_none h]

private theorem findIdx?_modify {α : Type} {p : α → Bool} {f : α → α} (hf : ∀ x, p (f x) = p x) :
    ∀ (L : List α) (i : ℕ), (L.modify i f).findIdx? p = L.findIdx? p
  | [], _ => by simp
  | x :: L, 0 => by simp [List.findIdx?_cons, hf]
  | x :: L, i + 1 => by simp [List.findIdx?_cons, findIdx?_modify hf L i]

/-- The construction represents the linear form `L`. -/
private def LinAcc.Rep (acc : LinAcc) (L : List (ℕ × ℤ)) : Prop :=
  acc.entries.toList = L ∧ ∀ v, acc.pos[v]? = L.findIdx? (·.1 == v)

private theorem LinAcc.Rep.linStep {acc : LinAcc} {L : List (ℕ × ℤ)} (h : acc.Rep L)
    (t : ℕ × Literal ℕ) :
    (PBConstr.linStep t acc).Rep (insertCoeff (termVar t) (termCoeff t) L) := by
  obtain ⟨he, hp⟩ := h
  unfold PBConstr.linStep
  split
  · rename_i i hi
    have hf : L.findIdx? (·.1 == termVar t) = some i := (hp _).symm.trans hi
    rw [insertCoeff_of_findIdx?_eq_some hf]
    refine ⟨by simp [Array.toList_modify, he], fun w => ?_⟩
    rw [findIdx?_modify (f := fun e => (e.1, e.2 + termCoeff t)) (fun _ => rfl), ← hp]
  · rename_i hi
    have hf : L.findIdx? (·.1 == termVar t) = none := (hp _).symm.trans hi
    rw [insertCoeff_of_findIdx?_eq_none hf]
    refine ⟨by simp [he], fun w => ?_⟩
    rw [Std.HashMap.getElem?_insert, List.findIdx?_append, ← hp]
    by_cases hw : termVar t = w
    · subst hw
      simp [hi, ← he]
    · simp [hw]

private theorem toLinearFast_eq (ts : List (ℕ × Literal ℕ)) : toLinearFast ts = toLinear ts := by
  have key : ∀ (ts : List (ℕ × Literal ℕ)) (init : LinAcc), init.Rep [] →
      (ts.foldr PBConstr.linStep init).Rep (toLinear ts) := by
    intro ts init h
    induction ts with
    | nil => simpa [toLinear] using h
    | cons t ts ih => exact ih.linStep t
  exact (key ts _ ⟨by simp [Array.emptyWithCapacity], fun v => by simp⟩).1

private theorem mem_insertCoeff {v : ℕ} {a : ℤ} :
    ∀ {L : List (ℕ × ℤ)} {e : ℕ × ℤ}, e ∈ insertCoeff v a L → e.1 = v ∨ e.1 ∈ L.map (·.1)
  | [], e, h => by simp [insertCoeff] at h; simp [h]
  | (u, b) :: L, e, h => by
    unfold insertCoeff at h
    split at h
    · rename_i huv
      rcases List.mem_cons.1 h with rfl | h
      · simp [huv]
      · exact .inr (List.mem_cons_of_mem _ (List.mem_map_of_mem h))
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact (mem_insertCoeff h).imp_right (List.mem_cons_of_mem _)

private theorem map_modify_fst {f : ℕ × ℤ → ℕ × ℤ} (hf : ∀ e, (f e).1 = e.1) :
    ∀ (L : List (ℕ × ℤ)) (i : ℕ), (L.modify i f).map (·.1) = L.map (·.1)
  | [], _ => by simp
  | e :: L, 0 => by simp [hf]
  | e :: L, i + 1 => by simp [map_modify_fst hf L i]

private theorem fst_mem_toLinear {ts : List (ℕ × Literal ℕ)} {e : ℕ × ℤ}
    (h : e ∈ toLinear ts) : e.1 ∈ ts.map termVar := by
  induction ts generalizing e with
  | nil => simp [toLinear] at h
  | cons t ts ih =>
    rcases mem_insertCoeff (L := toLinear ts) h with h | h
    · simp [h]
    · obtain ⟨e', he', heq⟩ := List.mem_map.1 h
      exact List.mem_cons_of_mem _ (heq ▸ ih he')

/-- The linear form of terms on distinct variables lists them in reverse order. -/
private theorem toLinear_of_nodup :
    ∀ {ts : List (ℕ × Literal ℕ)}, (ts.map termVar).Nodup →
      toLinear ts = (ts.map fun t => (termVar t, termCoeff t)).reverse
  | [], _ => rfl
  | t :: ts, h => by
    rw [List.map_cons, List.nodup_cons] at h
    have hn : (toLinear ts).findIdx? (·.1 == termVar t) = none := List.findIdx?_eq_none_iff.2
      fun e he => beq_eq_false_iff_ne.2 fun heq => h.1 (heq ▸ fst_mem_toLinear he)
    change insertCoeff (termVar t) (termCoeff t) (toLinear ts) = _
    rw [insertCoeff_of_findIdx?_eq_none hn, toLinear_of_nodup h.2]
    simp

private theorem nodup_toLinear :
    ∀ ts : List (ℕ × Literal ℕ), ((toLinear ts).map (·.1)).Nodup
  | [] => by simp [toLinear]
  | t :: ts => by
    have ih := nodup_toLinear ts
    change ((insertCoeff (termVar t) (termCoeff t) (toLinear ts)).map (·.1)).Nodup
    rcases h : (toLinear ts).findIdx? (·.1 == termVar t) with _ | i
    · rw [insertCoeff_of_findIdx?_eq_none h, List.map_append, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      rintro a ha b rfl rfl
      obtain ⟨e, he, heq⟩ := List.mem_map.1 ha
      simpa [heq] using List.findIdx?_eq_none_iff.1 h e he
    · rw [insertCoeff_of_findIdx?_eq_some h,
        map_modify_fst (f := fun e => (e.1, e.2 + termCoeff t)) (fun _ => rfl)]
      exact ih

/-- `Cslib.Logic.PL.PBConstr.normalize` in linear time. -/
private def normalizeFast (c : PBConstr) : PBConstr :=
  fromLinear (toLinearFast c.terms) ((c.degree : ℤ) - negSum c.terms)

@[simp] private theorem normalizeFast_eq (c : PBConstr) : c.normalizeFast = c.normalize := by
  simp [normalizeFast, normalize, toLinearFast_eq]

/-- The variables of a normalized constraint are distinct. -/
theorem nodup_termVar_normalize (c : PBConstr) : (c.normalize.terms.map termVar).Nodup := by
  have hsub : ∀ L : List (ℕ × ℤ), ((L.filterMap entryTerm).map termVar).Sublist (L.map (·.1)) := by
    intro L
    induction L with
    | nil => simp
    | cons e L ih =>
      rw [List.filterMap_cons]
      cases h : entryTerm e with
      | none => exact ih.cons _
      | some t =>
        have : termVar t = e.1 := by
          unfold entryTerm at h
          split_ifs at h <;> cases h <;> rfl
        simpa [this] using ih.cons_cons e.1
  exact (nodup_toLinear c.terms).sublist (hsub _)

/-- `Cslib.Logic.PL.PBConstr.normalize` of terms on distinct variables, without merging. -/
private def normalizeDistinct (c : PBConstr) : PBConstr :=
  fromLinear (c.terms.map fun t => (termVar t, termCoeff t)).reverse
    ((c.degree : ℤ) - negSum c.terms)

private theorem normalizeDistinct_eq {c : PBConstr} (h : (c.terms.map termVar).Nodup) :
    c.normalizeDistinct = c.normalize := by
  simp [normalizeDistinct, normalize, toLinear_of_nodup h]

/-- **A constraint on distinct variables with positive coefficients is in normal form** up to the
order of its terms: normalization only reverses them. -/
theorem normalize_of_nodup {c : PBConstr} (h : (c.terms.map termVar).Nodup)
    (hpos : ∀ t ∈ c.terms, 0 < t.1) : c.normalize = ⟨c.terms.reverse, c.degree⟩ := by
  have hterm : ∀ t ∈ c.terms, entryTerm (termVar t, termCoeff t) = some t := by
    rintro ⟨a, v, b⟩ ht
    have ha := hpos _ ht
    cases b <;> simp [entryTerm, termCoeff, ha]
  have hfm : (c.terms.map fun t => (termVar t, termCoeff t)).filterMap entryTerm = c.terms := by
    rw [List.filterMap_map]
    exact (List.filterMap_congr (g := some) fun t ht => hterm t ht).trans (by simp)
  have hmass :
      negMass (c.terms.map fun t => (termVar t, termCoeff t)).reverse = negSum c.terms := by
    simp only [negMass, negSum, List.map_reverse, List.sum_reverse, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨a, v, b⟩ := t
    cases b <;> simp [termCoeff]
  rw [← normalizeDistinct_eq h]
  simp only [normalizeDistinct, fromLinear, List.filterMap_reverse, hfm, hmass]
  congr 1
  omega

/-- `Cslib.Logic.PL.PBConstr.add` through `Cslib.Logic.PL.PBConstr.normalizeFast`. -/
private def addFast (c d : PBConstr) : PBConstr :=
  normalizeFast ⟨c.terms ++ d.terms, c.degree + d.degree⟩

/-- `Cslib.Logic.PL.PBConstr.mul` through `Cslib.Logic.PL.PBConstr.normalizeFast`. -/
private def mulFast (k : ℕ) (c : PBConstr) : PBConstr :=
  normalizeFast ⟨c.terms.map fun t => (k * t.1, t.2), k * c.degree⟩

/-- `Cslib.Logic.PL.PBConstr.div` through `Cslib.Logic.PL.PBConstr.normalizeFast`. -/
private def divFast (k : ℕ) (c : PBConstr) : PBConstr :=
  let n := c.normalizeFast
  normalizeDistinct ⟨n.terms.map fun t => (ceilDiv t.1 k, t.2), ceilDiv n.degree k⟩

/-- `Cslib.Logic.PL.PBConstr.saturate` through `Cslib.Logic.PL.PBConstr.normalizeFast`. -/
private def saturateFast (c : PBConstr) : PBConstr :=
  let n := c.normalizeFast
  normalizeDistinct ⟨n.terms.map fun t => (min t.1 n.degree, t.2), n.degree⟩

/-- `Cslib.Logic.PL.PBConstr.weaken` through `Cslib.Logic.PL.PBConstr.normalizeFast`. -/
private def weakenFast (v : ℕ) (c : PBConstr) : PBConstr :=
  let n := c.normalizeFast
  normalizeDistinct ⟨n.terms.filter (termVar · != v),
    n.degree - coeffSum (n.terms.filter (termVar · == v))⟩

/-- `Cslib.Logic.PL.PBConstr.negate` through `Cslib.Logic.PL.PBConstr.normalizeFast`. -/
private def negateFast (c : PBConstr) : PBConstr :=
  let n := c.normalizeFast
  ⟨n.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2), coeffSum n.terms + 1 - n.degree⟩

@[simp] private theorem addFast_eq (c d : PBConstr) : c.addFast d = c.add d := by
  simp [addFast, add]

@[simp] private theorem mulFast_eq (k : ℕ) (c : PBConstr) : c.mulFast k = c.mul k := by
  simp [mulFast, mul]

private theorem termVar_mk_snd (a : ℕ) (t : ℕ × Literal ℕ) : termVar (a, t.2) = termVar t := rfl

private theorem nodup_map_snd (f : ℕ × Literal ℕ → ℕ) (c : PBConstr) :
    ((c.normalize.terms.map fun t => (f t, t.2)).map termVar).Nodup := by
  simpa [List.map_map, Function.comp_def, termVar_mk_snd] using nodup_termVar_normalize c

@[simp] private theorem divFast_eq (k : ℕ) (c : PBConstr) : c.divFast k = c.div k := by
  simp only [divFast, div, normalizeFast_eq]
  exact normalizeDistinct_eq (nodup_map_snd _ c)

@[simp] private theorem saturateFast_eq (c : PBConstr) : c.saturateFast = c.saturate := by
  simp only [saturateFast, saturate, normalizeFast_eq]
  exact normalizeDistinct_eq (nodup_map_snd _ c)

@[simp] private theorem weakenFast_eq (v : ℕ) (c : PBConstr) : c.weakenFast v = c.weaken v := by
  simp only [weakenFast, weaken, normalizeFast_eq]
  exact normalizeDistinct_eq ((nodup_termVar_normalize c).sublist ((List.filter_sublist).map _))

@[simp] private theorem negateFast_eq (c : PBConstr) : c.negateFast = c.negate := by
  simp [negateFast, negate]

end PBConstr

namespace VeriPB

open PBConstr

/-! ### Cutting planes -/

/-- `Cslib.Logic.PL.VeriPB.polEval` with the constraint numbers resolved by `look` and the
operations computed in linear time. -/
private def polEvalFast (look : ℕ → Option PBConstr) :
    List PolOp → List PBConstr → Option (List PBConstr)
  | [], st => some st
  | .id n :: ops, st => (look n).bind fun c => polEvalFast look ops (c :: st)
  | .lit l :: ops, st => polEvalFast look ops (litAxiom l :: st)
  | .add :: ops, c₂ :: c₁ :: st => polEvalFast look ops (c₁.addFast c₂ :: st)
  | .mul (k + 1) :: ops, c :: st => polEvalFast look ops (c.mulFast (k + 1) :: st)
  | .div (k + 1) :: ops, c :: st => polEvalFast look ops (c.divFast (k + 1) :: st)
  | .sat :: ops, c :: st => polEvalFast look ops (c.saturateFast :: st)
  | .weaken v :: ops, c :: st => polEvalFast look ops (c.weakenFast v :: st)
  | _, _ => none

private theorem polEvalFast_eq {look : ℕ → Option PBConstr} {db : List (ℕ × PBConstr)}
    (h : ∀ n, look n = lookup db n) (ops : List PolOp) (st : List PBConstr) :
    polEvalFast look ops st = polEval db ops st := by
  fun_induction polEval db ops st <;> simp_all [polEvalFast]

/-! ### Reverse unit propagation on a hashed trail -/

/-- A trail of literals, as a hash set. -/
private abbrev Trail := Std.HashSet (Literal ℕ)

/-- `Cslib.Logic.PL.VeriPB.slack` on a hashed trail. -/
private def slackFast (T : Trail) (c : PBConstr) : ℤ :=
  (coeffSum (c.terms.filter fun t => !T.contains (Std.Sat.Literal.negate t.2)) : ℤ) - c.degree

/-- `Cslib.Logic.PL.VeriPB.propagate` on a hashed trail, the slack computed once. -/
private def propagateFast (T : Trail) (c : PBConstr) : Option Trail :=
  let s := slackFast T c
  if s < 0 then none
  else some (c.terms.foldl (fun T' t =>
    if !T.contains (Std.Sat.Literal.negate t.2) && !T.contains t.2 && decide (s < t.1) then
      T'.insert t.2
    else T') T)

/-- The hashed trail `T` holds the literals of the trail `ρ`. -/
private def Trail.Rep (T : Trail) (ρ : List (Literal ℕ)) : Prop := ∀ l, T.contains l = ρ.contains l

private theorem contains_foldl_insert (p : ℕ × Literal ℕ → Bool) :
    ∀ (ts : List (ℕ × Literal ℕ)) (T : Trail) (l : Literal ℕ),
      (ts.foldl (fun T' t => if p t then T'.insert t.2 else T') T).contains l =
        (((ts.filter p).map (·.2)).contains l || T.contains l)
  | [], T, l => by simp
  | t :: ts, T, l => by
    rw [List.foldl_cons, contains_foldl_insert p ts]
    by_cases hp : p t
    · by_cases hl : t.2 = l
      · subst hl
        simp [hp]
      · simp [hp, beq_eq_false_iff_ne.mpr hl, beq_eq_false_iff_ne.mpr (Ne.symm hl)]
    · simp [hp]

private theorem slackFast_eq {T : Trail} {ρ : List (Literal ℕ)} (h : T.Rep ρ) (c : PBConstr) :
    slackFast T c = slack ρ c := by
  have h' : ∀ l, T.contains l = ρ.contains l := h
  simp only [slackFast, slack, falsified, h']

private theorem Trail.Rep.propagateFast {T : Trail} {ρ : List (Literal ℕ)} (h : T.Rep ρ)
    (c : PBConstr) :
    (VeriPB.propagateFast T c).isNone = (propagate ρ c).isNone ∧
      ∀ T' ρ', VeriPB.propagateFast T c = some T' → propagate ρ c = some ρ' → T'.Rep ρ' := by
  have h' : ∀ l, T.contains l = ρ.contains l := h
  unfold VeriPB.propagateFast propagate
  rw [slackFast_eq h]
  by_cases hs : slack ρ c < 0
  · simp [hs]
  · simp only [hs, ↓reduceIte, Option.isNone_some, Option.some.injEq, true_and]
    rintro T' ρ' rfl rfl l
    rw [contains_foldl_insert, List.contains_append, h']
    simp only [falsified, h']

/-- `Cslib.Logic.PL.VeriPB.rupHints` with the constraint numbers resolved by `look`, on a hashed
trail. -/
private def rupHintsFast (look : ℕ → Option PBConstr) (neg : PBConstr) : List Hint → Trail → Bool
  | [], _ => false
  | h :: hs, T =>
    match (match h with | .neg => some neg | .id n => look n) with
    | none => false
    | some c =>
      match propagateFast T c with
      | none => true
      | some T' => rupHintsFast look neg hs T'

private theorem rupHintsFast_eq {look : ℕ → Option PBConstr} {db : List (ℕ × PBConstr)}
    (hl : ∀ n, look n = lookup db n) (neg : PBConstr) :
    ∀ (hs : List Hint) (T : Trail) (ρ : List (Literal ℕ)), T.Rep ρ →
      rupHintsFast look neg hs T = rupHints db neg hs ρ
  | [], _, _, _ => rfl
  | h :: hs, T, ρ, hT => by
    have hr : (match h with | .neg => some neg | .id n => look n) = resolve db neg h := by
      cases h <;> simp [resolve, hl]
    simp only [rupHintsFast, rupHints, hr]
    cases resolve db neg h with
    | none => rfl
    | some c =>
      dsimp only
      obtain ⟨hn, hrep⟩ := hT.propagateFast c
      cases h₁ : VeriPB.propagateFast T c <;> cases h₂ : propagate ρ c
      · rfl
      · simp [h₁, h₂] at hn
      · simp [h₁, h₂] at hn
      · exact rupHintsFast_eq hl neg hs _ _ (hrep _ _ h₁ h₂)

/-- `Cslib.Logic.PL.VeriPB.rup` with the constraint numbers resolved by `look`. -/
private def rupFast (look : ℕ → Option PBConstr) (c : PBConstr) (hs : List Hint) : Bool :=
  rupHintsFast look c.negateFast hs ∅

private theorem rupFast_eq {look : ℕ → Option PBConstr} {db : List (ℕ × PBConstr)}
    (hl : ∀ n, look n = lookup db n) (c : PBConstr) (hs : List Hint) :
    rupFast look c hs = rup db c hs := by
  rw [rupFast, rup, negateFast_eq]
  exact rupHintsFast_eq hl _ hs ∅ [] fun l => by simp

/-! ### Distinct numbers -/

/-- The numbers of `l` are distinct, checked with a hash set of those seen. -/
private def nodupFast (l : List ℕ) : Bool := go l ∅
where
  /-- The numbers of `l` are distinct and none is in `S`. -/
  go : List ℕ → Std.HashSet ℕ → Bool
    | [], _ => true
    | x :: xs, S => if S.contains x then false else go xs (S.insert x)

private theorem nodupFast_go_iff :
    ∀ (l : List ℕ) (S : Std.HashSet ℕ),
      nodupFast.go l S = true ↔ l.Nodup ∧ ∀ x ∈ l, S.contains x = false
  | [], S => by simp [nodupFast.go]
  | x :: xs, S => by
    rw [nodupFast.go]
    split
    · rename_i hx
      simp only [Bool.false_eq_true, false_iff, not_and]
      exact fun _ h => by simp [h x (by simp)] at hx
    · rename_i hx
      rw [nodupFast_go_iff xs]
      simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff, List.nodup_cons,
        List.mem_cons, forall_eq_or_imp, beq_eq_false_iff_ne]
      exact ⟨fun ⟨hn, h⟩ =>
          ⟨⟨fun hm => (h x hm).1 rfl, hn⟩, by simpa using hx, fun y hy => (h y hy).2⟩,
        fun ⟨⟨hm, hn⟩, _, h⟩ => ⟨hn, fun y hy => ⟨fun e => hm (e ▸ hy), h y hy⟩⟩⟩

@[simp] private theorem nodupFast_eq (l : List ℕ) : nodupFast l = decide l.Nodup := by
  rw [Bool.eq_iff_iff, nodupFast, nodupFast_go_iff, decide_eq_true_iff]
  simp

/-! ### Lookup -/

theorem lookup_cons (n m : ℕ) (c : PBConstr) (l : List (ℕ × PBConstr)) :
    lookup ((m, c) :: l) n = if m = n then some c else lookup l n := by
  by_cases h : m = n <;> simp [lookup, h]

theorem lookup_filter_ne (l : List (ℕ × PBConstr)) (i n : ℕ) :
    lookup (l.filter (·.1 != i)) n = if n = i then none else lookup l n := by
  induction l with
  | nil => simp [lookup]
  | cons e l ih =>
    obtain ⟨m, c⟩ := e
    by_cases hm : m = i
    · subst hm
      rw [List.filter_cons_of_neg (by simp), ih, lookup_cons]
      by_cases hn : n = m <;> simp [hn, eq_comm]
    · rw [List.filter_cons_of_pos (by simpa using hm), lookup_cons, lookup_cons, ih]
      by_cases hn : n = i <;> simp [hn, hm]

theorem isSome_lookup_iff (l : List (ℕ × PBConstr)) (n : ℕ) :
    (lookup l n).isSome ↔ ∃ e ∈ l, e.1 = n := by
  simp [lookup, List.find?_isSome]

private theorem any_contains_eq_any_isSome_lookup (l : List (ℕ × PBConstr)) (ids : List ℕ) :
    l.any (fun e => ids.contains e.1) = ids.any fun i => (lookup l i).isSome := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.contains_iff_mem, isSome_lookup_iff]
  exact ⟨fun ⟨e, he, hi⟩ => ⟨e.1, hi, e, he, rfl⟩, fun ⟨i, hi, e, he, h⟩ => ⟨e, he, h ▸ hi⟩⟩

private theorem any_fst_beq_eq_isSome_lookup (l : List (ℕ × PBConstr)) (i : ℕ) :
    l.any (·.1 == i) = (lookup l i).isSome := by
  rw [Bool.eq_iff_iff]
  simp [isSome_lookup_iff]

/-! ### Databases -/

/-- A database of numbered constraints held for fast lookup and deletion.
* `arr` is indexed by number: `some c` for the live constraint `c`, `none` for no live
  constraint.
* `hist` lists the constraints in the order of the database, latest first, possibly with
  deleted ones: the database is `hist` filtered to the live numbers (`DB.toList`).
* `dead` counts the deletions since `hist` was last filtered. -/
private structure DB where
  /-- The constraints, latest first, live or deleted. -/
  hist : List (ℕ × PBConstr)
  /-- The live constraint of each number. -/
  arr : Array (Option PBConstr)
  /-- The number of deletions since `hist` was last filtered. -/
  dead : ℕ

namespace DB

/-- The live constraint numbered `n`. -/
private def get (d : DB) (n : ℕ) : Option PBConstr := d.arr.getD n none

/-- The database as a list, in the order of `hist`. -/
private def toList (d : DB) : List (ℕ × PBConstr) := d.hist.filter fun e => (d.get e.1).isSome

/-- The representation invariant: the numbers of `hist` index `arr`, and `arr` holds the first
constraint of the database with each number. -/
private structure WF (d : DB) : Prop where
  lt : ∀ e ∈ d.hist, e.1 < d.arr.size
  get : ∀ n, lookup d.toList n = d.get n

/-- The database of the list `l`. -/
private def ofList (l : List (ℕ × PBConstr)) : DB :=
  ⟨l, l.foldr (fun e a => a.setGrow e.1 none (some e.2)) #[], 0⟩

/-- Delete the constraint numbered `i`. -/
private def erase (d : DB) (i : ℕ) : DB := ⟨d.hist, d.arr.setIfInBounds i none, d.dead + 1⟩

/-- Delete the constraints with the numbers `ids`. -/
private def eraseAll (d : DB) (ids : List ℕ) : DB := ids.foldl erase d

/-- Drop the deleted constraints from `hist` once they are many. -/
private def compact (d : DB) : DB :=
  if 1024 ≤ d.dead && d.arr.size ≤ 2 * d.dead then ⟨d.toList, d.arr, 0⟩ else d

/-- Add the constraint `c` numbered `m` as the latest; in place if `m` is above every number
seen. -/
private def push (d : DB) (m : ℕ) (c : PBConstr) : DB :=
  if d.arr.size ≤ m then ⟨(m, c) :: d.hist, d.arr.setGrow m none (some c), d.dead⟩
  else ofList ((m, c) :: d.toList)

private theorem get_ofList (l : List (ℕ × PBConstr)) (n : ℕ) : (ofList l).get n = lookup l n := by
  simp only [get, ofList]
  induction l with
  | nil => simp [lookup]
  | cons e l ih =>
    rw [List.foldr_cons, Array.getD_setGrow, ih, lookup_cons]
    by_cases h : n = e.1 <;> simp [h, eq_comm]

private theorem toList_ofList (l : List (ℕ × PBConstr)) : (ofList l).toList = l := by
  refine List.filter_eq_self.2 fun e he => ?_
  rw [get_ofList, isSome_lookup_iff]
  exact ⟨e, he, rfl⟩

private theorem wf_ofList (l : List (ℕ × PBConstr)) : (ofList l).WF where
  lt := by
    simp only [ofList]
    induction l with
    | nil => simp
    | cons e l ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      exacts [Array.lt_size_setGrow _ _ _ _,
        (ih x hx).trans_le (Array.size_le_size_setGrow _ _ _ _)]
  get n := by rw [toList_ofList, get_ofList]

private theorem toList_erase (d : DB) (i : ℕ) :
    (d.erase i).toList = d.toList.filter (·.1 != i) := by
  simp only [toList, erase, get, List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  rw [Array.getD_setIfInBounds_self]
  by_cases h : e.1 = i <;> simp [h]

private theorem WF.erase {d : DB} (hd : d.WF) (i : ℕ) : (d.erase i).WF where
  lt e he := by simpa [DB.erase] using hd.lt e he
  get n := by
    rw [toList_erase d, lookup_filter_ne, hd.get]
    simp only [DB.get, DB.erase, Array.getD_setIfInBounds_self]

private theorem eraseAll_spec (ids : List ℕ) :
    ∀ (d : DB), d.WF →
      (d.eraseAll ids).WF ∧
        (d.eraseAll ids).toList = d.toList.filter fun e => !ids.contains e.1 := by
  induction ids with
  | nil => intro d hd; simp [eraseAll, hd]
  | cons i ids ih =>
    intro d hd
    obtain ⟨hw, hl⟩ := ih (d.erase i) (hd.erase i)
    refine ⟨hw, ?_⟩
    simp only [eraseAll, List.foldl_cons] at hw hl ⊢
    rw [hl, toList_erase d, List.filter_filter]
    refine List.filter_congr fun e _ => ?_
    simp only [List.contains_cons]
    by_cases h : e.1 = i <;> by_cases h' : e.1 ∈ ids <;> simp [h, h', bne]

private theorem toList_refilter (d : DB) (k : ℕ) :
    (⟨d.toList, d.arr, k⟩ : DB).toList = d.toList := by
  simp only [toList, get, List.filter_filter, Bool.and_self]

private theorem toList_compact (d : DB) : d.compact.toList = d.toList := by
  unfold compact
  split
  exacts [toList_refilter d 0, rfl]

private theorem WF.compact {d : DB} (hd : d.WF) : d.compact.WF := by
  unfold DB.compact
  split
  · exact ⟨fun e he => hd.lt e (List.mem_of_mem_filter he), fun n => by
      rw [toList_refilter, hd.get]; rfl⟩
  · exact hd

private theorem push_spec {d : DB} (hd : d.WF) (m : ℕ) (c : PBConstr) :
    (d.push m c).WF ∧ (d.push m c).toList = (m, c) :: d.toList := by
  unfold push
  split
  · rename_i hm
    have htl : (⟨(m, c) :: d.hist, d.arr.setGrow m none (some c), d.dead⟩ : DB).toList =
        (m, c) :: d.toList := by
      simp only [toList, get, List.filter_cons, Array.getD_setGrow, ↓reduceIte, Option.isSome_some]
      congr 1
      exact List.filter_congr fun e he => by
        simp [show e.1 ≠ m by have := hd.lt e he; omega]
    refine ⟨⟨fun e he => ?_, fun n => ?_⟩, htl⟩
    · rcases List.mem_cons.1 he with rfl | he
      exacts [Array.lt_size_setGrow _ _ _ _,
        (hd.lt e he).trans_le (Array.size_le_size_setGrow _ _ _ _)]
    · rw [htl, lookup_cons, hd.get]
      simp only [get, Array.getD_setGrow]
      by_cases h : n = m
      · subst h; simp
      · simp [h, Ne.symm h]
  · exact ⟨wf_ofList _, toList_ofList _⟩

private theorem get_eq {d : DB} (hd : d.WF) (n : ℕ) : d.get n = lookup d.toList n := (hd.get n).symm

private theorem eraseAll_compact_spec {d : DB} (hd : d.WF) (ids : List ℕ) :
    ((d.eraseAll ids).compact).WF ∧
      ((d.eraseAll ids).compact).toList = d.toList.filter fun e => !ids.contains e.1 := by
  obtain ⟨hw, hl⟩ := eraseAll_spec ids d hd
  exact ⟨hw.compact, by rw [toList_compact, hl]⟩

end DB

/-! ### The checker -/

/-- The state of the compiled checker: the database and the core set as `DB`s, and the other
fields of a `Cslib.Logic.PL.VeriPB.State`, whose `db` and `core` are ignored. -/
private structure FState where
  /-- The database. -/
  db : DB
  /-- The core set. -/
  core : DB
  /-- The other fields. -/
  s : State

namespace FState

/-- The state of the reference checker that the compiled state represents. -/
private def toState (f : FState) : State := { f.s with db := f.db.toList, core := f.core.toList }

/-- The compiled state of a state of the reference checker. -/
private def ofState (s : State) : FState :=
  ⟨.ofList s.db, .ofList s.core, { s with db := [], core := [] }⟩

/-- The representation invariant. -/
private structure WF (f : FState) : Prop where
  db : f.db.WF
  core : f.core.WF

@[simp] private theorem toState_ofState (s : State) : (ofState s).toState = s := by
  simp [toState, ofState, DB.toList_ofList]

private theorem wf_ofState (s : State) : (ofState s).WF := ⟨DB.wf_ofList _, DB.wf_ofList _⟩

end FState

/-- **One top-level step of the compiled checker**: `pol`, `rup`, the deletions `del`, `deld`
and `delc` are computed on the compiled state; any other step by
`Cslib.Logic.PL.VeriPB.stepTop` on the state it represents. -/
private def stepTopFast (F : List PBConstr) (obj : Option Objective) (f : FState) :
    TopStep → Option FState
  | .step (.pol ops) =>
    match polEvalFast f.db.get ops [] with
    | some [c] => some ⟨f.db.push f.s.next c, f.core, { f.s with next := f.s.next + 1 }⟩
    | _ => none
  | .step (.rup c hs) =>
    if rupFast f.db.get c hs then
      some ⟨f.db.push f.s.next c.normalizeFast, f.core, { f.s with next := f.s.next + 1 }⟩
    else none
  | .step (.del ids) =>
    if nodupFast ids && ids.all (fun i => (f.db.get i).isSome) then
      let hit := ids.any fun i => (f.core.get i).isSome
      if (f.s.tcb || f.s.order.isSome) && hit then none
      else
        some ⟨(f.db.eraseAll ids).compact, (f.core.eraseAll ids).compact,
          { f.s with chk := f.s.chk && !hit }⟩
    else none
  | .deld ids =>
    if nodupFast ids && ids.all (fun i => (f.db.get i).isSome) &&
        !ids.any (fun i => (f.core.get i).isSome) then
      some ⟨(f.db.eraseAll ids).compact, f.core, f.s⟩
    else none
  | .delc ids =>
    if nodupFast ids && ids.all (fun i => (f.core.get i).isSome) &&
        (!f.s.tcb && f.s.order.isNone || f.db.toList.all (f.core.toList.contains ·)) then
      some ⟨(f.db.eraseAll ids).compact, (f.core.eraseAll ids).compact, { f.s with chk := false }⟩
    else none
  | t => (stepTop F obj f.toState t).map FState.ofState

/-- The compiled step computes the reference step on the represented state, and keeps the
invariant. -/
private theorem stepTopFast_spec (F : List PBConstr) (obj : Option Objective) {f : FState}
    (hf : f.WF) (t : TopStep) :
    (stepTopFast F obj f t).map FState.toState = stepTop F obj f.toState t ∧
      ∀ f' ∈ stepTopFast F obj f t, f'.WF := by
  have hdb := DB.get_eq hf.db
  have hcore := DB.get_eq hf.core
  have hs' : f.toState.db = f.db.toList := rfl
  have hc' : f.toState.core = f.core.toList := rfl
  have ht : f.toState.tcb = f.s.tcb := rfl
  have ho : f.toState.order = f.s.order := rfl
  have fallback (t) : Option.map FState.toState (Option.map FState.ofState
      (stepTop F obj f.toState t)) = stepTop F obj f.toState t := by
    simp [Option.map_map, Function.comp_def]
  have fallbackWF (t) : ∀ f' ∈ (stepTop F obj f.toState t).map FState.ofState, f'.WF :=
    fun _ hf' =>
      let ⟨s', _, he⟩ := Option.mem_map.1 hf'
      he ▸ FState.wf_ofState s'
  cases t with
  | step st =>
    cases st with
    | pol ops =>
      rw [stepTop_step_of_ne_del _ _ _ (by simp)]
      simp only [stepTopFast, runStep, polEvalFast_eq hdb]
      rw [hs']
      rcases polEval f.db.toList ops [] with _ | _ | ⟨c, _ | _⟩
      all_goals first
        | exact ⟨rfl, fun _ h => by cases h⟩
        | refine ⟨?_, fun f' h => ?_⟩
          · simp [FState.toState, (DB.push_spec hf.db f.s.next c).2]
          · cases h; exact ⟨(DB.push_spec hf.db _ _).1, hf.core⟩
    | rup c hs =>
      rw [stepTop_step_of_ne_del _ _ _ (by simp)]
      simp only [stepTopFast, runStep, rupFast_eq hdb]
      rw [hs']
      by_cases hr : rup f.db.toList c hs
      · simp only [hr, ↓reduceIte, Option.map_some, Option.mem_def, Option.some.injEq,
          forall_eq', normalizeFast_eq]
        exact ⟨by simp [FState.toState, (DB.push_spec hf.db f.s.next _).2],
          ⟨(DB.push_spec hf.db _ _).1, hf.core⟩⟩
      · simp [hr]
    | del ids =>
      rw [stepTop_step_del]
      simp only [stepTopFast, runStep, nodupFast_eq, hdb, hcore, hs', hc', ht, ho,
        any_contains_eq_any_isSome_lookup]
      obtain ⟨hw₁, hl₁⟩ := DB.eraseAll_compact_spec hf.db ids
      obtain ⟨hw₂, hl₂⟩ := DB.eraseAll_compact_spec hf.core ids
      split
      · split
        · simp
        · simp only [Option.map_some, Option.mem_def, Option.some.injEq, forall_eq']
          exact ⟨by simp [FState.toState, hl₁, hl₂], ⟨hw₁, hw₂⟩⟩
      · simp
    | _ => exact ⟨fallback _, fallbackWF _⟩
  | deld ids =>
    rw [stepTop_deld]
    simp only [stepTopFast, nodupFast_eq, hdb, hcore, hs', hc',
      any_contains_eq_any_isSome_lookup]
    obtain ⟨hw₁, hl₁⟩ := DB.eraseAll_compact_spec hf.db ids
    split
    · simp only [Option.map_some, Option.mem_def, Option.some.injEq, forall_eq']
      exact ⟨by simp [FState.toState, hl₁], ⟨hw₁, hf.core⟩⟩
    · simp
  | delc ids =>
    rw [stepTop_delc]
    simp only [stepTopFast, nodupFast_eq, hcore, hs', hc', ht, ho,
      any_fst_beq_eq_isSome_lookup]
    obtain ⟨hw₁, hl₁⟩ := DB.eraseAll_compact_spec hf.db ids
    obtain ⟨hw₂, hl₂⟩ := DB.eraseAll_compact_spec hf.core ids
    split
    · simp only [Option.map_some, Option.mem_def, Option.some.injEq, forall_eq']
      exact ⟨by simp [FState.toState, hl₁, hl₂], ⟨hw₁, hw₂⟩⟩
    · simp
  | _ => exact ⟨fallback _, fallbackWF _⟩

/-- Run the top-level steps on the compiled state. -/
private def runTopFast (F : List PBConstr) (obj : Option Objective) :
    FState → List TopStep → Option FState
  | f, [] => some f
  | f, t :: ts =>
    match stepTopFast F obj f t with
    | some f' => runTopFast F obj f' ts
    | none => none

private theorem runTopFast_spec (F : List PBConstr) (obj : Option Objective) :
    ∀ (ts : List TopStep) (f : FState), f.WF →
      (runTopFast F obj f ts).map FState.toState = runTop F obj f.toState ts
  | [], f, _ => by simp [runTopFast, runTop_nil]
  | t :: ts, f, hf => by
    obtain ⟨h₁, h₂⟩ := stepTopFast_spec F obj hf t
    rw [runTopFast, runTop_cons, ← h₁]
    cases h : stepTopFast F obj f t with
    | none => rfl
    | some f' => exact runTopFast_spec F obj ts f' (h₂ f' h)

/-- **The compiled checker**, `Cslib.Logic.PL.VeriPB.checkRed` with the database and the core set
held for fast lookup and deletion, and with the cutting-planes rules and unit propagation in
linear time. -/
def checkRedFast (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ) := none) : Bool :=
  match runTopFast F obj (.ofState (State.init F obj pres)) P.steps with
  | some f => checkConclusion F obj f.toState P.conclusion
  | none => false

/-- `Cslib.Logic.PL.VeriPB.checkRedOutput` on the compiled checker. -/
def checkRedOutputFast (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ)) (sec : OutputSection) : Option Output :=
  match runTopFast F obj (.ofState (State.init F obj pres)) P.steps with
  | some f =>
    let s := f.toState
    let O := sec.file.getD ⟨s.coreConstrs, s.obj, s.pres⟩
    if checkConclusion F obj s P.conclusion && checkOutput s O sec.guarantee then
      some ⟨sec.guarantee, O, s.bound⟩
    else none
  | none => none

private theorem runTopFast_init (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ)) :
    (runTopFast F obj (.ofState (State.init F obj pres)) P.steps).map FState.toState =
      runTop F obj (State.init F obj pres) P.steps := by
  rw [runTopFast_spec F obj _ _ (FState.wf_ofState _), FState.toState_ofState]

/-- **The compiled checker agrees with the reference checker** on every input. -/
theorem checkRedFast_eq_checkRed (F : List PBConstr) (obj : Option Objective) (P : RedProof)
    (pres : Option (List ℕ)) : checkRedFast F obj P pres = checkRed F obj P pres := by
  have h := runTopFast_init F obj P pres
  unfold checkRedFast checkRed
  cases hf : runTopFast F obj (.ofState (State.init F obj pres)) P.steps <;>
    rw [hf] at h <;> simp only [Option.map_none, Option.map_some] at h <;> rw [← h]

/-- The compiled checker of output sections agrees with the reference one on every input. -/
theorem checkRedOutputFast_eq_checkRedOutput (F : List PBConstr) (obj : Option Objective)
    (P : RedProof) (pres : Option (List ℕ)) (sec : OutputSection) :
    checkRedOutputFast F obj P pres sec = checkRedOutput F obj P pres sec := by
  have h := runTopFast_init F obj P pres
  unfold checkRedOutputFast checkRedOutput
  cases hf : runTopFast F obj (.ofState (State.init F obj pres)) P.steps <;>
    rw [hf] at h <;> simp only [Option.map_none, Option.map_some] at h <;> rw [← h]

/-- **The compiled code of `checkRed` is `checkRedFast`.** The kernel and `decide` keep reducing
the reference definition; compiled callers run the compiled checker, justified by
`Cslib.Logic.PL.VeriPB.checkRedFast_eq_checkRed`. -/
@[csimp] theorem checkRed_eq_checkRedFast : @checkRed = @checkRedFast := by
  funext F obj P pres
  exact (checkRedFast_eq_checkRed F obj P pres).symm

/-- The compiled code of `checkRedOutput` is `checkRedOutputFast`. -/
@[csimp] theorem checkRedOutput_eq_checkRedOutputFast :
    @checkRedOutput = @checkRedOutputFast := by
  funext F obj P pres sec
  exact (checkRedOutputFast_eq_checkRedOutput F obj P pres sec).symm

end VeriPB

end Cslib.Logic.PL

end
