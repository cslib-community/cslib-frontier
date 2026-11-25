/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.LineProof
public import CslibFrontier.Logics.Propositional.Resolution

/-!
# Resolution proofs

Derivability by resolution (`Cslib.Logic.PL.CNF.Derives`) records only that a clause can be
derived. Proof complexity measures derivations, so this file gives them their usual line-based
form: a *resolution proof* from a formula `φ` is a sequence of clauses, each of which is a clause of
`φ` or the resolvent (`Cslib.Logic.PL.Clause.resolvent`) of two earlier clauses on a variable
occurring positively in the first and negatively in the second (`Cslib.Logic.PL.CNF.IsProof`).
Proofs are listed from their last line to their first, so that a proof grows by adding a line in
front. A clause is derivable exactly when it is a line of some proof
(`Cslib.Logic.PL.CNF.derives_iff_exists_isProof`).

A *refutation* is a proof with the empty clause among its lines. Its *size* is its number of lines,
and its *width* the largest width of a line, where the width of a clause
(`Cslib.Logic.PL.Clause.width`) is its number of distinct literals [Ben-Sasson and Wigderson]
[BenSassonWigderson2001]. Clauses are lists, so a line may repeat a literal; repetitions do not
count towards its width.

Fixing a variable transforms proofs in both directions:

* a proof from `φ` becomes a proof from the restricted formula `φ.restrict v b`
  (`Cslib.Logic.PL.CNF.IsProof.restrict`). It has at most as many lines; every line of the original
  proof that `v = b` does not satisfy is replaced by a line with a subset of its literals, and a
  line of the new proof is wider than any given bound only if the line it replaces is;
* a proof from `φ.restrict v b` lifts to a proof from `φ` (`Cslib.Logic.PL.CNF.IsProof.lift`) whose
  lines contain the lines they lift and, besides their literals, at most the literal of `v` that
  `b` falsifies. This is `Cslib.Logic.PL.CNF.Derives.exists_of_restrict` for proofs, keeping
  track of the lines.

Proofs also compose: a proof from `ψ` replays on top of a proof from `φ` among whose lines are the
clauses of `ψ` (`Cslib.Logic.PL.CNF.IsProof.comp`).

## Main definitions

* `Cslib.Logic.PL.Clause.width`: the number of distinct literals of a clause.
* `Cslib.Logic.PL.CNF.IsProof`, `Cslib.Logic.PL.CNF.resolutionRules`: resolution proofs and
  inference rules.
* `Cslib.Logic.PL.CNF.RefutableInSize`, `Cslib.Logic.PL.CNF.RefutableInWidth`: refutability by a
  refutation with a bounded number of lines, or with lines of bounded width.
* `Cslib.Logic.PL.CNF.restrictBy`: restricting a formula by a partial assignment.

## Main results

* `Cslib.Logic.PL.CNF.isProof_iff_lineProof`: resolution proofs as `Cslib.Logic.PL.LineProof`
  derivations.
* `Cslib.Logic.PL.CNF.derives_iff_exists_isProof`: derivable clauses are the lines of proofs.
* `Cslib.Logic.PL.CNF.exists_refutableInSize_iff_not_satisfiable`: resolution refutes exactly the
  unsatisfiable formulas.
* `Cslib.Logic.PL.CNF.IsProof.restrict`, `Cslib.Logic.PL.CNF.IsProof.lift`,
  `Cslib.Logic.PL.CNF.IsProof.restrictBy`: restricting and lifting proofs along a fixed variable or
  a partial assignment.
* `Cslib.Logic.PL.CNF.IsProof.comp`: composing proofs.
* `Cslib.Logic.PL.CNF.RefutableInSize.of_relabel`: refutations of a formula relabelled along an
  injective map give refutations of the formula of the same size.
* `Cslib.Logic.PL.CNF.IsProof.width_le`: the lines of a proof from `φ` have width at most twice
  the number of variables of `φ`.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-! ### Width -/

/-- The **width** of a clause: its number of distinct literals. -/
def Clause.width (c : Clause V) : ℕ := c.toFinset.card

/-- The empty clause has width `0`. -/
@[simp] theorem Clause.width_nil : Clause.width ([] : Clause V) = 0 := rfl

/-- A clause whose literals occur in another clause is at most as wide. -/
theorem Clause.width_le_width {c d : Clause V} (h : ∀ l ∈ c, l ∈ d) : c.width ≤ d.width :=
  Finset.card_le_card fun l hl => List.mem_toFinset.2 (h l (List.mem_toFinset.1 hl))

/-- A clause whose literals occur in another clause, apart from the literal `x`, is at most one
wider. -/
theorem Clause.width_le_width_add_one {c d : Clause V} {x : Literal V}
    (h : ∀ l ∈ c, l ∈ d ∨ l = x) : c.width ≤ d.width + 1 := by
  refine (Finset.card_le_card (t := insert x d.toFinset) fun l hl => ?_).trans
    (Finset.card_insert_le _ _)
  rcases h l (List.mem_toFinset.1 hl) with h | rfl
  · exact Finset.mem_insert_of_mem (List.mem_toFinset.2 h)
  · exact Finset.mem_insert_self _ _

/-- A clause of width zero is empty. -/
theorem Clause.eq_nil_of_width_eq_zero {c : Clause V} (h : c.width = 0) : c = [] := by
  rwa [Clause.width, Finset.card_eq_zero, List.toFinset_eq_empty_iff] at h

/-! ### Proofs -/

/-- A **resolution proof** from `φ`, listed from its last line to its first: every line is a
clause of `φ`, or the resolvent of two lines below it on a variable occurring positively in the
first and negatively in the second. -/
inductive CNF.IsProof (φ : CNF V) : List (Clause V) → Prop
  /-- The empty proof. -/
  | nil : CNF.IsProof φ []
  /-- A clause of `φ` is a new line. -/
  | mem {ls : List (Clause V)} {c : Clause V} (h : CNF.IsProof φ ls) (hc : c ∈ φ) :
      CNF.IsProof φ (c :: ls)
  /-- The resolvent of two lines, on a variable occurring positively in the first and negatively in
  the second, is a new line. -/
  | resolvent {ls : List (Clause V)} {c₁ c₂ : Clause V} (v : V) (h : CNF.IsProof φ ls)
      (h₁ : c₁ ∈ ls) (h₂ : c₂ ∈ ls) (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
      CNF.IsProof φ (c₁.resolvent c₂ v :: ls)

/-- `φ` has a resolution refutation with at most `s` lines. -/
def CNF.RefutableInSize (φ : CNF V) (s : ℕ) : Prop :=
  ∃ ls, φ.IsProof ls ∧ [] ∈ ls ∧ ls.length ≤ s

/-- `φ` has a resolution refutation all of whose lines have width at most `w`. -/
def CNF.RefutableInWidth (φ : CNF V) (w : ℕ) : Prop :=
  ∃ ls, φ.IsProof ls ∧ [] ∈ ls ∧ ∀ c ∈ ls, c.width ≤ w

omit [DecidableEq V] in
/-- A literal belongs to a relabelled clause exactly when it has a preimage with the same sign. -/
theorem Clause.mem_relabel_iff {W : Type*} {f : V → W} {c : Clause V} {w : W} {b : Bool} :
    (w, b) ∈ c.relabel f ↔ ∃ u, (u, b) ∈ c ∧ f u = w := by
  simp only [relabel, List.mem_map, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq,
    ← and_assoc, exists_eq_right]

namespace CNF

variable {φ ψ : CNF V} {ls ls' : List (Clause V)} {c : Clause V}

/-- The inference rules of propositional resolution: from `c₁` containing `(v, true)` and `c₂`
containing `(v, false)`, infer `c₁.resolvent c₂ v`. -/
def resolutionRules (V : Type*) [DecidableEq V] : Set (LineRule (Clause V)) :=
  {r | ∃ c₁ c₂ v, (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ r = ⟨[c₁, c₂], c₁.resolvent c₂ v⟩}

/-- Every resolution rule has two premises. -/
theorem resolutionRules_premises_length_le {r : LineRule (Clause V)}
    (hr : r ∈ resolutionRules V) : r.premises.length ≤ 2 := by
  obtain ⟨_, _, _, -, -, rfl⟩ := hr
  simp

/-- Every resolution rule preserves clause satisfaction. -/
theorem resolutionRules_sound {r : LineRule (Clause V)} (hr : r ∈ resolutionRules V)
    {σ : V → Bool} (hp : ∀ c ∈ r.premises, c.eval σ = true) : r.concl.eval σ = true := by
  obtain ⟨c₁, c₂, v, -, -, rfl⟩ := hr
  exact Clause.eval_resolvent v (hp c₁ (by simp)) (hp c₂ (by simp))

/-- **Resolution proofs as `LineProof` derivations.** -/
theorem isProof_iff_lineProof : φ.IsProof ls ↔ LineProof (resolutionRules V) {c | c ∈ φ} ls := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | mem _ hc ih => exact ih.hyp hc
    | @resolvent _ c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
      exact ih.step ⟨c₁, c₂, v, hv₁, hv₂, rfl⟩
        fun | _, .head _ => h₁ | _, .tail _ (.head _) => h₂
  · intro h
    induction h with
    | nil => exact .nil
    | hyp _ hc ih => exact ih.mem hc
    | step _ hr hp ih =>
      obtain ⟨c₁, c₂, v, hv₁, hv₂, rfl⟩ := hr
      exact ih.resolvent v (hp c₁ List.mem_cons_self)
        (hp c₂ (List.mem_cons_of_mem _ List.mem_cons_self)) hv₁ hv₂

namespace IsProof

/-- Every line of a proof is derivable. -/
theorem derives (h : φ.IsProof ls) (hc : c ∈ ls) : φ.Derives c := by
  induction h generalizing c with
  | nil => simp at hc
  | mem _ hc' ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    exacts [.mem hc', ih hc]
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    exacts [.resolvent v (ih h₁) (ih h₂) hv₁ hv₂, ih hc]

/-- A proof placed above another proof from the same formula gives a proof. -/
theorem append (h : φ.IsProof ls) (h' : φ.IsProof ls') : φ.IsProof (ls ++ ls') :=
  isProof_iff_lineProof.2 ((isProof_iff_lineProof.1 h).append (isProof_iff_lineProof.1 h'))

/-- Proofs survive adding clauses to the formula. -/
theorem mono (h : φ.IsProof ls) (hφψ : φ ⊆ ψ) : ψ.IsProof ls :=
  isProof_iff_lineProof.2 ((isProof_iff_lineProof.1 h).mono_hyp fun _ hc => hφψ hc)

/-- The lines of a proof only mention variables of the formula. -/
theorem fst_mem_vars (h : φ.IsProof ls) (hc : c ∈ ls) {l : Literal V} (hl : l ∈ c) :
    l.1 ∈ φ.vars := by
  induction h generalizing c with
  | nil => simp at hc
  | mem _ hc' ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc', hl⟩, rfl⟩
    · exact ih hc hl
  | resolvent v _ h₁ h₂ _ _ ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases Clause.mem_resolvent.1 hl with ⟨hl, -⟩ | ⟨hl, -⟩
      exacts [ih h₁ hl, ih h₂ hl]
    · exact ih hc hl

/-- A line of a proof from `φ` is at most twice as wide as `φ` has variables. -/
theorem width_le (h : φ.IsProof ls) (hc : c ∈ ls) : c.width ≤ 2 * φ.vars.toFinset.card := by
  have hsub : c.toFinset ⊆ φ.vars.toFinset.image (·, true) ∪ φ.vars.toFinset.image (·, false) := by
    rintro ⟨v, b⟩ hl
    have hv := List.mem_toFinset.2 (h.fst_mem_vars hc (List.mem_toFinset.1 hl))
    cases b <;> simpa using hv
  calc c.width ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 * φ.vars.toFinset.card := by
      rw [Nat.two_mul]; exact Nat.add_le_add Finset.card_image_le Finset.card_image_le

end IsProof

/-- A derivable clause is a line of some proof. -/
theorem Derives.exists_isProof (h : φ.Derives c) : ∃ ls, φ.IsProof ls ∧ c ∈ ls := by
  induction h with
  | mem hc => exact ⟨[_], IsProof.nil.mem hc, List.mem_singleton_self _⟩
  | resolvent v _ _ hv₁ hv₂ ih₁ ih₂ =>
    obtain ⟨ls₁, h₁, hc₁⟩ := ih₁
    obtain ⟨ls₂, h₂, hc₂⟩ := ih₂
    exact ⟨_, (h₁.append h₂).resolvent v (List.mem_append_left _ hc₁)
      (List.mem_append_right _ hc₂) hv₁ hv₂, List.mem_cons_self⟩

/-- **Derivable clauses are the lines of proofs.** -/
theorem derives_iff_exists_isProof : φ.Derives c ↔ ∃ ls, φ.IsProof ls ∧ c ∈ ls :=
  ⟨Derives.exists_isProof, fun ⟨_, h, hc⟩ => h.derives hc⟩

/-- **Resolution refutes exactly the unsatisfiable formulas**, by refutations of some size. -/
theorem exists_refutableInSize_iff_not_satisfiable :
    (∃ s, φ.RefutableInSize s) ↔ ¬ φ.Satisfiable := by
  rw [← derives_nil_iff_not_satisfiable, derives_iff_exists_isProof]
  exact ⟨fun ⟨_, ls, h, hnil, _⟩ => ⟨ls, h, hnil⟩, fun ⟨ls, h, hnil⟩ => ⟨_, ls, h, hnil, le_rfl⟩⟩

/-- A refutation within some width is a refutation of some size. -/
theorem RefutableInWidth.exists_refutableInSize {w : ℕ} (h : φ.RefutableInWidth w) :
    ∃ s, φ.RefutableInSize s :=
  let ⟨ls, h, hnil, _⟩ := h
  ⟨_, ls, h, hnil, le_rfl⟩

/-- `RefutableInSize` is monotone in the size bound. -/
theorem RefutableInSize.mono {s t : ℕ} (h : φ.RefutableInSize s) (hst : s ≤ t) :
    φ.RefutableInSize t :=
  let ⟨ls, h, hnil, hlen⟩ := h
  ⟨ls, h, hnil, hlen.trans hst⟩

/-- `RefutableInWidth` is monotone in the width bound. -/
theorem RefutableInWidth.mono {w w' : ℕ} (h : φ.RefutableInWidth w) (hww' : w ≤ w') :
    φ.RefutableInWidth w' :=
  let ⟨ls, h, hnil, hw⟩ := h
  ⟨ls, h, hnil, fun c hc => (hw c hc).trans hww'⟩

/-- Along an injective map `f`, a proof from `φ.relabel f` is a relabelled proof from `φ`. -/
private theorem IsProof.exists_of_relabel {W : Type*} [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) {ls : List (Clause W)} (h : (φ.relabel f).IsProof ls) :
    ∃ ls', φ.IsProof ls' ∧ ls'.map (Clause.relabel f) = ls := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | mem _ hc ih =>
    obtain ⟨ls', h', rfl⟩ := ih
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact ⟨c' :: ls', h'.mem hc', rfl⟩
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ls', h', rfl⟩ := ih
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 h₁
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.1 h₂
    obtain ⟨u, hu₁, rfl⟩ := Clause.mem_relabel_iff.1 hv₁
    obtain ⟨u', hu₂, hfu⟩ := Clause.mem_relabel_iff.1 hv₂
    obtain rfl : u = u' := (hf hfu).symm
    exact ⟨_ :: ls', h'.resolvent u hc₁ hc₂ hu₁ hu₂,
      by rw [List.map_cons, Clause.relabel_resolvent hf]⟩

/-- **Relabelling back a refutation.** Along an injective map `f`, a refutation of `φ.relabel f`
gives a refutation of `φ` with the same number of lines. -/
theorem RefutableInSize.of_relabel {W : Type*} [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) {s : ℕ} (h : (φ.relabel f).RefutableInSize s) :
    φ.RefutableInSize s := by
  obtain ⟨ls, h, hnil, hlen⟩ := h
  obtain ⟨ls', h', rfl⟩ := h.exists_of_relabel hf
  obtain ⟨c, hc, hc'⟩ := List.mem_map.1 hnil
  obtain rfl : c = [] := List.map_eq_nil_iff.1 hc'
  exact ⟨ls', h', hc, by simpa using hlen⟩

/-! ### Restricting and lifting proofs -/

/-- Helper: lines of `ls'` with literals in `c₁` and in `c₂` give a line of `ls'`, or a resolvent
of two lines of `ls'` on `u`, with literals in `c₁.resolvent c₂ u`. -/
private theorem exists_subset_resolvent {ls' : List (Clause V)} {c₁ c₂ c₁' c₂' : Clause V}
    {u : V} (hc₁' : c₁' ∈ ls') (hc₂' : c₂' ∈ ls') (hsub₁ : ∀ l ∈ c₁', l ∈ c₁)
    (hsub₂ : ∀ l ∈ c₂', l ∈ c₂) :
    ∃ c', (c' ∈ ls' ∨ ∃ c₁' c₂', c₁' ∈ ls' ∧ c₂' ∈ ls' ∧ (u, true) ∈ c₁' ∧
      (u, false) ∈ c₂' ∧ c' = c₁'.resolvent c₂' u) ∧ ∀ l ∈ c', l ∈ c₁.resolvent c₂ u := by
  by_cases hu₁' : (u, true) ∈ c₁'
  · by_cases hu₂' : (u, false) ∈ c₂'
    · exact ⟨_, Or.inr ⟨c₁', c₂', hc₁', hc₂', hu₁', hu₂', rfl⟩,
        Clause.resolvent_subset_resolvent hsub₁ hsub₂⟩
    · exact ⟨c₂', Or.inl hc₂', Clause.subset_resolvent_right hsub₂ hu₂'⟩
  · exact ⟨c₁', Or.inl hc₁', Clause.subset_resolvent_left hsub₁ hu₁'⟩

/-- The lines of a proof from a formula with `v` fixed do not mention `v`. -/
theorem IsProof.fst_ne_of_restrict {v : V} {b : Bool} (h : (φ.restrict v b).IsProof ls)
    (hc : c ∈ ls) {l : Literal V} (hl : l ∈ c) : l.1 ≠ v :=
  (Finset.mem_erase.1 (vars_restrict_subset (List.mem_toFinset.2 (h.fst_mem_vars hc hl)))).1

/-- **Lifting a proof.** A proof from `φ` with `v` fixed to `b` lifts to a proof from `φ`. Every
line of the original proof is contained in a line of the lifted proof that has, besides its
literals, at most the literal `(v, !b)` falsified by `b`, and every line of the lifted proof has,
besides the literals of a line of the original proof, at most that literal. -/
theorem IsProof.lift {v : V} {b : Bool} (h : (φ.restrict v b).IsProof ls') :
    ∃ ls, φ.IsProof ls ∧
      (∀ c' ∈ ls', ∃ c ∈ ls, (∀ l ∈ c', l ∈ c) ∧ ∀ l ∈ c, l ∈ c' ∨ l = (v, !b)) ∧
      ∀ c ∈ ls, ∃ c' ∈ ls', ∀ l ∈ c, l ∈ c' ∨ l = (v, !b) := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @mem ls' c' _ hc' ih =>
    obtain ⟨ls, h, hup, hdown⟩ := ih
    obtain ⟨d, hd, hsub, hd'⟩ := exists_of_mem_restrict hc'
    exact ⟨d :: ls, h.mem hd, List.forall_mem_cons.2 ⟨⟨d, List.mem_cons_self, hsub, hd'⟩,
        fun e he => List.exists_mem_cons_of_exists (hup e he)⟩,
      List.forall_mem_cons.2 ⟨⟨_, List.mem_cons_self, hd'⟩,
        fun e he => List.exists_mem_cons_of_exists (hdown e he)⟩⟩
  | @resolvent ls' c₁' c₂' u _ h₁ h₂ hu₁ hu₂ ih =>
    obtain ⟨ls, h, hup, hdown⟩ := ih
    obtain ⟨d₁, hd₁, hsub₁, hsup₁⟩ := hup c₁' h₁
    obtain ⟨d₂, hd₂, hsub₂, hsup₂⟩ := hup c₂' h₂
    have hd : ∀ l ∈ d₁.resolvent d₂ u, l ∈ c₁'.resolvent c₂' u ∨ l = (v, !b) :=
      Clause.resolvent_subset_resolvent_or_eq hsup₁ hsup₂
    exact ⟨_ :: ls, h.resolvent u hd₁ hd₂ (hsub₁ _ hu₁) (hsub₂ _ hu₂),
      List.forall_mem_cons.2 ⟨⟨_, List.mem_cons_self, Clause.resolvent_subset_resolvent hsub₁ hsub₂,
        hd⟩, fun e he => List.exists_mem_cons_of_exists (hup e he)⟩,
      List.forall_mem_cons.2 ⟨⟨_, List.mem_cons_self, hd⟩,
        fun e he => List.exists_mem_cons_of_exists (hdown e he)⟩⟩

/-- **Composing proofs.** A proof from `ψ` replays on top of a proof from `φ` among whose lines are
all clauses of `ψ`. The lines added are lines of the proof from `ψ`, and every line of the proof
from `ψ` is a line of the result. -/
theorem IsProof.comp (hψ : ψ.IsProof ls') (h : φ.IsProof ls) (hψφ : ∀ c ∈ ψ, c ∈ ls) :
    ∃ ls'', φ.IsProof (ls'' ++ ls) ∧ (∀ c ∈ ls', c ∈ ls'' ++ ls) ∧ ∀ c ∈ ls'', c ∈ ls' := by
  obtain ⟨ls'', h'', hup, hsub, -, -⟩ := (isProof_iff_lineProof.1 hψ).comp
    (isProof_iff_lineProof.1 h) fun c hc => Or.inr (hψφ c hc)
  exact ⟨ls'', isProof_iff_lineProof.2 h'', hup, fun _ hc => hsub.subset hc⟩

/-! ### Restricting proofs by partial assignments -/

/-- `φ` restricted by the partial assignment `ρ`, which fixes every variable `v` with
`ρ v = some b` to `b`: the clauses that `ρ` satisfies are dropped, and the literals of fixed
variables are removed from the others. -/
def restrictBy (φ : CNF V) (ρ : V → Option Bool) : CNF V :=
  (φ.filter fun c => decide (∀ l ∈ c, ρ l.1 ≠ some l.2)).map
    (List.filter fun l => decide (ρ l.1 = none))

omit [DecidableEq V] in
/-- A clause belongs to `φ.restrictBy ρ` iff it is obtained from a clause of `φ` not satisfied by
`ρ` by keeping only the literals on variables where `ρ` is `none`. -/
@[simp] theorem mem_restrictBy {ρ : V → Option Bool} :
    c ∈ φ.restrictBy ρ ↔
      ∃ d ∈ φ, (∀ l ∈ d, ρ l.1 ≠ some l.2) ∧ d.filter (fun l => decide (ρ l.1 = none)) = c := by
  simp [restrictBy, and_assoc]

omit [DecidableEq V] in
/-- A formula restricted by `ρ` mentions only variables that `ρ` does not fix. -/
theorem eq_none_of_mem_restrictBy {ρ : V → Option Bool} (hc : c ∈ φ.restrictBy ρ)
    {l : Literal V} (hl : l ∈ c) : ρ l.1 = none := by
  obtain ⟨d, -, -, rfl⟩ := mem_restrictBy.1 hc
  exact of_decide_eq_true (List.mem_filter.1 hl).2

/-- The lines of a proof from a formula restricted by `ρ` mention only variables that `ρ` does not
fix. -/
theorem IsProof.eq_none_of_restrictBy {ρ : V → Option Bool} (h : (φ.restrictBy ρ).IsProof ls)
    (hc : c ∈ ls) {l : Literal V} (hl : l ∈ c) : ρ l.1 = none := by
  obtain ⟨d, hd, b, hb⟩ := mem_vars.1 (h.fst_mem_vars hc hl)
  exact eq_none_of_mem_restrictBy (l := (l.1, b)) hd hb

/-- **Restricting a proof by a partial assignment.** A proof from `φ` becomes a proof from `φ`
restricted by `ρ`. Every line of the original proof that `ρ` does not satisfy is replaced by a line
of the new proof with a subset of its literals, and the lines of the new proof have, in order,
subsets of the literals of distinct lines of the original proof that `ρ` does not satisfy. In
particular the new proof has at most as many lines with any property inherited by clauses with
more literals as the original proof has unsatisfied lines with that property. -/
theorem IsProof.restrictBy (h : φ.IsProof ls) (ρ : V → Option Bool) :
    ∃ ls', (φ.restrictBy ρ).IsProof ls' ∧
      (∀ c ∈ ls, (∀ l ∈ c, ρ l.1 ≠ some l.2) → ∃ c' ∈ ls', ∀ l ∈ c', l ∈ c) ∧
      ∃ ks, ks.Sublist ls ∧ (∀ c ∈ ks, ∀ l ∈ c, ρ l.1 ≠ some l.2) ∧
        List.Forall₂ (fun c' c => ∀ l ∈ c', l ∈ c) ls' ks := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, [], .slnil, by simp, .nil⟩
  | @mem ls c _ hc ih =>
    obtain ⟨ls', h', hsub, ks, hks, hfree, hF⟩ := ih
    by_cases hsat : ∀ l ∈ c, ρ l.1 ≠ some l.2
    · exact ⟨c.filter (fun l => decide (ρ l.1 = none)) :: ls',
        h'.mem (mem_restrictBy.2 ⟨c, hc, hsat, rfl⟩), List.forall_mem_cons.2
          ⟨fun _ => ⟨_, List.mem_cons_self, fun l hl => (List.mem_filter.1 hl).1⟩,
            fun e he hfe => List.exists_mem_cons_of_exists (hsub e he hfe)⟩,
        c :: ks, hks.cons_cons c, List.forall_mem_cons.2 ⟨hsat, hfree⟩,
        .cons (fun l hl => (List.mem_filter.1 hl).1) hF⟩
    · exact ⟨ls', h', List.forall_mem_cons.2 ⟨fun hfe => absurd hfe hsat, hsub⟩, ks, hks.cons c,
        hfree, hF⟩
  | @resolvent ls c₁ c₂ u _ h₁ h₂ hu₁ hu₂ ih =>
    obtain ⟨ls', h', hsub, ks, hks, hfree, hF⟩ := ih
    by_cases hsat : ∀ l ∈ c₁.resolvent c₂ u, ρ l.1 ≠ some l.2
    swap
    · exact ⟨ls', h', List.forall_mem_cons.2 ⟨fun hfe => absurd hfe hsat, hsub⟩, ks, hks.cons _,
        hfree, hF⟩
    have hne (c' : Clause V) (hc' : c' ∈ ls') (l : Literal V) (hl : l ∈ c') : ρ l.1 = none :=
      h'.eq_none_of_restrictBy hc' hl
    -- the new line to add, if any: a subclause of the resolvent derivable from `ls'`
    have key : ∃ c', (c' ∈ ls' ∨ ∃ c₁' c₂', c₁' ∈ ls' ∧ c₂' ∈ ls' ∧ (u, true) ∈ c₁' ∧
        (u, false) ∈ c₂' ∧ c' = c₁'.resolvent c₂' u) ∧ ∀ l ∈ c', l ∈ c₁.resolvent c₂ u := by
      by_cases hv₁ : ∀ l ∈ c₁, ρ l.1 ≠ some l.2
      swap
      · -- `ρ` satisfies the first premise only through `u = true`, so not the second premise
        push Not at hv₁
        obtain ⟨l, hl, hρl⟩ := hv₁
        obtain rfl := Clause.eq_of_mem_of_notMem_resolvent_left hl fun h => hsat _ h hρl
        obtain ⟨c₂', hc₂', hsub₂⟩ := hsub c₂ h₂ fun l hl hρ => by
          by_cases hl' : l = (u, false)
          · subst hl'
            exact absurd (hρl.symm.trans hρ) (by simp)
          · exact hsat l (Clause.mem_resolvent.2 (Or.inr ⟨hl, hl'⟩)) hρ
        refine ⟨c₂', Or.inl hc₂', Clause.subset_resolvent_right hsub₂ fun hu => ?_⟩
        exact absurd (hρl.symm.trans (hne _ hc₂' (u, false) hu)) (by simp)
      by_cases hv₂ : ∀ l ∈ c₂, ρ l.1 ≠ some l.2
      swap
      · -- `ρ` satisfies the second premise only through `u = false`
        push Not at hv₂
        obtain ⟨l, hl, hρl⟩ := hv₂
        obtain rfl := Clause.eq_of_mem_of_notMem_resolvent_right hl fun h => hsat _ h hρl
        obtain ⟨c₁', hc₁', hsub₁⟩ := hsub c₁ h₁ hv₁
        refine ⟨c₁', Or.inl hc₁', Clause.subset_resolvent_left hsub₁ fun hu => ?_⟩
        exact absurd (hρl.symm.trans (hne _ hc₁' (u, true) hu)) (by simp)
      obtain ⟨c₁', hc₁', hsub₁⟩ := hsub c₁ h₁ hv₁
      obtain ⟨c₂', hc₂', hsub₂⟩ := hsub c₂ h₂ hv₂
      exact exists_subset_resolvent hc₁' hc₂' hsub₁ hsub₂
    obtain ⟨c', hc' | ⟨c₁', c₂', hc₁', hc₂', hu₁', hu₂', rfl⟩, hsub'⟩ := key
    · exact ⟨ls', h', List.forall_mem_cons.2 ⟨fun _ => ⟨c', hc', hsub'⟩, hsub⟩, ks, hks.cons _,
        hfree, hF⟩
    · exact ⟨_ :: ls', h'.resolvent u hc₁' hc₂' hu₁' hu₂', List.forall_mem_cons.2
          ⟨fun _ => ⟨_, List.mem_cons_self, hsub'⟩,
            fun e he hfe => List.exists_mem_cons_of_exists (hsub e he hfe)⟩,
        _ :: ks, hks.cons_cons _, List.forall_mem_cons.2 ⟨hsat, hfree⟩, .cons hsub' hF⟩

private theorem countP_le_of_forall₂ {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} {p : α → Bool} {q : β → Bool} (h : List.Forall₂ R xs ys)
    (hpq : ∀ {x y}, R x y → p x → q y) : xs.countP p ≤ ys.countP q := by
  induction h with
  | nil => exact le_rfl
  | @cons x y xs ys hxy _ ih =>
    by_cases hx : p x
    · simpa only [List.countP_cons_of_pos hx, List.countP_cons_of_pos (hpq hxy hx)] using
        Nat.add_le_add_right ih 1
    · rw [List.countP_cons_of_neg hx]
      exact ih.trans ((List.sublist_cons_self y ys).countP_le)

/-- **Restricting a proof.** A proof from `φ` becomes a proof from `φ` with `v` fixed to `b`, with
at most as many lines. Every line of the original proof that does not contain the literal `(v, b)`
is replaced by a line of the new proof with a subset of its literals, and for every `w` the new
proof has at most as many lines wider than `w` as the original proof has lines without `(v, b)`
wider than `w`. -/
theorem IsProof.restrict (h : φ.IsProof ls) (v : V) (b : Bool) :
    ∃ ls', (φ.restrict v b).IsProof ls' ∧ ls'.length ≤ ls.length ∧
      (∀ c ∈ ls, (v, b) ∉ c → ∃ c' ∈ ls', ∀ l ∈ c', l ∈ c) ∧
      ∀ w, ls'.countP (fun c => w < c.width) ≤ ls.countP (fun c => (v, b) ∉ c ∧ w < c.width) := by
  let ρ : V → Option Bool := fun u => if u = v then some b else none
  have hfree {c : Clause V} : (∀ l ∈ c, ρ l.1 ≠ some l.2) ↔ (v, b) ∉ c := by
    constructor
    · exact fun h hc => h (v, b) hc (ite_eq_left rfl)
    · intro hc
      rintro ⟨u, a⟩ hl
      by_cases hu : u = v
      · subst u
        exact fun he => hc (Option.some.inj (by simpa only [ρ, ite_eq_left rfl] using he) ▸ hl)
      · simp [ρ, hu]
  -- On a clause that survives the restriction, any literal on `v` has sign `!b`.
  have hformula : φ.restrictBy ρ ⊆ φ.restrict v b := by
    intro c hc
    obtain ⟨d, hd, hdc, rfl⟩ := mem_restrictBy.1 hc
    have hvd := hfree.mp hdc
    refine mem_restrict.2 ⟨d, hd, hvd, List.filter_congr ?_⟩
    rintro ⟨u, a⟩ hl
    by_cases hu : u = v
    · subst u
      have ha : a = !b := Bool.eq_not_of_ne fun he => hvd (he ▸ hl)
      simp [ρ, ha]
    · simp [ρ, hu]
  obtain ⟨ls', h', hsub, ks, hks, hfreeks, hF⟩ := h.restrictBy ρ
  refine ⟨ls', h'.mono hformula, hF.length_eq.le.trans hks.length_le,
    fun c hc hvc => hsub c hc (hfree.mpr hvc), fun w => ?_⟩
  calc
    ls'.countP (fun c => w < c.width) ≤ ks.countP (fun c => w < c.width) := by
      refine countP_le_of_forall₂ hF fun hsub hw => ?_
      exact decide_eq_true ((of_decide_eq_true hw).trans_le (Clause.width_le_width hsub))
    _ ≤ ks.countP (fun c => (v, b) ∉ c ∧ w < c.width) :=
      List.countP_mono_left fun c hc hw =>
        decide_eq_true ⟨hfree.mp (hfreeks c hc), of_decide_eq_true hw⟩
    _ ≤ _ := hks.countP_le

end CNF

end Cslib.Logic.PL
