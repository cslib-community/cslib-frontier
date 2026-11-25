/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.Resolution.Proof

/-! # Resolution refutations from LRAT certificates

A RUP step of an LRAT certificate adds a clause `C` with hints `h₁, …, hₖ`: from the negation of
`C`, each hinted clause but the last has every literal but one false, so the remaining literal
`lᵢ` is propagated, and the last hinted clause has every literal false. Read backwards, this is a
chain of resolutions, a *trivial resolution* derivation in the sense of Beame, Kautz and Sabharwal
[BeameKautzSabharwal2004]: start from the last hinted clause, whose literals are all false, and
resolve it in turn, for `i = k - 1, …, 1`, with the clause of `hᵢ` on the variable of `lᵢ`
whenever the current clause contains the negation of `lᵢ` and `lᵢ` was not already true. Every
literal of the current clause stays false under the negation of `C` and the literals propagated
before `lᵢ`, so the clause reached at the end has its literals among those of `C`. Resolution has
no weakening rule, so it derives this clause, not `C` itself.

The translation (`Cslib.Logic.PL.CNF.lratToProof`) therefore pairs every clause of the checker's
database with a line of the proof whose literals are among its own, and builds the chain for each
RUP step from these lines. A line with fewer literals than its clause can only end a later chain
earlier: its literals that are not false are among those of the clause, so they are the
propagated literal or none. Clauses are lists, so a line may repeat a literal (resolving `a ∨ b`
with `a ∨ ¬b` gives `a ∨ a`) where the checker's clause has it once; the checker, and the chain,
read clauses only through membership, so repeated literals, and complementary literals in `C` (a
tautology), need no special treatment. Deletions remove clauses from the database and add
nothing. An empty-clause step is a chain from no assumptions, so it ends with the empty clause.

The chain resolves on a variable only when its literal is propagated for the first time, so the
variables it resolves on are distinct and, being variables of proof lines, are variables of the
formula. Starting from the clauses of the formula, a certificate that
`Cslib.Logic.PL.CNF.checkLRAT` accepts therefore becomes a resolution refutation whose lines are
the clauses of the formula, at most one line for each hint, and at most `N` lines for each step,
where `N` is the number of variables of the formula (`Cslib.Logic.PL.CNF.isProof_lratToProof`).
The size lower bounds for resolution then bound the size of every accepted certificate
(`Cslib.Logic.PL.CNF.refutableInSize_of_checkLRAT`).

## Main definitions

* `Cslib.Logic.PL.CNF.lratToProof`: the resolution proof of a certificate.

## Main results

* `Cslib.Logic.PL.CNF.isProof_lratToProof`: the proof of an accepted certificate is a resolution
  refutation, with at most `|φ| + min (hints) (steps · N)` lines.
* `Cslib.Logic.PL.CNF.refutableInSize_of_checkLRAT`: a formula with an accepted certificate has a
  resolution refutation of that size.

## References

* [P. Beame, H. Kautz, A. Sabharwal, *Towards understanding and harnessing the potential of clause
  learning*][BeameKautzSabharwal2004]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide (LRAT.IntAction)
open Std.Sat (Literal.negate)

/-- A clause of the checker's database, with its number, paired with a line of the proof under
construction whose literals are among its own. -/
structure LRATEntry where
  /-- The number of the clause. -/
  id : ℕ
  /-- The clause, as the checker reads it. -/
  clause : Clause ℕ
  /-- The line of the proof standing for the clause. -/
  line : Clause ℕ

/-- The resolvent of `d₀`, which contains `l`, and `d₁`, which contains its negation, on the
variable of `l`, the premise with the positive literal first. -/
def resolveOn (l : Literal ℕ) (d₀ d₁ : Clause ℕ) : Clause ℕ :=
  if l.2 then d₀.resolvent d₁ l.1 else d₁.resolvent d₀ l.1

/-- **The resolution chain of a RUP step**, following unit propagation along the hints from the
literals `t` assumed true, as `Cslib.Logic.PL.CNF.propagateHints` does, by the residual of each
hinted clause (`Cslib.Logic.PL.Clause.residual`): the lines it adds, latest first, and the line
it derives, every literal of which is false under `t`; `none` if propagation fails. After the
rest of the chain derives a line from `l :: t`, where `l` is the literal the current hinted clause
propagates, that line is resolved with the line of the hinted clause on the
variable of `l` when it contains the negation of `l` and `l` is new; otherwise either it or the
hinted clause's line is already false under `t`. -/
def rupChain (db : List LRATEntry) : List (Literal ℕ) → List ℕ → Option (List (Clause ℕ) × Clause ℕ)
  | _, [] => none
  | t, h :: hs =>
    match db.find? (·.id == h) with
    | none => none
    | some e =>
      match e.clause.residual t with
      | .empty => some ([], e.line)
      | .unit l =>
        match rupChain db (l :: t) hs with
        | none => none
        | some (ls₁, d₁) =>
          if Literal.negate l ∈ d₁ ∧ l ∉ t then
            if l ∈ e.line then some (resolveOn l e.line d₁ :: ls₁, resolveOn l e.line d₁)
            else some ([], e.line)
          else some (ls₁, d₁)
      | .other => none

/-- The translation on a database: the lines `ls` so far grow by the chain of each RUP step, and
the result is reached at the first empty-clause step. -/
def lratToProofAux : List LRATEntry → List (Clause ℕ) → List LRAT.IntAction →
    Option (List (Clause ℕ))
  | _, _, [] => none
  | db, ls, .addEmpty _ hints :: _ => (rupChain db [] hints.toList).map fun r => r.1 ++ ls
  | db, ls, .addRup id c hints :: rest =>
    match rupChain db ((Clause.ofDIMACS c.toList).map Literal.negate) hints.toList with
    | none => none
    | some (ls₁, d) => lratToProofAux (⟨id, Clause.ofDIMACS c.toList, d⟩ :: db) (ls₁ ++ ls) rest
  | _, _, .addRat .. :: _ => none
  | db, ls, .del ids :: rest =>
    lratToProofAux (db.filter fun e => !ids.toList.contains e.id) ls rest

/-- **The resolution proof of an LRAT certificate**: the clauses of `φ`, each standing for itself
under its number `i + 1`, followed by the chains of the RUP steps up to the first empty-clause
step. -/
def lratToProof (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Option (List (Clause ℕ)) :=
  lratToProofAux (φ.zipIdx.map fun e => ⟨e.2 + 1, e.1, e.1⟩) φ cert.toList

/-! ### Correctness -/

variable {φ : CNF ℕ}

/-- The database the checker sees. -/
private def LRATEntry.toPair (e : LRATEntry) : ℕ × Clause ℕ := (e.id, e.clause)

/-- The variables of `φ` with neither literal in `t`. -/
private def freeVars (φ : CNF ℕ) (t : List (Literal ℕ)) : Finset ℕ :=
  φ.vars.toFinset.filter fun v => (v, true) ∉ t ∧ (v, false) ∉ t

/-- Every clause of the formula is a line of a proof. -/
private theorem isProof_of_subset : ∀ {ls : List (Clause ℕ)}, (∀ c ∈ ls, c ∈ φ) → φ.IsProof ls
  | [], _ => .nil
  | _ :: _, h => (isProof_of_subset fun c hc => h c (List.mem_cons_of_mem _ hc)).mem
      (h _ List.mem_cons_self)

private theorem negate_eq_iff {l m : Literal ℕ} : Literal.negate m = l ↔ m = Literal.negate l := by
  constructor <;> rintro rfl <;> simp

/-- Resolving on a literal of `d₀` whose negation is in `d₁` adds a line with the other literals
of both. -/
private theorem isProof_resolveOn {ls : List (Clause ℕ)} (h : φ.IsProof ls) {l : Literal ℕ}
    {d₀ d₁ : Clause ℕ} (h₀ : d₀ ∈ ls) (h₁ : d₁ ∈ ls) (hl₀ : l ∈ d₀)
    (hl₁ : Literal.negate l ∈ d₁) :
    φ.IsProof (resolveOn l d₀ d₁ :: ls) ∧ ∀ m ∈ resolveOn l d₀ d₁,
      (m ∈ d₀ ∧ m ≠ l) ∨ (m ∈ d₁ ∧ m ≠ Literal.negate l) := by
  obtain ⟨v, b⟩ := l
  cases b
  · refine ⟨h.resolvent v h₁ h₀ hl₁ hl₀, fun m hm => ?_⟩
    rcases Clause.mem_resolvent.1 hm with hm | hm
    exacts [.inr hm, .inl hm]
  · exact ⟨h.resolvent v h₀ h₁ hl₀ hl₁, fun m hm => Clause.mem_resolvent.1 hm⟩

/-- The checker's lookup in the database it sees is the lookup in the translation's. -/
private theorem find?_map_toPair (db : List LRATEntry) (h : ℕ) :
    (db.map LRATEntry.toPair).find? (·.1 == h) = (db.find? (·.id == h)).map LRATEntry.toPair := by
  rw [List.find?_map]
  rfl

/-- **The chain of a RUP step.** If unit propagation along the hints succeeds in the checker's
database, the chain is defined: it extends the proof by at most one line for each hint and at most
one line for each variable of `φ` free in `t`, and derives a line every literal of which is false
under `t`. -/
private theorem rupChain_spec {db : List LRATEntry} {ls : List (Clause ℕ)} (hls : φ.IsProof ls)
    (hdb : ∀ e ∈ db, e.line ∈ ls ∧ ∀ l ∈ e.line, l ∈ e.clause) :
    ∀ (hs : List ℕ) (t : List (Literal ℕ)),
      propagateHints (db.map LRATEntry.toPair) t hs = true →
      ∃ ls' d, rupChain db t hs = some (ls', d) ∧ φ.IsProof (ls' ++ ls) ∧ d ∈ ls' ++ ls ∧
        (∀ l ∈ d, Literal.negate l ∈ t) ∧ ls'.length ≤ hs.length ∧
        ls'.length ≤ (freeVars φ t).card := by
  intro hs
  induction hs with
  | nil => intro t h; simp [propagateHints_nil] at h
  | cons h hs ih =>
    intro t hprop
    rw [propagateHints_cons, find?_map_toPair] at hprop
    rcases hfind : db.find? (·.id == h) with _ | e
    · simp [hfind] at hprop
    have he := List.mem_of_find?_eq_some hfind
    obtain ⟨hd₀, hsub⟩ := hdb e he
    simp only [hfind, Option.map_some, LRATEntry.toPair] at hprop
    rcases hres : e.clause.residual t with _ | l | _
    · -- every literal of the hinted clause is false: the chain ends with its line
      exact ⟨[], e.line, by simp only [rupChain, hfind, hres], hls, hd₀,
        fun m hm => Clause.residual_eq_empty_iff.1 hres m (hsub m hm), Nat.zero_le _,
        Nat.zero_le _⟩
    swap
    · simp [hres] at hprop
    simp only [hres] at hprop
    obtain ⟨-, hlnew, hoth⟩ := Clause.residual_eq_unit_iff.1 hres
    have hopen : ∀ m ∈ e.line, Literal.negate m ∈ t ∨ m = l := fun m hm =>
      (em (m = l)).elim .inr fun hne => .inl (hoth m (hsub m hm) hne)
    obtain ⟨ls₁, d₁, hc₁, hp₁, hd₁, hf₁, hlen₁, hvar₁⟩ := ih (l :: t) hprop
    have hfree : freeVars φ (l :: t) ⊆ freeVars φ t := by
      intro v hv
      simp only [freeVars, Finset.mem_filter, List.mem_cons, not_or] at hv ⊢
      exact ⟨hv.1, hv.2.1.2, hv.2.2.2⟩
    have hrun : rupChain db t (h :: hs) =
        if Literal.negate l ∈ d₁ ∧ l ∉ t then
          if l ∈ e.line then some (resolveOn l e.line d₁ :: ls₁, resolveOn l e.line d₁)
          else some ([], e.line)
        else some (ls₁, d₁) := by
      simp only [rupChain, hfind, hres, hc₁]
    rw [hrun]
    by_cases hA : Literal.negate l ∈ d₁ ∧ l ∉ t
    · simp only [hA, not_false_eq_true, and_self, ↓reduceIte]
      by_cases hl₀ : l ∈ e.line
      · simp only [hl₀, ↓reduceIte]
        obtain ⟨hp, hmem⟩ := isProof_resolveOn hp₁ (List.mem_append_right _ hd₀) hd₁ hl₀ hA.1
        refine ⟨_ :: ls₁, _, rfl, hp, List.mem_cons_self, fun m hm => ?_, by simp; omega, ?_⟩
        · rcases hmem m hm with ⟨hm, hne⟩ | ⟨hm, hne⟩
          exacts [(hopen m hm).resolve_right hne,
            (List.mem_cons.1 (hf₁ m hm)).resolve_left fun h => hne (negate_eq_iff.1 h)]
        · -- the variable resolved on is free in `t` but not in `l :: t`
          have hv : l.1 ∈ freeVars φ t := by
            obtain ⟨v, b⟩ := l
            simp only [freeVars, Finset.mem_filter, List.mem_toFinset]
            refine ⟨hls.fst_mem_vars hd₀ hl₀, ?_⟩
            cases b
            · exact ⟨by simpa [Literal.negate] using hlnew, hA.2⟩
            · exact ⟨hA.2, by simpa [Literal.negate] using hlnew⟩
          have hv' : l.1 ∉ freeVars φ (l :: t) := by
            obtain ⟨v, b⟩ := l
            cases b <;> simp [freeVars]
          have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
            ⟨hfree, fun h => hv' (h ▸ hv)⟩)
          simp only [List.length_cons]
          omega
      · simp only [hl₀, ↓reduceIte]
        exact ⟨[], e.line, rfl, hls, hd₀, fun m hm => (hopen m hm).resolve_right
          (fun h => hl₀ (h ▸ hm)), Nat.zero_le _, Nat.zero_le _⟩
    · simp only [hA, ↓reduceIte]
      refine ⟨ls₁, d₁, rfl, hp₁, hd₁, fun m hm => ?_, by simp; omega,
        hvar₁.trans (Finset.card_le_card hfree)⟩
      rcases List.mem_cons.1 (hf₁ m hm) with h | h
      · obtain rfl := negate_eq_iff.1 h
        simpa using Classical.not_not.1 fun hlt => hA ⟨hm, hlt⟩
      · exact h

/-- The translation of an accepted certificate on a database whose clauses stand for lines of a
proof. -/
private theorem lratToProofAux_spec :
    ∀ (cert : List LRAT.IntAction) (db : List LRATEntry) (ls : List (Clause ℕ)),
      φ.IsProof ls → (∀ e ∈ db, e.line ∈ ls ∧ ∀ l ∈ e.line, l ∈ e.clause) →
      checkLRATAux (db.map LRATEntry.toPair) cert = true →
      ∃ ls', lratToProofAux db ls cert = some (ls' ++ ls) ∧ φ.IsProof (ls' ++ ls) ∧
        [] ∈ ls' ++ ls ∧ ls'.length ≤ lratHintCount cert ∧
        ls'.length ≤ cert.length * φ.vars.toFinset.card
  | [], _, _, _, _, h => by simp [checkLRATAux] at h
  | .addEmpty _ hints :: rest, db, ls, hls, hdb, h => by
    simp only [checkLRATAux] at h
    obtain ⟨ls', d, hc, hp, hd, hf, hlen, hvar⟩ := rupChain_spec hls hdb _ _ h
    obtain rfl : d = [] := List.eq_nil_iff_forall_not_mem.2 fun m hm => by simpa using hf m hm
    refine ⟨ls', by simp [lratToProofAux, hc], hp, hd, ?_, ?_⟩
    · simp only [lratHintCount]
      simp at hlen
      omega
    · have := hvar.trans (Finset.card_filter_le _ _)
      simp only [List.length_cons, Nat.succ_mul]
      omega
  | .addRup id c hints :: rest, db, ls, hls, hdb, h => by
    simp only [checkLRATAux, Bool.and_eq_true] at h
    obtain ⟨ls₁, d, hc, hp₁, hd, hf, hlen₁, hvar₁⟩ := rupChain_spec hls hdb _ _ h.1
    have hdb' : ∀ e ∈ (⟨id, Clause.ofDIMACS c.toList, d⟩ :: db : List LRATEntry),
        e.line ∈ ls₁ ++ ls ∧ ∀ l ∈ e.line, l ∈ e.clause := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · refine ⟨hd, fun m hm => ?_⟩
        obtain ⟨m', hm', hmm'⟩ := List.mem_map.1 (hf m hm)
        rwa [← show m' = m by simpa using negate_eq_iff.1 hmm']
      · exact ⟨List.mem_append_right _ (hdb e he).1, (hdb e he).2⟩
    obtain ⟨ls₂, hc₂, hp₂, hnil, hlen₂, hvar₂⟩ :=
      lratToProofAux_spec rest _ _ hp₁ hdb' (by simpa [LRATEntry.toPair] using h.2)
    refine ⟨ls₂ ++ ls₁, ?_, by simpa using hp₂, by simpa using hnil, ?_, ?_⟩
    · simp [lratToProofAux, hc, hc₂]
    · simp only [lratHintCount, List.length_append]
      simp at hlen₁
      omega
    · have := hvar₁.trans (Finset.card_filter_le _ _)
      simp only [List.length_append, List.length_cons, Nat.succ_mul]
      omega
  | .addRat .. :: _, _, _, _, _, h => by simp [checkLRATAux] at h
  | .del ids :: rest, db, ls, hls, hdb, h => by
    simp only [checkLRATAux] at h
    have hmap : (db.map LRATEntry.toPair).filter (fun e => !ids.toList.contains e.1) =
        (db.filter fun e => !ids.toList.contains e.id).map LRATEntry.toPair := by
      rw [List.filter_map]
      rfl
    rw [hmap] at h
    obtain ⟨ls', hc, hp, hnil, hlen, hvar⟩ := lratToProofAux_spec rest
      (db.filter fun e => !ids.toList.contains e.id) ls hls
      (fun e he => hdb e (List.mem_filter.1 he).1)
      h
    refine ⟨ls', by simpa [lratToProofAux] using hc, hp, hnil, ?_, ?_⟩
    · simpa [lratHintCount] using hlen
    · simp only [List.length_cons, Nat.succ_mul]
      omega

/-- **The resolution proof of an accepted LRAT certificate is a refutation**: it is a resolution
proof from `φ` containing the empty clause, with at most `|φ|` lines plus the smaller of the
number of hints of the certificate and its number of steps times the number `N` of variables of
`φ`. -/
theorem isProof_lratToProof {cert : Array LRAT.IntAction} (h : φ.checkLRAT cert = true) :
    ∃ ls, φ.lratToProof cert = some ls ∧ φ.IsProof ls ∧ [] ∈ ls ∧
      ls.length ≤
        φ.length + min (lratHintCount cert.toList) (cert.size * φ.vars.toFinset.card) := by
  have hdb : (φ.zipIdx.map fun e => (⟨e.2 + 1, e.1, e.1⟩ : LRATEntry)).map LRATEntry.toPair =
      φ.lratDB := by
    simp [lratDB, LRATEntry.toPair, Function.comp_def]
  obtain ⟨ls', hc, hp, hnil, hlen, hvar⟩ := lratToProofAux_spec cert.toList
    (φ.zipIdx.map fun e => (⟨e.2 + 1, e.1, e.1⟩ : LRATEntry)) φ
    (isProof_of_subset fun _ => id)
    (fun e he => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      exact ⟨List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), fun _ hl => hl⟩)
    (by rw [hdb]; exact h)
  refine ⟨_, hc, hp, hnil, ?_⟩
  simp only [List.length_append, Array.length_toList] at hlen hvar ⊢
  omega

/-- **A formula with an accepted LRAT certificate has a resolution refutation** with at most `|φ|`
lines plus the smaller of the number of hints and the number of steps times the number `N` of
variables of `φ`. -/
theorem refutableInSize_of_checkLRAT {cert : Array LRAT.IntAction} (h : φ.checkLRAT cert = true) :
    φ.RefutableInSize
      (φ.length + min (lratHintCount cert.toList) (cert.size * φ.vars.toFinset.card)) :=
  let ⟨ls, _, hp, hnil, hlen⟩ := isProof_lratToProof h
  ⟨ls, hp, hnil, hlen⟩

end Cslib.Logic.PL.CNF
