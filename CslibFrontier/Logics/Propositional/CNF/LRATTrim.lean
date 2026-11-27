/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import Std.Data.HashMap.Basic
public import Std.Data.HashSet.Basic
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import CslibFrontier.Foundations.Data.List.Lookup

/-! # Trimming and renumbering LRAT certificates

A solver's LRAT certificate usually adds many clauses that the empty clause does not depend on,
and numbers its clauses sparsely. `Cslib.Logic.PL.CNF.trimCert` keeps the steps that the first
empty-clause step depends on through the hints, found by a pass from that step back to the
first, and drops the deletions. `Cslib.Logic.PL.CNF.renumberCert n` numbers the clauses a
certificate adds `n + 1, n + 2, …` in order, after the `n` clauses of the formula, and maps the
hints accordingly. Both preserve acceptance by the reference checker `Cslib.Logic.PL.CNF.checkLRAT`
(`Cslib.Logic.PL.CNF.checkLRAT_trimCert`, `Cslib.Logic.PL.CNF.checkLRAT_renumberCert`), with no
hypothesis on the certificate: a certificate may reuse the number of a deleted clause, or of a
clause of the formula, and may delete numbers it never added.

The checker looks up a hinted number in a list of numbered clauses, the most recent first, and a
deletion removes every clause with that number. So in an accepted certificate a hint names the
last clause added with that number before it, or the clause of the formula if there is none;
trimming keeps that clause, since the hint asks for it. The clauses that the dropped deletions
would have removed are never looked up, since an accepted certificate hints a deleted number only
after adding it anew. Renumbering sends each hint where its clause went, and the new numbers are
fresh. `renumberCert` drops deletions too: renumbered, a deletion of a number that the certificate
never added, such as `n + 1`, could delete a clause that the renumbered certificate adds.

## Main definitions

* `Cslib.Logic.PL.CNF.trimCert`: the steps the first empty clause depends on, without deletions.
* `Cslib.Logic.PL.CNF.renumberCert`: the added clauses numbered after those of the formula.

## Main results

* `Cslib.Logic.PL.CNF.checkLRAT_trimCert`: trimming preserves acceptance.
* `Cslib.Logic.PL.CNF.checkLRAT_renumberCert`: renumbering preserves acceptance.
* `Cslib.Logic.PL.CNF.checkLRAT_renumberCert_trimCert`: so does their composite, which
  `lrat_tauto` applies to its solver's certificates.
-/

public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- One step of `trimCert`, which reads the certificate from its last step back. The state is the
steps kept so far, in order, and the numbers they hint. An empty-clause step starts afresh, since
the steps after the first one are never checked; a RUP step is kept when a step kept after it
hints its number; deletions are dropped, and RAT steps, which the checker rejects, kept. -/
def trimStep (a : LRAT.IntAction) (s : List LRAT.IntAction × Std.HashSet ℕ) :
    List LRAT.IntAction × Std.HashSet ℕ :=
  match a with
  | .addEmpty _ hints => ([a], hints.foldl (·.insert ·) ∅)
  | .addRup id _ hints =>
    if s.2.contains id then (a :: s.1, hints.foldl (·.insert ·) s.2) else s
  | .addRat .. => (a :: s.1, s.2)
  | .del _ => s

/-- **The steps of a certificate that its first empty clause depends on**, through the hints, in
order, without the deletions. The checker accepts the result whenever it accepts the certificate
(`Cslib.Logic.PL.CNF.checkLRAT_trimCert`). For `lrat_tauto`, dropping the deletions measured
faster than keeping the solver's or deleting each clause after its last hint: the kernel checker's
trie does not get shallower when clauses are deleted, and each deletion costs a step. -/
def trimCert (cert : Array LRAT.IntAction) : Array LRAT.IntAction :=
  (cert.foldr trimStep ([], ∅)).1.toArray

/-- `renumberCert` from the map `m` of the numbers renamed so far, the next fresh number `next`,
and the steps `acc` already renumbered. -/
def renumberCert.go (m : Std.HashMap ℕ ℕ) (next : ℕ) (acc : Array LRAT.IntAction) :
    List LRAT.IntAction → Array LRAT.IntAction
  | [] => acc
  | .addRup id c hints :: rest =>
    go (m.insert id next) (next + 1) (acc.push (.addRup next c (hints.map fun h => m.getD h h)))
      rest
  | .addEmpty _ hints :: rest =>
    go m (next + 1) (acc.push (.addEmpty next (hints.map fun h => m.getD h h))) rest
  | .del _ :: rest => go m next acc rest
  | a@(.addRat ..) :: rest => go m next (acc.push a) rest

/-- **Renumbers the clauses a certificate adds** as `n + 1, n + 2, …` in order, after the `n`
clauses of the formula, and its hints accordingly; a hint to a number the certificate has not
added keeps that number. Deletions are dropped, and RAT steps, which the checker rejects, kept
unchanged. The checker accepts the result whenever it accepts the certificate on a formula of `n`
clauses (`Cslib.Logic.PL.CNF.checkLRAT_renumberCert`). -/
def renumberCert (n : ℕ) (cert : Array LRAT.IntAction) : Array LRAT.IntAction :=
  renumberCert.go ∅ (n + 1) #[] cert.toList

/-! ### Correctness -/

/-- **Propagation along hints transfers** to a lookup that finds, at the image of every hinted
number, the clause the first lookup finds there. -/
theorem propagateWith_map {L L' : ℕ → Option (Clause ℕ)} {f : ℕ → ℕ} :
    ∀ {t : List (Literal ℕ)} {hs : List ℕ},
      (∀ h ∈ hs, ∀ c, L h = some c → L' (f h) = some c) →
      propagateWith L t hs = true → propagateWith L' t (hs.map f) = true
  | _, [], _, h => by simp [propagateWith] at h
  | t, x :: hs, hL, h => by
    simp only [propagateWith] at h
    cases hx : L x with
    | none => simp [hx] at h
    | some c =>
      simp only [hx] at h
      simp only [List.map_cons, propagateWith, hL x List.mem_cons_self c hx]
      cases hr : c.residual t with
      | empty => rfl
      | unit l =>
        simp only [hr] at h
        exact propagateWith_map (fun h hh => hL h (List.mem_cons_of_mem _ hh)) h
      | other => simp [hr] at h

/-- Propagation along hints transfers to a lookup that finds, at every hinted number, the clause
the first lookup finds there. -/
private theorem propagateWith_mono {L L' : ℕ → Option (Clause ℕ)} {t : List (Literal ℕ)}
    {hs : List ℕ} (hL : ∀ h ∈ hs, ∀ c, L h = some c → L' h = some c)
    (h : propagateWith L t hs = true) : propagateWith L' t hs = true := by
  simpa using propagateWith_map (f := fun x => x) hL h

private theorem contains_foldl_insert (l : List ℕ) (s : Std.HashSet ℕ) (h : ℕ) :
    (l.foldl (·.insert ·) s).contains h = (s.contains h || l.contains h) := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.contains_insert, List.contains_cons]
    by_cases hx : x = h
    · subst hx
      simp
    · rw [beq_false_of_ne hx, beq_false_of_ne (Ne.symm hx)]
      simp

/-- A number among the hints, read into a set of numbers, is in it. -/
private theorem contains_foldl_insert_of_mem {hints : Array ℕ} {s : Std.HashSet ℕ} {h : ℕ}
    (hh : h ∈ hints.toList) : (hints.foldl (·.insert ·) s).contains h = true := by
  rw [← Array.foldl_toList, contains_foldl_insert]
  simp [hh]

private theorem contains_foldl_insert_of_contains {hints : Array ℕ} {s : Std.HashSet ℕ} {h : ℕ}
    (hh : s.contains h = true) : (hints.foldl (·.insert ·) s).contains h = true := by
  rw [← Array.foldl_toList, contains_foldl_insert]
  simp [hh]

/-- The trimmed steps are accepted from any database that finds, at every number they hint, the
clause the original database finds there. -/
private theorem checkLRATAux_foldr_trimStep : ∀ (cert : List LRAT.IntAction)
    {db db' : List (ℕ × Clause ℕ)},
    (∀ h, (cert.foldr trimStep ([], ∅)).2.contains h = true →
      ∀ c, db.lookup h = some c → db'.lookup h = some c) →
    checkLRATAux db cert = true → checkLRATAux db' (cert.foldr trimStep ([], ∅)).1 = true
  | [], _, _, _, h => by simp [checkLRATAux] at h
  | .addEmpty id hints :: rest, db, db', hR, h => by
    simp only [List.foldr_cons, trimStep] at hR ⊢
    simpa [checkLRATAux, propagateHints] using
      propagateWith_mono (fun x hx => hR x (contains_foldl_insert_of_mem hx)) h
  | .addRup id c hints :: rest, db, db', hR, h => by
    simp only [checkLRATAux, Bool.and_eq_true] at h
    simp only [List.foldr_cons, trimStep] at hR ⊢
    by_cases hid : (rest.foldr trimStep ([], ∅)).2.contains id = true
    · rw [ite_eq_left hid] at hR ⊢
      have hp := propagateWith_mono
        (fun x hx => hR x (contains_foldl_insert_of_mem hx)) h.1
      simp only [checkLRATAux, Bool.and_eq_true, propagateHints]
      refine ⟨hp, ?_⟩
      refine checkLRATAux_foldr_trimStep rest (fun x hx c' hc => ?_) h.2
      rw [List.lookup_cons_eq_ite] at hc ⊢
      by_cases hxi : x = id
      · rw [ite_eq_left hxi] at hc ⊢
        exact hc
      · rw [ite_eq_right hxi] at hc ⊢
        exact hR x (contains_foldl_insert_of_contains hx) c' hc
    · rw [ite_eq_right hid] at hR ⊢
      refine checkLRATAux_foldr_trimStep rest (fun x hx c' hc => ?_) h.2
      rw [List.lookup_cons_eq_ite, ite_eq_right (by rintro rfl; exact hid hx)] at hc
      exact hR x hx c' hc
  | .addRat .. :: _, _, _, _, h => by simp [checkLRATAux] at h
  | .del ids :: rest, db, db', hR, h => by
    simp only [List.foldr_cons, trimStep] at hR ⊢
    simp only [checkLRATAux] at h
    refine checkLRATAux_foldr_trimStep rest (fun x hx c hc => hR x hx c ?_) h
    rw [List.lookup_filter_not_contains] at hc
    split at hc
    · simp at hc
    · exact hc

/-- **Trimming preserves acceptance**: the checker accepts the trimmed certificate whenever it
accepts the certificate. -/
theorem checkLRAT_trimCert {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) : φ.checkLRAT (trimCert cert) = true := by
  simpa [checkLRAT, trimCert] using
    checkLRATAux_foldr_trimStep cert.toList (fun _ _ _ hc => hc) h

/-- The steps of `renumberCert` as a list, from the map `m` and the next fresh number `next`. -/
private def renumberList (m : Std.HashMap ℕ ℕ) (next : ℕ) :
    List LRAT.IntAction → List LRAT.IntAction
  | [] => []
  | .addRup id c hints :: rest =>
    .addRup next c (hints.map fun h => m.getD h h) ::
      renumberList (m.insert id next) (next + 1) rest
  | .addEmpty _ hints :: rest =>
    .addEmpty next (hints.map fun h => m.getD h h) :: renumberList m (next + 1) rest
  | .del _ :: rest => renumberList m next rest
  | a@(.addRat ..) :: rest => a :: renumberList m next rest

private theorem renumberCert_go (m : Std.HashMap ℕ ℕ) (next : ℕ) (acc : Array LRAT.IntAction)
    (l : List LRAT.IntAction) :
    renumberCert.go m next acc l = acc ++ (renumberList m next l).toArray := by
  induction l generalizing m next acc with
  | nil => simp [renumberCert.go, renumberList]
  | cons a rest ih =>
    cases a <;> simp [renumberCert.go, renumberList, ih]

/-- The renumbered steps are accepted from a database that finds, at the new number of every
number the original database finds a clause at, that clause, the new numbers being below
`next`. -/
private theorem checkLRATAux_renumberList : ∀ (cert : List LRAT.IntAction)
    {db db' : List (ℕ × Clause ℕ)} {m : Std.HashMap ℕ ℕ} {next : ℕ},
    (∀ h c, db.lookup h = some c → m.getD h h < next ∧ db'.lookup (m.getD h h) = some c) →
    checkLRATAux db cert = true → checkLRATAux db' (renumberList m next cert) = true
  | [], _, _, _, _, _, h => by simp [checkLRATAux] at h
  | .addEmpty id hints :: rest, db, db', m, next, hR, h => by
    simp only [checkLRATAux, renumberList, Array.toList_map] at h ⊢
    exact propagateWith_map (fun x _ c hc => (hR x c hc).2) h
  | .addRup id c hints :: rest, db, db', m, next, hR, h => by
    simp only [checkLRATAux, Bool.and_eq_true] at h
    simp only [checkLRATAux, renumberList, Array.toList_map, Bool.and_eq_true]
    refine ⟨propagateWith_map (fun x _ c hc => (hR x c hc).2) h.1,
      checkLRATAux_renumberList rest (fun x c' hc => ?_) h.2⟩
    rw [Std.HashMap.getD_insert]
    rw [List.lookup_cons_eq_ite] at hc
    by_cases hx : x = id
    · subst hx
      rw [ite_eq_left rfl] at hc
      simp [hc]
    · rw [ite_eq_right hx] at hc
      obtain ⟨hlt, hl⟩ := hR x c' hc
      rw [ite_eq_right (by simpa using Ne.symm hx), List.lookup_cons_eq_ite,
        ite_eq_right (Nat.ne_of_lt hlt)]
      exact ⟨by omega, hl⟩
  | .addRat .. :: _, _, _, _, _, _, h => by simp [checkLRATAux] at h
  | .del ids :: rest, db, db', m, next, hR, h => by
    simp only [checkLRATAux, renumberList] at h ⊢
    refine checkLRATAux_renumberList rest (fun x c hc => hR x c ?_) h
    rw [List.lookup_filter_not_contains] at hc
    split at hc
    · simp at hc
    · exact hc

/-- A number at which the starting database of `φ` has a clause is at most `φ.length`. -/
private theorem le_length_of_lookup_lratDB {φ : CNF ℕ} {h : ℕ} {c : Clause ℕ}
    (hc : φ.lratDB.lookup h = some c) : h ≤ φ.length := by
  obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hc
  have hmem : (h, c) ∈ φ.lratDB := by simp [hl]
  obtain ⟨⟨c', i⟩, hi, he⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at he
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hi)
  omega

/-- **Renumbering preserves acceptance**: on a formula of `φ.length` clauses, the checker accepts
the renumbered certificate whenever it accepts the certificate. -/
theorem checkLRAT_renumberCert {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) : φ.checkLRAT (renumberCert φ.length cert) = true := by
  simp only [checkLRAT, renumberCert, renumberCert_go, Array.toList_append,
    List.nil_append]
  refine checkLRATAux_renumberList cert.toList (fun x c hc => ?_) h
  simp only [Std.HashMap.getD_empty]
  exact ⟨Nat.lt_succ_of_le (le_length_of_lookup_lratDB hc), hc⟩

/-- **Trimming and renumbering preserve acceptance**: the certificate that `lrat_tauto` sends to
the kernel is accepted whenever its solver's certificate is. -/
theorem checkLRAT_renumberCert_trimCert {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) :
    φ.checkLRAT (renumberCert φ.length (trimCert cert)) = true :=
  checkLRAT_renumberCert (checkLRAT_trimCert h)

end Cslib.Logic.PL.CNF
