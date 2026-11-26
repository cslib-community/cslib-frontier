/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.CuttingPlanes
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
import Mathlib.Tactic.Linarith

/-!
# Cutting planes proofs are VeriPB `pol` proofs

A cutting planes proof (`Cslib.Logic.PL.CuttingPlanes.IsProof`) from the inequalities of the
constraints of a VeriPB database compiles, line by line, into `pol` steps that the kernel checker
accepts on that database (`Cslib.Logic.PL.VeriPB.exists_runSteps_of_isProof`). A line becomes one
`pol` step of at most three operations (`Cslib.Logic.PL.VeriPB.CPLine.toStep`):

* a hypothesis is a constraint number, followed by `1 *`, which normalizes it;
* the axioms `xᵥ ≥ 0` and `-xᵥ ≥ -1` are the literal axioms `xᵥ ≥ 0` and `¬xᵥ ≥ 0`;
* addition, multiplication by a positive integer and division by a positive integer are the `pol`
  operations `+`, `k *` and `k d` on the numbers of the earlier lines. When `k` divides every
  coefficient, VeriPB's division, which rounds the coefficients and the degree up, is the exact
  division of cutting planes.

The line at position `p` of the proof, counted from its first line, takes the number `n + p`,
where `n` is the next number of the database, so the compilation works for any database, including
one reached after other steps.

**The correspondence.** The constraint `c` that a compiled line leaves represents the line's
inequality `I` (`Cslib.Logic.PL.PBConstr.Represents`): `c.toIneq` has the coefficients of `I`
and a bound at least that of `I`, and the terms of `c` are on distinct variables. It cannot be
exactly `I` in general. VeriPB normalizes the constraints that `+`, `*` and `d` produce, and the
degree of a normalized constraint is a natural number. So the bound of its inequality is at least
`-N`, where `N` is the sum of the magnitudes of its negative coefficients. A cutting planes line may
have a lower bound, as `0 ≥ -1` (`xᵥ ≥ 0` plus `-xᵥ ≥ -1`) does, and VeriPB keeps `0 ≥ 0`. Raised
bounds then propagate: adding `2 xᵥ ≥ 1` to the raised line gives a stronger line than adding it
to the original. The raised inequality implies the original one, so a refutation still compiles
into a refutation.

**Refutations** (`Cslib.Logic.PL.VeriPB.exists_check_of_refutableInSize`). A cutting planes
refutation of `{I | ∃ c ∈ F, c.toIneq = I}` with `s` lines compiles into a proof that
`Cslib.Logic.PL.VeriPB.check F` accepts, with at most `s` steps, each a `pol` step of at most three
operations without saturation. With `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check`, the
`pol` fragment of VeriPB without saturation and cutting planes refute the same sets
(`Cslib.Logic.PL.VeriPB.exists_check_iff_exists_refutableInSize`).

**Sizes.** A refutation with `s` lines compiles into at most `s` steps and `3 s` operations
(`Cslib.Logic.PL.VeriPB.exists_check_of_refutableInSize`).
Conversely, a checked proof with `m` operations on constraints `F` whose variables, and those of its
literal axioms, are in `S` gives a refutation with at most `16 (|S| + 1) (|F| + m + 1)` lines
(`Cslib.Logic.PL.VeriPB.refutableInSize_of_check`). This is linear in `|F| + m` for a fixed number
of variables. The factor `|S| + 1` is needed: a rounding-up division, a weakening, a normalization
whose degree is clamped at `0`, or the final contradiction adds a literal axiom for every term, and
no bound in the number of constraints, steps and operations alone exists
(`Cslib.Logic.PL.VeriPB.not_exists_refutableInSize_of_check`). Coefficient sizes are not measured.

## Main definitions

* `Cslib.Logic.PL.PBConstr.Dominates`, `Cslib.Logic.PL.PBConstr.Represents`: a constraint whose
  inequality has the coefficients of a given inequality and a bound at least its bound.
* `Cslib.Logic.PL.VeriPB.CPLine`, `Cslib.Logic.PL.VeriPB.CPLine.toStep`: a line of a cutting planes
  proof with its rule and premises, and the `pol` step it compiles to.

## Main results

* `Cslib.Logic.PL.VeriPB.exists_runSteps_of_isProof`: cutting planes proofs from a database
  compile into accepted `pol` steps, one per line.
* `Cslib.Logic.PL.VeriPB.exists_check_of_refutableInSize`: refutations compile into checked
  proofs of `UNSAT`, with as many steps as lines and three operations per line.
* `Cslib.Logic.PL.VeriPB.exists_check_iff_exists_refutableInSize`,
  `Cslib.Logic.PL.VeriPB.exists_check_cnf_iff_exists_refutableInSize`: the `pol` fragment without
  saturation and cutting planes refute the same sets.
-/

public section

namespace Cslib.Logic.PL

open Ineq PBConstr CuttingPlanes

namespace PBConstr

/-! ### Constraints representing inequalities -/

/-- The constraint `c` **dominates** the inequality `I`: the inequality of `c` has the coefficients
of `I` and a bound at least that of `I`, so it implies `I`. -/
@[expose] def Dominates (c : PBConstr) (I : Ineq ℕ) : Prop :=
  c.toIneq.coeff = I.coeff ∧ I.bound ≤ c.toIneq.bound

/-- The constraint `c` **represents** the inequality `I`: it dominates `I`, and its terms are on
distinct variables, as those of a normalized constraint are. -/
@[expose] def Represents (c : PBConstr) (I : Ineq ℕ) : Prop :=
  c.Dominates I ∧ (c.terms.map termVar).Nodup

theorem dominates_toIneq (c : PBConstr) : c.Dominates c.toIneq := ⟨rfl, le_rfl⟩

theorem Dominates.normalize {c : PBConstr} {I : Ineq ℕ} (h : c.Dominates I) :
    c.normalize.Dominates I :=
  ⟨(coeff_toIneq_normalize c).trans h.1, h.2.trans (bound_toIneq_le_normalize c)⟩

theorem Dominates.represents_normalize {c : PBConstr} {I : Ineq ℕ} (h : c.Dominates I) :
    c.normalize.Represents I :=
  ⟨h.normalize, nodup_termVar_normalize c⟩

theorem Dominates.represents_add {c d : PBConstr} {I J : Ineq ℕ} (hc : c.Dominates I)
    (hd : d.Dominates J) :
    (c.add d).Represents (I + J) := by
  refine Dominates.represents_normalize ⟨?_, ?_⟩ <;> rw [toIneq_append]
  · rw [coeff_add, coeff_add, hc.1, hd.1]
  · rw [bound_add, bound_add]
    exact add_le_add hc.2 hd.2

theorem Dominates.represents_mul {c : PBConstr} {I : Ineq ℕ} (hc : c.Dominates I) (k : ℕ) :
    (c.mul k).Represents (k • I) := by
  refine Dominates.represents_normalize ⟨?_, ?_⟩ <;> rw [toIneq_map_mul]
  · rw [coeff_nsmul, coeff_nsmul, hc.1]
  · rw [bound_nsmul, bound_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hc.2 (Int.natCast_nonneg k)

/-- The literal axiom `ℓ ≥ 0` is the cutting planes axiom of `ℓ`. -/
theorem toIneq_litAxiom (l : Literal ℕ) : (litAxiom l).toIneq = l.toIneq := by
  ext <;> simp [PBConstr.toIneq, litAxiom, termIneq]

theorem represents_litAxiom (l : Literal ℕ) : (litAxiom l).Represents l.toIneq :=
  ⟨toIneq_litAxiom l ▸ dominates_toIneq _, by simp [litAxiom]⟩

private theorem dvd_of_dvd_termCoeff {k : ℕ} {t : ℕ × Literal ℕ} (h : (k : ℤ) ∣ termCoeff t) :
    k ∣ t.1 := by
  unfold termCoeff at h
  split at h
  · exact Int.natCast_dvd_natCast.1 h
  · exact Int.natCast_dvd_natCast.1 (dvd_neg.1 h)

/-- Terms whose coefficients are all `0` have no coefficients, no negative mass and no
coefficient sum. -/
private theorem cf_eq_zero_of_forall {ts : List (ℕ × Literal ℕ)} (h : ∀ t ∈ ts, t.1 = 0) :
    cf ts = 0 ∧ negSum ts = 0 ∧ coeffSum ts = 0 := by
  induction ts with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    obtain rfl : a = 0 := h (a, v, b) List.mem_cons_self
    obtain ⟨hcf, hns, hcs⟩ := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    cases b <;> simp [cf_cons, negSum_cons, coeffSum_cons, termCoeff, hcf, hns, hcs]

/-- With `k` dividing `a`, rounding `a / k` up is exact. -/
private theorem mul_ceilDiv_of_dvd {a k : ℕ} (hk : 0 < k) (h : k ∣ a) : k * ceilDiv a k = a := by
  obtain ⟨q, rfl⟩ := h
  have hlt : k * ceilDiv (k * q) k < k * (q + 1) := by
    simpa [Nat.mul_succ] using VeriPB.mul_ceilDiv_lt (k * q) hk
  rw [le_antisymm (Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left hlt))
    (Nat.le_of_mul_le_mul_left (le_mul_ceilDiv (k * q) hk) hk)]

/-- **Division** of a constraint dominating `I` by `k` dividing every coefficient of `I`
represents the exact division `I.div k`. -/
theorem Dominates.represents_div {c : PBConstr} {I : Ineq ℕ} (hc : c.Dominates I) {k : ℕ}
    (hk : 0 < k) (hdvd : ∀ v, (k : ℤ) ∣ I.coeff v) : (c.div k).Represents (I.div k) := by
  have hn := hc.normalize
  have hnd := nodup_termVar_normalize c
  simp only [PBConstr.div]
  generalize c.normalize = c' at hn hnd ⊢
  obtain ⟨ts, d⟩ := c'
  simp only at hnd ⊢
  refine Dominates.represents_normalize ?_
  -- Every coefficient is a multiple of `k`, so rounding adds nothing.
  have hts : ∀ t ∈ ts, k ∣ t.1 := fun t ht => dvd_of_dvd_termCoeff (by
    rw [← cf_apply_of_nodup hnd ht]
    have := congrArg (· (termVar t)) hn.1
    simp only [toIneq_eq] at this
    exact this ▸ hdvd _)
  obtain ⟨hE, hEn, -⟩ := cf_eq_zero_of_forall
    (ts := ts.map fun t => (k * ceilDiv t.1 k - t.1, t.2))
    (List.forall_mem_map.2 fun t ht => by simp [mul_ceilDiv_of_dvd hk (hts t ht)])
  have hcf := VeriPB.cf_add_cf_round k hk ts
  have hns := VeriPB.negSum_add_negSum_round k hk ts
  rw [hE, add_zero] at hcf
  rw [hEn, add_zero] at hns
  set u := ts.map fun t => (ceilDiv t.1 k, t.2)
  have hcoeff : (⟨ts, d⟩ : PBConstr).toIneq.coeff =
      (k : ℤ) • (⟨u, ceilDiv d k⟩ : PBConstr).toIneq.coeff := by
    simp only [toIneq_eq, hcf]
  have hdiv : (⟨ts, d⟩ : PBConstr).toIneq.div k = (⟨u, ceilDiv d k⟩ : PBConstr).toIneq := by
    have h1 : (d : ℤ) ≤ k * ceilDiv d k := by exact_mod_cast le_mul_ceilDiv d hk
    have h2 : (k : ℤ) * ceilDiv d k < d + k := by exact_mod_cast VeriPB.mul_ceilDiv_lt d hk
    have h3 : (negSum ts : ℤ) = k * negSum u := by exact_mod_cast hns
    refine Ineq.div_eq_of hk hcoeff ?_ ?_ <;>
      (simp only [toIneq_eq]; rw [h3]; simp only [mul_sub, mul_one]; linarith)
  rw [Dominates, ← hdiv]
  refine ⟨Finsupp.ext fun v => by simp only [coeff_div, hn.1], ?_⟩
  simp only [bound_div, neg_le_neg_iff]
  exact Int.ediv_le_ediv (mod_cast hk) (neg_le_neg hn.2)

/-- A constraint representing `0 ≥ 1` is a contradiction. -/
theorem Represents.isContradiction {c : PBConstr} (h : c.Represents contra) :
    c.IsContradiction := by
  have hcf : cf c.terms = 0 := by simpa only [toIneq_eq, coeff_contra] using h.1.1
  have hz : ∀ t ∈ c.terms, t.1 = 0 := fun t ht => by
    have := cf_apply_of_nodup h.2 ht
    rw [hcf, Finsupp.zero_apply] at this
    unfold termCoeff at this
    split at this <;> omega
  obtain ⟨-, hns, hcs⟩ := cf_eq_zero_of_forall hz
  have hb := h.1.2
  simp only [toIneq_eq, bound_contra, hns, Nat.cast_zero, sub_zero] at hb
  unfold IsContradiction
  omega

end PBConstr

namespace VeriPB

/-! ### Compiling lines -/

/-- A line of a cutting planes proof with its rule, its premises named by their positions in the
proof: position `0` is the first line. -/
inductive CPLine where
  /-- The constraint with this number in the database. -/
  | hyp (i : ℕ)
  /-- The axiom `xᵥ ≥ 0`. -/
  | nonneg (v : ℕ)
  /-- The axiom `-xᵥ ≥ -1`. -/
  | leOne (v : ℕ)
  /-- The sum of the lines at positions `p` and `q`. -/
  | add (p q : ℕ)
  /-- The line at position `p` multiplied by `k`. -/
  | smul (k p : ℕ)
  /-- The line at position `p` divided by `k`. -/
  | div (k p : ℕ)
  deriving DecidableEq, Repr

/-- The `pol` step of a line, when the line at position `p` has the number `n + p`. -/
@[expose] def CPLine.toStep (n : ℕ) : CPLine → Step
  | .hyp i => .pol [.id i, .mul 1]
  | .nonneg v => .pol [.lit (v, true)]
  | .leOne v => .pol [.lit (v, false)]
  | .add p q => .pol [.id (n + p), .id (n + q), .add]
  | .smul k p => .pol [.id (n + p), .mul k]
  | .div k p => .pol [.id (n + p), .div k]

/-- A compiled line is a `pol` step of at most three operations, without saturation. -/
theorem CPLine.exists_toStep_eq_pol (n : ℕ) (l : CPLine) :
    ∃ ops, l.toStep n = .pol ops ∧ ops.length ≤ 3 ∧ ops.all PolOp.IsCP := by
  cases l <;> exact ⟨_, rfl, by simp, rfl⟩

theorem CPLine.isCP_toStep (n : ℕ) (l : CPLine) : (l.toStep n).IsCP := by
  cases l <;> rfl

theorem runSteps_append (db : List (ℕ × PBConstr)) (n : ℕ) (ss ss' : List Step) :
    runSteps db n (ss ++ ss') = (runSteps db n ss).bind fun p => runSteps p.1 p.2 ss' := by
  induction ss generalizing db n with
  | nil => simp [runSteps]
  | cons s ss ih =>
    rcases h : runStep db n s with _ | ⟨db', n'⟩ <;> simp [runSteps, h, ih]

/-- Constraints numbered outside a prefix are looked up past it. -/
theorem lookup_append_of_notMem {E db : List (ℕ × PBConstr)} {i : ℕ} (h : i ∉ E.map (·.1)) :
    lookup (E ++ db) i = lookup db i := by
  unfold lookup
  rw [List.find?_append, List.find?_eq_none.2 fun e he => by
    simpa using fun hi => h (List.mem_map.2 ⟨e, he, hi⟩)]
  rfl

/-- With distinct numbers, a constraint of the database is found by its number. -/
theorem IdOk.lookup_eq {db : List (ℕ × PBConstr)} {n : ℕ} (hid : IdOk db n) {i : ℕ}
    {c : PBConstr} (hc : (i, c) ∈ db) : lookup db i = some c := by
  obtain ⟨⟨j, c'⟩, he⟩ := Option.isSome_iff_exists.1
    (List.find?_isSome.2 ⟨(i, c), hc, by simp⟩ : (db.find? (·.1 == i)).isSome)
  obtain rfl : j = i := by simpa using List.find?_some he
  simpa only [lookup, he, Option.map_some, Option.some.injEq] using
    hid.eq_of_mem (List.mem_of_find?_eq_some he) hc

/-! ### Compiling proofs -/

/-- The state after compiling the lines `ls` of a proof, listed last first and numbered from `n`:
the steps of the lines `ann` run from the database `db`, add the constraints `E` numbered
`n, …, n + #ls - 1`, and the line at position `p` from the first, `ls.reverse[p]`, is represented
by the constraint numbered `n + p`. -/
private def Compiled (db : List (ℕ × PBConstr)) (n : ℕ) (ls : List (Ineq ℕ)) : Prop :=
  ∃ (ann : List CPLine) (E : List (ℕ × PBConstr)), ann.length = ls.length ∧
    runSteps db n (ann.map (CPLine.toStep n)) = some (E ++ db, n + ls.length) ∧
    E.map (·.1) = (List.range' n ls.length).reverse ∧
    ∀ p I, ls.reverse[p]? = some I → ∃ c, lookup (E ++ db) (n + p) = some c ∧ c.Represents I

/-- A line of a compiled proof is represented by the constraint of its position. -/
private theorem exists_lookup_of_mem {db E : List (ℕ × PBConstr)} {n : ℕ} {ls : List (Ineq ℕ)}
    (hls : ∀ p I, ls.reverse[p]? = some I →
      ∃ c, lookup (E ++ db) (n + p) = some c ∧ c.Represents I)
    {I : Ineq ℕ} (hI : I ∈ ls) : ∃ p c, lookup (E ++ db) (n + p) = some c ∧ c.Represents I :=
  let ⟨p, hp⟩ := List.mem_iff_getElem?.1 (List.mem_reverse.2 hI)
  ⟨p, hls p I hp⟩

/-- One more line: its compiled step leaves a constraint representing it. -/
private theorem Compiled.cons {db : List (ℕ × PBConstr)} {n : ℕ} {ls : List (Ineq ℕ)}
    {I : Ineq ℕ} (ann : List CPLine) (E : List (ℕ × PBConstr)) (hlen : ann.length = ls.length)
    (hrun : runSteps db n (ann.map (CPLine.toStep n)) = some (E ++ db, n + ls.length))
    (hE : E.map (·.1) = (List.range' n ls.length).reverse)
    (hls : ∀ p I, ls.reverse[p]? = some I →
      ∃ c, lookup (E ++ db) (n + p) = some c ∧ c.Represents I)
    (l : CPLine) (ops : List PolOp) (hl : l.toStep n = .pol ops) (c : PBConstr)
    (hpol : polEval (E ++ db) ops [] = some [c]) (hc : c.Represents I) :
    Compiled db n (I :: ls) := by
  refine ⟨ann ++ [l], (n + ls.length, c) :: E, by simp [hlen], ?_, ?_, ?_⟩
  · rw [List.map_append, runSteps_append, hrun]
    simp [runSteps, hl, runStep, hpol, Nat.add_assoc]
  · simp [hE, List.range'_concat]
  · intro p J hJ
    rw [List.reverse_cons] at hJ
    rcases lt_trichotomy p ls.length with hp | rfl | hp
    · rw [List.getElem?_append_left (by simpa using hp)] at hJ
      obtain ⟨c', hc', hJ⟩ := hls p J hJ
      exact ⟨c', by simp [lookup_cons, hp.ne', hc'], hJ⟩
    · obtain rfl : I = J := by simpa [List.getElem?_append_right] using hJ
      exact ⟨c, by simp [lookup_cons], hc⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hJ
      cases hJ

/-- **Cutting planes proofs compile into `pol` steps.** Let `db` be a database whose numbers are
below `n`, and `Γ` a set of inequalities each dominated by a constraint of `db`
(`Cslib.Logic.PL.PBConstr.Dominates`). A cutting planes proof `ls` from `Γ` compiles into one `pol`
step per line (`Cslib.Logic.PL.VeriPB.CPLine.toStep`). Run from `db` and `n`, the steps add one
constraint per line, numbered `n, n + 1, …`, and the line at position `p`, counted from the first
line, is represented by the constraint numbered `n + p` (`Cslib.Logic.PL.PBConstr.Represents`).
As `ls` lists the lines last first, that line is `ls.reverse[p]`. -/
theorem exists_runSteps_of_isProof {Γ : Set (Ineq ℕ)} {db : List (ℕ × PBConstr)} {n : ℕ}
    (hn : ∀ e ∈ db, e.1 < n) (hΓ : ∀ I ∈ Γ, ∃ i c, lookup db i = some c ∧ c.Dominates I)
    {ls : List (Ineq ℕ)} (h : IsProof Γ ls) :
    ∃ (ann : List CPLine) (E : List (ℕ × PBConstr)), ann.length = ls.length ∧
      runSteps db n (ann.map (CPLine.toStep n)) = some (E ++ db, n + ls.length) ∧
      E.map (·.1) = (List.range' n ls.length).reverse ∧
      ∀ p I, ls.reverse[p]? = some I →
        ∃ c, lookup (E ++ db) (n + p) = some c ∧ c.Represents I := by
  change Compiled db n ls
  induction h with
  | nil => exact ⟨[], [], rfl, by simp [runSteps], rfl, by simp⟩
  | @hyp ls I _ hI ih =>
    obtain ⟨ann, E, hlen, hrun, hE, hls⟩ := ih
    obtain ⟨i, c, hc, hcI⟩ := hΓ I hI
    have hi : lookup (E ++ db) i = some c := by
      rw [lookup_append_of_notMem, hc]
      obtain ⟨e, he, rfl⟩ := (isSome_lookup_iff db i).1 (by simp [hc])
      have := hn e he
      rw [hE, List.mem_reverse, List.mem_range'_1]
      omega
    exact Compiled.cons ann E hlen hrun hE hls (.hyp i) _ rfl _
      (by simp only [polEval, hi, Option.bind_some]) (one_smul ℕ I ▸ hcI.represents_mul 1)
  | @nonneg ls _ v ih =>
    obtain ⟨ann, E, hlen, hrun, hE, hls⟩ := ih
    exact Compiled.cons ann E hlen hrun hE hls (.nonneg v) _ rfl _ rfl
      (represents_litAxiom (v, true))
  | @leOne ls _ v ih =>
    obtain ⟨ann, E, hlen, hrun, hE, hls⟩ := ih
    exact Compiled.cons ann E hlen hrun hE hls (.leOne v) _ rfl _ rfl
      (represents_litAxiom (v, false))
  | @add ls I J _ hI hJ ih =>
    obtain ⟨ann, E, hlen, hrun, hE, hls⟩ := ih
    obtain ⟨p, c, hc, hcI⟩ := exists_lookup_of_mem hls hI
    obtain ⟨q, d, hd, hdJ⟩ := exists_lookup_of_mem hls hJ
    exact Compiled.cons ann E hlen hrun hE hls (.add p q) _ rfl _
      (by simp only [polEval, hc, hd, Option.bind_some]) (hcI.1.represents_add hdJ.1)
  | @smul ls I _ k hk hI ih =>
    obtain ⟨ann, E, hlen, hrun, hE, hls⟩ := ih
    obtain ⟨p, c, hc, hcI⟩ := exists_lookup_of_mem hls hI
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact Compiled.cons ann E hlen hrun hE hls (.smul (k + 1) p) _ rfl _
      (by simp only [polEval, hc, Option.bind_some]) (hcI.1.represents_mul (k + 1))
  | @div ls I _ k hk hdvd hI ih =>
    obtain ⟨ann, E, hlen, hrun, hE, hls⟩ := ih
    obtain ⟨p, c, hc, hcI⟩ := exists_lookup_of_mem hls hI
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact Compiled.cons ann E hlen hrun hE hls (.div (k' + 1) p) _ rfl _
      (by simp only [polEval, hc, Option.bind_some]) (hcI.1.represents_div hk hdvd)

/-- **At most three operations per line**: the compiled steps of `ann` have at most
`3 |ann|` operations. -/
theorem opCount_map_toStep_le (n : ℕ) :
    ∀ ann : List CPLine, opCount (ann.map (CPLine.toStep n)) ≤ 3 * ann.length
  | [] => by simp
  | l :: ann => by
    obtain ⟨ops, hops, hlen, -⟩ := l.exists_toStep_eq_pol n
    have := opCount_map_toStep_le n ann
    simp only [List.map_cons, opCount_cons, hops, Step.opCount, List.length_cons]
    omega

/-! ### Refutations -/

/-- **Cutting planes refutations compile into checked VeriPB proofs.** A cutting planes refutation
of the inequalities of the constraints `F` with at most `s` lines gives a proof that the checker
accepts on `F`, with at most `s` steps and `3 s` operations, each step the `pol` step of a line
(`Cslib.Logic.PL.VeriPB.CPLine.toStep`): at most three operations, without saturation. -/
theorem exists_check_of_refutableInSize {F : List PBConstr} {s : ℕ}
    (h : RefutableInSize {I | ∃ c ∈ F, c.toIneq = I} s) :
    ∃ P : Proof, check F P = true ∧ P.steps.length ≤ s ∧ opCount P.steps ≤ 3 * s ∧
      P.steps.all Step.IsCP ∧
      ∃ ann : List CPLine, P.steps = ann.map (CPLine.toStep (F.length + 1)) := by
  obtain ⟨ls, hls, hcontra, hlen⟩ := h
  have hid := idOk_initDb F
  obtain ⟨ann, E, hann, hrun, -, hrep⟩ := exists_runSteps_of_isProof hid.lt (fun I hI => by
    obtain ⟨c, hc, rfl⟩ := hI
    obtain ⟨⟨c', j⟩, hj, rfl⟩ :=
      List.mem_map.1 (by rwa [List.zipIdx_map_fst] : c ∈ F.zipIdx.map (·.1))
    exact ⟨j + 1, c'.normalize,
      hid.lookup_eq (List.mem_map_of_mem (f := fun e => (e.2 + 1, e.1.normalize)) hj),
      (dominates_toIneq c').normalize⟩) hls
  obtain ⟨p, c, hc, hcI⟩ := exists_lookup_of_mem hrep hcontra
  have hops := opCount_map_toStep_le (F.length + 1) ann
  refine ⟨⟨ann.map (CPLine.toStep (F.length + 1)), F.length + 1 + p⟩, ?_,
    by simpa [hann] using hlen, (by dsimp only; omega), by simp [CPLine.isCP_toStep], ann, rfl⟩
  simp only [check, hrun, namesContra, hc, Option.any_some, decide_eq_true_eq]
  exact hcI.isContradiction

/-- **Cutting planes refutations of CNFs compile into checked VeriPB proofs**: a cutting planes
refutation of `φ.toIneqs` with at most `s` lines gives a proof that the checker accepts on the
clauses of `φ`, with at most `s` steps and `3 s` operations, each step the `pol` step of a line. -/
theorem exists_check_cnf_of_refutableInSize {φ : CNF ℕ} {s : ℕ}
    (h : RefutableInSize φ.toIneqs s) :
    ∃ P : Proof, check (φ.map Clause.toPB) P = true ∧ P.steps.length ≤ s ∧
      opCount P.steps ≤ 3 * s ∧ P.steps.all Step.IsCP ∧
      ∃ ann : List CPLine, P.steps = ann.map (CPLine.toStep ((φ.map Clause.toPB).length + 1)) :=
  exists_check_of_refutableInSize (CNF.toIneqs_eq_toPB φ ▸ h)

/-- **The `pol` fragment of VeriPB without saturation and cutting planes refute the same sets.** The
constraints `F` have a checked proof of `UNSAT` made of `pol` steps without saturation and of
deletions iff the inequalities of `F` have a cutting planes refutation. A refutation with `s` lines
gives a proof with at most `s` steps and `3 s` operations
(`Cslib.Logic.PL.VeriPB.exists_check_of_refutableInSize`). Conversely, a proof with `m` operations
on constraints `F` over the variables `S` gives a refutation with at most
`16 (|S| + 1) (|F| + m + 1)` lines (`Cslib.Logic.PL.VeriPB.refutableInSize_of_check`). -/
theorem exists_check_iff_exists_refutableInSize {F : List PBConstr} :
    (∃ P : Proof, check F P = true ∧ P.steps.all Step.IsCP) ↔
      ∃ s, RefutableInSize {I | ∃ c ∈ F, c.toIneq = I} s :=
  ⟨fun ⟨_, h, hP⟩ => exists_isProof_contra_of_check h hP, fun ⟨_, h⟩ =>
    let ⟨P, hP, _, _, hcp, _⟩ := exists_check_of_refutableInSize h
    ⟨P, hP, hcp⟩⟩

/-- **The same for CNFs**: the clauses of `φ` have a checked proof of `UNSAT` made of `pol` steps
without saturation and of deletions iff their cutting planes inequalities `φ.toIneqs` have a
cutting planes refutation. -/
theorem exists_check_cnf_iff_exists_refutableInSize {φ : CNF ℕ} :
    (∃ P : Proof, check (φ.map Clause.toPB) P = true ∧ P.steps.all Step.IsCP) ↔
      ∃ s, RefutableInSize φ.toIneqs s := by
  rw [exists_check_iff_exists_refutableInSize, CNF.toIneqs_eq_toPB]

end VeriPB

end Cslib.Logic.PL
