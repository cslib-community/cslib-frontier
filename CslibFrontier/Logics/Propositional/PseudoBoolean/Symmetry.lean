/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
-- `import all`: the acceptance proofs unfold `stepTop`, `domCheck`, `Order.defCheck` and the
-- private subproof runner and order lemmas of the checker.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast

/-!
# Certified symmetry breaking by dominance

The main application of dominance-based strengthening in VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023] is symmetry breaking: for a symmetry `π` of a
formula `F`, the *lex-leader constraint* `z ⪯_lex z↾π` over a list `z` of variables can be added
without losing a solution (§4.1 of arXiv:2203.12275v3, eq. (20), the constraint `C_LL`), and the
`dom` rule (§3.6, Definition 13, conditions (10a) and (10b); Proposition 14 shows that it keeps
a configuration valid) certifies the addition against the lexicographic order. This file builds
that proof, for every `z` and every list of symmetries, and proves that the checker
`Cslib.Logic.PL.VeriPB.checkRed` accepts it.
Locators are to arXiv:2203.12275v3, the full version of the JAIR article.

**The order** (`Cslib.Logic.PL.VeriPB.lexOrder`). The lexicographic order on `n` bits is the
single constraint `∑ᵢ 2^{n-i} (vᵢ - uᵢ) ≥ 0` (`Cslib.Logic.PL.VeriPB.lexConstr`; §3.7, eq. (14)),
without auxiliary variables. Its coefficients are exponential in `n`, which §4.3 discusses; the
checker's arithmetic is exact, and the kernel cost of the checks below grows with the size of
these numbers. Its transitivity proof sums the two premises and the negated goal; its reflexivity
proof observes that the negated goal is a contradiction. `def_order` accepts both for every `n`
(`Cslib.Logic.PL.VeriPB.defCheck_lexOrder`), and the order is `≤` on lists of bits, compared
lexicographically (`Cslib.Logic.PL.VeriPB.lexOrder_le_iff`). The proof works with the slack
`∑ aᵢ ℓᵢ - d` of a constraint (`Cslib.Logic.PL.PBConstr.slack`): a sum of constraints whose
slacks add up to a negative number at every assignment is a contradiction after normalization
(`Cslib.Logic.PL.PBConstr.isContradiction_add`).

**The lex-leader step** (`Cslib.Logic.PL.VeriPB.lexLeaderStep`). A symmetry is a map `π` of
variables to literals (`Cslib.Logic.PL.VeriPB.Witness.ofLits`), and the constraint added is
`z ⪯_lex z↾π` (`Cslib.Logic.PL.VeriPB.lexLeader`), with the order loaded over `z`. The
subproof refutes the two order goals by one addition each, and the core goals `D|π` are found in
the database. So the step is accepted when `π` maps every core constraint to one of the
database, does not raise the objective, and leaves the preserved variables alone
(`Cslib.Logic.PL.VeriPB.domCheck_lexLeader`). Nothing requires `π` to be a permutation: a map
sending the formula into itself (`Cslib.Logic.PL.VeriPB.MapsInto`) suffices. The steps for
several symmetries `π₁, …, πₖ` under one order are each checked against the database so far,
which still contains the core (`Cslib.Logic.PL.VeriPB.runTop_lexLeaderSteps`); §4.1 notes that
the constraints of several symmetries under the same order "will not interfere". The whole prefix
`def_order`, `load_order`, `dom`, … is accepted from the input formula
(`Cslib.Logic.PL.VeriPB.runTop_symmetryBreaking`).

**The optimum** (`Cslib.Logic.PL.VeriPB.exists_lexLeader_le`). For symmetries that do not raise
the objective, every solution of `F` gives a solution of `F` and of all the lex-leader
constraints of no larger objective value. It is proved through the checker's invariants for the
accepted prefix, which rest on `Cslib.Logic.PL.VeriPB.SatObjPo.dom`. The paper's proof system
keeps an optimal solution (§3, opening; §3.9) and §4 applies it to symmetries of decision
problems; we found no sentence stating this consequence for symmetric objectives (§6.4 notes
that the objective of max clique is unchanged by a vertex swap, so that `f↾ω ≤ f` is trivial),
and the theorem here proves it.

## Main definitions

* `Cslib.Logic.PL.VeriPB.lexOrder`, `Cslib.Logic.PL.VeriPB.lexTransProof`,
  `Cslib.Logic.PL.VeriPB.lexReflProof`: the lexicographic order and its proofs.
* `Cslib.Logic.PL.VeriPB.lexLeader`, `Cslib.Logic.PL.VeriPB.lexLeaderStep`,
  `Cslib.Logic.PL.VeriPB.symmetryBreaking`: the lex-leader constraint, its `dom` step, and the
  proof prefix breaking a list of symmetries.

## Main results

* `Cslib.Logic.PL.VeriPB.defCheck_lexOrder`, `Cslib.Logic.PL.VeriPB.lexOrder_le_iff`.
* `Cslib.Logic.PL.VeriPB.domCheck_lexLeader`, `Cslib.Logic.PL.VeriPB.runTop_lexLeaderSteps`,
  `Cslib.Logic.PL.VeriPB.runTop_symmetryBreaking`: acceptance.
* `Cslib.Logic.PL.VeriPB.exists_lexLeader_le`: the optimum is preserved.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Sat (Literal)

namespace PBConstr

/-! ### Slack -/

/-- The slack `∑ aᵢ ℓᵢ - d` of a constraint at an assignment: the constraint holds exactly where
its slack is nonnegative (`Cslib.Logic.PL.PBConstr.holds_iff_slack`). -/
def slack (c : PBConstr) (σ : ℕ → Bool) : ℤ := (lhs σ c.terms : ℤ) - c.degree

theorem holds_iff_slack {c : PBConstr} {σ : ℕ → Bool} : c.Holds σ ↔ 0 ≤ c.slack σ := by
  unfold Holds slack; omega

/-- The slack of the sum of two constraints, before normalization. -/
theorem slack_append (c d : PBConstr) (σ : ℕ → Bool) :
    slack ⟨c.terms ++ d.terms, c.degree + d.degree⟩ σ = c.slack σ + d.slack σ := by
  simp only [slack, lhs_append]; push_cast; ring

/-- **Normalization can only lower the slack**: it clamps the degree at `0`, raising it. -/
theorem slack_normalize_le (c : PBConstr) (σ : ℕ → Bool) : c.normalize.slack σ ≤ c.slack σ := by
  have h1 := lhs_fromLinear σ (toLinear c.terms) ((c.degree : ℤ) - negSum c.terms)
  have h2 := lhs_eq_linVal σ c.terms
  simp only [slack, normalize, fromLinear] at h1 ⊢
  omega

/-- **Normalization keeps the slack** of a constraint that some assignment gives a nonpositive
slack: the degree is then not clamped. -/
theorem slack_normalize_of_exists {c : PBConstr} (h : ∃ τ, c.slack τ ≤ 0) (σ : ℕ → Bool) :
    c.normalize.slack σ = c.slack σ := by
  obtain ⟨τ, hτ⟩ := h
  have h1 := lhs_fromLinear σ (toLinear c.terms) ((c.degree : ℤ) - negSum c.terms)
  have h2 := lhs_eq_linVal σ c.terms
  have h3 := lhs_eq_linVal τ c.terms
  have h4 := lhs_fromLinear τ (toLinear c.terms) ((c.degree : ℤ) - negSum c.terms)
  have h5 := neg_negMass_le_linVal τ (toLinear c.terms)
  simp only [slack, normalize, fromLinear] at h1 h4 hτ ⊢
  omega

/-- The slack of a sum, normalized, is at most the sum of the slacks. -/
theorem slack_add_le (c d : PBConstr) (σ : ℕ → Bool) :
    (c.add d).slack σ ≤ c.slack σ + d.slack σ :=
  (slack_normalize_le _ σ).trans (slack_append c d σ).le

private theorem lhs_add_lhs_negate (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    lhs σ ts + lhs σ (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) = coeffSum ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a, l⟩ := t
    simp only [List.map_cons, lhs_cons, coeffSum_cons]
    have := termVal_add_negate σ a l
    omega

/-- **The slack of a negation** is at most minus one minus the slack of the normal form. -/
theorem slack_negate_le (c : PBConstr) (σ : ℕ → Bool) :
    c.negate.slack σ ≤ -c.normalize.slack σ - 1 := by
  have := lhs_add_lhs_negate σ c.normalize.terms
  simp only [slack, negate]
  omega

/-- An assignment giving every literal of `ts` the value `b`, for terms on distinct variables. -/
private def allTrue (ts : List (ℕ × Literal ℕ)) (b : Bool) (v : ℕ) : Bool :=
  ((ts.find? (termVar · == v)).map fun t => termPos t == b).getD false

private theorem find?_eq_of_nodup {ts : List (ℕ × Literal ℕ)} (h : (ts.map termVar).Nodup)
    {t : ℕ × Literal ℕ} (ht : t ∈ ts) : ts.find? (termVar · == termVar t) = some t := by
  induction ts with
  | nil => cases ht
  | cons t' ts ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ht with rfl | ht
    · simp
    · have hne : termVar t' ≠ termVar t := fun he => h.1 (he ▸ List.mem_map_of_mem ht)
      simp [hne, ih h.2 ht]

private theorem eval_allTrue {ts : List (ℕ × Literal ℕ)} (h : (ts.map termVar).Nodup) (b : Bool)
    {t : ℕ × Literal ℕ} (ht : t ∈ ts) : Literal.eval (allTrue ts b) t.2 = b := by
  have := find?_eq_of_nodup h ht
  obtain ⟨a, v, p⟩ := t
  simp only [termVar_mk] at this
  simp only [Literal.eval, allTrue, this, Option.map_some, Option.getD_some, termPos_mk]
  cases p <;> cases b <;> rfl

private theorem lhs_allTrue {ts : List (ℕ × Literal ℕ)} (h : (ts.map termVar).Nodup) (b : Bool) :
    lhs (allTrue ts b) ts = if b then coeffSum ts else 0 := by
  have : ∀ us : List (ℕ × Literal ℕ), (∀ t ∈ us, t ∈ ts) →
      lhs (allTrue ts b) us = if b then coeffSum us else 0 := by
    intro us hus
    induction us with
    | nil => cases b <;> rfl
    | cons t us ih =>
      rw [lhs_cons, ih fun t' h' => hus t' (List.mem_cons_of_mem _ h'), termVal,
        eval_allTrue h b (hus t List.mem_cons_self)]
      cases b <;> simp
  exact this ts fun _ h => h

/-- **A normalized constraint with negative slack everywhere is a contradiction**: making every
literal true gives the sum of the coefficients. -/
theorem isContradiction_normalize {c : PBConstr} (h : ∀ σ, c.slack σ < 0) :
    c.normalize.IsContradiction := by
  have hd := nodup_termVar_normalize c
  have h1 := (slack_normalize_le c (allTrue c.normalize.terms true)).trans_lt (h _)
  simp only [slack, lhs_allTrue hd, ite_true] at h1
  unfold IsContradiction
  omega

/-- **A normalized constraint that every assignment satisfies has degree `0`**: making every
literal false gives the left-hand side `0`. -/
theorem normalize_degree_eq_zero {c : PBConstr} (h : ∀ σ, c.Holds σ) : c.normalize.degree = 0 := by
  have := (holds_normalize _ c).2 (h (allTrue c.normalize.terms false))
  rw [Holds, lhs_allTrue (nodup_termVar_normalize c)] at this
  simpa using this

/-- **A sum is a contradiction** when the slacks of the summands add up to a negative number
everywhere. -/
theorem isContradiction_add {c d : PBConstr} (h : ∀ σ, c.slack σ + d.slack σ < 0) :
    (c.add d).IsContradiction :=
  isContradiction_normalize fun σ => by rw [slack_append]; exact h σ

/-- **The negation of a constraint that every assignment satisfies is a contradiction.** -/
theorem isContradiction_negate {c : PBConstr} (h : ∀ σ, c.Holds σ) : c.negate.IsContradiction := by
  have h0 := normalize_degree_eq_zero h
  have : coeffSum (c.normalize.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2)) =
      coeffSum c.normalize.terms := by
    simp [coeffSum, Function.comp_def]
  simp only [IsContradiction, negate, this, h0]
  omega

end PBConstr

namespace VeriPB

open PBConstr

/-! ### Binary values -/

/-- The value of a list of bits read as a binary number, the first bit most significant. -/
def binVal : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 ^ bs.length * b.toNat + binVal bs

theorem binVal_lt (bs : List Bool) : binVal bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [binVal]
  | cons b bs ih =>
    simp only [binVal, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- **Binary values order lists of bits of the same length lexicographically**, `false` before
`true`. -/
theorem binVal_lt_binVal_iff {x y : List Bool} (h : x.length = y.length) :
    binVal x < binVal y ↔ x < y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [binVal]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have hx := binVal_lt x
      have hy := binVal_lt y
      simp only [binVal, List.cons_lt_cons_iff, h] at hx ⊢
      generalize 2 ^ y.length = p at *
      have hft : false < true := by decide
      have htf : ¬ true < false := by decide
      cases a <;> cases b <;> simp [ih h, hft, htf] <;> omega

theorem binVal_le_binVal_iff {x y : List Bool} (h : x.length = y.length) :
    binVal x ≤ binVal y ↔ x ≤ y := by
  rw [← not_lt, binVal_lt_binVal_iff h.symm]
  exact not_lt

/-- A list of bits all `true` has the largest binary value of its length. -/
theorem binVal_le_of_forall_true {x y : List Bool} (h : x.length = y.length)
    (hy : ∀ b ∈ y, b = true) : binVal x ≤ binVal y := by
  induction x generalizing y with
  | nil => simp [binVal]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hy
      have := ih h hy.2
      simp only [binVal, hy.1, h]
      generalize 2 ^ y.length = p
      cases a <;> simp <;> omega

/-- A list of bits all `false` has value `0`. -/
theorem binVal_eq_zero {x : List Bool} (h : ∀ b ∈ x, b = false) : binVal x = 0 := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [binVal, h.1, ih h.2]

/-! ### The lexicographic constraint -/

/-- The terms `2^{n-i} ¬aᵢ + 2^{n-i} bᵢ` of `Cslib.Logic.PL.VeriPB.lexConstr`, for `i` from `1`
to `n`. -/
def lexTerms : List (Literal ℕ) → List (Literal ℕ) → List (ℕ × Literal ℕ)
  | a :: as, b :: bs =>
    (2 ^ as.length, Std.Sat.Literal.negate a) :: (2 ^ as.length, b) :: lexTerms as bs
  | _, _ => []

/-- **The lexicographic constraint** `a ⪯_lex b` on literals `a₁ … aₙ` and `b₁ … bₙ`, the single
constraint `∑ᵢ 2^{n-i} (bᵢ - aᵢ) ≥ 0` of eq. (14) of Bogaerts, Gocht, McCreesh and Nordström,
written with the negated literals `¬aᵢ = 1 - aᵢ` as `∑ᵢ 2^{n-i} ¬aᵢ + 2^{n-i} bᵢ ≥ 2ⁿ - 1`. -/
def lexConstr (as bs : List (Literal ℕ)) : PBConstr := ⟨lexTerms as bs, 2 ^ as.length - 1⟩

private theorem lhs_lexTerms (σ : ℕ → Bool) :
    ∀ {as bs : List (Literal ℕ)}, as.length = bs.length →
      (lhs σ (lexTerms as bs) : ℤ) + binVal (as.map (Literal.eval σ)) =
        2 ^ as.length - 1 + binVal (bs.map (Literal.eval σ))
  | [], [], _ => by simp [lexTerms, binVal]
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := lhs_lexTerms σ h
    have hna : Literal.eval σ (Std.Sat.Literal.negate a) = !Literal.eval σ a := by
      obtain ⟨v, p⟩ := a
      cases p <;> simp [Literal.eval, Std.Sat.Literal.negate]
    simp only [lexTerms, lhs_cons, List.map_cons, binVal, List.length_map, List.length_cons,
      ← h] at ih ⊢
    unfold termVal
    rw [hna, pow_succ]
    push_cast at ih ⊢
    generalize (2 : ℤ) ^ as.length = p at *
    cases Literal.eval σ a <;> cases Literal.eval σ b <;> simp <;> linarith

/-- **The slack of the lexicographic constraint** is the difference of the binary values. -/
theorem slack_lexConstr {as bs : List (Literal ℕ)} (h : as.length = bs.length) (σ : ℕ → Bool) :
    (lexConstr as bs).slack σ =
      binVal (bs.map (Literal.eval σ)) - binVal (as.map (Literal.eval σ)) := by
  have := lhs_lexTerms σ h
  have hp : 1 ≤ 2 ^ as.length := Nat.one_le_two_pow
  simp only [PBConstr.slack, lexConstr]
  rw [Nat.cast_sub hp]
  push_cast
  linarith

private theorem mem_lexTerms : ∀ {as bs : List (Literal ℕ)} {t : ℕ × Literal ℕ},
    t ∈ lexTerms as bs → termVar t ∈ as.map (·.1) ∨ termVar t ∈ bs.map (·.1)
  | a :: as, b :: bs, t, h => by
    simp only [lexTerms, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · left; obtain ⟨v, p⟩ := a; simp [Std.Sat.Literal.negate]
    · right; obtain ⟨v, p⟩ := b; simp
    · rcases mem_lexTerms h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (List.mem_cons_of_mem _ h)
  | [], _, _, h => by simp [lexTerms] at h
  | _ :: _, [], _, h => by simp [lexTerms] at h

/-! ### The lexicographic order -/

/-- The positive literals of the variables `xs`. -/
def posLits (xs : List ℕ) : List (Literal ℕ) := xs.map fun x => (x, true)

theorem map_eval_posLits (σ : ℕ → Bool) (xs : List ℕ) :
    (posLits xs).map (Literal.eval σ) = xs.map σ := by
  simp [posLits, Literal.eval, Function.comp_def]

/-- **The lexicographic order on `n` bits** as a VeriPB order (§5.3): the left variables `u` are
`0 … n-1`, the right variables `v` are `n … 2n-1`, there are no auxiliary variables and no
specification, and the definition is the single constraint `u ⪯_lex v`
(`Cslib.Logic.PL.VeriPB.lexConstr`), with coefficients up to `2^{n-1}`. It relates `x ⪯ y`
exactly when `x ≤ y` lexicographically (`Cslib.Logic.PL.VeriPB.lexOrder_le_iff`). -/
def lexOrder (n : ℕ) : Order :=
  ⟨List.range n, List.range' n n, [], [],
    [lexConstr (posLits (List.range n)) (posLits (List.range' n n))]⟩

/-- The fresh right variables `w = 2n … 3n-1` of the transitivity proof of `lexOrder n`. -/
def lexTransVars (n : ℕ) : TransVars := ⟨List.range' (2 * n) n, [], []⟩

/-- The transitivity proof of `lexOrder n`: the premises `O⪯(u, v)` and `O⪯(v, w)` are `1` and
`2`, the negated goal `#1`, `¬O⪯(u, w)`, is `3`, and the sum `1 + 2 + 3`, numbered `4`, is a
contradiction, as the slacks `v - u`, `w - v` and at most `u - w - 1` add up to at most `-1`. -/
def lexTransProof : OrderProof :=
  ⟨[.goal (.hash 1) [.pol [.id 1, .id 2, .add, .id 3, .add]] 4], none⟩

/-- The reflexivity proof of `lexOrder n`, numbered after the transitivity proof: the negated
goal `¬O⪯(u, u)`, numbered `5`, is itself a contradiction. (The checker would also accept an
empty proof, `O⪯(u, u)` being trivially true after normalization; this explicit one is what
VeriPB 3.0.2 accepts, as for the order `lex4` of the fixtures.) -/
def lexReflProof : OrderProof := ⟨[.goal (.hash 1) [] 5], none⟩

private theorem lexOrder_nodup (n : ℕ) : (lexOrder n).vars.Nodup := by
  simp only [lexOrder, Order.vars, List.append_nil]
  refine List.nodup_append.2 ⟨List.nodup_range, List.nodup_range', fun a ha b hb => ?_⟩
  simp only [List.mem_range, List.mem_range'_1] at ha hb
  omega

/-- A witness whose values are all literals moves no constant into the degree. -/
private theorem substTerm_snd {ω : Witness} (hω : ∀ e ∈ ω, ∃ l, e.2 = .lit l)
    (t : ℕ × Literal ℕ) : (Witness.substTerm ω t).2 = 0 := by
  unfold Witness.substTerm
  cases hf : ω.find (termVar t) with
  | none => rfl
  | some w =>
    simp only [Witness.find, Option.map_eq_some_iff] at hf
    obtain ⟨e, he, rfl⟩ := hf
    obtain ⟨l, hl⟩ := hω e (List.mem_of_find?_eq_some he)
    simp [hl]

/-- **The slack of a constraint under a witness of literals** is its slack at `σ ∘ ω`. -/
theorem slack_substC {ω : Witness} (hω : ∀ e ∈ ω, ∃ l, e.2 = .lit l) (c : PBConstr)
    (σ : ℕ → Bool) : (Witness.substC ω c).slack σ = c.slack (Witness.apply σ ω) := by
  have h0 : (c.terms.map fun t => (Witness.substTerm ω t).2).sum = 0 := by
    simp [substTerm_snd hω]
  have := Witness.lhs_apply σ ω c.terms
  simp only [PBConstr.slack, Witness.substC, h0, Nat.sub_zero] at this ⊢
  omega

/-- The substitution of an order's variables by literals is a witness of literals. -/
private theorem subst_lits {O : Order} {a b r : List WVal} (ha : ∀ w ∈ a, ∃ l, w = .lit l)
    (hb : ∀ w ∈ b, ∃ l, w = .lit l) (hr : ∀ w ∈ r, ∃ l, w = .lit l) :
    ∀ e ∈ O.subst a b r, ∃ l, e.2 = .lit l := by
  intro e he
  simp only [Order.subst, List.mem_append] at he
  rcases he with he | he | he
  · exact ha _ (List.of_mem_zip he).2
  · exact hb _ (List.of_mem_zip he).2
  · exact hr _ (List.of_mem_zip he).2

/-- Under the substitution of `u` by `a` and `v` by `b`, the left and the right variables take
the values of `a` and `b`. -/
private theorem map_apply_subst {O : Order} (hnd : O.vars.Nodup) {a b r : List WVal}
    (ha : a.length = O.left.length) (hb : b.length = O.right.length) (σ : ℕ → Bool) :
    O.left.map (Witness.apply σ (O.subst a b r)) = a.map (WVal.eval σ) ∧
      O.right.map (Witness.apply σ (O.subst a b r)) = b.map (WVal.eval σ) := by
  simp only [Order.vars, List.nodup_append] at hnd
  obtain ⟨⟨hl, hr, hlr⟩, -, -⟩ := hnd
  rw [Order.subst, Witness.apply_zip_append]
  refine ⟨map_assignOn hl (by simp [ha]) _, ?_⟩
  rw [map_assignOn_of_disjoint (fun j hj hjl => hlr _ hjl _ hj rfl), Witness.apply_zip_append]
  exact map_assignOn hr (by simp [hb]) _

/-- **The slack of an instantiated lexicographic order**: with `u` replaced by the literals `a`
and `v` by the literals `b`, the definition of `lexOrder n` has slack `b - a` in binary. -/
theorem slack_instC_lexOrder {n : ℕ} {a b : List WVal} (ha : a.length = n) (hb : b.length = n)
    (hal : ∀ w ∈ a, ∃ l, w = .lit l) (hbl : ∀ w ∈ b, ∃ l, w = .lit l) {G : PBConstr}
    (hG : G ∈ (lexOrder n).instC a b []) (σ : ℕ → Bool) :
    G.slack σ = binVal (b.map (WVal.eval σ)) - binVal (a.map (WVal.eval σ)) := by
  simp only [Order.instC, lexOrder, List.map_cons, List.map_nil, List.mem_singleton] at hG
  subst hG
  rw [slack_substC (subst_lits hal hbl (by simp)),
    slack_lexConstr (as := posLits (List.range n)) (bs := posLits (List.range' n n))
      (by simp [posLits]),
    map_eval_posLits, map_eval_posLits]
  obtain ⟨h1, h2⟩ := map_apply_subst (O := lexOrder n) (a := a) (b := b) (r := [])
    (lexOrder_nodup n)
    (by simp [lexOrder, ha]) (by simp [lexOrder, hb]) σ
  simp only [lexOrder] at h1 h2
  rw [h1, h2]

private theorem posVals_lits (xs : List ℕ) : ∀ w ∈ posVals xs, ∃ l, w = .lit l := by
  simp [posVals]

/-- The slack `b - a` of an instantiated lexicographic order vanishes somewhere when `a` or `b` is
a list of positive literals: at the assignment making them all true, or all false. -/
private theorem exists_slack_instC_le {n : ℕ} {a b : List WVal} (ha : a.length = n)
    (hb : b.length = n) (hal : ∀ w ∈ a, ∃ l, w = .lit l) (hbl : ∀ w ∈ b, ∃ l, w = .lit l)
    (hpos : (∀ w ∈ a, ∃ x, w = .lit (x, true)) ∨ ∀ w ∈ b, ∃ x, w = .lit (x, true))
    {G : PBConstr} (hG : G ∈ (lexOrder n).instC a b []) : ∃ τ, G.slack τ ≤ 0 := by
  rcases hpos with hpos | hpos
  · refine ⟨fun _ => true, ?_⟩
    rw [slack_instC_lexOrder ha hb hal hbl hG]
    have := binVal_le_of_forall_true (x := b.map (WVal.eval fun _ => true))
      (y := a.map (WVal.eval fun _ => true)) (by simp [ha, hb]) (by
        simp only [List.mem_map]
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨x, rfl⟩ := hpos w hw
        rfl)
    omega
  · refine ⟨fun _ => false, ?_⟩
    rw [slack_instC_lexOrder ha hb hal hbl hG, binVal_eq_zero (x := b.map _) (by
      simp only [List.mem_map]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, rfl⟩ := hpos w hw
      rfl)]
    omega

/-- **`def_order` accepts the lexicographic order** on `n` bits, for every `n`, with the
transitivity proof `Cslib.Logic.PL.VeriPB.lexTransProof` and the reflexivity proof
`Cslib.Logic.PL.VeriPB.lexReflProof`. -/
theorem defCheck_lexOrder (n : ℕ) :
    (lexOrder n).defCheck [] (lexTransVars n) lexTransProof lexReflProof = true := by
  have key : ∀ a b : List ℕ, a.length = n → b.length = n →
      ∀ G ∈ (lexOrder n).instC (posVals a) (posVals b) [], ∀ σ,
        G.slack σ = binVal (b.map σ) - binVal (a.map σ) := fun a b ha hb G hG σ => by
    rw [slack_instC_lexOrder (by simp [posVals, ha]) (by simp [posVals, hb]) (posVals_lits a)
      (posVals_lits b) hG, map_eval_posVals, map_eval_posVals]
  have kex : ∀ a b : List ℕ, a.length = n → b.length = n →
      ∀ G ∈ (lexOrder n).instC (posVals a) (posVals b) [], ∃ τ, G.slack τ ≤ 0 :=
    fun a b ha hb G hG => exists_slack_instC_le (by simp [posVals, ha]) (by simp [posVals, hb])
      (posVals_lits a) (posVals_lits b) (.inl (by simp [posVals])) hG
  obtain ⟨P₁, hP₁⟩ : ∃ G, (lexOrder n).instC (posVals (List.range n))
      (posVals (List.range' n n)) [] = [G] := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ G, (lexOrder n).instC (posVals (List.range' n n))
      (posVals (List.range' (2 * n) n)) [] = [G] := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, (lexOrder n).instC (posVals (List.range n))
      (posVals (List.range' (2 * n) n)) [] = [G] := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ G, (lexOrder n).instC (posVals (List.range n))
      (posVals (List.range n)) [] = [G] := ⟨_, rfl⟩
  have mem : ∀ {l : List PBConstr} {G : PBConstr}, l = [G] → G ∈ l := fun h => h ▸ by simp
  have hlr : (List.range n).length = n := by simp
  have hlr' : ∀ m, (List.range' m n).length = n := by simp
  have ht : ((P₁.normalize.add P₂.normalize).add G.negate).IsContradiction := by
    refine isContradiction_add fun σ => ?_
    have := slack_add_le P₁.normalize P₂.normalize σ
    have := slack_normalize_le P₁ σ
    have := slack_normalize_le P₂ σ
    have := slack_negate_le G σ
    rw [slack_normalize_of_exists (kex _ _ hlr (hlr' _) G (mem hG))] at this
    rw [key _ _ hlr (hlr' _) P₁ (mem hP₁), key _ _ (hlr' _) (hlr' _) P₂ (mem hP₂),
      key _ _ hlr (hlr' _) G (mem hG)] at *
    omega
  have hr : R.negate.IsContradiction := isContradiction_negate fun σ => holds_iff_slack.2 (by
    rw [key _ _ hlr hlr R (mem hR)]; simp)
  have hnd : ((lexOrder n).vars ++ List.range' (2 * n) n).Nodup := by
    simp only [lexOrder, Order.vars, List.append_nil, List.nodup_append, List.nodup_range,
      List.mem_append, List.mem_range, List.mem_range'_1, true_and]
    and_intros
    all_goals first | exact List.nodup_range' | (intro a ha b hb; omega)
  have hwf : (lexOrder n).wellFormed = true := by
    refine Order.wellFormed_iff.2 ⟨by simp [lexOrder], lexOrder_nodup n, fun D hD t ht => ?_⟩
    simp only [lexOrder, List.nil_append, List.mem_singleton] at hD
    subst hD
    rcases mem_lexTerms ht with h | h <;>
      simp only [posLits, List.map_map, Function.comp_def, List.map_id'] at h <;>
      simp [Order.vars, lexOrder, h]
  have hL : (lexOrder n).left = List.range n := rfl
  have hRt : (lexOrder n).right = List.range' n n := rfl
  have hA : (lexOrder n).aux = [] := rfl
  have hS : ∀ a b r, (lexOrder n).specC a b r = [] := fun _ _ _ => rfl
  have hP0 : posVals [] = [] := rfl
  unfold Order.defCheck Order.transCheck Order.reflCheck hashGoalsCheck
  simp only [lexTransVars, List.append_nil, hnd, hwf, hL, hRt, hA, hS, hP0, hP₁, hP₂, hG, hR]
  simp [Order.specCheckFrom, lexOrder, lexTransProof, lexReflProof, runGoals, runItem, runSteps,
    runStep, polEval, lookup, initDb, pushAll, hashAt, namesContra, hashGoalsOk, visible, negGoal,
    ht, hr]

/-- The lexicographic order on `n` bits is a good order. -/
theorem good_lexOrder (n : ℕ) : (lexOrder n).Good :=
  Order.good_of_defCheck (defCheck_lexOrder n)

/-- **The semantics of the lexicographic order**: on vectors of `n` bits, `x ⪯ y` exactly when
`x ≤ y` in the lexicographic order of lists, `false` before `true`. -/
theorem lexOrder_le_iff {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    (lexOrder n).Le x y ↔ x ≤ y := by
  have hnd := lexOrder_nodup n
  simp only [Order.vars, List.nodup_append] at hnd
  obtain ⟨⟨hl, hr, hlr⟩, -, -⟩ := hnd
  have h1 : (List.range n).map ((lexOrder n).inst x y []) = x :=
    map_assignOn hl (by simp [lexOrder, hx]) _
  have h2 : (List.range' n n).map ((lexOrder n).inst x y []) = y := by
    rw [Order.inst, map_assignOn_of_disjoint (ks := (lexOrder n).left)
      (js := List.range' n n) (fun j hj hjl => hlr _ hjl _ hj rfl)]
    exact map_assignOn hr (by simp [lexOrder, hy]) _
  have hD : (lexConstr (posLits (List.range n)) (posLits (List.range' n n))).Holds
      ((lexOrder n).inst x y []) ↔ x ≤ y := by
    rw [holds_iff_slack, slack_lexConstr (by simp [posLits]), map_eval_posLits,
      map_eval_posLits]
    rw [h1, h2, ← binVal_le_binVal_iff (hx.trans hy.symm)]
    omega
  constructor
  · rintro ⟨ρ, hρ, h⟩
    obtain rfl : ρ = [] := List.length_eq_zero_iff.1 (by simpa [lexOrder] using hρ)
    exact hD.1 (h _ (by simp [lexOrder]))
  · intro h
    exact ⟨[], by simp [lexOrder], by simpa [lexOrder] using hD.2 h⟩

/-! ### Lex-leader constraints by dominance -/

/-- The witness of a map of variables to literals, such as a symmetry `π` given by its
non-identity part: `x ↦ π(x)` for each pair `(x, π(x))`. -/
def Witness.ofLits (π : List (ℕ × Literal ℕ)) : Witness := π.map fun e => (e.1, .lit e.2)

/-- The image `ℓ↾ω` of a literal under a witness, when it is a literal; `ℓ` itself otherwise. -/
def Witness.litImage (ω : Witness) (l : Literal ℕ) : Literal ℕ :=
  match Witness.litVal ω l with
  | .lit m => m
  | _ => l

private theorem ofLits_lits (π : List (ℕ × Literal ℕ)) :
    ∀ e ∈ Witness.ofLits π, ∃ l, e.2 = .lit l := by
  intro e he
  simp only [Witness.ofLits, List.mem_map] at he
  obtain ⟨e', -, rfl⟩ := he
  exact ⟨_, rfl⟩

private theorem litVal_ofLits (π : List (ℕ × Literal ℕ)) (l : Literal ℕ) :
    Witness.litVal (Witness.ofLits π) l = .lit (Witness.litImage (Witness.ofLits π) l) := by
  unfold Witness.litImage Witness.litVal
  cases hf : (Witness.ofLits π).find l.1 with
  | none => rfl
  | some w =>
    simp only [Witness.find, Option.map_eq_some_iff] at hf
    obtain ⟨e, he, rfl⟩ := hf
    obtain ⟨m, hm⟩ := ofLits_lits π e (List.mem_of_find?_eq_some he)
    simp [hm]

theorem eval_litImage_ofLits (π : List (ℕ × Literal ℕ)) (σ : ℕ → Bool) (l : Literal ℕ) :
    Literal.eval σ (Witness.litImage (Witness.ofLits π) l) =
      Literal.eval (Witness.apply σ (Witness.ofLits π)) l := by
  rw [← Witness.eval_litVal, litVal_ofLits]
  rfl

/-- The lexicographic order loaded over the variables `xs`, `load_order lex xs`. -/
def lexLoaded (xs : List ℕ) : LoadedOrder := ⟨lexOrder xs.length, posLits xs⟩

theorem good_lexLoaded (xs : List ℕ) : (lexLoaded xs).Good :=
  ⟨good_lexOrder _, by simp [lexLoaded, lexOrder, posLits], by simp [lexLoaded, lexOrder]⟩

/-- **The lex-leader constraint** `z ⪯_lex z↾π` of the map `π` of variables to literals, over the
variables `z = xs` (eq. (20) of Bogaerts, Gocht, McCreesh and Nordström, `C_LL`, over the
order's variables), as the single constraint `Cslib.Logic.PL.VeriPB.lexConstr`. -/
def lexLeader (xs : List ℕ) (π : List (ℕ × Literal ℕ)) : PBConstr :=
  lexConstr (posLits xs) ((posLits xs).map (Witness.litImage (Witness.ofLits π)))

/-- **The lex-leader constraint holds** exactly when the values of `xs` are lexicographically at
most their values under the symmetry. -/
theorem holds_lexLeader_iff (xs : List ℕ) (π : List (ℕ × Literal ℕ)) (σ : ℕ → Bool) :
    (lexLeader xs π).Holds σ ↔
      xs.map σ ≤ xs.map (Witness.apply σ (Witness.ofLits π)) := by
  rw [holds_iff_slack, lexLeader, slack_lexConstr (by simp), List.map_map,
    Function.comp_def]
  simp only [eval_litImage_ofLits]
  rw [map_eval_posLits, map_eval_posLits, ← binVal_le_binVal_iff (by simp)]
  omega

/-- The subproof of the `dom` step of `Cslib.Logic.PL.VeriPB.lexLeaderStep`, for the next
number `n`. -/
def lexLeaderItems (n : ℕ) : List RedItem :=
  [.goal (.hash 1) [.pol [.id n, .id (n + 1), .add]] (n + 2),
    .goal (.hash 2) [.pol [.id n, .id (n + 3), .add]] (n + 4)]

/-- The `dom` step adding the lex-leader constraint of `π`, for the next number `n`: `¬C` is `n`;
`proofgoal #1` refutes the negated order goal `¬O⪯(z↾ω, z)`, numbered `n + 1`, by the sum
`n + (n + 1)`, numbered `n + 2`; `proofgoal #2` refutes `O⪯(z, z↾ω)`, numbered `n + 3`, by the
sum `n + (n + 3)`, numbered `n + 4`; the constraint takes the number `n + 5`. The core goals
`D|ω` are left to the database, where a symmetry finds them. -/
def lexLeaderStep (xs : List ℕ) (π : List (ℕ × Literal ℕ)) (n : ℕ) : TopStep :=
  .dom (lexLeader xs π) (Witness.ofLits π) (some (lexLeaderItems n)) none

/-- The `dom` steps adding the lex-leader constraints of `π₁, …, πₖ` in turn, from the next
number `n`; each takes six numbers. -/
def lexLeaderSteps (xs : List ℕ) : List (List (ℕ × Literal ℕ)) → ℕ → List TopStep
  | [], _ => []
  | π :: πs, n => lexLeaderStep xs π n :: lexLeaderSteps xs πs (n + 6)

/-- **The symmetry-breaking proof prefix**: define the lexicographic order on `|xs|` bits under
`name`, load it over `xs`, and add the lex-leader constraints of `π₁, …, πₖ` by `dom`, from the
next number `n`. -/
def symmetryBreaking (name : String) (xs : List ℕ) (πs : List (List (ℕ × Literal ℕ))) (n : ℕ) :
    List TopStep :=
  .defOrder name (lexOrder xs.length) [] (lexTransVars xs.length) lexTransProof lexReflProof ::
    .loadOrder name (posLits xs) :: lexLeaderSteps xs πs n

/-- **`π` maps the formula `F` into itself**: the image under `π` of every constraint of `F`,
normalized, is a constraint of `F`, normalized, up to the order of terms. For a permutation of
literals compatible with negation, this says that `π` is a (syntactic) symmetry of `F`; it is
what the core goals of the `dom` step need. -/
def MapsInto (F : List PBConstr) (π : List (ℕ × Literal ℕ)) : Bool :=
  F.all fun D => F.any fun D' =>
    sameUpToOrder D'.normalize (Witness.substC (Witness.ofLits π) D.normalize).normalize

/-- The constraints added by `Cslib.Logic.PL.VeriPB.lexLeaderSteps` from the number `n`, latest
first, as the database lists them. -/
def lexLeaderDb (xs : List ℕ) : List (List (ℕ × Literal ℕ)) → ℕ → List (ℕ × PBConstr)
  | [], _ => []
  | π :: πs, n => lexLeaderDb xs πs (n + 6) ++ [(n + 5, (lexLeader xs π).normalize)]

private theorem mem_lexLeaderDb {xs : List ℕ} :
    ∀ {πs : List (List (ℕ × Literal ℕ))} {n : ℕ} {π : List (ℕ × Literal ℕ)}, π ∈ πs →
      ∃ m, (m, (lexLeader xs π).normalize) ∈ lexLeaderDb xs πs n
  | π' :: πs, n, π, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨n + 5, by simp [lexLeaderDb]⟩
    · obtain ⟨m, hm⟩ := mem_lexLeaderDb (xs := xs) (n := n + 6) h
      exact ⟨m, by simp [lexLeaderDb, hm]⟩

/-- **The `dom` check accepts the lex-leader constraint** of `π` under the lexicographic order
loaded over `xs`, whatever `xs` and `π`, provided `π` leaves the preserved variables alone, does
not raise the objective, and maps every core constraint to a constraint of the database (up to
normalization and the order of terms). -/
theorem domCheck_lexLeader {pres : Option (List ℕ)} {obj : Option Objective} {xs : List ℕ}
    {π : List (ℕ × Literal ℕ)} {db core : List (ℕ × PBConstr)} {n : ℕ}
    (hpres : presFree pres (Witness.ofLits π) = true)
    (hobj : ∀ f ∈ obj, ∀ σ, f.eval (Witness.apply σ (Witness.ofLits π)) ≤ f.eval σ)
    (hcore : ∀ e ∈ core, ∃ e' ∈ db,
      sameUpToOrder e'.2 (Witness.substC (Witness.ofLits π) e.2).normalize = true) :
    domCheck pres obj (lexLoaded xs) db core n (lexLeader xs π) (Witness.ofLits π)
      (lexLeaderItems n) none = some (n + 5) := by
  set ω := Witness.ofLits π
  set C := lexLeader xs π
  obtain ⟨G₁, hG₁⟩ : ∃ G, (lexLoaded xs).leGoals ω = [G] := ⟨_, rfl⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G, (lexLoaded xs).geGoals ω = [G] := ⟨_, rfl⟩
  have hz : (posLits xs).length = xs.length := by simp [posLits]
  have hlv : ∀ w ∈ (posLits xs).map (Witness.litVal ω), ∃ l, w = .lit l := by
    intro w hw
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨_, litVal_ofLits π l⟩
  have hl : ∀ w ∈ (posLits xs).map WVal.lit, ∃ l, w = .lit l := by
    intro w hw
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨l, rfl⟩
  have hpos : ∀ w ∈ (posLits xs).map WVal.lit, ∃ x, w = .lit (x, true) := by
    intro w hw
    obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hw
    simp only [posLits, List.mem_map] at hl'
    obtain ⟨x, -, rfl⟩ := hl'
    exact ⟨x, rfl⟩
  have hm1 : G₁ ∈ (lexOrder xs.length).instC ((posLits xs).map (Witness.litVal ω))
      ((posLits xs).map WVal.lit) [] := by
    have : (lexLoaded xs).leGoals ω = (lexOrder xs.length).instC
        ((posLits xs).map (Witness.litVal ω)) ((posLits xs).map WVal.lit) [] := rfl
    rw [← this, hG₁]; exact List.mem_singleton_self _
  have hm2 : G₂ ∈ (lexOrder xs.length).instC ((posLits xs).map WVal.lit)
      ((posLits xs).map (Witness.litVal ω)) [] := by
    have : (lexLoaded xs).geGoals ω = (lexOrder xs.length).instC
        ((posLits xs).map WVal.lit) ((posLits xs).map (Witness.litVal ω)) [] := rfl
    rw [← this, hG₂]; exact List.mem_singleton_self _
  -- The slacks, as binary values of `z` and of `z↾ω`.
  have hC : ∀ σ, C.slack σ = binVal ((posLits xs).map (Literal.eval (Witness.apply σ ω))) -
      binVal ((posLits xs).map (Literal.eval σ)) := fun σ => by
    change (lexConstr (posLits xs) ((posLits xs).map (Witness.litImage ω))).slack σ = _
    rw [slack_lexConstr (by simp), List.map_map, Function.comp_def]
    simp only [ω, eval_litImage_ofLits]
  have h₁ : ∀ σ, G₁.slack σ = binVal ((posLits xs).map (Literal.eval σ)) -
      binVal ((posLits xs).map (Literal.eval (Witness.apply σ ω))) := fun σ => by
    rw [slack_instC_lexOrder (by simp [posLits]) (by simp [posLits]) hlv hl hm1,
      LoadedOrder.map_eval_lit,
      LoadedOrder.map_eval_litVal]
  have h₂ : ∀ σ, G₂.slack σ = binVal ((posLits xs).map (Literal.eval (Witness.apply σ ω))) -
      binVal ((posLits xs).map (Literal.eval σ)) := fun σ => by
    rw [slack_instC_lexOrder (by simp [posLits]) (by simp [posLits]) hl hlv hm2,
      LoadedOrder.map_eval_lit,
      LoadedOrder.map_eval_litVal]
  have hCex : ∃ τ, C.slack τ ≤ 0 := ⟨fun _ => true, by
    rw [hC]
    have := binVal_le_of_forall_true
      (x := (posLits xs).map (Literal.eval (Witness.apply (fun _ => true) ω)))
      (y := (posLits xs).map (Literal.eval fun _ => true)) (by simp)
      (by simp [posLits, Literal.eval])
    omega⟩
  have hG₁ex := exists_slack_instC_le (by simp [posLits]) (by simp [posLits]) hlv hl (.inr hpos)
    hm1
  -- The two refutations.
  have hc₁ : (C.negate.add G₁.negate).IsContradiction := isContradiction_add fun σ => by
    have := slack_negate_le C σ
    have := slack_negate_le G₁ σ
    rw [slack_normalize_of_exists hCex] at *
    rw [slack_normalize_of_exists hG₁ex] at *
    rw [hC] at *; rw [h₁] at *
    omega
  have hc₂ : (C.negate.add G₂.normalize).IsContradiction := isContradiction_add fun σ => by
    have := slack_negate_le C σ
    have := slack_normalize_le G₂ σ
    rw [slack_normalize_of_exists hCex, hC] at *
    rw [h₂] at *
    omega
  -- The objective goal is trivially true, and the core goals are in the database.
  have hobj' : ∀ f ∈ obj, (objGoal f ω).normalize.degree = 0 := fun f hf =>
    normalize_degree_eq_zero fun σ => (holds_objGoal σ f ω).2 (hobj f hf σ)
  have hfresh : (lexLoaded xs).fresh (db ++ core) obj C ω = true := by
    simp only [LoadedOrder.fresh, lexLoaded, lexOrder, Order.avoids, LoadedOrder.imageAvoids]
    simp only [List.contains_nil, Bool.not_false, Bool.and_eq_true, List.all_eq_true,
      Option.all_eq_true]
    exact ⟨⟨⟨fun _ _ _ _ => trivial, fun _ _ => trivial⟩, fun _ _ _ _ => trivial⟩,
      fun e _ => by split <;> rfl⟩
  unfold domCheck
  simp only [hpres, hfresh, Bool.and_self, ↓reduceIte]
  simp only [lexLeaderItems, domHashPremises, hG₁, hG₂, runGoals, runItem, hashAt, pushAll,
    runSteps, runStep, polEval, lookup, negGoal, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ]
  have h3 : (n + 1 + 1 + 1 == n) = false := beq_eq_false_iff_ne.2 (by omega)
  have hv : ∀ b, visible b [(none, [G₂.normalize]), (none, [G₁.negate])] =
      [[G₂.normalize], [G₁.negate]] := fun _ => rfl
  have hok : domOk obj (lexLoaded xs) db core ω C ((n, C.negate) :: db)
      [(none, [G₂.normalize]), (none, [G₁.negate])] none = true := by
    unfold domOk
    rw [hv, hv, hG₁, hG₂]
    simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
    refine ⟨⟨by simp, by simp [goalCovered, objuCovered, negGoal]⟩, ?_⟩
    unfold substCovered
    simp only [Bool.and_eq_true, Option.all_eq_true, List.all_eq_true]
    refine ⟨fun f hf => by simp [goalCovered, objuCovered, hobj' f hf], fun e he => ?_⟩
    obtain ⟨e', he', hs⟩ := hcore e he
    have : db.any (fun e' => sameUpToOrder e'.2 (Witness.substC ω e.2).normalize) = true :=
      List.any_eq_true.2 ⟨e', he', hs⟩
    simp [goalCovered, objuCovered, this]
  simp [namesContra, lookup, hc₁, hc₂, h3, hok]

/-- **One lex-leader step is accepted** in a state with the lexicographic order loaded over `xs`:
it adds the lex-leader constraint of `π` under the number `n + 5`, for the next number `n`. -/
theorem stepTop_lexLeaderStep {F : List PBConstr} {obj : Option Objective} {s : State}
    {xs : List ℕ} {π : List (ℕ × Literal ℕ)} (hord : s.order = some (lexLoaded xs))
    (hpres : presFree s.pres (Witness.ofLits π) = true)
    (hobj : ∀ f ∈ s.obj, ∀ σ, f.eval (Witness.apply σ (Witness.ofLits π)) ≤ f.eval σ)
    (hcore : ∀ e ∈ s.core, ∃ e' ∈ s.db,
      sameUpToOrder e'.2 (Witness.substC (Witness.ofLits π) e.2).normalize = true) :
    stepTop F obj s (lexLeaderStep xs π s.next) =
      some (s.addStrengthened (s.next + 5) (lexLeader xs π)) := by
  simp only [stepTop, lexLeaderStep, hord, Option.getD_some,
    domCheck_lexLeader hpres hobj hcore, Option.isSome_some, ite_true]

/-- **Several lex-leader steps are accepted**, each checked against the database so far: from a
state with the lexicographic order loaded over `xs`, outside strengthening-to-core mode, the
steps for `π₁, …, πₖ` add their lex-leader constraints to the database, numbered
`n + 5, n + 11, …`, and change nothing else but the next number. -/
theorem runTop_lexLeaderSteps {F : List PBConstr} {obj : Option Objective} {xs : List ℕ} :
    ∀ {πs : List (List (ℕ × Literal ℕ))} {s : State}, s.order = some (lexLoaded xs) →
      s.tcb = false → (∀ π ∈ πs, presFree s.pres (Witness.ofLits π) = true) →
      (∀ π ∈ πs, ∀ f ∈ s.obj, ∀ σ, f.eval (Witness.apply σ (Witness.ofLits π)) ≤ f.eval σ) →
      (∀ π ∈ πs, ∀ e ∈ s.core, ∃ e' ∈ s.db,
        sameUpToOrder e'.2 (Witness.substC (Witness.ofLits π) e.2).normalize = true) →
      runTop F obj s (lexLeaderSteps xs πs s.next) =
        some { s with db := lexLeaderDb xs πs s.next ++ s.db, next := s.next + 6 * πs.length }
  | [], s, _, _, _, _, _ => by simp [lexLeaderSteps, lexLeaderDb, runTop_nil]
  | π :: πs, s, hord, htcb, hpres, hobj, hcore => by
    have h1 := stepTop_lexLeaderStep (F := F) (obj := obj) hord (hpres π List.mem_cons_self)
      (hobj π List.mem_cons_self) (hcore π List.mem_cons_self)
    rw [lexLeaderSteps, runTop_cons, h1, Option.bind_some]
    have ih := runTop_lexLeaderSteps (F := F) (obj := obj) (xs := xs) (πs := πs)
      (s := s.addStrengthened (s.next + 5) (lexLeader xs π)) hord
      (by simp [State.addStrengthened, htcb])
      (fun π' h' => hpres π' (List.mem_cons_of_mem _ h'))
      (fun π' h' => hobj π' (List.mem_cons_of_mem _ h'))
      (fun π' h' e he => by
        simp only [State.addStrengthened, htcb] at he ⊢
        obtain ⟨e', he', h⟩ := hcore π' (List.mem_cons_of_mem _ h') e he
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩)
    simp only [State.addStrengthened, htcb] at ih ⊢
    rw [ih]
    simp only [lexLeaderDb, List.append_assoc, List.singleton_append, List.length_cons]
    congr 2
    omega

private theorem exists_initDb_of_mem {F : List PBConstr} {D : PBConstr} (hD : D ∈ F) :
    ∃ e ∈ initDb F, e.2 = D.normalize := by
  have : D.normalize ∈ (initDb F).map (·.2) := by
    simp only [initDb, List.map_map]
    rw [show ((·.2) ∘ fun e : PBConstr × ℕ => (e.2 + 1, e.1.normalize)) = normalize ∘ Prod.fst
      from rfl, ← List.map_map, List.zipIdx_map_fst]
    exact List.mem_map_of_mem hD
  simpa using this

private theorem exists_of_mem_initDb {F : List PBConstr} {e : ℕ × PBConstr}
    (he : e ∈ initDb F) : ∃ D ∈ F, e.2 = D.normalize := by
  simp only [initDb, List.mem_map] at he
  obtain ⟨⟨D, i⟩, hD, rfl⟩ := he
  exact ⟨D, List.fst_mem_of_mem_zipIdx hD, rfl⟩

/-- The state after the symmetry-breaking prefix: the order defined and loaded, the lex-leader
constraints added. -/
def symmetryBreakingState (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ))
    (name : String) (xs : List ℕ) (πs : List (List (ℕ × Literal ℕ))) : State :=
  { State.init F obj pres with
    db := lexLeaderDb xs πs (F.length + 1) ++ initDb F,
    next := F.length + 1 + 6 * πs.length,
    orders := [(name, lexOrder xs.length)], order := some (lexLoaded xs),
    orderName := some name }

/-- **The checker accepts the symmetry-breaking prefix** for symmetries `π₁, …, πₖ` of the
formula `F` that leave the preserved variables alone and do not raise the objective: it defines
and loads the lexicographic order over `xs` and adds the lex-leader constraint of every `πᵢ` by
`dom`. -/
theorem runTop_symmetryBreaking {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {name : String} {xs : List ℕ} {πs : List (List (ℕ × Literal ℕ))}
    (hsym : ∀ π ∈ πs, MapsInto F π = true)
    (hpres : ∀ π ∈ πs, presFree pres (Witness.ofLits π) = true)
    (hobj : ∀ π ∈ πs, ∀ f ∈ obj, ∀ σ, f.eval (Witness.apply σ (Witness.ofLits π)) ≤ f.eval σ) :
    runTop F obj (State.init F obj pres) (symmetryBreaking name xs πs (F.length + 1)) =
      some (symmetryBreakingState F obj pres name xs πs) := by
  have hcore : ∀ π ∈ πs, ∀ e ∈ initDb F, ∃ e' ∈ initDb F,
      sameUpToOrder e'.2 (Witness.substC (Witness.ofLits π) e.2).normalize = true := by
    intro π hπ e he
    obtain ⟨D, hD, he2⟩ := exists_of_mem_initDb he
    have := hsym π hπ
    simp only [MapsInto, List.all_eq_true, List.any_eq_true] at this
    obtain ⟨D', hD', hs⟩ := this D hD
    obtain ⟨e', he', he'2⟩ := exists_initDb_of_mem hD'
    exact ⟨e', he', by rw [he'2, he2]; exact hs⟩
  have h := runTop_lexLeaderSteps (F := F) (obj := obj) (xs := xs) (πs := πs)
    (s := { State.init F obj pres with
      orders := [(name, lexOrder xs.length)], core := initDb F, order := some (lexLoaded xs),
      orderName := some name }) rfl rfl hpres hobj hcore
  have h0 : stepTop F obj (State.init F obj pres) (.defOrder name (lexOrder xs.length) []
      (lexTransVars xs.length) lexTransProof lexReflProof) =
      some { State.init F obj pres with orders := [(name, lexOrder xs.length)] } := by
    simp only [stepTop, defCheck_lexOrder, ite_true]
    rfl
  have h1 : stepTop F obj { State.init F obj pres with orders := [(name, lexOrder xs.length)] }
      (.loadOrder name (posLits xs)) = some { State.init F obj pres with
        orders := [(name, lexOrder xs.length)], core := initDb F, order := some (lexLoaded xs),
        orderName := some name } := by
    have hl : (posLits xs).length == (lexOrder xs.length).left.length := by
      simp [posLits, lexOrder]
    have ha : (posLits xs).all (fun l => !(lexOrder xs.length).aux.contains l.1) := by
      simp [lexOrder]
    simp only [stepTop, List.lookup, beq_self_eq_true, hl, ha, Bool.and_self, ite_true]
    rfl
  rw [symmetryBreaking, runTop_cons, h0, Option.bind_some, runTop_cons, h1, Option.bind_some]
  exact h

/-- **Symmetry breaking preserves the optimum**: for symmetries `π₁, …, πₖ` of `F` that do not
raise the objective, every solution `σ` of `F` gives a solution of `F` and of all the lex-leader
constraints whose objective value is at most that of `σ`. It is proved through the checker: the
symmetry-breaking prefix is accepted (`Cslib.Logic.PL.VeriPB.runTop_symmetryBreaking`), and the
lower-bound invariant of the accepted run (`Cslib.Logic.PL.VeriPB.InjInv.reaches`), which rests
on `Cslib.Logic.PL.VeriPB.SatObjPo.dom` for each `dom` step, gives the solution. -/
theorem exists_lexLeader_le {F : List PBConstr} {obj : Option Objective} {xs : List ℕ}
    {πs : List (List (ℕ × Literal ℕ))} (hsym : ∀ π ∈ πs, MapsInto F π = true)
    (hobj : ∀ π ∈ πs, ∀ f ∈ obj, ∀ σ, f.eval (Witness.apply σ (Witness.ofLits π)) ≤ f.eval σ)
    {σ : ℕ → Bool} (hσ : ∀ c ∈ F, c.Holds σ) :
    ∃ τ, (∀ c ∈ F, c.Holds τ) ∧ (∀ π ∈ πs, (lexLeader xs π).Holds τ) ∧
      objValue obj τ ≤ objValue obj σ := by
  obtain ⟨-, hinj⟩ := invariants_of_runTop (runTop_symmetryBreaking (pres := none)
    (name := "lex") (xs := xs) hsym (fun _ _ => rfl) hobj)
  rcases hinj.reaches hσ with ⟨τ, hτ, hle⟩ | ⟨d, hd, -⟩
  · refine ⟨τ, holds_of_allHold_initDb fun e he => hτ e (List.mem_append_right _ he),
      fun π hπ => ?_, hle⟩
    obtain ⟨m, hm⟩ := mem_lexLeaderDb (n := F.length + 1) hπ
    exact (holds_normalize _ _).1 (hτ _ (List.mem_append_left _ hm))
  · simp [symmetryBreakingState, State.init] at hd

end VeriPB

end Cslib.Logic.PL

end
