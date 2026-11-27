/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Propagate
import CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete
-- The proofs read the engine's private state and transitions (`EState`, `propLoop`, …).
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Propagate
-- The engine sorts the terms of a constraint with `Array.qsort`; that it permutes them is proved
-- from its body.
import all Init.Data.Array.QSort.Basic

/-!
# Soundness of the propagation engine of the VeriPB elaborator

The elaborator (`Cslib.Logic.PL.VeriPB.Elab`) turns the hintless `rup C;` of the augmented format
into a hinted kernel step, with the hints its propagation engine finds
(`Cslib.Logic.PL.VeriPB.Elab.Engine.rupHints`). The kernel checks those hints when the step
reaches the kernel proof, but trimming drops the steps that nothing uses, and for those the
engine's verdict is all there is. This file proves the verdict sound: when the engine reports a
conflict for the negation of `C`, then `C` follows from the engine's constraints by reverse unit
propagation in the kernel's sense (`Cslib.Logic.PL.VeriPB.rup`), along some list of hints.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Elab.Engine.Built e D`: the engine `e` is built from
  `Cslib.Logic.PL.VeriPB.Elab.Engine.new` by the engine's operations (`add`, `kill`, `rupHints`,
  `extend`), and `D` gives the kernel hint and the constraint of each engine index added and not
  deleted since.

## Main results

* `Cslib.Logic.PL.VeriPB.Elab.Engine.Built.rupHints_sound`: if `rupHints neg` returns hints, then
  some list of hints takes the kernel's propagation (`Cslib.Logic.PL.VeriPB.rupHints`) from `neg`
  and a database holding the constraints of `D` under their hints to a conflict.
* `Cslib.Logic.PL.VeriPB.Elab.Engine.Built.rup_of_rupHints`: the same for `neg` the kernel's
  negation of `C`: `Cslib.Logic.PL.VeriPB.rup db C hs = true` for some `hs`.

The list of hints of these theorems is the reasons of the entries of the engine's trail, in trail
order, then the conflicting constraint (`Cslib.Logic.PL.VeriPB.rupHints_of_forces`). It need not be
the list `rupHints` returns, which keeps only the reasons the conflict needs; that the returned
list replays as well is not proved here.

## Proof

The engine's state (`Cslib.Logic.PL.VeriPB.Elab.EState`, private to its module) is related to the
constraints `G` of its live engine indices by an invariant, `Inv`:
* literal codes decode injectively to literals of the variables met (`dec`);
* the values agree with the trail, which assigns each variable once;
* each record represents its constraint: the codes of its terms with positive coefficients, and,
  for a constraint propagating through its slack counter, the coefficients too (`Rep`);
* the occurrence lists hold, for each live constraint with a slack counter, exactly its
  coefficients on each literal, and its counter is its slack on the processed part of the trail;
* a live clause is watched by a literal at most as often as the literal occurs among its first two
  terms;
* unless the root level is to be rebuilt, the entries of the trail are forced by live reasons,
  marked as root reasons, and a recorded root conflict is real.

Each operation keeps it (`add_spec`, `kill_spec`, `rebuild_spec`, `rupHints_spec`, `extend_spec`),
through the propagation loops (`propagate_spec`, with `pbLoop_spec` for the slack counters and
`watchLoop_spec` for the clauses), backtracking (`backtrack_spec`) and the addition and removal of
constraints (`pushCons_spec`, `checkFresh_spec`, `removal_spec`). A conflict is then a chain of
forced literals ending in a constraint of negative slack, and such a chain replays under the
kernel's propagation (`Cslib.Logic.PL.VeriPB.Forces.propagate`), since the kernel's slack only
falls as its trail grows.

The proofs need the engine's private definitions, hence the `import all` of its module; they live
here rather than beside the engine so that the engine's file stays readable and proof edits do not
rebuild its clients.
-/

public section

namespace Cslib.Logic.PL.VeriPB.Elab

open PBConstr

/-! ### Arrays and byte arrays -/

private theorem getElem!_eq {α : Type} [Inhabited α] (a : Array α) (i : ℕ) :
    a[i]! = a[i]?.getD default := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

private theorem ByteArray.get!_eq (b : ByteArray) (i : ℕ) : b.get! i = b.data[i]! := by
  cases b; rfl

private theorem ByteArray.data_set! (b : ByteArray) (i : ℕ) (v : UInt8) :
    (b.set! i v).data = b.data.set! i v := by
  cases b; rfl

private theorem ByteArray.data_push (b : ByteArray) (v : UInt8) :
    (b.push v).data = b.data.push v := by
  cases b; rfl

/-- A byte read after a write. -/
private theorem ByteArray.get!_set! (b : ByteArray) (i j : ℕ) (v : UInt8) :
    (b.set! i v).get! j = if i = j ∧ i < b.size then v else b.get! j := by
  simp only [ByteArray.get!_eq, ByteArray.data_set!, getElem!_eq, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, ← ByteArray.size_data]
  split_ifs <;> grind

private theorem ByteArray.size_set! (b : ByteArray) (i : ℕ) (v : UInt8) :
    (b.set! i v).size = b.size := by
  simp only [← ByteArray.size_data, ByteArray.data_set!, Array.size_set!]

private theorem ByteArray.get!_push (b : ByteArray) (j : ℕ) (v : UInt8) :
    (b.push v).get! j = if j = b.size then v else b.get! j := by
  simp only [ByteArray.get!_eq, ByteArray.data_push, getElem!_eq, Array.getElem?_push,
    ← ByteArray.size_data]
  split_ifs <;> simp

private theorem ByteArray.size_push' (b : ByteArray) (v : UInt8) :
    (b.push v).size = b.size + 1 := by
  simp only [← ByteArray.size_data, ByteArray.data_push, Array.size_push]

private theorem ByteArray.get!_ge (b : ByteArray) {j : ℕ} (h : b.size ≤ j) : b.get! j = 0 := by
  rw [ByteArray.get!_eq, getElem!_eq, Array.getElem?_eq_none (by rw [ByteArray.size_data]; exact h)]
  rfl

private theorem getElem?_swapIfInBounds {α : Type} (a : Array α) (i j k : ℕ) :
    (a.swapIfInBounds i j)[k]? =
      if i < a.size ∧ j < a.size then (if k = i then a[j]? else if k = j then a[i]? else a[k]?)
      else a[k]? := by
  by_cases hi : i < a.size <;> by_cases hj : j < a.size
  · rw [Array.swapIfInBounds_def]; simp only [hi, hj, dite_true]
    rw [Array.getElem?_swap]; grind
  all_goals simp [Array.swapIfInBounds_def, hi, hj]

/-! ### Literal codes -/

private theorem xor_one_div_two (ℓ : ℕ) : (ℓ ^^^ 1) / 2 = ℓ / 2 := by
  rw [Nat.xor_div_two]; simp

private theorem xor_one_mod_two (ℓ : ℕ) : (ℓ ^^^ 1) % 2 = (ℓ + 1) % 2 := by
  have h := @Nat.xor_mod_two_eq_one ℓ 1
  rcases Nat.mod_two_eq_zero_or_one ℓ with a | a
  · have : (ℓ ^^^ 1) % 2 = 1 := by simp [h, a]
    omega
  · have : (ℓ ^^^ 1) % 2 ≠ 1 := by simp [h, a]
    omega

private theorem xor_one_xor_one (ℓ : ℕ) : ℓ ^^^ 1 ^^^ 1 = ℓ := by
  rw [Nat.xor_assoc]; simp

private theorem xor_one_ne (ℓ : ℕ) : ℓ ^^^ 1 ≠ ℓ := fun h => by
  have := xor_one_mod_two ℓ; rw [h] at this; omega

private theorem xor_one_lt {ℓ n : ℕ} : ℓ ^^^ 1 < 2 * n ↔ ℓ < 2 * n := by
  have := xor_one_div_two ℓ; omega

/-- Two codes on the same variable with the same sign are equal. -/
private theorem code_eq {ℓ m : ℕ} (h1 : ℓ / 2 = m / 2) (h2 : ℓ % 2 = m % 2) : ℓ = m := by omega

/-- Codes on the same variable are equal or opposite. -/
private theorem code_eq_or_xor {ℓ m : ℕ} (h : ℓ / 2 = m / 2) : m = ℓ ∨ m = ℓ ^^^ 1 := by
  have h1 := xor_one_div_two ℓ
  have h2 := xor_one_mod_two ℓ
  by_cases hm : m % 2 = ℓ % 2
  · exact Or.inl (code_eq h.symm hm)
  · exact Or.inr (code_eq (by omega) (by omega))

/-- The literal of a code: `2 i` is the `i`-th variable met, `2 i + 1` its negation. -/
private def dec (vars : Array ℕ) (ℓ : ℕ) : Literal ℕ := (vars[ℓ / 2]!, ℓ % 2 == 0)

private theorem dec_xor (vars : Array ℕ) (ℓ : ℕ) :
    dec vars (ℓ ^^^ 1) = Std.Sat.Literal.negate (dec vars ℓ) := by
  simp only [dec, xor_one_div_two, Std.Sat.Literal.negate, xor_one_mod_two]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one ℓ with h | h <;> simp [h, Nat.add_mod]

/-- Decoding is injective on the codes of the variables met. -/
private theorem dec_inj {vars : Array ℕ} (hv : vars.toList.Nodup) {ℓ m : ℕ}
    (hℓ : ℓ < 2 * vars.size) (hm : m < 2 * vars.size) (h : dec vars ℓ = dec vars m) : ℓ = m := by
  simp only [dec, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hi : ℓ / 2 < vars.size := by omega
  have hj : m / 2 < vars.size := by omega
  rw [getElem!_pos vars _ hi, getElem!_pos vars _ hj] at h1
  have := (List.Nodup.getElem_inj_iff hv (i := ℓ / 2) (j := m / 2) (hi := by simpa using hi)
    (hj := by simpa using hj)).1 (by simpa using h1)
  refine code_eq this ?_
  rcases Nat.mod_two_eq_zero_or_one ℓ with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one m with b | b <;>
    simp_all

/-- The literals of the first `k` entries of a trail of codes. -/
private def tlits (vars : Array ℕ) (trail : Array ℕ) (k : ℕ) : List (Literal ℕ) :=
  (trail.toList.take k).map (dec vars)

/-- Membership of a decoded literal in a decoded trail is membership of the code. -/
private theorem dec_mem_tlits {vars trail : Array ℕ} (hv : vars.toList.Nodup)
    (ht : ∀ m ∈ trail, m < 2 * vars.size) {ℓ : ℕ} (hℓ : ℓ < 2 * vars.size) (k : ℕ) :
    dec vars ℓ ∈ tlits vars trail k ↔ ℓ ∈ trail.toList.take k := by
  simp only [tlits, List.mem_map]
  constructor
  · rintro ⟨m, hm, he⟩
    have hm' : m < 2 * vars.size := ht m (by simpa using List.mem_of_mem_take hm)
    rw [dec_inj hv hℓ hm' he.symm]; exact hm
  · exact fun h => ⟨ℓ, h, rfl⟩

/-- Codes of the variables met decode the same once more variables are met. -/
private theorem dec_ext {vars vars' : Array ℕ} (h : vars.toList <+: vars'.toList) {ℓ : ℕ}
    (hℓ : ℓ < 2 * vars.size) : dec vars' ℓ = dec vars ℓ := by
  have hi : ℓ / 2 < vars.size := by omega
  have hi' : ℓ / 2 < vars'.size := by
    have := h.length_le; simp only [Array.length_toList] at this; omega
  simp only [dec]
  rw [getElem!_pos vars _ hi, getElem!_pos vars' _ hi']
  congr 1
  have := h.getElem (i := ℓ / 2) (by simpa using hi)
  simpa using this.symm

private theorem tlits_ext {vars vars' trail : Array ℕ} (h : vars.toList <+: vars'.toList)
    (ht : ∀ m ∈ trail, m < 2 * vars.size) (k : ℕ) : tlits vars' trail k = tlits vars trail k := by
  simp only [tlits]
  refine List.map_congr_left fun m hm => dec_ext h (ht m ?_)
  simpa using List.mem_of_mem_take hm

private theorem tlits_take_sub {vars trail : Array ℕ} {k : ℕ} :
    ∀ l ∈ tlits vars trail k, l ∈ tlits vars trail trail.size := by
  intro l hl
  simp only [tlits, List.mem_map] at hl ⊢
  obtain ⟨m, hm, rfl⟩ := hl
  exact ⟨m, by rw [List.take_of_length_le (by simp)]; exact List.mem_of_mem_take hm, rfl⟩

/-! ### The invariant -/

/-- The consecutive pairs of a list. -/
private def pairsL : List ℕ → List (ℕ × ℕ)
  | a :: b :: r => (a, b) :: pairsL r
  | _ => []

/-- The total of the second components of the pairs of `os` naming `c`. -/
private def wsum (c : ℕ) (os : Array ℕ) : ℕ :=
  (((pairsL os.toList).filter (·.1 == c)).map (·.2)).sum

/-- The terms of `c` with positive coefficients. -/
private def posTerms (c : PBConstr) : List (ℕ × Literal ℕ) := c.terms.filter (0 < ·.1)

/-- The terms the engine stores for the record `r`: coefficient and literal code by position. -/
private def stored (lits coeffs : Array ℕ) (r : CRec) : List (ℕ × ℕ) :=
  (List.range r.size).map fun k => (coeffs[r.start + k]!, lits[r.start + k]!)

/-- The literal codes the engine stores for the record `r`. -/
private def scodes (lits : Array ℕ) (r : CRec) : List ℕ :=
  (List.range r.size).map fun k => lits[r.start + k]!

/-- The record `r` propagates through slack counters. -/
private def reg (r : CRec) : Bool := !r.clause && decide (0 < r.degree)

/-- The engine record `r`, with the term arrays, represents the constraint `pc`: the same degree
and the codes of its terms with positive coefficients; for a constraint propagating through its
slack, the same coefficients too; for a clause, a positive degree, two terms at least, and a
slack of the empty trail at least the true one. -/
private structure Rep (vars lits coeffs : Array ℕ) (r : CRec) (pc : PBConstr) : Prop where
  degree : r.degree = pc.degree
  lt : ∀ ℓ ∈ scodes lits r, ℓ < 2 * vars.size
  codes : ((scodes lits r).map (dec vars)).Perm ((posTerms pc).map (·.2))
  terms : r.clause = false →
    ((stored lits coeffs r).map fun p => (p.1, dec vars p.2)).Perm (posTerms pc)
  clause : r.clause = true →
    0 < pc.degree ∧ 2 ≤ r.size ∧ (coeffSum pc.terms : ℤ) - pc.degree ≤ r.slack0

/-- A well-formed assignment over `n` variables: values agree with the trail, which assigns each
variable at most once, and the trail positions are recorded. -/
private structure AsgOk (n : ℕ) (a : Asg) : Prop where
  value_size : a.value.size = 2 * n
  reason_size : a.reason.size = n
  tpos_size : a.tpos.size = n
  trail_lt : ∀ ℓ ∈ a.trail, ℓ < 2 * n
  nodup : (a.trail.toList.map (· / 2)).Nodup
  value_eq : ∀ ℓ, ℓ < 2 * n →
    a.value.get! ℓ = if ℓ ∈ a.trail then 1 else if ℓ ^^^ 1 ∈ a.trail then 2 else 0
  tpos_eq : ∀ k (hk : k < a.trail.size), a.tpos[a.trail[k] / 2]! = k

/-- Every trail entry from `m` on is forced, on the entries before it, by its reason. -/
private def ChainFrom (vars : Array ℕ) (G : ℕ → Option PBConstr) (m : ℕ) (a : Asg) : Prop :=
  ∀ k (hk : k < a.trail.size), m ≤ k → ∃ pc, G a.reason[a.trail[k] / 2]! = some pc ∧
    Forces (tlits vars a.trail k) pc (dec vars a.trail[k])

/-- `a'` extends the trail of `a`, keeping the reasons of its entries. -/
private def AsgExt (a a' : Asg) : Prop :=
  a.trail.toList <+: a'.trail.toList ∧ ∀ ℓ ∈ a.trail, a'.reason[ℓ / 2]! = a.reason[ℓ / 2]!

/-- The structural invariant of the engine, relative to the constraints `G` of its live engine
indices. -/
private structure InvCore (s : EState) (G : ℕ → Option PBConstr) : Prop where
  nodup : s.vars.toList.Nodup
  idx_some : ∀ x i, s.varIdx[x]? = some i → i < s.vars.size ∧ s.vars[i]! = x
  idx_mem : ∀ i, i < s.vars.size → s.varIdx[s.vars[i]!]? = some i
  asg : AsgOk s.vars.size s.asg
  watches_size : s.watches.size = 2 * s.vars.size
  occ_size : s.occ.size = 2 * s.vars.size
  qhead_le : s.qhead ≤ s.asg.trail.size
  cons_pos : 1 ≤ s.cons.size
  cpos_size : s.cpos.size = s.cons.size
  slack_size : s.slack.size = s.cons.size
  alive_size : s.cons.size ≤ s.alive.size
  rr_size : s.cons.size ≤ s.rootReason.size
  coeffs_size : s.coeffs.size = s.lits.size
  layout : ∀ c, 1 ≤ c → c < s.cons.size → s.cons[c]!.start = s.cpos[c]! ∧
    s.cons[c]!.start + s.cons[c]!.size =
      if c + 1 < s.cons.size then s.cpos[c + 1]! else s.lits.size
  alive0 : s.alive.get! 0 = 0
  live : ∀ c, (G c).isSome ↔ c < s.cons.size ∧ s.alive.get! c ≠ 0
  rep : ∀ c pc, G c = some pc → Rep s.vars s.lits s.coeffs s.cons[c]! pc
  occ_even : ∀ ℓ : ℕ, s.occ[ℓ]!.size % 2 = 0
  occ_name : ∀ ℓ : ℕ, ∀ p ∈ pairsL s.occ[ℓ]!.toList, p.1 < s.cons.size ∧
    (s.alive.get! p.1 ≠ 0 → reg s.cons[p.1]! = true)
  occ_exact : ∀ c pc, G c = some pc → reg s.cons[c]! = true → ∀ ℓ : ℕ,
    wsum c s.occ[ℓ]! = (((stored s.lits s.coeffs s.cons[c]!).filter (·.2 == ℓ)).map (·.1)).sum
  watch_name : ∀ ℓ : ℕ, ∀ c ∈ s.watches[ℓ]!, c < s.cons.size ∧ s.cons[c]!.clause = true
  watch_count : ∀ c pc, G c = some pc → s.cons[c]!.clause = true → ∀ ℓ : ℕ,
    s.watches[ℓ]!.count c ≤ [s.lits[s.cons[c]!.start]!, s.lits[s.cons[c]!.start + 1]!].count ℓ
  roots : ∀ i ∈ s.roots, i < s.cons.size ∧ (s.cons[i]!.clause = true ∨ 0 < s.cons[i]!.degree)

/-- The slack counter of every live constraint propagating through it is its slack on the
processed part of the trail. -/
private def SlackOk (s : EState) (G : ℕ → Option PBConstr) : Prop :=
  ∀ c pc, G c = some pc → reg s.cons[c]! = true →
    s.slack[c]! = VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc

/-- The invariant of the engine between its operations: the structural invariant, the slack
counters and, unless the root level is to be rebuilt, a root level whose entries are forced by
live reasons, marked as root reasons, and whose conflict, if any, is real. -/
private structure Inv (s : EState) (G : ℕ → Option PBConstr) : Prop extends InvCore s G where
  slack : SlackOk s G
  rootLen : s.dirty = false → s.rootLen = s.asg.trail.size
  rr : s.dirty = false → ∀ k (hk : k < s.asg.trail.size),
    s.rootReason.get! s.asg.reason[s.asg.trail[k] / 2]! ≠ 0
  chain : s.dirty = false → ChainFrom s.vars G 0 s.asg
  conflict : s.dirty = false → ∀ k, s.rootConflict = some k →
    ∃ pc, G k = some pc ∧ VeriPB.slack (tlits s.vars s.asg.trail s.asg.trail.size) pc < 0

/-! ### Slack through the stored terms -/

private theorem slack_posTerms (ρ : List (Literal ℕ)) (pc : PBConstr) :
    VeriPB.slack ρ pc =
      (coeffSum ((posTerms pc).filter fun t => !falsified ρ t) : ℤ) - pc.degree := by
  unfold VeriPB.slack posTerms
  congr 2
  induction pc.terms with
  | nil => rfl
  | cons t ts ih =>
    by_cases h0 : 0 < t.1
    · by_cases hf : falsified ρ t <;> simp [h0, hf, ih]
    · have : t.1 = 0 := by omega
      by_cases hf : falsified ρ t <;> simp [hf, ih, this]

/-- The trail falsifies the term on the code `ℓ` exactly when it holds `ℓ ^^^ 1`. -/
private theorem falsified_dec {vars trail : Array ℕ} (hv : vars.toList.Nodup)
    (ht : ∀ m ∈ trail, m < 2 * vars.size) {ℓ : ℕ} (hℓ : ℓ < 2 * vars.size) (k a : ℕ) :
    falsified (tlits vars trail k) (a, dec vars ℓ) = decide (ℓ ^^^ 1 ∈ trail.toList.take k) := by
  rw [falsified, ← dec_xor]
  have := dec_mem_tlits hv ht (xor_one_lt.2 hℓ) k
  by_cases h : ℓ ^^^ 1 ∈ trail.toList.take k
  · simp [this.2 h, h]
  · simp only [h, decide_false, Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    exact fun h' => h (this.1 h')

/-- A list of pairs, flattened. -/
private def flatL : List (ℕ × ℕ) → List ℕ
  | [] => []
  | p :: ps => p.1 :: p.2 :: flatL ps

/-! ### Assignments -/

private theorem AsgExt.refl (a : Asg) : AsgExt a a := ⟨List.prefix_refl _, fun _ _ => rfl⟩

private theorem AsgExt.trans {a b c : Asg} (h₁ : AsgExt a b) (h₂ : AsgExt b c) : AsgExt a c :=
  ⟨h₁.1.trans h₂.1, fun ℓ hℓ => by
    rw [h₂.2 ℓ (Array.mem_def.2 (h₁.1.subset (Array.mem_def.1 hℓ))), h₁.2 ℓ hℓ]⟩

private theorem AsgExt.size_le {a b : Asg} (h : AsgExt a b) : a.trail.size ≤ b.trail.size := by
  simpa using h.1.length_le

/-- The entries of a trail prefix are those of the extended trail. -/
private theorem ext_getElem {a b : Asg} (h : AsgExt a b) {k : ℕ} (hk : k < a.trail.size) :
    b.trail[k]'(Nat.lt_of_lt_of_le hk h.size_le) = a.trail[k] := by
  have := h.1.getElem (i := k) (by simpa using hk)
  simpa using this.symm

private theorem ext_getElem! {a b : Asg} (h : AsgExt a b) {k : ℕ} (hk : k < a.trail.size) :
    b.trail[k]! = a.trail[k]! := by
  rw [getElem!_pos b.trail k (Nat.lt_of_lt_of_le hk h.size_le), getElem!_pos a.trail k hk,
    ext_getElem h hk]

private theorem ext_tlits {vars : Array ℕ} {a b : Asg} (h : AsgExt a b) {k : ℕ}
    (hk : k ≤ a.trail.size) : tlits vars b.trail k = tlits vars a.trail k := by
  unfold tlits
  obtain ⟨t, ht⟩ := h.1
  rw [← ht, List.take_append_of_le_length (by simpa using hk)]

/-- Extending a chain by an assignment whose new entries are forced. -/
private theorem ChainFrom.ext {vars : Array ℕ} {G : ℕ → Option PBConstr} {m : ℕ} {a a' : Asg}
    (h : ChainFrom vars G m a) (he : AsgExt a a') (hn : ChainFrom vars G a.trail.size a') :
    ChainFrom vars G m a' := by
  intro k hk hm
  by_cases hka : k < a.trail.size
  · obtain ⟨pc, hG, hF⟩ := h k hka hm
    have hmem : a.trail[k] ∈ a.trail := Array.getElem_mem hka
    refine ⟨pc, ?_, ?_⟩
    · rw [ext_getElem he hka, he.2 _ hmem]; exact hG
    · rw [ext_getElem he hka, ext_tlits he (Nat.le_of_lt hka)]; exact hF
  · exact hn k hk (by omega)

private theorem ChainFrom.of_size (vars : Array ℕ) (G : ℕ → Option PBConstr) (a : Asg) :
    ChainFrom vars G a.trail.size a := fun _ hk hm => absurd hk (by omega)

/-- An unassigned code is neither true nor false on the trail. -/
private theorem AsgOk.not_mem_of_zero {vars : Array ℕ} {a : Asg} (h : AsgOk vars.size a)
    (hv : vars.toList.Nodup) {ℓ : ℕ} (hℓ : ℓ < 2 * vars.size) (h0 : a.value.get! ℓ = 0) :
    Std.Sat.Literal.negate (dec vars ℓ) ∉ tlits vars a.trail a.trail.size := by
  have hv0 := h.value_eq ℓ hℓ
  rw [h0] at hv0
  have hx : ℓ ^^^ 1 ∉ a.trail := fun hx => by
    simp only [hx, ite_true] at hv0; split at hv0 <;> simp at hv0
  rw [← dec_xor, dec_mem_tlits hv h.trail_lt (xor_one_lt.2 hℓ)]
  intro hm
  exact hx (Array.mem_def.2 (List.mem_of_mem_take hm))

private theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  simp only [getElem!_eq, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split_ifs <;> grind

/-- An unassigned code is not on the trail, nor is its negation. -/
private theorem zero {n : ℕ} {a : Asg} (h : AsgOk n a) {ℓ : ℕ} (hℓ : ℓ < 2 * n)
    (h0 : a.value.get! ℓ = 0) : ℓ ∉ a.trail ∧ ℓ ^^^ 1 ∉ a.trail := by
  have hv0 := h.value_eq ℓ hℓ
  rw [h0] at hv0
  by_cases h1 : ℓ ∈ a.trail
  · simp [h1] at hv0
  · by_cases h2 : ℓ ^^^ 1 ∈ a.trail
    · simp [h1, h2] at hv0
    · exact ⟨h1, h2⟩

/-- The variable of an unassigned code is not on the trail. -/
private theorem var_ne {n : ℕ} {a : Asg} (h : AsgOk n a) {ℓ : ℕ} (hℓ : ℓ < 2 * n)
    (h0 : a.value.get! ℓ = 0) {m : ℕ} (hm : m ∈ a.trail) : m / 2 ≠ ℓ / 2 := fun he => by
  obtain ⟨h1, h2⟩ := zero h hℓ h0
  rcases code_eq_or_xor he.symm with rfl | rfl
  · exact h1 hm
  · exact h2 hm

private theorem AsgOk.assign {n : ℕ} {a : Asg} (h : AsgOk n a) {ℓ r : ℕ} (hℓ : ℓ < 2 * n)
    (h0 : a.value.get! ℓ = 0) :
    AsgOk n (a.assign ℓ r) ∧ AsgExt a (a.assign ℓ r) ∧ (a.assign ℓ r).trail = a.trail.push ℓ ∧
      (a.assign ℓ r).reason[ℓ / 2]! = r := by
  obtain ⟨hz1, hz2⟩ := zero h hℓ h0
  have hne : ∀ m ∈ a.trail, m / 2 ≠ ℓ / 2 := fun m hm => var_ne h hℓ h0 hm
  have hx : ℓ ^^^ 1 < 2 * n := xor_one_lt.2 hℓ
  have hv2 : ℓ / 2 < n := by omega
  obtain ⟨value, reason, tpos, trail⟩ := a
  obtain ⟨hvs, hrs, hts, htl, hnd, hve, htp⟩ := h
  simp only at hvs hrs hts htl hnd hve htp hz1 hz2 hne h0
  simp only [Asg.assign]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, trivial, ?_⟩
  · simp [hvs]
  · simp [hrs]
  · simp [hts]
  · intro m hm
    rcases Array.mem_push.1 hm with hm | rfl
    · exact htl m hm
    · exact hℓ
  · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hnd, List.nodup_singleton _, ?_⟩
    intro x hx' y hy
    simp only [List.mem_singleton] at hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx'
    subst hy
    exact hne _ (Array.mem_def.2 hm)
  · intro m hm
    rw [ByteArray.get!_set!, ByteArray.get!_set!, ByteArray.size_set!, hvs]
    by_cases h1 : m = ℓ ^^^ 1
    · subst h1
      have : ℓ ^^^ 1 ∉ trail.push ℓ := by
        rw [Array.mem_push]; rintro (h' | h')
        · exact hz2 h'
        · exact xor_one_ne ℓ h'
      have h3 : ℓ ^^^ 1 ^^^ 1 ∈ trail.push ℓ := by rw [xor_one_xor_one]; exact Array.mem_push_self
      simp [hx, this, h3]
    · by_cases h2 : m = ℓ
      · rw [h2]
        simp [xor_one_ne ℓ, hℓ]
      · have e1 : (ℓ ^^^ 1 = m) = False := eq_false fun e => h1 e.symm
        have e2 : (ℓ = m) = False := eq_false fun e => h2 e.symm
        have e3 : (m ∈ trail.push ℓ) = (m ∈ trail) := by simp [Array.mem_push, h2]
        have e4 : (m ^^^ 1 ∈ trail.push ℓ) = (m ^^^ 1 ∈ trail) := by
          have : m ^^^ 1 ≠ ℓ := fun e => h1 (by rw [← e, xor_one_xor_one])
          simp [Array.mem_push, this]
        simp only [e1, e2, false_and, ite_false, e3, e4]
        exact hve m hm
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hk' : k < trail.size
    · rw [Array.getElem_push_lt hk', getElem!_set!]
      have : ℓ / 2 ≠ trail[k] / 2 := fun e => hne _ (Array.getElem_mem hk') e.symm
      simp only [this, false_and, ite_false]
      exact htp k hk'
    · have hk2 : k = trail.size := by omega
      subst hk2
      rw [Array.getElem_push_eq, getElem!_set!]
      simp [hts, hv2]
  · simp only [Array.toList_push]; exact List.prefix_append _ _
  · intro m hm
    rw [getElem!_set!]
    have : ℓ / 2 ≠ m / 2 := fun e => hne _ hm e.symm
    simp [this]
  · rw [getElem!_set!]; simp [hrs, hv2]

private theorem AsgOk.assign_chain {vars : Array ℕ} {G : ℕ → Option PBConstr} {a : Asg}
    (h : AsgOk vars.size a) {ℓ r : ℕ} (hℓ : ℓ < 2 * vars.size) (h0 : a.value.get! ℓ = 0)
    {pc : PBConstr} (hG : G r = some pc)
    (hF : Forces (tlits vars a.trail a.trail.size) pc (dec vars ℓ)) :
    ChainFrom vars G a.trail.size (a.assign ℓ r) := by
  obtain ⟨-, -, ht, hr⟩ := h.assign (r := r) hℓ h0
  intro k hk hm
  have hk2 : k = a.trail.size := by
    have := hk; simp only [ht, Array.size_push] at this; omega
  subst hk2
  have hget : (a.assign ℓ r).trail[a.trail.size] = ℓ := by simp [ht]
  have htl : tlits vars (a.assign ℓ r).trail a.trail.size = tlits vars a.trail a.trail.size := by
    simp [tlits, ht]
  refine ⟨pc, ?_, ?_⟩
  · simp only [hget, hr]; exact hG
  · simp only [hget, htl]; exact hF

/-! ### Propagation -/

private theorem mem_stored_of_range {lits coeffs : Array ℕ} {r : CRec} {k : ℕ} (h1 : r.start ≤ k)
    (h2 : k < r.start + r.size) :
    (coeffs[k]!, lits[k]!) ∈ stored lits coeffs r ∧ lits[k]! ∈ scodes lits r := by
  have e : r.start + (k - r.start) = k := by omega
  refine ⟨?_, ?_⟩
  · simp only [stored, List.mem_map, List.mem_range]; exact ⟨k - r.start, by omega, by rw [e]⟩
  · simp only [scodes, List.mem_map, List.mem_range]; exact ⟨k - r.start, by omega, by rw [e]⟩

/-- A stored term of a constraint propagating through its slack is a term of the constraint. -/
private theorem term_mem {vars lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr}
    (hrep : Rep vars lits coeffs r pc) (hcl : r.clause = false) {k : ℕ} (h1 : r.start ≤ k)
    (h2 : k < r.start + r.size) :
    (coeffs[k]!, dec vars lits[k]!) ∈ pc.terms ∧ lits[k]! < 2 * vars.size := by
  obtain ⟨hm, hs⟩ := mem_stored_of_range (lits := lits) (coeffs := coeffs) h1 h2
  refine ⟨?_, hrep.lt _ hs⟩
  have : (coeffs[k]!, dec vars lits[k]!) ∈ posTerms pc :=
    (hrep.terms hcl).mem_iff.1 (List.mem_map.2 ⟨_, hm, rfl⟩)
  exact List.mem_of_mem_filter this

private theorem tlits_sub {vars t : Array ℕ} {k k' : ℕ} (h : k ≤ k') {l : Literal ℕ}
    (hl : l ∈ tlits vars t k) : l ∈ tlits vars t k' := by
  unfold tlits at *
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
  refine List.mem_map.2 ⟨m, ?_, rfl⟩
  have : List.take k t.toList = List.take k (List.take k' t.toList) := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this] at hm; exact List.mem_of_mem_take hm

/-- The literals of a trail are among those of an extension. -/
private theorem tlits_ext_sub {vars : Array ℕ} {a b : Asg} (h : AsgExt a b) {l : Literal ℕ}
    (hl : l ∈ tlits vars a.trail a.trail.size) : l ∈ tlits vars b.trail b.trail.size := by
  rw [← ext_tlits h (le_refl _)] at hl
  exact tlits_sub h.size_le hl

/-- The slack falls along an extension. -/
private theorem slack_ext {vars : Array ℕ} {a b : Asg} (h : AsgExt a b) (pc : PBConstr) :
    VeriPB.slack (tlits vars b.trail b.trail.size) pc ≤
      VeriPB.slack (tlits vars a.trail a.trail.size) pc :=
  slack_anti (fun _ hl => tlits_ext_sub h hl) pc

private theorem go {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {lits coeffs : Array ℕ} {c : ℕ} {sl : ℤ} {pc : PBConstr}
    (hv : vars.toList.Nodup) (hrep : Rep vars lits coeffs cons[c]! pc)
    (hcl : cons[c]!.clause = false) (hG : G c = some pc) :
    ∀ n k (a : Asg), cons[c]!.start + cons[c]!.size - k = n → cons[c]!.start ≤ k →
      AsgOk vars.size a → VeriPB.slack (tlits vars a.trail a.trail.size) pc ≤ sl →
      AsgOk vars.size (propagatePB.go lits coeffs c sl (cons[c]!.start + cons[c]!.size) k a) ∧
      AsgExt a (propagatePB.go lits coeffs c sl (cons[c]!.start + cons[c]!.size) k a) ∧
      ChainFrom vars G a.trail.size
        (propagatePB.go lits coeffs c sl (cons[c]!.start + cons[c]!.size) k a) := by
  intro n
  induction n with
  | zero =>
    intro k a hn hk ha _
    rw [propagatePB.go]
    split
    · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · exact ⟨ha, AsgExt.refl a, ChainFrom.of_size vars G a⟩
  | succ n ih =>
    intro k a hn hk ha hsl
    rw [propagatePB.go]
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hke, hcoef⟩ := h
      obtain ⟨hmem, hlt⟩ := term_mem hrep hcl hk hke
      -- One step.
      have step : ∃ a1 : Asg, (if (litVal a.value lits[k]! == 0) = true then a.assign lits[k]! c
          else a) = a1 ∧ AsgOk vars.size a1 ∧ AsgExt a a1 ∧ ChainFrom vars G a.trail.size a1 := by
        by_cases hz : a.value.get! lits[k]! = 0
        · have hz' : (litVal a.value lits[k]! == 0) = true := by simp [litVal, hz]
          simp only [hz', ↓reduceIte]
          obtain ⟨h1, h2, -, -⟩ := ha.assign (r := c) hlt hz
          refine ⟨_, rfl, h1, h2, ha.assign_chain hlt hz hG ⟨ha.not_mem_of_zero hv hlt hz, _,
            hmem, by omega⟩⟩
        · have hz' : (litVal a.value lits[k]! == 0) = false := by simp [litVal, hz]
          simp only [hz', Bool.false_eq_true, ↓reduceIte]
          exact ⟨a, rfl, ha, AsgExt.refl a, ChainFrom.of_size vars G a⟩
      obtain ⟨a1, e1, ha1, he1, hc1⟩ := step
      dsimp only
      rw [e1]
      have hsl1 : VeriPB.slack (tlits vars a1.trail a1.trail.size) pc ≤ sl :=
        le_trans (slack_ext he1 pc) hsl
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) a1 (by omega) (by omega) ha1 hsl1
      exact ⟨h1, he1.trans h2, hc1.ext h2 h3⟩
    · exact ⟨ha, AsgExt.refl a, ChainFrom.of_size vars G a⟩

private theorem propagatePB_spec {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {lits coeffs : Array ℕ} {c : ℕ} {sl : ℤ} {a : Asg} {pc : PBConstr}
    (hv : vars.toList.Nodup) (ha : AsgOk vars.size a)
    (hrep : Rep vars lits coeffs cons[c]! pc) (hcl : cons[c]!.clause = false)
    (hG : G c = some pc) (hsl : VeriPB.slack (tlits vars a.trail a.trail.size) pc ≤ sl) :
    let a' := Elab.propagatePB cons lits coeffs c sl a
    AsgOk vars.size a' ∧ AsgExt a a' ∧ ChainFrom vars G a.trail.size a' := by
  simp only [Elab.propagatePB]
  exact go hv hrep hcl hG _ _ a rfl (le_refl _) ha hsl

private theorem pairsL_drop (l : List ℕ) (i : ℕ) (h : i + 1 < l.length) :
    pairsL (l.drop i) = (l[i], l[i + 1]) :: pairsL (l.drop (i + 2)) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h]
  rfl

private theorem pairsL_drop_nil (l : List ℕ) (i : ℕ) (h : ¬ i + 1 < l.length) :
    pairsL (l.drop i) = [] := by
  have hl : (l.drop i).length ≤ 1 := by simp; omega
  rcases hd : l.drop i with _ | ⟨x, _ | ⟨y, r⟩⟩
  · rfl
  · rfl
  · rw [hd] at hl; simp at hl

private theorem flatL_append (A B : List (ℕ × ℕ)) : flatL (A ++ B) = flatL A ++ flatL B := by
  induction A with
  | nil => rfl
  | cons p A ih => simp [flatL, ih]

/-- The total of the second components of the pairs naming `c`. -/
private def psum (c : ℕ) (P : List (ℕ × ℕ)) : ℕ := ((P.filter (·.1 == c)).map (·.2)).sum

private theorem psum_append (c : ℕ) (A B : List (ℕ × ℕ)) :
    psum c (A ++ B) = psum c A + psum c B := by
  simp [psum, List.filter_append]

private theorem psum_single (c : ℕ) (p : ℕ × ℕ) :
    psum c [p] = if p.1 = c then p.2 else 0 := by
  by_cases h : p.1 = c <;> simp [psum, h]

/-- Dropping the terms with a zero coefficient changes no sum of coefficients. -/
private theorem sum_posTerms (ts : List (ℕ × Literal ℕ)) (p : ℕ × Literal ℕ → Bool) :
    ((ts.filter p).map (·.1)).sum = (((ts.filter (0 < ·.1)).filter p).map (·.1)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    by_cases h0 : 0 < t.1
    · by_cases hp : p t <;> simp [h0, hp, ih]
    · have : t.1 = 0 := by omega
      by_cases hp : p t <;> simp [hp, ih, this]

/-- The trail entry at `q` is not among the entries before it. -/
private theorem not_mem_take {n : ℕ} {a : Asg} (h : AsgOk n a) {q : ℕ}
    (hq : q < a.trail.size) : a.trail[q] ∉ a.trail.toList.take q := by
  have hnd : a.trail.toList.Nodup := List.Nodup.of_map _ h.nodup
  rw [← List.take_append_drop q a.trail.toList] at hnd
  have hd := List.nodup_append.1 hnd
  intro hm
  have hm2 : a.trail[q] ∈ a.trail.toList.drop q := by
    rw [List.drop_eq_getElem_cons (by simpa using hq)]; simp
  exact hd.2.2 _ hm _ hm2 rfl

/-- Processing the trail entry at `q` lowers the slack by the coefficients of the terms on the
negation of its literal. -/
private theorem slack_succ {vars lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr} {a : Asg}
    {q : ℕ} (hv : vars.toList.Nodup) (ha : AsgOk vars.size a) (hq : q < a.trail.size)
    (hrep : Rep vars lits coeffs r pc) (hcl : r.clause = false) :
    VeriPB.slack (tlits vars a.trail (q + 1)) pc = VeriPB.slack (tlits vars a.trail q) pc -
      (((stored lits coeffs r).filter (·.2 == a.trail[q]! ^^^ 1)).map (·.1)).sum := by
  have hq' : q < a.trail.toList.length := by simpa using hq
  have htl : tlits vars a.trail (q + 1) = tlits vars a.trail q ++ [dec vars a.trail[q]] := by
    simp [tlits, List.take_add_one, List.getElem?_eq_getElem hq']
  have htq : a.trail[q] < 2 * vars.size := ha.trail_lt _ (Array.getElem_mem hq)
  have hm : dec vars a.trail[q] ∉ tlits vars a.trail q := by
    rw [dec_mem_tlits hv ha.trail_lt htq]; exact not_mem_take ha hq
  rw [htl, slack_append_singleton hm]
  congr 2
  rw [sum_posTerms]
  change (((posTerms pc).filter _).map _).sum = _
  have hp := (hrep.terms hcl).symm
  rw [((hp.filter _).map _).sum_nat, List.filter_map, List.map_map]
  have hf : a.trail[q]! ^^^ 1 < 2 * vars.size := by
    rw [getElem!_pos a.trail q hq]; exact xor_one_lt.2 htq
  congr 2
  refine List.filter_congr fun p hp' => ?_
  have hp2 : p.2 < 2 * vars.size := by
    refine hrep.lt _ ?_
    simp only [stored, List.mem_map, List.mem_range] at hp'
    obtain ⟨k, hk, rfl⟩ := hp'
    simp only [scodes, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩
  have hL : Std.Sat.Literal.negate (dec vars a.trail[q]) = dec vars (a.trail[q]! ^^^ 1) := by
    rw [dec_xor, getElem!_pos a.trail q hq]
  simp only [Function.comp, hL, beq_eq_beq]
  exact ⟨dec_inj hv hp2 hf, fun h => by rw [h]⟩

private theorem take_set_set (os : Array ℕ) (j c w : ℕ) (hj : j + 1 < os.size) :
    ((os.set! j c).set! (j + 1) w).toList.take (j + 2) = os.toList.take j ++ [c, w] := by
  apply List.ext_getElem
  · simp; omega
  · intro t h1 h2
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.getElem_take,
      List.getElem_set]
    have hlen : (os.toList.take j).length = j := by simp; omega
    simp only [List.length_take, Array.length_toList] at h1
    rcases Nat.lt_trichotomy t j with h | rfl | h
    · rw [List.getElem_append_left (by omega)]
      simp only [show ¬ (j + 1 = t) by omega, show ¬ (j = t) by omega, ↓reduceIte,
        List.getElem_take]
    · rw [List.getElem_append_right (by omega)]
      simp [hlen]
    · have ht : t = j + 1 := by omega
      subst ht
      rw [List.getElem_append_right (by omega)]
      simp [hlen]

private theorem pbLoop_inv {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {alive : ByteArray} {lits coeffs : Array ℕ} {watches : Array (Array ℕ)} {os0 : Array ℕ}
    {a0 : Asg} {q : ℕ}
    (hv : vars.toList.Nodup)
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hrep : ∀ c pc, G c = some pc → Rep vars lits coeffs cons[c]! pc)
    (hname : ∀ p ∈ pairsL os0.toList, p.1 < cons.size ∧
      (alive.get! p.1 ≠ 0 → reg cons[p.1]! = true))
    (hq : q < a0.trail.size)
    (hW : ∀ c pc, G c = some pc → reg cons[c]! = true →
      VeriPB.slack (tlits vars a0.trail (q + 1)) pc =
        VeriPB.slack (tlits vars a0.trail q) pc - wsum c os0) :
    ∀ n i j (os : Array ℕ) (confl : Option ℕ) (slack : Array ℤ) (a : Asg) (P : List (ℕ × ℕ)),
    os.size - i = n → os.size = os0.size → (∀ t, i ≤ t → os[t]! = os0[t]!) →
    P ++ pairsL (os0.toList.drop i) = pairsL os0.toList → j ≤ i →
    os.toList.take j = flatL (P.filter fun p => alive.get! p.1 != 0) →
    slack.size = cons.size →
    (∀ c pc, G c = some pc → reg cons[c]! = true →
      slack[c]! + psum c P = VeriPB.slack (tlits vars a0.trail q) pc) →
    AsgOk vars.size a → AsgExt a0 a → ChainFrom vars G a0.trail.size a →
    (∀ k, confl = some k →
      ∃ pc, G k = some pc ∧ VeriPB.slack (tlits vars a.trail a.trail.size) pc < 0) →
    let h := pbLoop cons alive lits coeffs watches os i j confl slack a.value a.reason a.tpos
      a.trail
    let a' : Asg := ⟨h.value, h.reason, h.tpos, h.trail⟩
    h.lits = lits ∧ h.watches = watches ∧
    h.arr.toList = flatL ((pairsL os0.toList).filter fun p => alive.get! p.1 != 0) ∧
    h.slack.size = cons.size ∧
    (∀ c pc, G c = some pc → reg cons[c]! = true →
      h.slack[c]! = VeriPB.slack (tlits vars a0.trail (q + 1)) pc) ∧
    AsgOk vars.size a' ∧ AsgExt a0 a' ∧ ChainFrom vars G a0.trail.size a' ∧
    ∀ k, h.confl = some k →
      ∃ pc, G k = some pc ∧ VeriPB.slack (tlits vars a'.trail a'.trail.size) pc < 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j os confl slack a P hn hsz hun hP hji htake hss hsl ha he hch hcf
  dsimp only
  rw [pbLoop]
  by_cases hlt : i + 1 < os.size
  · simp only [hlt, ↓reduceIte]
    have hlt0 : i + 1 < os0.toList.length := by simpa [← hsz] using hlt
    have hd := pairsL_drop os0.toList i hlt0
    have hci : os[i]! = os0.toList[i] := by
      rw [hun i (le_refl _), getElem!_pos os0 i (by simp at hlt0; omega)]; simp
    have hwi : os[i + 1]! = os0.toList[i + 1] := by
      rw [hun (i + 1) (by omega), getElem!_pos os0 (i + 1) (by simpa using hlt0)]; simp
    have hP' : (P ++ [(os[i]!, os[i + 1]!)]) ++ pairsL (os0.toList.drop (i + 2)) =
        pairsL os0.toList := by rw [hci, hwi, List.append_assoc, List.singleton_append, ← hd, hP]
    have hmem : (os[i]!, os[i + 1]!) ∈ pairsL os0.toList := by
      rw [← hP']; simp
    obtain ⟨hcs, hcreg⟩ := hname _ hmem
    simp only at hcs hcreg
    -- The processed pairs are a prefix.
    have hle : ∀ c, psum c (P ++ [(os[i]!, os[i + 1]!)]) ≤ wsum c os0 := fun c => by
      have : wsum c os0 = psum c (pairsL os0.toList) := rfl
      rw [this, ← hP', psum_append c _ (pairsL _)]; omega
    by_cases hd0 : alive.get! os[i]! = 0
    · -- A dead constraint: skipped.
      simp only [hd0, beq_self_eq_true, ↓reduceIte]
      refine ih _ (by omega) (i + 2) j os confl slack a _ rfl hsz
        (fun t ht => hun t (by omega)) hP' (by omega) ?_ hss ?_ ha he hch hcf
      · rw [htake, List.filter_append]; simp [hd0]
      · intro c pc hG hr
        have hne : os[i]! ≠ c := fun e => by
          have := ((hlive c).1 (by simp [hG])).2; rw [← e] at this; exact this hd0
        rw [psum_append, psum_single]; simp only [hne, ↓reduceIte, Nat.add_zero]
        exact hsl c pc hG hr
    · have hb : (alive.get! os[i]! == 0) = false := by simpa using hd0
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨pc, hGc⟩ := Option.isSome_iff_exists.1 ((hlive _).2 ⟨hcs, hd0⟩)
      have hreg := hcreg hd0
      have hcl : cons[os[i]!]!.clause = false := by
        simp only [reg, Bool.and_eq_true, Bool.not_eq_true'] at hreg; exact hreg.1
      have hj1 : j + 1 < os.size := by omega
      -- The new slack of the constraint bounds its true slack from above.
      have hbound : VeriPB.slack (tlits vars a.trail a.trail.size) pc ≤
          slack[os[i]!]! - (os[i + 1]! : ℤ) := by
        have h1 := hsl _ pc hGc hreg
        have h2 := hW _ pc hGc hreg
        have h3 : psum os[i]! P + os[i + 1]! ≤ wsum os[i]! os0 := by
          have := hle os[i]!
          rw [psum_append, psum_single] at this
          simpa using this
        have h4 : VeriPB.slack (tlits vars a.trail a.trail.size) pc ≤
            VeriPB.slack (tlits vars a0.trail (q + 1)) pc := by
          rw [← ext_tlits he (by omega)]
          exact slack_anti (fun _ hl => tlits_sub (by have := he.size_le; omega) hl) pc
        omega
      have hos : ∀ t, i + 2 ≤ t → ((os.set! j os[i]!).set! (j + 1) os[i + 1]!)[t]! = os0[t]! :=
        fun t ht => by
          rw [getElem!_set!, getElem!_set!]
          have e1 : ¬ (j + 1 = t) := by omega
          have e2 : ¬ (j = t) := by omega
          simp only [e1, e2, false_and, ↓reduceIte]
          exact hun t (by omega)
      have hsz' : ((os.set! j os[i]!).set! (j + 1) os[i + 1]!).size = os0.size := by
        simp [hsz]
      have htake' : ((os.set! j os[i]!).set! (j + 1) os[i + 1]!).toList.take (j + 2) =
          flatL ((P ++ [(os[i]!, os[i + 1]!)]).filter fun p => alive.get! p.1 != 0) := by
        rw [take_set_set os j _ _ hj1, htake, List.filter_append, flatL_append]
        simp [hd0, flatL]
      have hss' : (slack.set! os[i]! (slack[os[i]!]! - (os[i + 1]! : ℤ))).size = cons.size := by
        simp [hss]
      have hsl' : ∀ c pc', G c = some pc' → reg cons[c]! = true →
          (slack.set! os[i]! (slack[os[i]!]! - (os[i + 1]! : ℤ)))[c]! +
            psum c (P ++ [(os[i]!, os[i + 1]!)]) = VeriPB.slack (tlits vars a0.trail q) pc' := by
        intro c pc' hG hr
        rw [getElem!_set!, psum_append, psum_single]
        by_cases hc : os[i]! = c
        · subst hc
          rw [hGc] at hG; cases hG
          have := hsl _ pc hGc hr
          have hlt' : os[i]! < slack.size := hss ▸ hcs
          simp only [hlt', and_self, ↓reduceIte]
          push_cast; omega
        · simp only [hc, false_and, ↓reduceIte, Nat.add_zero]
          exact hsl c pc' hG hr
      by_cases hcn : confl = none
      · subst hcn
        by_cases hneg : slack[os[i]!]! - (os[i + 1]! : ℤ) < 0
        · -- A new conflict.
          simp only [Option.isNone_none, hneg, decide_true, Bool.and_self, ↓reduceIte]
          refine ih _ (by omega) (i + 2) (j + 2) _ _ _ a _ rfl hsz' hos hP' (by omega) htake'
            hss' hsl' ha he hch ?_
          intro k hk; cases hk
          exact ⟨pc, hGc, by omega⟩
        · -- Propagation.
          simp only [Option.isNone_none, hneg, decide_false, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte]
          obtain ⟨h1, h2, h3⟩ := propagatePB_spec (G := G) hv ha (hrep _ pc hGc) hcl hGc hbound
          have hae : (⟨a.value, a.reason, a.tpos, a.trail⟩ : Asg) = a := rfl
          rw [hae]
          generalize Elab.propagatePB cons lits coeffs os[i]! (slack[os[i]!]! - ↑os[i + 1]!) a
            = a1 at h1 h2 h3
          obtain ⟨v1, r1, t1, tr1⟩ := a1
          exact ih _ (by omega) (i + 2) (j + 2) _ _ _ ⟨v1, r1, t1, tr1⟩ _ rfl hsz' hos hP'
            (by omega) htake' hss' hsl' h1 (he.trans h2) (hch.ext h2 h3) (fun _ h => by cases h)
      · obtain ⟨k0, hk0⟩ := Option.ne_none_iff_exists'.1 hcn
        subst hk0
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact ih _ (by omega) (i + 2) (j + 2) _ _ _ a _ rfl hsz' hos hP' (by omega) htake'
          hss' hsl' ha he hch hcf
  · simp only [hlt, ↓reduceIte]
    have hnil := pairsL_drop_nil os0.toList i (by simpa [← hsz] using hlt)
    rw [hnil, List.append_nil] at hP
    subst hP
    refine ⟨trivial, trivial, ?_, hss, ?_, ha, he, hch, hcf⟩
    · simp only [Array.toList_shrink]; exact htake
    · intro c pc hG hr
      have h1 := hsl c pc hG hr
      rw [hW c pc hG hr]
      have : psum c (pairsL os0.toList) = wsum c os0 := rfl
      rw [this] at h1; omega

private theorem pbLoop_spec {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {alive : ByteArray} {lits coeffs : Array ℕ} {watches : Array (Array ℕ)} {os : Array ℕ}
    {slack : Array ℤ} {a : Asg} {q : ℕ}
    (hv : vars.toList.Nodup) (ha : AsgOk vars.size a)
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hrep : ∀ c pc, G c = some pc → Rep vars lits coeffs cons[c]! pc)
    (hname : ∀ p ∈ pairsL os.toList, p.1 < cons.size ∧
      (alive.get! p.1 ≠ 0 → reg cons[p.1]! = true))
    (heven : os.size % 2 = 0) (hq : q < a.trail.size)
    (hexact : ∀ c pc, G c = some pc → reg cons[c]! = true →
      wsum c os = (((stored lits coeffs cons[c]!).filter (·.2 == a.trail[q]! ^^^ 1)).map (·.1)).sum)
    (hslack : ∀ c pc, G c = some pc → reg cons[c]! = true →
      slack[c]! = VeriPB.slack (tlits vars a.trail q) pc)
    (hsize : slack.size = cons.size) :
    let h := pbLoop cons alive lits coeffs watches os 0 0 none slack a.value a.reason a.tpos a.trail
    let a' : Asg := ⟨h.value, h.reason, h.tpos, h.trail⟩
    h.lits = lits ∧ h.watches = watches ∧
    h.arr.toList = flatL ((pairsL os.toList).filter fun p => alive.get! p.1 != 0) ∧
    h.slack.size = slack.size ∧
    (∀ c pc, G c = some pc → reg cons[c]! = true →
      h.slack[c]! = VeriPB.slack (tlits vars a.trail (q + 1)) pc) ∧
    AsgOk vars.size a' ∧ AsgExt a a' ∧ ChainFrom vars G a.trail.size a' ∧
    ∀ k, h.confl = some k →
      ∃ pc, G k = some pc ∧ VeriPB.slack (tlits vars a'.trail a'.trail.size) pc < 0 := by
  have _hev := heven
  have hW : ∀ c pc, G c = some pc → reg cons[c]! = true →
      VeriPB.slack (tlits vars a.trail (q + 1)) pc =
        VeriPB.slack (tlits vars a.trail q) pc - wsum c os := by
    intro c pc hG hr
    have hcl : cons[c]!.clause = false := by
      simp only [reg, Bool.and_eq_true, Bool.not_eq_true'] at hr; exact hr.1
    rw [slack_succ hv ha hq (hrep c pc hG) hcl, hexact c pc hG hr]
  have := pbLoop_inv (watches := watches) hv hlive hrep hname hq hW _ 0 0 os none slack a [] rfl
    rfl (fun _ _ => rfl) (by simp) (le_refl _) (by simp [flatL]) hsize
    (fun c pc hG hr => by simp [psum, hslack c pc hG hr]) ha (AsgExt.refl a)
    (ChainFrom.of_size vars G a) (fun _ h => by cases h)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := this
  exact ⟨h1, h2, h3, by rw [h4, hsize], h5, h6, h7, h8, h9⟩

/-! #### The clause loop -/

private theorem take_set {l : List ℕ} {j : ℕ} (hj : j < l.length) (c : ℕ) :
    (l.set j c).take (j + 1) = l.take j ++ [c] := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_set, List.getElem?_append, List.length_take]
  grind

private theorem drop_set {l : List ℕ} {i j : ℕ} (hj : j < i + 1) (c : ℕ) :
    (l.set j c).drop (i + 1) = l.drop (i + 1) := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_drop, List.getElem?_set]
  grind

private theorem keepLive_toList (alive : ByteArray) :
    ∀ (n : ℕ) (ws : Array ℕ) (i j : ℕ), ws.size - i = n → j ≤ i →
      (keepLive alive ws i j).toList =
        ws.toList.take j ++ (ws.toList.drop i).filter (fun c => alive.get! c != 0)
  | 0, ws, i, j, hn, hji => by
    rw [keepLive]
    have : ¬ i < ws.size := by omega
    simp only [this, ↓reduceIte, Array.toList_shrink]
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | n + 1, ws, i, j, hn, hji => by
    rw [keepLive]
    have hi : i < ws.size := by omega
    have hd : ws.toList.drop i = ws[i] :: ws.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (by simp; omega)
    simp only [hi, ↓reduceIte, getElem!_pos ws i hi]
    split
    · rename_i h0
      have h0' : alive.get! ws[i] = 0 := by simpa using h0
      rw [keepLive_toList alive n ws (i + 1) j (by omega) (by omega), hd]
      simp [h0']
    · rename_i h0
      have h0' : alive.get! ws[i] ≠ 0 := by simpa using h0
      rw [keepLive_toList alive n _ (i + 1) (j + 1) (by simp; omega) (by omega)]
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
      rw [take_set (by simp; omega), drop_set (by omega), hd]
      simp [h0']

/-- `nonFalse` returns the first non-false position from `k`, or `e`. -/
private theorem nonFalse_spec (lits : Array ℕ) (value : ByteArray) :
    ∀ (n k e : ℕ), e - k = n → k ≤ e →
      k ≤ nonFalse lits value k e ∧ nonFalse lits value k e ≤ e ∧
      (nonFalse lits value k e < e → litVal value lits[nonFalse lits value k e]! ≠ 2) ∧
      ∀ q, k ≤ q → q < nonFalse lits value k e → litVal value lits[q]! = 2
  | 0, k, e, hn, hk => by
    have : k = e := by omega
    subst this
    rw [nonFalse]; simp only [lt_irrefl, ↓reduceIte]
    exact ⟨le_rfl, le_rfl, fun h => h.elim, fun q h1 h2 => by omega⟩
  | n + 1, k, e, hn, hk => by
    rw [nonFalse]
    have hke : k < e := by omega
    simp only [hke, ↓reduceIte]
    split
    · rename_i h
      refine ⟨le_rfl, by omega, fun _ => by simpa using h, fun q h1 h2 => by omega⟩
    · rename_i h
      obtain ⟨h1, h2, h3, h4⟩ := nonFalse_spec lits value n (k + 1) e (by omega) (by omega)
      refine ⟨by omega, h2, h3, fun q hq1 hq2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hq1 with rfl | hq
      · simpa using h
      · exact h4 q hq hq2

private theorem perm_swap_map (g : ℕ → ℕ) {n x y : ℕ} (hx : x < n) (hy : y < n) :
    ((List.range n).map fun k => g (if k = x then y else if k = y then x else k)).Perm
      ((List.range n).map g) := by
  have hτ : ((List.range n).map fun k => if k = x then y else if k = y then x else k).Perm
      (List.range n) := by
    rw [List.perm_ext_iff_of_nodup ?_ List.nodup_range]
    · intro a
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨k, hk, rfl⟩; grind
      · intro ha
        exact ⟨if a = x then y else if a = y then x else a, by grind, by grind⟩
    · exact List.pairwise_map.2 (List.Pairwise.imp (fun {a b} h => by grind) List.nodup_range)
  have := hτ.map g
  simpa [List.map_map, Function.comp_def] using this

private theorem get_swap (lits : Array ℕ) {x y : ℕ} (hx : x < lits.size) (hy : y < lits.size)
    (q : ℕ) : (lits.swapIfInBounds x y)[q]! =
      if q = x then lits[y]! else if q = y then lits[x]! else lits[q]! := by
  simp only [getElem!_eq, getElem?_swapIfInBounds, hx, hy, and_self, ↓reduceIte]
  split_ifs <;> rfl

/-- A swap inside the range of a record permutes its codes. -/
private theorem scodes_swap {lits : Array ℕ} {r : CRec} {x y : ℕ} (hx : x < r.size)
    (hy : y < r.size) (hr : r.start + r.size ≤ lits.size) :
    (scodes (lits.swapIfInBounds (r.start + x) (r.start + y)) r).Perm (scodes lits r) := by
  have : scodes (lits.swapIfInBounds (r.start + x) (r.start + y)) r =
      (List.range r.size).map fun k =>
        (fun k => lits[r.start + k]!) (if k = x then y else if k = y then x else k) := by
    unfold scodes
    refine List.map_congr_left fun k hk => ?_
    simp only [List.mem_range] at hk
    rw [get_swap lits (by omega) (by omega)]
    by_cases h1 : k = x
    · subst h1; simp
    · by_cases h2 : k = y
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [this]
  exact perm_swap_map (fun k => lits[r.start + k]!) hx hy

/-- A swap outside the range of a record changes none of its terms. -/
private theorem swap_out {lits coeffs : Array ℕ} {r : CRec} {x y : ℕ} (hx : x < lits.size)
    (hy : y < lits.size) (hxr : x < r.start ∨ r.start + r.size ≤ x)
    (hyr : y < r.start ∨ r.start + r.size ≤ y) :
    scodes (lits.swapIfInBounds x y) r = scodes lits r ∧
      stored (lits.swapIfInBounds x y) coeffs r = stored lits coeffs r := by
  constructor
  · unfold scodes
    refine List.map_congr_left fun k hk => ?_
    simp only [List.mem_range] at hk
    rw [get_swap lits hx hy]
    simp only [show r.start + k ≠ x by omega, show r.start + k ≠ y by omega, ↓reduceIte]
  · unfold stored
    refine List.map_congr_left fun k hk => ?_
    simp only [List.mem_range] at hk
    rw [get_swap lits hx hy]
    simp only [show r.start + k ≠ x by omega, show r.start + k ≠ y by omega, ↓reduceIte]

/-- Ranges of later records start after the end of earlier ones. -/
private theorem range_le {cons : Array CRec} {cpos : Array ℕ} {n : ℕ}
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else n)
    {c : ℕ} (h1 : 1 ≤ c) : ∀ c', c < c' → c' < cons.size →
      cons[c]!.start + cons[c]!.size ≤ cons[c']!.start := by
  intro c' hlt hc'
  induction c' with
  | zero => omega
  | succ m ih =>
    have hm := (hlay m (by omega) (by omega)).2
    have hm1 := (hlay (m + 1) (by omega) hc').1
    simp only [show m + 1 < cons.size from hc', ↓reduceIte] at hm
    rcases Nat.lt_or_ge c m with h | h
    · have := ih h (by omega)
      have := (hlay m (by omega) (by omega)).2
      simp only [show m + 1 < cons.size from hc', ↓reduceIte] at this
      omega
    · have : c = m := by omega
      subst this; omega

/-- Every record ends within the term arrays. -/
private theorem range_end {cons : Array CRec} {cpos : Array ℕ} {n : ℕ}
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else n) :
    ∀ (d c : ℕ), cons.size - c = d → 1 ≤ c → c < cons.size →
      cons[c]!.start + cons[c]!.size ≤ n
  | 0, c, hd, _, hc => by omega
  | d + 1, c, hd, h1, hc => by
    have := (hlay c h1 hc).2
    by_cases h : c + 1 < cons.size
    · simp only [h, ↓reduceIte] at this
      have h2 := (hlay (c + 1) (by omega) h).1
      have := range_end hlay d (c + 1) (by omega) (by omega) h
      omega
    · simp only [h, ↓reduceIte] at this; omega

/-- On a well-formed assignment, the full trail falsifies a code's term exactly when the code is
false. -/
private theorem falsified_iff {vars : Array ℕ} {a : Asg} (hv : vars.toList.Nodup)
    (ha : AsgOk vars.size a) {ℓ : ℕ} (hℓ : ℓ < 2 * vars.size) (x : ℕ) :
    falsified (tlits vars a.trail a.trail.size) (x, dec vars ℓ) = decide (a.value.get! ℓ = 2) := by
  rw [falsified_dec hv ha.trail_lt hℓ, ha.value_eq ℓ hℓ]
  have htake : a.trail.toList.take a.trail.size = a.trail.toList := by simp
  rw [htake]
  by_cases h1 : ℓ ∈ a.trail
  · have h2 : ℓ ^^^ 1 ∉ a.trail.toList := fun h2 => by
      have hm1 : ℓ ∈ a.trail.toList := by simpa using h1
      have := List.inj_on_of_nodup_map ha.nodup hm1 h2 (by simp [xor_one_div_two])
      exact xor_one_ne ℓ this.symm
    simp [h1, h2]
  · by_cases h2 : ℓ ^^^ 1 ∈ a.trail <;> simp [h1, h2]

/-- The unfalsified terms of a represented constraint are those of its non-false codes. -/
private theorem filter_perm_value {vars lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr} {a : Asg}
    (hv : vars.toList.Nodup) (ha : AsgOk vars.size a) (hrep : Rep vars lits coeffs r pc) :
    (((posTerms pc).filter fun t => !falsified (tlits vars a.trail a.trail.size) t).map (·.2)).Perm
      (((scodes lits r).filter fun ℓ => a.value.get! ℓ != 2).map (dec vars)) := by
  have h1 : ((posTerms pc).filter fun t =>
      !falsified (tlits vars a.trail a.trail.size) t).map (·.2) =
      ((posTerms pc).map (·.2)).filter fun L =>
        !(tlits vars a.trail a.trail.size).contains (Std.Sat.Literal.negate L) := by
    rw [List.filter_map]; rfl
  have h2 : ((scodes lits r).filter fun ℓ => a.value.get! ℓ != 2).map (dec vars) =
      ((scodes lits r).map (dec vars)).filter fun L =>
        !(tlits vars a.trail a.trail.size).contains (Std.Sat.Literal.negate L) := by
    rw [List.filter_map]
    congr 1
    refine List.filter_congr fun ℓ hℓ => ?_
    have := falsified_iff hv ha (hrep.lt ℓ hℓ) 0
    simp only [falsified] at this
    have this' : Std.Sat.Literal.negate (dec vars ℓ) ∈ tlits vars a.trail a.trail.size ↔
        a.value.get! ℓ = 2 := by simpa using this
    by_cases hx : a.value.get! ℓ = 2 <;> simp [hx, this']
  rw [h1, h2]
  exact (hrep.codes.symm).filter _

/-- A constraint with one non-false code, unassigned, forces it. -/
private theorem slack_one {vars lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr} {a : Asg}
    (hv : vars.toList.Nodup) (ha : AsgOk vars.size a) (hrep : Rep vars lits coeffs r pc)
    {o : ℕ} (hf : (scodes lits r).filter (fun ℓ => a.value.get! ℓ != 2) = [o])
    (hd : 0 < pc.degree) :
    ∃ x, (x, dec vars o) ∈ pc.terms ∧ VeriPB.slack (tlits vars a.trail a.trail.size) pc < x := by
  have hp := filter_perm_value hv ha hrep
  rw [hf, List.map_singleton, List.perm_singleton, List.map_eq_singleton_iff] at hp
  obtain ⟨t, ht, hto⟩ := hp
  have hmem : t ∈ posTerms pc := List.mem_of_mem_filter (ht ▸ List.mem_singleton_self t)
  refine ⟨t.1, ?_, ?_⟩
  · have := List.mem_of_mem_filter hmem
    rw [← hto]; exact this
  · rw [slack_posTerms, ht]; simp [coeffSum]; omega

/-- A constraint with no non-false code has a negative slack. -/
private theorem slack_none {vars lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr} {a : Asg}
    (hv : vars.toList.Nodup) (ha : AsgOk vars.size a) (hrep : Rep vars lits coeffs r pc)
    (hf : (scodes lits r).filter (fun ℓ => a.value.get! ℓ != 2) = [])
    (hd : 0 < pc.degree) : VeriPB.slack (tlits vars a.trail a.trail.size) pc < 0 := by
  have hp := filter_perm_value hv ha hrep
  rw [hf, List.map_nil, List.perm_nil, List.map_eq_nil_iff] at hp
  rw [slack_posTerms, hp]; simp [coeffSum]; omega

/-- The codes of a record that are true for `P`, when only its first one can be. -/
private theorem scodes_filter {lits : Array ℕ} {r : CRec} {P : ℕ → Bool} (h2 : 2 ≤ r.size)
    (h1 : P lits[r.start + 1]! = false)
    (hrest : ∀ k, 2 ≤ k → k < r.size → P lits[r.start + k]! = false) :
    (scodes lits r).filter P = if P lits[r.start]! then [lits[r.start]!] else [] := by
  obtain ⟨m, hm⟩ : ∃ m, r.size = m + 2 := ⟨r.size - 2, by omega⟩
  unfold scodes
  rw [hm, List.range_succ_eq_map, List.range_succ_eq_map]
  have hnil : ((List.range m).map fun k => lits[r.start + (k + 1 + 1)]!).filter P = [] :=
    List.filter_eq_nil_iff.2 fun ℓ hℓ => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hℓ
      simp only [List.mem_range] at hk
      simpa using hrest (k + 2) (by omega) (by omega)
  simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero, List.filter_cons]
  rw [h1]
  split <;> simp_all

/-- The first watch swap puts `f` second and keeps the pair of watched literals. -/
private theorem first_swap {lits : Array ℕ} {p f : ℕ} (hp : p + 1 < lits.size)
    (hf : f = lits[p]! ∨ f = lits[p + 1]!) :
    let lits1 := if (lits[p]! == f) = true then lits.swapIfInBounds p (p + 1) else lits
    lits1[p + 1]! = f ∧
    (∀ ℓ : ℕ, [lits1[p]!, lits1[p + 1]!].count ℓ = [lits[p]!, lits[p + 1]!].count ℓ) ∧
    lits1.size = lits.size ∧ (∀ q, q ≠ p → q ≠ p + 1 → lits1[q]! = lits[q]!) ∧
    (lits1 = lits ∨ lits1 = lits.swapIfInBounds p (p + 1)) := by
  intro lits1
  have g := get_swap lits (x := p) (y := p + 1) (by omega) hp
  have s0 : (lits.swapIfInBounds p (p + 1))[p]! = lits[p + 1]! := by rw [g]; simp
  have s1 : (lits.swapIfInBounds p (p + 1))[p + 1]! = lits[p]! := by rw [g]; simp
  by_cases h : lits[p]! = f
  · have e : lits1 = lits.swapIfInBounds p (p + 1) := by simp [lits1, h]
    rw [e, s0, s1]
    exact ⟨h, fun ℓ => (List.Perm.swap lits[p]! lits[p + 1]! []).count_eq ℓ, by simp,
      fun q h1 h2 => by rw [g]; simp [h1, h2], Or.inr rfl⟩
  · have e : lits1 = lits := by simp [lits1, h]
    rw [e]
    refine ⟨?_, fun _ => rfl, rfl, fun _ _ _ => rfl, Or.inl rfl⟩
    rcases hf with hf | hf
    · exact absurd hf.symm h
    · exact hf.symm

/-- A swap inside the range of a live clause keeps every live representation, and touches no
other live record. -/
private theorem swap_live {vars lits lits0 coeffs cpos : Array ℕ} {G : ℕ → Option PBConstr}
    {cons : Array CRec} {alive : ByteArray}
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else lits0.size)
    (halive0 : alive.get! 0 = 0) (hls : lits.size = lits0.size)
    (hrep : ∀ c pc, G c = some pc → Rep vars lits coeffs cons[c]! pc)
    {c0 : ℕ} {pc0 : PBConstr} (hG0 : G c0 = some pc0) (hcl0 : cons[c0]!.clause = true)
    {x y : ℕ} (hx1 : cons[c0]!.start ≤ x) (hx2 : x < cons[c0]!.start + cons[c0]!.size)
    (hy1 : cons[c0]!.start ≤ y) (hy2 : y < cons[c0]!.start + cons[c0]!.size) :
    (∀ c pc, G c = some pc → Rep vars (lits.swapIfInBounds x y) coeffs cons[c]! pc) ∧
    (∀ c pc, G c = some pc → c ≠ c0 → ∀ q, cons[c]!.start ≤ q →
      q < cons[c]!.start + cons[c]!.size → (lits.swapIfInBounds x y)[q]! = lits[q]!) ∧
    (∀ c pc, G c = some pc → c ≠ c0 →
      stored (lits.swapIfInBounds x y) coeffs cons[c]! = stored lits coeffs cons[c]!) := by
  have live1 : ∀ c pc, G c = some pc → 1 ≤ c ∧ c < cons.size := fun c pc hc => by
    have := (hlive c).1 (by simp [hc])
    refine ⟨?_, this.1⟩
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; exact absurd halive0 this.2
    · exact h
  obtain ⟨h01, h0lt⟩ := live1 c0 pc0 hG0
  have hend0 := range_end hlay _ c0 rfl h01 h0lt
  -- other live records lie outside the range of `c0`
  have hout : ∀ c pc, G c = some pc → c ≠ c0 → ∀ q, cons[c0]!.start ≤ q →
      q < cons[c0]!.start + cons[c0]!.size →
      q < cons[c]!.start ∨ cons[c]!.start + cons[c]!.size ≤ q := by
    intro c pc hc hne q hq1 hq2
    obtain ⟨h1, hlt⟩ := live1 c pc hc
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := range_le hlay h1 c0 h h0lt; omega
    · have := range_le hlay h01 c h hlt; omega
  have hxl : x < lits.size := by omega
  have hyl : y < lits.size := by omega
  refine ⟨fun c pc hc => ?_, fun c pc hc hne q hq1 hq2 => ?_, fun c pc hc hne => ?_⟩
  · by_cases hne : c = c0
    · subst hne
      have hr := hrep c pc hc
      have hperm : (scodes (lits.swapIfInBounds x y) cons[c]!).Perm (scodes lits cons[c]!) := by
        have := scodes_swap (lits := lits) (r := cons[c]!) (x := x - cons[c]!.start)
          (y := y - cons[c]!.start) (by omega) (by omega) (by omega)
        rwa [Nat.add_sub_cancel' hx1, Nat.add_sub_cancel' hy1] at this
      exact ⟨hr.degree, fun ℓ hℓ => hr.lt ℓ (hperm.subset hℓ),
        (hperm.map _).trans hr.codes, fun h => absurd hcl0 (by simp [h]), hr.clause⟩
    · have hr := hrep c pc hc
      obtain ⟨e1, e2⟩ := swap_out (coeffs := coeffs) (r := cons[c]!) hxl hyl
        (hout c pc hc hne x hx1 hx2) (hout c pc hc hne y hy1 hy2)
      exact ⟨hr.degree, by rw [e1]; exact hr.lt, by rw [e1]; exact hr.codes,
        by rw [e2]; exact hr.terms, hr.clause⟩
  · rw [get_swap lits hxl hyl]
    have h1 := hout c pc hc hne x hx1 hx2
    have h2 := hout c pc hc hne y hy1 hy2
    simp only [show q ≠ x by omega, show q ≠ y by omega, ↓reduceIte]
  · exact (swap_out hxl hyl (hout c pc hc hne x hx1 hx2) (hout c pc hc hne y hy1 hy2)).2

private theorem count_modify (watches : Array (Array ℕ)) (g c0 c ℓ : ℕ) :
    (watches.modify g (·.push c0))[ℓ]!.count c =
      watches[ℓ]!.count c + (if ℓ = g ∧ g < watches.size ∧ c0 = c then 1 else 0) := by
  simp only [getElem!_eq, Array.getElem?_modify]
  by_cases h1 : g = ℓ
  · subst h1
    by_cases h2 : g < watches.size
    · simp only [Array.getElem?_eq_getElem h2, ↓reduceIte, Option.map_some, Option.getD_some,
        Array.count_push, true_and, h2]
      by_cases h3 : c0 = c <;> simp [h3]
    · simp [h2]
  · simp [h1, Ne.symm h1]

private theorem mem_modify {watches : Array (Array ℕ)} {g c0 c ℓ : ℕ}
    (h : c ∈ (watches.modify g (·.push c0))[ℓ]!) : c ∈ watches[ℓ]! ∨ c = c0 := by
  have := count_modify watches g c0 c ℓ
  have hpos : 0 < (watches.modify g (·.push c0))[ℓ]!.count c := Array.count_pos_iff.2 h
  by_cases h2 : ℓ = g ∧ g < watches.size ∧ c0 = c
  · exact Or.inr h2.2.2.symm
  · simp only [h2, ↓reduceIte, Nat.add_zero] at this
    exact Or.inl (Array.count_pos_iff.1 (this ▸ hpos))

private theorem value3 {n : ℕ} {a : Asg} (ha : AsgOk n a) {ℓ : ℕ} (hℓ : ℓ < 2 * n) :
    a.value.get! ℓ = 0 ∨ a.value.get! ℓ = 1 ∨ a.value.get! ℓ = 2 := by
  rw [ha.value_eq ℓ hℓ]; split_ifs <;> simp

/-- An assignment of an unassigned code keeps a false code false. -/
private theorem false_after {n : ℕ} {a : Asg} (ha : AsgOk n a) {f ℓ r : ℕ} (hf : f < 2 * n)
    (hℓ : ℓ < 2 * n) (hff : a.value.get! f = 2) (h0 : a.value.get! ℓ = 0) :
    (a.assign ℓ r).value.get! f = 2 := by
  obtain ⟨ha', -, htr, -⟩ := ha.assign (r := r) hℓ h0
  have e1 := ha.value_eq f hf
  rw [ha'.value_eq f hf, htr]
  have hne : f ≠ ℓ := fun h => by subst h; rw [hff] at h0; exact absurd h0 (by decide)
  have hn1 : f ∉ a.trail := fun h => by rw [e1] at hff; simp [h] at hff
  have hx : f ^^^ 1 ∈ a.trail := by
    rw [e1] at hff; by_contra hx; simp [hn1, hx] at hff
  simp [hne, hn1, hx]

private theorem modify_ne {watches : Array (Array ℕ)} {g ℓ : ℕ} (h : ℓ ≠ g) (c0 : ℕ) :
    (watches.modify g (·.push c0))[ℓ]! = watches[ℓ]! := by
  simp only [getElem!_eq, Array.getElem?_modify, Ne.symm h, ↓reduceIte]

/-- The conclusion of the clause loop on the result `h`. -/
private def Post (vars : Array ℕ) (G : ℕ → Option PBConstr) (cons : Array CRec)
    (coeffs : Array ℕ) (f : ℕ) (slack : Array ℤ) (lits0 : Array ℕ) (a0 : Asg) (h : Hot) : Prop :=
  let a' : Asg := ⟨h.value, h.reason, h.tpos, h.trail⟩
  h.slack = slack ∧ h.lits.size = lits0.size ∧
  (∀ c pc, G c = some pc → Rep vars h.lits coeffs cons[c]! pc) ∧
  (∀ c pc, G c = some pc → cons[c]!.clause = false →
    stored h.lits coeffs cons[c]! = stored lits0 coeffs cons[c]!) ∧
  h.watches.size = 2 * vars.size ∧ h.watches[f]! = #[] ∧
  (∀ ℓ : ℕ, ∀ c ∈ h.watches[ℓ]!, c < cons.size ∧ cons[c]!.clause = true) ∧
  (∀ c ∈ h.arr, c < cons.size ∧ cons[c]!.clause = true) ∧
  (∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
    h.watches[ℓ]!.count c + (if ℓ = f then h.arr.count c else 0) ≤
      [h.lits[cons[c]!.start]!, h.lits[cons[c]!.start + 1]!].count ℓ) ∧
  AsgOk vars.size a' ∧ AsgExt a0 a' ∧ ChainFrom vars G a0.trail.size a' ∧
  ∀ k, h.confl = some k →
    ∃ pc, G k = some pc ∧ VeriPB.slack (tlits vars a'.trail a'.trail.size) pc < 0

/-- The invariant of the clause loop, for `n` entries of `ws` left. -/
private def Stmt (vars : Array ℕ) (G : ℕ → Option PBConstr) (cons : Array CRec)
    (cpos : Array ℕ) (alive : ByteArray) (coeffs : Array ℕ) (f : ℕ) (slack : Array ℤ)
    (lits0 : Array ℕ) (a0 : Asg) (n : ℕ) : Prop :=
  ∀ (ws : Array ℕ) (i j : ℕ) (lits : Array ℕ) (watches : Array (Array ℕ)) (a : Asg),
    ws.size - i = n → j ≤ i → i ≤ ws.size →
    AsgOk vars.size a → AsgExt a0 a → ChainFrom vars G a0.trail.size a → a.value.get! f = 2 →
    lits.size = lits0.size →
    (∀ c pc, G c = some pc → Rep vars lits coeffs cons[c]! pc) →
    (∀ c pc, G c = some pc → cons[c]!.clause = false →
      stored lits coeffs cons[c]! = stored lits0 coeffs cons[c]!) →
    (∀ c ∈ ws.toList.take j, c < cons.size ∧ cons[c]!.clause = true) →
    (∀ c ∈ ws.toList.drop i, c < cons.size ∧ cons[c]!.clause = true) →
    (∀ ℓ : ℕ, ∀ c ∈ watches[ℓ]!, c < cons.size ∧ cons[c]!.clause = true) →
    watches[f]! = #[] → watches.size = 2 * vars.size →
    (∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
      watches[ℓ]!.count c + (if ℓ = f then
        (ws.toList.take j).count c + (ws.toList.drop i).count c else 0) ≤
        [lits[cons[c]!.start]!, lits[cons[c]!.start + 1]!].count ℓ) →
    Post vars G cons coeffs f slack lits0 a0
      (watchLoop cpos alive f ws i j lits watches slack a.value a.reason a.tpos a.trail)

private theorem base {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {cpos : Array ℕ} {alive : ByteArray} {coeffs : Array ℕ} {f : ℕ} {slack : Array ℤ}
    {lits0 : Array ℕ} {a0 : Asg} :
    Stmt vars G cons cpos alive coeffs f slack lits0 a0 0 := by
  intro ws i j lits watches a hn hji hi ha he hch hff hls hrep hst hK hP hW hWf hWs hcnt
  obtain ⟨value, reason, tpos, trail⟩ := a
  have hi' : ¬ i < ws.size := by omega
  have hd : ws.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
  rw [watchLoop]
  simp only [hi', ↓reduceIte]
  refine ⟨rfl, hls, hrep, hst, hWs, hWf, hW, fun c hc => hK c ?_, fun c pc hc hcl ℓ => ?_,
    ha, he, hch, fun k hk => by cases hk⟩
  · have := Array.mem_toList_iff.2 hc; rwa [Array.toList_shrink] at this
  · have := hcnt c pc hc hcl ℓ
    rw [hd] at this
    simp only [← Array.count_toList, Array.toList_shrink, List.count_nil, Nat.add_zero] at this ⊢
    exact this

private theorem step_live {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {cpos : Array ℕ} {alive : ByteArray} {coeffs : Array ℕ} {f : ℕ} {slack : Array ℤ}
    {lits0 : Array ℕ} {a0 : Asg}
    (hv : vars.toList.Nodup)
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hcpos : cpos.size = cons.size)
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else lits0.size)
    (halive0 : alive.get! 0 = 0) (hf : f < 2 * vars.size) (n : ℕ)
    (IH : Stmt vars G cons cpos alive coeffs f slack lits0 a0 n)
    (ws : Array ℕ) (i j : ℕ) (lits : Array ℕ) (watches : Array (Array ℕ))
    (value : ByteArray) (reason tpos trail : Array ℕ)
    (hn : ws.size - i = n + 1) (hji : j ≤ i) (hi : i ≤ ws.size)
    (ha : AsgOk vars.size ⟨value, reason, tpos, trail⟩)
    (he : AsgExt a0 ⟨value, reason, tpos, trail⟩)
    (hch : ChainFrom vars G a0.trail.size ⟨value, reason, tpos, trail⟩)
    (hff : value.get! f = 2) (hls : lits.size = lits0.size)
    (hrep : ∀ c pc, G c = some pc → Rep vars lits coeffs cons[c]! pc)
    (hst : ∀ c pc, G c = some pc → cons[c]!.clause = false →
      stored lits coeffs cons[c]! = stored lits0 coeffs cons[c]!)
    (hK : ∀ c ∈ ws.toList.take j, c < cons.size ∧ cons[c]!.clause = true)
    (hP : ∀ c ∈ ws.toList.drop i, c < cons.size ∧ cons[c]!.clause = true)
    (hW : ∀ ℓ : ℕ, ∀ c ∈ watches[ℓ]!, c < cons.size ∧ cons[c]!.clause = true)
    (hWf : watches[f]! = #[]) (hWs : watches.size = 2 * vars.size)
    (hcnt : ∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
      watches[ℓ]!.count c + (if ℓ = f then
        (ws.toList.take j).count c + (ws.toList.drop i).count c else 0) ≤
        [lits[cons[c]!.start]!, lits[cons[c]!.start + 1]!].count ℓ)
    (hal0 : alive.get! ws[i]! ≠ 0) :
    Post vars G cons coeffs f slack lits0 a0
      (watchLoop cpos alive f ws i j lits watches slack value reason tpos trail) := by
  have hi' : i < ws.size := by omega
  have hP0 : ws.toList.drop i = ws[i] :: ws.toList.drop (i + 1) :=
    List.drop_eq_getElem_cons (by simp; omega)
  have hPsub : ∀ c ∈ ws.toList.drop (i + 1), c < cons.size ∧ cons[c]!.clause = true :=
    fun c hc => hP c (by rw [hP0]; exact List.mem_cons_of_mem _ hc)
  rw [getElem!_pos ws i hi'] at hal0
  have hal : ¬(alive.get! ws[i] == 0) = true := by simpa using hal0
  rw [watchLoop]
  simp only [hi', ↓reduceIte, getElem!_pos ws i hi', hal, Bool.false_eq_true]
  have hK1 : (ws.set! j ws[i]).toList.take (j + 1) = ws.toList.take j ++ [ws[i]] := by
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    exact take_set (by simp; omega) _
  have hD1 : (ws.set! j ws[i]).toList.drop (i + 1) = ws.toList.drop (i + 1) := by
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    exact drop_set (by omega) _
  have hsz1 : (ws.set! j ws[i]).size = ws.size := by simp
  generalize hc0 : ws[i] = c0 at hP0 hal hK1 hD1 hsz1 ⊢
  obtain ⟨hc0lt, hc0cl⟩ := hP c0 (by rw [hP0]; exact List.mem_cons_self)
  have hal' : alive.get! c0 ≠ 0 := by simpa using hal
  obtain ⟨pc0, hG0⟩ : ∃ pc, G c0 = some pc :=
    Option.isSome_iff_exists.1 ((hlive c0).2 ⟨hc0lt, hal'⟩)
  have hc01 : 1 ≤ c0 := by
    rcases Nat.eq_zero_or_pos c0 with h | h
    · subst h; exact absurd halive0 hal'
    · exact h
  obtain ⟨hst0, hend0⟩ := hlay c0 hc01 hc0lt
  have hr0 := hrep c0 pc0 hG0
  obtain ⟨hd0, hsz0, -⟩ := hr0.clause hc0cl
  have hfin0 := range_end hlay _ c0 rfl hc01 hc0lt
  have he0 : ∀ L : Array ℕ, L.size = lits0.size →
      (if c0 + 1 < cpos.size then cpos[c0 + 1]! else L.size) =
        cons[c0]!.start + cons[c0]!.size := by
    intro L hL; rw [hcpos, hL]; exact hend0.symm
  rw [← hst0]
  -- the falsified literal is one of the two watches
  have hcf := hcnt c0 pc0 hG0 hc0cl f
  simp only [↓reduceIte, hP0, List.count_cons_self] at hcf
  have hfw : f = lits[cons[c0]!.start]! ∨ f = lits[cons[c0]!.start + 1]! := by
    by_contra hno
    simp only [not_or] at hno
    simp only [List.count_cons, List.count_nil, beq_iff_eq, Ne.symm hno.1, Ne.symm hno.2,
      ↓reduceIte] at hcf
    omega
  have hfs := first_swap (lits := lits) (p := cons[c0]!.start) (by omega) hfw
  dsimp only at hfs
  obtain ⟨hl1f, hl1c, hl1s, -, hl1e⟩ := hfs
  generalize hl1 : (if (lits[cons[c0]!.start]! == f) = true then
    lits.swapIfInBounds cons[c0]!.start (cons[c0]!.start + 1) else lits) = lits1
    at hl1f hl1c hl1s hl1e ⊢
  -- the first swap keeps every live representation
  have hsw1 : (∀ c pc, G c = some pc → Rep vars lits1 coeffs cons[c]! pc) ∧
      (∀ c pc, G c = some pc → c ≠ c0 → ∀ q, cons[c]!.start ≤ q →
        q < cons[c]!.start + cons[c]!.size → lits1[q]! = lits[q]!) ∧
      (∀ c pc, G c = some pc → c ≠ c0 →
        stored lits1 coeffs cons[c]! = stored lits coeffs cons[c]!) := by
    rcases hl1e with rfl | rfl
    · exact ⟨hrep, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    · exact swap_live hlive hlay halive0 hls hrep hG0 hc0cl le_rfl (by omega)
        (by omega) (by omega)
  obtain ⟨hrep1, hpos1, hsto1⟩ := hsw1
  have hls1 : lits1.size = lits0.size := by omega
  have hst1 : ∀ c pc, G c = some pc → cons[c]!.clause = false →
      stored lits1 coeffs cons[c]! = stored lits0 coeffs cons[c]! := by
    intro c pc hc hcl
    have hne : c ≠ c0 := fun h => by subst h; simp [hc0cl] at hcl
    rw [hsto1 c pc hc hne]; exact hst c pc hc hcl
  have hposeq : ∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
      [lits1[cons[c]!.start]!, lits1[cons[c]!.start + 1]!].count ℓ =
        [lits[cons[c]!.start]!, lits[cons[c]!.start + 1]!].count ℓ := by
    intro c pc hc hcl ℓ
    by_cases hcc : c = c0
    · subst hcc; exact hl1c ℓ
    · obtain ⟨-, h2, -⟩ := (hrep c pc hc).clause hcl
      rw [hpos1 c pc hc hcc _ le_rfl (by omega), hpos1 c pc hc hcc _ (by omega) (by omega)]
  -- keeping `c0` watched by `f`
  have hK' : ∀ c ∈ (ws.set! j c0).toList.take (j + 1), c < cons.size ∧
      cons[c]!.clause = true := by
    rw [hK1]; intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hK c hc
    · simp only [List.mem_singleton] at hc; subst hc; exact ⟨hc0lt, hc0cl⟩
  have hP' : ∀ c ∈ (ws.set! j c0).toList.drop (i + 1), c < cons.size ∧
      cons[c]!.clause = true := by
    rw [hD1]; exact hPsub
  have hcntK : ∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
      watches[ℓ]!.count c + (if ℓ = f then
        ((ws.set! j c0).toList.take (j + 1)).count c +
          ((ws.set! j c0).toList.drop (i + 1)).count c else 0) ≤
        [lits1[cons[c]!.start]!, lits1[cons[c]!.start + 1]!].count ℓ := by
    intro c pc hc hcl ℓ
    have h0 := hcnt c pc hc hcl ℓ
    rw [hposeq c pc hc hcl ℓ, hK1, hD1]
    rw [hP0] at h0
    simp only [List.count_append, List.count_cons, List.count_nil] at h0 ⊢
    split_ifs at h0 ⊢ <;> omega
  have ho : lits1[cons[c0]!.start]! < 2 * vars.size :=
    hrep1 c0 pc0 hG0 |>.lt _ (List.mem_map.2 ⟨0, List.mem_range.2 (by omega), by simp⟩)
  split
  · -- the other watch is true: keep
    exact IH (ws.set! j c0) (i + 1) (j + 1) lits1 watches
      ⟨value, reason, tpos, trail⟩ (by omega) (by omega) (by omega) ha he hch hff hls1 hrep1
      hst1 hK' hP' hW hWf hWs hcntK
  · rename_i hv1
    rw [he0 lits1 hls1]
    obtain ⟨hk1, hk2, hk3, hk4⟩ := nonFalse_spec lits1 value _ (cons[c0]!.start + 2)
      (cons[c0]!.start + cons[c0]!.size) rfl (by omega)
    generalize hk : nonFalse lits1 value (cons[c0]!.start + 2)
      (cons[c0]!.start + cons[c0]!.size) = k at hk1 hk2 hk3 hk4 ⊢
    split
    · -- a new watch
      rename_i hke
      have hsw2 := swap_live hlive hlay halive0 hls1 hrep1 hG0 hc0cl
        (x := cons[c0]!.start + 1) (y := k) (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hrep2, hpos2, hsto2⟩ := hsw2
      have hg := get_swap lits1 (x := cons[c0]!.start + 1) (y := k) (by omega) (by omega)
      have hg1 : (lits1.swapIfInBounds (cons[c0]!.start + 1) k)[cons[c0]!.start + 1]! =
          lits1[k]! := by rw [hg]; simp
      have hg0 : (lits1.swapIfInBounds (cons[c0]!.start + 1) k)[cons[c0]!.start]! =
          lits1[cons[c0]!.start]! := by
        rw [hg]; simp only [show cons[c0]!.start ≠ cons[c0]!.start + 1 by omega,
          show cons[c0]!.start ≠ k by omega, ↓reduceIte]
      rw [hg1]
      have hgf : lits1[k]! ≠ f := fun h => by
        apply hk3 hke; rw [h]; exact hff
      refine IH ws (i + 1) j _ _
        ⟨value, reason, tpos, trail⟩ (by omega) (by omega) (by omega) ha he hch hff
        (by simp; omega) hrep2 (fun c pc hc hcl => ?_) hK hPsub (fun ℓ c hc => ?_)
        (by rw [modify_ne (Ne.symm hgf)]; exact hWf) (by simp; omega)
        (fun c pc hc hcl ℓ => ?_)
      · have hne : c ≠ c0 := fun h => by subst h; simp [hc0cl] at hcl
        rw [hsto2 c pc hc hne]; exact hst1 c pc hc hcl
      · rcases mem_modify hc with hc | hc
        · exact hW ℓ c hc
        · subst hc; exact ⟨hc0lt, hc0cl⟩
      · have h0 := hcnt c pc hc hcl ℓ
        rw [count_modify]
        rw [hP0] at h0
        by_cases hcc : c = c0
        · subst hcc
          rw [hg0, hg1]
          have h1 := hl1c ℓ
          rw [hl1f] at h1
          rw [← h1] at h0
          simp only [List.count_cons, List.count_nil, beq_iff_eq] at h0 ⊢
          split_ifs at h0 ⊢ <;> omega
        · obtain ⟨-, h2, -⟩ := (hrep c pc hc).clause hcl
          rw [hpos2 c pc hc hcc _ le_rfl (by omega),
            hpos2 c pc hc hcc _ (by omega) (by omega), hposeq c pc hc hcl ℓ]
          simp only [List.count_cons, beq_iff_eq] at h0 ⊢
          split_ifs at h0 ⊢ <;> omega
    · -- no other watch: the clause propagates or conflicts
      rename_i hke
      have hall : (scodes lits1 cons[c0]!).filter (fun ℓ => value.get! ℓ != 2) =
          if value.get! lits1[cons[c0]!.start]! != 2 then [lits1[cons[c0]!.start]!]
          else [] := by
        refine scodes_filter hsz0 ?_ fun k' h1 h2 => ?_
        · rw [hl1f]; simpa using hff
        · have := hk4 (cons[c0]!.start + k') (by omega) (by omega)
          simpa [litVal] using this
      split
      · -- propagate the other watch
        rename_i hv0
        have hv0' : value.get! lits1[cons[c0]!.start]! = 0 := by simpa [litVal] using hv0
        rw [hv0'] at hall
        simp only [show (0 : UInt8) ≠ 2 by decide, bne_iff_ne, ne_eq, not_false_eq_true,
          ↓reduceIte] at hall
        have hF : Forces (tlits vars trail trail.size) pc0 (dec vars lits1[cons[c0]!.start]!) :=
          ⟨ha.not_mem_of_zero hv ho hv0',
            slack_one (a := ⟨value, reason, tpos, trail⟩) hv ha (hrep1 c0 pc0 hG0) hall
              (by omega)⟩
        obtain ⟨ha1, hext, -, -⟩ := ha.assign (r := c0) ho hv0'
        have hch1 := ha.assign_chain (G := G) ho hv0' hG0 hF
        exact IH (ws.set! j c0) (i + 1) (j + 1) lits1
          watches _ (by omega) (by omega) (by omega) ha1 (he.trans hext)
          (hch.ext hext hch1) (false_after ha hf ho hff hv0') hls1 hrep1 hst1 hK' hP' hW
          hWf hWs hcntK
      · -- a conflict
        rename_i hv0
        have hv2 : value.get! lits1[cons[c0]!.start]! = 2 := by
          rcases value3 ha ho with h | h | h
          · simp [litVal, h] at hv0
          · simp [litVal, h] at hv1
          · exact h
        rw [hv2] at hall
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hall
        have hkl := keepLive_toList alive _ (ws.set! j c0) (i + 1) (j + 1) rfl (by omega)
        refine ⟨rfl, hls1, hrep1, hst1, hWs, hWf, hW, fun c hc => ?_,
          fun c pc hc hcl ℓ => ?_, ha, he, hch, fun k hk => ?_⟩
        · have := Array.mem_toList_iff.2 hc
          rw [hkl] at this
          rcases List.mem_append.1 this with h | h
          · exact hK' c h
          · exact hP' c (List.mem_of_mem_filter h)
        · have h0 := hcntK c pc hc hcl ℓ
          have hc' : (alive.get! c != 0) = true := by
            have := (hlive c).1 (by simp [hc]); simpa using this.2
          have hcount : (keepLive alive (ws.set! j c0) (i + 1) (j + 1)).count c =
              ((ws.set! j c0).toList.take (j + 1)).count c +
                ((ws.set! j c0).toList.drop (i + 1)).count c := by
            rw [← Array.count_toList, hkl, List.count_append,
              List.count_filter (p := fun c => alive.get! c != 0) (a := c) hc']
          dsimp only
          rw [hcount]
          exact h0
        · simp only [Option.some.injEq] at hk
          subst hk
          exact ⟨pc0, hG0, slack_none (a := ⟨value, reason, tpos, trail⟩) hv ha
            (hrep1 c0 pc0 hG0) hall (by omega)⟩

private theorem step {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {cpos : Array ℕ} {alive : ByteArray} {coeffs : Array ℕ} {f : ℕ} {slack : Array ℤ}
    {lits0 : Array ℕ} {a0 : Asg}
    (hv : vars.toList.Nodup)
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hcpos : cpos.size = cons.size)
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else lits0.size)
    (halive0 : alive.get! 0 = 0) (hf : f < 2 * vars.size) (n : ℕ)
    (IH : Stmt vars G cons cpos alive coeffs f slack lits0 a0 n) :
    Stmt vars G cons cpos alive coeffs f slack lits0 a0 (n + 1) := by
  intro ws i j lits watches a hn hji hi ha he hch hff hls hrep hst hK hP hW hWf hWs hcnt
  obtain ⟨value, reason, tpos, trail⟩ := a
  have hi' : i < ws.size := by omega
  by_cases hal0 : alive.get! ws[i]! = 0
  · have hP0 : ws.toList.drop i = ws[i] :: ws.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (by simp; omega)
    have hPsub : ∀ c ∈ ws.toList.drop (i + 1), c < cons.size ∧ cons[c]!.clause = true :=
      fun c hc => hP c (by rw [hP0]; exact List.mem_cons_of_mem _ hc)
    rw [getElem!_pos ws i hi'] at hal0
    rw [watchLoop]
    simp only [hi', ↓reduceIte, getElem!_pos ws i hi', hal0, beq_self_eq_true]
    have hdead' : alive.get! ws[i] = 0 := hal0
    refine IH ws (i + 1) j lits watches
      ⟨value, reason, tpos, trail⟩ (by omega) (by omega) (by omega) ha he hch hff hls hrep hst
      hK hPsub hW hWf hWs fun c pc hc hcl ℓ => ?_
    have h0 := hcnt c pc hc hcl ℓ
    have hne : ws[i] ≠ c := fun h => by
      have := (hlive c).1 (by simp [hc]); rw [← h] at this; exact this.2 hdead'
    rw [hP0, List.count_cons] at h0
    simp only [beq_iff_eq, hne, ↓reduceIte, Nat.add_zero] at h0
    exact h0
  · exact step_live hv hlive hcpos hlay halive0 hf n IH ws i j lits watches value reason tpos
      trail hn hji hi ha he hch hff hls hrep hst hK hP hW hWf hWs hcnt hal0

private theorem loop {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {cpos : Array ℕ} {alive : ByteArray} {coeffs : Array ℕ} {f : ℕ} {slack : Array ℤ}
    {lits0 : Array ℕ} {a0 : Asg}
    (hv : vars.toList.Nodup)
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hcpos : cpos.size = cons.size)
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else lits0.size)
    (halive0 : alive.get! 0 = 0) (hf : f < 2 * vars.size) :
    ∀ n, Stmt vars G cons cpos alive coeffs f slack lits0 a0 n
  | 0 => base
  | n + 1 => step hv hlive hcpos hlay halive0 hf n (loop hv hlive hcpos hlay halive0 hf n)

private theorem watchLoop_spec {vars : Array ℕ} {G : ℕ → Option PBConstr} {cons : Array CRec}
    {cpos : Array ℕ} {alive : ByteArray} {coeffs : Array ℕ} {f : ℕ} {ws lits : Array ℕ}
    {watches : Array (Array ℕ)} {slack : Array ℤ} {a : Asg}
    (hv : vars.toList.Nodup) (ha : AsgOk vars.size a)
    (hlive : ∀ c, (G c).isSome ↔ c < cons.size ∧ alive.get! c ≠ 0)
    (hrep : ∀ c pc, G c = some pc → Rep vars lits coeffs cons[c]! pc)
    (hcpos : cpos.size = cons.size)
    (hlay : ∀ c, 1 ≤ c → c < cons.size → cons[c]!.start = cpos[c]! ∧
      cons[c]!.start + cons[c]!.size = if c + 1 < cons.size then cpos[c + 1]! else lits.size)
    (halive0 : alive.get! 0 = 0)
    (hf : f < 2 * vars.size) (hff : a.value.get! f = 2)
    (hws : ∀ c ∈ ws, c < cons.size ∧ cons[c]!.clause = true)
    (hW : ∀ ℓ : ℕ, ∀ c ∈ watches[ℓ]!, c < cons.size ∧ cons[c]!.clause = true)
    (hWf : watches[f]! = #[]) (hWsize : watches.size = 2 * vars.size)
    (hcount : ∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
      watches[ℓ]!.count c + (if ℓ = f then ws.count c else 0) ≤
        [lits[cons[c]!.start]!, lits[cons[c]!.start + 1]!].count ℓ) :
    let h := watchLoop cpos alive f ws 0 0 lits watches slack a.value a.reason a.tpos a.trail
    let a' : Asg := ⟨h.value, h.reason, h.tpos, h.trail⟩
    h.slack = slack ∧ h.lits.size = lits.size ∧
    (∀ c pc, G c = some pc → Rep vars h.lits coeffs cons[c]! pc) ∧
    (∀ c pc, G c = some pc → cons[c]!.clause = false →
      stored h.lits coeffs cons[c]! = stored lits coeffs cons[c]!) ∧
    h.watches.size = watches.size ∧ h.watches[f]! = #[] ∧
    (∀ ℓ : ℕ, ∀ c ∈ h.watches[ℓ]!, c < cons.size ∧ cons[c]!.clause = true) ∧
    (∀ c ∈ h.arr, c < cons.size ∧ cons[c]!.clause = true) ∧
    (∀ c pc, G c = some pc → cons[c]!.clause = true → ∀ ℓ : ℕ,
      h.watches[ℓ]!.count c + (if ℓ = f then h.arr.count c else 0) ≤
        [h.lits[cons[c]!.start]!, h.lits[cons[c]!.start + 1]!].count ℓ) ∧
    AsgOk vars.size a' ∧ AsgExt a a' ∧ ChainFrom vars G a.trail.size a' ∧
    ∀ k, h.confl = some k →
      ∃ pc, G k = some pc ∧ VeriPB.slack (tlits vars a'.trail a'.trail.size) pc < 0 := by
  have hP := loop (slack := slack) hv hlive hcpos hlay halive0 hf ws.size ws 0 0 lits watches a
    (by simp) le_rfl
    (Nat.zero_le _) ha (AsgExt.refl a) (ChainFrom.of_size vars G a) hff rfl hrep
    (fun _ _ _ _ => rfl) (by simp) (fun c hc => hws c (by simpa using hc)) hW hWf hWsize
    (fun c pc hc hcl ℓ => by
      simp only [List.take_zero, List.drop_zero, List.count_nil, Nat.zero_add, Array.count_toList]
      exact hcount c pc hc hcl ℓ)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hP
  exact ⟨h1, h2, h3, h4, by rw [h5, hWsize], h6, h7, h8, h9, h10, h11, h12, h13⟩

private theorem getElem!_set {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α)
    (hi : i < a.size) : (a.set i v hi)[j]! = if i = j then v else a[j]! := by
  simp only [getElem!_eq, Array.getElem?_set]
  split_ifs <;> grind

private theorem pairsL_flatL (L : List (ℕ × ℕ)) : pairsL (flatL L) = L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [flatL, pairsL, ih]

private theorem flatL_even (L : List (ℕ × ℕ)) : (flatL L).length % 2 = 0 := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [flatL, List.length_cons]; omega

/-- Dropping the pairs of dead constraints keeps the weight of a live one. -/
private theorem wsum_filter {alive : ByteArray} {c : ℕ} (hc : alive.get! c ≠ 0)
    {os arr : Array ℕ}
    (harr : arr.toList = flatL ((pairsL os.toList).filter fun p => alive.get! p.1 != 0)) :
    wsum c arr = wsum c os := by
  unfold wsum
  rw [harr, pairsL_flatL, List.filter_filter]
  congr 2
  refine List.filter_congr fun p _ => ?_
  by_cases hp : p.1 = c
  · simp [hp, hc]
  · simp [hp]

/-- Filtering out the dead pairs twice is filtering once. -/
private theorem occ_compose {alive : ByteArray} {L X Y : Array ℕ}
    (hX : X = L ∨ X.toList = flatL ((pairsL L.toList).filter fun p => alive.get! p.1 != 0))
    (hY : Y = X ∨ Y.toList = flatL ((pairsL X.toList).filter fun p => alive.get! p.1 != 0)) :
    Y = L ∨ Y.toList = flatL ((pairsL L.toList).filter fun p => alive.get! p.1 != 0) := by
  rcases hY with rfl | hY
  · exact hX
  · rcases hX with rfl | hX
    · exact Or.inr hY
    · refine Or.inr ?_
      rw [hY, hX, pairsL_flatL, List.filter_filter]
      congr 1
      exact List.filter_congr fun p _ => by simp

/-- A code and its negation are not both on the trail. -/
private theorem not_both {n : ℕ} {a : Asg} (h : AsgOk n a) {m : ℕ} (hm : m ∈ a.trail)
    (hm' : m ^^^ 1 ∈ a.trail) : False := by
  have := List.inj_on_of_nodup_map h.nodup (Array.mem_def.1 hm) (Array.mem_def.1 hm')
    (xor_one_div_two m).symm
  exact xor_one_ne m this.symm

/-- The invariant after a change of the fields that propagation changes. -/
private theorem core {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    {lits : Array ℕ} {watches occ : Array (Array ℕ)} {slack : Array ℤ} {asg : Asg}
    {qhead : ℕ} (hasg : AsgOk s.vars.size asg) (hq : qhead ≤ asg.trail.size)
    (hws : watches.size = 2 * s.vars.size) (hos : occ.size = 2 * s.vars.size)
    (hsl : slack.size = s.cons.size) (hls : lits.size = s.lits.size)
    (hrep : ∀ c pc, G c = some pc → Rep s.vars lits s.coeffs s.cons[c]! pc)
    (hoe : ∀ ℓ : ℕ, occ[ℓ]!.size % 2 = 0)
    (hon : ∀ ℓ : ℕ, ∀ p ∈ pairsL occ[ℓ]!.toList, p.1 < s.cons.size ∧
      (s.alive.get! p.1 ≠ 0 → reg s.cons[p.1]! = true))
    (hox : ∀ c pc, G c = some pc → reg s.cons[c]! = true → ∀ ℓ : ℕ,
      wsum c occ[ℓ]! = (((stored lits s.coeffs s.cons[c]!).filter (·.2 == ℓ)).map (·.1)).sum)
    (hwn : ∀ ℓ : ℕ, ∀ c ∈ watches[ℓ]!, c < s.cons.size ∧ s.cons[c]!.clause = true)
    (hwc : ∀ c pc, G c = some pc → s.cons[c]!.clause = true → ∀ ℓ : ℕ,
      watches[ℓ]!.count c ≤ [lits[s.cons[c]!.start]!, lits[s.cons[c]!.start + 1]!].count ℓ) :
    InvCore { s with lits, watches, occ, slack, asg, qhead } G :=
  ⟨h.nodup, h.idx_some, h.idx_mem, hasg, hws, hos, hq, h.cons_pos, h.cpos_size, hsl,
    h.alive_size, h.rr_size, by rw [hls]; exact h.coeffs_size,
    fun c h1 h2 => by rw [hls]; exact h.layout c h1 h2, h.alive0, h.live, hrep, hoe, hon, hox,
    hwn, hwc, h.roots⟩

/-- The occurrence lists after one literal's list is compacted. -/
private theorem occ_after {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) {f : ℕ}
    (hf : f < s.occ.size) {arr : Array ℕ}
    (harr : arr.toList = flatL ((pairsL s.occ[f]!.toList).filter fun p => s.alive.get! p.1 != 0)) :
    let occ := (s.occ.set f #[] hf).set! f arr
    occ.size = 2 * s.vars.size ∧ (∀ ℓ : ℕ, occ[ℓ]!.size % 2 = 0) ∧
    (∀ ℓ : ℕ, ∀ p ∈ pairsL occ[ℓ]!.toList, p.1 < s.cons.size ∧
      (s.alive.get! p.1 ≠ 0 → reg s.cons[p.1]! = true)) ∧
    (∀ c pc, G c = some pc → reg s.cons[c]! = true → ∀ ℓ : ℕ,
      wsum c occ[ℓ]! = (((stored s.lits s.coeffs s.cons[c]!).filter (·.2 == ℓ)).map (·.1)).sum) ∧
    (∀ ℓ : ℕ, occ[ℓ]! = s.occ[ℓ]! ∨
      occ[ℓ]!.toList =
        flatL ((pairsL s.occ[ℓ]!.toList).filter fun p => s.alive.get! p.1 != 0)) := by
  have hget : ∀ ℓ, ((s.occ.set f #[] hf).set! f arr)[ℓ]! = if f = ℓ then arr else s.occ[ℓ]! := by
    intro ℓ
    rw [getElem!_set!, getElem!_set]
    by_cases e : f = ℓ
    · subst e; simp [hf]
    · simp [e]
  refine ⟨by simp [h.occ_size], ?_, ?_, ?_, ?_⟩
  · intro ℓ; rw [hget]; split
    · have := flatL_even ((pairsL s.occ[f]!.toList).filter fun p => s.alive.get! p.1 != 0)
      rw [← harr] at this; simpa using this
    · exact h.occ_even ℓ
  · intro ℓ p hp; rw [hget] at hp; split at hp
    · rw [harr, pairsL_flatL] at hp
      exact h.occ_name f p (List.mem_of_mem_filter hp)
    · exact h.occ_name ℓ p hp
  · intro c pc hG hr ℓ; rw [hget]; split
    · rename_i e; subst e
      rw [wsum_filter ((h.live c).1 (by simp [hG])).2 harr]
      exact h.occ_exact c pc hG hr f
    · exact h.occ_exact c pc hG hr ℓ
  · intro ℓ; rw [hget]; split
    · rename_i e; subst e; exact Or.inr harr
    · exact Or.inl rfl

/-- The state after propagation, from the results of `propLoop`. -/
private def res (s : EState) (q' : ℕ) (occ' : Array (Array ℕ)) (H : Hot) : EState :=
  { s with lits := H.lits
           watches := H.watches
           occ := occ'
           slack := H.slack
           asg := ⟨H.value, H.reason, H.tpos, H.trail⟩
           qhead := q' }

private theorem propLoop_inv {G : ℕ → Option PBConstr} :
    ∀ (fuel : ℕ) (s : EState), InvCore s G → SlackOk s G →
    ∀ q' occ' (H : Hot), propLoop s.cons s.cpos s.alive s.coeffs fuel s.qhead s.lits s.watches
      s.occ s.slack s.asg.value s.asg.reason s.asg.tpos s.asg.trail = (q', occ', H) →
    InvCore (res s q' occ' H) G ∧ SlackOk (res s q' occ' H) G ∧
    AsgExt s.asg ⟨H.value, H.reason, H.tpos, H.trail⟩ ∧
    ChainFrom s.vars G s.asg.trail.size ⟨H.value, H.reason, H.tpos, H.trail⟩ ∧
    (∀ ℓ : ℕ, occ'[ℓ]! = s.occ[ℓ]! ∨
      occ'[ℓ]!.toList = flatL ((pairsL s.occ[ℓ]!.toList).filter fun p => s.alive.get! p.1 != 0)) ∧
    ∀ k, H.confl = some k →
      ∃ pc, G k = some pc ∧ VeriPB.slack (tlits s.vars H.trail H.trail.size) pc < 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s h hs q' occ' H hR
    simp only [propLoop, Prod.mk.injEq] at hR
    obtain ⟨rfl, rfl, rfl⟩ := hR
    exact ⟨h, hs, AsgExt.refl _, ChainFrom.of_size _ _ _, fun _ => Or.inl rfl,
      fun _ h => by cases h⟩
  | succ fuel ih =>
    intro s h hs q' occ' H hR
    rw [propLoop] at hR
    by_cases hq : s.qhead < s.asg.trail.size
    · simp only [hq, ↓reduceIte] at hR
      have ha := h.asg
      have hv := h.nodup
      have htq : s.asg.trail[s.qhead] < 2 * s.vars.size :=
        ha.trail_lt _ (Array.getElem_mem hq)
      have htqb : s.asg.trail[s.qhead]! = s.asg.trail[s.qhead] :=
        getElem!_pos s.asg.trail s.qhead hq
      have hf : s.asg.trail[s.qhead]! ^^^ 1 < 2 * s.vars.size := by
        rw [htqb]; exact xor_one_lt.2 htq
      have hfo : s.asg.trail[s.qhead]! ^^^ 1 < s.occ.size := by rw [h.occ_size]; exact hf
      have hfw : s.asg.trail[s.qhead]! ^^^ 1 < s.watches.size := by rw [h.watches_size]; exact hf
      rw [Array.swapAt!_def hfo] at hR
      simp only at hR
      have hos : s.occ[s.asg.trail[s.qhead]! ^^^ 1] = s.occ[s.asg.trail[s.qhead]! ^^^ 1]! :=
        (getElem!_pos s.occ _ hfo).symm
      rw [hos] at hR
      have hP := pbLoop_spec (watches := s.watches) (G := G) hv ha h.live h.rep
        (h.occ_name _) (h.occ_even _) hq (h.occ_exact · · · · _) hs h.slack_size
      generalize pbLoop s.cons s.alive s.lits s.coeffs s.watches
        s.occ[s.asg.trail[s.qhead]! ^^^ 1]! 0 0 none s.slack s.asg.value s.asg.reason s.asg.tpos
        s.asg.trail = H1 at hP hR
      obtain ⟨cf1, arr1, lits1, watches1, slack1, value1, reason1, tpos1, trail1⟩ := H1
      simp only at hP hR
      obtain ⟨rfl, rfl, harr1, hsz1, hsl1, ha1, he1, hch1, hcf1⟩ := hP
      have hOcc := occ_after h hfo harr1
      simp only at hOcc
      obtain ⟨hosz, hoe, hon, hox, hocc⟩ := hOcc
      set a1 : Asg := ⟨value1, reason1, tpos1, trail1⟩ with ha1def
      have hq1 : s.qhead + 1 ≤ trail1.size := by
        have := he1.size_le; simp only [ha1def] at this; omega
      have hsl1' : ∀ c pc, G c = some pc → reg s.cons[c]! = true →
          slack1[c]! = VeriPB.slack (tlits s.vars trail1 (s.qhead + 1)) pc := by
        intro c pc hG hr
        rw [hsl1 c pc hG hr, show tlits s.vars trail1 (s.qhead + 1) =
          tlits s.vars s.asg.trail (s.qhead + 1) from ext_tlits he1 hq]
      by_cases hc1 : cf1.isSome = true
      · simp only [hc1, ↓reduceIte, Prod.mk.injEq] at hR
        obtain ⟨rfl, rfl, rfl⟩ := hR
        refine ⟨core h ha1 hq1 h.watches_size hosz (by rw [hsz1, h.slack_size]) rfl h.rep hoe
          hon hox h.watch_name h.watch_count, hsl1', he1, hch1, hocc, hcf1⟩
      · have hc1' : cf1.isSome = false := by simpa using hc1
        simp only [hc1', Bool.false_eq_true, ↓reduceIte] at hR
        rw [Array.swapAt!_def hfw] at hR
        simp only at hR
        have hws : s.watches[s.asg.trail[s.qhead]! ^^^ 1] =
            s.watches[s.asg.trail[s.qhead]! ^^^ 1]! := (getElem!_pos s.watches _ hfw).symm
        rw [hws] at hR
        -- The falsified literal is false.
        have hff : value1.get! (s.asg.trail[s.qhead]! ^^^ 1) = 2 := by
          have hm : s.asg.trail[s.qhead] ∈ a1.trail := by
            have := Array.getElem_mem hq
            exact Array.mem_def.2 (he1.1.subset (Array.mem_def.1 this))
          rw [ha1.value_eq _ hf, htqb]
          have hnot : s.asg.trail[s.qhead] ^^^ 1 ∉ a1.trail := fun hm' => not_both ha1 hm hm'
          simp [hnot, xor_one_xor_one, hm]
        set f := s.asg.trail[s.qhead]! ^^^ 1 with hfdef
        have hWget : ∀ ℓ, (s.watches.set f #[] hfw)[ℓ]! = if f = ℓ then #[] else s.watches[ℓ]! :=
          fun ℓ => getElem!_set _ _ _ _ _
        have hW := watchLoop_spec (G := G) (cpos := s.cpos) (alive := s.alive)
          (coeffs := s.coeffs) (ws := s.watches[f]!) (lits := s.lits)
          (watches := s.watches.set f #[] hfw) (slack := slack1) (a := a1) hv ha1 h.live h.rep
          h.cpos_size h.layout h.alive0 hf hff (fun c hc => h.watch_name f c hc)
          (fun ℓ c hc => by
            rw [hWget] at hc; split at hc
            · simp at hc
            · exact h.watch_name ℓ c hc)
          (by rw [hWget]; simp) (by simp [h.watches_size])
          (fun c pc hG hcl ℓ => by
            rw [hWget]
            by_cases e : f = ℓ
            · subst e; simp only [↓reduceIte]
              have := h.watch_count c pc hG hcl f
              simpa using this
            · have e' : ¬ ℓ = f := fun x => e x.symm
              simp only [e, e', ↓reduceIte, Nat.add_zero]
              exact h.watch_count c pc hG hcl ℓ)
        simp only at hW
        generalize watchLoop s.cpos s.alive f s.watches[f]! 0 0 s.lits
          (s.watches.set f #[] hfw) slack1 value1 reason1 tpos1 trail1 = H2 at hW hR
        obtain ⟨cf2, arr2, lits2, watches2, slack2, value2, reason2, tpos2, trail2⟩ := H2
        simp only at hW hR
        obtain ⟨rfl, hls2, hrep2, hst2, hwsz2, hwf2, hwn2, harr2, hwc2, ha2, he2, hch2, hcf2⟩ := hW
        have hWget2 : ∀ ℓ, (watches2.set! f arr2)[ℓ]! = if f = ℓ then arr2 else watches2[ℓ]! := by
          intro ℓ; rw [getElem!_set!]
          have : f < watches2.size := by rw [hwsz2]; simpa using hfw
          by_cases e : f = ℓ
          · subst e; simp [this]
          · simp [e]
        set a2 : Asg := ⟨value2, reason2, tpos2, trail2⟩ with ha2def
        have hq2 : s.qhead + 1 ≤ trail2.size := by
          have := he2.size_le; simp only [ha2def, ha1def] at this; omega
        have hcore2 : InvCore { s with lits := lits2
                                       watches := watches2.set! f arr2
                                       occ := (s.occ.set f #[] hfo).set! f arr1
                                       slack := slack2
                                       asg := a2
                                       qhead := s.qhead + 1 } G := by
          refine core h ha2 hq2 (by simp [hwsz2, h.watches_size]) hosz
            (by rw [hsz1, h.slack_size]) hls2 hrep2 hoe hon ?_ ?_ ?_
          · intro c pc hG hr ℓ
            have hcl : s.cons[c]!.clause = false := by
              simp only [reg, Bool.and_eq_true, Bool.not_eq_true'] at hr; exact hr.1
            rw [hst2 c pc hG hcl]; exact hox c pc hG hr ℓ
          · intro ℓ c hc; rw [hWget2] at hc; split at hc
            · exact harr2 c hc
            · exact hwn2 ℓ c hc
          · intro c pc hG hcl ℓ
            have := hwc2 c pc hG hcl ℓ
            rw [hWget2]
            by_cases e : f = ℓ
            · subst e; simp only [↓reduceIte] at this ⊢; rw [hwf2] at this; simpa using this
            · have e' : ¬ ℓ = f := fun x => e x.symm
              simp only [e, e', ↓reduceIte, Nat.add_zero] at this ⊢; exact this
        have hslack2 : SlackOk { s with lits := lits2
                                        watches := watches2.set! f arr2
                                        occ := (s.occ.set f #[] hfo).set! f arr1
                                        slack := slack2
                                        asg := a2
                                        qhead := s.qhead + 1 } G := by
          intro c pc hG hr
          simp only at hr ⊢
          rw [hsl1' c pc hG hr, show tlits s.vars trail2 (s.qhead + 1) =
            tlits s.vars trail1 (s.qhead + 1) from ext_tlits he2 hq1]
        have he12 := he1.trans he2
        have hch12 := hch1.ext he2 hch2
        by_cases hc2 : cf2.isSome = true
        · simp only [hc2, ↓reduceIte, Prod.mk.injEq] at hR
          obtain ⟨rfl, rfl, rfl⟩ := hR
          exact ⟨hcore2, hslack2, he12, hch12, hocc, hcf2⟩
        · have hc2' : cf2.isSome = false := by simpa using hc2
          simp only [hc2', Bool.false_eq_true, ↓reduceIte] at hR
          obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih _ hcore2 hslack2 q' occ' H hR
          refine ⟨i1, i2, he12.trans i3, hch12.ext i3 i4, fun ℓ => ?_, i6⟩
          exact occ_compose (hocc ℓ) (i5 ℓ)
    · simp only [hq, ↓reduceIte, Prod.mk.injEq] at hR
      obtain ⟨rfl, rfl, rfl⟩ := hR
      exact ⟨h, hs, AsgExt.refl _, ChainFrom.of_size _ _ _, fun _ => Or.inl rfl,
        fun _ h => by cases h⟩

/-- **Propagation keeps the invariant**, extends the trail by forced entries, only drops pairs of
dead constraints from the occurrence lists, and reports only real conflicts. -/
private theorem propagate_spec {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    (hs : SlackOk s G) :
    let r := s.propagate
    (∃ lits watches occ slack asg qhead,
      r.1 = { s with lits, watches, occ, slack, asg, qhead }) ∧
    InvCore r.1 G ∧ SlackOk r.1 G ∧ AsgExt s.asg r.1.asg ∧
    ChainFrom s.vars G s.asg.trail.size r.1.asg ∧
    (∀ ℓ : ℕ, r.1.occ[ℓ]! = s.occ[ℓ]! ∨
      r.1.occ[ℓ]!.toList =
        flatL ((pairsL s.occ[ℓ]!.toList).filter fun p => s.alive.get! p.1 != 0)) ∧
    ∀ k, r.2 = some k →
      ∃ pc, G k = some pc ∧
        VeriPB.slack (tlits s.vars r.1.asg.trail r.1.asg.trail.size) pc < 0 := by
  have key := propLoop_inv (G := G) (s.asg.value.size + 1) s h hs
  obtain ⟨varIdx, vars, cons, cpos, alive, lits, coeffs, watches, occ, roots,
    ⟨value, reason, tpos, trail⟩, qhead, slack, rootReason, rootLen, rootConflict, dirty, seen⟩ := s
  simp only at key ⊢
  dsimp only [EState.propagate]
  generalize propLoop cons cpos alive coeffs (value.size + 1) qhead lits watches occ slack value
    reason tpos trail = R at key ⊢
  obtain ⟨q', occ', ⟨cf, arr, lits', watches', slack', value', reason', tpos', trail'⟩⟩ := R
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := key q' occ' _ rfl
  exact ⟨⟨_, _, _, _, _, _, rfl⟩, k1, k2, k3, k4, k5, k6⟩

/-! ### Backtracking -/

/-- The trail positions of an assignment hold distinct variables. -/
private theorem idx_unique {N : ℕ} {a : Asg} (h : AsgOk N a) {j k : ℕ}
    (hj : j < a.trail.size) (hk : k < a.trail.size) (he : a.trail[j] / 2 = a.trail[k] / 2) :
    j = k :=
  (List.Nodup.getElem_inj_iff h.nodup (hi := by simpa using hj) (hj := by simpa using hk)).1
    (by simpa using he)

/-- A code is on the first `q` entries of the trail exactly when its recorded position is
below `q`. -/
private theorem mem_take_iff {N : ℕ} {a : Asg} (h : AsgOk N a) {m : ℕ} (hm : m ∈ a.trail)
    (q : ℕ) : m ∈ a.trail.toList.take q ↔ a.tpos[m / 2]! < q := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hm
  rw [h.tpos_eq k hk, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : j < a.trail.size := by simp at hj; omega
    have := idx_unique h hj' hk (by simp only [Array.getElem_toList] at he; rw [he])
    simp at hj; omega
  · intro hq
    exact ⟨k, by simp; omega, by simp⟩

/-- A code is falsified by the processed part of the trail exactly when its value is false and
its variable was assigned before `q`. -/
private theorem falseProc {N : ℕ} {a : Asg} (h : AsgOk N a) {ℓ : ℕ} (hℓ : ℓ < 2 * N) (q : ℕ) :
    (litVal a.value ℓ == 2 && decide (a.tpos[ℓ / 2]! < q)) =
      decide (ℓ ^^^ 1 ∈ a.trail.toList.take q) := by
  unfold litVal
  rw [h.value_eq ℓ hℓ]
  by_cases hx : ℓ ^^^ 1 ∈ a.trail
  · have hn : ℓ ∉ a.trail := by
      intro hl
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hl
      obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.1 hx
      have := idx_unique h hj hk (by rw [hke, xor_one_div_two])
      subst this
      exact xor_one_ne _ hke.symm
    have := mem_take_iff h hx q
    rw [xor_one_div_two] at this
    simp [hn, hx, this]
  · have : ℓ ^^^ 1 ∉ a.trail.toList.take q := fun h' =>
      hx (by simpa using List.mem_of_mem_take h')
    by_cases hl : ℓ ∈ a.trail <;> simp [hl, hx, this]

/-- The values of the codes are those of the first `i` trail entries. -/
private def VP (s : EState) (v : ByteArray) (i : ℕ) : Prop :=
  v.size = 2 * s.vars.size ∧ ∀ ℓ, ℓ < 2 * s.vars.size →
    v.get! ℓ = if ℓ ∈ s.asg.trail.toList.take i then 1
      else if ℓ ^^^ 1 ∈ s.asg.trail.toList.take i then 2 else 0

/-- The slack counters of the live constraints are their slacks on the first `j` trail
entries. -/
private def SP (s : EState) (G : ℕ → Option PBConstr) (sl : Array ℤ) (j : ℕ) : Prop :=
  sl.size = s.cons.size ∧ ∀ c pc, G c = some pc → reg s.cons[c]! = true →
    sl[c]! = VeriPB.slack (tlits s.vars s.asg.trail j) pc

private theorem var_notin {N : ℕ} {a : Asg} (h : AsgOk N a) {i : ℕ} (hi : i < a.trail.size)
    {m : ℕ} (hm : m ∈ a.trail.toList.take i) : m / 2 ≠ a.trail[i] / 2 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hm
  intro he
  have := idx_unique h (j := j) (k := i) (by simp at hj; omega) hi (by simpa using he)
  simp at hj; omega

private theorem take_succ {a : Array ℕ} {i : ℕ} (hi : i < a.size) :
    a.toList.take (i + 1) = a.toList.take i ++ [a[i]] := by
  simp [List.take_add_one, hi]

private theorem pairsL_short {l : List ℕ} (h : l.length ≤ 1) : pairsL l = [] := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl

private theorem restore (os : Array ℕ) : ∀ (m k : ℕ) (sl : Array ℤ), os.size - k = m →
    (EState.undo.restore os k sl).size = sl.size ∧ ∀ c, c < sl.size →
      (EState.undo.restore os k sl)[c]! =
        sl[c]! + ((((pairsL (os.toList.drop k)).filter (·.1 == c)).map (·.2)).sum : ℕ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k sl hm
    rw [EState.undo.restore]
    split
    · rename_i hk
      have hd : os.toList.drop k = os[k] :: os[k + 1] :: os.toList.drop (k + 2) := by
        rw [List.drop_eq_getElem_cons (by simp; omega),
          List.drop_eq_getElem_cons (by simp; omega)]
        simp
      obtain ⟨h1, h2⟩ := ih (os.size - (k + 2)) (by omega) (k + 2) _ rfl
      refine ⟨by rw [h1]; simp, fun c hc => ?_⟩
      rw [h2 c (by simpa using hc), hd, getElem!_eq (sl.modify _ _), Array.getElem?_modify,
        getElem!_pos os k (by omega), getElem!_pos os (k + 1) hk, getElem!_eq sl c]
      simp only [pairsL, List.filter_cons]
      by_cases hc' : os[k] = c
      · simp [hc', Array.getElem?_eq_getElem hc]
        omega
      · simp [hc']
    · refine ⟨rfl, fun c _ => ?_⟩
      rw [pairsL_short (by simp; omega)]
      simp

private theorem mem_scodes {lits coeffs : Array ℕ} {r : CRec} {p : ℕ × ℕ}
    (hp : p ∈ stored lits coeffs r) : p.2 ∈ scodes lits r := by
  unfold stored at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  exact List.mem_map.2 ⟨k, hk, rfl⟩

/-- The coefficients of a constraint on a literal are those its stored terms put on the code. -/
private theorem sum_lit {vars lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr}
    (hrep : Rep vars lits coeffs r pc) (hcl : r.clause = false) (hv : vars.toList.Nodup)
    {ℓ : ℕ} (hℓ : ℓ < 2 * vars.size) :
    ((pc.terms.filter (·.2 == dec vars ℓ)).map (·.1)).sum =
      (((stored lits coeffs r).filter (·.2 == ℓ)).map (·.1)).sum := by
  have h0 : ∀ ts : List (ℕ × Literal ℕ), ((ts.filter (·.2 == dec vars ℓ)).map (·.1)).sum =
      (((ts.filter (0 < ·.1)).filter (·.2 == dec vars ℓ)).map (·.1)).sum := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      by_cases h1 : 0 < t.1
      · by_cases h2 : (t.2 == dec vars ℓ) = true <;> simp [h1, h2, ih]
      · have h3 : t.1 = 0 := by omega
        by_cases h2 : (t.2 == dec vars ℓ) = true <;> simp [h2, ih, h3]
  rw [h0, ← posTerms, ← (((hrep.terms hcl).filter (·.2 == dec vars ℓ)).map (·.1)).sum_nat,
    List.filter_map, List.map_map]
  have hf : (stored lits coeffs r).filter
      ((fun t => t.2 == dec vars ℓ) ∘ fun p => (p.1, dec vars p.2)) =
      (stored lits coeffs r).filter (·.2 == ℓ) := List.filter_congr fun p hp => by
    have hp2 : p.2 < 2 * vars.size := hrep.lt _ (mem_scodes hp)
    simp only [Function.comp_apply]
    by_cases he : p.2 = ℓ
    · simp [he]
    · have : dec vars p.2 ≠ dec vars ℓ := fun h => he (dec_inj hv hp2 hℓ h)
      simp [he, this]
  rw [hf]
  simp [Function.comp_def]

private theorem VP_step {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) {i : ℕ}
    (hi : i < s.asg.trail.size) {v : ByteArray} (hv : VP s v (i + 1)) :
    VP s ((v.set! s.asg.trail[i]! 0).set! (s.asg.trail[i]! ^^^ 1) 0) i := by
  rw [getElem!_pos s.asg.trail i hi]
  have ht : s.asg.trail[i] < 2 * s.vars.size := h.asg.trail_lt _ (Array.getElem_mem hi)
  have htx : s.asg.trail[i] ^^^ 1 < 2 * s.vars.size := xor_one_lt.2 ht
  have hnt : s.asg.trail[i] ∉ s.asg.trail.toList.take i := fun hm =>
    var_notin h.asg hi hm rfl
  have hntx : s.asg.trail[i] ^^^ 1 ∉ s.asg.trail.toList.take i := fun hm =>
    var_notin h.asg hi hm (xor_one_div_two _)
  refine ⟨by rw [ByteArray.size_set!, ByteArray.size_set!]; exact hv.1, fun ℓ hℓ => ?_⟩
  rw [ByteArray.get!_set!, ByteArray.get!_set!, ByteArray.size_set!, hv.1]
  by_cases h1 : ℓ = s.asg.trail[i] ^^^ 1
  · subst h1
    simp [htx, hntx, xor_one_xor_one, hnt]
  · by_cases h2 : ℓ = s.asg.trail[i]
    · subst h2
      simp [ht, hnt, hntx, xor_one_ne]
    · have h3 : ℓ ^^^ 1 ≠ s.asg.trail[i] := fun e => h1 (by rw [← e, xor_one_xor_one])
      rw [hv.2 ℓ hℓ, take_succ hi]
      simp [h2, h3, Ne.symm h1, Ne.symm h2]

private theorem tlits_succ {vars trail : Array ℕ} {i : ℕ} (hi : i < trail.size) :
    tlits vars trail (i + 1) = tlits vars trail i ++ [dec vars trail[i]] := by
  simp [tlits, take_succ hi]

private theorem SP_step {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) {i : ℕ}
    (hi : i < s.asg.trail.size) {sl : Array ℤ} (hs : SP s G sl (min s.qhead (i + 1))) :
    SP s G (if i < s.qhead then EState.undo.restore s.occ[s.asg.trail[i]! ^^^ 1]! 0 sl
      else sl) (min s.qhead i) := by
  rw [getElem!_pos s.asg.trail i hi]
  split
  · rename_i hq
    rw [show min s.qhead (i + 1) = i + 1 by omega] at hs
    rw [show min s.qhead i = i by omega]
    have ht : s.asg.trail[i] < 2 * s.vars.size := h.asg.trail_lt _ (Array.getElem_mem hi)
    have hnt : s.asg.trail[i] ∉ s.asg.trail.toList.take i := fun hm =>
      var_notin h.asg hi hm rfl
    obtain ⟨hr1, hr2⟩ := restore s.occ[s.asg.trail[i] ^^^ 1]! _ 0 sl rfl
    refine ⟨by rw [hr1]; exact hs.1, fun c pc hG hreg => ?_⟩
    have hc : c < sl.size := by rw [hs.1]; exact ((h.live c).1 (by simp [hG])).1
    have hw := h.occ_exact c pc hG hreg (s.asg.trail[i] ^^^ 1)
    unfold wsum at hw
    have hcl : s.cons[c]!.clause = false := by
      simp only [reg, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hreg
      exact hreg.1
    have hm : dec s.vars s.asg.trail[i] ∉ tlits s.vars s.asg.trail i := fun hm' =>
      hnt ((dec_mem_tlits h.nodup h.asg.trail_lt ht i).1 hm')
    rw [hr2 c hc, List.drop_zero, hs.2 c pc hG hreg, hw,
      ← sum_lit (h.rep c pc hG) hcl h.nodup (xor_one_lt.2 ht), dec_xor, tlits_succ hi,
      slack_append_singleton hm pc]
    omega
  · rename_i hq
    rwa [show min s.qhead (i + 1) = min s.qhead i by omega] at hs

private theorem undo_inv {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) {n : ℕ} :
    ∀ (i : ℕ) (v : ByteArray) (sl : Array ℤ), n ≤ i → i ≤ s.asg.trail.size →
      VP s v i → SP s G sl (min s.qhead i) →
      ∃ sl' v', EState.undo s.occ s.qhead n i sl { s.asg with value := v } =
          (sl', { s.asg with value := v', trail := s.asg.trail.take n }) ∧
        VP s v' n ∧ SP s G sl' (min s.qhead n) := by
  intro i
  induction i with
  | zero =>
    intro v sl hn _ hv hs
    have : n = 0 := by omega
    subst this
    rw [EState.undo]
    exact ⟨sl, v, by simp, hv, hs⟩
  | succ i ih =>
    intro v sl hn hi hv hs
    by_cases hlt : n < i + 1
    · rw [EState.undo]
      simp only [hlt, ↓reduceIte, Nat.add_sub_cancel]
      exact ih _ _ (by omega) (by omega) (VP_step h (by omega) hv) (SP_step h (by omega) hs)
    · have : n = i + 1 := by omega
      subst this
      rw [EState.undo]
      simp only [Nat.lt_irrefl, ↓reduceIte]
      exact ⟨sl, v, by simp, hv, hs⟩

private theorem toList_take (a : Array ℕ) (n : ℕ) : (a.take n).toList = a.toList.take n := by
  rw [← Array.shrink_eq_take, Array.toList_shrink]

private theorem backtrack_spec {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    (hs : SlackOk s G) {n : ℕ} (hn : n ≤ s.asg.trail.size) :
    let r := s.backtrack n
    (∃ slack asg, r = { s with slack, asg, qhead := min s.qhead n }) ∧ InvCore r G ∧
    SlackOk r G ∧ r.asg.trail = s.asg.trail.take n ∧ r.asg.reason = s.asg.reason := by
  have hV0 : VP s s.asg.value s.asg.trail.size := by
    refine ⟨h.asg.value_size, fun ℓ hℓ => ?_⟩
    rw [h.asg.value_eq ℓ hℓ, List.take_of_length_le (by simp)]
    simp only [Array.mem_def]
  have hS0 : SP s G s.slack (min s.qhead s.asg.trail.size) :=
    ⟨h.slack_size, by rw [Nat.min_eq_left h.qhead_le]; exact hs⟩
  obtain ⟨sl', v', hU, hV, hS⟩ := undo_inv h s.asg.trail.size s.asg.value s.slack hn le_rfl hV0 hS0
  have hU' : EState.undo s.occ s.qhead n s.asg.trail.size s.slack s.asg =
      (sl', { s.asg with value := v', trail := s.asg.trail.take n }) := hU
  have hb : s.backtrack n =
      { s with slack := sl', asg := { s.asg with value := v', trail := s.asg.trail.take n },
               qhead := min s.qhead n } := by
    have key : ∀ t : EState, t.backtrack n =
        { t with slack := (EState.undo t.occ t.qhead n t.asg.trail.size t.slack t.asg).1,
                 asg := (EState.undo t.occ t.qhead n t.asg.trail.size t.slack t.asg).2,
                 qhead := min t.qhead n } := by
      intro t; cases t; rfl
    rw [key, hU']
  dsimp only
  rw [hb]
  refine ⟨⟨_, _, rfl⟩, { h with asg := ?_, qhead_le := ?_, slack_size := hS.1 }, ?_, rfl, rfl⟩
  · refine ⟨hV.1, h.asg.reason_size, h.asg.tpos_size, fun ℓ hℓ => ?_, ?_, fun ℓ hℓ => ?_,
      fun k hk => ?_⟩
    · rw [Array.mem_def, toList_take] at hℓ
      exact h.asg.trail_lt ℓ (Array.mem_def.2 (List.mem_of_mem_take hℓ))
    · rw [toList_take]
      exact h.asg.nodup.sublist ((List.take_sublist _ _).map _)
    · dsimp only
      rw [hV.2 ℓ hℓ]
      simp only [Array.mem_def, toList_take]
    · have hk' : k < s.asg.trail.size := by
        rw [← Array.shrink_eq_take, Array.size_shrink] at hk; omega
      have : (s.asg.trail.take n)[k] = s.asg.trail[k] := by
        simp only [← Array.shrink_eq_take, Array.getElem_shrink]
      rw [this]
      exact h.asg.tpos_eq k hk'
  · dsimp only
    rw [← Array.shrink_eq_take, Array.size_shrink]
    omega
  · intro c pc hG hreg
    rw [hS.2 c pc hG hreg]
    unfold tlits
    simp only [toList_take, List.take_take]
    congr 3
    omega

/-! ### Adding constraints -/

private theorem freshSlack_eq {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    {r : CRec} {pc : PBConstr}
    (hal : ((stored s.lits s.coeffs r).map fun p => (p.1, dec s.vars p.2)).Perm (posTerms pc))
    (hlt : ∀ ℓ ∈ scodes s.lits r, ℓ < 2 * s.vars.size) (hd : r.degree = pc.degree) :
    s.freshSlack r.start r.size r.degree = VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc := by
  have hcount : ∀ (L : List ℕ) (init : ℤ),
      (forIn (m := Id) L init fun k acc =>
        if (!(litVal s.asg.value s.lits[k]! == 2 &&
            decide (s.asg.tpos[s.lits[k]! / 2]! < s.qhead))) = true then
          pure (ForInStep.yield (acc + ((s.coeffs[k]! : ℕ) : ℤ)))
        else pure (ForInStep.yield acc)) =
      pure (init + (L.map fun k =>
        if (!(litVal s.asg.value s.lits[k]! == 2 &&
            decide (s.asg.tpos[s.lits[k]! / 2]! < s.qhead))) = true then
          ((s.coeffs[k]! : ℕ) : ℤ) else 0).sum) := by
    intro L
    induction L with
    | nil => intro init; simp
    | cons k L ih =>
      intro init
      by_cases hP : (!(litVal s.asg.value s.lits[k]! == 2 &&
          decide (s.asg.tpos[s.lits[k]! / 2]! < s.qhead))) = true
      · simp only [List.forIn_cons, hP, ↓reduceIte, List.map_cons, List.sum_cons, pure_bind, ih]
        congr 1; omega
      · simp only [List.forIn_cons, hP, ↓reduceIte, List.map_cons, List.sum_cons, pure_bind, ih,
          Bool.false_eq_true]
        congr 1; omega
  unfold EState.freshSlack
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [hcount]
  have hsz : [r.start:r.start + r.size].size = r.size := by
    simp [Std.Legacy.Range.size]
  rw [hsz, List.range'_eq_map_range, List.map_map, slack_posTerms, hd]
  have hperm := (hal.filter (fun t => !falsified (tlits s.vars s.asg.trail s.qhead) t)).map
    (·.1)
  unfold coeffSum
  rw [← hperm.sum_nat, List.filter_map, List.map_map]
  have key : ∀ L : List ℕ, (∀ k ∈ L, s.lits[r.start + k]! < 2 * s.vars.size) →
      ((L.map fun k =>
        if (!(litVal s.asg.value s.lits[r.start + k]! == 2 &&
            decide (s.asg.tpos[s.lits[r.start + k]! / 2]! < s.qhead))) = true then
          ((s.coeffs[r.start + k]! : ℕ) : ℤ) else 0).sum) =
      ((((L.map fun k => (s.coeffs[r.start + k]!, s.lits[r.start + k]!)).filter
        ((fun t => !falsified (tlits s.vars s.asg.trail s.qhead) t) ∘
          fun p => (p.1, dec s.vars p.2))).map
        ((fun x => x.1) ∘ fun p => (p.1, dec s.vars p.2))).sum : ℕ) := by
    intro L hL
    induction L with
    | nil => simp
    | cons k L ih =>
      have hk := hL k List.mem_cons_self
      have ih := ih fun k' hk' => hL k' (List.mem_cons_of_mem _ hk')
      simp only [List.map_cons, List.sum_cons, List.filter_cons, Function.comp_apply]
      rw [falseProc h.asg hk, ← falsified_dec h.nodup h.asg.trail_lt hk s.qhead
        s.coeffs[r.start + k]!, ih]
      by_cases hb : falsified (tlits s.vars s.asg.trail s.qhead) (s.coeffs[r.start + k]!,
        dec s.vars s.lits[r.start + k]!) = true <;> simp [hb]
  simp only [Function.comp_def, stored, pure_bind]
  rw [key (List.range r.size) fun k hk =>
    hlt _ (by simp only [scodes, List.mem_map]; exact ⟨k, hk, rfl⟩)]
  change -(pc.degree : ℤ) + _ = _
  simp only [Function.comp_def]
  omega

private theorem getElem!_push {α : Type} [Inhabited α] (a : Array α) (x : α) (i : ℕ) :
    (a.push x)[i]! = if i = a.size then x else a[i]! := by
  simp only [getElem!_eq, Array.getElem?_push]; split <;> rfl

private theorem prefix_get {a b : Array ℕ} (h : a.toList <+: b.toList) {i : ℕ}
    (hi : i < a.size) : b[i]! = a[i]! := by
  obtain ⟨t, ht⟩ := h
  simp only [getElem!_eq, ← Array.getElem?_toList]
  rw [← ht, List.getElem?_append_left (by simpa using hi)]

private theorem rep_ext {vars vars' lits coeffs : Array ℕ} {r : CRec} {pc : PBConstr}
    (hr : Rep vars lits coeffs r pc) (h : vars.toList <+: vars'.toList) :
    Rep vars' lits coeffs r pc where
  degree := hr.degree
  lt ℓ hℓ := lt_of_lt_of_le (hr.lt ℓ hℓ) (by have := h.length_le; simp at this; omega)
  codes := by
    rw [List.map_congr_left fun ℓ hℓ => dec_ext h (hr.lt ℓ hℓ)]; exact hr.codes
  terms hc := by
    rw [List.map_congr_left fun p hp => by rw [dec_ext h (hr.lt _ (mem_scodes hp))]]
    exact hr.terms hc
  clause := hr.clause

private theorem ite_neg {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

private theorem push2_empty (a : Array (Array ℕ)) (ℓ : ℕ) :
    ((a.push #[]).push #[])[ℓ]! = if ℓ < a.size then a[ℓ]! else #[] := by
  simp only [getElem!_eq, Array.getElem?_push, Array.size_push]
  by_cases h1 : ℓ < a.size
  · simp [h1, show ℓ ≠ a.size + 1 by omega, show ℓ ≠ a.size by omega]
  · rw [ite_neg h1]
    by_cases h2 : ℓ = a.size + 1
    · simp [h2]
    · by_cases h3 : ℓ = a.size
      · simp [h3]
      · simp [h2, h3, Array.getElem?_eq_none (show a.size ≤ ℓ by omega)]; rfl

private theorem litCode_spec {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    (hs : SlackOk s G) (l : Literal ℕ) :
    let r := s.litCode l
    (∃ varIdx vars value reason tpos watches occ,
      r.1 = { s with varIdx, vars, asg := ⟨value, reason, tpos, s.asg.trail⟩, watches, occ }) ∧
    InvCore r.1 G ∧ SlackOk r.1 G ∧ s.vars.toList <+: r.1.vars.toList ∧
    AsgExt s.asg r.1.asg ∧ r.2 < 2 * r.1.vars.size ∧ dec r.1.vars r.2 = l := by
  obtain ⟨x, b⟩ := l
  obtain ⟨varIdx, vars, cons, cpos, alive, lits, coeffs, watches, occ, roots,
    ⟨value, reason, tpos, trail⟩, qhead, slack, rootReason, rootLen, rootConflict, dirty, seen⟩ := s
  dsimp only
  unfold EState.litCode
  dsimp only
  split
  · rename_i i hi
    obtain ⟨hlt, hx⟩ := h.idx_some _ _ hi
    dsimp only at hlt hx ⊢
    refine ⟨⟨varIdx, vars, value, reason, tpos, watches, occ, rfl⟩, h, hs, List.prefix_refl _,
      AsgExt.refl _, ?_, ?_⟩
    · split <;> omega
    · cases b <;> simp [dec, hx, Nat.add_div]
  · rename_i hn
    dsimp only
    have hasg := h.asg
    dsimp only at hasg hn
    have hxv : x ∉ vars.toList := by
      intro hm
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hm
      have := h.idx_mem j (by simpa using hj)
      dsimp only at this
      rw [getElem!_pos vars j (by simpa using hj)] at this
      simp only [Array.getElem_toList] at hjx
      rw [hjx, hn] at this
      cases this
    have hpre : vars.toList <+: (vars.push x).toList := by simp
    have hn2 : ∀ m ∈ trail, m < 2 * vars.size := hasg.trail_lt
    refine ⟨⟨_, _, _, _, _, _, _, rfl⟩, ?_, ?_, hpre, ?_, ?_, ?_⟩
    · exact {
        nodup := by
          rw [Array.toList_push, List.nodup_append]
          refine ⟨h.nodup, List.nodup_singleton x, fun y hy z hz => ?_⟩
          simp only [List.mem_singleton] at hz
          subst hz
          exact fun he => hxv (he ▸ hy)
        idx_some := by
          intro y i hy
          rw [Std.HashMap.getElem?_insert] at hy
          split at hy
          · rename_i hxy
            cases hy
            simp only [beq_iff_eq] at hxy
            subst hxy
            simp
          · obtain ⟨h1, h2⟩ := h.idx_some y i hy
            dsimp only at h1 h2
            refine ⟨by simp; omega, ?_⟩
            rw [getElem!_push, ite_neg (by omega)]; exact h2
        idx_mem := by
          intro i hi
          simp only [Array.size_push] at hi
          by_cases hin : i = vars.size
          · subst hin; simp
          · rw [getElem!_push, ite_neg hin, Std.HashMap.getElem?_insert]
            have hne : (x == vars[i]!) = false := by
              rw [getElem!_pos vars i (by omega)]
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro he; exact hxv (he ▸ by simp)
            rw [hne]; exact h.idx_mem i (by dsimp only; omega)
        asg := {
          value_size := by simp [hasg.value_size]; omega
          reason_size := by simp [hasg.reason_size]
          tpos_size := by simp [hasg.tpos_size]
          trail_lt := fun m hm => by have := hn2 m hm; simp; omega
          nodup := hasg.nodup
          value_eq := by
            intro ℓ hℓ
            rw [ByteArray.get!_push, ByteArray.get!_push, ByteArray.size_push', hasg.value_size]
            by_cases h1 : ℓ < 2 * vars.size
            · rw [ite_neg (by omega), ite_neg (by omega)]; exact hasg.value_eq ℓ h1
            · have hl : ℓ ∉ trail := fun hm => by have := hn2 ℓ hm; omega
              have hl' : ℓ ^^^ 1 ∉ trail := fun hm => by
                have := hn2 _ hm; have := xor_one_div_two ℓ; simp at hℓ; omega
              have : ℓ = 2 * vars.size ∨ ℓ = 2 * vars.size + 1 := by simp at hℓ; omega
              rcases this with rfl | rfl <;> simp [hl, hl']
          tpos_eq := by
            intro k hk
            have := hn2 _ (Array.getElem_mem hk)
            rw [getElem!_push, ite_neg (by rw [hasg.tpos_size]; omega)]
            exact hasg.tpos_eq k hk }
        watches_size := by simp [h.watches_size]; omega
        occ_size := by simp [h.occ_size]; omega
        qhead_le := h.qhead_le
        cons_pos := h.cons_pos
        cpos_size := h.cpos_size
        slack_size := h.slack_size
        alive_size := h.alive_size
        rr_size := h.rr_size
        coeffs_size := h.coeffs_size
        layout := h.layout
        alive0 := h.alive0
        live := h.live
        rep := fun c pc hc => rep_ext (h.rep c pc hc) hpre
        occ_even := by
          intro ℓ; rw [push2_empty]; split
          · exact h.occ_even ℓ
          · rfl
        occ_name := by
          intro ℓ p hp; rw [push2_empty] at hp; split at hp
          · exact h.occ_name ℓ p hp
          · simp [pairsL] at hp
        occ_exact := by
          intro c pc hc hreg ℓ; rw [push2_empty]; split
          · exact h.occ_exact c pc hc hreg ℓ
          · rename_i hℓ
            rw [h.occ_size] at hℓ
            have : (stored lits coeffs cons[c]!).filter (·.2 == ℓ) = [] := by
              rw [List.filter_eq_nil_iff]
              intro q hq
              have := (h.rep c pc hc).lt _ (mem_scodes hq)
              simp only [beq_iff_eq]; omega
            simp [wsum, pairsL, this]
        watch_name := by
          intro ℓ c hc; rw [push2_empty] at hc; split at hc
          · exact h.watch_name ℓ c hc
          · simp at hc
        watch_count := by
          intro c pc hc hcl ℓ; rw [push2_empty]; split
          · exact h.watch_count c pc hc hcl ℓ
          · simp
        roots := h.roots }
    · intro c pc hc hreg
      rw [hs c pc hc hreg]
      dsimp only
      rw [tlits_ext hpre hn2]
    · refine ⟨List.prefix_refl _, fun m hm => ?_⟩
      have := hn2 m hm
      rw [getElem!_push, ite_neg (by rw [hasg.reason_size]; omega)]
    · split <;> simp only [Array.size_push] <;> omega
    · cases b <;> simp [dec, Nat.add_div]

private theorem loop_perm {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n)
    (pivot : α) (as : Vector α n) (i k : ℕ) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.Perm as := by
  induction as, i, k, ilo, ik, w using Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop]; simp only [h, hlt, dite_true, ite_true]
    exact ih.trans (Vector.swap_perm _ _)
  | case2 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop]; simp only [h, hlt, dite_true]
    exact ih
  | case3 as i k ilo ik w h =>
    rw [Array.qpartition.loop]; simp only [h, dite_false]
    exact Vector.swap_perm _ _

private theorem ite_swap_perm {α : Type} {n : ℕ} {b : Prop} [Decidable b] {x : Vector α n}
    {i j : ℕ} {hi : i < n} {hj : j < n} : (if b then x.swap i j hi hj else x).Perm x := by
  split
  · exact Vector.swap_perm _ _
  · exact Vector.Perm.refl _

private theorem qpartition_perm {α : Type} {n : ℕ} (as : Vector α n) (lt : α → α → Bool)
    (lo hi : ℕ) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.Perm as := by
  unfold Array.qpartition
  refine (loop_perm _ _ _ _ _ _ _ _ _ _ _).trans ?_
  exact ite_swap_perm.trans (ite_swap_perm.trans ite_swap_perm)

private theorem sort_perm {α : Type} (lt : α → α → Bool) {n : ℕ} (as : Vector α n)
    (lo hi : ℕ) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qsort.sort lt as lo hi w hlo hhi).Perm as := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as1 hp hm =>
    have hq := qpartition_perm as lt lo hi w hlo hhi
    rw [hp] at hq
    rw [Array.qsort.sort]; simp only [h, dite_true, hp, hm]
    exact hq
  | case2 as lo hi w hlo hhi h mid hmid as1 hp hm ih1 _ ih2 =>
    have hq := qpartition_perm as lt lo hi w hlo hhi
    rw [hp] at hq
    rw [Array.qsort.sort]; simp only [h, dite_true, hp, hm, dite_false]
    exact ih2.trans (ih1.trans hq)
  | case3 as lo hi w hlo hhi h =>
    rw [Array.qsort.sort]; simp only [h, dite_false]; exact Vector.Perm.refl _

private theorem qsort_perm {α : Type} (as : Array α) (lt : α → α → Bool) :
    (as.qsort lt).toList.Perm as.toList := by
  unfold Array.qsort
  split
  · exact List.Perm.refl _
  · exact Vector.perm_iff_toList_perm.1 (sort_perm _ _ _ _ _ _ _)

/-- One step of the loop of `codes`. -/
private def codesStep (t : ℕ × Literal ℕ) (st : EState × Array (ℕ × ℕ)) :
    EState × Array (ℕ × ℕ) :=
  if t.1 > 0 then ((st.1.litCode t.2).1, st.2.push (t.1, (st.1.litCode t.2).2)) else st

private theorem codes_eq (s : EState) (c : PBConstr) :
    s.codes c = ((c.terms.foldl (fun st t => codesStep t st) (s, #[])).1,
      (c.terms.foldl (fun st t => codesStep t st) (s, #[])).2.qsort fun a b => a.1 > b.1) := by
  have key : ∀ (L : List (ℕ × Literal ℕ)) (init : EState × Array (ℕ × ℕ)),
      forIn (m := Id) L init (fun t (st : EState × Array (ℕ × ℕ)) =>
        if t.1 > 0 then
          pure (ForInStep.yield ((st.1.litCode t.2).1, st.2.push (t.1, (st.1.litCode t.2).2)))
        else pure (ForInStep.yield (st.1, st.2))) =
        pure (L.foldl (fun st t => codesStep t st) init) := by
    intro L
    induction L with
    | nil => intro; rfl
    | cons t L ih =>
      intro init
      rw [List.forIn_cons, List.foldl_cons]
      by_cases ht : t.1 > 0
      · rw [show codesStep t init = ((init.1.litCode t.2).1,
            init.2.push (t.1, (init.1.litCode t.2).2)) by simp [codesStep, ht]]
        simp only [ht, ↓reduceIte, pure_bind, ih]
      · rw [show codesStep t init = init by simp [codesStep, ht]]
        simp only [ht, ↓reduceIte, pure_bind, ih]
  unfold EState.codes
  simp only [Id.run, key]
  rfl

/-- The invariant of the loop of `codes`, after the terms `done`. -/
private def CodesInv (s : EState) (G : ℕ → Option PBConstr) (done : List (ℕ × Literal ℕ))
    (st : EState × Array (ℕ × ℕ)) : Prop :=
  (∃ varIdx vars value reason tpos watches occ,
    st.1 = { s with varIdx, vars, asg := ⟨value, reason, tpos, s.asg.trail⟩, watches, occ }) ∧
  InvCore st.1 G ∧ SlackOk st.1 G ∧ s.vars.toList <+: st.1.vars.toList ∧ AsgExt s.asg st.1.asg ∧
  (st.2.toList.map fun p => (p.1, dec st.1.vars p.2)) = done ∧
  ∀ p ∈ st.2, p.2 < 2 * st.1.vars.size

private theorem codesInv_step {s : EState} {G : ℕ → Option PBConstr}
    {done : List (ℕ × Literal ℕ)} {st : EState × Array (ℕ × ℕ)} (hI : CodesInv s G done st)
    (t : ℕ × Literal ℕ) :
    CodesInv s G (done ++ [t].filter fun t => 0 < t.1) (codesStep t st) := by
  obtain ⟨⟨vi, vs, va, re, tp, wa, oc, hsh⟩, hc, hsl, hpre, hext, hmap, hlt⟩ := hI
  unfold codesStep
  by_cases ht : 0 < t.1
  · simp only [show t.1 > 0 from ht, ↓reduceIte]
    obtain ⟨⟨vi', vs', va', re', tp', wa', oc', hsh'⟩, hc', hsl', hpre', hext', hlt', hdec'⟩ :=
      litCode_spec hc hsl t.2
    refine ⟨⟨vi', vs', va', re', tp', wa', oc', ?_⟩, hc', hsl', hpre.trans hpre',
      hext.trans hext', ?_, ?_⟩
    · rw [hsh', hsh]
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, hdec',
        List.filter_cons, ht, decide_true, ↓reduceIte, List.filter_nil]
      rw [← hmap]
      congr 1
      exact List.map_congr_left fun p hp => by rw [dec_ext hpre' (hlt p (by simpa using hp))]
    · intro p hp
      simp only [Array.mem_push] at hp
      dsimp only
      rcases hp with hp | rfl
      · exact lt_of_lt_of_le (hlt p hp) (by have := hpre'.length_le; simp at this; omega)
      · exact hlt'
  · simp only [show ¬t.1 > 0 from ht, ↓reduceIte]
    refine ⟨⟨vi, vs, va, re, tp, wa, oc, hsh⟩, hc, hsl, hpre, hext, ?_, hlt⟩
    simp [hmap, ht]

private theorem codes_spec {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    (hs : SlackOk s G) (c : PBConstr) :
    let r := s.codes c
    (∃ varIdx vars value reason tpos watches occ,
      r.1 = { s with varIdx, vars, asg := ⟨value, reason, tpos, s.asg.trail⟩, watches, occ }) ∧
    InvCore r.1 G ∧ SlackOk r.1 G ∧ s.vars.toList <+: r.1.vars.toList ∧ AsgExt s.asg r.1.asg ∧
    (r.2.toList.map fun p => (p.1, dec r.1.vars p.2)).Perm (posTerms c) ∧
    ∀ p ∈ r.2, p.2 < 2 * r.1.vars.size := by
  have hloop : ∀ (L : List (ℕ × Literal ℕ)) (done : List (ℕ × Literal ℕ))
      (st : EState × Array (ℕ × ℕ)), CodesInv s G done st →
      CodesInv s G (done ++ L.filter fun t => 0 < t.1)
        (L.foldl (fun st t => codesStep t st) st) := by
    intro L
    induction L with
    | nil => intro done st hI; simpa using hI
    | cons t L ih =>
      intro done st hI
      have := ih _ _ (codesInv_step hI t)
      have e : done ++ (t :: L).filter (fun t => 0 < t.1) =
          (done ++ [t].filter (fun t => 0 < t.1)) ++ L.filter (fun t => 0 < t.1) := by
        rw [List.append_assoc, ← List.filter_append]; rfl
      rw [List.foldl_cons, e]; exact this
  have h0 : CodesInv s G [] (s, #[]) :=
    ⟨⟨s.varIdx, s.vars, s.asg.value, s.asg.reason, s.asg.tpos, s.watches, s.occ, rfl⟩, h, hs,
      List.prefix_refl _, AsgExt.refl _, rfl, by simp⟩
  obtain ⟨hsh, hc, hsl, hpre, hext, hmap, hlt⟩ := hloop c.terms [] _ h0
  rw [codes_eq]
  refine ⟨hsh, hc, hsl, hpre, hext, ?_, fun p hp => hlt p ?_⟩
  swap
  · rw [Array.mem_def] at hp ⊢; exact (qsort_perm _ _).mem_iff.1 hp
  simp only [List.nil_append] at hmap
  rw [posTerms, ← hmap]
  exact (qsort_perm _ _).map _

/-- The occurrence lists after `pushCons` registers the terms `L` of the constraint `i`. -/
private def occFold (i : ℕ) (L : List (ℕ × ℕ)) (o : Array (Array ℕ)) : Array (Array ℕ) :=
  L.foldl (fun o a => o.modify a.2 fun x => (x.push i).push a.1) o

private theorem occFold_size (i : ℕ) :
    ∀ (L : List (ℕ × ℕ)) (o : Array (Array ℕ)), (occFold i L o).size = o.size
  | [], _ => rfl
  | a :: L, o => by
    simp only [occFold, List.foldl_cons] at *
    rw [show List.foldl _ _ L = occFold i L _ from rfl, occFold_size i L]
    simp

private theorem occFold_get (i : ℕ) :
    ∀ (L : List (ℕ × ℕ)) (o : Array (Array ℕ)), (∀ a ∈ L, a.2 < o.size) → ∀ ℓ : ℕ,
      (occFold i L o)[ℓ]!.toList =
        o[ℓ]!.toList ++ flatL ((L.filter (·.2 == ℓ)).map fun a => (i, a.1))
  | [], _, _, ℓ => by simp [occFold, flatL]
  | a :: L, o, hL, ℓ => by
    have hrest := occFold_get i L (o.modify a.2 fun x => (x.push i).push a.1)
      (fun b hb => by simpa using hL b (List.mem_cons_of_mem _ hb)) ℓ
    simp only [occFold, List.foldl_cons] at hrest ⊢
    rw [hrest]
    have ha := hL a List.mem_cons_self
    simp only [getElem!_eq, Array.getElem?_modify]
    by_cases hal : a.2 = ℓ
    · subst hal
      simp [Array.getElem?_eq_getElem ha, flatL]
    · simp [hal]

private theorem fold_lits : ∀ (L : List (ℕ × ℕ)) (b : EState),
    L.foldl (fun b a => { b with lits := b.lits.push a.2, coeffs := b.coeffs.push a.1 }) b =
      { b with lits := b.lits ++ (L.map Prod.snd).toArray,
               coeffs := b.coeffs ++ (L.map Prod.fst).toArray }
  | [], b => by simp
  | a :: L, b => by
    rw [List.foldl_cons, fold_lits L]
    simp

private theorem fold_occ (i : ℕ) : ∀ (L : List (ℕ × ℕ)) (b : EState),
    L.foldl (fun b a => { b with occ := b.occ.modify a.2 fun x => (x.push i).push a.1 }) b =
      { b with occ := occFold i L b.occ }
  | [], b => rfl
  | a :: L, b => by
    rw [List.foldl_cons, fold_occ i L]
    rfl

private theorem pushCons_eq (s : EState) (ts : Array (ℕ × ℕ)) (d : ℕ) (s0 : ℤ) (cl : Bool)
    (hh : Hint) : s.pushCons ts d s0 cl hh =
      ({ s with cons := s.cons.push (CRec.mk s.lits.size ts.size d s0 cl hh)
                cpos := s.cpos.push s.lits.size
                alive := EState.setPush s.alive s.cons.size 1
                lits := s.lits ++ (ts.toList.map Prod.snd).toArray
                coeffs := s.coeffs ++ (ts.toList.map Prod.fst).toArray
                slack := s.slack.push 0
                rootReason := EState.setPush s.rootReason s.cons.size 0
                occ := if (!cl && decide (0 < d)) = true then
                    occFold s.cons.size ts.toList s.occ else s.occ }, s.cons.size) := by
  unfold EState.pushCons
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, pure_bind, ← Array.foldl_toList,
    fold_lits, fold_occ]
  split <;> rfl

private theorem setPush_get (b : ByteArray) {i : ℕ} (j : ℕ) (v : UInt8) (hi : i ≤ b.size) :
    (EState.setPush b i v).get! j = if j = i then v else b.get! j := by
  unfold EState.setPush
  split
  · rw [ByteArray.get!_set!]
    by_cases hj : j = i
    · subst hj; simp [*]
    · simp [hj, Ne.symm hj]
  · rw [ByteArray.get!_push]
    have : i = b.size := by omega
    subst this; rfl

private theorem setPush_size (b : ByteArray) (i : ℕ) (v : UInt8) :
    (EState.setPush b i v).size = if i < b.size then b.size else b.size + 1 := by
  unfold EState.setPush
  split
  · exact ByteArray.size_set! _ _ _
  · exact ByteArray.size_push' _ _

private theorem end_le {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) :
    ∀ c, 1 ≤ c → c < s.cons.size → s.cons[c]!.start + s.cons[c]!.size ≤ s.lits.size := by
  have key : ∀ m c, s.cons.size - c = m → 1 ≤ c → c < s.cons.size →
      s.cons[c]!.start + s.cons[c]!.size ≤ s.lits.size := by
    intro m
    induction m with
    | zero => intro c hm _ hc; omega
    | succ m ih =>
      intro c hm h1 hc
      rw [(h.layout c h1 hc).2]
      split
      · rename_i hc1
        have := ih (c + 1) (by omega) (by omega) hc1
        rw [← (h.layout (c + 1) (by omega) hc1).1]
        omega
      · exact le_refl _
  exact fun c => key _ c rfl

private theorem append_get_left (a : Array ℕ) (l : List ℕ) {k : ℕ} (hk : k < a.size) :
    (a ++ l.toArray)[k]! = a[k]! := by
  simp only [getElem!_eq, Array.getElem?_append_left hk]

private theorem append_get_right (a : Array ℕ) (l : List ℕ) (k : ℕ) :
    (a ++ l.toArray)[a.size + k]! = l[k]?.getD default := by
  simp only [getElem!_eq, Array.getElem?_append_right (show a.size ≤ a.size + k by omega),
    Nat.add_sub_cancel_left, List.getElem?_toArray]

private theorem stored_congr {lits lits' coeffs coeffs' : Array ℕ} {r : CRec}
    (hk : ∀ k, r.start ≤ k → k < r.start + r.size →
      lits'[k]! = lits[k]! ∧ coeffs'[k]! = coeffs[k]!) :
    stored lits' coeffs' r = stored lits coeffs r ∧ scodes lits' r = scodes lits r := by
  constructor
  · unfold stored
    refine List.map_congr_left fun k hk' => ?_
    have := hk (r.start + k) (by omega) (by simp at hk'; omega)
    rw [this.1, this.2]
  · unfold scodes
    refine List.map_congr_left fun k hk' => ?_
    rw [(hk (r.start + k) (by omega) (by simp at hk'; omega)).1]

private theorem rep_congr {vars lits lits' coeffs coeffs' : Array ℕ} {r : CRec} {pc : PBConstr}
    (hr : Rep vars lits coeffs r pc) (h1 : stored lits' coeffs' r = stored lits coeffs r)
    (h2 : scodes lits' r = scodes lits r) : Rep vars lits' coeffs' r pc where
  degree := hr.degree
  lt := h2 ▸ hr.lt
  codes := h2 ▸ hr.codes
  terms := h1 ▸ hr.terms
  clause := hr.clause

private theorem pairsL_append : ∀ (A : List ℕ), A.length % 2 = 0 → ∀ B : List (ℕ × ℕ),
    pairsL (A ++ flatL B) = pairsL A ++ B
  | [], _, B => pairsL_flatL B
  | [_], h, _ => by simp at h
  | a :: b :: A, h, B => by
    simp only [List.cons_append, pairsL, List.cons_append, List.cons.injEq, true_and]
    exact pairsL_append A (by simp at h; omega) B

private theorem length_flatL : ∀ B : List (ℕ × ℕ), (flatL B).length = 2 * B.length
  | [] => rfl
  | p :: B => by simp [flatL, length_flatL B]; omega

private theorem wsum_append {os : Array ℕ} {A : List ℕ} {B : List (ℕ × ℕ)}
    (hos : os.toList = A ++ flatL B) (hA : A.length % 2 = 0) (c : ℕ) :
    wsum c os = (((pairsL A).filter (·.1 == c)).map (·.2)).sum +
      ((B.filter (·.1 == c)).map (·.2)).sum := by
  simp [wsum, hos, pairsL_append A hA B]

private theorem stored_new (s : EState) (ts : Array (ℕ × ℕ)) (r : CRec)
    (hst : r.start = s.lits.size) (hsz : r.size = ts.size) (hc : s.coeffs.size = s.lits.size) :
    stored (s.lits ++ (ts.toList.map Prod.snd).toArray)
      (s.coeffs ++ (ts.toList.map Prod.fst).toArray) r = ts.toList ∧
    scodes (s.lits ++ (ts.toList.map Prod.snd).toArray) r = ts.toList.map Prod.snd := by
  constructor
  · apply List.ext_getElem (by simp [stored, hsz])
    intro k h1 h2
    simp only [stored, List.getElem_map, List.getElem_range, hst]
    rw [append_get_right, ← hc, append_get_right]
    have hk : k < ts.toList.length := by simpa [stored, hsz] using h1
    simp [List.getElem?_eq_getElem hk]
  · apply List.ext_getElem (by simp [scodes, hsz])
    intro k h1 h2
    simp only [scodes, List.getElem_map, List.getElem_range, hst]
    rw [append_get_right]
    have hk : k < ts.toList.length := by simpa [scodes, hsz] using h1
    simp [List.getElem?_eq_getElem hk]

private theorem pushCons_spec {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    {ts : Array (ℕ × ℕ)} {pc : PBConstr} {d : ℕ} {s0 : ℤ} {cl : Bool} {hh : Hint}
    (hts : (ts.toList.map fun p => (p.1, dec s.vars p.2)).Perm (posTerms pc))
    (hlt : ∀ p ∈ ts, p.2 < 2 * s.vars.size) (hd : d = pc.degree)
    (hcl : cl = true → 0 < pc.degree ∧ 2 ≤ ts.size ∧ (coeffSum pc.terms : ℤ) - pc.degree ≤ s0) :
    let r := s.pushCons ts d s0 cl hh
    r.2 = s.cons.size ∧
    (∃ alive lits coeffs slack rootReason occ,
      r.1 = { s with cons := s.cons.push (CRec.mk s.lits.size ts.size d s0 cl hh)
                     cpos := s.cpos.push s.lits.size
                     alive := alive
                     lits := lits
                     coeffs := coeffs
                     slack := slack
                     rootReason := rootReason
                     occ := occ }) ∧
    InvCore r.1 (Function.update G s.cons.size (some pc)) ∧
    (∀ c, c < s.cons.size → r.1.slack[c]! = s.slack[c]!) ∧
    ((stored r.1.lits r.1.coeffs r.1.cons[r.2]!).map fun p => (p.1, dec s.vars p.2)).Perm
      (posTerms pc) ∧
    (∀ ℓ : ℕ, r.2 ∉ r.1.watches[ℓ]!) ∧
    (∀ j, j ≠ s.cons.size → r.1.rootReason.get! j = s.rootReason.get! j) ∧
    r.1.lits.size = s.lits.size + ts.size ∧
    (∀ k, k < s.lits.size → r.1.lits[k]! = s.lits[k]! ∧ r.1.coeffs[k]! = s.coeffs[k]!) ∧
    ∀ ℓ : ℕ, ∃ B : List (ℕ × ℕ), r.1.occ[ℓ]!.toList = s.occ[ℓ]!.toList ++ flatL B ∧
      (∀ p ∈ B, p.1 = s.cons.size) ∧
      B.length = if (!cl && decide (0 < d)) = true then (ts.toList.filter (·.2 == ℓ)).length
        else 0 := by
  dsimp only
  rw [pushCons_eq]
  dsimp only
  have hI := h.cons_pos
  have hcs := h.coeffs_size
  have hend := end_le h
  have hasz := h.alive_size
  have hrsz := h.rr_size
  have hocc : ∀ a ∈ ts.toList, a.2 < s.occ.size := fun a ha => by
    rw [h.occ_size]; exact hlt a (by simpa using ha)
  have hoccL : ∀ ℓ : ℕ, (if (!cl && decide (0 < d)) = true then
      occFold s.cons.size ts.toList s.occ else s.occ)[ℓ]!.toList =
      s.occ[ℓ]!.toList ++ flatL (if (!cl && decide (0 < d)) = true then
        (ts.toList.filter (·.2 == ℓ)).map (fun a => (s.cons.size, a.1)) else []) := by
    intro ℓ; split
    · exact occFold_get _ _ _ hocc ℓ
    · simp [flatL]
  have hnew := stored_new s ts ⟨s.lits.size, ts.size, d, s0, cl, hh⟩ rfl rfl hcs
  have hold : ∀ c, 1 ≤ c → c < s.cons.size →
      stored (s.lits ++ (ts.toList.map Prod.snd).toArray)
        (s.coeffs ++ (ts.toList.map Prod.fst).toArray) s.cons[c]! =
        stored s.lits s.coeffs s.cons[c]! ∧
      scodes (s.lits ++ (ts.toList.map Prod.snd).toArray) s.cons[c]! = scodes s.lits s.cons[c]! :=
    fun c h1 h2 => stored_congr fun k _ hk2 =>
      ⟨append_get_left _ _ (by have := hend c h1 h2; omega),
        append_get_left _ _ (by have := hend c h1 h2; omega)⟩
  have hpos : ∀ c pc', G c = some pc' → 1 ≤ c ∧ c < s.cons.size := fun c pc' hc => by
    have hl := (h.live c).1 (by simp [hc])
    refine ⟨?_, hl.1⟩
    by_contra h0
    have : c = 0 := by omega
    subst this; exact hl.2 h.alive0
  have hcp : ∀ c, c < s.cons.size →
      (s.cons.push (CRec.mk s.lits.size ts.size d s0 cl hh))[c]! = s.cons[c]! := fun c hc => by
    rw [getElem!_push, ite_neg (show ¬c = s.cons.size by omega)]
  have hap : ∀ c, c ≠ s.cons.size →
      (EState.setPush s.alive s.cons.size 1).get! c = s.alive.get! c := fun c hc => by
    rw [setPush_get _ _ _ hasz, ite_neg hc]
  refine ⟨rfl, ⟨_, _, _, _, _, _, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact {
      nodup := h.nodup
      idx_some := h.idx_some
      idx_mem := h.idx_mem
      asg := h.asg
      watches_size := h.watches_size
      occ_size := by split <;> simp [occFold_size, h.occ_size]
      qhead_le := h.qhead_le
      cons_pos := by simp
      cpos_size := by simp [h.cpos_size]
      slack_size := by simp [h.slack_size]
      alive_size := by rw [setPush_size]; simp only [Array.size_push]; split <;> omega
      rr_size := by rw [setPush_size]; simp only [Array.size_push]; split <;> omega
      coeffs_size := by simp [hcs]
      layout := by
        intro c h1 h2
        simp only [Array.size_push] at h2 ⊢
        by_cases hc : c = s.cons.size
        · subst hc
          simp only [getElem!_push, ↓reduceIte, Array.size_append, List.size_toArray,
            List.length_map, Array.length_toList, Nat.lt_irrefl, h.cpos_size, and_true]
        · have hc' : c < s.cons.size := by omega
          rw [getElem!_push, ite_neg hc, getElem!_push,
            ite_neg (by rw [h.cpos_size]; exact hc)]
          obtain ⟨l1, l2⟩ := h.layout c h1 hc'
          refine ⟨l1, ?_⟩
          rw [l2, getElem!_push]
          by_cases hc1 : c + 1 = s.cons.size
          · simp [hc1, h.cpos_size]
          · simp only [hc1, h.cpos_size, show c + 1 < s.cons.size by omega, ↓reduceIte,
              show c + 1 < s.cons.size + 1 by omega]
      alive0 := by
        rw [hap 0 (by omega)]; exact h.alive0
      live := by
        intro c
        rw [Function.update_apply, setPush_get _ _ _ hasz]
        by_cases hc : c = s.cons.size
        · subst hc; simp
        · simp only [hc, ↓reduceIte, Array.size_push]
          rw [h.live c]
          constructor
          · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
          · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
      rep := by
        intro c pc' hc
        rw [Function.update_apply] at hc
        split at hc
        · rename_i hci
          subst hci
          cases hc
          simp only [getElem!_push, ↓reduceIte]
          exact {
            degree := hd
            lt := fun ℓ hℓ => by
              rw [hnew.2] at hℓ
              obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hℓ
              exact hlt q (by simpa using hq)
            codes := by
              rw [hnew.2]
              simpa [List.map_map, Function.comp_def] using hts.map Prod.snd
            terms := fun _ => by rw [hnew.1]; exact hts
            clause := fun hc => hcl hc }
        · obtain ⟨h1, h2⟩ := hpos c pc' hc
          rw [hcp c h2]
          obtain ⟨e1, e2⟩ := hold c h1 h2
          exact rep_congr (h.rep c pc' hc) e1 e2
      occ_even := fun ℓ => by
        rw [← Array.length_toList, hoccL, List.length_append, length_flatL,
          Array.length_toList]
        have := h.occ_even ℓ
        omega
      occ_name := by
        intro ℓ p hp
        rw [hoccL ℓ, pairsL_append _ (by simpa using h.occ_even ℓ)] at hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨h1, h2⟩ := h.occ_name ℓ p hp
          refine ⟨by simp; omega, fun ha => ?_⟩
          rw [hap p.1 (by omega)] at ha
          rw [hcp p.1 h1]
          exact h2 ha
        · split at hp
          · rename_i hreg
            simp only [List.mem_map, List.mem_filter] at hp
            obtain ⟨a, _, rfl⟩ := hp
            refine ⟨by simp, fun _ => ?_⟩
            simpa [getElem!_push, reg] using hreg
          · simp at hp
      occ_exact := by
        intro c pc' hc hreg ℓ
        rw [wsum_append (hoccL ℓ) (by simpa using h.occ_even ℓ)]
        rw [Function.update_apply] at hc
        split at hc
        · rename_i hci
          subst hci
          cases hc
          simp only [getElem!_push, ↓reduceIte, reg] at hreg ⊢
          rw [hnew.1]
          have h0 : ((pairsL s.occ[ℓ]!.toList).filter (·.1 == s.cons.size)) = [] :=
            List.filter_eq_nil_iff.2 fun q hq => by
              have := (h.occ_name ℓ q hq).1
              simp only [beq_iff_eq]; omega
          simp [hreg, h0, List.filter_map, Function.comp_def]
        · obtain ⟨h1, h2⟩ := hpos c pc' hc
          rw [hcp c h2] at hreg ⊢
          rw [(hold c h1 h2).1, ← h.occ_exact c pc' hc hreg ℓ]
          have hB : ((if (!cl && decide (0 < d)) = true then
              (ts.toList.filter (·.2 == ℓ)).map (fun a => (s.cons.size, a.1)) else []).filter
                (·.1 == c)) = [] := by
            split
            · exact List.filter_eq_nil_iff.2 fun q hq => by
                obtain ⟨a, _, rfl⟩ := List.mem_map.1 hq
                simp only [beq_iff_eq]; omega
            · rfl
          rw [hB]; simp [wsum]
      watch_name := by
        intro ℓ c hc
        obtain ⟨h1, h2⟩ := h.watch_name ℓ c hc
        refine ⟨by simp; omega, ?_⟩
        rw [hcp c h1]; exact h2
      watch_count := by
        intro c pc' hc hcl ℓ
        rw [Function.update_apply] at hc
        split at hc
        · rename_i hci
          subst hci
          rw [Array.count_eq_zero_of_not_mem fun hm => by
            have := (h.watch_name ℓ _ hm).1; omega]
          exact Nat.zero_le _
        · obtain ⟨h1, h2⟩ := hpos c pc' hc
          rw [hcp c h2] at hcl ⊢
          have hsz2 := ((h.rep c pc' hc).clause hcl).2.1
          have he := hend c h1 h2
          rw [append_get_left _ _ (by omega), append_get_left _ _ (by omega)]
          exact h.watch_count c pc' hc hcl ℓ
      roots := fun i hi => by
        obtain ⟨h1, h2⟩ := h.roots i hi
        refine ⟨by simp; omega, ?_⟩
        rw [hcp i h1]; exact h2 }
  · intro c hc
    rw [getElem!_push, ite_neg (by rw [h.slack_size]; omega)]
  · simp only [getElem!_push, ↓reduceIte]
    rw [hnew.1]; exact hts
  · intro ℓ hm
    have := (h.watch_name ℓ _ hm).1
    omega
  · intro j hj
    rw [setPush_get _ _ _ hrsz, ite_neg hj]
  · simp
  · intro k hk
    exact ⟨append_get_left _ _ hk, append_get_left _ _ (by omega)⟩
  · intro ℓ
    refine ⟨_, hoccL ℓ, ?_, ?_⟩
    · split
      · intro q hq
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hq
        rfl
      · simp
    · split <;> simp

/-- One step of the loop of `checkFresh` choosing the watches of a clause, on its term array. -/
private def cfStep (V : ByteArray) (p : ℕ) (st : Array ℕ × ℕ) (k : ℕ) : Array ℕ × ℕ :=
  if (decide (st.2 < 2) && litVal V st.1[p + k]! != 2) = true then
    (st.1.swapIfInBounds (p + st.2) (p + k), st.2 + 1) else st

private theorem cf_forIn (p : ℕ) : ∀ (l : List ℕ) (st : EState × ℕ),
    forIn (m := Id) l st (fun k (st : EState × ℕ) =>
      if (decide (st.2 < 2) && litVal st.1.asg.value st.1.lits[p + k]! != 2) = true then
        pure (ForInStep.yield
          ({ st.1 with lits := st.1.lits.swapIfInBounds (p + st.2) (p + k) }, st.2 + 1))
      else pure (ForInStep.yield (st.1, st.2))) =
      pure ({ st.1 with lits := (l.foldl (cfStep st.1.asg.value p) (st.1.lits, st.2)).1 },
        (l.foldl (cfStep st.1.asg.value p) (st.1.lits, st.2)).2)
  | [], st => rfl
  | k :: l, st => by
    rw [List.forIn_cons, List.foldl_cons]
    by_cases hc : (decide (st.2 < 2) && litVal st.1.asg.value st.1.lits[p + k]! != 2) = true
    · simp only [hc, ↓reduceIte, pure_bind, cf_forIn p l]
      rw [show cfStep st.1.asg.value p (st.1.lits, st.2) k =
        (st.1.lits.swapIfInBounds (p + st.2) (p + k), st.2 + 1) by simp [cfStep, hc]]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, cf_forIn p l]
      rw [show cfStep st.1.asg.value p (st.1.lits, st.2) k = (st.1.lits, st.2) by
        simp [cfStep, hc]]

private theorem ite_pos {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

/-- The codes at positions `[p, p + k)`. -/
private def seg (L : Array ℕ) (p k : ℕ) : List ℕ := (List.range k).map fun t => L[p + t]!

private theorem seg_succ (L : Array ℕ) (p k : ℕ) :
    seg L p (k + 1) = seg L p k ++ [L[p + k]!] := by
  simp [seg, List.range_succ]

/-- The invariant of the watch-selection loop of `checkFresh` after `k` positions, from the term
array `L0`: only positions `[p, p + k)` moved, and among themselves; the first `j` hold literals
that are not false, and if `j < 2` the others are false. -/
private structure CfInv (V : ByteArray) (L0 : Array ℕ) (p k : ℕ) (st : Array ℕ × ℕ) :
    Prop where
  size : st.1.size = L0.size
  out : ∀ q, (q < p ∨ p + k ≤ q) → st.1[q]! = L0[q]!
  perm : (seg st.1 p k).Perm (seg L0 p k)
  jle : st.2 ≤ k ∧ st.2 ≤ 2
  nf : ∀ t, t < st.2 → litVal V st.1[p + t]! ≠ 2
  fl : st.2 < 2 → ∀ t, st.2 ≤ t → t < k → litVal V st.1[p + t]! = 2

private theorem cfInv_step {V : ByteArray} {L0 : Array ℕ} {p k : ℕ} {st : Array ℕ × ℕ}
    (hk : p + k < L0.size) (hI : CfInv V L0 p k st) :
    CfInv V L0 p (k + 1) (cfStep V p st k) := by
  obtain ⟨L, j⟩ := st
  obtain ⟨hsz, hout, hperm, ⟨hjk, hj2⟩, hnf, hfl⟩ := hI
  dsimp only at hsz hout hperm hjk hj2 hnf hfl
  have hLk : L[p + k]! = L0[p + k]! := hout _ (Or.inr (le_refl _))
  have hpk : (seg L p (k + 1)).Perm (seg L0 p (k + 1)) := by
    rw [seg_succ, seg_succ, hLk]
    exact hperm.append_right _
  unfold cfStep
  by_cases hc : (decide (j < 2) && litVal V L[p + k]! != 2) = true
  · rw [ite_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨hj, hnk⟩ := hc
    have hpj : p + j < L.size := by omega
    have hpk' : p + k < L.size := by omega
    have hget := get_swap L hpj hpk'
    let σ : ℕ → ℕ := fun t => if t = j then k else if t = k then j else t
    have hσ : ∀ t, (L.swapIfInBounds (p + j) (p + k))[p + t]! = L[p + σ t]! := by
      intro t
      rw [hget]
      simp only [σ]
      by_cases h1 : t = j
      · subst h1; simp
      · by_cases h2 : t = k
        · subst h2; simp [h1]
        · simp [h1, h2]
    have hσinj : Function.Injective σ := by
      intro a b hab
      simp only [σ] at hab
      split_ifs at hab <;> omega
    have hσperm : ((List.range (k + 1)).map σ).Perm (List.range (k + 1)) := by
      rw [List.perm_ext_iff_of_nodup ((List.nodup_range).map hσinj) List.nodup_range]
      intro x
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨t, ht, rfl⟩
        simp only [σ]; split_ifs <;> omega
      · intro hx
        refine ⟨σ x, ?_, ?_⟩
        · simp only [σ]; split_ifs <;> omega
        · simp only [σ]; split_ifs <;> omega
    refine ⟨by simp [hsz], ?_, ?_, ⟨by omega, by omega⟩, ?_, ?_⟩
    · intro q hq
      dsimp only
      rw [hget, ite_neg (show ¬q = p + j by omega), ite_neg (show ¬q = p + k by omega)]
      exact hout q (by omega)
    · dsimp only
      refine List.Perm.trans ?_ hpk
      have : seg (L.swapIfInBounds (p + j) (p + k)) p (k + 1) =
          ((List.range (k + 1)).map σ).map fun t => L[p + t]! := by
        rw [List.map_map]
        exact List.map_congr_left fun t _ => hσ t
      rw [this]
      exact hσperm.map _
    · intro t ht
      dsimp only at ht ⊢
      rw [hσ t]
      simp only [σ]
      by_cases h1 : t = j
      · simp only [h1, ↓reduceIte]; exact hnk
      · have : t < j := by omega
        simp only [h1, show t ≠ k by omega, ↓reduceIte]; exact hnf t this
    · intro hj1 t ht1 ht2
      dsimp only at hj1 ht1 ht2 ⊢
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hσ t]
      simp only [σ]
      by_cases h2 : t = k
      · rw [h2]
        simp only [show k ≠ 0 by omega, ↓reduceIte]
        exact hfl (by omega) 0 (le_refl _) (by omega)
      · simp only [show t ≠ 0 by omega, h2, ↓reduceIte]
        exact hfl (by omega) t (by omega) (by omega)
  · rw [ite_neg hc]
    refine ⟨hsz, fun q hq => hout q (by omega), hpk, ⟨by omega, hj2⟩, hnf, ?_⟩
    intro hj t ht1 ht2
    by_cases htk : t = k
    · subst htk
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
        Decidable.not_not] at hc
      exact hc hj
    · exact hfl hj t ht1 (by omega)

private theorem cfInv_fold {V : ByteArray} {L0 : Array ℕ} {p : ℕ} :
    ∀ k, p + k ≤ L0.size →
      CfInv V L0 p k ((List.range k).foldl (cfStep V p) (L0, 0))
  | 0, _ => ⟨rfl, fun _ _ => rfl, List.Perm.refl _, ⟨le_refl _, Nat.zero_le 2⟩,
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact cfInv_step (by omega) (cfInv_fold k (by omega))

private theorem end_le_start {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) :
    ∀ d c, 1 ≤ c → c + d + 1 < s.cons.size →
      s.cons[c]!.start + s.cons[c]!.size ≤ s.cons[c + d + 1]!.start := by
  intro d
  induction d with
  | zero =>
    intro c h1 h2
    rw [(h.layout c h1 (by omega)).2, ite_pos (show c + 1 < s.cons.size by omega),
      (h.layout (c + 1) (by omega) h2).1]
  | succ d ih =>
    intro c h1 h2
    have := ih c h1 (by omega)
    have h3 := (h.layout (c + d + 1) (by omega) (by omega)).2
    rw [ite_pos (show c + d + 1 + 1 < s.cons.size by omega)] at h3
    have h4 := (h.layout (c + d + 1 + 1) (by omega) (by omega)).1
    rw [show c + (d + 1) + 1 = c + d + 1 + 1 by omega, h4]
    omega

private theorem modify_push_get (W : Array (Array ℕ)) (a x ℓ : ℕ) :
    (W.modify a (·.push x))[ℓ]! = if a = ℓ ∧ ℓ < W.size then W[ℓ]!.push x else W[ℓ]! := by
  simp only [getElem!_eq, Array.getElem?_modify]
  by_cases h1 : a = ℓ
  · subst h1
    by_cases h2 : a < W.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

private theorem filter_perm {vars : Array ℕ} {L : List ℕ} {P : List (ℕ × Literal ℕ)}
    (hP : (L.map (dec vars)).Perm (P.map (·.2))) (q : Literal ℕ → Bool) :
    ((P.filter fun t => q t.2).map (·.2)).Perm
      ((L.filter fun ℓ => q (dec vars ℓ)).map (dec vars)) := by
  rw [show (P.filter fun t => q t.2).map (·.2) = (P.map (·.2)).filter q by
      rw [List.filter_map]; rfl,
    show (L.filter fun ℓ => q (dec vars ℓ)).map (dec vars) = (L.map (dec vars)).filter q by
      rw [List.filter_map]; rfl]
  exact hP.symm.filter q

/-- A unit clause: when exactly one stored code is not false, its literal is forced. -/
private theorem unit {vars : Array ℕ} {a : Asg} {L coeffs : Array ℕ} {r : CRec}
    {pc : PBConstr} {w : ℕ} (hv : vars.toList.Nodup) (ha : AsgOk vars.size a)
    (hrep : Rep vars L coeffs r pc) (hcl : r.clause = true)
    (hf : (scodes L r).filter (fun ℓ => a.value.get! ℓ != 2) = [w]) :
    ∃ x, (x, dec vars w) ∈ pc.terms ∧
      VeriPB.slack (tlits vars a.trail a.trail.size) pc < x := by
  have hq : ∀ ℓ ∈ scodes L r, (a.value.get! ℓ != 2) =
      !falsified (tlits vars a.trail a.trail.size) (0, dec vars ℓ) := by
    intro ℓ hℓ
    have hlt := hrep.lt ℓ hℓ
    rw [falsified_dec hv ha.trail_lt hlt, List.take_of_length_le (by simp), ha.value_eq ℓ hlt]
    have hboth : ℓ ∈ a.trail → ℓ ^^^ 1 ∉ a.trail := by
      intro h1 h2
      have hne := xor_one_ne ℓ
      have hd := xor_one_div_two ℓ
      obtain ⟨i1, hi1, e1⟩ := List.getElem_of_mem (Array.mem_def.1 h1)
      obtain ⟨i2, hi2, e2⟩ := List.getElem_of_mem (Array.mem_def.1 h2)
      have := (List.Nodup.getElem_inj_iff ha.nodup (i := i1) (j := i2) (hi := by simpa using hi1)
        (hj := by simpa using hi2)).1 (by simp [e1, e2, hd])
      subst this
      exact hne (e2.symm.trans e1)
    by_cases h1 : ℓ ∈ a.trail
    · have h2 := hboth h1
      simp only [h1, ↓reduceIte, Array.mem_toList_iff, h2, decide_false]
      rfl
    · simp only [h1, ↓reduceIte, Array.mem_toList_iff]
      by_cases h2 : ℓ ^^^ 1 ∈ a.trail
      · simp only [h2, ↓reduceIte, decide_true]; rfl
      · simp only [h2, ↓reduceIte, decide_false]; rfl
  have hfilt : (scodes L r).filter (fun ℓ =>
      !falsified (tlits vars a.trail a.trail.size) (0, dec vars ℓ)) = [w] := by
    rw [← hf]; exact List.filter_congr fun ℓ hℓ => (hq ℓ hℓ).symm
  have hp := filter_perm hrep.codes
    (fun l => !(tlits vars a.trail a.trail.size).contains (Std.Sat.Literal.negate l))
  rw [show (scodes L r).filter (fun ℓ => !(tlits vars a.trail a.trail.size).contains
      (Std.Sat.Literal.negate (dec vars ℓ))) = [w] from hfilt] at hp
  rw [List.map_cons, List.map_nil, List.perm_singleton, List.map_eq_singleton_iff] at hp
  obtain ⟨t, ht, htw⟩ := hp
  have htm : t ∈ (posTerms pc).filter fun t =>
      !(tlits vars a.trail a.trail.size).contains (Std.Sat.Literal.negate t.2) := by
    rw [ht]; exact List.mem_singleton_self _
  refine ⟨t.1, ?_, ?_⟩
  · have := (List.mem_filter.1 (List.mem_filter.1 htm).1).1
    rw [← htw]; exact this
  · rw [slack_posTerms]
    have : ((posTerms pc).filter fun t =>
        !falsified (tlits vars a.trail a.trail.size) t) = [t] := ht
    rw [this]
    have := (hrep.clause hcl).1
    simp only [coeffSum_cons, coeffSum_nil]
    omega

private theorem inv_asg {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) {a' : Asg}
    (ha : AsgOk s.vars.size a') (he : AsgExt s.asg a') : InvCore { s with asg := a' } G :=
  { h with
    asg := ha
    qhead_le := le_trans h.qhead_le he.size_le }

private theorem tlits_prefix {vars t t' : Array ℕ} (hp : t.toList <+: t'.toList) {k : ℕ}
    (hk : k ≤ t.size) : tlits vars t' k = tlits vars t k := by
  unfold tlits
  rw [List.prefix_iff_eq_take.1 hp, List.take_take, Nat.min_eq_left (by simpa using hk)]

private theorem slack_asg {s : EState} {G : ℕ → Option PBConstr}
    (hs : ∀ c pc, G c = some pc → reg s.cons[c]! = true →
      s.slack[c]! = VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc)
    {a' : Asg} (he : AsgExt s.asg a') (hq : s.qhead ≤ s.asg.trail.size) :
    SlackOk { s with asg := a' } G := by
  intro c pc hc hreg
  rw [hs c pc hc hreg]
  dsimp only
  rw [tlits_prefix he.1 hq]

private theorem checkFresh_spec {s : EState} {G : ℕ → Option PBConstr} {i : ℕ} {pc : PBConstr}
    (h : InvCore s G)
    (hs : ∀ c pc', G c = some pc' → reg s.cons[c]! = true → c ≠ i →
      s.slack[c]! = VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc')
    (hG : G i = some pc) (hlast : i + 1 = s.cons.size)
    (hal : ((stored s.lits s.coeffs s.cons[i]!).map fun p => (p.1, dec s.vars p.2)).Perm
      (posTerms pc))
    (hw : ∀ ℓ : ℕ, i ∉ s.watches[ℓ]!) :
    let r := s.checkFresh i
    (∃ lits watches slack asg, r.1 = { s with lits, watches, slack, asg }) ∧
    InvCore r.1 G ∧ SlackOk r.1 G ∧ AsgExt s.asg r.1.asg ∧
    ChainFrom s.vars G s.asg.trail.size r.1.asg ∧
    ∀ k, r.2 = some k →
      ∃ pc, G k = some pc ∧
        VeriPB.slack (tlits s.vars r.1.asg.trail r.1.asg.trail.size) pc < 0 := by
  dsimp only
  have hl := (h.live i).1 (by simp [hG])
  have hrep := h.rep i pc hG
  have hsl := freshSlack_eq h hal hrep.lt hrep.degree
  have hanti :=
    slack_anti (tlits_take_sub (vars := s.vars) (trail := s.asg.trail) (k := s.qhead)) pc
  have hsize : s.slack.size = s.cons.size := h.slack_size
  unfold EState.checkFresh
  simp only [Id.run]
  rw [hsl]
  generalize hX : VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc = X at hanti ⊢
  split
  · rename_i hcl
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', cf_forIn, pure_bind]
    have hrs : [:s.cons[i]!.size].size = s.cons[i]!.size := by simp [Std.Legacy.Range.size]
    rw [hrs, ← List.range_eq_range']
    have hi1 : 1 ≤ i := by
      by_contra h0
      have : i = 0 := by omega
      subst this; exact hl.2 h.alive0
    have hend := end_le h i hi1 hl.1
    obtain ⟨_, hsz2, _⟩ := hrep.clause hcl
    have hF := cfInv_fold (V := s.asg.value) (L0 := s.lits) (p := s.cons[i]!.start)
      s.cons[i]!.size hend
    generalize List.foldl (cfStep s.asg.value s.cons[i]!.start) (s.lits, 0)
      (List.range s.cons[i]!.size) = F at hF ⊢
    obtain ⟨L, j⟩ := F
    obtain ⟨hLsz, hLout, hLperm, hjle, hLnf, hLfl⟩ := hF
    dsimp only at hLsz hLout hLperm hjle hLnf hLfl ⊢
    have hrepL : Rep s.vars L s.coeffs s.cons[i]! pc :=
      { degree := hrep.degree
        lt := fun ℓ hℓ => hrep.lt ℓ (hLperm.mem_iff.1 hℓ)
        codes := (hLperm.map _).trans hrep.codes
        terms := fun hc => by rw [hcl] at hc; cases hc
        clause := hrep.clause }
    have hpos : ∀ c pc', G c = some pc' → 1 ≤ c ∧ c < s.cons.size := fun c pc' hc => by
      have hl' := (h.live c).1 (by simp [hc])
      refine ⟨?_, hl'.1⟩
      by_contra h0
      have : c = 0 := by omega
      subst this; exact hl'.2 h.alive0
    have hold : ∀ c pc', G c = some pc' → c ≠ i →
        stored L s.coeffs s.cons[c]! = stored s.lits s.coeffs s.cons[c]! ∧
        scodes L s.cons[c]! = scodes s.lits s.cons[c]! ∧
        s.cons[c]!.start + s.cons[c]!.size ≤ s.cons[i]!.start := by
      intro c pc' hc hci
      obtain ⟨h1, h2⟩ := hpos c pc' hc
      have he := end_le_start h (i - c - 1) c h1 (by omega)
      rw [show c + (i - c - 1) + 1 = i by omega] at he
      have := stored_congr (lits := s.lits) (lits' := L) (coeffs := s.coeffs)
        (coeffs' := s.coeffs) (r := s.cons[c]!) fun k _ hk2 => ⟨hLout k (Or.inl (by omega)), rfl⟩
      exact ⟨this.1, this.2, he⟩
    have hw0 : L[s.cons[i]!.start]! < 2 * s.vars.size :=
      hrepL.lt _ (List.mem_map.2 ⟨0, by simp; omega, rfl⟩)
    have hw1 : L[s.cons[i]!.start + 1]! < 2 * s.vars.size :=
      hrepL.lt _ (List.mem_map.2 ⟨1, by simp; omega, rfl⟩)
    have hregi : reg s.cons[i]! = false := by simp [reg, hcl]
    let w0 := L[s.cons[i]!.start]!
    let w1 := L[s.cons[i]!.start + 1]!
    have hinv : InvCore { s with
        lits := L
        watches := (s.watches.modify w0 (·.push i)).modify w1 (·.push i) } G := by
      have hW2 : ∀ (ℓ c : ℕ),
          (((s.watches.modify w0 (·.push i)).modify w1 (·.push i))[ℓ]!).count c =
          (s.watches[ℓ]!).count c + if c = i then [w0, w1].count ℓ else 0 := by
        intro ℓ c
        have hs0 : w0 < s.watches.size := by rw [h.watches_size]; exact hw0
        have hs1 : w1 < s.watches.size := by rw [h.watches_size]; exact hw1
        rw [modify_push_get, modify_push_get, Array.size_modify]
        by_cases h0 : w0 = ℓ
        · have hl0 : ℓ < s.watches.size := h0 ▸ hs0
          by_cases h1 : w1 = ℓ
          · by_cases hci : c = i
            · simp [h0, h1, hci, hl0]
            · simp [h0, h1, hci, Ne.symm hci, hl0]
          · by_cases hci : c = i
            · simp [h0, h1, hci, hl0]
            · simp [h0, h1, hci, Ne.symm hci, hl0]
        · by_cases h1 : w1 = ℓ
          · have hl1 : ℓ < s.watches.size := h1 ▸ hs1
            by_cases hci : c = i
            · simp [h0, h1, hci, hl1]
            · simp [h0, h1, hci, Ne.symm hci, hl1]
          · by_cases hci : c = i <;> simp [h0, h1, hci]
      exact { h with
        watches_size := by simp [h.watches_size]
        coeffs_size := h.coeffs_size.trans hLsz.symm
        layout := fun c h1 h2 => by
          have := h.layout c h1 h2
          rw [← hLsz] at this
          exact this
        rep := fun c pc' hc => by
          by_cases hci : c = i
          · subst hci; rw [hG] at hc; cases hc; exact hrepL
          · obtain ⟨e1, e2, -⟩ := hold c pc' hc hci
            exact rep_congr (h.rep c pc' hc) e1 e2
        occ_exact := fun c pc' hc hreg ℓ => by
          have hci : c ≠ i := by rintro rfl; rw [hregi] at hreg; cases hreg
          dsimp only
          rw [(hold c pc' hc hci).1]
          exact h.occ_exact c pc' hc hreg ℓ
        watch_name := fun ℓ c hc => by
          have hm := Array.count_pos_iff.2 hc
          rw [hW2] at hm
          by_cases hci : c = i
          · subst hci; exact ⟨hl.1, hcl⟩
          · rw [ite_neg hci, Nat.add_zero] at hm
            exact h.watch_name ℓ c (Array.count_pos_iff.1 hm)
        watch_count := fun c pc' hc hcl' ℓ => by
          dsimp only
          rw [hW2]
          by_cases hci : c = i
          · subst hci
            rw [Array.count_eq_zero_of_not_mem (hw ℓ), Nat.zero_add, ite_pos rfl]
          · rw [ite_neg hci, Nat.add_zero]
            obtain ⟨-, -, he⟩ := hold c pc' hc hci
            have hsz := ((h.rep c pc' hc).clause hcl').2.1
            rw [hLout _ (Or.inl (by omega)), hLout _ (Or.inl (by omega))]
            exact h.watch_count c pc' hc hcl' ℓ }
    have hslk : ∀ c pc', G c = some pc' → reg s.cons[c]! = true →
        s.slack[c]! = VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc' :=
      fun c pc' hc hreg => hs c pc' hc hreg (by rintro rfl; rw [hregi] at hreg; cases hreg)
    by_cases hX0 : X < 0
    · rw [ite_pos hX0]
      refine ⟨⟨_, _, _, _, rfl⟩, hinv, hslk, AsgExt.refl _, ChainFrom.of_size _ _ _, ?_⟩
      intro k hk
      cases hk
      exact ⟨pc, hG, show VeriPB.slack (tlits s.vars s.asg.trail s.asg.trail.size) pc < 0 by
        omega⟩
    rw [ite_neg hX0]
    by_cases hu : (j == 1 && litVal s.asg.value L[s.cons[i]!.start]! == 0) = true
    · rw [ite_pos hu]
      simp only [Bool.and_eq_true, beq_iff_eq] at hu
      obtain ⟨hj1, h0⟩ := hu
      have h0' : s.asg.value.get! L[s.cons[i]!.start]! = 0 := h0
      have hf : (scodes L s.cons[i]!).filter (fun ℓ => s.asg.value.get! ℓ != 2) =
          [L[s.cons[i]!.start]!] := by
        change (seg L s.cons[i]!.start s.cons[i]!.size).filter _ = _
        obtain ⟨m, hm⟩ : ∃ m, s.cons[i]!.size = m + 1 := ⟨s.cons[i]!.size - 1, by omega⟩
        rw [hm, seg, List.range_succ_eq_map, List.map_cons, List.map_map, List.filter_cons]
        have hnf0 := hLnf 0 (by omega)
        simp only [Nat.add_zero] at hnf0
        have hrest : (List.map ((fun t => L[s.cons[i]!.start + t]!) ∘ Nat.succ)
            (List.range m)).filter (fun ℓ => s.asg.value.get! ℓ != 2) = [] := by
          rw [List.filter_eq_nil_iff]
          intro ℓ hℓ
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hℓ
          have := hLfl (by omega) (t + 1) (by omega) (by simp at ht; omega)
          simp only [Function.comp, Nat.succ_eq_add_one, bne_iff_ne, ne_eq, Decidable.not_not]
          exact this
        simp only [hrest, Nat.add_zero, show (s.asg.value.get! L[s.cons[i]!.start]! != 2) = true by
          simpa [litVal] using hnf0, ↓reduceIte]
      have hF := unit h.nodup h.asg hrepL hcl hf
      have hFor : Forces (tlits s.vars s.asg.trail s.asg.trail.size) pc
          (dec s.vars L[s.cons[i]!.start]!) :=
        ⟨AsgOk.not_mem_of_zero h.asg h.nodup hw0 h0', hF⟩
      obtain ⟨ha', he', -, -⟩ := AsgOk.assign h.asg (r := i) hw0 h0'
      have hch := AsgOk.assign_chain h.asg hw0 h0' hG hFor
      refine ⟨⟨_, _, _, _, rfl⟩, inv_asg hinv ha' he', slack_asg hslk he' h.qhead_le,
        he', hch, ?_⟩
      intro k hk; cases hk
    · rw [ite_neg hu]
      refine ⟨⟨_, _, _, _, rfl⟩, hinv, hslk, AsgExt.refl _, ChainFrom.of_size _ _ _, ?_⟩
      intro k hk; cases hk
  · rename_i hcl
    have hcl' : s.cons[i]!.clause = false := by simpa using hcl
    have hinv : InvCore { s with slack := s.slack.set! i X } G :=
      { h with slack_size := by simp [h.slack_size] }
    have hslk : ∀ c pc', G c = some pc' → reg s.cons[c]! = true →
        (s.slack.set! i X)[c]! = VeriPB.slack (tlits s.vars s.asg.trail s.qhead) pc' := by
      intro c pc' hc hreg
      by_cases hci : c = i
      · subst hci
        rw [hG] at hc; cases hc
        rw [← hX]; exact Array.getElem!_set!_self _ _ _ (by omega)
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hci)]
        exact hs c pc' hc hreg hci
    split
    · rename_i hneg
      refine ⟨⟨_, _, _, _, rfl⟩, hinv, hslk, AsgExt.refl _, ChainFrom.of_size _ _ _, ?_⟩
      intro k hk
      cases hk
      exact ⟨pc, hG, show VeriPB.slack (tlits s.vars s.asg.trail s.asg.trail.size) pc < 0 by omega⟩
    · rename_i hneg
      obtain ⟨ha', he', hch'⟩ := propagatePB_spec (G := G) (sl := X) h.nodup h.asg hrep hcl' hG
        (by omega)
      refine ⟨⟨_, _, _, _, rfl⟩, inv_asg hinv ha' he', slack_asg hslk he' h.qhead_le,
        he', hch', ?_⟩
      intro k hk
      cases hk

/-- One step of `markRootReasons`. -/
private def mark (b : EState) (a : ℕ) : EState :=
  { b with rootReason := b.rootReason.set! b.asg.reason[b.asg.trail[a]! / 2]! 1 }

private theorem markRootReasons_spec (s : EState) (n : ℕ) :
    (∃ rr, s.markRootReasons n = { s with rootReason := rr }) ∧
    (s.markRootReasons n).rootReason.size = s.rootReason.size ∧
    (∀ j, s.rootReason.get! j ≠ 0 → (s.markRootReasons n).rootReason.get! j ≠ 0) ∧
    ∀ k (hk : k < s.asg.trail.size), n ≤ k →
      s.asg.reason[s.asg.trail[k] / 2]! < s.rootReason.size →
      (s.markRootReasons n).rootReason.get! s.asg.reason[s.asg.trail[k] / 2]! ≠ 0 := by
  have key : ∀ (L : List ℕ) (t : EState), t.asg = s.asg →
      ∃ rr, L.foldl mark t = { t with rootReason := rr } ∧ rr.size = t.rootReason.size ∧
        (∀ j, t.rootReason.get! j ≠ 0 → rr.get! j ≠ 0) ∧
        ∀ i ∈ L, s.asg.reason[s.asg.trail[i]! / 2]! < t.rootReason.size →
          rr.get! s.asg.reason[s.asg.trail[i]! / 2]! ≠ 0 := by
    intro L
    induction L with
    | nil => intro t _; exact ⟨t.rootReason, rfl, rfl, fun _ h => h, by simp⟩
    | cons i L ih =>
      intro t ht
      obtain ⟨rr, h1, h2, h3, h4⟩ := ih (mark t i) ht
      simp only [mark] at h1 h2 h3 h4
      refine ⟨rr, by simpa [mark] using h1, by rw [h2, ByteArray.size_set!],
        fun j hj => h3 j ?_, ?_⟩
      · rw [ByteArray.get!_set!]; split <;> simp_all
      · intro i' hi' hlt
        rcases List.mem_cons.1 hi' with rfl | hi'
        · refine h3 _ ?_
          rw [ByteArray.get!_set!, ht]; simp [hlt]
        · exact h4 i' hi' (by rw [ByteArray.size_set!]; exact hlt)
  obtain ⟨rr, h1, h2, h3, h4⟩ := key (List.range' n [n:s.asg.trail.size].size) s rfl
  have hm : s.markRootReasons n = { s with rootReason := rr } := by
    unfold EState.markRootReasons
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
    exact h1
  rw [hm]
  refine ⟨⟨rr, rfl⟩, h2, h3, fun k hk hnk hlt => ?_⟩
  have := h4 k (by simp [List.mem_range'_1, Std.Legacy.Range.size]; omega)
    (by rw [getElem!_pos s.asg.trail k hk]; exact hlt)
  rwa [getElem!_pos s.asg.trail k hk] at this

/-! ### The operations -/

/-- The slack of a constraint is at most the sum of its coefficients less its degree. -/
private theorem slack_le_coeffSum (ρ : List (Literal ℕ)) (c : PBConstr) :
    VeriPB.slack ρ c ≤ (coeffSum c.terms : ℤ) - c.degree := by
  have := slack_anti (ρ := []) (ρ' := ρ) (by simp) c
  have h0 : VeriPB.slack [] c = (coeffSum c.terms : ℤ) - c.degree := by
    simp [VeriPB.slack, falsified]
  omega

/-- A chain of forced trail entries ending in a conflict gives hints that the kernel's
propagation replays to a conflict: the reasons of the entries in trail order, then the
conflicting constraint. -/
private theorem rup_of_chain {vars : Array ℕ} {G : ℕ → Option PBConstr} {a : Asg}
    {cons : Array CRec} {db : List (ℕ × PBConstr)} {neg : PBConstr}
    (hch : ChainFrom vars G 0 a)
    (hres : ∀ c pc, G c = some pc → resolve db neg cons[c]!.hint = some pc)
    {k : ℕ} {pc : PBConstr} (hk : G k = some pc)
    (hsl : VeriPB.slack (tlits vars a.trail a.trail.size) pc < 0) :
    ∃ hs, VeriPB.rupHints db neg hs [] = true := by
  let xs : List (Hint × Literal ℕ) :=
    a.trail.toList.map fun ℓ => (cons[a.reason[ℓ / 2]!]!.hint, dec vars ℓ)
  refine ⟨xs.map (·.1) ++ [cons[k]!.hint], rupHints_of_forces xs [] [] (by simp) ?_ ?_⟩
  · intro j hj
    have hj' : j < a.trail.size := by simpa [xs] using hj
    obtain ⟨pc', hG', hF⟩ := hch j hj' (Nat.zero_le _)
    refine ⟨pc', ?_, ?_⟩
    · simpa [xs] using hres _ _ hG'
    · have : (xs.take j).map (·.2) = tlits vars a.trail j := by
        simp [xs, tlits, List.map_take, Function.comp_def]
      simpa [this, xs] using hF
  · refine ⟨pc, hres _ _ hk, ?_⟩
    have : xs.map (·.2) = tlits vars a.trail a.trail.size := by
      simp [xs, tlits, Function.comp_def]
    simpa [this] using hsl

/-- Extending the trail keeps the structural invariant and the slack counters. -/
private theorem InvCore.asg_ext {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    (hs : SlackOk s G) {a : Asg} (ha : AsgOk s.vars.size a) (he : AsgExt s.asg a) :
    InvCore { s with asg := a } G ∧ SlackOk { s with asg := a } G := by
  have hpre := he.1
  refine ⟨{ h with asg := ha, qhead_le := le_trans h.qhead_le he.size_le }, ?_⟩
  intro c pc hc hr
  rw [hs c pc hc hr]
  congr 1
  obtain ⟨t, ht⟩ := hpre
  simp only [tlits, ← ht]
  rw [List.take_append_of_le_length (by simpa using h.qhead_le)]

/-- The analysis of a conflict changes only the marks. -/
private theorem analyze_fst (s : EState) (k : ℕ) :
    ∃ seen, (s.analyze k).1 = { s with seen } := ⟨_, rfl⟩

/-- **Deleting a constraint** keeps the invariant for the constraints left. -/
private theorem kill_spec {s : EState} {G : ℕ → Option PBConstr} (h : Inv s G) (i : ℕ) :
    Inv (s.kill i) (Function.update G i none) ∧ (s.kill i).cons = s.cons := by
  have hal : ∀ c, (s.alive.set! i 0).get! c = if c = i then 0 else s.alive.get! c := by
    intro c
    rw [ByteArray.get!_set!]
    by_cases hc : c = i
    · subst hc
      by_cases hl : c < s.alive.size
      · simp [hl]
      · simp [hl, ByteArray.get!_ge _ (Nat.le_of_not_lt hl)]
    · simp [hc, Ne.symm hc]
  have hG : ∀ c pc, Function.update G i none c = some pc → c ≠ i ∧ G c = some pc := by
    intro c pc hc
    by_cases hci : c = i
    · subst hci; simp at hc
    · exact ⟨hci, by simpa [Function.update, hci] using hc⟩
  let s' : EState := { s with alive := s.alive.set! i 0 }
  have hcore : InvCore s' (Function.update G i none) :=
    { h.toInvCore with
      alive_size := by simp only [s', ByteArray.size_set!]; exact h.alive_size
      alive0 := by simp only [s', hal]; split <;> simp [h.alive0]
      live := by
        intro c
        simp only [s', hal]
        by_cases hci : c = i
        · subst hci; simp
        · simp only [hci, ↓reduceIte, Function.update, dite_false]
          exact h.live c
      rep := fun c pc hc => h.rep c pc (hG c pc hc).2
      occ_name := by
        intro ℓ p hp
        refine ⟨(h.occ_name ℓ p hp).1, fun hp' => (h.occ_name ℓ p hp).2 ?_⟩
        simp only [s', hal] at hp'
        split at hp' <;> simp_all
      occ_exact := fun c pc hc => h.occ_exact c pc (hG c pc hc).2
      watch_count := fun c pc hc => h.watch_count c pc (hG c pc hc).2 }
  have hslack : SlackOk s' (Function.update G i none) :=
    fun c pc hc => h.slack c pc (hG c pc hc).2
  refine ⟨?_, by unfold EState.kill; dsimp only; split <;> rfl⟩
  unfold EState.kill
  dsimp only
  split
  · exact { hcore with
      slack := hslack
      rootLen := by simp
      rr := by simp
      chain := by simp
      conflict := by simp }
  · rename_i hn
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, not_not] at hn
    refine { hcore with
      slack := hslack
      rootLen := h.rootLen
      rr := h.rr
      chain := fun hd k hk hm => ?_
      conflict := fun hd k hk => ?_ }
    · obtain ⟨pc, hpc, hF⟩ := h.chain hd k hk hm
      refine ⟨pc, ?_, hF⟩
      have : s.asg.reason[s.asg.trail[k] / 2]! ≠ i := fun he =>
        h.rr hd k hk (he ▸ hn.1)
      simpa [Function.update, this] using hpc
    · obtain ⟨pc, hpc, hsl⟩ := h.conflict hd k hk
      have : k ≠ i := fun he => hn.2 (he ▸ hk)
      exact ⟨pc, by simpa [Function.update, this] using hpc, hsl⟩

/-- The state a step of a `for` loop continues with. -/
private def stepVal {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

/-- An invariant of the steps of a `for` loop over a list holds after it. -/
private theorem forIn_list_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β)) :
    ∀ (xs : List α) (init : β), (∀ a ∈ xs, ∀ b, P b → P (stepVal (f a b).run)) → P init →
      P (forIn xs init f).run
  | [], init, _, h0 => by simpa using h0
  | a :: as, init, hf, h0 => by
    rw [List.forIn_cons]
    have := hf a List.mem_cons_self init h0
    cases h : f a init with
    | done b => rw [h] at this; exact this
    | yield b =>
      rw [h] at this
      exact forIn_list_inv P f as b (fun x hx => hf x (List.mem_cons_of_mem _ hx)) this

/-- An invariant of the steps of a `for` loop over an array holds after it. -/
private theorem forIn_array_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (xs : Array α) (init : β) (hf : ∀ a ∈ xs, ∀ b, P b → P (stepVal (f a b).run))
    (h0 : P init) : P (forIn xs init f).run := by
  rw [← Array.forIn_toList]
  exact forIn_list_inv P f xs.toList init (fun a ha => hf a (by simpa using ha)) h0

/-- An invariant of a `for` loop, followed by a continuation. -/
private theorem bind_forIn_inv {α β γ : Type} (P : β → Prop) (Q : γ → Prop) {xs : Array α}
    {init : β} {f : α → β → Id (ForInStep β)} {g : β → Id γ} (h0 : P init)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (stepVal (f a b).run)) (hg : ∀ b, P b → Q (g b).run) :
    Q (forIn xs init f >>= g).run :=
  hg _ (forIn_array_inv P f xs init hf h0)

/-- An invariant of a `for` loop over a list, followed by a continuation. -/
private theorem bind_forIn_list_inv {α β γ : Type} (P : β → Prop) (Q : γ → Prop) {xs : List α}
    {init : β} {f : α → β → Id (ForInStep β)} {g : β → Id γ} (h0 : P init)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (stepVal (f a b).run)) (hg : ∀ b, P b → Q (g b).run) :
    Q (forIn xs init f >>= g).run :=
  hg _ (forIn_list_inv P f xs init hf h0)

/-- **Rebuilding the root level** establishes the invariant. -/
private theorem rebuild_spec {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G)
    (hs : SlackOk s G) :
    Inv s.rebuild G ∧ s.rebuild.cons = s.cons ∧ s.rebuild.dirty = false := by
  obtain ⟨⟨sl0, a0, hb⟩, hbI, hbS, hbt, -⟩ := backtrack_spec h hs (Nat.zero_le s.asg.trail.size)
  unfold EState.rebuild
  simp only [Id.run]
  generalize s.backtrack 0 = s₁ at hb hbI hbS hbt ⊢
  have hcons : s₁.cons = s.cons := by rw [hb]
  have ht0 : s₁.asg.trail.size = 0 := by rw [hbt]; simp
  refine bind_forIn_inv (fun st : EState × Option ℕ => InvCore st.1 G ∧ SlackOk st.1 G ∧
      ChainFrom st.1.vars G 0 st.1.asg ∧
      (∀ k, st.2 = some k → ∃ pc, G k = some pc ∧
        VeriPB.slack (tlits st.1.vars st.1.asg.trail st.1.asg.trail.size) pc < 0) ∧
      st.1.cons = s.cons ∧ st.1.alive = s₁.alive ∧ st.1.rootReason.size = s₁.rootReason.size ∧
      ∀ i ∈ st.1.roots, s₁.alive.get! i ≠ 0)
    (fun r => Inv r G ∧ r.cons = s.cons ∧ r.dirty = false) ?_ ?_ ?_
  · refine ⟨{ hbI with
        rr_size := by simp only [ByteArray.size, Array.size_replicate]; exact hbI.rr_size
        roots := fun i hi => hbI.roots i (Array.mem_filter.1 hi).1 }, hbS, ?_, by simp, hcons, rfl,
      by simp only [ByteArray.size, Array.size_replicate], ?_⟩
    · intro k hk; simp only [ht0] at hk; omega
    · intro i hi; simpa using (Array.mem_filter.1 hi).2
  · rintro i hi ⟨st, cf⟩ ⟨hI, hS, hC, hK, hc, ha, hr, hroots⟩
    simp only at hI hS hC hK hc ha hr hroots ⊢
    have hil := hbI.roots i (Array.mem_filter.1 hi).1
    rw [hcons, ← hc] at hil
    have hal : st.alive.get! i ≠ 0 := by rw [ha]; simpa using (Array.mem_filter.1 hi).2
    obtain ⟨pc, hG⟩ := Option.isSome_iff_exists.1 ((hI.live i).2 ⟨hil.1, hal⟩)
    have hrep := hI.rep i pc hG
    -- The rest of the step: a conflict, or propagation.
    have hprop : ∀ st' : EState, InvCore st' G → SlackOk st' G → ChainFrom st'.vars G 0 st'.asg →
        st'.cons = st.cons → st'.alive = st.alive → st'.rootReason = st.rootReason →
        st'.roots = st.roots →
        InvCore st'.propagate.1 G ∧ SlackOk st'.propagate.1 G ∧
        ChainFrom st'.propagate.1.vars G 0 st'.propagate.1.asg ∧
        (∀ k, st'.propagate.2 = some k → ∃ pc, G k = some pc ∧
          VeriPB.slack (tlits st'.propagate.1.vars st'.propagate.1.asg.trail
            st'.propagate.1.asg.trail.size) pc < 0) ∧
        st'.propagate.1.cons = s.cons ∧ st'.propagate.1.alive = s₁.alive ∧
        st'.propagate.1.rootReason.size = s₁.rootReason.size ∧
        ∀ i ∈ st'.propagate.1.roots, s₁.alive.get! i ≠ 0 := by
      intro st' hI' hS' hC' h1 h2 h3 h4
      obtain ⟨⟨lits, watches, occ, slack, asg, qhead, he⟩, hI'', hS'', hx, hn, -, hk⟩ :=
        propagate_spec hI' hS'
      rw [he] at hI'' hS'' hx hn hk ⊢
      refine ⟨hI'', hS'', hC'.ext hx hn, hk, ?_, ?_, ?_, ?_⟩
      · simp only [h1, hc]
      · simp only [h2, ha]
      · simp only [h3, hr]
      · simpa [h4] using hroots
    cases cf with
    | some k0 =>
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hI, hS, hC, hK, hc, ha, hr, hroots⟩
    | none =>
    simp only [Option.isNone_none, ↓reduceIte]
    cases hcl : st.cons[i]!.clause with
    | false =>
      have hreg : reg st.cons[i]! = true := by
        simp only [reg, hcl, Bool.not_false, Bool.true_and, decide_eq_true_eq]
        rcases hil.2 with h' | h'
        · rw [hcl] at h'; cases h'
        · exact h'
      have hsl : VeriPB.slack (tlits st.vars st.asg.trail st.asg.trail.size) pc ≤ st.slack[i]! := by
        rw [hS i pc hG hreg]; exact slack_anti tlits_take_sub pc
      by_cases hneg : st.slack[i]! < 0
      · simp only [Bool.false_eq_true, ↓reduceIte, hneg]
        exact ⟨hI, hS, hC, fun k hk => ⟨pc, by cases hk; exact hG,
          show VeriPB.slack (tlits st.vars st.asg.trail st.asg.trail.size) pc < 0 by omega⟩,
          hc, ha, hr, hroots⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, hneg, Bool.not_false]
        obtain ⟨ha', he, hn⟩ := propagatePB_spec hI.nodup hI.asg hrep hcl hG hsl
        obtain ⟨hI', hS'⟩ := InvCore.asg_ext hI hS ha' he
        exact hprop _ hI' hS' (hC.ext he hn) rfl rfl rfl rfl
    | true =>
      obtain ⟨-, -, h0⟩ := hrep.clause hcl
      have hsl := slack_le_coeffSum (tlits st.vars st.asg.trail st.asg.trail.size) pc
      by_cases hneg : st.cons[i]!.slack0 < 0
      · simp only [↓reduceIte, hneg]
        exact ⟨hI, hS, hC, fun k hk => ⟨pc, by cases hk; exact hG,
          show VeriPB.slack (tlits st.vars st.asg.trail st.asg.trail.size) pc < 0 by omega⟩,
          hc, ha, hr, hroots⟩
      · simp only [↓reduceIte, hneg, Bool.not_true, Bool.false_eq_true]
        exact hprop st hI hS hC rfl rfl rfl rfl
  · rintro ⟨st, cf⟩ ⟨hI, hS, hC, hK, hc, -, -, -⟩
    obtain ⟨⟨rr, hm⟩, hsize, -, hmark⟩ := markRootReasons_spec st 0
    rw [hm] at hsize hmark
    dsimp only
    rw [hm]
    refine ⟨{ hI with
      rr_size := hsize ▸ hI.rr_size
      slack := hS
      rootLen := fun _ => rfl
      rr := fun _ k hk => hmark k hk (Nat.zero_le _) ?_
      chain := fun _ => hC
      conflict := fun _ => hK }, hc, rfl⟩
    obtain ⟨pc, hpc, -⟩ := hC k hk (Nat.zero_le _)
    have := ((hI.live (st.asg.reason[st.asg.trail[k] / 2]!)).1 (by rw [hpc]; rfl)).1
    exact lt_of_lt_of_le this hI.rr_size

private theorem ChainFrom.vars_ext {vars vars' : Array ℕ} {G : ℕ → Option PBConstr} {m : ℕ}
    {a : Asg} (hc : ChainFrom vars G m a) (h : vars.toList <+: vars'.toList)
    (ht : ∀ ℓ ∈ a.trail, ℓ < 2 * vars.size) : ChainFrom vars' G m a := by
  intro k hk hm
  obtain ⟨pc, hpc, hF⟩ := hc k hk hm
  refine ⟨pc, hpc, ?_⟩
  rw [tlits_ext h ht, dec_ext h (ht _ (by simp))]
  exact hF

private theorem ChainFrom.mono {vars : Array ℕ} {G G' : ℕ → Option PBConstr} {m : ℕ} {a : Asg}
    (hc : ChainFrom vars G m a) (hG : ∀ c pc, G c = some pc → G' c = some pc) :
    ChainFrom vars G' m a := fun k hk hm => by
  obtain ⟨pc, hpc, hF⟩ := hc k hk hm
  exact ⟨pc, hG _ _ hpc, hF⟩

/-- The constraints of a new engine index extend those before. -/
private theorem update_some_of {G : ℕ → Option PBConstr} {i : ℕ} (hi : G i = none)
    {pc : PBConstr} {c : ℕ} {pc' : PBConstr} (hc : G c = some pc') :
    Function.update G i (some pc) c = some pc' := by
  have : c ≠ i := fun he => by rw [he, hi] at hc; cases hc
  simpa [Function.update, this] using hc

private theorem coeffSum_posTerms (c : PBConstr) : coeffSum (posTerms c) = coeffSum c.terms := by
  unfold posTerms
  induction c.terms with
  | nil => rfl
  | cons t ts ih =>
    by_cases h0 : 0 < t.1
    · simp [h0, ih]
    · have : t.1 = 0 := by omega
      simp [ih, this]

private theorem perm_sum_nat {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The total of the coefficients computed by `add`. -/
private theorem foldl_fst_eq {vars : Array ℕ} {ts : Array (ℕ × ℕ)} {c : PBConstr}
    (h : (ts.toList.map fun p => (p.1, dec vars p.2)).Perm (posTerms c)) :
    ts.foldl (fun t x => t + x.1) 0 = coeffSum c.terms := by
  rw [← coeffSum_posTerms, ← Array.foldl_toList]
  have hp := h.map (·.1)
  simp only [List.map_map, Function.comp_def] at hp
  rw [coeffSum, ← perm_sum_nat hp]
  generalize ts.toList = l
  suffices ∀ n, l.foldl (fun t x => t + x.1) n = n + (l.map (·.1)).sum by simpa using this 0
  induction l with
  | nil => simp
  | cons x l ih => intro n; simp [ih]; omega

private theorem getD_zero_le_foldl (ts : Array (ℕ × ℕ)) :
    ((ts[0]?.map (·.1)).getD 0) ≤ ts.foldl (fun t x => t + x.1) 0 := by
  rw [← Array.foldl_toList]
  cases ts with
  | mk l =>
    cases l with
    | nil => simp
    | cons x l =>
      simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, List.foldl_cons]
      have key : ∀ m, m ≤ l.foldl (fun t x => t + x.1) m := by
        induction l with
        | nil => simp
        | cons y l ih => intro m; simp only [List.foldl_cons]; exact le_trans (by omega) (ih _)
      exact le_trans (by omega) (key _)

/-- The part of `Cslib.Logic.PL.VeriPB.Elab.EState.add` after the constraint is pushed and
registered as a root, restated as a function of that state for the proof (`add_eq`). -/
private def addTail (s : EState) (clause : Bool) (i : ℕ) : EState × ℕ := Id.run do
  let mut s := s
  if s.dirty || s.rootConflict.isSome then
    let r := s.cons[i]!
    if !clause then s := { s with slack := s.slack.set! i (s.freshSlack r.start r.size r.degree) }
    else
      let w₀ := s.lits[r.start]!
      let w₁ := s.lits[r.start + 1]!
      s := { s with watches := (s.watches.modify w₀ (·.push i)).modify w₁ (·.push i) }
    if s.rootConflict.isSome then s := { s with dirty := true }
    return (s, i)
  let n := s.asg.trail.size
  let (s', confl) := match s.checkFresh i with
    | (s, some k) => (s, some k)
    | (s, none) => s.propagate
  s := s'.markRootReasons n
  s := { s with rootLen := s.asg.trail.size }
  if confl.isSome then s := { s with rootConflict := confl }
  return (s, i)

private theorem add_eq (s : EState) (c : PBConstr) (h : Hint) :
    s.add c h =
      let ts := (s.codes c).2
      let total : ℕ := ts.foldl (fun t x => t + x.1) 0
      let clause := 2 ≤ ts.size && 0 < c.degree && ts.all (c.degree ≤ ·.1)
      let p := (s.codes c).1.pushCons ts c.degree ((total : ℤ) - c.degree) clause h
      addTail (if (total : ℤ) - c.degree < (((ts[0]?.map (·.1)).getD 0 : ℕ) : ℤ) ||
          total < c.degree then { p.1 with roots := p.1.roots.push p.2 } else p.1) clause p.2 := by
  unfold EState.add addTail
  simp only [Id.run]
  split <;> rfl

/-- No constraint has the next engine index. -/
private theorem InvCore.none_of_size {s : EState} {G : ℕ → Option PBConstr} (h : InvCore s G) :
    G s.cons.size = none := by
  cases hg : G s.cons.size with
  | none => rfl
  | some _ => have := ((h.live s.cons.size).1 (by simp [hg])).1; omega

/-- After a constraint is pushed, the slack counters of the others are still right. -/
private theorem slack_push {s₁ s₂ : EState} {G : ℕ → Option PBConstr} {pc : PBConstr} {r : CRec}
    (h : InvCore s₁ G) (hs : SlackOk s₁ G) (hcons : s₂.cons = s₁.cons.push r)
    (hsl : ∀ c, c < s₁.cons.size → s₂.slack[c]! = s₁.slack[c]!) (hv : s₂.vars = s₁.vars)
    (ha : s₂.asg = s₁.asg) (hq : s₂.qhead = s₁.qhead) :
    ∀ c pc', Function.update G s₁.cons.size (some pc) c = some pc' → reg s₂.cons[c]! = true →
      c ≠ s₁.cons.size → s₂.slack[c]! = VeriPB.slack (tlits s₂.vars s₂.asg.trail s₂.qhead) pc' := by
  intro c pc' hc hreg hne
  have hG : G c = some pc' := by simpa [Function.update, hne] using hc
  have hlt : c < s₁.cons.size := ((h.live c).1 (by simp [hG])).1
  have hcc : s₂.cons[c]! = s₁.cons[c]! := by
    rw [hcons, getElem!_eq, getElem!_eq, Array.getElem?_push]
    simp [show c ≠ s₁.cons.size by omega]
  rw [hsl c hlt, hs c pc' hG (hcc ▸ hreg), hv, ha, hq]

/-- The state `rupHints` and `extend` start from: the root level rebuilt if it must be. -/
private theorem rebuilt_spec {s : EState} {G : ℕ → Option PBConstr} (h : Inv s G) :
    Inv (if s.dirty = true then s.rebuild else s) G ∧
      (if s.dirty = true then s.rebuild else s).cons = s.cons ∧
      (if s.dirty = true then s.rebuild else s).dirty = false := by
  split
  · exact rebuild_spec h.toInvCore h.slack
  · rename_i hd; exact ⟨h, rfl, by simpa using hd⟩

/-- **Adding a constraint** keeps the invariant, the constraint taking the next engine index. -/
private theorem add_spec {s : EState} {G : ℕ → Option PBConstr} (h : Inv s G) (c : PBConstr)
    (hh : Hint) :
    (s.add c hh).2 = s.cons.size ∧ Inv (s.add c hh).1 (Function.update G s.cons.size (some c)) ∧
    (s.add c hh).1.cons = s.cons.push (s.add c hh).1.cons[s.cons.size]! ∧
    (s.add c hh).1.cons[s.cons.size]!.hint = hh := by
  have hGi := h.toInvCore.none_of_size
  obtain ⟨⟨vI, vs, val, rea, tp, wa, oc, hc1⟩, hI₁, hS₁, hvx, hax, hperm, hlt⟩ :=
    codes_spec h.toInvCore h.slack c
  rw [add_eq]
  dsimp only
  generalize s.codes c = p at hc1 hI₁ hS₁ hvx hax hperm hlt ⊢
  obtain ⟨s₁, ts⟩ := p
  dsimp only at hc1 hI₁ hS₁ hvx hax hperm hlt ⊢
  have htot := foldl_fst_eq hperm
  have hcl : (decide (2 ≤ ts.size) && decide (0 < c.degree) &&
      ts.all fun x => decide (c.degree ≤ x.1)) = true →
      0 < c.degree ∧ 2 ≤ ts.size ∧ (coeffSum c.terms : ℤ) - c.degree ≤
        ((Array.foldl (fun t x => t + x.1) 0 ts : ℕ) : ℤ) - c.degree := by
    intro hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.2, hc.1.1, by rw [htot]⟩
  obtain ⟨hi, ⟨al, li, co, sl, rr, oc', hc2⟩, hI₂, hsl₂, hal₂, hw₂, hrr₂, -, -, -⟩ :=
    pushCons_spec (hh := hh) hI₁ hperm hlt rfl hcl
  have hcs : s₁.cons = s.cons := by rw [hc1]
  generalize s₁.pushCons ts c.degree _ _ hh = q at hi hc2 hI₂ hsl₂ hal₂ hw₂ hrr₂ ⊢
  obtain ⟨s₂, i⟩ := q
  dsimp only at hi hc2 hI₂ hsl₂ hal₂ hw₂ hrr₂ ⊢
  rw [hcs] at hi hI₂
  subst hi
  have hrec : s₂.cons[s.cons.size]! = ⟨s₁.lits.size, ts.size, c.degree,
      ((Array.foldl (fun t x => t + x.1) 0 ts : ℕ) : ℤ) - c.degree,
      (decide (2 ≤ ts.size) && decide (0 < c.degree) && ts.all fun x => decide (c.degree ≤ x.1)),
      hh⟩ := by
    rw [hc2, hcs, getElem!_eq, Array.getElem?_push]; simp
  have hR1 : (((Array.foldl (fun t x => t + x.1) 0 ts : ℕ) : ℤ) - c.degree <
        (((ts[0]?.map (·.1)).getD 0 : ℕ) : ℤ) ∨ Array.foldl (fun t x => t + x.1) 0 ts < c.degree) →
      ∀ j ∈ s₂.roots.push s.cons.size, j < s₂.cons.size ∧
        (s₂.cons[j]!.clause = true ∨ 0 < s₂.cons[j]!.degree) := by
    intro hb j hj
    rcases Array.mem_push.1 hj with hj | hj
    · exact hI₂.roots j hj
    · subst hj
      refine ⟨by rw [hc2]; simp [hcs], ?_⟩
      rw [hrec]
      by_cases hd : 0 < c.degree
      · exact Or.inr hd
      · have := getD_zero_le_foldl ts
        rcases hb with h' | h' <;> omega
  split
  on_goal 1 =>
    rename_i hcond
    generalize hX : ({ s₂ with roots := s₂.roots.push s.cons.size } : EState) = X
    have hXR : ∃ R, X = { s₂ with roots := R } ∧ ∀ j ∈ R, j < s₂.cons.size ∧
        (s₂.cons[j]!.clause = true ∨ 0 < s₂.cons[j]!.degree) :=
      ⟨_, hX.symm, hR1 (by simpa using hcond)⟩
  on_goal 2 =>
    generalize hX : s₂ = X
    have hXR : ∃ R, X = { s₂ with roots := R } ∧ ∀ j ∈ R, j < s₂.cons.size ∧
        (s₂.cons[j]!.clause = true ∨ 0 < s₂.cons[j]!.degree) :=
      ⟨s₂.roots, hX.symm, hI₂.roots⟩
  all_goals
    obtain ⟨R, rfl, hRok⟩ := hXR
    clear hX
    unfold addTail
    simp only [Id.run]
    have hI₃ : InvCore { s₂ with roots := R } (Function.update G s.cons.size (some c)) :=
      { hI₂ with roots := hRok }
    have hv21 : s₂.vars = s₁.vars := by rw [hc2]
    have hS₂ := slack_push (pc := c) hI₁ hS₁ (by rw [hc2]) hsl₂ (by rw [hc2]) (by rw [hc2])
      (by rw [hc2])
    rw [hcs] at hS₂
    have hGi' : Function.update G s.cons.size (some c) s.cons.size = some c := by simp
    have hrep := hI₂.rep _ _ hGi'
    have hdirty : ∀ X : EState, InvCore X (Function.update G s.cons.size (some c)) →
        SlackOk X (Function.update G s.cons.size (some c)) → X.dirty = true →
        Inv X (Function.update G s.cons.size (some c)) := fun X hX hS hd =>
      { hX with
        slack := hS
        rootLen := by simp [hd]
        rr := by simp [hd]
        chain := by simp [hd]
        conflict := by simp [hd] }
    have hcons₂ : s₂.cons = s.cons.push s₂.cons[s.cons.size]! := by
      rw [hrec, hc2, hcs]
    have hsz : s.cons.size < s₂.cons.size := by rw [hcons₂]; simp
    split
    · rename_i hdc
      have hfs := freshSlack_eq hI₃ (r := s₂.cons[s.cons.size]!) (pc := c)
        (by simpa [hv21] using hal₂) hrep.lt hrep.degree
      split
      · rename_i hncl
        have hcl' : s₂.cons[s.cons.size]!.clause = false := by
          rw [hrec]; simpa only [Bool.not_eq_true'] using hncl
        have hS' : ∀ fs : ℤ, fs = VeriPB.slack (tlits s₂.vars s₂.asg.trail s₂.qhead) c →
            ∀ c' pc', Function.update G s.cons.size (some c) c' = some pc' →
            reg s₂.cons[c']! = true → (s₂.slack.set! s.cons.size fs)[c']! =
              VeriPB.slack (tlits s₂.vars s₂.asg.trail s₂.qhead) pc' := by
          intro fs hfs' c' pc' hc' hreg
          rw [getElem!_set!]
          by_cases hne : c' = s.cons.size
          · subst hne
            simp only [hGi', Option.some.injEq] at hc'
            subst hc'
            simp [hI₂.slack_size, hsz, hfs']
          · simp only [Ne.symm hne, false_and, ↓reduceIte]
            exact hS₂ c' pc' hc' hreg hne
        split
        all_goals
          refine ⟨rfl, hdirty _
            { hI₃ with slack_size := (Array.size_set! _ _ _).trans hI₂.slack_size }
            (hS' _ hfs) ?_, hcons₂, by change s₂.cons[s.cons.size]!.hint = hh; rw [hrec]⟩
          first
          | rfl
          | (simp only [Bool.or_eq_true] at hdc
             rcases hdc with hdc | hdc
             · exact hdc
             · simp_all)
      · rename_i hncl
        have hcl' : s₂.cons[s.cons.size]!.clause = true := by
          rw [hrec]
          revert hncl
          cases (decide (2 ≤ ts.size) && decide (0 < c.degree) &&
            ts.all fun x => decide (c.degree ≤ x.1)) <;> simp
        obtain ⟨-, h2, -⟩ := hrep.clause hcl'
        have hw : ∀ k, k < 2 → s₂.lits[s₂.cons[s.cons.size]!.start + k]! < s₂.watches.size := by
          intro k hk
          rw [hI₂.watches_size]
          exact hrep.lt _ (List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩)
        have hw0 := hw 0 (by omega)
        have hw1 := hw 1 (by omega)
        simp only [Nat.add_zero] at hw0
        have hcount : ∀ c' ℓ, ((s₂.watches.modify s₂.lits[s₂.cons[s.cons.size]!.start]!
            (·.push s.cons.size)).modify s₂.lits[s₂.cons[s.cons.size]!.start + 1]!
              (·.push s.cons.size))[ℓ]!.count c' = s₂.watches[ℓ]!.count c' +
            (if c' = s.cons.size then [s₂.lits[s₂.cons[s.cons.size]!.start]!,
              s₂.lits[s₂.cons[s.cons.size]!.start + 1]!].count ℓ else 0) := by
          intro c' ℓ
          rw [count_modify, count_modify]
          simp only [Array.size_modify, List.count_cons, List.count_nil, beq_iff_eq]
          by_cases hc : c' = s.cons.size
          · subst hc; simp only [hw0, hw1, and_true, ↓reduceIte]
            split_ifs <;> omega
          · simp [hc, Ne.symm hc]
        have hX : InvCore { s₂ with roots := R
                                    watches := (s₂.watches.modify
                                      s₂.lits[s₂.cons[s.cons.size]!.start]!
                                      (·.push s.cons.size)).modify
                                      s₂.lits[s₂.cons[s.cons.size]!.start + 1]!
                                      (·.push s.cons.size) }
            (Function.update G s.cons.size (some c)) :=
          { hI₃ with
            watches_size := by simp only [Array.size_modify]; exact hI₂.watches_size
            watch_name := by
              intro ℓ c' hc'
              rcases mem_modify hc' with hc' | hc'
              · rcases mem_modify hc' with hc' | hc'
                · exact hI₂.watch_name ℓ c' hc'
                · subst hc'; exact ⟨hsz, hcl'⟩
              · subst hc'; exact ⟨hsz, hcl'⟩
            watch_count := by
              intro c' pc' hc' hcc ℓ
              rw [hcount]
              by_cases hc : c' = s.cons.size
              · subst hc
                have : s₂.watches[ℓ]!.count s.cons.size = 0 :=
                  Array.count_eq_zero.2 (hw₂ ℓ)
                simp [this]
              · simp only [hc, ↓reduceIte, Nat.add_zero]
                exact hI₂.watch_count c' pc' hc' hcc ℓ }
        have hXS : ∀ c' pc', Function.update G s.cons.size (some c) c' = some pc' →
            reg s₂.cons[c']! = true →
            s₂.slack[c']! = VeriPB.slack (tlits s₂.vars s₂.asg.trail s₂.qhead) pc' := by
          intro c' pc' hc' hreg
          have hne : c' ≠ s.cons.size := by
            rintro rfl; simp [reg, hcl'] at hreg
          exact hS₂ c' pc' hc' hreg hne
        split
        all_goals
          refine ⟨rfl, hdirty _ { hX with } hXS ?_, hcons₂,
            by change s₂.cons[s.cons.size]!.hint = hh; rw [hrec]⟩
          first
          | rfl
          | (simp only [Bool.or_eq_true] at hdc
             rcases hdc with hdc | hdc
             · exact hdc
             · simp_all)
    · rename_i hdc
      have hd2 : s₂.dirty = false ∧ s₂.rootConflict = none := by
        simpa using hdc
      have hds : s.dirty = false := by rw [← hd2.1, hc2, hc1]
      have hsize₂ : s.cons.size + 1 = s₂.cons.size := by rw [hcons₂]; simp
      obtain ⟨⟨li4, wa4, sl4, as4, h4⟩, hI₄, hS₄, he₄, hn₄, hk₄⟩ :=
        checkFresh_spec (s := { s₂ with roots := R }) hI₃ hS₂ hGi' hsize₂
          (by simpa [hv21] using hal₂) hw₂
      generalize ({ s₂ with roots := R } : EState).checkFresh s.cons.size = q
        at h4 hI₄ hS₄ he₄ hn₄ hk₄ ⊢
      obtain ⟨s₄, cf⟩ := q
      dsimp only at h4 hI₄ hS₄ he₄ hn₄ hk₄ ⊢
      have hcomb : ∃ s₅ : EState, ∃ cf' : Option ℕ,
          (match (s₄, cf) with
            | (s, some k) => (s, some k)
            | (s, none) => s.propagate) = (s₅, cf') ∧
          InvCore s₅ (Function.update G s.cons.size (some c)) ∧
          SlackOk s₅ (Function.update G s.cons.size (some c)) ∧
          AsgExt s₂.asg s₅.asg ∧ ChainFrom s₂.vars (Function.update G s.cons.size (some c))
            s₂.asg.trail.size s₅.asg ∧
          (∀ k, cf' = some k → ∃ pc, Function.update G s.cons.size (some c) k = some pc ∧
            VeriPB.slack (tlits s₂.vars s₅.asg.trail s₅.asg.trail.size) pc < 0) ∧
          s₅.vars = s₂.vars ∧ s₅.cons = s₂.cons ∧ s₅.rootReason = s₂.rootReason ∧
          s₅.dirty = s₂.dirty ∧ s₅.rootConflict = s₂.rootConflict := by
        cases cf with
        | some k =>
          refine ⟨s₄, some k, rfl, hI₄, hS₄, he₄, hn₄, hk₄, ?_⟩
          rw [h4]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        | none =>
          obtain ⟨⟨li5, wa5, oc5, sl5, as5, qh5, h5⟩, hI₅, hS₅, he₅, hn₅, -, hk₅⟩ :=
            propagate_spec hI₄ hS₄
          refine ⟨s₄.propagate.1, s₄.propagate.2, rfl, hI₅, hS₅, he₄.trans he₅, ?_, ?_, ?_⟩
          · have hv4 : s₄.vars = s₂.vars := by rw [h4]
            exact hn₄.ext he₅ (hv4 ▸ hn₅)
          · have hv4 : s₄.vars = s₂.vars := by rw [h4]
            intro k hk; rw [← hv4]; exact hk₅ k hk
          · rw [h5, h4]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨s₅, cf', heq, hI₅, hS₅, he₅, hn₅, hk₅, hv5, hc5, hr5, hd5, hrc5⟩ := hcomb
      rw [heq]
      dsimp only
      obtain ⟨⟨rr, hm⟩, hsize, hmono, hmark⟩ := markRootReasons_spec s₅ s₂.asg.trail.size
      rw [hm] at hsize hmono hmark
      have hes : AsgExt s.asg s₅.asg := by
        have : s₂.asg = s₁.asg := by rw [hc2]
        exact hax.trans (this ▸ he₅)
      have hvs : s.vars.toList <+: s₅.vars.toList := by rw [hv5, hv21]; exact hvx
      have hn₀ : s₂.asg.trail.size = s.asg.trail.size := by rw [hc2, hc1]
      have fin : ∀ rc : Option ℕ, (∀ k, rc = some k → ∃ pc,
          Function.update G s.cons.size (some c) k = some pc ∧
            VeriPB.slack (tlits s₅.vars s₅.asg.trail s₅.asg.trail.size) pc < 0) →
          Inv { s₅ with rootReason := rr, rootLen := s₅.asg.trail.size, rootConflict := rc }
            (Function.update G s.cons.size (some c)) := by
        intro rc hrc
        refine { hI₅ with
          rr_size := hsize ▸ hI₅.rr_size
          slack := hS₅
          rootLen := fun _ => rfl
          rr := ?_
          chain := fun _ => ?_
          conflict := fun _ => hrc }
        · intro _ k hk
          by_cases hkn : k < s.asg.trail.size
          · have hpre := hes.1
            have htk : s₅.asg.trail[k] = s.asg.trail[k] := by
              have := hpre.getElem (i := k) (by simpa using hkn)
              simpa using this.symm
            have hrk : s₅.asg.reason[s₅.asg.trail[k] / 2]! = s.asg.reason[s.asg.trail[k] / 2]! := by
              rw [htk]; exact hes.2 _ (by simp)
            change rr.get! s₅.asg.reason[s₅.asg.trail[k] / 2]! ≠ 0
            rw [hrk]
            apply hmono
            obtain ⟨pc, hpc, -⟩ := h.chain hds k hkn (Nat.zero_le _)
            have hlt' := ((h.live _).1 (by rw [hpc]; rfl)).1
            rw [hr5, hrr₂ _ (by rw [hcs]; omega), hc1]
            exact h.rr hds k hkn
          · obtain ⟨pc, hpc, -⟩ := hn₅ k hk (by omega)
            have hlt' := ((hI₅.live _).1 (by rw [hpc]; rfl)).1
            exact hmark k hk (by omega) (lt_of_lt_of_le hlt' hI₅.rr_size)
        · have h0 : ChainFrom s₅.vars (Function.update G s.cons.size (some c)) 0 s.asg :=
            ((h.chain hds).vars_ext hvs h.asg.trail_lt).mono fun _ _ => update_some_of hGi
          refine h0.ext hes ?_
          rw [← hn₀, hv5]; exact hn₅
      have hcons₅ : s₅.cons = s.cons.push s₅.cons[s.cons.size]! := by rw [hc5]; exact hcons₂
      have hhint : s₅.cons[s.cons.size]!.hint = hh := by rw [hc5, hrec]
      rw [hm]
      split
      · exact ⟨rfl, fin cf' (by rw [hv5]; exact hk₅), hcons₅, hhint⟩
      · rename_i hcf
        refine ⟨rfl, fin _ ?_, hcons₅, hhint⟩
        intro k hk
        rw [hrc5, hd2.2] at hk
        cases hk

/-! ### Removing the negation of a `rup` step -/

private theorem pop2_flatL {o : Array ℕ} {L : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (h : o.toList = flatL (L ++ [p])) : o.pop.pop.toList = flatL L := by
  rw [Array.toList_pop, Array.toList_pop, h, flatL_append]
  simp [flatL]

/-- Popping one pair from the list of the code of each term removes the pairs of the negation. -/
private theorem popAll (PA : ℕ → List (ℕ × ℕ)) (i : ℕ) : ∀ (l : List (ℕ × ℕ)) (st : EState),
    (∀ x ∈ l, x.2 < st.occ.size) →
    (∀ ℓ : ℕ, ∃ PB : List (ℕ × ℕ), st.occ[ℓ]!.toList = flatL (PA ℓ ++ PB) ∧
      PB.length = (l.filter (·.2 == ℓ)).length) →
    let r := l.foldl (fun b x => { b with occ := b.occ.modify x.2 fun x => x.pop.pop }) st
    (∃ occ, r = { st with occ := occ }) ∧ r.occ.size = st.occ.size ∧
      ∀ ℓ : ℕ, r.occ[ℓ]!.toList = flatL (PA ℓ)
  | [], st, _, h => by
    refine ⟨⟨st.occ, rfl⟩, rfl, fun ℓ => ?_⟩
    obtain ⟨PB, h1, h2⟩ := h ℓ
    simp only [List.filter_nil, List.length_nil, List.length_eq_zero_iff] at h2
    simpa [h2] using h1
  | x :: l, st, hx, h => by
    let st' : EState := { st with occ := st.occ.modify x.2 fun x => x.pop.pop }
    have hst' : ∀ ℓ : ℕ, ∃ PB : List (ℕ × ℕ), st'.occ[ℓ]!.toList = flatL (PA ℓ ++ PB) ∧
        PB.length = (l.filter (·.2 == ℓ)).length := by
      intro ℓ
      obtain ⟨PB, h1, h2⟩ := h ℓ
      by_cases hℓ : x.2 = ℓ
      · subst hℓ
        have hne : PB ≠ [] := by
          intro he; simp [he] at h2
        obtain ⟨PB', p, rfl⟩ := List.eq_nil_or_concat PB |>.resolve_left hne
        refine ⟨PB', ?_, ?_⟩
        · simp only [st', getElem!_eq, Array.getElem?_modify]
          have hlt := hx x List.mem_cons_self
          rw [Array.getElem?_eq_getElem hlt]
          simp only [↓reduceIte, Option.map_some, Option.getD_some]
          rw [getElem!_eq, Array.getElem?_eq_getElem hlt] at h1
          simp only [Option.getD_some] at h1
          exact pop2_flatL (by rw [h1, List.concat_eq_append, List.append_assoc])
        · simp at h2 ⊢; omega
      · refine ⟨PB, ?_, ?_⟩
        · simp only [st', getElem!_eq, Array.getElem?_modify, hℓ, ↓reduceIte] at h1 ⊢
          exact h1
        · simpa [hℓ] using h2
    obtain ⟨⟨occ, hocc⟩, hsz, hr⟩ := popAll PA i l st' (fun y hy => by
      simpa [st'] using hx y (List.mem_cons_of_mem _ hy)) hst'
    exact ⟨⟨occ, by simpa [st'] using hocc⟩, by simpa [st'] using hsz, hr⟩

private theorem getElem!_pop {α : Type} [Inhabited α] (a : Array α) {c : ℕ}
    (hc : c + 1 < a.size) : a.pop[c]! = a[c]! := by
  simp only [getElem!_eq, Array.getElem?_pop]
  rw [ite_pos (show c < a.size - 1 by omega)]

private theorem getElem!_shrink {α : Type} [Inhabited α] (a : Array α) {n c : ℕ} (hc : c < n) :
    (a.shrink n)[c]! = a[c]! := by
  simp only [getElem!_eq, Array.shrink_eq_take]
  congr 1
  rw [Array.take_eq_extract, Array.getElem?_extract]
  split
  · simp
  · rename_i h'; rw [Array.getElem?_eq_none (by omega)]

/-- **Removing the negation**, the last constraint, once its occurrences are popped. -/
private theorem removeNeg_core {s : EState} {G : ℕ → Option PBConstr} {i : ℕ} {pc : PBConstr}
    {occ : Array (Array ℕ)} {PA : ℕ → List (ℕ × ℕ)} {st : ℕ}
    (h : InvCore s (Function.update G i (some pc)))
    (hS : SlackOk s (Function.update G i (some pc)))
    (hGi : G i = none) (hi1 : 1 ≤ i) (hi : i + 1 = s.cons.size)
    (hcl : s.cons[i]!.clause = false) (hroots : ∀ j ∈ s.roots, j ≠ i) (hst : s.cons[i]!.start = st)
    (hos : occ.size = s.occ.size)
    (hocc : ∀ ℓ : ℕ, occ[ℓ]!.toList = flatL (PA ℓ) ∧ (∀ p ∈ PA ℓ, p.1 ≠ i) ∧
      ∃ PB : List (ℕ × ℕ), s.occ[ℓ]!.toList = flatL (PA ℓ ++ PB) ∧ ∀ p ∈ PB, p.1 = i) :
    InvCore { s with occ := occ
                     cons := s.cons.pop
                     cpos := s.cpos.pop
                     alive := s.alive.set! i 0
                     lits := s.lits.shrink st
                     coeffs := s.coeffs.shrink st
                     slack := s.slack.pop } G ∧
    SlackOk { s with occ := occ
                     cons := s.cons.pop
                     cpos := s.cpos.pop
                     alive := s.alive.set! i 0
                     lits := s.lits.shrink st
                     coeffs := s.coeffs.shrink st
                     slack := s.slack.pop } G := by
  subst hst
  have hupd : ∀ c pc', G c = some pc' → Function.update G i (some pc) c = some pc' :=
    fun c pc' hc => update_some_of hGi hc
  have hne : ∀ c pc', G c = some pc' → c ≠ i := fun c pc' hc he => by
    rw [he, hGi] at hc; cases hc
  have hlive : ∀ c pc', G c = some pc' → 1 ≤ c ∧ c < i := by
    intro c pc' hc
    have := (h.live c).1 (by rw [hupd c pc' hc]; rfl)
    have h0 : c ≠ 0 := fun he => by rw [he, h.alive0] at this; exact this.2 rfl
    have := hne c pc' hc
    omega
  have hal : ∀ c, (s.alive.set! i 0).get! c = if c = i then 0 else s.alive.get! c := by
    intro c
    rw [ByteArray.get!_set!]
    by_cases hc : c = i
    · subst hc
      by_cases hl : c < s.alive.size
      · simp [hl]
      · simp [hl, ByteArray.get!_ge _ (Nat.le_of_not_lt hl)]
    · simp [hc, Ne.symm hc]
  have hcons : ∀ c, c < i → s.cons.pop[c]! = s.cons[c]! := fun c hc =>
    getElem!_pop _ (by omega)
  have hst : s.cons[i]!.start ≤ s.lits.size := by
    have := end_le h i hi1 (by omega); omega
  have hrange : ∀ c, 1 ≤ c → c < i → s.cons[c]!.start + s.cons[c]!.size ≤ s.cons[i]!.start :=
    fun c h1 hc => range_le h.layout h1 i hc (by omega)
  have hcongr : ∀ c, 1 ≤ c → c < i →
      stored (s.lits.shrink s.cons[i]!.start) (s.coeffs.shrink s.cons[i]!.start) s.cons[c]! =
        stored s.lits s.coeffs s.cons[c]! ∧
      scodes (s.lits.shrink s.cons[i]!.start) s.cons[c]! = scodes s.lits s.cons[c]! := by
    intro c h1 hc
    refine stored_congr fun k _ hk => ?_
    have := hrange c h1 hc
    exact ⟨getElem!_shrink _ (by omega), getElem!_shrink _ (by omega)⟩
  have hsz : ∀ {α : Type} (a : Array α), a.size = s.cons.size → a.pop.size = i := by
    intro α a ha; simp [ha]; omega
  have hlsz : (s.lits.shrink s.cons[i]!.start).size = s.cons[i]!.start := by
    simp; omega
  have hpairs : ∀ ℓ : ℕ, ∀ p ∈ PA ℓ, p ∈ pairsL s.occ[ℓ]!.toList := by
    intro ℓ p hp
    obtain ⟨-, -, PB, h1, -⟩ := hocc ℓ
    rw [h1, pairsL_flatL]; exact List.mem_append_left _ hp
  have hwsum : ∀ c pc', G c = some pc' → ∀ ℓ : ℕ, wsum c occ[ℓ]! = wsum c s.occ[ℓ]! := by
    intro c pc' hc ℓ
    obtain ⟨h0, -, PB, h1, h2⟩ := hocc ℓ
    unfold wsum
    rw [h0, h1, pairsL_flatL, pairsL_flatL, List.filter_append, List.map_append,
      List.sum_append]
    have : PB.filter (·.1 == c) = [] := List.filter_eq_nil_iff.2 fun p hp => by
      have := h2 p hp; have := hne c pc' hc; simp; omega
    simp [this]
  refine ⟨{
    nodup := h.nodup
    idx_some := h.idx_some
    idx_mem := h.idx_mem
    asg := h.asg
    watches_size := h.watches_size
    occ_size := hos ▸ h.occ_size
    qhead_le := h.qhead_le
    cons_pos := by simp; omega
    cpos_size := by simp [h.cpos_size]
    slack_size := by simp [h.slack_size]
    alive_size := by simp only [ByteArray.size_set!, Array.size_pop]; have := h.alive_size; omega
    rr_size := by simp only [Array.size_pop]; have := h.rr_size; omega
    coeffs_size := by simp [h.coeffs_size]
    layout := by
      intro c h1 hc
      simp only [Array.size_pop] at hc
      have hc' : c < i := by omega
      rw [hcons c hc', getElem!_pop _ (show c + 1 < s.cpos.size by rw [h.cpos_size]; omega)]
      obtain ⟨l1, l2⟩ := h.layout c h1 (by omega)
      refine ⟨l1, ?_⟩
      rw [l2, ite_pos (show c + 1 < s.cons.size by omega)]
      by_cases hci : c + 1 < s.cons.pop.size
      · rw [ite_pos hci,
          getElem!_pop _ (show c + 1 + 1 < s.cpos.size by rw [h.cpos_size]; simp at hci; omega)]
      · rw [ite_neg hci, hlsz]
        have : c + 1 = i := by simp at hci; omega
        rw [this, ← (h.layout i hi1 (by omega)).1]
    alive0 := by rw [hal]; simp [show (0 : ℕ) ≠ i by omega, h.alive0]
    live := by
      intro c
      simp only [Array.size_pop, hal]
      by_cases hci : c = i
      · subst hci; simp [hGi]
      · simp only [hci, ↓reduceIte]
        have := h.live c
        simp only [Function.update, hci, dite_false] at this
        rw [this]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rep := by
      intro c pc' hc
      obtain ⟨h1, hc'⟩ := hlive c pc' hc
      rw [hcons c hc']
      obtain ⟨e1, e2⟩ := hcongr c h1 hc'
      exact rep_congr (h.rep c pc' (hupd c pc' hc)) e1 e2
    occ_even := by
      intro ℓ
      rw [← Array.length_toList, (hocc ℓ).1]; exact flatL_even _
    occ_name := by
      intro ℓ p hp
      rw [(hocc ℓ).1, pairsL_flatL] at hp
      have hpi := (hocc ℓ).2.1 p hp
      obtain ⟨hlt, hreg⟩ := h.occ_name ℓ p (hpairs ℓ p hp)
      simp only [Array.size_pop]
      refine ⟨by omega, fun ha => ?_⟩
      rw [hcons _ (by omega)]
      rw [hal, ite_neg hpi] at ha
      exact hreg ha
    occ_exact := by
      intro c pc' hc hreg ℓ
      obtain ⟨h1, hc'⟩ := hlive c pc' hc
      rw [hcons c hc'] at hreg ⊢
      rw [hwsum c pc' hc, (hcongr c h1 hc').1]
      exact h.occ_exact c pc' (hupd c pc' hc) hreg ℓ
    watch_name := by
      intro ℓ c hc
      obtain ⟨h1, h2⟩ := h.watch_name ℓ c hc
      have : c ≠ i := fun he => by rw [he, hcl] at h2; cases h2
      simp only [Array.size_pop]
      refine ⟨by omega, ?_⟩
      rw [hcons c (by omega)]; exact h2
    watch_count := by
      intro c pc' hc hcc ℓ
      obtain ⟨h1, hc'⟩ := hlive c pc' hc
      rw [hcons c hc'] at hcc ⊢
      have hsz2 := ((h.rep c pc' (hupd c pc' hc)).clause hcc).2.1
      have := hrange c h1 hc'
      rw [getElem!_shrink _ (by omega), getElem!_shrink _ (by omega)]
      exact h.watch_count c pc' (hupd c pc' hc) hcc ℓ
    roots := by
      intro j hj
      obtain ⟨h1, h2⟩ := h.roots j hj
      have := hroots j hj
      simp only [Array.size_pop]
      rw [hcons j (by omega)]
      exact ⟨by omega, h2⟩ }, ?_⟩
  intro c pc' hc hreg
  obtain ⟨-, hc'⟩ := hlive c pc' hc
  simp only at hreg ⊢
  rw [hcons c hc'] at hreg
  rw [getElem!_pop _ (show c + 1 < s.slack.size by rw [h.slack_size]; omega)]
  exact hS c pc' (hupd c pc' hc) hreg

private theorem flatL_pairsL : ∀ A : List ℕ, A.length % 2 = 0 → flatL (pairsL A) = A
  | [], _ => rfl
  | [_], h => by simp at h
  | a :: b :: A, h => by
    simp only [pairsL, flatL, List.cons.injEq, true_and]
    exact flatL_pairsL A (by simp at h; omega)

/-- A chain carries over to an assignment with the same trail and the same reasons on it. -/
private theorem ChainFrom.congr {vars : Array ℕ} {G : ℕ → Option PBConstr} {m : ℕ} {a a' : Asg}
    (hc : ChainFrom vars G m a) (ht : a'.trail = a.trail)
    (hr : ∀ ℓ ∈ a.trail, a'.reason[ℓ / 2]! = a.reason[ℓ / 2]!) : ChainFrom vars G m a' := by
  intro k hk hm
  have hk' : k < a.trail.size := by rw [← ht]; exact hk
  obtain ⟨pc, hpc, hF⟩ := hc k hk' hm
  refine ⟨pc, ?_, ?_⟩
  · have : a'.trail[k] = a.trail[k] := by simp [ht]
    rw [this, hr _ (by simp)]; exact hpc
  · have : a'.trail[k] = a.trail[k] := by simp [ht]
    rw [this, ht]; exact hF

/-- The end of `Cslib.Logic.PL.VeriPB.Elab.EState.rupHints`, after the trail is backtracked:
the negation is removed again (restated as a function for the proof). -/
private def removeTail (s : EState) (ts : Array (ℕ × ℕ)) (d i start : ℕ)
    (res : Option (Array Hint)) : EState × Option (Array Hint) := Id.run do
  let mut s := s
  if 0 < d then
    for (_, l) in ts do
      s := { s with occ := s.occ.modify l (·.pop.pop) }
  s := { s with cons := s.cons.pop }
  s := { s with cpos := s.cpos.pop }
  s := { s with alive := s.alive.set! i 0 }
  s := { s with slack := s.slack.pop }
  s := { s with lits := s.lits.shrink start }
  s := { s with coeffs := s.coeffs.shrink start }
  return (s, res)

private theorem removeTail_snd (s : EState) (ts : Array (ℕ × ℕ)) (d i start : ℕ)
    (res : Option (Array Hint)) : (removeTail s ts d i start res).2 = res := by
  unfold removeTail
  simp only [Id.run]
  split <;> rfl

/-- The occurrence lists after the negation is pushed and propagation has run: the old pairs, of
which only those of dead constraints may be gone, then the pairs of the negation. -/
private theorem occ_split {s₂ s₃ X : EState} {G : ℕ → Option PBConstr} (hI₂ : InvCore s₂ G)
    {ts : Array (ℕ × ℕ)} {d : ℕ}
    (hocc₃ : ∀ ℓ : ℕ, ∃ B : List (ℕ × ℕ), s₃.occ[ℓ]!.toList = s₂.occ[ℓ]!.toList ++ flatL B ∧
      (∀ p ∈ B, p.1 = s₂.cons.size) ∧
      B.length = if (!false && decide (0 < d)) = true then (ts.toList.filter (·.2 == ℓ)).length
        else 0)
    (hal : s₃.alive.get! s₂.cons.size ≠ 0)
    (hX : ∀ ℓ : ℕ, X.occ[ℓ]! = s₃.occ[ℓ]! ∨ X.occ[ℓ]!.toList =
      flatL ((pairsL s₃.occ[ℓ]!.toList).filter fun p => s₃.alive.get! p.1 != 0)) :
    ∀ ℓ : ℕ, ∃ PA PB : List (ℕ × ℕ), X.occ[ℓ]!.toList = flatL (PA ++ PB) ∧
      (∀ p ∈ PA, p.1 ≠ s₂.cons.size) ∧ (∀ p ∈ PB, p.1 = s₂.cons.size) ∧
      PB.length = if 0 < d then (ts.toList.filter (·.2 == ℓ)).length else 0 := by
  intro ℓ
  obtain ⟨B, h1, h2, h3⟩ := hocc₃ ℓ
  have he := flatL_pairsL _ (by rw [Array.length_toList]; exact hI₂.occ_even ℓ)
  have hP : ∀ p ∈ pairsL s₂.occ[ℓ]!.toList, p.1 ≠ s₂.cons.size := fun p hp =>
    Nat.ne_of_lt (hI₂.occ_name ℓ p hp).1
  have h3' : B.length = if 0 < d then (ts.toList.filter (·.2 == ℓ)).length else 0 := by
    rw [h3]; simp
  have hs3 : s₃.occ[ℓ]!.toList = flatL (pairsL s₂.occ[ℓ]!.toList ++ B) := by
    rw [h1, flatL_append, he]
  rcases hX ℓ with hx | hx
  · exact ⟨_, B, by rw [hx, hs3], hP, h2, h3'⟩
  · refine ⟨(pairsL s₂.occ[ℓ]!.toList).filter fun p => s₃.alive.get! p.1 != 0, B, ?_,
      fun p hp => hP p (List.mem_of_mem_filter hp), h2, h3'⟩
    rw [hx, hs3, pairsL_flatL, List.filter_append]
    congr 2
    exact List.filter_eq_self.2 fun p hp => by rw [h2 p hp]; simpa using hal

/-- A state with the root trail, the reasons and the root marks of an invariant state, and more
variables, has its root level. -/
private theorem Inv.of_root {s₁ X : EState} {G : ℕ → Option PBConstr} (h₁ : Inv s₁ G)
    (hd₁ : s₁.dirty = false) (hX : InvCore X G) (hXS : SlackOk X G)
    (e2 : X.rootLen = s₁.rootLen) (e3 : X.rootConflict = s₁.rootConflict)
    (htr : X.asg.trail = s₁.asg.trail)
    (hre : ∀ ℓ ∈ s₁.asg.trail, X.asg.reason[ℓ / 2]! = s₁.asg.reason[ℓ / 2]!)
    (hv : s₁.vars.toList <+: X.vars.toList)
    (hrr : ∀ j, (G j).isSome → X.rootReason.get! j = s₁.rootReason.get! j) : Inv X G := by
  have hch := ((h₁.chain hd₁).vars_ext hv h₁.asg.trail_lt).congr htr hre
  refine { hX with
    slack := hXS
    rootLen := fun _ => by rw [e2, htr]; exact h₁.rootLen hd₁
    rr := fun _ k hk => ?_
    chain := fun _ => hch
    conflict := fun _ k hk => ?_ }
  · obtain ⟨pc, hpc, -⟩ := hch k hk (Nat.zero_le _)
    have hk' : k < s₁.asg.trail.size := by rw [← htr]; exact hk
    have htk : X.asg.trail[k] = s₁.asg.trail[k] := by simp [htr]
    rw [hrr _ (by rw [hpc]; rfl), htk, hre _ (by simp)]
    exact h₁.rr hd₁ k hk'
  · rw [e3] at hk
    obtain ⟨pc, hpc, hsl⟩ := h₁.conflict hd₁ k hk
    refine ⟨pc, hpc, ?_⟩
    rw [htr, tlits_ext hv h₁.asg.trail_lt]
    exact hsl

/-- **Removing the negation** after backtracking restores the invariant of the database. -/
private theorem removal_spec {s₁ s₆ : EState} {G : ℕ → Option PBConstr} {neg : PBConstr}
    {ts : Array (ℕ × ℕ)} {d start : ℕ} {res : Option (Array Hint)}
    (h₁ : Inv s₁ G) (hd₁ : s₁.dirty = false)
    (hGi : G s₁.cons.size = none)
    (hI₆ : InvCore s₆ (Function.update G s₁.cons.size (some neg)))
    (hS₆ : SlackOk s₆ (Function.update G s₁.cons.size (some neg)))
    (he : AsgExt s₁.asg s₆.asg) (hv : s₁.vars.toList <+: s₆.vars.toList)
    (hcons : s₆.cons = s₁.cons.push s₆.cons[s₁.cons.size]!)
    (hcl : s₆.cons[s₁.cons.size]!.clause = false) (hst : s₆.cons[s₁.cons.size]!.start = start)
    (hrr : ∀ j, j ≠ s₁.cons.size → s₆.rootReason.get! j = s₁.rootReason.get! j)
    (hrl : s₆.rootLen = s₁.rootLen)
    (hrc6 : s₆.rootConflict = s₁.rootConflict) (hroots : s₆.roots = s₁.roots)
    (hocc : ∀ ℓ : ℕ, ∃ PA PB : List (ℕ × ℕ), s₆.occ[ℓ]!.toList = flatL (PA ++ PB) ∧
      (∀ p ∈ PA, p.1 ≠ s₁.cons.size) ∧ (∀ p ∈ PB, p.1 = s₁.cons.size) ∧
      PB.length = if 0 < d then (ts.toList.filter (·.2 == ℓ)).length else 0)
    (hts : ∀ p ∈ ts, p.2 < s₆.occ.size) :
    Inv (removeTail (s₆.backtrack s₁.rootLen) ts d s₁.cons.size start res).1 G ∧
    (removeTail (s₆.backtrack s₁.rootLen) ts d s₁.cons.size start res).1.cons = s₁.cons := by
  have hrl₁ := h₁.rootLen hd₁
  have hle : s₁.rootLen ≤ s₆.asg.trail.size := by rw [hrl₁]; exact he.size_le
  obtain ⟨⟨sl7, as7, h7⟩, hI₇, hS₇, ht₇, hre₇⟩ := backtrack_spec hI₆ hS₆ hle
  generalize s₆.backtrack s₁.rootLen = s₇ at h7 hI₇ hS₇ ht₇ hre₇ ⊢
  have ho7 : s₇.occ = s₆.occ := by rw [h7]
  have hc7 : s₇.cons = s₆.cons := by rw [h7]
  choose PA PB hPA using hocc
  have hi1 : 1 ≤ s₁.cons.size := h₁.cons_pos
  have hi : s₁.cons.size + 1 = s₇.cons.size := by rw [hc7, hcons]; simp
  have hroots₇ : ∀ j ∈ s₇.roots, j ≠ s₁.cons.size := by
    intro j hj
    have : s₇.roots = s₁.roots := by rw [h7, hroots]
    rw [this] at hj
    exact Nat.ne_of_lt (h₁.roots j hj).1
  -- The trail after backtracking is the root trail.
  have htr : s₇.asg.trail = s₁.asg.trail := by
    rw [ht₇]
    apply Array.toList_inj.1
    have : (s₆.asg.trail.take s₁.rootLen).toList = s₆.asg.trail.toList.take s₁.rootLen := by
      simp
    rw [this, hrl₁]
    exact (List.prefix_iff_eq_take.1 he.1).symm.trans (by simp)
  have hfin : ∀ occ : Array (Array ℕ), occ.size = s₇.occ.size →
      (∀ ℓ : ℕ, occ[ℓ]!.toList = flatL (PA ℓ)) →
      Inv { s₇ with occ := occ
                    cons := s₇.cons.pop
                    cpos := s₇.cpos.pop
                    alive := s₇.alive.set! s₁.cons.size 0
                    lits := s₇.lits.shrink start
                    coeffs := s₇.coeffs.shrink start
                    slack := s₇.slack.pop } G ∧
      s₇.cons.pop = s₁.cons := by
    intro occ hsz hF
    obtain ⟨hc, hs⟩ := removeNeg_core (s := s₇) (occ := occ) (PA := PA) (st := start) hI₇ hS₇
      hGi hi1 hi (by rw [hc7]; exact hcl) hroots₇ (by rw [hc7]; exact hst) hsz
      (fun ℓ => ⟨hF ℓ, (hPA ℓ).2.1, PB ℓ, by rw [ho7]; exact (hPA ℓ).1, (hPA ℓ).2.2.1⟩)
    have hv7 : s₇.vars = s₆.vars := by rw [h7]
    refine ⟨Inv.of_root h₁ hd₁ hc hs (show s₇.rootLen = s₁.rootLen by rw [h7]; exact hrl)
      (show s₇.rootConflict = s₁.rootConflict by rw [h7]; exact hrc6) htr
      (fun ℓ hℓ => by change s₇.asg.reason[ℓ / 2]! = _; rw [hre₇]; exact he.2 ℓ hℓ)
      (by change s₁.vars.toList <+: s₇.vars.toList; rw [hv7]; exact hv) (fun j hj => ?_), ?_⟩
    · change s₇.rootReason.get! j = s₁.rootReason.get! j
      have hlt := ((h₁.live j).1 hj).1
      rw [h7]; exact hrr j (by omega)
    · rw [hc7, hcons]; simp
  unfold removeTail
  simp only [Id.run]
  split
  · rename_i hd
    rw [Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]
    have hpop := popAll PA s₁.cons.size ts.toList s₇
      (fun x hx => by rw [ho7]; exact hts x (by simpa using hx))
      (fun ℓ => ⟨PB ℓ, by rw [ho7]; exact (hPA ℓ).1, by rw [(hPA ℓ).2.2.2, ite_pos hd]⟩)
    generalize ts.toList.foldl (fun b x => { b with occ := b.occ.modify x.2 fun x => x.pop.pop })
      s₇ = F at hpop ⊢
    obtain ⟨⟨occ, rfl⟩, hsz, hF⟩ := hpop
    exact hfin occ hsz hF
  · rename_i hd
    refine hfin s₇.occ rfl fun ℓ => ?_
    have h0 := (hPA ℓ).2.2.2
    rw [ite_neg hd, List.length_eq_zero_iff] at h0
    have := (hPA ℓ).1
    rw [h0, List.append_nil, ho7] at *
    exact this

/-- **The hints of `rup`** keep the invariant, and a reported conflict is a real one. -/
private theorem rupHints_spec {s : EState} {G : ℕ → Option PBConstr} (h : Inv s G)
    (neg : PBConstr) :
    Inv (s.rupHints neg).1 G ∧ (s.rupHints neg).1.cons = s.cons ∧
    ∀ {db : List (ℕ × PBConstr)},
      (∀ c pc, G c = some pc → resolve db neg s.cons[c]!.hint = some pc) →
      (s.rupHints neg).2.isSome = true → ∃ hs, VeriPB.rupHints db neg hs [] = true := by
  have h1 := rebuilt_spec h
  unfold EState.rupHints
  simp only [Id.run]
  generalize (if s.dirty = true then s.rebuild else s) = s₁ at h1 ⊢
  obtain ⟨h₁, hc₁, hd₁⟩ := h1
  rw [← hc₁]
  split
  · rename_i k hk
    obtain ⟨seen, hseen⟩ := analyze_fst s₁ k
    refine ⟨?_, ?_, fun hres _ => ?_⟩
    · change Inv (s₁.analyze k).1 G
      rw [hseen]; exact { h₁ with }
    · change (s₁.analyze k).1.cons = s₁.cons
      rw [hseen]
    · obtain ⟨pc, hpc, hsl⟩ := h₁.conflict hd₁ k hk
      exact rup_of_chain (h₁.chain hd₁) hres hpc hsl
  · rename_i hk
    have hGi := h₁.toInvCore.none_of_size
    obtain ⟨⟨vI, vs, val, rea, tp, wa, oc, hc2⟩, hI₂, hS₂, hvx, hax, hperm, hlt⟩ :=
      codes_spec h₁.toInvCore h₁.slack neg
    generalize s₁.codes neg = p at hc2 hI₂ hS₂ hvx hax hperm hlt ⊢
    obtain ⟨s₂, ts⟩ := p
    dsimp only at hc2 hI₂ hS₂ hvx hax hperm hlt ⊢
    have hcs : s₂.cons = s₁.cons := by rw [hc2]
    obtain ⟨hi, ⟨al, li, co, sl, rr, oc', hc3⟩, hI₃, hsl₃, hal₃, hw₃, hrr₃, -, -, hocc₃⟩ :=
      pushCons_spec (hh := .neg) (s0 := 0) (cl := false) hI₂ hperm hlt rfl (by simp)
    generalize s₂.pushCons ts neg.degree 0 false .neg = q at hi hc3 hI₃ hsl₃ hal₃ hw₃ hrr₃ hocc₃ ⊢
    obtain ⟨s₃, i⟩ := q
    dsimp only at hi hc3 hI₃ hsl₃ hal₃ hw₃ hrr₃ hocc₃ ⊢
    rw [hcs] at hi hI₃ hrr₃ hocc₃
    subst hi
    have hGi' : Function.update G s₁.cons.size (some neg) s₁.cons.size = some neg := by simp
    have hv32 : s₃.vars = s₂.vars := by rw [hc3]
    have hcons₃ : s₃.cons = s₁.cons.push s₃.cons[s₁.cons.size]! := by
      rw [hc3, hcs]; simp
    have hrec : s₃.cons[s₁.cons.size]! = ⟨s₂.lits.size, ts.size, neg.degree, 0, false, .neg⟩ := by
      rw [hc3, hcs, getElem!_eq, Array.getElem?_push]; simp
    have hsize₃ : s₁.cons.size + 1 = s₃.cons.size := by rw [hcons₃]; simp
    have hS₃ := slack_push (pc := neg) hI₂ hS₂ (by rw [hc3]) hsl₃ (by rw [hc3]) (by rw [hc3])
      (by rw [hc3])
    rw [hcs] at hS₃
    obtain ⟨⟨li4, wa4, sl4, as4, h4⟩, hI₄, hS₄, he₄, hn₄, hk₄⟩ :=
      checkFresh_spec hI₃ hS₃ hGi' hsize₃ (by simpa [hv32] using hal₃) hw₃
    generalize s₃.checkFresh s₁.cons.size = q at h4 hI₄ hS₄ he₄ hn₄ hk₄ ⊢
    obtain ⟨s₄, cf⟩ := q
    dsimp only at h4 hI₄ hS₄ he₄ hn₄ hk₄ ⊢
    have hal3 : s₃.alive.get! s₂.cons.size ≠ 0 := by
      rw [hcs]; exact ((hI₃.live _).1 (by rw [hGi']; rfl)).2
    have hsplit := occ_split (X := s₃) hI₂ (by rw [hcs]; exact hocc₃) hal3
    have e3 : s₃.dirty = s₁.dirty ∧ s₃.rootLen = s₁.rootLen ∧ s₃.rootConflict = s₁.rootConflict ∧
        s₃.roots = s₁.roots ∧ s₃.asg = s₂.asg ∧ s₂.rootReason = s₁.rootReason := by
      rw [hc3, hc2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hres' : ∀ {db : List (ℕ × PBConstr)},
        (∀ c pc, G c = some pc → resolve db neg s₁.cons[c]!.hint = some pc) →
        ∀ c pc, Function.update G s₁.cons.size (some neg) c = some pc →
          resolve db neg s₃.cons[c]!.hint = some pc := by
      intro db hres c pc hc
      by_cases hci : c = s₁.cons.size
      · subst hci
        simp only [hGi', Option.some.injEq] at hc
        rw [hrec, ← hc]; rfl
      · have hG : G c = some pc := by simpa [Function.update, hci] using hc
        have hlt' : c < s₁.cons.size := ((h₁.live c).1 (by simp [hG])).1
        rw [hcons₃, getElem!_eq, Array.getElem?_push, ite_neg (by omega), ← getElem!_eq]
        exact hres c pc hG
    have hch : ChainFrom s₃.vars (Function.update G s₁.cons.size (some neg)) 0 s₃.asg := by
      rw [hv32, e3.2.2.2.2.1]
      have h0 := ((h₁.chain hd₁).vars_ext hvx h₁.asg.trail_lt).mono
        (G' := Function.update G s₁.cons.size (some neg)) (fun _ _ => update_some_of hGi)
      have hsz : s₁.asg.trail.size = s₂.asg.trail.size := by rw [hc2]
      exact h0.ext hax (by rw [hsz]; exact ChainFrom.of_size _ _ _)
    have leaf : ∀ (X : EState) (res : Option (Array Hint)),
        InvCore X (Function.update G s₁.cons.size (some neg)) →
        SlackOk X (Function.update G s₁.cons.size (some neg)) → AsgExt s₃.asg X.asg →
        X.vars = s₃.vars → X.cons = s₃.cons → X.rootReason = s₃.rootReason →
        X.rootLen = s₃.rootLen → X.rootConflict = s₃.rootConflict →
        X.roots = s₃.roots → X.occ.size = s₃.occ.size →
        (∀ ℓ : ℕ, X.occ[ℓ]! = s₃.occ[ℓ]! ∨ X.occ[ℓ]!.toList =
          flatL ((pairsL s₃.occ[ℓ]!.toList).filter fun p => s₃.alive.get! p.1 != 0)) →
        (∀ {db : List (ℕ × PBConstr)},
          (∀ c pc, G c = some pc → resolve db neg s₁.cons[c]!.hint = some pc) →
          res.isSome = true → ∃ hs, VeriPB.rupHints db neg hs [] = true) →
        Inv (removeTail (X.backtrack s₁.rootLen) ts neg.degree s₁.cons.size
            s₃.cons[s₁.cons.size]!.start res).1 G ∧
          (removeTail (X.backtrack s₁.rootLen) ts neg.degree s₁.cons.size
            s₃.cons[s₁.cons.size]!.start res).1.cons = s₁.cons ∧
          ∀ {db : List (ℕ × PBConstr)},
            (∀ c pc, G c = some pc → resolve db neg s₁.cons[c]!.hint = some pc) →
            (removeTail (X.backtrack s₁.rootLen) ts neg.degree s₁.cons.size
              s₃.cons[s₁.cons.size]!.start res).2.isSome = true →
            ∃ hs, VeriPB.rupHints db neg hs [] = true := by
      intro X res hIX hSX heX hvX hcX hrX hrlX hrcX hroX hosX hoX hsound
      have hocc := occ_split (X := X) hI₂ (by rw [hcs]; exact hocc₃) hal3 hoX
      rw [hcs] at hocc
      obtain ⟨hinv, hcons⟩ := removal_spec (neg := neg) (res := res)
        (start := s₃.cons[s₁.cons.size]!.start) h₁ hd₁ hGi hIX hSX
        (by rw [e3.2.2.2.2.1] at heX; exact hax.trans heX)
        (by rw [hvX, hv32]; exact hvx) (by rw [hcX]; exact hcons₃)
        (by rw [hcX, hrec]) (by rw [hcX])
        (fun j hj => by rw [hrX, hrr₃ j hj, e3.2.2.2.2.2])
        (by rw [hrlX, e3.2.1]) (by rw [hrcX, e3.2.2.1])
        (by rw [hroX, e3.2.2.2.1]) hocc
        (fun p hp => by
          rw [hosX, hI₃.occ_size, hv32]; exact hlt p hp)
      exact ⟨hinv, hcons, fun hres hs => hsound hres (by rwa [removeTail_snd] at hs)⟩
    cases cf with
    | some k =>
      obtain ⟨seen, hseen⟩ := analyze_fst s₄ k
      have e4 : s₄.vars = s₃.vars ∧ s₄.cons = s₃.cons ∧ s₄.rootReason = s₃.rootReason ∧
          s₄.dirty = s₃.dirty ∧ s₄.rootLen = s₃.rootLen ∧ s₄.rootConflict = s₃.rootConflict ∧
          s₄.roots = s₃.roots ∧ s₄.occ = s₃.occ := by
        rw [h4]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      dsimp only
      rw [hseen]
      exact leaf { s₄ with seen } (some (s₄.analyze k).2) { hI₄ with } hS₄ he₄ e4.1 e4.2.1
        e4.2.2.1 e4.2.2.2.2.1
        e4.2.2.2.2.2.1 e4.2.2.2.2.2.2.1 (by simp [e4.2.2.2.2.2.2.2])
        (fun ℓ => Or.inl (by simp [e4.2.2.2.2.2.2.2]))
        (fun hres _ => by
          obtain ⟨pc, hpc, hsl⟩ := hk₄ k rfl
          rw [← e4.1] at hsl
          refine rup_of_chain (cons := s₄.cons) ?_ ?_ hpc hsl
          · rw [e4.1]; exact hch.ext he₄ hn₄
          · rw [e4.2.1]; exact hres' hres)
    | none =>
      obtain ⟨⟨li5, wa5, oc5, sl5, as5, qh5, h5⟩, hI₅, hS₅, he₅, hn₅, ho₅, hk₅⟩ :=
        propagate_spec hI₄ hS₄
      have e4 : s₄.vars = s₃.vars ∧ s₄.cons = s₃.cons ∧ s₄.rootReason = s₃.rootReason ∧
          s₄.dirty = s₃.dirty ∧ s₄.rootLen = s₃.rootLen ∧ s₄.rootConflict = s₃.rootConflict ∧
          s₄.roots = s₃.roots ∧ s₄.occ = s₃.occ ∧ s₄.alive = s₃.alive := by
        rw [h4]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have e5 : s₄.propagate.1.vars = s₃.vars ∧ s₄.propagate.1.cons = s₃.cons ∧
          s₄.propagate.1.rootReason = s₃.rootReason ∧ s₄.propagate.1.dirty = s₃.dirty ∧
          s₄.propagate.1.rootLen = s₃.rootLen ∧
          s₄.propagate.1.rootConflict = s₃.rootConflict ∧ s₄.propagate.1.roots = s₃.roots := by
        rw [h5, h4]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hos5 : s₄.propagate.1.occ.size = s₃.occ.size := by
        rw [hI₅.occ_size, hI₃.occ_size, e5.1]
      have ho5 : ∀ ℓ : ℕ, s₄.propagate.1.occ[ℓ]! = s₃.occ[ℓ]! ∨ s₄.propagate.1.occ[ℓ]!.toList =
          flatL ((pairsL s₃.occ[ℓ]!.toList).filter fun p => s₃.alive.get! p.1 != 0) := by
        rw [← e4.2.2.2.2.2.2.2.1, ← e4.2.2.2.2.2.2.2.2]; exact ho₅
      dsimp only
      rcases hq : s₄.propagate with ⟨s₅, cf'⟩
      rw [hq] at h5 hI₅ hS₅ he₅ hn₅ hk₅ e5 hos5 ho5
      dsimp only at h5 hI₅ hS₅ he₅ hn₅ hk₅ e5 hos5 ho5 ⊢
      cases cf' with
      | some k =>
        obtain ⟨seen, hseen⟩ := analyze_fst s₅ k
        rw [hseen]
        exact leaf { s₅ with seen } (some (s₅.analyze k).2) { hI₅ with } hS₅ (he₄.trans he₅)
          e5.1 e5.2.1 e5.2.2.1
          e5.2.2.2.2.1 e5.2.2.2.2.2.1 e5.2.2.2.2.2.2 hos5 ho5
          (fun hres _ => by
            obtain ⟨pc, hpc, hsl⟩ := hk₅ k rfl
            rw [e4.1] at hsl
            rw [← e5.1] at hsl
            refine rup_of_chain (cons := s₅.cons) ?_ ?_ hpc hsl
            · rw [e5.1]
              exact (hch.ext he₄ hn₄).ext he₅ (by rw [← e4.1]; exact hn₅)
            · rw [e5.2.1]; exact hres' hres)
      | none =>
        exact leaf _ _ hI₅ hS₅ (he₄.trans he₅) e5.1 e5.2.1 e5.2.2.1
          e5.2.2.2.2.1 e5.2.2.2.2.2.1 e5.2.2.2.2.2.2 hos5 ho5 (fun _ h => by simp at h)

/-- **Extending an assignment** keeps the invariant. -/
private theorem extend_spec {s : EState} {G : ℕ → Option PBConstr} (h : Inv s G)
    (ls : List (Literal ℕ)) :
    Inv (s.extend ls).1 G ∧ (s.extend ls).1.cons = s.cons := by
  have h1 := rebuilt_spec h
  unfold EState.extend
  simp only [Id.run]
  generalize (if s.dirty = true then s.rebuild else s) = s₁ at h1 ⊢
  obtain ⟨h₁, hc₁, hd₁⟩ := h1
  rw [← hc₁]
  split
  · exact ⟨h₁, rfl⟩
  have fin : ∀ Y : EState, InvCore Y G → SlackOk Y G → AsgExt s₁.asg Y.asg →
      s₁.vars.toList <+: Y.vars.toList → Y.cons = s₁.cons → Y.rootReason = s₁.rootReason →
      Y.rootLen = s₁.rootLen → Y.rootConflict = s₁.rootConflict →
      Inv (Y.backtrack s₁.rootLen) G ∧ (Y.backtrack s₁.rootLen).cons = s₁.cons := by
    intro Y hY hYS he hv e1 e2 e4 e5
    have hle : s₁.rootLen ≤ Y.asg.trail.size := by rw [h₁.rootLen hd₁]; exact he.size_le
    obtain ⟨⟨sl, as, hb⟩, hI, hS, ht, hre⟩ := backtrack_spec hY hYS hle
    have htr : (Y.backtrack s₁.rootLen).asg.trail = s₁.asg.trail := by
      rw [ht]
      apply Array.toList_inj.1
      have : (Y.asg.trail.take s₁.rootLen).toList = Y.asg.trail.toList.take s₁.rootLen := by simp
      rw [this, h₁.rootLen hd₁]
      exact (List.prefix_iff_eq_take.1 he.1).symm.trans (by simp)
    refine ⟨Inv.of_root h₁ hd₁ hI hS (by rw [hb]; exact e4)
      (by rw [hb]; exact e5) htr (fun ℓ hℓ => by rw [hre]; exact he.2 ℓ hℓ)
      (by rw [hb]; exact hv) (fun j _ => by rw [hb, e2]), by rw [hb]; exact e1⟩
  refine bind_forIn_list_inv (fun st : EState × Bool => InvCore st.1 G ∧ SlackOk st.1 G ∧
      AsgExt s₁.asg st.1.asg ∧ s₁.vars.toList <+: st.1.vars.toList ∧ st.1.cons = s₁.cons ∧
      st.1.rootReason = s₁.rootReason ∧ st.1.dirty = s₁.dirty ∧ st.1.rootLen = s₁.rootLen ∧
      st.1.rootConflict = s₁.rootConflict)
    (fun r : EState × Option (Array (Literal ℕ)) => Inv r.1 G ∧ r.1.cons = s₁.cons)
    (init := (s₁, true))
    ⟨h₁.toInvCore, h₁.slack, AsgExt.refl _, List.prefix_refl _, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_
  · rintro l - ⟨st, ok⟩ ⟨hI, hS, he, hv, e1, e2, e3, e4, e5⟩
    dsimp only at hI hS he hv e1 e2 e3 e4 e5
    obtain ⟨⟨vI, vs, val, rea, tp, wa, oc, hc⟩, hI', hS', hv', he', hlt, -⟩ := litCode_spec hI hS l
    have e' : (st.litCode l).1.cons = s₁.cons ∧ (st.litCode l).1.rootReason = s₁.rootReason ∧
        (st.litCode l).1.dirty = s₁.dirty ∧ (st.litCode l).1.rootLen = s₁.rootLen ∧
        (st.litCode l).1.rootConflict = s₁.rootConflict := by
      rw [hc]; exact ⟨e1, e2, e3, e4, e5⟩
    have hP : InvCore (st.litCode l).1 G ∧ SlackOk (st.litCode l).1 G ∧
        AsgExt s₁.asg (st.litCode l).1.asg ∧ s₁.vars.toList <+: (st.litCode l).1.vars.toList ∧
        (st.litCode l).1.cons = s₁.cons ∧ (st.litCode l).1.rootReason = s₁.rootReason ∧
        (st.litCode l).1.dirty = s₁.dirty ∧ (st.litCode l).1.rootLen = s₁.rootLen ∧
        (st.litCode l).1.rootConflict = s₁.rootConflict :=
      ⟨hI', hS', he.trans he', hv.trans hv', e'⟩
    dsimp only
    split
    · rename_i h0
      have h0' : (st.litCode l).1.asg.value.get! (st.litCode l).2 = 0 := by
        simpa [litVal] using h0
      obtain ⟨ha, hea, -, -⟩ := hI'.asg.assign (r := 0) hlt h0'
      obtain ⟨hI'', hS''⟩ := InvCore.asg_ext hI' hS' ha hea
      exact ⟨hI'', hS'', (he.trans he').trans hea, hv.trans hv', e'⟩
    · split
      · exact hP
      · exact hP
  · rintro ⟨st, ok⟩ ⟨hI, hS, he, hv, e1, e2, e3, e4, e5⟩
    dsimp only at hI hS he hv e1 e2 e3 e4 e5 ⊢
    split
    · obtain ⟨⟨li, wa, oc, sl, as, qh, hp⟩, hI', hS', he', -, -, -⟩ := propagate_spec hI hS
      have hp' : st.propagate.1 = { st with lits := li
                                            watches := wa
                                            occ := oc
                                            slack := sl
                                            asg := as
                                            qhead := qh } := hp
      have f1 : st.propagate.1.vars = st.vars ∧ st.propagate.1.cons = st.cons ∧
          st.propagate.1.rootReason = st.rootReason ∧ st.propagate.1.dirty = st.dirty ∧
          st.propagate.1.rootLen = st.rootLen ∧ st.propagate.1.rootConflict = st.rootConflict := by
        rw [hp']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact fin st.propagate.1 hI' hS' (he.trans he') (f1.1 ▸ hv) (f1.2.1.trans e1)
        (f1.2.2.1.trans e2) (f1.2.2.2.2.1.trans e4)
        (f1.2.2.2.2.2.trans e5)
    · exact fin st hI hS he hv e1 e2 e4 e5

private theorem empty_getElem! (ℓ : ℕ) : (#[] : Array (Array ℕ))[ℓ]! = #[] := by
  simp only [getElem!_eq, Array.getElem?_empty, Option.getD_none]; rfl

/-- The empty engine satisfies the invariant. -/
private theorem inv_new : Inv ({} : EState) fun _ => none where
  nodup := by simp
  idx_some := by simp
  idx_mem := by simp
  asg := ⟨by rfl, rfl, rfl, by simp, by simp, by simp, by simp⟩
  watches_size := rfl
  occ_size := rfl
  qhead_le := le_rfl
  cons_pos := le_rfl
  cpos_size := rfl
  slack_size := rfl
  alive_size := le_rfl
  rr_size := le_rfl
  coeffs_size := rfl
  layout := by intro c h1 h2; simp at h2; omega
  alive0 := rfl
  live := by
    intro c
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro hc
    have : c = 0 := by simpa using hc
    subst this; decide
  rep := by simp
  occ_even := by
    intro ℓ; change (#[] : Array (Array ℕ))[ℓ]!.size % 2 = 0; rw [empty_getElem!]; rfl
  occ_name := by
    intro ℓ p hp
    change p ∈ pairsL (#[] : Array (Array ℕ))[ℓ]!.toList at hp
    rw [empty_getElem!] at hp
    simp [pairsL] at hp
  occ_exact := by simp
  watch_name := by
    intro ℓ c hc
    change c ∈ (#[] : Array (Array ℕ))[ℓ]! at hc
    rw [empty_getElem!] at hc
    simp at hc
  watch_count := by simp
  roots := by simp
  slack := by intro c pc hc; simp at hc
  rootLen := fun _ => rfl
  rr := by simp
  chain := by intro _ k hk; simp at hk
  conflict := by simp

end Cslib.Logic.PL.VeriPB.Elab

namespace Cslib.Logic.PL.VeriPB.Elab.Engine

open EState

/-- `e` is built from `Cslib.Logic.PL.VeriPB.Elab.Engine.new` by the engine's operations, and `D`
gives the kernel hint and the constraint of each engine index added and not deleted since. -/
inductive Built : Engine → (ℕ → Option (Hint × PBConstr)) → Prop
  /-- The empty engine holds no constraint. -/
  | new : Built Engine.new fun _ => none
  /-- Adding a constraint gives it the returned index. -/
  | add {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (c : PBConstr) (h : Hint) :
      Built e D → Built (e.add c h).1 (Function.update D (e.add c h).2 (some (h, c)))
  /-- Deleting the constraint of an index. -/
  | kill {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (i : ℕ) :
      Built e D → Built (e.kill i) (Function.update D i none)
  /-- The search for the hints of a `rup` step keeps the constraints. -/
  | rupHints {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (neg : PBConstr) :
      Built e D → Built (e.rupHints neg).1 D
  /-- Extending an assignment keeps the constraints. -/
  | extend {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (ls : List (Literal ℕ)) :
      Built e D → Built (e.extend ls).1 D

private theorem add_eq' (e : Engine) (c : PBConstr) (h : Hint) :
    e.add c h = (⟨(e.st.add c h).1⟩, (e.st.add c h).2) := by
  unfold Engine.add; rcases e.st.add c h with ⟨s, i⟩; rfl

private theorem rupHints_eq' (e : Engine) (neg : PBConstr) :
    e.rupHints neg = (⟨(e.st.rupHints neg).1⟩, (e.st.rupHints neg).2) := by
  unfold Engine.rupHints; rcases e.st.rupHints neg with ⟨s, i⟩; rfl

private theorem extend_eq' (e : Engine) (ls : List (Literal ℕ)) :
    e.extend ls = (⟨(e.st.extend ls).1⟩, (e.st.extend ls).2) := by
  unfold Engine.extend; rcases e.st.extend ls with ⟨s, i⟩; rfl

/-- The invariant of a built engine, and its constraints. -/
private theorem Built.inv {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (hB : Built e D) :
    ∃ G, Inv e.st G ∧ ∀ c, D c = (G c).map fun pc => (e.st.cons[c]!.hint, pc) := by
  induction hB with
  | new => exact ⟨fun _ => none, inv_new, fun _ => rfl⟩
  | @add e D c h _ ih =>
    obtain ⟨G, hI, hD⟩ := ih
    obtain ⟨hi, hI', hcons, hhint⟩ := add_spec hI c h
    refine ⟨Function.update G e.st.cons.size (some c), ?_, fun c' => ?_⟩
    · rw [add_eq']; exact hI'
    · rw [add_eq']
      dsimp only
      rw [hi]
      by_cases hc : c' = e.st.cons.size
      · subst hc; simp [hhint]
      · simp only [Function.update, hc, dite_false]
        rw [hD c']
        cases hg : G c' with
        | none => rfl
        | some pc =>
          have hlt := ((hI.live c').1 (by simp [hg])).1
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
          rw [hcons, getElem!_eq, getElem!_eq, Array.getElem?_push, ite_neg (by omega)]
  | @kill e D i _ ih =>
    obtain ⟨G, hI, hD⟩ := ih
    obtain ⟨hI', hcons⟩ := kill_spec hI i
    refine ⟨Function.update G i none, hI', fun c => ?_⟩
    by_cases hc : c = i
    · subst hc; simp
    · simp only [Function.update, hc, dite_false, Engine.kill]
      rw [hD c, hcons]
  | @rupHints e D neg _ ih =>
    obtain ⟨G, hI, hD⟩ := ih
    obtain ⟨hI', hcons, -⟩ := rupHints_spec hI neg
    refine ⟨G, by rw [rupHints_eq']; exact hI', fun c => ?_⟩
    rw [rupHints_eq']; dsimp only; rw [hcons]; exact hD c
  | @extend e D ls _ ih =>
    obtain ⟨G, hI, hD⟩ := ih
    obtain ⟨hI', hcons⟩ := extend_spec hI ls
    refine ⟨G, by rw [extend_eq']; exact hI', fun c => ?_⟩
    rw [extend_eq']; dsimp only; rw [hcons]; exact hD c

/-- **Soundness of the propagation engine.** If the engine `e`, built by its operations with
the constraints `D`, reports a conflict for the negation `neg` (`Engine.rupHints` returns hints),
then some list of hints takes the kernel's propagation (`Cslib.Logic.PL.VeriPB.rupHints`) from
`neg` and the database `db` to a conflict, provided `db` holds each constraint of `D` under its
hint. -/
theorem Built.rupHints_sound {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (hB : Built e D)
    {db : List (ℕ × PBConstr)} {neg : PBConstr}
    (hdb : ∀ i h c, D i = some (h, c) → resolve db neg h = some c)
    (hr : (e.rupHints neg).2.isSome = true) : ∃ hs, VeriPB.rupHints db neg hs [] = true := by
  obtain ⟨G, hI, hD⟩ := hB.inv
  rw [rupHints_eq'] at hr
  refine (rupHints_spec hI neg).2.2 (fun c pc hc => hdb c _ _ ?_) hr
  rw [hD c, hc]; rfl

/-- **A conflict of the engine is a RUP proof**: if the engine reports a conflict for the
negation of `C`, then `C` follows from the database by reverse unit propagation
(`Cslib.Logic.PL.VeriPB.rup`) along some list of hints. -/
theorem Built.rup_of_rupHints {e : Engine} {D : ℕ → Option (Hint × PBConstr)} (hB : Built e D)
    {db : List (ℕ × PBConstr)} {C : PBConstr}
    (hdb : ∀ i h c, D i = some (h, c) → resolve db C.negate h = some c)
    (hr : (e.rupHints C.negate).2.isSome = true) : ∃ hs, rup db C hs = true :=
  hB.rupHints_sound hdb hr

end Cslib.Logic.PL.VeriPB.Elab.Engine
