/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Circuit.Encoding.Combinators
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# A constant-depth circuit detecting a violated clause

For a CNF formula `Φ` over variables numbered by `ℕ`, `cnfCheck n Φ` is a circuit over
`Unbounded.extSignature` on `n` inputs that outputs `true` exactly when the input assignment
violates some clause of `Φ`, provided every variable of `Φ` is below `n`. It is an unbounded
fan-in disjunction over the clauses of unbounded fan-in conjunctions of the falsified literals: a
literal `(v, false)` is falsified by the input `v` itself and a literal `(v, true)` by its
negation, so the depth is at most three whichever gates `extInterpretation` gives the extra gates.

The construction is total: a literal whose variable is not below `n` is dropped, and the circuit
is correct only under the stated bound on the variables. The raw code of the circuit is built
from `Circuit.compCode` and `Circuit.appendCodes` by list operations on `Φ`, so it is computed in
polynomial time from `n` in binary and the encoded formula `Φ`, without enumerating the `n` inputs.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.cnfCheck`: the circuit.
* `Cslib.Circuits.Boolean.Unbounded.cnfCheckCode`: its raw code, by list operations.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_cnfCheck`: the circuit outputs the negation of the value
  of `Φ` on the assignment the input describes.
* `Cslib.Circuits.Boolean.Unbounded.depth_cnfCheck_le`: depth at most three.
* `Cslib.Circuits.Boolean.Unbounded.code_cnfCheck`: the code of `cnfCheck n Φ` is
  `cnfCheckCode n Φ`.
* `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_cnfCheckCode`: the code is computed in
  polynomial time.
-/

public section

namespace Cslib.Circuits.Boolean.Unbounded

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-! ### The typed circuit -/

/-- One gate `op` of arity `m` reading all `m` inputs in order. -/
private def fanInGate (op : ExtOp) (m : ℕ) (h : op.arity = m) : Circuit extSignature m 1 :=
  Circuit.oneGate (σ := extSignature) op (Fin.cast h)

/-- The circuit computing whether the literal `(v, b)` is falsified by the input: the input `v`
itself for `b = false` and its negation for `b = true`. -/
private def literalCircuit (n : ℕ) (p : Fin n × Bool) : Circuit extSignature n 1 :=
  if p.2 then Circuit.oneGate (σ := extSignature) (.ac .not) fun _ => p.1
  else Circuit.wiring extSignature fun _ => p.1

/-- The literals of a clause whose variable is below `n`. -/
private def clauseLits (n : ℕ) (c : Clause ℕ) : List (Fin n × Bool) :=
  c.filterMap fun l => if h : l.1 < n then some (⟨l.1, h⟩, l.2) else none

/-- The conjunction of the falsified-literal circuits of a list of literals. -/
private def clauseCircuit (n : ℕ) (L : List (Fin n × Bool)) : Circuit extSignature n 1 :=
  (fanInGate (.ac (.and L.length)) L.length rfl).comp
    (Circuit.pi fun j : Fin L.length => literalCircuit n L[j])

/-- **A circuit detecting a violated clause.** On `n` inputs it outputs `true` exactly when some
clause of `Φ` is falsified by the input read as an assignment to the variables below `n`
(`eval_cnfCheck`). Literals whose variable is not below `n` are ignored. -/
def cnfCheck (n : ℕ) (Φ : CNF ℕ) : Circuit extSignature n 1 :=
  (fanInGate (.ac (.or Φ.length)) Φ.length rfl).comp
    (Circuit.pi fun j : Fin Φ.length => clauseCircuit n (clauseLits n Φ[j]))

private theorem eval_literalCircuit (g : ∀ m, BooleanFunction m) {n : ℕ} (p : Fin n × Bool)
    (x : BitString n) : (literalCircuit n p).eval (extInterpretation g) x 0 = (x p.1 != p.2) := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [literalCircuit]

private theorem eval_clauseCircuit (g : ∀ m, BooleanFunction m) {n : ℕ} (L : List (Fin n × Bool))
    (x : BitString n) : (clauseCircuit n L).eval (extInterpretation g) x 0 =
      decide (∀ p ∈ L, (x p.1 != p.2) = true) := by
  simp only [clauseCircuit, fanInGate, Circuit.eval_comp, Circuit.eval_oneGate,
    extInterpretation_ac, interpretation_and, Circuit.eval_pi, eval_literalCircuit, Fin.cast]
  congr 1
  apply propext
  rw [List.forall_mem_iff_getElem]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h j
    exact h j j.2

private theorem mem_clauseLits {n : ℕ} {c : Clause ℕ} {p : Fin n × Bool} :
    p ∈ clauseLits n c ↔ ∃ l ∈ c, l.1 = p.1.val ∧ l.2 = p.2 := by
  obtain ⟨⟨i, hi⟩, b⟩ := p
  simp only [clauseLits, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, h⟩
    split_ifs at h with hl1
    · simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
      exact ⟨l, hl, h.1, h.2⟩
  · rintro ⟨l, hl, h1, h2⟩
    refine ⟨l, hl, ?_⟩
    have hv : l.1 < n := h1 ▸ hi
    simp only [hv, ↓reduceDIte]
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq]
    exact ⟨h1, h2⟩

/-- The circuit `cnfCheck n Φ` outputs `true` exactly when the assignment given by the input
violates a clause of `Φ`, when all the variables of `Φ` are below `n`. -/
theorem eval_cnfCheck (q n : ℕ) (Φ : CNF ℕ) (hΦ : ∀ c ∈ Φ, ∀ l ∈ c, l.1 < n) (x : BitString n) :
    (cnfCheck n Φ).eval (extInterpretation (modGate q)) x 0 =
      !Φ.eval (fun v => if h : v < n then x ⟨v, h⟩ else false) := by
  set σ : ℕ → Bool := fun v => if h : v < n then x ⟨v, h⟩ else false with hσ
  have key : ∀ c ∈ Φ, (∀ p ∈ clauseLits n c, (x p.1 != p.2) = true) ↔ c.eval σ = false := by
    intro c hc
    rw [← Bool.not_eq_true, Clause.eval_eq_true_iff]
    push Not
    constructor
    · intro h l hl
      have hv := hΦ c hc l hl
      have := h (⟨l.1, hv⟩, l.2) (mem_clauseLits.2 ⟨l, hl, rfl, rfl⟩)
      simp only [hσ, hv, ↓reduceDIte]
      intro heq
      simp [heq] at this
    · intro h p hp
      obtain ⟨l, hl, h1, h2⟩ := mem_clauseLits.1 hp
      have hv := hΦ c hc l hl
      have := h l hl
      simp only [hσ, hv, ↓reduceDIte] at this
      have e : x p.1 = x ⟨l.1, hv⟩ := congrArg x (Fin.ext h1.symm)
      rw [e, ← h2]
      simpa using this
  simp only [cnfCheck, fanInGate, Circuit.eval_comp, Circuit.eval_oneGate, extInterpretation_ac,
    interpretation_or, Circuit.eval_pi, eval_clauseCircuit, Fin.cast]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', CNF.eval, List.all_eq_false]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨Φ[j.1], List.getElem_mem _, ?_⟩
    simp [(key _ (List.getElem_mem _)).1 hj]
  · rintro ⟨c, hc, hne⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact ⟨⟨i, hi⟩, (key _ hc).2 (by simpa using hne)⟩

/-- `cnfCheck n Φ` has depth at most three. -/
theorem depth_cnfCheck_le (n : ℕ) (Φ : CNF ℕ) : (cnfCheck n Φ).depth ≤ 3 := by
  have hlit (p : Fin n × Bool) : (literalCircuit n p).depth ≤ 1 := by
    unfold literalCircuit
    split_ifs <;> simp
  have hclause (L : List (Fin n × Bool)) : (clauseCircuit n L).depth ≤ 2 := by
    refine (Circuit.depth_comp_le _ _).trans ?_
    have := Circuit.depth_pi_le (fun j : Fin L.length => literalCircuit n L[j]) fun j => hlit _
    simp only [fanInGate, Circuit.depth_oneGate]
    omega
  refine (Circuit.depth_comp_le _ _).trans ?_
  have := Circuit.depth_pi_le (fun j : Fin Φ.length => clauseCircuit n (clauseLits n Φ[j]))
    fun j => hclause _
  simp only [fanInGate, Circuit.depth_oneGate]
  omega

/-! ### The raw code -/

/-- The raw code of one gate `op` reading the `m` inputs in order. -/
private def fanInCode (op : ExtOp) (m : ℕ) : List (ExtOp × List ℕ) × List ℕ :=
  ([(op, List.range m)], [m])

/-- The raw code of `literalCircuit`, on `n` inputs, of the literal with variable index `l.1`. -/
private def literalCode (n : ℕ) (l : ℕ × Bool) : List (ExtOp × List ℕ) × List ℕ :=
  if l.2 then ([(.ac .not, [l.1])], [n]) else ([], [l.1])

/-- The literals of a clause whose variable is below `n`, without their proofs. -/
private def inRange (n : ℕ) (c : Clause ℕ) : Clause ℕ :=
  c.filter fun l => decide (l.1 < n)

/-- The raw code of the conjunction over the clause `c`. -/
private def clauseCode (n : ℕ) (c : Clause ℕ) : List (ExtOp × List ℕ) × List ℕ :=
  Circuit.compCode n (fanInCode (.ac (.and (inRange n c).length)) (inRange n c).length)
    (Circuit.appendCodes n ((inRange n c).map (literalCode n)))

/-- **The raw code of `cnfCheck n Φ`**, by list operations on `Φ`. -/
def cnfCheckCode (n : ℕ) (Φ : CNF ℕ) : List (ExtOp × List ℕ) × List ℕ :=
  Circuit.compCode n (fanInCode (.ac (.or Φ.length)) Φ.length)
    (Circuit.appendCodes n (Φ.map (clauseCode n)))

private theorem code_fanInGate (op : ExtOp) (m : ℕ) (h : op.arity = m) :
    (fanInGate op m h).code = fanInCode op m := by
  simp only [fanInGate, Circuit.code_oneGate, fanInCode, Prod.mk.injEq, and_true,
    List.cons.injEq, true_and]
  subst h
  apply List.ext_getElem <;> simp

private theorem code_literalCircuit (n : ℕ) (p : Fin n × Bool) :
    (literalCircuit n p).code = literalCode n (p.1.val, p.2) := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [literalCircuit, literalCode, Circuit.code_oneGate, Circuit.code_wiring]

private theorem map_clauseLits (n : ℕ) (c : Clause ℕ) :
    (clauseLits n c).map (fun p => ((p.1 : ℕ), p.2)) = inRange n c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    unfold clauseLits inRange at ih ⊢
    by_cases h : l.1 < n
    · simp only [List.filterMap_cons, List.filter_cons, h, ↓reduceDIte, decide_true, ↓reduceIte,
        List.map_cons, ih]
    · simp only [List.filterMap_cons, List.filter_cons, h, ↓reduceDIte, decide_false,
        Bool.false_eq_true, ↓reduceIte, ih]

private theorem ofFn_getElem_map {α β : Type*} (l : List α) (f : α → β) :
    List.ofFn (fun j : Fin l.length => f l[j]) = l.map f := by
  apply List.ext_getElem <;> simp

private theorem code_clauseCircuit (n : ℕ) (c : Clause ℕ) :
    (clauseCircuit n (clauseLits n c)).code = clauseCode n c := by
  have hmap := map_clauseLits n c
  have hlen : (clauseLits n c).length = (inRange n c).length := by
    rw [← hmap, List.length_map]
  have hofFn : List.ofFn (fun j : Fin (clauseLits n c).length =>
      (literalCircuit n (clauseLits n c)[j]).code) = (inRange n c).map (literalCode n) := by
    rw [ofFn_getElem_map (clauseLits n c) fun p => (literalCircuit n p).code, ← hmap,
      List.map_map]
    exact List.map_congr_left fun p _ => code_literalCircuit n p
  rw [clauseCircuit, Circuit.code_comp, Circuit.code_pi, code_fanInGate, hofFn, clauseCode, hlen]

/-- The raw code `cnfCheckCode n Φ` is the code of the circuit `cnfCheck n Φ`. -/
theorem code_cnfCheck (n : ℕ) (Φ : CNF ℕ) : (cnfCheck n Φ).code = cnfCheckCode n Φ := by
  have hofFn : List.ofFn (fun j : Fin Φ.length =>
      (clauseCircuit n (clauseLits n Φ[j])).code) = Φ.map (clauseCode n) := by
    rw [ofFn_getElem_map Φ fun c => (clauseCircuit n (clauseLits n c)).code]
    exact List.map_congr_left fun c _ => code_clauseCircuit n c
  rw [cnfCheck, Circuit.code_comp, Circuit.code_pi, code_fanInGate, hofFn, cnfCheckCode]

/-! ### Polynomial time -/

/-- Writing the conjunction of `m` arguments in `ExtOp` is polynomial-time from `m` in unary. -/
private theorem computableInPolyTime_extAnd :
    ComputableInPolyTime (fun m : ℕ => (ExtOp.ac (.and m) : ExtOp)) encUnary encExtOp :=
  have h : ComputableInPolyTime (fun m : ℕ => 3 * m + 1) encUnary encUnary := by fun_prop
  ComputableInPolyTime.of_enc_eq h fun _ => rfl

section PolyTime

variable {α : Type} {enc : α ↪ List Bool}

private theorem computableInPolyTime_range_binary {m : α → ℕ}
    (hm : ComputableInPolyTime m enc encUnary) :
    ComputableInPolyTime (fun a => List.range (m a)) enc (encList encNat) := by
  have h := ComputableInPolyTime.mapWithInput (f := fun _ (i : ℕ) => i)
    (ComputableInPolyTime.range.comp hm)
    (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary))
  simpa only [List.map_id', Function.comp_def] using h

private theorem computableInPolyTime_fanInCode {op : α → ExtOp} {m : α → ℕ}
    (hop : ComputableInPolyTime op enc encExtOp) (hm : ComputableInPolyTime m enc encUnary) :
    ComputableInPolyTime (fun a => fanInCode (op a) (m a)) enc (Circuit.encCode encExtOp) := by
  unfold fanInCode
  exact ((hop.prod (computableInPolyTime_range_binary hm)).cons'
    (ComputableInPolyTime.const [])).prod
    ((ComputableInPolyTime.unary_to_binary.comp hm).cons' (ComputableInPolyTime.const []))

private theorem computableInPolyTime_literalCode :
    ComputableInPolyTime (fun p : ℕ × (ℕ × Bool) => literalCode p.1 p.2)
      (encPair encNat (encPair encNat encBool)) (Circuit.encCode encExtOp) := by
  unfold literalCode
  fun_prop

private theorem computableInPolyTime_clauseCode :
    ComputableInPolyTime (fun p : ℕ × Clause ℕ => clauseCode p.1 p.2)
      (encPair encNat (encList (encPair encNat encBool))) (Circuit.encCode encExtOp) := by
  have hn : ComputableInPolyTime (fun p : ℕ × Clause ℕ => p.1)
      (encPair encNat (encList (encPair encNat encBool))) encNat := by fun_prop
  have hc : ComputableInPolyTime (fun p : ℕ × Clause ℕ => p.2)
      (encPair encNat (encList (encPair encNat encBool))) (encList (encPair encNat encBool)) := by
    fun_prop
  have hL : ComputableInPolyTime (fun p : ℕ × Clause ℕ => inRange p.1 p.2)
      (encPair encNat (encList (encPair encNat encBool))) (encList (encPair encNat encBool)) := by
    unfold inRange
    exact ComputableInPolyTime.filterWithInput hc (by fun_prop)
  have hlen := (ComputableInPolyTime.length_list (encPair encNat encBool)).comp hL
  have hlits : ComputableInPolyTime
      (fun p : ℕ × Clause ℕ => (inRange p.1 p.2).map (literalCode p.1))
      (encPair encNat (encList (encPair encNat encBool))) (encList (Circuit.encCode encExtOp)) :=
    ComputableInPolyTime.mapWithInput hL
      (computableInPolyTime_literalCode.comp ((hn.comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _)))
  unfold clauseCode
  exact Circuit.computableInPolyTime_compCode hn
    (computableInPolyTime_fanInCode (computableInPolyTime_extAnd.comp hlen) hlen)
    (Circuit.computableInPolyTime_appendCodes hn hlits)

end PolyTime

/-- The raw code `cnfCheckCode n Φ` is computed in polynomial time from `n` in binary and the
encoded formula `Φ`. -/
theorem computableInPolyTime_cnfCheckCode {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    {Φ : α → CNF ℕ} (hn : ComputableInPolyTime n enc encNat)
    (hΦ : ComputableInPolyTime Φ enc encCNF) :
    ComputableInPolyTime (fun a => cnfCheckCode (n a) (Φ a)) enc (Circuit.encCode encExtOp) := by
  have hΦ' : ComputableInPolyTime Φ enc (encList (encList (encPair encNat encBool))) := hΦ
  have hpair : ComputableInPolyTime (fun p : α × Clause ℕ => (n p.1, p.2))
      (encPair enc (encList (encPair encNat encBool)))
      (encPair encNat (encList (encPair encNat encBool))) :=
    (hn.comp (ComputableInPolyTime.fst enc (encList (encPair encNat encBool)))).prod
      (ComputableInPolyTime.snd enc (encList (encPair encNat encBool)))
  have hf : ComputableInPolyTime (fun p : α × Clause ℕ => clauseCode (n p.1) p.2)
      (encPair enc (encList (encPair encNat encBool))) (Circuit.encCode encExtOp) :=
    by simpa only [Function.comp_def] using computableInPolyTime_clauseCode.comp hpair
  have hclauses : ComputableInPolyTime (fun a => (Φ a).map (clauseCode (n a))) enc
      (encList (Circuit.encCode encExtOp)) :=
    ComputableInPolyTime.mapWithInput (f := fun a c => clauseCode (n a) c) hΦ' hf
  have hlen := (ComputableInPolyTime.length_list (encList (encPair encNat encBool))).comp hΦ'
  unfold cnfCheckCode
  exact Circuit.computableInPolyTime_compCode hn
    (computableInPolyTime_fanInCode (computableInPolyTime_extOr.comp hlen) hlen)
    (Circuit.computableInPolyTime_appendCodes hn hclauses)

end Cslib.Circuits.Boolean.Unbounded
