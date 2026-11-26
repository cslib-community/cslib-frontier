/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Bases
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.DSteps
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ListPrograms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Typed
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# The program GROUP

The program GROUP of the evaluator of [AnthropicVPVNP2026] reads a script (`scriptEnc`): the
number `T` of steps of the automaton and the number `ub` of bits of a unit in binary, and a list of
instructions, which it executes one after the other on a trie, starting from the empty trie
(`scriptSem`). For a fixed automaton, a fixed code of the letters and a fixed list of roles of laws,
one formula of the tree machine is GROUP: at every script whose instructions are valid, its weighted
list of values is the semantics of the script, every trie held in the state `groupState`, and its
cost is linear in the costs of the instructions (`exists_formula_scriptSem`).

## Main definitions

* `instructionSem`, `scriptSem`: what an instruction and a script do with a trie.
* `Instruction.Valid`: the instructions for which GROUP computes the semantics.
* `groupState`: the state of GROUP, the trie with the numbers `T` and `ub`.

## Main results

* `exists_formula_scriptSem`: one formula computes the semantics of every valid script.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54); this file formalizes programs
of that evaluator, not the theorem. Ported from the source modules `Nc.Grp.GroupProg` and
`Nc.Grp.Script`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [Fintype S] [DecidableEq S] [Fintype Q] {c : ℕ}

variable (θ) in
/-- What an instruction does with a trie, for `T` steps of the automaton `mu`, the code `cb` of the
letters, the list `kinds` of roles of laws and units of `ub` bits. A comparison keeps the trie,
with the weight `1`, if the contents agree and rejects otherwise; a block with state numbers that
are not below the number of states, and a role with a number that is not below the length of
`kinds`, reject. -/
@[expose] noncomputable def instructionSem (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Cut.Law A, L.Role)) (T ub : ℕ) :
    Instruction → Tree → List (A × Tree)
  | .block q q' B, t => if h : q < Fintype.card Q ∧ q' < Fintype.card Q then
      (simSem θ mu cb T ⟨q, h.1⟩ ⟨q', h.2⟩).weightedBind fun o => packSem A (separator cb) ub B o t
    else []
  | .input part B, t => packSem A (separator cb) ub B (inputOutputs (S := S) part) t
  | .agree k k', t => if tget k t = tget k' t then [(1, t)] else []
  | .fixed k w, t => if tget k t = ofBits w then [(1, t)] else []
  | .role j tt slots keys, t => match kinds[j]? with
    | some z => roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t
    | none => []

variable (θ) in
/-- What a script does with a trie: its instructions one after the other. -/
noncomputable def scriptSem (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Cut.Law A, L.Role)) (T ub : ℕ)
    (l : List Instruction) (t : Tree) : List (A × Tree) :=
  l.weightedFoldl (instructionSem θ mu cb kinds T ub) t

section Equations

variable (mu : Tape.Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)
  (kinds : List (Σ L : Cut.Law A, L.Role)) (T ub : ℕ)

@[simp] theorem scriptSem_nil (t : Tree) : scriptSem θ mu cb kinds T ub [] t = [(1, t)] := by
  simp only [scriptSem, List.weightedFoldl_nil]

@[simp] theorem scriptSem_cons (i : Instruction) (l : List Instruction) (t : Tree) :
    scriptSem θ mu cb kinds T ub (i :: l) t =
      (instructionSem θ mu cb kinds T ub i t).weightedBind (scriptSem θ mu cb kinds T ub l) := by
  rw [scriptSem, List.weightedFoldl_cons]
  rfl

end Equations

/-- The conditions on an instruction under which GROUP computes its semantics: the state numbers
of a block are below the number of states, the codes of the letters of an input part have at most
`c` bits, and the number of a role is that of a role in `kinds` with as many slots as are given. -/
@[expose] def Instruction.Valid (Q : Type) [Fintype Q] (c : ℕ)
    (kinds : List (Σ L : Cut.Law A, L.Role)) : Instruction → Prop
  | .block q q' _ => q < Fintype.card Q ∧ q' < Fintype.card Q
  | .input part _ => ∀ a ∈ part, a.length ≤ c
  | .agree _ _ => True
  | .fixed _ _ => True
  | .role j _ slots _ => ∃ z, kinds[j]? = some z ∧ slots.length = (slotList z.1 z.2).length

/-- The state of GROUP: the numbers `T` and `ub` and the trie. -/
@[expose] def groupState (T ub : ℕ) (t : Tree) : Tree := .cons (num T) (.cons (num ub) t)

/-! ### The program -/

private theorem StoreBound.of_mem_instructionSem {mu : Tape.Letter S Unit Γ → Matrix Q Q A}
    {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : Cut.Law A, L.Role)} {T ub : ℕ}
    {i : Instruction} {t : Tree} {q : A × Tree} (h : StoreBound ub t)
    (hq : q ∈ instructionSem θ mu cb kinds T ub i t) : StoreBound ub q.2 := by
  cases i with
  | block q₁ q₂ B =>
    simp only [instructionSem] at hq
    split_ifs at hq
    · obtain ⟨a, -, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 hq
      exact h.of_mem_packSem (q := r) hr
    · exact absurd hq List.not_mem_nil
  | input part B => exact h.of_mem_packSem hq
  | agree _ _ | fixed _ _ =>
    simp only [instructionSem] at hq
    split_ifs at hq
    exacts [List.mem_singleton.1 hq ▸ h, absurd hq List.not_mem_nil]
  | role j tt slots keys =>
    simp only [instructionSem, roleSem] at hq
    split at hq
    · split_ifs at hq
      · obtain ⟨a, -, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 hq
        obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hr
        exact h.of_mem_putStrings ht'
      · exact absurd hq List.not_mem_nil
    · exact absurd hq List.not_mem_nil

private theorem mul_add_le {a b K X : ℕ} (hX : 1 ≤ X) (h : a + b ≤ K) : a * X + b ≤ K * X :=
  calc a * X + b ≤ a * X + b * X := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hX) _
    _ = (a + b) * X := (Nat.add_mul _ _ _).symm
    _ ≤ K * X := Nat.mul_le_mul_right _ h

/-- A bounded entry of a trie, and its comparison with another tree. -/
private theorem compare_gives {pf v : Fm} {x t o : Tree} {ub cv : ℕ} {k : List Bool}
    (ht : StoreBound ub t) (hp : Gives θ pf x (ofBits k) 4)
    (htf : Gives θ (.tl (.tl (.tl .id))) x t 4)
    (hv : Gives θ v x o cv) :
    Gives θ (eqF (getF pf (.tl (.tl (.tl .id)))) v) x (bit (decide (tget k t = o)))
      (cv + 30 * k.length + 240 * ub + 100) := by
  have e := eqF_gives (getF_gives hp htf) hv
  simp only [path_ofBits, len_ofBits] at e
  refine e.mono ?_
  have := (ht.tget k).2
  have := le_of_eq_of_le (congrArg Tree.size (ht.tget k).1) (size_ofBits _)
  omega

/-- A check: the trie is kept if the comparison `C` holds, and the run fails otherwise. -/
private theorem ite_check_does {P : Prop} [Decidable P] {C G : Fm} {x t : Tree} {c d : ℕ}
    (e : Gives θ C x (bit (decide P)) c) (hG : Gives θ G x t d) :
    Does θ (.ite C G .fail) x (if P then [((1 : A), t)] else []) (c + d + 1) := by
  split_ifs with h
  · exact (Does.ite_true e (by simp [h, bit, one]) hG).mono (by omega)
  · simp only [h, decide_false, bit] at e
    exact (Does.ite_false e (Does.fail x)).mono (by omega)

/-- **One instruction.** -/
private theorem exists_formula_instruction (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Cut.Law A, L.Role)) :
    ∃ F κ, ∀ (T ub : ℕ) (i : Instruction) (t : Tree), i.Valid Q c kinds → StoreBound ub t →
      Does θ F (.cons i.enc (groupState T ub t))
        ((instructionSem θ mu cb kinds T ub i t).map (Prod.map id (groupState T ub)))
        (κ * i.cost T ub) := by
  obtain ⟨FB, κb, hFB⟩ := exists_formula_block (A := A) (θ := θ) mu cb
  obtain ⟨FI, κi, hFI⟩ := exists_formula_input (A := A) (θ := θ) (S := S) (Γ := Γ) cb
  choose FR κr hFR using fun z : (Σ L : Cut.Law A, L.Role) =>
    exists_formula_roleSem (θ := θ) z.1 z.2
  obtain ⟨K, hK⟩ : ∃ K, K = κb + κi + (kinds.map κr).sum +
    (kinds.length + 5) * (kinds.length + 10) + 400 := ⟨_, rfl⟩
  let fs : List Fm :=
    lett (.cons (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) (.cons (.hd (.tl (.tl .id)))
      (.cons (.tl (.tl (.tl .id))) (.tl (.tl (.hd .id)))))) FB ::
    lett (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id)))
      (.tl (.tl (.hd .id)))))) FI ::
    .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (getF (.tl (.tl (.hd .id)))
      (.tl (.tl (.tl .id))))) (.tl (.tl (.tl .id))) .fail ::
    .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (.tl (.tl (.hd .id))))
      (.tl (.tl (.tl .id))) .fail ::
    kinds.map fun z =>
      lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) (FR z)
  refine ⟨.cons (.hd (.tl .id)) (.cons (.hd (.tl (.tl .id))) (switchF (.hd (.hd .id)) fs)),
    K + 10, fun T ub i t hi ht => ?_⟩
  have hc1 : 1 ≤ i.cost T ub := by
    cases i <;> simp only [Instruction.cost, Body.cost] <;> omega
  have h400 : 400 ≤ K := by omega
  set x := Tree.cons i.enc (groupState T ub t)
  have hx : Gives θ .id x x 1 := Gives.id x
  suffices h : Does θ (switchF (.hd (.hd .id)) fs) x (instructionSem θ mu cb kinds T ub i t)
      (K * i.cost T ub) by
    refine ((Does.cons hx.tl.hd (Does.cons hx.tl.tl.hd h)).of_eq ?_).mono ?_
    · simp [groupState, Function.comp_def, x]
    · rw [Nat.add_mul]; omega
  cases i with
  | block q q' B =>
    obtain ⟨hq, hq'⟩ := hi
    have hB : 1 ≤ B.cost ub := by simp only [Body.cost]; omega
    refine ((switchF_does (j := 0) hx.hd.hd rfl (Does.of_gives ((hx.tl.hd.cons hx.hd.tl.hd).cons
      (hx.tl.tl.hd.cons (hx.tl.tl.tl.cons hx.hd.tl.tl))) (hFB T ub q q' hq hq' B t))).of_eq
      (by simp [instructionSem, hq, hq'])).mono ?_
    simp only [Instruction.cost]
    exact le_trans (by omega) (mul_add_le (a := κb) (b := 40) (by omega) (by omega))
  | input part B =>
    have hB : 1 ≤ B.cost ub := by simp only [Body.cost]; omega
    refine (switchF_does (j := 1) hx.hd.hd rfl (Does.of_gives (hx.hd.tl.hd.cons
      (hx.tl.tl.hd.cons (hx.tl.tl.tl.cons hx.hd.tl.tl))) (hFI ub part B t hi))).mono ?_
    simp only [Instruction.cost]
    exact le_trans (by omega) (mul_add_le (a := κi) (b := 40) (by omega) (by omega))
  | agree k k' =>
    have g := getF_gives (θ := θ) (p := ofBits k') (t := t) hx.hd.tl.tl hx.tl.tl.tl
    rw [path_ofBits, len_ofBits] at g
    refine (switchF_does (j := 2) hx.hd.hd rfl
      (ite_check_does (compare_gives ht hx.hd.tl.hd hx.tl.tl.tl g) hx.tl.tl.tl)).mono ?_
    simp only [Instruction.cost]
    exact le_trans (by omega) (Nat.mul_le_mul_right _ h400)
  | fixed k w =>
    refine (switchF_does (j := 3) hx.hd.hd rfl
      (ite_check_does (compare_gives ht hx.hd.tl.hd hx.tl.tl.tl hx.hd.tl.tl)
        hx.tl.tl.tl)).mono ?_
    simp only [Instruction.cost]
    exact le_trans (by omega) (Nat.mul_le_mul_right _ h400)
  | role j tt slots keys =>
    obtain ⟨z, hz, hsl⟩ := hi
    have hj : j < kinds.length := (List.getElem?_eq_some_iff.1 hz).1
    have hf : fs[4 + j]? = some (lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id)))
        (.tl (.hd .id)))) (FR z)) := by
      simp [fs, Nat.add_comm 4 j, hz]
    refine ((switchF_does hx.hd.hd hf (Does.of_gives (hx.tl.tl.hd.cons (hx.tl.tl.tl.cons
      hx.hd.tl)) (hFR z ub tt slots keys t ht hsl))).of_eq (by simp [instructionSem, hz])).mono ?_
    simp only [Instruction.cost]
    have h1 : (4 + j + 1) * (1 + 1 + 1 + (4 + j) + 1) ≤
        (kinds.length + 5) * (kinds.length + 10) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 := List.le_sum_of_mem (List.mem_map_of_mem (f := κr) (List.mem_of_getElem? hz))
    exact le_trans (by omega) (mul_add_le (a := κr z)
      (b := (kinds.length + 5) * (kinds.length + 10) + 20) (by omega) (by omega))

/-- The unary number of a binary one, most significant bit first. -/
private def unF (b : Fm) : Fm := foldF (.ite (.hd .id) (.cons (.quote .nil)
  (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id))) (.quote .nil) b

private theorem unF_gives {b : Fm} {x : Tree} {w : List Bool} {c : ℕ}
    (h : Gives θ b x (ofBits w) c) : Gives θ (unF b) x (num (BitString.binaryValue w))
      (c + w.length * (62 * BitString.binaryValue w + 120) + 30) := by
  have le_foldl (ys : List Bool) : ∀ a, a ≤ ys.foldl (fun a b => 2 * a + b.toNat) a := by
    induction ys with
    | nil => exact fun _ => le_rfl
    | cons b ys ih =>
      exact fun a => (Nat.le_mul_of_pos_left a (by decide)).trans
        ((Nat.le_add_right _ _).trans (ih _))
  have h1 := foldF_gives_enc (θ := θ) (encE := bit) (xs := w) (enc := num) (s₀ := 0)
    (g := fun b a => 2 * a + b.toNat) (d := fun _ => 62 * BitString.binaryValue w + 90)
    (step := .ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id)))
      (appF (.tl .id) (.tl .id)))
    (Inv := fun ys a => ys.foldl (fun a b => 2 * a + b.toNat) a = BitString.binaryValue w)
    (Gives.quote _ _) (listT_ofBits w ▸ h) (fun b ys a _ hinv => by
      have ha : a ≤ BitString.binaryValue w := hinv ▸ le_foldl (b :: ys) a
      have g : Gives θ (.tl .id) (.cons (bit b) (num a)) (listT (List.replicate a .nil)) 2 :=
        num_eq_listT_replicate a ▸ (Gives.id _).tl
      have hg := appF_gives g g
      rw [← List.replicate_add, ← num_eq_listT_replicate, List.length_replicate, ← two_mul] at hg
      refine ⟨?_, hinv⟩
      cases b
      · exact (Gives.ite_false (Gives.id _).hd hg).mono (by omega)
      · exact (Gives.ite_true (Gives.id _).hd (by simp [bit, one])
          ((Gives.quote .nil _).cons hg)).mono (by omega)) rfl
  refine h1.mono ?_
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  nlinarith

/-- **The program GROUP.** For an automaton `mu`, a code `cb` of the letters and a list `kinds` of
roles of laws, one formula computes, at every script whose instructions are valid, the semantics of
the script from the empty trie, at a cost linear in the costs of the instructions and in the
binary numbers `T` and `ub` times their lengths. -/
theorem exists_formula_scriptSem (mu : Tape.Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Cut.Law A, L.Role)) :
    ∃ F κ, ∀ (bT bub : List Bool) (l : List Instruction), (∀ i ∈ l, i.Valid Q c kinds) →
      Does θ F (scriptEnc bT bub l)
        ((scriptSem θ mu cb kinds (BitString.binaryValue bT) (BitString.binaryValue bub) l
          .nil).map
          (Prod.map id (groupState (BitString.binaryValue bT) (BitString.binaryValue bub))))
        (κ * ((bT.length + 1) * (BitString.binaryValue bT + 1) +
          (bub.length + 1) * (BitString.binaryValue bub + 1) +
          (l.map (Instruction.cost (BitString.binaryValue bT) (BitString.binaryValue bub))).sum +
          l.length)) := by
  obtain ⟨F, κ, hF⟩ := exists_formula_instruction (θ := θ) mu cb kinds
  refine ⟨foldF F (.cons (unF (.hd (.hd .id))) (.cons (unF (.tl (.hd .id))) (.quote .nil)))
    (.tl .id), κ + 300, fun bT bub l hl => ?_⟩
  set T := BitString.binaryValue bT with hT
  set ub := BitString.binaryValue bub with hub
  have h1 := foldF_does_enc (θ := θ) (encE := Instruction.enc) (xs := l) (enc := groupState T ub)
    (s₀ := .nil) (f := instructionSem θ mu cb kinds T ub) (Inv := fun _ t => StoreBound ub t)
    (d := fun i => κ * i.cost T ub) ((unF_gives (Gives.id (scriptEnc bT bub l)).hd.hd).cons
      ((unF_gives (Gives.id _).hd.tl).cons (Gives.quote .nil _))) (Gives.id _).tl
    (fun i _ t hi ht => ⟨hF T ub i t (hl i hi) ht, fun _ hq => ht.of_mem_instructionSem hq⟩)
    (StoreBound.nil ub)
  refine h1.mono ?_
  rw [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate, smul_eq_mul,
    Nat.add_mul, ← hT, ← hub]
  have p1 : bT.length * (62 * T + 120) ≤ 120 * ((bT.length + 1) * (T + 1)) := by nlinarith
  have p2 : bub.length * (62 * ub + 120) ≤ 120 * ((bub.length + 1) * (ub + 1)) := by nlinarith
  have p3 : 1 ≤ (bT.length + 1) * (T + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have q := Nat.mul_le_mul_left κ ((Nat.le_add_left (l.map (Instruction.cost T ub)).sum
    ((bT.length + 1) * (T + 1) + (bub.length + 1) * (ub + 1))).trans
      (Nat.le_add_right _ l.length))
  omega

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
