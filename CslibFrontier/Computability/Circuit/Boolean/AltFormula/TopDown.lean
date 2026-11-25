/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AltFormula
public import CslibFrontier.Computability.Circuit.Boolean.TopDown
import CslibFrontier.Tactic.LinarithCast

/-!
# Top-down lower bounds for alternating formulas

An alternating formula gives a Karchmer–Wigderson protocol with one message per gate layer
(`AltFormula.kwProtocol`): at a conjunction the player whose input makes it false names an argument
false there, at a disjunction the player whose input makes it true names an argument true there,
and at the bottom the named literal separates the inputs. Negations are free, so a formula of
depth `d` with `S` gates gives a protocol with `d` messages from an alphabet of `S + 1 + 2 n`
symbols (`AltFormula.kwProtocol_solves`). By Korten's bound for parity
[Korten, Theorem 3][Korten2026] and its extension to majority, alternating formulas of depth `d`
for parity or majority have `S + 2 n + 1 > 2 ^ (ε n ^ (1 / (d - 1)))` for large `n`
(`AltFormula.two_rpow_lt_size_of_eval_eq_parity`,
`AltFormula.two_rpow_lt_size_of_eval_eq_majority`), so the theorem of Lecomte and Ramakrishnan
(`AltFormula.exists_majority`) is optimal for majority up to the constant in the exponent.

## Main definitions

* `Cslib.Circuits.Boolean.AltFormula.speaker`, `Cslib.Circuits.Boolean.AltFormula.witness`,
  `Cslib.Circuits.Boolean.AltFormula.childIndex`,
  `Cslib.Circuits.Boolean.AltFormula.childLiteral`: the speaker, witness bit, and selected child
  or literal at a gate layer.
* `Cslib.Circuits.Boolean.AltFormula.kwProtocol`: the Karchmer–Wigderson protocol of an alternating
  formula.

## Main results

* `Cslib.Circuits.Boolean.AltFormula.kwProtocol_solves`: it solves the game of the formula.
* `Cslib.Circuits.Boolean.AltFormula.two_rpow_lt_size_of_eval_eq_parity`,
  `Cslib.Circuits.Boolean.AltFormula.two_rpow_lt_size_of_eval_eq_majority`: Korten's bounds for
  alternating formulas.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
* [V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AltFormula

open Cslib.Communication Logic.PL

variable {n : ℕ}

/-- The player who speaks at a gate with root `op` when Alice's input makes it `s`: the holder of
the false input at a conjunction and of the true input at a disjunction (`true` is Bob). -/
def speaker : AltOp → Bool → Bool
  | .and, s => s
  | .or, s => !s

/-- The value a speaker's argument has at a gate with root `op`: false at a conjunction, true at a
disjunction. -/
def witness : AltOp → Bool
  | .and => false
  | .or => true

/-- The position of the first child of `fs` whose value with root `op` is `b` on `x`, or `0`. -/
def childIndex {d : ℕ} (op : AltOp) (fs : List (AltFormula n d)) (b : Bool) (x : BitString n) :
    ℕ :=
  match Fin.find? fun j : Fin fs.length => eval op (fs.get j) x == b with
  | some j => j.val
  | none => 0

/-- The first literal of the clause or term `ls` whose value is `b` on `x`, or `(i₀, true)`. -/
def childLiteral (i₀ : Fin n) (ls : List (Literal (Fin n))) (b : Bool) (x : BitString n) :
    Literal (Fin n) :=
  (ls.find? fun l => Literal.eval x l == b).getD (i₀, true)

/-- The Karchmer–Wigderson protocol of an alternating formula with root `op`, when Alice's input
makes it `s`, with messages a child position below `S + 1` or a literal. -/
def kwProtocol (S : ℕ) (i₀ : Fin n) :
    {d : ℕ} → AltOp → AltFormula n d → Bool →
      KWRoundProtocol (Fin n) (Fin (S + 1) ⊕ Literal (Fin n)) d
  | 0, _, l, _ => .output l.1
  | 1, op, ls, s =>
    .speak (speaker op s) (fun x => .inr (childLiteral i₀ ls (witness op) x)) fun
      | .inr l => .output l.1
      | .inl _ => .output i₀
  | d + 2, op, fs, s =>
    .speak (speaker op s) (fun x => .inl ⟨min (childIndex op.dual fs (witness op) x) S, by omega⟩)
      fun
      | .inl j => if h : j.val < fs.length then kwProtocol S i₀ op.dual (fs.get ⟨j, h⟩) s
        else .output i₀
      | .inr _ => .output i₀

/-- When some child of `fs` evaluates to `b` on `x`, `childIndex op fs b x` is the index of a
child evaluating to `b`. -/
theorem childIndex_spec {d : ℕ} {op : AltOp} {fs : List (AltFormula n d)} {b : Bool}
    {x : BitString n} (h : ∃ j : Fin fs.length, eval op (fs.get j) x = b) :
    ∃ j : Fin fs.length, childIndex op fs b x = j ∧ eval op (fs.get j) x = b := by
  unfold childIndex
  cases hf : Fin.find? fun j : Fin fs.length => eval op (fs.get j) x == b with
  | none => exact let ⟨j, hj⟩ := h; absurd hj (by simpa using Fin.find?_eq_none_iff.1 hf j)
  | some j => exact ⟨j, rfl, by simpa using Fin.eq_true_of_find?_eq_some hf⟩

/-- When some literal of `ls` evaluates to `b` on `x`, `childLiteral i₀ ls b x` is a literal in
`ls` evaluating to `b`. -/
theorem childLiteral_spec {i₀ : Fin n} {ls : List (Literal (Fin n))} {b : Bool}
    {x : BitString n} (h : ∃ l ∈ ls, Literal.eval x l = b) :
    childLiteral i₀ ls b x ∈ ls ∧ Literal.eval x (childLiteral i₀ ls b x) = b := by
  unfold childLiteral
  cases hf : ls.find? fun l => Literal.eval x l == b with
  | none => exact let ⟨l, hl, hlb⟩ := h; absurd hlb (by simpa using List.find?_eq_none.1 hf l hl)
  | some l => exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- Every alternating formula of positive depth `d + 1` has at least `1` gate. -/
theorem one_le_size {d : ℕ} (f : AltFormula n (d + 1)) : 1 ≤ size f := by
  simp [size]

/-- A gate with root `op` that has the witness value has an argument with the witness value. -/
private theorem exists_child_eq_witness {d : ℕ} (op : AltOp) (fs : List (AltFormula n d))
    {z : BitString n} (hz : eval (d := d + 1) op fs z = witness op) :
    ∃ j : Fin fs.length, eval op.dual (fs.get j) z = witness op := by
  cases op <;> simp only [eval, witness, AltOp.dual, List.all_eq_false, List.any_eq_true,
    Bool.not_eq_true] at hz ⊢ <;>
    exact let ⟨g, hg, hgz⟩ := hz; let ⟨j, hj⟩ := List.get_of_mem hg; ⟨j, hj ▸ hgz⟩

/-- A gate with root `op` without the witness value has no argument with it. -/
private theorem eval_child_eq_not_witness {d : ℕ} (op : AltOp) (fs : List (AltFormula n d))
    {z : BitString n} (hz : eval (d := d + 1) op fs z = !witness op) :
    ∀ g ∈ fs, eval op.dual g z = !witness op := by
  cases op <;> simpa [eval, witness, AltOp.dual] using hz

/-- The speaker's input has the witness value, the other input its negation. -/
private theorem eval_speaker_iff {α : Type*} {op : AltOp} {s : Bool} {x y : α} (e : α → Bool) :
    (e (if speaker op s then y else x) = witness op ∧
      e (if speaker op s then x else y) = !witness op) ↔ e x = s ∧ e y = !s := by
  cases op <;> cases s <;> simp [speaker, witness, and_comm]

/-- **The protocol of an alternating formula solves its game**: if `f` has at most `S` gates,
Alice's input makes it `s` and Bob's makes it `!s`, the inputs differ at the named coordinate. -/
theorem kwProtocol_solves (S : ℕ) (i₀ : Fin n) : ∀ {d : ℕ} (op : AltOp) (f : AltFormula n d),
    size f ≤ S → ∀ (s : Bool) (x y : BitString n), eval op f x = s → eval op f y = !s →
      x ((kwProtocol S i₀ op f s).run x y) ≠ y ((kwProtocol S i₀ op f s).run x y)
  | 0, op, l, _, s, x, y, hx, hy => by
    simp only [kwProtocol, RoundProtocol.run]
    intro h
    simp only [eval, Literal.eval] at hx hy
    rw [← h, hx] at hy
    cases s <;> cases hy
  | 1, op, ls, _, s, x, y, hx, hy => by
    obtain ⟨hu, hv⟩ := (eval_speaker_iff (eval op ls)).2 ⟨hx, hy⟩
    obtain ⟨hl, hlu⟩ := childLiteral_spec (i₀ := i₀)
      (let ⟨j, hj⟩ := exists_child_eq_witness op ls hu; ⟨ls.get j, List.get_mem ls j, hj⟩)
    have hlv := eval_child_eq_not_witness op ls hv _ hl
    simp only [kwProtocol, RoundProtocol.run_speak, RoundProtocol.run]
    intro h
    have huv : (if speaker op s then y else x) (childLiteral i₀ ls (witness op)
        (if speaker op s then y else x)).1 =
      (if speaker op s then x else y) (childLiteral i₀ ls (witness op)
        (if speaker op s then y else x)).1 := by
      split_ifs with hb <;> simp only [hb, ↓reduceIte] at h <;> [exact h.symm; exact h]
    simp only [eval, Literal.eval] at hlu hlv
    rw [← huv, hlu] at hlv
    cases hop : witness op <;> simp [hop] at hlv
  | d + 2, op, fs, hS, s, x, y, hx, hy => by
    obtain ⟨hu, hv⟩ := (eval_speaker_iff (eval op fs)).2 ⟨hx, hy⟩
    obtain ⟨j, hj, hju⟩ := childIndex_spec (exists_child_eq_witness op fs hu)
    obtain ⟨hjx, hjy⟩ := (eval_speaker_iff (eval op.dual (fs.get j))).1
      ⟨hju, eval_child_eq_not_witness op fs hv _ (List.get_mem fs j)⟩
    have hsum : (fs.map size).sum < S := Nat.lt_of_succ_le (by change 1 + _ ≤ S at hS; omega)
    have hlen : fs.length ≤ (fs.map size).sum := by
      simpa only [List.length_map] using List.length_le_sum_of_one_le (fs.map size)
        fun _ ha => let ⟨g, _, hg⟩ := List.mem_map.1 ha; hg ▸ one_le_size g
    have hchild : size (fs.get j) ≤ S :=
      (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem fs j))).trans hsum.le
    simp only [kwProtocol, RoundProtocol.run_speak, hj,
      min_eq_left (j.isLt.le.trans (hlen.trans hsum.le)), j.isLt, ↓reduceDIte]
    exact kwProtocol_solves S i₀ op.dual (fs.get j) hchild s x y hjx hjy

/-- An alternating formula computing `g` gives a protocol for it. -/
private theorem solvesKW_kwProtocol {d : ℕ} {op : AltOp} {f : AltFormula n d}
    {g : BitString n → Bool} (hf : ∀ x, eval op f x = g x) (i₀ : Fin n) :
    (kwProtocol (size f) i₀ op f false).SolvesKW g := fun x y hx hy =>
  kwProtocol_solves (size f) i₀ op f le_rfl false x y ((hf x).trans hx) ((hf y).trans hy)

/-- **Korten's theorem for alternating formulas**: for every depth `d ≥ 2` there is `ε > 0` such
that alternating formulas of depth `d` computing the parity of `n` bits, for large `n`, have
`S + 2 n + 1 > 2 ^ (ε n ^ (1 / (d - 1)))` gates `S`. -/
theorem two_rpow_lt_size_of_eval_eq_parity {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (op : AltOp) (f : AltFormula n d),
      (∀ x, eval op f x = parity n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) < size f + 2 * n + 1 := by
  obtain ⟨ε, hε, N, hN⟩ := not_solvesKW_parity.{0} d hd
  refine ⟨ε, hε, max N 1, fun n hn op f hf => ?_⟩
  have h := lt_of_not_ge fun hle => hN n (le_of_max_le_left hn) hle _
    (solvesKW_kwProtocol hf ⟨0, le_of_max_le_right hn⟩)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at h
  cast_linarith

/-- **Korten's bound for alternating formulas, for majority**, extending [Korten2026]: the bound of
`two_rpow_lt_size_of_eval_eq_parity` holds for majority, so the theorem of Lecomte and
Ramakrishnan (`exists_majority`) is optimal up to the constant in the exponent. -/
theorem two_rpow_lt_size_of_eval_eq_majority {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (op : AltOp) (f : AltFormula n d),
      (∀ x, eval op f x = majority n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) < size f + 2 * n + 1 := by
  obtain ⟨ε, hε, N, hN⟩ := not_solvesKW_strictMajority.{0} d hd
  refine ⟨ε, hε, max N 1, fun n hn op f hf => ?_⟩
  have hP := solvesKW_kwProtocol hf ⟨0, le_of_max_le_right hn⟩
  -- a protocol for majority gives one for strict majority
  have hneg (z : BitString n) : (!majority n zᶜ) = strictMajority n z := by
    simpa using (strictMajority_not zᶜ).symm
  have hQ : ((kwProtocol (size f) ⟨0, le_of_max_le_right hn⟩ op f false).swapPlayers.comap
      compl compl).SolvesKW (strictMajority n) := fun x y hx hy =>
    hP.swapPlayers.comap_compl x y ((hneg x).trans hx) ((hneg y).trans hy)
  have h := lt_of_not_ge fun hle => hN n (le_of_max_le_left hn) hle _ hQ
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at h
  cast_linarith

end Cslib.Circuits.Boolean.AltFormula
