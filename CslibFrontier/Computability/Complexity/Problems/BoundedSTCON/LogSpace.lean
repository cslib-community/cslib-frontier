/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.BoundedSTCON
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Boolean
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Foundations.Data.Nat.Min

/-!
# Writing the bounded-connectivity layered graph

The binary bound is read with saturating arithmetic: both the partial value and the place value
are capped at the number of vertices. No register ever stores the unrestricted bound.
The writer reads the existing framed `encSTCON` header and copies graph entries by address,
then emits the unary STCON header and the layered matrix row by row. Its eight registers
remain below the square of one plus the input length.

## Main results

* `Cslib.Complexity.BoundedSTCONInstance.computableInLogSpace_layered`: the capped layered
  instance is computed in logarithmic visited-work-cell space.
-/

public section
namespace Cslib.Complexity.BoundedSTCONInstance
open Turing CounterProgram Instr Expr MultiTapeTM

private def minExpr (a b : Expr) : Expr := sub a (sub a b)

private theorem eval_minExpr (a b : Expr) (regs : List ℕ) :
    (minExpr a b).eval regs = min (a.eval regs) (b.eval regs) := by
  simp only [minExpr, eval_sub]
  omega

private def graphLength : Expr :=
  add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3)) (mul (reg 0) (reg 0))

private def framed (e : Expr) : Expr := add (mul (const 2) e) (const 1)

private def vertices : Expr := mul (add (reg 3) (const 1)) (reg 0)

private def header : List Instr :=
  [read (framed (reg 0)) 1 2 2,
   assign 0 (add (reg 0) (const 1)) 0,
   read (framed (add (add (reg 0) (const 1)) (reg 1))) 3 4 4,
   assign 1 (add (reg 1) (const 1)) 2,
   read (framed (add (add (add (add (reg 0) (const 1)) (reg 1)) (const 1))
     (reg 2))) 5 6 6,
   assign 2 (add (reg 2) (const 1)) 4]

private def position : Expr := framed
  (add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3))
    (add (mul (mod (reg 6) (reg 0)) (reg 0)) (mod (reg 7) (reg 0))))

/-- A streaming layered-matrix writer. Registers hold the graph header, the capped bound,
the capped binary place value, the input position, and the output row and column. -/
private def writer : CounterProgram where
  code := List.flatten [header,
    [assign 4 (const 1) 7,
     assign 5 (framed graphLength) 8,
     read (reg 5) 9 10 12,
     assign 3 (minExpr (reg 0) (add (reg 3) (reg 4))) 10,
     assign 4 (minExpr (reg 0) (mul (const 2) (reg 4))) 11,
     assign 5 (add (reg 5) (const 1)) 8],
    forCode 12 6 vertices 15 16, [emit true 14, emit false 17],
    forCode 17 6 (reg 1) 20 21, [emit true 19, emit false 22],
    forCode 22 6 (add (mul (reg 3) (reg 0)) (reg 2)) 25 26,
    [emit true 24, emit false 27],
    forCode 27 6 vertices 30 38,
    forCode 30 7 vertices 33 29,
    [lt (const 0) (eqB (div (reg 7) (reg 0)) (add (div (reg 6) (reg 0)) (const 1))) 34 36,
     lt (const 0) (eqB (mod (reg 6) (reg 0)) (mod (reg 7) (reg 0))) 37 35,
     read position 37 36 36,
     emit false 32,
     emit true 32,
     halt []]]
  registers := 8

variable (I : BoundedSTCONInstance) {B : ℕ}

private theorem input_graph {i : ℕ} (hi : i < I.graph.encode.length) :
    (encBoundedSTCON I)[2 * i + 1]? = I.graph.encode[i]? := by
  change (frame I.graph.encode ++ I.bound.bits)[2 * i + 1]? = _
  rw [(getElem?_frame_append _ _ hi).2, List.getElem?_eq_getElem hi]

private theorem input_bound (j : ℕ) :
    (encBoundedSTCON I)[2 * I.graph.encode.length + 1 + j]? = I.bound.bits[j]? :=
  getElem?_frame_append_boundary _ _ _

private theorem bounded {n s t a p j u v : ℕ}
    (hn : n ≤ B) (hs : s ≤ B) (ht : t ≤ B) (ha : a ≤ B)
    (hp : p ≤ B) (hj : j ≤ B) (hu : u ≤ B) (hv : v ≤ B) :
    ∀ r ∈ [n, s, t, a, p, j, u, v], r ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem read_header (hB : I.graph.n ≤ B) :
    writer.ReachesOut (encBoundedSTCON I) (writer.Active B)
      (0, [0, 0, 0, 0, 0, 0, 0, 0])
      (6, [I.graph.n, I.graph.s, I.graph.t, 0, 0, 0, 0, 0]) [] := by
  have hs := I.graph.s.isLt
  have ht := I.graph.t.isLt
  have hb {n s t : ℕ} (hn : n ≤ I.graph.n) (hs : s ≤ I.graph.n) (ht : t ≤ I.graph.n) :
      ∀ r ∈ [n, s, t, 0, 0, 0, 0, 0], r ≤ B :=
    bounded (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hN (i : ℕ) (hi : i ≤ I.graph.n) :
      (encBoundedSTCON I)[2 * i + 1]? = some (decide (i < I.graph.n)) := by
    rw [I.input_graph (by rw [I.graph.length_encode]; omega), I.graph.getElem?_encode_n hi]
  have hS (i : ℕ) (hi : i ≤ I.graph.s) :
      (encBoundedSTCON I)[2 * (I.graph.n + 1 + i) + 1]? =
        some (decide (i < I.graph.s)) := by
    rw [I.input_graph (by rw [I.graph.length_encode]; omega), I.graph.getElem?_encode_s hi]
  have hT (i : ℕ) (hi : i ≤ I.graph.t) :
      (encBoundedSTCON I)[2 * (I.graph.n + 1 + I.graph.s + 1 + i) + 1]? =
        some (decide (i < I.graph.t)) := by
    rw [I.input_graph (by rw [I.graph.length_encode]; omega), I.graph.getElem?_encode_t hi]
  have hfalse {x : Option Bool} {n : ℕ} (hx : x = some (decide (n < n))) : x ≠ some true := by
    simp [hx]
  have hn := reachesOut_count (P := writer) (w := encBoundedSTCON I)
    (n := I.graph.n) (u := 0) (c := 0) (fun j => [j, 0, 0, 0, 0, 0, 0, 0])
    (by rfl) (by rfl) (fun _ _ => by simp)
    (fun j hj => hb hj (by omega) (by omega))
    (fun j hj => by exact decide_eq_true hj ▸ hN j hj.le)
    (by exact hfalse (hN _ le_rfl))
    0 (Nat.zero_le _)
  have hs' := reachesOut_count (P := writer) (w := encBoundedSTCON I)
    (n := I.graph.s) (u := 1) (c := 2) (fun j => [I.graph.n, j, 0, 0, 0, 0, 0, 0])
    (by rfl) (by rfl) (fun _ _ => by simp)
    (fun j hj => hb le_rfl (by omega) (by omega))
    (fun j hj => by exact decide_eq_true hj ▸ hS j hj.le)
    (by exact hfalse (hS _ le_rfl))
    0 (Nat.zero_le _)
  have ht' := reachesOut_count (P := writer) (w := encBoundedSTCON I)
    (n := I.graph.t) (u := 2) (c := 4)
    (fun j => [I.graph.n, I.graph.s, j, 0, 0, 0, 0, 0])
    (by rfl) (by rfl) (fun _ _ => by simp)
    (fun j hj => hb le_rfl (by omega) (by omega))
    (fun j hj => by exact decide_eq_true hj ▸ hT j hj.le)
    (by exact hfalse (hT _ le_rfl))
    0 (Nat.zero_le _)
  exact hn.trans (hs'.trans ht')


private def scan (n : ℕ) : ℕ → ℕ → List Bool → ℕ
  | a, _, [] => a
  | a, p, b :: bs => scan n (min n (a + p * b.toNat)) (min n (2 * p)) bs

private theorem min_mul_cap (n a b : ℕ) : min n (min n a * b) = min n (a * b) := by
  cases b with
  | zero => simp
  | succ b =>
    by_cases h : a ≤ n
    · rw [Nat.min_eq_right h]
    · rw [Nat.min_eq_left (by omega : n ≤ a)]
      rw [Nat.min_eq_left (by nlinarith), Nat.min_eq_left (by nlinarith)]

private theorem scan_eq (n a p : ℕ) (bs : List Bool) (ha : a ≤ n) :
    scan n a p bs = min n (a + p * bs.foldr Nat.bit 0) := by
  induction bs generalizing a p with
  | nil => simp [scan, Nat.min_eq_right ha]
  | cons b bs ih =>
    rw [scan, ih _ _ (Nat.min_le_left _ _), Nat.min_min_add]
    have hcap : min n (a + p * b.toNat + min n (2 * p) * bs.foldr Nat.bit 0) =
        min n (a + p * b.toNat + 2 * p * bs.foldr Nat.bit 0) := by
      rw [Nat.add_comm (a + p * b.toNat), ← Nat.min_min_add,
        min_mul_cap, Nat.min_min_add, Nat.add_comm]
    rw [hcap]
    congr 1
    cases b <;> simp [Nat.bit] <;> ring

/-- The registers while the bound is read stay below `B`. -/
private theorem bounded_scan (hn : I.graph.n ≤ B) {a p j : ℕ} (ha : a ≤ I.graph.n)
    (hp : p ≤ I.graph.n) (hj : j ≤ B) :
    ∀ r ∈ [I.graph.n, I.graph.s, I.graph.t, a, p, j, 0, 0], r ≤ B :=
  bounded hn (by have := I.graph.s.isLt; omega) (by have := I.graph.t.isLt; omega)
    (by omega) (by omega) hj (by omega) (by omega)

private theorem read_bound_loop (bs : List Bool) {j a p : ℕ}
    (hlookup : ∀ i, (encBoundedSTCON I)[j + i]? = bs[i]?)
    (hn : I.graph.n ≤ B) (hj : j + bs.length ≤ B)
    (ha : a ≤ I.graph.n) (hp : p ≤ I.graph.n) :
    ∃ p' ≤ I.graph.n, writer.ReachesOut (encBoundedSTCON I) (writer.Active B)
      (8, [I.graph.n, I.graph.s, I.graph.t, a, p, j, 0, 0])
      (12, [I.graph.n, I.graph.s, I.graph.t, scan I.graph.n a p bs,
        p', j + bs.length, 0, 0]) [] := by
  induction bs generalizing j a p with
  | nil =>
    refine ⟨p, hp, ReachesOut.read (by rfl) (I.bounded_scan hn ha hp (by simp at hj; omega)) ?_⟩
    have hend : (encBoundedSTCON I)[j]? = none := by simpa using hlookup 0
    simp only [eval_reg, List.getD_cons_succ, List.getD_cons_zero, hend, readLabel]
    simpa [scan] using
      (ReachesOut.refl (P := writer) (w := encBoundedSTCON I)
        (Q := writer.Active B) (12, [I.graph.n, I.graph.s, I.graph.t, a, p, j, 0, 0]))
  | cons b bs ih =>
    have hb {a p j : ℕ} := I.bounded_scan hn (a := a) (p := p) (j := j)
    obtain ⟨p', hp', hr⟩ := ih (j := j + 1)
      (a := min I.graph.n (a + p * b.toNat)) (p := min I.graph.n (2 * p))
      (fun i => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlookup (i + 1))
      (by simp only [List.length_cons] at hj; omega) (Nat.min_le_left _ _) (Nat.min_le_left _ _)
    refine ⟨p', hp', ?_⟩
    apply ReachesOut.read (by rfl) (hb ha hp (by simp at hj; omega))
    simp only [eval_reg, List.getD_cons_succ, List.getD_cons_zero,
      show (encBoundedSTCON I)[j]? = some b by simpa using hlookup 0]
    have hnext : writer.ReachesOut (encBoundedSTCON I) (writer.Active B)
        (10, [I.graph.n, I.graph.s, I.graph.t, min I.graph.n (a + p * b.toNat), p, j, 0, 0])
        (12, [I.graph.n, I.graph.s, I.graph.t, scan I.graph.n a p (b :: bs),
          p', j + (b :: bs).length, 0, 0]) [] := by
      apply ReachesOut.assign (by rfl) (hb (Nat.min_le_left _ _) hp (by simp at hj; omega))
      simp only [eval_minExpr, eval_mul, eval_const, eval_reg, List.getD_cons_succ,
        List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero]
      apply ReachesOut.assign (by rfl)
        (hb (Nat.min_le_left _ _) (Nat.min_le_left _ _) (by simp at hj; omega))
      simpa [scan, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
    cases b with
    | false => simpa [readLabel, Nat.min_eq_right ha] using hnext
    | true =>
      apply ReachesOut.assign (by rfl) (hb ha hp (by simp at hj; omega))
      simpa [eval_minExpr] using hnext


private def regs (p j u v : ℕ) : List ℕ :=
  [I.graph.n, I.graph.s, I.graph.t, I.cap, p, j, u, v]

private theorem regs_bounded {p j u v : ℕ} (hn : I.layered.n ≤ B)
    (hp : p ≤ I.graph.n) (hj : j ≤ B) (hu : u ≤ I.layered.n) (hv : v ≤ I.layered.n) :
    ∀ r ∈ regs I p j u v, r ≤ B := by
  have hcap := Nat.min_le_right I.bound I.graph.n
  have hn' : I.graph.n ≤ I.layered.n := by
    change I.graph.n ≤ (I.cap + 1) * I.graph.n
    nlinarith
  exact bounded (by omega) (by have := I.graph.s.isLt; omega)
    (by have := I.graph.t.isLt; omega) (by change min I.bound I.graph.n ≤ B; omega)
    (by omega) hj (by omega) (by omega)

private def entry (u v : ℕ) : Bool :=
  decide (v / I.graph.n = u / I.graph.n + 1) &&
    (I.graph.adj ⟨u % I.graph.n, Nat.mod_lt _ I.graph.n_pos⟩
      ⟨v % I.graph.n, Nat.mod_lt _ I.graph.n_pos⟩ ||
      decide (u % I.graph.n = v % I.graph.n))

private theorem entry_eq (u v : Fin I.layered.n) : I.layered.adj u v = entry I u v := by
  change (decide (v.val / I.graph.n = u.val / I.graph.n + 1) &&
    (I.graph.adj u.modNat v.modNat || decide (u.modNat = v.modNat))) = entry I u v
  simp only [Fin.ext_iff]
  rfl

private theorem write_entry {p j u v : ℕ} (hn : I.layered.n ≤ B) (hp : p ≤ I.graph.n)
    (hj : j ≤ B) (hu : u < I.layered.n) (hv : v < I.layered.n) :
    writer.ReachesOut (encBoundedSTCON I) (writer.Active B)
      (33, regs I p j u v) (32, regs I p j u v) [entry I u v] := by
  have hb := I.regs_bounded hn hp hj hu.le hv.le
  have hfalse := ReachesOut.emit (P := writer) (w := encBoundedSTCON I)
    (show writer.instr 36 = _ from rfl) hb (ReachesOut.refl (32, regs I p j u v))
  have htrue := ReachesOut.emit (P := writer) (w := encBoundedSTCON I)
    (show writer.instr 37 = _ from rfl) hb (ReachesOut.refl (32, regs I p j u v))
  apply ReachesOut.lt (by rfl) hb
  simp only [eval_const, eval_eqB, eval_div, eval_add, eval_reg, regs,
    List.getD_cons_succ, List.getD_cons_zero, Bool.toNat]
  by_cases hl : v / I.graph.n = u / I.graph.n + 1
  · simp only [hl, decide_true, Bool.cond_true]
    apply ReachesOut.lt (by rfl) hb
    simp only [eval_const, eval_eqB, eval_mod, eval_reg, regs,
      List.getD_cons_succ, List.getD_cons_zero, Bool.toNat]
    by_cases he : u % I.graph.n = v % I.graph.n
    · simpa [he, entry, hl, regs] using htrue
    · simp only [he, decide_false, Bool.cond_false]
      apply ReachesOut.read (by rfl) hb
      simp only [position, framed, eval_add, eval_mul, eval_mod, eval_reg, eval_const, regs,
        List.getD_cons_succ, List.getD_cons_zero]
      rw [I.input_graph (by
        have hpos := I.graph.mul_add_lt
          ⟨u % I.graph.n, Nat.mod_lt _ I.graph.n_pos⟩
          ⟨v % I.graph.n, Nat.mod_lt _ I.graph.n_pos⟩
        dsimp only at hpos
        rw [I.graph.length_encode]
        omega), I.graph.getElem?_encode_matrix (Nat.mod_lt _ I.graph.n_pos)
          (Nat.mod_lt _ I.graph.n_pos)]
      cases h : I.graph.adj ⟨u % I.graph.n, Nat.mod_lt _ I.graph.n_pos⟩
          ⟨v % I.graph.n, Nat.mod_lt _ I.graph.n_pos⟩
      · simpa [readLabel, entry, hl, he, h, regs] using hfalse
      · simpa [readLabel, entry, hl, he, h, regs] using htrue
  · simpa [entry, hl, regs] using hfalse

private theorem write_ones {p j i M b body exit : ℕ} {e : Expr}
    (hc : writer.CodeAt b (forCode b 6 e body exit))
    (hemit : writer.instr body = emit true (b + 2))
    (he : ∀ u, e.eval (regs I p j u 0) = M)
    (hn : I.layered.n ≤ B) (hp : p ≤ I.graph.n) (hj : j ≤ B)
    (hM : M ≤ I.layered.n) (hi : i ≤ I.layered.n) :
    writer.ReachesOut (encBoundedSTCON I) (writer.Active B)
      (b, regs I p j i 0) (exit, regs I p j M 0) (List.replicate M true) := by
  obtain ⟨_, hr, rfl, _⟩ := reachesOut_forCode (w := encBoundedSTCON I)
    (N := M) (o := fun _ => [true]) hc
    (fun u rs => rs = regs I p j u 0 ∧ u ≤ M) (hM.trans hn)
    (by rintro u rs ⟨rfl, hu⟩; exact ⟨by rfl, he u, by simp [regs],
          I.regs_bounded hn hp hj (hu.trans hM) (by omega)⟩)
    (by
      rintro u hu rs ⟨rfl, _⟩
      have hb := I.regs_bounded (v := 0) hn hp hj (hu.le.trans hM) (by omega)
      exact ⟨_, ReachesOut.emit hemit hb (ReachesOut.refl _), rfl, hb,
        by simp [regs], by omega⟩)
    (regs I p j i 0) (I.regs_bounded hn hp hj hi (by omega)) (by simp [regs])
  simpa only [List.flatMap_def, List.map_const', List.length_range,
    List.flatten_replicate_singleton] using hr

private theorem write_rows {p j i : ℕ} (hn : I.layered.n ≤ B) (hp : p ≤ I.graph.n)
    (hj : j ≤ B) (hi : i ≤ I.layered.n) :
    ∃ rs, writer.ReachesOut (encBoundedSTCON I) (writer.Active B)
      (27, regs I p j i 0) (38, rs)
      ((List.range I.layered.n).flatMap fun u => (List.range I.layered.n).map (entry I u)) ∧
      ∀ r ∈ rs, r ≤ B := by
  have hc₁ : writer.CodeAt 27 (forCode 27 6 vertices 30 38) := codeAt_of_prefix ⟨_, rfl⟩
  have hc₂ : writer.CodeAt 30 (forCode 30 7 vertices 33 29) := codeAt_of_prefix ⟨_, rfl⟩
  have he (u v : ℕ) : vertices.eval (regs I p j u v) = I.layered.n := rfl
  obtain ⟨rs, hr, v, rfl, _, hv⟩ := reachesOut_forCode (w := encBoundedSTCON I)
    (N := I.layered.n)
    (o := fun u => (List.range I.layered.n).map (entry I u)) hc₁
    (fun u rs => ∃ v, rs = regs I p j u v ∧ u ≤ I.layered.n ∧ v ≤ I.layered.n) hn
    (by
      rintro u rs ⟨v, rfl, hu, hv⟩
      exact ⟨by rfl, he u v, by simp [regs], I.regs_bounded hn hp hj hu hv⟩)
    (by
      rintro u hu rs ⟨v, rfl, _, hv⟩
      obtain ⟨_, hrow, rfl, _⟩ := reachesOut_forCode (w := encBoundedSTCON I)
        (N := I.layered.n) (o := fun v => [entry I u v]) hc₂
        (fun v rs => rs = regs I p j u v ∧ v ≤ I.layered.n) hn
        (by
          rintro v rs ⟨rfl, hv⟩
          exact ⟨by rfl, he u v, by simp [regs], I.regs_bounded hn hp hj hu.le hv⟩)
        (by
          rintro v hv rs ⟨rfl, _⟩
          exact ⟨_, I.write_entry hn hp hj hu hv, rfl,
            I.regs_bounded hn hp hj hu.le hv.le, by simp [regs], by omega⟩)
        (regs I p j u v) (I.regs_bounded hn hp hj hu.le hv) (by simp [regs])
      refine ⟨_, ?_, rfl, I.regs_bounded hn hp hj hu.le le_rfl,
        I.layered.n, by simp [regs], by omega, le_rfl⟩
      simpa only [← List.map_eq_flatMap] using hrow)
    (regs I p j i 0) (I.regs_bounded hn hp hj hi (by omega)) (by simp [regs])
  exact ⟨_, hr, I.regs_bounded hn hp hj le_rfl hv⟩


/-- The capped layered adjacency-matrix instance is computable in logarithmic space from a
framed connectivity instance and a binary bound. -/
theorem computableInLogSpace_layered :
    ComputableInLogSpace layered encBoundedSTCON encSTCON := by
  refine writer.computableInLogSpace_of_reachesOut 2 fun I => ?_
  let L := (encBoundedSTCON I).length
  let B := (L + 1) ^ 2
  have hlen : L = 2 * I.graph.encode.length + 1 + I.bound.bits.length :=
    length_frame_append _ _
  have hnL := I.graph.n_le_length_encode
  have hcap := Nat.min_le_right I.bound I.graph.n
  have hnB : I.graph.n ≤ B := by dsimp [B]; nlinarith
  have hLB : L ≤ B := by dsimp [B]; nlinarith
  have hNB : I.layered.n ≤ B := by dsimp [layered, B, cap]; nlinarith
  have hsource : (I.graph.s : ℕ) ≤ I.layered.n := by dsimp [layered]; nlinarith [I.graph.s.isLt]
  have htarget : I.cap * I.graph.n + I.graph.t ≤ I.layered.n := by
    dsimp [layered]
    nlinarith [I.graph.t.isLt]
  obtain ⟨p, hp, hparse⟩ := I.read_bound_loop I.bound.bits (j := 2 * I.graph.encode.length + 1)
    (a := 0) (p := 1) I.input_bound hnB (by omega) (Nat.zero_le _)
    (by have := I.graph.n_pos; omega)
  have hparsed : scan I.graph.n 0 1 I.bound.bits = I.cap := by
    rw [scan_eq _ _ _ _ (Nat.zero_le _), Nat.foldr_bit_bits]
    simp [cap, Nat.min_comm]
  rw [hparsed, show 2 * I.graph.encode.length + 1 + I.bound.bits.length = L by omega] at hparse
  have hb {a p j : ℕ} := I.bounded_scan hnB (a := a) (p := p) (j := j)
  have hstart := (I.read_header hnB).trans
    (ReachesOut.assign (show writer.instr 6 = _ from rfl)
      (hb (a := 0) (p := 0) (j := 0) (by omega) (by omega) (by omega))
      (by
        simp only [eval_const, List.set_cons_succ, List.set_cons_zero]
        apply ReachesOut.assign (show writer.instr 7 = _ from rfl)
          (hb (by omega) (by have := I.graph.n_pos; omega) (by omega))
        simpa [framed, graphLength, I.graph.length_encode] using hparse))
  have hones₁ := I.write_ones (p := p) (j := L) (i := 0)
    (codeAt_of_prefix ⟨_, rfl⟩) (show writer.instr 15 = _ from rfl)
    (M := I.layered.n) (e := vertices) (fun _ => rfl)
    hNB hp hLB le_rfl (Nat.zero_le _)
  have hones₂ := I.write_ones (p := p) (j := L) (i := I.layered.n)
    (codeAt_of_prefix ⟨_, rfl⟩) (show writer.instr 20 = _ from rfl)
    (M := I.graph.s) (e := reg 1) (fun _ => rfl)
    hNB hp hLB hsource le_rfl
  have hones₃ := I.write_ones (p := p) (j := L) (i := I.graph.s)
    (codeAt_of_prefix ⟨_, rfl⟩) (show writer.instr 25 = _ from rfl)
    (M := I.cap * I.graph.n + I.graph.t) (e := add (mul (reg 3) (reg 0)) (reg 2))
    (fun _ => rfl) hNB hp hLB htarget hsource
  obtain ⟨rs, hrows, hrs⟩ := I.write_rows hNB hp hLB htarget
  have hchain := hstart.trans (hones₁.trans (ReachesOut.emit
    (show writer.instr 16 = _ from rfl) (I.regs_bounded hNB hp hLB le_rfl (by omega))
    (hones₂.trans (ReachesOut.emit (show writer.instr 21 = _ from rfl)
      (I.regs_bounded hNB hp hLB hsource (by omega))
      (hones₃.trans (ReachesOut.emit (show writer.instr 26 = _ from rfl)
        (I.regs_bounded hNB hp hLB htarget (by omega)) hrows))))))
  refine ⟨(38, rs), _, [], hchain, rfl, ?_, hrs⟩
  rw [encSTCON_apply, STCONInstance.encode,
    STCONInstance.matrix_eq_flatMap _ (entry I) (I.entry_eq)]
  simp [layered, node, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

end Cslib.Complexity.BoundedSTCONInstance
