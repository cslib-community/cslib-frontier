/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.LongestPath
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontierTests.Logics.Propositional.VeriPBProofText
import Mathlib.Data.Fin.VecNotation
-- `#guard` runs the dynamic program, the checkers and the brute force at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.LongestPath
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! Certified longest paths (`CslibFrontier.Logics.Propositional.PseudoBoolean.LongestPath`) for
an ordinary client, which imports the module without `import all`:

* the end-to-end theorem applied to an accepted proof, and the encoding on an instance;
* `#guard` runs of the checker on the proofs of the dynamic program: they are accepted and their
  optimum agrees with a brute force over all walks, on boundary instances (no edges, `s = t`, a
  target with no walk, parallel edges, zero lengths, vertices before `s` and after `t`) and on
  random DAGs of up to `8` vertices, labelled so that the numbering is not a topological order;
  a proof claiming a larger or a smaller optimum is rejected, and on a graph with a cycle the
  proof is rejected, as the paper predicts;
* the instances printed as OPB by the library's printer `Cslib.Logic.PL.VeriPB.Text.printOPB`
  (`opbText`), and the proofs by the test-only printer
  `CslibFrontierTests.Logics.Propositional.VeriPBProofText.pbpText`, whose output the text front
  end parses and accepts with the same conclusion. VeriPB 3.0.2 and CakePB report
  `s VERIFIED BOUNDS` on the printed texts of the instances `printCases`.

The kernel-checked client is `CslibFrontierTests.Logics.Propositional.VeriPBLongestPathDecide`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBLongestPath

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.LongestPath
open CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! ### The theorems for an ordinary client -/

/-- Acceptance of the proof of the dynamic program on an acyclic graph bounds every walk. -/
example {m n : ℕ} (src dst : Fin n → Fin m) (c : Fin n → ℕ) (s t : Fin m)
    (hG : Relation.Acyclic fun u v => ∃ e, src e = u ∧ dst e = v)
    (h : checkRed (formula src dst s t) (some (negProfit c)) (certify src dst c s t).proof = true)
    (k : ℕ) (hk : (certify src dst c s t).optimum = some k) (l : List (Fin n))
    (hl : IsWalk src dst s l t) : (l.map c).sum ≤ k :=
  ((isGreatest_of_checkRed_certify hG h).1 k hk).2 ⟨l, hl, rfl⟩

/-- The sources of the edges `0 → 1` and `1 → 2`. -/
def src₀ : Fin 2 → Fin 3 := ![0, 1]

/-- The targets of the edges. -/
def dst₀ : Fin 2 → Fin 3 := ![1, 2]

/-- The encoding on an instance: choosing both edges satisfies flow conservation from `0` to `2`,
and choosing the first alone does not. -/
example : (∀ c ∈ formula src₀ dst₀ 0 2, c.Holds fun v => v == 0 || v == 1) ∧
    ¬ ∀ c ∈ formula src₀ dst₀ 0 2, c.Holds fun v => v == 0 := by
  decide

/-! ### Evaluated runs -/

/-- The graph on the vertices `Fin (m + 1)` with the edges `es`, as triples of a source, a target
and a length. -/
def inst (m : ℕ) (es : List (ℕ × ℕ × ℕ)) :
    (Fin es.length → Fin (m + 1)) × (Fin es.length → Fin (m + 1)) × (Fin es.length → ℕ) :=
  (fun e => Fin.ofNat _ (es.getD e (0, 0, 0)).1, fun e => Fin.ofNat _ (es.getD e (0, 0, 0)).2.1,
    fun e => (es.getD e (0, 0, 0)).2.2)

/-- The longest walk from `v` to `t` of at most `fuel` edges, by brute force over all walks. -/
def brute (es : List (ℕ × ℕ × ℕ)) (t : ℕ) : ℕ → ℕ → Option ℕ
  | 0, v => if v = t then some 0 else none
  | fuel + 1, v =>
    (es.filter (·.1 == v)).foldl (fun b e => match brute es t fuel e.2.1, b with
      | some d, some d' => some (max (d + e.2.2) d')
      | some d, none => some (d + e.2.2)
      | none, _ => b) (if v = t then some 0 else none)

/-- Run the dynamic program from `s` to `t`: its optimum, and whether the checker accepts its
proof. -/
def run (m : ℕ) (es : List (ℕ × ℕ × ℕ)) (s t : ℕ) : Option ℕ × Bool :=
  let (src, dst, c) := inst m es
  let cert := certify src dst c (Fin.ofNat _ s) (Fin.ofNat _ t)
  (cert.optimum,
    checkRed (formula src dst (Fin.ofNat _ s) (Fin.ofNat _ t)) (some (negProfit c)) cert.proof)

/-- The run is accepted and agrees with the brute force, for a DAG on `m + 1` vertices. -/
def agrees (m : ℕ) (es : List (ℕ × ℕ × ℕ)) (s t : ℕ) : Bool :=
  let (k, ok) := run m es s t
  ok && k == brute es t (m + 1) s

/-- The proof of the dynamic program with its conclusion changed to the optimum `k + d`. -/
def shifted (m : ℕ) (es : List (ℕ × ℕ × ℕ)) (s t : ℕ) (d : ℤ) : Bool :=
  let (src, dst, c) := inst m es
  let cert := certify src dst c (Fin.ofNat _ s) (Fin.ofNat _ t)
  match cert.proof.conclusion, cert.optimum with
  | .bounds _ q _ _, some k =>
    checkRed (formula src dst (Fin.ofNat _ s) (Fin.ofNat _ t)) (some (negProfit c))
      ⟨cert.proof.steps, .bounds (some (-(k + d))) q (some (-(k + d))) none⟩
  | _, _ => false

/-- A DAG whose numbering is not a topological order: `0` comes before `1` and `5` after `4`. -/
def g₁ : List (ℕ × ℕ × ℕ) := [(1, 2, 2), (2, 4, 3), (1, 3, 4), (3, 4, 1), (0, 1, 9), (4, 5, 1),
  (2, 3, 0), (1, 4, 3), (1, 4, 5)]

#guard run 0 [] 0 0 == (some 0, true)
#guard agrees 1 [] 0 1
#guard agrees 5 g₁ 1 4
#guard agrees 5 g₁ 0 5
#guard agrees 5 g₁ 2 2
#guard agrees 5 g₁ 4 1
#guard agrees 5 g₁ 3 0
#guard run 5 g₁ 4 1 == (none, true)

-- A wrong optimum is rejected, above or below the true one.
#guard !shifted 5 g₁ 1 4 1
#guard !shifted 5 g₁ 1 4 (-1)
#guard shifted 5 g₁ 1 4 0

-- On a graph with the cycle `0 → 4 → 1 → 0` the proof is rejected.
#guard !(run 4 [(3, 1, 2), (1, 0, 3), (3, 2, 4), (2, 0, 1), (1, 2, 5), (0, 4, 2), (4, 1, 7)]
  3 0).2

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- A random DAG on `m + 1` vertices with `k` edges of lengths in `[0, 10)`, from the seed `s`:
each edge goes forward in the random order `π`, and the vertices are labelled by `π` so that the
numbering is not that order. -/
def randDag (s m k : ℕ) : List (ℕ × ℕ × ℕ) :=
  let π := (List.range (m + 1)).map fun i => (i * 5 + s) % (m + 1)
  let π := if π.Nodup then π else List.range (m + 1)
  ((List.range k).foldl (fun (s, es) _ =>
    let s₁ := lcg s
    let s₂ := lcg s₁
    let s₃ := lcg s₂
    let i := s₁ / 65536 % (m + 1)
    let j := s₂ / 65536 % (m + 1)
    if i = j then (s₃, es)
    else (s₃, (π.getD (min i j) 0, π.getD (max i j) 0, s₃ / 65536 % 10) :: es)) (s, [])).2

#guard (List.range 40).all fun s =>
  let m := s % 8
  agrees m (randDag s m (2 * m + 3)) (s % (m + 1)) (s * 3 % (m + 1))

/-! ### Kernel text -/

/-- The instance as OPB text, by the library's printer. -/
def opbText (m : ℕ) (es : List (ℕ × ℕ × ℕ)) (s t : ℕ) : String :=
  let (src, dst, c) := inst m es
  Text.printOPB ⟨formula src dst (Fin.ofNat _ s) (Fin.ofNat _ t), some (negProfit c), none⟩

/-- The text front end accepts the printed proof against the printed instance, with the
conclusion of the dynamic program. -/
def textAgrees (m : ℕ) (es : List (ℕ × ℕ × ℕ)) (s t : ℕ) : Bool :=
  let (src, dst, c) := inst m es
  let cert := certify src dst c (Fin.ofNat _ s) (Fin.ofNat _ t)
  Text.checkOPB (opbText m es s t) (pbpText (2 * (m + 1)) cert.proof) ==
    some cert.proof.conclusion

/-- The instances whose texts were checked by VeriPB and CakePB. -/
def printCases : List (ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ) :=
  [(0, [], 0, 0), (1, [], 0, 1), (5, g₁, 1, 4), (5, g₁, 0, 5), (5, g₁, 2, 2), (5, g₁, 4, 1),
    (7, randDag 3 7 17, 3, 1), (7, randDag 11 7 17, 3, 1)]

#guard printCases.all fun (m, es, s, t) => textAgrees m es s t

end CslibFrontierTests.Logics.Propositional.VeriPBLongestPath
