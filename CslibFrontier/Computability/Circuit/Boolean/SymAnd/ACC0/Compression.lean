/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.CNFCheck
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.EvalTable
public import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.WitnessVerifier
public import CslibFrontier.Computability.Complexity.CookLevin.IndexBound
public import CslibFrontier.Computability.Complexity.CookLevin.Witness

/-!
# Checked constant-depth decoders for polynomial-time functions

If every language in `P/poly` has polynomial-size `AC⁰[m]` circuits of depth `d`, then a function
`F` computed in polynomial time, read on inputs `(x, i)` with `|i| = a x`, has decoders that a
nondeterministic machine can guess and check with one `ACC⁰` unsatisfiability test
(`Cslib.Circuits.Boolean.SymAnd.exists_checkedDecoders`, built in
`CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.CheckedDecoders` from this module): from
a guessed word `e`, a polynomial-time construction
gives a depth-`(d + 2)` circuit `D (x, e)` on the `a x` bits of `i` and a depth-`(d + 5)` check
circuit `C₁ (x, e)`. Whenever the check circuit is unsatisfiable, `D (x, e)` computes the bits of
`F (x, i)`; and for every `x` some word `e` of polynomial length makes it unsatisfiable. This is
the compression step of [Williams2014], Lemma 3.1, for decoders computed in polynomial time.

The word `e` encodes a circuit `G` of depth `d + 1`. The intended `G` decides, on
`j`, `v` (in unary) and `i`, whether the variable numbered `v` is true in the Cook–Levin run
tableau (`Cslib.Complexity.CookLevin.runTableau`) of a machine computing bit `j` of `F (x, i)`
on the word `frame x ++ j ++ i`. That language is in `P`, so it has small circuits of depth `d`,
and hardwiring `frame x` adds one layer. The check circuit evaluates copies of `G` at every `j`
and `v` (`Cslib.Circuits.Boolean.Unbounded.evalTable`) and tests every clause of the run tableau
of every `j`, together with clauses tying its input variables to `x`, `j` and `i`
(`Cslib.Circuits.Boolean.Unbounded.cnfCheck`). When no clause fails, the values of `G` are the run
on that word, since a satisfying assignment of the run tableau is determined by its input bits
(`Cslib.Complexity.CookLevin.eq_runAssignment_of_eval_runTableau`); the decoder reads the output
variable of every run.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.Compression.checkCircuit`: the check circuit.
* `Cslib.Circuits.Boolean.SymAnd.Compression.decoderCircuit`: the decoder.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.Compression.eval_decoderCircuit_of_not_mem`: soundness.
* `Cslib.Circuits.Boolean.SymAnd.Compression.checkCircuit_not_mem`: completeness.

## References

* [R. Williams, *Non-Uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Lemma 3.1]
  [Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInPolyTime
  Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Complexity.CookLevin Cslib.Logic.PL

namespace Compression

/-! ### Words -/

/-- `j` in unary of width `n`: `j` ones, then `n - j` zeros. -/
@[expose] def unaryWord (n j : ℕ) : List Bool :=
  List.replicate j true ++ List.replicate (n - j) false

/-- A unary word of `j ≤ n` has width `n`. -/
theorem length_unaryWord {n j : ℕ} (hj : j ≤ n) : (unaryWord n j).length = n := by
  simp only [unaryWord, List.length_append, List.length_replicate]
  omega

/-- A unary word of `j` has `j` ones. -/
theorem count_unaryWord (n j : ℕ) : (unaryWord n j).count true = j := by
  simp [unaryWord, List.count_replicate]

/-- The word of the query for output `j` at the bits `i`: `frame x`, `j` in unary of width `J`,
then `i`. -/
@[expose] def queryWord (J : ℕ) (x : List Bool) (j : ℕ) (i : List Bool) : List Bool :=
  frame x ++ unaryWord J j ++ i

/-- The length of a query word. -/
theorem length_queryWord {J j : ℕ} (hj : j ≤ J) (x i : List Bool) :
    (queryWord J x j i).length = 2 * x.length + 1 + J + i.length := by
  simp only [queryWord, List.length_append, length_frame, length_unaryWord hj]

/-- Bit `j` of `F (x, i)` on the word `frame x ++ j ++ i`, with `j` read as the number of ones
among the first `J x` bits after the frame. -/
@[expose] def queryBit (J : List Bool → ℕ) (F : List Bool × List Bool → List Bool)
    (w : List Bool) : Bool :=
  (F (unframe w, (dropFrame w).drop (J (unframe w)))).getD
    (((dropFrame w).take (J (unframe w))).count true) false

/-- On a query word, `queryBit` is bit `j` of `F (x, i)`. -/
theorem queryBit_queryWord {J : List Bool → ℕ} {F : List Bool × List Bool → List Bool}
    {x : List Bool} {j : ℕ} (hj : j ≤ J x) (i : List Bool) :
    queryBit J F (queryWord (J x) x j i) = (F (x, i)).getD j false := by
  have hlen := length_unaryWord hj
  simp only [queryBit, queryWord, List.append_assoc, unframe_frame_append, dropFrame_frame_append,
    List.drop_left' hlen, List.take_left' hlen, count_unaryWord]

/-- The membership test of the intended circuit `G` for a machine `tm` running within
`cT * (n + 1) ^ dT` steps, with `V` the width of variable numbers: on `frame x`, `j` and `v` in
unary and `i`, whether the variable numbered `v` is true along the run on the query word. -/
@[expose] noncomputable def runBit {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) (cT dT : ℕ) (J V : List Bool → ℕ) (w : List Bool) :
    Bool :=
  let x := unframe w
  let j := ((dropFrame w).take (J x)).count true
  let v := (((dropFrame w).drop (J x)).take (V x)).count true
  let u := queryWord (J x) x j ((dropFrame w).drop (J x + V x))
  decide (v ∈ (trueVars tm [] u (cT * (u.length + 1) ^ dT)).map Var.index)

/-- `runBit` on `frame x`, `j` and `v` in unary and `i`: membership of `v` among the numbers
of the true variables of the run on the query word of `j` and `i`. -/
theorem runBit_eq {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
    {tm : MultiTapeTM k Bool State} {cT dT : ℕ} {J V : List Bool → ℕ} {x : List Bool}
    {j v : ℕ}
    (hj : j ≤ J x) (hv : v ≤ V x) (i : List Bool) :
    runBit tm cT dT J V (frame x ++ (unaryWord (J x) j ++ unaryWord (V x) v) ++ i) =
      decide (v ∈ (trueVars tm [] (queryWord (J x) x j i)
        (cT * ((queryWord (J x) x j i).length + 1) ^ dT)).map Var.index) := by
  have hJ := length_unaryWord hj
  have hV := length_unaryWord hv
  have hdrop : (unaryWord (J x) j ++ unaryWord (V x) v ++ i).drop (J x + V x) = i := by
    rw [List.drop_left' (by simp [hJ, hV])]
  simp only [runBit, List.append_assoc, unframe_frame_append, dropFrame_frame_append,
    List.take_left' hJ, count_unaryWord, List.drop_left' hJ, List.take_left' hV]
  rw [← List.append_assoc, hdrop]

/-! ### The construction -/

section Construction

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (cT dT cI : ℕ) (a J : List Bool → ℕ)

/-- The length of the query words of `x`. -/
@[expose] def wordLength (x : List Bool) : ℕ := 2 * x.length + 1 + J x + a x

/-- The number of steps of the run on the query words of `x`. -/
@[expose] def steps (x : List Bool) : ℕ := cT * (wordLength a J x + 1) ^ dT

/-- The width of variable numbers: a bound on the numbers of the determined variables. -/
@[expose] def width (x : List Bool) : ℕ :=
  cI * (wordLength a J x + wordLength a J x + steps cT dT a J x + 1) ^ cI

/-- The number of the output variable `[true]` at the last step. -/
@[expose] noncomputable def outVar (x : List Bool) : ℕ :=
  Var.index (Var.holds (k := k) (State := State) (steps cT dT a J x) (.out (.one true)))

/-- The run tableau of the query words of `x`, variables numbered by `Var.index`. -/
@[expose] noncomputable def tableauOf (x : List Bool) : CNF ℕ :=
  (runTableau tm [] (wordLength a J x) (steps cT dT a J x)).relabel Var.index

/-- The clauses tying input bit `p` of copy `j` to `frame x ++ j` or to the live bit. -/
@[expose] def certClauses (x : List Bool) (j p : ℕ) : CNF ℕ :=
  let W := width cT dT cI a J x
  if p < 2 * x.length + 1 + J x then
    [[(j * W + Nat.pair 1 p, (frame x ++ unaryWord (J x) j).getD p false)]]
  else
    [[(j * W + Nat.pair 1 p, true), (J x * W + (p - (2 * x.length + 1 + J x)), false)],
      [(j * W + Nat.pair 1 p, false), (J x * W + (p - (2 * x.length + 1 + J x)), true)]]

/-- The clauses of copy `j`: the run tableau shifted to the block of `j`, and its input clauses. -/
@[expose] noncomputable def blockClauses (x : List Bool) (j : ℕ) : CNF ℕ :=
  (tableauOf tm cT dT a J x).relabel (fun v => j * width cT dT cI a J x + v) ++
    (List.range (wordLength a J x)).flatMap (certClauses cT dT cI a J x j)

/-- The formula tested by the check circuit, over the outputs of the copies of `G` followed by
the live bits. -/
@[expose] noncomputable def checkFormula (x : List Bool) : CNF ℕ :=
  (List.range (J x)).flatMap (blockClauses tm cT dT cI a J x)

/-- The prefixes of the copies of `G` in the check circuit: `j` and `v` in unary. -/
@[expose] def checkPrefixes (x : List Bool) : List (List Bool) :=
  (List.range (J x * width cT dT cI a J x)).map fun p =>
    unaryWord (J x) (p / width cT dT cI a J x) ++
      unaryWord (width cT dT cI a J x) (p % width cT dT cI a J x)

/-- The prefixes of the copies of `G` in the decoder: `j` and the output variable in unary. -/
@[expose] noncomputable def decoderPrefixes (x : List Bool) : List (List Bool) :=
  (List.range (J x)).map fun j =>
    unaryWord (J x) j ++ unaryWord (width cT dT cI a J x) (outVar (k := k) (State := State)
      cT dT a J x)

/-- The circuit `G` decoded from `e`, or the constant-`false` circuit. -/
@[expose] def guessed (dG : ℕ) (x e : List Bool) :
    Circuit Unbounded.extSignature (J x + width cT dT cI a J x + a x) 1 :=
  (decodeExtWitness dG (J x + width cT dT cI a J x + a x) e).getD
    (Unbounded.constCircuit Unbounded.toExt false)

/-- **The check circuit**: true at some `i` exactly when a clause of the check formula fails on
the copies of `G` at `i`. -/
@[expose] noncomputable def checkCircuit (dG : ℕ) (x e : List Bool) :
    Circuit Unbounded.extSignature (a x) 1 :=
  (Unbounded.cnfCheck (J x * width cT dT cI a J x + a x) (checkFormula tm cT dT cI a J x)).comp
    (Unbounded.withInputs (Unbounded.evalTable (guessed cT dT cI a J dG x e)
      (J x * width cT dT cI a J x)
      fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])))

/-- **The decoder**: output `j` is `G` at `j` and the output variable. -/
@[expose] noncomputable def decoderCircuit (dG : ℕ) (x e : List Bool) :
    Circuit Unbounded.extSignature (a x) (J x) :=
  Unbounded.evalTable (guessed cT dT cI a J dG x e) (J x)
    fun j => BitString.ofList _
      ((decoderPrefixes (k := k) (State := State) cT dT cI a J x).getD j [])

end Construction

/-! ### Reading the check formula -/

/-- The assignment of the check formula: the bits of `f`, then those of `g`, then `false`. -/
@[expose] def readAt {P A : ℕ} (f : Fin P → Bool) (g : Fin A → Bool) (v : ℕ) : Bool :=
  if h : v < P + A then Fin.append f g ⟨v, h⟩ else false

/-- `readAt` below `P` reads `f`. -/
theorem readAt_of_lt {P A : ℕ} (f : Fin P → Bool) (g : Fin A → Bool) {v : ℕ} (hv : v < P) :
    readAt f g v = f ⟨v, hv⟩ := by
  rw [readAt, dite_eq_left_of_eq_true (eq_true (by omega))]
  exact Fin.append_left f g ⟨v, hv⟩

/-- `readAt` at `P + t` reads `g`. -/
theorem readAt_add {P A : ℕ} (f : Fin P → Bool) (g : Fin A → Bool) {t : ℕ} (ht : t < A) :
    readAt f g (P + t) = g ⟨t, ht⟩ := by
  rw [readAt, dite_eq_left_of_eq_true (eq_true (by omega))]
  exact Fin.append_right f g ⟨t, ht⟩

/-- Reading a list back from the indices below its length. -/
private theorem map_range_getD (l : List Bool) :
    (List.range l.length).map (fun p => l.getD p false) = l := by
  refine List.ext_getElem (by simp) fun p h₁ h₂ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

section Semantics

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  {tm : MultiTapeTM k Bool State} {cT dT cI : ℕ} {a J : List Bool → ℕ}

/-- The input clauses of bit `p` of copy `j` hold exactly when that bit is the bit of
`frame x ++ j`, or the live bit. -/
theorem eval_certClauses (x : List Bool) (j p : ℕ) (y : ℕ → Bool) :
    (certClauses cT dT cI a J x j p).eval y = true ↔
      y (j * width cT dT cI a J x + Nat.pair 1 p) =
        if p < 2 * x.length + 1 + J x then (frame x ++ unaryWord (J x) j).getD p false
        else y (J x * width cT dT cI a J x + (p - (2 * x.length + 1 + J x))) := by
  unfold certClauses
  dsimp only
  split_ifs
  · simp [CNF.eval, Clause.eval, Literal.eval]
  · simp only [CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil, Literal.eval_mk,
      Bool.and_true, Bool.or_false]
    generalize y (j * width cT dT cI a J x + Nat.pair 1 p) = u
    generalize y (J x * width cT dT cI a J x + (p - (2 * x.length + 1 + J x))) = v
    cases u <;> cases v <;> decide

/-- **The check formula holds** exactly when, for every copy `j`, the shifted assignment satisfies
the run tableau and its input bits are those of `frame x ++ j` followed by the live bits. -/
theorem eval_checkFormula (x : List Bool) (y : ℕ → Bool) :
    (checkFormula tm cT dT cI a J x).eval y = true ↔ ∀ j < J x,
      (runTableau tm [] (wordLength a J x) (steps cT dT a J x)).eval
          (fun v => y (j * width cT dT cI a J x + Var.index v)) = true ∧
        ∀ p < wordLength a J x, y (j * width cT dT cI a J x + Nat.pair 1 p) =
          if p < 2 * x.length + 1 + J x then (frame x ++ unaryWord (J x) j).getD p false
          else y (J x * width cT dT cI a J x + (p - (2 * x.length + 1 + J x))) := by
  simp only [checkFormula, blockClauses, tableauOf, CNF.eval_flatMap_eq_true_iff, List.mem_range,
    CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, eval_certClauses]
  rfl

omit [DecidableEq State] in
/-- The determined variables of the run tableau of the query words have numbers below the width,
given the index bound `hI`. -/
theorem index_lt_width
    (hI : ∀ n L T : ℕ, ∀ v : Var k State, Determined n L T v →
      Var.index v < cI * (n + L + T + 1) ^ cI)
    {x : List Bool} {v : Var k State}
    (hv : Determined (([] : List Bool).length + wordLength a J x) (wordLength a J x)
      (steps cT dT a J x) v) :
    Var.index v < width cT dT cI a J x := by
  have := hI _ _ _ v hv
  simpa [width] using this

/-- The variables of the check formula are below the number of inputs of the check. -/
theorem vars_checkFormula_lt
    (hI : ∀ n L T : ℕ, ∀ v : Var k State, Determined n L T v →
      Var.index v < cI * (n + L + T + 1) ^ cI)
    (x : List Bool) :
    ∀ c ∈ checkFormula tm cT dT cI a J x, ∀ l ∈ c,
      l.1 < J x * width cT dT cI a J x + a x := by
  intro c hc l hl
  simp only [checkFormula, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have hjW : ∀ w < width cT dT cI a J x,
      j * width cT dT cI a J x + w < J x * width cT dT cI a J x := fun w hw => by
    have : (j + 1) * width cT dT cI a J x ≤ J x * width cT dT cI a J x :=
      Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this
    omega
  simp only [blockClauses, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with hc | ⟨p, hp, hc⟩
  · simp only [CNF.relabel, tableauOf, List.mem_map] at hc
    obtain ⟨c', ⟨c'', hc'', rfl⟩, rfl⟩ := hc
    simp only [Clause.relabel, List.map_map, List.mem_map, Function.comp_apply] at hl
    obtain ⟨⟨v, b⟩, hvb, rfl⟩ := hl
    have hv : v ∈ (runTableau tm [] (wordLength a J x) (steps cT dT a J x)).vars :=
      CNF.mem_vars.2 ⟨c'', hc'', b, hvb⟩
    have := index_lt_width hI (determined_of_mem_vars_runTableau hv)
    have := hjW _ this
    simp only [Prod.map_fst]
    omega
  · have hcert : Nat.pair 1 p < width cT dT cI a J x := by
      have hd : Determined (([] : List Bool).length + wordLength a J x) (wordLength a J x)
          (steps cT dT a J x) (Var.cert (k := k) (State := State) p) := Or.inl ⟨p, hp, rfl⟩
      exact index_lt_width hI hd
    have h1 := hjW _ hcert
    unfold certClauses at hc
    dsimp only at hc
    have hpL : p < 2 * x.length + 1 + J x + a x := hp
    split_ifs at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      simp only [List.mem_singleton] at hl
      subst hl
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl <;> dsimp only <;> omega

/-- The check circuit computes the negated check formula on the copies of `G` and the live bits. -/
theorem eval_checkCircuit (m : ℕ)
    (hI : ∀ n L T : ℕ, ∀ v : Var k State, Determined n L T v →
      Var.index v < cI * (n + L + T + 1) ^ cI)
    (dG : ℕ) (x e : List Bool) (i : BitString (a x)) :
    (checkCircuit tm cT dT cI a J dG x e).eval (Unbounded.extInterpretation (modGate m)) i 0 =
      !(checkFormula tm cT dT cI a J x).eval (readAt
        ((Unbounded.evalTable (guessed cT dT cI a J dG x e) (J x * width cT dT cI a J x)
          fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])).eval
            (Unbounded.extInterpretation (modGate m)) i) i) := by
  rw [checkCircuit, Circuit.eval_comp, Unbounded.eval_cnfCheck m _ _ (vars_checkFormula_lt hI x),
    Unbounded.eval_withInputs]
  rfl

/-- The prefix of copy `j · W + w` of the check circuit is `j` and `w` in unary. -/
theorem getD_checkPrefixes {x : List Bool} {j w : ℕ} (hj : j < J x)
    (hw : w < width cT dT cI a J x) :
    (checkPrefixes cT dT cI a J x).getD (j * width cT dT cI a J x + w) [] =
      unaryWord (J x) j ++ unaryWord (width cT dT cI a J x) w := by
  set W := width cT dT cI a J x
  have hW : 0 < W := by omega
  have hlt : j * W + w < J x * W := by
    have : (j + 1) * W ≤ J x * W := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this
    omega
  have h1 : (j * W + w) / W = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hw, Nat.zero_add]
  have h2 : (j * W + w) % W = w := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
  simp only [checkPrefixes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some, h1, h2, W]

omit [DecidableEq State] in
/-- The prefix of output `j` of the decoder is `j` and the output variable in unary. -/
theorem getD_decoderPrefixes {x : List Bool} {j : ℕ} (hj : j < J x) :
    (decoderPrefixes (k := k) (State := State) cT dT cI a J x).getD j [] =
      unaryWord (J x) j ++ unaryWord (width cT dT cI a J x)
        (outVar (k := k) (State := State) cT dT a J x) := by
  simp only [decoderPrefixes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

/-- The value of copy `(j, w)` of `G` in the check circuit. -/
theorem readAt_evalTable (m : ℕ) {dG : ℕ} {x e : List Bool} (i : BitString (a x)) {j w : ℕ}
    (hj : j < J x) (hw : w < width cT dT cI a J x) :
    readAt ((Unbounded.evalTable (guessed cT dT cI a J dG x e) (J x * width cT dT cI a J x)
        fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])).eval
          (Unbounded.extInterpretation (modGate m)) i) i (j * width cT dT cI a J x + w) =
      (guessed cT dT cI a J dG x e).eval (Unbounded.extInterpretation (modGate m))
        (Fin.append (BitString.ofList _ (unaryWord (J x) j ++
          unaryWord (width cT dT cI a J x) w)) i) 0 := by
  have hlt : j * width cT dT cI a J x + w < J x * width cT dT cI a J x := by
    have : (j + 1) * width cT dT cI a J x ≤ J x * width cT dT cI a J x :=
      Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this
    omega
  rw [readAt_of_lt _ _ hlt, Unbounded.eval_evalTable]
  simp only [getD_checkPrefixes hj hw]

/-- **One copy of the run tableau determines its output variable**: an assignment satisfying the
run tableau of the query word of `j` and `i` has the output of the machine at its output
variable, for a machine computing `queryBit J F` within `cT * (n + 1) ^ dT` steps. -/
theorem eq_of_eval_runTableau {F : List Bool × List Bool → List Bool}
    (hrun : ∀ w, (tm.runFrom (tm.initCfg w) (cT * (w.length + 1) ^ dT)).state = none ∧
      (tm.runFrom (tm.initCfg w) (cT * (w.length + 1) ^ dT)).output = [queryBit J F w])
    {x : List Bool} {j : ℕ} (hj : j < J x) (i : List Bool) (hi : i.length = a x)
    {σ : Var k State → Bool}
    (hσ : (runTableau tm [] (wordLength a J x) (steps cT dT a J x)).eval σ = true)
    (hcert : certWord σ (wordLength a J x) = queryWord (J x) x j i) :
    σ (.holds (steps cT dT a J x) (.out (.one true))) = (F (x, i)).getD j false := by
  have hd : Determined (([] : List Bool).length + wordLength a J x) (wordLength a J x)
      (steps cT dT a J x) (Var.holds (k := k) (State := State) (steps cT dT a J x)
        (.out (.one true))) :=
    Or.inr (Or.inl ⟨_, le_rfl, _, Feature.out_mem_basic _, rfl⟩)
  have hlen : (queryWord (J x) x j i).length = wordLength a J x := by
    rw [length_queryWord hj.le, hi]
    rfl
  have hT : steps cT dT a J x = cT * ((queryWord (J x) x j i).length + 1) ^ dT := by
    rw [hlen]
    rfl
  obtain ⟨-, hout⟩ := hrun (queryWord (J x) x j i)
  rw [eq_runAssignment_of_eval_runTableau hσ hd, hcert, hT]
  simp only [runAssignment, List.nil_append, Feature.holds_out, hout, queryBit_queryWord hj.le]
  cases (F (x, i)).getD j false <;> rfl

/-- **Soundness of the checked decoder**: if the check circuit is unsatisfiable, the decoder
computes the bits of `F (x, i)`. -/
theorem eval_decoderCircuit_of_not_mem (m : ℕ) {F : List Bool × List Bool → List Bool}
    (hrun : ∀ w, (tm.runFrom (tm.initCfg w) (cT * (w.length + 1) ^ dT)).state = none ∧
      (tm.runFrom (tm.initCfg w) (cT * (w.length + 1) ^ dT)).output = [queryBit J F w])
    (hI : ∀ n L T : ℕ, ∀ v : Var k State, Determined n L T v →
      Var.index v < cI * (n + L + T + 1) ^ cI)
    (dG : ℕ) (x e : List Bool)
    (hunsat : ⟨a x, checkCircuit tm cT dT cI a J dG x e⟩ ∉
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)))
    (i : BitString (a x)) (j : Fin (J x)) :
    (decoderCircuit (k := k) (State := State) cT dT cI a J dG x e).eval
        (Unbounded.extInterpretation (modGate m)) i j = (F (x, List.ofFn i)).getD j false := by
  set y := readAt ((Unbounded.evalTable (guessed cT dT cI a J dG x e) (J x * width cT dT cI a J x)
    fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])).eval
      (Unbounded.extInterpretation (modGate m)) i) i with hy
  have hcheck : (checkFormula tm cT dT cI a J x).eval y = true := by
    have h0 : (checkCircuit tm cT dT cI a J dG x e).eval
        (Unbounded.extInterpretation (modGate m)) i 0 = false := by
      by_contra h
      exact hunsat (mem_SignatureCircuitSAT.2 ⟨i, by simpa using h⟩)
    rw [eval_checkCircuit m hI] at h0
    change (!(checkFormula tm cT dT cI a J x).eval y) = false at h0
    simpa using h0
  obtain ⟨hσ, hc⟩ := (eval_checkFormula x y).1 hcheck j j.isLt
  have hout : outVar (k := k) (State := State) cT dT a J x < width cT dT cI a J x := by
    refine index_lt_width hI (Or.inr (Or.inl ⟨_, le_rfl, _, Feature.out_mem_basic _, rfl⟩))
  have hcert : certWord (fun v : Var k State => y (j * width cT dT cI a J x + Var.index v))
      (wordLength a J x) =
      queryWord (J x) x j (List.ofFn i) := by
    have hlen : (queryWord (J x) x j (List.ofFn i)).length = wordLength a J x := by
      rw [length_queryWord j.isLt.le, List.length_ofFn]
      rfl
    rw [← map_range_getD (queryWord (J x) x j (List.ofFn i)), hlen, certWord]
    refine List.map_congr_left fun p hp => ?_
    rw [List.mem_range] at hp
    change y (j * width cT dT cI a J x + Nat.pair 1 p) = _
    rw [hc p hp]
    split_ifs with hpo
    · simp only [queryWord, List.getD_eq_getElem?_getD, List.getElem?_append_left
        (by simp [length_unaryWord j.isLt.le]; omega : p < (frame x ++ unaryWord (J x) j).length)]
    · have ht : p - (2 * x.length + 1 + J x) < a x := by
        have : p < 2 * x.length + 1 + J x + a x := hp
        omega
      rw [hy, readAt_add _ _ ht]
      have hfl : (frame x ++ unaryWord (J x) j).length = 2 * x.length + 1 + J x := by
        simp [length_unaryWord j.isLt.le]
      simp only [queryWord, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by omega : (frame x ++ unaryWord (J x) j).length ≤ p), hfl,
        List.getElem?_ofFn, ht]
      simp
  have hval := eq_of_eval_runTableau hrun j.isLt (List.ofFn i) (by simp) hσ hcert
  rw [← hval]
  change _ = y (j * width cT dT cI a J x + outVar (k := k) (State := State) cT dT a J x)
  rw [hy, readAt_evalTable m i j.isLt hout, decoderCircuit, Unbounded.eval_evalTable,
    getD_decoderPrefixes j.isLt]

/-- **Completeness of the checked decoder**: if `G` decides `runBit` on the words
`frame x ++ z`, the check circuit is unsatisfiable. -/
theorem checkCircuit_not_mem (m : ℕ)
    (hI : ∀ n L T : ℕ, ∀ v : Var k State, Determined n L T v →
      Var.index v < cI * (n + L + T + 1) ^ cI)
    (dG : ℕ) (x e : List Bool)
    (hG : ∀ z, (guessed cT dT cI a J dG x e).eval (Unbounded.extInterpretation (modGate m)) z 0 =
      runBit tm cT dT J (width cT dT cI a J) (frame x ++ List.ofFn z)) :
    ⟨a x, checkCircuit tm cT dT cI a J dG x e⟩ ∉
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  rw [mem_SignatureCircuitSAT]
  rintro ⟨i, hi⟩
  rw [eval_checkCircuit m hI] at hi
  set y := readAt ((Unbounded.evalTable (guessed cT dT cI a J dG x e) (J x * width cT dT cI a J x)
    fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])).eval
      (Unbounded.extInterpretation (modGate m)) i) i with hy
  suffices h : (checkFormula tm cT dT cI a J x).eval y = true by simp [h] at hi
  refine (eval_checkFormula x y).2 fun j hj => ?_
  set u := queryWord (J x) x j (List.ofFn i)
  have hlen : u.length = wordLength a J x := by
    rw [length_queryWord hj.le, List.length_ofFn]
    rfl
  have hT : steps cT dT a J x = cT * (u.length + 1) ^ dT := by
    rw [hlen]
    rfl
  -- the copies of `G` read the run on `u`
  have hrunv : ∀ v : Var k State, Determined (([] : List Bool).length + wordLength a J x)
      (wordLength a J x) (steps cT dT a J x) v →
      y (j * width cT dT cI a J x + Var.index v) = runAssignment tm [] u v := by
    intro v hv
    have hw := index_lt_width hI hv
    rw [hy, readAt_evalTable m i hj hw, hG, List.ofFn_fin_append,
      BitString.ofFn_ofList (by simp [length_unaryWord hj.le, length_unaryWord hw.le]),
      ← List.append_assoc, runBit_eq hj.le hw.le]
    rw [← hlen, hT] at hv
    rw [← decide_mem_trueVars_eq_runAssignment hv]
    exact decide_eq_decide.2 (List.mem_map_of_injective Var.index_injective)
  refine ⟨?_, fun p hp => ?_⟩
  · rw [CNF.eval_congr fun v hv => hrunv v (determined_of_mem_vars_runTableau hv)]
    exact eval_runTableau_runAssignment hlen
  · have hd : Determined (([] : List Bool).length + wordLength a J x) (wordLength a J x)
        (steps cT dT a J x) (Var.cert (k := k) (State := State) p) := Or.inl ⟨p, hp, rfl⟩
    have h1 := hrunv _ hd
    change y (j * width cT dT cI a J x + Nat.pair 1 p) = _ at h1
    rw [h1]
    simp only [runAssignment]
    split_ifs with hpo
    · simp only [u, queryWord, List.getD_eq_getElem?_getD, List.getElem?_append_left
        (by simp [length_unaryWord hj.le]; omega : p < (frame x ++ unaryWord (J x) j).length)]
    · have ht : p - (2 * x.length + 1 + J x) < a x := by
        have : p < 2 * x.length + 1 + J x + a x := hp
        omega
      rw [hy, readAt_add _ _ ht]
      have hfl : (frame x ++ unaryWord (J x) j).length = 2 * x.length + 1 + J x := by
        simp [length_unaryWord hj.le]
      simp only [u, queryWord, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by omega : (frame x ++ unaryWord (J x) j).length ≤ p), hfl,
        List.getElem?_ofFn, ht]
      simp

end Semantics

/-! ### Codes and depths -/

section Codes

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  {tm : MultiTapeTM k Bool State} {cT dT cI : ℕ} {a J : List Bool → ℕ}

/-- Reading a list of words of width `n` as bit strings and back. -/
private theorem ofFn_ofList_getD {n P : ℕ} {l : List (List Bool)} (hl : l.length = P)
    (hn : ∀ b ∈ l, b.length = n) :
    List.ofFn (fun p : Fin P => List.ofFn (BitString.ofList n (l.getD p []))) = l := by
  subst hl
  refine List.ext_getElem (by simp) fun p h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact BitString.ofFn_ofList (hn _ (List.getElem_mem h₂))

/-- There are `J x · W` prefixes in the check circuit. -/
theorem length_checkPrefixes (x : List Bool) :
    (checkPrefixes cT dT cI a J x).length = J x * width cT dT cI a J x := by
  simp [checkPrefixes]

/-- The prefixes of the check circuit have width `J x + W`. -/
theorem length_of_mem_checkPrefixes {x b : List Bool} (hb : b ∈ checkPrefixes cT dT cI a J x) :
    b.length = J x + width cT dT cI a J x := by
  simp only [checkPrefixes, List.mem_map, List.mem_range] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  set W := width cT dT cI a J x
  have hW : 0 < W := by
    rcases Nat.eq_zero_or_pos W with h | h
    · rw [h, Nat.mul_zero] at hp
      omega
    · exact h
  have h1 : p / W < J x := (Nat.div_lt_iff_lt_mul hW).2 hp
  have h2 : p % W < W := Nat.mod_lt _ hW
  rw [List.length_append, length_unaryWord h1.le, length_unaryWord h2.le]

omit [DecidableEq State] in
/-- There are `J x` prefixes in the decoder. -/
theorem length_decoderPrefixes (x : List Bool) :
    (decoderPrefixes (k := k) (State := State) cT dT cI a J x).length = J x := by
  simp [decoderPrefixes]

omit [DecidableEq State] in
/-- The prefixes of the decoder have width `J x + W` when the output variable is below `W`. -/
theorem length_of_mem_decoderPrefixes {x b : List Bool}
    (hv : outVar (k := k) (State := State) cT dT a J x ≤ width cT dT cI a J x)
    (hb : b ∈ decoderPrefixes (k := k) (State := State) cT dT cI a J x) :
    b.length = J x + width cT dT cI a J x := by
  simp only [decoderPrefixes, List.mem_map, List.mem_range] at hb
  obtain ⟨j, hj, rfl⟩ := hb
  rw [List.length_append, length_unaryWord hj.le, length_unaryWord hv]

/-- The code of the check circuit, from the codes of its parts. -/
theorem code_checkCircuit (dG : ℕ) (x e : List Bool) :
    (checkCircuit tm cT dT cI a J dG x e).code =
      Circuit.compCode (a x)
        (Unbounded.cnfCheckCode (J x * width cT dT cI a J x + a x)
          (checkFormula tm cT dT cI a J x))
        (Unbounded.withInputsCode (a x) (Unbounded.evalTableCode (a x)
          (guessed cT dT cI a J dG x e).code (checkPrefixes cT dT cI a J x))) := by
  rw [checkCircuit, Circuit.code_comp, Unbounded.code_cnfCheck, Unbounded.code_withInputs,
    Unbounded.code_evalTable, ofFn_ofList_getD (length_checkPrefixes x)
      fun b hb => length_of_mem_checkPrefixes hb]

omit [DecidableEq State] in
/-- The code of the decoder, from the code of `G`. -/
theorem code_decoderCircuit (dG : ℕ) (x e : List Bool)
    (hv : outVar (k := k) (State := State) cT dT a J x ≤ width cT dT cI a J x) :
    (decoderCircuit (k := k) (State := State) cT dT cI a J dG x e).code =
      Unbounded.evalTableCode (a x) (guessed cT dT cI a J dG x e).code
        (decoderPrefixes (k := k) (State := State) cT dT cI a J x) := by
  rw [decoderCircuit, Unbounded.code_evalTable, ofFn_ofList_getD (length_decoderPrefixes x)
    fun b hb => length_of_mem_decoderPrefixes hv hb]

/-- The decoded circuit has depth at most `max dG 1`. -/
theorem depth_guessed_le (dG : ℕ) (x e : List Bool) :
    (guessed cT dT cI a J dG x e).depth ≤ max dG 1 := by
  unfold guessed
  cases h : decodeExtWitness dG (J x + width cT dT cI a J x + a x) e with
  | none => exact (Unbounded.depth_constCircuit_le false).trans (le_max_right _ _)
  | some W =>
    exact (depth_and_codeLength_of_decodeExtWitness_eq_some h).1.trans (le_max_left _ _)

/-- The check circuit has depth at most `max dG 1 + 4`. -/
theorem depth_checkCircuit_le (dG : ℕ) (x e : List Bool) :
    (checkCircuit tm cT dT cI a J dG x e).depth ≤ max dG 1 + 4 := by
  have h1 := Circuit.depth_comp_le
    (Unbounded.cnfCheck (J x * width cT dT cI a J x + a x) (checkFormula tm cT dT cI a J x))
    (Unbounded.withInputs (Unbounded.evalTable (guessed cT dT cI a J dG x e)
      (J x * width cT dT cI a J x)
      fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])))
  have h2 := Unbounded.depth_cnfCheck_le (J x * width cT dT cI a J x + a x)
    (checkFormula tm cT dT cI a J x)
  have h3 := Unbounded.depth_withInputs_le (Unbounded.evalTable (guessed cT dT cI a J dG x e)
      (J x * width cT dT cI a J x)
      fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p []))
  have h4 := Unbounded.depth_evalTable_le (guessed cT dT cI a J dG x e)
      (J x * width cT dT cI a J x)
      fun p => BitString.ofList _ ((checkPrefixes cT dT cI a J x).getD p [])
  have h5 := depth_guessed_le (cT := cT) (dT := dT) (cI := cI) (a := a) (J := J) dG x e
  rw [checkCircuit]
  omega

omit [DecidableEq State] in
/-- The decoder has depth at most `max dG 1 + 1`. -/
theorem depth_decoderCircuit_le (dG : ℕ) (x e : List Bool) :
    (decoderCircuit (k := k) (State := State) cT dT cI a J dG x e).depth ≤ max dG 1 + 1 :=
  (Unbounded.depth_evalTable_le _ _ _).trans
    (Nat.add_le_add_right (depth_guessed_le dG x e) 1)

end Codes

end Compression

end Cslib.Circuits.Boolean.SymAnd
