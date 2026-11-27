/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Circuit.Boolean.UniformDepth
import CslibFrontier.Computability.Circuit.Boolean.UniformFanIn
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Tabulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Routines
import CslibFrontier.Computability.Complexity.Problems.STCON.Reduction
import CslibFrontier.Computability.Circuit.Boolean.AltFormula
import CslibFrontier.Computability.Circuit.Boolean.RepeatedSquaring.LogSpace
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Circuit.Encoding.MapOp
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Simps
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Circuits for nondeterministic logarithmic space

Each entry of a machine's configuration graph at a fixed input length depends on at most one
input bit. A first circuit supplies positive and negative literals and both constants to the
reflexive adjacency matrix. Repeated Boolean matrix squaring then computes reachability of the
accepting sink. The graph has polynomially many vertices, so its closure needs logarithmically
many squarings. This implements the Boolean matrix-powering argument of [Arora and Barak,
Chapter 6, Exercise 9(b–c), 2007 draft][AroraBarak07].

## Main results

* `exists_mem_logspaceUniformAC_one_of_mem_NL` gives a logspace-uniform AC¹ language
  agreeing with the problem on every encoded instance, for arbitrary injective encodings.
* `NL_subset_logspaceUniformAC_one` gives the class containment for bit languages.
  The generator reads the input length in unary and writes native gates with binary
  wire addresses. `NL_subset_logspaceUniformNC_two` composes with uniform fan-in reduction.
* `NL_subset_AC_one` gives the nonuniform containment by forgetting the generator.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, 2007 web draft,
  Chapter 6, Exercise 9(b–c), printed page 114][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean
open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

private def symbolWire {n : ℕ} (i : ℕ) (f : Option Bool → Bool) : Fin (n + n) ⊕ Bool :=
  if h : i < n then
    match f (some false), f (some true) with
    | false, false => .inr false
    | true, true => .inr true
    | false, true => .inl (Fin.castAdd n ⟨i, h⟩)
    | true, false => .inl (Fin.natAdd n ⟨i, h⟩)
  else .inr (f none)

private theorem eval_symbolWire (w : List Bool) (i : ℕ) (f : Option Bool → Bool) :
    (symbolWire i f).elim (AltFormula.literals w.get) id = f w[i]? := by
  by_cases hi : i < w.length
  · rw [List.getElem?_eq_getElem hi]
    cases hf : f (some false) <;> cases ht : f (some true) <;> cases hx : w[i] <;>
      simp only [symbolWire, dite_eq_left hi, hf, ht, Sum.elim_inl, Sum.elim_inr, id_eq,
        AltFormula.literals, Fin.append_left, Fin.append_right, List.get_eq_getElem, hx,
        Bool.not_false, Bool.not_true]
  · simp [symbolWire, hi]

private theorem symbolWire_address (n i : ℕ) (f : Option Bool → Bool) :
    (symbolWire (n := n) i f).elim Fin.val (fun b => n + n + b.toNat) =
      if i < n then
        if f (some false) then (if f (some true) then n + n + 1 else n + i)
        else (if f (some true) then i else n + n)
      else if f none then n + n + 1 else n + n := by
  by_cases h : i < n
  · cases h₀ : f (some false) <;> cases h₁ : f (some true) <;>
      simp [symbolWire, h, h₀, h₁, Nat.add_comm]
  · cases h₀ : f none <;> simp [symbolWire, h, h₀]

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

private abbrev vertices (k D n : ℕ) := vertexBound (k := k) (radix D n) + 1

/-- Select the source wire for one reflexive configuration-matrix entry. The first `n` literal
wires are inputs and the next `n` are their complements. A constant wire carries its Boolean
value. Matrix rows and columns use the configuration graph's vertex identifiers and sink. -/
noncomputable def STCON.matrixWire (D n u v : ℕ) : Fin (n + n) ⊕ Bool :=
  if u = v then .inr true
  else if v < vertexBound (k := k) (radix D n) then
    symbolWire (queryIndex (k := k) (radix D n) u) (edgeWithSymbol ntm (radix D n) n u v)
  else .inr (bad (k := k) (State := State) (radix D n) n u)

open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- A deterministic machine computes the binary wire address of a matrix entry within the common
space budget of its binary parameters. Wire addresses `2n` and `2n + 1` are the shared constants
false and true. The machine uses only the input length and two vertex addresses. -/
theorem STCON.matrixWire_address_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (D : ℕ) {n u v : α → ℕ} (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S) (hv : ComputableInSpace v enc encNat S) :
    ComputableInSpace (fun a => (matrixWire ntm D (n a) (u a) (v a)).elim Fin.val
      (fun b => n a + n a + b.toNat)) enc encNat S := by
  have hB := radix_budget D hn
  have hi := queryIndex_budget (k := k) hB hu
  have hbound := vertexBound_budget (k := k) hB
  have hbad := bad_budget (k := k) (State := State) hB hn hu
  have he (b : Option Bool) := edgeWithSymbol_budget ntm hB hn hu hv (budget_const b)
  have hfalse := budget_natAdd hn hn
  have htrue := budget_natSucc hfalse
  have hoff := budget_natAdd hn hi
  have hsink := budget_ite hbad htrue hfalse
  have habsent := budget_ite (he none) htrue hfalse
  have hread := budget_ite (he (some false)) (budget_ite (he (some true)) htrue hoff)
    (budget_ite (he (some true)) hi hfalse)
  have hentry := budget_iteProp (budget_natLt hi hn) hread habsent
  refine (budget_iteProp (budget_natEq hu hv) htrue
    (budget_iteProp (budget_natLt hv hbound) hentry hsink)).of_enc_eq fun a => ?_
  by_cases huv : u a = v a
  · simp [matrixWire, huv]
  · by_cases hlt : v a < vertexBound (k := k) (radix D (n a))
    · simp [matrixWire, huv, hlt, symbolWire_address]
    · cases hb : bad (k := k) (State := State) (radix D (n a)) (n a) (u a) <;>
        simp [matrixWire, huv, hlt, hb]

private noncomputable def adjacencyWire (D n : ℕ) (ij : Fin (vertices k D n * vertices k D n)) :
    Fin (n + n) ⊕ Bool :=
  let (u, v) := finProdFinEquiv.symm ij
  STCON.matrixWire ntm D n u v

private theorem eval_adjacencyWire (w : List Bool)
    (u v : Fin (vertices k (radixExponent State c) w.length)) :
    substitute (adjacencyWire ntm (radixExponent State c) w.length) (AltFormula.literals w.get)
      (finProdFinEquiv (u, v)) = true ↔
      Relation.ReflGen (STCON.configurationInstance ntm c w).Adj u v := by
  change _ ↔ Relation.ReflGen (fun a b : Fin (vertices k (radixExponent State c) w.length) =>
    STCON.sinkAdj ntm (radixExponent State c) w a b = true) u v
  simp only [substitute, adjacencyWire, Equiv.symm_apply_apply, STCON.matrixWire,
    ← Fin.ext_iff, Relation.reflGen_iff]
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, Ne.symm huv, ↓reduceIte, false_or, STCON.sinkAdj]
    split <;> simp [eval_symbolWire]

private theorem code_literalsCircuit (n : ℕ) :
    (AltFormula.literalsCircuit n).code =
      (List.ofFn fun i : Fin n => (Unbounded.Op.not, [i.val]), List.range (n + n)) := by
  rw [AltFormula.literalsCircuit, Circuit.code_append, Circuit.code_pi_oneGate,
    Circuit.code_wiring_id]
  simp only [Circuit.appendCode, List.length_nil, List.nil_append, List.map_ofFn,
    Function.comp_def, List.ofFn_const, Unbounded.Op.arity, List.replicate_one]
  have hshift (i : ℕ) : Circuit.shiftCodeWire n 0 i = i := by simp [Circuit.shiftCodeWire]
  simp only [hshift, List.map_singleton]
  congr 1
  rw [List.range_add]
  congr 1
  exact List.ext_getElem (by simp) fun i _ _ => by simp

private theorem code_substitution {n N : ℕ} (ρ : Fin N → Fin n ⊕ Bool) :
    ((substituteCircuit ρ).mapOp Unbounded.deMorganToUnbounded).code =
      ([(Unbounded.Op.or 0, []), (.and 0, [])], List.ofFn fun i =>
        (ρ i).elim Fin.val (fun b => n + b.toNat)) := by
  rw [Circuit.code_mapOp]
  apply Prod.ext
  · rfl
  · change List.ofFn _ = _
    congr 1
    funext i
    cases h : ρ i with
    | inl j =>
      simp [substituteCircuit, Circuit.comp, Circuit.wiring, Circuit.append, Circuit.id,
        Function.comp_def, h, Wire.toNat, Program.appendedWire]
      rfl
    | inr b =>
      cases b <;> simp [substituteCircuit, Circuit.comp, Circuit.wiring, Circuit.append, Circuit.id,
        Function.comp_def, h, Wire.toNat, Program.appendedWire] <;> rfl

private noncomputable def inputCircuit (D n : ℕ) :
    Circuit Unbounded.signature n (vertices k D n * vertices k D n) :=
  ((substituteCircuit (adjacencyWire ntm D n)).mapOp Unbounded.deMorganToUnbounded).comp
    (AltFormula.literalsCircuit n)

private def constantLines : List (Unbounded.Op × List ℕ) := [(.or 0, []), (.and 0, [])]

private theorem code_inputCircuit (D n : ℕ) :
    (inputCircuit ntm D n).code =
      ((List.ofFn fun i : Fin n => (Unbounded.Op.not, [i.val])) ++ constantLines,
        List.ofFn fun i => (adjacencyWire ntm D n i).elim Fin.val (fun b => n + n + b.toNat)) := by
  rw [inputCircuit, Circuit.code_comp, code_substitution, code_literalsCircuit]
  let prefixCode : List (Unbounded.Op × List ℕ) × List ℕ :=
    (List.ofFn fun i : Fin n => (.not, [i.val]), List.range (n + n))
  have hw (i : ℕ) : Circuit.compCodeWire n prefixCode i = i := by
    by_cases h : i < n + n
    · simp [Circuit.compCodeWire, prefixCode, h, List.getD_eq_getElem?_getD]
    · simp [Circuit.compCodeWire, prefixCode, h]; omega
  change Circuit.compCode n _ prefixCode = _
  simp only [Circuit.compCode, List.map_cons, List.map_nil, List.map_ofFn, Function.comp_def, hw]
  rfl

private noncomputable def acceptanceCircuit (n : ℕ) : Circuit Unbounded.signature n 1 :=
  let D := radixExponent State c
  let N := vertices k D n
  let start : Fin N := ⟨startID ntm (radix D n),
    (STCON.startID_lt_vertexBound ntm c n).trans (Nat.lt_succ_self _)⟩
  let target : Fin N := Fin.last _
  (Circuit.wiring _ (fun _ : Fin 1 => finProdFinEquiv (start, target))).comp
    (((squareCircuit N).iterate (Nat.clog 2 N)).comp (inputCircuit ntm D n))

private noncomputable def routedWire (D n i : ℕ) : ℕ :=
  let N := vertices k D n
  if i < N * N then (STCON.matrixWire ntm D n (i / N) (i % N)).elim Fin.val
    (fun b => n + n + b.toNat)
  else n + n + 2 + (i - N * N)

private theorem compCodeWire_inputCircuit (D n : ℕ) :
    Circuit.compCodeWire n (inputCircuit ntm D n).code = routedWire ntm D n := by
  funext i
  rw [code_inputCircuit]
  by_cases hi : i < vertices k D n * vertices k D n
  · simp only [Circuit.compCodeWire, List.length_ofFn, ite_eq_left hi, routedWire,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some,
      adjacencyWire]
    rfl
  · simp only [Circuit.compCodeWire, List.length_ofFn, routedWire, ite_eq_right hi,
      List.length_append, constantLines, List.length_cons, List.length_nil]
    omega

open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace in
private theorem routedWire_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (D : ℕ) {n i : α → ℕ} (hn : ComputableInSpace n enc encNat S)
    (hi : ComputableInSpace i enc encNat S) :
    ComputableInSpace (fun a => routedWire ntm D (n a) (i a)) enc encNat S := by
  have hN := budget_natSucc (vertexBound_budget (k := k) (radix_budget D hn))
  have hNN := budget_natMul hN hN
  exact budget_iteProp (budget_natLt hi hNN)
    (STCON.matrixWire_address_budget ntm D hn (budget_natDiv hi hN) (budget_natMod hi hN))
    (budget_natAdd (budget_natAdd (budget_natAdd hn hn) (budget_const 2)) (budget_natSub hi hNN))

private theorem code_project {n m : ℕ} (c : Circuit Unbounded.signature n m) (i : Fin m) :
    ((Circuit.wiring _ (fun _ : Fin 1 => i)).comp c).code =
      (c.code.1, [c.code.2.getD i.val 0]) := by
  have hlen : c.code.2.length = m := List.length_ofFn
  simp [Circuit.code_comp, Circuit.code_wiring, Circuit.compCode, Circuit.compCodeWire, hlen]

private theorem code_acceptanceCircuit (n : ℕ) :
    let D := radixExponent State c
    let N := vertices k D n
    let t := Nat.clog 2 N
    let start : Fin N := ⟨startID ntm (radix D n),
      (STCON.startID_lt_vertexBound ntm c n).trans (Nat.lt_succ_self _)⟩
    let target : Fin N := Fin.last _
    let route := routedWire ntm D n
    (acceptanceCircuit ntm c n).code =
      (((List.ofFn fun i : Fin n => (Unbounded.Op.not, [i.val])) ++ constantLines) ++
        (List.ofFn fun r : Fin t =>
          (squareGateList N (N * N + r.val * (N ^ 2 * (N + 1)))
            (fun i => squareOutputWire N r.val i.val)).map
            fun g => (g.1, g.2.map route)).flatten,
        [route (squareOutputWire N t (finProdFinEquiv (start, target)))]) := by
  dsimp only
  rw [acceptanceCircuit, code_project, Circuit.code_comp, code_iterate_squareCircuit]
  unfold Circuit.compCode
  rw [compCodeWire_inputCircuit, code_inputCircuit]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
  have hget {m : ℕ} (f : Fin m → ℕ) (i : Fin m) : (List.ofFn f).getD i.val 0 = f i := by
    simp [List.getD_eq_getElem?_getD]
  rw [hget]

open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.MultiTapeTM.ComputableInLogSpace

private theorem vertices_logspace (D : ℕ) :
    ComputableInLogSpace (vertices k D) encUnary encUnary := by
  change ComputableInLogSpace (fun n => vertexBound (k := k) (radix D n) + 1) _ _
  simp_rw [vertexBound_eq_pow]
  fun_prop

private theorem rounds_logspace (D : ℕ) :
    ComputableInLogSpace (fun n => Nat.clog 2 (vertices k D n)) encUnary encUnary :=
  (unarySize (unarySub (vertices_logspace (k := k) D) (const 1))).congr_fun fun n =>
    eq_of_forall_ge_iff fun i => by
      rw [Nat.clog_le_iff_le_pow (by decide), Nat.size_le]
      have := Nat.two_pow_pos i
      omega

private theorem finalWire_logspace (nD : ℕ) :
    ComputableInLogSpace (fun n =>
      let B := radix nD n
      let N := vertices k nD n
      routedWire ntm nD n (squareOutputWire N (Nat.clog 2 N)
        (vertexBound (k := k) B + N * startID ntm B))) encUnary encNat := by
  have hn := unaryToBinary_inSpace (ComputableInLogSpace.id (encIn := encUnary))
  have hB := radix_budget nD hn
  have hbound := vertexBound_budget (k := k) hB
  have hN := budget_natSucc hbound
  have hi := budget_natAdd hbound (budget_natMul hN (startID_budget ntm hB))
  have ht := unaryToBinary_inSpace (rounds_logspace (k := k) nD)
  have hM := budget_natSucc hN
  have hround := budget_natMul (budget_natPred ht) (budget_natMul (budget_natPow hN 2) hM)
  have haddr := budget_natAdd (budget_natAdd (budget_natAdd (budget_natMul hN hN) hround)
    (budget_natMul hi hM)) hN
  obtain ⟨t, c, h, _⟩ := routedWire_budget ntm nD hn
    (budget_iteProp (budget_natEq ht (budget_const 0)) hi haddr)
  exact ⟨t, c, h⟩

private theorem acceptanceCircuit_uniform :
    Circuit.IsLogspaceUniform Unbounded.encOp (acceptanceCircuit ntm c) := by
  let D := radixExponent State c
  let gates := Circuit.encGate Unbounded.encOp
  have hw : ComputableInLogSpace (fun p : ℕ × ℕ => routedWire ntm D p.1 p.2)
      (encPair encUnary encUnary) encNat := by
    obtain ⟨t, b, h, _⟩ := routedWire_budget ntm D
      (unaryToBinary_inSpace (fst encUnary encUnary)) (unaryToBinary_inSpace (snd encUnary encUnary))
    exact ⟨t, b, h⟩
  have hsq := computableInLogSpace_iterate_squareGateList
    (wire := routedWire ntm D)
    (vertices_logspace (k := k) D) (rounds_logspace (k := k) D) hw
  have hneg : ComputableInLogSpace (fun n => List.ofFn fun i : Fin n =>
      (Unbounded.Op.not, [i.val])) encUnary (encList gates) := by
    apply (map_range .unary ComputableInLogSpace.id (pair (const Unbounded.Op.not)
      (listCons (unaryToBinary (snd encUnary encUnary)) (const [])))).congr_fun
    intro n
    rw [List.map_range_eq_ofFn]
  have hgs := listAppend (listAppend hneg (const constantLines)) hsq
  have hout := listCons (finalWire_logspace ntm D) (const [])
  apply (pair (ComputableInLogSpace.id (encIn := encUnary)) (pair hgs hout)).congr
  intro n
  rw [Circuit.encCircuit_apply, code_acceptanceCircuit]
  rfl

private theorem eval_acceptanceCircuit (w : List Bool) :
    (acceptanceCircuit ntm c w.length).eval Unbounded.interpretation w.get 0 = true ↔
      STCON.configurationInstance ntm c w ∈ STCON := by
  simp only [acceptanceCircuit, inputCircuit, Circuit.eval_comp, Circuit.eval_wiring,
    Function.comp_apply,
    Circuit.eval_mapOp (I := Boolean.interpretation), eval_substituteCircuit,
    AltFormula.eval_literalsCircuit, mem_STCON]
  exact (eval_iterate_squareCircuit_iff_reflTransGen (eval_adjacencyWire ntm c w)
    (fun _ => .refl) (Nat.le_pow_clog (by decide : 1 < 2) _) _ _).trans (by
      let I := STCON.configurationInstance ntm c w
      change Relation.ReflTransGen (Relation.ReflGen I.Adj) I.s I.t ↔ _
      rw [Relation.reflTransGen_reflGen])

private theorem depth_acceptanceCircuit_le (n : ℕ) :
    (acceptanceCircuit ntm c n).depth ≤
      2 + Nat.clog 2 (vertices k (radixExponent State c) n) * 2 := by
  circuit_bound [acceptanceCircuit, inputCircuit]

/-- Every nondeterministic logspace problem has a logspace-uniform family of polynomial-size,
logarithmic-depth unbounded fan-in circuits deciding it on all encoded inputs. The generator
takes the input length in unary and writes native circuit code with binary wire numbers. -/
theorem exists_mem_logspaceUniformAC_one_of_mem_NL {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (h : A ∈ NL enc) : ∃ L ∈ LogspaceUniformAC 1, ∀ a, a ∈ A ↔ enc a ∈ L := by
  classical
  obtain ⟨k, State, _, ntm, c, h⟩ := h
  let := Fintype.ofFinite State
  let N := vertices k (radixExponent State c)
  have hN : PolynomiallyBounded N := by
    change PolynomiallyBounded (fun n => vertexBound (k := k) (radix (radixExponent State c) n) + 1)
    simp_rw [vertexBound_eq_pow]
    fun_prop
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log hN
  let f (n : ℕ) (x : BitString n) := (acceptanceCircuit ntm c n).eval Unbounded.interpretation x 0
  refine ⟨Language.ofSlices f, ⟨acceptanceCircuit ntm c,
    acceptanceCircuit_uniform ntm c, 2 * e + 2, fun n => ?_⟩, fun a => ?_⟩
  · refine ⟨fun x => ?_, ?_⟩
    · ext j
      fin_cases j
      simp [single, f]
    · calc
        _ ≤ 2 + Nat.clog 2 (N n) * 2 := depth_acceptanceCircuit_le ntm c n
        _ ≤ (2 * e + 2) * (Nat.log 2 n + 1) ^ 1 := by nlinarith [he n]
  · exact (h.1 a).2.trans ((STCON.configurationInstance_mem_iff ntm c (h.1 a).1).symm.trans
      (eval_acceptanceCircuit ntm c (enc a)).symm)

/-- **NL ⊆ logspace-uniform AC¹** for bit languages. A single deterministic logspace transducer
generates the polynomial-size, logarithmic-depth circuits over the unbounded fan-in basis. -/
theorem NL_subset_logspaceUniformAC_one : NL encBits ⊆ LogspaceUniformAC 1 := by
  intro A hA
  obtain ⟨L, hL, h⟩ := exists_mem_logspaceUniformAC_one_of_mem_NL hA
  exact (Set.ext h) ▸ hL

/-- **NL ⊆ logspace-uniform NC²** for bit languages, with fan-in two. -/
theorem NL_subset_logspaceUniformNC_two : NL encBits ⊆ LogspaceUniformNC 2 :=
  NL_subset_logspaceUniformAC_one.trans (logspaceUniformAC_subset_NC_succ 1)

/-- **NL ⊆ nonuniform AC¹** for bit languages, with polynomial size and logarithmic depth. -/
theorem NL_subset_AC_one : NL encBits ⊆ AC 1 :=
  NL_subset_logspaceUniformAC_one.trans LogspaceUniformDepthClass.subset_depthClass

end Cslib.Complexity
