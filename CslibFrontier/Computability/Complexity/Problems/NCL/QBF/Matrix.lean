/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Chain
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Network

/-!
# The CNF matrix at the end of a quantifier chain

The matrix network of [HearnDemaine2005, Section 3.1] feeds a return gate. Its satisfied wire
points up only if both trying and the network value are active. Literal continuations end in
pairs, as do the free red wires of the return gate's conversions.

The number of preceding literal pairs is threaded through the terminal construction. Peeling
one quantifier increases that number by one, so the terminal and chain boundaries agree without
casts. Clause masks use the physical order of the literal wires: innermost variable first,
positive literal before negative literal.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Matrix.returnGate`: combine trying and the matrix value.
* `Cslib.Complexity.NCL.QBF.Matrix.terminal`: terminate the controls and literal wires.
* `Cslib.Complexity.NCL.QBF.Matrix.body`: the actual chain followed by its CNF terminal.

## Main results

* `Cslib.Complexity.NCL.QBF.Matrix.holds_terminal`: satisfied needs trying and a true CNF
  on the incoming literal wires.
* `Cslib.Complexity.NCL.QBF.Matrix.terminal_spec`: satisfaction implies the matrix on the
  current latch values; the proof allows inactive literal wires on either side of a latch.
* `Cslib.Complexity.NCL.QBF.Matrix.truth_of_reachable`: the actual body's success from any
  legal inactive start implies the quantified matrix, with no assumed terminal contracts.

The two outer control wires remain open. `NCL.QBF.Source` supplies the upstream QBF evaluation
bridge. `NCL.QBF.Initial` constructs legal inactive orientations for arbitrary bodies.
`NCL.QBF.Completeness` proves the body's success equivalence. `NCL.QBF.Circuit` closes its
controls with an output latch and proves reachability of an explicit fixed target.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Matrix

open Diagram Gate Network

local notation "R" => Color.red
local notation "B" => Color.blue

/-- `[sat, try, value] → []`: an active satisfied wire needs both trying and the matrix value.
Both blue inputs are converted to red, the free wires end together, and an AND vertex returns
the satisfied wire. -/
@[expose] def returnGate : Diagram Gate [B, B, B] [] :=
  (pad [B] ((gen vnoc).tensor (gen vnoc)) []).comp <|
    (pad [B, R] (swap R R) [R]).comp ((node [B, R, R] []).tensor (gen cap))

/-- End `p` literal pairs while preserving the wires `r` beside them. -/
@[expose] def caps (r : List Color) : (p : ℕ) → Diagram Gate (bundle (2 * p) ++ r) r
  | 0 => .id r
  | p + 1 => (gen cap).tensor (caps r p)

/-- The terminal for `p` literal pairs: evaluate the network, move its value beside the control
wires, return satisfaction through the AND gate, and end the literal continuations. -/
@[expose] def terminalBase (p : ℕ) (ms : List (List Bool)) :
    Diagram Gate ([B, B] ++ (bundle (2 * p) ++ [])) [] :=
  (((Diagram.id [B, B]).tensor (network [] (2 * p) ms)).comp
    ((Diagram.id [B, B]).tensor (moveLeft (bundle (2 * p)) B []))).comp
      (returnGate.tensor (caps [] p))

/-- Thread the number of older literal pairs through the chain's boundary. -/
@[expose] def terminal (p : ℕ) : (qs : List Quantifier) → List (List Bool) →
    Diagram Gate (Chain.boundary (bundle (2 * p) ++ []) qs) []
  | [], ms => terminalBase p ms
  | _ :: qs, ms => terminal (p + 1) qs ms

/-- The chain and its actual CNF terminal, with the two outer control wires still open. -/
@[expose] def body (qs : List Quantifier) (ms : List (List Bool)) : Diagram Gate [B, B] [] :=
  (Chain.diagram [] qs).comp (terminal 0 qs ms)

/-- The return gate's contract, independent of its internal configurations. -/
private def ReturnSpec (x _ : List Bool) : Prop :=
  match x with
  | [sat, attempt, value] => sat = false → attempt = true ∧ value = true
  | _ => True

private instance (x y : List Bool) : Decidable (ReturnSpec x y) :=
  match x with
  | [] | [_] | [_, _] => isTrue trivial
  | [_, _, _] => inferInstanceAs (Decidable (_ = false → _ = true ∧ _ = true))
  | _ :: _ :: _ :: _ :: _ => isTrue trivial

private theorem holds_returnGate : Holds Gate.interp returnGate ReturnSpec :=
  Holds.of_check 2 (by decide +kernel)

/-- The terminal's contract reads the incoming literal wires in their physical order. -/
@[expose] def EndSpec (ms : List (List Bool)) (x _ : List Bool) : Prop :=
  match x with
  | sat :: attempt :: literals =>
    sat = false → attempt = true ∧ ms.all (hits · literals) = true
  | _ => True

private theorem holds_network_no_tail (n : ℕ) (ms : List (List Bool)) :
    Holds Gate.interp (network [] n ms) fun x y =>
      ∃ ls value, y = ls ++ [value] ∧ ls.length = n ∧ value ≤ ms.all (hits · x) :=
  (holds_network [] n ms).mono <| by
    rintro _ _ hx - ⟨ls, rs, ls', value, rfl, rfl, hls, hf, hv⟩
    obtain rfl : rs = [] := List.eq_nil_of_length_eq_zero (by simp at hx; omega)
    exact ⟨ls', value, rfl, hf.length_eq.trans hls, by simpa using hv⟩

private def FeedSpec (ms : List (List Bool)) (x y : List Bool) : Prop :=
  ∃ sat attempt ls ls' value, x = sat :: attempt :: ls ∧ y = sat :: attempt :: value :: ls' ∧
    value ≤ ms.all (hits · ls)

private theorem holds_feed (p : ℕ) (ms : List (List Bool)) :
    Holds Gate.interp (((Diagram.id [B, B]).tensor (network [] (2 * p) ms)).comp
      ((Diagram.id [B, B]).tensor (moveLeft (bundle (2 * p)) B []))) (FeedSpec ms) :=
  (((holds_network_no_tail (2 * p) ms).id_tensor [B, B]).comp
    ((Holds.moveLeft (bundle (2 * p)) B []).id_tensor [B, B])).mono <| by
    rintro _ _ - - ⟨_, ⟨ctrl, ls, _, rfl, rfl, hc, ls', value, rfl, hls', hv⟩,
      ⟨ctrl', _, _, hmid, rfl, hc', us, bit, rs, rfl, rfl, hus, hrs⟩⟩
    obtain ⟨sat, attempt, rfl⟩ := List.length_eq_two.1 hc
    obtain ⟨_, _, rfl⟩ := List.length_eq_two.1 hc'
    obtain rfl := List.eq_nil_of_length_eq_zero hrs
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hmid
    obtain ⟨rfl, rfl, hmid⟩ := hmid
    obtain ⟨rfl, hvalue⟩ := List.append_inj hmid
      (hls'.trans (by simpa only [bundle, List.length_replicate] using hus.symm))
    obtain ⟨rfl, -⟩ := List.cons.inj hvalue
    exact ⟨sat, attempt, ls, ls', value, rfl, by simp, hv⟩

private theorem holds_return_caps (p : ℕ) :
    Holds Gate.interp (returnGate.tensor (caps [] p)) fun x _ =>
      ∃ sat attempt value rs, x = sat :: attempt :: value :: rs ∧
        (sat = false → attempt = true ∧ value = true) :=
  (holds_returnGate.tensor (C₂ := fun _ _ => True) (fun _ _ => trivial)).mono <| by
    rintro _ _ - - ⟨x, rs, y, _, rfl, rfl, hx, -, hret, -⟩
    obtain ⟨sat, attempt, value, rfl⟩ := List.length_eq_three.1 hx
    exact ⟨sat, attempt, value, rs, rfl, hret⟩

private theorem holds_terminalBase (p : ℕ) (ms : List (List Bool)) :
    Holds Gate.interp (terminalBase p ms) (EndSpec ms) :=
  ((holds_feed p ms).comp (holds_return_caps p)).mono <| by
    rintro _ _ - - ⟨_, ⟨sat, attempt, ls, ls', value, rfl, rfl, hv⟩, ⟨_, _, _, _, hmid, hret⟩⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa only [List.cons.injEq] using hmid
    exact fun hsat => ⟨(hret hsat).1, le_antisymm le_top ((hret hsat).2 ▸ hv)⟩

/-- **The actual CNF terminal is sound**: an active satisfied wire needs trying and a true
matrix on its incoming literal wires. -/
theorem holds_terminal : ∀ (qs : List Quantifier) (p : ℕ) (ms : List (List Bool)),
    Holds Gate.interp (terminal p qs ms) (EndSpec ms)
  | [], p, ms => holds_terminalBase p ms
  | _ :: qs, p, ms => holds_terminal qs (p + 1) ms

/-- The matrix evaluated on memory values in binding order. Its masks mark literal wires in
physical order, as specified by `Chain.literalValues`. -/
@[expose] def Satisfies (ms : List (List Bool)) (values : List Bool) : Prop :=
  ms.all (hits · (Chain.literalValues values)) = true

/-- The actual chain as an occurrence in the circuit body. -/
@[expose] def chainOcc (qs : List Quantifier) (ms : List (List Bool)) :
    Occurrence (Chain.diagram [] qs) (body qs ms) := .compLeft _ .refl

/-- The actual CNF terminal as an occurrence in the circuit body. -/
@[expose] def terminalOcc (qs : List Quantifier) (ms : List (List Bool)) :
    Occurrence (terminal 0 qs ms) (body qs ms) := .compRight _ .refl

private theorem shared_top (qs : List Quantifier) (ms : List (List Bool))
    (t : (body qs ms).Edge → Bool) :
    (terminal 0 qs ms).topList (t ∘ (terminalOcc qs ms).emb) =
      (Chain.diagram [] qs).botList (t ∘ (chainOcc qs ms).emb) := topList_compRight _ _ t

/-- **The terminal matrix contract is derived from the actual graph**, rather than assumed:
an active final satisfied wire needs trying and a CNF true under the current latch values. -/
theorem terminal_spec (qs : List Quantifier) (ms : List (List Bool))
    {t : (body qs ms).Edge → Bool} (ht : ((body qs ms).graph Gate.interp).Legal t)
    (hsat : t ((chainOcc qs ms).emb (Chain.control [] qs qs.length 0)) = false) :
    t ((chainOcc qs ms).emb (Chain.control [] qs qs.length 1)) = true ∧
      Satisfies ms (Chain.memories [] qs (t ∘ (chainOcc qs ms).emb)) := by
  obtain ⟨ls, hread⟩ := Chain.botList_controls qs [] (t ∘ (chainOcc qs ms).emb)
  have he := holds_terminal qs 0 ms _ ((terminalOcc qs ms).legal ht)
  rw [(shared_top qs ms t).trans hread] at he
  have h := he hsat
  obtain ⟨ls', hread', hb⟩ := Chain.literals_of_try qs [] ((chainOcc qs ms).legal ht) h.1
  have heq : ls = ls' := by simpa using hread.symm.trans hread'
  subst heq
  have hempty : ((Chain.diagram [] qs).topList (t ∘ (chainOcc qs ms).emb)).drop 2 = [] := by
    simp [topList, List.ofFn_succ]
  simp only [hempty, List.append_nil] at hb
  exact ⟨h.1, le_antisymm le_top (h.2 ▸ all_hits_mono ms hb)⟩

private theorem terminal_spec_occ (qs : List Quantifier) (ms : List (List Bool))
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (body qs ms) D)
    {t : D.Edge → Bool} (ht : (D.graph Gate.interp).Legal t)
    (hsat : t ((o.trans (chainOcc qs ms)).emb (Chain.control [] qs qs.length 0)) = false) :
    t ((o.trans (chainOcc qs ms)).emb (Chain.control [] qs qs.length 1)) = true ∧
      Satisfies ms (Chain.memories [] qs (t ∘ (o.trans (chainOcc qs ms)).emb)) := by
  simpa only [Occurrence.emb_trans, Function.comp_def] using terminal_spec qs ms (o.legal ht)
    (by simpa only [Occurrence.emb_trans, Function.comp_def] using hsat)

/-- **Soundness of the actual quantifier-chain/CNF body**, in any containing diagram. Every
legal inactive start can reach an active satisfied wire only if the quantified matrix is true.
All terminal hypotheses of `Chain.truth_of_reachable` are discharged by the graph itself. -/
theorem truth_of_reachable (qs : List Quantifier) (ms : List (List Bool))
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (body qs ms) D)
    {s t : D.Edge → Bool} (hs : (D.graph Gate.interp).Legal s)
    (hstart : s (o.emb (.inl 1)) = false) (h : (D.graph Gate.interp).Reachable s t)
    (hsat : t (o.emb (.inl 0)) = false) : Chain.Truth (Satisfies ms) qs [] := by
  have hinput (j : Fin 2) :
      (o.trans (chainOcc qs ms)).emb (Chain.input [] qs j) = o.emb (.inl j) :=
    congrFun (o.emb_trans (chainOcc qs ms)) (Chain.input [] qs j)
  exact Chain.truth_of_reachable qs [] (o.trans (chainOcc qs ms)) (fun _ => []) (Satisfies ms)
    hs ((congrArg s (hinput 1)).trans hstart)
    (fun u hu hsat => (terminal_spec_occ qs ms o (hu.legal hs) hsat).1)
    (fun _ _ _ _ _ => rfl)
    (fun u hu hsat => (terminal_spec_occ qs ms o (hu.legal hs) hsat).2)
    h ((congrArg t (hinput 0)).trans hsat)

end Cslib.Complexity.NCL.QBF.Matrix
