/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossAdjacentTransposition
import CslibFrontier.Computability.PolyTime.CSP.StateSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.List.Swap

import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Executing a finite schedule of adjacent CROSS transpositions

`CrossInsertion.transposeSchedule` folds the existing positioned program in request order.
Only successful binary guards count toward old-name doubling. Raw invalid steps retain the
entire current State. The value word follows ordinary adjacent swaps, while actual names
follow the existing fresh-name program; no raw cycle or inverse pair is canceled.

This original schedule executor is a step toward
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091), not a sorter,
planarization compiler, recognition algorithm or hardness theorem. Atom assembly, trace
generation, metadata, group fusion/hiding and final reduction remain separate obligations.

## Main definitions

* `CrossInsertion.transposeSchedule`: execute every requested positioned step in order.

## Main results

* `CrossInsertion.accepted_transposeSchedule`: internally derived full checker preservation.
* `CrossInsertion.recover_transposeSchedule`: recover one source assignment and the whole word.
* `CrossInsertion.eval_transposeSchedule_iff`: extension on every `2^k` old name.
* `CrossInsertion.components_transposeSchedule`: exact rows, occurrences, ports and symbols.
* `CrossInsertion.computableInPolyTime_transposeSchedule`: all-raw plain runtime with an
  internally proved prefix storage bound.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open OrderedBoundary Graph Cslib.BitString Turing.MultiTapeTM

variable {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Execute the existing raw positioned program in exactly the listed order. Binary
positions remain data; invalid guards execute the existing whole-State identity branch. -/
@[expose] def transposeSchedule (I : State Rel) (js : List ℕ) : State Rel :=
  js.foldl (fun J j => transposeAdjacent g w J j) I

/-- An all-invalid schedule preserves the entire input, including malformed surplus data. -/
theorem transposeSchedule_eq_self (I : State Rel) (js : List ℕ)
    (h : ∀ j ∈ js, I.ports.length ≤ j + 1) : transposeSchedule g w I js = I := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [transposeSchedule, List.foldl_cons, transposeAdjacent_invalid g w I j (h j (by simp))]
    exact ih (fun k hk => h k (by simp [hk]))

/-- Every executed step supplies the complete checker result for the next fold state. -/
theorem accepted_transposeSchedule (I : State Rel) (js : List ℕ) (h : I.Accepted) :
    (transposeSchedule g w I js).Accepted := by
  induction js using List.reverseRecOn with
  | nil => exact h
  | append_singleton js j ih =>
    rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact accepted_transposeAdjacent g w _ j ih

/-- Exact arity is preserved for every raw schedule, independently of semantics. -/
theorem wellFormed_transposeSchedule_iff (I : State Rel) (js : List ℕ) :
    (transposeSchedule g w I js).body.WellFormed ar ↔ I.body.WellFormed ar := by
  induction js using List.reverseRecOn with
  | nil => rfl
  | append_singleton js j ih =>
    rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil,
      wellFormed_transposeAdjacent_iff]
    exact ih

/-- The exact component recurrence counts only successful guards. The symbol word keeps
all old rows in order and appends one fixed gadget word per successful request. -/
theorem components_transposeSchedule (I : State Rel) (js : List ℕ) :
    let k := js.countP (fun j => decide (j+1<I.ports.length))
    let K := transposeSchedule g w I js
    K.body.length = I.body.length + k * g.body.length ∧
    K.body.occurrences.length = I.body.occurrences.length + k * g.body.occurrences.length ∧
    K.ports.length = I.ports.length ∧
    K.body.map Constraint.rel = I.body.map Constraint.rel ++
      (List.replicate k (g.body.map Constraint.rel)).flatten := by
  induction js using List.reverseRecOn with
  | nil => simp [transposeSchedule]
  | append_singleton js j ih =>
    dsimp only at ih ⊢
    rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← transposeSchedule]
    have hc := counts_transposeAdjacent g w (transposeSchedule g w I js) j
    have hr := relations_transposeAdjacent g w (transposeSchedule g w I js) j
    rw [ih.2.2.1] at hc hr
    have hk : (js++[j]).countP (fun t => decide (t+1<I.ports.length)) =
        js.countP (fun t => decide (t+1<I.ports.length)) +
          (if j+1<I.ports.length then 1 else 0) := by simp
    rw [hk]
    by_cases h : j+1<I.ports.length <;>
      simp only [h, ↓reduceIte, add_zero] at *
    · rcases hc with ⟨hq, hm, hp⟩
      refine ⟨?_, ?_, hp, ?_⟩
      · rw [hq, ih.1]; simp only [Nat.add_mul, one_mul]; omega
      · rw [hm, ih.2.1]; simp only [Nat.add_mul, one_mul]; omega
      · rw [hr, ih.2.2.2, List.replicate_add]
        simp [List.flatten_append, List.append_assoc]
    · simp only [zero_mul, add_zero] at hc
      simp only [List.append_nil] at hr
      exact ⟨hc.1.trans ih.1, hc.2.1.trans ih.2.1, hc.2.2, hr.trans ih.2.2.2⟩

private theorem recover_step (I : State Rel) (j : ℕ) (τ : ℕ → Bool)
    (ht : (transposeAdjacent g w I j).body.eval sem τ = true) :
    let e := if j+1<I.ports.length then 1 else 0
    I.body.eval sem (fun z => τ (2^e*z)) = true ∧
      (transposeAdjacent g w I j).ports.map τ =
        (I.ports.map (fun z => τ (2^e*z))).swap j (j+1) := by
  dsimp only
  by_cases h : j+1<I.ports.length
  · have hj : j<I.ports.length := by omega
    let L := I.ports.take j
    let x := I.ports[j]
    let y := I.ports[j+1]
    let R := I.ports.drop (j+2)
    have hp := List.take_append_drop j I.ports
    rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons h] at hp
    have hL : L.length = j := List.length_take_of_le hj.le
    have hI : I = (⟨I.body, L ++ [x,y] ++ R, I.rotation⟩ : State Rel) := by
      cases I
      simpa only [L, x, y, R, List.append_assoc, List.cons_append, List.nil_append] using
        congrArg (fun ps => State.mk _ ps _) hp.symm
    have hr := recover_transposeAdjacent g w I.body L x y R I.rotation τ
      (by simpa only [← hI, hL] using ht)
    rw [ite_eq_left h]
    simp only [pow_one]
    have hr' : I.body.eval sem (fun z => τ (2*z)) = true ∧
        (transposeAdjacent g w I j).ports.map τ =
          L.map (fun z => τ (2*z)) ++ [τ (2*y),τ (2*x)] ++ R.map (fun z => τ (2*z)) := by
      simpa only [← hI, hL] using hr
    refine ⟨hr'.1, hr'.2.trans ?_⟩
    have hports : I.ports = L ++ [x,y] ++ R := by
      simpa only [L,x,y,R,List.append_assoc,List.cons_append,List.nil_append] using hp.symm
    rw [hports, List.map_append, List.map_append, List.map_cons, List.map_cons,
      List.map_nil, ← hL, ← List.length_map (f := fun z => τ (2*z))]
    simp [List.swap_adjacent_eq_take_drop, List.drop_append]
  · rw [transposeAdjacent_invalid g w I j (by omega)] at ht ⊢
    simp only [h, ↓reduceIte, pow_zero, one_mul, List.swap_adjacent_eq_take_drop, List.length_map]
    exact ⟨ht, rfl⟩

/-- Recover source satisfaction and the entire scheduled value word from ONE satisfying
output. The recovered assignment reads every original name at `2^k*z`, including unused
names. No checker, distinctness or arity hypothesis is needed. -/
theorem recover_transposeSchedule (I : State Rel) (js : List ℕ) (τ : ℕ → Bool)
    (ht : (transposeSchedule g w I js).body.eval sem τ = true) :
    let swap := fun (ps : List Bool) (j : ℕ) =>
      if h : j+1<ps.length then ps.take j ++ [ps[j+1],ps[j]'(by omega)] ++ ps.drop (j+2)
      else ps
    let k := js.countP (fun j => decide (j+1<I.ports.length))
    I.body.eval sem (fun z => τ (2^k*z)) = true ∧
      (transposeSchedule g w I js).ports.map τ =
        js.foldl swap (I.ports.map (fun z => τ (2^k*z))) := by
  dsimp only
  simp_rw [← List.swap_adjacent_eq_take_drop]
  induction js using List.reverseRecOn generalizing τ with
  | nil =>
    simp only [transposeSchedule, List.foldl_nil, List.countP_nil, pow_zero, one_mul] at ht ⊢
    exact ⟨ht, trivial⟩
  | append_singleton js j ih =>
    let J := transposeSchedule g w I js
    have hp := (components_transposeSchedule g w I js).2.2.1
    let e := if j+1<I.ports.length then 1 else 0
    have hstep := recover_step g w J j τ (by
      simpa only [J, transposeSchedule, List.foldl_append, List.foldl_cons,
      List.foldl_nil] using ht)
    rw [hp] at hstep
    have hprior := ih (fun z => τ (2^e*z)) hstep.1
    have hk : (js++[j]).countP (fun t => decide (t+1<I.ports.length)) =
        js.countP (fun t => decide (t+1<I.ports.length)) + e := by simp [e]
    have hass : (fun z => τ (2^e*(2^(js.countP (fun t => decide (t+1<I.ports.length)))*z))) =
        (fun z => τ (2^((js++[j]).countP (fun t => decide (t+1<I.ports.length)))*z)) := by
      funext z
      rw [hk, pow_add]
      congr 1
      ac_rfl
    refine ⟨?_, ?_⟩
    · simpa only [hass] using hprior.1
    · rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ← transposeSchedule]
      change (transposeAdjacent g w J j).ports.map τ = _
      rw [hstep.2, hprior.2, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [hass]

private theorem forward_step (I : State Rel) (j : ℕ) (σ : ℕ → Bool)
    (hs : I.body.eval sem σ = true) :
    let e := if j+1<I.ports.length then 1 else 0
    ∃ τ : ℕ → Bool, (transposeAdjacent g w I j).body.eval sem τ = true ∧
      (∀ z, τ (2^e*z) = σ z) := by
  dsimp only
  by_cases h : j+1<I.ports.length
  · have hj : j<I.ports.length := by omega
    have hp := List.take_append_drop j I.ports
    rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons h] at hp
    let L := I.ports.take j
    let R := I.ports.drop (j+2)
    have hL : L.length=j := List.length_take_of_le hj.le
    have he := (eval_transposeAdjacent_iff g w I.body L I.ports[j] I.ports[j+1]
      R I.rotation σ).mp hs
    obtain ⟨τ, ht, ha, _⟩ := he
    refine ⟨τ, ?_, ?_⟩
    · have hI : I = (⟨I.body, L ++ [I.ports[j],I.ports[j+1]] ++ R, I.rotation⟩ : State Rel) := by
        cases I
        simpa only [L, R, List.append_assoc, List.cons_append, List.nil_append] using
          congrArg (fun ps => State.mk _ ps _) hp.symm
      simpa only [← hI, hL] using ht
    · simpa only [ite_eq_left h, pow_one] using ha
  · refine ⟨σ, ?_, ?_⟩
    · rw [transposeAdjacent_invalid g w I j (by omega)]; exact hs
    · simp only [h, ↓reduceIte, pow_zero, one_mul, implies_true]

/-- Universal old-name extension for the literal schedule. `k` counts only successful
guards; zero successful requests have the ordinary identity lift. -/
theorem eval_transposeSchedule_iff (I : State Rel) (js : List ℕ) (σ : ℕ → Bool) :
    let swap := fun (ps : List Bool) (j : ℕ) =>
      if h : j+1<ps.length then ps.take j ++ [ps[j+1],ps[j]'(by omega)] ++ ps.drop (j+2)
      else ps
    let k := js.countP (fun j => decide (j+1<I.ports.length))
    I.body.eval sem σ = true ↔ ∃ τ : ℕ → Bool,
      (transposeSchedule g w I js).body.eval sem τ = true ∧
      (∀ z, τ (2^k*z)=σ z) ∧
      (transposeSchedule g w I js).ports.map τ = js.foldl swap (I.ports.map σ) := by
  dsimp only
  simp_rw [← List.swap_adjacent_eq_take_drop]
  constructor
  · intro hs
    have hext : ∃ τ : ℕ → Bool, (transposeSchedule g w I js).body.eval sem τ = true ∧
        ∀ z, τ (2^(js.countP (fun j => decide (j+1<I.ports.length)))*z)=σ z := by
      induction js using List.reverseRecOn with
      | nil => exact ⟨σ, hs, by simp⟩
      | append_singleton js j ih =>
        obtain ⟨ν, hν, ha⟩ := ih
        let J := transposeSchedule g w I js
        obtain ⟨τ, ht, he⟩ := forward_step g w J j ν hν
        have hp := (components_transposeSchedule g w I js).2.2.1
        rw [hp] at he
        refine ⟨τ, ?_, ?_⟩
        · simpa only [J, transposeSchedule, List.foldl_append, List.foldl_cons,
      List.foldl_nil] using ht
        intro z
        have h := (he (2^(js.countP (fun t => decide (t+1<I.ports.length)))*z)).trans (ha z)
        simpa [List.countP_append, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using h
    obtain ⟨τ, ht, ha⟩ := hext
    refine ⟨τ, ht, ha, ?_⟩
    have hr := (recover_transposeSchedule g w I js τ ht).2
    simp_rw [← List.swap_adjacent_eq_take_drop] at hr
    simpa only [show (fun z => τ (2^(js.countP (fun j => decide (j+1<I.ports.length)))*z)) = σ
      from funext ha] using hr
  · rintro ⟨τ, ht, ha, _⟩
    have hr := (recover_transposeSchedule g w I js τ ht).1
    simpa only [show (fun z => τ (2^(js.countP (fun j => decide (j+1<I.ports.length)))*z)) = σ
      from funext ha] using hr

/-- Every successful request increases the maximum binary name width by at most one;
invalid requests preserve the whole State. The bound includes unused boundary names. -/
theorem name_width_transposeSchedule_le (I : State Rel) (js : List ℕ) (W : ℕ)
    (hW : ∀ z ∈ I.body.vars ++ I.ports, z.size ≤ W) :
    ∀ z ∈ (transposeSchedule g w I js).body.vars ++ (transposeSchedule g w I js).ports,
      z.size ≤ max W (2*g.numAux+7).size +
        js.countP (fun j => decide (j+1<I.ports.length)) := by
  induction js using List.reverseRecOn with
  | nil =>
    intro z hz
    exact (hW z hz).trans (le_max_left _ _)
  | append_singleton js j ih =>
    let J := transposeSchedule g w I js
    have hp := (components_transposeSchedule g w I js).2.2.1
    by_cases h : j+1<I.ports.length
    · have hj : j<J.ports.length := by rw [hp]; omega
      have hj1 : j+1<J.ports.length := by rw [hp]; exact h
      have hs := List.take_append_drop j J.ports
      rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hj1] at hs
      have hlen : (J.ports.take j).length=j := List.length_take_of_le hj.le
      have hb := name_width_transposeAdjacent_le g w J.body (J.ports.take j)
        J.ports[j] J.ports[j+1] (J.ports.drop (j+2)) J.rotation _
        (by simpa only [List.append_assoc, List.cons_append, List.nil_append, hs] using ih)
      intro z hz
      have hJ : J = (⟨J.body, J.ports.take j ++ [J.ports[j],J.ports[j+1]] ++
          J.ports.drop (j+2), J.rotation⟩ : State Rel) := by
        have hps : J.ports = J.ports.take j ++ [J.ports[j], J.ports[j+1]] ++
            J.ports.drop (j+2) := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs.symm
        exact congrArg (fun ps => State.mk J.body ps J.rotation) hps
      rw [← hJ, hlen] at hb
      have hz' := hb z (by simpa only [J, transposeSchedule, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using hz)
      have hk : (js++[j]).countP (fun t => decide (t+1<I.ports.length)) =
          js.countP (fun t => decide (t+1<I.ports.length)) + 1 := by simp [h]
      rw [hk]
      exact hz'.trans (by omega)
    · intro z hz
      have hbad : J.ports.length ≤ j+1 := by rw [hp]; omega
      have heq : transposeSchedule g w I (js++[j]) = J := by
        rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil,
          ← transposeSchedule, transposeAdjacent_invalid g w J j hbad]
      rw [heq] at hz
      have hk : (js++[j]).countP (fun t => decide (t+1<I.ports.length)) =
          js.countP (fun t => decide (t+1<I.ports.length)) := by simp [h]
      rw [hk]
      exact ih z hz

private theorem prefix_storage (I : State Rel) (js : List ℕ) :
    let k := js.countP (fun j => decide (j+1<I.ports.length))
    let J := transposeSchedule g w I js
    (k=0 → J=I) ∧ (0<k → J.rotation.successor.length =
      2*(J.body.occurrences.length+I.ports.length) ∧
      ∀ v ∈ J.rotation.successor,
        v.size ≤ (2*(J.body.occurrences.length+I.ports.length+4)).size) := by
  induction js using List.reverseRecOn with
  | nil => exact ⟨fun _ => rfl, by simp⟩
  | append_singleton js j ih =>
    let J := transposeSchedule g w I js
    have hc := components_transposeSchedule g w I js
    have hp := hc.2.2.1
    change J.ports.length = I.ports.length at hp
    by_cases h : j+1<I.ports.length
    · have hgood : j+1<J.ports.length := by rw [hp]; exact h
      have hs := storage_transposeAdjacent g w J j hgood
      have hn := counts_transposeAdjacent g w J j
      simp only [ite_eq_left hgood, one_mul] at hn
      have hk : (js++[j]).countP (fun t => decide (t+1<I.ports.length)) =
          js.countP (fun t => decide (t+1<I.ports.length)) + 1 := by simp [h]
      dsimp only
      rw [hk]
      refine ⟨by omega, fun _ => ?_⟩
      rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ← transposeSchedule]
      change (transposeAdjacent g w J j).rotation.successor.length =
        2 * ((transposeAdjacent g w J j).body.occurrences.length + I.ports.length) ∧
        ∀ v ∈ (transposeAdjacent g w J j).rotation.successor,
          v.size ≤ (2 * ((transposeAdjacent g w J j).body.occurrences.length +
            I.ports.length + 4)).size
      simpa only [hn.2.1, hp] using hs
    · have hbad : J.ports.length ≤ j+1 := by rw [hp]; omega
      have hk : (js++[j]).countP (fun t => decide (t+1<I.ports.length)) =
          js.countP (fun t => decide (t+1<I.ports.length)) := by simp [h]
      dsimp only
      rw [hk]
      rw [transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ← transposeSchedule, transposeAdjacent_invalid g w J j hbad]
      exact ih

private def symbolMass (encRel : Rel ↪ List Bool) (F : CSP Rel ℕ) : ℕ :=
  ((F.map Constraint.rel).map (fun r => (encRel r).length)).sum

private theorem prefix_symbol_mass (encRel : Rel ↪ List Bool) (I : State Rel) (js : List ℕ) :
    symbolMass encRel (transposeSchedule g w I js).body = symbolMass encRel I.body +
      js.countP (fun j => decide (j+1<I.ports.length)) *
        ((g.body.map Constraint.rel).map (fun r => (encRel r).length)).sum := by
  have h := (components_transposeSchedule g w I js).2.2.2
  unfold symbolMass
  rw [h, List.map_append, List.sum_append]
  congr 1
  generalize js.countP (fun j => decide (j+1<I.ports.length)) = k
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, List.flatten_cons, Nat.succ_mul, Nat.add_comm]

private def templateBudget (encRel : Rel ↪ List Bool) : ℕ :=
  8 + g.body.length + g.body.occurrences.length + (2*g.numAux+7).size +
    ((g.body.map Constraint.rel).map (fun r => (encRel r).length)).sum

private def scheduleBudget (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ) : ℕ :=
  let C := templateBudget g encRel
  let U := (encState encRel p.1).length + p.1.body.occurrences.length + p.2.length + 1
  64*(8*(C+1)*U+1)^3

private theorem prefix_size (encRel : Rel ↪ List Bool) (I : State Rel) (js s : List ℕ)
    (hs : s <+: js) :
    (encState encRel (transposeSchedule g w I s)).length ≤ scheduleBudget g encRel (I,js) := by
  let S := (encState encRel I).length
  let C := templateBudget g encRel
  let U := S + I.body.occurrences.length + js.length + 1
  let L := 8*(C+1)*U
  let k := s.countP (fun j => decide (j+1<I.ports.length))
  let J := transposeSchedule g w I s
  have hb := State.component_size_le_encoding encRel I
  have hk : k ≤ js.length := (List.countP_le_length).trans hs.length_le
  dsimp only [k] at hk
  have hc := components_transposeSchedule g w I s
  have hC : 8 ≤ C ∧ g.body.length ≤ C ∧ g.body.occurrences.length ≤ C ∧
      (2*g.numAux+7).size ≤ C ∧
      ((g.body.map Constraint.rel).map (fun r => (encRel r).length)).sum ≤ C := by
    dsimp only [C, templateBudget]; omega
  let K := (C+1)*U
  have hSU : S ≤ U := by dsimp only [U]; omega
  have hMU : I.body.occurrences.length ≤ U := by dsimp only [U]; omega
  have hTU : js.length ≤ U := by dsimp only [U]; omega
  have hkU : k ≤ U := hk.trans hTU
  have hUK : U ≤ K := by
    calc U = 1*U := by omega
         _ ≤ K := Nat.mul_le_mul_right U (by omega)
  have hCK : C ≤ K := by
    calc C = C*1 := by omega
         _ ≤ K := Nat.mul_le_mul (by omega) (by dsimp only [U]; omega)
  have hK : 9 ≤ K := by
    calc 9 = 9*1 := by omega
         _ ≤ K := Nat.mul_le_mul (by omega) (by dsimp only [U]; omega)
  have hq : J.body.length ≤ K := by
    rw [hc.1]
    calc _ ≤ U + U*C := Nat.add_le_add (hb.1.trans hSU)
           (Nat.mul_le_mul hkU hC.2.1)
         _ = K := by dsimp only [K]; ring
  have hm : J.body.occurrences.length ≤ K := by
    rw [hc.2.1]
    calc _ ≤ U + U*C := Nat.add_le_add hMU (Nat.mul_le_mul hkU hC.2.2.1)
         _ = K := by dsimp only [K]; ring
  have hp : J.ports.length ≤ U := by rw [hc.2.2.1]; exact hb.2.1.trans hSU
  have hr : symbolMass encRel J.body ≤ K := by
    rw [prefix_symbol_mass]
    calc _ ≤ U + U*C := Nat.add_le_add (hb.2.2.2.1.trans hSU)
           (Nat.mul_le_mul hkU hC.2.2.2.2)
         _ = K := by dsimp only [K]; ring
  have hL : L = 8*K := by dsimp only [L, K]; ring
  have hpad : K ≤ L := by rw [hL]; omega
  have hw : ∀ z ∈ J.body.vars ++ J.ports, z.size ≤ L := by
    intro z hz
    have hx := name_width_transposeSchedule_le g w I s S hb.2.2.2.2 z hz
    have hmax : max S (2*g.numAux+7).size ≤ K :=
      max_le (hSU.trans hUK) (hC.2.2.2.1.trans hCK)
    change z.size ≤ max S (2*g.numAux+7).size + k at hx
    rw [hL]
    omega
  have hstore := prefix_storage g w I s
  have hD : J.rotation.successor.length ≤ L ∧
      ∀ v ∈ J.rotation.successor, v.size ≤ L := by
    by_cases hzero : k=0
    · have heq := hstore.1 hzero
      change J = I at heq
      rw [heq]
      refine ⟨hb.2.2.1.trans (hSU.trans (hUK.trans hpad)), ?_⟩
      intro v hv
      have hx := SizedListEncoding.length_elem_le (encA := encNat)
        (encL := encList encNat) I.rotation.successor v hv
      rw [encNat_apply, Nat.size_eq_bits_len] at hx
      have htab : (encList encNat I.rotation.successor).length ≤ S := by
        dsimp only [S]
        enc_len [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
          Graph.encRotationCertificateFields]
      exact hx.trans (htab.trans (hSU.trans (hUK.trans hpad)))
    · have ht := hstore.2 (by omega : 0<k)
      change J.rotation.successor.length = 2*(J.body.occurrences.length+I.ports.length) ∧
        (∀ v ∈ J.rotation.successor,
          v.size ≤ (2*(J.body.occurrences.length+I.ports.length+4)).size) at ht
      have hi : I.ports.length ≤ K := hb.2.1.trans (hSU.trans hUK)
      refine ⟨?_, ?_⟩
      · rw [ht.1, hL]; omega
      · intro v hv
        have hx := (ht.2 v hv).trans (Nat.size_le_self _)
        rw [hL]
        omega
  exact State.encoding_length_le encRel J L (hq.trans hpad) (hm.trans hpad)
    (hp.trans (hUK.trans hpad)) hD.1 (hr.trans hpad) hw hD.2


private theorem budget_poly (encRel : Rel ↪ List Bool) :
    PolyBounded (fun p : State Rel × List ℕ =>
      (encPair (encState encRel) (encList encNat) p).length) (scheduleBudget g encRel) := by
  let input := encPair (encState encRel) (encList encNat)
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hj := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hb := encState_body_polyTime encRel hi
  have hm : ComputableInPolyTime (fun p : State Rel × List ℕ => p.1.body.occurrences.length)
      input encUnary := by
    simpa only [CSP.vars_length_eq_occurrences, Function.comp_def] using
      (computableInPolyTime_length_vars encRel encNat).comp hb
  have ht := (ComputableInPolyTime.length_list encNat).comp hj
  let measure := fun p : State Rel × List ℕ => (input p).length
  have hS : PolyBounded measure (fun p => (encState encRel p.1).length) :=
    hi.polyBounded_length
  have hM : PolyBounded measure (fun p => p.1.body.occurrences.length) := hm.polyBounded
  have hT : PolyBounded measure (fun p => p.2.length) := ht.polyBounded
  have hU : PolyBounded measure (fun p => (encState encRel p.1).length +
      p.1.body.occurrences.length + p.2.length + 1) :=
    ((hS.add hM).add hT).add (.const 1)
  have hx : PolyBounded measure (fun p => 8*(templateBudget g encRel+1)*
      ((encState encRel p.1).length+p.1.body.occurrences.length+p.2.length+1)+1) :=
    ((PolyBounded.const (8*(templateBudget g encRel+1))).mul hU).add (.const 1)
  exact (PolyBounded.const 64).mul (hx.pow 3)


/-- Execute every raw binary request in plain polynomial time. The actual framed schedule
funds the fold and each positioned step caps binary positions by port length. Reachable
prefix storage is bounded internally from actual components and encoded symbol payload,
not from a caller growth hypothesis or iterated polynomial output-size bound. -/
theorem computableInPolyTime_transposeSchedule (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => transposeSchedule g w p.1 p.2)
      (encPair (encState encRel) (encList encNat)) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hj := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  exact (ComputableInPolyTime.foldl_spec hj hi
    (computableInPolyTime_transposeAdjacent g w encRel)
    (fun p consumed J => J=transposeSchedule g w p.1 consumed)
    (fun _ => rfl)
    (fun p consumed J j _ hJ => by
      simp only [hJ, transposeSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil])
    (budget_poly g encRel)
    (fun p consumed J hp hJ => by rw [hJ]; exact prefix_size g w encRel p.1 p.2 consumed hp)).1

end Cslib.Complexity.CSP.CrossInsertion
